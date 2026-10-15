-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5063
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:37:26.283461+00:00
-- url     : https://prove2.me/submissions/6488aac8-1357-4769-ba2e-3b6b11ded291

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 910431654 ≤ n < 910611510 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 910432904 1250 910431654 910431661
    0xa060c050a080c1806180306010b03150d0f080d09150c020d020c130e0a080412020307050f01120504051c021609110a0c03090b031501020f06060130060b180102010203 73
    0x20b0007121084c1c00d11030040c80005020080104040e40d0340700c070718202400f21001541e59443c0740c82c080c0d008035a09440780f124038078508030078900300440d000390b250421031008c0516460b4031141e81903072004620340310443d9524a00000515241c1468604120200000500011240c4081d0402d0120110082190030211005425a40d40e03131202101e03041e2290005012000700300d8851a00e842200081c0c051207000c03400298035000366180c1a0028402c0d02a00c0c0e00d140d446082c010207042610440d80461042030f3f88526a14045d4030565126028070b080721140007503a1019540d01081d40b80030401a00040000e10380410440c581e10010440200c0400040c1039440c01032880c1d00840b50114200000d18920006061042901401030000021142d0740da003043e41d03a280b00316000484550150085d40b901000c088004178400d84511010303191100c00c090711b40401003110714412543d9000d4000c1c6e104003c4452080d100d907501a08004442aa0310f07240c041c15404010010f4444131704580c010401c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 910434154 1250 910432904 910432927
    0x90c01020c100302070501020903060c0703022e0906060302130b011e080c0d06091401060f11030d0e100f0c02060f22140111091c0819020a060c050a080c 67
    0x842c0008518940103850b803215103050390182c45540c8405030325200318000d00c198100e401e40184015846a021103c0e10807085010311100641c5080081025003241f1620346c00c0112a001170254520a6a0000c0e000362a640000e0441141c21220440c007542c03164040310035600810300990400424045800c4440001c3c0b000b05844c50003081500c001c20089040c007a0140c030ba4100034080c140040090200c0450b0b60b5000c034044400f44941000100c0c4049803064040c000c0840600310b4010002942c9030035282c0d03640d80050140306441c866140b180104680f181525841143c258115030800455401d901c81c000910b0044081d02c0a802030b09104c0030301c04c203801e1359444c405055142c2040f0744c240304124104a001c0c1c1038140c05100c640d50800a09060849a2600030800c3c071904407603184040070a6000d04d49052607100004080d01c904025015a182800700d140394044610300c1162140c54041d80c07114281c03010030594074041180440c81000242d0040e103d20b43c0f10a101c03211504068402e6078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 910435404 1250 910434154 910434169
    0x1703070b0c0c0f060a0f0c0315050405060a0306151511033f07020f0a030e210a0f17090d110303190206091e060a1a090f090c01020c 58
    0x4070070000d000001c00001c0c482041c030041c5440d0443c481038402d40c0c60007211200c041d2050780046402c65240040b010805170281c814025807000d041060010203052030203210080102400d43d03030303107c40000000400103940380034101103a80d0b600b071503511043c40c240103c1c6014041c520110180f10440c02d1840c89014000243d41c0345911035422002c0c03803816005601c1d56610041d001c60103019203c0305000030003820101c1680a41119030071242c8032800580000d4a601d21050001d0018207035a411842902e03085514200b00074074103a0b003400b055008203d007441d0400d58407086070003c0d014511030081c42038098400c0250001c45440c40d00d064002e0700003503014251040010030a40c0c41c070004800c0380d141041926007011700c1c0312160200755241c400195403800219800200b51140c18140294815800c0c0258220299a8000d0200e501c440c40755201404101d0004140d00ba0f09001084042c1d40f20043d55009446034042000c0605024807054149000e460189040d54043c1040703280c0c580301d00e0b8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 910436654 1250 910435404 910435411
    0x80c060c1e0304020604030204020712020f161e211205211f06230a0e010f03291903050309130f05011d01090b0f1003140a02041703070b 60
    0x1400c02d9507a903403031001520034007585d08044e41041c80401c8030760400904000382c00d402e0145d5001ca800c400c407003400d00ea5544046040e098460703004040c04120029400031500916002d0b544084055600d4500c00d49411007004401e840e6060424400814840840b001c6090106149026072406500d415503800c2c0040002040349001d0002d0300041403d10545040041c8104000b41c40a601d992140c1c003d01601c02640001d0b036040b04956000700e614036860881d41c207581d0984441d601d4122810040da885d0704083d0709101816200c2c0c207800c007452988184503a42c18400e4807000d60f00405071003480003007003464440c103100000500e41880440d0000091f0f40845004803103010320040e492907610080c220325000301144505107000490b0041c241601d81a1a14844e20781103110380c3d850314440c0c250f911b6420780940140d440800024641003504240f030f580c107064200880c001c01d0000e0039810300c004c100ca010035003903400706040c003a0501d4141001c80b840e44080065040c03020540720701e204290042e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 910437904 1250 910436654 910436707
    0xc03110105010f15030f09060c0e0103090f020405040f050a051b030d080c0a0c0f060c032306010c021f0c03120603080f1305060c0a0b4f080c060c 64
    0x1140081c03130036842034005005500b41d450090100b829a8a0220041c15041658001046d60824118580c2d4464403070410011b40041080940548a40921000304000380c020742e080f2104c501101d021540030132038024024829402894a0070100c0744c0901443da1500d201442a0001030803184410b40c42104150040070705031280d540c984505030160740700710800e08001d0900002d90015130070b101103a848810f46010f65202130001e444403200010180c3e5105241d000100b4809012907025441084901c0d061880500170002c0b11540d0448114500f02c00704000e0006201d04011004050340b04108184040c10000244442e40c150b41ea03001c0c60307018945080c41411800301e00c02038580c900034801002844041d100543d1451601c4510b41c4601008000b82c0ba20802107000c40c190400304980360f0b012680d518015500c0300c2c1c1c001500600145107801d403060800313401c1c2140f801040184019800740340f00b440d10301d50302e990003d0800e040c0303030008041801d401c109100040f19034801041800b07044850 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 910439154 1250 910437904 910437929
    0x1080c070b071806020c0306010f0302060a080415092001030203070e0f0a0e07020601091407050a0807020a050708070504150608160207090906050a1406010203090d0f05030a0c03110105010f 83
    0x10603004030f5200c00c4440080310340104228002a04035008a0302c1c1c0030741d41c8141e064074116070300c0380d030a401088400d21000b500450704001780e291240c400c04031960010721681c0c10380001d0f543d000c10b04c3e040d94941e00e8140d0340981041d200031070003198001b010024540a090550075440d00d01c1000e072801401440d124007915541d411b40c10141d031080c270031340060144008402424145544000d6072113800340501320016180011140f10103001182161252030307103550751884c01d07401200c2100c100c140a46000194482c041c0d042001030f806000d000007074101e080041851070300e004100000e8644401110008181c00b0b101400101c1d030211103075520401889070b00d4480b4183c8030040b807401016502c80d07001c480c68046810100000b54200500802000c80b050292032002000440c640c503054800d40d025030310412000d9507905142410500f0517000d5112003014560716112141142d1100082800141011070b034401010b8210500460f0074501c00000c200c95810b215880844050500804119505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 910440404 1250 910439154 910439161
    0xc0a0512030c03040906170a020f060702041805100c03091e08120708070e040b0a030303050c1c02070615030c0947012d050403050f0c0f01080c070b 65
    0x10400c940070b000c040380490396159580c0800c60010702c0f45002e0a0f07500b04480040300b102e8107001502c83c003915002411040092080c208201c2075620482c0101d80050f00d071159861503c0c40740c140f01c1c403807a00031009002c030950b09426540c1111524a00300051603d440301850115810f5501d220401c00c02040030702044410781042c174881c0c09043d0401800c1e02d0120100500d069000300b11038007480042c1c6074900703a0140882007100b03403030b444003100307401c04020101000828031036000203802a04040d2035910306030140f619500c50032600320110404a0700011032204004140c420011941c01c1c10000d280c002d4115a50034004802921074040519103030280010205003c40c1e0241400000032020583d0800300140154a00303a50400c98100001c04030301002a5400b07001c227021000364512504000550036880c840c80000020460400c01c80c1c10f010110024000308454028440f89070000d02040c1035001c204620302446542d018100004182400902c450142c1583e0003590b21000c50421941e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 910441654 1250 910440404 910440439
    0x702010512090715111b06040801020c06010521071401030204050418060509030306030307080c07030507230301090b07050a0314010b1c1802010f090b0d0c110c0a05 72
    0x18103902000402004018410302e041d000078500100c9010008000f1380507580030042d10000850490f0002c15000301120703062140407014100c4554030b00038841e509250f2100c84003822a040300074012044d900007001803180e482c045101444040307081408070801c0e00c9070302c4c2c51500e40505100b1059041c0409108002a03802034050b6005420050000c102042c0003009106900c40021815182030b45050082481e0348070102c2224483c10010b8001e6151500c6643d40483c29801a2142d18060045010200c0081c0c02844000c4c000d00f90414010308640e1010481d10381050540300d010701c42e070300d0b049281c07000410700c0724082da0141031400e0043d21a094500190040c0c1481c1c02c2801c1c58850890002c00c03000d1940c0040d2058203149219490480d80301c091078011a40306a2020b0300c1c050000c101c40005601c216010718001140c0c0c640710780d00079610000112142c10406c0f00d00300c0c85441e00c04a4400c01d60140a0b44440c011000c010700740d0801c00d00100d44014181c1c010140607200d0f034603500c0f0158 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 910442904 1250 910441654 910441657
    0x1b062203020402030a0b090a090c050d02060d0509011e0203010f0b18040915140402030601030f080d0203011203030c0206070e0402031320010212030702151305030c1f0e030f07020105 80
    0xd54020700190742e03e107055050f000c002c020b40000c25100b4213001d40856032829151050459465120a000b110107050904000e4094000b40741240e00c403030100034081c608490f5004213801102d10b04008200403d890380342c0e120140e07601c0180705034144148010410780e04a981200e044541d4000180e50b0340d80150740004690780000d84164206041a208100b0000c000001c060001c540701800c2102803100444940c4103801503401950541c400001480460418205094541d206a907503e02e001e6480c1290000d98200764800d0704103005002106e01419094001c03000d140d0700600c041c004614207960042e088012103043d09000d1a030120009900b890400b501800e042d4020b040300e031300380c3c0f250504070340c01044c1d070fa16240c01401480001843c156400c010b49028031031907005040825404800402480002050a554460380d001541c01150090000740040700519000d441e0680001c200e10340c400003c0078042100c0791a100400f0400d00e40427082c0c412010b0950111a95102d40c0d00049415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 910444154 1250 910442904 910442909
    0x20307091203120b061201090b1807020718050f0403030f0e010f020d06090504030203160218390735120604020712031d1b031b0622 58
    0x2240c1c18240c100a0542000e0b0395101100ca0140620003035420105100c0e42d4002c92008032407001da040c00502581c940b03500b1690b501100501081103c54100e400d01402d414140d65800160b007080c00107000880c504980c0c5014001e0901c000d0086080c00c5d4405990104010700c00b80806654a24505a80005810448840e07050030003c3c01001c54403280c0c0002980291841100a8941200002d0300032031802204d214030b8164015500700310f62900c100190746000b00301241c0c402080321180e01808030b00075186014000107d000d4051206c0e600c43d50324a40340b1610b10030051002c0c8040340001803034100440b1215030b402003002074007110300441004811203a88456041032003d1044044940c1e2000c0038240320100500c4284554607202d0a01081384103000020300005450700003100880c0c0a03030407192a191040d203803481c800380400e012506202d20003c0d0220a00e4205a8580d070900d0200900c4019685022402c1c45480d00b06000500500c40c00f243d400400341e00384507182240c0c0680d0b058000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 910445404 1250 910444154 910444169
    0x220201200106090b090105010f051b072c0f270d0509150f0d0b01050c01050a020c0c0616330609240e0a0b0406030f171c02030709 57
    0x103034000021529406042c2074018089002d2500b0185103003442d158041604031401a15082100b9001d81c004542c2d40d4003807150301c01c041000b10821406030f0343c104846d1000304102015418103403410032070402404400c0003904030220380d042c14400c2101404001c503801c911840d0100070301d1502081007200461051880041602400b9901348030240c20400070161558200c0d07009503e12480c00710000c0500030102d942158600521011004204981c0002c21a00c01414043d0415001c0c415032401c4d141d044aa010407541c003c01c41d480c2880c002c00a03000d020b8012a201802c20700884000c030108a000b410251107080d0401c1c95404801c055400c03002d404c405002e04c2a40441040e01e200c001d4036403032080072410351914501c41d801001c8110100004062f000118641c81d00e8085d614a500401504200c001d60ba03808071549566110310550700210701c109448881c40d27240342400003411001007402070180034100300424043c1100a0000c00909a1442c01a01d81c0c482072411102460507401881 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 910446654 1250 910445404 910445447
    0x30603050601030803090d0807140d02070204180506071d21070b030108120906071202160e06120309012a020904050309040f060f051311040605030f0708220201 70
    0xc1c44040070085210f06c44d032804803100600241b07811203160700c00b1542c80700090325604242d118aa242c90003807844200e446000350608240d41c0021b001c03556800300804600b5200c4491608100f01400030715402600c50512082100318600d800d1088561200c0c1c440c0701d4800502c0362000012103810110444003036000b1251019160020f54019500a01550855210700c0001c0348105404070110751284070050201400c0410942c0c0700c1ca2810f4041c1118000d5004060100044084c800f10300d0740141450000c2c1c0d00346091500c00e1002c15903a28070303502c485401c20090207030b103640c00c426240740840406030914540f1222105211403090392807402540591b0030005c0c070042c810f00101800c5580340880702004040c920786140c2044411a1007070170541121940300304400c1c035000f0420b6405440300303900401e22078280082155168059000440810307808401c0c0039501004c070b01ea4a03485003aa040030102400c006007000e1100d110072881404680782c5d12405411039204850610400701488603d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 910447904 1250 910446654 910446659
    0xf01050711060619030305031b0d0207110d020a03231f0e0c150c12040f061209050309041a0a2304090b0c03090327151201050105030601030603050601 66
    0xe0015031007201144081c40360001203085460443c194064040b103006440d50454503542d0143c440c0d0300010024120b0f1030049000c148038568080040c5500c2030764401c0141d4a880d0b501e4140641811140c4280c050100503100b000181c84114200007903e4024040e10074004192200540e011902c003035580080c081d04e41d084940083c50180e040900500103000d0088006800d2210b603078005142d4156031201703502a4880c1401c3c901802403400305450802d80e81c164001c1d0310801d4003a405680107030038044464801f0001c00c0c1c3c1c85010952480080d0700103105805d4651141a135901480d0035040c8581e83e0303490b05c4c0b04000c029900c0148805006070140c2c039180c2c0d079000c00482c1407140081c00c90305440d85450400035440d0600c94901c2d419804203c6035403a880b0041048c2c030f907800061651300c140c4810013030011044600601c004101d0102c9091044066014080c402c03144601c64504501d00c40c10702002546600b86454181521000c4ca0030340d80742d6a444004074058a615800a0014010312001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 910449154 1250 910447904 910447907
    0x5031e2401030210031e0c1407080307030633031e0509060603191e0f0602090109060905090412090f08010207060c170c0702012a0213020901120e0f010507 68
    0xa20707040b40e000b114280350500a44c60290166104412420300c5444002c21402d40f407519903215083c40307106c2e0f20b014004103000c440c402d80c843d03000c0b42040d1001940403040040d20769160240d94081d01051a0b0a04e100114816941a04c8445034480b0b00c141102d540500302c191083d0300064880c0805035445134130000b00201800204401c3d54a14500d000f0940000c040b0704000813501e107605d010350030524039044e050f103502c40480c0b40094582c04220020b143c5002080140d0716030404076000c1d101c0140e98000000002d4100070196012a0500c40c40c12010800c40e51400501c1d0b501c140c00c08840c1000d20303540d0380201d0b003040c19900507100c403200c0040042401c0d48154003414180b0f01c1858100b0400c1040141990658903980d0b6007215110450300250820300d40342c01500203d403060510900c3d0f015582e1401c0761040181c200e590390b04441c10459004c2d85440c26603134032007030b1154104514190801000800b02c01051140340c0f802c5444407000c41c0380f10b00800500ca29024a18004c00990400210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 910450404 1250 910449154 910449223
    0x1a040f0b040506010207120b180f060906011203090e0a0b031e1501080a08071106030a0b18010b091c0b0720010c09140613081608060105031e 62
    0x11400c0c0150b10b0640016120b5000003440c40503070310039588200301301c03c01c0d50310404829801003500c15086060b100d4042c144408100b27010300c08a40e400030385051b1500340c01552400005a010010040445032a80c0c04240c001207424250b0312201c1040090b992021f1402028040c90303005070380c162040e2400103c08910180d01901d500c0b00301300a44948960400f40c00c42ca8580a01078a40260807140c100c1000411101c010110f81d8442d900c10b0181055142c006100c07a001110002d201903182c620380035081c600396210510306507044552141035410104924518042c034040f0500071203038801610901d480c0046034640d04c1e54009405961450686c5008203030108002125941010b0400c512500001c103020321618031007981c0d24140c03038518002c04548100040c00106400110812100341e0514804402201030700d1802c0043c11403a44100303098a8040f5240e10100543c3c0150f0010f014940d00450310a0500030010440e221629007440090705041944000c0d0310700c00003680700c01030801504803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 910451654 1250 910450404 910450421
    0x30402122b020609102018100f020d0f090f0801020408010b031b10140d0605030609010c14030a1506020106080705040207110904150c1e020a0210031a040f 68
    0x20701d0403041102280059a40c1c94058841212640001e0000c040c03003022035100210701040c1140c3c501d03102064100b10341081e4002c0c40101a080d8018110881a0600d081651400300703451802100240c0701c1d2400949810100c03200d1404c000544460101c8e41d4880e0500001400b018a42c0188096858a499001350b2140c0700d0300c00c5c01d50030014505218540400c503036040f1a100710203104904200020001c130f01e81018182c1007402404282803641040140150040e144c0107000000d07c0b5007070104051400070300400d00360301c1c1da05048849118640c041c14645040403400000c41d140c0c1c80e40581039010f00f40450000c001401b84070000640c09605401c4542100e038a0000e84822a4407681400280d100f506005002c0d55844850f028880c1003e00642da881400781111229510150f02d80b5016600d21035100700004100c0360341703005820381024003043c5007681400140034400e00c50380401c3e0040c1700100c00109141e40c0f04003042580404842c141c8043c54000d008110303142154002c2e5000701031070b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 910452904 1250 910451654 910451713
    0x130e0303100e0f18030d0c050a08150d02061803191502040b03061c08030c180607110d06020712080f09010506091302030c04060b0403021009051503040212 68
    0x1d800140007202010040c0103407003540c505034950303076100440014422103410440f0544410895013101c0b03086486000016501c5584060380e441c6425001400188003074802640c564949a03400020358032140581d010b203078161a41e035241d101074000112082c0508a1541d098040c1c1c8048048002c5a80800c1c0280351280000e0505250407682c982c00724025800781c0b0522000407c0440c2c0c83d850600c0034469091303086d00d04100e910340259030301040e50b08295070506000001003441201c004c20300d40000e00c03c6106548160a151030340d140c044820040c1c8207070a0185401c145e10740700707000300c5404844049810101200e030840d44ea4a00500c01070080300c629000c0301200c008a01942010300419010b4000100f09015644032281c1c6102280c01e212000c99052180420346982500c950103500c00402031014015140ea04c0d50041c880009854000d4400f00405c10100303200d0b0383e541c40d07221503a00d40000c107103941383d40c1d4500c0442c029110212070711041d44600c502e659000c1009a00080c10a6042c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 910454154 1250 910452904 910452931
    0x70b34050105180a0317040f0609050708010605010e0a05190305060c09100e09010e0907030c0807091508071e170616020a0203070312031119080105090403080a0b130e0303 75
    0x120f101c96150400030200500140e00f03a41900f000403400e0343d4554005010704d154198056060383c40f8011140d0401d0229101d8001d88020481c00d4030070b02c2440000c21080c24540000034401c8005445450640a40b0388501d0064401c90b012503580212070001d56400401c031046402c0604005865401c001c00851088500740000303105580300b8aa100c141c03200c003030300203103041c0d00f41110314030b00d120300400300160b522407820004041109954030310010a41c40d03015020050900d00c040d01030b0361044010244148507507100300584e4600194035401c440314044806802d102c0f17a00508800c407140d9000084402c1141e02e140b52491001c42c1e0b0a0140503441680280d520200005a8079403250301c0340698107800c801c4040000c00e488884a82c841001841c0004482200c1c00b803084050300101c030607040da07124810340980c01580040040d03000d04002ca07042c1d80180b0345580d00402c4140018041d5251603101c4440d101140c503001510000510061414400242c0d030011003696508110340c0000ca2148 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 910455404 1250 910454154 910454191
    0x30414010e0d030804170409060f0506030405030409020c030d060b030a0b0a0b0d050a060f0303050307110312011401020c030d120612030e060a0903050d0305010303020f070b34050105 80
    0x2a0140c400c891002030211641211191820b03911044d0080c0305a40384c03010000108412005080200094007604000044075418208424501d19894000340c3c0544c00030814440072500000c203a030100c1c0e41030140982d0303815140004c3c5045004800300c4241c094103111011034094094009548901081d400c20495a4105004c0040207181c80c070601000b803208001c0c030b5407400001e4100e42c0d800002c00c03c010a049564100860841706d181e80f0540c0000ca000c401e014200354804050484044008020b505104a50341840e0702c096040c461904040d00c0c2d0151505282d0080c00309044005004007614407041c140b03070015000124034081d0252842c5403040200303640300d40310b1270401c0c0b168056135a2020030906500303101e01079202c080040c0c144680074000000282e810403150b8140030696401040c07d51462038082d04d821003080030350049803c00c6400303011190110064505038111010040018040b48030751261998a00c41c000b00154078101d0101d05004054011600800c1c02401038a05480c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 910456654 1250 910455404 910455407
    0x6020d0c02012721050c0d03050103020102071809050609070503010b042c0f07030809040e0c0906040c050906030c040602070509010617060a170f070803070c2d0803041401 75
    0x106100d1041d64810f40d001c2c00c1d80c2a01000e025034041c100c0c414000750403514286034070f0392401d10718000928000b642c000f0303003844066014402c800d070101071420140055411640080d45420450180c6044400313500ba6903100400c10782c002c1156140c0001c140c070040d0405914994440205020b0b1500941c201303120f2030001e042c540300700c0e0350800010091000300c50955603c9001244260444210740c03144061001120105122081c01540b190b648503550700c05840910040e100680b100303000c0da82213400d910269407203000d06564030180440c0d000800100411041d0303010700419480035003000b0007200304142c1180100050040d038910f07408903002c01303903910b0402070445000d0140c48000303907140f251603a000c54045000c0340c1080c2c00074030126105440c1c01c0b001c00007000081003100c0070351210903100107054007444558050f1542c44051490030034103840340d078400c01d6188030700c601d0030038100f440c5a8621a05468804642107620314681100d560701282030340c903000350042e001d0098480050280c0c40d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 910457904 1250 910456654 910456661
    0x9010e0f0a0f0f2f0306041d0d0306060e040b0d02190f0806190e071401030f11180306090c010e031908071208130f020102072d08010207030c2d06020d0c0201 69
    0x120031394502039185903184000c3c4800345c0b10768050005c1d09030181c401f5a000110910640c01c00720703a02d6400080142c5030501c020703d42031000303040c1c0780100e140501e046a5911034062400039130b90103807174820084020400619580300a82d01042100403c1c44000c5541000402c0345c50050a0841c0e90b0b2004030341104400d02261950710400e01540d1111030100b01c1a907180d9045002e44005041c00110480f141d400340c2c05403105103c40e501c2584000074100b420000c0380083c03555404054004240d98501100c1e0f080d902c403042c0204e6414802400100d8415130f80c100071105050071a0103140070f21920f6850720306da0680002908072400500c03214503040c0c1ca4030441b802c43c40f070050b82c070198925411700d403600e50000e20810000c1c0c1c1180601c2c0c2011070b400020000303200d01c540058003551842406c500d4106c4000509070040c0000d0307401008a4000b00c0c0d030292640d08940d41000c2004500090800107040e61030044180703881c0c81c00154980020b115260307002c0c00100c1e01440b000e010410381058101d089 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 910459154 1250 910457904 910457981
    0x30c030a0210050d060b04060210050c030c0708130e090d021209120c040606090801060605070807060507021009061a060a1e140705010203070e09010e0f0a0f0f 70
    0x60348400044405031a00e002c1e007007a0a11281010f524120b500082d81c07007a00e0b85600805402c4c04000f4007001540c4c2d04002c0038034508925581000217082280400d00180700c06041c0001e15880810518180054601100c00d00c8002140340c200b86661918a0b521300030049403801840d014016070024050b0001c607000c00002c0740703482b034949070600e00810000d12907040009910140b25000311038a0585481c4104030151940d600d030b1203121881c00380c816003507d0942d04072200300142403005000251001d41034a8010f41c0c0464007003840e5803560000c034a080000c0061150b09414040e5400a0040341e81c051118129503e4178000d40382d20300000e00032540300d540c1e003000c00151501803800a2440003411064500e2481c9040d00801084503504031141d000000306a40c50f0b50f00005021400c0e8000088001c4010240c03802c844945c504045002908030007821002c005c2e041c000020701d4800c1560010b11459581e0204102c003441e03442d8128001d001006903500262a9148424007500401280440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 910460404 1250 910459154 910459159
    0x4060b040e0115090e040b0f0709212f130603030f031d1204170a0203120319060b18040e07050f15030705030f15091609180902030606030c 61
    0xc40d81d280c035003001d07403c04903002e010341000103902000c9000b001c94803c2074007450080c4858003042c2085206041c440e04042c1050083c41140340c810015400308400c0c010030801c00b103018217072141860a042154494102a201d40789090100002440710b070300d44611551308040d5920700800f400e448810040f10b00501028010480c850182c1d41030501c60380119952450045a1110f51850100d15a1070461940c0401400ca075003c2400d010744584150413040e5008404010b110282e040e801203500d0b003000a50401120400200184000c0c11a000c10800c1c151210020800b1503900d07414207000390448100d20049014500c402e240ca45010302a0200800040029003801e07450b00007040100354010303e030740780c00401c03000c40d0111121003a000345100c2da4258549039900e107481280702c03110301401028901503080c040c00244040d1035041300035038414592205016031204229090382d18000c1c0f548a00c01c00b1010002200d00151690851920305200390b04860042d101e11007091344070007800791002c2c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 910461654 1250 910460404 910460429
    0x90d02010b100c0f02150a0c0201110a0b04080307090503070603021908010f12021507030f1b170901020f0a03111005040206030c071407030303090b070309260c01140604060b04 77
    0x108007503101411044d44010803400320b103002c3e4004000c2c590401d4254030f000c581c030b400c012425540c1010703807030300310886000140c9840081543c035101e403c18042c001420055010000504260051800c2c0e000351000504560104bd9074000c0100a54403180e1150b412082d00390b02114454000c00303005040e10252254021910704203020300200c0c410f02c14040c1d0740304540c1c1002c559403491490061068a000350740b40c0d0000440c4d4880540301d04820455680f00c5140e040b002c401040c03d42d8601d070803400301950826602d0f0f0516004130f25110b0b01e4200ca41c458001e00d807400c07080503000741030040e0860b410400e403610b000031402a03208031501102e000e90040000c00010b15140c1c50304000f0603080c1d104a0b40300d0b040c118140c409605d400e0aa0700204d000c03da0b0b40440401744940c854280e035100c00507280c140003404241e529a9034010a40c01000e9400c88000c0b02a0ba11a1742c2c142030b0b0309440e5192008200e800d01100042c0315181041d40d15070300603440c0a2000c500640c031641200c0a45040c02002c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 910462904 1250 910461654 910461677
    0x81b0a05120307120c08070e06070f26040b091021150605090604030605130c030b1504090201020a0b070933142709070c061b09140d0506090d02010b10 66
    0x8d64001403d082807551141d0200402400105008000300b00e060040c40c0d8859040d1021085c4c0c414090001000c1c485070300140001c00c165681c250840e881c4810035246002417442d000e03020b03204a060b4500c0050240b10f90194401d240304544e10000d180b221205090790396a5445000391781c28070400200d9134000400f000140081807482e00281e4206c2602d0814028012484d1200e410285842d003040701c4202407042446a1070844489205407032908480400901e43c02c0d070300203540e40000072002011526080001110740340140c10550081000303030005001d15030342030307007440c0342c102c81f120050581d825217030b0f44806441c807803d0822130307000c2e02080c950310341030700040203e054008003160308643c0504408002495200d41d10803074024a0b040c1c0320300002d52100d1070044296178003080103103054000c0c80311101c82550700c9800301041340c02000002209440c401c010032001805580301a081d0b1003010280049160002070180107800315500805c601041d5104116068042c8161703c0c000521083e001c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 910464154 1250 910462904 910462907
    0x1807140a0905090c090103150f050c040e0402010e040c0216122d24140c0d091112070e0c0c030a0f02010b03070e1b07081b0a05120307120c0807 63
    0x10b01d80101140d0111048440300400040c1140e400342c00840d000704601c143c1b04042e03100c5001e02950801880402e004900e0024188080790040784680d901c07101410001c00d06690081d00030607800c48010340180200c2000c6900030750350300c11900346030100d00b40d104000280b00b201d1104100c0001e07480300410300d0240e640e0b00c1d0200d2a9043d801265141e02c0040000c0000468184042401501d02e4800c1d41040c3c03182e0504004076240f0301340c6c1f4220700c1801402c0000c0080041e04035807661070540c0000400900c242401c7d01c5d07200c8440740c02c0c1d03000b0b00d406080010340c16002440404035041c40801c1070065031a02001c42c403500031107400c00790319030003840b4400c42c07140036894058894035544000103079886000c0003c0d140208651144420381d4020041c0000c5d0b04c0c10600505915003461025450102d1f90307500e104440c421003040c4200c02602007840803040303009110003200c26030040111001c0c40315582141d2100d50081d1442c00110340756048510503220540614404c0ca0324a40324641150741e5400d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 910465404 1250 910464154 910464161
    0x108090a23030c01150509060d0215040f140405010b07080a08130609060c030b04020a0509040b150705010209130b1e01031112040507300203151807140a09 68
    0x24101400c1c00c8030200d150107000104058100000d0f56000425416211034100a40380c0c0103070800d0780030718405400c01200d52240c40341c800280d907050790900320410b2545481c00c0140516001700010b00107140c400210022110088100024111000c11560343d071a4070300d21040c801c040c00100502070a2050084180c024184035500102401000036009190380d925012605610000c60b145a0344039007281103654140710f0b8611804050310210b15001c10f441000e44240140c032860362189031143c220140d0f948a0030802d05210001c1416103440c0c1e0000e103492800b0750046c0e86128015101c1c5010504000464000c06101c0707200070746840b000101c09812845010101100305041c182c6811050341c0e03403106140280382d01240c001e0142c1580c00c05c1c0c500f650a061a9902c00700d0071454054403658504c25600b1002c01030b070309001010205910501c0841d003000c0d20303013006c90043d0409100300101500084120540d075604d10f8180c070714694a4a40c11004c13040c24500098104650041c2031051820329030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 910466654 1250 910465404 910465433
    0x705070f080f1b030d06060f021506030a05011506020d03180201080601021203011e0e010b0a080406150e01031a100506132105150108120901050c0a030513050108090a 73
    0x142c14610705508150070602c0300000c009030344415030001509981d40c4c1003034404d80340507018620b0104a09401d069000f5610744644207120003141c02040410500e580420a5041491b0b00500030711104040c000c084100c080b5034400d12025004603142040321038440c1c85003880c01d20b103134030b0385ea28114034980045034850300090840c2d0640c03050081283c80b0240c85000b0758001e042c04401e0404800701c0b803401551400d9540d03c0341c50f4050991005100f100c1011007541d02020031850711190a64590501c0700141803000b0140424410664001c80d0118044030700074140c90007204040481d01402e40700c0216038400b191201c6078800409004d01003450031000404049815145c0300301304548136900d400303e504c1304080c440210880003d60000300300050020002c1c01400902c2d030702c1150f01d050401600c1d2350101c1c0e5014181100050410020ba0050007034440c4246031038102c8110340791520700500700d540500406840203006d01e000013a03642c81111402d128036904c00150000716469a600c800710300155 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 910467904 1250 910466654 910466677
    0x7091415180a030b010f0605071a0402060f0a020115080a050a12030b06030901090605160c0210200a0512070c09050901060506030705190f0f140409020d090204050705070f08 76
    0xe1040721140d840d09040c0010b0760280071031000c69403410703040c1031845205601803c00e200013446050045014041007241c1d00404042a80240c0d4452001030304071301c5003420700581307082d01140500103590b0561000d510000c0c040d800604043c0c84000a95a405158400500d1a400a080780001908802d4803880411440c100864080d42b0319000410301d400486005a05030356078080300d001d00c14240502600806070107041d103c080d09030400101180007066001c0c1c0070f040c1603001400315510038054000018540007485003800c5409000c541c4480940300300340c2d02d40c840c008001908d514841c04842c04a0340c0004040d074901d14100c00e80002e848001d09060180d56500c20018203615071500540c8900d0346659000e1b5079040c0b6030242c1d14881d06545501d03042201034a0240c4c40c444c4c211541e159242030074107042c607401d04e4024008290303110741c1d00314040050011641c801140c01c107410dc51500303442150b0500499803030f000c08582c14068030744081c1c00b4840e0500c030341020898000003413521000e403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 910469154 1250 910467904 910467937
    0x30106060804210203130b07020f0913061a040f0c120c0f120204170303010906080a08090118080106120501050901050c070f060204031a16090303140d090f0b07091415 73
    0x7a2240605c1c6c11444c0d403000304100741c0003465804516250300b1114550b1821100051503050055811010300c0d2112001051503a403800f1900322240792541c400090344d00103005103c001c2c6148207079800b400041c1c0d003072070224180d010345110707450040c01000d2001e1010707078a44030303941c80b801e6045900603040ca01a0203030710b0b402c020210300c039070042c81c20781c00c480d00e5807005550300d5140c81a010200c0381140d0280e2a03d070445903400f0001502c00045409200091070510070f00f00010218441d0003515602290466203000400505036204982c01d19880b40190000c000954030b07400020b003601e200303c0301406108030822940c0300081c044449504114069540113040c9501c5e51354528910344462640c1c00c10070011010000c0042c4098041c08042002d03180c044400d600d541d40140a000c0381d40c10303100d0942c00c0403030b980030900441d6108000c5c4c0c41c1c102030700d03020314001400d04541c0000259814400a0007160300460500984511104800d038003528008201d1411030f26003106400c041e507400c0c0c1d44600c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 910470404 1250 910469154 910469167
    0x220f0b100e0d151b18260106180e060405071a0d020c010504061a100509040b030a1b051210051b03150108340912080306030106060804210203 62
    0x9034403c5100e000c40040000180d800350b24404114143d4035184800304000c504004400e6202c00300fa1a0003c4596146032411168030f58601801013008243d44410030b03600e0210300250010848074441041501c0c668100300342911307119581d4544c082100d000e0660b60004504100d6001548910034410081402880c100150111410240c0c6e0101c90446002e0f074540f004c0c40305111641c03040d03203007285043c1e0f1124541c407103810110b08130320071040c020828008081008030b071544658010404c018002800d43d0600c0c1c0d00b92900481c540400b2406c1485180002c202290500307001054096140c90280109a40e1841215070805070100824480020172646a00c00c0281d02c020051030191522f0010a260143e44000040c00104014402c0507110b144030402c00c0c3e0b004140c01803585506440b01700d0f00d50342420201c142d41820700b9a004500c01c0c0e0460081c80244805840a1409540100e00074040c05907200c00c2110f01c20300645010300760904141148552000d40d2110300c910810720b0050f00c3c00d000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 910471654 1250 910470404 910470413
    0xe06150c06160e18151c240504020a1203021608061915060e040902060f03041202070311090601140a090f09020a0e010507030509220f0b100e0d 63
    0x88050790460144016400d0403900035800500400b09420291042c15091080001000b0403a002610700c00320b0402030981c017004d5880e150204c40207590580000c01e9051050300d00450b9405000f900c10301f1a901d004407040c80d5050701e00803903029a4006040000c528204008455035030030844c000c900b0361051160303110702c51800300206c4006207000d0340501818580340000a24003618544081510307450690140c02d00b11203901c2c5201a1071144ca01076000c107a82001141c02803005a502079800b14020920b031400030500d0004622451040e2411204c1076410b250030399494107a800018981d07800e0646903034190422041a0b680090149411010000c059442009583c840707a41440001e5081c50b050006240d402001401001c44c01d004524041122000a0540d0b01c00e041e442c0c10880000b410710241407060b02a52500407004007180c0d4580315440d60305c1c00700f043d80f4401800b0503040c401d2201c0480658408d06105103400340040303034941040501180c0b070300401980c40781c1c000120003000005c074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 910472904 1250 910471654 910471663
    0x705060109060e060d0203071e0e010e0615270d0b010e0a0e070b0d0924060303030501150e040e0f06040501050403030b030d0903060f02070f051f060e06150c 69
    0xd1403507507000100c1505203001030b54000300050080740140d090141510040c0c4002429a088400c0c07140402171440140f190a040e51801d54048818140005e0002c5510500034a100f8050706080f15030311031103295182c0684050151007a048008190b0a0100d80750620b58118500701d04030083c104000c811139603036004140383c0e080c0c0006030180680d01c01c00c03503070b40701d14820329070b042c42c03100c000344110740c07a11406848a100701a804d60f501070720340c440c072020484a068030000340d0300c00004903c04517030340e8108a0010039040c4400d030006800c100c00000d103000324052441e0108043e0761100856043e4005001c05000c102e201c0822510580130031b0800484117110395401581305d40c001240d1410035040c001c058401010b44a4885d07080340204030303492a0000d9164040703d0307004e00301090b071080e462110f80c024002d03028041d16289040c00d803541040b6010070210392039200300000b08003104100308600300b143c02034096000c80034a00800b00718240f03010409440c8603406070b54a185403461140000313051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 910474154 1250 910472904 910472909
    0x302030d1e052e05090402060906121302011805030337030203041a130b07021c020d080901021303020d0c05120f0f03162a0609050111010c091a07050601 67
    0x80c5082c00c0c050550211201c07100e8070714201c50300c500f601040c2000c0000310704000180000380b00b07000028070724003182c4504041e00c03c405500d150b10350b4240761042e040100004d040b5012400140114001c1001e101aa4000c0043c4c41000c0d00031070800c007001204c270450142c01d260004029044c01c400b440b0b54a0007000d02028150903541c00341e140e0405103084c200b42414226281444546507081091440d80805005072054010410b07100c582c444480c00e03402c0c10f98171046100d005820740101c5440540000700c5880914265a0380701c0c0307031b41c0c0e1010304500302c0c011089980a80444480c1c10005441c181d0495883c241c020410390040c9507407600081c19150844181c0525500803041442403500c2c103009500143c543c040183d8605030040e502282c81d08080c0310021300b40032030300320000c506c40c51620202c00784c00c02c0f05200d80c0780c1301e0f01c550b800360040c1e025104179400102c000147c60b88048040c0a07000100d07c481d216080c81ca4107146507081c00c504480ca45401e94441070215202161040064500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 910475404 1250 910474154 910474171
    0x7030818010f2c0f061b12010608041407030804050d080f040609030506101d04031b080309010c090b04061b0c090f050109022805090d0b071b0302030d1e05 68
    0x5440ea41c1480122000f400c00740d450056401034416010109004500d01e0b40c04548809800100310201e60f82800d00d001d1120000d0704a07220030008106250001461405580036080c04009000e031a5680c0b6909d43c02e03400000e02c0312109101c01c0115003091040c000c0c0c0c0d0380c8100303905810a1a40c102199803504280e003d40c002402180041090003000d005d0607401c19580301c509088582004840c1c0000d03840701b035030305000c0b03080c041c00134040c14400c0b10071290030f03031514058001c1c040d180d040811040d003041d500e266255103000282c80690380100001d030101c85007080d0450071b00707142c00001d580300c039004c0e410304006801581c1514001f910000c8100003400c0405030010b0101130102c4814105c9205030801d44600e80304000020000700403414101d0341d503820f882c0345000300c1030040c0220b0f03041c018810881d8111040f00150710820a0342070515200d403490395158000a00ca08030751400b494006280500540c00412809291030350941120b1700d48400301403001d4060101d0015402180c800301d55030711 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 910476654 1250 910475404 910475441
    0x708150a05071106070c0f050303040f0b01060306050f0d1103030705010e062409040501200c0606040209010f0f091206150501050a020d050306120703030207090c0507030818010f 78
    0x803a00c19610529421000c10300d48121032202080303a60790b0340d000181660051040400350b580802185103070f4481c05035440302c2580e44a0606107042000301c522414100c60400f0390000208516110f0b209110449000400c1e29600810300070a000070307030241d200c06490b4907414006240c0c50307031420801441e803244200000200c500c4401920b03418050090004806521101c9072a82c00040075000f0301c0b250f10080756038040b19100c2d441cac168010524101511250564503000081c1d07083e200c0d01802c0190042401c0e01c1d200d03568001004204e2042906043c0441e102e4135400785110f10601d0030641e810300c181451800e05448003000250000507010840d044c50b02c4020403500d1010b400c2e0f4001c010070017803c00d241407410304840a0344030301d05c0c06408002c06c040400062403070b40e04c0d4031088000740314101c1640c20726902c07410000e4880455005001c07049060400064042e44200111241140c00d5940c61402e903c540e40d4042caa82c071b02c0c0800461540d240c20980c1a01c008500c500401e42801c41e4045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 910477904 1250 910476654 910476661
    0x40b070c060f050d0c11190c1d040816050a11040b030604020102100f02091207230a03020f040b2119150c02030f0304030c020109051f050c070815 64
    0x641044099411520810100d021040d81d0560001c0035134107030820b400000300d8107000c920340480b20b04850540d01030080c418400e10801d00b191110060708854020140f20300c80c0d584070300300c4002c40700d0540340d42071030030400100207404141440040d007180c0d08414034a44030800c542d00d07858a46040600f080e642c45410b001c0c044200d28291040441c180800c0c1d02500c02c3c2c2c034160b00041d4441d994010b000e4000f039125980c98807080104d60496680610051080a800045a0040f50b07510641d006861121880344e00000c01003003440100400441c5c018090000c0341c1c1103074280a0089000c480e1241c10548629030841d07156203501c0d28030fa80103d20412a08540e1007805441c1c6008880040d00c02c00741e00e000b03082c90103c0e40c0b5050b40105d0842e04000421812540c100c00c91441c80f0301c0140c20340c003520200a0204060f0f000d210b003071000703000740e803200d00b40360300c8408018440600900030001144d002c11200f0b0340302d01403c00781200403502c00a840c40c0954961840f41000020400050380340c0080041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 910479154 1250 910477904 910477913
    0x3081605060703051923062202070b010f1a0913020d090302061602070510020c030d0206010e071e1d0409050c100305090d0828020a030e0d0212090a0803040b07 70
    0x4000c011040840034000780d1445900301341154611000011001030070000070744580ca624010b11034608a0300c2900023251400c070000c43c0203411031300c807c841a0601c40c00016107400c41000c1d200030780d80000c003030324001c824080e01c0c15069400b06507180e0b00720700c0501c803110198200d480030b070414120f01400070407995501c1c0390090600c04010001494a0064030b00d4002042c0d0000f8001e06450068406011003d14104140d20781089810141d0f0f140c40f480b841d03c40700303035030204200d8100c502080d541c11a030b40722882e040e1440680000901604c969a02d006030b0210b10500b16400000400442075990320b2a10011070180c40740200c0555055000c80007442c258245030450041c020f4a41c0303410031140c14007248032900c58880d802804104068000030801d000380364104001c1040c00000c0d00003030382440c2c40994010350400002900864503000354203019407000305000020700780c540c1c050015210100000500d076086046540d03002031408002007800a01080200060a1044462900c0301e86c1c0c1e00e031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 910480404 1250 910479154 910479181
    0x301080d08071b140304050303070f120f05030c0d0b031c1211040e1e040c0305061f0501110a020306070306030b0a0212010509060613060503060a0b130308160506070305 74
    0x14070020048180d4104a21640c010b0b18500072551010b003000141013901c43e1149140150740000c2e901d40000645003041010442264046030b1140e030600e50b10940314102502e03d1182c0f503a10802003801000052190468400100b5134186041c1000400c0ca81d043c020070b18043d40a4607000746400c21a04903414543c100462100901802204bc03203000007008868080b40500e00c9441c8046100b9404034584400c0c0c0c3c0414203044014050142c60303898a828007401540e664030080d80c4500420012031090008490840c40342d04e2070b024100a0305281400444056690b06e40d000b01174041c0e0440c0f0401a90103101490280026070b0340441c1d22405d6040100d4407440140c0030f8624588100301c3d000114007400b0f805411150700b201d0912241d13980e1008500c00e445640c0703e404085288081c08102e4a030170101850284604ad248844920340320301006005209000e251440d9907460141000080e203028000c1c0300c45d080c40c881d10013100f101952403924161096030b105003c20307120030400906958080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 910481654 1250 910480404 910480411
    0xc0509033c15070503091908090d0f0b0405030301090b01022b0504080f0609010b0d03020c01261006030506010302070b0c1612020f010f020909060d080405130f06120503030a020a03110301080d08 85
    0x311098011f0700d00e41da0b107903014814290000d0140d180c1150800c00c1c44125166050440e410100c021003501d070034500703142c499009000304019145405152011075200045616902180100700740b9138a640d055505003802c8110b00000802c0010040400c1803c0c0500640c0d140c0c05441c4001e1401d800c00008d09801e4440d0700e14a01c1c01080c4590180010990000b01c82d81d491800b802d020002072070003000d610580c4094000c0c100b0f20240071040c0840890261885c808031075140d54100010b4444500440a0340f240b640c025002c1c042d89000b144401d0340700002000c110010703900c84031190210340e895500380000c031000040035030030030500c216400703e080c0126562802203030710851404c00d050300009c1c1c0070351000e800c007802503400240c80f00801007004106c8000d46001050305041d41704125100300030700800e440000c01c06042c04c4002803000e1001062000c542d80c4080a58119501c28041300002c1d00542d50050806444038581c1c850040088000d5002c0c28116015040d100242c81020b0242480035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 910482904 1250 910481654 910481683
    0x9020d0501030218040305070303020c070f030503090f19032018040c1a0a0516051603020118030c061202040e0106122f090102010b03010c0509033c1507050309 70
    0x4e4042100190348002150001030b03040c280143c840800c6c0c5592442c0c0302058210b04a801c044040100611000102508001e00110303010300a003c03102c8140941c0955051400003881c034044810300c0090f1284000d5035414204a130044140c030071000010321142c10032425030a901c00f0000910090040c18001c200c080d01040e0444e004418001c00b04c005a03110b2100100100070011880d18980075001e00a6000d03030360090121035108007100e0300c10400c110030344403c0780891a1210640c1c403240114000e40c080b203402a098004062a01e030080e00c0c0b081211030036080490f0b080001081d084440a43c55000e0314060b612000062805100c2c2001c40340060802862500c1c0140d1038140c80e00001011240740c00031080c401d0b10750450b040140e02520310043d10507030650802002d0304a0030391000190000303c100700d0450300e10f03111615240301d0580b01c45003511409001040900e640000c504400fa00d0502e00d04215007021806580031040c00c1c8060f51403d002070310000500017101c4c070802900001c003014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 910484154 1250 910482904 910482949
    0xc080a080301120f06050106021c0201140f070c0b0103030903021305090606010509060d18050715020d0806180702060718180e160b070c09061404110409020d05010302 73
    0x4940351424103000c140720740140c0e015445000b604000d0290b4003007040300d5100c0000d11403541c480c0c034041e440d160481100c50014058038204d0040c688140598500c600180004000c151551088031184c010300038486002c0c4400b441c22800081d40010245009500130fa0740c010840d81036104100789292066181d1107002e08040500001120118000790016000d0802c10303030f40c00052000c18264010541520101c81c501a400841901e00d0322507218031034440e40540c0c070907070303140c003600d99518401c5400c0c000168481540303070700810302030590f0a420800c02000d8080300c244414101c80c0c4420100c030801e005800100900c080c01d60030448071183d44413a5a0701b041003d0506000040c1e4041940040080c55107a01900c03a043c5070034005682602d050006a800340360303d807078200403594018402243e0540e514900003420001e58030030601512006501e28240c2c080c040204005040c81c4501d03149a01c404000008541c0b100340300612600a01904c04a010740c5180100507400d404070220b103150404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 910485404 1250 910484154 910484173
    0x21006090e1c1803060b0f0d0302071203090306060605090a14180c07120f08010b030c0901030905071e0302151e130f06031e090305041a07021503040c08 67
    0xc0842c81d03000007191581c0c1100310040d00d4030200c0d0001ca0070800c0294400400402000784001341e0400742c0b140c441a511151800c03c2e2000f40169051a00c0c80500103821a000c00d2082d2501b419000564500a01e0a41001502c0361960422a42164071050200c1e0b40001c00c5160303400d04000050040104068030402c000c0030a01060741c0d128400310098603055440001459544083c00781c891040e0800b80c941090720360fa07079001d02402d03c40d500c20001700d43c0000000901341510001c90f8850240c02890342d08040801d001500a00b812a00c00c6a840c010707a0004a002c1b0300e555031444105a080304200c50051550040c4030322005200c0400500b01c50410085245210034102101c0c03107849014800d41d0380e0319900c0c1200351000c0780c1d002484401d0300c156000a4950b80340e08000c001c401c41d0302886410070030302994401210440400140424002d000800000360a40405c04d40040c4050810382f030144a88d0000d654040040c0d040c405d1260044140010311a8400c00364014080c07281c02000c0104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 910486654 1250 910485404 910485431
    0x20c030d0504060f050c150f0f0106021e0f1f0c020a050a170708030405060403030507020f0706050a211a2b170c15060604060512060a08030a02100609 66
    0x2c19409007005009040c00d04160b400e116400f100d180d0125942502c0a26140002603d103511068419503001e0f100c101c00f04401103011003050f03049580c04d40040503092880074001e5091100c50080300711500400c0004d0284020520014208245400b40c8041e56050185024119442c4050003001c56004a900400007100003440315000c540080101c41103d030040c0b0748100710702c910500200311400c04014042003040028903503001c0c91180d10b05014613030720b5507001c07a600c0d04401c80c10b0113558048181005110301403001801444107a00d0b0107070b42401151245801d00e00714800c1c0d42e50003640d440400b0070b4040500300c042c2d400ae908580341038001c1c543c1c001e03680f400d50b01d5240b8201101600303007018041102d000c0c41c0341031030b2a40060f05500d03101440219a00e070350707101a058a0500100000643c3d03072070454103d6090360407585030381e4100440c401a00b204e0950044c0351a402c5425094003003500e0030104058001c5021603030045c4150041c0c410000b00f0b40c0c805903c40400756007410201d0f6180e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 910487904 1250 910486654 910486657
    0x9060c030801120c080a0c0303091a0d050405010f1d06011a071106071509022b0605130b13060b150f0901180f03020f031c080411060a0305010501020c030d05 69
    0x54010024043c80e928644c240101c140c41183d10601440c45002085420031034010a10300c2100e000ea291071011036900d840481c600500f40700392041e250b008201da02d01c0745800b6444a50400d000708000a200499140c034030003128149020760b542c801300d06221100b481d80801030140904840c04010241c1e0b01c6800c0015440d0040c11001003041c00804003203800742c0c4034001619542500030b070310a40001000444030f40101440b80b810303401404000c0101d03e84495030300402c403840e07010400310021745580e41c0314031005205c040c100807690603046481101080a00703103c01d000d880780003030058100380700b85407001c01c9440300041d81d4020000300e80c2c501022880c0c2415140d00d40c8444030155030766285d03040100c03200168011882d80303031441e2280c04980b200c216400304e802d4034802d48281c1c4440c0020000c15603070f0130446111507040408241c00c062581e2180e94020382181c480c52541902484000006050303800031011140000d903103800422166074108140d00e002403007503015241d80d160360200100a03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 910489154 1250 910487904 910487909
    0x50604021507080f0306031c02030f13030b04030e1c1e080d0f0b0f010302030c030109110403060905030d05070806090403050c120f0711060f091309060c08040309060c030801 76
    0x1440040c1110181a9907100c2110400c5034040e03455039807800c0503a40c0e8041d0360410796850307020f846401c1442c034140f20030392003501480d10320340c006500380443d001c203066a0703a02160f41c0d81d4a000000100200007030440c000e182c080c91081d01d86820110451041c42030850302c120300c1c518505904070140300400c070a24240a504420214603540c0c407581e41c1800c2220780701d10035003185c9080c41c0a201c1404e003220f80d40210b0300e07a4000c894034a800b818641c011000d0b0b00050b10041c5454600300010010a403841c2d0103d013054024510702c0b0f041c01c1e030b60b468440c11180049800d81c0c00d5000010001800c100c0d07817159951011039801c00c5085414010f02094141c03100610050134042c00003080f102552080001c1780340e0340c8017050155038804081c0d001e4411500700420440b44004011150f5600e07140950030740b090140c100031f0711414090104104038000030520034040127031fa80e0783d11000200716680560000344045407a9034200c0e05051a0042c0301142c0c5510030410492050440b10000e83d01c8a680d604 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 910490404 1250 910489154 910489159
    0x60c0605070c0b040506040b0a060b0301170708070b04031b0e0a09030e1002010207050c04020a021b0a180e0c010e030c043b100b010c0b041502270d05060402 69
    0x2010764421005944039905201c003d4405800b14040008001e000901c1c644528410440e500d46603c602e600344003074542074010000d10541c24001881800200314640c00b204422500700e0b5180356649603210700f03200041d001945501c200003814414051134040c86c01d543d1003a0800b241c09a45800150142200c0c0540815042503e0700b15400526100e04000604090003c203d81409003c850700a0b000f5400b03480101c496014450b41c0c0f0603d481c00d4030a4070325845480d0013421207401d07074860416100c0c03e0540480d500810750400440d54100200f071842403c0c0c59514001911221000002e2030035801c488a81d04114050f50b40c0c000c0f42e140403a00349190402958003151703031581e40c40d00500c1c1c1460080396100242408080e008801c01e4881000076030302c40e0006680503072101da003c80054500045003a408959000303040000141c0340000c1a13032141c02100103009030340c011445107042e42d120900c6801402400c1c106602c04850340394070b0300720224045807189246501581caa50700e821004102a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 910491654 1250 910490404 910490411
    0x307020d02010c02040914030a180f1a0c0d030209281a0415050901080702190b0601110d0e0f220b06191707030e1506040204050a0311040e0601060c06 66
    0x111741340e07900825005540004148410305c401301000b9925044070401d40005140642141070890501d940c203420303200c0d0705020200c0141004032803984442e01000e0408030420400071000f901c1c0c8280090b500c5100c003071b600580d0b1101c26104000c1d60500010018200c1452001c6d08918000d001034180300703c9074007000c000c0c8161040e196051a41c0142c0e4081503540340d0030a14100d84617405030091040d841c1c00d80314009103032224001244c0e141d0341c1d10020020040c031074103007501150b403e020541e80407405140c12000c15080709422130920040c260150041035001008003070714540019100400d0328180c42c960141c40c1072404240031398010442d5481c543d036450126602c1070300c41e137007141d110501031401000b04840038003006012044140d500714540d8400e5000c034100b04c1c0b00307001c0d80e801d18840c0d100070302c9003640d200b04010040b90050016507010768200b0000030191900d960700c800450003401c800c502d0310f050780c0500081c4c402e40c14442046402c10f000500040b030300200c0d6101140d40051002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 910492904 1250 910491654 910491677
    0x40f0608071e09180603050105160c330e07140a030f06140c070201090632160b010f06090303080f220b07020c0405151c0803010e040c05030307020d0201 67
    0x3503e00c0015500315482c603c101d1030718021150303101d0300100704030b03403003603008005590f038a1320329402d6071004900000000f010002004041104e034082d0030b5400150f1450110500c28420760501e0401145402900d880d0722840404d518500078000040180004450006020f034a1000941074903e5170100400d541e088240301028007009602504030400c0d255030640f99400d01e80110440d03034000c20300c22400500b9941c00414800d2280f034901c807203156410000c03611000184100b01408100078400b03d80d0040600075035012541a5a00ca294540604100303c0c0a5040040e50840031002da00300c2000e00155860400000b5800b095080d4001d98030740811000b0748072202102d901140100d02c05801c1d502e5200624140001d15141030b00601440c0c0803a000ca600c800140400d881c000c56a0350102c0412800f003854600301100c1c88000c008680000440c0c662869507004001d80083e00440b949990303c204010070407110b04c0303e80014000890096040c00303c1907000600d08142c542b4028104100c00000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 910494154 1250 910492904 910492907
    0xa050105180c2b110702090103080a0309060c09030c08070b030c18130b040506180a020703050d061205190809060d1b021011090307033005040f0608071e 67
    0x26548001d85100d00c540c83d00350303194140c00b0105142c0c1900860140340c2607503036083d081004c0c21182c0c0190701401805050b8659200c1c0d201c1504603441040526031920801400285a4403d078040c924080d16000741c201d046003400c1e00500b103203400c1030f03140f9030101105000c5a0030507420740741d0181030a0b28190352031407125480c1040340381341101d1903007084c0a505140380c0b4010315000790450803002d0720200080c5d030b0303080200181e900c503100090815822000c042440303103101d0f4004000e81070207424154580140b4a00000499040c1e62010105081c400c54450401005100440411041d602c2c004d5007a403281c0c841da2440d01c40e00d809d1900c140400110000f00b00003903044004004070054840340e0141d902500a52030b52404010505028542444080b6104130b5206807044a9805070003018490304543d0354009452180c28a410201480c02e000c103955006110560a0415591340c0c02da1614500740003125602c1254000e601401480b00810403d16441800808541092041ea05051204c2c840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 910495404 1250 910494154 910494157
    0x1e0606030e0a0f140f0607030c030507090b0c07030b0112050c1e040c1e0801061119060908070f0302010b030c0a230a0f08061909020102100b03011e0507080a050105180c 74
    0x4118070a400f5a6201c038017500340100c2e1180c0b0805103610248040c1a9442d0210111003007107985a0100b444680b0034030400003a04040c0920b2840130301111402904ca03282c501c0e402000740c1c0090100780c1c280d050501041000c0c080400180010f45040041007600d42c100c991000044814a00aa68894481110303901c141c0c4003450048508081c41c5840048510041115009003e2034002c1507003202c0c40080c00100140301e260418039100d002da01c49035070307030364080c0030744001d072000c1d1510303181030004001007010400c0002840b8425000000c900204505060400d000c1070368031886254074143c100b00c420741d40355000031040c1c181d19a1005403c5200000b030000001034000c0e000c0d0b01d9403000d01182c90100084c0039070283c11070011a0456100914059040c0e41c5402070090040e049220b1101001155070000c150315440240041800c220140c0c5000803c07000340c031244521601c0c2e0b0144401036400020741a0050960a010300180d03040601280c0414043c6401c0b0381040048000035811034003000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 910496654 1250 910495404 910495433
    0x9040609050408070201080117030403110a210b0c120f0910020c0706120c05041502070801051509160e0d060f09030207060215070801090e0a061e0606030e0a0f 70
    0x4820003107402c0c2403d000a41c0e82012400301c2c04291800d0011030140791112600a031414090b0055245c035086640301900d00f103071a80c1d11030304120308000c0401ca00030500f40d150b03054104211100e6000485040070f511003140541000d029900030001e0368074a20401d02015809003c902000f03e41d500e403d00c22510b01500501a4030320b89102140b14864100b01040010440e5070a50341d10a0110340302c007284080700c0c00914200c0103d001000304001104904031000f0880d409401640c410035601c5648509540d012240040103000c400740c2060540341050307910781c00440c10078503031a049a0b0140080d005425000d42c0754820a8009980020404da541000c190780b80030030001d0250307598618010b952040c05010318005802140c9482070100c1040c17400c940f01e000641d4030841d0607444c1c4030485004184614103017405009250301a400305170301d4003c0d400b00d8004615103aa1b00c01100c141401260801e0b04100d0805042078000d044c800400606155004c1d0002e2a11416003440c1c50b0502c1c2260b6041b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 910497904 1250 910496654 910496669
    0x14031204082d1603020f1225030f031d030c060108010b030d08060603060d1b150f27030c03141c0804030c05160f03060b0a120602090406 60
    0x88003044104110709000e030420201040389030519203042c100e04000e01103103109a40540e034003406041c8080028203c1d9100c807902034010b40e40f050020b00c90640c188481c52000d454025070004856200c81444c4051fa10790a064601001c2d0301c034400d0b03138014204a0f1b001c001c0f00c2010340300d000010020b0740f100d811b511a8002201141e640c4c0340e29081680e141c0c1000d21554072154640760030308480e03003004194080f40c08420b55541e0b01c159607074010000350390005000305420114070021800003482da51902d082038511003001f40d140d01e1400011140b41d0024095080800001d01088890340d42c200307441003000d0441c43c8018040c1c020310240c1e50101c4501d6800540552210b140000600010b10305681d850315074901545c10205428000c0c1401c12130b880d03040000682088002408203115551581106216406481465039120610444a0490f03040410850303400d0b0340c10030800c601c80c49180300b140410340c1c21803180c500c0c0c9801c0e503140712541d03038020b4070035500002c50021994440e8072880261068 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 910499154 1250 910497904 910497937
    0xa050a061512060504060e0a020708070b01080a0c080d02030f0d0902150a080603010603031704060e0f1e0f0a0201110f0303180d0207051e0f130509060f040503071403 73
    0x121000100b5040b00c0c5030085141d5460000c001c03440e0f08240c000c0200b992a07418001c0713010f85a450048000b9840000305643c0310400380116000500000d101ea070007815608020001c0d0b4080f42020341040305d6950200116601a0a20904564020082d1548500030130503030350b01c852490904401600c0403403030095111b0f0f01222074001c00180d25000d001503007865580c40600d0354420091608881140c013006d0b002c103a650001401d04402c4001079a4494418000400d96030a01c40390180381c10801c024a10264100d52001902042c5100074119080b0f2100014944045800c94054444405040203070420150207c0e401d000c0908100c00c144401099040326035034a03040c1e044403084129045404c445020b503002004015100060600c269540141468000d0079904500f020600440b5030f8260024200081102d2a41c2c501c9009650650706c48004219441c1035038190b420650010042c14008084400740b02c08548000213850340144d02c0a0600c8800b086c40011b10b1442c014412610b1080303d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 910500404 1250 910499154 910499189
    0x10e1b37060210020a050d020901110109051b04061a03041a09060420102001020d05090d090305150a0b1f020c01090605072303030901091704060203030a050a06 70
    0x1203031503003103a40315402c2c1e075101202014401c0071381c80b5510304600080c0d402d0103001181c0741c082c2d000b004500c205050190f44110520218bc0c05c2d9032054a041d59141c001882c40e0f80c08980d0009415000181200e00300714042c01c2c0300c0c10180e014032000405010304804030020741000440d044103250b0500d80e00e240000c903e495524030b41d803018111740494450400440c01a0140422401783c07041c514001c041c6005169200802c4491014281c144002c4552500d40400c06400a2004000864907001301040ba890030020b400c0c0b4004d202440282040035000040010650101d0385d03030542000062002c01d603807120750442c0c01802060284503401348520829a4070903003600000c50303000d001e0b034080e1410400d00300d005441c003a01d03511482010a40420128000907001c0441d92828001c40c810a5241c894001d40315207160803c46103035441e60355858141c000d00c50031081098080151540242c41d003420040c0027501d9000280090303001e01d031104d012a8180510760041c0002e0700c8562041c45030402c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 910501654 1250 910500404 910500499
    0x30221040201111603020f2b020a1512050c040501210f060b3604020702060f030f1504110a0305060a180606080603010c1b03120504060501030203010e1b 67
    0x79403920080340318601d51601d41d03155090400e02234190444031003a06100d09821007101080d00b1281074102e074012840100030490402407040c805072005039540307400300346004011840c121000502549403144080c0800c00c404d03039104807400300c16155130304485031948c880640c0002405818514a04041c10701d00f000c14010250740107003c09070550b5010401032402080010030884480e181d40d800011200c0c04010a814140c00170450503201800b01490407055020390200d942094070482c030070008100034042c0905002c2c2102c007540404407420055000300c0003083e0745500c00c4039620010705413100f00040d400d80d01c0d0105100107001c895040c502c084907008a28000b04060301031040070600d4100070407141d0405120707041d0302c0300840d204d8644140340c0320035164501950b443d0480801030030480042491036035024160066216000202c0d00e0b5040d48101805c1d200c04443e00701c129440042001b060750310f008030045400703078155036140740c0e0303108100b840704d0701c81c052185c0341112044c048848401c40d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 910502904 1250 910501654 910501693
    0x3170d11071e2109150203040302010f08150f040216111e060702121c17060402120a0b040b04090803010e07050c0304061206150306030c0603022104020111 68
    0x38030500d40250600300034000c05828607410080900035104006030380c03c07010040b00010f11280410f08004c03c0507a0356140c00e440d42003000242c0d0005810100c1e0820840d43c00660001241c0c5580c1401070071440c2c0180c46071070700362506c4d808074840c03500303002040c495459a41c102c0d107510302241d003402c00b501d80606001c0720140d002114035011700181d6211940c0d0fa041d0792503104c4c2041c0c00406003441c000594082005140607081c4500c02801260301c01e100019000d04098201402c54869600b160782e041c218410320f031802000640a1401000b6014014031070410955201420071030004a4040b090f0205000302900121150000d28200c030000c2440785407000340d4101e504900c04021696140c100c11200c9005010440185038410f2106008250144907101c981e01100d00001038400c1d0384440d003914038005440c0040200f0768450301841400b461601080180030f080c1000e40c40c0040000002d89000c1e50090b80a55441c5520045821607103d501141d010b4403441d000c0743e070101c900d225181c400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 910504154 1250 910502904 910502917
    0x60f07060e06180705090109050c042103120612120210060308070210030603020312030604090f060911010305060f0409020303070f0c09050106020d08011e0e010b0c0106080c0a03170d11 81
    0x5540f52001c196035554400a01c00058400141c034440c07090740381120910181501420715401c1c50414000420f2200c40070300c800f03200ca0500c04c4074202a810fa4140903001742140315a9040c05400c101d4107000c6011104001032000f540700034411011081d55108a08060039440c007040d04500300301e800400e004103a03000d40a6540201d84440b04964082d030168201e441911001350142c01103107001581c82c0560018503445100038002081d9207032075a40768441000c40781360450341c01d503131000c00c6c1050020020000c03102c04820300f020489403c040c40001c010211445180c0c0c07107107460781c00310320464405009603411294489407a246048840c035140403482100e01404031a03c1c03034000001007040c8001071030102c078540c1d501d031401503908101c103400d0740c400e1160400203005002c40000926400f10382185009100309850306c2d840f00070005003d0b00b500e406920010340c1c0c2e03100b40350b4404540e03245819002220b5200740c0c000c450780c0b034030304070100e25008410600d8203403450800c2c440307078940400c00140760 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 910505404 1250 910504154 910504171
    0x3110f0a0e1014130f0e180606130c1b030c050f03090d06050408160809212e0f09062304031b05031801110604050606060f07060e06 58
    0x21241d030128107002000700c644440c140041c0b07240340340b030f0305500c2488000d28003115010b08844010b5120000c0c28610007242d03000c441c003140c00d44104100000c01b84104081c0c130282c0f401810a038108080000c0c0b1402c48454219046913841240c0c00c5d0403800f41d580c509007034400300c5401c08007015606000d881070381020700581d4580101c1030780e034030401c0b40442200e11281c4010410b8200c81e103503865250041100500c11282d141080041e10300c84a0b5034003a4008851003052100d94501d40c0d0b100784801207030641d5105c0b02e164058500d2004a060104400200e05840c02d4290f800d03403038400341a100415074010320b180c45450b00c501003140c81201d8102c04480c5000382414420070180742d0030740f0068407002c0301044021080a01107070001f441003802c5114862a03083c03c112200301c07510313418250762000441c0b100d5503052018101c50303542c104d106a0340708264000078010074030301030301d4450b01d4101c02800e49104c2d00c000206034040c0c0390356900307440c5504c5c0c004408100c60f12072450b140f42d8552064030b0600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 910506654 1250 910505404 910505417
    0xe1e0a0b130f0e0114040b030303040b061e011403071818110a050901031505060f130503030901081f030614180304061d0414161202090a0501050a03110f0a 68
    0x42c46549540600219425421403108a030700e408603c072a410881040c407a4400d840380107003199941d003000074501a90003072207030895a042c5071081118030301034040c5030115080100050a420ba80000701c01c4143c1c51145003ca64039070301c40b0300451310400d100c444514818640180490921110f603c03003003003100a09020842c80b000510024401c6c02002c212400044003000009104d51103038003c01c1828049112035000c00342c0f0b070000101c01d44c001a400401d1810007040c1400300211211750700006010980c09140b4001020000030468a0010a08942d64140320404101c500945804070025030700b18001b00100550785d8801c81400c00241d8546003041210402c10038544408011141110090345911002d12a2500050b501d0aa0b1001c0c0903440340e40c440c01802081111841c2c40d00c1408001c0c0d00d845041803000e8058421030018240c500c5c46841404a2103940d00c41a801d00141d500900b490b50f1680b0b80c0420890140900000b070781140c2501043c0c80322110340c80b10142010803080d44401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 910507904 1250 910506654 910506659
    0x40c0f080703060e160210060803070b0a0501030b040f080403021c11010215160201020c010212061c022202070f03080105031009151d011103070815010e1e0a0b13 71
    0x310b0944025004544200d018140461881110340e00a058030300242c0c0180c071034200601448001312206a4840c0b03980b504001145400c00c04c000c000a07070310850382c2e0000c20003541961204801a00004d00040c6500344034403181c4140074506050760001e4de40101ba03181901501c00441041e100302c1c1c0000c40d0b41a855030748010403903001003041d41c003500d8442107840e2950348500c40c10500c0c91103400840d080d55403c01042014a100f070000340041c80c1071140900c140d0400701e0038000d5032100030401190840c5074041c40401a038900300d4039001000c03102011031440510b194650028861100003d00c20304440050108041d01f040070907049810885c2070300e0810500140d0715040d10b9201c0001040c4807081d008900f804005503003d81c0207106e0460340c0561040701201050708448682c0480c8240840c0801000100d5600c404a66480350040481348004c00507580060507406020b05003521494035844025141c443d40309090000800c007c040000c0680c0d10722036480341c2e900c8002c00300b8000b01e038400d02 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 910509154 1250 910507904 910507907
    0xa050103021204230a0c080f0601150507031b051b040903050301230a060e1507030e0f0402090a0e090f0304060813060f050a02090a15050d1a040c0f0807 67
    0x241c5802c0c118603101c111160303846580b100400800c1c40160012060302c4045040c0e080c80c208030b1070b160b96206960384a542810480c1440c0b80c450b41d81c101d4280740d40a00018002e2407003802800301502030f1402d04a0320789040d4603041d10040022129240103c0d410002c0e5018400005040a0075a8610041141c21b0760380034140026200041030140100300104010440780300c204561064030221103004400c14100440080d1998085500c041c0001d00520380401c407914011559400390b0000d1400c4515201255074007500e506082d01c0c60910918035070b611000c05480d150111070090000500804101da02c40031001110035041c2d44551441c07060b6402c1c0400e4001c0002158191055030321249060f80d2a0824540702007044601120713203039141d9101001010141c000e10b4000e89080743e0158580c8602418001d41d8115076000c80456040040c1183d15039801c041101c030951424140030519040001d0b40d1185c0756459078800c0d1700a171500f00307913960269100c840c403a07010314545e450030300b1134491050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 910510404 1250 910509154 910509157
    0xc15050f0d240605040e150d0312141009051003061b032f1b01060608060f0411090d0303060302060c0705090109020405010f05160c0608090d051c0c09090207030e0a05010302 76
    0x3c0d03070b01040e4100018000d280d91005a29480300300d03200c80508200110002c00c43c15407901130201c000c0b0b080025000f01c003003054094142106503e002c040d00324508171200c0603107401d032882080801981c900c0403501c10b42d003921540c030140d60041c005101c001801c0c41e2030374030303d60b10342c8240c000a45440d50b94143d4000c5e80e4031101440042c144c01103aa419410001c20007270703100746206c220300b280e5000c0c084e4500d002801840b00511054540c160a17191000070f01100d210040207862041c0e10701100d2083c41c021907400d451076032409941004021060746000d800800c01d82d0806503015501150303c80101d400014002d040d030310140c42c1c0c0d0f4031590761007410009070b004a020b6240804c0060308022003491041c005816002078030401c2c8000c0000301e45400c0c0d005601c9801680004518104000540c001000072900c65440e6162817031a04046914070301400d00352a1900c20326581741c040c44001244520074a00140c4058402156030b5521803038007808a510000190340104008440004d00c0e40c020710 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 910511654 1250 910510404 910510409
    0x1a070e06030103420903090503030c06150303070204050103060501060315081005040f200103180b0c0c01020c0303010b0a020c04140a0e011b020f0c0901030c15050f0d24 74
    0x8108440c009031107550200305a03441a25040e50040502c003041302c4800502800c2030390800520015030340e1090f040040c0f1400c40d0741c105601036441003041c20040b6200040081d0701844441007e54041b07050700000341948a042c03400b960041c00c000012090100580c0031604841190318100b010301d051b110220801c9046101c1c9040a8100903c02031443c901c0340c00c503a9109201c0c145200141c501350780e40b081440c1e0101c0130b00c0394000c0141c040d6a046c1d6014820039607030f40500321a088a4540700c2d900d00c02c100c07030020b0413000f0303505001c2003c40080200b501038420340000070040d00d4076036848088040194009840100040c40760701500c1c0d445060030301c01d080915a03c204010001c0e903600b02880e0207030810b60241446503582d20381481aa806031414147d2040c1913602409100310204015450008a00f0900b4810b601d1000100300180040b2800e60845e502ca1a4507032038071078141030540d0346008440c82000b500c1d0300080e5041d8005840c3d4803480000000341008980103455007a8807900c02d0090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 910512904 1250 910511654 910511663
    0x11401140d12030b01050904020c0a051204050303160204021204050f102315060408010605091e130f0209010e0610020c2809180b07391a070e06030103 66
    0x800c0c0c0b1040303284241c0001d07800c0c40c01810700303501d03202c0840040380c1280e00006a66409400407400d003410050244501c007508101200f002c1e040a0a113000a900c0744108040c0c1e0075a10443c0099401710348540d010b03540700754070840304200b85280c5400c200d0b8403404600c0c1098241c0c015402e80c600c88130a244901080d070440c4088a0724507109004d00da02030044040e040104840d0582100301c11580e0310350050024000210010502600e814140000d4036030142104030b0309408000d1040182d0805100c3ca940a401c201d4140c9240080d41003580c1d041c1a20070010350001e120038000f081551520300c2e07281c0286401d49040100340d008400898071001d03544030a6034442400204210911042c4000700c1214600b21069611155034200b41800c0f1902e222041d51401e100b10a120180094171411541c8150142402421140f50304c450760b1800a10903000b078020b615480c00280600002e41020070000d5010648801014500741f00d44e8a500301160308200040c019200400981090303016030381203d41c032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 910514154 1250 910512904 910512923
    0xe011415360a06050d0e0a02180402010c0503030f070f3e011e0c050309060106050d0207051b090a0c0507150b03072912040f030e03011401140d 63
    0x7159024024030503845400d14400503814603800c141d50300d03000780000818240c2c0319999514143c103855000c0d1400189070100c2500000c0110026071250340d414010324100034000c2c441e50741d40707100603500c4150810001e411884003000700b00070034260b034250f24085c40041e00d82d0503550003240022101541c1105c42c9042e001052800390340c4a00b04542040840c80c00c54122002c0181050b100303c0c2101d00e1210940c0301506580000680075600d440345407004203040c038040c0c1c50340c84c0c0442181d54a00c010704c1040104000000d104c20201d981e5410345040c0c0b5401400d03149144e40854014070459101724003107110b40c605d100462001211846240102c20f920f4980c20b0800720303a5114800c1d070034210b101c1c1c0c00c0f031143c507207400014541d010701c480d070b015141d000f0180da603260040340c0c3c20036260b80f200100300f4660b03c100407000700590109040c580c403a51214018030440b2007481e0031a064000c0140c0240c05d5800c00d401c44020584900e83e4030b0503a5007810742081120481c2e41002410030800700e01074580000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 910515404 1250 910514154 910514197
    0x403050105180c0d06110c070e010b0a05040e0408040b070b06210a020f0f030f06311b0b04060c0605090a080306060d090f030309050c031b12070e011415 67
    0x90103c0b04c0c91040c1e00030100006c12809900c0790040b5079210300100d03502da8101c80780034000c030080391518501400c2a0300c292803c0c000d142602422521450051200c0352100100050030480100d00f00c5003c2c09142c0516500d80500d1318260012110541e00640701d80320107900500c20300441c8080402d1199464000c124901540d001e0188180801c0c4040340c0102c07448002e5102601d04005000b40a074410005141620b040c104a000c01a40f6071000d03000b240c840d00403400100d441210f0f5102e10f80d002110390380381c1031103000140b0b003028265210350300d0400c02040c00501e15400100350801c0e64004c003014012940d8103200303a9121040320500600081040c03000c26141d0414002400f2100c08443d00010701c05481d0310f404e1101001e180044001940f58402c4008000c2c0a015520411000703a008240d200d80c07402c1c2400300196050203490040c028400342050040041001100909412141e041c0c42c1d41c480e041d8943c004c1a03204150b001e44d60321261701d40302c03904403001c0381c50142042404c00040301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 910516654 1250 910515404 910515409
    0x121050c040b0a080601171902090601080a0914010f0c1b08070c09020708070204061d0a05090705130911012c01110102130302030d0c080409150b0f0403050105180c 72
    0x110181e045411504500c00883c0c8034204105c0c00b170113059034440590094a40640d0a80380c50000c44a44d00711040814240c40142c5074400d5158000d0424240308069681d140001d1004007544032000e003181200c00040701c24450103500034011102244010300c00f1320866402038404080c01441d01901c145401d1a800201d030740304018001d42c034491100b48206a035602840426038000707500c140d9a0740c41c0020a002180745c1480b840c4002c010b60241c40c54010443c94200303018050003030800d140c42e40c032100080d4240c0c03010f0104802070320b401008a04010003800c0390b100140031814003100d00c02000707150b095a6600882090080d0086844c1e81d40d00071021800203205811000f103807a050210504401805d540c00f80094a00c8119000000300b6280c030714010140b07003003000345c000b000b031140b030a50a50110b0a00421101038a03000b107804600c0780486030100301c1c80601c40d40103030301c1254041000da0990401c3d0004000b10381c0640c000b4845925406c00c505549441c1d5250150507a1141c51040340a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 910517904 1250 910516654 910516661
    0x7081f05100812030604060e011214011d07050301060b040803071101180e090607050319020702150f030117010b0a0e070c02040203010b2706031803040801140121050c04 74
    0x100c0781c00010401070380d20300e41c580c6000e03845610071240c00000b1040145900306441168010181c403c020756081d45055801186041203110241001100071a20004501d0940000000141408280382c82550012626031100054040d0074444d50030001c002640b502e100043d101034801000145150209590340c00c3d032540840f03501c5d14140840c01c0313145020a076010600c80f00804150b0400c01e2546003c3d19618100100100708009010060040c80850421082c01200f4504100342c0141c0d1186030f030000404982e400103d250101c01d0000b0201c3d080c50400001e0350403628260903000010640c07120460a0300c400319061a040300303101d6020021100c5651405410042900704604041712540205060b82c0c402d030001d08100f000020b060040c1008204440e415017a110350030000ca28004000a609100c00780c183e101c1c09034100e015504181003130086400409426008100b982d8071400d410601030824440c5581c41d10f0f003d442100c990000140d0b003030aa40d4007034040c0c1860302144041000a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 910519154 1250 910517904 910517911
    0x5100c0302070b030a0c2705040f0b090108151501080601120b130b120601120803090f0109030e1203093312010e06010c0b07140f0d0e07081f05 63
    0x1c510400a00040d00c00c10f030001140610000c080105800101d85006003003a00c48a2003407010001001d120014042d103000310b08140e0b81e04a034042009813200030114040c00001d601140c0c402c01e082e00010392003000040b8080400040300c40c034500d03a0383d40817444840e50045581240031a56140010303205600c50b030841c40c003040c1c14240001c0d44250010229140e05030800003520b490365a44c0201c5143c0c41c259810b8404041c1104c010505076040081d25821a44040c0c4c00410008010021411481b0f0a1204540e59417005008000b103024074200102030510880406000301c0d820749404a00e13541c04012501c6d10500034010440407404201d001940050b084d00804d00031032040000540603d002c2e00070702c190039021010440c5035040509407100244040c1105050003a40c88005000401006a040e403020040c144801d803034007246c260511a1080b10100e01c9807940009a808084034180c0c03000e00144400b00072154041d4489884c2681c03502810415400840200c5982c0e20403102504002c1c0e2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 910520404 1250 910519154 910519157
    0x7110a080d0f09290a0209031c050c1204031e1109060102190308100b04050a1701021c1a03010e03120c04030506011d070c030f1d0310060311090105100c03 68
    0x50121150b2100d0075807440401410002c0c000310b05a0f004c03511100115280c0140c4a41002c5107070041c0580000d64940e054400d00c0280c500007590f030400c040c051401d0301e0750304004406540c0d01e41e41710350202282c0e5000e400210f401714841d070b0300142088510f400d91142c0d00d5000f040d60240c41003420030014000d40003000c0c0c1b4114881d501c6085001c81c034000c5c91066461080c0c80d00700440c01e01d0007504045141c075800c40300b010f60060004011076130f06c421062045681031868003046612020455029220720f10f4840c8603064001c080740741050460b400101403544404140c07800418007000c040c26a510366008444581c400e011110024859560f8250040010002146401d0342c80e610a400d085090b8000f51400b407643d601c0c1c0c8030304100321550070b500084910740b0002103101542c021741440c102802d40010030520040c0450003203060041d02820010080455a801e0285c10984c00a04124041111401100409081c039070030081d80e0036042c0e0340000c00c01c0549105031442111001d108210940 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 910521654 1250 910520404 910520411
    0x30319150915150507051504030905060d06122117010b130504110406080705030912030711070b0a26010e040f080705070f170601090f020903060c0307110a080d0f 71
    0x400d0f000100d00100f00c0000764403400e0b114201810250304101600b600920710310300c00810000002d91000115007511011142d054880741c45941500082080c1e401c401e00b215400003d04d000e0002506100c2072102104038000728005d14240221101d070b4030525240703003803040d40005102c051400d601500203850b020211326003295807480050b05a5840c1091803c4200000505210343d5500c003003c04e40c4189241071141c1f541c141591074a583c0c0c3c9842800040e14400800880d1005200e50600c0f6504c01c6100129452a03884508450040c2d01c60701820300802c00000ca105240384020701480c0c0111840c1c04030042c542e1800588180450380144221078070004070903880c0009a100b4082c2106500520040110904100c11400c000300c560f0007a900b040152021000119000a8403a040d12113107240892417540e00d22191029004a11907030740e00d8081c0400f0000c803034003440c010f0f6100740d0f0103540302c5803c031300305070100c1d915072120880181c0030441c10400b07626504896049a09404035421002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 910522904 1250 910521654 910521659
    0x10b030615040f021206030c100c0b25180f030f0f03020c06160507093c020d05090c060408030706090807150911010509100806060d050108030319150915 67
    0x201242d00c645c1c80296941c943c00705025441c18100a91590070b401541c40b00803d9043d890301901030391201400a00c501c0f555000070f140a80800e190054000c0d8000044400fa06412405429104142c524a1042090840000300450103901c1c203002c494000c4040c19200119444400d00308807103a80031b90961050503000318003925540000c081c0308a9500f10461004c03c030b45442d50030306003541e01c800c0c1040c5c04c0c00741c07800c1c1103802c800d10100250221060045000c01c11400102c400341c3c0400d0741c0e4003a920119100c000c81015420161280c03011100382c0f81c2d9110120104030702070140b40120380e01540207000782d000291156114002040c02100d010303040102c2a510340804000349a2542496a15011740364104140300401050384502400d106d424041e9010201e44130401c24056802048000340110b6801d440300404ca41c00e11242c03d00520a82d80c60b10900c40c2c2d00d504c2038440c544460340c40804106101018462480300f00c0c0d41d040890015498407590703074040c0022606188040c8040c9000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 910524154 1250 910522904 910522931
    0x70e010305100e01030c030501060603200a09180c0311030c0a11031c020c100504150f0b030a11090a051608070509100207060306050406050d030305070203040e0907090e010b03061504 80
    0xc1500071803180c24010311b5a8250b282079800d45a442c1c1c400d80c14181481c40416444402c6c19181800010466400d81c544502e003001310340d0b1102e140e01030440758500c00c4401034589025044103100102989040c0701d40c030f4001c1c151b0300051000301c0311010b00850030b000c1500301030311440825481110600c122410002010620500c01c5071854030743d020700703600007004010300d0700500c54203100c122103c90800261070326032200130500d50130700c00c2d030381d4a00d030b4580c0e0490b090341c503036401030303054942c0038041314041002898881e00f000b0030014181d01c1042d42d0360001d510034082c0d000d1148101c04d0f515090144411180041d43c1c2210301070030309000c1c04810711100c80c0c642c8403c00d0b1175041607165401131a40a18281016040b2400b03504001d00590801c41d0622680c0c4480308100617103603261a0018081c0e454823400c070301310b01846c0c000754981d102c1c1009100703500c0000079201c1d0a580d84076800300501d00300380001d9403c07181d03002e80094041d0041d00001c0c40c1600d0541510520383c1c0081c1c804102c92507110074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 910525404 1250 910524154 910524179
    0x1140a0c0c0f080706080c0a020703060c03200a08220b070c0506040b060a06030b030a080906040506030108100f0219180807170d020307020a0b090d080313120206070e01030510 77
    0x243e64488101041029070043c0c40c0d680201d203072826581341102d100c8000391034038030501018004584801c1c00d040c0351442030707000f629001c400c000d081420121400b03103c283c9034030030560b581c00640d9100102d0201828421124940070a065034200a00444c1e42c8520401c08000e000e40c0032310001c40b8400c40481c40a0240b14861803041c032841a181c075044081100301855900b01e80101850001e025a65403000102580c4054011403855111040c4000040b024410f507045240c00480200c00002ca004000071000f07070700080c41c94103101c090f000d00c1c0001d049025440ba954118240001c68140081c020190040701d44100720b80d40f00407e0300c1c3d0f280145080702c17035841901d01119070000b50306a82024054015040b480d07102440c81c0800680014004140c54044c400d449880007680a40030f42e50b0901c203003c5140e1121140f5101e00d0091200c242c1e020b00004240c9018a00c8403132140c50900c0820100d10404080e165140e0303000080c40110000c1c10001c10003079500d050130b04041465481c185 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 910526654 1250 910525404 910525409
    0x60b030319020f0d080903120c090a03081908102702180906180106050a120623151b240712020f0702010f0c060c031a01140a0c0c0f 58
    0x10000e000e074a82e083c0a151600d00700031942030800500800380304145401104881200046100c4060b2985481410104601c54034442680c0044800400410440500c021346920011a000400020450b00081d5034104085071a5141111110410301c0700401c020303416600d0354401441803a807103103044204000c991104082d00080d03c4440c417400e00619100d9889030780b12105481e420b105103102d40c0e00b00c83c45c0f0380600411052010100d6041d103460b02c85c040318590004442c070300340308103980c610890031500960942da1440f584101d11480c20ba00303124403042c080541d0010b04615010f080115829100581c110032465070052400c055609104014100076100040103280000d041586016003d45c0c005180c450308503005018446201c01104240c1d0003140d020301301070704010310340700080b903103000802002880d55180c1038005030a158168010301c2c105051b00001c000004e805070040d43e0a1100c19010a2120420484800e00900c01e0f1074000500d807103107103030081141d1603081150481c000ca8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 910527904 1250 910526654 910526657
    0x40b0a120f05060f1e010c0314032503021e030a0608030705010f0c0f020c150d0509070918260c2e14040b0c1b010213060318060b030319 60
    0x20024400b01d4a040d00345551305034411a40e044000404680041031501107000f024103001010070b190082c54061141483c03207584220366150f60340380c075010340f444984100c0340003420030310a05180d010540c003074402c5a00b0900075070080d40e450340d000307664051150700c000c0420320301c40d888250025010900f000075050192103180040750950101e070b0950201d50030070b0300807410041c103154101c0c0d1454000c0340c034115140e01580d240c081440f0f06104403010f07206a02d007001c00c40d41b03040104403c00001180709810388e00095401d0004850685444603908440100a400f6054003603001d20710101c540c00c210403c1d054210f103141040d820700072160070940003440031f105030508030012180401045007444c048072080c4404204446504039084c12182c0300a000420303460200300030807020f9000d841034440c42408041228882106503c886020703420003569150718540c48403012680743e000340038610b107030202801b0303007405400591110000f40c000300e41c00c0c2e038250208111403143c0340c03c44a250003e55916 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 910529154 1250 910527904 910527911
    0x120903080a050a050f012c040b060f01030608032d070f0c050d0f0f02040b040c11060f09120706020f0a03060510030504050c120705090f040b07090b040b0a120f 70
    0x250071032401c1d10b00040103110180d1400c41080030384810028183d0543c1d0006c1200d89041040c200b2a41010b429403060141d000160030030401004990389000d44241b03000d0720000b0049206074015410740d0050300071615507820a00ca900590712170141001e02d442550101c2d0041024503400d801801da108481c241e84982040303641e0814040b003070703407800b008100658007a0401d0744030303031141c5a41c100c1280c0000c0440c1d400004010075980c0355080845040340040081225090115002c1c2a01040c0c841840c0d1901a480025052480e1070b81854880c0e270f4008041c000c80d0329000a80c0c0c1441d840210106d403025070900c002c40c2120341200242828000f02d4600042041c1440c04120002111070305080406003020100000030f500429201c1c400441a10788255800340c150583d400e2424540140e508090200200054040900c0c0c0030340c080c134003c030104e25a90300c8030341d000c50710501c450084600c0b00504000400444034124020175500901380703030506c116140d09500005640c2040d038070442c0541c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 910530404 1250 910529154 910529161
    0x60f03070e1e070e0d0303020a030219080a0e010e06151f08180610090209060f160c1d0103230d020f0c06040e0c16050a030210231612090308 62
    0x12100e001a8004903c1d080601401c040080064900205080014100342e00840e080b0411406901900c51000c481399080030b0107200800001c0200c00d08039000c03d10315041c01c142e08203400061145c9203000c3d481001070140c0d40d65615015900600700030800f40c000c130000c1240751610918854451508081e95104801814015500040860360303110045054000c80240498000f0b514159011209829000758403400c03814002040342c001d090010001c103100181081d040301070300440d25905485207560100c2292180003d0084d00c04444224050740409001032001c84c80048a03841d081c08201400c204103c1d00304a0241003002100c03c01e400341e405820f81c01e00200f01444425001c003402d071011824075152410f840c4502c031029000014501c40040c032000c08060300c55140303220702d401a04480c200c12407072030001e503078070341d01031421a081d1320f40020010075103030f07003245c17040318a107002501181d40d00c0303286a4040d00c004440d01081484003010540d0034105c02806810b00f454065142c0140130328 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 910531654 1250 910530404 910530451
    0x30c010b010f0809062410030605210d0c050a0c120212031c150503032805070210030b0f0307181503081b0106031502040602010f050f060f03070e 64
    0xb026150326405018221081050100000414540c0300c420305070034603d03100d10705400344030214188440d69044940e00320390015442d0581c1000e81110801c0e83e4946200030143c40e80a04410006c100031aa90056128600854411142d407c4c1c014001d0068898203049903803090303031148480d808001814081503040082d072074100c075a1000540f2070009580b51505200031301000b8070b440711015560680d107160b10410154500b91080140c03c020f0300700c0c0e640701c154000000144140d654080c038041414903c0b003030f24500c81d4080e20714082d806030a426120313078020f4058001e0708e0040354050300044180d5000d03040369810002800240380c20340b110341c03010700b00146060a56074912030b0084404010741c01040040d00034802c40d00420305503503120007401100c1c6a072a0141c9101c2e800540543c25800d50b04d000c0d12520f80c010400c4449a8008000104026484ca820388030225590541c0b4000d1200094150504d10b030f08a0a207036004054401c4151036490100000c07209541d00070318451296040c1c003290 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 910532904 1250 910531654 910531667
    0x714130f0504230c070510113c092205090706140922060803121303120e0a0b150907050c1c05040521071202150c0f030c010b01 56
    0x70f4001d914035418812036031040c071a4600d01510042d140340c00004c60205020080c095500e24107078080702800100f001c0701000d07002d900240060808003003d0042030f030f105001c03810b0740c140094480300100d0400f03013600284c090b540c00220045801c42844400ca00e02d1402d00700f11000010031316500041c46040090b0003e01e88000f41e0403041c02c0c01160f0700c040c1008900c500c141c1d0003911007101c3e048101510400c0400240420803082d42265080036404540701c00048060000c003800d20803051800d40d41e44150010104d80079002801103494040e650b156040c054000310a0140304504aa074018072580c0c0d4481e0851046444443c7e40030307080c0d10150a890300096254101046107401030404088001c16501d42c031005100a02c1407000d01030381202c00e0f02a200341d40c0185070040800c04151111248080e0072180203510300c90500a0900204a445034084081700f4076401900605200001d858115450b6010b81c8040c6100d11990f2030038466240e0410081200103629000850070241902c0090980c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 910534154 1250 910532904 910532921
    0x80c010f030906020d0c12090510050705070209010f1508060d122106051201360f240203070e0906031005010f0602010b0108190504030e030318010806030d080714130f0504 75
    0x2030303600340454223011900014103c10b461419040c002115150782900f5103541c420707948000d400080d400f000162410040c2181800c90302011440300c44280000b01c125184842125125480f2082e03100c40070101d00249482d44444455007004030702000040f40d5220b07903441e1007426844042d1200ea0910080c00d00c5000301d02c0e0114410000d0044000403d0340002c18104800075812102601c180c10808500007910441503c0d0448444801c107001814208000c803404802041c480d031904207100211400c601c2107a00c50072050b902c05404040040070007189070b0000c0d2041d036140c411050320b8241041c071842414000c080c0710300c23100c48003464244040e094400000d0024107101000040186c1c052005980903801c815070306000035155181c0c901a2986120902c500e070f0148408100d07001441d0440150a01008090326480d001790f5031041003558424004504e0f00005205801041e090380c00760043c00c04074104013040358140701c9070174112600f10342c81e5070014400a100440400550925110f014071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 910535404 1250 910534154 910534187
    0x31306051f08030301080d120b0a09050f090f030f0f0c0d0306031205040b0301272c070b0a110325031440080f120301080c010f030906020d0c 62
    0x8540c501b111840e01c4140b4502e000f002d02c81e00c0c2c6441c0d0540c05507584a141103201c02461083c036070b40c0f202e08010041004846401380716900202003a0301c1c107400a01011314101d844010351804600d5101048075400ac120380d100982c5061159851828040c07240c140d441149660010380359155051650081258000036400e00200301300030710150702c000088a054551b40c8030f01d8032101880e014102c001e10001d91640c807100349002e20202c0144918030002c2c0c50820715445500c60b0380c10f00685035403982c03140d00c00c02c041b400c010088245020b000d103203c03214401400003903c2c18081a100c2d00d009c000c415031250448440802c0c04c07103003010f4001584a6503445840c017450b0408803199081c40c3d0034900c100c00781d2a85049100c10741501d2a04210300004120710031050106103940300920f50b40c0d0104404594a14022071042c114415004010749048a52443c005c1020201600041d14004861800403040584034078041c00810940e000030000442032280c0002c0303000d00c0080050070003450788841d41c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 910536654 1250 910535404 910535407
    0x13060b1201140421080c0a0e030d0305040c0b12060f0a030b070504080d031a091017070f08120a08070215091509191e05010603050303011d0105010f05031306051f0803 73
    0x280c03241c5d4403024007a8001140c0802d680e40e02e58544e01545c01c82030111040741d1522030410055403541d8103810080c0903e20460805d9407160b110b00816201d40200c11050481001c090700148651a010407003414040018003c0d015068580e260f207060b03124116640400b00d0302c00102008559001c10600f0103110880c81d04010401800280c0080318040d800c19a20400a0801180150005181080c020090100c0300040d001c05005400c2d120041c52184051038003050500045d070801c00300c3e13042e00c154031121003e4a0004110815140800060b10050862041e81402c21001038941c206a000b00118001014800d070050b000707100c00c2000800c000c0840c4c20050703071492001c40b0b20720074086859004480c240b1902c40c84200081d4401e4583c8090459803d10100105229000c4003c50681d0800385510b03060301d10304070440d03960241c00c8c41b0f00c5000601c1244107600081c0300b08003442e0006501c0004040f4040c094071000103a803c00d1710813504108054003607541c01c404428045006003203290195 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 910537904 1250 910536654 910536713
    0x20d08010f0b04091d010203090a05151e0a0b0301050c0c06061906031d0d18140a0306050402010201023108070f09090215030703051503030313060b12011404 69
    0xd006800307644158241e07540c440119045c0da13181c0412181100540e100215140d16068410741e40c0c400496034151050301a51030003c07100300440c4541485400106c54401c00e2030000c0840c501100310091140541e10399615582c1d426590a0240e030780202c040035401500d5040ca518407506210000c0c00b0745225111580c9050494a000340d1240119025800c1c0003404031061800307130403802c940d40d84000807401203504490907241c2200c21000c1c1c004555502c08091510782d41d0104050b801401e14580c03200e00300d501040004c0d19900443d50191061001606188501900e514010251038031070107042e01c0b001c800801c07031074004d4588000304030346030080500f11703c1c08011305034001c600d014000949884034107079400d41d2107808802214000700c4080950740d14017150020003e10741520311901c14441414803040c03503e0000252400366140f840303010f00d0300d10242d9401c0c0080840441079a00092070600e58a02c501c1c00b0320070520040c0f6041c490080e00c2c5042c0c07034820070340c60313002c12002d52000d02460f21 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 910539154 1250 910537904 910537919
    0xf020f030405151c1512031e03090f05100c05040f03020f041d0d08060f0915060714010b1311270307030b0603010b03060103121206030c141f12020f0f0307020d08010f 73
    0x550201508c0c402d4144081e25030810440141c1f20030040600251101c890000400c0710004a040d800351010104201103240510115210703c1a07100e007400750b4440c00c805201501d0110a01c20318042c00410000301c40344440c03e8039000c01c82466040d038041e04184049122940c12205d090f03845101250944c207030300c1c2c110001403003401000d004900350032400310290050340c13140030448641a03002140c5c00401d0118007182030281a4251540b40646034038903202038031030028010b00c2150006400900c0c1403080400c0040351403a440c2020708a8019568210032450b241402000301440c0078002802d11860082c0078076081d01d800400b15402940004010004070b00c0b90032456250303840c980303414101e4609080e4a1000740c5000d0b04040c040b42031211000406079404a64440034400c1a241c0183d0141104991200b0203081201c0c5004200700603003d4461f1035070b41d802040e80888000840d424a00f89400c1c000d0b19400444054006d0303440800c038021800d4101c9940343c0105134104071905820300b003090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 910540404 1250 910539154 910539167
    0x80709030602030618040f0611090a03150917040e0c040e0117030c01050a0507020c090114040209031c0305010303110304080c0105090d051c0f020f030405151c151203 73
    0x545a01c2e03011010905030b54405440108561070751520781998101410000307403480744410102c0d0400d01d801d8a81843c1d0241506403a0040310090842051500d151240b407041c1c4c0c2113000401d2015500c182540002e256040c40d02980e036400c5d07246903101c500341800340c1125003000e4030554864009000c03c0000640004800e815681e420300048840301e003014010745075000e21880001d03194200020040582d5032a80224800d071541d80c01c030b807285210030017801041e100070b0103003450740500000c901449050680051031051000b8003110f903d6400310b201d0a610b101088240000240c40c0c600400038181d00015110302d013401c920180d46013074900428182d40d0105101c6e81414030002160a160941c5c500010380c105030781080c1038503039030503e00c08800228000301030f20001144100903186034451000843c240c81d81001d000035441d060507c0304100310078a0040c40c18519640420014004821a80086880850200740403518010f042d0405003040c01380d03005180640c0b03103003400380e011030351081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 910541654 1250 910540404 910540409
    0x6020102160206070c031502120606162d0503031b13050d020d02031605100302042303031c06031208040b4b01120521040e0106050703030507080709 65
    0x4030f1541d03440303100303140c051140c1e2816480a40542e00981e9042c040d90103d800410b008071405100715029a0303000100a09406811030303090014154011400010b8030703564442c0303a0200303a511802c81c1d4000440251140c07010208040703031150008018000400c032044101ea040c035075801320301da040c40d1342028034a14030002031050500c550109180001551101b00d07100c0c2030a078005d0203a40020307040040095001e1501d02c54540900c1c200340801702c0e103c5c840c1c426141038480c038400700146910112081c02d2181c0a480080340d0500040064001e01c4c6910790040c0d5182d00680e40206040345541004004180f50461100601c0706180030080003509913845168071201c1c04010652070110360f10040100e0301060444c020032008079030b44800d038000c0329020024044000c031000710742c0c0e0781300d03651312112503035000000340b066100c940014400c51030490342401915544402c1030516584065039251880213030b10890210b440003c451003411b03858014241c3c00b011904101d0b906041c10b0600800203907062 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 910542904 1250 910541654 910541659
    0x71a0f03070c06060602010b0a0e060f010507021c0b100f0b0307120608010606050715020a0203091003022802100605010503060d06020d0606051b06070c0209060111060901060f060201021602 83
    0x1000400d0140122000b00c4541e03002038081000ca9100e400290003001440c04491041040c480c0018a282440e111140300303a00280100603c040c120303006441c2600440412030740200c020b11110707025190249240d0400303005011079000d80c1005405800010055003101070742c0c1a21160a2103100f00c0041240e40195081ca4002c1100b0030050755000200040d4120f44400c1d400c0500000b121079000002c0c01801303002d104c22058200314210b1090413441026108405078100f4040c1d4251403412a038429038444241c00c1c094504404035a880803058054080450302203034041c80c04900650400592501407980c06d402c004003400c2c07100190081c04020100c512500000710440c0c10000a901912810301c10310105000c00354039158040c145400602c0b100181a001200c0c054444000145060050401ea15070750b0701103226070213020321004000d00c2541031080001e510602d40200700721685c422442c82c0700001c1c07054241503141c0c400108941c00841168010b102c0c0d914030000e15483c030b22150350704 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 910544154 1250 910542904 910542907
    0x11210c09070e120304090c1d0f010c1a180c0f060c010f390507061116060c020c030c0108191d010902010822141c11071a0f 54
    0x107041c400c580c4900761206080d00018002d41e424141c9800201402c140c0d405401c080c005240215004c070741032070180e003002c146207110445001e000d0801c02c20f006808003041c5002682e110702a12800d002102d030270b03110704003280701ca42040740f803191608400d620301c41e460003c0c0091403035403c0092001d000310f0302158401c0400051000c2440b00035070220700100d011310024000001c4010405c2211501d603829103544504000c80417802c0d4181803d2401e090405031a801d0501d1402e40300c5034010071440c4800100307203104000c0c00c1c454501900c00130150354805c030400300b40c850f1840e200a0400c20940c031030034000da214201d4800145e8001d0640c40e444042d280e262800035000c401554003510306003c0d0740159100180c1111071204041d040054158001c0e240c030903068940c544160001c0d2404200c001904000f8900381001890302c02d03056100c3c040310001c581d0001c858180d1790060403010004080864202c0c28030503500d5000380440c000170608185c522150360035104180d01a44260720810319503810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 910545404 1250 910544154 910544161
    0x1120212030c01060e06100c0c0b0a0216090507120204060219290a061a0301090207020a03151d0c010c26030f0405061302030c1504050d11210c09 64
    0x90410641d55003048500080c1300840e0b031391512001c3c0010581d01c0720700600030135180700c408500813a840d0084650109185031441d02d8554001c00e6908541a2003045004d03042c4800040754007086180c01502d01500009441d04103c034000e4100e00142c803034900b0700c07401800f0400203143c002c94803014114040800607500c90403403030122505102026461000e004404500f0140b08089050500c1043c1e1504100403203a110700c620600c9100c03000d0780c102e88800800c0140a5001a500600003403840a07080ca044180c80b80d840340b038002c060040050502c2c2d692050501c040f030760420000035500101000e0510392481c180000e1a000c0d8918000c0c250300400740e0400c400441703510000d00480c44041d002901c07800d2060740303406100c5083c0c8040d51a4032801010440310400604408481030b4001c000745070441d4003400380501e8225003203036060282020b2000260300d4488540580590780b10700030081300001d224003080405448183c40000944914404401d400c0303000826050440084413050300a03034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 910546654 1250 910545404 910545439
    0x3030601030c090b03010e0403080f040b04140f01141906030203030f0f0705010e0c040f1a010f0210090807031b0c120609060c020703030e0111102007030e1305011202 73
    0x38410f502c19640148000000500290460300c180d001d09e1080e65034a1082d11851581d040322002a04d020b40403484580c0460009814032000f000201c1840d822b503044803c0c80a149400c6a062401c0342401c013090b0744c01c0160320902d040d840d154444010504100761811074010079540d01804030b03120300010000504000c400000d1040c1c60150750711400a10010722100c010380e840381c1a4400141c01503003401b014241e122160700030381b0740c44000c2251044504600d07400446440e07000d5454041503000c0c1d821025000710650203060686402054a595100b42c54a002080307030f26140c200d140c4403440125078100181f0505205421144010254031110ba040c0c203100d001019a03482c0105030601d040340b4100426004248042103074040c2d1610b843c5001140011b540300300308540001e54541040c0e050b1342c502d4034a84d000003c0000c10701600c034840c0740e84031142c840c281e000410507000300b004031105540c0ba2620311000b42007510b003d58180002c0d4546881d038888100b1241000303200304610b105402d4010b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 910547904 1250 910546654 910546667
    0x60a0507031b0309110433080106060e1f0c031d090106030b09010f050f011d15071e11040e2802090a150e100e1503060603010b0303030601030c 63
    0x2440ea44219020b4029425003d80100f540032402c40d0000c100c040140300c186450b01c01c405100c00d280c003101150020007007281c0b03214840e0b4070b02550343d60521000441c83e0002403041c90702900c02602c0307001204594400f0845006503203444c000c0c0380141c002e58841c41c55400719000405603403508001e0305003031001e400c0c45031503c5415081500704002400009400768190008500258250303003400c116601d0301401c080c1c0d2221402050380103034940c05242030700d52040e0b501c40f001100101400c10f0002c00200002c01204009a501246410100700700043c040c562001c031104404030101010b8411fa0f60352482801c03160344070031710320943d564040c0c0b40070742105203d8030040072006400c0f840c081d0000403860401c485079040503070080b400301001031541c110301c1c0f0850a154851550b507038503151a06490720320a406c010f1940707900c040401d0b03000680e0040800d4017030168010b0100284114110401d240c50701c00e009200da8800c0c3e040142008044d14040f00700c9401003402e00e000f066148010206881c40c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 910549154 1250 910547904 910547921
    0x10e060a110d2c0f01140708120f0702060f010909050f0f030a030b0906090610090e100e060913060f0902060f0a030c14040603090f0f2001020f060a050703 68
    0x9008800c80d50a041c0d0b40021100030344100fa07100520001c0e0b520390003c2c84002d16001060300003940e00c01c0141250b02032800c001c0d00b60480301e60545400c04980d2010b400f600403c8010a2150343c5d441442076110480f41101d5020019100406092404140d9064071503011b106104401d036450300c2440900105020713001441c0c07514001c40300c07626a480105507880d4481b091600000e407401407540d040d49408442c442c002c07030000300412161b403120030411920354282090724041c047c1031540010b035070200c80441c0e840380251903800c030f19062500d030b00c1d10b2000000a0034140300d5441031041182d80181a0300707503c43c503500f141000079034903481c5640710000d10440324003a5000c00086040586c240301d05000b00348065031541c007405480c0d0201030660f4190700380300381210956014403060210b00d1207030703114290301e502031086000c41c81e0342900c481c03149017043d20099903031002015044240e503090025a0606082c288000e080005102008a8580101601c854031300f50300d401c041405daa10940003c40c6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 910550404 1250 910549154 910549187
    0xb06180603041e030905090121110612250c150e010e030c0a0c0f0302130203040807020a14030706140406180b0a0216090903050d020313170406020f010506010e060a 72
    0x48841404d02805216981c03040c141300d12962400820400030381c1c00180100160a040098000c54583d121203141156416041d0401c005009032201c0c0c0c104066010f01034201030707080140401d0000e045508074031083d41c10506102c5002a450005a03010400e60b90061054000203800c84888110300d025040d8020648000d200200369600d0907031012405d02140c622424003a41c1d0703162354001040c444401c92001030340c0103c1d020844040342d1130903001560b2152085007801e05d440c10550002e111b0b100c0c2c42c1c02c22030312000030700010241402c08109100141c94603081c540c52280c0000c03141140d51007240940020020160a4600c04800c2c902008001c4d000118185031901d15159000350f0312080c41101c074903c0c85001ca00007030715040300d20851225541540c3d0f054a08103a0020440181d80041e0012040300a00c4604034041031840d02e0844030b210310700502c4c40c2c2c0c0701d1406400070f103040005040a58981d240509015481e0b8112032140311121041d0b5500e61204810075040da08955440b41c100c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 910551654 1250 910550404 910550453
    0x203030406022a0f0105030a0612080a080601031e090305190305041703040f200d05030418061404090311070e190e0c06090a0512060103060b0618060304 67
    0x9400354011840395041010b5540e240307058500e0580c9074440f064208401900320010b5514011194443c1c002550b11016601000c0341307099913554040e00c1140d42d440141d410706804501820078980c00460903070010001d1a003803040c4070700c010f5200c004030308010001c0d66081c0d440302d4450400d402001554912002c00034100c540703048100d0054040c1c001203404640036014500c42c000c11010358000c0e01e004e181c1141030007507200070540e101c4c807907020108500d5060359800e480d000700558560301035005130b80c4204040e689407890000f0294511108500000e440713800c100302440301c00041882c81c021120201c1d40840c000300d65003405e49200764441d013840c9540c0100c02c07000c61002d410700001c0d40544444840e40034280b503440c851070200c038540c0d020440b8941201c3d048005515140d006455083e4001386030120140d511030002c0d110040749420755010b50485001001803100c18440c5074036203030003a290146000714901400c01e01da52001c004611a1801001007000c0c0185410342c650f8400b800c10400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 910552904 1250 910551654 910551659
    0x30406050117030403050d0815060318011104030302030d02090103060e150a09090209040609080912101b0801060f090513050f0702010b031b041b050c0c010e01050a1b02030304 77
    0x180050403090161000c0303409807107050000c015000080301e0440c3d400901030032071519420401c0300c0d00c050192a0008181c09420b00c14201e135184401180100100302c074188002c0900c00c0760909403040104103028598051104001290700402241d10760300c544100140d5070708881005038014559034212841200005041040381000f00b030968122500480b4540009603880320840184d40125200a400442010208001038829004042014425091030381082605000300e841c0085507824000e00740e01c42049094071f0091031084580b079145164814100d00d08003117020f400c90f06d0601c200400c000b49400c19201d003612035801c110240c04010031031080070070041c100e4005080196889004082507602043c0014014401c1074100100a4082d14018100c60b6410030500345c84800c56030025200c001081e0300361601181500380074000e44800d0b858030340c3d1080c2c851401d41507040007818441038980404035a0303002070548500110900e4400e9440b01d07948418148001c0d8184001d40520011401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 910554154 1250 910552904 910552913
    0xf0601030309090f020301260c15070c0f0302010801150c05070f03020f0f09160c05030a03330e060d05010c0e04110f03040f020a0f14011d030616140304 67
    0xb0380302140c0006409120710000c0301c0d4904200d00c02032081d00c84021401d102c40f611500d10300b04e800c500c001030314103603003180300b8050200d0700707a40001c070a500c00c0440001e42002041400c01c1518060202100c107415164110f500181030441306000e1301c140c807051202140e030010710030b0300a80c44160303011041e504100d07a42c0ca14403603012450702040348642c2d01400701d4441400d000c1e00c03440300320000400c4a07481c1c3d1104c807504e000c1840d00040710001c02c91104400400300ea000c0000b0045407803140c2d000284401c070700d5240c88140e00d203800400c1e20003083c00c03500e04181c80c00413a5441942c3c080710703030106c198864500007590101c10090050441d4242003001c1581c0350003145081e0445010303142030080c00e4004100704014803800aa0194824050000c0790214241c0f41002c0940c6102411000e180c0e510396080b81450412544040c03030324901c031088500c01c2d59103d50200e0310382200300c10202d40c00030700b080000c0c2c45990080c010700381c0440388071440302400e2040684120344a040b2000594904050a1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 910555404 1250 910554154 910554167
    0x20d0804090207060f181202010b1e09010506070f021c291513150f0e0106030b0907020a020d03021c09050f0303031e0603120c0a0c051507140f06010303 67
    0xc0036240c4c03a1400410404542c0c1601802007441d45102035131032206403658442c02d201008183e40e004540d600e000344100c544445107030300d500c1c0910303030740d03d01540004404021080c60141c214074000c15041c88207000250044040200c0d596040381c3c0079050040f072010400803a00c0c44000a81860b004c0e1111074004a66400c4c0f49100a103600340740281961003002d1102c84400c0d0518154001070340d03140c40083c410083d4400c4280c600480b0600c011346981e944811640c41040c2c0020040d441e024004200d200d4141c030408e10061019a02071117246080d43d4040d44450007001e002e4000d11050f074541e03080500c240011102191410480019440002c0d0000d041000601070f081c058024500c40c07a0351480c0010aa0f031250341280c91403d06180d0540c5198840e41000e07021030342520134201c0812100c13110348090b00c1c2a0444000500c02140309041c4070f81e040740603911803402603200c0031660849056500c1110419500900e1041500e0704200d107580c0f41c41422204030b04640140303400441015800701 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 910556654 1250 910555404 910555417
    0x901020a12030c0206180703060f02131707061e0813020a260a051e01060e0c030406050a0b0906040c050405040617070602120901030e010209130605030d0801050607030c020d08040902 80
    0x11300f11001c95452990303000c110b0001841d00105540480310410004d15150071102001903049405030078040003d909000c0b81d019600940380da5a401184040c080c4400c00506000304000d00e041c00b0b40811411009a60091401c080000c0061180001e03001d4180903c1080c000d41e4050b02c210740242d542c4c140740c101851490f045140c800b10702400c0881d91000002c41c070102c1d0b034104000e40004081c1c100d402d0300c01c0010340002e0851f552964000612148030f092410310039141c0307400c1d650340c80c07070320f4135003501120401060004441d15004100b4000e03203800340703101d6120304141c400180b41102400140e0791406183d000d2940a82000703404540700c10200240c0c090910500300f1030f00d246803070b401e09030b840c0c00201680c440c000c0403e200c0380c0220b600c2a0080c0603e40d581ea40010301d010318510104400603a40408217600e280c444004101c942410000c404c0501c0041c6401c0b6000d50409002802c00c1c898070b01c0c081c00300a01ea00d000c07415582c4803a00b0380400765000f408141d540c0d50f41c4450a02039000300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 910557904 1250 910556654 910556657
    0x10c020106061403010504090203070e010906060f05180105030a090b180115080a1b080d09170f0312040c08030705060a0612260915090901080309150901020a12030c 72
    0x10400040c003500500015100558801603e402c517802e140500c0700504030080141d1789441081c0000600358100c900f024040c1c4860700000c03900a090441c0503000c0c03c0e000c1c441d1820040200f1034824031880c02210911807800c2482e040d66079441d080c90300005492f070000c010344280021800d00681000c84d40323500c2c86455a01d8000d00c400c00c081c2030300d811484050711900101c0d4001c2c0c4480d1001403540b024003d845428907104c2806261520727100c0d490040c0c8030680b0008102e044400340981c6000070f070001040c00c10301000300124505040d05517203e0042c114407440c0c00c95600040350402c0720b4148441d010303080840c1101c0e150003103401d00b01e5803801c1c00d4400711101441c00001040e03040c100f01c00300124981102102510000081d00401c02d9450305002803159031042c0f0810702596201100e00700c10840360591145c8450700501000494035040c5c2c4144842d91041006203460384409140394280d01c2d219500d07a031190f1000b40180e04003403800000500c0707860000c0150b240590198000d803400c1100703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 910559154 1250 910557904 910557911
    0x13020a0206040b07110604031202072003070f0803041217030916120b0c0702010903061803030e07080c0607030504051302030f06090613180803070801300f0f0c0305010c0201 76
    0xf454004c0e05c01040e007007603002950b0082000500460b00821100206c04440000140b50155580b1401c06c543c4008170032629080000303642260620b42088580041c2c405162500c9015103080b020690700c0c4035504c01c1c040040c0f41000040148011001ca150783d800a07803606c00d80d2443d2090a89881d00000442c101c040c2e1500301c0e0202d504d100b40c03200820402d51100c0980046d4461140041003600100030072070400000007404000a90580130782d40b00c0301c001c480d409210700110720700030f015161840c44030926a448840308009191000034045105071059818030b03561506810126464419600076035007001092042014140c0654010351040d461039801207ca62110300802504c01415620a0703440048059240d08660055201c030f0201c079a004420b640005061342c40784050740080350204041848000100225001820050b00c401e920040e0b1498085050701640002046050054440042001da000c1003000030b003401440d55030425a26051039907280f4086020306001c0010301300550a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 910560404 1250 910559154 910559161
    0xa0302120702010b0303071e050d050c0d0c020306010b0702060c010e03030117030705060c0f0c070e040b09070b0f0a0e030a1b050a0b04140a0e07090f0b07020d06050613020a0206040b 80
    0xb06100c0e489016078014040d40c50580c080e21288000022058501b8440021000250001d01d041003a9108200310b80c1741c40f501d41211481060a180701280a40180048003404500680d0003248640c15190990380e010348411729400810458000e8942d4985190718041c0c541d0340038040080658120340b40e10343ca0350088400000700984034041d00b000100305078040300103d101c0100170400b910b218508691041d080c101280040c41c0352950710b0344280d40ca40001400d000070320110300b01240d030007038106000340070592500361080068410102041c603a2100030855031a034501c609189142c0c0507008007210b40c40b403a94100190f6198078904000180301c01d041000605080500045044505003603159041a00c0e2162100913080130302c0c80355920a00a0f0800f00d0f4200064040501800c02e03541c40d0307100ca508069414120103503a4008000d00c0c03600344070540040c5d41d400c00303c07003c0c1c50744841e000c00c080d11094045071642000d0b5401d007108034004180c00c10010341c0014564480c0c3d00440c1296003d46 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 910561654 1250 910560404 910560407
    0xb0f060a0503070f2105060a090207080a11070906031104150612020c0106050607140d1d0f37240c0809042d1103011511030a03021207 59
    0x4648909080401d80074000101014002d0100c4480350444e828120b510940f4041080b04010f81c0e03810152800340d841003444000c0c02c001201c2c8002c0c14400000310b00e45485038454940501803590030a0030004040391184040c3e8081c0f14590081c11a00e00610142d62a46000d9803da81ca03600c5a07400707103260130001c0300c2403084110f285040741d026450300c440007030071003001c80c0c00382d48507500e22900b40d034030b400c400142502d41c40000c00c40240943c2d04442410510801c072070070f0814a284180c200600001034107240d07001c0040034140702c1d604803000100002d109000c103a00f691101c10340c582e004071048076200c201e00b6181203205030074211484c114106417900e08180c0101d5900c00d80340c500300d180c622901e1505e400340c4041d5181900480b1018141ba00c6640050141c0703818503040821050741c1b00c1007120b009084503d880c65604c2742202801074a40c210404403850005105140b024003140f6a140c060900a065000381c02d1100d00540e9510403441c01c000d00070b035000c80f0940356644008400100000e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 910562904 1250 910561654 910561657
    0x3040b18210c090f0601110a050d030501170f100207060f09081c11040605032203090918020d06111c0912050a0c0303050711010906200c070905071704060b0f06 70
    0x90554141c4c407029134803080011901480e0300895000244100c68a14000c1501002001e078084003aa0300400d5542c1441186070b44000b0fa000e0903c0c0c2684802110007200d000403403c1000c9010f00c1c0c0b80140c85e00218200360028050862042d0303202d03803404030700109000b284002030054038002000515401034028031482290180020aa01410b00384814094288160004c4d034120b10000140d80120340d800c10115001d10201d1300c114081900c000c1c0c20880d190b40e45c0100700f420010031f960b1100e002115004160000c10040008110aa0311000602e64146c0e00040e14001c1030582090031410a0360910f0310b000308070040044d60380c00d50380c1d415405107520a0040765406880c41d43c03080c0c141d007005c0c3ea055020348400303021407080c4550048203a01400091082c910002c0c05060080358050180a00d800c0c03034400e4611143d10300c1c80800c190b07004c030103002070007608031080e1500000c2c10356210403007100d5005191421082c40c540301d001f88000e005403500f0200e0707801c404862030701041101c43c0400059 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 910564154 1250 910562904 910562911
    0x807051204260705251d07021e031909150e040f0209062712010507121109060c0c09040c1a09010c0b040f17040f05030304050303040b18210c09 63
    0x350f52101c0c6158071080c29800d26144240049064450403945484081c1c86d14402c500400141030b01d06410064642d5040140000000c0c1000281703901c01c4030721204a0f1a441a11004e54090900c4131030b04800a01c115402e01c010400d1060b0810034000c200c1000304041d40c0c07200070602c07a60a0041c19400d001040c402c4814203403006002602d00a40c99501602032440f1b2080c4c50004001100342c244941c440310218250030a800c0000140ca10f00800b018012403545030b81c0d101e0251034500da20340512200400ca403222142140d0141e1500302802845203031000110700603802ca100203080c0000c002da42c1030070307400303031000148066502c1003c4603000e41140254500710340001c04032000750012521090740c1e95007081c0640415414103076161291030114801400d2864201e0000500f000b41d00b0407281c501001e044124081c1d440d2918044c00290b0f07900440c014071074003210004410030038070021a024008080050f040080d00e800c180d40c4a000105410ba081903a4095082c0108141c500000b44511 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 910565404 1250 910564154 910564163
    0x100e0d140414090408070803190e0a020a4202070902070c15020f1b1005130b03060303130303020d03060909150e12040801060f050d1208070512042607 66
    0x2c0d80d103400000c00c080b00b070015000780e0300350000304819001b08041d800298441c0080c03d9035070441e454041201012500d114815050030b402014000c80160307244800f5004590b002d1148040d60350707031100b9030b80c1400c580040310b00d030390b11503a91803044000d078059465280031070743e80990b404a136a071070000b8107030312031241c004050350755a80c0244071031940f8951004840c80244100ca608060f0f6011543c030340303130170900360f85c00e07070003004e001c500c5246070078880715040c03040c1490020304146140030440c80100c000d00401601100100004030b032a14200240d848a0910340103046416542e401c0103902c4528034032201000900f49400407596610394021a59060b501a4101d440420001c11400052040203c401500e00415810880c44122880504045d281000000860626264041103022269442603000e8000640c8e4540420b2a000858039640da0904098900e5a9884070494013031140e28030315200341100a0078402800050180c6c000418041800c5102c41c58007200c80440500035140001d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 910566654 1250 910565404 910565429
    0x3050955060908040302100903060501060504060509130912090e0105010e0f0f06130807090b100f0c02010e0d03020607031109030a2a03080d0f05070c080c100e0d1404 73
    0xc0080c989500030024a8080d2864500b4503851354005410a02e80002d0000081c410b100b080c070500c8024410365004000d075041803807038549010400f0300107000309150300e413140704560704010200d0815000120a180d01241c09039541501001c0030b0011003090268854804501d00041201d5015154101413041c0c028042c0380100108410401c0d03004803035281c540c1000f01030016500701c00842480c00c02510040340034286260525041c1d000301c81900b45000e1151142d070000900c8a40c12010511480314185841100b20311503000688659203a400119003214018105506140e4046455409041e80f9642445049182060740c00140512000d10743e045d00940380d288001000c400d4038011021280310006120301650120307012020b19580140c4918200081c22144074155101d6045c0300c1c0311030002004241044240140b5007000700e9402010020300280015111404200341045d2a89003034040c42210301041441d40c45001c10410f03600428500240706860101c0281540e0648013080c0c1c080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 910567904 1250 910566654 910566823
    0x15161202070f0b03130317090c030c040c051b1213060f0206011a22060509010215190b1909060515070b070c1712060f0d12030509 57
    0x3c4000c10005e010072018460014010b140038200382030802d00c52803260002d0301615440c0e01c280b60400381412915840341d8540404049642e8101c01581c1200b001c5001a090412110703034124900418807045845004010580e020389440e0312050758142d803942c0e910034004402a003016a6502400e02034002141c4130241d41d4100c61032048080d251440d082c1d55106520340709460058401501130300554000348001454449658040000c41036445c004002c00d0030b20314000440314402c2c0b008041d013844458031902f21007095581d281c080d0944803500145800819500c020100c010303d02da104007406401002004421603040d0016501d081707820411110043e030b03c881045651015080c02120701040c072402001402000030090a80003414a9010000707040c6030f000c0213400450340b0901d61165035030000490000f074075a5941c0e48502800c0c140498907840704000740c0d007407862804543d2009500c0303000705c180c0c0e561040710b40051300f140c40d00c0c030b82e0849400300e0010700c01004049140c0030504405220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 910569154 1250 910567904 910567921
    0x110933030603190c08060721020f0d14010504050a090c1203050c0a0308090111070f121b23010203060a0b030c04031e03110d0e15161202070f0b03 64
    0x190761154000302600c1c83d107268607000490340781d00d00d2000d407000c08204905000c000020030981d03401c07413100c0c00d24000c15106044408000c0d40211074103100a038004c5201040d0310761a40580e039a2411201043c40039901b00385100c040741809101d50340c40746040c00301141218a5501c19061996080b039140c0e10801c3c249400500900d00e908400c904015041000c105003100078451418054400d54600c1c0060815010150a58015440100e0000700410101000550807065405032580c0880035402d6445400c4060b01c208506003419800051904070140400440e60800e004080d83c900c89503400700102e540342c2e400c03400202c840540042c6803005c00e1000ca00508040c0d0b500502c0710880d60b29142d166900d00f0300e50848042c411003401480044401016081101880a040c0c843e000380071107821040700401c03244c004080ca9020b40f00c100b84414480400c18101d4000c1d0100502000c8800801d00d00a001c02c806a05c2410040c003400c0400700c2c101711132050303c008560b0341c90714450564640d00304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 910570404 1250 910569154 910569157
    0x524070503040b1c0e0627070b04080d030510150815060a0305150306310c0f17070602060f060f10120c110d0e0310110933 54
    0x380c80c148414400050884503040040c409900407112100c081210aa003100c05d440b1310210050481d003103013003041001c944410105080e002e015000001e16450030036914200302c0141c01100042c0300010700070a008600190100c0047d4240d0340c20012903448010072206441d0500420800038038200c3c140c840342e886040611740000808030300034034000781100000c0d1243e0015001c1400705c0e0305c034001c00c488901458002a00c0c1002a400ba0145243c07080e040d58413823800c2c803000c140040c1000b90761842d485d81440480c100307545c01840e80d074072103844070f804500d210303c3d034465151081e250410000321014080780740000c8401c1c9400078070040c0c03181d02c0100441080280902c0e000480c8403030000719a92061413000c5036040c152560821005501d42e00d1040d108180388a07020f00003d9110701030307111070000da18103041c10705280100c1400c0f54800064200074041e03040c410003508100b5400039600c07062009002401085400d81a241d102c03401480c3e014407131507186803031442c55000c030320030b512240e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 910571654 1250 910570404 910570417
    0x90d030f0909050907031202010b0a0501031e06090b0f060408060f04020d020d0b011e210303110414040f060503061f0f090504060e01062105010204050a06020c09010524 74
    0x10407406082c0c8600300d40c030484008662111155010030400c00a00c10105150004035001e803000b40a160340da50007084010103107209850400d65104c1070f4042d442941e01452010000343d450a001056890307201c4000791030400102c40c41000fa17811100000e11344001146c044500d14030181405580781c243c00c8100e04002030050741c000c2042000c8034010303640e02150308200d80c8030314498001035041841988184003101010b52182c0302c09102401100c81501460541d1001401a03a1204941c1e140440140081d4441660f402c80045004a00c203408500403680b0414280e404205056580c40311005a6465226058268100801154020402e10081110a17401510b82e14445070b64145002e20320180c0d60211140ca0f68075002d000c100421406400c02e07003400311009000759403d006001d042c5000014014203031110681d84941000000c2d010394004040050021408507079804002e900e8401d0744075558441d0461400124882c1b4005501d079106000b00480c12010700010040076a07140c0c400e6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 910572904 1250 910571654 910571657
    0x906090613080a05040f0e1608130b0c1909170303010315090302011103150901090522030e032e05010b0406031107020a1424180414070305100803090d030f 68
    0x1048042480751b42c0e420003030002c06007440302030781c0b5240c803007454158410f48402600400221130b09000034005026001115241c108c52080c000b17449800d4490028030941e40882d410281001180440c180c100964404036808108041103010001140fa912840240402040c03c20040c0004802c0412036100382c039058424000068000b0618014031080e130422100c0c40010b40c2c1c210690b11103070400201d05401080da100b401e002a040800041c090351450360030300d50204048900c041c05141c450040c0a02c00240502034544810324800d42c540c06000d00e541403151003a40c1c0d2182603e00009100d005d0403a4004510705003028100002103000d0103000c0703e464404030f42070000304050f0f0b44030403140c0c00410075100c0e00340b4075079500e609100d290068803540e440d05015551400e50710061520072540c04500d2001561220407620000030000c0c04c8441d00c2d00341800e0941c08000c9910b070590300c50f40c094809040c41d019003030303981d0010366130707070321403e0200b680045814080d100042c0c0242000540030409 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 910574154 1250 910572904 910572907
    0xc120c110a110f060412030e0105040b030103051507051e09061e0a090e01141306120b060f0d021809031605070f09020306011b03020f0a0b0906090613080a05 69
    0x121050a00d0800c4071082503890140d880c00c14000d40c80c001a0284451100792242420285081c02c842102c038040300c000350900040b41c0030000540e211710101c5014020b80d280329622541c6a042c03c9035180c916884003903004401c1c20100c0d490178002d80075030701e00c850350001350500b00400503050880c4d40c0102e084503130450810300001e01000340013060030340340300002e014003030320703205c00b40b0380100701580384c0d03202d03d00c3e84050400512100441004903a18031005442400c440d01c0c02c002840700516080d40700003c014031840000040040900485001c0c00049a40c2e401c0e000000080084421059000a41c04181400d5410b40c40c12940400d503071000900d01941e051070240c03c9a884a205807607001c440e1a00500400e101400300b14006401800f006601103045180440028101410010000200711000018070b01003520801500c00121414416180d40000c2131911002c082020340d07940060740a404000341c02200c0010f591480b0311070035a040c0040056a0315984020784c0420013200400a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 910575404 1250 910574154 910574177
    0xb04020103091707032f0d0e0d08040b0331030c080c0a0c0e07180902090301150f081e0606100201090c03080304031806052b0e070512010c120c 63
    0x124100030301104d0b4000c0d2907410441521813400d440300f400c5100706000d10a0460702c0040c0755200040d0764404c8080d0b9040a00038014031700000f0350280300d070520040c0100310001340172031882d07001c0c0042c1d8091503040009642c03103400c080310b030340070f4000b44e42851442d12000070794840802d00c61800d8284c42c2e8004c103482c910b891b102601990504140c0c0c103096a28100b0440104048002c2a414a03440100361901d0804086100d01301c8408400c0d0384a150700070f580105002d055503a00b03500001e141c864408a00b56066950503640d0900c644c1d500c00e5115a0044040362444c003051004071100041540f40a400c2c0755554404000c50301081c144c0c1c02045641e50015035000850789003004018501640a442d00c074680b520700201030782130541003640d042d582c181040001540007029101d055403800ea58121000d0034004600f641c0b28200f00980303e20f4180381280786410300204400c07091340c0c02980e1070000090f0210140e0b00742c40000403404006540d00c968001d0403011507001582104071032800014506 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 910576654 1250 910575404 910575443
    0xf140c100e060a1a0d14011d0706021605090c040801060e060a1d0103150209030604080705012906090a0302100f0801120308370506010e0d0b0402010309 67
    0xe400d42548000340d5954285000021010400300da0301c6041102c062010115000414074148055000140a4009413424504101c0920b03207228285590303c00070050074140303450b4140d03009003500079103d0078002ca1a0100d8030501c08100140c0810141d4407040901d07241c40140820b12030018825011081c0512020424000c20b0041000074007001741c00c2030715030400d401001058041130b0302a070b00e690040c1c400c40901101510b4003a0449801840d03103480c2c0205509144044c0c410110525810b005000801003002402c9014200c9030b80610020080101d9140488030354100300040341c0ba090300003009604071840e21a00810460401034040200c1c030360740e0b50200b07180d03603900040d24002c9100900384c054000d61054030940105000510700d102c180683c0c8014000c481c01170592400b0140c0c0700d80d800105011a000240c650311412040c0008119092180008090940d0164000f4010400180407841c0042c44403040503001006903400b0744603503005600030040c04200302e41c001d410721030503452403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 910577904 1250 910576654 910576663
    0x4120204020417030d0b06041518080a08040f08060603060c0c15150f100f122307080906061c050a060e0d030501380904050103060b0102010b0109060f140c 68
    0x2031120f90003162124400842c44050351040d4808600a550501c030402c241c80342c030502c1003540c40d070904100ca840c07420406074200000039600500c80354424548440204002a0020301c221400541803d6003207417039901c4a502c40c00d007a22481d0b0705070300c120045230403800003030010000401c04074100c4414041d09582c00e419504225240b6010308803101344000c6600b0300c08c2d0606a003a40440781000b020061000141131b01101d2401003040044222010030201e0140c1e1050703100d1540c51054219a00701d684211002c0102112d07800c00080c103100219521040015000380100d000408500a911101043c0c020b070880e5200140c41902c40d20001d100032580303e218174420705056002070002d031400614081d007038a0341071b4008040c52901807454010396503003a5100b1002200400070840c04140c05d4001d0410f805030110302ca038024901400002048490f42c46600c130306400703800a20035100750100550700340100340b04035000703d0380b0481020007061044500038442d181010000381052401c45095241 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 910579154 1250 910577904 910577939
    0x804021c1227050109090e030f030c070c0609030f080307170106020f0d1d1507140a2109030b0c1c050109110c0307030f0e0301020304121b0305041202040204 69
    0x401d10b0004800b0111164425580100c0d218840c40801d07186040700003092440e4602c031300400c0c140e0fa2032201007144002d1003215141044040c2c3c494482c200010b100c280350f0300201d4200c52003010703d8800200c4074090380e804411690001003500002d607054035404d0303142c3d00040c00c0300c0400c020340d04581d40040c0c009805034060704044c0e0081084182c04400c040c84d051028800d80c1c01e1000d04294014a09200d002480c00c2400640718031444034165401c0003094013032080010311865124815030b41c034040004219080c1400384041000c845118204d20001a14107401e1070b000404245060010680b00d00f5240c0e0002e80701c0021078a8501e2180340d900e0840400ca03401e040c00c40c3c4410040084251901400c55040b1080d1842c1c0e00d40360741e1424076030381d0380b144c180024107100e8684800c500881c090042042507a00c040c0c02559a4901403074103100c002180204074000c50504105d03500388640107420701e9803955150310766030300d403c0c01d10b02c240403040c190410882e0b00c40e808100104a005122020503038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 910580404 1250 910579154 910579157
    0x6040c030201020628021b0d080a0614011709070803131503060609120204060e130203010c1d01031a031e0606040903050414041b090519060804021c12 66
    0x181548002400c0c1100500b07200c0c0107007034605d03405146800740c01305810000403500006903900d49500307003004c000144181014445c01440d00a602141c0c20110051040d10450000c0120f075846141034444107000150007800940b03840742404800c0700212805400690544c00c03a9451303980c60002a2031030303000e4103003400c00382d0490004100c0b400316010444816074480c00e045c000941030440061004130980316030954880819000000c3d9104c2d82c2c043c40292102a441d003a00c0d14008414204140b8103807001c038001d6290074400c0361540c0c0b21b850300d034206601030080d0344514070070400110041e00e0f01441e091651400641e4190442d602000f400c3c009a00440c0040342c001c0c81110190700340f500042401d1300076401d00407104000390380300d012201036540e110310107402ca48544000c64028412010810720302840c0040d103008050300305840318120380080b115001905003410726005800300c07510031100420040c038041740041c503004406c403040c09801c118040c0310844075190011104c081d002c0400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 910581654 1250 910580404 910580423
    0x4060e010803071506050d0803042d021f0e13020408030a08010602070803090306181006142d01031e050f01030c0512210c060a020d05010e0903041e080604 68
    0x800c00c0000541c0940d084c4c002e01c400c1105518280114404d016a41001415880d000000500301310030305d004440c50400106c0d040c4504071361405010041015544107a1054032078407202585441880d00240c000e41e041d80c0c944a03085418018018803110310f802c2c0c0c6034800d40a02c408078a4a0040010380148145036880d108507501d81800a4145060f6405c003000300c1e0001c1001c8001901d002402503001507070010b40c400c40c0e00002d07994508152a64034200304050500c10001010249580c0b400038200c1c003103400c0c0c0401130344000700e0710541d4101c0b030003501141c0c140c00c07100003590b01a03405249181d0000c0c0010750010311003d4540119081242c40e010a460080c005106218408414030050700e025545580752620400ca52a941c607488040340c0340b02e80b081c4010141e544501c8041d6109110800f00701c615600b003441c1e542c0040c1d00804480b03402240380c20000030f803d051031110280242c0450014500d000c3c100056803803114626200040002c80880300051402d20400940703200f02e000b039040b0b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 910582904 1250 910581654 910581667
    0x1609020d0e120d05010b04080a020d030918060e070c0201020c1e060409140a02120f06060d110c0c0f060409151205060402030c010503150f0312043b1504060e010803 72
    0x483c12102c0680040a1508042c0000c0c4072117040050580c0086404031214a105039162804407281511a04601c0d400021b103c0c1441818009802000a0b41e200542010301e0b41e942040031a01082c109401a005034003a42d502411410303c1c1003001100000000310b40500f100150114640fa030245c1c0c0051079032555181e594044490394040a9040808042c05510740002005101055074028100215240c8140003182c8140e444004560400025039018454158101c2400585800500720301c6118013440d90301c002c891804059010790214000d04c0c9a092500344903244009190711a052100052106800714440341c603000d88001e224428801404a454688141410170b205c00c0411750502c4000c0c4180000d103400c18581003d007400c142d0700b4502c0782011a00092800041400311402c1510006010905441c44031400d00ba50580c4580c40d490704910071852070340b00c030100f41500410b188013004100100c1002d6940e1410401c01070020820a803900000202c0f00d0782a408403406a2001510 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 910584154 1250 910582904 910582927
    0xd0908010e0105040b010b0d0605041b09140a0e070903150509190b0703020f0906031f060c0c12060b0406080d110f070e0408190f030e1609020d0e12 65
    0x201090300070110024445802d042d03641c03800b040011300422032800c030042103c00c03403a0a00d500c00002800c00510074070403000605104941b0039003800c0301c84d001810112010458030300e06004000c048401071b0144000720300d0041520f02c0500003412481c10007004480000100da14003110340442d0241d0030b40003406042401550b4685940d240c4035600401ca07070200d4001044034003401e103a01c1003a0382409030ba1014940075000d104c0c03003131351425948080003000b4070810300d41e0080100d40d606518100f03000b0b00394840d8802c1d141c00030b6200d0b0040c4403400300c100511100c58001031569030240300c0c40000c82c110552800140c29100d2640001c1c0f600d41c440b01145540d50351294001000e4200c440180c036520455000b11500c80140e070203105451034060340030a0400820500b2608481c522032260903401d01d00000c0204442c2d00c3c3d0b080e810000e4140035648240c06001304d4014001c8200d068424411031914008030065000080d0607184140c1e9582101c142200a0008070502c05a00350351503614502e2402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 910585404 1250 910584154 910584161
    0x4060b01021f2a0c111c110405062d0d35070b06100507020303030709030b07050301080a030c032016090c12020c010f0609050a0b030609030d1104080d090801 69
    0x704001142e14039100201c2ca1308070000080b050f401501d1400c1311401100410a800c000450100031144000f5880c403d1001503100d04010340400c9800b0b10207510b0b8034080080c602403009420010264580b00090751507a000c070481d0a001001d400901014540d40300c2c8003d10321618035030480e0207100709840000c284181c031100d070b9082010030802d0502c0b0031a142c1011814004096a0240d4400c0e6410042e01d80034101b074403040740e40181102c0c0e5034a0140e10050580070ba40c4011070b24680200d01007500b81c1d024006a906070f4910400130b2a4030041500d0481d100b01035030000303030b0600c031702640000c4084104c0030302c0c2041c401d0382e13000402d0a442c1364045546002910341c8150540ca2600500072003080c0d11540e0481c0c4521780c0070b80903844200c0d10030707018010082c60400c008000c1c0f0340400060103421035000907105550005040149201880505445541c102c940c0c1145420030001e04174044007175442400d020a508143c2c5091680742d090840c0f41101044610700452402002044421030901 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 910586654 1250 910585404 910585451
    0x1103070815151b01091403070308010918030f120e0a410102090604030b060910181806060e04050f2107030e1915030203090604060b01021f 61
    0x48103604845034030b4a00c4411400b60b990708034800020700e0507000100c603003500546921a000003480b040354030754030000c5030f603a480150102c1c0862041400001d282019100d0040705c4400d40482200c0b2482541d4220760002210343d031401032200a12102c2000d02c0c062040318035029a840c014420301c05a4103105540451650100c0c204140302d40c440035400560343c50f90141d0511410b040e0b000c42d4400001c3c14064006e0030700c2150030450119000040c000d64400d42c41c081d0b1001e44903540c2c2e903122500c20f00d840040d50b004880c03102084a2000c0d080021585c0014070160100020301f0303e141c1142e0301d020a4603540da000c8503000607510203000600c10144084e03004030380313a00c0c0200786001c00c511000c81c1114040074054920b10303011074604c080c1070044621032400000208010882003403c100544d54801d90700602481100c1010810380c850b01034800c44c0c1c0690f4101c0c0c0107013115521696600d014107440c8140504500504c280142e8400f0000c040300c64000c9c03c80d90114040076040c2030380600d0b4030340c072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 910587904 1250 910586654 910586659
    0x303010603061728140c041107020a0308030c040b0f04080d021c0810030803070c1e0503030103170712080f42060c100b090103170d1103070815 63
    0x204498120710000881d4003650035440445101c0300c60302200c00300d400da03134408007074046211441041810328000c6403a01e00c002d41240d04210302c040366040303000c040c000c03803070000d400040750882440812440d070041c60380840750380c640c946082e84881d07003402203421142e03840140c104040340c18040941d0034042a14150342c103100826241401c0b412a03088031900314218402d021495010807048000510010003840d04900c0c0c02c0e48d07d007401c1c200181210040b10090b00c1006241400e181d082c0b0070800044521074100000b075007542d080d51109c041c40c5901d02082c480c0080200701100002ea948001504168260703221850315140c1010b0b8840010401401c41c1030316070460040c4c03803003480c60a00401001d0007401310070704001c1c180c84a41ea207251040d144103a0010b00440e000600640019410204845c46e880078492081148107000520000707000041a02c0c03003d14900c0d442d1800040682074219a1000110710064208448a082d0388181c1c0d07210005010b40040100c182007280500822420a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 910589154 1250 910587904 910587929
    0x130308030114011b0803040201020a0606331d121203220b0c0a3e062e090507080603010e06060102100b0111060f01031a060d0201030e100e030301060306 67
    0x2c012a985003181c804c003004000704004000704095901c02c100d9180b0056100004210b000c3d26602c074001c0d81d841c01002d100e115046810482032100282e4982d07800c004d13064940c5c03e450340d9a12040c03c1c0d12454500e80c947c1040c00c040313407484940c404024002c0e582007244881e5070790781002c41100859a0819401c22041161021030030000f60b00144001d501c0800212250b44032081c400049481418982c04150f5030035004100e070b0091200106010300194000b0820b0071030a00c6000e8658a0344001c844070000708881003440c540701c19454640b001c064107142c0400c0b11711500c94086500700c0b2025640000015920420080c483c00c092140f05407240c042801802c0c83d00d0201c00003541c07505030543c48134605895030882d41c460790203600c04002c0c2c107485806075422442d22000c0c040504e00c091005035a5104110030040704005142d00d0a8080e020141c0710301490403c44d001940074103100038080c1c01d54442c4072800d1000100507c155200000320300095943c0c1d51403d1401802d80e0499001001e401a1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 910590404 1250 910589154 910589177
    0x24090601120b04030f18030302060114040b0a060807140a0210240512070302090a050702190c06052a0d270e1012030c0b0112080706050c13030803011401 67
    0x64408490390181d40f45c40c20070054082d52400702c03050f03224210b58400c3e4120303a850100805030003040d01416a040000c2100c00360100104000a41c1c591182c5a81c10400403441401024828000150f000303460b03081002c1421017101502c400e60f40841300e00d0b00182c001c1d0310180c1e400c06c503a000740011581a5404000b0307108900b00300c000d030304d40305101d40ca00c15820704041c6100220103202141c000c6400801803442807a140c14101301400007216424014001d0081947c1f0000d08080000205038115460034002030a0120603155980301c0d034103084c0d81c0038034a80d03219001c1811441c0c010781c030074048006e800b01c82955003015107103d0a602c201680d00d82ca0344880c00a244028510b031088401d105240e07016602c5204600180c0c201035003050f0700580c9000801401d00d600000d6641b031040c41070001070701603a6030350304004901021005c001e012000130441d0348041440790700010340282444041918000009002c0c00c00c4008551045600c420040010410341c95a4580c04582040070300384000d02c0c15 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 910591654 1250 910590404 910590413
    0x1305100501031b0e0301110d0203010f080105090604060509011b0c12020f0a020f0f030303100e061c080d060b04090609050c0c070501051606020f0d1a030c122409060112 74
    0x43e0030080204100d644400034800f82d4094203d080030351503c145c095a100000050b00300070358024006c1c0d07240000c0c10078000940106c1445014801c1d1411406000700e40c07200da4504000d4000900003041564031003014000046803051540722a141c142c4902407000c08a08d4031800411410b0300b145c0a640040e13640c3e03c40707500301299496815504441880b1405d000c44000340000795504541c0d509441b010040203807031300031b208941c803c0c1c0e2420340d0122103da40312010843d488c880410107652002c888020a00015440406403031500d90109000c90031b5615490b50040ca03821a500c445203041d140d50003007010640ba403190f290000749900ca001c0c6043c1a02900e195070312024483c441c1000000030349036404105000c030004425038016010742d510800b01c0250712135504503640015459103440e40001400f04140848849184041d028003c002943c0040141d00c1c000103440505034004c0840e41c0e404500d15007e039405007003000b6207000316400e00000291400d20142c1081c0002c1c0340100c061400309 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 910592904 1250 910591654 910591691
    0x1080f060102120705010204080d031e090c0608090312070e1305010311271e010b09090103020405100e090303090d080c030a0519020c0c10050403021815130510050103 73
    0x1403001c0810f9036038075859071401c40d00910596200408034050b8a509418545c0e0540000e01000c0c4400d00040c010944080e00d20100c40200c24002c2c110401d85804000b560b00550885034031800c400103880c101071500c1007805840400300c40640c0007401540e00d03003a480c0b400380a4202c0e800c0c1c6d4140104515030650780c4080358851540011441030300c0151881e000a0b410001003d2204112000c5000700d08202d680c0000560500c1d08407280440d0800003c500309601e4425991020002032404120380d00c1e580a1000078140a004600c201078015000704544e40c0840d2044e0095034200000c40d600e2804541144c00c03d05607000042c00c000d105001c0c01044141e040540b60800006000000c0c107494181c40317440342d0204404001d00715400424444420f2002040d904281d010075158081d1440d0b89090807a5607200b43d01000b98090190505580ca554011204c0e076805040c00031400c01c210002c07400921510003810701140340e1130301c5130100060105100e0b00e20380240000c1c06c00340003520350380340d15a00703c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 910594154 1250 910592904 910592923
    0x403050604060b24180a150906080f1303030c1b030512010806040201140937050619080415051006031103100302010e032113050f010206040b18031801080f060102 71
    0x14040e102202d020300f941c0d9201c286c80200540355421050f40c1c240e550182112402e889200007282c014800034109449044105200c1c904604845118440c1035800350014a80328110404010800c8488403603a802d248861400600039200c640c1c84050b03003a02c0c0c000111058200301c02c0c07030f00700c0003d00c40140d030000382c0c111307034a04c101c8501c548510f070f810301040491006920b01c5801c250644241e188003200f04040d400c1c26100280a0121192a2000d010061091400310a10754950321864403c0030300c1100761541251103030340c940050510900185c4190b48003500c420201d411080810411240c2610810700e01140503030203141107213050225004030038014800a4103020703102e80c41c442c070f550b410b100381c800010001022061200c80804041d001d90810a0118603141180b00701183d01c1c41d0640b141609004141d0040895640d03030f41d10844080c1c0c003e8070040340a542545040307401101400680345a0b0000b0860300e4120700305500040c03120801501c1c01100c06500c00600100d07076030110b1002e10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 910595404 1250 910594154 910594177
    0x120a02030607200105270127060f0e010212090106030c030f080909070905311805122703150726101d0f07050403050604060b24 56
    0x4640d83c0c40074000b501150403001c0400ea9445e000c20804400010005a10b100051454488114503000000c601308d07284004036581081e0401d4000c0070b41280412a5070546103c2c841c040391995404d20401d041d03c10011407c40c041e50042070f040d42d001c003240c042940c8800500000e00001c0d1940d04c0301e4920810b103002c09054244c280c5842c1007405540b104803100c0000141c1000070501e001d81c0300409060181c040c2c6071240c0410a546880c0d800346821003203d91041d100c0c0c80402c030b10000c180400800070315000305030b040c80001452020441c2400810302103c6074109956541a00ba84002c0b6172054803986a6a80c00c4000c040d00043d49000401c01c050004810384d58801da221004284c0340384080300c01c0c0705511080301014000c20b178001a02ca030300079026094600d07002501d403800101d00c03c9152141e00b282050000000e045000314800c019003181c02810581c0ca80b42e129201c0c541424021501507480d0341e10f0300b030f040b5410300f2311050f45003200080c103012407240b11051184d41900d1003003400150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 910596654 1250 910595404 910595417
    0x40e0d0c170403050d08040b090a0201050f07020f180405060a0516120f020408013216170a02090a0602070501120f0b0a030506090c0a0f1829120a02030607 68
    0x2075042000c503045801864209080f50f02440d410440181031284c110780444607002c6040c0030480ca440c0018200a800d0340c161280c0d030601c0815030102e42e032500b1010301a40d0080801c03c010041e82c48080c5152001000c0b044e2261192a25060641c07818801402d0b40c0b2040d440e0400f0046030003150088072030b01010524005250b800714000c0800541103800c00c070a9280d100140015100780d0550042c60422103003040c003030a60b900c10544241038a1005040781e048810340740001c05078080d180403d40002c6050074482040030b03400c0c1e0150a01c0e2000c03503100f40c500703500149012480c60441d8218009203614402030071140e04100000b080702c1101d04e4402c90302034035104031407500c01254000700401a00944995403181c1d8070b0070324641d00c01c0151455081e50148502d410303520f042030f1100e0001d5546621b0305041c034500e03007007259520510b012960580e040c0d40c0c0e0100c0c2c41050420080c0c1d00080003900f005665150720038200013001c4094500d803802d0764440003120380180c602282c0c2540c008074909100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 910597904 1250 910596654 910596683
    0x40308040f050f07060306060305060906180709120b010302013c02010b100320090f090a020d1508070801050103110607080d060902030711030c12090d020d0c05040e0d0c 74
    0x1545081c00701043c040ca24001d040b80401c0c02e0394154010701c2181c440d0707501440702d07484100a00c4400c140a654a0350031000b400e03980c0450200789034a444d00000546040840d895554650380c000315076210084035045d20010041040d581e0001c10643d000e0311148900c2c2d005001680822074011540045264074400840200840350007903128112144000d040e20780102c0c2101002401000c00114000004079400703072081d0009d00724401d55034811005403520181d04000c008000c0c420000500ca0402c0c1c1e0b03002c01504c44502c07001e00424510401d503904e4400ca890800e008141001501e41007800160325100c0104003241c401040d404c450281594090f0f9a0701850511500f03c0c80380d4981c1607003081c20b010b400210204580e00940c42140316a0b245920740440360204c81c1c407440380f0307440602107510500d03401c500701101200414001e0401803100f45d80c0f481e1540460048020303c04152030b074240c0094200881e00b41809100d120b007d000002e0800d0408000014103001065100501aa10543c500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 910599154 1250 910597904 910597913
    0x10210050a0908161703040f0305070c120605010e071d041a0303030c120a06030218071b060209090a090c03030c050a060203010915050402030c0a120207140d020d08040308040f 77
    0x380b5101900a01010b5590708200550100031000b00e904440036010701180f009034135801c0b0f0980c1c4c01154807400c0306c070016546031022501070b00008415a1400103030000060740c4900b500e00f43c07003200d10400000c10303a589420b42800184400412100070711008808031906d9040450706080740e80c50403140000c261001d5500c100e501400020860b070980b00000500c00c00624140180c250b5038600c0c51842d50f25540d060740a019113042d80720094200768110b098201405c1c01d40040795001202c4d03d48201c5a560001035055000e500940980700366a0000b890710b100d0a10340c80050307000310080c009000352801d03683c0e00403c2400d1440058200402c154040040240030300020b204a40c00060654031303941c5031004580100b501000c1490048150503001a50341060b000792032103000e882c41064202000c042040e81da10005001404079254200411000200d00c1c1c8012248036510070010300c0c880340c0c4000080d1400d0149049882070006040400001079400481103a1107944a050800d4540007442d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 910600404 1250 910599154 910599161
    0x27060609120510050c0301080c012c040e100b01020610030221010b0603041a16080703180209010b310b0a030b031b010f0518150412060b0a0e06010210050a 68
    0x41a01c4c00d28050020101d02d24000d14140c62400d030603620300c0c00e61000150b60b400540c100b21441c030303001007140c0354207a0003450221209150107403010848101800c0e03942e00f010400342ca40001c881d610500f480785540c0c1000855444600c414144284074115000110900c1401c1d4003030481000d0004041f05075002908264540c41001d00f00e9520390609180c0350513801c0e44030345400c0035100320314000351400707111002401c903440444d21100b1550315002c100320040c1000d03c198003041c0842d03801c000e0050f1100417649008161050742d09444480003c0d0219964040116900540c440c4808120101d032070009000111402c42c403c1030742d01e01e1080780a4000c1d200c0e402c0c280b9403500035000e103800c4645003803080c0b030f020103400d036211000d524040d20103803041d001c0c000407030703081c0060319042d103070107091120380c040c05000f5400000d41000d556a08525801c40c0201c03003191080d03102c3c8050102c6080c00c0103143d019100303d41030790003203141c0100000e56510700000c0b685885034541d000700d106c1804a50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 910601654 1250 910600404 910600423
    0x30c020f0a0b06010c1a01090b030c0a060815031f18030207120c091802030c010c0506060f2101060807090212040318080102070308190903080c0c031201270606091205 73
    0x20303071601ca1b00f250076284403021001344603000a450030b001842c0c00c1d51402050400c00742a006048004d014101a0112040b6170b008090340055a12640384c114299010482110f86980f4183c000c0c8440c540c0c461244280c0d0000c8041d10107080801d01035200098020440c04140d4141400c101c80900c428140800c5e80c03100d81e8099810f4524000800e004040741c00c40402500e4003c1e802c5460405e69400111005001020094919006800807520034035141801901041c00100810a90020910100c0840080047ea0401d680d52001c2c10842c00308184403580c000e00e00002e04504001083c00c0f98194540300400041c200b089001d80c41000c2d041e0144840041c1804100031500e818491a01404020040d900c1c1012080b940c0382400e560181c501800c40c400703030316664040c00703a1208041d02400f9041140c100103a800180168041520401c80144c024045005002030406240c0c006520484007210010851820620180b00d0740da0400001c2080b6090ba560055000030070303003401e0f41043c4403034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 910602904 1250 910601654 910601663
    0x41b02150718090f1416080a150f030309060801140405040c090f02090a0b070302030a0c0303021e1c0c05092202181c0f0807032d030c020f0a0b06010c 66
    0x4120201e1099030303641c44440216003a88041107805d2000c0640e51a416007120780000c41e909007000740c180648501c02564020007144400304400003203c4e21915189101c0e00090210500284104145944044610000d01c0d036428030100f00d5044c242003408078440110f2107809640c40388041800c2181000c02c440081903c03200803c04100c460032110041e6000c182c400b0320400b04100b01142c0c241d0124112000a075060300114034000201c0710690301002041c000780c050540c21307c90307051078040d01050441500142d120342c66456012268095140d00d001c0740c56400707646000c08000d00981c011045034100e450440d050445041c181a4032031031202c142540800182c008140098060841e030820103a03000229154251a202d0f800000e089400001c0054942100105040701184840d00208070481c02841c02140450a6440c814070141100340a40071502082c840c1c001850ba0610030001007103598406004003d803980341e001d40c2c41980d01d00c06003040f403100020412030f0380100f00b65219142d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 910604154 1250 910602904 910602947
    0x31407260910150e06041104090e031c020703080114121002190807080f0a0e0a0f050c010c05100e07050d0303060f06051204110f120a02041b021507 65
    0x75000d1251100149a07441c0700d09030900080f0f41010150304682d1042d1150249000c1d426622501000042d146002400780076010801001c54420500c0c0180c160b011a0344000316504d410f07000c2c0441d40c185844140b00000381c0306110420002e580b004c4054111000c01c44c68080340c88c406e0000840600300e5102440c22807294001421050b2b007290050403046010300001c15803031030030040039105008112086000105504005800c0310400308501e904080724000004081e10f0452201d031806440300d10079140d01a0b0842d1039802c00100300310402800000b8640b05012000f85d03940c3c9a540c903404807007183c9007a2100d500544003003042200d00d000342130040078441d002e0058240540180460300850421080c3c403000031800c40c0c000c0044034003120001490040c01d5503280c81d01d00304013125909040d400350345080c1c0c2c1c0610740d03118041908100c486102428407150644100700071190300e0000c080030031400a81d505c404540102d10440303540312000c0d00300f80030703030710341d40103c1c3c0c048045142c03035508600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 910605404 1250 910604154 910604161
    0x16031407050a0c0e0f010b0f040e15150c07030b04080910050d0501060201020301050d140c2d0a0302090c0a020a0f03081806040804120203070b04030f1203140726 71
    0x203001440c4040240100000a0360320f880e8a000701d6440801ca9000705d03041c4850004010f0822005c00409440103640c03590ba00381b03a2180d0b407a60b40c255043d1100302d0440014041ca40355443c001030400c03180c1e061a00c0c49880c203400701411944540782444003910101d909030029050254400031074007500c00040044010082900300604103030004400624080d00c0d203800403079103034014400c0328141d8a00402901408c0111340d1490321480300c1800400080c051a101e08080740c072895980303400710620145103a0f010f50310f840002089140211803a1042d024010b00300003507210b4288080d0048081d0308010380e20014440306900d00703a0080401468107075600c541c0c1301416400150381d4043c1c2841c100358205103201c00c0c501a0707903031001d8501070140d0004001c01c100800510720322f0780400f403020b4140c43c2c5041d0b5555400259170002e510940c2c038501101720000c100003e0001d26011003d40382000c210204020480441044c80201070505000300c0c08505103040c0c1c8110b02450508803403600510f00f41c40d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 910606654 1250 910605404 910605413
    0x706090b0901230105090c1c0507080601030c020303010308040501081e091f051b03150303030103050c0f031b0607020612070c060c170f0a06030f06020c100b0616031407 74
    0x201034102908180ca1140b002d0f688032908000c014103d401c000d00360510343c0c884104038012030b400100041219030108440140e038484034005c1507c500c0d9981c0b1140200d03d0100005407d030382603008000f045400400051000454500a65055410a103010f0100c0c5c1e89900d88542e803a20200c4076205e42300c4800b0100940e0b00000a01d48500051038001148a260b00035000d000b9070704d061321700d60302045a10710315121125005d006181c1c0a42d169000c0303900c0400f140007003800d61348282c00130760312508601c68100c180c2c103180090000c61181580108801c8000d0b45924103480c100022007845901c3c00294141551b6804060394400365030b51070300c9542824000e0000c0d00007030102c081221543d0070411035031206401240e2540105070b003417440400540d6070076003501c146180104500c0415640f81008808100c0c00c0031220003441c8030f150016560310200c48803034504100940070340c00301410b0542c015015100c18050b603110100b2407420510028071458141c99100300d40b4040f01c0782100201c2c0d02c80600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 910607904 1250 910606654 910606661
    0x40518040201030b0d030206060d0c0906082104360c030209120102090d0303050a1404081c1b0c050a171201170616021c03020a110708120706090b0901 66
    0xd81c400d032010803054080009201c124000c4030000380240e0441c8000030280d041c0000d41600507486480703041e4500341c581c4040002c071009078200111640c40011040c203584201f420b03500703c080300030070801c1c03d03c1d281821040000c40d515005116250341c001300c103180a1710305500916130b408441c1c000e20280e00c40610080081d0002a40e140c8100f40d1004c041d8044070040c402c0b5225020050080e0200900c02d44007a000b4280c098250300b14035039a541c8a00c8844400b944071406244926000307640c070710039200529242040b1680746400a407502442004100204568100c55030311404c103c00c8400e518202641050380d03490018009238040224260103010000081641e0000c1e00c80160b040e988400300c01c400308a12942414065100340041000c480319010f041c90910410300c101d414104c441104044c005000c0041e8001080d004102e84802e80d40020244000303880c02c030001d252040c9001c01c20365603440810050181003c0018000080c8103041e08503060180d00548106928101440428002d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 910609154 1250 910607904 910607911
    0x51504030e0d110f03100603030f020d020601080604120e0a060f031112010b07080715090b06030c1f09090204080304080d1107031e0b0a0e100903090905060303040518 73
    0x1960400480d2120710340305840000c02ca8029000e624207594160501100800c44190a80d244c42070410300166102ea900840000d507100fa6a1950005049000a8504012001c191085d504030b00b0042c08101400074000d90310a40055180b200d42c82400b109a858440034210a6005182441e000c1283c641246508011100580d0204094081e2402c039800706d0280100b06480110001c1c0100000c1c03a00304058440c15000d40000c43c80d211003a51030102c0014150310001441d622169200300f44441a0411544890150060441c442140c800528252600707010700d005000c00364540740322107204010f554041c050a004c219601c03610342e10b00d284c0c1c03074202c0d1103460018424254004000c510501850f0038040044000b032103c6402c5640d03512043d00e6001d0030f4025030020309203200100e0b0300300002c207000301942c0714005440305c01c02044d1b50401298400c5d000d40c0c00c0c00c1000c4500020b034052058000c5071075100300000e845d164400042d0840c0315640c05254040c00710071718210940c101c1e0780340a00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 910610404 1250 910609154 910609157
    0x60f0b0316200d080a02180d0303140f0a0f02040503100f060f080f0c010c03050f070519080d0506010e0d020415080a081b15070e010e0909030d11070b180a05150403 72
    0x201e170f0344d04a141416441031070601c200602a640c01501e45040038421001028400d08012898040804542d502c1d900304541000c010341d150f0060141c81d1099100d00c039454041c8403420340c40c0a0030f01011030783d02e921058901c01e50a03520882034800c5902076001001400c11800040021640c0d140101e680d11000080c12103180558982d01d4070540c082c0c038a103940c040e41900c815007005c51446900390b0a0f04041c0d41a0781d0b40c052268440c0c20110b6078185a104107120390b404a80710200c076042401100c400400850503c21024200b5103140c0e0b400c0001000d46074102d0f0045404c08414010b02042d038426800f4100c10310413045070000b00000b0801400f010411052094880040401c1e1140c5d281a40280c030300206120002280c42d0300d1080990002d0f00c4010305107504180b2109012940c9128101c50f030023000d400c041021911848540070344500300743c0e03a4000364104580d0791541c00b03050001410041c2440100608140701500c140810f00c0b4040e049025144001025042c011102004903003c50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 910611510 1106 910610404 910610417
    0x9010c0e011d0d0c0608060a03171b0a030c02010f050906120a0b180106140705030409050702190b070806030a0b0f07030902120709060f0b0316200d 65
    0x1450b1600c13456020350b049192280040c000c40300034140500c100703000c58041010400c06000c840d100e190385006142da403010300f1a03003100000ba141500c4040e01940609106254000721000c001d5030003a218494181d1224130100c0b014413031140001c0e88604140180c2082e120b580303002030b91003010103e00054224040000414654441c104258050154001802056805613100210141c001881401c00519954003503ca0107540100741c1120707035560015400900c2000400c02d081d18284841c0041036a50030802c41c03081c4105c44000c04603c0700300100342c07a0b0038001400036400d500509050001d865400c6503500800010302a50201a11442d181016076581880080d036824568010900103281644103802e4400c0340d40198403517140804200f0518031485c01301c0b03034000c4135820040c44104034603a0503240d9100c6032a012107581600a11068500000200c140c541a1640c4811 = true := by decide +kernel

theorem cover : BRFrame.Cov 910431654 910611510 := by
  have h0 := BRFrame.cov_init 910431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 910431654 ≤ n) (h2 : n < 910611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
