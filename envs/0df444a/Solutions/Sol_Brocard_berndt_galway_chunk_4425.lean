-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4425
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:34:28.473505+00:00
-- url     : https://prove2.me/submissions/a2641962-15ae-4287-888a-2ee9034239a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 795683453 ≤ n < 795863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 795684703 1250 795683453 795683467
    0x301020f1902150432030a020c03010c02250801050c0c0c0103050c0a0509060904090b040213050919031101110c0106060302040b1b0f010c030507030606080f07030e0c1903020312 78
    0x4400d0f000010001844210a65040780692803071080c8103e28107803040d04506402c40110105071287c0169030f09a0052149910808203860140950100410340b500070f8800701c203001d0108110444111124081c201800c00009000d0501748601c1d0f215008100806480f110030311009030601d103120524034101400e160600c040314079204203d0316044110304040e0365540490300459010f0240c0b202c80da0348a40342c5074541080c020715003000da114520880d44250f004801030f00e01e030b08072401640c01c01103590200803080c181c010251b0443c6006402810701000508809210fa82500c02105060000040105412070243c0090080c0c00241031181010350401d03080001c052140c0c02075403141c078010f02034000c8500310090309100403091700055100a00c08190130160282c0a42025201c008c0000d1074018001841c1d4880d901150107030001240c5800740e905c031140101c0c05000ca00640f0800d50180d001011019603131040b0070031440c41408524105a86180105070800700c444003440e0f0306600400601c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 795685953 1250 795684703 795684733
    0xc12090c090c0c06110a1b030903110f0d03021e0c0f06090a12060203100e01060e010804140708070305070f060203040e0c04050406031b170d08040f020301020f1902 72
    0x3901c0c0036000c00604000314010032956410868009081c06103440c4941d904840402e00030300c1c040b0381d1519003041088602000d90a641c840c614050002044424240009202e100d640c8410113401001011200503210018a00b848140821009a4132036040c58000686c4902020302c070401d80c07c060300c0001c0c2d20001181c1c1c1c190810820720700c503510000d0710349a55503c1010350f801030600e80344509201202803411030300941c01950041a842666440011001164900d06050301d50341e640305100790366041d006640802c00680200e50b00811200e4240700c001081100c0c80040102d04018090a40b0b50300b016410405160468013546417070302414807c1e540c00008580c1101c0e4603410b091203076600c035100342c007842c002e64201543c0700b41030041c0001031202055160206aa90447d13942d0540c0c0d80b1b40310182034044640680b080c0d03800c5144a0705500340151507103a8440e003c0c0c50003903078840c1240d00080c2264425003164282c250089502207141200442c2d0480641702400105003800d100d500c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 795687203 1250 795685953 795685973
    0x1511011a100c06090506070f030b030c1008040c0b03070e0f040b0f1504050901090608010b0406451b050a2c040c0206061318120c0c090c1209 62
    0x441c018801509034500401c5030541c85071896540240c2034805600300400018005003900042c10006424000395100500d804144208950f0b4018284e12520842200654807140300800c00e6031610200c034000900d4580d030744001d62184801c0c1d900c0e101c05141540803c030107031741c9484299000e20b10300380a07000c0644844110301d132400000ca400d80f840d481d4500c0d030040d6501c02c03900015001550138000180403c1160410380c151039582d0002d00c1030100c15002d00044865600ca000305004445900c0420070340382444141e0420841c05a410f4030b00188aa82c02c802195aa09103071003e03952080e12400c2c0810040b48a140704092030f0180c6415548100203085003030768142c400c80d103408505401240d84190171f40d0f038000c1c42c0c06032041c0070a0b01c0681d0042d44490048801c12f020340785501c42d1300c01c4280c0718802c070f00e800744000c4291292000d40303848542c482840c80361410180401511181c0c0440c81e03490710b000013410307800030100d141c2045e2000241010041d4507601a054245107070f20000600a4078 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 795688453 1250 795687203 795687229
    0x301170102040b0f22080606130b01091505040e1312020f1f060e0f0a0b240c010914010b0a09111803030f0406031b0908060106080606041511011a 64
    0x15446a800c0030003503441c8403402c5c0050864004a080c002540c01c0f0200340e140c1700d04070072107940404501302030680065402c01851940080e0007144184400e8400c10391840740351640c0e00d0708908003a100e08a8400d012815112044031441280540c2e0802040314031250000307000e40301030328440a106503100ea5400201d08006000700b14004000c401d58200da100000504045050700381c2828900810070951100b5a10f04501500701424509a0b0400c10400c1008504220030b5415160140819080642241c0c0c55101d440d501c2c0c0c00c1c01310116003861400503a01007003038000902815010200151942c4507031102c07030b03d03900f030809514442414030103843c03000d030b003500403d9030344402c1400090641c854140714207514031001c1030100b4184c1d8164020840c801017025078000d0f101d0a090251a100103600c25418a54040c40050058900c6080d041d6001742c1c01402c040d0415807203035010708005028044e000005860000700300b690000034000c500700150600e82000b078416940f0082421080c0041c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 795689703 1250 795688453 795688477
    0x1a0609090708130807030c060b010906020c060711150d0b091302040e070e160e061201180e0102070809090703060807060e03031603031431050c090a020301170102040b 73
    0xd0641c140d8683c800020359020349015510461071801405a856030f038030903200e0364900713014813150394012181c40f8243c1d10103400801403401c100041100f250710102c800c66103c0d851409404ca50313120100d0710514150f901c40040d4590501d40c1c071000c201d0348012091032080c2842018051035061600d2f41c00d0256406840208a801d907000d002450b0400d2a409901c910454804210005820b45120180041d140d520308244907508020460140a00030b419820410744000421400d444210704440d034401d440300119602011600150881e0840c040170745008400282200c09803410028141e400f03804c500701006100d08005400f560f80803030b4010f42082c0720700300807485465a410010340e61b120125010398201c11020b4500100503110040200116007419404254103962801024000d10f64005024541c0060407000c0c600920800e00d00b80e0705801404403510242c0c4528240921560480102507543d507d8000e005640421901207141d5a920501c818059141c4100403520441003003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 795690953 1250 795689703 795689717
    0x1201080703261905120703060504060504020702030606060306010c05060108030d0606021915090b01030f0c052b02010c120315171f1103010e09061003030e0d06110c011a06090907 78
    0xc200780c0c4c80780304035039801d07140315200d4080214060b810b800100a40340c0c280c8041c0f0016941d8414001a8000c0c90310003503154025400203543c0d824400003450f80154145001050a40303292181ca0030b1403030070f8000106a4200090005407170245e4002c680c001d000138802402d18483c4500500b408516104c0700034188500d204801350501c509410020149411090b0301c0c2c81941d4a00e8007180c0e0f909241405c561108040e0030004152030410607a46001704420907000c000c0100500780b0301082c0074039500300d0600141d0030f40c203004200d144003034407007500c8261000180c0341c05d00c0101c5600b124155010082502120f10305d070f600c4050103d40c04e1044e0040501d800020056400c1180203041d50810140b4091000300000800e081d181c03120074090070351081901c3c01d9807190001c0a240c1c0d10300340006004515491241c0350107007040b001c03400446000300c1d000a1402f40b00c2c50300002d1948428410341e81603456003910f0124418034101e0900d84007048032540d10704110503011603d40f2900030010010300c100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 795692203 1250 795690953 795690997
    0x60114030607200f03091005030105400c021606090b250302100b01090302060301150c06020a0207050117070206061201090b1608150307050d030302120108070326 71
    0x36081e0882d40740900d140595032103130350f04d130181035680d0009152184a41201c01c03d100c40180100110783c10395a024144603050440014140c03903032012804401012010b6901c001c510100c0002500301c14201904c010400c4016032a000307103000008503d502695100140030007000d60014002d008507400da000c0b0320789a0021001c00c0503081b486100b040c0308828000040810181d01003030398520030340d402504105a1400030f00448400d811400001e4100c007081005000c942038002d02202c68200350300d031160130107800e5038a2a052780c01109050b0b0141e0306c8901d0034000c07580c0091390121030004ed0580d800d410700c0e00703440095950300064881401544016404000b80d5020b4200000b580d81028000c5058103124419040741200321004000040303291020031503280c0da13004586900d2800800920782d0f10301740020080c03c015140011014981d08120408003c03107196100c81c002d02465002d44111451828000364041c0703500082c0603010800b515445400380000c1c103840c200001c8055608130080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 795693453 1250 795692203 795692237
    0xc02270601030c0e03060405010501030c270e1e07050102240f130606030302060105013f0f090f050f030717090a0b03130c0504060303120b0a0506040b0309060114030607 74
    0x3260783c4c0c03410307014040d12081000340b140542180b030482e84070f0204030702081e554452801c40c0ba0a00d4104960001d044035041041c60b5150300b04180c20000802680d904d005043e40015002080103c03203500c0d500900c0f41000203603014803003e8505185150b10304003000e003808407600409401031180000494002c0815802c40010481c15076003548403008100329900c0341806552040c00744280c500050b200d02c0444401c0c400829251019000700032400300d03009000d031000d418400e03440082c81708299240c0803103170307000044c0c0501300ca540d0280380d20f54010003c604245080006000500c0c81950040003450002081c1100d00740c80b03e03003800640350310385604600042010085900502c2e41d0900407003030182c010b00001c1c0d110b840b40d00c01c1c0480c0c41c26030f540340d0520066a0315484082d000c030700d0400401c54070b2100c9401000c8032401c0280401c400076160b0b40012465009508440d107003580c04010490201c0301000850702505011040c03c0d9002c0c2d9020000740d030741200402840c1049405408005203903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 795694703 1250 795693453 795693467
    0x30326180c0613081b0612250905030d050c0a0305071b26011118120703240506130921050703091505040303051c05070c02270601030c 59
    0x50001882256190390302803c1d4161031a0500621649010360490200405100440c61111090143c8454100700000c21a644096001801c160728181450400f0404482007031103440000a07645803410f4290400c1d01749450042c10007542c8083c0001001204038550b00014418506513052400e9555508140782110006043e8032101442013195100800c044801c100c003100044800c008421012585820031800e0312011005001c3e1400c0401840400201c0c07102904904003018028004600a1031122841d000140d0300640b2443d844000f145a0313000e0341e0031400c1001c200044e0174400c03420500001640c00c80350000412001c2c0c0c2d02e178072050030050342000c845440d00150103c4519039203180000b800a80c002a000c0f00002c9520401085211001140c00700d20031107596101d04140c00d56030261201d42c0841030706848000003440000310040f0500516100710456594002940700a2051000144091918403406100070036502c615010f0748501c680d106400b403802042410355044180d4a10b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 795695953 1250 795694703 795694723
    0x9060f030f24020304060b1509210a0b1006050405010f0c030c02131b0503041703040c15020307060b01030207022b060204030b06011107080303040b2e03032618 70
    0x19000c1082e40d80b640019540910b10a5000300010301c0400c0c0001c00b00401e07807440c154500e0500000b801541e0040c04c08403218840d6152190303001901c0c0c02d2100b800c626084006404403580b505800c1001140c5014281401c002c000c2130400a007001d01b4070002804500c1d111071024100142d4041080506105403e051030164016042c48000140700e46e001d40a4443c480229680507910381502c60054400c1c41168401c54100701d140703085011180d40220242c1c0050800e071030030584c82d040407800209441c100030300389039260015580c0781d81c00d15203801551041d0350868103040c8184109030142c0c48100c043c030340c844001c0810341101c580e4403424030764000c8a440d000c2c0c0128400304d0084204800e810400e8000c4209899416880441100b00c99541c03c650017404541d802c09d001060006240041c1180c100700c082c03010060800c05041c12a40c1b80039091141101c4d001504000c000303064121032904036100260007030500700110241d00103030070300c030180c0076803101c2c0d10100070701c01015002e0040301c2c14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 795697203 1250 795695953 795695993
    0xa0f06030b1c0f1118040609020402130e09060609011d06061306030b04050a0501080a080c03040509070503180105060609060702061608040e16140a1107080d020709060f030f 76
    0x100c1414102030f0b408992851084960b111110302070441450550303140d21060750b9980700003200355107036614480074050403001260010340074072030044e1030714043d66004c02605960140e101ca0340303408452540b414002801280c040d1070264010700000c500702c0740312850902035010612135a165000410028441d04544484020034800085400da905410070302d0b90900884051020740c8550030320f0b600315482840b400003658040c007148000a5141409841e80c610908c042ea42003680d200c0c041313100c03940211a44400140300104000b100600c02d04500ca002003114000c020520b40304000c13407054400c003401184508404501907003191f40b201c085504140e0031a014094185603843d082c00d9a402c0303801450b00304103003e03000072468101415001c0c401c0c034040d9600100040780e401480709030f0f440002c0c90010400c01c6c8841d036100c0d90041100d90f0040104e00010011892030710740003030900f0030b25008281e0751401e1134400c2140f02c9130801070070140c0b6003003c541c00e0111001c2c074201c203100e03004041d5402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 795698453 1250 795697203 795697249
    0x1050702190e0a0b09010f0807060c060605100816031517030d0f0c171512030904050705130e060a1509080d0c110108240102070b0f0c07050a0f06030b 66
    0xf410035642d0071642c0110303030699240072507036220341c8400c2c1d181034180640d00c0245e01c18407003001010300c243c58004490b8094000044c2c059210004600210b20994000e40070503244010301c0b4441c0000610307259407070306070f240400c823407a4892988450800c0506c643e02c9102e00303c00a01600d14400d00c22500080140002085419000805440070b040d82d050640f0110f06010000c6004a000341e0040b407041d0b2100f4151070800d138001040080c01d07540703c0e244452600c424029421982c81d14844c80d406025a80c82d81c03600c401182c2e081c640a6a45a00020800b5200b0f034107102c0346072a480c41d0703407003980c050000c1d2115055001004560074001a48600318030b10400c00e8030084903400080040c003482c099400c1404803a5074400568003040282c86d4080c12199019549603002e8004642103281001481036850090350384400c104260013070720300043c40d00c1000540020303110b03041240000511044d038040b0105440c004c1100503e407000e100d0401071503104c0301c1e9010151354011403020000c0501580345 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 795699703 1250 795698453 795698461
    0x13030506062403061c060e0106030b16020a230a0c09060b0301050d030f35011a07120903020603071808031903020c030708031608011401050702190e 65
    0x190340d861054500900400c0380305002e8440302c1046096900c0402c1e4003401900d10b880b01001d00007160070789031240a01d2204c0f040481d000030403902900c15010925000420344a00354105030084170320240203220034174039000784240140c4d0003180f00c40380c40d904480d40310702021142c800d20703c240c00d0705090612a030144880c600108000c0180ca1016102c100700304210317140d11402c1002c5103100c280112640700c09906003060000303100d0f010310f581d400b8191401c82000d820352580d0f00d0b0004803004010398080d800c805130540c08050045028010210980b06e9207002c1014440e0150030311910401030149146d0390520708846024001000013198060a210b66a2800c403030f00900101202082c0784145494160005e2200800010713182c04800701d00710191900e0810100390000e5210060184040c00207001c2e02020502c0a0059403045a0380c4c0500c3c605590608001400f003001600303d103c55a01043201d03110103990050660f028580e05880462400c0003c0b0455028240c0580c01804c0c101c1c042c0c0100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 795700953 1250 795699703 795699713
    0x2104051503070305310510110405031b240c030406050a0210060605190e0319030f08040804032010020d03140606120c0403080712081e010603020f1303 66
    0xd521070b10442d6010000c584912404c2e0584680c0c16a000502028180304100c2020356125000318040c895001c40b404081e01003e03c0b0103540000900c030381e1003100410b0800c003d090601140c010388002c400b105a5640d00c41c00060300c200080407003984d9041301a500c81c3c20319680b6030b040b6454280030600b201c0e212a84c03010f00401035842420060014040c103c2100c04943c0305000d0342c2c01b0b440c02d584449060424544c80d0061078014600703041c041042140742940940c50902040001402803d4082c1441495080c0030745552644284103041021032010031020941d100196400d6a9014007080030404c3e1040c2d10303100700769030300c0401544648a602e001080c5a000242e68801c3c2000751030610600c0d807410560040e0300000c4840c1904a1000c10541c40c1c0741d0920030b5003942c00508015024181522901e80c00c0c2a41c220f21400c856164890744241d1002d0b0304100c0c11513000d6003080c240c9603020340410340308803911018482c1c6004e0607000b0898a01c0600150151045405d000c03103802d0245942c0c0c185 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 795702203 1250 795700953 795700957
    0x11031204080904060503011814030417061602030c030304080d020903150a0b100e0d0201200706180b09090411040f09020a0e060105040e361b0321040515 67
    0x1025100d9132914400003040e040600480303001809106041d070784901942c45060f0002c000070300c060018082003102080c076940202c120b00381c1304d02103001040c25142102c103c910450001401c1c00940d80300b0310071008071601c00401c0303da200380d01800307194503030418880160281c020900d040380d00d0300402100484180b90750308010300c01c2c640100140642c0b0840e9090000200b00b1600880014080c080c05086508080e0340320b84174180b06140001c0c00160076803151281407035100c0f204046400040042004a41c0a40d5540161a81d65040f440c828500340c0b60781079520460381031b14007070702240b4001418031160003003040011401910032b000c030102c03d006800040c294080300700c1c4109024040402c40120180e4010310400041e1541c0b4034144c1032000000750031000400c2800c3ca150440801d1020080d00540d16401c1074014407007941819004122074104403064840e1940c40205c1105114a13950000e07130780103440004140c00e420303a1601c603c60710703c80c851a004681c00a10807860001000001c0d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 795703453 1250 795702203 795702217
    0x2030109021305120d0509030a0507080f0609060f06130b0a060903290103151b09050103140c2a010c0e01090608010302030c060313020d0b09120f0a1103120408 70
    0x111128825498100700040414003112040c0c131540860030b0401828003400c0100008900281101c41e00d102c25a5000d2411a00750007450498211a190b8580540d0402c42e013600842d10344041c01c80e0f0701d48009003405009c8014a1a40700e840c000302c5100d141c10300e51780648299400030342803e00140e20f8000190180200b48000c0f01d0522200850065848802820981c2410f261601c80710a03440c640341c9040310b2032034487d044440d56690201c40404651148286500c107019241c025905182c640050120348101ca16404848005010072a5030510300f0101c0c0ca50030070f15108405200a007a5880900310f600300c41c3e5450641c40e102400401580003c83c003048220240d031086c103481d4980314200c0b41c0560a1000a400d6031000c24403000c145080d60166038041d150a0807440070300d21035000206c00560107101581d804000314140130001e5400d000754001089448040c6142c121a1540007410f0701c681040041006035481001010340014011500301d104510140b038054242400c0000b42a03000702 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 795704703 1250 795703453 795703477
    0x5180d090f24181d010311060306010e1314010f0f050d030c060216080d050103060509010c05070609052e05070c03080f070513120203010533030106090203010902 71
    0x800000d0482c20110015250580e07007900380000c41208401621030000301c443c0300315240e88a10021800026003014071083c0e11100b032a4288030f52550401c40e1490f10303a580f0060081c0000c00400c00c199801510124400a041d169400000300b1114060b000b08000035441c0d1102842200004514030400401000c4d2503100202c8803d2039615003c10881c030100030701c0140480d05400b000317800b04d040c60380074005000040508910750400c1d5900c2d260903034040b25141030280e50b103c0052081c0078103031040942c0070400380b0003005014a09400a08103004101e4001e00b0591504002000c00000348020b1010060000c101140031801d5a07840c26402d811907008028140b800740080c80707992181049100715a015290350a540d20390140000c0003600081c1031000b1300204104100045029411640003441c10441c9140f440794203104146c01e4901c0a042a100500141d05c207035245154280018804200c2c08503070021000040f01090140055034822142c2c0d03480440000782d107092503001400080042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 795705953 1250 795704703 795704729
    0x150307180f0615050f16080d060f0501051602030321072307110148050712050f150105010e0406082d03040603150807150305180d09 58
    0xd15502001c40d0094812140c1400c59003c241d503400340610003c2400d4840b0406582c500ba8022a5880380700c03c3d402811507113401d00082c1c4030303011410361060202500791a0f0041000c2480c000000b421402a5108806404030b501012011580c0401c00c8401010740c40d2150340b00c445006400d907a0083c01240d240300402c4420b08500e14240384000c0d0345c0468881c80d0501070400c00306071901000381e1006130119050100b140e0081545111101c80103030364511565042d440042101009860f1155a65060401038060705110b00002c1c0c01140c00d106075460940c910075100c0c41402c00c80e03d0000c4400d0045d08a000304042542805c1490034a0342c16980e0a0f2165a1007a010781c00380310442e030b05440780302615082100385114904103103414060101481c066070ba2494400340c01c0609651081e4003241c0442d998100c203018801c0c0301c580c03031402006454081c1440310714100501e400c06005410090030940e881c80014408060401d074420a5160641200e01e01c0d40141e001030b040c2c0320540240c42a203d0300c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 795707203 1250 795705953 795705971
    0x409050705121308160f0c080607030605040e03310f05011106060d14030d05091507140706021c05041112012307110d0e0a0e0103020303070b15030718 66
    0x84503c09803039100480d586812841da030516500030389145c0c2114001c0b010829040400c800c01c640f40058100744002d4406c07428607150290032079801c1c1c1e01040c0218181840090308031004801d980c01360700713000b8120618010303045080141d4401204140180200c0c0000841d22442c40da000304182c4000781c032010405a01c00049990f124000c444a980c0003000509113400506021140300f9080100811a810082c1254001d01a2032007260070001e107902600304020040c0c126401c3d50f070070419030700b0003505180c20080d4814031440b1b9020b006c1c0ca6150001000c8480035280245200c0450620390208000d04040c60134203503000c2d000502074803688a8005100300c044042c1f2507e0542d1015154200c1c0517000380c400a0700580c00240721109022140092000600c014840c041c1584d0700780d84e07a05030345000c207400c02280c4500e5070852442c0c08680401400187c50000817154400d030000c464030000c2d91a04c0d1034580114040006030b406000d001300018407003941080d400701254039201300b4000307044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 795708453 1250 795707203 795707221
    0x50a060605060f1b030903030a0320090306010e0c070611030a0c0311092106131e0c0501050903011b1706040b0f0919061418070f05090303040905070512 67
    0x1030001070003c2c0c02080140842c0c40c001d000044940340001400e0700d04002d0741000003802d580240355007101084c0c40d420781c0d2208035141080b5400398031840105a0510a41d4070100703564113014050105440318140c041840c4801e0341041c0c1c1ca10f03d41c044000d102003400404000119002603a00d400d00700e0030034044110b064001c3c000c00203d031280c50744207030501d00d9110400c1078030034100c003401d00401000181101c440a040c0642445517001c00a080b054001d20b240ca6400c8a404240720700500d1003150740c420020f10711b110075800300e500034070f00b840d1118041400680188100e803694170b140e1216280c03080d80c880d00728464480f448010b0b00740751140d648200600094420001155a1160964034005540d04d044644e00f500090030107039603c0086070000609044480c0d903000351600ca40368144044481c41c00c102000c82082c4091440503a07421701d040040c00c1244440700c84400d1010100d410b584d40d1f2000c009840003071444e11401d109070304018401802583c8443c02403020303c508000000c3c2c41c29 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 795709703 1250 795708453 795708457
    0xf02060d09032c040b010905040f0504020102070b130909050c09190c11030904050c0f0301120605070f080408090d050715030b18010e1012110102010c0201090209040b071b050a06060506 81
    0x303c2604424142c14400410000280f0707000c0182814802440d1001c0b40c1503c65120780f9001c00d01080e0001004d04160001a1810250364000040110108150f01c000605100c19400f2034480d908003050407805850060f041c0203d42000680108003202000300701038507510b030b4000d80c2d800c962042014278007007101200c00c40c104862448040d0310801031140d903030074241d0000b45d00c1029010842d003070189500307150803154800e9000f020b001100c09110401c1c01081d01c11ba43d0841c4c80380c01d0031280d25007441c02c050018800100090804100420f01501c16104d519000c4482c603407100075a1401510741c0c072a0340c42d02c4400302c20580001d00e4201e030b40300e142c01d210716823000240070940d40c1085a0701e04000c0c2003000c031009151b8440c11105000c0019040d10b00700e1801d030500e105200310f203042c000f05000282160107a0f81070b0703021613050403039031000750b19008034a0b5000750300280c0b8602245d43c0c503131007540e07040d00c408000d02801d10500f201c10203000e804104038502c184150790a01c045903440040000038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 795710953 1250 795709703 795709757
    0x1b23010c0917070b0f090a03050a052b08060424080705030708100b030a06050c030f09010c05121005090f010801060e150f040f06061709031908040f02060d0903 70
    0x50340201401c1c81030703030380003070280c45e903240f45003086494052581c012030b20340d00d45584216902d90210b00358070308100c02070142000b450812500a07140709441880c0d01001c4000710000810310000c100416040c1d1119001051030030704441e0b4160f00c0240114200d001c1205612418456005c0e03c080890507280100e00303c400c071004003009147e40302c8522074280003440c0242c040e0758540b0034059000e00007112805114420740c6030300310940e00c80c900010b43c0e4003810001001d1550691400a00c92140d0360810195150350040c845178800a42e1a10040c80d4010500e40110b42d20584207420407640c000c000f9907260589920f840240a0f89580790415161100240c0319401c01031841240b030369260402d98803c480040e40208089180705408007110101d4003a504100e00149145d002c60b0b400b01c941d0112150013440700401075141207a10010b00c480c1c44002d04c8264200070b10711001c00c0030f21010240780c0300303015002080301c3d03030350446a0510b0700140003581046000c1804600c0c0d40384005040102c441e25 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 795712203 1250 795710953 795710999
    0x614060304020108070e130209130e10200304050606130207030206072616020705030a020604060c05160e040210020d020606130e1f050c04061b23010c09 67
    0x464941e98015240a0402400042004012080b143c05560340840c030388000c0b081c403000141e4610070b81c411302c10032032070386885148014280001d007141e0000001d01c081e40b02e4040e13040062000300d82c0e0504003080c0c90f155906007c0d5400801400701b48840400d1442c001c840480344407034844030b03040c0144243e000d50100078000d60054000104001c0c024281040040203000103507541e081ca01c010302e4102101a40c0c1c401c101c1174200c0000391181c1e0100212005800218002c01101240f03900003030840c4298040d100400044004000400c541009003415049094410050315900c640b843c2600500c01c8078280d1041c0c0002854030403150020465030718189072070b07001c0d100541d1100184101950091784542100d642c4800d6286055400e103c05161400318014540712003a90700c05400c103035034018007000319015080200700103444d0450818501d000040c0e00240481100c0d00f848201d205a0300d80c841821102100910361202c0190b001284c0390380c068952a4010b41c85c1c00112100780c09502d80c03009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 795713453 1250 795712203 795712207
    0x408030307032f0d0e010513020a0504200a050705030a05030a1506080a0504110d08090406140d15060e0f18010606020d030902031c0503041403090d020f040f18020301061406 76
    0x40780f04568401004100220768021403924602002c05084907021541220901540c0700c0507011071a105588000603e02103505020103047c0e10b4451003076080002000d41d800d4000a039100d400c0c1d00070429185626005001d494a4501105002c3c081d41e00480384852124a014041d907004210b800d80201a90310030f0360303a03840b50394030006c1050041c440508151030702401d84007661060756424000d0000c0c5886180c0198860030000c0c01d1205a4015810071054840101c807600f149031100341100d10500e400040c20f46031100e41c5442c09000b420b840c0c000c03e81110143d42002900c440301c00c03015000341e85080710b80c180c030a070203c2c0c3c442c00c880043c040e8100580083c01b104c44014800d41214420500003020360f410b9009803071082c002014566001c0300411008420070040c000b448844a0f1048200e8000d1071501c8564000230b070404818020003449152030b0051541c40d5216a40415003060f1601800c000d80c0382800d102800401c500394040780309608001021841040d4a254840c00c000003500140c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 795714703 1250 795713453 795713531
    0x20d0315030b060910050a060e01031d0a080319050f01080c09090d12140403210912200604210e06030f1e07080a230106140702030102040803030703 65
    0x1340007000c0d1010a642030400720214641d90b42c401d03400b0003048140c07a00c031401b52410001505452004180070000501e200c0809001c400200322400d00f15808601d0984c0d90340c890088100100303906068004a6240004000c90211000d11841c140c44038001105d00c06000d01c1d0400440f100c0442d0400d0081d003044103410a020300030070402c442076036007a9001c01c68140c4070640025081d411103050340007a000302e100ca0126080106010b05400b12400c0501c2260700c1525610804050705030755034200084680c0a031918000034100d1165040240c06988a505180c00c0a0981c4c64100b004d4003001903051002c41c03012400b91802c00b0030f40034040d0201d0305640c0c40c00720b122200b9100038000b21a0650100807005006480d2000d98031424035611190700310306002001504541c400c4a00713043e0304800300400c41c55003420f0360781e890440315a454000d03c500312060a011460050a0f0700a4040d0b0020038040b568840201c00741d8070540d01d540d4100304410506600c0c41800b000e51905140d044171034107900c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 795715953 1250 795714703 795714709
    0xa23040507140409020d0f170c0705011805100c0b010605040e15040e07170c0904050c09060a0b1b0105090304030c090924020702040b09061305180d020d0315030b06 72
    0x300407020000d1001500c413200e0b40204104180d101021038a018180f90301408204148040780001c0d84100503042c140705201c184d1070b5035045540241810320a04d0950700450090b26254000a40390103441d090080702c2c0300d00701400d080f851590480c1c0e031500f0305001241c40c138031031303003c0c4c030111900313040d442840303859200b000045001020150f5030400e0315610b8403840317900708001da20028582c1c0035400444040d10320b07a003401d06000403e41c510032031580b41800040703000001ca1000300042212400615201ca8001480e046650703404802d5428000c91040a8001c140b603e500c0406180c0000b40b08503581c20040589074071171808020b090300e04042d010b21107000ba55200d0002c0c1d510403d6a03030345941060185e1a00011840c01c10101e00b50002045c1c03086007881d000e00c030350103c426180c101305820804005581044144440391605540e000000c81ea9407040c2540000010002709a902c83d102d001c03c020340f28410807404401007401c00702078465204008100d54220303a0004001c003a5900c440d810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 795717203 1250 795715953 795715979
    0x17091f090e060a0306020406080109060602060f040206090301060305070605120a09030c0b071103040b040914010b2209110301080f030f0711010302130b0d140c07020103020915030a23040507 83
    0xb56500440b0540700480011080e1004201810494917800c034290b00d400c510b0b200360744042e0000011500b002c3c0c10310072282c40c0301e044550095030451b070207500c4207201e00200380146004e50000e8078601c100d60001480e640c02200800311244092400341480d5904a0500b060b58400080100012680703006940800d4040110503000310181c034009040070050403085166400036041041254000542000740c11000d115409240c80d0030a4600c80962401c81018018010240c045480c00c11458420701c0003100324000c2c0010b090765a00810108403074014200154109010f44482449260841d540100001040d541041c020501991030440d0b60754070003501c003155040e014185030b024000791030381020200d00c40000d852440d1780c41e0b440380742c038151000c107441c604c00c00f50110003030110600030100c68500071501d007260203003005642d40ea885004240d503020a500401c2000e01c002c42070081e100317101c1d000940c46071501160019003142c0011100f00240d0280c9004103d41d1140608010288034841 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 795718453 1250 795717203 795717211
    0xa0f0609050a14070e0f07140f07150605090603060103150b0f0d060c0f030c0e040e030909192a0f1b0501020316021c05070f17091f090e 60
    0x2d031074000c52165a03c0c580d8081ca0100c0c50382c9900024028040181c900c250070380c0c02a002d02d03181429080c200d9010b03088200c50394010307505031030010310b070007443c0220001ca400b0035034003149000c4024040c500e15001408a405000e1040d000d201c003240341440c00148840c10b03603420aa881000c0710001e89a04014002c02c411590022035580084d01c00d40d4840d5140650b060040c007000c520b403071803007100405400c4642c000d00e00341480d103032044040991120036030070804001e6400140801000c0e006600d1030040d02e014130340c029014070400c0010448510b07800c0c0c0d0b1014030710080c40340340b402d010680c00074015140c0c0c201c2c0c1501e00100e0006c200d44245544600040ca07410075400b4545410031994004a1030042907880360340000a100844a15011100c04c090451000d8800c0c08501c0340c00c214980c0004c0c100c1030402030081245002c1c040e40210300d0950030791040150114841100e041c6159401481441e8454519040c0810705850344804031130702da40d215030318203021505221144800d420060 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 795719703 1250 795718453 795718463
    0x60506030a180215030708090d05040314030d0e03120121020402030a060e130512040509040308070e0a0e070f08090c100c0515090f07080c01050304151118030a0f0609 73
    0x59420409602e401404100303640d014131500b5501e140492000c0c16010000e842d0107000e0748a49421511664041c0a441c152130380184840c07403002c03004280b1851402030040030303021645049401c080c9180000003d000351107800c0c03072148140e030f607941c0c101054000301045201a02c041700c0200c00107107040c5d1b00542e0301481001c4d0024540f0b844505117003901c5c40458140074229540d444800500c00c0c1044204920340125410728a0a800e200200c0ca0242c8040d00c010140131014000ca1402d0f401108e0001114202801844410342d5508020302203000c10f0f200c2c10042692035401078080d92042c0c2c0017921400a10300208100b007081030a0029504858082004108403420300400250b001d01c080000404e601ca036100d040e05040c0c8006003401c0c01403500d00320660068104016081c030104020301e428100742001c1c0c1d181da60304d0a203041e0318a4410508802140b0b4030040ca1075001c010000381440440080740098811050010305030b0310540094041d01c006916110000060b103150041010345101e9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 795720953 1250 795719703 795719741
    0x6030b0a03080f1c0506150306130507091206020a0332130209010306020c120307121d060916052209060b030601120203010c0c030807180b0d1509060506030a 69
    0x518818040c0303000d03004c918a81c00c2d2140d061050510701030207901c18070150f6030903841c6103040a2001415428a005218454a494800280c43d241c0198440001858120000c1d45d040c0320b03e15006000f98000c85400380400d00d4003e07440d06440051090071140c001c0c2c0b07800c43e6200700d80c0c0440d000898900500341d800208001000c0f03001a00c881980c580250310480000d41c0b9141c0c00203400f810000c1680e00b243d41e450060082000b8036078001d1400588003000a030004031400f015011600c0c113000090104106d00c10b03076003480400040051413070010503142405002240c0c80304100000c0541140d040d4102403102d41414815501582c0000030480c49500005408d4280b0004603040c01800d9001c1640c0081514244003541400e005442c0d0611240c6000c0085e010241e03400f4182c440050600c004000401c0b0590b035500810300b0b440d10151804512468848907207903418006040041c40c90003000c00521000118400c8034020300080e03810043c011400d642c0c905048100400ca6480010f0321038041d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 795722203 1250 795720953 795720967
    0xa020909030d1509060b0901091403010b0618011413060e0a090608070905010501090e010e070c050618240105011d1009030b1e16050d0e0f0706030b0a03080f 69
    0x64483c81d00410304942c1803801591925403103c0403100741d07903c0710300901c1080240e41280d030b0f44284c6107802d588a00d00c05201c0050070b14046401001c460480c07a0304214000b403001d514000b040a0082000c00907602c0e8654000245804c0d591401004440d003440709000a00380200e1f80201d00c20076956601a000e40b801c00c9c0d880b0b80c62010b503502a41b04c0d420a07041118180411101e034050213004d00f07001e08251102034a00030700510000c0051158848242c3c400001c80c65403841402000074041d0000d00321010750900d2075001c0224445005403540358402c410035030200c01c10035203802d0084000407506000581c80e0000540300043c0f07400da4207075041d02e100b17080308855448030169042a84682d0743c0700302c20350a604d040b100b0b43c40c01504d02c1d03031013604078010342d11008101c071440c0307501002203559101032000c10b5034180c901c0e000e00040700d610142025020420030700002102424031000008940d031256030380130181c080341c81c0d0419103600607900c403074140003040704074009081011000c40c60510b4100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 795723453 1250 795722203 795722227
    0x11010e04091a040b0a0603030207060c1b0f060e0906180705160615210213150803180108160806060403150902130b13090c1d0f0f0403020a02090903 65
    0x420018108042c0810203000c2405804001c540c3d0160011800308071642c00c1d52400b03035490000d4450729041001c0552113004000d4504e41015070003000701601d1841d02e0b01c4000c4980c00c80c1d540d00500c00003c03040801d2420519282a560b07001e044041c28034062021002668031030803c0080004080c050308100e40c1826000010740c0900c8580203010005a1225041c0300325442052036000c030f15004541102000744443e10b2001520407a81120030004140c0e00681d1503018021048003681406000c0400060120010000b0036856400042000c01c6500c12030042d200740c0b00aa515031108200145081060b501070411160040d500414072410580e5940d207070071890030314502e4401d4054a0728040c80450600001515611409200c02d200243c0c60301c000c1050b454007181001c43d807a4a41d03400e0000e0040c0b20981d940507040b5044c42c2424101c02c25014038990f18160b540e90b0100744001f0019411142d081d03842801a50b041e8041d1440e15059020025140c8e80500307103001e42d0200f01b0010007000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 795724703 1250 795723453 795723473
    0x1080a0e0718090308060f130c090b0a0804051608030301030f0215030717010e0c12041703010605070c09020403021c03030b0a140102100b0a120f020301140a1811010e0409 75
    0x8102d1800b00e1102a540b40041c41c1d400c001c0d0186006282c144c00740000c03591410080702e40710342c80c0800011490b2246070101c8034074005901c141d12417800010010741b8682c0c00000148254012800c07a03811000074185101c0e95452482481625001400180700142c00d113144101c019000a010802c0c105108014034401e6006461040204aa481c502d1300c5c0520362a078094010020514000c27020301d051038101c07245200b440807035041d4681c8040003604001034100c0d0b540c0942c13070410900e41c4943c0c503500c0107400c640c4201c00980b2080d60304d90f00001c1d00d2840e8021101a02c4d409015a4140355807203500c441c0766040702400700c051603101c100200068540b050000010703c3c1302c020700503036015048000381c14147c2d00c0d1000b03050315080100c0046aa200c40c440b460458200010803001c6940ca0305051502e06c54000000f941035007800e103032416000d140f900242c0a20ba550b1703070811080813692444d5140e0b40351000000c120003290907514031190f0040c814440d807603802070004136105c0c003141d0740e031842c003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 795725953 1250 795724703 795724739
    0x10e060319150504051503030a0c03050f0703230405010c03050702060909040303020d0e03041a03040311010c02031c02031605130e010314190b0604091e26040501080a0e07 75
    0x10381041041645440d006003500040c0b403c80c45076480031000b0202342c0b02e204080544052083e540607a100701071081c0304407450603205002e01c41d00e48045103401041c0e440f000d24218291840440c0c4203010b130407110102c404881c016110071000c0030b20b6540c141d0f403682080b0320599004000f4486080541c80d0001e44902c558803a07030b40181c0d01c42c00c1c04a40b0003102c000341146945d0b644107000500081c03401059200c1c2141c900a54241c4039070307852508403100740c44403428001c1542402040c1c00f0080c3c00001406107454044030481000c440c80fa13404e000c80c001110a0038002e10710240e04800e683c020f500508184204240000c0c00c60303149c0008110151082e0700481c1d08040d00f4a0000b500b9805001c1100d150300300f8080c8400788001c2d038880300100039014044c0ea100d81d9441d03440d04104404020201e139a00e103004586140c803481750500d215400b1541045404903849030401d0908080c43c0300031507090390710585070484e40345c031341242c03d4000b0002035412110360b10070b010000c1108101a4820510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 795727203 1250 795725953 795725981
    0x206190e031b120c030d050405190f0c171f23180708071809060c020c090f0108100b040605310204060f08040f0804090e011406010e060319 61
    0x1003210912020b9241101e100028900c1c61014031607a00d0540d008001c0b40c5107440c040001090704d4a035824001d050003d85034042140320340e00c910a40c00c00500140c0940007a0140726076004240c0c1e10440300403214100c1940c188607822000c1d010502050074460b4800c0a020a0030015602c44d9100f0345101d11034000d0700c180da003030541d40304000102301fa0414941c1580d4140e000751480c585010b800d1039a50010307000d1240d80f080100190884031956900a20740380e50044800e105908600300040d44580c040d01300c030790045c090240050a2982200009412501c20500408a07108101c100b0320003050015840c562090315048002103075039071070400008408083c04a41c018282c0c100e58107041c100d40e00700c0800c0050051008100799a00805c140e210310300c250031310a50b155218a01034000750100c05004181c0d440100e40840e005d00c40750b00841c20096040700030010881c60005e56808040e0031240c0c0c0380001c00d03850b034030801030a240c030140d6000740490007401b1950515050402c251180e214804034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 795728453 1250 795727203 795727237
    0x320040204080f06090307020f131b0f0e0d03091509080709020c1009020307090902031f020d0606020c0901060f111213091a04020a0507060e06010602070608070206190e03 75
    0x510034074140001034121451100940c1f40090341e13801704030803c812808942c400c03003014600c0c2080c3d000c56081000040b0880741c03e80c001501c441000b625203211810f401c00003400125404d80300342452205040820381580b0b507208083c2c600300e01c00007450250380c00350040003981d40c0001400802000300c0000b40852110158540d5102d80d60b45180a04440d0340e549007508101d1042c001d030310041909400c2e030301440000f090303400442c00442e103016094903020403164000c201c51421075030071b0307409484060b204507410b20950380e1b00d14080340d817021228170890f488043d1074010001e00d405035007d100754134140e0400d6038100d211030000740d003009804070054803c0c000020765000002030140d000f10180960b01d80c20400114207100d0002c5000e803180c1d046000e1580018900355017030240d0b081d102c8481d8090414030000d02803d14481e1140420b10802002d407098200100304c00780030f00b484a100d01a280d0040019030348110510915000c80c0c024101403a5480b07400c100305d0401403000304040629048510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 795729703 1250 795728453 795728473
    0x915090d0219030b0603030315010804060e0a030e010e12030f030601020c031203011505030f0406270c08070f03021e042307090603020307091445070801032004020408 73
    0x4001070800405c01403098004204012901a680030b201c40d07444420310b03042e0f0380c03503a852400f04000d20914414000510903000c0c4802010381c411700c070ba80a00020382c0d402840e01e6050301401145c803151240702c10990814080e40c142000e002025541c0001c0502c1280c48a81780b88010a007048210f5085400c5410b000005201c0f0384c03250500c8485086191411900e98a400340da1000c0038140544020615500d608444407640c5449041ca42d00c280d007a41290b4603190a0b24001c9038034021803042410f1806100b000140c101500140b5504980e006030a40111862511440258901c0d8403001503007d40e45040b4035040e41521801100c00c030101001d0040b503070070441c9001d485a0b201d41c1c404400c150040080101984c4c0c401710340b070100c41c032410f950603130700040b900090f040740312201d1829181c02e002e105010074200803040b8408049030210746000811744548049102500481740600424060001080014104400c1083d00c0242c030031912030720141400005d050780e0040d8011201d81c2c0c0f01502003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 795730953 1250 795729703 795729713
    0x38040504060216080301240918112b0e12030406090501140a05090109030f050f041703070c060507110d110909061506040807060302032205150c0915090d021903 70
    0x40c08403c6001c081007d0000910080104600b4031801421610301e5280012a100c0c0401e401001e401d041a003881d07915980b1103001e8404210281445905840120a01501002d15441044070500454014101c4024001112055035001900803945641e843c03038a1004a042882091480100e0a10507003840c100b00d228002610006013042038540d2620080000181c0c2240c04461076a4160a0141d1200e50710b80140c107203401103522034400304982c00b610503450b06c0c0c0031000f4108184194540d0701c850f0f4a881c400c9400c1d020701c8200801c03080078800c1491040c40d00c00541c50309240328402c0c4604150306e6001103010f040c01510b041107194041d20030b100808141e2141951310300e0068031860304081ca4400301c0c0d6075904d10707885418141036001002c512401c01002c1514103d0103010326490b002c00246c903001e81d41d90010300920500920707003404921382248030350031108203000082482104407a1501180c4c1c3d12707130110907000e5103c00c40c68007140050f00c030b140c245c50f0700340c540c40241c140ba0b41c030b14146 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 795732203 1250 795730953 795730979
    0x5010303020601051356010225090f020c030d0506030705120316020301090f03020f10090201170a061806051002340e0a38040504060216080301 63
    0x48020355a051074403604042c907010080318103010a00c1c001d448402d908180d8246c20b05c400844c00002146c40c0c1c203c940c0b601c4016441002078290a900300c42c9a05480d4081540b070ba004810389500c1e00300c035110b04001200e0140c04c6803c45c6404410014030701604000c0301407556003c81100c07404a600c030000c011f554170301030202900400c82540c030816142400200507440e4841d422180d4003904a4014400a5450961140d038065501c440709140303054050801a5580104c100103003940c0c8074507801e0f10f0100c41c0502985090681c10b03110104860f101032180c21040500500ba001c00300d5541030002141c1102c4080006c00e0280c40b100010090f09000034829464040d20481003036502081500c010108468299843e0500c901d01c0c00c011940411502d5540c018940e10075060800988103200100c1c0c4554807504502e005e1410b0a00c115070700703258056041d505a44d003027000610582d00b0304801d00307203500303c0c0e9407107482210f00500d06002d07071031189a103007400c86042e549520007100601200141e142 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 795733453 1250 795732203 795732229
    0x71418010e0f060d02031806090a05060105040b130f14070f080a0b150a0e130209010e0f090c0a02030f070602030105010215240105070501090b2a0301050103020a0504090501030302060105 82
    0x250502c1d1180d03210011035624441c411000c000c10307070300000150034070801c0c0720003005684501c0181d0b00c503414181c000540e9218021402c0d00e0340e0055500000d00342c0307040c1c400c01000610160903110103035222031100000342800c80a00e40384030b8561940e0b4413500d1000c94038921440140e10b5200b61148002030050080c00000c1084044c01e2914405031883e541d126070300c10400c0d092500c000e9440d010310074201c2e0343e2840d40c403003c1e4000d030b00841c05142550154000d4240c1d0304d8207aa400ba109010034003008007600381c0b000b07031540107802140440e0110784504014042030200f40100ca00c2c040d8114140c54031940854800c0c0c880303e42c0400140a10341e81480141c0b101d42c0c0d007040e442102c2c00c10448048141c650301d500140740d0540d1842211569000e00f06480c01960498000c21004440b03040102444400f2140c00e031b5011070496031503d5184420005801d1000c8070722003541103a0078400150003d602c43c1d00c1d900c0600800340b100164042d19401a1400786110f540901101e501d49005c7c800041c0c0405 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 795734703 1250 795733453 795733459
    0x60f0a0e06010b1323061606320712150509010b070348080d06050f030a08180a03020613062c091503030a02010501261203071418010e 59
    0x10030942c8031390b21707001c10203031009904440140ea075a81c072150015035811040380040240782013164043e0303c246552554901e00303030045500c880f90381c0080d8071059107040031a6402d000c28550481d0382c042031030984c03007814005020a03010f1650341e202d00000b03c840009a010700c1c862080002c84400b01030f845003584c1c94005c01103010010018803400c1d101c40300031501c81026030f000900f5602e040310407941d21000c404c0070303004000240c0d10035500c020000a008580281c0f40681e41c0854410320718240010005900d9421030300c840e050852130540e05c1d00300c010090070345901007030302c180200c0980d442030004c0520720710031948850b40c145407030408de151784040e0004035508412031426070390b5105c100e901c01c98500c0003158000d82075502c0d00320090b145914460641d415101c04100c55408540560210341078070104100c0240ba141901540d590f51612000c0c200e6154025205242d031110707410300556000b076002d0525508880e000c0c042e840641d080803280c0c00c03404c400241c0840c0300d540c002c01c400c0501c82040d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 795735953 1250 795734703 795734729
    0x4060e160f0915020c040921210b03150c030f010605040321021f06180e030405061602060304030c0b0f0906070c0602090d05010204051305040302060f0a0e06010b13 72
    0x341102a100305014410383c0c45205544180f04192032003070150105405c801801000140c107942024004500140c5001391304200382e0035603105440c0114440d0060720090b030450310b94440c041248602401c1403002d80c1d509403180842c40c03001a0000c4259501c900c0070105099207910f03084035102c00004060b48035a0a100f800c01040c80454a10703134041c10041e41c000c240840b10501c1c0e61b000c130b142151580302c910032105142c0c5010240d003480d8100e03004403410380c2e4408584040500501d41224001180a5495481040100501e060400140a0b6900c596104c0052040b007500031505a901c200c1e4100c001030b101c071941404020302c15034003541003012800c51168502d89404000e07a50b0501400503802d00000c01c00220401c0b2154040700c64070800a41100c20035a82403820502035081805418030070211005c0585001c007141c810079210b41d8061b8028451501c0d040303244840b4006c06004c100201e600d800841c0c109501c20008030b8000c203024240d50f603983c015240709089841154003d0791a800350 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 795737203 1250 795735953 795735977
    0x10f090c14090402210a03050a090611030d0c20010b040c020a020a0e1005040614040b030d05070803040201090b03090c190e0114041508060a0f020f18040b04060e16 72
    0x284240c0c2d1584540c1c1030342c103140381200b241201c1c00180525814540c0920903042da413810585d2000240081d0405030f10b0720007140e5110a4107444801c4911014001503005200d030516104407904040c0c0d01e42001c2c20111001d503c1503090034002c001c4c08298107203907034591024085a080074031828603203182c0c610141469203a03c0c4d000800034103103485010090200ca4012640340c05140c24003000400c0d00501c100800e40d03845140040d4414141202807103645080c030b102072241008501290400368a0b80c501e4076102d2295601c0d54207400203031041e0b042103480140451340100001c000d5000c1c1ba9a00c7c018001c00c0814010855410551f070b00124407045100d908119145000c0301140c10f4807040c000040643c1480001b2030001c0003c405a4a1000c0300044005040c0c1004034507a405902080c0c0300307000c48041005000305038030031884814044c2000b00040c035030090400c803810310300060040000c0b420108400001d8140c0b0006d40140b410400c0101c18071022036404000e8515403a82d6007000510115 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 795738453 1250 795737203 795737209
    0xd1d06031303120212060306010503030a0206160507060603030815040e0309010809010e0105010e1501030911010c050a02090901140912030601050a02010204051807020d08270a0203010f090c14 84
    0x202801c058000400000d086003054080e0300301488003110358108640b50214298080b00d100404c2d1509802401950008100c90802000711007446000b40c00a202c2c81d00c0d2048040301401c0d102d000303141040760034070079000050300e2805050001c5000359074500341c500300700d50850003102c22030004921a41c075110042c0034081d404015220001c4003401c02d00002d41d01d840e01c0c680503004912004085510b0b2500100300300058805c45805a01c080021040c42c104500065048502e4440094011940d985003000a50302c50800d0b800014490b00c01e81e101189641c0c0455804402640d60074850394440b44850755484160710442e130b2001e0040001d106c840040c2c40d845030244000340c0140d041240010f440c09041e4000d4044500500028100440d0715111403000141000140c9140005010714205148480d1203181581d0180c0c00343c00c03000d0b1214024000e42d898524844600c0046401070901c86009660280308400800a240c400400d58003814600394040444907000503180400030009050591 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 795739703 1250 795738453 795738457
    0x41b030c09180314070f060f0903080901020a050409051306050907060f180e0606130909020108070e01090e06120304080109021c030504060513080a1407060903051f1d0d1d06 76
    0xf4085154803540d0303840342d04145a1b80814603001511050800440da0840e811992010211500130781d5418825102c1c4a466401e2b486007607101c1703001460a110034814a480c40d8003198111840a0803400c1021869543c0415144100c940305107542102e4000c2014a800a89400c10344001d0705e0f03c5885110b100d100721047e60501e000b0b9042d40700b84040050026260082121240345006c0340d11800c440d80d44c0543c0029100c200700403800520070b2404144414043e003c4034601c0790b4141c442d04212030410480c202481c0d0010180380c0c3c001075256500c00d074490180000d0028213100400440d020005006001c00c10b07054808040350000300c2004080480ea0050035207058950501e400b50350b45507031004403240c0596075000100580160410401002001000080345174110004d03a0720059a4074420345501c42944005005c2c2c3d004840f1200200c1c039203507080605040c502c8070020304030b90f100101d82a011112100700c082584954941c4a00783e0700000c0b100341d0410031700c040402918130000420054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 795740953 1250 795739703 795739727
    0x90c020f2a030a05011e0b0d02090703020f131e0806130305090a08060708010e060303090f0a26010f2904110319061d0609041b030c091803 61
    0x44107540c104800d0703054200034440345204018100c0301500e4250403c54001c000031800310326050005039440340c1411b01130040d9240d41000500541c4905d1094092000184006140104142c1d08020341e5100d42080d1020740429109280401841420800002001140d0404021412501c0c1804201c81103000030202d41c0803d0501c19501c0d01515480c2c20b84280c01003008043c0d1194a403c000301350b02c500080e006228481d107545d0f103c400d0360385071038030044010252801360f0135400030401d94050b07050464207200c00c20300250020080315650b41c00b083c45811703081c0413000d440c84e179131188076036010090045280104000307808210302d44076080e00082c000c661004603982c401c20081d082c0480e541d0707640682054010401c249549183c404040000c07401c0000c0300e044120b20786603020400c0a84000c0480300400100b003502e000751500703010422200b100400482d88444601021000400701100d9400107501c9042c0d0050140d08040d542010380d0141c800b410060302441000b40c020990244242c881 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 795742203 1250 795740953 795740983
    0x80f01230121050106170d031505060a1b06140709080a15091b0603110708030604020708071406070e03010e0d180803031005040c050a0816091e090c020f 67
    0x324541c0b82200c03289003401540c028059500c3c00364005050a14820030484a100c003000780e805001d03d01c101641190228081c00e06581e20301c503414004da06128005101c010720038242012060b400c80c0c0f844900401a1a0440d4044c0d10f0300400b400808801d904a5005071807400c1a00000e130801c5108e640d20444128090401040c8580003401700e1354561103000340e683c00024426201c0f43c485015a0554018891600020b1520300207a019500102c291071149900c50000d80ca50344500c0c08100c007a42040b0415140c07460b00304a258001155a200000032825400140c00c051604600140840103045070843c020b906050107d00ea245010920341204081c0d42007420000e807520640c00344942c074030f030071046180c48000b0501c8000070041403107604580742110705004c1e03082031f00e170100c1c0ea42c00303210300120103e620240070844c2c600c1d2041000b0450489451306c420340d599540000b9000d40086060786043c0344051506000041c1140030303070321844105000038210410807400e034660f9a1035281d01c00318 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 795743453 1250 795742203 795742229
    0x130b0402060c01022b0903080a02071e03020a02010e040501060e0409031b0506270d030f090c03110a061d121507090e060a060e0409051204080f012301 66
    0x31075403030400340c03100c001d0a803000315220029202d07002414481d00f00100881c1e406040103c0b541c02c800d010b0500c00c40e0b4155103407503154440042c07a034041d41200c082260048699445200704d81d0300800c0d4016424000e60080520441b1400050601954074022502a5042400500015030030078003113000c801096900060b41007082c10700315408c8404a0200c042d030010078090000740300700080c280b801480700c0c0121000840c1d004812200c4040900350f2010503410040000d903140d40a5400503c610b10f80810100c0c400c6407907507405102c487e041e001287c4424810850700c0303080c1010580c11001c0c1c80c803401c042c200c030652260703c0c0e040d82c641d600140e442803c221208407854181805210840c04c01d4000c440013500341000060140c0045010311030440c48100c0001d121840c0c40f01c00101254019140c080410380c401c010301000e401c11031010344092241d4a15881e02c41c0984d4010300c010041c2c4070240081071858444a425596003031081c03103610044240b80c41118081003079140c111192801194 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 795744703 1250 795743453 795743461
    0x2b140403050a030f021b150103030906200d090602010b0d021e150a020109020907031b0c030e030f1c03021305040e0709020d0b01031107121206050d050f1203130b 71
    0x40242420a8110404c1030021a0003a40b0b2007180c1c05c402280b0b4a1070059a0180b001e03600750380c1030300b0340912018001038004201040424050501210580794050000d140b071018046150700e41100442d010300040c0340d1000030840c1135428132554a50100c100d841c1580d0095640004424001c141c0303040180c0c0640321840e00f05a52940740300003100750f40903c41a1100390076107005e8020100e6150aa000720300003000140c10a20a205001c4c0740f03a091a4a100c0c0580070b500d00711401c1520110403820300080c6504032802d65010460184c480b05190024017442c60941d0660780300f0041e14001c0380c14140180841d0507111680784c80041030f50700644c0d00180c034050a8603100e14000f959400030034007a20016a403183c4e90043c1d04040702400003038905001c21080c080c1070100e944504140a00038100074030486181502c1603200c545840324050000c915140c440d0001040050342c42c00c1224240e1050301056503144d0284580a0841006441c0a0642c40c0200c400700e107038101608001c0003004d81c0c030700107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 795745953 1250 795744703 795744707
    0x1a04051e01022b0b060408030415030e0f06160203040b25020901120c050a241e0309060c030207081204060908180301060e0c070b06030307020301022b140403050a 71
    0x5546903022241021102c481a0030304009103c2d15500a000740f030381444003e20003402c007001101c0841e20464000c524003403602010007034902c29907001d2000c06445d01c0a842c0d00c00304c10400d078104604070802600c0c06003004801c6130b101c41c0c9544e01c0c0000b9504107001c20402000305070b081c2c0300407111036000346082c4145075480d01c0c07203038019040c020761240c1c400c0001300c0c0c082050503082401038403650369120517940b12000c00058140d680300700c1e030b18003e42c190002040c000f000e201000c0840c15092103481d4085440014110041c211f500c100060355a10040f01405254020711b81c2041103428118517051064a41c61114402c01000f408a0006074000c2010401d441d441081c1054200e980c280c1c58a844c1b1010389500b6410003e1a8480c0d070a001003c1003001c444503882d03000e0041003444600c1c1480c0e82e44c030111400002001d182d80741c04140403010241e2004c0c0000c0c540e182d51003444c032442c40618241400e00d03540300030020007114501080d40c0c08500a08071515003060305410300341d454201007401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 795747203 1250 795745953 795745957
    0xd06060803030c130b04050a030f02040f020307030c0e090105060406110304180906050f241305070f1d01020d0305060d02040f020307031d07062303131a04051e0102 72
    0x656040e00c4000200044500384402401d20b003000c101142c15110f40d071721031901c1d26010754060742c2c1c3d0281c24220f04000003050002451002d03480504007050810350350540c0c5c0100d810448000c008039480c2c2c40c0c0713880580e91080741034800d10000c4685c10300741d504203400700c3c526000f140074250500941c1003400c01e0909041041d10000c0c01c1044d0002801c030040440344000d450300d008101c52090030103010070524100002e10380d21400303840b07040b807503d0000e0001d01d008803c460304100d07801c020000207030b503040240750150501c10202a00d0700700481008000c001d0403900201640c0c50300b020104c140b5405030780c1c08100c0110000c5103107408140350321180c00040f955006144000d62141c42d0003818056902a90040c40c4a10b401b514204072108104064481c0044a148d1118003604190010306c002409889041500c0703820840c54a42808d000c402200907510a45d009540e0f52800c1d1460f10030801d02c0729094007007031b268040040c60303403e2581da510740c0ca5000c0c2050125841035500c095640703000940c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 795748453 1250 795747203 795747209
    0xb030a050a0c091a01080a110c010501170d110c210a0f030f181e0b1813020a052a071d06010507020a0b0a03020f0d05060306060f010e0d0606 62
    0x1050320761080c070528054035241c42d1485860072042c102a4115140e8100304c1030141c2004041e103d6030302c0c540e5000181030080c0600c0031243d0400c5000e121800968609216041c06460304003104d000d0046038240c0c2600c1d11120801700c400704202c5040c00d440260000c074158890200c251340020a5182d810280f4420008800322040745100790301500701400081092940054001d4544ac050110b92110803100303142244541110301c00d500508001034000b0440c0300010800d40d40d00c010b48980c0750a480c0c0a540d01c90488108101681840031016141181102070030f003805010442c0741101c100b10190041c007171841c0d00f101841400104c2c080640d440403482c28039078910816910031a4940602688a101641500042c40d12800008965501031002c0342d0049800824002c007031403030000c1000d402d50001d0782510030035070284240c254440c1510003030802c9541151020031341c0d18141007418502503005241e90310501100c0c0c401400c3d40d8020220441c0300f103054403c801c980f04541000b20140030564 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 795749703 1250 795748453 795748463
    0x8210c071a0d29120307080319091506091a04050a0609051006030510050612070c050304030b0601030c0306050a15050903030a080601090807030b220b04030e01140304050a060b030a 79
    0x10b220b070300400b050f00740e1100b4003801550320350192900090025000f00b441401500c1c5d4030411a5001050051000d0742e84600b03c130f0f01e404581e640d400c40603800d0340d020752002c9603001c1c041da1005030344440340e00030000901108082003060a01d10a00400510103059006000c0c40d610b50215000c0010381d0012006031941143c00e1050b410041514403d4081c22f100b100000307440c00001c00c3c065070884031000119103004110300d0420503408400902d80c00081c0105003400071001134540041c0c1c00b031015200450081d05010401d180c1000003505031216103800e00d007010b2900c2001d200ca80e0728488103100b50384402e500100304042c0d0b01d4081e1030500c6114282a410721000c0f9105410701e40c420750413803107070200381e072450f4150365030300d0344079550b02d816000044c00c40100800092800304401d480c0080001504034200c0303064801d407070354241030b04d0a0f02c068000800e05440118956003001c41c150500140d00c80301ba03c0d621b09a2141d40d01c0d401505001001e140c1c4402460300240c0d010001a0b20b499004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 795750953 1250 795749703 795749711
    0xc03240f0910150206131b1a04031a06030703080c151807051e22020a02010b0a0b040e0c0a20030d0f0b0d02131508210c071a0d 56
    0x102d85000400c1440d80715100340182c1c030340710505615101098150299681004000200700c1765607414904500c0b8091004110405460000b8203000c2044040c034a03110b011141c558640c254200420f260200f0012104010791348801d00116440009020084036040383c411511406103042660034880c0c1030344c0a4a00000303003400e110701d49400d010f002008505110840c2c2c4200d90b10b4090004050720004005010501c0c1e80300c1c41c2543c1446c801c146c20941d041e901c42034901e100384041c602203821001410b00140e41d80e4414485a00f031050515000c3c110101010f8241807601500c2150210014005400ca1002050300400180911002a00881c000000c1d01002c0c46920b205a0750341c102c07081c10a80e0b00e003004100008035445100b980f100380000703084110400c5064083c4604e1001d4081c69180aaa48a040c25400b03c4040c0c5410046c112280242c0300342d0001d80300c0f500030b41c0141d90f04852400c00400403840007040000e0160f00b214800b040818004411003c1e044040c003030844d14041950030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 795752203 1250 795750953 795750961
    0x30216240216080c04140f040f080909040803060a0f0f1703040807240302120f04050a0b09010c023c0304050409030c1401050106021908042103080c03240f09 69
    0x4070b0030300c81ca44c40a440410000303404510200c68990241e5001841c091400049000300b85d02d40c01e0004010b00541d4910300e0820144003284141e00100e07429a245640481031050a18000070131900038451304ca05645024200369a07040451881c1c4100894245460207109021006100b610002c01c0400c058440640d41e401203050441a40c50303002040007007410021003c58064400c1c0c409841800345804006c0d680c54061200c1450f002e001034995200b40c0300b1410008030b084007118401d0144a00110708908103c0d40031b8a03140b4600a9001141141d031046002c445110319410440c2ca01200041603030303120a40706900f18800c4e40c00254109080922200c2030641000c1e410f480103110780200b201e0380d000344a070142250320a001c3d110043c0c001c440d800308a40c00900312180d816018904d46441c09a98546400c00340c3d100d80900e0180d20741c10740761401410f802102050740406072003002440c518280c4250040c40541405070300000309048264030759074803510807251800384007800300812414 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 795753453 1250 795752203 795752219
    0x501092d02180907050307140a05090105030604090624060e06031b0c06010e1005010c02010c1b090e0c030d0512060607210c061b02030708030606090319030216240216 73
    0xc4110b5030540802c40c1200300280f03000358041200c50744a0680e9642f418007200b60011116680080c02e010b61042d110983c03840440e016201d15114222131042401c4041c1d204203034000c0d6880d081e40710809000703400f207220296889940460b940091044005004080b101102e5602c41c011800340080030f01c0b41100114403151801d500d00e0007183c0c0a000004040d40e2480111185400c85400038000f46002e11454000344510b4982c81100748a00c01014800351140d0032101102c10301c03001c1140b26401040c0518080c10180080c801900d03003403034803501e82603421210041c07072100908483d000c4d400c0018064180091000700801e180b1803580c01146210460500601407044020103503000b80c504001c020303c01c0181c1d8903a485903461900074500b010070a03103413505d141e0001426070f60400003c002c101207940c0d003031200f440084182e4502314566101410001d02d0801c01c9800388181d1103940134144607140140c218120200b0344e01d080404506040c1008030b041c42c0542c050405d00f40e0f014000860091 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 795754703 1250 795753453 795753457
    0x706030e0c06040b1303151a2d0a0503030f09090a20030703020d020403030807020624271e0f0618090a0c060c150203100317120a0501092d0218090705 66
    0x2510340140c0c001281c0703400c41003240e1100c00390440328518000c80c02d91700c9c806039083c840904000b4020000340c01180e4810110781107621142c4031090741c502c0024030383d0304c519000c407440d80c2000c035000e406c00030540c004d8020045d0f00000704071030340402d001100213503220f442501283d4817292000000d540316562868041d10100b42580d0240c098060700000401c2c440302c81c8825448001444981281221401d041c000442d007052549054030b0700b1b010a0140d9140b0440c0e8081c080d2152441c814440c15581c0312502d4501c501506052500c0200400e1102d070755594262120300394a00c010002c013139100c122860746002e8003035034001e0641101d2800003880f950461140180d8030301800c2040852000c5150020803403004031141c040c3c0d900007100500100e011000c031450441b00104045181000386d660075070864000f1119154070070380f544c0c0184014542c501038003014141101c01040301c0800c0798440081c01100b020744e801c407160701090b00450680e0b00d04c010121030401412000e0345040200c8000e21035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 795755953 1250 795754703 795754721
    0x61e0d0219140412030e03070806090714010f03180c0323061b0a0c061401031202030901080609060f040e10290d06020d0203090706030e0c06040b130315 67
    0x291075004494080c29014001003402d41480c190814941410010013008079402d00700f080c4c0800c08005030940b000d032020003008001d1721140d03004015501c1e26038880342c94580140c01840344610a000300804c10390300320020341940b40b25030801080c1001c7c095058148071b451298058514118494004203004403804a4208801116207100c1040c1c03840c1180d0381d54800a0300c26500f004151a1900b80703c10841018041c504a985001000f82110f42c0f40c85058035005580f203c101c1c04940010020485200050300da10a500d001441c1080c24010021302448070051115000d04880e5000030b545640c0d00c070301001031180c010402c10051303429001d00c2c0c1d0ba8544442500d200140b900407048441c03003d044d004e441038070b80c1c402001d130402d000e02c0500a040d20301500440d02280c09000700f1042c01c0302da002540c0308400c1c810080803801d1034640b00400fa20960303080c100341c0750001c6840310101c1e12141c0488003174030b04250b40a0b50f20822003034200c0c480e5000781c0c40903013820040b446000c42c0c110345030026401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 795757203 1250 795755953 795755977
    0x28030c020c0d0812040503120106020705030c0109060203090f03030f0d05060a0905060a061b060501060e03100c0f110a0204050c0d0e010209090402190503030307180801020c070302061e0d02 83
    0x3401c00900d040c004030450200e000741100310300b4413494440c4140a010b44e0751040c07013181901e040c40102c10144030b200d003007a006a00560803280060085080070000a024000c003403a06542c407902c0e00c00003941360b203d005140e80c0150006c0300b03914041c0e01c040040310000107035180013660742c801c0d40b01804001c05041c0c4999206084181000030182460700409000300c6008001111709441d040c400d54014040032802c20054481d0303c0080302180d81ca00c5280e0003002252200407074202101c040505100340414890151850b00c5840e003886603200c9400728028070103041c05070b5140b5416107203d203029048600294070030b04003801c10079560010805130240030503400c0c0134080290340c01c5100703003230b4000c144095811840349800600940b0345041986020007054080c0640e050b1141c000c13034215402190ac420200c0c2040390305030382610341518400000c099420085080c800c100c1d2040c0d85030b445510000c0e00c2503001040c0545501c0c85500c040348900b8546819644c0e034001100c103403019403c014200c2603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 795758453 1250 795757203 795757213
    0x10c031b020616031e05182b050c07120c0801051302130f0e1b030a020906060f130609230a0308030a0609090c051203190528030c02 58
    0x50100500c10310311040d9141e005086990794040505908210040403841016141d803000c42c00e14071883c038115510401400301080c10318005060062010300807440b03c0781607202c100d0301540e42040c0d199401c014001070b607030000e15188182c803c039098011000c925402e40201000010703c6842e007103043ca1400d124083c4d900d52541d83e18003e030f08a8004403050f50002e98580750344c0c001813034400d41054200511443c00200c0e145500c031f4400440311000000d40640e0701515003c10240b040c1702144452440490040409000c0c950103c0d100b0f18000d407049004186c040780242c00102c490040c1c0d500c41c0c00c583c0c00509070360780e0343c00014010703207191003494141c606482c1000e0960000b64204414080e000e00000c440701c0c9943c0c2c40d40c07010ba200411408840d5911580440c0c3c0c40110f00904000034041c5003e1101181030000b00100c14000842c0c140c81a4010040c500d019103c201804245070304909025441d9160551280d452182840714501c02d00301c10700c1002c0b00d20b40c0550003801d0700c4106500702c1d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 795759703 1250 795758453 795758471
    0x623092709070605040f150921030e370519030b0c0408060403110f070909020a0807060824090c0d050703020f041703090d05030703120b10030515060c010c03 69
    0x24402c3e118900445104032803481c4244500f5a1071030703850342100c22904d2300c030b41460340ea42d1300d80540700c80c041140c10080500007003541c14150b1008078000d68801c221b0b84017003d0100170703421840740f085d564918070302842d007051720b100c091401460707a60080401414440001c03043c0301d501500e03a0b403d07000442d60114040b000c158003100030310555094402d00382c01404030707807140d817401d59600350403d0420400c2d2040c400c091024050601106005080110011462082500c10401000d8150308500311a0f0300c4004104074007944800c041d43c014030b154860341d1030025a00850781c2c00000c0da2100079000050301e01070101c800d114030010049048001010486078880c82800c409031f11590442c2100720106000610455401a075102009241c0c04101c0349404802d0010070310300b034002141502e190f007020070b000b010f154000c1e1121540644850742081088481c4c0c0c00146a4000e000180042580c0d50001031624141a001c0c145a00300c0200807a0b141c03008004420701030a107200150700042e080c07985003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 795760953 1250 795759703 795759707
    0x812070305091902061b370302060601180306020f070204051003081e040f26010528020903010e06011424160c03050705090106230927090706 62
    0xe2500040d1202890102001540030007940750006c0051780d44501c240542c405044c18108040c002c80303a41c01c0c4090305004201390044910800c05181407104046d040400400250f01180c529448442400c188400c80e01d101046503101e869504014407103440054011035400c8200050300c2c0f03081c4201d4085c032865070b82188540d042a42440000e00186040c0081c0e11010540c00c43c6014614100d8805424291780e100c03000c0c3c000b0b040c2d50181030300e18641c03a02c50030040d00c05448540d500d601c11000380440d080c1080030342441040951012003805a5071000418628240c0403503200d03840040080c0140307002c400c00c2c42e4032100207110b410000c2081c0d010034809420040d000c41101c400c1d0500c200d445030100c20a84a1a0b40400c0300068500c003524032003c0060003207040380000d14000d80c01004104c4c1410240481c105044c1c00c07036814020f24000e800d00700c99014400f90070802c40201c2039a240c2811901185410540501e42039941c0b9a40e550758000c1401000254414840d4508407a07055581e9841 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 795762203 1250 795760953 795760963
    0x30708180a0c051302090a1205010507020f1c0c150b1309020f060a0905060406050304121b1101030f0603060203040611090109090903021903030507141309090c03081207030509 77
    0x8028244042c0040411552800c44800c0050b0005180c001d468a21b81400050710780120b5003100d218507402507040c1003400002d118269111036140010412012140c80c07090b5502500c0d841641d100340c1141808038480d226042445191380c5c400c00642d00240c84488130400352031000f110501494607409001e5600403107002e04031499801414101c680740110003445010740c0146440c00c18000214070000f03054840741c008000419559841039141e0501c2d26010802c8c1d21080340b40d0b070400c030340500034017461020390f0390000c1910351180c414a159040e00e80180d0142101064280c0e0b08c0d480c000000040c000d05070000c0d03220324418007040080480a01a512203030141c441c03024001380c00c001e02070008020a03481910f0301e03400303070046a40362006402d220718040007003a41280000d172100309104c01c40d60460a61200c401c040b00380a13050034000342d6601c0d00b0006510810040646808c400340a000d100103104000e140c004101c559250204403035841290300990b4000c00180c6800c002405a03000414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 795763453 1250 795762203 795762223
    0x9030d09060c02090a0b1f1d2d091503010b0d0b060d110d0309060f0819020a030207050a0605161e2f010e070603060305032d03070818 59
    0x2d450401c070352203400344200c9682c001d241284a40d81c039498000d655031850b5210b0f1010901801d81b510030051048000c00f5401e40f0001c0300b0b04140700c1512114540e603072125000c035503000040d0004c40340755076414040c0d0f068500b2042940261902040c06810b0f5a50200c20250b4003055009104c102e171003100344a07001071f804070040c1031410098081008c5113421401d200c4802c0c0151030705100150b0200005140c0c200e4020118003040c449202000003035007141e00082800410308100b04180361594400702512404419030b56036941c0011280c1c0c40d18002e0303050301c50b003540100c210344400b4401d1030440000c0c0b030250340441e20300e100c00c0507081e0700030b2180c240c07800c12902242440f010003c40c540e05484145004900005c0844650110b2440a41d03410610281041480020a081d0003900718030f030074090315400120070541403410600100f440081290000b8a800c000003c00e1120000e043d054100f06400d270a034005800001d0105843d80480140c0c0544407800d03403000c82c0c1483c1c00703280d5520a0404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 795764703 1250 795763453 795763457
    0x1150e0411010507060c18061b0305161a09061b09060d02090607052b2f07091e090308160e040e0307050d090303081b1e09030d0906 58
    0x30340080c000c6048801d0440c41810142d0404085a0340d981c00c1d949062010b0380020844660044180744589050b4011b00880c24500008811415442812500d004015080c448005400742d189604440c480340303025000003203841c80000002c030000d84140c0a07120313a0030034440c0301c001c02c20f035a1800016000840c5540c03004c515000e8141c00f813103030a80208144000b0140e09200c010f045840c1c1c03000405001344501c0161000d204c15641d20481d100280180ca00c10040700f010142115801c00ca003010b4600118090484c9040300480b000e220b1882001c401d4050301482900149002d040d4000c49600e00500403074004a000c4d044c110720468803d6040907000801c1080410300014281d46500c5c542c41e8140340500c0b1000750724012130140e49444004030603d44c00010184188a001d0100220710300301441e05100d210b2454038010b000c0300026010f692100c00c405030240000b271014003100d600c94107840903220781c5450140d8148481c0c200e051418000d0103140d0035488100c3c0305000c9201910015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 795765953 1250 795764703 795764729
    0x100b0403051b060c01231f0618150c050f16050f03070306022a030906030c0c0f07060f17100608130219050f090403051905041a0a090807030f020d0203010b0d140115 72
    0x23a0106c81d28032030000182410098000301280131083e10000034102c24003a215030741e203800c04c5d107001e900e81180510404c0380c5400558822141050548181e02215011600c44050031010740000c0c1c1043c3d0789a10091044e4400203200d44440942e4034980380310500d000c0708941c400c40ca500441d80b00e05c155800950f10100401c001109251600301034248120114211440d410318150b44601d05a820780045c408a43c0c004681003848c0d074072041c0b0808640741c9100f200100e0070100c210a0aa400300d001364400d204000c03001400685d1b5a41207140304580080c41500f0010703c580070030389011031170701500d0301618000b45c888030141402e150b00ca0055901d959480c0ca030282c02c07450380a003440091080e4080100c10000025004034052602107141b0000c4400c0781c0e50401c2d4400500011810303400503060360404074040011624110000304101c5d015140f408c076001c09440002d005101c000b0005d64407803071141c54039003800740280c2c81c415001c600c04004c2008580d850007180d03200f00203108800c00360102d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 795767203 1250 795765953 795765959
    0x13140a210318151e0608011d0c0f0d0c030b1005090603061b0c070305030904181a041109130201030e01091e03020a1505100b0403051b060c01231f 64
    0x3043c00b5424440c8011a000606042c0024220202000ea00c0c0c2010f91940300d40c41840441c00a104908200c00802412840010141205600d80d8a4400413601c54845e500d01c01203a03864603840320b03120036840400640e5803501c81c906009285415908c03200302040959002c500c034100900868081d400007001030803680d5524060805007001e080c0d0741e03c042c071402d06c011f00c20300808110f2140a54428006144c071900c106d814082112202e0b042c01000454543d00c2c8030114800c072070040005076031409521071a54650804841c207018044865400c0280c001c20404000507101084c0d00b80c40c800da0f4107004c8a001c00050701d0988481d890b01901c4085030402c9814081d2081e101d5040030fa11900503a52045460b07220b007174211001d010130490381600d5008004c1040340c10b9150f2006882660300311410f00d41140c440c1d0780c0e22070400d1229144101400802e42940e07840d0001d90f05420001c6009000c82407200091071450024400484020b0111101255100411500825003020144030946160345 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 795768453 1250 795767203 795767213
    0x1030c0608151f02120a03021213021302090619030e01110c101802040525030204060801050405190f090201110102070203060f1009060330050313140a210318 69
    0x2020401002580304100345c403c03030201c0c0c5402816000410383c40040c0c030744400502003109584000e201c844000d84c803d034410010f981b890864120360100940c01a1640071050209144c1c1c410606c4840041c107414400003140c031b6040d0400c003240109070f0028087c411802045000c24007911100340229000505000000740303581d8030501045003801c0055103e2038280d0081800c5500590f00310010400418880c000e041844280000c6168a0f150452503e85019401090711006000f084d00c19504d404c046a202e0301c140c1160711000f070b5618000c02c140b001d80380d01d00c0024040b0b5401207002c20340341104904d6845041c402e640040350042c0150049541b55819201c0d50800201016a10040248041140300c6a4858580610310492000d401524240101c2030309410074103020b5002c586040c2c50320f648076400001d1300c0c0c010300c254007054102c207103030b103010701100d40210501c2d6403500c601010a020700591803560751282e07000c02e020080e86015203008409a50b040030005204452818503040021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 795769703 1250 795768453 795768499
    0x3120605150d0618050f0906040b0703050408092124130c03050609010609050a0209010c120c1406060f060a08150f03011d0105061c020d0c050901030c060815 69
    0xb140c8102c005000b940341c10004403000303450700c40303010343c990303034008000006600018054129901030018102484c240c1e80c2d020300c1480051041d802c1544400200d01080f19840c16968400e40c020411001480e40543c031241154030304541e41d41d24400c520107800c4c80d0030801100803c030031030fa11500ca0150356040d0b504039080c09103081101c51414045000020230400d114007030040c0c03030003000451403e103800340300000d13560701409000030a481005208860fa82280803452140d03441842200d680003c031109460301840d0701005000d41c5100c0c00900c01461010400070700c03c4030704441801c002c043c004284112801640800c0021850600200700c1c6003c501c01403940c034100050126280705000d80103c2d0941e814115407116074122880310007810002800341640c8098143c456891300d200100101403201d81c14130f40a070281c00149146414407000070b069002501003e0001149560340f0b00d003800240645104a0000811400110b81d90f40001c2c060031400000041840a204c49181c540202e84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 795770953 1250 795769703 795769717
    0x1e01090507020c030304090501031106030c07032708150a060803040b0913020f13050f0105180409060504030c210f320403020310050106020d050d180f0312060515 71
    0x35100307030f04115000ea60200010030180c41c034210013241c65403451403c203032008803844402c3e1040d1024410070031350b05168404c0d54402505868080e0441850090900850200c4506825092007040c0c011032442d00025628140b040c0400b80380140750fa4402e0b040c01200c150b8003446005400420041000d41d6090015107181d0710000d00c490440d040c030400d41c80803640300c03a82903580d14001054030842c420318000c400005101c140c1d28800016190000213180740301b83d0a400348414109020340e45a0303120b59000074001030f4000420041810903040240c020310340290222014100030228920080b1400d02c1c05200800903100c0002c1c1c50f0041e2401d0b5400c04883e60b640d8001000e001251407500d82d40703007004021032855180d0f182d41c1c0b400c50043c03505106842c0340c41350515007841c0040001d66400191a040c02a072460440c1d02d50f80c4001003500502001013a2000b240790b084e1046082c4081320301049169880307911030040c1190b004882e0402e03110144185070380300801c1726002c00b41c0d4241800038012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 795772203 1250 795770953 795770957
    0x1205061c03022422030e010c1a010828170c1f0204060201060501091809020a0e0114091510080a0f0509010219171b070f060e061e01090507 61
    0x14071191000041281004022409052501003050082e090403001c82c0d013210f00d41c480c52000a003e05601c0c0074107642e050550803410020202d0414040c849000303e02e07140000040783c000c0c2c0550b510b4106658810080081880105510201003007100d141b4401c104901c0e40401000008224040c0e000003540180700c29601901541d01031102841424003e403684100310400140c8442c28510002c1c21100e580d00710605001c61034400b4004818803058034140b000c042c5d2400300e0300410620110305002225070201c1007610300c3e0f20011550000c000011082d122081d1050111655041984510b8414030008150010040600f6085861158884039401201890007180b0300980720191000c0362011681c40025940c003041500c10b2041c15000c1c0e54603002c0c02c0c42c196001c120640c0d0070809905010b4154007400342408080301c008040042500c814942200d01c6603a2071400741483c3d4003030520200310080c28018000080c00c03070b0665810410154142c58440c00c900ea0900d0b4078200100009025101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 795773453 1250 795772203 795772213
    0x1030c0c02030609210a0e04020a030605060d061410080a052a030402190803041806030c1e0902190c020d1b060e060f160201170a06061205061c0302 65
    0xc090780b0204000b60040805400801d5100c1010182008400070071030300100d51101006281c102c40d503c03100c0c03840001800c540044e80d86511603820340c000c001d00d6205a8001201040540a81d00b280d8000380481d1110690007000186402c2003044285d640d0607850007041408010420003c8940d126591001140d0388800006241380c50402600c22181d60913074224800108020031400c08a4094500710f182840c00c3d40d00a0401c900b05843c0e0085015520070888c248036503401d11005500210015504100c8000c4403e468104036140f1081c080d54958100d60316010000c1c6443d0f1038400c441e0302005141e10003070701003a80e5500b01c0e0201c140003010b036441010440c0c2907012849003c08262180c2c01881e107a01513919004e00134050481e2100821700c41c6e5000e00211911403018001c03030741c56040c150300e5111007503402d200503200b03c1c0c1114660f0340b807200042e041184004856000030103581d0103403589410420b22952800a07184103d80c0c09405c00c071091000c01d0701c1c203500940070750800e100e170042d64 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 795774703 1250 795773453 795773477
    0x1a040303050a170907030318121202150705030103060c08090c15040e250c030903020607050f0a11030c06040311060a14070c051809070b0d06170307030206061c0201030c 74
    0x1599400c015240c0540eaa003115078100101f50704542c40034095811500e001008514054810441245e52a80a020f034000590043d00140c42440b11544501c50744410170510308064100a0444d04240812103501d0b00c1c0c001104041c50040480b544209503600050465000c0c43c0140f00502c801d41b4640890f0b908184000b10307a0f2010040264407944070035400100403c0402c1c95002403a0034900c2c0041805181442a408203a00000e48410350303805070380803943d0384040d00d025032501030082c11580f41d5020300c1070b4640420115500f10152140201c041304d85522810301000712500c82d521005000000c020702c1c60001d42410005003441038024208140e410180348001c1c01194800c203400c43d00c401c11102d0a012903d800340c070218403800c42440c9a0310501c0e10341d11180d60f800d070383d00400300355160200d00140c443c1d05680100000e00118002d031013a6030101e0034410b60b031342c2004004801600420b40001c40c030b418621b100c5040391442024a000c88070032030700154000c103d00381d11603041104100002e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 795775953 1250 795774703 795774737
    0x10213090f0b03371a220f06060f060e0d031e0e04060905060108040f170f040f090207032c0409110f01030e03041a161505011a040303050a 61
    0x4210006035030400501d120a00620048110404000c1c00132400070f07080d048008945114544064909003002c500d400303440f40c1404800094558900d00d11104521200c00c0810546016180d9000d20a203000d10040d034440b81d0400b18114180204000121320f0b0f4001040b0349850042c10311014024103150712142103030a82c84180891780101c0e900814041c41d03506c3c203141000d20505008000a0300700300010700b010000204080b0029202602c00d0022154800034410fa4030169480e442c03a01041c1030b568184024612516089481a0910294040c00014144815008980c03a003685a43c0300c1452045220519525030004520b4000041ca401c481d40315989480c400c40900ca801390091040584a4404200c0d40106032683c080c101800c090884d07040c2c0f100042038a080e501c4900e0b42903126060309110070568003c00b9411030900d00250a080188000114074584000001a00340681da1320b035a00e0b40103840002c8500500b10000300301c10000b003440740740544040051854001d44809000d6a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 795777203 1250 795775953 795775963
    0x1050d2003100905010509060607060e0303090c0f0a0602190809151209070509011214030307031b090b041a09030a060b042a0c1b1409060102010213090f0b03 69
    0x1440c115000c00200b40000e035030401c0c040030000c1900300720502c200d43c180008240300040c01790074107005d0b010200c0d481007041100e41000c42400300742c038122900c0e440e01c010007955654115040310b0160810340241c0415042031028501a920705070011312004500748944070300340c1c2201d40305646c1440140021081907449036040078038481302d1190951103002d6036203056880c0101401420095010090402071074460100c07241c11034004400500200103281003140141c00181e00d10285804000108401143c02d0b0b4001f50b8040c200702d0203401d404420140c1603030b100c8154001d2106840c424031041010794100c40ca140308912903680301900303008001c2d010925100711140202d4a80fa00c035444000941000e1180310700702c2c0700b2202e02070300c170a4124074100303406421100a80c1c1003101d681d1030541480000e4070004440e80d0101c07002c400780e80c1d40b0070100044d00310405142d40304150140220748a5841402030703130403030440c0c84002d0319076500d000d24540c000c6c101075100014084d1145049403980ea001c7c04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 795778453 1250 795777203 795777251
    0x415121b060e04060801200c0111032e120803060d02090925050105040905090a0b010e06040c0c0b16021903120507021609050402010e0d050a020111011a01050d 70
    0x2ca003031481a40c9410881a40c0036a0014010b40e071521208407860a90a4044030401c1c0b040c840da6941e9107810b0400501501c0924034000c03103440000184400d030000300d800f2404202108051810220701c010603120b41c0202d501c0b503006030ba050252a0004101400d0040d03401000040403111034502c20b601103420018110740c0d00c140d54200501e15003081c000710640c0440c40122407440c40340c8074200b4002030001e000b14018514025136803800140c90f4030741040540c00041c2c03c003034400400c7d81e40c6e14420f042c0000032600b4034003d41c140b84c5a4800180280b1160800c558040c004602c2666003000c0072a403800460080703c00c51065079000c03820312902c0081c0c10310343c901a42d00c0200403400c41e03210b0401c1d600090301101c2154002945401d003111052841404d4a02914010846032903600040b96011008500715500c0503403410300c5000c2040000300b5000551003a01c0325141c10002d96529422904c80465030340741ca0b05188851380d01c80d889140104404061030000080c60500b0025080b65100666 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 795779703 1250 795778453 795778457
    0xb030c1c0b0f010f02030a08150306012303010908090607050c06030702070807121a09010902151215060a120e07080601030c08010509030904020c15150f0415121b06 72
    0x1a1040005081c110b0200392880c00038242200321545460b8000d642c1e100c2d04105100b0402000c0114840585c80d24041841000c003c0460b01c155841e810458035a100303051490240700e07000c4c0c00d0020981410b0080803030260304020b1300c41c10b000d894001d014542c2e0050344c04446501031154205450341d65040a1401803045900508105080460052820441e5000311090080c0c00251400140c203040481074000046007900055455201465002d401d942100a44c030503004030b030002c02c01310010007800d40603120800c80101034488060749242c2004100c050303504908100480160389000700f0903001301d219000e1001035005000d400140c00d00c034184d0080000782d04000010001c0c0b05002d01d154018207a080300030406402c2075404643e03244109000e0a0280d9000b14038540e583c00c0c00d0101e50140c03607403c4034074003103403404420b008081100500094400c211400ea000e185007001d121f4200192044145082c800303080048883c41d2019892040b0782d420104180c80701410300441d0090000e1500e0f07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 795780953 1250 795779703 795779711
    0x31203021201141c050606190f0e071202070f020108070504050a0f060e060a05190509060d0f18050a02040f0b120703051e0c1009150e0a0f050306010b030c1c 69
    0x2001007200c244604070b146100b0b41180c4c1c243c0404204046486600b0a80403507000301e10419400c555218030419a020350312000104000107149088006050721030355540d80d840061041420001d4103d004114019000106201d1940015409040c0c6a90045100c1c100307107050070707038402c0000d0f91004a41c01014403565204000c0107216001b10700f105050380112038050a024803910010007600403045400e0050260b0700d203210405001c1ea0031a1758181c4082c240565540c4400c44020107851b6400302142c0c007070b2601c52070119144905024410060f40007014080d4035a8613000c0101030802c2a00d07510542d03684031500c2e0115a00d000401e140d607400340c8060034409280d81007103800d1900b1425404c48040b520301e8014681080400c4000a4020488003980080c80d104c0302100e82c4021074118080c507503103480280e509180c11280d00640000100e8082003d151240c0b4100c0183e1154824550075170700c4040140040c804100107950f2107040307103106505159842c40384200e0100c0c80080412020340d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 795782203 1250 795780953 795780989
    0x51c110111040317030a1409010b0f0a05060f030a0e0a120f0e060409180b0a060311190b07051006090f0e0c0619020a0515160e0307031203021201 64
    0x200703000e41c10039400040201030400c0d00e15280d40b4a400000c081105100c18000000303005c0104c954081030141e40600071142c082e140c00103000c4c0c02050011101c2d4820b66540e16200345505c2e08080072010380320003801c001d00301006120268119040500301000003078858801d810041010011105013600032102c2c0c090582d40340d0000b034005650b07100318804208140e0300a2aa40d1141012031341141c03100c20000646010403080480c1210241400800f140c0140c000d00085082a41040703007070b03a00030308145c1d40c0b007001c110801100b000803000d00e6205402286040200381641800380400b140100c0a07285080799204030740301292100c1c1c1003550500d589007102d400f81300c4507124903040031320442e00405c1c0080c0400006007450041406a82c2d09241d42642044c0d078070310030300203410469484030464040c1002e0340801d18600d401241c1c50103c0282c041038484000d4071800c2da540d0782050150141611504544070b80803a00c2c00030084805054003040074001040700a401b031030003010848068041c0e062 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 795783453 1250 795782203 795782237
    0x121206080d0512070203042912090c011209021806060d0c1e030216150e030f0d0b010512071b0503030f0405010b0307030b06040b121009020405130b0a0504051c 70
    0x28001c4c040000315441070000384042a201a00c0f00c000c0d410300383c2240300d04601ca0900b0111031241042110321003a10b1018003820110001c0c9805010009032940c09180e030350391222404460402c0e002951080d0000c80540401c003403a40102c0c1c00100152240349040e444840c00c400703560030000f550000903100d00c0100c2009510ba000d419841c0010301d01589080b0344c0da94800b0790b14170032020280c0034103030340340c10403000c0f0115030701c20070040101006030b94881c611045181256001100b88100c074500707199864003a0f621810494039035031811450700403684c030350b81d600316441c9000541e881300a0480041e0040440c9003080a5403190a90b00c1a82060f07152900d0300b2030a480e000b3354828080d40c01880b06200282041c2e002e1036001c8801d40b000208990320b0000901c58440300b400202e403501408500252104482d0044410310303009030b0f004c1c015a19031625042c3c0b242c6c42c040c8090140c1080b01d0110714032401c0350304600d8220b030103901122001c035201c1c031104920941c1407044d074010400828881c801c0c51 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 795784703 1250 795783453 795783487
    0x110a05060304021311160305040305101512080706020301170c0603070203181c0c03110907052a12040306060b0301080d122421121206080d05 62
    0x4400c0c0e80907400e600303150340400c4c1c4030484840c00702c161944511036a4080400041560404003c00b0040381c212100d50a0103000c0d540030340425159030203981564000c620041c01203012081d00c002044921030b00d032800b1a1248014008120746000307003000500301091350343c00030358081c0c41d48002e1071148004406002d46040c8254011a004038000d01c200883c0ca40c01005407030301e4500c10030039804011816000101100d4440c2d4801e120860845558001d00521104500581f84205d50a0074042003502c1000300d900e804070380b540c1c006801001403241032003006440c04210284a540d10545500102c00309042612142100c0117100020800700140300036405007000400c141d014032442c41d41004102500c0e00c017016103030010f10407484c0035040800001c4c0e000c00c0b00c25804e403283d400101e40010000c56546218031600c000d116410b521b1175246100c441c404082960312521344c500c0c4500d840c405840390b060f014030b038000d0940c1e01d00000441500611803040350350026a2219036624810000f65218 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 795785953 1250 795784703 795784709
    0x40501080403231801020d1d030f070e0106021b090103060f1b050315120705060a110d0203030106090509070c060b040e0f03090418050d030510091a100e150d18110a 72
    0x107502410401c0040c5400420100f4891850548c0f050031407030701d802003860201041c2c0201d4061281080004030032007400100c40c142c6240d54251a81c204108030f101065603c11844035611034105401080003502070750048900084011012070f4480040c004056a00a01b244540218100004001c0e00074121080400e01034000c46402d2400f461210416030b030b03142140200d6018200026003205140c0c0600140038400404804035a10001c81e0a4029100d030002c1c07060324040b41c2841e01c041014940482541d11401c0180c4d01d4100148154a400c0081e08100c004d664200c1c0d030350300840c1c90b010300604c80031003428050002569502e01901c1488100ca0905070070859a25510f00c216002507004202c0c0102c40c82e161501242ca500e441140b038801c4603c0c2d0b804558028600a840c0d002681b00e20070070040c880c012580c2151700021150182d80315250400b0741540300d000c182e84003070350384c3c0140d000c0d02c0f240300c4281001811c0842904030302e00345099072500355030301c80f2444801451458942c0d555409 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 795787203 1250 795785953 795785957
    0x12010602070f0806061216141915080a110406080f0a050402210723030d080c070206130815040605070e01080402040507270e09010908040501080403231801 68
    0x1e280103900c98541402030070481c0305402c08162184905004c11000d454030140300c7d0780780740d6555104c0d104100d981e0b0050b10385000c0d61401da41d40e40940d181c16a400c04031008440031921400c138a4400302c90011006001c881074030780c0c401001031414810405400501519190011941801c000b582c001010051074410b505060804100060711441466140402d004041124650180300c3c0a401d0001a0300042c281401720341440c00110305a11300c08003000c07805d4040e00d6402c100494202d4407000120382d401c444180801640005007004d4009040282c924504c0c03070500d41d2104c4400f030401e0003941020451000090500091022a209154105a00341130007003503409004000b070080040104064440c3d551b510004d81018010388007016902c004088c0312941c1030800a81c00320141e05800307421940712130b502c0058041e00d41481100b4080342c02141c11400d10b45007200448a44000170421020004011040030205046628811800040313250301d540b01c040003014070f40501b14074114241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 795788453 1250 795787203 795787229
    0x60907030f03050a09080118020108090109020a050d06020d0606020304081005040c0513020c0106180e01050f1b0c1209090a0917090a030510020d0501050102031903050712021201060207 81
    0xa0a0001d810307091a40c14146140c40340c0700707800e00741e03000320141d8000c04040d400c1c01801c0602040503040c9030103141c0701740c03108401900c038000418203e44508000a41220aa400a00030f51920801032801c0610544000d031a09805070b202e2000d42d409a482500981d00100f41842080e80c20701c201d0580c0251a1010082c5180c95181c40809801e54401da47c0910b02c102d1440043e01d4558044520a0182400a00016a40c1c021043d54000741032400030885181c2250070800c51410f00803280902110f509455840c5c84d114925684e10428900da416034205c200010321046106014850200d541c90220507200c0a41070240400d01c2402071440e8a168070b00701c6100d001400568111040d89411903003c3c1e1200c84c1a4040740d0300517181d4102504500c07488225040e6055260001c284c05c081d60032041c441c0b0390740e0302d005a030b49008103011003644e07281c008080d11800d8869405541c1c409000c0c608a842e0ba0000c01c100c504903440404101500004000140003a5804111000090050480b046 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 795789703 1250 795788453 795788459
    0xe0606090c0409050c04080102070f03090506070312150509010e09010f02030106020a26072609010f050903190819020606030705130b040e0715081e07170a0e060907 72
    0x1c035080c40790b40079006140390b44d94046200160035509440142007190021540c80350f040c00d100c6200700855078203c1c001b41049001080d64200300068403881c40c0d041e02d501092125a04034034000e0304600103120f902020301c00c0e001949030b682c107001134001d08491f01c001005013001d034152400d45100300009260079004200410010b81e0020340035405682284a250381d401080f00c10b4514924000c4400c0020800801e02c0d1061140300c80720040309003920400038400016100441196016408105000c2402c01107540e29450103039005080483e002810b0342e03950824010201c449050b0108244c1d0031402c0420100041c0c00c14105080c601c4078140000c00c02442d040000030782d507070864001cac0c1d800364410415000b40008190407552600c50010402d01003555518035656440406110f13440c1c0704a022184000713414060700606001e40c0030220304450300010400740010071310f40900070208011002050011441150850390f004000e0780d5004202081c42d60052841c01501400041c61508501410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 795790953 1250 795789703 795789721
    0x3030506101e021011090a091116052112070e030712061b0c02091e06090702030d0c0f09050913031110020f13210204021803100e060609 60
    0x6035150000292990b080d1840d10b0800c03410808035580c814203032418241c80012a103580e0015110006081e00c4458465554181e030740251103503c8624006040100003803a001d40200c83c0d10070005002e10115504600c000d0100791000051003492810500701190400c94151f80c02c110b190000300d90300e4805040c050003400a42c07518828455a519104141c2c03508007003040d0380e0850b64072440d800604400d000544034014000348211b04c81203200302c426800061076074500d480d0001c0420300c1d0428090781503071020288001c1d04000341000003980b000f4858080b0000c4a4001d4408172583d41c0d80f49800003002104c09040030480b504907034400c02c1503004108a0726120b8101c1c204458041c54141e62000d110740115046c001c0c40c0340b8044030745000280c003450040154004140c2d0306003c00c0740c81c0000340c0e1106000741c030b4040d0303040340d100707020011421001601d0590068500c1d1416404881c40b01210600000d00e048003807a655412141c40e4184410124824040c0780c0d440f86090350344140c6807901d4265 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 795792203 1250 795790953 795790967
    0x60f02150f10050d0c0b090f0d0b0702012007020f01090e04060f0e010e0316020103090b0a020703020d0504260106170f010c020a02010c0b07090e01030602031503120d02070219120303050610 83
    0x3169624640898507559a0b0750f130742c123921500c1202401d0701040d4100c3d030410b00d050820803142d5101543c280b00d07024078180101605c0b03501c0000c181c611035042c551550700700451a0348041d05181004840b10300845c0201d501c80c803440c0100c2c45010006092851100404150703002d50600c2c2509900d070280840a200e0040204d850300700340689004025a11440103a0013803400c640041d00c1820f48004000e6910310540c010080e00c1d00903000c8940c001d4003008200d60510850140070f56180280514071007440615030b96900c41c464500c008100642c440480300020b0513605203510345607002c0100c640d0bc00c0310a1142007554041880901004a400d40003c1c0c0079241c1401c006108100010000f15040d20a0b403001c000b40030000e00c0800c103560340e818010080d420585a00c031070032f9584007040030030785000034500b40e8a06145101a003401c06805240c8000d4000600598011405141a510070b10407400300341c001c1c01884503010441455801d0047c21150010803480c0141042d6180c83c0d001134000e80c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 795793453 1250 795792203 795792209
    0x20d0f11041d040f08030f10090606050a110c03030c1b0604030b0f040804030f140609060103050721020604060201060e0106170c031305011416090f060f02150f10050d0c 74
    0x10303100580b43c0b8a451902c107920100f02030025030001c4144540020320b40c020b24054090403843c41c0c0b2a540341d000308000c40e4400d06c250b030003003413042004400d00c40c080c400325070741400e100098a07804d0b100c0e080401d04550007030081608030341065282858400320002a01b10f9440181c0c0e10318201819039035080e9102201030040ea0444241000140810000e80100d801031a406030340c001c007403c268580030a09201e1808100d810340190000111710b108002202812a90040001c01c0307180d1511524800195050b40c419070503d1424010002584070400104024800f580c0000f03001850101c14403020719040e04400e0410020104a10b444100404020f1f0040e0b04091a950741e52a500a4040d01d041450002001035080c03004c1e8119083c409130325039100310108089410701d2070240c0320480d2180740c5405010320482260b0801c0c0000d0384500c210001c20503140c0101c1d243c030b80703c0035000e0040101c100d030b10165810400041000101084040300010070068503a403030780140c036541d900d4a00507140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 795794703 1250 795793453 795793499
    0x2180703150b0703110703050d05030a0c020f0a060e12030c03010807060207080a0b06131a030f030a0503040b0408070506040b0a0609090f02010320120103051605010f050f0d020d0f1104 81
    0xb80040075507903011b1003940011640601220300c1112000d4000c0c04d25002101c81a01e00b074940b100f40740f00f032400411146c0c044200300f03014056502c200d03900d1000030211900158071034400e16000600c1c00d500c5000a50140103641612030b141d600d0410920b15001d00b17030300954215002403104200381d00300041d00401c2e19903c0102060603550b0303240840d04202440132410326650131310114100610602008000a4a050342961481503881080560300c0c4500c0c9044400640b0070000903001c07406940405400c00d101d03408540c502109519610302d05181a0b906590342c210100c14000f004442d40f00d100d001740b19080051000080a0f1645804510132040107418103459003009001500e0600610020355000803a090710b92200c000c1e10080b29100340003c0f500c40c480c52010050010305403042400701d9105075101100925441c1c001c8070185c2142c4012106030b070301448294040e603494000340604283c294400036901240e442442c0660b50028a68400a4410041444403511880004884100d10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 795795953 1250 795794703 795794717
    0x3040303020d1104120b1f050d0807081902071a310b07020108010b0313080711091303180312180b0c070f0b03011206090f02180703150b0703 62
    0x3040d01039016203c110104401c1c404005000301d500d0311207040282c9218040c0841441c107684894214902c88214050700d10000301031113040009151030059803242512402c143c605195040e80c4448641e000038200d095100101000b609005a040014100030000507401c06401d0a900008840b18800d56103500c80c0300203510b05010030354000040440320440c0c1807025054541d50740300041c40a8102e403100720f001501c081c0c000a18000181c060fa80070f0080205004510b00b4540d40701e180d80d03842404200c40e200a1018640020b44d2101c0c1c00c0c3d0f2203006480ea80c503012661914004149001070080803804443e074000078004078410f9a00c0e011100041d0404401400d00c0100480e0300b20340703070303846455401d0b80019260460074011542d00221010066000c2d4072351f8541c20402c00a0000b4001c01a82c090040c14003004242c01c0e40042e800c2c0d600442d0480d0443d40c0c0f0b900801c1c1d1400001da010f04008034150241700071070b40c5c144100320101c00303c421541f01e814200340c82c51030a0310030407030050308016403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 795797203 1250 795795953 795795967
    0x70f140d0f050c1504260316111501031101080906070806190b0c0c01020601080d0e010305070e0d2103150b0c03041e18020703080414070b040801020714120304030302 73
    0x42000404c488815072000070259180c140750440600109105100c5020030b41020088142c0042081e079000748040398503088204207219045503109190312060805200e0b803844e451007425000b80d000d018500440803880813000c4040054100305001c2c00203812584070034200060380e60310082054020304110b40791884038080d000814000b00740383d00308080c003040c00103000a040380c2c00900b022200e5400e801345c0d0040e83e41c07981000d403511036460300134011640c8503c0310300040d840b0b607100583c40340d120300f0032039080071004010502411020030304465400f51502c18a003042040208810403415601d41804420b1b50b00c44017064102e000e20030345d110404081250100030748140240c40241c500909070142c208002c401001c11554648034075030700e003c102c42e516148480180200c801050701611030000380e80303c503500d0030500648101901e000d401000800f00322285a1401400208501c00015032518100c2c203111151041400e8030f507040d5800200074003084801a01501d5000381c142c1401619005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 795798453 1250 795797203 795797227
    0x40b0403030204081006090e150c090a0914091e0a020d06020f030906040c0e1b0c0106090c031a03010606140c0f060f07030c020f0c04090201030b0303070f140d0f05 72
    0x940e8001101500449401020480b00313940b18208a61f0481d0003070286103e0581d20585601002d401031941d0850038001900740c40510000f070109100c00f5100d840e04603510f1031507030202c030341d892990384a000c103240c2030109100040051001c0c2d6800c001045034000488045142d4175000c40100074090800c80d096502405403d03410744000b4000c0584255491170001e13401515a1030440e004c9400a16480c0041034016181400910030000c2901d40b15040403c0444641d10b9006601950780c0d40d9200c01000c03424400a004031840da171121348010420301c0003e03151114001444610354000da161520401580b40d102001080c400c0c0582446951850303001c4551b400d006808490503290300c20403080c4842c000340050424442c00d05d40e86c04010022607003104076100c1c0c070040034500e425408900c0c110134510301a8400d000391407050500080781da50313020110341550070200d4140c4006100102c00c20500444008100d14500c00324080e00c01980e2058000d00400d44500001040080202d01c41071000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 795799703 1250 795798453 795798457
    0x10806280c0c08070606081b09060d050309211009170714240a0207030806120a0c1205120c2a03010207050a0c090e03090904030306051507020406051503040b04030302 73
    0x241c1c10111140d40c98105090040181480c0c2c800c1407880c1c0b0031140702358854003000d4110031034060024540719168a5500401c80c0866080d00306554034041084284505da85075014600304040018100c12401c2c0301401c0182003122600044502c80d0420519100062041c0c00c88a1180c0c00000019150407803428400990081c4200d00145881000c00010039651502c0c0080e0b40f00b1402c1c138400480d60b8035065480180c0c01442c40040205901001003605840c204540c000c2003410305040b2411401d807070712140380701c03000e650005140109840d00b0380280300d020700810a01d01c10030000309281c40880d03049695200c605140c50480c0701c569030308140c044075942e0681d011024004000f90b40703450141c2481921008040c0e001c40e0795407c2d120000900301c00c85d0140701d00c1c60b60076902450515040c0e0f0140300311404001c10480405544000108055807800d0300b40c20703114101610036031910040e10610003210120340010f48123540360405c00c0503220200742240c0d48258451001080c0b03460700e20b82074010b8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 795800953 1250 795799703 795799727
    0x114160803090a08070b15010c0203210906120610090303140309010b1503060420040605070f060e0a0512040f0512070801110702090c0c0309061305060304030305010806280c 76
    0x380b00000c1c0480070706c07408041c554043c803034030b80280741090192001541c0100c00004000d4044d04402e802c0302d20a01c0207507103417a5200c8245002460303c800b00c03001500640c484070b0003410b5000703000e06010003410a24681b074110590703410081c0250307003580c03000750290400400c104610382e0000009001c6501c203400c9a01b8a48000c0c180c40260803142600060340c0d0022210607020351b140405100140c03821101c0300103011334000242c0d00d03040c2446400c86a030381c0a03540035548901c0748002540000c03564031405003103080340000b41c040d8441785c1c038015080102200240320002c806200c10b00002d00e6500744a0200c40e0101d40b500715048000f2122810400140d00c0040701d546098285808003070054014510203200b21141440750b55040c2c6210351500a004003e401603006100010243c00c00c00c0050083c1a4201120444590b490001615030740c01210121700183d11075004100b003c108100a580281f03401c1e11010b0810102c031141200107600c007030040811915080304401d1203014a00c1c82000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 795802203 1250 795800953 795800963
    0xf18070905010b03060319030f050f04210209070309020a060e03150a0501080f0a080403030806130504050a140c10180b03010f0302030f070b04030609030e1c020114160803090a 77
    0xa40d83c1d9503007450300a8000711107840c003070b02030f10084441c0c0551508620080b9a41500d60380c100784141d0604031850340040611042a039400c202c04120f100030512405844411804030000549031403040c481d102d2005803a802c10726003003424082c01a600c08032044281c03003403442c10340e01055019002130326010016070000c0d91007810b1400d008620106401c400e040e550301c00c1c11114403121151980e5030b500700160b40541901005e100a00000e4072032408140c004030003c014040031802c0d1144282206c00c20744045441398056a00701c001c101d40e003445102c1c1c0b4905240238064901100f4041550304101200100c20012501404034408509520982c00380c180311000b40d4482d83c550003001400c2c3c3c09404180d1180c800c40f40004003400000078580d003551b100350b4402d0305091071681c4680c003600c0c3c0460200d080c8000c0c0100c204007500da42c000611192a0684095641c1040b40000b5103042c052015801c55a08104040f100f50120701c9201d00c0800d5010300034a60300c1d5100c0c5005402d090044d180248 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 795803453 1250 795802203 795802211
    0x60702041d0607080907060e09090a120201050411040e030307030902120706090504050f091c0c120810060813141501080a05010c0810030809040b060d09060b090f180709 74
    0xc0544000200340740301e50044d403502915510766904003540c2e25024401c0c900002c44281c814400e90038803076034158000681a0445040001503a2154010002c00c0422401030f03545400300320a1104841841c0c181030402ea0302000120420f41c8081d4403484010510000c0c1902c411005c2c0854891880c0d121615074003c081e00d0b80107403658001400c9540034840d182c07149040074080b6007002e0106489a00500100d0020280300d05014940b04001d40d0300c1c50750105004000c0245000f255240e0b00300c980b5003c2030303030b28500c0c4c0d031400b401e011000c140190440c0d001c102074401000004045000c1c4041030b150408550400c001d1000d1541e85810048881c00d84000456000080c1d50307400043c4060391548a0380c000e10420310540e10498080004480041e070484091001304082854000181100080034101043c201d210801040b800c0e4402035600c003009039116140d030188411482580031480045442154500700003c0f140c040c00c2000e00320a07600d0502c4e030301c507208076103003002218000c0c02d150030188 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 795804703 1250 795803453 795803501
    0x501032a0f09470303090906090406060305060106030507120b100e03120a08040302070816120813140315060d11010c0f0507090e1c0503060607060906320606070204 72
    0x920204181c4020810f000048a104042c1c58040203451080a0140810384159596030070840c201c00050f200b91585961680003001040091042c01c1c080c1ca4142c50104050034103050007400070b0081d40c90701d2006864102c0d403240e41e680300c04103500f4520903440c0420440e0203103000a41003c8190a0413010442e0024502d03c0140e009070615120b5030082d020b4666441d075070307920b10351640202001b40d2203045514005101e40a00741c0c8103001c00d540108442d5050200c01c0c80081d0000c40300c3c2d004034215012055100c580c5107000c001940891001480b903607200e00304440419001e0690803002080c00c0036000c2c038599a644120b40a02d440c80d04024032480810700c90400c1500c1e44040d000305520f00d4107005045050f2100015030b4800c541e00d60201891000001400f103405410141a003544882d0070060003010681c075008240d02c40b40904c078000350040480381044544981a54a080540040e0000f15441c0d01d00101d02603210905441a079642e40083c40040c00510358120012400c4501c3e00e814 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 795805953 1250 795804703 795804791
    0x100801091119170622120302031305011a0316081c0509091f051f030c03060b13170106050315190203190b010503100302120703060501032a0f09 63
    0x70300030f000b2017801003000030000040314401c00b00340001400c4051345140b84411070344284c2c000c56110f40c49604002d030020381580c50b2401d48490f031780d05c2d0741290444d074007074074280c81c00f070000414510465800188180c03600035070b251120080700180c4c84c0c3e940059403102c3d625000720100c0e13101c01d000070456005843d2140c2000c1508030500c0340d54011014060002c00c01c5c1c100440e528281c1602210205411000d0100480103840c903022000c0405848003800242e424002028200d0905242e0036001224203285402d220f11072104402280d980c1040381c00c0105e902c002c91010803040d059030320f4a42d59562070304030404940242201d0100c0034800010020001c80054102a044045002c11300c510303c4c02000440e0f49000941d01290501c0e0030500400062810181ca69402208101682c4c0c541c2e03a030392079480850740261320541e4031608590900c00134401014150b1917103550400100c58190404203502d08101040c002ca0400669401d01102c14a62003180060f15a00003101024006d060000d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 795807203 1250 795805953 795805963
    0x21b090c1b07080d030b0d08090f040608010903030b030a08030403080c1210180903080112060b181608042004021b010e1501053f010510080109111917 66
    0x5600f500e0003008001c2024a200340203d246001006010b6000700d541d649078104554400281d080d88950020300b004095100c6001d11801460f20700300000302110142400740c1a600401c403080d210f131f0485030102001466003402d80381c0041c0c15103002d113030341e83c1c130aa4826210f105202800c00c0c034124107810040c0111803903980c8000e50325501d24403904402d030401000280c40d80860000c020a02a60043c08211320100c2200fa00c280160004241d290402010900884003a0502c0d6a090215410400c4181a03410610803008441c504803210b460305440d101030056204a0070340b503003444101c2c40b404a50301c9405484882d9119002280000180d4400364020003801c030040c0014003554003800c10000810031034a0480310050034080d40202d15644006043e40200b410030459000301e03c05002020350700745c500c41d44210b58000001e003410411003422125085521180b01681010400000170b06c4132203c0e0080b082c000d42d01e402d412050f104000c2208001c640020151000d4054095449200081c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 795808453 1250 795807203 795807209
    0xc0f0f030f020105090a060c0e0d0605060301050105060a050a0c0201030e060a050f0c090a09050703021605030c2b08070e030109151b170c16150c021b090c1b07 70
    0x5506000c0701c001c110a9003030310811100c0a0b805d40086403142e0210704030350000998129545007e4000000b400000344c0c52410940041d034002c0d41c5c03001081010300f0244105400340030111002410000506001400d92080c96500360030050810080011a40207400c010540b414001c150b945900d4180301c0031006010807a1492000311568010500c000083c800311079a005025100724010350400454401410000e0412401c256081101452460000515075040741c42400515941d4642c03400c0c0d60b00d031000b800c074034603032220488506c0e142101d1001111081e0424070308103403003a56035401c02500d003550b00021264055003000340c0c007020806459070301001d8803070070b850400c10721005040301061403041a07511008220003d0324034482440383c860b0164088900c0507040c5c503001041e841c064440308130f903a08480404c01d0011b03000b6401c2190103403211030980740c40140380020981d14600c00d0b900720f00b40e50600611001011401a0083c50101d5801d5480d04030310640d141d003840c110365030b600c44501c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 795809703 1250 795808453 795808457
    0xe0d020d03020109111923090c040914010f290310061d06121b120109180803011a1306090806070807020c09070c1703060112020c1c0c0f0f03 62
    0x100b8243c0d041d24201c9605041d000081040011040c240040000409281801103145980310007c3c04001c0d92841180c0b03100e2412504902d482e2880c0028600c16500744648007060200ea1800500c1604203074151030302104d00c036070a081406015419001f080000310100009810000410030070f00c140d810307980c2c0040766a15030354600703902c100e030100d001044031140800d64840010000202a184540c0d087c2c1e0300001900b106400c0001c1000040110354810b0615450ba5001e440040080c04081e200d0f098540e2070800320b0804801c165a05e002040c481402903a06c440c40d200c107481d024400c0399080e83c2a031010030080381401c949490010b0304240451068071400d1080c000040c81040c032941c00300d4003640481e00104021000b034003c000708a03070010300210800103403550701000b040c84100303444c907045000c0362200d03903a00700b4100060070600151900680c16004105074405c0080008810a0310711a1035200302c5800740c0110115007428190201401d000d130803c203420140311914080b060954429 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 795810953 1250 795809703 795809723
    0x204020d09060c050c1608060a1d07030f1103010b180907030804030b0103020a06140301090c0c051606090807030506040803040303110309010608010c030c0e09180f010501051903050304060e0d020d03020109 90
    0x29104100009601e004001c4103410a0000c1168500d81d034208010240c4000c2034a56005c039400744080c6000501d0b433041d03c0580c10f82990030203024215544403150002a030003842440031450200f08030355040c1601062907024040099104c0c0002e11440c406950301203000350383c5517500c3c20702d0822210280820381c1702e42c0c90640c000561500400442c044e1518100443d401c5a103000030210041010300001011b220b00c070031104000440c107004415503065000d54202c811424081c0092103240d803500070209070b80c8080018004243c0c00500141d106070300607a0340b5680e5072646002c402800f200c0001800c080004010300c0001c0e141900840103540414008000507101340d03000303e096604006640020034080440c04206041010129902c040c0c41141c1c0319008400c40403103071a1840c43d052406481e59690018030080c074003000404e1004902600360b16026086172245500e910551186000f440075103114a01c144e11808170032501e0507002000e50740250000c1c14081e02800243c41c0c11940300c2d0f62 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 795812203 1250 795810953 795810973
    0x143610060506040315110d05090a050639040b1c0f1407030504060e030d0606020c0307080c0904060b030105010311011b1716021216080601120204020d09060c050c 71
    0x2c09001c0e00d04a0780c008505c0b9041e1092041c2e90002482544040403003d0b00402ca5003488000c140540c5001e195244010f2031134401c2c038144a41010005080600071201c4c1d50070071505160202c442c8280100c100740c0d142c02c04090240c00041d50321403607210021070007021440004034403920118020042c240c61041c81040300d40d481c1d58003115248462491003100c0080860f01c024800c1e807040d036029114590000d112813104150616580020700520016a2a81824000e5640c180100e90040c2e02c1070f001029170718100355881c4e0300d03009030103460b03802100d1890024080c009140c000003464030f8080d0080255585a05101c2c1c1004806801240801d0b80c0521030001040349141009159410038005058081000c078001d240d03030f1101c40d80004100141c40000003603031320102d803040c0d5203040070000c11009007140e100364000c0031a030f404140310360030140042100d40c0c010f030540755009504a030b0050f580c1001030f0848008000400c0c0291255180002603004690001c001b00303d0305804404460346210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 795813453 1250 795812203 795812209
    0x50307060203040e150a030f1e0605061005120604150308072f0a05041523030c030d020c190b0c01050a0f02070f02040f0e032b1436100605 61
    0x403030311701c0c181d0300130b00c00100810105412081011040340f094459603480d00c0650303400fa20740c120904064444580d1582482100c1c03078200e07070034404800c1d00d0505d907040c600c4c01080d082c0303d01001811140915140c258a10031228200c3d1090050b50340725419a4aa0b0f841d0300304000c480c0d400d1040c08160f0003180d4204404900c8040c080100e000d0700602a00c0014209024070001d031901191258801c0c001c2c40010032901034002c50b030440f184507045808a840203105c2010b107041d0815020600907000740f00c80d04881076010a2600792000196201d6a21b401d4014070b04041a6a07944610b43c0414045000c00b140c0c807041d0840d40c0a14040c0380c060200d00c4000e88500100e02c903440c0020200e181c6051903d0041c01d0580103032656400c80d08000800b0200d030107980342554007807405120324884d50f090882c410120381c580201c034040e07850400c0002c815000701407241c502020f022414054880e0145081307107101310341400002d005e080a001520110038211503031702c400d0001c640741d40c3da00b40071001c075082c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 795814703 1250 795813453 795813481
    0x915010f03021027030803040b060603010b0f030606070b070e1906051b0307062313080901080a0905070f171903050f040503010212041506061d0109050307060203040e 73
    0x782c0041064210098661041d40e14600c09080c2400e803240184002e40d4980d04024020020741c01650401c0c0c0e00d00e07007450300d01403103030004108a12409007400140325004a0f10f05807034442c07607142005a520348402c0e002a26031f00607480000c0064043c1c00c10441145d521000d0f0300100c07101661f0702091a0345580300c0a2804c141400340f0400194180003a4002c03008280d219101c0c2c3c040350050320305c5d0081584801d8256041034840c3c507040400c8402d01d55150100b14090350b80010f080403c0400d100050780c8152040c420321000504014040000c507a051b40d0701c1d8000c0c651940c1c060101d42040365900340c0707108009268482c03071f1410001c031400215106404181d06402444011025546480c00ea0f01030392181c22040f4101c0c2400002e010210b03080c0c40902c01060000400d41c1088030500e46071a118400c2d01751070000e40c54850400c003040000507041085407100400c030f091030320185c03080000101c80001040c1c0c4074681c584510f040018200c0c4d0044010800d407403a0424201a5a50f803006500ca82c0e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 795815953 1250 795814703 795814709
    0x601080420011b0305041e0e0105040b04020c0a050d030b0a0e010611031309390809010902040501090506010206090610091109030d0e0f01020c2202070503030915010f 73
    0x40030101100c1e1500d80c40320001c0050740e881c1410315550341c141c801141c0d041e182e2030b0b4000703d01145001074140039260207a0016050040c103d000303810140d0030203c0740e2200d11410302c00c0c28052a00c604c4241030695441d01a80c0094200c041103440848441c209203a44514404c80310011914026810280d42007190941091b5990300c400200ea50340b800104464011140e80d01417002c1c002070024820a040344a038800081545c01e0022406c0c100314940c203030b600d401c8172105925190301441c030b41c0d0b41042d90a201c0380340144542031492180d07031403194040c0540220f25000754000d02d00300000c00d941085620840c000d140030307030803503103942e4944407803a0b41d0740b80c10303907002540703020301c1e402000304141c5a0000d0b9140414400403504201c14200071902c4c08a0200d502c0011812901441c07010b4184080c094120352024802851200900e80204411078a012034181006400c03503481031140c40e05070100c503120381e406801c4035501e1400668060310365141810bc15541d20302d06000081503c850003a44084e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 795817203 1250 795815953 795815963
    0x8061f0c0c0609140603090c03060406060e0f04200102010e0a0503031b070203190f02041109010f0302191407020a0303050c0f0303012d030b130b0906151002150c04090506010804 78
    0x4454484d0100035907504002d282c070352184200300203200300c1d0f1020300680d8003452181078046010341c10714400d9840c42200400c2c125034081d0020812000c242202200e1405c2408406034460607240e400040340506000501c04015206080b040c03130812000200651141d07280e0780100d8188284252510642d10641c80c000c1c2d0305612001c1c0411543c0e0605507407180c264414034030007070081060341c0880c05032070307440d05010b214440101d55071041d542c12072403070754481609150461421003030480c49403603015842d0368481004002007e005c5803030070b050125036103503400410450740c140e80c80c60700500350b034825542d0700050700800051040c1a04004241ea0591318a070b01c040e0750301300b1a0300c3c01401011480d076a154002200d08000004280302c0c03a00a80100222940191110654180301c0e4008802a103810b001d50b000c0e5041010080c60380c4c400d000d04a004440048211140280032450311081020031000014081c0030b0011a043c441c00030030454a1080050066030303200801900c030550100c0780980 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 795818453 1250 795817203 795817229
    0x9050108070e0c0307050904050a020a030b040621020d1505010f121a0405190b150a05100302030c0409020d09060e01020a080c0a020f01020d06080f12070308061f0c0c0609 75
    0x80044004d50751124640c81c10506040707810000805442054403d1442c00347e00007042c1e1101507150192400d01101600c0c10f0040d00d00e0722a81020101000c000f03400d201c804124000115555004189440d54002c0c0c10b0340a0421801300a000604003803150081490410f000040c801c0310501244810542041408c1c0c081500c03a4001c1c601c00078000c0c02118a406015414030b03207809040468085a40501c07103a0825281181c2d04a03220802c6148180c0316841c051001c00041e0f440241283c0d420141e07140140e1a604e1f004101f002da40502d0b00400c4800f4000703d05400c940250303510414005006100c140141c60990001500700c0c8240075440340050822000201400a01401881e05c6402807048072940b03820f100b0260300f20b030050380e805086c141c0c8845041140c51030030800000158044000360041c030050700701c1034000344506e000c01030600400600140c81a44c1d070f0168800070720000c05440422540e0690300404c0390f0f010078402c99522000d140b010441911601042058a4084103d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 795819703 1250 795818453 795818461
    0x306010c030e040f0501091109060904090201050702100e030115120311070b22050307060807030906060b030a0e070905090c01030b3601050105090604030b04210909050108070e 77
    0x1660521040c4041c1c0500509100c9282981c40b503215060402104c018005040c0d4180092213003540d40c03000307c00c100c864091003041d8144e80c4a0080b43c0466104540006040c8054401601d850041c100080c1d44100415601c50780079820250b8a900c0320812002007165892000480c50940e20ba409031841d05080e10301101c001038007d0f0b2510300e1949005d401c0340c02140c4e032040c0d0f00c00c0f43e52210a0130305d0000d00b407000b00b0110701040700e40d29028200c1140905601414100d00074003207940200b0b00c0c0700309511416000180952540300300050f02030031a04075600e1408400000182c80344540070000e5200305072000492480612488e80101840c2024000c90901d060044026041d08601a0781c040f540c8003c14000160b11089000326400c5482d000500101111030303480e0383c00c016403100d1305201003044200c42560f540c00031a4180c0b070340006411201d4a55003061103502041d5002c105549040e0904028019004407400c002c403038405d0024451a0f0300c0c1d0221039255a018807035070b000c0d0300c5950045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 795820953 1250 795819703 795819707
    0x40b0a09030929040b04030c1521020d020a050a021015061d0d0f03020607031107061e0c0e040608031201170f150f060405060f042309070e01080d05030601 68
    0x3c0c1040403100d0103154100c291061480d2030607401070340485048240083c04108101c3d82148170401020b4201c8207071440e23250710034041c082c0000c00f2654560708081030122200c505507541501c0507048000c00440d1201c0603041c000d00107030f004296401c05440f4291010101c801c0c01c2c0504007038415042800d51074a85806008d0b101c030059851040c0f0140c1c0700354a844d041e80c075060303000304c0e56600640240c12000d00e070741400381c104032020f05072208050810808101c08506071048900e45a41300d040000c51407844e44c002500111291182080e1340d040c1000d01040c2d542c4290003591410086800704082d650750268103907284180c00d0544c07000c2100100411040404100c4004210801d4059841c0b0400c5424030f60b081611240c1194106500c2d03070107002d00414115000c0d03501c10b00c140c400700224108140014401205041043d1089880d18446400b006c41c140c030803e1681008110b111071070a10726005602c94402c1e01818138064801000051410000100541c20348482e840342485c5032994801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 795822203 1250 795820953 795820979
    0x60629030709051905090907150c021f08090601090b1f030b0a090504030f030626031b010f05090a032c12061803271c0506040b0a090309 60
    0x1900c81802840c00707000415440300c3c0d966a090340e58007081c0413402402e240400c455101d000d414016194025038042c04108808605440300b24501e0520020341680c903c0042d49607520b9220743c02150b00c1d0007600129042c1c100c01142c0c0984011740680b500d60380c0722a5600203c40090740503d62003114030001c1184000d06200040c0d41410610700820400c40d41c0c008207043c400f8952120034030654400c01c000034907038000e0100070003040300e20703040c00311500d0440303520300300e5441292040d04c0780700d9003424804890301007040724180710300c285601c00c5120703aa240d0140204a001c9983c90070500780b81c00683c3d00e02c00070035900c04540d450303200e0300c44240721842c0514156040e1a2044c6480c0303550006444282d49071781807100c04101003001010a844c02051129080d600d01c0041070b081d600500c1400c0081c0307055030041c0840201c919048010120729000240c6260491000816081d1345d15180c0090201c0030070454881d81c040c2180c2400c075202d10b10b91000301c0e003e1003805070000e07064030b90070722a0b540c0d9544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 795823453 1250 795822203 795822211
    0xb0414120d1407110a080d0f03092103060e010b070311030a0c0b040501090f060c0e0f09160309021309030f050405060a030203070e090a0c020f030c190c1d0406062903 73
    0x606216003c044d40100b0600c2105810401c415801856030210113135103c0c4820000c2c41c010b19003402408095501c00500d40c5803000109d200706400c4a0a414491081d07203e88002c0c031482c130f51101c082d40c1d10203114a03958800f550a40004d8403426282d110b0704800402c40725a0b0400da620300c0f040d0724052701c649103502c0e0045c004981e25501d0700e00550109000000e01400349004020000b01a40f0181001c0d0400610160300c4d40a0484040d5900840d41c804080c03a605c032030320607410f44010400401c110018551101d0080d8098841d098003e40c06400382e002000c42807094990001c18802c4001c07d6901c0e000d9072260a90203c810000017140740d1107034003c0c541080c1c007810030a120a594500194404800310750b0480750740d0b0f071000101c00143e41040b44044079400304015628200903e0075007a00c3d084460300f07078581d8124803032002d000c20201c04d0b407090007003118000c0c0b074111404146800d0702c4c0303d400f5641030b6540d81c109800810302080e0644411445030021a070034420042004402c44c071900014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 795824703 1250 795823453 795823463
    0x4080304170313090209100c030c03110c090c070501061e0603020f121612110315211b01050901080a0906020408100609140402090f100b0414120d1407 66
    0x2000f070f412198030341c2ea084000742185020140e20f841100c02070118a11449926030b080001d2803500c3e20110b030300804040c42891b098070380114070326800c2038040c4c944010356440a4002c0c0580f41044840d02c4400e024201c0d040c03045e030003031181e03035a9040c0340400c00c3d040307021800e0960300e240001c010050007540200178201c01c1c034502500b01044000800802c150458203251590076582e421203038190702496001c540c541c040c1c1c00700300000300c4901c0702d605404005d00102da4030041e40070110842d558412030070740810f1075407184800072288980284d140c07000040380320f550380410425031940e580103505440340ca010603501ca021590fa500c2d07031000680740d0000c5c00c0e20030503400c00c80400d00003814000085542640390740803170000d2030900090100c40700c1500c488044007500e820711005a8a14558a4200000340340304003c03501c9003841241280c0555000d00481c1b00006400500c5540c4107003520203080382100c90001c000c00c10300b0300c0380e2203544005000d40040e0920b1034210822032000c001d0800d881c010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 795825953 1250 795824703 795824707
    0xc1403090709050411030d020105100902130905180c0904020904080904090c080109170301030f0803041401060603060501023c1011030f0a020c03090f040f1103100605040803041703 79
    0xa2030b0410454406850503034405218854140640c00e082005540f039000300c1c80204546c0c80c00024100f000601401050340050300091b844000c520303441c0b410806000c220b4400c004c5410014440c0241700d10103000f00c9954007803105510800d01c0c3c0302c07000604c141c1e0098901101550f881d03440d00310550003400f01e658170607628065040492190100080500f449000003d080712050030410f4191101c1585150042e80c204014400108503580c800304040d07005103030303030b8903500c2d10f1401d000a10442d074200e80c004d40c6480d00006107a585600005c0446200380c0a490710700e14007001d4480307041e000030350b01e610910030140b0b228140d0348070f45034a100241450003500d403000c40440300701701600c2d6682200d5241701404001e01c03800c1c06005404540209682c1703800c501d418a418130242d2203000705d20205201e0690200003060701c1d160307a088818882c4e60218108010f8010600e414410342058a2500208100f00d40c00b14120b40282c0444003038030640f030000d50a0501d80000c041154500c000201c0c418041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 795827203 1250 795825953 795825959
    0x702100c03020a0f1b140f0603040503120903040302010e0f030606120a0204020c0d08011d01090510080a051f0207051b040212010807090f06060c11040204050d030e03100c14030907 79
    0x4180201d84103135100740b02d1440389802241c009212104150444400f0880694007071b8010780c1e030b0070340c0d107079440e0340035544030740c4039030f035500b442030550113414481355200008a00b005000d09011005200303907403003602c0e4040940c1040c82440302c0003400d00b510681503807281c00403800c0742c036064481411060301c01c0121480100a03601040030b9800908030500c9580c420ba0002c09616000304005025050080c800310518141884008011006100d544074040e566008103608811030790112020f80060001ca40c2c40f201c1d5860300598680001155124054028401500c4076031580200d441e91a004070081c40c00c00d95451130240840d03d0141529840780d801c20140100d0300121050318020300c5080090061103142124180998510b081e00c80440c0b440d10105014454102581c0d00225130452003000070718491502140080c86207800c02c0d6400b1141c000340104140d4007a074144400070041d801c1c1c41185542004080540d51907413212400308510080c40e40400094201440d4000301010445601d155 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 795828453 1250 795827203 795827213
    0x140d0203120f07061a010f050a02030f070f05160b0702060d1512120c1a0a06030212031c0203010503030702121624210b06090a060c170702100c03020a 66
    0x8458035440c02d2080300880e0072003d03c4483e21480c150080c2c0b0401c458914083d210000b8a80540303081e164052100c00324180010a10801c250f8442c41c801106003561030f01c1d18241001e5442440c0c40840c0c4c01d02c11083d0343c40c0441810003081d81125180301820781003420301e50030481903811400d80c02070159600c0b610748104031004500315006018040200888114a082003803101e0030300d403044409d004000c040c10001840e1741306214810b086d140c00341c0000e0740f25000c0d414090301003540040d500c252000381904c05082c011004007240c0707441e000303503c0300b400300e003101a010f83c00f003480307682d9068006100d0b01c00907090205003040d603500c07440c0c00e540c901844403401f24000c2d10f80e600f107481021080d02c5241e5032407040e06034000854640d411700076183c96105000444440c0040c82c1d0740345035500e50803440320a8031507006846034024010030f502017007a142c92006203d80001c50090703071f20194803180500110103001c1100d102c9500a480100b034000c4191050300c0c840c030340f4141102103110f24426040812 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 795829703 1250 795828453 795828457
    0x90103020f0d060312080c180d020901030b1f030c1a130902030103020f0909060411040e01020f13230409020a4b031b1e050405070504140d020312 64
    0x1814078400100c0354190b0070170f0405403a001a000c018420380f0801e002030000024144d480f64000d0100c1e8030989004c401c04107140c850200e0b80203420000090020080003503000ca524800e0203540c1200e40314000710000b254000d041c621000d0809110503030140910044411103440c1c0b0100c44a4081c80c14248002c0c640d85c66110740e010a148541c003100500442c41c0c6140c04002c01e0008a80160180c100010010b40700c1002034801806c3c84030854599a80d070b01e441e00058a0021a8002103444010780c12b04400b82d82e00070107030007803500400c1c40041001640c5200d84901107604411408010787d04c030301400024808030703e0590303000000d12800070300c400710740e46000000185400307154403a0000e911500c402c0c2c401c507044840011008900c0d0a40720510031100422641c0210031441b02c0203801070601d20803200368000035040b01d220380510208160007002002100c0d4180d41c10042030340c1304081281c160149028807407030540000ca920b56189000601803080d6400202954001d466054980720340d9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 795830953 1250 795829703 795829717
    0x30c100512270c040c2105090f01020406170105010201020a021f09240b040209030a031d032d010c0527060a0905030f0708060f10080a14011b14090103020f 68
    0x2c0d501c00c100401c0c0302c0c2841c4c01440340d40183d03400c3c148003400e41c20310b24203401521034254204850740c6000040c1c01c12020407002d050b100c1d04c02e0085540300e44a620007080e401444080141001841c00005483d505c14802c41c4d541d041a03601030324400c4001c2d0344c05090304682e54050200d0030703141d60f044008282520041414004680c0681c00d5a0441010391401e03181c046419510032031050003084450380300481c070780846591600c0c200e42400810641c6210603401000074981500c50213041c00f01c0156985804040c11481d44088a001c4c0c0c0600603181c00c3c1d840301031113200003e03030902107146042a500e0310040e4180740f0000140c0315402c401c0129103241c015a080380300040000c070b020405401e040c0842c5081168010151200a06000c1850f507100b0000e010b01071804810000a000d0800810f0008080c0401c00d043c2d680c2d607182403d2041801880703040e441510352034074080020300142242e0401c2521840e403a104070101440c0c1c900642d40e0030070000c09050580811552003008a080020554 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 795832203 1250 795830953 795831031
    0x5011a1b1011120a09080d33030b0c0c0a0210171510020c03060601050906041701020d06050117070305092b180b0304020603040609060c030506030c100512 68
    0x1d0703545800e0f06016002020b400140007515003014540410803c0040310a42001e400c008540c0d1038420754801030804c0440a000c0134030083c90075062181700100c0c2c00c81c0071207010714101800f9885501c854a4144500c940c2030304c0300d5101c030390f400d070040c20800c80b403080b040c00e41d04040f501c0c0d00101030340000415040b40c82d24512290110818094540400d0203240c544c0c05100400200510001096880c040500402c1c1404804142c1095980e64041101c1c080c4c240080e5200c490200188014081d4000a03801c41803035003440b02c007044079403281503503880c0a2103608105c001e0ba11208800d500401010300303408006d0041c0c205005028213120415003502e032051f1300e25210060103410042120207010030b61414403038103070000c011110f2031b582502c0d0415012903d06603203456a2420780010407035540001c110508001b5071003840c54055111f45e1080c0000d60564288140b15010001241902180000411828004507020044e040545039128070742c21703040c54800c4654110000c03601c0f00d4000d4914 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 795833453 1250 795832203 795832207
    0x4050a12020d140d060f03240506010806040b010915050702100905060712021c11070e07020a060b0f15041403060103021e03160f0905011a1b1011 64
    0x104218001030a111118520140000522070000106945011844480d038001c001c07500241d0f054640d80400c00901401410f04030442d0b0342d28140d00d84130421214411442e49055050040c070003107004191240e041651800d030701c0d5072071070b0421001b0540c201c8054100101c1c4000070a41000e8040c50032206501901c0e041c4d120310042c410000300c00c4075099114108034415100b0885612060141c86000b940510200d000d00c83c410412807803c4010336800e00d50400402c901401d168202d10800e0410520006442140d91518056004007406540c110010b0340150090000f140c0e00764090303025060024a402d440d406c840000500c1c070f510a52a480d480c280c0000c0c1005015445034441400c80780590140c1155850764001607000c5084401c0e0018502c076031504440203540c180980906a40090300074911340f51540c11a07211010240240e0f150300e03207030000104825074018003030001c0c12102c0101605c2c1464864218005030a103076820f203040d104410314180b190398103000d0600710141c2815a19 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 795834703 1250 795833453 795833473
    0x40b0a0f110102161401020a1704080c100f0b0f10030e0f0706050c0d0f0507170d0e030414241b030a12110703090306150504020706050105100503011514090301050405 73
    0x51728150081c40c5401d41e0300c100090003002c1d030444003041e40c40c1c4000030401c815513618200341e4a1071081c080007541e036000320143c664180c03503d90300c000c580c0c0c16000c4042200760542e0b0301f4010104042c0b01066440f010304220a40507174400d40145c01001104020740e06244074010310b0b03a190080b00d402800c0072500c085a8035600542c1005800d01c60788040c6400c0b0700310742076400e01404a1203040307409044a0090303c1c0101d039070398100c0111031b02d04001e00c9027085104040e840700d070f407a50804e015140800414040b01d402c0e074a0402d40b80244610802040c61507404a103045140c107510054030b10040078480c2c11032082c80c00327007880a0f09041100382c5840a80b180c407607141008a501c050740c4032200c284180300080c01300f1b034440b00c0d21090300c1d4030920026040491200c003409181d078642c01560300c1030001410704100106604910b0494100340c907101c251010440301620580000d00440e075003007943c0d5884088044c81588182007217503010b0300040c544900007002c607081d00c8003118140c0382540f10040304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 795835953 1250 795834703 795834713
    0x20c030705100b090708013b040512090109120c0e0c0d050703020f1b0f10140112021f030b042d180201080603030d020a020d090b040b0a0f11010216 65
    0x44240848104c0303e00d6401e14040710040c014401c18040c56446a0314005111004080405020080000c1301040e105c42843c01a44440403c0212804c0b80c582c00340803202e580b44145c5038261401d003501611410b040506004030380c5107141880070b0586d014a000c0000068400894803414024402080a10f40d940b07030011040040e0b4401810001c1054030400082200403c1d440a403a440e0180b8150402e909a10b481001e24103200c3c10a51442ca0064001c01020000f86902c100f14220740300042605a80c0c0c3c03a1402036038090315800c06500000c003203070754841920b5410010740c4064003070300b00041e400c801000420100c400d1882c14010f14249000a180900034150301d6840c02c8107060000e11a2281105c140c03140c540700c0c004020f041c000302001040c0c07a0740d4148191000103900d40e00031074860800010080d52540151221004103101810104e034030400e02c2e04507800c0d41c0888484a00d800c0800c4d008481820710040e0307502c00c000c0143d82e1204101c41c01c2c0010211039541e00000d02c0a500d140c208 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 795837203 1250 795835953 795835961
    0x60d112b0c0602030f07020111070e070507060b0a0f03080d02192109020f0f010504090c170f040302120f0c070306060f0e01030506130203030c030a03060e06061c0b010201020c03070510 81
    0x3000c0b0a540c03041c0200d440ca503540c07108948602d40c4c2803174504084003c005005180100c0354100810084801741000280b82e0b0040151910394010728003403064071110700034010f00315101d004e1058814805c03041880400c0c0c08400418440812800040c07030001960485d900030300000d0900800101c09042d203410703001030003c00176003422003070b0b00800100d041c650004003041c010b034030014010315011400c11016070040382554001d103041c2e001403150440e800b400400c840c08140c070030308020b180d00000c84c2d500f15074501c00d544034aa0680080c0800100500d41108a4010380d0031a140004c0c01c015078004c450080c0400b1004603ca9400880c24604024110801079180d0f00b0107440ca44241d001003011580005465400c00c032900d6200e05010030b1800440e00310300c80c20072401000c0c400000e03a02c40166041d80140704442e411128040d06440d002c042003020300c6070017160b48800d2001041100350001c3d560205002d618140001450301c404421800d0454101a900361815004170580d403c0c03155003800303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 795838453 1250 795837203 795837209
    0x15090a240c0c0305160e010b09090114370602071d06040b12010f0f020f1b01060e011712030c22081f05061c11010c150903020c010503060d112b0c 64
    0x11007072741000b42c4d600c04101c8920b014031802c6824407207450010041c0c0c03540310071003004840000da52107245a14a8410040a500340d000303071118015000e00080c03880c4049186130540c0c102d8022811b1a00888800da070000e0400b40ca40c0364801d648400d01c8441d03946c0d401101482480d40c4001140d40c2894405c0b08003100c208204170001c140c0100520f00003030080c80304032111400c03004004818522401503a50040113141c004c1380c00c14000c4000400d514070404259024a54040c007200c00a072525510301c041c0b400155460240004140000582510901142e40108a110001303803445a6590301742490200d821707801041403541703500c0e041d8240041e4015254841816504c000740002030b80c86404280e0040c15000d001820f522110f81280da20404070307680744e150401d031412402020b00a885000b020200c4013280940b054441c1801c0c0e5500807401c0c5c03842030b00001c1208180318055241d2189140c401c0d501c441d441055250150800b1461004d00c009440512107c0c001080c514580f01d25454030b0307a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 795839703 1250 795838453 795838469
    0x1e030415060f05010e090a0608030f073c030e130f1404020d17070c1d13020306180a140d0f0908030405120a0215090a240c0c0305160e01 60
    0x1a400b0300951740c0000c42900400e40c2565003c400da60b50f0350000313000707203003680040000340000154070424a0030f2401030008140078511002c584c1e0b085883d001a05140c00d00c81e0400c030001c8480650403c980d284002e01d1590090600300c03e0745a450002038030001411b00d01070003403961894540d40c0c045184c41178000142c00701d4004815820650001224800c150500070306ca412680c0b010b0700800700c014140e0320a2944a0288184551149901a04090954403903440078a0030030000d4800e08003c580c5d1030381d003038010300504203e446005801481c070400e003e1416541c03040da00c2d800001000d1000d40801c54015001401e99584040002862540710b52101c04c10888245014000f150300031088800315802124041c1c061039840b0380241c10080842c001942c030940360071116080003044001014204d40442c0d2041c40701e6102e405820b407000030b80040c001c00044040360503035042c0c00740c03d40ca0b4100740a0701405801c603550340d4a0070303e0302016040081003244804c60803c000131001e054503015004034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 795840953 1250 795839703 795839729
    0x1b010f0204140913260307080f07020604150c0c080f040f0503061e07093f03021009080c060c09040b09011202150f131d09121e03041506 60
    0x200c4d201c00d203604008000a01809032402064a280038002010095044c01002003912407905103c0603000c90400c071580c2150040d00b02c001041c0760b10101e40240301d182d024602841ca401c1d00d00b4072900602da154903000074011402c0441d404a030300031019011288400d0250340d41c83e401c0110b800350b90034151f4413203402544040e050040d00280d85211240b80d0300941d550010540e9506021240552103030b10103025001c124411036006181c1754100c80c0703082d000d200700c402024000c0009110a004c4424064010380183c0304541d02c8042c29086029030b035015003906410012031f000d4003410520162400c006000e80014040090b04040c00380d071403130010440303516220390716107401d18400301040c1c88002d00c202000782580c0c41034484401528203004280d0070160311401c0c29218420040020300410030125501800c102d000141c84409500c5030080c03e018120001c1e01c0d01c1202590b0300319140450010207070780c01d905490001c0c0b0000c2d61060b8040d0348040e0000c0c0400382d4040840d095500150481506 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 795842203 1250 795840953 795840961
    0x20c1b040c05160614070201022805220306020c1006050d02060702060a1205070309050f030c120309010204051009093903060e150a08070501141b010f02041409 70
    0x2082c19a40b020f0b81c8034007a0000c404031454500000e040d090528036019854000340031803030740c0c154090901410030000c4200b0030386440c204240340d040c44002040008000b003128800c0e841c1b0080342c600d0084504411444580c0d12a40c03070030140e800209982c4000d6000550f09180741c8035034020347c5d00410382540d03142c0305814180c01041c943e200712070000e4020000047c3c0c440300c0078442c410000700759042c0c08040201d0b0420442c02006040c03c20b400365641d02c5140c1500102e03500200868410031401d0004004400784500d0061940e0801881000325541c24000010f65031a0743c0c0307143d610903520b60f40710107410b41850303082c004a41e42560000c030802c0590001c160384001032144205403800440c4010429017019004134007505554100c80d010086010510150400c400c030300151002c400c03501103000a4075800e98540d02c4a10b0b01c181800190813207a07411120102c50001c25800b02488080c1c00e142c599a0b40f01c600359804a154214002da00180130030030910989081a900312046421140f6420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 795843453 1250 795842203 795842207
    0x40c0f0f14030a02041e0b060f3702010204051c05060402011d130c020d02060f0601210e07050a05040b061c02070b070201150504110706050712020c1b040c 68
    0x20305000d8149410740e01d00118000c2e507020007044004960052040c402920702003603401d55010074410303c0451701d08106407510640b401c4070942c1d030054504000e4a0521000d80a20b0320254a8807001e4800c03251205050320201c2c0060b010005181002d800159503540340c40f01303000440c0701880d0f4420305008180300b0f000018001242c459005070b0246482e98459031050104544901420310b03461b40302c0f1540c0c403510302c007a03816040044c042c5c141d5000d0794558100e540043ea150741d002c58824900c079064400266956000e40c81e00200e40b603401c59482160603810101004071404410f13449815880141c040166282c8244003070080c1c07000b0344043c011501030b0340100341c02d8021080403a03801b4010054072091035050394143c40915401c60154035642c206210040d000300a1002d058002004a0700040313183c2c102030281010350392680f0b090f5441c1c540c00713071694402041d02900c80000c1145580030b804c0701e4680d03130002c0c0001d613600c1c902506031044016031050f5200a2800200e0141d030a02c0c510145140d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 795844703 1250 795843453 795843479
    0x70503030a0b030f0d03050108150103050d080702120a080f01050103020f040e04050c03120d11030c07080a0e12070e0919081c2d0605060901031a0303040e040c0f 71
    0x60720204001c206089480002400e001c503101021295208030305000b02c0a0f94140c000c0d60407a000c0c00e0071380303000d010b80c80080042d4000034003001c0c0060344036250701403072540303d038200580c00345291054603403450011000786416800007600400180c4a8414007002ca001e00e182140101000d0904614001107001102c00e42e00840c4241080c2152040004040c803005001101e00c141008040ea44003104400e500c010a80080c00743c80c46192a0882000800282004072805a03100c14000750500d038141d43d40c45641e600c0000d2036020880710140031015511240c1052030030180c0034010f80302e95418103103c84103400c4004c0450040340e10260340d4030f80045000e41c3e510350141d000b159407035685180070340c2940c04c0c00d401d20701041c0447c40c01031200d08611040034130740c6030349002e02403103030b0100d24a0507200107507001c50003910350103401002224172640c0079078000c20101d06e240c119204600311b0140080d0444c0c000d503221000d05c0c400302c0d04110801c01d040c8031845c00ba1140c0d01d0030b0540780342000c070112410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 795845953 1250 795844703 795844711
    0x3030e0301290607060e15070302040b040b090d050706081b03060901060f020a170310050906090c0310050a03050307052506030c030b19080606010912080d180f02011407050303 77
    0x304210303803060400c580f20001251400e640041003401083c00100b05e490343c1d4090954880450300c0c1050204190600c64000c40701142e9a200c410740c1000d09100d15040a41d00030b50115500841c81c000d024001101813044000405450700c8001491403e00c1e004150f01400c00c031410015030381042008807c3c0d847c840640d040d141c00e072a00340740c205c1480c2001d0380380025500340034048076006040c0381520b40c0c50800451003120410b0600c0c0b00540d8039000c3c84010807050382c83c0c2e944aa8540c0000c1c90304034030000919400b411152650304490b07582c0002c16440c0303155410984640e04006803400600000304440220320040c00101105054403003500030301c80d0f40031702491040580b203466682e581d5200380c211201401c002090840d8061003614445409603c610400400340071b500c0010303040d90700170312080c81210105140c01c0000070700d59440074256070140703003c0b500e115640d4032800a03500c110b03050244010701c5003180224206540c000907010003841c840010b041c1c1c4c810028007001420110a40e600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 795847203 1250 795845953 795846011
    0x6030b180c0c030c16050a031101030b15131706040323071a0a050a050c04061419080a14060609190302100309261c02070c090603030e0301 61
    0x9161a80d4062003441d106804003600c542c4000f01e80e5541144c800300d00058200307610740011510503030380c0c0c0c1400104040c51001074541d50b07460228443e55402504a201ca00d035004252180164070101c103541c654000b40340c0039400d40030f0f0503c2441102021101a0752084101005107031911703090790014101c0303034040190841d08a0040c1c0c040b03403030308465041d206200e900545100307098021003001601803500319100080282070101003403c5107001d00c82c0034000d20301000618506402c0c86030030380d40403994070380103000c0e54020400e840500711130101040d2600c50729511480d10303041c0540c1180030f07255090a03040555042070248181e5584200458448204c161500c40810506030f07100381c040b101942c0041d41003810612016032196059205d481e245100712001600c0d080c00808582c0e1505034240815524801081100000380080424410200340c990b80035180c460789a4038400140031941c0203414150f03c80f40180101a009908018040b41c01c0d002000b5102d078420560302c28a80703840c0b110403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 795848453 1250 795847203 795847249
    0xc0c0a031e080d0906020a1d011b1401050f1905010e011205011b0201050a140408030103030c0c0b0c0705040e01020909010905090703140d02010c140d0f060815040c06030b 75
    0x802c001141007500d00c004541c5408004080f45418404040d5104505010014081c20700500d003004a0442c812603214040c1e6481d04070046410030400d0280d2580780c00d4070090812400d21401c50424004d02d44601341181c8005d042e4107207510141c0410740803a02e10b1901e06e04020040c41091006940e1604540a50100052000755401d0050042400081004002090041014a1580541109005001510041010b01900b0010300303540d48060720b00905000b010401000031034400c050350f03203d46000d00701c0c1e210025920081b4203804e0340048036540060308081410000e606d49807051408052480c0300130f500d8038404800050703103500b0502588840b00c1e926004078001400030011a400341d40d04c50840e0300c000861281042d640e0303040a104400541c00c2404200005110b00340807040034200c190103d060546401240c0c01410503014107035605d540d998000910301008120007002000240c0c0300040b64201360518a030810400e8001d8418541801c00240c02030310f8042ca0170180d03000d40b86c5014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 795849703 1250 795848453 795848513
    0x703032a05060a0507081305060604050612060906010812040e0414010e01021206040608010608060c03060f10170f010605090405130b09070f12021f0c0203010606050c0c0a03 76
    0x1512698045015100b40324400030840000841d91105009005079101c00c4450b5a0303803512964480c00030b1400a2039030f0054004681d03642881d0300441d80004004041110250442d201c062030700704200c0d001d6501d5480f03a40108403504052020186482d900404c032498241080b1186800e0f600c0074100802280401c401c01410160030341c00144451442c034029540d9600102c450034144000b5110180320382d251000008803001e0510440040f2101c000180500380e42e81e5403c080590802025143c04c0702c005821141507944201c19070521250603101c46904145248205e080010300529610880e50540018005203411030151200c41000b250042259650721131424030102c084500203100c49559410302040c40004100303001650b1205000c951225540d1040701c0a013140c13070304042c1d00508043ca60b650412030011a500d8858951b0030078619144850b40403c1c21150107a11000c00520041400659210180705c031710076504003140d040b081c003411506d900c14110781c006107141e100c100c030700040c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 795850953 1250 795849703 795849767
    0x2060f0a0b09071125031a090a030804150507050318060405190303021306030b090a38180709171005060102070f0e06010e040e0a140325021002070303 66
    0x1910f07040e0013290a21061002c154168840c0703e40e2400100c4035283c0207440400f801081f1203c80d4032410420008013006640c40e03c2c140e6680e02c000e80181d07030201c1c000c07076800102081c90280358058203007076480031340d0380c64455042c2c5083c40012040044541000c403c4c040414000504150500c0d007140005800c4822440c0c294000e00c10701d07991186c0f0100300d4030006102501540b10000180040d28074404a83e600c141e030740d003101d0b40c40700300c406040d030011907800410b071002c0100c241e0b1008c51180c0030b40040000d0002901c05001c040c41c0e55032141e0000400242c0c0760302c0100c800062040780500e111520002030619107400000765144015a81c60000030240d83c400c0110744000c2a41100c2469003903107a1440c010070f80c200301c41e1540401c0c40b042d9130120034140303449200703c0c0a0540000c0c046015541e9640c21890440c0c030510034580c130051001c007920131a40f20500b0282c07a100c4003e08002040391050001008040c3ca080040d074100d8070381000425004802512103030351200780b2080c1c4034207401903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 795852203 1250 795850953 795850963
    0xc030d03150f080706110d0c03050906120406050a0605010507050c0402070303140a020309060c0c0309010c06020f1204020306010501030e100c1e0e0a15090308031005060a02060f0a0b090711 83
    0x1d11403210442000140341e01d4081030403001e881d00e035610030301a5a569074482d95070741c04047c0180c0000384800c40384408288590b01502a242e0000e080910302498402c252a1f0207000307550940e039603590751050010000c0107100c2c4100511080c20894209100d980b20692100340000c0a14051900050f5100c10103119600c0300c114841c40d400c400899050889052000350411180326040b80318820100307603080207020580703058a490300000e40c135002200380111840106590b0884030355800340401d10004001c90007038150380110440d010390b0351419004040c9000d106900c03d43c181441c001b80008409400f0600540049880002050301d45c150074040301e0894144008414014151000480d901d0784150024800d0030b0450b0302d064841e445a0303401c81058082e0240c00c001c14010141000040c0403000610340c03000240c1800228682c1e28008202d0b29801260703040c0050304034030100200150b620601540000581404100d82044c000c041201098080c00540500c030385511069006001080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 795853453 1250 795852203 795852209
    0x106022a0d08130f170105060117070f02070801060909031e0903121407080723031b12070506060a06090b03010b070f0212011a0301090507090513051f0b030c030d0315 73
    0x1484030f00b0700e551401840240c0046117180c139403c4d402c0001043c1c1542c402d07101e2812445600041141649642c90240d50840c0600304240544c0034182c0c0014108d1802c1c80340030010161100042a07484040c50000c180128292104113040b0b0888414490341d54000562070a076a403000303201500181400c3c054401150007100381d100300300d0001e00c08040100520141056030710410140c80040401041805002c0c1141001822640148440c1c03642c00441c8030074007420000602558110150f48150300140e0344001c0080c5d0b8142e01020130b100d81420007a40c00d0300180507a103840141d590502141c081c05100600c170b021401c01e0089001400c0c015600f840b080c0d40e80d4001c00c800480010000320074080c144000901000a5002c040b004003420103001c0c0707080f26503200024210369801c044c030030801840040c1c444660f030a0090030200002d64104900041c1180740b110004400c0c5c2c94034001000da800b0140f00c039009030081400d80ca02a1000112110101542e04001c10f00a4450070001d82c5506554 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 795854703 1250 795853453 795853469
    0x5030c07240c1a040c0905160c1e05070906080c0904080901050f0405040f0c0e180414190c0503010f0c170c16080702090a1b0819050106022a0d0813 65
    0x213200c100000789180804035070b1012828072555a42040716441d50f0200c280720004a13481400113400604030b440b41c09a03182d0582030003c5800b403542c80e80b92400d074850b0024500295240010b000b01c21080110b810940822508600c1320315085d65001400c3c0903138402c071418050040790300304e1846610000d9034003822014008120300181041c05501514140404102182c00044091802d08241c4d000040c0e000c4802d1a0302c8598845a480344240e0f149901c00782103500480000d1304000c41030256944281c0d0090b4540d0035120b01741400c05003182c401c4000031600034905800e080c03c8a401035841c0384050341d50b2803481626a1000741603c1c07288501a0031100054651101404006144000d006003a0099400804555405040c0402c660000d42c5c071001032a90801c900b4511842909400d60015070310100c4c0c0c622246004d444c2c01601c1003a0080300240e0889407070350710b440311340d4000a1050515106c544210402000200b0a01d0146c52005409040001642d41811710383d03e0240008107da1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 795855953 1250 795854703 795854753
    0x1502072103090312020915160503070b0106020f03090108040605060406180609060f08030412152d060b040603090f0203030c010b01180b18040905060405030c07240c 72
    0x8658010010055007000700c0214401031308038400341403103109459034182c01515003101030000e2041040680c104900ca103070721413200441800090340610240c201148280e013075003040d50501102908003401c4d03c48075200c5900034013803044c45a9001c40941d40045d000b240c001155190304021501400594010326403513089034039980310140d0f10b5401101202c07502d80003085541d071030301032110300c101c4a803040384450344c0f0502041c401c4681d40d200207500b03e80320381c407580e80b425040044a4151513100c0114440002404580260900300302c4940c03102060424040001908000d1501081c2c0140e000d0001055902c01c40c140410031075030364940d80c89400a04072030319084030540c01406400d0146849000441503e2401c031965039445501040d0742445c14804d050800010310501610b9901031401d502c86e03258081040442d00921400e8003446c040e0021f513a8030002c4811003407500b03c2c02d034004a440748502c942c4800016030355040407070300341052400c05401501d40c10800e0503030100c1d42c07501c0442d0b228 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 795857203 1250 795855953 795856013
    0x20712570209010f090e0601080a0209060307030f060204090c0302090102060411180103081305010f12050a09140f370206040b03011403070b03041a0402030f1b040b030109150207 78
    0x444e02410116285801c0901c084130340410502e840320f1081c86a02c109500c802200c100624000a48940c80607001d0100d9540750350701c0d107501c840013000c81c0c030554285a00003814480d05029014035160300c0d000f800c095240912890000391750310001000a00403024000704103c89036070ba00c1011200c0b1807a5029901956105d007040c43c3c10f030b4800f0815002201103003a00007115401400100000e03840c50f00c030b12a1155842d00303881c0c06024000e1001170b131550340d100f2000000381c801880c0204000c16100800281c400c03100c8180c60520394480e039404c400c03030b40c412009080985203124011004065042842c0c000a8030100d01c150086800801d010b04021001040403440e410341041d80c40c0c0c0807800c0341c81e00c95071500d0b07468040c48140c4019146201014075282d0f6244403d03501c075040791002d4200c2d00c10941285100f400d2003001d104648042c0070034080c600251a060154480f00841200200001aa199140d1b0303003921a101c0810301143c1c000c290074044c0702c0e041000e00500900d00c0c24807043c0c404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 795858453 1250 795857203 795857219
    0x90e0c361908010c080115030c02011d10050f090d0e030118140d08010f17070801050108100b06090a27140f0a05240402071257020901 59
    0x680c1c042c0069541c6032200702d900d40d5201d0360781c2c54100c9841e1001c82c034002d9149001200984030789005d140035592101030003d41840400a0b42c2a24403050303024190250200c401802521005400802e50703030340c0e4005200ca0030002050760050700d009801e10001c4c0940c00c2000ca805801c50643c180446041e4411403428066000c454007000d501c1682903504119034001c0682c1c4d414000c0c0034081500c262002c0900594440d0092413004042c440c003150801507403140e005094400036000086150465524080000e55a0244070040042201c0e51802c003015600881c007442401c0c840d030050071f940d01c00b456640e104010000b80c104042104184843d00606000311059041540e1217044203441c81e000868000c51885a9030144203c211060703c064a20070360f90f010030900b160501d40c4503074204011400a185486660b00310740f00d540720308400040010914801c0040044000c1d00c9070800141030203501449528404050540c040209451441d00c40522070750b0344201001b0b4004a0000020074044 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 795859703 1250 795858453 795858499
    0xa0c0309031a040b0c07050a11010e09190f0e0d03020a090e0c0a08090307170a090b030a0617030f040b071505190506120703060e010e0d090e0c36 64
    0x503004111380c1c40540c45010316078005115181010345243c20039107180001681c0840c0b09681000149042c85c0d0a04d00480018100441a120310081820441820019111900400d034960341c401d5010407070010413410003a1540318176207911003016400035084120500030f109420140c082c98281d560545412801e0f600c8503030003081058042001d010004640e41800400c0710344032603101681200c401c40c24070070307400b6540008019500b40107031010081401d191074000b4503c00c40e182e15001c26520b00e400000001c09840907003042054008203c00001c00c103019084404440b2091400341d541c0c03c2a0400030288425450b01d055510b0502050148899100c00b081402c4806400100110b8652504200d01c3c82c581380c00040003900300e4031040010903078a5005a201052180c008210000c6030a14a400c0280c2c5220000200300c1e641014052028035400b0079070b101e5a102e020314a0002400d04117801030b100303038500c52041c8032040340b24090800407080c09194554040d0a80d442d00070542401e0481d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 795860953 1250 795859703 795859711
    0x6030a051b09060d050316140d08011e0602071e09020403030237140a0f0b040c0806071409030703060216020316051c032303010e09060c0a0c0309031a 66
    0x80c0d4100300491200e00d40321043e801a04d070300c00c00440c41e01f0003842d010042d83c621410b05031411240d88100c081150410720000d15010710550ba4400190b042841d040c41810320003601403d030f034040640612101d0740002c2e00f24156007020b405542c00750091424000340c0a000d8016400203070011500100301034001481d0311080380d001d070750007080034030000e07a5840000940000c00030303181881500340301003020f140029000e1440c0c103003610b42144040d2103003042808014001c4400403d200100410300c000c0c95000000340130741001425071030410600c002d01031601072038496200c220010b20400e59943c20420000216032022003076484950a14503240c2c5d5003503205050307000780107444800201c050000d0025040d03e8000701001e0502280c800c0c195140c03c600390003201031062030a4042c0c1031440c030030000030040d01c1142c0019620b41c106185801c95410150140e1a03550001d024026038102010548501c80c4207417030a09580801414225050902e82c1c0c4003400820b00880c3d1762a5505000600d0381c81 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 795862203 1250 795860953 795860959
    0x907080424020924030a0209010905190302030609061608060d0c090b030c010c12050318060a1b08090705040c020309040219170f0a0506151603030e070b1206030a051b 73
    0x103203c5411031300c00c82001100480840c66001c0000031004030b802d074003800c00440107160500c1003070344075400300e113003402c0ca04651101c014012404004600d010000151b1100002000e030045007014002c0902036010504d2201c140402000000c800381c6603076803c6e182182c1c01440c4d001401d0340e191107010040c040202014064080d860b65041c0315401071032150001a40b00a81d0716a000841c1070480742500f01500c601c0c03000d60f802080c50000ca80c2003103d81c0c01a0786501c40041c0c0b145c5d095040030703030891604102c1d50030b003c550010481c41c0240810100100c40e0265804101031080d0300d0100e0a503c900142d0030382c082c3c400b049420502e110b100400c24041d030030340c844c50214400140d0804400e503080b40c80c103a98004d25000203600c019a0f420590308050301030300003110110801c154440c9034003c001c8100000c100312707000d003051643c1406481104082c96015000d140e00345640c43c8076078490303d08150030349502480800c216071401c200040c0d085400c141640c41048240c084111117140076048244 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 795863309 1106 795862203 795862219
    0xf05090403090f0602010f05010f050d060506040605030f1c081605070c09110705070b1602010309110a0b190306050a1e030b0a0e071409070804240209 66
    0x1303400203400114103564400101401c07aa4168001c0f140344005c00d5040001b41c441056005545400500204040e41c032440810003401d841d500040d01485140c150420b04400401c0b1a24110400c441c0700c03404a03010182260610740545560258505603e44c2c0c0710340c1d0307000b6802448104e1180f14200407560f0745d003a10b00102c1c1e25402c00b182103030100080d0682000000d10180002c0c05111400c4c80c05c12101200ca11030203010070700700078107144d46c0d001c0160500080208026103030b0001031601380c10350707144c50342a0600d0f0454001d850513207a8503680c1c0b040c1507000b4042e0a09072400a86001c0402e0310701402d00c2000b4055200c041541c60001c20044045000c19015134401e03120040c021034000820840d075403514200e90302c00c02e0b5004c48801c40d141c055031440d00340c54200d291441c041c01103480f01d062032190000e098030040c030890400410100d001c0e50940281107020400c8034100c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 795683453 795863309 := by
  have h0 := BRFrame.cov_init 795683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 795683453 ≤ n) (h2 : n < 795863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
