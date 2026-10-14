-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2652
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:20:32.102827+00:00
-- url     : https://prove2.me/submissions/00b85e6c-4d5b-4e16-8e1d-c20bba1e1994

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 476798561 ≤ n < 476978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 476799811 1250 476798561 476798593
    0x80906160807020108180d0f17010f0f0e071d0a030210030c02060a02040803251407050112020910030905070f08010b24040b030a020717030603060604061202060705 72
    0x140c90111048a00020319108550b4000b0142e500440c07040000d81d01a601900d40b40d46035507564407014100305501410301c00192240c0c290f0000e4400e00001c509141d40c4a4030004180c000600524421450000000800900155030700340306111075503818440f141000562416008010420b540c803525041000c00540c2d9100c002c030811142230f88000410784010750740a030502c4d500514040100748140300410034090084100d0f40b5180030348000712001740d200d020000f101180d4600184c03404070003c010390200e0780000740000030744000340c84070044070403210b0148060303100d904442500802403211082e4240e0213504400e0040748160143c440607a104c51406500740d055511031034250b03454031000340641c208641025111401852052904c58102c11100c2c0c1511443c0306100100c040080020b800380c1459058500c0961b001e54002030140c41022080000d8100765280c40c864011000410043d00d800c1c450201181d8100321003c060048503020403602e42c1241e03500750307064004c945c032038820400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 476801061 1250 476799811 476799847
    0x1e010b0d0b191815060507081c020f0403030e040c0512040501090203011104030314090a180f0c0c020f04050907090b030a0c0e010e090d021216050a120e0405060d080906 74
    0x5080f4a002403101800075451064545001c3c882881d200045403d000c5540e01108990000c1d80081d44281c2e50041402c407003240300d54809140100c02d00c0461100300c0500d9200c02401103078003d40c4c40b9a01c40810900b00700840d01102100b00100d9010403011400c0598001c0e0150b000d070165000044d00c401a0b00800d0035a11000240c0b0075503403001900303008258000c60310382c1e080c1040700c48050074505080040f418450840c0207409000701543c03805548002d641c0c210800c043d8084400340060500600013501041a40c5412889000c2040d18548a41044c2c4155840b03001010000d054641c9070107412401450b0b01502d40e50036000d09841200458030041c1e5080060140d056011413542c034000b42160391450140015049070099130414049c00e500060036944800412682036607012040c3d0607a44c00581800014003034002c0c0b81d001d10902140400c040e03104202601c0341d03d050040e080c1008115a400c03641c0c16886060490500c01103034a0760090100c031003014203010f01d407503e0300c188481800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 476802311 1250 476801061 476801069
    0x10801260607181d06010305100b04062c0d020108090307023a031715040c02060a0509151b04050909030304020315010630020c061e010b0d0b19 63
    0x250000281c26200c650f80c0a014010f1101c2d80002d046038131644040d095007003025000904240c0c4440100705448114030602e002801d107051456615991090003410307905442d82003c482998000e003c2403103004e0303c1d804c043c505d07030000c19895003a2290ba0043d5030014000e80142080d200c280400c03001611000e140c0030078144c06802520920041481407040c08500484440e001d855404501000903004100c20f0381030704111049040350b56030f5501241800d10308025103640641425040907400b60089982401056440428403850b620340c2d00d9196207610129543d0000c0040d4000918181400d140a42d041d5941205861400f55a44c0000700c1c9010292110740058200009120445c90100030386440320a00403c901100e40c5011030107080004401c3c01c0c80000710200740c072200c80408002c50545840100390085464004089000d940c1c1c8108a41c03403081055145074242107005050340590490380c20188072803070f022044101d0000351031003d1582e80c0105070180c0e03c41c90a18442c01d204050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 476803561 1250 476802311 476802317
    0x150c0a1409041118030d14030a0209090a020309070806060102070303081329060a03020609010e120d0c02030c031b1c0609030512150102070603240602070e07020c010801260607 77
    0x41d0100c1601c0d0003200e40d02c0130045209070f100300920b5100f42d0300b2001129503414803040039520f80d40e5800580c4041c0c401c4440d440d0b4400002d2040225a9806501441c00307040e018044448181c1c5070f900ba240c0d6100d05544442c0503a00480003000000d101e01c1c0c2d1142e200c1a2100c40c440c01408903900d0b100801403003081301011162140041480c944880c0005a02a000722035415401e4a50b8020030400c0c4201e0f0701c82070420980000c8405980c45208a41456031003da003125242012070f60700400000b2403a030100d10038051508041c840b071500043d034101020401a8948199403882d00b00503100031078804100f9140700b0391001101084081c421182d550f400b03603e03066900d4281443e001003401d0014012000450800d00005041e40e00081600036102941000206011000c5040c0c20800c00551680790920b117241020602d50360116002085440a4a5071081d17910340d10020303610351030b1500070580040e00000041101d151509000c0c006205c2c0e1309100e020f10300500545900300354080790280d000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 476804811 1250 476803561 476803567
    0xe01270509090f16050d0b04030c0b0405100f022713050f0a05060103020a0207030213020d091406070c1a040f060516180b04120c0810050405150c0a14090411 69
    0x2841009211913180300c3c0b100c0c140300740603909001c000740d20034030300da1009803142041400080806009103098007802d9000301d94010750785014503020350744500c10145036000343c0c00d1401c0d10580b0101c500994000028100010103580c04d10070300e130009410300f51115a070011445003003050144091240d180202d090380d006244a00d40b0a00c0181596400707045581018030402c206102190b011480c04142ca030304440754040480d40d520880060300400f18654600740c5048150800c1006c0200c50082c02c11801c4103072040303a0760341e640503652804080b40c040c10314008102c004200d040e0301090340382c2c0316100d02d445e10b8030081c15455000446d6021540e110300c0c440d2602d404c00c4010781041c6604d034500b0b0300c1541c00d0440c03801c04840079807034082e6106a0700c80760240011142000703001148500074112003c00c49078031400454900018040c00c1e80d090707515002c0c40072090341c00c05200d1445840b80340c01e801c503145001504202100e5648008040070507031241800704010076511070250741544103209a017151 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 476806061 1250 476804811 476804833
    0x212090f01050606120f0604150801050402030714030d050304030c140a11121f09050d090f09020708071101020c03010e0a020114030906280606030f0c0e0127050909 72
    0x200b12a40500441d100d21070500079000d0010500d40110750007200782c02d4038481900da0001060192100445001d048050084080f44a81055200500c1036000700c0032594100e07510240d525846030255041c0d50542c0018503c2c0c00070500650040d0b4001d4841e1405000c0c41c00070f030301c480d80c03103800c0503c3d4110290003040f868410b0117296001501818400c4501411908290800513960141c104400c000c0c42101035000c03401c105264002504a604241511700311000c0f00740040c01c030720a40c010b44125406c0050045120b0415100751240c46a000740c10600e86401500d4250540c4a40c404e01c604602c940d60414441c0d8400303004880145421400800b481d682c2ca10001d4518120411b841960741414010403035403a0300000c1c0d1a030841401204080890049a0718880c040d100c0041009554185580021003079410740c40304c1d400c5103881c0c00400c00f68078055003c941c6c04440c035980e28001040144501c00d03a1000ca22a0b0314034502e0002e142107026900c80c00b045000004071030b64641c1c0d40080704655 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 476807311 1250 476806061 476806063
    0x405061602031c080703150b040b0406080c0408030d0203150d0302010e2401030305070f1a060f190308030603010b040603051e0610352a0904060504060212090f 70
    0x500d4001514610030040702c10210000d2950b44020041401c2507221582c00c7e0003480c03001c041301b02500880700119aa192074102c132020685c000e11400740003800034400140340c030202e203003038800703641120000e5440e10418586000c083c1d0005010288041400c8038554050ba580b503c140261034400c0e000801e0041e40740d8007403400c01001c0c505004440084a0300094070f103400701502030540c1e500d410056101d10f59070034417004100d00007000400000d814078500620a1443c444544644000c441640c6082c5482090160f05511100d520010010030001400001ca80c04042c542c440b20190000845a440350000343c1541d900d54801d845035004408100708050041d0000c01086101074000d0101d4202a400106011014032400005004106155200442c2260081041c0d06082020300044440100240d19003804804403240b410701ba520400f1340c0e89041c07002d8094044003c164000715515501c440c2d001d01402441224036650802c2681c42e030031040315216024080e004014101040c41410705 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 476808561 1250 476807311 476807323
    0x501030525050d05010e06091c090608060409063806030613020a09030b0717010602010b130b03100207030804052e0903020f0f011a0f0d0b0705040506160203 69
    0x5245400200c119075140c124003002070404030741090702c0c0510800c20504100e401881b25a80381411030140005020008900050740c412040c104174403110601c00d4604151040ca020703105500c0880c200c100014141d14150f4424482c542c0204d201003020300040c038100c40a022013518060b03500c80009070040c41c1d10394024103511341306e500351401855410a800000d018050742401441e0305a00000c4007802c1900ca246000e00442d80402c05070005e0801000150050511141143c0c0c5100c40d01c4c000a11140305018004000d42c02501c204490810103800300d000c0e000e88805c403501881815200c90305080948000d00308640259668251810305242450810342da281c83c244004a0244000300d840502c0c00342400c81e0080e150001030b580d100c910f4180e042150341d42e180c10890081407460324001c0419040b00001c150701054074038040310303480c08024400f145085a150001703404440725001541158051350400b0860a0070340c00d107541c070f40000e90154000d0f024610540c680e0003a01d01142020015 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 476809811 1250 476808561 476808583
    0x1401020414041109150f03040602030403030c020715050c160b0403050d090815060315010608150a0f0302090907090207050304060906080f0609060a0503010905011a01180902131805010305 82
    0x4180300111214100310704130300661809911403107141ca070704600600008102d0701c41c0310902d202c0c00d4803441d01d82841c000075042240c00b5000700381440a02d44040c4c0c40415a0010707100264408a501d11541500301c82640140c01c41009500c0303003201d1100ea100007425190001e0110a41156a0302c1c00d6143c41414030a19000341c0092080d141c1051103404004180705151200c401e2800d80e01e030343c48000103413410f001104507800318000da1001140199100f491544501c009500090042c01c0b1070003845a244c40300d1240d42030501c05100144018500204600d40040d184c40488240b03c2e200c00303168040340c2c0321900445090b0300002f002c20060341c1103d0100010200d50509540928003c400700b03000d102c000300000d1250800c24001141c42e90b940350101e000d0103015008002e116501c2c54524002c01c0400511247c104065401c401c0640c81028a00e404018404840314010b14110808003c1c0d001030f01492500942420041010a05035000c000050a44040420a54950704040b810a250064 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 476811061 1250 476809811 476809819
    0x90b030d09081207020d0b0901150506120c0a0207030c0608041208220501020c07030f020910061e0201142403070f121119060206060405101e031401020414 68
    0x100030603071003c590081c92801c10011203070755000d203100081d00142080001826021840d080c03040c0c05a0544c010f401507181c4c0d888030304e400e607110300401446020300d140e408141022240024012454400505140582c6004030380159071a40c4d00c43c41902c00e00d070002000541ca4600b00010b014000341d040041400e80c0c01e180002e800c1c456030a56200d03074041c40a100d075940e100726500c108a02541240d4a8401d0301e801c2d1190945c84e0b00e0a20000c1a003540146c1c402d440c1e190101c3e503601c42002c403217411070b040b9813a07a09446100d282c0161505a8440001c020765680345501e40c0e8410390700500c140704008101c0440144020700103c404001c40001c06103010b540030080c180060025012290151071b01e840c0583c0069005141a04440c250f403100b054002c03144651100c0201b0070b10301c07607109680c042c2e029a042c6075126001d003c1100c504880504403c0b00075442001031803e00002c2c003c0703c0c949a0009403007542c490701c4040d41d0b00461582c0c210541e60004081102c0c400c45284012415021a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 476812311 1250 476811061 476811077
    0x50a0603020108010e041b06090906080f0d0c050a0b0c0901021e0613110a030f0311030906160203010e060c04090c0203030610030b0d0609030503071403100311040b060301090b030d 79
    0x50002050030303905028017020600014082020b205140c00c450b41a22030503400c3c0080c0e9600d850000b400a031a900c14400aa410000045012030f00840c2c4070300a18440001480705c141f50a50855000000e640c040d644c601444984801148140b49068861801888015503a02c1004002442e10401e011001c580d041280021b845003000403603c107402c005a103c141010814500301555855440030701c55601c909440723000810040326424201c06240aa11070005440540040036240c1c40344e5030302c09a100c001002210000c010140040b80000d001400009440b004d1300101e40c5004001d45101c2003100d80443c0030801b400c00d5029a19200c0002c1c405035055051031400300c0d40a246485c00c0d0720078181c603001c94000e80d480380e010250603c4c0d080ba0f018024031110381000760240e401600c062001545120311424003c0181702228060044240e4511885285446514240c42200909030b8801d8503150b5049895a900000d10301903ea10b40000409260328800c25242c008450074000c2441802 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 476813561 1250 476812311 476812313
    0x41703120903030f06060310050a030c03020405090303070c0201030f14040b04050c0a060203070803060301090c0b0705190f060c020c04090605010914070203030a0c0207091d0d091a090a15080406050a0603 89
    0x2413000390400d10a131a140c0c1c82c2d4072181c114800286d0640c0180b41c006110010000620407c2414a01200d000755810040750329101c0c0701d161a840101c0d56800460800c101c2c1d100194400c0d4480354104081d40000a001e03c0452400241c084095405603019040b403000d0009002e01445100c800403070807210711262605d028800707503c0e4001c82e0800351000101100040040e2029000200302c1e03640401c12280040e1150544c0545410450b02030b81c1510a00c1181c074110300140c0080308051745c000b41620030203e030136990700014044107000e0104502540720706540c82e0301d907801090001c40c0b113107001003481e604003401c000071100d01e5401c1001d0144050309002d407568010007142e0304200d55420204050044020580c074201c0c0303d51100000c2817030300300c00b01d02040820141000d1100798409681158400d55030481e180c40c1c1c140a41101c0e03c2c40341c241413042840e96401040070300c10141c44031001e00e03a52104001c064503140c1d10000441c2c80c1d9010002001041c1c03203131950006805e94104082411 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 476814811 1250 476813561 476813581
    0x180e0a2a120b1005070c030501020403050a03020f011404060f11041d06040507080412140d0f150f0b18060a0c030216080a02090601020f0f07080c0301060e060f010504170312090303 79
    0x100e42071160138040005154010300100c001c00c500a150410029943c981d52407a0007540d48840d0381c001e50050140818420002c10103014003a0104600c070500c03500e5885a407699002882200c0e10707409001d58032714011070795000e40005080184001c01c13080004210030a44181c0700c0341c005007040d00c01c03440c282c05c00c440e03517810030745050308250844091342030510161010b5035000c490004010444030082441d00d902040e039007007001002e0800d6001e00046541c8402211100c80b140076040b101c5c03c0e185410310003000000d001e451144070001d40c01c0a01c60040011407ea60320400c8420f00141143c03c0d01014035404108288000b83c8040c1100007203840c00c00c440e43c4502c64210000d00c1202e20b40c006c160103a208000100c0012020000c0c1c45400d00d107041d0b00c0395114041d00c2007500a015a2a50b280b903440c3c10b220303010458004140d10046651399600300907641405c0484c07241403060a000215001e200c0390b0040d40d507002c58170021a540c10940d103a10343c0b41d400090900980d035104000300304800f00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 476816061 1250 476814811 476814829
    0x1103160e0d080c190615080303071205130f0807110a03030906142a0106050f28031401050109050a0615120609021c0c180e0a2a120b 58
    0x2400c0a09103856514080e0f60608180603c0b42508425120a43c50030a01485510164a9801c101c4441c0340450b41d9030364054407404200ca044002c101d072200e038440c416016410443c0d01441102880d10900d003555680d09260b61070700001d541026011900000b004002102202c00020131149610940c1ca035650050448869014540400001002c000d040c0e1050609840e512440c401544400041006070f00a401c901c8005441d00c56003030040000741130500b6a00040c43c1c103001341031002c12200c220b64078040841065140c5107441c240000010200f05c2020001750740006550020401e23500d00b19042080c2c9501800d02079403503181c16400c000044611612648062643c1030198200b00c0660702040200026413140040c1400010382844402541150440c882c1407079004001c5002204801c0303555600c03400c15111700d20f4000105000b005640902c03e0380c001c003c504080b0724001000d001c220025021310040040208040c1c034004c1041d0006003d100c0041e4240c01082180036180000744009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 476817311 1250 476816061 476816063
    0xa0f06020c01020405040e0c040f05010b04050d151b08091203010e09010609022d09061209010e0109030c1e030e21030403030503010e130b04080f0d1103160e0d 70
    0x103034009140c100440e0290190740080c0001081081022208410790707860b081408101b07413085142040c101c005c040b0504c20703241616680703030519040c0760901c0103205402010701001c0e5910b20788402510780300320484c01011400303c1d810341040d0b01d5440403000640300c1240038028113140d400c071508005a00d20b0b0201960704559840019070304548855116500500d0030b40c014158117800042d0385d10411580001d0b00601c6500703031160031145605110201d40c540075104910350b220008024034031850420180d0290001c480000028010040140031821100c1e202c0045001c20101d600031010322480c410007a00524501c10b070031503500400e560013003420300310000d001c1c400d00055685a1115001c240d081e41d03a40440401c8964594407820003404c250401d2144003e008040e200085d030140d5140b94400903075620a000180a8035540e6422440350040c8124031044802880030504046107405181c607034004000240d607032805e00c007202c4107043d55250060411b0001c80481e05078507841e41c1136104406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 476818561 1250 476817311 476817323
    0x7050a0507060b040e120a0207060e0303040306091e11010e0609010206010e070c0b010f08010606050c030a0509120619050603190b04020102071503060510080108150402130c030f0e0a0f 81
    0xc0c3c010000070014035003103803200c0c070f035104400e24500d14298500003029048800c0d0200e620340d40d50f441007101d04411354140d1383d815400c00c1c04100002800c540091a2032842902034544150406011800301010305e2000c0da01c004404c1c032588119604000e07841c0301004143c541c10325004903d00080d550702d006100ea00c14540703682c00010b0700c06100f81d19504005074842046006035a68008101c6040b009018004c459464400300040c201e005a049440404040c00618103080300c00b0360070741c1c031500085042504002c80e114110f051050a1240c42d00c41c1c0c01090002e542c4202c4562070204542d0b0050080c1e000f41d000d070b0b49992007040b4031200c440c002076014003580c81640e550f02c0100c1c2030141c02c0d405101e518680102c1088070a8040d00a8416141d01307071a140c0d421000c9010440d1001ea080c4640b07280d540204452450103a8010707816544a4000350501541c0000c0a55400407198400c018100090355032070700056200042c0241c944500f0360b64020081840c854454081c1851200001880c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 476819811 1250 476818561 476818571
    0x20030a110406090513111c0b0105120d1e02120403080d0c080903070f0809060a0918020703140a09050a0b0721020303060607060b04051e0f011a0901020703120c050607050a050706 78
    0x30f503074a9401c08010503140c0c7c9468a0140c400745400102c400d0b080c05020702c103d91102c41503c2e42c0c10000749140340d8001a580790443c640743c2da070300c3d00761000301c9000e04c40450084400d1900c0301150329005100031032080070701668038070070780d02040111190003c1445c2040103401c180840c1c01c0000090f500130580144403140700480740c0c40c000155100311181c403501b00341c0114131080025000f0011400f00c400707800e0f0090002d505003507030000f00e105003800180400e5620060303103000342d08480074000740c0c40141098541d4540710b0000580003001a44107860520b00041c8520820010840c20b000b00303c038a03004503144541c2c03041c001c0d442e8000104414014100412081e043c400c05030499007020b800a0003c00442c10030190000c02039134100112246000180d011070311000c41d6070442c0d4103c85a200c03a00c0c0e824200341141e0451544040262070441c81001c43c04400b09070342814030720100149840305601c0000c54900f80d420a600104500103004092000c244655040001ca420b00e0f9448980019 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 476821061 1250 476819811 476819843
    0x17070f030b213018060d0609020904111309022107050a1b03020a030e04061706100602071a090a081b1e0d20030a110406090513 56
    0x2d00c0781036400c0c5502240c41c0840c8000c01c0208502c000007a21051655418050108a0782110b18081c403c00300e410341001490040c1d08414000070b130040008041d41c0c500f5a091303000000b601c00c0d50b0011130001e81c0c001186c500038a058844c04020551480205080c42084204180d002100e4460302649035000200904a07501041c01051048185400314887d41422000200a134204081060110b0326201641d411500250828031080b80d242d030050a0280d01c0d03aa085411440714420150040d440741d4011641031485aa481a2060098000d200c1480d1040c621a848801c60780440159000120140400c0800042100003041c80064043e5a4501c1001107007091145600c01c4165000340d803500d00040b0394484820094030011583d203103549641000340700807584640503513076020a100030300034001001c01010603c0c1a1a5100c41101801900c001c40c1c2010f08000c0200e404c510848519000c9180520a03000504080b05082241d4075110340c0e08241c0003410040a4400301c0c0c001c002034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 476822311 1250 476821061 476821069
    0x6020a35040902180f09180f03070f02030c180106030504081b1b0901210f020a18050106080c1803070302190905060906030c120c06041517070f030b 65
    0x100100000d541165a1941e8a25000081d0062519502c3d03005400c0c0242595143c09281e000c0150350040c1100c00607112104c0d900d21283c1c24164a40d181c2c020300044d50241c48041c40980b40c2c0728064801c0b242200c081d841050704000d011040184a08582d80540d9482c00b0441c02c0039066461500b40090b280e120b0341000070700740c051140e401c0c05220307010314240d03032001c0081080c5000340c20301c40e0780c14500c1e118081000a480c00902448040b80012550318a90140260705850298001d4002d00019034080c0c0104a980c4d00680005105d804072a55035040c80307046100d0103004107064544082a4142180d2640c401c2c41080c00c0c030310781c49290031031090941c0e40910a80e001140c0c010240712140c020844100090a01d510031410300ba032070040001c1283c00c048111901ca900022f01516070100904c0401404141d2204400c0b11032080a070b2030034051329418000c0c40a400507448646840c0910080206810b0102095003290070f05407040c442c1068005c0d0b500e04d00d694403418045044003030398000ca = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 476823561 1250 476822311 476822393
    0x2030318070b28030b0f0103090221150a0203040b010501050a021e0d1805150310090509010203180c0f01031d030301030818150d0b04090b100f06020a 66
    0x2e00e810800003032a041c80c038241422809035004849200c101e01014440c2c1030f800c071064084141c1d00321180c3d00e5402c0107503100782c0c403c01030f00344001c22112081ca0303c18000e41c0c0c5c260341c0107a05212580180c400c0c20f5080090011260701c40002c40c019855403616a07a5011a6403041c1300c2c1d10305001c400701d6520b00a41c024400f107000701854101c1c507900d00c09003241d05603846146041400200700341c0000070344030700075641c11481610000f60045045901009084019070310050403c1c42e203204159000c998a1428050b0a0151943c1e400260716428000122050369044807040c0b891603001110710030954407851030b140d02165003424000b0780004a4158050320740f0f00381006009502000001104005402c00540185108160b04c24070041c0e410003404201581020f01c1c2c80e5452051150650304403440c1c10240032080060000b01d030105803666203158040080e617080703a455190742014421081864040350023402035100921018000d915007841000541251034a0707200346000441141c2c00c95051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 476824811 1250 476823561 476823569
    0xb03191a040c02010615021b06030402150307020102030411090f150625060606050c06180c221104060e040203060d1703040b0c040609060302090127051309030203031807 74
    0x105000c00111002d00034001c0c00180541d0124401a500007400d503403000407003800a0906003014144403040401704415504010300490b44040000300003106050307404007840c05400039400142c1c407824a40f8100c022500342544841c01a82d40108000d0903000d040180e41e00084070802c5012000050b0000c6240340c0310f4038108e40c081040d4501e0750141920480300e01d4040718083c030810071109840350b004441d24031880141c0f100c55801040812904036825038005a030781324003412a4807840b42080401d10b082e50011801c0e840c03003602c020301c01480500780a0300035801c250081c00d80c941070400b4009080e40980004240c041e590100005526840d0751115054403a00021826522010b01205001c0380d031003190203d03038400460010910071207250054409558850326110340c140d041070000c0380290000118903040020841c5207100c40b4004040e0b050303100d21480080707201c1504040c05d00006a00b2025079a029510781740203403011a901005484d00543c0c1001004040c4901c00c510516040391504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 476826061 1250 476824811 476824819
    0xf031d030609252601091a040326070e060904020304080304031b080306060705030d060603150509130803091f1d160303030b01020f0a1202070b03191a 66
    0x3003440103080c0d0000b40241c0d0f0070b4030051a07100790036030100000011140c91003100f20b10703800703001c040c1004808141180b18003107200c000040c800c00d25407a801c0030100005000c0090308150020302c002e05a02041e080440d50f0410340c90096289612030701d88010400030210400c0200050300d00200340d88080480c3c058600007070043d0348070700700f5003004081c5a2060340c04401241c0c20280314800d0b2003000b10b1940c0f070150070152150840d91000c003800380d5940003840441e1140010050000e501c1003503c1000301515680d170300041c00800313a10f0200040790540d00031502c10864402004001b01d2040c0403840000c2e07110026940780e480341201c2d42d291280320300c0c01075811170751514040e51010b901d80c082803072103518241660400984100c0c1503202c144400100794500b001c107009001013406500a440d4447c03040c030480c1c40106018030b27000e08240150b607049550180c22803030704800a60420882c80903080070300040d481d60030080e118041c080b680d903440a0089482d15011a07003d2104c241c002d05c00c0c04068 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 476827311 1250 476826061 476826073
    0x5040b090d0f03200c1501122001050c06090a0209011d0a09030e101e090518150604061107090203010506070f0f0209010305010906061a09092505030708090a0f031d03 73
    0x504d0380d80300c1c6c04c10303039141801c046481c000060070403c401860368117941062a40396498814080410200300c022640e80c140501003100682d0664100846885507484201801c4801c00070b00c10090248010f034010704a8190380080c00c602602902480c41e044004460000740c03180300c80c542a00c50102141c1e16607409040340ca03000c0d040c990040340e06000e50543d4a940d04201c02c604200741c5426a1034044c1a40100d42413001900c91159901483c4d000300701e02d240748180d0f900c1031001030030a50040d00001c1c00240c0000c0c0a00703445004010240c00390807803203420350540d814500450b00d18050b244003e089121060190003e0010910701c41078070940140c6603020329a12824454041c1660b403400300c81440c07a0010001d1074070100707105019110403680e075141c507000d000c0d402c1202c46d01e00609000d210025440e0414034401c040f4016031052203c41c0c940c00d480e440d0601011385036480051040940c0c0d040412614001079003404601030403503040c24946181125041c525a860840300050b40d0144255 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 476828561 1250 476827311 476827327
    0x21f05030106030c1d2815030b12061b0c07030c060809070f1a041203030518060c0403080a0c2f040e070504090203160905040b090d0f0320 61
    0x200065040c0c0b0b6040d1420300880d00c001408803890400c1039075106243d0b10102c00c8013201c0c50800b00800444000e4884042d45038051a4500305800c0f8550141943e04001d41400c031039203405006402c1610f400b2100b08040712002008070307803035031303130051032020385855009505505904910079200d0503005941101c030361907103030b2401a8054005005010200385024005490a003001510340d041d80c01c08640c890000e0b28050895802200c0410045500d00e020301010074110345080440740c51a0003641d012445090a15050408115026200910790048020411917130f1890b07086404413507002d08c0c2a643e071441d040341251091201c1c5802400300340e003206210101240c1c1c95240c031842003840302d5540c1b00c1418404000c01c58104107801d40280d044100d08000350310b0a41d020303410345030000c1c0c180c45090040b0304c49a501c60900e50071042c402c1d40e40700c0620050000001180f507020b803802c0c00074210184006800f40c0400315840b160070030980c842c41c08480c00c407403031070142c1c80501c20b20142036100c1640b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 476829811 1250 476828561 476828567
    0x120304032610240509060d0f0629030c130315050a05011e05090a060513091208060303070b07020c03030406120b010f1704020604030f1214090307050d021f 68
    0x30544580da18440040030201e00000f40810000341d03240c081e040d0000408a542c2d0980c1e4940150610703661204c0d00b4005001c40307130910300032a640c441c05403c1c0020035030b00346180b800c22a140e9001440a40000900a90f030303110088003280d4206007803004c0759403030f0700800500c4291000f2070b400090200d035043c9042201c0c6400d503003009000c1c0e00303030a03004d009583c0c171025a6451200b003c1d1000c00b0300019480200540c7c1001300005070489404000452040c0c0c8070004a00d80351800a508140da5582d958a00107020458444050407034441c0b03001045401c100000a41d80c1c010a81c015100810900c045032030903008008000d0b12942c00b40c01d0340d884a0b910300f0701400742c0c94a050b0300c00500341011054134056120790042107805030141c403080300d441d4445800b0031014100400c1243c20500401c80030010a850400c034084861141c400c180f413404c2c14002c01000c6a8140c1d881d01e42c06102486028402e42d408205042038413001c2d40d207445420b02c41e0001411142d40c030b51110b252201140f0403440b180e07038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 476831061 1250 476829811 476829887
    0x50724050609091b01180f031a060d0807060c0207081b0a0b09010507080309010b0402040b0d14040c421701140603070314070201270512030403 63
    0x4464411455403243d10301915005024400c101c4014020590f009641c02807056580103002d101c990342e00360751140003e001a1003540c205594240d420f20700c071148a080d11260382e40c0305006aa40d4071001c58940d40702800b501500c1070040c8403d803070f145601182e5108200c0000109001001c8600718880e4090000940c01c0b11540c0354001c00044401050003100c0f00704640003280d06a441074038003007494940c01c403a038001514440d00355403210f005080603600c1d40003500c0030b03190b56080c0c149c1d0b445d40080c0b46070840c0c81c1801e1452983c0c84000c108000320340008207000454403110341d9105450040c81c4001480c2411002c1d00a034078050a02600c55407103802001000e1840075181c0c0d000140360100c101100310760910030b51041e520320070000413050811318083c1da00141d4906001c90416130407420351881400071154000184e5413200d0104211060803040381080c40b00c2c4c10550380340c040c5615075a4490564900012464000001190070984142c0f111940c00100300c11041d06001143c0c00101510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 476832311 1250 476831061 476831071
    0x61908010807090b03100c1e0503072a020111070506040f0302010e0105161e02040f240501080103080f220e070f021b0619021c020102040501050a05072405 68
    0x48a10354000c50f802103944240684010300030010040550074000d80720190a84140e98002c0009201c3c04800c80c1d41340c010036090030041070f182c02d9101d244c6090020100341c400e0640c40c04481900203132100b1841d815061080154080c6410980c1091800f103140c07030072007542d01440d000000000c00040040c081c40403d015240300360385890405640d8030044034540903440c00e1102c0820344101c9030340001c2e80c051000030b550907010001703030028085800103030450350303080002a20303181c984598280740583c0301148404110046480e50709941002c00091030604140401848103200089800c003848001068442882460220510080c0741c51008010807016114110840706844045050b01c1e005030260486900c090340103110140868442c280c441440e00b141980084d001c20500b4540c1407001a5400b03540d2041e00240b01c0003c4801161942c44400110b402c00c69105020038481c90303900c0b200320783c10322140c1c1c03801c2901d0311401c0c10300c060089400a040407074000c015942050300e242940000380302d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 476833561 1250 476832311 476832313
    0xa020a060b01090e19092003010606020d050d0e01020c0102040f09050a02031620070f030b180606010c0507120f0218090706050703020c0d031e030b0a03110619080108 73
    0x200303210801500c2d907402e140180740003100c0c0600080c0649401720041284550b006801003050055901d4040143c0403000e9205004a00c5c0016a280d81c20240181002041d480c402070038680e40c050f178020700030300503d40703040c0040383c07078281c1c0d20b4482c0340c00d40503500305008080003150384580c1e800c01d0b200d018101d4130030417011604040001d80280c000d0b00c00c2c2c038072035030483c5400c2d6948801024121000040601011500d9000541e0144d6800c4108698400391170b140b08442d0016095080280d803070b02004000c011040407002d10b6020300140420400d82104083c00c140c0d031010311a19141d418a0b0f17450704031a10700740881580c4410300c4241c42e0207040050007520500300181550310309100c00282190307520250382c04003004100c072500c100010a905406481a02c0c01c03481c100000034a4210441c0d0180d0020b65141c40c0c80c1117812030020854040001ca040800c00c10083d2404140299030a2202400c0c2c4d0f5208200e40200d5100d1000b1224249820000b0500100c1e08600151404100307004000003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 476834811 1250 476833561 476833571
    0xd020604121b060203061c0b07110a02061e1216091e0e0a09050111030402040c0f0e060304060204030b0702010c02120c03070b06030a0b010b1206010c020108060409170a020a06 77
    0x41802400c401114002c4940e80000ba8069600e8200285d4406400385400120811300d031102800091449002c0a04c503a400400d181484000289903100ca181d0107a01c681150b030020f4016580c1f50201e4020601000c20442e10040e885a04039079401030000c541d0300711ba449810040c0440101d540300001040c1c1c0d480d05040c280d100c0c240c0348400000d03a5482d800c01e0000381c6040c04528006000f1a42c031029404003c00c002c2c1883e55510f007076a1342c1103000540b4010120a0104600d01401407892050844c0f400c14403012030310383d00400c0350250700d0704240a0580000031400784a107030780440d405190400c0f680511410140301c02402419070000760170042c00307240e40203201130700c42c802242e143d000300c003008606294441d2074502c0000c101400d51a4035108194001000a24a855442c02003c0f10003042ba01c078100100c40480814000749041d0401010905020060781c01c0801e06800c4001990001100300040c900202c501d8420340040c090108042680040d00e6800250040c88a10034441441 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 476836061 1250 476834811 476834843
    0xd15030f120314070f080a0608100e251a0904091b050618120c030d0f1403061e0d0b0c0904060f1203050d06031505040b0601090305030316110d020604 66
    0x1c040c403825600040005c00914551840500c503c0c0405d8004c2c0d0340720400603445645290140c0f0302055000c02c018119110b01e400b4503038100903c0f49451814000794804000e15440301d01440c11260b9000e240da00c2a82980103170307c614500010b0f034050752400b51013040101c0403421b04900d030015506050344c040620003804541d07410034500b541c0681c060250140704400c001001c1182021036415169124440c41c1d411400c259401c000c5c0c014480780319282c6c008103c0d43c103030303004040d515401a68844844100306212098a910480c030b1a000344d0b2085503001e05d48010001004039840ca407001c0c01d6101c455080c400003003003c400612008004850401002e0f0307460020120304207a62040c0307885071080032000400300b80108014042080071000004034030b601d0b540c60b0350040c030071200f80000456544c000c200800580b88206074016009003031105545165070745440da2440010450f2440c007408440c03c0030180e000340344200c0d40a210405540e110303600c607040255101401c40b826038222184d451845 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 476837311 1250 476836061 476836091
    0x2508091c0309050f0f06041716050105120a090b0405030d0e06041106160c08030405040f02030f0a2316090e0c0403022b0c03030f0905060d15030f1203 66
    0x46540359164980d05045441c00003042251811000c1c1d894214000c2c1d0701000303055a6040082c07014124030100403100c000020002c61400c841501c5c0c0c007550380c544841c00e02150781c0203825986d0350f1111001c134134902c0d0b42c0c0314229006401c400200920a14140b01404200300c008009460f00b80d60b0b0110811802080144450345c40c4816240075010450707001c460141800d02c50010403100c103401c1c10b80c1c0c4e821540ba9641459088003075200400c44c0d040843c00740081d1074a07005801c40241c60110660441c141041129902d441c042d10901800d0341c0c814540000c291864840030652102d81300c80701303ca10340964a104c0702c02080c900640000c1c500714006c284096180c02090180c08034000d0740b4105030465080c41a401d0108200450042c41610308040010f0042c902c40300f41445140d0b25500070385035240143c1004020080c000c10320200d54014070885c1c6443c02a5904481d079204042079480968680e601e40c940300d0340001d05403210b2944540203004e80e0452040d00d01c0501e9504020b0728401c25002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 476838561 1250 476837311 476837359
    0xc0103090b01030b180f01063201080910020f0310050604080303040303050c070f050c0109060e0f0105160b131209061b031404270204060504030305250809 68
    0x2024400041e006101080440c0e00b440e60045003851103501000c018040c507490107810652403d040ea444540600c201e081669200c4186a50b019006006803200480800c681106032407503410490654006103644404000d00031242c0400c00046555040071951982150300031642d100c902e001105001a480c06d1560841d412500201c01450940d2241c0e07804502a003400307000d09541c1d00041c04688045070240112821041c411001400102040000035092201e1a480907007071007a000d103034480c1520f4090040c860074000740f03070590b51004181351643e0400e2209001070554130081d03040108585034101e1005c840c40c041c10300b0400c00740003074500300c40c000da280c002c1030700048840d4401c00c0e81d401c2d015800c0304045d1003030400c03181c41a00b08800b10800c0c0c000303501044082c1921946981a20620000d51082e4440070b01c1c103500d040d0500c90058a40d21a40c80010204040015220b078000300410f90081300b50050b2000300743d10102c1e402d2014060300301710010f07845180042030705900403078100c80c0303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 476839811 1250 476838561 476838563
    0x40f12170a0e0c0d080307180f0603020418060e010b1e1801020f03031501080c090d03030203070f110a0f050f03030c0d0615091401050c0f150c040b0301140f061303050c010309 77
    0x42d4a11b15501c40790101c843c1e0241d00e091522240001c100070036090640e50000d0050940ca0303070300685413880c02881000303108144441d2a191454600240079918807081d005d03040d90040300103542d07142400c40b00c03581381c126030203420004040046080e071140b1080e840c400100d03a90907800c8406141041648035284c0c0b01c161983c100b544c144d2120320441d54050951a82d0080b00c0c041040c1c1051003038030119400c1d00f003990303003280020350020400c08420781020848041070f00f0383c5440e4038081c450b074002541e554a8002d02900046e4003070f07203e10401908202c01110360f0086002d480d00e81c205809003185982084540e15503041c240b4201181c00d0710219480152a1003a544945c0e4461501c140001072012100005040080402220452400810208200100c148000c18031070007020040c0c010214060a0352078034040400c001c200780040780080d0381c15240c403145805021115080000d560b03490501c140c98020b180891030704200c0382049488001c4900810555590300d101c600110121004144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 476841061 1250 476839811 476839823
    0xd060605121b0d06060302040504030f03050c040803030105090a1b05030412030c050316091a0c0615060d05060415080d0e04200903070306020f03070215040f12170a0e0c0d 75
    0x45000b5440e0588100c521140200c40004445459130003240c242d401c00c540a43c040b41d1100e5251142070f60504c5a40c4c2d02240b81401d241c00d060038040300341d40343c0c0300c10302ca41d520031821035012807860551a031203a200002c03420207190413220821005881c603041220213540f080301030441049654003e028180760701505684903450369646c150401288180f5007400810031140c1d601c041140c1d100031038031581d2681d800c0401511000d014440705d103410b10080c00802803081400070849a40c4946040c0c1d0341e00c00441c400441c290703942e0f001060050554840784c420054454500242c00c1c50702103190720180c8400e80d25100c070b040114050009541d481000300b43e08002a910502311441d4420280581900080645d9460399494440905a80001c1c10b2408028000424818001e40402c0803000f485406517032041e052820b82c986074500ba1104001400403a5000c52402034140701d210518803c2c00f0070300340d510781420208038071401054695064861031140641405240c608003e03042030b0164409 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 476842311 1250 476841061 476841103
    0x70209060913080d022208030708210a050f090703021012020d050a0605031009030806090a0212070e0a08070825030606030f12180504020c0a020d06060512 68
    0xc01404100d11009001c0841d403204658100c000030200002888124030041c0050b8417911501c10048103d8501200459001c614039020003c41c00088240d4907036680107001e607611100340105824001d20b442240782d170704070200d508022003c80242d00c031a0059404103c800f6280c7e0322407115039500c94543c0006580a40c0340115089018828008607195200b0b010015042040b000104c1d001d5074015614143c4198550900b8061424100f02e008145018000305200803d02920702801590015001d14000c0300c072031000860345c1d242354044501d8240d0b2040582c1807031400d110010100501c01346c02a1042d25040000181c50301c0020b40b80090718151009030006100818140d06010743c003059880c4400c001c3d0200101044051041200441c007800c6484661200c0385030800d05410840c82e1002802041154954030511a5002c481503c40030b82c0c0051340e610112071000c2c034000c170341400290b1106402d003207441001034030342154040318010f03204035150a034498074181e121b50340340d4100803135845a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 476843561 1250 476842311 476842321
    0x9060e0402030c0f0f0d050a0b0f0f070f1b030e1e01050d02070501060302061606050c0a170a0b280e06060a030b19150f09140402030c090a0303120b030102070209 71
    0x4613986652120000b8451101c604105020958030b80c41e922096a40d80c10603104901804580c100b4035030312001400c4034807010700e800380c03d504101401a003038004010115003d071440314064419484100f940c0391309414580c1d4a80360091030740c11145080c0380600003526100c4440b0452414003074203908140c40e80c9050944084a01000350001c020a40d15036490304e80001c050b032180402005243d4003290b41d034050060300e007401010358a000e06404886102040440e0700640c1c44510340da00d5440c0c21250440f180c4913070100c0303800b400d002c140ea594880c0303c843c007040354008031503034003441c05034481400f440095840054511441040381c0a82e0008410003011079030905c60340c00300f441c0c810002c01030100c069500b0001e094020b81d40c1c218840013800340340d10700d0000d43c00441d20314541610349091b0070028104440300062000421006008507004000300d40c0d450030440c1640e901034009444181c1095603810004e180f4142001ea080d0040d03c0c2c02e0b0902036904043c002c55900343d802602c00c0c8101d482d0303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 476844811 1250 476843561 476843569
    0x2e0c1814061303030809010606080105010c03110c060f0a1403070804021504030501141e010503071e120804180605090402011d0307140109090e061611070b0409060e0402030c 76
    0x480c0300c500798802030400c1075806000e00441c0c003030003950190356408514a841101d040c21142d4a8100c40248115840104126030340708920b40d00190341880c0503060f450901a5885ca001e034240f40302c503440040070030202c14041c881c0d0040c002c030903216a0382d9000c3c1004c03000400c0142c402500c1540004580000203005400d200e4200a881200d40403407514103603a986445084800d4608440c0210b250b40c000c0c440c1d420000105010341c140817400b20f2010b940360000080e90380c0054800c54445d4851001c450307565000301303100300000342000706030301c00080c0c51440c242d20658030601035054030030001900c003403032407100d40f042c1001d4840c0a054071703103251034a0300155842c003c41c4d48840c00758070080c40000c031a84c078140200401051810030000c0d140c10340900140c90745025030024401c842c82c017104d205282d000021a42c0d04199007020520764130341083c404440348c4400340031500c65481407460002c0d5072400c10b00100121102d251041051703503103501e40b60038489026540030b94142c0c0725190b186050f1030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 476846061 1250 476844811 476844839
    0xd03050c0f030409050609330a05060c01090c0e09030a0e0d1a0403110f06060f0d080705070e01050609010f030b01050d0c020a050f010c021902032e0c18 67
    0x100c400c225031140020340a1180703141e2080d000704107907a865505210080c10148203c580041145045d14100c015041e411807d500310400d165031101a00300c0409040e864001401000c0c020151449540b01c2c0345083c1c240c040c011801702210400240760000035802c0f60300203000e02410000000c0e5161450b0201d040326441d0300c1c0c102155003c0171146610340014040c0f03422404d55a0003440c04042031170300d81400ba2440644444849807030b08400c10604540401040303080c3e1000d801caa0b1680214107600218a456100d0080245003690002c4c0401c14080300194070021100c04010102c00d9030307243d00500c02240190304250340030580b1a5643c6901500940020502d5103061401d00d040c240c43c01228415100c00a00c3d00c1c004d0b8000d2510413051040a200300440c5034030540c001e001e00000c03d24000c4d5500592060040303404071010000e411581c06002074003220000010504d804203034182401815a9031410b07c0758002c1c070313007000e4400380c5004881541c02c5000305030244664600c0c0078000142c0c0b507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 476847311 1250 476846061 476846077
    0x7021f0c090b190807020610050405040c0503030309030c1603170306012f010f060f030f050a15051602010905060a020c251d09030a0c0501020918060117060d0305 71
    0xc18003030008211500004050003241e00c10f42c420702c0364000e28440142c2040300281c061421074100e0b5040241f442c1b019052a0100c4009440c0003806988508010300b000c04650002c55140c0000030034014050700001c0903040c00c21051003034a414554045900c40089020310000382a04542c3c503840d803e080500001c0e686c4900103044c207150f4080c000124010841c1d20400c180000d0042341d00d003e4a5010034403641921001407882040300354180071000076160f82c0c80c840206080800d40d40d0700100f10080c0841c90005d50320200b40d60811441c0c010b0340b8050001206c008000c00302c081d00d002d1200b07105014914500d60000c0240465449415000000e9400803074070700c02c42d104220b007e01d84032150500400400400c5140307504020301705403000000400140b107904140d2218011701009120100c02c441d801c0f00282046003408065160441c060f010f0114804d501604072003c1d8051322040140582c441c9000360794914103856128442403011000317131501600f085440301c900c00001c3c020b8000301414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 476848561 1250 476847311 476847317
    0x50d09080a02011b020d03180f03020d080702060403060615030e010207021810050a0b09030d020a05190c080607091809170a110303070f2d0e270f07021f0c 68
    0x20721303158010408025840d00101c0000d0f0200c0303440403252602da00240301400000020503c610715540008600b880480070144c0346440029604c4110355921b021100210380c0a0f80c14401560750b000c200600500110b82200480c1c108040005174960600c22a0f184d142e005051460389403031102201805040101808821001004041403039605c000030a002008001801c50fa194050400c2c182081c2c90b48100c1b00030b66211055100010b9004940e00c00b410031030140c8403148580c1400c0c0703d01e41c04034075800560f20b401114144400740d94060359100c16105404070640880d034050754104100c44080c1d2001d000b416003803a290305884826002000b1403211460f2495810008450940c02c0d50310a40b103410208400e0382440000a400042c54104403070b490402c0c2c0a0040d1b02540c1496840030380184000704201441043d0495031814203009a1098882c200c0c111002c002202c030f001260700380c4604490300c018000160b5114400102c01032822401c803003107859850706208000261071081e0155041c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 476849811 1250 476848561 476848607
    0x1409090a1e0b0301110301030f11040605120a050f06013c030f03030b1c03050304060b1804050c100f08060307030c080114060d1a100e10060f020f0717010905030f07050d09080a0201 79
    0x142e40c8600a0020704501480545007500b410300d00030380f0b840d4405071508141c2d040940104641e422000d50b8001c0c804407034001400d1290000420022100c1072401538003406190350020040c01246640d851003d4400d0724100110142c1d50108035180400510500742d1000107454000002e1054010f15000352090300b003c03c0041251b00001c01c000e08072040b044034034207860200400d008003000003662003101a1140c0b0038a00e0f03030880c002d00303d0001c0190102840303280c0000c50001d0300c0c1008108015900000f038985000d4480c0e0400c0d000c0e2140e41d210030440000c080102d61240f400208510701e80f030f84201e203c68211412100d09039000c00c0208541011840c003500011421908402c0a1051031038040004820b03003000406011016000071502c11540300120349040d050f00020703282c007691094400c0a07440340c801221075025080d0504018546d01020418840d0f1030f000c41b005d0107540344102c0980e1140004107030708413510309403031041c514681c0c08240300c5400341d40543e01d8a0500c3c5100d68000d01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 476851061 1250 476849811 476849819
    0x9120317072a03050904021809010b07030504060e030a0605070518190e0705040902180937090c0f0510050a210207021c0309061409090a1e0b0301110301030f110406 72
    0x80780c0250890315009803601081d52301c5072030001032580c0508a0241d946041140d5030310000c3c00b60289000e110144000105000c00c2641c040103c0e0b04015400302d030901c000d240501008080381c210b80748848290010560100c031a103403150261000c0d00ea60000ea10506d07143c030001c4240c0107805441901842030411000c2552403540c0005c00c3c8426009808101c01a500024050700d08070080c07407240c1c110010b119083c4c144042c0200d200c6030666010b8440006d048803420540100012440107100c4941c03a0030010f469a0315002d10f50841d44200c44030204660650f1003a5450f11441d00c031100080c01d01c14002c1840c000b42c1ea00e0302c80d08010400c00506151450307010550080c01c0d1040c50b400c840884000d40c2c1010f520044600250849c6d00c3d0510009001050800c0280524050144100103801c000758449419600c102540306190142c51280100a04041c00401c0b4800086009500340b2800c0782c00c204040084030304907139008203400c402c000d55451b004003c0303490940842d401911450001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 476852311 1250 476851061 476851069
    0x130f03030206070e010c110d05010e100509070504050103032a0b0705130f050604060c050f0d080a05010905011a1803100614041a010c0309120317072a030509 69
    0x40554400d07001084242420340000e02220040c00b8814100128071141c000054a09140a0640c4800b03540316030110203103150181c0034081115000c1c050303114522050080310700e40e0300308600860711031054485103078460040c40180c810900010340410442030016442c0034150f1000540c40c40201700000c242151a541c1703040c090010f944010024402081d02940340001c0d220300d40040c08208a071002c00c524000100f4600d000705d20400c401d120510b40e81c0c00074000e0900101c80ca40c0c0c1442d09031507208100741c0300a00101c500b9070b46420740a2034130b800859001000d114560590b01485007400b0141d82c64140d000440d88101c408003200c0005c1501a21952010820761861800440700401c500b401c0141d45004040c04145640c40769080028500710030b465194109004807080c6860340008000d41010380d10040c183d400540300001880c0414289940105803032014035001c51017001544800c48100c5c0d444519240001800440c100c46080303007000500c0045c0081d10034103166003000e032500300107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 476853561 1250 476852311 476852339
    0xf18050402040e09061003120513120803041403041a090d060e0105090c0409020a12021903050303040303140f0a0509190c06030b0316030b0613020c0c09220813 70
    0x101020f55071070034416440c4045c07044560000c400e60000c02107034690348032030304200550000401403000004000400c0e100709081c032406480f41540b5100d054513589820321052b4400c40d0f00f03582001070120a0801120b0102c100c0d002c8540e400e500e6607842e120b41640c0a1070364400c1030007940c0b108110762200d000484c1402400600070703070080001280d240c610051307400d140e401c007481c62041e881c1412403030059985002d420183d8101196250040c00f0300d02c040f0313005043c80440c0b54201e401d00c0400204211000004511862090f6400c0c049034018240c80e260074003040d21641c1c0d01041100024040300c01603805503521104481c219501120012240d60210349904810784a040c8094007d1042c15014090302003014420350007404482c1d030001001c0c0304070549001c0200b0f4111a180894a1941c60103007042c5080c960302d404541d1802c1c0000c0480d034400718407075100c0c020491800001c8080d4044040c140d0145040200e005d252039599035181c10f02c0d0700c200842d190680d0301c2803020412660100e00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 476854811 1250 476853561 476853569
    0xf090306130201020f2e1d031e040302030606010e130c090e0f010f12020312180f01050306132a090807050f0607030320030a14060d030f1805040204 65
    0x80c1d406181d402d000081c10002c110044205603440421009140d83c40700e021100c1c428041520800c61100321000c510140c2010440040d8000070203c680052150100081c0000c2d5002500140c41041400c08062503010720701c0007030740c19000315002407820350158171134010003140180200103240040125408403100d6603030303010010b03045140a0000c0e8800004c91500010318140c5e09410398504100c100c1c03001c489000e400050582c00054030110340381040a452031840c00c0d4032064954031200b03100c050540c1d00300e01c4036125400d45852842d284d40100d04483c050030740a07150715003240700c0f03282410280080032170700056040301d00450241c0701460300d40000d22a03d181d0794101d00c00d2030000500d18210b0305412803071085031208604505990b41070304442c0401c0c0c0c50700340440d003007105040f0400c510320111518a80e1550010804c0300001c1603500074407900c51801600c4440e0f0721a60248400700e5130100300100442c0190311402c980601a21a40c100e8000520842e480c6548074404501030382c016501c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 476856061 1250 476854811 476854831
    0x220b0c03040512160501110709020a030b010f0e090705090a03080406030207051005010602060a09030e03010e030a030606050f03010b160f08070b0705032a040506040b0301090c170105060f090306 85
    0x10303050009151160300141d001c108440141381d080701380100142d07200d205110f95070500514289203000110207225480007450741d50011900c61001900180160151403030050002c2c40b402038850b02580900725a0643ca440a420181e1135540c40354259105d03840b600900c0e501c4a01c4110010003d00310800901c0540042d03a40507840320200e2408901c0c1ca0300c1541f40e9072400d41090010301c0280d60004260b9132113a90840c3c0412003108038102602c801c072000c100b10750554248800c080e1074200001c003c1840341c000d603a0410406036540700445240c068644440c3c0104020401040811a40c001401d10504941000c0c207155881e680c0b451005440741030f0482e038255010428030144440b58420301d40c46507581c14a1883c61034010900030700d0465042c41d0f0401c42500442d0985102e4682040d40c02414000d4401d55a1302e4499a001003c0c0d04240700e000016030a115440400d54403620414440c0003e441c1140e0307559080c10308101031030300f00050030070388500d0622901c901035404208050007207070611 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 476857311 1250 476856061 476856067
    0x2030c0a05010b0a150c02010e060d15051905010212071e030c0501060e040b192007061a010516050a080d0906061a040302190f031a09070b220b0c03 65
    0x8060202840155000c82d28540141d110340103c0764004e0031154446d60309280c010085001100029007c0c081d0100c0c84024615140200b281060207003862001c2c0c0e04112904800000a0405c225040907103004690040e0000003840030141d40f40c0c006041914030590760700d4007411000080c40010004844254000340c02e0881d0341c4d05100f428494400500300c0c540b803c601d40e14003520340d40200000648196540d541c0380081051603d80c5900444400c7c041068101c80e80d081c070540c840554201742c2080d0b03560703454000207084580c91039054400301c0178181c42e500e01340550600326101840c030142040e40d445c0540124503000540000081a02100c81d810000380500942881e100300c0e841600040164003000041101d02c0030300b0300c140c408907a41221610300314048840202c291441d02d6000346441038441101000f00716000710420302403034a04407000f40d1503031055601640d0b01550312501740d01070030130410001c0c602d40c40500c840f200c204c905803080343c055030358912406581c80315079998440c2e0004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 476858561 1250 476857311 476857331
    0x90609050105031b0d0b1002030903060a0612030c060212130b160909110405120a03140405061e09120c0f010c0b070305090a0b0901090209060603091b0102030c0a0501 73
    0x4449024100a02c0c201c3d0031072520513450250b16424144009460b9408034004450f0401d94000f40034410740901843c0f0006444940a952a0002c0310b403240b1a0180c038000a5900b9802e01c2103404544900441c00d6408640d920107a50040c10711009075034403a020008102e0511485600c3c500410758140869420328482c01d0401c08503c01409403400510700700001420203901c400080e0a035218101c0000e5403d00940100890b4451540b0494000400341a6500324130350204450117014000e48462888010102c0d00703c07081e10450042e103a1141040c0005641c0c51010740000110f4403024049500c1c0a04a034000382e14083d1020030103a03540d0050401c466542400401403810140a00300f0806c40300042d502c1c41d07604440113260204041e510300000302c00b9001000003264040d0000320342500340c01d000303881c907004c0c0074401700680c01880814007080326810840e080324451000203000d088007264010814404c3c03003450808504510040c400d0400d00c0c04e003849004801c503c5400000350300c01c070b2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 476859811 1250 476858561 476858567
    0xc0a0b010314033a0f0b09090f03030403120e15071e05070809060427110901170c09040f0203010f080d091202010c0c060507020906030c0114030a0603060c0906 70
    0x80014a10b00b182c00c1480754030100c00c0403491241d01a0070702c2150300005450030707054400e6100d070003035401446404c01043c143c9002160b480560440740544440109136902244180c0e00c4450400381007075070b4000c00004010900c24001c25820080d20000031801048001a85140a2001c2408840c0b007401c9070138800c841c1d40151b001c8a040e1144204540804907640e0060142d004910740030381341610006440c01c0a5030b85400715005029403020300f0740000c02c00020240e540343c0a100ba5181300780b8015940705054030718416100003d005175181d190401c071804c0400c04a0704090300071402510240022026550340740103444c3761070320031000161650701d0103400f02c1070380990b64007214035500b240d030344110b40a030b0122403d01510303801c81c0002130a00c0035200480b031110741c00c40050119000200040341c40d5030300c030000340b030030324001c0f21450b03402e48601003015119803e14a05a02246195142e20001309034078000c1d6a1140c201c202c0041c070640c0e00d486220550300c12505190008480a1040c0f0120350 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 476861061 1250 476859811 476859833
    0x20a0e0f0906150c1c09030c0b070206040302040b030106150f09050901150f0e030a0b060108060a08071701020c0a030215010e0c0301090f0e0f01020405040e0616050a050c0a0b0103 79
    0x103049606000c2800c1050106400d101c1542085400c4000003c400e508284104070140f40b0322034640e090f0b19003101803d40200f0b1880b01e80821200140c1441d000121480381d80d0503112041d130018605032800e0728542c2003000808612600b00d405540340c0100044540340000c1c501d00d405103e440381240c151000000074041405a000948641580070050113504010244d98200a0060406894001d02410305681c00c40482c0087c561510403002c440040101203250240541c07403e80b104891500c0740702c05c01c0058000340c066001290300591040103480c1000030b691003c50b90442c00140303000808914103050035000310301035004d40c1c04104101f620f0000507246500508681351204214108102d0401252106200c0d06c08003503154003214140510640c801aa00700c0c005c011585047c0802203124040e4226200c0c0d03911031071038010940003450000c00e5251240014041e01000b50590003003c1d036590300040c1c802400c112083c0b20300200a9400c100025099000303c540051540c55071030581c0c4003035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 476862311 1250 476861061 476861089
    0x120607030e0c010215151507060903140922020405090411030d021902041a04020c060115031a0418080c010203010e06060711220c03090c0501110d051309020a0e 70
    0x540650700f00140d6034203641d20175401142c0740c0030480c41440d40d000050107101c0484101044400d0004061003000110782c09101c4651081e02c90701442001d0221031442406091200358001c0c00702d040d4540c0340c142e880500d03803060514420050410761203002291203804c040b2000c07500760748814094a010302d002c00510f181c2c400300744000c00e08050070144400d404085280c0081c0555201d0224408005007a9103040c8150b00140085441c1c82c07180751a19a191003e1142c031350000070f000740e101c92240c880e001d41e00c1c06800c030310201501400480c052000810303291402c884c01c1c0d421040044000b40322000200000b03403800d8009a00c0307504000b5003201c4940040d250b00c0c42200108400800100381e140036103005e2208507030440b0101400c000c9000c42d01c2c90000c0391101c1c80e02d403134412070865030140c0c440c03101c15004080700c80e6101c0d00c2c7c100544005040018582e0503910070071840f5034140c8214010f007400088010b4001d0700139603c8001c041aa0071003070280020031000c0703211080f90b04080d11610524 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 476863561 1250 476862311 476862313
    0x1c2105070b0906040f0f030e0405040b0402040c0503160e040609020703091e03020a090b0310050108010e0c10051b03070501061202041505131a0d0302070e16020714120607030e0c0102 80
    0x3c0d061a50300c2d000d4410740c12200512448400241905142c0144001540b040c400381090200d4900b6240c4180004021034089104500c0c155550000500c1442544d115000281040e40c440300000d80035181c80f07410009950340300b900c6140101e4117010500107001c90b640300f9118488054140700c0c410036125024507001a12803c00c1c54200090703680c0c034803000216040c200c000154840300001003401c00c1c001141c004401030516000103860340c41503200040e01109542680d02290801c3d04000e084400e1440070400102c05026040d003078100900c0c11018000c5a0b011a440c26090390342c1c907030a603440303030b80a220300254800343c1005508060140040c0b00e008881290325442c149000550700300445100240800c2d603440c104088501d0403582180c03d500010034007404082c15290080d510032960003107041c0c2e00c90020100341144204242520580c0280d0050310400703052010030b0804062081c01e95070310140d4040400320091003800300c18012280e80c0e030041006102d0b071610603e0051080841811 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 476864811 1250 476863561 476863573
    0x515040b090615100219080d0b061303030305091c0f1e020d08070306090204180e0f15040303110a020d0e1e1507050706080a0b040603021c2105070b09 66
    0x3602d100031032000f43c100888510b61000d040d980204d02d80070000804d040c595189034011400d0000c4c1c0e802802d1103102c0e03104103014a001501c14081103008642c0500010301c80407500b4000a40a40c0103a58000c4000b422100309540200440c150071020656000120321180c3c50101201d0303018542d0b031200407107000401580c1c00349010013580c604420102d04100048400401c400a10a4010078014660101d0541d101d540740d040301e881c000c80c2c200f141384405146c102c03006042e4101041410043c441c40c4090700c21802d1200710400070050080049003010760354860301103810248000383c02c0c0c17904154000c10102d1602031f4060000021468000c0c418040200070b81f0b1a00d50441c0025040482980c45040d001701c501c110080501a000009045000380500071641c10b0748035000c244035000e00f50050164450400603c4107c0740c00d40006504180140c3c005014039491000c41200248201000d440040d00300740d24403800381020b80503070700050000455205100e007940086d904000e500c005001d0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 476866061 1250 476864811 476864821
    0x206070b2a032403031b070603060b07170f0a08180708031e09120a030806090103080f030601020c04061d010b0c0304150309060606080412030b012a0515040b0906 71
    0x92240402440d07003000078243c04103c1500d1180c0100010880c0014084035240c403030000300b01110f1898100e00c05a50322401c0e8000032558404c1c0184805c80382c42c4460545001c81c00c3d11102c111076215050946900350400c4211a00361590005084441c115620581c644c20000d032070340d0301341082c107004450b16800b00c0c0701400f10840100c1200c80c42034582103030744816100c4070345030034950040004281e848554144043c01c0b5040c0880c028a4681c0702c0da0340c801c0c81d42d031088100500c182d02800301130007444c4284104551060b01c07800454000d032050045482030700080c8005030a072040ca8120811140b03400d180c481c0ca4013804162a030142204202d074a00b858852003815507030b80035610a8189680440d00a150b54a020341e204490b40d640000003030000b56201c0001138941c2105503070440305050950140103000b4480d01c0fa600399020160b490f200380340007502803058503046840030050440c0100d895840020410021900c451203d0000304503207282c44e0034046240078000709644503030b41040003040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 476867311 1250 476866061 476866141
    0x309051512190513120f09080106090203090f0f0304051017010b1e0c0d05071a0f070e100801050906040212090c010207151421090c030d031116030c0206070b 69
    0x160a403601d0410400c803080e44046800441c22382c0f03c0502c41d441c210010074044915001035105006800c111900503503c094842c2c0c0e118641c81040820b40c10a00080c081803074845050b4149035410704d00881044140c201842c50302c082030327100007251500000e44965864400390600c100300042d585d018240381480c40306640301d021818052082200002d110810024041c05070101107500401000c860310740081e440c8003002042c0c030200040307500151040c00c1454000c03a030f126400019a00c08419910388411301048020140030b0f15440b075003d00c5417654109100032010300c40c200200061295030320070800641400b00c150041210740644218a8003001d03041000d504c0182010010523a03034842140980031208036602c1306001149620b0140300004100003108031320034404406542040c40c0317202c0160100c0d010a00c84905a000a10200ca40e410454114104550080c100002d00c405aa40051840c0e4491002100c0e003c40110900540d8200040205466041c4403880c01040204001d18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 476868561 1250 476867311 476867333
    0x5100204141017070305093a030204090915111e0307030b120d110f07030204110d140415020937060c1406040309051512190513 56
    0x140d0041084080d80e0407443c3c8038440981040e0003c4003144410308190368000c0203400b090768618640e1003003611415000058207840b002d202c500c1429502d414841c6a113441c0160511512501030650910000541840354015490b140d8402e20b203a03550a030019803e0000c8070726003008140c01910038480440d1280b015400582e0415400140685a42e25110b0807005000d90404445c0c010b41c51400407850f070007001440b10000314440d00d40c2c007000d10b1042c54855988500f104550001d80c480c100420240c145503200442440100d10241d00d0b0000c011000d00607118001000c650100420041109100c180c4c40c925400200303040056180c94544800104109040c4400204100340c0c0500015052064142c000361580c0389001d00c600659264000740c00c1270341401c4240d400201464605c0c00c4200b000c910f052080d903140c1c5441000c2030408050180b03444000898801c50b8000f04113a0a40b408583c0e0094420090700c03075002c040d000d1413402e0748203a0700c01a0440a0000d12a80c0da8400a0014004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 476869811 1250 476868561 476868599
    0x120309041514011209080409020a02010515011e020111040e0403110106060c02091305010903021c0e06121009060f140d02010c061a0405040501091b081216050d0c05100204 75
    0x124131402691400c00042000d200300504981c0e001500103901c1d011600940b2601a19400810896a420010b0061000b032209043d0000d04481080c00310b03001c000f044103c00380c400b8800060000c1441c800e1201540c0242c0120a465003510308000805270300c22410303c0510544030081c08000d00d8558050f2a014080b00002e1081e0491000600c1c041622020045681c0d0010028081c2499504029440b0b000031102c500380107584245040c0c0381805158a040102006004180b900c003141c1c4400c2c40102d400340c00d1411050200400041030720301800b8040c09050b003d101d02c204a8603101d401c00303c900c100581c01d03018803004408070300580e81001c407241030716400a03808110510f0345003201d408214280103581d40180340000b440305002c0c056104400b0984203088241035640114150300070035200344124280da13884a500030701e44840300409481b00381c1000900d2034a0b0502c40d643c590038070096054160001381c160a8100030300000704156002c00501c040114506424929500001408891 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 476871061 1250 476869811 476869817
    0xe0601050306120a0b010e0a060621020403050a080a02010609060b0d0b060405100c021c020d0305090a0b03010602010219030b03030711150705031207020105060901031b0512030904151401 82
    0x14009031142c20301101403150f0300301a15903e280700c0c6805000c1d10360a00032001e00090a02c005007100d14139200c0c40d1b041d5075140d1142a04101246061501e40400144100b0001e4091200000240b810004222007502c81c482d800d0310340c5d403171010081c21103115511230b4003514202002000134040c5802103990b10b040d102d41c01304484080502140300351080e03034011900040004403c50910341e02c8000301d8060f138801c45a01c1d01240c101d2000a07460346e417901d8007950180c2c00700d000e440024041e100a10307c210010b060b4054040c0c0c1c44682c000c454000341e1000300543d400064000b0b010110590071307008103590741004c00980380030502003552070003030b000c0042150b0f00c0020001c005540301c00f4000101e0382811141e55032102603180c000c0d1aa004614150071010340640454403030742c0180601c41c40784002410381c260681c81d580b2401d10b41c01c0402c080f00c0f0310b50048070300841c0d16110150004188000340008541e6610b280342400112101e00a50b00610848081c0920004400b4580c1181d0070340246 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 476872311 1250 476871061 476871067
    0x108060f0301090b07230a020309211b040506030726070b030c0406080705030606032212030b281a0408010c0806010f0318150b030601080105041b0e060105 68
    0x101e801041c0c1d50f9405808925071408000704194040d0300418141c2d80181d101051030202801c00001d40a0505810050f800c140520f46140c14a6004104034600c0141c81d054000347ca0400141000c0102d003070f10f007030b1025185c400401c0d4205801150740040c0154020500e240c9002003484642c011200d02401078521440404038503141040004050040b48902c2c0c0e9a90504034080b01d070550182c415a0041000d15001404450113401501d100d00c80260640f0b1a46e9034985603c0380e90fa00700a0031101c5441100d1f00300c800300d1100310444a01076040d4600040302800b04003004030005c03007240d0801c0c0c64201042c0d00404051011114021160070000c800718988030401e0302d0115008e250811030300c80d840c001c0c510384555806180309020310390a03220f020140b40b0003d0110156161045c0350240000c0306480176000501ca2649600381c261a01400184211030400090034588280c1c40600c0c035a458806210900030100424800da02c11061000f0f002481c10f2024190018010006030501c2808 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 476873561 1250 476872311 476872339
    0x10c02010503090304030605010b030603150c040510050706020a08060411040503030702061602030316120f0c1209171b0108070807080705130308030a0b0a18050406060512100b0906010806 82
    0x80003517501440c0d004000f840150303100d418640e0ba0703420445800b8803d06c5400c90036001294442b250034083e1501600303070f80c039040c10841440503901c4680e03288000c10008202c2c500200d0340d50300c06042c2903051566600c056091410400054803140344180c04c1884041208010903a4004112a1080c0d4103413001c603151200c0e03603000d6014440f480c0303001e50513010004500707059120809681e06d010748030f081b0341010030016507000c407003079010b000042000c1000c1035806000300d050011030b400e000681c1d1810108080e15001d0054001404cd8030350300c0c45c2e80c0001500e002e02c0b80040e0801c080c420702032a01007928a040c80006026407800b9242c841800380c0a00440e06142c07040c401c03142da4000c9d0124407102c19a4070310303145a45030300c00c6603c444202c0c60851405001d1800b0785442c03048a0140c1000c0c0800187c001d10b0310b0090102500071590f03a65100c400084a80320302c10500260002c1c1400340c0b00c058011403c003c140c90400d0003003440b0f000a6020800980e820410385500800240c4000f0042852 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 476874811 1250 476873561 476873563
    0xd1205090102120f090706090e011221090305060609070e1509061801020d210b0f1201090320070b0c030721020c0117010e10030b010b040e011202010c0201050309 71
    0xc0c0501c100351810001d0400109020940413a40607048a80c00c0300e100d0b070f0380c40104864180a41c0644013107448184010400b4040c11103c80c0d03c08ac0c00340c3c410a11303c65280403051036a50000d0284004960018010810b11000380000356000506480d801d0403850400801040c090b42402881e10812080d080c814500c02002d0580d80d2501c400307402c155131115480049a000c0300601003850051242e41509160b040c0702c8e2500d01c42034180a4500c02840c0501c5000401404280d40c459030083d4410707101c01055943c100540c0e2100b03441038000220110541401000f660007501c0c0c1c2c10b905440c6004e0100c9036040043c0400803a042d012040b40c40701d041d0203c0da802c610545ea8041c080c0444925000c41c5008000c04401401c01190200d410001800b0015203840c24a6040503030144150070040024501e500070f602d6112072a417010a401da40c0302e507500d8064010a030051100e0810100b02840801c1c0034031456400743c084552031a0f0304220640c0000c0c085c08104000a041180110100f000014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 476876061 1250 476874811 476874817
    0x619021602122e0c020c10030f200304171c0902060d0f050708060d02031b030c0303041e06030b030316020415061e0c12050901021002030a0506040e0d1205090102 71
    0x79400d450034a15a010074070180a1503d01541419040d15104006034003d000150841000c0c40c00703021412031035031000301034004094800308071451680ba680d2001115040d219558a5040c000400c03580700d080c40e08002c40a060080c40030b60010104211448440c44c0b030074402800a1244407001c10202d40768408100103000e07901a820314a414030101c101c181514ad00302030f10803900755131381203043daa902d003c021a003494040302a415170070403807601c031224002c40035840c10110007804a0300540418000701e855980141d0100e00c6051418480c0c02c0d5201c020316081000380310500d001d21100251200082d100c1c89120111269000c91840202c110b44a94101f4200d5040040384c0c00c03a050342c1c1c2d11001e04000311413100c1100f2240a0801d401d842d60042540040298018100e001c85010b8540b064407541e003e000b240d419489014940c4031044c581d400203504c80d480381c0704081a03e0800074240000c1e03400841d1a0102500100711840640d54410a100c00b07a40640c5c801103015141d900f40300340244 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 476877311 1250 476876061 476876083
    0x30f16090e07051c091a010f17070335031b0307090308040605041e08060103080703120203040f020f040c0e0f0a030515061309120c03020f0708061902160212 69
    0x80c03005840b01391494400d07480105018001d125040c2c0c2048082c0b0490140c0c0800d005a000210b035082051014101c0542d0025558210404030707031620780c580c1c0300c1c1004400e44240d0503c40243c0c0107810003915103050080382c0c0740c02100d045c55040d404c042c00c030104141c00300c0e00b501483c03400100004d80c01c43e1291005100843d0004051907960343c0342e880091450740180200021180d0701f04d041c0c00085040301841c1d0454800d81c0c080d1034107900f1962090560b61000300181c04004181200030f402d0f900b2440114000e0b481034010020002d490f00c180107205040d001868442e5140006118180340c0000d240c00780d160049a0780d560080950700002c203601020b07000982148681c1c136003216061100004d040c003c003011505440e01c1d8401c08000c000b5a0111300009004803130381d0720b13040340035400741050520b002e00c00d00580e09111441046149407581a030f02064480c0e1055003400342d040881a120313400711024207001c0d403800d01c03844032042404560810090240c05400a9190f4005007403190402c99 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 476878561 1250 476877311 476877337
    0x140f010b1309050c1f02120f040303080618090703030906020d09090c12060e0a0608210703030615080f07032703090e0f0105040f0507020a060e10060902030f16090e0705 74
    0x15a0404030b482c030f05d07011209140c00262080c910302c00c400c8030050007904e041d00a2111010300d4642941d40840340e10b403015200a0b001010f130000700480b1621003820600c21840c0070010210746240d0708004024084540c04031782990441182c298520340d111150b407003502e5600601240c2c0d145040d9080725866070040011948901d400360220307080408040440c002c0325407100034050f4544a950003906c4001a001d001c04240184181034a07122010019011050180c00d00107412542c0f04140078031003c0010309113000460074020407298004109000d508178003203123410000210741c404141701303000d9000c400c1c003d0650b600303c114042501c0303500c501015001050b00a1054240300e1000f0403070890070300400f4805c60034091100c84400f0944180c510501c04c40d402015210011703101c03030707005104116103990240202400450300002c41d016070380081c4103c1170010b0b40c3c1d01d4070030000004000068505108029508034100003181c0c090003401c25110f0304c1d4102d00030794031000015166881690200084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 476879811 1250 476878561 476878579
    0x112050711030f070203070501080f15150412061103102702040f0303020712081911031602010809060105240c0a0804030201021b1003090305070f140f010b1309050c 72
    0x120352203103002e40b000030310a07070448034036523191801555561b03002c4900002130f9440e0700000c1d050014103803a110011074054903603040c4041c1520081030300e5216411111241e0070700310003032003000000c1c425800c000741d03002c021070f081d82007200c0d6000c1040071a1042e043c001c68042d034103a248254820313840b00700c0c41c98410215079460369101c0301e100c5080e4903c02078000d4080c0d4030b000194941c00d20600586180e009002918250105401d00e0340d140406400800300701c2c42d8141c00d404c5103420401020305490f035080ba4030803541c1c284001070200400403e903d030190012801004152902100c0403501c1f13090406800c2001d003d0009000b00e40601c004980b824480d81c101038081c4000200100240d0b4000c2c7d09840514074244130441590034507042e03c42d0441049500d00550742c0c8281e1081c45214804d2506a1030a0615120b20003000b050300ca0580b0341d1600341c0c8482c0c841c000f00b041a8810b42000c40c0007807254200c14000500405080c0440800c9144c8400c030310030402c4000d10038240179100080001c05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 476881061 1250 476879811 476879827
    0x901050f040521060a020a0c0b09190606080d0e06070f020d0602030f010518070e01080a0e060c0c150103050601061206080114040c1e0b0703110d0e0f040209011205071103 75
    0x2103038852403034030519029480c00b00d26540708600884000302c0180d1944808c2010540c1d648107860801000501c8a01920320784100d03d00c44c0d90424401207001c1c80d0b01040250900c44200c2c200010a81290240034886255a0213a1140c0090b110a5900200c2210007411140080340d8641c07143d08009040c5480002000302c0302080c06941c5041e00c90a8480c0e0000e5141c2010940c05900103441e4034001c506c42803d91185584624071282d8000c1084c5c0d004036508016100c158a44181a6454540e001d4041014101060b041190320140706101a0240709549103803220b03074407400103000b29020406d103c03600b07050f03141a607000b110082c03480707400030002500420b4081c80c4445003902c0c21a40c406800300009852005c0d00b40c0d020700300c103440b2250309181d803a00c0d502e40d64540c4000022401e02000c00020940b00b04180000da025111584900c2514540c46041142140c034503c01c0030310403881072128000701e0340d00624041d00440305d90000501921522030541e003212890342001424031000603040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 476882311 1250 476881061 476881099
    0x60903072408040f0f060b06070308150105030c3703050601030501081f020d0f11070302010e06070e0f010201060b0f0c060c040e270a20010305040203030901050f0405 73
    0xc90844030080706100755055a070403541000c080e01c001e007501c28840c0034000803032030340400b22a01c3c511640b030018014085030007280d000d03004a101900818030040070040c84000c89113044160714000d00c1c00e5461403806043c0c1d480035004a80c40310380040000301e00c0507010b0080040c00c060b8480c400c00400c0f0f0151001c88024003522084400500190030f00000107051000050303104030f101c10190204a0342004500e9600003504103512500000e5282c854a00d825116842004144800c00700390b0b0340d441034641000b9003500c00002001d01281c0c829410000210361055a080315481c0407184440700c4510000101d0140910350844034400ca00054190100700180c0d004040990059060b120595909506600d15000d0740c42000035558030310700043c1001058522011f25024002c402c00000c0000210719032809203d40b508845603e208400006c1340c056030341c90041800320910707050100e0302d440d0340440c0c1c4131700503504d2841c180040868402a00d400b000155030140c00040c0098500c075070400440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 476883561 1250 476882311 476882339
    0x408040e01090e101b030906060b070f14060412050702180f0610030504080306061b011407030515010e210a060b0909240a090203010203040615060e030a08030606090307 74
    0x45107040c030071045003044c44511070154114000e103c1c2c0006409502100c8140c02900540e20203c0e40c0d03941d00c00d00440c015103444c000e8141c0c0b5001e001004034503c030500d4031454202d03025402c0722559121000304000248102d106d80301da003040d403402c05c1c1c96507401d2012400007481d4418510503082d0041c10021202e2402820b0761107010200c80304001a554040d0990031264259005806100208001005401e0a200810303001c081c509840c0403440a4210603402c489100c004840c0da0f44008080c0101d40f43e0600800c0d4200b0301081550030481802c0002030801202c0fa0070460140c0100d00750302100f10440d0644003000c070311503800e9900c0701c4520b15000004181c80c0345501d01c00c600711b07000300b880c0d4040090002020012803103e450300c02201d8820200c400b1000f402d207101b654580c2d00403001a1000e0001d035004510640c0041545240e94617800c000e101c080e0060304c1040900030650312544c0d400180955500d403c84201380d541e40761600400c1c00c601c13401c0649501880340d02400500c0488072054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 476884811 1250 476883561 476883581
    0x30109090213231e0a0917030103051b06040605030a0f1b0206041b060c080c01020f04120209010509153007060201141e0a2901020f010b01020a0b0408040e0109 70
    0xe00010364135032000320044088555441481e050b02030000301e0200403644080681401a03c111605080d14004040b8551090700101c40c25080400c40c034500e040c01004820f90001c040758858241414170300f00405901009051ba49059140c10007811011a10b92280c0b88107a901041c4002003441c0c064042d41c0c1740c0c2d042e5000c0710100714034480c902d4500c50801a1000b0784840756248140f007030b020381324201281c100ca401e038000307035508001000300d40d21800010f01c01031003045ca8810b0042d0342030041008044050780a1805003401108001010b2034034844040102400c0341c032101a50b140c001380201118548505141440704806c0c2ca0702d00010004d5904201c0d1820b81c000e0000d15101d0b00205164602643ca10380b11501d600d000624580404607015030000741c14200007408800c141401486012550212000300910240500d095a05000b43c03145451044024822044203400003940e445c22003901800900d44440070408003e074041c200c038010282002075116658444121074000d00c2d484103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 476886061 1250 476884811 476884871
    0x30809040f0f021801120605030706080406140f06030d080402060906070c18050907170c040c02100507030b01020c180c0a020a050102070c0e01210314041d0a0b06040b030109090213 79
    0x1b088540070f078180124016504042d015004d074510b0300a059070008400391049514644443e1403022421300052030030f200d0201d001040e195030804d60b0926080030080d6071030104101c80401084096100d141c11520150010389045a80d69110708241402440743d800c600c03030400c100144043c10b05416000030b80114200000e0755491551940e142400d0760708200f240655401c00c494031005840d00740d00ca82e0205440e4016180000f60a890200032100d01b00c84036800311f552000e00013002e503410440070001e94416a410800740c03081c0c00e04079010360401886c61612400004407c90098803d110755401594084000d64494200d480e0850f40d019141c0554030f01c060448000080011010810512108840d1607051340101e05440c11500600341c0d044184000710104000a2007910b0034049900c0500b460030031240e982400d44100040e46c0803500624450b40b0103020500030301e48007004490454445c14070000d0180014400310700e030f00000201c2c120183d8035214180407602a00c131510b44102c21540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 476887311 1250 476886061 476886077
    0x608150a0e031c020a0c02120601030c06030627020c060c03011a0f180a080709090b01050f010f050c0a1406091e03040608061c050d02070807030809040f0f021801 71
    0x8421240d07203004845502c2050200044a1a01c4084aa006180000c903e181020292051f5004903586a40c42507031455503034840001001804800020107010384803a240611181b850400e03854101540180d0076102c1005030315201c6046e60345c90381110038000c4110150380c082c4c039042001500c180c00034071501120400c4440380008040c140011110b02448039800c3d40e05002c1034030700c21607442c0382c4e02c8441074002454032000324451208100844c0103211418020843e1041031500744001030040e84103d025511b03400b8205466030f00160038084415482c600552148a500070b42c1d031500c0841000a0000300845031503004694002c01c40034031074011201140ca0440055500e201c18420019014400b0f4005000a1055070b1240604a4021600a000000e84028a000248105400c01c811035090740140320003610740c0d4051001030000c0114201030640d1510799207881d41540304844020b0303c503a56a41d602d0200d0a02c5034480c1c107501c0d103544011919081041891010408030408250210f4080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 476888561 1250 476887311 476887331
    0x3071505010e0109050618090c2b02010503091009031e0e0604090f09060c0215011508010312030924320601050c030a170a0e07060e03010608150a 64
    0x40d0003068102d6800e50700070007440e03182c02d071544000c100c094481c40d03021680301d4604042c90ba800710014003c030030032400b510310050341000308040103031948001c0030f08401c0000c950600102071542d0324040c03034080c01d0496485e51340c0d00e6503d0a0084130500c1039000381c0b80400321424158841030b41c020503401107440c0600041c9140c0151882440c0c40c002640c40f00c0308002c241302d155125080b182d4840001300d00883c40c2c0e151070780c42e10242d41d182803880f40182d2180e036070381d10301803007000e0401d0040001c49250000d8003a4100001e1950105010207407031014200c60b80c03440b0a120b680030500a0b82c200c240950ba03c10083e0400440200d07128000300002e081005a100340402400c1062460005e00d0503402184081c0e180c01c0700301000209003d051081c00c1c0641551003005000401a180ea1541c0394462040f625041230003454001d8070420003240703803180154030141d000034090180d8206003492184214001d002a0147c0000e07002106e403801800c1c00202c04005110b103590050071103250601080d042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 476889811 1250 476888561 476888603
    0x61d010608220507090501140a06030f0e120706050105101407110910090606180320150301051509010c0212190b010510020c0904030e0103020706020f21060a050f0a030606080307 78
    0x8236101c0c05a0210020b86d080219501990000a0040750400301095442602000508101c1003001580d0320ba280000e15104201f0750307200c0e9602400d003c840501901451460080120241e2443c0024034040010800240011188850081072004110200c2481c00d0b801407182c0d80000c0c414209081d00f4802d002c500f01d8052005402e07800da240d40701a90052a640744d0904000300000c2901c0854950410702d0303900c0d1195400030f2840d0f00308000f020b80d40e5140c82d041c440d003400758403400d00900d9810701c07245100780ea006004986554048031b1b450401403105908909100c02188400c00361008104258100106106414100d903000c43e540c2c1041d07196100300f84e0b281c0ca074649010341d01c202c0c1d007400140064043c1c0c0d51a29040418900141030100f5a030ba0341c0c080b41d105030024196007102141182c54425000c15414020028240030119400c1c200041a070052403030040d18400c14242d0051303c2251500b2004a0003550041800d000e142e96803048192240c4c00f01006441070512001d4040440e85 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 476891061 1250 476889811 476889839
    0x807030c020307020d15090f050c041103130201030b121e0601030317090a060c0504050f0d02060924030406060608010e040b2d0a020409061d010608220507090501 71
    0x840d402031071810f8215030820240c00c0d142c03801191641e146240e00c0c01c1c52003031803045040301032084e070490312010700e0b6051161800742c040080c0c520542c14250100c08616084090740d0b001100d03034102035001c02e098801a0003178070422494a400194070311248441ca10000303844086001e48a2401d9002c1c0e841c4542070f0f89a03d000d000241c042030343c22038603044155451044035801a0040280c07902d0f039040b944d480c0199404007905900262001c5003d110b06d00e4005500c0400040c100c600810110403035000c6030490041100c068440d900741c0690311400a1010b042c050541e40f6040b0580c4e0301e20301803034000020b0400b070040000040c036000010501c3c82c05450070a0189401c4549024941d4440502181d005210b61045914000c50001c603e2080000401140a5502200090b84580c00d0003222411100194050114000300b81c5142c04042c2580c5400c1d410348680d4542040c00744d403420381c60304136801c4040501018001140380c04091000120319034095070020002481141d80e16190700032404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 476892311 1250 476891061 476891081
    0x1005010f120807032712030816120b03070306140114030d020a0f1a040b1902130b13030b07030c021501140f040f290402120106030f0b04050403030c080703 68
    0x11400f0011040801d0042d034104041d002c07108000c080101c254aa800f0284c6401c0e880442c0b4049089403030810180c0000c2c000b540407181d104101244101e8402c0100319102c000841603403c0d03500d5407611145d071801d000d102e0107950440c8081c0502c0d00401c21000c1001000d11841c1e040349000c030007414cc5460f0224801c0c2140c91958014400c0e401640c80308003084141e01d404440070303034091284c40c240700d00c0364807024841c5014018030401403504101e09904244043c2c5a00c0100d441042101014008181c405041e107000000f0300380c941070070052150001d80c1c580c0003c0e1803011038004100d10716070300d50002919020144d0a44400610404060212101c28010408400a6071104070310600b09400c00000a89000300f01003500c0082c4000e0004032a0080c02d03068400064618551443d45000000d80c804d09003a00d0441c038009007220010410074042c016070040540f94904244045081c0c2c01145c501e0200800030403c40c03d01e482c1c090010075900b488400454940e100081c0e05901902c10100d8003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 476893561 1250 476892311 476892323
    0x1a120604230702010204150203030412020303090a081c0207080c01060e011206180b090f060c0307020607140f0301090c0e0a050a0b07060f05090f121306030c0e031005010f12 76
    0x410301c6030941c20201c10041011007107650900002079060034260150141c00c000e90040c550f41d041500b401c40900d00ca845001056520810900405c21400111b503808503800c8005a510390380c0c1404011032045038450070f40101c0340041500360601800c00024450500650000c000301c0e40c0e1140c410101c0d0000f403082c9607074240300340c5181d00810075a40001b080603e10900c00030120049035035000380300d402030762001c0181e4004880124a03d208118250304010000700146c110b10b00208002c0d80c0d440b00400c000c041040010010410740221410f480502000000c8036440c0d6840c1e41140c40144240044440090340b4810305045600705203002d10251381e400307400001704904107940010781e64880d031000c0300e40e1a80c5000c4804640c40920485000301c44000240801d01c44030b00640e49442e04c030009884600340d00300040010b003104503869508882c141e00f00800c410312080001d45d808002d0080041d0117015035000d0500700c030002c0d8001810380c0d5000080222050316480208440e80d4460703401000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 476894811 1250 476893561 476893601
    0x6080d0908100509011812030e0a21090b03010303020102030f0703020901140f0d11070201030c0908071a210105011e020604020d08161a0106110c0d0c1a120604 70
    0x1069070b00e80c000c0e41c2d1200c498000403030303035050121206003820b25031102a03d02402076030301241c40c280c0c5400b0750080c05012100070319016049403100c0007281d0051420601945000d0000c180e6075024075052002841070004190700e82d80e582c200607010758012922001d0b60440c0d07800203160140a4400e50b005458180d494408524452054451940c4400c040000f5000c0600058080107450701074420350642086050341c60740400c0c4000340c1500e44806103c0c003884101e960511041000046900803a460b8590004105540403201140e0f4032540c403004c010520120300c080684034164a445049034020ba9a602024810f4649a902c0f14500c2c1c036004010b070801c8001c100546080c0c24100c042c03600507208c09250100950003050000510a8110f83d07420704c1a400980313411004e5046401009982440c03200400031100d290b0b250b00b8107000c1a4400c4100065805c24032070255010400761003050618507180601901034040c2e83c0050041128500303071580042d00c03d00b0640144024040ba440e10418 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 476896061 1250 476894811 476894833
    0xc01050726090d08120604020403150902131b0905010207061407050f06040309090f02120612071a13091107150e01020a0503011701050f070f090e090106080d0908 71
    0x9400d154181c0032800c0ca00e418808080541d64901c180e1100c82d1042e1001035449038150212941084002e10700c5c0d1103240305000070004540ca1800401281510407030004d1502e250b480020350040c1c028909881c40c5e0301d40b0060404101d100d01181c040303c00b090301c038441002c1d5078500480e6960801d002c1c2000140c0a059241c140c42c00304409070031164400e00989440051100c0c0c801d2400030202d40580000f1031840c420840d5070074500c00c1014140700d90b030040d840c00c0004a120f5030342c868040c018901503610003c00c030303c5840051107084041d01006c0040c94614100c1a20040c083d0030201c0600c0d620103c81c403001940c80518400c80310360303880c41c000d5141031480e240c65a800203a000f0014001140d1a00007101945038203100818884505840701da0300c079414200c14a44040985030b004c0718682c548014412551780d040c03159940b00ca1140703484160034000301000c44502051340e05c10030080c0104170511002e194103410090507101000111140d0151801c01210640c1452148000540001c02040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 476897311 1250 476896061 476896103
    0xe03010e19050705090a050f16021f09060e061506070f080a11060916060807090e0a090807050d020d1b030302070c08030d0e0705040b01090e0405120304080c0c010507 73
    0x504400d0003107054583c0d103681c071000f00b03568840c1241c0316071a50f5030742c0b820442d80f5141081055000410015587c620381c43c1c501c8007960781d0886003c07141010740340559510420030a074002100b00383d4030480900105154400e415502c540598021442c242c065403140725a06000042e2580290800c26030200511240c031555240d40c0003100c1c420400c2550a1403155151040140c2801641d40c0e00c0100503000c8541d243d11000885c80d00a8000c00c03822005100000d94040c2440c0241e400a61a450650310703030301081c500078600e543c4014000d550128140c000e003c40401c0170300491103140c0a680c019079030000102e403400300c446000c004480d82c0d00d2526002c688a54064021107110700c941c00c8a1980b03880c03e1304e156402c00210b0003142910395401d502082414452800107081c00d9030107000c0d038196500043e12001c01380c050542501a030740005424003400f00301481848501060310340d0b032400c05007000f08042e8003c6208410522130721305c210780c10354810000c0300c0c04550002101800c09020720079807 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 476898561 1250 476897311 476897353
    0x8010905160923090c030a030206160801030302030a08060f03100b090a0c08010e09160b07060e0d12090c0506271e0d0f170a080906070c030c03030f110702010e03010e 73
    0xc0d491840303991701044803601e00704024a0224040e40040c44180f420030125600c003044a80440c040144403070042000a40001c20b5134101007007404e2100280e61158086249180800c0340b00b035162203080f00b1050340c0025640101240034041d618000b0907960700c039001060368815405103000403400c000401580e60741140503504070b28550309985000e90701c402011540425900b00d0610030340300060441c20020b640c802d01c0f9001c0d580c040038203400c140b90840500aa0060303403000b22101e8454965408010820f41c401d0041c003c001c010640303c10030b03d000c2c0380b8a2190710003400c40c18208a419958a0710f4070304181d8043d00340e041c1b03a4041c0b04d4030340300501c06804e0350355200300c0e408181c0b402141c0005c1c01c4c030450414031014500f011038840005200007031910001820b1041d4681000c41406030300c80c0d10048100301c094040c00e140c00c40188903e002c60003000c1d030241c280d88071464121300c0000010104010540b41e8000d0b030301c040e03d4880b0b010815007240c0601c0c100b014a50710005058040441c44605 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 476899811 1250 476898561 476898571
    0x50414060c150a02160804091802010801270c0f09080604080d020c010f0c2f03030601050a09080f01060911030f0a0e12030a0501051005070803150a08010905160923 72
    0x50f0a146400c030598101c12417800d02140d400d00c021a0034050035000303100328800f000000c0d490440400070340d000071700174407018007400900c219441c464004c18003c0916406139031202c00410868810714050003041010f40170055400503114000001d041c040c000354141c0100c0d00010098908a12014441e00039030012000d69115501c1d5814030541c40c2c003d20031a40313280c071030340c1f2201c0d4190786040c40200c2540c0030045c6a00703c80c204008541c0109000019681e001d902070a0142c0ced50034104800369032020082d4420340b014441c01c40c042c1500141900070504036480c0c08400c1c044840040e0224103140021200020342402500004146454641255045041079401d40b03d5011803504645030a0307004a030115400b6460300c00401c00c0307041803075101d484003031146030950800035a03030381d40c050921014140c460741e9100340b100c40c1400da480040c024002c051190080000041e149071140d1100791451041c07090030b050031800151244e5070302800701d00c0050b4003090b40c021003070340503134900c001000740c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 476901061 1250 476899811 476899831
    0xb070f120b0a0b0c010c030f020a09031415090d080106090806130804120605010f0803090d08030603120705160b09012312040f0b150906040902010e10050414060c15 72
    0x1603c008960001c00c80340038034000200d0b03941a0f00d08042c056610400d40404074520400440d00d450b0740c42802c0805903940a00041100084042c5413803030801100c81c40b1040240030818007014681c0051043d401146c2e940702c0d9002aa60b403c81580c945a0398841c4190507000100090100c01071a03042d0010a40715521a5040540316058205081200c680c00c035000c5030f9600041c80301030003c61000000b855a400114a4258a880403401000c0c0604009005131000300205040e541c0500ca105545841525040d031100b9030313414010b0342c0e01c4a14601001c80b210181d404203045603803d040b40c1240d001a103940782e140c0d16100e007142d0400104140d80b24062000d01060048914454400b40154025161095020502d00b40000c4041001d001c002e0a83c0c100800c84916450350340c051070303210204580005541d100b900050320054000903110350300001c0c1007400c80c032103500300b0b000d4010307920690344140f00310f50300c102448245e21440c1c101150b1988a510f40078500025241006d900c00c0c4610 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 476902311 1250 476901061 476901079
    0x30403120e03070905010b07110a1203141608070b0a1b2f010b091e06060a210515010206010812090a1d010303030b090f01170102130f030b070f120b 65
    0x2074000405c4500a03003000252610000351802030010340141100011422a844810203240c6070346290702108840c0d0041c14042d0350603921090b03244000030b071f0324215070511100d05171039454681384880d03038450b543c11500014064041201d0f015030744191864900e0000d405201840362050a41d0700c01b0300e80701165401c2030f440c3c20407800e940f40414401c600303003030020022440604c501c04100c0b100d24002d20396145c180030300040f1564413801c013501c44e400240540b8042e66602e808070088038000c495006c000c80417580003181310740c442d000340e0129200381058103901c0340010f440001282c480100384038202d00e95104d0000464001c01c600010001c02d440140a11196a0345000130000c5810a680d180103210348000104281900750003180341c0004111070170f15007440c1100000c8d4042c50103000351a02052804500041d4000075030417200c074188401c0d44913080315a60000c0c1102003910703000c00c591001051020501940c02403d940680b184c1c1901e40000382c0c200440340034000d000c1e1440c1254400c244c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 476903561 1250 476902311 476902319
    0x70308030c09041104050306010e0702030915040905040b06042304060c1809021c020313060c0311070c09180302060106030c020a15021e040b091e04060e1503030403120e0307 76
    0x140c4541d13014000045841e503155440c05c1e00300740c24003005a0290350403011120400c044223a000c8200c8003508011610320f00b2680401c003910500b0700458100d076844910b400b05000a00c9621600540b190382d040f80c0074415054111480d0108801c2c02c81e04043d442008008600041c17507030303048400c801c2030b24038009002c1d08901e4242d200d41c00490340085030302a800501e035100e0f2204a43c5521082d80c44110a61a5040503083d007101c4280106000d01130582d074081821506110750003400719840703000e4485031900104c2c108810800114030508050728035058070400043e80c41c54108038080c2d00764001e481ca5030700e410780039006408103074120030441c00f804030020700258103407500c20380030881240d0042c3c861074607500b003000061828040044440341400108840c00d0603604659500105440c11807884c80c0f0b400100c3c010888131461540d009040142c00320340403106040140c499220b04544018185910b420716807248542e000191001031140d180d94a03541c0940c280d42c408000180c2121101917507 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 476904811 1250 476903561 476903569
    0xa020301050f090708070506070201050a020c090114011d0a3305030f0f060a15030e0307050307051b0904080702060d0f06050a08010608060a0504140d09180c02070308030c09 76
    0x2102c42d14107400501083c00703590682000f03050043c00c0084002d101c01d41c1441c0c0043e07039500980710003d040000c00200d44154030320900103403c074014090444811303540c42e4010b01e0756102d854164580003514411100c905816800c181c1e44e0784c041c0140298070b000b0b0604bc1e00d0f066481d02d140b40d00b002246601c241c0190202020071012080d007071681c8064582c02c0c1110078141e8620003400400080300b40c9020b000150f03036a03503081c40071103c00000c50500d04800002c1076010b80001030450301c1500002c1090000d105011005280b03141c41070050b01e05962a480344240701500f01086160041112000a00001d0018000740007980c0001c04480c03c00e09040c0030b172407c0e2500310751007000d66030f16094100503c1c1030003100c0c000500f421400911801d4201550300e40d48180082411000549030300100e41440240d20600300c034140610244c60174001c6040c0003410100300c51041c1c03072440751501c0248203010102d2040c1020082c645e40034000d501e107551145045a040907022408600c010072500405540d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 476906061 1250 476904811 476904821
    0x12060d020d0c09020310061112030702010e0f15060a14040903052b050106030c0c110f09070908100c0e2107090b0907090f030b0a0f020a0c02100f0f0305090a020301 72
    0x3d006100540e49250003020f48007203403010340c032103002d01c842e1601c01412120045017a011400c1e0030719034075031266a0b21404a0151540344c1c0c41c0c907524025089403944506d030229841030301341032030280100a502c0f2503091001480c003030b120700410329482c65001d41e8240b4164208181d9503009217055810706015210f600705030415261110400400d0303032001c000c81441c0b0f004d894010030890a0030002500d0250016025804083d4000c0c1180c4002d00704002c140c1e01c10030040f00d21a000b40407016a0315081c040038010071400c0c0507070f1032248912200d210a6488500032034510b22034964800740440d5528062040c4e5a95507085652200344120380e0b101e1035201007149000030000d648001c2843c038200303420700200c5a000351820301002680c41c02030014900d00c2080301c040b00e82c070800049480d03903500807810081c0a0340034407550450001078021440f5a100300500b40443c02141e0721714035142100c40c240e640c42184003410000c102c0105d0358111f4140603a00c8580d00242e0b0700240c030785000300c5030300003801c47d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 476907311 1250 476906061 476906069
    0x706060b04090b0108060603070504090b0406080a030c0b091c05090a08010e0102090f121504031707080f1e150402071202030a110303040c09020309030c0a03120e0312060d020d0c 78
    0x50380c60200342415a417108100f80c0004064071850700c1c41c1400300780180303144694094000780d5a100c14140720592107660022008140500680b1448031075403a00030904904440c0079070740d841b0040007207020000041401c00110710407401107001120b0b010340c00da680750007102c9000d5100000c2d0000281842080c010000004180800141e0310702e0404200b001d880e18040030f0600a100940001d080001c3c0000c9480480a05d0404207081e6a10761508941c50060003202036841c110304400d203c0344540201d400d03070160280c00d4448610b5503481000071850355080307600c0320310000b605000c10656110880c0d00500340101401c05480d0003041d8075600b40354243d815010b001613000044402540b5401503144d4500381900f00998a1410035454001c802c803558040d00003203540c000301190340c54800700206c1d240d035440306054a001c94400d0074040c08901d200e110400340c160030208402d40401000c0200d0b440c04450002119554070740c502800600341c0b42801c201e80096090205002040510103514010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 476908561 1250 476907311 476907329
    0xb030708060a0c050301142209120305070509091f030606140103050105031b10030902030d11190b010e04171201080d03050103020d06091104020703030f0b0306090604080706060b04 79
    0x1d0620902c80c00072a11180c19000410500b840140900c62403074070010b00c400e5003154101705030703000b25403c504421640c0440100c224501a1240101b148000700385040d80c0c00c5032801c01035552a44019691441030642e496031240e1483c00084549030300a440420dd044800d020b000419103a588400c02c661098000746590004a04151440c2d80d040c00707154050482034010b401207403000e12a5901400b98031507807500c280e401000e802c0402d4400c0d84005110382d0010115a03c280742184054214508070703490f04c110380a101c1c41c003007902e5000305141d50300030b5211060400030b80ca45450000c0c41d030000382040b2140c40002c030000003d03940c80070240108101826600c446549010580d43c582401c582a500905040100410141c3e0b16540260401e03038124601107280107c40ca40014003c42c46500b00f5440703840401d445080c154107038030501d8080d1070b076002000301056143c205640e514046588050b158801c400183c0014a1180036100035031148502280c855110b80c2051050f8005400922039 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 476909811 1250 476908561 476908573
    0xd0806090c0705030406030f02090604152c01050c011d06070215010f0e10081209090f01080307150603120806030d080f1314060c1b0607051c0b030708 66
    0x1940c0380485000d41c000986410281c5800c00c1c5688094403400390f80320b500e09140e40c0e80c80300c0d8103008941e0100c2c2c11103c002003032141d8494691815035209040341c051100040c0702c0c820000d01c1c0300c900314501d480f410000394021303044582c24001102c0761303400000c000400e0b540314400244290b40d0450000280400280546042c1c43d021783c000b4030301964030851804240c83d0b08010040f0601c0019000b0944501988150361341d5100603404800440301d600c101e00e00d20a42c2c1040e503034200010042e02401d40211082d1750700da20703031a03c0414078040a020f0120540c000f00302500004d040f400e4251050340d07820344040391044c2d8a4a4100c0151000320610000c9094001004510b15080c803620031012182e092185080c1491218407131070141c0180105080a45182c00d102480024001c003042041050b040b00c2040c80e009070b04002c1c0d9001f107401000e00134101100005c0310240401c2c441d100f0900c594804e4205031034403030315007440529885031400e4113a03200c03000101910144a4000036094810007005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 476911061 1250 476909811 476909821
    0x91a0a0b0901140901090e070509130c111f150f0605250c0501050c0102040b0d09050f0609060604050414030a0c020a0807062c45060d03050c0d08 64
    0x108450070fa088440914042102d8a5940e8101d90f4800903100200011041556407a1040d11103110b402c5c00c0701d5110390780c40c2c00c50407400811b420516920409d580d82100704094a0107003550f405a03610404070044022008001c0030711580d010107031100f10038441c2120680c0d54154511800c0079070300210006100045c690700102144c2c1c0e11280c80355004c10a140089000d0b840b000c01d4031400d400b0b02410018000f0b980810213809405507005855440c80761980c038540503691074014403001000700c0b143c0c01404030300750102c000410014414169900900075580c2c80c00108001130000410071a500b05050446991815040001e000880c8854444840c0e403000390041040c0d603142c55000059580c41001c080c400d50b60303c90038000d0b118100c080050b214096a804850b541000c216201d900708407031414501d41003a00070500413002c190407440040c0740000941e0b900f42c458944401c0c020090402300880c07201e09054000402560080c603000d42490001c59410381402d940c075401100081c0401c047c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 476912311 1250 476911061 476911067
    0x7080901032009130f020a020c031608100f060b04060806090a061203080606070b0f0711010c05030103030e010c0b13050f01050906040f11060a03050a0e0f07091a0a0b0901 75
    0x12000c0d074241002200102d01e091508100b885000841405034100e82604603100780e841e0010003500001c900c0540d15203051101c000e554180c004410380c80b83c0b1846441c0d00b50200e0702510340701610900d401401d10481c1003960360003c0d045840600c030709581d403490000b400c0300c100406840030302602d517208406400c015040080040b0041e0051700240e14020041000804c1c4900c050121a49800c05054540e11440001d4443c002c120700548210341103401c001944000d1810386102d082543c850840c1041c02c030840e242220031900d4514041801000144042401101100c40040d4145006600c100c155a904000e840301503940e02c0d80764010140640420100340100500d240411000b00020314004406582e182ca001d00050603c12000c1040001c2c0140140116844640607051355662504114014024101121030086082c50400c0045005001280e6415403041e074100078410305040c41d1318000100050b001410710103501e601d00c0c030401e450700e03c0c14030000c0c25800481503c5040d10790000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 476913561 1250 476912311 476912321
    0x211e0f182d0706020606100512070807080a06060e12030706060b041a07080a0e1507030c0b070c020a060521040c0f0b070b0411040e06090105011e06080c0d110708090103 74
    0x71a15a0410002804801c1d40081e0b4194071110844070011546801781081d0303001e203e1010a0882682820204440790740c00003585800340d034450340d460740c090341c440003010221032450003070000094840d9504811881c140b00b50300700490400d010b99260030010f40d0394104561041c2d000181903030010404202c942e08519010a51983d035031340780ca107400010340c0c40d40350502c02c014000f010f005941c80303c00d0494440813083c400e8081c500a003207980750110300700034100b46020001107880501102c000741d0614031582c8140d505a41c054030a000b40d0341031140554450704021010300001c80c0d400c2c90501601f044280c054026405a18840380e0030f802c001030510440ca243d0031a0100500c10420074002031044054603034460f03000004048445c01040028001e0301d00c84d00214001e21410052080d10700040d48a24101c404101c10110303d042500540300e8046036500c20b81002c282c114001500a0203444024071140702115800078504c149002203030b8040d08400001c0d508604c1c086003000e9256018821 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 476914811 1250 476913561 476913643
    0xf0f09030f0302131e03050d0e04060f060c110f181812030406020f090d20010e03191115120c04050d0609050a0206211e0f18 55
    0x100354504001c0042014012041744500c00030520310045000c100e40d088282c0b50061030707200d01030310070070601240014561541c00145620951034000001084240b455278401291000e80380c220400195480340240501d04c0c03500550890b110036101002c0e0755580311000c101483c1e00007043c10508108849558140c1101c00141c46540f050b090842a043c195060383d5215501002c0980d58415009a010403030260312a05604548840c0d908400c12801038003101f9030320790040b03d110342900000b00454503180c4602e86990140c00216211103409014804080058010a00441c00340503840c049420188255075400398010702080a440c0e100b1260310158100c2c01c2801d200d17080c94200340004a170030545101c01800140da034900c490400c0014400301d484a500281015240d014100300748121100800407208a0030840c400076803080c2c0c0130100100001c0010480001d240e541c490705000900c8080d140300d4440554903c400c00c2c0e1001044503000d008056013120000580540d0702402424409030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 476916061 1250 476914811 476914817
    0x20904020402220f17031e0307030e0d0f02010e06070905060904020705120726270a03051020030a11040b0d270201020a11060702041d0d080f0a050a0f0f09030f 70
    0x801410341c4242d54814008400d10387e00801e90301e40300e142069000f460b035800d1041040c0214a24000c82d66003105505034210080d40003400b506010a00b16078460307074125450800b00f138840a0500840c00c041c0c000d4a007400b0003420051074080c0342c0c2c44151600a142c803600c400c07100001441c40400840000d40030b200ba034901c0e28041403207c0501151458040c110380c0803201980d00c201d803504010108001100c0903000341c40300003404e44a0606a03250705218030700b1043c5505140040c01c940210103085c80d40c602e21000030504544070255850050098425800c9888105100104405280c6401800e10b4107464000080064080e150a40c000500d1444203440d1680c0300301c603034090b1360041040b03d1042d0723201248100007400e200004600e40101e1001941003440e16000961001041980e119400c030404e0407115200300c201001c40300e50030304039050341c11402c2c084040303206180240c1202d908100d402001041004021240c0030844046105800005885000200500d5004040072504c1d515900d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 476917311 1250 476916061 476916067
    0x10e03031602011206120309030b070203040f03081327050c041203030f060f030b0a051f090209060706020708030411090c1b0a0f05160f03020904020402220f1703 71
    0x21081548044450001c1d044c020b00c01071000c102842c9510a4001e0a480803e0380585452800d008100c081383d80400c81d0340b0030b00c48002c200424000010b8900b220754032008000702608654404207281c2200c00f4518200c1402100414000f0020301411140900b00140c2101c2080843c010010340e88040c5c010b0000001c100000c3c042e02511001950000c0e805080100c0e140500c00702d00300041c0003030741c03001c1e4814003820400b008100349054043d0146000d58170912040e02c4841c0c1c0300690a003c200540007003220110304010200054001d800c95460041000d820310758541c880b801660310941003200c18000000c01c010400c00301c82503107404400b0030f507107020852600205914091080300368541c02010b403441c02d1001c9100c00c102d04c0c10160350148008a603030005141017690340707000e0b4111554007001d802010800040442c41c0e402100e40060030904280c466800f4480254443c3ca03850b850f429501c0b0180e0442111885d0b030700014181c545403007442c10300d00002032501403881048840702c2d400c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 476918561 1250 476917311 476917327
    0x5070f0f09050a12050f030c0a1103011103040212030f0a090302043602062106010f05190f02010b030706090f0e01050619021507090f120510020d0908070503030105010e0303 76
    0x1442560003a20441a5030201201c03132030070040d2400801c244076080500c000a0900c40d078920104521803c0d07841100c0e03a04200c0e500d1000c060a80e072465a107007015040500009025242c010200c0d00021441001d032460b0864454400c41e0541c4102c2200d00030811054040085040500c607a022199a00c107030300e26000a0300c0702407c56040e114511100c403000d4102c004d015542c80108940303501d100c003404800144452104602d03005000c44e0818080b0320100710030040d075800765080302d018027100c0200c03c0c96060b420300190380f041e280081880c11503503030f2280700b600d82d10b04009410152100e0703100c284c00d0502d446c0566a10240c240c204e140980c401030010050b5032141810354000d42503c481136100c0741001030b0100e00d05421018001000c0c608c1805006209400011007000d403078040e020100780907162141e00301c40c02003890f0010055030007000000034041075a4083e100488a0000108041c41191624a00b0b900400410354241d0000801003240703680020b80001541d0054015600700360384 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 476919811 1250 476918561 476918569
    0x1506090c0c07061d060d0506090c03011d071106070c0b1807030f03170c030406140717040804050a030b090607020d0f030515090f040201030b030c24040905070f0f0905 73
    0x42d074801c410a00ca41002842c4011301c0c241003500082c6006800d8a4460f04030001200c044c02c1c0907215a80501c03015001b140300101c288045034180c485807100c49085640c1c100842a108000404000c108181d9510303069200005000e21400307103003580d880b602d4810301800c01d400c401201030031340340180151101000c003241011846404403070b0007001220040160b4101034445266042001c00036512402c00c204040358541d0155000f14011402004840c3c038500340c090064070191124808110304010070340c0740c45141c0f41e50b20380c814070034042c10342405e541c0c4010680c2d0600326041107034011203040030840701000070001203030f214100744000c05951085081c0940358482500c1d001f001c1640f2400051a80c00d440000d841c032401014280601c0d42c0340400c5000c82c0c0300026a01280040c0c2003002040d942d00e00047c6440311350302d0045c0803a080c20705001d80520707441e50700700114010030814000003401c03031114810036129080303640b07944039405441500185075181c01c2e65000c0c140101158180f005441e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 476921061 1250 476919811 476919823
    0x6010f0603020f09030109050d02010b040b0a03020607030903290603120a110304150905031621060b0415061b080901030203061c050c1c0f0f080c1506090c0c 69
    0x1078100103030307103522480c43d1200521441c4034158040d800c04105204010001540088110312a802046038035050004c100545078541c48040e40401e9610080c0094507200d8002c1c2845403190409a004907540d6075621309601100e00b03008401d500340c000c00c820009030840c030184d02c0b0000b00c000d00260100022a25018001c1d400c8000401039079200c1c0c0f0103034140030000c9070042c000d80c8804507810204402c0081000303006000b458080c1c0554801c02c0d015040031104001a01e4009111240d0108004030341d04c0d02c65401d58058a07019120304090b407c81e22540304201100039808101840d807400d04a000c0c00e03640301c0201d6034140c9140184003601044001c025030f12510001d00e80540e50b500e40c0340000f0718039500900c4840061400c411650100580000c0c0f0315411942618801c012000c182d044034241c41102001070460301c05a40b02c1c000144904030180402880b4824003410642e0b940300c950b2405200c00010883ca00e42e42090203d0b0745041c04815500210742c0d0340c01841c0c07004141c00c654640c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 476922311 1250 476921061 476921069
    0x61b03050705070e090a060c030203150906012c0f030a0c0911120a0c0917070b03040f1407080114091c0306090f021c02040605040b0705030409020d1b0206010f 70
    0xe4085804010840c0034400754000b42504032440300242050b04034036032120344003071046a1700c03440c100b0004910780c0a0300a07a40b00340100880c0c08800001501880140c2500604c010304004268107d03050300f01201c084c0e400d10203814413044841c02c03070f403409002c0e100b0014441d0600c04d5001c41000c0c0e0000300440c0c100d5003640c441200100d0582d110860740c2c4440d0080d4101030390343d801e02200b0002a200642d108100710b1207a80d85d2518034603564901074190264105a121840c1c101510500c0082c40110084d60018400e01c000c54401407943c4800300506024414030400d9045030320b041060020900480c0000b0b030300031481e80c41c5400c011345002d40c0d40500b11484098000691400c654450080e48680010001e8030701c00d01125a12440020003580840c040507840c1800380302e00c490b4a011442601c2c2680d404c1d440e150300e840d00313240552080e600010700880d0f40784010800401c002d9881c1c005004802000880030500c4510406003d1030007862860100071903014034010040b102080403038074121 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 476923561 1250 476922311 476922317
    0x903180522020a23031b040b0d151a030f07031503110f041b12020a050f0d0e1b1201141f050d050a0302060a05061f0315031b061b03 58
    0x2003c510f9003c0c0e4032008401c00ca144c50410704980402404201e03001980701d8a4600900c1c4024064940808428000c0f400b40040388501400503948040b90743e0301001c0d1903042003402c01d0740035075640c0c402c5410a03152185921015000f2050045d00c8400900081d000551400c00b44903800c0380d01e0f00107041c0001e03484040c0c200440e0107485140b5480e204030303122107844090424007036180118040030307450306130000600c00500c1c0c0c8000c01002041a2095608050041d0384092820007040e80c000103642100c11100010790352903002d2108400104050340c0a02040350012450303040840c208042d20254a260300c201d40d0420000700c17000c001c06d81c04107a200c170364000c0c8140c1d95128602c00e110b49000c9070704029044100c0380c03180c1d000d05c9000074180700540d05c40e601711842036550783c43c94030075100c080d45c0c0703a0380090100e01c0d0310207207249181c140124480c5a03d0001584c0009172001301c0200c68542c016203c0f541c4141c2c08100103c0c1e1040b208001c6c280c01e00784540740c0c0c40000d160b440c0800300c07140701400f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 476924811 1250 476923561 476923567
    0xd0f090b0415120b3604121b0c050103230f0105010e0f090c0d0906090b04050c0a0e0103020d020d1a010503160513090c0302060c03030f01060c11130f090318052202 72
    0x9064945045209480001d40505c024501840c0910b400031407441200045588484451032100b0310004001d5207603800341164000a14000054020b085264468a040706010005414190040503202d1241c6007450b07006109500d0071002402501032021180e000d01d00b890b0044800e0749603c0012600034482d031107190355a07c11007658500510300180001c120320308195012062020b481903042c002c900a00c1990500c00001041000002c00c0d03100d40c180c801e120b280100054030b401c2d8142c9085070300181c41c2000e03000d030964078003250008021410760075611086c014401400d04005c20409462a481002481c908180000308080780b2070030701071103031910dc50365081000001c9036258000d40e40906031030344030140d8a100c10740341e07001200c207115019100f2000040151294940c04001ca412980080c101003003a82400081010640240e20042d1a540d45d082038007890301c80d1280144c000d95410321226000d00c1c100350301c001d480d0701151251400381c0301d2040c010341254a654012070304030710060b6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 476926061 1250 476924811 476924869
    0x71101090e2406040305010212060906030d1b02100c0c05060310051504080111040303030f0b06070609020a0e090c0102060901110a1107030503032401020f0d0f090b0415120b 76
    0x207051200b00007290740000d8081000000c02c0015006446083d02c4aa800d01c5565140740501250b0726007100c1040d81903210070404202c960241d54845443c0700c3c00c0d8005030b0300004c2900031828405280c010000025010061081480488207240e00507140c1182c08528504112100e060400418012144103102610700c0701c998210361812a0001c140c110002c0c841e41d400f25000d201190807511056020905003403941c4888182407045450803a4010489070401d40f40380c40d482d00030031030354404a8103c122114041004039448101c60300c107003159001000005110400241803c80140c690704c620b030b05114060604268a034184c0316102030781e107000070001c910103041610b4500c0e103a001602500000050102c2c0510080c458582c1c000305d901000141e05400c0012683c0c1c0c482103e045855800030b00c4000034485c85403a50aa240e0018a80814540c0e00d9030203400c400c3d809036000420610b406042c03001411b410900e82c20380050b030071784104010a0b40c2004181c00208080590003800840e141d122 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 476927311 1250 476926061 476926111
    0x24021b01210203011511070b030402040f0e0f010f02070f02091e0a051b0703080708060406030215070c050913060f0204090905011a0303040b0f03040f0b0408071101090e 74
    0x1c0980680140d0032400c64800c80e40c5500039402800b444d15082c1d2004000070340503004464540074400b07144002c002207442d1a400d00c0d00b6401c0a0700c12640140c459038046080e4070b207401352103101c0705004080c0c484404c500c0781c4036084407483c1000d19607080c0140440c074080340c0c40c00c5100d0041c94054500000f03503030380c154540300c9440c01e80c07000250a24890052000c00300569100612071842c100484d241d80040c902c40c2120360041120003000a4402d100041d0070340e116049554008070090401701e202600da40c0000c000d804030322610741d003081010424100340440008810000c000039038004105080c5582d400da11003000540c0545601d44800000f841040b080d41100c00900e0845000c02402e04c0600c0c14602030300c4501c0b8400804c041740f241c100360a1034003108035000c031080d42c9c000501d030400da20050156901b0040c8191245040d00b10360b40302242e0700c031004c24455445451226590000d40c980380c450b8540541c40c0c1410010600d00606c28050030764401d94105000303030301c03c01811204008074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 476928561 1250 476927311 476927327
    0x110703081806120106020d090b0d0c0e03010e150c03041a060112050708070305010b04050109091a0d081b010203041713030203071511030901050a0c0f0f0c24021b01 72
    0xc0e0342c21620014099080c2d030340c80d00225068490507820740e40d80c101e030710f5400c03520307440d444c0642007292004000c81d0300f0481480c0e014401310b13002401c00030412219580020f007100c1c22103854510301c1d0041a2220a90004513881030350002510403801d0039810944c450310810300c03640240c1d004610191000c9036940e030013240c0700008465410380c28000d40c0380108008082c09816070701c00c1c02190910001040395440700c426641603d0060790b91183c09450001e41c20058071006507002d0704081010384ea40100d0300d9160702030003414041c4108036518071010040810091180d01074030503c0c1d01c14414040002c010b48075500440030004159906c9a000307545160703903000d050b40029172501c02c070311740051150894032100c400051243c4410140b600e682c5155070302e91184449403400107204220441095004010408120713006600940d0070b5021985c80304c0c100100114160340c04010340e001000175030100340c1b080c002c062201c12021807901d030606000c4d40c0c96003448103030780c0711112551401c05145d20407d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 476929811 1250 476928561 476928607
    0xb1e060f04150c231906060305030d0203041a010501231201170d0201060b0a0819020d14091f0b030c04020d1a030d1706150c0f010c11070308 62
    0x1401e52500b0900202403c41004000c0481c1c603d01c02042c40c24a0000303144982d1124150b82c4003a203040003a80b480f144042181c2c031004c030f658590740c20010001c50000c00c00340880d845407180050f520700349400e00354080c00d030300300ea5034400c00700380d0005100e40d90307101c0c1e202081c07401000a40781d0380e100c1a144946441c01007242c5491002e402100020340d0b05003104407022050344080507140840c01c2100c0480c2603403103601034075404880801c6081140e51181600f0750f8821030191804a183c40340710000f00999200208c412a840c0e11615240201003000102c1d90304844070f10f000340720340c818105c1c1c44140c20008404810044c0c4e9584000369107a2800e0048060043d0020002c540d14480b6a50350b030010076803c4030008a07901800940c0101d030400040761035025520303440703001610400c2c505200b5603640042040e41c005484100480010740c1010207030076502c0041000c0d06070303204080e003c0d41c215001e00d01e1181c100700501400d80b6081030049145030541c1c0d00700e00d41c25620b170300364a0022030103400c43c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 476931061 1250 476929811 476929829
    0x3090f0d08030a061a071a061207080c1e09160203090d0305030a110f0f0703030b060301081e19021314090a0c050405070e100e0909100b1e060f04 64
    0x803c0080d1a500c03548500c045c0e07401a081481c1d665030340580d10300540140d400041c003d40c0001a04591980b4103000140c0c0840b000300094444004071034491f003004265403080a003079200c1c00d100b6055280888000100b24401490106010740f004006948001d01401428154441c042c000008a10901c11101c07d02c101502206400b0400d00e03004009034801c94104c140a0f00e4009440a040429400c940381c101d802d040450030940c01002d4942547d000c582c00301c090540d102e2200b1040d48604020314000d0071864003801c480401000e00c0703044028041e0400c10142c022a03204803044407907050030f0749459011380b0b0441d014407071041c1146c020f2441e011507624200c00c2e0001c009800c0400204000c102d40b05d28090406903079103900b030000742d8005481c0e032004a80d18400d441c0d540d0426003c4525038820929004003000900d0005c20424071040d60216299000304015801a40040c041d00d41c0f980e00c1601c400d2050750318903000c40c00c020302c0c82510502c100000900b2810984a0b40d00b03490207841802 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 476932311 1250 476931061 476931067
    0x512070807022a042406050d020c1911040905101d010207060c020f0601050d062a030b011107051320040e010513091709120613050f0a0503090f0d08 65
    0x82069000d1a0031101c28070030b90611140354560300c072000003200007014585002030b911b400d01400f5502600004904420154240225030001500304103403030410102c100351100300003442c01c0c540c7c000303000c1252481c091070400340d00c4e60000e0700c0050007281e12a02c904000405d41364441101040b021540170440d1158008220541800707a00da001d044800c20a408640000192600c0140c8401d030034858903a0120341103481c440410596085500300c000304010a542105070000078000c50f65803803a2010000f5a1131240c1426560882125100d81c0110b800a0481616000014211544043c880c030803c5894840301c4030400310030308148000c01f6014a082e030b165030301e40100d00c0001d5000d03c102407003225043d5140c2d01000c610701c40c0f5500c4c13541102001c1c03081d0480d5451010154000c0c030082d074202d0107011202c002c8030403d00055004621b05041c08141c00442d007002c17458500b03a91103451035600158440e50004030008101c801403402611050410400ca00002c0ea0000c900c200c00f8107407071800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 476933561 1250 476932311 476932363
    0x11070c050f0a081b0a0f0608070c08091e04050a021204140109020306040f1209082e021605010c11210d050f07020d051804021803030a020d030c051207080702 69
    0x100000801c118010f0761440c80300e40c0e55020446c030074a4540b0071080031654140c08104003074420304070031204500681c10303145050100004110302c11070701d0860413010440301d0482c600528090195a410141d80302e000e44c06d0018a50000c01c02941c041d1005041044455071541680029004003130301c030742c000381a0b44561400c0d04020468010070801102c05c00c0003c0c0d00b88220900450011041c0c40742c0070300a101e20184400d1080240201c007c0c1c6040180d0125450065810706000804000000c00e0603a20000d060389016400d44569442c13040500603003503954400060300007071201c2e0040300c518a0b80c0c0c0a90ba452001410740c8108801c45003100e060404000048100007c0ca41c0540d40903405c40780c030812000c40c00c40d142d01500c1d02d89040c2035001411a07a481c54560050403008942d041803880366551070000918540c42500c202e40581c01074035114201603054030480303421048134103256250030301c080b1640c84c8411000f020942823000b5030010030030702c2c1e00c03c108030f0b0795880320350303000f60141584 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 476934811 1250 476933561 476933593
    0x140f03030a0c140a120b040f020909150904080d0e01150524030a020c031314091b030103030c0f060c2102070c0b03040519030c0611070c050f0a08 64
    0x1200c4040c8528100780c124952640f088565200c0300740f22421190508001e01c10807650b03c03600701564180700351160040a1590b503544208520300350380c42801aa00c00c01e0406010345010001e002d2060404004407488440c3c070380f140255070055025644a65401c9480740344401440c2c2003600040c190b1a00c1c0360040c6d481e14581c2c1c400c054440c00c80e5000249010303401d070369054194003100c0700102201440482d06151254001d020010342200176207081c1604400c0b4180301c51180d43c0290130881d005128100c80d801d1007044c0540200c10072800d030403106000d428015480c8010310001701009944410401440700e10f400c4850341d142d1100b400d201152508800404040b0b5034103482c1a6000306042c2c030004c00c20070348221400d0642c00382d03240c9003403403a050070002d198100400513250b41c0510580c3d54100000180a1324845200ea100c00030106024140b030021128080900d94501504101400204c1ca8201c488001c66404440300d0b5192000d560200c0ca654010780d100240901c194401c0ca030840c81 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 476936061 1250 476934811 476934817
    0xa050115180c021b0d02120607031107051507030f18050705040b01090e1f094b150305280201091401090b04080a0201020d0305090d0c140f03 62
    0x303440362000200d031207140300c50044841e150050409603124202100070700c4015609904540002840b10b0019520368000c20559111000025503e802c20b100700800c103501841482ca85003181d088403401c1070400d584d41c555840c80083d0385c1e0503c00344840010041c51094201600c0300328120414004480c8130709042d024400201d408032041d010b500400f08950600744241e6500f584141d44115030749151195520402c030003d440700381ea05203100c5001c64207003090490030006101461001a500003504505d846250310b14201800c902c06104414644119491700004c1c480e030b04024070141c00002d5103400c1e0042c519500031810a00380312030300000384a404140d10741119030240503000c07486c180b00075000072040d12030030083c082011043c050004070783c92204d101c00000d040c10156001900c43c000150a070708035038488012a481031000c07174115603041c4042c0c80e850086090900c500d04260700c0b0107441d03900c80b0086408110240c40010207202001c4240588403800d103040e11042a03402421a07100d038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 476937311 1250 476936061 476936069
    0xa020307020414070c0b0411060304081b0a03092112020c030606040b0315181501151d01051804020c03040f0f05030703060911370b030112050a050115 66
    0xb81c94038100400350119081168416130650b0344903d806400c40d070314000f00b150040c000340c560340e0480e4059005034031088025030045000f4105a92038140034600e0f200150100c4038200080c0d008034021600107a0030901d0082910440c0c0001d98140b19030f000c40840b10000940007030002030319903100d1000c0341d4012881c40345210042d000e0350312650360394050009542006a0294041c1d0200c41510040c07250340900c185c0001d4403a00b5418540b40001a042c078200b148614801e00310051401040450766400032102880320a00f824401541c042d151600300c0701140b10a00e0620000190040f40303401400c10f624038150004004546500ca000109981c0f030700a409001903222403900c4c04146a004081c1450840d40024014500d050079540c0b04070191100d44030444119a51455020380c940d2102c6440001da124401d5a104602c80500299441c43c6030420081801e140d802c0c0c08e20191030070b1000c0700c5c1952000080c203035079950203180c0546404981d000140c2306e17518091400301400c1d0f100c07003510304030b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 476938561 1250 476937311 476937319
    0x1812211803030313031b0b0114010e0301140103020f030a081c051e01290a08061306050a03080a02031207050d1a06030a0f061d0a0c0305010302030a0b0901060b0a02030702 75
    0xc0410018140d03684000c0e2180326251000394031500c0060304c81c4011500000700a525850b0700c10b4103a42d00118410f0a0f002225a00e080c88011003565a012003001c100700c1e030481c000d12101029115403003011506000280c0541c5400303a100c025030724104100900c80341d000804036911161524081c0c6460401c15802442070300b46004202c11851030b141100c0201c252a4002d4103030b034078060151502e448000301da00c2c031f480c003002404022203c13010302a0180c3c1c200307034440b203d251510304104290110120800e080c424a4000188541d031560700c400f005595002d621540d40f0022a40f003030386140501184400380440f4801004035095000c0082d08900300580c50501074104009020704c00c0c1d0b0240340c1d516802c1a004e00c000f810182a0350000c1300300342c200b1480002c446407204a20103410301e40103d42017411044000740202c0c440d41344078104002c03010385000c20039941107a0010b41c079151091000340124400c1808280301c4c140030346c00140103040002107503980350360901d80030751203400103041a0700c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 476939811 1250 476938561 476938597
    0x90e07050301061728020301090e06161824020601050a0f0608041a0103120206090109121d10030617010c050405131b080f070206090d1209020406030c050312181221 72
    0x6510005140350003007203a50001ccc4240500f800040b07031400340300004400503a210020000e02962119080c024502c00800151804400c41c80040c1c648601070b0f00860098040240801c01807446021213405c1d2203061415900c0754442e402c01104280703201c02c2c0c000100014074000003c01004244000500c1c2040d0250388056036019106801c9901001000e40000342e69406080340d14466110031100d4501c031341c8240ca14080c602c000c130381500c04021100d80800c3d5907c0303061203000000b42600b020090b001f8000c0c001c0001044008000c2d0295100b818002c003105c1500700c986581540103000402a080711b841c6008004040043c80c100040e00c00140e9020044003140f9078910200d86039106100c140c0c01815100b181d02811540a00c18009408400f81da81d4035002c0181d4490280340c0c010360050010b0080399043c1000c0504040e0034041180503144c0803c0303543c0d20128003070b24160720325a04030b50b40d001407030070455450f0404035002181c465040050381459030542180014180c40c440320758021b51 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 476941061 1250 476939811 476939831
    0x4080c0913022b0c03030e040f090c091d10020406030e0f0705090a090605131101020f2508010e0607030513020105030610050f030106090e0705030106172802030109 72
    0x400e007840940069002888860f260341080c48a20740d1900e03044003100c150402d402c450303d840701c1510003074000b2070024515542c6030380c441c40d050140d07041c91300c02d585041050034000d650b0401d440c02544201400d007a100c1224605141c03121b1a00f500b003410081c20b9407100d2a50b000180025070141c020280407074644998198294400201140300318031550040c5045070800c010070a0620000301580d1a241e1200010400542e560203814001d0340d16520303504040e042860200d01038460810414115805044101002070000403d00d1310078100c1883e84134015207001484c4007090840d00900d440350b0802c00111580c4000140040c400c14595900b048140c80381c00008400714072401001e1700003001400400e81c9407a0142101c12542c0356402e00c00c1c03a0400e2071690200c00d0b0001da0219011441c40141000f1107108006950b078040c006e894102d2442d030400c08007401c40d10742d03082600c21403030505000852885407155610f90b4000a803101803041004000010042e48c000d024454890341800c10002c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 476942311 1250 476941061 476941081
    0x1611030102070f03021501120b060f030322150c03020d0e13110a1d0f01080a1407210b0a060f1413050a0801090209060d060603020a030c0305190c05060d020f04080c09 73
    0x1c403c65509c02d4050285448150400c4124441d04d1815a0305000400c200c2001580985030b2070040c0e0740311441c04a2007458040c19061040c412402c0c0c1061102840000c40000e5020a604000c540c907130a080b01060060301c00309007805000c6040c1d403200d514041d104980303080d105c00541550001640e5155000c0300960326140881045034925800c99045040e00d001580101c19003035100c590207200040c484215851904800f10688104003c40c08032420340581e40890021904aa4a00401031141007190f5000c60000081e92252504000076006940001c611441c2c1f40a0031004007001540c5480010900c8618400f0502c1030700e100b003000720070000305014103001e000c3c8850340060044119079a100e00f400807943c5003410481e405a0346031004801030b511460500085c45c0240d45250800d800c6252042c68414000008445400c3d8900e0303890009520788030f18015139506541e01da84881d86028401c0203406440b087d500482c40103d004a42440006202500b000c1e040b03550444d103407103c070120 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 476943561 1250 476942311 476942339
    0x1020d0614030106061209030c1b0303020609010504120e011701080115081203041b0806070305040c12020901150201060906090f0501060f120b0a0e070806030d051611030102070f03021501 82
    0x45c4040f80801620151102e02ca50000c1001030103818030400300302d0266a0300110469500d0342c40000c6610441c05d0050545c10082140d110240f50004c000e40c1c100b50b00c030400d1300500310070040e04100c900702d000103142c2d202d203541040c0300072003e042c40d40c41c0d61a800694081e2800c1201900c03030719402c41d40011140e10005079090801d001c0800c06145407100e0b1981d0340540d0501c5001d1120501d4800c2c0058050420800c242c0714101640c1d000620f03017403a1a1400d0498603a60054103200d05030307031072100566075100705a811101000c0000d004041202d10a0740500340c56808003c0092030a040001c0c81c4200c1e17040172008180c03405080195a0306c68006841818001d43c052001403080740c81d01c10031078142da000c81d6042c0c9000b002c2034032555a1381505000f02e1030485035200001c001605025481c00c4c01c01c402d000a06030760070300509154502c0e9034141c1424503070402401c0040941c030139406e03c0c0c5003075049540d050b410181c5126040c00c642000382d51541c201001c858000b07690800002c03030150001030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 476944811 1250 476943561 476943569
    0x2070f06050610140d050901060302150a03060b030c0a080712090f020307080d05041202180a0b040606030501080c012604080309191a0415020d23090c011b020301020d0614030106 78
    0x11541051445d2442c0c0e0300400c0d0080103c8074541d83c416010000d42d03204032070510200c800d8071100e9992882c007200241941c18130f0b802550000020300502142c4ca03403140688100307516901d00f0390b0b8550343d003810868204c003103205204030040c50811441c0620030455680a8014000c0d8111100c843c1e482003c580da5028440c166400140e040c0814484200540e00b4860340a0004040ea8003140741e180302c81d4206401903400310030306a99102401481d0416001d8400201414101044190315040760240c540c030b021501036040020f154070b10140c041c440313030f00c44040b0506200b080d11245450b20380000c1c0e40c0e20a440408091003880800d104d0782d0343c4405005003c941c031030108981d6103150110804a035002610407280350902111419106289201070440200c00010100b05e203007040340354020300e0011540b0004c1d034990903810041c1c181400140e1007045102031030031403445880036861051603040c100e070007541540006100c1403140c0c40b0380c10207000e80d401050018481e03815881014200c86051007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 476946061 1250 476944811 476944847
    0x614090705010f11070e0a0b0a0f051908121213230f010c031a010e06070209060307030b13031b0f11010201021b07030521070206030a02070f06050610 66
    0x14051100c2d512488600d501414a0304010643c084400d1301c1d2418001d064120500c850b0243c01007141150940c090316107036110989070845d00301d080a012043c4036450340510344c0214043d0846a43c1024142e100754014410002590352282c4901c03d1896280d01c0300414406545081011801400480c40241c01546e40906107800c0ca452280242141d07810b4034000b002503025070080d0b03098221080c003900c141807a19540000e151000010000200b410a00700f2a0401500280385202500c030071080b00d4035036404071881c400542d01e44c07001a24000c455000100349a42d40401d0121003015203c00b030302c1c2c1034841d489032a030b084a2046101d00c1680700110141030240c80f800c0100100d0749500142c1034140301840054070380f1400307013203001000f0410344a1100c4da6004c00d004209106040c84818000110366400c8103001c020b01c650b1000d540103508000c5d1140d640040420540000383d41142c0c04030380d000f070482e0721000e12420442e009180840341280210030503081c0c80c1515206000e038265882e0258 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 476947311 1250 476946061 476946073
    0x60323010510090816030605091612061b121802030303040209040501061715150102030a08090a150b040b1903350307090b0f0f09180702010603061409 66
    0x90308002d02d904440c2041070a01801080c00300c2d0031481407151103411946105c1d078610301c80c690301c0c01c03000f2141d000f020b8800c1c81d04400400e18441404200f41801c803a20310300200300505642c00c28000401da103485d0346100028282d407000c0c1d0260825001d42c14240ba03420708100a42e440650071030380404210b0001d5254000700001401450481e0b6a1a00640a040000758558942403ca0041c01c4a1102d005450380554195031685241c85c182d940e10807090a840c00b030302502180080e59134003030b0210751000d10040d00d0001c2d1405000b00b145a034000c0e08032148415035186e40300c0000c02003c0201045018a0802240b400141804203010400c3e01c42c0d4241450302601e5520f4590100030703440d081040408401540f14101e03002203a82c410300c42c6450000c00d0f601d00b4071020140c1401b48503844501d200605028000001200d01e090394141c0000c50318031070340d5550b900000b808a0340c1011050b02020b001a060005c03041d030541c0448250780c4120b80403c01e05d12844151030810340704031034488865104d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 476948561 1250 476947311 476947319
    0x9060e0d0c0e10050303030118270b090f0a0606080105130201141b0312090609060129130303030f0b0603090c150c01090b06090a050f0703020a021207080406032301 72
    0x1510340180c1c00212103d0310201c8540710400a41150700030392102840c080c488c032002c10001414410502c0c0f05c092001d02c492000c62181036880b048924010251583c1e610500007031020704248601d550701e02202c400e48110001d01d1a004e0003c00d039074012038049618280018600f144218000d40c1810380507141c031b500c001c141c00c95403030461b4050300c07001c0184da144651181500c8810009070648604191408a80f407030076940035440c110000b094400340f03900140040001984d5120382e551142039007039101c802d03021707601403560642c41030640503880e480b0180400800d255041c1d000c0c54002030740c4d49051181c4608941003092030b0000b40d503503a0385500001d03045000c1c1c0c07902c09818000d002041401ca41000720f2000000e08480001c00280c810100030b200300403040c81c0c030411596002c0d003011000c110608010841030043da0703006200c403050580c00a4007400482c020000000c051102400c80d6503203412600d8200c03ca41c104d4420040402c2c1400c5e02e02c0c000400a010000e00843c0720103105440f81c0c60 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 476949811 1250 476948561 476948579
    0x20901140d06050d060b090702070311060a030b120706020601090b1e0a0f080a060507030c080f280e06060103061505030a0603080301090b010e240f040801020a09060e0d0c 75
    0x2180c01c5980c002e58903840061152905030100ca00580030741d0740010900d2100302801110b40009000d9421904840f4040c0006030803100c01859500003a25259120460004190000c1070381240666101840381c0b20361032044000166001966113660a4440c40c0c0d03a80c9003814291070078801d6596001c0d03d84c1c01e400d21052000461402d0028004202959081e5508150303035034190325800800a80e0070103c82d04050140f14003038541c100d1100d1034104242030b41c1034001869050b02802c02c00c46030ba5010040f83ca0b4168004003100d43c051012101e06800e010048010000e2000c0782e202d4649020b0600065040c2d806032103050110351682d0100050210800003c8556031320080603c80856641d0a01002007103a00c1c000e980640b2641400091281100c0005804c00051486041c8188507101071082c0c50014119440440c1106500c0c2d203442d64140c405203201801103400501040d0f1010505c016580e0b44001d003801220f1740d81d00c403144a6880213080c000c4c2c0065040c00903001200309c0c00c0400203441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 476951061 1250 476949811 476949817
    0x703080406060905091e030f0d1e050a0e06100303020715050706180203011a061801020a14071505030108070e15030d23032208071b150302090114 64
    0x88541d4000828070b44840310034045490550741a03020394000c1010076407803c1b418054a00c5481d0b08001181800040140d20485100314200d140c0201c3c4c807803940c0c4480c8031075440c0300507129084690034040c82ca05004600010003502010407503501c503100120710744550301440b50003a00d405501400f00a81400050745058200f804803008000d0b080100300c004c1030f800d20a004020901441800d140c0096004160039a07441003121074040c0450700520325281c0d60b0004490016000100d520580080040143c1c02c220700303550060300340084c80740c0c907841421000c205841980c0d045100505030f4804e042c81114075000900690401740d010010a02c200f0840c1d1600c26031088a00c049102000648800b0a041a044164500201c0c181c01c0c00440381d10070321403c007031030301e040044980d045240032001d102e03d0005005140003400d03038a48484c3c007840b00210491701c11980160014070189240e405100002000340300d0700c0c3c84442070708049121140721b4022a82020b50503524500c02000400724005503074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 476952311 1250 476951061 476951063
    0x10050307020a12023a11031201080307060c2c0a03060903090501080c280338040216330e100504020a06112803020c031207030804 57
    0x4440c4040d51000141181d40a04449205a01401300140308503405003174181e2880b041144030140c1108031403c6041c2004010710030f0480e151170f85610b54100e580906500c515202004021946400842d03a41e10010080c07051600c118010410010854001c90310704007507902d17001c01c001e500c4441404030070340110684200305c0002c0500c0a010741c1c0e5698081104c400b0f207411404101c003030104000741d603080b041e455881802158940c3c0303400e924102040c485098480501480e084c000c0075140c000c2c0c03099102420300010303c0b4408200280611003076020000c0f000b100401a07029410b041014100741c02520304014400c400401e940c04140e5a141e0070b9210b5111614205154504410348260b1404640b00c6000c0c4c90100020010700e409800ea081c031600325641390080f03081c5418040140c40c5c45c101407048a210345000c044825230b240025007002401c0600c0300710f1400c181c15481d03407000e5a1341c0d908180c520030f80031124141e1422003811340b81c1c00142a6010303003901c01c0c800c14021a01031201c8a5200f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 476953561 1250 476952311 476952313
    0x7030c0c080c060d0b130212040b1b0f030a1d030d050c07110d030e062b0207082b020d0b0913030203030a090507170303090f070e061c0c14030c0105091005030702 71
    0x910006c0800200720f8012030720305001d04400e4424001401042c1103200c1e00400200510a90f01917803050180142c030071401c001d94013a03400000100b242c00305601c8104118600358100308412006207040383e0b6034000c1840c55400c1c0d8a41804200013940c00c00c00c0300c40190f03200c2d0300b036100c03607090710204140b00c40300320000d400303120070070a001209580340d42c024001201d810080704139006200d2200206140d2050080b0300b521f02c10486a00800d03680030a6424009440840c50f4680e02408001064501900d01d40c1c0c0b425030011803018000b203001e03001014150002d0f503821003070350365580034032919040d0030b40040c0c0584c000300003040c01302a8640040300454061001c0b2180280d82d01c2d50403000e07240103c403501054001206104400000703003d041140100302000386200c0d402c01092140210014010700e1154600d9040400103030306c00080701c000940c00071f074601d070004d580721040d5200c60742c2c01008600c0790140401c2c0100301c1d800303081550500070001d0704400369514101d40c10b40321035101920750415 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 476954811 1250 476953561 476953579
    0x3020f061501120f110c010b0105070b16050c0129040c0918090b010902040608060d110f1f0210060503031614030702090108030d0c0908190305040b07030c0c080c060d0b 74
    0x4405a5004030044821400180da03903c0100c0b20246e8216117001443c1e40c10000c1c104400404520700400b020b070071102080c136404d140213810400347d6440c4a5142c44c1e1806500300100c0503a980315694131005c102401441024080b500c010030881210030720f44065010543c403600612804448004000c6071004411000070200d0b007545030710780d91220036817000060a0b0005401c0c40300c5a1f0116045802c200709507010010f9523060b68071184440814465580a08201540d00700c45990702020072000310a0502284200000b20000a4440350752205503080ba80c10035000040e24240081140d010301e5080038035070b00544083e034035060704100c41a03019100b480140001c1c80940d8074103030a5402040c050004603aa000714000d03250546103468012000d2080301d11082015400100e1500186402e600c581025030065107810342d080c0c0a50b0700200540302e800300d050010181c00074152021107010300f0840f0f8405580d90b8400d9a01c2062034100e5400520070b000c83d060821080e00300020040d0000e101843c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 476956061 1250 476954811 476954831
    0x12250b0c0304091a0a0b0d11070623010609050f06071205070b150d080a02210a1805030316050f0102032403011a0d0c05060c0a03020f06150112 63
    0x14a50044410310505810001d810400c06456108224545460b40003544040d6101000250017000502c24809a00c0303000400e0fa080d140035070702064007030550415007030b241c07003150500c50b00034644d680f01e0580f00c0707811902404204841590b00c0c0e0480341c0070380e0340320845424003041c0b16006044a003099001013040c40300400264080031842204030706c0c0d54829455402038100183c4070381c009000280900c54070143c046a6403241341d000c0c40140c0d04050700a590b941d41500892030034034021307030301002a0382e9403120302200e030310b81c400605140c802c5070b4031505001d5070068815840c3d00d8a2140e01e030f15a008110400000c5082848880b656006005942023000c3c501e411500b60781c011202444200d030803140e05400020700c9410000b91701c40580080107012200040c50914071201403020f4840d0b42e0041c4d00e002008200d0100304068080a028503859030034907400c0f2503985c030100c8011030150140c00386241c101a800580148500b1402e2504034428040d90300558510300000401074038507441d400450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 476957311 1250 476956061 476956079
    0xd0b06090901030308220c0b070201056642070f0503060607050102040e0a06050d0f06110904090302070f150c02040213080604201225 59
    0x42e0003035001c0d4903981d259161820110360100d0f501000d041c2c20081c02c3c05c0110118004020709003d5502826880d5074405507400107958038001c0462100710400d203406600101604211b2140d000e0009040c03c482c8100005450030a607000c4c4500480455498034560804c000e100841c00703d4881d50070191103001e40d044c01104911000d00302c50505d641d45002c0314150142a408146016002440c0c46100030306107842d0080082920214840810402002107011a6200030880c0c1030135510200843d0ba4a949807181d4565010071a07282c00c4092410030300007500d0924480e50742e6226032101c0c2c0c41d400c001480d564040201080d2413100b02000c0700f400021006d031114414007404038000e4000308016441e0160940c0031992603000036541000b03032810760203069000120003400541c1118056210701c0300520000c0540007940c044003040c0709000501041c00524208030b4400d1103aa01d4050301c04200005001402140d1940c103183c81e071002d003454242e0220701d00d800740c5504507186c8015060313541d44209 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 476958561 1250 476957311 476957329
    0xc0d0b03070608100b0414120f0703030c02120307050d0302070f020405010323010c0504051e03070b1e2503020c060a0f02100b060708030702070302090a1b02120d0b0609 74
    0x440104110b40c0038015a8084404140c0051400c00c5010f89401d08100b00300e2241d40308820a24003031482114541548c1e40d0a2010103420304140341283d03040d03603880c28000d01403e94607005038081c5075041480c0c0c01c03006000c005c440700960000c004200503480c22100710003c0d4131500c0295a1802c1e40055000181d459000302802103004285e50f012500008000d418544140c0100c100580e04d05400c040c1e8440c2c100c8181c9085030b20454140c1c2608181e40944051036140c0600070398103000b450404030340e540c524005030411981840141000a1039407661461038481c1c3c007910300b6074001d0704034018030b4404546e184461640c400c0c410b503080c603040007003c28003d41264450201190207078400842d210390410003582880744100040c000800c03c000895100d1050000150103010000f0004807014002c0040000841d0f018016421503d0f201410000400ba45000c1c0c0885203003034100d0f803401500c001034441030b1412142d8130624001c0c446145900034181c6805060b00124207001d1101c15039280000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 476959811 1250 476958561 476958569
    0x105210a14061003030f210222060203040b07080c030c0106080309010e040b0901120804080714130515060a121a030106060f020601060806010905120f0105010b0705060c0d0b0307 78
    0x100d80e00841c0d00340100760a141c8000c012469203c150f49041010a6008910b1010410282400005900c1040150030030803054103004004500010711f0356a0a003211610310b00200c8208804c201003611000304a8070392142d03204020880c0c901b44400b03030100349040001c0480f4040401105e2515200b0312515094940d05ea004803425040810040300e6540c1050300c454000702c0440c1c042009002d0f4000041d000d05041c05494920300c0180412000c109450b0112400381550342c0132a4091683e428a41120100c0d8495060090382d90f50810208241701e4050702e400360f0505000c425010010009000c02c80d0810442d100400080c90388a440d8a805882500c03d007140c2e0280c1c40000b440076205050a40c0d034150b000350104410b4400c1f10035400d034049205d9054440b280343c03102d01610b802004951035640d6820055000c0401c0400c5041c6800c001840307480c4100000080c001a80c1c4c82c034540040340202c00c00907040b90000310002d83c1223074080d0002c2003580002c08001840041203000b10f031900e82c0c0f07500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 476961061 1250 476959811 476959823
    0x6040c091a010c12020312101d22051006030c0317030403050d0c090b030109020703030606020c030a141009050a0618020105070209090a0813090b06070b0105210a 71
    0x90280a020020301800d140069003a000740c000c1414180000c10a9880300805446840560642c080841c0309201302d50405100e01980d910328148003000d207008115078402e104911008440c1c011854031206042441640c0000b044000c003c40550100702c50018402c0440f4103001d4204ad10107030240a02c01c2c4030182d4020006c0d010014150301e40952100c03d818400f84c0c1d100b00900c10880042c1c0d11008440c0c040b0742c0c1101c04180360207280c000b520500c41d503402070030300f42034003000100303452030705602801e262402030380c0134012150f1301e01f002e07601c40901076119130300f43c0c100d00e0341030000c44c0314030b00d040402c082c842c0d046035103031a40c8810308070454001210485150304554403c0d8140a040d0040400702c461840190070b99900070350010b0118400c4184c0240546203580c00651808410310100e0005074021a02c00e07a1240c6898551910314068022114401c0c43d1400c50405402c054040e140001c2e40449005c0b210307400c10b000c0017070400c084414200b00790b140d00220010b00350180142540d26200b15 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 476962311 1250 476961061 476961083
    0x80402090613020a1d0315060d060216030c020f09070206061203090303040324060b070210020a0b040602090406080c210703050706081024030b1503040b01030c0609080304050f0103020702030604 85
    0x51420609031550031081d1b4407980c0409030505e5075012110240d0741020044030200d1500d003203841c1c00c0001c1d00a103603132140d030081514a4602810382000d151404148200c503403015001d229001c00485040c1555a600103902000004640703080481403191024440e0080f41e0078541400d000910755403040d00219020290300e2140c41c20105680e01407500e0f41c020b03200a00045040c01400d00700e600495801030b11407407122521108290003804000e0850b90440e51000311442c140c20290081d60000c00420700461903e000040d000d4004101c1407464100100b604034403e0164640ca4200020204d220310a40078410300000090300c20070000c002044262103074145d524042070304042c3c0c900a0351211160200699005000c0d2074145152110640d540c10001008650742010034280c000700080319808201c0003040c4024080e00c1a0358604881c803450086414075101c09085482750104d100d84110790780180000d22803890300c1101d4105426062500608290303541c0c0010b407400c5000d640940c0c92054074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 476963561 1250 476962311 476962337
    0x605030a0f0203011b080c0a0504030f20040209091306060b130807090e03070321020d02040f061115070e040203011403060106210b1f08091c080402090613020a 70
    0xa01643c080178191070907100c203030b007600c080c09081d035100100880411070740090f0307800c1c50500403c1907074040c54001c040066000003e10b0a54445a440c00403240c00070340e00c50715001c2c240f810740215200a04060311045050f00c851a00100c11203143d01d040b1241526a0310100b44000e110303020305a50402001440340451610a0302802c0c00a03036002042d00074209054444d4100e0000103d07898154185092003020104074800e00c0d044001c400b03074491440c000900c0c2c141c2550340d0b802800640302d08601e103091380ea9a0306000c2d035074038130310241c003074a00c1c0c0000f00f64060090840000a9004040b802c140b80c115030800c000800f2640700343c001004102c2410150b0b21141420811035014040e40d007801c00c203001104c11070407102802c21000036112511071203141c1c0300303441c2c4003ca000400c000745050b000b58441a18040d10702d110860318080d0921620300344801d50300001e0f19102620409850f00826916070780c080c8001403900030100c039040542c03e41c020062181030710040c180c0480b0b41da1070020141c40c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 476964811 1250 476963561 476963563
    0x271f111213060b09040c12050c041d010e06100b0a020f03031801200414030705030d1e030603021003020306060c0607110f1609091509120908060709030b06040605030a0f0203 76
    0x243c02e40841c000ea1002c01000001a10025500250b8010080020340340080e03241140c0b802a1301c0712440d030098101214021003006512034450806c0d4400c0092207045400c650080e03485034101c980101c206102081041072910a500400e403481507441624856181505101e1450380252111400e1080498400c1400300080c413591300340e640c002c4035003800c0b8072884020101d2401030b03010358034162002500d40d040c581c0d0700b000100014a009801d45a05038030440c4082c20300517041240a03d0812070317603980b01c2954864850481641d030300070920310055800c600c00b10000d4000500443c3c100900f0000c0110301e280c10805223114071107941e41d0b4072007500c81c8265141491000f483c424120b603c4142c249001c800d00d840d401c000c1e92114240040c884219081010800228605050180b417030300760780c0e8050101c51040140c00c0b0b207064484281c460b540740d00e02d5680303c0c2c046070203000254885c20184009640c4d10f001c2d40d0480c40045c404a003140c1c031800020b0818000410456002c19800744500c11410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 476966061 1250 476964811 476964821
    0x3101e0e0102071110020115030609030e0a0b340506180a021305041a070f020106060f1b03090902180f01030510060e0a030605271f11121306 62
    0xc410300950030460a565141d50101810103214425159284103d6881d031003540500d541105074800c41152503604e003003101c01041010826800a904a81c8000305402e20844074001c60795042140e51610707421901104c2c50325410180300702403400041c0b0107404102001d1078068106c0c020f40141006041203494041134070401d4840003103581000c0c09110140c1d54000d10001015194400410281e03070b2803821403444d00034110700c4be81d05031107241805a1194880620300c92035504e41c00800c20f113501c84000f0340e031001c0715090580000380b200c0b50507440403c0140f4554042440380c1001202c0790f417980d60b060142d0708980300c2280d03903805061910400e8a4241d4282001032400e003010081c41c240328100300a60001402524203110070f4601d40640d41c0c841d5010f04c401180c01041c01c10140c1482415005003008c404c05005800c40c441c0000d410700360002c0b801c6201c070a003515060300d44002203d5220040d00d44d48000e40c101041c180408407002c0301c0e07105818415154200d0a50083c842480d083c02120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 476967311 1250 476966061 476966081
    0x10082505131a0f1c020a1701060c08180f031905060a090c03081e031e06040c0509010e04020c15040b090a0b04060515040c0509131e02070203101e 64
    0x24011003140680754002d801101c410901d5150256584d24044440004101428101080c2544000340801c800366001c14410010110320030130b4641660303540360441e4650900c0c800074240e22000c005038810744503600e10030030325100c01610500308c540891002078201003154900c42c2800c1156a5900b0401c41c1c140700076075215804090030404040701d500c9099501c0f401c0d002c02000960300044882006201d006100500c0c0c1542c20425524900240c420800108001d20f03caa9080c004020030300e00d1503e8060025062034135a100707030070070007140011642e00408050517600b0690800c00384200304010f02031041400380802c8622440c0c1000e00d404411113074000c1294105400503144035000881c000700080d0000d421440124094842c803038021612650300032100d5005181c440c1e600c04082d0090007408014408554600201c2d0b84000c007d0b050715400c401561500b1000790503070304a192280e026000b03041c0007070103d0b290b034000d59000f80b0880f03100361216035403900c1884603100d14501da406142c1840c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 476968561 1250 476967311 476967329
    0x1805120406020115030515070c06151d0f04060b0a12110916050a0e040e0a03020a14010b0307050910030818030d030902130b041107080310050a051008250513 69
    0x1140b85848081c7c0f5800301d070141c2144d03a449000801c4000d4070a415050019130480c20410440c101e00303203102c5c000501ea00c10401d9800c155078044c00180101c0000e58800e11808401070a1a5100d5444200804003800600c2d80030241003400700704261401202e20000f0311918020b490198441c0411101090041400c0401c980d8496103841c05503105007521070940c5182407541441107100000b41c0078100e81001d004461143c500403a0a246d4001100c1c02007500454401040c0414296081d09881c1e50b00e1610760907903c091402c02643c202809119807007108034070389404150300d07940c036010150f000c2d80c900c6003142d55100d1800418502400f50060070803031070504214240841d0302090750703250140641703c140c59540c074011813140c070b1315005800310440c1d200c0c41c1656030343e1520b080c0d5425081038030350008a04a9010109150501c2070522050700da00810301d0700d0f1480e181c0401c880f0f100c001080c10305540b000a09090742400d1102c10290580060f86400b5200ca0002c0b119200b0008203074000454 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 476969811 1250 476968561 476968601
    0x3041e060906080a06270f0204050a031415130302070f061b0204090b0108070611280309030501051305010f0606050d020a02030c071215060803090418051204060201 72
    0x902500800c100c1c08950071800d007070100d903075550760040c01484503a000380400e400c0d10a42c1c1c48034240140c40c5548401d0f02d40c404000170b0380e03010104012801240961038001000b030b2003c1c00820b20307050360308000c151210211808410701c007010a650144c290b0388a2030050315641c40000b0587c05005483c050495192120105850504002d1410442984024410752108005025074036940c000c041d0094201d085c0402c01d5031341c1d0341101e039504550700c20140000c0e6400c3c002200c2103008102400700c42001c03002c0044162034000701440c04503054034220180310081c640000000c1080c0222403046001443c07a0503220100d09080f42074500c0503410350348092400d0400c6c07150700c0d00301c0c0603101030350712041d4016260410f00c1c806a00c0e40c8036124040038039100303d9000146080b0b0007000a0402442000f148140f1410301c242802070f2401401024030942040c02445002e06140c0c0c080d107031075451001710710039500c503d4442c07600303098070086000203036040000e0900c0245d4090040b0004201d20481e0402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 476971061 1250 476969811 476969819
    0xd0b0a082b080103020d0f050f06090f010212010303050f0417010b01030c020f15071218030212030f040209040c050d030806010206070f08010b1b030a0f02071d04060e01020d0c0203041e 81
    0x4900341050000070300c140c21503c1c241c0280100b803440d100b0b4048e401001c82e10194540c24000340d5480c000c83d00c2286030b218807038020303050420600039900d90600c1d101c2d2002c820f90955030241c40c1508862a1451800c2c400e200029500440d03004007248091010000518085010001000d941d0ba0848000956005c540050001d80d40012851261074a4070200225611808000c94089481c07000180c180d5040508041800c80d194100b50710f1140320383c00321441064120214005800304030391078200b12011200050160a00b441c807aa442445101e01820180e15540010f12801900005600180c8000c00304203040d6010420180c22903520304202804502104d00103040302d0050182804084e0701113550503081c2c01a0720118610803144003640d40f00e0010f04e400400100700c98120000502c43c2d140e0001744480c4444002c1400d91005001c801c25a9443d00d40001a0007020301903017440d0b5080008100091451142c1d101203402c42d400f840d03031645014548000d00c00681d102c980c4848410200304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 476972311 1250 476971061 476971067
    0x10e070b03061003020c0c131112010e0a140f0901020d05040305090a0b04050a1a0409061e09051603020714030a031a0603090d27090e0628020d0b0a082b 67
    0x19030103107411072351380100030038444040024101d1130101c0f807103928010400e01445400f03100c800c0c0c180d542d01510560295140142c40c816203002c8051a010300a00d0404034248403400ca0403182d01001440001d8a03064202e84020110355049500346c00084001c1a41d0b0341501c0e001103070324010141210402d04241c208000110341410600c201c1c403081c848003001020040d1141c042d600100801d240400c4030310380c0e55803500c41d800380d8002c1d5031542042e58203001c02c03040c4a5115060141c80060314800c2e030745003107070300550003980b100901341c5055241200f120309080082005101c01480d41d6400310325040400301d03422542c8003849849201303c0c41030042049030742c0c000411025040c041d00d0400325081d810340845584a0083c505088109003204c00450700180c1a003008400e50070030717001c80c5c803107569041c1134026801c01e2404000b840d140903215002c100c2d00e690003800b845000d207400040c001920700c00203030000840e070740840829000344410480d8000d10742d460f0701e001075055024808500030b106d801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 476973561 1250 476972311 476972323
    0xa080702150a1a0301060f030209131a06130606030b1203070f110d050f1c0c2f0607050d1407150203070302070f200312031602010e070b03061003020c 66
    0x10902c2c1035a1036060b1a444041014141e4140c44083c00800c2255113900d80c24242c4640350009034010485c01300452591144aa00710504c2600019152005900c4c120b09100781c4001521386075101c54000080c5060b0b40c001d03c40d0f400105200c2d140001c02685480030300541c102c411340c90340c110b90410b119980210b00420140c000c8582e000144490311900b240000d201d405460002410510075602119448a8000b42c08070b5615011800700780d01c01000d210803500d16681d400c00a0905046800c074010002d0218400c0a0030b40496404e1110140440c001c10303929008078405440d035030301c05645924020f0b00800408417510600d04003615010712915140310012045c11030080e42c503800000608682c0c80383c0d064440071940052807400344e070024205140300c500d006414003411080c125400740f0603d03001541440401300c40a22031f0a656070102d2810130f001409100800755505d07078900702d031892018003410b800391500019081d02c0c2c2c00c0c03901c00d202d200c5071080740040525204000c0c107071a51400080c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 476974811 1250 476973561 476973571
    0x108010e030d051e0a0c031107030e04050403261e10030f1e030302120105012c0d0221010b0108060d060f0f0501090f1a101b0c06050a08070215 63
    0xb044544484a2516207007101d004040210307405201800b83c80f00181c3c100b00e0401c00c1c285d409100c023000b0750130072074460711803000002c01040010040a0032406d26030021030b031046c0a81440d07601501e001c0c00d059a50710b40d00f00004010030110007080141c2d840f0b24002e0b0901911200410614a010062180d01c403040303000141c12203d000b10101e0801500304155001509a0002020381c0482450080c000e9001144c1d0309074542181d0b0004201940715101b4000d81403401c042c0b01c45a01c800e0320500100ca01c40d003445a41290340b584031500580c0b204440300d500c103c40500c18508131940202800e0071111001e00c1541001301950512480d5510b5074203000700c00340c219600040c0b45480502c41c000502104242a2040e0b00304400000c0e0426607a00289103030044950500007284800e01c4541119000c0100c1a880311181c4460050300344140b40c0320280310400380c913081e50400c20f92246a02c02c9110360110300001c4000074070302c0719640d00024a680244aa0000300058484100070055211005007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 476976061 1250 476974811 476974837
    0x30b0a05040b0708100b0f03070e0405060303220306020a110f070501020a023c100503100308030402180c070204142703090619020105070804051c0c0b070c03080108010e03 75
    0x804101758107581c00001c40205402d2200c20f680d203180700c080740625001143c00b10085061010701c038941d0700b81409841e11581c0300801451900c2c0000642011640041c1510141e0703030b0a00c01c010000441c0b501c01446900210b0310b0322004003001c0c409031071a003004182d40c011640c02c160350411031070740c00003242548603074111a21620f02d0003000030048003015a02e070501080c06040407035940d0000f10750369600030803004d54040c02d0380f00d6018410f4600e48004e944100004988803020008100400302660b045880101b0503024092080103000700c00106403140340450b07030001616400c500e040c0c410001c45031110003c844643c640107010100611703901d105940c00c0c502814500429030018000c940e03101c10010310340346d15040700d80060045540301011b803501540c03805021966032030042811521a0f0382c400300070f0041e401c034100c50a244c401c00441c0079003880040c85c0380b500094044501e181c031580440c4c0c0c40d41c6030704c070660400504201040c0e000c0c034100e915103a0320080c6a4000b1040b990610340b50300b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 476977311 1250 476976061 476976077
    0x1412070b0f0a1218050d0923010306180501140108010b0d051005121c03151401020a080c030a0e01080618130b01080609070602030a080a050a0f0c09030b0a05040b07 72
    0x100282c4018209081c0110200d181400303c1c440300300c0110a8602143c0128106c9000098101c015030b0071219600a0468544c0d0034203800070612210100208100c40605d00030540c6030303903150f41d11200d108001c0e840d5241602d074030051045c00c0010040301c28515091030700c1c0302207501d0300750100f0b034900c40c034496000c00c1e9481d03070005501c00a242c0d10040082002401682c01c204920b036059480b120003440304502c04003030240c500c1005109024051040c0c0d610102900000e280600e00166104c10204c0141036019101d203120108883d20040e080d0380304454040e65861950f604010043c00c0149001414040c802c414080140c484815a446503005020504000c2c2c0705da0002d160f4001012500070078034100500042003408010039428055481d0710101c480c00c40e2030b140b05a880f409400380001c005040c900000303808612030381281d07820140b030801c0011000710b801d0100c02a9401400d8807404107880c00c2c5c0410030880c0800342150301c1454130404102e00d007440e607900c4004000262490003001800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 476978417 1106 476977311 476977327
    0x1180b030d050a050703121506112a0d0203030a1112091e010507021503070906050f04051516050106031202032a07030c1412070b0f 58
    0x261181401c1420f140c81c103c80603000031105508102c02c240e0981c02e41c45c030521a1010014031003041c02203150404002401c4109031031141400c1d0b42c00207441100000220100e170300c80d07a5408241c032403881e07480390000d9068025508003035854080041c2d4014260f800000c2c480400c0d10042c26241541001200003116000e8810100d400c800b40945080440180400c0134a0103038050608605007403441e00480d07011543c001030a900250000305104609420001d010020203461030320526058060b4008146030040d0b00c101c9005c0c1c030220443c1c81301443d1060950303079401040c0003e0340e0340803003170b04189028180500c01900c41256030710110b521148040105c4141c10703e074444030644c0c3c51001b14085e50703006a10146d040d40380154034011000030303a080d0380b0703034002c0c14aa140d07400400700c46010041843c82205030340c0400da0120104100c084050f6080c1c940d100c601c1d0321050780b11b13a02 = true := by decide +kernel

theorem cover : BRFrame.Cov 476798561 476978417 := by
  have h0 := BRFrame.cov_init 476798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 476798561 ≤ n) (h2 : n < 476978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
