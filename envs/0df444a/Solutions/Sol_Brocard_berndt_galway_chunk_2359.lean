-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2359
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:28:29.799612+00:00
-- url     : https://prove2.me/submissions/bc2bf38d-9b70-446b-8dee-5c346c93015e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 424100719 ≤ n < 424280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 424101969 1250 424100719 424100737
    0xe090a0c080c030f060c0a0804050703080a051804090b04080d0605030703050c0301110403382a040f05090c190c030e010c0305030a0f0204090612060f0b011b1502 71
    0x5410062a24020903013407940c000d50010b4180c000d801000355031280442117540c00311050038488050b803224240749180c000603420041c15040002007001004d0341100c0504812020300c2d4590414583e06414007050f03401d02d03100140341c2d21411020400081e40c5d10080c0001c0440030000095455807000003e14010f019401511242c02500111241e81420701505202d40710180b0b00c0361a00e4516074400c041440300d501104181c040301d500d9110b401541c00b911000d468081c5012041c5404c105010119500591440c00810403107041c6189000c1c10844c05d4074111003c0e8003c2c0041c6525080c103110519000030807001040c0300401240d0662103101180d2a1850900d5548080b1380c00240340103003d604801c0c403201d05220550100c280080c1d80441101e070702c01c88120011440c00d07030020342c60019014541055042e1800c7c2503010601a81250308a0004d138042c0606206240c0038038440801c0fa0342d42a0070700e000419010010301d0711004030b01c208a51a100b01160040c5e411150120070807a0040401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 424103219 1250 424101969 424101973
    0x30a0b22140106050d1a0a020904050f090606190e190204030b01061205101403070f06180e010609060c2915150a1107030b010f06020609010e03040e090a0c08 69
    0x405016140921600c0f0203884242c61003008104152940141c1c407500c211040043d403000c400155881c9100d40507142070507000b40c024002410600f956009003002182c08002c00c1c416440060010f244c100c1d56600f4483c00400f414020301c2c1000041481d9540091120041d54031a003458a19600c00380700500045000e24001c1c0c18035414804001d00c030310703440c0c0562044e06041c401070010358038055150000321104000c819540c08011400309080109039407003507440700c1c14010000703081900300301648a16202000311903600c0792030348400190b94400b030203245e0004a1160044c408a0b00408068a01780e0040a6640440c180501441c440805003142100c440603031a041c008020703c1d030324600c042e042003110b0201d801040381c490380045000744e0840f0345c00c00c2840e82003541102801e10501c00030f1a00000f0040c0950f031141b06204405801d0300c18940148110700000b40b13022010310401c3c50092035200074603d0236281031703202c840b0004081c00c020303000d0140c1c41040d000601a110004001c3c404000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 424104469 1250 424103219 424103243
    0x30106030c142a030c0c060a031d0c1306030f11030307050327030307020117060a080f03070b010f08071511060421140d020a09051206010e15030a0b22 66
    0x10f20400c00300150030035085a07074024030442030300e404045800b4012100903100d02c5c1d140d000b00c0308128050004982035030240765554076191585a00400d1200b00003c3c160b48000201c480b6524032401c6914500c000b4068494000000000030410214140c407402d0007412682050026201e5070f0546e8862004850034010b0542c03503142080c042d4900800e92802240590704003542500083c08042c50404003070300c0c0c4483c8a0008103190780381d00940c0003901710042100e242440c855030080e5240c0c88010151400380020000240081c4582038500a84440c4c40140008070300c2d0440e4004c60950340c802d984144112030b072526042c09010042544264062280c0303031003020100b901e8584603e111039510040240c280110114401c07810119514440000401613480c1070885c0211040d80047d0805580089180500c00c800807000610905070754180250408076101c0e042e0600910303170700100c125010780002102001003a40a20165881101000000d0181015040c840d1200003a048101c0d05918902 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 424105719 1250 424104469 424104517
    0x300a021002010e0616020619180503040f0f0503030d1a040c021005071806051b0d050d0c170c030402041407022506020309130b0409060b1c0305030106030c14 69
    0x481d1580102014240d0840101c0d0307005c009440d40c40080142010030740031510400354100d01e500078101041f000c80d0390214540b8519010f6103980c171900c01c180364000d411902007602440c4002c0b400440d40002c00031441c140c800e9035884080c05410b54401c10368110301c1051803c030349075801420920301c0300c1d601a21141010184103011104080c1c080020444a00840a070000303141c40745005030740e414100280c980c80d100a003004043c8500f003059446003d44000040582d800a0203042168425041800440c1140004031000c100764402d0396820300a81c00400d1205030300c0401940c11500241000c01c0e60b0060b88054800254280c0303074400140d201000f1034044030b02413080d0380c43d58021040c1c4060035910f0704000030740c0c03805804000c1d44500b6028140c80304120b56580b1040c2c00741d1024106210100e0a03081030710040807000b000d2402401d003e683c04026241000524082030f40c1522640d041d6400c0c140201d0051008425070303814041a010b02c00e03400300845024100180310b000442c04418504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 424106969 1250 424105719 424105723
    0x3050601030614071805060705070b041214030336010e0f010b0307050a03020907051902070303030b060703080a0f02090303070f02010f14041a07151406300a021002010e 74
    0x41400d004c02c00a41040310588011320b0019048031030071260707d80c8030356031800d1081c10907a541d804200c4000002400242d0080b00c942c0d1006224000d4084480e0311420415898a80c0300031640c411060464040e040036035607441d901c0e10101c40418140d801c0c0c00c000545c100f400c44182802e07410070390344421032603800d4800900403000c030340388141c01a28030289428045201031200340402442107110300002241c42e84074105a580b24180c800094442004540c0c0c041c1d01c649080c003056001a0502d00c0c4a0260b0030900c0807075015941c559a00002c0341e0b20868504010a111a0000203003030b000c220b5120195810000380004030700030f5580403402c2940d880050501002100100c0038041c40c0ca0044c03140f2072130b44068031304540d180124015010241d2400040d944548400100003800700c04001c00d455889034841c048098a0750403461603074484a04001030720340d640c03548a0000d15800c0d200b489884803003010441000400080713841840c0150b000441c1208140f21a00050395102d000144900c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 424108219 1250 424106969 424106971
    0x90d0c180204030c0b0a02010b0901030c0503010c03020c0a030f090b07081803060702033a0507020601061803030c170c03130905060a0e04020a0506180f0f03031c020403050601030614 80
    0x240e1085261516682d40e004c0744000750301c1406180240454020340140c001e40040d04c0c0d00c9030090403c0e0907503840785409505014140621402580303400b40031380130107002e80f0843c0c6d412403c020080c1f00321222954100d0310004540c140000300405500e002608071841c00140c80c10610880e401501e03040d03c1164414240800250b07548a80d02030814002d500b0340104c200d41525008000240d00748000c007001b51902114404107010b1541c944c03c40b10b0480344140e005a005000f10741c00c1e0f8900740d03a01d15003101c61210441c820a15142c14102c1080024000d08103480018441c1000911454150810242d96005031305d55441035000007581040042140910308064201c3d841d00b003005041080101d41410058000ca1038030b20010408601903580340b0134400c00820b03000b405a03550301c0290700459840105203140f02d00a8002040f8028907103001080703d440080090015410400d60160361011a0310b90144200300703075420080440803070002e0020a01a50064802081e13a4480058030161800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 424109469 1250 424108219 424108259
    0x40f05011511010207081606150e011715090304030507120b0c090d0609061a092e03062301060e03060c03091203090d02160e0a11090d0c 60
    0x1160200600c41056001450340d440080c0d0300e80b0345056614554803034024820500040c100070f201160f104a441c901c94070442c0100e10480713040c460380440309507600c281c0e4181d000b01c0040e10754050043c8104140c403007204006140100c110b50000e0759507418420b1001044e652828903820000e01482409010003010000740080c09055402060507200d03c8000000038001115a107400680701c600c2d40d983e81e1012170b465400083c00c020030109031034450004d00200d4407611105280906150b41c5103010303c0860310802c04642808003040061001e0a03500100070304d0b9180f12a0300310800b0000c2a100d215205040081101c0c6d4400711000d41c0042d00c2040303050744031404004041101005030b48020403000c0e04818524090f40c4c4070384490502a0806451186206182e43c0200c1005a6948006900f102c4132400d03030256640f03403072118090408a0190b016681c0c240d680707100400c40c4013031158040c2c10f4801c0c0d000011400c00c070907040000d036440e800300819200764981c40c0d424840c1d540380c084000c00c114 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 424110719 1250 424109469 424109471
    0x30e1908040f0b1c0f0603150e0105131a18030a030207060f0501050d020103051519030210020c0d14100c110f19030e060d09030c0506060a030c14030a0c0f05040f 71
    0x51049044d000d40e07100d901801c1d00103615100400c0401d401600548003469001005960083c042007207203006290017040e0090035824030021544001a0a005010b00f6402c06d101440303000c0c2c0d44a0300c010003800a054000941c1200d0700242155100b13002802e40ca41d450b0342e015980f01c11500b00601074600b4900b400e26403d14005c0100556902c08510007092135080c02c1c0802e030340d5544042220040c2040e903840b82c0040c0c0e610079081c044040243c0340001c0d80d20031102d1111600000804a94859a01a009401854286c0a1800714550000c0c2c200d1681254007112054450b02e2040c00c19104011f13010004101c00d407800081c007075000d104843c0c065060b0b1005001c3d5004104080c4901d42200402800303100c40c05031040f200c3d131200000c881c030030566540e007031150f0700031442c004103040d01c202c200ba290703401400d0201d60b903450aa0fa402c0212a08400c503d5242402d000c2c1c03ea40d00d01104440b1541403060481071030015141210300e00c020305d902c1c02c42d03480c21351508061109843c1ca2861608042e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 424111969 1250 424110719 424110727
    0x60102060c030a150b0a021e0a0209010515040909030504361503051c17010f03060c051c05090f010e06070c0222050a0605040b0f01030e1908040f0b 65
    0x4021024140c1e03600000c600c9010400718182c03101c03480c6503a41d642020300b2004c2c5c0040d8030107009070001031007000382c03640c0040002e00246600c0c86540f140c10f9000000d40c4290200f004001501c0d10301048140b142007030142e60f140076a20300200d421120741070000c4010401c046010040d00510a00c00d440c84c40246c900e00c065405640d01c00521402c0c0c0000115400e41e0310301084004800090651001e1544038044403005000121040c2d14290f5242d8444006281c11146035180400b0880040c1200c29100c51942c045045a0b1410f000e0240d0107000c00c20044144045a42460030760000b0000b400e07103081c001040d04000e5112400c0c08942c4840d001b00b03032b0404450b001d00000004207190700058074039040304021924400206051000e00c0c01160800b185084507541480700e60000303024803407004c800c10005030745109000a644038500d846030f1141c0c45030542c241e82c1d402504104040700014003620346800b1200d402041000f0740400070394502c200450140010a40c2c0c41118018194000c416428 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 424113219 1250 424111969 424111981
    0x4060506030a1110180b03090f1903050d020702040213030201031b0e041d03030903030f01050d20150a0503060f040e0604080f070804171203060117040c0503060103120806010206 78
    0x2c0301603e030140c10302415001c02c9802c0d00300c3c461100c120300d080c0004140c0c2d0102d40e030748904e0304d06c0d40c0054803e0484c0e40036458018100400000e021341d20308045040144070050076480503620750b0060803102d03040316020445d100041c0e03200d10040c80c003040c15202039042a030541c000181101d449560300d00d010440c1c00041450a174001c0c20140c00400c040360082501880345031304150340681b80512610501c804424010f410303070040081c62058031103001c0717009141e90f554104001140e02d45806008224034001c03506015100d0501c80c0c00c05840a0881c0310800030300e143d18002a8081001c4000058001c003c0c48401d14242a00c203c900c03a0885050140541445080307491781c601800080c0490400180b00542c10381c1c0c04196080303150820305041e01c07a81d4441c8034162071000c00340c428515025510412159803412001d80b03015500603940c41c840c544204213a242210800341094503441400240050181e41c01c00c50b15000e1407150050041501444501030400388010f051b450654000f0741c10030103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 424114469 1250 424113219 424113233
    0xf110d0b030613150b03011506030b0303090603010b0a020c1c02030c0d080a23040f0501320703020c060c0a020a0b0c0a0816020a03031110021c0209130204030b04060506030a 76
    0x101c202e401c60725105102c0c0000b155013000385100841c554042d400c00c0c01c800b82412100e03410204407a02d41d00e0911803090303140b040548134800c180c21a940100c042c801402103003013040142120340740600403541004003000000d42000b0400c00901948000d1104200840c1000d01028a000c0d5056a100686845684d42d04009004559180c000c00c0340c11107070f04001003c0101c100000072580801035640300e03119040140692814000e6074081000c00b5250f011260507503a000751940f26803071185c1004a4010180040d41d0f0000c10207034218441c17491707034460b50f54410000704181c0340701d1802880d078901184140002600213034810800100e00f0701c41844098008503007149440e81c001c04003507a41e18a02c2c805980141d0807a0081d4000103030540200070550821410201440c04030300f11000c041d80d0101140c10381c03003004244008080c0072401e111a19110340c0281c01546402045000c0e44005e00349503004030381055005407690701840041c4010b100403441550b030014070507005030642c0389072034884007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 424115719 1250 424114469 424114501
    0x106030c03030c0c0b18040c0c0c0905180304090c02120c031e0705011404020102060a0b01020c090703060317070c050d240b100302030f0a05070207180f110d0b0306 72
    0xc2d05001100c60030204104134520088054030f00048400c2d15041c2c0144001a02d040e4010310a0080d0300e041c1c2046400d0780100103031640030380e10800703000c0e01c0d6040442d01c00103001c1c00b91450301c0d00300d181da08000510310240b001d440908506000050196099040280b4088504a140900920400242d1952803010003200c030b80035907000602c80d001100619101c5248660440a80294039114510000701184071140e8042d6000764221811501c45009401c2103076020f406040c0540c0c00f202c2e245000d420003000c4c49610104074240002d1865803901d681042d24800e607400e44c140140011a407040002e0103403140050300c019240c19a04012540d1000300c0084484240391907026581d0055250030b800703400c0b42c0c2503420054015103040c1c01c50703400030300a508107035180101442c240d40000c1d030013043ea200d0148108a01d600070581d10340b508100302541c054200d6a460419117803203143c007403402a0b004100d041c6e2042d04503144d4649443c0c041004079010310070681c1c0710390000d405100d145e40c0f45e44551 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 424116969 1250 424115719 424115723
    0x1020d1b091403030f041502160f12021305250816030b03010f0606020a030909022109030c01060303081906051012090606060305010320010c0809030f0f07170106030c03 74
    0x40b2896045100001c0c69405031182850586400180201c1c40481105003680c9a40c1c19808031060344481042850654400d070185040306401c10804000008050039909555400a02070b01c2030f0303d00607104003080e280d0460b82542c00001a4015030310a140d174511040c560800c0d8500381d2840e0820a203c01c108800500b005000c05446004e220032541d0294020200307a0315420041151030740d1514083d451307503c6a0019000301e20f0324840080d1048050080b04c0400c9824420300e90001608603500d0701244018185400ba072209120040c0703002024070584000d140a9156410146048404100f00c81000d0000c0e10b09542852010407194842450300602c0413568100500b00b100e0482d59030b00244100040500080c1c1002c81c0001c08a816034000ea041c1ca0041c0c43c01c44046145980601d054080020000c1c0041e440141b884041510700b409841d58000041c10f59140b5440919603900d401d040d0140c50741150444071003001008102000300780a41e080380000d1000d06d00c0e5413503500030103005100c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 424118219 1250 424116969 424116989
    0xd02060918180f03090904050c120106081015030303150b0a032922090c0e07030b06032e030203061f06030c0e2103071208240f011e0201020d1b09 64
    0x1203402c0101c22702030304100d80c40103000c90f00e8071014550440c5c01f1300b05c1442001d07a01d00444401c140b00e0368881c080e01d00da00b000e51011604940c55580c00714010560f141c100030200d0007040001c0f0342c14007808010035160700c06039070100d4103550b9100106c104114165120440d8500a00310f8040d54a5405603405500e4080361303449a020034588815000c0c140c4110028207403080700902068003001041110701400540d60104108554801448454072040d0341c00311100207407801c0c8212441e485d00f807004144544602e00040342d60b40761f0110b485e00b1030903a01c2d105038500c820340650038030400702c038a42c008000e1481c0a10002c081881c028100712450b6500c13600848000048605040c2490001c08601d04030780100c03559505141014070740700031480386000008241c580450700e000710709116400c085d200e4110410030b40f040c2008008803800f41c0c0c1e03500f82c1800004406070f19014440111300c3c0310318011360000759071519a100d400045406800c017900e01821100c1c0c501a030240d000e0703022020b480e0f00d159 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 424119469 1250 424118219 424118221
    0x4153f050414030a0801180213140301090c03050309130c0e04090615030b07020d0518010302130521071a07150b06040f06080714090d02060918180f030909 68
    0x51155036000e503400b03888528800090501080d951101055040340e426030910108001416500b00c00e0b44109900d000d080c4107070100520459150154100401c2001800003510a1059032154440c08032907100741c03401d40000c541d196050500c9850b0000101d840701080106947c1e6032000b034900c0d054108114001c1d80d45280182c01c0260079031000d81e0102c010400b50701e0459480c0390880040c1400c41c0d442005028010303c6000460248060380c0c1c5c031480010010440302c102600450080d0480130507210b9440c80b29200282d951695140201901000f03044219903d0f414860f00f85407001c26407101d5400701c0c22071030300040242020300351f510361907000103074641900302003100c20042e04214803071075070044000400148203505003c12008596040d1034a80940d51400c0b000d840c2c1c450114401d10a0602c10405000a8903028501444089c80202401e04105100b00410078540900c0608045484018181304401910407406140c1c00c1c01c40004049540c101e000c544c6c1c50740240c0080e41d000e080d07600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 424120719 1250 424119469 424119473
    0x80607050a030b0310060812180108330324010b0c0a0c0e0a0b01080412030e0133081912050f0c01090c050f03120a0504153f0504 57
    0x41c10940d00080000c1c103d45c1d440c40498180c00040400e0f200302840c5215074080548020070000c00d4880302c108501d0040101d8080c2001594404801019104050041d840d410a10004c1086a036085244412000d020050384418180f5052016251002070800d03056075203850691540351505660700103000715200e9903403c0345a480c00c10340d510020600c0c42840d00211b40d01d540c010301148a861305034002c2c0710042d854801950b2160050b030740078001010700984805882d020790055080f000100d400021644010351010003a1204500c105880444001500d25440c1001c0c40a0020788980c20181042c4260810130b03d2014101040c014401034194070080300d0356010f4015030304500c44640e581070365000d20070312035802440c1e901c00407542c48818200104150070f04101e02c2204480180040c15800d00d600d001520a4101c0318482041100410002c00c2100429441001400c515100c1c40d94407011025248031184211540b4010141c00201102144003401034000c00100c078900f00146a450b54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 424121969 1250 424120719 424120721
    0x20102070803090a0c0518041403041d0603070902030f04030f17270f030f0c07030f050d020606010305220201030f02030c0a08090303041214040e0403120b0109080607050a03 76
    0x2094003038400769011042010800012903444070b160310510000d900305071036504028800c441d0315008044401c54600007000204800d264031b006100e00c20403242000d60f108032500604040c1c609031980000001c0500a041c00c1c104000f9024044404056007945842d120000c25800c0c01000076003080001405007003164050280c02104400c20f1905008505d04009014090360312428606043c5c41003494007000300d64041003818540d00c0401c0907620b040c4600c0c065130382c15084054414018060303240c0020005070b0150707100400030f2003500684444c81050714040d08042009007846d040c5403d1000308440041c580c0440a84003003104108903503040e007400100c00400320009003100540c4000b05220380e0b00780080190100c10910b560b5550b041d500c480f4260744074042a20010a200a0300d040101d119004020300203043c0c2c610b0190a082c15500d600548146009030b07010f50201d00740d403000c3c90605240d40200140364500b824040d50040c40d1003030240e070319100100171100308900451484071303081c03003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 424123219 1250 424121969 424121977
    0x20a260609192301140a0302060315060405181f21111519050f1602060c060a1b020f060a0e01020d060b09042009270a1406032b020102 59
    0x45803c00c0d20300d030b07008022220a03069080c043d28584104100d01c010140c030348103e402060340c1c2c0c0a0006411600d9102c0c02e94070070f0103080d5640703510400501c00800c980c1c03910410201003d00b02d144050f0756007012191200d0541d5040303500f40280c2c42d0b220007404001c4a09044503407215035105044550101341c2805226a8230068985a00140030304042c07900d10143d20240c61280c03000802030b003d00c80b0301c40058800d442103407600c0d80d8059040c044403400b100c1150800c802c0b2800582120b15200080102c0385c10904112031120703803d41c0e0b9080321019000c851700080303a0300d80d032400101082c282c1c044820740c0d0780c480101041c0c07145403101000782d003403a000e4066030f0745461941000e2040c151030320414085900b0030000f05000b01d02e0800940008610100354115044424515900e000f0041c4188035103003442c2c4180c92003489030005400c0c6241d0303c41e14401d2045501c41e900107503224040082441000019010900ca9485001020300048003401100300c0e071036295040c076084010107501640a805 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 424124469 1250 424123219 424123241
    0x20414010b04030807140d020705010206090c01091502190b09010516120b22020414100f0305040218010305030703081b090f1306180b011e080601090306020a26060919 73
    0x244641205101c8c1e00041c810b41a00c00c01d800b80d61554ae50b004071699204401040300d4001141c90030208020350408096180203866441920702d8040f42d8004039101d43c0341200211144010303070041140341c00d03003031282c0c941108100260b41c0804030310b190010f20b0644000c030010711040d0b861060074116900c03410242485490661401d1a41c0c50039030f0760f440250440d1145a07046d00341d0004095440c075105411004070304031900c805048030280082240140030051040703820003442c8103d2a04540026032460003184030780011a507441d06032a00400c5c40b0001ba144d1242d10020342c000c440c19014101c2503031001c0000b95003009c580d130710714000034007813041c0d82c24847c03041450080c010030032a0040c404881c4407000c210081c803c00340c448004580019888607010f80d04050705a650215602c5a8240340d0440703814035000f4a00c5407070380c440c80c0481c3c1c011405074000c82c01200c01030076165600b80180d03000407111100c81c0d01a00d03049010840026004050000c252103201e401c01c8801580d0b442a02c00070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 424125719 1250 424124469 424124473
    0xa11011d01090218100303050c0f011514030c0f0f01120903200c030303010b0a05130f090b010905061e07050601030c03020f041a12010b1c020414010b0403080714 71
    0x103000c80da0618000e18040509030b00641070000711940104c09454428000c80e40310200060251441d2022100c603003000300da995090285c0c1e44030103080c0409020b098403409840c00040c82c2503240044004442100b1120140260440e001841c640d58a80e00c0a1800f02d02c10ba68003a0100f0004c0300480d0441170140d84040c0c80c80c0360104103014140d0042e41c0c00d030300c0c0840ca08410036103200c209130280e5880040103c203074540d000b08014025110070308081c5c00006060f040c0b003410400803508410407501580c02c03541140f42111010000c1e2107481c0180c4020380c00030b0800e580c41c03504000c0030401511902c1180c403148514040d4138135481000c1c1c02240e0500d038211081e02ca0741c1d41c40c0d1400b8020314480d440280d20440084010040c6460f09118107040c040c4d140c1d92095140000005101558503032401000507956a4600704100e40c98402000403180c0c9040d21000410042d8030401040b03559200d02c01e035014203030b03600502144000c0011182074a8102c46210307103c08007450900328003e40010481018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 424126969 1250 424125719 424125761
    0x10905011a030d0801031113060312020a1104060b07060b031204090e0d0302090904020f0f04020409050613020702090a051f03030309050c01031b120e0f030307021c050a1101 76
    0x7100c000340030307441c00703080701641c00c101484a82295501000c0c0805080700d0607640c1c07114064079064444d26a08800c442012500542d240c941042c010100180340016804c10708400d0300b000030407010307204450b03000c8034204131440c2050700c074201d540121000100301c25922092400719541c2049030030050540031142170394854694240401506050b03100200a12529213051507803400790090b24070a903400703410b00d000c030368464003000540d8421008041d0051008603019040380c45600040001e4040f1200100322801c0c410107201452000b0170100550900c144030304c1006070b540062550700100b07940c1000c24141c43e0082e01d400300010303034000c89202c20313800c0400104058140e00702c03800039800b03002600c00030111240190140c40b4600d031710710140406c00c4039031035040d80500b0145600802503480081c0741c01e100070700030340742401e05140d0f543d55600210820010990400c110b4410752620f0034507910232648024050440d02683d004101884049100201014401d40c043c181302c450304c60031075a0b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 424128219 1250 424126969 424126991
    0x10b0604030804060306080d0c0206071505070507110a0303170910060f0806060405040b07030e0f0a0309050916091a0705060f1e010803040e04231516081801090501 72
    0xa0b0741c2c004c0c440e00b400300b824490001512400414002201c2c2e220b0344070442850f00b07650800c45140d002c0842143d08290b0070681c1f940c048013500c92103214240b15200d490b518011401c004e1001741c10031070394a201d1b010312101400000c3c0e02241c0300d06507046c13020280e0716a46451004e5801d1040c2041c000860610b404000142d80e0786440e030400071121007100b940c030107403219018401503c20849000d00a03140010104006500c668810014040b102041d1451141c0318003000e405c0203043c010560024040352414403842c40c15070095a0040b0b0800c1020040c0011200040d108115502c82d40118032004a03042c0c0506001800722003413a984442074071940d00c2c001e00b001d00d2031103060302c407440c4001142140c243c89504407030459041e29101c1c0c008600705460b000600b16680030080c4111410461000450b0454004001022001c40348002800e071381d140c0c1c4644509d01036001050000080c0042c048010340581001d03240d50071050940008400e0301400111a024046510300200190f10380605002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 424129469 1250 424128219 424128233
    0x705070606060f0e0108090a060603060b10021902100903060c0f02060105030d12050403170906041a060f09071e0c0c090501080619090c12020f041802090405010b060403 74
    0xa5564414039081010a8880400712891051955101c021480c0e0752090121580201401075100300d0300011107040d5001a03441600b61742142d0300449805480b5848408145407401010260012a01c0140075040f194180da85000505d00750190056402da4103032401070741b18140e9100915042001405400071301ca0004114084282d608001030050f0300012810303140c0441d40b0841c012060380c80f2000c12a20030a07007001010083d20407018401c07510481c448501038240034600c203841e4035014014500d06400c091300d0014040b2002a044c10a074010810b15542c0c2c40c403040290401650403298583d1034900c180e9a8220005401e000340e060303001c01034210b9902c04a08371240748281c1800202c140d403400c981c4150342d028050030165410560018291b054103903401511544050000f007000111a1500381c1c181c140340e0400002d03940c6030700e00074003541484100110700e5603041d41e04100c4140f485204003141242910020b210f210400d000c01d040c04425005640e0080c0c000304040c1e038540e41e1b481e00e16 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 424130719 1250 424129469 424129477
    0xa1509151a030601090b041a03130c170d0e0a1401021e0c1c24090c09051e012102010215130308071103030c0a05220f0803030412081e0705 61
    0x4d0004480c000003191480070f64060b00e084450760b11180b45420401c0002e990301e0f800c000c009009180740102d415010031300301c0210500030405a661040007011400c40e240c1420041a51502403048044030815180c0700c90b0340c440101c50601c1c440b070109032890b0740100c0c04d02c140140c00c6c0152105950b140c100400010450200c0998100c880562000c01c0090003e08404030301d01c0645034240703d031281b032280c1003e5400000364001d800d04c0094600055510807000f61040d03000020520750380c1023000407031803013007401010303c00d8550000c0e02c40350b14100c0368041981c01000e09940806000e04003c08590003080705940c2c0718003191880c4083d1802e118100c0381100804415030009031120045111030f4081d6852848074064a005545152f8a2003511001540001c0d044030401c4006c00001124992607942042d00d603c1c5441e80f84000352501a001c442c00a0030341002010b60030410600c000500d02d0312400b41e042c1d0160400b00038964a0800c580d141e1300c40d06140340c041c005007d0401c10351652000c020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 424131969 1250 424130719 424130731
    0x81b010e1f021905030406030e030c070902040504052206021c0f050402090619030b0601141b011104050a1703090303070b07020610030312091b060e090a1509151a03 72
    0x50302c0c0710842c880d000141c3e0051410250550f007080105000803803080d00301d081007000b1801228a02024044000c1c81c01c03905900c240c03c00765010a09000500d420300600e030300101181c81e94010603007403506450818076042c400a2040c0e60008511900751803020310041c3c05100740c0810803090941c0440d400241100300c0d0120f115031101170010349a8a008108402e14204181041070000c0c20340c0e030ba4442030100502000c0c1403160042082400703000241c0241002e01c00d0400304400007034103003481420340300880b0001c03903840c2c028801800b590315003102000c1100c01c00f500c0800942c5800149600b140310392511560180000a054024000050b110500581c40c81d402ca038019980d805600b841c451050000070002511300a500038680c1603600145c5045018039003800c2c5544a5010100c0c0c01a015440340d800719101c8489a20350f0314190005607030042100f9014001d0341480d03404149402100d000714441c03940e46084180071746100f07143e4500900300ca000307a03286100c00c02175000a40e8004481c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 424133219 1250 424131969 424131973
    0x2d04020d091a0907060809010906020a1e0f0f081803130f051f0f1e23030705220e0c03060405130803130f05030703031b09081b010e1f02 60
    0x103851002d0807104000c034800c590000c080e000703050034507800700d13800040901503142039901c0d03100c1c000104000d440101000a103e40f581044104002e51340a9050400900c0b941440b601702420500749400109030000c440c2d461500348101e80e42c000384c0501078900c04200400300d10020580460034100711407443c082d9030070100840e520503074680420031001c2c548600e40c0c0c001904600c0b0b28a115004e107050004000b0075003449d45540305141d0f00741c1c071203848000c40c1c8000110b040354541070300040c0d18546a01c10350a946c41d0391031445c160f480901540305440550004401248102d00c80b41c3d6405800300150403200be06140b81e050609100c25517410036140f01c3e100d00c2c60701c0e01081006401c080c01c5011280d0040840f401c554035144541c10168551205442c101c280a44030303400100d081c001402c6140c801c5d00c00142d80e5001c69851a40032004061443c20f12015007401d00c403070710000913003640320350350001182400d100100c0121000540c01c285280c1240350030a80500c0040841807043d201009682 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 424134469 1250 424133219 424133243
    0xc03020a08130528020409030e10051305120f0f0307020a0e0f01030213020405131a0a0806130305160c0e0c040605040b07021c05060405070f03022d04020d09 69
    0x400300c0320070340002c40100382d81e100768080f200f044007850100b142066804914030100d03086402040070364443d88402c0300003c420600380a000d00e002d203205242e40100789862400c0c05040c4440c899142002d0040d01e1040310542802440c0400c104031100c0456001403e948540d120000c0c0680c0e60340194008900c107004039003000c00d424810350f080300e1007550444500b030266460b6400707121100710704070003010304a50200008503094031a011070100320500514001210103980081011084054a0051146102c00010803059a0004240d60080c80381c1e06001982501c5140a407920711a4404083d000780c0354404503810311241d4240b5104071800c044816001b030340c686444013158403450051001296007840140068440b10018254851010b000681401c85050920955400e4403200700c2d2150700071001c0100308030090103800c0060810100019800d4215800124220304800f10018002030280b02d5241c60414500d10120140002d002159222010301070f18001d0100603c090300d0b4108660 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 424135719 1250 424134469 424134481
    0xc01150506032401090503070807170a12030507030b04051501020d020106120f081e0301080f0c0f100c0b130303060b03060d12121107051e030d1503060c03020a08 71
    0x404680c49143c2d50f0b101c6028440641503900c803015148403100303040155407207011485403000c1154501030041c00c401884194035020b40c1c0080d051a5072009134481d0000e814013000508000840600c44440b400c2c0401d1030360394124228003c050308600070398007500f024180141e00c990900c8500c2560401e81c26a1a4011401c001703a090300c5051144280c0300c140b203e00d810100352408489030f00e081c8100c0391145481750389121070b491013002c0c40354454407560004c010050071b1303c20860709203a02120009000312000c03990008540b120121801409034246e90548003885200300310644d8405d501144218980c100940c240001c0e05c200401240800d10704100461032000079000d40f0b1003103000400e99001d401150355149806800f40b450001071100c091001c0c45d03103c444d405608480414017003540e0320b40040f41042460400020340180451009600501e031000c0080116910598440d40200e041e001940c1401d1000b00c13558800f0f88280d00d482c00c0d41d948158150000c12105500e070303550090644483c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 424136969 1250 424135719 424135729
    0xd05071202060405071203210204170c03060105040e0f01050403080a0b121908040801090807060b090411060f0d1e05060a06080406051026060c1c200c011505 69
    0x383c4018009900c90102008150b0850344c600a002d4803030710b4403501d800042d6500c1c18600000041c02001e40f40c001c1010702c5048845402c5d802c034909501c004201003800c4101113074030b07a801130046d80d000d691104107182301e2000804c032240402c0f9404e8001c01980c5024180200003e01c00d450801e04203041281d480c20301d10704010b0f001700710165030000e00100111810002c200d1400e06000325280b0009000c0055400030078071500c00c6103806001c1c10b070755035035007450801c04450003003046c2882030398035005000100701c0a4420013044902980c81503a2004800e4081181e03016000d46418600d08244043c0c3d0007040040c1c40e251a1001c06600348015200c40c4c1c01c101384028140a002d000864040c00140070a0664001d03d4001c40300311912030720162103522040d550f11130000951200034444500c01150f407400c1040c02d034040301031000c040c100825036040c101090440084400d600e9140c6032030210b17141d42405c02205201e040710342e240e5504100e6018901821074040e02c4006004156000159400c00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 424138219 1250 424136969 424136971
    0x6120a050c0c0606060a0e0a0602060a0f0204080303070309081c06050907030603030203030a3b0f010e07030809060f12010f0506030c09011b0203010213051f020319030e0d0507120206 80
    0x248003d005265143ea060040769007240c0808000c1000c248110892500d541d000726001e81481c1d400342c03e252521241200503102c501007030703940103481080204100000071003566000000c518010481c84401c1c00c1c890058060041051070000d89040c6008142403164440011503400f540c10458a940700b038000e070121a2144400f0780541c000b0400507250f500b0640c0002d90901c191071403c90314040e240900464058070041d5042c00c1041042007040107a007c01141c0c402b1a000b1009109400040100680700d611910009248150100d1000020707641c800070f81c0d80e205908401c058803914580a1824a81001e10861090805621f4080b901c1d0508204491040d07007084100da02d05540c200045522501e01405095598442005580140e81c2030000382060780c440c084808500d030030541080640007058000c0052182000c6030f10308420740100c01e5610303d44040c0c18900051030108026000f0300014038203038259000342d0040c2072400d41c018000c0c21516000d00f00640085440080507a17075008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 424139469 1250 424138219 424138237
    0xb06030c09010c0819200d02070618080a0c210b13030e030a0b180a0c06080c040f080a0b010b130e060301090c2303060f070f030b06120a050c 62
    0x80400c00341c50994000c41c1c00d200241d1207140703402e00d40351000800c2140200c03d1000c80c00040d4124080c0d46000e10411000003030300798100041d00c1c1c0003c0350003000c1c0d41d800c264814102130000c400001d0712502d905980d640c0050095109440c501e900c28908900310785a41c1c0a07440c04074a541441452420803251120b041c5a032048189070141c59658807041c4810740494201c081003405610f0024a403800d1040200a0f4851a1400500d00b015281e09817081c160211803141ba81c00388a5000114251102507002c5131064280100342e078441700401062840740f50080f43d00440c00000000d481c5000040c2c02101d03a00a440b8503850b641ca90000710704600c41c03a04920004400d45005200c1e4070056081c03103070003540090002030b0b141c50694035034446d06110341c0418103021440700c844803100300c0c1e412080d044450803805030400c1d280202c00c3d401ea140000e09804d08100545003652409402544845543d43c401400c55407034260700410b03041414411104125200e041c1408120040d2070740041d221130315 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 424140719 1250 424139469 424139491
    0x915091c14040b070c030218040b060607030e0f1c030c050c060703021e010b041104050a12121b0804180b042016060606050a0e09070903030c03111f0b0603 68
    0x41c907124100c541901310003010f4848190128001006a40d03800d0b1409511103280c3c000001460207041002d10500001e200354001d507020031200c00040c2e4400c91040c0080400c072808200354072514007003842140d9562000f401000c0481d501402d041d045083d900000e84558100c508210300501800803600036840000c0159000a03611405013000125491005076100f00015584548a00060645100c06c03082090400d00040610640c1840c0341e0700b0018001c454007108160050356981010010308680c1c0c1410441943e0400ccd03038000c035000300d010016800600c0a504c036500c03807da09200007002c109203504c07603180048510305030a107801450712000ea180b8800c00c1c401c00340407800410364801180c40c07420203039008020700050a03170702c654806000550b503416210109402e025210b0050a149544204140d108200240d41d00c400f542094942c0740c580000d0000c41807178242c0b021001c440d4100024040d0781014814004410000c01d261160500203107c242031400a0082510007901c84100720 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 424141969 1250 424140719 424140727
    0xd050105190902030a0e03040605070b1b09090709120605060f030f06190603200a1202030c10050c0607030507170f0610050d05040f060615080106080915091c14 70
    0x10010b10740c00f5550000d5418004142c0f809058681070a5a100f6001803000c24004103c00302417140d0303ca071207540310703070410050f0420b0300d00d50782401401d01034105494402e140040008208611850b14140103001041c40100708010a10f08500036244c00c44070607001c0c1d6081c8071001101d26001800b84015801c400280c9400e031901d0030b83c0c0c03000d242a15040e440d103d4886400200060070900c404422600c0d11001c558088010010030280407011b030312540c12900760315845800b594010400a51502c0d0440b83c050140003101400c1d6414010105415041c0c0038000030081440d405802540c8038a54542c3c402d1032001050416149841058038150b025100d0f09000030102c1c1007100c40203424281c40d0828a080c06400c410385010745104840486244440012000401509001c2c201c0503140e0401001108520b040004105210501c0340034108540341002c1150203106008c0d11a1450394282ca0400a180001c0030130f035035000b103c9031091781d9001c4681842d18070344242ca89401c0c1401001e4901d00e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 424143219 1250 424141969 424141979
    0x40b0a020703171806100305060709030c05010302090a03020d0f0b330f06031806060618010c111e090702010b1c0501020d06090f1407020a0206030a0e0609030d05010519 74
    0x44400010141d0300c141c400213510b501d0554003088520b02c1803540281407008141035290007410490050b00c200b091040480e003c3c030010b19040f03072240a0714820710340180c45018001c0010600c3c1e01e644d101a400c500a0800c0000f0300c03600300d000116080c050348900740d403500c420111403a0050070026203002058544105da00280845110b00c4918600500c80ac460b40028800101c440e80107440000d108103140e0700154495105001d450750185080f15074504059407140c82d1014141e45665082c10050f401642404105440d10301c11035103500900000304562800c1c2498001ca0441a44244104a01000144224414003504058150142001d81d081c0c130050b00300c160001c950b00341250155001c0c44088050201413082078010460a280420426413220a240441e029410413035442401d020401c021240c00003104022140e050f11010303641e0b91021011802090301d000002c0c0d4600400d42845070005000000e041c0280500c441089203999a41c1085405d4410451440e1000c441510803c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 424144469 1250 424143219 424143257
    0xc060e150c0f1c0807080717070201060b0d020a030b1e21061513060608130809030a110108150102060c09040e06011503060602010212011202010c05060f040b0a020703 73
    0x300c414801d0442d101100204031180c108801c20526804561020fa29455140e9211546980181840c1401a40c50801480090a01540010180f862142000030402c518401d42c401401401c60b108055100e281c0000c0c00b40295001004000000b030504019158510f07001d0a820405113a01c0441c103440b07100c580510a80448800120810700100c020a403890300781440061b00c40c4455484010340841c082080004244100300c600226510300744003072200b182c03c0a07455400c80c5032201600c049903600e2800304041d01c600202c544c0c0602034907103500c0030000c4421881d408030400b40c8920404e59611141c0d0340c50541c01c000d51a0041c0c2c000000300300c5818070b40004004040002d0000301c4d4020141c411145411401e81c0085590400d050ba9096130680c14400c12028102c14402589841c1d8a5246a2001007060007141c00d500d494020070011680034a040a40f2564484180c40aa2401d0138a00d141c02c1412601a00c06541540002d50082c5032482121211030785502c50112031401d2a907020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 424145719 1250 424144469 424144477
    0xb09090d210504060204051503070f140408070f1a0703021023040c0509060d03021506220501140f0d0b0604060803070f12030b18070201180305070c060e15 68
    0x12107080a01e9254680400550103598480ca001c0c8002581d29407a040521075000a89084822292403e00900002d5030340b29018100d6101c40f441c1c020410450103c2251240c4516400034010303208480c0c000580742c100340090000c88640380d2501001945121300c440003882203050080043c0c021180c0d1910011030350388445403014641107040c41c40303090300c51541c1c80d00409640c01c0e5008011810200214a0043d45460b030201c03059840048585d100e039804ae5031007600b514007156840c0060300040040c1c9402c0300900e1000ca000b00e002250310880c140541c010300c0280211090907017102c0d1551564100000c0e948400d0a0180c55641107500c10b89031200107042c09002e041c3c0c880c0d00c030070b400100c2c80401c0000d031030224061500c4451609007860007003000c40170742820303400b03050400782080b01650702e00b020042c10982d0041682c0ca1a61100001c81c01840004800807140707a94111308414140d101010304040c0e403180c012881e00d581c03520300989511051030009070744118411f89990409011601030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 424146969 1250 424145719 424145747
    0x50a15020304180213060311070605183304080306040b030f010509010f2003011802071209050918030f0d0219051306030b0d030305071106010b0408010b09090d 70
    0x18030704154954400c0c3d0a030306095040302c110785401051402c80d000c54040003500070021801d0030841105c602c00000c1040c040c40340f02078802035442d03000900d10840009078114008042003034540c83d8841d9044010141001c580d400f07000055624202074400c110b0080e40d00642c1c010b1303e6030381107aaa04082001030203880e803407142c140c05805500501003a00b40a901d014007009800410040d2420030f040045684c80394042c10407040c4804000d500520080450341500c0600c000000c2e9004500c1c0044041c2c49002c000810040010ba68860007603400b111700c2080d0303101110310030b119481e428001c009005100ca1110f0454100300020309928480c180100112101d1140150a103070380b2091507900c2080700c00707411022440001c3c80070b50402000d0501c2000c0e0032541002c00448920340003040e1000308840d8014180760b030792000300e039815014000c0c01d9000f1050204907403841da1510b020340043e4000384110f00c81076082042d010028600045502d00c10b04000000b84000c26075503400319103011102c454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 424148219 1250 424146969 424146973
    0xc060c031b0f05011505030c04090b040206030c040b03040b01090c050306090c0310030b0a05151e040209040216050a031b0b062407080c0601060504030819020f0109060504140304050a1502 82
    0x181800103602800303108001e13031124034145d054038640424541800c3d04103642ca4820ba00c0c000880d400201070100741900140c0590b403450300c1c1d6442d51040c2000d071141d80c02c112056403022040000300940c0940c99416280c1d00d0348240054030728030310b0030b440d070b4001919401d501038103400c00200c0346030801001d158007502000074000300c0f80d5a074903294000e00c02520120b1100e41c5802c104003441c1c4c1e1145e464040b028040d12045950900071081d0405894100207030b510030754001942c0e044c6070707a454050f2140d00000305002d103559407840c40d210b81e83e00741500d0200c01091002c80015880c0c00e0149001043da40c00c88400e40541d910402001100d8505800300004001c15600c15001004000081c0c0142131052030069510640e4245e0719242000c140e1140b01000410001030000441e513800b5a440c0310030340e441444611a05c41016400e045007100641000d40c030380001c1800f800f409800060107a80a020712180c51005003007800e03100d11a0b40a0345800a400c05d82c208032007003090803440003410540c41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 424149469 1250 424148219 424148243
    0xb0910021e0106031a01032303190c26070206070204021908040b010e13060e0c0310091401020903060f09070b03071125060e0307030602040f030c060c031b 68
    0x144084144101c52140c05103079500e500c10300c00c00c81403c03008491700d09090012421903155075204a009a52444440c4d0712040c1c0d00c01c0f0091400c0c08009441014040c00d44003c0003960442d801080c0350803805040e00d5a0940c2c90200c11064101c862034070071010b076003000901c1c0c600035409101c0c030355101c0101241c00c181d08100803203c4003044008049031b03407001d039a009000c5c02c0c141080350303102406800c00d111212a00091000c14201018000096030f031066001c1004030020f000c1a0515850414080c0c05001c5c902181001c00026400891b25502c0b40b01e20421505d000165507080b4058550303020f1300350b40000c0110f040d40302915180f662080500080341c01e050388030303d0403000c41e40050f61000c0116900c8030f10b900c204181480081da0017040c64107100f104046003070142c08900c0c124817904050080e00f60222086840c01d03c0f44501030740d049079055564581e80e12701032454981612054841040751000880e000d841865400b00c0707030f505a0350340c143e00340541040c0d02c40004110b0b421111410032076 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 424150719 1250 424149469 424149493
    0x14040308040806190204140d050109141c02010203060d260d05190e0a0201050a0207080604050705040b0108190b010905030d09080f0d02061501181502070603060b091002 74
    0x200144003802d4142c000e000e4508001801d12241120b83e9141c1404034014003041c000c0d44020a0600c10801c01112402402c200c20b0508074010407002c000641481c1208041c006503090000e20b5a484040c00c41202c11702c01c001100486c201c0c0401da880075481007541c00481e02050410103182000c00c0c010702005003100e241c184018aa900c241310351910b0585500c02c0001d600c45404020300f20b450300400500c80584842211134443c1c2c030a45000341484004684000207e00c20000200038244c540f0448585003001d041c140d0361070341c0074400d0070b00c10350401d00c13140e80f1035200d202107501582483c1c2d480f5510201415002c40078020702882503042040c0c0c00c00c0002c00341c0e000c1001142c41586912891212070a02281500f048214100c03d1f44036400300070030403881d03940021101d50015140010307100f02d88800004985280700301e0808071004241c24000320b50600c1402d03030300c0c2d40c03500070307408481c911950703201d0503400d40d24103109803400b208061208035060300b003402003010b040c13883d84140d9038006206 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 424151969 1250 424150719 424150733
    0x9060f040f061704030503040b0709050301110301030521041a120711101b0818060403020609010f1808090a03080309030403030306080f071a1303030e01180e07140403 73
    0x80e4030051140311400400c100b4a0742100303042c506242800084082da103400e48018000c0c0c400500003c0882000740005000588102010005840010001d003c007280d00c0c0203010790347e007080c0000d030765078003801114400d0003e03040210f00c2d1441c42d50f00744a041c2480c3c4240a051074050303480c030b0780d200c000800100d6032105030001355a110320240d441d00c440c22030004920320b25100d01451003030301003458040800600c1007028141b661080b010b103060710403603441c8240b0b00300d42c20b4100801d003203500c1820280820903401240c920700c5010b0a0008001e02c204011410b070a450140c84070042c00000c451122012514031070042501c001e0140031130280c01d41c0c907620342c04240e10031500383e0141d41001ca01071041640c503002c0d41009200810040c4042c0482c8c07248103858207a41e1203800242503501d003000c1021a08070003030f00c111005211041c20515903c2c2000b03003040d02820800c500042c180f00b03454180802c1d400000d01a0380d0007440240240c4c1d1104410751303481144900c1c01d004007409000000010f00d003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 424153219 1250 424151969 424151977
    0x91703040e0f180f070b1309020f070302060f01050108040201050307020f0a030f0e0906060d0e102a05130b13030519060b0d0f020405040f230d02031201050609060f 72
    0x124518150741450b005000c1904030580c901d2254a41e000b040c200131145070000340600c107413400850140e51f101c40007a600c140c5d0b0011640a000d01c9030022400a203c86140800740800900a8003550300c196a402a20544603200b4014079002c140f0440204003d54403e40103141d00071018012260890070554406c0d02e811141e2108600056250401e01c2d0300703c2c0e01220041010340c054035400c105090001c001042e07070040f0100d44103525074910b0411440f404c108911040021400020820858654084001420407a05807985e05a1315503902c00303014820380c1110b198402081400d40980d044c88181041390340046800700911101c40340102c0401c0d018454513102c42c80b44003031841182e00c60f280500c107603041d2160355071094020440000118aa0f019a1140b0542c111070000b041e07a078920304540001c10100001e02008079000118001005144c00d081303071381d0080000c881c03181d4400070040b6078a05c2502400d0b8440103500004018a0504a002d0320400c00010725060818015034280c0d009500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 424154469 1250 424153219 424153231
    0x3090f05010912030606020d0219030507022706061206101107080604050c09060a030618081204020a050f0f0f0f060a0210060602070f06120603050f01090203060f0403091703040e 78
    0x607005003d451241c2d007520a0340e0041040b80081e20300c0d0490303014040d481d4080420400c884c8030795010260708051060382213038406507000b0310031121742c3e585004d030440f50305040d10101440303135510000c01d580f4500401602e03000301c040d0803916030942d42e050500030302e1180c91042d5410f1007010400110103c009010030805881880001c080503d05410300b50325001c2d226002c140240021414404943c443c00c02c0141aaa0810804140400d456000c1750f0380d0105844090002e8101280f2007000c0690344103a0350103103008131001c8070034035210000c21984200f89024207500042003e010b8072142007061901029032002000c0200b501d0744d034404100540d210002000040e0001c880140c41e484052060310003601440c402044d00f94205642e4482603500c50081c481032022001804000b1507554004401550f0300005640f07803104e0b07441c03a45000c0d00000344200d00c24050303180080c8440210032001413190742c00d0340ea00844580b401480700070780122450941020300080002043e540400c070f108500441e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 424155719 1250 424154469 424154483
    0xc160605071b0503031b0f01060308091002010c0e1519080915010302010512090322061d1503060d120f0908031305060f070b01030606030326010603090f050109 70
    0x7055854162070782241e2845040c00d206100d2002e22040e2800002c1c3c03809910000401c00c2e188190014451610395284d081c480e0560801001000b00540440030382841003044c0d03a03501d40c41d0b241007026802e90fa02903000303400041c60040b4180d20f901d00301088070100c07160203415914184034184c44d42a1201d1801892011461140610000e1081003051640030300d5451b8100c006541035600003440c070f1003006c0030712034030001030808102024024401c4540e42c91242c00d082d050041501220700303561810380b2420022030500030910090800e003804140764640020030400e03003240001c4400d255904007420a82c0c2240d0350200c07801c0020310000c00103080c45000d8803070603000d010803400108000c0139600050307079980040c02480c1280e20b00c0c44020381900d40458100d5103443c3c0d000000300c440e000f940800b40841e01d14000000500905074003034025a8003030b6031611812918008104010460741402c6008000322b00010806c9510036444000d01c01e00c03810800c014840070351980c2c2d0039030702c916200351384070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 424156969 1250 424155719 424155727
    0x70b01080c0909060718050d0f030f1b080307090b0705010902040b0609030607080910061403010f09020d0f03030605041a010f0305090c06031306050f150103060b0706020c160605 78
    0x85441040191804001121061070b90b203080462251104005030460090056807061080b00d20381d00942c0b503002e400c0c007804180000066050940300d260344075000f0740214010070703032000381948600c0d80c00b44811041c4002a40d010007030350340e207182c541c0300401200070009214070100d854001c0302c0003099014010b00c00410003094500400040318125415a03108220410124240351000309945900c01004c1c10042500c1d83e51070701441c00c0c8040c0d403840c49865481d10102250300038210f20300500310f0000358020080352807600130440807a112504069480104042600000f6241030300041e8650312920340852034a0703469020a003512801843c1000c0d02c2c004440502640d603200c1e1418014110901e07082c0000d003030000c00242c07245071071080355010707090000000306003181e100f040a0369a43c4c4002d00308038510380081803e44551055851a1040382090041401584640589410744124490701464a0002c1d41d40100a6001c1040c03200310740200c441c408400d40d203500b0504010640c50320780b6640c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 424158219 1250 424156969 424156979
    0x6060527120714040204051f021222080a08030c03191b0f09052d192105070608040f05101d03070f03111c230c1b0114070b01 55
    0x7510050907120f500481c0306001c1005140d80b103980c205815081c808201d402000c000804034203100d0703440004025120000303030300e83c1d14990300da1852000c41c00c03a01030300b49815202c101d81c507100c440c448800b6200c80e0003031001c40c000c554841b000350707080710310084000d070045444241001552004403100c1c00c0e0b142ea500c4c0010fa81600f242d0040e800c8140e500e84080030905040010b1207240e0080d07003c98903032012500c0100318a00c0c04010b085a034400034a2100e03941c2d4801c1440400c00404d0181e100c5195043c0036010003940c2c0840000350b542d91110140007601c0c1064001c80b50303204010001d880c11002c0701d8002c0045401401403a92401e4280b41c0401c41c02c0030058070300064404414850865841005101c0c04a00490b45c4905c0b900d6040c0390231901401031000d10b500e0900d8200707140000403262010f00758241c3c0c11202e44007640001049048031102d4807150004140181880e108c0c450304490940c0011001c550074030585074005040a07003000d10b0100014090303810403882150010258001800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 424159469 1250 424158219 424158239
    0xe0a02120c03062d060705010603020406060203070507050118090e01060f0501020a03080f25020109060c1d12010e010e010203010815010602030a0e04060b1606050901060605271207 79
    0x54009400e0245615600303000380802c005540030055000c0e000107814804204d85104d000c9954024001806241c0710561400c011b4001e2203c1e210072071149180540015105002009552000e81c008019008040c500401585d443c11581100302c1c500d454a803021070104902d209541d0351280c1c00c400010070608008001a603801c1c190071290640d4850348200300002c4e8490000342d800381c1102d00c840060b8603000e4101c00e02002c1c2400d007640c20101c010200540070b5056000f09903045c041d00d410301c07044082c1001030f207841805a000c41004141d48802e100e0504100300c0b01494541010000102407805007c510308481208402d458217035000401008082403c203c11054401005100526075140070006560b03413240000080600103800c0c0300704184d5032281c2c0b0010090042400e030300c2d0380366100384500c040740c075203000d04543c45441d00d0040b40414005100e00c0041c0c590030f0b03c032103150071000c001000307107229842900ca014005e0b4000740e411a48800846500d5100203000802c28282040728020b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 424160719 1250 424159469 424159471
    0x70f060e031603030b0a1203080a050a02031003020f01171302010207231002160603020d2409020f190801060801080d05030714190509040f05010305030a0e0a0e0a0212 73
    0x141580c01400712407901880091080ea0795a0f140c240050500300ea0400301d000e900b41580041c0480503007000d2101455000003119104000e1032800308800d5451184200032800241c0e0110300e00d01040d5014001401d10001e0302c051540141001c4c00b00c0c0b02e15125000066008650007440e0f42c104240740f100f196010070100018001c10765944150780c42c5401407840e42030080909c4e600c610184000030b81680c0c001c0c006034070728200782c034501d00302640c4611028000e58461008000200e01d014100e20400300f07004100300081c003081400036100351604040340f02039089004180b11010f420404481103240c0803180704c2030f198040c4c562080f03035850820081c158080c16804076802c0d401200038012090f6104040300d0744500142020484400b14810159560040c01402c410f0322020015220b90300d5000000340c81030080c11101404a408030305c6e64402174440a100041141c2c3c81071003c000d11500a1188201408000d80388456942e43d40e0b000341c0c0c464a00340c50411010390300081c81100300440c482a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 424161969 1250 424160719 424160741
    0x307090207020303160206120c031006110d030507050d050f0403020c010203041508040303140f04120e060403111f080f15031005090c0d05031308060103150903030204050402070f06 79
    0x2142481e44540120744c591107007054030340d01460002c2c01c0740119030f41c04060320746880300c040d00c0c003143d842d1001c41104a030384166449180411098000645584101210260800104060082d440c010711068000d008060102c209200081c045c2211001180c41864131850074901800314604007418082d04110135460040d0441d0401c00041c03006c00700c11400c2040541e80c82c030f00f000540d81d99003411002025012200c9080c400ca45050020014400781da841c000c40c0220580445d4820112081d1001044581016008031041c001000824840150400101c00c00b40540d005a14440c1c007501203840c401100740c0202d1115010702401201361000c9991248240348201561483c10001aa48948441a41036000c2d140c500140d1014010302252020010207000d000c5c1020840ca0030315100d802081e0f51152a09504000103040103000600c42c0c12030f1b410101e4403238451390301d014a10127400c11078401c0d4241502000b001541e520380d0310003072908078001d40c00007101219a14145080c2c4007000c0503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 424163219 1250 424161969 424161971
    0x403021017070f1b0b04140106081b0d020d1212150504020d090b09070848030613060c0903021c06150902040611030a020307020d0f020a090b030709 65
    0x4404440707003842101d0703504056681080e040414000500f2140d21030040c0d280ba103115001c2103241c04010300120964015440769040188401491402c80d088461503c24149258000140142c0c00c0c5481c0e04000d00e81720001c0c2c8000501354072500468507202d503200c003c4440e200c24800384140181e0101d8810766120088006104110320074480b685640b440d8020306215a40c00100c41d548590396a101c0b200140d408111880b82e89400c0c04030545400440c442c07603402d4003c881d0031014540c49014030011090000300d600e1400c542581504864180d00d20305002c013070104858000b5259030402200d4454a540099200d80c0d1000b440c0c0341c1c06460044003000180300f00c40c1070902c0142e4844841c2d035006845501c000c030f103d200d1360030004003406803041d6502c140707515280c02050814658000781700340c62440c0c4a09284010244905070b40f4400e0b0404080182c000303100620061925502606c611401600104160343d40c5800185108286a1010848581d9140344503840d0a040c08403500a0a26182c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 424164469 1250 424163219 424163237
    0x3090d03090b0a0507200d021b090103170c07080c120102070308010b0d020403020915040c020703030f050304030908100605010e0a051e060f031005041802130c030605041104030210 79
    0x926191400b8000d40580240d50b02c860000c0c0c003d9104100da060755205000c41d01d00324a01c4040080e032122a820502030050180780c00c00010810102050080b10401500d801d1080e8a0341d00c5508128528004d11001002c04200d040d45c82a01004900e000e01100c07800b170201c05140300700b04001c100034050140380d240d00502c030840110303030469a641c0c1141c000a0101d5910980709007800d000744500e40000354810465010f20450384641d0754110310000341a2010808885486400e0343d4548091000500180e20206405200c0d0310450155402a11a04000c494140ca8407043c5080580c1049070b042501c1e030741e00040005691116986a008200341d405041070743c1041c012400003030b00d07601e904005e5040101d0100e910b403140021520600d003440509030301c82c1408217000b14a250f0501c9094411030400c8204940d00c3c0180c001407180e20760044c5203040020441d40d000001c4c1c06141c105800b80347e0340d0700c000200c0b0b440e507014180c084d040c2d003441207540b18214070400c04900726010542c010819844 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 424165719 1250 424164469 424164473
    0x61602281d06090702121602090f04080f0706060504050424020415050c03040b0a09140306070507030c0c170d0305090a2a0f09020705011a10030b130203090303090d0309 74
    0x200320140c020030240c40d64005680d600105a140c1558514a820b03251000180382007000c0d5019448602c0307508c01c981c0400c15031250305628107010700c1950041c002d100c0800400074001c4402d0024004244109001309900d40c0d604000303022214211025500148146021840d0f0407078140705680404071140118240380c2400d5801d1040222204004c061050004072412071134401c100b0794000707006540b038040c0d607642c01c542c000341030640300d105150040c0c80b40c10002c0c80c54900490580e1251a441c0e96860500c00030740c800300d8034261070081c00d440c4030001c01400320744481c1030541102d640204a00428521b0030500000b8200c4038014a129019002100c031040013401d855590342c89000040b1110707501d44040c0d0300000c000c00040c1c2c0524802403001d180058048915005040d881e800b82000700010b58840707039103c01d0b00d1500f0803526840750074900ca640d681070090f1b0104d00c0081c0d02a0411751804100c0c0250800c0760b03c207803030842c0594804010000482d808000303141c0c0c1e034580c83c5424080c0440c0d90f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 424166969 1250 424165719 424165769
    0x5030f0301060305240f060d0c020a020102070b0a0f0c140f030c0d0201140403050715051e06010309030c170c150f09150c0d020c150405010f020c0c06160228 69
    0x12420186c840c451136900d0040694496042d6035049001106c01c021030460003002179603820850368102e001d4007902200060000c400001e076141d1a0b0640c42e0044103003c42d0008860400c143c0a084541c4079045004030b80b13001d8100501e05101c0a03400c011541c2e000034940311803524003810b00000441e81003005160300c41912035440c541041e0306041c031030b448020f10f10300328030506581203510000380c4c942410030003245c9501900b402940c044c80744000d29516120011000d940342d40e0400340c081001d46006d04001035003000107000c01320116036405c1c1092100c0060360700b8603400517580c008100590040c440c800440054150f00039862500411034141c0614002d03801101c01813031080c0b148004170b920f0108082a0301140c0304443d8020903140b03440445601d400350013400350b80c183d5080d881d14682c6803142d0014821100c00801a80051612081c0907080007800e5105d8000191038140030071000006854440da0000744111607010303220303070114612408804202e00e5002154a048a0072010380303050340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 424168219 1250 424166969 424167031
    0x8240c0702031e030c0d05040e0106092706081e060702060105090c07050c090403030504030e100e0f0424080c040c0e0f0a0506030a061a090319060905030f0301060305 73
    0x40000e80a5560b40f4440da00c0c1d013540540e8800c03a006001d06c02660001c00c0d0300c0070081c03081d1411135a001042c0c0c0d0303c41600f103a14030414018918054102203011029000d068810800545641c402040180c2c47c0c0a281d42460001c810b030f00f03070416140078140c03503104c000e00415521460340c0c4010500d40d85050005144080302804881e403500001aa6200740b0205001204081401411901c0c003410985401401402c1c00c481c181e000405015451402d807504c0c00c04100c404525680d903c080110030000c101200110409071a8401e9550000340840110020200006030080c84442d021900e840001800c01c14110b840c0c030b1185e481d00c2600001a60800080c03982d16030140d03001000c5028002c085416a405900000e42c070200110811410070a41c0d000741c4251006a4582064420803030b082e480c0c0750180440241d815000a550501442805003040d45440d0180d1008a001d410341d480342801d65229003071100038494000014400b00d41c00d4050f4507080000700f4500002404680042090a24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 424169469 1250 424168219 424168243
    0x1b081c23041707050a030503220305190e0a0324020a050f07020418050304090c050403050d0503070c0c120c210201030b041e1401051f030207030908240c070203 70
    0x1c2c1d8001070090302e0990340a40395034591000840d03c045840303050250032074000b00c0b001001e80320b9407001c500c01a0040d8002220305581601c0790b0342030003440e1b5410305410109040d40030411140a14002075907076546034003401140542e110500c11032008000704040d60400380682d5643e4010801e01e61216880300071210b030444100c00f040e07182c01d41480045c015016022070211440c0c000ca040c03100b40a40030009108503000e2040c01c000c543c84500041d9224080c504c00a405a044040c01c0c5903124081c10040d6482001c91a001441404960341c040d501e015680014140d0054003c03214200444400c1110141c0814040c011881c5501000c0c0b0000e0f2031003c2d0024101512480e000c1001e1315503030000e96a2a01c07903081074540b90312041010006015280d44014409000000040c89040c845581ca0341d80141c0000a001c845006a007500a5480701104034104048500002003a240c01c0c4403900015051010344401c44c08042056100240043d1030406990b00c10001c07580180e1f00003801c900214 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 424170719 1250 424169469 424169483
    0x220b0705070605160204180f1b0504110d09140d0201090b010f0b0702040c050d060b0702040c0305040201050403030c050307150506011d060405041503082b05070804031b081c2304 78
    0x308031050910340807031f000c100209050358209445042245600740c10110040d29008151180d80e01d904000a5910b505d0105581420400005c0005620707600000001c0e1701400e01039035058100a000d0b4a44000e400f143c00060f55a010782408101c41ca07d80c1e140142844104020300d28180004101079101d2480c0081c42a0b5a0700c0211510600540c2a242042c0102c00c0400074141e0b0f9011608040d03000e65401c0744070310b2810620b03c88441c000c3c4100c030b008036010b9460342d0600d4150b5070180c070400f5070301c1000c1d203888c0310920a0b070380024104500b4101034994040d0101d600d040910001d01625a0a0010802c402005442020680f1200141c40880b0803c440104003080302c2905c2200f0f014064201600b01c4400103080a0000001243d00000500c1880301002e81c12144060b10100d807000d5800c0e000040c0c0b0000800c005c02d10070300c1745404180043da81c1d130680d0702c2965a40c01d03441e170141c2c048003000c140d8200300c40d50024862054405041000c036104002a20a14040c580c0c8030300140000c01803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 424171969 1250 424170719 424170731
    0x8010c080a020d060906060306060e06030f01030b0405070e1302121c0509010908012d0b0a03060b01030b12010b0a08030f09010c050f0106030b0609160207060302220b0705070605160204 81
    0x11840c3c9400450060600c17290400c5100e8031402c0042c09481c441c01034070080380c80e0401c10391540c18460708680c45003c810303620243c2a401c41c0e0740c1605124000c0d100340c078248071350752010a560b41040c0d402800382c03020314a01d094400503441070025102c410664680c1903003100c01031610703041d19401c08030510b200900c1c05591701d080380c9006945104403500205065843c1c10400007488480c103400e0400f0700d41ea086d001000d16800b2510138262a000c0501c0303a0041e80f8402c0820000d0b0080c0c01c81884800141008500712689902251040315040c01511442e9140c22030214582842c030340e50b601401c0070703601440c034180800c14682001d00c1001811810003881090702803c1c00003c2c4019508415070380000c0c8845662030400710090401a114580300e0201c6902141c03951030404960000700c685900500130301d40c40c1180c150001e40004441d031a81844003a10200f1204903c023944018092000089480d0407040c01c00b24500203090301701b8414480c0800c400802420318200c2c103008030754100da000c5a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 424173219 1250 424171969 424171987
    0x30e040e010608100e060606030c090f0103090605160f020c01020318190608060f06041223030f071a0106080c0a0c0b07051803030913050a0624080108010c080a02 71
    0x1842d07160f0004010f402041001030b401c0d202c43d04008240c604180c21208283c0701ca90070040e8911099420400f036000412000100f07040c81130740c5080131a01410005400582c1d5260002030311741c00c43e0f501c5403440c0003844421000c0d801c804540c6440c02144010800100d8100001c3d603284281005c030060000750690f00e148603614940c070600305814600c6440045951400054858841a41c003a03109014120041001d42028429101210007400080c400c2030750710384500c0000c2d08250441014a058203182c1c81d5915810002060310109644941c2c0c3d594035036040805010292001c4425111309042c010042140e100712205c0d01b24410580d9140c1d5588400c205844265000c07100070000d0003000100302c1d105400c0700c0a071500030f040310050b2071040500310406880c1c0c800d425549030b100100400000e101d40c980d601465000780d0101d000034801d82c41e5820a004003954100305540491100c000d0180207900003407060040460b20000d00c50303841024005014074400030528000c880c0d01080d0891 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 424174469 1250 424173219 424173221
    0xd090c050d0311010b030604020109090e0c060406090e01050d020a030206032d0402010f23090a17010606170106020309040e010b0a030b070323043c1202010504030e040e01 75
    0xc00c401400400e01003003a00e400b41c400c8100d168042c8495103400440c010303070304001c00c0551250b40e050356104404c43c18811654010000e505004241e4071070321414081d140c03100d40041002d0401070321280d40141c600341140c1007010050300a40d0107240b0036030a1000507103c41004c0c8050340e40c111100340d241d0350350645164032621200c076583c01240303178980909102052807807950302881c003e907280600f000e0a200305441c011030050010030041080640803c2c41c1c241032010300144400184003800c003595414544c0f100e0f00ad02c03051000d550b50350300010003415400600605034060f030510a505990702d03000c8065241d0068520309070040b51900e5007203000d00e0080d031042125141c02003c2c60320a076160b041c00358408504868417000b09140c100e01156020ba406524001807060748001501d40c0d61381e5541c42034440030103a148500b0310401700d1040c6000c14002d0b804910508202c41c00105035070909003d80e8030900c020291096900d401c0038000030a502c1101411005001c1d54045410200c2ca44014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 424175719 1250 424174469 424174493
    0x40305120f0706110d0e0309090115020f120c010605010c0c05010810030503030f0405120405030615030102071e06060501110613140a060509010606030b0a0303260705070201080108120d09 82
    0x1007480741342c1100341030003500d131601400040041807001c0184d901140e090940d40d01c07441c0c04a035030100545004000880c128084140c076864548107071650110b009100500d8005481458090501c01040110100c5024440d40008180910301408000000d4891390074180c2c250141c2410094645c000600c140d010030364120095600808a0340da1b131a20729030008150340c0c192001c032464001c140c180202c804458017901e0584e80024080c0c0b9541e16080e07626110f02856081540d0155028401100400c980350501245c03440704038a495900004c920b481800c591458101ca418403650b51070521a1404c0015146e901039070a2002c41c1c0995541c0c2051140a402d01c0c5826180303100324052002001a03641000f0300500c2140c000303004140d01c400c415400d94241000450304020b10b903c081001c41d01c207105c149514102e070200c064281141c105900c000c064101da02002060002880c1821943d0101e512401003143e0030250880f10b030740f02005d0341e2500c81c086200d0301142e2265615814041006541 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 424176969 1250 424175719 424175723
    0x11031c030b0102070f06030e070f082e021219140609040201021f0606081803090108180109080909070207050f0d03030204080a030e1e1815090408041a040305120f07 72
    0x1700c0002e558440090162003515125400c5002d1a0301c00524181400a524141e03048400074209251000e01c0050000400150303802c0a50215030b96410595030501c014401c42404000f0768405242c024143c07650f441051012a0400d850822142c02d001c40c1e145620303421030341c12103444850f40c4842c00100d2404211300148480c404003034000d214252070b990702450882d04d05448031000e6541e0070900b0f103001c01c03442100001c0398000b000b480f102e07503110702180c41d441078055494260740a42060002d00312010036004543d14500082c9041c0c0c1d52402764406c3c3d03400f89942c4005c0c00c0c00d80c100400304006c124809001c9000c0e80104951404040c001c4d01650050508002143c1145c0000c0c2002003c0c203140d06401c5000d0091800141303068103441c0000526624050510100c0d60050b0700d008401000007400031507000c00f55840c1d00d4180da502026540640d01440401e070700c45007007580462000190240e0020900410030080000840201c0d03844e880e481901030b01a1510b23060100301e2503d100300980 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 424178219 1250 424176969 424176989
    0x20312070503060406060c020f09040c08070312200d0e01050f0c0303100e070c03120920040c1d060a0203040f06020a06050c0304030e2209030201050411031c030b010207 74
    0x108004140c0c4800558801c0004980174000d15503208010740b0300020901001c1d403c100c0d200c0b200103039030a040b110141c201341301d68024146a070f9550803450034000503030802c40385d0000c4070050103007550b404114101c160980c041c0000d500074550280c00c0d0f455000e151110240404070041c00a1680218161000ca10b42811220b6540240184083d1207900c1201c690082c0340e01807a0200c2e0951649026521a010b40d84510144000548082c3c485941d044c00d040d880360340f501c01a40c006880580501b01c01c014603003202c05065101d204000c00e4480041c100410030501110810300010b0300f40c3d44020340401550b20640c0d6605150080303045100310b40001360380400b01c84000454aa0000e6080007080c02030104000b00d4850a100030414072055601400003030100d0441c680794a0719040b19154443c00119402c640c40c91f00112000f5283c0c03044050300903035502c000300400d111490001a030703411404c90241407100a00d103a5a45600701c80c104110805031f0328184030b15264020000c0d94050303c03460394 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 424179469 1250 424178219 424178221
    0x30711030c1b1c0302030f030c0d060803070213020a02070506090f1215010b09091f050301050c070b0a06030f080c0c030703140c0405070207060c0507052701061701060f020312 77
    0xc2c45107442d001e80d080c0310340a9152061290060911100c0798031240e0744c03642c0914034080d00c041e9401455040a0256114040c0410094030309107030740d20800c0020f040e011b0240d512032031140100880407842100740c40000340100702940ca5143d0111b6074505451003101c54988844446002c508149a48200c05400c4079890680900035440003d4000100c0b41c942e10070242d980c0ca9371010801d90040d000307020341203002640807510a600d0702c0382c4c5e000745041c003d881c040519902e034002429110141c0d1505050a00020003200384600044c600e82d01205e07885091014510b0760340c604040201d01400a02544004920f407d035111003400100c9107000010200c4510a460781400c00d020340b040305842c907180c45800000350150415000346841079806402405105240007400e4034400300d0300c6c00c211800d001e11a03000c07900360f0320005034000b4030101c0000c06400200303a14914a02c00c0307040e003014061000398450b011101012034074050540e480351401880c0b28070781c06000d80c65405045001c115640700c01e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 424180719 1250 424179469 424179493
    0x405030913060f0e0712050a0c0f0c02090c090303070602071a0f150603190e010b0102011424042307140a02250b0d020c1006050303030711030c 63
    0x1805050800300c0c0d410503003261000401c01103902e18480e062000c1103000080019001d024080e5034060103500700001c901d05c1421901040b40c00440741c40c920b041e9510300d00311903958800c0d0315244818940c03d008904650340e40000c1e03880c20004000d400141c500190084454900b442902e202d9a071248065454210501d4540d043c4102c860412078402e22000004442407072403040c1d140540e1341c1c0d2070300c0c1003002c030240240400c41d40014802100c4000000c0381c00f040224034801c10603600907010000a0718a9042c00090a5400c22620020044c001b030003030051003c84107048059507044211010405840f007000702e0003400e03500d4100200001102640789103222002070183c8902040d0390340740c401ca5603102d90307403c9034000e54103d400180e22080044401504500d501c10807001c0c00540b0f41d05c0c0c1d81d95224141e400d07034818002c45040c56000304880341007140802c1560f200c01001c080501c806428600485c1e45c1c4d01000f0042c0701003205280100d089044240101c4220011080c195803d450003e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 424181969 1250 424180719 424180723
    0x909140604121d090f0606040519051806062704050703020306210a030c1a13050606060403022b02040f0b2b0f0510090c0905160f0311040e0405 63
    0x1000c84900450000280d403c0c89006100160728849801894940a600c49041c014400310000b070601c1c1c1c201c0070800c00072825036282d0000d450f4005c2056038184640341400240000c0b499403a004a0f050f140c81e03810721001d69103400940368200e0407103141c0000101114040c4841c2e1403e0407415401c1440c010500001c240d054000710720a000541d114207400503044c00505036a040e0f80c1045080b85c10158425001a200b41010740b42d4601032411a02d0008089100c0b00e400501640d511860b903d0403624a802c0103424469540d11050449125003058a103402184000105079512141e070075103180d030908406081c0c684082007603006403003000140c80d109154002802c1e03800c1c0b59480344443d202014528450b5013417182c0402c0f0025442d00c4c81003215610380d00500352030b410496090065200d4041107030f54902c2003020aa010344030682007140752a41c9401110405043d50503400411641c00b50380340d0f00f1130314010021510f4600014900c901c8054040c83d8010398101d20600c0c0c07800d0b000e00040c4000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 424183219 1250 424181969 424181993
    0x90c0b0405040c1404090213050402031e090a02011704080c0109050c180c04090e0f06071706010c0b04110f040e07030b0c270607050a030906080106030c090909140604 73
    0x180c800308070803c4520700680f183d190342d0391800200e02040005000c00ca0154026100284405a80c00c3d0003948a07070014040c0d800445020901104800510b801e110002c42d4058100300e035072010f00f807a0402c0b40c00007080001c20304044075881c0c0810000c207003041084021a64102c00820007041360b00c115103001a15030301c0c840126841482c80301c01043c01046582e000364080c1c1d0000d020980350602d0b005103031024091460503000c040c041c40d06000c1c0584001c3c0042c0b48101d44070b07640d42c200c01540030200004803402a21442c1003082c4ea0b940034001503207603400150459004102c2e041ca05404d42c0c00129025980c0719116001410414034004a2400182c188162481241c2c482841e03a01c40d6203107800c40c0114600c600350708455801c4a49044015403001001c4030300500420701e490300a0722131600c0c102e5030700c030304a001902c190340401c901a480404c89014000c11310b407d20030b07a00b0300500180707001a140618a0175580d01c82d00703070007080480303508444108802c009840c0140f50509081c212814 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 424184469 1250 424183219 424183229
    0x30506070207061814040b0a030c0f052b060b1f020f0606011107060e030106031a04021f17060d052d030708072003030316020c030d0c0213090c0b04 65
    0x40c0f920034081315451400f005416290043da20100d0a40d0440411018010045283d50002d92100000c40802e444805440180481c1c428800e2001d2818007400700c41d1a5012201e400c20229400054048492050045400350000380110790f501251000a001c07402c0641e1640d103900c11039001c940f51a0300852a100c60805120644d005603407104015580b0b036499000f042c3c1950083e030414800c6500540c0c61a000c01c8000d40000385094403555420f07100301e5503000d0000103031284420030003103144c694881c001090420800f071726010a6918054014280e01c46411a10b01402c00012110713181c06014100309034020048030b03008402c800146510140207440510321021104111210f814004211802039900c0814203203040020384441c1918442503000c0d081c01031560003d00001c0d070b0100046c500503400d26a400c1c2c02410903400180c03500400054945c000e8104103a52105580c01811245240350103980d180508025041001c00400a004000340b90a40b0703858042001c080d090080d1080e01c1c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 424185719 1250 424184469 424184477
    0x9070c0b06030105070206040807061104030c03020f0409080301180902041104030c06080402060f0a0315060905030c090417160c08151f090b01020a06290a08060f070903050607020706 80
    0xc0c954105141c00e139403007110401c000da441038001c50000b4010000820b00d060049000107022040b00305c7d02c01103a03210360700c00c2d901682c40c0d0700144150314000d0058469030a00311030420070040c0b6030359030b918035000501c20414042c42d145003003510304a09800c01400143d000344104540200c0e0401003400380c1003400103a90040742108081135090103582c03c1c80c00f0700c0d0014022030502251a00010710b41c0c0c00490440101620f0740e40d49400f02c1c1e4480d01190240442e501c90030441418081898900340308030004910400d80481840003203981d4801c804220080d5035822962482d0071041c50010700b0380202c0c0180b20800700140010301142c007040e910004074180d00a4485030700c8040c101c0c5d5032040c100040103048401c034001007200302c19aa10452030b1403010b0065485c0c1c118141c80781700440d004802003007010030f2020600340a40000110b400c05524084404814982c241413445e0303a41c8900510340704140c04081c2c0898001d40c06000b699000350342c80f504a55440c41e1810b4020340710051445110041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 424186969 1250 424185719 424185721
    0x11d01060501020d05090f010309050d0c060c0e0a0506070f02090f0f0f070e040e160306150f0b030114180703020d0c030c3e033c090f09070c0b 63
    0x182d0300c00300340c0354240c1c80c00b50346890804a220080083c1c4191209549060640d0354080c040011070a002032009512544c541e6400100325041400940304080352100402803039114420f01580c407102e580d0300ba224103030b90594451003240380091005101d0750001e075000100f031081050920b036000d1082c1c45a840b44600741c800380ca5020b90059080810b1f81c02c400410040210a019811b00da48442c4e40103a5a0302202c824201203c0030b150150314580066079880e403156a900e10400e030900444000300300c0c00080010325803900b8007094241c0018041d03010004000d140d00c4800c0e94aa511555030303404413448505550401c018082c1c029031105030072000c9581820406824640a840750323010044440d120003107010100300344203040e003024035040c0e008002c020500c2882d60351a1600c3c0070100e1100f000075030f0b80e4100c104c1154482003003450040034a031407200b4140c84198000e00701800c043c2c2c5124060b03450740300240c0002e82c2c101c052144207401003241d00412007500ea0207001e1300c2c2250b01954005c44a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 424188219 1250 424186969 424186979
    0x6030c0216053001020912070e010303081906090c18030b011403030c030307030903020708010524030102090d0c0f09050c040302090c041215050a05131203060503011d0106 75
    0xe032250301100c0742001c400020200203d0800030105408100c0c3d982d80300c840c071010300160600c400141008480c00d80e501040f8441030381400c0f00d00f0880305088000801c0d0451030060140a000701c140002402c100c6c14902081c4445501e100c08086440c1d490400d000b60764803085508024600c0c0c112000c0015580c0c442e0324003003000001540c0a903908022084502c2c1c1c00c000c1403503061308192081c29018402000407000401d8180003850140415940c04a85490103050003490305106400c82500360f490710040c0161a03000142540030500d840d0498801007440c000080d009001d44c0c540b0f5600b2604142400381001001005041660b00209520f81419203401001085610844003000c15031410002407002d0318040079020351110f01640308030300c0e02c0e86400000c0b42c03042d58443e040b206103188150050a46889000d04c40e03200d00078210400c094507042084020580703403010090506005814041c600900c25008030028020190090203850740d03203140c0e1728100800c001c0000c1036510b40480850 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 424189469 1250 424188219 424188223
    0xe040501020a09062609030403081c060503030f04060e0d02030a06050601030c020a0b1b07050a0c0929010c020a1d090c03030a080a0b0f090405010e211209010f1506030c02 75
    0x500e02c55600481521070000245c01102040a4100e0125100038040080000c04d9007000b0008801980c440c0380303d11005900480684400d0b0300700701c0c0700ba001880251010700d0580c066900b207031283e15003440c4030128840131560348240d07444040e40600400c00c456081c403580340c0007180148002e0380d0030446900b0740d0724100e8079044190401441000d41201040d9102a9180c03054a0320000c48405490001c0d6555074030301e08510030408442000758443d04100c4d10405128180004804096002001c400c603041c907880d0040190381181070110014104d0300755150490800c0c05040b000c2054039034031440030200300d8a840101c405203080d20502200074802d080100641d0701c0f006541d210200b032521615200c01c0640345420445401c40810b4a6007d016900c64444a00a9008100000310412001515030030641700000040c2d61810340d142141201c01c001084031904900ca10384880c00781ca4940c2220b015110186100301c1050800e04014a80310101c026241154034a88080000041e0742d001a6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 424190719 1250 424189469 424189487
    0x2160501090b0306030f01020a0c0c060302070c2601022d0403031b050c060f040e09060103120f0215090c0a08060f070f030e120d18110d05070e040501020a0906 70
    0xa00003040c50104000310b2201d03401441e00644003c099480ca100d50101d035608903008001d2030800100c0c000c64000030705c040c6040c020041d051500d8290724100c001d898058001e0614401c8244141215040043d070444c5411503003400c103011402275540791208204807156003000c140c0101490005100d5010301c4050b0411a0120780c0e168940e402da0032804c071500f00002611241c00c0da42030240c07105408440e03032144020700341102800700c40c907212070a22074420341454008100012a9002000510109074100000d41c9000d03901e180205990035554012402d0500c2090036420248803441844405c002c081500d1070103400507921240000d40d41d1350312320360fa150150b40b40d80c0300501d8003010880340c510401c43e54194a00c1130030041241c100103080c941c035202c03044040d209505004104038815049a0048203648d54086428803034824141d20768103050400020340c54400d030908555102002001c0c82040d0003040f02030043c405600d42800d00074040e51109400c4000522104c1010031042c1c0a02210303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 424191969 1250 424190719 424190729
    0x16050c0117060a030b0402010c080d020d0b010c0b0a020a0507020901090207060b0303073815011103070203120d14040609150911010c061d100f02040e0a0504030507120806010216 78
    0x181d400f061840e168031801c840c010b00282e04210010788000e01080b6003000038030352402d01002c0181e9464428920308229905d9251a81c10040740c0d070180e001103104441c400b0741110040388010f9845100034402d0342d0f548190390000f900007201000010700030305c03140d01402216019032828000320103840e0800d600e178403880e900149040e11003e10016080300509000d51150000340d0700326401c90b807040c44400454400c44210300c5500820312001c901e540c2c00114804d901d034541006506145440e80000c0d298143c50300c0b0b803103013801d000c07074028003040094021041c8486603c550780c0d17040c01c2070304148025000382d00c400d48074818070100d800203000940c4140c071a03076074001547e9072402284c90011a03040e1312a117810303501740f5128075001c40382140c0e41d8004140400806d0042c84400309000c401815200c90880c034100e11803052008101c01184643c00c1c0c0e80c00f81150f4000912a6078911303041da418001c286026102c2012140c024064540002c0028040c2c6e500741c007220b00f80d0b0316806030201c40c2d804500038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 424193219 1250 424191969 424191979
    0x6070525260706080c0d0c03020d020c060601022e18080c030a08061f03050402011106010618090b090c0a09030602120603010b0a08031c0e030f130608010819020616050c011706 77
    0x40440d018105170b2000704190210708e000752030010f114550320b060f071b08021400702242e0803002c01e0000941e0100309500ca0b0620031801014000560207001519125101c0554215030300e440d1505050354442ca05078200c03d9016219549446402908075a01d411240b000c0011074203000101e05180342c03a00c6ca05640210012440c0d00160464004802519000e0012414081d90040c0c2452480c2c0500285010b0a401d5032102101b0400d801820303810715159100c0419185442d803840ca036611600c05044d07010360075810859480c4a114401c1741c2407502d60b2b102618081c1701164400510020804c140e020310403c80092060780014020040c074100d0b603103d11416070340b00b0070800001ea43c0d46c03e98100c4401a10500141c080c50005456085610101281a00280000c0d242c0d03407000724803103500d003e00743c945028030310303503040444541e500c0c0c0c82006130384061444241400115541d60045444418104410b40e40b503c1d0701d807801d02e640f040e01507a81804114520180c004440c100d090462043c00300401c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 424194469 1250 424193219 424193227
    0x90209040201030f090c0602030901200616110609030307171317130315200a0c11040e0a0201030627020a051b060106030b06070525260706080c 63
    0x20054005241c1d02180b21901911910080d002c1b8405440d40c40080032690040c540d5505036030001080c104140e06281030f04580c3e841203d032201d50000b0055440040385030000f0b25402d0060050b58601d0718031b0000b1000703100c0c400800901150201c0694040e51054650741c03403201c2e002e00350900500080780c08180e002c9c840001580030950048460390800410060945088511050420320004c40e41065542c1710103500302200313030000c501c10f0b40002d020b03409008052502207440c0c04854480c1682c00e108020060950005011000c2415240f041b030041c810444200705000d0280c58080d0282d082e80440d1401c100002c9070315000c003400383c02c58400c0c550841c603044000d0301f41000350800001c400801c0303010b110b82102c0340980410405c4100c9030500421466240020007016210600c0120380201001c1c408000051000100e10881c1155905040d480b2448280b0039542024680e111000122014200d0108900303041c0036a950000d443c0c081c2c40ea82c1361180c400f52180344040d1403041d80124100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 424195719 1250 424194469 424194473
    0x5060c030702061605160309050a0b090130230c0f0f1c05010608090f0703080904200f0d06080703050d120204030b01330516020f0d051f09020904 64
    0x10074100e4040035800c0c840d080804480b541440c10900300000c40100d901154180324a00e80208400010079a00c40001c1c80d0212030cc00090031926881c018404403404140898546440350020074080390000c9410482c0620483c20303c1c1c02d98428003c550001c018104c0440c85462400f070496600404c40540c091410401d12140343c141d51040c4c030740c03400c0740d4240300341e0900e103600c0c03801040c1c02029942c2e509031007800e140b041a410580403612001850340400d030104001003407002070f245405022540041c8500b442c400d01405044080f0160b03d1801001450b41d080c42e420310050250700c48020030800010340c489400a6540d03880303004c083c0541c0e004120b6130009500c2403005c903500017500a40581010395981d00c1c0c880000c000c1e080070458542100311541d00c818800d60001140a46d00c20b24501c2600342000a400c41c1b040320140411b80f16505960710641d1190385840c10380d200e010704148444602410120f89a41d40c1c540f100c0c840d4170032051808406011400b030b020607581c0080040045403229 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 424196969 1250 424195719 424195741
    0x806010309050717120c06011d01050f0d11030d030c030c0914040203271c0305061302131e0302090f070504090c03091208010810090c03020d0303020f070f05060c03070206 75
    0xc1300c3c40302140b14032000c440e807180f02c043c090103400110780c0007001130354101040e0030300039940c040d41c21b060b400d1700300d00401842d6105035039611f000c9802d59080307010f0070301400c0c0080c0307120301100a10741503c1440c2079140c0c0759615038001004441c069900f00041c050114045170124070350711600640f0300f814806200245000ea000399040408240000203200311403003920001903001003502240c1d040f506d002c00384500c2c440d00603401d903c0180740030066440c0c210b0003d0749000d01c00b2491410283d02240c90b0000c155200e0498001d0002c28510400441c2014540d40c902505800201d000e21180c001051540d060503803441c0c0a440740d0303107510b8242410704014000a06400c0d509400705601c4160182c003040314885141301110566131102da83d5810709560030f151071501c00040c3c951a00d482d030000040340c240070b00300341920b50443d9041c0c2c0111650800300c0107030003540d40e5045034000006400041005840c40642c0280c490f40660740c0c542d0307604c0301d51802404202c542d000545c02c104006620740c102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 424198219 1250 424196969 424196999
    0x21e06030a05060d02120309091503031b010b0312090a12050d0c0203011b0302071406010501020c130222030302010c0201020f03060d1703010b1c020a02030f0d0e1005010608060103090507 82
    0x26003513020300003032078001510064100d24803803144d030030000e96407802c0c0c2003d01c3c40f0303980507000e5a0002450305240010994a1080c864050000281681103c81105003900700342180d030801812140c00c0d80c00002062440d6001c2c02800c3d00c5148214000102c0845100a065141e40c009010b80542c0d01000300c1036800c2280040202e03459540c615619040071901c200d501c15043c0150b600588601040c5032002050b4440720744940b45034031000c01042680e0740040c0d01e008504040c0c940c01d0390701024081020207406801080380a00400340e0510b080030103c2030180d0708a80c001e600074010070302c2c855001c0c0d00b03e00c42c424203c8004802000081d1260a02440c00c0900c940702e0110f00035900c10328019030381150004e0b0014407140c40c0c0058000b0007055501c41c488482c9a08a00842c41d011401d50080c4d6240b140034140c0c07460300c00200340c081040f20103a00c5213120310350980945040305414122240200000d0156601141212002c940d09512030711601214a03030007401806000d0074805100c0c0c1142c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 424199469 1250 424198219 424198231
    0xe0d02120711041b0f080603070909031101180c0906030f02041a030f060a0c020745020a0f081b0903030f070c030b010510050405060f0d18021e06030a05 67
    0x2d00001d110450303443e00d1203051282000358031090f401c010704007401082d09020419000800c065001403041c60358011806004845c3c8a80002030f850310b1500c2c0960344107002e045052000d5107080c500c100c03040840c5041140151041d200c14081c692521446000c03142180809841c0e03024038401c840060400380d2003803c010840c3d000c050002441038000911700480311402018682000f0140a804000c902401420b41d41c40d0014042c0360f4242407000c0400a0180300d1fa01403000c00d00c1c1e40c07a100004081c500e0000c41000b200d80f039100140d0070b458030041d5000942d008001001c6c4000402c40c0c910492003035001d0032102c030030000703800703481e454050140c0c1003094995894001000101c10100d00c3c50b0051035114480c0e84600ea00b1441c5080c1a030543c5816400726010302d0200c402c0385005030340402100e0584508650f82501c03003090740e001000600801001c400b1080c94052000100c0b151b603d00c01843c10f20848003456a201089080380104c8081002c842d0400f009201150710342e5055080190b00803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 424200719 1250 424199469 424199483
    0xf061d040207082d0405060d15080f0a030f0e010e01080601050d140f0a0905060a1509020703020309040605120a0312020918070e0126091203010f050102010e0d021207 73
    0x75050f41c4402400758460903049544c1103804181500c0c86640041409000070511403036400c1c20b160101017000e0b03109040c00c003c0c003070b81d45040c0c5205410804d1032401c040c044101c200e9107132450081e03045136551084070b0141c000c80c0b0012a440000c900c5248955003202040c3c1d207900d9005a14001940d12143c05000c01c0d0612100780318484000782d4030302c20611000d6201c071061189040451868404880280072401280e00305020b0340040f6000013011038000c54402800074100d4131018807003002c80c00a8101100403800011080149940000a0002c0100481d007c03c481c5689070100884c1c0b00c2c090304201800d030425207840c00882d009050321040000101c8015107807119010004512550107030280894500c030f403003401842d642c070120082030084203080141e02c040d00e00c16100051a40141c4600c4aa000f120010b002c009080c44030a09520410074215103a50f103402850580c0c000390300a20b40150319012141d4a0520009828120b2180e141c01901d800c404044217507c5a6100c0b100a4801c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 424201969 1250 424200719 424200727
    0x2010c021002150c090112090c05061b1b1804230109020619140301080c061b010c0816020303010f150c050a0302100e0115050405070908060115090f061d0402 69
    0x40b000c00d102c03074413400d40c48050581e44c822035000503180050304280c03000700038602100d940005440c0d00c1450b05940c4d088640940f41c8a00d04180c0d207000d550302c1380584090141460820b9004038588030b0070340e00c650450b00c029a40e43c803010006290101103d000d0044230b203170201000d030081c1c04001c580035400c3c41d90002c81c00a0b910740116945901c41010211204001d2a4a148282c2e0045841d8031180344080d01e18070b9945800103296032004524042d5109440001c0c2c4000310f00036600580c4a00300801e07000380400064042c01412001781152654080c50400b17810126152000c421a0b05aa13801c101c1ca020f002d00300f01c141044248a43c1c44941408070104107140801d108000364840c0d580b10342c0c018003801c408003503460141c0b400d201c5902651f0381004009111103800708550300a40d201a1400900d81c2e8494400b141c0d0f41150760b0200c01ca500a46002150041c2c40d440b0000e58000151548407029540f003801d441c00e18410311900000510706000380b0820306101000042d1000028000f5080c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 424203219 1250 424201969 424201993
    0x4061d0604231f14070e150d1802150c19020d0203070e1909020904060f0204050406030b0117060702061305070f0b0d0c03020c0309040e0a0b01080a0c0f0302010c021002 74
    0x54030350f5400501d076041c004000f601d0904203803800f545040c0701c2440084030503410300781009091340300b403145000d1107062100b60b038550001d00d0505807980301040c980c052004510b84030903072188048801d03051740200c4442e145006c1080c3e003c4211081201103000824a216210300c035004412609201260300480b803c1000015903020005800605602d100400301410503d0301105002e60b0903540800031401c0083d094090307503d42c08100ea00a8000c00082460040034140748024415078204a0b4454034004000c024055480c42a0303040e10307014158075081080c0c108016035a44000c4030154010b0f4004000540100701c0010341a901ca07101d08100c2d031065843e40f0720058000030076006400800d901141402401504c1c0c01a81e101500500b01140340c00398041a860f1240306205000d4025a118010f00001c148100320ba0103c050300900409500e5071542d100c0d0b80c0340c070f452640c259032450902801045000060b00081e08595050711a41c4103507a0560038003140e0b85100c00e0f04015405072800c1c5800d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 424204469 1250 424203219 424203223
    0x41b09110d05040c12050303010608070801050603190906020408070509060604080703080a1404060f12151203021908090108150a0303030509030d0e030c010e1c030e0f0304090504061d060423 83
    0xc0320b00d100700065234032907040400081021000400310020051004010403441d10381500b10b94006c0e4180c01080080c0030618401000b400005e94002c0c0150300c0001d00190000d0b000c1405029640d045441c17210700d40760b40003000928000c0b4083c11145800001d01000000d00d00c6008008004443c1801c108103d80e104903410a5045076100401181101080050141d40101040700f04075118000308002441c41624100020090151603060a244500302c002d05000304841e02a040d201c083d13165010806260140c000d40100b00d0343c50100e0b0481012850340c901e41d840405900d02c001d0070040459145d9282100500405000d003034113400100200d6201010314050f08045c1820703580115961a541074401d0b00b1641c5034000d041c1190044d80030084442078242001140030a03519001c18005034003001941031014040c2d18086500c40050b00090360352540d00628801c0e030103542c0800144010000240c040380c0f2904c1021031a401c920005800659004040c1648440340100c0000f803003490841c0038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 424205719 1250 424204469 424204499
    0x51c0f0b01030c021b120a0f08040512070e07080a0b0402390c0f0301060e010602012004030206030613110a0804062301030f0317041b09110d05040c 65
    0x244026121505420296094014150a00c20501c001c0401c1d511075020600c80001e000d134034511400c2008841100c18a0400c00c0790790840d049031605034074502e9071814544a611922555000301410100060103020100b07841048600c40c3d5201241d0382d030b0b0000c003141c06000041c0340b90803a0383c0d00c0072540c1c02e5841d6440070b05410407041135400e08041c904400c0d000b100801043e01e414150b0100016080583c0110300c48030011421358503031007142059800a40540500d801c0382001c843c43c1d0f0000070355180d054010140005402c1845941c2c1d4222414142c498810b60201031340000041011035082d05010b40c07010b01440314904009081c0e1800c0380c841284da41700d2000c10002551903014401401080d10880800c5505e2200300c1160300385604291940e00014840985100b40c1d1958920130f2500500b01e201800c86610404070f207900c0d1031f00e8000c40401c850604154006001c84021074000b10300c3c030407070b1001090214454104513070702045401a210003081111400e25014002481410021502c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 424206969 1250 424205719 424205741
    0x7030b0409150905071a0a050705151f1509051e0306010f03140706020606150d0903170a0605012f030f0306180103112e0201020301140102031306051c 66
    0x200b046200703410403a180510603000200b001d560710408010041d407840445141760304230b080041c1c882e40d1a040036814003040041841e0b10059032010007005074204101b0f01c1d01c43d140595a0b003a01c94585522908207020400a040441d501d09414400c5103420480841d90000b550707041a80207000c840402c0c01c00c0e00071390003948048000001442000b100e0410301c910440040c0042c08040e203044c1c0020355903980540194003407003413012100180c2da01c4000319030034424161003d008200440c5401081401c02c40780300e00d080901d95020401c3c0340c846d40181c00464005940c1c4184890500c1c840b80e6281285a8a1511000e80c00c240b580313404400340054102c1c0d00c00c001d10540c9a190010030300020746901d0549810307440810340103000007030814184941080080d02e6a060b504440ca5041d420a1900015080003c030900040400103605400540c161103208580b0043c102c40038006a81c0e03070140308056070124030780031818840584900301030000a0a1200c1c8040c0750711507148008122400301001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 424208219 1250 424206969 424206971
    0xd0c03050f0c0609060d020708040f0e0f0c03090a17040e01090c03140403080705070c081e0f07060804260703030c0207050d0b1306060b16020405090d050307030b040915 74
    0x60201c180244001440e100050314014948205000020104c0c810107002030445030f40800c0071014003e030201520081d01e041900605501e0300c8403c1c606400004450703101c506201c840000766903035403405c01d681c000d0081030010420343c0f1080e070321041c002610681030510501c043c4000180846280320050003050603400c005894107200c200102034038034901d0303e1200a0f40903020301c00025804034801d5402100f1303103009a200c0c201e514101107901116031015070700713202d160b01e40d400317620010020940500e0302104a44130b1043c1908101e0703c43e84103110b58000300d1000c00024011035100b5120018080045070955001c010b0320681c04031035002a2025800250343d00680009235804000b00b0000d420708903108042c4a00564840011100007003000718440c1c5810207808c104a182d03040f04010344110503041da1501e505103261503000d0b4480c4000d80c4187d0030440401d512401c003003504c00742101d20b690707801d00d1a558004140c0c003030049040025001903580410300040f911110540d030414080742d81c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 424209469 1250 424208219 424208233
    0x9080d1d0d17070e0321030f06040e0703060f020705010606170a140412170a0f0b09040f140c03060703020415110c1c02060f03090d03090203070e04020d0c0305 70
    0x299074a418448140c280c01d004010080403803022070380ca000707030b0310102074905500c030380300090b020074185412020400400100450114946403810001c1e6216410b0319000c0301c116600d800070001503d4404080f8405500000ca007400171604070b402001482060b00d03005072034900c00f0799403203003120303000e9000900060f2119089c003590003a41641a4200b60301c10410f1001e11a81890810044005400189078622842e04600780b9401202c001e003c0150501c043e29891800700f040c1d41c0a01400b441e0441c0032481d0136030500d45032428055103030281d40c0041620718a0503065440c0c1c80d620032000c904400300d100744850782125903003c1091500c6440b455030b016071224503000c40000300c00002448542800030142d000003002400240f0051f43c150b04441590208003841107030300c40b03100c014034042e4204100251181e401c00c5a40f0040d0300400303003103003250500c0c0c0c0b001808800321000d80d50300030362507040440100159008681840e40050006007030300e015590aa60313443c60390a881d8412542c6400000e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 424210719 1250 424209469 424209521
    0x1b030f120201051b3717090c0f0310090809010e0d030e040c030b030703050a1b060e060f09060a02010b0a1a12130c090b040501060c0503030a09080d 65
    0x180340d00c0328115031400284500c2c00d08281c61154082d20741c44110302c03101c004c608074a1a0300071405805c4280f582c00d00440700d80b544246441c4940b01c10b4031034900030800c01e90f4a0040b100d90340600512a401d004081c0107107190490401038414440e05040364907102e21030500148800b103100d41000c042c451020256281800c01c000b41066400c20011441448402d08140100f0f401005e00e0001031011640000c1400c1d02c10000c0c2d00500c0d103000700c80d815115003003000c8100311000034588481e9000d991140d26000c803140c4880c2c0305403a6400b0350030000f0042e02d0148900d06201c4080d00c210380922820900307099402e0040340c0c02d0381020420400603034441c03a519a050400071f0101000d405004647d60350100c080d4100866889004811903102841000141c0d403c507018403034031101c0d40d010f0129008141d0b608200009442603480e50791241385080c00004825001d0010205807070707400400b0b181980c2c0d889010800a01440c0010b444910040041007000303031030b41c0300ea42608281791100140308900382c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 424211969 1250 424210719 424210733
    0x190306090603050a12093605010830070809040b040209030a03050d06051c060515130906090212010c0801090b060304020d1106120108060a060f121b030f 67
    0x80d91000100d81d150050900110340c010400700038242e0440b885258000c1d08902c111040440b51344101d0482c0b000c01c03410740060905503224182d00c000c82907000c1080c111040c1d000c0c200c41083c400e40b0501e6101c0c240116034a0058194000362082c441008038050280c6510b40300140e20045044447c020000742141c45032829205840e88120155421410421090042030b50303a403203128054280400465800c901080607040b40018001c041c11110300340c0c1242d0500c140681e48200c0c101c5446082c500003424030504590030b10529100105400c00c442c82c503403a00e0b001000420820f4424079100e14040c4050303203400c0903494210807444000207403520a00401800048103030040315140b41000348410403581c0d10016070350801d404607904881c881c41482d02003244c6e00b912051540149001c218000f01c1d01e1811032450485100109840041d40c40b405000c040b516140116a2070804984042c00202220441c1d0902944a51f01c40c85507910000b401d12511000e40d481118820301c0150850200441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 424213219 1250 424211969 424211981
    0x603050f060103200f0406090e0f0f030a03240305071406090a030209131b0302010e190b0904110d02130b070f03030c1202070c0609170601050609151903 67
    0x80d6102600c00e55045940740c00d03901c001301d010348040911115450b0503982d50340d1050590350000500411801f0b50311410040a0300314200301000a0144103150000f61801003041e44802e400d04002d5860300380d203d04140c0040ca05031400c10010411401955020070303000e08100301840c019801090058641007240d9042c3c0040b9a00f40d000303140c02d02c2014230030b03101e01c0141c6007560350454000c0490754808008400421116501610810548608492440a24200200b84e9000783c0c0d9400c11503c1040911140c9031240c1009440b0703080741402000b00003294009005880c02c0140b000c100d505004e40919442d0f0007074030205d00007940c0003604001248556004200609062087d0303030910046440300103440500e0540941416242c008000c541485194030103d0a904203000710745498441c1814008000a40505c402003070b40108045240801c01d500050b03144006401400c580e82002c060142c0e54211800140e040a9110b120b80c800e680800c02900154603612080d41038a82c89103001030583e82 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 424214469 1250 424213219 424213243
    0x80307210c0207030507140906131803090509160f1d0a0801050a0e0c06040b030408130e0603010501051c060b0307150f0305160f0804020d0206130801051f0521030d060305 75
    0x900141c0c1c07403a510b81d4510365900844c111510301c0d0170522b406407100501500c4c1e00d82400480b40400502c1050381143d100400d807031069a8840181e0f0390106a9104020508044004181800e243e00f00c0d440c400c1c0c00300e0301043c121619020010031801c0110f400031110360006006039441e001081282c0085210b20b01409102d00c00a2021590300404a0720a20541c02648031041c4000f00003400c0c00744510407204c204150506005c000346d5110008600200300740c406d180319500344400007410345040c0d5900c1c0c0000045500c06011240c450b5034450040c03118524403909030284540000b44484641c4031110706101d03540356000c400032884401400c403540106024a507019420903014955072000300141080128203050821f61968000039800180ca194001d602040c009000036040151400c800c0840fa9040024032080e190020006401101e05888403000115148200300514200c0892201c500c01c1c0c800100d641d5401c0308015080d644042c000d0184a80c95240030803c020041050f503840755 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 424215719 1250 424214469 424214489
    0x308040b21040c06230307200109030e10090503100c02070602030a020624190f0b070b0a020f0705030304121101021903020c030c07180501080703080307210c0207030507 74
    0x8501981d6840e8007444a00861041080d0b001c1c2174001c050b1400e03291a100e0008159450322460680c2d4004e10020071800004039291241100c40400b031014007480b4822903042e1100000000e24000340540340c0c8a83c0c00450801c441080005a2602c061081d184015420080400c000c0082ea4001c1d280c14010340c4a882103600411013944481d90114a25401c012070060803105080321b12000c22016040e0003c4550000c040c06908800441c0148071030b0460301400990041d49680e409a8090350040b48001b0b8409109100090746102c03195000300351704c1404140c041d00300551502d400349180c1041341c0884002c481035201c54000c40d04500c0c0c0000d0400030100a500d07201000081d4511014501e03d0340007459004102404580740920954048491034400c54120a664264030b0352024100c02d04641c41034a004004981c4030f4020840b84292078020340400d2940c0c4880c80101c0b99490842030051640003071402c2c0500d007080034011071000345419401401c149056080c00d03424078104d03520460b029 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 424216969 1250 424215719 424215721
    0xa0e22180b091c031515030e0c06040303090905062715041107060b2719200a1b0b0f160c0807020a080d081f060c0f06060308040b21 58
    0xc05403c43c0c50140040071841d003c999192400b038a45001644c50308000046818a0b5040c495694190700c020624080f07042140c13010110b803c2400300c6403280f4040074002682e08207061100c2c1d01e2982081d50003007405030001403aa100d0400c42c214007190402e20340184802c0d4802c3c89500c400e0303200800203c03082118100561081d6403640c25441c492808000d0803592194003003000c959a501d19166415240261485910500c600320000800115400a0544042400c0010703c5c4400c0c458041c400c00700944410303c0c0d00c010386580c002c0d9084803512408010b024070b170007410f40400005040c401c5200b0902480c040c00c1400040c00901f4005110321003500c5c0d5441149801540306880858454100101c5a40c07921140085402c0c02000d4011134180d100313458450002942c003521309480ba5540400c00880d0b0f400c400c1e803c449a100e41d214800c0040c000782103172408038a004c1490601c041c0314502c000744040c0e80341c0d00d0300d1158000c6c2e40034040d2041e001c60300710b4040c3c803090b09441c050106d208100c502 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 424218219 1250 424216969 424216993
    0x1e0105030613060f090203030d2003090618010b130c0f030b06040b07081b0c0907030905030a050a020a2a05060c03040608040507080f1c050a0e22180b09 67
    0x1102c0600c080541000e882c0c040842c420034166111076603464015094940e10300c50b40e0000c0300941004501520b00c1388403503201702a075100300c209881c02030044001416103030311490b4410858040310940003915542c0c5030180e1009640c1c20b50503a5440c4500768002c64450584400604200d00b044020401c1c507007403001190701c40d9104800c590588030040035003502d07001030303050020300c074015612585500c64140003400001d6a0008003c0d407140421558441c259603012000c07410388403601e20082c01c55000307116a282e058050005021805c4051044424040c420303110042c203840b43c00e407008030400f11107043d4458070b005040c4d40809018155805480d054501400d03e03600e10680c424070080003160004541040024003204008104200444031442041d55000b51200ea2048428030f490310b1489000201500a509841c41445291960f003403551058040c0b1211481c01c00d417122071511000040604440c01d0304c03900b100f054801010512988991400c945a14000740a068182c0c0c000f0491042d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 424219469 1250 424218219 424218241
    0x602160b0313031103041a03010504110c070303080403110d030c0809010b090406050a02070b010b040501021009030e0d1401060e06180c072009090604030e22231e01050306 75
    0xb1240c1c2d2501d4500c41481c0c207001540c0c218001d503080300c49209411000c00d1201440d03c00914142e4204a408101101d4105000025445a40100310540e080900c0800101303004019140c0d01c50700038280f400891000c001003506007008100c44d0008255501e40d80c2d01a01da101d041140c2c0b200f4100c008200c1a6411400a04030f5400144024081500c5000003222000250107035a00c1541c00b0940004950b111a152640c64000e801003a0052250f00d40c1e00c02c007100700340035250304280c054a800d1030a10074117050006130001c8650542d490ba910007407070034980c0c000348244002801150300144081c2800010400c080518410b4181c060b8588018008206020b5084a10b042d80c040d050105402c24001200d070701300e080c280c500745e0050000007005011000410220301c600c3c8213584520580c242ea40030807410070020b0201c2910055888a060660043c40d404010000600b4246181914003044011680502124100c0100c4140807400314543c0070244c0d81070152404030003920003803600354000c01d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 424220719 1250 424219469 424219501
    0x2030907060e01120b030a02100906030b0a0e0106030e011b1115040c0b0a091e0306050a05010b1b07051e0a0803040e04020402091c0303020301080c040b03030729010602160b03 77
    0xd480d1542e40c854107840c5d40e0f000c101903206164080c0c42c01342c10200001c0094181d040500c5214082401c2004040003490508520025200700580343c10499080080450091810b809038035595981c85110000e903024076451a0880320701a42c85070050320041d160300d418100e91030040d4459040007801d000026609000080543d21403044440e1110010102203d007031006522645001c03000c25030310880c0c2a0308100c60401e40b03026010a0150f074490284000880e0f600344624075008106000c2a1541180b003c60013001504c4a0b003294011b54640d00004e5401542408504105000c00600c2c45141403440341c240040408601450070f291608403100306441c00180000d120319800511071480e03035100040480c40880c10a9080f05440017031074050001c0d0f1081c06400c409101b0407034100400d1502c0d000c2c4990082c0007601540c2080c8150b07851141c5402c1c4500f07060340f17040b04d81c0081c4e80c140c00c00c200040d00a0038150700801c090400c07100c44250780b004075080030307103401c9042080242800c500e003010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 424221969 1250 424220719 424220747
    0x60a0803070b01350607080c0702090708060103061a0301030303051e06010c1a240301020a0c110303040312020a0b060409050c1905060406030f0e01060f09021804020d02030907060e01 80
    0x4207410180e9041c06412804410850300c1034441071150380c04e022580050240c0c801c00e07003600d8070109030702c444000c0e80b007038054420700035404000c03000050802886841901d801c500c1c181804200c0701d41b540d6a0481d8031030360342004c0d0f05a400200c01002070680c1800341d0340e0822010045c452044120412110501c60b0013488641071190b80d0b261b10f000c0050301e400d00542d155414481d00804e040c50f0850642070700c1d2900027107156100b0341450606500d410300c2242c13845407040d11840c3c9440c160b07a58298080c0300502c415039160200744000000f140c40c5403030441f100001580900118641860401446600076040602031440c080003880090301c0003500078411030f411103044000c0020103058a410b0b90745d030b03001141c00800c0800d000821907019040600c20341d030400410b001d04180540503d080b51551304c00ca40c203462110100300310703840d000d0b8020300c4032a0140031404502401c11b004a400c0e680002504801c4c01d40c0081040a900c60610203900603240e50316100d0341d0721080d040000d28420180100d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 424223219 1250 424221969 424221989
    0x9030c0411040303050708090a03030c020a060f0f0305060a080321011a090f040603050106060c020103051509160c051e0c0103060311060c0a0c03080a0807030c050a030504110901080303060a0803070b01 88
    0x30047c03188500030364036100e000500c608181901c03490020481050300800302e0041e01d102d9804501103000e840011548140c540d6020ba2450741040120040c00740035100340e8115802101c0800d844405200800e2802d0703070001c2d01d240c0c2101d8003890180c82d11050740321000740c0074041108e000d5000440704036840d03240100c0700103000c1800340c030010300103240701c1d440180150b02c0e003000065000e41000a41d01c0c018000d890800403a0b80303078081000041e10700042598026140e40c0000d001c420428043c091078451450815800c1d0a43d80e9803500d880143c0da050580490000e45020503903608101100d81c0500030f1800b440788030300c1c65807001e40036241003211600c0740e140404c0000c0784407030400c900e2030f01541041e541c011043c0d40b410580c220750f0141015000003504240010307103a03070181c090040300c13500c940c0c0d8039444c0440b1101c08400400d0081c0c0700700c64252558028640584d500020399000c0d110b804042e5179a8240310b0308101e0b082c002c0768054455900103002c184040384008011a044440d0545 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 424224469 1250 424223219 424223227
    0x90e07030e06040624050907080403140c0307021302090d0602030604020c0a1202061006020c10121d33041110020705091806040312061a09030c041104030305 69
    0x4040e400361041079688003461107103404000c00c0c0729407a084209001e42840d2042d02d04c031500c1080d003003000b070f56002d5940c2055020011503940303072080000a5000d802460007441d001c220060190281d031140600c4070307080d440403036420254604440200100e40305501c00b18900038070740380451810640e42001a081a502100140e15901c454040703406010840041d602414a01d2070040c400070944003081005102d488000340760041d18983c03001c1962580e800404101444100308000d100c9000048070402c51000315224881d2494041c03028002a003000c5100008021607a1034601010001030007101502c902c10050740f071b0740154807144d03135154100c4540b00f02c0d529414843c80c040e40d0302244681040203142e0000080380d02040900545004940500d0942c40b000045004054818450749080c1c0002c000b04001900803400e5000c00c080324040031030700b13030343d1a15448410144007000c84d00140780055012060700d003c1c000030140480071602084500c01d040d004088034001d600004041c001d0000f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 424225719 1250 424224469 424224481
    0x1509081509120f031f290d050106020a050f060c071104090203060f10050303090f011115090a03020c0a0b0a050304030e130e0105090f03220312030203012301090e 71
    0x88550b503400000b042080d0b99600c255600b942e01d40d030085460007062492401c2c201001c4000702040e4045549038a01ca142103000b12803041c14819a0300005286140200185424041e087c040c0d64002d10023900508046412410070506081d94460030a1554020b0b800b0002403411880a9a030003a070403900001e084c012034004500100786410002e5414415581044402c00d94806901c1c45003110105941545640b00185039a0303004070b5044603804521401e00c25000d5200d20201c40542c3c40c1c40e4100e030004190034076800c00840c1d0507540c0760210380000240301d0034150100601703080d100040d6044228a8648002d100c4a80030304241714042000000200e803c0c5072242071014a5020300600201c04003c0c145001d0005101c0281c0f003218a50810001a41000c00070502420070311100c006545005401c008652000c09069400b100700c00c1d45810100206494049034548032900392401a40d03941461450710940c00c01404d00d883d95007480b82c41e111140d038401419000c0321410380d00c00d520364841c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 424226969 1250 424225719 424225723
    0x120d02040306021204021e030c0d0614010b091905090f0403050d0c03060f060302090a050f031f14092a121504060b060c0309090705090a0806011509081509 68
    0x160700c060001d41c000304001c4540e05003058450300451088802c6003134201c1d11007144119901030700842c0c1c0e06401a161407203e80c1010000068030502c1401c0c00201f2036804043c9090440c002c0e08144058203000c18403110b242022940000c18803609036102c0e401e1844d0000041c10400020800702d12904070202007010140907400741c50f814071104a09121541b184080100106054401e01440810f803070030024a02c2d00907c206d0355500b2002c0c1c03c80d100c00741000705010030030000922039074052080405401e541806a001601c5628070341c1000700311805801c001999402d4090284040b540080401351080c000d84806011522560010051440009800905401460210550b0718000d0310900c04503141e2007107174144100d01c6100d0070440150b4800038400d441c0900e11920f0b40d55802007244800a01c2d1900c0d074142e129055107411450a41540c011905044080d40000595486400140308518110450b59150102072178514034091030843c050b40e0321010f45840b04030456800001c98414441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 424228219 1250 424226969 424226977
    0x702030f0d0806091602210c0a061406100818190f03030f0c200c040e03040f120f060b0a080d05041a090603061302070c06050705060a0e120d02 63
    0x9144255540c00c44000e0002d022000704842c407522035400c00002034160303442c00d04841700d90611640200100090300d4040060381c2a00180c01000c0c680903c03907140450010440e01020511a400100d641404240450408034014040502c07400a8030b8110503589e501c82551941f0030158008202502d81d203204040c1030160140341c00e0741040c001440b28080c01400350780220890b00c255002c1201c090075142400c211043c0d40c41200000e0700c010756020b2091880c01d100c60724550090b09641c0c6014081c0300140481d2211034859169420104003000340401c801c000000506410104810040c1c196846860710b55a0074001464940e0714031203031582e5210300070410050500641110345040100318023505d0b580080c0700302d84a070140c4c0421303036800c03540034820303104c00c4031018010b00d08640b201420000d10382c40310081c801180c0d900f403004034040781c3c00301e4002000700360503103c05070b5500351420130f9424900b0082151040c141070492500d0000c00020b0011020142c0e40c500544a218113220f19001c8c0c89 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 424229469 1250 424228219 424228243
    0x609060b120c090414160c0816060e0a06061e06050d021c0c030e010b030304080601090509031e04060806010e0f130f091202150124210f18050601030206070203 70
    0x1140580045038001d6914000e8016201100203200e034003880101120b1007851000010040d40051207410607040d027081100c244240328020100c1c0c90302d00c5981d071a01d044945d290031341e0500d854072002c00003140d0680c0411605040c240e21044454100400a130007071050460035920154006001400c103000f0310f090011821514100380702c520440e10005010f003a849000402079407034600c64984601d000000c403021241400054040e580c0b8002c18207000b048014500c2403e404100116400140a00c0c5880c0d00e108110300c24986403410000c1c01407607110010b14050500030880220382540e0303541c86207c08132940884880c03501c800d003242850054011401162012410301c8030510810401031141110324205600305d5a440307000300004c03041b01c8820300c0703a106d0401010806000c03141e54140211200b0325141001145004030640184d03000e00314502e00c10b000350f51980d1240070340074640189200d07000c50a0108500c4c207459100c1d142c03249010302c0000d11a0700c0c0000c3d294219107090000403040c00f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 424230719 1250 424229469 424229471
    0x8031e1207200a030c060c18030818010e01050d09020a090207060902040f1e09020d02060a081f0803310e04030e0402040f0506070321060503010609060b120c0904 71
    0x401c0902002d0070007401410103009603291240c003a01102030004000c41c2e1503826594007190203a0b6502c8010041611807000c104210002d00205110700d003004000c0019803007052241d9032003203ea0f0350070411f01110b1305030314100010424010b501c2e0b0380c008255480c0c03103a003c0001030b00031131501c005940d05d00c041e8090300c90140046880c01c2844402e0384219100e9000769424441900b00c05000000c85002d0f103000c0c1c0014034603a820200031943c80d488903600230f201400c0720805400c141c00203446a04141c0114000804110030032a07046598140646141c1c8603100340c0c00c18508294100b40c880c040d0b1800c40710003031200c4030703d0006100020040000c1c8404924001e8807962910f102c40d2511004650030b0700450b1200b00c90300343c4d50030544201c43c2220030001c4941901400d0000704030081c3d02116041d420404c3c42304010902d6600030f1080d00012800010002c0d4007450030082c542076482580c8913000a038a032505c10013020000c01d0840305020400003400c8403076035031241c40c0540e50007020030260b041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 424231969 1250 424230719 424230721
    0x120115020601091401180615171303080103080310030f0f1a06060f09130903080405071d2403070905060f1e01050304021311040303120e0703020f0f0d0804090e030408031e12 76
    0x180d420641c3c942c07080000d40082d01090350b441c0d0407400c01252b25980100040d01c102c0040001c1003940001e950081c52200380c030113440c1e030b507610b8190000360956004d440b01008000120200580c1c00d20f441d211400000017812549402da000034014020144040950000000c103150217964501d0300ba622112a08010000102d042c10014440c4000f1542151944122580421501e10601c00e0b04015816021040d40681d03920900700102404409a20303541e04170302c503000c41103941c03e1080c0c038080d0050010004151415004012000d403031403c810f030041405c4070b415000c503e00001440e582000a01b0480da481d15244003180c0041d00800380d11620920f024411038004411400903c1200c0c00f0382d07034902121080180510445e0fa13209202125580610820001420050301840041c24001c0a041c8442001c002158402001c004c0c219415540058140490f01c0e2074440c0c1c1c0305610b41103004500301828400f50035034034402c0a400114100b02442c03030700b0340c0307400b51030445a8502c01006207401d2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 424233219 1250 424231969 424232009
    0x60513020301030c0611120d0603081603030c0507032a08030109050a0501050a06050d0c1215031403090d03080901110d090201030f02130603020904021201150206010914011806 77
    0x750020700003181c4146a1103000a80c1a2094642504041d03106020700280404041158090b0b407180414038605602c0381400404108100c01030040ba203046500d5410402c040c1c580102210110910300050090501280c0086030340490300b17a4220b2001420314181e00c001d607800ac1c0d281690b0890080c42c0c0c4500000101c0e80c60310941005000d28001c54090110340d8a0b5010010003914900400300008d03010b100481c0440660b41107040c0704807060600c100844e4a0443c00016a900700c40c60000700f9410f014200104201414190260000320340618200031508000800032064050090200702c45440410300340c202c20350000c404524441307021507545c5040c031414409081040000ea0119140484202c00c0c0d48036402202c961510728280c110405080c11015802504407451480d0495401c0c042012099000100d00d4080c281c0e44458040ca0061082300a140c10016005104076a0420086024280e03a2101140c1580c1c0c103640300b2941e005803001c00200500d6184d000684031003403a8001c0070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 424234469 1250 424233219 424233221
    0x3030a09030611040e27120304080315060406020d080a0b03031b150703091103070e0613151d150906010e1807050301060201290d02012c090106080405060415060513 72
    0x41c41072901c865a0001224802ca5261540c120314110107c41d8010000200001d4030b00000310303030003243c060700708050110160200390203030030541290016074000109011410f411038041c80e4000d4800c0000d00a03080010301003900c900400c118000e06204040d60740c45101020b01091007038204404000382580790a02c0d00401074070040105491192801c81c14a2580c2000305440d000e480c0003030040612515a002880821000d201d00099416540c224519241000421b4040100f4100700c80b55895085548800d9603400c001c0c10742c2c0844030705080300c18000c1d240c01199035805002400c013159034140f4400030070300c44441c59120701690100a0708201318182c0200241d410707124030b41d001b0496903004070100417144c9198041140001c0e0003208000d0075103403d2105048861041c500351107085c0a03040c00b28040301251031004580b8408049103a000d050400e250740c0105030070700d410b49050806464a984031000a04058800800d07a84030001340a0a030300301c480103010140c003140307003d202d06a030303d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 424235719 1250 424234469 424234501
    0x18020405010e01030c08180a0b04151107051903030b0324060301090201021b01050f0a08160801120b0a11040803030921030f0411130b0f03030a09030611040e 69
    0xd804580b0b018031150301ea511a106108003400c0b143c640981340e4072150b0300340d52403109109680304184100900c180000c3d558210301030189100e042c22988405900e070300c8000307559984980040204c07052014031b020640c0022003503640b07804445142115441402c1c118064000754102c290944940520101f690300f240700c90140c0d00c542c00480e042d998640c0d600b0542170ba40c2d4080042c1c0140d100c0201c09980481140040b100020141000b5190034045c940210140c0c100410000110b00b100713040080d040b07042058030005844a1510300c1e819030600c3c010080f001500ca40281040403900000f81884c0e50350b0344a550003482580006841e0390b5202c401980e13a500441e1048428021240204506503550f440c0040810150b0425415075850700e0b80e546030002e0040040c3d501c4601c2c072100300c0942c0c544541c80ca1161019000204a2031482018000f000c40648800c1e4042d900821071400d01640c007460302810303268819004100411043c031b020a0310300458204d8079038204418203000b030a01207601d000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 424236969 1250 424235719 424235729
    0xf030f020105060f0312030a23011d01030312050709051504051306120f0c1a0702041d070b0c03070b0106090806010602010605030312070c1401050a06090204030f020613180204 77
    0x24032181d07072030f030b402e00902d2040c0e0610240c155001101700d407204507504001d158400e115110009009000620076040620484c03d244124599000140306160401c01181c1910741500003140842d4074643d4020701175050404000b000030766560114441700d10841102c00280380040540b0030070721842c84244031692280c49005d2045255006041402c149c6025000c120ba1102d001011511101d440c5c030b40400440407422100c00400380d6010136417003012400000d42d01511a1915110801481403004640750b40c005806c44140d0301c040300e4070100000030140140c486880303c042d182c50740b00075094a50300428200410314150b00001044030755114450504032a640c6048440503644c0c2c84040c1d00f00d84040c01000e4058000304084001c0c0030032003411580004c2c0c50320b8100e003103420135180c111589204841115aa946a10a000584609015600145c21030003021498a480d50341c404940c2035094100038050f13400803600d80440b1064495031401800a400208401f0400d82034240086d4814011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 424238219 1250 424236969 424236971
    0xf131b110a0804030f02120d02150612120d060e0a05100617040204051009020c010b0307060f021f060b0a020309091e18010e0d031401060e0604210f030f0201 69
    0x603a04203000140c40001e054015611600d4141140c444030340184807904140d0b00000070142103940f6113400c20100e164003d2a03070107011030b10610740c484040501c000e440c17148a1a12001400c9000b40d020603a0221400c4184219669400310b2030218007410603a48440c05600f800340800065101a4000a210b600901f00c0415190386035041950300d00c00349100215500180c1000500504040e80419000648409410714440d503844d2800144c0c1c1c80301c600110542d449842e008000e00301048100080c000d141031043d6207903580d14000395100c00d107032803201c12a910045031814000c5603034040000340c0742140c0010307643c1010300e03c0695240e22107520300b0b01929004c000624110701c2143c0e22910098031010290700c540300c00c201c000a4900c44003031101729540e1144000d10b0010300704060a140b5145442c0072480c018510007003880100c05a124400740401d4400801060341d499003220165403000c200150101084e200c01241128050b41c005c00000320310391440d09158000b4690305076280d060340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 424239469 1250 424238219 424238237
    0x90c08060a0203160518060406050a17061311090307030c150503060105071b080618010b03030405031e15040305070b10050109120201030f0501030605100b0f04050f131b 74
    0x6007070003240700880c0d0361080c0e507100c1108003000724810700042680104208005a42200b01c500007009607015901100116000203484039104e50008400502c01c1d807841c02d002c8141c41d001000c01c111102850a44a8031540c2d075501d8038103c942c0c9002d803030003044043c084801058503468120386000084c0103c41c080586403d541405038410000c481c8503203410394070a820461540d54500784090305030b022010b01032440c600881c40f03100c200701c801d101307130750340400d12420310b00c2e00c4012800c40b40d6051440c0d0203908100428001d0382c6000411540f1507082c203c0c02d0720152107401c982030503c24000b000301d018001001c00c0c002410742c403902a24000380a05200741c00c9032600d111400c0c11130050310866011680c90641041000000c4024506480c0181000705060816120300b008441c026041100c6041c1d0341e0052107004a5001d03107207005000e09404035446d1601c2e655588201780201d01c201c40c4904c07100d00d1594000c1d02d480c5503445003070083d041c0c01e01030b02d076040c0d2181c00d140b04181c0411000580c101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 424240719 1250 424239469 424239481
    0x32409021b0f0706050703020a050d0f03060f0b09061b0d050307030b1f050c071707092f07030c0203011a010311092202071203090308060604030210081801090c0806 72
    0x8581c0b50480d00c1c12900600501e840c080040c0c94641105109400358020740c018540420360a1184c284018095920035102100c403441c0902294030a821000c84400d0b00301081c40010044c0c8100c030b85004044440c80d4580e01500815141c0d1409032841c95401c0c001c18842000940d00b01020750301a10181e01d092144040070401d1103030503d0f00394803800904510f890362800423400f5000801c0e00000321415200029224400f1864031000d0300c4942407039900c0342c9420896004540700d03240f0719285214158101440e40892460700c110172021006a81000203a16010540100000c42e017140d8050000e00c0515000321611050f480c101084038007213400c0100320400d06560380c0441d041d4100003407103c04000f000d200d8500c1c0803482070448014056003008804003050300c4910a0714401c0c280e581c0421a126140f80007050000042e01840c0240300900007800140d44405402140c0706691078203070319a60b0f500c1c002010130403491000b640e05510f0400340105010035140407009039a1400201c9145031603038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 424241969 1250 424240719 424240723
    0x3050c1204031404051002060405060c1215010e0406380706021305210c030109030e060307020721052505150408010c0e040b010f0906032409021b 64
    0x5031250501035051400080c0010340120416450b10301c070080d0060420b500c480100b183c9205460340340300036078031000422080040411a180c0d0000403501c1c02030415610510a5640d20005030413091804042c4000c01081c0c2d10032140440e8051005100380500e41d43c849890305000351951622000c40d406c0d07019481c42d0ac0c44200c8010100e800f40c440d01d464024151140c0e4000d4000d002c2c15600c620031020005090740d00d03006404890002001d6840a4201036024503140481c80d034030705800382e410a40c40001080c0c0200400881c54003e0321401c3e070303a50750042c0403810000c15400c0882d5282112941d121107100c50040340100510a00817203680382e5142180554610100d5211f00c1e03550340740314041c050341c20110784c2007105c001c42b2081c2c0ba00789070300c13204220b00350b502d0300104500051007c020b110007442d040c01a850703207000a0170003000d208541a4004c08000070b81c0200001d240d202e030849144d40000600d00c441e9584440341c0d0303151054550100401039172145103200300340b21042070280c11072000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 424243219 1250 424241969 424241977
    0x21e03120c211006030b130e0c030d0c0803011211030a1b1a16030c0b090606012703060506060d02070b010f210f3009081b13020702060c010504020103050c 68
    0xf40310708111010307141400403406400c0710b55400c0d800c1b42c44031142c0100c0c0421401020701600c18240589a0303010441c0038146440b0041c0c01c90710800c00b6a40c00c0d0300200c1c03090000c0700c2c1035410420151084105506002d000c0c010465002e43d050b00c14038501c6814410310340e4141d40b60802c1e14500407178295440b074984102507607004070481d0001d410480d80c1c9412020000d0742014510a08120381154010389442a00c86821144010709420074420000341c2d44c2c1c0078140c10044000d000c91100340902101380c0e00d8104081d404024052940c480200d81d081e940d8038103441c420844004190741d01d0b40c0900d00380b5080c2d9402e10551041e680c04102c041a0f46007a8010304851210702d0300824410345170750301d07420300022400c4001c0d01d1003000300422203400c81c05003182c0307071201482c2c0d01c00003205084040020804101c95100c0e00440c1c20103070b000b1002d032490007070b40b00b11688200d40501c100c1850011040c0203108101c1c0c02036000100040b43c1e5025030043d003001d403144c1c2c000d0328100000d9440b030a81c1c0ba110b100d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 424244469 1250 424243219 424243231
    0x1e1908151b0a1209050111030703020c07060822020a080a1a0606030702030f07030309020d14070803030709050103050c0d0519060b16061a1201061a040303021e03120c21 74
    0x201c1c0100452030f192544008030083c00341001084e00c80c540d40c0380103100da2044d124000040e800107242c1c090316004012441c0100164a054842c42c03518403001e5640d00440e4825818541c503001c41c2c1015550750582d40c1d0040c090391829a030034400c0c2481c01e500c08d4480102c200c0c18101440740028541e150840690348903c801c0d40146123059100b4682030b155a000714004c0f4207142d55030782001301580300c042210751558898074201d01c005040303090309450846983d1200440e540100f080042d200d910100c0402140d00a08010845841e03481e135990b110701655a20b0403007149484200032810402030020002d031101c505040140030744801402519104a11071042107c0c1000c10441c000390340380d80034200720b0a0802c1c180e00b00d92034400000f082c00560448008407a07440310001d00c920030100400f1141040c10f440310034640f91070b503540a512961016640c00305107080ca440c0c0e6080312820b00c00c440304041603420b514414a0119580402600300070600c60004125030f06c03468030190902d0455000c2d0f8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 424245719 1250 424244469 424244477
    0x5060a0302030d0f11160603150302010e0d05120c060412020706050f030601020a021320041d220b0712090515091005040b0708061e1908151b0a 63
    0x3c100500503160700405080d643d04212070010710414142c03081c0304480020380e203102402c440900d44000102913480745210160f119031300c61410030050381c200c14041c0000000b94ac1115400a00e41081418584004401c0c003007078100141c41900d45001081d50380c4118070503400506502000b101c103c0c2d0b41c0c6a203001c1c44001c0345080002c481e5041141019560208051045a02e40d500ba035010982d0030b06940e01e00c1c40a42d450707498500c904201e040b44550070100301c0d42c0003400c140c40d002c9008030034410307941d444a0380100b901c045100354100724900b00c0d102034220304014280300c440c600074090000460b0080009105400d40c00040680c50048208194100b00148030481e00202a190503085c042c04e20b2031584141c01ca4045404105d014203441103009001650b070324641800080c240740c4000745594807441e120740945c2c070741e062040140c001888050300d00b4480c028807074029410707064564000c0100b610a580090360007001440240c3d1040032420303401d0320070b0460307513503007502ca4041e20040b003000ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 424246969 1250 424245719 424245733
    0x10080312040f06090203030d060311010f05090904050a0f12080f04020f0405180703050114100501080c030c09121b0108061c02031510030317060105040b0c15071205060a030203 77
    0x4990b0203180030b06101c2c003a036070010700c0802950021303107541c2c458480d600c2c001e83c5070312003003003440b400c8411403103680000c1c20101103200c005000240b030307803080e68036242c400c100745004907041c08410441d400c0000d5002c0101d5031040700508003035074030b100e0361050400040c00b0301780000c0e00083c0118815011b640d02a00d5a08804030f01010040174020003040c0001008400c1540140301c03c04001202c0218001c40000854145030158440b0b008401010032040d9401d10600b00f100d030364045070710747c0e0051920003003a443e911081c0f03000030309210b41c40c0e5840d0b11140040310b803400030002143d040f0b0403500c0400e0700504078117003d005444034034045807007550140a112800361700240000d1007904403803000f01a500c1c83c410740341c840c05110320190303001040c18200c0e0000307104040d00200d00504ae2501010f100030380b0703c0c184000030850b2261740107000104002251007103100c601080161441010700c1e901d4402d602c1d11450040c44803200500548282b420000414070718105101800266138001d40a401c0e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 424248219 1250 424246969 424246973
    0x90c15092117030c0c1213030803091f0e1b1005091503041202060702161a0705010f051f030803070f02070f061206170606101b0b1008031204 62
    0x8140301c0700740d050b0307107032402d40c074640482150389002140318000c1c10010076282c0014818003440c009141c9005e400301ca500700147d0221444080560040301d5002c26001d9480e540c0000035420041c122010058031020783c8030440d0310005c1ca400007481c2c0160241294a04804900017814124400f04143e8000781da5015120920780300f9002408911405009803401040449100165910817242a01c20141c0c0c03840350504150705110441e0000f00600c014030101a81314840003140d4210701c120300600c8945442d9400201200040c0c844031600306d4001c1000301d0032400d4040141c50200c03081030b01d1210808501842c44100024041038a810030304c9581180c0c0e4107901600c42c1001c1090f08429803142c4080080c00000d01505a005461036607610046407080c50025010b030340346504010310304a2a00988441140001107203a0f01078002c07034040300d07854184807042d01c69041e00e009030300420b05554084414450b81440c1c55029100d503d028001c12641c90f5601602d0b4021007400110000903003003c600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 424249469 1250 424248219 424248269
    0xb071a04020120250303030e0a050c0904110d0b180a080d15031e02031009051908040906091d060403020703060f1103070201050603011a01020c0603100801090c1509 72
    0xc0d040504401c480924807042c05a02c4142201c084c0c0f0f205031041c105040c420164540030700c90385071303411000811f4960002d41e030340c0d52180009407580340111005800a4103000c0b1500c450f4100c5980035140840100b0310b81000b0007501411a03101c844401c240c086400c60102c001100c40d45950800882821f0000e107040b070f00c000e007248628803601011780800c0071000c240762041208442c1e58a058004140d6060301c181070070300d039031111105212840d000001c00032600c00300310302e41924240341d26452503004134609039140e030140c0e8201c032426526044010480d46125400042c0700c10001607246840021a000300b60f680d0350444d8004d0060300030150801c00141c040c0c004e14001c040d030400104a080401030302d1340b8190421241c10005030b449006200c15410b0a01c141202080d003680341d0742590b04401d0020395280f0140c074240e401090000b00080d2341d0980030025101820380000203104484807400d0a1001845e14007a004407110f9004070100d0071070103234060700d0850391414031007c0c4038484c100c2e00f00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 424250719 1250 424249469 424249517
    0x1202070f1d060a0305010e030a260606091306060306030302060f04032304050d122601050f01030f050c070b0c031303030c051c0509281101090e010b071a040201 70
    0x43d401164103107010002030420300440b0740c001107103130045485003000480107003103c842048100154042021002c5401c1d082c00025038031000c01d6407225586e1502c10046a604c0c0420786400715854a40140402c1d0305030326410050440b4001ea00300c591035140c100500c0c580b10025100100421030102c003101401000b9448100300c1d400401115042507a01c00c049030803840501720444400e40d6641740c1c03102c00e98100d50400585014608680d030401e40180c203081c06c0c0001070040c640b181008c5124211300ba0b100f42c000301e15030090440d0600460500b5102103200b074000103411100389615600003240000f111054a10076122411191090101500e0581c003c2051b10084000c0040400091102501d904103150351215120000079040c40e00d03a018500700340620030380d0360420b903005440c0004450301c2602d03d50a160040030b2030f6140c81c18000180c0d41c030b240c0c5030311000800004e1000000d00c040240003408010b8015054042c11500d4640d100b04050380032074000780850620a58880e070a02c84501c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 424251969 1250 424250719 424250731
    0xb040906080c0d061104090204030b010f170c0616020a1805061804030f0519021e01060303081807171c08090604120905030a05010603150c050d050406060905041202070f1d 75
    0x4a4505900c42c1318074012390303205401c2a100340074407800401c40c611480000000501307074490414205801c1096442c2c58000015001c4d1240c03901040c2e615a1140e111007105065500800c60720b100c540e80c1d413020100c440c9860304140024070380b50014003181440c92505140c0000e81d40c0300f03603541c3c0ea1a50195240840d400400042000c00c5c0405182076550310350815844015800901e01e0b00c107601040260303091010f0081c200750341003500410010b81c000300c041c0e0300702c0c04071200c00e047c3c10b2060441c1481d04410354042c04410001b00e0b0711051914012070315a445e065988070b19000c41d03621007010368811209581d070191590015000402145182d042e4051b0500c262922140055030740c400627151440c1c0c50b030165606d95558030104200840c0a943c4005085610400c2c00010a0000058124054450200441780d2660001410803036194001c0300500007004080000d4241402c01c0142c00c2d01a22240c03001d44034480003c01c1c00981002c1c01800c03070f10894035100c4041c982200319420040043e0107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 424253219 1250 424251969 424252001
    0x11a16080309100504110f060a0203090f040e01052e0320030f070f06090e060a060507030306030c03060501051003140c2508070b0a05071202030903070c0b040906080c0d06 75
    0x49191112211301030180518010741113a032607211640108040803a080d80e01511424081140c0c69203941c0201c15504200c0040380c0c40c02c00900d04c00041005840c0c0822800e02c29403a0408101151078070092541581d030514091020929052800c090520611b002c0600041c0c10903191038201d040704a805040840c02600752400903544c2c2a5440c64403540b6040352401c02d041c4401403101e168002d8580d0000d00c1401c0d0040039a09150000c94480240c0340200c4040040016504041c18007a410440065610100003200c403542d0f814030000508080c0a041d2050310b01c0d0901242c640e1013805051940c0c043c110031b01005443d02c412100c0c1540c403d0030003280301586010000c0d4111040c000640c00c260084013600e036600b05900c2c0c0304040e0800103069051462078003045c001115400244804420000d080040c1e40343c5481e03201610b54085d0304002481c10281180200b208500031001d0411100d050f10700b03006041e1108600b5032503110764401c103508040030101410108220b41c00125021000d005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 424254469 1250 424253219 424253233
    0xb0105060a110703110f01091a0708130801060302010906021501231f0806150306040f0209061903230619030819090509064005011a16080309 62
    0x1449003403841d0343c0d206171a42c1c001a840c0740101d0401c0002c803000c2c65000d18080c0380f4141000d48070000c20f14019850083d0303100100e240d0b01000b102038100c51080c0c260b2510000c4080d554040c03507001e071000380070403400185c503c500000e10700d0000076160800c3c111300e40044803583c00c250b40c00800e0705544a44000e03400103130760040c28984400c4c80c080c48400d07100d40f00c809107160014002c1c4c00c00001030021402041c014000c030700101c2c100d0f000e0b03d4000354100c45c081160300034520b00a0180c0601c1c00300c0b80d0303c4500011001500a01c2e00704440b04540c0c02d44050080e50424003e2400340c010001440c2e620795030550000c4da052a0850000310765030400c0c030f00032517907540702c0d1030704c0c0031541200c2c200348045003001c070104120719089911040102422a01250580303049408190070034002c0c0180f1004481c21002c1018030b00881008130300702829100e06050b52101d02400c1c00c0a428288110800301d04001805141c0800740400c442e124403003c9440089500b0b655503601d00c1c0c0e800201828400d000b201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 424255719 1250 424254469 424254497
    0xc04020a12090501020904020f03270a06020307180803120108070602030706151d19180609021f18140303040308031f090e010c0c20010504030501240605070b0105060a 73
    0xc40074151662009e0110360f140e143c035078a50450080140724900b1180d040c0391480b800b0305400290b49240350341c0220003507107076215054280d4030386803840c6145401040e080c801181030103002018000d4401400351580541c1d81e0b030840143c90301c2e458054000140c001b0480b44000c40c9190b00315050000070150962a87c5541d0841e50180b455404856189001c20708140404e41035405040c9064a081d580100a9032a5180e031100f41c031a43c1c80030040c6207544950a003410355403003801c1c120803c1e85042028090441d92000140420b01d00c6070b50400044600b61301084460f035640c1d0001e140000a0015464142540c4038038080e81c100074130044840c0e4aa482440002c5403d24150300200b400503000305807412000d00050a6270342c0608854204401d14002c640400c0100d003c84e207410640014407054072000e400100ca0a22440d0800f5000390b00304004948492281d03c40300119208080c41100040d0f11140e08a40340d1142c4031024169070a001c00501c040d207010320051007083c0c0c3d242441e2228003440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 424256969 1250 424255719 424255721
    0x9040c0329150c0c120c010801030b06030a020904120201060821030405030f0a090f0618090c1407110f09010e01090b1c0506070f0504030c03230f0c030c04020a12090501020904 77
    0x14202d450b0303d80c21131a01c01e80c0504140c841c801d0200c820002070302111241c10002007c904051001514503172140c80820015107041c0103404203c0d802a01481c11407034a420030402402c4c40740768120044d841c3c0301d0300286c80c0e4004101a404501c4191694040030300b0034038005502e4101500660b802e0008000c40c05615400c403000700901c2c06c45488a0070a20301e0b000c4441d603040c60981c030103070601240300010040c60b501d8003083c03000e0380e12500d4000360580c8080c80c00c843e039941c45034540c0c034070010019943d801c2c0110400d0109800d1800c841c29070b805042e01041c840f0405080c0300f84050000d800005005114090704003480085014004031910b4103449850305203603e1030745060741d00703810a070140211076602401c0d1114404042c00d0003880d2500e0341d56010b010322031601c00600554244603501441c01050392900181004880c2260554a10300711400d44529080002506c41c0c4190703001c0d42841e0810780251034401119845400c00d10700f0310304440c1c010382060749048030103560070410740b2101d03965 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 424258219 1250 424256969 424256977
    0xb0c1c15150207091406010e010f020c100c02090105060405010c0602030405160e041b0807050d0804091d010b04050606030f07090b0d020406030f0e0a0f240209040c032915 75
    0x350307500800381e0624025100045542045e8907000200395881004156600f220401000100038a01035040b10070700c400803070522004080b1107901854012031111980e138082400b2003007d0084981d600c09981e074030100912449144282c41c040f4a0008440000c5074041d409940c0c03250040b01070350308814040030504140c0c81c1a4000c60306255130301d401d000c00e12010034403c180790080141c210109030309020640303a681442c2d201f4188107000c4204084104016102900d005080301c66082c4101c0d40c841d000410045900301110240c0d40ca8050040300c00c0c0b6040c0151805084007800726851500e4802c5100c0e24108004d00520070300444400c00039042c180c45004014203078801c1001030300c035820402c0c000c043d11042108a5651410401002d0002c2c6011030302c80402c1d075000c15881d40e103c56a1800c0d0304c071084440c030240d0714421a500c490340d800c00aa0002c00052504540400c414203404109a0860700a040002001a0204001461403400c911001d41a0100500c0c00c440840c4108003180a42c1c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 424259469 1250 424258219 424258259
    0x50315030a0b15030a020f13021c02120a021303151805071d010f06050307020708120403110103090b010b0d0b030a23060c0a0c0c05040e0a0b0c1c15 65
    0xd02403c0040740102c8401100c5407841c101c1c0501101440c07500011000c881e1441483c0c8581041b020100d4092419411990041206151900c508610301c003260001d4110350341a03080d04000c24001811403200d8821203803883c90341d0342511443c03419512001c1380d00300a6a00c11100302d17503a400e00800000742041004616100303074020301407181000381608001c41c82420039a2206202d00c014000c03a03090401c2081070310900d281042e2650340c1d0b040102e1800d05c450f800701031140100c50000100f49031142c0100185c0740074010041c000c0c0c800d44011002c440203050082d0261030784a0050001c0f07140c100c02031818005403240400c10000e988006400c0c001012000c8801c41c02c2010b40c0c40c0c43e0400010b1041d201d0280c1300103040c0030f01c1c05080c40105071043d00c82d104204001c61120030100503501d03400300043c1c040940704124602d003419030140d640d6068503003520801c5c0303080005101d10b2880c608a032082140e001e10ba540056500d03481901600c4003903407100a0740590340d0b02240b0704039040340c50701540c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 424260719 1250 424259469 424259483
    0x2040503160f0b040503061815040507090c110309010c0201120212060f060918090316140f031c090206070f0b180a02010e0108062b03090906060c03050315030a 70
    0x28500b0181c004260701903070043c800c040080c001045103540100303585034414010502203101051082d030b80c0d41030050900041800f16500400d2006000300001e000c8140c03109885e042020400c141c0c02692580300d41035200c0c40c5070f8010004502194402c0c3d07070007034081307106052081c1240040d400a80c1a40c0008541c40c0741d070f41c4620100200c608d40180700700005c0d03000380c50f41c5207000410303004507111080f0701e040ca4103030020081c0800c8400c6410011205000c030b9203811410001030519204d801d03c02c0d450358410603445010401c0b2081c040100c116800c659840b50141c89510a1440903400360810903801c0e680007900b8800240480e80ca02161000302d44103118040c4140b40c405000712004014a80b20301450f0f01a0740c0280060b600f00951001c800c109082140c21581d03103400003030002102101848074030900400d40303080100b41c006522007252294a800f10800d44070914081190401e01c10f900002d201c2c0d500340ea000c2806000155080101070180c800419941c3e8046031400c000303168212050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 424261969 1250 424260719 424260763
    0xb120309040f020307141305130c110c06190309050106060903030818030307030f09060603060c11011a010f090824010803030403020a060507122f1201060f0302040503 73
    0x1071405208440c0381c00080d40d021421400c040780300805114201044040030600001c025240c1303959890120028000284540085e80e403003401c00b0003601101d690b4101081640203c11965800400c1c580000746014100600700100c0882420100b81c01d40000801e069a889104012803000e00607280a4030391601d50b60384441c69450010b1031030703800400c04116810920309404d000a00807048a030002e02d1131030f000c605190300c4101075005002540713005014910344440003040240e55041a0314440b51030300c07600d8840c81e0701500d0600760b40e0800b10360f0400340384030018002c0941c0201c6035a4100100c5e450044040c9449510141c03410300b00800408100c2800c41c0121003141101381194050714030300002c0e504506007075130003039913411142c0d800800d03242e20385000a180f01d20034002000760f50003624040c884240041242c048000600b460420740c04020300d0007640e007425010131210003081d040d40e40112686850030031140a00340b009001c04245d001c200010b8265010030508140b41030a12890300d00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 424263219 1250 424261969 424261987
    0x1c140d0203070507060e2803030f03020909060d0507030b010e0105030d050408062818050d0c03080f09010906020f090f040c020a08030405100903050c06070905090402130b1203 77
    0x24002a0208550441d4030030800d01c0c0c001240494031070129000d40c1012403d403140300b80058980703006644100300140c04c05400107106454140007004881c02510340c5074070301410440480c180d206120340e81d600050f003500441d203941007000c880c17504907016605440203540c4940d98000c0c820ba0a9102d070188a2800006001511b002c1c00440000c01c402d0030141c0c82d05240c080c1e03007526640002c000440c64000415002c49080e030446114903a6888800c0c1045480c2a40c1603a59104122041c1030707590744500c0e220300103c14062024049460b425488810f110751728803041503110384000b0082c600954a402c03042c1d0004401d4005801d880c40002040f41e100c002c01400d00070308540400d00306120b84e00b001a2822502d4000c5502a86c072608000a40e40d29611420700c01d2412505152513000e6074546440981850f40c00000762514000324015100b984d00c540c40100d90507000e41c0a8540d006002001103001458608400b802c0b41000f1400411014100b20010319040c11203003000400350000140120 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 424264469 1250 424263219 424263223
    0x3040309080c0a27020a0c23070b0c01020705190515070813110d2d1203090212060f270d0f0c150f05090a0209070e1c14 53
    0x406000008000d005210400c000030f000b9a071a4407501e903401c1c0404a86000e02c0305002510006021410019507403003a14a46c000c0c60010200d206071101c0c850219181d244c40002c0c1d1214198217940f800404205017000f515610350760200d607a0b06c07007640d804c1240c0000100240810000720040444080711401c1a040960030041d030300c543d04034526428801c2010003a0050300d42d5411503440c0007117821484031850080c8a42c440301c841e00c0e0748402190070f50750800c0f000444019114050034400085800c45411f00d00300f440e103400000301103507202c00151004a202c0e91010424078002403c3c00d40d580300b56000d0324100a0156000d8800108030400c2191403520b80000c0c401c07079030440c1c5903403075521004000e0713a403560003501c0742c6010048081220035007244a10303214082075401021460618040c100c5480040151201300c50006041500085019801080950340705401900030701c5140d40d2720a0842380c10040c42c4420b54004010070021281050311301182642c81d01c1800070068021400f030500d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 424265719 1250 424264469 424264487
    0x17010212091c0f09030204020f0a02161802091f081f0f0e100305060f011a0403030e0f0303040f080606040f270503190f14030105010e13020d11030403 66
    0x3001d0350004242e04581020303440300642c042c41038501050b58182001c02101c000b0650380c0007a50040c0080744520007802000000d048010303041d02140c0d10074a071850001d400d690340388036404615a110a0a8400c00e5454008201b402c4008041d4081c0c0003502032461421143c0090a00002e41454100700038101044001440c00e00f1034841c0e9000c030f504c0d000d07585840c40300b1400307004101000507011500c2015000d100b0340186038004182c03038803480d0404524601944c00d00c210380c0040c0d0400105641d174000403048605403501551103c0503202e6210600510062090743c0d0f80e05848108030014810540103107440c0a0b0054002410403402c6c100200000e5030092001400e002c0c1c03425800f80200da15441e4004c541c0070f60780a61003880c4240b401c181c0c0c03c501414071401000c401c80b45c0017051080d4804800b44c00c00d00d1a0b04e45482813801815090b949000034050309001c6240c4118204940c90404204009454032036005441d2002845002c2c054841031580305011460100620041541002c490 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 424266969 1250 424265719 424265731
    0xa0c120c051c061a1c0912020c1005040501081009051303080c030c0909040f020d0b07180b0f2d070c1a0315010c1703160c0503040603020a020717010212 67
    0x1840700b141429510904c134042960720001104000134000c0c2000e42109008106a21604080040c1d000d01d0400054500718200403000601520b8959100351805001c5084032007159076416040030f041a0065866210180822141244032503000980c00e8550056138400e0102c0244031782114414035000d0400c0c0005020151b29100501c00c0042c01001b07202900d00300e610498402ca00c0c2c0c0c44504111441284c50f04010b9003288000c2c00c01010b0150034003000e801640d0a0792081c55a0008191060380c4003050700445814010070421100c40207001c1018207480303040c480c005140c40c3c2c1c924940402d00c480d0b001d0300b59090040841c0030b0084c0641703450700500420140f44600041d03c7c51465407041c0f880000c0844013551940010b03074009074814040ca49a060307002c010420b4902d03059500c07404681040342d2070403060381c1c0341000c00f40240c82540c07500080360340301c401503013001e0600070b017980690405d0401c0d500f1032250f407000107500d0b03201841003c02c11802c40001a500d050406981884400041c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 424268219 1250 424266969 424266971
    0x1060603061a07020f0a120f0215131403010e012a0f0c08031e070e030735150a020d06050d0f02040f18050105150f03060a0c120c051c 59
    0xc00391100748002c11507070072a504503800c00181c514140016a40182a04101c050000505202040241e0b100c803401102d80219007610490882268006051240005482e55020380080820191002092900c4040001400418116010b42c0c00f1401c46200d401c19400b01400200482040b00781d003840201c460000e8540026100b95080d0042c02c1200b4400d001450f20300c00100082d60440c44130f1070704040d1204510880c0e034031308010300003e0440e4000344242d8813038010060000391890b4000c803c0c2c081202e0320090f5000024030441134880002d0032083e820014060511641650a41d80d003515102c0c019030480140c940c2c040b201454126030154006c2c0303014108019880d0040791410174216602075040790045000341013140c100d800b80c5813038040703214108010f80244040003410340005214140e080b041d0700031030040c0c504004940d1061000b07103803d504258003040c00d401b00b42c3c201070801c0c0d1581c108080002d81c24080d110850700e464280e4000240c0210740d502d43c0304000c41105901d8224207074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 424269469 1250 424268219 424268249
    0x80c0d1410050d2105040306050109050f01231e0a0303110d030506060928171506010e06031503150106110f0309130603060e01021b0102030903070f030e120106060306 73
    0x2131003a02000550201844420080d299400e80300c3c801c3e0110f401444e804a02400b29581d2046c11201814080c1c500c840791040c110000320301401c4c200100d4070505510221703036207402030881c14005a03101d619a94030a50b484803d03e035a0315180c103154080254071940d50b0009240801c000746003814100060755042504020502c10907075500401e54110b04c000b01c94810070340030b400180100c00700000c00b5003a5043d50006000401009201ca070b00d480f82c00b44015a0001860b0301d000e000a00b82c00c039615404a60380044c1c10080d820094091548130140c522404c261441e805c0001f0b16111041403512910154940144159507220b002c082248440d01c1c02030900d4a510f00d40d01da140e006054a01c0d000701c4e4005c40c1000301e01c0250300030b84000d5400a00401c4012302d4542164040d500c148009603031145c40e0340c176426100320144201e0303100f20043c201031800d04810b55a000b8a0f4a0b1040c0c06500700030303295203012a40c1d60792000b900343c0c0f100c041c0f0000400510b08400581070724803c0e0b10814803844080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 424270719 1250 424269469 424269473
    0x30703080702160b09030a0605090d0908030f0f03040c08070e15090f0601050f04050d06020d0c09030f0b0c0d02030708010e1f09020307090f0306060f0512030a080c0d1410050d 77
    0x400081c040d15141030341c0b5178880c0d0f120404a8a0000b4221010306418140702c28410804000b0505c81c6068031595100380707429403141c140f02d036079100d00d011410021108100c0100703a01c20200146400a1050044422041ea520a114584180741d0400201706443c101405411554002c1100410b1015100301c02d1510f0640903140000800a00d41030600900113001400d031607003c0d08407000703007200a01c0c0d80e06241081c18030800a4000c0c90421049601d860170030140c081c00380c0d201004903a804085011030013926940d0200700140070300180c1c01c4100900ca03030200c40505002445c403812866031281e40640c54500c00d0284600054802c0e11145d040d940980104019029514261b071000d03240035903251102c3c071085030003202c41d50100a41d040d03400c1000c41000f0f61604100700b194032100007489181d4803081003250b483d5115010312001c7d4800c014050200d0300515080d43e0040c0b03035136071285c04c0044080105c02a2014030244100c1c80741d801c010480c00c40002004100600010b481c1076118074215 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 424271969 1250 424270719 424270753
    0x507030819030f0603150e0309032508010b09040f0302070b0711030c060301050607080306150a051804060605041502160f0608090d02070303140d0603030806011d031c031409030703080702 82
    0x202406c1c1008548884c00b0205580040007110710500010b0122148003042c2400c848070b100000c1d9511001e00300c40c51001a9a4005001d164403296004100c40343c00e843e180c1d56880d400406040807003d40c00350410010300880c034580500005400b51003100b0360b80041104241c105204601024810b501c18801401a41c50321029519500d500c000d140313560351030701d400003550a079801c10181070144000800c18805684640680140703200540d5420388200c0420810050b18442c0c000d0f500003c0052000700031020541150fa140e1200c10300680c0c00302c01e00d4841090b044a843d0f00509603601031708070100602980038668640c40a10a406003060400141d4001e464070a9448080d04001003465152204500c81003129001c041480d010810a0758030318015000100c00c50b049408581c0c1e02c1e020600d200008012081302d40f00040190100f51a00742e100000004148400010196600e0880c0c3c4030b03840c00d041e40c81c010318021000b0350300d0b4191450014402d6000400c41400c5401c4111401554204 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 424273219 1250 424271969 424271993
    0x60504031407300204020703111501180507170403030e0f0304050901030f141906050106020303040302060f0714040315110c0c04180b100602060109060605030a02070507030819030f0603 81
    0x203050400a440400241c3d03a1140000015020b9071080c4001040010142c010740540000d42021044d11030684410100c0c22000701c0074482c00e040e1000c3c10101000c03442c4154030684d031004003814034100032401c00306102030b4940111800c40c04203542c0d20303501c441410f0030064000d44114a500440c580390600c00410074001c2c040c0320040c034001c10f4115910400ca03034400f800c81d4980819084400804a1012108121501603c1035a10500d0840080341240c4003104807032040d070705500100b12946078146400a03440004100740b04022400b129105681c03202c0d00203000950040c6560303a80420106000c008a84039054071b4110260f04001c00d070380c250808106084a00d4046800240c4802c80c40f0804000020500c2d005090324942401c001083e481c8249450555803e07070b085030282c0ea00c82a418048600d14042d400206030240002550b1280b550020a090340c89582542c0c015980e07070b070320340a440d0003600c14900380800d0280b0201f40c40b94148105213034010701440501803245592910356001c10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 424274469 1250 424273219 424273259
    0x2030d0903121d0105010902090a050d0c120807020f0a080c120c0a080708070503070f0e0c090a0806040b060102060c04120816050f0607090f03060213051c0b10050f060d1104060504031407 82
    0x20042c0c0803600344a8601d37030700001002e121070001d02e100365610f030140d041d40c88460b08070301c90012141584964144600e408080d10300040041a002d0b04070700030041070a2404881c140c4c41d2060030364001140d2110300b01c410082660f5401001840e040014050415100380c000d28025400b00b0020046185402d00c050103d83d0840b07a0b184150f00d5150050209204540030b140d004540401c002840c0000021010700c920700030105c0c408151200c4004903203400043c3d88040382c2c1c890500040c000da01c03c050031180158400d825241c54001140d9480700505008941035a0f0340c1c02002c841c1ca0300f10402d120044e0301c1225454501e14076414401c0414028450340809044542e000c184a0b00c1000e0103c21a40503060061400c0004000f0306c808a0030f1010701c01040f108910701b0703408105840c258444020549070001c00f120000f0b8017013410700000341c0000c1c60f0f0021032900ea11140d21030400c400000e0010304450780c0c4082d078850660a08118031030030001d5000d0594000c181c00c2242501c50040701c68089 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 424275719 1250 424274469 424274479
    0x604021513140f01170a0c020a0b09150906011203030e0f100203010f05150d02220f0509090d1205070201020912070303140a02030d0903121d0105010902090a05 70
    0xa48400c168851400341d44031408025050700c0c0e000c515084040d4007108641e400700d80822481d4420401101c0011010170650401c020300d00216030060f610303070080e6540a0302e91044504404140d240c040c5103407400d50307580005400103001c1401c0001d0205070a07a000707036414003e1209500d0f010404925503006e40c0090f04142d40d4022a10b00f1000909c90860f603e15001e003110141140b00c0440390007540207126080800d01e02d02000645802c000600280301d000d50041d060420b101d504034003000c2e40c40314440911081000078030b0329200e00c038290340ca0050254510800c410504000034072451601c040c048403259404041c620314002c5d032168038501c10000310800400e0b15120b1000a034068000d20040795032007481d08014520384103001803000c1c1200e009690389a0360f9558048060b21502c00c5071b007240d005030010040f40401880d10b4006440303c0c1c0c482d213001010a0720185125080350342c01c4030640c0303164a41c22181800714909004141c050705003105d00714900b031322000010394541094850070b4010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 424276969 1250 424275719 424275739
    0x611030d020306010318030207210510050a020f03010306051b03040b060f0a05120105060301200a050703090506030403020309130b0a120606090c020a030306060309080306090a2d050109090302060402 87
    0x264440e13004a1081b07a40c4080025583d01640b90180d182e07100c5008042d040c2942140f440c0c004483c0c80b110140d070582007409405031045d0042c1000103804c006004c403003040d0b02005070603141c40e020401075000303502a810008542c20000b4000000304283c3c040504103040c140144004103040b0340156400920858045030514014800315451449a40c0160ba01c0f441d2140403014803007040d08460310801c02200200304c0b528401855035981c901244070a00c1143d4240803d0758054025001014110f001e0b0402c4040c035680c2d400001c20380d074000c075800c50040e000402d14010b6820440000d60704800c58400c00d0144840980c0030030740c844814455101492030780d6891388140303c6036901000c0500b96402c010300406c022800301950b03540b08640c00702c0000e864103030b00060552291080182040e484001c3c107285484540410280b50701c05030600301229602e942d140b5601c003025041c03950345600c440603d0010180c0a800104644059014000b00790800341c0901c0065070200d06113a205604403868a64 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 424278219 1250 424276969 424276981
    0x305030a0b040e030d0e010b0a0b1b030c010c031b0e0f060f070b070c05120f030a0e01021306032c0c01080907120b0103140d09060509040f1104030c0611030d0203 71
    0x1030071a500001d007413070100052280079811950051780c0d900348604004d101141101c0e0900010004d244180e41e2000e00610061184049079141e003203010000400312420108070120030303400c4400c40c81104001c641e81c1c0d608000038142c00f0030411041001400c12211100708180807800020b681c81030144180760018000210481c0c00094030240340d0000003000041c0342c641b40282007100d203481c007603034684541850129081d0703281048444410025a90324159207e000d11040548402150461255020310408a4035900c03000481d0041505580c042003180009918004041d910360700c4002c980f14401d007200400b0000036490804000038030b0b010f070195454a01e414101842e82e000345542e18550a1040148203ca00070241600c1c02904010715840600740300741c1c4c4d01c134804030030500400c5000703904102c2640104064950400081c10100d24441d0040c1b004040340d04106001210450110b070074018040041c0035a00508818140703103c10031010415560360b07005541007807036490340000c00112 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 424279469 1250 424278219 424278221
    0x100c053712140d140403030605101e050c150610020307020f060702120f0a170403120807120e0f0706170118020706050702030703171009090c080a0c1701090305030a0b04 74
    0x1400d2101e10104000156074064a280000405e590030350000b410080007144510700038461240c90311103a1642500b0301c40c1271210601d20400320b41500140003081c401c00c13240020130f0185400c2854030824050491500c602000760303007602d010150007107610601820006840e107003500e20300003904442841e1500744a10000d401e051048804000c24004c4501426820500060f0020100d102d200d42100106803010b01c040c0e5405580b1003e4440c0070a00f9840300101c0c010000c3e03940181003403908118041c4202d0340c403c151480b4146803250707540078166540c8130120034003854001d444146041030458140110003e5480b6040c0940190418181160341508905a040720030f42ca500000030700c034034035049801940f250801101038020032a9080400341800c0b85001441c41444040059a02c03d400c090362134005113046441201c10f1501100c0c0840c0d031010801c0038201982c46001e00c00c000300c0c00c0007108500e030ba01850071205540c0c100403030303080041c0e0003405596018002e42800541c1c0d02081c40050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 424280575 1106 424279469 424279477
    0xc0c0504020d0e010e071409010b03190e0a0c031b081c26060109090e030906070302010b0a18060e15100c05371214 51
    0x80664903140c1d000d41210a491080007441e00700d02800c03039085400c19101d080c0c2640c401075003040700c2180c030f003502e1401d11416103e8010300c0d450b2003030200113800050b010f0003074021201d140d0803811560340d12803003844008604503000d130b04450130b0004030720000c0e000c02d07035040301c4843c002c0c0c5004d00048012805c4481d1040141000e18045030300301c1416000110003c20040035074202c810850382d00c65051075a004105c40040d1600b401d0f000505850340a42c0148442803c242d46a80324240100a850000e6010748034aa5103001d5468101d004100b600e10340c0d81d03c503405010109020a10400600d4900d041c40340810041b42c442003904151442204ca0340090002180552003d08005041d0a06003110b41000c840e00c0311070340c0c6d0300c80c10820840075021002d880c81014280c200c0300780010b03d1442d0099001c0001c0ca12132600c69503800111310300128148400d4120380140322521070112 = true := by decide +kernel

theorem cover : BRFrame.Cov 424100719 424280575 := by
  have h0 := BRFrame.cov_init 424100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 424100719 ≤ n) (h2 : n < 424280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
