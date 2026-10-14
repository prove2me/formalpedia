-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3220
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:01:16.669978+00:00
-- url     : https://prove2.me/submissions/2a728e6b-2d1f-4e9f-b838-615acc0af998

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 578956834 ≤ n < 579136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 578958084 1250 578956834 578956867
    0x1090923010e06060307030b0f1f0b09010f020607270f141306080606120f07080f070f14060a020a0503071a07210b06040b0f0406021614010c0305 64
    0x10500160780d101c0c0780348200350006111503608800110000c1c95882d10750364408021260051041034240b0340c40d8000b590400c0c10600c0e45100304030040e01a040310780c503881d004c806034002000303a40c001440c824400421500000d1064064440e54850145545014003920074080c2c103000310480301c02c0300550002e0a070001c6690040a0701d2215080321703941c040042031080349902892481900e50070300c6d10030409d42c00c01046103504400251040d011651802815915104212072051010312550000142c402c2000c40c81000340c120350410f541d02d0941c1c130405605070001c03900400c0c110f0051419043c0a601e8200001d003010992401030301c0b012134242e102c2505640040c8015940070311014141c05c0050529000b0940c0075195041c42c05014450500c03e81e141000015041e906903a1090091120754a17032081c0c034000d0802c5180b00365194699040c41c0a1900a4490ba601521950200421880c680062403055403114503d154a0400c4c00b4011195010800400d03410701c6001c01010844140310b40c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 578959334 1250 578958084 578958143
    0x13050a060c08090d0c0b0c21010f09021c020a0306051804060c170a0e0c10030e060105150f1309061203020609010e0d110309030a20010f08010909 64
    0x40015074100220000740c56244018007030100c80d082640352920154202e010880c101c0e80000110940b545c40000648207031082c0c29032a2011034940c681c400d80c103101003083c03e040ea04c1600c25074451964a1001505034010030080100c0400d00d440410508525a03000e09280180740c60041500da0303441003c1003107001c1020004d000e41820208020510845024a585c1c245140ca440e00c1495012000e0300390682000d8284410107848445d12007425008001c1a00600ba004140901c6841044030180041c07050311045145070195800000e09450294900c240c1d25030101c06d40ba18003503181859150a0f4060705501649a140080c0802c2d02a200d1095070054203030303c4840da96960301342c00c01034a403040003070425655a0505400c0354000001084008990029040c031502190f04188002d0650080c20021a00740c81044441d6003405200074241c00038444204e641e10030346080400446d0a08008103040d000320b1030260040284030000d074000c03061a40103401041c0038140001803d003900a10303c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 578960584 1250 578959334 578959343
    0x21309170a02010b0a03030905090415020c0a0507080d02060c03070201110d2304030e04090203030403150213151d2103130f03020a032904030f090b0a1713050a 70
    0x80307100036285030244a102d0109408840044007a4a1603038001c0c10b1a04038011140a600c007038000c40d04000e10b40301070200080008606649440301d0b2092150b540500e10403d0300c0c1032055a100181e8002d003c500285808540d5010700765650341c5e5011644264405040b8108540d83c8403030f0f001c031201b581d8010700b1220042c1240070842007288540e2440c040c8081c001c641c00c80061f5418400003030740040c07107403c1c40ca105036804100040c1070b0001905500803640040c04034484000b207010481d1b40c2d940244400052041c0d0411200d882c2c04144440441c00a462808103d2480760101158000c1182e01c0340408000c28030703040707020b020300710395500180c0c0941d001c11648085018219a201140315038090701100d070021090624640000e0383c3c0d80c0c103910024005215040304205030b0f242c00b000f41c10f170002c0040b43d801c444d82003a00d0300414003000b001c0c002000411300203001c1001030041e8100d0728059030681e00d00318403424403400c203ca003600141c008004801ca0180b10000281c0074003201c030502d80074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 578961834 1250 578960584 578960587
    0x150f09080d020a150507020606010e0a05060d02041523030a0603141b04090203030403022b0c1d0c0307080c1c060801052a031902040308211302130917 66
    0x300e140604c800100300f0b001d040c210b82000c00300104590300043e00e43e8001000d10300909415080343c0842c0d420038140e0401500204006004000050250006c000725031126208940c041c900e18001c40d41e0101628503401c00203440c0600d10409a0344502441d0041003901002410030303500d0343c82c525800640851209190402003500451a03820382e10040d00314030a450500c48104568006a103c0c0300702d010003071190002c0001d50324442c6246422042a50140c0300da1100d0901c5810041c090022074403441100900607100516510f00018000c0d00031414110340500715252280c00ba5a8024000c100400b0b07510305208a0101d00018540e080741a201c0ca180043c415041c00d524600b902c030000e144100802c14810802c0b08070012001810b015165114140c1c0c07603803100542c0501c44001450760500c0c4034000319021007800101e02c000c00441907901ca210380055943e0b060b4281d00c110031207418508603503400700345000d400c00e0300000d0400482c05200003580c116603500c0c40846041c8840c40d2445240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 578963084 1250 578961834 578961853
    0x61e120114031b13090c1710050603030a05040e06130c0e01021c17091c092c06010f030e06040b0106122708090a14010e040501150f09080d02 62
    0x609008119a06210a200001070340c44240070030080c0c824035040030300c81941c40c0c40344424801051b0348a405480304114031000e00c000182c0d4980e403070003400b84600c1103034940000302d0120301e000000c031910304c8803544949040c1480d2040c2d403540c5800080005400031080030314603d41100620510b044140755442d1140754840d4080020300e0906101d03d640b0602d2030301403003150f030550403c2c00e8907850162450ba0202964031018084e0500701034800c80c0004030084030b80120050340241c0d031502512007007442a50302c2c0e041038001d00d52140680c401d059a0304070320804903210f17520803080c1030012506402c0110b00c4221442c4501d2421004580907140a5410340041c0415603000b05158400c2d0824141400040181c9969001c0c0f200c07000c012050040c5072040b28400c00850006450075070000902e207413042e070350f42d030100c00c02840e1f0403090a0024082c000d43ca9000d18152040c28140e0710050382d120440089903605880e020040203180c0144000e035200010010340400c41fa28084180394050581840e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 578964334 1250 578963084 578963089
    0xc0e090c040504020d08070212030406020105070f050901090b0f040b04030b0405010c02030f03070e0a091419020f04050f0a0b0307170708070f0c020111010c050304170306061e120114 80
    0x405030350103441907041c0300c207100c09079039182c0c210400c1d1904555801c2d900c4125200013400c41008400c03d420700d000c0881c0000b032007034065118910803800c0d915070130412800d062084440340700d0303400d416020886802c070134451804410080c0541c080701502c014a890f0721b80c0d043c0724041d001540f044855052005c1004204042030141034611030300c0d40004c0d0f04051001000c4110ba01004001a0421041c80402c034026a01c1c003045c540203215012080141054192800300180e40407030300c1031820081c1614042d5850070610856001c0c03070301101140d0030715040c101004070000c44680b15980c40b0800c50b0f40421008840e03402140121102d841e0181021100790142c100414000c01c8141481006800c0001d815005000558040c1803858441429640d03840140c41074405000101c1035036107004041c000e10f0340c201d0015401175009080703900341907580f6105840b05c3d120484016070420310034890002201c1084a64042000c8a41c00346400c2c8410240403000340c0400740d0050301c0211215003041c0090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 578965584 1250 578964334 578964343
    0x91e051206041a0c0d11092814040603080a09211a06130c110c090108032209050709091505030304150905040e030918060a0302010507050a0c0e09 64
    0x40950001922841c50241c40f2199400008000e5041c0d07480400000380b040c20644040324144400042c0800002c41e940c1c41c600020f0300240c0c85540518000403800f05a4003c0e000e645001c0301a110004026500389136021101548400e0800d800c2604c9910210000d01c0b030801601905490303aa510b04c065140240c04009a07159002612a01d10b2000071500881c1003c0b0084940c2c4e024008a041c0325140c080c042a44407000300399500507140303401c2c121811903a200e00480700d070b18030f80401c898071801420304000c2c0c81c84081c03141c00c0055204000c1c1b114240341180f49003102484245900c0c0b0981d944404403015503c0c00c0380c803000000c0600805201000540c818581054950721020104500301000711340c0d06c3c410317401b5841d4a81e012041e24103c551040030b049000d480040d006000c8104000c43c01c95503904410346161241c24100d14202c204806201007030300c180741c010701601e0034600d1500103450755840114280c600e0700440c1030b407c0200380c2d1580a007008160803000241607103040744445080c07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 578966834 1250 578965584 578965609
    0x10215070203130b070f02040e0c0d060e0f0c13272d03091802070203012f0304050a02130e03030f0402011d0312030603160b0c01050f01051f091e05 65
    0x20f0409011260100c5c14000c8101c5030b040c1e05550001e5122660101c50340f8154200b0b012b2a480400c69941034204211038018400f83c5101900f1242c0c08010002e2003600e030300d245807449410010201d044d4000c82c0c890b170040006982d0b00b4000502c2005140700c01e004a0002803019a01e9000307915031090b82ca010402d140482c1520144028030030800c2c1e030b074020044509841101100d100716451907041d0043d9504444a03180d0040007000a0181c040362001901303107885d404a2040603061541c01400c0341401102e100e154800302a00183c1c450740e023040121031000000b20300391651041c0c118120701040006600441044840010b1850a440010b00f038419030128030081c20f8140360480825140041d090f0420418000e140c1c0d101c2da50600407a252260154510003640070100c070014a01309440020007070007005070020710142d9189074044040490a2243c560400151039003800c42460301405801448200d14204d07003120f40d5007480600d044d104102008030000000d50030000c51504101c140350 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 578968084 1250 578966834 578966849
    0xd03020d020d0e0315070e10110601050108010f0317070b090a0213060b09040207060f02041503051e0a0515041a131401031b03050331030209060d0201021507020313 72
    0x444184483c0404d848803a07140711680ca013820080890300f03180c0568040051003030082e10b000c83c00c41d065040102a071600c002c1507101c6020700c00010a403544110f52090580d03440e0381c40e4441c1146180c0e14843c1c0380410340c0c00c100a80b00184000d80000d441d22110500070800b04005103001e4009004101c00307041035120015480349003007000c1000007141410741e094110700312030041e128011400d00343c0c05130903100b43e100f01041c4002000318120300c40140c1181c6091840d6400c000da540c0d494203090764001030100c098010191040098000c21058100643c030011104551070411000c03008102a59074480d00b010142d00407031444840e50a003880d1044007146200c0c01840b807803221090b811f080c4038040c00080c0c4482d00303548000514101c0008a0340c0110b03880400c690362030500c01840180044c2c0e055501c19202c440303003140c44402f000a08210300307890300285500f540b80c94410411120320800d00301281540111002d01f040715400c4018248240c0c05d41d000346944808244201b00b4804c1550800c42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 578969334 1250 578968084 578968097
    0xb07050f161a071e050c01090515070306030b01031709030616030b09010e1803070c060207050a0b0a0206060f12060a02070203061e07030c050d0c0207140406030b060409030504050d03020d020d 84
    0x81e05603800705130400d10342c50040541e0500f88800004032078034400c10542d50515820302001d10304200000559030002da1052403101e03841d89030f82604509498851002900a540060043c400316025050900042031040c2d101443e121550011a06100b03040300c1b0114071002103031340c03880c8698060091001e860401c641c03580956040480c0114000c402501d4141082c0e001c0d500412300c80b8040044520041c1c00100004000c0d1346c5501c0250380c7c142d43d0260900461441000150b80030050b0160f0310707907160b00d40203840165100c80520601d0f400d802006980491180045001031909118660091011210141e0341d00928014507140910141000f4400c0c3c0c4400a042d1901460b040755613000000f9150100d00d0844d00e01007103032240600d01300d504c80f9920b0584910011900045e60350700f290a84800c03840e101c0b518200304811102c003884041e22095210000512620300303035104e002014400e00340241083d8503200400c00100e0301140440245e440f0061109000d40c04000c20f0012500b20f10303004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 578970584 1250 578969334 578969341
    0x10612140a0e0c1903020a06050f1819060203070b060a0503030301090504082104020907050c07090209060403060c0c0506132102070b0d0903080903030907030b07050f161a 75
    0x644040000800400c0c5280d40d0701541d030b00e520410710541c0790f40e0300010424004c012001c001c6842020300703403100301c2c4182c8880030002603007401130781a90700b100520141d0a0a01c00b051510007001e910842c0a01e0340700c0001180100701124080009001e060b165000756129041460300584a0340094216407003052034407010415a40d00004980c1503070412000440e42d84c49615113074540c2d000e03c10100d01101c1c4070700c000d1000030003d21b0785540b2650007200e103170840b6211000c0c1544e49106409940d1880d4014050502403050141c00800341e1b80c401030421440c00b5600e840721011a4010359420380003d042c201c030740041c00420001190007001c3c0a28514420929589804890510307086402c6500c1d84418000d41d003038005d21251004010a410550380c4595100306100104200f110071404a0001000b02d20260360000c203a9218a440400402a0300d00310340f22843c04810050141d41044010040400000d0509016001200d034071445c03008040068980301c40481e443c1c0c807444030104aa8801c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 578971834 1250 578970584 578970611
    0x41a07080301060507140703120318020102192102010203091b0d1709040e0d030f060810090c0b2b020901120513050f06060909070f06050d020d0c0305010612 69
    0x8982c111030303881c1007942c0c0e6030080e07291455120900d055800c0d25406011310020034003028650f011042400350b541045441c4403041001c140d0886000b0182c0140c0c484d26589070b403d8002c020b4601131038041c201c840725144155200d80c0c002804000c000c40140d40100601614440030007064820f1651000b003076550040240115036a8500d2980c0a0711584405561080581c01223003280c405020140c0240300e0040c030a4003a540e501175019034000000d14100040540c01c0d03591081e1802d50300710790701400200b05800c131040003a16450006030755200488900255955240000b00400018004410900303c4182d80c0d4101920412035601d0503140100403442c942d0381e001c2c0305219101c02c6100c00046c3c503140c64060081460318000010032900c074407080c40d030308184000340d410301c00c0034101d0350041c940d0380d901c01e030984803d614484c06040c4460000f060042601440207017541941030f120050815080c0302417030341134a100c81c90031b1010070369480041c840540c1c85000e1500040b010101400404541120b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 578973084 1250 578971834 578971837
    0x3050c010f020f1011160309030c1a0306040515030a050a030f030c0c02010f09050d11041116060902240304120906050702040f091704060f0219060b150f041a0708 71
    0x810103183e176561018400800210007a00c1c0440700c0100080c500c1c07035140c0340180000c095800103603112a580f05001030076501d40c00724410380483c08841c2d82d056454500070b0101805029055001041c0b54403034410781920b0070800c004d40e4500600003009484082d0070041c18810328401c041040508181c07081200540160340100000e0f030a00e0040c18030688010201c906503201e0304a80d034026140790b00c000c20b2180c501c80007001000d04a90403c92070203101000cbc0864456000e400b0054021940d50300003154031a40310380300d0b840c0054198009038181da038028a000307a6040c0c801f0005000881804248154200555503880b4a801e100d0501820582d018009014a85009100c0c41d1561150007400d01113401a12002c0c0e48002080b160322204074200c42d00340c0043c014503000030503013008a5000b510011b68075504520041382d044681c0c480e40c545034040d1100c034000316000001050f680004002d25030080000300c0791154402d1f02c480c01c020a140d000022991071a00ca5031040c00090040f0340900d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 578974334 1250 578973084 578973103
    0x7020904020d0201030905030f0403060f020a0c0215250312062d09020a09060210290409140f1e030a08090a050d0e092a03070201020d020403050c010f020f 68
    0x54842c40c1414403840100c010b07002e44000141140004520745084d030070703154050401d40344680307030501907021541e4444c4100e01542103000e0004101c03004030301c050b007071a41d2003011103005207542d540340c80c20141d03800700c61103240c0514214001499070340f44103240e80051010900e8420500a128040c03614002070b0003240c440700660702e85c140218524680e501d0101c100b4008082c0440150349070b000b030506c05400d0001c14412100507000324408207005050318410311849804491504c0b10310000081400401c099074000650016903841e00c090110343c04056082c0c55801a500610281c0e1020401904200c12448140e201c04607410300203c0300c88002c404d90314400b14a240030391040c1d588014640c0350411000d0041c040e4020440c3d05903901e540a0049030b03450360240c1e8451080d072616014005244910301e0a00e09406110511150a1003800015a00012144009030400ea505a40941240e000d5801151142c0c0000215022941c000c0e8021200d040c050000d000d4488410700410344901c01d08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 578975584 1250 578974334 578974339
    0x3080f061c0201050a050405030a0809210d120e062503090203030702060307020c06030a140601260a0f110c070509040209070c150204030503180f030a020d020a090e03040e0c0702090402 81
    0x40f1704103c40074031860aaa0040c00e004003103c041c6d01141c00e000b2290341c00f26072a0b80c014803030200b25802c1d403410040b150145c02c0782c1c07000500340003106400845e0306114503940042455150040031002d0903042284034000c40d0032001e40a0428580a0030318105050003580f20145410000b1141c00742c0e4001c4181c50186406960351030341ca03070354080120308022500148651051000c020701c900e604241d03100640c0140403220890890301c683c1d0065941019414a9120b0010301c04c00c410b800059995010741c101b507942d840030070403012210b00401a641000300300c241112011501407282401007000200030042903515900c103042a030040b5040100042902081c013404243ca0801c0081207040c0144000f41140110b4490343c40345022070f01ca81c49a00000710005a1149034901d0f0f1074200442020328000030000e00a030318542d0300b485a450708002e0266801041c03040001016070340c501502d40200d00030030203143d81d5418101103410188001e442201c07030798000e0240c03100603280c002210f900035404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 578976834 1250 578975584 578975587
    0x12030604020909010602030307030c0914210d03090303060b04050a03080c0304150503090c0a0b0316120f1b0905030c011103091e121516090e010303080f061c020105 72
    0x2a40003080203032180d9290039412002c031400001c5c00c0ca83c003001650240c07103103036000d0141074990701c012110300d0a140a9036500b2042e9250000181c9403003800c41d00443c14a80310b084120820385113541c1041030443d01c0740301190302c4908600c00c02da03242c0300d840d0161039888011420682800040b4542500340c0c08010484140000c0c1800500f1040064a000301000010082c51681c8040010003d400555124025205031011400d00380303080c040d4907041e94420404a4150f81c7c440030060028080984010180000f07446070006618513030040f030400d00566400416207003010903002c40450240c2c04be400030451400e500303000650740400d50030b0070150240303007040c500d01c0820707105420740c0f01e601d10050b0b00402071b800d43c01da11040b06840700c500617012a80e0a800c02c0001c81825220300c00b20586c0814501b0300d5000584104490011102822a5181c40c10a01d9101e1000e29442d14081c0c10075008115058108051000710302e44081d44044142e60305e142104a01c26840a210080d100c001d05000c0f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 578978084 1250 578976834 578976841
    0x90d050c03070503040f03110618060a09030b162a0227040609020307091116080906030106030e1006182a0e040e0a05060c130306020a08070f020f1203 66
    0x41054800c543e0704541074a40e226510400c0710b003107405500c021640c10705074a04030411403900a0680f40e070f8181c503140e1100c48508040401c001584002c04807024410b0040d004404100407202c4503101d9040030140d08075500150002400c82089070540b090710391800d20415035444003801102d00d490340e05a80c0701d40c19141e001041c400418500080d1200208000100000d200554001d4032046009030251070501da00c44100c181a942c100b40201940002003000740c40700344884040000c0e40380154401e50900c00003500203132285e071080e404000004d44070080740c14080d10034090340c090340c1d403a81020440c1e00e00c0c210a28180c2081d0f0500202c65503030f00c00060840640850f00110590344c440d07400c0c07a40b0010702030050b0100c102405110300440ca00035030040c80084c000340c0305ea046600300300100010f90750070340700108540c0148129a2175000d11000000081d4817400604191034072030b1200b0f182c502d8240002800310741404810021580a10300304034036980c0200311030600c00c103400d00003a41c965 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 578979334 1250 578978084 578978107
    0xa0f0611040b030c130e01060e0906040617030304050d0e0a26070b1e070803061002010e030d1410030308060d02040204120303060f0902030f06040c170718080105090d05 74
    0x203681c082c510392640081009281400031006086449680d02c06501940d01c4400d2049a08024040d0402161320440746202500e0b0150315079501080081001ca0704c641c030784002e840c440c00000101d07040d590002c814007080003028050b0311461005440c02c1c6188529074000212603040511070b0450034802c036000b04c031420b0801e041581c103207413811044900441e41e0b0a510300796940041425204600c40da0320042c00da4440c0c104459241e80c01440c1c041c10764550304200800c45042c503204406540d0b858000100b800c10900c00f4210b0a2520500042c040020000089580c0c000900d02202d00900340020b0002a8200c5051034001c40c080c0c4e00d51a40c01c2d40d0b032010500a2141c4d41014008514691707143c2704055060308010150360042400f100f000382e8070079990007680000d40b00e00c00c409218800081203401c0980c00494400000d252400511402c2c101d01c1e40c8258003911450300181c48084032402d050a00d0705207500402c4104000c20451905480142e20744505a0040080040000c0c1004105 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 578980584 1250 578979334 578979337
    0x1603030b040b1f020c0a14040209190b070209070804021e0d020a03080c010e0304030312021804150806070c17030705130f05040f1404031107350a0f0611 67
    0x40c540586910600212003165206094129092100505c6920003034002420201e00010441d01d010141c00c5401c912001084065000b03012410717003003002c203120f01418221134108000182042c40d0480d51b00c101b00e0040c403036458401400b904c280b2180105000040c2c450005c4110504420700540c00940c1149002400700d251500d0003940c0b0100e0260044280010b41e00100490001c03c0b0081041c600d00c40c11450301c4e8000c6100150110705140c2c001309008c1a903400402202c254100845081c4103400c0014084803d048407103100103040300710602020f5020411107410030000d0030094040c002c2c56840300c00e8a2100c01503203c10780404404100614015410355803840e2407a10003070803440d25800880c1002905200e0a84658107106d00d28241c1502c6101e0117088201404240c000c41ea01c0d41c4003510120108481c0070641d20811400160314008420036002c0440280c1a22042800c03020503218140803182c1401b03141e03007200c0345a800207024981e046100c2d40c1c0c0038001161143c0c8240303298045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 578981834 1250 578980584 578980601
    0xb091521010c091e0501080403030209010c1a070806060408072d120c050405011805063f1b0915091003050f0706021905030403120305090d051603030b04 67
    0x1c0d82004601c441c0b07a070300b009841d42510740182c10282c0802601c5404240d4076801d02c2003901048004002c034010902c240c0003401e8003030b01818600d0200d155903880c0d84004100ca4184605100c00313509210941d40d005605681141e01190810b04184c00c03e90001d8407100588107100c0f010341c2084008950740b0001601845243e1104641c0b82c8065580c4048100004001000c85040d26008000700340c40c6840d11805058441c062151600030044400e000018480908900c3d40000c0241c2c011003070703800303800b204259401120700c5035440c04200b440070b0086041034031000c0b00a82200014074101c0316000130320b00c4a68011a03a11303100e9100d50031000340d2060716205554200300d9140801421801210354001140e21030f0b01141c1c0350806082c2425142c1703405000360b40058101e20031154421030084e8810003901e0180b02a02e152903640c1d40d4040d104030a80e0441800710346c0702d038200484840c060065144015407405c02c0c034a45030040210300005201124000c05055a501c1c00030619241d03603020046 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 578983084 1250 578981834 578981899
    0x101a190902030f3408091c0e0f03070b03042603090105150405040b01030308061305250908030406081b03070c061b05041217070c0302040b0915 63
    0x10340c0c3c244003100400e8580122110703080030070000d480e08500440700113a950406075608500390103122128007140d84070f00280c80303011240f01e050100302e00c6c001c03c40d40400c0b40400a80b58403003540385c0e0209001c4d00b4030300442940d1090300303c404c080004081c0003044903842503105842211032455003483d010760019400b000203440c10084204896030005501141c007a00c100400121030309404410082601c030100c03801008141640700410020740601c0748190070070b01c014048030b141c000d0030f120f03d412558100c2e908007460301e4007a600728015180c030240000c50001c03440c2816030705041c0070040e41e90f0300c15846180c0030040d0a10002d04070240758000710301c02d4002e0360715680d924104070b80c0003090a0030110041d43e00e140341c9850000498196601c80c82b07100415181d090505e480d10300101006010b2600540b000b1b0902c448404840345040001d020403485142104d9502d030441c0140702c04c49418040407406911520103114800c4400364a01036030a800b100c0800030042c0462a00d582200740d0307c044070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 578984334 1250 578983084 578983087
    0x50c060a140a032405040f020f091e30030a1b0501200a03060806070914060d050c0a02060a02040f090b01031509020c10090809061305030a030c05101a190902 69
    0x1d11a00d180904c001c84000b03d1b810b201d90f0098850701c00491082041c2544c0302e000402c032051040c03e1406510441070000d01c0f09601c1404990b0100d180c8007001c0c03840321103001c0b071505d65800c100380703030f05108888175040c6000f1410100c0d882c0002c2c0110000e210010107043c0c00141ca4010410309401c29180d8200c108104804e00b111184032039165003000c2d03d52000b090600d0004162510700260503841601a5650a40390b985403644c0903015200100e6031a420080400141c0e51900050140c1d80c000c0c150000c03440da666002c030718020708100c40030704800324140c01003000300a00169103d005003590403440b0700184e001140c80c0164010700d484502e0f245d202ca120440002d0340e07401e0b0b90140c07a09680b060180c5800484c080d00d15412100100001070000000b03104821030360402001074140c1d000100c540110481c0c43c0ca00191070049030817400c81c00242108240d05c1080f50a00218884022032082440078011f0011000c5540130740f1507080c1c0c011540500b406002540c000341910091a00c00e03400c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 578985584 1250 578984334 578984381
    0x215041208031812090d150e070317040302030a0b06030337030207020307170f0709020706180506070f2c0102010c092d0305030a0309050c060a140a03 66
    0xd6110b80048034003403002200b10840038000d500200300e407842c1c40a00c0810914240519042120f000d607105015a070f05000d1801c0190500c12a203c0d105102a91f90010324101d8034526120401044054079602d0940f0148401c100607240010382c00d55165100072240c1c025600c0700040f900c0c43c0100f800c25010f40035071402280340140030840403606e41c409a01c1901c003058585905400f43d10400314001d40650005004011800501101410340d0740b03c082960514001303070f10300ea40b0740001500290403566000501100700000c40c880e05110000c48407a0180c0750803140c90301603c41c030340105482d060180b4695000070052042d400590141d132806120f0420b00c112814075244035200106180c0550b20349005120213034017521442c800c03140407011142c21080c10604d807111900d01c0a0301820011400403000c000034000340068051017513541c0c1d00080b91165030810b0380c5030060380024140104410800c0007a15503100068030312903410f05403616961070a95034100c0c000c0030443d201490603000821007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 578986834 1250 578985584 578985593
    0x90c0432090f2e050d06140103030201050601081e07030b04020c0f03040302030d03180609031b030305151c08130f06090f0b0f090d020f06030c070311061302150412 72
    0x140c000d1691046110400083c1103025041d007100c0850f00b4071401c00b08070108258600003044140c214070410020400d480041c1400a01e0202a00114050b27512981044188d590201c08a83e21004e40341400c54915510410030003510006050306040540320990486140c40300c0c3c0440d484201c000c022075859421201c0410b4030380c0c002d804120b1090181600c00f000300fa100e40500414504401c800a91001250740c0300401000031075401c03824400c8142e14031800c120708035001c3d00858002e460104240c641880141c0b503006c440700000b4410f500d00740510900c5032615440c0049541d0025540d42e803051907001d0600e9080d125032180c0607420781c609002c1103190340b00e0f54107011901001e099651098944203c0101400340340300315200000d00b0721502045207400c083c501c07999800070700810360312a90380011484a40c8225071110802000280b46d50401d03038420280a0881784210150115041c2901010b8001c1c415100181c03040b600e00101030b140460b10400c60f4000c02c007484c0c00010a018a280 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 578988084 1250 578986834 578986861
    0x303040b040806090d091e0b030112060b15030a0902030a0b010b07050f010c0e010c110d030f09050d170a1b052407120e03040b0f0405090c043209 64
    0xb40b5861405420042641208000342c0f1500182903034480030903150920404004510400c07120031107045294600141400e008001180a40b04808a0100c010440d0800c0c40c11381d0061904a401050683c3d88552034480000a40f5041102da480101d628900c90000920308011800c0c0a07260340e06aa0000410303141810060071968402c0341070390b94008003209403d080350840100c02001c00d0a2496140041d882003600c1c416252041c1c2c820307040c0049010101300600c00d4150120081800350a030000b286800450082c0100030441d00c0c888030180c56501c0320b281e2580181e11811101000c40d0030340325580035403200b90814081c40d5820b06004401e00f000380c0d1703641c4610401171074500099204008048080403180c40344060b0b0315407802c1e100a0010702c40051954442d0346165000600003c20503000303443c0200942c0400d08000d50f20349081c0410440c9041003e40b00c00a049070030441000800410072801c401c2441c04101502c121600b1190010000d08085d9020b40c00b802030030070000a40f880b1703031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 578989334 1250 578988084 578988089
    0x30703060503010e0c0a0b0310090b1c030f020f03040b1e190816080105180a061a03190b130c02070b03090d02010c030c020a020415090c020d020c1e0402090d020303040b04 75
    0x1b2010a10203984122050080c4001c2e503220b01c0300c0c0d405e4070040c402150300e80c2080030203446c094840110115030f02c03261415207804040880004021194849100da0704000c01000801400081d5251901d082d070880594419075012901456100b07a040d103054102500380c6104191400b50f2240d00050081c004014181c2100c41c010034002c1d41e0720144150388180142410b86202404c40d10350411295940303110b5100082141d403240751640c00119070101e481041c48440092843d04607100c1c1070803100c001c000038241c444544000d14040c00c0e12200d0780c07800412108680108000203920a458008034205441600100ca003058000180f140102d4000745c1c2c0c80c08020180c0c000c0100c90300380c840c21808d81e681d00500200580c032101d541805440c00742e020701c0a408031000f01c031105071344e58100036003a20340303200740000540c21001c4609540740e01405035a4400c04103c400c603180315000f81107556040070b10010a4001c03a40401c6038119a01c401c2d00d807008ca250000c003200c0d2a03540e1042c49641c1d582c040d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 578990584 1250 578989334 578989339
    0x240f040f0f06020d0512090a020a0b09090a0b0108060904060b040903090623040b0c1c111501030b0109111b0708010b0a080303040b04022d090c0c0d05030703060503010e0c 75
    0x100001070003e10200303544e1303589001d55a61501c5d02c00c03001403e0143c0400034102501a00450322104016a960507245005040c80c40f030094698515508226048400410318052203051101e4162140e80c00030025510410440b0124003070345850a01e00024007848100075001440c2485c40c1e13080c11740111408040320301070b41c0d90f04505c04040c0716010760030000300888040414240000d020000c407100242c440d8a842808996902000c640c04070340c0c00e40304d8000c41c00410001c1c0035055112100b40508100340101c80303064509540b46071307103450158205100d01d00c0407030360361540d00520040343c408581a0201f40380d0101c582c0f20f501300300e1645804440c401c9442c90b620b4054049031504005081d20100c460703600182d421503880e9100c0c03600050340100300b02d9200e211501583c0120707948000c840d21001e00e02806003032a9031a1014040460005000d5120b079401c2131210b0304010030001a00d90b00d42100c0d180c0030380c690700e4820041e000740215402c180c3d40b650030802c1411441c080001c1e10410803004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 578991834 1250 578990584 578990609
    0x5060c03040b180607031116060905070f06080a0b01030e030304063303061a0604030b0406060b09030c0d05120d20250201120f050612030306240f040f 66
    0x3c000d043c000080502d018001d00f50001c4000880c0c80713001e0f41c0845140000d55030160720304282c3d4190722204045000e0201c586540d1050034005000c81004080302400240c1103480b451810054080e2441c0d100501001549458079103c100c40e900c41c3d04440040d4840f281100e07240d00706850418041e22800e403041d000c20207984081d0801d0041580c03c205142c4840003441c24403800c685444011307216007039041002c5042158404030300d8507820010f100031801030074030003010b0905240c2241561070b0356014002c03503402030203e08481da0b0042206000c8007030071640988035155900c4d0070360511107440340702907049502166080321800103802c01104c2c00c000e184000720060184542100d5400364114045004a80801c080069400c089a1a40844c0141411305140384031103481000c1c2d9400c400034884040e21a000d200013400d2204200c1454106070025508614004011070501e03007507441c0740d000c0707a000904400c18990030142169810510800f181e984c9a45440895a113102c481c400e420000c0070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 578993084 1250 578991834 578991841
    0x14030d020304111315060503150a06020312010e040b06130b041802040b1014030a0e0a290108060606070303020d02131a0c0705040b01021e0d300504080705060c03040b 73
    0x440b0b105000c3c001c1c502c10205c00140b07052035002c03952a04002d0140100c3c0b41d524600702030301d6170380c146400b000341142d50085030740384010322007002c1d04070307040c3d0013481190030700c6003404002290401417503844041a0f803ea44ca80c008200d100e4040c0c0460a01c9a81052426202c0c44248054900c045000c90003580c0074028100e180040c00381c9041c0000e1082e0000300740c40b4050381140c00040c001d6400a440540c081240b00d80a108242001e1401d2000c0f500c07442d0380001880c81c0751144001c00707041031408603a8602d5600d08440c094403200d004148900c0f940c0002046410140030fa41512000e401c00d000031500d6903480b40884c084124140030f99400b60410140c7c22800d64041c00855982c0e6032181d01500c03100f4030381001d1001070f100c982842410750003885044420300049104036108211028020058880b4000f0064043e1a40881035440e510315403100e10b03425400c0e140078212883d02400000358030794441c1000700c054011440020850b02031070041c0460048040051400380c1d0192103406800c1d103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 578994334 1250 578993084 578993119
    0xf0903030e0c0901120308040f1703180615040513140c0102010b150a140d1e0506030c010e0f061606020705061006020a03110708030a0306030611090303040314030d02030411 76
    0x100f00b44503030f60881488102c0d000000b48690300c03441d005807264600c0030803903801c3e40d00ca041080009620807482d0341c02108100a00c0d20402040410b43d48100191005003000c509981c104448045814041c0d0b48540201d5620310510041d0340c00c040d004450030091038502640301d611450040e00c0f4a00640c205000d19078a46007846246d61140e2800100615042c0b1300d030010f03100b4204016210780c260005002c1480b40c1840e41c01841d11074680d142240c4011803804490900301c54002d0f1590307010380d10202030001c090360480704403801c00c5012940745030404400c1e000520f10344034070250501813540c1100b11008203c05500508600c0388184250382c01a52041400c040b04c01681c03250310010782c04034035082c0c082400b640002621a01c1d10f0b00390741156403a082c800c1d1440e03001e00307442c0703001a035500300820a00c01c0302d100e08100c0210441701c092601e043d040c00281c1e240a03d00020b811110080101c4010701000c00803180b000301064401d64403480c007810a0003085104042c03050150305125091032904 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 578995584 1250 578994334 578994349
    0xc06111b03220b19140c10061703070308060d021207030501050a02030c0304080c25050111150610030207060f1a150a050705070807150f1d060d0f0903030e0c 69
    0x8401c80d180f054185045080030b45803500101a003503091203644203555001e22600001800000002d50007400401d01d9038a2040c01c86400c4c0e07008283d00012030303191000d054400300c1241c0107140c15280610b03940c1c840b50b001440c4940d0700d69001b0b50040c00c0510001c43c1c0320011902008403401007001304043c2c0c0c0c0b08214101a44011110010121010000900003440713000280c6800b1845404450380d50301c00d8005a449510380c100103080040f56100200540d40c4d202e4003c0c03410315540401b404010140f21001d849024010301100e10610b2021340d0800d101c2d219031b040e41c080c145c121806204e10140030001c00c00400c0c01d0036030700b5018901100d44440904000b514100304824401030140381200c0414211415080070300100c2d9640a00400018002d13000c214042c0038090b02c0c621a83c032031340c2176200500401b0b8800d4030101440801800f20b0081035006100c1b40c4c00c12401e41380b10307699010744100c4100a0900c0c5c803030b445815291800d24001c0c10740c9540900c84110307064007100c404d64803960810205 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 578996834 1250 578995584 578995589
    0x30a02150115140a031401350d1b051f060611070b030c0d020403080408010c181806230406080a2a0f03060524010c06111b0322 56
    0x2c00d01c018148003c01074407400078200200140f400003030000d41710f6140c4640d080d00703900020000314048000d00c902c408c11001c6140100e59404100c0524185481507521900c7c6c8507031800a004100d80303843d8045101319a852080740c0e000d800d980050000701c401d80c208414010040c1c100038501640450118000e29900300c08030f803004000c11416250504c4105294802404581040d01c10710414111511900141c00a5417248441545450824000e242112002841c02041181c140c40400541c2c0c43c0d00e16503403d44c0c51020032680d01240b03040e00f04010b0b04195011103010100e1200c015143d8011071100119028200c5d0140405640c5c5d50720281d98940b00b020181140650000c4224600c51040501d40305c120403107011500701d42c2d0341114010001140d407043c1c0700640c407042040480c00c0c4e0f004041400310118411842c06641c5400000d04181541030000e00181d92000d580300351080703030b1091301e42040d40c15802e502490080e625190301da400811071a084442407242c0d5100c407070340707082c2800107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 578998084 1250 578996834 578996837
    0x524011205070513030b06090a270305070212010903080a0c050f180d081e03072114010f05030616230d09060b1003050106020309120708030a02150115 66
    0x8030340c0c0080038080101000703080311040c008100031005000d224080310b00300445c0544c2c0c0e5042103146c0300040c07200d441b1006083c030611510b801801e54201c047c004405140d03200d9088803400054403842c0030744280c030078480301030b40c400c500e80c109100f01801500305c450140d100780e58070f0f4819116041010196906400401c01164003400a0550030981d940948211090924845e450403c6071b00400d040090f20401a00c40200009641182c1807001640e41c40d0104144140703869490114402495007440d0309403580d2450501007a8a8403000c0c0e500300f00c02281d0701d01d0422078556503c1822100f5415584651f90090044000040f40d260407000250040da0403521342079031400e0008080d134202c4042d440311001c0d0400c24808808008103922449408600c604000511801a42c3c02c12160f0b13030b003d081c210105420103005010440c3d0103c184d9100c079074160f901c602c0c0e0510b00d0218504080380d0740c00003056803001107901d21a02e036000504500101d41c1c03200c0211240d0301d68002045100c4800700c0f400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 578999334 1250 578998084 578998097
    0x1612060c1805150919080609070e07300608010c2a1a09160503010c1d1c1217091504060b03060a090309060e010c0204230406052401 58
    0x1ca1401c020420b80f0507807140c000404d2a140c107440009030340040c020b400e1105040004400e112540e820800190032a00c00001040000d1901c000e4a10300301c001803807002000844480703140c4100c01c601000c114405905221510b20202e001c2e00360040190b80308400466007010709440b50340c2c1c00f0b04602c0003c81070010380305201c4456400000444604120225206518884070701c0818042800325402030b9400f0014000005100f41107034502d4200f5000b0703e101c0c4c1d241286c203c600039080440c540b480c24100c6c3d6101100c0c100c0c040043c514031095216200c1e042e2406030300004100700481482c0070302646484210000e4201040091800003c0b10700d8405580440903848402000c1c2c092550712501c02c080100d408101d034000b0908050f030548500642c9030301ca02559042581220004001e003d041c940320700f03051030050009020403882000607009540d0742c0300328803132048a1403501c1c00318100c0c9011800107043c54502003000f040c044035060203810200d85c0100c41e4040d13601800d070340004140e4480703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 579000584 1250 578999334 578999339
    0xb310506030105040207050c061b060a050108030d0903020f0102121e0105061209161e0b16080906090901170c04060b1b071a0409060906060c030c051612060c18 70
    0xc002c0d1b000d00000d41c0c1511503000c140c100d03992110020701200f591a8070580230307003551501803443e0980c00b5280074451400c0c10b0041c00b12400c004140c40c1c05440380240807806120b1401c3c182c0c148010080c0030010f6500014804003045400b803070701c0f030244107040d040184800d100a002030340d4040038040c856201c101001500740b0042c1088000f90041010410b903107021071104294007441030554803501c4804003543d0840000000301c0d1412004058402440f45013043c28400424824413045005004900120701250982c0354042602d05e041c0e0050702208095843e000e1011403c07181c00c140b44058400c03120000440e0030b09010342e80440f1428048241041d588186180d03010000080c015003d200b00307100060404450200c0a00703e816440c1c015a550b400c1403054410380fa126040800e0060600324208480796014200e80b0025805203810b01c0b6400721450045e040004009604044454040c0003092554183e01840c00f19071184004200340c0206000c16a0469200c1c00320040b44400709408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 579001834 1250 579000584 579000589
    0x412030f03020c070608070f080105010f110a0605070315080d08060d060b040f0f0e06040f034b0314010b0c010b0402030915010b0c071503060b310506030105 69
    0x940d10000142005070030310159581d91850010590321040010f00480103010301c194101c02040c44620003441d240644d90f0400b03001802418032139000700204242c00722a0310008606211301d40100d49d01000072311990900c89401005040d4000a6085a4400c000005407032000041c12415078283c03904c0300302c40b0340c0d210400c000c04015030540640d007c5482d003008940d80c1e940e5101d40c3c0c040e03490145000504421501c42c0c80c1c01c444134040c96076000c3c0d120005210124072603080c00849189c2c1460081c0f000b043c0c40600d001c41d026031080ea4403012400e40d68031142d050440303181c0028030511524001010000a07002c0b4195007426a000800c074000d580144501e03500e11004000da071001c000045841419880450b0499104541c00c80164016280c501240411224010b0040070209030182c2042c02d024541c50f00c0d14034500c541003c00c040f0701c1188482e0707402600080000c01c42d480d038043d1500c0300074008190032800f56485d1a03201d010403c12403196000b46003840c0a460000c0c0c02c40e8116030a0005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 579003084 1250 579001834 579001847
    0x61003110910030b040507060e030d092607081c141614030a03021201050a0323160303050d060602060108070e13020d0f0c05100c200a09020c06010803041203 69
    0x12045007100c0c01d20007102188504904c00d006070300c130380d00801086180000040c401000413956070b2007500440c400c0004a50301103150340036a8250001000310b0700b009100541000d002200c10702c000d00400c24002400b5101241000d41d0321307210395448206d440101c00403a081103501440d01c6030204140510022801c4410180410500c1400c0d1108070610001c003003031868100016400001b5000911180c2054070b9000c518010401594500d1b81a4119502d01d5a002d007a01d0042496024414081d141c0c11070070060889030902e5910346071242510b07030030014000c0e8044003078040001e08200740003030060710006045040303c10f41409465000d06209a103200702c3d2025080200043d46440140c0244c1c0e81c000c030040b10756200e00c00c0203a510205103080c22084006600080c45100a0455029003a42100100103030f0341e800040e44450030007800c4040d00f0301d2448251136400203850000440e403c0b019600801d61103140c0740c1200c11980c0d84100440c0c1d240324070b004140810043d1f06828000900401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 579004334 1250 579003084 579003091
    0xb0f04150608160c291512011107080f07170309010513120c030504050405012706032d051507022812050c1002132306160f12020610031109 61
    0x150180c141842481c5030606050003501c1d0303070048a44000c09507a8a11f40030a0351444160094008e120b0b481a40c0704840c440c0c09004e001901c1c0c0c020015a080704e034113511045403542c0d035000c00b004941a000c4251855182c0044615582c10b40ca04000f05900c0300b01070100b4001c0c0e580c40b1804c03200f0b1012010085400c0144840d04030705114040c070002c221555580102406000c4000d14402d4580100c21285070860700f040000012a00d0008240302040075030803030102c00000419168000c1c0f00c1c1900441075801e007004043c081c0e00802c1c01e00c0c0c009100048031180141c00c25403c0700c8986c4400740b0f100c01e403001c030002d904007224525000c02001074a01c03102d5643c861024103085081c04419101681409000c52030441c50300d40c0000c0c1c42d034156400c0b0101c4c60207018009004c0c1d4080140b001d00c0303215080381030062446200041004211018101807005085030b2080601134000402e00d4a000140c0700840310300702501400c0000768203800b40c2c1f8051401c0300d070050704080040700b021040c00001603014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 579005584 1250 579004334 579004373
    0x170718092009070e040642050a05090a0b1b060610120b0f0604030303050103060f09080702010c0501151206050f1e10030605090f0d030e100b0f04150608160c 69
    0x10000010707c402c8468811404011084214000480400341c08410071102c284924a0b2003007504400e80c401d910000b9101403070460309095544250400000d41e100e05641c2c0101d025200c0000d0301c6e620b0800710b2064081c4101c40c401143d890341c50300010400042a550051760000700b03c6010402e8100503034125105400c8090302060407803500c20041040c030360141d00f0540c08284c8a800400400126104007184101c1c10041000404103544c2c2e484000d1144400290400901440ba5003c0c00020745c4002c003190440401d485d03640c0d542d070300304180320481d500c001e4035401c1c50500000c1c500e007610309000784920002d509000983c0407000c2844401400176000200600c50300d40702100003141d91080130b001340145001015406001082c42c0c0c58894030004103410503081c100c0d0f0303460401e4006450070303040040d8480880ca400b03001002c942c820042080d540d80c06410300d44d41511820f910100001030760100e036540b000303641e208900d40449560112215000603008507844000c10b58480620f0003503040d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 579006834 1250 579005584 579005591
    0xd020403020306041b08070315020c010e0616080c040605250b0c04090c11030301150c05010207111003020c15040f0b010807060e0415170718092009070e04 68
    0xca801281c80d007041150708441050844861905240600f43e140d0000d011150046c0011030459542521212140304488806500442d142001030b0081d00408202003c0100b11100340c9060403490001f2106008428085080e4201140d003080202d0704070b40a8030303031035100d4528210b10617401d10440f4403122029801c002d9424201e900041c3e9000d107160003224942011500d543c10302842600f112440b01025081c010283d0040300c0c940d0703010023624111100c2034460364600800350019a203000640b50001c009510024031f02d800c00400100034404040c0548850100141c070a0b0283c040f0321a00441c04480d0740640d01c20030480003071103102940148100554032211600b551030085480e02a003010719941c10071181840226445200c0d055141e00480b4140070303a580c40340c24100c004c8000d01981c0c1d03001c95241100c8031030360345c1008500020311070454481400d079a402d011100174040ca45080354080b1001c58240c0401c5c90308191104c0d0504c1c01070003810036440328001a1040a1507025440c1c0040e00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 579008084 1250 579006834 579006839
    0x3011a04090903030f06050d0201020d050901090b12010f050d03050d09150e01090623061203160b01050112020a021b0f0a03030c02090a0e152809110a05060901050d0204 74
    0x1490240103045442070304d020865481612500c400d40301c4e80c1d04818028681000e00c01e001d41c0c0e000442c443d074002c19040055030780008000498601c943c90304880ca041c2000261090340b00c2c64581603e0494901c0946428910749840c200400303038030703102409000100c3c10301c034480c0c2200031540155650b501c1514802100302d02003100005450850144500903591090351800781300c2e244c003400e414440540c0000c0755070300401c00b9580c00c3c0200035150301e01038840b209100341e41000401c1210039030341143d41d0f0304018a40920b0312510f152000d00a090001e00800241d01c00314a05e8026100b0304d200913001360452030580000200882c0c1404001079010403654410380309030319100503580141d03000c0d6840030002541d03070051060302e0074094078511190f0f20781414813044840210b204407803407034489501286074803203100098982c18084200c100da0465400e4103141041280d0012116600c18405a1404810402000040e1005101d005e403c04020421080740d98441c50040034034100c41d41c401403d040c2c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 579009334 1250 579008084 579008099
    0x90e0a060f03030c06050f062d210f06040c0e0601031e0e150f01060804050313090e150c0406031d010e01090b130302030f09060d0e0606040e030f03011a04 68
    0xc1c61907006901103070314848520240102030007141d0b8014884090901c00382028070200e015240c5004030030003c0500c10f030007460403010031b41708008400b1004210b0a422103c440c41252545002100006103100d90000f0b030b00c003041e0200e00d084c0700707603081a8980320840c540362142d100c90800400850404d079581180e8002d82185825002000c040070100003000c1d940008081c0c6449003030001d40c44d0010035103080010207915601c01505448881c900440f40d6115840c01500d54065180c1c00081504142c8010804800950051108010400403039086d00e4100001e040107580541c0c082803091010001400010b010740c1001e90b0948180e0210103c91003100f07100350848103110549840340c1d4580c00c020082c07040f0142c20a410042c203080d00d001c44101c60b44e001e50b403882740307a041040415010030000c156075207a82c141c0d151520700b08010720000003640e81150311030b042110607078825407a00402010482d0004191008103074a0202503141d41d0910580c20050100c43d0100c0301c081c60100700114408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 579010584 1250 579009334 579009359
    0x20702120d0f0e01080114041503080315011416120507081908071b171b150709140f061b010902040f1406010305093301090606090e0a06 60
    0x22007a074400440707040965006240c3c820322401c40e0304128011006009203100140c0c80c401c18401190300260301ea12001744501820495480540304440120400c41544c0c08200c4480e8405400da98801c5c0071000304161070b040d400f0345e0542080d10700a410a08002407044800d5281c42441410240c0c00d0034280e0341d50031001c1d40120160752003e803080c044003661a40101c4825008034440c202509024140d010103800048004405420f050a070380303480107410350313120440302c0b040740100506034487c1d000313000c1c10b542e4901d03001c0400c246010340c0002025648500210000d17110010440e00d9020502401c1007450404481c5255200208100c2c802c1c20554106420580303c00e21000880c010026004100444110030010f03030700c3c507051003600c2c00c5141116030195441030007400d001945442e028065403a284401e070201c1d441e103201c0038000700503011011440900e281d03100d6024941d03a032190841000d03102107200e008041189407105101d240000c074413299218103078020001d10303a03030fa410524054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 579011834 1250 579010584 579010603
    0x160605072304051e13200703030b190510200303011e08120f16050628090309050607110306010e070f1d100c060606110d0c0308040602070212 62
    0xa4000400f0011030520215460300d40100100d60510080c4c200b020902c3c0d1409031148101403580e0f00104c251080300911024802c2da0a1000e540e11420030703140281c000c18843d0300f480c0c030a1214030b00350000821602c121200740d540240001001c04200c58040e01c60250300a03000b2000302c1240401c42d5004d00410145009220400c118010000340b00b2584031a0b424070f4004200039000010012100c03c02ea41c100c8600080c0000c0a580d502c021540c00808988040300043c598040c1c001840b20b105a50242c07c013518044087d40d8030100080b8041c1011611000f000401161080300104203501c2d1031005000594007850004207c2e02d0210002810f02509821200000701c003035081c032226a41c040c004026103c0c09040c03070305081031010b8640c24000045801030344035240c4803d40d00802031140c1d5020f016540c0c001ea05011441d02e5041c05420b402c2e900000d50700c1c40c0714111280c10f01a01c908540032640d500750b1a100710545658550101035400010103a170800e40320f8885200480f03041002401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 579013084 1250 579011834 579011897
    0x50f0c010c12050906040f020303070507031511070209010509040c0b0703080a0e0115050f0111060a0204060f0503070909051b070312150e1f150e030d0516060507 71
    0x3221180e070100944415110480d00d80d9407072411003000341e800c00008003250420341084e402c0c11351514a100007403441c800c81400420b6402258000010000c40680481c002c01c1130241c03c0c4150060307203618007901d02403007101941c4204000010403003410b000c41c5160300503000c0e58120140d2a101d90403a080d961000d03404800240455003000000440c44c4146141994030000a0040c655100c03405101c0044900490348641c2e41d5006080281e0f0103031280718034076100202036035514a4003a61280007904288a032002158000c12600c80d010700c00ca044900c12121915030041150500c003800009010040c03510341900d0075000707074080721806a409480541c0c882d698609101110f46e072080180d031904460748000c40c48a10092003490b2004c00e40c2903022100c07902c80700c00b03039200710b0300d01215480584c00442c0e00c40300740d9100028254007084140c203c0105400b01c5d0389450803040111450720402c492400c148490f0a4048001411134015581004141c40e0070300b02042007400e14480d60b00c09a80311003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 579014334 1250 579013084 579013091
    0xf060114032a0f01050315040c12180c0902030106080a050a0b060304080a03060f0b0f03060f090c2106010c02060d110d2c0303060d0515040b01090506090c0a0f050f0c01 74
    0x10945004054810fa50400b0b1030030504504007140303080c5d100b07500b08980340e1203992070b61025102d0030700c07440c03004071003550100062020108421040000c01a82001030390302d00010f02011071707a040d25000b202d04032002035482c0400c5030f03503910a40c80105005050307c0651602c58008445036503c00703029600030350140181c0382e69034074952009400c50303540c2e6002043c00341241c44100400c54200c1e041d03d481d8055042141c1e5295a03070b10000300013215100406900401da101404003100000000e80401146455040c03075840c000d05510800c080102c030098001012640040c00500f000406002101c8400340c000c60b41400e00a02982140c10544500501c25643d442e008401000c0704201034003020b05070501c403c940d0090007115241d04c00204024040e440841c480c0c41089800c02c101c507084200b50001c3c040350305240c0307405890b2400a1183d10700c1141490041507052901c002c51a0088212401c0c880c6400036070328094800d006201e40b2081800014800e003100d22415500809580000d0380000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 579015584 1250 579014334 579014413
    0x7060b01030b1e010c020604080f010504050f0307020f010e1807030b1903051002031e0109150501020f071a0c0f0a05012012250306060207080f06011403 67
    0x40c00c0b5a000e82d026032154962040c203140ca1010310105502850b420300e4030a10303480150000c40d02601c2035a12000c02440703031008044200c4010760210303000320320550990f20321100c800b03d00d50f038034000c03500d020b94002c1c1d881c40c0304080c0d5030203450349111481c0c01805010320000000c2c807040390300800719021030200303444402884141c9031407034000503000084000524034500f10389a0554400322200c3d810103c9500002043c00408101012447c03990024000c84656868044900150078010310300d210782c8500400c080340c19800410360191720710b075a400510589140c04100c13080c1c031030407054601003000200459600524140812213400145d440140900c026a2900c182100e0002850803103170045c018800c8064045401101e480c01d1040151003ca603c0381d00c0c5c9508070170705076001045101c0928404020b426011340240c822104244c00380e90701c00340d8441c50241c40e000100480d952a8100303000602c0708100b4080d0303070940510301400b200c1c0d0203501141c41120ba140000651003200794201c540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 579016834 1250 579015584 579015587
    0x10e060f060c060916030503030a0507051e071a0606121519030c061b1202010f06032105090f0409060b0a1d1f0b030a0b04020d0c0809011b140903010207060b01 70
    0x51170f0454448502c44141249582c5a00303859000261103004074686480116140b18400d00039619604601046900181030f5140300006682c8084ca04990011140d48260803a9030a200001c0c031500d409071a003460107940c46820104840c005041c81c41e0b0044042c1d0907001d6407503035038040b580500c2203000c5041e01c60641c106020000803030303480401005a101054440c2490340c2002e1607201e544000d9900d12000c0b0144140d01418100100e00d0b00b403883c1c032100005000104540510098039000040040700c14010211b54a10510f038110360400c485021a003a0f034102640060002c6010755800a103541c03c3c0350010f205d0108946c0500d12803036128080e50b14180c0e1407407900c0d03080038448002d0b0000c506d8060300040c91070507034480c0071404080131002031203006a9800c160070760280100115030303c07500c2c007140c4d1004121680034200014400c00000d5100b9405201d8400c0308140b0b04400b9540d0507000c81c0c00c4072507003a0714503183c400d00300610055031240c40900251810740e11a040210785071290320700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 579018084 1250 579016834 579016843
    0x311030109200301030309060f0c08030f040312060506030c0918010b0901120c080a091a010303120b09041707050f0a0c09110313080a0c140d020d080f010e060f060c0609 74
    0x402c003508004100400001b034000103034100312071081c141941d281e000e104007070300c24004090018082c41400020050396001443c40c00c3c0c03080c0e02c6500c0381c410300240748610f80c08880540c09500d8001e5800c00100e01d01403111005400d4081e0001d19441191105241850082da002c0c0d00c550040600810140c002c2d40e00480d842503906006001000340e0110303c000102400409801c24081903902c038101c03c2441079074030501c40c0b04c5811444030a0f00d5617403440d0007440d00c0101d01d0000e07000c42c501400b01406103006e01c0344500403074215149050a007413400c906026a03003e0700b412640c5105a007000c0c92242c5060000c84c1c900350083c100611000d02c1c040807a01940c050701c7d40c615601d0000c00c100b100b82643c0e02e10030113556820003074464440d100401c05031080048620f001c0c12507402c0c0040709001220018400d0740d40d04840e0709a0350001c01014040e102d00b1020b90b010100c0c00d09120042c0316411740054410340c010b60080c4600c036003440c004c4c0440c00c954840b101d901c4083e00b1030002c0107900101040f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 579019334 1250 579018084 579018131
    0x20c03040e24060a030609140a061a07020613210209060609060a0c29090709020702010c060213030f060207020a0503191719051201060e0f0108070311030109 69
    0x50300a14169145032925048002c4a031a491107400042030300d03d2454400e41c001000750459603000c02c407140d01d001d01101107074001c8420b0306100707090200124906140e001864001c0e83d4121120b0b003010b906034200013141c0c000b005584040041c009001a081d08407660803c0106081a40b2950400d8140180100600002c0c021401407100f080111620b450700d00c11910603081c149086205c0042e18a084045aa180300003219000000b114010300c5041180319030340954906030440f82d0869a88142000342d02030a00080e0102e0000320b000800301d880c60300104910610050403201c1941c503a9a07440d0f042c2044002a80c40950100300c1800714204009601c0142404400500d807004440700385038421084068001c104451814005030720042210603110781d00903001541c241d0150310080140150081c000b10b072a240500e500001c0c07120f024401c8286080c0c400b524062401d4400d900644849074090211401c25a9840c01360128140380300c0036601070b055280300400d42d40305030f85502a0030780a81 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 579020584 1250 579019334 579019351
    0x617010e0303060603040204051305060a0b01031505030304030213060e07050414091b0c0c030a062702030604060e0a050109030503060f0906060412020111010504050607090e0f18030d020c03040e 85
    0xb04180046659940c00360b0f035025504035030104459803990780c0020301e8070b10568020414461002800703141c07034140d00250b060f10801c2c1d808000c0481030200e20300204055104281d0150410403061000d810040024000007465030b80c04180365584296220244008a40120001d074021900348414a04041e03e02446201242c82e0921130401e94014540c1c16400350030820f4500002411070b0380c188041c80514200345004007914040d652505010000d00105034101a40e404581c0d1480c040e43da0140703400d02e04a0b00079004040564850b502c0724010710800310420003a1150140e0440010310900422070001e109076200b03500c0781450024440d101051081040c455241c040401c0b40c161a01d00644084901041c2200d8222580e400140d55100c4240201c01d415420302c0208418400001160b0780181610340d1041c0000355950944022464291644000c0c0310940300803c1030b805110100c03404a140d1001520724245501c4070242c2280d10207201c0029a1700003180812a40b105841420b038400d009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 579021834 1250 579020584 579020587
    0x4060c050309100e010e03040b0c070806090a112e02010b03010e030708160c030c0f0b0928050607110f010309030f0c0609150515300a060617010e03 65
    0x1440050303d41c0420642c412005581d0210400001d80c2500020154030b0388500b40c0342c0c0d80b43c8450350b08405030300c541487c1004d485483c400055451000558a00c6035204001400d2001c19541d00c051610080007100c66018510000c11440000ca96448500852030b0507803441c2c580c88014400b0f4291a8200803440c401d9240c0001071818400100c221400241e202c1095a504e141f140c1c10000d0344c410381d690240100401c0e1030044100310821640c501070f18450490300c509076684181800315842510709d120b1f00405c211041d03080030004250003400c04001001078184007078560003c036245800440c000d81e541000b0310642c1e51300382030170031114010303c0082c40d090203052131039100605420b40c4089030404000b058006801400010f520101206500c019000c0e00c8850710311886010300760030344d0708082d0303a0054482d41f5010f1400e084000801c5946032441144048400049014141208600c203882e0007819160000110244922401b501311a02c0780701400d440c0034800c508480f8030040e5002980d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 579023084 1250 579021834 579021841
    0x130c030501150c02060f120112060b06040f050d0201020a02100c03080c070b0c1308011409100e060601140913060303020607090b0d0b03100f0209011b0f030c0c1205030304060c0503 79
    0x90141c0c414508a40554103180c0e1b40c0400c81d010500351242c0262180d081c182c010000c1000d09901280c00b520707602510b010700042d90007604002c454881c611620045403050a010485820003012107020303180140107840c2ea007607842d004503092444500911001640c401c2580f8201500079407841d4014200118490230140c107039544006000020700f03009000003000c26200e480440c9202c04001420320a03000380480340d41c1d4131850f02000015030384003030f441c01920305502e204509440744003142a9414002c10480d104d41c80191807450302001c141c0000201007140000a80310704200d46250307407204600207400381c0303503046c02810036102030240700400c1982541007180c0001c400582e98051011030000a0004507480020f1401c4158803099965070304000382800408103e9002c1d11075101c0a0b29840103210707615803420f8070000b0141d0020306000c00300016401283c40760b440c06e200d99129000c5148500c2e2a00f1005204c056040740407103c2d6400081007000300301d468000d9501004007410070030b05608 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 579024334 1250 579023084 579023087
    0x902010c0614060a29131509090c0503040f1b0504150608010503060f0a05060609030a0c0e0711060c090f0a0306060305120a0e0d1b14040605010c030c0f11130c03050115 74
    0x1d4071170400c1c224410000c02c40f5015003050303e11400040c0020310b18042e04c031040d0040a400320517a44500c4100d02d2400e0120b241c654061000c80f0301c511b91002c10700700e070807072203581d44140c00600801c0880b11245040012a8035100e0380b094408503298454030320145403514800800009c0140c000600940006d0280800080314010540e045050f096000c1090382c0c1303660103d8401c2c052002f1942e0700d131040916040a121514a0800c1503421f41403021040383d84660041c0c2c7d84483c0503a50f03624603446000041e040e420844003030880804002d003190703280c3c0c00640004050a105820035100d8030380c0ca090810400400f041460841030352008420309184545102401408840410601401f8810240350810080f0601e02c0484000c040e1201e981d181ca0b00044205240c101c0c0e00580560301d0140041015030040c88581502981035440001c4014195228007000c00e04040c206d40c07002460b400d005075951801c0c00c1d40741d034116841c400100491000d0f0014240c0703a046c0d2100c403442400d0304641c41d045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 579025584 1250 579024334 579024389
    0xf0b0609010f034533021b0c01050c031e0403050d080901050709030c15030906050106110c0a030816030309020406031203140103030e040c02070906240504080307060902010c0614060a 80
    0x103404c699508540903ca144468220a940e030549413510b10024a160001c01c0a03401f205c428901c001c200c60072624510b00544603840358840c04581588240424580e0394680d90810040311441c845070b03410980c1d603642c1c940c60641040503440c0840c81d04010889001c80900c10954004040d14040000d2031030368840c1c2e26404032900844001c1011105400010350007900040152a401001089190b07913442008084d800c501407105414028420242c13094030b032074a810403d80f50481c3c030042c9011403078440564012190081103041c55180c8410001694407807107280004c500030104c00000003031503100101100c19a00c19410404203850041c00801da00c00e010711040350040c1c07400200742880130401d074500700442d1301000710f19081140c0070600d40c4000142078004404001071490213503c0309020368540c0114090782d031b2a68002e00c150408500c5a4200548840c018103200e406040c00340c0b2480203a070203420801c9940c071100c0041c8011402c1c444080e030020326030134203901030a202c5d08030045001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 579026834 1250 579025584 579025613
    0x608030d09150b130506180108030a020c03061608070c1a070e030d09180207050a06020a110a030813150c08011502030a1709010b091503010f0b0609010f0345 69
    0x40307170f0b07035a80002c886445a0308080f1002e0a0804003070181e60391013081e95507a0b480180041d006004070310b000e00040c100002c8043c06015440141001042d00c104100c40701380c0c0080541082001c650015400704e1170f00366010294a410b2900201c042c035000201a1406c104101803a020303030711211001c02070710362010100f002e5440185100c0081400c1031a500064010598003810f14000c000000b010843c10750700410100816803259902188980241620b50b122401c0260101e401e81001540381201c1c290100d01580c450842006c0c00da00c1c60202804803400740d8281404915240011300240000ca1010080140d40d48001d51a08901c2040100003d505c506803510400c0d41c0004610308800030341009043e00409000d21250b03141c41083c502c1c0b2100c0d41255a0300030351800e003111004501d64064800d0980000e040c00d4a4006120011101c48070308506950030555a00780134001501c510806201140d60700000000389070a03100711503071003802c61403e140e924140700e20b80400519400d210604 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 579028084 1250 579026834 579026869
    0x417030118050901020c16050a09020913090501110a2102031e090f0d0c0309082109010e03010c0c0302070b030603060c07060204030b250305070e060a030608030d09150b 74
    0x31a5240d4540444c00382c05008610142070140e840440240b140800c203000840788100d0742020b80546c7c80c0d0105c01241b0032122020b4111003104419462019640c0240c1045c0384201c0001035071140c1000310140c140c00201d0324400041d289000c01884c58881c0428000702d00c071070401103117541172a01c00811031000e66010604203403400400255004814403000b4404c0c03440c070341980c039050061000144150f518280c2103010500d4201c010030084c0c030005003843ca00c0000096040c041c4040110302d403071604100c1c002c0e41004800d03c000724450b00c0038001e1a00c4d5416588840403003080c0ca00d00a420400075401030001143c1c00e10403c21540d5000800907003005403040002d90f54001401d0001c00392250f40c0000d4001c059080502400a1103403948599500c0121001031203520000812001d41e6411740355080003031000403690413945802c60040c1070f4101d03c1c0c200054000c1c0c3e00c00d09982550440402500940c3c0e40322128000d0020080381114020180700d8100100015440043c000a010b400d9881 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 579029334 1250 579028084 579028091
    0xe07020129010c060603080405130b0a0e0604020730030504020901050909100e07090c020c0a06080907180c1818090309090509010c0e0612061002031605060417030118 73
    0x6a40d010f1a0101002500100d003881501e03201d042c000c207035a04c0741c03041a000d200c0e2039507855640911407140d0041b0040c02041310b401a4904101c4080c1e009000c0c1c01203a0041e800c12203100024a804018500018030f0811095000d1104a014510010004c441010316090408000050381e03008210741c10340c2e004650b50030072a05c9406400c1c1c504951941c0701d100f120702d0455150103480c070024550702120031000302072140d20214841203843e42d030310122042d0020640c00c4c0c01d00146000d40aa0f42d4000d0b461000c031040d2507501c408500c0901d0180c02c0061500395181d0728900c101b44d1007450a0702440801042c41d0300309151450544002180005580c0c01079034421913101054451801d04c0c2c000c01070f1810501c00b508018074442d009142c50703141c0c88041a010018040c1c0c5052010a442102d000180c0c0001903949a07001e001c4503001c800f002508500003080104124a084000ca804403801a002001c0502d813038a4540110014030b0207445c0140c1c824401000300c400c024003601041002c500c03010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 579030584 1250 579029334 579029411
    0x1303020d0303180303090c0b0c0d0809010e0703030c021e0d03030509030910020309011e0f200a0305030a06080303010e0a0905070f09020c010f0606050a080405031201030602040e070201 81
    0x71002030071280034500b0f510030718031403090605506400080d2a64040c0700c0c615102e95440e445102c40340714401c81c55100750000080342d110395024005d0789070b00c90703015400440e40c078010721000e03410401d10b50811800301d0b555912032015404c004c0b058049210450000210718600b000020303404c2081d520006080540702e0000404150062040d0b804c1e0380313009045442d1198600d08081d440313403ca504030710f0000c1e808003601c1081262003104181e018215858010982c2505002210f44007440700750b000c4440c192419102d9035910030030410140b1402a0307602900c90400b4124081500c0c00399200c01d403140d10510041c40030b200250000c035004200d00000085000c46440d115017040504d40c013400d2110900d5000044813200e503001000d141c0420002008068203211222045175591300580000500c03d000354421719000f6404150810701500880e0308181b400c000000c018a42600211010f54000c2000c000c1541e80a1010740c0014540c0003c6c8141030216100e048080004624001403403000c0051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 579031834 1250 579030584 579030587
    0x1020705150403090905040b01030b0a0605100e01052203140105010f06051b0d020618061003030818301602060f07020d05010207050c100203033106140c1303020d03 72
    0x1000200510402401b480c40c0c64101160146d8003403006803000c0010500080455515104070801e480700102018880d41228404582e04408690b0140c1841000c000f40303101c00040746003c0306801440d010040505003145003c4030321182820880015a0500d03005101c07086d030503403680301070b0340c46490002e803140b418040034481040da500383e005150041542840c2001e40c0459100c1c0701e422913115100e9a80d140607000781d0f07202000c80c0e0751060f4034900703041400040c1c40782e4412078101c20720b244030100c0d10618482d824107140c00601134518017484000d0029078400700c0751001d0000b6444014040c01c00400325a4200708440070b0384001c5c1b144000207220000341c01d984081d501c840750040c0840c54199124034082e8000d60010710300782e0711803040d0002000d05242050b07803401078101c1c5070f005e1403d6454258400e410345058180c030b0f0402e407841c00d00d079046030241400ca840016024040c042000c5055030805901030300c0203044a400c06e00304102c5d14801050300c6490760112581134030241c00d0b800301800c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 579033084 1250 579031834 579031847
    0xd1e08100314010504061b0801030237030318050607110402040f0e060301320406110c0102030717060d0305070c0f0b180402090901030b0402130c02010609060801020705150403 77
    0x8002c000e64050034208445800c150f100a1099108140c00c00c0841d4a00140704060903803a0440e800144a800c01480182000d0200c0400c8000c22010090300c042070016004901c6030b846070798984c450f11114200103040c0c0c006041e030023081440e14051055070424020070000c3c441c90314090300c8002c04148035021611558120303401080023241c07160305152034202d000007007801640c00c0ca11940c00c01d00001a081c09200e0b1010760209a10140e5081d000c0702503050254140042c4241c501c5e942d81c580170044010140010107142e082e503000107a80e8900b0003005854a8640c0100624104c102c00801000d07403030382400030f18903503014100291110603e203050210030b110740e00480ca4a8550f880c0000f81d410842000d00492500c0f40403503841307840300b1014041203008010320b07141c2c8000860010004a03016450700e80d0098005803090b040070000c14040001d85403007003401d03030060399038080c00c0000d1110b03442204050802003000358030b01201c0d500c0b010394a580708001800c4040c40d800214040502030700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 579034334 1250 579033084 579033089
    0x20412031b12110f010513030c08070203010612061a0a0909050715050403021c0b041707020312091825120603080304030801120f03050906070b090604050d1e0810 71
    0x41c555000b468801c000410308001c49107001028070841c140c19004440600809129881c403250342c07001c0340300d191400c032181e070b01500e400e5481e60030400101c409a1000e01809002e0b200c0341d03001704940c11a500d4844100ca0f1030140c071500e0340d00e0001c1d8070081552034244440c01c5604444d00410703036800c0d070b003041800c042881d4080d080c01408020070144941e00803000c0c00440307008884100881c0e032400c0c03c00e034039005020b800401c0c1c03040c48400140000c50b80b80022264a0b86001941c0c10103400d9400319141130829034089181e05008a81c000c0b0624020048202d540e9102160480034100f48522020002105411400f0308242100002e000c510402e00c41401071002131091040d15603e041840e40755005503410b500041100002140c041104100140c2c00c69006140c9284040d00b900c04440a8000030a00f82c0e02c020700300180c4006c87c0103004924082e002c3c4070041e2a5a09041c40c005203401c0c1c0e091051401e004491041140c282085910450540d2b82410070402c0c1d81d480c0c03081040b5120164 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 579035584 1250 579034334 579034343
    0x10207021f17040506060a0e0c16030504080d1d011b150e0a292403030904060b031009090b0127050403020f011505130207080c1905060a020412031b 65
    0x403c828044001009802103105a5030406600d849a05086c0341440841c1c0f001d02c004001c00c11300c00050b0340501c11529443c0030b0300d030090600e0744419205013001007044104000650350700c40d2454141d06c41142d400300010034200806000848032140104034001e0401401e109040300a03c013484903150016140307020690180c030040305661070120f060a8400012045065a00f0310240e031503c0b602c82010f02825a1070b400301454444500200785c0401c880700040d400d8002840340f020603448500400d0080d007401c080043d140c3c501b40100340d41e0464558003125400d41016000004642d200711450306452504a0000381c7c5600201d0301c22000d4140c54001120a24050400003031682c0403888a80f1006404002c0c401d200748a907490841080601070154441070314659050000900d600900006102d80c03062800e1151503010541071405004020346040002c1d60701c401080418820039a1081106400f14180b50400321410f1010b21214402000d100381504445240b41c0007115450545900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 579036834 1250 579035584 579035627
    0xd050315030a0b090f0604171c1a010e040c05040b1e0d0b0306060a051f090801062c010b09090a1b020717031e13030501090b0601080603010207021f 65
    0x51801c00710104084450051900a60110808050300410030324001d58000c02e10413541866451012340365070058079044618086544c0b2102d078040c160080c60301d4200c00428001c0e106203004009172080c1c85000d8002d103da841c00001410300d64100094800f07860440000076140c0011b0f942d01000d2905451204400d5440856036814008241d00814420107003030701950f4560302d07031405200008020b40503203a0302844003040d0100000121100c01024140c9182031174805640350300e40b60840b0701d00d4000803219403c00000d0100d60059040d501541c40c1481502505589441d05140d000d004030b1000c0c40c824841c090200d48c0e240010303000f07008044031a00d0380c04112012241d010307643d06541e01c96070100c03190408444140034004800e440b07100000c600704e400d032044582c40c01c2c1e94652207240d004181c0400d14401002148091045000080c0701d50420710302e904200c3c1c0050010640100805d10a0303004211090050701d59103484001d0303144010140c81c03140c03e005800d548a040c040e0071190201403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 579038084 1250 579036834 579036853
    0x50f070c03021002030a1d03030708040b13081215030303091c2d0206011721160507060305182d030a080a050c090a0e0a060320010e010f020d05031503 66
    0x50640c0320348060f603401d11802c07c0500c2c8040140b82c603400700b212640007103100c0c070b8009030205c0c01101d0b5060b808050450109110040c030707078604020340c05c50003541050781c14100070420f02024148004107030907401c9009609510740781c18170315603038403003031081c400f8403028000304800c154001c5030354800c4881e0401c074004001305c05c016260445c03003101a40d100144584c0c00005510194000c0100c42d401480000d061000058070403d0a203641070314111800610070050030100e6807008000010a03032144020301041880d001c4001e003641c83c060a030349406001c41c0030038299120000b40111103000c01c000e285044026010005821000c84040070200740800203d0320700256010090900c52a12100708000c00c0d16901c070030005a0260503000d64204c09042d0301406550f000307195482e44015100b00c04203a15440e0740e202d084d2500a0881076505107544801c6030341c7d940e0080301200e660a822300c0c2c85021002c00c818001e41c1c0f80089402c47d02400710010100e40c121980c015100c3c5035010150480e042c100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 579039334 1250 579038084 579038101
    0xf23070c1a04150605041e0504140d020604120504060504180939050f010804050a021332010612060b13030311150103060f02072001090603050f070c0302100203 70
    0x44103600f02d41e089a01e44200030409140c1031194940302c008100140c403002a40140c8000144400352054a042107456540101038504210b49100140d01c0d5000e040076041030b00c1c101c0b20220b03004020b041401010310041c4025640041900c0c2203070083c0c03001208000c4950280002400703103441c00380c00d070b20700509821b0074114026921802c40800c100c2070800d000307c40090131a1840280620796022a2117088042203610402c000c0360000c0c040c0054400241d0140d00140c00e030840059007070000303a283c9a10380304540d600c216020381200000362840e0b00c11603001801200d500305000c0c030303401d10401000a00e01041550b002e0700c0905118000705135102e080d50700c98902c104552004a00065a940020001d110041000514070340c400d08191526401c50750754101130195200100912035080c8500d6020910b0b143d804402510365a40c50500c22815000052580c070f100e400c41414941000d007030144401c43e0000d690b41c007031458a0460148112440e08a040c10150320604503410f0001c0240001403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 579040584 1250 579039334 579039353
    0x807110d050a11010519050402130504050601060e18040308100e0114040e0d02031813020d06080f0c03061306021e04050f0405090d0305060a08010606030f23070c1a04 73
    0x45880343c640300209040c01201c035082e61002c43d02c00d4602034409400b03900d41e0310913030491504284020081d080108101e842017003151804c84043c3d440d1340c02100100210b6401003803100803000c00340c070000a6031380689101d00b5888000740005080108040005406800c0c009601c0301a20741070381001d40559490100240c100e840040085c80f591900d00c0c510f203040341c002036070b028500da41c0c1c02840c00d04ca41c9100c80c0c21021659054540c1080d203e035890100b84056200070f10724904c1c002c04c0003070f000d400c2074005403030403001c061448060f41c004503030b41c074642c2d400051181d400000d1240e42d11002406280400c060301402c0101100b4084461114150b20305e43c401520a994081e256200076941000802c01030303550540d0f10b502e854201c078240c44001c500c660840c50f803099000c2d240c1c00741c05584e0a4024210381403640100006070343c61006420030b84d45405002c80030191a4009040c40044440d0900c030004040e04180038013020788a40307801c02440426185242c0c1008240400500c3e1505020490 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 579041834 1250 579040584 579040597
    0xa03050a050105030f0607050a03110406030e0717030d0905010b1801180c0906050903010603080301120c0504051005060a180e040b101a0c100903110f0309060702010807110d05 77
    0x180e4100340011595040c000703804010b05e15400010070098a4480301680c595000c119003004050716100b07004443c0d410300740104014440c42e500050102d0b4075004113414821550081d1058810f0b181494680e401c000040e42d585e00121400011540094075015004141d02002030f9002a20010100601c103240c903081412610440c0030500340d800044824030032114240103020110354400320600002d44140c004d401640005000064030039183e03102e0041030b4209078401c001541c49603a88d041001a0000c10400800050b00d042c02241454034154200c070f4848c0c011075001d08000f02d11464038500c5a05e00500d150901c0c2d17200c0c0c5ca0720380c0741c00c00f020442c00f0444040c0d03070402044011a118249140c840404c4540880345648401d2161420148940c8801c0b190400b070f100c0d0421010300384103988940030119200b51504180c2405924095080c03210f11a0a51041e410600a045140e11454203d40751154246001e1800ea0f8a4000c00d50b40440c5c500d540142c10304c180b0005480261704100105070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 579043084 1250 579041834 579041851
    0x6090b10020a0503030f090a170901020d020a05030405040507090e16270e070311030906010314061b030c0403050109050c0a080d21020f0d02130605211b0a0305 70
    0x1041080114242e079a2102d00301c008100354002c00001d06d41c3ca005000750f9401c043e1190544a40c0120f544400c928141070184c212100040010080c5c02903804103c2c03210400240d0000e06200b940d1610b0355500c9005512600b40500c0d108c00c0000d8810388110f0340c0f400545030340e40c0d0034042e604014510301c003490900b1420401252900c1e42500d00031207a44000e0b511080908050fd400500b05000384100c04005490340c0149515405043c1d4500014000b17144103a0f100d100601c81580f650800c40c2c0080c03c1c01c8241e40030303600300909021900c03484001000b042001e044200d0395a1716044c8540c04d451083c0c0e80040c04951a01a81c0b004000b0040380a0390040c008840c44281140c0b100c4115484001c41c02c4500041000000b12521003a00d0000c03008103040c00080050409010312196603e80d400110001c0700c0c41e60025108e10102d00103c041c50251040746002410f0101080c00410f0030214111440c0c4a8400c010000c1c0c0025400807031006656140d0000680751105080c004e400f904041c0c0b40e200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 579044334 1250 579043084 579043099
    0xc03092001080c091c031218051005010b1e07060c020105070311160209060a030f0308010303030f023109020d140a0506030a140f06010e04120c150b1306090b 69
    0x80403c005074040c2c902d44e2400420300d8801c0890515050071074440450f084084c0b140050382644c5030000d074031902c010308803c0b01c0104a1105a890018101070004401801040c540300050180484803000d940030f42e40f408901158a8500d1041c0580303900030700d81e008050f503040240070380f502641908903e0040c1c00d2038400784050410a40c501d0701d54090012100845042c2d40801c00143c80c0c02d0080c0303a0442009029100c1140e00c07510303504943e0011420650100320454010801c050380342c40381c11108440a20218100151280082144500c110507441851f1780030211981200b0030018103802002074420440d56500c4245050015050780110b54060a000000042640926000340c500c100340c01405440c40d02c82c0c075034a40e10241d60403040c0c000144203024400d01000303010005240603100c10142403850b0310301843d142204403580040b900800180e1050b0300c2c0065650010014030100035803002c1000d4595101046a21b010600708281c414104140004c0c2001c0700c0d40800040d203826075565 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 579045584 1250 579044334 579044341
    0x12190507051522180f0612030804051509060c0f0c01060807090c09050303041a0708031e090a0c05040507030b15040e1003030507080d1b0e120c03100c0309200108 71
    0x4200b072402610400c5048101310740c44120541c50750b403011248040c0c1c4400000c4603a150305210221501c0540210041000202440103100d070402c100c2c1a540c0440c060020b003894032a0030b80d1384076032020b8501101d50340041522a541c1c504c43d0180c6910300e054000030003440e6038030003d0680e124002e200302600940b5111004250b02d108010f828142c41d0050011807900745807240d0199424000760921250b03500038003040c8001030f482d200540c040c0d03422010a140c10030022410030740480015013000c005520200c40c540010f6540c125100456004032030000d07044c4c0d1100010390113041e80c0d8040c00d074031011100c1c5c1034541c181d04c4400362050ba10305540c030489a6889201c400b04510542c040500400c40900c103490008802c1c1e0020716103198a1030005c41c6a10801140400d030011b406c0003200820302d50284000d00e0704001d84401502402e02008140d400c0d90304c2c021a450b07407074025101c445961264481200e01d4080d400103482c15500428846141034044410585810b000b100c860008031400d021 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 579046834 1250 579045584 579045637
    0x30f0615010306031106030a1815050f06220f0603240b0603220b0109020c1005010b161a04031805060414040e070b0c01090c05121905070515 62
    0x143c400b502d500560711189041840c0802030301d60402048807044985074074014007038510030310302000041d20881c50403c10903040d0714440d040d180c008040b01403682c40d1208000c110b40d038021036070810800a4015000014922094102a110110160100b94100400041001100794052241c185e6064129000d0b9400e110784c942a0307031035101400d900034018000324080000e8074515440056024004003056a00b958401c045000240d000c02c0c007950340407682019010051065501185103007004000303540c1848207202d40d42c0503041c08400300c6c1c4080044401040050003254151100e046400d40c583e26251a000700310800d102ca4208000029200000d00b5080c00d60603601591550030845107610341643c10701c030041c42142c07107000d120700c0352441c00034407801010018468950b000380085481da0044c10701000e0325000b9400719009403d602c0c03565240e0721010510544424801c020481c2c058420304090349032001680000303611800c0140034281706044d040c02827408501d900780710340c130710b4400842 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 579048084 1250 579046834 579046841
    0xb0a0e090709170a051c1b0b07030e120d0b10020109030f031a040e0706031109090a090206120c03010608060105090915060f0c15010e0c09040c0c02030f06150103 71
    0x2580e4010070000802407181c00008550514400b1102c0d0031030f10444c40359102d144c0b8203410b0780c01302884d0400b840b404914060b880305000c1801901c01d20900c0f280c00051f0341341d400700310004100d0410103698002115000c0814030014a03811800010740d501c42441c1c203140d400a10240c03580f240b0624003481241c1d140e41c010302429840d1038160321045800c500e50b0106070050304094012142c51030b0716404541d22969070380b01e040808140307800280422401c203c0040c04407404105009034481c010701c0400440d03940c11a10650000c80c00300c2c00304203100b091001c03075168018805000301000c1c1e41410000c076107140ca00654100c8485a5903014151602c90055aa43c0703e0400b12a42080001c80005d400060f528840e03140400060415860b042c0c02050101342c40d0483d100c0411760350400e100c6035080c5203916440c14090900440c00080c2814440c800440ba881164000c0d400f0301c1d11b84510b42182c9000e129412040381d006000e80720441c002c01a5a52984001c880c1840c01a450204181c100e510a12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 579049334 1250 579048084 579048091
    0xf030708060106140702030613060e010b030307140a05060f06031905060406150b07060e0c0303040510030906111b1005070e09250f02191703041b0b0a0e09 68
    0x4050800c1e40d0030140100c0d04524494040c600040d0100030500042e06c08004441c45003907070440e03c0b04585481e25060042c1d070701208000300182c1c1410704403500c9070f40100449400e01d9118580d412030009070b03080135082c1000458064003900861082024495603800164031425045041e10014400505009102c243c400070290095206000080003d040d5902c01d560143e080c9030450541581c0b0800d140013035004030412100d5589901e0410740d50703242040302c5458a0b0048010f0742c2040c0c100f202060200c07a40404080c03c264841c3d401e4802d0154035800904c0d1901100c040c1a174800d0445c0d4400c4040b8112100e444462059241382005c100d0203101d400d000e800c0f03503a075100e0f07a007001c5800c0280119024000101e140b9144180304081c00c0c050000c1c15981c005600c401820b0001000043e04028400311042000c3c44545c03014400644028407902c000722240c041c85440342c80b1400c08407c110700e44444030b102d00b400f007140420341d04040000f91404c0c400d00e9440d80d01d407648140c02c1c0b00740c0c0b0302d094 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 579050584 1250 579049334 579049349
    0xd020604032a06091b090b03061510050d02040909290f01050d03140703020a1e080f0a030207020a08010b030106050103091707050a0c1203080603010c200705130b0f0307 74
    0x80e490b682c0080c15036005884818095203411200c8290154410102030980d40704860b4a680c416170781c642c2d400c06000d00365014400010869088120300e002c0380011004501c410100440000c54281c4540705a061f18041e1030307030200c10405150b041c5009620394465040301200c00c61548011401e4a4001e0782091103010b00804006403646084140480e52210600031010310483c025a5010f5a10300f00c00f07466140c1c025401071081d0a210b040002800f03901106a164054140d42580701080c0c02c003049542482c6141035280c0c5c2c0ea036085804400a000e2102c00961044201e90002403024054208500600b41100200705041d40c440040d41110a000001010040942168080f0f6a541c1004c2c00c00540940c09492a289143d500d12080b0022038000d2080709405003504814154170481581d400700f0164000c0120400114000c0d18040c101e6200b29980c2008606c040e034600000e20015005280180600c0c04c00244c18035204050401c0080c0140180708500d401c80c0300b032900040b040111501c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 579051834 1250 579050584 579050657
    0xd2f0901090b090a050607080403060b060304050a08032509080f031c0f150e010f0504021c090201122c0c0114030621060601021213180e0d02060403 65
    0xb05409018240c100000113a40544039420004a50312882c0003046018031a01c1d160340e44030b0851808204a070600c113400cbd4040c0c1010700400c0006040003c01c0a95150000074143c1c070f0b990780b401c0c51602040f000c03843c20401c80a803503601c11003680008810f03049c3c030131441c01e840903045940380880d070b6405035070104130421141d40780d0240103881540c440c9000f00c150000c0460b10194509800e041c8031200e50110500c0c1c11988010400e283c002200c0d03802526048505600e4040c42c1f0410501919160001d00d25090782c4201e4103045a02586411800e01d651f81428006080740d50100c0c40c1122002e0040001040b607103220b0f860251001c1190004840140c40e442d9150a003130078800a83e40008005070b41007144100c03400380f5013108130780c801c650150001c002c000030324244000a00307141d040002106180010b000100c0203124403015281901c40f0f46898211030701058140c50050f03e09040790001c0c90050409004015a0101700c03544a24041d1311030501c3e004440504588042e004807110005010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 579053084 1250 579051834 579051839
    0x20d0503031e07050a120f1503110f010c021210050a020403030206010f0305070e09010e0a0b090d0315210b130302160602120d02130e060111030c06010504020c030d2f090109 76
    0x520407903411010941070007d110407500210380201c40040c00b01800202140104004100103840b000302021410ba40c4941c50b402e4820002c0c00c10b0608601c002c0c440c20031408400c2c20200204003071940628003400c103102504101282d10001e5005010130303801030090720000700e00826407600304c000302ca80c084018291103140908000316840080c040711502d5407901c035480080c150402441c10940e01446116040781052260545000c0e40f140e0a0407e00d0f05180e0701d003810710702e000f80420845400b000c610100360009040041c0045800100510100d040c03818010349904030983c03103090300e100b03401311441e562101e1042011140640f040b600103a02018007442035125100c00b4100b80e401c00340000d0704111000c40d50904186042d0410002c0b0301104003000555039100d10094400b0500d0307000342d450100c0e8a4102a2120414080d841c003450300000c81810300c900820031510348640c0c0b000100004006180140340705401d15410b00d00b909052000300c1d85071210013007281c46040d03058481e07809192 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 579054334 1250 579053084 579053087
    0x80c160b07020f031203010b0a0e0d030e041a060414040c051c1104030203030304060c0201051f0b0702010e090901020904050a05060f0d020118080a020307060f02060c03040609020d0503031e07050a 86
    0x20398403400c003505401017200f200c803801410000b860207004c541d40c9041e21404142d60041102c80314071032462260382c40300395100200707030003130100054502d095401151294030041c4284401006142c01c60308034400213000130313581c1024042c104d1061011a8148850488007404551500038104a0707035001800000303080300b5a20075403081000201c00c1c003200f410107540707400290440d04110b07000d960494a8200c1c1182c0750b5820b10031a68031032039005440152014031081400d1010340307402060b801481c00500c52056a028910b00ca4201000524901c0741d07180c0000305d94042e4001041c042d0142d401d200200749000c019000b0b02c2e1198401803c0c168502d28140200070104078072640907810b210540824410421076000064090400100140071011070352050500d0801c95070301c5102002100340425502c0703540030500f290070006c42c85900c0d441c2d8035241400c2000b4000a00e0085d40024205000410850040040d51003180d0f484104440b902c1d4181501c06504c01c205c542030009842004809002e5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 579055584 1250 579054334 579054349
    0x705070b0a180210030e0601050303130b0c07080102040303020703031407020904030804020f130608120a08010b030406180c0303081b030606070f0b010e04140c06040b071e080c160b0702 81
    0x81120700b494006204039004141d1203400d10404800103620350505803144c401c10040380303005103800c3d0021460f1136142501c0507602000c60003180c044080004a581d00102c08000705400340124800841d540e03039503850081c0d60742d444d61004501180d82e070440d2070004000901078035410354000e8003150303055507141c0d02102e101500500c202e0b40001c00da58800f6103034403401441000302081610000e000f80c04c04100d24a881090070781503149400c108003a1440700d91000b4090f04484050f65001d8032500c641c41e200380030b492002030441c0211400c00f124402d00070501d030880e0890703000303403122100e075100e2507007208401088054103859070204002240e65824802e0043c02424020070b000362880e2010b569000351903000f03a109103c2d8500034002e0005101c0108140355140f20807200403d03a5584500c04540e1034000d41c032800c0c030322440100301c0009100f5401d080345000140d41c0986540c80b1407506e00112aa000780209180ca44a0740184014154070311041c2c00903503502e580040e00b0011154200140c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 579056834 1250 579055584 579055601
    0x8070e0705130828050330090309040b010f02070b0a110609100b090f1303121b020c04090809130b0d150b18040b0709081f050705070b0a 60
    0x4001041042c07101105071204000d000e000070001900342c01605001c09400603002d07070307071400e0790024140071540020000411540241c0410000284101d03030f80c9070103240c0e1aa40f0342c090031100144c1080001045003c0300800e0310b403208903003c10160842c440111121900d0364101000b585c0300c2d8805114079070800000d0702034240c0310302c1c10003024030a42e04842e04044003500c0301c09043d4403802c0c0c0c0b008088030074050322400d050103440c1e40c1c00c145007071360034415103c0029200209060400d80102e042c103100d404807083c040c00042090096118400c1d11500f080d201c000e5000050040785010354103481c040c00f8802080d1b030025035080c02d1507802d204104140800300403074011682d503442d1240d51901c034142480d141e80d006a0460f0304010941a0342010f84900802e002d101d41e0320750001d01c461103600e4901c580c1154010765010415074505105490403100c58109040743e224060320f42d03800303e1517842c000e91503e600500c240100d40380c1d201c066455005910008201e0442440050180078091f80702c40107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 579058084 1250 579056834 579056837
    0x130b0f0621030711060708040306051b030103120807091d130605090a0c0509040305070305030a060e0108030c15160f0219030c050d020a032a020307060819050108070e07 74
    0x40c0741ca115550700780102007841c0741800e50400300c3d001e41405881943c40e00000000c0c0d65040c41c00300c0c0f95403110514481d50000a01c100c0da41c0c0041421301c1240c0051004000b40030303079199640c0d40c5a082c41d0064220140208000400321000101911322446200b011114a40b602050602044d501250383e1030b00108034050300b00c10242e0b03030030214019001e21801126010041d003010f801c0c034185100c86c0b020070340040740240464020f0000080c0d00a00301c3c1ea5098040c6049038580d00c42001c00009400329074400d010100b01000045581d80b00170000701120340074402151402c00700600304001482c4125060442660745030200001e15006a5082c1c10000302032041c3c0c1d004100f800c1c14039081d03c41041d0142c0004103031000203020014100702c1080c010013280014416180c150f0b07002400301066034070f03d20168504140321404480c40001d00b00903158000d05544216440300030081281504940d840e1101d0300498000c4590301d40d5205440c140c4603500044c240c0d6034100403007410b0006d4040c00000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 579059334 1250 579058084 579058099
    0x60b1807030c17010e1602010b0108010e060f04051503100e19020102030f1c0c050705061801021c0c17010605040915210210090f030f0507170102070209130b0f06 71
    0x8002c8940b041040b40078094a030300172202401c0403c0c0503d8101200228142560b151241006040e070304840d01d0313411100e210440154583c0c0c2e1002055030308030504005c5420900342802d01000041c420041203c4510a4003110b1070015a20488400e40c2c25482513100d05030064004070748031140c0071100f040028010700440746400142d0784010a554052241c40203551405540d0000180540c01001c40c00f44003450b010342401c400c0d868071621000301800c8285170f02c000d201d40d100c2d00d0000f0340641e004024081d150b0300040002510700c00c007a050080c0ea401c000b9400244c1d844500c0d40c410140350507500d8640c2d9290906081000d000020802c180070503c10407020800080c0e03400066075401d00c411101d02c0b00140c0d0307800502c180024a003401005806000c01135200380078080c01d404c03010007140d420811455202081d41452414901c0542003d486007000c4148030380b80720015001001102e100351816441603032001106103070f03414401c0b0000e01c20a200c45c041507520169101c01500079000414030b8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 579060584 1250 579059334 579059357
    0xe01140405091e01060216090e1c090527060402040b0304030c020303130803090108010905060105090f0d02181603090f1401060b130f052403071218060b1807030c 71
    0x140c030f21070780076400b03c401a408001c0c00d03024005581d50400040800030740c240801d440c046862500c80d0307140c001c128289503480c0b0b9803a03035152149000c48002c0c0000303450b450324000ca802c0241e0f0040700801c05590745a440070b009c10303550f09151003201d044615010a160031611982d0741201d11742610032090340c0c0751209008404088909440f083c004054000086981c0d242800025054010590201518500d400d00b0014542d811108135a0710b100304481d00451420303a00e0002e10b000440701006500440341c2c048034144400c07210396050140f4000700b40e24030b07002c088400480540b200030030010100601c1032101d40004d8030040030a2008810000040707003090312110b500800b03070042d030701c102180318243c641000003000703401300c00300501403c0c1d80700c2d0713a104801d0760560040140c9860101e40400000009181c4500c1086402041f08410300c0c18490710203080f01419000b003800c0400c1ea4818545074021040d8a4840c00070f0106004813a03990f015591030000c15802007046010702d4050002c0c51003031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 579061834 1250 579060584 579060631
    0x14030d180b061c0203060a0501080d09030b060d08040315051f03050d030f1d01020a0e0a030804050d03050408030715060501050331060f050108060f01240e03010207050a030e0114040509 81
    0x10944039140c031f003900061541c900241c552806001d04990418000c4840d0b0500c00310b0f10310b2800c0c0354000d0b01981ea80341c070444146003001c1c0d54404e40d400a0702c4103859846045081d2219001903004001c02c0326504e03c041c6402120034800c4001c2e11008007a50b1040d540307502018007903040000c0c044120200003400350350000000c1c8102c145403413500c8269500090034036200350001141040107005850948601b8111743c7c51443ea8440c501030640b003114440150020035200e003040b03901030892a410340352074243c0c601c1c01104420004a803814924100384002c40c0551080301074a01c01c0c2411030f070320281c5103941a9a08003c986a5490104041d0035480d000c0c0421024015500301c1e0f00c01c55000030711907240104c45820404060003050041c42c1c01c500401041d003524a01511080c9130040c403083c95840f43d8401c0c1c0340d618015240030380550010500c0410304c24089248055a4042c0e00e828500f040c0d007100444103417001051210a13404180000e000a06080c2076869000281103040b40b028080c4928 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 579063084 1250 579061834 579061843
    0x15040506210d031a130203041415010e0a02090603160e0d14120415050c070e0c0a0207050109060f110102070804271a01080601020a14030d180b061c0203 67
    0x1060201c82d804400840356040c0d0600c5601c010024104e000410b2400000001d120074801c02504800b581e004000b1406014514007e01804041441283c6940d8042980b40d03080c02c400f48204044444c1c10400250107040500882c1c05001004245520b10b035a04113a1840061031001071400300203000300c030f415444d00c650840c04140c9014902c224040d4101c1c01c00d1a280c6070341d601d03094000d50003d0200b0000c02c50203804042d40c40c90b0701d00f45141c6640851002c1c81c5403203040c1d44104100c5000304140160816410003c0c0401031441d03017078070000703511440103403030181c2e0a11410700040c5901c03280c02d00310380c45000c0c400310081c1900300242c5002c8540c0c613011819040380d003002c00004079030441c0c1e0710003c9403031070701c0c2003100c1e07501d8020b000c86003207803500408002454400760f05111800e80002c01c50b81c4244028030406500a0381403400080f4500d5150b5680c110314402d5000500e00031106a503290b4413081c42d03a18075030020725103000d5500d102c00c0c80942d652000c0d00140307241c9038014010050b5401d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 579064334 1250 579063084 579063139
    0xb071406070201021309060b0f0304080c01060303200d0503360c1c110d0302010e1501050a081606030c020f0708010218091314030d020711030d020615040506 69
    0x14005038031500341110f414070b00080746d40035114280c85c0c184101300c6d070984d0f1015142c03c902c0c4100001d8482c3c0c0c0d80d040c091890b12406060441c154a0000044101600040b000341c4c041e6451141c94240c0b0f00c4028400e41c0c90a0400000003c40c80c02d1000401440c5011041908000d89202441c04050005045c804010100d03d45040c90340010604000c142410711100d0064208209036083c0d102c0240c45406082c0407440303505000d801c00074440c00a05000350041f40140c005001210b40c1205c807921036000314074003801043d00ca8541d5010004403000001078040001c660f06d85e1804d5440d10f0501d0a0340100304500401c003c0d402200ca80081a00c400d100d5813008200f220000341e9508172444454841549005549109100000074071140c00c0c2445082d503403155102400244036800018140c0c55401203181d00c10031140000760710400c00c507003409000c0c0040310680840c0c00c1034007114000c2c0e072a588101c4100c00307011181c81107400603142a070001c6400c48006406103441160700a101c000362000391 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 579065584 1250 579064334 579064337
    0x109051f080607030516080637030b0901020c3003040303020c07051f0e2b02090703050f150a0b0c010213050f01090905060418121202030601090b07140607 68
    0x8810040c40c07580601649600c00d10b506d4212054418901c0d0191491070301814050045042ca42e6040035680068072801c0941c00d40c00c100243c945210030403210400c05800b0803181d90305003c0104036568814000d40d081c4c0842c51001d004001003554009584400c6081c2c00c201846a80c06101e6445c41800c0043d8002c034040daa001d6a204800e092082c54400f25510643c00f48004003007090401c0301580030981840300910309401d0008241c13000955560110607001d40340100d24910100d2000388841e00310b40c0038401c2da81c10140713a46c0c44001b038084580c11500515a8080c040000c0c040041c00041c00c81008002440e005409444a070300d450035401c00b4600340d10507035002483e460300c5030b01c040c2d40000074203084810104080d0044002031001a0503c900003130503486801003400c69440b034015450803d1039292030b03070b080c2ca03e07414010802600300140c0000703e00792003550286520140201c2e44101410b0715181001850b251548001d50712504060b228070344c00341406074014400748026400b07800305 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 579066834 1250 579065584 579065593
    0x140d05130302210412050708010501080309090108070e0f070306081506010e09190b06070f06020703120221090c03070801061403060f01210c06030c0801050603040b0109051f08 77
    0x2854060300d011140410b10b1484240d00b0441883c249081c03085038207641618407400084619480c1043c984211900042101d500f4403001013102c80e000405405a480100e4080000e666500710325030b20f88080380611a03000d40030700d000400960f412245207030007400318074000803003607521007a482c10300321031000c0201c0c104000300c28040b0941e4042288a10200e0443d400c1516081c030f4001b43c90090503030003c3c440c110340c0300c81b10100c0a40d0b82405403401c05400c000c5038003402059180c144001d6205500890119580030b0055072011491310035900b03080900041489259403800e524508a0401010300003c0c2c815116600d0650b101401040003d05c0000c002103556428400503402c20403600342103d000c0d90000d01008807142002203418116062100e04100c0c80309000c0340400031191888020341118076a44001862540c16407000c3c0d241d04041c2c3d103401c40c4d81d88038800c20006100c140d40143c0a080c0c2103005200782d41385a405550440b03403800781d5010070804a0840050b1281560209005400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 579068084 1250 579066834 579066871
    0x3120307090e091506120a0203030408030c0d0c0519020607020409141c05030f0705041d100b070b0403030c120f05040210230d0906020c01051e0702030703140d05 71
    0x400038455801c80040c402a120042c80103c1061009000905c07443c401c804150030b1504500c0d041c00010b000c1600503050700c0d40c171611070381e640f80d813540b2042c0800382e14814503d100400920607174104800c613a006e40905211114a40b445003a0065100700341d82c400c104014200c0144e17202c1c8103ca50207442410700794240503a000040381030402020109042490350f080c1100c1c480e42c0401100d80c00601c00703402140c0c5840c0c88400312440e00880e0800e0881c5144003182a00341041090903511a814441006c4086501d5200c9072209021b035080040070343d10302002081c0040c0c081d03004058240b21b40c0c9081000801416140c0058404102040b40100d0791002070100f1b42c01c107000d8603180114a130420792150041e4030381c00440d0040c01d0003221000381010928444a020b0f0350802807020341c11030300654503220030a0342c050090a0656480030b500000040d65503605000c1d80c6510b01c24140d80d005103080c16880e403400d40341900c9000344620755007810842015609018800c40e400b41a200300388901c00380 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 579069334 1250 579068084 579068099
    0x60c030403170702010915150e0c0d1404050c03190b070e030d0f080a05010e070809330615040b0a0201021b0601050a0f0f09090f050d0e04060b0f0403030e0312030709 73
    0x4403250551f200c0740c1c0c00c01450384018001441a40c080f00d005410001065507184d000c080d540c042c10103079449140c101410b81001e660b007501c40380d0142e0f000b0000c3e543d4540400c0101540c038104205031400c0c964140b81007101288010304e180398854140d0421900641e100800a410002071081540101300e0942905500c1640401c01d190310040800b020451941400800d1a42250080108080100301c1c0700051381004148113070790707003c8110501e50780d01400006110000c81c1c1c000e4041f040703501c003050028800380b40405404100c0400300031613070315080c01d20f1100c00741a4040c240040c29503408203e50404484590205400c0c4d9086030302a1007254144001c110940c000c0f640500450410b80c0001d207c1d544245a500b001c0f9481c3c5000000c2c0012540740c08140c90301c0d044406003103800381540074111160401c1c0d4103803490340101d41c1040f43c1c544440c0b13118494000c1c40040141083e0901c0140f002078000d03d1100e101032402001c231085c004c05443e00401ca40e104442c480e0011742049000c10050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 579070584 1250 579069334 579069353
    0x1101111f1b032a14031302010e06030f010e06030a240c022e090812060907110a120216180c0309050a170c01020a0206061f02060c0304031707020109 65
    0x390100e203000e104040c1e882c481514411604140c40c9403c0075034107410a815401108040c116408a001c01a2686401044000c80c0c00301100c0030ba020903602c5240050918101c000c07640f00d1480a012070f082c4d079080c40600081c5400040005070035100d1001140045410244503050f08012108664461143c00e00000281c03841010f80c0030a5500c44092560414200101001140d441001c01140c84408450540182c801100702800303c03c0d000905609241008950710310901090f1029511a00c4046045900c2d0004140010803074104035807005c00074101c000080030f004041c2c8100c852600b075084603810384043d254440c110070720003841e00e40b1034000304d800340040b1000780782810885081143c64980e02e41404078801452a50307944466400c0d081a441503501c1d5151980085460b400440c00183d611f500030340e8040c0c41240b070002c0c1340381d00007000e080454541c20705a014145584521561000640010704200d003404140740790f000c40a00d030a00400c2c030442c100c4c3d00100788071155080c0800f00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 579071834 1250 579070584 579070631
    0xe06010f1205060a0209010909020f0d0507180b0702030f060f0f100b040b0a140309030a110a03020c0603130506190f27020a0e0c04050a0b071101111f 66
    0x1a0440c00721000085180820a41e901c001100005603460310003000403a00c3c01c105d038103c601d0781c4e44082001c440411020020301002049030800b00034135115a4029a404080e5649a12280c1070425061290801900140500501c041c04803096102a98021420004202d808804050340c0b03100b000002122405055003055a42c502c5000380c0d401d1202a522510450142c03070412040010004400d500c20881100080007500c4c03015240e040c07040710182c5961014640c10000780301905505000100481d201c0d11040c0e2640040c414002d05405001c002d401c001c10035442101d00181c0c1c3c8002c078100f40400c5110752200400300711031881500601c802c4403020365a00c41c103113190400040d07980f010800c01461030000d607000b805800c0a14030009801c0b80c1c1a410407100c0c0c4403c4028401340a086074050700035540c0480d400c03070304c50b5202d01c1000810b00a0400203010405210303039001041d4080c02c81c45541c04114002d43e80c24604010f00c400340c440c10b04d001c0b003100da940e030000100d2a040030240c1051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 579073084 1250 579071834 579071849
    0x3060b03060117070303080903120405010506030111041805060a03050a06020304301103040305070b0901141603080a0f050f070f141c1506050705070603050402011d0103060503010e06010f 82
    0x180f0381d2422007559503a04d41c0340030080520203448003064107000c040080d42d02045450205858030315141c9031041c040c110030340392a8080d42c20180640061030201054605031134500c1d1500c0c00003050201d21002801c005003180d50030000d0400d010002c510300340031082e6110f014650169807030503d4a86407003d070301094000703003070030f81000c04c01e1107070404d508980f02d0940c10030314003c4040d0600c0007050381035124582c40182944170b98100000d2440c2070300e002d09001e10090b29026480b00301e289400e442031050032180b80c200e210f4118076a0000e4040c402a64000035891400a07010703542c0354040d001ca86d0709903001a018180302c0c04100200d83e01c031803000e280814900d846c4600c444444c81d079080038060b06a00010020004c901c9102c42c0035180e00031490381c02c50442d1440403681e03544014100c2c0e48000e00c01c3e1550b0181e03007070200b2264064040c00703009950680d6038000075203c2015583c0508070403255a0f041603245c0e100010960380034001d040c1d449410101400003945041d802c00c14104240e40800e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 579074334 1250 579073084 579073109
    0x408070e0a0605030604111318120c05100f0f0507020a0209010b1603140712050a020f120406030b15030a060819080a1d100302041e360603060b030601 66
    0x41d200071600b590040e6100411040941c010310008040c80308150b10400018900b00c05070038401c64114045027854090071310b1700d440d120801000c43e240076600310098059813050090261107406503026440b80301e60180300146c4180000305400944c1c00c151515030050b40050080d000354608044a2401401c0c402c010718a0091188041101c64a07801c070041e0a0282000030a401c1540b80c5007243c9126902581c100c2c0303e00c0c00b501014096410403807442c4014030500c3c030200714400000030400d10102c4d00c44201820719140c00021000342045404594201c0c60109204c403030243c118010707500840f55148080307021414000300c140b5140038401400280d4516450240c0400c05503801c48203070201d00c1c688a04400c03803406d100020b06800c00001da4102d10342d00000618260305074040c005507200d14508015182d070507120182d81903c640070380f0b128021200f0a2159140c200030154000304940c1c2d0504404500780782251040300d1260740140c03249078407081e8284461400b0300920340502003580808 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 579075584 1250 579074334 579074339
    0x1080d0201140a111905120a02041a0a051317151308031b0301031104050f0405122203150b10050301050402030a0603020d050a03030b0d08031f0305030408070e0a06 72
    0x107141000381c1078003142c075a55040e40c22100c1000044911000014400c800c5240900c6001041b40d4440d8410031040308040000c14002d160714000c640803100f50704802400383c40240c002c08510390100c900d00c420311804002081030303161b810007050000d00c0b102c099803442201c1100414104054080c4020000341d2070410407500c1c00842d020b04d502e8541120760f4984984e101d185501c822810340b4003844021101000000c00c02036680e40d02c030b01c0304605680a00294560000401c00c40c8019203004105401c40044050012030a0024011400e0038903042e0290050114500032190f20980080e110582803891030103210009000308040031034243d540401192003800005d146000c1030042034402c680010200d02c44407942d401900c00b942e0010318180b0022250f1a05951b41e0303d07103030011800b0901f4010515413034600304490003441e6030000740b4a480d55690254520301820010b140300078090a4043c0031020440c100042c10190006070700401d4402d00b00840c401901600510680c2060f0412109 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 579076834 1250 579075584 579075611
    0x6090c0403030518011419090f081c0210140405070e0601050307051305180604050106091a07230d03051003020d141015050a12050703021908100501080d0201 69
    0x100c442d44e0190446000360148400f004881e071030f81038400121050808a4080d51390910308000700c01040f0140c0340c2085003540d50f00102d0502040d4480c9901035000034080c065600c4810b12050f01700c030b8a0344140c4204c071103200038060481c0c0340342090390020030b0f980042000300801081000050180d900214605141c802d000901a100080c140800c214010400e0280c00d100058070320081c0000810740848591483c904e4000050304031001481141458000120240035201c40f40658960038414004091b042000701c1c5668010803080322008001e44214560740c45250a102141f180c0d48080c0c501080312400040a0790000381c410072031900420410001a510b07240030710102544250303c800064440c1c0011800c0214440c0b4a155036410090724440c218035102c0d401c815148100c0c1c9180c1026180d2030403e4441740d140000800d183d2141c00309101500d041101d4210345450712003200c0040b91208941824612174807651840715481b10014007161400b07028182144d1103d200030440030381814003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 579078084 1250 579076834 579076837
    0x1030f0e060601120e03030f06041a010807141e0307080109140105100e13020c19020618130c120615020604031b0c08060103050c061809250806090c04030305 69
    0x240c24144980070210307100c1318102d60040640b651044c01585d8403071034003269400f120582155502e01c110300c1c0400340c0100700d00d400790020403c0c0c3c0c1a59190016611100d0540e6641c0e84480c9035503100c10300b44001c400c03100c0f40f841d4400c099050111a10b0300d80c10291800341c10644180c1100c08407500f06505408031508803407806044400031688071901f80c1f0700c05010740d0130344100f0b03e1140c0c014403401c1c3c030718204004980007030142060046c1101c1c04403098442c5000528641200258011400c00007003014100302160807030112401400711400080c241d80800c00c8030920007102000c5000b961115040044612030031005080e43c8400441f0300000d8800251a4040200002c040c00b020481c0e070034014601c41d140325607043e03000283d00c40b6203844002440e40e5083c06d11084401384a0300000720198240701080d038004000701c40724601011210000c1002a100003021019052400000e075100300740030070411009a031090b16600b0721810104c05100407e01c3c0107003141d005103010081080001d50010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 579079334 1250 579078084 579078091
    0x204170a05031927030302071a0403020f0402090a062303040201020c1e13050f01120c06080a09020d0f06050f13020d020a051008010807091a01030f0e07120201030f0e06 74
    0x2424081100f445202c203540c40816030307250754105080d043c10180d000d01401c1040d000d9a00940031151041d03540d01908021760085000c030801520240001c20050030316100380c480207800140050b081040c2e0700c0100d03800c281c85901400c0006d8840110702c0f008401010002c021507a55100d4030301c3d620f400d80010756104440c044a900414041e007016034405505041d645852400400071080c034816004464081d180a4940d6002041d10200010b441644100380c0401c081c0c0c8662000422481c01805480d20780e002018011010740f070b071901c42e0050355420782e003454a500c02d50001076100b02c641441030031500c3c018450b10510007854240241504030700c1048250300d60480e045040e0100d18804568a1082a403245811040428141743c2e0281c00c88a242e05990b0704030100c0b1140b6070341d201d40c482500d03241e0240858000080c0704205165202c0d400590004501d19170129201942c22145440c12840b548501010844502e08000b19a454020010a0f030000c0d04203109140ea200d00e0143c0314807001d0f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 579080584 1250 579079334 579079357
    0xf030c080403050f090a051e19060207060c05100f090b15130c0309080a0c020102190b04151e0b0a05010513060c02030f01141608070f0e060d0204090204170a0503 71
    0x4905445c0595941d40303603c000d0030000d005d0690f10079006405000701d6580348243d6108124104805c80c0c9600c0d402c405c2c00845990394001e04c4200c4c0b030441c040d1814504c00c42d041c1c640d8080c88105294040d0701e80100c00600170000c000098095803810040350303601000e0700345440101e44220001840e0703200715806507004600c40c2c0008084c03a2443c02a0010005140b0041030444042000d00d0320742e81014403101698005c0e000c0d601c01d500c451035411001c0ca0419002800300240f900481e01047d18002045038002201d10002342d080d20300c0050080c500c850460804e60b20b5201c909007101e0741480d4950000510080c00c1940c14080070f61204079000c031407406000c0030480380030000015580d040020070810220071b002002651850200d050b05404121034601c19009101801100300b4829a0410702c1240190355503c41144044021204204d25030b07061603000342c050190308807103406480104002d021075407006903100d00e01100380c6203014120100000581140503ca004603002004a40c3c080208 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 579081834 1250 579080584 579080587
    0x203070e0415031709120f030d090303141f08010e1002090307030b01090204060f050a080601080709050301020c01050a0e0106300602040611010e01020c070b130305030a0f030c080403050f 82
    0xa0440c4500a40b0a9070024102d415800c4802c00911496001485003110949086000e495191400c59503070100515180142d441009006000851039000021182c840c4c500480e0400200780103e43c4048144d9408014001d1201102440c444640e044402008004000d1107017507042c1e001e00307032210030042d81e505903d9000100c02c1800d5030248501c0001e55804500c902c0c4558603040d50724000d4000d40580d0340400c3c03101707841e410024040c0d070640c1c50f040e039079070341e903030045da80301d600441e03144002428407800d000e403d0713001190595081c0094210112413900014142c81e20344030000603140c0740b0038450300d143d15022080c4000c8480d409004010892a0200d1049071544401000b8080303160001504880c808a40811120792018181e100b1000604c000d00020680700b200c14201c1c03243d4000f410240d801840201300c03000401c0042c00b00d41d540e00390340d003102d10740d0380c0c0b1880d040d40d0000d440b00d0b0005040c04035001c1c03659094802e40010305864138007070317195103042d41d40038101b84180c10340c89801d01d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 579083084 1250 579081834 579081851
    0x6090a02010309060f090302030703020f01110304240509151f17070f06030b190f090b030c0a0f0617100501050315030a12031815050415090507090e010203070e04 71
    0x745504074954170001010100588445420020740326041303800214014083d0b880705124264050182d00301c0315041c11420340c03440d1560390307a030200c03221a1100c00c03000346801c42c031a240c1c242444c407402d071180308040c000c0c0c1103280b91078040c0b011f5410014240445161100c81d0140030560300144142a210308019183c44404030100b01883d210381a44140e01c4600340403808030307449601d0717042000040402d6880d0702180540d80850200468140611001010384a4040002001c0b54100818030540a015996101450408a1500b28050b0000d80c001d107200001001026032000320203100700c01d903002c4003840d800c110f0540010b6440600c2120304202c804001308100d00b82d010842c1c80c0c2668001c0807200000d4051414000c0388414010030004a03140500503400034020480c038261503540b001d075071161165100700000091030b01038070507a148a055401da841041482c4505c00c3c03150300520040c03030350528000c03841c400c0e0f458044a083c035070f0740141306114403150440d52000c0c0c0341d03d084502181420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 579084334 1250 579083084 579083093
    0x21f0530070804052803090905130312060320010801060813060504151b0206071803020402070f081c050c04290c012c060403052b0e0309010e0306090a02010309 70
    0x304c1da9070100312050701d940c20604070701e41030410802c44031b0321a03103401c0c1d0141d41d900d003030700c080703072400c170f405500395400440c0726000203105078100b000b440f142100004407282c481e00c800548071810000404040d108840c0a001580c104008034010030361468041c042d80342000c81c0f201c15007100301c00208280c4d1a6004602040702004030b01c1c003402c11802d002c12031000c0c48030046281402c0c640d070030310150080402044607141b15911400f400d01c00b000c0e22401d882e02d990f003400002e60181e60207440d00c2d40500202000106600014401c42d1400d01d0512051030031300703188030116400588141100c0104004c10000c54084c003080c5280b801040f0401e0103000c0c5825404401e912507091480340c59403078144012220342000401080040d00c15401640d00c00000740c080303950b581c0546014000c55401e1200f0010380104a000007440c8402c04904c540c0000c29a1485050b200d003115103036011380000c0b85602017940c0c003800e13026250204034020043c40c28400c000302d8a40282880103410103880d2880102440b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 579085584 1250 579084334 579084343
    0x2190b1e04180b041406240f0c060411010512040221030c0106180c091502120a03051806040c060f021903170c0301080705040207021f053007080405 65
    0x40c10600342e00c040410341c08003020b0080c840c403c4903521503032400c89400000621080d40600c80c40011300384d00340042d40a42c0c0180441803440c10f20004030300401c002c10b44184900060a418007401008080c0c03402c00b0300d804000c2480003100a81004002d00410351003024424401d6049501940d110a003a00e451403049200d0f440300b01420725600c030014151210100562082044032903e60035002120708a80f0300c0c105882d40c41255034001a420141807010103141440000700d0000da0040b18035550540c2c0ca07005443d000302058501083d96841044900354884406401d00194280900b016203441d9640e9080c2c0a0306001d21010088840180305000c0c0c001c101c1e5142d044032006000d6040b010524004000d200c11070f0494498960440104040f038042c441980e06841d40b910140c0001380c1003005000081d003140340240c2c1d0100035042904a1744144400c0c00800c0d07110307669051707520307280f00e1582700742c21182c0c0340f0701a0765404852089400340300e10b142150b045081032409a06945032420482c1ca032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 579086834 1250 579085584 579085589
    0x31c1802060f070b090c040e1203010501260f060901050105090a060e011b05010603110d0c030803280f060f05010507021e06030a020913060303050307080711030d0902190b1e04 77
    0x5030290014040b03600400190700c0102c281c01c94040c042a40c80352305983c1c6402490622108140c030510040c0150742c007c1d00c20003001044c0045500e00405120f102e03005039030b42a00c3c3da200c820b2030300090050340c0c1840c41c0350354007520081c00d005180c400d9450200700303c9550340c880c0340c1c204003001101520700d038450201c4401100701c421800824002e00d0030704900a00640c40708a680701c1d6203d5001302d031810400600202ea5410071414080c83d80307151114450b5034001081c0b9121440f00c1444000200c542141e10800510381100015000c290110380d901216001e410081c0c203070a8500e01041507030307800340440e21666810389001340414103011220700040c003550002a440440401000040880e660107060741080459518015a0001d0b41900c11100d031808081c00044013040010800c40c0200340d03035604030350645800e1151441c0864140d0440c0c1151881e1101107031907242c544103516105911200051b000d81e03141d880b082c03410034908000e10036041142d2402c2c485404002c0840c01d0842131f10700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 579088084 1250 579086834 579086843
    0x110c030f13290f210610030218012d21020405010512071701081005010b0c0604170c06040303020408210d0902041805031c1802060f07 59
    0x1150129400e0411a40e040303404a100d5060100301c0024a40d01e00b4014820044100054011002414000a44140e03c003000d8404818070030484100050000b002094110034480d055824500b80365082021036a43e203000c0000300b50041c014801082c2c1c1e10208a2150703034007402c0802c07100440c82c1d200c0e66100c51560844140b010031814541059401c0001e00c060281c6480c00294545001c0325603200724041c6009043c0002d405200049001440111007a0440340d2420400c0c0f030700b00d0b02102e0003100c5101340c02c01c080c282c20040c100b002c41000c50007264007400d41016840d080c0380c001001903544540092014040120002c20620468600b004807441003c188050710b01074505424040c01035445407203202854420090801c81c407810b49100d213005150b40c03000c2c162030600b420854030b000c0e048400b401c0e80c5c800d56401030160039081012001c1d00c00b900c100c000d980c90f006003414402901c0c4e2541c0640521900f0811000e42e40e0b51420803407092268102c3e280c9440340c4440c6070040090090b404005e2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 579089334 1250 579088084 579088087
    0x160909020a021608010e03120a02090301050406060512011b0819060e16020d0c03030e010b0d0f031701030507051e2d040605010c0f03141617070510110c03 68
    0x1010366030103d07450729081e0b10031030b441d41040d0b81c8003001404c807014203441c01d14a070000e100c0c00c400307011750681458008888140250900000300000780c2190340c00e8404948a41d030302c44040020307080c09041d8500c9401c5c0f100082240241c0d00c41801e0038008200800c0f020400d40d0780c0003c2c00004404034042c00400b000d1801c200d82e80e100c98000e044100300340c1c0c400240151200072410340d20701c00506004604030329502c1050740f210030f98003680a00041e00c0c0e0700c41d940d520307510000d800e500e070250003401e094050031420b01e000a103820064001508078000500048030300c0014804100d000404000f106d80940329007150251510b021034600703100344400d6501464000310403004480303c101200415450307240d1101c90b1090b60b800c000c1221b1082c4100390200f0b1a94500780c010400c1e00303a403003079464003c3c00d00441c20088104e0316501c40e030240ca0380c010007200546484085c001c049005c0d5441081043d0b54174505521621030300c0d9180c00c0d054980e501951107501402d4448400d800391140d0b0380c1204203da = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 579090584 1250 579089334 579089347
    0x60409050a050a02030709230405031b06190e030f0c190f1b0f03020112180308150f13090c030b090102071707230a170406020d0206060916090902 64
    0x5880d425243e000340e20030300c5595004142c042e8580319030101c40941045541110120406200700b4030320091041c0c1c2d541c00140310550b1462200c80c81ca54540a0540c080c1020b85000703880304152803500c608414049107014a45031104a00008980d0764003928503010b62500115211076251056140184407100041c070200410821058001d2034500d20513841c54002682c507080d40001c2417400c1c03040300007980400b402040554056a071400c4244003911002c0361941045125030250448900b0880005140030100b022100c900954062450400c50fa4030110f00e02c1c00c400190080c0c4202241d20504c0d51703420f0320008100da0300c003c0710700840e8000f680102920b04803c406000b50050041aa10200150400302c40e04004030225410668420100000e000707004915a003006019151311109100304c00921011801449042e189154175160156440741003d1009042c4000e00641c44d0035503100388244122940d420394250381c0002030301800c07096621408421160110030b0f920083e0a140f000031b50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 579091834 1250 579090584 579090593
    0x18110f04060e040b0f06070f170702130509060a0b120f160e0903220f03080405010e0402031b0904021606060918050d0e0d1a01050f0a050a0e060409050a 67
    0x50030440360300741c07a0168240010000d00c410b0716818805143d0000460310900360a25002c006000c6241c0100b42699041d0401d40d5030032803000280710400340c0c400c000f0409004600d05207400d04a0031604032024000d5041c0f51905650b0303100045e001180c0562200d200c00360a468900b10300207500105000c8400400302e9400b1140c0359800744a140c200d4071031007407000c240340c1001f92000e03002d4810303000210320705000c2e092400ca0014007041185250040848001036100009882e80040d40c000ea80c0c180e42c803441d10001502c400ca22064aa000728018010010501080c10341e613504a034004d01042d80c0d4540c0c02002400074402c040720581c600c0642c082000900101d83c0c0050240e508048041001d010700d039a40c0c6410300c3d00c040008003240e1040f2014404075105e808058004900900b010800511580c0c80d006809005011000c00c0318000300100094503280321000d086003000c0c0e17441c0001c542088003280003040c813400780e00301a2801402092664a460b409480d40d9500602500c009902a280 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 579093084 1250 579091834 579091837
    0x305120a17190612031403060a05031b10210b0f0a0f0f050102210c0111030403050315010509030c06070f0209160f051204061d06090d08010803070201020718110f 71
    0x120000c0c91850450080f13484455182505640760301a110490052400d00c480840d070303800201081d030011041c0c8400107440c0c0f810810002401604480814880320700d9003803141e413500b51251801080004107414100c503035602e0360604010312003003010605909030300101e0001e01e0707500243ea8118000c12000507800942d01c95880640d10580700d0301c0052584d400c012690313610fa08080a81800022803103600b42130040008247c600201d0b400403804890042e81c1c1e007650b030070407903007500851070001c108203e2140d40c1e202c8031601c81090074454200084c44005c01e545003500f1072130f0360040b10005208002c0c03024100180380c003954014800000b81c0b51a00508401204245600010a80c4600c600c2030045c00388064504006010090320441d55640e110480a088078640843c61446074100442d034441050090031b100720300d00d000504020101d114020f190a0050744102c42c960414810000142e9002c602c1030300301e5452107050030003c1e05a800310303401807500702915030320340b540014607640c3c54105070b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 579094334 1250 579093084 579093121
    0x51b0d0906090b0f0909090a050a03110609070b0405010f0e03010501091d150402060711150c160302060307030e03040f150801060c0b04080a05070c0905060306010f0305120a17 77
    0x190b5460710700c1d07942c5040c01000e018003521003100c40c00511140441c1e00303010f0b0005511108150450344211101d40f9080d0070050035100a60018803220f0940e05182820044960054004030042601500e031840c540c01c280120b000e003504008803c1c0c410491603100e24001a06041c0c018003c0009580d07511202000700240c2c0300702140520030f004485c43c0341070003244030b505143e040700c0a035886a1f00ca508101d45940140d000302c0d0642c0b05124008100d07194800010410031507090181d83d110b141c8954540f0b041068841c050003000500f60a000680311030049d25040151401c0109048000d91041d908500503a0001aa00b0946d80e00018161071074600003420a0041d4860507040c0e42c03034840c200c64501141c04040d04880d030100c00f240004a081004084010781454564100081076903140d00303521141c0c2c003402140ba103075020302006140602c250341c01040c4c0f000c0c859407018911350b01e082d103e0301c82204556200101140a9142501640882441248144100855187c40340d0422042d03110003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 579095584 1250 579094334 579094337
    0x9060e0f0c0406020a0609030504030b130605131112010605194104060b0c070801050a0513030f02160306050711010606091a2104060c050a0c03051b0d0906 68
    0x603011600c4000304108880543d14140c0c068041701c00d00c1d86580019140e50002202040020040040802e600403591030182c520685c1d0000a4552806d00400340e4101402811003840c6080b02040003500c81050407422000a40e1103400600c40c0f110028010400f40d0b0105401411164108141504e006012016a009403450311500c84c0300f502010300c15044481e480c90b010081c13070f4800c00c0440380612002c03203000b0001c00214401e0384a0344035820b5070304408050a5207521070441405010030038010f01d42e02800d03080d800c002c2c902e4040e0f002d040360140744101030b0034002c1500c040d1010a1003448885211012600c07042845680d07450701d0001004200d4102c4d0000710780001c2d00704207000c10f0298074120340c06070303a841902609201c1410072280d59140d01c0d034207040040200f5110b80c4603000c00185032070400c68000501d490326042c01c80940d0404481c88040280401c56510f0301d80d004454441101d4040c54955103507089000a840001407210711b6070306501c2501280700195038802410b1043e42c845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 579096834 1250 579095584 579095611
    0x619050604140124030510030305071b0609090e060411060703030e0a030e040b15270d08041802071a0c1201030506010513050c12060a0308121806150609010909060e 72
    0x2021406c03138038241d86070720300c02918120400100303201e00701801101c0e015442d0098412981e201c4131907522180e0380b01070301042c0144010841241d02e8070402d03200140c0c0c0c038041d04551403c0c0d51503d16100341032940520035040803c51100f454403c0c0e118500b1303419000e00300c6145d03602c41d0502074213818075100c280344500e061421040c1141800306058442d000c00d10080c40c10280326101c0c030b0700b12000c0c0281c0c0f030056aa1110b008629641d500b0804000a0f000e2082d090b52a420841080d04a203a40c072011080540100400000200f511054904100500304000e03d1511945440d1a881c41503420b44c080c008049400401844408a0754504131107040b64009a025000c03401074040e2002140c000c14a07003002c3c41000303a4144a003105640c8030740014010782c0e6507604ea64408950780c0024107100641e000003030803c901c8103050070800e0303001d0302d007a4000d020528060100c00d141d90b05803041c0c640242404102226240d000d0040030300038000d400b03024840c0b1a26031030f243d805605c0171503140700d45000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 579098084 1250 579096834 579096899
    0x80304260318090c0c101802130c03050606070c030602030c09060d050a0606031107110315010609140a0b1e040f1712070f080a0207180b1206190506041401 68
    0x500c10b04844407495042c0181410000c420003550003040e08509940710314400c03401c0000140ea942227031091024214000090203100484000d04403a80101424000d10081088501141291207210308a90340715002595035601c61201e0b14050041090b10350300881c001c0781020140c0c07a95008a4829a5150820845582d580c40f0440a9840c03100c80c0f151110020000040030903549002404003181c040c1c119010044000544400710b00241c1c403c00014605d00028030000116044003051050226000440c09052044c440c0c010f01c1080d040208030040000c1d282c04000c1064280c600410f071500c03070444140d545a40c0020b80c0d000c000350b280f1041c0144039224280c00703048000d0301c440a400c0044988004199a43c600c01a8820480070065101d00705001411281c0c00c50060542c15807542c010a1020307240060180b4030550644015a0342c03c11400c022162050055035280f4103034201c00840c9a8039040042801010019881040020200008948031207107415408201d442c09448008a10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 579099334 1250 579098084 579098101
    0x1a220e0105010612020711030f030406020f0606010906030b130c050a0909060b12070c020a03060902030d030606023a0215090c0906010804030e040510080f030408030426031809 77
    0x4200b40a4880401c41512052280c00003550140100c02d07c681c181c800320f0043c10780024500130441c0144005a400050203000c2d441e030501c901a02401c200d0010305043c100900060180461402044109a41c07079400700120740ea00b220314032502c0c1c625071082006c1c008413903008100342d103c4543c00021510300040021040c0300e0780304100c01c030f0707104141031410107607000c00c40000814050a005c1c200301104880c01c0140e56403040c10350003140300f5500098101e18a01c1450b00784041400d41000740f61400004000c41178008c202d28418811850021300e800c01c410750070100c002c0a05590141c14440a84803454598002600744072059a00d54031607019558141ca05544894803840283c0018001c000300300554041e410300340c0c006101c1e00b803100171080208041421100c00311160500350040040402541806102d49200c5098150103549440e0400c001701d030741c038800d600c1501d5841075240801589001c003401c070f160103d0b07031380410b90740d9945148903008080403440290a20a03190741020401c1c1d103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 579100584 1250 579099334 579099341
    0x281205041502061e0603070308040b040306270204051008150609010b04120f060603050607020a060c03090b01051c050f0309150705190602041a0d0617060a1a220e01 72
    0xc0e500c0001411403188495000311001c000034148039054894140e0100000b08480c0280c8040d19403040099202c1e4514100f00d402cfd682003003410042a0400030316045146c8840100080264040ea0003241689412003210200002c40e4800851406402d42c00500a03c000016500950040b1144201039803100d00310f00701d6208510a042e03a0a00702180350000890300600c2c640b20f180290300c005021681ea8452504041044481a00507000b000c0420204551807203035440c00145407401304444401c03580e842c45c4460043c0141441030311000710740004619864510000282c1c46016a070250244a271125980e81000551500c2903101c515011034403d0b04600b902c0000f034014000b0110050582074414500360501c1080e540c0c3c07a000c000c0429996103a050280440c8000a030056403940644d4034103080359440d41090581003c071141d050080400001c525801000f2120001201443c45802d60300000b0380141003600410424500b100585000500e42c4000c000d040e800c0c00704084500301a800c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 579101834 1250 579100584 579100591
    0xd0f06090507020f0a060f0b0d0b04170306150f09040e1b180f090a0606080c0a0806070503040326040b0a05071e051c05040b0612010902010228120504150206 69
    0x3941d108000980c01b00d0401d070404043c25642d0360303001580c8980840850343c180070b01e01e005d84004035640140001c00c50080a50111103010304000c0c4d0450804a0006008048481c1c0a00f5644400f1130401078245901c000c40707018100c010030805c258445010300c0d41e04d40c0e002800b456101011603038000c11900b881c100c11036050200307d030700c1c540c03e50749d1045400303040c10041e12508080c4102c00715540019002e00c9544064070307000d8018180784500c0401c029003074003240c004480ca9007142091000380c40e0040d082c3c84e04150b060a040744040f00340c00c13171440349842000303d1140c10410301e01031005001c0c44060103402031805030021b10040c1d440708002c0d40e00f4003a070851442e01e8009107509541d214450405001e20b40d041c948080c0c850b00d006e82c48001669410341e800c1c2c502c1c0d02d0046c00e0110a2a00d41800c503007401101001780004c01c51a00080d4a40e405d411142014480c41141c110406288049032841c0b0790748451040c17560080000c004205410502403800c17030080da2090440d0040c0000703a042e10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 579103084 1250 579101834 579101863
    0x13151e080606100f0c0c0b031602010207020904061112010f090f0905070611010e12090a05030a0f031409091314151f0b04150807030b060315060d0f0609050702 70
    0x3c607907103680d200b01c48084034200020704000684881200055004c1e001200074007461030342a440382000d0007102064040b01c1d103890296031041000800603110010a40c0c0d1150300100009031074034680d84820680e1280f401c1d942e0300d0504550001c0303036001d190401c00f026140e030108204854152940d00d401102c0105c480078040e0742c40407808015085c854030366040c000c0e40070000481ca0070000d564281c600111003920308205800030550700c003181040c2003007400905c0210001c240003402500c0e514040c42c01804060100b21001c1c1e680040c9003194412104451009001c100c0c1c3c5243c0408998001d0707002c900210362101407140344243c441c0c030001d13903083d1809018809d9943e50b21846a1014440f050010100c070852104000044000f0740002070401001901d8540300a45070040740104030b803c1c0100804141840c08005004030385a4000f500d9000815400d18041d9518940008545000d800c10302c4411030300340a09007074641c90325003200048441c5071078144000d4944c01d009030788550150740d8029 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 579104334 1250 579103084 579103099
    0x41209051819231b0a03020717180a1719020d0204060308040e070305010e15031005280b030303130f0c0e15100e13151e080606 56
    0x345148024107068112140c190b0036800d0141a8030320000769031140040ca0b214a00002c4842818151000801e80c0014141c0105402558448110304c0900808581d01c04065000c2090070401402858440503200050031090b1030301803191581c0541015114140d0040402e1280087d1802001042007203126441003c0c00c1420b8002000c04005013003940140e0340154407503140310241e100c612a210255001e104417a940710304110302200c5290024000384200b41c9040010000070000341300c019001100d0910b40030390401c0c020f00080c901281c804469001610302018000395134107600000260307820080a0a02d0310800d07403031000441c1e00e0940708036059001080090000008042800c0c2d460b84584084014000c20303481d06c0300c0e40440340d0000f103031040d010000d0040c400f903805501c0c400311400319407245110104035001060944488401801000402036001c0740401300d03002412660425503000103203541d90801401e100304002112512024644070115030010040b42c0b04c0d104100281011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 579105584 1250 579104334 579104359
    0x140703020f040e010e0117060108121c0516171308030405030706020a02030d06090902150c0c120d110607090b131203080f0702030405030a1403041d04120905 69
    0x94020354400c01010304200c00c100008100c03500b800007074138041d00e8032066441041d030400c000d4012040e24002004182c0e44180010490180c1c00551014070112041e041a1154502002212a490101413175078640703082800304a001c110410305443c003000c181d954107404103001800082540010340e40000c4103152103840c000451414070013590414821000c0702e142a41d035444401c01c98001d69000701c0183c2000441c0004001c0c2402110040d20060600700a1030842c2e80c0081d5400c103403404545c03510700000c580d0300c07103a08060044c400054409042045e0a254940d507043c1c448140d418034a02240c5400c50b119440300001403558450141c0382c5458403410300b4450110380b03940081581444002000c9804200d0f81503601040041c07a00c2501d54004500300461440c0002e000100503204561081c04100f050b5500015041480d0741c1040b4030904003121440140d003035200da50083c0f1650450180103122029410303540c5407049001d414402d42d0001c51b45000c81d5070340310074030440b5400150014032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 579106834 1250 579105584 579105587
    0x20c100911030312010f05120c04050712060305060a05090610031b0302040c030e070b0c0c040509150c0c150103020a14030a14070306060504050c0406081302130e010f1407 75
    0x5800198050380880030910703100da000a24680c0580142032100465000402031070342c1410341000a800102c4140030284581d00001d5a540a851030783c61040d0b0b2900d01149100d0b000d900c11240c00b10406205000507612070404940d034690507507800d2070381842e01c00044c003c8480803821310b000307141e241c600c0341c0b00a00c1c585a0a13031890b1005507002101074000f50000040c2d589204401c03044440f910081500304203114402d08180301503100e0540810304000d006214103001c14003001d503650498001a254440c45909481c01340b074001c80c0001e5884a0050110b0100b40201520b5041c50400c00c80d006408620114080c9603400e110080d04070914000038010070304041111030102d80c0290441d1440035994030381852000324003801c40d81da0f400413181407003845140c1c06844054202540e041c000c2d400c000010031140d100364400d001c2005400b401083c8016020001c4982042d0024284901781103101d05030780040c00c501480040b50361818400003000a150300901041c01c8403c0c024404a6465200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 579108084 1250 579106834 579106841
    0x405040f0305030405101b021605030303182406100c0201020d05071a100503121303110114130e090d08192007060501120b06061b060703050712020c10 66
    0x805c0f2000d01550500e808081c1c0c07580700301c0c0380317484240c0c040d40c0417021000c41c0681010410800307016007141924083c003032901c000086070b4218000c400c00c055940304606003c2e003407158049030480400c140c13041c00819030b511307a41000d0044000b100c1610f03040a40d8074094409030008640240503822090b10a4101401000505241406044000d003041c041c1020741404480449110040600d0100c041c0319908003040103c1ca00c8a440b04035515003480ca400040201000e480700030b0540f4540002c50f0900e0348030b0524400d00c10940760245031030703d00c1442c990301505d40d070b40609081030303000c0d10001d8041140080c1040000e20251504080f644032a01c4504126141803250801d03151242e1040705100408500700b00781602088000e0749444091402400b03869044e807108450b05a01444800450700984070140c01001c202c60140c3d94900303032420b4002140484c900001710740241e408003d15140c03d60491031084440750b4030361207403444100c5500300b24003400140c4401540000c1c001c4a2400d6141e2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 579109334 1250 579108084 579108091
    0x6050604020909040c0305011b0e060901030212100e0c03060d151104060908060709030c140d0f050a0311120d1d0304060906030e03042103120c020a110405040f030503 73
    0x380054940311111003c20101c040955045540140e07600040050002c20300c2044082a100c01c1d422900c420720100040000214607001407050400040c0d510281c0c1c040d90403154540035030543c00020b4501a01c0402060901d4494020500809400118070007645021a441002c00500c01e201000c11394562142e5503c1a100383d40606603280c60346110105030202500042a5036620002a03e06040440c0c1c1407803005440300f8103121601101703000054400c40c20340d05860a501e91f003800500084005041080c1030f600182001c1007000803c010b0004c082228103e5074002e49502c00c17980200800990345102c245441d980c1f4400910005c214414140c200f8040005035401d0b02c51080c00076005170307045034401c1c0e0000000c140784070750030071000790940182c002942c066005035003050700d420304c1d88588006402c112040300e0401c5d614401050f001c1c4281003d8001c101c0400c0004492400d0003075a1607240d5001603d01c8000c0301c5480c8401e00d0035005151107658459802c803075480c216902a1025000034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 579110584 1250 579109334 579109339
    0x917282a09050406060810090203010b0405060906090a02120408071b0302011211040801020f070308010b030402030a1112010c0518060309100513081602090109051006051e0313061b020a060506 84
    0x2000000781501b4200181000300081d15030005011150348105802c498202d88860b026500301703010041540d4030118403541c1b0103800d80d070102184c0c2e20f000841009209010051520314100800e010030700283c6001751002034030941d8065000c844c48510901c0003003152000a000880c194076289003a51660030450494120a4500d4182502e40114509903044900d18000444c0c1c00300e8000249a4005034290050850941c07c038994102600841d8843c0c0814502a00600d60851036181300c1e1186035801ca45601010b000f0056443d5070b407001040d543c400d0b01d000d000c90400c81e8218120341703800c0044901414000700101038a070158a201805032034001d0446420100e11200100480c3c1100f008044078000038840d1708400d0007510402070106010780000c5401d0b4a008200300700782496804030401d403041402c020b07843d050081c11160034050b000440b80000000801441a0100350007100d504591260000740040c010060008103840300480b000401a88005602c1300462101e1380081d0700030070701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 579111834 1250 579110584 579110591
    0x7020112090323270f0d140c010f0f030b15190305060a0810051b041d010e0f060118051008010504060506090603010b0f070f0b06010305090705010917282a09050406 72
    0x1c40582d62a141558520203607200c400301c02e0b40234400e01c0040d02003403c01031030200d29001c2c0200720520445140d01410b0361900602c03c04d994484280111f0f00f80151310070b0703450002000684113850540d0791070700441e04100100e1203e16100c0b071514255245400144004036240c0180d802030200a09500cac1215259003204009600d800000c2000c0e18548910030107a034100d96442003108016800b0b040c603c11390005001241e84640e020f0758009409103031901b0031003000c14050808425503404240d000110068903005150406400c07412242c00300c50400080340da0364103224143c031031a00220b52100b0200010f0291400e0040a400b107010b01020a6081c10840d503900520100c60342c4090710351008500401c0041d40c0c0c1805803a5001604030090640c0d54a8000064070054103800b4000c0c1209031500c055900c844104419006544981040b081600c01d43d60101e5441014480546032040e00600e009920b1200d4a2002d011640301100385c0c03500351614001000819016208544071030301d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 579113084 1250 579111834 579111859
    0xc01080408040510020f07050306010530030c0d171b2b0203040506060a051003110f040e090d020607080105010302070212120307120b09010501050702011209032327 72
    0x211385000c0280c1c401d86800622012503004521032601400380e20003846540910018000ca440b20950380d500300920040c40d881c3d080362903010441c40d10008080e003003103200200344e46e01d54060010f039018400070a82c40e00c1c0c4003d1507046a02000d00e504130351408081268a580c1d02c002201400141032180ca500e03031540e400391800800c00305035806034000c900d50035008420300092120034041d154002d10100c038a207148501d02004220074280d444408000e140d916030483d000030798508100e8110700c2d149040c09a846881fa180c1d500d40d11130644620015100d00c5500c6521071b80001801030140c0d441c0d4554220036807800004401a52021400704d80010260084412a0900b0003d803034084428040c074035103078075044500515885030440036007505420901e400c0d034561a9140d00ea81541c40c2860440e5549403079000588000322203194444c403483c5809002000e055002c60340c80c2403848045141d00880f582820720248500a02d8014041c4c00c83ea00150100c4c071049851010f07010602400c104103141 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 579114334 1250 579113084 579113089
    0x10c0302070b030f070e060a0215060a050d080406030b0d1110050c030315040f20030403030e0a0b070807050c0c010c0303151e0503060103120804020303040b160204060e01080c010804080405 83
    0x100f0941d508264031012a042c84105500406000c8071008140d48141c10141001c00003582c0300064208446807800c042c2c0460255107400c20104007412000c0c10b00440341d01646004500c45e80184140c0000a00e0081c0001451400700360140c00240c03c0030580000340070010401c00c0700811038180c1c81c20f1003410000c44c100e10800b40b020718840d440d40c1404070030b14503040e401d00094505100441d00110310b44400c7c00c2262100701d48001c54080d416a01c15103030341d03461809030000d0044800303080403441161409010851102d001c9403181c10641e032042655140c2c2e050646850040128501d1560851441c0003502d522440d1030303131002e501a00e008144116070320300c203002d04003842c0c000182059090b006003034469005007001c00281010707070007441f9a6141d070f00c0c0c2e030305e03202d81c082a00801c1110120210341555803c2090b43c002d000d0b031011460755100400320b42400c207014840224011820202e001a44030b01100c0018101d41107900504640c80810004450700360000b0000c6840640c144030219503038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 579115584 1250 579114334 579114337
    0xb0301052502012007061103070c0303050907080a152d0905012406110f03030f0a09050d08061905010207060516060e30041505070f031e03021206010c0302070b 70
    0x4500013a0b09551503a0506289041c0c0e0a42c02d810015054100244a030065000d0042d002c090b03018075000405440e0313600c0c034900b400c00540c0b1403a0244035003030900b130038010614400c0ca40c040d45c030041041514410303010080e5041c101e20304083c3e007964a00860f0643d03c00740d0090b190040c410707400001d040e8882c01d41c0c41d551070f180c043c2c0030450103003140051208503000101e55a80040800042c1310041e4060b08030344e0b41e0701c40201030700e403018848408168441225008003440307940c4170341529904100d5400c010044082150391a100d01984a44410701010f101c0c80401070f5072040c0e001d001d110b4145602611598049a906844140c203804104080b5885126040d01d581024015000c02c4041c007401c140d940701f050050031641580404090181000c1c4802c0f1801c861140740350408461141c241907a140c0a5200080c15034942600c001c010964000184124450b000342d03003804400300440210200c0c0988100c0e0002c1d1014800440c45641c010b000f01c201092283c411240d43c2c6442c0d90016403503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 579116834 1250 579115584 579115631
    0xc0b0406051608040f0f03110105071d120d08060109051206073f0906050f011a040f0b0f280201051503060604110c1b040b030105250201 60
    0x42a50350814072021500140c40414a200b071443c20340ca090070203448038a1401c44a0400820803c40280ea40302014058100c68443c01d0f0107100070411450b02c40000790540c64004085100c150000050bc4507030702e0021840e00310303006240000c003646044400145c8803c000038240342d042c04007605001407940c0da00d802040201844001415881c14000d0010b0890b82562400340920030303210300382d0200692541324055410111080d0b0411f262880c0741c00500620b0018030240540d801e007000c1220f5002c0002c0d50b98101e42910b800e001c80c0e0951050b1132103042c040c1e405284200401c0c0e500810421260030060002650ba140075135103814110301c00c602060720310004659070038000405040ca0580c080c0f0031941e01030321400e50101034030a01000251113203401002d89214541e59040c3c0d8003c2400801518243d80d801e408640855507813810703150007c14580340152103641031a0143da034034101070003070364000c62400c013101500249a4506c0d000340341150140c1d400310740d6208a0401801e0030198070529 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 579118084 1250 579116834 579116843
    0x3050c0c0d02240603061501120e2b09090f0b0d0c0306060801050c040b0a02010b120f070801110702063015031b1c0c0801150e0114100c0b04 62
    0x804440002d112a004803803486003460b800343c00003004070903200801e00d00d500210300740d800e1184410440041c1e6050b44280622007020f4900349565000141c0050381031203107828400b045054404c203070f01185030503400f40d2a00d400110328043c1041606900e4000700a1a240210089061030080d404109103846698081c2c903c028108020000e00244c0d104d42c40160202100902079803a0008080301c0c3c0d482503125950500d200066420303080c82c400c0d030250328492801421929803860030300340c00d0780c0da092603240700c05607000b25000081c00600c144911100b800407182d02d1420844103030200400d60f00008000310840c410154051800c02911441c1d04107400c0e440c099500c1420001e54440004d40e204c125a4004d90150142a1000403032801014043c142221150321889085070012210104410001c148030642c1c00042002034040d01300c2d49251200c00558445107035a151071040c650310a100d402c50b02041140340129030304100d00080c10b1820380382084150398840742d031684045601150180d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 579119334 1250 579118084 579118093
    0x30c09090109090309120318140f060705340f17060609041b03060e0c012337030905071d0a230a0b09060108090d03050c0c0d02 56
    0x1250320341020344a0152160100422602000d0398000d00382040f140101003541e10000440c50403d442040c000918030400b42d20b200049944107481d10303561070700346402449889419888165410000160b404c1c1d0780e0003100078540d0254200500320b8100902c81c01010300b80d40c0d070382c00c2e80358600545e412600401c00740441ca40301d42c1c03502041c842c03050f003500c076000240d400080600c4001d54a10b03140700c0c1c010360030195032032000140071279104020151745c1c002007a45051200c3c5803c01400401c0c03000c2030200070780310340800d17050342245000520fa100c0c400c100300240034011040d401c1c9034500400085040081442162101c1c1d011001840003c82d01a00c00251901241000c01005201d92002040c252004140007000c0012004042000400c40c1d00c126503107e00d01100d0711224650802580c0d094102c1b2021800d191988502410402d90154010130054020490a5202c0c07006e081c410410000070f02503022200004402031f240c003619204292005021280620303005000c1040741c410380350020f1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 579120584 1250 579119334 579119347
    0x807020706050403030f140918040606140303030408030a14090313060905010906033620061801020a02280509101701020d09110117041e17030c 63
    0x240303010380a4128004200c42400104000394001c00e040385a50700500b4003030b03d8030446a514174034501030400304640c0180ea400c005c02042c12100b081e40d000324001c600074030540e510b6244a00100d40352142c1e0700c0c1c041c1c3c010000100810484409140c02510010001c112078507052020001c03024155961a02904002515480e011140705400000c010504101a06919020000e01070244a206070010715032140442d020403d080c00000e072143da4000081d03842c0a4540c54a40240140700c001110944c1b14035201014040314880500d40006c401040c0c00e181c48602c0303a1144c02c103500d6080c0c90f810761181904140060380d460180403008450110706413400c6440a413030b81c0e001a003507802103000f44000d40030b1040311200c0030303000c0d026034604d240c0d000590010f00b1061802441104454850706240c00381400810140c180701d40740721502640c0e06100c0b207035078454103002c082c0c081d00c00a0034000316001c0c803505215101041d480060041074030042032041c020402003164001c9614903d09807001801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 579121834 1250 579120584 579120587
    0x603020913050129070b070f0f03060302030307110f090910060f0815070513061d04050f0f09010204050301091109010b03160810091a1c05030304020609010201020f0a0807 75
    0x700700162444010511180d4034060304907103141c2118462068400785803001e494242100350483d42501da02c140003c0359407404540c020710040704600040002552021341080c13842c0729020308030640c0e400a01031490071070319540e5054141c545802c0755400246120720b05e80d940d660980901d20603404800074054944c3ea00b55040b0803100c1a0304451000c090500c0240000040003c544a4000d80b1020761005511482000c1c0c1c0c07603008507900704260300030001000c43c2c0075922406c5440491b0041c0c4100e14202c0c031800401c42920012140d0501c24454940050002c000c940b1803290841065000145010784480201e07095401c0c03144181d40030740400989002c2400e2207007019004060103082642582001d41040c179800009080329020050900c02080d14880107490200007070040c1d10003000600b8a059181c0012170881d03172194456401300c102803427144000d440220a00358484061031956a0380e50810030ba90700301840e0a0304665090207800e503507213101c1d802887e1006564580c01d140740740c032400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 579123084 1250 579121834 579121849
    0x60f12031d0f0316031e05060402060d091e02091e0621031b06060a03080a0e0109050a06020d0e1504051c0602040e0f01090c0905121f060509090a0206070213110406030209 75
    0x2d0003401c6c0051990020620104825400582c104c440564485c0e20020b6500582403440c80500007142d030031480491660400120141c89100392203000d620340d02c1e000c1c4401c0c40006c04042c07103551301d404000600f06141c01c0344104020180c00507108a1a01440329851031600801d00e610b8498200c40c05109281100700200c1c4da010800300c60007507009044d5074842c8558000c03401c0c101c083c0000031942007140d80c003907007c90340070308000380c4280c1b40b01e6901c02c0d00a54030b400213404030340030603001510038a440c02c12140340300b94036401c0c9119500e06442e0009112518503c04200126801070403490070000d085800280010800c041c82c81e00d940c1024581604207503010380c440802240703400306000403540c00c252110704483c022540d4241c0c54015241003820000901c0b0a41001c000c070352417520a103074007540035409070b810a4034151560f41d01e5102103951411414000b030342c000300511031040140740c02d50200003e02111000440d1451198500f00c100d0341090300031703d0100340c0101c2c65802a04103103c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 579124334 1250 579123084 579123113
    0x9031211040b16080a210e0c13020c120c070b040f090209040e01091407050a3f0303050f0a0b0a0333060f12031d0f031603 54
    0xa00800620610100260841c4541e108859692401040f10010b4810344002c4501c4a070f040344095581d919151030044c03c2440300000f0050500c501d201005088440703204425040c01c0c100028680e94608108201d040f01c601d4503c0e14106800304004072588100348403102406492001003619107400c49006070600341c2c1600101090744051100b0800ca036024510b80040f162151001a134449000c2c010502801094815902941c00c00411004121305401390b01d801d0703200c00c02515680d40d10f400821082106034400c00c100090000220000e050700350200400364010b51440b08500004800d90b06894407040300c054000ca03569108000a00c01803249440c0d10544000c01000a000e4410000c0c050b251a404050803d44050a06003020111030306480408042c0204000c0c05541500181d130180006010f09083e01307681c02d1700015900707602c80d00e0394546541510b6801000004a00d5071600c83c50b80c3c4400d0b80c1c403a016030403142d09900d00703008035002c202140210b0301055080d42000d0112144a8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 579125584 1250 579124334 579124367
    0x103050c1b1e120301090b010302040803160618030527090702010609050106110318131d010b0108070c110d08030124020c03030a080414030c0604050f060708060607050703080d0903 79
    0x7500c48200000c0902c1c04c5a040d00c04071240040c20180c0000124000e002d6a040184184000142c9076031980c1101d00d560803c81c41004240003000041104545c0103800c0741c2d008002c2103091001c2811a0340c2a100203e60f004500d4200d0000c00d43d507000a5685c11090f610303c000350759290740601c01c080d03a81c01f40b6809401c00d03042000c02000d505904955074030039980c4001100b40381c034922010503524072048d04a00c20700c4000c03e0005200807003100100b40710600e104001c662034403181c00100e500a500d9648660b480380c0f42c1341061b90350b43c1c40e507280b0120b1145a6517030094481003d9000610140091070107040001c9280e8000d0b03450000004550701541803407401d56010f00b403071044659000040b2401c154640c80d0480d07050301e503850f00e07030801640c4090300e40c5a400003203040e40c418040026560300c01da01420466204c40a200c0b04070b900c0c1c100996182e030005e00c046000a4944c2424402007046a00c1581101d00341070f034a40355949503400c80c07508102e5181c0c40c1c407200307414980d20042c2c461441e10407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 579126834 1250 579125584 579125593
    0x1060309080702010f14030c0a0201050123060d020706111818070f090801060618060801150302093f0601080c04050603030706090312050a1a0103050c1b1e 68
    0x80d5120100d990284401c000d04010b0705207820305056105085c1d50400100300400310781c803410a01d540c02c540742c1207085d0641c0190710f4000001401944110010a580d0240c60440314410083d41448615400f200d0140e1845408002c4400011841c1c882c0210000003401881e40381c400200d1980c0c00402032040003440b8402d9580138483c01c1201e0b0711207a4019100341016041c01c2c02a48094a2a200e00c0c1e0004416510380741002641c0c0303070405a1500035585500c01c2c0990300741c40302d40584024900380188505400c0384841090340c0390107039009208010f0b0060040e9901414850744285480e03d0703e40c4251080400c903908020b15405e1504400c0d29070100b4041c2820750304041550b965502c450704100c1c803560711800419060b40b030a02c11200e2250308950180810b181030b050103082c60070141c1d5070000c080d14240001d0810301a9226076002d64005c0041c0f050403000f03e40046001d880c011f80742c2c4060510030072007419000802d00f85520f0b000b601d1405442640c030301d421071032140400e80900e156150403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 579128084 1250 579126834 579126851
    0x30f0301030b2a0a140c1501050a0b3a06060206131e020114070309080706030e031608040b0d060e090303060102120d0615020604050c03010e070e1801060608040506010603 75
    0x10a036800c0c82c4901070240341629040090812510030980c10009218032070f002652440503000801d40d04000e00d0721210107c45c03a45c1e55410b00c082a08a44203500c03140340e0602461a40146c100150644038850010b021a0144046901c02c500119200d6228419940b01010000c4c181c05001c1154070109102070004950070b5a15040f000621100d825840c00480d020b20004584c01100031542180343d041c135031901d4170f00918020704146a203010303400c02c522500c400010340621034001c03a0100d2281c0030241d410200400d00189010311825000c40d035040c010b02c0049400e0807040d004c2c1c40e640446440100c0c505240c40c200c00322a21001d000511660806c00030031829036000070f0400701d046009152540e03501c4540c19100300601c00c40d009030300888410401501580c0c0e002035064004d5004030305031090b0038072010415013201e030442d078460341a400c10f12040000103904031a1652001c0c203020f10140c00790740c2848050840d03101f5000540440c003544d0a010030301004000160140210f4103040107002d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 579129334 1250 579128084 579128131
    0x1e0b0307140d060e070b070308090c151c0b041a0a050402040f21060609060e07111b01030902040903020102071403070c05040c050706140711060f01051c05030f0301030b 74
    0x84002d02d0103005251540c1c00a11030520070040e40006003000d10030380c0d89610b21f078038004100e0202079800115a20400b1b281958034500100c8402d000014100e40070b02c4c01c450707030130403e000c969905031a1101d1562160000110b072500d0003040740340d0020306259513070880702c3c50403c480b51220382c0006009503c140b0080c051100e210003030b0350135503034000000202808016401c0100e150480002400d19061500004210307003941c2040042d10541c0911913455aa0900b003200c002c1c180c1c0d03034400c0407035110074041c2090002c0d81c00d005109810601d4041514138058000c81d090340c00d000703800c40050794002248424045034054004959041d1000755140c1507098a44100c255090301480384a55960091061080e005004440b502644520240000c818030502c0040c80780c012034824021503000c40c001d90302490b0100340103200c0c02d00030284c1d00d503690801c03041c4030440c0040524401c60740c001e61711900c003246080024000c1128819155075a940c10752400c18840c0d040600005400040c00e0365110440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 579130584 1250 579129334 579129349
    0x60309080406210f09021c021e010e04110a1806020a060203130f0c0e0c071e031809090201030b06120a0e031605101a10050d1e0b030714 60
    0x2c2d1101c0c03514504045101c02c90f00c900480010700402d81500d0808041001c1d52640c101801c020b00888a149400b400c8150f010044080200c0095100e114000501001d11511100060303061062412818208100b00424211401440e406100c04804100203221941c09030749103041980c080900e0002d50b2802c02c0103561110102e10003043c058012001504255480140c0c804240d0800f20072020040d4500b420400c401c618000d44c48141d0450f80041c00c118040700031104c0c0304c3da05c81404c1c0443c5070398040c0c1103200130400500701d0070030008261001c0200c0700403140c100906440d807000601d0482c144005005c998512810360f001300006c1c48114001700400503499800300300d2a0000c0f50011154907101d08501c100d0800f2003400702085008000d1100005403c0d50000321920100706100c400f206001c0103a2502d2101d80c1d00258058000d021248a41c001d02000e07100460041106003100c203082c1029888040c0302401282d0310517125105207030401516005055a6140c00800a0510046142c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 579131834 1250 579130584 579130589
    0x60501050a1715040606050307080a0515010e0d02030a0b071101050f160909020c0d0e0603060d02120f0a0803041a0603120a1b080c1506030303240310060f0603090804 73
    0xc82406000080c20804070800e0110f410340300501c00c020031a2903d1000d0080d4000350340d0f0000003114100083c0980c1d41c071348906070152039010b8261110f1400e441c011502408503500082d000502142010b005032020001030307001ca442004c461446141c4940011b103103800786441515241c1c180002c1c01000541c0b400525003200ca00341941d04c0910600c0790030303143e014659200b2030400c0d03c0006c03514400480030888005400b0603990b000346079060041081040e0009a07903403588410303001c141030011f00d0074503103c48200100c00151501c0241d040d45240c1449080b40042d559610008100020082c0290300d207840070650020450050410001290390b620300c0007254001d41c44c001849511060085084c119400003040ca0b040100c5010314006080c0e8000b46100401032090010844241600310500c40c03003003001600460455540c00d4040e4103800c880c1d00700d246440740200c4040402d80b0305016900c8065070482010900c40e2800c40e088003043c9180d4001000c051030821840000b0355480c048804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 579133084 1250 579131834 579131867
    0x3110114030f01171509031b0109080a0f0c0606030b0106110a030e0108060a030b10030c0b0c060606070c080307060c11012d0605030303190f050103030804260a080901060501050a 78
    0xf5051180116890a2407440c00c000340c05c1101810820001c2c0000014020b04c06030903110400c9010400a250a0b14841e00004244503010310619400e00c0c880d500035914601d140c0303000c0100c1090b54032540115252500142d03454041080144036094018288400c03281001008114a400d00d8030700a2440350350311900c504202c6403e0110340c00f983c8000720000a507400c5403c584460a0803581d527200c0703007080d00c011240120040000640c910103002a80c8011340880064510f5642d010100aa44d91050000300e0b80e8600205000c01c00c584104080c081007841403500041c00c10003035101801c7c800803030040b85110b0781044880e0851104c90a0400440d411950b010a100c1000c0e582c03103006840a5004586c2500c804010007400e45110500004500c1070000304100004001c00000255102400003801052501000c280020ac840c00784480d000002080f0083d030301d180c000f03400525031100c420100010345100c1804880c0c502841104000c180908002d17141860840700945820b0091130310300c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 579134334 1250 579133084 579133109
    0x904020403140a1118071d03030406030506120f03030118023006030d0c0b04051005040c0905070509010f050d09021009051801051012060b0d09060b010c030210091a0103110114030f01 80
    0x100000840814201f800801000c0c3d90b112030312180c0050041100700c1e82107205071a10303107541e05113590111308100e521804038040e51540e8244001710344804030a580400381c0b150700300440c5e00180f11341d02c91074148520040b0141c4080c405c0c3e201d1080c1c900c102400305407003600f00c1010f880b100c83d00104100d003150b905c80b40421079682c880c00c6c41030420301030040b6404003038108402c000030850000600026500c03000130030041600c40034422216801060852801705003040c100c1c81115001d0005800d08540c0034202080203041303680441d4146162410310000716664103018460f40c5044991042e0340b8406d6012a45a0340c94075000444c60382c0066000300c00e001c0ca00021000030102a00200042c001c1c901000355500040350b001c000900502c00140d0707c0506c0c1881c0c500d595846400202c0f4095003650041000000a07021400200800c400c00c880307940c1d140c065100321811140509008501413031940d400c2c40300d5800007500035000510000d20280c020030411540c0c1080c4407040d415101044c8550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 579135584 1250 579134334 579134357
    0x1a033121030e19170304030c03110604020a06081801060e15150a141e07020109060c050715050d0f0905010e0303070507060b01120f091e170904020403140a111807 71
    0x41d00701c01e80e020392104c1c0d24074000108014560007010325510144a5035600b14496070080143d0f8440c0f03810f49009500c0b1403143c2e810040d0903c43d09010b5040b407400036259032004084803029084441d5903211030008208001040490002210b038a03072410410741e0440a140d88030000c070a4248100e04581c000d10507994080f450030404501614882c0c0084800103181c17100c0c21118800c1034000b01d02c200d0015041510100e000d81c410ba00c0b1100a5038000300901d580e50400c001903060a110394107131802c2010a0043d1001018a8014030740203040c2404005103455203414600d0075121016801480c41e4010018840361913801022603141d41e4201c01c000a26617200c100480e404d502c1c1c0a85074100c50304082c3c106d0107a0706942d002c1c2c42604e226210140c01d01a503950401d2141d00e901001411007078005a4207d01001c40c6401000340c9000280014600741d06c0750b441c50b0000b038070707500d482e44140c5c0000c0341c2c1070810204545420060000310703100700101c10f004d000040c0804008210504004502c00303a07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 579136690 1106 579135584 579135593
    0x902150c03030f19060f090606090b03070509030312180c01030606050f030901060806040305041503020304170d06032306011a033121030e19 62
    0x91400d40e5039443c07403c2281100101142e05604508804980c4509640308110140c0520216043d80b682456101c5040761401e41015041c4040d0306010320010079424103070b90384a0540d03c0c15940d24118500420b003540641c00b0208140d40008040c0400c00b00e403041c00d1886240e843d4101d17801ca0106900442c01e0310b00a01c1000080382e8104103800607484101d0056501c1815200082502c47c0d9852545190490450701600000c03000b0a050002504128030042c111140307260940c2035040a0310341c1c0e1f000b03820310f8500b410146400100d60001e0032583c1c2000009541002c45d038100c22048110000e44040340744c00c032003100c0c0144000410445640e800c540f0311010201d01d12800c641c0c2c0c40321925414103282c040400d41ca0801142408203843e070710801c0c00345910541d40c0302500c100b030035010110101c11401f604c0074182401103120184000040c0d041402c602d888103000f030390015003003 = true := by decide +kernel

theorem cover : BRFrame.Cov 578956834 579136690 := by
  have h0 := BRFrame.cov_init 578956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 578956834 ≤ n) (h2 : n < 579136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
