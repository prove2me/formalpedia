-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0003
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:18:15.048418+00:00
-- url     : https://prove2.me/submissions/95d567c1-01bc-4b3c-b88f-a6f81816f0e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 359720 ≤ n < 539576 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 360970 1250 359720 359731
    0x50106050102070302011403100305010c020102070b01050a3002060d090213050f01061202090907081b0703050702010503070c02030d02030306010224010909020607080a031a09070e09071b0803040308 87
    0xb42030f01c0b84c40c540c0068207400000b004145aa00007000040f080404065000002e5400034003d00c580049020041d0003548007a00c1625281c2c2e6440000c1080c0c10200c1d82c4804407401d0070304421441c0c2121550320700c00f080710b4080d0350003c4203914100c0c0159882c00c000d00030b0420010030004901c1c041d4810490ba0510780e1420040d0182000704028001d1300010080d41103070800c1c140b400381306001c901034030300a1251805940e488450b86050040169000c00200d200d0803140b0780c0e10216644880c0321154500407240000c0c00200c04010207801541705001031500408a0709200c1078900e45680081d040c440040901c000591010041140720340c1d04011500000c247d1544035121100643e0740006d50907014010840641c3e01d41c60900c0840d10f8123400c07039a56a800020654517510201c80c02009410302a620f2600f140c44407607107102c103203000190345000f17000359211528811445c00c180411a03600070040c2051003011000d03150272000e50708889046502c54000f0654a01d814900034040e208064503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 362220 1250 360970 360973
    0x305010516020604050607080702030f040306060503010c0c05070303030908040503010c02010e12040302010903080a02120408060103031e08060405040602040906030602030406050112050303010605030411040f0207020102010e0c1809010b120a050106050102 111
    0x134040854004076800350443c8071442c040b41c0b6a5034881091707181d807041002501500000250020034425580c0c003000580c2c2040380207110180300704200703e86440c0d07141c902805a030092081080064082e500501c006441508076900340341e550000030342158110700000016035118204c00380403003130511482c62303107002c1c250300e150a2505540000f8007403402e1b400b004140f43c1001170451103e5000b0044444503a402c0d244c6255581d0325000c042c1c1d25107e080c030044001c522011604000c25580d0341607d21889a16a034902c850380d00c0c0010040500740292040d9016503007008042001c3d4818041e032009035018a40c050398a0030503161440846005900810b1290020840c03203000400100443e41192164540345460b0b485a040140a203080e44102030781c803918043d58401142d80b95005865800d000f40c00070000c1503201e802280e183c0c01c41105403584440ba030a001c5a40c4090585c0203504034080c01c2c000608844254041a031100c0000c0e0046c0c11684901c0c2d401d000c0040074060040500020320 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 363470 1250 362220 362233
    0x305090c01030e010209030102030108070602120301061403060a03060203010f1a030106020309010f020304080105070804030f020619150302030109030507120c020f090604141807050306010506070602030403020304030c030501051602 101
    0x451544461415280c10304141c0c440518246000d02501920000c0900034001c658a59550030706c82ea55144502c035a40250240d20b03411503500a00c4c0341500d0499240b03886200d40491a1a85100150b000400c01c40d808680044003002040c86403000c4c60190a03904039820899080221281500034040b281044c40303101000184042540401550f010884c21700380800703080300d0250240d0440c080c03500149020340c42e1004200d546580604130a004900940300c44111700441ca0301282c450b081143c150107000c21201c00210400300540c048035149914422003e40503807a98000b0f429204200c000380c0011700b011400c1e81c1400100404042c2004290030058140d03440d503030200d0300022130390800350f12811700d12000501c151280d0304010724118800402c18203d01e0b21402c0c4030501081d00b40c802e11244079a00340070905040000340303c1c3c182c81e80103209505046a039607421020b94001842102140014000080000c041038081c030007a512940000c00c642c5400119402e00f000600c0a1208550000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 364720 1250 363470 363481
    0xc0e15030102040b0904020906070803070309060e01020705070e060402070503030907030c0602060405060109020d09050a0302060f06010c0c03021302130605040501030c03050601080f04020a050d030302030a060e04030914040b040204030303050402030d0305 111
    0x4d0302150b10603881910050388440a11000640b1070040101c0034000407000010064000d030300d5400200541d00c42d402c10461142107600241c00c0780100b4000400d04d5201c400d09000d0682280321b01395111500500c054a4080b165603100e0030340e081543c011500c0c2c1d21000081c0200714846000320301500c91480181098541034484641da00018810500c01580c000340314071030509550403041001d50048101d803020841884c0080d510801140c1a0f1410754900c004284158810034000f14916003054610058070306540030040f6003d490400030310082d90800803800d00101c4400114010b0285071256034480d441c040000d001d45080704424030406190504108060782c00598454100d80004200343c942c0e6a40c1c400b240f030043d6560006540702c224000f0314010168590002c40c896030007920103104517551580d2078000074000740c600501103041103c0a21004469031040ea103401d03801800403034400041408113040303901680060740080d440d03508010940c00c1c108a501c1844805181c01c102c10300d0070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 365970 1250 364720 364739
    0xc0b0105030609070e04020d1a06010e06030603070501180503070e0106080a020901050a03020702010905030102030a090203011104060c030c0302011103010909060b03070605040506090a030c090207030207090903080105090402030a0c0e1503010204 107
    0x134000c0c0145170075060007060554881d4907080c142c45900c40c1540c0306000b6000d01d000c400e45070482d02c2d54002201520003d030345007050010b99024800160080201c0350030440151030b03048442c83c5800b2405e901e12000140c42c3c0d420003940c001040c9001880313002c0e505200d00240042c84c028a000280b07401000080d17030070b980c4541101c0c001809854016100d40085c030048503254001c5c0e00081c0d05600100500c60664221380c80000c09500c210020032869a000021500364010b80c86803c0205a40320607041c082406440c040c10401e201b8400015180c90706419080d40350000e80068032420340c4d5003d9102044006c1c0310310708444104400410f2a1444d210000b0210b100398050540102c0300810602419100c1445e90b40c043c42d8001c0f25000480d40f24070a1800079001068203400503c9071100000d800e074071a01c90703204007a4040d0b607401000ea080c9400d0141810002d80220f81611525407032034007081c00e00c2082000307401e10301802090b030700b0007002c5041c07082649008c144c820b0b4810401004800d15 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 367220 1250 365970 365983
    0x6010506030604090c0602010c0e0a080303010603020705030706090305030604060503010506090a021b0303040501020703170c0403170d020307090602010b01020705060712020106080307030504050a06030203060306040201030b03030c030a0c0b0105030609 110
    0x1400c4460a9980d80c0340c8001c50090b05030030100a0035403c3d01400841c909406401214804000b6964100e10549540811008554610070341e416600100018802984a0780003032469a010300112482d00d062582c031107041320301103c0f0a0b0002100481886441d14041c041c400c0102801c8009100d07500785a40003d64050000d00781c12105c950000b1020020712400e0900054064102c050341d40340d2500d030610078007035808000e04400140c0301150502c0c103070a8010310180503d4043c034040381000d0550f40c4865100492080c090721542c0d05200188000c0014002184160815514000601c0c80c0c03c002a09541c50500d0983c1507400c207410501080c2c8882c810b40c1c90030360f0071941860a03603014040690050569400003403042c0800554107081c95000001441154002d451000c02c1d03907540c1808070300300c1c04240c446691580056000ca805036100e900000303100007008058a00e800064001c6a02e194000916100032403070f112084018413110444160042c0000e03006020a880d02038041070300e403007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 368470 1250 367220 367229
    0x50403080a09030210060f030210020f0304030f0501020f04090902040606030204050303090609042004140a0302060702040504020f0402030a0603060506060705060106080405030c060106030506091006020d0f030b06120402010f020601080601 104
    0x903a110740007800c3c18801c2200524060040e9420000303035440d80e034401546240350209034044c980107403a10404510000d422410321060740301541c105411036440c55a9807400080544407503400340016914040220014001840464070020f0038030307000d205100640c0c1031b030b6101c0300078144140020400b039100401200c080d03260480b490b90741c4071801c6001800401403505c41c0001c000b000041000e100c03082e90010410759940d51200b5254226113010801c44c44802c0c04025040701d014004000141000d07081035030001d01c010301c4240c45503004000b080886e08122070400341d00d900d07a20704105000452141d55005207064491743c1c84c10b225610381c0c0c0e680300c2c07044c440c00741003003030103000241807280034010768001544000950f5919651080000c024080c00d0300c45612a4000c600801c40098030b56840b80f086600c10b40151414040c68042540c84151400548091545804a40c18160b403000d00900703044201c06580203040c1401d0000600d00b00345141c5941c25503020b0401403000210004581d030445 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 369720 1250 368470 368491
    0x11406040b030f060106051c0c020718020919050117040b060904050703050312070305060d0302070b09010302130305031905040e060904080c0f01050103050f0304060e120102070c0602070e060405040308 88
    0x18506800801c0c0b43c0400250080e51a000f000004104181d11200030b20303101c9244d000c80070506643c680241c040b601310540c80c0d005a03101c09170400c200d80e20940342c3c0d0050741d81120700609080310440451480c40300060704441030000d40401348119a0820001c00c40d900303180030050b905160680e10b6511000000e0291441050b5550010b810400100003030405540d00c04180c03a107650042c00d03c0d20b4102c00513103220020a0030f2400180c240e0802481007031035281c16600504440303140c280c6800702a806a4070303c43c100b5400b0001c0d8190300184440350b500940c415801140e80c0c001c000160080d071035444004000f0030204210030410804c11206064001604890303500d4951140d1030090302c6403040c0401d80a080c00340c13070708264400b40107602c500e0480b4000c0041c0e41e0342618450301c0795224815401600045113150b8000c00440c18440c44207409001303003400041c178114154a61114000180e4400401a030001106020307000208007507036084901034505000601b000d07940546840030003000b0440f003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 370970 1250 369720 369731
    0x20601060e01270f0b0304020301110c060411120f03040305010f06030203030d05070504090905030304060501060201050606073807030c020304030c050607060906050703020c060603030304020901060f020a080d05040201030e01140604 101
    0x1c46001141d40d8001c0c0b40c9071111801d83c1d5074034a054042c51b04111b030181d11951810b20384040100820049030030404070300000c0c0c003980d0b855a55040e0704050903e03200d60814110160245140000c00010080885140044d5121459403901c582900d901c1c40303845c0d41c07241c1480d80030001a1400020344109010788079001c511a0f8840000b101c180c01180c0c071070041d96007008403c409002010000311300070ba0007940c2c00c0c0141c0e170b260360041e402d0b248161209904030004014000101d0741908841041540348030080300b000d0326122034070103070300702e49043e246400411000b40540e035509031103000006021800958101440c684a00d03420036954402d050140000160802c00c01125920030801654042410002030520560090094002d01020903003446480d02240603440c2c0041582e1103158010207030b50042c0c1c01d1034070844656170004444000d500c40c1620140014480324013801010108041c005000e1030580001030031786402d1141e041480e450490803030240004003102e20703400707282540c01103030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 372220 1250 370970 371027
    0x302060301030b091603030906030507140301050607050709050703050105010f0c020603040303110915090a0f030c0303050f070606120209060409030f0e01020c030601030605040204050c0301060203070b06010c0501051006020601060e01 102
    0x7070020711a6041d02107410b20f10f0106c02c05810410f5501a102250350410190303840c8402581c5070070035844008000c050034001000b081c035020300185030083c45001510400d0b90384c1d01186090720400d80310203000c01d441c0c0b00140065680511080a000d12a00c0c140840032403a80104001d4403010b080035007050707211541c40040300a050104c130000c3c4000b402003c903c61070391013908003c2c3c0100000c0351180000c0b100001e90081c1c000e10400c143c94000e0b5244820501e566410b4540d58000035280087c0801403281c54003140c01403040100070085000303480b40c00e000606c100042448014070b00e07440b652500d07000002295112280865600c01c1e410142208006080141d25000c8404d0b842d07545849000300100c2007011300e41005014510036203081c422034950341d6028107180024084c020041e40f041c011030002c2000c1c91a11a0000c0042c1806c581c106101e88542c7e00355a0215109004248420350800c03031280e040042310300619441c54401800c00e03182c00000c002d200d10650703201200c009140c4192 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 373470 1250 372220 372223
    0x10c0203031b07080102040302060d020309150108010204030302010507030c120905070f06020c03010e010c080a02030606040302060403030c0203060603070501090605030408040801022208060708040605040f0204020a0302071401060302060301030b09 108
    0x1011500102140d031198034018240d101c01e10141e8400c011802110390019440c0814000d86060300e43c018015414a00d51003480c1000390401006041144180c00c3d050000181c810a201d01800300d420015036103e065040183c00d607034028280f0310401d407a148070302807200d6201c2c040342c8034400302101c08075a212140c10031514060703464001e031403950645840000c80c0d540010b40c01c400c8003015402400101003120301d49003240c41c00c00001c00441e0384a030008024070f200740e00460388607100512081c18582c494010622540003508101c5c045035100e41400c065107001c210666028600302d009242c0c05042600080686d803203407041c0f10901c280407020a04012049094038017500040300215200c414132800441c00c807102e500303402c8401c2000c3c030011036000c8011079128441c891507160003015483d070765184001010010000d907200e01c8206543c00041c1e80e240024001c03c005541c1c0541c48204608040310704001c858849541d60303140940400042c1c030b4030f405490440e0341101100b10651340c0c95800a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 374720 1250 373470 373487
    0x5040606050306070201020408060112080f0a030f090b07020115050f040207060209030102180a080706020705060703030902030703080301050a05060306030604030e0315010b0714030a0210020c0c04020409050417030412080601 98
    0x90b410b0269000700900c45a056000e0011500b85108860090b41e072614030650080e04104098040c150030009031002419800062a0440070340c940000d00014081264084407501401114241d00001c1884209642409204000ea040810510f41c4600c4d01c00000e004050481040e130250340c010a2400500610b94142c5102d038002900035540c0b07030b4681c1e1308001401203514015210305000400400c00303510000c0c4001c10b0350269001041c1d03080c208400c004841c4c012610481c00c00d61602910390060301d013440400010741c490500320b03859505020810105005035000203001c3c802c1842000102d54002826a07003240d00f40c140140242004130102c3c1c1021204108006c3c02d141e8080000740c00403548000f010303910701440141d441c091100c051980c507449001e040800590041d49140315032401940245411a610382c1141c0044120701e01003030580c0c0055101d0740300c0959030b50802050065413440050f030048401c0003207283d4a03280e51060344890010148504105540700001d410307901840d1413 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 375970 1250 374720 374729
    0x509060301020702040212040b01150804110604030602071101020f030a02060408070c0302030a030206010e07050301030f030809010204090f0e010b010201020703020703110303040b03010305010203040c05030705010c020103020c07050a030503040f050109060504030605040606 119
    0xe547d109520800104000b100303850898180f00202c00000304042e01401561800a0507950030586407140e44441e00d055440d1941c640e4054010000000010301c0ba1005005080c0b0030b1210560041c40680003a0800054416154854104000ca114400d502207800c6a1042c1d10000e00341c0c56207000d083c01d101c5441260002074061103803c98000a154000400703034101d0311070803035008140da510305045030b03140400e2000138030303100319030301e00000190095401641c4800310000041c1420307a0b605090701a11075030342c0114400d50b0780d0b4102d2006c0103828000c00c404480c0030700087d440d14202c1d9030003d5540b41c5511001e030900c19206a880715aa800317000300c40c0104511260f4548951712820100d000b540141d40407640c9141039034002132142804030b018811114140c403000007488050700103401039070209045202500600e1804900740c1d40f0711400714080e5000300700440d10f442c00c000700c0c0503109405804c95414400208410844260320408940580780e004401242903143d62900401411b0140c20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 377220 1250 375970 375979
    0xc030d060b0705010c0504030c0e06040f05150307080102030c030112030302070204020304030905010e04060506040b090301020903070303020d0801090509030301031709030a0b16050304150203100806090307030e010809070509060301020702 104
    0x1411201140c081c00c03456000c3c4000300112212150240d071a48a98803000380381c120800c404021100c010b080341030340a9405440410800d492000305404c440b021a90100e46165143c004461130804009101c0a081104000c502d10b080281111010b400705100300710800050143c502e08240c4a034050300d180c198040c1081d0340b20305161401038161000c6001e064001040040401c00354a0280152000c60700050070241c80c1c282003240d84816a03001c0303d06c0582541d005c1101d11082c0d00c041024000850182d4041d0034517500710a801044008180c1c05031001a044c034062211009001c022641140e034009608000681000140300c103a000e0402c0d62581400341c3c2600000b0301408110440c481c070b01b610b070b180072255031440090741c1c5400241d902402a0f038141d4049002c10020703500450f041000c055005081c140d4510a40e40307018030483c0c0003841500007007100c104040c1c02c034004101c41704090030641501d2400c0c0d003000359507409078481c00d44101e062101080a0361029030450340c4954002d030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 378470 1250 377220 377231
    0x3050d02070510030b0904120e03030408060105030f070602060106050d0603060f0902040609091a0c070b04060209040605040506060a030c030e0a050309030609010207030503040b0703062103080108030405010f03020c030d 96
    0x6406901c5504510840f8015210482d1202c161482407003502c16004004150322031a0b1a80d40b40e640580315982041800c0c0f000503030b2400402d54080002e08014807118000304215030405003490300b40070844510003c194480d41d002d10200790003044050544000b860226107450407880b2103000b0702825030000c1c003c0b5180130086180040a500f00401e114025581848030135940c5045d03408075244044003a10b0451a0300f4414000c0c400e980c034498200c070340c0c50b01050529a4607282c500460070207540131246981e00045030002d6013032901032000100000c5800b008689041c80c0407440070302c500340c0000e040550b14070340020403034000d034802c05000c0c0c0c0000842c1e080d141d00d440c2c07180d981d920104003d8424802c02e0002421000c05000716036015070705030344040c10340d210b5a540f24114100906200c090545804000c81d45003c01c407d0044483c0c0b80308440d041d030f82ea9504004d03000b128180c100e04880d0f04100802d01503640c0190b40c101e01c0031141d20300141d90b1002000c0040c1903000384c40c0d45800760760500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 379720 1250 378470 378493
    0x50d0c02010902030601060207080d050903010b040509060114040501030809010302090d05070609030302210405010507030507050a0305030411030a0201050a05070204060509040507170102040807090209030a0b040602031005090405060105040905070305 109
    0x150b00040c40e00b4800d5084900c80d90700e880e800e81c2d07030711041e00c1206544e034010000d40f010b882c4120060311b26401d01400204d000218070b4001000d481044442c1d82840c0d001d40c004000d40f500181c91040b001c10152400c101c0c41d411921444154415808210305050300001d000150303803140740803030051300e0700407003503c450716111400101080036901c0154014424190740226013407000401000905550206a10740f5141c00015542c0ba00300c040207a050040611800d03021443c00d120204d469071003550f58503940d1038035181114100d00c0e0b402c1124000d5004000420050340c01904441d00030303880d41041c5071503041130720010300540041d4203d45c2e005076101050104128000400109699a5015060301005140d4100d4204c0c0a10320460404d42d01c07147c0d040022052581c01460000c402034103507240340040b603e0361a03450f0b0050b642107410540c00420001e41c56a460f511002503c012a9190b0803070801d601d40540d5140c043c05081e00c942e50f41c451041c10000c0402a1400540e1b103c0203580d4455581e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 380970 1250 379720 379723
    0x509040509030307030b06040e0105010c02010908030a0c0c08031903050603010f0e030c0f0a0b0103030309031103070f020108010504020901080a0c0201020405100305010617060603150102070810020702030706090302060a030c050d0c02 102
    0x1604d001021a0401c0241246031074108140c8040e41e54500c1001e0703080c0c0c40d06004481c001c02000050f414080d60b842c1c0410790540520052408881589070388a03031121920348202d0652040e4031808641e001804444500e4054403042040d0211703030f19020426483e41000240180384101602405a28201c226010200c010000d080480400c3c0300303880c4a4407c041c1c055840741c08040d0010034000c22040140000790207940700103a140c1c080d2511080d01e01030f40004900e9075001000a07a8555124428401107603800321000740900002d64042d81005900400a003101c3d40152100526507254540d08401503c01d506450080400404c3c0078106030604101034000c0400f8001e180019035007c3c083c14241460040305030103240701400d52465592000c9040c4804550214183e046004917031001405660410943d40c0b0381080c0f120042c3e50341000d10426182002c0c5074803203010300103040c40400269542205070b5603c0500390030049500b5a0004007160340707104107000c132480145891016200e1560 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 382220 1250 380970 380977
    0x2070605011409041707080702040c0809010501060e03030a031a03060c0c010f020405010c03050c070b03010b13050904020102070b03070309020a030606030302010c020a020906011107030501060e060120030a030507050904050903 99
    0x30030035509044600105105906008443c05400c030171380c0083c020514034030750006000d200d000f0040e01d410303e542070f8000b505403425000d035103000416001c248070800d1828230030180103115500f8411102821080441d8407070044080803010305545209070118a46106205682510002c041d1136091501d04400b070082d80012428192075840c000f440c0685c00c600b4030850703007500d078141c6802c80b60410b10b540407500c55000401c1003801c1e010304c02d0000358055045000e14040c007070b005c807407030340300c8000a802441401c03031940700c6881209050140800340c0d8022031610f0581f003100004580d20390350500e05070b003d4011914000c0d08003141940020500015500c00c0301520f10a5000707200742e12a40c0d82c00c03030380d80c40030180203035000c151400070901c0f41d800b0300413803243e44c26440151500341d0740d00d03100c40f401c51b0100e5002c0c50250441908101c801d69010205600c84000a41d400892502e18032410b0781c2c81c0100c50041301410f58039004100c00c503010702c1c191036005c0360040040c4818607041b5406601c903003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 383470 1250 382220 382229
    0x303010f030c0f050109030b0c0d090303050703140114040903020f030301080102040905060306060a090b0307120501020307020f03030c0403060209010903050f01060306050a060302060702040b0402070f030e0112090503030a0e100207060501 104
    0x4503808004100001030401081c00c466051b542d000c24075095445001d0351400140154400c0d10041040c54400f842c00d00456030160b0083d200001c2e18a031066015040d21214950880c00316680401445041c41030141041403480540d000603034010540b42c00c2c0d1815001c0d40c92038086100200002484d40c60540080c010342e0b418502c18011600c0b03a4040c03543d03640703081d981281c1c009804041481401c1540d4070500ea40c600040c1203840305503407200f007a0300d00460120265840c1c1d4000080000302c03501006003003c0c1c2c454a4004514601c0c1c248050302d5030703000d00e001c003c000380e40004400e017145c0e10903000c02c0007442e00324054070b0001030045d000314020029440100d13a401e09207400030f01c0e0b510081c0b00d100c0407070f5005803506207440c07401c0e1b0070040208031841501d44e20035801d00118001c94249030034540c180b0b1007034451100f8241c2641c000b4002480800364010340c00e007070400714000a41c0100543e5004001c035400032440550000301c01e4103040e8560700e52550781c4d01c0800c1d01001c2c0541904000d0489 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 384720 1250 383470 383483
    0x30702070902030910090204060504020f070c060503010302100f020a08040806070801050105090102030a0c050307080304050a0309050603060a0608070207030605090304090b0f01020604030503070504030c030f05010b010309030206010b070804080303010f03 111
    0x140e580704041001d80c00111541c41903500200d5250056220b1900070000440c80204006001601c840c00036040360050b841e42030203040082400c904016443c9505c101800c0d26081c110b0540d80f6650000380d51840026420003000b114446030418140200710701031075160300c410b03616110364880d00c120b03580e118116903100000d01c0b2080005082d5005200721000c0c07490681c00b07545001072800d030a640950340810110b500780320410501c000b06058101441c042e80c801c0000c0c240105040c100100742d22810380001e44a40010814080706503940d8414000319926418603007541d545000060342801c40b10350001d04160304200401409400120003030083d1010341004010809480d000e01c060501402d44e0342d4007503444400402c010901400240d984440b00d894950301d03240d2a951070810300345440d07000300d07907500180300e601041041c01c0c05146401502071078108460499620002e688403c1846003c5040b43d00180050030300c000b000841c0c0c0500b44072000c03030750b60f0b581d13403c00200c50078081c0c030056580 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 385970 1250 384720 384733
    0xc05100203010b0a030c0c02060a03020a0908030307030905060f010f17010209040507050301050301060b030609040605130807030201060e0a02030f01050603060d0c030b060306010501090b03010506090607060e060a0b030309130203070302130308030702 109
    0x380c01f580000b001c29801400007401c0c40c2c0c00010039002903110003440000d12040d1080062a000200011407044450303940204802c4100e1a0152400c00c02a040901c079a1303d0b44014866040e204e81c20a0071681100340a41c60314800159003802842941102c0d500701d4144410000c01c0c940220055048a80c00d80003001400da032440009000e02064607a1a8007414820215021500c9a002250083c0c20410491440403443e038500d042c56200580c01c030003503511603004100411448605690100c0110781c154030303500e01ba24006042030814051944598008001300d00241c0b120040c0040c09135214001001003510703403d00340001c210884029102c0c2c4194400450154070030404c1c81c0c1240d0483e80d4503400d50742400100103135600103c2d0301e1740e000704081c403841d004100750f4007800040202d0315002d890340341070074421300d41a2280b11401038065401048a445c030307520384148c10081c424000300f005850f500c821100724007030321815030072700040d66980101105006a000003076020382c0d072a4003103852 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 387220 1250 385970 385991
    0x603050d0c02010507020405070e0a0303030c080705070201050712030f0212060f100f080402030a02060d0203060405010b090a0303080a060911030108010509010501030c03020d020109080706020304170601030203060105010c05100203010b0a03 105
    0x900c00501c0310300900090b01401484014109504910f03080308441c100700529040c1d074004240d030700b24241c5c000c0e400030341c0f108840d000d040e07045800c0603001400791420900d41151a000070f0103503c2400802040d03031480300c100d02003052113031b405161100285030056582d9024541c2c081a100d4090303c0d00c0307101d484a03035414047ca06d085a200403100c04140c0354466203ca484c501034406400051040c0c5e00341c01604064401642e400c4010700251140d1070f8016100d003040e00a10045500503046040529001c06c11010159244850703002100e07410b2820b2101c3d0307a601c550445c05046680d000300400e909080008540101300400785040e500140020070042d5a200086800c1c0c40d0280300242c4603030036240050004d800e082400b80b5043d401818500346c504c0c0c1e0f404000c0d00d8000c00b5801400107130004a03040c0150428500440455405000200b20a5046400080c3c682c08103114590502403034002520400c80c0501001c003032039891100c119200d6075a01d20141242e8055416400001d01d031420b03444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 388470 1250 387220 387227
    0xa0503010203061c06090203061003060c02070308030a0c0201020403020d08030105090705031510020102071202011b02071404050907030803070c020109090504050d050d0b0a03050f0706020f030d0f0608030d0603050d 94
    0x910400c0700070704e111044079140c0720380e90b2000c2c03070303c00152000d68681d0700c0c02001d42c404200050051465220103520030b4510709007403003200c440307909030401c64010400800c0461203000580380c1122a50800140e02e003100c8409a0081c495030740000e40000300c1e2241c07003080c0041600514100c034000d0b00d200c0b0b0248c3e51403500f00d03203501c42280e00307041c0c40103007208116081c01c0c562a001e0160105000062070030000d91102c0d05220131100100c0010b079100c69004400030095003212035138084074001000610704268810f400e804001c0300e070a001d540d80b00000741d09030904110504c02980c00251941e660300381907600514004210f041640841c040c0c20000405240703600c84c1034800c50b0064080c0210f0100c40300211000d03400440c2c030325001504c940c20071103d1307920b03c0c9805004503c90001404a960340603c0b40d030030141154445800c1d90408400c44210149c08401c0f0303219a0000f00d00014058400020350700100400d8100c140c0600c008105490b5120b000c1c2c0c083c0c030070b42e40524201e03801c608540000310f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 389720 1250 388470 388477
    0x606030a0507060c02040b040f06050102010b03010207030c0209070512010906061b02010507021302040f0801020306040c030605030d05030601020a060e010c02010e010203060a0b07050a0204020a0f08060102010908030f18030d06050a05030102 105
    0x703105a010210070020607118a5480d00300751310083c0042030800d4080006010303503004c90a641c030b00b550340e5842008150b80910030240c450400750001d40c01d04a40d61030182070504250b03c040e00444c0c440d40007070101d6114070215820703480500075101095031107001100040650380034103c0401c5480c5558024a41c00841208a1503416595149040040e50901c214080c00c04041e0344003640034403000c00e5118412200340f025000071800140c480ca4442c0802041d51543c400704024907107852424080d82c0c8001c9160142818a410000e5817902e903500101c0c80c00b60550710103441c0340d00e0441100c18000041d004426003004a030b009214a45030349100500701d10054400a6104400c0042007002994240c0a007000b5070082d401d5800c0a203035038001c60241c0e40a002c450307001030800008007100139005103d60340c012101f81300811024803a80d032005241d03c0050040d20400d28040d001564000302885107411b40401007065944070700001d403000019200c05d0040a104408111002c0384a04051007038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 390970 1250 389720 389723
    0x509010b0301031e02030304090b040609050906040201050307020f010903210e07060c0203010204080706020601030308010803040303020a080904091406010503010f02031003020103020703050c1501050405070203030702060403030c09050a0b0304050606030a 111
    0x4481c41c69180d0795480d0b0000704c20460006980301819511400340e0360500280c8028284400042480300c2041c0410088aa0035045000c0e00b6140209210941d80f0004415500950a003010396070390301c0710303402030789007861110704055a9803c0c0001c2c0410107030f00036550075840340a01e540b2201000c4115004080e1210b46079070316000c1c0c2c400c0204008662003036641000290020b40014503158454844504000c0301d5080b090150b0b000000400426a000841500414583d0061400c250541c1da0094480c21030482c0507040d184081349000d01a0b4079544846c40d1142d10114a842c150081354040d5241e0109209040c8294039014000c410340b58680200ea01c01c001d01c406101c3d10313505680c01034000790407021044c3c04020090102106080d01000095407122410078444201c0d0b150030100801c0e03480c01041e02045400c2481440700d6560006a140d400c5a030605004c951401d4142041703507000e80544c4002c0e44014055000110910400025070003580100103840e415036980081c141e507040403030300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 392220 1250 390970 390989
    0x603060402040c090302030609010501060905030a0b06060a030b0907020601050306070c03080610020106030803090106090b04020403110d08091011010513020102030403030807030f0504050c01080601090b0702040908070f03020304090501050901 106
    0x380042c03038203500080c92140ba80c01d02c2c0c13041c01c3c0c5907000300c0d1501c682180e00c4000c1ea036450b80140001604075405c14020301c0200d00601110740c4130790b0307000803101c0d0181210b0700814010980074501800381d0003034205080b000d01204801e02d04103600a503034036003e104060090082034080345200d44203111449810f9016210a80951100000c6c48012202101c1c444119541c1d088044000788003140214040e40004002003411420000d1040032609610504c51140e88108800c10003c4c0100c104002c1c10401101c51009404c101e060142092081e900600c1d4450320300203003214000c0d0071006190540055000030003c40c2c3d5990040d404c0301c0c42109029015900900040001034070402c00d00c0d61100c05403901041c03510402d80210107441080d1400c03038691b000080b440441d07580c4141855031001007445c00c080c00c285002d1250580b0f224940c4081e001d1030b1118040c2051120050403210340315486030801d214444907080c001e40340c1e0010700900c01d8080c2400000900c9191950117141131301c10900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 393470 1250 392220 392233
    0x50109020f04030b130501090302060f0a0501060807050310030602030a0207030806030307020102070e0702030c010603030e01020609070b03010603020901021203010902070c0f0308090906030c0a03060608070602030c030711030a06020403060b01080105010201050603 115
    0x204c800303102e02c100900801c0603019408450000400a01a6420a034880d800808031340c10000b07008645c0580007451034483c0f80c600001000301c9503010281c0d42d0024035505026aaa446804040d068140c1d1a00090881e030700010902018903001d9004160072030003a507403444140c42d40e9042503280e2103900001b0740180d000350340922020840c60580d0381c00003118011030b0300e441041c00410b402d44082d1b0b401940440e400018104d800d5805005213a48503213039002030f1240314101000d2807032900060040200701a070202d090035051b4001c0140c8402800c428440d91f031250303900d40c00318001c3e50098030201c2d2424a840710000b248000c10f081c00054980c0080c5050800400e041800f01248008000543c10311411482c070b4440c0d102c0301000c6001d18000d04020601500308240c10b071500d80b048d40f10303000b15401004a444891804410350f0a4ec99000300c1d03100e454480c0400087c030308951001d002d00400c2c80010000104410396000b440054400e0325100b02c142c0c2d0b60401613081361381c119000c540640154 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 394720 1250 393470 393473
    0x10c0e06040302010302090d0f03020106090b01030b0a03080306040e1501080c0102030f040e0a060504090605070906020c030c0d0507050a060504060807080105090f04020102031909090605060304020607030302090604090903020102030703050109020f0403 110
    0x3070f00036040d00720000d0701e107520082c23580d140c0b20b8a070303070318910b0543c00751350b540d00d00340300c44400760040c805c2c81c580a007000d105030113280c004200607a01d40e101c041c01290003c00495070b00d580780e170080c010010f00c0c0000c071a00d28642d8038000101034401e22441c1f10038480d091200c1e00d203500101c2560780e0350011800c514142454140d07c1450148001c100d070b80c1ca036035103c00201d0b00d070340c0f9441910715250107000c00180f240751080723001e0310040706074000744203551090035040d04580d030018140c03601d09005d4038900d441264900d0030b0791800340543c10255010b403410300c002c2000c2d03a0050103801164071039a5440204e4640010030340b5042028001c0a82103030071310b4001071821407081080c0f038009106104403840e106071007021a40003e50030140340d0008803d05420003001079a806840e01405c0300319240c41c55400c2c40d0f03001031401c1c4a40c8000900303040e000b02d4810b00a030340b000141d400500804030140f14210151400078002e5204940440100e417501d0008551000e1510a4030020320a5030065032400c2d085 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 395970 1250 394720 394727
    0x5010e0f06031006060302070b0117120904020909070503070f030507081303020a02091003020306010b0c031b010603050307060504060f050108070603020903010207020a0b0406020f03030601020a061109090c04050102010c0e0604030201 102
    0x1c111070303003511560381076103a8a5514400c06000305403541d00140c60710303101d2502502d92003040c0d0040f91201c1c1a0241d400700030401051080c9030020744100b070f583da2030020700400c01034051400410361100b181000c002ca003d80104c0114407828240d503030710454280d81c2a05600300c907030640c1c2e4140003c14045c0001c00035500d4005241045001e40103c030641d1405074009a40b10008940364907260701000343c10021400c040144030f0140608040c09800d0040708640c89644e8002c0e24401c6254050b500315500c4494029842030000e941c0100c103880c0d07110f589041c11005003805032021507950b8a0200540c80c2c0013060710616042e102000e01902200e40341000442c0a5000611102c0e0301d55420099900140d8035100001c00500240841d10f844300e1a2032400781c1020150007004002c0c3d04104108141aa40881d8590505a00541c00154050b4051a500b0540240340000d40c024800381309104481d4032000103030040f94800d07030080c015400c2910085034100d103040f03809a000b01c410701c410b0005600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 397220 1250 395970 396001
    0x3080703030e010e010c0e030a050303070507080706090302030306100201051332070302030c060a0503010302090a02070803040302070f0f030305071101020a020d060501030c0506040b070201080408130602060609090105010e 97
    0x7840c0c082100005039416030308507004020501026076464205080203500000400c0c4034220413009460381c0e944a031103e81c0c5070310000b0a030f40b04004000440710100061741e01554a0b140d0010002c005810302c0d0b2801a540b175000ba035070b2920a0700d001103d4501e80c2d00c14022144113942e42405103841c6406540c443c0307100d03402a034503824212440c01c41501030009642d00104c0343c2c0104002444a185540107260415034071300b0989024030020031840c40d5081d000b40480341120741c1600c03202c00c2503507070005203c02030141e44da004280744030002c18070050550015450040c0c50707600a00c603d84942d188070300a80f0302ca683c44001d0200e2028046100405d003440300078040c007207043c0140ea100222550018502170b1804004440c4156038000500901070783c11400d4000d480143c4059203030a017041e502100302e00510b0380090400900c00009000c0285090a0350455982c614817100310586980019441c0e000441e40b040c0030703444540005038204070500949048a10341d81e99824942c0714280d034649083c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 398470 1250 397220 397223
    0x1020409090305070c060203030108060408070303060b040303120b03070501020d0507020307030203060f040506060907050f090a09020412020102010b03010c05070f051203010b090102010b010c020a050d020118030602030711010204030c030807 105
    0x15424000080c1460540c012203520a1081e5105655072101c1d25002003901c000d5000207045500078030041c0000032000a50b2908070380c104882c90348800342ea01d000c4003c0c012642091180d8600468004209608140303074040c0411081810300c40c1030a01414141e8030160b5203e01401079008050b02d6007001c1c003074801495140d0014050f5521607440b6000320703160400c02c0d6900810002810108418014140036550704480d0880380e0304114100041c00600c140100001c007001100c0010303104039941d0765020103d000740420740c000c0d91034640d103081181c40c151521000780c0c00755080188507015440d040c82245d00b02c9600f034488034140080c5458070034100e43d00c64001c46d054414690310042486101000c0e600804903c58019501c14500c0002400d64080c18425414801c25511403001617440a018500740e50b000d036134001180031180012152200b82441c0780ba58001000f0010051001c1500154450300da152a449807441060300000c3c01c0b03200e0340c031010300100c2881500b84000b8980000905006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 399720 1250 398470 398473
    0x2090402040e0106050a020d020607020303070807020c0301050411030c03010501050d23010203040b0106030c080405060106030c0302090402040806041106040e04060207080c030c06010315060e01090905010615030501090506060403020f090702 105
    0x168030340122400a0b1004e03000b1a01280d404070706c04c1c100544c10001d800880c800b83c4050309280c00c00c500b01941c0c07404060058024001d2030303400550340764401c00005201080080091001c2e040070b0805404a10050745400d010340940c00c444621810b0500850781210301c0601200500d094589820f080000e20728031000d070044610300000748183d000d0020710700950054a0300d1046500d07010307000d4111840d003004a000d00c4400c40c1000f000c00e101242e41030450304241401315040009080480c0284140181c5551061003c100800c0e03c1100080040c4a18465034aa000045525080121900070340c0300e004661840100000d0001e01e4903009030007080c0c8641c0945082c00d170410398084c11074001c400b8418042d03000074010814880c0d4540910091042d0110421086040203c8841212030501498100a0319203945104001e004d5002400900310052100210465400010043e240a200d44407045041c00d0208000d0b142c20f208660071203500900091002c1d00200910050b54002411003055 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 400970 1250 399720 399727
    0x705060a11070306020c100603020607200307080105040b010b03040c060302090a12150507080606040905150405040305030708060102030a0504060f030e07080309010809010b0a03020d06020c0106060809011d0303060402090402 98
    0x2150104502c1000e10302c11400541c60703e00100849281c141c11940341c109645c00d01000700b02580350034003201c40840c1c0012401e0024086980b480402404042c003030b035098401c3d0480018580010340c080ca011303a00c1200740f0191642d0300c000880482c001600d010345841220700c820411240a0380c001c2c50a010701400302000150f5078038044000b4510000c041e94115081d004281d4000407601c10150f2201040c1403021060402c0030108405000754015040c8896031000803070720002071b0212403a10804014014003d500c0c2501c0c00602d50741082c0d80140200d0300480c00700781c80d90b001005491402815a0714a814507241035011101041810080028540c0e6840d50245541e01400320034080c12854000b035078fc0e00c590000040842200621440030740e413521810203025581c419030401140d0701260780d01000110703803c2110007845000e950001661800c600012110b40021840c0e200301c403440c00030001103209107141c8903004a01c4922581e26002000018103900d85503015040307403580907000508 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 402220 1250 400970 400997
    0x7050708010c1d0102010c0801090902030304030f03030b0102070b0403080a030b06070212010e1002090901090b0111030a08060109060f021c03020706050c03060405010b041203030b040b030615030607050406020705060a 95
    0xc641c2c501529000280244000d0003a0034040e08032291036600031720080008541c0400c0051104d03506000d2007003c0d41d2115852030946d5800c20503140555001210810007100a140240060241c08140c5002d4000e0704400242c102c0c601e41a60102c90300003400a00d4a059a01c04400030101035a0003030317000b1810711404c000760312404071400185044900015a807080341040d186403000311510954010300402284c202602c0703009080e4111500035001154810b80b010040c0c410b05401d003401651840081004880b06a00524260250a080c6c95000c0340f03d48480c403c80d003202880c0031080160b03102107641d07014900c5880c442880b0202d985401420544680d03100710a895094403914001d00012040c00110301d001d03c01c450040c05083c5105103003070b281c80075003e16107101c03c0e009014107a0310300316440d054540383c000c2040544002c069074001d1500c0c880d04900d1b0682514110b001c0e20900002130b1020b800391040b5030556203a50018440036183c0004c1115903841030343d000c020003489030b20310b40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 403470 1250 402220 402223
    0x201050d06081603150209030c04020904060b030405010b13090209040f03090801020403031101051501020a1506030204020c0307030e01020102030615031e0906040302010b0405060105030408160c080a02040501080105010803040b07050708 103
    0x188a1080e8460090f48240b450804818801e250410158007520422101200e650700143c043c0b042107003a90051b8441d0b0300d000c001402003110717a01a0301c0c001030001c100030030050194041d4405000c210790300e0b0b03004412083c0741000c036a0014402508030002e40041f9021803903941c40d07086441c0c400e140165580c1d49070f240041c00d981095004078041002d2014003524101e0a002e01030340070007100c040251038070a01c40002d40d26042e0700030117442d40b0030301e4180030714072420343d0400806190098003e564a8055558031541c0e907000a00940c009001a001c1c0202584103000300ca00690340103050218610317015030740005983c405848010449038034110b10403880d28900409218070311a2015010f5450541000381c2034601c0801200d00c07442c901820070206a800000303491300280c0011002c1d864103503a00078000043e0000b01c0240c040804020001004d010001d0f0500610703100b56418001d50740da40c0181402c0c2e40c400e00404015400a000500554072200040e082035070045041302c90305c2d50742e030b0300c3d45 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 404720 1250 403470 403483
    0x5041202031e07030b25140903010207030504030b06090103020a0501030c1101060909020108010e0408030106050313020307090f0b04020301080601050603091006060503060901060f020d0e04020708030109060e0702060705070201050d0608 103
    0x20b0010703411611041051001c0c1c00c1e8050b0340710000480b00c011003a922020400c000344035641190a2100344030461205906801c141d520360300014008560701e0380c55080240090304180f10840d02c00403804001503617401c000000074100c0e0390190200440d41e003082c0040d0b01030054040d21004020b0070000b81da6003040240500782c010056480700154070f0740640001840903c05070050030b0b08420385070500000440c0381040b82d0464400d440d0454494036a500704001660310304001a42c03610801c040418003d036039070f00c901ca02c42080a010408140240140000da010034441c640454000d5030040000f410b1150003984e0001c00b11040c0c0d0035002102d2246c2040700c80c0e5030060b00004001004001c1142400604c1a014102905001e0114140d07580c0003136890019145030300401c0b07655030028500351131b00c0c1c041e5188240d000081c81e480b5a11950540010720701d40c8524200e540e01e11001c11714607400852242d00598080d41d40d5803501285400548141e4032280f4440042a03a50200080b41030091015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 405970 1250 404720 404773
    0x70803010b0405010f08040b0103030e010509090702070906050301060302010504090f02040b0c060601030b0103020711010c03030e0d0201090c06050408030301060305060a0b071a0108010b0105040905090102040504052d0103030504120203 103
    0x5858660b42010001002c2440300c5075605c0c24080d40030140400b04040400c92030441b0350500e0310f96020280d03030700100e90274081c2c051295000420f0300c05010005802003035200c01e80300d019204100340e42d0f44204050aa525030f100103030100c0e90812062000420341d400c03548240402207005850725070b80341100c84003a40040071590050300080107100241da0b0501a590b20404246010f41c2004242d0b101c0035100c4603a09400c0307050000744200f2408141c0650403042501d18010251540d80a0f1075102034080c243c00700c0304581e50308000380c01241003800358064070280d034411305c02036007540e0030300350103400810303001d40601e52140810700d000985884803402042250700c25441800424280c01c0802e400c0784060f0014070b042d0341040c401000036684503046d107046403416040828962100c0c00707030314024401e41d000750ba0004c1c140f50400c41c104104507444010490041c50791005400200080024960280030080009004200401c051400610007100d102e0000f816612030b0f0341e500c0860400360b4040d501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 407220 1250 405970 405989
    0x8060106020606010c020609120c060c0f060609160c05070b0a03020919050609010c06060801140402010206010608070203030109110c0a03080a06050402070213020703140c03030117030c0a030f0507080301 89
    0x51200320780c18459503411050030709007400e0910560340041c0d62402100c0d1010301a1400c0006140040c9080185e040c68a0020708480d80d41e600c80c00e00103845403034401c0d041c1218030542000c0340403402c0c59800d07588645808806401c0c020000c0c0401c5800081600c000c0d940b6107d007010104a102201c4000c1c43d00d2103ca850050361901d11006105c111450410303170356104580c0240400064846004458038410300746840207141c03aa40c42d044000f00060340021142d0340ca402080025071200c00b003594041d9000341c00722100350703a0300c0c0801c41c0c405004803000e400681081c001007041c0395458001240080003130380514100481804003030b1800e0b40d80d0bd0294002400c420138000c1c400320320300c6000b01806058909500e0600c0503004a04849980c0503418901035001440d2424107210301d002c01c80e00d845820300203640317140d60301e20195260400c2c0a00c26283c0c41300b0003080c54a803c0001207840042c62003000d0030000c1c865490940f0483c030010988410b00034200072400c005003c0c100114081e048928 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 408470 1250 407220 407233
    0x12030605040c02010207050705090703020d0e06040605060303030103030c021003021207030b040b040908030105060c0309030709020705060703050103120309030203040f06030603060b06040303140306030106030611120903040501050d02030604020705030408 111
    0x60800042c0c824108826055920402c0600042100415401d050320301c1540c030414282c4454001710002c2c4200424050b076680b600c81070500308800450018051806540c1c24000382c1c071a8070805131240700c2807000401140c1c0040840e40141840d41546182d4080b0781001801d001d030400350f81d00050350485030100040d80d5041d8110040c41c0600c01c00341c41c01002e83d003c02030070100350b448500c0c511042c0070301449920040b94011441e2410400c481c02d0714000f40560310141d544403100c0b0b01941002504031064024080003602e0203100b80300d024102c0e41c00099103c4240c3d50554258000c2a40c0c402c154118002004003045516089512400800072558002622880c6040c0082100c219914a0341718080402c010000710743d10407031100007202003468099690f107400340041c0c0144502e038030061180303040152816000441c0b10280c41c100c0120580c480e0342c0d698920307190783c49120b107002d090b0100701c05010b440711404403507001d1a40300501500040c42d000003038070351030302e55085076111403000c1d4002d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 409720 1250 408470 408479
    0x2030601080111090f060405030f07030309080303040b04021003060509010602031201090203010b0a0f050705100b0906030a050303070509040603050a05011506080c0403080702030a0c03050105010609080303040816050703120306 99
    0x802006004001140080040d1480800044a01c3c4201c02c5039070f11840c4920400c03001a40e07120221401040c004046503854280b900d08035880d12080d200c281e0105441c4c101c0040e8507030b0048101c0744180d40c018611080c9035200c0d82001420f1385942d403070701e042654405012a0325200c009280b0b0107044190011500c4d80c180c0300600b0704090051f00014107090062004004940d042801c0d10003444260500705d903000c0715600c040301c06000c0c9032405885031003404025411800b10390b00c00100c410041d644c1ca0030640c1c40406056842c0c2070b9002c0188682e00c20000240c2452044014015070308000704007140d81030f80c903103c8500e0201102c4c4184d0700c0e6559096008078601c00e044401000701594200a421440c08880c066214090352001034410714000a80302c0c21035078107004586805034804c00343c048168aa0805038020300c02401240d0100d00501e5011030b0780079000040c0c0388031f1a8020003091408a01e92f43d040142d01c8040021100c80c032403c0000b00001c1c2050b400d0811041032a43c0000d80107142 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 410970 1250 409720 409723
    0x901020301080f0c0d02150c07060306030c050103050708070806040b0301020f0d051003030503010608041401050403020c03060108030909010b070203010e0f010b03010b010c030c110a0503030a030504050c040203010506030a05040302100204080a0203 108
    0x1120114061580b1568400806403200550032071170035011240c20b82200c0034650444081c1c403a030300c41c803041400f81580c04242c054059206c0400d0780d02074090100582c1d100c0f40103404a038070079128580406d4907100000c01c4036105005060307001e40d0240c800324840f000480486d081ea01301407450b070903011010480800c01422840703003d60040002010b00707046440c0d40c60141407844180208010401c4660003e0184010744040340140c5407c00c0c000c008d03074602801e0003504c0f185580d2003180300380982800041c01c1c06c400029551840c00052116070715134a841000c000710b03070141c00102c0c5c265480302170328442c00000744a1110620f60b040004610078000104041c2194018542103051004441032840425407002c0400c1d10b0650241e0614001410354000401d05200781c1d02056051000080c074042caa90302da00038900461250081b2a0140c00c542c0400090340030901405400000c20300c0003a050000c96000543c0150003030058072040c410682d61007059a00980240e4082d501402216045090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 412220 1250 410970 410983
    0x20a020f03010504020108070507030207050904030806010201060603050c0a03020702121504050106050a0e04020105030601020a02060d020a02010b03030403030e010c060603020a030b060f040507050d0c0e030105040b07020d050708040306090602090405090102030108 115
    0x1401c4000300403d00e8194006803c0903005407103101007041c04a00c203010903000700031040250200801000c0ca07460549401400300b0003c445c618015400c0c036400080a40c0603003d2030f402400040500c5080410280084000303411122013640e000d92510b25200c5212000d0103004e0308021201d008000700e10741820081d00f074945503485103008041c6044208030038080c1c03955a03070704281c0c24a8503a54076207640c1c0040b4903000b10003101a5000400043d03203252140075500910040180b80c000b070200a06090400d9182d0003903200260204401005104413580316010a14403a0700c100d400103004c5880313401069031003d0741e82045840070040c01c14054140340400c1c04803100d040c121802e005515051f00010520301800032500c50b1035442d2444525014000c0c1c1000d45c01c0f20000d4003c01492419007824a0180c00c152810070150140c2c40d000e004481c490811075071415001440f05241c01e1556507603000400d06907200342c640b00d509208166641d0303500d00540703000710103003000580c495042522079414042c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 413470 1250 412220 412249
    0x3031608090706031d1b030d020604050d03020708040801060801090201030501080a03090b0a0903021201051005090c070b100b19020606010504050306010902030c16030309031707051602030f0706020a02 88
    0x10032404100490900282400c180d90542c40e0101d5105520482c94481c0c42d040d20150035140580c0310b400d0881c1e0381e880c25030551842c08030304444e0102183c40003a81c49160940d00a009a080301c060100d403180a074000301482441000401d151650b150102c03400c5886580010009035100c44c5c0300c00c05c2d980d041c0070740f038003601c0090043d04200c0f0f160fa0703010f84203840c0c51060150343c01c0b01194104105004c0d8084034015a00580f10055100c0c8503c00107000744803c40b0008040c800340e603c08505400c00d40c140c5403042248101c801d28142e880d03101c003030041d00020080c0042306101407011503000e124002034480441202c00b401c651009151019091801c0100103074100601031004116941d0b00050107411184200780041e0f6036201c002038a0b58a214007400f0140700d0402800c07150030103a00da401501c0c16030081d5565080c40c1030b03c00e1082c80118056400c3c60001d1418484442801801038089650324070040c1103650315007240070342c0707401c02102c2e52003080541c100c198041c0542c00c20844036504070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 414720 1250 413470 413477
    0x20d030506010203030402010c05010609020f030603070909080a030203090109080403080307080108010e030405090a020403020a0b0d0b010302070308040209060102100f0e060c04050102070b0a0c020a03080903010b03010e0c1005040b030702030316 107
    0x103240c0840000d540317000c020006410804200c00007810b00c6000e40c01a4043c0481250640d5284512208283c0b19030007a00c0980c000e22400c5c0300007401d264144a601301559011040a20344500300004038060f4202a040301a039550b41c03155000082c8102000f000298811b03203403a51245803e15025041c01e40591080f0896410207464010202c404000c61b4140d4100700e554082035102c1c0c0b04810f00074080c0c0d4100a402c05901040400c0504800000d09900300030424103100380d0100000440a1303000744500200800c0070500400c00620384a641c1d49c0e4032050620485110800070401113007910075039a05017071081d94580840b20004003d1184e40d0b4000080625585003031304c0c000000350344018901c1110145200030980e920f011f880ba2030225000c3d50000c018541b07080c0c49091901d01c0ea400a20307907a1003586410607240050406015070125210144d01510714002c800003408a51030a1042003810480204000b182080d4020302a44c001c40c1070364002c5807245801010500d10508410101c1d090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 415970 1250 414720 414731
    0x6060307050303030106030f0b03061302090106020c0f04020a0302070204050406020901020d050403050a03050906040b0a09090501120c1701090b090606010806030303040b0106050702040b04090b070306050a030507030209070c0c030507030201020d03 108
    0x260b4400008881c1181d00610340080d2050045182e40020030340c40c003105901d0f014220030310078814070103180030030402e000b2989400e803a42d03240b009903501c4040c01038860300000e10214507507141c80d1036400380103440c400382805885d0208550001c1d080300d0045800f2a26264049020300c00f07940e0401c00101140c0123424080d142034110303280c080d5115450311008042100c0010042c1c016101c0d00e00f84d0b40100481c402180d02c800e5890b50140102140d40030b140c3d602483e0100024148044a8100c4d462036080825002010f051803a01c0441c40140000c0c04183c0d900c1e8940d0348001020303403606c1889004500c003d0480c0e0f0500c84001071003904047d000b14400e50040c0240404101600d035150304485c0c05080503681d40b0303061320100d0f0141100790011a44a480c00300c42e141400460310310f003842030000b40d03801c00066846104003c41034450380005131041d03005400a0005080c20044280c00059034149400300714402d0f599210451a10b40048915801c100010403c43d43c04000c0400540b2440c1800d020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 417220 1250 415970 415979
    0x60a060605070602030402040e03040308041a07020105090d03051e03040b010503060c12150d08090f03010e07030f06090501020307020708010b01020303010302010e0d150509030403020a091104030201140906031806060307 96
    0x86010b0070074080d0090b0b500201060444d5605d5000c4200301b110032007520b07140ea55908000b0302c540c00c02e100b40ea510f410310010042100c2a400e0842c1c3c60268161506410070300e009050090900d0054005c40c10322408200d8030303102c550810b103900f00031044002030b01e943e4a49403078000d940c1d0806170300c080d02982c482c201344030604003030030305840024400c03802d040d0f11941c468074883c0202c803070641041e80200c009203010090050007002842c07008001e03528080a00d0348103080c1422a02909000051504010002d200184421024109072405184049108002615158220385c0182d6184026a100d8241080302c0b8001b80a02180c04000b40041c41c00c40d803454001801800150700c0301d51081c04480b819008004140348c0f1160012a150000c100300d14288248903540d600500080c0d1103136003404c000080c00c0000e401030400c049641140d950510389198019a0003009081042c8020030b41444854000e8a43c03034003070b601c25000c8000d00009189928500c2e4240304001c0d14181c041d4001040500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 418470 1250 417220 417227
    0x90b06060a021005040803010302010305090705030714060405040204060e0a0b04030209040602090105070b010303030510080106030c0905090a05060702010203010e0a0b030604031101020903060906010801060b03070912020103110307030905060a0606 108
    0x650024054902555403500c41d04102d00b01509801c035444158134081c103200c2400b13070040146060780d200b82c80c200a0b54482462145e500c1105209140e0b050348502c074140a0000c03441905601c059001d05003134203143e04c0e00d0025003a41c204d40c01107400100b000c5841c5450349441c049510003440345030307186860700341950082001d2090041000e051203800240b02c1c0d50a174030410131520700c6504916208450758680c500240605419101c90880040002002c01c84c12018811300080ba0f0b40714540c0295103280102d0706002e0503008001c6405d6004107481000031410902c0340701c3c812402030303000690301d42c1403d01c0b2007006000940394008061401103250303040d03100004c1494200d070301424040302460b01c034002c01e4060f119910a454150190310180b01500c080010f80c43c1c140e44041000f4405c168076882105500c7c002203401d0701c00519440010400e01c5003911500ca100780c01894003080b003e8000e5000c00613035005840c000c0010303035a120a0010300209108103508108803107014882c00d89400c0008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 419720 1250 418470 418493
    0x1060c0510050403120e070302010306060201020a05070b040302030405030703030809100b06070303050a06090f050103060507031b0e01020102190203030a0b030303060a03060203060303090301060303020604060609060510050a02010e010213031509 107
    0x4a00c0035903420100302458010700300c94170005680901071028581180070580c40f4140d5110490109090100c040340d070034018003e03544807100950b18076003808074a485042c044440540140c095000811001c40d5580b014000080554000d44902042c2d05282c00080d19011081114030203407490104e240300207903202c0044940c4540c251070003140c0c6031507041112000303015a6210308200b0345011610131040d40325405c80d60403030f405020308218540e200e40090b0240c030a1061580c10b9804034038500d405e0b080c01070484110484d4180300040c100b030f1207000a11188000700c204c0700050b03170022003000440e52290081d0840d0007003c3e00954218100000459014006800001c000340e0b004000500d0b42e840c10001e89002090003002884620707964140652500000d0780c065035014204070380414030301c0c4a400391500b1100b000c0c044005015808008503001d03003296002c40119500c1e94100d10b003485090029002d00c0144d204246a00c52035480c1c24040550040070803061503052100c0d8802003802181003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 420970 1250 419720 419743
    0x705060a050d06050a140102011401030209010506070303140403031d07030b0106030f0902090106050909010b070803040204050402010203070b010305060a0e010e0717030c0d0302040e0114030a0201030e0a15020309010501060c05 99
    0x1948450200b181c0c000642500d80002d40c100a940d140090102e40d003417107002490b682a002002030300200084204100c42c24000650880341b604010815400c1000060921901038a000110100d4020a040c2c00f010300b0b640a40000340c4810901200c2c01d082504400c0d554240c000610901e0301c1d55461aa4500c01445072000340755503071519510706901c982041c3c0400d0741c010300c42110b941c1c440e10090501e4000100d0540100100000071501c81051800c48082c07507000664035086079941d5003040080c0400800c101e046000c00e100e17210004080c0c0c400300713010750b22a1015005914181d0304400496004c0855a00c103a81040d0010668201c00300705101540d59106091701502c0300c0003544c51842c80762403105001d40c4213002c00d8140050340740d800b61081d2900040d401c59103903a22907480c64503801000c0640c1d8140c110900a900540c060341c8800d0150192106581c000c910703a440300c4203036240c8909444541c0d40c0020400511007000e100ea14003412560820044420381d60b11004d65a40340c4904 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 422220 1250 420970 420977
    0x2040b030a150204080105010501020304030308061005070f0f030816080c0309150106050301030201030f020702030606011815080405060105030a05030406080a06050409050c031011090402070206070501090506010f06020705060a 99
    0x84892a503181441881c1d04907030030408041041d81e81e140740b50000d502a10945106510b05000869a90301c080f048800b169055a1a0703070180d100c920070000803c403000c1e0710400b131010070802c2c4000605904044200640036500c140e10384685405e000d8800e5200a200002c015115202d400310030383c00280c0107400c0018800d131103840c0da841519280c1741131b22070072a1280303098405e00002071450b4001c0055050ba4401c0e0780038132402084d101c2c12000e90044240c000c0d41600b11070001012544a107813034070090070502100c1e0340300350303615501c1300c42c03c51207404c0d240002860002084140704082214900620081e0028200040c440e1030f030715124011030203181d0070003284d04e000c14012042c0d0342110340070b4200204108101d0705180b40c01a034403158103103250300030b014004070355020940c0b40c421300c3c8415140c00d800919104009003004000e500846040382d100c4d10030300011020030024452507900380d120300d00074481941045d040d2030344000168400000c55012071350610803912101c003514412084e504 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 423470 1250 422220 422231
    0x105031003030806030102090402070507150309080405010302090103090204060906031403030603030304080304050c030607091502060601020601050103020f0c03040e01030213020306100f0314040302030301061d0a030b0c07080403050709050109020a09030204 112
    0xc0c00640644223101c49282d03c580042102e4051010118821080303410585c4280702c80794a216094042d10814a006004100244010455075000e900280100401490700284e15129540040d044510a82105084c075036039106c140304000c83c04644e07a41200010008504520701030300001d969200080c001820b070303a80407005c41e08014080185c0c1c038180400605480031072400407001080c00b0001d200b814806210111104a2640007203015405800c3c107030301405040c0e0030200150041d520111030b424940800f008010607102c414070140010700841ca003a43d2507540340d801080a05005584c02d0344000b4810010700c116543c904000c0d184503401d50421070000a2a0242a0010072080c00001c061050310000c0100301540400114140c0e00c442c1c490240d0901d41e030418600a0640c515541d410400249080c00400c3d0104640303a40028620426440e140321070343c2d50701c0349070041d9000300d03504e9015241c2403221400a0040c0c60262004550440c14a101000b000344101c45070300c07000e40125542e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 424720 1250 423470 423481
    0x1060e010908030406030b13020a0207050105090d06050a0902030d170402040914010203070206040c060903030504050402070501061505040602010501060806091602070503030c0a060501050306010b0703050f09100807030b01050310030308 103
    0x6507050002800d1500607603031156a0303000068050f0000f0305c660791140140d8a01d6640d10170891007139803a210001d40c010244907003400d0040d14281c0c4900f0010794010381144600c40010514000c0500c00d0070400000b040d244240d02c141031400003900c94040c00d024002000d8881c0d00c60359404264801d4046801041c0c00245040a03650b80a016156a945500000070065410340005005000324031a250603400e03950b8079482180d5176049400300600040040108010910b045e030040e04009004000000f60319507107005510001c0f00700218100419030104041000c0c5e6020301c101e80c0140b4950804800c3e0b40b8112000403040c042c000e003900004a50413113000710503442086250041e050180c1226528801c030100740c0c3d03944403001400c9030040d08040002c180c0d41000f041079170485040d2906203090140c3c65400303035515000364a0f58910b4040a0202c0c100e242d03190182220004203d03111048241040b56005059444010b99641840010400d101c2103884d11102c2008070303909460401d00350784a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 425970 1250 424720 424727
    0x90105090a0e04020a05040203060109030605040221060a0e061003060e07080601090608010e010902010c0305070f02060406030501030b07020d050414010c08030906060109060c030f030b0d020306010b0306030106050103110301060e01 101
    0xc4086440e0050001c0740e01244410715030314254000c1d0700890320119101d69076030400060b48000c480c0940010f418510803c0080d96680105410510003408584044150703000f05800e03440709441524154051014048421014410000700800b08405059a40380500d4207110021461000820850f03403001d1840d40000d0501c10040503204410988055503915890310b4041c1440340910415941780c0303542c007448280c0500c5820305055041c4c4480c121024252029215600900b10035130b008d482e14104d110041c1c0c2e8100090005e0411038034001465411418034001a02c40103001c4010340d4800201420403d801005503001ca0703411172101881600c550f030040303d1100c0c5080c8000c11660300401800002c800c0170030b0003403182d1300c01e0b42c0f1802260741e9282c080f0f1782240c031400c0203804500e041c200c000356035109421002c04500046c00c0c800020000b58003092800310241d001840200010042c0b001d68502800340400400c0309107401e2000f000c0c01c0c4007800c4144010310913602802268030610107183d01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 427220 1250 425970 425977
    0xf010201020c10060911070b010302010c020d06020c010f050601020a020904020915060403050102070201030b0105030f0a02030a0e0a0501050714091503070306030f0b06040507110a020907020f010f0e06010602061902090105 97
    0x248001543d1100d50203480c054013810315030150303400c5030b820190280b000708500f40603122816000580742d00141d19580066910a0810780c05a03000340201c1007a00c0411183e0004080304294040002400e0801c1c0c1558030031144081d00060441d005440d00c900540d5071980e00740d401940440e25070441e1303211104d030b2250207884a41f070281c02050218000060000c1940500343d03144c001e880a0050031f0444004403214403003102c143c519805414045012048550f01442e840040e0070000103040070311a90243c5810f03440001192569107500420030010b51010050001544529069041c503e60000013850001c541505031070a100210002d6a0740344607800010046804c4400d0400880c01d0b414101c560382030840d50503018a040c5000720303919a00c201244112042d1000140140070b2a5070308202000e10003901c1e10b811449807201c5000f20740401c0c800c00d10b040740c18010000d011400c0795401130a24005074030020031364110004100d000225800c0c4001c4860b50800016600d5400701c005030303601d02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 428470 1250 427220 427237
    0xb030708011509051008071202010c0b01090203160203030601020316051203010303020a0302010b01050301050a030f02010905120c01030f09030203030f1e010b03061306030302120a0302040302030102070b010509090309010c020f01020102 103
    0x1820400140070b0001403100401c00e940f0090b00600c00360b9910b4800702e0b001e10f2540b040c1e812039404184100301c030400203442c400e02c07079205240ca03004405894460541455080c0c10803205264000b081c0301e0741d0044d140b0700480c41c0000340060b500790b20304000040d40ba801403880b035524004503403060204004042c01030310b46400d03040018507160b503101c2c10b00a64903400100c08030095072806075043d40541c003034000c2e68125500103101034119415030303454001d041c042d007200b01e05005486002007210303910070030b0b009002c1c03442e40000c00c0d42c4c9510360001020f44018001c800d09403861f040b407603404a54003108072a0700054402900740c207500c88030035205186413400880002d101c0394400200d2812540307001940540001c0703a1800d40080082c030100100d58140c0b1009001da4003c1070711380170081d0041c0281000000340d00b0f0045c00d159607600860700366170010404590080c40b1030b0041c0401e16000340d01d02d407c8510380c0300a5080c6080080060000114035102900c641068000c0b99401e070702c00d4044550b0039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 429720 1250 428470 428473
    0x9140102040909020102060108061005010309060209040501030305090102070902070206040b030601091701020306090702030307080a0b010504050409140d050f0a031a0d050604050c0103020a09090513050303040309030219050102030306040b030708 107
    0x40360354004010040143d114101d005018001c00011080c20024525010b4400c1885c0030341340340d01d800f00540003400b07003140803030b0340c01d400740000c1c0280c1c3c5c0c5510403940214080d07103a0659070542c0000080c200006a003068280a105010640141e29041c0543e0300703441081420b20b541e0b0b00c2e820016501242103a00444030120b40080a2244480640180d0300a60302500c3c6100c00e601c419406903101d000c01c5640500062880c0c000401109181d00700541c00e41040c1020344c60913031070b00089810703601d11030760544072030b0785004282d20020003c014410f03a8003036a150031410240c0710b01c0c61000030320440c21040c0405440b07141e41e22080465005084150398001c102c014040c2c000d192483e15000304503419165070003403c1c0c10b94010b5001e07000b11585682a40c0c0c0380c00d00e8a0600c072504009240241c102400c041c02000f1100000303008000541c0124000d442d008030f80784c03a500c10441d00542c0900d000f400fa00d414039041080d83d80010a0f40c1d001102105c02080e1952030f2008285050f62640c01f86007a0f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 430970 1250 429720 429727
    0x603010b040e0601050304020306070309020406050307080102030108070501030e07170106050409050d02010606110a03080912070507080705010504211704090e01050a0213030201080901090503030106030203010501030e010c02030a0309140102 105
    0x148a2840c0040c0121624440350b15659aa03aa0055850380021100650950000c0d40084e084501c40d902c1500010310061000614544820110340340600940000c852030703500000600104004211001c020704091805014986507070015544490503403043c2ca1941e0f2005001c640600801e40250000d414081c004000741000c500303215640e02c1c6080a8000954a01400403a032284a060450b4103154024000c24000111b030381d0880c1c0e400c20060500782d00f070195000810150740c1180080c8001030003800148005801c0c1000e50f802c00d0801c2d400a0305010003040f04100f4041402e40360704c10007406622201140806040c07030b00e09901c2c01c28a05128500018000c18001a0340e80410304190308500204910f6442d11118001c9200d0000d080204548440d02040190b100d4032109500110b2900082802d50300c0340d9030b076480d541003030b00303c400844d40110051209581c184110041ca0003102c0091003070a40e000f070080d46038494140d01a007010748072001a018486410382c1d0310103880c0180d0003150b9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 432220 1250 430970 430979
    0x3020d05070c0210020106030201080c0c03040305030304080304051207020904060203060102030c010c0201020a090e010b070b04020112020304030807110604110f010306030c090204030c05090705090105030709030506090a03031104080307060209040209060301 112
    0x45800c0561080380700700040f815135009184144681c0c0141d80d0b060f101c0b00200d07140d0440c00aa01e4000d03580e0800188002c01002c400180300b880034500481c410b1844036200e040515200b8244102c1c610401040d5400744503540141c4d64800181c0d801c41c1c0c022900590f2034903080c004034214030440c842004c2541c20701501d14901e650560042a19a84958030421800c1e02e40c04e03c242004401c0c4103c4000c0c040a0124201003817480f48441e421901c14100b19240c0312444030000d050341c004440c16070114103a10204040c0c0e0360410303041038480140c40d002e40020b00e4a5604c02c8a800f160501e51400b440e004101c0542ea0b0b4001d60004000d503030048418a03400d075035480c11002a5000e80010ac07540194001d00280a05110400c40e0082c1b90700d807600780c10102400c004603044c1d000140b4280c1080180080080862407d11480d4040c0c0c075068068045a8039600700a01929140c2150310010802004100240b20010042d50b03141d075444500542e0f0348182c6070018000c0d005501d1a180e226000000004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 433470 1250 432220 432227
    0x30f01080705040b030a02040203070905090a020301030204060b030403120509030903030403060501080f07030209010e0408070c060507110102061003030503041a010b03090c0105040501090608040204060b0406020a06050108070503030703080703020d0507 110
    0x1412992150200d5150320b480d4410f000a035103c01e12003030b405a001c0c58102c0014a895006942e20015a1404d460382d280c2e140002181c4400503200070284540c000014800d505040c0502c401500700c08600354074600f131941c1d008165102c041c500d0030320195078801003a62900b090048555180e80102281d8665441b414041d004080a00c80c80201e403003241c0700d800c015079000c02c40ea000c07607400074185c46080c0e1801203070840703501004104803000c060402241e8009a84c4c5503014001c2d1030f855a555442c1c5c00030b8a41520010300e010a101d065500c20b030300f049000007005041c01d090741d9145c0f17001501c0b0340f2a0310780181035a481c0c114010412040c44c0010035038050b614007840c401e02d0a0003c07550b072148141c4c0150303614072880c0036860010394848030501080d401000f031290041c0c409403000585a03516510f070308490b00160043c0d4010b81080581d40e0601800d4010345002d4604880580245440c100c0001d43d41d100d914030007014800c6440018407910f0290703050303441210392850300b88004d10f84010003d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 434720 1250 433470 433501
    0x20a0b090c010905030c061207020a05011406040b0405010b030a02090102030705030c060403020d030603030806040506060d0c0201020a03150509010e07020a061503030801060f020d0302090609030a0b01030501050603030a0f030b120303 102
    0x50b800291107030800589440d000560329600395000e42030b107240069004640300c01100082c54181540704046803503002035002d10031040822081c018403206800c3c003008000942d10f004181c10310980c10580107000c0d940d440c00860707070080340c200c6005a49800c2d000061b82075000d076450291842c04042950706032503034003090061065110781e0036960140071040c82602129010300015001585040c0090b0407402c0c180d0000e5000000102603505001d42c103422240ad45154240c2000140d40105076102c6840e0103004118149122105181035203040401140c5030b110144944017420036250041104a8024807031505800d400a409000d83c82d2052044403440c121448118002480c1300e00004413548507059859171008a40c0c05003d400003d654110003070f410056800344e04c82c1c0c00b002318118994003040400c0384c40b441100e1101c41d940c1f46041281c00c45d600188900e0182e0801c20a00c554598898070031301c6400707914200000e6120407000412034003000c080f591582c2d440000103010512180c0a0746 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 435970 1250 434720 434743
    0x307050c010c05030702040b0105040b130503060603010b0f09040201030207020d0503030103020306060d0b0f060105040801020d0605030d050a02030703050c010f02030109050402040b01021609021804020703050403030201060e04030504050402030403020a0b09 112
    0xc850300c200c515001110402c094403400b41c500c0e04103014000061505400c807424090301454003074200354840c0e510318200d6002c0c0e240b03850000758942c020096403c09100090780a10210000c101381c6007902d02041140c80c04441040c0721f42c142c100080c046a0207641900d80040e005080d0f0b2006030141d02e80a50350750310a0000303900c64412000090031364078080b440500d400341d01031380001d80c0307459a0511404201010340801e052000c20320000c6840c10091015042008401e24046401860a002c0c503007400c0d401c200e80700c1003007410815092250307000811582215814986595901d02c02c20300c043c01800104d85410681d800080009070100307507604814011402124200b04004800b8016a070b6211684404001d04280482c00c019050142c0c1c003030413a201030320240c2c06a508610000500700d0b48030400440204501040c00d10501d5424401d140203804e00680d407420a041c540c50240080c001d82c451607100e690000002810980300740010300c245036220902503901c0c200b2005440c2c8034107400d000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 437220 1250 435970 435973
    0x403050a0309090510030204020c0109050303130b06030703030203160c090906050604051608010501050c03070b010b0307080a0b01080103080c010207020a06050915070f0201080402030a0b0712050703020a0f0302030a110705030705 100
    0x50202d4503aa1a21405004103001710050028a1840d8240400b80d08001c45409407550303200070070710110700244010752254501a4100108039001d2030061704868014100d14002da0180c241400001d070000216100899142e200001d512080d01d010302e134900060f0001c7c84000e040c0354500040280c141c0105014070001c56042c00780d036440c560100c0400482510b0303138000901d400b00401c52035000c1c03030003030240740c540c0c0c0d00303484c5000d1003034442c410041c50070780c03110750f6407200002000003280d403240340160800105034052146040b5000000c1040380c040c08003078941d08001403031003013510003513040340c1e04254042c11070303000c25a0310341c0c0c003030255007045001c4d80c001d11090112003411084203048480c019030203150f1031713038998054004407034043c4020022601449007104440202c4c614403403543c820740160b50f031442e20842290704c00090b00c0c00500540d05050040c80101c00c0150480108152040d513468016107960b5080f071000e02402c14400480300b03110000800605100e0044000c0a07403a00890 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 438470 1250 437220 437237
    0x90a060c020a050405071206080607030506030604050604110d05011415010906080c0903030c070e07030606090513090507050d0303020c010506150f07020303040504020c01021b0606010c03030f0e030403050a03 91
    0x1001039034540c44040000350300c00d81c461001d000f50b14042c2d008940011003440c003841050100c000070800c442e40360b0040c00d81c0707034440f004000d602c55140c000c0320b50040080d409001e65040ca41e48440d0b80b104064001803400c40d44d09031641c42d80c0c90708000c544510b60003400a0141c040d041c40041096030055454204d0030000541c1e0305041e500610340c140844400d55a40c00780c50790342d143d4441c12600720380101c5c1d91502040001d0a04400c041000c04050010351050700f1050900c0f1001404032109503215405000c0c0110081101c1da803074604003000307044202c0e0049052056271a0280c100903150f0032a0360700080845444080c1a40350f40601048689517008025a4a40c90100140303400d144101143c041d40c10071416101c88d007050040c1a0840c07016040340d061944600000307099030401664101541c0d4013103044900c01c03480c1d14208a8620505008d0441c5041c2400001c2115403441c001909160300d6040c0c07000880c44540c44004803d40f990180da4035944c0b0385c5000d686858504c407080e170016407001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 439720 1250 438470 438479
    0x50402030c03070602030a030b0409060903020304090b04090b040209060103060e07050405120705030a12090806040308040515091b0109030206030406020c070605040803070201110c040e0607030f02030c03040605060a090903020102090a 102
    0x140101a40c901e60000c47c186a1054000c8024150800040390401c0d190b80d035200000c3d00600441d40800c1c03117a0080c0d41c8660401511a04a400003070510f842142843e0303203078002c640491012500550143c44030622642c800006034080e00159203d6680b98040000301300700c25900c107010300217541048602030b80d2000307901c00042d601d40d100d000b0030350300d5040000c4000024500c05001186403200e810035181160340c0b00103150400d5001c88050380804c04e08810041004400d00400468075a400403e02003401d100030103a540d4a190100c0410100445280000c0e683c0114041402158000c0806550346007030302e0010f000e0342000c40e02450030b1003000e0010800600076410b40d41a554800300071400d0110640044441070500a00814180141048049103071210300800080c507085400500d1941000d282c01400c40d400c074450f00c904a0700c18002d00690440701c6003180e8205ea0094004151911458002498801203602104080b890b010b1a0b408041e01074002d0462003400708e990300a2503594 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 440970 1250 439720 439723
    0x6090b01020c0306010e04050f07090506011106040b0403030e0102040801051e0105010801030305090103020d0e010510030203060c04030209040b06040b060307020a020103060e0f0403140408070905040204060f080604080304020d06060603050402030c03 109
    0x20281001d9261300482c00501061500c4e08209601c14061402c42d00c00c1c140301c043c400c0c14102903400a2401c03e8442c8208110b95070822868a80095108003c00d001d240c9503c854150050241c4010105a250711282c03002c0c9500f5010f940140101d50001c1156051024843c00b40740308090000c8c2810f524a07000103055070003025040d040743c0d0541c54091600210f040110029440b40c0d00600c0340316030302c10715055816000d200d0140f04079069002c0180307050a42c0100f6280800042850403038070000c001c2400140c40350040c058001e42e008420304215242d602c00507024041048600f500850301004001c4607a50010303145003420f000703880810080381c40d445d4864401c04112508135800d1140c1c0c0206000901c6002d00c900380c08010314513541010703191452581056a1075101c00304154a4000b4401545000e120b4000141a030386103151119141040d210340301c1e507009201410702c580210000301913460348480710007103552162041200a448800c050024032007660168002c0c4101c00c1c1194003403d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 442220 1250 440970 440983
    0x60e030406050304060203070302040906060e040e0102040501021009080705030a05120105010806010512070c05030f0a080603030a090303050a0203090a0906030b091501050f060d09030302091201020405060f03040201030b030a050106090b0102 105
    0x41e0b5102451a0fa079601c45801943c4080d01000415500300f10000b5401d03000e10902020f400075549440c60088000100000e07141e410300034154991041100f08100d80c3c00084000e0001c120100110342000380c0e05240702c5502920002034481d0000140fa504030320740c003000410259009003084010b50740c8450045801d900201e46103404200c082200c0e40344184903030a103a9100855151122030060700350b039541d04581000391a09003d41010503218081e9403c801240c0c2c0c805402e034011410140c410b1801464004c480c88050140400080d441101c1c0784240119110954098039003034105e41d460740303090002c0030144429078010142d00d000c2a00c002000c15045401c102d18030007020703140d0174081000038140228800681c400d10421004001c140ca0b801a088464025240141c42d14524000d1180c0034407a000e50f14510f0f48100810300080d03503034074240c1d86e070102c020782656201d40d80ea20040e0700600600c8182a81403040942d030000304401508284282c0305460740c01d12010b00c904006a030340d840e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 443470 1250 442220 442229
    0x510060b07080304020303090a03050303180105040507030303020309070902030103030903030e0607020108010b030703020403050115080c09090303010303050904020403050307060902041d0705040b010201110307080105010906050414010f020f03040e04060e0304 113
    0x803420080030300420320050241d40c00c580002c05984c5050000000203060030741c1035204448a420100c104007040c03080c100304e011001001c00c0244000c0c641690340c3c988a2a80c0d000060034103074040702155249408000701b401030002480119039075610380c1000707807980e13078140f1040700023a016541c031030805d040c03880c10f50381500d6044e180c94900d40d0804201c0d031000e800040400c01015800e100c0000840d01c240180046c04a0302166240c1d00c50800d54200d0030020f01c1032515025400741c2003480030800000040320f0449805152154a400c008400a070183c8140d60020340903110115205c02400030550003402035520888040007815480b402c0360900d065070820100854018010801880c105034104e8080c66405200010710448851a0f900083d042a5903c80004416800511184d41c100140d400904100e040c860304261034400a0544600e058001d18108583c00c01030ba82014000c000a0904140b0031094030b80702c03030702c0c3c5002502d83c1c1c1040303406139002401c2c000082071003c8040300721019203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 444720 1250 443470 443489
    0x5010c0e0d060c030b04020708090a06020304050102030f0702030106030b09011a01020111070201030509160b03010303080a020304020a051002070b030106020f06010b0405030601030201080717070305010302090a0506010e0f0a0306020a02010504051006 109
    0x140076a495100040203860421001c2c5a02e0794240560759440f440205010351161210030f84034500c0c0002e001c1e1240703283d045401594000c00042c486680c00100751001041081c0600383ea549040c80400d0240140b603100410845008080c000004d806411650030440c001024480346003034200120b007a00d42590015108050802642002d9480b9800165005156900701c50034411411040003480c0200d900c00d03d00014080018810543d010550300c0d040444a0015800d5040c580c0020300715102c0c520907141310744407405423a4079560080c800c540050041001d01600d030344c0e545501030340340c100d401d0410110f07015034000441c3c1c81c40384400f603d00b034403005402003055a0031a401582e401802074600da05024030403007000b00c41300340c46080030b100b00f1042d40e000c00c80394558410f200d011500600502000e6092404124090364840841c40c407100084075500c2034002c1f41d10100c1c028440300c1d00050046030000890750391058054002c14042c9106404a82900304001c90010445190340a120901d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 445970 1250 444720 444739
    0xe06100311010c0303140403030903090b040509010b0313020411040801060b040305030d020f040b0705030703200c09070507020405100f0602070608130303020912010501090b04020708040e04030203040302090408030405010c0e 98
    0x15486200042100fa100e4240002d00e1840a0000001254111011400642c40303064400426a0006044e0001d20036483c1c5d842c2481d040c8400a518a00140230380d540325180840010b0360f810842005910fa10340240c010020041d00e80f80c0bc101030380c001d02802d103440d800d211000940340d48000454084a401c81c0c00f440c2852001c1d005040a944060790592211005000120320400301200414185204100465807028245000341c80e08210b5103654200803811403a41c19044004902c0021f00030b0b00b00c1e00407903150303500403060300c060081241c003a400c245001c0c104030200001000c048283d40459915000c282e940c0c00d000c030b03568102070203044002890003011990000e8006142c0c603500e8441c0c00c000d41450341c04004945044a400070188081e919072004211080705481041e100e0700d13090700d080d8a441445e890751552440349100d0308401205c0040001c00b458424410340f805154001c0949066003402e0800c280c0e9a00f0590b000e42e5194648405424128004d08480c000e01c40c2c06001c4043d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 447220 1250 445970 446003
    0x20105070602030702070312020706030b060711040509070909060501080105090c0604170304030b07021c051303030e0406080f0d020607030c080105010c050a050708070305010f02030c030105130603060c030e061003 93
    0x6034201600e04801d46c0b141080c0480090106c074828029488a03038000c01640d460400010241c5114140b094010310040220101048121480811181003a100401c0e15215088005d00c0d124956000480c0b49140804400400019400c124100c034480d60080c0601d0b00c2e03991140d52640310440308180c0c4800c080000300a280500010750040009a030181c80c100356403a150010500340c200c42c1030b00180c0013070900140c0411046036901d035002d494545581403209000c445c441a101c0c03400094140030b58071002070110341e520381203407000d828441c0c02c2da20f1040c003100780e403599284c1117100750f0094040d950000d090b01c1d10030704c140c00ca111410b03900c4079030a9180c0390040d1100e4500328010798450041d15004400b1610410900d0014800701000b40760551840c180707a804c50310041e0440403050700400c2407200703684202c02541d0540300304940e9085c2803840280030500501e050380c00207021504001c0301030b445540650100517295902000c0c0c9508d80d0b41d008101448910718000100071584c00503840e907 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 448470 1250 447220 447233
    0xa05120f06220f0c0504030302060f0402031b04110403030504050108010905090a03050d02070506040b0912030405030909060102030c01060b04031401090312020a0314010e0703060e070206010302060904180b0402041802010507 98
    0x402c0c04900c600000301410811280c2003655409020b0601150707001804204255040192640c8004a0700d080300290500e6400070740c5641100703080901c58150301c1102416981ea0741e0003007015048101c002d42e503031a60b13440c019119030010707c03442c0c0c04075450100015500b440e03401418070400500014060701d06440d582030342c10b0f03000549100c800356400d1001d000064410088140140d00840c1c0d0040540b600c0325404e8646881a83c40031a01d0b0000e000f070000056000059031340514040340c0e8500e04d65103120040f803660103010303c14441907003001c80004004004800500030b41e0f014407480a13002496850540c262821032100500141642c60201c06076206540507114903c603500c0e02151110807000f070050348417400e800c1001001c1208091224140d00340c41a91b00400c07140040c00205e241c41c03080603498110500c000380c06034100241c10800c4d40e60b00d921900303004041c030103a2140c485d4070f0b0400741d4682804840481c040d030310b08999840590403007000d1110080d4169210341c6071001035501c00c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 449720 1250 448470 448519
    0x70503040915030204020304050c0406090b01020304032307090209010306090905030706050402060903010603080903010e01050402090106050705030d14040201020c0f060a0c02030102040305070b03040c0e04030c03050a1101020a05120f06 103
    0x81142c100c84000800180d0b11030004600542c09540203120394102202000111134465100c120120b02d0203805000c42d0b60003000707071012030307800c004950004030048416030130f107120745140d54040e40145072003c1016100790b0b014100400007aa0200503090300c03100300108a030091003000d005640280400c900140e02074000561041c8050105414083c0610210342543c00e19001152106c1010400281500b000d2040c03042142d6944000d0020b03003001c0d0081200080103000d0304040100010310881400030410850704a600c070054100300309503041102d1101c0c2c101c1590101d0041c081c0244240062400c501c1a446200300100458908001e8031001d444083c0000c81c01c80e05035401740700c000049801403100000401810400c2640d038036040c41c01c032a61a6030782d00301905c0340c1c0d1204180004650b0000d005010b85034141410307a03542a9640703082e1460720b65915015130f9907000082c4c4051700e950040180c0844c5c0c0a200d02c60650391590264007892840450311360360030009210050360702c150391a446 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 450970 1250 449720 449741
    0xd08030a0b0307060207030302010b06030105060301030201050a0311040608070e03010c0801060309030c020d05030301030b0a050405060403050306031005010303050901090602030405030c040c050705010903030213050405060108040204050604150e090607050705030409 116
    0x60810300c1e84010a0904030b10354403110150f000b03c00d08205050b020300400c800341c81d0481e840c902e150f0410001541d18001800064104070010a074822050b000c2da0004204110b40140f20b6140d031780d1440c00500800085454500084042107155481d0905002c0c04041e040c0e1910f40c00e00300c0e13090100440041010f00416010408498807400260725100744918215004601541d500d41c103504002d0074410700540f8454046182c0790401011803c0840d40a0b0070540c50720f080d555030f0b101d0304002842c5c20008101080c80500c5c0000000c20560000e004121010080c0c131a02c890503030300c2d20309036220b02861003804d405800c4841c080b0007501c1e0544c0100090840c605019041070350036243e141c00c40d61030140032408282d00080449030203112050f900001c0104607001d11003850081d00080850030040c2000380625110b80100d050b90f55160406803050308403ca0000031701d6a15482c1c42c003d40c0042d41c107840d95000d410041100c4503c0780b000c440c06290060010b40c9410301c0c10303000d01c0041c000104d2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 452220 1250 450970 450991
    0x3030706050a05010e16020312040305040b0a030b010206060301020903070b03040c03050609030c0705040501050102030a0806040b0d030309020a0914010e07050d090303090203010b010e150309010209190303020c0603060d0803 98
    0x40000040c840d108180c054014030100244039810a642c2440948000d0300304c00340c00303088604401d00160300004561682d0001c80c10745407552280d01e0140c405000d103030088042e1410110768416402d5142d4004520346500342e003100c3e1700341c0f40d950602d8200d201d010142505504600303004d04ca54092440215041032051244022041d0f5030744949080a400765080c041715080000c500c0c04455041041d00c0c0a854112000c00c4154034040001c2c0d5284150001c1100340141e10340010000d94642d4000000d0700c002510581500401d49002401403401c540100d214802102000c01c40c150180300d40d40002d01c4030109940ca41c1d09102c0e6081c1e030b41000900060400c2010065141400502e000e4450510320a0b14042100d45443c070401d421340c0c03942112641000311664030404295190301000302d032610001002d9540781c8a03c120140a4420b00c40c1d032542007006150b94181e03580000e024001282e000e94240c031a090701c0d20b410032034148015a403456021040d50054004104010300558201c6019031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 453470 1250 452220 452227
    0x10e0105030d21050f150103020a0906030504020a0b040605040501080a020703020706110a0c0311030d020f1902060d050403050c070e0f0601081302090705040f0501020105010b16051504080711100207050f0303 91
    0xb8021040e613a0480343c1c80340c2d01c08003009100804480194049414009081c2035080c0b141d80140140890002d10680c4205a10780b0046401e54031140c1c2048040c00f4540c418076942c03600e500001d07009d03511500c00c3c1800200c0102c0050506070240c03082e1010958180e0140054621f04801141c8080707051110813014020440004001880c04d06a0001944200800108818040201818040700200790030540d000300404003044000441d42003640d007000c0755403040b41f240703074004a68075024241050501c1c0f0300e0101404213040c0c00030040c2085031050300444201c25140c10980942060540b019112100140d0124404d076000300180c0c0d50004414940c044020707000d400154400001303452070f0000c5200003070140b108422000d030000c0507250a0000380000d525146441e12140301e04201031a49046040d070140c00c1020500c07080d078405c0704104c5c1d0362030a0305050520003116800031104a40c155a80c21415046080c10560100035012580180503030900c1c1106201d5401c500c07461076980341c007080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 454720 1250 453470 453527
    0x2120105010f03120509030c010f02010e0303090f0111040b040902030a0905030a0c03080105030106080c0405100f08010b0301050609040308060904050309060d0207050c01140a0e01020a060204080102030708010e0105030d 96
    0x24030645000300b9242d0300c0b01c0c141d5855810f010385458a604034820804c03000b00052030103900c001602854407082807030030349528a00000101d0040921001482c4940000001c1c4910b041c070001d42c3c0188404290000c22600d00503a200401c644254440c0088182083c00204480c1e02c456010f1030340803481180106001ca00796071a541103908c43c00c03c00c1301080c06030303c42d6014943d00c410964098403046d802000618140070740385545038501c0303200600c5180c03903074009044040c1c110007040003421415280360311640c86404403400f03844210703c49030081d0700e800000384040ca130181a075401550591183c81c49512100c09128030903078010000d684610080211030202e80381d003070051081c440840e10058880035549011400c0040140015040007074507000304030710904490490384e064403c0d0030075055014460006030f081c068a0314004d047c6920210b03001a030340c1c0042d00150312480842c0c3e03a91440d40e0302c0e1804071780402028011640c140d4080c0b180c0703020460007416200040145d05e08441c0000460 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 455970 1250 454720 454723
    0x3020604080604060b0909070902090a030b0c0a03050702010b060a0c02010903080a0302070b010503010509030306060304060e060103060204090b03010c020304090c030204050d0c031403070b04060902010c0605010608010f0501020a0c0b070212 105
    0x365000385081c0d40108200400d0140303903c51441c1c6100c0c00c644202d694241380203099a1002540a083c03061030b80084d2020a540c3c5405e00d940065a00410381e0aa07480d00101d03c1e0015000407504001080c01e00000a002500c184a2070150840c018203150621407454811130b03c59000d075a00300d0522810070000300126012002911042c110b59601603941e02035803500440c04d00041c4d20090181e818602441803045010068075032000041d60450703242e41e610f003841c001401240c40c0d0b84003d8000d100c00841406100c0d0024825a44003440038882c0136804400d040c2210301c40c040903401070308240310520010b10b190704102080021481c0141c00d00d41c89000046032441c0708401101c80405c82e010030801c014484480507444020a8003950410b011912a8140000000d0004120b1585c07114103004580c001e201480e5000d070403c40030800c641e168407010744000d1b000c0c040d0170b403088020200028551303c000350140071241d104034100f441d40d1030000f00c049039410800f001c0760b02820950f84003c90000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 457220 1250 455970 455977
    0x10302070606080606030f01060b090103020f04030b04050105060a050d0b01090203190501090b01020d050f07020d020103090501020a0305060102070503030702130203060609030d0507020a12051504050f0d08010f0501080f070507050304030206 105
    0x510300f02800c103504108003094607081c178060b4241940c0e410910108002813802c42550003251007800d01503565141280c1d20851840b0700c3c2c1004002c440d2590500007800300c154000c80c460b1009a4214003440d40394000c02c50205a2602e0040002c0c00e000010f00525841d43c0203140c11070401545003c8959600000d8015903000341c06c90b245060f80c031a1002507940c2d0400180328400032a007070107841d221442554020906c07078004042c1c09014141d18010440e4803c0d4001c0030078942040003103456400b0742c000200030741005d031140c40c018032130003101244030f28010003141d02c810f034010140e810b04000165910003942008001d61703440401444520403d44007404602100000b40d9100f542d51071480c410010307900403d030004901e20780c50b000f13074400040d00003039205403046501015185a40e00e40c44c6c020b192490720313000060300380074072032400600035040640241600c07120f002140740c441d00c90300119100312040300c4401529500002003000385005100130905240514152450180c81c2d4001c03d40551 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 458470 1250 457220 457229
    0x10c05010f09030e1503010b07030c03020304230a060503010503190219030302030406090b0301120f05070911040602070510090e07050403020405040b0601120603030f030213050d0605040201020607020c0307060e010302070606 98
    0x42d1038218030625840c110196186255004c1c010317500310b5041c104242910300070000c00609000c0e14241002c24503008100f594010071900c5903c041041c0341220082d010152180360600410038007001045550090b0156030603074001900900344c48600180c1071915200001c816a00400155045000e4085809401c00070f140690011070b0744501e0a4401030028a0961040081c0c80080c00188901d01056501e032414940024450090803000d0520b60704044065109141003403401483d0848145148068011210241c0a4943c07070350b9100240100f141c03141c5d28100004140c01400c1c000122000e03251034000c652840c07c42c1c180b503143d90100381194425282511942124401c0202075a8441400d054001d0407840910040380756580c080d1244a6105407030b0241340c0c010600f0209495643c16100090500070a0b0003000549410003200520f4240d4090740140500400204124000102c840e2000d0f4003900801c10989001000c03264200300c18172890415808120b03800c00b2030840e0140c0320151 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 459720 1250 458470 458477
    0x7060e07170607030b010804020402072301060f0501020a08030c0703020a0501020a0206040b070c0203070e060114070b01150503010305030703030203040201050904020a030608070f0605030115090509090703060605040506030a02010c05010f0903 106
    0x68090040716460188010a9402010305100c0c9025481e6031001005410503410f650141c1c5a02852a00100c0c6c8900713100c0c1d03c103c888c5040070700c0c8480c503c1504528200c42081d89001d8070320b5192001287c4400c0011000361a001c420008208140c0038440100040381c001e1041e150345014540c0c0f61800d90b88120508801a4406404e000c203104031626090b40111490030002000106070740460740b601034500c16400342d20514000100240d006005444500302c031100309599405d42e40c40c00c04803500080c042c240c1103480824080180c00d018804490503250004000d40c1043e0701c0d541d0440181d48020000ca04115003441490320740c2d02ca44c0042c0090b0400c07500c0109859003800b602924228180d8001840200345038000c1160f140c001003200e042d00c1c0c5007200c0d10f90043d0500016551109581e110030741180e20641005004000810351030182d91058801380102c60741e41d01008107070f842c1036400035415000150100010b40c01000c00d00319492107040086420b00d81c03140c807481180e54204059011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 460970 1250 459720 459749
    0x301030209010609030302060a0e0106080a030503190501060c080703020304050a090509061b0706110403050304030c061202040b0a0807030b040507050a080604020301030506060d1a0c0403050f1203060607060e07 92
    0x1103103401c107280740c05070240e8500344d04041e2440e14029a5100d0180851180f5954ac208802c8500c201303420101c00f07003100d001126030321042450000e0090707000700e88080c80464107681e4000800315501519040390a5a551010211040c2d103550308680e10000003202584010000091140c0301c03120340500400014100041d14a80036000c1c0d410804020701c102c0741a10b00b0550f504a20500341d054415484d0040c0001881c0009604509050b10881d04003500300c1c44080760020401c5400c924100903600326075182440d981031203038503034164001d41c002c51501c64028844244e80320b11030740742341d1303844148d51502141112200001c07074100d030001e0742c003503001a000081250000c0d800c0703d074140c0c1085003035030704510f550300d0b64603415255807002d0040d6101d52003150300da5052240c2c401004082d02e914480c005058280304244250b9035000b40720880c0e440c020152800f07066030020440b02d0710b84444012071855aaa80010000a80c0c0b1401049031403560f116500c0d40b5014040004201422031500c00001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 462220 1250 460970 460973
    0x12040c090b04051009090203030903030d0e0f0303070c06020d020d090c08012a05070201050c070609030209060414070e060c01020c010207060b0d0302030405010c020609030d0804060c020c09041103011103010902030103 95
    0x1e440c00c12188601407800e24003031180e41c10104031000100c40c0705c9080040c01c0c41e0180b0000b0304603c15039a425606101c003013004052850954401d01d1001c5440f0100c0310050580c100c0c007612400212140d50202c0c008591840210700140c0003840c02201c164801441c0c0b000c55256070040b40d4040308282e400c003c803800d040c40a4002445580035031151091030807200c00c94003491301c0d86407150300c3c156810407201042d240c0843e4010000d61740401440815600200e0700c0c2c250051030030b049880281e20803502d007408501c081c01c003031003100d5280d0140d0700d03604c190755030f01c0201303880b642100841940c0100c0104140002da000c2840902031304d00582c8009a610302d19801c255098410311100d95200341c540e08403450000703170004115804c44400303082a5010120b06e0001807254021807240365014010b21820900d000d0b400321600344118030034542080340c0301005404994030710030311503403d401074006408a008110000034940c228a07000700040fa650650044515064100f0b0b8800d0382d085401100500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 463470 1250 462220 462239
    0x5090c010201020711060c0a02090103050303040b0601050306030309040c1b051e010e0a0f03050d0501060305040605071b1103030403080a020304030501060b09060301060503060f030105070c03080105040c02060c030a0212040c 98
    0x56606001d200a500b809050b0f01c44545100125500d603204140000d445800d9900500207880011b070020315490305580d40341080c50b22680200e6044070400360342c3c2c0000c0c4081d0301560940c1e0003032710050021410400007409000c01840b41c0d191610034000520400c005c42007444120030035042c0b042001d800065030f00e055008035600b004c011940da90f4146100740440d001c0c0003501546258100c205000c4400e11818195400d01c201180187e145060200129000340c054010070300880c4540e0302040560340b035170801c4032081c0b2140003a004402e045d900d000c022880b007158100321078200809803440c140e66a581d04c88264449144900543c1000c5410030500000b8807940f07000349004140640b07440384a500050491005024078000e001000c000305d00a501c5600c0041c1190300301030000c000d5030404107005403104510a50440c001181000080381c06d08080c0074054071440c4039001020ba0b0f44486003a007402d6000201000c60301542808001c0550304d01e6071040f4002c0b4001c406001d5481d0500c540170 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 464720 1250 463470 463483
    0x20702010315060c080d020706020d020405010813020604060509030f01050a0c0801090501080303070c06020c010e01020301050f04060b0706050405030705070e0106080108030306090103080a03090503030c030907080703050307110f06030405010509 107
    0x10500c02803250b80030001d064020101000782c41d07200c1620b40d070301c400c580344200c003e024003040901240d00c00b2070700c5205070885034020400d6402c00d80320f1350a9641c558040c01200c0306d42140080d0010400d000810140d4002c1015022070700c0d008040c0d45c3c58083c01c420322801c440c42103601c816141c2d215041542040d8014000350f000d070019000030302c0b0359814040b6003a900d00c400f820031700402905640075402d22170540d05943c20480100d00034000c030960034030160b010350001c2c00740910446180300211194036041c85120700321002842c42c80c2c20140180c07666802040005c2080c2d446001c208901c2c0b00240081c400003011300380600004101c0d505010004101500503002000c81e58010414005582d840c080901e045039130011440d81d40d00034018040303001d4440c4001c000d080344804010b0280740440b14001d10320070b6184000b2034111507500c86e070141c0c1da002c2922018040c0d030410000000819114a0400800c2d00007070520a041102d1101058080e801242d091700c05965600c10301c18400c50500c0a03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 465970 1250 464720 464741
    0x9050304050a060f080106080403170406060501080a0902090a0b0a0503060a0c030f0506031b030f07060c02031203060109030602030618010b0702010201050907060905010302030a0b0301020403050a050105010602030406090b070c030203010c02010207020103 111
    0x13007411036080b42c0d40503241c0d81040c0151401c1c008050300190406100340b01c480c120a1100c4800100c5043c030b450800050422801214003040c03402e40080c20350340c118412049000e0b00101102e0260701c480316030070000c00300b00362001d40142d51800c0c0481c1d292000c00c000c501450b5aa08001074081c21040300408480d503c00011030740600b8407040c400b40b6980001c1600c41c01c005500c10103050242200028644a90b415402e1210f0050b920001030150700716030100c0d100c90081e026108140600024207060380b0080341c41ca0b01007000070030180b0204101b036014550203500603098490798098154082203402e026445803004042c0015290110359080c012150401140c42c01455000c0c00d00750042d1490b00300e802518105940400054102c0e10340307400c0700140c040080e0086546a40700e05100b91140742d40312060754990300b82000018040e200004032801c0382c4d80c0350364511800d81015442075680c0d11a41c3c1c140c03500164602e012004d6034080c4124501442941c00043ea40c0c21180f0015080d10803003900d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 467220 1250 465970 465977
    0xa02100b010c020607060c0309020909010915020403031403100302061303110907050d0207020303160b010609080c0303030403050a1110050907120206090405090a0503030702150901050907090f020403020409050304050a06 96
    0xb04001a241c1c4002c3e04c81c000d5002101007100300400c04c08800820012901950040502c0305000000304190f103c103240c64061f44101440c0c01140007000180c0c807642c413000b4002109402114003d42490300070b19000902c021464254a503260002905504071b20010107400ca5007440420800000e80490107040ca02a83e4903210b45c5000703903015115000c0e000f00220100d400281040031036609004603030030a80240080d0120a80608103a80110424040c8902040c8103520103c0d8215000030180c072150030007401507285548950382100c140d00030144080901021110100c0ca1030428081c15800c02051000052503180c0f010040e89008006d030300010512540c1c081d18009600c2d017201315640321200f40c030040f0f990384a801845141c20406803010305140004028044c0b03003a404a0751a4200405031214446d640717542401500300c0300c0c180c56201035a80404010088028190032030b0380400d014440041c2801c2e5285c0204090340c1d80c04c03408440c2900001024084d03403800000100241060b80f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 468470 1250 467220 467237
    0x3010905060609100906030f020f06030906011404020708030702060402010e040204050a0504050c070506070c020102060105011103070f050c03030408070504050106030504020105030a020f040306020a020303060102010c050307090e090a02060a02100b01 109
    0xc603900c1d12a400504424010043d80000400c0360940c04003280c01804070901c1000134560702d040c42d9802100e401403c034401c4c41c4084400d4007074a05041900d000d0107204002c0c2c0096441c0c140d4555540d0010809503070069001d11031107020450040165100e2200c0c0d40140410345400d1000404a20942d4066441944180400d10050300c480b40b060701611419a00044d80347c60300c0300034410500600a00070700c10f2140c1420001800c0d449540302c403001d8800e0b001c460460340c03288015920420040041345240d84280219004541c0001d0540301c258090b00554180c030420202090440d4803a4109075820ba0020404120b1030900344078981c010007051508112508069000034564880a000352942d140c01045403820004228102c3c0c0c000c40c3e020704115036030f50030108082d4883d00100d42c00790240d4a003041e01d02c1c0c0d0714010700071207108134055540c540700f407810040b4207182d0f600c000d016085203108034406803005807100c0c0c00800715101680c00400b0b01d01aa8040041039070141c031f0900e0304120000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 469720 1250 468470 468473
    0x602030c030d020708040902070c030b0901060e070f0905090709050102060a05090a0206070602040506070c080607030b0f10030b0d050307140703020102070504050a02070b04060b010905030303040803040303090203070306020a030c0905030109 105
    0x22040e14000d001d625009a581d01140c10a90305c20b008540050a0f214070024441c0f04100b16a0b5084048a104105054089d42d036151800d00301c4829200b0030000c6007401d400100414800e80307031102c9501903030500c400c01036100d60100320051011600305020038100403051001d0341e01001129031014900e441030110340b030094091615107803a13000090080740d001c100c000c10000c964055801502001e4882074481c0101d0811010b49003e91088902078040c0b400400c01080c441d014004560360302070000d0000301c514005101d4501400403d01040503500c0303d03044026900c203c1c1014449000e0b500441e1119400d007802e00c1240080440201c40d603002a10800050744c0200b6031508541080f9400100313130392aa0950b030040d2003014001803148101504000420405034005a100d0341e0a0f80c5403080c0070384030300a1641e030380300c161409040c60a017400040e0020b03110380c0060300020320150550701601da03a1f983c0c0c0070981e0402c2600d60082078450121812140e40441590002c1108900a000c0302d00107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 470970 1250 469720 469723
    0xa1104031101050304030c06020307020d03060e04020f0906040b0a030501020a0306050102070e0604050406060801050403020706020106050f060708070201090806040804030201030b06030402091501020102090a090e070506090a060806010e040906050403090602030c 114
    0x9015a90b4140071011000609150044003000304043d0007003025907032450000d000945440c40c209052000c42c0c50001c1c0490b0810039108080d00c196400350000103c0f04081040107981d000c000e00041c1d205890320340741619500c400302c41200545c8580005a12055000005825190240c010a04660207144204100007001c810907070000c1040da400212078546081c000050405504511902d6003000103000806500103030090895805900070090b09071604108400e9000300a40035070312840610841020802c0c000c001c2400a205060500c2015595450242402c204885c140c40c0404007140030070640d605030003200c1c20100b044424901d11f20300ba42c0090814200504140380b22420107200c5002c9074000d41c11502c0612005104413078250351717100703250007500c10b504128405000340c1c6800165800c06406481c51204d0003080d601e0513900700750049403200c030020103d9040018030404003048d52280e201e500440c038003c02021171549400e003405805414640d002c4e00455100f0410050407080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 472220 1250 470970 470993
    0x8060402011b020d0204060303020604120203030c040b1305030601030803040b0903030c070605060a0e010803070302010605040b0105070209090703060603080307080610020601121406010801020903060c0408030403060b0112050108060a110403 105
    0x14070380e6a010b8008440c0040f810400c544c010003034105150150105c03e00d1340008003540304601c162054030f4200454a0700300c0e203d0205a6403000c0d04403082c4003c1c4840503184020700341140c00d004122203084d030b44600091516030281c0c0240c1c0d004400100f408244107001c8820740c0c2c80a03440d001140f5505158200e148a41300c0e200014015540d83c002140a680e0b03401080d00080011200980c8a540c648034026140e61044400710007543c43c0000024050405000e014480007050312014140035668080c0243c8020042c07144100c2d014052011000a210b4840c802c0910301444180d83c881c5000c4002500c00200509a80d06c41d02030420300080b200c1d40020000d0641c1d05407070035500042c006280c5240b60701e11000051041d07014082c004201810b0541c040c04402d0412070458426441d61180c01c0340381d02c5240207004580d001080280003280700b0350410741c1c10000600d0810440105040040c003180c0c003e0b00f1604540d00540c0c103100c403a2645001d10452150312501c82c40c070380fa00c1c640d110301c45440d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 473470 1250 472220 472247
    0x2030901030905010b040e01020c010c03050903040b0f040801020309030406030c08061f0306080f0c010806010c0c0605030709030f06050a0501060302090d0204110c060108010917040612050603010b0a0801060504060806040201 98
    0x68940b100c82007000350a412081003d200904140004201c040d2068084c0d0420140c01d9403541ca005e0301450142d101e030007914000d8011801071442d00b81001641001c0d94005545001c03011420400001c4001003440203503c84e43c84100030395183c9060110080c2660403c15a12080002c41d9040c0001aa102d158214603d030045008505008007800160050520355010200e28011580300e101c81030740120307810b88015826a02c8409640c2c807040103480d000720405d0f004d45510310355102031000902404c0115004112030805040083c4e40f5075030000b002594440031190aa04d4406000c21103020b0302405002d407215050a6040080040200700d0ba040307a604040e2040703448444800683c41d01504840052541d501aa0074544e1070b039481d2400303007603407040c09c941600d1040b603550b0901c20404283d80c1a200a95203c1d01c0320245001c0900c003801d809000709505550b2040c14002d690707208003a81c00140140c100201d10715180c84100030071600795900c40302e100d8000c1401c001c0180c0e8805400074104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 474720 1250 473470 473477
    0x603070e0112020406090512010501060503040f020103061203020a0b01050a060203090402090d0b0906070e030604030504090c02070503030406090603050901060501020606060a03020903160e09010603021e0607080307090f08010204030302030901 106
    0x156280004079030040b0180c2c039210207148001804648194803402880644105541c410012022481514204c030070912644002881c2031000c640060100d00160f101c41d8014500840c880d501c3c2c81c404c0a038900c10b40421400342e84112445400c019082414a0042400f1140234810b02e1030309902030740380d00c03680d940c462055030700103082411a542c204004070140d8001c91004414a0b0103003a40355214001d0b106440031642c00d040c031800360302d40000e89c144919030503a912820540742420309805032004110350070650041c8500440c0b0354070104090001030241d41c1d00d034040189440400781c201e6001426482c0b0990404506020507600021220380041050b28015031b10481018110000e0040c1d0160030740c18010f111884152404e01280d01c070a0300c4c900c5600c50500d803204080c0900f214440d1200035000314040503011803180b000d1100380c0d00e4600c00790440d440c0034042e81c0c403516194000c5078404003150079020709102c1880881101c1000e4a075483c001c61802c0e041d910069944d02800840c103040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 475970 1250 474720 474737
    0x10207060309080c0303070203040501090902030408070206070203010b040c02010501050a05010801030807110a03060e07060806010302070b010501080901020d02040305010e07050613050402031003050105040b071b03090504020304030302041505040e010b0405060307 115
    0x30440f0788000c40d10700001c008244d0b5140c0c03d09000c000e44030b621030312805000408405d00801d04000314401c4a025543c084c4c1c940d450302800c0d60a004194001407410b0ba419503940522060700d0700c40d8000c2101044069000040e103604050801103641000d42250341004020301c01800016160030031145103541103201c0c0800c04000b000007458412490304001c103200d0400400e0740c800400059071000380e1b035407604e807001c0c40c1e60340b01c00450480c042d0306000741c640c140c0341004006950240007081d41080b41180054500b64502150328241c0e846544101e81e030341e54400c00b40340c0f142010b0000c1005060103c0d0410b1070541c3c00e42a50314154840e00a60f44601d90000108818010384c1d801c1c2401194040020b1205240c01e041c6400f448000f1598040840c1d1106022202c170303132001800003425030b40364440317040c81c2e03003401d05000080d00000c0048090650811000c82d90001840e00b0b2110164140e4800c0c0e5101e0a0003a0541d10340c0c81a8002e003040403041c0014411551420140c81d40081c880c03508150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 477220 1250 475970 475973
    0x606020a08090f04061707091407020d08060102010b04021804050a0209030601090e0a0c03050309030609010b0604030b04020402041e03030e010513030206030a060306020f090a0f0303020712080c030d02030601030b090105010207060309 102
    0x2040782c1d6208406c14003a14104d030f801c0391404103100301240c03150941008404507921341b006417218116500b20060304542441c080c024007502900c0d400240601c00082c0540b803045c0410b0413640000c3c4490320f2201c5000d0b0100c01c5143c0303805510f80c001e511a0b0250704004e5460082960b030607041c001c1e02c6110f03440c1ea0a9040900040100e0001d850300072221801056480c20890f0f100c0e80400c10300c5000e40106800518011414001c811014002405192810380307580c031b552000b81d00117001280d12a40822001940060004004512524042070381403082d103149005030a0300810030132207050090502c0a10040c08054031014100d94050b01d0f080e640f1703034030103504500910160304010000ca1010400340751034241c6501400084c603013503c42c01c02850b140c0003a04030002d060300c00100140e00c00381c01801032020307621241c00c51901c142d00c100c1c140b0404092035405c64120912140f000c1d40e010080100da5a070502409503c1c00c410784145102d9410540000c1d20789007140a08024503448042900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 478470 1250 477220 477229
    0x114040f05010b0301050403030203040204140402091801060305010e03040509010609050906060901020c130507020d030e0709090305040801050106030b010e04020316031107020d080307020106080303070e040b0f0d0b01090606020a08090f 103
    0xf003009000400803c102d03e018500600250400d550076400703245094100d400180340340302060300a6800a000d10140e66420700400142180660905143e540f90140000020000d000340242084084040c42d144c60400c420700c503400c541640074104201040300100038603210b4211840d0440d2080c1e07640ca0351a840741c2c0040c1e113019901c8040c2074201c0c496031312400f500c0d40349512240c00340c1c0807a4203540d032403e415039040b0305950036404110050741211404103d818600d1b40305050751032207400c150b8202030f6078a00945c2154000d030300040200c0d44540300c0d902590b910560514403e00111011415800d24014500071008000c0000090503aa1140c0c00c40d2050442c0a64001c03070342c01000d01000c450782d4906884160802d440800c050742c20240081749070400441503034031802c00c81d510b2440f00c00098040101030b10160707050f0760308240000703002c0d001070b103d045180c400319015064410103940341407412411125290701020031504110614030006124500722180e04204032a0a90900d00307040008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 479720 1250 478470 478481
    0x3050402181f05030c0306060409050a02060408060a050105100503070f050405060a020a020405060405011203050319140601020c040c020a0303020706020904050405060405010507090308030105010807090e0703020c0705030114040f0501 102
    0x540307502400041080c40c80c0c5030041e03aa42c40b405000120a856550001e140c0e5580d50000002da05402100c00980c40f81029800049601c0c0204111341c120585900402c80b280e0003030700242d109810034000c000710300b1013078003641c1d00405013910402c500301540b07c0010102c0c00f014249404100e0031b001c90016007885101070b03a01501d0000e2100740d07600c50b8400081e60705d45c95054200c0c080e600b00070000e60300d803800e481843d040314550880070004403e1076600320349a900042203030f285050346d8440310b00400c03c03030721030444411803090088a440c01e0040000e4a07040e541610310b84124105818008030b43d5010a4687c0700741c0d030500b0091b80301d0307040345010006400b850010980091522041106119002900c81d00403401500200529207802004a070082070502010300781030010001000a94450000c499001e02c1614284d0b100c0707a190324894800343c805945800000e82c020840c2010b40005124410052504400821404200300120984040c0060010b040c0d040d00d01420301c148682034001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 480970 1250 479720 479749
    0x10605060409020405040f0e07060c080706060603090317071e020703050604030302040302120105010b0405090402030309030106060906270311010507050a0303050a05010501020a02010215070201060f03060501090b03060408070303050402 103
    0x806403503540b689400c100075003003032140070f10840c00d002015520700a90b104109010f6940c8014200c4281040002d07174119200c0c0f0000c0310014070030002500801c00604c00c9202900503950b0128409409050040c980441494644141c0c5241b401b408512078001929030030a108420760388a41010303440d4107a040441c2e5a201800c140150401c1200701613040c1c4c010800d40c0d100b19045020081a000b03124203d8000740100400580204014440d504c0d000302e92680c800e100404407481c0c01d0160002c00c2c00d6405551082e008286120002d014064000d0305500312018081c0918010fa81d400346c1484144141c1d10001c3c0c6040594041c1e0b144130307481401181d0344581c0107404c442c0e00981e60301c1c0080003040100c800d030b03544500c4c10740082060341c4007051910950f03030140e0007480080d43d003125030340110a0103400102035640e10100002e80480d041076403c000d5000f0b400c005190361500308080c05507180c0030a02d5100e60015400c200008141e0426108070355058540003807a82d45074030105250482c0d82c880d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 482220 1250 480970 480979
    0xa050102070507051c030801030b0a06030204020a110c0f0d020603060102030c0303070908010f0b0102060403080603070f06030b090906060a0b0708040b0403050a1202010218090a020409020307020303040507060203070308040b0603010605 103
    0xc1c4001032020001e541d01c22140300303950460100d05c002421150b4900d403450700400203107896004102003003401d903005410010107400002c04503600c0c0c1c0000e040342e03c0240d031200481e12000c15020310000900003042016030684141c1040d0905200080a1203400c40b00248210004070105507164400c2041c0c450304941303c021203980f8205050090100101d074845c84d0015801c1651010450303800f40200310543d24180c0080c070250311950740503144c1a4000300001c3e05482104000a0080e403003040070001811705403000203105c2c41c0ca401340509003000400071a03040c3d2149042c403140d501c9013510348003218403000d945a100c0780c840c900300d50700707208582c014074965802007400f1040c0200400e844042502c6030791400041e050b5001c043e0b09030301603048440515a05184d5510302d608201c003081d82d108c040f0101c01447c2c65180c040600c12600203455803801a80302001b08820080e0801c40d02000e440f59000541c10590340c5d64000f420984020001804411240d001c524a502c0940015026040050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 483470 1250 482220 482227
    0xa020405070c050c01050406050a0507030e040f020403020405010f06020c060f0d050f07170705030c09010c05010c05040807080304030506060103020901020a02090403030c020c0f06040302010309150207050303010303080604020c070e090a050102 106
    0x200000c2140081e42d105450398082c4080d2401258020b10868044a04c1038884d0340c1000032054041d25541c014400c21f500780101031899a005076079911035080a444c01440058449095005200440388141c000d02c100403016202032141503000180f0401e403e8049402c5965503082e030350003a0181c0140001d0940740c85c106000d000225403203452503485003550355a90744102032002042c210142c001c1c0c03032002c013103001040422202e400d10001021900740604040f009400c540c0e540c00d085401c040d290b8400a1400700d014048900184400c000401c80c60008500f010f00f1901d80540750100079204505141c0d000031046400d900034840c00c00220f400802524052500c0d09000d000381000e94900001402111121003281c82e100c01f0f10b03111010b010b00b4007400c0c40d04580c0194010b0040c0407041e284401c0f40405000c04050900050511a10075005540c482d45545800707003600c0d82c050f040c0c5214030b005101d030440310600011060102c4010340e10300758068807141c0705503080400c2c01501819950000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 484720 1250 483470 483481
    0x4030609030c06180209040201050a11061302010e0105040b03070c02040b060c01090c08070b0304060509010b0303030a0606030c05040e0a0908040b0c07030507050108010b070303020309030405060d0b030705041107030305090a020405 101
    0x2120a200709000b120300f8401d08148084e14076204507001c00007903100105d0340100d0095480781c0043e0107a503001d030514010340301c20040d42a1412030100c0e100c0c141320005070400d00865901c6070780000c120f1400c0c244035003854241207580215020050035901089482a08034081d5566a009201c0020024003070507a202c3d54814240d02805440340c7c1070310030703005681d0001080e01000843c2401c80348501840b07820340c2c446691b0b5101900001d40298225900d400006905640c01d100940c02128840d00001d0b200d41b0300305020b400d6580c2402420103001d400d01c4104076401c0b0107100103600081c80500016005214540189980100e41000758003802c0894281800000010402d042d00d00071411100a150f5607001110480400d005682450b4018003a60300000d000340c02a580165100d01924101501e030004501a5000000b00300300640e140e40c0102c032581070034040caa010386400e80b001c0c001da074008003480440340b141a2004003010359540019015550a004628040d64010400d02950400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 485970 1250 484720 484727
    0x2070f080909090705031e010204150c0b01060806090705130305030a0c0c05060910050703030b030604060212181b01030f02030c030405060a0902030606040b06120c1e070c15050403060903 82
    0x262001c14000c00e8104041200300b40e00090010031258018001d04441082d40c0d07040b440b8294000842d5155902030201240381c0350704e440140d100c486a66102101d9400b00d04100079040f1040e4000f03000d020320305050240645803038400c81c0d0720150f1402c00903a100c0120640e18906d00c0682e00203005400702040f96550140d118403140d850600818044624903180e000300649485294170070307136100c000d07800c000002c40e0150020f00a40c078081e06001640c4c0b40c03014040381c00c2c14402c9a04481540d4001040d02c240c034500d005d5035400c0b4590b515102d61907030750720341420354800d00c0460004143c00340c03c070759501d10313842900034210040384001c095441c1d00740382181c140b00390026102240d42d4016080014907080e0284140490316400400802c980d0701c2d50400d0100174004001c1c0c00d50480800c00012000001e0f40e601c0d14003a800981c00c0507603401201e6509001881207261403401707003108220800121301c40c4610002034400c1c0c9100f50814104030380d420380e018444c56100401050800709200306240e003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 487220 1250 485970 485977
    0x70e03010c0203160b060307030803010e04030807030b0102070308130f0306020a080601051204080702010302070501020a08060307050a0608010306051003050d05030105010e0405010305030706110c0109050601080c030708060a0504050102070f08 106
    0x109900034000342110300d1081c0d890340940e103000c4070b80b81e50164511000c00d90005419030090009015a10201e450307440380400e56009801204110b2018000e01080541c0f0904183e840003542c9000c001c00084040000d450320150f12001d818030502181c801c6c080140241d125004090004013981a03d40e42d10f02107004c1c3d00400210008034074000005113965003e40d04a8000e40c0c0f4040a9043e00e03502c940d540c5e81d403a0016070301a41016401d00640000071002d100a1409402c40c0c1c8620841d0b02e0400101403409480e074100c40e0080011400c10414075400403103250650346d0006010031550350b400032035074460b6010762024040d441405500b200e1540c100c401581038400c01c0e80c80281c02c5120b1414030003a242c00380700042c003641c420400e11000c10b02590001040004030040203140c012801046400d42d03420080648103500a540100404981005421222901640030b40300442c5044c030007a4990310300520f02d040054032a00010304001c020350498010650164494410640508000c20280c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 488470 1250 487220 487247
    0xd050f07090b01050301090e030403020402030103080c010605030102090102030d050402030c1906030f0501030309030f05120301080f06010504090203070608040305040306050c0301060f0201060e1b09040203010303050901020d03020309071203020a0b07 109
    0xa9440080740004150103507204410060311803502d03592038640004000d01c0304042450040c00705000c08401a69140002c40c02580110701e1140c40b5800300903000c0c01c5660326441144030760f1042018200590700403041da8000300003584005500d645a0010a04140400300078950200e2654041d81020480850220940e8007540c0c2c10807441882c480c100d02210070030300000e404280a10300420000361010b1180c481d5038450000c0d1034480c1d10101484010782c0003a001411141c006e450803041c100d008102d0030740105002c0f40d0920031413500d1f402003600c03004240101c2e0201300300c03d00040d0525001c0d100b01c0c1c0c02503500010030011031400c0601449103800a01622000505c01c03c14095036501c14010801990f4600d08100c6039600c510002d4951012007824844c030140042c4803021440c0c3d40d070710141d0b008602a03180d141d030720346884000a081010b4910a101414814410310101c0034001a40c81c00307640d0f9800008121060f1424140d2500380354010040c42070102a04100c0da43c3da200b00e4056204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 489720 1250 488470 488473
    0x10f0905150105010207030b091507020106051203040b040504020901090b030903040f080a0308010b0a030609020c030702041404050c040504060b060d06060207090e03030c03060a05030703030305060112050103030503040f030e0d050f 101
    0x107525581141858034000c0c4a01c03030060384411014000705144844440c0c20291030030451b940140d0084401c200413204031541c0300941d546004c10030050600449c14051600882e024610f80780c189a042841400707103018040c0aa40e011a4813542640150554000380070b050f02003d4aa00c0d040e440255244e2107070007809005078541c000000c80b42d07400070303032210a15855140c1040d56070901c0103504094129101d040c08040e00d50308001603a42c0c07079200510205541c0000366a49500a00620040e55420312804141602ea802000080344020400c00001007046902081d0740d1a42c2c180000549414101261f018800103030004452220740d128400725010381d025030b040141c2d100d40b802c0c100c88501c10403004541040001624141c010001141e0081c00209003141058071200403a24005aa800403808641d0368002d2003032640e0480100319004034110380a0000398103550300100f080c000640000c1a14048201e070f241014041c004512600c0806090b00200b00c0035030030a160b0391021340b0410707200d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 490970 1250 489720 489733
    0x1205010b01050301060503040b07090506041706010e04121101090602040e060102010605030102090a030609020310020c0d0e0d020d030302090103090803090705040f02030403140c010608010606080108010e01050708010902070503070203010f0905 106
    0x22940507200f5030341220b166403515411580c83d5201d40207200d000501a03010880c00480109440e60b0303200150000d04040110404081c4207006c80c24a04041a0400e03500702e070503c0c08000c001800c01c4a048120100f524045998628042c4c1c0c1902411101c00010055400810041000384081807550f1140000740c3c002c0c0b03d400d03562001d2608030321503028540e400c203074461001d2000c02e02c1500282e1b0703402d201074125648180511f119008030f030042c0c2d041d801142c01102503a480c0759880300d47c596002008480a0003074280c03a9000a841c060221001004d00d131700811403018580c0203a0110030040d40150741c0b10b90301d1500412641e100d07445030060507c254604188250040003520075644125499150110030518004400f601074000c44501c251a64807404046000384080c0503003170050090f41c46005a5504200b20f403425668140c1c8080d074680c0c5404200104d50364415581030440b0504280180d9a4006043c16403c62245110194040d030034a0111030510045a10071201503010300195500d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 492220 1250 490970 490991
    0x61d0a03060c02010c39050a030503010303090602030c0304090e0c0d0305030702070b0403050d050306060f04080106030308090105150103020c010204030b1003031403070206010302010e01090306051003060f020405060417010b0901120501 103
    0x141760b20103001101c0342c140554485072107003010482c14483c2d1404011403410003070319070f500c1c7c2e0314001040c0412000201c010004008041e00803450001030a1a40061802d00d041d41035032540e82e00542c41070303810850311003580207043c0354240640c50741c45401401041c05c290769070a01800355401581e4003001071007100c900203840c004c45420b07107042d20f9020018200d440701c6030000f21000c0c0c201030f01c0303158000010401c01c42c00400c260000c000501c4ca10001203195440c506010301005801030003d042641010108012000b822540303100d032540034240141c40e04000031a040c0240210f0304004d18089042d014491604c0c04032034a001201d10030344c5d403002d0b042200c03458008140002d0b1070140c056403041005100541c0901400e504041d41850700d5403100b56681c80300e0b015140161010030710500a07907810300c00c1c80307014044c0c0300708080c403044207625203840c3c0008944a07100780e124046800349461403111403200290890341d001c0b01c00504050321540c485407100941e140522048901d51728120b030110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 493470 1250 492220 492227
    0x30d050415090305070f0201020c09090a060506010e030606010305040804050604030302010501080d0903080304060b061c0504050609071409060301020d05010611010606030501050108070c060e060a020a0210050402030304061d0a03060c02010c 105
    0x50700c00c0d4195a020b0400c0b880f46c1c2d030640c54445905d42207040d4003400d400401c40343c90740c0ca100d510999202000f13180c0344200e8185001102c0006d400345041054190b40480d2035280051955040035007881c00040350307680d504004000780200c1d00043d520160005000060507415000103050326111010388502210300c030301c140c8034121188002046a90244009000f041090b448101c410001410b407901c0d02d080020350840b6014034881c24070000360f80d40180410301004020040d40b040d010001043c0c0c01d401c01c5001c92540c84c3c03100c0c2c014031490360705000800b2910290103450320400007504c140915610f41d000030303003140c1c080310b45420300750700e0510700080151003030203450b0407240180c5580c0981c0e200c500c1c003250185000e00c015a0656100c0d41d0b07413030001d1001c2008506c40c000d00800180c4038100780c68024201150801c2c50b000e4141450148805603a001c000c9804452a604000c4240c4ca5a2172815004400c05400c450340f2540d03042c0c0000c1440701d650050001540c3c00d5008001d1408440c9080c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 494720 1250 493470 493481
    0x304020307030305030a020409020409020a02010b09010b0d0e010e030a02010605030607050f0306010503070c0b0c0a03060b0304050304090506030f0703030e0103060b0a0207031202010207080f07020405010812070803070c0203030d050415 103
    0x2940c0341d8455141000428007910003150032500c3c45c20090714190300c1765299800d07a400b43d400058660ba0024412038082d43c20300c2040003614044514400651400001c80f482e03000e46444d01d80320640d10030860044510941c800f480510410050380d0726400b43d0007001c1e000341254490f5038000d0054000003407606200c2e000311111240482e51070303419a00c44030300440f51038100411080c107100d10f5a06100108ac0350b00270346445050b10300c0007580c0d80c4404000003015280c2e00e9000d1b12490703a060003840700084000c404d44041d500585d031700003226510400024680754148800052074014428040241036214064a04140c403c0e02c1c207010013944c07240200c01c10307c42c10304c074480140c2041e00f003800045e41700c82d1103a040e05070510002d410300740142c41d0701945c1d80c082c541103aa11440001c0c0d2404500306401400e00401c2203801604001041000c2c100c401d2280410040803000c000000400c6980504641c801140d0054200c80c0c6940080b46071000400c02980c05540c114070500c4c407110848514000c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 495970 1250 494720 494723
    0xa060c050304030308040c03080d0b01030b01030207020603011203030b060a0504050102010b0108010302010f080a0f0204060206040606060305010602030708030606040e0a0506090a0501050307030213020c01020a0f0e0a03030507020d0c031407030b010503030304 113
    0x81d45031525540f022209054050021201200500d07400408624808090412181c5101001503400745c81d500140448541d1115a0306050050010002580e80c21017620704480b55403000d002c900d503040c070f0f048006010148400b540800d0208030700c40c0c1c1603448005031040e140c01b80c0081102d44000c20055900f001e0910000740010440f0209000062080480f15001101c1c4100402d161801c60180c01c16a0465045800182d020000b0030007403040320301840c801003101d0f050411155061460007910dd12403500092303d088000004110301c3d0303ea10048030010414044404600d040078a82d06c00a440c003981d040e485042c654000c00e019042c4c4c1e102d003a040b160018010401186180d0921190081d08000b0484007039080c000b101e00c00400303000600240103565030f00386c40d1070244400548070003a52155136010715038031801440001c1e00081220344c1c075601118219400001494140c1c45030605810040202000070117004c3c90a00006070303035040d64443c003808212aa210802c0c16600e00003101d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 497220 1250 495970 495973
    0x5040209150a030906020a0201090c0902030c03060111070f030602030106030b040c020c0d08070b04080306130b0d020f13060303030203060307060e091302030a05030301030c0e010909030c120216030506060a060c05 93
    0x5056918803250000c0c540502d0303e08002c52109501e48843c0c00301c1c1c22003000300c03000d40d46a0900c001088400d034228009441e14003c1141181000300c0b1102c160b010080503603040c02441810300c2030302d040c10003d490041c0062000d00b1640c81d200c2c0703020800384d0402e11032040420300300707002340d01149450b01072a41e520550782d005028100b9140100424804000350541d803400d0104000301c00f180051302e440d486140246000b0713030781c0d04002081c0800c0c403260006a00b4058604074901445079a180008407440f80c04903120b0100403c40c1c0d0004142c044c00d22205a445441c00000000b050341503005184140011400d80b000d05036503c8003a5900128002c0d4541d02589810004030000e007030041d41210540054110f5001358215510030b1301c1c6500a8009032052032403031504001026050313070f1103405040b12610030300c070b01001350390003800390618048000c1540c191080100c01c814420411400703102400b003880c80c503156030b03414070075254442075400500803446488045000da00940d09115156031010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 498470 1250 497220 497239
    0xc02010c020c01030b0f030102030c0309060f0f06010f090e07020a0c08010608060414070302060403030e0f0d020108060409060e010f020405040506060304020d0f030504090203070806010305060306060d03030b13060807030303050105040209 104
    0x80118010036201790280d80c48046440c001030750b40c07024406180700303d8000c8442940d80c1003c1400500d0440010551001000950f013002034030b0610000c0190082000c2c00c0c600c204102c091400d8031500b81c40c0d0090b1901414100405c0181940001c85200c081c0c01070103a01349654540e80481d007a20164042c4075031503408203002c18005007071201e5480391503484400784c48d03201e40c40f41c0c0050465031140c1d0056001170703000c458100d13031460400c4410341076045c105c030764070750001541d400a04840d0006000501c5650788404607024428903805c0400035510580c0204800345517030350305000940290103070703a003d00d180000044c01741c100501142c0c0603e400170107a000c2e9640c5599120520111400300700c040150500c00010032002c14005140184c280c1d40310f070340709440c18400044c03c540000f0000c4c2d100b5403100b001d002c2c5545800340c480800d20740510f00494051000c0d07021500d4034102c082c100355100c1c9050400905d0343d0002c00c8a409580c07080c0d80074815030740c0c3c030307000c0209038001c00030b040754400c00d000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 499720 1250 498470 498493
    0x311040506030901020403020301060602060703050a06050d02060705010b0a080a03030e01060b03060d0305070c090b03010b01030501030201050910020c0303031006020607050304080d0b010c0f0602030106030605031501050d03020f010608030a030c02010c02 111
    0x107030103198045104400985090b403a0b0b80420300356502d9034042400359101ca01401a01c90f018002e81d5402802d00c00304015861801d0001030003c0490791029000e0080064040c0034000d0070740103003942c500c011f08030072652692840c05580d40c03100c444040d0002460250307801e80180301805071204550888031124110340321003082000344c2c90500b4048051210030070450001039003815400c0024252002d000500c1d41c886c000b458255103046d002581098a490010b20050380c0201c01d13607903002c0301a15610700119007000e043e850100361101035a85403102004100d0746410901c0c106056074000c1d42070f5141c2d500c880380c0903100c0740420b440c000c042c01c2042c411a00002035650008190401c1450401103841c403a846140070710352090400e0704d805800100600015030540281401800150018900c0301202d4020f4104074506002d120700c00c20409000d0b9041c5482000071414642645c0000c1029507910f0720081d6480d40002c2000c0007080c14080004100d500600c180008288180c001e0540b01c03044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 500970 1250 499720 499729
    0x303010503060c0a0203070501050109020304060b040b010807120603020307030803150d0804061404050409050106080607020a020a030b04060209060f04050102010b060901020307110301020c070608060a0f03020607080c0307020d11090703110405 106
    0x13060b0b001103100034040310740891001d008650082511080041c0d8a0603e41400b070709940c002605140280d00b402010086664001292035000040e0303e4240604a0020440c0000e031645520295041c03095110120612031030780c0045000d00068002c008251021505004881200301e202808040302484100a254010810041001c0da100d039220316144d140c800050884648030b00941c0d0581d5505414064003c01300511500088103000410070101c5a82c0021440040c6010080000705040041000c00c107250301680c918201c001e140903100c000c1806501c40c0da400c1441018019802c00004400900340002150345401c0107a000d14a000f0341034840c902942c840a5000390550341c00c02012446600912070b113400303442c40782d070341c28106d0030320008214404200d41c00241050130104010001030751680111100e6030f40c0003c12640741e02c0c01c03910700c3d4214002c110019400410310b006000c00c0101030741c45200da0140c110369005103510b89640c01c40885002400e2844030000c01c200078441c80c0391 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 502220 1250 500970 500977
    0x80106050a12050f04060e030301080307020d06020d020703080a0b0d0b06010302070c05130606020105100b0703080408071a04050f060c04050409080c010c090608070c0203030403030302070809030105090706110303010503060c 98
    0x2070342e09052038002914541072044900488a100c4490045002e20081181502462001d40300c3d580055007035504000c402c584034811540300a100b401d03a0f082c0c07081001510340540b41000c1c1c61010442d203800d07140c20041c11a001c1142c7d0b15108528000e91500540781c5036400f072051541000400800d56148070041d002948002c40581b820190079400150f59a186c1d491510302850441c40803d9841c0780920190a6a00103001442c003050810428801081205c0958480542515140c13507643c40b281050100c42c4246000940b01030b50040c5542486445500c545004e0344c0300c1c0701100c2e0b208101481482e145d038010780c0e04c4111090304010030842e61809030040c1008030f0146104919180303102d190a400c4680841010010450100c0100240c83e0803001d00c5038090b8280c1030407400714a9950000380c0f1307481903000007424107070b0104041c0140070042083d1124054003600810181c1070101c44540e0300c2c80385100b0b80c40010032000d0032540901020082c2c078100c2c1c0010380289060f0309d034a00783d5a0a9003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 503470 1250 502220 502237
    0xf06010315090f0605040503090301060504060b0703050a090801020703051306050304170c070b070f060c0801120b07030605060a030501140607020609090405010908031302030d050301061205060406081b090a0c08010605 95
    0x300d1281c02607000c03810300d05c01c0c0740c00380340b00300000c55039030200a09041c00e540c2ca0f90700845c800c2d4035190342000f6420400d011a02055854a421641c8240e80c42d001c0e0b40400b10358100c54410f40c4007141600403d50040000d000e1100700311400d00340c03150b80355002c54180c44202c1d0020900d07808646541008601c18000c3c0602143e148203486c130041d26040801526045408165400101083d400d8180100f0b44200701c0002d8507031a1403184c1d0340c10500384103900f8a121900138804016a03001903070311442030348058040e10001782102c2c0e0390140b6150040c0030740801e0042d41e0321082485000b1240c1d280c080d0483d905030380d01800d010b08001c580020010b0b00343c4010002c1d610340d52161041d00005145000442c800c0b01044120b2050342d03d1401810302e4035481c40810003d1140030001400070750342040390751070300d840e40c0c0f0400310301586c41c0d0011401400c60b9620142003032003554110801040d1840018911784005e90709009503585204200054550404050b4082800d0b01c00500050340305800400164 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 504720 1250 503470 503483
    0x50a1416030302030f06010504030f080a0201150306021b0705010903020607060204050a0b0d060605030c0301030209090f06070f030506030703020604050108100506030c0301080606010309050d051605030c01050105030f0601031509 100
    0x403111010320966180c905045001039070020410841ca90b021038170503084542131a000b41410b04543c0e5072000e01c2e410141c060024a00401c01003074152003500a01c901031035035440007010fa50760b8a01080a50800d80100003001061003601d07181c280009407140444e84c0595407041102c0c0380da002d010701c0d984480420f4a11540030800400d441d02d500c03001100078010021815500c18a01a4034011244c580e00007100f0440104148420f8420040580e41940d8044aa0040503124031005920b80411502d01c40446c1c020542044000c0e504040c1c0403205850546042c4202d41d00d0720101a01c0340c09078000250321180602082c44030394440e180c51a03110606c08040324100343c40e000001d5180d003040707507099524603000006114080041c0800c5030080f0081c00e0a22085045640b10380e2034003080b4030703204104080030070201d03101c00c180e07101c030724103180c1040c1a070b43d855001021a60223030a09016240c00703071003050b1025003000c00010300c2c07038100e070b42113080d0a02580e03400c044040038241407901561030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 505970 1250 504720 504727
    0x30609060c220504060b04060f03021602040f02070210080108010b0303070203070303030e070b070501050406060506090901050f01050906030103060902011403090607030b010905030303070309030305010801021201030807030203040e0408030702010f020901050a14 114
    0xe458a105e00c0c00a00070113132a0548aa140c6500141411034182207441014010b004400d255000380074401541d82d811100415041c4134188404002e008100021358006a402c000d41c0001e6044a80c2506981d200d80090015034a00b50031b040c0c2ea40304014000303406510031078080001c28465480044d590b0085130a4507102680c1d540c80f284590000801912165504d07400d001c01c000e50745c40344100500d421b4030030a0405650500048070b1100510950303024808143c1801500ea200b9012a00001c0005092070384a5031207061500c002c2a900300d04034045180024400c4c1a0b400201c1030700e00c550303941d0780107048a988508003100a403600c0004281071000f84080400c4c83d035402c0c00518414503403543d0025902205060040503030740c0607803100c5c080e03910402c4903410030185a800207054032303081411180d07200c10f5403600b285140300e83d0b4440209025030409200c10002c40300c0080d4041c001581c006e01038a0b001100c5c0008a115001c20180401d5003040b24044a501a10341040f1f81030b1580034480c01d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 507220 1250 505970 505979
    0x906020606240a020f06010501090302030c01030b0a0f03050a0b060904020303070609030e060304050f06010f0501020a08090a0503010905060702010c0305060901050d030c060c030204030201120506030613060905010c0806030609060c22 102
    0x7a034210f1601000560098410783c80c0102d41002090700410091800d9041181746401280c0ca0303903410360040e1b040503140d2040481c85d4031041000030080060501d400c003021b68a0401540b01d2108050440300307280743c1d0300424003a1030407110590041e60020055803409030b05607110b100900034408101c0074810310b5188043d4aa950f4006903120328012000b510204000c0c480240c240b0b84140c0103100503201841083c421139074000391600c1a154043c04165866000100140302c03200706078403141e4590308090844040000108105006844c1e03078000307200c3d4030700500007503040d81c2048490320b4101c040c44004000f02e15100d4440d1a1044c000e0402800c60f2506407200d005031440072004d01c0209800080800440d47d200c1c10320308009104000030416400c1c242e00203501e440c4060840d6600f19078020300c4109010442c0d2021a03003940c4100200709459a500000d054503078100da2462090266400050500d100400c3d40740c440c001082c0070b1071078080c8410620b1810a840310703004c03006411216010a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 508470 1250 507220 507289
    0x2070506030a0603140a03020709020d020c010608030403050d08060f0d0303020712020601050f04050408090105030916060306030308010b070c03080309030d050c0403020907110a0201030f0f050a0906050105010906020606 96
    0x10b02500d42c070304001c184242541062040180748102542060f030144e503501c0c01091b070102d51035040d0380c5016005a62803004400d200041d014007085031815502c2c3c00e00000c3c1d100c000000034000c4a02c54416034201030309030324040d82d02c3c0d1402c642c03941d0424610900a10185450212490100d1290038018148052901ea003100b00800300400070141e80701c60014080c41c502410201030500d000c6070144a1890640e807540c03400d005040c81d49052080120206005036801d000c04509854a074207140c0740035a4868000300a00b00d0b034403040c0e002c10031840000c6003080a60040b03620b542c1c0c01100d54422140345654013a03155000509100c01ca0009000460801d1024092380c1d02074002a03c4158449003507004002e1414000303017440703050003408039204043c0c03007000c03d490b0f080c2c0740c09003800180e22030204509000b52400d04e15070f19580d894502080a021020791186420303a000e4001003000341c0c0c80b4030065441400394040c420150380124000784007880c100a0010b802c100300300c0314030010140b0343d4032203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 509720 1250 508470 508477
    0xd0203040c030201030b030307050a06050402030304030b04120e040606020a020d020f060a020303090c0603091b0105070b070804050d0212070204020304060603020301110a030c030605091609081009030801120201050405090702070506 101
    0x21200c1d284405000c00c199030f0705004104050301d089015620300030b8150740b420354039001c044c8020521a1546c0015055650a0040e0b400868100303200001c5481c013860019540c1050803000030102d1445011220355060903ca40b00c1a0792464004011101c6240c08008040340d00d58422a0311060820568500303031607000c06070550004e503400854880c00c00301c00d024103000c0f100d9005070041109208103c0090310029003400c0c84604400d40c012203c00313580040320244a581c0014100d26141c4042c4800e02e0343c03003c3d91901c80d40c014020384000d040034400132600c039509100c01c401c020310107004c4100549000c2e801180c000d4850b800000d11581d4a0380840e00b501d821f58030710301c0d00910105121000366051700815039a411140b808110786400d0038001030f820300c40685204548a8010185482c5030300980800c0301405120382201c103540790b84401d170005002080800c034000385420000189038a0301d0f130240b800a0b54140c4801e0306207030400040c07004406005005000b1842042e0340001d003500e940004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 510970 1250 509720 509723
    0x7030606170105060609150a020307050a030815010804031d0102010b03010608010b180903030117010902090f060406060809030304030507020a0b0a05030a0605010203030601080c090d0206040905010f06020a0302100207080d020304 100
    0xc150580c00c01c269500e0843d04000c000c0c034042e0000700100901c0d13580300014007040805284001d602c406200340700b02d16501610744004c02a1290314400c005058121010324810f2504d81108440152001c00440c1c5404060303030000c001c100c48040055265040c80300712441080f041c8000209040000c000238290f500e60340c012451a552a135075000c084c10305051b045c10900000044190504104142035906e100500c5581034060440b205826094402c0d00301c80d03602c5400600b2300400341825204509203810545805108034a0010000b813141e00448490388140e4407a0041c50440c0c2c3c4030b860644840d80704501c2280c0c054840e803404522000e001e4082d001003007450b6241500ca150050320142100d0182c2c0081c5d040d94024810804140c0e40000c4c69a070005815403c035803640c0301200421013500520200030351152001c1004201010749504c40340c1224404200c0001c0e0558a003016a12441220303409801070300140b002c0030400703206400800074a445181c1c01c1c1e103003c0d030f400324910898005540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 512220 1250 510970 510989
    0x50c09090115140a05120411060d050106030e010b030c060309030408060a0504030f110604060b1201020c060402030705040902060a0507030203040b0409020d050702030f040509090307050105040803010305010e06010b0d02090307030606 102
    0x804060b201d43c403280182c00c100c00301070740314030300020b010000e0994011085d99032010720154000408105808125a41161016205588650054a1300d0000e80405d0145100282c9000b040d0301c0c407154140104850f000019024080e043c91100500c101944000c4c40d98490348001c00000401c0101080a01d10075080e01d400051282494503000740021030801c180e008003c2e040300e680034112804900d85821540c01180010071300384960108043c0c0942c5800c0300443e520220724030580f600c0204902d4410380c0700704c090300c0c1103584030030402085034036a84019401035410311070818654001d07001800303454000d0048908107507507041d03003014660041d04013070303031554010500d14001e01050085603080707401800518141901c0500192460180748a054070461004011401c0c003001801201c521a400c84000d00440c40c0074284a5401d5100303100898041d803034000b03440c0d500751011640034103071240110000d00d0010207410030000394011511241c3e05000340003000001928a10890009250145 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 513470 1250 512220 512249
    0x209010e01031104020406050d020703030b0301020c03040609120f0201050a030b030109080403030305070206010506090f01030207020415030b01080309060307030c02010e060403080a06060201050103020d0303050702030f0c07050f120a06050c090901 108
    0xa01040e0303c001088210340524011311040c80610380000645180c9602c401005854690905045028103081041542c0551000641c44030414000c00200300b5030303011341c8850b00d4031542c90603805031116801c6009000790450380d8a00d00150f00c510001e01181c0d81c3c82c500410f900d50000b00090031a07642c81c03400c84155800103010010141c250041e0356003c7ca460018210079890f080102300f03944a0807100d24800c03c400c40040d002c0f0780c040e9058802c40307a0081c0040141f207041c0103100050200c2800155024034149000141c51807002048074441000503100a0558071100e0040d4040c00207509044255500c442d414808800200f00d660b100b070b80a6a02c203070b4241004040c210444016411a20441e41844018009a1140800b00c0640c079810700d0000b0b0503030b49440040341140985007060005910000301150030800002d01030050f50001c80f05143c1850400c0c1c10846201500c4030704054039080714244c1004100694045540300ba88070400758904460b03440015800b003000d0b04212904200700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 514720 1250 513470 513473
    0x5070603020301030b0f06090103020108190509060103020307170a0206090a090207050a020a06030b010207050907050f0a020307050601090203010e0402040507110307030909050f01051806010306050402040b030402030c0405131e0209010e0103 105
    0x2017403154105150210840150034000003090002105000203030510594002049074420684140446406c081c031040000e402c00781a03042c0c454400788401c4e4030903c1154000700e04042c4542014244540c40802842c10b4400c81d0700b0300445400900308940c1c4840e0f00d41c0001a48180c6000a00c003043c812000303005003c100b8810428810b07400d0300a1000c051400000c080c1913600012800103641089903c05166540c4803011140c5100d40c00e0500380c1b26901103200c00b0101d4000003d000818031401c1518080e03a07d031a1061b040340424410054074002c45000b06026050640c000c5070051020315200411a94805c1180d03e9544805011000a401e000c1c041000c003105101c0e16410070700f01c0810103019450240020410b12107880c000b043c1881c1080803a031940e02a502a100422001e00290b49507550b40340000202c0c0c00884040c0e0181c040c480070302141d4640383c0300b018032807005545400c0c036802841c0c440c20302c040d80e0091001c2145211a50b40c00159540c200e110b8002c00e1f00030420221581103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 515970 1250 514720 514733
    0x30c0c09050603030f07060207020d050a030201050a021204030302070501060905070504080c0a060f180e0a02030106030e0609071502010212090a0203100b0117250905030f070803040303030504020d0507060302030103 94
    0x55502880c48039241400b4820302e075a011017150300e0004c981428949806250030250002c1c815960000c0d88501c02d000c2074001c008000ca66242428041d8008001a40d114a60502644101c68100030703000c04003000100080d00aa000d0f0841c1400391000050190303c0310f107000110764041c2da508010840c00719040040f18010882404d00d02c60a032400700645203800c902416003c1400304c080b06000a55244810000d0248403200050800d000b1400340c2e07082400c950002035000f80600700000e81001118019240300040160050810300010010b80380313030401504007045c01d4440d10301155002c002803084d10751400c2a25000e03800c50005030104000d07502c101480d21030400269581c4038241020129a87e03040f001455109070f48002e00b00b015510141c0100c0080079200041804000b01c18419020707541c880708000c15035406070229030050400810003641c039000351048108a5204210a200080c0709030400343c0c00a02c0034245d0340c00101c01d562554200800d603009403000a40c08401041801074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 517220 1250 515970 515993
    0x603010606030209030304090b13020301030303091406060102070501080a020c03030c0405040509120f030402040605030a050a0201030605010c0b01090209030c060406020105070807030501050d020d05030c01020703020705030705030102030c12070c020d030c 111
    0x7940c10114905154080820b8581c000d0748508100e03a503594a4181c1d550300e4140b200808008411030031596582c4070300c0c010300185410101520a03003c07080003d41044d60015816000b40816001080d00501d41001121200c00060002c01300035020701407030020000c20005580030703103440160507807958142021f100480300028100e01840d0720180c10903100b007402c82d044a15650911185d56526a1103001003030142015a02c20754051241004140a0080102e1001071640c800d903024403400340d5400044440481690000e8580076015004201d2484203600915170680c02400b503a4001a0030700016106030400d5000f040540d440300c0400000540c000113181e8000394508042105504000118040400c0d001000b070152260030070072428401c00b001a1000011804000e560740e8010703140c02500ea201c2485283c4c001d1117140004552403906000b170700d00c40c0700106038003070510701e244120f0380d10310744087d141f24180500c5a04040240e10303614020f000307040c0a03803a40c10f5125503503c1c0c00d0500c2103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 518470 1250 517220 517229
    0x506061201020a080106030b0117070806040f060501020c01080604060308030103050601080c01050f0904050709090204090c02060f04032304030204020324010903020303040603090201110102030106030501050114030402030604030c03110706050306030106 110
    0x244100600c07281c043c0c01c640c1240c1546c94a240000f09034190100584031600840824a40700314008100048182d0010000b88210f40540d418800c141c80040080e042d1f40300c900915000da00b200d00c1c90009135204014081d0300c500d0040000c150b080c2e40c5c5d1114951940282c000b45d800b40c00a400500c503845042140902151007841c00c240340c03003040c5a690569000d0640b0b401d218036221004107181a10448000014010b0020110742e200e684e814400010600c2801d6440036010301e9001424501c0c035119010301c21501611044400900e1aa100c20f1401c079907281e08820b0881404003001689071880910301c104d510300c3e15803e04002c03001c082c640d01c88146111a040102808003072005031804426030b02212954140418030302c3d11440103079900046d2100c070b0300140d0320120002400542c5604040d04880b0203032142c00100e24001601403c40c0310448029415a011304045400244903190401115001c1c0c035201e00c100990f1100c3c00d0800e41154009800590080144640d41c44e0a128080040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 519720 1250 518470 518473
    0x2030910020a050604080a020c040c03020c01060602010605060f0c03070b040501060302150307020706050901050c10050a05010605030103080f030a0b03010e0a0b090d021009020102010b06030106020102040609051012050705041205060612 103
    0x410303a80e0f42c0c89540c0c060040009007008000f1403c408201d00070414071030749075401003007403180c03040c4101c00400941010880d240e5543c202140040c03030074018071480c000e50384094215440c10310792159080f49580400300c400740c02e100401c1030f140410304441d85280183d2081002040c0d05286004010000161140740c84880c1d50400c1441003240e00002c1c2a411609076040c19512a80c0341001a2200e025005000b41c0500070f03021a0308103200c25902191190020120801882c0d0721901d04584502003400010400c440401c1400708110f804000303035504c10b0303d140c00840d900c0c00c10400310782518a26981c140e0799600501c2d0400400c03a1a5044c1070740000884024140721503641c20007966003181040500c20160303182140e41c20340e4400c4d000071017204400b0b40300c15a2541c7d1140028000d50252042400152900b07001041500d40621020b000d100700303955003c40001c88094680082c40c000d4500130610a040000081103075000c00d041400502400240c500c900e4039405020000c210351048040c0c4d0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 520970 1250 519720 519733
    0x1060e06010203070b040c0b0706020c0d0c02060d02070204060f0801050601090902090109270207030206010806010503010204050d0201050306130e0a150b0306040f03020a0605010b04090c0206040201050904091707030203091002 99
    0x1030341c0c00015210105d0300204032100c10344490504815038006038120704525000050060244a10b58004102000f400c408840c402c0b1070000048403080c8a010009600040c00c200b001c08900c0c0540250000e14001800011810359501c01c50012465a9100c1d000994451003041140d42c1c014040800030810440e0951400300030100003042e070744642c010a0007050451405c4514800181c86400d080280c0480865179405542000f0796030309400d204614030348c0718020011400c3c1c2018001c3d10b00702c2d4030150100d0580c2c1e50640c01074410742c10081102c0c0d0443d0311039a04800d40c01e00b5000380b0360a0f551100142c00120b010b428030701d8004100d90790081181d418103600208944000640c1c55009030000c100d0008901c50b0300d006c9003412007200b005403d1a0a0000108198a8840003041102c01d400401c100d042201d40081c0d0312000101c0e0080d0200303105101054041c186070b0061841c05120b0150b540705c48101d601100d1146e0443c100035401a13001080c0e1591505114240e203181c80181e0005014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 522220 1250 520970 520981
    0x302010806040c03020f070f0203060106050a0903061a030a0305030105040f060302090106050702030a08070b01050108130b070503060102030408030304060c090e010308040302010e06040509070804060f0b010203030408090616060203010801060e 106
    0x41035001400d0540640e0340d814030000064400d40c15111135a8140004690300d00c09418035203030352810280c1c1a44a400341000004100d4024004ca80c0c030f480b01a1a0810001e14585561004008804001103929013454110750940e03002d10481036107500c2901c0f01512941000d0a01003140c40200150302c10342d00e0b040040c8050f03030320703d01c2c2581151103610303103560b440701d403440401c1c240403440348020702d0003101140c01d03800c022016500a040e1003080e600d00754250340d100c552040010039544003400381c880840c041060320b031090300107551000301801240c0c070740ba82e103014941c5194000c841c1a50219a100301c018461031780180082d0041a0309540081a0350454072641014481c0b0301c0000d051100c0b210011120344c03594816180100703401082c6c0c070f80502e450034024290241c100e8048810310700e000c510703000d44119403086811801043c0c4c01141181e0b5541d540b00060303805981c5156110405000552158a05841642815100c2e54000d031300d0b545802129070035942d0603088000180c80c080b04001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 523470 1250 522220 522227
    0xb040902010c020d030507080f0301080d05121503030f04140a060216090507090e0106020c100201050702070501080c0c010204060906020705010206010b070b1008060901020a09050a050d02090405011107030e03010b0406030201 98
    0x242d1501110044030f52941881c0548580c031460f80c0c020020344010030309003201e551040c0554101c84015081e1040710010000c204c0703c604c540641c1d03442e4082440c0200d5450754039500c60250f02040a000c80349002e034100da04000940256004100310f4984046d121601c0c00d0040d03207500200400d0005011b140300b011340c1006000100d01541c03c005035500c00088503c0d114155203c020011300d01c0008181d61601c100039102e400c1d02110038010144d000308400d4a03441445202d12030100c1e036018000c050b00300380044a90300070113001ca2038510010f1054000c1c092003072005100030300c5242c8401d4400c924224029040501c1c41d80880d0541d08003d00410880c51141c0884040990142c00c0c0061540c816003000d070f00341c045401044240c4070354010441c248030158014441c02d842c64965000c000d5541040281451040c0034040e0440061018840103003400c005144d001849072001003162908a0545211900032110a0b00011000e11140003142820b00c1070b48818041581e00340a034074110340018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 524720 1250 523470 523487
    0x617060c03090106121103012301050105160c08010b010908010203100b0904020706050108010204090b0d020307060305040302031905090a06050a020d050a090e040803040209060612040201050901030e030a02010905010b04090201 99
    0x1030984010000004a2500c000c1d40042c000d448002d0740c0d04003098681c1004204185818881e6000758a448044234810302800f0300805429421a00c0c0b0003241c0c01e0000445070741c2c106807400e800c41e01c0e070b40f11090001820008c02c0009007400760300004450080030300040c26211217500264a5902c1007007400300c0c41020140100640314480000c55480400c6004907009121729040a0003483c80c10002203500041900248112100d05606000b04014882006100c550121303000358954004070341048200e000fa001107a1242c06801a42c0c10180641c800ca64907007101d079084400190009181d419a1030400724041c06440300c1e25155042040540001e513480314100f007004248200890a10030851251848802902c2803448090039400c00e0300d0000d507540c1060701c04a129122000010b035490070804142c0d4002d40c9000d141251545681e00151240c0c1d001c1d801460400d0f4a9030b4050404d40000c0005248500302c65000107186c044030300300142100d41442010340305600303164803100540e0740035191 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 525970 1250 524720 524731
    0x6051602090402010507050a0308010f0b040e04020f0402040302060a030b0411040305060f0402060c010c03020903010b06030601020601031407150203030a060503010c02030703050d1d07060206010801050103020105030103060b030a0203030d020c01061706 110
    0x1140c00c5442e1400180c5840c000c0c0000140640300f00c625060416902c400030034100c0d00c16483d845044e03600c49450b0341440c003031401075118008401001902603c0e240002d20701c030300b60142006182030303200e17000300d40d181d030201e60306e00d021a4507a00322401a050038441c0f1415001d40700411810710b411075880c65224480503000c4400100031401090941d40c40804a550004014000b081100029000038000c3d4020300c81301d40c0729503c0c00250b00701c0e500305003089910503001607001d448943e0840ea80e00207041d5007c41c040c0200c3c400d0080115030350200785141d40c0b00c40e40da070f0004d43e140e241800c481c4c2e00766181d07a0072550203641040c0003040f2040c1c00100303982455600d400d105440c0c0700000c007000003c022003075005404d00d400e0035500090000c081135400c2911455820b41c1c01507a25000703014203940c401e00c002070008004000401c0400c0d982d6000488148004044e95520645600000d24681001c1d007c0d0324070690010b04250444001d01c5194020014001042d803100308441e111a1640d100400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 527220 1250 525970 525979
    0x40b070e01020c0306010807030c0905010303021c020f03030403030902130603080301180207020901030804030b010605030106020304090905010e060a0501080c030606030d03020304031e05030103060b0904050703020f010909020f07020102060106051602 109
    0x80006181e07000780543e08441001a0880e816580d542900135690300040c0300a6400241d03441e808282140c0c40c3c081c89046e030342c140e001040d411a801034500a82913102c04100c0841c0296841c1250042c2e05000960040f40203075404036688495004009450b90a010b40e400c60741e1601d6070410000e403054050702e0442e400303890b46035400080e40d02401c0c040c2c07103407000083d030240c1902c00201c104000d0340c1c05441aa801145e5100c502c0e80c0380c06054555120a000700070160780280410003800200d42c1110900380d1041002007558280001078600d0070302c040d0b8890030002c2d105c0e801400066800c02c142e0030b0810048008105a08103040441c3d110040780b204001050b40000004007070501485407030101c1041d603005015803c45480004001d9002070204403440c50034108500024504121800d00880d080345c0504540c03481c55081102a101d00900c2074103115166100188503066031026010101c092201c841e50b07201984002403c10805030000d10030f0240500000324000400610744268550585 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 528470 1250 527220 527237
    0x801090209120703050105040516060207050d080c030a030c020d03020a05031305010e06040302011406040606080609040c050307120204060e010e1303020a02040509030c0d091203030b0402040306020c0307031205040b07 95
    0x5000c0b510b060710b1919076074264441d006000081120550140c1c1c0320714003500548240304200c071005407000d0300ca48900b00060b800b00b5010310451078000800303001988500031452900c540c500c400b50031904880d403a400800d0740c0d00c4071f41c03540c44c3c1c040c014180307081044d240840c901200313050098517500000d8905400410b200314200d003080801d5102054180c0500c046036a103140600c3e00038040c03d007070503001800e10407010120381682418042c80c030070394500b6120b50a5030b41d603080c14003e100c80700400584150004040018417030300d0501229018100007440180115854014801900c85079480310b20510b003036400400040d030b294030750207410407040300e258038071803c0e5130a0481c0b03402d080c0c0c5400f83d44903192909100a04000000900e482e46958041d108080c0c1101c3c4140d511411900c12071b21410030104d08007001a11a40c08103480030b50003040141000d40701c2c2c403035800300e800100040099a00020b4030030b0915070030100f80e4241c0125410306111a107050742c1d0f410381803030b00a01480c06006062 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 529720 1250 528470 528487
    0x21c02030907080102030408040609080c010f080601020c0918010509060c0403080703030e0106090204080f010c020c01030207031701030302030a02060901020a09090e0102070f0501050604060816050108060303040e0103061a1008010902 102
    0x9020741002800d01d000217544034105810500303001e0740980314040c042a181d04c0001043d900c00300750b030a1060380503140d202c840e590149050b5980c2d0342c01417072681140910480c01400d42d982c03026aa010380e0b0700d40c030402d91074040c901003d030031114040c004a03260760101080121810b0700404030307010b40b68050071658840045c0c1ca816000351040c4101040d09500b004404190701c0b10725030140c001c585040c421207c041340c10004007402c0b29100c242602c010f801c045107903880c80d400380c0c00810b0802d1081c5032030030361003561200e4089000b070700303030021801a08000340fa0310000307604000550300a840080214504006400041d0140c1820b114000020344c41d17054107180c0344400e41c16144140d40040420310407108500d03106c0c1c02004119601d42c402c910b0400003141c023000000d0392010180c4070040c520b10a500f40401903072880740c0200403036810320007000007250024044a029000314814a004030f0803144210003509080c1d42c1e09070160107140704144881d5000d07444450541101c0c9040001603891210 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 530970 1250 529720 529723
    0x30e0303040b12070e0402030403020d050c0307050105090105040c050306100302010f09050301020703031b02070e04020f030703020d030207060305010605090303070311030412030c0605070302090603010306020903031c0c09050301021c020309 105
    0x215800912128000301e01c0501203915103c02620500c040e40c0d0350801081700b202000124041640d000d00181c3c00304108c600014003800080072612403803005c490500080e640d40c2800e44400326450307403940e5165800d010811001030301000103014110040c00d45841c02030700312040e4011910010f0304120a198050b680f031405411000040d0101a009644e503040508015010301641010405801e40c04510780030158404501881640e2141740a81c0c0261955000c1140100501d0509a4580218140080107a4400c840c1048491184c3c02800c002d07481d1160203811100d050740002c00b406020845200b8568021048401d4241e150800302c0c40238101401c17861550090750454801031802424000030f154000300c90001c00c521a0b042070010366281e020850aa000e40310300d141d0050b101b80700610004080350060100c0e2103024080302e003445c00e8121019403003085805180f2000e40d0b036007440e40003940d0000c140c0000d0036055000307502d06150041018075000c1444c1c00d042c11158007002060b00100c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 532220 1250 530970 530977
    0x7030c0305030604150303020a02030615030c040e030904020403031d04050c0304030503040302010b031f0f0608030f030405010b04050109020d0c080c250c0303020303100603090507050d030c02030a050609010b040e0a030e0303 98
    0x391507450341b41d1a000e5501c07007410320242e1280c0304000002d20002d00910101c0d2101401030054165450114140f102038611a03a0008440c041403203c203205481d2032001d4401076010360b81d4690f80108012900c1d000703510b90440140101d091a08100700c00004108030703601f260b40b500e4142d641e9940c50604038014568030070095494000c00d400c0e00017000c40142131322a8454000d0f0100001c0c140441aa005c0303030001e2241c0354640e001032000b10b00c91180c1e000a1640140101d0000c10985811000502240c1d0700b40c001e41c10007603000c0b640e080001103a100d443c11009050801030301034146005a03520310300840034805480c1402e05000400b6482d02d41885500707640c8807980040d42522460040c1d02c1c1d070030443c0ca03034280082000c80043c40ac0d10a00070346500d80e4001000e0042c41c1d00300024002000c209123000d80c1445404c00159006071410400e220800f406100503100e1401d110801d1400c1d1142c50000910503810321079004208030303002c00c00b910500c0c0d150a028903d5400c0c2804a4154003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 533470 1250 532220 532241
    0x1406040c03111903031107050904050d0302070311010204060504030b010605090a090b06070501090b01030203060f010f061407020d060506030105070306030c090209030c0306010602011407050301030b06120102040902070606030c08010207030c0305030604 110
    0xc2004001041541042c2d035000045078600030b48030702a232200180702a04a003100d014007598810b025004500c3d01030360050115078001e1816151902a500b000c5081e80e205034000c80001d2000581041030240306078800b40508001d2078080c0ca0000381c440050b118403114068030304495a1501e801e50160340d2132081b140c00341c0d8042c00921000189003400344642c0d40c24401031f07001c1c0c011080000d00540c90071303070390606880e0003100c3e418201e400c001e802c50355408800b01c114050384003005260007580c0c0e040d0115400900c02c01c4081601d20b061000d150a640d800f40c0b43d90281800d10303005100040c1c0842e4040f00741c0360761150050300d510400c800039142030400c44140740c250041c80008074056a040d04800d141c0c40c20000c00c490140c99200c8100c03400c0c442403001410f294125030110f401441c08114804010304128009410291161101d004a030712192080f0740c950750300c49042042007800782c1414001d041c0c0300c00031820005291009003096030030798002002c00900000041586e0343d150f11001960 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 534720 1250 533470 533509
    0x10608061e10050d050105010503010605030a0203090c090a0911040c0210020d0603060203090f06060904020d030f0c060507020705010207050303040302090103021003060803040b0a030506040c0f0507020301090b0f041406040c0311 100
    0xc20420b00242c52a80201e030115007003030822002143c994010000c8a04a41e826a111391a40e5903030000715000303400242004110340140d440510b955940e00e40a5070040419001c0002c100f2428508075500c13060359204e990085040130410350800342c0115254503000d0010801680d50050741144900a0a140d007004240500c08400d100318140c000a030b0b000d0f080103c108031125502d4030410403034914011900254424940206100000c1c802e040d03684085006013400b004401c1355a80c1e000c1078440850300742c1d0060307119910401896904000d02c80050000742c000c1c600d01400c54011502ca0031050001a0003103180103041c80302c15200303900400051070a04c2c01c2c1da807074940764450840998406100940003d04020210b0b2441c94144111031040714103444a02c4444861541a5615003207841c081c8e915560381c0c204100800c0001d0318240c443c0e070102a03628079a18040c078096116024102070f0100540c459010400001c1c007940403001900e8200e01404502400c01000820300000f803001c01c80d44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 535970 1250 534720 534739
    0x501030e030904090305070201091409010513090506070305070906090302030d0509010908010c090306060501032904020d05010807080f0f03040506070606050409050a02130c020703150b030604050c030d0305010608061e 95
    0x41c5a1b00c04041c024040c800d80e5111281643c2e6540100c1c0000c280c00c94590180c4124010865071400c0f013010101a01c80c81c001041c01c80c120303294141030000845030580842d0721541001110356210f4265006440c0c2c50402c07900e154119004651354505640b8824244500000e99442d1a030003458284024884100248500064154020495450b0303200443d4442c2c1840f5011070598000d00a84043d01e1300c0890385241c0c40e112414403103540f1864003050b50840e60070414400c080c1c40a0040c20701a00c0a8401000580e25050340700e49480882c59266100390407110604e01c4540d0040219404c681c4100c41d001d03201c001c14102500180748540c0282e5105160070000c0c4100310340458a82c00d003900849441d8021120306a0540503514134001890068101000500001d4800b101c40d4802d0584c011000805148080c086807500b40c003541d0a80700b40d030200c09450300504c0c0c00c01c2503c1c10b07502240f4044c061540b4020380076041980c05446580320740008604146c0e5807020450050703240200800e44c11300d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 537220 1250 535970 535973
    0x60c0a03060e04060c03050606070503120604020d02040306020301050909030702030304090b01050405120105060102010b03070501090605030a090606080f010e0109020906060304020102010908040b0a020f060903030103030c050304030506011401030f050106090501030e03090409 120
    0x501405c40f001001c03d080400081d218504441a00d1010b074116002d1460848003030205200148014800c030381c07140c0d080c0191581c0100741c1c07016101851080300c0050b0b9a5040030b0400650003401400c4602e1a0310800c100310041e1070210580b4201e0348140d0002c04c000c000340005031154081c9800130303600483c0c1e603803081e000380c0e105402c50790190300c00ba00200040c022003810716031220664004c090204501756010000c59204000941d4400c540b810700081c8001c075a51040c0c02d481c00f81e804002030b80d22004d080c0b106032000b80715413224922003c00800c200d02c0349078080741c1101c0740202803c1c810a00480042d0540e4000e4014540040d4881d0341142c1c0c864445000601a4000c00c0c1c81e000140703c0c5d2518020b260a00180035800351003624002d50443c0c3c610390301110b040444003821942c41c0014080040010420400c0e10b000c0c0901d0110018541402d50004040b90b6550070311030619401d08004001d4bc41d0414900c1003628400c5c0b0340840c1070249000d0300703403440c8140740080d500325207044074220 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 538470 1250 537220 537233
    0x10c030507110606010f050c010b0301020708040501170112020103020a0201020c07030b010f0905190b030708030c03030f09030304020a03020f030c03060c0d060602070b0a0f2a05010b030d02060c0a03060e04 90
    0x18807030415516242840400421002e5856070102c0e2100d01050000d444c50031810301803000352421841500011070884d8001000c00d082ea04224001c0300d40900114040c0210f6030131800d84640641c01c918028101d40c0362004081c0040c0983c20302a06256000074401500d601c00c2d01207c0310760002604481c40c40b42ea034501301321101c1c003d20801c80c4c44d0034014004654411a8042c0501840c1c49041c041c4034040c08501c40740040800c040440d5051180910000718078100f40044c0844c4034100c0003950303d82c540f08641c6502c5120061070458560001c004020042eaa00001d49040e00d4060b10494080d2190078042454080780c10b40a90781071052030100041040e6000003410880b2030f038072090010302c0e41c071841039071b0750030b69801402c081cac8006206240389a4071540a40c80c07101064513046414183e011019555500042e40c2052945225414003080c000240141c400103002903000b0000504040c40094540303002500c0c1c82d0700401c001a941d5195482500040041c00c00310070f040243e8189880c20f003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 539576 1106 538470 538481
    0x60103020418140c0102010b0f0117061302040801050103050c01030c02070612020403060608010203040215040f0308160204020316030f0603030801050603040606080105010617010e0c04050603040c030203010c03 92
    0x34041600d89508004020f142005007407549002c00c002030079200341682d4140a8685494504440d0744d0000c0103144000c010483c2e500c081e196040001d00c20507400c040590981e0003c20040307a082d4041d40000e0490b44104119000004800015001e0319403103100000581c0013003c0070400a8003800c1a00c103440e80107400140703003a4030ba640700030032981250080c4005a601108000c21403c4ca80010070620401240c0982002c0c5400d480380301d0780d002c83c00010f0100c0c1001c101001024940714901003040d60042c0255100d1500c1000c10680e51642c014410000c0d007400226455401588501415a90143d075001150b80c280014000c059101810403554035550300e00004440301c0a00c1044d0103000c1030ba41b07242c04644150b66148040c10184c1014640f0000d071403e10040503145022038045660648903981c0360b9507507081c00c1c001c9000c158006509542410b400911503a07165011 = true := by decide +kernel

theorem cover : BRFrame.Cov 359720 539576 := by
  have h0 := BRFrame.cov_init 359720
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359720 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 359720 ≤ n) (h2 : n < 539576) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
