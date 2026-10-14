-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1490
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:14:02.428259+00:00
-- url     : https://prove2.me/submissions/dca81e2f-35cf-4c8d-8786-62933e73769f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 267805755 ≤ n < 267985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 267807005 1250 267805755 267805757
    0x91109090a020a0212030108010606081006021b040f0e0105060a050f0d11061608031501030207050d120b03160503060603012706090b0f10051009180213060f080f0f07030507 76
    0x14071012000b000340b46d007003604101c07101da64946007001810340c00201c0075044900d542d050542c59003884402501d40302070f01d07880d1903201040b6030f0a00103a141d55005100e0b000c509001009013190180c81103010301380a940d654401c4014904c0801e0600d4480e944a034807104c0100701e60340c500c1ea241e503100000e407801d101041e8406824080c00c1020125105980703182072107110700543d00d00c2c200c100c030500138031520205810188140a1400003a800050201c4a040300782400d103c0c411183e8610f401500381040c0d42d0f034250243c2c5050081296000031b2040a0b0f4004505071641d6a84d04403c2c5400c0380d40000c261000d180a90540f85801401c850031344503c1030246101040c049402d03151081502000e80d1074103807038020304003000001c584102d40c0078041c150440d031110742200c03181c00042280302d060058800201907400403038220a01c5504842080c2154030001004a9403800302500c0610021a100042804000041c5101c1c0d00304503420320504410480315400d441d20802180101801051a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 267808255 1250 267807005 267807013
    0x18090605090601031a04151805030d0f0b18010515250312110406030b0f1002030a090909080403030f02031201030c0f0608090c0f01090e040b01091109090a020a02 71
    0x44081111401114030900c031680080499514510713282005803114080824044003c400344000502c5c0c800c0c031705039091880180824200b038410107440e07108001500040c142c0c4400140b030b980040451300300000700c58516904200c03040c445070510409108001688440902c11001405140761603841030511800c0820624100a42c2b900b440492010404103050028078606154040544c0221200185d0a215070103024200301240d14941f40c0c003941c084c280138103171a1041440c4a480e40c0d400705120040040c804010b540764000065102d50180e50040001800c501000c940d860160040840e4594484080341c81c02e4510380701101c40405011030181180010030410110000202030980a58080e241841d5604d150410480d1301400950041c018082e0700402c00c000c00c80040340501c903031103051700c0044c4903043c00030040390300481c142c120032210380c02c078018002072141f0950760354107036034a10804001d02080b41c01103d8040c01a0f503a504e502c4440f41002604614070758015100e2030207540111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 267809505 1250 267808255 267808271
    0x50c100215091b0303070320150406020c1912121107060c1206080a080c01091b060207060c0506130203010b0d0b15040e0706050a200c0301111318 64
    0x501403040d0070749007030301030703500c621114007000d44a0301c02c1c89403e02c4200c005514101507a038000d804e60300610302c0c084140c40741400c00802a0000d200009001c004003070b6080f40c900d01864100e00a40090040c0e05403481881c0700d141452510440c0c0c8150315800c1002c90145078003600044032007405034003c403104d05440752100c0b119900b208000d4160148034100200b0000000c600003081c179107400d54080902ca007000f100700b04a140100355103080e2504600311940d603000c8410807901400640000404000d01007582101000c1c50f0380d20401610450303801d85941960740c4c42c0450f21200d41180c0503040b90090000704070403021501d041208144054008258681000c000489030320103450251050041d00c0e040200c504854840c0c01003084d0102d8080081c20082c0340965a1030009009010a200c000a0035003030181c00f076504540b2440e01c1c1c4a6581105a402003600c0c0c41e9007030800014001e41c2400303400100241315000342c4102c8082080740601481c5007103510941002d80c4407418542c55075030040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 267810755 1250 267809505 267809533
    0x5160f09140604090908031b0405060403020402090303300109050106080609040f0203010f0f0e01020301060503060d1a0c0d0c020706021c0903050a0b010302031005010305031801020114010f1d0103050c1002 90
    0x40c401c055030151b0b4400c2d44a140188008004640c80d10b5200303260007040109010319540d503c190b0b4242ca80540300142c40d0035026001c03d01e0361082c003042c052950100c06000680c0101010700400b0994520440c03d40359903668003240554100b0b0051030040340c824070021b011810020b02081d030041c01035814a60b101e006802103421149a000c1e0300c0303500d5443e07494545900303005001c1c01d07000300e640500851566143c0b640080c054040600224464042e88504800303000801498110995080741c0e19a164181044501c0065100a010000207400c2800b41c100160000c600b04003240d5064018000e00b0314514608041c0c2d4080342e078140140141c0c0d91002c07000c90803c008015205201c2d140301c00c525411070040610f030070442e4803e10a41c44c1818018000120040140d50540c12000042001500010010303030142c5010b5040400c40503108000050300110b401801d4220303100b41496810040100d00c0c3c5078003103182408084d103035502c20070b8140700300d0400340c0e0442c0c9460128030549144c0114190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 267812005 1250 267810755 267810761
    0x10e0a030b07140715050402060724141e100f0f06020c0d050a0303021305030105070e09060d050c19050604080a06050a02121801021b0105160f0914060409 68
    0x1070354140c84907010081e802d50000507100714003e01007502030a14003644d684130005016000c005c082e5a848401040c219140c0b0020340fa5800e6000d480143c082c0f042110030740c91180d1034800c84070168140500f640c6100c280000442c029404c2c0a68038130800d6810304000000300e009402e4544a00005c132001030800102400040500713078850b10001403600e0698001d250506c10406c0900c6180f101040d070001510001d04800c0c480c4d498103025841e000c400500c000203c0c0c503a8001905075081804108890b503000b41c4600040307000f140c1034006921030400340921081644d074004d10a038000c7d2505400b0b85084d4100c01040301c12601d1003095181c0b21004031701b090700942d221000c030f42d12040c5584104080341c010a40d004994003421401d02120031840c80380c3c00c1d0050b204810780250340c604002044029011038201d0789100d1040502c41c10890401402804110341041c407004000310500c100d01e2140c903100d048424a42e440840c16410305c50000100c02c0034003d11940114101700005003221980 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 267813255 1250 267812005 267812009
    0x1905030d090609120807120f06050a09051e1003020103050606160b090706021209010c05010e120403060b030c010f110703050d031a0108250c1704060207090c0905040b010e0a 76
    0x28002189a421078509408492140744402c400d2017a9a4104a140d030341c011185642014100004548554000720400003031115402140d001240301001140b0040550410f41c0241c02010704040c07244c6407080c40351102a03055810034000d180207003042001d0340c440e030400307504800001c251074584544a4000321884000600c2120b07904601c0382003282d10101809044020200390000e004115000d03120003000e4800c607443c2c94107100c80b104900003840000d521031880c0c0e2a44208440348101550150502a0000e1104803259402d01000e0242e03424040307001401002c06131508120300022180a441d01400020109110300c201e20000001c00c8003045522a8500316840004111200d400c24000d5900704003002418044030100340140c41442d242022030101c03119a054042d000119070440e1400d480000c0a40200350401201c40e40d4055400100704642d02c81d022103402d95a0303001c121058035030105844010170b88a1000308098101600401c1400905140040307800b43c51400003900d40ca140c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 267814505 1250 267813255 267813263
    0x1050408010e0c0306070201090b01180f1508010b0d230a051506090a050702070b0307200312061801030206130803030a090c080a08033c160903051905030d09 69
    0x4100f401005041c10b004994218900c1d10082c4400807454075502500304c4188203e80b24404000104411400c07a030b44814040b10803a5000e1000300c0300c0e0040c001800501d800b402d1015440c000404e40d139440c20b01180c19106600c01002d481038010b03180501c6002440c901c10400c140030704103140c00004c90500040765101400054010b490a08406001c002d00e0010f180940b40c1d0b00d000248050305400081000031a0248101c0301d66903a43c0000841e43c8500c1124264105040c40308003010801010029203110b51407800c12044940d0740204000c40c5108440c00c4c03100480da60302c01440942051001001203a80f5002280c07045075aa035292403566000311340202900ea641c0003031b80d0401c003200101d84020551000107100c44607041c0c482c5912480003805089010344507908131242541150303420036118007400b5a02c090302c2e0803490b00a10307190003212101e0705082c112144130410740c01140750300e0036282c00c070380100b48042d40ca40c0f21506c4481000300668252105100c552500000b500901081c20301c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 267815755 1250 267814505 267814513
    0xa0b0a0c0312090201050d11090a180e0303010e0411041401030b04050c04110a05090d0812041509030c0b0403090504050c1b01020a080f1302041118030a020a1401050408010e 76
    0x641401002c0c624030a02d869500c900300742001000d43e038040705444c00030140c8000014844103100e00c0090903c80c07842c0e82074201820410000359a40c00c04203000044484202c24404400d0050299440c2c2c0310034014202c084003914041804a000ca20760300d548a40d01910018982d000184501d008200980c0222545400e00041004000c81400b440f5042202540d00b03008000c094540940140640807030a4108600400e00e041107544c4e11440e0f00a43c2c0e0454042c0399a684540d41d01d03082010102c0301690b9204c01170001c5402e00c400f501c10342912a80668038605145116590340720004c00141080d000c1001e480740100d810303952445041c1c055008154425510216100c00c0c1c1c1054400d50071740034980c2d106200d0608800d0304541e00640c0800405113040d182e50750104000020a0990b20203504070b480c0c000e20390348010b9580000c0c0342c60040e20003500c1641c20300c941050350341c20a40500940092000c07004010f12448019a00054801414000d081c2512100c6544c00c60340205041241d50788 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 267817005 1250 267815755 267815777
    0x3011d0c040905151002010b060901030e0a020d05012702030307120e0405070f030e030301050a170708010c080f0c19050c010f0e07030c0512070e040f02030a05010b120f06060402090a0b0a 82
    0x10380300200081761902800207000806a150002d8142d0094004150615071104114000d90074107100d1900b185500400c1c8850001040c10954002c0001206c0600101c181c040160006e45022811f4641c55a000b0021417508119550f120501151010a4414026440907610450303540c2d0003000d00c6042951b940410304802a00c00405580c110b10041c00b26401c00c00050081e500c0b44070012050300d0400d41c56840f801c1c05080c08620700421903124405a5107004090a81ca545c841c1950b400303080030110038a030944490700c2202c3c50f44a0361100d48810340c8011413842c3c600c1d00400c0500100b215031000080d00c0ea920303030841d1040d51204400084150810a0203008009424140d1000b810007039a10b0f0481c0045880726079542c500500ae48a03140f80c8000001d82040903201041040e50780c0a030903681c0d48070552518034060054800e90301e12805a00345880840440084c0000d0300ca410080141041d0f00d40a0510000b54040302c810358001c44805408074100341900002c020006a03030340c031002900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 267818255 1250 267817005 267817009
    0x6030f1a0c0903031b12030c09090121030c0606051c12050c030f030a06090f050709081b010e030703062a022a01030b0307090204081203011d0c04090515 67
    0x2402081c054040310180300c008100e0314000b00755907400c000360b8000000244241045407030003000240120311030000204000f418101c50000d0104c2c0042600c03c40040d90b00c41d110700b16100b2641c4050348009001e200e044c0301192041d007040220a0060000149054980010803800702d000c0300411400410400054200b041e540c2002c42558a94503109050400b01c0510580728426800c82c029002004008111810065400100105002c1608002d102c104940c25800307880f0845005010680010000030b61040114420f030034585a4a414080000c11034015501c000908040641604c546840400025100d1082810f400d40000004003e41402c2503d8076030345005440440844d00014103940c845842c150041d03141200905600d060740c529003004a0050100c0400311f54076109041d40040c1075440340d401041940c074800705807524038090150501543c0300c20301c031701c1402038583c6040c60b01448521040c2904084a803010358039041d0384480c940161481030725203190f60320030100342031024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 267819505 1250 267818255 267818303
    0x28052706030c09010521010c09090b04050c0f0d0e010207060e0d0207050d15020c0a080a0306051e010302070816030e01080702010911010809031b0a0212060c0a050d06030f 75
    0x32003011001419000314035404211100c00c10300c5143c0c000c1d0303202c4521032103070303030001031461441c0752024000c000c00c10071018010880086846411a09441c8c400c03603914500b024015103200d00d00040100303280c0b034550f00d040e030b035143d00c00d289880446559203004100300f80300b8002400b805000b40da0204009840000043c00c2052030380c00d0300203640c4030307020030000c1c1d80b40c101c21580da03560400c942500f8441c2c0d624141c0c000e4801c52903200c0b03a0740118500c020400402401800304012282e07001c00c0441c2c0c46001307001c14031040c51007410301159283c91030b804961081c0c009140c02449005034078206200180caa920400d0940c5088022400016201026503400408290b002c4950300c001d016900316522001401d405c2e80769400d04020310540040e1440b6420011550381130900340d889041074007021407054651300b0658040b40304001c04a103d480e030070300c000340350340c0901088039000e841c04000120942d4981d0140316801d208076281d99000000c150017102803c1c016020b9513122042e10840f0302d803511b40e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 267820755 1250 267819505 267819511
    0x60114010903021503010f082404030309050303090a0309150c08070314120106030b0402031501110319090905011a0d0906110c030307030b040e07050603040804031211070504050105280527 82
    0x1495009c0d540e100d01516402c0440c0780600c00003241d00c000c80c0c0310f03810120007500c2005c001500c144000400d01c10008000941c00d40100d0207a640c3d0480c00d40c03200c0f0860b01d86c442c1e00c02c0a00014550080800c08140b0500081400c80c0c4242001013020040c480e100e0b86640162503050302069084004101194050081041d2600d08803003c51444c6001400b01d10354204446100e4100140c80b03590307880c040d030104212002e0800f4020031440b04200b10000070b020002c1e03400750120250811000081c11480c41c2202c22880c010b50880318140320030850078000402c2141c40941d407540c1c0f40e8060114075111003008060964002000e1030b506e280c50380014055804000c01e89010710710b06501e12035071841c081020010303100200e5049542c0c0c0c541c0d0402402074001c47c1c0010300b80300d07c078101504500b03800018111018181300c00f50303840185e4a000704001c8030000d1155981085100b50080d10390700740600c80250444a00b0060010f054850020400710322449254901c040300f410201605074002c1d000d5598 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 267822005 1250 267820755 267820769
    0x403110603010e0f0901200706110906030f0c130b093109030509091302150705030406051b010509070906080307020a03031b0b040b0a0e0609060114010903021503010f 73
    0x2280d94941880300c50000c90042c0150303561450540410071480c000e4000c800f1f003540c40c1c0310040c0f20f1200c00850b2219039100c0b00c002c4440c603203010300b207107483c4450405461105030000c040600710342d503140802c203c2c02001001c14243c682d0030481415100341d40c0007540040d2490031019a1a1240e003024444903000044c5020103401b411500c0854940b0810251401c110001c81c0120b108441441c00392241d0080d2030300340740d01503008810070224034010511244505e0003201c10005e400d21b1030007600824815001c0161064008000c1404894042c4008040165100351511000c03072001c2c0450b42150015158501e0581020b0020409517a10b402900e01518410700510700e094610341c000f410604031031100030123204032010118220195020b21503440c980095106080b071500349094030740c00d0000c0360700b802d80340e14000c00620000300000e01c4a1148210750018820740c3d0800342048046405660001c1c100801a6008001611103a035580d54000c1c031440d03590740b2035040525501c42d25039282c01500c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 267823255 1250 267822005 267822007
    0x102001020d380a030b0a090302071505090f0d060510060207090b0f1915020303060306101202130f0e030301050f09040804060c0c030204020708071101021204030605090c041104031106 80
    0x14440116480010442c04440ca280d103400d03200ca10046210303011950303c058801ca01e0300040250002d241c0e002507086a109034266001d081d191100b803080220249413210001d0340c240701540a0b403c08815141f44840c0040202a01415075500d0303c007911b104446908070f41c110fa4004015031a01040110090101180180a8a400040803803604407100726480c0c82242940a03503800c0d56121000e80028014400c0f10310310000300914040e550790310a4075028068410000002c94010803148948150351b190340444546203040e03000c201b0200c01c0041d421101990302c041c2041c05282c284519140758802102031900d81d0701d0a000c11100c83c0c940c512190190f201c2504200015142004960684000d0b084c05200d9030210300b040c400c10b0080b0b0704000d401c2880010514184251750003c0c02440e031141c8900c40340c04d001000126100d4102d5520031205c0380050100b44000344054114960140d0054100c1d000c2031190000a02500c0950b41c4008810000080178010b00601d07540307151403404280d44807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 267824505 1250 267823255 267823301
    0x7050906010203120a0b10020706020d140a03020a020f190201120e0c060a0507050318091303080c0a051306170a060b071e0215040503010e0a020f102001020d 69
    0x30b500c81c404e8151007010328240c600028546441035009190000d00500512841c0c40603010283d80c03400c09020300c1001d481803145016500784501010b518001803c1c08590038010790103420b03806508500ca0f00e2007540500e26004041c0401040240000d80c080360307500040640500026100840b802c441c0c000450401c443c41000342c50008039501101800e0b07840d15034541c3c10030700460b03490041ca8802415070100040d080c2a61603502c50600e021a0220358200041d107a45c81080803108807444002c0c0451403c01c001f524410124020304034008181c1002d61030944c1000b14001c14060a0701b00d08040b600d610b01000641a4014166500411140c0100300480c18041c0030581070103162401480911031064541d41410511f0f00307541055070141c07500e4807509900a040d25560014082c083c000e40c0f0b0041c100d001e040000411406064000d0141c03860014003030184400e000c4200e042405001c2010f040e60300d040c40045000c0341000444000580300ca01c03043d4841c041d14506010303c01b40c40e12000c44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 267825755 1250 267824505 267824507
    0x109300c050303070c08070b01090b12010c0212030c16060504050105101d06040e1501080c0a0302180a020702090703050619060203030604090611040303051b0601031a2211030705090601 81
    0x3c603500b26101e803d00020500243c40c128005104010000300b40c0c8654a000140d14400c507082042d600c1411601924004844c1001c01c0c00c8540c08048600140e000b1101110301c00d40c6600110340056140300762501d4045d844c0d940403080100d41c04110303a515503541c100b1090010a02c980f940050005903600811460608400b100d94407003001e40c484083c08901003009961075034060380360301c00840c0a6400c2c20f48400e0107040d101a00344602c10580c043c02031400b02c0d5203010320008080d694010440039820a40c020369003103040005092580c2c40f6402c00c928009a03843c100306030b00c96030b450303503001c581c038a845001e01800d041c6a078203000d1480001c0d84180806600070013500e40c0b241096900240903c0d0074200380014105005058181c000d0001e0040181035100d001401c080c292850042c01d06183d14003082d9842e1024440074005401075501190b00744105031449400c00780c900354a481190202d400c8000c00c940680b0100c80d00980030090101606090048030020001200d90100d14505080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 267827005 1250 267825755 267825757
    0x70804020d1103011811030c01030608120c07030b0405061b0703090308070204090b010b040518060307030807080c010510090b090108060703200d240308090904050109300c0503 77
    0x54000d0502c04030500e849920f440944c07182881020303000c81d4000d2041c030b5082c40e03010802404001c0d1300038080c8038403448281d40240900c400300d6804800819080d482c14000c00c02e540c20000d0f2242d961b000c0d20703000201281c0c00030700c80e80c0034074000d5018001504082044582d80c031140122591455403c1c0700d10004680c012134800304882d0810f44050742c50102d07100040041001250042c07509190000108202c01800090016240c064940e0300011165403c23005646408580749945a4003544041c0001203244000c3c21b00d843c49805000c0c00c0000303462a40b03003900d07030071545260001c0c0c45410411075035441c1d00800e81a4482540c085003e54108000c050b19101c0042c0170303c01f0315894004440801c02c1290610000b0710b080010240c94108410911014190310118402954880d00a81c0f60034402c3d108064110707544001014a40990102401a0810300400c140d810755a074000040120701e0003d50b40303103810844c00c4070040c2025203100c1c4803184111181c080007002030340d01726074001800000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 267828255 1250 267827005 267827029
    0x10030f0f020d0606032102151321020d090501180504021605120d0b0909031909120609020a080a0201080a110c030a0503010311060309210d0c02100507080402 69
    0x40108000c040c460011a00e204010000104202d260020010602021070702003c141640d0351031070180050b1400c801c0740d031801c041290700f000d140c0300c0e03021400e034901d000f03281700c403a03072082c100d00c143e10b220720340f00c0c040b103a40c44030480015030046001c02003400ea200c0e119401070482400c151200309a2124034000e0901d950080f14000c5034001904501d83c0e488255800146900c20300f22044180e00070b122001682146546554503400c010440603180f5200804a12441c2200019428035052088031010414a51504424401a0344012408c280d1914141e10304e680110300108080041d031052141504140e0711611540c1c111901c4c0c0c1005030380c40001280c00599440000c24000c40142c41d42900788110301a1228501c40040c51008c0076070031034003940c106c81c0030b1400080d00100800510000388801c0b60404e059400012120381c102000041c082250040c03104120304080d100b1000c08110b50701ca01890b0b0150b80076406000039902e0b01e01030035078003031924680310480d41031550100d40c03002881 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 267829505 1250 267828255 267828263
    0x1806010c0201120204060509120d020d0f261e060120010f0204030b09010c030902010f050c120d090c080a020105040303050c01021e040302040b01030e060a091103120a020610030f 78
    0x204030300105580c49003031109070012403660f0071981c0b1652841d01a1141d448003041c0d900a00030b92408003000301c0081101c1000306580d8001d4030900c01c0d1540112466864002e8080c140127404110040c4042240509040403640701d0b840c040a017440704003044500501c1c0c4141c01d04d2080481040101d980c80101c810000c09004659440703140d03040740c49409000d01c646c1c3d00c5800362010400000740028140120b0283e12400e00820a003507a0b054100d065032556078000e404925080075090360705110340010f02005440d00c06032000365400a0141c00075502c0008502522030b260001001808808c00009004005460040005111540c001707410341c0918400903091007404030300c2966110742901100c01c502d450408101044d14801541c42d2140c1142c08140d024518001071041103500903c80d005600c20000005c20b41c0d0303512000ca00016010b1140e007165a52103410107500551002c0080c2c800f2403a03044145a2590306101000307140c0309004150030041d40780c5200400204003a403206a403200c0d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 267830755 1250 267829505 267829517
    0x4140d03021e010e0105090606180114120307021e0a0504180f240f060605030411042304081222030f05040503100504030e0a14040c0e0306010806070806180601 70
    0x342562203401082d81c4c100080c115402d100c10804c00c040041400d6104a1044454003420349a0912034400810240142c86900d182c9400d00995071400581480078070074804100d80c5400c132964042001600207071228041608200707425101846c00c0d0314928007070142036508009105003280d8564829040d0700014044021a15200c0280034a041600b20240403540542079041015680c000040c1989101c0309461481d007080030400328030401c00c403405036800c85143d07002d89400c1d500300002401040034034400803031040701c10003001c44c1145215225038007030081c4a8030741313180c42d002e0300b042a4001c02c0b8103c242d4418804a440004210a120120750146005001001410b100756407500c00c1340c1040394140f04440801041d082c0b07a8010718421343c4a0750314410785201110600a035590700d0701924040d200c1440320a001400d10b80d1280c03500c1480b0b45050a009510784000c07034107200c02a0080041c0d0f4101c0410011000c1c0c0059000350003820942e80c040030034003418420884044082c0c006030410007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 267832005 1250 267830755 267830803
    0x20606060702040209030d0206060102100216110f0a0915060903080d02031f031b08030307140d02160c03060c21051b030c09040501080705010801050105070804031704140d0302 77
    0xf03403035050701d5803540302600b1038503601d0b5403d4000e50340b10310441f545401480340c100d401c1020310300c1e402504d070001c507010100d135130901d045c0c1d0f601d400c03001240344401e810866900c0c007000940c1d1001002c1700208540c207000500c400d1141e0b0840d00ca152160046024031035020020400110120300301d40c450325a040006803a0346074200b0352a800101112181c0500710b0000c0040207101001d80c400c1403200d42044406050340d51201c00e5600ca000459212002c40e043c001e0004a0038a44401000706504096006241102550489410b030104070403c5c0c40f04800c4420510070440d880c450012120031504051140f10052000c208510049a140600842e00c401c041081e02340401d4100407803101100c0481d481e450300318061000c1350010114641714034244000082e0025010903010242e03a410307541c06403240c1c2454019181c5501c012070840d8081400c0000102250044c075100c0e89002142182030794075440d1207041420600d211007624072400742c1c100210002900054600a4950000103e603100c00e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 267833255 1250 267832005 267832009
    0x71701090501020d050a1b0909020a0909093509040b01020c0d140d05030c0f16080a03052d07120905031803071e0e0c0708070b0406050a020901020606060702 69
    0x125040400030150360020421030004807083d082680b05c0d112001c807c2062a01130f002c0d0808580208405601240d01e0786030501400c0d4444d0000d244000785414807101040d030301c1c0200c0c000c40e11806415110354008001c1b600c03031030205c6101c445c01501098000b0b61130860300c009040041c42580051403259584207440c0089174020f112a8908440051810f01c00c40d1890030841c500280c4031080c44880d02842031000c441c28015400d90780945042d451050400c80d10f44e101800382d40c00310f007040c021b201c0d2540303800700002c6002004201001082e5804a1113040c81e46200d001080c224400c0b12281541c20042079101c811300e4070f007681c44800703450850f5043c20300b61000002045042005010b90100141c8541642d1880f111191100000c3c0c045420780c0d0b6594034110040c00580d030801d030408000007410030403103900b540110b41100505062904d050020354442000d030340001405c4840d09010410041441040d00c06c0b20b0f4440c180040c107525140400d03000079241c110043c0158801c40340403d1900641d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 267834505 1250 267833255 267833261
    0xf0f03120a090602031c09391208121509070903060f0204080c01080406021b16050105090d0f031e020d0306170a030c141e0607090303140a0311040b04050f09010305071701 75
    0x146a0500403410f0310308410a03040120415080407014162380305200007000185107401d5000590030400300350801e0401244c0d505000f00c081c0000c4804494400441c00682c4c034040442d005440580360182490715606e4000c0942c0c10031146823008520610080100c0600482c1d8103d20403000d103024116a5600d2502000a00808424007204102c9400140b01040d001030b141c2d16603171600d07501e00146075490004590038030801e007042d074201141c8800701c0001034010300b0140e0614441d06245904001c1c806d58980c5180d039a586d1500143d00400780034101c079416110f21801703000f440881381006070801c0480c40c1d5460100c4e000404000180403101d00703000319264403048644181d405d80702d10701d94a0003242074002c1a4001514180982c001040c07900340176260b2070041320760545508580007129691500d80b0703000f030401c4c40e081c1525404032611381c00c41c0d40300800250081256554541c1c1c10802441070591078075040e580140c10000050003c15400200b0f030040300d034680e22040304c0311400c580e09405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 267835755 1250 267834505 267834533
    0x403080601081b0a09080601050411190e030a060f1a1e010e041b090b090f060703051c0c1404030c1208042c060612060f0f03120a090602031c09 63
    0x3041c040131842e01003c035402240f2104030b600b41c2045410590f00c420030403049901c1e20403000603101040024201002c04004030743c810302c8041c1000f0004200701d102290030001c01d504c088031090350390b00d01880c0110751446100030006a040340d09400c24040d0001c54460f2601e030904d80302d5440c109c01c1103100c17a8410325600d440c40501910070303c0514606c82401c0864508012843c001c190305143c0031070b050138580c2c00c1d1445680c3c020207000f40c3c02d5000c000e104403580300b00307000e50403c84104260b07054680d1454442000c9030107100d0000302030007003040c000c0c580c4900c182c0c0f440b0311a42c100000c1000c128401c03107210545003000000400b2404c640340449641c4519400010880701900000400c0f00040180c101c40c820041e035041413a40d550740c1001803900c0740040081242800b1000314115040140422803c60005040c010340301d241c88000916004040031000d022040001d00c1c14409603129000200400403130001318100380c581c0c419481310f5050240c0f4030084540d100c60a1050141072902214 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 267837005 1250 267835755 267835801
    0x206190c1505070f080a150e040b13030210020904020d0504050f06130b0a0b011b03030e0106170316020109080109080c1219050715020a05070204111309150305011b0e09040308060108 80
    0x400c1d88d400c2090822032040310103503950030b903400004034031414401403a5001d0350315038045c1c648410600521002900440c10154210f81e0034007881c5c1d801d40b200d1240350701036030041c0b005040603102c94443d0344c602440103046140251901c400d4800056086801d190091200de0f008a071688040b001255694003002d418152000442d04020a140d0198840b049020200009000150711130b00c1d994100c00702c00a01c030380d41e41d1081080108946044021004662052400c031042c137640d081c01e0703406d644220310f007929400d0b400216019504030030880c482d405110b4401032400c00050441e0340110007154a101c200703106000469a041000b11089091010280c03242103494040b440401000d035000000100d0146241030700c0070358190420001d8414000b42d00d40c00c60101ca041403107440c050110b500110340d482800c104003200140080c000c0412950b107090036800c0158440c80c009000302d0003091030901403120101480b010035400320034964003c10a003810742c180d850360f01048048402c5031503444 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 267838255 1250 267837005 267837041
    0x904050a081c0507020d051b0a140102220b1204050a020303310e010b07080c03181e030a110316060f020f03250206190c1505070f080a 59
    0x5000d411030980e4102c4a22444070003041283d840b9041030340c3c2d404e11203c030540464400d200c44040691070320039010a5a000c10242d42d04003034a591115000c10f081c004c10401d5075008540425450904000300c0d1280b40d03030074145410340d440d080706044d4038407500c400340c1441d0650038001010301c4410826400c155a0103011603075070b000714221708000c401b00502020000d4003141c40c4254200c8a46216109546003045101e01d240d20780b0a03810460361125a00301d8901c2c8050246880600090019000e1483c49081d072000c130703643c550700f0094941e0564800e10707096107401401e1103841d100050383e00002640441003248182956001900e003004140246c400d640c01d0383d00100e045941b25020b83d11501658088880e84c0300c04191041c0c40c1d000302d41a81c04240c0e81c08000210313940d02c40d100748000500181016190203004101790850903400341900f004190449146030030000c0b80710b60701c04144c0c00e0031001c100a0520b07400c000d201c1c480c881441c808120080003c0b510000195019441c8071003884405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 267839505 1250 267838255 267838267
    0x17040f03050a0b010e060a090e0c180a051806060405040201030e0307060b03160e0c090406180b0112090203150a0204120506040507060305061f02030405090c07020a0906050d020904050a08 82
    0x101c2d640e020801001c0b02c19914601c000100c488405e00024020000109000d00440c02d1403540e000601000c148641075214040c45440962524400560714003600324120109140c251303230035004d03620043d01101300c070512020700d08014107002c1035503600544211008180c2d40c40710b000480281c4188903042c0c0041c0800034459003040079943c00300210600682c2624401c3c40d42e5640000045401d100d0900000b0b901300018405141502c010043c0c10b200a10006940da1104400400d04030540304020030303556180c960202560b0800c4840a000103070010a0003440c40c1c9a012a1b2510f400d07035031800c2030241d80b03c081030508100c0d40580b0b0142003851b8007909000c1c0d550603c079580e84030070380f8291124022200041a050f209004291191602409001041c0400d0034484100174980c0c86103070450100b4400429183e44150b40d040c01660014421030700d42c50180104000324401d64400d000c0180b509104201c1074607000000c1154540444000c080c699a50800c2e0341451b0503802e0040028400040e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 267840755 1250 267839505 267839513
    0x120906020a050a181401080a18030810080610050f130c050d0506060f03040308100317070302010518070504020a0219080417060910180c09290a0317040f03 68
    0x103040d00301c25640d241000c502d4a213082040f040414011019080303c240302d82c0d07400e5402580341c1900019a20000125040c004281100089007040d0441c000340340e203010b015483d450068024040c10440c8007910042c00d024007900e03015482ca00c079482c0540c2090f0009041ca60b1784d05e003003100400402100740141062404024101c0d07100c8502400440e10f003c0c00314007903003415015100c015510b45801c0d451916541c030f090350350340300081007070700150f90b03946001c40000d804000c1e005050240e02d03507130b0740c4840030351802a09540700107007110041e1010400e00c058900340068070408880c416200143d07100a44d8100700d0030f00c201d465029501c21070307243e035000c10004010024401c03039800301c2c1d80800c40c1070100c0941e62035400a8542c004e05078401449142c0e140056131100c4615849812100540e00b003690300c146114506e0342c84101d0451b5a0b00340c001e101003000190002c1019a031001a070500401c800148016071240800340903c2200b40c51542f040300210700b154042c2244413185200e180da02d01d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 267842005 1250 267840755 267840757
    0x7020a0b0f0a0f020414010311160f150b030a032003130303020d080403050706180f0506041101180308070809150403120318171902010b041d060403120906020a05 71
    0x14400e82d44900d003280600d0062210310a503019203032003043d10b040f921002d00045020303120780c4e4141c628580c801c003c0c030b2a01000000038008424464001d4151008013800c1c4500402c2090108090250812401e42c1140d500462a0700105034141130524030324503400c2030031403d80710983c0c4e030411510000034181c854007915140402180c0c460f900311a0b50903404e25040302e8100c1c064070001d000c50400c0c000740000a54542101614035140405900c00b15242d80b079400120703114080c1503489030000001d001c01d1196080d41400c01d0b401c282410368081800140255600140384400340c050500130589508214040b41240e60051000700301c1c8681d0703401414000c00c00d40c05880f00b258102d050310b40b980c418501900802e030003c1d140c1d01e41c03203600302142c0d00c443c2c081440800803440242d808100e00013942441c9103029028502d668000100748180c00284401c56081042d8461704103d03d04101a80d0b840018081d5880359040c44c000142d500c0f24107140c070251001180050080f80042245628564414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 267843255 1250 267842005 267842011
    0xf0d090c05040c050301060806010c0b010608060a080f0c010503040501090c0807151d0d0309050306010b09130506060a05070c08060705282a0804140a0605030709060807020a0b0f 78
    0x100362840101c1d910070811080754103504100000c542c00f880100007070360003100d516901c81030605010806d21041e645800c9020800d07040b000201d98460300b4000755040c84a01e120140070002c0c000e2900e01481d428141c2d540e5001c031070250400c90008001020000203400a0701262760044801d400b458448800c1c2e41c0f200c6440c044c000c0d0391029080c400d0720b218452641c4840c2a020f1b10b81c1020a0102c1800344071000d0b191000503420301040307041c00105030f2404c103c00d600034401c0c60f090907199600401040300c507100c48045d10104030b00b4841808001e945a80c101d481c0c0e00364600340310f56215050314001c10381d07000c0740c0e208102c540900780401c5250780c1c00c800241440640c00e080480b640c8001c8000f03800a000400700e035030003d20b4404101c107401c4201010040701d032400e420414aa01143d5640c280c1c103500640002e40e001d45403603400031650800103e0030b0041c1c03400d402d145007146441d0000405901180c0300d580b0806c464200820b44842c028410460400e401c0308408105141051451030b5420302a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 267844505 1250 267843255 267843263
    0x30e090702011b0302120f0a0e1002030a0b0103061508180604110a050108270c030109060c030e070303080609070504090c0309020102060c13090c050c1609110c0a06090501020f0d09 79
    0x40d103403c4000da0300c64800c130342040000c24443c42ca580c4402100641044004040901c0b0390354400480900e40320822100035803a07558036002d42d83c0d1425450f90300903208001140f038141820420b040c05141100c4444011040c46403424440d1540c8241d040c41e01d00da030705134000c1e5042c014001072200340410013101884000043e01c010048641d107400442c2c80c82c4044824807810943d122a840210a0006805140408000480e01102d48400005e13084030031104003144e206945e405901c02054050040320700c915070707481c050403d8074a1500c0140003031000034110751044030054002041c0e90300a20560300904485402005074100ca0a0080c0c01001c120030264058840c203000a040d61240104139182c00d4010000700803840d2400780884040e000d18503050091141c1800030407800d40007000074030907041260341c803400c91600c5e0090781011110000c41110882004004d0f113054901c3c00265801410781c072140c000b8002c4000d00b0900c2c0240a40d50329010024000603541700c3c0180c4d03c0d0062100c090107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 267845755 1250 267844505 267844541
    0x30408190e0103060506092815050903060906060108070507080f03041a0c0f09010c0f1703040606050402030112120306030b10050906060702100c170301031a180712030e09070201 78
    0x750000c100306c0e409101c00541d0f0044030101d6480002501c1500c03241c0c02083c0300c0350f80078007680383d87c401e03540303e545e1541100000f1004a44508130f85010003410f900f04084138040c01250420a00003030070848000c050809000700020080100044078003100c03c0b145041d05100c1c3c50381068a000c8117941d075004110943e030b08107a80407030110100e074012140043d07500d2031114540064000151036400180405841e034142c0c0c50300c40004150f1421800d00e845d50103000650f9a440d0503c3c184040311600e4120500492062005020000d1411040d164158000130510205041018120080c200380d0f04010903600c1c901e802c0c4503000020700b090f94240c450032251000070399225401e010300c5000d401c038041d51182c01c01031503020703550282e05400c0149008207103000b2509171080000c40030394004c5e441150344031780682110801000b94405a50410580760851440070500280c1503034903806802404010f101100c0c0d1642018002e9031002004c1300c020781502264601484040d00074811405c2d07004071144 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 267847005 1250 267845755 267845759
    0x1d06040f0c0e4201030f020d09050303091905030912011d0d091e05060307120e06040c05010804030c1401020d0e07090c050408060112020f0306091e0a03050f030408190e010306 77
    0x28541007003c41c024066121101ca203004004401501010b030207111126400c02243c0b105050324003c0da03814a005500035680e90401800f001d240003c036031002401c4803044a8041c0c0040e0000c000c541c14008210340701c410a58456001e01e0040c0780d070018444c841c54080008070804600802c20320034040300d5071a1703131004a0392091650400d04803c0450921203003003d20034445031800902468001913603240c0224200318514003d03044074000303104140c00d940b08004110406c000d0480040c00780c4070a18000c0002e00349540e0203010b8020b05580201a88103518810303014100950680709100304140b001d2048034000380700ba43e2a848280a081404c41c00d015000d000980108100d60840710100010310081c0e2a203109190220404417049a006d07200508070380196404010345070140e501440a411010411254690701101d8400b80c0c4115030403440c15140441d0704502680d480e8441d50080f10b959554610348800688207102c0403c25088910380c8100949602c01d41c40c0c07100080a0720200901a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 267848255 1250 267847005 267847081
    0x2011404060903121e090315090321110406081f031e02010302040b0708030a060503060709030b091606091a0909040f02012309041d06040f0c0e 63
    0x48100d01440010600088080000444082101900e4079140c989000d0a003404401e0054540d0345c000c0b4040043c1504030f0078814007032a142d4201300455440d40400c408a1151380241640402c1c813080b0504a0030039014905861094010b14602d0030381c0c0c0380d410355903030303c1c0c0c04090025003094400905014100520142c142000582c98061b240c2002d202c0780f012500c082810b000030641c44040741010b13002c1c000026100f105501901c511441501e850b503ca1600c94220b078220b8141d5070009200754008824401102d401448000c2035a4000c508100c0c1903541c076041501c1d0032002030b0001094001880c00081c0103900401010075210765000109503000100c21117000b5004070320700f0b140c1c040004000f10300040c0780c03804000100d500c1030502c0c1032030ba518001151a040145013050703d052400140003ca03c0ca400d04c00e250308425000004800441c43c100d0007940d904c40144014403081580041600340b0400280c110003e10480100802a01d49030b5801590315078043c04140b0302810308002e01d4858 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 267849505 1250 267848255 267848257
    0x4080109061506021f02040e07030608010b030109110d0614070c020a0807081e010902040f0b041107050303131505072604050624060304080301060e0a080601060507060b0907020a020114 81
    0x44241e54020720440030001713011440c4100011003640000c0d0708020024500c1402c08440d40304038041e440c00a01d092030a10f405080d21010110a80f083c4d140950040000e41c48204a01d4140c90548010322200e505140502c001c0c411012004030800030304042040785c960180303040d03030007038030030340e922a540b17a6102d800ea42d850116000380380c81600101a15480743c03850800c0c2400c40804400041b800300a2034000c20b04030340e61004008070f0191221004c1e407540c2414002c92500d108100c650074504400b41d00c0b240c0c2c070380c0000341806409059112410092207004003120042802c0c070701e02006503080080c8007424404007505000c459103111500b607400310010a10042c415500328010f00401e5940590782c0c203d01d00c1890039600503074603010291030982c032601c01451003a03200d0754000e9925410200058040c080d0369000c036204030303041101800182d0300401c411381150400d09100d6242c206a2030000042c0c5007000e11a80c004021208020025500041e600342c0c3d03a00070b8a0f121b94040308003039a5000c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 267850755 1250 267849505 267849509
    0xd05011703071e0f020d06050403030b0f01091a040e090120070201050901030e030c01020724110406030915050a0b090601050a090e0c0705070b043f02030f0102040801090615 76
    0x70380003000c48401116074808407900c0359030b11407481c204d0841c03000d40c00108200021a0160f411580e6401044101a01803241700342e015001ca440d00200f1010600003440603401e4080c0c0441cada212820444086d1201d803080d41c001e000d042c40c592119140c080c1d241d80c020034042d400c01882e88800603510f942600f400040340c041c90380681d180c603e084030003801903015006000c00303900c03a48010040c1c0305d009002880500052840b81c0d4030040c0ba03500d070000c0c0882018400d408000d40314904183c2103212604d070700c1145e00300d030554140800d40b02c105040c02400354505107020414141060100310002d080c5e07501086090500325040d0100303485020044505001381228080400c440003020310882a440c0b20b04c551021510034031501d850001ea50b01810045154440680f80d040030406105161002c1c40024001c0b0380300c1c01002003500c400e2180c03640810405100d8080e0040d0349038070030039501c0900c030820901801200955403540e4a05100e0300030103500d0004d45100b031801c0300d040e0741c0e08150001601 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 267852005 1250 267850755 267850763
    0x603020901140102250603060b03100e070e1c031d03030f16051e100911040e0c0d030905040614030606060a0c0b010f030b010806160f020c060d0501170307 68
    0x244aa00342400000302850402c04241584140494002c6030940085407001d001403184e80c20341c81d10f01d0100094144d901c10b42000d5521613061040004090003181e8000c100d902c00f001c111081c0d1210a0141d580c0c4c06044421904842e0340506800c10300340801801c0e0100d032013036036171610090300300d99000345035220f04040c2ca40c1900104020b10325580f4001c003074000e0303040048a5031404040e95a80e9890540148000c5a090751000c10000b407043c0103104803100e440700fa440038485010301d651a0075561160600c440d01ca15501c0290109030700c810815800d02c104090100c6c407506903179060242c0001d20500c2814800c03810000040390490309860540e00b0400007600920040d00e130349080180340c0c4c100021807810007095440a20108004d031064074002e04081540701095821406c03c04d001c0b12058210300c10aa03c01c000b489420b681c041800c11801d0001d291030034041c0c54614040b400c05a2410034664030020200b5902e004071501d92040b8101c7e031000c00440351401d51204010780300d01500300003030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 267853255 1250 267852005 267852019
    0x203040c060806181512030307050415051c0e191104050a090b011d070c020d1209080106080606180702060c0913020c0a050c040501080d030f0e191203060302 69
    0x1001c980200582078011000400c202100300d0180a4994030030800c840000b40e00100601a2401c3d0030310076440c0d001151804051440d61074400c401401c5481240702d4041a0300d103842c4500e00301481001500d0b1032518001c41e81c003144400e040e41c1c2c00a0500300d80200298000c207082c07024103201c1000c102c5100c0d603024143d180d94408040400006290003440d40110131b4440c00c61100041108407401e000c1d203950a002c1c0a5041400c0d8454810302e0010241014042140d5a40000da602e924400010a500400d41c80741d030b03010188111042c020550040400b9801c00d140072558030400f1800c1481041c6c141c1d100c45000d01c10450401840000343e403d007015801c00c601044103908030314000c010300764010f01000340c0d0205840e1000e040742c1c00300001507107903000568010b0401c242801000544482141d00f030055504140c001d81d20360741549111400d155440c103410210281c51b40110250b046254280c4031040007400c00c02848240d0f00030200d42424007030050213480c500070310030142642c0c0c026102c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 267854505 1250 267853255 267853259
    0x20109141f15030204060b03040b0a05011a0c0a0b070f020c03070e0117030708030a0c110c030c120703050a11090703060e070e01020a050105010b09030c040b0607111809030316030203040c 82
    0x2440c001c1071040141c0b42e44000c0504048096211405144c0045c00d1008031030741d0f01d25060810380820341015042c0d0241d01d003000c0040218407024042e00064220790503480d1303512410301169502d843e18a840042c0314001400c10422519007004280350905d0054003031301c261112000c20142c60301002e01800415030f1248005103c001d00580c03503071191464100031079240400c9520340365401d40088403611401c5498010164149504c002940408100040204103c0781c14000190301c8440d40068180985007a420340158850100420001103400005a85103c1d841c0e080c6500c0ca1440d00c00c0c003a0040e1a9000401e8086200e4803e2008541c4016600005030721507440c04c59a030901010341d50704502c240c910b02030200d4001e11495000b05245560f0035176030040f0340141410030054101d90341c815894101c2120300c03070b182c0400b2107003269401035400d41da0416202c0013425640e06020300101e241003400c20010207039000001980160503a1801d0307a0110008030046084e4031003254020324807403040e801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 267855755 1250 267854505 267854563
    0xe03190c020310110901120b13200c0705010201232a03070201050610030c0504121412090307090501051c05010222090501080a3f02010914 61
    0x2030000e01c01400c0d00d4a040340500c110083c0d9031881c03040d400604001420309020742e00207130841078034082200140002078451f80082c0203200030030303c040c0704c1e207480300e00030310110342802d0840c0016a107003890603840701c000c45802581c540241c060700d80591703c0c084802c40041500485602040070b8410204610381d00d01c03080d845801801e048020510b070366111050f200c1404240618407514040e80000b5680c0342041c100a11000781e620b13220241854000c81c1d030007181d800003c41d410381740620001510091149031442200c5040342e05500a406025280343d24000b03a4402030400140440c1100c0d040c544030260801124000e12801d90301036a2001d82400c00700d20300140b4100030b80518001070a2459040040502c0825200d135081c140912003810700c000d00f114400d0300d02510003000288929959a921200d400000080801d003440d01070300c4404981400016145000c0000851244ca4007480b50003c2d0283c94006030031036406800d90818124550002014424880c3c401821240f060312006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 267857005 1250 267855755 267855767
    0xb18030a050c030706050a05190515190905010b03180316120306050307080c01091502070611010b06070b06090a050609131a040804060f08040201050702060a0c150608010e0319 77
    0x50950043c0c001840102c021920b80d1003401c1c8500b0031040c000ca0315280100005001804180c08030072100c0c5490103005051141c42c130020f0342500c5c2a41e0351101c4846200b2014203410a40d800b60031403508010022480e199020040c5009142008005030030305080c000c981c1e140e00503450818902410020580d0118888840c1c1c2c4400121600300011070645490100e801e104072600500f02030340c08102011401d5034452078890051030415010303050700c00d002400a403a01d1140c46484100902081082020f01d0b0030341c00024200c20003480155160458035001d6003070b550444640b4403500c501d03000034020712094090603100e41d00080800e07041d42c1d100c0201a0081640f030900740d50f605050700130031003c1d881401041d070145000c7c4201c10785a9141c15001404407a0704859a01008003080c181310050760000f0075038051907030450f191500c8440c886812680286031510203407003400800d40000c1040d00702e074000c0d2700b510300d614024001a003008110991301d224a0761001d8001c5070800c000e00426204d16 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 267858255 1250 267857005 267857017
    0x10206181203040807150c170f010614130602070f080d080a05101a03060405091203010306020f0904150503010b040606120203072601080c120a030e0a050d0b01030b18030a05 76
    0x18a004e030a0074141c0e102c007400304049035480004d1075607540c0b1680320301c1e800102070882d080302c00c003600b119880c1051004244280c18072078942070121a01142c0c800030400c0c0b007070316035900c000319980c009a95030b50802907032074484d441110440401c0c7e540100f039a2202140308080c499840d2981c0045840c1c803818a0b0050000500708103692181e41c4002c04c1918690388440030201d00312000710303100c0c18810b0801084070809803d210155010f0300c03880b005229100c5c107a9044980020005807614600c0d02c17002e10a21070750883c00d500510b865140700e40c40550b6010001600c009400810801015a05000883e12103008105c04265881c1f104408207556400940d800304062030b118140800139440e2406441024600c3e100f90050a4018016103404000400d040ca0040f20906440c041d6030000780e48410300001c02030100300306060f0001468071032007035500040c6009010302e91800e075903041260100303200b0b010450740c0441d074102207003002d4540344150b840b00b0029006185042442f00041e40c01c0d91000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 267859505 1250 267858255 267858263
    0xe090a0b090609010b3c030a2a030b040605040507080f090c03030409150b040326041a070302010e0313060905030d090608070207050d11040b031606030b01020f0f0c01020618120304 79
    0x80d42d20412070514042d51ba040c540030410144c40e41800c4804100b52152000040a926400e9142c0d80510002c6803122030403034090b085c002003613552070307000c10f000d00342d903400058216003040d00344940c0c3c0754403240c1c0c0340c4500650640070340180c5919a1898440c8954851a54941d206010600107408182c0c02035030640e003400707034204c0c0065498000007200d0b00a0340c0251849050300521700080d0882400121220500a01140c901130030320071029040a113050122904000124945081500035449044107007c0101141c1d00c5828030b04001030001180e004e1200042c4422000003881e04000920310506010754442000da0750410780e0455141800410090451059003000101900c0d00429800440d002e84d0300322410320311a505000c203031400030040074040e610001c41c0001c860303800ca060005032181071030042031489104004030700c1c01011720000c1c1114011410092219a000245100b0501007a02525400d907120520340840303082030061400b054211100c085c0100032034030002c0d076000303104e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 267860755 1250 267859505 267859567
    0x30e0906040e3301080a0c140108010303080c0903060103080a030c03110306061c0216210c0b07050403050303090a050d050a021c050417061b04030f020d02010e090a0b090609010b 78
    0x200142500c1c0908217a1208809400c4143c0c2035081c4168904401c010f0050070701d0303000d0034150100c0020001401448058104500e44002c40d0344500e04000b01c80007c50010b00b21845940c4906110390f5503030144000302c010900c0e0906200c123041c00b9011b912807000100ca80241117039030302e600f80a11030340481010501e400c000c180382071307005a1510241c0030034010342c0c4110b41090340c03924002c501d010000c05040400440348030b524043c640d004201c40307281a404800000740f612110020b07103042c091a0801011030202100700209040001a040c00d1280980c0840c0c0209141940544252083c101d013580180c100100e01003000583c04c20315007400e0300b140307483d920b4180c3d11041192849103151f400030180d00440103100743d4480c00a01022404000d551040c5080c0c59950303500744102035001d0013806117440000301e006680c010501a250164040d010301d450b031030131004400090011441c0f65105e00c44420104070036080c800d85480c140c1d16260380746440c015800b410040c9030442d080c0c80c001d5641c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 267862005 1250 267860755 267860833
    0x90e09011409030403021e0d020411090d0b190501050d0803040c1a0304030e1c020114090904080a121112100b131a0a02150a0f0207030e0906040e 64
    0x1000303081c40b41c8a01000f075911541180b040000c24034101011007066458085200c00659502e0805c081072076048500051800ca071008001d8540640010b0aa0100b04149840203000418851501c5141c128030611030070640030030324200b201c9003070044c01c0c3c00c510030700b03540d5000803021002540c00034002e001604003641c5d41ca5200c041c01c400070b50b014883c40c501009200c1015007055030421490340444400c400b48000d10300010340c044055601a040050480340c10700016011b60840f030a10001038001803162403d402c05685903848031041701c000810080c001d48400d241842081d04100d0302240703161500107801d00204020a001e08541207400b402c480004001032044004c0181c040c1c0142d00340200c41c54114070800102d1880500f0190b00300c00c0085032130050b070104091842c05005c2d0000743c21a01e495000100412558010070b40303413031001400000f4590002d151341c0c02c40f035044030300d9030301c0d551984244010780b400940141300a45c0403c140300b00d00000c00c040c504010051941c4100450 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 267863255 1250 267862005 267862031
    0x60708120a0f0e0f0616090b031e070311030103140c03011406030c0303120106320d0515100e0102120d0b0120031219021c0f0b01090e0901 61
    0x2140c103032049145295241221008804036004810700000400301500040028080440d1a003200400030010700c95607004640c4914020340c0e40744041c0c0b008007805600ca00d81801c01d900c040c0210785e003841040d0580380002c3c0d600c6110380114600c400b074440d41c0328256441d50303031180c40b1541a40715140d12805858010100383e2424030a0b1082c000100e000010b240c00d0603401c3c581406106180c50380207401c204000b00d020b20f20610002e0440d441c0307241010001c480c50884601005501803c280b8840b800340d52000002b121402810301184040010850f07074a44507684807a900700215070b0794020900c14a11a01c0500903030a005030f040060051b2040003640c00c0c1542d4083c0d0207442440e1080380d4561448040c1d5900040c039aa60910b40d04201d010120500c6c0c0311a42c030f001da415484130b2600f0500c0050342c1e0903a030414078041204401000d6407941050b004110000d80048440759006103882d15000b418030a90041c041a8101a1a400009401d14285080c0d0f04030082071103590307640350703100301c5014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 267864505 1250 267863255 267863287
    0x70b130816150f0c0b0a0b0d1a071e0804051e060a0f0c020318190312020609010b0d0b040614180f0a020a1707080118031202040b09060708 61
    0x80307207121038040c1c0c450804046214812041590808114180100b1010705401820015660360800c488200d540e54040000e80502a03140c0d400b500603018105083c03c0000d400624542d00d94002c03000d0340345554424007151074070051030b1064014000e101007950858018040c1d1504140218207541090040b04010740e250600c0138a407a125900c49010006406540e204140d5140710075001402500c030000c100940d24080c46102d15003000b804500c000302a612500d514400ca040600001111a964141540075070445051140503000e2000020810714042c451003101d050001c3c1b402003014461340342d050b0090002001242c2140da121850078181415002051281a1090f07250480c01e00d1445041e0800705c084040d500300c0e87c0300340c04500040e5200d05501040d20310b0082310741914800c820700d40303240a4440d07100f10119403030001d049482d8049504010f0600f402a00c03030205680c00f03016003000b20b1040e8414901e00c3c140c24001c0c00e65901d042d400814501d4011700d16142080c0c4801c10004030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 267865755 1250 267864505 267864523
    0x10804020901181b090612060311090901061e0603050f1605091504080a0507121109090c1305011a0c1b0d0c0e06010809150402040f0906050f01091d070b1308 69
    0x5c200f110108111045e84020640b0484ea42c01d076050188903c0c41e9034032580c041400402520914a820000e021200254001c6000b0407840c00c11082092688c6200180e02840e1300802c0b0000c1e052000142c90341050a00c00d50048021402e00f51440c02d55010845250700198031055208800b02002045007415401920103030142d0303000380c449880715207407407031918450360321481c2034181c60543c240c04038190084e50b035940714041d1080c103016a1075086850900c09180c464540c400c030a4000d030246054681e00090607215074101c90b4100148010211509005043d28060b4075404448441300171000b44001140080c000740201c6044c440903910000c030102e0b02e40007103015851766001c2001d2903a011030000c1d00051001e001e030450000002c800300101400800203070003151241000b559206059215104054000000300080e040942c455001c0d540e00703101d6240c00700d050100b0815603115030b030b80c1440014141c4000f0031010f4945940c0c2a0640c00c4000044c114640904000030b51074018494041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 267867005 1250 267865755 267865757
    0x306121406160f030207020103091b03030906020c13090309080706050c010f0209130510080f03030114030102130e090319030e0d08071704020d02030a0f030e010804020901181b 77
    0x10351050800c03146041401440e2030403a070151120100c03000e4000380755148840c128980541c0e0392031940011b034050720500e03900902d565044c25001415030000000c40381902d1107079450b10400c50341c84500326500c803000d40c105a4400131403040d5651a54084d400703c55128400d04200940ca5560a1172900b00302c01c9034415400322f200003591400e1a14284140f0031007640e030780320460030110441c02262014045800d07403400503a440011510391018000c0603002440110112040149080d21250b00c0742c10030b1040049016030f44482c00880d19041c0280da00c1074009083c0b8558146c0740100441c1202c1c405071051031140409c100304084521048120b200301c4807940c60103d04048804a514500490681c2400402c9007403010f020055034401500c01070745e00b2210414000d42ca07a0300014910480020009506128440010080009802c02c2103c0c6a010391170300d16030408a68010b41d01c04808580003544034031100014011204001c25243d80440300f003000240d449152500f14254400010101c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 267868255 1250 267867005 267867023
    0xb0c010e0706050f0309121306020601360603140a15050606090d06090204090614060d11010c02040e0d030b120d02070303200a1b0902090604141903081308060405060601030507030612 80
    0x488016010020306006107259058012015040069107040b04c3703041718405001041d0418168100c41c2940006004e15040342d6403081c0d078401d0140c4140d8500080c10129046e007030700c01c94201005130600c10075108490240c046490321203032004200c4000421a4121461035491506001603144da1149003c007520807240003e000740e82d4065030324030b11002800a4422811010b401700001d20600944802a60070700784005504513510014001d011507a6110200b480342414160311750380d040e0807001401006590b14107400800b20300c2c20351140060101c1c0720250b4860002080001d214142e140d102802c0e51002d1400b1a84001c08141401c410500948607031580c00c0b4070800d10152040090000c02c031680301149042550300200b0072601961080800144200348100c0302e54650340c0b0f400754090306943c3c5070380100382c981c585541d03541c20001c1613040310030000c500440c00c4000050300a001d142c12030000c0c41e0940d01d000045010784802031030401015110540000c507070403200004e044051142c0b180b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 267869505 1250 267868255 267868259
    0x1801140c0705010318050a060506060f120a0612030504030206030403051204060905010c0207030203070308030a140f04031b0206071b08010609050a0c02070e07270b0c010e0706050f03091213 83
    0x5058450800704165240700c002140c00010704001f130030f4041c1e250301040105580d80c5000015409004882030091598400504110604207804400f4468011040c0811019840e009541d209034009800200400c00c100b00030301c09840e20a01a681c094031900d48586013141406d0380403075210080d02c040742d6280c0c64407611001c01001780210404540b044c40180402895500040c1d0303920850b1101603c06100080840c01c0420550040c920141c283c242540b0641003100161218490450742540050f0008403c0c00c410000c00e225003040c0354000f001d0905100d62034441041058900c0b4064036140409400010004020b0007004001e00140c000002d003840c14800801c00c0d01c46001100c1d0440d000401c00b0310010601e0f02016400200c3d900e030203024800075011030700380c0c40003000c0440f025070060100010700710103c0000380b00d90070a0070000c0c0305014515410036030b103200c6401010041441801644c01030030541001d55800103c01c411a050103800410001440e8484400191090343c2c504003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 267870755 1250 267869505 267869507
    0x80403050105041101140a051b0105011203090812030a1a09090106230312070503070b16030c1103090409020d02040908090a0b030105031002160c08100b0f061801140c070501 76
    0x40d99901300003e090001181190410610880c40740301d5a41301406030214500a6110f03820760b03561700d0b03282c084000304210f5031201a451005030715420100d0000e44410001b06204402046c8031a180a00e44502030540d2a4100042c0262441850035940640494070546540c0d13071b1103107010701134100c0100000f200c90034101e030741094142e10240f141001e4403490003488d43e9200041c0f101d4285e00c0300c2c020641c03a41d01a1400c1415841143c002070a611804014032008502200e600e03201030102e130703c0800215805141c25a946c070207516944000790424010301040e030a06400c0901d00310301c020032201030308a469000500301d907401102943c1401e004950000c00e4181031102c9006000d0004086003951315002c0007d94450400700d50205142e0040744030700e40d00c1410040382d094298441e0b0314030001910344004599400740405401c9880c1c0c1800c10760b09082c2080150684c100c4c0d03010f0081460450b07038076401e070902072800c07202a0400c00c0c0d400050150001510260803245003400181a0162400300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 267872005 1250 267870755 267870773
    0x50c120c030612070e01030609170c06070e0f0d02010f02010f1803230d1509020d05150d0309090c02030903070801020d1b05090d2603040501060b0702030a0b0c0708040305010504 78
    0x1000f6169000b19801d0040e40c6048884504580d80110007140c010b01d00d00d01a0b44e1400f9401c1010503000d80070031107441445011078100d206402960f500809c56198608010411607440407281d0001da1114404025500c28a4050b0382e44d1050f00010420f50b40070a0302d042290000810030280424015106e01050751140504c4541454000044146282c039014400e030341c4500307450503c0d11a550b0110b01d094100c000c03844801007509031000c42d00c41003128103420250604031809689040d1045100509280c4407201683c61070b016500c2d0000141407030034200080146620800c1548024403515016950402150f009000030000140c0c6070030700d0403459019680c0a031072010340582403021911100340d00406944843c0c40459041c59040320608260050940c0e030141e1410115080c41e903154400c0d2340030700950045218800070043d05555880414581c094400029415000b16503403c000c1807448400c9500b0041d01c012203490610159900002540140d1085401c3d944a100300000d06c800300d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 267873255 1250 267872005 267872029
    0x20411160b0903030f07180f080c040e010e12090612040c06021612020d031106070504031b06021c031404030807021614040e0a020612040209010617040204050c120c0306 74
    0x8030065042d418144017862000100604139400c001c880f13000c40c0380c0701c86028407060040486095525000b51074880490311920b00218441c06076081440e8500c06610511840800100c5040034141c2400415a102810360000d0001fa40c021402d1000304e00044c0054907035809a4400c0844d0ba01c05072a201c40603040213000b0401c01c0c800c01d041c000400c502501140c9110300700340d040b6100e0107900c10502d01520702145a03c004a028407580c804c01180581040003401a02c2c0500403840020000160007101040e690255800603000f11408080034203c1f041c042998140d18140410302270391100382c0e030f0768241c8212000c0e4001b9200d00103020005405000c03001c2c120070802c0c03904003150304200510a810540e0a0414004c1d540c03481c901040b14000c0c0f00c5c032805168014596903a420200068460900c1300341c0d016440b07282c640000154681c02105000301c010100d45403640f1999443e000c020091100a140b02e508100401c01d8880d440e55101c1510302c070748840302d22943c40341004414000884506 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 267874505 1250 267873255 267873271
    0x705120a0203060904020f012303150a0f0509090316050c010908060f180c060408070e060123070c03050d020d08100503031803030c0d020c040c03140601030504020411160b 75
    0x100140059900c40c00b4204e81d003d50162184030031f09201d04012507407800510042c0c400911b600004410019070320b1300450003038080f440e28440c3c482c1e4010802c940000648940c50007140490410081414030803045c43d032105038034050300c0c2041003c5824900102c503014048074142c002c2c035480083e541e0094143e00242042c0b0340200014035001410310100d09000e0102401c0100c0200c560120540800100f840000f01511060f21341d0b9807030102c3c079682c3c4018003420f421130a0f02d4000034019403040320031401d07104440c01590001040c1411491007544071502c25140824440b0010010410030040200c5011081d0b0080034150281c42e401070840c000904043c40e4072880340e504215681d00002600c07030350040120017140d01c4c5001c4000928600c00d40c844641360f40241303110704500d03540124410f01ca402060300d0500c503100540030103c080341d15610101001490310800f10704154403a510460744144040e00000e05403a54002800c06900410b410025010442c4484010045590f048039084214 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 267875755 1250 267874505 267874507
    0x506090f0106080406090c051c2a1403030403080412050709020a050f2104050f0c011b080304111504050301140f010e09070506030411120a0201050f09010905090705120a02 75
    0x612030700603e02c25010304040d03d900d8582461400340141030003444010107005141d50300c2c2c80c010908440c51814180e0303007900d4640c20a089400c0c5504180e00000d44200087d03180e1080f282040ea0604c601000c0003c1940c05100c140400710001f4000c82c0148080c0560090200601c201454818038014107500705000013030041c050f1001040d040425116601d078501c41450b01e5184001c60701c2c0400303e200c85100c0e10403e200e014001404408034240380350700d21540c140d43c1030382640310041d1031011990100c138400ca8010180c01012554120280d50000d1050140cad0703184000240003c2c055040503106251140c0340000c040145190034880c807111300704c003500307103214500d48000e1880a01a0520616080140a02c0020100c103000d00101c0090000140a44e03100e09050410000407030101680354040c810483c50302c501c80c84006071048040d83c0c165505031a040802d0745000454004580d101e040c844400b4010800d980d82c0703c0001d225003019070340c894944d994070b070302a0010310002e000200d12a00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 267877005 1250 267875755 267875759
    0x1503020d0b030a081e0f0a030e1509070603050702010e07060306060905010206060a03060e150709090b09060d1407170606090c04030c030b0c1b060106180b180607050a060506090f01 79
    0x858030040d210000309601c06900940030030503941700288660b0b501601100c0d0009080200d247d0107912148103028a9001c49203140d86012402d0b00007002036403190300550011100704042403103500000e5201100384000708446201c44101442c2c00c4858000c1000700e40c861105100b500c0d4000002d01c01041c09100500a03401d251000c108244154040501801d4540c1c201c0d00c540c1604000c050110903061a403115140b03001c983c014079160346c5009140c81d490401011600a2400e01250307400394000501c0044c00c125541c1e5001080d1940c0c1c40b05959038000d02c0740010f02900003030142540c460134074024021500d00708040100c0300d80000d208406100052105001003108904030300c041d02d50010114005443c1c15070541407501aa43c40801000750001420300741c4135001c541641200d1440d1030381344900742100c101c2e51155100d409002281582485041042d1080c040700d80003046000c2c000030710b13028050301c907241040034008080c2c559580703880900c08941003403151158020710000c1c41580c154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 267878255 1250 267877005 267877013
    0xc020c150906030c07050f030a0c02040c0c050606040b1f030203011403122d07080a090602060c0904230c040f0f030f0210090504150611010c020a12091503020d0b030a 73
    0x100010380329013601c5a0214941003040710420801b240c15a01c182120b44902401900916080c40d5200032802a800c104403411014061a46010056400b002074003803aa5a001400000d0048200c043d500a42510b12511000c003520907001010225540160352503040c0603c65065190131074a080c006e51161800161110310b40301a111102c03d5486099040c1c1c90402c0b03051811221000c3d451820040020700c002002032060003071078110060344820210990b50b441c00d9072118002c0b241509002c0b01000324610714507250380700c1250128402d01c2c941c12100e01e11400350303850000b22a2484008030000b41444884000f1150000400b400b4002e03602540c00c0d0b43c3e80c03846510b01c1c2c004c024000d4a507000704140301c3c0c1c081d030b544002800002d40100700d03d280d40480c02c44030401e0351080c0d41c082844e110b40f117003c4540602880000c014250014017950781c80c3d07682d1940a003075014015042210b106400f040e41c1106103050f40910649550168890307403512506801c4850403040329110341e00c4012220005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 267879505 1250 267878255 267878257
    0x90a080604122001021902160608150109150302030f09030703090315020702040c030606030f0b0901050105091c0c030b0112170306030102070f060f110313060b0409060c020c150906 79
    0x1040c4a894036511601a80b61074443c440c2d40405400010b500108040c0480010030880c0444030741c5550885091039161243e4180d0401c85000e40c6c000205520001440b0303c0807080c00d0a5a8a0181b410000c140d42d600300450180b5074a10050f0002900001400310380480a0442c98202d0010300c0594540305013546c2c05440c4072600d00c8003c00344030f070a00c0280158000340d410b071212181c0241c0280704460124400400a180d00c0c05a013001c03070f04d400102c1e18100c40b90700c6901c040d44005040144180d0034400192103d801ca500c0d4664080b510b955004c1c120140c00720408a014445c0e85040760050031403501800034071050b08414a000760105e440c42c003040c90342c0311401304e486030480c0c055560384a000120340a03200c3e980c005030600404c0c0088508001240d0321a031007843d2410402c00c4110030681c000301e22488260f81304090702402004100124030300f580000d5480d8001131000071580b03a184c0d6564244ca442403518000341e0803600c51628203041c03002c8500810031b00b80080c00d01d40a5044002541 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 267880755 1250 267879505 267879533
    0x11100c060504170a02060403030606050f0403020d0503040f0b040303030c0e01020303040b0402031221010501050a080127110a080906100e04060213080d030b030d090909021f05090a080604 82
    0x10340d44407404501400f030400c01d480310b01e03007207009a283d075400d50f02c0c0042d5907484151405c400092500c1c40010790140b180060712118204601520f181c10301d56000c03c0032100c0066000d4446e8002044002212031030034000a0043c40c0740030210780c44030320b10b050280866440f010000140320b04814526141e071b82c0401120f500030390002c0d08000c15191400400d14100f404407100c40c1d40303800040d0804401103a040138a248035007010071400c651f038941e001180e05020b0307810b009003c0303803140c030051118454008603aa20507c01c51182c4201546072107400069402c14003400c54603407400900c6943c441d43c403080103076021620100500c0c042c100081401465080c91044002011120012504000399a011115100b18100b0344030049074a41040d503498a00c00464007000c02d10b0b00c10040781c0d505010801c04101152900e40c0c0000c1071400c04144040c0c1410358040703a0100c61106800030700c0c13020000040c0440240e540d41510740c0c6118080c40865181c0f5001701d1302640c885804c11002030031807000350603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 267882005 1250 267880755 267880763
    0x20a051903051218010f290303030705030721090218012102010e03060109060f0909110105030a0209040e030319061511240f240103021305030102120411100c 69
    0x260b96607004004210940288441e20301e550070117501c01d06c00050b40d00301000c0c0071400c440301d03920010f8000000846210442060341c142e003050000542032406100915401302c03c509000c125007612003d4103100381440c1c1203202c0299543c0c03000034250300b00000204401d58041c03409000d65410900d05120301c004652000c2101100001c400703045900c00c08640300c3c41403002d07007115465610303a290b90014041c540940c020340c015807032001a82e48614061040034130340004010882240c0e0400451b200d5100034000d807441902004451960748440c41242d96084c00c0c0301c09183c5a0801014803c1241c198221021046040003030512004980c03603054040b10550381812010f18000300b20041c28070110f141c00065500e030b5480701c4080c1000c642d0849115141003003414030542d407081030042d00d0240858081c4240321002c4803055055010380c4c000d15052882000d012505e82d550030019003681d00070310020f200038a240c802d1004000c8035080d00c82090008459400d808444002d009042140c0888050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 267883255 1250 267882005 267882037
    0x9030c080a05300d020405010201050c070f0b04032006060312040303020303061c02030f0d0f050a021504060f0c03020706060801021c0203060d0c06020309010e01090b090108190903020a05190305 85
    0x8081082000352800100000f04075250311003070151680b1009410905c141030155081400080703400c402c0508550000c0d0b8800d0560350b0810098448001409005004a048c000700c5c81d401546610540100030032a41001d0040c12189400014103003400c0400624880740901030206000081e0044140c07a40480281d4021004a0078482c529100e4000300130041d426024108050900034000700701103d130b8007440c0e190503100100500d0212690701c44c8680040c01038008038106030004c4744042400e90458001c04002c82c540386040c0d600c4080380e104071010000f0960000d0f41c40d04000c840e000d107030002c00c01c8100842c246400904000f0a5001280e00307010701981c0040068219501c0340704440c07500c4e40207d41c0784411919280043c0d526444448918045180380e0707003107192580300342954001e59132000102814010000c00550b030082c00030b4080c001c61114550080a40cc0d1188110480d240c001d5004040720002c0b401d2613824200d400c05000040342c0c4803509200403076003000c1142c44c0001c81130000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 267884505 1250 267883255 267883303
    0x10090b030a0204060b03070201060f05100c2d0b1323070308040f03020f04200a03090f1b14030d0509011107091506020309130b15070309030c080a05 65
    0x1a0405000c008003c0d84a864414049042c400c483e016602c1111103800070480561261800d0515040c944207140d400101d04a40f20700041c4520903407050144541e040e841301ea8490060f160b4404900484054860800300340d20381400048040c190b009800d0220030071981c07105490b01000517688980c64002d0000920400008440410031040110b408c10390307585d166501c40030140b10118a0f0b22041e489150081d0042030145010b101d0306645003143c0300109c1c0b02956011101c1103980050f50003e05050740c5a00ca400455400c1c407451410912524000b242c490032042100a00039030354100880390b11940e05082a5a14001030303408484070241400c6841c1c0661038012204442e0b40240115503002e6401c0c00203014101c3c0e000f42d5490358110001100403a21000201d82d24040c64440d15446550350406105850580d4840c0700303400e602170a0303001e19804030203102220fa80190710450002d003802000304180300c40c0c03d1a0a01501000020389807620003501c03111383c0c807420003c20310b0f150481034100b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 267885755 1250 267884505 267884509
    0x50c0a1b23030f0d06090b0609030705040b0f0604090203070206090601080d080a060320120a110f06070c0b13060806030c040e0712050f100b0618130923030310090b 72
    0x1601c41001c0c401c07215a0761a0b01013800c02002e46801c2c81420030b900c0c20500221820724041054843c00440980140b010b01c1c54401008058600c003100c185d0405600b03016050ba40c0c0f2414007c1c805070821400241e80c0f414140c40080c80c1c420300620162864010000612156101007400d014103c3c1c503240c05005512840c40400c014141584010040d00d40004908118210b600341d5240401040740c2d2601e4002c0281142034580c03024240041c204c074074080040c2d04519140321340a600420140c285c9060210310b80c2c44805101141c1c024028000000c159912124103100c8200050700942c03501c1496400d190010a81d02c09483c10040d00c034507105c43c0000d0b0702c040108051030080010461010600c4041c4c2499034036124501089500d6010fa1890b100054440c3e010798800314502038101c5103043c048511651807000b02040ca13581c0820700d150ba1440840707040c0101203000b4003841c4a070070b020003807201080420b030743c204485107140c105000708807440518109400441c1c0c1c1e04040843d8090b201c0c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 267887005 1250 267885755 267885757
    0x80a0209061b12180d05010e0f100f020703050a03020703120c0c050f060709150909090b0609060f0f0d06110703110f0a0f030e0112050c0a1b2303 64
    0x3540c00d80001012032a008540d5800c00301d642d4085180b0260380c1c1d06040001c03000030078032807044400002e0340100744d00795990520780c0c15908140d0080d0000604100340603501d5003410041c2c0345507031565001c00000e03018144d15101d1214050b00c01c51003180b41030fa40d542c0c0503000e4040c034007a100c24540c1c0840c048050501440b02c0c00f92500c500032080201c06d400c0100602584407804040d0759512039410600d218100c00503145004402d81d0f1562000c440c03404030b113158601800c040703480400c20032103000203464106002e0300b91021f1140c1104000c914201d401c0c00744034540140b4452041a03103081a0b2010f0b1102120303982d5001e003e840d0b400a01d002400c1190180403003e03009806424002410024517600081c2481031092150a84812402c08005165a0000389802810100700e9941060000f4010004244211010306140c030144100b07403162011190f040701d2414403100d00241c7d2000d0207610054414035201000b070a041c83c41e07040c0d19051a00c46a550902800301441005d4040441d0b0401c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 267888255 1250 267887005 267887017
    0x9090212161b060606120b1e0102070b03070f120504030c110409020d060b01171506071e0c0e0718120f0b04060b210d031104080114010510050c0d080a02 67
    0x242e40003020008a1600c00c0c01480f40748100d00001d07403001e892140e003e2a03401182d90001d0010400c5981c0c0e41c00d441e044141c12150844141544203444000407a0f520380405540705030610303111a10b6009110f40041e02081c00d00e0703804051f8615201c100300c002600300c11600d542c0b60304031058501a00f0300502050042840c00c001a500018a072000c004101c0d642e0414404620b00380c0e2003031203c130480480c0d050a0242520345020316100d144e03001e40d080c02d100d0003810406003c0d47da28003074042c09004038550076002d00010b450780c45181405228800070565019000750301441c1100e403040c3c0c6400802c1706036241e40900b45450000300680030a03c0368000385001030540004c4194a0740c140342c90508001c1046101d00c500071580d121804001d03501c5542c4000c0200003104c050607450240c81c40442c02840c101d500601c00c0e003410302c800700f40c010007403145d5440c0c503030101116030195060408000904004803841e104115040182d802801c1c004500d0820200301c03420b125241d41c641c1460035010340a44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 267889505 1250 267888255 267888287
    0xf060906171611070906170a08030c0306010c0210080912130b1602042a051911010e0d020d080a02031003330c0f08040c060c230601060909021216 64
    0x700601145518145d440202240e604102c080007c0030200022038807102200710140445500380001140040740d40000d6900c12014509a6205030660340000c03c0c0031a42a801c3c40020444810420030500c100810180c240e1091621030a003240000b4903600b1800d6400b60a105a8001c1888a0790241a410390648164003c2040c07010504442900411000141c502c0076801c0104000d5504a800b4208840401d2408040c0d90416481e004c402c3d83e50ba0b4500c1c90242c0150f58849070950030000c24001c08450040c198041d00c00800c0f41403008000d1403000d001c0c03c1c3c0303862040043c480780d00c020724908402c80794851403d070b02c60120b02450b50380d000b1004403c400b42d07510400003050550035036881150303008410b80711100001c40405c4100c031803601c2114010002009550240016400f58510003019032013100c40041d407102d04003510040300000d46004216520590040c8041c540101520b0043c1880c0941103003008034060742c003d51024042c2100984400c0074901d10303049440340300c0e003080d10144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 267890755 1250 267889505 267889513
    0x9160203040305011d07090e070501050306060c2505010e1c080c0a0c03150216020f030304181a19090b010e120703150603050304030b09010b0a0f060906171611 70
    0x14882d0780d229174012540444407170340507010b00411030880b14802c5854056603000200a02400c040041d2000d0384040c00d603a5011405021407040001c04001d5031807442941405169000010202d0f0f81031510740d500a241803028840f000d103103a4442d6101c408007104030000b040040441401e08004904c1500a000e00c5030051034811414005010412012a446001c0c28101d22042c40364280485c00380b1035005090311303071405408015151603189000c1e52040201902e2410740e83c0c0000c00980354400c03960007881903c0340c0b212041c0c2100350b844002420b10940b24460703105607007007034000000384c1030145507201566000d015000740d101c0c800c04200c1841c043c00749442040840889952284035100c216202c0c08206190b890f03c80d442d0240724100c980c440c0042d0b00b41400c41e40c3d0000164001000e5041a640e50180b00e03500b903031803081d0500145044445121b10f1801e1001c01030158141d0381151003403140d021840001800300c1804554040812200e4113065260340004071410f0345280810007051107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 267892005 1250 267890755 267890771
    0xd0e0708030a0822110102031c15091e1a09010e040b06030706050a1b0f15140c0d0b12010606020c0906040b0a03120c050303010e09010c0309020916020304030501 71
    0x400040200042d01e2940c882071400c1d91040c040300b0302100d2408024180181007550040003070180310420a5580050058a040080b1010905e50183c0303008002c080c200e44980000c502407004510160240800ca90103004a4500110070030007410140210f043d02c0baa00d00d0920030034030302054800700c41c080003010081507594940d0343c0c0000c000306840039907103868504003194462800144080440ea421703102d050030a040b0f25400d40b00000c1d240020401030030102c09400010b910003c84990041c41820030f070441081c10f49900c0111800c00c1405c1e80c40340460014480c54409010540d80280030501c070200d401c1ca24500494091303460b2116010096083c2000469038540101d0056a80300d801d03115900161b841408010a0710840302c45143c110754600000d1001c2001c0a000e0400f6084900300003000000d00d50f5960726551003603002c554260000c00911003603c03002e020301c400da00b13298601440070146036000203104c1040076100800226444031000000c1b4002d10030384008540000007081034003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 267893255 1250 267892005 267892019
    0x60f0a0f0f05072007060f020f0307060e0f0a11040209040b030607080615070b0a020a0216061e080f06130905060f0907060206090c101709070515040305030f0d0e07 72
    0x2c9003d40c2c00c140441e502d2010100c580c0c858400345410040140020210189400070070303204103640002da40d0441c0940701502660240400003008454412400014500444ca680a08100411403048056001300c946500484c1408802c1c1800000840f001640c500201c00005c0080804441ea1509030280904112600c0d400c224500d02c83d0005403076403000080888441802482045d0004203000711032400f00d4405140d91b409059144035a00441d20070369074411405207031007002da0000000602984107211100340c444905055a01c9038104141d160600782d814034060b80c0002c025600030035a1a202000e8941c05402034846035420205460076810160b584004003501103510b40d15610811000090712440000e81d00e1140505002501c004030b0200100500030002c0c1d02c0c000b0030440154801c00728409052440340c0111840001000b0342c40c0380000b4040002101d000048904500340010004120301000306c6d0300e03030803548203081c0d070703038000491408020460b0251003100c61240040214800c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 267894505 1250 267893255 267893261
    0x4060312080a0b04020a0512060a120803150a0312030b2206050a05100804140a02090a020306040b040b0a03080f16030903060b030303011a070f060507021f090203060f0a0f0f 76
    0x3280c2e41c1c4030500079094054107020076441040308041c0012800c00c0728815012036000f4544d0021300042402c01c2955985104030000a24004156625000001031010003040480346280b100d50a80d20220a03616503211281d65502c45042d00041c143c458a090fa4107a80c1d100004441d1300c1965040311900720030f0010030f0018a9a40a058080c03901c214001c140c070720f0b02c5001010b44505a9540b081255240e59505001245006811300e40d4030604a1440040c0d60703105ca09403040303171090001612440c141c0b0400080c0c444024a0300c1c01185051980c5503540c45002d140021b40b038101c401503a466505112004141c840d0043d41200741c42d48c1c0c00304100b0103502c80d10520851703000d51004d00001100004243e100d12003803040100305201807281101407800d80c406444114020281113600440d40d86074581610030407101640140c105100e114401070031520740c250010300c0030508010440003035020a99a4074058002c0760508ca20a0015440400c203412402200c104d0807418004402c00142700409 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 267895755 1250 267894505 267894511
    0x102010b0409020a0b0706020702030114090c240a0210060807030b0c0f040620071e080f03090f0d0503120601090806090a020402030a02090a0b070209071701140406031208 75
    0x1942030520240c040d15107401000940d640080481c0640fa01d449021142e80d40f1100c0f04840140d0248008800360f5000c2c803a00b0304140741c60340e24400502e00505124184201c0c180b90920400307031145a0381032240c228409032041d030155010303256540d06007e01640f0f0a045190040700302410000301047c148030114000f0110780c4550720360012900c1f288058170160084c00042c0028101c288801c10510344288a128203900c150240c100403060180c00c2d5604149480d0800d151a8a10400813103420b6646403081004294650242101c010505183c0d42c40c1c0c0300d0040000e10401d50310b0b4a0f804550390340c0c208446003039401012a83da40510070f031010348a00c0d0455031580840e845d200006846140414058400c941d020050031040c1c41e150f08020083d000a000042e505070700780f02e00051500c0342d48548019152151901391540014410000c00d00302c010204010003461500e003980885031760003180d046d1005c00c50250030300340761080850010714059002601d42012002c044c041581c1040540740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 267897005 1250 267895755 267895757
    0x304091401030510021303020d2f130e07170d0216060e0907090b04030629090103030804031e1e0906140d18150c020718150504020a03020901 62
    0x4840c1900c4840000c40e060244005000b5410044030340c1050911540180b40405401c401024410385940104154081034441220003030044900b141c405a042204180d0349180e0094111060041c0c00125190100c00c034400f511182c0c8540448801000c00d00500d4041c0c59402c40504001c44013140040d928035030a42c4240141c092004c103004490804919101541ea96448400a400d1944103009511000800001c00c010545c4000b180c3c01d25030100910040d4040c5d03a011500701240c0a022425034496400503900100c1203c0c4240251250003000f411a038250914040c144c0c1c86007005d449a1580c5a6003c441a1a000e010195260010034080c01d56691503400400b080040340251a10303101800f03020302092200010143c10030316200285a85442c64801281605040d2811105841400412100d1456002030220200020b210f088240c41151000b001a20f1078a4241814035094026a01e101c6891b600704981d002001e00c0c515000348800b4104540c1d442d54400020000d401c80c4692034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 267898255 1250 267897005 267897011
    0xb06040509040f1703070c08130b0d06141207030b09012a0807020f1002180d0803240a0b0901030e0616020106090b151606060e040b1806040b18070305030409 69
    0x280440c04e40c16644520800c1e140c99201000c40d450f1001d10b40c100070035403540c0411107000410103403c52000f40072644030880f404a00d1608000000c8100c0c4420740c1c280d0b02441c0000d10302c94031001c000a5400840c0d420a10200c500e4407540800c40c0034060618008a580303440714403a0004d1694041c084c518088a07a03a00f511507101c0b0881240c6444480143d208180d109800c800c030301a04071390042010442c10180d281d04510340b4008200b180120220545007500040104400b420141d0583d1094840c0e42165034101d040007400100b428580340a00c05c801480424200b400e03034000d5001c1c5070800c0211f01102e45a2400d08440555401c0c0811300e20010350034510009400710803401100b14100e80107001c80724540c00040d8001c901e41014500c5003034030717211083e960041101807042a000e4409640e140040349000d00307184040000c094248041151b000418010036440410340540007680401c6e0402d81d80c84085644000e01d90440c5100c0c0039004401000040010000052040311040366080c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 267899505 1250 267898255 267898283
    0xf240a030b06030603061f030f080405120a0510020f0d0e060a0b01030e060f071403010b1312030c020d150212090705040b13050415050405010b0f040204050d060b06040509040f 77
    0x4000c0901054418503099845800071070100d40d02c01c03803820854089504003c81681e5230341c6440e1030b41c240300340e0107440c003200020301031082d42410f500428980301403200504400c42c0301d0340c03203d03900c618910201414035070200e80c0940c51042a0b0880e15500b2603c0804c0c0a02c210102c41141c86500c25210f50b20074a103401408096540030303003c3c1030031010408018140aa03a903011a030300040c0005d091508200c5400c1d01c108860307260700f001c1d42c040c11a12034056222021404650034211098100d144500840710b40c4c0b000107503100360f80700c0c2a01d50654003401d989026140a031800307007580001000c0780b400801c1c04031a12290381902c0340304940201c11248480d03036440034001200e0804019541180c0c48892800f29010603402182d0030501c00e0700c28110f6410861481012120181d40861b0030b039440b50164500c0745001c3ca000c0d0005101181c7c02c514181c130f4040015084110440001d020035160081e542240e0703101000e42e001010081c0000606103002e28045842c10500441140c20703c4d406084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 267900755 1250 267899505 267899509
    0x5150708010807091802040c17070503150d1104050705070309091103040b071715010f140405010e03030d0903050306100306030203030315040e0a03030606020f0a0f020f240a030b 78
    0x11203812503180e0b8000d81401401c00f582c03207000d0103200000d01d0114900804c01c03401030312130344a10000c82c0c140344e443e600303c1c881280c210190500090a074008111061007845401100480302a010305400c690207030340c10005142007501180c048001c9039010346020301300316960350803400034401d852007613a6084400c1e84640080307003240c24100303140c41000400c1c0000b4000a00c4d500741c003508402181405031f0403030410700d02510300e500200c1e9000d6206000d00c1144546582003416480e103014981000d402c15503030030541504078015407042c5810800500000d0b103c544040c404c0716041001c846042c4183d60301410701a010341d006540d43c03406440103a4442c0c210038400d114001c00c0d00d0b0300070050b51840d165010b075903c04244515001d0343c0302c0d95030018102e0000e000c11402d4040351003520089045842e050b0040d003801010040081d95801c00846080001e00390712a0103a4550b0448101418004000204404901d0703a1941001c0c100e40a85400f28000d000001d4030303440d145560203120392842581 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 267902005 1250 267900755 267900767
    0xa080703080304111801080705041b080f07050403050f06010501090501111b0a08060a050402010f020a2402090901031103071d060904030e03030a0314010b0f070b060409020a03051507 80
    0x2202419640060010a0008569190710041900010030340328404171300d65a4084e00000a920410f0341d0340c07054134100a00d082a0065901d405461881c01021400402000d002004010032095482d208240012078881c011401c0d1000703150041c080790780224048000954030700c0300303000742c5020801d0180001225072250f0031035041c008281000d00303915420000c1d0b026203c4000c0b00000e030f0000e080c4501281c42101004030ba48140c04044010403942013034000504060030144c201070464000060f0346001c01c0000344002114803109209100c200307004070010000f40900100c0715400986040000b0034085003022100c0c9092049098400d2290f481d1a03034104030507400494524000640001405481c04546070f0f070707025000341000885414070000007410340d80b020440d280466039580503001c041640e0f112050241c907545a032503140031264042101d4602030160000c1100c40c00d00c00207400c41d100ea030064070016502070000010780e500c130701d03145803201c030b1423480390358038015400024620a120b44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 267903255 1250 267902005 267902009
    0xf0403050609060a06060f05070302010b0402030705030a05060f0121090b010810060e010e01060318050610030506131e0303150b0d050901050105100c02030309060f130905070f08090c130b0a0807 85
    0x1403907c00b4010001501030350260001c1d202542995a1803070143c0c2d8545a500045104540940e80c81d641c910345041c218003125000307012540200e40003000c001c5143d8103d84005504400a051220210001c1413800040c042d0403100400c42e08090740005441100011130b4a50300c100000140b1505171070b0181202d45080921500412003046801005524040c0e0312140b41403030010b0018010070140d40760741e8500712054a00c5840302d5416601081071080a0089070b03003200100e10b02804806940c0c560040b030b080c40600404120101c8110311007007500903401205030820b50300350340750202d68650407010030350840200030340101e0030600082d6000c0c5040c81040d058450040c0384100101f449001280c1746000c413041207030184410010034103140c1c0c800340a481c6d102249101d4558503800c0e102e0503d10842590f021200c014180f100b0310030841d4100c2d440c0007a00707000f45050351042c3c1d58406580d2510303007030101d0280c0040c041c24440465040f1900100322001066840d40c007610b90700c180855407003001d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 267904505 1250 267903255 267903257
    0x714160501050714071415030c07020603090a05010c030209090a0905150901063203190237060e1228080a05040305060a020304050a0f03050f0403050609060a0606 71
    0x20a006111035800303038025010250281030300c000001000500c092800d021a0000c410414031190f10300902e00d0484066a103444036003480a0640c2010041003c850049801c024412640400040d59481d4104480d4100a0700080240f24001002078098006d61080704401d024402c0d00d0009521111a4000c4803401d41d8490001c00c4010603154060810000151010841395211107000800c4a0320007807040358000c00c800ca000314140c41d112074194442001e00294043d412440c45000c4910002170700005854064034804140e5058180c00d0110410441910703a43d4a1142d02542402e4075441100042d540561604c803218803407041000118000b0040e02000c1d82d01102040c0000d4415800c1c1c041103803944101e0521040c0c00d549d810000e43c200c65000d9000410200b000c10511408000d0703d034100006030011403440c2410f8985075141c030700d40f04000d8074003000e6010304d42c20140303e20700300d521502c00400160745031522841d260b0349915058411401c18880c0c6c8000c03c1092f4031902c1100102c3e421 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 267905755 1250 267904505 267904543
    0x100c02031327090b070c05032a011406060403060f09020901061e030b131a09010305060901060603113a09060b040510171f0b1009050108010909081903020714 69
    0x38042c0c08844110786c0d4401211180018842e1f0300c001d10b50000c08002d40b40c1215041000d40c0c4500d200d1a08441801c81140200c2c0700703103014002a40c41300f1084400f035035044030b00419404031102520000d080d01c02c400030b4124020000018915502c150350344606248011f1207004c10000c0d200440680741888662980f00f042c1ca41243c01c450f808c1c1d48001c03104c62070b050705070442103111400070b950034209a00070303607454000c681001840b0000703101c1e03072000d802c950808110001404003081c2990149151445422000314a4280300c0078075100308080b00545503070068400b072081180903020780041401100c41c14205003a9000f9490076000f42803003050b0511702542c07042d103084030301c0701d4450403140c951145002d0b040d0940e507504955142d034508021a81c10100b44884140113014152070070301c0c0302d141000081c1c1c100380f125070381c403181160444030545800329907800c01d820290414414800c0030303810b98083c540c1000a0300c1d0941c0180c80942d02600c80900200d2501c81215200c1c40225000103403015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 267907005 1250 267905755 267905761
    0xa0503061e03060112060b0405090f0d0201060b09010804050c03010617010b010903260c01050a0920091609170601140a0e06091308030a06031211100c02031327090b 72
    0x4881055140240146c3d030110b13049540c013020400319002a90003440d2500254050007001d58208181007058410340700802260740703026640304990042c4d003040c0e070422002d540841c0034000100400010468020000c101461b541c04190000a8940090072199400c00303040110f690300511103003040366000000520030210000343c19548031010125501c08103030070300c035411458070240b184502c03c1034010300000341a0700c036051000c5080b0040514903103001e0845030080300b80d1103002c104c1f41c000e0751607100040a40c4400500b6200780803150000c001e00141e0045141010b200003802e14101c8095003850790341c04001505000254590f8007a4003490f00c1c8241c00f19901c0d00307103140680d82c003149a020a4800320099174816016900036603035898040e88521061090201d00c880100f0710000c41e0601c0d5480c2d01582c100c00d9203803620441e9507141c9903620000c0c00c80c0035000740b003156a0140c1c450310b02e45c1c085840346003c00c0703885100080c1080703a91103003214140c0e8400c81d208409541d50804100c150b296 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 267908255 1250 267907005 267907019
    0x30e04021b0d020f0c011d03151302130506060d0504030221040f090c050f0304050a020406080c010f052a15010b0d06120201080114010c290609040b0105010507170a0503061e030601 79
    0x3040403240c0522444102c45040000d0441e020b0041100d00c40412b00215540104500d0308440c0c800311006514047c180040c9036031f0442101c1c50318150340c001181640d998201a4100410f0780b11800907112150000a80801c0130070080007030f41c400541814030280c883c0031200854811001c035102140e010840c415105842c1400b030348c1c1c000d00c6101100d500e00c0c03084d8040340554030541e002103032941c064800c00c41e01d90782251040907502c844d45072090501c0702030300c0851004c1200c004c01280125414a64032030510303062017604134030214104a111a969140f103104002d6100001c12004c06107800408503c4070f802084408050350142d48030400e0742d003000c09804411015910172814480c11051400004010301d1414a100401e0080d440340010382d0b10b64913001c03a000500b15840f5030380f448100000514907460803410340b8000e280258580c00145800020702450740c00c03078100c600c40030a528400c075074084001d500c1040300707036001007040105040782c50b00c800705a40e46a501da0003101c014410f00c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 267909505 1250 267908255 267908297
    0xe0708390105220909050f061513020415182903090f0f0f010b0901050303070602091206130312020a0e040e01020405040513030e0913030e04021b0d020f0c01 69
    0x90240010f2840b0740300e80c4000690841a0b222945041d140e521032018040180a108104001d0b035000e4003030b5242103030802110a4020980921030900922651030311017065065801510000c400d642d1034a03098030003d40305884141ea25070210b0f200500206403030f03c54128051761a00303051a5026a0303540e003080c0b44180c0d0001401c0596a2040da003042d502018100b2401d803030611100c0c0903202800d0b40d08900c90a43d0820311b6140e01443d100c2004011545000089640d850341024005850b0812040041e45007024180e04000500c951800d101d0b8070315008032241c480521940b103551040300c01c17111100c140d02601043e5008a005004091030301e04194100c1649005020300040c0342a8a071000101211000e0300e41c121115403a800113010075801030000455480104d4280040d4501405400541020003c00a08114021070182d14584581c2c05a5038004558aa000340d2003203240f06a0346d49012410000006100301550441415004508814a9407040e90b90404071900448083c02c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 267910755 1250 267909505 267909517
    0x6040203060411130801050a1a090a29030d0e010e090405120c0c03100b0901031e021003020901180501090e040f050102040f0303030606022e0e0708390105 68
    0x803540b12003d5072020300c4020010710045142c5007410f000e9a0900712900e0031110014440c56559142c00c0c00c49d12031386104500201e138440120381d084182d0340c8064086018011480702d50441300e4040041c40c01c5600105809000300506030100e80551941e03c400701d8400c0300039060303503010ad44840100180b5040427900140d01a00880c02c4845100442183e0200f66012114481d800e81215600030701e24642848105c03200125890207000460b20b8000296549a040c03000612148010280300031130300d13010f840040040d4000b0001044c03007064001c0500030750b210801c807a00103416481c1c100c202e1640c5003c94419110306a5802800714107103055418a410080c009a86107412560503000050003400200040d080d07640071103001524528001c1e003910515007299055400c00c003250700c000c030041804200c080080b400c4010415800b840d000c0020000050302d41e406018150000c41c0e540800510b41804102122585080d00c029031a1081c06407040ca2200740191111040519103621403809400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 267912005 1250 267910755 267910759
    0x51005010b070b062b0201080f06091612150810150b0c0c030d0c0203060702070b120c0d050c1b0a02150c160f0e0901021204120c0b0a0501050907170604020306 70
    0x440c410f102d03100c00e16a08007001003000748901449101b1540d00100f0b040d00900890301070303a8a800c1a200003410058000d01c44180e860007400003010480c42089041d07091807405004005c0c11049100d001c51141c11802520110700c1144060f1500000c80d03c60740c0c031014220001200f41908003510f43d01c150b0f20403180085603120700984041182e4007405000940034442e201c1000e1a180c51052500300400100750340f0035504030301d100300400e051442c110344210782c650881c08803c0ea241c065000b8140103109030885a541b4020030802c1d01442080100301c1c401d1360500908800c410180516611a12908029007000d0480e030401000c4c201c1c800a04003403400f1000303035030700f00d401c044408140103042d520003107012a110b00200400003280b13400d40d4004541800075450920344c00b8907108a50000780004084543c0c0c40103004010703200d18040d0580f254806082d001908000303030441c000d0042801405d103d550294003103004140948010591003201c0c2d0003451723960b5101030410000b900002c001903 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 267913255 1250 267912005 267912019
    0x809150603030f0d0501090e060f060d020d0605070207080c1e090703060e0703141008060411011206080a0c051c0305070f0c0303120605030d050d0509012403051005010b070b06 77
    0x203e618080300d020307224404400700001034540c903040b10401030350113030000010340303820020510158014080c91070798008010382c0c0d0b0b2110341d0141c0c0301284582d01400c10103006240b0b07000501410310b50100b0807404442c0800304403114801e00c00200541032030914040545200c04052518090500c0840b2980c080858100040c030680d95901800c0b007400c0071039003400020342c1c1c0d1280200c040000c003541030304144041a14100c060420705d0311540c0c0ea0019001410366030070a4413141e25070f03100c0d0041200c00e024000041c0708140c0d0b203855080d07a13400c45040807107a1000d0b900012515040ca0071080891400c101204044407019441c1952180d2110005884e8004000e40d15000325281c04044d0340110702c00d0751007500c00c0c0c1f4a00402c000f111025005030317100f42c102d0020000099482004c1e41c08140f100e40c40003420f901c1d440700242c01000c074242405005031817181808004c0491141c000e00701d07801f803416070b040c100d1003ca0740c40c100c510034000d291444800740311381408606001c12842d4410f00203070982c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 267914505 1250 267913255 267913267
    0x212102406080a0207050d1119021507020d0c0f0518070504051203090405071710151b02040e03090111030901020316061401030c08070515030601030c090b0307120606080915060303 79
    0x46407e01e0307406041d007000300704103901561031140100107004140540c031066032001800c6500140380c001d0041d52014001d000480c000d0b0a40d650940208080d0303a0000701d01401c0c1d9500d500c0042401c0c240e02c14588030302602e488014881c036218819230720501d40da54441d4038040c100800c0000403480d07104080220305c01030021041d0342d103540c41424040e040c5512800f80f4002c0034001c00008840041c1411008103c010b420071005024000c0c103104000c103800e05211124114907400e001072a40900a076115042103100318a081c1c0210040c20803c10a98402e101002c2d010101580d900c6a003500500584c810451101c40d22403518610f1181e030b03c0f461000c1086440c054000c58001000e802c280c50600281800300a99842001414010002502c03411001694856508168080240303514185600c41001ca402c051048000c00301420400a4244e01c03800c09580c0188044400380400c0702c484d10b814000303c0c1d003a00500300c06204010301030080c480c6904c0e0344003d0342507003809449182c02d0f00c410320030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 267915755 1250 267914505 267914513
    0xe150a1d0a03050d0506031b040c1106040f03020d05040602060c07150c020606010306050f01050904091110020607031425091208120c0301030218060d0212102406080a0207 75
    0xd80c10301c01c1d0103076942a413181d0540000d8400c492018000034400c0d800922000351460001c9024032011800711400900c459010f0703419101804101e01008541c0910001c200800503007042c203e5401e4025401c40d40c01c20034400040e600c502c40d50040c04050380c400000039084600f0030300103102d8140700701c2d06008a4282041c518044d140c11a001c8000340c0c10860420603c0d5905128410081104a0f10303000b0038110140041d28900c07410501ca0700490701c1e000010300b0700c0180040b45691000c040c191a0a41485000003510380c41c00751001c000090500445400319800028001d002d084460301b00120140452070105000c4501c00c1c100c070030711183c0900080c0740c50680e0031601500e8000c1d0300c240d40c1c5800d4030300d41c400701d4407006181c604081d10070300050000da04d50069450054204601c002c202e80c0310f400002e40b010b004220000e5109408800c4400c0007400421811583d02440200f1b2003540e0a000b0400042c000c03444c80864401d000e10f904002c6144254200ea80200090400516021040c1c032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 267917005 1250 267915755 267915763
    0x15050903030c031b2701141b0106030c03051f05011410020c120a03140c0d11070503030d0204031202070b190c020603090304030b100602150408120103050d030e150a1d 73
    0x6112405e0500030600c610003c050240481c00d546400d180032502c25070100c0602100b4010400c00d04000000000c104002903000d42c41503014581000d4000007040d580c0c41c14030390714203201380c56056410300c1c403440c10944203881c060030b07060303c40818441091506030010302c00300e84490310645c01148141c040340c0035541c81c0d000180211404060250003440c1c503d003030203402080007800701c000b0a20200403048001d031002c56407000c007030b0a03450207904541110440d41d01e445c100703412a60b45800300240300c20800710598000c1045078840c0c0c405aa805000e840c00381c0c0ca600413403040d15020300040029180070020010780784d1907002141000b02200203203030041b0b200c54004480b01d60055000240c1172041c0540e42c084280d001100080f003211440c2400301c0291604604141080e90400c1000882d082100c06400c0d2006140c2506050895682d641040d950380c680040320300000c80d10340101d0348000355000c11a2444000012140c040c03944440340700d0002000c2800603107090758005a80c5600c0c03d60b00b40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 267918255 1250 267917005 267917017
    0x5040504020f1009080c0a05030c01081e0a060302011704020f010e04090c2d0b0706152c0a0b06030402060c0106051c03020105012106050a0b04090308010315050903030c031b 76
    0x141d103884d141402c04000368174044090301c44510556001c07a08204a81e0300043d01543d2010a1905442c01e8a41c44426681140041c41d18000002c5141c00c206518401d540b0900c1204e0003607813030801c4030201000b00f440704081918081c1d04954000150001d40d402021050300c0c030107005d440065030f421203072111561424550004003007070402c0c82101615500c1c5a460310203030400105104201403406148401030710864800a043e50b44505c00e0b0200d510701201004020305d003061805030380a01500d60151003020108414030b284408070003107049461503114030b0400d0303040640340d1440c640b00c41d02006405c0e0011031012100c1d6489240104568a851440c140e400c00070025094a00d04240340180c20360382c0580010550407600507140070034100c4034004041503074002100268503107991010401500ac2d003c9040d4001c3e092020100426a018003064105c90044401d07000c1200710400050581790190341600c0264000c3c800309100d04000310080d500184501c2032a041030b0524072850410341c000d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 267919505 1250 267918255 267918257
    0x15031109060924060f0d0501050a0e22050703020907170a060f030609050f010c120b01020309010c060207260a120203010311060d060906030f050f0f0d0e1801030503190504030c05040504020f10 84
    0x2807c0100418180a0010f0000d0040041090039038034102c0b203060801030b40008000c24010341402c510b0140601030186402071500a0084c142610b020700024141414502c10f00001e0413141d8009811020580b140800760740d00500900d140c1d178950346407180038081651065406001e0682c03d51012502482080601c40d11515040030100b80301001e03071b089070510f69a943c1550400c10180741d0740d80c0e000081041d4554000001a03c400040c2000c4042007461300451400803d1070b103101403040609005001041039a640e071124810131585c0c1d800980c0000e00c0000c0034802034041c1d8005920303087c00a4140c000d080500021165601c4d903940b82916200e40c002d440100700b0b030300c85c00c1c10b200c024030441c410521010014050001d82d11000d41e0b40e500810444010402c55080544241e03940203414040c01800d03425002442d6142d0811036201e41c040e281c0c01c003080700d41c8001402450700500c107640c11a608048141c03602e5240c40c0c1408041c010051003241d01003807228501465039901c030410444081c132 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 267920755 1250 267919505 267919511
    0x60f030f0718060210230702030310050a030b041410050c19051c0209010e03031216180311060408010219030b0d05070504090615031109060924060f0d 66
    0x160780082e2800321880c42d981032640d5600760a0240300d070000358a0014802c0715800040c2e140c03030322000c031566174070010148401d01ca80380c01380003403164008042c0d402030054102503004c480c0d80c1e50400909502500c0000e01c84089038001074080354038050205500c5212500791040d40f200b41c1d07113240403610121040b0034900404564031107085580c40c4504412500b07800d01c203142c1039207486c80660030032039415991915500002c2540150344910b0040c0c0340058080c3c1140d0321a034212612750b0300820225804c61000704030b611208207003071160024440f24040480744c0c0000500f107444901e241c502c0e0200c20781c0c10000420000910320340910061042c0440f920203000941c0e1080b400034151041c1504043c8603160f080e4103030010031004a010f03030848000311380c0014140341c1072402e9030240c01c0c0c4484030f040d42c07019607a0001c10f1114140c0c12001900c02101c590285035902000c1085400702586c4c10402d000907402c41840c0720000c02502c070041e43c4024000c500b41440c40c1c0c0d100000354015903d0900c0d40b0f072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 267922005 1250 267920755 267920761
    0x14030c1204091103070806150d0c0c02120c010507061503080a0314010e10060302030910050c0304060513030e1e060c0304090e0109080a051b06180d0329060f030f 71
    0x11540318020a183c4150501491810000780c001c28104c00600741d81d1141018002e01c00e2984080c4080f0741410314034601c00e008e0755140311780103011120310801c1039010b018011f000d2002513001150700030301a04161122810200642c44500041c00c0ba03c1c0300510181da072110120102d0b16a0004d8230360b6085650380032509861985d00d801144a0603800303100016485414001e5140400300d10314140c07060751a0050316640c035180010b00d010703034070361a45884500d0502881500c41204000314443c0d80549018000da858154080700f5010140d00c0280021f882001481c0403450001581240e0000584540b40e0009c400c400141d030f1a0301c81c003074030400b551001a080040700180e002e10301c15407000d14000c204294250b01d034100288581010881000400195160900f012803000c1d04002c01c5d19080743e6040c0f034102105082d400d010011401e040c424000701034040ca1207401035608480050391218404070164854084c9a2014005154005000d105558800d40c0e10b002441c4104403218081016013 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 267923255 1250 267922005 267922019
    0x80a14160b07021e0306070f0905060d0c0f020c01091404091a010602071403071401090801140a052d060418060510080a11090408040302061611060c060414030c1204 72
    0x344804120110b1031403924600c00241d030003040066001d90b081c08c24220b40c1c1c0610b0403c0303441811581085038032000c0815000c1e8051003552005415840c2030301d641c040d0180e00c960507640c604002042c980054a000b10500c04060101047d50000c03030044c1021407105507556031100014480f1140c11003050b4064010000c1d2941042900001c0201001000308100114082503d50810780541035000007a1788030b6800c103901c1160240000c181450080090409500c459001003100351810b07404241844007081803000c04c0041c030001c5c02079a41c40d03072183c2d810300e007200340013144014039055006a84602c1c2420102100940f121b0191080800281c0303441c10790030404458260742c109400744e901c080886000600030b00881094600c003102c0d903002ca91740310311f0000040e100d207803c001d4000b01c02181c0c07004c2911020406c80881c5205010315025134a400b018882c0500a441d9102c400340e00540102c0d02040610004607015002d2805581c030304001140346502d440d44420307402c40f01c443c001500304010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 267924505 1250 267923255 267923269
    0xc060b03060a0f1b05090402090a0e070801090c030209011205070201180b041a070206040b060604030f150524190510020318030a11010f021c030c09050a080a14160b0702 74
    0x8200c4074079118030104442d0304000c040380502c06c0c4841c061a40040d81c0521aa200d43c818002420540016640c2d0301e03001d48014003500b828070540c401e25003000340895030140a4000d0380c0781e41e041031f521000030017803c840070740c06400040c0c4641c081d550ba9003180d00c00b04203005001c0c1385450040700561103a0410746880500d144001c40c900711200060818001000e03400b0503010f400542051041c0e9035038580200085003885076500041c000d0f030000c01d80004000c01c00c00b01002c10075641d075040110342d82d8002524900400f242145100c01d21140368810540b0300110503a510b0090007849584140d203070400301c3c0c1c402c4000c980b4a00564000316550300c181981011410000386c0030340c01340243e4051661907003000b151020059051003c05600d02c1c1c20103100300400e481d29110480050048140c400c0080c005241441550300026026200814a400c240302d20034100e03010b0300f00074869481c0ea604ea803070340b40d1001ca1034400d55005070781c190500c842000c0b2030b560284c811002c40940d1381d0310901c100a21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 267925755 1250 267924505 267924521
    0x603060e0c03010b070f080910030902030114090607050d1104061e170705090d0609030e0a0603140718030506010803130e060307090b0109030c08060f0c03010b07030c060b03060a0f 79
    0x2503200100018000d20404600b92058658041c08400c902d506d01d00d01001c0d24001c5060554101040c2c02c0d50304007042d23160b00b08185040c001e400030840080d5100806609007011640303840303036610502c085401c1a110308014070041c00c1c07901000508018800c814012984180c0c442e9000072161507050b0407860a00401c1040070020381800d0b0f0414543c8003106015210080844080c4040490b825245032140c00701c640659600100c00c00048105140c050b0041c40d0224000b40a0500900d001c50024082c0c0704042d030100c1e801d19806c025548480084481030410410200742c14480c0d8030000000b80304000b040c1c080c1003884060350711848403204810000384290302c0883e6142c0c4030740070300c59180c40c0428180700382c620541011840c40f424800507183e1582d01d034802041e0031240b2034001624440401e0413802000e500100340115107919507405254042030182040d00700d020040c400010707005803e03c4801d03501c03030400840d2050300400081d050001c1101e038488500d4a4140742508a0418803400d14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 267927005 1250 267925755 267925771
    0x11032806060b270604050d23030a0c06092906010e01030b0108060114041206090501140103020a0b0703031e0516050301080703020f041506020f06010e04030503070f0e06040603060e 79
    0x2c01c1000051100c850703d40d00c902014680d01041c80602c01588400b011100580f60242200040681038a0808109140a034190001514040841109130303804400c450400c0e0140c0e540c214001103d80305c41e40100301c0444201c1d20754040016100301e80f1600310900b01e01c0000114540302c0382c600f1100140c011140140d04a04240c5005100075860303801001c0503030010000e00e46142d50500403005d01020740700d19084400c00c201c85500e1001000b181d43c024100c11445003000784844427540712543d034840f0013804020340c0721079203030070500001180101a0100ba806490041108500001c0b14070300100c02d054a042125203900801134171310000a600c0302143d003186003403032841d031400f40c6030743e20744a07a408000e01c10008650070300020743d21900f207246c10500440c0d20b445c0d0944d850f50069658540d01c0f002e075240d8003034040000303401403150740420f21032034040c2c0b1103c1c99076980c2c00e4201c80a14403440180244403600886080d5038a0716400703030024103c540c50001d006420030281701c540100041c0800303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 267928255 1250 267927005 267927007
    0x30e03030609010b130302040f020903070905010509010b030a2a23040b1c060f180e060a020d02070609151a10030e0304080d05040f080102090d11032806060b 69
    0x41c50303129100034904440a440c00c0c2a120501100c1d9004034040300d42c8080c1d880317030504d00d400c0405046680204680d500850031140010303598025142950800d10501d40d12400b640010009900d00c00010355200c500c105002405014108900c0d261507034111458081c8180c042c0c50905168000d0644641d2010074203480002c802904050710b51445280204041c0c8580801e06080310141101d10b64902d0350000001c0c0a01d5484c2c1d1044010300c40d9511810007031032403c9140090342c0020b4071603960040610005400030359501140c0201a522401004cc0d03420350030001180450b4123803103500cac0040d11401c0c9400c105403001d0782074130540c4d01c081011a01c95808c3c000c1e22082d6526100c007070040544506000c61a1300c0b091086908502656000700d50502480d01e6081d586944040100181e9102c5c1e80215829922410714600b00e02404c0b207981d8102405100c2107002c01c2c104400018003078001421200a2100c161004000c0440d00b14511804480d03075581500300650741c0290b4000e01803200c816 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 267929505 1250 267928255 267928261
    0xb1206030109020d030f0e0a1d0105010f0507020904030c02190302030f030c0714060f0f040801060906231207090515030604050d0c0305120702151b04051207080a050d030e0303 77
    0x2802c2c48215490050506c440f01c960100500d00404400c001210000c140c05115a070310001011150400e03d5904101d0b110140041390640c007a50180042485640d02c40d070030050b081d8213212a0391000f4009500b848400a14180141d8844c80780315400a1040c01c00410f00303145106148c500b8960346016501034006015248000d580000e0030021107600d02e000904654510003c6009880713000744892542c400090700303000c28400b07036000300205d0b00414001c01420740d4464503041202c0b03050190045c0105852181d6046000001403002c44a20050024241003400c0131240d1401010750f01c681b603e140c42e4810808141c000e8005800065801e030b001d80650726080e940c142d100c1140c80000e20a100144449005051151080e00c8403d6042d6001030401c1c149004040d54a50120f620040000c00520008103600a80b0302243c030f00f00b1001d04c1042c1001d0814040254646100c0d0191255114601002401752410480000e4060240d000b03819500c0140c00024192001d241039103034250f0042040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 267930755 1250 267929505 267929509
    0x21b0f011518090f06020c0601060909090803010b0c0715021e0106050105040b030406022a0f0f0d05070204020f0403031110090f06230a1a010c1208041a010b120603010902 75
    0x4100c030100c102c0b510000d60031040d85814206043d28a0000d481d0a10110365445201c200103881c0d4107030f40d400e4880000041e540c84603102a2402444000c0000c0320038001000903001c40c0010700102d42c1204299280396448812154000300a0003042005031302810304c106840f00b800b042c03008038042400003401091308000c0081c1c0703948280d1154220443c0c00000040c103105141d81030f6a400c08540300f01d980816040c0f603e10b01e8074021081404058041d10900312800b0100288491084c10001c0c05005030b00c0702c1100c2916a80c010703600591f0007503004c00081940200c1d10005001031807007615500d062444441d07081c0d10f01981d5000040300c0b140390691304c00102d801c03100c0d00d0b0000795109802041c5942200c2060303251800e04061005504c40c075200b40071240085412012420880e248214808035070a001140c0c001c20b251030280c040003000c040e000300c09108401940e445406a0404651304a01c0c90720307000044400d90202d040904040380c1c01c0c0030b07800c0ca0b001c0d480e00010118008e0101040c1600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 267932005 1250 267930755 267930779
    0x30423030c01210e07062a121404090e010b0109031104150306021209010b0f090112080910090608060411090f2803060b0102060c0a0f03021b0f0115 65
    0x62110305020451902024031514645a0521070010741c9041c407210044480150703580036107009031ba000c1054400c00d580303006000201c2d4400100c1c2140982041c2c607481c0c90b01a81e141107026000c0801a890880f0419804d10350700401c011700700f2040020322100301406075400c581803115101d0400c80001030070000700708000c403140c0400c1c40032140015010399035050260302d100180d0004122074004110510200180c0c0012482181180000c3c050140704504003c0c87c10b880c1c00c1c03083d9001c6440c00c014004a500e02501d0102076100f11840352400202d80000b0310a402c0e500c0001000030075040e818410190f00c0504590060000c2d18180040c002088200559000e038800c41341c003920404028020503555a0300d0310348059800389003c03103200c0d070070301e002020100b550100f503546034141045110154400a01944500642c402503402c0c8008505c0481e402d42200b8050010141c003449481c04074855101440d45100c40c075001401c0c0026120702c01d9080d40c941e40741919540c001e083c800c205a60f8194 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 267933255 1250 267932005 267932023
    0xe090a12050d0f090f02010311042d0302040e100c0201060b0a0f2703050f03040e0403050304060b3706210f020c0105060a090507051801110109030203042303 69
    0xc1010380c2c64104400200d401031200411242c42a0300b45208201031205a48084d290305000380c0e0305208080200042c039015124a100319066071040550803c1c0091241028204452220400581c950740e01e0300081c040e6894610041082d8110343d00428250f00c09105d415848103181c002071108034074050303034500d090107100a11014012036148040100384036001c19042d0f500310401e4180e00c0e010390107030a0074040d007030f0008a40b148500c16008030520300002c1a1801c5558540741d0034510f594070369048425410241044480e00c0c1c81b108070443c3e136a1050b03000300f201d03842c510b03010850b1140100d018582401a41d14840b120b80e4441080c8640365015000125960000d91590b0850000b5010800204940400400d0903840880c60022800041d042107010300700c01c9600c240500e0710f6110300400c40e20107807041c01c04224100301e00e03112100f4481009042c0201410820410040c200c0c01da801d4420f4028210016080014203104102c00c1d1007104400f06544c4c5000b4152480190201e940c8070004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 267934505 1250 267933255 267933257
    0x1b03020904060b0f2503090b070203161509050406050901291818090607030e0f0703080901030605060a08130201030207020d0f020901170703080c0c060a08010e060f1305040809190e090a12 82
    0x1685d1042d522f08002000d4000395003031082001503940c1180030040c5031070040350380c00541c6c00c40c400070300c2e4503082c0200e8065074001000d10803541d103840307071b8207070981d6074100c504203003104160603259400d90f00e07006040140d186040b8401c5441a441c00c101040341c03203444c1024144010002c1c0070030310f903002451a622209034100040d5080060310100d00e0b2070b82c26031000b98030b40700300300d400700030444200041c0c00d01d04001c0e00c0500a00f034681c0108102c0d4018076002900045483e80086c98844200c01d460100e180107040040c505007190700810b800110401d0b0580d6901c160b400c0d035004505090600d03d00400c03161214117060940f103124031740c407401c140c440540855004141e80000c000144800c41c4c0c4007038024a8a55241003942c0040c003507000034422200c2400c224800940107060141042240b891700500001d0549a00030f10300c001000050b01c1591220750601c550302083d03c0d00b859090b00e2716400100001c0c611b1030190b0b0800450340c014400c55142d0000e55036940019822508201c1422903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 267935755 1250 267934505 267934507
    0x40606050d0509030903010606020c1e09150d060207060e0f06010b0a05031e160201060519092301171e0304151403070509030609011b03020904060b0f2503090b 70
    0x340c0c5403904c3c03460260602240c1e141d460103200252083e000030300d04494120070f8a030348216001a482d01448a00e05201080d0050344c507070002000c0c003c0d001d8840601e103000815110b5454005c0d01c41e0380c1285c001c1d40701120450b03510390030804219820803800a0240b54040101120741c1000460484c1e0300404400740140003001c004180c1030703a1038120580112005003100f6403149494149907603640401c10059016502e01030303000c02c00f8285100125800400d5460030925546070649070340081030380c1d41c0600c1201e800b80401e401a0001b04c00c94a008008880c0140b0401080403510b03400c1ca40e51062400220507101c552904188001c41903c040f152152200311340f420b04a001920384044650f06812403090020402000e03035082806006003440590844110769100c1803801e00300e403410b0420211250682c500f06912500c40d400900c1c14540182c404198595140800240754021003855542c4c1640800c001c100c03409403103481444108a4101d0002042c06501c0c0a010003034075028803004048 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 267937005 1250 267935755 267935761
    0x2190b040506280806120a020a15050d060305011a0a0e04020d0f151a06070302151503010e0604020f190e0a110c0a020a1d061207080703050714040606050d05 69
    0x10500c444a98100f030600c25102801d2400c60000c2291004640301d80c407842d24148250b0a8000000701580e62a50103880c2c104018241242258000c102d91411001c000080015102818080c000c8000440c4104004144007034585a4211141c03800c0301c205000b500b1107003040000e60301c50414142c0080d01690740c1e050050450504500d1100f0b1400081c05680c00e03120310003002d110907444a85000804584410104008010840d59110b01364025006a004846880100001c40001a04068800c494011761b160500101c0d0a403401c00c3d010495503009941084154109203181182c403c20071035001c080042086e0304030240c0d0500d40038600203200243d001035071402d440d40c020351900360200780f03040d269142d0b48080c83c1d8501c400801223004840d812400a4840d01c003036511400c000100c03808641e0740e0390742002d000044845078104040f81c451044000741c00350045c41204c014500a01c060100682004e07c045d1248100303005440c011450101c04100701a0301c201510001c203204403011980d91 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 267938255 1250 267937005 267937027
    0x20607050106120c05150c0c04151a0c0d080103050304060c020d02040e01050612011503020d17030c0c06060a0e0c03182d0105060108040f030201060f060c02190b040506 74
    0x4150b640260b5503c0f15070b51654810b02c4032215101c01100c0b421142c40c60003801c40c148a803c5401000900c648562203c200f08003240f42580045001c610203144501000780e640408480c0310300b43e001c00c44055000003889001818050082c1251001344d0306107840203514540d290369403481079200e4030040105400307020046589081100a603e90020810702c4002040d0068500a16007507451501c1816076415107400707204103016030a030324900030b07400c000340c80d10350340034030607100c18840044070803000c00c03440322a841c080703007020310300545041d041c254a5000d1807080b18076080c07020705803901c00d1810000404c07501c1c0d100d803d81030f480030070b00d02c1035500c07070f10741c040384d92580a440e1300b40c00382d50700420306140000384c214019060f16071203641d09041c1071703913811040a088a000355211800107140340c0000c0c020803c1d4050f421001d034464800061724654841c0d00f10040800c9070000000684281680d00c190303c3c04e19007402e24803c1c0b0108040e400b07031500504031060311070313446500d02508002c10301d04402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 267939505 1250 267938255 267938261
    0x1051504090f020a081b030c13080102130509010f12060e0f0d080702010606110715201c02061e070c0215090103061d0a0f020904140403030e15040206070501 69
    0x4100764942405000d1100b0000c90107500082115000920860001545140304c42e07250805081b040c028140381d6107031032040340601d038004c100342c040f404001c01380022900400d01c01040c0010440c10f01c401d016080104010010300103030301240c10009001400c2c005c8840c0e40c0100340300c569000000060002107032485500f00458250388154500440400c1c0d4100341d0068683c0d840391440342e0003084140e8440c60181e6070b1500101000340c550303004c03138024030441524802a04c0400900c3c18241d12102280c02032207111110380c0710401d12908025a50141c003841e2410a8104a109001426161a00344001c20940c1d14a030319040d011001040422461030152101da2081c580140450400d1450001410f400e5409030300390701d002a00c0c3c0000042c160165410060220341d20a44444040d292031150700c02800c0c44038517070007400d0350802c804081552140308903440c4c44551b403207228491a15003005000c5a419008040c65a041504140014003d0251180c0c5c4541e04941c0c40c0e494100d281440c40c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 267940755 1250 267939505 267939509
    0x20607050f3004050c040c0909020702060f03100f051002100506060c01020a2c100509011407030c03171512031b1e012705012d05060a030b01051504 65
    0x140e00c2c4401c4034080c030862908001849940a0002c440b1750407120002d00040300d910b01c0004c000034142c0c0c41c007404540020380007000450b0000b000c2e14208407510b8525000d0740d00c1070b10000c001c924401c008020f190410344402004042c00c551501075001070340c001945841c0304007101c1c404580d803035000924980e00d420941d400e00800c00d00840d21800c101c040a4200000f0340f88405555540020070200b0058449101ca500500900071003103415010724183c40740e810446805040c49580044004000280d20142810318020b5841c110603034000e060240c0300c0b186941c0d4100c801030051080240342c600b00c41c0d00510380002914201110740f10f911603c3c0c294001d44484840680d100c001c4c81c081c0c84400100500c8500000812610981d8610390b03060807103207100c0106111000600c0b01c0300080303883d407404200c16401400080b42450311102c207201e861005c5c004880c1c3d5032070707420589100c504003489070030360001045c1c0d42d1a0065003592113503407661005201d0381e41310703810150184603548148026900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 267942005 1250 267940755 267940807
    0x6060f04051816080613051c0c080d0f051e01060c0305070203060108060106020f0601030b0a090f0210030c200c0f03160602030706050a020a0c1104110706050610020607050f 76
    0x84950304412002c0f43c5001c60b21514030075100d010b000c80c03100c5400f980d2883c20207a000c0010600c208444411078025400800050b0074004c2848400001c5031400c4001c1c521505403800010b42ca190700300034130342201d0029000d404e100000c0300c241c1400048503c19076043d0f80786420502e184910601c0c0407038440c415500009c0d0540203c030000641c0300c0c030025141d410395072281c0a9822880d80b8425150b0b944c0c00910000c1c026194002c0400e0020190394820003000e805a1031442d055442034000c1030640c000740c8501400a41c0c1c03400c80c0ca041e55031108000c600c5c1e40c024961720001d201120001d40da1449864503aa01c00d89454036842d1a60340c3c100103440e4400d42c242c0c91000b6840e0f03a02d070041c1d1283c000c044260351150801000031107003003903413080360307002031803510f40140d001916101e10345803034406240c00b600b199a03501204a81d440f5000507000a91190901090b00d24041c001d21038070800310300e020010b650058041c010002d400c14280c440540aa042e500d0300c0342201c2c0108404103203221176405c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 267943255 1250 267942005 267942013
    0x1d0a0c0b0310091103040308090d050a030c1403040506060a0821030c040f03062703020a030e220e0d030903080f0415090b0901150515071104180c0806060f040518 71
    0x41c104401c4e4074007440c0700e0307402503c0d2401c495841c2d540b180d442c1c1e00300480c9100000c6080100b95101d5019030712404201c2ca65284c0303c01040319015110103258000d640585442e48484104441480c0407540c80001d0a4024050420510076015180018030b24240040f101c41d40031002504056546e0155002082840c051a045582e40c1c200613009085208e10703064405508110380041e001500c41c4482c03615456401803c80032040d407800c903550b01210341d44591089000c1070131511f46c5420300c2d1815040c1d440010000c1e4600da8031114514000b4801c83c04001d150900712441c02194020107010f9116000031120005682c13246058054112100c0000c86141c1c44c1a0030700c4e0500440318540c0340302c0c941220003049000312a2420700c034800c1d00c51040035404180b100c0c504005000072030140c441c0b94802c1404130030b980d5040000170113030f8030851148560030035020329000c20310203400c1c0c2036402001d580c40900041d0074914086126490040003e42c003aa807140c02154102c85146004801c0b500706030251 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 267944505 1250 267943255 267943271
    0xc070605030a0b1c030806010c0206160203010915060807051e2101020a05090f0f100e011211030603101a10050915090f0612040221101d0a0c0b031009 66
    0x42802c2c4031130100750001000880000c2555004040c50069241c0040030181050100c01310118008400002241c01d9521095401e001650407615551120320814001c903180d0709140d1703802d24103040c540c00700348110001c2000704a00e0318900003441c007101065030702448a0451440300c49884052404140b007561000441000040e4028003502d41c6103412200030401c40034100800107503d2081d00c640c0d5000e490103405020035400350300d000040102c1810501104078210043c0320803603083c0d07040144840f500004001c41460305001801500c0e107010410440c0c0020801d422504104034140117008940703148004403450f0103841135800c00e510003170480042e21000101c7c030110743c101140d140d000e124101b400350b4441c036104064400c801130a4189881c00e5945400b007218621068040c01c14058086200d081189000d01c0070300d000710362505010139400f64150000721103c80c905e204c94416080519054000b41204c1075140894502c005540c3d00c0303864010814081c5401580300000c030311b18010320 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 267945755 1250 267944505 267944539
    0xf040c14030103030f1b03080a0513141005060913020112060306051303030b01020d080a0b06040e092d03220504020a0914090c0706020a0203070b0a0b10050c070605030a0b 75
    0x42c8170004820f40d28002d1840129128001c04d5004400080104200760005840d115181d031003a44e00c044003806229905520391252107000040c21074518213a000150281e0480f41907000c1d080e0070450684030004145444015a00981a0048020304010042d103081681c4e0300680c0114010f190030500402c07560a08130001c608418a0200c01c8000c00e0074234500000660022490010307006103511140101d544942012000305044c00751284e01c40070900c40811b8807060240c241707105000f40b00051102458040c150f1245030308400180320403010f500881c0180402c040260313404501500c521201c0204030103040c1c0d20000c00307034000d103402c030348049902d0265590014803c0c084500b032071480d0b41c0040061050114692040307501e07031420b40341048000001000755000300040d844510540e4207101e0715981310340102c0010754681e413803513485215180203031030141a0500302c1c8401c0d00740b043c6009011721540713440310001d101e81c405100c4080300040700e8052582000c40300c00c1000700000307009121101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 267947005 1250 267945755 267945767
    0x100c020c030c09071706060d14010303030e010c17060a08060c04030c08010605010503011a0d1a090a05040b0a0b01020c03030a03020309060a090305070807110d260304020f040c1403010303 82
    0x15995200b807144070a0b904450400010300c0d03000c2e020580e10b0001d411607a5145c00c0c403045000d040290080b604201c1c0148050080c030890034030042c51090030015501d1820300900703582c001c219081290345440c2c2540d5080381c2014200d1035080d4618080caa0319a5035a00040d0081c031136911803c0700f8001c00b010408801c080c45c0041c01541d11030002ea000142d20b038240345e801c0740c0c1580100790100300200300601484504000402556507100e01240c641040c8040403400d80340d03000d4076440d4081c480d08c000b0303804d4603054083c9540a0284241000280383c07070346851025200c041c04190300c01e5962140350341307564400d00c4101c030541c0700070701120766507104880c00900943c0111404400c41c020640480c0c44900a40295006540c06903200c40c00c1444030b8503003040552200508030b40c10f0425011500d00b5884041c1c0005d50180a0b82c0c010301c00e66031404850303076240380305580a01c00e840204100401a5540c805200210006880004250074001000c1d43c040c800d039000020b00c81e1005c0000010954441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 267948255 1250 267947005 267947023
    0x5030d0c031715041d06071107032010080603100e16032a0807030b070504081605010908190809010c050303040b090106050a060c0b06011806030f2301060e0102100c02 73
    0x52010000017011080024586421300b0605006030080c1c004112241c0c81400d440404440351810307100944e030740b582c8442801c10514603041042031168140766440c03401443c2212003074000e0400a0320342c9401c0e4006911202140b42880402d0f035221203e04540070104420840f600c3c0d402080d04003c1c1d02d03410020541007411101e0403029042002d0300360400504041041150280c10003010440d046548900750301000a088108020040c0800151101c040110105108000311540282828580014030b0352009412501880c1d000142a800c105440510400e001750081c0c0300030b4940031003900403540706d01c02c01000b8105220205c03d00080c0302983c1001402155440000c1155a50f45d2040c440c800c002403103080d003c907054441c034001254001c0c1040d07501030414034004038103040103408404d11406c55000400007942e07c2155008040140c800c0180824141620200d2401d41c1d489420701c00c101401100e0030045204620846079008000c01159480448024400300d0840d0f08000d55441c004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 267949505 1250 267948255 267948259
    0xd0605030a08070b130209130c0e0105061e07020a0308040801141b0901110709020d06091a01051c0518010b010806060a0c0302100207060c0206010f05030d0c031715 72
    0x150000415203000540e1580d81a0700c0b4160904028031512034140580300200b0102c29210300030054401603844e021841d129110401c0814041841030800310126012600035003c40e80b50100103000507074441d801d031408800128022080f841240c040480e036802030405c02500800c200e1004020000d8640c09130056444600080100e0500b07003010600100c025141044116941f84d030b0000380400c0500144500c1506040040c0104581c050170785c0342c10f03034a9101c0020343e5808103404030004003a00500d001484440d10501c9042c8100300346001d0410040c0d06d81e03051000006404a03210b00e031104020503841d80013002c00c4a4500010380080c603c4158040c003070785500c0c00782c15a04035801040450300400b005407186003499600329096503201a085002c0c0c081d0b100310300c050320b01e03145280010100a84503c0d400301d0505070340c44010303140603c107030012044134001040500c915180003a262440f0103d9150108a0142e1030409071074408004240e015110184001c11042c01c0c3c800280020007541 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 267950755 1250 267949505 267949511
    0xf030a020f0105191a03060906070f02070503030409050919031701080a330203040f03080f0106020a11041d16090e060604091103070602060613052203020111040602030d 74
    0x80e040d4890803280210369013550000302046400003441154400780014005c2030b01e180e005c0e00180006841c0c0030381211207802d0742d4000c10801030965840b02002d08891303514002000c0782c03410840080d460b80190b01030040b07901d0741c2e00c0010b11f0004003009012505c1c40080c3d050410344d40c1c03506001b080360315106040e00402c0c1d5040c000041242000966101d81508540c0d24110100c90500455418a0400d5206950800038540300c003064070303a1005500a074469020210108403e03e8040c01c0351000801d078124607140040104002600400c0d5030360203d504c20201d46100c0d2100340024020001626040840369041c20a54001e1100040003040050203d0107002e40c61354600100058444400768401035811480c081052400c089d08500e4100f0300c03403081542d43c0030036100445d20301100c0e40c0c803400059100c1000c0c01030b141040d402140301301100132000c1c0f2203840c103464582d03519200e45080f010141045500f06003450310130762013640e8000081c5103180d41c0700e5899070025a01e8010b41448140c9601d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 267952005 1250 267950755 267950773
    0xf030103020d0f241a030a020d0201050408011d06070f0212070516170601080105070e090a0216080325051602120102040611010510140d06020d060e090c04092409050f030a02 76
    0x1a0280c202c80346414014007d1841055680c2440307107111107020100e050140c10311000c00c0c401002e000300c1c546c3d6813665135624190000c00495500d0400007800400602c800e0442d20080c2d42c1c0c0c0800c0e02c035054030200c0d00c3c0980d10421890b10500c0d0490403c0542d0b0999598900400c42010310b004601c16003403294100e03105031343c0350f05c0304908a90013515007101060403240404500c0c02d014940c1039001c1907010005003080345100b101416140c1c0346804450000d0b0003c01c2000c0002540011813611040b00c050000c1242d898030003400620070558020521200c103010f00085540c0c00d4085103c074100e0360003c2d506c0725075615001d4160301d41000303994425424040061080f0075004080350440d081483c000300d080d8581c00a00442c000081030a603010740d020419058100141e0103118000d0261036410030b25403414562082c00c140091070300034072640c14a0002c1010810700041400112801d0f240e021032003404a41060041c9140807004000340180d03509150964000310240900401c15000d44641c24 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 267953255 1250 267952005 267952031
    0x9020f1b010b01020607181203030b15030714032508060f090925030c0e0a0b010c0b04020f040e060a09030e010203070c181d010f110f030103020d0f24 66
    0x10000001540145d00980008500303610407600c000380c2d4044a003101145c2c80d00e03900145040441c3c01000ea01181c3c13603c41c00c3c41e6908240440e5081d001d0451555415803e00081c01042051105031800003004040080303854500f56109800c0251201c80c0c0444030988000303c09004004210342c00752041510508030310710380c00e01c10045e03842030820303c0180c0110802c201071310803446900103040c0b00d0581d40760404400038911101190290440740b11181c41c920303200f110380e0103841103a800141000140c0c907502c2c000401c460040c07508030f94115504074a0344641c10206d8001c104802d40e000e4603116500c240000091241d00110070580640d554440c0e48070600016a0349101d401c900401400401100300705002604021040d950072411000c02c00041e01d4525044841c1d00304601c1c006030350b4906080d905003125100d40f03070a02d00c07290b40c83c0f818800300d000220f080703000500c0064082c1c10005001c20410242c010b0002c0201d0344400c40c0101203e03400800c00446002404100040c1d28000c0e8a905172 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 267954505 1250 267953255 267953261
    0xf060506030106051c050115030308100b070f060507051c0207020f010309021305040c0504020406020d0807031107020405180303011526060d140d05090a09060e18030409020f1b01 78
    0x3d502c014005400b0001c0500884202e1101720105448655952006407400d00d04962808021406552205881e0600303c25040b81d01d0002d501050500e0001c00c5040001406139010a01030f80d000180040c07031f40c0c1c8115090780d82d41b151004141859008041c84989026280d0203080301e24000c1e6084441580c000b0019800c441040f40040e5000070814245001034800d500581d521501c14000404600d40d99808a4113980060f0015000368122290080c00c00b98084640c5a0000036841c1c140035421a1004090280c403032101c003e0700598444002500140030380b0119843c5507401d104807982c80d80d451204220307614030a191440028411040e00076a84d00c0003141d40f01040d0744202c24001511000c00300140041d48103c21105221101400c050f10329003030042010162058a540c4d070b441504100b005264402c0b07070064001c003441d05d542803201504040300c480e44a601c2c07400d0302800c11014100d4620b90700896004078001d41c00000c190680d00294000f5110351143c4064000c130700c1691012490903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 267955755 1250 267954505 267954509
    0x30209040b04050309030d20060105090117010618020c070b0f0315011b0c050f1503150102030c0604060c120e21040503060c0405100f08061005090d0f060506030106 72
    0x200502500200e8049040001001d401c684100101c0b442c1046420219041c202085034060204003c190b940d01b5211400740c551081d21081d5000d003201c1d605050000b88042418011940030910305545c0c84030b407103025030008014104a100d10300102c4201001e00019601c045440c000a0085250018182c00b00b401683c103560400b0b1003041c1150f030341500c01111040141000381c100801103086080079540c1101d0485413030700070541040907900f4071301070000b1101c100001d203000d21662440100b5080134841600d801444402101c04589140c8004034a5401002494800342c000c41c1c040c002000425400455044480d407156204101500d614000300c4840707441000f4036401900c919070410000c3c0c244020114a0240086c0c182502d0714082450310318211030800302c2c08030014090016203031800070f80061114901d812203060390722a60042100b00040c0c041c502607480c00c0c14112a180c02030f41992509071000d45400300b40b41d041d0400c042c1d0856000404c1e200603140401083c0d0385d04040c019401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 267957005 1250 267955755 267955759
    0xe010f1a0711060d0e01140705070206270a060e0108060d020603130303020c07080601090b0603160f0201092001030e0c0f010c020a03051516031802040c11060910050109060302 77
    0x10602100b42c95210000111078800c582c0110104405813007415030b4403540d400400941c0c00041c50f80c641401c40b05099001070000c0c1e003880014040e40c0c0040c2d44140c212540340100780d0700a419210f44441c41800d001283c10215401100d401010171141c0c5e200d40d4980003000c090faa07231a02074807202c00f40f0610303a012680c0650443c3d001c0000902c01c09901c1c42500c802031003850010300d40b0325550040c5080c10501d422201442e0130010041240310440d010f00051840120b524901c0d42c2808500c1d403442c0204c013600c0c0418003008100b4030419500070f44c40000c0c09500203490300b4032460810f449216801c0690401e80c082803401e103810669990018500c1001c09018041140710040c031001500c00360541e003000c990004444401000142c401e014600c403403010300200c54000e08004e580080842c807074405182c1018036000c2940c3c44c0103480c440360541944c06450002c2d101220880848000727600100b040c04510911043c450005400680c2c25031803103010008116507601c8200d100141c4642d0710001c0c2d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 267958255 1250 267957005 267957007
    0x15070203190f140a1e0507030206010504050f07111914250909050a0f0503030103210806010302030a090b0115031d0604060b0d0b070302040e0106020d0f030e010b09010e010f1a 77
    0x3c41d0035040c00040c10000c6203420944810050084407012424800606000043d40420060100354041040501402c01150140000d1422090800340c900000300f00307804200240b26072513404a4144a5051940e41d20384682ca500c001c1c900b8803100030311124503011500c0c414041404002111001e0041c03a802c02d0040c0b018500d441c182d9001302500b907221003034580c2e0140f048401d0000c0d5040c5a6020700782d1158000c1d5840307614504003051680c0ca84550084903040102544d0100380d448512070340e01c44800d08006031243c640e80d030041c0c02000710b02401401c0c0c1c1c4400d00045107082a0343ca40c41c611180c5980c0a00c4107440b507006046460340c46611070501d03540301c0800b2a0010f203190308103010074000903091006600d07040c3c451403502c00d000d85003000403c0e40000c0c02c0c003803081c2500703806014011a0004007148007802500409401401000c80101903030f5030421400242d0a400c81c903510382000340788004550710f03188000c007078072020302c03aa0108a001101c0050520103d851820502d65011601 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 267959505 1250 267958255 267958277
    0x3010209091503160e0f070512041b03050303070306090f0b030703022106150102010b040c050a030b040617150a0e0706111504060b0405060618060c15070203190f 71
    0x100070315081455001d9143c0a00c401c640304a94451304960020054091031661606051540d8041d40001030003060030000c0810080c80c04000b601301c81030b009544000d002e070b0b9142c030783d001406406a20b07800042c43c40c00004148000650300d50407007030a03a00c00c0b80c001c1103810054901203080790030402500ea019004032100708094642250120b120811310050b000903000c00c2c00042d410507000321650342400e0700982800000396424814a0502407082d2010001c0032200e0a010348940a0080c00c3d504140d283c401c038030155141c54002130001c1007001e030290301040c21440a0b5884030900c00c030310a0007004d03100004070345411a0261404207480719000c0e100e800e0400d042107400c3c841c0107014454070f11403110140080701c4207290451107540031303140016014045400b0882650ba02500e1300d03200d200140f066005502d0644020316006c40c00302e0f0030ba40d4a0b2103e51040d03060420199000200e0301e5003108000400350048010302c80325807400300b6171860b031902480694020b01c06c0d0740b40f600080e00d04014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 267960755 1250 267959505 267959521
    0x1b160f12140c040518160608010e04020d060204182003040209100302031902030d08090705040213051507050d03090b06040504031e050c10050105030c04051b04091a0301020909 77
    0x1c40012000c80c14256168050800701041c242e0300c0a54002c5001c60440c1c0c04c4116402052040c41040252080078004252030a40001d10085041c044c00343e100644c50040741c11556280103442e042a4055030941d1141e5542034420f041c00d203000c0b080010a403c0c002d80c0085440510b41a104000300c5111041c2103450380d4003402890b03e4020281c4420303280c900301c04805030760100094003810f8015681c1c040035818520600d410700151550000a0141ca036050045000c07001c030307161003030711400d0710010703180d1902070400f0041e80c0c2e00b40e2000d41c01208000013800060302c114010100180a05c084440042c99160103d0490301c20510103880085208080744043c5083d800c01a0440c0c040d190000d100c40c0083d004000f05100c000821012035030024202d01000014408206a5081548100b00d958503080129031034003000c90f10107200380d07610360010314400d5120501c0132000380301c00c40040c2c4850300c584080004165615404428400905a400d0107180500888107205000780c14071240ea00e800003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 267962005 1250 267960755 267960773
    0x5070b0f04080303090307030e03030a090e06211b18010e04060e0d0206070f090e0103121110020705011512240e1b03120a1101021b160f12 61
    0x5403404120390401000442c18802c10245001d1217040c0d0155a03110043d207400340c94101310441007406504244000ca2055410041440846490388000441c0d036035001e002031802040044d00a12a03500002c0c60b250100c0c001070100b01d004042c0881046030b43d200c004100210001814164041c402c06005100d1314140e0b55403107070441d10504021508882440d907050078000f40a0701a030050380807000b0000c900d81c1c840d00c4030781075000c0c909001340c5260a09000710040b5005001c003500380c2200085180c1124800c1e125090480e244505a4102c0c4000c0c2c1c41d45000f95000c0c41060796507608040414028000803d8a2811181c842074030343d10400203a03480000c051842c14240525a81b0384000d1100211140104a52092850b0181824040100c0c00c41c0310003100c000864081d6001c032101100018014048968411281c00d0640000f41c03c8540c140c00392040d400c00086010011447c0142c082d00000c9a0305100b00425012200756118244281c59002e103110b5402a200315a4400000c569404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 267963255 1250 267962005 267962017
    0xd0c0c02100504242015010f050a061805030118060e06060d0201031505030d030f050f010b1b0703020604031505061009120627140303060a05012601030602090a0503070305070b 77
    0x10030140304803103007078044070703c0040340c0d0314405c003a0740000303180c0e1842220b0588058003414460895403120360411001c5102864140140c800f07001c84004025481011821600000c0034024020302001060300008002d011100740c04480840c00c0007401141400007081042c03103900041c0014000080c0f680045020307103030b0000310301407010402001023100e440c1800703800803880e5151008074081c5800b1280c401100d4000f0980c145403030004006000800e046c00c00c441200300c2462074038500306141140f072420000c4036070000b0350101c00090004200151b035a00d55844c1120a84100a41e540701e10070702803411010412079001070001d0710103003c80d5041c9007000507031600411001408480c2c11b284100c4400c0c02c895004000c600030110320301044005034110302d007124081c0c0030358103504000020408801c1d15000e81410310036050142226503041c0300c031094095407020385913116541c0d203041034030003580b02902290080c0106035000c070342402c0001c0d84030100d1303174050b0040908901d4103000b07102c42e80003c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 267964505 1250 267963255 267963257
    0x210c0c10050c0d03050117060408041202060d020c0109020a0617010e1e04150c14040e04020d060203071d0307030302120a0c080c0c0a060305040b0f0c0d0c0c0210050424 74
    0x1031122001c850810401a0b02500d600d40307001031a541440c062210641d05c01946120a5001d0740400000403131a078182c0c0d0031262407811030401c10702180300040250040b04fc06a00c07080c8007040d00341403001c05400442d0f025000b40e800454083d01e5207401c44103050705580101089000c00e00402045030b14541c46540040d020128900343c00c24564074028800041c0d034103981d040c1a0042c84510240c407480780c1180d0040c1c50030070740c04819013194010020300a031b1082c401302e80920f000040941d1908000d11994540c0f10310f04650304e2074201c001800c038980c40441c5140103015154140c1d424180040c2c1c02043c2c0350141c0041c40e4140000c40e1b4225550b1140a4101c100300c02c0005401c000f80d48a40541002585400600903005070003040c01070030b84a580c061b02c101800c110501c8046101000400d402130300c040320390201955481800c4450384582d1385406026407800842c1800507900c203c911040b43c0c42150403040c03022072403a0856a9021b2402128040c03030006c40391180c102c0040305500c601401c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 267965755 1250 267964505 267964507
    0x6040f02120d170901020319021e161101050c0c0d14070e01080c0301061206020706091415011203021c02150a051906080c06130e0405210c0c1005 64
    0x50208080c00d18001c8246800400c01100303c00d0740360315003a00381592210f000c400850461500c4011a0b5114407401c042000c216800501c00451502c200d40504c031190580302c02e1a61524005101003050035051001d40380c0804402c3d081c000f41d88603904940c59040040c0c0282413081148042015460720000101c07440303801400300c80c1d607840042c0015402803c0d800c580504d2580b4040b4405c0c03e003085d440845101c0d901d800410f0007500401a1085001c0307412140040e1030380024034091009000c0b248002c0c0c03c0c0c140e00c400e6801c80c600b0004641e0b02070a00000207000b1a40d03150000d009a501c10380740103015030408030000ca0080038003000d5003201100ea1040300c101e05607403910880300700d1040c0c5200003035035114000c2000b2210400b00c00000a045040200305d01840e2030411920f91321455002403249c40c0c00615100385c80718000c460320180101c1100c1d240d56080a160581d51052162014a804444400102c0702021000181e4450414003000b524402d1021010041081c0a0301c060205203d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 267967005 1250 267965755 267965779
    0xc0304080105040f0218040807170d060906050a06020a020d0206070807170301030314280203091c02030d05030f0703020304140a06141021050a1415150306040f02 71
    0x100034040c02c0c2c0110300403007400d50400b0150060081001221442c107560303440e00d10910002603000d900b2108078642054202e5080326540fa03034110141302c0c80548201c800e0074030740c010071400750a500850494004480b00ca415507501c10059884118028003c0e500000ca002c014001d818001d0040404500c18880701d442c0990311784d1208000808407240700c108080c080b0040c420035030444001441601810801402c0095440302084400c4e0b81c21440f070628901d070a220b044440c001c00a4801700070000309140f41000548a5041d1002d07036203174040c0e1091180070404110383c0c0c050011280242c20840400351541c1d2081d0042d00030f9403002d407084035410401c41c08a09003610074000a1b0500e84200000304141341c00150002d003403407001d00840c1e004080c601e01046419407130382c1c00ca1f0f682c1100d003041400c4404581807003810b290028402030b0031180440310005002a011030441c41d00300d5550244400c546071100e07001490960600b9103034269103d05e0101d804580001104030840f80b000f440c01c52022 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 267968255 1250 267967005 267967019
    0x9060906070206120a1d0d030e071802071a060303070609020607080403141b0315040f0f0308010f0618061d15090310142205010203010611010f060602030a050c0304 72
    0x1d8480c0d031300403944400000900044a249010b90f0b030403070703180039142c441040c410810141c440d02c107a1003201c02d042e9103a4021418031401c3c070100005000b1840585895440b04c07801c10065400a0f5080341c20b0704140c0304d13031401c060a50684501460014009501340003090b6100401070992a00a0340e0003d400d11030396000900031801800994490a2015400d00800c0300e0540b914015038401042c0c40f02c0201c86140c41d032800900c0c91104480801c0e04850b45e11182814500c128840002130280d206442a10f420b0580012000c1d0485501c900d841e21070f2030f130310101250102000c20303a113946451604410440e15107d40402c2d07a100c01c001d115080490030210015040030a80b184103144c00c1c00102d04002c0d103140a12010100d20500701d424407480444914411030744000400c14079440304082080310000b0380b00f15030265115030000c021541c9507103507000078001143c0e101407a5138960900d25070030805015406400201c840700c1d0021402c0a14101c000e56440d0031410030200c0902c4140000a504 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 267969505 1250 267968255 267968257
    0x50703080f09060f09032203020108060d0b06100306030203010213080f19060506060d06080607031409060402060703110303010914060607030909050606071e03110609060703050403170f01150905010509060906070206 94
    0x1800c0865006580c1f038518030025108641c010304070742c4100c451400e120081a0f46d101110390000c41220551803c49448609400420140e0406034141d03202082c1001e21000ca91020001c2e500600116500c2c018508280c51b40e80180070000c006030b828001144000804035041550007102c028119400c00a00e41c10030001c4031071a5000501c503604c0324040c0710074141c052240510105000030001c040d80740c1522003550f00c0b40e02402c000d00800000603604180b40c41607a0144e15010744d030040d81c1e525691240d0442c043e100400a12072414008004940c50b807070604201c03030040c1e9041d02e42010503031914841d41c0c007c3c2401804650044001c101000001e6980c84056121064444004541042078200140303080d050810781c010035402102800341050300000c400f6440b14040c41c0104080d5141c0c503046480d280102200d01611110341b052100300c803400040c86050b40d46400d500c007040408010103c5602c90f40d0b00c80e45001c14000c10400d12507050010051007842000781c05149014107035130200f103036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 267970755 1250 267969505 267969547
    0x807170c0105100f06210b06070b0105030d030209010807030e0705030a050105180d210b04020301080604031814010e0409050f0a0c081f05061807050703080f09060f0903 74
    0x101d940d039504100c54031284202c028050b000e0000b00b460200c2c1040780140502c94400b9400c030894010007011001481036404c00524042c0c0682a00d0f220b5449190009581c0c0c000e0042a210b4020b142c46545601c0c468801e5a0b540c640581d070344105a1148071003a0300030062841c09100e18010400081865141003140c0b18001d4480d500024007440c2207459440e44150107412141c170303900035423a20611254003c02c4101c188141d10508e001d0080c1d215996801000304449494101d8000700000541000c080340891041303001c0c0c1c6031480c80380a100c2aa054400541c080c03904011108041080d00d540b07c1c0c16500c4030003030007030000a80c100540e00c40d54175042903c0440202940300100c040700700490110650002d12075140180f00e401da107800140112401802c40d02d00c910758480009810f0754a0308142d003180108440030340c0785400d1459008105a02074035060703012501400100c0d051381107075002a44100e4208016281c103886410034452508000341011501c0e11050040a0142d46a4411501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 267972005 1250 267970755 267970777
    0xc0f0d0c110a0326042c060a0f0b0c12070501240e060603040503120703060519030503070609030c06050106020313080c010e06210a050a050f0c07080717 67
    0xc0454644040720315480d5030441d01580b000310082000034440c4403040e1010030a0040104102c500750714110540c00b031640300b214900808030551028442014160040341c140b0b40b02c0651580d0307403100340004c40b03445109007083c000701c01c2e4007007142001550242107001c50000599881d2506032541c43d64940100101780c4140c0d540c0c030300350b181001c0c1c0c095a24402801e400fa41d08102c0c2c0c41d040421165600c01080c490148100100050800c50240100c80d0a400016201c1d05c0070f080840e0028014581801558001d01404550a9141450042042c110f0303038468010351030070074669a0b200c05004158411428490300b514120000349440c003405018200990045494440f581c00a6805c100355078440c04840e04120350024071079900c43c508002e214070541d01c80e6500ea00e1800e410a0900701c014074500e60b61070000030721240c4c0d0407540082d40161b0f6041c4050203d0344503000e07000341e40e0000b40c4010544c0303403040045d00000380c0001c000d0414a4003514420b012913182d050780403110b500401d4201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 267973255 1250 267972005 267972017
    0x50a0f0509011a0703030c170f0105040e030f070f03090308040303080a110406020c012d0201090512161e021011160510050d0e010c0c05101103010b0c0f0d 68
    0x4021030030181e403403074018866048030704030040114a00d80750074460910301030105a211440090380901585824084803820006041756151040d040312449900b800b502c0d00c60703801c0a80d612840320000081e1084041040341041c600842a90b8405501e07070031740d40c114288204004000b000c121014094402103000e500d0b50f1900d894407010300001ca03012074052140f1344405100910801d42d0000e03000c00544801e081c2501c00711010a1400c0461140f5541c03440280742e00d40619601a1f81074102c009039512403c1180d40d40c079140610400c10703000b240d4001d41d1082601d607589010400f4403111760112101ca08122a08509035000700d108403130090711503004240d004d8002c0404140404c080401030b84100700603100c3c24141000100300c1e1080c04e5001c01009400301c7c00042002c5d056001c0041e007010b0300c0c000c001c008030010000d48000d04519040d1034034010a1081048852107004003602001d08068451544e800c044000c1c2c0b03950022040c044c81072040c410226a0107404125081c507852207610b0740 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 267974505 1250 267973255 267973259
    0x6030c15020106050d08090f0f0907110c0603040b070f0c020301110406110705031906020c06150901060206010609061b120302030114030102070503160f0b040602030f090c0a09020c0304050a0f 84
    0xc0c2c00d540711a400907024401500d84840170a1a2000703071040c1c500100c07900344404a05100050b81000388502c007541c003080807400e00581c4c0f03820054a1003968184002d85220a0440c0204030260008450181446540500240f80544a4002c428030845c488c1040c0003800748540100382100c2884643d8283e1103c00a0305000654210b41c0c4c642c1c1c00d11a06c402000124180404241c980c8400104101c1125224014008102c241c0e0140c41d1250746907070456107a0b2604c078001c0c040c43c440f140c22260041d285200045035161010644905a40d2551100550309103400320440342510740514000390704020422481c00500c035808c0038172851417a039030056200e5040880c3c107852503001c2c06029109a03c10040c0000058020054400300c01542c4d186262040311400c10350540c88001000802032010f107401c0104002d034640c00b460061170303a402454100c1e5103400d41681c3e03440c0780a030003d074800c9980d10100301c040c055070010302000b81da220680c1d04065490010818400d0141c020608580e125601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 267975755 1250 267974505 267974507
    0xb0d1703011424030712090503040501030513050c1504030b18070602032109030c100e0616020616050c12040302030c060906070b040f082115030d0e030106030c15 71
    0x41240303260b500b21004030085044a842002140050100200015000c0002507000d0300443d804201420882c2c0d06112514051a00540300d500c10300500740401d181c0004603040218048550841c16030000061400100d00000c010002600640c0c4000600c0e00300004400188004151030041d5500503181546190040c1d10600b4640160402402c540c02172100071540485040290143c40ca5800244510b03101e46114a00710f2180c00035504035881002c444011403400340e0702221a00b4003403070607039445860341d03408103440044030840c0c071005903c0320000c40d04a0341e4960a003c02d60180e4100700d0701d4848d00011460801014600c2c03600c7c3d0201c045030810560409100c0702c544240121041841c06080e5400205903009031351014250340c42d80c20005040058002c0010710250b00040178544802540c4a458108001214015208948400440c08031100d00684400034040203015042c6400081011038402e0549140e840d455921010000003003054060103030064401c1c054a0035504581e010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 267977005 1250 267975755 267975779
    0x223909021312020a03050703080706110a05120603010b030d02100e03030903071e0b040602040312020a031d010201060e100f0e1902210a0507031107080307030b0d170301 74
    0x121816019004001031403010156140750390903210a002c200d018550300e030000c6a110002034000804174401c5440c0030050003003000140903e640329820a11000c070703042220b45190300403802c0c2c4202194050061041d950641c10803c0e074045806000090441d0040001a14044840f124040580c00014500c0c41c0c6966500400c502d155000e0300861a6040001c0b00d44d60340d00c90010b02130502c1c40444900409030002e0345501c160030303800c540c01101074140b50806c1e00c003d60140c8011a800c1040b109141d0b0030a00200d0015012500340e118a9110710300f1184101c4089030007030140d0b0442d580d81c44040f552111081d54240204102c038030007083c0e02c1c00c14026210780d441c9904010b00e150120400c001401070040900c45004e44c4600c000360f1512010b002c0454100110354415403c48128000c000644405a015620424150350213202d2000c10301d540a00d20310484001900b084010400200458040d030048902030a01800ca0001d4a082d61680c106d4402c002c884080100c1000004110080d4908 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 267978255 1250 267977005 267977009
    0x7030e0102130b03090f030d02180103090c0e06191211011107270207030e010806180406020f1e03010603050c0c0a031220030118052239 60
    0x21403802d038860100e81082d80039031007075901d10400007000443c0041c0030311400510346055401c49440b01240c03640f80d000303500030008100c040c810354104240d06610030301444e03400541060000714040d051003d440f034005c00041100e5044607018041c12a41c10701a8618002040d1440110900300c02c0c9260588007820b030000b465042181d039034211280094085251801c50761840032031410075200d04002000c800642100000103840410184103158002d010b410071002c3c241e0320600c207a40c840082103001000c0042900e48501c42c0c5001a00040481d8000d01c0340e0f82c00e810f001400c1030000601d04601020342c0141411039036001c401082041e0301405101d4000181003032450414003c2c03001141d0342d01c09075a016080108240082400c00034903801101a0000d003c41062070355031091109003140d10038806d0007214500c803848103080310054071405e0f000d03502a1800082c800d800001d640c182c10f01d443c1058a005517090520910003451381d40c1c94150741c284404007131030114079031b10f0000044543d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 267979505 1250 267978255 267978281
    0x50c0706021b0301140a0506040b281e090905211809010501080703091a0702070314242e06020d030515010f05040302090405250b03060906060c070303080703 69
    0x803c0c3c0085e5a002c0840c1d5500c0b041c2a0800202030307540600040282150f202e4403900b2041e900d441e001d940c2e00c1e0802481b40014100c101510803644d9a5041d1040801000056a880c0b00d0309010b0080d251613400c05a00d040c09801100c00300c04160008001821825010401900000039000c22840301d0b4240200205000c032000a015858480041e00c811001001d00d400c041d42c030841e820400c90b841c40c1c58290302c000214090402e00d010a00699039204a00050381d102854000300070001e040001c032582e80d10000f00083c00442c241c0c0c100c07250460001f07003251956810b545001c100d028031891143c0c074041001145403000e9440d040000c1c1c1010300c22101401010b0130201005221000402160816802807034926000d0b5011942100c06000320740009510156140500041c440b0004064460f549501d05c2011540c010100d090802d48940c0b103842e40c541c205000181c0c40c0d2418044081d13003c407000e40803e25000a64081d0707410211240c1084001c00c1416050004103641031003403040590031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 267980755 1250 267979505 267979511
    0x1b0313150c02100819050702010b0102160f0501050a020304080f0102181008011502011d0c01170702121b100e010501050411040306020c160303020f0c0d21050c0706021b0301 76
    0x8540105490640501d100c40034001d0b07403000305c0c40d6100001c00500c040e1034901c00801290410140090180207902d100a0040c880c1e0710f911030007480600c000404890301c030107034082c0c814589030064072281c01c1548820103501060200048600d41440488a040f50f114001a074500524001c0c00407540301d485841e000e05203100c500d644558003c058181034641448031401c03a80c0110030b04030f0150480d03401e03021420102d1a420405070070002a0400c642c0826200c0b807480e0160301020042540044805000590200c503203024400089001000c48003407101200ca0b0f8100a01d1510386000212103040c0c0100e6610301040082100a00c00c0c036000d401c04513014040c905544000090b0f90190b030001400d0075500088808041d80100300b00c005080100e841001030039902d0030b02a4890000d90801406400b45449464107440d10720b03101c1603c103900080daa040d50214512041c100d2040c000340005000c8d0030889884550070800104004000c1e982c0200703a8030702850492006070448600450080c0c0c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 267982005 1250 267980755 267980777
    0x90501060806040f0608010f02040512030c0a03080402041503150501150c1509021504030507090213060309170c030a02071d0601140409050a020a0807020a0506010501051b031315 78
    0x40d0001c80725400040c12200400c400c00b10030000e00003028a5804107580e0343c60320007440b080e60201d030058011100100e41824040c2d00c400c0406440e0f104080010005400814100c00003134086c400c400d42150014000180d1500384808102c0d42c210144c200b55690049030f00b45a00140c1d46000311400f5100405001d485c01800440140040e24041da004003408100f5100c010400c0b6190f1140503091b4000749190303400860036100c2c900b44d50250206031103501410700040350803070b00d40c022240c241c420301c01880c503250315001c0304500801c605c2030200c1c0c500206c41d940c400180743c040040c01d0200b04d40c002640e582c42c0001c102a00e03042c0b01d9803212213180c001c2c02e00400704101603c062580414282000d880411524541c0c400d04e04c102d40224040b503103440f0030b0010168456018010907200c5803120303261a00e891109980e42d80c1d4801c070007042c1e980310b0001031002d5446030020b02804903044441d0714210484540607810b42d0000102e6200850290100b003014800382503554014024504220154038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 267983255 1250 267982005 267982007
    0xd0507090f09090302120403030302040f0e010501050306060c01020c011a03072705060a0f0b0d0c0503040b1b0d060e15060703022e09050a021e010903060506060903160f09050106 78
    0xd0704502c202401c45544801550a1500a00640100c000110820356580b0785070301d400b90007500070340a148011b0400f0000802c6805a401e001410b803101611103506642d10041045881d0303110344840703105550248110a07640c2024014480d07440601c0c907004412a242000b03140c0340811650014003d074048002250880c1c1303520024a0300d034070b5071040200703c070764811020421409007940525211120300e0400a07140d2250400fa0001c8070448509116041001104482901098802a00c0403051074041454041c440c1459102c011210121038107109001a00000f01c6009900c000c111588100402c10007142000407111400800c80b81c680c1484015200250380d668018515202862035526003140200348181d100280c8a0303802d405d01c4520941e25200740c0b14454688124090f8607900702e00f0b25040108a1b0800100c28103a607000b030720901c3d50700c1b440d0181c20701901e103a40058042042407655101030180c62280d091106100790000c2ca400313001c8210a60aa0000e00c0c1a0700d4500140185 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 267984505 1250 267983255 267983279
    0x19110a0c1407030b0a0504050c01090b161502070c030c1707091a04050c13090e0a08090612092a0d0206030a0e010c0f1403040302250503120d050709 65
    0x40d042000010300c0103000c01c66a14140300c980010f0181c280f5401005100d40103030700103d10072441042650303c84c0c03000e500190748080543c0510400384c001480b0207444003400036403000703030b0f14080c1d060340030080312000000c03089030f101c02d00907146250654170506c1804203040702c0c6030040091032002400e4a090000d826159419400b0301412aa214041e0b100c54003a00b6900c110b00300d400800400141c00c0250040c01e2680c011740c018410503015180009030108544120441c400650000c2c05c1c24541c01e685070403032039021409042e4840400d00014540801d03ca50046c40780100f94020000c04204082e00d9026104030315039411100840c2495441c0e58035042c21441c80c0c184d0503900e0540b6074646c104940e001d4100100f4003842c0c2e610740400d286916900850140203440640c8854a202000044007180781c0310494014015a1209010310755500015040510b51201c3c0142d0700a40ba450741c002a003000646e52111490b01004034182400502034441c0d10340100148c107001c1c0c2d2140c0361030418044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 267985611 1106 267984505 267984527
    0x207021806010909020f04120b010602120301050a03230d0305070909090519020105040e190e0f061603180c0e0106090b0d0218040519110a 61
    0x20205450003018010201a59001e4009043c222600069400729000f262981d0007040000b543e4084001c404014520454015000d5498020001d103020b4100910b407207440c4080004005a41c1c03001c0180b41101d0b4400c840440d601c00703070510180c6040019064800038000c41c0c1941141d0b40e41680301d28400c1c0c24a8840c040c50a03150a102411144003610040242d8000d8041c1403081002032441c2c04018814940300d441c0c140c8810503004110029203824942c0341021550350f983e102503025100310420110000c08a001c81020440d5032010041d20380200080b1214004d5080f9109401103a48610601d4000407552107515207070900003454480c160003110300000110302d040c480c075a0f00382282c0803107000d03d0030a155002c1900096004100810f600b030b10080c5d5854403512103000342c61090a81142c10444140c071014441c040ea003403070b03464414402003046003000040e002080500 = true := by decide +kernel

theorem cover : BRFrame.Cov 267805755 267985611 := by
  have h0 := BRFrame.cov_init 267805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 267805755 ≤ n) (h2 : n < 267985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
