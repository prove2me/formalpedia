-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2063
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:34:28.680305+00:00
-- url     : https://prove2.me/submissions/1c9feeac-288b-40ff-ae28-46baf9c9b2f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 370863309 ≤ n < 371043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 370864559 1250 370863309 370863343
    0x180e0f030406020d030902240d0501090b0f121e03130902090a140d0503131809030804030c080d0f0507080703150b0a05040816080f06060f06030406141611 68
    0x24502e13140a80150036258800c0b81c00010400d02c08180255882071007041c0d080c2d4a480503690303224540000292041a0003100001c0d18010380406070b42e0f04c485c4030f010880e5059514180b13050300000c000d42041d07000440c000c80c01ca00004c1f411f1801c1c0000c4018990803110f091054412a2a061000124000c0301c0000303801182c0e1480920030007451044030100307424018410b12500d441a030750182140c220070503418504205103014011820b0300a00a0719015030b00c0d40811454a0580740201110f030064005424000f103903254000303000d1b03000216100e590074000180440d86090070a0001400f084803000001044400800c076400c0c420302400280c0581246502c8486042082550f056440000c0404c1880000c000004070700d42d0500c4a000079000100b0041400c42c030744107082c0d00b800c074901d2030040240c20047c200b00f46070380e51403052100a00280c0c2c0c044d4580e9580d24180d40100741900691403243c4040040080010400a804040f8100d50b41d44004a000c0d01300510340d107084a43e0007540d24 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 370865809 1250 370864559 370864573
    0x8030103080c010b1816020610031b080d08060405060d02130506010507020d06051b040e160905040510140d0809090703061e05090714090f0604180e0f03040602 70
    0x410045009408161001000050764441c4c00000420100480c200040a0032a2004200c19085007241c060701c4818980090050f500d0081c01d4002c22041c607000090034401c00c09010210304034021210f80c05000200d088480c0340c84819405402d031902190240d12442c1032000040303050034503406035010241e0207088030b806441a04145809400014405030402801b800a100941d941048944059002c0c620005030390500d010080b0710403041d00c43d005030b0f40004020802c030a009058241e0381c4003051140c100070340014400c007250043c2c0b95500455010742403005202c01c02c84140c3d142400c680395410000c5410f03e0117030074840300307480d00d0704003601200043c4100c1c000c0b030500c503070850b50020b007500e0b0000d5080c5d1104c00d40342d00d8201914041d215000e00003422f100300e041104040c4c0d00032201c1d0a00461041c10039051400345e108101c1000d0040366040342100450b00c806064402500d5860400002410196418070003400050f00c0340d02c10380310b0300704215400d00002c0111002d98440354040c04507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 370867059 1250 370865809 370865813
    0xf01170d0f02030f07060207020a080105060a03060b1c030e0432040f020a080604051603020f0f030a0c06020309041b0203070813150503160f020c0d06020c0a0f0b010f0308030103 78
    0x104103038041d40c1c81c003540020029003c516016600810800344982c4005031905c409005011501d000d680280d44241e14007024080d2540e14a200e01c011290300c0100810f41d0701941c0c000c16107140c5000c001d0401d04a0404401c5e0030903806c00702c920003884081c0e404010303112030f402041d08025034440c040003859100782d59029104a040b0080c691150091555242c02c050b41c1d80880c91088103a84030401d10b810100600040010500680c0700510b604003000c030f01d15040d500051101d8040ba00a2845101055840006514244040350000740c011f80503100140d40d41101940313940c42060142e05c2146400107040b1060001030051814941e194020f505200c01940c480c00b43d503204400c08400c1c4001088001401c3e164214401d44132105a5181c9480c0e05004602e03c032030f80301d04181481400403401224001a60001d40707010958000c540710b6441000c1814410001e01c18800241224002d01e0728480c01c0c01144c100c0c800740948100c8424001c2d0b0303078038000c48a014140c0d000040c034a002c10001000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 370868309 1250 370867059 370867067
    0x30209011401020a080a020d0f03020c03040e0a0b03010903090501020c090c12040f0501050709050a050f010f030f090c42031508030a0e09010603060b1903140f0f01170d 74
    0x1d03603103040c01140c40c500040c0d15480c00c180c000c1c00c0210016030090700746180c0c00360311044402c0014020700f8194240010726904c2c5440b401280503501c16419040001640c010543c0c002090441000e0b000304003c181a040082c07549080b402094050301c5a003030000c0c501d0820000940c810705140f10300c14200004080388a80181c000381050316910564540325011550a210702402007000391141010b40d89031006020350a80158406c903c17030301c1c08102290040c1d80211602482c186a0704c0c1c005509081c140340480104103a2401038130000340960040789804852621300c0000240042c003c2c2c0c40c031419421800e21134454002d42c100100c07a4410f0a402c6402904036604114120702072a0440f921061200e01d15000382090f003000030074210044105c1d00702420301a002d4042031406120440c10410440f840b44546158400c02e5000c0d0155011544d100e41d011901c0c400d609840110181042c40341144804030540301e8040d02d0980c00c1c00014084211017403101c1240100c40909501c01d21004191 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 370869559 1250 370868309 370868339
    0xa120b040b091f0b130b03030a0c1704081e030301050a170106090e0d030606020c01090b07060204090e0307060e0a03090b03100b030108030a0305010f030b220b150f0a03020901 77
    0x794400e01e4025860380f880300824444100301c0820000c4d18001003410001c25580c07100e65841824946402c1e2a0036441c08011a50410040c0c01c1480912030240740080c3c555410950ac0d034030401c0b010501182907038022404034203003440d00f102c40d40748888a07141c19071280300070b2081c0d50380700d50100c1703040040b10004158942621200b000001d003859039041c02c90281da0206699001030b4000044110496405205950140100c3d1008108086080001030a082410300a041824801090107070400040b074040768003500030b441090180ea5a1011050b03540e8001c40402c81e141c508164602e03040343c600041d407215141d010350b140010b10f0303d011480c0c8169840030b02040900001c694020074200c15413001503001f0700300000190340d10682c41d10024110384042e00700342c0b05086600b50420201f512000320a401c0b40e0b0215080912055040c010858141c1900c0c0052981340c4600c03c0109000e05c0300200c1c00110700c103841c65100315100e00708200380d1403c1804000d5005c204840180f00040390089c041e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 370870809 1250 370869559 370869571
    0xb0d11031303080c12070305010e09061017010207020d030c0b0f0403051204030e03010905030c10050c040506090a03050d1d1804141e16052403101e050a120b040b 71
    0x41c90b00e80d10305d5000c0784204c803c07078441000c00c0d2a40d004010710501c52414030303440742d81c0201404c030a060403c0c052204541d00c1c42500300d80d034094401035100c0c01d0b080d411203003c15401450b2850030009454083d003900080c0d0401d9a258500800062240c0b40b41c2c2c10302c1c3c1c40340d503041da101c84c07034100c0a0310290120400500140e0422040140b034042d6a24244102508140120029508e480385240f0003480d1880742408007140b1030802d801d0045500300c031004e070b0342902d00485100c3d071219840b03008031325103003c03d6101402c035115411100711031a030896201c101c1441407402860886203a41e052003c3c0c0c00030348021a0240300ca2f41c0008000c503050f5403000388a22500d070301341e60300c03013800b0300c60054083c102240070304094008040901d18580e64a0740900201000d0300d2a0301c0c44c10421944000c0d60340000304002d4002c000200140c01c0034402994900070f0042d070380901c010180e003001d4480e031700b00c4a401003601540150b100828080c407400042c0194507800b50381c42080d0381e0b50396602a01d4103806002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 370872059 1250 370870809 370870831
    0x71a090f210903010906061707030b0103110303070506010906060f0905010203030a1a1018090e10111c14070e210114070c03080609040b07050309070b040b0d1103130308 74
    0x8040481e83c081c0112007070b9900528000c0394460400304c8042407042e01290380e07a0958001c03101003002804204203141100e8014080038503440000001c00d08500c60840000c08a000e12000840c0340c3d11540e0118003038940b240d40d54602000080410b448008a5010700e0b4056402440001c20280b03054208210844021030031014220490010403486101e8001c0200465507585034001500c014170801001080b03548000c0c00607050120f441510345202d036190300b071000d88945203194440c161104455840380d441d2a140c030313036888615102000304116034040b0074081840c0041201148105424a03a0140007031050007500c43d400501852a10880c400546d103549440c078444984440746012032040d541e40d2200711085d07a0514009000c4c0d038009064a102c2c40f0024144408100301100c442d52010382e40c20240e40c0c0c0d4641078000c030710701030311540700894001d000500840c1c072540a4003c0c3c40c004011140621070034200800744085800105c81012451462a000c4c2010034444c40d900380d006140451 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 370873309 1250 370872059 370872067
    0xc0b13090539040611160e0105040c08070e19081e06070c120e030a05120a140c10020f0d14040c0902030411010809030f071a090f21 58
    0x9200015118201c800003a2840c030310b040319842e245401d00103000304401e01c0c003400700807442c11084200390069010300420010b805400c040e10784d4007041001904200d041d0901d2180382d50b994820010300c000d000b036034092424014203034000c0d8010043c90f03020b01041e44856108984010601c03250103444a200c0841c0c4441c41000a003104060000040c001540d1640c44c40200c183c04100f0300d4044040d20040400014050b1000810b22000601c4103c0c0311926041201400d0b02000a1034180c1164001e44940120989104150710000042440e404251a0592036410a152540035406141c40400381034008500c00c91404030564002d10380030250700c04079030a118207407058004403610701d40d0400071103c0c401c00380001d00c02da0681400060054010079031840c500341c0c1d0780880701c0e0210131a00381070103038010204910960500135180d58074080403c8c55103645050400401c19a2200302485150500e1804200c014001060100b5000b42640040c9800710a52241c000c00c001c03103c440030b03078220082c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 370874559 1250 370873309 370873319
    0x21b0f010203041d040302010e0a0c030813091d2a130e03070309030308150f04110d020a050d0b0306130b13020a03030201020d1d1209030a0f0b07080c070c0b13 70
    0x8421000540c0e1a151644c0c03451400d0b10f006801c691680b15078a21651041c540b002c0003c000240031b00c02c0d254440c00300c40c1c40d400b491a0601002c5810703000b00803018101070420000c9655002c60408050045d41111061494000c130b014040d064510800040b0300382c1031100a4900344000e1500740c0d104c0309140001c660320091851821038125a408400040408404206065109035580e4001c00303070706001e0603030940080000e0048400c0c00e0105002e90340b01c60303564031148220811f459080580ca1020755840e050362000230125405100180b28903440c00745e5028460400050580c40786414222a100200c1161107140312610014440301b03203040034510080060300e80800c1c0d90000e52107500096119018034000c40c0c01e0710580d441806040202441c400c0c1402400901b0383d219130206a1256a00c0400102007400d0003210078000d0903101007050380d9000c0008040742c4612594046d901c03000c01c4d84803030030f4000d41c030302c6118000361107600c00310018411707406040000e21480510200c50b0000316a00c13 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 370875809 1250 370874559 370874579
    0x2090a3f050d091d2502071806031a0108030913060521060702010e100f0603020d050307022d0915030106080f0d02030405030a060209060c16030210021b0f01020304 72
    0x81e040d040b0006000c44000c0041205680344111040c0341a61483e2040c54038000301c124898022000030580160907001c0030303005000b0b02054010308180d262540e5000310705002400501005d00c822207506c0b0704019115098106a0721a5069076036801c040c0d46054100010002c1d039061740581801c100d5517441c0c000680e0f07600d84071565900c000d501d00a1160030b82440403541060710007055881964101444131500d060003050160000c0c405000001e11000c510303080b20700030852600001d404c0940007074007005100c000805010201c0c400c80e080f042c0c0c42d000300e1621100385801811104401d05890b8048220318001940603030000070344a8299990f21084002404e42c1c0745984000003030f4000360240c2180c80000d12110300d03014614001540740038175001c0481d07a500b44604000e8a007560100303028400359100d000704c4021a4100c000c641034201d80003a48110101c05103c124441d0584c0c050070790005002103609500c618541d2650805e080d80c040612004e0311504400c0360440c0010071012405140d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 370877059 1250 370875809 370875823
    0xe030f03070f1a0f15041e0507140c0109020907090e010506030712020304060b041a03061b1612120b0d0b15030a030c0c0503031c020702040906020c0102090a3f05 71
    0x4c400911a080400c08031104008101e4194050360901600d18030344c8445940c104400c91540500141c655103c1808803006080304a00000350000090094a01041508030b082018021039030300045032a2114140c3d13113031481e88a10001d080b024001000701e45040c4d000380d80d01c118075003840510320004000040481c0d1003202d00f156590340d100500c0d1103904251240c910b00d0016100741448400c144c000183e85d8510003030140408880c041c2500e501c000704801070b5100d140c002c0c032201c0745c41e24191030640340716811803201c04001682400300c008403c1190107465401e0790b000c1c154550703594030341c5c4076030a01040041a43e400c0d00103c1101d4080c544041199441e102d00950f991001c1d601039240804112801c0c0c0d201500c83d03401800512a185030400308041c00c060020b800690700c202d14808240030708074100020303222510102d03090003420011740040c6404030040740e00710700c200d0720360000900380400c54031805503010203a182441c040e03041107404400c1283c04414040c0b021810f603070311403400c0c2c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 370878309 1250 370877059 370877071
    0x4060b1912170c0c0910080d050a180308040504020a30060b090a050919060e010e1e010603020d020903010c23030108120a110f07060e030f03070f1a 65
    0x46480d034060601202e0180c01810090319500c862078031414041d441d584c0c03681000ea161013400f1a0000c500b040003d07000340e40040142d50169011411802000f42c081c3d0403014522001c41c04400703503078030110012032010381680da01c502c0f01e600301070400b010300001703402510144090212103482c1d20b20142400c0300c0000c01c0070300a80c0f040014807204a01c64283d6059034001041040140581d80c040c1e61044004000e0754000d0f1075804840d0307904483c448280f0f0343d1100c102c010070310784179001c18912007201c00c45060b2100e0080f106019160002501e0748013400603094038000c0c2101006210051194000f48000c42821001504001d90070000a0841e50502c05001c0030a041c05646004c10203141d41320a450640030303586a045600d0940c125850f40c0380d941d265035020200103410152580030f00d4000101d4100c002c225100000516401ca5a070341d21800364101091100e60500d40c0e6260004a40c091010114081d41c20006140d803090114045000100ca60500400c26011004000042030344150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 370879559 1250 370878309 370878329
    0x20c0601030c050f01020303220c091a040c0804030206041101230904110c0a02010516050313031106070503040509090a080307080708060423090c120f0706020c010804060b19 76
    0x10300c1e11040000c04400c00213458150742041c1b08014881d2441440035449651a1007412060380303542c5407002d6049a1a00301d10502d5203407000c00c6101d1800352580d03c005031702c155010054844103031000e42d04440200c50041c010381c081800074001600000d0f5000d20014107040031418003520003001d600340c829581d8200103028002c90508540d14040c0610f5214101e2000154034000c100c0c100142c541c0400e07007002e8140b000005031503d2401d8451103229440d9000000d598403240d802c01d42005581662100780e5510405020f501030034501007007202c1540e640080210302e82482c2005021280400030701a44d100d0007407850103070210340048001d43c8208025a10644585400c10024007a1f07440039000324000da207000c0c0340600c0705404118800c030030111403005c00d081d50b8070b03409140e00d00703030f44103801039000345202c0801c10517810000303200040b1251603801c0e5500140c5800c000c0341e5541ca003801550014120101040100da0705501c90044140042c6c003840e010440003401c200310a03c19401006a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 370880809 1250 370879559 370879583
    0x1806030504060c0309020a0303050702150f120105060901050d0e0a0c060203220501052b020d02040e220201080a0e060c1b06010f051e030a03030b1905090c030a020c060103 75
    0x6450701c01d9200d003054a060030170182c00c3c01d401040c8080c2d074901005003407160010b240e805558a20004030062043d42c0100340c0d030358984c0600e03014241c10114440c2d49402d007282c008541860400c0c141ca640550682d07506041c0003410801c07001614041200381400e024485031040400c0b181050318001e0141038004650f6000114090398082408180c0b1401e891481581030180382e900104603000d8014000c0701c0000d0b080c00340d60b803201e14484001c030514581e100080c003008090041c3c015004903114224105140e03503814210303a01a4040d8103200708680f842e00e041e03100541c0200701c981d42002040c900080c0c0c0a5080b65000d14204081e40e407148001808a491b40c444106440110b4400140c1009041c05515101040300c000c00c150050301d00c900080c400961104c0c0702d202481000c0c2030300130111040300c41b2a08002c2e0050240690f200c0c050078400d4a405490304000e42000c085500c003a040803200d40e201a81074040f07420251080002c9074081265288501c010040c00c0c0c041c600640c0f50811b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 370882059 1250 370880809 370880813
    0x6051f0e0d0c051f0914011b1209060c050a0f0f050304060816180e09010b0402040902070308010506040305060103031d091e090c010c12050c19050613080d0c1806030504 74
    0x90508200880e070020801800240f000d40e4007803017240031101e15107030f4507001414201c0140d031400001849401c6510b1114202418492603e5102000003019122001403070b40344d0008460913041031102401c030394850000c490000308154103406499000700d5403284416003036511f5a081d580250700840001c4c5541c402d10154544401414440050f03504159000305045240c2c441140c01500c541403031700355610006510303100203402010303004000420466850f0344903081840250002c420079800504410000302d51403c045049a082e82e41250050045078a541d40850701300b00400b6001d02130001c0d41e1016001c0d52107020000f806019240d00e04070501c034065801000c0f29000030032100181c0d1204041340040d0f41c2001c170361090030782c00040384070703002c8421003040e078040c07103044d0b410744c0f40b80700d00c55411008001122401071918800c80c01e0b1146511108888451145015005403210070304025201c022103065010246a003824100f511012200040c06c0d400044a540b01c000132a880b1020842 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 370883309 1250 370882059 370882069
    0xc0e0114041407170718170d0906050f0310030606081506030c0d020f1516060e16090b040b1003141f0e0712050a090203010e0106051f0e0d0c05 63
    0x4001c10280c2805400b0324180000625110300704000085613408080480c508602c04c0010901c901540d0001801e2503940d041e10020300f0003410707925801c80c000c90918a1182307109405500487d4441d66a150611901034114511548060050204011000c00000004120303010704801000d400024108014034544000141480188820f06c00e400aa00d83c0c0c0f502c5d541d0502400d00281c050795200741c03600b042d601280d800303810400703200c84d54400404c038001000d140000500e8540d2280c0b20a10012440011281e40e03580c00c4001300c0c101c040d0300700c81408109081e6100454a0b000100046640c16031500881c100da03205040620001f44c98840d21480d12034007440e01604140fa80c02000804520269401700c000680d0060907003507003510000c103203428400c040c11078001003038010030007560400046900c001d00b80c8071001c0340030b54200703503031064000380600c24502120340c06881c040b0070120841d0000700e11040c05041000f844242c1080314001d844400d4540783c01031160144c0c0c5081410241009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 370884559 1250 370883309 370883321
    0x307030b09061b0d02090f1804120f0518041416110703170c030c061501090905060a0501030b1206010b0301030b06060c1002030a1b1211090a0b070c0e011404 69
    0x140443d604182001d4903d4801080b111140c864140040c3c6410500d400240743d50341c980811a8008000341c501c02825246010035401036105881000c80c1d0907a06106036a01c122045200000c2403050040d21007200d00c5031890342d0030b6080100b0000701c00518a200b00f0700003900790b6080c400342e0b03964003400c4500d036040703941409036001e00c000400615186640704400710380352440c08040b640d40841d411349651010400c0d41c000600b40c40556800d0700d4001250968850818070710760000381501c4000405060a200f9180900401f070301c103441c502c0c18000150040d1010302091b5402004a030024119140d003030000718042d1a06ca4401c56032545135007801d05206002501c036074491442041018200000001d1803582a4604200561259541e0703140d10000c1c102c100e4000e07840f090320218001101d07030004003500008003014080102c1101400441118015a130300c0c01d4100390003800511082c0c0000d405071031154800c40411175141c4e110444010480020303405094524682c401d003010a20b4240645 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 370885809 1250 370884559 370884571
    0x10e04021230130909140f0309010e0612070c171c0e01110304110d02091602011a01020c01030e0102040504060b0a03051509040809010c0212070305070b03060105030115030b0307030b0906 82
    0x7041c200000500d4070366460f100b5204181d1440c3d5603071804000c10032040e90328210191410290303241c0c01e400080842d01d17944800303d2140081c1000c2194605440e00b84162040860440710310742c101d6a0f4a04256070380f2880b04d40c203840c10750200000d50700c00840d8400801c003c070000386111204251420740c00c4160744010b440380c029a41000031014483c40040181d0398401c1c2c110122510303a2003520082000707a6000c82c0e010390081700180800440b566031788446003030110282d00800541c2a40212154072940140800d801030700070341c2500030f196110b40c009500a40b00c903400107103401e0351140010106e510342e40c800601d444010038429406a05031040940c44103400349030711542c50503603000031111240140000c1c01c3c02c50115081030503900c41c900e000300141e805414040700e040c58140d2103590b0260f9110840f002c3c8101c3c1030110307400c225002602d00864040c1c480301d007564280054071311468040e1442808041d6200006121079a04014800080d0301640300b03210241041864603003010001400e17 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 370887059 1250 370885809 370885903
    0x901080f0d0f03180f020f15040504110c16030203150105060f0c0a0b0106081b040e0a020a140304060603030f030509070303050a02010609022808040803010e040212 72
    0x4005020140072031140c0c4480700628091100c40480302003078000300444d0440710700404021035484100841081d44d180814000c031140d180e059100d0f810040540000c3c450007005143c207110800080c10709401135802c612107071343c5203800c2507112906940b4142c4e02d907120b480150b04a00042003541800e00101c9640744020094030003543c10040401e290340300d60b00003600281400103076500102414001c40100590009000b5241d50703465070000c21904007543d002406a2584203e0315600560204503800c403441d080c501e8807155604070740400250040d5800a080c0000c5102250074103040c040298030841c81030000203030050445c03c00902c11035900e000c55061518180621102c0900002d0702004ca035414a0406d40da021981d1080307024125239480b2170000350000c140144850b0b00000414042c50151004111088a242040766981001e44010305040410801448401546080355600a0002d800005800400050140742a440c0103d101c10405c529181c1c144010b40240b50802c0c000711202 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 370888309 1250 370887059 370887073
    0x1a06090709060e0a0b0c28030e09040507083301030803040b0919030e040509210d110a1d0307150809011b0504030b0121032615090108 59
    0x80508090002c1c06000180861240c0641030307580d9007036955020700100c04046031580d413002c00c103e0b03450b540c10844001000f0b16222a540c81c80580402d00301c141d1309a5035207400c42110509200001c138018009941501800034040b80c00f52041207001071411482030042e04141090501c0c000700a10071803141000700c00c620040021402840c00d40c0c0e045500205801c885807244809649000300026012203c991004410014980c100d45000d8121000343c605021940e1003030740d0315442d001000540031885140c2c443c907018050000029200f0106e0a41001841240b81007440d84a5085925a540010350514503224520100702071110000360a030010701e00a800c020100c250485114a1842002001d4002405c030400c00d4004005034a4003151172010302e00d031194000c10541c400d008c10340d8000d107000000140300c0305103440307800c403603c10000500c0c9201d59030f40e0444045500404c1c1c49411107031a40021410908009410b005441e00104842c20704498000c2c0a490304050f400010a038012070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 370889559 1250 370888309 370888321
    0x6050307120201030b0f0405070903060e030906030c16080d0b03011508030a0c06110c0601061e02120702041e0605101812030512040506060108180715110a1a0609 71
    0x720026a11030780c24200450304c8030010b008521048000b902450344a0f05100501c050b0b41c0d0040d40c910152801404103011984003081c40035074901c9900b50302d50304010100002030742c00c60000003074920b0300e8401c09000280d02280d19400516040302c6512018541c0e43d50340c100340d61a007485444807401003840c1c040720b0949031001c465141d0040d40580303014440d01140c8a0208034050340f102116908141c143c40c1c035000b00e03070512543e4010074003a0b070004c00c0311304843c405030404c0c00380413001d04400c65006200124201143d0011500700080132a01300c1d40b1505103203100d01d51911003542e001c158680020f0080e10f000c04200a400500f80200284980c10030384140c4400503800c800d040d41c04a4000b500140700380c2c60101c4040c81071800c1a40051040402d0004019022603814000d98003641c0b004c4554541352070740d804010302c00a282d6400d62040500b0801d0301880904c0308100c1c041810444039180c003071080b20382405001c0c10f00300e0b15024180381754034050205170001a04108182c07440d145030300d800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 370890809 1250 370889559 370889579
    0x61d090c060f04080106032901030b042907030e06130b01031211030c0604020a0e0601080a1509020f03040510090f1106160b061807120b0d1406010906050307 69
    0x4884541c029140056080d041240308001c68009207a40c030000c000c019906e00b0130038100d03107058640707a8085d41c107642c0d0a0800d5950b40788050680741c22101120700c40e25140cbd100628155000c1c20003140da090003181441c0e4001c0001c6852045816032400b007815181c0d8402c160500500602d013200309800307405c110020902800785141901e81c0803524803100480802c041c2d441c16800c4c0102e06140c4000110028a070b5004a20203006a2094402c691083d40715015181305201c1160f0150008089500050760307420250031442140e0050b424036841039440e001c4030400c0c1c1e0b00580710740c83c00400c00024401001803c202c82119040e40038000c00030f1502c80c0e9034071503450f41100005064075001c00840403480c0d41d05800c40c0c0010f803070204010f8400c00c1c03030b10789417078602c0040344c004d481154140b02045030700c0e40c3c00c54000c4c03007a001e50b81c030002645911083c14006001144141d80c002c0851110880020800702c25981c0c030000710001071880790302d884550800d442d80d5402950203500201c60401c154050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 370892059 1250 370890809 370890823
    0x20c0409050c0108012102040e0a0b19050a06140108041704090617010203010312050708160b0603060601030b0a06031104030b180d030603120e011215140a0f1a0d020a03061d09 77
    0x104640100e05100b0020310a2b182c080340c498040e00b212880070134400da49180342c001c80b000100c3c40400f032081e961040c1d0354404607a080c0c402c440920200c40300002035980b082c0ba181c3e0b480b071310a400c04554411784011150701e607017150f00310128055880f24240080a00c018201588241000c0250314541c110317a07610040c0701d8041c1d00c000c1401000309030b5404004942040d01c10b002c01507102c1000588250504800b84141640c5c000e010780580000310f000c6502ca03028900d41008090716460055240c140114003c1281d586003024071001484088002422128840e0094651800e1922042c415440c0036090242101d440001d05140ca0b40404c009080b040f40e49026204608081079010b801000685d4280203092004149629004000e2518091143c482094910a20900858802070824000702c1000c0d80500c44a000e03400c80200f2180d070000002c003a10748041200e07241000840d01d02c0200740c0c1c02c40310705940480d803038a4040c005400e01c0140d041c41d10f04005000c4407582400c510302c60311441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 370893309 1250 370892059 370892063
    0x8090123041a0c0105090a030801082a01050c031305040c0206101e12030c12030e030318030c060406090314390706030518010203040201050f0a020c0409050c01080121 73
    0x149282c0c1c00d104490345094541490b40c0320028080e500e800f844554503012480f4049010407207000010518903c00101c1d131750207080c405180c44012850142006824240e40401810040c00b089000391459092000d0002c0400c071100405400e420142044103491344040c02c1c400710b42c801d0080142c000200010704080750040b8040621650700310640130480403130fa4100780c03d01c848100c0114100342e4407003041c0b41107038000d61a00701a50460030b030807415039030a24002c0000740d106001040c00d400820352030f6a0b40032860400c4034500b041c484421420001c04440581c1c425a0303d6064005064114601c498513070104c004c1240b030089a000365100307241c6405c11172051400250a560483d907481494100348100410403100160f95440001700600012124001c0907032103043c80c2c502c006c0050007600c1c0520b90513101d643c180541c0000c510000d03080980c0748401c510460500031090b454602c184c071800350051010340001c4041c00005440e00006901c82c10a5401d01c000440d50090140e0300704100907 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 370894559 1250 370893309 370893329
    0xc02010f05030a110318060f06010f030203060a0e01030c15080708040f020d170a0e061201210b15040b030c0306060d0303060f081e03033705040809012304 68
    0x512a064203074001e107401c2100300410308002090140480c0031b44080400d14030324104996040d0390704d40c4841c0301f4620940b191404594080800319049000c0d8002c1c661120000e0b22443c04141c6c0c0340e5401c110302c0401e900c203039071050f0b0410061101000c10800a111400c02d41006122420301c0c0714001c00d400c1000380090041c21184010004554034822000358a90f0002854803031040e0442020105500140620300440d60030314859041d424058240c9415030884080003129a10300411501e01c0d060f03980e18060f94688003c07913940080d8100d2885805040090b200d031288500c1c0c0002d00c800c94a207401d84500c29449140c00b1030703241e6000640d240e4421410749104d0302200c02458107901501c2603410901000310610307000b25010a00044644003104004d4405080580200034103442e4441595401c1e210002c8a80414003002d09110301007001c10079200d03c00381210541e0121007151022f803401c64001e400010510104c1d0b07800456910b003101c0060031218600d881c0508054148110b1003060109 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 370895809 1250 370894559 370894561
    0xe06090d050c030d0302041409010e01030803090a080d0b0f1c140f01021605070e0903030604020a0c02090a090308060402040f030f0812190507051602120106080115080d0c02010f0503 80
    0x441803181220300b0001070101c2e00300010742803014020b1f420034061020b00c82240c0030044140d142050b034643c12260b036940c02c410240d086403035403c1c9560000300010000e2003018030290002d851a00101100341c81100001420a40381c1d04200c200c200a030801351082000400b102c0414094003c400801307a4040c200140c0c0c01403d4604e941012440c50207001194808241c16040702807048030300c14058801c1c000c1d11440382d00c5101d907036a614000e82d001080342d4001e1000803498205030703000f480c00d4211070030205106010350703001030b500741c0049440b5000d142c0c80d06100420550840409a082374003144d09504203401d00030021001007a07880080c004000303c00480050250782802c03255041c400618119040c03500c02070781030075000051107004a0034903042c0041e1103540b181e03050301c8131140e11401d0000207280d503808001440c003020b10300080329581c4070300000740030b0003d11a4050243d015140b880c0010324040040b0300b012202040d180c00d02c2205827032840144c0e406030024038a8240d505025880b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 370897059 1250 370895809 370895813
    0xc13050a0e010918120c06060513090c0b0c0307110612091501060e010c15021b03040e070309120f0915110c04050609010b071b0e04120c020f310204050a060e06090d 72
    0x1e0301d1294452500700d03000c44e0ad800c00c4254590020705980d401a0318a0340003580d00d80350365445128151032440030b9042400140c0004464510350903030204000d0145041c0f4208450684a40b58140c0d08098241d00505c01c0168401c03003a02c0c080c0c0105614101441c8045060001800e003060003c0d004000f90045088a000c411156056030310008050b036120301081504003a150b41d030f40c041d0055402c010b44600019454034441d000300400340c2e5005d0000c943c103204110090b81c1041d0090451000d108160101190004402109088420359a62803100410741070705250700301288110840d0045081c2000c1002039125070350640d0449904170301c91940c59125003001d101c19007640824501030f402d85140000e0388001c10030003e00070f40c000c8109410f490410001692103a910040c000e4005105805020031483d000030384085040c0310700e40311400051112a5503030480c005503036030402d03590301040c14030107402e003c02c040000d01440c1c00d16050209515000036154050b80014521415a40c084501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 370898309 1250 370897059 370897061
    0xf020f033106031e0513080903010e06040308060f1f0503130f2301140c0c01090203120d06060203031306110f070b01080d02150c13050a0e010918120c06 67
    0x1040d8000441c201c0659a107800004020f86149207084103800c1100004640907000c0c0d00c5000d01502401d40707200308454559403080da060300515120b60b41956904011010140c06003c110f101d03030f00c00c0d80d440880e0b10b4101c0030400301107101e07042c090040e1a42d1a00c0c0310302004c1e2241c28540e03000c042c280642ca90740e40c82003201c500707180c15400900030482d60510000b04401c4ad540f0040b0420486001c20301c145904110754222820344c072121130100c04031000300340078802c03060050954200f00700010441281940101c1c3c41c0c80c10002c80101c1c41e9000140b41410901a84502e101603c29440550b1460410301616440c83ca6203190280090307544540000d824824a011544d540c4507200c1d2558580009042c01c070001c034070903c80c1060700e01802d04520b41007032020607188a44100841e0040442c0c40d9032000c8d21168020350012129841200c9000c01c1e036945102c40040141b808814960107903041c0210b01c4150381508409104521506050f00005140a5070111040c07001e4640b0700354000707060500744 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 370899559 1250 370898309 370898377
    0xb1e03060a3801020601090207020d02101e05030a0b0a153c021c090b0f040906030b04120305010b07121e111209090c130504110a0f020f03 61
    0xc03031070300c06a00e448407804081c407000e500b02c00826003c0d40c009aa0314600b135000e81c86200e00007503016400910303000040c13420b42c18058008039145080e450188951124490744001c880348140441c201208014203d1200c2c010b070005540300703580302000d052600c03214500072504d04500800784021030000c4d0f422540d422644400030383c01a040500040744c81e16550000a205400c0e000043c05805141c603682d403c5611064051903d81d0341d0340254620346642e0103940d0308001c400b100c404a08200c000b5042e01c2c1030054002844c0540c49041c80b80c02c03c0d1404c82c4c802030031006848103140c180740040041040102c1901c1070190050301c0d11128110058048070780c410307100c41400d261035a4855104950381e0107145d541401c04028100da0000305140404d031650300460394115480380c1c1c1c220003d2503c0c6903010241a84141e00700c3c05503000e546035000101a00c0501a040d000d00b0b00c0441d0f001c0c8055440001c0183d036440d14005030001040c3c90749029128428051030743d115400302d41d820078407015503034440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 370900809 1250 370899559 370899611
    0x120105010503250903050f01051b090a03080c010203010e011202130b120d021e010209090615070f03051c0504110906120601080a0302010c080c04031101030b0d060b1e03060a 76
    0x22080000f60b0400a403a81c01a8041038445105400144840200c140302d1a03002c0c5401d82e09941001c00e0004a0781c0140e0304c00408150050b800d00310000000301d01d0400391801c01c0103080003589030340c18030002c5044860705a10502c20501404641005616451450440121104004a0900780d0311010420346042c0c1d1199903403510070341c41d00080550340480c01d0900356182d03011203440041004125420303400f48000c03444e4842d17540c1010842030701d84400c84c0955606492101c4e81026003544400503614094030050380820f200080010a124512015100003141a44104003e05060300d8055001c0c45c9405035500601071034003c1015540c0f05c0301a5510b2107081c0040750761355a100c009150f12110303800b00480240d070800c0d4082d00c0c5540202c5074036100382049030699080502c0d5460b0080040030b04410141419030f0341e40500e0300b90700c1c2c400180b5180b40c0202c1021900d00c40369800c0c040003d405001c103e50140346034560454a50b008a603ca400010102c0c0c007040f0018044e512250f80b144116003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 370902059 1250 370900809 370900861
    0xa0f0302180d050705030c0a08071e03080c03041e062106051e19030b040b0705040521100c200c090f0703110a140d0b03070906030611120105010503 65
    0x42d00e410000e000074004141c42c070035001d8036258403203582446002a05801050036a030443c00050240011300c94020308060444583c0d881442d0f03481e07d803003080e41d20040d12a6a1030b0000101484a114415148070b1110758060081201c11324150000300940d001c0d4511610400310004000d4400030160811400791200a09040d5801303208440004401b062562403170092a00003040f00088948003482d5045135007120403504517030b46c1c0365641440244002d0a600034043e060001168541301c03204518441c00394070009088006013107d80038642110008140d00d821f04104e850a00283d1000b01c0188021801c02100b04901c2d0755580c182c14009000103042d0007081040401010003e1100c100340100060b4504100c203403410703c0800558801c106054010410310040702c00500d24400003010710140281000541c1116030740080d04205c0c1c01d5001c020810741355030040c01845000e10138080c40351070110f2502d140846804c103803a4503603070510a09050010120000d80b240110410b011100c41c01404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 370903309 1250 370902059 370902079
    0x170d09150e0a080f2b0f0c030201150e07030f0510050f0105090d0b0f150d12030912030507030b030303060f0114070c030501050403080603030a080f07050702090a0b03120a0f030218 79
    0x344da030790b1041c03500484a00440f00600030068400d071031541c03200c07000300c0e542c4584046400580940c0c141c0f106500c12001c40d0344c0d400841c039001d00400701c0c072400743c6691902d10f185402c0913a030040680302070858450445140c03c0c184011a402da14105048600a542d00b10036521910300590f4140600821950000d13040d41c400b01c02c04c921420b48610a00c043c50b9600790303d4807644101040499544c07030490f00301450102c220045424070641e02c0d41d41c2007600d000301c0c1500266640d850034940d0014002d010a4460043c4046e00340c16014401008400358015030031450064001011500c0b07070b080a80c18402c00942d02c028418440c8115050181c00108844042d80c0e20725041d030080404407000c0d40022601400b0585520f400710840e0f10940040c1c3d0740c40c0c0c983d22200d0350540e40c01406404941408020403001c0016121a050544075000c60f03400066411040b00506051131414420803000c240100030642000303070000b001207480d40c2c0500e401a03e40e810b0f0461101d084c55207140103580201c042e0b0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 370904559 1250 370903309 370903333
    0x30b0c070803012d08031606020c0f0a020301060801090206030606220803040608070504030f1709030d1205010f050a0603050c1e07060b010e03280c170d09150e0a08 72
    0x31041c00707070381000c2070260742420442104d00340d00d80050340121142500304010b9101c400078054254514a40604001031605500507c100d00c0e040030419000d805801440c2c8440c1035103401e10580c03000b4040c150090225810301e50000d1710703900c8000c040c3c0d8803da001145007401d004900c940074185202d00d08203083c1c225100c0540660fa50040d21074000000d081b0030001d44500e201c0d80503142203a52241c041141c40105640c0c03040c50707040c00c18101e81c42440600620304c065404000052441000e0b4079044030030f1071401d810074140d85050704101102d940309081040191160a500c4045920a250028464642541c445c0d1244101d010000e48004400e1031101100b486070001c04030188540010051030810200544164040c056641c0e8941c000300d043e904800c0240c01d01e00c054179400882c41001c2e8046a03a070140e6003056822070010000784040503100f20700304028003400070b00e090030080140751502900b05200302606d00940104541c02c02e4070480354039106500300151202205603401c0c00a84 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 370905809 1250 370904559 370904579
    0x5160f06050106021c0e060405041806020d0b150c0606101b08030f1302010504060309150204090203011a07020a26120c0d1701050d140a060b130b0901030b0c07080301 73
    0x129208000581d18410b2070884240074908940c10001b01410060800385082d080000400c07803904428144504a807034080000c0c4640f000304458040904005060018402401036180702c14458401c0401c04104001c90480006081ca501000440301d03402c2224a07440200c0303280080303030513001c032901d68100460200b00c10403000c5e52080101c1403040c0d40c2540d45501d0310258044040c000390120314100302c140000d920a40010390017a004100e00d00000404041540c101e034070640c003503000c0d15800f00041c08403203043d0800c15036200301401100d040460036000a80d100049119204608114031540c0300040d0030200b01521980d400c1085d500c88064510102e000d503480521540202e0080c0411a180680a01c20300029504050000d08042c3e0902040c810000e621203020b944100d060310707141c0b00c0740a0400c05120b80a220fa00003194001481c020b02800b50052455182e52504110a000c0070f13864000d18641103982081031a04c0c16200c000958170b10384180b901c06002e006000002003600c000e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 370907059 1250 370905809 370905823
    0x50a0c120513080a020304080601030507080c062107030e0312060f030a0c030b0703020903030d020a0807091809110d0c050f060a0f0305060f0402070b042105160f0605010602 76
    0x2291214010408003850440444804658440340c00d401049120040340c9040c000c0d1815600301e0046070f28054556a08071b1409800b41d10440b4140d10446003400440014884588145019561541083c140700314805a04054810100b000c03025040040c503218401c0e000b10701003030220001d0303903502c000041704a00b440104845d0f00740500e10340400c103180b6003000240c224805821090441d8124210b583c0c036107407007002030010300416030280002a01c50b0390500081688034500c250040c0d85000c074020161006000420a10034003e99050801045251600042030544007990016008982d890b02c4401050904581600811503402c02c41c10024031b05505400e5690844812164013840303820003a0911440785250006030b20850300e203980a019402c010341140c4014110604c04124101003004c9030003040c0141d51256828007030100344414040b0103c0702107100e40080426444241c0060f1441c4a41d240104e07589900b4020780092103d403030303503125800da40b088083c002d950355a0f50007540d4a034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 370908309 1250 370907059 370907081
    0x6030809100206010b0d09060615020307050705030601030809040509101a013e0a0203060a050a1505010203030c0a14030c0c0d17010303080405030d0524010e0f0909030706050a 77
    0x41d500a901c80e160000480354102c48850309010300e008116802c040140c8401d0314116426526802d000c1201c01e64004c492031000c070280e0095403500600d050481c070b00221a0300c054041e8100e10014000300e0f00f020203da480c0441590085103a446101c4881c1c40c2042500c403403407003607150011070070502d54000710741909503000340d88542ca002c40d200c50300c102192080800c2c1140c074182c09070060a1015419123b5000140507040d07500e5094140c000c2410404215150035881d42d0703403800c0040f950360301d11406044e21541d1105e00d10740d40c01d00300041d50301d100c090230101055001142a2920310701c10351043c00381c003c1d40142c0715241d00307143c4a0540d040c1c00484071030016001d1f4140540070584580580110075404802c4030780941d10b1624180d60011025000b40d455000802c00050804090300404c0d0298641ca0b202c00c2102c042c68001d8503e440301c4034865810000d0034280c034140b80d558440360007440c02c01110448240d131541c1491626500c0381c03080040a05040c0340400c1502c0c04180d000a8401c2c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 370909559 1250 370908309 370908319
    0x40606090807080102120a0e03041d071d01080f06150409020409200d0c03020f03070f1e05090616020307031b0905010608041401020d060f1715240406030809 69
    0x241c1c0390b040b240c1c280d003c1c2c080104c21040403000010947d60003500300610103540070054074038081e1501c45002e91241c411b80749026000880d13003031090140c2d002400c001ca0404424bc4021580c4030140000c242c10005030041a9128055001c520261380301c40640790f19004014a9503034950741c0302d0603d40a50400d10423024041c0c0b409071013203000303180c10701c44070383d03170861104c8052406095044c40c0000b08040059001010f42c00d0200480101c03059000f18003e0140e6110a0114421342ca0010014581140ea50304000008a520609150840c00740c40380d048007211115100d546224014110404401c0c0103545881078500000a0003810003441c41501160403074941c000d80c5404451040e20801e00c281400500040005404103586002100102104600141c0340c6450500c524040e500c0642016a40c0086218100031600c1c081e0301c0d00e00c40444442c003030001c502d0181e81c450070b0820003c022483c0480300740e141c41050124000440d40ba40e40c0204200b042c01d480c0d0a000b001508003802140c051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 370910809 1250 370909559 370909573
    0x180c0e0708160f0302070c080a050105060105130611190308010f120305032202150d0b0406060903020d0c0801140a0b0d0203060129120f011401050301091a0406060908 73
    0x30512a1803081e2003a8141e8803442611444031000700d034443c034024000c4040550034400e8900088041c0c0044004010f004000e00c543d8070582091800c40d40041c05180c1880800c020b5214542000250082220020300b00b4900d804040315142d41003403100c210b02c172200070031010400300701500040201e05a485040c4141d80701a1220952002c9003a40030018010440500008107001000711018090811014102c240950b80383d0200762100a15010001c5100001c6422040c0d20f203d03100d00b4045050844d001e0006d94502003004c2c5c030510345400080e018640c440300c0c801c144001341c3e1800000700f000300002c0000340b400091260001078141c6400f01c085040180e504c1552030001011508603400802070a901e910306146001c0f14040312841c880780300c040040c5c41c5404207030040034142c1e54503142000585450222041c03102e855050300402c607440c981024241d51070b43e000c01600ccc1940c1100c0000680ad84d41100c602800090030400654028140302c408075119501c080701c0021100242e04031520 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 370912059 1250 370910809 370910821
    0x8130f060906140c0403080f0d0b04060602010218010c020d1e0b10061407030e060d0908070503070227040305090406031b0501180e13020f0a23060414090a180c0e 71
    0x45c461884041d010200a110b40007003480c1c14402000707804c03440040001c0c0d818100d0f021070262180b0ba07002c60702503540070619060204001420541503102460700856810066001400300f00005801611855101d1502c004001c1e102490150450300010740c5400c52a00c900401c10048c2a8028040010400724026036100e4858081c3da41460703160302c3c1c000d01e1008290600600f508405142107505448126800114840e900140045401030018564541c010b006019810304003500801c41079a42d200310359480180051420303041541842c241c1d654000900003d0301401c82504003034031440c0c81003002c00b040120b984040c0220349080e211500c4030401c01107404040d0245204651f5640603440020313040c0400340c1d0500f00319902c0100400055050840820301c1e040481e000103e40641f4042c08108011600b02c2200722800121141c40c501070600650399401070f203c0703005074041ca5895000c5104070300583c01c279074041009003102c10b0702c0c2c040a00b0584008a1a841038960001d068800700780 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 370913309 1250 370912059 370912081
    0xa0204050406050d080307210c020309090105030f070603090c0e090102030a0b060a02070b03130812092503151409032502060405090405070510031b0305040308130f06090614 76
    0x4c84c058000e0142c030f095945100095400d01d0070f0b2481e20f514103840100005000f0303410b200e02010240305500854507400d0b55000d000d0010f0040e00064801d520180501510301400200700081ea0441c2c50003040c2b8007140d103400650300c02103400900240c80d041041151245c0154003442c071a540d42d682c14011741702e0700004c0c890140300b420380420042e00034020520034000c008004680100e060481c110f01d406960700d4108081d0000002500c5058444040c855450b00800c40f1070308024404001c61318002080c50310111018151200038221800030490301d200300125803180014100902001000d4501840d0b0130f51254484e07496000d920517107003410039a1030b151a01900d9100c1c2d000e00154901f03820711082101d42c0c040100120b0f0513101c0d1041c00300b12510344498464184005403408210103a030882c00c2030007244054400000c0616010820003c654484800c9030084506d903491906d0500c503003000155290704000c0680614204002c4004100840e4000085d4990843c0441c689490f0161120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 370914559 1250 370913309 370913329
    0x312020f1204110901030c060c0212060f01080708120d1d070b040617100303050306030a050f0703030f0302030907090c0909020f0706060e04031d0406050d0c0807151d0402120a020405040605 83
    0x1802203107c8076002d100c2c82d4028090104c86900003040000b200f5030b030040d01882d0079411200041810505001008520020000f00c0050031040000d00b1704406849581c420901414044c401080c3c1c07290480420544c030612040c10342d401c0342c02030f2015a5151020f80d1000d903c5489004001042221031000500c042d807451401140e80c8104010804d141d92801c803403035080905103a5040c003450320b01d00c2c0081d000304a1742031002903800c054107810b45581000703844105800740b840240741c01041003014000000c03451009440c034a42c00041e02031800c22003103032040c070190440d50186100080001c116000300018003131003403142d00d003032102d282c40d441020f9001c8020748000b03001c1000b94480d81c000100519014000d000d0141000507143e564400052826078a54000d45202c1c3c076070103003840500d2060000305c028201c81e43d2034801c60210040d008161003200040c00821406460541c0300b03694640d01121414050303c2910506801c00c4c6048200941c4030f03200702c1e0f01c107900e00a030004072030074018596 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 370915809 1250 370914559 370914563
    0x38041b05040c09090902150403050706030c0306030203060612010e0714030c011b060b040b041b091401050a270617010602070e0c07050f060c0d060e10030312020f120411090103 77
    0xfa00c0f01072401a456024100f440b04c100c0c1d011031021091b20003d9031150240c00114045e900420600d0724004019007155410a0751508060900d841800561000074405801043c20b0b14000c0c40104403a0f0304c24018084100540d240703001c2c4100000e004440b07107c410004000031415141c021a0380030041d9250580540c03a05500c1503004004404100240c1c800e50855030082d001140700b070024400075003140c1e00c4414810845006001483c01a41d2142119000c0c145980ca081164001000040d2190090f0300001c010440c20a04211a60048003000c5060300781c404000509140c03a1480500540001130b01f48442c5282400001000c80c0f000540302c00701c3d5847d5800407503940360f0a207054061347c00b083c0180c64601c03400400b5158070b0820820765104215070341c4800e4543e8403a8200c03905946403540000f048403101014084d40c0c0107061802030862f0f0780741c2030050038480d00c42c5844000c6e016082a8a0340010701080500054040303c44440c4200d100d419040c900810600400c07402c1c2800b03000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 370917059 1250 370915809 370915817
    0x215070c0302060603151810020f03010603051f090207060213060908100614060a110709050a0c0212250b0a02180d0c0308090420040302090f0438041b05040c 69
    0x207d9040c3c2e1400b1000c151080c005400e40b840413101220b640c00f40d922440c01d507041c501e0300000410102d5030603c1403541001c1642e03403422120b0903070350411700c882c0410b014180505074001454810010240d048654605001c40c44060546d941c00000e480b00c025849181c00502410244040d0b4084070310501040d00c84000c004124201400240402d6411090f0351806000340ca0030038481d240c0c401c211141c010071418101013804e242401d644000c0d110044121740079540010700c22001250001c0545034804280c0100101600c0b00300d0102101060710f80e07000e0b00b480e42030300c00c0c400c040d090340d00104851140304181001260340001401007150300303000c014041c0c1000107020300c001441c41c0000c0003402d00081c800310340502c00020003043d481c1c207a003d2100c64000002d04208606001520592112009250143d0340c5040e840d00c4014023800307041c4540800c0301f00e1800340e284c034501c0741c801055840c0399480502c80c6000d107040b0220120141e09900e0f9407841c8000011a03213024018040b290300e2035030b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 370918309 1250 370917059 370917061
    0x3061107120507020d05030d061404020c03031807180506010e010905090615040b040f090f05131101200c2b1401110703080708010e1608070215070c030206060315 71
    0x1c1d08503100d401001040364410100030981e004504200050a540340d2000c000082c0c00740f50048017030b40002c00003903650142c0d0040c85118400b0f0300c08070540754007084100e481c00e01c0800c400c1e80c0c0350900c6400d4008604901c020042008100381c141e2000f07200d0310003a2205e5100b014040015900d040d0144941540f040c81000061100c0c01d02112a0440080c5c140400d8102a26071154205076003064000f41020006400d040000108900906901104943d41048141450701c408000307001c0074040a020040c1c4894015813a03403284007100869090f4062310120040303500002030311001d1803040e443c0b0410300c2200079140640303060300c1d56900461500510700354074415038928481660b10b4200c1c6000f9561b960141e40d20100364402804801d2103581d404030f1a287c10310780a04602c80680107140919000d0003003000c08104c010403d0389800c41810520240d070707650f26040b07280c8031074850340002c1c008078202813242007504941c480110307620076000d5921a03699041071580d20701342805041024800d41c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 370919559 1250 370918309 370918343
    0x304020d0302010603050d020a05060a0501050d03210204060917010b100e1c0503031803070f02060906160c05042a21020310150203090102060601030209040603050f010603061107 78
    0x250410803103403082c00041245540c94070380714106a103042c038010141e0040110301003001420f01000d580842110b000300015410580800d00300910100c000301841100c907020282c8200304a079054550b804490300303664458803001c008104c04454407960b11054116001c5000d00381040c010103281c40030180100c11809004031040751747c200311251840d013004111406a440d510701c3c15504820601500055640341091f02c1000160545005054410340040c4561800556489001c08030b090301200c1850319a0301e001c0000700d10388502c095003d900380d11800050200b104110361501151402c030b60070090003a8942c03c9000240d200040802101c202050b50300c050350140c40540c0040b81d007100c482e8142054180701d0402ca901c1541d0f52803446c2580c0710704000c040d95410300b03a20007624910180d42400c05060010f982e40c00094075507030505401040c9107040c0d841d5544150700079500301d8122500101c001c00400c0c000c0000b80016107121341400d04d00c0d004551600e04440c4451390240b4070b03648a07200c0e2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 370920809 1250 370919559 370919569
    0x1205070f021e030f010e06130b010608040809060304110a080c0609060a0504180207050d0c0b0a050c2104121814030a060603060e06070f170604020f03071709070308030402 75
    0x42c4080c110030302d80a011000d094808111620300384080c14000140d00c44024045458400b00a150384d41e0800c40082c44400580d203d00890704460380f904040445480e540b80c80c1c14513008141400f41c10400100410080c44905165011184000e8800314103040d2500c13012500c3d09274000300c09801010030056010340d400c0004c010000c0c41f280f40303001400d194861024001010b6240c10450070182c01042450a0240500c07102d40b00d04040d0a00b945160a20756940c4580b0701c0007001c0f6071403142d555000404042844040b25101e1421040c2c0c0b1007605032051040f420160b042d2801d903002c0c3c821010740800e26000b00c3e4151003001c1c0100304081d07498900500d0b001d06617580001c07250580614898200010014000c138005503114103c041400e00001c0b152074074104009200c0400c120204c0b07483c07200b0b640c02440742d03a00117680e04400d492a40c1c905c0302042c041c2c0310300b0070700180314900041003044450380b045e0003501da9400030080d03010319211180b02540c1d4103024040604002420000b0070014981 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 370922059 1250 370920809 370920829
    0x6060a120e01050f040b010506090f060c011104081006050409051c050d1103090c18011202030a02060301030305130f0501050d02280f030f0212040809030304091104031205070f02 78
    0x5520300110390288040081400e45505407024446100705405100411101c580c142d400340c14281c4843d4100104100011405070590402502460000400c404860b10a4102c203010301c9042114554455407000c5040d5508000d01e00c03130a002d8944640454a0f103000d0250b006501e4002c8000c00c20f035010484840b5940c0d60b29001c600a1040400c00c10551038818002c0c60721650400503a42e0b1a0b14041e14040d080000303c4480354855010800c1e2411545410007210741501c0d0081d0594001c4a81440800e241c8004180041d5000c0004070000040541c0710004040c0200814510342c1c10039900c20540c14406540c1c024240030910a020358440c20312140c0c0a80050f0b80b200c5215031040d080301d0040742c6c0c0c2c20305815040d00000c1800da0801d201c82d802d4040e440040140c0300c002c40c9424400070000e58500005080181160000201c40c42d8603507040058802400d601340040162040344207003a44964400d110031101070301a0800880210700540c29160400d0b00070300003008400107a4200944100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 370923309 1250 370922059 370922087
    0x32060103032607030606080906041a0a0603081c0b01090f061407120306050420040b1602090a05090c0405190903140f070c0807030201020304060503090a061812050306060a 75
    0x100081c2d54110741105200c160044605840008401d81000401009910024920a03055100b002840b0000f4403030369005d48082224100e004880e22641210000713400194030240048a010600107601d0340700d8207010b14082c00088041001440100040d5000c0110b4464100d03100302d0b0f071354100002805002c0d8500c0590729082c1c05450070f11070b41d49900c901007a810703030800000d584020a02c49070915100d29909082c0d02070b02e00e00d010300700030402d00c018451801a0072001601185e80100440200c0031400c200380d00400320b00440c81c10a07050001031100322950a01c0380b140ca06988510300303007881024014428510350540c0c0c3d4007040001d4018050210f02102005103010050f500042000d014200800340e101d002a9034150a090007440302c0560380201c0100e400c4000708000603130300081100c088030802d040503034580da20113600604240105002034a098140b1204684400a0a0f69522090321540e0a02403036050302508a485000441c0d50641150342001a0329400740140240d0714104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 370924559 1250 370923309 370923347
    0x10614130e010b090a0507120204050a05011202090a03050607030c0e0a050f03150c0a0908070b25050304060f0305130b072f061b0903060103060e0a020a033206010303 73
    0xc03c042000c103c4c6041c040ba421038102d5038850a202005d0340c44001c1c0c1042d070035003483c10750a1a040500040044001e4420b103414059001c0c1c4484c803034507403601a14200c860040505410943d2410916103450040b24041c0c00079180605001e46c0c1030148507841030004001e000014243d00b040d0501102821f00074281d42c0c0740c03049034911598800c00309030340c0344030b0000224030a0701c0340f403044000340008815411100190700800418050000801c0c00e0f1007917051441001402c81d141040d6542000d00700201c003a009000000c2c000c102d80e904034855800f0b540c1d80b541d04010300c1e91a1141c040600e0a0b0010041c0408002004501c00f02d100c0c04404003010b2400840c02c25209903080701004504122543c0c2c41d0b13541048081040d0308402c00a028021141424002d19104140300060f403a1001400000e220607591442020740c81d400300848032009501410711a1121744034108050490740c08400b030000780c1c00c1c807804001110403586540d80407038642002040c4a0f42940d8054810b040d01c20141c01c0f00d2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 370925809 1250 370924559 370924571
    0x1707060212090309120601080307120908010e0c090114030c24190807080108070e070e03060a1d03070b060d1b18050c0307080712060b0417010614130e01 67
    0x8091a020424001d81c00b0300001c56881d14090305225044900385159101038002c0c0004005045000c03044031141c50b4040798142c0190f590b644203866040c02600007005562801d5010140c1c5500060440c4101008586415550380d845211003d000007072184981c142c1c2000b1303000e40040c10201090400112100c03044e19009402e0213410860f0707013040c4d1146440920a0720754a14040d0010151034001d080c0d49071032203842d810b00300042d0361020300b4854603080e1041500041d580c64420500c50845820050949010b4201203440002070803041070000051204000c41c0da0300604000111941c0701d03030050341c3d42441d6880904004c685044a9400d94103010601c1c41030100403c010001409402d45100351940c20315081e4001044400082a4141c00d107810400e000344280c01001c003036800b440a02d41001400c0800c034035a0040e1070664840381e0071400100b00820303a0050081800800d140000080002035034401901041c1c1d00780d801c0e0540c026900003200c0303000c0d0101e83c0010640580e218004039607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 370927059 1250 370925809 370925827
    0xc041a0d06021e0714010908180a030609232116081c050a0b09010302090a060b0a020f12030103030e010c0c0b0f091315120c0b030c0a021203010317070602 68
    0x41204009154043d48000031213804210140c0014001c070f1a101000f082000080e544200d01031150084a0500c2c05000080059540e80c6294040265034032020900c02e0484900e401d407002d020703100c91098100380030400042c1880c03001a440c0c000c4452290604c4950562224141c01580324000707160b816800329080901041a01004282101845041062180d540f00c0140111400a03040758020ba003010a0070f80c1c5070b9a02c800c0613054a8048501d2402502c90811100043c04264000e00b442d410104a030300320540c01080c003403c0c0505400607144e0002e442d200c00030a0b80b000340401008a0184018002d8a5100719030000340b080c4640c045a0307603651100900c2c4502d401100402428103030003d035480d03240c2401c03460061064900c0c2e00520200c5849440c23aa0185254020b8003070140c401c44400301885402c40c121001030190f503001c1c9542c4e080c41c000c0a116079000080e01c0000d0320902d14540c980c00480d004880c100c0e50444452240300722410302c0c0c4e00040e80710b100241e9442e40c0034014221 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 370928309 1250 370927059 370927087
    0x60a030b040213060f0909110f0c010207120315090905070b091503010801150e060108011a1e09240a120209181005030102122d0a0204080c041a0d0602 66
    0x280120b40c5403110301600000c0002c1c01c0b03403071b19000003036550305225000031915928400c0c3c491008041c032805444400c1129094024014600c014080c1d0140420b190304064042e4404041080ca80d00d011440c50b0b205c0c0a03000c2600e6090300c0043c80395110030300800c07458045130003038095010006c1c8007482c0c101084141d01d0382600280c1040b00306955034210044200d84904ea10300c01000b03400d082c14410700e44032002902500c0140714616106e034103440c3d182c90030040e48088843c20100d051500c6116040004401826000286110b02540035000404103031004010044041040c100b0341c3c40c03034041c0201d012035217070a168141c1848035800f4002120290780d8401100704009502250303500c2c0b490f03c4240380c5024885640003031700907441082848104001c0c0b641c0168400304c04407002014a10344a5a421144008000250f012903803078240a078580d4107400510459440000b2030303074a07040a8041204843c00c41800215603c4010705c1035000e802d004200d942441d001c0d130ba005082c5111104040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 370929559 1250 370928309 370928347
    0x3070228170c0a0f152102120402090c07021e03030d0f05150915190b04080d021b0105040302040515040e0c0112051308030a0b060d090201031a060a030b0402 69
    0x1080740e0844403a4040500b840c90310000202050883e111002c0c0c548200c100d80b90b103e110580e0b0421201120781c01d140c0c54282074041512194880c11551001c0704110307040c00580581b0201d11a0b03c20f40c010800c8031080200b9a030360701d070b00200110040301807065045181c21507916284c0d00b501060040400d103540d24800e440e01030781ea041c00403481c2d00d01520784800d000106003801e0b1159403200203015500c154215044214103060310028000013954242c0e00400c441a172066003289000240410708a03804519108a49402e800702d0b0400c0800b40194502010000a640d0005000307000030405071805403c015045003c42940c54895002d0750040390568041d11504d02e00e56010300d03076400541d6480f00c16011484a0583c003085a03013042c1024510480d02c81c80c019017160301c0170020800c1400c4580c030200c0003078802032001c0e6481620441f06406084041ca050307022a2401c5407030000c0c1140350005008014004041501d0041c0e154400d400030807a9041d03094015070300384810003a00c2211500e80d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 370930809 1250 370929559 370929599
    0xc02030714030c0904170f070b04050d1404050607020906010315080f07080f070b07022b0c0b03161107030f0b0a0c0c030e010f0c0618030206010803070228 68
    0xc1c0c0600011000741894007582603055405100180100404034490b64040d020414903030507400d903900c0e048040307501540071360100035000d0140c01092204102c00020458044480e0b030303c41c1c4050004480050346140a18407500750040010002c210043c544644065444401410009600340100c1c40d034204085141d0000c2580e50300207180e110852204100110040c003030840104103e1845240e12511349006200702e45040c440442c1401c2150b8400c203410103495000c412603480c02170351445520030640400c00c01e40300c001e0035240200b500103d000840340b007840b10600c111912861110104d50740955007101e001140100d0a012000403d0203000001050142c001d00059051080c4a8800c4074908c0c203160742448090040400082c2c0c001e0303044482c41609082003c0c2519440c4403c0d20040041d03c4000c0079145080c62186e51420f581c2903894146000350300b10780140e81c941c1c0b40e1698910454401035401061070715120440c4058221020041d000c04400c0c042017640c0b8800f02d20303080585484 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 370932059 1250 370930809 370930829
    0x121b0305160e100f030b0603070b0a020a02040f0c0e0f03010221060906010306120f060b0d08180319020409050a0210050a170705030403030c1809020c161a0a0c020307 73
    0xc00c0021a8000b1440340d000350302031200a180c00c2c03410811500d81e031584d2200400f003620490000e050f607a4140103140041004007006503650903e200300a45032141c24104074481d628000020141c03074010706c0307161008100c9440e50301084211104004080307640c130107815410340d000c00c0038032151040349a1690201c0f000382c031045142d046c00b00c204494540020301140c101480c000d0100305000a1704c02c80c200c0103800c407940200c44121350502001908121040b60f030000342c00c1001c50100101790f0000c08211502c0344c0422000140340d020941c5032074644400c400200f4102c0030050240c9019400b180d035031031007030084480c0401244d000c00d4a81c0d110590142c00718001140c81010a81c01030301c4010b85c20250b44001609261204c40600280800750010b8201903950010349400303402070750720305000010306902c0c0d81e14643d200303c0c0c0c030080d61000d19038190070300441d06141c0400549a0062003030301c00c00c0e25813107800805e4080e4004260405c41c070305010403030081d58141c05601d051107100068844101303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 370933309 1250 370932059 370932103
    0x80f090f030a050d050f07020303040b070c050d203c0a0305040e0a0b060a12180b07030c0804080403020d0c1a0a1e0215070203071401150f121b0305 65
    0x80d0130480d0802020142ca22031310341d00f008426540401204c0d40183c2c010311003822919a410201c480300c00d0b00794010682e00c180540010b2460700010783c4410030985a122154030343c400b8903555140c0d052220f4a560b160402060580c0b58140c1c038640c0d000c484101802051070419000c0d00740c4c5030841802043c0d010820005090103c11200589550302050614050000c4c0300302e4000b01d80385120b175000c88003c0181c018100c01108100780c002c4910003c40c03d05524100510b4208191110420756000000c24641494004810702406045105540122645051034a10380034072010041c0d002003110032000c1c1179004901c03c031203010700c69240c0c00e24408132621070540c1e24029118000361a4441498010b0181d09a4229400203000706584c0c901841000b4170b442e0f4803170a03465805071600040441015000554421405600c1030000c1d00d0103448108256a43d4454440785030414021030104680a0315032030041f5180e06550411034410700b84000d06565a9100c0c1c0303003071290610b480b4070010790001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 370934559 1250 370933309 370933327
    0x1b1a06010f02030a17060d02090a05090c0f090117210a02010b150d0c0219081312170306060712020a0c050a05062b060816060807080f090f030a05 64
    0x559201c2186005000951524a520b000644055810000341709100000000140c20b0f4965001c4c1468039903002d01800d0b600d0074100c510f040a07080031602e203c0d00744194480070b1001d203440340d0924542c034030280201c0d0a613424014042c91214000c480030440380301d100b5840e1b200740d000b0400c072501003040f041400d407140c1072014001e080d00d002d1030015109a030b5032003d042c42c201110301140d0001c3c40b05980041e240341c070b05405a08007042d03155108584403d841e58070050250510050107065500d805120219031030301c800300d0b0b506101120240403446400700103424640c0c020015070b00114020200c41c01c20303400755504210a182d501c00d20300180c202006400030040000703000d601400085400d070302410701340404200a805603610750310901c072458958166400c030380415140d0f4007030603440a110b45911001800d940e82d0f50030002d9081c90a00304030020385640724000c06030059a181e99a280d6580f07034650315121210000d0400e03407150207024250403418204000910b0340410584441351145612 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 370935809 1250 370934559 370934567
    0x32307060e07170f060c0f03150d0605010603090b0105180708040302120304060c030e01110924120402011709030a110309090403020c0f0a120308130b0901050a0f09121b1a0601 77
    0x50001d185261b401c0c00904100340c00c602c192a0302801018010141e005804005203151603195006081c0700d217800000301c0e00e968190000b412090080340e61360342e280d0380c1c3d0042c4581401003120700080214054080b0321428400d0075900d401600070702c100c600b092184500ca5580e94015501200c407180c0c0c42d1010230312aa010300902252406203402040101e030096454541c5200f880b42540c810404403c80042001050782082c0300078448080f0316031260020b62180500107010ba4050b808a0303800070b900c000710010203c0c1988245071100103036050208c546010b889140500803284180d005c14414400d0700e444042c00c00c0d00c598000e500403d40506294144490f8820180100d0b000743c0542c882031202076504020080e030603901d4078012109a13a0702110342240c041c5240000d000344a200203010715801c054000703078007641811030b0030082c1c10380c3c0000000c12a001540010003071a08025142d4006000b950482d40440e061690305101103450341c0d65540c0c10142000f0524495103000a00c0842c2d42c0c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 370937059 1250 370935809 370935811
    0xe0c0d06080a03021c030f0509031213081c090f05010c030c171906120c030201030510031e020301020d240e0f13080f0f07032307060e07170f06 63
    0x2124040d01c0000b042c1c0e18000c3d02d031821010f81658062020501c112800d20952100020107481007040084c0d0074200301d01e030385961100152001d60144000031070034581d031002d2205a102e0340071008514010034a040c0c1528240d10700003c807075096a0380406804a8140c0303100d00e0328948544000240340d04115409405c40f82600440030421050703611880c5007100015031190000040f00e40700004011001d1458060481030b0001d0503258138500031034041180a05200041e00c1c804d803800e0015a9403070340550300b01c44091001901440641c1d00c0e03415200c11030700a00064500150002d850041d103242c00c00107441e400140c0d9121500340d0308a07d07220520012000c0050500541d020515051500b0744e40006203001e0300e03d5084003d071080142c204141801110010b1350925862a20f0718066842c441180e0000501039012941c44001442c900284400d0a03025051140701e42d4106520794135818020040c03001d20406c4e40c8074074080451700c4800084840040407001e030003825035282150425082c40c40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 370938309 1250 370937059 370937069
    0x8060115050f1614060621011107050a060606180b070201020c21010f020f030403111516021006080304181113060f02060103050a030f03143d030602070206040e0c0d06 73
    0x1740c0501441c5e503a5200104c01103000da000101c0102e0320713001e0780381c01080140c840c20f4580c43c0004001c1c04000c808aa8841694016030080092130b5a80c0c07000d880d1600244105141060b4542082c03113551500005084081d0040c41142d070540b0354040440e802d41440b000008400c80c0c41c06848154103802d000740128888050030079418401c8081128003140000350004040c813980b40e40e041011401000152130f5a5110080a2094200400c6501401d83e41d003c2500040c01030a01c0c42c0c2404146000c0e4908481841000b10f1505142040901300342001f00c025100064507050249124200f800252021000d206a2050003610b408000780c10b04003202200403d41d08904010000b00300046241e07400540c01d410b019070591280101200248108800c0000380340003102031201c0c00c001e4036200b2002c80080280c90950074860340303d285100090320700444088810580610004000f0f4010f000d1003071001d030000341090b407200104030f00f00704c080742d0600c0ca40d500401c611906000b94025000104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 370939559 1250 370938309 370938313
    0xb0102070e0109201815030603060c0a05090301020408160509010810050402010c20011b080f0705010e0304030803041e12030b030f16080d050408060115050f1614 71
    0x2450312001c00d2240c40c051003411a119a0783d1030350000c0c0c0320b81d600141d0702024001c8a6503030b1020100c0c9840c024460034044540500322590013860390504007070441c1c1c000c440040051806965110641c801d6501041c2c44400b00321f4184803104040e2400d00103000500480805000b005481c550f864a26540c242e01451040380144010480030b5400305455580d401d442401040e20350b1180010f940310384852000500852248001100008810030490030000c3c00340e8402c2a01e411040c07800083c40070941c00501112420070078814040001d500908038107200b40f0002c20004101002d190550f0420340c002ea031840700001c108401c100002c00703c084080017411000380035030000d440c1c41080c1c0482004440601d640c481060a07035030f9042161a0301e00300176200b128070100030349c5040304010b0b0b020320502c00a0712444407804103e034040d2003a40d0540b9042c40c01032941e686000b2102810209080f210414001304004080800702c0d9070f0024880051086000403c4110500e04800303d040782217900f500075 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 370940809 1250 370939559 370939573
    0x61b050301180b010c060b040b130506010f050c0c09060310050f0a0e0109030806060714070602010b010e0405070f0c0303090602030c030415061a07060605040513030f0e060703121b120b0102 83
    0x140c1c0c02400c5c1e84051034004600258012811000c54000c3c400c49240c01da101004c810850100d40c2e4581255104410a90301c066106d54084400e95450144e01400006a08006520f002c00e090420702c07142d12800040c2140d081401c030400250840b007040d00c4420380600d402041080052150290710008600e0b01c4c005c120204207510028949038024008500c02ca00c00641d100602a04040d03104041ca200d40554141c560b0b11600039009003244600070303004c40d0301d220340e807000e40c0750511840d4800c48003a100c006150300c4099044803010b400e04c034105c00b03040d90b454003100420841c0c030141d4420030f003140720725a490602c0d08183c0100e14012451040f12428403500703112900e1f103400e4002808039840f00c0c7c42c0c0c0b035900d075251003005014550041a086850201000b007004101c0300b5681200c0e000b929890090030352544201c8101f628034010b290403c40812000000074890780d034140201c10b12403800182c03461400900c5905281d0381442d0000907001ca0701503007000030030344030384104490240020905 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 370942059 1250 370940809 370940831
    0x3051b030405010c14100f0c021006030f06090305070507082118091317040905090303010e13080d140916050d060c0507080a03020414090103020f0d061b05030118 71
    0x40d031800050050000c20300381c00c415080241001070000160301b4113000d1002c0c1d154143c00400410718941c0c0d0000601c03035460803d105c070302d042c845d140a60b50440d4090392800c4050b00e03000090314000e80210100502000404003051041c040390000e80002c0d0040c1c03203e00c000c1d980c81d045814440021b210002410082c050818107007440840e0b481314142c0e00c85081d0394a034020020006940c00300070b415140c1340c0c074403980e009109400810541e04240001c03c1700f502c500c1c05641c2c3d80c0c002409440455420301d004210108010507880e60070900c1024010310700345071005460143e5444d4002a00941180c0003031113040304041c0314130340c2484060f1466000c102d16003400901740000f201d8003d013030640e81d1007054407168820320843c0c20f43d41d0800342e100d0b918000250001c3c006e40c824441d0090f01c00401c220a441c5161107460790741220f80091109590344001070411421004907001114141d580c3c07062140c0b50480580065170503283c03511002d48035031410601544280c86401d20700111841c0008000e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 370943309 1250 370942059 370942067
    0x1a0f0406060e190b0a0f17010513020603070e04020403080d0f0c02061005013f11041a031e070e010305060409051509030906041212210908120403051b03040501 70
    0x1402903e88400030a00d1000100451641c07601504071342d2001c4000c80c0c0105003000d041c030580007541c1108008104941d00c0d488420f0400b1081c1301d00950090017080495512442440c05859040c0c00420051600e0b90303035a1440e030303103a1048916421494a5494a41444d03485100703100c080303000ca0002c0c20091500401c10460041a401342c0c506208014450314080c0d07005c1c01d90a92048021951003410400c03841c10741001d25402000d0300000380c1012000e0300f0401409041d80c1c12580b003056200d0b60b03190300c0780814043d6000241400c00e01c5143c10710104c5401421031095020b1b401c540c07200b84060f1544400101550001421240074070b0602005070005240041d915032009030000c910112600c82d05e1509041d0311410404c9544076602082c00710301200c024900d150501c0c403071507800702c6a8031261026200d02022004007000b40b45008102d914080a0703802c800725803803081d404a8070704004512002d400c5c04c811b440035000940c011404401d4442070701c0c1e082d00402c5090001b14141807520300024 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 370944559 1250 370943309 370943341
    0x5060f0408030a0e03160f05101e0b0d06050c13080a0f03050c070905040503090a080607080a0209062b0b1f1b05030a0c0b01050f0f0d1a0f0406060e 65
    0x41c0c10f0350b81c1c1e031041c40b480c4418030a54901c6601c00480c81d414004604140e19510304507101a0303034501444111281c1c40302180300c0c140c0b1200e10007548440300040198020001e11a022001e6003141084d0103000000d5090702c211880758620b022096250058503102c0c030351030100b94100102c1540b1081440d030102d004c41c0c1e400409541d05190090352071039040f8136907091400c01e0f40001c07000d42c1800e0500c0304104020014120041064034680c8100380d035910802e036a080281c62080124000c43c002c240c10003c81e40003860780301c002030001c0c1d147c500b000200010006411f0b0060390a6240c844464003842503e008541b408401124212110310020809000c5030210b4019001400751302004520816400483c46103907030741203c140c80d120f0084030700103060049078030303011201c8000150000c5124501040200e04202c000b07800600d115610720700b4403115010b81c42c1c00f6149207400c00000860344500c1d040c2c03584185010305042909007081c2ca03000040e50303003a801c2082c00302400d50030015104222000300d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 370945809 1250 370944559 370944571
    0xc09050403090b030c030108010b0d031d1f0302030a5c090103050105010f0f030e100e070602060f0c161104020f0a1112040324060e010305060f040803 66
    0x20691920328003598424015071100c2118040402000b0300c0c6070a28010b10304032043d5400034401041d00404100000070b0440004000c500802e00d00800700321050040c2000d040d01130b20b001031015040965aa00341c03000c0030030310006a00041004081051402102800f440c1340034481d1011648110643d01c0d0300522882c08000e90450400444d40b00c000101300e541c2030b0506007da042c02581610141d0240d00c80a5414086400d21000050302e5100350b00d0f182143d69145d8070554a130801c7da508901030035203005015254802c10404581d0400c283c4140d51800202c08000d1441a1030064041e061840c01003101c0049031000c420085006060000c9440d00e00c0b80704124005943d041c5003c603400e0014500032a00a4030208400d20000250710081020200c0c940764800500e50700c500841e075502d00c0203140c40c180c6a083c801040010030641c403d0202c03000424100305c07100c44480c9603030304035079039070380300004102d42d1030010004e100c4144400d9401c41c0d01401003088500c6c050300c0783c00b81448007400c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 370947059 1250 370945809 370945811
    0xa14061510140f0304031709030405060705011b0c0b070302090d1e05060a0605180610081017100606110a080c03040e090105011d15010807110d2a0c09 66
    0x3680d026215007001c0468842e070441c043d40f240b01104801e00c10740c00c01c403401c402149041e00c070460841040346030346110b03010000c000c528060510341442501e030043d03030b1300725215901c03500d8003010041c407594890603020aa690700a03c0150a0408440550029090201b0b15104100319440c0c0d454a4100d410344a8211050000003080800948815040c901307003e04140100c609002c0014200c0e0458003c8a40c2201c50714410140c541110950440a0fa0318036481501e07400900501806a030800354410154090842c459558035240380c4c40744a1440e00016503000740311004076140380340c46030002a000764980044007940a20711700b50f4418801340301601d443c0020490000e107600030001c540c098a24100100c6050500160640c080c1400303004844803a08510342000c5c0804c021002c0500c16141301e658140e021054000549056001402260800600c424103c500c3c0c0e104000fa401400c8041d903540c2a8001a0303041c1c05c084150081404051025a480c01d40105e0705240d8580d080d1030910070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 370948309 1250 370947059 370947079
    0x190903051c0c1e150b09040f02030a05100b03071a030615090604062001110301140328030807090b2208070608011401080c03010603021602040203090a140615 69
    0x500b03036440704224400400c494600d480c403080030001c5090b0b65420700e12643e09038064072804510081070351000c002d0150003c41c02000140444d21048006201d98000303016202080003a884042c140b41001c0e0500d001d0588554101707189041c1008420010181005000001c40100820300c0b0103101c0900307004d104107a408202036808401d40b08843754044014a07a80e555940c50304003400c0c2c0340450224903440d00c0100c80340e03091490180540c000c0d8110301d500c040c1c9180c0c01c1070b80216002c1c8102d0481901445404c60694080c021900300045d0407101c404810008113083c42e008040c00c100402c03500810405080800c0441501021382d081050501051412483d000e4031b03050002e5019480170f0420305c00c46c48c0003d0a9074100620034142c400b1048004900b0441e0b800640e1049400e5800c00d111140030801000341e603100398003400320000c45d02d045800000d040d8001500340d0300191151041e542111402e00100301100301a54441c0010794060030540c5005488609403440e00742c1140c1c09034035070030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 370949559 1250 370948309 370948363
    0x9040210030605210106081902010c0606050301090f0219050102100c0e18180d05040312230a0f02011803030b010903050706080f1e01140d020a0b19090305 68
    0x3402080181001410070060000380403007084128101402c40c1281d13510b809000305403407c0211303007503150b0342001c40c031a0a00400780d401151211020102a40d040b5680ca201007025502070041882c041c0c0540c1d09101c00154a004026081686040b815041c0020941c10449641c0116090040e200301c0100003905a9121a098039400c031701700c0c03410354042141541d410305c4080300300c26680101920300411166402d074220300c1d0b42e102c2c9442251000b0440034401040020f030780842d03100c0846c0b210301d01400a00044002901025400c9502103810600402e0072030707007543c1c4480d1100d8284024402804031540001002409900c1900c0140c101a150460000b131b0364090316141005540c0101116403803981c40900078003541080d10003c400ba00f069000c11111000a01640341e21010074200c942182d00e80b4400710501c007803036940e094110700441c05a60160b916646108000c110f8100c1d074640d070f46404c0c1030030303421500340c4160341081c0301500a0600104200060b2000584030340305c03c104000d1111 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 370950809 1250 370949559 370949561
    0x106031d0d11030f1b07122402160c05040506010906120f06080609010e0c0f3001330f06110109080a02010b03120408121b0f0a150b0904021003 63
    0x40b620707400c1c00540010314000201821714483c030403290740b00a503005183c0360810007c400c000d07220041c00b000958010b10b950307000000ca200c44030fa04403100040c6000c0080b07505241c00449940180d441078501e0a0401560500d03004450744a1703030902e0094511818400003518a69031504044185075a40d4a0a084900030b58440009069098200c07025850050b00c8030340600210a44505603003c0c90412181074144403a004c080050010305900d003034044030780c0003003055004007401c01d14a014040003022081c0c2c01e100742050802001080300d941d0341c410704071082184000340e02c03140800342030030304100e05d080110008040c0e4207a07161410100c0307601f0500a000d03110140014142140005800c151603805602c820300200c4290240e43c1e040151615114450040e88100382140d0070100107074000303107402001013186180100050610304a020006488c0045c41402210280d109205120078030031301b10714078514421144018005007800d0408074031000b0000e440240200d4084c0c444020050203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 370952059 1250 370950809 370950817
    0x70506090102131707030f0813061b060222080133051012050a2901200708070303020114180a030e01030b2e03091109060105041802030106031d0d1103 66
    0x9500840d0380e894100040d095001c102806211104100004ad24a014110070202403e09500005604a060303c17120083d50103001d420b05600c54484500c1910450064040f014041040000416607514450984440d00141410f60920041c4240d10080001020944181e5a0640700034000c600345035410f48640403075407160040a0f007000c00700300c101050741d0701111040c03142c404408140c10440c003404140d40d1116070018001010916172800b010020705d2a40b25000784d0000315020f56075075171040c0c0d00b000015001280181d46610100b201b46004200341034122900000110191901c545025621221200d0090920020f45132a0300c4582c044d52168400740c50161150000842d10b040144211202c0d030219211501c140c6c60301500a80b11b0320842d110540d00c440001c49003100e0030100504407030010450342c1001020000820034031552000d0800595640b0b00150301c030b506100f006000c0da081c4d400c400070f5a20b0103000c421490200000d0402c824206802c058415040103200302d825489 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 370953309 1250 370952059 370952063
    0x2070e070c050313031a061903170706050c040509090d02070312090510020c0a060e0a03060b0f060c0a0b010e0403050a0c1502070807020f0301021e090a0e07020307050609010213170703 81
    0x40326a000024440d40700c1b4145d001101080192429594041c1000141c84089402d020354000b092001d03c0002c80101c4103e10300c0c0c2104810b241000095500c40c802d0b03440032104184888408503003008030381840100c858000c500500604610060104000c4d951035803844058100268001e070166000d0044440b03601818026042c100385c440000f1006c1d56564a6004803400313284a4a000140c0c18415080000103820041100b031860780ba6032140009049010f0640b1f0b4802c0d6561038030089075540d8030040c0815a4588064004900c042c1000c003203030801648182d090703002d12003c000002c0e80c0070044907051296030802c0e2440300105d080450380ba5401e8030007100084d02c0000e03594148507030403000c0e0880510031110b000125444c201818280c1c0101c10907d084e11414046610307111300200040c1c41c2c40c4402502a030410782d50fa5110456041c02a581c00001d42c000040d00401e0082c14001e00e507000075403100a6180441c54860380c2c3ca030070b03c5031060103140455200d031455814018001000116 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 370954559 1250 370953309 370953337
    0x90a0f0e04050d020309061b03040504020c060103050601210b0709091113090c1b031e0c05010b0103060e070f2c18060f060306060c0109060e01060602070e070c0503 72
    0x95155100c042210000341d034103031014800d200000398514400001c83e940d4800181038582030840c04112080768811b20a411b0b00d440c0000c4c0400320310754850f80702900f241b00040001303001a525601f001d0303091503810b0700000c116450368074002c900d0780341d08413100380001d41c0220b01042940c0d40010850380c02040c1d41100d04100c0c10814040c0456a14401805055952079181e0101350760356440071045608004820b000309041c540e451144204410b00c141b0010b00034103011030203511044000c001c00c4c0e01e44440b01e001c614510b1010092003000d118222a0403001c1c2000c01205042480039805004018012810442c5048407000384510032a518549003544640c00040314804030119014410703400d90a078000d460181507034103c81101240c06000e000040c00c00b01003200e581041c00301c0c0d5840201403e400c90001c115140c4c281200b4401d41e00018000c1c080015001020b034101801e4690907440340c811540844000d006000c000801c0b5904000281840e50900b0241d00e409400d502800b00340c81910 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 370955809 1250 370954559 370954589
    0x5090609061605070504181a09100f0f0617060c031b190e19090b0604080d02010b04061512052e180c081302010e03010f15050102030a0212090a 63
    0x481c3c0029a0300a40e0421a81803041004805894601650743c96001c0c254407203000752240083c1c4201c100704d411100701030669031a90300b0381a010301a2209109550b1003559500f604420b01c04a900ca0032010707058102e6000801c050210a055440c80c0281c8541c00d0003400001080843e848104508021790051021648410446030483e1f00440200d048502040d070700c405d03000c4189001820405081d1407003460400142c1480e610741e00800c0c5400030707203030410310801001c1440102000800d503e407032203600105400704504c0c24082901c5a40d4808100b010074400c03404d001c2a001000241c4143c120100001c0981d0b840c054117075900c420600d0200350341d80c5028001c040781d4041055009980c0e41d13442c2044080d450312000d40c202d468458401000400300c4011455450409501103c064014174001018402e2100060300319185c04c2d080445480d62000c1001d418454826508010301e024000356062204265010b5150181c0700c643c4807851500003032003c0306588800034800a808079800c05141 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 370957059 1250 370955809 370955813
    0xf051e04052106130503040b0d05071101020901021f0f0c0c0b0903071101080a0e060c04050f06040602060c0309031218060a060f050111100c0c0b0903030403050906090616 75
    0x3035100d8011036019107051003070440c641c022554588400d60301000200060341d600b0403640e00659500f0801c6540e40001c12001032250b002c3c2c1d000c0c1880c417820900008035424030a502601c1c40c0301c803003100380d0242d0051103079000360707030f00807400740101d2070740030241351805407c2031814000b0701e207004c145440d80349010140c0c103d01741c1c054400c60311140f00ba800c0964903102d1004c8569030740103003c4020841c03440035592a205500c52002d0316007041140ca004103100c0f042e50040c0b0304019007101c0300c80c7e450201140c1006589005c01a0030041101030754414641424000300239110341e8010480402c0610000c00309065a5040088455884001c88024098101035102c0440344000305000e0700580b00f10000310340000b04d00c3c45540200c0f1070b080240003003c0d140c80c0055440d0311080c3c07408000c5016825001001c82c425001c1c480d244034241c0d5a04100700c40d81d1801002804000c0c04507201031380240304010010740c119040710101881204c080380c81e81c2c0d020001440910420024400c40c62228070482c1c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 370958309 1250 370957059 370957117
    0xd0c08190c02100512070504050a260f160f2d03050a0308070e0603090c04050709030b0f07030c0206011202040914031209010c020c031e070b0318101107030f05 70
    0x1012600c0d0702e1712070a54840803c215a580282d0040b0755104000c52010441d1080441070503800300c43c0000c9900c08040314081072070401104105500580d08180000c01a046032100382d0009002001240d68029040c4031405074030f0b5100300d822244196241c800c1100d021444030780e4000860784801214036215003403400a18090069503504046000c0b038980181a18000056901c120302d04002001a405440c003000302814002d0030107004d2000e103020200c00b0441c110349140c480c140201c0383c001c243c14050402003c8034020440101150413040050158800c000d0014010940454011507035542a040640c049034561182e80190702c0000740c1d04043c940010038051098082e00001c00002240304004e0380c0710350b403142c901545500a0440044141c2103c4411114007060508503043e894442c6841d400d00d43c01607c881c022420040010103403440300304000e54255110b4078080c4030074060a00c1c03414003402014001810b11030600c5070780540034440c02c15520201e0101807000c03010340319424689 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 370959559 1250 370958309 370958317
    0xd0309030f02120f03040501090f0b030604111603092102180405030f1620030a03030e03070c0305060f061801030b1510051c0501240201061211030d0c08190c021005 72
    0x1404201c4504000a04a900340700d142b00310380340003618900d035030743e00c41c200001403582c0072001c10204000d106051101841b00a00a0401d100381c07555022182031800841c030030160f035008888006007000710403005031a00030700001080c840c180742d0042501c031840e285066000740580e41c0980030012840d40d03d0045100e91040c141340c0110040f040801c980e200c5100d429404000c00340e05075003c03104001c0020320a500ca030b80c0890b0008152420003403203540f8107105a0807a4021b43d0540c0c0032105000f400690700010640000f411164007025603004926165041c105100150001c08040009420800c520328282c01d000001800015030038001e080c007400710341042c000003001007090130907070400880c1c0c2d11885060391328102e0360307078025544014600802494502983c08554a5910020b17180c10302034600583d09205a800c016500300803001e2528282c40140c00d4410460f40e030b100c640110b0204030484050105080e02c03074080c0400c0040c140c0d040c03c2040402034001240b100317404281a8400060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 370960809 1250 370959559 370959569
    0x60a03050601170405061f030b010b120a0b03060a0903262a0405220908030604050a090f11012102040303080c04060e09040f0b0a0e06060d0309030f02120f0304 70
    0x16048405844180f51400780200c500524a52001c00440c07840c1c01180c0da0720a0540214500c09001a00d1b03540d0802e01c00420303070042c2024070b4049031700d0101c401c2c03540030687e004105500820a646c541c2c80001d0b520358005e080100003540d299040400d162081c4284c494120030560300150041c0c0001071282e0400c1e04842d2040004410380000c0345558460704005150004840b9076410b05013404104140f071841300c0120394501300c1d52042c103400c0082c18003404807014000c0350607036224517003003041c44240d480c0104006a01c41c0381409200001c0d80402c1c5a0009541000701101c8415070140161030000001109410074040c00800c1c00045c8510380040c4256440f075034482c421601c50030000035045c000c501542001c58801500d464040c01c0040e950361340300d40650100750006006840344280110252000c503407150b1a0300c8010031550080140700d42146081d254031043e003400c2d8900400084c49400018055a282a0300d03100303650340c1405100240c400784060b01c4982031403039141c1d40e4a50252140d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 370962059 1250 370960809 370960817
    0xc060603010f20030702011407120b09010b03040b040c12051c02010b0112050c0904091b141305060301060306051f06050915090d060c020106080106140a12060209060a03050601 77
    0x40c40b4a002c0e1401004801d10201c5000d81d01042d00b02a240c0403600b00402000856507240c0c07086030440928481a4002d4240391a030070690701d1303850284010b443c030803078041d40101c071084010002000c6d940d007241c0e0312075000a1520310700d883e6403800410204069101c0415000d1002d000800d12038080380301840301c2800c03c0070320030307481803c841a8241c2d83c1e010002d0f4041905094644200b106680105901ca00310b140714a2070586410300090407110040c030240c03003020b640407a10009040c13030015480a0103050151720380e601d500b000041c60812407000948880303621140854610784094110070302841d4490f8040c8118600b88124104800340b1000d4140081c0d408080003604d00e000358201d821100b40681141c9a41960b110000b815501000c81540c0006e008003908002c506c061061030441072a80e40003060761890b20010500f9180c0c0c5811186d0451b400804680c07581e61080c80010071250200384000300070141d400d000000b40114100e00d03820040c00613440b0388656069100780d11840090721 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 370963309 1250 370962059 370962071
    0x12040608010e0112020108070504050414070f02150c07021305010e04150203040314280302030a0b0301021809100e0109062103120b031e0304150c08040303030b12030c06060301 77
    0x1200b000071040c02e104441104e10000032a07005540304810341503000f29036040591410f07030788401080407102450013100070101442c00b0b220410f903002e4500c045036a200e00c0182001d0700c040400c1036140d04080e02282540c0c40001d0754500b19112001c05481a8110040030090303036035a01010700d6840c0c0103c5045411100ba0031054130303001054426a8000ca070540da403c600701c04100501292503201c201030800001c003245285950f000d0303800c1d00d0741d60440c840c4d601503200c3c101800e0303000c1507882d04410329100c0d90050001482c0c01201c6c840c2840c007000100c403080400d4440c2c10103402000d50503006590306040202c00070564410380d8001000300d801c1c05284a281d104516056030f20403000600c000c0c0042c0c402d0b410000304100a82049060800003002e458010380728200b50800d03600c04e0040302c542ca80011800700072500b409044842c21501d02e0402c4401126184d5520390248a507000c018181079607540c0b00d00c0e06403910003001000d0516442200d0f41e40c003d400b00c0c650303288001c4036054825801d02c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 370964559 1250 370963309 370963319
    0x3140a030e011e11030705040302040f0b0301050a150609080c0607060b120c0901050103050c120703020f1201140303030f0403120f0204141e0d02121002070b010f0803030709061b051204060801 84
    0x4c000c5034412103003591b46a0629046a0810006d044280c112944007a00c8821a0701d03903540038400d0b140510050f820006039101c007940c6140f0185016417100040c40700d4000101f00202e004581c12204460841d281c5035150b545252100041c0742c021483d50308840103403000518024001030300c1800f2881101d201803103a0b650401142036890480e12110800018000b80c42604007105130203412200d41d040250134214010b2100300c640d008401c00c80500700c5404010010b850359004014a182415001303589945403982011500c51400740000381044600925501070a445034401d440d10030000348195601d07661540b175013002c152480328891150000307200e03010502c880056454000903001c0e00c00c58140741c00c1d40030424155103204102c5114042c030100003201c000780307100404490b44a09400b565079410705521600100458101c40f4066004105100141d5005032500d012900c0a1a00b108442c0c801035401d050528261401085845220308602c0041c074001d002c0c0c07081d0303a2180e4680400d0ba98070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 370965809 1250 370964559 370964591
    0xc0e070908010f0c05091306080d090512030a0e060a0c0c0e1909020a18020409060f030c06030b1804051608070918020d02010509061b0a030e01020a03140a030e011e 72
    0x1c011300c600440c108103c00101d504184151060040304d0000001e1043d503030b5507066041c118050311800014001c201c080c4014030304101c807a180110344a000f07509048036620040d042c1d52203074008501c6031300301141d8001014410740c1c0c9211410b500242035050aa0b40355000440218182c402071039501e0003600700751003104244030305106c4ca0f8000303100d01102d80c0b810b400400640b04c1c952000d02071a80070003002c11080341c2400740b0001040d02401920180e45141040803040c1403c0d0415810035061554001c02030381c40c910700e402404594442000d046d00e03149803040c5414403640035118000700c01d5400040c3d84102160f204101c60403070a05100c81c00380103104101400c0c00050007540500007142c0745016512840241c60f4100780504260319000b1508422440c1c40119820300c015940200007000825500900c4c0b00d5801d54280000d050800ba15a000b0701070400c070400c030710900100881c07484003540c4640c12442410100300002c010b18240c65030245c9502c070968000c40150350a04502013581005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 370967059 1250 370965809 370965821
    0x110304140c030c04050702010b190914010b040311010309022806140d0c180905010303031508030306040f020904090303050405061b030705450f010905010503040c0e070908010f 77
    0x4003c0c10588120b881004010400580300c1c1013103640e10000b8050503110303800e200c0f4408001c100018455840c3c19a510150707405400c0312a0600c0000d00104100281a4242c90603a6403040350b503030701c032030061004900511002d40d01070741c0001100300e070030001d900d104850b0445041111250b91115154101500c6070f4018820f85140707890104110394054299078404c095104d920300d0b0250050011104001c80300c0c6031034020f2021150b448004108041e0144542840c6c102500e003041c445500c0c100d000c1c2e88074040100003c1c000c684610035501440103581c11101c04080003481082001924100200100801c03a021912445a4401f041900d41c0c0e1020140d00b0304010700490349180e032800400c564a0f041490210701c3c0244c01280c022511074404403183c040795803002022104c0c0080640440030480200c00c9502034410056180016603016111a0540c0d00a01f08650342e92181e00e040f000c88041644844c1d40d00507a0b800703201d07190794000c0e030740b000301c0381c03034000078820201c4d019500011200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 370968309 1250 370967059 370967083
    0x1e0b060a0b0d0b0a03020a0611010c090b0414130f021809060306130804090504080903010c030605130c0c0f030806011202120118090507060906021905120906040911030414 75
    0x81c00b4440403040304680e400640c1e0110340905107800443d900e90206071011055002480829556180241950360901c03486204111074501a43d034507180c024084018480c03030181c021500307000c041c0701d40c882d12003803009900010322810422000d420242d000c0002e40100008280503600e8040181c3c0e2481c14024045c020302005001d000316445040d9868102480180c040350109010b11000804105502c1214072580c050400190703140c0c1800304240c2100e102031040c13001c1c58541502480262100e00c583d003046135041d1400200301c08103480070f0f5004043e45900405113281d45524400301a40300d0011030140000f83c845104000802502c4000d034010701d0b1500c5e040410231001008200c45800e2844801a81004001100301403900c480381866070540054020903403a0030200a4194100016080c020a20340901272010003035564035255408250f035102500c2002c2426240c55848004450007400350520410000c0c4104000401c0358004507030a0318030650040b031001e180d660200f10424092 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 370969559 1250 370968309 370968329
    0x50f1006031a04020a03050a0602030f0c07150f020906071514040f0803040314030708040201020f07030819031503111302070b0712060f060c2102030a0c08071e0b060a 73
    0x200e0b00040310302651200034416030b40001015400400b040c0e060003480d5896000f40005a564503140d82c0004003c00c014060ba0001d860400c994000300b250351442500b505043c4801040e40ca041ba00c08001901417101016031000e80041c0100030001d401000342c20f200c0e6003a0713080c440000e080707134080320788507049030050003040012410000042c0420000c544c400c0c0301c4c0c140b10f5200100d002e80d13840c090f0002ca44850102c0c0305001807000355a010491079a944071110010705085040d03aa84154a00600b142241c696400c80e22042e02280a40c114002c4401172b018503524481e501e007016402c101d40f0717540440c020b902c0070801e20002d1a85001701d80c00303150007004c05401c68072540d00c101c411245494460403082d40d0340e040402c941ca40802c1c1c2600400580e500d5410600007410020a110340c8020842205c0e00c01c0c80c2020075464021041ea00107407183d0400081824460500300c102c2d00c81c544004040400150084800c1a1250b58003480c0b24096021120305035615003c0c0103030741442d806006091 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 370970809 1250 370969559 370969583
    0x60423030d05161727031f18050a1a09150c09040609060b0c0111070f080a091809140c0a09020903010b0907021f0603030e0603071b050f100603 63
    0x914446600c04408911821000203216025013034010b981e04403c0940031810b244a0384034810204080f101030002408401510200da100d004404040401c07502070401d050701ca40d000b11124000710010303000160404140c881100c2907252591840780700c000c032402518030201c00b060b02c070540041d12030507140340f40c50100e141d51106d02402c0d50f640c00c03220500703900c80d844120100c2c00e0400c500a82d0000c10040d214161a14079070f504803801e51f104508134213413012051000d14042030403000012000c58025114980d11302241808440c605525000300c603d074005070503144461021a4001c5103054000ea91440300350302e16865003074076080051000c5510410400081c00b003010158001d025204004000049810002c00402d800d01e2044450b000940c20140700d11020351071144298075081600d010401560b411940c01800309603004c0c0607180a81000f00c006506540185090140f0100104000c0900c0c42e2500e00f8076a1b500086541e030110340143d03600ba00c0d42e02054040c0c1c3c01500e5004080c0140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 370972059 1250 370970809 370970827
    0x1002060c0d0b27060a1d010524130f0503060f0106030c2102120c0301080a030c03110a0f060621080c1f090b01060c0f1b05060423030d05 60
    0x180c02c640800c1c1d40c2c0b200c1041030b90040c5101201c0703c045801141503c031456882c0440c10019008510390059110710902c20494030741c005400921415500c00311442c3d10041041c7c81550401003003104800c401400c0018034590350b210305844d00f0200d90190500f81180c90711001403503180c100540d41301c1004442480103020343c038066005494003c0c83c52916043d8003001a80110207138074000303100300da142d600064a18255681d641035940c05042094842c0c40d552610840d156220142d040260410003e88001000c1500c503081d085140808001103e82400a83c102005c10303404401040303500340d191180009010042a480c03001d803114a06010340e16801a0325261516407003c42910701601440400003032020741c1303000861484201c03c100152030083d0b850155041401038203c5c1e41400924200c0c4030002c0d403d0f400010015500004524104a207007a0407120300219400841c0e120402107800704441650404a8102081406100c15500100c00c10702da1105401002c1d000010810813440e00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 370973309 1250 370972059 370972061
    0x609020c0c040e0f0a0804210b04030e0f0d0326220501110318100203102102060307050924040506070c0f0320011d10030e0105040f021002060c0d 64
    0x1030003181c51003510305000c103c60001341030104405086445030000311f4140309000c805580c1c000100703251a1522850702460302c610100741d000410081c2081180f400c02c00c6203032901d00f860440381d8000f41c001c0610b500070b881d000d00b81c0491110785012411880088580343c0c409172041340d0040b203003540071004041c01c030262080d51168481042d107081d074807520500c92142c6142c00840c1310b17040940c0043c5990b11181c0b902c0d07040825901d4001162170050080c0300003c41400058001c443c0f000203000c5962802c02c0e81c52900307901018010390700c4040442007001180c3c1080091114580c101c0d641190064461520f20904080e100c10003202101400b0a00250904d00010865140105c03e402d2207d5a148004002c1d0441500304982a00005948a42d1a14418035040900c502400e100c800700c1c52540d20308601c032402d20b07601b0780b040c0c15007421214441d000354404100c282e03d0500a008030b140030b08184bc50f800d02002d04a00910440ca011094240b0205015010f408100d8100e0b1800085c82c032008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 370974559 1250 370973309 370973321
    0x6071d040c02030702100801031a010b16030e040f0507030e06090c0105030601020a0c15030e0c0d030e040b0301090b010302190303050a050a2007080f0106050a0b0c0703080408060a0609020c0c04 85
    0x180a510003041307190096075600b00440f25041895550801d65815480d2600c00b52811170358290706040040c0050100c040028260360101c080906650601101d40c282100c42c2424001c03041e80007860b000d110366040c160358010f544600090341301031043c1d070440e003009070707890a045030441440d40210100c00201d41c03044000b0340d0400d80500c102c8030380440300c0c0c03250304001e515980004842850341041c0d1940c0d41c0c150084d5014881c1440c050018100c580d40843d012001d503050007010047c082d020319595a42342d50115441c2c89020b4000c00c10f08440e494880c2801000b80001d034800d41c480b400150403a000c440090081d00d40c9070b95058100000c800080d81c181d003021070704a050000c2c9080048a0000c002040c05508401c903000f800502d183c01c00c0c031418058909488511030341469028000c1da01c0d41c05101007100d03246111903a07030f004114003103410300b000e5410082c01c2103c0054000741c43c04001441034010303101c02100b08007090396035402c02c04a1080c2a08411240c0046160148070300c0c1650040b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 370975809 1250 370974559 370974581
    0x60703021906060302060a0207150512040b0403020f190219210503040509090102120f0c09010c0c090c050d05100e0f090a0813030b010e070203120901060510030b0306071d04 76
    0x1241c0315071a0707030001e1070b2034202007e41c100503882403004014404000c21058038070003141c02c00b00e2500d80c1d1140e1002e04c42c9002040580b0307507041c00c40800c00301803007040208200b01102081e10505c0e2080c0c1c0315082d102d2171400d400e85c030403002032104d1910303400c038003d5072021104240c3e42640c2102c00700041880581e2424002c0da624082480009100d0312407102141c41202c401c000140d5542607540401500c00d006400000c0d6030005c58200312202d00c1400c11070381c550900342004500e0003150328052401f511180c10210b5514104418503c3c40c64024014040d0b81d070020600344400d6940c602c58103400ea01d98410081c84201800201c0c0c41400682e08041d00309261505171405014551240c085543c01681d103116100c00c001c00c00c0060080307030501d40c0d0143c05901000d000711706044100035940e0080c003203c031200c00040400302d4802d4009602c0380000f00000b5002c000d061074108400750080c2001314003c0d0190155000240d05a4807030035840500081d00300c484035140c44000305000c002e01c00740000b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 370977059 1250 370975809 370975811
    0xf0c07080409020301051c031202090307240908120313030e030105041506060504080d0305060109031a07080a020903120a1206080307060c0215010302191502010c020c060703021906 79
    0x250408245160000c0c005401c0072400541d4a52400c0107114001401c001d40517a031180003901d140002c0e40c881c0030f00850491007000582c0751800c40002074240000c2d0350000c1e45c05100301307000e40100c1d843e00c070900d44603020303540350080c41c6a920518151a00d07401444001c1403c82040012141c03401e420074404598000d192551240015002084c01c43c0c4054805407006070264641c1c0d0021242c5008900c044d00c00c51420504003490030091a94030851000004241902c80300000c005903c560b41400c01141c10424035211103649002d800c00250301a00e80c0d000103084007001540040b100e000b00e07004c0c140054010451a60a4200381000390001080c10b000c01c0140340074404001024066070300500080c402842c0d6550030f504d0320400b1601c00032140b43c20b40d00b0041c10141c02904020420307044a4051b295000101001c54040402c100d00b904001984000d909100701e04c030f581588000004544e58003150b034084508803c01000d80990769000b4016408440003000d44480144601d020a219842c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 370978309 1250 370977059 370977067
    0x120705130b0c100e0a0302031b0a0213050a0f0b03100504140a0602090306072c030307140a03020f060105130b040608010606080a0506040618052e0e0901140f0c 70
    0x40c0c1c2441560081c0000d0300b16520144040354102d4591188030f801810729001480f00f403032140d5000e5124010340c0c038419a590505201c1c0141000300f071040941c4164010600100f0304150041034005007401d90351f03280d1003490204041c0e50440380344590580400300030300800110038a9030581c805040024812a850711f40c00416400403401040386c0303900d1034070407900540c03074003e0782051510305000245403900300481d4120950001100740545080911f10040a805008000012134074600c1a150003c019000c4050048442c2c81c010800c00e154612980c2a1040105040080b6507a558207009141e4000610400207114042c264400030703403680c0142c030200d051a541c1c0049402c40d0890362185010406050030440702805d13521070142c3c0300c0c1d070481d4101300e064104214110391a55901c4003510403540c40d03010861003140d2950b94116410403081907035a1401014020302040c0d1ba9200d0b00250a10050100b0350b01801070007444e918003503a0b211103e02c0d50703906405040040020304030b21403183c0104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 370979559 1250 370978309 370978319
    0x1090b010e041109151206010c0816080418050906150a0803120f1003030e01050f0915040602010f02030405030a1b060e01060e0a150302100306081e0105090312070513 73
    0x4040c054685440950058071a682102409560384199000345c2111908001e28419011620300f5603400034004e280c490710400c001d207003804540c482d42500041c1803104140920801045a00420a4880d0225001440f00701c214200d8161007081c0c034001541d400c52400111045030f003c40858804800905182c0d1560751151040e04581c00000c100015001120400514041c160310090f000740103801a42c613101d15649009081c0302c01348208074100840004c50050000e003100030b4518649004101000a00e80f00c0f001d0310030795006200d114055404c04c4c140126114251094a1145030090f000d145098603a200440300b055007a40d51100d101c24120500f07020402600c074842026040100001e140d50074400f003600780d020020400c030503250810408110818004000c83c0c1143e0303040da50000d2058040000f034000d00580e401c04580c0b807080712108422100c0c40b180d150380034a0500020482901e9182c4040d481784510744030780c4105451360000c1882c0600c100300402581d042c166007101c04580312 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 370980809 1250 370979559 370979561
    0x3305040c0915090504060207021f050708030a060b03090109060606020102040b0d020a140d050123060d1e0e0a0c06080f0f25030e060106020304141e030d020d0e030d0801090b010e04 79
    0x40e1780c2178501540c01b107615000c5080c025401c405840300c0042c0c40c0c042e20340d20b04005040d4480d40a0040101c000400802c8241c8203540104001e00800460390791a4500704580d03500801c01c10070155405414038800145803401803084a040d9441441c64601d49203038244100041d41c440c91110007040305c000440f08401a8600103006803040c02d071400308507035160480e21240011340440c500030203a000c0000074510340d40c40d4221001c1000030320b030108480b20a02001d0840c0002802c40c01411420500c00c080005408914400e03e18410a403155900341c0300c50044600c0c00c0c040f908202c000300814040b0b0303c032081c1003040e294401445481c1ca03802c0000a40b070b412030b0120b0b140804010070f1701c0780e041594441301801054090503080c4000c41c2410300d00400c0152801c1c10b180ca42c0d02943e40d40d0601980070006a1414000441c06005c903900c82080d000d0017503640340b4410381d8400042d141001d1107018030340403c9040341034025645030301d9141d0030310307144030700400901c882e550500c80081140115070720b603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 370982059 1250 370980809 370980811
    0xa08010b04050604210813080106050604061e020a1b030c090b0319060603170307080f061c05030c2407050415030f021e03070216032604033305040c09150905 69
    0x108400448007685888c1845081d81d40755040070744200303414041032000c03d42c4021400401d071a100d051002c82c1b45010810f0381410440c0501800c008051500c040d0750b02d4245949104036446021000c280c0e596588802080303400000030345034150007c80d81800b40480e0034003c1003c1a008140000d03099559645a13000d0714140c1c1010012880e0100400a030182c000503095440400c030800512245041000107000103c0075804071030208101050a050100070405c2c3d9012500e00d104441c212000c01610450940140c1c2590110070205d1002035040c0388a4001d039000c48015224000c554103034000c2c2a030290581443d94100107900380070507580440c085040c980c02102d4003c05039238070f0922680083c03e1904000401040300c0343c4040800011307032042c40c103581302e12407400503d01c4460010158003541c4156400a00050304090441d10040c0d03201411800320142088282e10901d070081c02c81060340c000300d03405481029003980410040742550002c042000c07105103d01c41d41500c8000d400100e0390 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 370983309 1250 370982059 370982077
    0x61b07120510060e04021518090c040305013207031b0c02090705070f020f0d05101401122003010b0a0f0306050c04050604062109080a08010b040506042108 68
    0xb102c0111008240b42600c03d480c00b600503200030201d50b00e0117802103506081c030011a00b4070240c00041d440c40d0041000c40e48580003038000e10504690070014107a0000341c200d030000303541a5181c40110030350003056100708140070000000303c101001e00070041124001d8000c080d5014503445440e00e40402c0c11f50021051780d680980ca0b240d1520781c40e80180195007200514040c24030004102220115071000c01d00715545a046581358954410000401d5a030f08001e08014210300c102c5010381d2000c0581d8009580c4107112203101c0344a070380e84002824035400501005040e5155007004a0010394400900e4005160040d00104d407440074100401c00c1c07802c1c2d0b64844800d00700000001d00800c0800d0040d542c000740c000c1d0100e42480c1c24000054118410381c400e1383c00380100c0c0c121160b0001c0c1d03042c21000c019107030141c0400040c034141c20118083d5001c0c5006100007400040040b0380405008117450984401425280c102420000c002c50600c0d103ca40c0c611400b0740300d050740c1e000240c01000403d8a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 370984559 1250 370983309 370983313
    0xf110f12030a030507090803070807051009050a03110a0b07030b03160605120115080105061303060203040b0f0601080906071215121203020a1704020f040c030b1e061b071205 76
    0xd55002c900404656015215404201200d001002000400000d8814054010b42e006a80b001d8070701d049840d00c41c50a22100f140c03401e03d5096401d1020100b6042e40c218002d0310b49924210308003c880761a00440c8100500101001e40400c5400d8482c4d8400c0c01d08080c041c0455260000224500c404034885034000c2000900002c1c8042061000d03c0c00c081c01806501101207440030301c03d42c0501828014091032340503007004240020502c0034050000000d50300403008540c0c034242400c1c4185200401c4900c000d2102102010600d5941b064818501c10314200002e40390f030b512918011a18448104c1010400a4440d032010070720b4680ca591820080c41009101b43d092142458a0038404016170359800a2520521000756041e41040302c3c21014040c1608020031995140300081404198800007604540380c4500108401d415900c40c1d00340d01821150303084101e1444c031a0740c1e500303011240070350380052081c0a0408041040f100c90a8a40c80e500309807000e807a103d40b0b44080000020605513425 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 370985809 1250 370984559 370984567
    0xa1409010b03071a040b2a07060f1b0816051b010f080f010e0c07120306090b030106080a08070804210c0b03010e040f0311011d010501120f110f1203 65
    0xe1404008690080514841e0a2582c14940d040c203901d44c05148240d40100400154012544013040b29088601f0045c840310b10501d104080c080ea40ea4a0500480022501c0007500c1459540a040c00da000220f211014404468290340c0d5002141c010001c1e21045045002002c070000310140b000c0ea6401480c190302c04030914041000500b181c20070300c5020284400c1c0002c3c49004020001900d0558141c1c4220300d000b5114240f41c181e29101c0c0b450302410107500096290344840c1c2c03540020040b11400f0500344400f542c075104260803502c052041cac40c0700d58080b14001d000203074200042c080c0d950080d50f001d0304069031642841c051101e0300c3c401428160344101c0150410186262034009405400c4000c1d0441d070401c161140040340262002c0e01d951661104101054480c0d005440b0401032000240104800341e0010102000f500307104c0c104035420711001203205419050b600541d650440103205030300350b55840d00a044800c91641c0341e00000364181200c5691201a5580c6c0c103410040002e55407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 370987059 1250 370985809 370985831
    0x3190c091701020d201209160305030c0f0f07050d060207020d050307050d09030c05091008070620010212281107060b0118091e06121a0c030a050a140901 67
    0x11900c485e088220000174229941d4981c41048044e10501c01d550809000b05442e07103c0210b20b04181020020600342c00f07070380003004004d8040040c0c007415406030300b01d0f001551075060f40c648405101c15403c04230b60001e00100268a03118480c0030346c05004000040c035045c4030b0340108080c04c903d080181c409a00010301801003100401c0041040d20f00c0e403408444150943d5504c0950607030501c1482d03c51503140c4042162841507091410060411108440502e030340c031940608508040000d103000c010480b400c0380310614040c000c8507164144030800d541d40380d0b62104502c00d01350601d289400e007440100e1100200c0c540e9849090400d10b80e0665058584041e8508081a510f44480b518104081e2030000d0540768001107010056410349a0007140400216651b076020501e21324000d072032070342466400500b2185004e0548c03211402010000000c100c0c44c40b246005030300c155903c0703084035801c000042010105070b01458000305010302c0411480d240d00700700c490049041d07825000c1a503485400750700d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 370988309 1250 370987059 370987061
    0x60204030302061302060904020318100e0c03062e080f0726060117010b09011d07090b18010c0f1a0108010c08060907020114040b010f0b03190c091701020d 68
    0x30340f05112220186941d0003503800728101d4010003980718043c0390044003140c105261050740c1504004807003301c1d0810340c91203003114058100d60141d02001d0041c8000501c0c0d40c2004681c041c031581640d100c5421403000140c11701510303500030500c0c03901c0c2c0c0c0d034901021803846000d200d40710b10400c0c00c1006084c11418801d040b41811f280d21034244000d40b018050608030b4201042e02411945210070f5240541190140319002d010020030495010a1000011480350340d480711101d44009041008845a0740301a004e840c51621405136840c241c00c28000c1d5010340c52102e1960320003034418544070040410720751300d4050441070b54100320303a400e10f0700000c0030405214200550061041c00001c0c4010100448043c103d4400941218081d0380c2c00d40010710024004d410101d0280c2c84241c1d91050f40c640750070326942c0b0000a0041d1032844400c1c1d240029020045030541e07003e890104a68003242c0b07841d610740307001421003c1d0840c0c10b00180d09400a0750000e0000b10120301e0810310009a80e480400007014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 370989559 1250 370988309 370988311
    0x609060f0106032304060608030c03180406080714060f04090207050d03060b0409050402030a1e05061303050a030903140301120303111e070602090409030e1008040b161b06020403030206 81
    0x341c105032130140d125912a120002040c407110300407075070300c180d83c50b01d05281000c0d1100381c1007061a07120000e0710103000303140000101404480d1081c10200603452038204419100144a8811154007a200a00c138140d02074100030340c208002409030380340400c6c82c0b04500d820341040d401b03c025070794082104001d105080c00101203025040c60104400d03030610100402d64001d60051817215544c0e40000707011074608001880c92980c20a502d00710300034203402c038184130304204503040365640140c40119000b081d101c1180c16510f5851b403a4241002680d00d0100d000701620a01a01003025840110a40008090007036018094000705091404268203010342a14901c1903012403103103042000d15004c69409100c0c140d1115031000c120b0b81d40c0d400c6c4c104a0080d005540843c0c0d4880d25281200080680100040d028000199445c04c0c00311041002903500400484014108543ca000069070f40302002003009c1400707006041c1400c90800f482000d0040b94000b110440d2160380c001030034814140c04000d25 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 370990809 1250 370989559 370989569
    0xd1e020d24110a050a02070302060c06180c2b0c03111002060c03131406072f100c0216030c03060b10020a0201030c031404060b130207030e0d050f0609060f01 69
    0x50216082d5518002e01e14440c00101c40708010002c10541d1441c0d10031711003d001950001c02c8141c9594907815900e86441042e152034420f14041b41d04250541c402040d2031b104008020020240c0c0c000b5800341c00c0090003954404102000b5049541d400641002c6031280554082c1c00c00200081c1000144180c40071280e01040c20b5600880806c2000c0c0010701c2201d50011320101911586103282c54071081505401021000d140221020048815803200480001d4000490480750842c42c8103034060786140000702110454100f90382d40142c004403900f108100644500c1110654002d10303074440c451080d150000c80302240c07074178020402c0c41000d0080030092502203174440714003050300c40302942d608019030b80241855107031811442420b0007984807802c2c2001c026502201442c2030710b03101000700351101445114a881d641c0e814200301d514800d0700c541642c16102d254950b01000c0070000c2c542d2003c1c50499803845101c5882000003000c0c0115409507904400504040c02c0c095103183e5155016042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 370992059 1250 370990809 370990811
    0x1050f040605131e0807150c02071202010f11070b0f09090a0c05070303110d0c031d01202a070312140a230a110601050901050d1e020d24 60
    0x580c00032072184c01d482406400300c85100d80c2026130920700300f45540103190b030243c0704c014100420048211150400340c1c1459066007520507045e2a0216021800ca00b44000707400102c001146c507210501500382a010168594102d030403441d41c0c2d0500b4000d5500c1610310103010040400d2021950500400c001d402a12070300042c03001d07401c9035000030001d000c1d254000c0c08160302d40180d18001940b41c2c040f200640100303c0c0c240100c0c40d180e1400b4015090310700320822003141030034029400300d8041c4180108208001c41e01e602c0c1e42e2200300000d141c0c0d0441c0c02c15402d40b00d880d0700740b0050708440160320120b8101a401503d0040d10b5810720407405100100300c20184040d200340c06010300f840c0d904688040109081c92822041c3c00d0311440e107054940c2c0103140c0422400640e071411503400c40b00d400c0040d244c61045510aa0f00ca909001c8800028401d40c0d41081520900d43d0004801e070091406000c18440e4a0445c0c81640d000280102c05a102c1a1001c41c04000c5403452000100b00e1806100000c0708 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 370993309 1250 370992059 370992091
    0x20901090e01030b0c0d020702100503010e07080106091e050402030406060f0806060906210a0813050303211e0a050406050a09050c01031107020405010f050a05010f05041a0c01050f040605 82
    0x2c5107845200010700741c079171060001541110000e410380c15a502c0345e070041c0645901420202e405065036000707010307841c07111381c480c1c0004505c0361155070032034103a4240e41e0754041454a0215504240c03408003100c014601e00450002c07540392294405144502e0062401180d181e20382500280d140002e0342002c0307083e03040700c000c02c205611440d84a68011000340c48001c210014881c200103402d103149024502405013050352424000c9401c041c0200140300e07165910030075960740405949100c1d400c805280d0100d80e1840340e500c0f800140940c0c0c1e001c101c103080b8040c4c40d4042d07a0400d1340b550044842d420269543d40c10310082c040144a003a600201c0c5035001c20451049440350360f684d403894000b003030415841c2c104a5244c0c00300314040e10402175000c0c0c0144071a586079121141346d040b45004403406010b280c1000180ea40c0704449000b6032500b50b4072540d14080c2412040c00d803078001c8403003000b5045020050050b10007001d11480d07204000d601e01050300360819103014419910094140c24807118084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 370994559 1250 370993309 370993313
    0x91e0218090c210d08090d030e071a09101e14070b040203120a03090203150601080a0507090308070f0c0f05150c0114100305160605090603090708030409020901090e0103 74
    0x10310030482c07a4200c074440d502008420151181c150301d0f44505940d4041c5180c8420f0840d00114190f0241d400b00050f80d00c500d1210908a0450b0212a00c4250342e601c11304040062140c01d803090030012000c00030007450908464041120900b04180260014280280e046410307416a50300701c034050080d2400c92141e11092021501c80e009480003d4031407050107000c42d0442d54204080c0888081c00140301d0f882e005001000b03402440c03503100030b900038020f120141201c4600e048015201d110141c442c1c241d50b84406400f40b0080c58010075409c00e0004c61140440451014005022024410300e00c1006281070fa18001d614025590300c80d61103403000300700500c036580c1d4100054444c034040c0c1006546640090100d94007401040c80d900e10a40b101c68103205031100f0103581c80f02903030300810481e82c004882c154020360081143c8294000107078103001889191904600a5400440700c00440e0726103512000801c1c250341c41540010410b40c0d00051485055030003014a100401c20081c1442043d8515 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 370995809 1250 370994559 370994563
    0xc030403021203190e0c15040807050a0617070c0804090c030f06031106070611070c061407080d05090a02090709061b020306061c0f0803180d0e06030703091e021809 72
    0x20f0504c640003135031510324a80210380f081020f1400003100410680030408030708800280c039405409201807901a02c140452941804400c8034215040e554034001c049030780341070f0f40c10010b030007600c41003c0000c4583d03c800803501c10405000503208804c00003854072510360000c1c04440100100a9489040960810200d504010a0030900805442c015a00e150074500300340104025521582d540c64081114420b0240c0160b202064841f19110048104400c100c1c03c1c105010f01c4038010020781e810026240c030000035402168000d0110305c04c803450000b4503800107072207050854220b00081d40c80c89080100b241d00042e0200840c5204001d10403d01d041d0700407a440704801407800f0302601040b10f000e4540340da442c000d2034540d80c01c05886085d0824030b203030180250f407055074409405841843c07000c1054001141740c1048400d05d440300504905142c0906c0702540004218106069882d500d140105421a02c034803801010507081c07981c1030060303104004001d00c02d6102e0080c03241e001c03820040c1c04180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 370997059 1250 370995809 370995841
    0x12050603100c09080604060f05011a04032306090d0206070c03020a060c110a0803010302130204081b0303092e03020a080c071e110901050f0d03080a0b090c030403021203 74
    0x102003000c101c00341c0080040c3c2c0e01d8030f810340c00640c0d5842000200418000d090703118218000801c402400f41c1d0b6a81c1d40b000700441180d03104440c2c4008100401c0001840d140005240c4121480c2d4040f154807a01d10300d5030030401c003150010358903004400c0a2416641c180500750307008029051886400e001030303d00a41d103202000d4000c2500b130f40c424202c109640150271190741101e0300c4d41102c21036109894400c4103502b0a00c000c0f0300035201c8540e00b02c20301030035009607419a845030300104a602c211480c0149180c00005090703425000400c103d40c039a40703c42075007400701c0c03c20300510015504000704103e0056910000c10003014030500103a01c88540c4450960340020310f045111391619014140980c0010200ba015481401e5000306031040003403091550101c00700480f0070720302582c0d9500070300c80d0b001420042c03c0d82c0308c100d90813610000381c02950595082040100c0001d40d10b213505c00481da00b81341c00e55101240150101c204001c044d410000c0c80f080c2c0e0414070000c0c0c1182000c0403172030032082c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 370998309 1250 370997059 370997083
    0x1706160f0e030a0b04030f0206060904030c060b04060911070c09180f140105041a1f180e010504030c05190507141f030c11010203060907050f07060603030e0112050603 73
    0x10088520107115901040741d4072669810803c0700c621420117141c05010001d080101e1070250091346d001030042d10b41058154801c43e015162528120302941d60780c402004c8900c0201d80c80383d0f54080200c1c2548039440b40c1807240040500d100d9071001c90b130070801c0d0446d01c41d81c0610000790800a0000c00101e0021109024542c484144e01c43c0c12040d140c40d80c3c0c4101d8000340d820302d80d0300e0a800c020502c01880100e03224074100c0000d0846680f6110000c0059120054143c05c41071202001007180c19000080c101004489030070004042148008080c02d4500c155002c1d40082c8010121070700388403050100c2d014482155038800303840d104590741c40b40c44051b0740c802e15501151b40c0310031041d113440b060f02004030882c05002c01d540c008003510016008103508140e1800003809901880382e03d400510840703000b400d0082410b01d141d52801c3c41140d0650000030600500a03040c0200c000007031060240300055846911056607d00c0501c000404171442c1070742a51045080c8010702043d61030100c0c01c0c0c4420b00f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 370999559 1250 370998309 370998317
    0x1020f0a1e050f15010303030b030a030c03050a030209060c0609010c18060509130e011d07060e1323010504150e0f09210904050c0306130e01151706160f 67
    0x9220704005003403005000740c8031810f00034044e0425102041e4410641603d1107078404000c030342e8040d410305640707202d951402004610003009a2000c04d0203040501030401c010700c1c025140c0000c00c0701090464111002c407400c2540b03c1e400b440594002030244c00f41c00402450003038200c02a001c140207241e0b0140c42040c0510900247d402c4154030b0751400240d60201e101c1702070103c595103101c0c0d0b80c004c0640046040600841483c0c031850032401251820488100d5912188519100800c0020b4046142d0041e00304035552070004511f06200801c00b40f2003218558500c5c2c2e99851b040030b11040da00e444503801c540380044e03401070042600408004d60484240703403031302d8082c0e0740d141d5040d803901080e406c1161400c0c080380d0744210341004850041001e080180d40c01c3c040764450300712412850101307461450380900d00c44c054204008403030b407042c030081e0f09183c00401c2c0300c1010203003032200b03060540080c48248441d166481011004103c050303082280f02e1244284035000001c010441ea1261114030300f08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 371000809 1250 370999559 370999613
    0x1003091406101701020d020705060405010501091a0f0f040603051f0b1e010e130603170703210207060c03051f230316091401080606010801060305040501021c0b01020f0a 74
    0xf0b00d095054a000c104000000c540d50112810125981c030803c8408881c41d41c01d000c008144e0111a004010b440210076104103c0001e0484c1040700a0041d03401150304104040750400d0b00c1d94840c09071310015030049000d000030115200c956086a140404001b00c0e2070305080a83e802ca8482c1c1072900b07605510150002041e1b40c1e0f001c0121081c0c064216100d43c0000007002e510154030342540000304882c403a41000200318040a11259607001c0c040300030300441c40c0241c0c1c4a503a6421094500c01c100ca140b0300062070b0200e0b42d43c0d00310807038260601640002e0741d40e4081015650b40100741c182c51b007602c014100600707864980707a00d801d114a5808001d051148200c420296141088041d0f0100e4038800d14030300d00d68507400c2c1c40c2d000b04410350221240e24200e000001e066040821078500410301a95918203ea08051080d0040c0038003a000301c0b0259070811060202e441c020317000712841d14980301c0c00b0030041400d000080c07521214844000c100e03002680c004c40015400300701018400b5422050b00d02c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 371002059 1250 371000809 371000849
    0xe101508061903050d1d0a0e18010504030206191a010509061303080d060f08100207080412120f020c0108061002190303020d05070302090d1b05100309140610 69
    0xb40b04030100c40000310070039080441081400b240c0503840e180c0c2036a400c900040007964000440d0380e1000940d41103140c4200500840810340903c590242d9840034105025000c2c600650031600c045405400581040082c080049805c00701c11041c9420298140b0513040220442c0b9954110860f000c1e0500c003001407603681d1920740c6400d03a00c80600d40d2020b10345c0541c2d42c0c240074045a0100921802d03642c50014003007164401010000d0580303000070000d080b240300c000d6040c0000d50210501303898004040c000028200d10084440e2401846003081050300044810050030605041c10510150f40291809a980b640d22245484c1e00000845203980c0440246105a0400303001c00c00003622020362001178000d05170160000d1a000a14100130011562000c0317003181207000c1ca03550300e58841e0003500404081000c240807080550b90340c0c0c80344408603503520300081101038034400c0d00002c40d884082e02c1c014480242a60303442102002d014185910b08071412804980c0705010360118070103100c09d8601 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 371003309 1250 371002059 371002069
    0xb07030b180403020705060a0206060f030f0a030309150f0209010e03011802010503060402040b0406080702070f031109090c061809060a03031707020c03100915140a02071a0406060e10150806 83
    0x30046c000508019a40d07031010304000d4459200715000b5005d0703d0460941101402c00098600004100c0f0000e804a42d41680e07080740500005001655000c3d130201400c440c0300310314814200c8003800b0300001640c6410703c2d40058000750907050418420f0f490700010100c0d880d9043e001040b050340c2442c18035a296107040c0014028055a0040d02c210325000c134004c0b800740d03002407a09018000c2c68086a00c0306580d01000920700e0601c1c0001098203a40340540c10701403d100741c400c2d800203038041c1943c88c141c40c1c000110707205410580010b5000004011801c8850805100341a00210255140c0c101d550542c1c5001e0201c1c0158084480180c07144000140514400d1104641d803403001810b0310900c0a400b0a250302502c0111030543c3e0703050b21101e154002c046180314408203000e408403810010764620032118000d400442040c0c4481c00443e201c10140100071541c18480c0c2d20484001800a05182401003140c200504008805401020600031603001e540701d45e0072400c13940ba00188540c2c42402250f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 371004559 1250 371003309 371003323
    0x30712140f071a031501050703030902030f03040501110109050d0c02011b050606040516120b031212010e0f010b0702270703091716141213030b07030b18040302 70
    0x21a030140c8505060020008150b8008032038034002540400a2210010f0348240f0090720500d24010142848190b0765000300050030180707009040020314861140c010906002c40b2044041c2e00e9040020144400e40c1c0114140300d030a2000380003042100c600740c1d81e56940700d07128100c00007803000750002d00046a02c5140024800545420500000310319480c02984d9548280c6402c2d2185040c080061502c5d0712200102c2180c03640d40d035461000b0b40c080c0718800700038a030004130646c050054820741101b03a84000c009052581042200c45e200e1b6261411030088868068a10700b15142000010402c080c0715a0956000c2501100c1d01d1030410200c4a03403604882002c00ca04c0d501064080400c0100c6401d0351100b04690b01585802030000d80c0b40070303800454801d400d18400710408000300e80e40855110164240c800c4003240844261400c1070b41290480e400000e600e07c00d4404e40c410078030411014010031a0000c1403801d040c00a100900c001030380751a024203554524801080002d02418400c100c08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 371005809 1250 371004559 371004593
    0x1150f0909180530030906040b09031911010e03041a090d060903030c080a050106090b18150d0b060a080f060d0204020a181706040318150804060f0b030712 68
    0x31204800028070401c0782001d003091380503000c0c800c042441c440e000f0920032248120103620261180c4d9a4a550382e0058100240c2884a24801482107020700d00940600d074040348880c1e141d010b071050711686180d084d90b20b0f01024010350340050204011030b0050404080400e4000c8103015151400d80000c201e40811088001d000142022290350515816070711141e5001c0040e9142106951481130500a4900c00e02c100390004110707c1040000b040d940004d0051410b820050700c00c0c00303200000045d00700c0101d28a00f4a0003a002440785200080e43c400d0081e240026600385081103032020700a816040001c00c0d00050f000000700141241c1c0d508868050300c1c607401003045407640901340004101c012042d020868140d1002130104a20381c2c1c500000f0307a00c43c42a4001e0006075610343d0b0480c0d2541d00f00500231000e60300c41c4000b00b0324220141100301d440440b0340d100107030f91906062805c10348171410a0260740c0c500d4000304402e070352004078240d000d40342c0c5202c403c2d43d03201c110f152400d405003100d800c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 371007059 1250 371005809 371005813
    0x312130b180a060e130501081902040b09041b150c030e01030e010c050301080d02011109010e1c06140606030615030c090d08030108060c0307270302130501150f09091805 74
    0x800b0035429009120300c424200d044d62150a005c24851107a01107030130038040c0848540c0b003070448580b01c5c0401031356811024030242c00070a11450001c0820700361001554215600c1c80b01c0728104010492008243e8000c005401e4222104031160901628002800307202508001528960b540390b030340207800144150381c041000700320b02914140b0003000e030b801c00c0c09800e560340035240d4200310261050003240d101c038200c072110074540380300f030001503a100d9020302c031180d040700300ca095041e09001c40d2009490840d000780004600d5404510710420303a008000c01c03d40c45a00d0174020300000e40c407812071214068640d100f031103550341c0350103113004024000d00c034089600c41c00044040040000c03a0002c1c604942d544000c440c82901c0d08041744400d40812914a00090005281c0c1500320400020300b800d010030321100d0280e9161641c0105007071481071482041e507247c541c0d00400248442000c6101d0110340e611f000c1e02602030f40d0070010001d00302c80c4500036610b51209003204a080c2282e030b060b201d080c6e0003c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 371008309 1250 371007059 371007079
    0x90c120a02030708070203130b0307092d1a0d1805060f04021009142812051c080411060403080d02120121030e0f06040e0a0506010c210c02030f0c0312130b18 69
    0x24022080c81c5685556a503a900543c0000343d560b0b23b25528000302c02000c1d8400c0c10041c0340c070f109400912038150f021035100941d0f0121004540d081c0401d5010f50f001c0c031030b103102a15060040c06480d11540054608124051f1020070031003039060411048081d00301c500c0c0e82ca4150305102d44141d000a24500e00c05065000e6001550503200c0f201080c00038824402e41c0d50341e403e01c100c0c54440340a000b4890011509000c0044c002582000920341c504c0b80007041941091b40703e0700c0781030781c6421040602080a50000c0c454025600505c0f1160040061800911140b285641d0300361501e0b441510080034000c442180c003035199a64134000f140403001610080d2110755620030310160f200d0540c0d003092401e11b007001060702544501280b6204075040102240d1220703103040314000300030b0303030b90190303c10001c0d14440c54006a9050000c0e034402210b602c010140d114006040500300402140c0d1030191800c10400c02d1880000c512441046440d004112604c49110f41450040218411130b801c1e80000034103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 371009559 1250 371008309 371008349
    0xf06031b0e0a0501060e060c03190503061804050c0d1118011e050604140d0f1230090305040801020c072c06090c120a02030708070203130b030709 64
    0x2040e01000c4514811101d800d540741d600d082e030101d800c02e000b4000010080d050b1070711241811001400e011042000300da00d80300083d550301e4141070007048461300040c00001805821b02d422100001c0307490714200c040300141400d81d240b564540048080a00450543e01900e05004c00b41d500c80c04a4080503003505480420319140208080c002d014802e207241c000c2d0b0085a0429072050f1341c0c81076170006080c0070310703007400c0072118403401e1889030460390b01228240d001070000d00e40030760034050184180b14a1051a031030600140040c0101c59403400849403281038081001000319500000419800c030000d01d001da1414115028803403608540b10960001603219a801c90000303040f41103c0441c0c0042490410440000401e000c0c800200c00d2002c41e640042a4285822540940c01509072502185031145066103000d03810000c46140d890903501000b0441e40a0300920f03038991000d090700c040d520b0001e406070304400b01241030041d140c0b4003001000055034035001b40e4281c405030440f070b0482c4c0d0220000d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 371010809 1250 371009559 371009603
    0x4180215032208041206020c0d0309140c0a090209030a1a1b09011d130903081b040503030409050a1103090d0f0207060219020d0206221401050307030f0603 68
    0x1542e0700048804280119030420300c04400e004040c59002229616103407820710f5103940d80403a5481920090350800c10740c1c020301020002e900740116070b030710701041c1d140481c2042d0302c041c42d080c0783d040c1050700f00c0104130801d6a0b401907240305441c0c1040740140c070740a220f80400d28184203504010a6409580f519107584011124904d114840504078020500e941e170303040c2000d1b8010304000d90301003842000040b40b4010000c1c07011050310b4024008101c910904440407064a62001e025800714100c9418002441c000103c05050b088009007043c2c030381450400803c1d83d9101c0d0340b040e8007080d65a036022411134105504940407854030101c1c440c1d05c0f4182600300a07120391004d02d030600899100140c40800034000f0401d28121201c98001d4400706440010202c80600b104004030380c008000a60400144c0d00e11018015039000d05010300031001c0ca4191110035061a40c03c0110348040703032808521103070f900204583d403046c2c5600e004103a010b810740181b0042c0c18a47c02c01050020614102d54800043c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 371012059 1250 371010809 371010811
    0x2904060911091201141f060306030b04020906040e1915020405010509090a1104090c020c091012050f0a2102011107080706090b0a02031b0c06041707060606030203040606060f08060418021503 83
    0xf06c207451209689000c00d0303080762200d11008140780584d00003d0054640700001c00c0c0d000c0c10280000c0f5490413480710250400b04205101500b52810503800014820440990481d070410a50118941400c02001800d24000c00d01e80d244034210400000b0204802038101103840c100306149940c48079201d814900c0a0008196004014803e980c4100e0180c50010301007802001c0c0c440c1d50684841c1881441c651a1459113400ea8070b500c200c43d0858090441007141d80c903140c0c06002603c0c40741c4c030390584e54100202c03c92010011a0705120007100c1c06d071448000c031410150b0120106640d0b256903d800000742c03030ba501d0054a403070001003c000c0705070040c0c3c00a6100e40b01040c10610a16201c0340791210501413090640e03211352003e00010001550022448080314180e20414204649995040300b66001a00b185000035004018007042184031b009200280c003030b80c1080c510720340080000030400d000c0140100d100719240c0341014840c40c60030314181003a64001d401482c0c041401d18000c1c4041d44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 371013309 1250 371012059 371012101
    0x102040617060904060b0a0b0d060f0e07020d21090302070303030510080c150912160902070803060925020309090a090f060f290406091109120114 64
    0x440c0605500e4000703580250a4400c2c01c0003000d0b02d056880da41c449400801240300000d07041400048086294170071f01028012031210200003103925030805185c01304d600720b40d03880b840b0380910880500c925940c0214207001c08512500e0180e100c10f82c45100011b0f45100c01c0c4403203140610300f4000754141036000c56010141c0c2e0007034a0501850310b9080381d9000c042c0c154402c07081ea94202d043c04046c5450b00f00390f045c0c100c50070f4034070b41401c00185600160b144115120380340100d92003506039404007001a5803000c01082d000070118102000c40e00c80b00c00d17a200040245215044110003c1c1c14103e040000c95403441007020006e120689100008e5134a40c0001140b52260781c2d5000001c400c0610360040099140e40300440c9800c107401a0f4400019040320003c0da1142030f10f60003200000e0601060005120030310043c00c8400c8203801c014441110219001801654248805901c0b00007003082101d114100545900340303010707080005240140200a849030071400520148194240c8040c03038041014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 371014559 1250 371013309 371013317
    0x9010c2a0e070203070b0604090b1303080901020f031609030c09020a020f1207080a030b0303030a091416150309080307050310060302070213050405030d092108090c041d030c01020406 80
    0x5480c1d240c03200414004850303180059004100010000b5a86905140c012202030300201e01900d00f070342c458200d024101d070b0410032000701d007540c8018941d002c00d0903074212201e030300218a45511403000c403400b4803008001642c25100b905101c986075214201e820000e540000c11759034500e4035241d42d800a5400102d100005104012081c00d80160208508862107000d9031501d141c1003203030340c510520741c104070190020b265680d04900c145890900085114100306070000034485207034039002940d414180b2204100341e006030b501030a062816086102958004995a40c50141807401140a00301e03984004040c2c040200910511541181c05940a40221213210104540f1024114100e004200b000781d40585c1100c03a10425200952109030414000c0c0c0030340e0f2908411006501c29035402d040e0868168000000302c03840c8003c1071010b145d80b002e940ca00744401e41081c0000a580c0c0c2050000f507449140c0e108508072982c161000c0f0318050080c55400d490f1903454902032a4001d4210748103a10101e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 371015809 1250 371014559 371014643
    0x30b030c0a0803071e060609060918020306010303110a0804091a060c060112230703030908011401051002030c1c180503030a0c0305041206051506070503070809010c 72
    0x180703480d01240054681e5a40190709100c86034881d03442c0150030300e100b900c0309141001e28401055290142c0c0014006c80d00740820382920304440071046075102c00300300e50740c2000d400021006036400b107441030440e60076103407003c800d000740164181004200c00000f0000b441c001030000d8800090340058081486094491142c00c3c256410310003188140d050110080c0c00c0440140048802220464084c502981e03492402d1120941516682f0000104d002055404041c04004051348811030710701810028000388880d0b0040340800400d2103060003a00d02c100f1040f105076034140d10820990b601c000d0100d04540b414100c20074081101001011060009964115568101c1c0c0b802016a0200c4034098011443c00061106c110341c5640b140004500304002008001004040c00040c060064016440011035041c241f0000500c0301c1120038480c003505051004401194020054071880e5810070b102507515502180122006601035000500441c0f08201014074100e005402035840f0f8024a42d0600d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 371017059 1250 371015809 371015833
    0x60e01050f030303090d030c05120f090c1009050411090d0c030506070201091703060d0b010801292b0b13020910030b0a0c0207150f020d080402010503061c060c030b03 73
    0x40e888103c5c1e03110525030182d01110292440390f84084100445450039a003890f95020a94940d00300039104001c1e08a210401c0c44010541400041c8001c181190714003000f540300710300a4008000c80c840c00d0320840d60b50301140c40c80c469000454400e80310080c81c01041c40310a2422414800290005440602c1400001410f51303005201d00c164441c0c111054074000301c0046d140307000710782c0010080340c1c0140c003240c081000109060403a50180011034004a00711018120950b0aa81108079521101c0d09017440240c2d42d46a40a2001c080794505020318903c04101c0051000c800e4000b800520740f0381e5880800c0700c4002c51300da00300d1540e80700300c400c0c000c603860b024a010006107090001421042116010401c03082e00c2d940080d00c50324036401a99252680e42420f030300c1080046030010041044580181c4080d5810f0001c41100c00960030300300e200b4105500003c01c54000107240500800b2807103509903041c41c04000601586900801c20321851001c228000d014100042d820f40c00788c441d00300c102c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 371018309 1250 371017059 371017063
    0xc1a0408060105220501240c0b060907050403080d09063801121a0a0e011208070305040b1c050615030f150d0c0e0c03040201020a14010609060e01050f03 67
    0x8590341040245426420502000710750b4000c401964a401004164078044941a001d200d00030221910544002c1000956403421161510491303006c105400002e00c0c00103242201c1e440c0c100c6e80c04c1c0c0e2003041a68030b11005560354842c2d074101820209000c030300141400300a410440000b8070035407050001c881c2117081d41c00f61400a0b90150300e0480501001032116018042c103081c03c0005240901150322104c05020881e5007080401522403020740281c00c00342001c1c13841800500010090a4540d0701d01203501c6a6445000300c010003108001600c50300741341c81081590050545401b80d80e903604040e0300f420148a10b0119800c41440c14200010454940503c10403450480181820b01d10b65131641c604201c034000903d0130580703030740d40011000d658650111040c41a441750701c80c0c0e0a100d041803612944044010300501102c0f41c20410040140d90209002040079880856101102c11103007a140c09000d0b641c00c003400701842c100b00055035180b0403486904951050303566142d0065042c003415 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 371019559 1250 371018309 371018317
    0x8120c0d0905060d240306091707020108010b0c01110a031b0206100302010e03010f0e060a0b040c0507150f020d200f040e070e03120c0c090714090f030304030c1a 71
    0x6a4811402d10004218515541049001d00c180c01200c1c004006104030303c07590401c172508151400d5079189218410401081c000c4064160009805420001030380d000a250707104c14000e0f02c00190700460902c5914400b508030080c00c0008030003054590304e41001c02402413b01c800720708081d1002c1749403030707414a0000c40c602d40100c1d01c82c0000d68180f411600190741500c070b0000016003643d039851000142c006984240c0126680b01c0b000b0305200d0818a092100342c50500701c00c180b29a01d80303560005c8554100c0203d80700941d0050681183c0c01c0198138290060a1038203a00d1501e81c00081c14414400c001d038003c0c000e0300c4903440c00d030341298126002010903025241c540a16030307104001c10f01c54540c8442503140e2110151400040c90182c00c03012a0901074000c0d0480004a40401d921151500a1010720701106040d651074440d8500503030001c0401c810001c1313040030182c0015030a00d141d2254101a41e03195006002c686e5074035a6490031050407038017886481c80c40740541e8020305040d47c41008503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 371020809 1250 371019559 371019569
    0x209220213050f1b0406050a170c0a080c090d12110714010210020f16080412080409110a0e1e031218152203020d0506010f151706060408120c0d09 64
    0x13600340740c1880c1c000c2c1d4081d804600a40284116500c5c03140200041c1038000b803050803c1000242c6428103084050b1a01c100039080005204061100d0511a00d441859089090b004100480240e25490742550355030001d05002c0035070b0207a00d4010034064034681c540c1040985c2a0f0854550300000d14010040340500212038480b90740c10015412201c880044030316079035026040301c03441c2547e100c1a041011611400c1141c0c4d40c1d07800b0404011b00c8010744101006074900026242c42e0041080c00100200e092010b100d102c4e65a0300c40d40da001c1c03102e0504200c560743c8003800701d90b0107080c4280c003442e1642010a00501d03060919070f201c6c425007402284512210612012030381460180400b010001c40c0342503030768080722080a0000056030300d1840345c5602138090f101030142541010101800001c00b9004903000d40442c6c1e03810440194424044613240c1100034480405271030300d10000e031440c4030710b92041000c2e00c94201034010104424005000c003030707824411240c0c03200d03020005a1360000f40e4410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 371022059 1250 371020809 371020861
    0x7230d1e080c091813060605010302040e0601121d060f060d0201020a030809100908070308010501030213050d05030408121801020601051809070b0d0f060b070209220213050f 76
    0x41180c00c65090060208500d005014141010000d00c1300d08068000310388060030f007000100500b0502c9130510810b4054402071134150310349401d040b03d90035030302400f03445c241c100a240144250b924150f03500141c0d9406102c0e40010f8200d4004004940d244070583d003502d0804100c0e4041041854035521400d00e851f8181c0103020b04182d16201170b107400c2030083c00325000740030780300c0d401c0408802e41c0314603c545072050480320b844481c141001018130b00d050700080e040c58810400e02003035211010269048900c1100e6024800307820f0b14103d03046000f03a601c14290351250707900c039007154a0018042c003015002c900c1c03400c0321032400c0c5004984d030f45400e00c02d258014004a548100c205111441c695109403100c0469215645c0c0700e003a01034540c00341800b404407a40d41c00805604044038001d100082201320b04540c01c01e6681d0300011041d441c0941890303045890040308600300040c50290558144d0000d09041e8000041003840000d0700e01100c0010401b1100d01c0003800a01c0d013048048030654401e18 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 371023309 1250 371022059 371022061
    0x31206060a0804080a0201090b01030c0e0a0522020402070b0c030f16050a0c0501090c031203140903180a031e11041505100c1b0918050d0507230d1e08 66
    0x50b413503155440b04a03100115522a007488000ca00e50b20f03a42c600a511402030215140e1074a4140b50079824098000d640107800c00042c8404501d400070303080e1480044041003c0100250f1001500030320a550740200211011b5080051760b106600140d03120b00c00035000c4904651312100140c0000341000c01010214030180a0360329a02d03c02c05206d0324039889a000060900d104d40c640741c4800f89968002c81341d0507480d080d0211a254140201403c04203850604001414046020340e01c0e4028898071200c4400d01d503a940016170f8901100c0f60045411000480700f09400031072140020b54050810303600149450094049407e0911800da618240b800e4030080d0142040304024055081c400e107101007210341d10642d0045996551001102000c0c1828400550b140616050954002d441c000014104c010850004640c0c0424003540ba2180d0b03140c840d903103003030501c0d18a0045000c40d5183d0707404800c3c643c100c0443c4100041702103004c203c5840711036901c58410400c2c040c0144c4000d10382c0001da443d80c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 371024559 1250 371023309 371023313
    0x5010801061d041b030b15011209050312040c0b040b0703020c10201f140906012409090204031b0509160c0f0212070e07020d0e0906041d031206060a0804 67
    0x84c502099034101d1011002c0001d9603500c1e0b0400384601076132074940c60250108059490b613040724800e42c10f030500c01030034041d0641548400703440340122880c0282580d81305002a0410402042c0781c4080e2501d0f0814a1320745888134840307038082d00403c1c003ca025100c2c601100c505d902d01032012a0001d0243e0f510b4114080711070783c02c0c0d040e44a441640300d89a04c2054454100a00005c0d0340100344010701400142030b074000e500d41c48082101500c42d6260b500a1401400340c103654049450b0048100d4003c0c80309030040380300031141031529a0003204440d00c049070110030807088000220001c0d0000240043c180c0d160001c000000c141603420503408030300046482150b074001c0ca601d11300c86003d0700c1c02080008440d0045142c070f89903c50b00002d1608191011b00058040318030391030304010360340f00401c1c0e121801030000e0100140703800000d12800801000a199948075000000c0b00000b04550031301960319608503e90b40d8004075803102088903050001001c03800e00900fa507402000c00c0e500c0d84c499468035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 371025809 1250 371024559 371024573
    0x6030a09050a06230a0b0105090108040309030506010b030106170702100e0a02180117010b2d0415050102210406050912010507020307150c020a080f041805010801061d04 74
    0x3440d0212014041e0812040104000e4840c52000da5140030720255403110055188071040c0d80104120040c51a20b455148182d9000041c1d54000100b800e1120140d242d60505890003015503000400720710035500045040201c48028504171074558442c02220321007040500203030310302104c8600050f88038240c0e0004039901500114143c1503044103031800c0c00d0b0582c0101c1c3d6201d10807031446c0307130350b03409013004004c039100303039101000442c032030354000c004651701d440028006181d1034849659880030b031807485445600340c95403039107442e4004208020484a8404002840000d44200c80c0940180c010700480d00303031020181002c2407588011240350a0800e00e040e103a80e0001d00c00c190f0044042a8081c45010092241500402d02c907002113459031024a40b16174603900d21030444003654141100003140c00d0b00000d000d00304691200c540b58480c82c05400f03041c468001c0e43c0c0004440d010301c42c10040360b420207a11281c1a01d0b2400000d207c16901c880076541c60703c1e403400e00c2e0410240c0100000340400c0700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 371027059 1250 371025809 371025821
    0x90f1e060d0209040e01060303020c01020d0828090f0b06010f05031f1a0301080c040e1c1101020d0617030c0d18090e010c09050f030c060f04030f0f1401050606030a 72
    0x5041e40c018103120101002c60110b0f0000d1460840c180c0d03440e94280300b407540400101c0c1c2c544000344002d0107806482040184095001350181829400340401001c2c500c110b0078001051420f071400400044490f800c11440480c049001030311450560700220b9225441881245240110b5403505407031529289100107640301c04080c1d6401da00340b84080840c030480140034007100c1d031070301c000d43c43d44950400004500f002c900b480c842d8071407450100030301a4910b0209103081c0322442d2032100c0042c0a520740054032540c840302d026080a510003c3e040c0100d1425610400a5541d420044164400200f041d242d6078410004d1a200c6a0720078540c104401784202aa0480c90011010210f0950b0755130082d0400d48072448000c4a5694440314039100140d80002e95600030001101c281c058400c41c0002700c3d0304c900b2040920741c00f5520006d5240f16080340c4d00e0444000316841187c8828140c0a03080c01c140b01c800313a0b4070844007003800c0c0108584200050241c10301461008212502e0364481010361001044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 371028309 1250 371027059 371027077
    0x200406170a0b100b040e0108010c0302071709031f0c1b02180408040506120f070207230609150702010216032316080106090f06030b01050402071406010902090f1e06 72
    0x35032100f022515400e40c1000e030008001c10f5280c0707019541004080350a4803044040041003500c10f000d4003003c922405a9107801c1610300700d10559072a00c0d0004682040c41c80c0302c14041d001c1c4594002c581d11012907002c984484119900e5080d880750500100c0340c60b240807040690300003002c00641c0310036202c8100c9190030070301c1001d0301071074199610081000c9400550a44180312040740070000c10040d14800305030301200500c0913003000c908210840d001d20300c0500030801c0800706180742440f036403a81e0046030580d140c0100140c4041804040d400407a602401d0202d0060049102c482d1003800308100c01401d80e0b5100107240c100c50f198030424024905107141d184140e10071019410000c1d030403094010040c22181c000414218100362036001a43c0341002e101c10800d18002c001c00208811703464441c1910422038015a5400c0c0900340a4552892510300126500a4400005600b030b0785a004141e0180c041c0c0d038514021402310100400c18a00b8001c0201d02002000c224821b1300d0700034018144c0030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 371029559 1250 371028309 371028331
    0x90506011e0206060406080c031018051e0106060516030e01050f130e06032a060913060f0504060521071a0306040f0509030d020a0c200406170a0b 64
    0x207036940c11004004210300300c0500260300a8410300c492400d184c020318020b00a6200100702e403901080100f030303840d821f00701e144000554684805020450507a010308c1201d40000846405960b504030300300c1550640043c0c81c400e5841d007040055410300480540341c046041079404d090280c526201510700000341c099041c100714040001004118400001e4054080340a281c0a10141000c0714281d88050241041d88a41e011401e034042242810010030680e50440c00d6611020350002d010584600500300d003079600507650012041003421541c408002c40301502542c006041d1f035030050000303e461502950340c05c44005100c01164104034546130795035074103050850324019501c10301c040303088500c41c0a0b4504400e00005011030340c81d25010318108840c88840c1007295040c103107007481ea80e2160700340d40c1c0e000c1a00818461341e07050190742c07210241e54000802c055210511070410641c180100108c41c80381c0c3ca409000301d1640c1402107103151a0890b4001050070800e40c1e03c4e99204100c0c020410032540c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 371030809 1250 371029559 371029577
    0x30f030a05120a0504410a1130161d13020105191e0c0201020f0606100c06090b1306180c090e1009060507170609010b0c100e030904060b03010302090109050601 70
    0x281c80312034001c0240703805640251207013807102e00d021a076071940415541d10075581030880c130003851411200d50203227100c9001d07600e02094103103d00302e05195003800004041030600d800090001e1b04000101550032800000f900503942e180501078110000f9007001c0d0000c1e1061120b200e15902a1303c4a0350140c0d1a400d10b62082d80844c0c0e404405010030000f40d1000130200740246d411035804021111400c031002001c1d051615020020403e19521480f0a104100c00030401005105490b44540016274002664500b540f6210721070b0802d003401114221055071400c01c5030070140300d4280c54680c40550007c8a40c07100d0f4900412070740a440094503008a6001d03140f42004400600e01c00c98040324403608000c40d0500e41030384040c000b81805000780c600345161000b040125034807032a502d4150341d0a290001c2e15500442d0100e40f030300c2c1d00000c104450301d1800716040004c800020152203206401c980038080541c80300e00c00c00b140c1c0400e12009400c4000070005000e094125009207610400602d052194 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 371032059 1250 371030809 371030903
    0x81b01020c0a0305031309181719020606011205040512031e190501050306040f0611090306090a0b07050a0c02100507020306041a010b0412060902030f030a05120a0504 73
    0x40d602d2a44101e0350b0350310004081081c02403a50000c0007c20721050104000f4403102c45a4180c1103250030000c00800001841120b8108124161200c038408a04042006a07036202d0195a429060305c1090210381c40c400010320381103c3d4004c0c9407180d940203014081c483d403848403180310341e0005030411300e40000d10600c51080200c000384d0320780f0550003118150f095918480c400c4c0104e51068000e280645c11800c00c00000c00c4040e00c142c0c02041d84103074002820594911032071014002c482c0035071b505008100900014a90003da14414540a504910080c0e103480000b03070f5252041c1070761070011804425003c005032502c0350400ba42142da40c14610b24217501940020b0501004581c1180c8000040280f01d000c0c1401c024094058411125081d1402e0305140d00b203181000b416000034032458032020103a045440a000810039124207000300e03622010780700c1015010b5001000c452002a03020300002c3c074800e43d140180d5000e5034102002003403040443c001442413201c14001d4a100242003441401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 371033309 1250 371032059 371032069
    0x20c190c05060f090405060609090103120504050a090504110108010f0b1e04060503010603060503070e0408071704090911040c050901050d110a0c1407050f0d020a0509090609070807081b01020c 84
    0x40486400c0f10580d903c0940504002c00c0b514040c007154007400c41030111a90b5a1144032940c0c1c11340b9000b41c82d40c0041040514112080e2003540c000a0f084485e02c600000e44c660a40c121500642c400c0810040540218004481c0c0c0c071002d00c50511840302c81a020480140d40e4070003031a84854101c0040c510070302c9440308900da13034019400400018000801007140740e615101d0321000c0c00301100540411883c0100d1000001800350006c0e1041000049035010480d04150840240e0014100b00380c60326a13619031100188042a0292244046c3c61401c5c1c03290300d01072103038041d142d00c144c5800307042c150325000440e03064011440c40c841456076070b0034032030344250540090300808041d41e4500d05401400c0c5014070b44a20901c548000c141c3c441041404039a0b00d000c5010685042a14440b000303035840e0000603080354140e03102d19044050070302401f4024502042451194075040204d4011a640d40c10031070b500c5030315214495140c2c001c6560b084100070381403800e6080c001c0c1441221803400d080c100284c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 371034559 1250 371033309 371033317
    0x2070807050a140115150c05010501060f0e030102071707020310050c0d0e0c01020c011202070c0e0105120d0c0201121418010c090506040902070501201c020c190c0506 73
    0x3488640c440900c0b4401c20003080d05030b20303d4404641c024010094403414141c403011150041d0002400514040e100c481d22806c1072080c8150480000d1207217581d40c500250903c00741b00c0e50074001035141d1b40c2c0c1800c5410305000702d510042c0e1203a240103480ba142c900400315070304140000ca03418080c40c13504c5000300742c0324000d69000b1032500c20260f60344c6107100020302c22136180c104454059084032000034144e0b82c01007400d116504080c00e00900382058016844001d10414070010305000150310046000940d4a03c4c0505807032094880c1a14036640b50b030b169940e40d5030f4603c0c080c00500218000401544242140c2c240309200100110740f030a03543c250a9007040c02100c010023801800c645861410600f4004d1307285011503814450b500900f040049071691180740500541c5580020300d4108220007580000001c03001da08540303481210341c800300d80507940080111b4000e040e0039409404200b02c64400c80d01420300e880010030071040c1034801e0442d002c18684090303c0e2003003d00c4002501e521240c0c024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 371035809 1250 371034559 371034563
    0x10c02030d0f08150918120c1b0303040b0301060e150a2d0207030305180910090c03050c120a1e141005100503151801052409010c0602070807 62
    0x1604040b4440340d80240604402048820454504041c0400d2500c0d58224607401111486280c030035000541d269610740085c102501c11043c8000840c03a6039081d000c80c0918445041a400000600c080400c050f500d0040b401030741c814082c100300400c021030081d41c01c451396510141c484c00d00d030203815480d403101d6005404401d000c1100c40380013034034085c440c003804c60100003045100c0c910b80b004040c0080d600e1a00780802802d000001a0040b086800850020404603000300501400d01d04802e03e00365108040c0301c2c0e010440d003040403078144140a030064500c07403000c80305c18508002c039101180c080c428001d82030031b40a5541d8071a85030366902550240041c40540d41d008120342040c142020b0903100c000701220b081001c110000d200c0c0d07548200a0000c601d040d468565125180c0d600500b003440d1141ca200c503440041ca41181d4030700c005031a043e504031002102e10300c2c025040c14032581640244515a01e030b4002080000c0070040d8010b40d8040c1d2464001c071030050800800d03a80d10300c240e0f03000200c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 371037059 1250 371035809 371035817
    0x60e0406050a23070f0917030c070807051e04380904020f040903110d080709080a0312150906090f0e0307113607030b0f090105040b010c02030d 63
    0x200501c001d203501400d030000910b01c24019a0701c00450070307403c40200140c000c03000c02c0089000d0034020b0340304151140243c1025403444d25460080794807903a0304e030322154405003a4052410002000380c40071a40000725540682100f807000940114410042254038030f142d40180c6c2d40004101c41e035009000084c18481d00841e80c4000e10550300b62400c0c1c603140d000190f00c1445d0060403c40181c643c142d404800c000c050360085414603840c541502e203141300c104280c0d074501c25044540c0c83d02c0d600801d000d02030000394403500c2a0301d0b20385120540364008580094003065140108011049150388030148070000100c8083e002500c4404050070b81d00741c0e500c07210380583c9454a90454101c039106d007110b02d02c4003000640c54228141d403004142007003801315a05c9503a840074800014500d0300c0300b00c5120b1140500300e00052201c059618120402522040002032501108904605000d040c00054404c0280b0000c59a840c040412010300348402c405410000e0650b001001620100110340c40302080e611 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 371038309 1250 371037059 371037061
    0x20d0c0f0e0d020607060203040c0510020604030f0c0308060108091c030b031014010e041a0405030a02010b06090d060b060705011b0206061c021002010e07230d050705090a060e040605 80
    0x5007002030301c4000d28801c0c0300500d44000180d452100300c680d06a40000e015032240c2d02c504040d122007034180c0c0900d4000a03061804261154041503942c4a240b00e500d90045846400c10100c3c1c0c98080c0e540000d010503000c9000c10700070b60180c100c440d4030005903c212800c1038440e170a000c8038414020112004251244440c3c1041d243c10b00c04035402900c6841c0c10040098001110250750106118000040074900301080900c010b1071038001c00d200030320050368000c0c01c042c584946d8a84c8881c202c0030040d407900c040c0d410145015011a0801900181414110300c92a1940030080c04505145c0e0f0b4411801c22184c80060402e02030980400603071030940041c00c62401e0083d050000041a05105c0d100502c4600981458401d4043d401ca0b0191001c0600344007078403060f80102680c160b042030384e101da8000000c692080c80c21491420401c1c0e01c01001c2c00c0d525400703200824646103401003840d044101c3c24080e80c05c1961020754800d0800308040740c065500d113452042100203523001d40e00789440e04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 371039559 1250 371038309 371038337
    0x8030a080109050c04060f050c1f0b01140d02160203060103030906020d030219081e1005010306080105061309030210050f0105090105120c09060f03030c0a0204240612020d0c 76
    0x3500450040150000501080c6800d5281c03221074403990061405200c0050310202c9914407405c01d1321102c00226080f288480404000d010503441800003c584007410007041180c55480303030b00860b284403004219141032610025a21001c0e400404100051240d80003410b009a5410011b0340d000314000d40b41d0040d200e040c050000d041c90401c41041d0141070040200d800200c0c0c00e0f00e80b50301820060710307004405480d803800140c80a42405081c0c0a1054003409018841840141c13007401c0750340c03d8900b00700c00c550f40d03c1010f003030394011290140d000614541d6004d030390320650040c40d0484d02c41c0c811390310644102c002c0c5804481d01920048210002840140200d083c1445040e02402080710405a643c90006d01d441d5a0507501d41243e01954440e0042055600c030010307070280700303140141074a44880e12408910381c0d0b4040e03408264400c0b41884030340807502000015400003a0341500e6155002420843c0c00d0755140301c1050580a801e03820060816005803d1083c0b45441e02540c0d40d0350251100a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 371040809 1250 371039559 371039567
    0x180a0b130612062301120c09020304030306050a1202091f030f03121a0303030a0b010306080f0102030a0c050702150c0a141606030c050a0e040209041b110a08030601050c07030203010608030a 83
    0x441d04401c40b007401344405640c0c5603500c0c0103075030442e81310599125181ca0f50745070101c010b0030142c1c4404607170303400402800300300340e00b50300203030700703807a17042e070300f140e10301e81d03614580b401008075110060740010400d00410368164251082c001e48884118820030a140d882c0e940822108064405800290488401e6640d500442c0505108010505c80ba00030001c48140000d807280300c0580000d02a683d100701c140c1071a4029007058004000103820b960910303810b21041800303540304072066103c1600e0008440922030140040d9040c107034018190002d2030921505858860780400c1c18000b4500c61940c1103c00103850340d01880000611078050200c0b211071414180e4408440d4005005050400e00182412a0300c00140c0310301c0405172802d17551049102000c100203210354180d06400c01d041400300d200f120700340f071450400110165140b0262030b5400c000983c5070042030310700420400741000030444075071081025000c0d080c1c400c001c0c0c942041d940d0740003c2c00c55005038070002c0240c0000c10342c040a580c00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 371042059 1250 371040809 371040821
    0xf1b090e090703030e01050307020109050f01020d0605092205070b07080a020d0c0302101104150e090c1602060304060b120d030f0e07290a0309020f180a0b13061206 72
    0x20074020702030301c0e046641c040c00101075030603110b0400002000042c0218802d410450740982c00c0340540d0324645500c0032541c082d510114080e02e071301d42410070009e030f103062050b020307442101500c6540060b955801d150300344007051020256007511030480c02080c0f441d841c10042c03240b10f214222255071502c504102a08008011012900b400700380440500401e40104086640c0111404002100241e19901c28000e00481d000900300980d10401c0560564001c2d01c107070320120081741e44103107990302d01104140601c00c45a40c0460750288090710401824034a001d550418801d1002082a000000110341c00e20b41008a07101540d004211522140d500740c41004011080b1843c03e00c12691380f1190308ac0c2d03803070440c03140040c0c030b90008030100102c9514580f100c1c0c10140103201d0641e81c0075010801009400302d51400ea2007034041c02c15140c614504001c1c00e51103400c0d281c40b00c185554034200c00308010110030462a4020075004114040e620444c4110005460b42103110015a4803902b40031080b00c2c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 371043165 1106 371042059 371042071
    0x4030b090102040602060f100905060103021b07030606050a1d070201090209010306202b180302011505040c120e03300a02040f090f1b090e 61
    0x203010b40040046460036030072540d003920303440f148243c80b000c15920f00605040003035082004015640015510183c141001400d1000030200c1c6441c0c0146100300503031641001c03409004001651003200701921301a60250b00c540e051295034003c00d40d200080000c20f6a0303500008078003034400d401182c40c99a02030004c0d041940d4038501031015094170381908402c150b5006005148019460660706150700712514100510740102003580025104502402e00540b25a0700c8071404100380100b60044d48240d000294441b44c21489800e681d44c0341d04800d108900700302052082c3e070f6016084014083c0ca9502c001756000402518900c5c520070f0901840d40000d1090750464200000c0e41c0e4076410098030140c480e07160742d500c07400b031003248200d00400600d158890030038000ca5071305a0000301c1c440007c0000040030b80c0e52001240c406502031010307400040c580d90b400e1002c128000020380c1c08c00c1d = true := by decide +kernel

theorem cover : BRFrame.Cov 370863309 371043165 := by
  have h0 := BRFrame.cov_init 370863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 370863309 ≤ n) (h2 : n < 371043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
