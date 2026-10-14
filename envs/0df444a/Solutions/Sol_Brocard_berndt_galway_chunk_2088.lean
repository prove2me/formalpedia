-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2088
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:34.93546+00:00
-- url     : https://prove2.me/submissions/05546b98-4b06-4ee5-9ab1-20948bc98647

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 375359712 ≤ n < 375539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 375360962 1250 375359712 375359723
    0x60604061115040b1f0e18070f06050414030607200a0204050901090c0506070f021c0b07030c0210110f0d0b060c01020d0f0504110d03031d030306040b010804030503011a0f07 76
    0x620b420900d81c1c242c0c6841c0c0c0101c08495007940000d11040c00007000c95500a6034241f4591017882c000800c90346010040d802031040300d6a0000005040c0c2e402101801c251220348403141120b0410f4814503544280031249140022040040c00d1403e10322180350580010b1964140c80d00d0003039540100d01562800d03105614180e6440092205008440e223814001d0002205c04902d0441c480c0c484544a1030035650203481809175105401c20000c0c0301c104401c406a00c410420200e00d0110070103001000000a05405809800b408000c40e240034400c102d00d1040411220f400c00324441c00000058006100d044a083d58603242850241d4582002d0011020201d00260344c41004046400a0302c00c042c55103400c4c94242802c0c0400100c4100008818681c15208030420318014207080300581240051511141306c407115080b1001804002540304036010f42d424002e10990702c0044601034002c44001d00000d01c244014011645031901603c899800064103a0500080d022001540c1d070100008651 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 375362212 1250 375360962 375360983
    0x31806110c1905060901090c150215160e0603090d030b030c060c0601080c01180504020307030b09090703140607270506120103031101090507050f180106022406060406111504 76
    0xf00242000060350000707000e4000e01401c002071f600c000c4d01d01907034082c0301003101c04854071803500361003084124101312124102c01054103081d0041d1400f15100d2002000140c0075450041085c10030004880c0070342d513440010501040c4094007207005194240e1815814000c210600040742d480030040c150081080b400b8128551600d180240f03402d210424960600980c0031803841991000c5540000305c55044e1390140e680c0e6501502100149407140909501100110900c591107030001801c9040c1c900c6050380c00712254802c0842d40c0d0303401040b100c21f00010301c60340b80050b52615040b40c0440b8030001607050701d016030300e0303400181580d00544002c5d5021190500101300f072551016024540c0001c510003008504820b0700d646850700c081e8058940902d000307882d20042521801b1812800d0b17170000780c2049080d40c450b0ba0094803600c0410244500c0e40440c0c1c4014882c008021016000c0c00008124a180c030b4688003081e94800c404003402d1405015503c1859184400c0d241c00501c990700c640031200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 375363462 1250 375362212 375362263
    0x1e0f1c080406081f08030a050307022103090706021504060b19090c0905010e01020d0f0905210c010810150309050303151908030d0f0b030f1c031806110c 67
    0x502c6004c0c0e488541100308009604004c100d501000303c4a00c5d03281c030f181207503a80d40c1c1e04009a2403c1980d694161610304101b503240426503c0f6406503000d0040101603c4415a41d400201d80d100202003001da508800304010500107500f580c80001c1c000406050307103c15012481c5075200861081c1e0200010a8542000b402100d9000440e03c0250001342844203019010340f000035941c9440704011000d00800d07051a410090085404030004c0c400200300c100e49911707010556000c46c4942d4000c40c607612401650344855030003020920f11400310f10005008051400c90080c45141c0303016005000e1665805602c00840c070f007071005501c15400c00004419040740f036010300401b055558504003601c0311145050010070004021a20940250300d80400c103909040c450000500e0f01e246240e034144610032002c4101000820300b80d00900011a01ba028003803140025010342c0c0ea600d00b004268070b2913041030f5002407550781c080304005140c0d11300d450600e040c81d05094038012080c89008140f40c08180b058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 375364712 1250 375363462 375363481
    0x6032508010b0105041d06060904060807090f020702090703182f04060b04050402030402040e06090703061b0c0b0403020a060c0e091b0a05210708061e0f1c08040608 72
    0x4114091080c03030030620b018640a1205206043c20360b001b5074640e0032074045041d6603240320645603400e00085c8100103455072806075550300c8125100f006211414009500301a000354400d440485401400303007040c3d80d407000c030210b0080c204090880c0202007040c102c0d80200d41c080980e68924900b429081c800055200141d8640704000361407944124103080d81030103a5407415040c0c1d01200c405440158aa45851000602400d40e802c40220b403482500204102901d0018480080782e004d203004000441075252000302d495181032126010450101040c0006880c20400b42d034824041d1068450100580e036620742510014140c90000403865203100a1604c0d24000c05908901c10300342c000c540c01a20b0b00710401a00503802e203c418000c022828140c0070b9281012072040702112050000c241c60903180c090a495429503403a80200c440603d0f0314028036a902181a51030002427120042e50213010170004c66414002022424401420301900000c0c48200540060404da48480d540b03890960031a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 375365962 1250 375364712 375364721
    0x1051807170c090306090c130905030f0c010605121606080a0f09080a170105030c27090106030606150206010e13051b0405060a0609231009030c09140a02030603250801 73
    0x2a07446d150080c0245203690341c1c4440400340805242c40c1c01045c00c5040342031282c110b000b54000f14074000d600141d4a80240c0701940441c041e11000c0b00c04408030301c002c10036103070f5079092545d03110000c002030901030100500400c40203501401c10704002c0340314076031440500b00307039500c0302403c07070b01c2d08004100b00d0700c0e2a41010964802284034016143d6079850540002d03640c05c039210baa5030040c000765080d95540c0e9a43d68515245c408548203200c00c1d0305129942600900d01848141c81c154984072010420300040c3e01c09a03070310007140d070040280780d080ca5903584017400061f21129001203091180400500148151000131804401c1c00e10f020410906000503030741c000384003030f02c12810b0140c00d0180c0c0780c02020120903605010400212480c0c9528000580e58031b40c40e41135440401800c02c0459250702c44544020359114402c25480103a076803480c10290342c000c400d000314100c85980003481c4581c066000e554068401021212941c01480c00781420300420340310f040d50004804000e00000d1400d004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 375367212 1250 375365962 375365971
    0x7030f02070522050a0908041205070504022b0b030f07030b01050604120602030604061a090a080c030c12010908040f1502070302100c0302010e060c120a0501051807170c090306 77
    0x21000401e5074808400294610408003d0741410f94510201d070320300c100c0d5401400c40a6101140c1582c1c3c4da120080041015a0400c0c119402c2c450a600482d09083c54000e40f01c0008400204032107a6081204a249000740d046110903000c0c0e0780c1010103040d54013000075002c40e406400c0a4004c1d00e085091043d054081600081c0c080c101c10001007290310100304250020b180c0103800140c42e6280d06000038081c107400e5001401c81c203a0900e032043c14030741e02d40003010003581c11501c1000303e5030340c4c0c541c103501c42c0100741d20194540c00c8074503841076508020201031106062400000b410840710307501d000c9503411a40011640c0d0f403800b00c00b0701c012144007440d524140481d00081034058034545c001102401c2c4000c80008002c00b51080b1001c050007504142c8034481094142c40352490400c80710b04040d007007440207101140c5218040b1700003a18510070b090507160041c010301c0c0c06245103a00703010308881c06001c0070200b2000a080ba0410f1030502031a0f40118054030b900780d6140c1c02c050030585484030281 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 375368462 1250 375367212 375367219
    0xe060a0e01030e0106210311061e0a050609130503130b0403150e03091513090b03240117100c05070b070e0109050f01030209060c06010602012703051305030307030f020705 75
    0xc40c14821440e5405400a0784402105502e6441c401b628003102d0000035455105282d2180d082401072607280ca488002c0d00b289003011071030065450398542010340c2d1043d03c40da82c1004108c0003180503550005042d101e03050041c403c4910f00840102d50960b078044c0c03548802c0c100c10f400716040c01000000c3e50071103000300504a01344983e00a100e011601d038400c0b8441ca512130b0079103140c8501070620174001d0790a00d511003200040c0f001d5a03482c1c5903002d8281440f90034468040c0071801841c23001c80560020300c0010380c0301e810303103075a092040c1e22020002c0c0200394106407251349145041003916004500b58200700b503942c10344900081c81c00c0201c1c084050400d000303005440110851a0364064110300c1180e904075041121900c8020058000b445802551900040700003038202c90a000000e40718125101580204081c5100801c45038142002810006503085010300f01d1002c00d209a0240004010352500c048d0420354170000285035034004030049004c0348000076902c51064040c46004020030043e03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 375369712 1250 375368462 375368471
    0x6020c0306040c091a03010c091a0408031909030f0f02090a270206041511120405060a0c031b1209060905010e0d0f0b10140301110a0f0e060a0e01030e01 67
    0x1561565454000343c00f40380c0d03c0d82c3d80c0740e43c0030010400d404001c141c5c982d000b6008004107009018003c181c444140681140d181006410303142100000d0101c800b00c86155002d10304003003021541d80d00c001c4416400b541048201d15010010495850101640b5446421400d02e9120148188100c1080082c0400c02403032500358502d09504c508240190300a1005903002c00723035080e5100144190080d9048030b409032501d100c4500381f96810041148800c00c00500721211072481c1d000e510814030490185503005103043c80b0030410717540140c5542d00403a01c02c0c28a1808615041141d000b8100001ca0656005004002c0d1921303194002c51443d0142010386010504a401c000010304841070954005000c0c10700c0b0054402031101030442c044807154403d00d08011402c001c8100d1684041a0003103000e95400003481c3c80040c601440748100340160051031909144004074151007070984800704001303126071100c240740c040d901c0d480104003c802c07946681c810301042070001800c031410010051110781c9032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 375370962 1250 375369712 375369721
    0x50a0e120d11030714130e0a0c02070f08070e0a090816020f030601031e211e050720240d14040506180a0c120b0a05040b01031401140f0106020c0306 65
    0xb0000880c3c45c00c50303650317800765225041c5102c2d050703455040d800078084541e20b00c180b1280122982041100b01d1185d400c455401c0e8488400a0b55031955100348841c6910108040040100d0721120a82c0000d410b60b0000c0e0b5240c42e6100d40146d503100f40740345007445c180c04811500314a400d504001d5001020707401424290704582da4001644100300004c1550000029602c1c1004400380d048842d20840151080d000c1411110180050301c8100f59581c19100c1c0e8021004060f10035020750741c2c00b940040d4801c180803000341c42c416a019502c060140c1144010700b041541c1341040d040c0c2c175002c003a401d50312a510407640310100308540313210750b4210540d0784560902c40451800100039401207083c0c040c42580702d082e0820385d898911001030041031030707011543c000b5200c451441c90a100900580101c50203940340a4114100c03030003203c4c0140700d4040b0000501c00308960344159040d800210000098041407200c260749103413000c80d14504e002a60744c1c010306c503042d4140140300ea40e0600341e00502940c1403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 375372212 1250 375370962 375370967
    0x30618020a0302060912010e0601030302010c020d020607050f0904090b06150403051b22060e070c0510050604020d0f0e0c011403041707060c023706050a0e120d110307 73
    0x1c20388006442620b01040648280c0c0c2d84040b02040420090001c000e543e02c50803040e03840f4442440150050351902184540c039900100d00000900c040d58042d0403255240e81c4240d4054001020408d03481c081800f07401a95141e81c41034012007400349074140c100f4a88401000950390f0b510303080c281c046c2001d0000b000051000211420400d000340328601c5807006030008503442e400031084030f00e010040c00040403a261100d6000c1425244c1580e081c548036564081c003920306a10301c0c24003d065600c090f0700f50f01d112019601250300f12074020405443e01c0d14107018201036400060704021025641c9184840c0110200244580c0f2402820400410441d2000711101408000e001408000c64440a00d1145108800700c41e00b940e4042d200304401c0b240e5540080d92415042c69000f19507140d411840345c07406150441c1c1d1386001d120b00352600025071a03614203014010113440b410b20709846480e10b5240400c02e00c80c91014400b403201d01a180e4005402400c15160700050849910004105000d0000d0703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 375373462 1250 375372212 375372229
    0x90e100606020c0d050120030403020c0a180c020f0607050a09081203040b13080a0c020f01110d050d09050106030305090a060518091906032625050a0c030c03061802 72
    0x940884010201d51401c3c208a40035101c92824910720000da147c03440d4034070645a000d50302440c0250f00f10703950030044c0001e0000c0d50300380d070041d81b03c0100c411302e1081080445800028024681d841036034403590703403d0035481c40c18406070345a8021410100f08040c9159010610100900c0514014580d52160745000c0c107d42c40054406052010300c0b40015240404034407422014561008015941c0d01104034001c010b56004c1d00100e21405000c5c6121250390321030142c0f1035241c0f44581c09040b02d464001810358040d84040c282100054883c42c0318400310b00700303128a40042d402500c803540da600d511010400210300075040315042c89002c0c003103070b03c000b1030304070794021204030507074103445c046e11b5816070f11203440404241805480d003030038404800c1004107401c03840c90518221080881f0f17011000e000725a806840c0c0a9403a04020141c21802c803000c1c0303003488001c2e074020001e8400e40740c0d040c0c4801000092a40040c2c440380141c0504004100d00b51081618403100020150b401c44141e40c002034031302 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 375374712 1250 375373462 375373483
    0x910080c0702010e030f060c04090518150a09020604030602120106020f100902040b1c0201030f3806030906010f05060a02030901230d0506120f07030305071a01090e10060602 76
    0x3000c10210b00301366031000c002c2c0900d078034082030465119141809145d016903001c0d008140303e0509010110b401a08001c03038401813410f201c0060903805110745205001c1c2140249038525940d01ca90304040907031980001030010714000c880c0980c1c1d51408281203d080003041c0d000c107003113502c001d500601580c00490113844580c151003020810a85030300006d0301401101c47c0b4154420941c0110060b511341d0440442c192602c00c0c1c9041c440341684031500c004603140f04a4980751014080e00d10086245109066101c1102591400d0b09044221000c981e07541c200b1100d030095940124010b108000141c480080140400c407002850080c100000940743c0c054282c0315410b020b8500e80b0030710310b1101c2007801500301a9005445031513403020749455001d40b406907032141c040d03020341801c00000200440c0000b582e400c4171000344038203071070740d40c04444d0b0381d00040c825a002c2d0501003041c1d03a80c600240d00c1d58000c0c0485040800c0f8000103407425418011484a00920b203840c0035810885c040d00071890b503826 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 375375962 1250 375374712 375374717
    0x602060c0a03020d020301090b040f1802090a020c0f0312010e04210c150902010e04090c0e1302041401080f07080c0105130f0b03040c083c0a080910080c070201 70
    0x15001c001005034040d0141c60446500d0030700100010881c0d03041d0727074494810700c5400c840038040461241041000c840b0364810200d810000180c1c2140542440d1101c40d070400660360300149003203080484103090150052a10015820000e51410010750b0036041a0140909061140a42c2425507a0b0701c00a444961100307020007130494840b405901a60000c05020f03040401c4943e8164500760180041045044c00c80c0882c5580300c14107280d04191190301110baa01200440010f42084490140aa4001d007039000380740d03004e2884401a103403409a29611352003201c0c40c44055050040d001d040c03000c0681c0031071403540140401c006000c000a10031032105006e080040d0317500169070784050542055040f4500010910000150005204001314866400744d00900300725900d46000c140c69212601600b000201ca001c1c0c0c0d8248151024101f600c2c1c0c2c40c42003011a02c0840c2080018240714040c1d905541c186c0022801010905080182d8040341e2481c4c94102c0e0030349055941c800d180d010b1501d02904 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 375377212 1250 375375962 375375967
    0x41b0b0307030c0e090c22260a14070303080108010e0a0201080c04050306010b090f0a081b120604061418071536170309041e0606020c0f09010602060c 66
    0x10342c40d010ba0504840e00030003604c0000c5600d4000260f40080d8403100e04600d8500e41d0a8070303a09070300561407d01d03082e40d03404420840480c05d01c10031003c00781c2942c4030500d91802182e104c900001c3e00500200440101d69000e4500240755040c044d1221805910080c01641801910540c0d0a03021078400d84555090070030380c100d0340391055003609601540d00840e8061082c40004100d01c01c0e1200603008a200481d2071403c0c00000000f804060031052062500581c8680e1302d1040605100b07030030800ca0700300940750f8103825110448152404e401035900b6111603a54081000940c001450035940c040c0c040d000644040d282e40c0000b41d41c9079981d204400e0ac0c400c1e20746c51440039512428041409040c80c081c9554104075001d03440c0c0c14010016803600107203914110000b03d000252070b0601240018201560030040150203000103000c41c18a0311500f03080d01c41088600084510414010b00500e5004050070b504000900c18154400c00e0018031450710130300100211a030008110f90f10a1401d50340c01c0c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 375378462 1250 375377212 375377231
    0xe0105071407050d080d052d0a0b100509040c03020306101b050f1b04052211100201060924060c060b0306070e240f0f09090a05041b0b030703 62
    0x50400304160001c60740f1101c0a0714130300a100e8800080c15030345081200411040d01c400c00885041b03e400b49016488404100c14900006222208980d00c40341c41c00022562a000c94002042c1108a0454002050b00800d8040131410603226030310707102299003411455800d0270800902c0e400c20740390030340040084500c0c0346448010500c009016055005c3e088484449003400100d84880142000000c000c8084d4205046486c0c2805018010a01c5050b401c0413608501c250009003100420140d801140c0c04c1c100e0002c0b5220506040d2191003a0b9000103903513400d00150806941030000c01090364900c0310703400c80c03901d14140250741c111a000d00380000a800c903450183c0c0504480440c51350316019540c20040700b69045071849503030040440310603110340c031054510a0740003459a4089040041030126000c070424100003030131084000c40c0d210381007910100004000210807141c100100c0c2c0c96900b0700040002c401e80040403007901e1200c18050904010075900c2c2c40c00f0042003a420140c4a415a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 375379712 1250 375378462 375378503
    0x17070305090d080403050d020c1e010e0d03090503390d0804080703060c0c03020a0206130e010b0705120406020c1e2107050d03230f0711010e010e010507 67
    0x1d9111400241c541d9800708202c3c1054a1550400c0c80151094010b03501e04001c030751f101164100c00d0303a00041210301000251707084c503a10302904914084c184815070358a0110356545000042e00184a03075a1404c003103041900b8182005007540d2a0b0748200000d807011132141a2802510301c0c03000244407203120076151800020141042c44401a00c21140001e001c1010413002c0b4000782034078043c00041c00303030320282081240d50303541c2c0d000040d0050704481d460360700504e031900040a55014154190412a441d00142d9040007020303840144400c40c000b4103001000014081043c0c0c0c0f08200c0c500904240c58098040d4513800c0c0000c109202d00b102444519a20211080c0045400c0d00a4440c24a40aa400b800552000c4031313100d0040520407840000b03a00e150080070400c01507030595400210f02e0000c540c50001c0d1043c031f0111030302040c0c18080c1c00d1100607014080c00350103024441480408007004005401c0003004007071503042005007181480c0e42e0760044112401a070784104400d45514427039851 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 375380962 1250 375379712 375379717
    0x90406050c0412060203100605030610030b03010b12010e1204031e08120a09030306081b010809010b030a050304030605100f060513050a0f0e011502120a170a0e010506090417070305 79
    0x4520b0121188012044c8041540a18841c1490b40d4a640d03c0580302d4000b52490701003210741075444864100c0320654513200342c00c61440600050008a92900040006500707000c0c5281503040b40da541c1e4103074040c01582042543c01c0c02500c403001307914240c1549c8a41e45035442c5800031240c02140b80b46ca6104000da2001220121020640c10761801d04045804002400343e41c002500005d003005c0e001f054030240481c020004180005400007036074021801074072401402032148402e550385503181d11458800340b044c3c1c0d201d02d00c00e40107955a10705510303043c41140d03000f82c001000d41174820700a101c1e58286022a01c1500c01c070b4100b2640380c1060320600c14080c02035811040c1c108078408400a18000c1c500d18406c1510b410440105e2542c0e05d40303081c08200104180c3c1e03140140e1200d0300c0f0069200b161002803034000d45a20b0040c610a0107182e4041070f06005607000c1c0030a40d13031860062400030081c07252a4102004540301c20680c14075884802d031601c0c008691202e0144002410707802c05005004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 375382212 1250 375380962 375380969
    0x10030501151707060519200f28080705031902100c11061f080303011806060e030c130f090c0306060515030a050403110a0f03020f070302090406050c04 66
    0x9204842415001d2141d0030341a10420202440c15401c50800100200f000c40075a5003d60741c4a0520103500e568406440c1c42c0382e002c9040c821091601c04106551070341e80081c41003201c0c020b2020041d01c0300800d181805804104003000141e49581002212403c14000340a0300030105944494960030210304522424403242c1044800007480710480b40c012405241c00d101b114000c21144010080991301d83c0918100245c40303402100000c1d00c0c2d0228445001e0707461704400f00d502ca02c07a45514882e49980c2c001c0e0081400c04280003811040e0300400c0c080c44024015070b1403c00b51001503000801ea541c00c210100a104841c2540510b0717900321154005281c9501011061000d600a4200420f182c01e19000075100c01d400c220340800c3e24100312000f9440e040304454000c2ca1075450302d1900300144030181c42103007007201007600703118900d03010805041210301921250140400300c0c500a880c108140044c50003075000b000b4100096560811000d500c940c000401248990752034030b00060600c070b01d41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 375383462 1250 375382212 375382223
    0x50c030c06070c2306181216290703020a06060f0501020c120c040603080c1506100302070f120509030106051f0e1206040c14010203040b0904020904060b0c0f12071a1003 74
    0x10030950400c560300f8103201090090340e84890b110281002988c940043c826101030142c207081c030410003402045100c442c1852620864000c8069a07004070f0103950041d581a001a40324580324001d100313a511800c0000c003030f0b96000031260761178140040e4a910b8110a000d201c0e500c6020b419490040c107110401952600602c00c21446407a4508003038079400c0b040d100c800c1171041104d01c1c8203121181c550715005020041c41c02507080d4213100110069800f40c441210205510417404001940b40300b0107031003003001da445954440e0041820b0600312404c5911040c800c42c0c0c102c2e4001c610100c0041c00c694008041c0c90304881110f030420124681c0260303421090b83c1841041c0c05c01c03081c0180c0c3c024100c240c800040000c2e05019490b0012643c07401140100a901c01080041807c0c034a42a40100001c200182002c07801c160b440300c480c1c1886d00300c0d001d69181504415503070075440505100d07080c610f001d481d80e81d5040c181107460fa2080b010201380786c8500d205040700403078902403012112400455119 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 375384712 1250 375383462 375383467
    0x131e0c0507031b03080f04050a0506010e04060f06030b19110a020604030810050f01030e100e0304090e011122030609060b01080106080708041502070c03050c030c06070c2306 76
    0x4610080003940254026030008903405007492075612070141144000e5010fa83d40482d41d10381e60a4417090020142c0701300c1d66807052480c10400a0024030000d4000d0000e28802c05991501d802c0070301c1619200106816140d1800606100180c80800302e1a000800d02121070b05158020030340500030070707080242d11186040815101c814a0b4005038461203644250756885140c1c03a00a00048a4807072805426840816074044407195413090384040c1c040080001150061405580d25008a80c031120500788590800181130202e4941d40c0108240007004100030800c01c15003d00000c114014050031510580c2c075524440d4500078101c070102c01030354002c2c2003080403c0d020b00e0450010300298000c1c6001c950010000140782d800b03042024030800164490101550f650381d1101c00002e1340810700e0b610700c1e5090016070080f940a01080c00954480c0300104480c052820815140404482c46148502010000ba0300000c119001d10b00841d02003803036070b2504000d8402d500304400f6200701e8164010501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 375385962 1250 375384712 375384731
    0xc021309052a04020c0a1e03050415050d0509072c13080c0303010b0306090a05010513050405010e150901050a09020307150201090212160803030601051e0f0304030206071d131e 77
    0x319841c28024811003046040583e41c001007910f0801447c3c0c0034021440a2208001c00c2204a00c1c15540c80307041c1c0b078803d00c0c14210802013002c40d4420b4924a20a41c06940c0c10300c05801e900e0030008182030300f00320310400d002d010321031158040c8000b0107031103400302d01e00440b008004148040c1c0d8411a2a4801e580c2c0781c0d80c540010030040d4100321501031040c200003011501d060f180f442507a0584070060090100041d010301c001d0040e12001d803040700c0565a0303d2003100608010b03c6400340c00c10a40e0158103150600c00c807002d0035900050f1802070307030502d8141c0c40401030740c1c0015040100d69504161032801001900143c1c010100b00d10040e42100c85a100e184034450007145202803041e1500001d40340c00e49840704103a582c0402c80d15903002c81c00400c4030300d4602802d8840c400044200701220380c60300242241c034170044d80007510300318056032203041408206504038810f003552404000d4042d002c0f50036500059000002d0000e8a4201580c610703020702203c0c200b52101c41c210040074000e0146500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 375387212 1250 375385962 375385987
    0x9190203070806010608040501140606070f0f0501021b2107032115030203011407121d01020c030702010206011d011a1608030105011701080a03050c1504030c021309052a0402 76
    0x4100c50480300c8e94600b03041418440c1900c201103000d1100036001034180b82007a6988081c01460240683d01550134a2158000803c24001003c00c1c9a0418544804810324030721a81343c207400b81124822035525280c50581c9030004400d5511294040c5004042000145441c1070100808459040e20904010400302c0d0100d21340040f00882e0710950081007401c0780c0d248007140801c0290740c1900000c00c1014107280c40d1000345c002201e04100d40001802d502100b4103190b089a000350345005960b000410000150760f018010503005003c20a9018068038028014120f445814025403118450744a04c1c0080c21503810150b91154000302d5510880e1025030a040250303030000d201d0b0600040d117600c0030315000c13003a60319503034121340d140c20080c005440c1d1550b007a0b50369088660880824452160072245440e0071800d4030340214001e40f40c0000c0c00d0304600502129129005100c800345d0704050040000601c001208298a01044c0000040c4000c80b1901c108041c01c4100d0242d001e400841d51449074003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 375388462 1250 375387212 375387227
    0x3070b040f08070f0c150e0f01031a0d0c050306090f03090907170901151215020a030b0a091a10051603020f0d0201050a0501090e100507090905090a11030105091902030708060106 78
    0x20000001400440c451a401f01c850510002c1425040b0201039002c40c01540650849110384c40401d244950f40542c850102d034004010600940d400d134205481007102d400c2c1885201e0300880a00068441d070495030401d81d94a1081c1a40309000f840318030300050b425803103108070303101e20710849100070b035941480701410740a0210182c40c0645400c4083c0c0000e0031400c011121080075500c0601a801d45184c0c1d8916002504071540103020705171100d001d2002643c03500411405030000c03c50000f020b4400c00c00d00e0f01c062400c0b031788480c000c200d03c1c0aa40180f64204040c0c8030300f06500d944140d42c10102e0726080341054071003401e00c072041c4502c0b40b1080c401d64064219900c07072000454100403a0b0fa9070300306041911484240300a0310b030019a9030030f10702e0006800140d8840b40908240750290307a21004142294400c4841e40b500741c2000111204002c840c4a0011385080201c3c000c1c8200d0802261098480340001c28003080300c41c0c2c20503c0000c640301403107680018841c05003a41c41543e9502c10150a81 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 375389712 1250 375388462 375388469
    0x705010506011e120f05070207090c0e06030105040507031119110a0308070f0504052101150308040b0702010c0c030b250807051b1002091203070b040f08070f0c 70
    0x15428080003441d01c1d4465048507141c0c000d081154142d2407002c0ea82030b00c8240d040c0712000c3c002501c1e04610720035101c0c4d6008050044035a0b50041c002140740440100855608807495820004030450255080d6100b1061300e0560b10300b1540040d40d511005400d50051a20950040d00a5030124502c00074002115201d000050366440b01c83c01c1b0442460306544802981030028007082105021915491140e01c00e00b0a422103402d081e850a900c5030001040c42089034411031b0460361744500002c911400b030082044403442054802d96180c2141c1d9003049a00541c0a0f510350000f0102d4903206684c818101032000b903412264500c03d00b500c80c00c00383d1141108903407400480403040c4400713001d0016800700c050008241e669264840e203500b102280c0f42d500660004521140303140e05114014824451a041a20105c10061380c0d1100f580901404100b4603400350060741003030109802046800900e185d1003039208204c0701040c0a18a0416072500402c2405032682c5541c0b81c03400f040100103000081035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 375390962 1250 375389712 375389723
    0x2703010b03060105060d05101d22020a0b03070203070c0b0c0706080709093314031b0402030604150e0604050a0501120f0c17010203011a0403050304030f051507020307 73
    0x1400d044005040c0c0c0c1d02428407401e500031204208820590095500031030f004400c9002040605a5034045684000c0340d0007030003000700c0c0040381031180b14440401030084180381b6612403004410140c0014811103194495007110000020002c1e60711442441100c0301a039204400c42003403500e408a140341504220004200f910a45001140341406410724900ca881c1c107941d800040c6061800b1240903290100c100d030300f01c80c1c2d408600c1044042d40010111020050005080400e2620329a0115040c500340103902a80000e00b0592462084503080b80c02220142d0380540e80352240c101090041c4001c0454011301c10182a01003460469002c915000d090100d50038485503c030b4601c003600700c6000784545003582d0174402883d000501c030b0354807004100e801289100c9450b543d0740b00751001141c3e101d00302481a503000005020440c0008800455800c1e50002d880c02c160031755582c29500d100b9804047e000b10308071a500410072100300b0084031400f40030741ea2030303200741481200a907076030f084034208842 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 375392212 1250 375390962 375390971
    0x110606030307080f0a03090b0f073e0a060c05040602010501091b0c02040f02220b0406020c120715200a0201050405040b01051e030f0106050301081b0402270301 70
    0x102490000142c0b104650030500303552030070b41c540010300e520340e02800d8001c1c241511104c51001007074001c40c00034030419018034020020324010704000c005e194818601034217041c040c2e0441c00c080446a40c14001c03810104411201c00072544021444e0401c6450001c20361402d2580e52540d056001c00604101c5d40a60028012a600c508800041c0d0780e80f0184da1070031100740d414001d095840741000100c0700740045c00020340d002408504405a81c8070060b44e503c1c4007203490200c89449181c0c441c0400814403542e07042c2c1003a040c842c2c003c0d103d28441091a20600012040103500c03035040c0702c01c6000b0400010a156940040e05001d0074400d0081c3c00d41421091030440b0100d518008540b440311a41d0595405161030f0400040000420410400314108a8240700900003080325100100e10840550000c545074030301144040f507400c130160028020480240010060075078005001021070001c15400c1401c2a10078000c43c009000c2d10602911803914118030b078044e007216015208200d4000d400922 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 375393462 1250 375392212 375392221
    0xa110a0c0611010603050d0804031b0803090d210519090b0f06040b0928020403060237051c020a030608011802030a0605040611041e090501030201020c09040507151106 73
    0xf800c81d242844082c0558101100003040e1511507030049500c00d2080c241b03001e1510903141c0f4420030881e500c904a8000da00041480f001803001c11000841407441e1415072401e8002e4a1411503102521801041303807030300c0304003103181d803c155a20b585505451580400c10002e02d42030120044c042034406a00401440b00400da090516004082400724060208003031515040d5010000c61807200d541c0d40b242c1440fa401d105404003500040c001140161405030301c1c2c11b841100000c0b0345c41c1c14890f0700a150303c0300280b0303090404111810880b04c402410010b8440c4036282003a0b86080b004ac40346078005200140480001c0e03050381c03204c1c0503150540000c01c00b0900c075078158800c00160b100c0182d456480300440f140040d46039089642d220b0f21a0030045151402140114800d81142c5c110040401030b80b0700c0c105400d101c1980400092205220601083d45540c0000c0d4a07140106d03941c0f40109142c03c001024480100801e82c010b040300c00e6224a180b4280400a04c0c0300f401549910b818081d41d000308 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 375394712 1250 375393462 375393497
    0x20f12031314180901061518050402122a190f0302030702070e041b030308010603200703030c17090c150a210b06070b040224030703020a110a0c06 64
    0x20080000094260108076081803c0c1a44001c4003c01480f42c6640f5180c01040c2c440d48110080902d941c65100c0f011224040c0580088000d01034114a00662040c48080e100030340300811360340c02002c8a030304000c916450101c5403620101011a00380308400004400340d0b6011420141041a10556a650501d5003401c13400c50583c8016a00364005078000d0b80240020b56405d00c3d03007608036100e0342404107516400213150500c241c441c0c0c016408125060010404581c050041031072000f5840744049060035209404031040c001e071080942003556640f0038000040c0910a856144520020600e81034504513112917903a400000546015035441c840c0d189a11401c00103032400400a03444040001c500f240b004166424000c40c04c3c00604d889032051681611350034024848203016143c14030f02c0740742c42e00501c500b03c10201c0c82c1041443d298610009040485425a5040b2a4614015942d0011014100c07900c88001c0c4440a40780158007000003040341d030b03442803002c6810980300c800e031100001885 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 375395962 1250 375394712 375394739
    0x301180e12180102100c1e0c05061b0d0f1b020102090a0b0c120c0a140609061803040302040f0507110f03030403050d020d05070f120c05040909020f120313 68
    0xd40201141c184121240d10861044000c02000180b0484104422180d4400241d40484203031303601003003400d0507144000380c00c60381c941024921420081580e60466036196580e0300c005169011040c1a1806106864012411154440b204100c203220b5040c90b10381c4ea000800341c0742102c44800c40401c0e82d49034587e006000351000c42d030b0001e00042d400d40c500f0000303c0310ba5100cad4200c0511070040c0030f008216201454050024203104000410309518107151200e1030701c0089c084c0c4169030f404401004009000069050381c00070040c20310b6112581d0249071685180200d400081d4400e0410f520110b442d04158041c0b4496501684c43c11400460f40550640350601080208095002080080d010034011401040e60410b00d0200500d004890320b00d1004880090b103c900c0014401740304160740c40d5000c002c00440c9158450104900788101ca005012889640728980b101901d4111540641d5100309071401c00100240007580702c5c10301c401a2a480b41c0c80800200b5082c1c0d00f100d00401c5000c0c00d6200c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 375397212 1250 375395962 375395983
    0xc05011a03160308190302070c060e0a09050c0d0c09050d1a0c0307120b0604030c03050a0302060709050a0314012007151406010302030901060f0816051f0f020c060301180e 75
    0x450f01d250010242c51002540e52090017807041c03640030014100051001d4070044010030540c1d4410303046074020700400140710003562200b03141e83d0501c024400e074007400c04215988120102c2d030000f800300741d500042e500044540d100716400005502e400040c0100403504444410041041c004c0340d0362551021b0029010990f50b00e400580b4801480620385010b41c441802c80c18001c3c0858100f581c1c943d40c207901e01740540c004039229000703c4a607200f00340d0100840e40e0040c42d981401c803203080c242008250b6040841c400030741710324a200941070307481c2800e501c1126402c24100130402e10b480f40b044500035644c8094412980d00050003800c0030981c4e0144618030540d0182d194a20326a100c034030044001c0d4001604e070010b107569032180041c1890000c0c05280043c482c420240c00e800c402da03151012104031580c09280102c1e034003080140a5122031a010000d1000da050042d01e038101c03003404a00d40b14031154203d4001400100101c0c510100b2845048030040196051011441c0c03410b080d503c0d0780f050070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 375398462 1250 375397212 375397223
    0xc0f0f050d11090c0c010c050a171501050d0f02030a0618020c1011090306071809050f04080715051504060605160b19020d1d0a030804030f0c05011a031603 68
    0x30303100c45580f500ea07072510307001003a030300b060f81c10044000741e0b4908494810320742401083c0001080e290795034102041480c03803644221400f019241c81e402040301200c0044825040080015080e40204460382c4021100030b90420115200d213042c0d4110390080c41980685007640c00307140318000d400c12948c001c503134200756401c000e0242c0c04100401003002e0500368103003071034401041c041c141007600d0400800380315000d140c1e200013102058451486212103160405034441e0308007800c2040080503503851941050b441503145030780780194244039a4040d0200c40ea0401d4038246010722014101c419150f050301d440849041087d269030744400e50b12482183c0c0c034612121a4030018001291040d440282d008044103107000310248091480d800b20b07400040e18020160f03541400d2480b0308520521456410190402040f00c02480d0300c0181030103a00820040810140040002392948030300d120302070203a031040017401100d62404079849090200808a4024424507c0480e4030000414040b01100e4024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 375399712 1250 375398462 375398483
    0x1090b010f060212070206040b0a090e010f0b091921150b0306130303150308041406090310050703060302060309030c011a010c0303020304061d070e150105091c0c0f0f050d 75
    0x200c00c4c655103038026001c00d0f680400107100c002050b401c11b00081010b801c2a64034041010b09050040c9640b50043c1c0020f505c107040e1000a101031600030048809000d400c45040c81c4ac10160300d8a12107002c002d0b0000300b010100ca0030b8100c1c6849218121025486c0f08918420700b5144203810b54040310a40d80c07010f83e05912400101c2c0c81c14461404c14010b03076010349008121410140c0c0d000d641c12049910031503c0140008080120507106031021030451003c0b41c03501c1c0707080070610020b0340e110b51072070300d10001950b10f50206003003a001750300510003981c0c090149522072074142c0e020340c0c50340c1000d8903c3e1005d50903e400c0741c000c0b030004c131004500384005858030b03076150140b610300301d000707401c0200103e8000da547e00500d40314041440c004d86400c20710300c00030900107090403240e0901e00380203010104d600b641824182c1e1240e1b0024113480e410b0301c007669251104030041488054007144a1006400c07104840c00c003140a01d25107010005035440707864014404c555030002d120b64808510809064003040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 375400962 1250 375399712 375399733
    0xa1b02090c07020409120504060914060703050c030405131d06010f1505091f12050705090d06230a1104030203030a030e03040801180c05040e0a060c1701030501090b010f0602 76
    0x700c401500b205400907000144055060781c0c0d00d42c0140d0600c0409002c150040f400b004190392040800c0f001c4d080c6d0081e008100102c000102d489030154210080c140200403071030702e03452070040094600600c40200b030403440d1890003882600400b00180c0e0cd0400e84500c09544100000c005030040c101c8a42e00d00704030100b490f042e2603290581207001d8110810904208044655840799a841e840c804c07402d1294000d0f443d00c6801030321306089100c10000325410b0100304aa19500318080c0c03002118113031142d100c00307400d9240c044002c2025050410300915a02c0010b02400e011100103445607510300340030044044050440a80384c012444002d5150f4002c1019010b143e01c280c10498010110000704da06044d221320302c01d800d44480c80b000c0c1050b00b0120004005225a0114036002000305440030081d030741042c0d40d2030f40c9031820110040e00080c0c4075030f420180c02d4499100029071158124135801c16584a01c0c2450281403d5501034821144e20f03000454091898070304181200d20a070000c054149a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 375402212 1250 375400962 375400981
    0x5030a0507151115070807110d0c0c080618011526010e1c02060a020306330724020a091406040e0a0e0d02120d020304110d080a1b0209 59
    0xb58101082c0801001c503011410600c02007081d500441101180000c1d549041d410040070910300070300303003020000802c0e0640140800404c40340e82c0001d091412000020041c1403c005180003988240041e200b01410024550044c0000b004001c069100034410302c0300e0195052400000c6004103200202941c075601240000111403100744001080003040c40b05420400c0c2d804e044040c0c100300500100a010055a10b50505c070190b0b04c00441a401c41c15810182c2c04030b50b504160511109039409602c842000c4810aa02c075002c006141b0084143c0d10005840d0244044000c000054003c0303504030741240210703d030303402940c080701000c1d92240182e51a21074900c0070942c107803100350303040700701084086540ea51800c012886400764036404590042485249031074150307400607940c21900800b40700360a09580d01d04031800c580e041c1070301517140e4440c2d00300303484c02c592144162a03000348481131305810485540c0142441c19100d0301c4500590f43c2c04043c105881c005440d00942c462612400501c46a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 375403462 1250 375402212 375402239
    0x8011a0307260f070314010f09080d0c11030f0409150321030902040219110c01051801030b06130315050108030a031e0501081b060c03120402031207081305030a0507 72
    0x4800d07003c50b0003286030300d89241c2c286482c075041030358910885241e104014509009000d498007800c18100101d4407180c603038560900490a99200594660718090031141c407581e00c00034400184000d41e03a032905030590032815a803140c802e000501303080051103d4280c504c3c0b454002100e4100c100100c640718070004e03050304000442d1690040c1541c42d070900e000f680b03843c405009201800200310700c02004c10f070000351008041c0c1c008100c4e0380d0302c1a001d0a0942c1d900c003040d109082c030380c045600d518182400058024205210350560016004550b21a0048000491804807406034419224034031155143e04182e42d03090103008a07580c400c01015000c81d200b0380c4000200d1a071140da0a00b00c074441e501d0300c001e441c3e0a90010001d13070b00c050400c0c81c96950850009801080c00c6401e14941000d80c2d2509480f4020081d0303045010000500281c00e5480510010003606000390310343d41e41d90f0651500e030160b80c029a25244030380101000118443c2400a4407a030004d0300311001300000c40c81c1500301c0e0301d0348 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 375404712 1250 375403462 375403529
    0x30507050c011b17012102280302040605060c0c01030f0908031306050903030408160c030f0c0302090c070b060f03070302090106022a1305060a0504140402030c1009031502040308030108011a0307 85
    0x4039201507075010241d440b0b080c5c1c820207000301508c0181d2a25600402054582c1c94024034441e040800601001300000030305091030250a080100d102c1518517030390070082540d488090300042d400803c01c2001c0b411100070156840c0300304410441525184002c5540c4c1c08102c40c01450700c0300c1000b0580007800d0b02074440451900c10380d200d03110f650300d0b580c0e0703030a000018400440341040305500a00c1140340c9801c0865000804c02ea10b581000e500382c031414500103015201707038015000e0700c070080340a031001e100c481c024680141000050f569a040000d580f02020004160f20500341400800700810f82d80c425090581c00410b01b5108040c0954450300400025000702e51000c1321041c0014513840d0360141c0c903480001103500c0c003020301d494014103007071070b060030400340c896440021086102a0812a0b80003543d8000030034000303034030016070140d0085c401d0760006081010f010000040755041504011040c10369882000c50000841040c16500c80c07150040c401ea21129400e141904207070280325800c01c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 375405962 1250 375404712 375404719
    0xc0f03111e01020a11030f040308130b0a050a02060106021212070c2405150603040f080c07170d0f0807030b1903230a1101030507050c011b17012102 65
    0x303070611041c2120480c0c00600340781050b6500440c001a191703400c401000e114400200185103091803100385140c0611660200410b44080825581e00000e40004e62101070315144080981e5011010405400c0d50031032980800140718103800032901500c081487d250312140c003841a0f0070001004403a50158000a25400c20006500402008a101ea10040c0c000d440440400440800c8446850b4151540106159406009503001c0f540b183c403044101d0741d000e03410804144985d41503142946441c03041080c1c00405110b880300104480314083e910340b0704018208100d46016041c41c0f000c0d00e08000c00030105000c947c080002a162a0190f0030a0741706000c02040b50303047c101603052002881140c0c2c1c03c25071720014410050320105101034140c004000c03184004001580c1c10b03945d43c1004000d0090700754109a140c80109080ca4001c1c42501d00900c940b40092180f041c201e1201c2080b5062540d466001400e02112400c5150312940720354180c4001c5003501d8400d403414403503140c1140b40381c8400c80c0c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 375407212 1250 375405962 375405973
    0x702150402010e1c20030606100f021204090203010f05040c02060123060c010b030d11060103021306031e020102011a010e06031f0603020405040606050c0c01140d09080304020405070c0f0311 83
    0xf11401c41224000b100d101d1441c8080c0320101040172400301681c407201c180030760302080510445590f90340f100c01e8584100c4c0303000701c440342c0d011a080b814130b0310b00411022500c07000b040101c0c07000d041c1e40246050703808445030821100d50714002c2206a4035085000f10168100000501510410700d94000c0103801b0f00007102d041d0300000d030200305182d00c03040342400c1c1a59a419080058502400501000041440c00d0082c3c1b01c008084142c5442061000030311841c0220f8400e042c408098000a0007140c00841100f074041d84200608108005030b80100d005500e0040c01e1401d2940c0480500103e5406a4480800c2031240b030500280750300c003510310010300c83c1080e4a0110450700c60065001b5041ca540c2c0940c40c2c1d13160005000c107564550f000b000521100b40b249514242e00060703481c04801003440c01c6000c111100230307807070010311401c81d841120a080081000134020700c20000d5028a00c280c0c2e0402142d0380e140d2040b1040001c8550003414030b900c0c00d81400200b40f01d948817450801d5140181d07103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 375408462 1250 375407212 375407239
    0xd050a0e1014070f02070b1e12040203010507050c07120503070206040f080c0a031205070f02060406020312060d030207030201110c0405070c1b051011010f050f0f0702150402010e 78
    0x14582904149448001a290400300124002d01c081c000d410110600744014240110301010b91a00c00b81d002d00711250300085000a240100d00c10315003500102142d016580d00b0709268801241030301220103900070743c24040401d04a40c801d0b011610400005000350184c94101002e802840d80b550302c00307564a11061080b40c0141c2d58480040000b04103040c204901c1e00d02d0240014240f0595000ea40c2c03043e070740300c042000400c0d202c2c0601010381090b440c2c8070f0ba99145a251050780c0420700385000e504000c02017070101d210358000009002d03c18540400e13010950f80d200c2002603589440c04000d005810107c0c00f000194092a014010b080348101982d580c8041c46000c40c3c115a0100c40340741c0001c1c0851030100510105109601088081900f0b002d0428104004107940140d128038403401c01000c0c2c5140582090203501010f201200b030701052200d81400128121301c902c0551b82c5c4818041e4180100e0398440c00003170700c0366000e0191048201c1588d990380040d43d403074030394000c11a008000c00b442c02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 375409712 1250 375408462 375408491
    0x10f0201061a0a0f0e030604022b050c0a08010216020f060f03090a11030f0606130f0509010203040c06090e040201051602031c0801060e01090b0c07050307170c060f0d050a 75
    0x2141110b14034105291540000c40c40180007181142c030400500103007801350f1070b45807404920680e100e501542c40301042c0c5200c125540000410b0321030503210901c8070188801300040411140d07103015086426246160301c0304041030803842800c900400b0580060060401410b01c816008024900108564107014140d150349490b644105c0f07a100d5241c10204018003081032511003803c0441c0c054006241c81100b5040403542c0b000302420052007494030100b00d0a0b07000d030300c1d0001c1700032000000061085042640d0310030701075042600c048440c58000b500100d0303c10b01c9643c80c0400c8464943d2058080d407171b035400549040d40058400c924251000c070041c009178500300300c80307421110707068401010030804071001021400d068010b01e0402030600d2a200c516a804414030066906401c1007a035166611550146002115400071703416014171500002d42d2020f0704032145042c2d54940681d040089507204001061003448010422040c05111494110b0180e07449203a1004442400282032030070040c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 375410962 1250 375409712 375409739
    0x40b07030509011d03060a05090f0307060501030b060d0305030f06030102040906120218010f0b030606040510050a02100209220603020402031812400e0420030c010f020106 75
    0x1034020810020b801c40e81075900000104044c41d000304410403c10542c40080c2c0c942e480508180d03000c903115000316101d50010b112070303100b00710446e040b44d555030391620705000500002d00c0300792940b4035502d00045407030408200a008540d0f166494a1841d584c0d000c0ca074404110150800e9015035080c4000700f400c5040e0701c0340380c0c0603004c8000700030404591841006000480010000d4045412030010020740707240c01c0c0004190b0340004042900e0b0341c0c64101040300e5001d03590006521000721100300010340e410000500d54001268241c4804078010821201a482070752181070b007245e070000450894801240c3d43c07213074080c01480040340c131035569000941643c0065a041c40030103480d500c01e5014000402051580850801030325003800c00003506900200c08404080702245821804800d40e41000c80341e0603654903903401220043d6807aa01c135045d03606001c032412140300c18086d1500d0591180d281ca51074842900400401c84c0070007150044030000342203d0500155901c3d9400880c03c1541c2803a03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 375412212 1250 375410962 375410977
    0x61404080a060f0c020c0906010507030e031002030711010603050a0f06021209011d150103020108180601030b06040b0906130f02160f05011103010f0b16060e0703060b060901051e040b 80
    0xc001c0f504852400c904001c45655011074015903101054511301611030520250b4403110908100c2e480e0402030606850b0b40a44047c6036a00d4060035001500302d45a982c050f500a00c0c0760303901e0400e000b95912156080b01c07058000a48140c0c02404c9940014904c00520302c2c6031031051030050b0901100b0030030b808200d1403d03a80c0600c0c41e5100c45054010302e0000c0008170740340100400400715017001e04454280a1410300010b41040381c5180062480a510740c001130440d1420821a0740c15a5603003402c8060010981e4020f124a0411400c034081d071511340700d05c9001d42c100030183c81c920010090b07a04010070b100011164025001c1c0705855010302c030045900080d900806018200d0619854040d0031071710b61404214010030180014003a001c840311288095075160009503030f548182e00c66030042c4090382c0900508031030500c014800104000301e001c004072407150744244181d020388820003001e4058840c1d458001032040c01882c00d80d10840c0b01c1c1c11081900071143c5444d003a100c550425080d4001c80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 375413462 1250 375412212 375412223
    0x5040308040201110102130b070303061d06010e060f190e040e100609050f01030602071502160c060206220606030b090a030e01050304020604060f20100b03120301061404080a 76
    0x30400081d0350300010401c1d8015102402107260452005001004400740d025030f00c120741020a04000300350080d0b10110150070b24482d45840700c441d8480c002882ca0048034000d001560104005105003000000d450044000041990a0041703640450915802000700c5008000040d0000500368540d032049410031220b4901414000340780480301030030365003183d0000781c2d03c520f080b080080114440015a064079403060002d0703030300d1000342001e1116240c4414107602081c40090350f4401c2c1c000b407119024916101c1c0f5400100290307100000d984482e0119281c1600c0ca21501c24104280040c2e60b00c012030512031040003480720744076100c000350440100c2e20708205500000740c2906140d045602a80c40d01001d10f030503459403a0a9001c940c0f11b00507842840144070300c0420802c06940035804070365041050b01502134950444945182d03070b8160b020b8996030a2071074415050005d06004c03400018400d407501c440c1d45140d1030840c00302c1d01000c20300c8a5001808007031002050980083c82182c0e00180100f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 375414712 1250 375413462 375413477
    0xe09100602190201090b0c0709020a09180b0a091d010603080307021912051c05150a09110f031914010608090607090311040e2a091003020d08070204050403 68
    0x100041c0c9002c1d05507070700d0341e20281e0b1100311034010303079018001d2819900d5041407191600d80c0c0c0b0519900c0c102007500620402400030a91641e030980c4401c065085800c0c054901011030f8091035011700f100d0f198045981c01201e51003040c411500300342c0142068000b2100300d80c041100c00c12800b801c403003007604100e0700c0e00400010b02840380d50400120300f00c0308a0358042002c01c04107558000410448139190000e1000119030f055100c0c0002d07034a004c61600000c0240803510f00301c1010398120b0128042e952044000041c00b00305030140340300f405214011729014901d08110045400000e400082c00e1900d07071038010201401e050100c6c0540641170081401038081941040000b42c0070620080412074964092400c000d440c2e94442e60712400c0b660442c2d54022001d0001c2c0110303001e0000e60600016511a10303204108003032602496040a0984001205150a4080030411441402c0d51300e2401300e00050014030140c5010803141a6551007114031031303e05551540403e0644100303c03025000b01d440b8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 375415962 1250 375414712 375414719
    0x1050f040b0d05061c0308060406050d0c0801050c0a021e03040b0d05090d1d0108071404030b01330e030102071a0414030a0f0818011e0608031801030c0e0910 69
    0x640c00340e80e0b0001380840720b1100301594114159801000450041c080210100c04203c00e526a0740c080b90180c80d020300001074002260401c090794007682e108014003903203081e001489003c092000d03107030020655409400c6804004810304091400c4007920f40c0107000c20800026100360080040c20301c0100ca81e8042520700d8440301039400c00301d0800c20b030004e01210400c69410410b40c100c1c20301000c0002d0030140c200e5105c00c501162140c0f54048003002d80a40004c3c0441440920324101d1704031000072000e030210407904044159080e12060030680309041c202da0707802c141070190445c0000d10380003600043c101115903c50000f00410003200c40070840200c000e000901c41d44000d20100d400500e00114902030390700d1001407080e5004080302c1c1c00c202810012500e81380391f0312003120440c3c01e034800901005083c141829003141c800300c0d52030f0704a840c012001502c4200801605c80072898207081c28145244840154040c10f000d09034403040002ca030008102070f80d02c51004c107006504075048098403a08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 375417212 1250 375415962 375415987
    0x803040c210311010c090504051005120a02040f0603020109050607060227010e0301050c031308070602030411091005010917010f0608030d1841010b10030e0c090601050f040b 76
    0x2c080001c3d052907414140b144050a4104c45000110340e425a000995542d510b5868030301d101950704110383c0901e42078104500500005020540305001f25801c100e10002d40b030056044401d2880001d000c1041034408229600c0c041b4090300200307000d00005131a000c903400103694880100c000102604082d41c01402c15540d000d8004454000d040e4002c121030b013003100c8200446d0000034071180b502000d05180f01c042055441c1518010340c0e210320295103904040c5043c54804043c01c0615004161890025421601ca21040c0c2c044443c10785130305410303908007242301900c03058030709000e1401d40d00e0788000c401c080100d02c128001000c1880181d600c405241c040b1000b0303100f0102c00da4103424240010100810740030403003d411440032201ca0944015200d841c3e814602e03200c00c20f8506840e1080c8c0c2c3c244000d5041d00640400007046031041d070306000884041e800c40700c00d5540c4c21200c0c1d20410056505080c2008100e801c80014101b29090490401c0c0100c256803060704210683c00e00480c40038203600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 375418462 1250 375417212 375417227
    0x909030909240506160507180507170415060b190201050601090302010512090a0b010308030103030813050307020409080c12040801050117100221090322120803040c2103 74
    0x82d0803944164006000307410021001080c00b900740b294800090002d12143c000100041c60341d070042c20744030707850b90f00d1030108005401c0c01d4031956011f05040020703c0b42d44c0f00362078460302e01640d20400303006925580c460300e855a035040700300b402e103664643e07020ad58000282c02a2890800c206c0c1441031500d0030143c002c1c2036071000350034176050205d40202400141c0e0010182c80052041d128003001903540d000e8000e16251600c07001403c0440302000101c01e10050030000d40c180c9000740c550040a880300100d42810b6406000003510a4205100780001071609401150300b103405000e1550401e500d11125500b8900c0589000c0c03584030303000408000c0b25600b802450300404008120f4058408045032164641564503265100743d5030000e00d074000c407010210081c1d1580c0d2903a444040c6442c1c0015480d541c1d91120f61a845103070100c4080d4514a00b801c0c406105580c4485000c0f564046580ea030403056407c094001c84150300b00010100d14200072915568442c142d01d05601c6004016050150506 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 375419712 1250 375418462 375418481
    0xb1b1515041413021e09040804030c0b0f04030b280c03050c070803041506090f020a020613050c10030209030f06040314040e0708061c050705011d0a05060c070909030909 74
    0x11011141008902c00700e000c201802d207038050315501120203911707070306118084494207500d5110501d00140000d01c40030001030300940380300304c40f0519607580b180c40c01c01d1f040c001e042c400e0351854001c000600000308a0f04403990003e050441c0c401400380804058080013072440000b090319666243d425000e240d060080640181c3e041c2c810310b290066988516800744030040c0060b00c04400304c03429030b001c0515540705100600044008204504503003403a02c010b03501c031090364401442010b0124915103c46d10021450700c1d07201c40141039401343c64090102c6007581311841400d2507402c0c000b00d0311a860501185110035114405000300b8a42440c001d040e200c3c03001410710030b11030b0601080c0300741c40800c21440d0304a112030030701ca141603840c0400202d901c41a003095a48503680b640440c0c003003100010300c072001e0b68002d8840d141002078400c0103a908110305107243c5d81c881a810000c0055081c20750080c20501580700035640055210780c109000c0c0e03800800d040700000d10541c001c001c032110511401001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 375420962 1250 375419712 375419741
    0x15090b060d060902031b0f0304022e0f0e1c02130b060c0f01180305091e040c0e0114181c0803010e040b0f01080a02010e03100606030204030c060201060b1b151504 71
    0x10b00c4807c42c500a0107000040c0024066410b1441602450b034080c00d06000e400d8001c0c161781e15131407060100602c220498040080440c500e00c030806143c3c0b0700750400c0880074500c69650000306107d5020050216940d00d0000807503592221030f1101c0d5201c3d98018164520081300805e180a0060700c41d07070846203000310003040d5200c80395171000002d40c02000ca80071482c08860071015001d5819280070720103c166025580300d480c00c0044500d01c0c2c1c2056241d0420902600c80000d540107070682103121303100c0e4910b084525201181442d6161901b101d6142146002e80c2101e10788801d2030341c0307034039840e8400c1e00708000c20141d4204100c00c0009114185501c81c0351450042d0f110351400005a0f81c0d41c44100d8000d0510030710012403011510208000d008101c4c40c420140301050ba10360b03014009500c5400b040e00c3d0181c1c19140800c4090050050b00101c4401c0c405003450400019450041040b1a405045c06802144688c081000750480c0e0f4500070018006000f00710300e029001c10045640c0351140108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 375422212 1250 375420962 375420967
    0x608190b0a0207030207120b04050c0a0b070305030c160812060a0e07111516091505030705160605010306020a11060c1b0a020307080703020a0915090b060d060902031b 73
    0x14200a0503981c10194100016031900c0346840c00f0b904110030360300850150700d0450100d9023407012609525004600500a84020700c18842c01d0024441d81400342100c00034081040d0b0000030b1003440103550103081503d620f802e0584040c949050000300882c01c0c0c98526000c43d21511020b21041d0440e000380040300c3c013401d242c0c03803c00e03289003c86005000314288140721400071002038051280722000107101d810400145400c0e0400340a010608070b1001c000b80342400041068120307005070b1140d20000c0c0d1951401e55035020b00c1110395034051445010782d0b4480200c0320000032502e003e0240a5489190056150203280030300034001c1d00e2800a06800340c0c050410b001211468500b1101750003a888a030000c02d00402c0503003407520800742c00017500362281c403200156590005c02e03560196842180c3c2d5681580e5115000760666400c403004129041007924108500c581d81d41c0010b074560400b80c11039040c8001ca20b40c8104941599200d905415000410043c0c4810030342000d880f59280700f9078560 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 375423462 1250 375422212 375422263
    0x512040617060d0219230f0d031e0906080916030602030c040e010e1e0702150a06180c030b0d030e040905070e090f010b0f03060610050f07060608 64
    0x400040c00803081031049020310011400b562030300905440e0b41500030300010a10350040403221a496400e105070211845100041302c1c41c96400c4401d003c0b2110001d00805034004205c00f000070284480d1802c40500c031842c000100b900e0103680c0c0c0c403240d03101030342c8501100c0b2385010300c090100200200703846c05a400c000e2112901c2c0030b117003e0305000c1e01d401c108016200da0790921200068400c07500842d00a9018000020f1681e406d4100c003849122000e5441404c4401c0c210525081da00c00d45004d40580c00212000c41848940034103e540b042070003c0110700a44d403081014880c0307040324401241152030745510140903030075000f01e000b58030f420703030704e001921b22a038800a2a41303040c42022445035489103070304424814100083c03c06070000d00b06000e51410828481076903a03607041041c10729942090b40c0d03041d10b480c221000414045001d0b001d0700c0c46030744803420003030008000600c41013444802e0001d079203c0074044014151f01485008001802400c0000786454455a502e0324501380b4624041c88 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 375424712 1250 375423462 375423467
    0x6050c0a1b05060c160e06060a0f020109020a14090f0912180a06230f0406180e010f05010207090606020a0f0c09020d0b1306081e01150801050405120406 67
    0x1103100c5078000760092507035910449892526081640260750014010039185040c010214000e001c191211351000c456907502c494101c00c418003181d00982c0040140a98110781e40070b89400002d160722440001100e081e02d43c002025100c403a000002c02d44500521340e0030f5401e00c0c860854128101144c1c001051801003005a42d44800401c04640c0140108140f0750fa92404050b1450a00008282c4118030b621290020010010405130003000360714507400d100407203882e03c201d072068088900790b00d1415060903030681c1e80c0c07040e2004940d50407807960400210b400301c0e495407501138511070912601041c03074200024680201038104207150740c43d04100b001560740000b0080c801030b6001245502d0300c0c0860800600c800020762140e404540002280351a0007100c0e03000b0614510200e440303070180a941d02484040382c9141c024800554070403050802aa441c0c0741c1014101c502c0d840000c1005120480221411010355005c1c41d460380d1254141f0042150a104007c020045482c00d40e0401303180c0b8130300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 375425962 1250 375424712 375424723
    0x18011107140102100204090c14180f4e0a110604031b1805130b0a0204090609021306020a03120c2a02010219030c060b011713020a06050c 60
    0x800340580703101005258164000c1c02604c0f05076800701c0301103403541c1d500e4260170041c052950124001545c2c0203040404c80f0004070a4451451580b60100c910502210a200c801c02c0752120b05540205030030006014030010303606c2d050212180c150002d03103001d00396a40388204680031000380c1881120885041031541c0c000380e2161800d0708480d59814800001d0045803003031046030000b0700807081e50b81c040701154428001d100308992418260043c817218a03840d5100320b44040c1c41d075901012503900440e0200e10110b001ca60021400080146400d9480b0801e03400c65406520004c19280c0115549100b008140c030010005d04150001e08406030440c5d5000344004600c0000d840c1d0706941d071509400007031180009940c80b007004110229003004102c143d0a107038800c0c041c2240140700304001c03004801860060414081d503d81c0301d0402c0e00540e83d407408d003c2e040c3e1489203030400200095117a51089400116800f501c1d01d20f02d01880e500b1a801440b0340c03e405500400c0038800e04004030b601c3e50800180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 375427212 1250 375425962 375425969
    0x190e010c111311160309060c051914191a06030303131e050a1713120f0f0309140618120a02030d03020d0605030106060c03050d0f0f0218011107 63
    0x50101c0303052840000c2d030008208080c04aa06241c0202e801c00f200003510452400343c5000b40c07980c8203800e56030081160315485103036004210f900180018900c0d0040c204900a02d507108020310980c040d8030540c142d19103400006810003c1c0c58040c0ca50050116160f060001c01200104d128234918180000c641c0c0c80c4000341680c01c50035030150000062160000111100d07001c84088001088101c0c05c0a40e0f480003c4001a1074904044040e40c40b030407401001c54140b0b8641c1d0504100c904d02c0c10501e41f200e801c081d1419207101c200b03028414005210100401d0500e4469161808401e0518030510410001c0300b11150140310b0410084440284000c51091181c8044031810719400c2c0c1c035075003541040713110140207400d8803615608100390b54241e0060541d02c02180d004000081e070b102c08260a8626030302c1424040703181000d100b8042440b4000500c00c001152001040742403d5010782c1003220703442044503900660114050140111904643d01c0a860918011030000f100044113522440c0b41e20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 375428462 1250 375427212 375427219
    0x5041a010c0609020d08070b060909060112030309230d030b0901030b09150a05091506090402280602010b010905040c080c1309140a0c020d0f0f0c08190e010c11 70
    0x1019042007103529085010100e9014021710304c0c0c00c2a07843e200c41c8540204000b120f8244d0500009021401c1010308180325034103090080c403041c0d2a1140c200380440d040a4150b041548403155100824101011a8900000101181950b0400025070340c00c00020a00000816040a01e42000d80e0b031200141e60550382c201c4201e0f509034071952113252514400316820704100b00c0b40301c20013048910b15440103124000750400d54403207080410041c1e0b041d0074125035040e032250600c4046409400e04480c184d90691a2503081e5002040a0141c21a661016441000180c0d107440c403402c0075517070004854000308070545041c000b01018640180c00c0f10030040100c080000040791a4148410000703809008040c4190200224240100000c42000013100c11a21082c14070065420303080c030000d808214080c0960700c468014408810445002070f03408400c90810038800042d5000c904040024450542c02140220358803035848005000880721801450600071482c40f00070101e0498814842d00c000200c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 375429712 1250 375428462 375428477
    0x140610032001030f0c09060905060c07030b0c120c07030216060f0c0227010e0106020f0d0507020f1002010c030f0c17060301090c0b0c2b0e0a031b0f05041a01 69
    0x1800101c009000c000301135042c0303a0810780403820190300074208030280c8080340d65240c0c1e195251014440184074040000c000c0f58014641003002c03400428689806c06960380606180c010180040c020140094462075049100019070004260f010003002a24110001da400c080030314290303000d00300e001401d50707a40a20884403088411551019010308501e201020041d9484224090005010b0024001c8034a0782200c84000301b24907000184004003110414000d214480710180e04889a07040f9080c1240c10107114040c1d121580d551140400c0c03941030036800041c44d14542040203080c4c034141071410880c80c0c600183c00085603800000c0480c001030900ea80341036038550a010031700506100e44068803121032280d0100b15001000f0080c9a6562020126000c122129050501000307031100c2d40d2030032203901c0228180d200c1c003e010002000e44010242040203550b81c95484083c5249900400001082076092050407960b20700070010f020b00307503010440c80c2d0803080100104480801134bc2d0511400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 375430962 1250 375429712 375429773
    0x6040b04140a06290f0f0d051507030218010305010302030d11210a0807021b0409050f0109030e01090b1201140a03050307031e030203100e06010e0a0314061003 70
    0x10402c242a02d6880344040091400e00118509603502c1c0c0480907a00902040c1032102d03a01e030205000380d41d10170040c196181c00814500300f00e1541c0811404840d280900c441613600d611440d9041c5100341c042d9140982c1d18200038000b5a401e40b0503205e00781c18189880010700168800040c401c0c5144048e0800c40002040a00400e1a085d240104600168400c40c0e000030040748075400307070524180c552104081a00e0342e1000f03a07280c0c080391030303004000001e01607884410b10701a0080742016004400f600c1c1081c2c02400300c5030942e0b00b015000e4010488490b0000e0140d41d2003699940103107801c0c2007a508010704810301404042c03040c403941030303030400b00d54005007507a44030b010380380065a0100403250754051601c5d015113101004007c0c051120b13005800380c041d042c06030080341e02c100032140421070080d04204205003e00c90107060b03a4100020051000c1c02a2641d065100145010f40f6008454070005c1d01410f00d400002000c0d004011085841000060081401d1440c4030305512a030103022000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 375432212 1250 375430962 375431003
    0xa0201080a060f170d110a081c02280f080c0d1410080d03020304031e031508031b0a02010504030b0606160b180309060d05130b190e06040b04 62
    0x43d00400807000c05400c000400303908800e00c0c0080e0240700020b0302c420002c1080191502e0440302a91b15250300301110b00d2000a242d00004c1011541000106104401070310724035003281c001c00343d92103e40075614800c01e940006500324192050a614000c4009042c1c20002006100c2c05080c40d403d110001c6540520003000c1e40160070702522808403d4032500c2c181002568084180c41148018000d83c4140e926880c030074000c8034440c58241d10b9259160300d2800380c0c0110441c2501c0000109603450780540d448030300415000c4000c2c00e000c0011034841c0c484460100d20508013000c00803003a40000010300040c0d8010040d14102d0760070007150200b5950b208045445485600c05118030303550200061020000c201d01101e0040c289034445c0c0c4c6402080400e096501d2080c0403190b54031580c240440c1c040b6044070380003a90722104046100d00c4601e86a40c5880d60380c0702c1500c007050004001d42c2c2044204d000ca10030403000142a0700107165904164403072154a5402800150000d00303d8100e280c030059 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 375433462 1250 375432212 375432221
    0x1506050301020a08041209060507030507060608010e070527131a04030c140a32030c0102370c050a122708102003040606030605010b0c0a0201080a 64
    0x88003038000d5646040c0c20b40001c010203c01c0ba0304941e10030000d0010030584e4403e80c501d01c03e82d03986072074940c031b007d00948080c0c510350003005003140c0d526207441d004075480c3c401307000380314810039050010311106003070008110440d0b01045941c1c101091640d9446420b0040c11911a00300c4e00a1101084603080303401e0480215911880282ca0409400140310400d035200f66080c2d0740f1809443c039001c2c03540149030213646840c0581c4000d00843c40f070010b103106400802000e0365010240051202d4004c2082042c9401c40c2c004151400302c695010401c21f0340401e81c00c0303428124a810540c1604141486900080403144a981d91420810612900000c000040200e02c15103034201031005010f40030a003000f0450050001000780795540b982c0c1c0d07410525000d00f0a4016241100054401480c80302d080c5801411100c0304000491103049080000d00e0402d401580141c0c0981c40c04260786080d0308080055400607440005c06683c200500000644040703100159182d09281c01255500c400c007512003c0c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 375434712 1250 375433462 375433469
    0xf06190e07082505010503090a0206090a08151b0a090b0a051b0f0d030b0a0e0405070e0709090b0609060a1d031e010f0c0f111e01050403031d0a1506 65
    0x244030b41c2c4904000c0c6180072100f40d1101e03150352803030744540d51507400455580c04243d4003038000d6840b425001c401840d094019120145014204056546e0b40c0c0c0001454198003200c1c0808101015084c80b00240d2030842005581d180145ca41d4a0b0009901004188070b034140310f002c0844201184a142d580c2c030a204484840c03058564410766070280c1060703152684819511602e00d480341c0303460020300764081d005401911000070481302c441440c2120848400400030012540e6008124000c5100c080c270280182c0101c1c0b0550b1480d681074101030f503441c1110030350807040740b0464082c05a03901559842c8202c1d0704203003540c60306084018040c1118042e030844640e038150306002d114141d00a500346102400f9610041d0b5000f40a80000d401e40315044a42580299001440521a801d4028012068039800d0b8079580102c410050342411601c40d441030540d08031482e81d441d001403005050707140c091001080d800049110700d05240d400c450b56140350940e0300400705101d80c20950325014850b4440d0008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 375435962 1250 375434712 375434729
    0x6050a0306050c0904050c0a08010821090301140403020a0b010602070e01150309140a1719051c0501141f020304210b01090903080f0f060f040e0a0804080f06190e07 72
    0x590501f0b0002250540002e6002c400040d182c000000742c1c0100041c1034040c104022690309051070304100b20a0080e40401d86058141d92601e000c4a00e400b10310f030190b8030a0340aa030180c125500039242c502c120f188180e0244003154402e4806222280780c0b689013604640c0140d501040c4a038540e40190302a00380020054030100021000d1909180e0100d00348141c01c0c405e11281151034525140c040d180d000707100369511110882401a1800d1b400f0318010416001c04081c500402c150515103034041c2d0304243c00a0b000b0710850188000103040002c80e44003d540715400c007000a88813040004e55070300a51141d040ca903000c4031250b00d046440c1406140701706401070410516582c503418080090020b5090482c0050800e0002404458400380d040e03000c0c1e4120440030300c05440f5101001800204039800582c000c1c0c1c4c03030100c0a5034201c1008209410740c803d100f415200d83c50080b110781050450003c03107a05812210401ca48617855912030f0741c01c2d460381040001d8502111405034500324154000444 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 375437212 1250 375435962 375435971
    0x5030d030c020a0515071101200306031603060902010801081b0f0a050d0605161110090809030102072f010e090c07050706121b0503060405090c0a060e1306050a0306050c0904 76
    0x1345c00f1600541500c98109910313000708540211aa441c201d410550890750340c0e480da1102580351081040003507821860060844401c0740f250a20712007044c2544d8030403110030741da903e1000304550b080b507901401000700c43d01401e0000900f00908180d038103800d000b184213080030242c01c191950750303000500240201618045040345140752800040506a600000c40d10302591000d2250b481050150760120405010705410040c5038101005130401302021958100c050103032003010341302440a0a201402402100e03401150000c85014011658209801d1146500786418039030342c000c40411800c900c01d4515611990341c0a0150069000702a00100ba43c06440000940107030b00c0140c6d20b400160f481401c001c008001c020400924450500900c04244140b00044441c0392a520860740903c1030025900700e18600320000d019101035420204c0414282c1c1407408107400c00410b45030400c03160780b004019035400c28000a550b902a032000401d00c039280e000107040e035101030064601c203030b101400511 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 375438462 1250 375437212 375437233
    0x609180a0305030402030c090c0f0a050f0c0d120e0d0c06090204092907120b01090305101401091404020d060e0a0803040209150901091d0a141002030105030d030c020a05 74
    0x2c200b6401a01e040e0f109205200107100d09282c1070b002c01d0702400603010414070f07025191440b07403444d401c0104800c0c01e0010030311023440400410780050007150100e5000e00a4071141400241001c1428480c401c00240b400400203102d120001e944484000030381066000740704146040e101a043d50400290040d040c100100c04100244000795084400c1255480d041540100028020316007111400000307600e4440030304000d001684081d5100d5010324000c80802e40302e071a031a00c0c04507462045420b43e035641c01c22094000c8496811405800c1900d81441403051825000321400d038090000f9219000040c8004100202c990101c0c68181d0260306580710390803e410560303196001201d05030b00411041c000a114a00300341054440914000c050003102e03420310a42000515240c0542009119501c10240c4441d00402071b40c035000380b0491245954251460104d81446c240c05184003e02e4014001403001c0c0c2d402080300c902480503417400103050115858124900207516070050202d0240b800250b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 375439712 1250 375438462 375438467
    0xd020a030b0601110a050c011b06050106050433081009090c0302132a2003180604081b04020d0207030210060602070f0e090c03060910140f0609180a03 66
    0x140c402c20003600c40035103846004441a40b120686030000701140c00000c0810055070140003500c0ca94444a49080012011079840104643c07007a00301201046020404100380c041c40d100c0400c0705200312034122030601d4078500e2810b00712680441a0301b8001c1620000744012218480a80101092001803000fa4150704000107d0801800140e01407035443d608410318003145e000750015070107000d2038109021420002c0e40c0c40b0040c6850724104104241200455120300c03824019004503018000e0755039800d190b1520003115699900680c0510400e0208008000c0089080c1e080000547d6989450640402c0010000e104203c00356118a02c0400d61405242e0b00240400c00b00f07142803010090070f41c07950701c160b940e1302c001d2003604c4081c03869041c188000122501000e4014a43d601184d0f420218030000a003441c1b000c45010440b03030302070144812001964026000200c144038203404840c10140b0540354034010082049000720412008580000207404035003d1411700a42901c45c800c4103443c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 375440962 1250 375439712 375439733
    0x20d03030b0108060609091302040e0312060f0102060408040b0f0906220503010204050f120309040c0c0c06080105150a020c0918070b03130213060b0d05182a0d020a03 73
    0x860b800103101c000002c106040460841e01e00c210028010707861581d980d80f10341004810740500300e8003d519640780340c65400e8100302401030840d000540103c8d034544201800040034940d0b1242c0c2c1198031100501000c0398520080300c1c1901c2c0180350180c1d86014603508032402e40325020f03000790403501c0025081ca240ba118440440c02e0b00b00c0001002d0040d50b200300709803c0c0d01440c042c269002c9040b01000344a460160300001c80184181c0a0328249010074000600300d0b00c40300341c01f01c04070b54242010300030020300035030300c40c0178100b6414a0a225410107000c50318241040e0b625070440c074800240403000d24020010040c50300702c0101542c03401d2601d240700421050342d821b80e1451a00c9502c9000c200f0380e0f604010f0300d00c21540801104c0801000b5005c11a01002103003c8426040e07850b42c0100b000c041210007491600d1801c440401c450400607a8403003420481840b09041e034001c22155010072400e100081440055640703d100d1035488040024510703042c0c4078000394002c200000c00420000803210 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 375442212 1250 375440962 375440981
    0x607120e0a090f0b010306030b161e0c1502070506012601111309020306061602190305061e10090218091003060501080d080604051509040501090b071103040b0c0a020d0303 75
    0x240442c4c0d40301c20040d020384443d030100401c00c1128400281d2502122152001c0814a0346824040200c038201003034200f0200003c07141c000741c3c80b4000d100601c0102d10000e800c004400c60110314105035919003e844044c1805403601940c85e5940400700038144000c0011940e14441c0200410a4140c4140309980e0000301107940084c0403400004a020080c400d9030b208420141c44603251401c0005ca2111105100ba01280c0c40003040041c0c2400186003a010b9002c0c51043c0010070301c5082c0305029456400410048400c02000d06c420410410311a03204e460843d06400d8000d0784403403034070162101800d1101c450640046035030382007100c0e07110713004005c0301100c2c05841e00300681c2c4d0320b848115071146000c182c084045a02540410603500f015840240e226200d6080d4441070700716000065100b0034195816145a9100e54401040c04034990015030828010b041c401a10000421016101d0042c1d100d40c0d951030348007146501d8500f40c1070050820007607008207214a01480c0d40750140043c502c010b07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 375443462 1250 375442212 375442241
    0x141603080a02221e0f0b090102150405100f0b030a030c150c0930110d15020702181504021315050c0111030c0d0507121112090c0607120e0a09 62
    0x540e844040e1131071039000002c0c3e80130358807400f0b2160304007801c43c07aa030791203080d031241103114004d076501c0350954800c2002d014510900c09040b100051500c52801c1d54007032002074107101d00d0440c07241015540001c55054055042c18138010036409820f040d0f051840000c01e03c265641012100c1001c680c2c40311130345040d101489401c00b0702d40c00043ca00c8038000c03800300d0607843c803501d84840d40c0082509014074070780380d140042c1040c4801110b03035154040440e4003000040603a8011a046d8118a00742640d403807018003440ea104200d18003012a0a101008441014000e0303a00240d107a00100312401c00c40041c000c07003d000e2088501c625402821540110b48960309540780003c00440085100101c80c045c0815407445030515a00c0e5500c2c84c01042c0c0030701701d070003400241e940019507490540184001789401e000c100352a03003107890006001d8800100100c80580154030044042c1d602e95081e0743c075054100f180303509503012850b000d8502e1450740010b1070303104400e950700140c2c081c0070740c20a1506100c0380 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 375444712 1250 375443462 375443489
    0x30403031d030c03120c090a051c06110702031c02030301090b0301020f040602060f0f040206040302040507030e0718060b2104080d0e0703022e030506040902120d141603080a0222 78
    0xc280441b03d40071784040194080700c504000c10051a0036680303c1403580c4411100614407600d5030b204011614411003c0079000c50100d010402e514080c040020065141540202c0c0c500011000070b4487c881400f442c402c044c1e40d00744154643c3c40940c107581c0d902c072013003543c40d54451325410302a56440741202d08600710201d420004649c0b40700700780c0c0382d03001c1d1790301404690034075003075508001c09000300500722001c06030b45800d0304900c0d4100b00b04102c01400a40302d2400c00024042a41054405030740006841501c2040400b031042d010030005600196200c2200c036681d211450410070912030b2102c01c04950f420100f10404038080454105e0460741f08032290541110054241c2e000241c0780c050545141ca004111519418000e8000c0d55010100410001c0c1c1c3d01030381d60002d400784d00b51029035000c03644810b1580a165421003003a100e41b035080c114481c249a90f5224001001166580003010001c1040100351800d0140d01a00d86c0d842014854121070300301603290641c0b020b628070480280f40b045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 375445962 1250 375444712 375444721
    0x3090504150b030126120a08041103060f04060e01020a02061306060506030408033c0411210f07290d05011e090e07050d050a0501140f01050f0105030403031d030c0312 73
    0x40c12440e11b00803021800d0030701c018903500340c40d00d41000384159109170000b0103c07010365a0510240388540b044446c540b006007014103211003194280b80d401865a0310400c01500ca880e0001001307580240c0190961200c180b1501e841c402804d280d60005400c12408800d00040140342e101851203000641442d88031161495124140140180c1a10b40e8494060860414444400c2c1c0502d40c05030103030031304496407998200407030071003645e0410418490001c2281414407070028445480050900f4000706602400c200c01941c146003d5400044c60390415590b4140c0020104169900610007881c03c22a940c0d50390300d00725a5020300f490114000280d0480172520114621500030910448001040010704000520002000061040c5d400744110608840041c1d0240920b06280701c2c01d42d00c0c1c1c6820708001400d0b008012040c0c01071407040d01405014103260764030109486c0d1298051a0100e13111070b58946102c25295041018615130000141a001980c0000000d144c40a502007051405956 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 375447212 1250 375445962 375446039
    0x30307082a01020a08040308040c05120f010e07060801050d150615020c040c0e1309020d050a05070609050d06020f1902060915010b03010e04020111030706050f0f0403090504150b0301 80
    0xf82c071130420007041c0c0c003c01103804280b0402015900920030305a40c060b443d100e40000303c8103030507113900c40040c5d8000840318008220a0061921015084008152541c1004405014458140180d03030140240c60f400c10140080a039102c81c00340c400c10f0b8104243ea4030740c0002811482084c52101c098450a0505400ca0a01c4d1243c1450460700d40e0f0750b448044013140400c0b24001601c0c43c0c1c1d2400d651103103403460143c0c1d10034808404003485940103100e40d16561400a0400d4010340c44071062240e5142c041101c1d4607411581c00702180d12060050740c6003000034007010319005100c1c070b070310b00350b1212442d01448540002d403482c0034840d2001107520052400502d02900311090003400d0014100b8001040261361480318541c1284c414102070b0f1010300c2c00194140355070426081558501d4440302409640021244002d1b00200201500030070343c80c1585014007800b596101d124000d556485012645c50380324540d000181c03183c0100c0507a82e50390381c4c40668004900d0314805011620b40300804c5c12010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 375448462 1250 375447212 375447217
    0xc2e1119020d0807030c021f05060405010503060915130f0606090b030309060f07030c081c05060f010203070b040302190c09050c0c0a150627051005030a0809030307082a0102 76
    0xc1c40c1d070f40d081e41666841c0781c11400b03000c14403030b10b10540c4070b030b00c2500daa00841011051415001070200003640d107131003000c000a580c03040e88500d000350414028800021000f190701d00e01d83c00030181608081d2039003082100e134100e03182c0000e03044211074220b0208100107a0000e208480004105100f50072500d010142c5901c2402c1740035520100400030a03001c0d4900b1400b400d103031030090030b20381ca13030034501c0d181d5045a038040e0126180e800b80a0b148010b10a40c40d12409402102c10740c0ea4501ca5452800041d60707a00c200341014024174122000039041610802c921391081d03138a1040e00100e04551f140407241843d16004000c1c1080c24040040c00e03c40f074900c26107c21044500060030b69401d00c0e16000038074601c5050003850680c0b6014042343c3c811218148940303034250410001607030742d4040c145408450300138003078401407903448070104155a40003440344545600070003096030342c41c0c424001901d036100c0e00034028440040401c0c4000c2e5008030514090b84111107101c69444580c51890031401c07807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 375449712 1250 375448462 375448483
    0x3021216120e01020d06060207080105010e150d0c0503030a0302070203011404020916030f1e0b1503360a02010210021e0a02010902031b0112020c2e111902 68
    0x301c501541119044160300300c4403070522014001445c2c40c841520000984010b80c1281e40540d02249003001140024419180105076400440c4407c0c20030307600d0b0815410303045807424403481c0c901c10403100b8801c91619640080400404407556451030490150103500329841c203074825403034101c41c4001a43c454030301a20555004280030700c1d40d0784200040d2201e1178801d0b040820103070b460742c0d40d81180546101e00c01040c11191102483c443c0035242d1402590524000c1d2401000c0c4450065811052a03050780d4102c1418075040042085109000c224004041ca00394484401c000342402e034800007145500c0310b94001c0e400d03110444944c0030302c08141d2007a00c62001c04142c0200c1d8800d400428040984202c984500c0003054000c0303240c0010786040034a0b80c0f401500d1951401440c0c0560300318141d00f8181d01101d1007582810140b80c00c1030348886403500814a0301d066040d02d5071501040000751200504000b404018160000c4140702c142d8101030f8101d400784943e1502100d5041c000152100c45 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 375450962 1250 375449712 375449717
    0x9050d02010519030e010605030303130206070f0506071211160809042003010905011d010303080402010c120e1002011e0207020613030c05010201182118091e06060c2405010603021216 80
    0xc1074153700348681350348072890503070750005240f08130f40004d28144080341c0074024035a2541800c0341c0d087c91701c03c100d42103484900c000c2002040200c0700d030324140510700c0043d50440c54460701c0740c5ca01c20100d0054501122451215010350000b1880020180081d50680e02c5000f000c0249a0320b45001400080c0200344e00d00c5c6155030b035001000064400d22110354843d00c103160041d005070741035032594a22564940c1800114580c0b99480d02a818120b412a003242003c0c4000c0c040c1c0104003039040b9030001805504020940c0008406081d074072103508441d021100940246680c69403818015107844090080c40d0055003400c0d41d040340411030309503801b81c4942180030b000501c40c640404504e100d524844580c00c0c044c121325502c50315902c203e02800180503458000c00e409040b0486070b1001c0d000c0055042180b4034003401400f146510490f030540a0b50310a100b068000021030311020040c0b40b4011540c2c80d0b500340760000c103a00d603041e0040c0c6411aa0b000d10700405403109a5625403503c2d010604100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 375452212 1250 375450962 375450991
    0x30a050f16020907020a120806130b0406171507090b0d05060d0602030709030510020f0a051b030414130e0d0509040f09030c0b0a0c09050d02010519030e010605030303 73
    0x100c00400c0014004540c110048000c0c8000c0c0c0c0e0301164540504890070303c09a00001c82d1401481b0400024030000652880c000303139546044000980f42c20032210540082c0f694850b52504140c482d0751001014100042e01d0301c500e42d0280585a030303503280d810520008000881c000c03e10072809103212406072501a8019820640000070031001090020038180d40508020101700214406d8401107008000c9542e400f0701103411170a04503e441c516110180c50f041c410010803444c47d1141e0203070350500305d051400c165103004040303003500d040c2c0b440003100c0e410303000004000640c070038150090000c0308020384000c070400748a1403034201242d000030701120054000120aa10980c814402030110300d100402c005040003460302c9400488400c0141200031608200daa481841b40c07400106600080d00401404030340c421440c01002400d5034800c1c01d0003410000181011607001c1c0b0151f4070041d84ca440314034450041a40c4c028050207003007565070a10351030083c0200b8a0704001c001c59214240e008107560 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 375453462 1250 375452212 375452227
    0x14010e0d03020a0315030f2d021c0b01030803061c02030d0e06041a040906122a030501090b040201022503080a1101182a051e1002030a0801090506030d080901110403050307060b03030a05 81
    0x190101c0ad54240c00030744100c01101e100084100d0309240c0070b980501042e58507482c1c904180300d441070301500002448080d00440800507640051008a400c92900d072034001902d0b10700108400d07009030381041098200d0140d40344111040600030b80100d9400c0f02050080654440d20b02079090081030000d4044101c0b44d2070501c42209030705000c064400405a0810803560b283c44080c00c40700421421188415103100344815580d040000fa100d510243c0b0082141c0300c4010658004040349200040c10600c000c62940142400740c3c0c1202d5416050030000d201d64807034644200c60036061140d00319803c1110780510b4080103041760301124400c5403254004886030828003004108020745035402d403c4500442e030360751541c54991541c00c41000c1d030b8004540342d07011454040e101c0c0300141c110070b803894500703030802c102550001840819403c0505000b0700d55116262803501412490171012082040090700004101d0000000c11802b4020401003046140201c00c16480c2c2c0301d03a8004c040003580078050607 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 375454712 1250 375453462 375453469
    0x405010c0e1008070909090503071b2403091a09070e010605091504091b14131205070e01060c061103010501141c050708010314010e0d03020a0315030f2d02 68
    0x244c11803080e08101d048a03580e5071b885020b88008074811159034202095075405c00501c3c06042c0046c4074142c43e2070400a0406070000310810404840f031045a2000640ba0b05040c041e2b031180d8022900181104a80344a0315a5100c0d50b00c400c0d2418442e603c64200f000400c2c0c6120003c41c0d060310415075070903140801c82001c100d00c01c02c10382c844650318182008001b89015503803158448003020540c2c02c01d0f542c1c10706c00010380000308000b40340c4c4d10f0100411081d070410b40b1044811090f00c0095042e050503410701d0030620b14140d001d4001c600c420070f0080001c01c40c21b800c07110100300f040c4145d100303000c4006d0203e19107516020a1003000d0105041d007807144800c231001070151945e2641580702e04103829100c001e86060b1003042d6810000305089000600c284a6940d104035080d55050700248088141010f84aa0317503103209000c84105070307001c10b4600b8003d100742c0142d01c1c00c1c150f0001140000e52282412000d04100c4902258803154060100e41c10600d00c042d40f20710842c411a84a8a01d81c80b40c007030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 375455962 1250 375454712 375454727
    0x30b09040c080f1c18090e2a0d0312090209010b0c0118051e0a1a060a0806090a061805100b0916090e040602040510110f15040602070302031e030405010c0e10 69
    0x7200314030b40b81030307201040c094640c0c0315642d01107054000500c60248c00c3d400d201c4000c240f40c014000c8040b0100d2004401d41c03501e03213211824991510b0009800c481c001c1001e00240391206000b50302808480000031542e0740c00e00a0030700000540b008110110f000586034004140010000740550404203080c0342c0d50200515a001340c10240041c1d440220095130f03082c0e40440300f50f402c0c0c001405c2c0e0b50180442400d2003110a03015182c132100401c141d042c90303801141c3d41c01400000412040c0c83d001c14450440500480703611155000302268121202c01d200000035060f00e40134180603007008800103206410a40a5040c54002a200c20301204d0808800ca20034400007001918160b4003004001826100e1881410001c4030517624181c00c40c0c0d2911311681819041c608295495101c001e2341c1c0c003004030b030f001c040303400c1640701500599881880c5412f90075030240700c48040302c0ea1104601302d80d0005140004602c40c034401c8008220703d4004c031006a881c01d50300001d15800442c4028060740d5540507100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 375457212 1250 375455962 375455987
    0x2c06040b06120a05070e01050d03020c0907030b030d051e07020604060509030a0b010611060a020301141c0506130c0602030703080a0507030e16061107150807030b09040c080f1c 77
    0x8081861070410104500d0f000a008080f1400e0f445101e08000c641c0c07080078214003400e403c0714070318817043e042d4900030355400c0d00c0f84145100d9038203200400d40e0390340a948039280e401c1c8080e0588818129000b0043d150b5007082448a03840d040301d810300b800b0031181c0340441d401d140d802845d00b030034a420100c0490710368000040300e03a0107205070040d04000c200d64400490080005a81e1500c4014041a841d410404042c025140c52801400188010340c0034860100c0c00305003ea074161800e03820520300301622826080302074603074041d0740306002d4200c8207460311035001405044140038850360ba10040b41c0e030b4803500034003800040031130002c50b40d2140d503a0096600a4001d19000c2400d90680d83d01c0c509280171031110030703080f451202e0308101c03043d0000026002410b40302c025294451800c680a801901101c1e50902000700490000348110300a80c844c640c05400501720341646e1420f4074000303805c0303095401010103d00c02ca480f001550100014001d4410240302001c40121201034416140700c0c00c00320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 375458462 1250 375457212 375457219
    0x6180c0f060f0706021312120206010311130227031513030804080c100e1009150504050316051b061c11120a021902240a0f0e012c06040b06 61
    0x12403800c00e4108086d2002d894044c0080103040020720b4520b1326000141007460964000380b0041010943e00601944120301c150350351030702c0310750405180000380300740d00741904030b203000c1c0c10a886002c2220501110078102a81290440240d005030b185810004540a6002d0341d040b05031000043c0c4100c11103500039102c0c101d95410b088110140c18102440550a43d03c5c507590303501c64091400b0100080c103c102d54200d0204210540d0752180c44600400403440110551664040ba0802004000b1100000184410030030380b44030f90300c0c0c02622a0600d07101103002c08030400070744000c0d1601e08225825507210707000945036007419110b14405407400b01189450344c0343c2400740c43c14101c0741060180c0700300d000301c4006a80c0c45460049908405c1d00d10404004c56001903807000c11140750903580385141048400400c42d03507807800d450502400325450a0100d10b0704201581d400004150001d0f212000c000d945d07410340c030038003180000d642e00707407140f60300d02c00d50104e40070801003801c05190b5500018040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 375459712 1250 375458462 375458467
    0x1110f010902030d09030809100504090c0810051512090a020a0f0f090b220f0f140a09080331080304050606090912070c0308160302070b0a091e030506180c0f060f070602 74
    0x6100700b400300c0e070701c0c00028804920703b0380410004d44203480035080038041c100d4025281036a042500083c40c020680c2660381800d000021400d500b00400084090581c02421008004d8451165107e001024480d02251451481c2c1c0441c84d18054000d2141509001e0050a0391040c424207400080042180040d0f03550b030b60340c22a61142c0342c01e0060000b500350b81b800c00f245641d11011008002c2a0040c00c6044441c64194a10001242001240d4006403201e07030607441c1c0f1859440c401c1a80748843c0c064540c040d41c8100f40001c01c4408000385109500a0301503a0142d610308042c400c0030782b0219650000303a00268007074030342548003802500f110790003241c0c03134404252030390f840450503401180c1c10044060000210b008140c3d04014003070240515414003410f1400300c41d40500543e1090090400052091854a90840300408008010360300a811142c80d820100c142a0038040c8500ca41d940902944d80411140c1c24101ea450b000014060006840c0012010305130007150031401041314030f580c08 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 375460962 1250 375459712 375459719
    0x2c01050304060f0c031a0a060e01080901021207030b0f011806050c12040303020114010b04030c0302090403050c161a041208032208130504200901110f010902030d09030809100504 78
    0x10f92050913080042074500181020100741040341030b004041900b44266031454040c0b0140b58000d45082241e0028204046540c45800041e406401804450090340960b0000c100100c1c2d4150040071400e0b000b035503078a42020124004680d0044000f100b042205180304080014a2140c8000d003003070390003502900c400000e4501c0c2c08000c0d902030f5100740c005130344034100300c00f20104103603000340180500c207240d0349081e155a6a07205200441e100203442042c4980c00101494051001c4ad031030440c40100f60f61010900c50100c2880000a0140c0300300e40e40e01e044080e8140c09060119410f555108243c190440b48540d600c0310641e200031700380d441c180c1e604022a08034802e2500440002441002e02c2a00e032440400303407400c1ca481c560301c2141314506200c0c401c480c8442c108800341000703412140c80340e0f81c0d040c400016283d004810000d00400e2090818541480310f040d130100d402c15100310161604914500e0007100d0640c6c1c2800301525110f010449000286844d4040e100d004200d402d283d400d081d80d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 375462212 1250 375460962 375460991
    0x804080a05071406070305010b0313080706060302030105041511160f0203070506030f07080f070e1203090d050a140c1008070c021002010b040c020d090e040804050409050703032c0105030406 83
    0x40d125800034113644141c080c021181e404d40541130140902d038640c01e0461500d020b00041c1c030850018081e051b100c00040c9601400309a800c400081c6401600a0140b402c0a1500c0040010742510120f0000e01d00004000c1c840c441c40c007121403a51641a034018240c15a0300d6031880000c40502c01c036414071a2a000207600d85030301c0d01540c03103400442c0d003008080c40c0240c03010785201c0000f0400c0c07007044842402c2200158008032948441d01e810703150440b201003031092691442c0320314508181e020418581ca44104900081e4840b0a18820047c01008084503410540d9803281010425031050003995000100ca229018040c3d02144030724014031102616004101002c003629921801030751103900041180c10309010780110800244000e0001124110009000c040c450140508010a04021409106541e02500c004e400010070400a090042c6003180d07a504040c8030032800308030031000390800e00c58551400c00b50604c560207480c042c968400c00444607584003e0048035402e0343c1d058543c44550 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 375463462 1250 375462212 375462233
    0x150507170c070b13090912120b06041203031134150204090c0918020c010f0c0801031505090601120303140906150a08120306030a080c1509010c0804080a0507 69
    0x5041d000c695600b00f44c84c0c4820010216130048599182070007446c0700020075180f41d000d0011ba0a140c01240c500b51000aa0040c0c0480007030b4a510540101e804103000703000c039030b46080b21442901d00f00302d40070481401210601038034a480c48121480d1910320024201015010000307401010f4410300d442440e40c40840365072441030074160096001c03c05018044240c4034684c1d00d8001c074107102c04450300d40b40400c05181c100c00b40324400d80340c001c100b00a441209400c00e600100e095002809010168080100685002d220a0b02d600d109c0c0d100b501c0814065201c0c040c0241d4200020b02403980c00c000340d001401c1c109100840030943e82c0d00884445900031441203004101ea600a449541040085114070300490b0301d80a2003400605810042c404c800a01c004c4600761034101903071241e5035080000e04211025034040e144100c0050203500103507001c10003441b00d80c03a02d000c030203e586845010b9400c03500d00c0b0720681c002c2425230011074086072408000e400324140710700d001c03450700303029035103580009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 375464712 1250 375463462 375463469
    0x13030501060308090f040207110609031e0102070b13050d081e040501090b090f0606102303010e0703020405130506060f0a0e030f01090b1302011403090a02010207150507170c07 77
    0x1c03d070218201030740d450f080e040b20b0f07400342d130071103040d0304244c0c280c4c407411440250b03030084920800300040c0c0e0006644050190383c050300381804001400101078243e042c081d43c08030100b160b203402150009015015404035020003282c0050050880d07207a124426112054050f06031007407030210080c82015040e028801071b10551066001043c69189440c0c00021103001814034081c54100d184500300c00000001c1441d40500e084640c85030350b20940d282030312269070ba4801c0300030100c0d22140c1d128100140c900218100c0e0705800c0258110782d91480c0031801ca00a6014840d4003482c07111806221400a8202d1904150001c0c801031802c4080d641e8140e032648001d8020012419080c00400d00d40740504c07507002252002c80082c081c0101390364521440140050520140040c100310841c150392140e404141c8107a2408001a030720705200c1e1580340d4070284901b00302c2c01840344020100d042d07014440c0d0083c103400710381c8882c0d00b000340a5440ca10315a07103800750840500c01c2400203c003156000c10400004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 375465962 1250 375464712 375464723
    0x30601240e040207030c050105090d051206150a020a0c08120d0c0324060801120c0e0a1e060e0916050f030c03010f0c11010b100509030f0703030503161b08130305010603 74
    0x41000c7d14105007036400041c0202c0198001c4058000030503005400c448a405106a500000d075450f0700010b542c0e41010b2032654000c000201c1c50b0711915800040840c03203030f030141c40c1c0b440d2465034410616907200e040c0050540d11307903401d01420100000c940c0010309400310504000c21004e010400c103c8640c801815122590b480076401002502d800000e89405040c1b0760600c10b108030041d88071032040c00100d21440d00b50203024400643d100c036003035200000c016003c60300d06607244000d030411406000030740a80d8004900700d07004514064000208103400d0741d200000403959a252104009080e90180d200740d4150041c160800010b0fa020310138001c0340300304000002004003081c0401003298000e019550000d1307141c200700c103503180d0f60140640d070390341c1840ca441542c0d070740b0601c00300341000850038011400784107291020080680000246202d0103202d10b4982e803c1c00301c00700031900c0b15200502c1c41c0c00d9510400300400800c02c4035004041040c13820800b801c2c0c15a0703d599480c01c680156000791071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 375467212 1250 375465962 375465977
    0xb090a0f0b07140405030a020d15020301080a030f0206090c01140c1509010b03030c03032a070c060e041802061321060c0309020906090a1d0303060f030601240e04020703 74
    0x40e103d0708658411415291401c8407420b05080201081d580d8600f1900603215011003c400c40402403040d40310340200044e101c056403a541e44030146980c800c5994802c4000c500140d611511451000ae1268801c044030301c010000302e45880015070744550b1040300e4406004c410040711203a0402040702d1040054070030b210603950b00c0c2618402c0d007111501a0b14a1182c3c108112080032140c0000c19030b90440c1d01c540c01c100040c905c011540d2031070032200200c5000c0d01c401080100500000e411013408803810303604c0c1d42d1803041c80d440403c402ca80f0403100803030074800c1d400d0404015042c02c20142a4036030506000d0f580b150340324400490524000380000c60031b0903e2a00003c00c00102d40105610410345080c240440790a41c5d00141200600230611401b8550000006c1c0403410644c00801c810a05501500003c2c00b03101c400c5900c030390040350068018141c80400c001103060011740c143c1200d42581c0c07500303075458009005036081d201012549040201008100782150380320310090400b035200e034943c5030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 375468462 1250 375467212 375467221
    0x10e0f0f0d0503190506030a120309020103050a0501050d0602180a15020c190605030709030c0f05010810031a070309171c05010b031515030114090c0403020d0b090a0f0b 74
    0x91034204858015402c001c001d00c240b0031040207503103403c0d6480e043c10901040790740d07a83c000700e4503014002c0000b5240c0c80344021040b0800e1781551081c582e45000b0b27a82407003a90f850007100400d4920070301c00c2d1604011070743e4508011031071039800b0b0110100c1e005600da54082010000031509802d80e0041c180001c150245680d070031383c04124034646a50245d0ba49010003d800c020044045642c0c81a8014080e0000002c0e064501c9052020007443d0b00c0000765845949404603425a02c80314024103000c9484403000c110b110070180f40c81400c8943c005950f10351403000702c0340801d440d00b026281e90207154654621100285800c40704c54051184d04401702d40b281070b0854566040b040b001c4481862514000041c0911110601102c1d0300c5800d0b200d07071a0100700c00300c0116a0180c150052502c990f40c001c4004584800b4a03134010175200340885000800752102c080703590841c4078510000350300001c1d404208000a07995030035103500c41007110035a20311958a850752854606080e500f00c8944500341c0400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 375469712 1250 375468462 375468493
    0xa2109050123060303030402120f0109080a110f031602120a1a130b04140f1015050307060504120c0504180203011b08010b070809060f0c1b130e010e0f 66
    0x8204041d100b54a9200314105100400e0301e03444041d0010b80524103c504108044c8810803100103114101b0008000002c2903080c4220540c002c5070901d80041e004031824100314000082c1c070940000144007075468414084030385501c20000010882e082210f261104a04150a10505000d03900a2000b82d000c13800044802894000040c00b9600900c9a1890003003c10311880203268001c1e40207901c1c40038000302035801840c003e034090b800c0a840c03003140f0b40204a0b880c41d40040c02c01d1050801d02c2854a174a4004058464905020b1000062030500c07080151800300315608102c0b0380241c0788030740741d2910b8102285c2514240c0a548940c640c0c0c0f200c5d0310302141424441c076450203192800c00302d00b0b9225031000410030300061007441c02000010840005100e040d4044a0000340d008140c15601d0924204400c1d55801c039007460203140c0a031007a10718409240c00444464100010001c503809098011910002c2c807000c800741850b03642c0c41e2508903480904100522002c0c1968004000d61075460780c0302c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 375470962 1250 375469712 375469751
    0x4030c060206071b020d02040b0a1403120a080f060f04140415020301180e1c09090c0e010507020402070609080f091314061315090203090606150a21090501 68
    0x6043c10002103041904294814800c2c801c40250304642e03410210005d4000600503055003405a580030030101c0f030006415084149180560005070180e07907041c405856140301500840d04c520700801d10020000d11895200100e050b07000d94000d01081070341610f400400c0484482c1489040024120340a0006000100d9840703980340e0540c0c3d9081d4a10745c1011890500c102e071050a0a0115031544400d0200c2c0030b051041d4050030002e2414103c203d90b5100d4014610241881501d60041c5050343d65184144a240101410901038441d40c0c070303010050b4280310095015813025281c032039032549000e0004240d180100700106000c1e800e1a100c40700d071000c0140c048030100540407014a8220310002009070701f840300f54050400c44912a4402c1c264001d5400f80ca20125110b1109190b40c201045800d407aa028500944084044841c03d40d10941071010300031107101c8180c540502030080c20f007000d100f0784c0d0188929240003d906032840041c1da045042d0340c10f00a0483d226511601070445001483d0741 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 375472212 1250 375470962 375470971
    0x312061906050a03021305100203090108090610060f110d080108010f0501030506060d02030733110703170c0f0717060c040b0d09020603090606040b0f1f0207050604030c060206 77
    0x140010300c603180400290841c4103e452440034544c011400240c6142a5040c03003000b85005805020f80c80c030310100007502c070781c00200d009001c5078100002c070742c10b080005459071041c100c2c400e41c1081e079420030b18141d8070038110350071090808c13125000d0084840418040488214000d858000f0f803541858445420344124814625100e4a0310004202140b000140d02da0005801c0d190f020440006001103400c140aa402624000c03034865010614920340a0318026403281c20900c0000d0f0b41403442048a922840d034221850a60040304280040740c600035082c44000e0302b120319070f40b03004000061242012110618000103420581e0104001c00d241000e100400c12a44084c0081303241c681e02255160107a8060421000000b00d09145003481542c0003294040d00106016143e00e015262039030740390402c03101240200e0502c240d0b1001410400d10081015100078091440521100c132a003a000240780c4144086103c1c0e0580000d241d11500000c0018500030282181c0076400d00d00c3c00703440d0500140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 375473462 1250 375472212 375472249
    0x4020714030c1b0411030f10150845010f1802130b09011e030f0f060b01020d050a080402030a020d0b0106021c1704020a0e100306050117060f04080705031206 69
    0x11178070016100000480c1e40c40380c3c0c0b6540c003444644581c01404040c2c1c4080d04882014203200c280710445a4002030301500c00c0070049102c940250100841c440a4804100c00d4070b4400ca0303800f501172000240c801c031041124a0034000045859400720000103441542141604528600c003480003503041c44a007080e001c00c00603a0611040750300b2804a0f60f854014814180c2030441301440040f16098110518002d64010b2202c400421040c14102d40f0400022021500d01d8a03200c0c0124181d40082840032045029840302c50910b518420309071107230b4000030001c07641401040041d40050703568085244440d40a0317210010150705202c4043d01d40b0701c059800340700c4c4907102d2384181203040c1e0200ca00c01d0705002c001c031643c174640c0b25407000c1072000e202e540140c4841c1f00340350304014868800d103c0180480b801968117010603640c981d60508007560031146c3c0a02500b0180000d80f002200d0356102d5007061090840ca8541270843e101c080c01e5410090144100c4920801801818a08803109100020b13090703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 375474712 1250 375473462 375473471
    0x303071d06030618070c05061018060e070c0609060606020303060a0e010b0d0903050c100f1406090117030408030a170609061e0a120f02181504020714030c1b04 70
    0x40001400010041c0c0a48104e20301c0d030400140d016203d6098a010b4135841407c071180c5044c85070000851b0b42c80307400742010942c038010000c04040d00d11301500c0c1c1150380d02c09030b0141c7c90301c03908000c56a00c00204170541c0e081c1d45802407440000c0c1c0500c43c0e074000b4401c6c1d6006e15100d080c880100f0003240f01c2c0380d0003903d00004003801441882031303a4003294442c0191010001d0055003514081e101c2d400381510643d0280902030f204503804100390000c40ea190f4084a0400211050b0400741d924060150741d1306030050b5007400140a03980b05000004004a400021641001d540d01038161455010b032241100045000d01107a4841724103400760b9170405821174004005160031404a045490180344d1002201c03030954943d031160b11122184000303011903051009101440e414103602c1200701d09402c0b401000e0143c0b1090b451402c07042d64500443d070755030041e200c8041c2d40c01007002a41221030705445119511203d004041e00c01c10040000303403510005404408070b800001080c210301400c03418025802c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 375475962 1250 375474712 375474721
    0x71505150303121f0e0f072706030e0d050904020c030f071b05090106080f15120105041e05030a030f060b030a0b01030b0f0102151003061d06010f0f03030309030309050303071d0603 79
    0x20502c540c007150b030030040340c21903452010485000482040ca824038000031003502c1c05084c6d0890423101078900c3d985041c041003c404800310358410b01000e5420004100f8002c80c511407406e074004104235050001101d05000440003121801c0d4009502150403180c030041c0c1032800c03081c11810100506048840c2c00d055032400c8409010307000010104000c0c034007003174005003001680400342d480890001c1c0c0a1409101240e03040b500810081e903054454441042d8804491a81000c580041a038000080c2d03007030842c002c9042d4050114400110042500ca44002c10100304150181d84101e04d0800b0107e4404c500c9800901112041c1c490140514060310024040ba6000103080032141500350708000265580b217075030a407810300d42c1c0008100034100110542100b003495130000c060501c403025501242d0361180780070b041080603c030300000141c038060100702081c041d9004900b4240a801d0204c0d6005959032a181581c0c011a0300384045200410380d052521038000703581d4a201000d543c00b600d1401c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 375477212 1250 375475962 375475979
    0x504020109050613090608030d06080c03150907331701050d080c010507021c02030408072616060207060c0807020909030d090b010312020102071505150303121f 70
    0xc5501a641c000e800c000303035003100b1010b20a13180005125801c010001c0300d46030740b066500ca83c40011143c0500303040c05000700f288030340840da51040441c020014060001c2a032500310341c00200410450090048080000b007180c0c0e8190f0702c1001500b52250f105c1d0b0030025483d0b02c001c072100201c0c00010480942c100804180501d001181943c60031542110b001d000c0d4038103041203114800c03810301d455003000d0034428541c3e000150b4000c0000c690907040991a403a4000300e0b60f900031481210030301c0d40110001c1114a90b03418007040801001441c1d51118814816058681054070110142c0c084154104002c1c0c5a814070619019000b2482d000611881540f5030010303034017601d600030f0f110700e600c840801c0108000b0000c440c0751a09600050114a032030741006003032150248010ba400c4d1f043c51420100c0a44184200e950096101e40b81d100411000c007003081c004c1100501280300085408804462550100b0240c0120459490310340d035503180c803859900d10002944040c42c14a0654541401190f5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 375478462 1250 375477212 375477227
    0xa090b0307170f0102040311030705061e0d0605060705100e0115031101022e0b04110d1104181a060a230405060a021005160e090a0e010204120c080105040201 69
    0x1601d1450300104881c4003200c02d0b0400003046801403c540c400500002005244410440c550000b101a9030002c2d503030740140601880f411030b052640c4160180403c1ca50154023015240c088400d1000150950721800070801a61201800703480c5a4008072440b8071001c1103004104c01001c02d00c00a0040c803c0744400d00d0541081c0d40001009484504a1551264800c000040d140f0400c9240030030019526900d5550f0b45041220882e0703c44d00f0610302c52002d003000c1c05a03004250031000024074165401d08900024103c600d20030f44030410401c8009028024000400d1002c8140140001d03111040640d2030203034480c40c100c2d980180024807034500740d103402c4581c0c1c0b40400c032a68100c0940d00f441c0c1840c01c50910440d00000d91000011526500320340d400a1030190f10500b0130300c1001951107881900c00c84209410701d0500145812050701014200451800d03082036001d00081030072500c41c0001c80c00e90300b141e00070010500e0280c1c116014800d04d12089801813180724000c1200d42050740000300380d00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 375479712 1250 375478462 375478469
    0x10e0114030417130e01080a0b040b060117070207052b150207020301020d1b08010315090201051614060c041401050705030702040906050709090209130e0a0f030e0a090b0307 76
    0x4480110000742404201d03c4140c81e807102030108aaa14a0440c01d03200442046000b02e049455010700085000003001440700d03440c580041c0b00310340a0741d507a602c51108020041011f4104003001d0500300e12601da80c0742e03281c02059140c020f4801c0c5030821007480303000e8102d0880c1001c0d00c00c4980d4811040a01c51140c00300c200e4001d90b4404811030b988280d00080d12403800000c1d010f61000900d503168180e5644900d002401884508418200d40d6100315440d40c001e00002e080e0f188141f80d4104d245440d91f01c002010341c810704046d402c00c0c80d80a2418200c10b03410f902a03071482c503c60411880e00100307000260340704240025840c00d141c140458005084421012030b4180400000c0710300c2840310800c143c0f070445a0080051202000c40d240c84005420300b40c480401069045d030022070185064000d40e803441c28003424600e1034800900380d403c0903041e40c100c1e00c505030040118040c085500748110300d07921030083e101e0890070414030044c00030344034507a44415005490001d40010b140c1d004150032044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 375480962 1250 375479712 375479747
    0xe010821250b0a05040b0708250e040f1b0c0803010e041505070e21150402010309020909030405091e07141306021b01050304151a04020d0b03010b010e01 67
    0x1403201c03001c0160449503200c018042c1d20014040015035141074010354802d038801c408400c07240c2c8860307000f583d840c102600d44440100c0e919948980d07a401c024080e80c480304507071070a0285080101e01040440320b070030504078101602c810302040c04c0d42c1d01003d000d400840310b01c2d2500081c551034540c030603240018007461380a1040000400d090120082606d000c02c5c001a00811203410440303000341650501a451900441402c405600d021071504000e005c81410030016020189049a800301d0710710000740228103141d0381c0d424250158950000203441000c84030000c0d03a949003020200b24004000500e40d00118500c620200c0b5041340400c074480c0c201c40c5030300300640c0a409181c10020203014444503032200309a0100005501a0300086601e041540c01500700c034154104401100c003848201c90140049805400c40d05c6d00b20f030b85070302000301c00c60b0109841358002a160001000d0b41c0c40311020b10a002c2c0c4400400105107000e2144040c1c2400900f08081c0c04800000042c140b400c81440b90b105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 375482212 1250 375480962 375480997
    0x30209010e061512070206090718020c0102070c271104060305070e1306050109080604111002012d0f0902010e0625050a170306090c070501020c070e010821 68
    0x1441c2ca60445183d0070000071003581e034440b003401c1c001d8004041c040b41d8600c0148203c0001c40c0c1c00d03d2001c07400400ba07610458503088540e8401d50100043d61000440d01c180c0c0d9406c01440011490078816200030700400e404034810003983c0140041d090a0842c105a2501d180c0403c102c0c1d11044002224100c4002c0d04011402d40d50b204130585400301811081a00041c0413445510000c5059002c00c05a4400b600c42c0c1320101e0301e440000d80d690360200ea000b00b40007500000c0350070920700303691b80c0c41400c500383c030012406001d20240d040c00f14450220311209a1098a041040080140107008200c5503102c000c00c44020309400091191901c54801c0d80202d40c0068001c101c0b200304292041c200141004242003c01d4600c0c01d140d64144081096a125090403250313080c000c40c020440f8000e00008010b0019504c4070a8481c031664030000080314103641c204443c49c00207200b0b00240004040d00c0110b808650f24105c0d650342080400c1c0c900407002070740a80d42e06a003131600000d642040c11300c26074644 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 375483462 1250 375482212 375482221
    0x3100e04050a0c09020408070618091e09230d02100b15190e060a0f051b0d02060403110102041208090a050d060c20030313050118050a0219030209010e 66
    0x141858070b4118003400800610704042182d0b54070f030300100304807101c0ba400c89080700d90301c16080f520140101415030002c21080e40c01c0000c090640c00c00410741c494000b04071680740440f0441000c48001c440111920110851400c0d081542c407030862300c42c1c078140805043c1541803903200940f5982e46496183c00c0c95070b203151001e000d40714640d00f58038845445450540d00c2c202039041308680940074139140000384e82127528901908080040d40e400701d021383c9601500c0a003a844c143da03181c001040701d0103010725846814142c0d00d030401100c2c0c964622170b000b42503903003094140284407981a01940d412030380104001c000c441c3c5600001218035810440c19922070a88000190413188a940200c0e031288000d2414028440c103075004111308031580c0c0b02c900400444102007506480340001a0090384c00501c00a0b60316400d00c00c000c0c04681c0301c4c5000107603841d050740d2045a01e08065205842a51101000d4002c506003e18080115006400f07504a41461341e80010060315050140030320003180d000224 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 375484712 1250 375483462 375483473
    0x2010f110c030312150105090319170412020a0f0b041a0906030106121505010c02131b0207080105010e090304032901060302190e0105180f1903050706020303100e04 72
    0x210a5004002c00362640c03001d00c9105884a100305032110a41030781600500e403015800303107046507039107407001d0042c050b0701205890186814030401c0c0181d0304055150305040340340c11448002d202800d01640c59036001c02c070b6030050004800d0745802c0303040f050b034070100140003800340c81050394202e692880140440c007100313950074120390060700d5071190880008000440e08580110b001ca08500c181802000f40c140c0c840194001640d4600c42c1c6c50114070441d8450000d81840001c1c0350b8102c051003000f0a50000141208204610f2a001740d00107802c41041445424020f0150074010841c0240480347c0d41000c0361070079168810b13407000810320f01504287c0f441c12160509011440054a00c030032020303695a00006d4069401000301004c054000c50342c4506003400740a031134032513120607034416040800f00d549080040c880907030b0641d8010101070442c40c965541640788101d20741c410344000300b460f280d032134a50300d00031072a0044401d5400074420003000b000e114500d00100c8011060483c1e481c0c544d030800c4d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 375485962 1250 375484712 375484723
    0x8010909080717030612010c0c03030c18030606050112050405062d01060507020a09020c06010509150405090d0809120313030e130b1e0108010506070201030e1504061802010f11 77
    0x701446840302800d1000c0340790a01841c41140e003601d148441b510480701c443d080380d040d401e0b05000f040110203000c0129200e0f6121041c8051a410440c543d910214920300b0360a1496004680d01ca0f143c00003848556032000c4060601411701c20305004c2c13070810780e551546916001304881e4050414130000654180f42c4800c414074409044d50b55101c40d61550301c001c00d1a0b1003c00268096030764084002411305070b81c4219640e4004001c00781034180d09007000c202d181c0d4405840e03102c01145082141007150360350b105044c00360002500500c0224403981024045c00300041418810350800303071443e209241040212a403000d45000c00141c000c0b41c1c0d250955003240c81c0b400c1d1580000c416030300650702440507444a030700700b101184e00c4044002c400380920041c085007116180011920130042000b4100140034000440c814180840e140703001c4a01745240012100c0034405002c101070500060000910804545607021003082d40300200c2500003815000b00c82c0250f00030010325104022003580180701 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 375487212 1250 375485962 375485977
    0x7030b0603010303030603050d080c1602010519180506070302070306020c1908090a080615130e0d05180d02010807080a06080304060f080138041e080f06070801090908 73
    0x401c1e00e03542c49050083c010324190004481d0303849454080141d40d4041c070080d03132140300c0c0603400078682000c14440c4a141c03001c40320100c0c1405024400440100d211303460040301c505255440900c0c0340346001100d005404035501081c002d03042000110046903003c6415003c0d00c0c2c102c64056515010020071a02c0e100c0602c514071809000c140d608410403d0480c001d00c00d0080403130f07078015855101d100550325460281c1c1e0b60150340700740c480e100341141403920280090710080ca00c00660103035208801030422983d000100d00003400011980310344107040ea0086418502031310300144101e641d60018280d04405071502c0f040c00482e00024014081039048070020300565801d0341e80741c2d41d86500142030301020b05041800f03e1014030011172440c0c08850084842c122098840340c014200320000d009140c980031030805412000c00010400b43c40481c21030181180050b04044020300e0800b0060a02ca075403201c0c4d44082d008803050200b180c1d880484107054801014000864041c3c51a0507100c0340f04070070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 375488462 1250 375487212 375487219
    0x130e150c0705010609021b06101208070507080d0906090308030a050c091509131107020d082808010801090f12030204120804090e0a0c060513050303160c0611030f0307030b 75
    0x1003000c145e0f0a084c0d005400e50301c580e0903034600c40904030704034240c448800300d805072420804000108805152081047c464a000301031540c43c05400d078a0302c07410060560450242903021000f0091200c0e405184400101502d207842d40503582955607586003131001410300d106640d11040400c20302c4684008607070640500402010300603100c901c04c007080c0d070007181c00a841801d0412011218440c14041d4020281445201c1d500e4100b440e401c100c0d03094048001a220644244250032280e80035102c1c011103841c00c1c030b07061203889488a1009048030781c141c000300a207034181421000000d00e210020780c4e4903a4081c2851006280d0030b08220300a01690b80140c03414200206c4090078007150300c00610559200d12402e1081d4289020307501e60340c22444000914258841c0307002c200407032140c1c028001006001401c540700075035035400a4a1900620005e4245000521101c0d0800c005106541c00a0401c3d080842003102da80c03109949078000c00200a060300300010025840500c2a406601803d1005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 375489712 1250 375488462 375488471
    0xa05091c03080604050c0c071208040f080a02040c0e131e0213150c031218140f010f0b030c04090f0204091b0911070201180b04090b130e150c070501 65
    0x2070070300a0610768141d424074060392401700420184102d4800300c62051081e440200300203881d10702c680d2458001c800c8150f03940300c020700011540c41020402030004240e000010300842c075035401000201d4048035592014020b4804d00c2c0e0446444051407040080c00710300f0001200a04418800701d242001d203803844c0042d02c0080e900b1220f05283da99602590359050000505050301403040c3e0300500d00c0e09000c1d010400802195100345215040315900740c0f07108221682c04441551b415039840c42c040340b4411107410005500d04440000d00c20484941c1600343c0c184006a06040441e0316191005074241c0a1521444904184410080303410030080c0c0c060403c0040e00320034217150700400e0340c0f0304441e40c089801400c0010154664000c448800fa400c0f10018944002c1e98015110310403050240714000300c441134002103800510340504020001e42d200428039800311000c1200514100801010443c94101c0030300041d5800602c0c0069441003c8803400d20b030b103070042d00440380c0c040c54000500360341c2403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 375490962 1250 375489712 375489769
    0x309120d061a040807031b050a0e070f0807050306101b031707030204050105040504020d0f050c0a02010b01020610090c0c050706020102040f0e15060901030e24011205030a0509 77
    0x1a911080403070b4801000c510200c070034240600d0070b500c964815a6025484500b051002c211240c0c0024006003048040340e40d20f96030742d8007040e074070a1542e00c042c448590040412003540d0b04010201140d00e102d142540152a040c88040e10f140409055180030308004c0e0030300707090075005906000000141a2003111035980f140350003040c10943d250b111036404501404207071014040e0003070342d064a0050310343c5403c040c248400c1c80001e4000c4540c0001c0e403a15090444010302c1a0700c9100c0c05080e61500700c0d6650070402c44040d09440b000c0312039034111741c05007042016150107951480280c8038aa580416022200b00e800c490841c840076000c1c01600900d00001035282d0154018001c844e0a401055407180c5d65203aa04e0441c002110b10a1061400d500c80383d845203445801090001c07014140000c13048400c2008914002c80000480e602c00d4840c0310008482c0b62507180207006107042e0f54080400700640d503840b6101c0c082d41508000340080401d00824598901e500c0070201c4041c0c03990185034111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 375492212 1250 375490962 375490987
    0x90501061401030c1103190e0607030c05070f0e0c0c01090203150702100903021902150f0418050c0a110a0b0f18010b060919050d030c110103150b030912 67
    0x481d168680864580701008164a001c0c4c0d450000040885002d1420603400844180a01c0c9121407168200b105504010505507203a20140003910b000c0d83ea0401843d0151030b1440c60480c1c9500001d080800c0708000b0403021411007800343d4408003458800c0c2d104d200c0b105240b070142505c4c1500940c14000c84882c80c15000118071080c3c4169003d908035010000c01003002340840f8500c840290040c1c00006440c59240074841800f5080e42c80a40401e09002e0805880314040d004400c490701c81640009080110510305041c42144082901c070802040c10b000e405050580324040c20101484079541e00703480742400501100000c1d0ba04403201030031a26013100060082401160003081202402000403071011051142c00c0640b071001e00510315001500040194000c0c052007046482da00d100c9011401d52140c01d440b040e041e00c240c071044014101468401600310304c1000c2c560400d8a409502d802c5003e525490804440390150708903525140d00c00d02e18102200003c1e04c500303a26001520604554 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 375493462 1250 375492212 375492239
    0x1a030a0506100c030c11040c0e151615060902030a0b03011a0901090b2b0209150a1401110d09050a0e01030812180706030204060908240a09050106 64
    0x40a100080110703540e58010000440211000400068218150800041d010b080d01c00ca02a000b80194800d0950100014080c1ca03480340702034000800c4100c61260600b0049807600c0c036440f00040950905240c401000300190103400c01070100e01d83c1d000034041f822100d038000310250541c1c28041d5540d15010441001070036529000c0390283d8a4009501700022507410f00e600c071004000d12050183e40b03000d85c4500a410400c42c41036110001c08800d2a0038603000402c00600c11101c0102c160081c41d9004104098070000d0812800e03180c10008415540c0c0c0e5a0901d20a030381103148484810180710340100c0304203082c40e44980151040e80c0451890640240b80d4808907501298280200c03034a44031929141c070400e100050121105122000000f810010504c6e8400090f818540c003442491000510389405944042c0c0481c0d0300050034443c0550000440025201c6032008003c92051b0440001542d402000300c0f04200c1c001101060418101c3c0d00b007440160740090081c0030454844560800c8072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 375494712 1250 375493462 375493471
    0xf14030403091701051303180b160501061a0a08070306120f020a080316061805100209030d0504030f0201120e03040b1b06010e0705030702030f0d050711011505040b04061a03 76
    0xf080c80101d0040d8004140541780c03148035100400d58020701c996a0a9924803041d60002002d4102c03502c000c5000c0d4001d01c040e0025070f0401c403660b80101e003542456804c4030aa500300300511f040440c40348003c0f080d01c0c01181d00d004600d2601e00b4580ea16800218020714981d0400c54903044100344a5003403020790203030380017503c0c000c0311b2544801d030f510507215581e032243e0b416410b00704607001400c4000c106a9030240002c007a46103524140e403a4150b5469003006209100c01c54482e034003007000003990600300a2610040ca150503d10718150950725012080800d803c0000c0c10003104281c10703280c02c469504010703420b543c0d03401140d07113541d02e0300542091034000c08000d41d8141a1042040c06e80c690000700c5030704807007030200400b0a9845400c8110b5117030f44000e1503582540b004206044034800507000810034090070380c40005e610b040c1070b030004020701e008043c21400740c2c0c1003040551002200980d0316040716000c6400080c0a80c2030700128002d40184d502c130b540b640d2802d50302c2c03801c400400002903104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 375495962 1250 375494712 375494729
    0x51e28030501140f0d111503041b0302062d040602010902040f090b0613020702100903020907030c0e01030b0109090510030b0a051603020c03130602100c05030114010f1403040309 78
    0xb680c03100394010020303125030401c030344c003000180500355a8246000c0c003016490144411504d6001c4000201d03118140010405a281c100001000180040b0700e4030000103c80810f84280d0491842c4c00107070a5005070400d0340c030700c41d0105441d419610100521121150701c4580d08607150360741c40c50b001e4000c10744144240d0045083c400b154000c1e0100c0d01c1010180390740924103261648410050211210309a142c00801960030003d00700584e80d03074401403032040b24030380c0d8002040f0f0a602c140086524050100d0050504000401104581210900a50b03100c28a800103485000c0710040328101405d9018628251420702805002d80003141c4c0402501d0084501c15500c0e203c10000c0412030b88100c6941e42c01d4600385d642c8400b180e01c240c0003040d004505500b20383c00c0104101c54181d07000c12550080025a01c05c8017440100030075030040d00b8407280103060203030640d0701d06481c860030045900c9085041054400d0f240000e2405032030070521540403440b0180d124601403074094607070155401608074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 375497212 1250 375495962 375495971
    0x3030901060f1a0304150f02030a0b030a0b0f060d02130e0f0a0f0209040204140708041110080402090a02040308040602010e0c0a08190204020910020a0606060305010303051e2803 78
    0x1c0342d982c2c40504000312074500050f80c03482008128920391941000d041120394a90103807440b45080245d001d095401b0170207200050350ba0608003101c03401c4410114409000c0c3c1c000030001030100d01440b4401d03500c1215580c0d540860b41c0e61174001104400e040e0002580140d0441d1060140c0e9015803002403440d0079501110314640202a44658034a0840c0c001492040e0983d561001810030380700c02a0480c2c03000e8004180d1594010305240c12900484802000881180401c001e02c8442212524524415503034120340d0301c0a604010592071009001031f0141d4032071808952140c500782c0c1181c2c003c542000405403501d4640d50002d004e00705010b43c0604a10800559412501d00300c541807045034100001011076009403103809022882101050342d02030343c01d018000305a226014a50014520b69028080507070061410404039a03c5800c85801c00d481c1a0041c00002c0d000011610042c1c03080150070b144000d10303a48c0c002c10b40309a00d0764403916900b40c00c103d150001d00d50381d03101c8019100d880901 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 375498462 1250 375497212 375497219
    0x50109110301051e0a1d07020114010812160f12023304110307060903060608010b0a060c0c0312090501110105090309010f121104030b0c0a020a150e06090303090106 72
    0x11014003083c002c2c640d200740055003480d81d0001202d41c0124010300607181d4038125a07100c3d0110850581c2e80d64184101040b8410002445d03428480c444c11501e09844610b010750401540c5ca554180d071081d0208484000980e000f0755200b0300c6154407650342d000b455080e03240031070300d0101d0081b01d004445d00302610544105c0c441ca0150005088003500d01c41c504a240c0031308c100f00c040c1c07240e0340183c01500c640143c0110588a510103001d00e501414240d100d17140428590302d8080100d0340c40740d0020300e0b143d1400c07410005591b54070181e07400320750380c0e86080e8083d00c01071308008201c0491076000810f4004450601001c280c2c0081400040702c0b02620707a420700040381d10305039007030750b03000c0311403a8054008000b002029030082000060310b181a10706200e032aa1070300030203021289400141d000d2004003040400802a5882c0e040b5800743c2001340e501e00700720305820044d685000d00600240203001d44910f030102e1140315803000051444041c100c0d403450501d440d1440d16903005070f4001c11a54200003012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 375499712 1250 375498462 375498491
    0x914010603110304020405130c080c031204030b0c0702010908070602150903070f08030a09050f010902030d020a12031a090403320d02030411130f0b0a05060d09170a03050109 76
    0x4042c201e0009031018503650702ca43c00c11006040061101350501035040107000890000d89030703940580803050007404800305d04400c1510300000030284085c0100200002d000084507a003c103034001001005140d1514175900c01030b140c022681d00032811a1164000005440390700240c1c0d20f0000300402031f0180d0343d44500b4080c940320302c54910043c2114440f41e140800040e00000215841003981030000340100d07160f602c0d141042810000d03400117039161450030055140030b0040e001104450b0008120035005640c03101e1a45040d01204010f155031100200440310945503060101180140040074903d003d24003d01400c1c0c070589000744000c403182a004a4059a2420300001150303c0f18283c01c1c995664001406580010b20031a88090414071100c11034950980010307010711200c5e400f282c51202c42c00c00700202c0d020059221b100781e80b480f5041199464030f1041b02d13940e05140b1004640701c0040d081400c0621540b1005010368800092001101945944244d059500440c01440b042500c80501d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 375500962 1250 375499712 375499721
    0x706030b120c010e030102090a080c0306010b0301061e0c021216051c140f010c1709030301150309020f1c06060b18061b120304140f1b01050403020a0914010603 70
    0x30000168030140301035038150f008204d200d404c904020000344c5881c001c900480c243c00400d500a40305540b00c01c200c49401e2509104441c094a02400c5040c01c540c0340c20001071010480420303102d0345580c84040b00d12014480c2046069258015083c0055508880e11569403600400300500c0030001809010070549412003640c261110600c0901020f00b0150f1130341952002c2411144504e84210411111050800c1c000c8510780007160301e0301c04000c401c0c0d411031305d6440b10042940100d0f810800040c0018523118500d03920f428658500000c6603da1344c40071501c1060f08c11384150f408000456140019422004001100d51041070306101041d0380714405841c50243d1030046551520201c624210760030b01c1c20150007a03035406d9610708038540d40001c0c001d0901040c1b042008044a0000c00c02c42407110010800c4a141f103050020901c0300646075850b03484030051500e0301039105c2c0c91a11000568420010396001c0c61b0000c11210b42c075580e9840280040001c10010314984000d4800003902c103009108 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 375502212 1250 375500962 375500989
    0x40509010b010e04020a051b03041a0a17040228090b010c0b0109050c07080a0c0b0609060901031203060b04090902010e011715010c08071202010518120309010b030a050706030b 77
    0x15422034003e0000200f01c040e4000240d01810006c2c14829010004400c8620045181001c009150341314101880d80c42c445000d00845600708604020b0b45055980c4040c0d0b03d2078068100c400c000c040e413100e01c0040c41000401c0c2c45007800c0c4440c0e41191b03c502c00410307100800c413101d0300d41c10055911684011754046116040c040c00140c2c011004000350080b90300f0050303021561040c100d250000d9581c0c0c1410795046000c2c0714000483e880005000c1048604085400c90070488043c603803850300d4400a401004140401040e0308800e880d6814424081d40140c07014101c844020364441c1d131070b14280d40050410318000ea0000d07100c1380001c3c52950294030707506207440151a01c0059560303402d154504242d420a055810805418072850100d003506000c0c02501d40301e5031424510480c40c04009003511809002e6902c103481440c00d00d10300803000180e00b000110500e00c5140c0303942d1842c1009004003031b0001030300c0c6c040c01202c41c1e043c02c0100c04102c100c25580244c03004c105a14100007880200b94003a003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 375503462 1250 375502212 375502217
    0x61506020106031112010e070b091c0f02010e13060e160503160c020319060504050610050f190b040b1c0501060512090109021f120b010e100c0c14040509010b01 70
    0x4c844406a0504410107401840c052001140350301040d002285820240d03841000c9058020544003001d15010182c405050520b10010119413055120b0383c000030b074101002418000e9100c002070442d1202c0304c55003440c0040000811540d5560b04101c041200b044881c502070044e00d0006504030740c010703802c0c0c030300035015112040030740440100141d900d441c0d59142030b60b0500c02ca17101400001c60401110350014443c07140400e40741020702d0090f20f45000a0140507180000610500c25903c9500206100d1441200d0b94401d0b15001c1c0d05005442041c0d801108200400007000f007054041c0d4001040c00250140c1c0a0140071a00600030003100d13003c0c043d401c0024401c00020350380c18002c507000c070341104c0381344000159540990300040c40303605403625a908022020460901490f008018190300600104081c403581d09500b000a0403c403469803100d03c0380744150051390000d8421040c1c3d0000300d40c440301c9907a500e626200c00a4000e0b510251542c85242800f00090103d034042c060300c2c0c140803045c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 375504712 1250 375503462 375503483
    0xe090c070c0302060d110f04140306010e191103010602030a0206010e1312020f0f1b090f010b0a052104140a05070b03060409021c050105010609120222050406150602010603 75
    0x10b900700b03c01d5910124a02030700396101c1240e262001c1451b401004403816000070207a4492801084000002c41c005500d442a000340004103d124296401941d0081007000e043d003e54240c0401d42d4000d10f0764015a103015a004030000c90940d4001000b40102400307038080b9010f0703030381c1d9003c00c3d0360044045030840c004034403c0440000058904444680c840028019295604200041c1d03e1500e00b290240d01c4907548440e5481507010070306864040c0800c019118141c2034505136010b42c081c2403041c895a0001c0000141804589105006480024080710440b052220035001c081003110001d5401340d03000020000141c1c4240d100003005298075900c01c0142074010710b089414002504010701c06a04035491f0045200169101c001040144005001840d2903c0707050034054212a4141c01c81800d1200881041c440070b000c0d4a000200158101e9540702604141c901c84a540144a040c03500c0080c10701040c00100b01c111b802c10041c03c0c6120350102c04095a9400c100c0c00c0c2c41c5c1d00d10015107800400e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 375505962 1250 375504712 375504719
    0x602100908042403050a020c060c090a0506160501060509060d02010c020a080d110607020105041a070306090e1c050a0f0c020f120f1212150109030c060e090c070c 71
    0x5a00300c0c0c03880301d00680c5140d0070180c0c0c402d07401c00118040707034442103641851505032a6142e018443c140c5c1200b0000c0086085c8046044400c2c1d94200281070a40403c5010440302070719071307400356880050305010f00060380b42d0030700500c08100c92103030000c00c072119401c0c12030102e901c1c108100214418003005211850340801c0d50019140c4007000341c8140e0304000203880118a5550401c044030302c400c42aa1900032845900b1013141c1007a0003c1c0c201c00459041500b80700c0426140401d07c02143d14499402150b600c402c0000d5001741000c0c0e01604500b030416940300000d00b00415000304030b014000006001d114091001c45aa100c2e07240032001040c5407481454400d485403d50109891000c0c2c17110355030440c00000102c45005900444c0500e600041c0c2c8041d141d4002d1192410820020b071000f8140141c074070602802280c014400522440c2c0d440340c8030181e03880340c25040d005541107000391121584800c8010940e00d91f0310745150042c2c07040d10214040039012022a2860741d04a5a680940c504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 375507212 1250 375505962 375505993
    0x1180309090b120706021e07050105040b1b07090603050105070f05181804050f0d050f03070e0f181005190306090311070806010302100528030f090b0604150602 70
    0x4002c1c4290880c2c600e5032a0100d001c030800140c005402240c00070003041d1903000c00148502c0407540290555007083d2002c0020381d80200940d400e6607002680103448849405907a210040e00700c1080744103201e000c0380010200300a0344079070150b1b8064002444180c7e00d200c0e05613546e0242c6922400040d504010000c56484440c0811030242401000c900c2420392102202410071420750b0141c41d180c2010a03450840c480c01c11071018600543d00f021401c104030b01150a000e0b0100510b1001448107499001c030306981d0304c00a039415804020320810310f820000f185a06411011119202241101c05010880c5c1c038200c0202c02806c0b40400716400101c1c01c40d5142d402610303c5090440910480310701105000700244a450b01a07d0800001c0001d0762450042041a482803a902d02c18000c00b00428a40c070b11080480241c440f005444214010700780c140114024159500f10541540c5000c20301c0f02004608031255000ba4002c031411b00032444415864a03d1280b1031241d0380c0540d001480c044c49042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 375508462 1250 375507212 375507221
    0x3060d06020d090206030c190807050d0b041d01090b150d020d0615080303040312020319051801060801051611210403020d0b041202190b09120c0f0118030909 69
    0x28075225021031000f54a50202d01150810f5481295502010500031015086040d440102d815246000e50381c90400641c058064030400e400d18070455110a00500c0d50f4035190000e88160102440781d068840ca44011140200121401200c0504824000c6103800c611160384940302d160042444c0b036901680d5081003c8903400c14030171903030aa00c0d0040c5110b000844581c0c10010601007019595070719203441c00400d0100d0600800503c588180b0a022100b2020b0443c03408035181c0000c0000c0c1a00c2d45c019403405ca00303c58289031071b82e600703001000c0f903100030642200b8050166010b01c0000d00d158010140c0e0b40001210b4105295402510030a40300c182088103e201e04504940903850075844c1c0d000b0440f12001c00314241c441451200c03e00c0100700000c01c00c9166003800b44058038031074072203c5000114644c0c0c0720018010540c08c40116806880034040c1048200b00303882c1c4190340d84c009080c102d84942108034040081d518200c224100c0d0034114581c1c0b0002d41d4075680304c282060074143c03060f0050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 375509712 1250 375508462 375508477
    0x38030f031b0f010203070203180306070e1002070b0c01020909060f090c18040c2724050c16030212030f041503020706060303020313050301061206020309240105090a0203060d0602 78
    0x9102e14050700072800000e10007035010340350544c00f9594800c10000c0e0400e03890b00a50f2941d02990050b010094000c0c4e0003903914014140132070300010080000c0800728540310803900a9a120040004c8404c0014415030007000300010070390f0340c03622039a035290420101d510300c0c101407600000c9680020388580150002000c15490030101007002803040404501184c85a403000d0001c105016070100500710005065a00918007010460360386007020003034404248009200c090a04a151841004600600a07500c0c1070f00c4003800c8410707044550500c06c0b95004284026070088081100440c0591008811240c3d101c0c001d40d0801c0c0f520745045c4440b2144485503544e242090f07801d102030b000140b10760064400560207a40250b071140010032840e181c0401e140d1200d80300342e00d0203100f00300f450201d105403500d03a07410100058480e91500261414880001d420131000f000d40301c09900080c1182c00c00e00d0583e0004c1d501a1410b503515001c0078202e20040e603611383d2101e520020440055490703002403092 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 375510962 1250 375509712 375509767
    0x1404090f0b010b03010303030e19030315090e160509160f09080615040506100210022a0f010f020304031d190806061005040f030803040638030f03 64
    0x3100d406071240c960201c1c00380c005020003000000104185580b5020300500d000701880a44448040d107000c1300019201a9001418151606000203d800d80c82c2000001007840603014021640130f0400c1d10707214040a0009149010710000100fa282845000c9611a0643c3c0c0c844034a440c10240b410349880140340458030401c03502080100311054240142400f030400c0c0c8102103070488001c0100300503550000d04290140c42d01c0c14089a003903a000603040c003499244c540040e03807a01118420704040b29551898401c01c8941000041e4501001501c11140d18100008210300508031581d241070384000d58000d0001015280d04600c0e54403000742181444000809103e80388104a80380c001c54421a88851070135000322040041600f007200d03a06244d91187d140c01490035040607030341144e8107101d0000ac1c101c0d50010000504224045e070280e0039100008628040c1c0030100d4501c000c501140e0000c4014100401407101614140081d20801c00b8281c10003640c200100f00219101209417032003048407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 375512212 1250 375510962 375510983
    0xa0501120b060301020f070629010f2304031407090510090c0e1e0a0f0303080c03040807170706200a110304031703040b0117100228030b030f07140409 66
    0x69100f5035006087e024802c3c440071903000207030200e1848070202c812010409403031100a00f0816030b80b066901036071002c941000d03800c1030070780301c0c00340060b0010ba10000040000050013106000382103c650511038101d4040710800b0340c40d00c130f03030100380d40003910a1301024040030320038015000d4603009580c1419243c60a0106203041000180032800e0248191001c0c48240da0840f03401e0809007904009840184039110300540f5595000749058801001e9881d00760011001c601040b8052088502c000c5d00036a002e00381045120149480341c0c000300702142d1091814504c050a443c1e4200c01d040d40380980c498107414002d10610681e8220318521400744180801c020120004822900f517001c00e10135003a1a50b103d00d0a071a08808840b01a00003004d03000030186006908140002c405884084910001da00d5851000c400c4145c511a04c512442440302503514807007542d03140d4010084240104c3c22202c44640280016484109900440c0b03000221351011f205e01d03003815007001103414403c1c80c40c00c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 375513462 1250 375512212 375512227
    0x60501022a0405180106120c091107060908040609080a0213020a0c02090c0306120312160309060c1101060501090f0e041403030a0203070f1403070305150301020f0409050a0501120b06030102 83
    0x3412100f00b01d52042c00742000c00030a03010070100740f0604000c0d00084e0000700c200e41560702c400150483da4031a00155545649400302e0004001094502c403681c005420b100300000c80c034100c2941d4205005c1c28000901a003800a202c1c440001c4280026802070101507284581d045607a002e0750040030702c0000e1100e50304020006840d10940103100b40b83c20b860050312402c14108120340b6000900302c4100503070081c800344100c40b800075a030540043c00745001805000040e42c055000d0f040101000d04600d1901da51451903e800004110481070404001c200003034948005551030482402461421543c0072030520200d4201c482003034020740100c00020280000d0b200262460740f00712440b030b0321a03402105102c800c0307402c44048590320300702d41030442e5400100c0c408024103000040000c402c251300d48011600d00c0c221403c0034445040090000d55503401040e00020b4154403a00c01c07412010b10784000541d040003030b40710301c5050300c00b10321680c880705416895015900e40c0180031540d01d55401c000c1c46 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 375514712 1250 375513462 375513469
    0x60313060e0f0a060e0c060306031203040501111206031011120a180302030a120504020f0d0f02030111130b03060108071202120f010e0a0902100c030c050303010314060109060501022a 80
    0xd6036540c0c8911001702e201301340c120300541004002110103010701014024401c242d40c01003609515800e150301880d0f16035039182802409044421591040e04100007400820703d03030103001042c4520002c0d411141182c184030b46280845002030000c0482040074401d1500702d2103c40c04079600101031110119583e00e07000040d0021f0380ca404011000741e03200003506201c05400080e640800e0829034800c0000d840d064000c2401c008200100c203101d80c2d5601524020050f025080c04d130304540280081081700250b80c8103101c554040b05c05280030210451000070315100305c1c4100d0344595030617540e044041d110b4940c03d40d0000e09000c0c00207102602480000d000d113000f07840941c8036200701c6110f25415494580b5601d0310396006000f0b129100c0c180341d000b0003d81c8504502c003018100c1860070f0000380281d410202c44400c00e0100081141c000000000144a40d548804c154031a041c02522400d03641c801c8008100d400324890319025030840002e0780303100c02401810f003983c030b6640004d2042c1446001e002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 375515962 1250 375514712 375514723
    0x9190c0f14090901021222140c03010e0105060f240d020a14070f290a0f0c0207030f0b18010510030510020901090308030c040b0a08070e060313060e0f 66
    0x708a103044049480245480c156101680001505000f145441c1e4046030a95020303a004168030b007071220000391a041d60303103401d00100e0303400d03081400c0380a01c0d108444040d458001464241c1d110398203101d10402a501d061180310f029401c020034202c0d25a001006011030758055100342c0b00300340b5807000980e1840040000500700001030310001641d503080c00f00068520f05900c040c043d290340041c800400000d018451745400990044c4020001944c030346075500740b40600c0031448031840b5452060000001150b04010503c0c44040000c0c0304801402d042280d0b40e07245488090040b001c1c80c4104000314000d5010700d50008888950040f500e041c2514441c02c0d983c0070f840d00b00104542c03a02c05c000380041408050317001e4517030b07450551410044000084c00100b050102402005002000c1541440414204d4005102040400d43c94020500001d444c40004890303030004100c20362218001d5251980c2203a111342d110300b080007003010f11911072200030009408584850321039400140c1080c08100407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 375517212 1250 375515962 375515969
    0x2101b03020c01140f1206040618020d3e130b0a12020f070311010902190e010501020d050f09220603051c0905010c1505130b06030609190c0f 62
    0x10429661100c0005040c2100c200c404104c1d00f03028005094496180c9048480007103c9602011040e103807040080c00a0a950b0b101081c1e0114a40d1022812000c9401074442e45004101c10460818080d00c0103c40a0000381c0d07549402040068400502d01c1c242c94076400c0c1c2e40c038883d1050030f00780c0c203008003155000e01e500580203201d4045078445503980e01c03500d20540007842c00d00542c284001c0d86000e0f42c0038011514000c0911a002946c00c1081800754000403044c2c0c1c00400c407125a0741c04a40025200b81c4902581030800703009000442c840d400011410500c1041d075a4262030440185580c900ba500240105507108800c801c8088803103551800480942c8541d520008149145140c1189851300d40307150a50301298407401c41c27911030742007840c1d002111000c0c21f00024030066458803020410902e9032040e1200d2038002400000c0444094100c0c283d4803405084041d6112001096540d50088030a909141d0064940340c10040c9940038085845104e5004045465120301001e1801c0640f40c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 375518462 1250 375517212 375517217
    0x70c0c050d0f02090709060e010c210905130b0306151314060307050102010e0c01030c02150109060611060402090109020c03070f0807021504030308010b0901200f01230402101b03 78
    0x4441c1010344c54840d00300340e0005078508040102910f003510141500403807605003810320100c52040814028942e41980d20000e000040e6010361107629405041c12030580546409460702541003602d100161003443c9403180b00030b0046c8026503407203010394614204005d0182e00710000c0007103090074400d107004080c08044e0406040b540c520b04002458508641940524110782c142000d01040020101da0780b10b6000007803901007000740d8420410380c40d00340021101000340704020300004048016510500540e4410341c2e4103000e074016442000e51f44e003402c0d036002e980844044010044843c0e558020040e12076018241c0c0c2c10034000d5191400c0140c0380900c03e0341c5055002564008520702502214884104074800c1d074101415605c0040c10304805024003c032030b5400044a840680c051000790403210010343c5c100031190010a0b1036902c3d040100100500c5609207021055149090713a44000000325012a0491568070f80e000c0006901d4410218020700c211414020340b034001d41e004150302c46001c0d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 375519712 1250 375518462 375518483
    0x20a02100e0c0913021801060e190e1501031803090906240305100f320102030f1c021b2803080415050702010b03120a08070c0c050d 58
    0x414030940309240725880312904109900c01480d034031005000e070040856a0322006105084c804204101490840c4004a24115000203010f542c058039a090409096074001030340010200e8442d84030105006109200c4003d2000907001c02d40800c031081c05200515003c03460340d0a0900621400709070520650010744007010910480d0302c64028800203055000024000640d680c110a000303581746108403040688580102c4c060000401e5410043c0c04d801406d110080d90301c411050026052828403290540401d440030000c1c5220309c68004142810b03000b440c9810070400c00d82c80e80e030f031000c03022080c0040b00f00b46500008a051025000d203590800c030100c01c0900701d005044c500300e85500510050300107500100d03607840441b003454080945c5800d29007426140e51510101014169600c040341c01d2a14041049032a4150070564043e002502601e0101d0010a48884140304880e88880803806660100704194442e02600d002e1500402520038041d80320000512104070703203c81610f82a01d00d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 375520962 1250 375519712 375519733
    0x40515030a09150b030f12041e150e01020f01050411041d010608010617060105061c09020915010f0503040b0411031e0307020109090b1f1701090e0d080c0301090b0112020a02 76
    0x8001041c80c1004517002002c0c004034a4a84000c44d1240e80211600509c1c07001c46005d140c556003c7d001c014001501032546c1d0b500d2800001030803403d03400d10280c01032140c2c030308030610094103104140c000c9810480c0305c5840c070418424440039042e03144240c071140d0030039800d01d42411404e114010103000c8020000c42c80c01c1c1b400c002c412030800c90030541e080c59007007880104400d82e40d00e021034120030042284228204c21000c454002480c0d0340c540690000902020000411241c1c1101840103509880300845908000402c032514042110001d002c64038960100c0c0100300b910724030f500c1c0368100404031038030312802c81c2140d604102c1e020b10008441d840031560038110b40e0004800c402600c0301d8441000f1014414001406800c2300041e0064150494900c0040340c92086664a01024081c41032520550355250790100030405100552414055100c02844003449051030601948001c981e035400c40c3d0031f01050724014003d408a0b030b070611040c3c41000f42c0d8645140040c0891480c00d401405c9001c0780e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 375522212 1250 375520962 375520969
    0xb1801080d03060b03131e060f050109060906080c120a1502120a020324030c0d0f0605133309051605031c05030c0d02030f041205040515030a09150b 65
    0x30f19030400310000c80c0c20300030021520001c981858000c2d410511101042050186085441021840240199060001c414116529a00a039040f2024a44208415030351140074100300e50841c000e1007500d4104500500032898450250110f490b00041a200a801c1a980e102e180c40c11050445400a4000c0741e41e20703100007a070241e29407010280c1d41c01e510358074148100e1b44101070055001642d000c0344090b000865101080054101c00b005002c0c420014900e0802581c841d4030b0344070441c3e0707031070900001601c0d6281d80004910040d9000d401003080c4e1070100c285c884045450901880714500b50000700300c2c1d01ca0240121450a401903001d4802e01d40c0030010813003000c03c141c010034080d0b03100e010421040c0d60030b4001004400e540f0703d41103807070f038480300300c440803a104511104000c1030020007070010354200303000c1c00da008500c00c1b4500f00242e0b4602e01c0996050081d8810141c3c01000744402c0c4207015070b0f200007944e220001200004180026581d04482a0789148100d072042d59a146444280e09 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 375523462 1250 375522212 375522221
    0x6080a0302100507080612122d0405062b0507090e0609010e0a151707082e020a11010c030606020c240c0f0a03020604060605100e040b1801080d03 64
    0x42d0004052106243c000b1010b0300404028007030310300034031002c0d4203849000f206210000011202044091355000644001c51003100100c00c07103107401c034100c0702a1030b00071040000c903001c840000d42070900f00480d40440306034583c02c80d402081006a4280e00ba0405521445510b1082c8a02e40701c3c941c260703007411851359401000510403801448801c1c0140181c6042d180040d03445500c1c0000401c0748a101d00d42404c4000542d4445c201444420804820b40980400d18205940c001002c6500300b840c5000750036a1051688140c5510080801c659102d0000301d40040000c000d09041441445c4020455682100d20110311500000d944d060107102d43d580c1448020387c008400c80d0740c05d102940050554441c0303031580d5841c0c2da6880c1c0016203801804001d001c0c18000748036400598403404403a0801075100c0100301c0d8211801441d1500200d80740c038000c81011103a0045a4070002840801c00a02006200d01024540e214201e020030501e041c070450700c0140604000c00141c40850300300c080260955 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 375524712 1250 375523462 375523483
    0x3050417070b06060d1806200301150c11061b0c0414010924060801050a06111507090f0b040509071707050706060e09060402101d0d02040f06080a0302 66
    0x103500304146030110b1541c0c02d000d40c10550071510f840c0e0380c0380c0d0580043c1c0102207403540c038940207600090074000c0c410b81e81c1c415000400031624505010612800c0c00d00c0c148000d005880340101c020021020f22481203203044601c07440340300d0a6650309130321000a0340d550002405401d0500f040900e800c440341040c0420700704601d05a41c10f1001101d003010395442a030050003191207240c0d5841c2002c80c040c8401039038103414070048002c0d0100580710b2000030041242402954050310204000043c91031203180843c0c00191054050700302a04081000c610b48100502030408001c001a800714886081300d07a1140113140e151000b566035494613050100c400300042400090112242c0001100744190710910703885109071401a546100c00d144c68402810359410040c1c1900d01d0408101c0417400006565010780c0c0212000c50180910b03c4084800707078650341d6440d000c0c80443c02e000400d42001815201d1151000f08040354125685041c24103c848603405000d41b07621800000341419014060041003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 375525962 1250 375524712 375524753
    0x50a1514041712032a07060504200f0904060c0c02040216150204080c10022b08061f05090d0204020a0e130c081506073e10030b0307090c030504 63
    0x442ca00070039030010211401d2804110340c040c403201071404400545c00c580d00d0710303440070b000c00507814541043d94400d080651640140d00440c1c83c000424548404190005c61005102c0c0c001c0d55210342c0d9080c0a062815002d009012071800b10700b0051340d0728006044402c4540941c04080302003030410300121090f958065008520401091269481c04034100c00c3d90001502c54040c090360f00031041340b90000c254010035030f000040250403014404030034075031280c800a94940b46662900e400b0810100801c0002c90381c00403444071031448490088001d8003440d40000c0131500180016004101603a000010900000305942c41748421442c04640b41e940c0c49058002c00c000300c02c0d0705000a40500f1002d442e150034248200003d040a0756280b045034807a42c0e0203202602e000b14160300c0d40001c910006101c0b085450b00803401502c04885800325180301ca0010030b1a07030b40c0301264100350b00030410b1001e030725010700841101194a0030715015945103101140e900048074170701400c080f6600a00e0000541c80d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 375527212 1250 375525962 375525967
    0x501030501050d080a0c080408010606030f0209030604030e0303120f010602010c1b0602030402060705030d06080c01020d171305030331030210050a0204080d080a15050a1514041712 79
    0x10b03a12000021003516501c020b107203903202070503802a40c5c10302c60340000511107000010302103482c2c08190003d5044811740e4030180908070002d0b944e081a4010020703015015407103040000c011a21401c0700d2215181c0180c183d80c0b408921300181404c24ac0116503d203254501400104000b0350b0900c9014103d0200745418000c6500002c0301050940c040d140140c159074010020405640d2440c0440c1d03144c6d94000c0440b950f130a40d0303001c04030142c01d443c424034080d0b01819001048a500203e0504030480b410f90703410748480801400340c1d00b0708038041c010060024860302e02d070000490400045001d5503614021410b0292900d02040245441c004c880745000c14204101002035000140c0071000709074207a01040c07954403040410024011940303e9002441a5900442041e800031000c0b80230341c0e40c140003030040744c0b00340b100200341000724480d40d40c110f804100d040255101d0703582210440800c030700e40160398198903a070715140c03604035400142039a0002c1040800c401810000c800c4240000d010450 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 375528462 1250 375527212 375527219
    0x306050f01230d021303060e0c010908030901110102070803013c050607050a0203030d0207020a0512190809040c08090f0f0c060d0b0a030b1b0c1c0c02090a150501030501 74
    0xc2c002c4100b0041c10260b468042004203003084260103940540b404803040203022940c908100000e0003600d80405800d0207100c210b45039651183d904c12080d5a504001140b420754000c0c01103555008242c815180d035542401a403000901c1400114002c01c0280e0118404000c86025007032002c0d1580f001102840340e0204540c20200807045040c1150380841c0d003d504d03000c0714101301c0d080c100e0b21b0000a44c1b600000400d00000825540a07024483c001d0b50540e41c0c00b9100c209204841103a0210141d9070b60003854080c0c0040594130704094903e22540405007011000d80c045000c1d070300ca00c0c00d4007010412040403c0300c00b2008200d5803201160140080c02e1400c0c1c5054500e4072000403000d000c0c001e00e40000e00101c0a81070740c106100401c40034100d16100b983d2070030f040d18005421781c0c144110f02c2e8290010007541000320207444400c1e2620000d4a444440b0580d005210007401c1240401d002d00d01141d28056651090b80038464440504041130003070001c8000b1180341701d00d403c158141841c240051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 375529712 1250 375528462 375528497
    0xa1703160c21110d08150a030c12021503040804050f0405060d11040603050f0a140d02030307030923150a11120c040e010303020d0e040902010e0f010516030306050f01 73
    0x1042100b41c00210007060b200c1003012548101030040e607001c9485000024a2980c0d405000503210341c04180355078101111020803c600d079401c510010348511a40c1d50240403102d45210b822804900c0280320038440304041d401c04500e500111801c0d1207010011a0400c982c0c1032804c00d82c1d5095030211020041840c1803c0041e0071541940c030041c04641d038440d002d01054480350300081c0075580003000c4400ba02c00568407195100148901150780c250407100c0042c4c000070008a9114815241d006076056070b8901208034001c05043c0010303180c0e4508580f60500d000e006038032000300582c03a48090302c2c810690803c0b8210b989406405032801030714140d040c0303154180c440c003a1007039405000d821440030345070303140707486102c0c001ca4019201440344c240000041680000d1540c2c0400d41c19220381d00000761650803c4100c4a5080c0060f01050900c0e418a80350714000d41c6c807010301a014180142009604450f4802c5444024800c4001c00d540e8002444207240c82c00b6001c9450600740707000081d003030206050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 375530962 1250 375529712 375529733
    0x7050301050a020c0a03030e010b040e0105040c0f0f1505040b0d09031116060c11030d050a03050109061a09040906110c060a05090a0803040303180605070807081012050a1703160c 78
    0x6d010541d82c0d108040761440e007074004c548640e0000b0800d00c241009008507600030720003900c04441106880c030001544002910000b4111000e460508500da480d00c21001320210200442400f044800c0002169804a01300a4550002107680c001601d0748945805404000550001103142c0e006482c01d80094150480d1031081d90194500151400300707510389074101800002c0b01030340c14040d044080070f0803503002000c0c024282840c1c0c0c00b48000c0e42e0b01c4c01120211480d034000c2d40340d000054828900e00c2c0700c1510003400010700c00741c0300081001054440d0407c95070b50300030301400018009011461001d04108203030304600702c0c040c10400d90a01c204080d0740c50600460043c011f42c00440002c0c1454001c0e40001c4082c02d461151b80c2d0000ca651618a00400080701e540c001728100700082451103201d5100b09105072494000c40c4125410300307100940d0921020002c4605200d8500700c480050500f000300707441e030091038045a4890601419051f0b440502002c01d40030442095910000310341c07050700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 375532212 1250 375530962 375530983
    0x30c030b040b090a180503040303030209090f070c03142209060f180e070803030f0613050f0c03100504021603080708071d12060f0a060f2402010204030c060207050301050a020c 77
    0x8000541c61710aa1100d0b0b030a51100d107000e481c0d07000214000060540640052010042c00c54110516a07100307149010191f105903040e40001c0c2c451820440003901484849506081c0b2820321410401d20140300d0015201200b035215103c1c45142c0100b00782c40c45805910080e000c022550806c5030308000ca0f071592102a0f0985024071901c400c0c0d130032041d000c00d01001000d03284900559940b49011805030f2010803094600034040ea100010581c40e60040d03114180c043e01400c5403444040d140d10722409075581002d003c030780e1344031b91002001455980382d100a00100e641c8803030840a654540c2070150013108010842c00070300090300100044203500c030b510200318000b510310042400605101180c045c8500703509540b590310036101800f0762001c00400030341c810141c0d100309002c00f944846501d982c11344a0f2050003640d9014006c281d44158908030280c42620441c400181040d82c0c0703446112810001d60300110150300010070a100340d00f4280038440e0b20803e00401945031042c004041030344c8203014032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 375533462 1250 375532212 375532231
    0xc0302031e1011041d071205251209051509030a0912060f0603080912010b0f0603431d0105092d240a1d10030c030b040b09 54
    0x528500c1a08502581d0240c10b07062490b81d40c4400700c0e00c014901c068140c50003000300d120301d5034801c4c03844201d0088601c502ca115000041127040002d000100d507990903030000c14085005c54103216403c2510440c01598011002024a4040711085900301400605600640e402c20408601e0a5030010911b1040305d0086111490250003030070000c000380100c2105928840c2003810004c00d03c0303140c0e07000e80480d54046800400c6000032419a074200c82c4883d10f000d801020700301d004101e038940000075552248030b1940080405d80d64002c2e03042d05e60705844480a102c401d01c06c00540304888044508240c0760a400c21401001c0002030842c17188881d289118100280003d540c101d03900c03041d000300d6881424490f540c0030202418802c00d0850710f071803402802454400c944251a000301c07080c8a6450310040c01c001c0c94224860300c1100c4144000c0c003000c050b0b007010b42d8101d126440e01c3c0401e030740c1c0c480d499070005045411204010b0568a50700541ba1250341080703000c114036500e12844907045149034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 375534712 1250 375533462 375533471
    0x20c100302040b0a0804032c06210f1f030b06060a1205090f010b0901120609080c0d020106140f030601090b010c350f040614070503070c0302031e10 65
    0x200124064899504103071070030b14001c90303184542900484a10302580c03081c0c0750004480780c00c405000d60081183e1000d900c0d40e1519081070f0580c10107074020a031400012424512500040b05501c0c0d280b0b0081d19002c003010b22041c10070030346003c00b5078079400107100300c0b1580f82100c1c23664840d40c01c10394028008900ca404001101c9080c2ea01800340400d941e0b0010605210920340280d46517101c020100000001d0350030070f91503040618003064154141c03580c0301a6200302e01c0154844c1d400a01c2211400c8039441001c22001e03210480c02c100c80100c2d031038240d002041d01c600342003190881101c008401c2c0d005401d0501a4040c82c0d80105030107055680f0604001003810b01070700125415600c004001c1c18520794034a41c5c15021065030765600e10443c6403558841c910a068000302030602c100900b0f010040b4086c4000d00c189881600c00003040046c01c480c0b9414081c40d5202c0a00355403152108a410400da01e40420031410306010305c0c4a401201c02c3d085000700541640e07291644401050400816900c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 375535962 1250 375534712 375534739
    0x3100504050a022712011103010b090102030f030114030c0913151d010218120d0c060b04060b0904060b0c07050f0a0306050414060c0406140702010e0301050723040303020c 75
    0x40703a0688403801072844905030018201c0301c0c0824114540302100d4040d0600000009424030140242047c00001c2001e00b0301d1a841d01c4490f07201d942100100034118041044041c04050040d00950301801d8509604401c1403003900415150010711000306c0d004030306240400a61003044406250f1154006030a040c000403040d030b5070303001465070ba20300504042c014003241c1400d100c1540606004011088241040c9012404000c40c003161076100306001d40c407405000b5035903032003450030500540c801e180101d04550404001402d03130b400b641005d81e9011010440a0607803605001c0c030801421402c00807071404000d400f1441c0c54516a0107258010360071440e100e030341600c4180040000b180c010000b0000343c182860b100003880044028540c0b05c0c460f01000c12541c4030f00b1012182125402c2e106c0840c91000034400a905800101d0143e05001690000c4402030300c0a0040c980308104503a03480795107103461130585030070700d010702c1038415242c0307042c081800000c0e00000d004014100403201400c1c031009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 375537212 1250 375535962 375535981
    0x120e190308040c0b041203080a05040f020d060e010501090b10090b09040c091d0906070504050d0b06130f061a04030803040b0c07060612030f05192f030901140310050405 74
    0x1043d600c0b00881344d2000400140c40740d20311034000030706413181d41c54841c96204c9641ea00d0654a05440c0a0700c0c510803140102d006183c941e041da80124441c0c48041020050401d6550868409a01410782c840c0c450800618628211a00880c80101400c01e100103d050401c417542c0ea0042800d0140110303944c4140701c2241e4001c01428004010b082101d4900d800180080640c0702e00030340f01c14800b4816500807800060250042e50195080600804407554540c1c46d200700d0a20040c08043e040203000094821035440ea0050b05002d0494000c00729203035140928000100e8001e15030904070030802d100a10000b00000d048903041078120300309951544407646c9407002c61058070001030640d49454400290000410b801c000d459009403660300c01020b44803401c1e100c0d441001c43d134049044821070030150441c0a01d15020749a980341217070402c140b28610344240c5800400801c00040d038000300d052200b6680c0002c0130000d111f95094400c0c21030400d000481044002401014072441e1508005031007002e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 375538462 1250 375537212 375537233
    0x30310170a02220216170301030503190c12020601060905040b060d0c0e0d05010606030c030513020d0c0b120a1b0507060902061908150306060f0f0301020f0307120e19030804 76
    0xf9060f0045640c0d01c4402e00d040c0200070300c14400c5404602da410031040ca0b20014054078100c070740080140d440c00d46282c091076605804d541c4140140900141c0f40c074049003840c0110410549a50001c0c4100c0d410000090101c0700395a01c030303902c2141017119014507502c40b00103455105a2010000ca0700b844014000e07201a0749940308075030040348201c02641880015000b000440301542c40c10000c882d84500200c0c1594000c82e003044a404a5050b00001130410000c1c01c145107004003100f1194a03254900020160b000340b101d4131090f0b524205201d40102c15200350402132085985d02c82c03c1c80c8002c0c8000d45940501d0b40041c1030255035980250540d00c0d241c0403524031020f183d100e4100600301c02000f812041083d60202e03011012549481001e05000a1190088074018106840d50602408110310304030344054103034055400b4000790002283d0f0201550061020380c40c2c6040c0d544940c4650f204032040741071501c0c1294003a04c01c0800041040403107540e541e405240286650740c40d401d0540224 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 375539568 1106 375538462 375538519
    0xf110304020f03150a0905010b0a06021e160306020304231f021c090512180411130e0106030612020a060e031c02030310170a02 56
    0x5140c0b031262507804060003011100903100c044104402c0354800c0e280d984009854140c00d104004080c0a01c03188000192042010141f802c20000d40c0e46442c003401034034030024041d8018000c0c07400e02c4154465518100d601024a80d2441c0a000135481100c0548842e88420030095040c05101144829416070400030f0844075281c1c20403820401e0304a52890440e41c0c01c10604903a00c5816940170344a03070300c04034000303824881401c215003494840b20718078001840801005080c5075000402e21656074041d180007035410803403180784005229080040c40d00307401907200000e0703100031443c1040c1642c800b5a014024150768035031000403010304c1e05000b0340c001c0702e80c00140000d81c4140c0702c243d126140101203624030b0700e4580f0040e554141d0001c10100607040003040101c8581120401d100030040c000480d40d80c000b803c5101c61301e800003171300c0003403240e1416100840c0542c0300010070b0024 = true := by decide +kernel

theorem cover : BRFrame.Cov 375359712 375539568 := by
  have h0 := BRFrame.cov_init 375359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 375359712 ≤ n) (h2 : n < 375539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
