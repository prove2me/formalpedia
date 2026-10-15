-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5522
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:08:36.604103+00:00
-- url     : https://prove2.me/submissions/f03c1804-57d1-487c-95bb-8300fb0ffcdd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 992985611 ≤ n < 993165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 992986861 1250 992985611 992985629
    0xe0c06030c0a0e0414130507080f030d090c080a0309140603041e32211e04080703030507030810050f010f03020d0516120507140a0e040f06050a 63
    0x401c0103a500070000560b00c0b98115440c216140a00c01004240104099050240403040c078004026032000c25101c1204018495000d80c2c40303107a604c2d28441e5a820b42207000d03904d260400e0000f6000d00c400c0e0307031100e200c0d035006408482c00d881d0b482482a04101c0c07030000940004110500501005825020b00e44000805880c4249180341a8540440b420364141580109910601045c0305210350b402544038940e2102900141080410f18a141c00090484a22141d4052002d4407510141042000484c800049004915200362007841c4580601c00f441b044540107410301c004a02d02000300043c9001e94405e071101d5039284410300700641400d0009000d40c0f00c80703c0303042e8144040e03291500c904044403020700708010039040c84d003402d801030301400e898415000c0c680310801c1004114202c10081d003483c5a2125280410344090200c10745404646410100b03103141c200201640c0d9407001400000e0345840c0001c614608400000c00303075903138001080d0341e0b41e455038003c1c06140351600003d001441604 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 992988111 1250 992986861 992986867
    0x71202280206070e030606100c062c0114041209080f0325020a170109060203102c0402091314100e0705090103121e020102190306050904020907021f0e0c06 68
    0x400041e50383d20f4007d05040c001c55000c1c8400202c54003503200b8401166019009201d082c110070340a0b00c003080d002101102e500901106c010036004180300da0107001005070710094a5543e41d484403c08850000c410b034040101f01c40300020605803d2101d50001a6184061130f9100c80100300c982c0407880c6042410012000c00002c400141d803551500b41c2150341c1205c96040c07102080240d40c0c0107007400340000c0c161034000020000c54044e010b0361003041d14204100044000c100c2c040e02e2011507403200009030145040c0c402b00d0054a0003c090725032090f000210480140e501c0c0d1390307140402e1125840480d0550081b14548030f2400700d4080c6020345540000106051461f1000103500a401840040d1440650024012801e4030032251201070003c1c003010800f40c05005d0350000d00035880f074206000081d21081d4010f07401031290241030b0413240010024111030729150200410b40a0242c800815417107140695030001200d404034000b103807102c040000d0540f1040010b1820000303d144024481c00c010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 992989361 1250 992988111 992988137
    0x30503090a050f010f08070e030106060c020907020312010939021506010c03081302120a0b0705040f031103161418100e0a020c1906140105030607120228020607 70
    0xc04245c8000c59854900a140e5440708582a9908813032007102c681c05501f410070205455801860072810140f0a60380101d099665000807a100d005121f070000b202000314004100702845a0008001c1c095440305840b48007501c0700418980000c40d1000d001948507892000000640600c61041c2103035002d007900c1d94516003000004d0801d112040d0082c20303c00e042001c540c2c03401c40a4100b42c01258050401c0f1005003a42c00445d60715511640110b8510b100310740000d89862158043e03070111072111030217201850840d56410308052690f05484e8152040e06100187c1d46c106104540081caa410502000d02c4280024490b03840360038800c442040c0c0c01c120601640004465498040fa56034000d10f100c1511140c03e01006403041da03c10201c45d20400400c0140e040000a04080041c8508401c1212007182030301c062102d0000d00c81c15606400c0000001e126500911684c01d8110000703000610b00811180041710280840c20255180c8c5a10203080040c00d030100401034000d03942c0c0c2013010760b00b140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 992990611 1250 992989361 992989367
    0x110418140105010c150c260403020c10140d1509180602090d0219180b03060f1803030405070608090109030804060b0a0b040902180306040c03150e01020c0d140405010c022404030503090a050f01 84
    0x902f80019002d07111382075680003c00e110b07500400c3d004081c5040c880e5100384141420000e4264030071500c00035110303000c00144070340700303440750055020300b402408025039030340e4903150020342004a83c0e540082c0816100c10040e5641d01d0710b0441e00b03c4101d4080c00070b03401d00b11085204ca003881c074980308c140d24200c000c6e45e455a00066040d8070081380d4000021550b0751800c8180c4448040c00228800d20021043c84108800030031844203941c0f403551003064580d24000d0180c241c4642260150120b140840031802040c665080405010f01c00b40940101c1c540d904484c619641c026800761070740f00d030302060460720351061b00710040800e80101c0050410f81059194071140b003043c1c0c4001810480404070b038062003400d903040510042a0b01000b1500c420440e9501501d07000340411500010780103805050500304c044050fa015030300185d60b00304c50a0307801d078240900b1101c0f224200d101408442d81450f1050443c0000300080c51060703000e5503d80e098003040c010050f90b180c000b00d01c9018020034848403668 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 992991861 1250 992990611 992990623
    0x2c060415051002010e0a08210c19110703060b1e0303030c0d09060501060c03020c060a0929030108030a11010506010f0c0f06110418140105010c150c26040302 69
    0xa0102c824000001103403405034014008260408102e000c0c0e1550034007840107030809000ca15100c0340b02d4071202c99036481d04004101d07080780e910b4a0741c00244141440c20500c62000201c820003410001e07001444184400d26000310f030350048850030b8403501030070020f060038427422440b85d80308640541c4818692000a0702c80c00700511541002c400401c2e542600101c0d604070094098014204112550b1984070080805150384e009a0151150394855901424008216414411141e841900460900510303440780c0540750403c031140c550000240000c1190304004500810103c0000c2d9034030050b0a001600c500f01156000c03019916013010804aa600300161140030a03161800d0100d005152800451300c00d20120301a025601d010300c02c0180c0c1040c075000b081521450f000c032540e49140d541c48041541d845180010f05116103100421055014540485941d03100d081c2d00041c2035481c030482001c895609112400003402d17504001e602ca0001000080400010006d032402481c0c1f545020b90780389 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 992993111 1250 992991861 992991869
    0x242a030804060b0603010f17120315030307052d0304060c12050d09060515030a0c1a07080d060501090617040b0a092f010f0c02010311042c060415 64
    0x500d6000182001290f03445120940002411180c40c0e585171140700c0c3d0150b0326809807d51651480080d01a400070004480f503510410b0314100340f650380c803400c00517011602c881107960148402e000b03070400504203104500055141203005a0204910f10240780741c00061201310f270150f00104011b2003003c2c0d1001000b4105500a0128045245481c404940da031003a4030b00d110005103421140f00411030150000c0d8042c0003589142007017560013804154494000c1d500050103401c8d4000304000d0300880b8032181601c80683c1c2000c5081c01c485440780201540801c802c2d640c078903500e41e03007031209607000200500900140c1c81e00c1c1b13861041d400c502140b5404040e201030000000c410004110a607240c100101440d8001040c90714164022041030308000f030305004451101d5482d9178a54903521a44200c4554040340c1e803220b00148181e0015030080403010a0a002001c1c00c01c004510b80c0941111426180c04400101e60b510000008407110340740041c08451003642441130700d1041074080c80c503140580d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 992994361 1250 992993111 992993117
    0x4030801060e0d060f0c140903030301210803040f05060c120a090602040b040303120605180703091109090a020102120f07030509030102090901180c09030201051b07242a03 75
    0x4802c440e800101250f514810042289040c020b0070800107265400c80e1078118026100c0c61401001101101d81c2d90003544005601a80107100401040b8000b900f1041210742449104444000f15140c80d49268000c0301c05480340100b11038004104001008401da204c000003002d11f0622541481c0390918000140c5414000354035400800b09000c0d00c1c0e41114010008400c207199500c3c1d5a03d4003030811554a890808103d14240c00015070341041c080703441450003800807003200e503554154154000c008200007903c1a00b4000c0c082150f135240c841c0101e0003500c000008140890183c8002843c02e40c5106025100300e80c1440700030720441200d001e941503a640350910039100d01c0c030140400d0083c058032042c03e40c0000b01c1d00001807191034560304603c00b02c1c0c0c900c10500401400d601c054620484038440240000c10411201a400c2a540000e80c402c100c2581640c810540e00d10750303020502500440c0080c031401d4007004c0142c2c7c40d004110740d58001d100f028107035144004001499006040020041c040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 992995611 1250 992994361 992994377
    0x70b010905060105301806060a060203120408090a03140118020108070e010c0816020a080f060c0d0e060a150e0412030905030f0a12060608040b0402040b060c03210f0403080106 77
    0x300200c040122441e01d17002803c144091808610a84540784021403015240c05110702040d00c40c200500750400781c410a400540c50103032030851a0480450003802a40e4040c1d080c0300e80d000c40e58a034800f6900071800745440c0d0b039800103c00341c050300b1111180724259001c5910006500107076001102d5070340c05051410140210031038040180e80c18040202e00034024400040c0128507101800c09040c000341c0250703038919074551650703030b4140e0380c0ea0082c0141d001503101e540001c0a210251004141c0c44117811000b250011816643c0303417a00740c1c00e5480ea8a410380310441034a02c58030351100100142481c04c4420810700f01510340280c442a4000e0755000c040e110846c0e801842000c1040750706e4030b64900d10fa1543d0340c00002c0e0003000045500d0300c1e0111242401000124548213402a60259030808019140b9844940c00c00c03004001c3c0e5a840754004400b40042c0005240a01c0680214009514140349101841030041d9004c50001d100e086414003034024400130990209910f41580d04508100c86 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 992996861 1250 992995611 992995657
    0x70b01050d0f200307030516060903110f010c0203010507030c0e0a05130c090302120f0706030e1b01020c130203010305011401030812060a170114010605040b1e040e040503070b010905060105 83
    0xf405154a8659a054480c0800c00403c0010000e904482c00f131000310152815038030b03440101e620307450511025003c2440c0c2c002c110f00e00d10740494201820368050402c139148524641c0030070300b911030880781e200100e41e03581004403909400112070091000e08580400e1a42c0c2030200140080854a00882e8141d0340d0f8158264441d01602d5107401454004280300c0f6540c400c1c01e02d07039644480d05104100d0300e024842c0300182e180d001c2e0246000701511070b800303031054211003035603001d0115901d001c0504602c00da43c103001154449a00031444040508405640e0f9815030038814252170340e003580c601152031120b00400114030044107a03004800c0000c0c0c48075803a150030000504241150b04842d01070a0a6411245001c5c0150322140d820042103401c5115a0380e141825259401184220040a01300b00590380c0c044550070840c0c002c480142c0c01d91400d00307450b510440d40c40441183c08580c2d41d880000e801b02800460101c00d401800c0904050000e40340400000f8050701504030f45110303440c0e42c4a0707010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 992998111 1250 992996861 992996903
    0x30b030309100e0a0f181a1c020301060f092703080417091806010f08040c0b0c070e010801020a0206010f180c030b220b010e09040311030d0f02070b01050d0f 69
    0x40c8540c004c0c1085031707030701ca0240038101c5000850101e046450b00c03282c20503110340d0307840541900000030484141215038400e2074240c87d910711000c9034907541e2004049001e0f000022882c1c00382c00305100001d20600b51141354403040c555004000c01308400c0c3e80c4244c2c0003076400f0070243c0e401a444100400d1800700d45542040c2800b0340c1c140705603c002d18002c0056034540d090489441410242e840b0359001e035251406540c1d82c0380c00c0e1030150082c0a80c1005005040840e4010711100350300008541c40b1a07a00c100d0981401000c0c1c10403512070b500001c0140103580d040001c1d902604a450700c0702c05507440c003001020b032240020f208045961311040d45140c1c681c084d41c0320400d80d81c405044201d10364641041d1580f00755590b400810124a49001e2414551080010740c80c0402e020341044281e03101d685060760301c112078072a00c022500c0304100f5221801c10b540651000152070b15005621070394285005080c6410580140d4040c41442a241010600c015440703401d242e009000e00b400700030100700c50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 992999361 1250 992998111 992998129
    0xc0c09071d180c0c1c05030f1f05191d090d11060103020112110a0314150d140f030a0210050f240604090207110406060206190c020304030c060f030b030309100e 70
    0x1049145c00326044912003030f044002180f045c60354503845000390b0381d000404400365160b5050003400c005501014819810444402e402070840c070549003402036501d80f55146102c00f039071000901d1074050020701007528020070102e904100d09040c20017482e41084c5066507104070512002e8100990048100030442a075401445c0303e281c030528040e0340e44111100034001d4220201031401035000320000400c104035801c050f5a4524000344030321b40548185e110380f180e55440d800c0c0d40120380940c66070340c41035100800081010300240d0b009004e4442400f04081c084650003031048024186040030011160240111720b403111400c800064007c070306840104000d4080c80c0c020301340040c80007070000107001360b0654450100c3e4044805101035034450303c00304d80341c64094500d405814110103403101d000160b9003204440302d03ca441103c5c00c15a407915400e00c010300540c0300001203100700303892402c2c56916014504000b002a0002d519240f542004100100e40c20060301041104110350655a507482100d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 993000611 1250 992999361 992999383
    0xa0c0c15090606090b130b0109030201121503120f090509040320030301230a0302010c14030d020711010f11030f0a050702030a141e0c0103020c0c09071d180c0c 70
    0x10000284c88840d41d4000300f001c510b0b070741e10413071003d0a1040100e8160181603107010069440c1c41803545168010344120340d44401100b0041e494221551824024541c1d41d0019402010f501c2090000c0303210103440d1400c003a000c02c1c00c200b595481448070b52601b0680d1a00a907140c98908469945c0701801c1e02510703140910703d01c45000010000449038103100010703101c50444030200f0007101128080007841c620f1840000d020803401244080483e9030216603480304609042602d1402e2201e50b250340403a0300804040303074501d01803088101d403075920001c000d0b07071140d02d03042981c1c4005500580664078004d500d5902004140010039942c076034807070020340f8600c0cac3d80941101e40700130082c98100050707101d4400d034509500c01c811209001e407501c190010845000301014103054600c0100440182d444003112102d03030b100c0c800c5188800e8072542034241c400c04a9a03903071824003001c07028884032013036a0045030f84110300914a101224201807059034000181240c0c0d640c2c0c5028200f00b581c01c200503030709 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 993001861 1250 993000611 993000623
    0x1005091011071b170a020a0510020c18070f02010513080f0d090b0a110309120a0c17070b07020307030f08040f0b040b07020c062502010c020d0804180c050304030c081308070e0a0c0c1509 81
    0x5052510cd04d0004140d60240c1141d86460050001c0158120b00300c60040b90f4070b03061011600e002401080600005052241c54044080e10b010f40e1109804165042c811080b9001000c440c03c01100b054641300d03d59013401081d45c020300c2e505040382119514052820075107200200003510030984d5000d550321a00305540451080000e0103401001e0089800520060b14440c4482c0006101a807001c8100d404403035054540c001b41c61180c501c02c0b9889640108122884c007505081035000c9821803110600c168490031501445242c00000242001011900c0d103008180901100201e20982c1014086841c2c0380c08119104034803500040b102d40c030f180c0001a42201043c0d46070410310000000410641c0c001500c0c940740301b001a0408801c540000711100b0000700107002060000f8030418034100b0301406080d11070f003400c9a12915a511000960100c450380d03002801c1000100000020550711101800b000c10044801c001d01520000e071450008205007400d9184075200b60250b4412180250000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 993003111 1250 993001861 993001879
    0x1e090a03121d061005180c130b0c1605010e0a03060b06040306050708010806060609010801030803060102011104080f1b03150711030a111005091011071b170a020a0510020c 75
    0x411540c3c5441090b03c03001c0394825407141c046441d00b03110ba003692003190000600c2c140c0d83e070341c80410782d03180d0401ca00d12040040000320000e640019400503150b4601d84201902c406060312004080e901001d501c024140030b1102c05a04803591603068510881e0f40008010908014480000b0511310480c1c100911051a107014013100942c4401000d060b5905001117a001d5101c1d40d003004030034041d0b803107100d0000b00044010300c006030440025540003001070001061a40c268603000440d44c0242c4c1101100e0b034441100703500e440354100481c0c1c10841118081180f8440c035100840d496082d0400e0b503408424007880070403052407064000310f01c0032008005494513000d02c024020204007035900158902e00c90032004900340c0001c0e201d1907016444101c0101075040c0740700718000242c8406001c201c0020000d2250b1400300303003224503001100740d95230300b05e030300d41820503105015801c0003082182d00d9031f00c001c0d5013000585a045492060f180c08075182c64070b07501d45c03c00880c80d080d9003100282e0004110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 993004361 1250 993003111 993003161
    0x7080613230a05010e0a0e0d0309020d0c060809160305120304030215040804030308010e25140d06360b04061707030209060303070c0b030408040312081e090a0312 71
    0x143c1e110f181a00d104080343c01c11502ca0500b1141602d00c00100710100f60455590148050f0007035101444c0640301903c030019080031502e41d112407459950204010034044020040c00d02c4c0d0a2240140b40702d4540c804401c0c290568484540e100490030480c4200c040000c0440e041c54001c02c82c8181d80c48d800c640004440c50646005034494015100440203d00301d10001705100e80d40382c582501c43d1441c1d1018180f1103041c0c0005040036004194000c00b808000e101c0911038280c048000d203415401c0e00e4010880e81c3c60080700d401440b03264200f118403103141d520030b08070110403034101501d044544013001c03da510480d0001002401513520156001c100a1500452568003087c04412a03008646c211125650901410703168803460380c006226031035503103003401048070105c0a150002d01514109003015180d5480b4a0060141d01c1c0800208803c242003043c0c408260401c40d0030f1000c807540d18021400e021503000e5548600e1080101030000c10251070050078055400000204000408028903940c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 993005611 1250 993004361 993004381
    0x905030a06090215031e04060f141b0903030f0a022a0a0e0606071412030106020f0c012c030a05030d020a0905030303060603070c031b030905090708061323 68
    0x107206002c0380120500482c40a5480b61182540e00c15194001091080a0080b1142c0510038004004440e010343d104827425412400f481303102d00103880c8070340b000341c5803c0c4000010342485c09220345000c1c503002004451459140841601e005000362420180c481d140094164104549014161480b82a00406458109006041880700e0344261001c12074591500004804c00c0c1007200c079190030000410208000078410850103450f0403446c010b480151007481a24602070380203071b1003171b801a8403109413100c0208090102c1149010300342810000391a50050110843c510040c0400003a01481358481d801c5c1ca003170202039021980042a01d641da100315a844c0000d4000f04c811500182503290041428240081201e000e048010083e90842d540d5013000c80b50b10340503c0c800c5007000041026a45400741c00108814058801d8440000646c1080144089280014421320800c01e2400c14030080e40c0740c00404441184501c00007140c648840c4082094503030001c0915148000101c0802528586e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 993006861 1250 993005611 993005621
    0xb0f031513020a08160207061407060501030804170309030a0b0601110106060918090b0c0906040918110d120503100803030f07030e0303010807060e040b030609010b0a090e0303040b070905030a06 85
    0x40c3c66103442d441d5480340000001c0000b0700c4164440964403101c014410b207400b0300f41e0340d10240349840440c0d281507060b40d5640242c0b003007070748101c80546021905102c642e4180d082d29a046041000850a282c5004000307681c030220320002038005402c80c030105a45900c1040f0b104403000f00c620081c0081556990000c2c220b903224414101c8040d041407102d00300765100d00490049640000c0400c800751100d2203007011941c405441e26600144c04c0000003115115801091503e00001c54003241d20300d240d040076075245038003c0c0d80354401c2100007010800a0190010b80036242c200c0d103003036900c2ea0f481c100b14002c4403a09410084440c4000302c00c021038000024078581c840c841c2680c05001910007011b034a590b90200307000b40c09880d081000203001c210300c6402c141000001c020401f0551009203404070381040341c1035030101c0aa0351944190929400c195051200400c0002c030100b014684400d4010b4403808003400040034540c0a1010941162081f0304c500054940103056403d05101454154002e007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 993008111 1250 993006861 993006877
    0x190203090c030d17040b060f0a12021005190e04020c01090f02031204061409040f06090b18070f260907061710120501090c090b040b0306010b0f03151302 67
    0xf1181500340051503124008040751100244180710890b01c49075101003400c01c00500c00d0f904a8240e10019006a990070341e0f180c02007114240740d0964000d54014440d08601400c2c120040c0300d820030034610440807450218ad100e0f440d03440c050415400040001d03001e481803030401c41266090890600c14092008943c0003224401c50440d0031035003040d000700c4410302541c800e0f04081054072034040b2404c42804020700c10800010800a005070b041c054210450b5200d41142104c55034804050100e4102040c0e0003481712050b0002c0c1046140540f0700031b2081640a0031982040382119807200c0d000c0c462568100560b04031340e80c4205510707091003005d944005520072480080c900c180c903c0922141015034038003030b140c01d00c3d00341d11150404180050340d01101508a42c0303076507200440004290303100c850001800c0404000300d040e021881c200010f8440c04105a40300b078001d00e00401420560350100c49004054004c160f0b100d968184400e140e0b019002407081c0c0103100d41008400c044030950080c0030341 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 993009361 1250 993008111 993008113
    0x6090b0c0a1112090d0c0312050901030b010e150a03020706050403020307170408151e011e06091203030b12030424030513141207080903010b0303031905190203090c03 73
    0x1401c0c02d010b0325555a0115003102c1c07540b1080002c0403241c18003020342281c65000e180f049080396030b00e0b034640d020007400112000000700c0101e0700010940c1d040c00340c009041024a410034440200c003001955140042c908038a10450018400348a24000c1d0140c981a9400c04801c100502e01404c004e03441c0c0d0b000c4002200c091501280e000b0100e80454291800d650341d450041842c00002c810a0f60140d00180180b05182c1420807150858410008018060910080c00490217859840b00d414480c21580200061180c076200902218000500c0d698040e0380600e00811414002c802203245400600c07040284d6020004010410500030140c084c0034040c0b1b411111810b21005d082101100c900b6a403807001d2201d102e0758040446d1111448615003e981010388100555040c1c0100e1650b1098104944a02011440c43c209190071710170b010440005034041d40c07542c540201099000c07802c080045c2c40c2c0325a40d5003c280c0b030449000410110a82802003156281403040902c0d54414a0090340c40c03207 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 993010611 1250 993009361 993009377
    0x421090b040b0c0717070302092203030b0108090f0c0625081e0903030a080702190c0e0901140c0f04050d0f0b060f03151f03030f0909110406050706090b0c0a 69
    0x902503c1c46400f41a40425801170006d03642190b00300200000b02408026140800c2c01145041146281508543c94800e441c0020303c0c101c2c2d40000341407900002e0240302140c204410a001200e000b2589013010a01240c0407036440e000a8a00141d451460391000390740300c0e0344001c0c03008000c1e2040041640c120b002800d01440d95145104c051a446080469a0150801d100944034540101981c541182c0c1702d0042e11141004040d140306078003440c45043d6861204e00c2d0007003007114500f106094002120b50003c0c80000e0366401540e2a400015160318a1070304001005d900c00015581500c010f003500412001840c030003410f2046001d8042082078a401018401054140c5010940460401005000307030803501c1d01c214214503125001840c111503c4c000e6201c480c903200501d502000654402c0d11800120400d0040040c0030040c182c01c004544c0340340c12040c46002d9160b4003503504861140c070b04155504003600d0300c140500131480000340b038800030304184140f150b0418003900841010703a0711382071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 993011861 1250 993010611 993010619
    0x4110f0a1809061a072414060307422a0b070c050c060730020309060a1101060b0c0c0f09010e090f0a08040317030421090b040b0c07 58
    0x119845031040844d21007101c1c1d01c110400342e07058068a0700c18000e800c0c1c24000551101407040262060000070901c0307580d9072000342c0d000040c16a0039004035040d00140308440c00c090b0000d244503148801c09440b1813006040100307c6409242800c01300003891809526070120500180411000b1056290007070420030078100d0304086503411040b50303034000000c0030481c1c0360000181c03000c092050041d03d09005400c0c11003000d846480042c0710703951140005c4140e4401003107070802d815008000c0c0641405008418144003580001035603401c00007102e540d0794030640c902041d10144a08100313040d40707500302100040e20400f4203000d000760321480d03030a82c0c20b1210090200038009404501556204420300c0042c0300208007a074045070b00c826100100d80022441143e09840d0a21340c0e2421030386154005000d008001911110b031820550114150782141404d0390707244d100380c918818850741103202401d0a441c05100d9601d10004104849480f9650354440030307225503a92103072802e040d49100f080c038006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 993013111 1250 993011861 993011879
    0x90302010b120a2d06051608100b04260d091e08030d0c0203310b03060603061009050d06050a060e0103020a03080901141225020c04110f0a18 62
    0x4443c040e404422044120031100c0880c40402c013080f04090104003c2ca01e403000240688200e900030028607180050f00f07c44940c0041c407150f00281080040745d2200010091008203400b5070302640e8171040281070840f03d401c1d00100002102201e01d00620944180001050b0000301640c141d40005200302002c40707407140000300c4003005118000e141d910800028030103508683c001881c1c0740316441a40d03d002000c0d4281591010380c000c41c501e0b01c803500042d050350840c600c44002d0040003c0480c5d030741507103024400110503010042906018121210b001100d0510030f0301c4c490041c010051009455010b00d08016000740720480c0c120340b8507894400041341d201d0154180604a81e03000700440015821684e8803030302c5401c800140c9050004441204005480c11030142c071503c0315910f00660f0528000320402071074070212906460140c1080e641070bc203a0b0380401c0140e031404003a1000702301d0414400018031103201d503404e43e00c3e950340b002c00c0784042103078007160b00211826044103405416840f00c58013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 993014361 1250 993013111 993013123
    0x4060f1403070e09090f1518010501030b0a02031008010f090213050405070614091f123c14040506013f020a03060f06060e090601030506060706090302010b12 69
    0x40700204150304007284151421800b4154083c2102c400c0e2101031079046e8083d483c1040c50352404000b80d000000700214a200c50704003145800c1450000d20140d4555200c0340e000b00340c00ba20506c0384070780010024003c0000300c04030000500d02c03107001b0030807160030f03050003c024150a034040788035007482c2800d00340301100c9016550080c4d800c1006840390b9441e00c40161116000c84081c084100c10502c40c1c0e038542da498001c818400e46550070401e150801054004144107805090405190700c0e001c17480000d052200c0e258056100380a0031014107249045440301c1c01c10080405460441c20300d509140c044079500e42480c00349126504544869883c0d0052803072200542440140408811203074107400240d10302d1031242101da5404e040224543c1c0d0300881d202040c1900103403001a21003200c84880c000c0c52040b000102010700e003030070440d481c00f0009210a14050500c40c100354452010500f07666880e002c865800384d101c07038104a03004036807038003030302a01d070b58202e25100d9840d6503284103100c0008202 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 993015611 1250 993014361 993014371
    0xb0c0301212003101e05070305160f0c05010204030f140f0a060c0c120206090c10090306091707060f1a01050a210e06010e0907180504020f0604060f1403 67
    0x21240c04810b0154085503000e624110a030f242c0300b03000700c190f00512544124900600d081c08440078042100c2c40c0c035029124064900b104152412040001442e54010850707060622440c010343d204052a40071140141c1031000501103520000e00041040080c5150a00182c8070b01188000c40c1030040302e031620348084840804164222910102c00140b42c0c0d4401440103c40e41000790415100340c0310303003420110a01405002d030340030394148400543d0411103101c44501c2180e0b03140403850050740c01024064107100040ca09a240c170341c00350800c040725594110040e60307952482c0e282e615601b002c80c05421100342c800c039214a0031100c050281c401112105460806850742803400003086011545022211000302d000600040c12a491100380d01549204501600060000d54105050f03c10000006000300c400d6601042d01009041d01d0303440d6103000101b82d0200014260b5031400462250900e46c00c1d04c50b4800c1c2c000030702150154000c5064002003600e507035003410f0030f844049540c245110540c0c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 993016861 1250 993015611 993015623
    0x515010b04060507050a061a0a0e0903072d08071415130606030203120904140103171c021204052e090303020f0301031a0906070f0c06090b0c030121 65
    0x902c4100d028000400002c1d20440403514801003a03113504c801c0b20384662507410209001c6940244070f2410080b01000f070a240305003000e050070304500d03042d80c9106954000704407900c4121074400903000b840282080345c182c0c0303120030701c42e89103403810a070b03568001201103440041c40c444448010038001014020608030503448101341d1100ad1101c00650840802200e1541c0c0781c06000c4010380f000d014412540c8401c822032500c50188000300400d403913030003003220120081c40c40100007040380c804d1a032415900c0040740e2a66801c5455280d100002c40d401109030305e42c00003404031211a9203501c0342d40329900444c01d48600704038645003494074817194192000c8a85d0600761407010b01c1c5103a4010781c20030384a4140180742640381b10071b02205400981c000e0310b140000ba8645040141c259449643c8a14107401502e070070320389550041d02a03c001c5040008001d50441c545007003000c1e6512800086400c10031004840c980601075240c594400d00039a0203103001021072980c0440d82e41e100202c1554004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 993018111 1250 993016861 993016867
    0x2010509180609010e06010914060c0109110a0e0c0702040c1b120e061806090604030b01090209030d140301060305100b2212080d0b1f05030f160f27060c0515010b 71
    0x45500711040144c8860740394010010496179000c0322f001d01c00c00e0440c5200e00480600c0030049010820040d80c280d0090003492100d01c00c01048441c800202c07180c941d0b0440d00000c1600802c4000c0741ca515512006400504404219005102405140543c481400d03500c241c810342c4020188082c50080e004103034581c1d84403414800c1140b80141c083d0007101009000b8508041e0303a6103541c0080c41081e4000002c640d40081c041c030240c02c0a115908808040d03080264507540d0b00d07207007102140b0051191000b0543d44002141726408088003180c010700c4d80e8511541ca0b111000c8511139900690961032605441c1c94a00160542d9946408414603810880480c2008200e0400c48064226400d0380e55000c2110505800300407011549110b00c00d44a80c1c520340c0340d28100080320f40021003e4003440c000703100340c201e44108581c07000801d0101905482c0440540c01c84003a2241460b84110500d02c02001c0e102c0c01207030440c2e1260515494500400484203110552140f10b01d0b140000c0c01000d840320410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 993019361 1250 993018111 993018119
    0x14040515011b06020f0d141021020a23040b1c06020325020307060c18150309050f15010504020c060c03070507050d050301050f10120902010509180609010e060109 71
    0x2201000c86590300074440941350108044500c0002c0c6d00800301901d8290369403402c00005000d04004a9000d20f030803800d107011604080c002030902c20001e844413024070301c15000c23104545481125030003e241b5940e4001f601c20802d9182c2000d400c0351561907005d07601e020580001c070f1914000c102000710032102c031400403601c01e80b04d0341d019600081032202105820010300c0990044000c25101074102d66000e0768450702246000400d03603109603900410851a206004c01c014503540e42c0b103084590381c0802d519a0000d0110503409084032484c003821600030b88014103030700d00010412030310a07410000c0c600b84a0b85c90f10300b0803040380030f054245d440580c4010005202c100303021004581040d09410310a05004107039503400d182c00e01d000900000036402000410036400c00820801004208071400c04d1882400307a070041c45a8500750481e40465264071072a000c0d64000e80403159075000240030f10440844680200a070400c0c19200e403806040c90a0002420360300501d0502d0040324140d41d880686490 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 993020611 1250 993019361 993019397
    0x213030b0f040210030c020a17030f0a2d0b090114010207060318230124080a200609090103080301080f03030411190801022206020a050a080c0109020a1404051501 71
    0x1410b07902c00651123882803103000b040d030005000c04240c1c441c0561075942d190002660107100406000c4000040c10080d40d0084424455800d44100c40c4840c0100040055000e00d00080c0070041d0546800466160012900c0c0e801842040c4040c80281c08548155a840d44200c2c1161102e0740d14545c0074100d0031403d000216001400e05004610050041028001c10482803c6592422100140e404901c00844c00501c1c44030103000280655405045005115151040f070a040c40c11240d0080a0101c185c4410360b60380402c4c1ea582c0d4001401e2060700e980c403854404110740c403e024486217480f5603403800089030340020480f0b12a41c0e12254084003d0031030424891441a6501c105070700301e03c54100801c1e0b06000340b0181903e04401190500034912903c0040540107494100d042190001101c0300c0c04500c0c009410392005901111842e50b0300b1110610381d0040c0303030088000f50301c6070310300e10300140c2d2003d03182d11141541c100f2202002140c44440465000121071462140416003d0031780ca000b2000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 993021861 1250 993020611 993020621
    0xb22050d20240405041404120e06190305062404030809010309080d0b0901081b0f1306080303330603040204090c0602030703091d011a07060213030b0f04021003 70
    0x50072800200701d0740740d8040c02050007041c5007008240042010401845e0500901960282040b4940030500b402d84860382c0002d510b00016041c801c0d404401095511144202d414203040046454800100d01c03000802800058a409100d988076421030aa141c5c01041100c1d4881d00c090161840d16180d41d40740b6621350020030b030240c14556101a4400415207250052000150180300010042009000c0114610b01a00b14040b03940c03005207503440704802e80031078a55481c3c040301e5503803001288000141c80c003d400030740c2041c0781d800c2040000d8100c1000000d180110107400800100c178004641c62003802e48001004c4c2c50069440020351082d050510040d6000390000d40b0100329814141c1302d035041c51a49500c1080103a10000d80c1c2c4e014140d000704142d0283c0380755010690a95868500f0605502060050030034a40d1854803d02e19580000c0861b490f5a40c0580159260100b030342524103901a5484203031004c03410480062110802c10301c6440c8600d5000b042d0504e413110050f0b017200140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 993023111 1250 993021861 993021923
    0x1a2101110412022209060b10080c0d090507090c030507143405011505031002090d020f01020a050d020c101e03020c03070b1512060403090b03100b22050d 67
    0x240b244e48288060b0015004a4050500803030001c985040001d0034415900090f0b50f016003046810f00a2100d400c2d00d6104030f9a8820940c0e0001c5803003141e81c249142855000d80c000710300d440c075010102010b140c00d81c100a1080c030407030b210b00340a222034008044561050302104800d144034541003201103001c0d404100c0c4440c20902c020311000344150380e03860854090210462001c136144804212614080100c03c0350110800307829400d084900c4013180d404401303d100244a54001106804c840c0d10800404080c5508035003201da2030030407201e000c0d4031658030501c4c0038050412500c1013900c40f0f004403540c82c0e800d2845200d0602100b0003000460094209411401302e40c0010040540865090940c40d40141c01d40410708040207070380c10400c094040e16810746c084ca50040001c00003c00c0c0c01640c00b41c2224007140b00241d0304e64560a81c6070b0450350581166884001c0403d444041c000741441c02240c41e050099541c06c0d864440b4100190801e05040040108561244100c02d407401701c40b03216110307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 993024361 1250 993023111 993023149
    0x804061206120b01050f0a0b0706020f07020915030d030e0c010305060a050a0315051602070b070312111903050108101a030303010e1e070e041a210111041202 69
    0x920b884511074028060201c005036150810f42005001900d4408101b004d040780c200d44e200d403111b14016415805000704080a072005070702003554500903524900321a8000d41c014844419444d20103070021010401105c00c0e0b0103480381b50811900359000b44198000d424101c8014104524110011406080300a20442e0040016500095251135a0406a002d180b01c1c2180300c9d420401080700d4402c86100800a0031548048168540ca490300801c280c4147d512011b065030380c5032000d007000d40d007400c010031152580c01c1c5001102e02c807a000ea0800782000280000400c0429900680100c0c1581e03002c0c080e1201c3c0d034215088002801c000d50f408200608138014172001c011501100003800c6030002d0707110a007010307100c1c17041101c01300b0a81d0a8101e1031480c15201d207050b04003908000c0038810700346501e40c01a5581c100f1440d070700e81002d950560800e001820b034401c8001c07103211210145500091a4200c3d820404424205030381001030b101038a404000010b40510356401704820301d041666442d0301c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 993025611 1250 993024361 993024371
    0xb0f090d0515010e33150a11030906090d08090306010306060314150601050a0314010e04050f010203040c1403010209040c020132070507080c010603030201020711091003023d081308040612 82
    0x580d4481b160b80090120340d920619444800b03140c00074104000382c0c83e090442e030308100b080400d155a07160540d507103031805a0703032600804c000b80380c1b1004078030035021100e80c907104580002040100e26046001901e1280c0010f881d000c007072403c0c442e80c9010307424a0303402c0e4056040000c0c02e654440c0c80501000481c070325000c00c22140c0310114544651087e004800407084846c00c21091050804c40072064982c481700842c594541a1200000444175024403156410320114900039660f003501075803a400d0008204210300061314201034003c0203005180c0c244511119081d07140002d00b4151500b29902405031070717042da0354080b4221681e5000301801c55442405206840500350244500c41c09144660001a0382d4029401c2c910410200302d1449881440c040c004c100e04240c1840c0c030f00040300ea043d110780409281d50340081c1080036580c5c8850220048805440f000080d4602602018011546030060103813141c42c5d510340c2002d20400040c0066208100800030b5912402da074184001907030000081c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 993026861 1250 993025611 993025711
    0x15020a06051f0f03080a0f1101050f0a060906060507020f0301060333020405010e0f0301020d090c030c120b070c020118170f0d02070b0f090d0515010e 66
    0x3080301c40968800e14010030800102600041010285020300001c001c4402030520350750b1407803610700c981405c1c00c0030032104c100d0759010ba5000b41100640b08141800a0006190001410309582c9046440450041c20071a000409004511800c0c05840700c50760f40e02e2811450f0b03028060380c6028003140300d03015036803040004013003154002c0c003040c104c0d01c01d00903072030340e400c4410712020307010000c15012080b0344100b008104580e001074200d049048140c6440e1f034040725200c00039009000e01e5241c03a07081410814030004001610030b402c01500e1094141008658860b0130b042d40008501c280140040e03802004100110300030040b54181d144145004507074407140c0000b41503013000a51000071000220400c40350190024002c0041d9242a03000401c84040d000c00000c3d80c441c101d101d4441c00b04400036441203a0040c000481e0f04d8440064825484041149070041e503c0c00c0e407244040c0d000c100c520021913041c5107400b045010f0b1500020302c14039050010f1401d169000c0f0b0b0480c061002100d0300c5410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 993028111 1250 993026861 993026873
    0x906190603051506373e03070312050408030f090a060906050f0a200c3c030304030c1104090501090b07090b070b0103242906120115020a 60
    0x81450205401412182520300180c10a40f030038000890340305840c104130305150303241d010303074550300b001c034002d550740880301031b0302840040b03280c0580881c0b2801240c0741e980c611400000000380205482607031075010b40d12001c840c41c411510f094400074842001040070642071403114820359044004038094502d0f440c602e80d0740ba0100c4442d0f500840302144c031802044400c0382800c80c96030b44002e64a0090180c80151060318011401d0175030320488404001c160409590400c010030441c000749204c40e00d8071f2106400440211102d468400c0420705000508100113070804410341c1e008544c161610040c03072a580d0355010b03040340708480d8035420950382c4c0f10700700201d90309000f25800180210740140090420290041440d50550807554800307070304006400005412408450440b5000544440b0b03048203003000c2c0c40d04c414440890800f40d41840b000428840b268040c002301c1060a0f54522003403202e00c0d0a000c4e03035004840b044801480c802004120f03014041080030010066841900c0413108156164 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 993029361 1250 993028111 993028117
    0xc17091b0604171b060c070b031003020d0807060507021b04020702011205071d101b050f100e0705040c0c020d0203120c0a02120a0c09180b01140906190603051506 71
    0x910002d9200303820131524440304003040b000e144001d40e41c0601d400c0c0c0c0d181b081a030b02e902034850000e890200000040009423000801c40c0038540c014042e45103c1c0305410f1904141d04640c80c15500c8921700300c085401140000356000803070600c0c829a100d241c104108020003504141426030502400018070802c0718901d2051511400d1541c03100921341005158280f035500c1044442030045040b1018001e001e034000c14000e604000024a00e80e81200d107240803800d1540c0003408400900c549940031a015038507822284404e01e030007080fa840b080c0d40d50b0400081e1000c80d1060700200f85490408009402d001c1e4030300403014000360465180480a030040794151b0b108811100851b04080310340030442c070748216840e4032940d407903009111010403511011203003100c0e44604801a59618201048003200c6500b0a54254110807000e600e5a500c403c10340c40341070002c540c40d110b0000100003820741c7c6445d415030308541041c281128081c2d818190b00b0b80c002c2c900a00045809031586036001e03003540e02c82c001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 993030611 1250 993029361 993029399
    0x21c08041d07030609051902160602120f2401300606110a021f141b011b200309120f070902160f060209040e010c17091b0604 55
    0x101e200c03507203460080181202d0840e0801000b490178002400b460861012940481e44090a07006a5403a416135210354407003517108001788128000300344044140c42c25402d0b10b03c100401145410700303a03500302465808800000c01d00f072204600c031000301042d5104840069110342c020904910030802032405400c00c01c02c24100c811410b80b504801d02125078403403400d03800c0d920b1001c010704208920b54005900800140f8000000011040862006611032105540007454107501c0c140d60f4205071080380b5040c601c0c0582d1509540c227084081884003084d6640514003031103a903600c012103000c110201c0c0c1c00c10004244144e98407041c0840201a503c10f18005006807416000740f003c1880c9017015401e10078542d01c0200194410711040481da40ca44518805582c1d010f007100d90068102c0c40c04800a010b0800f4040d00a49480b2000c0804141544903d16511043c0c44070358203d00c50b8005801e83e03ca08907283e00e41c1340c201c8000f00603015100c441c1d004a42030001e20003070400791034080a541840d20051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 993031861 1250 993030611 993030659
    0x8030c1b031b07080601030f0c0e010306020910050a0f03050703060b16050c19090903210e061302010c022407030e13180f03030f09060218010804021c0804 68
    0x50780c001c0c50082c80010803000700860b0043c01d9207078905200ca039143d1405110160211510301900c40820800f00300c0742c005007002c1d103140c580701d5860b8142000250080744085c1e010720b4a14402c040c0440c0290107403507034190240d5411000651240e022406000090400d070700303150702d86901140d00500784000e410410300c040c08101d41000b09042552074a600300c2c001600451741c10480940504007103078840d05a50b000d520102c0c0c402003a18044a002070510707200001c08103a091480f100b04080c0d08908106400348084686907107503d6888030205210300030003400700303110008580040c00c04400400300d0351300c9000c8080456550722851115507000110880008824154040e042d180c0b01c800c0c02024406003400300302003c143c2030400e03180c100412000c0d10180d10451010101442a00080044240c8070030074400d220451400f100a50051035500c2c0c00400e800060501a5101e04540c2c0c1c40b440e0004e0034001c00c4a0380e422240007240b840c8600380d40d03c0c07030108008589034100002240d01c0c0b00d9100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 993033111 1250 993031861 993031867
    0x10120204050d1401150b0703030c020309130e060105030c0f130b03010516140712110f07080d090b18010807021528060e16020319030203040b01150c08030c1b03 70
    0x71048900f15042c01c80703000000e2040341411b200742007100c0d050322215a41420001226031a011090b032071802000200c0354011a00b0f0380b1001d100500d9080541c2c440a50760480c1c00c540d032038004064407042c40c450040d420580c0c603d103055562910360701c4480724140b5600000b0350100e24001280c20b40f0380840b42030750781e8800d026504840b00e61000c02e02186220f0340892505040442e61406003040c90b5022000410421110a4030136600510160801400070800c03201c1003951810300300d813140c4001c000318001c10084200001c1c861655021206a0b40d070904241c18500210b2005440e16200600f0070400c61107410b80000c41d00180a03400c40c0110955000b82100d03084180c080351850400c56100079650b4200901000f9041040c002280c114054021554800e440101c04900c2d5016002081c00c0407070b50341c046011465095801140200e000c3d4401416aa80714200700381040102250200090f0070301c41034101081c4601d000d1030f00024124092880c094150311f080c007180ca03c02c203500500760000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 993034361 1250 993033111 993033143
    0x1202040e0f01080106060e090601030b09270c21150112200f040c0e0301090b010501110a0c06140903030a080a15050a120f05060c13060e10120204050d 66
    0x40e001c000d005201c0c140003807000c1401c040d0000c056030310140025002d400e10801040090303029800c40c000134540509440194646509058440440d00a02c0700314410b00210340a00d02d903010400709084000a007180000f00d060103120810301c400e03602c40b20120300940340d010050507908000c09009021101c940035030a03000b420051f006068a03409078001841c0341c10307a110141c0b9004030114032135500b203900059004140310161110355203525a540c0c19444c0c2004201041001c010f294142e8400303a8a410010780380303080c56640c4d00f0f00100003406241129204103c12841014031280b421126408107091501d2203022900d1904011100b5021901c2d900800203407540750b116a40f50f41e0b181c2d0011482c603c5c50079001c6141443c00c3c1c0a511806145071041000707000e441d0340700010441d804021510a442c100030801a280c014110340d40c4014600c181c000f0704184581038101d10924020208622810503042c180c64150280402d03034516031b001e000010780340d62051050541c06018106000000c103034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 993035611 1250 993034361 993034381
    0x112704082205100305360f012903070e0a0f110c16150e0d0515040c0807060905040b0a03080c0c0405010b1305100216180c08061f1202040e 61
    0x603580f0b140105880c1604005860700405c0e05040c0d44108000300c0111280ca5243c0c000030b581d40448500d00e28441d242000051250550151090008180617a402001381c4c0402400045400c03100382d81c15404040c091000c08002c0140384c0d08002c03040b20008107020f500041405540c0b945115803620380002c94142c41d02182840001181040e1490120419041c25402c1c2061111700300140100034980c0900e5010ba11078850a031101030300842140c40301109032007442d0082c0d404440440700c00362108000a5203030340010300ca1080d10070176200c804000b814a800d000083c4803d080855009800700340c00000705a00d480104095050500908483c1c01c0c842c0c1840251101a4080710340d10008115a0644000008014054401c121602c0c0c6c4042c0800d00104c0c5400e0040c035101c0b21512501000107000e0303c01910307843d082c400a8000703101800d01103100303407a50310040760280d810850001c4002d001d102c000c1c16420b0705140c0350400d8085501500d004901b247c20a820001c2003030004000d101401c40c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 993036861 1250 993035611 993035629
    0x60e0a02210105150708160f02150c03161b0303030516050f030402043206040c0503090703030f03020c0303090601030c12110f060f070609112704082205 67
    0x9001e80101c00294503050220b205164140c203a00c0268001117040c6080000300800c940071840074a0b56070070941020308003c00720000201d070481c172504416400040c01f07184d16042e0303015a10b214000d14105500c100008400c62040c0204607031820006110f00005890b03003c000300654000c6c0d800203002c0c0342c82c04140002c019020541410f01070240b190012551001080301d6000e641aa000300d140d070060bd2901030a091a042c881c010142e4070301c2481e0080900464461042c44115000d0000024039182a40c4611050f40c811b5105e4014060a102090050640100030110707480c0062512510012041c1150000c3c2c0750341d0820780000e0010030910208503100c1d0043c04240c17455062051143e558484941c80003d0210300a030514140010b550340d4000c20795051140c1400680d40d0380907140781c60300090140000c2100c0746a00c041e201c840c6820150341c9200078040110814035040c040740000034a04000520898510004200d0788041d200c810407050000c042c4d01180089844c00c28007080200c02d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 993038111 1250 993036861 993036907
    0x30e0a08030c0a0809030715020c03060c04122a0905090d0816030c0c020d0b06180c07080c01090203071e081203060418020a170106050a05010c1203060e0a02 69
    0x41d0040c440c1040c070380c4000c03404a018991044103d641c90b41d540c0f000c40e042c40c0c000d51140c0448618040214003254003c2841c1c8280b03001141555a01e0b039480c58500d05502442c01484408070f1461103402c00150300d82c201720300c1342c100d90480c40307521840903030306400c0f09100b0b4001500f943e4840b030900110000030020301c00d541e155418404840d1801016000110b901072009404150b103e8880150007800341d80170035030b03080e005440d00c105002d0a04140ba000c54003518054010a541401c021401882400c80d9019403105106185009025240ca003886e40069007503011955942a5420042e50700300084c00003801010100300b80e119001030940c14a11003a40030041540055900046c0218103d0440354050307030403100000e0048000404a011070302c0160000c2d00046200c40c00310703010f40c0741021124013104203002441881e07121028009003480501c100ca02068114082c00c0010306031510039518002d0a20b400105039649102c410781e251810b1720782071060740c1c0c0002d6101c440e10726444500c1c000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 993039361 1250 993038111 993038113
    0x1513060210090b060114210106020d0c1106090a050901060c230d08131202060114010e030703060e0f25060f140d02040801060803090301060f06080a050414010207030e0a08 75
    0x1c2c401540300d82200100c01000c40b4104000c0101d0216005030460070703114440d032040706080c00360380f135850240603040081c01144094420180242c1c807561151886407070555000340300401000d04082484515001114000c1d4442e01142e07003c102070b01d41c1c441150007020107540d00a1961202d00f010840f012800034100d02c01403e0b0440d0400e00c00300015444510411490000080d40d189100319084d00491040104118182c03240b80600c41d90018101e0706035005440500100d4954030f00558680040038059609074020080801c0403891700d81c0000705102507a425a07026a590380e13182410300d210f10001410424109464038203441c00c2e025040042c108604040e02c40c800031200181003915860b0b42c480b040701d00007550010100341d98060750010545d06009011858403410380380d0b121f03004030003441d00941c82d0030800143c814103540342c5422a03c040d112070160b03443d041078100c05404010001d40e02e44410400012140070240300070300081c0e00070b545e6030030200307404030401c0403a0412783c2c015115 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 993040611 1250 993039361 993039371
    0xf1407081012020d02270601031e0509030405121f06080a0b0a0e2b03051902090303040b12090105010504020f0f070c080a050a050721111513060210 65
    0x3403100c100503403406542d4004495141070300140300082200028000082d00910b02c0c40c400703021940c0c6407031030600350303180c180081450b560350300011400c42d403444d03101142d6224003004091044505a00a80c2c115200c0310680303280a0320741e004100020480e1a030415190700100f03040d81c0c10360008140c1451104030381e909105007450b201e1040da03140909507020706a80410008505650070952081c1150b0406505440d0340b072100d10056140022009001e0710b0400e5124403e807103282c82441218400c05d2907070049200356400c4440b40c4003c0d000840d1a0340c0600c010000403a0000303200e0050901100c59841540303061a00f1080a03080d02c0c1c0c1a44418040c0d07005000440ca0703648842c0c2554001c0d50071201c80d07503c417003481c241000703c3d9890b80d12160403401455010b00901c030300403a4a152440c0100c080b100c0c4039996800745440d804600082204002040c0041c80008080101218004000801e10000903100003500c541c580d2002c40c3c10411301c0c0481c4402c1005c0c54041c01482084a01c4000c2082 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 993041861 1250 993040611 993040621
    0x904020f1201050d171317010605041a03190c08060a0905010e2a040b0402030c07260301091a1f02070503060c0f0c0a06150302010e031621060f140708 66
    0x1c050f500d41411842c40c5c4011440c1c10a41d03007410f54480080038402d40300c1c3c91000b4070326040d40c001e0445003d003a02880c10603084c0303071f90000302100200a94501800810f0707001c02c4110041d03404502d009040715032603226a000109000e0070420b15005085215000804c201a490020b086071802004005190080d0210540c1014000c00c038810425038403114400b1582d0400000f0020304034204040d07400780c408030900c41d9400041001d807016500c201518090040c01c0c001026060b4051458200c07600b00400050102840a410584204001070342030100b00303e02c280002c80140102d91401d504100b2071494034880343c2c0c1000303028020a0168054100c9091580452405100e03583c0c100d5100c3c0e0b800186688060b0b001c001888500d81c000030200f000e81041031b03088400311110710007030b0f000803ca40100e002c50f28000c9914a000038592842e8000d851030a810107050000d0801000e8103201401c9101d00810440d00030000040f13285900002d10a054511490548c000941000100700c1c40d08200f007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 993043111 1250 993041861 993041873
    0x915020709020c1005010b1b1614120a0f05011d060414030c0d120506040e0c0f0a1e1802070c060e040609180302060a050903071103030904020f1201050d 67
    0x502980c0d5101c034056501c9840030b032690300d010440110104500e241c4400080c203800014060212000041e81091204a078541095911000440003148449420004010800b402e13841c0403c40700c00070300314602d50a410707102c01d42001038941040d100b8072000d8081c081040400e22405040b114001402c148084200004555440c00200b0003409600400e0100d20480710800c00e070791210b001b0f070007181e034210741c2c07124003c14110f10500d02440950403c0d003c5201c0b4074190051503c001050700040605240c900104458461103240294001807411000310703c0821140d0300180d1184160420b0444c9403600088035082c0141c0400c0500c8603105201c90400551645206022038445250030703800d5440c4803001030002c003d0380d0b2007202918501410082a06038841364000002d003e40c00750340107136440c072044006442c41120642020b400130891180014000a0389507030840000c1e00f12030803c2419404107049034000d81d044030340c02e000890300d0b00c0c82070880c444c5079024100a99083d040e41e4102d0f9260 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 993044361 1250 993043111 993043123
    0xc0f08090d0513080d02160b040302090f100918140703020d0308071b030903021008010e0c0a0203070b0709290a1407050d0f0311130b0915030115091502 67
    0x4003041010029880e41d84070611041040608443e03015034421000c805e10181d5a11807551a82c5000e01880600007540c40d2107109980403250054590011540d1700c1c1088042410000e008403015041c102020900c60014842c031080e812704003d80c0d07016108181059035800183c01142d1031541c2c4420400c1c001a105d9002001d8250350605100290b515502000e40c0e01e80030180d0b11104980f680b50100f410326502c000e000d070440340266404402c40908610032100c1401c02d000d07010034940b10345c01140390403001400601c0b00110381d1050703030b0514015580f1404041002c1d550f860000720b64160a0101c0328007060214000780c2180c81e4010041c080c0707541010940a42410301c0c0a201040051500c0c255040c803c85600c1548202965007420100b04003404130000614581c1c0061700d400002120004004200e4110341e08150401c4440c40c600002030035664044284240c0207490408543c0003042c04c0800342d03000e01080042c108249480400042c20b000ac40e9100740459100c0043e80b0300341540111781c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 993045611 1250 993044361 993044383
    0x9050705010806011725080601080115030204050411042111011b15150527040f0c080106080c040c2f1e0c0609100305060d02040501090c0f0809 63
    0x1041030740c0c1d942e4000698440d24245c5400380440c0031107040080e00000703160f0030300519020001076103003c03c0d031070012101c140d41100e0443c042115000180030100d845002101c20b41102d1501518040d1241c0c081010b90f1034442c4141000440410103100341e410041c94040040300c1c0b103100c1200c6649075100c05d111030305c4080032141404401b450041c01c0d0004456400c583c540c00c1400d40c0120f440c04444d1000400c410041d80c00070360300410b8081024074104e4261070103007d21554204544082261100102c540070b441140c00180d50201c8c400000c006101c4103005000c0c0000000c0c40c5450582034604090070042a03034071440c51701010249103038000c0322002486152fa02014075a00a42c4100c4680e100c5400c0410601e00c00c90020540f2520054420716030f46004109035010600342c1014002d00e4010500e100d9405440000003c0c640c0388203610081d03005070300030030184014030543c012808403030003a080640f0140c0c0740c40c403100e015900700303480402420311403421011910b0b0004c2107a80721006101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 993046861 1250 993045611 993045617
    0x11a04200d020d110a020607080610140325020a03020f06010302060d020705120f09040e06040b1b21011409191a06450f0613030c05130905070501 64
    0x6480c03d581120340e005025640e55610301030f582c0d85032048080d503a45011194a13001465a800144442c1003800303000f18900016110005038104d144070080c81c5400040000089030360422510030758502c040020009403a40303401600541000707080080c00d0642c5400c2d410495070002c001040161141e4040350030304138407d40014ac44201500d00f203410008500f03c9400701e14404900800b040342140003c00301d011084408010b440c0440b8161034450b07400300c9003e000c5e02c0003140042c50906e104c2c00106c04082d440c0c14580d14000d5889041048144600007001c0c004410f14018003110380a154841100030040303071031000310b00d0661a0140101d440c01d6140e4a000d4680c1604000300914001030b03409090006c2405455030b54500807028004003080001040e5200d614028012000a048a0544007601c807541d102c0d46142d003003802a20112240c0054101504104040d0a03214001342c0c81c018500c031740f4100c00401d251400300201006041800c070802481c058130302e0002840020201c086030300c20b003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 993048111 1250 993046861 993046867
    0x1e13030b0f1806063c0406080f0606060a20030a03060501031b110c090a151703090f28060e010f022a090703050702010c080423030408011a04200d02 65
    0x10400c1410a100031840c62038003001c038902c132801400140905e203940c1100361820805a665444100d90b18541c072410000c1e160000008940b59040c000300030480751095041c9000041034000b0040c5900d47e804581d2441a01f010a44802d015414060342c00100703001d103020b1001c00c141011440c14800d016442c1800d028940e80940c42e060340c2800720075541c40004010341454540660f43c10050312511a140c8000c50f2205004110654000c40240107481c4c250010350070a0444810b008030016041502e0303600c1f20364401103501a0000000200c075001050032030f101c183d403400034050800d8480c074106906020800c070300c0f086550390015403000c480340b21180c1e80c0b181c200c48801c0000110100d03200f5a4000340c1381e108011107150113822540c0541d400d43e008001e070080424007201c910b94252002071603c0c0e0703004a0701c030150038100525040130110600303803803801da1746503000340c2100c1140051921070400e402c0585e00c90714040c4039480801c500c814125502800c090b0002e06140700d4140140382c2c0b0f507404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 993049361 1250 993048111 993048139
    0x615120f0f11040302090603010c080c030705041205030d110f0703030506060c0a03080f01090504080313050115081f0e150a0b060a050d0f0b0102031e13030b0f180606 73
    0x1074100715120303401c00200300400b02d410b00200e001e541c01800181d015524486c0400d403181814803070141d8107006075482c6540c036210101e05480c1c41d0710140c8410304022007407002150400b64288070085083c8500300555644000010041c16501d50500b90356a021040c880469000141000c581030300394107280c006820360347c0500040d00c034060850350310898401c280d0800d00b010b07000010035004051007496000560f9030390000505840c002c03640180700b850700784081403035409001c1103000302d503100d1000810400400315014014603803e611607c03140c0e100d12811000703056080800600d2019002c000e014104140441c166a071940903200740c6885c4019001900c1880d0640c0080c031040b00c002c040c9a0b4810a03404010140e4000300406030301c55142c032480c0d0700351201c1e0340318552500f981a0055070030007200d074402040c43e40c0c51000c00e1000d417504008005060400e0b205580140d803055480440303038203200d0110f0611001c000c009040010300005803041d128400200d155100c04115524802c500c0d070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 993050611 1250 993049361 993049391
    0x507050f0304030b0f0f06060405090405011e0b010306060c020904170705070e010e0c1606180f050d0201180b1501120c021b0102031602131b05070204061512 69
    0x4040303044403180c00003080c0441000394050703449024521200312080c0d9622004c039454640721007950b0143e807018040104001a052074041d00380e1050142000003555a00c3c600141c501c0040703212205020b40c1d440810000968049c070403000940800e143c11400e041d5243d0110310203807009000a48100040f80d0000c000d8a0703040226024513500c001600c0e489592141c0d84400e0b07050a015a011003040240040e1045031041c080e204001c0c0d034014401501d400c5910781c140244504c002d22040100c240b00c42c04041b40d407800410390068480c4009285e020007a540007801c60341400740682ca0680076075a6a000b181610202c0703030f0003000d9458903881d00030b07007040103940c030040030b001d50741d0002d0801000c5c0c108180c01050012030040c4803103c1c0e65045203090012600c0b032061914920756114241035000c01341c20204a00101c8990580700041c2c8a03038003003440c8111003140615400041c1c0005500e004500745401440000c01c00d040da1004076144070b10000e44800161651062416a01c50600d060040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 993051861 1250 993050611 993050623
    0x513122a06240801060e090d120b030102040308030a06050111030a0e0103020d061203020d0203040612110405060f0315060f030601080604091e062a110705061303120806060307050705 80
    0x4512108104503002d2450802c40a640910400f401940b810900140a00d40000a04d00c20300c1c94101505403010740e00410f5920707151001c0b03c00301d00381d9210f2603540980c0f024401000a50f0088844e95141d251440142c421340700241c10450400c408844940c03907420000055403022021410100a20388034040101c00900506840c00046400d1940014242c40e5070084401d9481c002d03800c0d20303a2494903510a030380c5c0f803155108940002e000d01c030304000c102c038040d48171100709400c1c020170b1498030b80e40304000b43c01350300700002c0e41c104010b00009022403400c2142c03a01d50244401d540e0790741002d40e0340b42104120300004000b50705100c61500000c0d0144e5440d03100c8641136038861461100910007228020301c0b83c00304401103410390301d041060131b80f04640b5850480f41034017820042b0131030300e00c444d400c0f1340000000445141034450703070300c001c00c641e99070201030f0002c0b40345100d802c03032a14990b05200c0d01c01000b81d010b56003032000c61000d00c8142d031030785811240c1c09481070a1007551038449140c580c0c6064 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 993053111 1250 993051861 993051881
    0x5071e090b3a0f0b04051b090105120a080c0606030d020d02211b0106080c040501211406090c010f0c1109180a060c030e151b0c010513122a06 62
    0x50b90000c3c11504002c1041e40b0f1a000d140500c044440b6554400300002c044906040a25400340600380100650710381310708004048801001030311003214450707881410035000a9200c00d1107420003070801c00c650404116406401c05507100419004011f070034003070b403928046844000c1c1451085450319820800c070086890b80810345200340800812a5400c82c0240140e0041d00f025004140d000302c0c0c0c42ca4070f8002e07141610034007040086034a641c42e588144007082190708699a51002d0307245681c0300c01c2032241e140305002d801e026184510904000420340c1301a44040d9042c00100b00301100420b07480c010390f020fa5003041c4e030b60218030b4880d8010959218004c000d0620180300714401c0c01c08010560b0061007038031285840500c86801c003200807603145c1000550424040215800080f1400c0504d90082c43e0b48094600305480c100d40044120b083d20b81c11201c2d1101c1c105420454004c0294004440782201158a1300811881489800c1c5000044060100c6d40d0b00e000c03200480309014050380249401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 993054361 1250 993053111 993053123
    0xf02040305031b190c12240516110312150d0c1403030a0f030c031508030a27122a170102040b0706020705071e090b3a 52
    0x140e0310011034803c904414000303018140160b0301c0220b15140300300907085100703900144110545050044040d1b2940b2068002c5ea49100042107400d0707007015a41081c0c00f5410306680c00b0817035141c2216940d00a0360002c13801c0040110b0b2380c40301030307080c20044199692a02e01504100080c3c0302c030f040c2e654680b48180c0701c45500c01001c1c4856030400c003000042d1001c6070320f90814101d803009600c0c1056103d000d84800c480210310ba42020b036030000d2103644202d040c00c0450900007411103401402d075001100c0b5801100c90b80d0300000341d804010b42c00c200301b2080c00f1014040d003114000b0203804030012141c00d01c60300810b910981491401c000300080e03040c07101078580444071290f45600c150280030340100c0c803803529251400c01180d90319141c107001322003d82c0c0341000c180f840c104030f550b101c6000703500143e8107650500585030081091082c04102102543e060180303004a0303030518482d070044801102a1a1041800c0c0d48a444034141414004102607640c00d8103103035a6112050b6444e1a40040c6002410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 993055611 1250 993054361 993054367
    0x21908070906050f061e030c220501031508120f0408010e01020304030f09030309052101050703021b0c130504140d02011a0118140103090b13060b010f080103060f0204030503 76
    0x840c2540610200e4104641225040c054602400800e1040364814000000082410300e400d06d885001036800c41c200f42203003403800e010b80c00c07509030034000b0078114a245503060204014541c0e05005010f40500380074602c1080c10710b000701190351402c1e20141c44100c2c0b43d000c00c2501161000d401981c00130100c02009000055108650900030b5004440480204d8442144050707211b204501c600c00341d903416222911036908000400c04c0294220103038810b0008922403038140401e080c00b52a00070a03c98502603140c5901c1144404107210320000c02c04c2caa80308940384107c80c0e0703a500c80045485001c410000d01038407103040800c808880e40e40a1001da2262448130703880309030f0541c44802d0315142e00050401c00c3d186072004481d00200c200d02c00d0400c0350042004e11900683c3d030941614404141000901c88042d6a591041f07407000b01c9018400e1075a0000010a100c024069540041e00901c1c00451410740e6600161806606000141c45940d8811400040c045198125409160800e040f240c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 993056861 1250 993055611 993055619
    0x150c0a12020d0c08030f100b1603140a080105090601031b05120f01050d060c031e090c0e010b030f040201021e030c1501080c060717121006051602190807 67
    0x96446419124031005119a8410080d07842c441c0554032a00760b0320490707083c0b454484006882c3c40400180c8002e511b075504d200c0002c0d61f96196401004003503019112100c2c00f43d070b10305000d0581c1002004010b4021010441d198440340d00c0490941504e00c05c40c0d5006507501d0f6140128000c0030204024604c140c03001c91220403654100300505000b10103010115519a104c02c20204086401e108454000c5000d16250700043c019421600302c4220504d000910f0003948030206281480d090305502c1000d03554420841800b505e011550060600303950380d8803055142030300c1d44409100c01024040c0c101d15400200b000c6a101340b0584109561414004009143d0f032031901c0d07200c4d442200108014412075501008150311144124100c50900e0f0240500c4407512090010aa04c5254100c1d44808107800030014042c100300a801b05a2402c0e81001c501e141c0541e602c4004141500421b0a006040c02418448502072070180580c1b1340c1640e00030403c5800ca50b0303400c940c0d00f040d00103803102d0003811070100e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 993058111 1250 993056861 993056873
    0x5010f0e06061204080705161206110702030d230307050d0b0405060604050d030314092104180b131a0a14181f060f030b0103050f010302150c0a 63
    0x1615010010315a540e22028108030062044203102d8100c014020300050100f8020405008041d01400540700018201c080c4600c5030481c0da04482000301c41c1c20000814420b907032090042262219038040e01e040c0301c0d50002540c4911228450003000101008000c0880b4400b072515a165501090140c4a04050790701901d01d801111000b60241e141006061251a09001d401c0c0680300142c052450241420107110484034201015012f140e140e601e81e8440402d04200240702c2c20307041e406003000b8141ba03655698000003590040e007c848007400709110f001003000c01020100f071080d000040700380d01c04011491103108480a00002840e20400c0014481e05920400540744221521301c00c650303c03440554000f04d001c100194000c03820234900014214120768581c3c2150108000400c42c2035000344000364010181c010000103404042d03071200c4c07240c050250907079030042400c2c10300c010f10f041c24030610904814800039203c2c070012406901d221880100304c401c12290320060320004034003400c00c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 993059361 1250 993058111 993058139
    0xf0919090618050f040c05040f090b1801060602030c1207030c022e0306060e04020306040b0d1b06032d11120f07020307020a0e090c180a05010b040807050d0f060501 72
    0x1240c00d420305000070980100300209500ca2603000c00c4850806d402c000034400105200121500078969422582c004188402080c52090109000f40505110302c0b019060a44505034801c81c01d6500074040f0b900d98490101e0b6884041440030080c54480c1c9040c00e0450700c0407048000650440100303811044000fa01030205243e03400b000f0010086203008040c110100d0f0600e01c42c420014221010103495803420350015a04094004c00106020203140005081100085000c031820041c0369207044907481d030902130500400c0345040421038240b03100c0040d080710305283c1011070060b0650402c48840441d81e8083e080d992b1401c0d078080e4072121079403c0b2115624040c0c41110301c2100c0e48002500c2c41d8400001c40e00c44030380c050a071031303c11441d001e003100480d40040c0c0586030f0380c014949521915156108c0003c1190120b146020082c28203001d03010403540c040c0c000745000303034040005002085000410038100c0b0002d0f55403548901e4542007042c2c04035004000108003d0a00300001100010350b600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 993060611 1250 993059361 993059399
    0x90c0302071703010f090e1507020a1b0e180111030c04050301050901020f042615070816050a180b0705062d01030206030601020f0a050609120f09190906 67
    0xb00740060384076004405a5000c00d11590400c220848014098120990480f6800586003411504030f08400c4100e070754480c3d01265a1030069100c1c02c148400d10818859001820304c6104214046604000503a01e840300000c0c92030200102904402844941c01d6100c40702c00c51950b9940340d140d040815040d581030b4424424180301e5802d000102e0300b41c4030b06100302d8414030030400c0034901d003c1c64403200c2c00103c2c4407410205128409401141e40c0048240240c42594034003003a84091031500302c1c4040e10746030001c1e001036000800e1507075240342c00307400c40100c4221180904017072089030000d082d010a501d441c2e400800032800e001c507000040140000f00c041c0600c0c0d0309039660b40724a8481c0f00352055048158801c00491444900410150820000860f0480c0061041c1c681c0441c850845d50710304a01307001c003210b0903408481000030400c0148403140e51980d02d50f14a0b458281a1111700e1164040d03a5074085c13066051200015000e116004108010030590205010b2240d0f25400c0c640b80e8030000c81 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 993061861 1250 993060611 993060623
    0x60a091505040507050a1e03141501091d010b10051803070f0f08061605130306090c0501020d0f02150705040f0605031f03031b1b0b0414030303010509070e0307090c030207 75
    0x3022501c815488950503440148039468a07c0c5071554507440ea074040c81140e00901406400c80311190213164900c8140604008000070814203030004040c0d511012941207501076034502510924181c1d030b861102200c0700745501e03089440b1041c2c2c1000c4003c4030840f0034480d0b030520030740a00240c1e881501d0313944001c80701d4040d040345409075160f411913101e10301102c201d01640050b881305100c585c0a140030381020703000d00c0c1e500091a41c5030f5072800304464030120191014401d9140070082c0d0b42c4d04100100c1d0f0207015103402c0d007a0a10610002c2c1d036503200102500c804440c6100040c9689205070265001000c0e0340700c80300c01c0c00f95078400c0504254001e450225441682c2c0400020482081d80300c01304880d4035540c0e10f101401003102030b0005c0d1a15035011604100182c0c00040c40070807440868024000000c0100e035036074582040752500d90400c0341118000e81041c00104480e91311422402d5000c03031141004040079000c10002130500d4610f40003042c0c136601e012407440c0c019031705a0140070702521030f007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 993063111 1250 993061861 993061879
    0x705100e102a11061f05101805032404020d0602072109030c090203090709150602060a0e031b122106121903091d040c1502060a09150504050705 63
    0x910111007084003d25100e54907030008020805809403840390241e43d200381c0f88504d0002d03031105d001561400c807070640000014146128040c00c00b0301410b90f18000d01e03040380104840f0007005d960580300e00d046c040800208000000080c01d5485134404061083d50000c41156242c01900d030000c007031503c9080001740c00301002e54840d034441c018070304801940c1c0c014180460003071515016601a60001300070000342e01411000083c0080c0b14002c0c0c0c603249042c02c0d2111440380c28050002e10349040180f403280c01d039041543c070040d0010080122511183c45680001c1c0740000072101d00d1504a0b4003c104460b110300003015940c0300b590780f103070f510f004074202d0240c00c19855810410503d0000f0b90291001074120040c103401141e0140d0845005600c41d040c035211b440e039240e9502c0c00403040f03446110bc1e500500d20401040004400d10075029001c81a0000c0340c03002028002076603206e004000300751044e0b40b003044805001c880c3d041d2040381c1c50103c0051001d4078180c9825600d0f06100c1c81450f000d00122 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 993064361 1250 993063111 993063191
    0x70b010b03010e0a0c0e1002010b030d020f15040804030206070f0c1508070206040302060f09101d0111040f0b1608030709080f0a02030a12031d06010510050705100e10 73
    0x940200f05c81294142d503800401d00c5100104481ca141d0407002000390340d650b20303660126440511042c541102c42d82c0142642040c0800050f0801d039556030046000a1800200320004500a0964090342e8065175040d49618261400c100507200d0352002800103400320078005400c20544e00c103c11000c3c02940c508015445084040c4c1e91500d003a9001000360b0000000a00804054648558005010021681120b444013601c000300d0f900741ca031045410003503c01e0104403242c24052054002c0319034125503d010314216044071001e0f0680034900000900154040c08440c0410780e8040141d0403a014554038107024074081c1c201d0070a07118096040c010348420f1284a1004200c0a41c0540c01402612408000d980c0e0301447c021022641428160b90380300d90314801a14015201018034001d005000550501c006c11140ca0821340c006003c10804000441c0000c50206039140c0d5601071020104200144c0301c074903802d10301d0b201b20310601c4915021700c40c0b10103d1101049281c0b40c8892108880c00d5a00f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 993065611 1250 993064361 993064381
    0xc0f010f09030503040615050d030507050f03070b0c0a05040b0f070213061512020c0609060f0a050c19031416080a180308090c03060408040914060306061302070b010b03010e 76
    0x41c000c06804943c0034000980410002d4001310b0555981da10749100c00c1c1d49840005041858060003a00000c50100c1c0c400b0820800304061160440c540e40218100041a95000c00d80711004004c1703000043d011590f4000c65008100760790107882901d4580391100103d5000d1a050b401546080e03200e1358a16a01000c280c8007071060400766240ca4041c00601340c0c0c100820b4550a401c8103014a950380d08001c80c0d90350306801d0010b070307003c4d10107500a48018280064400e0744403078040c0588021038504001d200c8403e400350b0440d610390a402c07066013800701880b501900204203402c0850124801d44003003040c1070310103104024514031251030350341044d103c05024204030340c0012100d070a401000da107200f000c00e006824256024110b40100c5905100300d001007401c152007a40c2c03c444520740440c09210010040c01120703805800b6001d405658540040040c4d6509400b41ca190700035030200014408a505603011980115000700600e409565250030284165009100b502086d044010100b103203090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 993066861 1250 993065611 993065621
    0xa0b01080105100f140f0910050f03040b19090b2202030a0b0402062101150804050d05031803040b040503010b01090303051e07051015050315010312020102040b0c0f010f 74
    0x8000740000d894500ba100c3c1c00e03140403071982100020b00c00010600081080007000500b4407401d51120541c6482060040c020f00c00512034800c41440800e0008c0500782400d1401d803a80305802c1407100d012606c0d030100360a541c01009580000c2c560418a2030000d000a03d02d05600030402d030251607225100350b030000d015810403050003e5240c2c200b03401c00d101003904210b081d030f002800102a14a401c070f90401011118076003c091480d100101c00040120041c0e40b1a448200312990034000c0042c0703890340d074030780c0c854203c0c040300018000c0100c08900700d0b075269110710300701c00100c03421a569103460700510720300340e081407013624030030740c20f00340d506170f036075104000035003c032a03058842c142021500d40704080c006415960b2455500c2e0240701c00710100300c041000c004005500c4000140c140e0f4070004c90400f80c07025400c258003d23070040f14164182c1d8400d6030311390704582c1c0203400002c8a02102004038064803903903211008a0501190a110405010513901c03070b0840800000c0048810304a415801d4070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 993068111 1250 993066861 993066869
    0x2070e0702160b0c011104061d0411030604091b0608160906081803070c1217090d08030a021b0708160f06230a0302040815010b0703121506080a0b010801 67
    0x1d02e802d010404480c3d14006448012150310000c1410350308050110f4260b080303980000d000842c4a814504c80059840461080e00c1040d07406100f03100034032075402803610019100602407030740d4001e80070034400c528016642071503c000c03865a41035601c01d40105501c0c4241c94104502c0701752611100240c0c0916221401c540883d00d9588260f030b15007501107405c00300024008558001008080700003180307803030b0304c1c0090039060031081001400381c20308031345001c000caa000b16441c404200841903583c1d0f1a407419001d641c4142100d80d030b40d8901c01c490019000700201451750880412104200703000c041501c2d01940c0c59501110500b4a4108000d8030b6664948101024000000310178080c50344211140c0b48150044042060a01c8580c001000e444c2d018546100000342e01040c2480b0f00d40050040c1c001c0510004134102181d4141030300c100302c0d403096940050611083c0d270004500d0b18042d0f0001181d4542c000e0a0f4450140d841e00041c0100794111a018501890240c2c0d010a0358041c40080e0706803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 993069361 1250 993068111 993068143
    0x504110406090902070b061903080310060f03151e0305120a080702060f0408071a250203030903030a050907080703050d120c092711042103050909180d02070e0702 71
    0x340e25407c007840246a1401092031408620010100110342c1c82c1e0000e6010f110340010322040140b0b00800200076802ca0340c2c035041014104809040c03c02c404101e408140d82c0302170407241c0400c004103c0d103400c0e0302a0740c0c0010020300074807090000f20b020310405010552903e840d2410203a0750440204e032102401c03504240c090390100c0115001c0b600542c00b6024480c81030608065151640404002c2900c0c11a132100441c492005841a1103c0894044014103c240002e50441c10000d41658a0f8000100700381c40c201e6a0314009540c2e00d5041240100910503081079510385601c0e41404c03500e607503403a0340030008104018450078a4000e544245c0000710a17036030302c441c516400d200e240310300f11004e0182020340c8801d07040b191140034141d200c0ca8005200200031182d46038680380180f4a440714150310307121540c400b6124800407a070003204507404423038102d80303081e240e41da001c6a9510406c00011154241e01c50524203038420b5800080c034100796810300401d12079507500c804049a484802d022181d00c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 993070611 1250 993069361 993069383
    0x10f0303080a1112100501050a0915030b060c060a050f04030804030e030c0a0b03061002010606091401050d05040b04170a0f180b21010503240709050411040609090207 73
    0x10a114200303068000202e19004507a01d2106626030b02c4581285000e141154024410b1081c03011061050030020a402c1c00e0007030400e103030311001030848401442000100004003050b14682803082d400b8280416004061640720030840740e03869030b25413007210444451481c280100d00d02c124008480e40c410390303050343c0d00001a0ba413550308440c01341d4080e52083e0544251105211036030b03100304244001d00b11f01e4240d29120728001041005c8a41d030b040000040da458150240700d0341c1d505c60b0801e01a100c803030b100100e406204a0048070345102d8081305c000300c00d03c1d01050104020b00c001c80e2600035400390146050100c640780c2c40702902d1003814056400f15170b100004202140c01810345030382c502c10490170705d00500d640b4041901c444d401050900e441596501802d440b84050003510b9000d40000d8005000e891406084440648003042d200c8891a8406000400d8944100c180c04040c3c0406002449001d001c800e12080d990468007820000c00c1445c1c02c00b04110140c2e02c00c0d0703100035800c9107880c60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 993071861 1250 993070611 993070613
    0x170105070e1f140a0507030225030215070803070302030103060e0c0f1c050a0303090506100b090d051009030f021209130e0a0b07080703060623031315051e010f03 71
    0x1e103044001c02c80d020b00101012041d8502d031403102400810300c03d80c4a480e03071410f052400030301348513071800002e1116414081d018800580d104005042da541030720000e148890900349040d00380106800100140c0e00001006800c0354140c000e14100c1e0310a80c01481240051150540c849102c5404282c00001d140348844051403d04200d03280d4482c4525a401500e065460305410b100d50707a401078000c02d496100c071800300901045500d5010101a081008040c101600c2a070f00b44504c81340782c2e03c01e004001e0f03010144030080c0995460130f061600c0130401030001d8500501100444106400940944034a0344100c401c031204880030514000c0a05080b150164520b00c0103002c091b0000c0054801d003031000c0c2c0050205901c950080019440740c2503c2c0c5015a0000c003590b0b416081841006100074a84d040300c030000c4131042c40501c004c1c21040c1c481c0c0c0e07a1604101e4001128070054840c1c001140400301520842c2d2281c0e0140346000c070400200c40320404440c80d418800c1c490000841b02146c4100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 993073111 1250 993071861 993071899
    0xd05070c050109111309170d020d0e03130506030c090d06020c061003030908030a0221070516140402040302091305121c0617030706050406090f12020c120c0f0d020a170105070e 77
    0xc44a0323107049a00604103510400100b040301c800803112140d0358400552880d200d411400310744002c080071140c552031480d001d6030f070341c40c28014040d40304d004110345070382c040404c0480d4041c0c1c1e4056413604115165441c2c00000c002d00180548416000b0030109040401d8000021080350710302d181a40003800201c2c21242c200412000b003844c0380c01010710501c0640b0001d070307050086107044100302c002069198140100500900c40c0c5800052103103104000810050b1a1504032607401403a05600382941d48403824101d060000044050100d4030001407164107400307410300c2e8284111702c4c1890401c80a40c655590343c0340e00040a02c0040c655005004120024030303540c003c2036000340316071008121070489030b6810041c204000e60403100c01403d030f00c0300ea000680c1082270840714142200d0003641c1b402c120390083c0d00c940d00140d032140111070f0b003800c00320a502c0b07142c0190391541e809081107a03032960b036a50000311100103050004980d400e100c0030034042846107003401c084440081c00d60341c04000041c410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 993074361 1250 993073111 993073117
    0x1020a0e060c0f03040e1005010903120c050708031606050a110412031101060605040518060108130203010b13020a020607051c021b12041d09030d05070c05010911130917 74
    0xe502c00348161040d0030b10382c41051018000504100c0b01c90085410650000550f040403038015504001c201d020030400310303034401210110142c0d2403c00890f00f451a00300b00703041600c1a084400d803132200089400380412401c1c140d080080c0603020070402c94548140d407200f51900c0c0741ea42150f001040c003050103400e4071402004906446030030007071408058140311600f0354006900100201c1c5005c01c040040c3d0804c1402030103071082c140321408292501c400081c0c082c65001d031000382c92010742400400cc54401750301012200d00003d200d030040c46003c4468402a42c0b00c0d0740c0d218018011500407402e102d0080090b107180c0281c0d103d40307121041c80801c9400094011704847c4c480c03500c0c0d001d44004064010b1040026009000c0115070341c039410b1100c170030550101d8400d1070342e1002210701008006500030003a60101e10b140600842e654a600d0b50443d00791228500142c4076500e840c5520042100001104054903001c2d9480d00c242000d02201c0004c82d54074140c00341200d8140c540d00d0710b1190a202c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 993075611 1250 993074361 993074377
    0x1021602011b0606060905041b120b03010605040f05040218010e060d02150c070e130f080304050c060f04030c060f0c0b091c05030603011b05162105070b0901020a0e06 73
    0x6030000c1960b07611240142c41c22944480b0100310444c1c1d05010904050290060078003010101148845041400500f0141255282c051099861445451f583e80c2900008024003000704240092080e52880702d005010560b005c82c401c0468042d81c47c940c40070200194101d035000321007461107640e280103101800310a0442283e101407850301380c0c00b00040c100054001c000200c030041040c18140107603140a418090008040c54801c800b0a9000902c2c80c030408007100c1d07002d0344854681d00c0b6440d201303107042c224220b115880b41011400c001210ba501012b0421170340504030b441041e582c1d032803060b1000c00c003444940b800521111584004984c82400e0031750032402900c00ca441e984004a52482c1020717120940d03000250002043c450a0b19090044400d00c0c030b4540303090310b00502114406840d6100d01c803040310668501070514414061400401d020243c003080080045484101004000d41c5c0007400846c1c60352075000220b000800d051082c1c1e210340200c0e40319190040300f02810428590480c0c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 993076861 1250 993075611 993075647
    0x9020105032208030c07151a06370806180a0b030a02060c01060f0806070503190905150103120801150c021513050123030a020706090c080615030102160201 68
    0x18a00b00040e114030015071242192242568441c1c10a00c0c040320385a02d400442c03180503041090b0104181030311081218420000c40710980e40f24410503845098800b0b02c0076a0f50131354144000840b4a15810100c4030140400d03030707220b02c40360f607811040044a2551200e05280850f00e40300081e40170b6500d50285804000003003c840340c11080d07500182550384000c0e440503440e5110395040095001d0305407004058420070014240e24600400020301e1030100801082000c103a0180b860321800440c1d21950916070400f00741e824a5840710a130103010f078801e10040328200d03140612410000d102d004028160781150b020514084120001165000f803240301c02c3c1c1e8484030b1a4104124178941b80007d25403461508550000345240c01d0002d0142c800c48546040d82c090a88070000c0000449070459901290b041c0c1c005840311000e090040043c0200d1388010031040e100301d001304810100040f524443d500d1581c4042001042809050a07070043d030040da82c020401508580c010341c00384942c81d1664055007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 993078111 1250 993076861 993076921
    0x110703081210080c131e0b030d1e050a180303020106030b090a02030705060a0210050a05040b0601050a09030f0c091d10061d0a0b060409020d0c0306141306091109030f010902010503 79
    0x286c281c002c540b036507150b00310801c1c2e59402208030b608042c015901d07082068201442c140030a608400f18128a455000c010400005204040d140c065214801580d5020051b18115522807a000c3e001f0079160006840b40044100051041000041c560043c0f40d40034000d050039901e803030107000442d0800741240c000c1d0301a0345400c0358400d03400d200d0b50744922803140c030210f0281010304001c14203005c0a0b101c02e04010342004803080c00758010b030007842180c1e400a441c00703940015040443c101a6150030020905060280c184080c2e84170014840075490f2240a070744040c04408030140450b481c82c40340c4082c098135100c0801c4400103a25040d83e0200090001042d4203416100081c140e40c0650021713440d8540c0401c0500c0c000c0405d105030b000d081d146013410842c481c1000240ca141f610091603e6126801c0150742c81d140001ca034020744000c0c000b0000c2408800c985198400f40c0c0d8128488150181c414011500d00c1c00c241402140003054042e16a507117151680c0d0182150164000002e110000c7c0c070b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 993079361 1250 993078111 993078131
    0x105120c0c0d1d0306060105190201061a032e031b05030111040f0b090901031212020309010905060c040e0f0c0415050405010806040e060a0c110703081210080c13 71
    0x10b0104603201c0003940c0e03030050480b07103542400c80d10b241c1420506000754804801c01c88a41d03003203001c0321905480499641100c210300c80c0c0403400b400c016001200800b58810071214a044100040c50059883c8444085868000090b642030085c4407008071026000481d400c20210f280d8401d003200400d450b843c2894215100c80100b42982e1200100c00455000005e04018003000390100c0009050a80c0d500c6c1d01d490205030001d100d40d601030102a08940003650b85200043c081d480b0100111f0401d402551a4030302058aa8006c00806000303407000e0042c0b50001d240d1810200032102034400000650200f6102c103603811b40050401401000079150810004c03400580b4420403504411103540d4040d5618242800140fa00e1000b5140a000b10b0400c2404050943c01054495022002c01c8000940200d080011a540314240301070142a0056210110074000d58a0043c10641c0700041e00b4040b40c1c40b03a0244510b442060310900c5c0450304401c451080710b00d0030540141141e030340704001041508107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 993080611 1250 993079361 993079363
    0x60604140a0b12030f1902030c07150e040510090605010e060a030c090e100f06021f0f0902060301090204080d08070c0b0c0d020a0906140708070b0c04030c080102130e060105120c0c 79
    0x1113262501c042c4035010a900b1b1007403245180c3d020307813101c4500c040c41c200041e14881e241d80740f980340902c0301d40030301313401030003003040e200710850700c04444002c1c810700c500d003041e80e0242c8480049004100b0081d0030040081060350144043c820304103c0a0101880c6c80d040300000ca000b00307540c441e508104016144001041501a4400f9000e858200080c2e01010701c1c0c010720064203441c69000d00259000030081944881e800070750800c00301c200ba64049580821121480020918860001d40c000e00102c004a1410010b43c081c1c01aa62000c0844081d08070007401035805500846001000448a044400c0010f03250b400e0150070640c41480c0608000710100b5600983e08904030560015a80500420030540d2000424000004980e080340c0b40ca03421f500c801780188141074000c0c00341c0001c0340114880e11151001c4030019904134840c03844041e00c03181603070f001c1c0d0b010441401d108450110041030049240c0741070360250350141c444074a030250b40040002d68243c004c0800c001c0b40000c0c07010350540f0710 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 993081861 1250 993080611 993080617
    0x10f0302040303200c210105061f0e060d0906050901060504020708072406120312050106020304050d0813120b1e010501080709170f06090c0a030f05070503100e060604140a0b1203 78
    0x4258028201100501c400d00c80c03c45000a027030310310510310314140c80156090070003969442415172810310200815880800c03201d11910200d001c24a240022510038484039600c003901400f4884000c1c000a640c0da8104020f9001d01c26010b000703074004102120014500310a018003c40c54004c1c5071080798105403200302219510381c4110300c81410400802c0070035034802280c80c3c01c0509000c04012550500d440255039000e5406880e005810300c0c00300b00d080c080514191000245484c1800212940320025008091650403045071030b2070070035000c100a4a12042410180d80e20b141c0b03100c1e1142e1034800119400d032406011002400600800810003018004001d600e8202d003500810090680c071040700d241205c000e0000c00e00340c01009183c0507568505030301c02e00312604190101c80603505803d0090030074840b0703807059505120343c51003041a003000f6008170908100c0b010503241c8c20f5079017800340400c0d525440b01000c1d0902c0203500150000400340d025200c0c20700702424040c010b20b0703032100c481c0c03440d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 993083111 1250 993081861 993081889
    0xc030c15020d0807080a0b010e060a02010c12020c060a090f12030b01020c120706050307050409020c0606040b061602061e0705030c07080712030305041e11010f0302040303200c 77
    0x5280324180e008815010070901c410401d031442c014007140b41c5068000e041070740107019450121703200c90000485a00c541c151004480340107280d5540c400d0002e13400ba000300403120101e00496a503180282030301000b8800d459901c07000d40042c100395039500551074000e004c4101c044070b541044520b00c00200384c0c6090364020486094a000035000c400b07c00280c50842e00c01c070350500c25400b40300e01502c1e0080c0860b00c401214030a081950300c0c4d46882405890304e0149400ca003c02038408181000100c02c001281f600801081d201001020070310400c1c40034a10941d00031040c1c004c880c01aa0f8018140140140009204c3c1c28041100105c22040400b560340000f406480c1540045042542ca041c180b041d200180261002410390901d0408049a5030011070b80c0a002e141d0b440d000a8180103040e14000c0f001d4030f1400d491100786115151200c0f8081960a54030b00003020b4201103040309000b0300c04c58065940580340d1500309071050045a4551b0450b07041c0c0c1c8818040c500c0814503680725010342c1494a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 993084361 1250 993083111 993083129
    0xc0a081b070f110a120209040609081206270f1005040e0a0b0a05060102060c090604031a07030c081b0c0a0503030708340806280e060406030215070c030c 67
    0x44400b50030b0141401a070800c0003481a195079904000c001c40b00460403105a60545160003d55544e00381840240021a40130b000001c00241c058101a41130380601c0c460032040710850314200c658212400e0b1078050741e044445c0d080684000c1440d203601d0510440d4000012500e1000268451002c2019211080c4021080740e002d81d51240400c83e2400326a580441540c00c2001103152090000b0341d1148007805255005400048503202600d86a0845d03002c0e54012030185003220307184001e50740c080e804a820724006440c1001d01301d8074074860340626024820044000368100012102c05240b40e0001c004114240305011000c000224140065441450240c4690040c1d1604581100f40002e10300790110080c11114491144d02015420030301818440e840c125007190345040204002000e030740210b610000720740712400001000c0400d0402911881320701c5007650b494010900007682c1080c00000c0d84001150104030703002d0000e002070104540111070081d81c1b11f070340c0e40b61640900c1194000700e440c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 993085611 1250 993084361 993084383
    0xc1233050f03010c02070b03040c0816170a0309170a060e0f101b03020f0c0604050d110a0b010314191b14010905120a02120d080108060c0a081b07 64
    0x1007454030031120801c64605400a10511048200c0292500c0007401140c11004010000c2401d104e51203181602a100f03c0088501c03070001440186c0185000344503115844888003040e009000700491808074086c0c0c10789546000300c3c1080079203c412069011101c142d4441c41c088200402e545008013100a1620341c09010f102441385211803d1a801c080d003260f485003030519508003000e500003920b44071f4550307140040c0ca031038801100c1d4149108414504c0054862a000e20060000106008841e031040d601c508455115001c011074890320b00d0341000c1e1900c034a0000400c0458541d5080b0429070b0205420303501c500356150100c004d09480a031041c3c0d54003025600e42c244000d6400c0790b000140a00003110110340340b901000800b818580e02400d0300400c0c80b20503c040b1041c08103e01034146030300920340c1540b00011510f480d500d0403000c01506c0055034090002a0b180c101040c018000c1c0021280b2903e41400741d90706454244000d0b05003000411005180503121003c0c6001d4841507215411400c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 993086861 1250 993085611 993085619
    0xd0f0641041b1701080d0c020a0302130605040f060807150c0b1501030c140d0e0309060a0e13060612020a02151303140a0903030305063609010c1233 65
    0x44482000012400f00c801e6180051014130380c0025400580d03030719890403c0101c0b02c1e030720201e84091003540c07000b50060303921004850400d002da004401036400c1a54100110241000c0c90f4007581c0103889003024507080081c00303209451040d64040400c000c1e07030520311100b101c5647c9600024a084900c40c1d40d480841c040516227683c5401022803c1c292890f000d8841d0b0076044444403d4450107400e207481c41e945038035031100498240240d0f05c25060003851203440340901a0080c100c00c07102403501c0d101e50040003104800c46080c0c8586026103056548140c0c500c3c038101e083c41c000394008140c9030306501c00c038a40381300001c50f10031020340710760744103960b00b0324450940c036000c2d1141e0558000308031704001c06d00c0360201c401e80c003007c400d0480e034052401140e11345841e40800d9002e0b416198151034408444401c0000003141c0c80203030b41644680701a01050783d584040b840c22500c1e0415050001401c20000d980b081941da00f20f12420601054800f000005045103c0d01c858803248550017812540c1600300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 993088111 1250 993086861 993086867
    0x403110d030203150603130b090d03320a0f110705010b04050403050306011d090c09030708030f090f0301020903151807121704030501020d0f0641041b 66
    0x2914180c2142400d60860038403c222503ca110000e00c0180180f801000003202c500605800030501600b00c0012661401d10701102600c480c40500e13040c020034200a803454060401d944807074840c03900c51034140c800811a604049400001411030340704184c541c001d0007440001c510600c5884481390304501c0d41d469882c5400750942c1c1084442c0e5105915000401c4013203600901145e9007c042407130b10260460000741e189000744c0801803580c1d04038014101b0440400c050398004c01c01448114100c852040e0754201e4160b0700d00c01c01390010304003102400f60350454240714000c0f50b0030020040c0054240080040420f1400310f840345000e1844216200b4031901144200101820644d00c1c8007a115290401a4018141c2c1c51001c00410759584c1c15a00c040740d40c0d00e02c01390303405560701c440299030354209600d50a024000131070044010902e001c100080010031aa1344280141400d40002611074245007480038514000d8003071401122503c100803507a50b102d11480507010403a951003180f81456150003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 993089361 1250 993088111 993088123
    0x210912030a0e121903031d010e030309161a071a0f0406110412080706090b090102071106092211070602040312021501031e080c060a05060105090f1314040311 69
    0x30029541010342003000c03408441c60f0030349186403d1b040105940c80e500c0740a880c8038011480b00b0801d5440d1102d19008a003022000354040ca402c04202d6004210589840702c0841c0b40d403140d040920000d4041c004400c5102014000c0c0c02c3c02107000320442c41a9126600d030600007260b600c1c880c4524081000b042260703031301c00c0d00d10321070000342a9800d0600b05048c0c2000c48200c50b1011380481d00125885c0c0030403400c0e410000c0900d40c0090a02480e0900c610703000d010f500100012030b00c1090107441c00000c1e05002055078441c110042108002d07458400b0320850740b600401d1311001554640000150300d140080c0108006032185400695662850030080e0010080250304411074100d1002000c0582a020680b810f481d0482c64480c1801981c1c90b00b03540d08500a0b00c01040a0b40c04900701c070764100d010415600c2000620400e000a6640800440300c5104540d070080d441082880741000a05100307070b0303101d034041001c41c000656902e4294212400caa044404400044460740c000002010074440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 993090611 1250 993089361 993089389
    0x803070507122109050304090e0312070e0901090c021c020f01050114010903201c030e030c010807030b01020c030709020406090b0304020a031103030d09110f03210912030a0e 76
    0x455607a00d18106000d88110b9075008401c0544844c142001e01009004560007001c010b141005900c1c3c0c080800e41e10794204210030203002e05950700080400d402041402012a001000d000c0b440c4c0c24035180d4801170000320600300462040c3e402c6581031346842c0c040d441d0007054035001060000c3c421400030b425244142c0003902400c1c1c0ca0943da50051341c10080740400d4036406000064208920020700241100c0448400d41c858098040e24403142507510108862500171364800340050003c00a0503030700c001f03101190f40003c0740d502c002645a4400d510500c05044148141c0340d03421304e5031000900e80560381d08000407036940001e0130000d080c0c00160b03000c020700380559005d00758586500010a040e030148005810001060070450039a0307410f10031220000b50000c4c0c10800854542000300b49115495a01070107100b12034402e0383c40d0b02d40010503500e0a0268103440ea203610003160042c2c0f150b0003502800e500480051301c024140541800900405c030503c1c3e648000c440d06200800c1250307184060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 993091861 1250 993090611 993090617
    0xe1b0d152309041403120f341805060c15010f12120306090e06090c06120604230916060f0813020a0b04121202010b0a14010c080307050712 61
    0x4071254494442e075850a0b400b6400000e8040c4c11440c2a0b00300d41184502018149000b510408000c05000120405030003402803080c05901d0506200340d114581070313411215102c5543d2242111500d078400e0001c03810104101c1c3c17840303440136a50000300d413154200d0000076005402c640e05584c070f001254110907004001c403280c0d56014900c0d01c008081031456804014040480700d030780d00c5100600a4102c0001480b411004000300903948200d192140d10580c0c001109014503a012407a901d820025904100ba41c44641c0b0026200e40c01048000c2c039031440e194400100010040844d104042d00b014481d4802c103010b00507044207404040082400ca030020b105200b500c44035005c00c0f076031201016520991031f001c0c0d0780d1015a00d00000d80362442c3e03540012401580028080f405008000d6404045e5100f1808200d5105002c0c00c00da090381c250004240d00108441010021480321010300040c605060401800800098440c076506620443d10310000c51000280c010400c04800000004180c080c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 993093111 1250 993091861 993091919
    0x2100204050f0d240b1f0f03020a0203132d050a0e1504141605040605030a0e070306060b0d0531060906020a09050f190504020a051b06010608100e1b0d15 67
    0x2240140c26a45841d4501c000c043e404100ad02665001b0412901e229804040f8424082d9a0380c071190490754180c0b201d14401400000d002104000d60003c103000e85000038441840c1a08050042a0303d1100520a0038003404440e0000d80b29192403085810001910401000714034100f6280d00f41c107003841c8481e82c2007140400c07082017010340c410150781d04468405004100c692607009990300c1c00b03020707800180482d480c001c000101d400b0102c0003030001541c502c405026699910018000e411904211300702d021880242d2284015050420905140c0c82010005481c8002d52560000c0780c00c00560300000c200c0c03910060000d4581003c42d058510011901d45408814000240704181100d108103409650003250386840b950160b41a100700e11903a007008404280d013400850794070f950a00c2010301184400002c03a101c2e4048560807c107440c001e03507880540f034070780301c0c4000d120300615440740c0c0c0c200c041401680d0030f4003154001c8185a82c1220404c01034141000f4290307000c9520300403100100c20320745c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 993094361 1250 993093111 993093169
    0x8120708060d1e0c0f090b010c231009080a08182e0f021803030406020d05250308090111180d0602040b04060f02100204050f0d240b 58
    0xb848980b02c2c552009451042c0c0c1856032000d02a1561503400804200713500101144416030080344c4401c0703c1500100f80b00369990207006440c0c0d5842e44c2400351050340c0c002e40010b2642d054031030790b221520b0030b8011074031507060901410341100c12128044800ca0310000344e00601e41e61129041e80c003d0718031440000307080810000a039071400c4846c1d01d03850369100c02104180c0b4401c90110199481c02c1c030442423001c25030b51000c45000f07500490134241d0070189c0d4a101e4005080000a94064070002e40041180c64080c80003680e594000b840c0000d40810341c000c8080e415a070300c0c520800307194400d03118041d0a0502c50302c0075007510118100301e00550f03002e10009600000320801880001c00c2a11104428804c80c00d0540113403140380c1100502041c00500082c0082c0e00c005115800150b990a407008001e5146400b0b05905c5148150366020040381c02c200001d113066007900381d5807403107410010b00c0e0650000c00ba181d141e0220070000c82da2551084046510708005460741a02d141e0003510b8201d4403a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 993095611 1250 993094361 993094369
    0xc020610141306080a0609170c0d0509030115030317071b080c0c0307120c050904150f060e07020c1f0503010608040302070515030106120e03031305190812070806 71
    0x41c1c80c0701603100b507100881030040c480c0d203540a00042d00440d801e50f8060b020794104600900308011084481c01401c07600045902010000c1c0d0b41c3d080f94220103000d8199030f40364210b80680103000410f905569941e4602d8450410b0443c0c2001184a42c4030b1818140c112000300c003490200502c000140a0f41122400c10164000d01036a203050b03103c000507403640941c4100500e410781e21180b894040c03052000124118201551151007244500c900c0c5c080f50781c40f0b1b010b10101c00004c2d5401011541904a1804100d44a4002c100d090fa07190200041c074603580e03681a1505001070b200c68001d43c00c0452f2a2600f400c0a14200f2103c0f050540110007010344044010010f100500ca140d040004500118042510900230600140002031110141015076141c025003948203200361000b0600141c8480c0820a180c010106d42809030b10140d401d541d0b800780301c0c105241101c1030844940c0240503440260850180b10340c24503d0080c0d21040d02c40c28000c2045540c0c1e00c01409581c1802424010003005a603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 993096861 1250 993095611 993095639
    0x613110a05101115040503030907120b0f150a14130209090f0403050c070e1519170f060901020a030c020a08090d0c09140603160602100509031b010c020610 68
    0x546850300c00540c0701d00650042c24a0280e22130b8216030b031454000d220038000000b000c0c41c0102d04550990301e400d0f0369140140450210700c9401440c444000d0009845201080e000580c4100c07041c01884010481100190200119801c5801c0c001c40200c0032848500b00400300d07031302c1440001011458500582c0010340303244002842503403240d07031120004041500c14000d98000c10201d038102c5002c1a110440b1500e0103004075145405521844245e0b00305291183e1031003521035a00f8402c45205040c103080c21201c0e50752140118040c810b140040b8180344e800c001980c45941c1c2000016100c200b50341c0001c06403101c001d640310441d4010070500002c100080c00711034080d14111407441e0400c4042c507100408008541c0b0441e0b08130702e003480841d409020346d210644103460450588800c0003411224032208059406128010782c0003078051090114a07071b00c06a00407000c1400c482c1847c240c4407860b14112101107003040183d4556078860700b4260100102c4d80c02a0915018065440c28410110502c00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 993098111 1250 993096861 993096889
    0x1614030d02060406020c011e09060c3b0a060207081c051602150f03191b0302071515150509060d1d1009050c0609300613110a05 56
    0x1380d8005064044881c09505c0343c4064003c0c056401660700072001c05400034143d940e0260741b2241400e030414100b900c100000c4a45c075440340e440d2403030b5000c441c202c915110000702c0300c28015081070030800c0c038981c0c070710314040c00401c05070b0300800303513075040c005014104041d106c1e035000c0d80003200d84010b520700c0d048025561004140e6464420030401d0707000150f44810000d9910403282c1c40041c2e65600f0b01d800c100207520504000716801c0110308110045811520703c80c0380550046800301031405090701c00e400910301c2c18041c0f80790517042c03144100140b04503407210680c6460040101d40801c040d060b560b000d922421990305000307050051840101700c8034420790240b010942da495409180715903108002c071021144100c01c0381c00c80c1d41000003c40082c04202000d540512694103c2d0040f49403590855500c40c9029000c0c04000b1903500d00d02042004103a03902e0b1311400340b070540070113998040203190b214814490340c1c0088101d150038407101c40b000f82d0789614042d9030391460074411a15280e034206111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 993099361 1250 993098111 993098123
    0x230c1b061612090e010306291509040e010507030603120906170a021b0c131a0603090a0f05062e050907091e1a1305211614030d020604 59
    0xa003003841d0089503d4411500034480740c130300038000401401007a90100c80040d1424820100c0d0010304844c0288607007054284070f81c0060f1450740c054480751a030300580500070002d00046011a407491156094034411140440040e68031700c030400038040ca010040101f2401801e091281d6814003400400125462030441c48040070784000c40d07240c00117517041307504040c0302d109901404c848100c031042c0c40d9011102510f2182e4079088000400801038445d691403004088031403d0740c9400c0700c05021150b040108a035000d4058404240c010a10780710302124000c1c8620050070740b030318000d40c480c422000f001c00461040d110000c0c003894011199000c2030165101100d43c081d80d43d58181003128a0001a08146403860031240a143c1280007080080c06031582200184107040e410b0090b40000d020704038040c0710440d50803008100a0420017004c55100c81c003900181080624080e04900c0d01e0090300c85c814421074030718020081007405642002d480141100505031803401030710003e59a2030060009481 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 993100611 1250 993099361 993099383
    0x9030405011b05011505030709020a0e0906010e0a0303020303070318050a060e0f070b030f010b09090a0b060f0a05030412081608061c0b01090e07060f230c1b0616 71
    0x38400391214050301841e80007000340880b0b84c80c0c40c0c1c1084170441e94441d1038064401c0d41c0c8007082410441c000d96907040056920403d2507a810320412000d044c015290f1414441d000b8869452512060501c40c00b9500a030021640c03810054002000c81c0c000100a038030802001d0400d1001031030220381e944400e42c20400c041803410040d848a4101090700340c41c040725120b4003400081813003c0102861103006c1311944154183e030399001c007002030b00c10f07c41d880c0c0d0f0001192000a210740760780d81c40040020701c05003005092941d884074442c0c2e241d0108480c0e0004c01c5020080200b0030400340100c1c0b000051601d060446420300c054443c1700c19039111180c20a00c030340c240001c2c819481d02c50009607d61091600c0ca0201005410b09420b00c12081c0282c0c056941010401c1040c0d0200007031542c101c41c81503460003c807000404045036101c40f00c15002450030300030b0040080c0030500501404840d506030010b0182c01c08600481c00e011092048064041c402c240300e5038592840781d90b14141090717002140500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 993101861 1250 993100611 993100637
    0x110d120504170c150a0c0c021908100621020319020f06121603060e010303030e1e010614030a080f07020d0b0702031e0306100f020a080408240903040501 67
    0x26860b1080b00300101e82c240116508400c10f8001821140100c030380c840303810903901c8144500c03042d20b1400d400d10000c601425120001070a101044000d0f0500d00c2c0c400e80c07042a04c0300e040718100b4202034104104940c44d01c10a10050600704200107004000f0605d05ca6254420703070101c1d447e141c410301400c402040c076030501e505540302c4191202145034010f2846948100240c0d8494444d002510890209001d600c903100000b0b000b885410291203403040940c481d80c2c0707150380480260000b40484141800703006045107000d05001c0d616206000c0000022a0181c100750300003182e201c0001105d0300c030760700081c903190200e1111400c40f20b035000002a0315030b8565060000c1040d480c2109402001c896480d400c1000c8142d001c0042c007007030310b401001c0002d0030a0380c541d4600d00340001c1d10800d0f40048401e058540841c0903940303800c10302885005a5008694503115584260055401041c190b00024040c0c2c081030781c010081904181882e07071186890034400300980d0789026034000d0605006071821200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 993103111 1250 993101861 993101873
    0x30a02040b030a06291c02040e07080403020d02010b06090d050c06030a020403060b0405040b13060e030f0c07090e0a110307030204110c0c0126041a010b0406110d120504 74
    0xa01a01c1000851696400c3c0018140c0080040348507162008406001a0590100071404007094603a0f441565080c40007200c0d500644850b107000040c0c280c0d500300000154154421502445210141c41e6060359241500700030741406218001030301103914010082c85640c1c0c401081e03034440e803010740306c0810700c0e401450018944607424170307030682c410004410410408042e40090045da44150024480c01c0041c100b40026204190303402805115003800082c1d001d100c040c1c0b03050001c1d01581c0d0110342809d01041d400c0c1598004071100010403400079020511070000c02a00c4001c0508050820081c0140302c0e8003515048004c3d1700401c440340e50130301e000d0f15580400c444005560014010803100304045484a466030254180c1c0040340503a81c4103d995602680c0b0100000d0b41079016503000c0601c0c000d031711148140c000e0007110101e00c4032402e40380d90440424000d000c1d1002038038580e03445062010103000c6d401078a0880c90207900c00c00720000300781d501c904031a010007003980002c1415100d514280c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 993104361 1250 993103111 993103117
    0x80a1707080c100b040c120917161a160f03020d0c17070903150c05070b0403090302030f0303100b0c010b03010f050a0612050c0603182e14060105030a02 67
    0x6003000714080342e2100854404600c2d460141480301d410000c141ca0a002e00c000d55004c205014041182c0f04486801459650000920ba40c4100301c2d15841d450038405428050f0081c0b003015500e9481221084c08100d5603d01414480001840d02522440d007582011100c00c00e50010908201a580958004500079010784c0c01542c03003143c0a005108031400300030308039001d1100c249a1a0161804501d109001d0b1850b901a20b80103182910b0b0b40c00c804c803045019110500c695010410104110310220f11149003440c01a4440e5698455092860041500e40f41c1c1c415030b4510350781c1080080c05155000444200100c8405092190711005c1c45480d03035006250340340d0466010350a00c140940220041c2d0300c06445986501400c202d220307101c41000c0c0d40e103150800e0007002c0e90b02080707440205251030409594469130078000c80300324070150441c1a04045000301aa41c603441c00300150748520240d0030f20b103007103800424020000364800410242030170002030302e80c80c1401400004a243c00c03e81d071b011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 993105611 1250 993104361 993104363
    0x100e190c120c0507121701270501120605090708030703080423010504060c050a090b0d02040f091b0806280503030c060108070b070b0103060f151d0a06080a1707 70
    0x10030080c10142c00b10150065008840032111106010707510404e41d8001d10078000132032011a13010055a00300020030010001d02c0e0000011500448500c0714208900d016950181c65401d00e250070012007898006d0580c0c001408114580d000050306006032000002583c0c042605132420368015210350801d86125100d00c0310742c580d8181e02d03031120030030f11005401c00f6000303070f124807020010103080010403038181c01191109400038008200c10030103100b03d00040d02c0a010400e90040c0703030aa94901001c1100074603401071482130780300d00f9550720b4900400804100012107041c101c26034078280c400074801c0b030f4040141c0060105080302c0d070b652840b0701ea607403103010301b001034100c07a5503410044040783d90313a00910481c034007441808800f01e505002034007580d2155521158480c1e5036400e641d1000080c09001d0600c9030f580e9560091a12100d1484001c01c0c01003850040d229104d08014618040144d0b00030800c61800f41410410400c4034000142104181d40241c0303d58114030303a00d81107515501c10741034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 993106861 1250 993105611 993105647
    0x20310030b010e0420030a03030f060e24010504030f020402030a09050102030c070c120c1505070204141906080d0e0402120703060e07080403050a08091014100e190c 72
    0x4000b040301c0301c0c0512218041e80c041c06111400254034000703240243e00391783c0419010380092040c4c2c800280a0780110000e183c6411001c81c406894a100c071242034002c07241c00d0000c42d02071400c0d948820412401c1071907a0003e1030000d2900e070454865021008800340c00034090356000000403c00c03c0c5a0348203041c100d601100a56482c14169801c460940282c0c0003074464801c400000945e075041700280c680310503480503e8018540c90311046400c4c030125900c500c07040c030074100140740044c4e03960f1103019001044250305095a041001102c170001b0781c0d1144540840c1d18220050101d070740c002440d500d004072949018240c241440c8007140180c0120380010755488441c4042c00a029019000035007940c0b42d5001c030034410707030f01c03220200c0f0000310542d0060040381080040c1e2032460320030290140c3c0506d446c4212440c10080180c1d90003240c00040003040c251f5580c405001000000707441140041118a055441a04000803e0280d10820a8020f20441d07941c20812021038040c0c5185c1800c0b52030380c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 993108111 1250 993106861 993106883
    0x30206250c0f0503012c0a050d1805041e050c0f0d02040312021b0906060f070302010506030c0a0f05100c080d1a09070c020906150c100e0d0f0302031003 67
    0x460510081d5085000e6949040ca02440100c1c90342030501c2504005101010040100c1c164074240344158046080b00c441300c0e014170050903021078410014000c0c052041d43d107034064107202a14440b030481145c0c0105114504110300300b032040741a04000f01c0b8101da40703400000c4603196601c440410f4070500c1000707000d9071404500f5510561030b581c06402205d0080034a080505030420040362500c0c0c29030146854100e080000041c2810300000321940604050040c519202007002103004c01d401c402c0040b00181e44a000300441d5041c00d018204a43d6002d07540340750007609200c0c400340218410300540b4001c90105d100c0d41c644031311402a2649017900114540e503110744030720151025141400081d190303082d1004d00641c080c00c140c144107109120a82d102000512564200f0501c3c040c0a08407541c000304810300e400c40c0340c40c91342c01400450020380003004051401c03e41301d42600d20f0000728108642000103440041074021180b4180c0d03003910f160040e40c1e0360f01d501c0000501681508042c14402d0385d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 993109361 1250 993108111 993108113
    0x70503071805101206140d060510170a03033b011b020303090c0105030f0402060a030b120d090504151701060305121b010b1332010608010b031003020625 67
    0x43d039105502139104400344a07080c2c076036030f000d40794622862180d0b401c800000c0c0074201140c0140d0102c0d07000b0207075000d41d018007030f42c9441048000f003078002982115042400300d0707810507825114010381828403500c0040d2004140c4505103246200c604c92201c4540f450040c900381040c20752111011807502c0515024088083d01d000795a50003c903004070a91281c000001002d43c065000e0f640309001e003080e511310a03a155800d1203040e801c02403014090540310503030340d6141d64590022060080f40c0c60010403000c0c03ca041d004140d51265407140780179504e03049004506100404815003561070168100c0400078800307100c1c5004103180e502c040c1090080300c146040c2a61545e0040c008000f445040594004401c2e491301c3c02c0782d01003032459500c103040450a0a0b106241c0d000901c058628080e9a0a00c3c1c072141084c5406507006e404012401655a0060051079002581ca5000d014540b050a003186000c06070020111201d001c0030b441140040340d00c00c0c004094203103640070400c1000e12044003c45c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 993110611 1250 993109361 993109367
    0x30207170c0f0d11030a1b0c0e1603090b0a0506220f0c02030a0804120c0b0c071a0912160816021c081606020c240f07050307180510 58
    0x103145240b81c0c2070b020341c0d000142e1151040c0c0c8100c42d00103800c0040c529002c080c12041d2070181c000035910203108800c9603180c01003148503c07410020074900074000162b180c15040b55041c842d00e1a1107030241340c1340c00c400f0300c0414841101a60300201c038110000386a11828006115205190607208033307010240d80c40c16a003803030b64014404404003100b050202d50b00c02541a030326801000e1008001554440000b000329090a540358030303120b604c1c00c2c5105200d005440704004c400040745e40ba1101440001c139034041045e0480801040c0d154a01144071030300348001c0c0580c5806034001411200d07000403564000d01d244204d6880041688604031079503d80040f0800301c40c0300740c0518180e11440008211850310840c200c4407502240e48603ca0500e000b60584900f281c008000300e007659202da0a00c00d128102508102c01c18103a0418098003855170010b00c0300100100004001c0c1c4000089030007480340c15604079058a411034820b0401101d814000c8024106600707a40d4401a4450300c003218004201d60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 993111861 1250 993110611 993110623
    0x202b1b020f010b0a0803191202160515010f060f0e091e0f070509061309090c290405010806010e150a2019140607030204090b0a05090601030207170c 65
    0x10749040244075400000b400c0061440061160084682041101200c202d003081380451000354107040800a04054940c0b100c1240c0108101441004600240a042c00010442e40d080c04007400710303507030003581001c8907460941401d100d001c0903c5a00b00225401502400c0140001c1c2d801500004041c03601c0c000100a00c0000030000f040d1000c03940102d42c029241030140b0b0b03c603600c181c5995162181d48801d0001d03940c0000072807005060314000220301c00004e802030050340341c0510112401241412008465400200c1e10744080000d001c2c00c41c813918080005076002c4a01c00d00b0240701965036200140c80c0841804d801035803065003011007201c3c000084024100d600e00542e58114160f020190361405441420781c0c21040760b000c00228455091000021101c07144600c141c00e50038050380300e50324900b50040d141c1201182d000308050161040600c1180e40b140c90441e0030311070f0a40f8040115002150240100c0c1c101754002074440e05100c0301106100700b4102581c5201c0d0ba50800501d0070351981 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 993113111 1250 993111861 993111883
    0x40f06020d05010e0702010b06180a17060609070e01081519060914010305060f150d06060f0f03090f0b060409020a0b0a11060702060c18060d202b1b02 66
    0x4028070085440c40380b05108e40e0381a18000340845152149880200000b401c2d10401c0310750058500c000400c0c42924600c01e24444060f040090450303060400400c1a80d0718024034880c10848030740c200400d5682d001a0b815080b5202d202c0b6181501000f2000c01c7c49421004040c540402c4407079000500d00b540700e4001e00c00c0302c0150715030800841410004405541d03068544990010341b01e1104100c6180981030f01e05081c0c0380a03811413610600d03a1144058911513444803021440071880c3e1211a504440b007040104158942040442442c0d542c896500d5140c917400ba00d1102404001991a1500c3d401412031540040a00d000c131503452401040c90360017510301400280b183d10307a108055800098003030140d031481d0060103c590311040020030940211041070035003000142c5140e440c0c0c440074014101e0f840625000b0441c003401c0d180b604040c0580803000142880700f0003600c02c0c4207081c41a14030500113100c1e1100301c1410800341c000082c0007018400300c00c0402940611401a4001800e0000c0b4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 993114361 1250 993113111 993113129
    0x30e011404030b06090c090307030606050102070902030915190f0603060f060501080403050c0a06050112020118080307061e020a05070c0e04080702041d120403060612030f08040f06020d0501 83
    0x18880903041001140180d00c001001d48510002081c1c2524184920a5000e18948821307420038035003030006460314120398016600d040d07549400344801d50b810b0180c000a80710000c5c09601e1030030020900c560301c422419101d03e58840341c40c00b08100e06501880d00c0f03001040064180091000301c180075001b00300b0f41c4412200d40d4900141030a1400c000d004000450f00142c4038881d041c0c0e02c0da00c00355019030024140c1c03081401103a41c003900041d01445950301a0046695045800103144000741c031007038010404140d0112000e07801c200c107100001c200c0d4041c0f5030008001c00c0c00d1240058040003648144d0300385031294004150b055610398003502500601d4002c0343c41007880d50b91298a0031819406a030050540c00d000c00440d405424241c21004810000c2a0301983c407510b6184100d0030005684104505100c0c002000c10134030400e405260064402044000b9140c03c6555003c1c10046c012a080010321000c1c10000301440302c641c43c1c01e2081608001c1c25950b0700c001910090040809000705004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 993115611 1250 993114361 993114377
    0x5090c0406080105041a0112020d0c0908010e06160e0d0503041205100b0105040b0c031201063605010311040f1e15141c0f0b04180507061407050307030e01 68
    0x100d2a060003051b10b4051103101800820401c03400464a61001ea0300034025180c080142c140c0342c0d24984a8a01160080d0791040e0400f030600d1129030035111104110b2025601c52800c1c44030328480c500210303421240e28100600c03981a0080400c81c1200403400190042c000460300003900b0100201408165200340d040e1040e41414a14440c2240c003107004642c00141e0a01040c85104072110003060031491032421a4240b40c110701800e8030313540b4241c00c241e0001c2e0000c01940020002980755001200040c45800303054140d130f094100c60030584d4410711341015141d03000044103005005c01c44001d45400d10700d00d4503441d116015464507070b07005644c40865403903546000501e4521107145a40150041c2c0c0d4215106c645407075481c1702c41d00642c16040c02145141d01d180840000b9100b801d40c5c5008103500410140c420030304000c1103800d60200400a150240d0320103002400203c2d0081c2512028201800c01d0401c6821030001d40c0280c0d07070028a02e2100003400c3d01816000300254040ba082641d85c200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 993116861 1250 993115611 993115619
    0xb030f0105100b040b0f09041e1d03041a0706090b07020a0309060314040f03030b0418020a06020c060a0c0f021203120106140a051606060b0310050405040b0a090c05090c04060801 78
    0x912845c481c80304000c6040c40079039840c100b0080184a1040000c10100c0d00802041c120880d40c2403480381d015055648078510780c940300300300c0e09804036000110080c5080c1071600d540350310001005460b0040d0342c40001100d10410610f540451304142c0c005c000e0500e58030f0000d10103951415009400d60125585420000750907201e406040200320800c04800031a8807159500c000c80d00500700c0842c10716884d540c0800d42a25241f250403000d100d5601c007001085198014000c040d9400d8101004541001402809980b102d00880782c0002c05c1e444d15403261070a5003080b03c1c00f030030f4002c0001c0d40110583c0c1c004030407050010281001100882c18800143daa405d0141c404d03900c0190388130b0a07000c2c14440b41d6011400751010700300001050041528040c899a1070108070f0f03105411401c94040c000c01804009409130141c1400740109031800c2005041c541c940d42800c06005104500103900c5410103030030002200c412600a0002030b0075030215003842c814a8a07507030424000c80c00020140c1d00002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 993118111 1250 993116861 993116879
    0x120111031b0a1b240c14040e13050c0301110901080f01181109121f1505060d0f0f060503010e1c0509061c060f06110c040209040b030f010510 62
    0x507000c4055a1070f9079000ca85400b841005600c1500c00981e400710362020501e08003a136034054a40c480e0000e9100143c9090401d070080c10501c01c1c3c0802c90300107a41404180189030042000d05e4120078185162144a40755103085031802207848900f5800d07500303045a10003240f55042c00b0380036441c070036258485a036071000c0788100b0440003449000c209001035000309150968a0740a01d1034904801e18480c548129007002c900c1180002d55191103d900603541c0c00c00700c107882448180544600b21040c4803206840f114105203600d54007030726214a42c00100c00e0b401603202d5000009501842c041801001d02c032440100082c001032003024001e50a10b6822215240d000c1482c440d240b1003180c41030086400060304907181d4000e20700c0c060308000100170322080000120126030034013030020303c045544e41c02c0040301e034050000c9a1200701401001b0108100004000c40e1000100c4025a0016100c17114480010f0180101024941c3c060082c2e401a2038162010f40150f0703c98802c055481c00343c3c665403003100d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 993119361 1250 993118111 993118117
    0x8040306060504180311070302032b08070509040f0b030d0309140c090a020a02150a020703030c03021c0f06170c040506011707080702030732010b010203040e06120111031b 75
    0x31150541c40103d02c00002400303540c03c4240b1b0140c1c0c50444440a440b40e020034074161545040c044918103000d03101c0080e0035140000300310313100c81e860a00003900340b0394000b600718085c0c4100c95110317548900202023038032641c1d480100005002000c580384130418280142c000c0004142c140c0c1c80c4884400d0720054500700013840302e88200040c061800560b143c2403908001e4001003600411806043c13030403c407964603180700c1801045c0c107400050b40c541452030302500b1a568a030b0f80100341030040c080300d50450b503940040c200143c2c001e07001150326000181444028600c42d08018902150b03528455260780d0001181c0701040d8080c1c6080201d51150300040d2102c3c0204c42c00803214004800c0010001131080e001036801c01c99030b004407424100365654801041101c03041440344030b034510260207204688650814904032031540200a00e40c12a80002d440703114038005d005002d16507001083d0581c0710852038404159060000b0094200c42840c1201ca41c1c2c0f042d01d00240380004e050f94881d1401003c011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 993120611 1250 993119361 993119381
    0x72109060315090903020f0601050109060c0308190f0618050411060a1b0f060c080c04090b0111030c030702210d2109030206010503070e01080303060f061608040306060504 75
    0xa901986480c121084002d08600200d50050400c681c42c00200080203001c2e81e034419110b900604130042805031514074150f41644024100110004104010f64005030300d01c20144c2c151030400342c1552002032000c140742c5c505080f10780e07152034907419840b81c0c2901c0e40702038150340034041803844500b80780006105450041d540a899200700b1a150030f010b150884c0140645129030429400451840e400c0042074a414401601c580d444941e5400c1040046d00c2804459a05d6040010050070045d001080f00c2c0514050f0031001981c4482d54070081e0300942816440c1d05c0a0001c9940e0349092030310301a2290800c1c0c0c4100c0c006d20140ba014101210215008022008403d005015014050300c0071251404002100c01030384c06020611070f1003914500400310041c2c002e800a01c0b072545400c062600c0c0243c546d22040c0c140303801c03070010301c011180030086a4110700c044941c005112084000a5a00d10401c0400c0c114260285036140030424800c000d4070480740070f05010402c1591b0341d030a010554080240f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 993121861 1250 993120611 993120617
    0x80402040504140a0c0f302402130b1e0c011808040801200f0307031d06010609090903020613021c050d0e060f09042a020a020310020412030503070302130603020721 72
    0x83d0700c40a46801100d480009008840c144d824001c5802502083c01c3c0d0b45200f4103690303400188ac6400001c003150058000d04000380c0281c40c1c564090300c0c0b1f00101c01c2950300003485000c0040d5024548600b50000b03156044048903075078074405c00c0c0c60041501d40c000e00c03030780c02503500302085099103c1c030000041002c02d0280c800c1038030303111070071044070a103520080030101410307a100100140304140c6040460303d000c5010061078507504201d4050310f061031503480514040c0c00c02d118000069804511340307070000d03075102d001c40520a00d072000805003021046041c442c000000520030070f004002841401c000381035140c9505040300716051140d00d01c11010340c0010742c8010803507050642056030049400c900c0103481500449481307413429109080c04070b04000160300a507442001d40c9000c2c000002d16024500d000c6141500c0c2440070800c41c2150f42018040c050080002402c0d036000390100c2c3c4000100600f01c086068840d0303000f4009410a0030141c44400d5041e0059201a51421007034216918680b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 993123111 1250 993121861 993121919
    0x212060415080d0503040302010612230313030206072d0606050a060503070815060c0703030224010303050c03070609030c05060601023415030624080402040504140a0c0f 74
    0xd42c244c5140d440508100c00b1596107660000d522048040c071161003500ca07400d03064840f118090140c0340f400d80e040c40045240c108001c955050341340d05800703108880d03064540d05d44031780c81760920001e032805003100c0f1204022405110b070a005030700ca008c001c07180e10030802041116260028002010313068007400340400c10810104080354020603000307034003000240c009208050786402040094200090010701903000c04400e004140d01404948108a01200703140ba030444100b00b0750903071000c18031004d000e01c400017904818584091040780c0b10503030030600c01e111407161490001c0c2420107644060742c042c0210004114190710120f001e420b40c0c10f0700700c0140208817104405840c0d620f442407000951000540002a98154034000c20702c952403541c5002940a240c100c05048116a800010341042c0c440041d40594a8200c0c11058219806803000562680c2c0c2e46441c00d4401c00c0f1201c4070041e4403c0c0b607081e000308010021100d0980d078210007080080c0b5038a02a03011660350200020515000003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 993124361 1250 993123111 993123133
    0x2112160201030e0f12031608060d0303230c030f010b031303030e030705150f07170c1804020319150303020c09101d041205040302030c12070504021206041508 69
    0xf0b800c2265041e80010030394003240c041450300f074a84100b003c19111004000b10800611000024a84c0c0e0b4081c071504018403140342c11800a465661880ea0040038103903a11400220740384107100045c4403000c40d000c0c031490350909903c0881c00350011a9901c4144000000104100000314107880c0101e0301410a00c0c2451020390f4190050040e8034a511810b03c0144800710110b02c041000320404880100100702e1404d16110401443c40010404828007031001400c0c44456903500c10140d10412510145444200480781b09400034140b030728003030b8800d002005015186c0401d1b4841d407990640c40706c08011103003a92501140c03c400500c009030160300090b148500c82d040c001c210b2640a01645401030f8400c0c0c4481c0e0020100c0c41400b1401c440304c91b0340341000104089813601d40e40c0b000442c2403040c1018034550000b81d40d0f10009000601440c50680d00c603a141303400b0002e0340c018180042044d51078009440700307034011910485089200724240040c0e06503140b0a0f2210030140c41c0000c016080c22481 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 993125611 1250 993124361 993124367
    0x80601062a08090d02120d05070b0726150d06020a0810270b03060426190e041b030c090e010608061203040503120a020d08010f060e030c2112160201 65
    0x80e2650a07038010441d11b0321044c03c8002402089200d168a4a6a42d11146207082c168020714004190609001d251030281415840078420380602c0d80c1c4003c1c2c0143c090381c1d59001440c032072600c031519541060721805603030b040080b9038010300b04121031580c5c6d03480b40742d51701c00b19a20340c03141501ca211000040c01808400140d000c0b48160350b6030f065110045520785c6e203480401c0c6010000c030fa081c2c910044011101940781c90303154a40301c800307903484078141c10030249132840c90351401c0c07520403103091012b10120344040d511550008404040141034a18030a801000f02a0282110003010b000081d45841d01160011014000c43d045e00c0e460f58404880e5a122028000d500f10300d1402d603401031100b0b100c0041c481d9800c01143d092009283c2501e40c5403449540007914000b254000c407400c0c00030140050080d5000c0200100460b034952804440c001414000700341088030140c0c0303503a00701c0c1c0150b84482d40c02411458418030822108102d6043d160b4081a100c1c1c94000c040c00c040f000200084050301541c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 993126861 1250 993125611 993125629
    0xc010c08190c0b040b18150601030b0f030105100f09090f0f0f0b0112110d1a060406090e0f0d0519050702040e01020319150825080601062a0809 63
    0x6061951405102d511441d205650443d0110340e24070000c0108828a0880f80340d01000e07620100040003024070545000448802c02041a410140e40304d81e22241382e600d28041e01c40c40701c80540200704038201840e52100c811051300450300b1784a545140003801c2c060034454050142c0e005040880705052559810a0451ba00c480c2a01d40c00c08514040c0d010564440780180204814891000d000005140040781600c590880500c1000c0308862800441c5001d40b88003494040000400d02c5a6104400540240740540059415501c0d1001c426100c07a0300052030680302b43d025003141c083c080c2c4690125180d2141404610090360409401c0740406d02a00c05481124402840850620f0806c1c3c2c0711401c98008031518040702540002186080d40c40784900c40e181001011324000d480d06040e103050b41d0317411000c004d13240074105103907010020924180120140104074250751a55a42d401d009020366401000141f02d40440c943c89101080c8000761a074056038040c03605800c0401c20010055056 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 993128111 1250 993126861 993126907
    0x9060b150409050a02040321030f0b030d0e043309060614030a0603151a060406050403110324090f010524012a0b061e190503060a0504050c010c08 64
    0xd801b48008000070300b07110704041811410380120410442e4502004044d50040515685a6450200d0107221500c0102c0d10a6504600d1b0910251131545440844d0041203503100102003010b040c4d030400e003071805aa181c0c59410510005024411f61500300140454145210720f1000c1a141d007000f16a01086801031640241000070000e0125a80d0b21414807503207070500c07200c01040d6103040c0c2e0300024140003c08018440151b078a00d050a041030006400345c403a07404054801051280000a41d680c20807217802181c124200758083c001070381c91200005071040d0b420880c1c6004408240c5160241440780c140b2488002501c1c03454020000811100d51400c01300041c10020070b2225a01d050742080c40104480607000114000c240b001c0c1400301c20100301800d0144243c10b41c4040001c104142c0c0c980396814101107070f48540072844040a070400102c02d611aa0f0035004003800c00c0007031007295004074411400340303059840384032084004681c26107417004000c0010f4800e115014004219803407182041d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 993129361 1250 993128111 993128131
    0x70b010b0c0a0b07140712020607030b1021060b07120c05120912060708060a08030301030c0302040203091501061701120312020d0b0303040b0a110307150506060d0c0309060b15040905 80
    0x703e1080350341070314580c0480c6d41590880b816000c00b10090303504001c01c40d070110803460100401c0e80e20700000303100070010751112010892030386480c244a0b81105007030400480c0c5640f00300926503607040f01c005d04d500002c3c0203031281c148903919000b05600070103e503102c403903001c0054079110304400802501c0340c1003c00000c2d04006002d00482c00140c081103598059040e5845403180c0b494040200100303100c81d40c0040b09142c1083c001000050400038082068990480e8007603200e0f80d58481c0b0328503200c94101070881c81c0740203400014240741c10990008205c14039020540c81680c03a00c3c0c1c40d00148000010050000340c2a040701c0540d07602c6507000e0f14140c90017803008202c4070201c0340042e240d5000342d0403400c0240340000d49050099044031a036030038800c514001c0d5044c01d0a5031281400400744e455240001034a03000090305030b41c0d9040031942c1d004004041040040c440d1700c0c5c001c004181c5020200c17041454165200034a1a007440c800251032040715100b03143c075041001e0017000c1c040150440802c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 993130611 1250 993129361 993129377
    0x60e0915070c0203060907081006060915021501060906090b0f030f07030e01061d07032702040609051f08061915030f080a230f0c070f0b070b010b0c0a0b07 68
    0x681e018001a4046c80c2c5ca01d000303041d014202064542825544010401c9184c40c101040092640200c4a90212002182c1210002c40000d4040c0d050070001041030840359190300010540541061005080d15026501c900c001911203000650310721940400c010a0001071001444107840d90200c65401143e915020500510000c1c0003402c0d9945078221800d0b12036a03c000095201d1403915070b66020b1018a001d110314030806010358080c1e02400048001101025900010764803142c004900602541000b08950b2400801c2c04020810940c4007000300660b840c00002c1b0308a00150250061703000b14018030181501c003000f40004c00d546820703034500002c11300c400004030300962111890035011302d42d02d039a9500c001c500105130105041000621220b071880d20100b1405400c159000081c1f0000b0403030703640744030030025494070401c6e90180b02050880400424482150380c003501d01a841016030301040d0343c0b60140c40400c0e01501c0021000c5900220510340480d040e001f500742c10008030300704402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 993131861 1250 993130611 993130613
    0x9080138010e032d1914070315050126030a111c080613050702030f0309160f141e0d0f060c080f090307050d0f090504060806070201060e0915070c 64
    0x41001614494040c68241500744c6130102800d40252118180d004030103001c1c40040107103131001880940304054414070001c3d1414008603020040613002d5500001c0081451903510500c0300944003d0080e025000c3c440344090300e2a003004140700c2c031110440390145050540c8610100c9183d00302841d101114400d101340f6044405051b003180c8103d44041d070300e9461a00d86041032100203a41704c0114070000d4900020002e14130341c08826038105100c1c2036041592a00c90900f6686410040d00c010710080f00300d00400500b40d14007520030800c903040440d550600e0b4400c03030704000c041081998241100455505040010b20b406840c8405442c40ba07501d0840000050f103c0392700316a4148480000b00f04040700f840040d1440e0385800d503000100078000d51500303619581e060b807110706101c1010144118038200c0580c0303d00501c070443c05010b001e00104902559101c0307007550b803441610f2050165103030240100d01c9004a008080c4200d29001c000d0a6060940410700e5100000070800e004204180501d50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 993133111 1250 993131861 993131863
    0x1a090409080904050105030f03041e03021c0302070602032703030c0a030905090a1a0108060f0d08041403030c070e040218040602090a080c0d020409050307080a09080138010e03 77
    0x22406500540d0003a842e44a00d8060100300d80068002d107110354001481c9540d10003001080320161b80d0070300c50114040d110b80c031240c04510f80e1904029403003074203804e28185803200345080a8000d1702035800c594000d40e44034816a05d0348100040d060500d4100d401c00c1050708030840501e240500d000d421070f45001c14074001c00303041540180c3c0c02c40000c0d101503000c02252409080c4141c02c0002c10300200002c00820411001384210030154070b0520800b600040c40544c0d0b00c0c1011b6950800151840056069618080010303030310274001c0c40c0c82190445444281410000250f501c00c1402d44020982207040c0075104940d00da009004a82c000094181c04134145149203e50380030300d1040394050707180c3d8122020000442c0c001c1d08101030540c00300c01099003650b200c01c0b800b0140f680640300042c8005460500d14254410000c010780744400000e03064403650341c040d05200844a400008116540d8444815031045010480c9002e80c0744d14428450f0580d019003450404144050528090754401c240220b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 993134361 1250 993133111 993133121
    0x10c08210c0c1b0607020405130c08010b011206050306180f0a140f120d0207020f04140402190315020c01020d0c0323130b04030c0b0a0b100302070c1a0904 68
    0x480560303000841d40d1602d09600b008440118505181c42c00c01401c1c50340c002c40c02d6030140040191085403140c1c0461a50081e4126030705040740c12410b1404017544822500740a02942407456002400c810790f401c0b1048440d00c03074101600c00c002c0203410b07a030b1500b0a8041d40006521020f44084c01040c00d40346c8166010044062003c0c41a40403509154030398005c80d05001c40c80c043c0080c10340041d58411202c040714811a80720060100d00140c4610990010801c003d100c81c3c5506e801c90305d4900e01c00b22040504008a10a9108540c8608412040d04d2002880040c2d0f10000306440c9c04000341400e00c81c203a4002d07220040c505000141441440014402680c007400c0310318022980c0e0f203040035803039044002c1c42e100000704910701003000c0c00c1c5940e1a114000d10444041e1400c0e402002080405204001c40041103400400400031070a2000202c801090310550b0903100f1003408841080140c068000d844a1607041600f8006403440e0145400c942c1c1c2d0700d11000c8070032200030042001c05980b54410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 993135611 1250 993134361 993134371
    0xa1e0c080402150c0a081c061214030430081b060702070317030603070e040606081e030a210c0e041d0d030902010309080c030c01050c030105010c0821 66
    0xa5010141018010b21a0820f148003000304036110811050b0307400e5000195040d00e00b5481601c2c036039507459101c0440f40c4012004079140c0c215081150010700300034104070b100d101d00d0140c2c0504840343d81142829580e44154441d018030480d8000034030004c8180310300100c50301804046880c00c07001450f03507443c082e60310040840340304803e5110741015000e010000075a0111442c002062598156240c0b060441c01050082425110000c002620303074505001420060180c03040d120040d003801c0ca4840301500b40740c055101030b4454812100c00840418012503c00640c02002d1440c03c0788400048a040c0c1c181c150b0002c4000d140426220f0101c00c80c4140300b09004260b07112080ea68046c0300304401c0d11a410f0300541881e1140314260380300180810b80c0000d810803030a00044200180c070069000d00b04d010700143c440030010031170002907100030004059540fa244000c00c220b1b036401c0043c1806000a024650005d00e000c4d48503800204c0307841c0204010540c400903000b9814401c0c1c8854101d0328201c072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 993136861 1250 993135611 993135617
    0xc12030307030b0f0604090504080c070303320324121006080c101d040204030602090123161b030302010b10020a15050c0c070801020901090e0f0a1e0c 66
    0x8014480342e2601c030300c0c01c01e65421034050301101d000d580040c905004600075410950b035202c0101d807c0040400868011448580c19520415600c0c01d0281221207030122110403620100000b901140c090038010300317540c110600c15402d40e00e58490103c140402908001c880d40c824a005098035600d855051018440d070a004180314540e0888010540c0d619501c030764543c4d03201e01d0006101d603581c600c0484180e500c0d450000e82c1c2c80aa44200c42e82c160030040746030b400038030001c3c1c08014443d06800a100f648400c2c0c84038099840e648065807070201c549903084081e91801c3c00341d421041c1140689801d22070040c2000c100c14043c80b6007401001081e0341c0110b025039520f1106a109060545448002510710b00141448150307544034520030400e1020f40f16582903440340003d481c0ea0444058030703003880c0e100c0212095140ca405800e0f00035441851000d0124107425000034880d4010340400d0301c25201100e1b4180b503a155141c100018040d0441182c42c0c1c503820f030409400d040d610340b24506c4201e219903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 993138111 1250 993136861 993136867
    0xa06052407020a18111e0c07240801050f03100b0d0c14040b03060712090c0e1009060b0715020a140304050a0605070806011b1407080303040c0f03030206010e090c1203 73
    0x40410704459030585c50000312901400b003c0a054085034040840180785508a50307190380c2c40b03c2c02810132800b0b400c0580d43d52140176500700e200d00c44c412200c003040095101e04400ea41c80f0f0341008400301c19150003551503800556002e48004254000410300d600151212076040100c0d80c23502c010307000740c2e0000c5144036507000e260205494140181440c4480074dd001d00700500709820700a102402c50208000c1a548030000e00b400c2040303c0b061540244080c8402c0c041d1410603060f144c010306c00922075403c00a04200010589001c664201c2e00559400000886403803515030b4050065001101550188014036006440003071b01c05004505c00c07440b40029001169491814604880024000c80200132602042041030790708445800e01402c0305811204d4042503607d0040310b503660051501009d8003510300e0000b074000c1c0000103980030390b218a60f0740c2442602e40c0c20802c0001443e1002030010391200004200341ca500070748440c6c0009000d03054500c50050075002c00c1000c0078500e00724240758000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 993139361 1250 993138111 993138149
    0x130308070822060b0d030e1810030b09071d0f1609090b0a03060e0d020615090112020d06060602011a19051c1703071d150f13060206010e0a06052407020a 67
    0x10408c080102044035400c0c40f8101083d6060020381280001400380031040c02142c01e0803400c2100c4c0004018010612868174402141c1e4564031009407075020038040da500100e04101c130b101003207030101c5c60b083d50703102c1201c1d10b800140d001412802d00d00c103030809a40280400403840ba40110303840c420002c00200840102d24070b0007858032500030000c4544800c2c0d112104401d558011032641102e031010307840403d01407980000703400c5400c80200140440d1134a00c001039407079010740000340d1806c100c0c4441800f0303400b49000d1205c55020b40c0354003002c4605041084c04a49441c00d4544003090f45508048172000745079580200080c0b101007071011150b404420410754541c4418801142c12041c070082044020407800b00f0414529040906501d10005c1000700d05200800162000485104100340800c5d0f0b8820010751501820302030100384800d07441c0028140391141c00380608807a8060400c0816041c1e030b00c0255110600b1441030080d80401b0400c9401596591b0301c420042c20ac1d80200800355440c0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 993140611 1250 993139361 993139369
    0x1060207081e0c130b0d0c091103060a06032003100e0603030a020a0314070c090b040c1704021309080307110705031207081809130308070822060b0d030e 67
    0x3185862010b2910388400192401e580840c11100c41007040d580c6042024100c444e200c00303426210845138104440904000911601015110448107070190400204040b10400e107900e01c4220345180d001000000104000c501c030b98030604140941d510b20f54902c569005a40344c00e54400c0d100351811490f050410301940c44070380e102a8000d98100c0003540317881741441010791100e1000e8005402d03c20480e041c1c0207402102003c41c0c0383d080c1d01440580c0301c02c3e00c0d0f902d060010704c002803156016901e001c5500302c045c1c2c0034001084000190549040803a50f9507403c0106600c009000c401003a501c9034400c00005442c2c4001d180507c5050311410703881c01e0180302d950310f4a10194031080c440d51000310031243c0d1041040403151225004034100350f480c0c0d00c41c01500300160314004200c0c2c100c2960003c2152078103100008030001842603607012102d03100c13044111031105007035035903508442400e01001c841e04000d03803a0070300c003c0c494039001c81c03405000c40014000030007040c400e82c04100c0030011103043e450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 993141861 1250 993140611 993140623
    0x1e01021f0609060608010510140c030c03040f09060b03010b0a1806020a030e010f12090c0b0c0d031104060917010b0901120b0c18150d180b070c020924090106020708 72
    0x103130780c0c5410300e00d662402000404020301e0b840000c1c140251200100a000380f103004a8807080290b004580d51a5401d002c401d40ea03510600c40c1c002040c2c030102d40801c8a298a00854045892598909045908201380307001a6482007403204280540c1000000c03a40040d114054010041a0050541c80d4007504015200e1150355810341c1c100b06001c040aa461600250542081d00d42e280000411025a05d450b40551015420292540d6000708a505400380006800e4030a0b0301655070510a500c1009000e04050107180101004a11221421300001c003984240f00b104013141c40002c6828504c0c440442c21000e0280c20a0841400602003403007030140b54005540c1008290745282d10300b0400c03103208070231514255035883c8524805020031600c0300c507203000d50b202140b25600c00c10110301051903205c08118a054112030f447c620b00700280c012030050001c1100c50fa00589009000e9503150420a01c02d10339100001d4044903c41020b01241c8400c42110301801c000d8004119803400e14400c11b117007070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 993143111 1250 993141861 993141869
    0x1611030c01020f060a0905030c0303040803011a09100305042901062c01050912060708010303030b090402030c0405060604090e060406051303022104180c09080a021e01021f060906 78
    0x548100200800041d00044c0a50312000c3c11100150441484c5461825132041e2a22a4071900c800700904c018040e00c0401141242d482c0c1c0a50201c43d00032000c003004a0069120059100c410728058001c46400303078102e150701900c150b1a04028030202c000c10110a014101d011615042440051050903080b00c6900c00b41c0c0d0040d14018141c050030802c100380e014116540c80c0c10000041750003280e40e200d1909411404082030192911894200b0005008038024441034000900341440d080c1e60741404552783c0d02594000d070152020b003c1d40f0040c00007400014120b50b4200d08100800a11f8071064400d070700c902d811341400f0340b00904240c1005402e0f82e8010380782ca00c1c189045011000040d130002040380418410340d1500007981c41c088120744480c0170725403042c801011014940c441c20611503101e000650210b88501080325215160190756020301007000750059192150004207000c9408400304010701481160081c1c1500c3e0040903880e807222080f00da600352500c03000e1000c81e4603401401c0243c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 993144361 1250 993143111 993143113
    0x1080705040506040909110a080a03080a0c0203160302190515100e0a0e03070b1609080712030e03030f1308101b0806040902030717060a090302070513021611030c0102 73
    0x215003040b00181e054803c0f481424241965456070700c2c00c0080a42c840c20021038018002d860040d5200405622140341020450029480000040a1000900c200214012546d005608020f4002001100d2806002099082d440f80303015510010b0700041d0010055840f034130280034040c40f100d081103442c0340c0140406465101b10a000d001d04203044e40404d40c4503490400200e070156080f0901c1d400c512032030788050003a502c0c0c2810844034060741c0715010700c45902c42c1c0e148041070755500e48440c0c0750b07000ba00030b0001c060084198580440d200d02e0b1486128503006058034a4400e2210325400c9070b521810340c40501c01890002081802000d01c40e1030590190000300b80305400e0115107542c8190aa0f40d459014011781c0c6003c180307161503581c07008010307a6000d42210900c9881340c02182402003c0001c2010a02c03900d40050300c0518035000e059111b0b94035400620b151800c2004005400e04011100e02405600384000d41e0030711390b14000c11703031071900501c1c0039101c04000d0320900d428680450045415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 993145611 1250 993144361 993144367
    0x40801060e06030a0201140706020d020f091305061c150c0207180603020105040b18090c0c1009080301090c1803030302190807081605280e0307030f110a180b01080705 73
    0x250343c00800d107d58200c2c00c40410b83d03588202e0300e0294024040c040d800354905101054848606900380020112520111342c0c4840c03440c5155100070940384101c5040d600b00b0381203402e480c0048030740084003551a204010011203102014101411114800130486c0142c2c41050100034007511801e400003003e0345800c00b40410350444c0c0028101d44107034803400c00103500004a090310090300c3c400c83e400010b4003c1042846051504006d4030a81040300025000d024280f00305900b4443d40c03254400c04c50b800010107040da8605031401000b00035003e4a0403c2c04000c0d1400500c520610b50000d0207188203441c0142c4801482070402203000d000c141003024000c1c142d0520400b15000b9040700c0d40100444422410185000320072100e50052030201c040e0b004d07425003c00410708070b0080000018604da6200508000c840080590365030040c4000390507a0300751080800400c007207480600d15000003620540e40300380e90b55003030b461000e041c0546409560307030340440305110741e4000c15040d0803262516200341 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 993146861 1250 993145611 993145613
    0x1150e0c03040c0e25020109022119020d021545150f04140303030123030a1712060108070905040203090724030e1c18080102040801060e06030a 63
    0xf51000c82e6000e003080f04803808001550102c0218005200c45400361011925180b650001078040c05049408a2140301d444911100d145031001124900c000e06c4002003240711f1020303507010f070f0140755600c060ba040b420858100000d621000f410311404408000c03a140ea5100610582104a6150300b42c440b0136414840894500844007140e46420000c0c20039040100c00b001c0005060b043c00003500c6000f0100c08145030b0082010741010300708072840b00301b0348002e0035503080405490348000d000d018001d1004031007400c2c04e044854007100744103002404940464245444800c4003030245111030306c582c0c80000e001401c001000e0419a048002070030301c80031f58100760300090100b02142c000d50b4000d9502200007169000b04228900003030544840c0c2c60346501c206101000b44503820094440803a040100c6410092130001c1c07155402c0c4a920030071803038078410500850741d80881074841d20307415100074000725010300300f880104020003803440002803c0749082c944100b4038900801151181d004032840d44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 993148111 1250 993146861 993146873
    0x60302010c030f170c0a0306080a121d06040e1f2702090d080a080c0f030c0901020c1306140114040603020a0c080a120b3f01150e0c0304 60
    0x2044103606040426030201a01c0701204e407801d132240e5030901020a80c0500080d024088018111900503a606000322500d55443e942c0e0340150100c02420703100d0000f07092201911903400d501010304001c2e0506004880980010590b030450b8004001051030302090050b1115500c16081c40b00c000b140c01501000d2800c3c0b04203046840c01043c80003007141c2c40d810381c2081c04540e41190700c000710090003d0004490350801d01c0c5039400c0f41e100b480210b40c40c04003261103e0460010f44052106480c8001d1640c0d49000b40031500d60000c0d60454154411400c00040996a9041c0040c003500d4200d4002215032a00500b9946019201c0c2c0c86810f004808188580d08006441214103840d040c0c2400342e030320b4010003012103455051740000340c41164007095010f0520b50100d40d52161202c1a407051100d4403500302002060151003182406271200c07540301c000e010212030500f030000c007900c0840580369407a0071016400e48098105101c041c0190780c17410b000e009110f42406401500b440c0145081d440d00c2c2d80e84d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 993149361 1250 993148111 993148127
    0x19051513200d0515060118081902040b03061504051605091002210a08010e16111006260307020105030f13080705030c010e011b1d06120106110106030201 67
    0x15002114032598000298881040321103000f68008102d60300c1c501c0c8030b41c100148120941c1e0450005036811217404120001604d01c0007684c445202820181c0c200d14120344003041142c40480e049500c0b00d04040b0300355014448280b00e04038000041c01050a803500f00320484400030004405004080c5400c1a4a6400000d842c2031610070740e03240c0401c04525005038074282010030300c1c0c520780300780004030700c0c0150489004e40759100303054481120507600d6a40b440d01000b021980346113031000031300c10095850b2140d40007000700740303d401c140c40311005c1603481d00d010755440350480b48040b2807000b001107000c0140c0c0302485d049003082020b5400d0202076030000b000b03888041c00300401e1041d640b0104035440240307002d00c0301c484d51104203283e0300c400d01c1ca070064803038104030705980080d482c10801480d049030600881c8031019070302c00d10902040c524401540c280c85411204000e0b0031070b2081c0000c1e651520b5004000444004c41024420340c54008010880c4054485040441c1d062100420041c1d0b049031503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 993150611 1250 993149361 993149393
    0xb040e150414031b0106151413091505150304030915031e0b04050f06150a020a201005070503030406050606090306070f020f07031205090319051513 65
    0x3226036031202e0601c1980b01255081074100c80c0000205080c0e2010041d0840c0100d03183d00c0000d0050300d1340c0340071088814904081d0710740840d041400070728001c1c1b02c1e070005200003400c13020005942a150f01c0d0100848030383c50f2800c20232240d0514144001d180c8640d0b805445030401e00e03164594a007554000780703528101d1007401404d1180540d00c9001c18040d070002034049e84a61104600010307008000e5002c2e0034601601d500075440c1c040810b840105d11103860f4030840307025117803860040000350151150780c00103d250045000d4008a100058002d08403107100c0c03111011100030102014080098034548081d0740300510070104940360015501009407a4003a41120000829644010209002d0b200b41a41c2c0742d41400341008000000c0c0e00320362040c540400c2d035400c030794042541e0008599030305c6190002801c1d880950b4130300c0165a204a000700f2030ba26020707042d1500c5820581c1d131090301055210040340c144d00081e66422107512160405c3e5403080300c201001940c1c0480b9141d000d41044c036600707 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 993151861 1250 993150611 993150643
    0xe0a09020c0705100504081605040b010305070c030509150c103e040306050901050a06090b01022104081f05070c020904150209030321070908071e15030e010b040e 71
    0x46201c0c541350082003500c0081c9000001e8800c0c41d070300c0410701103030100305020380c5100e640307007504031b0607603500c40d1042ea489440c003a12600c5200c14152425035407034101d0603603158409a1070780f0103062000344c100070b4208100c5110080141da40710f9075070842a105141c0c690703810580c02c80705400030b620013046564141c11120f880c290070b106030500c00c51654801e980000e4546420f01341130290402d01544000d204e411040400c001d41a200e03107491055500a66203030303006900001c5032414034040030070740f40b1200840301c2400c2e141070784d42c40c0c4150a01d900690b0800007054003c0c01040e440c4081d003c1c059005a80c0d15041d42101907903400200c1c4888003a001410f08008401d03c416645940e074101e892030280142203c1e107074a544500780d8001c0c000d00010f458401c05220121312520302a800700025140c4c1c12000d07000f95800c02001c20f042640280c106400814010300000e101e441c080d008070020403050307402142c40090307a04a1400e46e00c00301d484a0055182c02e005207003c00c0046050a106502c1071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 993153111 1250 993151861 993151879
    0x604030311090402180a0501030213051516030f021507080a15080f031305041406091e071115012414030a02030615120f041a070e0a09020c0705 63
    0x1000c1c0182a004421003150410b00c00181c0415518954480c4407150b0001c9960b51251915040114164000c8a060b010b41003103840741445203203024001c2150000b0344c00116410101c00040c4440d00c0104041c3c241d01049110b000310140703075414801400e22048540e64200e035810243d2004165a00050021b980107588403090701d0082c0030800402c009001078001c58101e960410019500d90b4008624046034140c6070b035000499044c0750150800b82c00901502d00110769617135091000a4200508400b000328480c941620441111220207001d52820382d9080e488044000e901450104002c03003180e1960501401001004080da615903031a840340c03020300304a11070030b91056a202c0040002c1040c0312001100304102420680e0145100315030450b02c007080d8960031103000c581849201042a0100300103400078000b0b00e64240081d400c28800d04215003465420704003481c80010580740c0b1400500304407104d00c114644012444054070345030b80f045282c401100b95072031361400701d889140e000d10014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 993154361 1250 993153111 993153131
    0x305060102190b070e040515040b061e0405010306081b041e06090c090b120103030309030c050f060106020f01020414121f0213150f03151203030b180906040303 70
    0x1e01c00003500841241c4040302c15500c5241100101104444034400100000002201c03031405000d40e5000340d00c610601086104468288800f900c015150507030440e600708500e0b81100c020100c91782d01c100c04180d080340c449040200040540d1419404101c20340c0c020103958560a0006d031802c3d0201c1c03400c80e40040d0a9244481c0c0040c42c601c1400005061498500700003111406500038009003540b581e59811440e8454885030028000c110b62034240c880031400500019000360711552a0502900741591545925038400d4540300080c940103086070055401000b20f0350701000311030301421540700258100b41c2444507812a4030403078043c1074407400070140801c3c0e130208184001c0302e01c02048802c1440000007644190040d60000f07802c10040030111000180246800c41c410304080d4081c0c1d600c0b002d0308040d600403000f8100300c98001e1610481840c0000746030051403016851940301e81c43c0812092121030410003e11105c011a0010141960030046078040100e401944180c1c9424001950501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 993155611 1250 993154361 993154363
    0x40b10050909040c1508090f06090618010f0207110901140d080f13080a0b060105070c09020d0e0304060903060e0318010813120504090f0b10050c0c030a08041505030609070305060102 80
    0x7443d030054120290100151000a9115200602c5211003400b1030f00e22030616092559036040031228013245400bc0301c040382d442015014280740e100e400d0302c0007103507202894040408aa10000c01210008200002e94200d030415025450060402e00d03e55111480381e5400f00701e410808100040c034841c0c000400e091380d142c005041c0c0d000780368810f0061100319164880c02c0c0c0c2d40c1e41518410344081301c1c1e40001078159032081e412125070079807044408000c189000080740203074011142400019894481400311104c041010304003d01c1d550341d648504a1039402e0860880b241442250707060b82081184910b0800b040c07024030741c035840030b02c1c1441032603885491840310500b8540b0010b050b00901c400c0e0700b07a9198030402500c150b40e2119030400c40c152903c04986c04413500c01e9040ba420007007010340d5002003801400a419003000c444d064a94425441d80000e0900403a90340849202c2c402140900044030b40302803c40140029081c1341e0b285082200014540c102c0c01030a5804045e2900000b40440e44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 993156861 1250 993155611 993155633
    0x915090501030b04050f0307020117060303160c05010906050c12031b0f09090a09020d0308090a0501051f051203030a050c3a0b1c060605031902040b1005090904 70
    0x65508109558603841c0c030101e51601a20700340c030703103201d4090703060250704021080358441c0e0760585030419a450080d80340c500c1001c0040c140c9506000500c103580544024a04616250b4810030104410604140001d0001e01d500e4004200304030041c028030040c51800105210707002c00c00b2480e0741d12039507014400d4200021540061031030101c04500d5146c1032034184080c241501c402c440e01030b0300343e4484030008115428200c002c0e500003c03036028000400d000d40c420b0342d0070900c9030003950368851281e00c0e0182552001c1daa84c4142070f511034890701220004442080c0600411181800c286241640003541c0b80005045440125038410100d00c1610626040f1414084100201400c80d002c000c66451010007280b80d062880c150700710140720022032071040b4249040700818001c4581c5d51510310241c07400001600322940c55880300d001c12990750810289a604111070171901201c80c940c0b050206461813141d005000702519018050059000300c02d60f4451b1070107441c0d00700726544c0e5081000c038141c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 993158111 1250 993156861 993156869
    0x30c02160b1602120f0714090a0b0303132907030801170307020904061a040b06040605071a090703060c02031603030911100c0512160206130302060f2802070915 70
    0x4044c1e1041ca030702c1c02130200d00c605040c1141001d81c0c80083d03541124800e0b41079102d40040d0303c42c1c140740020b5600c0016900034004090050126030908008001201c141d802a800060310054400380c42050704480202e0628000004c480940c204255990040d240501c180249007582603010f107413241001013041540d81c41a001400900c0a0510341071480040400ca8080303140441d81c40d548410030300305409103142c1ca10018080c14a0a4908001100c19170031040003280c0d5080b102c500029074402c003000e018040c0500801400e506455450040121000c4001348011f5410900945884910a141880c1001d41504021415070510302d131110200000700c000a48c010024481d00c015954817141a60006101d503003290054070004820f08582c0c02400740070305100968130205801810001c0142140c1c0b60700c440003503075442d22503000540d01d4010241d01c1c240c2d1000810a0152080041d0749070009a00208543d07800744100300c0700039200c107a24059441c00c00d84954008030058a5030884c50028 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 993159361 1250 993158111 993158119
    0x1e0a08071109090a0503250b070207061d01021507020a0606230904020f0105070c0e010b210709091e0213030515010609031b0e1006030c02160b1602 65
    0x901007071400c0140315061801181c0240b103060002081c61000091843c0c64070b8100005500300702600003091603050390099400f4140400c061101c0010303204607004c1d4010304960f000b501c552400c01e0310062483da0722400301d03c0c445411a40c2044181d030003291036125400c1032903014500c0e40c0c45070b40503440c000300030000a05d00d51a00c5000600402e2108920510020b40000a00c14610020030040e443d0015a0f02a51265140d4034400c907543c0070740000c2c03104500c9040130510003991415010301c810001d89c800c001d075080001e01a40c1110018001072030300c0a20307808a500508105100a224506a00508203069914183c04c040b18445101000003014401b5080d5980e241c1820181c03404051413004480b2031241c501080f20b19003040b00e1542c107807106c6945110420b4a10344401942500315000e00450034015038021030100441402148254102e261001941d45840e80040460b001001d01c4011074100c0d2080041d21000710080384200c2c1c152002451f00c034044400e440d4000c4108640084d40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 993160611 1250 993159361 993159367
    0x1a09040e0a050c01200606122a0910060509130b3c06073018080105061c02040e0f0601030c0f0308070303020c0a020402030108010213171e0a08 63
    0x802c0000039248001003000e81e25040361010070680001ca000e144840030401c0d401603000544503040c00c40080c42d0201e00481200d0000f43c43c1c9903012701c3e113102a00740482d5900003c41c00b26084c20046105600030495112040c3d4152416000401a020300c0c250b0500c28542d00b81032a510590345d8014038020b000041500300058000310b07207140c400d043c048000011058160030900150004404403a1850010304071034035203000c60342e440c210031519488100c504500c00129072001045901200b0700c0446584541c824004828040d4121a12a51000701213138145030400c2459141d01010b0035240100d0b46e4408081c081c01e20024010300301c590320710041032080416804010100117852412a07002d18201c403011525485029900c01143c0400b41401200b0440c500019210368010f00707028070100d0540d41c160006900040036a44280e1020340b881c1e40100f2044032881032500400020510031405400110a416500303031185c81c506121504401c0b58441074420802c1880911040c0e42e000503003540d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 993161861 1250 993160611 993160613
    0x60f0717030108071a0c0303070905010e030d090603020c01110304030315080d2f0105011e0f0f1a220303110a170a02010207020307090b191a09040e0a 66
    0x111a4008100a039140d090080d00001500440021a070507070b14240050700c049410100c10700504090307000c0100102004004100d0302c1a130600c080c40c01140581c0d104003801d403418000400190b2420203c51094019400040718142c024040f1012968141000350b11401d440b0305581c01092a54200b0b05045030010400c010558180d101c045c04074828031040e00d80070f8681c000c803581c80b0025030f1950b001c1440403648840d1512005443e01c030002c0da04a100580030b6a00601ca425910203274880f03440c40745440e1480c20840d01040c201c602a242c050b0700c1007409440d2208070306c40c00380d0910426600c0c007240d203c40040b0240b542c0031281c200ca0307a040c03140804c4d0440c01141d08942080d06c0242c001500200c080d034800007000c142000002d82104003d01980700308103140d1030320391180300c51a05666003085003c00580b4140b08550080c016140c00181d0491088240006070703107284500c60300c04030003503820b01c00c1d00003e80c2821030703484100c00341c6611011090086070050200809554039403080b0051a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 993163111 1250 993161861 993161887
    0x921081206010324261504060608031c0906090f0f02040b01050306030c040510080a0302100b15070f171602120606060702040b03071703041e1d060f06 66
    0x40d000d5032082c0d0b0200044030205000700001d4081444010100310900410410181703400103050b1402d00e02d41803402d002e0741842049180c03c3d905150000158208804c0000384042d44c07060300c00909500000e189050f00768244989144084000003600c1c41c1d80300580000c5c0301ca01e50018186030340c055012141c1d9001030402241181e1059022803003103003000603440240d481041502c1c05401c01800030a00b8100160401020b0175004140400b00e441e540307000950120104014540b02e4060340107842c002085c18a11410f0701c2c552015140145001300e030741d0340079981e050300311680950020310b52100c4000a240c0015800303803c2c00c0d010540b000c0419180702c01144d40c00c407400c240703100b140e188200c10880c16003d070302d82e041114850307408242801040c3c003509242c1c000702a07070701001f016103500c0780e207a0091412030517066038814880d600100c0c0600007030401142c0500071128031a0b103507107250b10703146001d103428030302c2c07401c00008170018400705809403035907a007403c1343d103070010a055111023040080c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 993164361 1250 993163111 993163147
    0x151803040b22050d0b09100c0507060e011a090c04080d0e04051f05060705070b0d0b03190f240608030c0c0a030f0b040f080301290a092108 61
    0x6034080b0018a00c1281c48110690311001211005007002d0010816a00c40c02c54107500140000d1a13401804041c0c503808078907100b010105107a580300c0c0741d2540a5400e00e14211011414034014a078034204034415000c00a15400c2300000381111503181aa403101c030088001e010320f5100c150988518003220746a19008114119504000d540070402b5130340b5103c800c1ca0412161a03003002030f13103400301c0074010380c14807500070302d041030040c02140c5c00709170f030b4002c0c3d010300303602c07141e40307660110b81d075540d007503180d103030500856010079000c2501400c800c0e4540c80c0d41c3d040e146c042c24001e2400100030002c444109440030310f07046080442c1d00130091551754998040c0c40b54000440c2c11510f004001c00c8480030318120704c03080140c035080800594030b84455a291341000d00050419a115900784401c200004c90020046001e8803d0341e40049400001c03800d0501a00b1480384405c0b60840140030304014213500103031840898181c0c001901d1018580300194200700150f150150000c4800110301e2000fa003102c2c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 993165467 1106 993164361 993164377
    0x1710091406090a0b01050f1804050105240a1707020f011d1f02090a0f0311040b06090103090809030706170a090206040b07020f090411031e151803040b 66
    0x2503003050350440c5648c0c0c807a005d03104404902da801e0900455004200a031080f00f001c0d81003044040300c2c60381715065081c8200c4089699036a041c45608244180f41310220340d0809400c0000700203407602d242c00000c2200b903082c81c80d41c03601030405000d104008105040030f007040f03640261f46406d107900500314982070941c090001c031203595550000e40006051824048c07500900d9450010100ca412040b02031146103040065107280c0c54480840326060000d03e0300050800d01c600c5c1546141c020800c131305426103e411400f140941e0019400c4450130725007040c3e02c6440e500c910741c000589004020082d001070050004020160301c0d00f02801c0d02ca032005143c0303c0c4440320f003808241540c41c12a025110314051130030754403a0b803d090010200c2241d4100c0007032000d10921030801d54030117540503c0003148148400043c2e04948928902000c041140d050301d580c0e55544140301d9146e040024 = true := by decide +kernel

theorem cover : BRFrame.Cov 992985611 993165467 := by
  have h0 := BRFrame.cov_init 992985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 992985611 ≤ n) (h2 : n < 993165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
