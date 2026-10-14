-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1368
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:36:51.602734+00:00
-- url     : https://prove2.me/submissions/9ad2aade-5ca4-4426-93a0-a644c1346f15

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 245863309 ≤ n < 246043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 245864559 1250 245863309 245863327
    0x10e1005151005072a051f050d0b03030c0307060b0a0f0911070f1101020f0a050c15040e070903030305010b03041112340b09030604080a0c060207080c1002040b 70
    0x84040d1002c45580c030f45145030045503595401160012440c0c0300000ca030190310210313151031460283d8003903c8115110302c00400401a40c81d2000f000d403038102c04002022905503250324103600600d5075500c00500381e81d20b801107450161340d607802007801580c13014105031030064107040c0103505a0540360640b5800310038a003400040317000f900030645400000d6608000107408109605011303101948141c0b80040e4649440000901d44130490041a40034ac01c880100c01c000341c00022040184102a02c036004801613504905485002e0f991041807031014610412929940c002075420540303109440c00c00107640c8503c03004801d400111002008001824001e800382d151004907901514041c20896100604521100c0c40d00a00c048420721341c81d58100c2c1c52020301d070341d00c084400500a11001103040282c4000085e540306e80140c030240c403441000500b03040711403080c6022507456400490665950f2418178103d00c80360302448000d882d900420100c00011195130084800b10307100491040d0901080c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 245865809 1250 245864559 245864569
    0x2040312031503020a0e07090614072301020301060816030218090612010204060302040801290907050c03030f0402010f02071413060e010b030708100510140903010509010e100515 78
    0x440d0342402c1d1000d44420010059030390703003503c60151038044800d4000c0d00305040040c0c141c2c0200d030003100070300a52040401100c0111416910103d4124140c400983c140172000c1c08070001500c540412540000004203603160001d450600550102e00044041c01e08030404900301e00880c00407881c0c8400304441d25580c2d140400f5056005078000f042610303010420b1411500320b0b40140c0c41080820b401041c10001440e0038421101d00b110f0b114042c401c4400c0c04160042c5481c01c1001186c414069400400d8070241b02d1400e550720244400101eaa403030505c0b010340c030b030703001d10840c1c0c1240003d80380d20005803c41d10214200003290030810f0501c02c0b81800c0340801c0b804a50345268020450798805c00000c40707288424a4034003d110813600c9554070b00f01014010820b19006040302c000c1944001e007040340ea128050075030a01102d0749440d203d2184603540e100a01e00c92003c0d01d80e070540c206002c0c010101c406500103260320200400700d81c00d4440d8054400705868049956819040c581901c1030304500f81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 245867059 1250 245865809 245865821
    0xf020307050a11040b0406060810050f09070c2d02090c0a090b1b0106030c0e0c040b03310b2422020403051b031b030d0c0215070f050106090204031203 66
    0x2005002107500c2170442c0108040710700607400f07500028070000c1031040081818141001600d003e40d100b449080318070700414050b00001d8240700422000001c090140601429240340340c00c5050b80c041c0c111081c0e40c402d00445114800b041c1d11402803440840e40b01c0d04060101d0f040f446090700c515107054600340710100d454028010f01aa000089095034031418001c0c41030002561080c51181c0c41c0340d0801c8440c00f91000000c00244101500700424041c20382c400080d250f001c241249180c45640c41c640071603419107082c0000749541e0384020b088408000107104483c0c40f414250010303012014614484024214000a5441c1c02a18a05442d0365989075a040031040e81c801150151501d0307501e0352154901417030155041000345001c55002e000d481d003800501e6122410000e00c0444105c01c40000b904e40420224010070300403000d064104645071240035045000110103481e84455a80c1440d150012010720112200c2d480d1120114280a44d40700b0f0301c080e65000301d4031a88602c0c800d0004d60040031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 245868309 1250 245867059 245867093
    0x51003020307020a20060a0206100801020403020109210212010b0931050a1e0303140601050a03020c010b031f0605180f090106091e14190b150304050d0f020307050a 72
    0x411501100d05c5a00c640c0c005145803250303a8010016031410028540c10b11580d03400005c81640100410000340c0e138000a94000e807039250302080c0c2c03004514540003103031102c1c0040081d0080000741d09904020019800b2100b4100c0c26241056556203034a1820310703640c0107040503084800018400390169484160421034a8800c0084812032081c54130b480c40d04810012820120050104608007090f62500842e00c00c40a2107080300d10b01d0030300c0c8002038028091105481e04060b4007180b061079540c407d40100c01d0055014081e03910a480c08000c0780120a10700306481c0240b1700f403810004042c10320090542d006041c121000b8044c2d114400b40000c3e90401070b0059a5035926103a012820804510400100002d00c18910300d002c005152018199101c03046070b8036a00300030700200001c0c0c0f0448001c3ca002405090b800090620203040042c0c0c2d030010340b8500d2202c19101204002c1000800540c6a240602540b0b17072420540700500308030303581d10078030b000140f440d00882c003454002100c24080c5241c1031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 245869559 1250 245868309 245868353
    0x2190806100c1b030b0108070f030305030a020306130c020123090a020906181e0c030601020a060f020c1204050a050604030809130b060c0d09090c050f03090a0b040804051003020307020a 81
    0xf1408072007a50f0861400d1304181d0351410344500400400c2c4041040b94000c1140060000f00349240d61800b9101f4000280034010142d00040000c0c400d989010001240740803c41c000c014007840290001d0081c0300308001e45400410000307400822401e003100c042d12450320301c402450100c1c166401d220490f1400b0700f0090b045462081107465000800c48110f206240e14004036800c003207000c8031030301441c80203401c00c00d0703420701082449481d1360301180c0500707515005080404c12080100c2550002e109540c2001d40c28000e100000f4107054140c00248115442200d2010f622510b400030040c180c4281c3c0300c010500c0404000645c520300b0700d0358040910500503040010728508810100314650300c123040448554106050700d00c1c0b00380d08907450b200903040300c1004002401030428050400d100343d840c4156000350101c000350010380c041290320682a070152021105003000d15201b0000d42090061b24406d401d5400810b00c1d43e80b1038801e6911030700440e0b0051100600d02c0d01d0f00104a200c20042407481 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 245870809 1250 245869559 245869583
    0x10812090a14150f03070807052502130f0902040b09060d0f020402091203070b0115020c0d080409060b07060f110412060605190801051b1b03040906060302190806100c 73
    0x41201d0034054456400f0040c4d905549182c503440040809000070f0452003405020b10504808401d03000510181c140c425881c24901019400004c0b001207401030100b1f1000d040c030103074100122082e000b1600f2140b003910144400b60322101000790301c0c0c1086482607000b030384052066003ca12070b1005008814006840140351000c3d20002c14840090403000e0021076100042c0042001083d0040c1c3e8010b002070340f51a014110b9482c03000b502c0302200d940c100c1c403c0709054400380502c0140300c201d80080407458800c1002c036548240060280d00b200105458043c54601c800303050600070302440c921450b210000d6850142000c0c100d10100700f4110003514442e80d105000708158550311044600d800480030074071301007454114114252040201104d4202c074413440c3e45030306080500c050f40e00c5980e81d1101c50b800310032003d20380c0c2e2a40c00760b588138941a07410320200060311901540203000200e03090140100c1c0d00014501a92003a0090301d200c0d81040c5240c1410300654031590381c450105200e9800c0c2c03100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 245872059 1250 245870809 245870839
    0x305120d0f05040f03110a020907030c050c16030b07080105010c0f0f06050c0c0106050301060b0d02070212030304390911040b030f0a050615090906060f0d05010812090a14 75
    0x45034400c42d0102c1d0304200d030f980d254040c07682003406601b040305a84020400403106a0100704801005800c4805054031200501021030140c402c0c0c40a0005c00c808544c03066502005900c4240d04a22003035402e0400100868603840c8a0781c0740324142c600603140d644880240b959011301c042018141910600140b01c41c100000305036001d03050051919001803501d4055200c8001c2c212001540054426858613104102404094054900640c208100180c0b03500050002c03400c0240c4507803e5005c640000400c120401250f51004820202c1a20a820244122035083e0686144544040182d00350011042001d452960013000e0300324041420356003010340c2c0382981c001c40c0c0c1040d40c100a980c030440b001c00921110a1041c568003010446245500c056002d80c241072900c54802800d00808000d0001405030322000110b556200108442070758844c0220314400003000e080c01048420b0207000c2d19900642d40b01c400f070341d120001c0244581500c3c0e01c1d000303581d50708201d2196100c0e0030814552070516 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 245873309 1250 245872059 245872061
    0x139051b010c02010603150b0a1a070b041a1003020607061508030a03021b06010e04080903070e09030d05150102281202030c120f040501050a0c0813031a010305120d0f 73
    0xd00b1840540000c52101d003103103400c0c50003019034100c42c07000350f107401c014800e103030350b014002402c940340f040c9100326a10044e0008c000c01e205440000d441002c0d40703000d0000b041400703040010f0401407404801102d45400d5603200d80081c80d4031010703501c032000340640c4011900e2544010000700c00c407201001c03010340d01e12403036086401106180001c2039001c6032200102210000d42800359500340c000d0101d640c18000e12a011107409400600780c141c000c507040d056034500300810030240a001a07039032981c1c0340c0f680411740c0da039022803041c10f074807820000409c040c05c5142080040e0894143c02409110030880c050701100d03600880b402e000c015402c081100070030019804036030301001a601556a410380c000016141101e100c1e05140381100c00c01180710802c08800a490179101c092a0584d03070b4505040d411505050f5283c0d0150603088009101c81c099081d001c215030490340316450013841d602c180c100005100ca030902c0003400c19005020350b80e91100349040100810041c6c8030780080c0320024020403038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 245874559 1250 245873309 245873321
    0x1e0203060a03020910091413080f0904060e15030a030f050703031805070e09070609030201110c130b01020111120112031806030b0906030a0f1106040302040e0139051b01 74
    0xc000c14040c0001440440180d0144001c201100c5011601f2030600108042d40c7c445080790141110b040400c14002c955085022112081802030041c003505031a000d45205480b005c1d00c1061001e009075034034181d1810b011131080045a016240e0090040c3c0d900030585e070039849008100c04040d91030081820590020600300b800500400052a0040c101440c0420744c03840545260501d60cc0700408218081c0d02030740210a4907070a19016410061001009181440500110740d0200d108a0038048062140d80f220011007026802403000d00041030a680540c840c0701180034029542000511211300c0f50032894440314401e10340200c00c0404950070040f640d00c95041200000e40350f54080503146420000640c021030120003900a4068540d9070583d5a265008014403040406100b04031907030380c0074146c800454003d0b00c18050025545101030091000750392854842580020740307403c1740394220526660504020403801520003020b41900c59420004030000d412801f81250320312220203028203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 245875809 1250 245874559 245874571
    0x611120301030b090610120204110c0a1110030c09090b030a050f03070b01060f1205180f0a020a060c05060a05130f05010b01021c09090906060b07031706041e0203060a030209 76
    0x100f8403400e0071044103042c0030000d0545036122440ca0401d0001d224803003001e6250301da0413507001a4142c0291700400e0140074218503240607018040c41000ad03c1400c0e060f440350b0041c21101410258a844070035812a4070400142000812409050250403134503444800c0d0804000d0407216941895038600745000481042d4000c10340002c244402086000340a081c0034142d0b5050a11942d025030b40e0050042c8a080b4545900d2900c550209001c92581524804403403861002e54038041401940b86030f50700c6900c01c049008410001c00010f055126141c05c11280e648640075101c5621540c4a001c003030540a044204424a80150711000039040081070426078403e6001240210502c4000b904241c0c3c61300300e21b80300e442001d410400d0994001d0303219095526078480020401d8071410200c0042c03000f60040c0c10541d0703002031501c042c19000f00d403290703807644480e0001005950301001d0200750b501100002c80020001500c1c404503038125000303198811400342c0030002e030f181d8907000143c040d9410740b06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 245877059 1250 245875809 245875823
    0x5120a0b101415030705031b040602030c060f0c0702061804380102190813030302060115020307050d0813060906021c0e0c091b0c10180c061112030103 66
    0x3041180c000482c1000c0c0180b04681c0203540d80c14800344a00c03180300081002081090000c0001d0403144030040001c3c4040300740c0031864a5903251a4044c0d9030350b0040c102c04485108038070026281d03043c003412551040c40307400c94880c105415903007400500e4200c5002089403004103145142c90361504d100300045240d482507201c80510f0140c2008400010f0030003014403140780310500c4801c5980000f0781c0f080700c01040c01410659446420910301c10301131000401440c0e11140b0000051544c0042c5490585145046000340b030101c0d14003d0707a0f0380c23043d00b41c000e1454010f289000032180c000e201c03807a40005400300d85000000590384000803180180d0003110407030b6020400c443d00c015403180c2542e14240001c1e0420403540f03500e02295a03040e40c41c4401d88540b90650014909403030041040048682811f01e543e1034030045960303e42c50346841c20241202c503280540041744400406100e01003150402103950896040140448e0301100c0c2c0c8645680d42c2c81255080fa000c50a00c100442c025400b50740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 245878309 1250 245877059 245877091
    0x15030b010e030c150a05071a090d02030304050a08030705040b190305061207090504030c0f0303090506061806100216030c0f08010501180506030c0a030f12020304060905120a0b 77
    0x10000d060000c001c1c1d1107a0003940000c3d41601d041d110102c20510350044c42c01d0150f150490340c00c013100ca03803062200084c46c400e04864070041481221650710300601030003080e01c5c083d040f0400201da9038001201c0c06840359210701070f0040402c0c40c1c0780c01036411000504d420340c505511040605003a5104400c1071880003242820700140607030600c070700c0ea0011400c68006410101303203040fa60782c6284c980110140c055440010808060203941206e5080e40c0c0084d54420b03130301380c90601034010a40c0010545403800744100244440ca402880300c0c0168811f85078003e0300707403034034002d028058020612174000d40c89104810150b441c00c1c400f40100952181701aa03551a09110728511030810561080d03105a0520703005008074640d680a81d18403406a410000301a074807600007a00d0140301415142d0070011840010090080c61511403981c54001c4c07070307140300e4401488001ca07543d218921800b000101200402e018515045050040645284003140c0051110740c0780d90182d900e00340d82c1802070014043c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 245879559 1250 245878309 245878331
    0x307050312060f060a0507051006080c011b06050c13050d0807061509150906050a03050718020706020a12050f040519053a0e09011a070f080913050112080a02071503 72
    0x401500e12852707180c01409501e1502d0384d000d07070f20103403c5445410b12818110340c0c0342d0f041899034090042ca400c40010702040c01c01c06810b481d0f44d071000d8034805801e18005004641c43c1004a0414045580103549520b4034816844590040680c0307000c108038400060b81c0080d03c81c10b18021a199100d206411000c50b0341752218003401c40c0c075940d0005010f000e81300801c0020440200c1d4410803a0340c2c6004407802e00c0700301e0040c80000e220b011301c01070105201240004ca034a41c004201e8031102400300c030401c081c0d2a03044a105140301c6c00c590047c07540d44040010301d400c0280c110f80400c41c074440d00845240944c0d50a1020254550850036074017034000d4100d034040c040c030072001c80f07612162500b0302e682118100d9010545103007050141914140e408241c10645103001c2048030340281d0000d62100b4111034074078003203035030394451141c0c18820100c41040d100c1c126424443d2504841700e07010404010f0b040c2e0394803441c2e10b070001c1022009500031600000342038241400315107500c4000c0c0e580096940540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 245880809 1250 245879559 245879563
    0xd0504080d0206130b0903040b130e01140f010302220305060f07080f130c05030a030207090506040b010e042c070509070905010e0d02030f01020a0513080307050312060f060a050705 79
    0x101c034214007194000c00611510444090700111a0340d001030b01c03030070107070380d542ca21625520a50b440000c440c40000f1310300241281e040b031041c0c195a298810165540d85c1d4124004080c8011500c0d00d81c030095406070141c0a6000364024840710944034450301c0700186e032001d1010800e40550040d0340e9034215004000c000842da000d00f560201c5a0309118455050242007981c03040002480071082450f1a8941c00511105081c0d080060800400f182d00419035407400035100d00c0320b4819070f1022820a00460082c0c9460300a83d0f0740248103a48482644260b00200700c081c1450442841084214a4040c6024000e204480804400e0728000323100441c641000c0c0401014001d1099040081061060060740e90151039208881c0085030060808542c500009080000001c000c1d001d81d880090740c6410590800f000d060a080381d21080c3c2c0311075684210780382d107a00c039003c00102140c00c10499111551120501140c2001b4050711603500140b00c000032840a60109032800049540460500208442 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 245882059 1250 245880809 245880823
    0x60b06040323030c07151b120806010e0112020708090334050d02090601090e0a0e1504032307020607030c02040509010605011e0201020c0a21020a0f02040e0f0d050408 73
    0x400218600000c2140464a900c034501a110f801c0a981d42000c01c207d220783e00140c4c2e0307901d034481d0b05040c60603246021001410100d400700702107910761000445540c0900c1c4400300164041c2c40b001c1d002800d1500c400000d6100b400101d034501400e000303655840d00c0030030044407410b001c0001000c0c101c2c1183d0506036020b540003103c1381c101107020b5081c080d0342c807400c9450031050790586041c1c1c990b0320b448005030b80021880e0054010003c00000b0000803500315084009606055416600c2c41803010310120344441c0c0c00c40c0c01401084100b5595428000c03e22103049490051074141400e00010398009035881d403181a09400240f840b2051a0075807400b0310800e0b810074600d0008200f410702d064006840321004400d54000c404410415a103114002e4048511020b5034000366648030307040340351554540711281d0020303442c5602c07417506507101800068400c00d210b030000c1c04600715510a034200006040c0030844081680146070700d20388a00c004002d07080c0c080005031203580c0c641e401c1c50a21860542 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 245883309 1250 245882059 245882123
    0x2702180a0905040512090d1a07090e010e1303020a0501020406120b100c0308060103060801091505180304150c0b071709070501120e01060e0712050a050c16060b060403 73
    0xc0b80c1000e120008400180c05121a020a0f00154842940c00001401c40c1e001c0c035005810a01c440c01d400384040c1900719414400c041c2c90b220350b481151074010725503030042c00b401800e0309000040c000c038048001038a10b03880f03030300d01c42d10486105e4601541e5041c2681c01c50b0b4010b0340400d20030100c0c0d41545025004c0c07a1008001591981482010318100a150f86110003020b0144085c5101007411030340f1940082002e081072400a100c000c3c501d29080d0300c034804042d1a145950302d0000815400f90361601d070182c0b9802c00400a5052070f0410622040503004401103200f07015001080f400000c0c0c16100880c0f20740d82035107424598210000e0015250507000b0107a01c8241c01c50481804140c1c0c0244008203c18500c0304006503100344500c226004080c0b941000d0307090161141008407140e842507128000140d01c40b400d2205881b03000841088e20300564a07192011014485210000d0001040414050141c8070100b00e4402d81408540140d2042d04141c400c01c4085080c00c4508100c4444069548 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 245884559 1250 245883309 245883311
    0xa0807140307141b041b0f091d0108010f2003060a031e0c093e0c0a051b0a030602030a06050402040603150b070b06060a02011b03050901140906012702180a09 69
    0x350501840d00340c006c0e0004442018130030b1034110141e41074440c1c4481c44c060701c0c84c0300960145a07100b0081034071010091142036031542c00c0100010001e2124021000501c410a0a4045c01c09104a8011454100603e1940c12681c007a83c00400b080411030324800101000901c0341a21910342000c050494031504040016810000400f01e08642c40004d01106071140d190220300080c051b601c2c2c4440302075907075684241d040204413854508004190108400e1107001242d40940464881410ba10a82c00e140d036803003c103e540030004103043c0c0e0011588004110400a59680c5500001c0c040740c01c9a00300c0000203560b10313000c4507400c013004c4104000d00b82c01d1260a0500c0b030583d8506c0e14003000280390394003c000108044410714001d412040e079103128810103807245910718600074002c1000f150302172a80d40c20208580301084640e0491130045e0344080182031103a08000003000b4641c140d0040c0943c03041d0b0101080120001c07407000c0c12a40f6000015100411180000c129904000341c00c001a49 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 245885809 1250 245884559 245884571
    0x50610110712080c0106060e010816050d0902030f0607020d0f050c070308090d0501060b0d060b0a020d0806011709030406030e03031e071b050c0109080a0807140307141b04 75
    0x1000018903001150491401d511080b02180760410f0103010b040b620001d80e46c00c1950120b03500341c0001c40140302400c01c3e0f0b5911410fa0358418440e030352060a222820200c1e404101e040000c1240c1e03008140c03041d001808640c1c4840c0101c010501d000821120070b40181c02403c0000e00041c0e105054604200c5d55240c400e04000c0041e40d040c1d240c070700c140700c01403c0c0300001601803069103c100c9243c60312a042402003203201c0c0d5402c0003511951240300341d042801e02e440804a00c594040b01581c8101a40754010f01000c108040103880c07001c005401241400108080c1c2d420f40318072609003900c00eaa622010f503454920300362014003925200b0038403407401d420910402c07825102020b004402e00d0400104220580c84601c0300340c45040581d00c030383c00d01c660b41c04503a0050001c0041e8020107410300381d0b41c4908003995100c0c496190166064000c1403407408000440103d207a40503030f60b07540c440d90816249031048541d07c101c0100d4808030390090136000303610310ba03030802ea04601d00380b80c514081c1c40501079 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 245887059 1250 245885809 245885837
    0xa0806100816210303061a03100506160b10080a08092121090406080309030f011e020c0f0a0c03030906020c0907121d010e011a06030f13080d050610 65
    0xa40824000c41803440c030340300c08000f000e040c42074010b100100b1104041d0001034940d00710740b101d80ea004441d1a2100c0d202d02c900010541002ca046401c20540309a140c501c0741c4440d40d034030049c2c0802403c1c501000064000c007064280b018003100304d540b41f05100d01a41c52407200c060010b040b00500504841a510718000c20398500c000c40c8a00160703034511507004800b44042041402d50003444411600285492004602600004010408500304408a070021441d4001c0a420386980c00540201c030130764503200e4080f00d01c05801400b0700c5400e002c10349905444001d0405d1034094203a4050707501e032134000d8007001856004140c24000e060140b02901d140f502c814045140260050428020004030000341041010b01c0da110b04075000d0020780c00c240c0000c003102c0f41800390580c100400130951801d1a03083c08010342c07014a0b0f200c0c82c4040c001e1400c6030f50b03198400700c00d650018103040b012000341640304c0004100e40b00400840e40c207070b840043d0078141501404901d40a00401d0810f01140340000070b8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 245888309 1250 245887059 245887079
    0xe0108090a08190201020d111c0c0906140408010911090906060114070218010b04140a081b19080105040c05010f020721140601050f01050708090d020a0806100816 71
    0x488070b140349041c010b451003c000704a00910a100d215a000b502c0d1008040822001e20000c104580c00b24194000c2c03011030310041003c84207082c00100104207240c0d810444940114a80200c0041c1c41400303a0a043e9266041400d40d81d11403012128000007285c83c81e0289402c0001e250800c02c200f009050354501100060100b001c400d0400c01090300100d40a421941e0303600c242010444a0100420a5695041424000d40150291910000810f04c00611078144468034908860415000385614815029441401140381529641000f08501e40c0d0700c4039003641800c034000f071a00000003e9145003500f001c0107084101c1e00014100503500640c010802e900040d108103890004640540c001c1c40200b031a0105160f07184000c110328851910a4112030011130342c00d0403100c041e03c1c555107104100e001121b05100d0420006c14a078000d1244c10300c2410032144492a491014000c2c92015468803142490408101c071000703101c01c11b0500034005640103200c8003800b19901c010700c4060343d0410381629 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 245889559 1250 245888309 245888317
    0x1050a060609140904020f0402070605060918070b071a010f0305010f0b06120c0903100506040e060603030a0536040b0901140d29010e090a11010c05010902100e0108090a08 75
    0x5481644e85202140544d603d011144001420041c801c41d62020280b601002800f0101d40700d13840743c49424006a50081401c28031241c10800c8400340001c582845034848868100e900b041d24158031820076a522280b4036082d030741c040c000c40f5a58055440c5149001801d403080000780300690b5060100850f402e0703c0318400d0700d201d41c103000018a9141e94148040c207085c01510005640740c03040082d040101143c4d580194000c07001503c0501c4407040d0300410a41e01d10080d500c20307401da402049031000c61446400545503110600e14a1281282401401010400c03840c541c1d010048820413201d04515103441350000030311054445800f0b0f580b628001008041c80c4602c0b040c003800b1400e501e001000600006001032480e00b408011324400d00541c01080454240900321340708a115010803005480000e0207014194130681c46818016410011034100d4008401180c00d036480e01c0c0b2400040e5a03498510010600d0f540da241c103e43c000200042c200c038000740000720341d07410001c003010100d100c0034103c2d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 245890809 1250 245889559 245889599
    0xa1505010c150b03030d0204170d050307050a170106081f1419120b01051804020a0501210c0509030d030e060c030c13080105071e0914030a0c0801050a060609 69
    0x81c1161518604500c40030f018501c50f2668140000101c2c800c09901355409401a5244107070034840e140102114255120382c9440010b02044090000030301484c410b4000302002d21541c9003c00d44844001040200804280c0050300480c12040802610701c507048006001c017000b640c01c02150723514000d9020200710151a03468068552540002609401001640002c2009900041200c100350400d007401c11428014188034012030005820a0710003802c0c014021078004142e070360202d00e000010340d207203140354203428003040848107000b103010098443c03008000116110255288104010541001218040300052510303110040c40041400546107a121164030b413a103a885c0c8500746550910b00a41d030300c40440d201210404900002c0c19008280115010780390309540315150a000320840c20b22990190010b14043c0041141d84881701c440e9030742e0400502a24103480244d164501c9c80585070708100c0c2d4aa440d481485400d030200d10078040184250300e0509901403c05014805c00c070342d00d0001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 245892059 1250 245890809 245890823
    0x91f0306020318030d0e011104030305120a06150809010c1b1101021e010911010503010b030604090222050f100e01090c1713020a270f02130305060a1505010c 69
    0x5030701c0a80203551070f40c24109841200d8840c85407200e204050300c0428041951542004058880700312034a00396004c2d243e25481d01c60400d0f020303030020820214003d004174086a00c411000a900582203e4401c0c010015514104a03143c160241e9003034500340b0322418200314a00b40c00c48030300390701103404084941d4008a0001c241020b440101e181114010f01e0461500d06910000d2404c1c005501c6001c002c0e104d1401041a8200c0400541d45808244110010300b4000c000103241c600e001e85c032a1480c24030081001031a000d00800340d06200412151340010146d4500034414408400e0304a1039000d812000010046414116245c515100610034500110345a6104101443c064421a040c0c81011500e003030b81445d0502182c050050f103104241d005542c10b2030003080360140054104030101107200c21a903c0d01c1c222000e180244a00c140e1400070315824820308039100150011400114019001800b0a0a10b05840d800316607005a06d03a45d1b04014007820003e41e41c01c001d0700c0c60911342050b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 245893309 1250 245892059 245892061
    0x140706060e0709030606050102011509050406092f032407140304061e06050303030c09011e03050403020f010e0a02120a06060f060207050d0804050904050f0d0c02091f03060203 77
    0x292480103444030340c000c40841e207040030800c400c655201c060300c01102c2c003030842030001513520401a401c907010780d04a5012980311840c00d20a440b11070700840e40081c030468000414841030746403140c8005101c000d450010680b000020702d01505010f141110130070032005041d040741c4680c3c0320083d00320030203014041c4a241c48006858a402010080e60740c80e240002c940d5249000d01d04400207105507000303a210518064071001c6412a688105d40661b04003800640c619142c0d110200754581004440382d042000441c0310b03074440086660b40c07003503818980d280802c040c01c251038042e0070210060074464261f854580320480702d510000b5152032070358055546c611440010a151410035410800241c01130b82020000078104400034242412100b99501ba246d5a9884004020700c40c807005c0000b81c42c40100b48018455441c06a0300c00d43c120348900308807000148010141c03800c20350404101c80105400a030208158203155241b90303404050014010103180f16588100704c06074090101518865000c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 245894559 1250 245893309 245893313
    0x70b040311060708031306110a09090f0e0a0506010e071b121103070b06030d11060a0506040e0f0604061107020102060a0f06050a181505060a030c090f090b0a0608071407 74
    0x1011a49401c1c0c014030204d076170307103440d1071171101c19081c0102c1290305505c0c0c0b049083c4100921000e0b08c00c0c4a820340d403102801854121688060000b214640700281ea60f005c64000d0400c041006901441c8900054001907141c29032009810360010aa08180b00d103500a0b1507101d52211180b600d110b5000c0d40f40050b000e1400b50442d96140c0c0290090700030f10000503840184034545150034450f030310440031150a4810034134100c8072005480402403140c3d00c81004541083c800b900025403010000e000014020b16601c0c41074035001109001e00f4094010100744000e0050a0203101300213070075109080d16001183e40002d40d1514010b09144d443d036900d40b1505190314042c0c20480041400801d1301400580742c01d040c0108032489044c049000c0d01d00407a105140c0600300741c42e03089440040c030440c24010704941c10381c0a000040090b80403c4131a45000c9003145c07140c106e59000d08100c07103000400501440c00d0150707400e815001030040c44200010050140d61003140f108117082074820680e16034980d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 245895809 1250 245894559 245894569
    0x20090619050f030a2a090e04020d0203030403080a031b2a080a05041805070903030521010e06030c0108091e010912020c100f02070911120705040609050102070b040311 73
    0x10845076000002d000090004d0101141c01c50300c403900e030f4000000608802c01e41d09140c0c040c030310041c000115080039410050b03c5c800c503080e19800381c00580400700d40d21066001a00b1503000341c00885030300728007081001c05581e15100c2d1504034401021210060740103002c001c1d0201c0f400d106180e040c0020088140200f030020f000c0740908039880702840c0d0301c0d0340d21454003404541250040034240082005501280307416401441d00400307054948440c0c0350b01f0364504a1702c84c0d0158841d64012111603095046c402103910764503009140040c4a83e9003070816000b01401c01c041170109a040103400000d00004840200352880017100c5800c0160315032100047c6c550261004180103030140b1030f0000c0b0700011035000300d005081c0c090300300c0d68140075034003d06050324100b100e0034848005074016881403014020a500110320701e541c0d151641d081c9810383c1441014040111500d5000036008582008401d4028006030301402090002d043c83d00c1c1048240003180c042da01c00a0140202904060000d03215 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 245897059 1250 245895809 245895817
    0xf09140d0605131704180501120201050703021c0207030309050102010e1b01260709080601030503070b0604290102010e070b030c0706090206040909020a0603090f12031e2009061905 79
    0x446804a45100c00310750119409030020701c520250300701b80030b0103e1265a241e1003540d058601c040a146105185071b0011205600300c580114194803c3d0307455a15501042c5e4880c00110b003165005101d528290300c0d005201019642c00345040d68105007403d041140c002c107070400300007020700c200056009600d004036004a10b0090b80300301d184c0501c4e1a0a5080d40c1d891842e4401c00e01d03a07c40c4007001d0340e5510301c0c83c1c0d915801d21000d007150708107120f0f02000500c883c80542c0c1065000b84080b40f007243c10503c034643c0c4000c1094242d03480c1c096010f01d1819503028041c103e103601c00f0030f000c0c081152900c02001498030004200402e103080005003c0e0410a050740003a6031550042e100316241c0762030b00c1d03a81009000c40f0205a01c50003c1103030006190344240140a20f140d407000040742d03c0342c0700d40c0d0740c115078080038010001450b45466102039007441c40000210b403c00814400704880208410600e244005554800c800c2c500c104081e102940312030040f560f01010f18001080e81e440c80c2042201c041c06 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 245898309 1250 245897059 245897063
    0x10b1206150310020a03020315120d0503100302100203070515070e0f060d02031611010603030516060b030d0e01030b030106030b06220903030603020f030d120f0b04020304030f09140d060513 83
    0x100c0130039030145c01030b4140d028521800121640b42103000e0700800300201ca11481d1b9482c42103900c006221100f01d44a00041c0d6002550b03038966103229610707640012000520020b62100607840401d9180510000f0044d000c0c18540e01409403000c0d05190340000c00200d0202080ad008a0202e5031251054960030308660311040001300454490a00b030038881511031071100b0210000c0c0c0007814a54041106200e0001220740c1034482d6440e01c1030106000e00f40300104075054614542d512200102900c003800f84007098030065030745071003e041c07040024044403014940e1501a81c5040402d000150010f41c100e40c02400c101c0d00159079054001c0031200700e210304022003128a0034540c50500300768140d00f00034144da20031a04040031078100424035030b80741d880002d644005418a0794162858249500c1000e42d290761310804107031580044082000d036407096a0890000304084c5113a1107569012807a00c0c0548480d0501e03007495414840040d040100700030300580340a1341c6102080f00412004c030304400c0c442e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 245899559 1250 245898309 245898311
    0xb0c030c03030709060f09060215090f0604060b0103110c060604090f05070f17010b0d020609031015091107050a020625060905011107020321071401020705010b1206150310 75
    0x460403082c01005813413a80715000c040380c8452800c84045010302c155200303a0720310b03078020007001808850840344441c0c01780c0210014041c000440c60100d0050000c140b1070f40c0075003800301d2040140c000050413140c00701d20140c0c071040c062043d9924070038003040d06900a20100c0b004a4902c0e03140c00c1c42c88080c40301c804000d14038801d119000a00900d4803803003004a8156584898200c042003134114241c4801d20a000d074012a03c02c034103001442d21038007030306401d82c02408644103211408107010458a40d40780c0c040c0144941c1604000010f074502408017143c0448910500340f031072965400b03a50b95a03a100080c411503000c100c0041e40e0604010f030109200070200000200d187c1824000020041003805442d15400e140803182e4a8501004440810303601a000300f103c050403003001000d1903c0740c2c0b400d0b043c0440800c10200492103240108202414103000160341f2015407030801d00b1a990500e03030602910760314540c503030802c6001c6049a4002010340c0701412480703da100007030612010141001007a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 245900809 1250 245899559 245899561
    0x80606210a030f030b06210a06330c0305031b0f1209010e060907051509090c13091802091b03090a0302060c1318060815070818070b0c030c0303 63
    0x1169104581e01c3c0e540308079807000c1090142c204103210943c42000501e9a42601002105110740c881d0b00700242d0003102003400103452501c442000540c2c018103100440400c06500900000350038a606000804803241400c450003001a0740c094100c2c0801006403102500000410304c40c00030000c22100c4000e40c91262a980c0d0000180d04500d0003015110021150719013644541b00c05400503044c0d019900b14001407807010324100401c541c05c00340309484640da80c0306100082c10354548c040e016000c0c8030790030011610f6401507600c10103030045070790103401107a08182960a4020204680d61300c60380e01956041415910180d42c545051980134a6228510b0008204100c810000ca01c1c0c0d000f0501c00d5099410603121101081060702840b00e24450240249000304035081403240c032600b840000d010041003207070745c840c8803904003480c0c021203005101c42c49d010021004d5101506940c01a0020b90884034203d01100c040e59610581c0600b01400000261001242d0001c0069a800c80c5a100c1205e07a2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 245902059 1250 245900809 245900813
    0x121b040b0d0f051308030105060c0a060608060f1006080601030c0c0c030b060a05011409100c1713080d02120c0c1e010201050f0403051213020301091b060306080606210a 74
    0x2c00c2411180101e0600c3e04010500320104100c41800140c1c001601c513080d6420602040280d03803250940803070354464400d50400091050084200900495001d03184900e080d8168000b11400100542c5038207079685030a200c1146c000769010f8004a083c40e002034602c3c020b94041d0f4141075101c1e009000c108000703100008000081c0204e500c15202034850050165440380151a5981d18070906401d0f0b000501505041c0d051070039108109148a1a1503001040036496460310984015003c0303003180000280f5034000080c81d10603200805d1408001d012243c2000c03802500c07811046c03140303007a01500095005201c442000484454940140004542c0307020740905040a0f80554803103015500b008005081501009409031144c1d40580702d162400041190700124408001e082c21650b00f45003840d800561001d200714190f442c803030003034800280f41c603c03800119660540d01c03400405080030406c0c010510f000c00c00c1a00580269010808010104009401a402c504800f805c1e44102c40354001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 245903309 1250 245902059 245902061
    0xe270c0102070506090d17120f070e010801120b070207080f0304080d02240901090602191403061503150402070305130e01031127070e030c0402121b040b0d 68
    0x1820a001d80031149619656014402c25006000340d032507006007110000c07404250701211400e0f0403407108803410328201c0b0342e41e4003106103c4140c070207010a850f100c0401000a0b08000082900482401c0680142d807421307920a0042244030310081040c00000d010405844c000c01145000e01140019500011510010140d8a40281c0309042051241041e0200382d18004502482e03c108100e0221240501c800c003440c403807103c003411400b465036841c10900c0100e486840500504071142d4002c0481ca48440d500030124414040d88106180f010010f0001c0c40d83d0b10b101c0040c082d400d041c5819180e946070301c070040d60305045550361a0803500005054042507400030080882103110b500d59142d2548440c48051281c1c000d0000401e10b8110304152200c07031402041c198401c500035030752100004101107989240250a48a4502285584401c45c007945010310801d400360034203440442c00c050918000d203903071140207042d8412a010740185421071000d1541202e02500d60205d016544051780d02c0544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 245904559 1250 245903309 245903323
    0xc0302031915060614073f09081c030608030301030506011d01080307021203130f09140903070b0705120403050d062c0601050904050a0b01270e27 64
    0x85003000c44000303035140000c0d18483d0105072400b5607182c02c818540b512203404154840e20b82510490112446041e4165040f40101c8000d24101400c41e140350340d18440c100c260f02c00070304802c14000c5032007041c04900300024020360419240600001004812a000c1d0020a5140c1103102c082c00004004000c0c450b0010303180f812030b4000c015001080c04003081d00440c4179028005e98006800401c107035800f61400c2c440920351041c0f03103c00d880c5040300f8002004000c040340c3c0d100d003030507816504003000007560a1260f03c15841c01408032130428601103598545030b1041c01c2c0010305500451001c00c000c14811825100f40c1c25652100c90191305003810003805641180102501880c00c040d00406c1400d410300041c81c120000e58100702140f070b824803113002d104038000c0680e81089030910801c800e90b600e5004450090040d2071000409000c1640010031030501019220000d0356500a80c440705001c10700001c048802004148000ea200d604003202c4441010101c080081c010640045e04150080b030302d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 245905809 1250 245904559 245904563
    0x11040905010b03091603050d03051e040f031b1a090132060a0501050d050c190302091306030c1802131d0f01081203041704080a0b01090204030b0a02070c03020319 71
    0x5481d8100b1805c000ca03d644a0344c0001071441c0c201481c2d84400a00942000b9000801d10008507203c080d49110301240b58412107050341c080d041b8072490002e142d0005610801c00052881c141c0541300c080d1101041c0000b4828a044481d61100019122100a6000c000150301010800458207224800341243c1041c8003c03c045040c6d5500205d5428a000c41c0400111501a11617a043c8031070440080e0050900921341034000004028200b1000160b00040c40600300640300140c4501c40d290a0003504191080400c84403458094180003003035144010700111120007444500080401020101a0051008045101614003c00b0814400540982c40d040800792680c007900e40e54a960034003003102c01c4c03094407030507041068a02c07014011080110360080c06040d04800300c8084030041441d9034820b034803140090708004442c0d010020101025401044c8208055040c48d0441e00c5103004c40700080c0c07000306400c1c3e0001d80c060030025035559031002182c0040a5503080105c15021001001c400308007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 245907059 1250 245905809 245905813
    0xa1b0e031204030f060c0801060c140a1506170102071109151905010206090c10200a080301081b010e131508010605040e0a0b040b040221070501201011040905010b0309 73
    0x48842a0720803142c7c079040b51915901c191101c82e4a45400c4640c01014425481034016110480082058001d042a04000602000400a00d032052002000b044401300021a0b40100040e0010131322002600d04018800c0310740c07c03145d40300c04014840075400081d020750041e20468a081d0301d0000d4080c013a007100e8003a02500c002e50354400381c042d1220110291709a20103062000c0b500305a20506203003a25010700c060307910f41c460908040c01e2401e045c3e000c0c00c403140d05001005102006050146132136941d100040d90144100090028050500003042640100503004d40003400640a81040e240300580b40344009080d0384a1100c640a020a0b00406024600340400b8000ca91400070301e5a0030182c01c6803542c00907455541d1807201242c40604140e90044000042d110725042011044c41003008442c0200038862800c000076140280300c0d484d40c645e00490f000300310f45c1c1c2c8002146442d020218034800107500301d01c0214075455805039801803030390306281000102e22186800000d40c091024402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 245908309 1250 245907059 245907071
    0x30b040501050103141603020f0f0705070b040303020322120302060405010c0e0d060c05070209011d071103030a0b210709060e1e0a060504050702060a050a1b0e031204030f06 76
    0x107609841c5e0b0221032198110700880043c41c00b408000c5e11740b1202120b441c02502c1c00003604024425500100a21207440f40c0c000748242c1080410080c3c4001090760304003040c1490314648003c0e40320b01594000f2075106100060090070200600e0300240a0711190220a0b2003400d18180207507941070443c2c0c03c5030380750b10381802103015901480041900c5540204100408682641c809000e00705103403041003400300170b000300c00040e9514a01c1e140030f0050307540e0035044894900502c0c038a035039000d410b020920014000d50911480007104407584844210f402140d03000c0b124012802d00039003c01c0d04a2554150704685908001c0402e5401c102d4408001c00e0141c5910b92440217000881919910310a51090840c07411029202e6017042c5d12480c250000191140d0314800718098034403c580c02e00040c2c00000402c440c0325020700c034454021034101c0d0104072040c0031011603004610402c0c0b00720300784174155417850710b40d039410401c40c1d5100c03080881c0503481d10340c0c82ca07014903240f001503411542d441c2010b07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 245909559 1250 245908309 245908319
    0x1803020102031608010b0405041e0e03070b0a27020a0e0702030a08010b09030705090714030f0402100206071407050a050304080c100327060207021f0f0c0f021207090903030b040501 79
    0x41680e040e81d0080d04d11610301448c040c00c110041919003190000c215400010280b00e0080388184d5420420740d4000d076581d5401031a201c038030b2000003010f20985620f002c1d5581c01038032080300c000744188152562208820000d000245200c0003d80c0b200080040c1001001102c95001c4007070444035405440b010196600c0b01e000010030302031000781c42e40592110804101c2403030058002608080301e410701c03000c203403214800a41c40341d0048607a2895068608103100440c2000c280d800041441803005d0442801c12490003400700c0f044d25a0a00d03200300c041070340b00c18410144801d80c03400d0ba0010880b50b4480e030310301c0a141c413854885501c621842c812100044030328000e009012003501760b00314040348a148503903480c0f40e0004124040d50200c0d800e100c14030058540429500828812119280c0d85c01d0060741d0083c140d261006400d002c010000d05030900040c10720b01c5116036294125084014042c100418514180781640304640650800c0030040500d42c055201c3c0c1d10320036090b1028440b80ea00c031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 245910809 1250 245909559 245909567
    0x110f1309060b1c022404120f15020316030b27100b03090c010c060204080105040b010306270206030601030213170616020a152c0601050d030807030f18030201020316 72
    0x400800385d00028504164000b440d142003280303c040b5568580e042c1840d8440903031400c0961415001c450750007054100000b4072441d84d9480c2070401c00c401080d8a9484c0c103007424104030b034000700d8110a05481d009214031554072203008d90401d510110b802c06002500100851b04800240d940015640e40320f4008220380c120710044900c00d040203002041250070503001150405505e10040d50b201d50700380f0000c55041c1c0c0a000d418000c901400880e00d00e5411800c010044864074070408803a05421490080003101c0f5220210800d50116095601c83d959440103801901c03400072140d2a01003000300106041424141c05008070b101c190480e1150b070b8511900403201141c0001d10b0001d60700c601100e4002921407418041001010301b401310302c0c141c5400c640a81c50503504144200744200c4180781410799000c00800d401040100c3c1e00d800075440a0301c019154000c0030b0914010941c80c0d50100303a22994507041401105034902903010141024107009000b90001d49442281c4240ca801c880c191600c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 245912059 1250 245910809 245910859
    0x90d051c03020c15091c03050702010e162c040507030317010608190f050721020301050d1b1a0307080a0903050d0c11060c071202010504110f1309060b 66
    0x4450001c00540070300038609445051300400d0740c0380c144240000b0a081031040108814114242c0d00d0208090034084d030b01900395000944100b0319035101da501d01c003000031500b06840413550740d403104108000c0094580c10320b032a182c007030b100c400b070189030309100030000c0020709002140d000c2d5480c420710079003107074030740b9144042032041d000007501c1c801c082803214880d00c14142d003c0f500741070001f917070400300304200c0e0985108640b00740119140b0802c04a40903880f8882c402c808003800c034218610360501c000144030b81015200941500210042d100c80001201c281e200030700200c0001c0d41080c100c078070020600d0340c4210b6042001820f90004100c01d40001c2c0140e100c09a03140d1605410030812524003c001c220b004820f0081000207500e4030301901c4c040c07003c2c0303004240c142c0445e2350f940c0300f42c140b62503012804ca035440c0840e0715000c1000045004000c10703034856501110820000c11000300061020611660213480003464250f0329400c2080c6d6501000082e01e0030b680300191100128041c00070034013 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 245913309 1250 245912059 245912077
    0x210020607120207240207020a06030b13140f090a0c0f1403010c090302011404030b040506010504110c0705040f061d01170c0303030c0702011403010801020403060b0402030411090903090d051c0302 86
    0x14148044080300c0c0f805c2c003240a000758500100605050742a00040c48615080c2d000902082d9690b0402e402c07800e20703c1400b415211461801c3c054107031150800c55a0000040c04450740820400100d00f07a800b05000c801c90450b040b40c000400d080c1c55003607451911146104640d0300c0428a4076107800342c1418096030404014948030b65034407034910303001910310602d04101101c0308a0200310210008812107003450080e8051720080c0807940c1003200340400c50711842d694400d011414081c1c0c20071503200044090660304242c0300031940e504621b51010150000d40c0000003200380030140b80304400c800c105018102c0e07104501d070104040b407040b449030b1121008072040360550010800900c030b860151009092481c8185040c12042c000940315400507042030308071401c142d4001500300240401401800e4803101d00f00d0b811440c600307080d07075a003c00381002507206004100280026220071414005e65440400140a0000000e018980140c686c4000355221101050030001c0320f60080c400d10940704001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 245914559 1250 245913309 245913323
    0x106120b07140f0f030a0b0d0c060c03120615030b04020903030406031104030206040312030509010506091812030a020a0908030703050909090f010f0e060717150402070210020607120207 81
    0x14a8100d811039008a10b58241d0314801c60400100307819605007002400f0140046081076120f0130001d00700c40a481b449802c841c4200111482580410041c008010441e90607090a00600c4c07207034a07040d50005007107007641000038030300600002c0030303903440800c010200c450fa0360410a03a500c01013000100c1c007405014a404d6442408180601c0e8080d5000c034644503414079503030742029500d90004589e540b0540003140c0300c11024a40140403905405a60b8111440b04000d11861030144d0200f040d114004100800700f029090340d41440c241d081c84000248010003003c1b503564600744c0780000c080e510440103800040d2680d0000580500081709940509074180d0f13030320749020740401c1081507016028180d00c80303d010b580c1d10102580001d105198448681e0440811580e541c0c003d040c1c00d100008254200744040c00e600b00904210365500f1903404140040802600c5454801203030003800b4501009410404c40c5203000d1480f600001c1440c40ba140b503076a04418003116618003004d0780945075006000c0c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 245915809 1250 245914559 245914561
    0x31a0a030302070519170123060102030a0c021201060305030901021b0a092d150e0702150a200711060c1b060f070b0a1802010806100903081207020106120b 68
    0x3500c2c00d5108440b65150b04110f071000141c03980d81118a00c214840803207120b1b075403018508918049822024240e0400b90301c48d0f002850448000b035164070405240c02c04222408084034115a10091a10381d50b4000400802c6095200e10701550f41f580240340141c00f600c10540701014142c0b1000e640e98140704042c041026492034070b080240a80748071910700f1104106e146030058400150600400d0074910000007003504c82001281200e00b265a80040d1420051241004820343d00051007602c00f50b2402d0791703003d2070703a65070304848024600302c0242c95031310820004c54020303c20310001030401c45018104500b450f81003001001403d1050009050064100e1256060b507084c40d800b204400340000390903645400c11400401d011640201c0044803540104404d1160703101042c800e084515601c45a8049000010b40001c0d001d180001c004038420100c2c4402d44050610452540c401154840a459242c110420041c0c0c0ba4180454105005619200e40080c02240c400400c10310a90000072412031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 245917059 1250 245915809 245915819
    0x1a031e010e0d02060a0b100c0f080f0f030402120604050a0f031808010911091b0702030c0409030915020a080307050d0608031803060f0103050717160303031a0a03030207 74
    0x8010041166601556515480841c101c814818604541c1a55010300b14a140442c1d891044403840c0c81c465000700c44800f06802e4a42d00203094640e65600310366a14002d1002e0f250007090303403181c4c00c5800b00c5c011012502040d10180c00001d103000e10320880310400511002d60700340740e90792070450300533000343c2c4408d8103000070424048a4480290280c0341414200000c030100003004d89a943c0056181c1e07540308000c001380a950305900340395410840c0d0040da1401e00c00ca58003800741d014540c61001e03281c0040e00c8800c40d80d003040136040389100540b040c418480c5604015210302d44911480014001403001c0308145840030540781d87c85544125407130300710344403100c0864140d000000c0100d504d43c3d84180100d10824100040c04110300200c6020035443c054006060500078060074079010342a040c001400001c102060071001c0e0b8100c415504d940c1e00c0440314040c40d15107017010780411500c6211012091642c190050004074185614014502c21a407040c0b013103680c454400580142c00070402842 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 245918309 1250 245917059 245917093
    0x70605011e052806080a051e0a15050411030f010b0f0304200a09020a021221060307030b0415142502030403080d1b0c031d0604091d011a03 61
    0x1202d0444028040c5480f0040c00d0907040c03d9100b50454408200d0030010040c40201a0003015030000162451070803c00c0c07182d041305888d0a0281c1904030003a1034404416250b811142c001e4000c01000300b06101420b8042c1c201043c0b40d0007503802c2c443c15403060001003209800c1008942019103145482c2c1d1035a40c8035101c1c0050b4000380100e101000c42891007a85132070740c950a000c0040d0004e54801030351400d02120203131a016101801e07200d082710034481090102d0462201081c0c04501e00342d1400c45a46401c000f0f42880c002e600300810055003a8240f10902141031480081c034107070010100b01003185800190f1882c0c2e0121403500c1d0701c24400580c4103050714480048000d500700c0f80101c81c100b507202d9483c0100d07500001001c0307100c59034514030840d17501c44400240800342450b0070540392040b4141c07401800d40392003442204400c162120070450907180d03803003110300070f000c40901001800b01404040c201000405040d03003441d82020700b8441c0b00c0840b1a003c0e551944010000d0100143d9400401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 245919559 1250 245918309 245918329
    0x506270f1005040c0509040b150103061202060309010e0a0507080106060c0f1202190510060501140f0f1608091003060f060305040516030c0e07020312180a02030111070605011e05 78
    0x2c580180d101300018a41d151032000f2405036229142e0f00660f80341c468407204800814400440c10181080b81c00c100f80220880d00d403880a0b0143e6000d80e480e40c40c60034880c05450503d145000f5840b42e03080c0c46051050124000050f035000074001e0141c181e0386d80c0121a505a5003c02030803a6038180694000581c1c520659910180e150040d030f10700103a47c004030061115580300c1540d19030005802105004043e2040101401d030900301a00c084001140d13100c41402039204001c922580051402c80020b0f5110503905040680084802d5024040c507140b0880d801010100c0e02403000c440402a0302c0d40607004032015105a075544c0004940b0f0064100c0151001a00035107081c018101905860030030860283c0145000d45880d0520078902503121004180040ca1201150024030406000c00d82e0060302035040b950a1040d08241401080c480e4102450138000071b41c50360ac0c101c0c180c002011918050041c0d0350041c030040100d0703070345e410350a071030b00c40342a18113411003081007010320030740c50012049 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 245920809 1250 245919559 245919563
    0x70f0506071a070306030c0f08060f092815050106120b04060306060e040312020f031501050d05151203070f030302360f10090302090c070506270f100504 67
    0x1a03407442d001103550625010081c0c8079500000c1c0c41c2c41c4c090003800306520301798005143c0443d01c03070641481c0055107038550304007401a0740381201071404038604080c20022842c45801c4620343c00c284d1281032218401c001010301d811a00d00c100340c0030300000d0040f2440b401e8100e590944520107461365040007180100070003c02185d100756900030100100b0014031640004d800070b1f403d00d0800707092070308000c0c0c5440b03085015841010300401c4840c0c8150084000d80e504904811000944482c0380c90050f52035020341e0303100c03d407a82c0c50001001214000c581d02da0a803040c054038500c5007800501100780d01c9118400d00036008d03c924103111000284643e0007045055809080418228080003c4d04545507003c031f9038540130030b22189000010b240164030010018011102070040c4082400043c1c40e03034059100203445a0004000601180c0c2110212007940c0d601009850151a01003c40c1700031640791190804145500e044600701d2000005a02c2d0340002d018006154031040d01da05403014100003002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 245922059 1250 245920809 245920823
    0x152409090b01020a260f040306140124050706151a070b150d0212060f0606121512010207051606080907210f030c061a0105040509043003050108070f050607 68
    0x80010122000018001d180751b14003000d50390742c2c40d40c103048081d101d40d00c0420400751000c40041000505400703201540e07501c1c100c025040c000d4000f00031b6801e40120040a401e143c10006000210642c140124095442a40c00c00d81400c020384130242c614001e02e40300800b044030090200301c2c074030306184800c0e90640004040f46039150540d0701041900005090300e108a601050a02c4010640300e500c460740443c054603090f08000c4081c1290610101c00f9040418810b4600c664a0315030715284200783c00014000d0095588100718a445e030b81c0d4400c2c02c499004121a9410081072491080340401d000e414080c00900d03900f400d00440300541680c603443c0c100320046a801160024021710200344c50b480c003030348465084681c0c030704148050711443c018000c280d00902200d40000e80e001019078080d90019900c4010301c1e526480c044c40707032aa460000d1030035111540c0c1040d5582d585003032310540001c2265000d000d141d98511841d41d03165130750b0180e40e00542c1c4d00c43c02403082c2d09001000d041e0450041c6c82d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 245923309 1250 245922059 245922113
    0x11010603050a0b010303080114010f0809011401140a050409050304031b0302030703140f0a0309270504060507020f06010608040803041b0801021b0304030c0504152409090b01020a 78
    0x91207510704009018110b90741180c4030010070070b00d0380100c13205005124144a8014500311000020800400980c0c10402d03c10340e400030072008402544042c00007858000c4c0c0d03030503658482419643c0110a02105485051450b0010800341007a0240380c2c44194001c0055044c1800d6035144042d2868401d10b12044641094000025990403c00440114015491904154254844103040c204480d6400c1c04c07030b610404500002030740c46660001205c9040103566209101c052401d604200001c1003403000074100400d00081c07045662001d80200195002c841340309000105982c1c503034030f0910070342010480b46c400040c0800c8214005641c00761040c00b218080c04513a00b00685c640340590032002140c1c1d03011444c44607811045c4558040c868901c07004609261550350fa5806080c410700440d0b00a0b500d40b0b1095580e0320240c04ac083c0070b0102104020341000d4a001014000e40c07841d6503841c00a8000364000624655074440c5a140c040c5c182d010b0640c1b00802d81b9803150201d50314007400300d0031140d09 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 245924559 1250 245923309 245923313
    0x1005090f04111c020a030e0d0c031202040b040803090108010f0305071a07060c030911151e0906070501050403080f0705180a080109080c0d02070501050a0c0503070b010b0304022e11010603 82
    0x48100c03180c3c3c1880c2d00107071070320074001c001002c941d0415140e01150744500e0104580c0c9400080d2240681e03414685200400c091000e040003034040c40d40002d02c0c01901003004101f051010001d051040d20a0361641c1c250f030f070380e0b00b42c4001c1340700c4500c0050941d4206d00014814070729403800104a2407070240c01d40380341c840d075581e9205c21a181008180000b0b80d44941070000c00140308440240703000308484501c800d0000c42c161007000d00c50100c180800710200d1660524450442c4c0070b5501c8020004d110b80e4440d03101d42009070181004440c00c40001e22072100250200c941c0302c286500031461a500e143c01d00000594110107420764006031a4850306030500040e84583c2401280b6041b48200d0b205034590001101451900303145003654000c0d50090001030101c5d90303010044e01e560303014624040d9495016414800d01354400e8500107000304940c60000b0401220450086014910070b1320840f2130a007118031100c1c02040d03042110364074880364201160203540f00360b1010f41b41300c94440c00003d80c940d86c2d0f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 245925809 1250 245924559 245924587
    0x120c030216050c120d172d0a0b0102030a14090f04020a03021209060601020c0d140303100312080103020a060c050331060212030712140a0b1005090f0411 67
    0x190070071662644022508510f81c10701c0e0003111801a10803004004400d945030024142108102420444658450000d00002170450b01084c03400a018418a041015904c0702038003024201c0300d100c0c0c01401e0250702c1d51594400000c07110015101e030303212003082e01441082c0400d6800b421850380d0041ca0342410b0005540c0c1ca10003003d0642140d140140d07505001c60558082c004001c08800040c3c00c10010003c09076000f0a03441c0780b0705000c56544141d0300840c03400c0300320003e559480d0f50360741c0700200030807042c0e084515200c01030b6070150742034070b0f0000070f003040031610200309010003900705100c0c500403c84140500030180c0740611503002d0b60300304200d14800a41003c1d1184204003040000480c8070121303050ba80c4010050040c92002d00114020401e49103a607100c003030105030400441c04001b01c090034503070340082c910300e240383d0307070f2160604220030007001810f210030500c2e1059150a42c80c0315058050301c100c445450000e005003016449507010400140441042003403414000c00002039948a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 245927059 1250 245925809 245925847
    0x30203060d0606060e0109120803160c0602040e0f010509160f050705240c040f0303050304080c0a0b06120102041a0705010608030706020c010513080d1d0709021c0b01120c0302 77
    0x10350751740782824203020001010401c007a4466590880a0750038200480c0c411000c580d40202010030b094282c0310300c0c403c2207a1076522000c02400e0184086400b140d0642020145030169192001c040c8a507601c440410040c45c0c3c040c1c0d07001c81c0d505002d110343c441c4240070344e0100b182d01c61035080c61414082c45490b22030078440b441040b03060302d20380e9040f03c0c41c5102c44d01d00352a0300700e000d005883e070909042480800e80c2881c03d01015061110100000301000341000882e01da403003e9901361504038030940b4040e1400d50003501c8083c49250528500300304031405100f56422110b500320801c1080162640c00d9082c2da01440c0c05036015500e0b000089950581000201540343c440c240c0107a0780c1c00010b005130708556000e0007691488070923107840c1021804940591b141940d002000050300001c1140b000011410004411080e0240460001301d0128a901400a440591004504030303142d6008420071241241c582d240071540b106140e20300c1e1000c0f07500240c00b00c0800d080052500d4958a284110307440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 245928309 1250 245927059 245927069
    0xc090b0a121b08040305030a0207060f0e010b01110a15060e240901030201120216050708030a03140103230f010603140f01291c03081f0f0303030203060d0606 69
    0x314000c2410062031445440401d03025207010191640c40030740b00500a00000c0c202504204000c808030f0a680d886038100c4141552191080154035031800f08603020b401d440400394040d501c0c00309411900e5004400e041c802024800241c07500100c0f69403925410841541c030036009c283c1c1c0706008035521080b041c2007030003410850341594061003500d81002010404525003170040401c03500410050740c02640740c010b9480f076800090386480c0c1c0480d05a45401c04084060700300d1081c0180081c044d07801000500507425940d500340f050707030040c0880c0f070323141c100a202c010b00c4800b00400310106203c421400c80d8444030500280c807105682c403d03005080d28403d81003550080d01035000d05104000400034072100d013500c2002404480800c0e4444850a0301400c044d04d01003104480d40001030341c800002094419642c0e1003420080758030b081c014007000040300e016440f41e640030100c05020000070890000c442405440e2060340381941d500310040d40000d0b100c1a0460041a80702000455502510300030740 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 245929559 1250 245928309 245928317
    0x4050103060519150905041e0b0720030304080705070801050405030a110607481a0c03071808030a0309171314010203040506030a061511100c090b0a 65
    0xc10001c50360000c0b0b000e8510402c0c0d48520340221038548101d041488130031190420310015842ea1242812840c03010512042007800d01c07829652030800c035000c4030190064203503685600608401d40820f100c170480c80c4218004aa1042c80002c000460303000042081d14410740c29220843d558411481c25190142d9040b00c0e190004205c2c448419407050f0300da00f15404000040c085030401481c06401901c1c00710f40d0550700e40c083e18050707104501c11240900b00c8407810041c40041e840401d045560076161030800c503000d03445012460079807010710754518001c040700c5c03a07020700e10b440c0d04030144c40d01d00340c20f1480c0c00d0100a03020001542072080c1302900d06003400f038901150030140c0f481c020303200c00360b202240b0000c50303001d000c03030740600d811a21101e045e202e140d040140c2085a11006078918010765001c1607001000004100c45201960880700481d0003803807003040b012981300001c2d2058110720000840661103d4000c03c002006600321803000b00d25800d00d0010f19880c0c90b038100003684244134180200d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 245930809 1250 245929559 245929561
    0x904050402060405031b102a210305090c0301060303080a020306210a0209061203041a040f030507030507060f0c0206160506070e1503090616030b030703150f0e100c030b040501030605 80
    0x60305042c030085c4601041407420741b00c3c015030244083c0da01c0c5544440c82031039102e921038220402610411401c990300b110707440c060f4040444c500080141400b0cc42c0075106010740c03245480c040c181405a03074281c9605884403c01d07580e500101c14002d4100603c0d20b503000b0314840c0e0740300700e2024130415620368880c40c4010305111241e07801804840f08014000c68000c1803515411170303911102005840641d41c20510713001100c081e1001922450281c1d4105c000a005c0000000040200000d00c41b02120b214070141d03803007207a6a04007074511030041c1c1c4203000070805401921005141c00030040034009c0c1070096004401a041e03c4042c50940d00321001d1010581000d02c0540074544031040c58905403441244034510320302400030b83d4840070090310340c1c0e011554026074081c0540c0a9000101c08032000340484080b02e0340c07824504065016940c03140c42180c6071461002d94110a401014048003541c40203260808220450300c0061554200840805070f035402c4601180e0f40340c0c01400d00940c0585804501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 245932059 1250 245930809 245930863
    0x1c0603060509070b19020102040806071707020c010504060507150c09080f07031109090708030a050d060e090a0305030a1e0f1803080703050c04031406070201050a090503090405040206040503 83
    0x1200d001034200d80d03680d4043c01040025804103002ca444458040101501406185400b0b9001e8021900090300500900c3c00b08800c03c4d03402500c821b0b00e01120804019551514a016601e83c0780340c80400c1d000420401003448024001c40080c080c0c40d100b05035680c070510200039074104603041606014006515640c040180c05002c012900c1e039604120050306c0060318540c0c3d0381c44045142c0c82c41030302a4090000048040c0340a00100740144180c030142d0740e0350760107014020140e5201d049488402440d0100100d404900e1084191003040341074000d10140c0c0362601c00b550b29400042031140700603240c0344400030b48150fa1000220126860030301041c001c8019040c03006070f441c0700d03284a07480c44000380740f0008690f20007810b03608203440f410000342e191121859038042d4459604003a00c03c00684082c003039a6940010340078410350305a80208040c0e1034007641c0b41d050324009440900075920600c030604d000e00d001e62010b50843e100038611803419681d1004682005895138040c6024208035100100b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 245933309 1250 245932059 245932061
    0x20a02010902150901020c0d0c030b0103050a1b081906020d1a100e060316090e090c010311090a03080f07140303070e0f46050a090e06060904081c060306 67
    0x200043c855050281070040d5040001e554036441029107104074036a01205d01441039440f964006150008250095503071a13040c644da039203c9001003114a500742e801c410540c031303c2d07070030141c0c0584144002030080300700c4881c190104020848800d42e100c65003001040718610745072090301a01c907995071200d88012900f4041041030649100c03140c0070f02c80c01c0c1700d0000d11a5203110440358405403001c80c482c80e0710b4000f00304450f8507915402c203086e020448401c1c044620800604c0010b000f07000d90b000d01c0030442e0040418040d004202110b0b4100c002c50805000282580d0054455001e084580d203081200d81c5c0ca0300d90300300c0a48844801190000005c0c800d420364046c6188400420a4032105030855803940800d04070115010700c240c58a50b80c42c07801c82035003150700380d5440c050400303040048954100504501081814441c00d84215626280040c1c11502406095100e0038198050460750b0381304000d0100200004004035030000041106c00c440c2c450801900003c6901c1500008500b4203501e0290 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 245934559 1250 245933309 245933329
    0x203060f0708070507080c01060e010305100e1009061407090807060e060a0f0507060509010209030d0201090c05150d020310210525030b011d0f07090b090d06020a02010902 75
    0xd004604140801005a0704004069001495460070170f540341064113001940d0b000350a400385d0654205440040c48502d10a05107050b2800f520564258090501c80f84080303455201351000030b82c001c00314521081c4840d80c41884403d004440100c0c15081c041501b507a95601220440080388400310300380f003400c104000c000f02400c0e07503007046c507010a23042c00024168020306548204100e50546419a1b03035200307200303456449a004c6020300035401c0402d801c501079004900c0441c02441543d6429040c10300c14015512500c8d00b01c141e0910441c1010309000c040e60000c404030429a008100440b0b4844541c8021441281c690b40031003542070619100b08180074030000d5000381078131008811004a000840c0000d20140c0c0980310300c2d4860140b0042d80d080c208194809803491881340000110b0990080a000c00016070307020016a9039955155410f0015051300d4a00000d42641c0d4144403070001007000309080b030001400e18086407a03540e1410309a038441c010f0440141d440340001402c44c20324072100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 245935809 1250 245934559 245934571
    0x6040627050708092e09060606140f03041401060506030a0506040c050a0203030a0b0a081b090c0301031a0c160f0507060801060210053411190201030903111603020306 73
    0xc4182e0a000c428190303101000741c95003401200d620105c5c0a1000302079410004448904024030401b810750034944006d11a03440b42d080810701c400c1c403040904100008884003c60b003900745c4c60450f111070710741e0319404491245104945d966160003045641d1403002a40c8140702000010806103083e80900042c1c40c511124078060000034010744071080e8010003a40e91041101c01c0c00100918180c00240981709540e202000e135004900343c0c0d8a0140e00c201c4070001d01081541d01051903119502e84c800c043c8404d200c080c000f11940501c540f04103a0131101c05c0c0d04940c071948c50f18142603a0409100b05c4c00142141141d01004610005081003410300c20702005200f18145031226614008000e5250301030802c503010300541c0c8a00180300d41c00e41150b0100b0a0441030082c0d28140e080d5540702c140002c82910300004210181040a4aa80c0008401d1000c006040c1c2207851583c566006401505213054100c1c2030012145251070440c0f01000400c00700411051000301091a50040c10b09040c1f0280c12 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 245937059 1250 245935809 245935817
    0xb04031410020304020105180f090c120105031912030207150203090d020a11120304030602490504020103090204290402120106050f13080601150302030717060406270507 74
    0x4000250ba0084140c03030381c03402c800b072354a00141000c400184010900b80d001640c491170f02ca0601182040c184041c00620041e40460102642c81c0c0007016540c0071040002c1e2000e0851314540700010344101d18130400c2c450282030250821aa59031140341c1590f04005a100c001c3c0d000c800c018a1040811031502102110b0014200740d0740185c4462a002000c03094440c05000c041404014605e403c00884000f10340099007103441d5491741195401c2420203403e10140e45440e81850300c5191804100c4d034021840f58051640c404c507a1800c080e001d03080090081c1e0505585440140150b16107024040c02c6202d46e00d001c800110704081195031694903510003a01491042c400c05114209203104141524554100341d9240c1d4045505600c040c414120080000100740a0001d000e810004485060341d4602064007100301c140301c401c400301c3c007049030000001000400d180c250048441c51684d00700e803000c3d101040c500d4031104600d062004d82000c26200f00785140c0c110002100500c80c10f5006296498 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 245938309 1250 245937059 245937061
    0x323090c0108010b03040b0105060c030409020d0507031d030331140d050f03010b030604021605060403020d030c0f030b0a120b19060308030103080a02161d0c0f0403060b0a0b040314100203 82
    0x1f100d42900005015143c0118400518102c41c1502001954004c01c4c130000c080d59607040110340c00c0301070001640c105011030f045c0084c640c15482c8411402c0014016039008508603510011900200001c100030310500c94000401c81e80c007100064001c0c1c50b00c0307000b081c8035207400c03000000d441d103042100d4150604000e01403220380c3c40e40b149070007102e0441c0c003081665500d0b6158540000c1c024862590024110b11841d44907908108020a6213442540240c0a6030312070400118141c1c10742e4803035140640040c0050000c07100b40c81c0254802c2c04084400f030034801015484040402210507000c00550740840d03440c0400240f44401da00c00341c502e03008070b0010f225461844d56003194500060000074003050020440d181c506100304a4880710349501001c40f4601607940400710050042102008100b140010004482ca038014088424601101440700e140602c2c64542c0c4004150107072040d030340400d88100c00600810b0103405000954003800c111502c2c100761481191900d181c5190300100580188 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 245939559 1250 245938309 245938313
    0x210105030309030d111213030501140c04172e0f0209010c0f080f040f06030f090507051203130b0405030d021c03020304080d06060503161701060323090c0108010b0304 73
    0x1c92146803500c0d04c1d0400d20740c00c042c8410000d0610f0103041031b00041c003c002c5100d100c1c20025a4420040320700900c02000003030f18111001054070022983e05005880c00c100412904a4161000445140f101300f41c03002100b403415252401800c0c4d481e241d005990348031405055400d40e02c241f10f6a40780180c421843c00031031070000380940060382d10151201000424060510011070704a80e85242d040306142e65840d126040c100318045c0034060b080000b89014200115182540300e1880360640050003070890601c3e11080003c0c00c10b0081c415000e9000a00056450125510704d41c40581100481140c9603803c04041c54030b05014090113004640c0401a560705506101c1050b00000240f46000359881da1103045c044054862806941c1c1a2807800900250180d0b104c800b0318042d1000c2400110b43d1101c5138802c0ba480400d101e0a4800d05d150400104003690090340f0021b20342c28000e0610845000000c04c4140c0c0d0201120356039069080001d0840580da0b11540003805080c192520702c1c04e5003016 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 245940809 1250 245939559 245939563
    0xf060403051510030807081e120105090601030920010e01091a0a0507080a030609110f040b0a0201090f0b040b0c0a050712090506180f0913080d06030821010503030903 73
    0x40c80400c1d55a181c81c501190000c0d030441c07101e03000b86030003200c050394078030f101c1c64034041c15844003080800d81072441c0d101800028422003109c4580740318420702d02c51a4203000c2040440031000d0038090625940300345041c002441c5c1401c42c196204040d000c070710001000000900200b9010000c0c070b0400500e04014886415992000d1449940381d0000548603480031301d0549241c40b660714060011200403599011496142c0c02404c25903402c48003d00000c0340c500c0f52080c01d8010061140c080b02001d000a2141c003140e040901000d020f9440080b4000718603440792082100751a01c1910000440d0080005001d0b00b94080ca0704801301800c0f207072526600c803000414034083c0001c01802200321207020036080b84502c2c41c100c05040700174034003995800313862030280d080104c5860050051442d03900403110b1b07180c82d400d6070744034218150142c040c0b07080c1590f680125074060b9514820440d502d020110202d8002000351458409008007c880c03044403a9100200500503070000c1d1180c2c0c0200b00c407100c240c40c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 245942059 1250 245940809 245940823
    0xe1216081f0902011404030506061f0c0605060f0418030813031d01020a05100f0f02180d0510110702030c1f12180320070b0909190903030b0f06040305 66
    0xc8000002c1c10000ba1004039400d501c8952100d0501c0400b05d408021f1050100d1118040d62007204c81c0c00100e0102903100d007494010108117004204240c2140c000b10b00b25800071075214000501c6004d001c1034100000b4222020340b400f603020391000074001c40425410081e00b541280040c0c502800709100c80da8010680080c0f0f0448550001241c90040b050741d00800110f03002580c46800e03100282c0c2c01e0010303c002400b100c08800741c118241401a00b549000d4400c607000315000d40b07039511f000300b03400c403c2c4800d040401d003086590784161001512000781d94401c1c1e070403507603144003415580d0001740105480d002c0c80ea0b5456200c1c0707002c449081d080c808500000948034286040c01840102040d010b40005c200c0088020010820b000764038003003540c0104083e44c10220b008150f580c0e00b440117911175942050b40242030100f07a0400905c01c40b440e00e50105a8030440140e014511503500d80344da913003030381c00d2400110042a100e41a2880c5854440d4030610055001d40e010b600301440c5445091b51202 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 245943309 1250 245942059 245942113
    0x50a210303021602030d03150605040308090d021f0206061206150415090603080903060f1003080f040308120f06150f0702010215040803010f09020702010c02040c0e121608 75
    0x41c2c000380c009411410b42002d004603603001025281c0440c8040f4000d00a031000c0004220400c115900c04035a0300d0040e02540c0941f5042541ea500b446021004c2c03050705100311000741d0740111705101d1818280190680d6030180d0b03005070301828490820703000b44151160040c90040058000c5800c1002008800280b010f010004403004078421003102e185117001e82c2c0c20380100202d107040500200a1081c184000c0c61042b505504451a079540c10020750440c0703109a500303071490910ba03101000850041d078040c3c480921039080303e40c40c0590325030360140558042c0740d8011f03071581070318200b00d001c8000c8640598810030540e51410484100e104001480c481c5c11045141d171940800c4500643e4801c001000460786402090962800c09080c042c0c59600244101101d4800d01603020450001500a90711001e906854000d0080c0e56607080001408a580c50f500c01c0100c2801643c0c03560350b60082084c0020215005803042103090030f54120b681f00031307411040c0c0c0d80d031188403180200c80043c541d0340c40d514 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 245944559 1250 245943309 245943311
    0x2607030902040f060603091e0b0708100f090e070b130509090f0f300d0507030b0402041403011505011407060b1005120601020c01080c160c0306020301050a210303 71
    0x41001d200041c0140306800e40c07280e8961030b0190120f49150158800d0b258180991f455006d9a18030000c018204420311034020800b003040004204c0303d130b0190449642064134080402e080949130b8008004680300755200e04170490f00d51002501240b014855500074140740e04807070385800d004440c000d8014480344200c0f4099140d50002840c501020312002e1004400c01060799490080c0301c20703c85c2d46210060303084c0401d07100545404102c02c1d946440c0070056684080003410402c80741c002400409000300000141a1540680111540e4500c01000500800100c2201002c280410b05027110031011914101d543c000030140540e0ba0001d440344803550500d494503540f18101d00d050000340807206451600403640080c9601a260400d0141c0f140444c101142c000a81c1ca00004a980301d10341800c0e140820144c602258810721103000514610384003000310105040256030303219030011568000d49901c2c1e400b1006000380e05d03004600c00010510141c501d03500640b03034641400039a184d04001800c0c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 245945809 1250 245944559 245944571
    0x2240f0c070e010308040e010f0303080f0403030b15130b0906030a1d160314011a090915091c05131211060d060504061d01170a080316260703 62
    0x814040208202800b91450b000406594a01e480e900b50f8006005a90003150342e580041050407082015404494250b620410380d5241c411800e100c250025109504154403101003076042d07102d40c10349203484a01151802d41d08c090011440d103884242d604280440b1030304214840c000d640384020b07282c001600000005411070315084100c040849006030946038001c0c808607403041211b6008034000c89004260b1815951103006995080741c3c8000c4088040841403004e040c96810014400c42d4440328410450318101c105140e5007619160440d58030580c0e90014050444540800401c1203040c0c1d02810702e0790504070f818900b80c40740082800342d4550480080006030034403040ca41e0350400c040e00076110540e600400780c21003015081c1e5004003401603080c0800000d101c50001011450068100c000300e0841e420001079814400807070503462407d1007071000c030f0408030b4114030042d4058a1403d003007414051042c04040d00f4000c40c4080c24200850700c21a04460400b0409075540c400500d240008070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 245947059 1250 245945809 245945827
    0x10f1707030e120304020a060e010c150f060905190606020a15020d020a030c180506040b0304020f190f150c14010e0f0c010806060309120d020c03120402240f 69
    0x621009100020903c9a0040301041c5441e05000b18042c40c0241c900b855030603103941068420010410100c1c0c001010b411801020030301d98800706907440560400414012910250700040d40c1c03c1d40c000350b40141e43c034000c0c0028420b0303002d9211003d0910810038000039107024006501c5012031600501601034400c030320091010306038112520340c41c51150840d16000f100c04010001c1620801050104585083c102100701400d1588412520010295450a4240790340f2a90350307040948205e800c0205003407004d0140d540c420000d019100c09000039445285001c4040100303851a1784040c05480c130002c00510300f82c0d0301943e0340c48200d8200d09020811004088001e0041c2082d225034091402560020a00580f01040e1344014803c02d0340e99810f2a2142c0e0100a41407005480426080e8400042a01d02030840c0e400380030508042e090041c2000070700301101d07095074403503048100c80f202104100800c40c42c0142c14404960741c0102141c9000801c4e4030810b6091045180c0012002c0c80840c41c104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 245948309 1250 245947059 245947061
    0x7080309150403232b0e01020106080601030f0b0705040602030909060d0506070f0f020105060d03080405100e010212010b0c060103020919020d06080708030c060712060915060e010f170703 82
    0x450b1301840410b41a0150341d600b0754080c0404003410f546000b442840c5140d00c07140c120959000501c1c0c401d201c8200044c0c1d1003030312140042241281035541714500001d0821043c48602c2c000c46c054101c00428440920b01081035441c010202020310005000912606134000150f51200c00196030004440d1645d04c005120881c465000070500e05c1307058208041d40e54071480c400d40944446c1c890405a903600c0350240d0980700102c2320690000300380000400405c1c403030803000303400500032400d81c1c0000c02e9080d03210040c2d8940b69a800d1890f9000603d40441081503040c1074014010481400d0034900c842010940350041880701a10510101000c981c050340003c2d0780410180c1010400c41d076403003108807864041c0c802381c4070b05402401000740000c2c1510340030084a4401854001410fa2592500c00565400c4150189120a00d649000108002540348100803001100044a400b142d10b0f1020060904541c900c0d2581040301e1010904081070f00082c1010f40300c01000008420b9550b201003c074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 245949559 1250 245948309 245948317
    0x4060204080604030c060506040c0c02090a1b020304051f0813050c10020c2403070f0e06040b03060a0915091a030a030903110a0b09040e011b0306170708030915 70
    0x8446000b0070090204064010003942206446100d0522055a601081000300e802580912000c81d568200e50001450b0403243c0d030350302c02000c480001d225416400180010302c0c885940d08090b038400107003401140f601e1401100301c150707255150310440000340740041100f000a0600e220700c2c00759608120030080306000c404070501c00034040a09002c44218000c1d90b800d045e016003030081c0942804009600300c69403c0030040804091210314503101e0000c11103684903400c3c041000c021480041c034800b9500c2c8002000104422500662281001e4080258075442c0b5804a00c03a2460031981000200d804008039003101c0c800302d400105000083c4d480c81d202c4ca5000c100c1d81e030502603604500c1c20144c01025180035070380561b01084100d8a61300034005001514064515810002e00c038551940c6041c0d0040c1030034800c488004556004500c1000d0108450031035860302094a80d40b007841840c0c0719500013154a81c421000b004458940004c2a8032480703085e081078010801400040d110f46110b00891b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 245950809 1250 245949559 245949569
    0x504091806110d06080102121f0513090b070c0c06030216020a09020a08091603060b01111e2e0c05070c0602010f05071e0e03071d0402010e0d050d0804060204 69
    0x280080d160b02c035000c880350707400892007500251500001041c0340505200341d40b4040c98140c4010210b44440c2101040f0b0f50200000c000c03804940c840c0807401d40c64641501c01c0c0f05c000340c40081580d00151034480101c1100501d00c000300000c0d0031403000814210f603041400c452481c03d006030745001604400340d0044070303440007075004180117a001451440c0759001f4520754520b40c0d50030500c7d4469003001915030160040060304480b1014060000c9035250b8481c915414050602c844101450050300382030025205040c01d1001c030500300758503032807000d010b58001071081c0788240484031703d004545000001034448580c0d142e6514521120400e00403400c5070f81e0150050701c800040c030350700e02009020b00a0310740c1044207142408041000d00d03008040e444140c6c2c02038039035403040c003c207000125401070010010541c14810104005111030043d80c3c10300b0140c0f01030518030030501e4140005010310204800c3c41e40161105004000801c0c0c01069184100806141c809583e40321400e00102902481d00b203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 245952059 1250 245950809 245950811
    0xb061c0602030a0b12070e0a0b0d0c171908090103020415020f06100e0103140109050f0f0d0509030c010804020f040c0801050a0e010b0307110a060f0917031308130305060103030507060e06070504091806 88
    0x2c0002804000400b2408a0f00c65040b500030000000c20281c0c1c607844c040c144010740b400dd07105c4002c0010000e81c09454044810b00d0300505045c0d40b0810402004800540d0340056000180c40c070000e8a02405100c2e4002800d1010049117441c1c101900001001440042d001c440403240d0058107500039000a00e045800c20200c03800140c41040141c1c441c00c1300380910340544550044102034030302800075280c0a0300001c02509110038841d0054580010040c0200c3e4000141c802108041c0e03528400c4080c00d00302070380c0360030140d8140010310030b00c2805600306080d8020003400420004002001b108c0e07004c0e009140102c00d0800201c1c0292801008440040c04c03c0c0c104507070740b00c01c0e000c1a401142c1c094051041640e0107521510f03d03ca1903c015aa2081800e600c00007a00120700840001c1054102c40c2442c20b01d925503076102c01d41020020f03003044001500024083c428000b041c005d0489804081002d0310650070f010303e02620750300c51482800d00141e1201d40c1c01e444030900c001c01d40c18140c1c200750 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 245953309 1250 245952059 245952079
    0x3061c140a1208010602160b0d060f0b0a0206011a071202030f030a050a181203181407170303010e22150b01020d1b0b061c0602030a0b12070e0a0b 64
    0x1610381d241100c42003002c00000c9692000203851440020140026500c484102498608000800a07168440092404195101c07080054040071048070310b4000e00c1903840454548101c030f80001d08143e81a07114040380005070203428003184000b41103500050b48046c0984c20742c0d180e410300764118001c100000ca5000000300c10171408400e035401081c8125100b03c820441000f158076980d001608007400600100c00410030100c2f100d00a5101003003440702c4034500e001c1d45042c0e80c1e8040c290500c46880001c41d4010072010003d4240303400500c40b00059540c0554119818041d201c3c24050000305507401401c008a22800c4651004801c88601c039040018500c44c1800400b401001d00301d47c5600a00500c50441040002440303040e8a030301100d01d1140726034288034142c46460500e80c0c0a02503a9102040380509002a10308204c16811944902c0c5c1c0941c880c074000b0182000c0fa14410040347c01401d502503040041440030a0b18000d96a04642141035a01d840280900810b85829886e0300700345500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 245954559 1250 245953309 245953313
    0x1202130f050103031403071211130803070302060105060c06060d110402030a060f06020a0302060a090201090e0f01180606120c0522030215040e0a0b0118230603061c140a 74
    0x140205043e24042d4850000904510b05e481015200440c1c3e1080042c1c10100050b0072410690080c1c020409400540c0d0306151001c607013100c04130800d500000c030340d80c400180401095010700c80c0038014481100d45a0818003024421034039204000c20041c46142c011494070100320951045100c1c181004d48119201c0c60038801c40d000600c07150044081544144034000307910340c03002468002c01131b407541c064000c58a034044160041c1501001c100c0c1801150746021031200c0303d8460440c4145070703a00030382d03046503d4100c0042c03640c0103920060008500b4028203000050708140200802441300c800020310320780a01d4201c845015a100260601c401146440003000c001100c40c41034034000c807607440321008403038002c410500c04c9200740d0508184107400119004001d40c0002d214000604004400071009441d030b1212030103d0b08151200700c000d0f2242e08000c0b115460a0003070620030f41340103155040c4200010100240700007080340410f2090481c108005148428401465441c0304540c002000341c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 245955809 1250 245954559 245954561
    0xb07120e060403030b0906030c042304121d0603010608101502010903020c0405220309081905010f110d02071703010b0c160e010b0304060b0312090316030c1202130f 72
    0x582c0c041d80000d0600e140c805240c0781c582103043c0074460090041c0403411201041c03001901c440b8003400c0700404400700c0252013064040380c50b88103e01c62100203006420850014042d680b00001c80d49551180b8242c448031303178030b07000c0440c2d065448908100103182c0d15a410007107611641d400c04510059402c0d000325a040c4c0542200b540c0910070b4090350204242e15092004a0360215024140c002d001326112155450b8802c0c2144028000d107030220304e80d03031613607145442e00884c03a146142c0081162544001d0000030b22540c070701080001810f203c030b044148041c0d0031500440f54241075440d4002150303401c0210328a040446a0010b00609883c3e42e0f680401d0074107500300320280c0c2c606000d150043d41c460240d4500c40305c280d82500c080007000340d01700300200d0f449070001081154841e036243c9503942d982d07604120a0080c0728946008940e5000440141030410109500384200c2c1007824005000280300b140c80c45080d601c61440d84101680580004ac440d50b2500018188961030318501003462155 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 245957059 1250 245955809 245955811
    0x109060f15140a030b0601170106020c0109120309061215090f0b061303030c1a1305070f0509040f0602120708011a040b0a0804140709020315010201060f030b07120e06 73
    0x705682000119607101910560726034030007a21030348240f8480d010b000090350202800d821040615101200b040500e070310131030800c030a030849405a409051801c0d0f82c2c0da8080b5590000d46010800540001103d68025003880e820380101d03024000554559055518543e216080c286550582c42040c655540d80d03040c000c0c06464003c080300ea003065004403881c2071040c202d0701400005c60b00402038900c1c54504407074052701c80d181104c00c01d410329039000a809460320403034001c3e041241710300403440c80352608600d000700ea46d012807101510380380304006a0382ea200000ea8029045080400b04a04901e0800001e01c24145405141c0c0030395024080310580c400d0800713060300d4603019920042e02c0348c050b1240f1507001c2c0d4401c422111808220810106100306072a9812a03c652038030404020203000705030614503241c02c0403034560f03804410400105825001e00100c0e803400e0000b00407803401d200c03240b10503c9280c0000340c40d140c5030301c010038000c500c038001c85000041200d800700120304030344940c1038031508 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 245958309 1250 245957059 245957081
    0x607083c13020a14060405130209130b0a1a120115030f0506061602030a0203010f020703090909050d0f050d0c030e0c092403011407020304061103090a03140109060f 72
    0x811100061014620341c90340c4400705800600681080e8900807168041011403480c054000c10240400a15900c44104140c150f41c0c40500250301c1d41c251500b44425410411201c2404a09204110a190719042c000b00140c0702c0115400000b1442100c03102c4c0c091040350a41c0b1a0109220000910754441107a559812400340d642400031000c0f295080c41a1202a150640c1c081c2081100c941441c0c241404000c50a201034140ca0910309160000307401c5503520740750041801e80005d41d803810160301c18080000f4010000341084062020b841310f681e2110103180440c180b0841d00004040f49000d9020354403804a540400c0c041c00040c6280103000d8070301c40ca1146039910801c100010365180c0030f50003a10840c2500c03200840586400140d86140031130070080c1d44c041d503070740b0746900030041e00c41035043c07140306660010740e500d078504500203003050400030700c096481d041030000240175500e10781014101c07a04100e240000884042c1c01070300515501e48004c002c549840080f10740e20076640c004e114005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 245959559 1250 245958309 245958421
    0x20c0a080f06010e070215090c0a091d0102030c0403021c120c060c2c1201020f09270c18030f1606030603030219050a02060414091503060708 62
    0x40d0740c070404000d0101045c1c1780e40c00582c100c90300d0800c603520304905050340b081c104c6040720315101c120302c0400c13020303070f2150807001c102e0341c5910315100b070004982c42402c4481503100085146161519210305a40100e01000303100c1c19a4400103c8100b084076110700320140c2000d000890260141c001610100040c1d0080fa603060801800340c9100b805216180110440200b0361a0785406d0750280c01c03021001c4410095010710b2003c61141c0200091001c0e010700700540301102e507116040b4040002012481045410305103528008404402c01e600c100d03508540b41a5005841d420044118003140114901080c5c041c0f003107000d41d000e07058002800e10092103500c44076800060b120403046040d40c0c43c0d40805000b50380405500610280001400800180940e0036100b10441d140e0004406034081e038080f842009840c00060b0240c41c0005241d5089410040303c1c4c249500410302080c0c45a100506000500c1104000984111107881e040e00c80008090b940042200c240c86e0004480c0e2003003a0250019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 245960809 1250 245959559 245959561
    0xb1c020f060306100f03060812070c090203090d0813080c100e0105150118090204061d0904030e0f1813051501050d0b0702030705070e1e01030c0b0a020c0a080f06 71
    0x1d0520034112070150388003070000310b41ca4541100c15142100303070300200710426580c0e02d00041c2c103001c10702c110b00440800031b501343e0751400a03040140302440160445c4078024410000d2003105040056104800348290a201d0403680d00e0038082102040c901c58003801a02e40040c40800002003c41c480c8000845004200603036075408018600325601156010007a001c840240c1805600404100e80c0d0655100607180c0b00c141c590140300113a810031b071310a002080e204d03070035072203462129100180d60240607031303003100289055240200814144042d442c00781c0c080940c00b0760940c4994048200280c203c003090013007400c0145a0741c075944086074040ea041e010f507600ba1006844800c0a041c101c40e4006c20b144089001c036141d0402462010b89640f0540c03004009040020784244514801060300d002c46284c1464003945078244110011001c14a000d46440140002071440741680e0a88003c1000305844029400e0140d251480d40c0c000594030044140c0002524074002504e885541d10a000b0313a0a1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 245962059 1250 245960809 245960839
    0x70605190c09062106060806030f06070c0f020103091a0a0606050c330910060501020303070f0302090a0e0f0103020109050607200604051306081c080402040b040b1c02 73
    0x21945021a040000b4000314810041d26114141c007441158208401c090300c0101d911003102110304960000002c035070000c01b0000300e072034240462002da4580300301402440c902613130f005101490116009080e2042c002c425020359100750301c058810717580002900d1192030f81140380510180c0413078440109078144800450341900c82c04c00c0c1c0d05a40c03800001032481c49803050325001d110b601c829800030504490407090400c1c1d101585540d02921000000d8600c143d4131034111403c0d500c864201a056510420601c045107504c40c5800115124500c1c00684030b4100300b00040800c0310503030284802c1c0f0302c41024400d4182c05941c81070b0480b8402d8a60074101e50b919400d1244030300801001502c030102040c550440f40050028002520200414141c5050703100d00004050301201c00d800d06030f80b95140f009000011003003000c01110f01c042c40301c1e41c9800d44504c0c0020321050000b040240250745802c4518070740c1d02c40b2b4012a030803010052601c400509882030344120100070000c260b125a4070100f40d60301c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 245963309 1250 245962059 245962061
    0xa0f1e0f02090d0f050a02060f090a050108040b04060c050412150b010c02090c07020f0d0302060a1104081002280c03080106090e16020a0503040602070810020f0405131107060519 78
    0x1922040c060302200f003100440d1074100031158255415203850256601d10401aa900002802c1d884d1543c40d1064640010400380804103a1a40002c0e061010040921000c548001c25695020b0f42c0488046012700d6540c800b10b40601443e0300100c10b10300e0802c0680100080c9014401d4003615416041189110080044074070054510000c0d400004120118140404100050400b980041d001e400307000e101c400801c4506003c1c443c00d80043e0030050612030403e9847c01a150117110700c0024505150170f02000301e80380e00140c0700002000e40d00042d86155080d9074940740e400c00004a00700c1c05004202c20300a05502203140044000139004400459442e0183c0c000f0425101000f10716262aa54000240d07040310306c500e885419446941e14240000703100f0030080002e0103903036001c1c0c00c5451505070034070301e412142d9003540d0100d4010f02041060191000965084072002c0780c2581815148001510041150100070070410720300180305411b22500d0f0304441d0069113100b084107817200c88062008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 245964559 1250 245963309 245963317
    0x180f0d050d23010312030207170705012003060d03090302090108160b0c0d1202070b041104061202030c040b01050408390102120306130204090504050c0105130e0a0f1e0f02 75
    0x10710500c402c2c1005001190010301d00d408000400d050051a100c001d44410741d0341c0700307050072500511400180103000c1000a0241a042240007800c24400d030070041e2204480d0f0000070145070154148500c0d003400d041c41003040c54001c0d50090080e03401b0b9611907658a881e11400c04000d805404802c2c80010f03400c1511084820317100c0c1500c094440e5030100181243d5042c4580300e6804100c2c1c00307004403c042008080c0450180e44100010002e003480729080c030007622096440301c120608034252000c05600e005c10500104042181c1c00500902c03101c005888500603034202e07888030700ca0b10403041311a0000d283e420000400212007084000c0c207096104840045443e10540160800e00f1503840c1c00041002841d00803400910150010a1420503a000c80e04503a101c00d026603121002c0c0401d0000600050052100070700c0c1031417500301c50110f420301b03040d014460321195200400000d868036049030300c61103c140b00e4040a00c000d045c818604080c80c1c0c1c0014410000d00d1038980b040341c261701c940c4215 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 245965809 1250 245964559 245964611
    0x308070503071e03050717220501090b0a083103020c0102011401050d0b070905030307110f0f0918011413020f0916110102091203070605060301020a08180f0d050d 71
    0x500d00110303a640e0841207036588000c0f0294031010302681c8e8801500150f00d0903022400d60208100360f141100044c501031a0341e109407140e06080281c1c600a50380300000550111170184209000c01607100c0710303140440304040ea681c103042d4400c07669041543c0400c25864882e03099000740320f00c6580300417000002000380f081d981e102c1e051106100c001080f101409600070391905188030340540c1c07400401d00b1a0720020086403400c2880b41003054900d40031014040d107030402d54004540b00500008140368000246c55070b10248280c0701c4c54803604009401070848c2003c61650508242031807183e45280c02c82428049114200303c0d1601096800c00c0180e00d807040880180c6103440c220407040907600c0a08501da0415255001c00c400029038440302c0c000007507110204000d550701c0d00141040000c549000c0e01161099004000f43d4020a038082e003c1d0303420851040b000c00206000c0c0e0312091a0010b454885007090040c2e6000e0030a154102024040d00080402e06220b0750920b280e00c07440300042d104e62 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 245967059 1250 245965809 245965817
    0x391101080f0f0402031204081014070c0b10030c030b070e010305070e01031802040507081801090206120613090308060102010f060305250e100f0e040201090306150308070503071e03 79
    0x60305141d44200b185402a00160a441484e0403000031100c40c3d078010307040004240d0050036a640040058424a03050034220b550a0310070b828000d4009001c0c5842010203040c82c035a00300400c1c2d1843c44401001c0055a000010300071039541c914100d42460000c80c0c050b00421120010340403294040d0044a1040c500d43e594001d4020b070002c0103400400780d8010301400340002144090060300c56115450161b0043d448000c1c141c80c2c440c80034004100710710450349042e41099004d2005807500c5060750707001c084e4031b4070240d0b5582d51100031462144460700403500e01e5003440d4030f80c001d05400508140c01907400703a00a200345494599440250303000740c4001002c0d07a101d4503840303103941d2900001c6210f281c10b0a00301c1403c00d0b0740744c4002d40c5103d4140d40c2d5043c0d01030641420400c04212520103001000850204900761500c1c0d000a400100d01c4d1002030811070302c441801900601030000203004c0e5901401391a110a26418907603642c0c0c00044040315001e601106082014094402c158406513043d07079 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 245968309 1250 245967059 245967061
    0x501021902060a0c06050c0d0e0a0f030f050c010c090e06041104090e0a1202010b090a060608150f0319110306090607052115031c050406391101080f 65
    0xc244511980100d80180400c02c000304c800c0000350b10ba0180707034000c032000b52100c0d480d00c8150f8120741c21221250510960303036102e40201c6000400801001c131245400d4204074030800403403007050f030b140c1c03189494a94055103080c80049406400000c1e2106031801c411100c14541e8070304003840104c94074142e1001c030403c0305000802034840c840d0000d03071090003650b003554001301c100e46d101501e0350390120b005e06c0940d44915050b140ca080c13401d207070b070b50102c0059002d101c620300d803c0c0301800200002d881980b06003203079511161151501c080080d60080701504a0341406014203541c4540502850202c40701440c7d804500740d58900086d83c14040c011201c05030505840ea11000e5031141d0150f00c485c50101e8240e4101121162911142807081d000328001410801000d8105070805ca9480c1142d50010381500c07000100301d51100548003564518240000204241000c80800401883c5407002c4c004080480000303404a00d096484564400c80c1032602c0b04080070015a42648100c0d40300300d80c8400d900c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 245969559 1250 245968309 245968313
    0x616090b03060303040914090c0d0c050103090507050303130f090207030e27070e030c010314060d15020309031b060f13111807120536100b04050105010219 68
    0xd0000d640090000741107034901a070306c80040041d130b880b04c011140340c544203108116020106009400060a0854032824030f14042e03a80c502035001d00d03000300340c1090356480074101082404c0060002928004003120b4842d00b9240800740d541d03656000396410301620050010f42004a4000c4d00c40860340741e242c2c0044007854400b4000c2003490f00703403004501c441f80e01c06110342295550102e40281d68655910042c0c000300024036207800c140c61203082c1018600307040c03e0f43c820310742440103401500403505600e440c400c904100001c1d2418040c12100c2c9031001042c090b10038000001002d401c620300001068003042da14105441e84402c440c64518520640000351003040000340c8a16214490915440c0e0703900f83e1004120f4040b003054815070781809407828003c919070480060040c0c0403c00344d0500c418602000d008d1a480c40110300d4841800704061104586411442c1e8452041580c0c01168030390b114644602029040100d182170240789000004541c651000c585410f8400e00b111260200030a19 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 245970809 1250 245969559 245969579
    0x306042a09050306061f1b05070905070e0a0b09060c1b1c0c0e060604080f0a0308010b0f07080f0c0a1104050a05070509010c02040605040f05060a320d080705010c02061609 75
    0x8110404104642c02e4021070721850034480344200540034070009e060301420540c5100c11164040c00e0301060041c8040e00c1c0810742d82d120b00c603505607140389441d96200c40c142e03404142c550240c124036a9050058050700d141000c035190108181130700031a03905031440c409410385d651014081801501500403104148078011200800035001400541118a0580d958800c503003030000503540c40c0030315000100514245940090280d0242541c0c00c801403400c1008a00c1d03400c03a105010004100c2030010503031030030744003814042c2c403143c407200702c256803204949190800300720404079211480380303181c032020404c01803d9101300c41c444c40072034442e02e01e0f05034074038015505205148800c80e0302070f440d148041459181c50184000c900380700c000200c1e2a0a00c10100404a92290071003c101103a0001e80d00e80482155404603c1c01c1900151681c41000c150200300101400080601190400034145080207815440510f4200c3c941c2e098800c26210b20b0740902c070811102c9036540000b114540203104a41c18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 245972059 1250 245970809 245970859
    0x1227020f040903080403141e090411180f06040e010e090f010b010813062705010e060603070605070614181c02100e07080610080601060507030903080306042a0905030606 74
    0x4903039042400c01c403440010702c0080540003441e0341c0c50a804149c950007800d003402010700c030741e015100d1b86041074640b10003080780b90000c4224501c184e008507844070440c2c480500300c802a2107078500902040d07844562101c407071130042e11441614401c803080005a10411310510359441d805964a503203031f8544240419045460800950f0a25614500000d004481c005a01411881c0b405005035030601400e0040c21a8070103084100e050700100208240c0d42d50110b4880c045d100903060194454501e1b0034514014480c0b1501e0f006509444018062510041c1021800b1038000c042207030504401c40390003042058078400038901691007465845a0800700760800e152400c1d2400c11504250b40e00d9041500c0c00005907041c1014512604007070026190038421540035007403500b4080d2920b9106c1e23030000d156042508c006000000080041849503549801c01c0141459007001c180f5074810401c08941e101b805403100c0d101041114400040074140810940d10130741c002081d106111480300d20401070380300c4c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 245973309 1250 245972059 245972087
    0x405010f03140403020c0a0503010603050c0904080d050c07020913020d03030e160b04170d0801150311221409060603040c05030303090604060f0e0c011227020f040903080403 76
    0x244980080740240ca103860081d103e030380280c0c01441011309403800c0c13003910400d503003009019904100d4203001052000a4001841700103841c0180140c8d1507060040141c000c1800030014682003800340481c8241e004050407a46000300c50b101c5698640388150b003c0d820310004004c1d00104807800000119019030311483e442000c000030384002c01001100a40c02068640000d003100101090074449810a01040150043c200005120020ba40e10000c1c00c2c0c2d250502c0f60007070609604503078006c102d110b9003001c010340d141c8508880d182c010806c200420710180d03851014400d1300024000400c98242c0504605041d00030300070f81100e403552401e103c1d144c1d20041040c1c03512140074000144985040000790700c103520303440244c10b43e41041e00c1c14070b0541d800c10300301c50043c07400c003510080c1040b008100c0107240c201c2401c02228a000140e4081301400d08542c00155905c541d0400c01c6200004c126110107492013219a010f80e030f8039900c1000210b074240300001e00010056400100000e0140390f010381c09030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 245974559 1250 245973309 245973311
    0x507090b0c190606080106060302120f01062709020a050c0114010f0b0912060f1009110405010305181b0909010c05042c0a1b0207030213021c0c0806100309080405010f03 74
    0x5e0701d500340a130949150383e20080010f60300182e12084403001e0300350b564000d81e01c0c00c01007003a949000c42c0200440504e1038030070504040802c05020000340361502070010f00300c0d8907055454450860000c0d041c1d8009040444955080c48020010380c260760721041d0682e80c002e0a1082400d0902200222681060300a039400945540103140700401c02c0200d1407158140b1902d1641c03030703d48101e8034080002c080e80b1100001d41460102031020f00785a0a5038191202860000750750303900c56400c1584503801c13008240040c01141c7c109a50810261880c00755041d09807800e400c6511000800750880c0c03460411080011000d0106200600340102c0d13540111103003c000303000b041c511440211103c0020703201e1b2648240c1e542d6408514001c510b011044281550001e00031882c510380109a807000c490300608110f07a0300152208420441d000c91400614050004110300c9040360380c09001000103455861103407400340800824144603018100102d0b40c010704007403c16141a006458412151440034141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 245975809 1250 245974559 245974571
    0x20a09120f0212010b100c020102010b04380307060c0c09060605071a13030e04090f060c0810030c140406030f0f020f0102010e190201020a150507090b0c1906 69
    0x44945000e14a0114011180349185091034410084456444080400c0f01d0b41005002080380d55075490090340091241000681300c8100d10040340104640c925807503015207442d402e01000b41418a140903555800790307a881c1c110407070405078000221003400040e41680000300038000307070f0f01c5192801d2100c1c0c440c81c000301081d510381c0c14500a658080c3c00403400034102080c03140a00403c0100c4242d641c114060f23040329030030b1100c4000e0000c0e203c0300c0c0141c00c0c4601006035000507111540049030964105c810f40080c66444e00d4400041d14510321024006510080454080c4410507440000c49502c14000c0c20182c0ca482031400c1c0d07404c1c00c15400c6620554404001020403c5070401c4101360740b03c0c40b00c18024403d0b52040185210313882c03800c10b0440e80740c585512001000022014240081e0001007a1094011f100403860a5407110000703103e008242c071fa84681d900590480c40c040c02d65500d80160290711030058a18500458aa10605034844040c8101c60112020384664840c0221008661 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 245977059 1250 245975809 245975819
    0x10824041713090f1803050702210f0312010e0108071203091208070c0b030c22170303091903050724060b0d140f06100e0436080d020a09 60
    0xa265903502c0106525150843c4641310062031180c2050040c1d60f4584170b410110a85000303101e0300070500f000b401001c200b0101300d40f88050740c0080724005415001c4406144518440c81d40f6034101190040740100e07290004540700d140c0c81d460034181c0e603100000700202890a1401113540c20b4901d02913051100308071010070080f64010100d118140902810f07a40d0f40710310718024041d16031642c003103000308009006002100150314101d1700803142581c2c42511450182d0303404203a0b0020703030f44079580c03400710208082849000440514801c19042040e2000c040308030b88a401c48903007060001700080c1080041e40c001840d20b02484845107042c581c0340c44040f031001c907080b003202d41d9a000390f0030400c0040703181300c409001d0b4024640708403c0c03115081c50b641061302e10301c40ca4180c00b5100341d2041c41c00110000d4028418401da40031181c0040043c81508403a81880050301c4000f0340b51a401d101c01c400285c00c0d02080c003ca1549151300664142c90110024010380080d007007052080c04001340d414000034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 245978309 1250 245977059 245977087
    0x50a0c0c0f0e070809060c0a14120a0501030c06110a0818090109050109060609050d0809151210081f05091603080c01050709240512040b0108240417 65
    0x1c1d005102d040d00c0d03141840f40c80900b05003001400001d05902c140104404d013088a400d540b02c03418941440c5104178500c84541c4500c1c0688440d940c0004031003000c0283c1d20390b080e0002c0b8100e0b4010f003103d0601c0d546404084800c0c0f00241841402603100030007007070016030118010650310035002000084442c80d40c0c006482043e007030388105000790701c070b90041c040c1d0403561142e18014441c9007001c20285141c20003040d49201103c101900403070020600400540b10800b003012540e007103256007aa2418000009100000b05031890140c01d128004082044940000e05074510b1800d03060201c112a54066401c01900c0010070500c0d01e400780c50785080300c42c99201058000fa512a00c0040e40b104000d182c210708542e0300425840810070b0121040240b01070701000031304d2000c2c4041c801c005040c190b06040d5507511400900c1c002d040084010041400041082203060f100010107588100603030030320503010403110305010003060114001040019031095120013845a2842c0036504261000030841d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 245979559 1250 245978309 245978339
    0x40204210c06020c03070b0d14010b0418020306010c021e04020c03040302100c0b010911041a0307030b01050c03250602070c170a21091a04030605090c01050a0c0c 71
    0x149145005400d0108115454a0580c0a00154030082c044404220700180d07545006104034006614000707203c20240a10b600400ca03d500008086000f9594500040c0100d500910410a24911601c00072000f40401e0084034014401652001ca4404d070540070007041000d074000da903d031090280840507040e03c0300d001038007044030071001442d212131a500501c140381101001c0f00040040304000103000441d4014020706541c600000090500c603c90240075403480b59412035100080009500b200035050b000045100c0d282070342e42400304488880055400c0c1c050b041030400190024001103242c0022881c3c1b581d0032006240c441401c00c070403522003c0032640602c600303036174282c99214203125504a51302c003041e016520340c0081031a0350050312040c0c18139100d203000d10b90304803001070300c0e0070124840c002e05030103400c040c80c07040d1242031254000d103519032242c8021250b250404001450030000131800c001c02040c10b855003481c100110008982c2c95032040700c201c0d000e1419442c00700d03420015003904 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 245980809 1250 245979559 245979599
    0x1801060302071b03020303033c090c120c12030403060510050306222910081603120e010c05070303032304030f08270c1903030801050906040204 63
    0x59a840741803c14803051003142500240d940b842c8581000140c400000f100d50101c1c6d00e54610404c0b0310682c440c41c1c0003034020580240c041c4c0c908500b000c0b55200e80c0b400a401a11b240040740e0704101d8440500c1440d0040300025182d90f0007801c0c18003460b04001c1c45400208d800401a030785480d480796580f034201e81c4280d441e2400c1408210048c0428142040075541201582500240c00403003c05001501c003a2180014100700c0528136408000301c0410040008080d094040a031902d04041102c0c21020756118840c1d080c0304045150741c840301c9070460078041d250400d070841544c0040001c00e45950011140e0181013169000007030022800900c801e00203144245c1d4041a00721a4544116107804011844200c8154030014080003d42001c1003440d400340c641003292180e901d01580058079240da00c100004c40c4440e078031200180d80c0c042802c070480d45c01103801c0030490f01110000b0309000680e0000401195529005010720b1400d0242c01c0c0d40030b0750040001d4035198980700001080c090140c10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 245982059 1250 245980809 245980811
    0x1a0916090b1b0d18030f02040204050306070201290306010e10030c030803040308011403030a120e0a0f020a060507120c1e03030207140c1302030a021b0d02060a1803030b18010603 78
    0x400160040b042c0030210460505281030403803060420220300d000e10191100400003018100424115141c580543e40104402810b840040c500703450080d0180c8502d02c1590302d10a000e61040d96100000c1000c18000c200240060120b40c2c244409030300c500c400540b40d8128072030103200c0000000c40040a0300003442c8501e00720340e02d3341028030703000d080c010040c0c010906142c2d41101ea1210364800000303a030703034006584c685420240b011680c81401001e00c580e491404d80030b2035400c002409000c1c90340c004070740e00c20313110100c049a641c2000c692901510304020f2800142010111140e44a041090249030142c1d8040c4c4050b034010f1800465440e514800702d0100e6008103000091002a00c003042041c1c40603809004926549400551000d20441c1d10818241d07011000c913a004030300d581a20900c0064240380c8a070703282e06580650380d80d0000c901c45001446800e0003e4400d40981c010f4029a10120904d800c2140c00d0340d50540c0036001d1064181d4200016096100840b08042c2d800f50007440c154074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 245983309 1250 245982059 245982097
    0x509030c0904051b040c0509060304110618030705040506010504052101051602010c09060210020a0c06060e1b040f0b07080705010501090510080c100c140a0303050a1a0916090b 77
    0x78180f440c03004c4400e20601c180c0c035140c10744d02e443e50400115500318504840003070362035455203000c6404421140d03003103401080100d215030580b4036803500b0703044213941201164106940c1d9000c00c01030700c000300c512500090007403004002c02e007070404e0520002c804ca0f4a004104040720b0741c00a08403402140e410180c403a04546426800e502031150460240440c40c102550310300b0b015019555040c25155000e006a0014810341d1451042c40801744042d4482130a100b46030b5141542c1413030400a54044c055500c0081d44038042e82c040d9001c40b0200e407540ba240c072601510b80103000b60344d50041e40b41524201d10400056001030000e2007018003820011000142c581055041c446803405517400c0620740d80d0042d03074001019516140481e4400003a0f140c01480300740d2030715007040181c40d8103400b450a440380d18070340d41c100354040e00000d00c1403180320f104000121108000080d040a42d100841e0420300100118501c3d1b810290309825602c0c1c242001c3d40050355619170301615522902e103000401e00424 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 245984559 1250 245983309 245983333
    0xa02030714070303270611030c150105030d172229010b070302120c0102041802071b060e1002251a0f030c07050a150e0d020d020d0509030c090405 64
    0x1168410045d42d5812184800310b5180040070265991400341a00f8481d1a48000c44039250030030490311124050307001d40e80e2601440003080c004407c2030044a11034003070b0154a89602e48200350440d5010782111921915480e0000019140442e040e04506040c103040000004180300c1800712001141402010700c40d00d101d645100790280040e00031110111b030810070308000c0303680007480d46651088100b40c6540d03400003c0b461402445280c1c8860040d55000100107079080f0719a016141c15401351400d03030800d81540c5810182102540180c0000c980d02c0f00414140d030500d1484079100c00300030b0048480740c0c60114104007000421030031030303000d00380c10490910015280f00c543c850300105188949042c00b00b1a0748890b528000200441000b02d030100300441404001c100291080760000112515003480d000000090003100c2c00d201640d102ea00790940340c40380f00041c64010031b01c09a020303004012450034202c0d8280c0c400c029107680351248103c241626900d004903c0e005c0e9200e0340042220500b11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 245985809 1250 245984559 245984567
    0x6040b07030b03070608090a0b3c0a0207030309020a090c030b030d080105091b130305370c050301020a0201090b0f0405060609070219030302130803040513020a02030714070303 77
    0x300000d0401d400d2800041c0c581d20000380d00402e03a401c40c24848803035664248030900e001e03c40e07203000c1c00ca00340e69014482c0a8451441110454003205080400c0390035500700c1010407000b186480c8015400f000005669000c5a4041c14401c1d110b03140219070402680c000603c40c2546410420400e80d8410908064580510034525001c4040d8090100c01801c10310103030441034144225801500c00030f0002d050700304503041440c1003100f00310805850754081075050007004514042220306200c1e100e1400d820190065070304103907003189400101e0303031030b40b41d406000c1206040004036002d504201c00810030799030078005459084440d50000a81c9015401d2280001d80050301600030300d490302c0c081c0008100702141456021400f5581d400081c0c1700d180c4200c1c42d00413207105145140c01e001c10a8020994183c000700003c0488a00c1903802d291507048858482c4124400c0e240c2c8081d602c03800900e890101e07005000b00640c14016203042c4072040c1c82d10f01e120302c2e0009859200d6003000406200301600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 245987059 1250 245985809 245985811
    0x40f0b0a090603121b0c030f020f010c0b1504092001030b060a08010905040822033e0607021c061404020f040905120406050304060b090606040614071406040b 69
    0x20110702849070074950f84800391102003031446213040100900380c2e0541140320858003c05654489280c10748503640b414486c043d110007200c101d11a41014504100c1980b085040015a940090307001d8001e85075103503411221040e541c00580c00c85c0d140d0010030b002c1102004442400300c95410801d20603126000010110f0b10307542c500c02d22401e024081c1402d040d60142005064440b001c0c00084c441d2a103041038140d600403165610360070381c40901c601403800d424440b1001164407614030740806990100c2200180d841404614900c000c040c0400360181c0c0d058140c900360000c01908491a1001c01c1e00070820001120000500d084200990300e02000081c2c402c81c948c84500c1c203032030010381c1096070000360b0203104404103034416611020780d441400820311560801721076104e8101c0d0f44545d1600083c0468000301c0301035901c43d250810f000020b0420711011031048a000300741601c0d09042840a440c001c08040c00e981420400388202000201c502c070941410351150703001003044e407800c0d2918800c9040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 245988309 1250 245987059 245987069
    0x2160f0509090a1a0a0b040c0509010e0301020a020c2101140118090c030219090e0f0c030a0b060907030f05071106060d080313020612040b04022b03080601020a02040f0b0a 75
    0x100c40c082c400c0108401d50b2501c6104081c80708103021907285e058803440a042e0381540b0550040ca4040705c003040b03603009402449041020b032a04040c0c3c4481c80300305803c1b8000d40035860050703003100d0295945850700ca44644508035101203c5409001140001130845400b0f8075500e41417103500c401400040c1e040403c01c0d04010100009004244895603201101c0e1046d1000034050070041507160300f240c00c51010b13000544000b110800c0081d00883d0380c95580e548608055080b800740901c04043c504001c00c01419082d0445c608851030303204d030b1003888403c00b8010080810199102c0a20501c80364070b01560340070301015607510511401102e440340c20104050300c554412180d20710490005611001601d80c0716400c14071a02103502c1c03034004150b42c0d03c03528440b102250310040400c800c000b03034101824015030080d0381d082c0c02801e0f89882140c03c1d0001401a9001d4965143c1038030000c0d1003040410360214042c1305a0b40d00d0b1500d81c0c041415210764045081110b625840021201e060100c07108000300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 245989559 1250 245988309 245988313
    0xf0507080c0a23091503100e10060e0109170c090106020105070c081605061003050607141c1b0914010201020f0f0f0909132003060a050702160f050909 66
    0x2090302c14007900c040740c084504280c05941102040d4001c1e0350350203a0b000503a026040c0b44041c80008203031a0564000c4450701d17a500403100380840d0f9117190b0f000e0140300d241101e10307182d680b80c20202c00361a003406080bc8141044494130012481b4210034480c02c65070380c030140051010000100400485003016008501103a240c030041202e00e5174020601074819800024059032141c3c0345144055040990801400d540702d60414410500c0002403c00b0840b4007a2058a410f42c646000c2101d03030791940c42d00c492000205000380c910140a02d401640034151107440014405140751b00c442d410b4030320518000104103e51001c0041050180358040e488001344021444c18080e100d200425004480400400079004204805171445032422505c200d44001c04003410b504d449040140d46144500c01101c0c0343c030403000354804243c0d09100162016200030007800c02c80ea202401c2030b0043c400209928214410300c0b039855003c1c100c2104800107400035000003901c4504000a020008001510302d00d00e039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 245990809 1250 245989559 245989567
    0x9060c07050c12010e01020a020f0f07062109060c080405070501020c15071703130623010b0c0705042c0307020108040803100911070201031409030f0d0f0f0507080c 72
    0x1500480c440620050403100010000c190b003070414010840310200c803407071b98400031b42c8103a5a600040c025403162009400c40d1140c01804007241d40f1142248035880100314412800422040c45000c2020a0408800e0000301c80d0740c07a4032010240c81c24501c1d00300c00f00d00400140428840d0903c5504098a802e00081c007d601c49000414690f45c0c3e00501101c02c40000315021042087c82031070782d20b004910528550b00c07420704090007482e2241c4201d049400d240391020503c1000d419550411010182d503940070090b80c42c2c005071600e1030b80210b884030300b81e00640f4008561a52984035100c10100044042415010074003240c0202c45458a1510340c0d55105006590040c7e0340140c0713155105920800c40740e12a1104500002083d1440d00304a81d494108004400c0525008000e0b1034014001d907008d000c1c000c5104804450300030305560074003040c0c02c02c10201102c12621401407480502401000800c07414901c0c0301800c587c0344444900b4015151030602441543c80b402c03090f00b05c00480032072850 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 245992059 1250 245990809 245990813
    0x31407030b0909060f1302040e0a0515010e01260c030a0311190503030604150f091a0603040f0215070b100f05150409150905280603080d0b041d030309060c07 69
    0x300c45001b000c0c5001c202c1407440c040b0454495030884100103181c9002c07030307030011560725140c3e4542c5c2c0700c600400445c9000b078000155000300168058100c4209210215101c1020b0708082d00150054005011620a40c84041e00360344041250000343e0b8043e690322201ea081180b41203003002110586c100249070030300c0b8141c000c20307808012246c105508841c00640b08400400300c0c205042180c0c0402d500b0803900400149262032a000742510758414207486092a100504015007404140c401404500054015a00504080851a80c0c1c0e2010380d03086030400c0010340d60305c50040421160300d40001000313141008851904000040644406c6514030b1003071441d2511400b09010702e00c141190300e41c03684003004085031044505005000c0c8104140718900d4540242c801c084213030664903103418040d54400051548611520050729804441e0030319003800d00c10950007408451170810380c040e68071540c8186c3c1c00501c414041818200780003554407441d080c2005030601c1c1000f02a101510410004100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 245993309 1250 245992059 245992081
    0x10c02010815031606050a08100608040215160f05070b070f0f020103090f030e0f0a120308090102160b010602010b041107020603070309080a09051908120a031407030b090906 76
    0xd030081100181c0071003034500c1c00001c0d103084c040d907103040304a0b0071a4802003481507000000300f421080caa00d505595441c6c24411a070701c5880752040400080c004000300740145801218000c880e10440d203114100b10f0741d40050118034002d40000c0321440001a180b07010081c0c10b000450040003080100345c1001e116407150802038a00c0400206100300000b6802c1c01c580c004d0b88622540c0750460181006007515180107082c03a140301001c80e11580d07406980450b545803101c64902139410540f440700d04c0908503a02910b0b138450183c10a0f082d95001d0040180c2d0800c082d007940d00c8180101a60f180c0c5501d050800f0b421140c1202009000d00e050100c45400902c0ca60100c9940c00c0e8142c4103943d89590341d68080300103248000c0018100f110006892010b41d0f4000351075000c1d0b8000700c409030b050060b01d810044048485200d80091500001d501c0c07003410740c403503024140840844c1004030f1040c050445001791001c0c200e030a0740200c0d0b030b112040101c50400c2d468003503101c0b1030300f00181024100004240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 245994559 1250 245993309 245993311
    0x907050d030c03020a05070603020409050a0b010f0f0903050d05040f0905060a0b0c160e180102030f011208040f0603020d0617060105150c0601030c05041104060819090b090c0f010c020108 82
    0x207030a0000300544502014070130030040c00007a401105403070006803645001030207540076201d030054282c2490089542d414440c410480031300016101c0d01185011071000f0750f0103441051100d0207208002e280000400d00c2800851110b001580d1000e540d0350a00000201d9000e040d00401400c6103071408100c001d03210051414140c0d229002d41949401c02210391518160414280c00140100408001803981c9860340142c05401450000700b200d4a010301002c2c00c07800102e0f55400d11b41c80c1c02d001002120350028a006543d4000c0c01110326260302c0309403601c03002041f54450030000703034000340c40c601d045d00e50300c5510058052862a003100199540a1a940e15010b00602d4480c0358030002a1a025074000d0072242031070740c0102510780560303482c204402124980c1c03041c00d010728103041c0c610110044117001c07079094841c05d4651446c15140c2c0811400300003d500401e08280365030b00324000119080700c0c2c00c00e100d00e100310003c2c961001850f0030700c4951070502c80d0320340c1480107501c0010010703038002c210307070f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 245995809 1250 245994559 245994563
    0x70602030a1118040e031804020a05070512031f120b0604020913060305010f0501080a0b062d15270307090c0c030e0303070b061003090c0b120907050d 66
    0x9600c07034450300d1816008042151450310b000c031000071181160520150811460602214204101007140c0b540507106c0c4104c2d505691140800003403803a05180950217440c0c1011980b03001410181e507035460518248607100302c03210003407000c000c001c9a5000ea51821018454409454010918114101c2044180c1e020f0090145c012070300010350a484503070540c4d03501000105021148c801d80900840107004501081c0c42d107508060700032400c00d0241c028141221040c000070003041c1969210724500c00b4010f031155501c1440380240040c28034081c5400d0480d0590380c11281202c450a50800c102180f211007100c4a000040c40440c1d0001c04d041c03120034040140d801009400b00004000900300000350b00312610f0140f401700310950082c0d12403001e03240c0320301c0381d00d8402c0c1072612142019601d01a64038000d0064000c14005900390400c40150094074a0500300441c0342911a92400d890354032582000014040124540c0c100291044915422109800c05840c03003a0424011500c001001c0c080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 245997059 1250 245995809 245995811
    0xb07030305060301271106030601050a0f05070b0a0c0e010c0c210f0b071413060c03050c0609100c170c070305040f0e06010908011a0108090307060f0b0907020d050706 73
    0x1031020b4030f007900141c0064095602e03601c403010510000d40525001c0c03100988203200041803206150414008503030160700d0503152642400702d070440881d110110185400100101403001100090758030a8107401406440d101290465130003000034083d2446246950401281051800110300e1000840c2d043d03403140201910142004c0001c0080d0035a251002030491a901006105010700341079003900403051035540418440c1b400000040502036404a50320a01902d501000081d009500d1420414400d04107a820030400d10301490401c401101c0d883c5454110140d40c4a9032480b030300c02c0c0c400070819414980003000070001031803440382d0300505030001c00d0ba0001d010030500d402541910000d0007841c0d0504061901c88000041100003590104d000c00c14040001c01d0070340d4103009140102508007018103100d00604011613030124060402821030000700b106401048140c043c0f603800418295010901200047c2446002580102070000f150403184d01e42d541e0a610404607003c0c0e40d04598 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 245998309 1250 245997059 245997061
    0xb09130b16021203040f030e030607050a051e1803010f020c060a02030a1415090a0c0e102a1103010903080112061401060f090608100b07060e1e0c0a0b07030305 70
    0x901070f0329210500c240444800008400c2008001c908107040085510076583c00c81425628014541c0da5141550114007050046c0b011050a52140c000745c1559100018406140d1085083c1803405178003a9000320101001000c1e0304000c0e04003405010084800c00c1c404501d800d0b480b500d0716450700400743c40c0c06d14213500007000c1081402260040404040300d200c444640381000c840140c1c2d203050240480d801040c0400004960b8200362003000034034601c81d210008081e034240d04001d18407400c5185078040c000355401d185865803040c10114501227044800c1e05580c225400e0081d022000842040d02c41d1707050410723003000298070040c0300c0e0440f8000a0900ca00c10030706c0c035020001c1c003020143d40200c49170f5040000340c3c403640302000703007843d40c0c250b21014002e83c1c442c0821540e041c4201c0d4000784c1d4946010003080585503941c0180841801800c00048242d41400ca40d07050038148450382c034141c44681c07032100f00342c4010b000c001140754040340c07542c08603031038240c07240401e016485001c0d0615507628 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 245999559 1250 245998309 245998351
    0x20304080729060d020a031b0806071805060901090608070e09040b010e16090b0706020706020406050a141204060e0a060603060e010e07050307050402030c0f0403060b09130b 76
    0x906a0300090b03400380c20441c18045444000c0c21800c480000108031102100108180c0e080c0040c0401d2290380141158052a0031138442d0041e40d00d1180b45000392034080d0000251045e07003400300c180200c4080d901d920700c001101c030072490210b4141e00400c0c40391310204506999681c08c541301c4e03070031a00700e4204211346566207142500e4880e1004640c54200e034212041004000c0c0011005050301c0742c1d51280805511156078640803801019600c1021424001c0148402e000003c05400c440d032141030301628001700350b42c07003d05a030030170350009002c01d178003080d005092a007082d800340401e11004030721402d002c04003800110445001c0c002900711030340ca484401c0c401d0420701c2000825600981e043c08840d03235034a046001800c4105042c403095207800307183c90400ba00072600340100e42e0300030700501d039181c20107040000a5002800d01011407008100022480342c8000151000b10b0180000150341014501480014100145002c0070301c903a905010000444005246412010083c0c80c03242c07000c960 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 246000809 1250 245999559 245999573
    0x11130c0e061c200a0c032d030f0b0d0506060108060102030310090207020a05040227040603020102060f0601030219020606010314012106270203010b01020c150c0c0607060e010c11030409020304 84
    0x448400c41c29100000340d181160fa00000301601c3c2070720075540d182c102d40303200300103c21047c5003220b00360030400f41c503e43c0300307072140f10390400030000301c070f40c14006604010341c00061034107000305004580c01d4002c0da08115141d0f0700900078580c014800c3c0095895850420760941d0881c145002d81d002e001e502054500035526005480f038007400c006042150b448c5000c0d45890072103214850340ad82001d0302c680035106030707003400d0103450100c0354103800800954445180b00c0f5030310740d001004141059400d000500340710000304500c034105080ca8001d003500707081401c0010b096492800e00700510010240041010a003400070b140c0702600b005040e403500880c83e10303040700074010509001c40e440c0c1010825084034041101300740c5110748220001c000c158074072001a80c9403940607803441e034488c2000d805200740811010040041c01128005c0d80c081d0b5440780000741d001e4100841c1034a5080d621290f0050002d0244640040c0788107500b0b00c2114085484041542d274491802031300140f540201c081010402c176 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 246002059 1250 246000809 246000851
    0x9080307110c041a030706031a09180118031704030c080d200d20030c07060917030604050a050f0106120f060b0a120204030201050409050411130c0e061c 67
    0x700620902440c54041d0039500513078245282c2c1486402200720004901d402407044850001c2d8841c81d0306210100c1004100c92070100500440040c05a8609800340b0042840782104410a4000e00c48064606080041070140c80400c50303141c2140e16814003011079003000c0f20307488169100c0e4040b680e403625040c1d0f800207484400c00c00085041c00b00d900800c140981c101070610f44066260030081d450165200074662105036142d5030801500300041141e25409100502c0303482d01540c0c01040784501d0307681d000203441062280c0c042c1c294000c000d011180c40c0600569403c11100542030005040ca10b803101d0020070188503940c1032140b41e0584118503542a00103804101e492142003240c03940d1401892020390001e45c0001c0085e210100d011a04140c0340700345c0301038a4044e901c2c5401d00341882e41240007850081c03c03c0c0c2e44a00e0000c0019400e580d00103103586800c5601201142d990340c0751070003500a00e05d82030b10600c030b02010f200c0350349091506800100c0030500c100001c6804d1150703080115040030b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 246003309 1250 246002059 246002083
    0xa090203040602070218090f12030a051b16020f0f030c060306120105040c0f0b040f0302040b130c030b0307050301020a080a150302031504170406020a0303050402013f0908030711 78
    0x400c0c0c22580d840000b402085503c521f4462003901c072004241683c5c140c503096042e1071800746110a001050400241d41d1100741d015055208400300c3c1805050320501c04e4104000d080302e41d051140c01401181402c1412040c44039044d00e9001151500030000307038544400380503150141c14040000303100e030382c0c4500e442002c1040e82c000800c20b9041604040541885500603040440e03100400092644030840c110750403200e410100030025411603003000050b000d000c4005034000c2410321301d10352922192090806c0c041e0a51400501c442202040c07508080c000d91006110380d10500c1010f04154208490740c0e40900341d40780c00591800c400040e10b9051256400c042d40511a01d124568054040141503001e02d0192400c4128140044030000040c400c50040d400113030000e51100d00000d0180e000301d500248141000c83c80c040712400b030383c0e0701103000111005031300b544000f010900000900c0911280ca01c0c4030700521408070b480c1c0311080e582c4405400c5030100100080034218200d400d1109aa80c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 246004559 1250 246003309 246003319
    0x1a15060403030c140a021c0515010e070314090c090a0207080705030d06120c1e0812120c03070c120e03030d06030303050709151404030203120a1701050a0902030406020702 75
    0x380c03203081c024004030510300c0403a444035100c1844d02d0081d000080f80803940340d0040c99910202c04140e081112080d074117004488038400c0c09208940d030b00c0c100000502030030b030800481c80300746081c403001000e441d0191071031640e507044501402171842000c20728013003840c4242c54038102174482c514410300138419030b03501414015012440108100740070000382480b41942005100f02c0e601d030300c101802c807508090003c1c07024081140170000e84d0705441c03054040507a5440d5041d10203170359410f80c80c10300d00b00046201401c1800510003407074580d100307281508101c40080d0181140307440310014182c0099883d002d001c0449003403000c910303948584a1904000f0026042d00c0e102e80010707a40002501e81400110086402c0000003080a480b60150104407140030f028585104003500c4140e69400000040000e03500d000c10001c005a1420490b60200044840e202c641d10781000d00f0082080384c030700105001a140180c010403c41d035443d00c41a042d43e001903030051b030300d80f1075141000082c415068025081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 246005809 1250 246004559 246004567
    0x706140c07030506040201110d0f0e030118080d06270b12010f0207150c08061c0c030f1209060210020f0d1a0109170325052a010306031a1506 62
    0x3c0340201d01280550700c03e0700c900e603019a0085480e512003003440305100c00240c0341c07406030304030307a1062850100c035400250000424800c03007030390b0381d900b095220003d550a01c00010a8a0030009520654000b808046030144025401200301400100052000f0341240c1d00d40d0690501580c9404c0d104d000355a00c0030003000f070a00d90403400310282d0814031096858a02070742903800a61240d0040311190307501c69071a82400e40c7d4a4040007030034000358401c1050a0142661a0f0000e6002061100954040c612800ba440190700e40810a508050f84900401c081a141023110640000f00d222400c0111400580c4818401020100da401010805049942400f1011008a00c98590040501420fa03100d007100f42d112210ba5800c07554651441d003184e4010070000324004440d003100b00d50804014810122001c164669520b0400301144c200080001844045404503242da507d1000c0c0380282400c2c003000b4030b540c0f20081c841c11100d080820358201c51002414000007034010000d440c0c0010880341d16 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 246007059 1250 246005809 246005813
    0x13060e07020d0201060b0319092d020a150503010e0403021204090c021b0d020904020402040801240806060109211b030209010b1201030807080d180b0a0e0706140c0703 73
    0x901c07440c10b5102d00c003551a01c1e90104201d000c10007200c2c401c4110070b19145050524450410042c0b156020030347e620402c0d0031074100c40701c41e8100c02200e4a0160031000b041160203004120090340c05030301c0001e42005c0307022022a030780d401000b90381c116002500c880b00e0790342d01c90405074100b00000020003080c510015001c00d400c800ca510001d41918581d081b9000107445020542ea8010305040069120600c03603001c00062170101255540705202500242c28161b9898895080d19030940e800303612501711300c1e17412092580c91081d4500800c080310081c446070800e0070020700302040c5030045d005400500007c000b1950741409001400592110503442014100170b0f41a40381d00b100d0000b00d210f2446a8000a619014001543e841704030b1011594950b91a50792a050745a10003202114010010312201f080d5541521400740e00201910900e800c02e010780c64034240071070004000c0c90701c00c1e151891a40e181c140004003682507945a040c2604819075880b00680349009044c40410766100b16000807007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 246008309 1250 246007059 246007063
    0x201050309070e010b03160206091b1c080318280303140705030a0e0c030c091e0f160507121d03030c0d021e06040201030f1107050a03020d0e0a030213060e0702 70
    0x440b8075080d80d00061000921f03075080ba00e40f030007511100042d03408501c62007000d1818a25400403440300525441d210888002903403030206980e0b10075a4480c2c0e0101c01c0101c400310b8000c0040c001c80707141001d8030441290001d01c0d04001c00e41507140b801840b00c0440b8001b014001c0c0d10400c511148031407180034501d4403080040240c2c0c012036803100d10904044600d02c6141e8000342d1300210000c0100a08506880f0405115420900502c00c540300046804190445014041d62034083e400004680e50a880c044140382e0030101880c441d1005c10004101c84030100702200f04803119084035203061002e8480380013100303146200e5075101d40d5140c00001042c06240b80c0000d452500103003103070217951b695a540c00e401e0020032201800701c1590b130000d07000940103600c26030100c00d031103032071020010305403040f2041048150000d01c012103196105641d400182b40d01000100300e100d4003490a107101041d000c3c040340ca403c08921009005a1007050b40c0c90003180c190700508040e180100b90000241f03030001e0029 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 246009559 1250 246008309 246008311
    0xf01060e06430308010509370b010804080306040506130e2b02030a1b06060b070308060a080703030e130203090a121412040c0b0c030a0809070807030201050309070e010b03 75
    0x14440d18050b980d04803600b0a00141e00c0981e0ba0541c4800340c40d68a44410710404080c000c00040c210841c040c29440c0700300c080002140451004c1260000c40d8021030481c00484400040306418841030b0420000010440c100b20ba40c40241030f0750106240c0c641d1000304004400480c050110142052070703880c00480009441401040c0401000722402440d8141449944000b233628005070810056541c640e40036205090000c1c44c00c04da040000d00f51a04c4e02c104417a81c9802c40c0e0060000003e0030b409160380008029000b0300105c1c0e040e101c1900d4038491650b555400c0c80014280410800106025555810a800d1099a00405540d00c2c03510b080990384412403408121a501200e200082e4021710502c00140c02c003907195103d901e0311020820071480c12400800c103d640c0c090b25400880c5090205003c1e0000308804030007181c035420021000b0380f04840c0100030701001da00c0300c07408021507003000500d10102d0b0f8080c288203691351100c400880c100801c5810900524220000009075841490011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 246010809 1250 246009559 246009637
    0x709110c10020412081605120a080a0c0906120216120809030306090a09150c050405031b100f11030a09060807111f0207050f031b03030f01060e06 64
    0x1030380070921404a05000ca000714065098440404282800003400342d10003490f101d2403402d00d800c4800041c0d0f6070a460300e010301880c02520080418040c0ca01038108407615000b0941400900c99044d1900c4020594101c074402c1004108004401c0c0030010392a504030f842d00c48d442c140390500001141410f000344034000f9000310011b40c1c4d950010307424031800300986c0c7c020203004020b030203c0c1d100d158842c00079268003801500d490000e50340b1301140c14a203100b1504480c9164550399216490a01054201802c81c030b901d4003168003a00001c1c91a584407030324042014460704050703c488006681c2107a01041c00c1c4e000e000144000214503103c0b41e08185d201d012244203a6821326550385070348003119250180d030303d070701c1c1c2950000400401e02500c22000300e81d0900c00401c01400c003e0740ea241c0d1440d240c0c040521150700d4000096003454441c0404d124144106000700861460030440710780358036190148a03240c01c0285815100540355100401c8900c101c01115000d40d055a1640e028081420300d1051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 246012059 1250 246010809 246010813
    0xb130602030301030c03080a030b0301050f060906010f2115090555141006020a08030a0e03040e0f060f04060b090d0c091806150e060d03020709110c 65
    0x4001502440081100d041e45d41c00040c940d841703840c46c0d49040154000c400480203142c5c81c0c0302c0d4002507813024800e00d403040d8010b22080c0c45a09129041c002c901c40701030181410032407542e10031074200f6000451808007064840140c0107a00c4000c221000820100802d54000e682441002482060390340002d4007400080c08022850340409100d4440706550311030100c901c04515504000200407100a4203000d81e07c5401c501040c03804204600440d5140040b50280d4000002848a503000c026010000307400b89000038000c0300691749810440303000c02007650138140d40b2001c030b03001503c0060054400401200c1030098250401c9600407000f2941181c80901901826074400341600e031500030a02128141d04445180034164400d011007101c4001059814a080003000102e503080c030701c10f80d501c0035520381407002441c2c8217103040380070b849404500680117541b161041c002d80c2d017511780d515040340b406c07202d0040c030001c18038060b03040c000254442e0703400c149844110707140300101c2c6000300381448400c02 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 246013309 1250 246012059 246012097
    0x120b06040203011202060306010c0c090e1e0606190302090103030e040525140f07030201140a0605010806090915180f071a030421020a150902010e150909010b 69
    0x205020807070000f40300d4a408004610601805030030300034000d580000d01032400210203030494940c100707100070b623031701102207250744170322140031154284045100f0020581401860030101c0f9105952107a026101c4d51194402610708181c403000390f4400720065034060b111401075a03581c140500b440a064188034040c90802001680c000000048aa0300c840c101302109038821004c0003c66140f00d016103080340403a0100289240c0d00070110150525911940c00494080980321054a82c070001401312145242014000c0c0403581c0c1029400e6402181601c60000507554144e0311440c08000744103001c0c5050651050002081080c0c9042001d480314030b04961005aa240840e907889446100e2100804201084d80000100200c02541c0041c06403c178234154042c10a5658284900d0155000140c1c4c4910b44e0081046120001c4c00c1c0000502c42081000807903580001e484014809042da106e11044015030b44a201d001c8203440581e280540040c2c0c5568445100c0581584074604042401c103041c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 246014559 1250 246013309 246013321
    0x7080f0c07170312090c0108011a0904021201140901030506130f02040e070501020c10080a0c020c0a0602010f0513030203031302060d1d120408030a0e2407110109260f07120b 76
    0x4601b54960010794590700f6a80c6440d41c4441a04200381075138440c0c400400c048a440c1c0e8a07800a0648482c4c4000529003e501d00000b010342038903014220b81c002c09400004002240002c184154440b1003c010714030060414a0640040c52840308000e60041c50084901c600d840d001604000ba1030303083e000c640301c00c54134400704003002546400b24400a41074000081006003250061440b402c954011211906c2d10800040d04003404d0f60442001030b951252410b160191500600b41c01828030040428440344a8600a4907803200038205000289d5031000701046440c2c81d0103c032020300c078016040101e101000d0008011a4035210038503000e01c650281c0c510281c0d03031401242c0448200328011480c048c071290781644d48a0702804466031001d00034017450001180315000b114502c4410740156602c0c0f07414982040b401c6041c1c0700f51410132410709020701c01801c05210340d04170310310310140000b182450400c04a2418544042c1c000d000d0181e000f00040c3c015043d105078440a20407d403505580d41d0310 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 246015809 1250 246014559 246014563
    0x50103020315040e0c090117190210050702010903050607020a11180415020c0102030a0903031b050a110c12060f010e09060a0903020f0610050111010207080f0c0717031209 75
    0x240e440b00c91955000208806600d066400b80300e044c41e00500ba0307180030400f00000780c91064260f00034004222464034a1840d181d050005226551104000003030700c0c1c0d09a00481c0d000300d5841802000e0103c00605030042d60700810362480159800001c490683c600504000c0d11850002d00844418110b90700d007858503d0451200c1001d15200800c0c210b1b81d40e1282c0301c0042592034031070380310f900c5507080044690408003030000b140b003803240d10004103a50905140041c22030b03100c9603903c46010303091558502156400412920403403024075080003012400725240d81410400c00b0629440a90841f1550352000c0102c3d10612840f1401c10b642070a070790315885284043d0701155903c20a8204200052500106522201c40301c2d00901c11241c1d140480340c00203181007002d0722a030385a00c00c030500800c10f82d80e000c41c0a466003061400254185070f100d81e034807030050040c10305201440d80d01050965440301c0402000005100f40100740f2105100983e0081d241d5200c0710720b200440b941c01002656100300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 246017059 1250 246015809 246015811
    0x9050309010e090108121605060a1409010207110111030d0204080a020405060a06050702040903050c062811030a02090402120f0a0501060306150807140406051201060c050d050703030f18020405010501030203 90
    0x141d0800342440e8014145142459801f03564002c40c4410303002c0500001c00c104010640c4514605a400180d03100c03600518144010002c0402c1e00c90781c010846107001a0101c1071446140d20f081c00c02100450300c0c4d00398181903000e00c004000d417403880850001044403000031081d001d21f000307440402803522103401b80610729072280500004210200200b4005080603881088258004d2510310b091040180f062418810140e03500c1804017440172048144403600481806a1281c40c1010003180070048a4544580001403024024640c0421700403116196501101c5c00b12441d544070811034030b80a900310158250903140d0f040e01c2490b00c7c001080e00e502070b1156505444050405501d251020f401c00c4074140801813000c0d04000754a03601c1c0c0ba514941d400648003409080c1c40301030300c41049100e90141040142d020004004a260301c13140483c3c030101c0c410a04c4202881c02540e20586410181e004c0d0852000444010f4907090421204403507840385d461560f031084600384016640c8500460580c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 246018309 1250 246017059 246017069
    0x509060d020108011e030b0a0c08100f05270c03010f0618031e060c0f08090c100c06060f1211190b07030e0411030f010b031003061d0109050309010e0901 67
    0x603c400501400054407410f0140c014040f01a10350315480303075102c102d03040741a5000d4412580300c81200031495000145c081c0c1c0204401c441584061030b001102e00603c0f150303c6400c2c000d140c1c0402104510f5420b100c50b0805004040103d0b0f01c0d403c11a400e40025882441050f03c6e081032400b020a000307210308404130503445140b60340c9500d5030440c5c5a140241d07251040403a04403080290107800608a80038041c0e5256454580e4812409030a401400c8507400410150302a0400141e0703865a030780701001c030b40143c041403074420480d04040c900340008007910b400060b84010754a10005035a524034140c0d6424500c6410441c2242e0444001c1c400504440f00c031142d00201d40140078080441c41c0e9011300700c5540280740235400390000b03601107400c940c4204049176450400000b0086048406071407203004011003807140f8550b150508402c1400000d0713000003000d030b640720380d101201c24214032000c1501c0d02c5984000c00c8003030700c0c42c50075540c3c0754410b54050780400c00141c010440d0345805441c4d40c1c101c0d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 246019559 1250 246018309 246018317
    0x103030801060e0303070f030210180f031116140a0e060f060d20120f0702030706020d09080a0f02010b010c05100504080412080301050a23010c02011103130509060d0201 74
    0x64209a0b0075501a48150002034043c4028003801011850313000550b082c00703000781c015003482d168445080d401d0302c8600c02c030010100b0301c401203c80026140c0104a0210360107183c0072a8072940040d15604190f2000011b00143d030907014080b03004003405001c1d02c5c9105d01210281c0710240daa904410903020101c86056006542088080d46070401030020042d02d5031141001542c039140761030100c610304844007500703040d90000c201d0380244144049801c0e0481d801c0b0341001811316081c40c2c000c1d0b6074412907030000c04854020584101342102c60700090000c0350301842d00350f114411050014002e0240c842040700541c24007844031b07180d50042c55040e069640203406869451081050440905400303042180d4a038001c00000070281d8911040c64943c030b1003645410b03a2035140904018604025420003040042c01c50103112202c0fa10398a03241e0350038400e00b480309403910b1900050302c0b010001420701d0360600002602d103850740102901442501d00c100d925000075151001802010003000c44001c1c003003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 246020809 1250 246019559 246019561
    0x206040b032e03030c12030f0f020403020a060c020904060e0115120b1b0403021504271b0e0904020a090e010204030201140703050301031410060f090507110c0609060d0203090d020f0601030308 84
    0x1b041c0c40b8101c1d200b40c440700341000300300c50411a003410100c4450b00400c44010368081401d10841c900042004d00403d814500502040c21075000180306540250009100c10754403919641a14002e400c020f131190301d0404203100072030780c40f8404450208002005c0741c90a0708040010baa011a890601c0880ca2507040401e0a0904503030900031407d00c000d88542d451103086c4000961440e00151288031401d010820041f00a09603080006a65529450704d044110001d840004250b21460158560404071403170b841549450010950309242a048240c1c1a030820003030b8442c00e10150010030881c1d01c01c0c1d8903854401010a40a495070044441c0100022403c000400124448100094000c2d8050301078811510441c803039a8110b850716445481c0e4250018810010780ca101d00c200740d03005006003840c085140003001000e4407444078460b1a80705190100d8154040d4403540c060b242580c002400455490030030169180d6120102e8030041c005100380140c0b6062500d0106005040707940c551985181 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 246022059 1250 246020809 246020813
    0x90302030a120204051c020a080102030f0403051b060c1c0207080901110f060a05270d05031324110a080f041e060c110c0306130206040b032e03030c 65
    0x411020080b0340d80c8030076003d0202040e5603446118200c4000640c10301d002e0503691034814406001143da101145691043c02001050703a0b400840960040c2c0c0351403e981c2d1040d15030300811480800c0c1c900320351144140d100304010044001e00034403448200040c0d02140030007501d0104140d10514000a14080050000074240e5005040000d0b1000a2009807241050018241d5140c8001100d000d11059252410300c0740f031a42d60411941907100d2050503030010020b1003c0030b65135241000640080140000010315003d002c0104550328662102d40782150504615a5080e03401c400b100403d0313054900450b5071101200442103420b43c3c1e600c7d03180e4664960314600307a84100400140161420390244654001c81d004101e0b80d402d91610591000a40d49414180200140c0711000c502c0c401e40d0003e8001c1c0c1c2266030000311903900c1010401d4928801c0e00c03520110306d42c0e0061390711000d8800700100900000308148500342840303400750b013000070171a101658614820000d44c400640031078240003003a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 246023309 1250 246022059 246022067
    0x9050a06140306031509030a0e1f2a060605130506220f05070503070206070810031e0f151503020901050915030714010212041a0304050c060a050901030b0301090302030a 74
    0x30344084018251680707070404907405d074184041102e041481381c1002a40c5500540c00003000c8642950030743d0540309102c948400c201010005103414000d20840c1500762100c081212a0881151039400c1011a101082d2030484013518607400381600c5000000b0314007242d00352520410313118400c024035003184150220035184517074030b60b0300a40c0b48080d1102c0605454500718040d081c003c09480d90344070fa59241001c0c0080c00c00038090034071707400c0001c03074400c0c4400000009201d2090f01d4001480c51100e10f0b2110410241c0203202c2c42c010f0003c050f82c03501e5070038000c01c010a0308a4010349402403042c180203080310006072a00c0c2c00001d502c8041040140a6407c001220380d0b4056640d603d9000200f80401c0042c2c5800501d60112901d158001c0ba106101d590500643c1c0c4400341742c04403079041508246030507990b00f001c10f00c04900c00300003000080901808000c1c212030360310050f0803180c1c0c800358494010102c0d031110754114042418a104250f042c10305200d0310a135103401d9400f5604020030003500711 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 246024559 1250 246023309 246023311
    0x303040206070611070b1e042102011b03060807170a03030906180501050106021002070c0302010e01050d06091a010c0c06030c090f080705090906090703080721030c09050a061403 78
    0x1480b2a81d482154248104d895001402d115028840302c40329480c0170300c900740140c101941055102541c810131301c00020203602e14074072807400d20000b495000d96080e40480c01003040c50b2039005106c01c6007400c14170040d0113900010039a4292820f444500351601064201c004910340e5400c00741d0b11090200001c00d1003a480a694103100f0f200115040c412148185a982c40c038250a84250755504010040340340c040103038070740403a00d00400754107161541d2141c4c0d030a00032502c4040d040c8001c282e440100d680c030440882e1528081c1c0501080320030348640071758000b442036211500d6000d1501c00c00d865150f0041c11280ca40560180f0b6511850b030800e6000c8020705079000214003031001500340851581c1d10410381c1c0010700900e0004042881c0f40c001000707413020000d444500d16421076424020840170120354002a40d03042410705640b0710161520700c0340c8900c912243d00380702d17044605000d00c0c9a030640182c0318440c0640e841a41d03035074840d000c01c01c850380342e88076201c00310b800400c0c0c0d0319141010030061 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 246025809 1250 246024559 246024563
    0x304060c03050c011b02070f0506030406090302120f0d23160e1507060507090b0a030b0f06030a1410080304091e020a020718020406120e010e0f10060b0c030304020607 73
    0x890401d00f2200119003980c25510f02c0e0003080d82c400c0034030414a641000001e00030070084144542203490040803848a201c00303400a06032a80b81c05082081c14000c0284038844d0391003c82c11561580141c090751203c4d0045000301d00b0850403c2d100031401a0000c0710310031400302c038203d401160b4032107030500c549030710941d03007014184544210f2541080d5241010948401d900180461307036440945060402c1b00c200410750000e000c1144001c0c4881c413000c0090340c01031182400c00141900c501c0d000204550122600d9a922007800020000f001c2495049890042d036000d2400119889401c10458881c506c0c0c02030070926070040c041040502580d0300b001c07003403403103641c200b0814890128800051f0380c800150f210150b440103104115a2101400d19080300461940c210700300750414034018090300114461007504c1e03494559528080c00294807100e0420694000c440c0e030a00d001038000c4e11038032000c0d0105a441d107800c500103400034000c000c480c008607284c809589555210303801c21415803c00801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 246027059 1250 246025809 246025817
    0x5030720011d0a0302060c1603050d240e09060c0d09020604090c0e030715090b090f0301090c08010c030608120c10020c03090f030c01020619150b090f010f020304060c03 74
    0x703500845020a18080c0080300d101c0c0c05010f03916264140079282603030103003e40150035800c0281185101e00c0d000c1082000d0390620709581d542c08d6100042001d41b040c00d141d171301c49400c02101c0c0f282d1017200d0300d285000c4070044202c4425a80c4c4c0c41100c1e0303882e10421144a8280d020420a08180c08015800407015510050004e4201510340307420702d0445080c5030059011510140300080545410400b00009044120124012a020100090078581a80b04e00400103901080f540030694403165001c4c101c10300900208000c1c0c0b01c1d0b041410742d810041c4201c408a529010750501014400e0191300141c40c0b40d00c00401041c0089111541940d1182005162601940c041c0402d00243c0d80001e0444818000085894070b01410410a02100741a812442984100503082951340c02051a03a48a41e030000c4c0f440140e84540045000341c0724a03d9040347c0d00065484c085806076440c0d0180c80d5400c001e031043c1c0d480211420044d20300414580704400981d00902c800c020305841110100c0c200c07072203803130 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 246028309 1250 246027059 246027071
    0x90a0e0a08120103050c0306070f0516020d06060311190e0402030c06030f040c0b1c05150402070b040605060603060d110301020d0c080906091207060908092e0503072001 74
    0x40740003080d044842d041c210580c801004000b0b221041059803010031040300074101e6400d012002502e8482c81805610500502180300c01001160700d2000c1c0c01b040d00a481c0314a0883c0074500315008003698001100d0a409203403c0711518109081c0600b0103d81514071f000e005420702e1980c0016480003403049a0511886180300803035215680a10300a45200900e00a981050324040391200752542207450204003c0c8040c042d440d205284c54410140741c441c00080036124010341d8880c804803001c2854006000044040c00c10824030401d51080d0b0154004000b0342d180c050400c0840e21098501a0b4440b581450fa03002007a00710142042d10b240c0140010b140250030303138089040e20b910b03162031000f10b8110030802c00c1107030040c03003032951201d03801020b01400f10402104404a014086015000680d00c0049000300001d030001c4818000000f0400e001c10b0b01020900d030b178001e40460300700040303a42e20382440400724014000d6900400d8a038a941440d8091010b0741c415010300408011450764883c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 246029559 1250 246028309 246028313
    0x90d020f0a03080a0207080c06030f04210f09080312041707060504060c080708012709050f0102040323100b031c0503070f0804020307030206070507080303131202010b090a0e0a 77
    0x19210004600c601070040e1144d0a039880039003005001c1c5c0c440c0066400c01d5007450300030f54559080780da0082c1c24594180403603e460404200d0540100403000907035041010040c0c40d180c02016400d545602d80d83d800e0501603e034140c0a4583c00b4002805a510b01c9603070202d400075040d00f20981115101e030246505000c015129181662001d44007a01c00341d03510444640e100d0f90004103158481c0e040d040c8075038554034000d00c80c111400d0460000882c0c80e440160078429940f07607003040c10307050740000444070810080c00d203440c003d60080c4811079202c1000d240c882c11081c2060011010225050041c0c00e02c50044203400000c2c2c0848040729038140582d4030351068480c90000b00e400002e806945180e281e03e000d6401400940c0c0c400c0055090123001d00c02c00c001a034001484000380d9030b050b40c103651a1407061038014500103041c0c2103c45603000100330440b800240d14201d140c0e06000d440c1d250854814600c0c02da0880344164481e54000b281d100010355080b2558101188034402981194100d4100d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 246030809 1250 246029559 246029569
    0x6060504382809180c03020922050c0f01170c130b1218010e030d09030c020306010305061014060316021c051b1c0c06110d021b12090d020f 61
    0x142d00200c65012611040c0310155040c4900c494000d001210046400134540752a030400200c0d02c00248600e550308001103019540d008403c401510342041120f140402d840d100f602c500000780307a1740c01100c200218030800e44c400c0d1508090042c1a02a01c2095142c2d900d030104141d1008008d0f82c45203e003a14005816143e680041c00800c819184c07502c5c0506194081e40c80403031480c005600980c0c102018282a180c010080702d00704410398000168101483c981554549042400654117020316400081800400b198403480f0b05000460f0f11625600c1d081c0e541e00c00184410b03650b81040091001460403080342d01d2900e02d62082d030045aa521700c44462000700d40c101d12001d00c00150021510120048040000c101b5044600000e40f8029088076032a100c03915101c1841070401a10000c40390900620380d1188900508100304103030303110440c42141c0081d6015454420642ea80121071200c0e006000c2110306810724941041450b041030481003004040c151401aa8450303201c1c0000003059442c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 246032059 1250 246030809 246030859
    0x60d0c021501030303020c07151413080d0804060c030504111315060c0302010b0303030114060f12010320010207030b010b0a0509060706091502090d0f0312090606050438 74
    0x1003541c02598034400040c0e528107103031296018100c6200c00041030801d0715001070302b445140d00100314031911500301c0c1d07035090705e5042c0c0d9510022041c0030b14a1907107002e41d8401203a621440c001d00302884400f0312904120212801110041d0103890a250b040c4a00d14003200c00040c4003803415004140107244511041c0341d001c40703510200c0030600100807402050307028042d00b242103404078040c40c00c5601d0310091080b801501301d90340740f00381000102e580400394a2019a00f0200e03442c6031468582d13131a4a04100c03000c0300d20b502002d00030800403001445602c0095024190303039020710099070300e910b0b0010510090b0401c0101c1400c0c440184040d440c90b840d04809004507038003a41d80400c0994140c140300b441840d261429424450040180c001c0d80c1d114008280c24090340800719841618044c1011540080300030711b00300e60141001c11181c2440f5080d000031058800480d01009a40c4000f2405140c1d40a44aa010302c40c82c0c105c202c207081c030b010112100107101c2c00035100b250310956090802c104807a0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 246033309 1250 246032059 246032063
    0x10e0d0e030c090c090907050d0f0902011b1104020c0a0f0f0303150b070213230103060f020403051009170406050c010c050c0312060f04140402030d0e060d0c02150103 73
    0x4100312101441d042144185080302074a03100703a00d003003036445091136104059604d4002c0310325402141c4480e01c00c20840d034009654070b0003000240714020701d01001d400510b40c00d0b800101c295504400705100401c030048225800786000148040310814000650880801d80d0164000c4a00700404111840f0070002500d1140c10260040865450082c0444940c0752035034298004161013404201d8151080740e06041c3c04442d402e005a0054502130094081421100a2200c5032400c4150090f91005028182d92140b8001c0c403209001d0b041e010105e010743d02c03020b0b02030750000000c1000d54170385501c40b03807130940504600d01005000b1320003030640351700c03541c40305000030070029040250308801e100304000c030503c61a00c1f5160880001e03002d82d881c0291a44c4008800c1d076240400d40607230720200c0c4030030b15640240007844a401e81c1c600381c82000c101100c086e4041d004004404207021302c51940850007000c003d0845003818410b000c0d25004106440c0c020096108010f109100d0381f0b00e0751017a1f40214 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 246034559 1250 246033309 246033317
    0xc04120f080c031c0c020f06010e060d0c0e0714030603031602190b0d05090705091611060106020708061b04030b070c02090f091e030d1808040803090a06090302060901050903010e0d 79
    0x4613000c0b00c08801c03030b00c60340181c408640141c0c840703860003030b008580345046890744140da802580b20200000c1c4a8040554010320901214500061440e028615584945465264034038219940c20281d041403000321000d55164004000b54107206240300000111030f40094150801108a0a88991903460640200901c8800450040072070070641c0100b41d4860441006446514a8000801c0c0000e03006012003801c801c459a5100351144503803080783d1007a03980d071301b19000d40d603641034040e45865050003000b03a203005e1a00007a07840c0c0088000c11414480c1d185810780392515549801821b00300140c9110200a496050703540907a441c04081406162400c2048034903003071660005291408a4035240581104074886255036900801070316940f4541020119518402405980400304848801422000f0100e004107000300e0000c0641103a1000fa501d0000080c0c64107416662031446201c0258401010000d58209510401c05004600000360000c80d0420b00350301964108604c03001144001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 246035809 1250 246034559 246034597
    0x5100203040f08010b0f0603060d0b070f0f05040b160f1a0f0708070e0603060102012003041a0108070605090f09250c0f06050403020f07080705090c04120f080c03 71
    0x20b00c9420003000c020000344008100080d00000840c452540501c0b02d1403081e1004800514240c43d01500304175400da1100c20415103140c040750160500c8804140480040d00714582c03000c0040c002c0703040f582a2150241c1c160308105050108070282801020121440100380a8110005801c0442402480c6007d40110380d14580420110304c9030784c004010004000344481441a040c4c1c010100c402c40100075130b04d65039250386000050340035003110044983c0f008400e8004a00c4840c0040c0914003c6114602851401d40c4020000004003001e00030b100c2c5942040d5800c000d81ca004000500312880080e10808464251500084a20b03100700ca99001d04c0001a881e4113400c5140e0300348070440da42d14140080510100e803070381f01402c400030302e00916269450b80401c06040c020004103d101005800b1203810a8850700001d480f03100c24800c0d0fa0044c1000b4000c00c02c4181d070b400544094405060410150030490384525400c8000c220041d00c03c01c03410001074444c500300b400107003070010340c5856400700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 246037059 1250 246035809 246035819
    0x507090b03160b180a050d03021b01020a02061204030e0901090c03060501090b09091b0c03130b120c0d1d010c120e0319020c04060603050f1305071502070510020304 72
    0x144000ca180c0207440c401102e03414040300e4039060554a0100e007160a1044140048003c549800c0541d003200e5803240c591030000c410194006440c440c043c4500c1a07d01c2d5801f0329100681e550f96404900a5010005104161165016040441d0710a00a20748250f6043d020004100d108c11f003a00862344044d203440c601100300b6014010040144400e280c038006041c83e0811085081c015240014440c2c6480000b0402a184c1d6005203600c880041021071b6443e049922031980e40e600c04618100319046c841000a4020080c900355100c0d0001541c0c091020394503200d402c4440d60082601030380681d5101c4500c103009a06030341c4070912041500000034042000c1c180604800f104003040e4013918140030100c00d01580100654160400e008102031300059000070681c01c00f003001010b0364000d480c1c0400094102d41c1a00114014120445026619284d90300351b00101e2201800140c40c59020b0321040204604c9412100032400c050320603640c8003601d450019044440c03000b1414010790000c80c0c2408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 246038309 1250 246037059 246037063
    0x6030e060c180a0305031305031e0a0204021b0d031a06070210080c1605010903030e01020a0c021002030409090515061806090406060e09010911061213030203070507090b03 75
    0x10921008001400c0078a00a40014482d100304a406003000b490020112100d031911900c000c0910f61100982e0f8a585161000b0362400320f01d0700c41d042c0300b441a0300850480112031040c0302a8490180c006e044243e24503001d20020b94010242001c0542040d0306020740140c090120058003002a03401294019401c0158000802c0da070b500c0034880c550401088005a680261400120056041407401c0350354a0440000d035029511460403109540d603248000c1140c103502a00f1494840c2d00c0400c860f42502040a0803805004d00050205018105441c05840c01f8555130307104851500c112440d003a207403142d000503203d101c2c00854156000012043c41100005581c1c0c0c2c1c42902951103031801c00c0c0c10b1740c00300d00100016040d0703806003400302c001c101440318030f8001c0c402800303a08600c405c1609000c294607001305652401611038180b02410b08a81389030010442d80500800d144503c441c0c1c60740c84151245c0c6d00e0b10700307084003940b00c10000381c4001041402002d0003020800000116624804140341c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 246039559 1250 246038309 246038321
    0x509060a0e07060206040b0a021e19092909031912080601050409051b0c0a0302010f020922240f050303040620010e010608100608061e04060917040603 66
    0x40c500b0b0b080181c003846440d60000b00164001d03000640701110392155030700b1341d00922500900b000144c400310020100c00354004010030030140c500104c20403810742d0f0481101e00c080b09000d4003c0189484601d88041c1c80019101082000b4444d070144c5448072001c0082d180604085021203001040e520300020f0100c0c40b050412070040d07905040c445403800c140002d00c2ca11070b50050392802981c0320086013483d40d08607900d44607062001803051380e443e021201c2d0750365190780c2d840490041d800c200301070484031498026564084406030504003e41601d1482381611250b020300c01c0307013450313aa0703440f06a184686004c151200001f40345580c140c0e400c2008240b01200c046d00800c0c000d900c2000200300007503104016150305104181910f1007508c03107012190240c60440c024521540c28484042a402c4020401d041031581408040000996440c03890761903040403941c000e0b20390130b01c150b0785130007500101e0429801841400d000410318519540d032380720005040e0004207041800f050a1260705e070944500c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 246040809 1250 246039559 246039581
    0x61b180913111c031d0d0b0f09010e03190c0803150a090504110d0206070b0106031a0406080c0108070c17040501030507230901020a0803190b0a120201030218040509060a 74
    0x10700c100490041014003d0501c0c2c0c01410418411811440070080503180c0f2007904009000b0300300307881c2da03003081889402e041e03e5601c02c003403001022400e11201407052032440d01181014500b08005200d2148680340034201410500100080800014107018008d5200e1003001c1c80514294000348e042c0440c01640b41c00071410645010180400710f90000310103440190104c4902c1c0c4224840d2022803460f000da07a0000742102d1248002103441905034004800c801e4042124020481c0c02d68104030545800344603010031a0800b141c2e00b03d00e948501c146ca03078042040e00700440c10750255a0f41c10140d00c0314031000160060040b5040c44150b0303150003070304d40240192428400011143d220141c040d00c915200a25082000071750985a900900c407074525603070024107280d100c0c600f4050400c10000613481e11081280b400607110028a840f001741c2003516002e4503034800500340d07580154001e40c04609850313015a1b13003001410041e6075900815101d00030240240c61179041048001e015100f41c3d4040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 246042059 1250 246040809 246040819
    0x1802120108031c0207021c030c05010e0c010504031e08070b0901050f0114041e0e0715050406080f0c040504060305100506030c0105180a0e040305040f08061b18091311 73
    0x8104a03940802c0111026044680c3d00141d0b261030034400944c00000d50718070012034008403140282403603002000442554060002402402810803503180c58400303d500075804100c040c841480030603074812581081c80301c001d44a4484911644030642c0326044880e04650002008003007080510080c0580c940000c400001c59450754100394100c80e5000071512a20300a030317690052512000805449240050840c00080158002d0071000e2034a802d00d500600741031448515811040c0b5203c1d408503011070b0b50503500e00503541c5800b04220840c0c000900200d9980d030040c0030110346550f03588a07003c01140f20314000e000c2852601c54440c01e50385c0c014031480c40703030301310144028041e604070b800c44004541c50306e404c40441009500007040400b051304070031024180c900412040641080040c02a10285c4011800441d5030b407040d50303601c140c00c540303115030840c0c0104000c40f45c1585501a0458450b50074a141c0280103110210310601001c488009921038800001e030180000348480007003051301511 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 246043165 1106 246042059 246042067
    0x50a0e040f0617060702030406180e0703021812060106030908041e0e09010b1f03022b0e010212070503040c08060c0a0801050102191b180212010803 65
    0x14494280d50240f10840b40000009940c07031003003010760b005500e040c0c1041d00890700552007201540303c0310324150000c00d48070003207a46180300b2241d9503801615080b1040c0300b071002c441c44129040c01050844c06001c5090004900f09065450702d00300421942ca0605d07142069204039403000124500c04103121049401440d154030031151000c950022988544401300e0899190702c0c3d41d00e03406845108041460b80510000240034091400c0060804850007420450100100c502c080c10342c4000e015040144000d1181084059109008604101d40e06c582840c00000c0500f19406011021000404000341008410050141942601d450b81801904900f49801c50240d00d004104c0840000c10756501c0020345441111500010b000402c081d5125600840303003906070051410540080400d1070044010306c0e082c0848942c0c07005a44a100c0060503c4e42101a04806003a8000700 = true := by decide +kernel

theorem cover : BRFrame.Cov 245863309 246043165 := by
  have h0 := BRFrame.cov_init 245863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 245863309 ≤ n) (h2 : n < 246043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
