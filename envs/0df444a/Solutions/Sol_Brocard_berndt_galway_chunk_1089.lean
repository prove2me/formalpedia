-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1089
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:11:34.941144+00:00
-- url     : https://prove2.me/submissions/33364dc9-07ff-42f7-9b42-0ee5904ef0d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 195683453 ≤ n < 195863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 195684703 1250 195683453 195683461
    0xf0d1d1c08090613060e0124050604051c05030d0906020a1103090a06050a0201020c07150305011712090d081812070621020f18090c0a1b031107060e09 66
    0x31125101141c0001c01540800049413081801c0640070020601403000498007500d0301400c2402c0d6003448010012840c043d207010042031160010301c0d8061300c4206c032024507041c070300000204900d58011000c521001016600010408200116200c0d02d07078620041c03002c40024141032009400180d80c01001c255104407091022801004450041c140104010009410040c0480d903907040000003100350365081000b400442c2003000b846006180c2d8240021001d040c0010060903104c069000049100078040c09820442c00820659009048200c84680b40d00c0c5103c0000c00e8000564809080d11000042820742c00c82a40d400007040035081d10f1a80c1c4a00d07960822070740d07924240c80340200003480da040001c0300082400d9405c40c3c0240f03090015082c42585000d415140c3d004248034600c48130142c0d5040d1340b500304050007541c00b42140c000642064410f0602a040192a1040140d0b0001e14841c0d1420036004170301140881c0071810441c0e44540d150309020b01742010340d4408511a00401e0001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 195685953 1250 195684703 195684707
    0x207150e0a05010c0818031f06090e01060b040b090d020a0909061a18060a0515180604060504060804031124060d0302120703050705060c030601030f110f0d1d1c 70
    0xc649a900c003030106c1c45c000c0303111503a80d80b200a02c0d0b01d45a02d0700a14004031311203040c406e98411214085040050460b00e07007004101210389203c40c001d2540d042040812030006008203840850b40c1c41c00744281d9451007100042c014000f5103800943c031034a201c2d80030610342c140383d000c486e00d980b06120401601c1c181110422070800f07101c0307070135178401c04104244800c070710400e40d40745e00003d01a002e004199122400541d40e49964002041c0028001c1035800c0d800c05000390601c05682c00b950101e20b441c1c10a4001021441140280340c140141000854201440fa075907148000a111003a26010084041c144140c40c1c00c46819008101d00c5801044081c548900003400503030740368000740707402031240702e00c030005400c02941642445424402a4003040c81446020303c0b40000c1c0a419680c1d2409400140841f4400300c80340d0301d124a005540f03003001032980700303c1c0e0080030070320b0b551500c5005102001e8040d1825295903180c50130660416944114001118401c0c0c1386403d0302c00503542108941 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 195687203 1250 195685953 195685967
    0xf01050906040f090f0f1704030317060d02130c090e0903090907170a050106141201061803080c0a02040516080604051e040308101703030c09010207150e0a0501 70
    0x41991250308100455100d203081e500c201884002044007090f1168651903030411014211405d175140c1840390401c3d010062001c0042c640b070141808014185401c50310b004100c004811800440d000d1070b000800c030107590740014070307200d81d030b0050040420301148810500644051020340c0c012400034403000c80c01001545440d881154040c00640c102140942000541d200240007e400c0c07011070000103400a000c80d204a10460001602050303652401c40d0003000c4a03c0d203248004814400d004c0648224404d004241c1140d40ca072615420322400e17411103100c000c0395584006d00d400300c001103400c007040001c1201e00c00980201d4042040b80e403461030705e00f4102c0d080b0740c12a0004600f4000110b8030b02e1f084e446650803000d0000510481c841121144407402025541500400c86a00422020b090956600c00250052100c8040301d1060b06e083c25903a800f0140c001c0103294004503100c401c84e4401c1114200400541020302e108050209016010301405816280110b052507004180365000b030030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 195688453 1250 195687203 195687209
    0x10906050102030f0a0e06030907080601090203060f012a0b09060916030609081306051c0b1e0312030f04030207080c13020c0109021315050a050f0d051006030f03080f01 74
    0x19502c0d209201d084450194400310b07418060142003400d51b01c65403580000780d88038412040040056909261140c0c2c50420140c3c41150301c030b401001004129104c160300c054805100b0700b000d50405501c046400b48000ca41a40c1031144070b403050040083c000140c000a028401c0041500c2158699a01b87c58444500742410002c00651980820015680e9400a0201c9005180c002d060240041ca508020080359021100284003c201010b41094900840da0001c03600c041c00c1292030740510206501002c071406c0300c105c03200c1e207941014a03614240842010b1440407601c051341d07864880602c10a80d00166010b4005124410000c03c03030b000005000019504014941e91540b143c4090f400003a62080c7da1010040d500e4160b0400103890382e0700d14548038440d10001081d42065555001000e01c030960026100d042401410043c41d12200035818150074144c80444105c200b5051031803600c910584248010342c6007520000a2000a0001a1806109903140825030700c411030020162076081c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 195689703 1250 195688453 195688457
    0x70212161e1211120d06081614060a03021207020706090905071403090109061b030b090c0706090218100303030f05090c040f0b031b090601051206010305150d0c09050109060501 77
    0x1840b02900345004404400380900002e0444d520b1800d0014070848981040101000e4540c4542c4140700100c01448082c000e4800180c0c601905460084080c81c114420748030783d400b4480c00070358442d11a1080c3c04035141d851075004461041c0c2422178009603280070511501000038190080030a10400b1030181901032400351303036070034070407941c110403c0a20340c00a03200210741d650b582c00c2c00c40080c0d010700030700100c03400950142c02980900b00000e01500c040c2c50072280314491071402c01c0082d00c4420103652450b40c00110006254031580701054400d480d401c4a007078004541020032000d804558440b07001e03207220f07640500c11126541c03e50004d0310802c1d40d01500640002d00d5212050415501c040c4260042800100e030001d40c03207010904102c03071900c0e00300400503e100f2048441c2004080d26410070402e280480c43c00c400460040f40b40c0700301410050400d80c0311000b2a14000040c0601c10300c040700201a030780b000304103142440710400503109401040d03003401e000142814040c030940c8121001030b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 195690953 1250 195689703 195689723
    0x3050403030f110a20030708100906090c030c1a090d140709060b0d2d0203040503040e09012c0a030503041704300305070b070212161e 59
    0x1550103403a1112811030070000c03c51001580301c140c103030403c0300079062800b0301e5410b0780441c190500301c1c1c510400b890b00c060203684012810001c80900081808c0300b4494803000050045480c64440007400c00d0036006070041c0d80f44d40000c07040c403051446001c106c804440307020448105040e10711190f805100d411a9204115001100210f00103445010010241c441601d6105c4d403280c55201c1211120380022004217004105421022080d1082ea10040070b650010350b20003115010f007840c0c400b001031215045540100105007000b4040042d038015150b000464003103443c0401c9824002c0200e18a418050604145080c2001800a0074056244d03074079030141606041c00c1d1810707900d036400500201c520500f080201c024034084400034001a03c4010400b05003011400181c14400310003241811448005a001f200000e0704a4122825143c1c032010840a913941d192050342041005591280000000142113225a482c0089940214802c41d00c694407240016903000c2582a001c43c010020000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 195692203 1250 195690953 195690959
    0x7050708012a050c1501090618020316050d02070b0c0a18030209060d381806070c060f2a05120f2206140c03090a0305090a03020405160912030504 64
    0x1040f801000100707091400c554000d06000000c5a15140c240e200e440007954441d400c0c07041020119074228003a080c04420b40c20350501c242c03009014116119000c05100000800038005442901a1a0503640001803803031103141c0a41e14040551004540038002030005040d940040c044115401c1900c0e0003030201a8140e0b15141032055190302d02509446e45c0c0e202001208031030705041c00c045a0005c0c0e10654501103604c0100011001402414400d0114400c0300b050a4480300020425404911840e02044002c03240c10040014160800301c0012103080012407030141c10002d0b1892854031198542c0c4a01c424500c404450500510103000c5644403500003254051130000c860030382241d20300c40070940c10303c00011102258504000200d074500d03154481010744910385090b156105d81511403641c0b0b14540305000c0764689a07010802401d01802080c161102d031641d810300000384d07071b02800421460801c1013200c000c02211403607000c00540350507808207107212003c0340c051805e64143c0f259070034281 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 195693453 1250 195692203 195692207
    0x50a02100213090608010207030e0102150f040201030603080309010501030219030305070f02040e030c0f10090209180708030c0309120114010b03040201050702041404030306150f1803060207050708012a 88
    0x10050100d4030000030b101d100494090950700c0b0300402801d8640006036500079500e4007a10840c0d22624003819508403020410310310741c080e03800c564810b8802d1044901c41d41d440c40160300421503504080c04500c07000c42007004100c17055000e00e050b2802152090140f0381c58011415600d8807074040180080e030180642c000054414090b5078820f84010300108100000800191654010342000035403540107104404104005000c0110461030303500c400c1c010780d442c0d500490001c0340040c2440c00f6008030054600807802052055030007420074001640d6858900f11070880e5250003094900e44201e003038587c1002007200500c03854401580541c40c001181c1c1c40c00e0140c188a400c010000e07030600a0412814005a6440c86241a6841504140f00281c02c1908006003200c586070003210380e130b0a5904036003801c1c1e40c2103007803803101000501e06041071880d21014507001c000305600003019540007090080c1045800f042c0c0800782c0382002d00130840b02d09109010a254080c0d4030600807540d1039984583c401d18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 195694703 1250 195693453 195693457
    0xa0219050310051503070e0a050a0510020c0301061203020f370803040b0103060b031b1c05070e040b0c041404020a18030b1e04020a171005010303050a090501050a021002 74
    0x16052001107402c460380c50001c03480f4022204030007001c1400c0003080244950700308500b1940840103494001b0a0340c1001d001c90f000646a004039485429100000d940d4203108004090320031202400a201041e581c010400855400c003c04a0143c007850304c0300200c1c0354000484200d032001459091070101e032298660501035010340c2a0b0600c0c100d0b030a03641c4010800610045005510a5810408a614606081080f00c06e0341031528800d4212801403012040340c103040071490001110b001d10848200314010142c510b42880041080c0100d0300300107941d41a01c4180c03481107000341c046c00d20917078078001c0440d00b40c41a8043c050701c20221b40c001201a0525070701415550f5000d08204103081c2002c4414003202c05a80d000b00e400781150010411005034007000c5003e00d80608581100c80d0406900082c203e030928065500c680d03080b003842540c44101000b00304008002d0040400c07441d40c59042c01885544000840008185001e200040651040c000c40300200d503550301600351030104440c2d4001075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 195695953 1250 195694703 195694711
    0x1a01230a091a040312020a030e09060a2309060a0b1c0204170a03030609060608010509070e0607141b060a0809120a02010608060a1b03090303090b0a050f0a02190503 72
    0x1001c000741c04240c07680407a0805096102050002e03032502e1a6241840340d01d01841000720864100d82c13042c20020f81c019480490395441254514160303075820021420500095011514081501d05113030950380c800c03900c11902ca9425541d03810281d42ea071040c880500d031940301314182200b04208102026100c52201c1440100c4624050b140941e24407900100c05c522105555054005891000030981c0510a075030090540c0003040c0641443c2c031502a010410510680303000b982000001303811a445140c1c891620f01b0300800f100e40369007031402c080d00010f80b00c0d0003100b1203201d90b07541a0b013403180084041a81c4000142003e01d010200c64040700c0d0310380050408520742c4034800c654603105d00800090b0040c92050b0b070000079900c0c03510083740e00d02400a0308411204e40781144a10030405159902405803200b424085880c24603868128004c080da03c00141c1100e0071101882807407042500040e000c0c0404481d500c64903180d41c12240124450626001d5031104185048d003a0a4041d002079640 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 195697203 1250 195695953 195695957
    0x10f051504050c0406031a0d050f072301030b040609050f1e01030209180a051e1c0905060a0c0c0b1c1116050703060204080c0a08010905030409020d0e010606031a01230a 74
    0xd547d0114080b9058a0346880c044a16401281c51b42c40f40540420040004044540c01c0c8451042c5201c2800030b150310010349036040503144c07600d254160312690416001840320030300c00c0110f45400760001000c040c0c1540d562840d48001800302c83c80910100055060380e8005040400d903450782198400786018898202d00e00d4081c001c440c402080080c480d11070054074418000100054400c421400d002201003070880c050705010340d13004110f9000040405495090b1200c0d50790303005606003a81d012040d000014802c1070210004039114900e0ba0182a4541c110b04203003030703002c2d00c06c046001601c110000710303101401c0901510705030640d0354003141c222902030425203203107a4494569800b81da1080d0003d9846038003070703544508541000342101c0d001b00140c80c001c12014019650750341e00d03032103188500c0424640104012860014130350211038002c000750002c008c1d8580d1500040c0c05040b0383c0a09440d41c2006c03281d03410a55020324084503082d103248100046540c0a00504d40741e6802c0103c001c0300f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 195698453 1250 195697203 195697241
    0x302070e10121b0806060102150906040b190f0f060902031b090112050a0b0901080304030f060506040e01090f020312070b01051509030a0c0e010b0a0e0d14010f051504050c040603 78
    0x452a150f404842c3d02902248014110a280400001e882d00d0b0104080b23180c3c0402070300400074816004140c841d08180e00412200058440368216000c48001107610b0547c14a0706001440c9a0201e41c424040d042d01e1710000d000c02d07680c4640d61000ca004c00c83d101d1088812843d550303208881d00400500c031160b0141002c01c1d089102c092100122002256800085650303849400000c1c035000c0111801411008001c0d8540350071070703907440c1c41001c81c4400104840c2c0c4076408070b41e1940c0c032900804017a40c130480080000d90030300d04040c0350503102ca100507030081c005c000341c8425034002c2d5000c603115260401c13904421030f4a060144000050030000c0ca442d414401d00210340240e03400d1094800c4035000d40700548241e42400d101c0b001c00c05040e4001083c80301c041004d0000703690010a21080f81008403110003192120b820100c00c424000c450b60301c4694a0b0100700040c510090f40220700038903001c2d24009080c81282d05000031940c042d1107540103007806100800a681c4a900720030b00d020b1004078904 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 195699703 1250 195698453 195698483
    0x10f022d040812092e080405070509070203120105030607051204050a020402030c0301060e0f01080601030e0a0804080706020f0703021f14030a05010312030b10120204030c120302070e1012 82
    0x50501c04150081404031500141d40402440c3c044c07801c64205204110404104a115880c07290901c031706441417040c409030f040000d00303000c4140140000ad01000d071000110b440c01e80d1000b9142c1c1d1000492410080070000041564100021098031554040d183d8924188200c40c0c6940391110041080b034140c405c0ea03000030016102e600103540160710144400c0d80307950602c803024000040c0e4038507241c00b132035050150303042e6684c1c0720103419004082801c00003845c0d00c02d07a000d14180700030024060b0840034000350010300d0000000e80e040c12102c1d641d00b5150700f1078606480c540c50b2038031844042e62002c02e0141040c0740f81000070300245100c070181000315086c1a00e0301c00c4012604100d0312604115039813001082448029040c4c10344c3e510891a0400c6080c081c0000620202158040b85c410050051000300c0e4000459045801454000c010300c000e2664407115000305c00d001813000c50040c015094006101c5414502d42401943d07900359010707026060103843c00d80410111410380b01800010303160 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 195700953 1250 195699703 195699719
    0x3020721090501080c090d060b040912050408071205070608093414090c0f0c0105131110020601140630130c140118060f02010f022d04 59
    0x2011248a8940380e0500a9181c94000340135520300501e240c40d80c03a07003004038a4042c0d407078080b281c0720b141d8003150005100c402000070034010010817000401c5000b07040440c0390480d80010141c0102d40b4154103c9122980b41d4803d240c0400100c000204150f2000100b070203210b020390401580482c640044882d00a08183c0201d04840103c4000041c0080d000003106102060402c2c00c01400d50302482c1040083d040d40400d1002c0350080c40d0744c0350503c0c0440c2404424101c081210100845038009004500f070070300440303c52028001c411144070103945d0a40f8990306110202e040310940031b070040e1910743c2ca0606074092080b4450070032503100e10704000340144c001c444442460044006800201541d0301701c084120500c1001e881845030480b815000000035a00403a400281d44075402824002d034840c40040e91002c40042010f00044d448000114099502c80e003000c3c541c3c1c60a40c000e000e1552520654001c80c42004e07002410819081d07500c1844082c65042000a109000002c9142c1713a607540b01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 195702203 1250 195700953 195701003
    0xf051012021336060522030e0f0a081005070e06070605060f040f0c020d090f03022205190c051206120f01021602041a0f090907080d05070201121b030207 67
    0xa681d9070b8120310b0301c0d000c14818580321705607100b00f840e40c0b030486051041d2500710125404020003010051807900b020a562600b0301110f150b4400030703001c0046c0b292034480e441e0320340320305500c0034410310314002c0002e503200d2003071f004040038100140c80580b4044064580c032002d00fa004140507002001e0001c21442900d4030301c18419919021500000d009000080c020b0500c00200c000c04100145920207200d690401030038841100d80c11600561940c01c03001c01406240401d40042c0c503041d141000700300302d050342c10045240d2180f0380c0c001003008041101040c1c880d4001c1024400c039820500000450b1402d00c18036590f0703a40b52450072074114410710880c10342680d0250b1007141919031040391201c00c40c1001c0c001c180d80041c0604582c0c0703a18044602003043e03100703a141d240d80f00340c85610110b070124005001c0c2030050725683c02540c02e01141c0c04000342240e8004c5104a0000c6d82908002603f1441e5200742d90301c44d81c0455000301280c0d5580422030107034000720f0054a0803051211600b11980d20359036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 195703453 1250 195702203 195702281
    0x1014060d060603150e061609090c091503060f1703040504050a0216030e0a08030415030b0d0b042f031c170f01090c05040b09010f0309060f0510120213 66
    0x1010900c0c105d518491400c008000d40359504201811040c00310641d04803140304240d4001880c00a01c2c0d25105030110384070220396101c20803006c01016550700e402d40c0740e004881900e4080000100e42ca03034a140c4004e4003001c980204106800600007406140341c113800c85900303c1c80001c000341c01e100000141200114040c0b41c200d000c0340301601d2003005400c066002031700405c03918020710b00717003890650201c000301c003916245410103542e403a07007071070580d00c1036445210103402040c00003862400d868050554000039040030142c170103413902c03d102041146440044c441020b4041c0081c025000c40081e140c8803c1071407001070020003540290a00d050425451280d10880c00115003540350212000454101e1084c80040103401c000521124004208841c8511028a8500301e030700318425045006210341980101060300301412441c1da01d5240e00030320301842071410140c00095031511201e04401c03a1030070094000a0390b40f80040845c9099100c0e1007082c02c0106d615048038544000e258411038488 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 195704703 1250 195703453 195703493
    0x50d0519020c06060307060f020606040e0703150e1902030a0b1902120619081b0406170d0f0f09061419020a1a0609010302060a03060905010b0c1014060d060603 70
    0x80404c40c562404022200007440241840c00d2440d418040094030307490010100ca0080c7e0f21404c1c106c401c1441003100c80d00440c6c04c20542920740c4941703114400540049000040c86101e80b0300d211000c1a450442c452000368002e000b0400040d45035544008600003c080d0703402102005812090007615000a021180d001d524801280c64210101303d40c1604642003c4c0510b00d91110a120700840043d40c0340c0344c041018801e09100000301d000402502c1a0703002250030f9100703c01100c060100000d000b50301e41401d5102d41c48110046001221541c0459a05600284840c0e9041019500030950f113040350b03001220716803601500d0900440390307200d07035008000181d01c8040c010003802a2032208038815494044200c80b5410540000340c1c9074001800080d100391800219082da55020b684644002c1000e42070134071440da51075070b001c010781d003001e4a40300c2d150040c015103183c071b540c4510400d404004881c090720709580b5a00c00b1710100d02052001194515138881c0c0c0480070030b90703200303224210716008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 195705953 1250 195704703 195704713
    0x11215090501090501030807020603090307020307140f03010c0807032004030c1a16030305070e0306010308030907060203040f0314100906052410030b1804080c0708030a050d0519020c 80
    0x440c284048a105a2056491516100051001954400c11101041c0c0c0460318a0b46a071540382c1560304520600328025454402c40000080880c4203aa0440484104543e40c20100880038103040c20307034600e46001800141c4034800503104074000d510104503650409120030140092034910300140d4000e42040c2c1d80f0034101c0c0c0c1c04000307403c0380d54000d05104100d610341070700f080c3c0b80340203c001003c3c406000270241910ba10006009034442d418100c02d001004003140e00c0c43d45c0d2801c1070f00c078981c000d4403c10010b01034580080b810302d000104030703807c031050404640c5e501e9140d40c0350542c1088002120048500400b52800c030b6400036802024030090080c80c0000b114100410802e401d40280340c1a94044440746218a10302d03500c44008100203581420b010503100c1d010800540c0d00f54010a110300c11210710300502c414000b0301400380c0840700300403007100c03440e030380787c0070b80c10380c0d90151290040005104100c0d408a000c2d06403c8141c010010701c4603c0759400c2e00c41c42e868141d8122a088030056405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 195707203 1250 195705953 195705959
    0x5030607090f0e0a11070f03030b0103180b1e0a0b04150e060909011d0303090601060309020d0305180402042c0114060f04031205030906010f060815011215 68
    0x2800415003001240c148051010300e00034204411600d039218204900a5603800034107980740b40c0d00240e4449003032409140d0350b0140f625062103071200315282580068501401803425501902c2000a0301b0f01d942c000300c402e90303059681c2e0b0140c550006c000ca0b4081c03106a51810402450100040c0110f1443d000450091000d6060008035501100014a4486500c1007046041c0c102c01245420403010f071440c4503660350340c4071914054440d2544600403080c84080c1303181555000300c0614001c2c03548a00703856069980e0780045084c1c0300c0910000e54401d003404c1501001900500c01441d8100c0c0340f101d001410440180010100c0e08941d11005041a10103959a07040b645c410800c04091150115400c40354107000e440c051a51012000c28003450000420b2140035080505407030040d81d100380f1000c1c42c66103018004206400c166620364541c81500d0020884421244c02c031000d03611a80d485030010f6403010034412002c0306940c070483c180910610340192020040c05181c09001405e10210800c501d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 195708453 1250 195707203 195707209
    0x150f090f0303040b070804020d080a021e030f0a2111030a0e010c080a1107060203150a0b07080d05131b080f0106140402131805040b130f06150305010603060605 70
    0x995041111a241c10410400c00010082d01c09290010b1213490310029550f030740c1c0b000ca0603c442000c4045d001d075078041425034407540c0c001b8645601880307210715503800c5880c03030749459540e0048441c2c012424a040c05140c40251254849030b0200d43d010300329418501e0070220983c101c80380e890100a186100104000302000d05010b4600c0d90b0716500001c00414409910061030040040e08510300da50300c0b084001d01004c0404180c1c0c0803e030b0000b9003156a410007082204000700c1d0b4a0020703000e4407110600080030b100080030f44a5403a00420310600e0b003a24030a20303030300400d4000c02050003103047ca03071940007160300301c40b4040c0d000d03444098150032541803180207841d10705100d0240f07071203a041100601180446051036080035809503405621203e0146403c071007140300d1b400c01c450025a84120750020744464009070300880c004e82072034100e511f4001611240c02061040507001281c0800310340d00042041c0e210782e281c0c04801d240815620740725170311642900c400794820b0301c89070748130f09060050b45 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 195709703 1250 195708453 195708463
    0x901090b130203150705040905090601060201110f070f020604090207060e0c041808070302011e0c030b041109132301050907020309011e03020f040303050a0e01052505150f09 76
    0x407001180d030590103200c03540069a90764020580090700d8482c0c60100d0400d80c02601500c001d080b03101d9061050f80781c00319246944080174890314006600b004844004107400c60125421010b640c1113491404c1c81c192503141030041c4c0c1b000202d0b00f01008000004074041c03a031003c0c051891043c00040341d5841840c130082e2a1020150750316100d1464a0413107034015041643c004101540181515240c0c98241416030050007440001101e4480070140882c002c9001d41c040d0030000380300d071800c000da603001030144021642e0b0422036500800e802c02c2810703514500090b0b0341104a800120124030001e000600d0034000a07a110b207100100e84000040c4518501180d91560150070751008500307281070040000d01c103c42000340c14081c0030b941070b507084405110760102d80d07030001c0c3e201899541c0c81da03d245c001c0a81e03100c1001100010101c1c03a0030303203080d0700c10421102c080058030083c00c0b000c110a480000c1801d807410b0100c80318030890a00c840b00001581040f4850340b644054552030f8608442214106 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 195710953 1250 195709703 195709711
    0x60207060501050613090902120a0b0a0e191401111c0b09040812130813031202010501060509130204030c08031c0203091b06091201021c0204050a0911040e0901090b 72
    0x9090103200d00c0820845040c4a602191100d80c000300321140b00340080f6140c1e10b04183c808038035024101d03d007001d01001a0b05580035500c050401c10400300e00306000340c1c4609486180321152a81d8901a00104080c0d03f2440026112600001030440688901d0101c81d0b10810040d0f4440a0300480806002030a01c00c001c01070030151403081951806035140c81c3c3d10310543c03030014416201038020030340c004a201c00010019920070980c0c0c4c0d58002c5890b07140c030080083e1204550034410300c002c84d24480c1c41805500d040b0381c00d6440d0030707080210708020008030042808801d44625824040000407030101c540990052000754059661010a002c11191100040c58840500750042060204002d4001494031411400450940798000c00c0c40c001122442507403c0e0f107510075203a60240540c000306600900460003242e503506c0c00d8006644103107050740500e20a07154055240754040080d03609603000103903203440250410b85019200c0d40c0c000b00e0b241c0f098440d514145e40d01d030100d00c10042030342811604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 195712203 1250 195710953 195710959
    0x50102010b0910030f0516060315091a0603070e030a11040e03120a050709030b101e0b1b07051804051b0d03030b04110c06060307120506070e030705060706020706050105 74
    0x2142c030380b541440d03c124465100040c1501c01d04540c0e1814003d080c4420840009544c0c1c0d0040d40320358540c4001c003d41140040c0882500c88800c0010301102d0030310606c03000310405207209035000064420882c83c4d80006060f5002d005803c074441245640512854418612800b00e002200310032000b40700403601c0c1685c1d1040194420042c00b160140341c12842c81e4070000d24407002c00c041e60f07a16422100d941c01a400100741d41803034414031141119905040040d602c0d82d621108410710380105050241585214000d081c031401c00002c118400b041c0350312034422141c58100c4041c5d5a039040414008661101c40d9840c44800209010800005000d916464161140e40044400f00500000c000c50b01d20a0001c0c281641c1e11206581034545400c0002401c002c01041519008d0844403181c0310345084030460300c01c0c011568041082032907158201c4900f42c03c04010869651b4880c03040e1703404124200c105030702d071280c500c000600f5a00ca90080108034824070b800368071281180f8080f010b031081a001684 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 195713453 1250 195712203 195712219
    0x209150d051f03060f060b0f07210509040504021215150108100b030a200705060f0906130302070b040f060f0f02060c0708040b03100602061003030c030f020f01060807050102010b 78
    0x18480c0c02c0c0c40003600660360401380000d080300340784191034002c00b0254000c2144140104015210f4030800c400707840340038040c18a00c0350801041846c01e14080c0100c507640040381d0301b442045c005007001c3c1d001c035600500c040d006a00303544000b40c1c0c1919007864079005c5015500d030305040180c002164282d404030200b0030b00380b40700755052100c0c0702d0000c220203016015079100044001210340c0301c0742e005000781250383c110703d40d044a00900c00d5a81a406aa01030ba803501c12203000c10744451030451514425010600600215102e080e1107040c19031200348180d0442c420031070003180704a0540000e2000f0005010140c1d0003500d0004040e01d0950119045400e000041c828004025000718885900070481600c055070340f940340c540144c060056030820864248080200040c000d0b2030090041074805c43d4084510640e11000c41c04c150036180d005c0100082c0d0301080e01c0300000c1c084c0c210355900500320300640e4501c030119035906003169103d030320400c4243d0140d8010032a03540c080c85005810703030b402e41e8080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 195714703 1250 195713453 195713491
    0x18110706050720060406020304050c10020304050f06071a0c040b1903062411011812080105061e0901050906072d03020309090a180f0314040e0a0f0209150d05 69
    0x140c0c0352500100080c1c003447c0c0000008040010510001c0c1061800400390503881e03001c0740001b0346d29002801120b006c0c003948440500c140c030302441902c072020351190f0341100090074a0a0b1b109080805820384812500500003c500e103003c1d0745c05481c0000e00d11030096641044160004d00760f030010b5100d8001020810100d843c48000418220030307903041420903184d1318014600c003d0042000114445242462001000400482c9903543c04222065034503032503240d0b00c402c2005510302c103070300403054800c5100ca8140c3c4080c1c02d85000d000b08500504019050141131030101e4419402050f0403039181103408004200110071044039a010070040404610781140b039a8040d5680c0b00d004003480c8540300d100d00180018031395030018550801e03c410f808110403403914104000500703840c004c0b008602a00c2406074000c0481080c0d40c201c40e403400e0f04581d55151005400020100000610300c81c6408008540b4a40c035180402600c3d03d4044890a60fa440200382100c12030304050141195a08401d0a00d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 195715953 1250 195714703 195714767
    0xc0203060109020a0f0c140a0609050105102702120f04020307140a0e190603051c05070b04020d0c03170915090306041415010f1e0f181107060507 64
    0x1049a038690307414112076907506070402030722640b00741c04008114440ca03089001003105940007401d41c544a80000d001503140c41168003e1010740340a04201990f0302d2444031171107144004843f00c00da000d038400503e0032a0001010300e208800722540d0b92428016803d2000f181420403000b0020444201c9400700c40701010001910300949200f003010f58440b02001c220102a9892241401c0041500070001c03240d03685400340d00c0e0804034030144080903205810301c2c481c030300401c1101c0304d1950207517903a011941c4a81c00c02c12801c10000302902c3d4942d00c01800f000091400e042440340c29418501503403070310705d140100650541312640081c1841130071300458001751800a03810790025403060382100b10000e00d1803a5450048540c14080402c5039190000600038071541c01041a01c1c0640d04c0c00880d15400c4440c4560291648551032808200b808104441091401102e44075000c4203004103900b0400816140039400c0960b042c1c80c0c20795030340305100440e42c111604141c0b60004100103100011b01d5414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 195717203 1250 195715953 195715967
    0x100f05090607110904050604030813080307200d020303150f0d06050402030f1014070203030405070b090a080a080409241505070506070905030f01150306021e0403030c0203060109020a 80
    0x55030050703101281620400c10003080710400410041d000000901c0d090820b030b55910300584e01603002c1103d00b00070a0301d000b0801ca800709142d4004640d00c0c036540340e400c0121012000b11b000740c0c0c0d4140400740c1000b8003110510115a84a4003640110713143e040c0750034100025010046414400c540c001e002c076003142c48118401b0086a0080e038000303065900c1d1b0010900308008061800e109014070308514101000c01d030320411804203108640c6446589083d01a6074034881070358042d000d90320a0300100500280c50004185040c0040e042c5100315a03100034180c0f50030302c010011154040082420320100950340b040e40c480d0325200d181d40149151840003030302015501e00904103031040c4102e10f05402d50086040b2501031b9484000ca80d0181f61005000f000c1c0500d81c0078041c820302501408654030078050149007216240b206039a1046031465480500a61200f5a0003003015500da055040320b00c0b01c079026000031400707612210440a000d2041504021050b00400c0301c10748144030081311541c0c0020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 195718453 1250 195717203 195717217
    0xf0e19020f0a17030301030b06010f05031501050f0409051504110711011e020303180304062106090c02060415050c0301180f0c0302070c12020f09150a14100f05 70
    0x912881000d2118000c01c10b01c91094000e00800d2500049900141070300000560480e805120b50403199145c01c4011991f041907180e18000040301070020410704081090641e41080d414141981f0b01644210700840503000f962050000b640e50b1020099800041312880c034001c00101c408201c1030440204a05090242c0040a820303030f1004074a2010903400781034004940702e003a0006030b81501c61400000d559510403140071000903442e40004980c22000410348050741c1e010744885482c0e0002d200080d84042c1d40c0350700008460345410380022022414880c0c0700c840042c03a0301412107881d103414091f40a004032019910400c2c075180c00c0046450701d51040d41d042d01c00c010803900201c418107107058064511000c201c0c11940c44d1040308100340d41c05900a0186038820101108240c0d40c41c40c403c00c000200940c007a412149041c400505032500320062940403441140004100640001085240354260407082c00003100d031100c0015440c058066644c0c48100d071901c0745c190065924001c20500500d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 195719703 1250 195718453 195718459
    0xf183901020d0809010608010f0c020c0d02030d030f1401030302060403021501030c05010e0303070b01080303011e120605090703050703030504030c1e1a16060204051206040302030304080d0603020d0302010f0e1902 93
    0x40101303000b00001c1d006500200802d400070f11401e003540d140b490091a242200e02c1c0584910151080141049114024481d400801401c1d501c0341410041c0d01400c1c100c0007580e036850361016141c4804a5248443d07010f18040e90092489150601c0c000c1e1401c1242c10405240b010704400410004100c2c10044080c0c540a10703001c030710600c0c607001191660242e020000d21b4003020700300102d801c040c0000550304072028500400d6602019800122a181545c000d844580002c5850705000c11400d13042550056200c40444005990703d86032941081240c0e0011800250002010000e000c1c03038401900103030a0022070a07600da905041880b610307e5192250422101e42098644a02009801618605006500302c419110b10b640f4054000358090f0107010310407090406118113a54002032860711aa40c0f603001145582c0301d0342c80d002e0302034100a44039040c0c151182008001a19084032020540b4440c0d000418100068040f480941c0c4400091511990006c00d04102c501c0c00e00a0b4061026019 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 195720953 1250 195719703 195719717
    0x1014160c08040314060912040e04020d0c050a080102031501030c020613170d0905011109010c0609050705100e030f2805030d050c04060f05030c030f183901020d 70
    0x1900e0811218056580f014214098502043e21990004039100c0c1c8129100f0091342c031001c10316030280906005038002c141141c031028000a006082403410107001d036000e45000990a555400081c020909a4102044603500030060084e50760310341305444040355007420140513010072940007d594000040c6080079901d055004142400f0307070b90028001c07501080c0c0780c4659440070380c1d0002c0082c0030b490108680c95840c16100498891054050340d618000503924450300c2e50107620307020701800b10400261414000c004000460742d558103114080340b041c0c2d44455281c01c0d0035008250910782c002d86540495000085a440c4d488114024042099890a9090705070714443c1809031840c05011505d091103840c20302401a4041200c010b4401c5880030781c2d039586c4040c44030100f1145400b0913a00049014424004900d010095640003a07100104e41004140442c85034a80d502c0c00612070850b5600c504600100340d4050500d40706003408515a0300251755000020300001d42d00c44804040c2d004010031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 195722203 1250 195720953 195720977
    0x14010b0a03180c150e030102070c0608280501031505090c041a03010c0207180b0901030305090303120f0a0606050f03060d0f050d1e02010b031506150309101416 70
    0x1e0152003980c16401c0200e60010a4403501d41034180145003010f00e001c640131607905c0ea0b0500d014003c840b00b040d8044c075500c542520f800c1058903110005007103800581000058542e8010300b08070300c80c415600c4c0d408041480e51640c181030300054000b0280c803a840b800c110400001220000e034910882101f80c800040803150a64142d0242021480c0f0540c5542010240440f0a60025442c001d50f40c451802c200d548a81d0f24041c1c00b10303008900c800740c124003800010000b103030007a00074040e0180050260b038a03001d000d0440c0c101840084460b0301142850400b07100c1710302d50f5445100042c1503541040d0385030110141c035411860000521051090191303010600c1000070128546444c00c0d0b2040c00c44420054402001d880c41104480d1039006c1002c0048070700003a031050003401c5d072850001d005851491726040001e200305100400d040e0700a0b0801901241400ca440000c0d8481c1e08841c01500441652024800694141d50750751051800d084003800845842d11054409210300b85c00c001841c401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 195723453 1250 195722203 195722231
    0x6080c070b01080f0d050a1e050d15030c05061804050a0b1002030a080709060c020d14030705030d060e010605121003020d030c02040b03060903041e05040c02030d14010b0a03 76
    0x45644401015881039000024103040f00080c88040c020701c24080d81c800000c1c0d410100c400340036180d205e400003848240e000d010021614110b01501c02145015803910443c0c0d500007064031045542d64910807603222042050004810091000e000121181c0d441c00780740081549909070041209480f5603a1000420802c05042c1d0000f00000300c05004e20038400d80303909005e52250001c140290100300100001041144149034400c03e40c0c18607225043c1e490419004c1c09900d0446220885165800b0b121107220b22104001514500e0310401c0290740d078214440101d800c2d0743d541d0748111070711032507000107200305034000086c0e030444600c2c14000710559a9002524031041c4c1564406034008420740102c50a00d036004c1d00440c0020300a45091001030141d100307140c0d0f909000c031807640e0f507900706001c01e2041000d558000308210176420340d116199a21b440c002002c5031000c0311800c025030705c0040d103201c8100c40d0f40604881081c0390100c0002e01e6240a210184c0703031082c0211a0700309655441c504031040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 195724703 1250 195723453 195723457
    0x306010605032406070f08180a050a12060b0901170709020307050f0705070906030609230606010e15120103030f0c0201020a020405060429120102030405070e180f0102091302120106080c 81
    0x940002d919401d8050604121040c0d0380236007130164040c00886101102414120030805c229a0003500e4031701d00c9458844058098070060340216071080e1185a520074941d00c0281b8030f4040c08a28400790340110b0702400d490700e400c00c594040d604450042c41000019900902501c40b03086030707624620390320b1025107000707402d010303454025500c114030b003c4010061185c1a40541912032140050710040740b001c0b001c103d10702009240e940354542c0100009900ea511a507408d64a02c03601a01800101101160340001504648045200340c4082030042051560064003900c06020504100c40c41d44003980000792180a08900039006d551a100400c665455070f03889010f00e0104490130b000030300e1780408d10100740480c807400580318142c034203145940c420061084a001f03d41c004018010140b405140861421000703000d941d0310320281c1020407140d0810711125050725041d1000681e102e500c2c0c001c0010002d22000b0300c000e0b80d441880b0102032041d11a03405070645007541445201560354030820f410034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 195725953 1250 195724703 195724717
    0x1030206070305070b13150b10030216020901090c0f11101533020d050d18050a0804032607150b03160815060928090b04020306010605032406 62
    0xf00c900d40013080502c1c0241444050003e109541020050070084000c0048d60300105000b640141c81400001a1a0007603000f0518072858007294010300403d600090b00441099008191480d2244100d13940e030350340f181c0d414888034501e0400012002c811502c1903560748102c1024109185c1d102484c0022948800c600c0300105445400022007240700510000680152015011004014038065040301d0002c00c264507910b100ea0b07201c50400402070b0141000d00a088590240c40940c0c80c16600441c81c1440380001c81d50103000d03c5581c41d4658500200e411240d90602c00c918910030007080407401c60700003120b501c2504080300130020380d4400014070003000e103d001d4503414480c090f0090001a40300642208445580c01a1554001d0584054034850740440c0e81d680d0203036401d0001800c0c25081503284c02d0400102d0300b004860403200b103400044852001080d00c2000d1034104000452604011683c0035025070b140881c20740c2459508400c02d1082401941c03054240c44400008913102c2c0030940d401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 195727203 1250 195725953 195725963
    0xe010905100f270305040e01120b010e07020a1b120c210b040212160f1d09031c060f17010e1501050d02010c050607090503070f060804060203061906090503010b0102060405060103020607030507 84
    0x15541e4482049c220f00419020841f2115842c40c00001d089218900d10741c841c12054020348000030190b910400c202003540d50620240400300f0300800e0058600701c51454003403290342c20b041c805080400e440c00700082c0c0103d40d808611340103103035000545420500c5c0c1d040755050390000383c5856044466424000848855a0b100030507100c000b8401803145c81020440300f90f040300a5100e41c47c44071107812980300310b880c41402d501c1000703465000c40303075260042c2808400200c006015901e0b1074100703035a41991c4d0b101408030002060016024102803040000c800700c1c44000b441040320380c40310104005414810584219840600c010641e40030f28040c4c2ea41c641e01c6810380d0100c1c6481304000d0700c040d40c503025082c041e100e207880202e0540c0c20405078009491003500d48d038130166916a616000b95000401c000d41022050b17001416000e802d11101010b080c144d101c0030815410704080c94210340114000307504651143c3d0607c0003082c40411540c0c192501501d1495540105081c103940621480d100101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 195728453 1250 195727203 195727229
    0xc040507080a06060801030803011505120403020109030e062a0c03060f040b01050d051f1e050f0a0603260f0301090e0d0c2102010e010905100f27030504 67
    0x442a0780c000c200e188900301d094010000591100030880c3d032084240401446c001c000c100600002d00b03c4654141810076601d031440c42c01c032412040f6001d8145c00d490490260391204117150400d9005a8001c04062080d1030603070a01c0c3c0790b100c0170014603040c5c86150300048071030110146906001d05c40848541e0020302103e8550400d21041680d5880854041d18600307204c00001c05c02d458001d21107040250401c008001c11144840310444003c00304803140d68803951605288059820322a1144203245803100c009182c3c980382d418680f004100078440000c1034a8440240005540b009518003411021050b0b100c0d009140c00a4460b6441290b8450082400110000aa40303034182c200385149580e0300c05550008134400740542d440101c0c070f00002c0c20044604108400301c0c2400307020600f809003134070011800e4810b00ca01103003196079940c429603503500305400b08080d092043c0250340100f01401c104004104141e01203007080c00c1c00c03100d02e1007403000b140c800c2428188610143c4000d0101080034007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 195729703 1250 195728453 195728461
    0x702010e0a3201030203190b01230d05090c0102030403030c05011503050f0106140612190e0c0a0f05030307021309060501060905031606021e10020a021e0106080d08090c0405 76
    0x610b4010a42080c241910800000c2c2d00e181d4402c1c02924040c0d8040008001c81c4e1019495840242c00083c0c4698100030002c551141080d01004010b0400a0241d000941c0c800c03101c019001990030082c1184010383c00505030090590b4000200d4003180e070146000c0001441c2854994050580404d007007996000da450302005110004c030300c0c020003500003c000c0100680c4c801c14401d1320045d182413554410401d001c42d201d054450594039a00c12114410034280d80c08198084080354048810f6040301d9110307041e0140d07a4205450500f003d0041139840140300f924002c0060342d41c3c401c2d0784d0000d00500e00d003410f5072200ca000d038001650855100030280a5980c6429004210b0040c91103440e129108070b08440c41340703d0300c0509000035990207902910590980040e4184801d040000150313aa118000780d1009183c4617201900780956581d02501c14907800105528108110300400003260b45415810015001d0001d005118405242051110760303882841043c14644200340040e04141400204 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 195730953 1250 195729703 195729749
    0x20d02030c04050909011404060b01030f0906150608091e0703080a020c09060607020a0e060111010f0c0e1210050c04050607030309022119020409050a051005010e06060702010e0a 78
    0x20b44242d54055500042d2076075407642a5090320b0207040c59082c0000c0400224001c6842d070303002400c002d401030401040c2580400d01c10421251100410b48002d80c2c3c07566900300c121050070041004103994a003202d4541410500c071030b1030f00f00d500c08826044c1c00780d84030088000420f02202c00110340002401d5100c2d076494201940b41c1405034651031088003107000141c44d0386002400e480d00150003904401580c1e040804205200710080e00f01e034140000c01c42e891418178003d0103100190900c01c24007180852203001d02402d07045024102600c24812050548200000050307000c030801d0760884040b0702da8480b19001500707486980c01070744d001200090910306268040e0041d60300c6920985079218085e01189060016882c000c0c007850503038101300501254051000d0f0306040302030005000042c1507086580d103915121718004120b407035070403218100070456154420716004201840440c846441c00c0c8002a105100f042d800038148800b02e103070600140c8540410f1030103010f900a06245100b00f0307100b1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 195732203 1250 195730953 195730957
    0x70e16080f01031e061503080702030d080705070609020d0605010803030601021c0207050112110301030c08010b03070510390606050f010503130611160b060306010e06011101020d02030c 81
    0x500804a0035000229652039a07841c4107038100c0e80c210000002ca52070031200070502c0e440c0014255403143c1c076000c03080c104440c01c2044400462194004695890007032050604080c4004805400e000080d000c04c0300d01ea0b00082240e40e081d82c0a103000480754103610008280700042c6c1700c054400c034a05000482c4091002000b5402038800740c080302d55020140001c3c0700c401c0d500c1c04c0c0440050300444010003055009030b44180c52141118800f2503502d500d448540e2483d00700740e000307030340700898030380100a002002c1c8074110b0071390019009001258140740126000340403c807041c40412024212022100341d800741003400308003c03442039075560312065941000d001d0b41344800f40c0e051464103400064516004007583c60740c00060b104d1a06558510410000c6802112019a0544d031200c00760074464a1550091030342c8481d12000318400252424481d4031000d004119600a51003a0014000c4203541c03440b80307501070401d190500741c14448655041c0a40034407055070150324004000d01a2540740040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 195733453 1250 195732203 195732241
    0xd0b07050706090b0a0e0d050f251b0605040803041403100f0614040e070506030c0d0216060b1c080307050706060e1f0612180807030c120c081902070e 66
    0x1030280040b102c030045840d110010b801f041c3c00800e0f81008000c3d485210007000d0307c0616000c8181d40105818403242c61001200d400b8100c441c180e440030031514411031050720030050f21881c5080383c101820111815624810380c0600321002000c041d030044030303580402c020002c0c0148003005200026800282030060101070092000e8200000d0728103c1c227003040e110300d03294680d04000500115250005101083d171014010340d07001041041075035280245400205610840050103c40c0b1107201d04104080715004444144100d03080652246c500043d11510b50010340c01a00d00d0740d483c0c5a08000350340ca4852034800500440c205080002c118840c0b07100e19119041010300801c442c02c0301050002e038075290340921f01c0420074000340100d0301500e50340580040c18044009802503101a11054044c0d00003281c1100040c048036040c03400c000304040b000b4901801414440b10101050b035a0a015008a22000842076201041346410314803c2104400408c80041445680d0030300d0074401d00d03410000380d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 195734703 1250 195733453 195733471
    0x1c05040b070c050a02040903091e06080105060c060a050705091003061d06031203040f0b0a0c020c01050c120706020d0204030f0b090601050a06080a0b0907090608090703020d0b07050706090b 83
    0x400099401e401240741003002a4024050b0401203c160308200040410350807d50400c801e00c3c1000c240c40103182080025401c0000d000180d29107030450041c0300810581041c2c0c000e50080c03007003180007200041c0654121810410101d45d60382d45a50462341030040d10901c80d03000304200600048a9015845001034844d500b60f0402c4900321615525400101601c0d12601170340003c41d03000d5502c0410307020310f401c6482101c87e0440320481d07849034140c03c0d600340c4a9003c90703541c0c2c80d40741d858a41c040003502c05400080c00c2c01d134109540d111080e61074108681b1030f8410088000341900420103070707a04440b015542001304548450300c17403c040c1c01a070101142110303102e00200215032404000607032a070403210000d014091040c04d10904840b02d00014203e6030249480d003107152520fa84203501c451266403c0e030f641250302c0b450400f004001210280404101d40c000c0748040c00562182c0030302801c1d10350014404c4413143c958082c1203845200300100a00100e01c0e106844c01048a1012818080d807460 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 195735953 1250 195734703 195734723
    0x601050405040203060103230102030a050f0f0c0f090109030f0503030f1f23030f0303061003110901030c020f070605040e09010b1e12030304050307170313171c0504 72
    0x550512048880a03980070754190700c01c00040000400b242340250f100d01c40030003003140e40ba08011a079070a81e00181e90580050fa01e80c0100202050500c00700c2d0740c011009035202d00c00d4100200041c0191181c2104002020b40000d1080c0c03869018800303540003103501c100602c1181d0043e040c000d841e038006580300903083c6102c6000c038a000c80e9002c074000c00d00f450001c0c200c111610388000c5604000b80041c3c034607010100e10502ca00c40e03940034006c000c0840081ca02842e41c0b40341000410980525081005081c980b604040b050249041800e5805e0f8032002e0030f00058000000400b039190450300d142141c5248504000031401c103034040c0250003100c8e070382c0310014007a88400c1c10b171500307a91880c5c640541080103003645002c448040902c20503004005040e41800c0103880c4440c07400e40c1d00484060b03549a00000701c00040005207104a03030300a0030003200e28114200404404a0201402009420ba2055500b04000500000121001c0c003420690b5402042211a0082d0250404840a65102c044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 195737203 1250 195735953 195735959
    0xd020d060b18010f0e130b030105131106070201030e030c0307110604140f0f0406060203031e040b04032303070c05010b0406050a03080f040b03040516050d0305030c0901030b03120c0601 81
    0x615020b80304442d12040c081c0100720a0340004550544e544500303002042001c2100c2c144c96141e08041010740740303107000301180c00c0060704145400e40e076015100c400d0365820b26881c2d0380410084010168100c404070390741d40c2d81c1d0b42c00c1c1c00100c001c0c000344401c00001d4000020280c400e4000000103204440c450500d03007468407690010803500b40102d00c01c0701e41103031801a090201e0310b05004039402000c4001c010340800b84002010904680c2107400c8180960300c00014818070688061101c0c0d65042c030040c1c070603090315095a40c1c0d80c0d2044094401828410782c1d4200d4200d0765400d440c020f5400b020208400e44030719003040008c1c5030f1411124252519441c004544e00d450030039000310000d5640140400135640e1035555151301951203e0f40e400c0684006100100340c01c1e808800950103980aa00100f012250040e0200c0840d00154402c6d88074040700801d080021f504102926448101c4882c00d07915029140016405003202d540240d6050007203004009104410402504450140e0412075285a132 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 195738453 1250 195737203 195737219
    0x1060201020f030a0c020a120306030c12080909040501240611011418030f0304030306170106080a080306030a0506040605010819020a03020d03091a030106110307032c060d020d06 78
    0x10501d0307050004110108000784c1121007540000c0ca1090703c43c41251034004454581114079980041c580b00004d445a10170414003040742c80000144c01441140501149582e072008400d201d0100e1503401140b11100003411b0100c29409004648070000c424000214400b20320584402c10b406110301241038a0706948041c01e0510900c44601c03c0356005c00c2c025280c3e071110b005290404000c11007070b07200c02c00c0070001c6001c030180036500852003900e000c80c0644c04c00c41d00142044000b140f0110b0390785010010081751030300040c60003100360010000b075942d480b030700080782c140184203501034400d10950050200700030340c560155040300c185c9800e41d0101c07064105c2603112404603080296001000c1079042c40985031494090172070074840e05006070305d240c3e200c000e110429441c04541580701c8020004112030758102d01c20b441c800300c42d00301842c13800b201c0d6500076007100041224111590101140e0703044c0c407101d1100c05000301100805807500c80004020403c0690f106140340085103040c130b00000742d018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 195739703 1250 195738453 195738457
    0xe160201051e1306020c010f0c051306050702040209101106090d05070b0a06050907020a020f01030605090a09060204091805070e0f0118020d02040605030a06060504080d030e0c030609060f0106020102 87
    0x7a41c01400d600619800b03140030002400b8090403100040e6541c403400046551000f80a1020320500101d103401c200311039003084680c0f040c1c1c0c1006101c1c0401000004900b100410001c1d141e4270b092107503d81080d4008140240205a40140c0211902005100280d003010103000080c40350b40440700d80340c1d02c1580d05501d48001c60f464801040d02407180c00005071010b03210942c4054800d1740042c00c5582d5100040301100151898005600a590204198245000340d00d842c0542800d040c0309041c50140840c58501008040052040d551074040d0b0401a81d50115001484965000e1207020318030110034100d5800000d04681500c5041c10000b500f4840e9803110748110306070700362010142c1c40d08140240042154404000540c1c0c00c00c0521080744540c03028101070a100d5464580b0f0b481c01c03020200c00c0f90850b801000c14081c0c00d000030041c802d00040c44046c0c40303000d4a0042807401a00064610f80881c25003415810700a42c010020000c00011b0018822400c090042081e642c1c0e03150160308038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 195740953 1250 195739703 195739711
    0x60c0e0a150f030228050c0d170402040b120102040f170106031e110310090b0603060c0a110c0a0308090102100207020a03030e0f1e0102010e0c030a030e190e16020105 73
    0x800d00e8032812030701083c0a58050b011900384100711480d070914104520384a103030036407601d102003440070901581c410420400c0380c40341211820000c0440d100140621400440188002c0c4170302e403280e490b00d00b2602c422000e030403040d003140000d5440e1510b6850000c0b0428007030180b400301150100003401c8003c1c1c14003480741140d0700725844c1101c80c030a01d420b8030a2003507034800c00e90380d404000580c000340e074808001210704100c80010001d04190300f454542003116020f400301d03200794000e0040c820595000001c59031a00854280404c41c80c11404045051204107800160302c80303800c1c000001401201002032000140c00d034203456031941301952460413801805c1020f50407904130082480002d000701b4408070b000c24002d1080143d880203000040400c9100030405038040240480080c540d602406482c400b281d400000c1e02151004001081d507911002c40080d040020000380a03409466000e82d204900b20141392104509456401c0c03d200c441d001d80d1500816a110303c03101c040c0320f1061040f5406 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 195742203 1250 195740953 195740957
    0x11b05030a0b0d0b04030302161403030f06090f190605042c060705090f06070204091a090c030a0b0c090a06021c11060f060102011122060807050f16060c0e0a15 70
    0x5510b45d41c03011030082d0400358542044481e0043d802d000b0440c0e5500000700000f8400003565285400007080c0c5082401500c0240950f10031814010f042a0030246158030170445480c61200507444144540541a15032100d50003a1600c0f45c2000036641c80cbc00ca401c500074010081e444ca600b40d0440c540e80d2540200e8040c0001030060217606a6454054045400507200504070303030608401c0e4000800710b0f50841401c84020401d4021801d104030001c90040d44403622a0181441c80581e40c04607445124540e00100160380c40d01c00218019003e9003603600e0444040d00400346283c450801960300c0c103180b1131080b9460112940c48401d90b11800711681c8601806020b8031041e2144031050102d400c2c05000b280c1595220401d040151001c48040d021900c03048220b5141c919548008060440c000d4001c9c0c02009829000c00100580003021030302c498904880c19079684562000e0003249207048140100224181405290394a038080241004044100d403082c650603a60107480740c1906141c1180c0e00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 195743453 1250 195742203 195742223
    0x102030a0e0301021201090b030708011a04020313050303040305030f150a060e0f130b09010b030603060402010c03020c0901270911060d090b04030305011703041a0309011b05030a0b0d 80
    0x520180704402031040c110300a000581040c00f51160100400001d03080f04110554800c00788060b46020003040c1300602c10440204500910403090b450201451500b59004540000124041c2002d0200181c0c42e16008001d41c6d032681424580201564026980a00c4042070480441d0b0010104081c04189040040c0740c1c0308142d290110a552043c0d5241c1400da1209071001e05e21080d45031858001101c44001c4400220074402a081142d8000103030002010241e051041203160784001500c0c0307801c00d80908141e0042d04e002d00d4120301e002200301c0303d2a00003050100001d0010341040c841e0ba00c05081d0380c980905002500c00d010f0440b800540090900c0c0c241083c2c42903103081010042c07185105611002c110b002c010303110000e500134240d50481c00aa59040100241009104529485085000034601d02442c1490228007008880d83e44242c411002000c02d22001003544000c050154248903d0101c050103403003e4550f410071100e410074642001001c004a14101340c5913031070607501c444062 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 195744703 1250 195743453 195743467
    0x6040506190e190501021c15090603170702060c0109060209010e0102030c100c050705160303020601050a15032703020601150201091e0f020a0f030320031b01061d01091a010203 77
    0x1103e00007145820b8449550811503800d000c4881402d030060041d1000e4007103101d402c0a070119400030080d41c0642403442c1340c50800e00004030102d2040c2d5010710384250040e01da500c5400001c81314410003600b41221342ca0302982c2c2c03041040300c0e000341a120f00f0980b2600660540c40005a03124410310015080c160844041d0712002c0d40d45602c000075030b02440c40d185042103650b50f1102d2400b101d1040500d041b95a1003010000c06604201e46800340a0075030300706162500e81501e41040140040d050b200b8561070310f0103a01012aa00140920884c042407080c4628115041c06501d8132001c0c0180340c03079088201002009180140200d10b1101e501202c241048005100c00116640005000b200d101040c495943c02590b580800d200182403018000300ca1703d841c514026002500305c08c45c19050700001034002400b000c0100503280e58801241c0e0703030380411121001c0280148040d8000205803151001c080c07240ca1201442c5a040e541000400c02c00d8102083c0500c2c401e1400b2101d803801a80104000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 195745953 1250 195744703 195744733
    0x31803110118051c0e180a060b0c0d0e040906050a0b10030e0c01141b0d0801050a15120618020405040e070f0b0d0609020f1804050c0412020303070506040506190e 71
    0x40c0030742115290107112045170b01c0000f0154050340003070302d400204c004140405589503114101c010b01581100e00d1601c082c44610b0764031440310100d002c05102c1c1070444690940c4580d0440c480b4a540000100100c0c0f0304540408010041e440c06140a0380514401031a240d01a11551031200810001414103061280c0110342d0070b0602c0501c7c6c4288070081c824001014041c0d0341c03003803000503100c020340807050307144000030500d00d8140c0c03050344251a034201c1048040e00c0141c01c0c00b00240e0074640b104600034a1b03404103001e400e140d80300d43d035450035140180100b204950b001d0015250125001d11886541d280c40a44d550300e18080e600e400400282d04103c000c850f00300406c0341203014070740811129660000c4000b2070b0091440c044c0e1140c4001600744c0c0d5912420303d02412880d0845003042242030004008140e8016401880312016032194020159070742007080e2108a60b2040450300e0702e150514025440d08425038900b08038801c5610802c10b0414180203400800d202da03002001310003c00408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 195747203 1250 195745953 195745993
    0x301050607020d0218160e0105040605030a0e0a060b03150c040905040302120c060f0a05040317090f030415091a03040b060a0806090a0309060e0f06070303180311011805 74
    0x801c990042100a2400041c1c45070300c1c00504055000700c8045c40c0e8036100401101038000c0c0c2054208200c07912002c0c2c4203ea8200040e1002d03123510380341c940d13101d68a01c490a8010041031381c010641e40b2481c0045010880c09400c03d540800084d0281c41e1100c0021200c000400030950b14843706a006100900100010b0ba111079032007070091048800c1c244000d80010304a5200c03d0300107950b500120304101000384042102a04141152401c00251400e03440050004103240d016210010640700410f40d1542c040122840343c51004007035a40d00ca41c1e840004960346141251000031038040c00780001d014094010b0b0090a44440351000c0c1f460740c4541d2000c0c40c40703038010500d52303100c0440d1201043c82d0b60304003d030074803600504000b006005070506001e0040200c0360300210400c15061074007040b07621002801d8407481801d46060352103103002c2c03400340d01920245420810105051042c401070550000040c8005c4131040000c1000306080549609101450704002d0100d50250600118040407000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 195748453 1250 195747203 195747217
    0xf0c170d090e0c040b030f01050102010c0804120f02030d060b09040b06040302010914180a1d061324020c060a0e0307030906080405010f020c15010f03030e0d050c030106090c030c0306060503010506 86
    0x83c2e24a480d890f100101910342050383d0410b0030481c14170040c07085503024070441800034000e08041c00180f0f0150380d0490444500c80010342044083c00b1044034507402002640c00c03111010909006d51600e45500d200300e41c0209486038490f0b820403194030f001d07090038401c032419243c040e03640100c050b09008400c100840b54001040d0042c070220034800b20600c4142d15540101002800031801c401610107018914010612101e03041c0c0099061040443d0742d60752039541d00c2e620441074441441c11200107440d91080100002d0f80038000038854417022008500580b003408031140401100f0b90400420350b9038000e00030000c2c041404042c0a103d414000c130f50803a806449400003080745601c60075000140d80100040c2c3c0035550040a01c0302581205400c400d014290013003c0030703d000c6c0385840c0104255269107243d800350030481100d0f01800000d120715199404050000c1c0321140d5506002d8000b031070381d18840000a46001d000300300592107800750008481c1d03541c3d08c1d5801d40c1d0800080000f6540002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 195749703 1250 195748453 195748471
    0x6091308030c041503230c1e0c150f01060804080904020313020a03060c110309150702030a060e03210f0402100302040e040c030611041206050402010c0f0c170d090e 72
    0xc00b001440712030308003616552506a85d804500c82c50342d0104e0410f200f0b041c00290401c3c010740f008001c52110035500b070345c8102c01840401c1454050440c1036001c9442440140022805040c65544100903800300720307402140c0070703003920000742e90320b001c12100c0c09415240189100b8040040c00b0300c6180940156404c4690510641c0c4c02d401243d001030700e840c856600c00c40711030382c9407111003600c55001039401550020540244d4901b09a44000807010300c2c0e03125407006031550100348541951801c00035816140c1d070081081103019015801c1c2a40da801210902002042010740351030944202c0e8102e41c001d07414640008040c1c0c541307500f00a8092030742c140c242c04250b4240800102960100703007003070089010b4011040f0305815820104103a4108440b102e42d200410002000740348840895400115042040012070307072202d1004031890b40003104042d052000c40314168041c0a80d026075441140c20085140318451044103001d42c80d40341e045621800308000b452700b004103c601e100310380d5000da445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 195750953 1250 195749703 195749707
    0xa120807051611210105060a271103010609051c020f010f050f040b030411180a0e0106030623070806030a14070b13061403010f050d020301060504050a0f0506091308030c 74
    0x880e000c5982003c13103e01d44040c1c3e1680260500381100280709a5400003800c1d03881c040441e0500440040c16040081144a01c441c2d1800261140413a07030310100781402c0700c2054035030303e5075205002803200703001c0c1c080d040c1b250007084000d0705185407940c0100c60326580079141e845159034120054483c810110724290500004200101035108440020805040c40700c0c0000c0c1c03681042c2c10111a07000c41101070a0284808240c2c20600311404505941d0116003440301044054040418034054005548000d00f0682840d031501811945145a203800350340c5a03888000360760341c0d514200c0e464030040da6030a800d5041164000c0210359000c101e10310000401d81125405565040d81800e15440100c0a200201010300184240c50340b00707000051142c106c8042506550500c030078090704020521400b4030130030f0034501c6c00b401c54070290410001844010b008102c10314010b007005000e4101041442811481c2800194403440c1041540e80070301682440707101d03000d016640b4040190b0028182100180e42 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 195752203 1250 195750953 195750983
    0x90b0d05070f081e030327060406051e15040c050903060f010312020304050a0b07141005090708070e15033c19150609020c0a1208070516 60
    0xc100094401495000d5004501c40d1a1582c1c0c0b904040e05840e901c00c01003034035200c0000f0190b00000b07807074001c5440749040309a422031050020b00000c0c0018501401e0058808000a10500d54000c40c8031701e40300380400f462126611100040c0d098100c030103240702d62400c5088102c03070600f60700c05503500500e810018500141c140000c0c0c5000822600403a1203007141005100f00304181703445014a0301c0c9800114101808c010003e036182040d402803c003c042d01041c05400c0c840b4184814a441a200040c2c4e040c0c0040c1480742c10107800b0844030300c48540706400c00080c174804001031107011a1201001d40000b500d03071004c2d07901c4000350301c00030a5042c400c0040c040003505550759120f003500c101440a8a40d04089190845400036a148010183d04041c40210303441d60410f094003031243d03000381d88034105952101b20000603e0701d0b4100411003031011a114a03d00400154000300034001d010207403c0c180b03160811680d0040456200c0700043c02440f07800c0c00b00e10a0341b84417000034400d0f20a40d850140d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 195753453 1250 195752203 195752213
    0x80c0c0a0803071119060b01020601080a0807020103060b030708070216060e21030313020415081c020f030c101817070312020a030c08071107030b0c070f0c06020c0604030b01090b0d 79
    0x200240820080c175505105441009210301c5840c0f0700384001c1c00600129890002c00d251590880b003009440b88900054460840e07203ea480074002d4095048a15140e08050700700601ca40c00c2100c01c20098841c68a19013002d03426058078608540890351011080074560003480310f45410040401051030740c000c010f0041d40800d20181d03208800c0e9949041050415004210039240c201001448150300d284090110a00101e40e10b00804003044660f030120080d000100e2620342c00c0101082d15000108080402c3c141c0452390410445071840144010021100041d51200b14541c004042030069012207910082141c05006d02d54000d051003000f01da1034100341002e9034810390084001039070b510904000940c0094031903401c00700a00d02152165200c109a59450300366000180207040e0520014030440160011280e4681d400f80904200f25200d151408400c0d04c41e018a2003d40110310220145080480c1520308513074009011458903403030b281c500402044400a090340084024401d040421 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 195754703 1250 195753453 195753463
    0x4051009180c03030f030f05040b0115020a020316091a22020d05010b0d15060203091315060309120201151701021e091008060d03111603060b01080c0c0a08030711 71
    0x503001c5c2d241c0503034201c0c201c0001000c40740070115401080d45801c0c20320010a0f81000c0c10360544010140701e400d5030385d49505c00c0e850601c880a0013981440344072611030524014501140c1180d41c112800d208014080c81541070f1001c2e082480381c0c1000c0140c010b0030440c04580c140d01e5030083e00c01e0700185080041a00702003642c4098010b00e12181c40000c100c0802001845402801d2414481c44a60907042081c002c0d20383c401c1e040442d00c500010203109103c4030081e802141d2100099510901680d602d5402901410214806644a000d0f94240300001401805071032500401f205000c40782c03d0400907014182d103c02c01108582e594248082500c2c400810103150486d0401700398161209013841c03c00001040e0002203030100070480d0f0621200b501c030f9403250565280c1c942413030b1420071800591246040c003c026200b4066500d5240007060000980c08000c00000a90740e0210654562144a105208074941443d980e403014505401043c1e0850107141c00403810b25240f0441107540207014a04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 195755953 1250 195754703 195754709
    0xb0a120f1a070c1109060a0504020315030f010b04060e0c04062f01060503010507051201180e1b09060d0f11010509060a0203040e070e0a0e0c07060203090a1104051009180c 75
    0x41096a00410180401407500d1380300c048044568000301e19201c004034400c407c862050600544d00840441d090300c01d034000d02c0c4404440a011034902c0c0521084d0140030b0a806505980140d18101c4007003810703c2200c003054800d03004410010714040c54904222240c4541c1c0036803050a000e202c2c800114400c034404004020494480003141541c1404201401c69001034108000e12008001c01025801e440070010f04561196041440c00038589108001520310491492044d008809910145600841002c660840e080d598003070071f0340d00c2006001044141c03e9010f0140035420880100060141025200000c4c0601d0700310b041c042e900c000f16116030480748101c0b025810200c0d061260101c089900340d8130010303d2400201e00303070305000402c0c9000418000c0d80710b412030420009000000c810110b072030b4a070f44541c0466803840d0941409072100a0759908035a5520316015010700f908d05405010300500c000d0460341186450800550001d000031402050f044480b40c4500c0d0204014600d40001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 195757203 1250 195755953 195755957
    0x302030901090b030603120702040f0c0507170403030806100314010b0408151b0708040317040501020607110606040c02070b040306050f0115080703110912010e010b0a120f1a07 77
    0x480c0c0280c00058240d804a42224003a84400d10401200d0f541c0042c18480d240c84040780c007581c840700340c0082800b400510404000807030400016003040c40c2d0060051103000d010f45860a40d52062440e0032007503101d5480080c0002c0c2200010410502d00f085025010702c009080c00254404003041d440400b40c000d0340110024200030508000828050145045076001202c480602e4036180d5a0600d60300c3c0a43c050b0402078802181e03400c2088003d2040700e003c2c43d00b080301c0c08415a80c217800c44d4881d500c0b5028450041c0108004980d072540034080c1d290058900c840544078507550030f4103100c0141200c5000e10b003141f140c40340019417a0b810000600185025100201c1c15203858504160480b0701030340107051250f0a034050008055014403000d030070a686145c0801c004042c080030fa00b950048007501a400803408a64540104056000c0d50914001c6002070080ca540e160422010460a20403000c141d5852860800061003110a01d1140c500c174940d2311541d9441c03007001c44082401200c1d0b10380 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 195758453 1250 195757203 195757207
    0x15090901020913060e0703020a12060f0612090b0a0c020a0b0a06060201050f13030e0a05040c09050a090e0a020f0402131203170c0a080604060b0a02011524050a02010216030203 77
    0x40306042c102000f09095030102d07024401240b4002c00070900500c01044601019408036110b003071039100300180d04807240c0c044014810070b61a112000030b00c000358841c500210720a00b030603502c5441c40307004500d00140c1007400c00740290f80f6031603a40040d10701c02410f5011805421000707000161814046400f40d1300d201e00000c3c0680c00c0c07001c0a800c48402809110200c40a0000c005036044c9240c070248074240e06103015030040c49500045000340c12640c010030341c041e06100c400b00b200b542c4808803000716a8100c03400303200c4039614071201d07080b01c4540348050340d507800c032003001030142c10a240e8840f00d1800140c0010300c1c0c000c0351342d0168404012a0040c4610040d098003203c02c2c0740d07000c0340d40100001d101c80c88040d103041c59602250588a400030030402c0c015502c000400c6555140d124100900b6441c851a5950f00c0b0414000d0080c64240d840c582a00802c010210320390000400034980c1100c03601ca00c64810002080039038503134003d0100b00301150340030014030a50715650b0000940c958440d8004607 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 195759703 1250 195758453 195758467
    0xa03030f0e1f05090102030108100b0109120b04030f0914010804050a0b040f03030c08220f080a021e15040f0606050307140301051f05010c1a0720060106020607081509090102 76
    0xda42002c4c01d4080f5583c018070050064001c04a50402460301c220f04c006200d4005100595907092a80c1c8403c48021a004820060002403107145209034840d23a180260101512010f417607807d1039028500c8103441580c1104004e5008860700d86d001402841240e13507524a40c0d695102101c8101e500f12803a8550f401c1c101d04042e01800f030300b0009060b9080000d101c0ca0090203118844ca4031010181006000b1402001072000c0907111800294001900c80e9030f4070f501d030201941e05d001c0f681c2c80c3d001d41901c1c5007a50440b00c03008203281e08040881c1c0d0386080140c403603440e00c0001d1038032141c05582d51691180e0018207a03804004d200b00910781d20840f10f0540c07216904250851b0001806543c3c00d403c0d400203508420005c2403600c0075107409003005000c0500038280b0211036440500c10341385603c044014031066036004940002110303040058080001c5404041c141c480b1420300c0740300c001d6070000b00800c0311240502070056000990030303021010301c0c1c50000001d000c40400e403180d0629941c00a848 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 195760953 1250 195759703 195759763
    0x10612140601090504150225030801060f020609060115020f01020403030e01030b0108090a0b07050c03040f031707050d1b02100f0e040b010507080d0605190e07110a03030f0e 76
    0x1060040c9100f88082055103046e460340b014132800c0c1e00d0201e003016070016181040303141c6400300851071601d800301001400b01500c1e000d06130610078020180410415200c03009203a01c0040c145100d90f0f0601d020301003e03407910000c4140c2400a01e6600c01f0750241c500800d003505401d00c0a0401180603035205e9003a0000800003408482c0a44201810402c0010400145c000001000543e49910045c1440c1995032000200c0c0d03540110107e450b0640000100015688009070010b02034a019902c60005009440c0d1031404620a004009003650000c09083e82d402e8090480c500040000d480c0d040024100ca60028940f50588000345003c900503503222400203500203540c203101034090f2010028101510000303090f90040d100d0080c6070b01c1c4009900f03070b441e1b03440d90400c1e0000e0101070035032060320100d0a810510300005014030300324a074440c80020683d40c45005555188071a55001e070058107501c3e28114081e00000700010442c40c1ca40080c165260410084d100b40e03415011407509040d0008145 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 195762203 1250 195760953 195760963
    0x90d020102121c140618270f0c09131101021e010f0b010504060903110a030203070e040303050603030315010e030a17180d0203030906160b0406020a020d030e0c1201061214 75
    0x1ca00e030551100f000c002c40c0b903d450640409207240d0170221030141e47c6600c20440d6412888a000c20307400d80001c200c413818a00000c0d03030700081e000c08050350040c050300800e201040504803015640c4d03100800700ba5010800ca98003a00c802041841034515181c0c0035150030000301ca80c0a481c030002c0e95113a40e102180c00842c80341a034401424a0100e103000e1412400905152082c000070745041c0d540510880030355100207000000b16405000d40701101d0b503680300b04550500c00c0301c3c2030340428100030008415207004005c51740f040c0384014101c940303106003a00450301900d1030002244c2510510401002050791043e440e514101445103459842d48604070035240c810b0042c540c00c0c0a014091007140c0182c1e800b106866400109542c80b9484010841d00e03003028050005010304444101e4041c442070000c3d0b40c000b402100907035001c40340920400c030b004500f200c110030712819a41d040040d81d180140350614100311b4107510b0800103d4040d4603031141d200700450128007203525050402c00001c0f2807c8c1404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 195763453 1250 195762203 195762221
    0x8090a02031f0b12010c0f0c080304121b050d0e1806010311040b0409020d1d07030b09161d1f0302150403051b12030f090d020102121c 59
    0x28015002080d804079984409094840000c00b58120781424030005681c800b00c0200e02c020030103045400c4d02e46290740240720040d10500012810320f500c01e0306a000700741105056512100b498030710340d00e50f140d00c2c0d00c0a84c122400300411605400d43d00c004030311303058044101da0003403018060742c82e100031000d003c00b0500d442e10307130240b110024003003000c07880000300562080003820007080c049241254151103210b103130440340d00c40c5070200d40410300003a10750180800003040c400c100480c40c140201c50701c0c0e0303a580d41001c4806610064092000030302c209100c0f6080950744045840c21b040b5014603c1003803500d43c0284c03a03002c2d0010000740c80e401d2404142d83d004103c0d00c5010100070741c0c4c1040381c0c565100f030303000203030160060404c4041160042000c55005503040801d84403640c1040207284178500c4116441442410a00110b45580724048100e0b0700d22210212071030b103000c200c1d40500441031111801a4154010100014400304c0703004002c00c80c000342000c0526a0002da020410110340c803540e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 195764703 1250 195763453 195763471
    0xc08130510030e0a060506060408120903070603092609100509190f0b070201170705031005040c05091306090c110f011103060d11030304060c020103050c1204080304110415030308 78
    0x12000c110b948004201014805e4002e10082102c0d0740e0800818214840c942c082c00040c454000c2081d100411a0050103a05400300c00741d1b0b41040c1d407078000300c0950340520320145c40d0342d402400c50412403049401400681400071174941c241151803000640c0055001220004140005260021441e0a2560b004403d22006601e9041d500303108119881e240a40940c6100d000b000a82006683c001c90b0b000d0a01d42861401d82e4962400600c001c0040c1c00c01c4e58468045024194042918a4540159480e040039992000d0801484100b00b2900e41c0c0c645441d5030109a43d02008100401c2c1402500032600240d20760386803502522803070070314060116003c00f0159150070985000c100018040340e8020001310b0302003010403814201880280b50b4015960b0b81403000040018800da002424901528000d272800c1141e5540d01e02e102c40301d88034201e0070000780300003c00004c000030748100146400c24054a00c8c04410003480022a084a0710001c1c1c03103003902c040c040100109940014840d034011551 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 195765953 1250 195764703 195764711
    0xc0a14030618030403150b060a171303210209030f0a0b09070e040f060f090318080303010b03010b0c16030b04140d0804020103052a0a030c0908030909070c0813051003 73
    0x14400c2070340f203020302d0000070850882d03c4250401c2c030714541c00c45800d05000614280d41e40120450203050300c00c0513050001c11010b110009a403105065011341301e440d400d41c44540da8440e035501c00410b0300e174942a011034690b80c01d01019489460412a40d0b1041c1800ca0090085180d01d04240900801c0100071840560000400384a050b01022815800c00e038000c0544620341050b02e803040103420200c0481c0f6040349401000411300d944044035015500108010800d03454a40c103045449100901030640401c1d400c000401890000c040148400c019000554030303404445083c40e05002c10b16442600c0918800c0e09220901489011000700781040740000e0407661288540034040b840001d1000e410b1660318070008501c0c140310304e1140012140d00c40203d0f1502e040d40f0284080b50802605000064604940c02504602a00456082e030f81140c0c000e5003483d00c1c4904000058100920260400c1907481c0c04c03000040004003d030180030480441d01001ca402c001c140070100714404940d0f4205414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 195767203 1250 195765953 195765991
    0x140a150e01050901031d070510030e0c060903010207051618020c0d11010b04020c0303100905060d1b3201030b1305090c1206101410030203090c0a140306 67
    0xc180c850000d02070801640707400404005800621401e10202c001c40c411480344500c65502084000c2a0f580455140c4400805840124203d50008001402d983d0082d030448504e894501d0140c5207100b4024005032809400d507a4807030400e0002000000182141c3d9410f00480303224503200040c594200c00114107141c03075840e00c290b035960440081820302c01c0741c1350a0011010203411088025001501c250b6a032003c0140303540c0d40707600c2183d038203441c1069181c01044501c45401058005c2174010002c0000c0c00f034039240c48035070740165440700101600401c1c1c0040d01e00e48500280c10380401004402240600c02446181c0e81085050118101450107034100043e5850680001c58001200310001d460b035614582c280c0341c0000c40440c41d41c00351a03002d64201e00031001504601c20424040c5520341e0302d660b0ba418640a0400c4400c45c1d601025401c04142c1c01c9100764051035110b48600300b03e410f5442414042400b03078415402c4141c80c101a43e40007001401c08001064100070505121008582 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 195768453 1250 195767203 195767207
    0x20a090608090a0c30030215130b011d100602071203020102130b03100b09060913090c06020d110304180c0c1b171b1002070807140a15 59
    0x654090003007401048070108004800400c50a01941c0d48541143d0b100d83e26500603e608528020904480d02c022a00e02c102c00103403940745140e002c0d4103400a01d89013080442a004401c002400064150084030404000c554640c80b428000c01006c029060501414090b4000300e0000801c0d070100744866400800400380e000809108075503021014004165441c5001ca019202d070800192a245410101281340120000114001c0701c0d441b607200000d555941c1400900d020b040b402d80ea0082c0c0a1050301c107a401c4c86030b01c05a5651050000145100d003564440080b1440754100800592007580054246a000981c0e040b20100c40b50045003894545409000c0d080700c1c003500e0b94a056224010440014010a1104c0e4010313030001e6000d410f00c0d900b8000300c440a0507803103080b150820041d0b0740b0b500c0d458003140380742c0d0490180a10724100074a82d010320101118100c0d90030218440d103000044d5444051020b24081c103110701203600fa6000f035100b0019400c1c0303183c0010074002c0d04c40340301d080001c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 195769703 1250 195768453 195768467
    0xe0a020a0e010f051210060e031605040207060f020c0105070206010512060109020f1201092f070b18011a03060714031602030d090807050114090a0f08070c0f08060109020a 75
    0x80c0034600100003601d00c140c00c0b20a1702074865041504000d5000b0701048048059803101620510380c0c4040726014550308040d9182041c521030040028070038000d2011742441d03002071848500840d404910f00c50039040c4030701241d1041c2255a8140d6584c0148040c1a606011160050100302c0d1900c04a400d0500344d5500e9140c180700f2404066800071b410114460322100b41e034684c00b1038043d5a02c85603991125440030348040c0b010440c444500c010045a81c0c840309000001c1e590401c02d10ba4103100d8542c0e140f010500c130103012885110800008209015402d025604c0544403161092503804a00000e03d86000c0c0054440018485021403611100030309009590380001d4845118200340e09445040c0e003903104449079010100c0c01e0416003428070000c0b100411940784184e0007000020202154410000c01c143c90b01c0c6101e4024010f03c402081440d1405803440e801012101e161109a079030300e491a510550188010b007056040803c04060180000d40c01030010304400d51518000c40c0d40103200d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 195770953 1250 195769703 195769727
    0x9090b060909090307020f09010f0b1606180c1a09011b0c0b0403020a1d040f0c050a060c05060603011e0b010905040203090c01110619050c1621032003060d1b0e0a020a 73
    0xf12401144140c43e140b000740c80c074088540c102c4070811082031210ee01922510024205445204d541d000000b19259042c0c000c29000c12000905400e04600000441c0c0643c41c110b034180b540700701144074034085200003940800a203039901b851581c6030301d1841807015004056008580c120ba05200c0b5152070308900c601207a02680c0321448216900745864030b102c0403502d68100c0c9401c03488482c0c01084045d00203ca002145000d201119a16903503601050700340c8254a82c54103181c45290b0300300c20340407142d8010100110050500d00f034603d03100c01c0428200e0300300300d806101c554481840307001e10f540c04c43ca18100c2102000054240c41c64070407a981c032030160080b510070303405684000160b100d400e080e05540442d1402407050039039518030705207588402000c542000450441ca02c100310b83c10300030704c207550052520302100c0c440050b41c010b03121910b400040c83d0030b8102584504142c0090300c00449010740000f581402c0c3c00c03075420b00d081000071240c0104210301c070a1042000191942e000b041c82103230 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 195772203 1250 195770953 195770969
    0x201051e04020a0f0b03040b0112020a05040e0f03160c15390302060406060f0e0406021803030d1b0e06120924061002070609090b060909090307020f09010f 68
    0x10030746562010600c1416143d000c0428000e0241d40411035a4040004600a500501900c0001d0340caa10b42d039000c0900c0400020f5000320044820460f5042580009100c62280c0054501e00903036000c4160440e48020302d1400340744d21225401c0200264500d21f5400303450311040b4110407111a601c0a0300c031500300c02c40600150340031000c41d140701080444500c800003a90b82c0280d20b5040918010b55038081c2504d045030480c2c01d210b400b00300c0210b0503a60364101c4180180b0a55591035540702c0724020f50204003080d4107155480c800c81450b40b0300300010901c0f0ad00613000020701c4558110910656890300704400200710040d9550104e90f65003034103503844034008840119841c1c8804c03910500e4410050340e503032104101c1c418080e48e180c032003048091103404180c8010981440c56030040740ca13000d00380a00d00c0858041c1005110b60700069210750039030b0368054a03051030104880000f81417503404890014095000146c40411410074090300b0400060a4900140707e504081d41d5400c074050502585074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 195773453 1250 195772203 195772261
    0x10206070e030307021c1103030316080a060302031606020d08070509041518140c0c0a170f040b1c0902010806220204060306050909030406020a0b040f06151401020105 73
    0x20760780d024011111910381c001c0a21210780c0089640c042d403240325600541d5107100f480382c01425420040226807203025010246030344641c5041040c1c407070040142445d8019940e840d40403005031070421511410070018030071061882d00e0148000c2ca007402c4c19100e101084883d17018881070b0781e00030064904102d41101e0100d0042104040e21001815560081c55402e0b681c614400000c1420741c000080d1505650280343d95640e80e5003030307011340e120745020010160300c9601028046151214000aa040c2c08150700d843c00a0802e541c82243d001504001694400011001c0b405441c9c40c1e032014000b19000420310090440f0780003e001600c3c000c00142c010b9014140684c904594003141160031200c054045403119112240280100032601810b401a1001c0c000b03d200ea02000050710216100c560040480321402c1c2d42d529a244806403048615110703501e184400240c2c10300604d40044080013a154801d442d000024052280112040f8156403412041c4050450b1030b004a41c0c80065480c0d502e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 195774703 1250 195773453 195773477
    0x1b0c0307090c0324090f02040e06100c140d030b01020609100f200304020a050901030803040809011403070f0f0f17060604080d08040b0105060315090709050406060e10020c01020607 79
    0x1034050b0241c0110482c852200342c900060040d038040625094441c0c91408100201001300c071b4008900c01e41c080c181301c0603001c80000b00c0c0d901d00b180c0a05403078651840c0540d50ba1040380d8600381318000d85c034016280d9402030031203185202c1c1e15124816100c030091000b02050b040c070000c1c0c241c440e174460101440305a00e07042149410031042d00a005141d03500408a00000c01200f40d0b0580c0d0740090710700700d2044103000c80000d0360b441c2c000c15a03070507a500400618074680301d941c0c0e20a05ca038480140705040c044040400c0d18045001d0b0086c41c8254010b440d00404008171000040407403001c24a07130400e028401055801040d48911420030040c1a480b4030a541d031204000103120b806580d000900511a00d0340f00c010030b9500110042c0070b10f101c3c11903003107540d032107404000043c00200d40000c10700d090120b02c6d9401e843c00c541042d0b000445801d08038000c90311040403d00780c034159002400440c5820480c15440c0c10401040d06414406201070240c0021000000327440e814090841010040404409 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 195775953 1250 195774703 195774707
    0x20312281b05060103050c010c03020d12060e0109052e05210f03190207060f03020d0b0307090207050c0f0f0d03030e010516021b09070507050a0c0306021b0c0307090c 73
    0xc40300e2100c0c1c1c1c00445035099100c0c50025603429007408101c595001e10381901116501074424a0756080e0f02d500035100b005e140b98800c8808aa11410501090783c80c0d42c030001e401c00e03160000a000e030145140129032071520826101e5503000600c0d4141d04259a250000c08420440c007100069440480340c01400c812075220314006018041840c804034001d0340c015a441e102e00100400103143c0d42e207078032503420a0b40181a600d41f50319204000100740301d010a02d03400b41c132039030051006007100700e0002814818140400d01d00001c9810141040c1e60010700314003404000c010805003940200c95103400044080c0c00302e0b00f4414804c812500031000056001d04040c0240c05c180a112041e03802045030340381c00400000c0d0100091f180340058013680818007002c01ea05014540344501c0944641220f4840c3e0344c080705d0b15840480c2c140c800380254090400001c4c0000110b40c001c50052601503205e03545e105422200c0610840200302a0f0302c03030500122503807400b00f16082121240000001c010785100c40c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 195777203 1250 195775953 195775967
    0x40b130302030903250602030909070f020a120e0f060c0a0b04050a2117091c0e06070803010608010b030f0103080d1407170a02040b030a0c2a02031228 66
    0xc0f541d4540a114101d441161581c40d518046081a000d0030b14090f90312041030340c0303e1059049207904410706100044c81d050003402403030a804c01c00d01c102c1d4003100c480c0d01e40c00608030940062400060072080c0c005c10b02c0c5024501d10314026011280645480c0740300743c1d00d0f0368807000b01f84002c0c501034a000001c0c0c184102441015069038101841010840c061034000c000c60100396007100100d025401d041c0364524207010b1151140880d00020710084151058021040304006a030340c08005035460041d1103a00c3e89000b40c9070039803040a5890301c0754104074014103070500503001803c1c02c16080c17003000708240940340018112900a030507559102045407102009e494640030720039a842d40c82c02030105036a40a205c60000d00c1105c0941c2c5090745800804405902c40c9100b080500202400421905185503001b1032500216062144809240c014a518000ca0802c1c2041940c0c40da89181d5080d401d0900540808440714450b4a203841800002c1005182d008803034001c0c1d11511702043d640e058000c000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 195778453 1250 195777203 195777217
    0x70201062414040b0c060106140702090c1b061911030f040c090509030a02060702030a0f0e060c01140a06060c0c1701090507150e030607090608070203120a0e010b09040b13030203 78
    0x1400c243e54503104c03425400180c1c0718110812107407207464000940107209403038032a0803030100d0090f00e252018030340810003200f90107010185c440200300a61141c190542044240607141000070b80b29916015610f441014900320362210600e082818002600c2009801c407940000b003041202990303111810071010f62142074001c0e1201a1803c0705001c2c00b040e000014059422240c0e080310590f40c0d54100c2240c89000307a120703170408039200702c90610760140190100c3c4509072020300080c0c00c1c034200032121400d5402d0034a002d0103201080d000c1c00300e490740d01d009010141c44d06043c9a1039032842d0b9512032076000b6041c403e40c000307520320110000d5007281c20f420090075503400604452410f9220284001420349501d1401d000c41c507100d090030300906022900c9071148140d5150307180c40928144042d2128003004109030300314082001806000d100c1c05440f1401131801501c00a00340108801413070841c0d1000c048030348145ca000e0100700001304d05200c81c0364055100140300c003410519180a034a180038281c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 195779703 1250 195778453 195778487
    0x70807050310031502042d0b0a180e0603060a021e0702030a0f0b070e0a0509040212100c020307140c0f04020904060e040602090a050a03080a032a0906080702010624 72
    0x6131000710b110301d240c0140c8156003265040d410350800d90304043d0301c0c440443d80035003864000c2100810190080c0e40141c42d106116041010195040121285c002e6882e5084032050301010420701c80c060508004144d40401c59000451600301d901c03110551040700e804c02800881c800084107001c549090203200c1d94283d0003c0341c6010314840d881e2086c00d000c1c08980200001d02c1c0c502031081e061814820b00000c56401800d508443d449680a101c00089407000d114814492100e094641c038030507100f5000881c4e03496008d03503100c501c01d00c2c2150b0003102c1c6290704c070b2503a030007010580701580d03a40c201d04450000c115001a542d5403d10007141c09400aa403004405860980401013400101d8005044500301240d03a607036416180e20411030404c0c0e1500020341058800c3c801c3c1e11840c0d000c0c0e480004a820a00760307545a080320804045c0c10303450100c40800c0081c1d1074600c208591900844c0060b00070507180000d1088a0034140442001c46a510681c3e40b440c03008500c4030003150094041008148038a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 195780953 1250 195779703 195779723
    0x1431021806040b0a0b070b0601140703091a0a021b01033c0c2a080f1201080f030a03090c081606090b0a1418040c1205090607080705031003 61
    0x4004501100c0804485050140c1e04280d00403105107410007680c0700b030b54440c8511a040003071a40712800080e10081c00c080c1807150304515004042d41c80782c080c142c1c5074426550107501034203200c409a202080076410403410042840000c2a442d00800d80001d104407540c110501c0c41d00303a200481c050031103143c140d15400c4a1340800c004401002207020f0010080300d07851204030840d031541d0801c41f031002841100048130b11450310300701c851a0361420b2032891881500100168151103051071640207400c0f010b51184001501041145685004c9004100344030282407002840c008403601e80c0300390303040346041541c1d0360f00d0a8100310316000c81d003000d0410130342121031000d1104030300e0016180500035080460361650340028401c4040c0c4c1110f01c4060542e071000c5824486401031540c81d040f001e031000380c032658181268040c1d2901d225190b0328000640d603941e04d1041d04011002110b502030010040da40040082240c410f4010710b0043d006149441c101d40d481c1d6802021803214101394100411900c18 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 195782203 1250 195780953 195780979
    0x110f0d1404420c0216061413030c090f18030206010b160b010807080708030306060a05160506040c1a03040807021c08040e040b061c020103020906041e0801143102 71
    0x2e0f9405068054544e07021202c82075075006144507143d005215910010b503118035545802c9455101600580d50340b0030460361282d480ba900c20040102c90340105403d5035860003200602e015902500c4810f0b81000d0301c0c5000d59041ea10000c1d203074401401020445030001540100d01d501150000d002035420a407000c856503110b06249840d044a40701da6120747c8141c900100b141d90f80071084900030200104a5890701150080565154101c04003900c404a03444110001003141071065030320492240c0004002c090402d004020030400441c020034030420300740200400650030104858086030100d840c4907800c1c92510505d19203910364100100610f20204000550054554403503024078420328586906544500901000f021810000e6161030082841c0e80c001d035000781d008101c41a000b0303108070700e0151118100b012500c8c6814802c0704030780c0115400c011680003841210004074030807689035070340c0c2800d141a1441c035071110886e50340d42c5881e511210459000c2c1c00207401a95014000c0c80310480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 195783453 1250 195782203 195782333
    0x6030c0903010e070302190608011412190213290d0f030c02180402030604030c0c050a0303020c0406050409030822140a020108090706050f030a110f0d1404 68
    0x10b59100c103d020747e218513007202e100c403603040500042d1030155030b8134402e507843c1008042c41070940d0310781c280c4c0050402460550100d000d120480c0d17405c80002120b462144588144040c6403451040380d4041403800d00000079041480d0f84000c1108200050341d10842c0306800007400040a5032402080400c3c1081c9080405400040000c1d2050003181c1240c519104283d2208150310304540095041d00700d140001c0020303008071240d5900740d00811107684110303110000300b04801c1031500f0541c00343c0d1010f08556400d00d8180109030127002c064805100011056401030080d80c00584a0f00588800e080c80b0259500028801032000f40c03c00d040625030b2140e00d00c1c0e03d0315041080e0081c0d00107107203000001c644100004941080311400ea541501d0500030a82c100c02681001e494900c0741502c95250740c0d00402e40001801482c40751b000d440d03a40c0e40c081001d00d8100c4003240c0c1c0800b00e030001c0c3d4040202290180e031310600001080b28210b4003081450601c01051049140941d54444441c048404000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 195784703 1250 195783453 195783463
    0x17010b0d24260111160302011d030912010209100f020c03011e15061b02031f05011d0c0f0c10152306161403040312090b07020f06030c0903010e 63
    0xc807182c1c440b2000b10301054040c1c00e940301803028100740c3e0030400c11070185c0010351040d0b50199000b03100000d8000444000410725003200e11841410741d102040d940e02d20b15010312807103402c07034119000314a460b04050118023100c01c2e83c00b072403090029010200600300d0003030080b4010701000074000c000080c203204406c0c090440d92141d038a80300d403912405007000ca07450b0040b1380540d00151184441032020704200d502c880740f0510226050300403143d04201a80340c082000c0043d102c3c0c410042115030420a426440d800c0385500340510b204032a00b88003420070b1010468100e00d10180760b03140d44043d030710441c07460301215007440c0e8485480c056055004094a9100d4800c1e5200d64011814140c02c140c600b03000d03404407101c00c69121804108441031a20f41c2c04000080074421001c49040191004069041d40c225510985d038081414840022066218001101078452105a181002309035000305601c1e82c9030110940c024000013001c6440d210b550030a030380e06040010002d02c48603e0b918401c680342c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 195785953 1250 195784703 195784739
    0xc1511030415020a1d0d05060109020331120e06030702011406041401140d0f0308070e0a24200709060603020903030f0a030f0f0c17010b0d24 62
    0x1100c509084040000c1c004c885200c0c0150384c91440b1844031464080312020f2910441d9441002c240d4450001102030040324020701c408040162285060180314440790b20a0103603180041400294403040640c010304140b00c0c6821102108004007250380640d00d401d121b4481c5135001d4008010400f401d43d05400481c10403100080740c100e10303101e83c010300081e500450b6990300c0425450b8010300070382c0800c10001800d207000400c0309110b50300b5901e800501c1b0041450550001e00b24104110703205030400380b00c254680307081d910241d4040ca4566190503248808180782c000d855210044948984114001ca17071918482c565050b540e0902030403140daa48842c400c1d01911400d2900024550340a8401d9078003100c000313006189010b8042162101e681d201071440340c18180e0380c445261002d04540b04512030002d003280c0008440054400c003a09101c071350345c003104030482c10758014031640d82143e06448a1880400020582c010b40506400540c03802101c03054071440c5808000420a480c2c2c0ca9400740 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 195787203 1250 195785953 195785963
    0xc1205040f060e0c0d02120c09010e010e0112030512040f080a05130902040620280201080a05042319030203030f07020708030a0e010507050706030617070302030d0c15110304 76
    0x403c0e014591010384603203240340e41580c04a02100d0050260030440030000d0800d0b0351070f05450210b412a00000c0b41004280c1100f408078124100500525803400c21150161000e10310303d001a02a944d001007403031082c03208026000143c60049006c000b0303100003009541f603021310b20030703101c0c15015802082c54001120700d05c40c07a5412400000e81511910888003a2401d41d60f40d00300c00f0642288200c100406158040c402e8441d0142140541c0950310140030500c802a441a41d484030a0000400411025101660075071518040c0000101000214241e1a19054400d0300f17415028102900b00480107542240c0004c0300f0190750100341e40071008602c41c68410582d44203e460f0100120380d9120f8a01030711241e544200300c010b40c000e00850101074141014074060340f50800c581e03501030909010340d02840210340c48044c103200e00032260020141002c1c802001f8045070707295800196450103001c0ca071000344440c942c400c000380081211081c8152038248414031028044280010803a801241c5c1611 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 195788453 1250 195787203 195787211
    0xd060f0b040605090f07030e100c05130503031204060c0207090212040215030112084005010e0a03080d0207020d030809120a020c0909010b04060e0f1003030504090c1205040f06 77
    0xf0f010325100e10105d0281d04080240010b0741d4070050b00342e00500d1015070401c1c0c1c1d4404c000440d8004801c6000f03c0c90301c00c00c145c1e20030b6295120144181d07160040d603000244250401c3c000f5216041c401561359a0058200c440464800401d03001a41054040e0300403201075400081c3c03480d010349216a803540a01c0c801e44502e00c6140c10070000d2415030001f0b00410007881c00aa02c89404296400050003985c400c3c2c00b0b00900c0c100310180100307100d60740c0340068250700198a1413078410f5041c082d41000101020308101000d2524500020090205800020302510300803032483c030543c005d54140c03210303c2d030f0160140d284510a170402910180c021500d8040b42c4c800e0340560a0656400701c1620148800b98001b130030342d0700c008030030024101e4000304907050030746d80c82c3c01051941d40c031806207000500c040707403002d007885c2040d402c0c9103005a001010310072240c0b600b010400000341c1c840d041b1030490b03102038400203495015140440d0440b1201c04214a1242404280300501c0f04601c00d44403c98407d4100704 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 195789703 1250 195788453 195788459
    0x3060b091318060515030703020d0318051815060a17090c090f1014060301030f03020a0602030a020901030b0a0605070b151009080c0a030b06060f040906121b030f110d060f0b0406 78
    0xd9502c44023800000d40202c40041b03c4030020740a007003d480c2200c074910080020948034008905c80d40020082310400f0741c212820b0001680c50210080c0140e64251f5490340b5124940c040981400781452940003e1080d074000142000014000c409086000030204903043c00c26000417151507a040d0307070014000201500009515541d481c820400c00000707003010341540c0c6181c860004603403402e9425003d50280c3d80800001036202d100a501c200031441c030061300c41009100060403100c949000d180034040043d014040c10350050140c1d448240d1041095a80f540c84108003000d419507004880c1e0010310b22443c066134150003403002003c1d11004011104191804001c0205c4d80080c0c1c40301810403511030b4003041c25410041d0040809035039141102d0310b05540c13003200e4821a0340300c0d800f01d0012044460f448042110003544054280009141d504960b41180c641d4030395103202030401042e40c4100040b00301d65440e4803a42034090b982080c01000030a0309071400e400600728442c4118800c52401c0e1000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 195790953 1250 195789703 195789709
    0x1812030e0909011806091a100602070605030603060109111c05040b2217070804080c03060106020f070504020a09051309060e0a0b0a0209030102090a0803040303090603060b091318060515 81
    0x42c44111107406844e403c12540c0c0b40d0400030810000c0c1a1912010040500441d00901140c0d83c003412291807400b06036450705030000d040014540010703007008004c200380041590300050a90544600010006074412546c02c055400d104192500308030b40900742d11089100c0f07617640854419405030840c0c4400369552094102c2d179044520031400c2071410640c588002c50495002032a8012804040310300d0541c103601d514041e50856804100c1d00d500001182100707040901c00d280c010852400200744103554100056100c0c0c2040c05540e00480d030204c1c940380414402c4036a28000e0502400d080346c01d12400718558013034034000600361801402e0807240045190001108103d540d0800001419a111341d4501806075011f1201658159000e0240003010794134800150001c2010200843c3d580340b4614001d042654654001f03000d06103460020040d20b154481196020f1204036040314030031401800c454010014007421105071180f440e81c450400082c0d80c403060140101c81c180301c1a0714058020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 195792203 1250 195790953 195790961
    0x5010e01120f0507170102031b121501020705060406122d0f09020907020609060a06030b0106080601020a0501060b09010201110a050a14120a090b07030902010f1812030e090901 77
    0x610103000094094841c00310b490042c2d01030b01248208180d48100759541c54604000b2004020f10259950000522000712281c034040b603000c4800c0d81d0710904082161408110840004000801c400295056809243e20a010100c05880001c0103551225118103004080200b6010301483d4645000c2c84440943c3c40e042164454001034014103200e85480c20101c005000c4580550708500c3d1030f080c0d040c0c016903941103880d00c14000d030b60081c511031605418242c41e10102030003940d031a03850314505101150300b400030541901c03454244400700c2c3d103401c03004070315010300c945018102d035103010f40220340340c10540c0041003d010264000c2c00400d21410491400d4403070350b0182000710350104403800e49240561101da842d0003225a6050504c0e503206948610b6a5084501050b0180c0e603c192300200094144103541040301840c1c00c00200d400b82d030001c2e1801003211410410b000c2c02c40c0d10660503204200008002d0000c1c07140c1030396480321625015003841601e01489100c0c4032800000b4048040c1441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 195793453 1250 195792203 195792209
    0x5060703030504060e160b0c010609020703170f01050607030e01120c0305011a0408060f0414100606080c0c060c0310030507030b06031c0903060f060519090c020f0c06030a14040f0605010e01 83
    0x188289141c7c60030b1710035042640448240c20280d526070200090300800c600c06000d0190280e115584005200c002200c40b0540082503c092800305800600c40c60f2102c4041d81c440170b5050070b000c9641c60040005a83e070304001d40420f05040e08009080c00c005515410060481d900350324a42944000070307082c0803543c001c5000e003141039440100010058040500d45981160080f03444910b84500d081146080945c000c440c0f03030109403250400c209a80e401840e04d54007190300c00106d4100951643c0746521120080d054110440f404000301e400400300300c442400455105048601c025074a1500300c1c3c0509044580d20310034060080700e03460401030205600c12800141e600c0714052415995400c0c01030040c1d4200da40040c0d940e910204090b05c031103943d4400300c5030307404074100003e14014a10041d1101140c03914119004039609440102e0300103109086203504035030082d00c0c2d58035081e4110041c4500090b020001e0034004c140070034803440c165401481c07401901c060000380e0301c90100c82c80403038081c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 195794703 1250 195793453 195793483
    0x20108040b06060c12030f160e132403050c0f030d0f0512010e0a06090b010c020f03030d14070f0804080a0807110f030903010506040b0109031b05060703030504060e 72
    0x190025000035540421a980544001c2200d800d0400d1100000d241001101c0010503110000040c4410560000c041540c46100300d51041c1c42d030f80e1611402002480c0b070684070780c0510000400c1c01403440c03054102c440558410310700c000c0088208481544a400e4510081d2047d0040e00c400c1e40300b90800e61070000b041e060160040c180304071414822903217911104640c0041100600c40030305109802c20717001e070003056950b842d048682040f0180e50100d03803840c1d1008100c02d00d8103250007000c1e43c01c01800381240390100c41e29612200f0150110307095116900002c0d002c149002000e00640c0741d030250a80c01005641e942101078082d0007000c0c0c032202c00940b00a403050700140408144640301c1c8081e264040890300c2d0842c801418407001a01e000c030900384444007a080031808400703900302403040130381c0450200c40034448100c3d90000a1300001813400094079a20704140380c40d00c0100c0b030800d0f48004150181c05195030303020b2803c00900400c010344080700c5031410040c22584204000502c008200822 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 195795953 1250 195794703 195794717
    0x51305060f031602010b030102070b06010f022e0908030c1c0c05090402090103021201080708010f06210206070b0703090b0601030506100e0103090507080a17040b040608040c120c051203070201 84
    0x140c807040300840c1009409404c40d900d40d413040190792801e002404800d88203079050b02e202c6c1803c1c2d002400540005510307004662101034010590486100004004404007210300d40e40154400d0140107002401400303090288000140b14004000c1801007807003020f20410010380160324048413007035074514241c9a001903001d00c80704125140c654018404500141001854220040000e00c1c100000344e01c8001c040c2c03c962010032030040c2c2030041d174844840980b000c001540c00c00c5540b0a4440310010094101c0c050030042c94119104c9608035041103801c100060214940a5001006011105c50840f4203020001c04510154024003406004840c01800859a8280d00340d08075004581001c1c074030304040c0c48031440c0f0089481441410042c00b41000030b4020007060341400003444861020914110204010030000c42900c00181c600382c50607883c0440c5182c4507030500040c130561981110145a280300b1040041101016641003100c0058480004020110b00794544a00075a00e001c0d010502c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 195797203 1250 195795953 195795961
    0x30301030b0a0207060507020105060f0105040540020918010810110d091b0e040213020a031e0b04050901060f0b090301060905041208090c0a030b06011e051305060f03 73
    0x50605a90701191080005003403000a440d071801b69841a01e0000260f5903036800e00525007440d0400c10f11401c0b003030800760310b401d1404010645010258074880800c10b104000c5884201f40c054050b5044c4e00205807120341c41c200c0c900d2110081d4840c50381070b84034038603811500c011003401b031619604984000d8058601440c10003032030700240080020612036090f0420503114008101e01c202da5203140a000e115440d01d003101e604142084050304014800d1f11030500300001030b0b075111503100c01041d001101503102d0041d10340540c0540300501c105a940c160b145204a0003607056480013040f00ca045405120603260340584c1030803640315010701c1000e201203034800c0c0304040d81c003001001c205030041c000194007039603071101d441150310a03601240d20148098407089180d602c080d00503042807461001e00912844100010f109172417070701c0010325140c4c1b00c0000480581c01042ca8401402e04034802d901e80c5480c911005103282d1001164007190401484082074130b080603c29104c88101101360a445c6440f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 195798453 1250 195797203 195797213
    0x6090e16140c07030614042a03230d03110a0c0203030405100e03120a0815010c05070b030901110403121103070602120406180c0e070c05010e070e160203030103 70
    0x3114506500521040001d00311095000c98000c18442d108a0003400704142140740910075a000b5803900744454024605002c089025201d905c0c0c0109444c9050366205056810b40c20000c0c0045c2d030028007614000c071490040c5421001c62406002c8a80c01940d0080b04c603d03c0c25030840c1d8004001442511082c0110040d903030144501410f010b000038100c03070601d540e8400080e10980d46024130070005680c0c1424107041d040402c00120190340301d083c803034142400c65a0003842898010200c01c4d00800301da0074a44164000c891008103640c1000540303c0b43e5498000ca02000e0340305841000c0c0640c87c10140003604030851040c0e905072035102554400c0c0a50014040b2100b000d42c0000c2509030004100000012344644000c10b2281e440724107480741e80c50f107810711500303e94a440b4081400041c240c44100041d5900040d4401c2d216032032442e0000d51925101180d00d8045210000c2c1039602c2d04414113a100b80c00038410301216160815200ca994030390444441c00a4205416070243c0c0c424801400062 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 195799703 1250 195798453 195798481
    0x6030102070b060f0d05030c0a021c032a1e0212010c021203090337080114040905030d0221070519030b061603050702090a0203010f0501080415020a021606090e 70
    0x350004100617405241922500e0656104040e03a01c2c041d44101c64000442c02e1240070202114140c15030300d0060002910007134010382c905e1448103c0400000381c2c0d0766801c1001800900d040384c1026208040c0341d28160411071a4180c004180e02c200b00400c140c0318042c40c14007400c1241d1250744c0c09402d0f00c520341c40382030000d9000581100300d09d02091162003640e0400c008081e088141e224108520780b4161612051040300401c0b0210400c00800014030501818180e400c880280c2a100042c4074079242c01c18504502549410b800251f0000030349a207010a81d1140802c426415090030720507440c0d0540650b4140319440c085041101e42c00440d2a10174025030010108000140002c0d150038400b030003048140d08110411070210314041500c1c019800c01420b09644a030f03c0501c114a15414075404200c519000d118180c10410f1420000d0f04000b034202041c0140d200f40701d0155200c140813000607488895548a9180c4120580350019240d80b01d20000b20841701e0030340040d201c07a10792081c000014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 195800953 1250 195799703 195799729
    0x402042007110d1223090108150409061505090c12180a050a0c080c0a0303020c120c0612040b130c0311061b1e010e070b0a0908010207030c030806030102070b06 70
    0x140d84403003c8008203140e0b08092201c01160341d9005503a50340c50340c00782840e060341c00c24800e486006204140c2c46980240c4d14903000071030074282c10101c80c40400050f0142c43c150b28003d200c0b03418020340c18a00344400f800102039600403207920f021582c801051354464091240903222611128010402e003080305140c02240450060276251800c0c03043e02d90505c2c0448002048400b000f00c6181000761030300c144003c0c400000d003111440071061840c2c400139502c1c00e40b20015441040c21103c0700f046584100428110000301402e20368a0300781b440c001c264440000c44059a1000042d00000c040d800340c149030030f500c240e00000780d8002c00d0640d19124103111105e070105810400801420340d080a241d000403030480d101200400900c249841400003400c0e00000980d050b03070402400c42003413500414040b042d15502050703c0c1d210b0380d02c00811580d40314070354000c003080d520004001d024958044165031020f406915003c0664a41005040c04c03032061500c064445102c4038013051143c0707401c114940c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 195802203 1250 195800953 195800959
    0xf0114091905071a131413020c0c0901120303060506070305160204060e150307060516080307090f08060403021902030a0303050604020f0c0a05060603060f0106050309010603060e0303040204200711 86
    0x1281d0b183c0715400c5014a04e01140e845442021a20706884082e00003194080c0c010740c03c0c051225010000420000c2c1c0d84007000c1d10741c86401040380c181c112400c000c1c0310709400c40140200440d51b540c031079070030b10b800000318160300090814601040c41e061a41c21907200c207038140d4400307142031340c1a0300d0746282c0d07150400120303800f580301c0200064034044468150301840482c0c0350280713032102e000d040615020aa5108806000c810f0105618030202c10400d583c00302c0c1c02010b0140e03a55110901150b2400c03942d007201d40015019500030a0941b40080e80d6442144650220b904403101a100c81000402021000758540e10800c11700000074441c0d000107401000151000d42805e08081503200c4a0b0450303a003100c0640e10400d10b4105108040150b40d8005400b58041e000b141051201541280c0b0140074103c01c0c000c0000120b2405e45095014000441e080395007000300c4034100300c13a1602e82c1d2054805074443c41c189104081c80c0144040111403c0c0d0b1945120ad05e0480c13551b4030001072502c00300c541d680c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 195803453 1250 195802203 195802213
    0x9110a05070f0206040902030907060221031305060405030703120204050f120c1e1f0e1c05010f1e27030507080f0406110601060c0201080a1b020f0114091905 69
    0x1031320b800000d0800317002d6842c0c0150b1a131622a0740c06191100e01d600c15011580581740b880c1d100b070820616100f07070b5010055000e0740d9950780e0700707501110148004018900d1045500708018000048082c003d0140b2994078007604000d10068a8168001c501039142e001701d6158001d921841c007400303c50360034401c0e9000d0703591200d1440001401880b038030840500280803001180c80c9441c10540300001008145140414500c41c110010052100000d40c540a074003000306900020207120324040159074040000c0c4142d0800106010140060308003403180300d600c11a0060091042e8010a141c0d0000b810841c00d007444d070749078a9440c0e501034030783c16070501004000740c4001c500d140004200d61103803604650794541c40e015001308901010b01024455420000040c00310561082074640510740918122030587c07200f0120f000148080320602d0303840121020341e0b800444d004210030704410141e20003088490b03009003074142e01201c00c42d4040e0b519045807040c1c800b16011f0a9501c190203002d40200d031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 195804703 1250 195803453 195803483
    0x4050d061506120c020105010b070b070203041203050a17040215030c04090603080910090f06050306120604030c0201081f0902070503090901060903110d020102150402120d081009110a0507 82
    0x11031074144540082d40014011401000e04100c03901a01c0075140582c0300030090f542c900000d0116a008484005001c0075041000c240001d10030000e4034007400c144811640c4140c0c0520b806020743e070061701120042001c9074844015918007003081d51240f0740180050300d01d81c048441d001e450342e00c01003030040c0000060002240b007814078070855002e54818221305643c2c10680c01003121100c1c40a100368204081140305210b1040c100341e0480869166040294076600d585001400c5500d104804d804c00d4414002004140355012506007440b90007030b00c9040707094a40307020780490040740d1041203400c0c0440b203804000d20b6055a0080c14918004c800340c0342001000d50002c0c81745402a8000000200025400d20502120445034035108200b11011301c0000070980c0040c1d10390600050b02801c03c589070b400a4155250414600054908101602c0e008000000050b0202009440c00340c0c0e070084c1c400d00864a2800cdd03210307040080303c800c0081810040810802c0b18140d014980490b102c4c0b40010060b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 195805953 1250 195804703 195804731
    0x2131512030302030f0a0509070e0403210b090703022a0a140d030506040c0906030216020604090c030b060711060d0608010204060f1d10050c0c12010c02160302010504050d06 76
    0x6050003512a070b501613520306001c0e5940c0e940d0500542564030107446d140c280941b1000c0003401400f00c41140b1001d4130f55650720300b07080e03810303d034a0081058800c18a0089088801c0039038821919840e0442c1c009496894507000ac9080303020f200022256560103543d07400c801c12511016400c03658040d0101d407401242680c0741c49120308904001c400350781c003100500002c5900760180302d0b071215050700c0400200610190080404060341300300d20600d603001900705d030f048850504540c0c500e43c0161003e80d1300c030740c1c03415548020704800c1d9955000a00c2c026100c0003520b010800c884016411406001e24240030408000d102c0e0f21840c44040c5542d501e680000b1180310a00242005200c031742c0315150220762458000d0852000c00c180e86110525039005d04039259211080103d01c54150700e80b07542c07a080c0050109141c070507141345580c0d1040e0000d2446202500c150003520500e001a400d46068200c0c501213110380c0106400004c0c04500e0500c4148501d00f003112a5400850145070b020403161000300c54 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 195807203 1250 195805953 195805979
    0x30b28030218060102060c030f01030b250e0310020c030d1107050a03090f08030a08010e0912030f0106090e040807080d022205040e0f061803040f06090305010c0309021315 75
    0x2c410011003030b100c1044820341e018402c1c140d01900c6641e02c0e03803031450f100182c134140100500006040d0071240010a000342424071400350000b2000090300d00c0c150003044c000d444036480c14051407184c410710200401c244202d00a860801d4101c5d0700440c1003029185c1058090003409212504aa800f40012008104200000c021450280e1542c20362030703080c0640203844081d81c1c1c11550306640100410b401c407a5020303500c0c0b41100d9482c04100010b40b0303000402c9040c0841184285482e000c040148440c0a040071304003412502a500ca05c10700507655610040703100400c40e80908a61400d0003a2004200c03010001c041144a4040051914132603031408812031804e4078400c0c0d4402ca200c1c0043c0601d00b0188500f0301a80300c4c4030010301c0d0507038070041000c1d07039494000d1a0001140c11607050a0324141d041080e2000741c00320603c2c8007503070798076404010540b42251205407000d41c00c02ca2509940e030702034410a00d0b440c1e00502840c14a200b44982900544a0320300c1907c000346400c08006590081041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 195808453 1250 195807203 195807229
    0x120302031303120210050f0a0b03030d02040603151d04032d03020c2a0f1311070c0504330902030106020d091a12040302161202030607030b280302 64
    0x1034948041240303c0c000031315181004034200e6529207001e060003900c550900304203030711141803000814686001d00c00301c0e085000300000c4d940010300216001c1581501900140041d9a0400c0d0040c1c11969800000741038040b18810001801106400b060100c0d2140780c1a0606050070050035818004440c00e1070360744000381030340c0300c0000c1d40468011121072041c8005040a000d0a090703003000e80b240441042a0381d00f01d072580c0d2145800c41469061a101c2c2102030240c030403e001e00304190701c8410201d00c1e0070360101c041200c040f0080c8002140c2443c0501c603040e202010562552220803521100c03411403100702a201041c0c1c0b610b6400000d00702e08500045002e040698080c180c081444000545003500c242c0120103070a6100000810011101003a1182c019003d03060803065107940c18181e0600c48002c101d000031400d004c002181d030081c2c940c542c414181c030036800c80e1141d07550350750210102e511400d0030382e52100d08a09001144120300e801c9459a82d1f11522000d0100d0703032a4005003103503141013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 195809703 1250 195808453 195808463
    0x1060302061b0d030504051b0d0b0f0f070305150906120604030909110301080307031407120c210f0e03012301080601050d08070f170c07090c09030c120302031303 71
    0x1031610b101001040c0040c600d844194141886103041941d00c0a03107a91000c0b03100402d410450007190a60354803507a100e1401c81c0c01c6400c00c001410510308440c003001040740c0200c000c940f54004075048d03920031b00c9a18801e00c0c5e60751300302c4882c24010080050300b10b001f41400f64400201c2003186910340e070a010250145100f0303100d0854040c81d10380c10300140c8a00d001e81c0c043e07811042c03004000c048000320840300034560509d01002582c419642d1b48441d8040c140c1c000c2c24003d890640702029641190310803030040d001b01c0c0d11001a058180846c5200c2c41c0c0b18000c1c5001400c3c0d00c007020001e41c02080107642c1004020000b1038401c2d200160100914031002005448401020041240c0c0b40248200d42c050001503d00d282d011807070340ca842c240b03403054800c02810407a112082c5002d01840780c01c0a041150359514203640da502d00914039581d5615401015021440c2c02c100440490244030a00103c2e03074440c5130100068601039042810391228407042d4198002045440d82c0c407284c4107139101c09076201d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 195810953 1250 195809703 195809737
    0x1140108160b04050603040f0b07020c0108100302180703110c0a1103010606020303011e0e01090207141f0f02090603091b0d020f04200316080f070c030f020106030206 73
    0xc2a205807501012022002a40c00c40351401e0090504102c2180c042d0b400c02c2d0380c81c60b03494803581303408000e0841410303000d4403814800382805000e81e40030685d00c4240800342e842c05400d85a2250801d2007010394400250701c54541f18a14070040242d500c0d6a500c141c0b14240003030f2100d404000e85e8040c3e80003800300082ca400000a81081141c0d0f07403144c45141c24141c00810029090030806580e03440706004146c5080c02240540c00c5496031380070322001400e14403400404d1035079160b59140194200801c11540021200a01c55161000080c8041d1200900780d04140c1042034110301002070103a5819080019003c000820041c2c40e448000c6000751044030042003054264451021070219100c0000d04ca0b1511405140240e60360800d03400040da0304442c0001c0c9800f2100803c000c060001c204591689001710402024517601d9503c8100301074036440c0c181c000c0d500e0030100310360348004980c45008148680d1509011030704c10401245400498000000c3c1c07a074403034000a083e5080f000c0c0b140c04100f80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 195812203 1250 195810953 195810959
    0x403030f0c17090708070e090f10020703030b0d0206030106050d02130e04050d050a0c03050a0c02090c09100203040b070f0c031a041101050a0e0f03070e16090503160504150503011401 80
    0x114208541d0103c00400038214440c100310140b0381311085881401102030505001c0741003044203001d29010100180c040702c12108001c0b24200180d045104150042490602c8034034103810501c0244046543c000d03e4249960300b880c40584d41900956070b01400c003607003807000003e4644040c02160142214484522092500d85000352510100354622820000c1c248603035030820360005002c0044a5150403c6901c550742120112500604000301950110000050086160207200184644001a50071b420094803c2e14180c0c0c0d6481248038040301c6950400130907011036480c102c0c0400c820321510701d0421460350303501c520765500760340c0804c1120501c61078107000c00c01007480e10f44102030a007820072609207103c03000080c00240749606218021144070b10b948050355810300009001e008200017509180c2010708400301d1100d16031042102003040c100340030400c1d160000300b00701c5000d955480c0480c40c41c02d0009000180c541e4400e01d1000d10310142c00807895a400380107400000c01d02c111216882d40c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 195813453 1250 195812203 195812237
    0x3021c060306110a0e10171003060c0c020d150209060d0b1801270608010e070e1f15020712050615060a0c061a04091406220b0403030f0c 60
    0xf018007541c1c0381e10820401c5540498015900400f003881c102c4103d2105140d04070256410a01443d0700d40a0307140040400c100075001e0428201503a0250b50304005074410036000750b4a42041300c0001c6c0d40114103034006400924840400c0d44540500c100140c02c02e25004041200c03a00188020b411698698840800714200b07100744001600444880d040315525040300f9040d112004102c0107c450038841042260b501d460300b25070000c0580764000c12800b0944005207458854a0191022803a105004a680c5001d00e40502c040944c508040b000500e140c0301440f010040103042d000194000ca0748000348a458146400c045280540081d00461511400c0e0801440a61070fa0501c6204180000070020343d2207480f002500b50710082c00990b01104181c600c05000099034429403080c1072008020030400c20740407a09140300d40d481200c040740c4844140003142010454401d84603e05a4080b1010030741410f042900f25010741400901410840c8500050351200b80011001c22414541031002d64 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 195814703 1250 195813453 195813461
    0x1c060504121209080a08061f0c0c09060f05010c05010b0604060509040e060f0c07020a030212010e1902030c04110d0f0b10140415092c070e0f090703021c060306 70
    0x1600b1850200018821961070380c0050050000b9881001444000601161190032401c00c3c2280d0440b10306141c107183c408002c0000306424000c03078006001c01d0001801702003502505064070440d0002800c034a081100456548034410f5064a56640303400c0034803169128040180054007103560798594549640b4244800d680000000341c02d180d01a03001c100e40c03a0300880c100c6800030750040ca80c80c0e0792001800000c004030015000654080202c3d00c040b40c0e415015130042e000c41c0e1558080d10301d8142c15107030140ca501420f0201079003640040d440703401f0f07620b4158480001244000381882c1000b04810811040701c1d412800c810780c0316500c0b6901106803410f40a541c4400513a4074040b4950002807240302514041c6201d4043c0d058203c18080c00118092a0442e0207000900d998002070b40106042201201002440500a00061003c40c100500c5802d5458401802a003050356030103120302400501540100034030101542401041a0411407441021002c0002c12020541604504140080b1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 195815953 1250 195814703 195814727
    0xf0f0409050a060b090a03020139030215040308010603111210180204140f2403010303032003270a060f0b04090c12080f0d090b06100504051c06050412 66
    0x3002d000d020700b41142d40c8080c1c082c825070b48d0a02c0c0210340009840d141d03c01c443c80c410444604102401c0201030310600010b140c0021a020740e00b228180c518a400700030051a080e5405000a0314010050109078080d4005070091110f0b546827501d072041020303d044800c2415565090004544403007001014100d4118040380720b5034102c114507043ca040692052000e510100324040c940e40d0b01030915030f03170342c506200070600c00c141c041103001d6030302010750711952303209000490200b46000749400b412810607101080071a402c0c114145107880e40644540610790f06c0600b41c81c5244602e0031947c3d03004061049200c3d040c131580f00818000154201c083c1074030000715078030b03000e20b2510364071601182c60b801170070046403000200d14186103c0ca00b0888a2032050b02115198a640013072022001b400d0355002c0c5071f03128044e000a14103a120141004520034800340017030001102848240481d207031083c020441a0000c9802c0318a2103010381d955029114225425151b0b140c0000141c84900e030000003440078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 195817203 1250 195815953 195815969
    0x20d08070516020f03010f11030406110306060d02091f0201020703021009020604151b111e060315060c0f07080d02070503280c170c0f090c0f0f0409050a06 68
    0x51030b4020754036000504a00402a100d11516004000640c4080d4003500070040510300038080f00000c285070710381a07802500c00f03c60007450002214002d00c401003d41e030054800a00c0c9500d00034004050601a40000c0c0d02907902856412949820300700e8205428a0485150000360300c0710a1420042d0505055418120205041c4401800180d031001c003103d0a4410114001407002c9100724100d508958202401c07081c4122000540188820201c1c00001c03050100c2d40070480d50148c0408034141d00b064144990000014000314812907410f0004502c5140060082c80c02c0c040e40b80d080500d0281d441200440d10380100400b808540c034140f1900e00110104c3c0001e2910603c1c2c5000b03e51740d0102e41106990000116403000d600070424015041095040202d00580d140c0b91b941e540c3da14400001008841d201d18084100181009450881c401c68002c040303d2a41d40c8441d40c50b04940c0c0000f0a16070140310400c0341549001410010380b001e05030501000a562404500d00c2c0f04482081d0481c0700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 195818453 1250 195817203 195817207
    0x105070f020f03040e330a0503011505211002030a06050d1a060607021230090609010c08040303020f07090603051b1504090f0b06030408190915020d080705 68
    0x1907800b00000484081380d402c0c0f4012529075030380d00b01c5003451180014111040300569215090f020343c40c5a0f0b20341c40c18104403110000b20341e40d2010182250140c1c5844c50500d811140100036a1400301c01201c1400d00b85030401d0303031075040210340c1c50501181c0088103008d0f550100500032800b005102c2c90300540b0f81620901c3d000b91654032044800b140003c0d41690440282d070020781c0640300c0c1d400340c464441d8040d26510701e003035160f00295110387c02d86100e15011341c0d40703100134000030074065400b806480d1070040c403902c0c01c80e174441032190039440817288a06118a0081c0d41c0b000414080080000703501a60181002032982c81845040500d41e61141491030f0911006001099002c00c140d04c906120794010141c2c4e0b0104004034501300d000f85162291000040b0300002d01000980040382242c00e903071710420021500034100403e0b400161005044008184465a42d03d000804103102c0d07001c080c241020b0300341d552006845001c00181c00400180c02841d060f00040d60070003051a009105410054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 195819703 1250 195818453 195818473
    0x3060e0c0c030d021e07030c03020115230612011503060605070308070305040f2001320318010204030c060f02070e060d0c03052b050f0328050103050105070f02 70
    0x7503901c1c003928000c1525030b980026440c2040400014070b1810f250504c1e00c00340c60700d4950130042c009080070501038000d0750800120190342c610529600701691490100035611903070700c071801e500503c0380184103074200d00100314011844031851180c60007040c83d000a00061219140018140c43c0654040343c10300c00c0074000000000e4010003c0340d80f0204034900002c040d65a803c240500d034083d40c41c060020410324a0040c414501c0040003c0f2244081e2158005480e03104652011f1a2003002c5000c550304d04c841c0c20109c030312030510055400034900a0352146403400042c1140c00c81e072140d030046403d050f01c0701c02000030540060018440800c240040c10910b49840407510380990000d240034402d11003415094100b1a0042a02000c0c1d80c01804403450412644103404124102d40c0d100307040c0d64007185040400310f00c1103041b12580e51180354150b00755100e100110a080070341c207541801080c202440c0b010800700d00d03c1200d0007180a00004900f6003804030380a42100f06800a074400c43d00a400b41d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 195820953 1250 195819703 195819727
    0x13090c0f05060d23090d090b16061e0212070311090d02040c02030f04091d0706120b0406051909150308030412020304050d0c0807091e0f1b03060e0c 65
    0x348003001d0700c0f1640810850021022012200d900078851044002c9044c04d001050500050100241190743c03140050580c03952019015070140341d5594044485440c483d00005040d9001a030300341d11404800802c1510325a0300c402640c00000500d0103c1000f003042100b15541409030b560724140b00381150340b402d0300d00070100e001c41d00c1e2260044d0055454403074001050f4404c000b1210721086074080542c565071121088000390210459a07021003000007031402e41b00d0f901041c01c0342212200d85403030312a41800360f1080054a030f40044164400d590f208002081d4880019594000f410486001c0b1501c0c1004951821034001014005c81007812801c2400058503400c01c980c0c0041e04141003400d2045022005c91540c0b1a43c1c000d960010082d103078034010062524080380c1a6544030007500d0354140c4a40d90101210000035140c101c07040560310440c149001035001081c000903080c0d01103a4280140c40c18842d10482214000000b41d540d0340800ca415a8658003581004100d0181d500c1c14443d8404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 195822203 1250 195820953 195820957
    0x30706020127020609150d15050a170a1407030f0302030901080703060f180209040c09080c10090b0901090f06020706170c0702010513150302123405040513090c0f0506 73
    0x1015004082c880c0c0c0700c90f1681c091b001500e000080c00d450501410540441141100381284102030150600da0000b007040f00e002d10010464840303040003027011015076100c59112101c040c1190301140038200011010481401e8450a4680a80c00075079641030031000043c000e5a005000d03404040c07412105010b100401d0301100100c030043d90300e0440c0c0c3e089032400700c0002c0c4950350000794003c0c0362143d84000c094022140c1000c0360400c009850780002c040080c403003003500307103c001c0c80050411801402101c1c5554058440c3c01c3e03040c54045406503c1c1c8000b1080c0a286403c00d030003591180b44101318031513011844d0414001da160018040c0c0c104061108041d009221000341889070102d000030010b890009840000c10320214a0307101c0280015024009500828401005140200005007085015a50a0109501210198055084240c41c20441e0451803461410000100400511076940003094821600c0044001038158202c0c5000001240d90754404905400c15490030092aa92941 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 195823453 1250 195822203 195822217
    0x9070e0901090b01051c1b050c03040e0705071505160504030c0605070510020403080306010806180114030c030a120314010b07021c0501020a031505040e0606040216020307060201270206 81
    0xc01080f40110100140d03664041d4015446035805140203c00803c5d04542101b54422400c0d003d0355141c06419804030b502d40305255001d0101d81c0100410020402d0030415a0303440b81a034546581808159552254002150304440c82e00940310424000c8010b400040c2c0b0b0803503601401c2c04c40c41d107072540d510360707552854510511040c4040840c481c400d100c81400603c4100147d03d00441d0b5440e124030700003046400130f4840c54001174218002a0a40c24440701916010f9008038641c0d40307ea00e444803c0404085100320141c0502404007100b81c4c0303450030000140d940740300d1503400110101d0560010300b2901a04006100100340300700400c4940c00e000b0445828903015150540480300b030600107240c0710300d810302c002e2a41d03100240c08408964981c0c00300038008120415031141700e50b00d00404c41514a0040c83c49a103400c00d83c01f0601c545000c0e4007c042c0103040c21080451026030382c000134108503040e0b02c2030380981d44a49610800d0010247c8414071201c120703040550302007054011a5150203460 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 195824703 1250 195823453 195823469
    0x60909040611070f121803050606190504090305040806090105010e1b070c0902180306012615070c051606120e0f01110405010207081506060307050f0d020909070e0901 73
    0x25070241c00440801d41190591078004c3e5000c2e44581c003501d40000f042d54106402c000003290302540710385500d0380c3c60986c012030380c0000c01410207485100c2001301007440c1040d0b1034400c9110000010315600c540c0180308000e4000d448840e152450190b495013014030043c810307000d0b64540b90041c014290300040e1250800c1c10310a4146491520040002c290302c210800a442c00c1c20a82c000070b5003180c150028611151809102c00d0791440200900d6034840c800c0c02201c0c1c50319031201c84030003001180e050701648082454125081400c0481d44440c0740e0000b42d640e580040c0003040c0e03200900404000b84e12114542e1415075030441e05d4035400520382002409151100c0351691041409840100405910f07100c0c048000c008188215102d0003080e03125200366805406951030028440c58041103405aa07444100144200e64900040000300da000400c841e0501000340700009903905001d0191603140c036003003030059032143c011080042c2244001c5c03079101041110703580070145490701c2c5101c0d8115903020b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 195825953 1250 195824703 195824711
    0x1305060f0717100501260c0c12040f030b09070308310609170606150a0c0503040603060e01050933030f030307031104150503060a0b07050a0c050609090406 68
    0x1086007100c030305200100e00820981500d09200805010080f188200c41c026210680d1440c203044104165140360304c041c1b1240e9206800181007040b80c200240008014141071300e10314901e43e8685010b42d00190008020a19034110500030803170500b00c101d41012482c0300801c03545e499991101044d10942901c0c40c80c0d801070790709503248510f1510143d1301c0340000420808803940c9800c0700a0078120385100310408580e1200407c002003202190280c024031000c0c2800703100302c4940c80300c107036681e200c5c44144040084c1d110190010070000c0c07000c0e0015120a84e03000c502c02c3e15000b8402440101a0443c1e0304c44d16444c004d101410010701550392004582580b80d24a030500d400d0a00d10041d0900c441682600540c606c2d0f124807940032000710720440603502c0404c10000c010544a595008038000c0920004244c4040c0981c40e010300701869210320700814603401c80362200b40d00984c1d43c00200d0126003560011070010200446851401c024202c10f841444c14010210001001190081c1029041e0355031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 195827203 1250 195825953 195825961
    0x3120106140c060414060a06060c17070b0a0501030218070c0201031d030a0c0203010c020601080a2004090302010b0a0b0a0e04020c0c120304030302160f06050c010e0f030706051305060f 81
    0x41c0809a480d1910b00200b518200d15040c01d050400349401e511140e000d0042200141009007035100e040203485030350b81c808036240050f82d03070009036044410084802000a02c81040082e031544007a51003040f6881f8042055499803041c060720070722400c0b1412000c50103034208804658408440840660240303008655207034060b6101801090400c0742030480c0c0800221a503441c0c4c1c022055040c6107100303030020424100c003050101e80701c0700203000b9890320703800444420000ca440300c00d508032015064480d1030141d018620000c1d0895130852021001741c2d44880300301c05c084c900030f40030900900d11003200c0e91034043c031282e0081001042c0444c8074452940030a401800c08010804140140009414030b54400c00c3c0712202503a0b50440d2200b20300521512007942081030000110304e0450b0710780b40c010600765081410035180740e00a915540e42c0c80d96190008d0398134480800c2508651040980607541e0f400f10303414100c05407900103041c400e49540c989580c0d00050b100080250b4459542ea8000034641c403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 195828453 1250 195827203 195827237
    0x1e02010507050f0912011a0117040201020601030f0602090301182001020d0c050c0603011205100e03031306182d02060f1c0e010213080a030e0f01050d0207051005060303120106 77
    0x820428200c1056103840c0d9030419280010101d52007d5400742c990308842c0c130760b4844540b4200800ca80082c0160000320040000421003d40000705500c04d250160804080b480070a007140c8001d080314a140f1440c44181e07013403000510310001281c6050810712150b0507200e0010b9600d01402d0075000400445c907282605120042c0300c001e124900091841da540c0d42d507640345500010b03076690305403054052102c0d000103c410030700c43d0301c0710007030001d01441c115503c5000a2a0741010440c080d01c0c0c1d2030301e5012241c4d09064120340c10902e00d11a50041c0d03010780321500500124944a4000400070031494880009a076882068901200546030b08a90b2003400b03242803d200920360041031380d101c0c1004014819658190080d0521480041c428140d059580100d42c3ea10b0700c0c2ca610250104241e04072020060034208110910594103040041c0760100c419441000c81c0c0c8600d800381c840c2e0300b2414220307070029040d000e80c603041a0220300450038a503d10001c3c800d00901071092200303000710b451074880c07040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 195829703 1250 195828453 195828469
    0x308040b09030c010f050103021c030e0f06041d0403020f0705030303010306020304050312010603020d1b0c30050310060206010602030406030e010605151e04080d03051f061e02010507050f09 83
    0x14031060024841c5104405c4200701506007070204078410411000c4510200d0543c5c000e402503d80c141e40ca10304100303110402d0001003140c410946400030000c000c0898181e0121402404900c0e51000c100b01d1868281802400c04c2c001b0b8001000035082040304000d03c0d580041a03d054903000407005030b80b80c030b0780c1c81c1c424038510402c035200021070100400007a00c2130b00340e03000c0c011091540c03805010302006801001c2880c2801d803c600e020a04070184913000c5403400d44a481c0b42401c82c15504c50506000b201240c0c03082a480318480019000801c1003a4a90503080c44c000410040c001800c80e941080d01c040d449000d640030b0141050303611951240d10365030075005000101405008948628440305401c04030398403200c0c45513100000c0240b4030080a21740412a400c881d401c0d07000d090341303035100e80d401c4000c0c00000c2c110301c200d2414140c82040728804010400020703c170503102c1001c41541c09560154407690b106020040d640341908100501da00f1008035414040f0502d03a840c1d9030389a00001480c1e03c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 195830953 1250 195829703 195829717
    0x4050a050906061905030103030207090b0603070507020a0305030d06080730050a02090709060807080606040b0a02010902150403020108010905150f030f010507020f07050319020402090d080f0703031103040308040b0903 95
    0x702a120520b8113850307030054000c6060f01c0c0a07070b090b0b592060b120405401a08c101c1c1500c1c03608000c041000840040c0b00d100600308040c0f0041c4420342c1150f49468061454000181c06803034075660741010800742c101040714400600a42000b08110310310035a039423005204000c048900c0d00d950746400010800f00f440f8903040c1c139600070043c004c1410000d10040c00c01403d030280e140418801030100d6001409508070901ca4400207000e2850541810440402034101805890940d07482d01c4441c0016a5203034520003e25120012060301c480c81c0d0b000040803240183d00860301c0c549005c05002e80702c85800312400c0081d8055407085003526070800442d190220001141409510f0301060040c92580441c3c0c2d0204c0302c1c081d80441c2c04a503102c004040e110400076030740c06030151001081e2001420300350050880d28800074902000f18079961503d800980c001d00b643c0807644800035010302019010b1150082207440350000754107510702035901400b01c1170094006094000c000317002030030303c1004204807429 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 195832203 1250 195830953 195830977
    0x4021302040608061201140c0a1103040801020a030506090c030402040903111b03070605130e0711071403120c0c040b15071109161202070312110a03050c04050a05090606 74
    0x160356514034004003d40d03010380b0070358495003500c441d04d900c05205015600c08041940110038554544034840b40181c1e210310040c03000d00c0340d95400d13500b01e20340610207040140074141c00540e403004411070080c100c4a000309114480c05c00b540c01d01c03941a0415042c0c907071040e815540011119164141030751140310300d0300c81a03050312030f400e9443c54602049030120b224480540441d2070b01034403004181c4543c01148a03230002000c41000c104100c92004440c07a4110106090024809118041c4241000b07056044491413055044484e8014142008075400300108200150305152107444001e1310f9501070501c0d644920388442c03400e074207580c6110090001401c4034401d0381c1d0318045898946807034400054524492240d10000ac0d40e100361000003030050322580c0e134070280c0012510301054000d4010a40550802c2040c07010009420214440c0355221010040c0a50f1160403400000b416500014901c50070f09400b40001c005075110a10700c0c1e01510001c42d200d08081e0380c2c5501103400707809100b000700ca03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 195833453 1250 195832203 195832207
    0xb2704090b07030e060603010515010c06090210050a090803190806013014070e0108041106031005100914101103070f15060f030209070c060e010f0c1803020904021302 73
    0xb04142c0c055200b1030054982c81c059030a1a550350007054201da01c2103c502095641c000b003080340341e41c8035484003100f450ac2208000b9400c885600810a201400194440807443c00140900050b8015031088010003003040110b1070209204130840c0d0110308641c0c84e005005c0c2d80004244168010400701484030301c00c5603840b82106209100941c02e1400b0424091603030316010300d5111010303081c0b074114460f8542d074698840340100c1c00300460300720780020300546148500c002e00000c55560500214055100b0b8520510742c1c41c00c1c18100900142540250014448811000c02515124581c585000c800488080611044d81c20043ea0800b000800d401c240d03000c00a00001005040d00c000f484617801010b0203041c044070300100c1c0b412607545004854000a034a4406c100501d0100748080d489480e40c42d01c2041c141c0180c1e101010303603a22145400c02a5111468455842c48500c03444402161610701040000406510181140e015020190007080d607800010300f1340d220b442e04021510003981c2d00315 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 195834703 1250 195833453 195833461
    0x10c02010606030b030c1c082104020f3003040302030307050106030b0f100e0403030e0d020c030607030c0512060316060c1a07020309010f020f01091b0b2704090b 71
    0x240204042d00584000ca442d000800c2414100003600700d6a800004c0e01030018541180e80c0c5980e03900c40e00008880c4280c042114901d1803400320505031005009030003480c040d00b4980304000d0f070400c10f1400c1c64052401c00208101c03a44208004000117002c84024038035401440446c10304502c17031600040c1d01440006461801c0140543c080c0b01200c0c02420320102c0303070701e404020b00d040d4002600ca0000c0000100da00340290300404082940082c4a8100007500030b6040c6410b904001064811a0141c1c2001002d44c2c401d04040c0300d01640103c441c035003000f241c070308044080c1c02c0f0300071a42c0207207070b00f1803030400581d80ea14100000d104000044a0a80841c2d0740d8201c000c00f5481d40807001c4481140d2204100143c2c840c229501c0c0c001c1c09160055800c0800201c0112035180811541e601140f03c0d880421075682000c0c031411102d58026002c006442d6240940c03014003400d25031000c05840020041948401c0844d12f068202c0815903002c02040740801d0001005040c1c1888040c0080c80c01e10284 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 195835953 1250 195834703 195834707
    0x50d050612151509060d140309090c0306010f05094c18120b10090f0f0b0a060f0f03090b070c02030c010e060d020c011503060923030d09060e010c 64
    0x740c1c2c4a480f08018100044042c2001e01c01c107100150782c0030b5000b200035503440001458001c002c010329826001103a05040c84080040c1003c0003d0390383e540154400410310007196031129112407000100d00303102c1e28060010700402d441e00810000212445480040c1e00d0010801021120480b1191640c0b00841ea07641e03100700c1e00c9019070240040c042100c0015a00c40c4480380d840c050f0803a80aa034548103d9585519900c800d800c0040104c036540c2d05070b000104a008141c400c46481100109001030310400041c0c600e0222144d220606116400e10001084413540c4469480c65102062801503c0501c0c8a4000d402903d241c0c03900030024001c150403c4030700380d440491860214003c804648a21900f2001914640c8018072015000f4800300114040982c0c1c2d134008090481d0300d00300005003643c410303169800c07044090304102d40c13203501c0360400070500420069120a51103011441c016600c08021740513a40c1c4611640b680f240e9032211a140180220f40d8404080012244020300c9910320002c80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 195837203 1250 195835953 195835993
    0x4061503061502070815070c05160f0e010e010501030c0c050f0d1b0c0501110a0b04081206030f0703021c060c09090507020c22150306020310090c050d050612 69
    0x810b80c041031050494034a691001540300c0c100d401d0140500840154204e480714034610040140c01403003a403064803000100100b091141391000ca48040400d1030800000e285103501c20b0384001c01d40203400c80184011808101041c2c11a40242400568280d0b8a00123403014424080040c1090080031030003403148401045801000c6081d684411441503a403542c004d4901c05100050040000080c00b401103502450364030b507a803549503089030342a08543d03603a042a104102e0341195061710228008070b005050210841d0058811030151130929400e82d14103079214514440130384981e8817035049c444419107200800354113a0b00701a05002a20244002030b040007109e01ca8050964541000110402d202007140c002c0d40c000102440c4031200410007101c00e84d18075000c81c1c1065541e9205008410800138074800080d40705030000368807032425185821f103841c103c1e4000000316041000c0d1450280c1c0c0582110403e40e1488070005135034541c0300106d03100108070900058a4800c4652503980700701c0200fa = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 195838453 1250 195837203 195837209
    0x2030402010e09070f030903050910031a0607080a1b0b160216080c0114191d1c03081e0a0b0306010909080415171503010b030a150b0406150306 63
    0x31690810341d200c10a001c42d5100464004c00003554001c03514504034820740094645500902e800e605000111000810711050301010501003a900d0040d034000d051102c1002002c5142203a40d142042441c0c0c40c3ca50b9180300d59070088041003c0c0d07008041503640d909076021480d50f00018041494030b007400012007181c043d070307540201501c03a11529503181c0e081414400c0613a150031014288502c9504d0040d200b0070b400282100e901402802400480070403102c02d42030b8420f540d518142042405510800341d582d80140c0c1a00401001d40702c6c900317540c0019100700d0169850318110b038880d90f80031140380201050b000e641c500340365080c091080c5905990410b0000b50720442c10780c0c200c2c1c0d036a44189400c40e110b5030402013030f20350140405c005000000208010902d118241180b0074104100d000c240032004940c0440180182211004607080910408400c0312040d001800310000ba9100c00300032410510700f03890032548030f45807812182c88a03040000140701d984590710200d20311450143c06440540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 195839703 1250 195838453 195838457
    0xf070b060904050d0309060e0105040b010f0603270501020d06080102030132191a07170a0804060b01050c01020304202220070c0e0106030218042d0203040201 69
    0x2501092591070001e5006001e40d41c4a0000c081c43c1e00102c0c1d0079005072680400541e4003c0e03985d90001d000020030f020302031042e40315920f030480701c2d8107161000d8252441c0380c00040400d49402580c101c040444034001c1c0e04603402c480d0071580e4445030b10b4014003901c62000c6a1505a042000010b035000d015000355050316030001c103c02c1c0780000304050204a05070a0443d2801c024000807140c01801c220600d16000c004803814410030b141c403500d0810301071061004008040d00001040c90074003202c8000c080000c0c0740400500d02e0101d06581c002c099040180c40038200c00e039601d11890381e903030044013102c0e001d502c0714000795280e162609156820030040d010314440440e28012404c66441c22180c4200d104a440842d01c00740020388070a04020306a5200d600310f46004076603598480623001c0c01420b440f074030904c15101d0003403d003119a90391600c1031388008103050041c17003000384506c0e130802c562940c0c0340c06036000200c2c41a94584a003900152161482c0110107e400c000c2036030f54560000d5100c0c41c001e0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 195840953 1250 195839703 195839723
    0x10e15270301020c070306050402150708180d0506060919061205190b01120501180503090307090507170408090a06051801230c07090507020a1103030403050303010b0a140f07 76
    0x40d00740740c00d0344660f41c0e0b040240d070005d0005100040441c0c1c020350b00140040d01041503003003c07148400050380310300415641140c01040035240c281080380c0e003aa030120296869640350341d950341c0c0e06035201c030054400c0d8807075204080054080c0c0c81c04210500800100c600c1885640d075101c1c1040008900b44806907224000d80d0180f070400442c8601c12200264402d0060b034242e0310700131428560448018003126555280c0c0e509481110181e059959214000d41c060b40c1d40c2e0b111081094a40180740e0321529000d420142008107868000d00c80d0004044001814052a5100d103080f140324400c030010f007544440c20b0310010403001e42c0413014015141121181a1844100d900155a105403008800c40f4071440c6c1013030a00860380d0040035002c03004501080356401c03511041d03070300281c5004461080050744811041d01c2805414280714005d003c0680145103424290707101c071a02e03840140120303228007078006145400c1c68803640b151100d140303a20000396101c070240b0100d50003c0e4400d500036110302c104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 195842203 1250 195840953 195841027
    0x1605030a0e01021002071e0606081b041a030d181517010e281e021305061905090312040602010f0f02131a1c0905072102010e15 56
    0x413030b1085900c85d64102c0c4060301c105564a20500074000114400c4071079945401c40000c80e240d0800c0790100c88aa050311640080f03445905120440710401c1071030030b01b000740c09500480c0f514003142118425140385070041490108003203485600d20558002d076a40142040d40b0032034a5841400483d08d11194003c000290344e0340c841c44400442d080d40d0704c4034241c8041c18500c00007100c0c0504185004084c038004600601003821601c40030a007140300d002240d800081e0f840c03507024100b0b29035010b040c3c220350090401314880e040743c50112402000a0a200c80010742c00c0b015034041003100038845100c01410360340c0e078a070000240a0002143d1141595080c101e22840800c3c1034026160340c0d200c0602070301e60003407908002c090380c000211400c01c00c3c25070402095031036000140d0980c0c80315540c140d0115212260f45482c07841c007140e6500c42400103088000c1da031458040200425002502407030404c2500e41c00e0000102d40644200e21080402c40011740c80401045c2039051260305620300e010021304010f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 195843453 1250 195842203 195842233
    0x306090a030822200109050d0302071715180c0103090f02090408090a08010e10020f040308030910050a0903030c020303132d032705060901051605030a0e0102 69
    0x10558004001c240e100000503072040141c1c08255141152200c01010103c468aa42d154031200c403d03039410081d54034080702c019580000000c0001c00c01554460280141c545001752070f088603006541d0303001800b030003600820400300000c1c4500200710884008a040401c0e080c0307000c010b078610006040c001e0045a030021340c060300c205a0a60f802003e01000d0b030700c03107a003044070031240140119502e110a102c0000b1a8846082080141920300000994010b01451842c50408441c89419401d4010880c80b03007420005002d94007100c9e84400c8058407600c2d01c400e020b0404107400c80c8000c00d01c0c031341002c00003000350580010011501a4600300f010320b181c3e0f80308984070310088908103c0421490325010008220000b01d400508030008182505502034044001c0c480e0030741000d400241c20040107103103134043c1d80c00d41103410303825540110f81249884085045805620409030500101040c8102c0c840d0707a03c2c00221505501c0300c240ca076a040810000b42032981d45044607401482650784184c8801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 195844703 1250 195843453 195843463
    0x120605090403050702120a051b03150114060a2c0906010807020d05070302120a080106020709021c05040f0c08030a0207082a011205010603060e0a091a0a11040b09030609 74
    0x60b0180d030703014900070742d07a0284015080e005106150504c07422101c41d01081e4148544c00c51041e0480c58a031180c00c014041510340760100c0c01c2e4103044c03101c000c0100540c64034040c0c070880001003500d5031030315400180000c1d0340320314041d5001250b204e0b80b140c0c801403912a030103425440e000221145904c40e00c2d00f03001151441812100440940e004d403d190303580b0382c0600058a0090720078412200ca110300451b10041c2a0041d0051070f0209090000620200e501488000064104c0d00004c42c208900500103444d1628001c0100d0030f01503a81010405100c80241004c40141c0c004c004070550300e40e40c09406680e940500001c1d001400ba0301400b06454602140c40e02c017100503442c43c900000d00c048120020351038618441c505001c400d140309120104603028035030081c2250b40300022514644003680314207440003030841001901c3c020304007001079040003540501380c0c1c070454054002c1e5910401c250040243c07036050048802c0c0800c0008041031f410340100803c0c6015000c1d1103440e154000382640c1c40e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 195845953 1250 195844703 195844711
    0xa0e0a1208090a14030306091e070807030605061809160905130b12061501080708070305150d060906110903060f0603030d0903020a02010e01050a0203040608040204110a12060509 78
    0xc03810a05800603158400e450058020071a072090703812801596403100b54403402d064071220307190070101c2001380e00c0c81c10898070b42d40592404084615103008070448081444002d280000b4040f48501142c00c941c0f003540700101070705010708100e59030101883d01d12207646100c003056208950100000b801c891500c01c4000080d0a00e0b111009070034248001c00110101d01d0b2343caa411281e6414203806070781d90781d0382000c1002c00701401901c22403d004405501e420342c00008607040c8010380c0284030300c2c80e500c40c1c0e00c40da0090301c504c2c001a50f5101c2600203502e074a06111282d500c0034086e250300082c07117041d0b8095000070f4400c86003048809240e40150609010703102c107482d89a000388000a010700d2420518590080c0000c003940e290125000c982d1046445151040d00140d12545c414000c40d6004180e0440000d000d0800c0c5091055030701c402547c074071440c007442e010046240e01040c21912540c01c141d030b9410100700d0070398131005c20000041504007041c0ea000744e110305000300014142444100580070f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 195847203 1250 195845953 195845963
    0x50c1e0105090f0d0b04151a091f0b0d0c0207090902010e0d051603111003050903090d0201021009081207030b0109050904140601170c011d0f0109090e060a0e0a 70
    0x800030b140342040400c07660051032507001541c03150340100280241009a00c03440c41004100c0d042d451507864501100c010058000340000a0014440c16030395180032254803c2090b004210386001c00c000d02000c034882036100c40300c0703d08041000d030032140c410f4001100c0703411160700711500c941d62000c0b508161079004c0800f90110310b5020304100581050010040c8043c0071b402110380e4405260281c9045011680c000c6c0c40c3d00780c843d18040d02601d01211441c1066001d460148640d09015104940f24820170035081e1140c650503100c0411640248800e511800e542c1d40c1c00c01c418955401c0c503407e203510442910300d103864200c0002d00d0f13580c028451004809410b03500c0d07640b600c2c1444184262402d01030000d5640402c0358607003160500b410401c2d54064508903500b10741e080a44481645094060f0014074180700c000307814444c0c1d51041c199240c42c200000c8814440d002401c00050341d070401c2c56040000c45a0905a0328040d410000480c01e0240d18850001c210864040030516100e032107240700109 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 195848453 1250 195847203 195847207
    0xc090f03070e04320c040b031b04020306150f0301050109060203040b220504020d090302070b04030f02040b04140406060302090105150d0906020d0c020105040b100b0703050f090d050c1e0105 83
    0x4034411800700c0b42c2c0628004444d80440c039800b1103440000b1401c800e4007110b5030100321034a140342024054100031503801d600038580180318106200c2c100f00282c10140c0100c0e40400000c14540d60341c03942d003000074010401241e845a9045958425500c01d00550740450500200058094030010440c0e08603030810403294100314844108410f1003140f02601c1e480c9801240f00401c107661648014600b14101c46000103598150345000313800c1510307076400b904400c00700740030400200b5010503001c0380d8030350304440009584040d8800a001070035440d1081c1211201141080100690f03a0301c80d005a0b402120803010130781c0d03904100301006c6003105803034140309424010b140d044132141e000382030654401e20002d0b040540c2e40068070704031080380754200010703915001840180051100456005105150b80c0740d140c1d410701003a00906d1148000003005c200002812034203011718a4141d400720304004011500a4066050503a6500c080c410700500c50070b01e1405400c9440001d203003400020714182c4601d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 195849703 1250 195848453 195848461
    0x12010b10051b031615110406020307060b0405061302030a1121090105060105070303051009050a020a0311040506090d0807020301020d0606031505010207060c03170703021908011802070f05060c090f03070e 89
    0x10007000c5c089080380000e03a80b070302c075041b502503541005403019111550003103444180c07504000f8240d542505029000d50314040906c0529140c140300d0744d202c0414000c01507a06c0d2211302a100003494600f000007640c200c023142c1558486c032030040d5803101030341c503400c1030501e51a2402000c1c01c8500964070709001c90810054200042e00a0b0007031588100d60041c200c1d900bc1c1e580d501e0a040e00c1045031141540b40c4e0000e000d0108540500ca400d00d02c00349440e000381002c0c00d00300414158894100308502c1b40340c48854620402451204803642c095024000b07640f218002d55601e0040c20241c000e84020a0070015800d0305484203864020032544140d00904211745810810707501103800100607820000310410703041c520800008c1141c0a1002d60340c0059841324101c640000c02c0751001240001c1000c0030f001000b621f00180310341c8441c001c81050050b034170043e030f103840c600410310103070f004015004100400014058541c090004420700350f41d0741c10101500010140c6801040c01100c052242d110042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 195850953 1250 195849703 195849713
    0x10b090409030e0d29040c0605090307091503020901050105090328080c0c0a080a03080a0f060e0a06180605060315030124150801050102060612010b10051b0316 70
    0x6078807041c0c000e080036a40500141c01042001c0c0d000b00094a0000065001d04d144400c05800030085028036503480386036007803594820540d00d183c0e200343e804102001c51044299075044c481f41008281c09641004000c0744000902c20200e180d10069109460081c00010103501407000c8694185000300609100c481100b660646a1803000504203058507500c03664002403000401442e0222200c8010440d090000042041d07144a0303400c80c092079007049030210300090f0001221b42d080000c3c00c7c000f10703a80d804c98048400920030b991241041d56094414480030301d0351640003074151505851502030512b034400d0044141c0c1e501e0300c40d440d000501000055200002c0c5c0c50009034172070009001003640a005c044411050a03546601204400d001c07000304503004e001301c08944458001d0a100006601d0040042d44805004003a40c0c083c000c600340f1000309800039030000e1140311000780010314039550740c1801000b070b8203c0150204d07229140003020444400010035601429405411968401c12a03555 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 195852203 1250 195850953 195850961
    0x70905030a03030f02040b0f0d0f180b070e09041104050105120d12110304030908100513020904020a0812040501020f03030f060d060207020414061c120302070507050d05010c08010806010b0904 84
    0xc083d41440d03080c030000c00c00b000c0301f400a000c0c40d00c1100b40d0585405d003040c0070108a0380400f00c200e60103481e09020740102c03000710004036151504030301c1c9a10590b860340001d0701d00da031201d00300c075a0203a040301c100020419001070210900d8402d440400041e0380360f400384040284074250100781540071072040c0710014407030081010094101100850b407000240f512402e56002a07404134085807108405000c00c1c0e00c200306c05000c20078040c0c130902c61802c04031407600f5074481e9050041e01943c994400517096403640551403000340011422078400010710404210a50040c0c050a80140194110140340402c000140c9004070810003602c4540d407101d8041144046010b0000c49041d0380070301c425005a512071140618078501c4048041e03003490044104580508000f682d00b1451f084071481d600401e04146003052508254100140d40e1035450070454503021003988103a510004119510302000b0040d045003a80c40c01c1c60303c5908050340c807102055102c120900940c5130701c0c1e1051150408c3c0e8901500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 195853453 1250 195852203 195852221
    0xc0f0903070801020a0c02100c0804210f0b150303030f010608090a12080402131b030209040e0a1109071403071209120c050d0309050c120c0d051005070905030a0303 72
    0x101c50606507581042426030b041403040d1808118500680810742c101074074605442c50951828200c4c040440d40d4945850007540564030814516440c4409000160810710007021341000003105440c4030b915240f000d20700111017440700003449030060145424000140d80c090108070342c00444c50703828980b045600010061281e94188110380328000401c425011240314840d49603245803141c034150051010b1850701126483d0700782d00e0000d500c01000750b11412200e03180000d02c0d01603034420840340050043c06901442c0c0b642e81c083e014209040041e1095030b00a034a10545924500707036180c2c4419616482241018610450b04100040c1640e100c2e1002a640040c040e0002440074420b84444503401c101801410224240b0140300007480b40070450541002008e180c10f0000c00100c4e500c1548469524a00178020291400440c00d42035050004000014010300000e490500d982042c966400d030075910181014076100c0490012481400000140c58002c3c4c000c11184409a5045005010240c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 195854703 1250 195853453 195853459
    0x92d020a0504051b0a09080606011e030504030e030714040c0203040509010b0d091703100803040f0504020318251203051b12160605010906120807060608010f1b080c0f09 74
    0x1240394070460001a000c1c00080001d61b035044015824001070700c0c5407c1e009400070341400443c880c6501c5c2c4002c1c803080741c01d1840040c90040341c261100d240a88040f07062846032039060044000118001101c2010716100c40011102400401c59000c01a0b0700c911880c010240c10403c071b0001405806c0d82040100b60301c0c5540da40004e007801240e21079100d48004061103a6203c94000309219013140c640c1c11003001303440e450000d985898a0301c901c0c0e5440c952180700d00c0d4012a008400116209c1411214882d051b594009807594030307407a030342e4010081e41070748074949161103c00c00220b07050000d101400811076158030358030301e49655011f1404030683e0211202500d03100d06c6108841801c42c4a010340032080841010940c003c00741d00e040740c144c0c0c0b0160882312201346402d0040001c0c20500900e0503859410411199650310142403040142813140c110304202d6081c502041d07000c84407640840304d504294800c00300202014001140d40260a503600500208103121908000e50410014001000c0007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 195855953 1250 195854703 195854731
    0xf04021c05030702030d0e12010e031804060504060305030a1205060a1208090307030c0f06031803030c1103181f0e01081530031e03040213092d020a050405 68
    0x142c4c0001e2500005d012200b00040c0d802c9903c1c03406051202c540d00d00030681e10300900c141d55000719559a09e005064414004d0004544601415207450340130b0400780c030000c0c0c400c5c400151641000c550380d510a89900d07001a0410000383d02c111800d20500c0c2c01414000d1502400510307203251440f503202c1400e0f050300d000300708200d00340050b9400c10484004521417410018880d2a0900782010150310780d00040615090040d5007250282d20000c05da070207903050800060091031040f04440d92031402021103014130000400c654070481d4800408207031542110800100c40800c502055070502016105004c92040035100344c0642c014110554010109074104000b16002000103102d031102560701c1089000300d4203891082a000d00803882c010403408000d6140c80349103c1031a1a040304810154100741020012408541e50000c2c000d002c1c0302818030500002042d41442c00f1000890b64100b4405102c64404880c4059040780045050741c000300320021880c070f84014030002d050010b007070300031070706803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 195857203 1250 195855953 195855967
    0xd0305060a05120609190203060c0a2001020316170a0902040b0d031107060806060f0708040f060e090708280b12030d141014030a061e050f04021c0503 66
    0x60100c140f4042d890240101907500302000e0b41d90901075194244100e044803190808091b8800281c41900306d0040980c40e40d0b501c0c0c200d9011501c40120045c4040146030503402620450b40c1500950b024444549805240c030f501e2600558241941c80303031318810038002030002902040c240d8440c52040380050404954009031200086104007941c0040b80442e80400e4503c145000c10007000c0091b180508103d21142402400652180140b051a078000300000440f013040180310419074000b0300c0c85018180400341c803054050502452041c8086c01800c0d10000a11442e211f10002400b415094102d0010002401076000501d43c1480c4c03036142554403000c074621a07403940d0783c026404d100303440061501c0e0940c081c590701c2502c8801098444c0800c554050001d00118514000c1c1114112483e03a04840303502004241850080d01300030b00401d240ca0043e400581003520248080c080701003080100d40d59520300240903040603100a07402c109170082c22035141c2d1020f18070f100700354018003c49040c215 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 195858453 1250 195857203 195857209
    0xb01030b030706090303030b04051302060a05071208040506100f170a12031b020c0907030506031f0c02010e0703051513060203010308040302093301050f0c011b110d0305060a05 77
    0x9a107034003c000161101004009142c2d15108290017504122002d01ca503052184107190800c1003440013a20a020000b904000140204100c0b00c1040e44a0381d10b1440d884841400f40004404403030030780342400741e80001414800079080c2d000070384e041d400100d01e43c02d040601410340d5075000e8564081c0743c8541903122010644040055128014a90300480c4130a40f0b02c40c40c0c1e108501190308001554000303044001190b0f182c03070482e0f5104541f45000a080e41d079080010346003400500c216075007140c040104110394051a001031130010455002405500704920b010f66031955988000390498000c0250058400c00d2901003d40103c10401324a40e5005103456aa040b81d10a900841d4800c000217010011402e001402d29841401c01101e50400b1030304503d04041042844a003041c090240c0c440d00b11160b004109540d80300001100464407510b450700d0090007410403607032080e01482040d80d9000040d101d1420420400c44480140c4040000d0300e0064020300405030910358403191003200800d40351 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 195859703 1250 195858453 195858463
    0xf0a08130b0d06080111030c0406230705150718050405041103030f04060906030209060d09081b0606040e0606010906030b060d0c050310290f120103031e0503010f090b01030b03 77
    0x240b85000001c02a1070030404a0845004022000c041c0c1c0051080041183d14402554111105810501c3c0505400f6a20980125003c1d402240c401804509042806030000e81409a07150054000c0003030303121000f06a6885a003103038100284d028510302807015043c50341107580c001d445901501400c4200d41c000a0540d0030040300d0f281e8440b00890100407003035100c02c1890082000d8103003140740c0003007280800c1042c403415070501410b6884420100130409648200d0f0f110a061151200d400040c5501e85034558200350740c0107200d50b04119080003030b074501061003402640b058481650140c0f500005401501d000840341d031303004005010011903607482d4041e01c5011155555144c1d80c078909026100c10102c3d550b00f202c05041401d245201002c2c000c2100001d42c01d00d8846096114004280c6842d90380c89030040c141c0500c0e840d41c000004045d0061908002c2c4140346501c201d415588007022a0180030900c42c0d5004030b40300a50401030080c0070381c800842c600041c900401c8098030400400c5c500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 195860953 1250 195859703 195859717
    0x3010f06060c05070b190f020c040507050408010515090610090f0e09010e1605062d1e03070905100c050604080405010f1b081605061509090f0a08130b 66
    0x20518442c00304040010520065018003003120a0b1420006c1e52400101c0307a84080440724107121000000d0311955008021180e000c590081c8184150715000000404580140c45440310720360809020030a402c0c48206202c01c0c1000140000985584d2602000002548602a442031048030040440d40184d00b9405402800b540d4040c02054100005001d0840e90050803086a94128040482010000f00d0400089480455000392101080034601000a10354440c80c1c0c980d11b00010740c801c01c01c0c1e488003c1c0900400c911241801490050b6085015100454084000880900b0700340003500e0b0406601180d0170b07103450203500508440e980c0928040d07054406a80080020508002381d6a00074060740f540b0b4982d02e400034450344001ca103142010007155004207455800300310090000548611507034840d801c0070495440b81801c180c03850b0388444900042e07020b4000c5000261914800144400c1e40141020080964880d40e464600054101954881d120601101e001070810092400341401c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 195862203 1250 195860953 195860957
    0xe09191704081501050306040b0c0309030904050a0e0f070605030a090303090204090c21201c08120a2915131404060e07030b0a03061407080603070b070201050903010f0606 75
    0x103e10080e0070207288070b8405174400ca21030f510900421000940c8180040d40000c3c620762955165103a15003000d00714040c200300603400c1441d02c010021350304e03140c1d00503400384207540040e6a080b400d2030810580318a160301803c2c010520070408901c0141081d0710820500e40245400100f042441d4002801c0d02d41c2c00303505035004042c00f2b42c01e011822010003400041c000c0400c1e194402c1c0301640d00d00d0845040441721050380301080d4007070030703290b2190f03070100b6840c0307180c41800884210340e4900b145072030700000b40184a4514071000552410700c280300e0407049044103903c841c61001c104036055421500343e0116500a44a0700441c0c101c481d841010700081204404506409401c01c403a00810100328100b680c42141041c10070011550301020f11a040b003a14a004101140f0b5440894440c4202e94401008240303007400b0180c0502204030094000d09a41e071710803180b92980301c101507071080c0b580140440c030301c1d0410030800150b0054009204841000e400822502c9014240307104070350b034ad9444400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 195863309 1106 195862203 195862213
    0x2030a0212090414091005070c0c050d02240d0506030303060609090405070503070303050c0c030d0504120c080318030616020c0904060f050109020d060e0919170408 72
    0x10303a561000d0700d03d0000e00380441d4044e46d40300c1c07080200d00c40038500404100900d201303564006030b8a80120210310a14103201c00c021680c1d10f40b400c103e81c80070090840801c0c0b0220340c0c80e03e40054600d4240c0a4680075148a901d0949100501462094004004204032580c4106c251160780000340c402036860340d00c41c54040c1c42d00c0340c19002203a2510030b179a000810180e01100a210015400050b64018034070300050580d1660081807039804280b040c8400d004a1600b5a0044280c03070040c0b03500d01a1070780d60760071682968000e0364805da1080110300c0010391400c003000226000811030710303580c0c00c85080180003510f9a421380031482c07045005102080074001207400190a40a60202c10441c44d6076442018001790b1064840c10001170800c60300203500500c803104a40f0608800f0b019207141841841c0c45170310380e91001400c0702e0710007400000e140e800e03d600001e04050034142000344 = true := by decide +kernel

theorem cover : BRFrame.Cov 195683453 195863309 := by
  have h0 := BRFrame.cov_init 195683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 195683453 ≤ n) (h2 : n < 195863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
