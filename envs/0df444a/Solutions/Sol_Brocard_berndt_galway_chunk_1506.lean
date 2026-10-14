-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1506
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:18:18.320761+00:00
-- url     : https://prove2.me/submissions/d8f2bd69-1b2c-4427-9926-b1c29d22e63b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 270683453 ≤ n < 270863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 270684703 1250 270683453 270683459
    0x6010602160501080402040c0207050a0603020309060c09130507021509160e1506090f0405010e09010b150d05070c050706210207120f0329090601020a120507080417010507110106 78
    0x2c4c001c07000900007a104507030b41c002e103c41c40c600030040c5000801c8050b000303003003182c0d80368406030094004880d4005903001d01030010ba00d9a031010200d681002000b00301c1d0404440c040c0881000741001005107055114102110059942454072a4480c411080080c40c40390b011301011149500719520880c42aa4610305100f01c59010304d41c0d81d44811b00907607107e5164036495000580c030042c2000303010b0f005403800c00040b5482418402c3c40d0f1091810134020b1000011030710502100800380b125400100700f00703002c107000350f0744650803c40d088409850302c926100d85913101e060400c00c070ba80c0008089030034000d0490841c51994618141c07003000a80c110b0804c412a2581c0c418540b03801c099404201c0f00c1e03042c0040c51030082c0c0c41000002080c006c1c050302075040b1103004004040045a9910404c00040055240e40c80050f0300c0c016554400f0081c00c144500040c1980c41d83c001000803202082c0900000c140030031140d203c000d0b42c0301c4c044000304a0f03081091002e0280d4864055404071a41018018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 270685953 1250 270684703 270684707
    0x140d0b0409081b071401030f0209091515090d060902010e100302040906080a0803011719050c1503150105090d201807050301180f0203160306080705010207181d06010602160501 77
    0x10750210780c5c2820081410079007102d414000b44203c10450354005a41410704c041c6040009a443c910441034aa625000109024804c120f000f1404029030150502080c0300005007107070480300e00284181400c0710854003080001c0e8198030440190320000f80d020034208800001401210000d0072003c0107013000c8605c0b52140140741c80140a542c410902e5611a03080300c44080264051105c500c440c03001c0f210f4030030318000d510340030628100341c46103403042c0e0300002895001045a002d696900004050035107a01d00540e091b4022408095000000c19030318004180e4202c12100260303582e03d60b185559a81c041000785035844042c001c0180f40103101000b1000782c120b0212415103001c250006190541c0340e80780c4020300b811414070f81101740040140100410b00158081403031030b89480c10300c8119254030340d00d0365550a42c41454016408007030100103601b94040941d612028040010810341c1a03104880d0401248228a06242d84044010404070780c0c10b00c1100000c000540c0c420400510741000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 270687203 1250 270685953 270685979
    0x90f1b0812070c030b130b0c030702032b020d0203040b07020d08010618030f0b0a061703040302130209030607050a0201050a14150a150e030c10140d0b0409081b07 71
    0x2480e40c00d500c005845410700180160f107000542d40302180b40c0552803e244940000c0381d40030300490381c07503144501240910003510140c0f440340c2d1191b8021810901000e94030f040c41c45200705400c8028454907182c5c0720801c0d1900041400e2845040051303079a09040c54050000c5078014180700c11908a680d00820300396004e4117550440b982c0380ba04400041c414240c000c5158026800100411580f5400c501003005d82070703509200380701000d001c1081c0c60307a0300b4540f41c201c24404140748581e08204005e10042c0342c4400500d240c00c3c0502300044c00e10320f100010a1a10b481503580c9004618081008900c007030782401000c3d801002c544040c01068002c6402c8101c014000c1d10903440812118101016511440382100082c515034051910303903190030714040c00d07100d803104984c0e000c0d0007100c1103146542000316080c0c209403903070398485201c50a5081e1654440d0800c00c41c142080d81c44007402c1420365154011100400d00034640940c0d41c40c81a400300103000101d1010001540203040100252020804 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 270688453 1250 270687203 270687223
    0x90915020a05031f0801050a05060909070b03010605130b0a02030705060a090807030e130507110f15060d0c0305010f1a0f0102061f0906030b1602120a0c080d090f1b08 73
    0x10740004004020f130041380308250030307003155582e507280c1b40c200401080c2d260041406248165050625511100d51194031450240101c0800920420040111074840c00003001850703c45060180b0040d102c410020306036214401690060b440441c8c60010300074140b00140e081500c850081000f60341365501d85a00d4020403c02a05111407840005071703944682c4585480405426001c000b03a10340503801800e808082c9075080d815101d41d141c0106955000103091005808010980c0415a185020482558010103089425880c1c1103c0080010024000d42e000003196601c0400d520302070300b4154106a003100005486950031424520b11a600401c4071034010070300d00060845241d101000300700e0100c1c00e501402d415407800000005103c96002814000c2101e004481f110801050080303907a507040520382c07a4103481c00c00c00743c5c503864040c00c82c42403424850b8554034209050078480c1c20495408100a0341ca954407031910100f04031586130f1440c10f6040744410f580c1401d051a0509554070724002c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 270689703 1250 270688453 270688471
    0x8220201140906121510050d0506031906020901020c01050a1b23010e0c0d1a04020307030c140312040605070f0f02040914010b0a120213060f090915020a0503 69
    0x407a101e07100c1004040b500d840e4005840540d8444e0f444806088000003216101240304202d40e41141d6807824404d442c8484c40565580fa00f001e0040b04445d0040402030701c0254903100d50901040c5025000005800c0e06000700801a21408420006418480100300ca541044410031a90038207d40003250020550f0741d81c450f00b0a41a44e519040000b00700d00040410b00c4400d101d541c4112503015003041e03904440d040281e82e8900340c54010301c0003100e0720074001400001142011460f42e846152207551140c0002c1c01c490030545d603a20381f24450b501e80e070004540400103840014079400c08114800f200303120a880761b4646480c000f4020703d03c0c012680c00a244143c0d80071140c1c180900707000e5642d400c0d03030000c004120208003440c0040310080c0510f0031449550801250141c1c61404e800c1500480f2401c91021038091859400c000d08601400300e920030f21641e41c800450f24440008191000d00a20000007900d0017090525107841d100a114030916a8010058001e030f44d44d0160030384c1d8000120f6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 270690953 1250 270689703 270689717
    0x1221030106090e19061e050603011512091a160801031e0501060503120715060806190f05090f010e01060807051012020f0702040b010813030503060f030f060708220201 73
    0x12006440302c14204074070b040e4031141170000c08510707201901d451500741025a20040d00d20b568070010f015040c0000d1040064070350445000001460140500041c0e03158040c100181a4165030349401c9111003010415134402032180412541102c22514401c00b58a1410206003661540d503c098050020745112480306901c5403030035041010940020001e084000d06903640c80520744000c004507004400c00f5610800c14201c00520007c4505c9030905840302c5202a0580c1d55130140040329050b0515076003060756079103034840c88100b030003481503074004c40078000689107500040100ca403c1d9203c4200000050345400d0341045404000910b810850340d040c0c800307a50f0410040700640f4540c000d01c8880c4041ca000084a11514240b04001d003078846c400c4030200300036043c20004640003101261800103d481400a407804070740103e0145174000402011041a6102000440e0502c031000c4021031060748144240448540c0015001f0341c030603545a0220b012441d0040382c0c282518040300064184000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 270692203 1250 270690953 270690961
    0x80c09090a20030a1b0f090501080717070206060915030c0d030309081b0712030503060d050309150319090c0e1f140901060206060112050a02091221030106090e 70
    0x9041c10080000310b0b00107800780c0300d1030114280c44c040d16030714200d40300010810f81013004841c062520f0f040a0384841d51440015414a00156441000a0050b005004507000c1d000802102d01860794485d03540c43e400f510b041e003001018000d50740d201510850020000a2090316551000079006844c00011500e1001600f550b040c2038000f8070340340d4000351004000052042c4d031545200d51900001007807000b12100039170365040d8015034954515005000072070410100741e591a00307451582100d801102624980707941040010804000786107094030001c008001c20402c9808042420410b000307450080c04240c416641f00401051203000f40000704450b003000c81c900324401101100003490f00810307142c1090300c806044220004000009206454400012030b540c1e2021560030700030786060b1a0603203011802004a00030700802058408941e600340454101035880300c00455001945c500901a13420b501040110b10155046264080e024200010028142c0c0407501804882e0b44103e25507060316 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 270693453 1250 270692203 270692231
    0x806150a0816142a0607120501090e0703020105030c0d09081209160b1803011a132a020a0c03060203100504060f0b03070c0f0c06080c09090a 62
    0x4112001100044010400300a51600041e41e540107100710344050032070100300304044450703035100340c04650400400c0c44084040403c0c0300004981400d8203000482400642c031070180b0b000341c111031000000340824031902e1959000c1c41602e0250199000034001004c854540c07aa0b100041c1c84001d04000000000580c0c4414a005980c10505400c03001c0c051090b5505010045822100040c000e2001c400e0200e102102c001402400d840c004400f11b103001445e041401ca00c541140c1207000c00c0100d2001e0f110025a0203104500d051098200740046000080d01404203840c4444200e0040ea480d1449130b1019803051482007500383e14102c0d640001c42000c0d50101c1c18904451001040c0c82c0c4006004000c00105402440c4201a40000710301001d035a2002c01041d141240b0842e018400d210000344482c0c9a01d1000319400821810b0101441e001a611a0319050b00000286d40c1c066822009000d1340350300c0718246400018407441c13035082400950000c1c082d04005410300e809581d6030340405007554 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 270694703 1250 270693453 270693469
    0xf030f080307200c1215070f020708030309030304061b0c0f020a0302120a030e040c0c170c060106030632040b030f160306110408070605030901020912030a080c09030a030806 76
    0x1d804103c0030049000c5a0b0a9540f15554200c49104060154069041410001c1c100410741e40130420b003102500c403901c040e10000891810001140148103002c40c01c02010001103018021007001182d40e0319280c101907044031140c1d0035241401c01e01c4250340900c56403200c80d403046603401002d8000014043d20000c1c80344001c6a000a400855286030440c14410125000400034040c0e103e68081c1040b5404101c21541c0d0152001c02041040100c000490301c16602031880c1440c1c95201c2c0c2c680680358051a00e0003100364001000692641014046111001d0040c15555426550000903456070010034044104000d0a10302560743e0b090004415030342000a0070001c485a42a64072140d90300803000c08401403070205840c00d0b418407100155040035041114101e9498802a003000d0741440750071aa283d0011300b05064a41d002d00910000c1da4910803607111140102005668460801c0009040f4160041401108420600c68402c0070f8030003003100843c00c1d03818038005450b50f4401001504003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 270695953 1250 270694703 270694727
    0x8030a05030f07050417010f050a050105010504120606050a1512110414040603170c16060c0206030a060509180d0f050418110408010b03060f090304120201120f05100f030f080307 78
    0x744200049107041c1401980002302c1007050000c14056a9504100507040d91020b1040e10700240c0108030400c100380c2e440e0b0a121140d0702c83c07000401c60583d2500029409031701a0082c680301c5802c5801850075581011010800c619954000d0010345445600f409050003144941540d031200721070704034020380d0b959004201456022400200c0c075840045a13810580024072020254071a0b03980044003c0131089200080324007541e0341c80241c030f010b5801d10100b500702425113203c07140c640002203840c5e550180114860401210b591842140e541681c40c642800701c511141480f4410714801c80c01d0307a000e01100c0940c0d5013032480045101c44c0c459410010605030114013400320000c140403e94000642080c2034411040f01120200e45590076069105941a41c10740480e0340100402c014014885003001106030050408450102c4110024001c0e9024880d550101d40d80c1d41081244501c10000c188020f071094014100240c2c3c00c580e00e02400310346445c40503010481c0400094207051040e000900c00e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 270697203 1250 270695953 270695969
    0x16090f03030c0614070e040c0e030a0602090d050a03020604021804030903020907022b080907211a19051e15060f0c0a020f06180f03030c0304030c050a08030a05030f070504 75
    0x640e2401d49002002012161b460030310982c01c1480841920b84540f0b0f1020107560001c0241038900720650f030303400081d402425203c0c0c001c0ea0395206040860b205000a10241b4003a401501c42032520340704005890504100c0218001c51010501001c241d2180706542503c0e810380304440c4da606d0307140c0268500908a80d030000d51140f82a114900021400c0c8068103000043d2143c070ba0310b03181c00303070b2250b124841800741d00c001600c4c054203101c0a40c0d00d5643c000d1014010040342078044034110b00c1c0d81541d80c0c00c480c0851464802e99220f84240081d116035684546224072005540d80c6d44100c2003017103040503048051f9081610029610307541c5000885400032540700c55240c0e1040d2034a40261184180ba005030710400503141511042c0c01c02c10200c403011400604210101d40c01c401c1000446500040d001ba0580720501c0040800d034420001000a51300404070f82d89030078649000c100c101c000681003080300c1d0b00207001080f4010b40203400c1e82d407c814500404019a622004111020b029607882401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 270698453 1250 270697203 270697241
    0x10c050f0d0c05070611030d090c0b0a0522080c190b03041505010503010b0612091509070302120109020627040c03060e150901120f0204050406020316090f03030c06 72
    0x12001e8010b00c0076032000740f10304181d510b501e0f510070b010340318980003007105980c0784c00070006c02000c41030f07551190351040d00c074002084100d80c482002e0881a0803010352407000c2480000c0e801e0b03804002002018009070f034032245c0c02d171040c109040c458842840a0615000e450b0040c1070b034a40e010144450341c0944004840b094482c0b9040c00e100713081d0300d0340480142c9118a080004500d07801c041c010741e07191101c081c100a103010382d403680080303051070020700031402070082c01204411712039105141401128040002c00e1803e096004000f03420000b609280081d80c508003600006840ea0000d607043d180c20340084040c01410300d181850240c0b410008603070f000b072920400e000000e402d9801801503405050801c401641c81600800b0040031240c884c1d03500418107801080580d5040044080c0148540b280301008007813540464150740b000c0c1c0341198510303008020014079600300e03201c0c40c0c0c40000310719003401000e14202e503c01400616020140400409108450034098650050903041c08240c1c116a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 270699703 1250 270698453 270698473
    0xc0c060705031b120a080408090a03110f0301140a090804030b0a090b0106051219090f0f0218010e061302192307030504050d11060c010506010306091a010c050f 70
    0x2510381d031200140441c004420f0350303800250140042e0046801071511507040c6010a001016940140024800c0351101c0c4108035860032a25000c20510080d886004a42826003e250812081c0d40000119a009a00d0900005010050031140c030b0b811640346e80000400d40c4030760418421174070036a00054200600c1c203003400750106135540811403090068452244a90700da071403c403458070550318519403d8801c10081061010400d10344008503610383d04c0011038150035a00c60a0602103404240c580840d840c040d402941018201c070040c2d51610495503042c3e60622060700e490000140160b40030b01c5001001d4003035000d250303048803002510b0300000c0f804c94180060040c8000e5114418086c4075201c03050208550000e0070540d03509039419100c2d01c1c241418841030211000403101b041d5540150b0921035191501d505008008500c010b4001207200d203807000025054445680c0103904dd94508078440407407407141c44060b044981c0034608070032fa18001d414a54a407210802584415000302c010700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 270700953 1250 270699703 270699713
    0xa0507020315040b04062f0c0c0f03190305090603011701241707090914061006090501051305060333010905281401180501050406050c0c0607 62
    0x242004510803011100c0034210040059078040c0241c0d001804441400e0109001900e2504031640302c50650750300c082a065040d83c00340001001d00002500154001100580f52106001054000d1003c2d04c0c501184280c2030046960b03400c0103239240a17801c4800b824941014403690450306c107181d00034880c40d00c0e0758644035598608021102400700e0fa40ca411030f14085419442c10100c11100c1c1d800f140650107150035000e6403501000c100401050080d0480441e85820900c100c0300765600034100340c4e4044880302409460000041d0460000c944201010044550b0110014050313400070702e0955190a40101d454045d0841500030380d0380f2040202c20440e2a15a03044000081c009404802030208043c603581c501660a170700701640095140318052050f8148440011601c4001001c402c010002c0d03101c4440c41c86180750031074846a648940744004035a404000138483c143d00c1c0c00181805460100080c11030300c184d2040b4010300c98003003800111100288007208140c5009440c156940d0194035207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 270702203 1250 270700953 270700957
    0x512070606090c0201060e0c0a1b03080618060d060b0607060c0e0f04060315050c07062307020f1005060d0204110307090b040f031b1e0e070311070f02030a080a05 71
    0x1034102d90619000005207000e10500034032045803090402203229441e0b82007511240d82c042c400400c00e00180c22417010f11001c1c001c0f40d80c0c6003c0c1c001d1b0b80d400c090f03040220400c00d003d40409080756000e0391513003d0207090f541d003200400c00700341e10140c002441110030700480e081c0d00440720054801890040301741c3c0040c2d040300d200510303d0401c680f6000c181c80f9400400c41102d92500001e003014101c101280f0600050354412a08075042010301810620b865498034151489210821410070400020014070402d620200340c0005090001c0d00c250441c0b8110183c0d6480ea0050301c000b02e40d111004501030303440f10011001d031075070054020301c0b40d0500700d0b801161581c400c0e12048002207204400184c198004420b603015a00805020034205155440d0f480a20000e021a4400e68000f42d20000d900100c00108943c400710110307000e003c003460000c000c6034250004081d0000d250522042207040301c5081c084036005980070103c20007003101800880d1408402090042c03c840300090340c0f0358410f0308880 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 270703453 1250 270702203 270702209
    0xf03071a0402010c1e053003070e060408011515170408090406032f131a06030403030902010e0a08070b0c011b05030130060b220b0a150203030c03040512070606 70
    0x700f11011400c6110f0007c1075107403c2403c8010848034003005d001c883c01050000c6411500354545007860840030800110541d01c580d000c074a070341e903484030760808a10003030004a00502d2034440d0400e080f00003030307030150070000301103401c51503400d20780e0001d420410800103844454001900c10040c00b52285400c13450308444202e0324901c406c42000841203500e0080b1000c0094002500401d80d2407044000c8401918100d403440c2c01d401c110141004880d00c5c1c240145104500075035010400d00305c54000900141746200e2000e008000000080c03003900c80000b0280d007121b03e40310740382d0343d01c4842065850041071141e03040d5850004040c0380c1d100716940702000d135041e500103078540b040c0f50200300705105d011100c01260351050409400c4500c0032458503800b4101c404805015044c9000111026025242007444c40070700c920340c2d81c4903502c03107400c19030a04400317094030248285080b200054082d43d139020081c2000a40f00c4004002410440140689558147c01c4141030fa203036529031910314080c00f80c0f40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 270704703 1250 270703453 270703463
    0xe1c02070b03070c03180305120a0f081014011202070f0c0f060f141603032c0a06020306010c06050c070b0a0203060d29180f03071a0402010c1e 63
    0x3030008141c5000310012640181002d440c4c5111100c1ca56505807451841c90f84480101d440408000020900c00d01500d44e15400280c0032940d02c0c100550054962441202c042c0c04203d4010108258008116a0313031051b60710312000700092911070f000480d00c0c001d000c00030101c0d850011a00030700304900341030105102032150040210b4940c841c1d8911003c0382c0d82c1e22500d00010703102000c48920728000d1103810520072100e00040d14100c1603000806040312440f2084000a41c3c0e02d00c45c04403050300c1d00550301c4c00000d510041905014128040d903496110030006000302c1c0d40000450003aa0003032080c0030320720b0740c4041e0501c010310b00701200311181e40001c4030507140070300110009101c01c0ca1500c01c5900c18400203040c0d1810611580b141a0701c401c00003039071014655126034103c40c001000c1c480d6807040912040e80b403200103141401e01d0500411600300007181e88240404c0e000140d100601614140900101d010b0756540c0b40012291241880340207000c8204031031454000070240c01c8180d1000b070086c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 270705953 1250 270704703 270704713
    0x6091c060510170a0303110403050604050609010c0306031110180801020a18051c031112040302040b010315120501110313020301050615090103050a1d0a0b0601030b0a090f0e1c02 78
    0x40391a504041e100c040c40c10340d84d80020004800007402a8400050b151002d0211800c2a880303543e00ca1510741c3c19602034404c3e9110310100300788000d090141810341c2715140b8050007841d18560b00c06402034589500c0300d100d421004070844800b07201702849038203038035540490b0240a40c0ea10609000794840c0c83d01d4000034a020624072a0003ca112241d0221200030f00160800e25031101c04600700922900110100940c2c0c00c80804441400c120b014140c01416403115515859441040201e440c20205c0c0390605040066910704103101c48d00307480441d03401d40007101d886209846c0541c014000c0c4078007440c1064003c401d10070780070000800c1d00716561095000300700c4c44c1c41d03441c00c00008030302200d80c0712208601009480c03400c0d407007a0841c0360044048100440d0b8115204039900c007203000c5150740b504650001c541c290510450102c00c2c0d410120a00b000c004400d0303a40080b039a811013074040d20302190313103400300070312040c0d01c582c011200040c6c4502501e66140034200d5981c01c00490880d41c070b00501c07035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 270707203 1250 270705953 270705959
    0xa0e0d1115040209040f170307020f0c0301060b030112060b0a030c050112110405040c051911060c0f0702010c02130606200f030d150b070b041e0f0206091c060510 71
    0xc00100c1030b0059800801d90207a035925982c0b10034100c240050110b4162a401d0340e02009041014041d40c013407003454000d0701e003e008002031545094800d0018512a070305160007041412a42c03402c49044d90121054200090020305145026001819140b9040480880004184001d15868005984099880c08100c07010842c441c4180c4d0010940d24444800c2000704005511f00350703000c40200040c60400b64103082e4191100c502078801102c103140800d00e01b20384891000340900c440c3d40d120320ba6010081c10311800d01410b242c03a01803614020b06108448000c2c60555580914410203c0d540000c180441501c41c80d008210341c20b040030a0b05d00d42d0034039140385465080402e140c4907a4640343c00460030414018810405000c02c40c04903c0301c2000b1210100c2c40140d10402001418003404400001d8205031505201441c001807a800b4035a62600b4220700180000e40e0402d4010340490380e0039201d85107800052241105035a01c0010000038110701801c1117132540000d4030420968003240303c180d503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 270708453 1250 270707203 270707233
    0x14030f04090605030d02280c080703290106140d0f0b0406050303070b0a0513080307020c0306011401050a0348211119050c010b0f0d06050a0e0d11 64
    0x1070000c15450243c7c00c690f00c10a00040190640c003c0d0300c0c2c10898201d80310915032a0b801001c11190481e000340c0e008507109105120451a03142058251002e050103034031389082c003413002a070040c000c000c00c11640c442d40da42220075000503121706c001c01d094100070b0900b01c4103588008152440c0305030302803820140002110314010040d07400c1580c228a80f5252690755800a800600005102200c4100035540100119005030051031140b4100d4000303112100c020001c040c039060059100c0f00302498038a020030340782e99028058a10003182c3d4107010503d1034041850b050000d02003d43c9044000a07686406560601c10300b01d81c50609084503410b04d46001400c0484204210b01c001241c641040081c5c0349110201c3c0c0d0040c0d044004554400d401e28034800c040828442400300c015000031070215020184101c28070035040c854070203c4040002040354804a611112041006001140e80f2000107048580a82111100703442542c140c1c0c02c00c840c40c600140081d04294a40000e901c5001c1403078110103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 270709703 1250 270708453 270708463
    0x801240b090103021b03030c040f12110607060e1204181422060c08040b07033b0304060206070f0c0309050603072f010c030504110d14030f0409060503 66
    0xd2981505a03207842000001540a54044800b0740901340122045500d000d1080c0b01950089203e4010290351340e02c0d041c1c1010300164079822403840c07000701800048c001601803c0c81810004281d40c0b40351910030508088005003510300d80c012841c080d03000c40f0f4101c0300e0706400401c2500d0400d10000c007801c4051483c1c030704030340520009991a91209011504040d10003085030200220039070709868048040d03075440159001c2c1480e0b000415614001c0c0000c0200b0003250940c010340d0b600c0d040090207602d0781d2a00143d22850301d41d1121280c0c031003010700608907513180105040041c408607580d40d40c0c1e8000c000d6491104035542d500040304003000f0400389100e407045243e80e51701543c680d070346141031104124980d071025124005110008400b8148182c15408441065440c4000104c1041045a46a0950313008807924007c05107401c5c03c10000404d81c69002050380300c03e94403110900010b00d08030480326400c00c4821314500c00850b0040940e0031000042c81a10b8403c80244074060383d500505a4032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 270710953 1250 270709703 270709709
    0x1e06030c050102151623040906030c170601031e0b1e010f24110d0f0e0a0317090121050406110a170a021b01020702030c012d03090c080124 61
    0xc0300c488083c1c45d82c0e980c81a07170561240481000340780d90900c130345049191664090340c00301c0c2c5001c1c1c60b00c00030410302c903a000d01440105622120941d40f820300403d03440d114101404010441202c40d0545003043d2000c40f08541d0305a0300041180d250304003003421301d400402c0e1504a5031000c4140d800840d0328402d1000a17021070b4120900b0801401501c80000c80c1e140c0180141010020200041a1000303402c10002905074902e1b00d607a0f4645690f044004d14124015085a02480b510704007013000605031041c0900b441d004500c02511640c0407401207072108144802940018009420701c1e26850150f03000501861060604000b0703400035007800e0455005006a450200c1d4180644c10341211003114422341c08807000d00300502c0c1058030309140010f848140880c1c0c105030f60103d00041141010001290000000d003002c015200089656619a070000100c40c541e84110921210b40e10b4000d400004200f580417540042440d2100d070628000d1044440c016044884442c150740c00154081c403d0060b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 270712203 1250 270710953 270710971
    0x130504060806130302150103080a03060608060303040302060f04050a180c030b060703080601022503061d0c060f1e07060f1e150e0f0118110d1e06030c05010215 70
    0x115070302d50706000143c101401c02913041d4000d0030b40c00c9000c150201012406544100c00e0940c5481e0b00c5903008040b81c22079048601841804810b01901e958000280c4040360f50460304255600c070090510806806030340e00c000d400c42c0350b460001c19034088071002e4504100704000e0403c140e50300381c002107059170a401625500060204a241c01081c8151200c50388120180101c450122a158072000781c00d860100030882c0d0000d02800303004006182c0944260104d5000d4100342e9a20300100721601c0e0000040c03050301c01c22000031010f001605d8407050310740c11030803a0b500c1503900a0f850301c11042a801040c044031524540824401c0719400380c410343c41400c00304041c9580c0305a00d442c0c02c500601c0f00444c02c1c0c40040f00b000380000c1608058030f0344d5204031441d0800500b0b41d450802840c10702c40305c01d071400c200c1e0f90400040c040c3d5070fa038400582e241e9800c1d00c03030007050001d1a440350f10400c0200c40885000f46090140c08424040d45c0d00820b0210360b007ea00b00c909002603180c1d41c24154a05440e4041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 270713453 1250 270712203 270712213
    0x705010e040e010207050703061d160e04031704050102070b0703051009180501020c030909070507050307080d0b03011a1509150a0509061207020c0406210c08010606051305040608 78
    0x1240c1c2080e90166001041e4400010b29200d51038450a24250f4507510031145540c4911202d82032200c4515100b41c1079070306000901007800d05107410b1898a180380104510650108000307024180b04d081c0c00e203440305070704d8406003c0d230400e400e02c2d43c0070707500941054521602d00404111828840e1141520404103000c40c408010b0030035010030090308041008806996803006035401080c003e01c01405c800e0909002541da401da03a00030b10500410041c10318003400410311103007001c1a0040225081151300810550b42ca005800171400284041d21040c6d4056181c04c40d0010559610004840380c0f10381107030402150403041a03106c846105240c2e0550308035203040010380c1c0062100001d8076014140e8244141007814031804100c01c1d070403c0c044401440c25840c21701c24207036014086850601810380781806a64108400241030300c00f042c10445842d55400b0780d171010300803030b894020007401c011002800100d41c1c64900400a1b000404002d14081c00e40200280310315040c403030b0b041101c44207800340c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 270714703 1250 270713453 270713477
    0x110f0a03090819030b09010503030405060703080403140c030c15070f03090213110d0b030d0824040f1a030106081c05040302040603151d12090a030602120106020f070501 74
    0x10301030701d4490412100190140300e01d00d12080d004a24441c03421040d031300001d880030000c080026100060780040d000b0f410401003403103a81c94074000c45000e0b40d014107044040c1d80748d07454200e88804652030003105c1080c004c108545642d0340480100100c191482c110340d0440546000d58040310010768401f008205c001440b241e101d4040c0d0002e46080d4001403113039504000302d04150094580002440526000001348071900f00c0f0581b040c515451816001040c03850009000030b4291200900303641401003400c01500c0b10044810300e000c01100d8060801d2121040d00c6a4100183c0826003c000030f41030034120300401410305104410455100c000188074656201e0340c90b0801088a140c13070170030820f04200100143e2a24005c04004600c5060041a0422201d25101c126012608410031902584900b180030850014080c1c80461620a0503641e400003030002843c6509035500003840f5030300114a15091203203150a0340d0491b40c3d650262206103c1100149448003080d02030745000c100000029 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 270715953 1250 270714703 270714707
    0x7020f01080f07030f0209030d0c02031504030e0405040f060e0304050a0b070c140333010509060906011b02040f05220506010e06040905100603020411040e0109050403031b020a06110f0a 81
    0xd41c1317000034201c005182802440100c1d06204501000c0c00114030000d2001c41142420820448810a0b14800c0c004c00c0c10f25540043c519200001500d1007540c454021506000c2050341d050f244a50001c000c00c5031101000c0c40c02c1c3c40350001c0c0f048512a4140c41c00c00070315800c0150441d05a01d0340840221072850401021904101c140d50500e60184a0700c0392051180307241d031071003212844000700b00c40b16455660f0303904000b605050f0031440c0504020024407400d030f00c544900d00c0e0408401d0800c032102040b0f00d042c9410310015004041e5101381031072613002d940341140e8040e60051600c1840046000d520212005d24a82c84050082450b8003040040184801078640150000c10007880400c03203a600d503c0d40c52512040a486005695072240e0030011461f0902c00c0c01c3d1200c2100300c140341010315018031421100b0741442a03050441d00c0c0e6000404151003948030807040c10340340d040304081448a01009649140d195002ca0b520381c0342059000c2d203d45800141c4901032403401185241109940302 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 270717203 1250 270715953 270715961
    0xf010b13051317040e0106030908071115070b04020a1706010e0603120a020c0901061d09101a03070f0201020403120509012d14030106050304170d05040807020f01080f0703 75
    0x10b115a920114000000003408140b544542107060780450b030f01e807401d181000b808202e042c0c0c010024546480d140100249040050303420407030f040304442d100c0c6604d91740440e100c071080f070304161000c0c40e0000703880080211002c05140500c0c000c0d100c3c1c0c03d1864803250444080071448440c01d00700d6025200400942244071034469200d503001c1e05891030000390307aa0044545e009a2480d0003d0381012070300003004d080001d19240103140c0d51510300d8440303d100b04003224619030262150702821010000801040d1841c1c00c00c0000d240310a0040c0040300440c80170b9000d41c01c181c81c0ba000041014140111561050083da03090300d41106480c062681210000d1354942d2015101d281801000369100303014050b9801045c80b40701c1040e004d6403101c1d80184000f045e94171800d014080a40040c03006010141e8884266680542c3c04a04c5001526010414050601035103d03038000c0c550034441007004008444010300b119610a031540c0038008041c100548842e0700444082210b8106c0c0f0000442c1544a600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 270718453 1250 270717203 270717211
    0x90904120e030313080d020604080d0c1b03090e07091a070302010f09030206270706081e070e0f0f010e0112020403020a0806072c06071e140f010b1305 66
    0x1000c01c44a9103103000300c2c0c01e6410502403084440f2041c0c104000c480014010041c82c0c60a510180001d80791503600c030340c2540588d079807640d9400e0f9250b950343e10840c080c1021041200c0340580303000150449150081004906000d20103099003000040f03410140101462170646500da020002903000368441068aa000320304207904642d211000007030481124440c2d901080d01030b07070103018285030a0000440c0c0782c0880200d405400861290741c0c0d43e0700004544241030b60304e14034018400ba1210401c01d03080d00d90301451020340c03403582c0c82448030260300040395410201c01a00c0340000c84024904200c4500d40d030240160110707011800e002d441d503214140c019814050b60a00504040d141e80202d040350102da0003481c415400b9000340017081e0f412a00f0312020304094040c565100300c41c8005c01c001810a02c43c05406108003007152020000010860580504440b01440104100341040712a84001a03241e4a4074043c81100c00c41100040c06280c1081e28003130411003500450420f0a401414020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 270719703 1250 270718453 270718457
    0x3060c0c070b0f0418061d04020a0b0c07050d030905030717120405100c1e0602070215030402212b090b0a0c0b04050102070206070302030310140d020909150106090f0b09090412 77
    0x146d0201c1e0350244e000b03005501e0400c2c01e88000355894140705114200c4010f80208a0f14401130040c0d1001010002d00c1c181614000d80d000340c2044220b240560388074100c0d03000950316005100c004900155024010f2440c1c01c503420440d60880f4240d8001c0c1000c2c8180d00134140c1141103a07400c1503078a03000c0e0004e041d1140c13048100d40980c115010502501149258003203c02640004000c0103600e8112501040c82c1407030003142c0c1ca1400d050b40005c18409580b4051118046030001c80780d180c25052140b0031101c0244101501d440001c3d11848181300920540c80c800324803a40d0300403906a03055406d41d19900d95540303e01da2640340030789850b115044028422100c03507401300a164010b85480c400380c0130b03141c4079400440c0c0b80d080500f1804c156a09070f80190010700410b000c107a03116591400c6911916805440250050300c036159621b05092074040341c2c8580b00070a00000500561242429044420305860260501d8942c40743c06158450001c9140e4894106004200812101e01d604c80d60b06074a8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 270720953 1250 270719703 270719711
    0x7151b0926071715010b0301120f12030605030f0106140105090303070f0c2102030303070318060903020c13050f0a1e1104050a090e0607080601090503060c0c070b0f0418 74
    0x14140c602d440c450b40c0200000410348904070750700d11410000b012200c0091400d88081d0360420301080c802d03000500c28242d0400340000b10b0710a2010f510b011040082d0003080c000c228041c448400380241c81c0070b102c0d150080c0f1070340100c1c500810040c4910b2041d40c98030006500780c03d80c1c420044a2640028004a505020801986000417080b40404a00902c00e500741050726192408260b01c0c00840030000360603105080001d0010781d40481101e03801003040c00d0000344108510b070105101407600d000105564a01020765040c15000210b03400241800c490103540c0704154440e0801703492054906160f60908400442e124075120f0704070480c42c07040050301c20400364200d03c1030000c1d603280418956034010005400d22031401c1c04c1070504050008440240300040510745901e64965008091204104520010500c10307849a810301c4010640202180c0903420907c14001070384c2c6c07040050986610a594000507807080030f03410303500d41c002c07000015420a40380a841c1da00e0b4034060315819410720b42d9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 270722203 1250 270720953 270721019
    0x90609091e0312010306060603060b0c15070507080a03051602010b1f18090e19080d0504050111071a1005100f1209080a090504290a08010207151b09 65
    0xc41c180321402103006c1e85002c1405468084090b040f6403461b000f0481040c0100145450321000080c0d0740c042904156070040b055940507011107a6018040d0010a8141c00183c01d5100d40d605030419800307070301c1186d8500210500410240e00321482c01901c42e07084000c0e140513a1100f001042410702514050030304070b584400c1400300750074080c60f90b04498055135503181c0742d0020880400c0780e490107420b4004107007a0924035403504c1109004500a1110068864000608104003034220b0512454066441600c135552450011203060b2142566201e80400c1c0c0c0c00555194848403000d01120f4000c0d044041016001100700c41d200301130010601489080d0350203c807294992321991145501401003580c840140d800020052800303640124480c900702121591654030b042c00a46003803122050f40e441145850000c50f080e540140d2084140d5440440c0010500038010f6403a11081c2d8030a004101400c1e80c03404400d01054002440b4000a400c0304c1c0034094048507441e06d00b42482c81408004040030303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 270723453 1250 270722203 270722227
    0x1302030109031706031b09060406030605011511031201051507240e070602060612010e1506090a0c050702040e0c03100204080f030702060a0f09031401060302090609091e03 75
    0x4034004080300095500c0a254500d00c0c8203071100d58124004902600c50020401c0e005000030041c4042148210007c502050055441e50300010003142d100f4420b0105e50703500c0386208540344c0107808140204d080072920780c07900381000c411140040c0d99204641c010380d0030a07003031110103580c80d00e81c090203403001c0281e1408245c00551810b404104444100d0407414a01004801d441000034440d110764041c02d0309000a80d00440c00c581d129100703a0350861219880391081d405004814030514803409850f40081d070189882c603115103e0401500d50340c010b91605002c40d0201d615504802e40040c2050000c400140b4281d0020b00d410b0003044110785251140c500064101007100c0b00c0e041c3d069500003400c1001c01802e0180403401c600010146040c040e9603008a000c5102c0c03000408100800b500501c40502e0103485594040c40c1c004110036110408106190b0007031205001c107a06c0f480500c0c0c0051024a4840c4009104501f1080070707160300c0c00030381c459440444070ba5401040500007030045a084103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 270724703 1250 270723453 270723461
    0x31e050708010c1e08070e030304090f0b040b0303030714070c0e0f0403030f060f17010204260c1c200301090813061806050a02010605060d020316050414060313020301 73
    0x46110002400d01100040908130742c0c4103940302400d280518407007142164101250550101c9a4100004604200310000341175105a80113030b619240b40400c0910600001c0d031046813200020313201001000ca503d410960340e400300b100d41c2c40020f00d03a290003003182990b142c06011400d205800a40360300f52582c00c0f0740014441280c2d041c0d41250f80100300418035506018040b880078100d1010405242000440e000c054403070f0041c0b0080c89801c03a00354885540940c1107400415401e1240140104280100b0301143c51010300d0088600c150031144800b8070b030814918007011400c0e000e80501a10f96907c9040c038207034007102c04c0e0718000d01c1842c4000c517440c01e0181040191041d0100b6a80b40100c511580d5071500b01d0f0400f00411403181200c0029445d0002544103071b81450801c59100c11490034200c4c0500910f4000d0387c1c1040303000c980b0358a00b9482c2c0c0c0145000d11460000012407420800c0200c8603030055200b01881d40e02d420028488900304100110341000a04089801100325034020900359 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 270725953 1250 270724703 270724709
    0x20c040c05031005040203011211030a060e210301050112090606050622080607051b0703120302190e0f010c06060911030402101b110d0506011509081501031e0507 71
    0x700341c000040001941da9041448081c0c001241c0460965040030031640d0003800d1403000610380540c1482507402035a00308500800320342c1c040002c0c800401250400d0383c50b8a061700b8034443d441511a1680004400301055a040c1c80060303403141c640303510100182e00a001028030030340f1055500d00c400701d4143c40c0c034030081c0030f401e40c040701d000c05040c011200b074001d004541d070210301c00f500071310240b14005038440111001c080616070101450003c0d25005810a0f14580c00140304000c0740c1c84501429030580c001e460901001c4001590301251604180c49040c120444168090901c1350030940660180c0c820500240c0039400000c0c0c0356490355201d0303080b00c007001d10031500170b0000300c208401c40c81c1814400821800340c0c54011400c100740c0e07401341e444001c241d20060105400310f03c030440b65260b03120300c06516908101266055659510004c101003030141c20b410005000d00380c0450b41d0a40000e40c8104102e000d0030035840f0f0b0380b0715140c00160705144c20845154000a12179840801e00811001010b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 270727203 1250 270725953 270725957
    0xc02040e070e0129030c030603100f1b0201050405070504050c09030f030403020f010203040303080a11072102010b0102070803030c030c040f0b03060915030606010e280f080102070b0115020c040c 85
    0x2c19418445040d00d250b001a5842d011541446070450822400d0816240c00c00a078100c0a80c4070b4550100180c1030017400c141c4483d010b4507220030038004e00b2054025000f8003903010842980e000001d4030407401e03a1400c17a4040e11903400301e88200298102644915804005548810309000740d1200183c14030035840c00040655101250901c158075024003401103065023400110314049c515035000e00742d48001007000c0000f594540784203c0c2190b00741c04941d2003960000d00c00315049211902100c5140710140050015071074128001c0095000199400541c1e800c00000e6085680b906486006903000402d1085681418000000d50164101000f005071040c20f400a860f440c0090078400c0d4040003d1603104202c07055050748945440c08205c0a4001c4020b03e069401d400121707003c125084035074002e404a100f40c2c00c50881c003007900c2e42c0f4103e095403119601c403810b413595114100e00740c2c0034041010b40030328001030040185090310348c41c0c000410b085006880c3d01c0303069080050200d922450070540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 270728453 1250 270727203 270727229
    0x106030c0f0e160e010210061d09072303071a0a0807020c0a0e04061d0705040e01020f040e1e01260a050304050105071401060603020c0d0c030c030c02040e07 69
    0x400c40e15550040c501070040640825110f15240740b031203003c2607280d403103032007070020b61903110301507910900c007214210103031050600c0080ea03162142440261055404948441243d0204010007030100c2c002d000c90344101140c0c1c46078030560700790340303100708002c60304d207902d0300c2250000070701701d80c901c0c1001ca1030035260320350f1580b103d6401c00040e060100040800d0119003203520140c031720359101041c68099620701003a924007a901d40c034008000304030340c5825090b850050704008240841c0000d010050310000c2d1018440b007141d580c00300d0700340c2c0070304000340000b50000d100074000d0031500104036500400010040c4221001031019016041c0c0c00e800c04480d10101c4000358900c05140000c1040c0c0b030122100511403c48142c44054881c0103030301030141001030000e40f41081c0b00c11404c0e400e040c1241d82d00200142a581c80300135000350b00c051b03071540480c0180d604100107a8003a040b02010160036480c0c00c03112840a69003180d100703a100030b00b04c2c0c1c020b07075501000400d000204540341c01f42c05480300c801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 270729703 1250 270728453 270728459
    0x7060e0f0907020a1b0803070314090d060204060e030a080f0304051203100914091c0908030c01050105091e01060e060f120114060a0219030203090d0b0a1b0c110102030c0106030c 78
    0x40e1548400c01202c1180f900e8400c1c08100d106d00010032180440c1d01860306207000c0081c115a03034524407402e0141a40001050019800c0c016aa4028402c40d000ea889a00c882002d55041c140c4400c01400094a82d00781400020004028138008581c00381c418404d454141d1848541d9122940050700c804500b01c450072028083c0c4921032040d00b00d00a08a1403109540c9800f24059a035070300381e0b021140400c4a191888400706004080c00000f40c480312040d01d884480954245000b01000d00c10540300d4002040800c902807421400007031071540c11008400640c2c02c200c4c0549020029070212078000d03504000001400b40100c0240031800c10020700b03040194900b10360107201c4030700b81c1c4680e0706c14981003108182ca40d8000801c200280d60b000c0304110095054141a400e60040b90b104d070b03801118214851040101288005106006205041201212903000100c0ca81d602c143c0e194081034101034510042211f0700b64444c1d0102d01403040300c1c940800441c0060940c0d44651080b1095801c030407085c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 270730953 1250 270729703 270729713
    0x20f180414070b1612030b06120a0c0309020303041509050d060b090a02090a03020f1305010e0106030e010c050d051b190305160e0d1403120a0f060807060e0f0907020a 73
    0x41c00200056800c4a0510320b821140f9940e904c190706005224000e40882c01d00c81c00d0281e0000e03444050018100c640700c22383c080c50384580e50b20403207401d03180c24078016000d41c46074045d01c50010b966802800450400d410000b50880b07110440031204103103c00c4541c0058256038602c0d25003140c07446401c01080c011541c0c82800f0b24002c02400e1010202c1c01800003c141d03880b081c882c10100d039012076003914036807100008501164401c0121602e07a60815001190150180881c0d0703040700c1166800304501002000c055080726861650711000541c100036020121300c02d82c02194000d14a00307480300710b18503000c40000150b80020201c1501003030540607000038a400d48965617020340301c0b00081555503000e88004000d0490141c0345486090031640d00350500c0307041c055941070f4003801401c50340d5031110985c1c0c2210815088481c111140d080c080032121b5908640100c07000c4403a00b80c0181006410503a003550181031a80c2916004001c2e40640d00350b5070780311040180200e02179006420020a0b43c10b00b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 270732203 1250 270730953 270730963
    0x204050405060f090c0708160c08190c06140d090308010504060e0108061b07051b1201020c07050603130b010b0706062102010302130e090c011218020f180414 69
    0x889201d40d03c15010407125484007070149501000c080095503076042c80b8903107214075000c0e01c01c000d1394030761000c002c580400107403410810681d03810100311610b6900c16071448003013030300e0040001d1100c00d69150810145000b03911034104002c05442c007034209042044070400300d5415580c15400208907000401c2242090322940340a401010603031422076044c500c8003507881102615518020314240840352040c0e103032009a13024943c2c07007400d07121040c11903e04219a100100a81031045030307040c1e0081a2407005108440c0b040c9061030160103124602800c0100c1038000500101d14540040002c6000611070b00540f07011b010039804650301d840260074024100c4109802c250085440b84c4100400b00030100e06054074268240307405a545c01c0380e4880c580d406801540700d804050000c0c81800250100801c8080300c014003aa9007843e107014588a80c025204104103039140d400050450f0b40140c00c00e00e450401f0b03a1000381c081d0001c640d0700c44214103031010480b0142d65901500347c04000132082400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 270733453 1250 270732203 270732211
    0x105041101090b1b0a02060408030c28030e130c030f0b011106130314030c0a0e0a06090b030619060f1101020a0f120b03010606110c03010e0a080a1103030a0204050405 73
    0x10388000a141401c0e0b4403a50f521841804030541c20310000c0901540600704848051164090901030300d440c2c0e50380180b03a603600b003059803d1480c01194005500001d034404040544042403083c05a2417016480980e001c8015680760b640020f80f1802c01045a0002e0080ca0b04401c8071380c0d00016149000030f8442c1c112a45584901e04001c0c01c50305045c13120740006840c58000c121810f40c0040002eaa16050701e642100f00c006c4601c83e47c1c0401000680e218500203002020115240e81103807192403410050b0340c0d480d034003030440442d00c80e2030144129048240a558000703409030401c440c80b142e600080034041001d501000002c0e11040b0014801035002d8135654101c00c4150007075040014a000241a103042042d44000304036500e495080700d044207410002030703008040d000300704060719120010031080b074101c00d420003449104980000d5060510900d20202010005000da14a444d91a81503a61010810710104070b502d07a45842103180600042d4003603e5440301c01a500d515100c02c0c04140c401c014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 270734703 1250 270733453 270733457
    0x1050a05150a02010b031009051b030316050c030601171501060503150118090218030313030b06010507060e030405150903250f1d09030703051210170105041101 70
    0x2804120648400e200100c42004500744203489a4402904a00400c900280c81da4144505500c480c001d940c0c952102c0f9016000e40e054400b81c50400d250301c10302460580c1e035660154020422460700811104a001034548a01c3c10f0b03400781d6000f40c0000740391003400c2e000103c849912040b0114460350411240b110350a13009041c1156624150024001d408018041c1c40e651013001d05d0160729030710428903500074032540ca100a44d55500c40f1140002908156810280b010052a00a000d85070000585920404100700c4c54021402d41d0754003060343d040981a00d041c410700748003440020390725014804541c2c2c038090007952268540402c104088585100500c00c2e00c80412002c0002e89000c0b03402500d50003080e02c2900d0744224081c1c006000700c00b5a00a02d4440e0f12920045207441c0162aa501c0a80310740002d1000391300d842686540301d01c22940300a0214008226481d007d010341120035620a60164079000d40968030b01c603443d84120700803018907041e50340c0d8042004000440343d440c01f0128085c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 270735953 1250 270734703 270734719
    0x311040f02190e031c0309080f180109060c02033c0f0c0604050f01082502100b0303030f24040903020c03060a060807090e071703040801050105011d040e01090b090a0b0105 75
    0xd142a030f904014400303c02c03400c054881e41301f0310610030b8000c1150705605603641d070207540b801480d61880301020040d02d0140042c10005000038610302c50206003014580083c045d01c6d40a0140004a2880004605d045880307692545221803220708414940c03000c017540c0b00580b91000c210020380d81032018481010707114010620050103246c44690415100200030f00f004400c988403813030b412050f401c40000010320700c4090b007101510958003054880350400c0070141480000c0200c000c0540300d004c1120441d0f04907003403000080f40c0b81035500c4160011108110210650940c80f0049020f407809140240c015a200c06408c400c5410100f01c050360091001d40d0070407800f800c010025440e15514460100e80c252918500503c1200a002810040a04840c41c1c003517044404002910391700940f003405403652a002c00008d055000300495048030888145440c00060b1050170440203040360464114030359641d40c1c0f04c4002034000e40c026030090780c0020040c41102110302c1c00a03484001604030364000c18034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 270737203 1250 270735953 270735973
    0x114010e04060506121b190303021906020f03010b03070e040506060405041104050301140105010f0306080a120c0f0303061a04050607030c03020a0b0f040605090a020a0311040f02190e03 81
    0x440d00c040c5401940c40305022695481d1880000c640864404500b0310310702903082c0c9050300940042c2c102048800590f495000c0145418628031051160312000d0090381026016107c480c054001d400c450b58411080103040020043d004086ca4000340c21002060714004140011580c20144007070b02e80001312000c1c845898210302048903402148511401180c031000d0a030344e4600e245065070f001c2e04001e0000c001001c05580c043c04410f100781329941c042421441d005410500c02c1c05907005075503100c002030000503c1580d841441901290041c0b04001880014030006085040b142030316078025580410070b50b0034040100304140703403980248500c0314100000c00c87c9460302c00c01d5581a507090f0421460031a600c0c01e0580c00d1005281d030003404000f07010100318000c02c0c400342e014066401480c00b04003e646014078541e40306101030303020b5032000207120208000f4034007100e03912820354003805c00b0400c071144d8443c500980c0c200c60441441c01c0e403000c148803803080c0d00108901855800310010456268 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 270738453 1250 270737203 270737219
    0x3050c30061e0103050a0905030c0303041e170f07080a0908010c05040f03080c0708101b0f171f290703080417070b0a02071407270603080f03010305011401 68
    0x1400b03034514149a10303900001d03898030055205080325900907058a0b92140030305810398503540101e030100d0300c1c40c0044104504003040c101c284c406d401e42c04513103100c1c50b02d0041210560f5401c01c1c4490150321500300b0000e00007460600c003809101100b511062402030402c2d141c00e0a444905414000700842404104415400f03a1000c00440380c001905994038402c82d0075440c100080b641254181d849040050342000c91160f000500b907041c04048444e079000018412240610401070500010700c920a5040c24401040c03c0f964020440f201a00616a2030904051580c00c1603409000807061280071000d520008a44500740715540d13040340d516080c1e8569000e45140c80c00f5102074150500c2c40344191072549110201d40c42e0b01d800c80b50f2900980b80401e2000080e40c41504122007044568600307040c9118005411415150441094200052079a8610ac40d071070382c030040b5085841c1c441e0000404101c0c40c1000f04400b40e14440c0450792503040d41030003801d446d15407544030000d5080200401c0110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 270739703 1250 270738453 270738499
    0x3020a120224040804030501110726041413111b0303132006030a020705190305091903021201150602060c040303030c050702091014040e0a0303050c3006 67
    0x10b80c154110800035111400c0c400d5a0b4003858000400745c1d840c205101180890b12409085540d01c2100d0324500d2072088214050380c0c042c5e80b2030366449080d090105000040070f111200d0103c0c040502512240c030041714100060300c0c48401ca80c8035007240000c2c5a84048102e110001c100c0381210020351079030a0500c4894003d0705094009001cfc00a04400c2d10803801400d07221940c0c82c000209001c5e22400c0941c101c000030752002c2030440d0076108480c4854000341514041c54030311758158031030a041410300b400b4466034804650300040d420312044008001a0340f82240500c501000a0000454414646a19048200c07a0f000b030000d542c00b080070090a40c03401c20844c1c041d2a414034007c01d40741101c140036505400340e40703002948104000108036050f5100c03041001150407582200d420204201f0910040700d000000c100c0341c5801c07a41d1048007280c000d8000d2074111001c25916460181034100b040445080308070a50030040c0b100307246030000100182c40300e0b001071b030071510010701c40d48405106003c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 270740953 1250 270739703 270739753
    0x204090b3112050310090e16060809060a050604090203010609020a0f11121b030d0c08060415030b060604050d03051e091e1306030c08100b0a03030c0204021603020a1202 74
    0x4040040000e96101d21103422a009010f00c1c1c06c1030042044003562079840f280d40003000c625500c1c41c0740000400510a8400c14018030045010b01016280d0324802c60140100410054210361960240001030b1401d00c0754078000d102d030140058450700080c00041541c01200d030342004000c2c0c542d00c507400ca010b002c00c4d040d0040d00b007030141503070712104002140b249110200340407100340808589100d03200120380042484003230f070391b8550401c0d40d5210100800c80360254801200d41c0c007195028070000c0c0c0074180164100ca002001e417400c1c0740e5603000144d07410580300030480c0040c0700880c0b40301600040d02c3d0f0756810b00c40070360000c0342040c0c0a80c01040c0b601d01100321101a2421681d10003081c0d0322006800520300b0f668480500c6503540b07038200980549030768802c0400ca80300f0030844041c1902c03d48284800c4031002003102c1d501a01e0350306d04940001320b200040e039200b51300700003500441c01204c4409a415103e60040c04804c0351508085d02026060190710080d904074049482481011980d5031401c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 270742203 1250 270740953 270740957
    0x201300509011e150306050408030f070f0203070201050904060b04030c15021c05130f08150c04030c121106030f070314071b0c03050f0610060320070204090b3112 71
    0xc24004400040d1381c142e1203a101410043c54001070109000d003950040d8400e10039510410211344030040112103102c0c60552903030043e0420321660f0300543c462401080051380c02000401d2654a43e035019801d0344c881e0340112007003801c91000704000c0e002212401c800d1301c007034006411194003111814410383c510180c240208140003522448082c080c0111801400310318044100f011748407070084c4d60780c01084116040d070701d01000014030301c002e20310202c40c240c07548480c0c04030740107140c19440840300703c040b04215100810b255401901c1d48507180070b540303d4080d02c80300c00528100110050225008444d030035003050b071442c00b000705642d0018001801000402c4808060211030304001c0d41589190b04018040c0c083c00150f001c030981c2c00141c4c00c2c003480102c800c000205945940c268120f94904000401d00041400c0761801c0005960190012500246c00810725409507070f00c00580304e0040310647e080301900d0a11070741e244640641d4081500d40030b41a441503007030300d84134075003a03524407068281 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 270743453 1250 270742203 270742211
    0x1e180b0307170d031805070602060702190c0302060a021207030e0a08010b010e090a020d0e0a061113150e04020a08041b0509040b0406110c0607080a06140108040201300509011e 77
    0x280c1450a04685c0f40b8203504103007075034105030b00c40344001d4942109844100052240c0c4070900c10f05526905001d0060f0750250204612614550034491260820380050007940543c2030b2060081c11480001d0254074400e42c0d41030345265203007042004c500c00b5504004082d80c075081c2010320b0380c0d8204070490fa00b90021140c00001e40d0300d00003410040d110301841900024140000c0704031141c030000e803062039180f18000500864140301401c10031406030541c420103c441481c403c2081918182544000464034a00b44000c42041170200f410381e40001108400034121004102c00e201c0d4020b000d4041e4240d181300c800c8100d107030400180f9201d001800242c550001c80340490200309055005200300e45c801742d001510307020301d101c10381e072a19412501880420803000000e0b5461a80703114080a44140c3e40106075059200401111901e030300030b108034103201101e038255500005003903d041c810f602d40c003c10401c07036841d0401032003a108042e11140300d9a0408082020b01c1e00b20407108100380080c098002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 270744703 1250 270743453 270743471
    0x31602040f06030b06040e060402031f060b0f0c0105060609100503060d0c0807090608010203040803040303091401020f130b13050904111e010f09050a1e180b0307170d03 74
    0xc0c00400485404104007882d01000200304000e007803400d441600110350800000f0742c949803150301c1c0c01045400a625801941a0403400000e080410804802007040011400e0300d620480619078890740c0d81f08000203020500382c84418090141c0c40e400b140c00e41d0160708086081011850302c4000103019401d1000100c001000d5850704a260b6000c82d0308995541d162681d580710941d00c605c01c5000700102c0074201503000c00c6041050080380d024661100c0da052560f6100d40741140100b201840480303021441c802c40d800103800c01d001400042200310a0590380e00951425038042c0886507000f040215428440503843c121860000c00c1195000d40b210205030340c0e140307480304100052006483c2e0100c0c13a00d2088442c40519018041101002e88965a11500184090354181218801c1584c411000038051240d201d83c00c83c08510a089002510400f40d282c01e40b0002480c1c0034505480420b039100703603200b40380c502042810001d0221a090940003140c1a01503500c980c0c0205003041410f899030440c2e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 270745953 1250 270744703 270744709
    0x9100602070b07032a021c020a0306270507060e0109050a1e0f030302070608011e031101050903030c06100e1905060a36020f03040b0a09170715050702031602 69
    0x48006074421117442101c10214401c40341100c504003810f0380541240c8500290070003000d101074416071740080440c1000c601d503541c2c010203001038041400ac0f40060095403018102101c008991992141001e0000380d07052040061202c4500b0180b94100424107200304200d8440b072076090243c409510040070485540c00024611030801d0b4010102180113010010a1607800b02c0c96809486081c0c0c1ea04280e0b0340d0b41d42050441180104104069146030401000041c2e00503040d05481c050604110782400c0180001904541218040391000d070031041c100708241c0070104c4040c0181c100d0800030403160030400c980309070781c55011044151082d502c4000c140035954240480c4000c00e101540703440055290707901e00c400030070390703100741940a841855110211042c41c02030b161404580c69200b03081d9a150317160b0b0703020700300d000d000c1c403071415030f208032201c045646088007081c1c4803142d006150b1350754007514004c0314650704e201180c61f004e45030906210a90f40d01201312555080300720400e1441039124000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 270747203 1250 270745953 270745967
    0x10327050f0601150f030621051f1401060305071d2d010e01030b10080c09150c16050a18140901061d060114070809150909100602070b0703 61
    0x2044a0303902c074150001510013503a03641c2100c2e29000383d941e0124414101c5042c0c040e91028010400c50ba008050f00b107201841041c1e03021030241c000c00c100c5401d48011114517550000b2a0804040c0315120720f401c09100d01d60f5074a080c0108024a010400ba02d40118018405801038095501042a00542030999a500440b003171000c0b80050408030303400010b0300700705004c0520300081400724008030504c3c405c542c001d00c2500840c4001500301003403a8910312040320600300042c0340314000c2400f41301d0020b40e80c6900e01100d03071051035405074554030f0304000c84540c42c01c00fa82070501d41c1e0040b074540500c1135440b0b44d50f020084850125031885005d02400404001c1c2218090403591f955006081000c2c542054201c40304403a060752046403111000208048c5a201c1141c00d0781c08505643c1d08818500810001446801c0c02a00390508008908000600c1803282d84212304559071f01291001c8546815192690080940320805041e1072814201035102d00c2d103442007a541001c0030403100c00741801041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 270748453 1250 270747203 270747223
    0xc03040302070e070e0906030f250f060509012309210d020c01090b070b060609130501030b100806060a06030c02070302090f090d050a051e070b070806090601032705 72
    0x760343d0325245400c14004241d81ca8180c0b4441c418404500402c0c00c80c10041035114840340c4890160042c1078045400060444560a003091501000e2038001a00401c0c0f0b49031801610303c6507070b0300b0b58404d4902c00040007511003080c040462078a00c244917600c40740407800c454200c40300352080b01a00030410021000d1094900c182d04d130741e021399081c94104550205807252400401d0301c41c0880350381c03181071a4915006000d0b008160341e2621000c14101c1c0341541c0a080040c0d03000b00303a81e00013003d41c07040310141c070000c0e44120b841c20040e2003444034290150f80b5903005821581e000b000c0600d448000507910458500c101000c4c9591403d801c0f0400340f01f0b02800700995005044500c05080c840003d18084500b1a00300200d070103001d4114038820b101c0e60460320455000e47e52035081c652808081960401e00c001040ca4944003000120002010b40c680184200c11944070704006240c003030140600300c81c00910080c10549820845c8404180040d0b102c00c0e00310b440902402c0040b42d40c030303081c0d152601c812 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 270749703 1250 270748453 270748469
    0x4030204021b010e0a050604060e07030c0b1206010e1e06040f030302100c02010c02070608101a03041208160e031203010e09150606070f06060b13080714090c0304030207 74
    0x703100510010180807402e07640e56120001c02008865040c503649441d40d0714401800c0c0d800c014085404075065403c000c018850030b600f682c1d982a030320359030302140d159164082c90f14403202045403402d15450a1600e54001d40a08282c80400d40880000d21035014240c030100302004412411280c1d0b840f044189c401a01c80300b0101002035449080c0a5912520b82e2010726240781004003142e11a84180221301e80c0001640091042c0350030000e0070b0703074046001010300141a6510900040304c209905941480080040d641542d9013030030b040150501e054244881c00b03000c40882800510f0240003410440c081c01780c500285482940307400079041200301a6841c644180101c0081009038000c041c00b400780b103035007048485441699401e8255004125042076001c80d043c0040b10101d1902074108041074481c000c0029000d4540170701c02c42c40d41010b000303140e08200f4001c05000001c002c214040140202400d0030004010380c4000407102031002b00f0032a0445008008282018000c00c4040d025000c00b07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 270750953 1250 270749703 270749707
    0x1032d080c03040e150f090a09051c0e03010e060a0f02070f2301050f010911070c240305010b0d090201021005040f170324032e060f06090315020403020402 68
    0x1100c1c10941e42e801030b0044005001090740854050b942142009010881c0500b81e0307a030021400040044250f03000b05040d0b94503880c0c0e0008000a1400d0140070000d40c2400d02400c0141c5034150000d00400c425900c0a0003070307260040c0e050100000040255110040380000300c2e21068003c0315030080d010b00840100405800204141000501d981ea0890b002c030b00781e2112070081b50f100b4081e00f40c2c1e4080c0c529503401030103600184028041608514940106001100d103080b80c5a500d420140d01964025101d400b15000310400304a100d00170804507850300d00d07003070001e0b50404100c031a05110f03003000d08440f15038484100c0210b90081c00079411004008500708803074a41414840881c18810004030303102c1d500542e4040847c40c89078103890050091065106005043c410000d84049500304038070342c1803080c4a102444400f0024129544250b5022410703000080d03140040251092a081501e00c0c0e05195001c0c0b003140e902005201c11680c001100c99541390b030741c4154400078461500007940103400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 270752203 1250 270750953 270750967
    0x5040b180a08040905060910060509010c1103060a0b040c0f09050d032106030c091109040e28050f07080d03020d140a0b0f2b06020d050f040308010501020601032d08 72
    0x30310341c00607108220030344000100b5aa1902304640b44100d85c020080070400034803c070307260741d4806c06841c02540e214400c41e00412150740d000a190050031104511640c1e1515039800d8a4140b40c00b55641d5001c95061101c400c2e00c888501601040c5c3c036024090041890310341c20750a05101d010a2102c8a42640c9400000c00070001400098075240c0404e41d03200800200002d05880a8880c002c3c142c00907040c12410729115404010103001800803421083c847c0d0a5004a0416000010420308903520603403001400140340c118104a0441d0741c011903904005810030958001103044800840c0b0f5260043c0d440941c444d9134030042540d45010010710210710204244c644050b0b00002c1012422a0103520f0504100c0c00c001c09050042c030310764100800c40504500a201d41142021098400c1c403000d4248110342150004a40080302e40710481581403003448240350f004549503001d481c2c2840580165070450710340083c05001c91035005096030110f01040d0813180802d0540e061b4079807268026a981c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 270753453 1250 270752203 270752219
    0x10020a0f020606180106051b0f0307030e09070507120c0b0f010915050f060f070602070807170c120d0e250807050f04051009020301032405040b180a0804 67
    0x414510340d02500c51403001c901c062a000c0b07051a50300d04480002011030f03080407400c80d659001248a2007010400b0403140311402000d004104800030074200554032840a030800a0282003440b6006000c0e48015080c07081c141d51050441d020715810140c3c54034124040748017200d03411032490014110108003028080340e1052034460078100c0d4840d10061080284660000c25100341334841c841c0e0040307008244e44c1060070210090410b1050000c186401c040c03660701c80744241d80c085002196001d40000e02401007040c81d00d01c80701070048040800b07050484098843da69010340d850100218040407904c61a8801c25411200480c0c0094090300d10044000b034200c5100c1e110089980742a200000b40416940c000007141004c440c402000740c01200594070601c0002c00000c3c0c00c0040d00c020b000c03000725450440740021030003544604c07110303107886504c00c0c211031121502c1c1060305601c40c01c09003844003240d0000301d0395801c04980207010b14890700c0c034048107140c01e020b108010042074004c034000880034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 270754703 1250 270753453 270753467
    0x507030501060e030d0e1c05030d0501060219150207060906020d15140310150b03070c0614130209061c060902030606060304150b1c110102010c0509030c0105070510020a 74
    0x501c0300e48880841d44060f80415844805d01813250001800c52500c001841c585040c46030316180817041038509560b45038407190308507444803245050301511000100f00341a0304111075005e0820300c010070034400760b02c3d55555214851800c0b00c0c2040c1900401e81d4000e014165204684065000d10115074444006801d0070180001c00d055065020500c40e0016088904040b10400c5400c0100a0328100c030001003804002e01c109000d071200340c07042e82c2c404144520404020b60080099469850f0416110324006050311512a951020380040d4000c0c40204420015051a0960b048801c00a8ada0b240c3d4007084007122110a803001d4200c100740c460082c05225405500303003034025000d40d80d4135600c51013030201f10311040c3c070300801c1d40c0c801c0004e07d50420b000d54481c0749031390b900500840104c508000b0101c00192000030070f44218a4540c1c586039035680910400700c8151460400174140b10080c000251074030821010a4140700d00010480200001849414000c01c1c42440840d1201a41c8500404d09 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 270755953 1250 270754703 270754709
    0x2030d0f1d01051009021305060708070609051608070e01030221030d020909090102040503060c07030e09040b070e0406050f1507060905060708010b07051905030c06010b0901030c09030b01051011010507030501 91
    0x1401c4401012442903407174000c80c1c1080300c1f011035610a041c0350000f4092568840301c010784181906010140003d10303240208646107003e8070040c1070103c8118401e60300201340d40d03c0018240c1c8100810401c03039601400e09070440c0d804491020b41c01c5148020f0507100481d01300340441f0381c000026882c5030640700b680a00f404540c150383c50390382c0d95948072101d4201d01c5540242541030340f0030000201c241ca42d0000400300d5038480d24243c44500c0307403031000c034220500c1a101100c00d92018420081c1003648415030440c001d100701c4081c440c044c544004980e1901e008441603014103a0801404442114081101c40391544024100440f103000c3c20041d40301d207400c8d542100092281e0000103955407500701540c40240d0030102070000300d4681d41103070f5204042c5540440c0c0310300042c04803440d910b0003400707064024580a40c20315a0342c080080010100c8055840c0701041c420f20390004c0c004640c902c01c00070b0640c0e0094803800c13080d203180e203800e803a031803200c4000181e00c2d800d260411050b1941a0051412 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 270757203 1250 270755953 270755971
    0x90a020c0706050c15060d02040905120d092904021003020412050304030317012102130903030b011806020a11150a03020a020d2d12020c06040507090c02030d0f1d0105 73
    0x45d5031030001c0001c04042d10b001b5801501020000701514140c0d10100000340324000316080074a00d94054036054009010032031415945401c0390040c400c03080d1100c3c2500c0c0c0c3c045528a2080442401d41c5e605070300c040c201a024961041085a4aa0180d4100d4000d03001c820b030102c0b40310780186402d44c1c0e80c1d8083e010440000304914148483c0700100d480c007a058a440c120340000c080b4042d80d030003a020481d5101680d00c003490725041031140c0c0b020b2083c0c91070039001365000304011401100160500fa25450a6000e0a4001504115442c0d010a99912080e8050309540303024441c2000641400540f841181418000092140300c1641690080c448400f180e003d40e0300c00302c2c02c503d056441ca04040e481403414000b8030346500c81890300038120a4140c0040c10408522040c0030540001ca8201c201c000000354086030a0000340841001484002e19200c00b09001100c078205000303450703014020031000e001c0c0d1104200502e10809410040f1503000b80460f034202c00090010150103048103a03400b00c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 270758453 1250 270757203 270757213
    0x3030203121f0b0316050306150703050405360601050a030b0a0b030907030506061512090703140c03010f02090d03110c09040c050418080301060f090503030d09050f030a0e090a020c0706050c 83
    0x30a060040301500d208d944028194080e003102a8035540c1711713500c5850101c041100410001c1880d40d0343c0e005089411500780007007042d0014800d00318001501c40845028891664001c01103107a83c400704030b40002c0c00501e0701040d441002c40c01300c2c4015200744c002d01031000c404000c00c803180500081120031240160102d4206803110b4040c85105070602c2c400c04c0c2c60750404c2107803403040c240950318160003090720b0040307400d4035a90703403203400c0d84520f60490b40364250007900c030b4000640740901420b4003441003580110300d40a420000078084440a110007410701052400c5003800030b40904c0481805071014000c11034903e07152409100192550140c03d20981c07810844420031380d8007003100b8501f290b003c143c4a146034240b500c00d503580301881842c0e1041002c00b16001c207050b24244041c0500c0d03000d0a03c041408806482c00f40d040902ca506500a9580709221411143e64046040e1201244c15182d100f9182c481540900c0641700d80c0041440702d00c100000081d016511200401c44041d40c0400d0b10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 270759703 1250 270758453 270758491
    0x309010815010503010303140c070801020d0c0914090c0412050303070306211b03050a05010e06071d09060f0301020c160f26031608210103030203121f0b03 68
    0x1000399000e115002d001807403e000520010703014030a45101400c44c80012403c0c010303c0500140317407050030707004001c099401042034038918107640140c000000b120f0800d51310150501c6010700c407c58445403440e2045029401240111070882e0440d00030741000d1000301034050190401c00e0b981d620075200341c80020f14020700081d00c240315041d419111280460002c2c1c00400035203c1c1072800115210704403512500050020008008110300152103118400100e8042c118007402c1e41400c02c0203110906000f085583d0043c40c190b16400e540d10440c08441d14007031a202d407808600c008050700e4415405610010f10301c45003060000ea952507200200020b86d851503214408520f046d03080b131064444852036610000c6140c5e020280d983e190307d244d00304684c10142580c0e5032900040d003c10007a2248440020421700860008040c03843d0924400036030391643d45035940095880c07003034101c003039010401800403a0456105250103078980003c024506c0c0f046444640c1d2a0682c0e10035a550501455a00c01103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 270760953 1250 270759703 270759721
    0xe03340510020418020304051c09120302100b0102190b04060f0603500c0a03081c06060914010c02130c0e09010302090402220c030903020d021203010603110f040803090108 75
    0x507441582c0c07020291074100030400720501c27140030f03060501d1305000c0c100002003000880700b0114111140607a008203001a810241d01040b690040140c034119000802c0070380700c40420850a080195004401f401c2980e00c60030007000a250300b04440d0350050502100205021820340c201c0c03207081e00002c920141d01410a0340f6400100c6402c445280050400d40d030389584000035041401e851910400c0da180030381c99034005448580f0941003110b6800010820049085c041040c11802c6000d11504000e20350828401034020340303d0344150001120700a14603032142e44103d10001e80554040c08007007400c08845443e1002c2c00000d030b06000007442c4803c2d46540c40c6801040c2078100c9402404c2c0d100710f0b842d47e40034040440d00e500c10308280c140d610172424804261900c102ca5000300c0e50f55000506074114607000b4140116008920110344c01044001113025000e070440381110030605001529400c00727502c0c09150702030504124841c101c0424000b40514022004129000e826a02c501056442c0415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 270762203 1250 270760953 270760957
    0x51e0307200c0906040209131506080c0f04031103011d010501180b060403030f02031b01090320100b030a02091e0105030304060f0302030a06030b04050a02040e0334051002041802 78
    0x140c242d103c1d07031490104070181000c4d4010200304201400d00c1625003801140034081d590624400800c0c0b00d01c150040054030f90040c40c075504564144201072401c0381084480d48140940d000140c200b4100303046d407082950302544035500c00c0c205901480312049030b4508190007410244100c0700e1130f4584034040b09000c0e01c68882d0718202c00c07001f0003081c20720f400c5480450381d07400c0c03981d140c00651104018001006882a424a50850446001042004952030002c100b000c5403d09504107402c81d03a4402c041c050f000c0b40412299a00d1440007a000d8140e00c000791030180c030500082d4201c1001d0341480fa4101020903455903905840d4484032451340d84505066583c4a07030b00c2150006800701d103d2107807280c42a001580c1011103184003140702d6031292102955050160b600700c51b1580710403001c4046052501800d0b40340005000039509140c070307031401c040390914450100c1a42a44211a11304c01c103201c604000c0c4220703001030407501c0c0b016248240300000c1d845030281d64152000541100100036a07402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 270763453 1250 270762203 270762223
    0x6031a10080a0302070e0c210402012303150f0d1406073912111002040530030c16080606011205041406070201020d0b0904050d051e030720 61
    0x3006100481c0703070203030450131600007401200340018104400c000d10030700d191000e01da103808d0484014141c24540b001600c001401240044103000006601d141c5400c103001340c031f500121020b044034003000c40300006021a054001d85a9104d0b81e07005038139040c089024900306008450030110364254803a440260b900d4140c440c1c000100790040c5400701d1900b03121030301c1c1c0ba882640709210311480701e400e699512900400d190b2032000150301070000c11860241000300710082801100c0441c5403506102c04103210b20280c8540a0701d03015240412038464141609130780c24079440e83c050380d44842810010b03e80341e209035000c009001003181000300d040c01022030114041c0380305841d01c40c0c2003100d00c40c43d84041c0800400550702c0c01000e204003108210180303c51849810f15500042c1d5030584400b1040440d0a621346050007220750004000028400140d110300781d9586007807241d1100b140c2c2c201049841c00707242d03a400110388040240314004e03420200c03030001d580b05051007603101d62410200607507600b5485 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 270764703 1250 270763453 270763457
    0x5030a05071707080709020901022a061804061d01151d030c09010308031905010e040f020a0f0f030c09140a02160501110c060f07050a1206031a10080a03 67
    0x59410000707480c030348454444901040c403d944441c1e0362040c0080c14580c2590094400f5500010610150340c0c1c1801569035204400f00d03690660000100d2121031041c4450003113005050004032141080c1040031283e05c200001031090010300d4a806500120b00059000a480102484004210b1500d00d081240500d200c40e5221050425154038140316441500c20701c44d01401340c3c20050100d500c4004046010b07500540981e0358078200f101c1c246805110703010b21200c9291a140c014065180402803070740e0010f81020f5100701e4010b0301e00000f0390181c80c0e0f900c103d0020754450030005141c09224084411240210402045143d503150b500040d90180c14031122040e01c01000209140226406070982d00614203c614507401650340d42400c5400d60940780710249800b042c1036400003410800b1691103400c1203002c028605280d04050f00500604102409100424644803080c4141e81c1c0080020740c8c1001c16050120b5014224071035480050300c1d075940350118101c01241280000411041c2d0560503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 270765953 1250 270764703 270764713
    0x30c0302032a010f09090504053007020f180907260d0c14030a02070306060f0501020706080c09060a0507050f06060604030b0a06051009061d2b050303070c06050105030a05 75
    0x82d03004580d0b11a031040144140040103c0105000c4241d00c0348500c6548580014001610355280d0000c00c20f00541a410001c0086020280c0701d001c0c038001d40d02120f6060b19030200d01603185002412480018070340e02e40006103042008010b200c00a450301c00c41d800c01150343c0d215030340d01c1110300180c8088180f2600c207900c2640d0190107517105000d01414240039010200702031490303800c6141194810140d0400507031040da000e200313200c01407084d40002c101190600300d290345001e0001c0c0d01d5807810b1096000740602c190000e48207401d0364088810040006065503500c001c0c103080a09607400c02c4000b9510361041c1d03410800038550010368230707019580027441c0a0130310303103195104403034000002d010800e9162942d4000820ba2a40c1b4007030400d403095a1a200342c030342c1c00c01100506441440e16450149030741c07164001110780315082c00640c42c000000306c1101200210458000850f070307048008041e44400002c00c440b00d54480051140300748139200a005590344c54040543e540c0490501515607004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 270767203 1250 270765953 270766033
    0xf031202040f0b1e04060306030c1502061b070501060902040311030c030601051e03010507020624011b05030c1204090c02060c3903070308060123130b0301030c030203 73
    0x50301d40940b503051440402c0c681071075504ca02020b45600700394009000301c0c1e220030080c410060420340350300240000d07140011103814041d400035030710040545a00010600c149a60b6140070800c0e080300e4034690004020f1029958038a03011009501601c4169509091604c00180c035180108062000f848018001c1c00d090b401c040070003080182c940301d040350601554003568282d0b1420b02039240326540d03c0d0007800043c0b07004a2401100708401c0782480344001000746500d22030b03030800d07445a8a07400c2c0108901c04008a89005448e500c1003d42c6410540310344050304251001420087c0b05a0380106010b20800e16070703030ba041c0ea9400003541c0101405e1414400d40388058103007441040304003018849044208210b0200c0c0d501c0400d8006503c2c02c40c0c20014008044c10780014946030414030030310b401c458606001c0f0f204980d415540307210f5246403000040f800b0481e048110187d0242c0721460303c0541e00c0d40e41b85090007414406100803406809100e503440c10410301c54507807114a2900c0000840c204d94 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 270768453 1250 270767203 270767219
    0xa02161502070f060614180f040c0b1602031606020a020f0301180b070201050112020916120f0906110a0c1707080f090102070510120b060c0a0f031202040f 68
    0x21001450305aa081c40741a000c100c8462000c0500d43c004c9030f00180300350404005900d0b520050700c80c075000e500000c08004080b103460118503805031040d000a2103070b842da464039201d800c0c1079a021807040d290101c0c00c00d80283e014001c06100342d1080301121305181c400750b9038540000562042c0005604100b8011003d41811089014100c1d0028000101070700c0031042c1862040c20008140d82900f00c01d001c200c01940c0900c1114054103c281c4042003d03801e650010f40d81c0b500080840420005044038905400d0044071442c0018506031300c01d01224409401500050980003400e5134054241410071030403801c40d1040300c2c4030310484d0361032840001464503500c070340034445d00c6a0700c5030150030417281c80807a00f098082c1c050059240301480d035402e0f0000c00207103440503a40055224903490b04000c03105035040001400c6c14034a100c000329194102400241c050b005a0f6100301301802226000c10030040a804103414044c8603445181c401c031652082e1804030b028a004440010300340143c2404022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 270769703 1250 270768453 270768473
    0x924041107020d0b01031406011401050d09440702011103070f0f140714040b030c0316030309060806060901030504230d03060801020906070b06011b1101080a0216 71
    0x561034611040c0741c100c081c1d01103071103880c101c1000d48080003c0d200510401c240d082a01182c1c18030744c0020b01c529410001c0018002c4042074840303050000014a01ea00d001c9185c0190115a0f0044c00c95052000d00c510030740c00c032101c000e409019552100340410840306074100d4078909420540030550402143d64015540343c21180070800d00c2d07110034030050000881c0b6040c1650030340d12441e8880b20503c1035160030000c0c400340381c80c03410030b41d00217032000c3c042032004540406402c075040390301041030850000444d00b0588010308240d00f60041600515500008181900c1141d100e552148080c55403a281103a8244043e212940e1202c410407410b45550b1081d004650814051644c0e285110f031004083c0810400c1c411002d102a0080b00800340441e805200360320040071010000e5242c210100c001905c14031581c00c0007440340d0040004900c407a4490100c104005000554490031441c5500340140d102010781d2065001030003120007d10714550300c0c02941e078107203030300f549031444284942e40b45aa61 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 270770953 1250 270769703 270769721
    0x110d05030c0d0905011d0906090a02070204110307090f180c0314040f0203071a0d020307090e0708061905010203031612020f030108010c090f03030e010e040911092404 73
    0x29100a1010407400c25050108401c1c4110980b642d5580501e00800507264035441002144000c09066407015030352120307880c40d40c0c8001d08890381101541c03020144402801075070406500300d454040c02440260502c1c00443c0901c83d80c5e121644c8031a550103202c0910701a5020320a8001700c00c410401c0040207170703002074040350454180490303030f09081000b00c0b00c407200c1103e040c4c0c0c0100541199106600b01404807034040e014003c140c203028142c80a0ba0460780c0b0900301d544210740c2d800000140c81c05e20409085020b0070070f845043c035941c181448001c000e03540aaa10318803804017480003406060100d64480129001078002d1130459031002c0c65a14030003005030a0b8403c1c0301d042200306249007035510090200e0350003d556141c403541044001400c5440c61003186043c403084c44018080621a81c5410048940c507203080ca00c2841342a004990740c0440001c001c2c1c229050644000810200c074910040400056a151203240e80340d446c00c0d14400c00c903450701d48407414045074182203414550024021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 270772203 1250 270770953 270770963
    0xf1b0d020d030507020406080d051803030f030f01030b0121110d02090c04030b0a0608190606092a0c030905010f020a02030f1501090209130b120f0c01020c060304110d 73
    0x500101500441c0c1c40d007001140880000e000000d03020210300d4148241d0000d0103890004020160030010060800d1051202d003554401c5100207200742d550b010012190184044950300d83c80c4e041c6801c00c0061505c0a02080b58448202000803881e041d010b01214100821922a002020807684070340703540100140c0d649400c0035103543c540c405a00c502043e5800b400e0409103050f912403071820007405d0000050515408142041010004104002504552001c2001d50303c21041501e1400500030480c66001c9150703e405c20b45241034540524982d15480c10002c540b1500c4080440011191060182401000706901d94014001340d403207000785220f0706141d801241c03c4054190006454049108840342c2107a0011001c1d60a0281c1c42e05218010300102400750f08000c1c0070000100050244440c02c40003554a51010300c055030740e0500d0030b6420811400395294010702c80c80060b11903803080d03400d5002d880741091180160805804070f85c0309640102598000442403420072401480004e000da030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 270773453 1250 270772203 270772219
    0x13031a180a020906061b07081c020c0901090203070908010504030c02010906050901080c0a170f09070b0a020a06020f0d09110f0d020f0f0607021215010603050f07030c140d02070c05030f1b 82
    0x1d0f1054104114405456103400030300202c041127a091440c18404141c020842d0400a040601600c41200f1039064a2840d400943c803030303440d010100da02a06541c4881070560915052006168020f898058010f000baa00e903680941c942c8002d451a00c104807516001500280015081c2d8a046000d0300e8a42c0f55031504411041e0101800b031000d200655188032258280302c00d121030301108005450040416440650500c240c1c0312004c0d454180d00c039001f82240760000751585401d88403504640804800032030810203500582402d050008102c48894007414028100c00100d01d055031801c1116980200f5507003001c6107e40c1440440ac1022403400d030440340034414000180e4400054000b080790220003004102c1040c1105440703164181d21803000e140c9400c00f485484521f0444442d80440141000706804092002c202c6d129460040414240180400d45140790b01e481d4006001c0d8038000c01301310310100d44940030036443d100c0d50750415160703601290694a41c1e80d50080c1005400000900c410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 270774703 1250 270773453 270773497
    0xe031c050a0f0e0303041d01080607050a030c021c030f27020105070215190305150105190c06020c01021818280609020304120c021513031a180a02090606 67
    0x1900c0c54010b0741103005444441e66940f405001c7c0c210305140106a032000070a054200340e02d0161080c840d071040c140400d500c2c1c50b441d42005008111007440c00621050303c84c461442d54000030014120303100c10000f241e052404c43c24003100c141103e801d0010b1180c5060708211401e0b40151000d601002c012030304900854082c3d00c58001030f8024018851000400000841803214004c04940f0300411107031040003036220205860340d000342070f144480580070b00f40703400742c0591009a407aa440b4080040c080750001074100340414040d00030300050305d0000403d00c0014030403810400549400c960584e641983d05000074050045c0c2703152140461411000050b0f94190040c55000781d40ea20f40000c80425000004e10041000c01c2a003610a01c6503454200da0401c1c49900143c01d810225005401c40c150102c2c241c3c01140d0300000c806d00469101094151100c0054000201204115104607002d040d91810089581001c514920004c0e0f000300a81526501c00c01009402d4101d11480810051442030b06 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 270775953 1250 270774703 270774709
    0x30b04090503120f0c0304080a050928171b010c1a2d06013009030206010b0a09050103110c0a03022104050a030618120e031c050a0f0e 59
    0x8205014007400141d682c43e02c841c494492a80c0703001e0038521181200a0421400910302c0041e02e400c01d900101b41642c03510070040484460048030032103503201410001a100808002c4042406210a141d014555542d105004005203980804500a5410000031420032048185041442d0700b0141010041c490b61174940c3e4896152510840b42c0d820604000c5c012103140002c010501058540c201c600304450204a9480f4000041c3c0b40074184010b40500f45d40e40100401500c2049400404e41030a10350fa41090b90040d11045a098000d40203800000c1003064a050803502446082e0729048109890000110b0050500045600d010a828001c1981300c1034140082c0000c140a503001300b0003c0f210046600e040180b0f2324981c04c4a4a04020070007103a100e00c85d2001c12281c10550000744585288091100d00c0b5580000600c0d4054082d030304039071640c20010b0004401c1c4c041d802c0f03403140121081c1c0c19114888a00520010440500645401c1d52040e01005046a15440c00d2598801d1007004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 270777203 1250 270775953 270775961
    0x9071e020304081203010602030a0e01090b07060906050a050c030103321c36090608060108010f0b010e06030604060f0f144c0c051b0f10030b04 63
    0x50006030030004003044100d0003081131440040c00300755114990352420344040d54a1050419003028440484160541c0d0380c00780b0303504001070401c40c110302c0c1c3c0c1e480a483c221008044440c0d0843d182803410000c90b007401c0d4503110385d511a28503070000c5031959095071140c21000b2031030038a000400241e582c0d50011103042c5806032000e0b0b1162001400f41c140303d040d004032184921002c40d410409412028660f0314444000d81045038007006840d416a034075060441c07220308250308423011301030070030381c00150503a400a0120704841c100302c0200090220105030b4030540e15203185140c0050402d864528852400384000d517004200200009401903071030031a100246010b82c0309185121991030204402204080c2158098004403585d05c0c500100d004481c509045114a4403905042c1c40018641042c074130b10364848801d0303038081184030130528000052040308075980440d846e01512030001000d904502c0390f41c00c240070040c03402c442a501c5006011030118410403500801d030320742410140070f48491103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 270778453 1250 270777203 270777257
    0x120c0a18090f20090c041802091c12090e0c0319060609140411030121080c0c0406050402090d0201121d06270604080d06031520040303020c0907 63
    0x81e01910001c881c2d1a5000450340441018080d440d02800c116071505c400044070180c46071010f888090041300c511070802801049143e030f030041e00000ba84c201110307441152800c0c5900c40d90781240d56040384601165045101e1044a040313460240109036010b90100c080c590281d203009103504080071000941050b951654000004196081c1051200c401c034008082c0034908291424402d1407940000d1103010b11051241070905c0a07821b4000519001c2c1485518a01c0d8000c500c80c2d454012520385907888a00c0c0500c0144200d00d018800126410140240c83c24044d0003000141c2401c2d554005507207040384101c00404c1c0707036603481541c2030901070b00c1014a060007200e001000303203180854200100d000d51140041c94543c0c00d00400442800001c0c0140d40a0780c0003511544a04090802001802054000074031004816206508000307903540550111846140400d000100c0d40a01c0381c0310744281c3c0030140040e040503e4404450900c2546150094158030340080200da002084801024000c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 270779703 1250 270778453 270778463
    0x2120a0509071703040302210609010b030709060e071d030111070209091501210804080a0c060f0e060c070801060b0a02010b0a0b090d05010b0a080705120c0a18090f 72
    0xd00008210400800c0060482c03c600c19001c100c0c0d40300900e03924011480000d105455000444507400c181f0411400b05008a0003203401c20709100003a02c5c06400d0107000c13180240f1400e000003c420f982e6000300d90840e28415144c2c01c55443d002003c41e40c42d0022000489181c08000d410f8103103440c244500103151803802e010700d03121602441042014100a0210001ca40c8041e0600ca1000b0740860f90504440f082e800b13660720a0100b0501846405000402508400002c900000e41c1da82c0810444004e0b03100303d40e47d51590303494030800e40e0900030707030722010f0001500c802595046003040c0c0700030000d50004004a4245941e01c429460a50714207810400e0280b40209031803045a0302400b80e41c1040c00222000d0300400d0a1180b61007150007000c5600c0d2241c03003036120300410300101b98020124040b010349010400d40e21042e2141e601e4480d4481c203402401c440c514048107000c0804ca4642088005015010903850030804408010b10341c0302da082815561041e180000321456034050b4603034890 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 270780953 1250 270779703 270779711
    0x15030d030b0a050f100f020f010504030806030d020f03030114031207050c01140304170304030e0405070f17060604060f02070902030114040b0603040210030f0b0a0906030b01080a0804031502120a 85
    0x2a40a0010100c5107030f10050007000340c00ca4100442d1384915061090140ca4036101040000f4600b080346808403414120f18254641402c0c0300601d03a109048a104e20020750440301c1d0411495001caa50341290000b41c0143e80040c0300500400c01c2c51145200c084000408803100d10340da403007141c00b2590291008a855034001c0100020550b000038003170400003d000000d9007940341ca0307110070382c800d2044a401c2d070601200000003020980210201c0000072000342c82080f040c070b05502c0c09420a20f846d446900840c0c8102515850550080005445404007614080c201407400b02c05842c0c0c007121140b82801d602030b0500104942c3e2a42c409107000b861030321030310203109003900700b0302048a160048090181004004020251700c0f2052a001d6504e264980003038215000b0180c84001c0102d000040d6020201c0000010314441c250061002c0d43e01480811600340da0b5864040d5660035501801083d00c0350500c230400102c1e400c0e18400c4441e0400410140c40c02000300301500000c1c0040b80d05810207956 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 270782203 1250 270780953 270780971
    0x801020d0c020601061b08031b0703200d090b03181b040605011e0e060c0708100b120a06050405030d05041208010b0a0504090e0709112d040b0315030d03 67
    0x4104a8913004040ca418070542001c0b001c00c00c4000a42e540034064400340002001c151410b0854500194042c410b54505403101c901d450000d000c5c0c100e400070843d01070820b228032182104082040080c3d9403140e10751070700542c07402002141c1600001c000d1025940e40794212500113606014908118060004400c3d02c800a0740030801100d100d07420840c1000504c06519044504001031035040c41c1d41810f11409010582c4005070b01c91154402205150013001d1001442200010301c41e86c1e000907a8109204501c03100c0f082c407445a800c48080d0b14244d00070303540d6101240c0765a00454129000e1303020b507071520343c1030121001900c00c261411119008140c11040c0074550002102d40074088081a5900d131035107101c0001d00c14000ca01521511a55502c00841440780c1040380b031004005c40c0300c0a001218842c15a00c0f8039400104040342c07580c402140c4642d00307075003c01100c002d070959007028504090030030715030405580008080d10303000440c0c00c1c102c0754240d5040000003c495026940442c60902c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 270783453 1250 270782203 270782207
    0x10e0a03092306090307080d020d080a021218070e15030609152701051e09030301050d060504022e0f02010e0706050a02030f03131716060b010203040801020d0c 70
    0x20140c0c800d850035080d440d0a01c2e0704414100c051049002d0484100d901d07515124006401c1040395480696244180c0c03111b05030403500400d046906180a890f40d0106542d040600340581c800c682d03a0911340c0292000045248181102100752140c01c981210203441d210142120808010b4500f1707090b02c840400510304600c0c00b04140755021620101511042c400c0b403141c980c0089001d41041004071400001e507480c0a0b042c0da4000c40c6d600f80900130320260421314542c0b10300614200c1c416070200e140800090b0234a4000045a04131403002d020019242c2c070603102c510003885c0252003240d2200c10740461800203044600d624a074036543c815101d0f0646e003c0f131409441d011016035550103590411030640d260081c082118421620070742081e581d1000d1b054030803401c5228080d9412981440482840001c0d100540d4112880344140e08603022134400100c814042d00072079848046d000002d00b034801c0081d403150420800002c06004480c1440d803580031a60aa800c843c544020241d526814490115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 270784703 1250 270783453 270783467
    0x3030f17091e010b0d020f01022a0414071409040204080102031509100b0f1b060108030d0b0d0b0604090606120803060307050904030212031015020d0206010b0301080c040509030903010e0a03 83
    0xb44041c4020402d000010002c254000c0300050064440e40441403000b0550b4024000b165403101d100d2a5121084407240ba540c01c14610111954011403516018452401c810b00089004400176240e85406444000c4120360540c00031454036007040d000e0200056000c8240090b500402448004842054001061040c081d80041040101c400020801c1190703030340341c00886444121400c6260750b2141d10f001e1590b032000800440034001d205240000880c00c5000c0050b1a580318030740d0307050041007910003c02160254803c0041e04103008080800c2c080c0c0791942c00001941d2003820041041580c81c240380803007515607481501c1641000082120525042c050b58002d480c00325841c0c0304a08090314002c0d607603a0246076100030101d0000220340106212150382d0020210450b21850100c84410025110440d01e401e230000340c070070311001094140408095a0613038810b04020321001c140401040f02414016001c54200e00040100600341e031001e005542240e0301040041c49001828a4020492 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 270785953 1250 270784703 270784753
    0x60d0b120111040b030a0b03060106110f070515220f081006060f0503130507150e0d111512090102040312020105060f01030b030c10030c031805030403030f1709 70
    0x180d25010307a052003200d00d0300544040d07070800130f42c881c0c89990b034001070401000c2115000b80c1c18412a00006002c560001800e0b6141c80018243d030b507124a0b20702800d03650380240c0a02503021014000104101603007001800e1031300c503c0c2d50607031640c601e09443c40c4024400c41d002444521842c0c802808150401c01a020001c1c8040c03070100155072034480000c01c034148408680003085000400304044035191549021030b41d03045010b48598540e10028405519810b001400c0401c010750070709407840c0342042510940c1034003c2c11200c50707803111030100705910702c08241e4080841814800803490f0796444c94110b200701100400180d682c4d045080940c054018000002d00b1617042004100241c1c40b5426005500b02d42070801107034914810000074100305400e030021783c029082003140078002da4181c220b0448034805490810140700690720b402c2d50140b6403100600154002c11007000060301c0303071081c40a001190310300a2035000c1e15a8420362000da068078280c02c04e9004031920203240118002c20040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 270787203 1250 270785953 270785989
    0x60c08150d02060306010e06130b0a0801051002120f0c0610060306081b09040303140708040201030b030f15150d0f020112050112110105190822051009060209060d0b 72
    0x8003241642c0001e125100040c2150b04000e0303140c1c52040e0545582c001e541e502c0c40031103001d503a0607031112002c4010f0303049004002c002480362000090242440d90145124502d241e002e401500c4403a80c58103066480106c00442c1403c04102c0c1d96030906c01070188600600d004032107113511a1a041c8003e00362a00c0350440700007034100004090694405060306518040140c508c01c0c1950703120300f4168001c0004031054407501e40420200086594080083c1d48654401d803001c100031481e003030505507140404040c0494a0b881021021600d0655480495011110401c003103403000d04000815210f03040b411084500b44c008040d07000c21980c10040030003018912800c03c0104d0341c50500320010302d02d5180d001402440e0b981c041250b49920410443d400200502d240d4036100c0a503c000520075001103d4010301102105044485a40c034180c0b103280e02500107005005480c0c26910f07102c010241400f00320f40f040d90801600751a915071901520310380d100c0d2000092600c2820003030180d102c0042400c109 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 270788453 1250 270787203 270787219
    0x2b24020901230d0f0905060a0e030d15030503040e04051b060a031505151e0a171f0b0a080a0902090c0f070203030d0903120b030705010c050109060c0815 67
    0x200076603204044030290000311a00c100e048900303489000c19031040b040b154280a003004801040304080b90040490148104215205662694800b1048a40180e48e03202d05400170400c01e080310040303401c070081400409510280e0141e07640d0383e940c40c1d40d02940c07003009100b2040040209200c0203000e4568042c00020000d008042050700107100c43c4500c10030034050541c0c3c3da0303541d041c010744120030001034140503042c1c414004586010781d01e01e40082031100b5804c01d00c210000c01056014068a030054581c1d1900381030060380c1d0f94980082d80c0010103144c1c001481001c0700c0071a00d1150f450400414035914150ba85c1c1034010070007003000c3c04c000c000808160070540d510006848002e6070592200f2000b101640700d011130b4000500d40c4c420001c020b540b6100106003507000d0111030784800f81403842910381d070481b0304000c4034410035034030b44169069141e00000070405c8154000d40400410510030800001c05940c955503140c11500e00c0154440010720013000c0020440720048905041602110110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 270789703 1250 270788453 270788467
    0x6030905070e0703020c010501230d020f06030601050d02030c1e0304050a060507050706060b04140a0b091c0213060501020c01090f09110c1c0314070e2b2402 69
    0x503a544141c2c420a120074408200103030406201c1d9064406101500000303100550390341c94490002002002d0900195240c0c1826003081c2c5441c610a1012a6016100035079024081007008200e410003000d87d41407050410100c01010f41c035200440c443c20700c0e40c0310b054494040844040000700141110f04080038100148000f0450024421230103c0d400040480c50f0756031000c0c22607290042070001084641084000b01f0001c41c00c40103002a2842103030807240301e0b4000710400c081d201c10b621414054210030403111226040180c0303c05c2e00082c030720513513001e959450343c04114010001404002c18a603264801e10866a040c840851003030001d00e00720142c981480044000c1010781e2181c041c0c46591822074034246068070083d101011940800d5a203194000301903c1c540f003580300b180da000240f0b8030900c0d81100f02e403140154040c411030340d01e80c2003800d04070b000c1c0114100303e5000e00084110307909401005800c400000030354a0310072000c0721511000c0c0501c41020325411180c0f517000b140184054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 270790953 1250 270789703 270789713
    0x1c080307091d0106052a1e0f011e090201020309060c010207030f0503150418080c060a0b19140a03021201020d0b0f0306060112020706050c0912010e19020a0803070516060309 76
    0x340c0e5422021301350346c0d42e840c284280d10380ca0101c0e080586100c640290342091b0415510203501184540c2e10341c041d0b800441c40300792200c0c2210505841e90000310002404d4002c051b4107544140c04803441801140c1c42c00821000041c00d130341100842802981d00050404100742e844000502c039101c26081407800c50070301e0b8000281c07500b001c00c000d81c0216a21007140d1841082030f04031400c61600000ba0aa0310a41102c80945682d4101c4040c2221418042484518105180d164000d4802e00c0040001035040c0b000c141c00714804260569030108080030301202513926008200c41150b110300c001130390b0300441c0f45c12405640e6940015403080c1aa84441c5505480215401d517028000b403808180d00b07c00300d4600802030081c10030103800719191a0420444140c20802005544011540102d20943c580c0d40942030720b89042c15241c081c6c10260700c04004c070a46480e0a02058402400c080d0fa85840b107100b20b00c2c58022020a440581c0985401d07a0000800ca8003600602110300d010300c001c420540301e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 270792203 1250 270790953 270790957
    0xf03110412050304050411130f0e0a0b031c03050601230304030305040f050366011104050111070e06190306090f0b010f0e061c080307091d010605 64
    0x46150540302001a40708001d024421607000d018010f0041100d52004012181c058020b503400c100c040c1c440c05001700341c13001c0c04000380044a4101d81d070050555500038540001c2c00641281c00e81502c03c2c4c2804e01da01c070007840c0001c00029030301d5a00040301e00d0444001011280c0b68812208142202804da00c1c0c0c004841c800c5a5000713425040c085442d0b00d81d450560243c40e119030010300103000c0882e1481d130280c18040d80700f040f9480c0301003d00c0c080f40ba0a002c0b00202d20384d00250119000f0340c24568075000e2482c40d03022002c07501d90214881c82030b008140c4074250f0b1200b1241c81e030221000075041c0030319a00144a40e401c0c0580500401ca40c1c2e00f0444541002c00c2c019189901c0b640c0840c400c2c2030158040306080010b9039024200748111409440d00410082d0079801c119460f124140020038105a80fa05140c111103091800b4130321078030341074103115640101c00c014103400f00042420001141204004502900d01030342c0785030a40b460000d015040300c0d501e07001c4044d480b01c4000100041588042 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 270793453 1250 270792203 270792209
    0x10c05040617043905010813021005190503270a0b06040b040e03030601031109030d140f1c060b0703050d020309070f080c040b03010603120c240c0f031104 68
    0x241c1900709840b1030070800f14114021041d112404d800401012443c41000d05043c3c140c2022851041c810b030300c1c1e50041d689110201d6903c210014500200f601600e000c0404a942c03056030700b006850200111a010a410b00c109582c07400f0600004c1401480f540349200010440c400300b600f11a11701e100c600054490040482c00307010108500701041c072540d285e0b4004400072400030001c0268a03080d01c80641c0300d4004590f840c3c042841d0002c0d1a000c410380c4000c50380e648800030043d16108401110a80b1205807191507181050b40c00c0c0055840c03110030b44010f0546014021512122070902c004c083c095038000e130040c01000d2006e00080300082d4010080c1c0305030360100c1702c0141e1280e641c0390016182c1200b41e40000d003400c00e141c00c005541d1201203a103411088082d101030000100d00e0381410300381c40b00c0344401412134180ba5860014244121048506184203002c3d02d0b2100c0544810410207201d02903404850a5031110251506a08a051070480c656681028820910b004080d08954020341c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 270794703 1250 270793453 270793487
    0xe0103030503040b070e03030d0b01030c0806130e011b02151003050d030c210b042717042c090f0a1202010f110309070609140120030a0f02010c050406 66
    0x100c041000c16008003220120818045c040340d4480310b09c0741140c405040d4034540207000ca8036140010f50700600c680b05440c41030101500c4104420034407861308000b0110300302540c405550710300351141c1c8031441d91800c424842c80c41d801401c003d4074100401040075805007209140d500d0300001000061700c04108074811103490b0800180520313154206072840d0351084d16805052880102005100700c036544007480f1040256400c1017200040c00803816400784168610102c00507c40c0380d5000525607403444039130f020210181c0c42c02d01d40d0b1496030b01121402c00c25510030003254244404040e80045101950002c41800100440e4000d03510b15501c500c0320003c090080340380281442030140c000d401501c40300507115800c01c6210340d000b201d207203260070680c1e2218950007041000158103100700911000d6032001802c2e6040140850010748540e6040d01201c4aa000c0144501703010031024006000c00c50b00ba9150700414a148080090860710311150354010302c40c1c1400300b4001980e1001148140c3c1c0d03024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 270795953 1250 270794703 270794723
    0x50c1905100e0301140901051815060a030803090102120c09011e0201110c0102030118090201021b030a0b01030311151012050102040b0307090614040e0c070c0503100c090e010303050304 81
    0x15407012038004038014007036074244d82080c4000c0c81d203102002e2005c0c420101c803002044991600300180e01030030440c003c03450166009000000201442d4500e02c0e421110040c4a50714040d5281d0310200c04c0c0d04100d8102003581d6022902d601081806440581d121100e6036025243c1814140042c000703407250684a0301d40000350316903420140c000d5106c07840400c400d000d05621210000301ca9400f0707510900071401c0c004440110081810b00c2400341c526030960580103082c80d682c0303141c2010a220110240e5980c1882a1080c46001c1001c182407203001e10702964031b104650070302c2c030140ca1400c54214824030044040301c040001080c405280c00d0300b0f039450307548503560f050303000d040542c00380c042c03038020710240d090000038402d0070703a040905602180c801c0c0d180c2c1803605251000e09140d074059486010200707010480044e00e101080b000410009102e91050346800341c0390008079103440b401c4800410415500c03801c0001c3d03907030003002c204004c003510822050b0960650798000e101e0300024000820050748 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 270797203 1250 270795953 270795979
    0x603090302010b060c07080c0301201e03130b0f040b070c050a1b06201e01020c011d0c060711060c0f0a0804030b0f071e02071a0403050c1905 62
    0x200f0b4014003140c08004100b0380e21482034003000c944904061040c07080511840c5614241d82c01c06010341400140b800b00c1b004000c1008501c4968264483d040c02c002d0143d0f8602c80c0d1090010740c9000d940102c00c480c00d041c11020003840c01c02c01c480390241041004245c800c2c10800003a010a180e150701144928004581c480b4501d801c13883c01141800040c61080d208809070b60b0010703c2c03c1c0c2136040311615a031381296140b08405488001c581e4004440194004078601c155a446040c000e12100342c042e0001480c064020031004c0c01c5440c602c800c6045555070800d0411983d0301045510003000088072040e00d803485540e1540ba107440342115040c000c0c0c10204214070b11004c1403281c0c50503900d0310b1060780c0b2586d400c0c2c41c00c0d00c5d29511600049922000000c0440c4031854200d0300d0301c0c03207647d907034846c4119007070890720b0101495803000309201140b00c2c0c00320101d600118a100080390949034845a07407510b085240050902e02c3e0503080c1e41c000c00705031028040f4008448900d504550f0142c80e60352000003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 270798453 1250 270797203 270797207
    0xb0a06121104030809040c110c0613090e0106050a0501030608031608090603010b0a03050109090816080d020c010902150f07060e0c040516021606020307060f0204080f0d0f050f0406030903 82
    0x200041c0746800c5070707501003000400c0c0400f20300206801d5404a6007040405400b00003625913007a85080c1412a90040d0500015410f15100030502d403140d010410300c00b03030fa0b0380c03000c0030a1315148070003444a651a8101004281803600c020400b802c03090806100f0b03503050600095413030280d0581e0300c0e07180b1a240000380c2804482811200c001b800503141550301d41e1102c800790034030fa00001103100041d00c1c0c08000104440c540c031850720229485007131145040180001403205100d0102d09440d00a020080c030095016140b00401d10201c003c0004500903013a40100f2442c0500746541071b88103c410032034040815040342c11a800b203a03004000042c003403c2e03440f2040c54140082c0388160864039000500611010f183c4550108104c10fa0840d081003040c81640b082c2c004840c030440000d6441030000600281d2550002100d5018508005040c50b95420b0a28580001c80001c1d14081d04080320102205502a05001504200d400e100d8580b4048a00300c88a40c852845503e04241d510301b44642014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 270799703 1250 270798453 270798461
    0x20030c07020409080a08010f060c06020702010e0915040e07082a09010905090105100303140d1e021201090e03040e090a02040515030c1f0305090f010c0e10030b0a0612 73
    0x19801500401c4480700f40e18260700c42d0b40c0b04036101d2001c070b0002c1e000080c031203200e1904001900c003aa80c6940350040f003503a03907801941003010124140080080096401e03140c50109501c501d280940d2000c0400410045c84215030300c0c140707002c0ea5a04451820f0040072070001d10760119085047e4401700c4190070482101407100da1218043e4454080000007031802070070340140e40121440740080003240c03990380b00c590ba514000e11000740411400c41c14a1422103859015100b039030800000481c007a1030f140740c0022960800d000c100082076020410315540110503d5050151000d072600300300ea004190700165982c02030307200c0c4419844204000038904001401207154096001e00240043c0c141201c1b6461100080c51009000703103e410040605854200c5040340d500d80c0c079801c245502c1c1401c0c17108801520000b05801e03110b115400e50703014244024411945503036050b0380c03144442e042c00010481c813444203c0c00c04007014144000c450031980d503040f141c0b0403140e2500340b04c40c603a6032000742c1d80060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 270800953 1250 270799703 270799717
    0x7030501020d051605130e100f180507022e1b02070602010f02090d06051015080a0b01050901320c07030501110408071815091d0120030c 60
    0x103500124200815100701e80189014089820f04601051101c4c00215454080e020b25921060b039440e1081214040d4124141e401a005003004030000b80c68031581600e402c407030303400003150045407003600e011442c90b48074841c1c11200d20303c05414044020001e0140118045010302404ac1460000c1300564205030301521442c0740c02404100b41c1f81c0700c40c4010b5211003080c45150095420401c0c08084852b56100700d80324030b03d004040c80c1000c807098480da0001d0500408c8003103216014003011490030085072050526559940d101d0742640383c5041c82d10f0598090a003580d044c054140003081813603800c0340101c07201d1407900b81c85003205113500d100d40c00b502d8030540300b101d250400054190350301c2c0c00204411003602e000d90002e22a5901c46903030044184030754803404030740d60001c4805107d080010400c0740c104d929889004542c03050040c03841c401c0032009030b000b4160b0704d94071248040d03185941c120100f26640944020445e5003041d0441580c01c40d000d000409200c44008002091844110251422 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 270802203 1250 270800953 270800963
    0x901060f0203090901080d03060905160c02032e0b0d030c08160b0c21040302120c0c0612040b06040b01020c0d03050f0706051819030e0111010e01051501170f090703 72
    0x1380d56500c0d48815140c91078a009040064100f03680860405440e0203480d0064080a9281c012408019001c90303880b03440100880c0e040c0100034062806ca664203407031a00c02004c1d982c000d010112001c80c6502220102e01134180903080c188000b102094020640d6800690003400555440d50341d225084444801c0e044000c2980d8058014000c100d041e4001800f400164102d03ca0f441c450780c1c80f89940e8211049078000c0040e4040c19401071007030fa5030070150020525540403549001e0b000300020301c040c0c0060b04000003900f0124108400e0044071440b440d00203d06507000c01c402d00d03074840001c1d22150b04120082c01040040b4140c01054418800c4038810103518041c1c54640072145804406080c1c20b560054880e84204160900120007040b50340b00750140d07182d40e0134008805d0f50196507071104420440d05200320800100d910103402c4c042c0240c00b25401c800002c2c546058200c04410181002a041c1008200b4082040906984d0352039904280d00c6c0d402114156106161145403400540000700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 270803453 1250 270802203 270802219
    0xc020d051908030601021614060703050d2f160b0702030c0105100302030d0f02060a0b0402070807050a0213020f0414060f0c070e07031406010f030209100206010e010e04020901060f020309 82
    0x1d000900b0040e5000d500c0c01d0b4213556403241d5004d400c0741c1d041454001d0f404104042410b4844900c2c200340149001c0d4841c0c148075060001710f4216508454a51034040040c0c4120b61007103a08000d0502801a00102000c202c1e0809842166400d01807488150007032401202c070340032070000d82c020070543c1c3d90f40040754001d00c0741d850921001d8450140b5480100e00a00c58804c2c40003030980940790120420070941c1c004c2499039250b82849000e09000c0000b41d41081c2c0c02c2042002107040361000740102402180208060071051040c00220203940d10031a25483c410b100012240e141c1c242198102c403584040c84202491860024401d4443d01000c2506d0240018003090008404030386401190713208050a012503548010680540307216500b40d414007510b100000d4003035030140120f250307164018a0014103208901c40070450f4905490f0310340000d0ba01440041100a04458000f405000507901620050415502040b810207060080c20107020741000b4040b010b034820400d4507440b0200402c1c80c1d23 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 270804703 1250 270803453 270803503
    0x9050102250c05031513061e150504050907030f05100204030c06020d08070503071b050d1106010503030c1207080904090303020c1e1209010909020a030509150103030c020d05 76
    0x1081d0201007a00c1200d031815440ea00040e1840d02084072082041c0300a0344810300d030360300c0c2c0c0069881d0400c04811900d141d500d0002c8406503400407001c040e41c01c0610300006000100701580343e41c849060344014402d80c14001040344100d004900381c000c4960110304622100b8081c40d20383c5c01d00070995400c0c2c0c006803011800100303200c1110040d40848401e80c0035110100d5540d081100c01c140116580804102d0410110310307140d119040315801141460b1400403058850f580742814031481154410024521554401d400e020038000940184811001507150030030f10105140c44007201c48250561410102e0501d0911002000729040110028000c01040d0305a03d0040c000703400034683c0c051305100f00160b8840c00e00d00039900b905c0b680d041a000300800340e200d8130001c0c8658009561541082080d090018260145001070800845640c40200b07040c135141039110f04d80b41c1002044024924101c004101181c1c208010300c82e266010b88610f0921141420000d00c0e01743c00328411500104240e00c54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 270805953 1250 270804703 270804757
    0x60903090d060212100e130c0e04110907020313170d0f0c0c09090b070302030405070902030a23040314130e07052107030605031f02032706010302040c14090409050102 73
    0x1c002581d007200b06e00b54054503020480d4882002028004150f02c40e108400e02064280494035540b00d4881c0c000084201a24004542c1145c1c0036505840581d00220720444540d0641510202504628501e03564121151074030503542d8450b8501c2c0b50a00203d5100c1c3d403c070758451a8125412600038a04519203503a6500308401405106020f0322071409240128940c907200b0f00132a4011038000b0014910075041041c580000d500c05031101812580e1540480c80c0c0101c200c0101c049405070103a450728501d0242005400000500c00c40a4840c00c02c0241d20f03181805114400e0903a050f01c00e00b1000d030ba481c3c40e801d440c1c80c410700b050810b104180b0131701401c5800701010356500c2048690381c01e105950740c40d018180c0c1c03100d002c00701020012030540c4e280f888012940c00b45a001c0708500c29407080c0b890110800320388030040b40c5001700e95044040140294149405007503404003007860101d802404001c41944207002d0423601034840d940711303503078001400ba0940560355004001001024814244280c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 270807203 1250 270805953 270805981
    0x6090a03020c0a03020d060f0213080102030f0c19030506150c16050301063f0b040b0601020a02100c24020703110c09010308030a110307051b060903090d060212 70
    0x81280103110700490011242000b0428100300d07507000c2c12101507038a50344d40c2d46000d868000300c4617621990074460040c541456100c41401002e843c1c0c0010f07503d080880c88203011280050056094a8081000301111307c541c00c00306500b52107a24001a0ba6100c40c3d00041e5138407204190b01c019810007090a0340680320100d400075507144a00d0020303807030b503941e4018582625083e224000d100c451202c500c11003848448401d6418007400022003030b42904100c000c81080300003100584550103c102000200105100b8058009009000414200740c42c0e0f400541c106614100407010001000450000c00c00407102800d2041442c07503d802c218a0f0710700030b5030000e400111098000404840c84928041c402185804010b0300152000c0466800c50722250899840600302902003a521b4948011550f814000f40d800350646a544540c1c802c0d01542034502c1c031007408492142074002c54140407030354400008651095001b0340350014603010340e04061009010300c4400795422080b80741001010f40294407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 270808453 1250 270807203 270807223
    0xd0804090c11120f0c150103030206280c02030702030f160509010807090c050c0303040312050c03130b0601180f03020918060601030b0a0302040f0f05060d03200106080609 75
    0x300030000d44615480031518910030420081864110042440b01c01000f40002e16800d0b80180080c0c0ca0060703a6000b0a1920705542401108940741000600406506210280c3c212603014100d581c03440782101c40188071004c1e20b0030130803810b555000b01e00c0068028019200c00c0c1d42c0043c1524958800c5c242c1c499229a000f140e80903840c441c0c4400403840e450200f2213103050342e0322500140788842c1440d206c6c60040c0340712281201800424040b80820a104200440c4103600c41c2c1d56101c0982c10391a06481602c20280195450301c23401d10402c0b0201802e90300c40304091390007142d00921b546500300180c0b108080e030001c140301049e04203c013266950300d086107a022240309031803050503540c0c1d000c03601e2016103800c03050503215004500401e00c258440d8000d1054500000d011100341640c17540017600722001d100f22071803030325141c0030319140035280d910510307038403100c1a2600d01c0003100580c0c0052011400b980d440c003034203880c0710030381c02c40340000d521000c09068004111400b60821548090740e85407090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 270809703 1250 270808453 270808469
    0x304140705120318010c0f03020f06070f0206060f1c0c1706010501090e09160e06040f0509070513060308070b0a0b010c0c06030917040f03110901050105120a09020d0804 74
    0x54400107041c207002ca92240c2442c41c81c4069400d20800783d4400c504c034a0b1031425a410807040c80103d4000c0351442c0c0c03d849104e8480c0d00140907a081604c1d1080c2032002c02004041482131000060200300d8000c43c0c116888001120440c042d80b07000800510301c1c407800703801101001802c5010908001000f0410000d66451100b00ca0100e903100761210303523405d02405400d0024610040402540c407030050044d805c1a41d1009940418200400300040c1601e55070181c000380e0096030503c89130b803c29100f02500a84c01c901c05001501d030903510640d548070203101d02d900a2180e680404030002d004d40c01403014590004141e9a07400b0306c0d050195068005644040809141001c20400766016042210020754081610410145004002e40003011403040a9903139000c00946451119480c00041000e009800400c4802c50305505110066040c900c03c554040c00d0aa8010701145e80c000b001d41d4120003090f00c000381c10b59a24844440600070215000390080d070b40514040c00c20503820040c00c00e4400903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 270810953 1250 270809703 270809713
    0x20a0506090a0308030c09101e1106190f02040b071415010501030e032107020f030c07120302100f0506040c020a0b04060f0b0d0f1101110c09100308030414 68
    0x180080010340d2240d000d4056025028400c104000ba00007070107551300183c0d1240381820300241d00082250304018800c140c0006141079072002200c50b4101743c01700600050b04e8144034401421a4940da07030382002d007620350420364120320f01c4143c040b02d4200c0f103003030100078000750b4856683c0e0902c00001e0b04141c2d0100c2d4000c0c00c1480300b2421100000b82d6090b40a003007500500030b43d18080c01540141802d00000c4d010340006c1024000c4107181e0781903200383e500340301c00c02e544901e002d400080c00c003101d1552031a07407134004003c8044503020000341c602c1522080007190600f20f0070303490140e01c5d00f01d83c628080091070403c051506e0f0b000050744094803440003518148202e0342106002c030b031038050444004220b52040d002240103d43c80d6408001e60f000150030002d200010280020402240954105c61851116a502c000c0003c10070601650003001e0034048194017031280440d0711107030b1a190707182c01103000000080303603521000303c00001076401c1200243d8030304050400d40d1056042614003800b40c402d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 270812203 1250 270810953 270810959
    0xa0b0a0c020d1707090503030c0607030e0307030c11010203130b0a020d081303140c01090503070c060201060f09050408040f030602220b0d0911030f0d02010605010806010f03050702100f09020a 84
    0x1045070a4141d00e16610f10076540c509098407101058081c003840c00b0000c8441c008103a1391410801042c00d40c00a40061a461404078801000c1e180203114240c4035400074880314001070b130402604041c3c45d50103ca10480300e412000102d10314000d00d560b560511984040000e00c42001e90020b00000210780d080d42d0400300c040200380d900400981c0c00d40e41e42c08c40900540c0100e07215600007140710002c00c3c0311601c0c1008509140c0c0c2551140b160954240c2c000162440401441d18041c900802d901d00080c8001440c0400030300c2c062085104620702e01c2d4039400050104038030304d412074000d002d01c01d0700c0840d401d86030b04024000f504000034040c40da03270b0101c001200f007000404585040b14803c801c014546150000004050001d81300c04540413582c0d1811840e0340e66050206003414507078074009003400c049124001b425200c45902250600640106011050740e00c281231561040d014107001c0b03440d441d80e02c0c0032480d007c0c1c0c00e844402014a0220b1145d0820721641004074094000c48140a0b040c0d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 270813453 1250 270812203 270812207
    0xb01031407060915020a0b07171501090303110309030105040c0302030d0822060b0303071a070801050f01050a0c050d110c01020304050a05040b0a03170a09080a05060708180a0b0a0c 79
    0x40c01d80100c2d004a03241d50303c20003041c1450324501c1c92440300c1e44140c6000c079006549000000302c0540b11071002c10350005002d1f41040c03e0400d05948094031124240d2115194000030b00b6030f0f801d600019041141e55510217040810400c00c40d451600c01070000c01a40c42d150811025044560008a102e0302408650b81d80d801e01c900c408030700235900b20541c84030030024000301c8c10000f02100301c00c9604a488803c03038203d03540c0074400352078014001d0801c90f5110740400050810114020215010300900d00c0050126495090340400c01010a0829170790300e450f10f000a64001443d890010800d11400c0039503500303207622113013202d074420300c4008943c00084114011b80e02da004a01606806c50140002044949400d0300032000c80403000c1d00300c18000c2c1e101c2e100c8210120310170520b02d0a29800040540c80941d10110032801488980041c0c0301036009981c40940b110030241a640c1000606404240c4032500802d07110f49a040d810b04403014213180e45882480004121106464240381020f020305a41c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 270814703 1250 270813453 270813463
    0x606160c03021201090b1603150b0a0306080a050a02060f09030d020a1b030209040204111909081005011d0a110c1c050f07031803020406090f0b0f031203130f0b010314 73
    0x4c1d0701070f80004491f55040c0f141041c0710b00d1045d880c2c0070142c880d1044145240c0e100d0b544c3d4081d02c0001c1c8455a246038007080a41540c4195000fa80203900c00c1e5030003400b1139008aa00611180d049813407658524180e803801c112030003040700c03481d45801030780c1031040640e80000d001c002440c0302e40e20355502d2204c030802c0c0400302c0305244030194100404c10005001481c203a4420007440c401062010f00741070f20142003903103120560900d1408104c807080c06100c45003040103401d021014881c020312040d81407003807000c400c0f02d00c00303100b4494101c0e450114103a040c0c641c0249103892403401007161240301140700240d490241791004800240701103201502c49100740111144c00b003548101c24034010199404603036102030031400c0501e6502900d40880103039101d004910003409a400c010820b801102d5645003210300705160517226126161015002e81c401041040985201c0c02d5403a4690b601c482d000005040c852030000e10341d19000f06190100200702400b41d0580e0b00a00072012030781c1c029450f4a943e6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 270815953 1250 270814703 270814721
    0x140a030e04020a0e04020c03040e04030503040303050a0b01140724090b0123190305070e07110106080c010f03060306050f040c06020105040f1101050910021b04230606160c03021201 79
    0x6584d12000761003070429400030410b10003818100d03481c15540c0c07116101d241c0030903201100081c40c00402d010906505014903a00300c03900d00410000702001c400040d003400f07007244060a060300081284824080000c81d030104228181d0700104001e146030110300d0003803405c0001110100030020010580b41c0c903c28020450011701c1c0c8490764162038800402035403140008181c0e10b040071840c00400050400d1051100a00680404058074205070b4005002c01503c0c184142141c4c1c9007031000c03c002400060807440341807080c24620341400f26000200c003e0400c0c0c2d000039107842e080c10103001d81c0b50b075020303203440c492401100040081c5440341002c03400d13039800f0386002d000f4040d040401c44c00b04035045454180140d0504001e881c01c0d51700c0c1e000c03400e0503035035881c102c000d41c002c0300c0860480844c2030030902d41488100d40c2080748458128154200c01d140004581d1802101c0c0c0c0001c209440b080704030762035003040440100e4075488a207082440c0c3e4041e4003049014140003030318800d031000c0500882040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 270817203 1250 270815953 270815957
    0x4150f0c1404030b04020d05121204060b010e090a0f06080f0c010f180e071b0c08060c070510020c0304080a05032a0a03080402040b0a030b061c05060a0207020d140a030e04020a 77
    0x100f6100d03078003048400c02c1f0011041d03620b805842450b032400d078074000c002c064160350400340e9520b501d09401e01e5001c40d602c6812883c180700030b04e44a912569114281c2076807080b00800700003000055031018000600d9135401c6001244542c141d030007046d100010706081000f2090381d4022500c80040340071540b000c0c0305c0e00544036180011009101e44001c4007c000d030711040300d28141c426840c038240039a40110308107034296400c0807044014440407200703100040c0e0201d182001030749404036940c0c44642e50001c0e409a0381e003481d4003048968403800c00340300b01c0e002441494201d64407540750313040ac15260342c0021803102035000b0000841b00025480c2c00582004183d10019200d103070031640381900d4046000b40226486544d6100045da01e5981c0104003019500034081c001081c60b100092052160807500200b000094440841002030800a101c42d0f02c1003280c5070141e00c44a152010a07040716200e50010100c90202d02c0c01008000000741c0b1900b800e0080d5910414040b240c3c040c4404c80c4a05030344500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 270818453 1250 270817203 270817223
    0x1e0c0e030a030f031803030902030105071e0507170a08010906091a060c12041401020c0319120519080901050a290a03020a090b150a090e04150f0c140403 67
    0x210f402107804500140c07071410041501c848030814101c007440880c01c1100440d550712400c2d801c1d42024440d280d8000e0103400c0c003017088030f01502f4401d00706007840c50410402a002401e107040181d47c07a00b944581d47c03920081a102c0a070500007500d030841c240141e280c003514064001800c0d0116029003010010b5200c0e02108a4000d101803014071350018005940c14482d841440b4000340c0c0c00401480140035501e00a514105402d0009040403010280c4520170f6002c51004100101c1890040103615841201c803131410660900a81c1d4500900390350700804d0a5802000b582c003a04000d03201c1c81a030000300204003d5454080405c100c81810b51003c1880300c503c00643e41d41039025482c484101002070650060641e01d90001e49021503e030402d81c0382c00d442d006061002c2c2042d0b844140208240c1300410b04000e2103620090000486100358151000000040b030300384600d120000744c01c5810801b0030311174986034040c000007400a84101400050032070004034000d40545058406880c2d00c519010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 270819703 1250 270818453 270818473
    0x307110c01080604050c090a030606050102010e12030a2705070e130b071b17130b040b07080a03020c060907030c060c0803061e0303070614010b04080303040b18011e0c0e03 75
    0x4001000001c2446e044420100000c502d40d69626038010001d5124440101c0c480707051400090a407001c100008445902500e4a55043c1503c0403e907075018103100b00004404500600318046003003c6944510314020005c0c0c800c0600c4008a622400c0d550825101c1005880302c64401c00b0031266583c025080c0e610403000324418a01c90f0030317040c1c0c2111149803041002009034075425008034101318071980c1c690b40005c9455501070302c02c50b0072005003440e41406e800d00d494002c050601e840348a5000307021900c002983c09000380680d041d80c00000411040320180d140c1040107555554050006880703028201d036001940600c1046031181c200e512004290031911451705005418220f60000300600e1900d00d000d076050b840420140042501845000c41c001d45110090020105c06800c01c5180950422061000c840000112a0800c1c0c2c008940100f650b140c804541806049454000c125400e01170700815074050085440d5031800c90704001c10081b0b94203242a80c40030002d1071038a4150b0000da44074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 270820953 1250 270819703 270819709
    0xd05161d010e0307080d020a060f0c0f05250807060e030f07170d142d06010c14070f1a04050307060503130b181501050109051306090507050307110c010806 68
    0xd40d42c0c1c0240445808503100c99146040c074141d2501c100059124144440074024140034400c0c0b0700031012010407400503040001441c140f01c404a2809002d000511101e1240b013100c000d03640c4084091282c01090200d1602e034005070311820090f14160300b0018940e00c520710101c21901c4084042c0000ea02d05030007a0741d510501c407200720b07905070582d40912005014000c14010603c1c0070101c070382c0700702c0300b880c003804000d034000007880360480c0441d805400c0507030b485110f50210390046003d0a00003446451407912240081d4001104982e80c02001d00c002445000448400d054681c9204151801d8184040118240c0564495154141c3c0801c004104c424090310043d0f410283d41900294910b80c10345901d107130b62400b5640521705220500740c10341061030500c001540b401c01040b1084095241000080030f5602d42c1c0109132160301c03980d030070320b00c500740303d5101d2001403030f1800c0203000500e0030710000b807d1a001140d84c1c0d00494103042030a8498400031407030380d029180585656500d61103180034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 270822203 1250 270820953 270820967
    0xf03180506040510021507090512070e04110f0a0e010807090908030f070507053003100902090f032406030d02120d020702190906080c01050d090501110d05161d01 71
    0x105a00394018422451011012001840c0c402c2e4440e4807040500c0d450300d0103014482c0e2072010046160741040f242330049400c0c001d99030350815000201c202d420317440b840015103000c4403041c29660100422400140f079542c50082d0604803040c00d001d580b10696a5504c01064400c5004000d040d8071081002442c240e41c03482d0f0a94018100e071400034140800b5560f107528080300040841008a02c1c0c60301d20079071400300200501681c80803080e4a0840c14814a002c03000d94647c005d600f005038020801d2022902c4900a2074040400182210002c0003451006005008002c110b808003001d003200180580c00c0000e10301c07081c400030341d00505c90907070034613455051b80d0424012502c001e40c08204c50f90160740c0b504c0710404042031900c00003882030b00d428522003c8898590012031250424110145640e070000c080d108440c4203041702103021007440c0b03499030050800c542002e48604c03010450705415191540304600c204180a00031900314a00402a140c0e207103240603801034142c1e0881403010030b51203600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 270823453 1250 270822203 270822229
    0xe03090604030f030e091807050111100b060c0a0b0a0b0a06050a21090b061f171e1017010504080702041814011e09050c01180b03040f031805060405 65
    0x41d0482c401080040000d071821006d99801d41c130101d51405114487c0420f00481c0000c110034241750307410080c0d03054000c0e110051030100880181d039a82c1900250348941080b501c0810302c4106944810b403540c6001031504000f9260680890720f810640c041e0341c10202500001d03114191141c60801090001c221070500e8035108400d824030304017031180c141080031701406003c28400d81c82d000051506c003041c05411080304241c3c07800c40b420070150515803174000c9207500015a060314009030325038400300040805c1030503000c03078010a0110760070032040415441e244e00c19155034034100001608858a541d00742c0c3ca05070303005440d25000700401801484e159100d064246102495800c03000c4650326501d20680340424408a140d44920011200b41600000045a020605020860240c068803010f5449541c04812070600595030a0f00c0c881f103042c1d088000042a81c542d0784d0f5035a02e4646803800c100d003100001100811b03903d600101044100c0800e150607140d0281016040c50f24000030000d16504d440c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 270824703 1250 270823453 270823457
    0x60e0f0f0709230906090f01171c0201200c06130f0c060e0f0303042919020304030201080901051311010306090609020304020307051008070302030a1416030e03090604030f03 76
    0x2200181c0035003e800c0c11030340010700c98241d0b8200100041401140d1600503e000d228031001e10411680100071a00ca0341540c42c449400b05440c507548450340d00e4406030703003c40380c0104075a0100c8451964150030511101c840801c43d8410002441006107160140099400da160045000544440c110b55074410f0054000c015001c507122182e1110000d045c1280c2290740005d40d4800300800324200040003070034820b81640110300d0549000807044042858070201c40e10039145004554205a21100b03031244141030f00040070642041410281da44c4e130082c80100d001c03903107010005290342010b01c281441441400720300000d5648540c0d4641940100401c5603062698031400860702000c0e0344204805840700d07031b00c010395031304141c01003520b03054890f03100038030484015400c14410355000c1423058100e140d40c200940c403601c1c0d030000300003c0c10038070b00065962400d41c0c1c20400d204107402805000600151001c11a5215115440d42c4921840b1240c5410000410007080069008040c401032079000e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 270825953 1250 270824703 270824717
    0x12030510092c19020d03090f090902040c0504050d030e011e03091709130506060906070f030305070f05070308180f071403070e010b09030a05030c0709060e0f0f07 71
    0x16820050032640940d02e01c080c0122106040c03401c1101c0e03004062099259070006142807152400c81001901d01060003d01552800c1150000c1501a0034100d01808052150400040e22404958020161031109a201301d09001802c81618002d8040f6803e9410140c026580102c15807825945503001c00d549504000c4125880e03a0807030f42041040d55046442d40e00820311844a0a14541403044001e40c25009101080400c506584400c2e10810040042e0b038041111342c1da40b40040c2c15802651100c40e0407500c000b0380302c01003210351860054064481c0e01e04001315118548101d41c02000120288082a801c0114002090150860650140d031840301400c00d42041610142011400440f072062076000390030a00041900c0740e440c000c1038800350020698a8940701480001d000c1c1803049101c441800210102151030501c841d80c1d0150700202280c0d034401c025002c00356152410700c11240300364a8680c000c07449185501c1014002e0301083c480b22401e8403a290042d01601025056200f072000c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 270827203 1250 270825953 270825959
    0x60c0c05040c020f10140f0c09190302040504030f080a05070905060f040504240b0307050a03090501140705031603020c0a02060c0a0506090303010e25050a031523030a12030510 77
    0x20805d840394190090f42c00b040308049016140610b076805840c103102c0300201001c211000048406a0f42c008404840021048550940740000140240c10180d0400d090104000c00d15400c900717120b480549564600302c4035580c2d0b51300700d022524280d940000081c04440104a54507004000e800140407502d4076500c0c1994800000302160a280701441d4008004940030483c5c0020040000c000d240002c0301d0341c514580703e48000c225100b540041d50a00d941c4201302814494254008640103900c14040c0c2000d0500d2440035025030400c80d000b04415142a8000c5440e0b88240240c0b080c54400e00300030145214590300f0041981c1100741d4081c52032280d6442e040100300e04103d01800768644070059079495050140a00b69400001c200c5441801c00e507200d01840071003d21904000d50580c64682c0e12800c2645003280035142e14503041d88502c0c0303c00d1004c0b8002c00401034082e0034007a20020702100840440c10326456500307488000d06004448500c0d400164040c0d00020741c010344040c0b0b000705c0e190b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 270828453 1250 270827203 270827233
    0x4020906090409050f0c03070e04030f05071b05030705040e03040e06060c060a09020915010e1207120c0509091203040b0a02040e0408090108090f0322050325060c0c05040c02 76
    0xc3c100760035241d650010010f805048814000c04184a500350b014244c800d040004900407018050001000c20440804a1030040d2149007618070146d40581c1c0e15280144201c0d00704003075142401018070900ae02240080c2c07134a024841c004030710341c4100140d81440d14024103912080c00080c01d0b41e4004c4000c1203c02d407a103100b03115152041008550001b29603140303005022103114000c00083c1004410540c5910340d80c0c2001850803030102c100c5070365421403484901e0b11b0812140360303c1040383e400001c19120420055111585c1034807420f5500c91342540d100c010240d52195443c0c00140d40400400104002c202c0d000c04295109425110140c46c20359034000c080c0c2010b000311001d40d00d061020850301c15035030780499000d030800d882c42e0040c00c0d55054007240a449115424036404450095048501401450b40401b4014100242520403400d65031148190b00300d0554047c105682074202e0201d5154022006030340c00642100100c0002c1c1c2c101800d00005100c4025501c048d0710843c584000624 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 270829703 1250 270828453 270828461
    0x3030132090705040306060503010203040f30020f01050a2a030b1903050c0906090705130f030606031a0c090d1104050c09030c040b1c170304030810120302060402040209060904 77
    0x3070303400c1c3d07100341d5070320310310f00705213007103421503040386120340d00420a10000c1002080000002c1d40c0184100845040790704290000145070107445000865008115040f6500410303c007044803c41c10007400243c1c0c2d650341082c2144c020401e00030783e9695130110319040c2008a00d118445902178100002c608060308001205102e854002000108021106000b04038007448124010402a2814021802c0440c00074580c024010210003c02c000480c4202c0c0e000100f80980c8010401400c01c10503451300c90034802c000d4140d6010550b4200d02000e6821029412545400d12a0410702281c5041c00501402c10800d050056000d0f5005414501888070f140d540e07200360b42c01703070f1881401c40d0b590761544014181800040605d07a4495843c240b014040c07031710745006007407103e0060000c20740702141501d009110000341c0d0081a03080c0c03e0110401082540104000d801005500022400c465a034040d0040b0240301100050041c1c00100c0070900509040d00505240603005051909225071000401c2c112 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 270830953 1250 270829703 270829711
    0x40507030512030124080703050a0f0203150406060801120209071e020a020f06040e0613060b03070206041e02060a0f0320121302030a12030b1206070906020303013209 73
    0x100c800000402c4a515505c03070095a20450003190190a544558007510010300140360000341925100040c3c02280c2da6400900120801281151070b41040a2641e9405105800700d60095150030b6012072454080c4d00041d0480d44d2180401052200507801e01c082e4031805040c0c03e05101c2402e000d8000e291640c0c040407041e00d115402001c00b09401e00401c20080c44446565001303c0c070400040c003900d01d0542d0200d500c030304151208a84005000c0c2c140b00101516844455441c5000c0280201031703902241160240d03014900021407182541201d240204010000075401001003020740415409030441d402c00c1422803c1c0003071002800b80f000f01002481c030416080c807050004c3c0040b07103605009801c507000b001e841542410f140e81d9901083c0d84951203440075206602c2d42c4140221180f01e90042440380074054602d80b68211404200d83c1d51354002d451600218000640224030a4400800e0320b049074401c0c04000002000710050310344032121000c00500b075580515112081d9100c608209001d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 270832203 1250 270830953 270830983
    0x30b0a03151d0d030b031009240c0c0f0219060f02100203161b1703010303110a02010f0309020604030602040305030a0807020307020a090b0613090c0e190b030405070305 74
    0x1505201d0740e66000c44030412080000501c03102c080c0c500078200010f4980c01c0d41000d050006080103218006840d0007540030381c0c4881542001c0f9110200030341000f1104240307090700f180d03c0024011200d043c06072a203050b00040000c010042500105110b6a204400d46c0d0001d0080103500c0381c0342e0b180c000c004280744c000714003049141004588050381040112202620a1011400d504003200c081070010401407c03034040182404050007051003000c0c0c0b81d030740c2d41d1380070640c440d050300c140142100340d410074072066020654503400c201a800c80070841d035402d594140e4424064150515043d0010044050180d070018414031000c0b000aa8034401040918060030046441d550309001c010840700000340b140d411500306004000068a49400b04030076602003210100b00f00c0340b0f842c081038950081d5a407040c01c812248900044003542075000c036116030440d545078003000198505014400500040008140212602c1000800381290103150401c1c0301c0c1c07007a00e6545589403600c03460110f55044c0c54103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 270833453 1250 270832203 270832223
    0x13080f090a15270b0a02070b04090903030605010509010819110c03090f0105390102070c030201090911040311040e03180307150e120304090c1218120f030b0a03 70
    0x5403600440d0503404034140300c500314185160110f03a820310302054030450001035404a10400c065000f071284202600c0074882542e1a1a42d0b0710540d00a00001c041c2a8082441c2070808940e5520900407218040310603101da4040780c40d40070340c4044c0c2881d5800350b80c0480b55140e0011806403040c20062020b00a200c00035a110003c42003009551113800304103e0612208002c090480c0951810b40428600c616a903410021140302030080c020008070101c00712544009514000c0190b04409081624001e903510740342c00791039500043c01c80d815001e024400d80c100b80300420014140c00009112004060004280303001c030b02c0f4060b451900300c1846c4c84100c01a40d2100421800c0400070312008145426951820041c0c400c4050404840d540c034050245e143c00c100c00d40c141c8000c0003103400404a04108000c00c4080c07810003400c8000e01d10314001c403107041c5a6440361030b1000b903208181c01074004100e04039800c81c0b400107480c0d488100c410b0340306158840030318000c107036034030940c031002980140f04541e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 270834703 1250 270833453 270833489
    0x801020a09030b07090302180a180501090b07050c1e0a0206030405070603140c03040f0f0c14010e0a050105160303060306050a0606020d02070602071e0801020406020304081513080f090a 81
    0x8018100000c0800e0108100c179641080543c5d18031003484148140103003200d42c5900d900da500340282200201c940c28200e40702c0c201104005055100007081d5000c8c01101c0c01c5501c8050040f140c40c4a600440680c40d800031100180001c080011074500125840803262409002c1e4013085c20b9810450302a14650803d94041100a4150255100740b01105614460b40d20300301182200500001c0d20103000201215034600400c44110310b4102c80c160484540a68107586000c0c4402c070a10f03554205001503003c9082a03d141003203072240c01941c1c2c2c140c44850070652100541d24a004c1d24100980c105521440e000010481c184242c50258962a0000c1001c0781041000f07494100d85482040842d4440c0c0f104000c00d5902065900a0b501c2002c505e41221820707844204214040303410404c3c3d294400100015032640000040c41140c2e0103100341c42c158020424960f05c5848126070f5040c040ba94092110001030507a8010054940c61080060800c010040411420041500a0040e40c14140c00039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 270835953 1250 270834703 270834713
    0xa020408151b0a050c1b030106050612280903032702090a050c0913050603071a040e0c19030f05150109030f0807020d03020c0901060509101101060801020a0903 70
    0x10103002021a8054031440c00d02c070001030b00103903049070b624a00940c0810f25010043c41030003280d000000316421078140807900d85000c80b08200c801d005511030341c41d06100050605007403090301c442c01e904a501c4030ba55030b6005008440700900d402e00b164182950707155282a00380502c10086032038060707078002822805a00c0c030081e001d07410031909500301d03038072101d81c0005079903d0040e10b030b06c034100803804251900d072a04251114041c0420080d071000b40700e02640c4081d0304640c0200d01c1848200c0c00c80360283d0741c84403018591034500c84503c80d8141c00300000d010070024003004a800c40008040c0307620748008444410f003244080b0a10400094443c021005902e0041c0200354200c040c81007200c2d82c403480312001070203504551000130b207245010038180e014481000140d42d0410b4000d400984401c4c0070340323070094a514241890510850303200002044861142e401c2c1e4040d00d10280640c0c0c215600e50500b03485403603401161060b203640303d040103d8100d000780054134503001c2a4440c110810304602e40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 270837203 1250 270835953 270835963
    0x803030a050709081009110402040902031005100c03030b0d02090f090d1e0e040626010c02011a130f1a03010b03030901020a080d0e030a200a050d1d04050a020408 71
    0x403010800c1681803060080b0070005c5541190100600400600b08286151403604010108082c030380c451b1010a001940021503001140700c2c901400586072075948650030042d410300700042c2c29002a40902c180e1700024085c0e031244600e180020204003400b02c007940041c102d404212105550320340d60106020200604116000010805080c541d00b010a00c814a40810030142c010700c003046071000d2125005d4a40f90711540c00b400546099880c807640b000303803003268640d496981c44515071900d0f102107101031062040c1040242c95041400310b000d00c020400003151021002c2c2102d4a40d10011411030355000e2084505e82c55420041c104010881020107085034000011103019401c20000d0102d16139010070510f8203943d201d610b80b85c50303414428942d0014103e80c09880058800001c0ca2168960414010b8039000c01d500f40c200031000e02c0d0300113280c0301c41c2002c2004081c3c0d8000b00481d400180258030718590714515590b2002120300d0940010103640307043e550300300c040f40c2c0007400340100c0748180300e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 270838453 1250 270837203 270837211
    0x10302090a14150f181603060f030b040516030c03060b01030b040e0609070f0b0d020c070f0305031b0a230a020a03110315070c1112010518100605090a05040611040803030a05 76
    0x80d034040100d0b540014103031104c0021b18001604d034221011404d000d000b94020700140036240aa51342c0c0540307c0c03404c2c00c8180c170141c8080c0ca0724030801c0b0308a01c000c0410340f080c00c103881d840036402d426140b550313480c8070141622408803814552582c2c00c5d1a070310b0f00ca81c8544148024004010200c6082c11060300b07041003900c0d080070180494035041440401c0404c004c45d12032800d82400145d42d400f020f51a1400c0084a401a2010110400b400814864000041c01161541c01490181031181c0392881d55180b500c0c00004100b202040100e104884150000051005883c030540360403110b1580021800e00041d041124002d14012418850741401c01a1602e1440202d240a019050810020300032504400001306078080351003c2903200d469841d4000e01d0040d190009010904000da40c6072549074015000c01058403414409112525141c05900d08946c1d01804144140e00c17440000070180c2780040c026140540c0f40c82451000000d4000180018000e82001d9a16400e0148a0038240c80d80030f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 270839703 1250 270838453 270838459
    0x2703030f030c02151b0f03190c020a170c030f0423010206011701090b0702010902030c040b0604050402033606010e16110f01050c090102010e06010e010302090a14150f 73
    0x191070380220b181c0004010414001007484403280765942042c03241e01040d5840c0120074890040351181c17010a14201031401085e100e6031400b49008408030781e0b0121580c14007801b00607403005182ca40410204842c0c0c4004480100b203441c079120a50713206900d1584003032461051100c0020301040b9001c40780b480c0c0002e2240c56a450002c1040b240c0000b5034a10044c042c20b46004c0c80540101c103051025807005002030360100160a0390f282c0a400a4000c2110700d505030f0003401405c0c80c1120300d00d00b510a401480303c00a00880c28039003041c0500000b50401058202480130040500ca0042c907040042000c0343c421182c005130402c02058120b00f000e0040c0e10441494001d14184154041980c4e80c0d0401c001c064508041d0a0100d59001491304102c10802115035180c070050202c0140698020448420280c0091050a4480c00382030740d20f0009218504e4821044030040c001842c01000040d041002440042904840c0302489000400d003618a0303280355800c03034808000f0f41003054111890a50807 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 270840953 1250 270839703 270839711
    0x40f08070b040518070c1a0105131e090515041b0906050f0d0227010602160f12141902040506030a02090a0e070f08010c020f030415030c2703030f03 65
    0x407003c5510140348011382000020454000380605110340300d041c00d8550000b0003281887c503c84085403041000b03004582c00b5108602c51420321000c40c0c0030714503603215480d00966a5040540504004201c1024115258051100c0c0301c465200f6120009001318021100c101c1d0100ba480a01605c6090307a500120704181013400410140d9111075031613503000c40c00c0d100440007140710702c0022076803d104981b0040a4442000010911907440789141c141c0d021a001c0303d0a1a00504010351411003034410515841c00c68882401300e00b20119070401c419204521080c00c0306901268141032045800e025000e0102500681040d46858000c03603820450940103803824580503000305084501c0200151030300c3d07450701c5081890450403c0943c00825030155641001c54590003401d0291101d00303042e0005100b07084606049210100031241150500501c420300b01e885250141c01030501e48a90f0b0084c418200208e80c03001c046014402000c03105489050540360651801410324130404460000b018a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 270842203 1250 270840953 270840959
    0x6061509031e0c1e010503131202010c1d0904080a0507120503060a0909120809070b040602030309010605100c151b0e010f0206010f260312040c060f1403060114040f08070b04 76
    0x41d410388121044403c6c6440703135407680e50410803603020404c910020046002c0b0294022926030640c040710050059540e128036551020141c5520482c440c0800d03a0b004440b500407600150200006100801640c10030078188070440c1ca8032913010020030303542000710b40000100012446c00c05111000b40c260a1420048140300da22410f0311380c02110078000a010200c07010455004042162800400041074801d43d04c41c0c9894009449401c2524a8100c07036080100110b090b151034003015a07400b00303e640351220040261100c8070941041481c01c0c2e070899079003081010115110020120f0800d04e9103904841d0069040010404100586100119040039005101009091300800c1c202c1d6040741d5549411100c950302c404041621040403810b42c8000185102e500180308180f40c8540e0040180c1c05100340e84100c20386000280c00726071800a0038100ca03a04503140007030041c582190b0306162108421496605401c1c084c3d00c070390015080c046181000b08190f080811030f00c80a130035004481b40c01c15103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 270843453 1250 270842203 270842239
    0x604090c17070f0e0f0a0b091003170703050901121803110f070b0a0c030e030109032d080a0207230304140303070809040e03220906090e06061509031e0c 67
    0x503005d0002c0710300b1030a06021030b010450b55042070050003001890b901042c180340c1c80e5200c4120061108441490b600c1340b5001041c50420150f401311505616003500e80349502c070045a0241d203120104195542d68010341325803039070a00d101d01006209444048000340c10380b20207460f14440c0c2012030380e00c0d4044030307041c461404404280c0c2d080306c0d064104000c40c0c0d046440c0950740800c0d030500c010342561a0041c042c050641c003a101c0d48030281c103004d211610301e80b20768601202c00314009005001c40c00c6400880c0c0301c040385600511216000704d2508842038444a21282d52030542c036422000d9520100b0f00340a2104180780076032080300c0480043d03140107465038411742c040c0191210349105950314040c1100c031141c148200c40b1500090007000140f4100c091400020720442d01980c4c0c0b60a02d410004200001c651150461551040000382269038a9004200541c1c0c032009003010781040910000195450420200b10701c06613142c0d4915031412603400c014505a244402d062150003003804e50034401c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 270844703 1250 270843453 270843479
    0x1404050a1704270c0f1704060e011e06060c020d060507020f16241d010509030d050711060306060d0b150a020102090a091a090604090c17070f 62
    0x50703803200c08140503003040d2140400501656100e107442d4001210382c44000a0500d990f070b600c40500c40003c0025054000d02200d0205031009414041811000702c0d215000a031011654414869807001c1035006405400c18252034218140d0032940344801340e1708800c001c4070700910700900341c941340c404032054880e000601071014504015120075610f40208040c0ca1080c007901c488410f03440304136855501c20311400403010b0610f2113407018090b9400e13000001e07804146041d85044450384d44404540185a68180311980c0d140001d40c140107040241605c1a1020f1203076804250841d143e50b40c0b05c4025041031203000291184051041d00c04000300f100503038a180035038030450071149002642200311008035044005014121503011401305030042c03442e0b4150001c104184069600030300b86079403008944261184000e1b00f1407000c07c0b00140d21038604041c060030344e205c880200041100b2001c3c6c0c59901d040062904540c0d00c040e0060403941950b9010060070008140e2a0b400f14210352138214004002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 270845953 1250 270844703 270844723
    0x105130b06030a0f030c030206071407020105160c0906090b03010905150a090b2403010e0705040b0604050a0906080d0f050301120318080303070906021605060714030f03040204140405 80
    0x9a540c40003003080c644041015140055000d1541c001008490034003511500649800f140107115607030020f200c103071140c082000d01c01038031603201d0b0515103942d00554803074212401030012050102d4052001c9480e10107117000030b1890640015140d402c0011000c1500c2040c1d0006002c0c0e03040111420020340d0001c1d030000759006901d503a9089403506200c40014140062001d00a0f80708941401025440308909081408940701d1000f2803100d60414142038510f40c148070000e50700408401c026605203900095100c082c01004145480e4541d40051103442c203580101c14000e590310400d11070400c0c208115071000a032400d040740c1d141807404000b41144414002c05581c10303150b0b842c503c2098021030b80718080f5084480075144650302d681c6002e0342c07900300322004800100e011304002802030002c200384082e844214406c4c21103e0906041c040b0a5010080445818101d003896081540d800c9c0090103945134040c420701da480c05d085c0100029140f4250f0030001ca4043d8a040c400015030004031000a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 270847203 1250 270845953 270845963
    0x20307021503040c090609020a03050603060f07120204050607060c020c090c0904021804021b0615010207170319080703060e0f0a09240617011112060d17070c08010513 73
    0x2d00d0383c0c1e91900c030310706103019441300381d4080c1452408110400340b9006031441c181240da01f04460359850303003007695455060750403d03032000c22a404162914070844043e0b940c01d110200152400e581ca10100300350703038070964040d1889a941c5088401c55075041c8440c036a00c0d00c0c11500702a25040c8031889a00340c0c03085242c01440366a001608891403800c1c40e13019060713a9002803003152105482003c00008080c40c034010901d07405a2000a5020b16494415040034807042c1c0c000c0140a0800704e03030310388144080030030100503c4107100e08401b0002d83d880721602211140d54032405401c203540043d0686503250401a80c5060f10001c01a4582d059007046070b00162810b4040382c071182504001341042489140d0941c04c00440810700340d441c0b065000801110f400da04240c0c0b141000307500e0b507800c840d003001c081004141d041014000c4007140c1c140c959000100202003070345070307501656001410a05031844d40c3e1202c50108801d4240a88600000d00500501c402400146041f080d450301150808100800c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 270848453 1250 270847203 270847207
    0x7030c021207240209210a020d020d0b010b0c010b10050a030216020a0b09030609030304080a0c1106041409131104020703170a06031b08060610020322080d0203070215 73
    0x501a0702510354100e14040014071400103c18150000a1351210f00c2203130240401d034400072560b010500b4480030f40ea0031752018082c41440c582c00c100301000040c906030791110200c01d101007c40d0010b40d060380208000404159500142d01180d03003940c02c54160729106881d50803101c1e99113074000d42101e090010502c3e005a544c0850b04640c403400101200194111280c2c45021451034510001807658050890403140c003a0b807504034160380c9120840e001440500c0a00c0320340c000078040d09814640300c1c0b044003803221744051705011032201d0b08a03900406200030204060003080c00c240c080715401034041105240000f00c0b54840c04000d01d10480c445000fa81d00042083c103161054841c5d44410018041c20001410300032102c0001d4100c1c0d00017920200d0041c400041d0320791049510600320340d40000640160380c4c0f503104011100607070100d03600560004105000b1301c4084040401110b441321001d0380a0907062404c2140b0340f41c9240b610000f95071081000c03038096581c0e00c4103807a9588001d000b0a07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 270849703 1250 270848453 270848467
    0x61e010e091f060906090501030c0519091b110c011d03032b06120c06051e030405010c2c0f0f030a03020106140603130213021306050d0507030c0212 65
    0x3440c0481010740300c001c20300b1554042c010011680c0041040b108130b030005101e0507459070140001c50358288401011022401002c03c05414141000b21001c1e0044d101c00702d4082d540c1c0285025500b08181407200462002110014590006920500c03c181000142200100d400019203a41c2c150420860580145403100102d40d070100126158050f488006a8115418840302007103030760b5440368032160600306900400c0e03032211421010170260304158411011840d0060070307200366201d8607003540d00d018401d0128082840c2d01000f0341c000c0344204000184803138200b0005000b01d02001c3c02c50700c80402c1e00030090f000c602031640307020202d104a404441c9881c4050001b002e1343c0c45c40d001035425002c0c4a04040c107054040d840318007100c00803480f15004008007010001948400ca806030300180c40c80303e2010140c00c086030110f0b51106450801807130290000b03e1210031046a602c1070000410005484600d040c00e8028a50800014101030046880f4144040c1d00d810000d90704200781a008900d007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 270850953 1250 270849703 270849721
    0x807030c02150c0102030114091b090604030b01150f08060d11031603050d092129010b0714030301080c0d08040e190b030f0c0d0609020901090c02061e010e 68
    0x350030540d0011107680e560b9803610038031134007030340003403092400303400088090089905060711030600c42d60403d4a601d00700e00107070f102c603001c5d40c220040494001005010102c0007966003c44240600803140a0207a4ad000c1c0c0d420007420b20b14050149410080c0300c1c0d090018503161120029030321a800aa8118400a42c00120b490314072482c000c0341192990041c0001402000f04554134031590710340e10f6050181d104c0300c0407266001821007030f6003d0621a044075003c90852004007403485855000e11850380700030903001007a488280c210300596440041c00301c0070420140c3c16080c007060100043c42c25580361100c0756841da9a40000240141d03814a001e0040020300c00881d0041e041190b0301c0e10441c00d1607008004968808044039100d039183c1008910140b40015194034008840d5009040b400100b909005039001c4106048407004e440316080c10040ea5580489400b91205082c0044c01c42c40409c0020310340000900088442004118150345160509189905490010041d58459120300ea00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 270852203 1250 270850953 270850969
    0xf040b03010e24070e211903020607030b0d1e150c0e0f1819180f02090115020a02010309080706090b04022d0d08040305060a050a11070807030c02 64
    0x1803180316020703a2807901c0e0302070f000305140d0381081d544140b16522036940c0f09007078452140781c2c0c808030703070208450b80d4901d981030b602000e407030004085d003050b1349613000c42d02601014484400c00440250700120100400c4550503c00e0001e40c800c126401416003001d1313200ea00c00c014030043c0001d26060381c22211400d01c0006901d141c0340f400b20110800c220311844000030420000c20019610500007031641401e82c0c98140364011400a01d00b264000540b07690b101403c035440480d91500603a9101d542d586a10544480c150300d00d5130180020401a4002d4410059580c0058005400c025140e00c01d01c1d5025500140b858003165081c02c00251804460030641c0d210b00800c000240610305000d640c5003080701004655004038800d540b181a42e56036810207440b8110081800540010300d9100c60760075203000e204002e41035010b090182c0c5041e843e9261701e070501c1e03c2100c01200c81a116018840460150b128040300030000b00110703800c14a080d50780c05018420f8000190070840000060015507540c0380e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 270853453 1250 270852203 270852221
    0xd1d07060903020609190806011404111215040c02010203010911041518030204050106210203160c0f1a07180b04060302030a15080c030f0106030201230904060b0d0506010e0f040b0301 80
    0x10f0846d03c02586d03100110b030b460009005288503034600c82094401c500b424003441d881e031194a11140d08000c001508112550b00082c100090032031706011202843d00c442c4a00400c800c100c0d4000340c1d40e07604214000d0151211802d00e139000c100100010020710422181941c000c01991420310006070710800949048040341d00041d52051a010000641a4002c41a240d15010701c6914078151282c00051500724002150205221407051206078420351103401040852413084144620f44d00c003a4860014400040040307201c0284284203104080d03822034840007080c01c0321501610b666042c81c0443e4a80e000714400d0300107140c0c011001c10b04000302c076008500c1e002c6440042c02012543d038801956a0700761a140c843c020b0180300312040d0801d4060081d501901c0c0c060310740ca2202d2201542d00301c0700d43c2446a40d1030024006002901c42d55455005941c0249400707a103040e121140200c1076170032035401030b100d141032010280c0c08514546599101801c00b82080b6000110100080702003030241003861 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 270854703 1250 270853453 270853489
    0x30403050106090e060a05010302030d0c080705030a090302090901152606040507090608030405030d08040f1a010603140f07050a031e06080d05040303020a020f010e03030d1d07060903020609 83
    0x30b20041035400d050f511800e12031101008032241c0742c075010b240c20100c031404c2c00042e404d60020008600424024104960072030720808486160149917103410b800c3d81c00041c00b200026200031010415807a14541040d048071504008009210b103079800300203101c01c60310030306c2c41c043c400341c80c011081e098500e0403207403042100b02a1980303443c05207481c40c0c4400c02c60040400c0d0915207140414031460002c242c1d0150744001d40107028450501400303403510301004000b22802c1c152000c9000001c0c40b43c0c54101a20752900001c00102e5050a002506a8100c03c00501d2100500010070480c4084100035039004411360410741d80c0c3e0b910380c540840251074420303115a0081c0c41c8004001d410b44980d481709045408030010749142e001e16910480c0e403481140700140040c1c2c8070f0425403015140100380c407a1080414144200c0c1321f60440040f80c110b4002d0016091040d680ea22441019007180c00d91070380d5680c000010f0080b150030900c002e04095060300001c1d000d100c01103150b10300781d01d540f0140d00900c1205 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 270855953 1250 270854703 270854711
    0x51e0c030d0b0a0f050d1511040e0f0f040b072d08160503040b010b1c1b02070501030e15090114160f020a0b04080901020c04020f120903030c0403140304030501 70
    0x50194200070780000302206003d0546803500103800b51035a1000010303224010108800080c451b03c03043d06009681c500240040e5a502643c003149401100820040c580111a4200c030b1901043c12802060000c101044104c03d6000f0403000030410b84c2020750001450130304029054203c00e405c0e4401088244160f4001d1501d0990200c1c640c02186562048000d504009040014440111014001601c00078680452140140901034000c009400c0d900801c1c40c8030b85043d101180008203032401e099040010005550410040581c1031101b140036001c02c0c2003e0099640e4509000d580d0321b40448260390418140003c110200420b4003c8030368491111050a458180320004003107000c0c224030b40102027100e0102d604052400425000203254010518440c16a100c1d1580d5025a200c011460704602844114854a82d22440500304100d401030078180c5400c00c070450602c102901406942e800e5000307000b08907204954000326000c1c0c0341d120811002d20b03010001d03411701d0b502841c1c000408035424 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 270857203 1250 270855953 270855967
    0x3030309010e0601120b1306020d020307030903030b0306011a0705010609140105010f090e0703021c0606050c0f01050609041412040902030708060d050d030b0a12060e0601080d051e0c03 81
    0x150440b40346946030b6419101540d03070b05c803c00d16070000c400600405400f13090b00081d081541d030400d12100305015007405072500648260302070481c1d000f1181e02c0e000c00e59a40406040c140d01d442221038a5805074024032295041c07000090350030400360380401008000040303079402c0040a402000007400000024030410046405504c00f6000034058240003503500d1106601062250031684102d42e03072100e908031a5100c500d001c6005c0e42c0255140c0070104e00c020b42c035210707402540c807a030f80003008103680e071984a80000464034201204240641e4140e03041805110310356503401001a0020380c440c10b21b48a0803141d190050130600040540000d1190200b40028505420b030020340c4034081c80d540d03003079081d07403000304000f80d545556402822a6100030100030384c05000354080720300f9807001403140514550364510364091481c4c40c0c200b105e01c41e031034288020413400104035060150070590050b158000060070000c0840c09004400c4040101020115201051401c00c5820912060003901e66a0070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 270858453 1250 270857203 270857221
    0x10e030601240206040c1a0f1606060803090303030a0b0301091a0412110c040c020309060c0c03060603010c14090a0b03070314090309030703150b04060f08060a0b0f090411030303 78
    0x200b0760045500c00116101c8900c110742c80400c806110f1a4800521400682040c0300d902410102002c0118516020031060380c1c00d4010034040c03d6030038120044500b02d904d40740741542c29114988d100c1403240e802400ba4400a56001c0b003900e51000a1142c00500e4165520002e80035181c1003401030040f13050003400010880344810304074860b500621001204418110007200c803904a140301c40c1c26a000004c0c411003914060308a5903144107544103d03070070320039034a0000b9120350100142e03010a52094403241180c1c01d0920170a81c0c840012002006448514070002c0c00440850f80c10203510b000c0014403544541c1e039004007802428406014079182c0c500480701900404000e04442c100908071800112040400011103a500310052301030400580b07540c0e280c0000c10002d042d816007060712a01d5203840354036507101d020b00515012003e040f20301d1501a1950800002801c104103450514580c100f4079200d80607414032982d4281c0302c041c4540d949013454806151401072841d4180000400c1c003000d030b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 270859703 1250 270858453 270858479
    0xc04020f0d0c05180f0d03180f080f120a0212070602041d0a1d0319170c030714071e020103091401020a09091b0c0f1b06031d06060906010e030601 64
    0x40d61801c800d41600441c64100190f1305c00d1030f88135a0f40844240070310780009210740e0901c11010742035002039003400d4440c89540b08581040c1c114040c01c0d4882c101c40a82c500c400c0045a041480d41010f440ca4190100c4c0000d4131229020341e403440d50175001500030100312982c2d0444e00101500f0a00d100188200707405135080c000c0540e072400c017890034010554501351032100786001080c2854003d40c0f03803c41800c42c5c18000300744441d041d0140300702807600d20114100c80703800f684600b01320800d1507a03038079101d140503084003151403060755125000d00550000800ca0020941460841d0803401c40200c0c442c0700403006403800800c0100451440c0c92003211341d100540191074690360907140d1000b442c0d200c541120440790604000210b0540700c40c665000c0500455001030018003c2c481c00030305004a8035512240401c044a966035842c004000f0441ea9500d4410b80725040c000c680d500700c0320a500841d49a540001800140c0b150203068081192a8001e400c000302c003042c05800e64081c1c3d81d40e859540c51b81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 270860953 1250 270859703 270859717
    0x903020a06030e0a060b0a08030309010504033906020c1c080105101d01020304080a03020708190b0a050709080106030804031a060a091a0402030108010b031606020c04020f0d0c05 78
    0x9203041030320104078540680100d44003c81d07010300411008100b511000d000d040f00003d0560400b41c0c8510104030000b041c802184200c25140010a2908181c40d0040182c1c1c16400000d615840d09a466a13010301d009240700740510500c0c186640103204c40c05c041c07000f80304044824001d8401d80d46200f81d032407400e480113404c011080c0c407858020fa03a160180009480c1b030309030140014680b40c2440311443c0402032140710690301031040764101a1504a01450022040e8081e80980e01802003003103144410030440b81890310391140044021485d80c3c9600441c0b502810b82007006484400082c503051098035440f00606800000740000b40e540e08062203281e106000603a550b003852a40c0481e40d40c55201070f14000c041c00350003c04034070310f812a44001420109584490f202045c07046003215a103e0020b10b0103048154000905039003058201072801003400d900200d10f000c200d0080190f00c3d0040b94042c0c01040646002d60345030b855003a0a03041d03100c2c86900041e5603160100124456078001e0241c862 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 270862203 1250 270860953 270860959
    0x411101701091107021c0b011d011a0318151f080105070e100203040e10080c010806030705041a03010204240e03030426070e09010c0e030606010e0a03080307090302 72
    0x156600d9034082e03410b55252441250b200d0a08000c020014100303c4140442ca152100c0c0e840c107107051940da054048802a8000003030503128168040c1240380000500d0300622101c1d503440c026803605500e4050310b0000605a0045c200c120254142c561010f12607100702c078055005040b550324210218420003c50003603c2103040069040114424a0521660740508050703240c040060700814108802c08164191010441c0405c4c00006100c01040707545c10302601c00c51014400701810310232014039100d1401c01c42030401418400713203e02034801255081c1a0350040d90085842c0c810200796404103e42410b085e43c2543c40020000340700140010070b040d030b44c444500c0c050042486010104c44520f4402c4400da89508200010004d403200c04080c181c0b4292198100d40034241d03032449031400c06000c0d0703200034042ca40d08020003043c1d81d0f080c45142d00c070090b103060002e880e1000c900440d503140e5004004c1414088848640c02003030b501c481180004551182c042d660324a8004001800c4802c18441280 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 270863309 1106 270862203 270862247
    0x11090a020c013b1e15091617010204030b0a0e16030b0c0a091d01062c0906040e0d0309030905040509030d0c1b050703200105030a05041110 61
    0x601032244030301810340d2a581c0d400028a174240141403800300d4222142007140006241d0220050f00c15407180c4040055a8504460091240340c0000e070041c4103a800b04100800a6008200c1c00c404803405e41c0e00203030b00e1140d184000c41a5001c0280403490a0380011900e40341c1030b003c1c10340c218503864890815981c541d440030003290a00f2186180c80d500500510206800c80c3c10000310f654001440301d0528501d18050039055541ca03401031060b100311000c00e003030383e0b1140c00040d82c60f941a0203071104400500c502400803c40103070301b20b0119814070f400240615240c81114410025603010714a440d14851a0100824159880b041030046a000780781c1030030b42e0040204074141c032902c001c04816085041c8000e650444852482907001070008811060340d0083c00d80e50407044980d00411191194a00302041c0307148803d80c150807107192400b54094a03484400d8568130810500441 = true := by decide +kernel

theorem cover : BRFrame.Cov 270683453 270863309 := by
  have h0 := BRFrame.cov_init 270683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 270683453 ≤ n) (h2 : n < 270863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
