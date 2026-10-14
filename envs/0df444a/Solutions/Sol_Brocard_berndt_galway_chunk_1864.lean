-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1864
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:57:08.198887+00:00
-- url     : https://prove2.me/submissions/74ace89d-d2bc-4c9d-915b-58af30ad354a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 335071942 ≤ n < 335251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 335073192 1250 335071942 335071951
    0x71d06040b0912030406180909081b0c042c03030f010b18030a080903190314090402070c060305041b030c0b030901020909010e1e090d0309080403050a050105060f0f09 73
    0x601d00030407030b0862a00c6158200e01d1041e10f4104990f207032940c1d910b009080c1d80768040b00c1002600208070000c0c100c4d100d4002d4203107041e4000e000c1c1e4106204807851001c00d50751060516a1f9109001201c48652160f00c42c0c00f2070036107114a044141c1e1035200c00c04081c041c410104c0405548100100108919556140b40c191203100e5081070f900c89601c013001c645c0202ca0011198140600c201c1c04082009860040814040c00d0b030680f603480b000400c610814041148018002c06c40c1c005d0715920a6a404c07006150914005100604081c41c82c0c40da600d051405810030000710341e84500784424820103102003c03520603802020b1000e5030035640c030a010304005108176800f1031000720128503070080070f40540d14241c40c0904040c58540e590001d00405000655000000e0062842c48050300313900700148070320688051001742035070f21440d00201c00500400c1000e90318024280000f0000420520003064001c3c000c4001107140d04140c42044030390214022040d1085641e040300396429114800000d0b8403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 335074442 1250 335073192 335073209
    0x270f0f150309052103012402100b04090b0406020c010e03070309030b040606090f0603020a051e090c130603060e160806040f0f2a0512010b0a200105071d0604 69
    0x40c440b591034020300d0101100c04030b4003081c80316000503080380e1300100030318100e501003103600d0303002c00c034810166520302541c04080005070445451003142c1c10351a0040c074000c82014000260498260b100e0b03e00c50720003520211307040d54002400d0001181d0034091039844201100103903181030010f0ba8084c111494901c00180300c91303441800101800502c0c4c0c4490f0081c2801802070017140200c04030f0b00010902030000b00d100b540000c0c07010883d8209405440c2000b2041070011900d064020704200c8180c800902080c4c035030380c081000c04000381011882e070000382040c1d200491150b0a0403006030301d44a000381030545140e200701c001010b19606c150499080001524000342940103031003008042c1c078203a0380c1201402e081c400c44030340444c401001c80c00b50b0100700f410000004501d0b0011501c0d0701c9060003618464604400600617a990040144400b00460905d40c1d500d5020b07800740c030f0003002d884640401e1659100c0400441070780100c0050034118601c4280c40d15455800c001403c1030141e806040700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 335075692 1250 335074442 335074451
    0x1401060c030f1704080d0606032c070308120709080d0c0b0624130b0304020a170c1f1707120f0b0a0e07110607080109020703270f0f1503 60
    0x942c03d002ea12514985442c4000c0030400340380a081650555101752641640146010f9000400ea031013481500c02c41041c2c07030030791021030a4040c5071040703c00086005050b94000c0690020002c0c0007a8010007800c0e2080c5c00c00140c5203007111000e04040c60708d520082d031541040020000349940000c03445d2205601c4500e40032191240d602103000e2100e42110903071001055034440d40c0c180401b0300075280740c02400c10050040b680351048610340340800d440094202c2800801030103c100104009240c0c0d0b8006811940400f55510008000d065a51000c01d505003d618802c00da080c2c1c415030840d901051700707040781190f09041000500488840141c01c030000e940381d48401210480c1d80281c000741c030000749080b0180f625040c14080007074040d505540800c03541c14140040b600082011b0b440364045071101c0704580c1c0307045801350287d80440021001c00c0301038603144ea2010061208410040c0e80100550802810002981003000c00c4c3d402c050903d8248020030000c5090825402c6140000c0340740116 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 335076942 1250 335075692 335075717
    0x9030f050a021609020c0d0207150e15130e0112020a060e130905070608100305060609040c030803040614060105090f060d09050607020a0c0b121f080307080705011401060c03 76
    0xf41000f00c401c0c8007000419a0a5000600c03060a401822000360464180e58901619144c03e0b6030f1550113200c0c403010316030444a660b4400e03004102016001074080c04020030304460302001d002c180d00c22280708040081032901404121004401113001d0061285120310240c02900083c80c690200d01c54141080f86804a00905032500c5045e1004680d903400144541ca141d440d059817641040e0145000003032045000400014200c108003045070b8003d005090f071600c1c0c103c00d10150020003041528000c035045000000120242d005500c62401040c0004040c0200410000701c0c820241c41c450401000780710b040450390700c500c072185081c2c9086480660304c003c4819030030b005c0d0103130348005020350150b03604102040c1c3c0c01103607810704248600030340d51074151a4003280072a4084c1c091002040004000001c2c43c0240d00d0020040b0600c048141c0d0a0242c0d0b28640e0b1850740d440a60101d030040c001141b9182004000d0040c00025101e00b00c0030001d640c1099001803100e05504000b03000c02030b0919110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 335078192 1250 335076942 335076947
    0x9020619030f0f0e01110f072a062708070b0d0905031605061b030a0519020d090201091a030c0307090e0411030d0215060d020f040c1e020109030f050a 66
    0xa01c420480c0c0030a0003c0020b20140c02d00801407820303011125420030000ca111000300200b211303400c40040f00e0590a0074980d480e0355044002880d94032405407030900080005e41110314402d8014019075484016008181d95400881d10300d0580c00d40da00e860401c024403101c5004503901c1c042c0c4008550a980345c41e1032034040000351040d448040e00600001403001440003049800200580c0210704841c600c2e1036225408401c05400d495030a00c5500600100e6800410340d0056900815030001e06010000c1c0d605110003264000303c10200b03402c0e03503000044210f50b0001511001410040001d0b60340086191140d1a00e21008156411005001001445560003180010003412549035180e44528052030414924801503030740030b03c648079401c0321040d040c0c400240446d140502a81d03024050711110148140710034509000c80c0d00441d600050b050340c0d1540d12440103502441e03543c1961200801c801e10194071b0340c00240c1011641030541e0b40740400e400400f19089007012f031900b2a5074108090f404c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 335079442 1250 335078192 335078201
    0x402070804120b061507021f050c120414030c0a03060b0114031e0f0403020a0213060b030c30190209030303090f07060f09030b091e100606030902061903 67
    0x410701e280144514101400f0521512610a010035105601800c90095a10006010b40c0c1d40c02503202034035403001c48200c103440b003480307854a01d503090441c01c0081d030100150600c075485c10b091001120104040080540098041180350015070203404240d1000002c00c0c074400003400301610803500c41c80040c1140c1d1050000c04801c0605501d0251030341805203811090410322411180c29200b0300010901d10340006050500030307035254000b01030500740c0e58240600c910f49998001009540d907100016018090740c01188501d427040c000b00d82d0303000882c1021603244011144541c0686419030005503910729818219006503c4c0700d20507807020300c00b800000182c80794065854141c0004001d110700100e001400155140e00e07403054805a0303859100460f0490032616043c4001a80e096040020480c40c4440d550030a480a090711899040221a000b801c1c28003481c00201d0341c07050b01e02c10031442441c030407d0040c052a1a05200300c080680009010307001c1e02c803030704c080400031100ea003500d21b02a500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 335080692 1250 335079442 335079449
    0xc0412140304050604081006050f0f12030d090b04050d020a0b01120215161a07020d030b040207050a0c1502010c140a020705031207050c2e030905030301032306150402070804 76
    0x500e41e54031b482d219003071740b82c00615014200e0326003000701c041800d1500f224100c3c400d05000e8100c6040d140c1e0305080220084c030004110302c0c00d01080111034030041180c0140c440d0103000705414001410145011072809a81030400021074120118140006401c00c0d04641113075443d051042e11400c6a000040400340000000318101200080d4000e648441510f80303d081c502502620301d000036010010b24488a085a00c500140c00c040407414803c0d006c0d03070000000c88009800103080c03070800ea4480d0f1130101c1c00c081c1500c0c00c154403542000000d1008105105c3c032405803000b800320603a20300003d40b6182482c140b044180101044984103203200b00260b000400700282241e501c0004030a200303010703070f0103100c081c0c0f03c0307010b50000c00042d810703e80440054800200901e5004d0343c5c1c0030010b0008800e40c0c0e209801016114034200d40401c2040000c8c6001e540240a000900d030301151580c1581031140c04044007a42040c000c0090103428030381038000328130040e01c015070344803030030b10742040c140c4a41d40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 335081942 1250 335080692 335080699
    0x9340801061103090d03091412070504110c070f03051002040302010e10021609020318073b01030605070806090f0601030c022802030c0a0e160507060e0d03050c041214030405 76
    0x10032078400d255101f040d4004584400180b2140030200c441440300b00c1c540c070b2118040039444541c0400c03603410661b02102c6140c1415540310304200480801a00306409640608900d0950351000e00602c1800e20135007141c081c907030301d0440c6494a1940068915181a0341551003510500c0c29151964000d03c410030318440060405600141c0ba4106007001750001c1d01c66820610f0760300d040b000300040000d4944103a45484241001c080760a103106c0d840141e9194558001800d2961402450030420200b280611b00c65400803549e8640020003e1120310000c01130b030300c505268818850082d00101d08240c02007404e10b4080b4415401c2c002c1642760010441c02056481514000d801850407508604405d10380308506441054540c01c08000c0481d0450103644000c441360700114003107071000c80b144051101541000d5081c84400e4884100b2681c4240f41103201d900862084900c041e03140c410182e102c60701d019075908050400c504814440c00c0080024030106020041001d0040204141e800400008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 335083192 1250 335081942 335081959
    0x1308070c06020d0c0305040b1e0703050909060a030b0a0b0f0d080403020405010902031902070f0b0a091a010b0a0813050604140d030902060a0c020d020934080106110309 74
    0x600c0c000394100d1003032041400502850003400a075503c9044041400e5401d5562503040500b440010300e030070ba2200032402c0c3c040c50180c0e009440508100094010507009484194488080f030f03017444650080241070611810224100748000b80000035003c1e008002d0010000394440103102042d503840b03441444590000608514000700810781000b402543c0c030a13034042c46180d03616050041a40400c0d103031028034a108918407402c0480d00d50180030f0351801181128040c0c031481e20340c0f42c1c0d1080d0656481814a464941841c20b00c04001d01440c07051580da1040c000c82d6160442c07540c0b0500039540f01d0801c00c42c158002c111200c542010f8400c0d16038006c000d8640c48d00b40391800d6200c800949040030b260b4050b910b0012010703030082c40b030700e4180f80e00503282525003280104100d03007141c41048200c1c0c5c0b00a00725564005030f281c90100304d00c50b415954408807e039401640380b28106d69200340d43c00d0541d01621081e288036902c4412141120200d051010040c804083c0442c114003444103003030b4000284 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 335084442 1250 335083192 335083207
    0x90d021c18090e0c01020f16030206031b0a05030406150501020709020c030d0c0206101d0402042319060b0301030c090b06070605070905091501170702010f1a03070501081009051308 79
    0x40b071284d450700c2c800d07000c94500403400200c0a0305e44102d000b035880041c0002d0810805401c1100007960b01038404250030424000c0c5080f00a40303900000d0761071000801c00310402080085034890401d0307000304900300b158410710f8280003e60b918100d01960b42c083e5000f00384080d0410081056031a460004442032005001300e490003952103000300d4020034503010007480010600d0010840d13080101d01d1004400540d600c80c0c003800064090086400002c00d0085008074000c42c0382078100d40550b40c404440010f24419052050942c1e2030b0340c10408c00308204000400015000c0b0549074102c0344840808a0031800d0321000440e9130240c4413000d0165414102000b021507480004502a01c4040302c0c0580d0790b0311006003000c0c000301c04d614410b01268040f00607000780040c3c4096542c0c4803a8502c000301c0d04440c00c003212420746000340c90980c07981403510342d00c07441c0d8981030001601820081ca068400c80c58010341085100340b1501ca0f080619130380c1e4021841071904e80c03441456145d0046040b0303542d03960 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 335085692 1250 335084442 335084471
    0x1214091210060e070909110903190204060605120604090309030c060e03100504020d0b0414030a180e0415050417190e0913030e060c0f06090d021c1809 66
    0x140030341c0401c00c0e5441c00c400403820810140103140540d00907038641c0c100381d0a001480b0024040300400d11540e400a220620507541c04010200164880200c4c4003425452417040c0001e403401c64020005000e8103000f5040f055044075541a48441c0803600401e04610714107098450001c40d41026003410340720003000c00e529400c02c078068146c3c0c2d0143e080300c801000d0109103e0031140e040e100258800203070100540420090346032260014054800d10b10101c2c566034070309195074000e01c40500418951221400b90300c0c050501c0c1001860048411515441d00d566181d00c0b92088080d503c1200e039541012400380003c0184150180001c00c030070b02d544401d01d640009141c0407070b000c0d00001400b82046da50660030402c8109005d40c00d500002c52080250f550150b5440e0010031400703030000e409008015514401b00119008019a807000d001e0074140003d107117040548074000720b0250340c42800c51348a1000d51542444080c0d0180c60150020010910130504080144d03016020460424201920840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 335086942 1250 335085692 335085703
    0x2609030703021605010504051e060d0906061205070e04032307140a08030a0c0e130c0801080d0206070522060201020c010c030515100c05010f0501030c050d12140912 72
    0x81c080c0c2c00b12050031807410307402001100d0600810f070005905202c1004981012069585140414403100c24a544504049805900554148010182c65202150501000348500b00223405060441018049180c54440c0d07200494403076110030301408000101454490303c1d103440e41e41c00800c0d00c1c20218481004e440f859802904040e0703072110590042000c041c000242400d242507101710183d04641d103040d4040002c120000d20141408038600d03103d603560340e800c0020024a5040c440c005070444944c1d0004001000c140c00c4040540d005030700c410015500000c2145c0d1000f49032070029a109401100b20080e0071410300303024011540d4000c04510907406401401d8441012070080160180400c003c40940f502500c03010344a0584280c02c00843c28002c840201e80270b59800d027850001c0042c1c2e01c69085501d4000b00c1c9071010356810050040003030048454004000440d5008080102c6450300100e204801d1000001e120200b481e4281050302542501c0c18800000c0074481c0403403000e2102a2102d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 335088192 1250 335086942 335086957
    0xa03020607030c050a0e100e0301090804081c0e060306040b102c0d020f010c2a0e06011706030c15180a120b060f09041a0705030115260903 61
    0x3a0901c02e83c0010b1a101c0d030151008026241e5130401196500d40901100551082c1c3c0002080042801443c00e900d09000e500d600341d00c1210420355440c500703c074072030401400c0e900442810000c000d84650450303022580410400007140d40716502c2d201d4a000400410100c40000d4200800036655201e030380e0408000c01e145100c15a90141c00c050701d0030411100b941040030310340c0c48408100741d840903040110800c0500c2c801030428403850309260715420044140340030007404e0b40c41000c026180001c61403941c1001040b52840745215130910000281c124000554600c650f40c50741c0c00011010360707040064815030304001d440120105600344881e01c007a07110340703856410140b0386540c4005c01d042242d010300444544800c03403003034a041d40d55001c000707250280503164460300d080000125907580040a50042d0320941600c4802500034908a1350030000070710340d0301440401e000400141d2079002c04090440150700d080032480c25102e1100804110005101007001d400004026000030000020703e081e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 335089442 1250 335088192 335088197
    0xe0603190506070e240d060b071202010b030102090a03080306030c091501030506100519030603080d240305071206110c0a020a0b0a0f1101020c37021f020f0a03020607 73
    0x40844000740010410020101804100000f1a640402c0e00c10005001044c40b98100410180e230795a018510320341211034182d0b840100003080e111a03a4092181409800040d4029800c0030640c1000034003608180c40040e180f140c0000000b0050341c0d082c000f292801000400c4003205040003028154001070071294540820f00d0702020802ca40b40034203801030510040d545a03458140e0b0740e2283d650217202003480d07105064a074180840003621480140c25401400751000079401c600c6007141071031007051800000d42b202010814400705101043d440b09480c09080140e004100301d280c044c00034203910311840a083c0e408a40102112004240340091a0007100c0858009446901c00240c80c4120309601005c240082018030445018651110b241030074a400103003000c02c6955801d0030800740c6070743e0034800303400843c0e50819a82840c840f007003c0074021001e14804100c0b603020660b010340754211020400100000905610304c02c1140041415000c803d0340d4020740c4516005e9901c0034140c514401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 335090692 1250 335089442 335089457
    0x3150609061215100f1a07030c020a0b03041b0905040f081c090602040317251109071701060905010e1905030a0c060e09040f0f0203070f30020a0e060319050607 70
    0x95080b015901c6c6c0c0020214480442e142c250b0360b0341e041d12085e070072540881e080700701d50034009060803148010750712907030095214900c5003500d5004425580d5035a0095008285000300b40004507050603021072265611408540d5034110222030820304141d1040c014940504003210141042026009041200e1044191000228424108416a0181e200c6001d0081c040701d41d0310070368000800c0b060352603600481e000441d540b8913501080009508403548004110100c8035825450103043c0c01900401c0390740f0b0815502d80c14900000c0031032140c180301701d10606000c082c4188081085c1004001000003c003106c6031442c091503c071010005502c103410105042030821a40b50a0802c4103a2003954803a40700040b032190b80e070302e0f03615400714440c1c180d0b0544140080441c6040300c50030b008014089810700740145102a0310640402201a84082e007041d50848404005072520f105107001d403592604403003c030b5131720b400c0400d1a152039003000350810707220b55030060107205011894900481d16603031040c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 335091942 1250 335090692 335090699
    0x40314041e090203010e0a020711060a0509090117070e060a090905060417040b0306062b06210c331d0406050105300c030603150609061215100f 63
    0x10b08900091241c6050411050700040381c01840fa0f000301010303031054070000003003c0200d021070b00c40d411503454403021400000f681c04480c80c0880040e0300500d8100c0050080c01c061800301e41d281c070b8080c03040e082144004030220b01c403581c2d294a104090303c4019010400da00c070505040eaa600401c1c8c0b070a5400b944c22030042806c1114140032a401e58505c8501c0030b14540b500c1d02407040c4c9a1104621801d09607200d402d041c0b0f501d00070545160510034240c40411f03554148a02260940800c0c1007001e280108070b0300c40000202e9405002c004c0350400803105d00042c02c4045200305c0b4815802036400c5001c03d1182e0120482c1d003080045c0d04070700303034003000840c5a03c001040c0000c940c664080c0b40d000c900c2c02e02446100041404400703400c0014110480c45046207001c41c4105036209452800e03914001004000041c00c0c20080080040c0c1c100c18072407054206030000c5000e2220142065026421070701444800030010003074240382e83d00ba40380100051400e03490b00d001d0b00c507141c080c601d903044041c2c8000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 335093192 1250 335091942 335091959
    0xe1903090618060806010e1302040501030c0309050a0f0c0b07060c0e0111070e0a0b1c05011119120e06100302010e0a0302060d020706140c0705060117060609040314041e 74
    0x60320303a1000070b440718541e40c2009000e583d0340b0b400404450410466045460540c4c80d414440383c0b1a80483c0300c00b503211403c0c000003400303503802e000180f0105403a00111a0200f000040e84601507604a144401c140131181000028003e441d08100c4201000044000400049a00c903000d8825180da6a041451040c001100c0d58140341c24214040d600080046c84902070403411035401078500f810020b5080a0180803414919181c00d40540a071107485215007130040a000303160426144d820032030f1400c4046005441c1003121911070401304000d001c400f4810b14026489010900c0705402240e8080c03510402440c1001d00c5404103c0c001580948040114100040c401c01aa9801015141000c0c440080e00c130003500304c0d207010b8035401c0d20755402c1c0c003011a84c40c00f002e004920425240303958005a060913403400e101a4800c142e842c0c41c20003402000100483c905800013402c55000001d612181000c4034901c4900341c10801d414400100000d10b842883d0409180100800d1072301542da6540340302 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 335094442 1250 335093192 335093207
    0x3070e0a1a031b040812030a150e0705071e0b10060810180f06030308041106090a090510030506101712070321050109020301090f091e060e19030906 65
    0x10501c0c5000c1c284003064400265645400c8100b04011042e4141a5034842d0140340483c40e40980703407810703400000d00c0340ca041c07103006540700e00d04030030f0072410113134540b49910a1440004100c3c204000012800401700300e09112038004488110035001c00190b141d06090318202401c0d10f880e03051008a4500040032401407400a00c1005038400c0c0040446c6005a20103070000070043e0008c1c0559154200d020758000e030f00c25103010b90b00a565142e01c2e89403626002003184907030a2401d10495050000c0c845580d00c080c058815600d1045020841ea00c1e007507076500d494946500001c010707000760002c110f9407a108a5403582186c103031003a010aa6500d13000120340354030880d04070b10b200c0d410402c1604003007030003990341c18200c0d0501108080c45c41d654010400c1158002c0e005000c043e82c00000400850a0350b00440d15002d02111040001d055142d4851298498144e0f45000130400c064040c000d000559002e614581e45800994040000001c0360700f44900420000310003040a0202c08941607104031308 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 335095692 1250 335094442 335094479
    0x609040203060a0b150c03040609082b05070f0b0910090f03081306050c03010501031a0102070614040f0305060708090a0c290a031a100504051003020c0303070e0a 71
    0x980b00ea030f02c030030b0080d80c040c1c04882c04035608401d041380b030503121100c008000d1614070811005107841307034109540100141c0003a031011400c0d9118208001142c40001c3c560690080a1100600a10080407042d6240e005288001c2d03c6031240000410500446401d41445040407205440c0c84c190703c2c2807950102c803003022000d8000440d06819100003402507400a402100035007004144000d650b80301c005031030003182e4864843d0700c080010051540c140c01098000140303494026440305441c00003e41e606a40d1041ca4100041c0d1002d40f09010450003c480181c0791302d0340182c07111926414030380d5480740b0035600500000e000380f0016100c007c01080d1400d400e079002c50810006441e01c050454403040c08401c003002d090000c201580810b125070002d008641641d01c0216410340c030f0044860b07840c2d1a03040780314014054030b048185c03c03940c00030445098910840e5500c0010102400807402800740c014904882c0c400041842034480d044541c40541c144100da003100000d407a5111014021201c41c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 335096942 1250 335095692 335095699
    0x7060906090e0a022a011a010f0f0c0c150203030103110d0203120a020102090d0f15020406230c0303010e10060c11060306030f0304120614010b07080c0c060d021206090402 75
    0x1002c030301d07003d40716001000914000005149030402c101d5501d15501c0f42071402800d0340e0356070390101d20005051021000ea0102c2400d045c828083c190001034540c0c2024881c04040084600000d002c100b16120344402030300595440c10800a422f010282d6241c3c001e0000b503800020b5082d6070b40c82e9190110307040310015406000b404030405100740e0b544044d0866034130030040d55000d02582d0320a46401501d408401c0c042d00ca4181c4034a0715041c200c44010078402500f80190040005001e150b400c0351943c482d0b840c07400c40c01e00e83c2045000c2d8000150040140c80000c90000100008106040a00d19030090840c0c03200d00b40b0550f1b80b4682900e5205c54a03000424500d03d042c180c1f115885c210740510352007400907080d20480b030342090f1a181540d000350001901d4000d80108941440030b83d104e00d101c070304194881c0c42103650410035030104a0052440003449414002404803070082e090102001003a0f024000c951a920002c5041c8065001241c44449004501e400500f40b840c1c0100005c0c02560040d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 335098192 1250 335096942 335096969
    0x121203150a290f1c0207210801060c0f140d12050405060103020f130603060c0908010908070b0415181703061305070203091909050f0108030a0509010306090e0706090609 74
    0x2c808044940c201c107407103058140040c4202400101001d0010003403901d03c620059865403640380001e402d0318866040503501c0302e04440c5581c0c0382e030413251190654040c0d04002e030501ca01c9142c01c00503010001802450220962035460501034000b540741c49080c81a2503a00b0307000e9030f2a21440807684125009001030b40103c0041015080400d00301c0c4141038007a0103102c440d030030404000d045e0f03021035101300d503640da071070000b0b51071503a00c41034500113400b807800244608456a110200305000300c140281280f0401030100c0c0404c07114401000d189030a90f407007409552070240c01d110100800c4803081c0c482c48200707560840100b0b144001c40740300d440002e16644c040f0410407c07810013003400400704000c2d44810801709200355501c0e5012110406202c0ca84042c69041c5660789050382e030085c1c0000604a6941d0050101c0c1c80003000307a03182c4d4403c9190482e01c480303400300120b02800c02d59100303840d03841c44c1481a43d00140c0c04590b00c1d0648016032141c01d6900c4d40c800007160100024807500c83d014074030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 335099442 1250 335098192 335098259
    0x1112061f0504120809041b090b0a08010e090a1a0a050c12041b12060203060f03070323190501020304030e0102030a02070501030f09020405180601140f121203150a 71
    0x3038810014000c1c003492501d8206106a00806e081f610302c4581d11501e8660110069050baa00c04c0c0d020001d403010084840c1007696000014150351410b000f0381d80c0c1d12429500180c03400c82c0c06c100700a86aa0880420714a805580242014821082d80e01442003401c0c880002c1c46510b015040711070740013146900d0071040d42c031522101c4144250801d07440c04140c144030b0005a45106041340500c55000710b40040c0e0301e003030410810144604100216010750000c2108002140c001082803200103100400c41c5685007003990356604102c00b15012b003060054814914048c098150701541c03180c0d00c030340c0350050802c1c002d00c010390343ca01231036002000591085405105952180d008181c0d8ad400098021400c1045a8001003d070ac1d070446111000542071080c0c2c0c40e070110704214031401841c640e042c615605c40320002040300d2440150440e401008080e1101d000341c1b10801c200c1c2482c4d06001c1d01d0b81d03141c0c200f481d84400d03a010803412140c8103d1902001080c1d2004003c0e10381c800c1a99a490310198025 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 335100692 1250 335099442 335099459
    0x5011b11220b06210402040f020c07180b060a050c010204150305190b090703091e05030a180f090c0203120a020408070816030b06010212070f030912241112061f0504 72
    0x1c002c0049800c036840c1c40023404880f4003400617203800c040450280c2040381c104005180c1291101008454981c04c02c0709180c1d044c0c48150446000810a01e012640c03114dc110311175000e40300f50f07440300504c5115060750110056142d4000780c0200041e106011008401e144054140e510071403c2c150303c031035800301040c1c0d070b0381c002c0d0b0001c50009d00c00d4207030010281c0c02050002a4a107524420394046e0000190407544540c030800c41d42235400e6400b801446103040101201040311279000348110a80c0d40c50702d10410900070401d4070100408101011500c4c034001c0342c0c0c0b80213504988035008040c440c2540200741d9000200700c0302d102040d40700c1c14800079455034460480c10100a0070240c1940520000d0f9180088210300030041c003405180018041083c03468000e045014503440000c5a1071380000b00030002c0c41d40d00c4096000452403180b20405412002008000e03c5441b1300052103070000619441c0800c0110b4071688070700012200302401088030800ca800842071138000742d00080040000780607000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 335101942 1250 335100692 335100757
    0x903080a150f0b090307150e1c050a030908070603020909190e0312010e16021509190f02030606121c09050a14040c0905011b11220b06 59
    0x3a01181025982c0e481c1004400707141150414007042000143c02e000324101040014014201340341e00c054010f44580005084c43c0b4103110081c820414000300018035001c42d450083d1150308801642d400450701c2c5801781440e100c51107030880c24041c00d100090442e00038030030b6074200c0c6070180030313102c0c81d031b641c5805450440e1040c400800091340c0d5183c044842d19003040035200119014190700c03010b505100000e84c0e40365004100908a2030301c4044600c0569000c2104ca8010385005440c10958540d014100d0401210030000341c86e00c0c10f050000e05c140040200304100960081d02030756120b403240c1e0244038054480c031a004102c1e9002c070020503204155020303103a807140c030b403403400c521055107400c0051702440741540000151034480031100702ca0315042c4108968803801d4100b0100e4140740000203000d0b0304400000c2c0c580403042d02003010600c102d01d030102c56240c00c000c02400386000b1480030580d481c214014450080f80c5080d500f0089030400304119100d20000c4903003600d904904402c501c502c2ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 335103192 1250 335101942 335101961
    0x91506090a090903111b0d030804051c09090b030601030c0b1e0304140118020a0b0a030f060602010203010e0f04050303011a280212120a05040c1d060a0503010903080a 73
    0x2510000e0000703019003551040001843c425500c5e221080b8845136407915003490441c400000c940c0a08018010b80c1d1a0383c1c3d03450550380e050404414681d100e007030142c10b1100b4200810204d00c503c40031031030b005030320980f14819183c04103000c105001c4c1d01e000b450f9071040e090100400f01c241c40201400614203081c05080345520fa021811031201801e182c89806400c01c0e1800c4072641010400d0b4200d01000b0b00984e00740001ca50141d5003001419000225171100c0ca1007112194400000d045000303510070b4010040f80c81c9030030030038441c0c0359668100038000d600901c2a42074030540d00d00403483e0b0292001125001e40e03007100085096901f002d00303006074030304603000c1007a000c8400c10032400b400300d48208a004040603269030031900702e40700c3c1019040c03051030038449804c078804200c4840c2100710702d044d45800860709900042c3d16615842c0c90880c04049401c0341143d4050101046050b518082160b4418081511010f402c56a01c000f03041c240e03022a100180401ea08400041c2003c400341d10a6182 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 335104442 1250 335103192 335103199
    0x6090418061401050f01110606010302030901090803100f080a0503070611071401090c0503010b06031302010c17090102011a03030d0c0513170c030601121103010603200301060509150609 81
    0x10000941c0e10601181c00e508000c2001090182c010002c3d40f90803100080384140a08201030303c041e101c0b01d03a5489480040c03603141419408000310b4a12102540704811246e80840c0c002d5907424001e1140c0300c06c440354442c0d040c0401c00c40001244140c000b14046130317480c2d4001d000b1402c01140c3c2e07031b651000e400c8510701c4d0f00c02c060052000e900441d62503129035101c0c1c18090000200768049051850340800ca030b801540c00303a81040b00d8482541c86407000ca0381d000f107040c2c1d4004105006032004a6900c20201d8010b4140c8100a2150381c1107144000140b031520400d8001b00104080107034a010100c04000045a140d0002e103c0041d1070380c181c0d00f01a500c1c1d41140b401c0c40c80c0013400203640d800b8425079008140450704422480100c801c0030840c0015000007240242220b40c5020070000355500142801000c3c1c04065110408039142500a02d0186912903074021025210410703e200c1c0c4441d04a403507209600349800003590341172045480f4000e1020701c41c4034003806a80024080183e0100400503007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 335105692 1250 335104442 335104481
    0x80a030e0c150a020c15091302120705030708010807120305030901150b0405040f1104050d0302010b03100e100501060203090105090a03120201090b0c03010b0301030f1a0106080108011a060904 84
    0x819030703070b0700006580c02008601c02c252101441e010007840c20607594002d81c0a0ba14140ea00c10b00700303026000341c1d9074914040315481e40004a000c8004043e00032540802001e101a0041c404000d8002c00a544112010756a0100c1e0360390700d40d100d0395a10701c144520200b010170039600307102291094006542c4001c1c50800400e141a05005002003c882584070030136001c0c01080a11507483c0c1401900110146400c05003c440301d15500e6075902c4c8594807507548111482a143d008150003900b00040e100c0f80201520414540c504041008d082c400070790001c0c1e03000e6020300901c03040d80ca100d10340c1a1210707940103604018010005544907404075158a5008459502c00000900819030042e501c01480c2e0001c240f030b0200b454290454480601403125403081400103210320380b40340050b85d0469400c0048020901b03424101800001c0010080d594491900400412030301c4d08290038504a42ca800004c000390340003020003101d1105405409640000b082080e9115403419810030b05282c88070400781761 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 335106942 1250 335105692 335105713
    0x90d0b131502040b0d1a1f02010b060702030c01050918041208090105070c021509060309010b041503120e010c020d050a1b0f050f061b0d02070f06121d0a060b0f010903080a030e 77
    0x6800e1829a100c00454109060010347d00c16828002d0b200e4509094943d0341c22300c0d02e1030340001e40352109001034904002e404904170000b951900c999202041046840c3d181d60300381410001500c2c0e512140c017a000c910910049184100c0500c01c440c0300b48240d81d103d03034140a03513608001803806e120031401c00c161403c0c48906203690303a4000860060a20f070000040c0c1e180d4107810300007500d29401c88103111090104080001c41c00546858804d00c007a840c000d0034041e400d00060b14010030024001c5c1d017149080a4200401100180a03081e02d401418038891321a0008119002501036019002c5864100d203420000303030a0106100d800040010320290408904d8265078540100e500070850300703a030001000d403a030aa014000f903030192518403250802c035803d00001424860702094038400150380c528266000e41c4840d050100180f040c6010b841419000381040f1002d412031a81440c450840d010444104e036010380c10860441e648151034a0424801c0241500105184c14108245006000c3d450 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 335108192 1250 335106942 335106949
    0x70905040c0c11030309031c0504120f06150b1c0e030304050d0e090705180103090501020a2109020307120f02040c05041502070806060402090d0b131502040b0d1a 71
    0x15400220607a450b416150500c1c14403001110303c0c86101c83c040c1c2c1081100900c2a01c0108852941e25460348040714840e041c200100c03410702c60381d44007900a00860b0012000c01800020907012076010700e00c28005000c0e04031485203589454402c0183e015010000400307507200f1014440b900308810600000c110407000700c60ba0a552003110b0440712a005100ea454915802c1150001100401d41d100b044511b00000c0291003031043d8020050704d5442c4001d00c0b00141e06c0794000c00140d9504c02c00940d161984540c0180090448041c46402141010807129a4250038030a0542c4590020014804145803805486850742c20b0501520070b5940c020b482c0d00540c0b0f43c0e0140304100c0a90f42da0740395550340b810159141d40000b1082c2c510440d0409442048441ca00158441c0c010108031001640c1e4903c000016000c00000a8000e060740d105800300810b080c155841040a06d00900300c0e821a0010141103100700d03c45e40c0a24282040c003885069040383c810b074809480b404403401030025000516000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 335109442 1250 335108192 335108201
    0x90d030b1c080910080906060d1e050304050a060e1810030501060e060f01020f0a02090903120c0903071a0307080c040513051006020a0206040e1f0909020405070c0b0f07090504 77
    0x19603403580b0001c0c04541d1070411425101300200a490403074032a040040106440310405800e1074400e5040c1c0c2e80110034840c1c0744450110381c024601c01c00140b0905464016103c0d0040e201e86803040380381c81800249540114080300c1d90617001800d40c8480717454443c10141d111005061111061511038020001400911600001d002400c0102442e0718210342000600c14030a240d03281190040b40d00341d000c21000141041a096049405401c00d03615003072080e10b1400f03600c00f4650744544d008144041500c011005101040b800e409130340c05107895001480b40c00c1b503c000c243c0441502040010405441003204640041c1d140305c1c1d241c58240d59030001170268003911403042d07110359101c050100c41c03c07084010a006200d01e00150190041e46d8000032054040c610038074410621450001f482c440f030080c10901c011301800740b8582c20f50340b031350300240080100071400c0340124903105c045802075008094030240554801c0741d164595481051201400788050403240030700908203004142603846004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 335110692 1250 335109442 335109499
    0x180d030507110f100309030302090a0e0910021306180902030114040b0312090d0809044106120f010501120b1308030402010c2117060306090d030b 64
    0xd0385915901d090500d0007941c4074042000e849281ca01c121407000d600c50205071003c01e0703480e081c0000ea040141c14194080d00c112100140d010b050144045200300c1c824802034010604403040391362005861100900300e00c0f9982c4441130078110800d0420605204032612a1180b20302c0400f04041a036603404001039802c02c0e000f2085031030101d904040107044c6803050359000d42d001c40080c00d610446d04000d52541c40381d00c0c3d543d170103014100c00d440c040c440d440c2c084507440080a4010090700010f00900d288440095501c00000140805907000d440d84044003018100ea03002c2c03043d0324a4031071030104080e0282d041110300da140502550405201420703c5564001e000010700c40180d40b40c10b150042c1e14078001090b6050381d82410032003c3c00718a0324016641d00c10b9080c20100340b106a181004110742445030f0b000f96503030154502985016902a03110500001019400241500c45004160722520100c400d83d05503844642080700b014426004081030340c02c05030401a2610407442110b81a50b0340c2c80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 335111942 1250 335110692 335110697
    0x10e10050a031112070509190e06070801150e0901120510060e06010f020318040504051f020a0914010c06020f04090203130b06010906080109051803070302010603060629180d03 77
    0x580f08801401c080c0d0580d44c842243c81c000e0002c00341440001143c0301000f400800f000d6901c1c0c4035241d0044550f07442071400340603400440b4000c0c60700141c01444108240134607402800b01c000f0200009001d031b461051060001403003000d80c1e80c00d00c0810b080000e8502416581407103000510b6260140340d10811010b0318807016529814a403250009d000d441803007200e40c013154000c1200d20100946d40c4d04004098104843c08101030300c1d2810041d2801d0300402c4460502040c4c00381090b504446035006200d00203050b01c0300c0e880c607541c0d0301c40c4000b04521281a180840ea0708d84144000400b10380c014041110fa601a441c14107450740d10346400c903002142d0203214590f014215100b0b02c4840395400b903000d00c003403820b4641182411401403c069040c4a1981c4154075007001c0b4035000080c2d40e00740407078403000d002ca1b502e0718006d0400901074000e84c401500c04501d0504003080000d010f2222481e010308a820148203403c0e80982051184d00c86080b00d02c0c80c071920640384100d6920110305682407070090b07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 335113192 1250 335111942 335111963
    0x140d050609060102150a11070b010e071806050a08040203070f06090e0901151404060902121005012f07050d140105060603011d0721020408190506010e10050a03 70
    0x510501054801c00341c400740c1990f003c1113070100703a0501c071102d0781d070b2060740d000740403075102d08000d42555140941c1c94020052500381d000811001d03104901b09118443d40c0d42d45055481384054031420030034450007800c000030803c21801600501800c00103412602c0902141c00e03690382c0344103094046401d5000480000c84a45040001c0c411040070305802a0b0824020403283c2e8001305400720240f61480340c10360703a659910a0104664a80d40410018044000f00b55501d50041c95004d21101d01200c20b240c03c291103150105080d40f20303040d00701040814004c0d58000300c0d00c43c100000c1075502021a58031922594202050399100c1040039140c41d4840c112503a4031881c00604d036400e446009104600490050004000c82d141a03990322506400000070710042c0d4a490200b00c0710b8031440110310314107800c410083c522000c0654020401c89000b030302500c40303407071100c003031828143c9203100c014010340c0c80340c0010b122105c884005950800840520307104ca2541ea81c010a101c0c0c0c00d994015645460308 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 335114442 1250 335113192 335113201
    0x2010e040e1e07080a030c080721030c0306080d3b0102100506061605031e1803010203060a0302041e09060902121914010e03040305010501051912020907140d05 70
    0x1c00340a104100b141c41c026203055070414442ca039840070f21510140c20418070b0b1075940140701c0300c0c1e000c840b0010f40000300c1410f0703ca01c5030a00000308603128405d1000a00d04200303410f10601c00c0c404d500c1a500e1b40c00241071342c4895202c0031101014031000c540e44140c202a103144011b400e204a034900f1411044000c400c40d402900068100203ca01d6454101c1c1e0030b000030003405503103540c111044514401d00c0040c0c0c240341c40c00c20902d540502e140e00324a1181d00d81b0f2109641045602401070741040501250402c403001c1c041c0b500740c0c0019560b44c0e400c000a03807802c2c001464503400000c45062168484000304518420030810b4540740c040654a0507a2040208150b003408000c08946070348003030051a10385182085a440c01007100c1c800340c100b22140d00c140000f81030079000058000101400c50381c03a035449040c05070013014203114ada441003000c800402404a00103400e00d0481d0840c0007442e41c4042c2d15024840d130701400429a008203d0449000300c0315060341405040303000c440703400000329840d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 335115692 1250 335114442 335114473
    0xd0c03060b0a050a05030a230a0507020c01021209152205060306030d0f0908030a0816020c060a05130f181410031b0503010c1205010902090f040902010e040e 69
    0x8058000c1641c020040105440d850f4004080702c50094070b520782a952540d0f40502080105011182d0a00030043c1e403e5034411a03c030081d0b55400f03202808010880d80d140d0080990307945000c20b80703450140c1c100e2a40d5501d0501010301a201e0f604000d42003000b8503000907001d80e050f901a5000c040c01d048808090641c0c881040030101c044c082c00d031042c80c80c500303017540000d40c2c2e1805840c981007041034000000007203c2c07142c0080802012200112515010400c0c405000a88103d4094986851b8841d03c030b16102e00c0020544820040036242c1ca00e00501d00d18121060340c06410b101d140300560010009881001a180d00300418850341c000d035030704c8641c41210040d901e6007001052407910802c1400003a4810500c0e003400c40307034000c000940302e1140d110000104c500d01d0b0700c107550551030206a45d1809800400d980c07503043d50044200f12980e01c81c0c4c1c0c100100e0298031101038000400107542e01860800b9400f05205d1401414001071603000303000003500360380441a00700c40e55080742d00307000d11250 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 335116942 1250 335115692 335115701
    0xf060824010e13021906050a1701140d2406050916120e0c09070905010f110703140307060e0304080d091d040213181203050f0c1e0d0c03 60
    0x140c5440c1603055450009480b4802c00c002d00081c01425074241c490045540e564003000b9000d43e621400d1562913590070001e030454010a50030004074400740340b095211082d1240306410b0781e1410503580484080d080c14402105400300c4119406c030040640c02c0d084066865080019018481010803030b00e0814040c00384032103000c0c100030840c4c07921050190000350400078041140034001d0f030000781490307940c007103524085880d28119001130044092040c82c0e07501041450a9420a0301d4144403d46062401c541d826a00f1103501110381140c0b2042c40080c05000b0541fa601441c14101c82c2070901c56280c10341101d030300700304005160b8030006040026800a01c02441c41c5c5001d0300701006003514006021040c03000c01c081e0a80c1800b40d40c80040e0842da50a00c00f03003075000161004004508190fa00b103c101c6540c101c003030321900011004021494401c1c0249032040c485103840041c00c1d1030307480d800d141e10b402000d070301071851220442c100d907010b01e441c001e00544800c090012405545002010b0304a6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 335118192 1250 335116942 335116993
    0x709060e010f1707060e0a1805090c03120a120b0603100602070611030d0506041503050d020712030512040809060d020d050a0b01020a0b04060b0a0305010209040c0509180a0f0608 78
    0x2000703201c0d0009254240401e1138402c462045c18122400100e0344009600c130111600b049910300c40c0c042e00100700740074540c032291081d0009021030b031420120008044d40c44c064400c1c41c0d000c10000304104e15585206007034402c4401c1d00d40380d006c510400000d0000f8a190003c0751103241a4000c19020003440b541080035500a00d06030900134040c03c0100c280c0c94072841182c4031407602c162a032005c01c002c2c0d1120b41c000131900b00b0241c0a0541c450700c0b0f00d01140c130b80f91010162001441144008035a40f14035118010005906841e030601c2c0031052541c401c21200014400e94094506204040007616903a00900b224240c1100041c0e41e400310400f107508407607000d810244001e00d4180f6012840c0d0300000c02400e50358200f40d2200b11981c1e01d240050103441d02c1e18242d500030003015000010031030150040e10b198001141c060100111085003115a40a84501a03602190110b58141c0354403901d694603030007a180c1500410210704420044081e82c80743c1e80100b0069114000d150000800c0d40102000c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 335119442 1250 335118192 335118209
    0x8090f0103052208040f06021c02071d04050f011d0118022b05070b070312110301060c080d0e0601030b091f020d02120f011a130303030e0709060e010f 66
    0x114203007006032030b100024500246240303c8640892205101c402001c0c0d9004101030241400310f40c0c1c451800941300c43e12070b800030444081c40711707032042102d0000c2852000c0c1c07034441040300100036644c80c1c0c03491b01c40d00c05002541d0600643e40b150280c1842030141c1c0c0c04a0b0403c810740d0b412601c44003121400c580c0f100c6041020024032402240041c0e803116441c010038007003000700040452106000200b0380c210004001c0481c820124001094a00c880c0508046402a11071421110040121006036009401d4480f14100c08000500c0424014211440198000c402e050f04119408004d40212040c420301990725500c2403004004026601c84019030000c403110140100138104201d2620030800c01285805064000c00d034000070341e00303e905480c520800411003003014241100d40d03e00e11017081c01805202d84c1c40000340c0c4011240c00d01200c214491201e554269146991003c4009100b842604000350180d0000090340901c0c0703001e80340180065070400c018652415001000c4030704954000141d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 335120692 1250 335119442 335119451
    0x80c0303030103231903021e010903090b0f09060d1a060c03030105010e011707091401050a05040b070c03140f1b01020606210d020c0f04050405100e070e010308090f0103 74
    0x5401e00500b03440b452a600ca8992196411041c110f0820103800c007201880c0c500601c0103418035500181c10b01360354401c001004038110782108e01f0348c00d0302c0c8400406004a419404100504403642004114500c00e0a00311801e1040400c0041c2d942e61003004e0381514907440341102903100da0403000440f20900111062460044220f54030f40d200e0205105444c14414900003101669020f0054003910b071818107411500c500c1c1c60b01c80602561100d001da00140085800480000e50060040324071441850b103034142030500c2c180080d54917a01900b07084441c00402e090002c000f41c8544d20070110311340d103c0b0240180c000d0040040d440c110003000008008031344030320401c1c4240d0300800c0c11034101c1c20076150880e800442d101c0340f040b80026001da00c41148100d0098184031640842d1080081d031007100c203498090404001c11043d81c00945025016401c43c922075401a04168003c04c8000b584005441340d0725902c9001c2e4288080c06d030b206440101c400a00405545409090402d0010003420200f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 335121942 1250 335120692 335120699
    0x211401050925050405060f12010e24130207080418050f06101413170f030f031b030709090e0a0809130212010605070c061b0f0624080c03030301 63
    0x1c0040001400500803070b4012521a031161003030046401618000d00240e541d035007055081902680310400310313869403280304000729410341301608482c09120380c01010144101490041c0c0404c01010840c3c0d5401500b981148024034468000b42c00d0550240d8bc446459a207046140d45190040c20541c811700da140c0000c0040400450491a401c45010f5a000a0003640d44805035400c107226501ca00e4201703070219501c030801e070501c900041541d030a13a880301544205050341c99a1a584d41c0c103803500720381090180749103142c0048082d69125070355070300310400c1c0041e00000403807079070040e039100001a2030b032034050001c0d035141c0c0500c2507030a84c4407000b48511182910341c01350314090850380511030b0802003010328040710643c042d603140c480c0740d50680c035403540d6506003c0e109910440301291041042c07800010094060105402c4030b00a032481662500090750b202003892801620445007940d540e088504a15050702c0007007024105c1c8290b10b140c0c5070034110007914040c1c8048070355210703600400052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 335123192 1250 335121942 335121961
    0x31e010f06080703021303110f01050309030403030c020a0b0a0302030105010318032c1224071b0206040801020a02010506010210021e071406040503280203090904032114010509 77
    0xa4084070350a1500300c1494079240400c4000c1e1003990415207440e0001100401440050882c0c40101c440480314401e00079403000043d0341d580422500107295070820700082000c2409180c50303595540c4010101d400c85900c0c0d0201001c0e81c0c00480f40c110020b80d0210050009503014412f4000000842d0300d01c245480c01c907500144040ea40030f5416801401031160701409602404615001c3c260081c005242806c05440076551010503c601165500da20f600800d208a80072325224043c6102342d6508415a102c03140601e2140280d1500300d800080c20000080c191100b071010345205c407815400442c07181040800286416501a0741c442e00740d204000f079a905064400f05c6103554401c4480c2c0940b01c1c107460800043d60003070440c544070786000c3e9000f0401040b0000c0000c040b811140c1000000c00694500a80c3e103401c1142c580b04092390082107000e545180c01c40c8503e500511034942500241185030b04856146003121180301d04949412415481c0c1c04044a4140582019602001d4901d070a2414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 335124442 1250 335123192 335123219
    0x1201061b060b03010608010606020109050c0a15030c0c080a03092f04150f0620011103181e030c1b0d03050715020301030f050115050105031f120602031e01 68
    0x144003a0b03541035040201c0d1070a400a074002e104460081004030303a5020003138003800180c02c040780c081c082d580d80711640340313448401042135541d411010b0740c03000c606000c1a4000c041d08065001801329a031244000620704100500d5140600e42c0d0201d40d44070b55203080032500ca4000c0d6064260504403030011125202d2030f03a5903402403030031078001c030b00c1c046403290382d8240b06199040301440c1c4d82d80480c00300744036400843c44014480c083c48111043e0102030a01c034220f83c0c040c100c800d284401040813941450002c01c05d5284c00c905030050700c4010300c0641c2c02c4907036000800400011508041610071160405011100090450f112007072140c40104001512400301d5074801001e0020104201090010202d030484120b810190115902d503142e08146020031007084d42114650708010f0310700078411108003a0300132910182c41e41e0341140c9450a4035685440c0122085031080c41d6214001000108a0341000280703015400c010303560705108003248500c8680007818002100020010041c1d0020b4400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 335125692 1250 335124442 335124497
    0xb0702060402011d0a080102040b090109060201060303050304110f2d01090807052119060b01030b030d05030c0d0203190509060c03040602132c070c0f080309030c060c120106 76
    0x1e1642c50000070f000085c64500c1d003604245100d41c40400c0201d03c0c00b2003c401012000c2d0241ca81c0c038003035640c401080b8280d8070305000c0200020f10034400300c1d0004038450301d050790304900140b05022007500d0001280c2c070307400108210300350525081c080c1102140e91402c285c084803002c0c0b802110761818034003e5650307042103216203401018500e0319842c00903402d0001116450350001918030401d03040460030a41c0710080d205450b43ca150000b001e103150b00a200741c0c10f01e101e01401808469000d600306a620b0341009245072a052410440350f9007108140c402103100724a159500d002a115200c0d05000b2150001e121030320550205050084116020051f00e44c41a8031910250783c909103490302d498400050b500644100e0540d25805943c0303101d0410588800a2851a140c250765400b841180ca10703914480c0505100b502c44004d0b00801c440000841c1d002c03a10400b02c0786031807400c11940345404011608001d0594010034504103804110700310342d004149518105680d00844c0b088114441d052a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 335126942 1250 335125692 335125727
    0x307080c24010f050a080615011209030206040606050f06070f0c09110d050a110a0c050a050a0803100b07031403040c03140a111f0f0302070b10030b070206040201 71
    0x5805048040400030441440380c1c0d0561805800041400240c0c038410070300451030210b400150100f81400c014a85408440d0b2400c0280090740711102d0000146401c01c035118100070742c401140c60002000d010b40f44615200b603006100d030345040d040220440d9600c1d0003151180c0090300c036040080d9145e000340d909450b089a4824502850340c40c218002503410b80c00190441d00388000c0c507052003102c1020b4800c14a40000601c00d6a41c0e50242d60101d48221a00c0b01842d04148000b41d501d40c81340c1c241c031816030b11502c2103418421254840c28589910f08204070f80e0b0300800020450300380c0c122000140203116801180c4c0c101000c90b0f0700038042c8442e862803140c0001c0c000c00014140300c01c8040c1d0314029604a01c80c80030f0041901d80c240d4440c4060709040c0d0300b8100026043e0303994108a0116110a48400f0900c10000820582258800010140c6d1020141c00b44102000b0900c078034003040c0141e42010070000c54500e10f160011701984000c0944080d50824400c00c03026076007081c00890442040b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 335128192 1250 335126942 335126947
    0x1050406050f090301050403030204030b070801150c02060c0303181e060c0304150c020c010207050d0807030f0504150f09080118020f1c05010605030f0601032406031e0201080c0c030708 81
    0x110201842801002c3d0780719071643c241000e100c203154140e070017001640d004281964581e03503201c0c0c05a482c041e081c81112100082c1148c0031040c544210030803d138a0340300034521441c0003002d03001c03280b654100ba03881d45e40606070018284604601004030440005111229101180c41d5040d100e0f2241c800030100620040000000781c00c00050b002e400b4a6404141d01c100305104000710000d40d00c041d440180d602511810720702061707078030b03000911481c880e80c051650340c40c05030310381e0703007290300c0310151004400b481340911002c1b55980c0200d41c01075411120f40d41c1c1c032429404a404c0100f21141c0e81d403100307807140d00d048020b035850062003080c0340c400764060350052010310521002c01c01c0c03090882c1d42100100d00c1103181004100064120404940741201120003d47c20503210302e8a50708284030003007810200d070b280f01700c0d400c42e0b160f001420074409120000b0030301c0d508c1c3c0f80d03030604184441490011071250fa4680f011582c100450a8000c072490070001d040100c0c85100d903540c0e114024001e083c02c0d802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 335129442 1250 335128192 335128207
    0x5010908070e160e1905010305090c030309060a23070201080705090913050c060a03051e1e06030c060f0c0d03020c03070b0925080f03090d060c111b0306090109020105040605 76
    0x102c0350001e8581018002c2409090709a00345d02c0c600303000d03008250000303041c4008944610000600720800c000000e020310b00e00300141c0d040007902c3c0c2c0209050710500540300003003150510580c0aa03150a0350940314a170340d40034241300040071910014169400d1000134821f03162a40c0329104c000354044c0c2a6007100f80c607214581050303850903640c2401183d100f400051040e0300560315030442d500548001000030390a03950002592090303203045804074aa60340c02c9180c4402c804074410a03c4e04580050b083d00e0040c03021300c0101e0300c640d0082a00d09000b10300018041c0404400300710f111101e0b540391404505040d05d00c1d0340140c0724070a101020f1304c0f606090010a603040c83c00c0c80180c1c40c200300184041e03502605201200c100c00a107101c0c40311203020721071090364014004001c4548a01c0b000384801419482665210300070311030200c01c1820481546804110800c0801210300e00310f0b800c96012182190040400d490200020a4140e090b4100b80810300146d030040141c44c11346046003015500d9006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 335130692 1250 335129442 335129447
    0xa03200316060f020c0f01051e0c060c1911060a020a020102090a03050a02100309030e060705011407080a0e03040f03121b03030911040b090105061804051005010908070e16 75
    0x2881e5070708a01c010200d0500290882e084400000006010b409030f4410112210410044090000005002c1078041000702481840d01490744240700c00001a9414580310300b90700c41c60300000300ea47c1c1c891200001001b403125201c8800a0750201d040d0300e081d00700d042c1040e01e02a11030101070040c42e00150007142c0748807914000e40607203d10308400307042206000c3d601c4c24411f83e81d516a20302603000c3d0020303082c00c820f020321a01a40d44a66055102c0003a410a01c40c28003286600c07c44c1c040c2d49075540c4809004545002800050107507000b50744050303c82c140118060110b580c0c00000e10856881044200400e240071031511044035000b49184d1050f900c0b400050383c0154410604150112800303840108254240e0b00801c905400380205280089032070042c041103e240918aa038001100c000404c034503d058001048240f01c1e04140188032100b01c3d0106096541c25100c000c1c0400c1c42010500195038888101401885400c00901c0ba8614044511102150152010422100d052982010a070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 335131942 1250 335130692 335130703
    0x80f0d0e0402091906450b031009050a060302030a02060705010e06070503070801050d02211e07241e0e0a0605030f090f07120c080d0903110a032003 65
    0x8001910b213072000c003e03100c0c5450381c40840c2e0007800003083e210900c2c80843c0080310703514804103100140304842c0c0030306a400c441a00756512a01c0150040d014004160415071002442c0184c000c1003201299504091007582594401030289520f03031b02d4040100050b0382e00040c0c285485805848050350f61035141000303800740445000814841c070802c0c05004030680c3c820000d611800041e540c50519980300d0b4108500010041030296102800484a41d1201e0035040c500008c2500c00c0200c81400c0c2515052000100002418200310741060808001009a5078030780c801d4005015019019018450b0000c0c00e8212010f28000c07040c4840c2050b214024000c645811105030002c1031000c107251b035220010550f50040318107846640c9c07014041980400d002403540d1107280303000d0203006401e0404281849051030014140c403000504007000518201c280500304502d8041c0e0344030351209045041c100190715682940c01d00608101c8020004501e07000c0b0007141428800751128820000c10000901c0d20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 335133192 1250 335131942 335131957
    0xe07051c0c080f0106050f060a050d0b040c020f16050105160f020627010c0b0106140418060e0106050313030e010c150507021002040f051002030c070807060801080f0d0e0402 76
    0x407100124007140d0580700040801c841c0d02150000c3c802e00e5100c0f014041c1c6104c003610740e5500003d00744907810a42c0d0243c4050140c2c41111701d00000c3c9404d003203002400380d80490300d800c2c01581114007440c580710b4060185d04a00701c45070101281d118680ba000a000d0700c02d1007642c1c4064152141c0c994204234032000d1001d405600148040c3e103d441d2040004039071045107150003c28284002c09130380e01c2d40208010401745801000140c00c41c0e02c0d06400344d50407104000c40071215501080b0104400c4e29181001c0d6041c0710484c00020740d617003001a0740222b10410307007088042c42014400c1002034400c2d1941808200e603d031500c806d02013425401070350355003490385008200000d404c01d038049100007a4002840f461040e0300716030801c164480014100c1c410b600070403188600107641400b41e03040a0780403e00d08180b9104491500c00002034450918980ea0000b0700c032600549420020329a00c24009400342003000050682c121006242540c1c501a01402c13000344400c130511010b1641d90b81c0e0544004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 335134442 1250 335133192 335133203
    0x4030e1206040c0509070e03120315090103050a030305010803071104270b0f0a150e040f12020606090a0209130506060f0d02220303080411130f0506040c030e07051c 72
    0x50b410145007210000100e400b515005801d01d000040384c040c071802601030030a002070b000e44502d018901c0c55540549c0000c2450307141680b0b590040c03031661200709a01c8c4c0252f0040c0c01510b907805c0c1c2450010305648060340300345040d51051044001041405d1022404614111000030340c03030f908251190320580207c0140034060158554120038031039030401039403050306c5000b112071240c3e4441540c1000c03100c1402c04170128105a01080c000c0c03d00d611541034009020f900301c1c00e2060807603602d03c0c540003087c0c0148001a00714200b40071042c1003091708150850309644080d0300b8075a0450100794220142c100c3c40d4001c58440010071800d44556040300d00c000b4010b03540e243c0d0303440009000030107036111041c03000040c02e003590b80b0002952844040303002d4942c981c0d0b415159403a107856035080002a20705031544001c008140c4e200b070600a22500d8001c1010510100302071030404108800c880b02e002c40103003030609060400400410108420701038403011240064031369452203108120103d0544010b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 335135692 1250 335134442 335134453
    0xc0b1b101104170c06071103070905010b07080304330c17042013020a080606031501050c0118030804031803030206130f020d05031201080a080901052206120c140304030e12 75
    0x14401d04601d01f041c0301500781c00701c50f074090340c40203171a0071a90309103e442610001400701500094000c401150400d003d1300c13103000c84030700d405002600a100724810551540d0582103d04c079054a60048071661000d07814405071039501203c7c403c0030050b004100904641000c40688040e429200c020403400501030000a0b0341404940d40d00700031341c081c04400005c030f0f00312030004082c1d240c414201c0e840b91107240d106021b1040e2800054440e0380102c4d003060313855500ca81060108070403684d45207020a002c1d580350803043c202414050300c8002005411345400122010900102c0d0300054520f41020034400d664101c12101d0074080c0300c45801090095000c2c0c00d001403c402d0000002c042c1252f1040c80c03041403050b9aa44034001d64505a481e0010281c14044c001c0d00f0141d801070740602200b0b6940b160070318100c1d810f80000e29880304142c02c10300110780310f08040d003900a40e9100b4441114801e003000400c60040000c0c29019000040004003000801e03074072030b0400d88601594441d081405822580c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 335136942 1250 335135692 335135707
    0x5061507031716020714030a08070c090510060905180f0c04030503030408031602030c0c09070905040f05040b0a02040501020c06090102070323150c030a05040c0b1b101104170c06 78
    0x50f4640c5042480014072400c0404101d82c0011510a13603e84001001060000c1c0740d035440c00c105404c1a030081c0e03540c820034a40061006058022248038000c3c045c1c182c2102c5062501c090070b15034880d04180d000c0e20081840007404c20044078641d8100c0382d5001c403039001c3d60310800050180d00c666000200203000120070300080103402e00c065801f0b0601700c081010a0700b5074410407a901d0040c814051500d6208d20082a6241410000a5040001d07032400503811904d0300c0209040c0d5046c80b40b4503480c030303a0341c60030041880200305103640c000c0030090b0150300d400c0ca0240002c0d0358002c0102801e21450000640e845280c1c020007401009541c402203940e0104180d6044400304c0714103170a5628076000354400c0411110001d0341851003500304038081030131508d61140d104024080100105c41460b84200003140c2c0c0800303440070344140d9030101c1c243c1440101088155013090501e040c031841050503e0259200c1b0380200055805445040c3ca50400c0d10030305030340292910602e8181540c010000027001c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 335138192 1250 335136942 335136961
    0xc150c120f0204120b040c2705090304090c1e0e0d08030c0d051807080d120f1116110a0501090e2505040519050303030a0c030b032b0201050615070317 66
    0x246c0f2990180c41d079007a07410380c0c80303815001c0b8840008030355412103484c2001100c5040b69602541c1c10200390403c0382d06094580d0120b00c21a0f00c8140220046803203004491806441102d900c14444814540001d0711051140402c0c0d61130241d140c020401e400c00300004d1111683c2105032103400f54411810720880c14a071296689202d03a4041c1101c060146000201d0a6800000c103030303080a00c00d40d2030304111840008000001cac0306407299104415111060030409004050107448a401016040800071800c1d180910f840442044800d0103035003100000c100580c3c10031040f10071030300c0c200040b1f4110756075402001d0481820b2891501d0342803008002000c516030190103081698407d56911602101c00c00907030f504985c05215150380341c0e004000164082c03c041d006064810740c5402c1c0814091003010000c1e090800d100e9080240b1030340c84d002c03641d90a5000c824201e03c0103050000b004681003040c00308e5003140c002c0d042c0d0058074200007000c00c20588200711410130000d0403420500b1a0401d294032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 335139442 1250 335138192 335138213
    0x1d04091e0501092306091212041e030f0e0f090106080c040e04060b040b09040210050901020f030d02070c050a0f05210303070e0108061e040504140304060c150c120f020412 75
    0x980002c0d00c50b51000490320440003520701511f84165210754140940e411a081920034010000c541607192020b240c0b4800c61482d0b03a40084520075214920100c014860003003d101022012601ca44d90401c0700a84c592103100c4150b05451051800c2103003a46d81079500002440b560703025004d945801c10400090201d9a4000d0541c1a011101408100c0d1484204060076005580181d4001e4007904554880e0340140000c00340c0c420180180d03104c840040303416505540144002c103e8083e00011540c041020380c2d40500003614080799040d00060502c1d00505c541c008500445000f80380d10340d03642c1c0b000c040c000f0904001c903018100b01c2e075407494104001441e01348010070742808504208003060f824902144e49003001c144600c0c0200300f040c22102000040d000c0680f099070704d840b0849081d04000802c1c0b0061002e01415215050034811750b241800360361442d64440100e91307161200d400101c0e03500071002c042d141d542d03034400705600d480000d40c40c000f40b246a00c01c1440321207600f00c807001c00084111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 335140692 1250 335139442 335139503
    0x10309120f021207120c050c030d200105011a0a120c030b130c020c0405130f0803072604080d0f0f0f0e190807030903121d04091e050109 60
    0x240c030f201e5800c240d10001c01d40201e4000602a41d000200540514410104c00c14030900580c1202c18424100010a0600c004030340e030342e400a149071f001e091400d8100011b00d5243d0700308a00810466143c01e20029110094000344000d168001610f10031542c071030903031b1070404440810204460a504e050160003800c0002546014080962686140541520038401012400e030003420601410f00100002840c00401130135602825604403c08580d0400f1071962481c822011582c0d42d042c400000307444140038407101000c81c559070a101c0ca200d840c140f80a0382150b44210229280c80090385500040c1034111a160000e41c501007400c1780039000343c0c01c110850b6071036a0040050440203541036484107031580c685d400013070082807180005031603e0020210a0301905c1d008903065261340e60341c1d1045c028403411000044000341010100200c482001a1112007120100220585035840e00361021003030400c1070f000030b184408001842020340001102c07560000d0500c0200049103d03458944c0100d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 335141942 1250 335140692 335140697
    0x30e030d030b1918020f0d061205100e0706080c1209030910030501050a03030c0f0f05030715140624310b0d0903050409021308280809010309120f 64
    0x1900c00c10f03900c116040e03000c2552110480c000344400f000c8400d002962108500c00d01c0700c0d20400903c4c0140e042407160401030465808034142d811110300f0070901c0d02c13110a1090f4042d82c50302100007070b00d0b08001442011210759084c40c00d00c0350394016500c085c40c01441c031805100c2c40c80e0001c019104201000800b2201c0303003114200c0380c1e191003402c1101120401d0281d59005030b1418003d2020a024182d15050a4070070b5001c0c0c82c0040941d941c031104100300150465450b03001113402130400071040040d203a01d0048010800c6200078128414640c20b001405130b07802240e0900484150414a50394100e50100390f0120369903a41d030700e908403040390040341100c54100311801313801e84150070106a0700003151501c81a40b401d04c40c0f101d480c08020200140228184401004009900c014a001a010607a520070295041c0c0e45440c194508103962036003089021801c4070006143c100b6160704c240c0c900d641001100740c4502e0310400590060007804005081c40020000903045141c9c030481000060140d035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 335143192 1250 335141942 335141959
    0x61409100c0e040b04062c1e040f020f1207031a010e0a0b0303190309120305060d031b0803010e011e0510030209040f020309070f140a050d030e030d030b 67
    0x4800000841c0d03074126440300000e110b840408524901a000300f8002d20b00101700281d142e41c1c401d60810034802d45041d04c048183d00651100d120030b41c400001c0d9010140043c00142c8a160b040d18940d00280217000903c92100c0c0d000c01d10541d2940b01080e8940740d8040c00b801100b1240c070b0b10b480d940f190316106c01c54401d040046102e201e2255490018100d8000c01c80482c03013902c4140d4010007030400103203203540510060040c010b61801c3c2030b401101010541c1c40004000c151fa0400c84102120800c0590034141804107128181d2204c8914000c03498040c1f0308512124a02c0c0e512843c1140c0040001d4502d11000c00040742c4031320324028450484445401c80b213000404a00b0b90800e0010510030b10b171307200c0c00e00490ba02e412802030b0020f01015100400000e030003041ca012101c100d8009990409241d071002409018800c0c01c1d604113005040c2c82c20403001510001c0c000a0744c804010f0048600900c0d83c0b0301800100360081110a0141000905841c1b0440e1728200040003401040081d5108a50340c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 335144442 1250 335143192 335143213
    0x20a0509030606120a080f0c0105151206010b090105220303030c0206090a03021c0e1306060e180c0703021207031206050f100e06070807050606090f01081b0409061409 73
    0x120000701c0d010b04c5601c0151a92038925110300c3d0309508410b0008000ea0002c20080324454400e00c111849107401d22401c98555050b0814080070081e00040f060060340300400510242c01601c003640e009000903c0c00503038075051040c0d10030061080d020500d4000b0740c441c0c8040100350701900301040c0401140c0c2199070315647e80415903558007031f0070300c0640540c0018071030390021521844941100c040a04104654410000200705001d5841c0940c001c2513680e0301d414032034941e00079816031200c1ca0841e2416001c0f40e1102594440f80c0019002c0041c0380000120002014000d1150030803245484202c252602c580d400c01408a25000074401c000301e10340b01c1d01180368a4856003030b901e68403010341104151078980c03205689030007075a110158044810300c886400648140e0041006500c10400360815041280c00d1046401010341202500b400c0703c401803041c08000241c1642e000c20f480d0a4007010041807000c00c005010b0084060940790034030840241d003109114100d80182c61040850317440d00742 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 335145692 1250 335144442 335144449
    0x41406030f0604110c0a0f0506010f0f17010908040b040509060108010e0a0c091502010219140a03090809090f040203070510021005100906030c0807050d08040e0403090306020a0509030606 82
    0x440709260811007a0000c5a41814141d0044030f10500803541a0316040303205810070b142c20300a02d4100d401070f15640100c2d04200003880f00740d0052070507558020b40b150415042140d100da03d40242d601c5d000310381c80c0034220300c5400d40216103045d0f0851003441d5901c2c2c80c0c001e440582d600a0244500402400d00800c21070b5100b24101030484c0c440c4508406651142d800440107800710050f20030821140c040e01046d007035408400954803005035000183c2c2c805517005100c402220040440c000c1c840d0101110242078207002c1101c0c40105503290000e00100c941c989240c050282d5242c17180c100c148202002083d004d012036090003140200c04070b030716a9507620100003111588071010801608a5244885000002d8020a4104c800d0903140145561640914000c45d100c9510617102d20707841403400c024030740c1c0c180012400380c10151141031a5403400c0e221070020348610b201e899075411140d0002414540f007070b400080a1684031a0941d65000b05c20302c01001c81e00000d850078070a020f40c00203e00c0e40e24 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 335146942 1250 335145692 335145697
    0x11030408040603020c0a0203120c06060a0e0105010f03020d150503100524010c060c03020910050c0a03051812010b040b0613090b060c010603120e190e09010605090c041406 75
    0x40e8492100d514080c10032508501a42150342402d0b81482402a50300040e40e0034002c0e00c5004c1e000d84815902d070700b010030440e0b240c910090100c40c003c1c5011041031149011a94225040d10001c3c00d0861180d030065001f10002d1040d1141c10081601d071030001c441d02011214098112038044044030180c00c81c4143c0c0104468054a0541c0c5060390700f003004520007545c0c3d00c6030412690505014682601c0c54861030269034000441c41c4c0080d50000f0f8030440d61410444010b0b059a081c5043e82c1841101500c159450110710740c080c00b400341c041051907900d880c40c4071036092050301400f0030b41c10070281c00245000c0d0200c0710089200d1400d00c104034002c0d007050010b40c1d144241d000c0c40c0a40300e41c54500b80500a143c01081030360004410018440d2560090040340700661003410a1250307a01034400040c41804900d240521640b0500440c04001e82c414410f00c068403110096180c15484181e01140104110742c071694000e0f02280820880c00040d8014108403000386406400780c041107800c004052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 335148192 1250 335146942 335146951
    0x10e0c090a15170106030c030803100f03030e04390201060602010c050403080c010605061b150402060304122f010f1e050403121b033e1e030a1103 64
    0x21100d500300b0821401c0003420f20350780c3c0b2110400050059261740302c0d001c1120f02a00190744422000090201d030141c004903d1008100030018404a14215030f4028190030420021510464484220014540040b1000200f070304840c801c0c12140c1c40240981503200f0000c50810003d5441c10310f001498a0043c05150340003d92030796900e2406085586552003038100d10403040856588000114142d21000300504003089580c01c020382c841844030410b440c290792420380d00884040041803100503210a004d4036002a804041c1660911400c2000c07030300b42907824410b11816242c40e611803200c0c41d68074646000b15460130300920a00c26041c1d551801d41e0a503920508230b861401d00740505a4010350f011940041c401e181660009003c03000318425101c4401c8001600c000c0654502c1c41c803601132207410040a61207807000c2c0315258008503d07104c803502c40c000940c08002c6d4100c0c2405003100c90203c441050f05510305000d1860383e11008100e9820445a040080d45040b001c0541d494000c42038038410f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 335149442 1250 335148192 335148221
    0x1507030e0102070f151101020f040b040e090c01080c160b0a0b010810030c0312020a120504065c070e070201090b151909021e0c2d010e0c090a 62
    0x10b442509000303c44606c071140c800e55a556090081d5500400500d0061009107450043d064486003080c144840303120b0040e00b0648950b1000d100c0c2102641c10450144d8042a41d0752243d845404050850741000941d10000305100404000c01410740700c0c41e4000440c610007030b601d500c608d90f101ca641050707080050001034856400c0140400000321203110155201d000c034030644003013040a07510a069035070801503036408200c010174207100041c0c0c0002115144041e002c425030350714020404081d94210ba00420f82441c41501420f598000b180d440c150b155100f21501000c80c07041c20a401c00c0d1034046502074034601c0c170326000128104610501032083d6240d0404d0f40040192a180101d1003091a0442841d40000300303200248144003040090000500300c603640541d03980311001540301715000c6400050300d40d8030140801882c20700c00151281c241d00302d01240c00c4c01310079011010040300030091001a00c40d0b08158041e402114081518080788070140c0701c0040d2a1a0707c0703100000e5030b45c4044403401c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 335150692 1250 335149442 335149469
    0xf0b030402090c07021903061d030306010e1005130905010303020730020f0405090106080d140f0a0c0b010602030703120c08040b060105130807050a050301050708070e1507030e0102070f 81
    0x10b8000880008003100e51005042940d11b540b41005001c0030046171f881a41c8141d51184410b241e00d9807982814110b40448018610350716207100080c01003106c1c448518007607460780c11403000030b5000f00203c802a070b050f40c00340c0061a03680e00c0035601070720090000700c00600580c1c4c1d001611501058906000c0c2d054480c8000048480c82190081581c000364140d03032000552000210988032032080c180692130400c004515241414041440c007554041d00354100481d03d0702c001619405030040e00c8110a14403800c43c1e41e002c100d4002c603164013a101002d00605a04000096001d4002005000c0c49200b91100d0401082c0c8080b441c0464070151004000b08189074000b80004802e1352007650b10103014180b050600c81d20040309400c280a81d00900f02a6000350814040d51401081160040000b00c0080c0200e01d420700009045d001c1c0034040300240031001848104a545a448a40801006421041e2200c8044c24020140c40d42d06030300a001d4018440b01283c02041192039000350b0b00e80031f800c000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 335151942 1250 335150692 335150701
    0x219050703171e160f020705030714030c060a0804050709110405101707020708151b0309010f020a030f050906060f1005070203010c08060a080706120e1005010303090f0b03040209 78
    0x11520740d0000c02041800d441d00303450008101c40c44070f580d80200700c0c500c00308414205898014142d584560340e200155801080e00b04607958000401000b0b4030001c968000c800d90301800400d14001e952540294407a00100301e001314940d0001d00540705a020380101c4510f5075642407030000b200e003450016a0b440904120510460903c0c04084034145030a00d001d4009503010020b03844000c809595650050b082802c0c20040308a041244440d04500503c0203016405d10007000d00e4415100c0503010403040c0040700203488110294422070080280900070356607106107030030050080c8001e0700519000361030078011a40c4040d002900c203111341005052080440c06003010043c41145a400d44020090100f00800040c1c80038000c1c0c0d40c21590586619009007010000c10240c40c1d0117030007100c1654400d100c20440180e200345070000c880044040068407840000c0517509111381c1881c8800540d05040000081562001c9160201d60003000c0700082d458407640d52a20030301c000c1d5030203035000703010b5000b04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 335153192 1250 335151942 335151977
    0x30e010503070c0b151206090a020f0102031e0307030606020a1101030216080d0605040506031506130204090c08060f0d03020322080a12031d100e1603060219050703 72
    0x19a04001c250500c1c0f2090002503444c400080360440d161400402032414003201070030b040c203502d800040b400c2e000e84440d00e00101034955405261030040e100340a5a1600303921640240101c0f54408003a04501020300305184400540d035200341c0c0c10b200001d240c80e00020301180701043c8203150035880808055205209001100650041b554bd51071102c0011454000950f0b020000c00e05000904000700d04d080c541401c120844000404050180d000001e0300c981c0c04010a0000d50b1191049030800312284082504e84000d02403500301a602c549002c442081c0720f070b0002c0d80f5511a060840703490640c07212101c00d01681c8888410000c000d41e0050004000715030320360000c4e402004200c01807205080d40c41074030a1828400c03090a0791000100310410041c19814059101140b4004010103000c40f090140a503850407201d428400299858039000c244903803e11014000340b200f0b11903179a6980e100d0130010300a50040700002035075404a4050049540202c0564001c2c9405850380c91250300c070007010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 335154442 1250 335153192 335153197
    0x30d120e07030507051509030a031101110c160b0a1409060c0105011e080111070f02040b03010c02030c1011071704031509060e06061e01020c1201090309060507030e0105 74
    0x115414161114104100c0110401140e0001d500403002001014508420b000080c0c0c1c84d0448480190003c111a68468600051144c050382d8149810744031621206030032401406011407840d0384440c0014200b20a500c0003401e4a141000d50308550070407030b9540003600c40d6204070900381012610200c4481901c4502a010b0144510701801c000c3c41c1800c4800f81600f181c409820074010010301030300c501940102e1a04490203050940004c00ca460130340d001407a40342c080c0050080201d00c51148080464a981e0058a070080b0054020b0080701115000a0b46903002003c00b500c842c0304020101c1c001e52818010300407441c1c0d414025a1802c10140c49056481548420050008108000c00400101c440018481e121a40600004c6e5220719190241c00c0c1c1e14503040340c1c0c416a00c1402400030582d5844601455140c00081ca0421407140c500107074100848040349030f900a10038046100c8415064000340d0100d4403030740e154558036854460582e024024410043d0004802800340071003940200c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 335155692 1250 335154442 335154467
    0x10c081f05090f01080613082a060403051b1504020607080403150b0406060302030907090509070b0712020610150503150907020f010b1c080906040518061509030d 71
    0x129020380940700c0c800300e41d64160640d0340340480c507140e900401104000740b00d0170390071440c1e881c80da015600458850001c90b0142d48110b13004041401c40042c03003000d461503412170a0301d00e002900e403249481d08002d8100c0d045a074140a00c8800300d294058101d502050a55000c8044100307080151241e0702030101580004108031140c4004000201c049031002042a214007615900403a0603245035007440103540003540034005140c014024401c01c004081001010344841040025090b500c0e51961483e108841c1e03c854040c4100141080030711a2050040700070b4020364089403041d40700c07410b50a9010b840d520400408803a8800740c200c100d48a0002103800207084641c1c038140f15015030000d02a51070980340040940c0c84901c82e09554003080c011104803840490b415521325145c81c01d0b100b5030b40341e61100205840c80020305c2d007065940e80015100038040140610808040d50030104240340000d4546070f200724120042810180700f803808440100d0400740241c200700c45034450507a8064501103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 335156942 1250 335155692 335155741
    0x1103062a03130203030c0105040201020c18070809030405100924052209060e090105090718020904023f0103020f060307020f0f151006050717120f010512010c08 70
    0xc42c002590341000a007866070300c94400020315050510000e07180480c0c0090650180e43c00840c0d14003140200340780113031302c28420305110100c0c0e92014086c41c11840749800c91031b84012128200364007264000b18241c140c800220150902c07038030810884110080d04000180011400c01c1a2403401d800141d9079140c1a1441550b0407089441d40000d60940c0c0ba207411000607003661900300b0096690034041c413600201c4060141480509001c003558001e00007011850200d41c00184d034484580301c903412584400f4003451061400e02c01450142110940c003e4021900021409003800c4003042805260483c2d0b8000c0420503d80e200c2e1090182540009024400b5801801e8010751801030600041c00c05201e02c0d400f904500108074581c4000c00c1c1c0260102c656011034040034010b180c0c101d811152019002440c801408800c40004000d070720034054071710601e50030b603001d1041002d04014424140c1c0d00481d1151550700904070200d00700c078110100ea100081541000c50604001d0300c218507080d442c40c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 335158192 1250 335156942 335156971
    0xe01060906050d08070c0b0304141006150507031e020a0c0f060f11030c100c120e0c450705090a03060e010209040504050709050601111c030b0d1103062a03 68
    0x50f021400385410880c2d0076034061765105103010741462b05110880b05a07000c00d0080064504112030034250245841c8030344180540007035034005250050540200ca010380d200140040d100c0c5580080d21165241000c0300c1003030410b60302040d07204004002c4400c2c1d40da60358442d40ca208511208449a000400d849a49800100051100d0000520000d5940c00e880c68006c102c80307084d0b65004100100c0400c078041e4031850000f0465010001152080d054403044034182800340804607940c80040305d14450082d4110408c120b90500c030074400d8565043d0303810034030604c46565078a5003550940f01741c46201380e010b04480401d01c0020a15805510132502c180d00050030001d51001007021100140c800781d80f5135000c10410021824140601c40d4024001c3c07901401c40440c102260f99600c5000b100c070515014524010440980b10783d00007800501e0060680031300003154104110170852a4503a00e019000b034070006452a840119107020110944120b1034604502e50740c000000e800141c51000b0480c0700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 335159442 1250 335158192 335158199
    0xf081506161a1f0602060a020702040b0d030e0405180604060e240f0601020712030302030402011707110606040b0607021306170d080106020a0201080f04140d030e01060906050d08070c 80
    0x400c0c0b540c11032a0118141140075040c25401e88540303002104010158200ca01c206200c07460340400d2407604414100380c0541c840c030151001601030034a44107815044a04545e00009241e070007421b08031018019030f401c1050f620355207202c84203040c54070a1509103604c11808240042c1c0d00d948180c8c1c403101b40b5000d0381c41e5040c0e800381102c1e00341c421100105071136a001e000d200b002c3c4400c1c1007040d000882400104466460101c60405074070f600c01001c1c0605501000080669014500e0750450b00c10b0300b00910020f00c0d01c800040c294042e5000301c0704003403060500184103410144195100d100e40202034509003811942006015445000b038240b8180d1611800104201120b0b01c009441819001a200800540f4001000c40205a00c00c008662000c41d1000c09030b42c00c41101c50f0000d0b101c4c41143c55035983d40c28620329150300d21045103200d00c625a00783d60324582c540d000050391445078000b44981c5e80d84002c010192041e1740102c07035001e00034410440010b40480c005040162061503000e040555 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 335160692 1250 335159442 335159453
    0x307091e0602011b0c470603010b0f0411040506070f050f0a1104050402040b031006090e0616050901120e07030201140310033207060f08150616 63
    0xd1444120306540020503052000640a0040b0100b600031a0701880403001c000c0c0e8018041c45e442e100c0a0326090300484010f102420700c0200b0034203060308400114a0b1840b122001c005640001e00c080035988034140440c903585010b019110079220001c000d03241c0d1200c2070080000a100682002d0075600080100207620b80b50a00a450070600502c1800705540090402038102400800074000540203000700500080c21407210021800f0150b80000e041d540c2c40c03000c500200348020440b58503114590240c122580260070903c00d07940c00d680140300c4e0021f0b6024103079585d4401d80d180c4c4001c4894482d9190054442c030080c103101c00051510310002d0490300c0000f011a01d10940c00d20705500030311414000d55030001c008020115114100c0740c69850019001e001050042c04028580c0c801c040840802419030270b2010001030301c011100046070f4500e26501e60f10541c33481010049840f020001415a000300c00c0c0c24420200001301e141c418051300108081036100c004d03402c03c04100e0a200d08007142 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 335161942 1250 335160692 335160719
    0x81f060f020106083003010605160204060503100605031b060306040203092104030b0c0304030e040902040f020c070306060b03040308131703070503150609061215030f0d030e01050f0705030709 84
    0x10f02208035010308001014002100e05c2c402c42000315040c0400040080960000490790007151403003d00d101e041e01d601c0000c0180c0441c0d80004d41c0740c070a50018074450300950303100c10100e80040741211800340748604051451159040d078280e12074400d200207002e60416400a581c4103503004181d50324000088221080f00308614852690890041030a204004a91400c0c60308246440d6800e4118507150f60018070789805082205d002d45c0d2207080403421511070b600020180d111920b0155190307410419072070750310711491006403006030400d800012880d02a5086038020b80e0181d43d807400356590b540c1c030307000c007007030502421510410000b205904581c40240654055038140d62102c3d030740d040582ea0509400c5031880140d00c01e1204003c1c0c0d1141c1c0e070b111421220036414141c40d20480d03940d0584c12541c0200916040358042c000e48040503503501010501484440c001d4904222030580030f907a4500300c42007260301008904150000c150003034000c0c00a036901903141c0c500a8403654980c4c0403006a007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 335163192 1250 335161942 335161963
    0x210403062c062d0402041a1c0302100b0105040b030c0904051303110c060d0b0316080604260304060506040b040903020c03100207200d0c1401081f060f02010608 70
    0x20340004003400070500c40c8800340100f1610181c004502d444411410700c5450002820080c0700d29954500000c113400703200c102c4100c9590081091103591101002c1c10400310480204030018018421064100700c2144120040708606070345d00c50800b410000407244903030029080c20f1540c10705004402d181ea60f41d0180300d01c183c420801160880903a464060102e1520950960716a008080500b205440d03001c1620407160110074003161403044180440d0504900e80b07550691002da210300814289400184075000d1803094492800c92014200001c410140302c00214008807002c10204022034003030340103542c005000a10000f140c00c5948001070481e25400d10440258110140200b1149014410350900e01c6001c1410751601555640d0f141c002000005400724a01d030000d61070380309032180307001c7c091003035449404c9102c1291280c43c0f030580f008070845030a00140907400000c04c00d445103182e1042070000000303120040741c102031081c0e40b081038500010007150343c0e400c0c2c00076039010704101002c0c94 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 335164442 1250 335163192 335163281
    0x80c0d080c24010b0c0d03020d09050304030c0e0601090b04060503060609090a09060c0f0503010509090703020a0303030509011a061c18030e0f01091203080a1b02060921040306 77
    0x14a002c0b01500d420710741d4141e0103502e070714038240062640388001050100c0300220910380160340c0d039035013004100281780c0f044000d0a64131000c0f4001c01003110322402c0009903100302c0c22042060751594011a1006158040c0200483d000d2000f080707004c0c06030b406541c000c60024880b606045030034000c81c00c0540101d90b00d13984a911511800c0901401c0d02c00c1e03100c1c001d0700d80b0b4107480175400c00501424911061094600481c944d00003c1c10b240001e0083c00040c2d0b50050031a501c1c140e9a042c0100a007509039200000b0794a070244208180c06a80000055504007400e014100a6001c0100c59942c800f101c51644207626031004249000440c403955804a1082c3c41d1010244241c2d41400004a0018409410700c41c94100c01d1080034a04504600c1003a0f061800300169502c200ca680003800b1604880382050b0f070030355402c0c26040c1d004100d441c400c4050000b1030307110b402c08080d201c10081e448c1d031040105000400052002c10800d0300090b00517080c1c0070b0307000010121480c820b8101d41210485d10314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 335165692 1250 335164442 335164483
    0x3090902220906060903020f03010902030f030a02010b0307060c1e0210051c0908030610022d0613110103020901020c1513080705011e032d0c0207080c0d080c 69
    0x202110402818400b40c01848401c0209505002c0080c0c09036501d0700010744520281c0c00200c2c000e6074250402c04410f46e000c0d0540d000416800343c01650780d00040c4d402005542007180003d11400e000906c081202e8140d50392101e005216152500c04000c3d4421145141c021510302e4005a00ca40186003402c06c0c0503641d00c1d660b50390401e0010a841c0700c03403455981c807a00b49012940455000320030741c0d8000c80103c892100206a2020607441c06840d43c010900a04540780c0c10000b41102c1c1c50940554840082950710030303035611b000384c41c00c500c05610041c01c84454000f5803195521a81c05800000810300440d00200c0e84100058a00520b071440000046400180250140c402c0e20310351009040d2980109015800d2a002070700802e040448984c0b02c01007018181d40442c40f03a001244480401404815080310101d01e04241800f05141c8076440783c108030700c0c000c01c684000b90309021180c0c841c028101d007400c800100007020145c000c0c25105440188442c11040909000e14407003100552001007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 335166942 1250 335165692 335165737
    0x20310051305070b03240a03030311040f0e0117060f161704140d0203070503070b0402060d230903070b0f0903040b04090203060126060d050712060f050f060d03030903090902 76
    0x311000396403808500c0650800035245611f44013075038401d0700e40c1400d021401c0e00340004940b013240241c1d4010f1030510b14a01c0009212001040d07028140d419400c800044e00d11144280c590302c4000303649030204201c0e0303640003c00c020b40300e540b048400705180c41c150030310141c00000750b101c84009903000d0b1032010340f0081c01100c0c0d403410024240d401c06035001a40c1811959204d0395100d005207000544500148000582159951000c80d11480703102c400811807801d1900c4c026109a0904120424001d490004900002c070b0000503120300a6000c0b480c943c5a5880070294006000054118078191005010100b0001a52005400504041540162289070003c00146078030300c03800030403608811100f080186040c040726801d0303014005a43c5040800c8452424528050141d40040c010100c0c40300d21100700105a00840a45182c00c141880079031146510001030000603140b40fa0310100c0c80d100e280000e40660003c0c00a54080c1c01c00c03e1741c0c90b0f83c2c0c060312020313070388255800c0c0c2d1f06800804500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 335168192 1250 335166942 335166961
    0xb0316090b0108060112150b0706140c040b090f130204060f0905090106050f0703090305030a09030c0b030f0721050103030e131a0402090609030307260304020310051305070b03 77
    0xe201941c402d10b031154941c1009030020b04030000c644c0750040d150b5107441142c03240380c00300000c900040026000030342e0340300346905154004108070818a01240e80c042b0218100c0382031310040d64181c400d034441e0b40307243c15040d1040129038160030034007540142010601d51902074041c0302920003402552030b154901d0042c800024403000c00380d04030612500e0795100500003ea80710050b5142990490700311a6204480d060031364502405500080403840006041200c0d0365224036808102c0307124004075000b494441c51954243d010072100348038058810000500c1e411700ca0094191310300107030741d07030f0001040c0562009030684609806c20390200f03840c01c5001b0308900340fa038070840003110411001c000b11060341c005101c1c58410ba4401d107100d55008074000510b59035005c2211350112008045275595000c40c43c00390313050041c1c50044030382078050304511000e01d503600044034840d075401005043c000043c0350031000109805007118602a14907582000000c0d000c21001003c0c204403200340e030f00c2c0d19005842 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 335169442 1250 335168192 335168201
    0x1005040c2c040f120f09140d0f03122f130b03010b09100503090604020f0a0b040f030317041703040c0b0304030e120706140d0e19020906060403030e0f040b031609 71
    0x104405c0004490050f0300b01039101c00c920050314510440041d80d030804400261880d02c040c1006416255050000001c06800980c2d034130300046201c106010f9031940c0e1014803000e9045900c500e080c903440415030b822090720a0000c100d21444101c00f0f0840b5a15541060003641003604012080c1c10005035101d81440d2050341d000030001c0d0752410703a15518251100300d03142da5000d04020301514203481410b115036290001000030744000e194003a00e55588440f50291500148026804a038812240e15801e032040031030a840303190010301e0b00d0800450713084031741131a5000500580348003540c9200414492811402075000701e00036030b190f401e0180381c0001c01500030240c040e40041d0350301c0342a041020b560000040b082044030000d1084e1601c2028280350003502549a42813183d000d0440b018188500e0240c001240300d0003526440c1140e5034400a00225200344c0c040a40820424a1406030502d030502c02d0421070b03a4060004680551108042880c040c038a1241101c807061200c821b001100c0540304 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 335170692 1250 335169442 335169473
    0x108070b0702031c030f0903031409121207030204050a081e0105090a0f11030105040b070f021b1903060f090209060a0312080702070f0e04051005040c2c040f 69
    0x103441c40d04941d540003a40c0d0b41140075809000c00444891809824026404580c005031200c1d0b00f40040d40007480c000300240400c22284030100a8503020400c89600044c500b5052104800000d01d008103c4419a59405004001d6070415408010100b01c540b62903114600600c003001c028030040916480030258011418640002d903031401c8200020840000303800c0381c10035003044a1949803c1d041c10204031180318440c03c5c980560800e0144020080c0c080609846004140e4030002420b40140d000c03602c440607406612046481d159400781685407694141d12034030481d030195242542d80340d40d04130940d149090428022566500f441040d810700002d01e036030000d01100c01032141e43c1140d03100b0b00068030303000c58070301040240c2e000142494005c1108202410403144140003940c3c0e60800c200c6221403c40381151580150b01d042e280004090040901903544964191001e40c00d00f201211a0070901c800c410011410105640100c9030014806001d41c2c0103621807507240c402c6081032808040c1514 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 335171942 1250 335170692 335170709
    0x1080f0c040f0e150d0b070509060f0a0206090d0302030f070f020a1a09070f05060409020c03070c120c05030114040615050a0f08010605100912081210080c06040842010807 75
    0x2d0450300180356806d44582c8520103040140d03c0700d0100700841d01c01d020303449050707007881d40018428480ba5000290305219030046411195440c0c0301ca00210180d00003961030852424500e0040790209010703211a01c80c02100d44100d40d180c02454540d04400038090b43c802184031070440c1888803440091100001818018804000319840d01003c584148110300c100401c00340d001c5994041c10303a090041318007480d00f1951041d003141d143d404090110425600c1103800210b160f000242c641018090a0040741c040c0b18007150f29952a107400003d414903400b419200c102080000c60517030f50b40c80703410018002900080c4501c42c2003c207003c0c01c4495582020b88501012180780d01103940c071012070419140c0f140c583c86120141c0c0e140030300690190040318a0205000340070024001d1100f10220111101c400c01c0f1106510f1400500804d4032030b0340501e14141c1c00c80c03117000050f404c40c001038040c1c10860b8565084500e5003102c49214811107100e1840801409000401004400300b1031800a001d00e0b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 335173192 1250 335171942 335171959
    0x1a0106030c02061303050903030f13050d24020d0608030c01060608010b19020109020414040b0714070f0f0f051b03030406050405040507020c040e070503010e0c01080f0c040f0e15 78
    0x440040d5a41c0700040c5521506500e00130240c0805204509071514004050103d94995501401d0507500303030001091000c1d40d0901c0310000074103240c0308a401c140701c1d4103c91010040c10b501c0740042036801c02c00804006154007008220b041c0c21041c803c05006140b110099502c03040006042c1e400d5400b581c0c8801d080080d454014090110031804461041d07510b0ba4041100040c030150507805000b81c000c1c040e5109140004004001c0c2510ba0302c544510308c200030000099075050001d032408000d4002c107140c3c4c030b0400d20491000410b0303400007601a5003e0050106503102c01c0c6e80e80e0304084a079a02c221050b03002170003849680b42e511481c00e00846000c40c003441c00c0c02d0401d24010018080e1740b01d03961065841d00041040513000784a5072075010340c06042407000d2a15440210350310011407164074001e40c688109581e0b1a04007007440390302da031710580d5604041e888956034000042c0000d0842110064100b00c005105290300348910014100e0b030101c2d000c14070b04030b0031510390005d5014400380034600e81c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 335174442 1250 335173192 335173211
    0x3031801022505010c06060b1903241a0c0303040f14120a03091b06021c03050415050402010908160302150a14161b050415121211010203041a010603 65
    0x10800c0d0391040c0c0f4800e20340034904c2d00c0b09081800142038203621080105900158040c1c16207156461301300c1d01030f5143c800313212440c181c81211400c050300708005501035944402c288680d0b8002075460b0041c46200c9140e40c02c0bc1c580071a05400e40e40152411541040c1c40f1903c2c2c010005c00c2481a441e1500c498043c1c5000a403090450541c1d1140b03c5003401010b9403040c070302d0104000305610b4030002141109942c0503644440700650341c0c584032140c40034284860082c4001891090081b544941d43c050940b0b00c04881d0156032801509000e072089050008a14000c0388402007002202c3c00d0491641360070240303034510300500c4400c0704c90418944994104106840013647c1002c0000b00c0d0765941e0441d141d480036450840060b81c1c9032070000a002d44120048030489010980b820010341382c003114104035204030604042e04040b198412441c00c4022220503c002c030b5010014030100c4003460410b00843c2601d00303481d0f402ca03801154100c1d00c11602e50710301d0a08400384581c441c05015241820002840c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 335175692 1250 335174442 335174503
    0xf081b0901080c010c030306081c1202091c080708032811090906040b130608190203070b07020f0a120605010506032e03141005090c01080103020409060b0303180102 72
    0xf860703a00181404a1510081d041510a911460080c404003042d0b5980080c0c100d00000390b0400c0704000d0001919801c0c446074050070910848150910050190418050f140e140c003440c84800482076031030150a0001d81c4c040341c2500300843c0300d1417681d820600c5010754040004180f1403060440030200d8540705010303000310748e0b0310215003601c10220344c1c008050381c4840010313001e00b44003100c05400c070692801c2d170a4002c14540045041d102c2c1e040c140c1d004d00101a07108030740748119004c082d41c90b50081504129825400f4000c0910358000b801200c9244002d40c00309a040100354854614884255081c0d41484018400c00c2d026000c211201440c50030000c00072082e174000040000e86103540e502c04031000709402c1c403284004550140301180c440411100954881444018002c5520300349030000382c0d58000452160400f0005840d400d8059007140c0902000380500201103c0c0a0f81e03c038051403041d03504102070207801c02c40c00c0401c1040c40100e0f000a0800050341c005151000251038140401075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 335176942 1250 335175692 335175703
    0x50d05040b030f0916080c090603010c08040f06020d02040b120a0c1d0102010e1e0706080601020d08060d0212012003190207080f031303260f100f081b090108 69
    0xb608020103d800e4840303503142d40c02e244101a502284210140c80069412004580d100c0c849a0481c1c800e0669902c20090500344c0303110300d403d00c0000e000b01000900160304070300b104103c80e018081c01424a0190648002260b019800568800e10080b600f06905c002c003074690f41c1d000013000c009220f001e800e00c1d0042d0002c10305280e20300501c40c1e1394001450f9640f00750301280c9480f80120841e0061000561400521007840044040d00d000315200416180d000e0100300b030094006a00405510851000c03c84664102400c01580401050107103070260341c42849049a0040e00400010f07015411520742d80e4985c40b40c5055109108180208150160300004003481c4032420600943e40e600107107014041d40c0b09a08081c0e90065002c000e001d0030071030b4074076212452486901c0c0c0441010649203c01e400c0b03544040442030000410b000603c055104000454000503000e22003100d217519200c41030a62843d98108442942c0325664130002c01d0381c4a00c0b43c40b50004190b400700c1caa541064211919003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 335178192 1250 335176942 335176951
    0x30e070b0a0e040f02030a051006021902010e030a0b09010605030c011209050111030103050102090f0d120c05031b0f01050a060b041a09090a09060c0201060f1701021e07050d05040b03 80
    0x15180800d0907038996014409101000340000c1c03007040b0031100b82c1c40c1040203402c141e420540451070900005e844a0f1014804400da03960741c0c0049c0305070701c0000800025086100d404030304004950b20510666203080201022151090060182e203113056608075003118136580c81203120b070f4070641c245807540e60011020400c4100040010500f400075040c00b6000d00714015040d01910f50000c0000140031041d806040d0100702142c1d82008611a00e0400101001c0040090609421008400d9130b09002d00c0690024520890559044c40c0c40b901c25444100300c41803045c01c00340c20003e10105204020710030264000001320041000500b02503c03107070356005070f014400c1c06800101e445a03808902005982e031040008000c1102480d01c045640058130707500d0800c070b17115400d082c40d04070014018007880007541c940a02c115601850040798020000100200c550107541c20001703201c424401d0100d4107424402c10044a84d50b50f024500366181c0380080d19100e080000500050101080d00c80440341c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 335179442 1250 335178192 335178209
    0xb1302030901020c070314100b01050904020c070810200c060c0a0e040c090303030b0108010b030a09030c020d030206011e03080d1a132f0406051b0703050c0907030e07 73
    0x120740e200320034140203200300c0844e42250303c9080c40000420010340451642903040c1800c1e01c4200d07078600e41c603409540c52246000d0205e101400b4170420381c2090307809071244100f0041114455a503c4031a5400c000d02c021401070002e48850701109071814091500d0811808280034270b01e40b04801d05107a8650750043c01d82c90020310006001700c2400c1c403400462801d017500410410540c880d8200240c0200d0319440110046414058030000c1503000c1c0c60340504075002d0162580ca10766a8422040050010f04022414800c0040c2000d000d0385610000082c0203100303400501b05541090500400040703020760b9000440c001031401c1c8009808002511540070080a0200f20b407c24a54132071007240c043c0b8942134201000865803600451542c00140e00d400c1c8000e08481c0b02c03006400d0207428030f0755001c402c41c3c01c1d100401c01000094032406c01001043c00d16182e103008410809101818a60a0b074029200c0c2d82c4210203509007450404074040d003007000c6043c1008400420840c060b213600007845131505c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 335180692 1250 335179442 335179447
    0x5060304030503040f120305162c04020d06030f140a03090e1e04050c0907110304030b06060408151f050315100b0c100b010215041118070c11040b1302 66
    0x20004642c0e17445d0100b44d4001c0b0120809006200f00a000300401c9905800e00f41c030380780710310b500300d4010300e511900e1b9542c03c0c2c0740d07008042e00100103680c3c00c8811035055811550030072041c030803141c851040001940c03080100c00700c0001181818481803014002202c49a0480b4100c0d900103500225500304030303030307440c4c014840310742e00c400603150804203100b101c04c01000f006c01000100705c0f011945c24a880b404403002c01e29078076103107400c0b1207001100e01ea6104c50b81c0100420300220b010b042680358844c0d40201910320380303500c40b0b8016081030011690301045d81c0701042481840c02e150b203007499170400c0442003008c0c0d4500d8940042c1ea5104100c80517494202e5140101c0c0051500118000280c40c0e660342c01503480c804406215034078040001286151440d106e0700055035840882c80c1001840c1c8000840c3c0b103034849440320140241203001e140d902c81c0b42c00c000c0f80c02000344501074501c80c48560b1a45036400e101e03803c02c801c0c0d0051054100348182d1420709201002da45000f00100f03180d010980040c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 335181942 1250 335180692 335180701
    0x5070902040f14030316060c0908060c0d02030903041508012313020714010501120209100f060f020f06150127060f0504050a030f020a06020105011202060702031c050d140105060304030503 82
    0x34114803139003041b590301d050524500018004203402c18042c16400d99565003015640b2039142d511b8603415201d00000c41781c00c002b03400302e5030040d40243d50060100e206a920f80ba42c0c2d40c5104ca6454590080310b000320399240f00400c00c4185c020303c2400b5561058440b9103000992100150681c0e050544482038a64041070503400d00003441c440806421a10008100550312216203030620302811804a100e01d8064000034048108951208119034100100300c00a41c01c00e074081e600c1501131660041141b08030a44412040b00400c000303401007403800e4901c1110302d400800101801403014032030000c00d4842410050b590060501002160b1440c40d0200e448041c1c0f4000b110b0612582c1e010580c080642c010200074840480403c1290030f108a8102c81c80c29038454003607099403403d10681d090042d0ba26150005400c200e030080505074030060640c0c510a0300d909440329a041d0055622000a60128403a4005111885a000301c0c1091030000d40d0b00390325000000716240320041004082010200c0801c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 335183192 1250 335181942 335181949
    0x501120906021b030c0d02010b030d030905031207050409050901090f030f050403140d08060306040309060f05120703061401170a0b0409082206080610030509030d02070c0305070902040f14 82
    0x111030f403941c404200400316500c0207980380e0f00e421542841540c2d00482400300c081b00c0c01481254500100980940f441e01c0712072006a006080d00003007030354140401c011901c054030102d400343e0b04c2500c0725121903032a142481000403c0b40c900a00d01842c0d43c0c90b10305200b000c901c840d070500b50141e0349032401800d1030640710821101805258001440c07500103030b00c04814101e010442c038401c0b484503591190140d07121020180c0e0703184281ea001c2c021400408043c0410380c072500d010f4081c4812414000d103462000c01040d41404421145200029034a8005000d485e00070120101480002d2a088500051000e004114044094141070a00341c3d90042e422190703c031034201400c8940c00c9440e40391191000c1408007040240c0340488283c0e5080e02d40003040c4140140b0711940110400742c6550160902203d06400412018048903658407041c0072018902802c0e00040001c5840b0300080d0116030704d580303013142ca401c0c910740146801a005100c28003d50700109225001c075803041000440f099040f0b400b2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 335184442 1250 335183192 335183197
    0x812030f150102070f18050f160509030c06030a0b031c0e120f030f04061b1707151e060f050607030c24021909061b14060708070801090204050112090602 67
    0x38040075a0960380010406c251103402c41c80c03c10314070760a010070b0307036441b51180141404450341d01c90309082210140400b480b0303401600303040314050102d905101001001694507002100c0403a09a0b0300c4603078100d9582402e1065181c0414144400c90351385c80a100d002d0191000c503030400f40030f15003141c001801040c0400521000350103400a0780c3d52381c1002c010f40f900d00da109001d07030000301d05423504640c2c40c00c641a100504e401e80103446584a480700140280340d5600101054a150b0b83e0141d40c070381c10112600c2003c107905802e40c805290300030850340300c0059a03240d07442020328ad0050001000181c85000448032481d6161a01c0c0b8180c43c803500c2c2c40e000d2158180b1004440b00b81820154941c250142d0082a0704094012010070800f40041e085276200c0c0c0e00d00400e000a28141c1136000182072501c0906440342c8941d8038000f40049810680e440c0810490b500c00001e00404140b00010ba000340d40a405000c10080030b5141ca400c21001900340003410301401038860ba901050414051682d06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 335185692 1250 335184442 335184449
    0x91e0603040c15090e220b10050f01180e06120709050a0b060a090317040503150402090601020f15190c12061203080610020109021503010812030f15010207 68
    0x8465101d0034181001002000103018582c2c3c0e603400c0310f880d080c0d028091020603040355a40c0281d0541d9a0b14030020f00d50b90018420206c1d0180c0c40c0c8136660001856072442140708508100d4400c0c64035280038100248003000d442440e051014551a08540f074024008010640d219a0340301109903c4100124004600024418003a0b00400201042ca018582c001364000c601008062220010034001c10000d0321407040c0c1a000b164024900700000b07540100310700004c00d04500c805040030f603070780c000c603040600308001c2c22003030000c2000304421403904600c40c54205d0000c1c4010b041100090300c100d90f40710b0f00c202000c0c00701c1c040d141c0010a038003000348102c3ca07900c00c0c0c0303081403100c0c8400701006000070008480702d0401d2410101c01040c012419010005640d8141d43d070f5447e181c80b40c0c8180880620b001d010b150440d500d420150015846070a80e40740b4411420f50041c0d0f580d0b15008440741402d11810030700d07003041000c006000300154000c0740c0760340120342160350582c1c2681e4000143d141c95001e91 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 335186942 1250 335185692 335185699
    0x1005151e07030c0c0603050702030315011209030306031b030c12080d06030503030406060e07020a020f0616150612020625050708010608122805120414010b03060c091e 73
    0xa001020180d20a40030b0f03511510840001c032080d9110302c0181c00390b035002c07200107005a00c24070014141d0b10501e00c0742007005406041511024100b0f540c010151416200e0070350210351120010001c00085031611480721001d1100d2060150460b594244c03213003181c2c4102303424010b0542402090010308000c4a10214407c14104040f0b41e0303070b1400c0781d126041102d0503a038080ca0000d0004462000c9003020744120303603990103041240a070f070b801c100c105101810b14070740080050006040c921095003a0b106064041c0051405400806041e00280c40003901f2030840c00081c0d961030350041e200c907416224180c5003202d07480081980645580c0d04440603082c064514403501e50002000c01d0190b12210540b103200301655065031890b40d000f0080d00c40d040f900c0502c85e0000180b41f60580c1d00d80500c0c08100081d2820034a40503103050105982d8109603400e40f565500310180c074801c0c0c0424415a0940e440a0b00030300000d29040c21044640e0041468240c020280300d2924145401824140d1f00c000c1c6008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 335188192 1250 335186942 335186947
    0x16030503220c03020906010306210302160e091207050705040e1c030b01021b090621060903122215020c01090503070507051518060403060c0e03061005151e 68
    0x506103031081103a0b030b201c140d000d14020404150554401e0045906075100d090050341c3c4011004c44418207649028400d81c218040d009a4222112401006400414515040390100c0c14144041d82c140100703551102d001c40c030b04010700000a040450554120740702110001440c000e40b406150400b603103540d405440f80341c0c04101c054102c0e0140c0c44007822035820303401c5810b003000c1c2030b04c0b115041400e82a070700c4e80040c8840001d03a140c0b07400318030000309502c80d0310034001840e68060000e00e01311080d0707190242c0d508007042c0c0d00981c83c0f8180711031798009410304204503034404030081c044101c41061006441148840143c0c0031200380c42d01101d6045200b00700030030004226081458807508001d10848080c01610b0001038503180c041800c1ba040e4180c80d10f003900c0d00010000244041c500000f111750410401d000000c00f14500388120b00101c0c110b502c0703050711140904101410800018941581088607510620213900c507034441d101224054080340303039102c4140c08010744804d60640211511b0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 335189442 1250 335188192 335188261
    0x80d081005091f05040b030601090903050c0604030c1b0b0d0c050408070608012603030c031e1f080d020a0b060f060705030a0806030d08070e1201020d0605031216030503 74
    0x9040320f072910100740400c0107a11500c4804201c2175030030705942154103500060041c00454015482070007040c2c4242081c9140070150a616404d0070070840d015004210381c02000400d201d00c0300179584642e61840740d01640305080c0305414040340070384540410710726039454098040320701076405c4402400803101201c24003a070b10381008001000074001c46030b40d0104100003100900c0c945e40007c1203001170401440c00c582c2d0384d941c4480c0c0c50300010b000d1140b950301c403819800c11500d030200440c001d1120301c080804040054541092005c1113078082c0b030460380070708080038101c0c1d40881c88403405640b1003440303c10340d21142e0019089680c9080141e501250001e104010000004000c101740105500c0b4081c0590741d401c105500d841024030400d020130201400a02910300c14008031b500002c1c01002c08050400321b2101c00d089030403d101840e021555030000303208030300c0c0800140a0b52002c0311071503883c0007501c0c82030050505c440c0600500703021010010403a02c44d04d940c06030050603004007008448085 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 335190692 1250 335189442 335189461
    0x80f28060614040f050d11040614010215040309090207060204050306091e120f0715090b24030312060102210a0806010e21010b041404120207080d08100509 68
    0x162040030049403404000c001e2408400c0183c40c21201d42201c803181940c60032082c0020081c82c01c80466114480e444002e4080d5181c0c1320f410f001c0d000000b1500b01744401c05002a01c0c043c1100f04041a4500c80c0080100080d80807001c001a41d2024001584414452510001a02568000e00d90500035001000014400041c04000c490b02c000c0d03400a100b0b81c0c0c5101d86865500212980000a50802c0340346000c105400091021602c07403601b1510390500c40c00303a88116100c4000444e400152081402804075544944100343e11120a00c2c0c0c1d10942c0c03600019549101d840c402121260354440090490307802448400044070701e11200c040e41e480000216001903000d80f0010300032407520702c00700b00c2d01d52054403030b142502c001030301303a181200d030042c01c0f062030708455800200159265100358640b500e90340148682e84080039005000c604245c03802e42d4103c014030900314110345c4000c60030441d80400180a03080a01c00d400d25100c1794841400c80d541b840e00301d4120030f800c16101c0c000d1166490 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 335191942 1250 335190692 335190701
    0x50c03040c090209012a1703100302010309030c1b08011b120b010903050f030316050f2209090c090501150917120415020c0103060501021510030b040803040b0a05040201080f28 77
    0x20b1080b5a03454081c5000c003461f1101b404151402c036650b154001c000d00c019400b903440030545500a041418200085a4501e500d000784d4070340c025801b0b0221842040155403d001d088202c802c040c500d00c01010040c80014581c01c180d05100e0704541d203e0007016070a1740105040780c080e44c0c00800307031031132101c07502c2105550b64010b41e14045081071280c440304481380f0840c00e84038909901c9000902e884a01d40f0000310034001a1800c0c0020844c1140c0000c00044030301c40e0080062250708510040c51624000d13404440d4164050101d002d400c200d0311118903840720b1000c09445861841056110b4080541440c1c400c0c88a510b85401d00e00080c041401102821901d03a0303650540c2c2240d248004840045041e41d4041c42154007582c803045118030410841c8150b15880800081f0404210f681ea0312001c070b22101c02c1c0c80030344144c1d0000041c0170034022010b100d59070186001a05011508103a0300080c0b902c017005001c8040f504070240812010081400e2a00b007e12031414074451005821320440e0042c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 335193192 1250 335191942 335192027
    0x106050a09050109050901030b040303270c14090c0f07020907110c0a0501050a0e04021303030c020907032003040201030e0601060801050f0307031a09070e04050a020103050c03040c09020901 83
    0xd4501c540c0000d041d03126814020655101402d484d1103039280d03998141d01b40d2005002201030540340c012020444614050210040c40c4444900e00e10701000c2c10922800103954004c15403510761111138220b03545034282c0302c680105410300156640c10011407824018000d0b0074009502003a8081403161080d4400d41c900b50300300c013800c2511007000003c410000540602d00c40d26021840c2405070018440c0228070344911200094009032030044d240700748960205d15500b04030b0209080c000340d034041d424102c0c90302e0f502c5449401c0804c80300685002c003080c041000c10140b104080000005021648282c010041782c200042c11a92503584401d0094805a424003689004024070309034101e0601c1d000980c82d04a0f5002606c500000e1100500808e01d180010528203141c421070304005104140d20007880e12172400f507001381411408074800101a90340181080058900600c14080070800d100c218400319140c043d0016a21603c8000603140045240f04520441d01c02105c2051410080116401074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 335194442 1250 335193192 335193197
    0xc21031005010f0e061809040c08010513031b0c0b1801030b030102120f0c040f080c030c0117060904110a2603040e040803040804030b090a060c02030a0e040b060f030106050a 76
    0xc941e01c40c401182c0100341440c80a00040c8220510295410108010304808038642c44100d000080c1d58080740c049501960102da144042c8041000a15001c0c452150050f403d00d1b8078030788510940d14010203140400040007030003580300e4024000c1000806021000700b00b502e03225512034088156610404040034091400302e41070a0b8185158034040c8200d4a64003200340c04808a03171204000c400500c2c9000346100201c0c84100000f089a1300f03d2500781004094030801080c0100b800d809140c1007000c1d1454160601000d000c80c003920501306402141e2100c000d8850041d156228109017238070090100415410106030840450035150401d00e56601d580b41c0c5400c4000800b140284558078800c034840e200c0314200c01004100081ca14000468015004000d01e40c1496180d803540c45001a0968917852558022080031007004524042e882800c1040d0001d581030584413000a40111003405c65280724a0740d50441d030f04596a00416500480e0000040030789a40c3c49403c050400ea0100c501c4401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 335195692 1250 335194442 335194471
    0x11100606030e010c180e04051005090303010305190c03061e0c57021815040c08070302070204020d090c0f0902040b070605060d0b0405160f080303040201050c2103 71
    0x540750082c01c03403e200b11600f0042d031410700c1c46d02d404035030500350160044903d8040c0761854503c20910740510750040800c000515034035450361a1003441c140618130049210f11a8440e2200414a040c1589048035080350000c0b404840000c629001c458900107100c1c2d0701840c01001c0c15134140c0c4412aa031070004c030204000c0d09400d101d1010000088006103074880e50301c0c8041411540303d01002c07061280d07a2600c9640c10144c1a960018907030030002480200b88003200341c1040710300203281710811000c0d50281c030101304174039000a00504490700104200d052640001d0040c0854130303a03504a80305042c1001d010084080b0920300302118400030b00c14030600c0080c2c0340000c03401c03404030310840d0301310399030104824a00b03001951a4005400300400d85540601c4010b4080085076066004510451288000e0002016440c160f606560000c0d04411410350442c40240305401000040300c6d0450b0302400c10035251070b01e001c1141d01c0d0211040008401d402d084042926800c0070344003650148049222458 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 335196942 1250 335195692 335195711
    0x30f01061a03040c14060d0e0109030f03180605100e0a02040602061f15090e04150e01183e10050f0a0e1f050309010509060405070611100606030e01 65
    0x7030050209030ba01910764852800204203111004c03d8101d040540030340014100780e03417100c0c01400c131400e8000400303030b90351903206000405a110446c1d400b090124101046070240c1c06c00c12407410b00b18840c0c000d115603a1540818080001000c00b88001c204050907144103180803250040a5046441884003520949010a003640c2d4140300352014660400d05011000386040c4005600d00651110340c07082c08104100481c140c0301c400329440c030460103180600040302080c890301b01110740c083d04486490340b400d180e43c02c07003124a5513541d0909401c000240c0d8000348665807583c41d442c00032a0f03c2115102881a40401d00501900203500301044420060f840300c3c1c08420742d03072442a0803420760a8181000059440303402100da482c3c0e54400980f0b0a1020407140c2801344c0c82041340740d040400b28030b01004200b41403400f4003c650348500c040b00504641e007020b82e035482c6c1d1030445014110610505041208041c501003212140031111118180002c5586441c0039006019841000005500341003c1e034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 335198192 1250 335196942 335196989
    0xf0e0a0b090601050102030d110d0f0912031104090e010209030703030f020d020304061e02070b03090a02190602070302130e060c1908070e040c050d0c0519090506030c0705010b030f0106 81
    0x2d42c125030301a00918a0305c141c0400e280300802021501010441040c0a00b4449040c60b1244840e4035030743e840009100100360a0403c1c0394003200034481c041604041a01400c2d9030310400381d5045901c903800c08680b42040308076041c00390150303204094261142490000074076500403200000004079400f5120900000d0074200d840c0c0c4128000d41c1c1c08210400841e5004044019544410031001e1040c1c3d019a070700d071142c507041c60f8010794079040c4684c44000071600758a0400740040c036607100f07111a400d01510713008000c1d44030b00329448080d2140703400780d14042d40303108160802e0001c0c1803c0010703101207252840307000802e50080741460f6000c4c1d170515074a40b6090300901d00a802681075031101042d0a081c0c1d0200070141a00d00e403d242004028484200104038901501040c4151a02c1d02d0762500d0300340058841e1402d030714a02108200303108200300101d03162002102d800150b03e03001c0e40d0b03070f541c15030500a01400442c1c0100d1742621500e21040e280040c10750180099810600800f2400d555a1980 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 335199442 1250 335198192 335198203
    0x6080402030316080c011401090b0f030c090c0d020a050d112701120f020a02010b010504060f050306120d023306040e15040503092704060f0f0e0a0b09 66
    0x7500350b07000304610805605000d0300028058071501420785043c0600301c2082c00e41c1ca80b41d081020101e0000c0060010800340d00401c40500340c15101503076504440c800080c1c3e00d004692202e40540c112501140340c00d1059405c540450b442601d043d0f584400151005044d0350141503402030a6180c0010384010104200840340e214081c00400041601740113003041d2411140c69071103041c4400280401d260214a00a825615001210050311100000f001a0944100c50701e46810414100414080e00703812000320f0007801c01910740385843c2c1e030341c1501096000d60741181c042c40b10722496001051160340010b4880224500301003500c090001500c240400d58245040b62080546d41d50014090703050562043d4240701007001200d0b50030301c100c850801490010f40d41520180c0000071a0103883c01c020307510942402e900c04101e25801100304205543d810054001024680c0b1f400084e404101d550304180c800409046040240c0e059900d81c40c1d503101064201141c000d109032000581440c0003140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 335200692 1250 335199442 335199451
    0x2070801050114030d030e0322050a05030102040602071e090e250f06120219080106030c091202060c070503030a170c030708040f060e0d031a040c0f0f0215040614010608 74
    0x14000842c17240c0301070700034051040300c0c02004d20050101c48403c1c20190000c1d04804003c1c1c00131180b0318203100500c010b220050300001c3c02680100010802a41d001a80344215100c0c03402103400d0030700003442c19110074040e0f48544005420141c081c0a12440031696610651144108801e01e41c054800c2c08102c2c5228071900123034100035082005100d0140100c1e04460000c2e0b48010702c2e00005080f00e03402c001300191100001040a0014020f042c0c061040c50f41d001e49034200100c40d24904407813060341401c40e2034024054023012440c01d141e20801c000340b00151500030f050702d490342c0c0c0070b80c0700400610501305401110340020010916100b01d0900b140d0042c8001e5070f4110103a0b85640340c4440d001400b91085542e00d550305070840c45000140703c0205c80049980d00441d091740c1e148001404542c24544061080345040301c50f405003038000482098003c11410480e1810705500826400c105610a92401100c1401c00700010080719912056103a66041811019a41c0300e02040b01c070503101700e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 335201942 1250 335200692 335200699
    0x170d0c0903050705060f120103030302190813021507061119030e0d05030408070f030201021b2d010b0a0b090a0803040b03010b031308070311011d251502070801050114 73
    0x9020711a41c10004001c0400d501e0720746e05249007180356a201c03581c40e04260b1059001960214044108440840c55070041e44034518010060b4242601840b00d072808070b00c1c1c000d03c00c2655800400542403600251f43e0110b800181c00c001c244e0010710780800343d07805080d1244c042121009c6000d9224001d21802001103601c0f8024590880464819545648090000d44881c0800c8c400030000a01e944101741520388030fa800540c40d01c007902d001d031105403180d641c90040b54126030b4044165070304c0c91020be11030514248030b04107014071000c0124014800340700c1c4240c110683c4107010480003024402042c03184420341d0002256075903003200d03c1c4c490095003e4202c4040701000104603800c440c0c000b4682010080c80d440701040960b9959044540c800d40044020407003644611000c0d050071710502620300d00c1007400c117002285404000d0b860302000074090410302003030f080e0454140c072100014409043c07079110242a03423200101c06980e40c0010300c90f88290b5030801d00003040c0700e00c0d007540c00c2850f041e015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 335203192 1250 335201942 335201953
    0x706050f0d020d09081908060a05100e1c0803090f06070c060905030d050a0b09010b04140607062705070b0a0c11011206090209120604020904140703170d0c090305 71
    0x82a981020f94407203658102040d45508014010521040041c40642d480349154400010b48600191048074001c2c4202d03c290300c101020055500c400f081c80690f080146040f00400d00d1b1080095180c000c0500c0e1044010811980901000340400c007c1d40500d40b4841101c04100716418030980c1c400741116200006108074a0000c000384480d004600e10034070400030b590a24141301c090f1000c43d0821210401e0843d207600d45881a414801040c6015240441c01b030380c078003802c0c0700d0040e00446020101c107001e00000510103081c49410390001c03142d002c01810012144040382007141940c0c01240c0d040c1c4880c040c424000400411040449813499084d4072580c20b481150b40740c0725103100504420b541030041e00c98044075041802d11424002d410b00c0c081c01611903806200340405001190a150340e960322007000d002c0542e80305010182c0c080c2d484225000b4440c2d221510394246402d40d4002002c03030100b056450000d18003000505245005450304220700d0024800803980c0e00d0b43d610005c5c0a58000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 335204442 1250 335203192 335203207
    0x81603030f05040c0b0c03120f15010207260a081206010f0201090b040201030c1e02010f0b060319090201110a0b0a0b06090907050309010b0d0501060e0714030a0518030a080106020706050f 82
    0x3078001b40564200c078509990400994000703504503084101c80ca015500b10f60410405281141e603000781c40090203100034044c076810480c3d0381c109c050f151074404550030b14030900f903030400c0c0c800c105841c20a0780c071812064482407540744441080750241d03074a0340410452209840c00030701c140710b80200d42da00000804d40d41d45658005400409241c07075450104065001c44903490440d83c0041034042c8807907800024030322032640300398003100ca4201c501c40c8914420424400583c440098642010800d0800010702d002248016240141e440000d000b0074041c0130302250074080650191340c0314450742141807210517440000c1001c50f10500401d039034000c0d0080041181c4070b20980185500100d1130f000081d40c000044001529020410030481310380c0c2d100c0e4403c3c0105803220801a420180c18108454001c01060310200180402058249443c0e070301c0002a81d109a101810720070010170105880d40c80c45505002040c600090041601501c5420800a043c0c1d1082085072001c0e403031021034500307103e003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 335205692 1250 335204442 335204459
    0x4290a051302090906010608150607081b07060c020a0f0605030a0c410412080f0708030a0b0111190209060312120a0609110313020d081603030f05040c 66
    0x1000740c5445030032603481d6400c00040c0c807490009400750340c2c6080103144640c5008001002a00010441d100c50002070001200e142c460340c0a0b541441c2d80490403507100c030034080c505580032210028200d0300380b0800070300252141d0014000b04465000f0b171142c0850036165081080007182c9403240c09d0024608100241000701140d000f10512120b0b49481c141c00c00545014508910345070811a88074561000505c2c2960346d40e0720101c0041d400200d006080c01c0c9410a144100103140707201600082c40000c2c03001c0c40900308422075444a50100c00e46071282003032451080200240d820080c0030a03515001c050031140009004201e4000000000b420b0609a9081c00304900c00609566054030600d0303655218842c442c4041c10b29100810f841c000c5600e8980c00361030a0710010b5002d8001d4526014482c1c4462103050108c0741e002c0040b80743e08240442c207201088650f4511a006800740b2000f06000c004241d01c8500644014003e03039081c0001d18010307640c0421285c0680d402080028401d804110119 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 335206942 1250 335205692 335205701
    0x6290309010608030315030c0d0503030103030507110d060204050102010e0105010b0d02092b020a14010212030606160305030601030f140708040302030708040f0509010b0c060a15170604290a 83
    0x4031190021a52a94a035942480c642040da180c5200000b8510451024101040107421541c0101c0703800350f200c840398590703648911040c00007400f0404001050414080307a40c01554401d600070741880091601030400c10001d400c140100ca005500b005003401c0703501414000c0c1c905844403103000c2440c050b1000c807024020b52015102e290050a800190f00c440404070404a54480c0d03114030a44615209104103d006286074208100000b0031207212344075a41d00041c00388a40c400c03015003550341e40329100090101e0054501180c003040f200c0d40d1003010940e004c0003a50003500c0a8a00b44081c501c0000040c095400c44490000e07400c8100c40045d900500c554a6650420300a00640f464142c1c5911000300303a40c000c2d00415102c1c94542e00c10001414200f08050050000702c9541d030403c00d01c10b01c10303500d031040a007811207130503192440c0a80f00e9000e8541c800041c020401c00d0802684041846511200308603030980708003c0c580c80c1403c0e92030403070144d6800034441d20360a0480360f039180da84c3d03001007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 335208192 1250 335206942 335206951
    0xb010e060d0609020301030b090f030307050901200613140a1a04021912110108240f2e0e011b0c030b070206040209060a050f150d02040f09062903 64
    0x1c0c0c0c4402d40060284050301c000e6001e54082c5100d85031303d14002c0650340c0303040c9030350384415000d5108008101c17a80d0351140603a54021824030706408150220505030700c01c02e148605141c0381d07000392010700c11201115010381084d14841e03840c103001c0c120000461603c0b45c0404901510307120412020340c007480c0007026081da03c00c2c4010304070200c80300a106149070f41c4000303800007040301c02c000c4484028010041030445100e0401d1070300341c425103040c0c0f110b007801480310000031000b001c58005042d969643c460020100a0018041d00342d4050741c9500240e40c80103900080020704c500d101244002885201c0c410744080068480844803c901d2000058091101100f035070740041d035000200001b07120720302d85406451240d0061000381003500401c203803000007400080c490005080d08000750b0f21ba0050648425400700c900e400c043c8984803110401c1d2141c65281e000e641d200050125000d000b4078149415200f4203c41003240540740c81c0d001003640c140500740c0c45d0b49068201c1c1c0303440d500030710b9004642c071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 335209442 1250 335208192 335208217
    0x715050f1308071203080609012102150307030207060501050f01090e10081203010501021506091302030a1401150626070e180105011b0803060d02011e0203090406090b010e06 76
    0x11030b54604909041001982100d4500c0040300c8a04051680c4a4406604a0012140680f15514240040c0300c5c10305140100d4043c0d2443c0c2d0804425541e80110927610521090315031070f0790f80b40801c0020000e6000007c01c075001131802001088504100490452060042e1101032083e400e0041014415100a19140700c5218145020501203428420284081c46001131240c41e54108000a030819034030401214018403001e0030020590384400d5855041201c1084d0300c0c4240190b0700120782080389a44000e061591a049040503e02055011500e00084c043e0391007011a2030342c0080307400d2000714441c0d410f02c0340e040700f11010349034080442036013000450420321446248007000c503003a0240410700542c4500c44000401031541c00100d1000940120303003130641c1c00e95495507003401ca400302030501c03030041220301e082c2811640036080c590564032890f44502c60314000d000d4000c0d41c90b8800b0b0b00490046060820004420015028401036054141c4504035030300b070290188000d03600460941e510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 335210692 1250 335209442 335209477
    0xa02060304032a05160b0a20010b0909060402040b0d0507091503050a0b06040e010902030703110402090a09020a031802100e210a0519080414190b0c0715050f 69
    0x207503010784a40702d5180e501c500040c19000e4030560300c031180e44c0030642c40305100321b800b00101540726502070060940302e40f01070261551358802c6030156004010720002560402c1c9070400f8000e1846c0c0018076a40300d14400c650a10081500c90244062404900d000400c40da1100c101072100b084079400c44586101e4290f0801c1d80266240c172610b00d032101509007034807441043c03003e00420b03003850300610a00f0440c43d4000d00410a00c1c0c0e0101e0b0359a441271002920a100d03900700302c43c044c0c0d10f50301101c3c10158001c01d0307403180710b80b01c00e0360704000d51059410802203858002d0000d40d110032403110244003134005141155174869110152118030314600410f0380704600c0a00700500c050390302030640c0d02d0720000d03005148801041ca007451800c45500340d02422000d0b031062150018403c20201c400b0350710700344206400c2140f888041110b000b840d200200300001180408101c91300801d01030014610400110703088560398080350700c1083c9042441c8800610200310300c00e00b507802000181406d502e043d81e890b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 335211942 1250 335210692 335210747
    0x10030f0b1506070303020c0105011a0d0b040b042d060b0909070e04290904081c060b27090106020c04091b0f0e0c04140d030c050105041103010c020a0206030403 70
    0x40b56644503070800c8003c41d134041200c00c4d0600c42480313500e024120a0b0364610b401c4a14030841c01040c05900c8249090340c2d20341c121030301552180d030071405400d9400f60050102d02d011010520150b4503da50900760031102c10400070380702440c0d020300300490740984810351401c50100244100e5039801401882070008418040a45840b41d1107120061082104100d1501d01e000380b140c42081007401000d4811203110f402e020119084c1012600c40240c541c1c4002941c54060309280d02070807090784019800d200118108104411442060601d0a01410305100c0b8041003000c0191031103080c001d45005038002c0002210b28203007940680001c0c4d001c0c1c60343d00e8104055040b08424802c140d0000203448150403400c000c42c41c110003145070010b880c1d07180c603420203040090b088070060000e0440c0d0b03c00c1561001e480203060244031261500c0d50010000d00245c034250505080c1c2e100c1044007603002e0745c40c2c0030180941520101d055a06554003c0415165480700c0c1c07800ca0b42c00d148240801c0f02c41c10a0100726 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 335213192 1250 335211942 335211949
    0x1202160210030b1f030609090c06030c09030b0703201804021e0309030901021e0a08090a030b070306030c0911030c03150621060a0b0d24170610030f0b15 67
    0x1d0301c241d40040300d0130b80c3c440e10020040c141e603e01e60240c032016051a40e0080059104225001a00c155150028078080103103021a8240b402d03034005403811003004180080c0725410f41104804000c03a000b440d402e06000c030b102951522030605131840041150041900a141a80040c4080380d44080603041a04902d1401d0515510582c2c2c681c00ca0780c00042c1074401941c06200c00341151441c60352403074070034800307030001600c410034603000400e2120005a850200d98a6880e0080910742040e0f0400007840c00306030150041c1307400c0c001941c0030703032001030005441003e900035041a00b40954826046490300e1646080982020b8148841548241c0c61130b00f0303580307940018050b8a624200c0d038207002c00c0074403400c260304e500103010103000c0c00210f0703c244500440c0c40100c0e2001009080b000a000994090302c9507602c0a898844c005a080c6060004600382e0310309442d030401840c0825681c542d15522032407142c50f20f50b40300c010a0319804d04620030101d08070300301c0760341d109001443c00d500b000c40ca58000f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 335214442 1250 335213192 335213209
    0x131b08030c010506030c120703080a030f021b0708030c03040902070c0308070507140303120c0703021c0e04050108060730020a051218061503010b030706020a031202160210030b 77
    0xa480c1e55903c1042164075040001c02207820041c0c4a08621008010103d80c0780c1c00b250001030098800010000d81541c826030081c00f00300c001000c00c54450442040ca04012650340b140020740e071240c4d0740701041d1550007000f194852401400210700e001c0c90140a000650400d51056641d030440c081c000004c01d403584000e0007100e12840140c14650f080c0405c09880007003040e5800d029510500400d0001c074510b0b41c2558004090620782503c030351035454100e280c005040e020070031510080c0c40d00116250401e1483c0c6002508950500c456a00d03075400c251b40e144212070040015141107003c2c280c3d0150b40c1c104440901d1000d800512895120500a0507039125140b000000b41c40018035140407207010103001c0c0c02110901c440105580241c207460380c0c1e400b02410043d03841d81500411030441d03809501201400030060251120140d0724035010303480d1480340d502503012520001d2748528001003482200c01e22072003801c50b0040b00c00142c0038032030b040f00585c4240003030581e03c04880c090b5980d2401ca = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 335215692 1250 335214442 335214457
    0xc050c0a06181707030201120b1806030c18152e170601090509101211010206010f12060c0509030604110a0906030206072018100e131b0803 61
    0x3681c800d004100700041c61040c00035402a803e680c2125042c401c2c0702070215006007100e070240303000850360043e0391018000708411385115511181d081590601c45a41c540144d1054004030191075030f07a58942d041c400200400320894420001c0e030f4001074003041a0000039016040b000c1c040740341c400c0300c8400416040a8462000e50303001050708200340c0d0f0a610140d105502904042c04003041c6c1030031000600002c0450142d03e01c00c8800c03400069400c002515010000c0110088126002000d400e006002c291100c4015005004070000460300c1448045420101d44005c001402c01c00c2c40c6865100007131a0100c42542002002c02490202b42e40412810303024134082e4115000703818059040000b40381d02684540101810548100f000d80e5504040d2100c054114401c480105c0b4040201c88200740c2d511503a652086d41c040c00c502064106107800e0784240c0e5091385042c800d41e15860000e2920008480315840001d641c01d4002c0001c04404142d0006850b50303d04016941d2902141804c0d50000710 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 335216942 1250 335215692 335215697
    0x180a06030608062401080703150906140d0506180c09040b07020105100602030901270f030c0b07150b040608030316020c0d02030c01080c04031e0b180d0c050c0a06 71
    0x4040c4107450003800002d820080e5461080d04622000c00504c102d01e10038112a41804500c0000544290094011521100a010104150f00c0e2503104c0307030004002c0744c0150720303144807481a245c281d414000c0207891000e4205000780750b9544c0d0713045601410f8050b010111100d001e40c64000c90540ca48070303c0240074522a207030200c00391038801d200a003181c6005003181c52002011804100d02e41d00481210b00d00702007882c0100c0b0070040c644400800001c1d0358918200806203410015145005420800a0302e2082e135049410660303c0c0304203007040c0206030b03001e4030b0200105181507a580280c0d0203a819100302074800710348256103440d01401c40e00129332040030070a000c018100c1e5139506001c510300f00b8001b1a0802000303070054000c01d6030381d015203000d50305000043c004136680c0303045903050310015548a05242c03403c2d56588281140c21307030741900840d1502c1801010450780c0c603992400100c4051204000c0c9030b80c03002d0300822521803134120390039242401200002a20760326190340b003202505964 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 335218192 1250 335216942 335216951
    0xe011505060708032205151e0f130501091a06100309020907080603010902030a05010b0a0801060b030a2a0306050f0306130206090a030807060c0816210e16260c0402180a0603 76
    0x301c103242e04110380c0c41ea41621510042c8c08200d1130320041c8000c9034121810300c3c460421074600e45880d07401028042009805140c0c862101846401940c8410344161f80584d2114003038203104900b41d0542d8407100e4003d40c41151800018911841140000c0d4401c0c001000454140a246c02007070a0941e030042c03e9405944415042d019401c002080c1c10080188100030050b441c90002c0072030060001074120750905454101900482c820013040700a0302c0a030741011010b10203c110302500401c0380713108060241b40c915514040500d000318840d44117108004c0c0f002c003138017626070811440340d0002c0e24540c2d00242c40030010001c00c000c0009031500c070303100700000901d46034804800b070541c40f0000c00584892030b140240d040c08541c450313107640c000b0300d40c014080044407011a00d0000b03446040702800e000c0c407611107500140c0c2e8200b090001100c100c60162541d1415076600002c04004081004e0043e0740304100400c1c0a00746a40100403900c103104641c03441d00e81050004511004603409800003984070f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 335219442 1250 335218192 335218201
    0xb090a02040b060a12050705041d090601150206041115040306021c020406320f18010306050a1e0f031406062b020f040e01150506070803220515 63
    0x28070510008400c2121828184400024001c16074402140b42501080e120804100500c2c05201034800ae010031000440f060f2880e960600008802100c1d1800140302c0c800c000500010060600041001c00354043c00c038a075260f46511030300e0040280019005800d10111031241240c00c1c025002542c803174280540d403039626850b0600e840302940b0b15001c0580c41040104811600507101c0c6100d80c600a117011991102da06620107400d2503000e49580407500051042080340311036004044104003184041841401c0030011000c60702c0b280505078014409090030f20505030b003c6001d070494115a050060100c1e12188410081c07050742e0300840f81007111140c8444009001d00080c1c1d84800103a4515402c0744c076001c49101c00440c1d9407080300c0c81d5007640080d0f20954403440040030b40410085d00c14130420b2071100c0350500901503071142c190494044200810b4616160045070341c02c9400c44003d0b41141c5504841c3c02958446010001d1031510407040c00000820601c01142c100b1460003207030070103142 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 335220692 1250 335219442 335219449
    0x240504020d0330021b0712020d050a120507020319110607140102160b090a17090f0d03021e07031505191401090c0e030706140c2515091206090b090a02 66
    0xa5950307440074190406d140900c1240301c89001c3d0441580c0440c1c9061000805080a504004051a02410310b03420b0305001e64115401030000c0507014420b81c115201a04550b072500d2240038640030040c8241d1045070000050703d0b0000141c5201800341340c024200841c4664450f0883e802040c2400c0403400c10740b02c00d414417001c1c5540700d50025181020780f00080307160782c50001108044099118009002c07948100070b403581c400e80e5065001c040c01c442c0f00c10f0380900b0069580e00606400240c00b0000d1600c004c02000c0100da10400c0301c0d480300c072130800364a0706240203001e041c000780705540391550351049140c481c2d528001c180341001041542c41542d414001c100d03060356030044615040c8240d4051484072600c002036100100c413442e2a108220103444611030400744194040c050313003481149542040c035801554241c40903c84201031412050b540d03540d407000080d03021103100100340b03844010082a4901c0c1c80e8400014810940003602401c01e60ba0440250000d8a03481050382c00103405904504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 335221942 1250 335220692 335220727
    0x140406150504480c06091217060406060507200303070813050405040f060b03030d090804050307140102030a0309170d0b0a0603020915070609020d240504020d033002 72
    0x90520201c80b03101095020f4000004a00c0c1d55103104018900e03440c6003c1c080540d00420009034890401c041d500d291280051150000005481401980038007184681ca040e20030502140c0090700d0315818810641c5072105444410750807060f00f1140481401820340c0c00b40001c0843c140301d041341646901d0100700301c02c0246d902c0d810407805907141c601404003040d074050b0560003040d808200405c2c0076240d03c020a0850040350f0014a5080c00c15584000f000f000f00042c000340d4100b90211841159514540c03620003500d0314410b0b0260b0020054801498425007003101c071180511124a04210000d20064690380305004c07181400d6901c402101c441e2501071081d074003c00e418034055080c420700300005500c0c158140c41054003190b000903040104015500000c0c40d442c1c0050030f101e240030391400c00203240d60b103104201c980740d07425411035640e0a03828400c5500494002d45401504201580c040c2c40105001d40070482d4890410120301c400c03602101510ba500003024409612031000e039020306a0740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 335223192 1250 335221942 335222021
    0x130e240102120d020d06230906040b15030702011e0f0e1c051308030d020c070b04030b0a110c010509070f0b0c0c04021303050601031212140406150504 66
    0x54104140002e44050707100309445101e00010001650340604a03c0d4000400c0150701c10850110b50b0301c3e101000700c1c03a14954880420054410030040d030b17641800c10080350700041c00d20368455002c2c010903540155078006590f2044050000140c5904a04d0245102c0c113160600c00c2c0c80f13541c440403003800300701c02d41c00317015540961f802c01828100b11078400544c00303404500456041080120740698000300030b164150041820005a903540c1d11581890030281d4031032070810700244503001c03000441d0481202114104c0340c000c61003c4c0181c03140c0c8407481c044c1290310708008403c1e03c1030189002900080c450035008640d14001001c116240c8a030003546c01a00d0b030b0110349206c00500012440741804110703102d00b25402c0b0760050391420009180155441030342c2014000d4883c2d1000403040101205007210351072960303114120300300c0c03882c0640f40c11781740c82c10110b0f002d02055101050004a0903040b50080a031407212030341d51540c803000414221005c0035600c20f0f0445010703490f240a20003100208001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 335224442 1250 335223192 335223197
    0xf09060801020c0c0105030703151d0c191409060c0109061a09010e0403140708030109050c0a0c020121141b0307020a08030406140c03040c050105040f0b130e2401 71
    0x401c3d0149030302d10380341c40d607688409062000000003c0d4038148203a000c000c04018181c0710048a503156925060301942e0000c1e1402c240c00104049038965031984160780c007a800c1810040c00381482489c0489a009500f802c40c03c1012090021071400d0791024050a589070000d000041c16443d1410104180d07142c03016914030b10850380b030b40c594064682105079819540200390502075515035260850341c210007024a51511280414000c0070020301000560403590454014041500c0315612088580b140c10700303440c04150812054801940514003428002d500c09290f00c01422419110900380c5154202e83c0c101e101000041003c08143c4c46d940441c4080080c40c150700703628080d28060355078180210041c10403540800003900304583c98001c102c441010800c2203146081486c0880416042034030112405088400082215482042a181110503210700c00c90b185290141d4502c00d580001a00c0d2100d601d90400800c0305100c0721101809580d0340004202010349082c0504000e80f540071200c0d04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 335225692 1250 335224442 335224447
    0x102060c031308160501111803030310061206030501060b04032d0323070303060e07020604170711100f11070b0d050c070506010f090c0e0d080c070f0f0906080102 71
    0x20700490400340c40580981c80f040d915981d038801550310203509800c41000785151f081c44000404440c02002030245100300100ba480101002070405449000490301030040c8440d031001003040382e100d0403104114a601302d0300001c0301512510340c10300390b581e150041c00e00200005001c0080120440c003c819049404941c03c85100d00c402904050803040c08000c2c0c1003011034001100c203404600c150740721814007018659a503901e181740160242465214012440c074020000455482c0081010703841194088210751042d00c0d0700e001100d298200720800d9070002070100d600c407107035154000709060740255030b241c80104d4002540010702910100800c1c2c8155085003600b0481855540c06440d07151002c00804540c5907184031800e9081e0003840c80c064994400c42000040c00300040b4104130a484001c0b40c280480d0510707200540b03503809560b03a40340e0000e55202d419408200c0200141c0b2900c0c072664182d42e48641d03207149005051030190443d40082511040400001c07405128400003011220003d50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 335226942 1250 335225692 335225701
    0xf0c0803031f12080a120203040c060906020105070206071d0a0905270a020609120307150c0e0117040309030506090f1e190c050a080309120c1c03120c020c0102060c03 73
    0x80f164443c02c0c00090100310302040309528240201144811a072020341d007191203103400c0c10051441d82c4140319000118000c860086021481070013001d1080001c0d400a00b01501c580f501280c0600c00c03030b140c040c213108504500009a03601d804d00b14004081c03580c0045154206295100001da03081c4207250740f10800314071800b500740808248002c40a07011035101e134543c44400003003001c28180700a01c05081c000007807404200b10450058000f0600704000801c00410b401c4030998000c8181c1e039845021501144681d50b0350003800301032540c460302c60301c2c0040c801603607075480c0c0f85481020386044070150442c030410a0110303030800450300c01640000404034000005c8074145d03103d8654542c80302100b4441e03d0b0030424840c000c401d41d00201005459400400c0d0303548403d5849800c42d14a0318402d608409903407042c42e000042904040000030807401e105134040c91140d454078010f1000307e09100380c0b800d48040e0440a0b1060391060040d5802800c51a55114002070401200405888903c0d04c02d10901 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 335228192 1250 335226942 335226959
    0x10807050603060d06240e04050610050a09110d050405060106022406040509120f0a0909050106050f0a0c1205210f070f022505100c02010e04090f0c0803031f 69
    0x1001c1503405c1100090076400c10440401003191181c1880100c55100100255048001c100305102e00d002e5010340c0c005884070740100824500c24400c495000000c500d0a0040d04401e0307000c80390b20003030204014580305207985000165a0210780550700da07080701004008003a010f014a11075180c0380c05d6507901c180d2811200e0100b602000d40561300031651130000400101c030402c0300c00644144888110b03120350300021503848641c040c4131104000b41c1e00081c0061824551300a00307050798082e44a40c0c1c2410080082820190808107004d010400c0f4080c014000c11143c1440e07160b0500729a03511985e994400000310280340c140341d400b44030301e0b41040c10019092542c1d010540c0121451030400f0414a00200032841d0421404d52400e41c075405000b0344861480861302c031401c403201a0b0380700c1520351150700f0640c0c000303429002c00b9001c41d003681103800c01c1d440c01da4840c0034924407900250300c81c20603d45805804913425007041c0e0450b80000288200c030041c03519811503890002c4812200103081c48141c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 335229442 1250 335228192 335228209
    0xa05070c090c11010c0807031a0301090c1a07051b15040e010303170702070302060d092420030a050a0204170c03010b0a0311040c02120a020d090506270103020f07050601080705060306 80
    0xb43c404055a400311096420001c94800030f9274000100284500798050a00c8150b01000e4400d14a9080b00150220064003c50742134410240e04040030741081c0b0840c103060300800b40c0c031602241c1d0028680b0f001481003d001d4002e400603007a801010b17030503036040d03260241c402201e501d185a0032024031030401241d581d0010f40ca9055a07419107509894030000d14504001d040901401000040950507040c0c000d4440300f050014486118400c2c0880c036a010f4108400040000a07000c116104000249207c0c4a03500f01c140c0096005500525141d03454404200000400b6030040d010f82280d0407890161409000b4031409100443c1c0c1d02014502e942e9808800700e807404856030140d51520460615030340288078410707012070341011240d952969800025102d4a800c1190800316820344808109400d040341541c601041402e00400e40c05051401d01c42c005040405450416400300294004c008681c400385c1401c0d8852001025207504010400e410500141c00043c022a81802000020703a6245003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 335230692 1250 335229442 335229451
    0x7090902031b1e13020703030e060a060806010b0c030d060b181215040602090312070620030103020d050a17040e090d08070503040c0e0403051b0106050a0504020a05070c090c11010c08 80
    0x3240303550003407110049510100c5107612070a40300c2c408505c0c0c06c14580c00d600103200c19501c00003600c1c41543d4108222040310410302a8600907444032005200042010005180981240040b01d00f0442030410000a4840701d03001221051000719481d5050868942c0007800d91008550600c2c0c2c80f000017200c2541c0c1c400104042d40522070f10404241400b11030b80c1107452080c1d014083d02e54102518a54815075803021b8000c076095890b14007080000c0e4441000d51201e4088070505501d0b59186408102e0300700c40d829030944480c0541240e0b40e0006541a49601e29032500f0b00c0f9940e1502d2902c44405401d0788010320140e10b54200c1424101c019510003482039000005e400c0c015265217550401440f00c0220340c02c07940c40007801d04207010601d60491701402010b482c02206140801c200c6032028240c1351148035040d0000c50741e4005100c14502a009407000d02ea4914010741007101c1c80e1598035881e1056400190900d075500c4100311030a5104184072103c8440c58002e1140c1a1010300040c100c000081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 335231942 1250 335230692 335230729
    0xe0c0f03030a0c0305091c1703091c020102120106030510050109180504140604030e2806050f120411031501030b0f0402040605180105011e080406020a0203040807090902031b 76
    0x140c41c0013054003860a80302c445e04064801002c801c0e05c01204500c01480c06425174034050700400c4030300031100d098216485203041002400004280340329410200102245603001d5540a000071340242c5545101e15000b041d4980d00410340e801d20320000caa8000751604139a0401030390140c14030440b000c1c2a5401484c00700780000285580c0c5509005501506240a20030180600070a2000b07160344006440c00d058001c6841c114114400d9000c05510110400c4001842114074010000703140604050052401e24580b0349113807208401400d8101c11088500311144034a41e9446502820100040c101c000c030155110758070b9506580f224032041d0380040000d0001080d0500140440d100e42e00580010b24014240720000a19044803046503402400741500241162001c442061002012704228032a15218054503848a0703c805001c2e621208500080d4441008005020802001240001c000091002483d0030651041504104180080485485840340e0a02442e0340700c82520041c500c465 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 335233192 1250 335231942 335231957
    0x10201060b03060f04110301090f14010303080f04050c03070609031214071403092e0212070201030e070b03010b040815070504050108100302131505030303090c010f050d06090e0c0f03030a 82
    0x139000a01030f0a403599a1415500c3c007100009680441d0742041314082d02c566070501002c00d20207800402c00e43c0911016000030070041c04101d00b82d01460b0440e42003030040f410b5464078640440880d141c505d4540c44400000c82840040081c0450f07540541c041011a10344044500d012441120040c0a2003030064846a2140480fa00740380e000c20450b01b2445028125a10051841a8040025010b0b40070030030b000741c401480381100c902c0803030411144800703040d0482c1406800e4004400030031110343c1c004410310072100d01040140658001e90b00819a45900c641d0351810000c005090214030b0b10040c80d00580881800000f5070000c05a4003500e0080c80c20389165560349081e803080b150700d503002940191422281e560f0340003c0d41c002c00e20004000507501240c5a40368241545d85c4011109000c16030001040210158810f15002508107010b11f800e50418150180910031115207520500c2c000b5551031841c860088140b06c4110344000481d001d42d000c01c0c0c02004242c90b44250f039101c40401464 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 335234442 1250 335233192 335233219
    0x15210f2502070f060903020102010b0d12140d06030506160908060105100318060e0c030a020f090c04030605130209010501080402180a09050106080303071407050c0d021807030c0e010201060b0306 85
    0x300200c10081915a6000f0401c1c0c2e41e41802901900060006a0042d400d005610390107040100001c1c5159601a1034000744980e11042198900301c103521039000c40c2001c00201119070f01030702401c1c7c0514051405442542030440c0e644070310082d0103402100b0300042c0102040390755000314880e41115415103061584e540240d10480c010041c0b400000c003822400a08403007886080d610169800c83c060080718110036407101015030301e004101000f540300100b1813a201c0e01d800c161201c1034000d110104903074106074495943c0e8041d90030844500c5160341c200040d041c254500300640d1401800301303081241c024282600426041c2440d070400c0020410f010021400000080d070091000c20b8000000f00401034075a01001c4e02c1c1d500036190500014034180c207542c02d80300d50008980b003047d0b10100030148103852400b80540d104040c542a030744044200c0d080c5a9400c4a41015441280d40d60380c001a000610000500000c210340e07451811a8504642407080040d100c044076000441103900940341940d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 335235692 1250 335234442 335234447
    0x708070b09040f1b11070e0103140c090a0b0906090c090f01020f030f0304061401050604090e1204140411090109060305090c04021c0b0d02130b15210f25 67
    0x540f800d005040f49401e00c6410340c0c50820388035140c151059603076540b000b425101202d94541c01070044015801c1200010000640102c03c1c107500140d186098401071450400050000030048881350b10301034032407171005241e02c2c1159010b5070210301214080080e00700ac0c00484024011003040f18050718448540f5030442e0700800640d0300603400701040b00da40e14100c24081001e80c0050703030102d40c800e0402521100107940a021141a10340150a080c100351800503100050404184004418000e50403018011801400148040d04000c2d6100c0c032441d10070800d00c0216180000c08110a0a081c003500030541e0740921304c88202c454514010a294075800e40c010304180b05840074941c0584002548101489448c0c2000d44240342c890040010449501c280300b20100b440200941c001e88400ca1644104015400f8903400140540078840c1c0c40c4c445c1d0008005903000b140010b0310000320404045004041d9100303298441c03240031546401d42841000d50012003251062484004540300f444c010192 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 335236942 1250 335235692 335235701
    0x4050a0503030910050105030f0606090c13090c0e090606031609050607210c0f080a050c1506040c0e0609060f0c0706080414010519151d070305090708070b0904 70
    0x6030404166075407410b140c0111039540078075180d1500802d00b0180005450318002c681000400d40d890044c00090b80e441e4108403076101d00415601d1408000c0c0f00441002e103030b03c400c80c40945038a0b0800100021031040c040c010440311090346106103020f004016183e242c20b015a40c1200348000c148204150031681564070a00b603801c010f412620101d40f0303500740030501308501e40001890264182e000d01c5603204950321005042c002c1e10196044510b403002078158801020b5403910342c0783c12410310040c46e041a0826540e0785200d80c0d6002240300384000c52030288502441c810392801c003c010f0382c000d80d0200341c2d140140b140c010702c02c43d0b021448020700c0030104100c0703060040c1e8005846200b600d07401e010703120740310548003a00d08450205100300c460344e0500c2600e00a02000c2000c0301407801c00d140d0500034256284404060084103c000581540220024440500c048036008002d180c020300c004c04030740005000e103250307a0292400b0484100c000c1110010380d56102c41103607484069034003140142 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 335238192 1250 335236942 335236963
    0x9090c0e13020304060e0a08090616050f0f010b010e0102070e060f0a0b0a080c18040b0109080703051f0c090320060423010f0e01111c21061d0405 64
    0x46002100d06030001c08550086204034801da20030030030049901d041950703400303044000402000d010451001140780205c044d041c40501c10307003141d454403881d5480c0c5040045944d120080c0740e11604103608046028050501e14400a10f8402502040040000c0da0740100d031140b00d540e076200d0b0000c21580e8907980842c4074550b0000d0040104141e0303409800042e907002e40e100e140000c8101c00401c42c00185034040301c0740442500303042c074200032a010800004010440107103040c003520303040c00102480107005000045008002504a0300c58601c80d41c8460020340c40440880351801e6000030b0840c0d008034180c0c041d07a0300312092603d0522102240b41c5a0085942803540c0450007240003c0c0103206400b95222040744001d58080d6000520019103141c2030368280c1c2e02c0450036085000e402c1d03500c503640c10000d05801000322100c81d81402d070a4403494008854a1000404e40c2c454401542c0d01460380d540d40d003442d0780041050518106922110181e03011300304103580e005c00082414070004000c0034092 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 335239442 1250 335238192 335238199
    0xa0f080705040e09101503050705041404150617070305071d18010b061903141510031b090305191a07201e03070c15110d0210050c0a09090c0e 62
    0x1490921890006d050300740e200899207482110b8010510307003424066105054000c0d8080d0045448540d502803811680d01d100070b000950303c8000180c88029501c0d2144e007030884a002c0d010381e41c11030500a081c000d07950051b5080111031048041c0c084910300350325a00c0800b03207445241c0d454000040902400d2a20380c25075000c4804541201038003601c0f0100d10801131561800c1004500e60144122842000c44800e101208d40c450916581d0030400780320041c00c525842c001800903810405c50134202e01e44c00008000411040b414802c11804026203000e28401d2041040c1d440c0391036580c0d040280e00545026010124800800d0301b1074040e07aa81c1c0544105406501d606c0c5e5410111303281d440711030210034a400001000c0e10300040c4404021144110340003041381d078005041420981035520301900307000400000c1d020440300c0ca4010b224000003200198080c00002c0c110f000001c0c16503102502e0300da6000800c12076440740340c0d00030048004480c000c0d1008243c0b5541c8000aa404510110709a40c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 335240692 1250 335239442 335239451
    0x70804020307081005010f062c130e03070b0903070f020d030e1815010504050310051b07030206040302060a0606020606012f031312120c0c1a0a0f080705040e0910 71
    0xd04035000d80005050756600c28107c0748540e6240b81c12502c0c416140d2800400e1918a845496526007049203081c0811000d40410000350f54250300382c003152070900f80c50f69282c0000c1070000800100c20699500101443d00460500078680c5918020401030140248941c8401103200e00f01170050401d1880000002c18100342c910401039401c8001c101102c01520304508440c00c41880c0d0300542c2a81d00b0744402a0040c510000b020041000806003d80b40005502d05070b050311030843c249200510f1007500ca540a80a141050b02d0060b1a200e0003900a00c4141d00b010020301c950b07580051016440102440c1560144001060508052400003080c080d10034001b00042c00340e240000060403100c800c07510183c4d0f0b5583d50132107050b400401d98001895851110070003c02e05221340324130115030740286a4680840d0742c86952420301030040d8510002020085107a1220741d070456840b8103c00454200b2490f5032504a070014001d02c2280502d0701c0124800380802e9200400b0460000341c401e60341070400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 335241942 1250 335240692 335240713
    0x10815030a2001090807060504090506040e071e06050f0a0f0c0209070908160b0a080406060909030c02130b010e27040c05090a0b030a1713060e0415080607080402030708 74
    0x90b041014219503404034000101c00101007a00144010132a60300ea03958030b00700317401c00c07452034042c0c0b40c05401a640292074240000407494184858802425090500001c03030200e000314000c014902d903c0403041c000c0500c89484495418000c40b81080d14526080705051007003e02501c1030410f6000194101840d001001b4000e81c03c00170342426150900206d60521503040d1141c110794007103009035410000c0038000c240c441d40c004c030001da03002845030070045503460301d8150810498200c2c0c101500000c024204240960030000d00c2100565000242030003100c6200d00080c0000d010161081c3c0203003013014003190510440301c5000c91a620700c145044190919052003960303410341d8007581e44540307040e50100c0c0900e01c0a20804505500c068054011156252658000d40f581401190484d44081100612540720341f0001c002401d00b41d112201211a03810610040390b00390005042c1d074400550003845500c200080160344a502c610b880d82d010341d034601c08242805041c4d8001c203c984030341010340717 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 335243192 1250 335241942 335241983
    0x1e12090303010602011103100e04080c0a050c15090d110f0607080c010e0313030305160503031003030306080f100905010e0a081206040b0f0d141906110405010815030a 73
    0x714100c8000794002c1c004a0307101c0a21040d644001d9901003030740341400c0c90400440320100d2070b00d5032041c013800141c0c0c20500070401040c10210041003c582903040b0800b4101c7d5481c02c0310508601d09031003031185003840014000310301c0004480c40082c16010421210302c5850b903c0ca0520881c800c00906030b15101d4405141547d2960811a145640d550070845251540c0710000192040b204509410020007031642d1010784c0c9035400000e44a0420140113020404a0420130041d80510a0040d94801583c610700b001412510f854200d00016008408024142000040c41e060081441c050024159195140c200d004110000300c018480c02141c0517801072000c08005401510340501461240341da0300e82c10031085402e80258164000c2010309000b40905140380d005517414802e1100d0528400c1202c005171410452418101040001610781d8081004500420050480c00d86407141803604010010700440381c020a540c06652002151640569080010710109904a8540c00020b001c25045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 335244442 1250 335243192 335243197
    0x60603021003051003081602060c1f02180f030109020d0f1704030b040b100509090709060e010509011a090604031119240c020306090304150c05031e120903 68
    0x341c0c4601040e80703060001a0080c0903e81c0302d01c290808103c50303282180c0d40c2040c0354022041030408504030440101c0103841e40402080c0d21a66100101000c403810208800c1030000c410800103c10700501000d0045038189032242c0c6039000c00c03100c0b5420400740e1408a4010800c110300a5400320b10501148244009032610140c018020a40200c9070352803803940c02c0052246d480000e00c6c041d025000079020415000c6450307041440000e10242c8503680f82e0004202c01c10507140310200d50800d0070100500c284601c2004c1c007c01c08581030300504d602d040c002446154051049030348000007040c07640c15095010f022150342d03090080881e43c460382c03a402e002890440781071070140a03041c1b480000b0501c506011080040b940c505544110f030400440030800c0e1820343e00ba10380c0a02c070304aa80e0300c006036014040b1910801581005540784c901d009600c080c501940e00300c5d03034180504072a5040200388044120b44000b11818901301d85076254800c07110062041d440c4541c2080c2030305c0d040c801a040701000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 335245692 1250 335244442 335244449
    0x32a010c3809030910030b010c0b09071d060d0f080c010e030703200601050103111b1b0d0302030906130b07050c01090b1611030109050319081612050606160606 70
    0x201889580d2115180da0b2031080f0300b42c1c05d6224002e10062400b080c401d40000e46485410714000640d8103950b9640781403441c05407151241500000c1c8103001c0c280006104001c900c0c80c03039a191070241803101c04079100d00c00c0b02e07101038028054041c8020602c0300890484210454080007049071030245420b0740e4603504400c20883c000784c0603064046881040d00c168110504028020300116480c0900541c0140800c00500d610700c80203000429480300c2c2c4602d8040c01003503e0000c1c05d1800c4907003580d11168401c11a24030320030174403500043c0c0465400810703900501415103101d9507580744040b60010346c0c4004e0307015040342d51001401d841048808030f0481c007608801c0c0c03074107003150f07498000e105010701814248441c1da03044d2104aea40499422404554010b4000e400000d0a1400391070325030a550103010801e0883c110101901881913201401a0340003103100f0f201105100d110748000d20001e01100d40440d000d48810110702d0654400d4201d46403484a0344030b480074400c0902c0e003070010b0210b522 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 335246942 1250 335245692 335245793
    0x7090501050a090903020c0d0c0b0a0504030b06090405070909050709180b01080f0c150c1e0d030216030305180f0d020105130c051e090408030105032a010c 68
    0x70310000d030f4101076004105056525801a1403128400f10501c8082134a01c0016034816821a000207480c0003c01c0c003c040b0041d80d556943e507601d0641c10845000103004c0c0009008ad4100341c00c10010505c003052440a80d0444840410008a40e0520a141c003c00e1f400081c3d0040c601022903041c0c030300461040c86000d2003003000036482d0781e071001d11603100c8010103030454440e000501c10b4402d51409a440f20042c940112a96060200001d580c40c42c0410712002c032486190100c2400e51103544c208000e412080d00c524040d8a00140c000039085940b0510301c006043c50f46034001701d0b04894010b02c11280c1801c0b0801101d415496980d64556206240110200554680004618180502146111101d07088100005250b00e80b406101c07001540d03c50171b0b50b0621804100c10400da84071201103000b980260212510b95050104060402108944001c140061000d5007207442c00e0218802800b00405d081c90106078159007444451a003500d0034181780440c042c654542104610201c07000d2044405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 335248192 1250 335246942 335246959
    0x60e030d0306080c060c0304030b0106111c0c060209041e021b210c100e03181c11041806060f2c07090b190f050906030a0f0e0709050105 60
    0x3800180c00312207880c0070320082038200d00512082ca003040310041c901840024100d034503040e0340391101d00c901002070b000100062916400155200000c202040300303400b80c580340c2c0002e070007002c101424171101004014501070f00847d19101543c0c132070340502072003401e6580c0d004200000041110007540509034100e0802c81c10301244468600c002130828441902060401c0c84685c4582804940d800c0a07128038582e08c5807241481741c540d00e03030007007030140080380c001551a100030382ca01820802d0358110003401003440803501c101d0003c40b503c207140c50356000b9014400c1c3c60821b40120f03001e400ca10f00b1302c4c0d0100000e0701d101c0080080d1940000100d403c660454010280c0b944681400544440298084010744054403101003010f0700200da0850b41508215541ea83d0310179140003150040c02401c01c98000d06409051860740098403005640400d16003240ba203501030000505034000030b824045140c1d030725181e0074110901076002c0040d4015602c00c0700c841e42e55404901c805400300b406410b0180010f13 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 335249442 1250 335248192 335248213
    0x1e0a050709080a050c1203090d050a170a020c01120f060e06091302100f020c150a020c0102071217091801030519020607031d040501150201050c0a0f0f03090507060e03 73
    0x20030003c1d0450742c080c01504540c2000002c20070301c01d1110f06815014001003160060310b642d010402003480b4445d4024190045039410f00b1401041c01b4240e000c07084e44200301c0c90100c01d030f0104d4082d035012002d080c0850b446103840302c800c00402440c81c00c107282c42d00c0c6c0130000c111000340c48070300361060104881a81c10341d41c5e14501c104502a058500940100c1036401c14214240070f0181c50321481380b9441200c3c03c8003c0d100018107000007804181880f550000b464820041e8140811041c3c200e00707000502c149842e01c4500710040b24038400160415554580345509071510908032964004000d0540500c003080b0080c0040e000000c0c4000c480d948a405051801d0319446036000022a4005001034241001a00e003070318404001040c002c500039000d0045030040e40c4900c6114080d0840f0042072840300b000303090103400c44101800c083c081c02c10602c00001200d070300000b0039003000c002d86842034441f02211030540c003030080300c140104180544140442c11031b51000300b0910301d0000318200c900c01e140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 335250692 1250 335249442 335249459
    0xe180f0d091a0405011b2405040b061f030f151d1605121503010e0705100206090304060f121a0108011d0106050a0c140606030c10050307081e0a050709 66
    0x10f0380c410704d40400c3e6012500d5a15021000380400401c2c00740303e000840000900300440802e0840b80314030b540d16981c030300780028480d12a580c0360b4000026661190202001785e01c1d018924151002c0d0010161103c000c20000c0545802030100540c865000100164031007405410011001c941c202c0306601e180300107001403003024942c6115224585501c1d1420b204000b036001e40703810041031030a20403441516130a4544091040e64400e0400c40007402880b428101048409841c140240046500c030b0000d0092004020040750200d402b1400d002c0b000c0ca60b2007030f040d10901910390032102c02d2860f04988441701030340801c92100c005402d9a8486031341c1c2c1c071240d1a1364401c070705010209410741018010b00c2030b60700500c0140510202420a611020940d54550000050000078038241d0f8002b4014000305082c10012004c0d580d500b1212035040d038207203a82c000e02c02c5c00014405010004a00003180c103c2c0b0b6440c0750f00c0310780440c034150444a4079140c0704038405890705413201ca0001d8140b4100060042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 335251798 1106 335250692 335250697
    0x105040b030420010e03190f1406040510050112020d03090b0708091503040209040b06011202030114030f4303030f0314010e180f0d091a 60
    0x402515041818011041c0e05034107005c5003d10950065602040c5451031782d0031100c4185070307204a800d2201658620f0400944000ca050a61500d42003000c00c01c9881103020300c04841006180940f09811600244204c40c1c2890381e0b92106001031030002500f138144e0b400383c070b00b01c10300a0f00c07451011044c4c1c0c00704d0301c115115407000030742c9012130074001c00c401e02401e65602500e042d4580781e0041800c4041c002d000610b02c0c4100c8000803501e038084d003400340003010294802c40d101c0d80c50f100c0b450b00c030b900d1445145120384103c40d11220401c2c000a14041c3d043d68420045252015182c200454140a86000e4683c0003140f00c042c03202d44008560310b0015400313035984c071414600c02c1c2000b0f000c0f1815120315130903840910005203c000020203d481c0c12280d0990304907016802e003e01c0c40d040500c2010b100780a401209046d1807210fa02c043c018054801c202c200300b01c03030280c0405503074251 = true := by decide +kernel

theorem cover : BRFrame.Cov 335071942 335251798 := by
  have h0 := BRFrame.cov_init 335071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 335071942 ≤ n) (h2 : n < 335251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
