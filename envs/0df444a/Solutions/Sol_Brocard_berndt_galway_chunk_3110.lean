-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3110
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:41:23.088729+00:00
-- url     : https://prove2.me/submissions/fd3acff4-74b1-4d7e-a2e4-4689e6b51fd9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 559172661 ≤ n < 559352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 559173911 1250 559172661 559172681
    0x8180312010e09240601050c07060801211e0c0b1c110703090603020918040831050103150e071106090c06040e10180b09090609070303050f04030c18 65
    0xc0d11840070103080c1a1031351000d007107200300d81110383c0e40c1d981d400006884030b00c624242c40c1c0c0c561180c84d000003a10f540c03107580716050fa40c1c00000c0989906100c01000700381e4071503a401411401007039091541801c049110038400c035205003041403246940c0c2c2007000342600036240d0302119070080915903500c6c4015201e81c82d030310b0f2200040181005030688005080001501904c401c1c19400211540240d441c5003035101e1388403c889005015103401c1c0350800c1e407600104006003103000c954124210411a1841c5070381e03c45140d0a01d40d114514120044010340032100300c15955001040340480c0e070440c928921445550191104084103800b9030321186881c0d4001c041c00440c0e0080260007000307030385400850301200c0d04402590099110049180650300059000705449010020908402d8009420515801d84112140703d101c0c4c0e11908060b0703c4150444100703903103401161007800000d000d10050641103181d450328900b004d85035503030307030b15240120b4025009501002080c50304a0a0034003c5820070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 559175161 1250 559173911 559173913
    0x16021207080c0d060906050c04090f09020121020702030118030f02060f0a0b04020d0f0608010c08011208030711060108010f0606020d0915030917040602010c050a090608180312010e09 80
    0x62524040707548039074004000b07500c2040c000d40c0c10320610610350007141c4c80340c1e0401300c1040365081c10442881143e00c44d210b804107803810006401e4043c150fa20131040040d8040c1c4842813032031181c0c00010703c008800c000c03c5507840c0e801d001c104050b85092017840341c011500c0b030110500f0714041c240646100042c2814108540c4840c0c20008005445545142c2250b00c5950106640011400040283c0154560700d2a1149000700d41e81c0c141006421080481702c040001b00541c118410040350701d08000d019a188420480700968005a80034006607031051a03450441b52f0004881c000d1424a43e081e840782045039110354030001c1c2c1011a20070380740141098001000c4441a401d00035110840314451403e03403840700b941f405040d5000750400c0d0503a99211340308400540c54004c203030322590843d0007081c00642c0307880d42d503d0005000c1c0040b208042c0c0c507510340d0350b5040d04d4111304a40030384008048042510003107102c0ca06107030040000d02109401018445a1581030406d050502d0400810503aa9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 559176411 1250 559175161 559175173
    0x4030f11090f101215180c1502060606090303041205100c1713030e220c080f1b0f07030e0414270c061204030e0405010b09010302090312160212 63
    0x41c00c44580d14400c1220124002081e2402c1c413814105080c0e85070700c6a00e10740701c1c10203002e14003100c0c0c6c200c03403004a03510030001c1c40000768403900d6071032070340d1001060100981e000700081161441c0c0381b40030340f5184000904880c42d0544601d202455801ca203103080b251588088041c52410816000760f91181403603180a412810b00351840a8124034007401600140c0a9142000700303141c440c0e80004101c80000c1c003a4511070702c0e9641c1016180310383c1442000342c2841e0078420640e051180e0f9502d4000d1480c00c005c107089480b0205a0025061a40111001020100700340d00107510100c001d06200c902940f19103030484131420900040c5c6041d1454590407003030100420008020302c241030303000d4010b60801d5900d4234213640f2030141f401c03051406141d840f00010a42c0485600b54030480c500c6903109544640070345000e4000d02c01036450a0140088000081c003016906520941c05041494802800c580001698440c40c9c88035602c621034029100c01900c401ca0b0541c1800c54610801810360001061 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 559177661 1250 559176411 559176421
    0x12061903110102070503120702030f0c090403050f090301050f1821131d09100510230a03060605030d0c020f0906030703170a0f02010902130209010504030f11090f 71
    0x181140003400001d0880c00d99284004860b4400c1001c600a0328001c1d044800c4c01d07001c4580b05049402a4600724400c1c420590008131424000c11034070b013100c034042c00d04402921240d4090300c0c03e8010b449504001c0300700740701c005441d80e001d00035203015610860b40201c4905200f40320002c108184a9996041e92101400400c03003680540401a0404208582d40c0c5914180c2d45c0d08401281e00c2e4810b04000b18903c0c003203111320741f840c00e49500a0b40d40706c0072110540300b0382d5001005d459040700c0104000c0054135040044100034803000c640c0d4210440298a200000000640004250340054030400d81d940c0041c829030800b00702c5000c402c40c5508042e41c0412440e80010030f8803001885442c0140d0080e408a5500c0d01e00b0802d850186a1007003103169412215001111039030004d00090700010750386001b214003980103209201c0465000b4004e40c42e8040766100110296026050150400404210010106403403d0030707940440d21901e81f10039510840d90410607110000b41c85c4800c0c207403c10007400f03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 559178911 1250 559177661 559177699
    0x40e060624070203010608250e0c07170d0912021f0e010204081c03060501090e1602070515041404141603021b0c1518060903030f0703051206 62
    0x216404001c41c00c0784641455101600424015000001c0d050741c02d00d440401c94034400b1817842003d000060340d117000240341e0780c0d2207a52a00700703201c0d00ea000c1c00c06401048030030150a006114080c0500944a08031624401c20324050b84040850380c191aa0358640704100030030718858018200f410f10080086420100360001c001199510000c0b0359560f61070b03445021403003034042e100149660800d4600e0009500b2030203074403880203c4100000fa14000740030440d0342c012180e141c1a1101d44010707100c0365460044a1859444a840c501d0652180c4240001e1560340c020200d00c10b00440d03c41c0d80d4a5503d442010a0f18181d071642941c0f08a0a240d000c000c43d82d161a94107500c8014072010404840500c5820b0700284501d960f217180381c9141078075640388060002481184540203841103124107031604070702c004c28018140250021600801d014403035151107000703400300c8070f0010207803454030400740c003100b803150b10181045009c10f40200d02c0e44500710007900c2d41c0d0f9100c00195640d80c0c154420000074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 559180161 1250 559178911 559178929
    0x20f210720100b030f0303070c0b0106210f0b1512060d050d0c030e060f1207020a0206180f04050115080106031e0c12060608060301110414090c07050d0905040e0606 72
    0xc150070b99030f40f0300e4221076904100c0c0d40d800f043e500007a40c0d9030341402c1c1001081c4245601c020b44802385400000180180f0880c1390b034803820b0f01e0207400007944d0b02d56200702c0007428110b0342c0240659269841410303e03030303244034401c1200d21042c00d4107560b580710340d134150031011001030000d440b900c002241c05000c00c2c400f19042c2010b891170b00d440301d4001d15515081d80d8540c017200c0066001007001c02c40488258a50009054488141e414280b0300d07500c04000b00d035228548000290000d10074131200c40e9140070707e42c60402120008213101d849860741c0c00458100c070802d90005000840d60f1182c032901c1a0000e03c138a01500140c6000d110307101d40f84c0c08544c0000105511002981d80d66004080f000c0d00c6a481c2c00809402007109001321596043c000b06001010b80d1598400c0d407030189007a1444a40700c2c1102c1c00c8840c0701004285551a081c104000d40c20f005211040b10207040029400290003845400006401d41c0c42c2e02c0442400e103400d0204841c82440c80507840e500c003c062082959410b00d41c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 559181411 1250 559180161 559180183
    0xd0c0e1504051e0c0c16140f0d1101051b03070605130308071d03030a020c1306140d0503070f1b09020a020c040c090807030614090304030b0a020f210720 67
    0x1000e10251508a5511840e200320841501c480c0204680c6c0564804407003070641c1210000c1d00054292020b410402600c405425840d941c801c000d00d03c1a00081c030303000700e05c0d0011ba405061003400c2211845200a40303c0708030103103008580001840200300032080c4a01600021709030801d800b440350743d13903010700021401b401d03860502491034202914290007180580f60f4000207000d8a40700c01c84400c3c060354403008085158071410040b4200440606030340f08400c00c58003044c2d211001c140a000601040c0800c1d8602540e00d8041004020045500c0500d5071204502c1038110000f94020031204446043c40da80143c10840c0c0108803031040076900203031854030480122000241200501419524016207502901c440d024105c00041445100d910840800c03407014402c507601d80d0740d215a25204e1159010080884000d0004960800b08030360143c00d105800c800c1d00380c5801407251603182c188110280342c000020010003003041c0260302042400e08402101c20070140c01c0b03401d182081d103620b41800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 559182661 1250 559181411 559181461
    0x40f050103080d18080a020a060b030d0c0305030a020d2405040b0f01030b0102070312020d021002161205070614190b1f0504030606240504051302090d0c0e150405 71
    0x13040e032000b1201c1c4490228a541c00760109554480e83c0f840a52500740e12030090318071503c0c00c040c0003040e040c045011480c90000c2d940313211140803541d038240ca02d50000740040d484540c1c03c0c41480c80788120b40c492180d190100d0714603850500f02d2200c1072035444045412a80c003403418a0048070054441603044110f003c0c007400c1c0440c5004500d40102d25081440d880070b062009030418030725200d0340124213003034000c205074240c84401c400c80700682c06a02c41c0c07100a0308803000c00401174001c035503030b580c40521025561810500e040c10b5529441d058030208000380069225942c14003e04480b50000c130001c964613440244544a900c80000b581d5100072050000c0d4040b000151014107803003842250060b5070b10038000c00907182c8619240342590031141816400165550b41410114082c2003aa421901d00800016107015045508006074120244068000003100581d4000540f01d00600015118903100c04103989400c40d10041000884c80c46980201d10304010f109c0349005501d044a820b4000366 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 559183911 1250 559182661 559182671
    0xc0f0313090e031204030f030e120a140c030a0e0a05180a0209060c01330305030316030204091e06090216112409150306010e0f0109150c02040f050103080d 68
    0x40340342d42188a100c048041d041524070401c020541c000c801c1080044156800300b202d00485046d03a1b513900321060f40044101410301c40d62100c1d500c00ea50522007004041076507030410003034540d00380c6503400c400b40034000b0541d10032801a040c01c12850585c010501203070502e2050300c152a00943c1e075840941500840c03500000e07109502d0310340108454804940310003c200a0f40344e194640c1c0784082c60a0005900140700c00c1d0070032a04118060241079981141c0914035585460fa4404d401d00344d003200e1582490b400380000195070314907104074039140244484101400d4080c00d082821100690071800c1414030600c01c01e000c1c01100000c00c40101e07800140c00c001d0042540003c2c2e1281c141350f50912072500c5070031620301c00704801c038060000682e095a481c0809000c119081409000880c0c045000030b16140341e404007440d000940c0654414181041d000703064440d040c000d26030f511200208045170140c40c42e0030441c28148038010f160741c02040d00300035950540d550325010348a07550508032004c0d01c1d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 559185161 1250 559183911 559183931
    0x203060f0d080d1103011211061318050117030409150e0103081b0706050f07060b090c0a02010e03190e01180821030723160b0906060103050408040b28050c0f031309 72
    0x48401c407925800c030300d030088481642d22103480091030454003040c2f61403414072000040a041c2031280d40301c1400070201650138281020983c0c40200114010350389070040d54840012006482840680039500801030141e44480905d03414804c0d0f034070724003e400d07558040e040403c80c1c1036004003910807540050401c959141c01c1428541701030003034141c58980c00a24003081c00744003074103c80213081c2825160000d1100c408403800c100d0b01d030302601c424103150720060700c00403280d90710802c2040782c080c4050500c12040065105407c0c00c55045801c4558598445050007000307445460702c01405250b10340720766207107180c4940001e1029031043d041c0c0700f180c4030304005a00c40c03c0b9480242c6088681e61204080c00d41905c0c02c0c4070345241016540846503000d0400811500d522038010103220340d030400b4600340303041d1900e02d064640380c0c041d4101b1160328510061080840305505800980020103a440c5604e59090030915800c041c4100104c50b1142e004001d040040032010074424111110243e000450645c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 559186411 1250 559185161 559185169
    0x303050322060608030a12060e010b0706090609030f232b1a04050f091b040b03010e03030702010608031c0b0609030303180717100203060f0d080d1103011211 69
    0x524002040b1a040000c0811101c90002c003078030b03000010f6601c840b9140b4103003090000707e0300d6502407011403001d0080103008501d80040181711840c414040001d400115444403002c0342d100ca003045000962034200c900300c00da404200140030744800001c00004a29442d460200c611810040c4580c7d940000c80030480300781510464a104859000141329295005c0d0b240d8a00da15200880c51043d49424041040d0b1288200303440c2c8548030075801020583c3c1c5030080b07070300094290640ea43c1c1c03040e1210300d00d180f00c7d18203018100c0070044000c0115140d0a2010000e400d481c5560000032856205200c03450324180581c500c121111108580001c0c825910008110507108060300e064041c44000180701401000c075441d0300340311010b102520003190301d0300b5120b100e146007c52400c0490b489010841819030056000316000100141119045008040420400259000180c40b40e541c04100030344065024010440d814010284640c82d42d81043d20443c840d541800c03009c0d120700d81e456440d41c001d4907 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 559187661 1250 559186411 559186471
    0x1240e19050a09020a0f11030703080c090a06050405030d1b03081905090d020d14041806080d08040c06030606090b0a120608010b03010e030703080105090901060b07140c0a03030503 79
    0x100c050302c0002402d4840c1c8141000c0d40c4068035210000e08003601508401744a98018428242d00401841c40c003540b94804807203108010703010609900c000c0280d04919540c449455004060030f465060319036140000701800e100d190300020080c0241458044400362403401c0b403800d20790381814100f9490304d031010803c804220031282405c0140c501400c5c48070000340098000440490b9030f0840d100c2c001403000c100c0341ea40c105041c4581881c01880144040c28803164100344145411000150580e9900d5003585020100410f0b44007007812001444140080d84400300302034031140c1802e001c40c80c40c0c404000c090b02c0281c80341d12051400452401d890711b11404036a080703542034034018085562100c003424020a4400352951280d8641011100696008001d41c1c0703895406840e000034580c0382c00c09004d01003034024030110055607078500c0801e40904a90103812505d020f6103003409040f42c151846d0745840d113455a020302c03c40350351104200082e03002d030440f6404800c0351601c041200c40c02103000e0b0002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 559188911 1250 559187661 559187669
    0x703110307030c500a1a0a15050103111306050c301b03030106031d0c030a060b0d020a121b181a04090b01240e19 50
    0x4000015a442403641c400c0c440306a40340605100c2492281141c403c1510f1600d070b4210211148184030450041d000c0c0003811130103510f401181020070100b0744103c90400740d41a10444061903040b10307004540c0d040e8020a0ba0141a072a000c120082c50a02680002d03031161044038109601ca50109084031085000c0d550140440e50051020a880340350141064000c8003010155220381c0c80341001440750a2001d00400d490b4000259654126100e00d4001e80c0c81506025521510082c420725074030070820040d802007040343d60015240004890880d0346000704081d0f00e01d6a0301040b05040581d402142d00d4141076403019000690540d1040401d00358541d1204c042d50007c800c4400040b406074070070640c0c50b064030941460580040701150040c41c48524001c1a000034150356000180e18419404140c80708005060f19004400d45400101510041c2404841d43c011000040200e0051513141c01d88004400b03d01a203c00d0b07562400905680030a0034030b5114020341e0b494800942c6940701c501004e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 559190161 1250 559188911 559188913
    0x160b120a1d0a0b0c040e01050f0a0b1204050714091305120a020303161e1d04090f0201030608061b07080d0203070504060810050607030e0406170a0b0c0c07030305070311 74
    0x300566450140c54402d401030076a0301c1401a40041c02e42c1c0703000c0b0b04132010340d014a03840b4100da03400c0009100428004e08181d5070410340420021440e112a18094029054010801340803485e0610304982041c80c42d91090b200f00c49101c9511090343c0c2d412458a40c480740c214044070114074117050042c6000e4140c80d1048107017a00082d80440582d011000b5403090240d03440009a204142104481d075107011464507001d85906800307100161310980728943c0307030241422803240030b02c00316002a044515141d007c80320b1001c8845103008550301070055900400480028000034500004000c03215021628010030000000901c2400c010240007521260009d56004648926081c000900346c0e60080c05250040703004007001899481c0640e80d8581558406010103040c0b02c810394007074800c811010a4503910540b01c260114817100440c0d4181c40c0e0341d0041d801002010414106505860805400400c0c1c1050030024008500c2c1c00081c1c1000710381d414607201e6580c40c4141012207000c1010244020f807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 559191411 1250 559190161 559190201
    0x114030a060f0f0b0a1a03040f1211010f050c0313060f06060302030f01090207050d03050901091a070e01030509070308090a030b0a090b07050c06010510020a15020a02160b120a 77
    0x55482c0320340c00064024018541000040c541c1000c00131032201c14462000c0140c031400125a4410001d000f45400521469030311540c9507055964a12071030201600800040040c0381d01e203003185003400740040c208507500c020405810701c52582089440018080007105086094440411034250311071601d4410342c802c20407826480382c1005000e5031060700e00c507607040b41d65000072078400c5582c400c030b8007000e43c08070003000203008100043d070140a0042103600207550768540000465800c0d030311407000d03040962940d13883c0c0c1752000e4054500d00108080c2030416160408010f101d200c0010801c0659401102c0207440d4098440000c030956107035000245401155001e02c00a0b060315006903034030314070416603c1c0e0155100c1c50115140c2c0500403801b071199200c0c6004000d103042c03e40c0917201c2c4091603c10790720900ad440e00c4000c0c2410400c2c9030102c1d42c0d0340c000303a518040c1da03041c442050001446c0c2c03c002e21051401c40075200c40e02800303062804050100b4082200e000d581c2d4416001c2491102c41269 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 559192661 1250 559191411 559191431
    0xf0d20010c061407201e031e070501150b09091012121d01050304080d0e0d0c0c060c02090609090111130302040c08010f1a0913140609060a0303110a0c0807060e180114030a06 76
    0x903035074021701402c440c113600f048403440a04070f691043c330090317589065001c1c1c00c1900369010018a803c0252a0f1500c0c035010480100b07280500d16282d200e00c901800045c0c0c6506d0880c40018030110114016160001c0c0095100c81140e030301c40c0c00c45c1e8000780c000d007116803101c10440c5000c00a01944105105500c90034180e0300010340c2240410f48002d015074032002d080d554941055851841d04c0c0d600035403028002c8005125454591041500130940c0300002446207049004003103250b02082c1e000c0741407520a04d04004514190003107080d000b20928011300c242d498824107074503103403c80c09002500c45481c0a02c882d4000e90030309032480c0c80700090104e8000040c4413000d000800341c40202003030029a408c0000d10604240d10b00328064440a010f5400f031a19648040362840800c0003008181e004034035601009c522407408004c081c02610014014043c54008007901140002400ca805201e012503100482d07111401e040341120100d04503103000c004900f00217402c2441c0894001c0c0000c0c90840c0d151 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 559193911 1250 559192661 559192717
    0x90603030801060801060512160c06020430110603150a060305070f090302030d030e0304050d051501080d05032d150f0d20010c061407201e03 62
    0x7504840140e15200c05030f076201c11045410307116108001d680311100001041003550107028010b0100362501c1c0002c1a024560b075124180d1384960302c01d820300035800030500700e004216030913507c84c04034800e6140d4070302da4030b603a4100117561940c6e9010710840c3e02000164220b55201045084540002d04070345549480d8030010b8000c25068980c40009001400301c54505801a8280c0302547e40013402420844a80201203014045da2040c03480580002e01c000a280d407282d00c50300405038031503070103000041103d12200780301c08016400361409510150b00b0010054005048a80001d400080042c041030300010010901c003085407901c107201040e10800400c0c03084008a81c0d07030110308482c0c01c8001919241040311441a060700035000602e0314400314280c1a0001d1501540c1a0605180c0c0c44004542c4441080f02d01180e200a442100d0900300503d0342d501a41e0010251440c50124a8141c601d250580c2d44400600c081210030016010440b00140200140e50482225540031000200c03296030031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 559195161 1250 559193911 559193927
    0x41e0e01092a05060c100e010204031209031a0c090904060b01030c05041d061c030305010e070c05060609060418050c130e1209010318200f01120e01020409060303 71
    0x55605003200703030410001100c0441a2000c0318900354442d030b280c6041c00104101c0343d2001910080314803541d500190000130b0f034024150701d07070201800162200d18505246a41c5010307110480100112800f060001178004200d07440c4058454a00c0c1041d90f83d041d82d404507900c5030010160340b22800e2001c000400000c2e03080603406080a83c3e0900500241c05d00070359050189014072580e11500c440454040500b29040581c0540b00034402580316409a402c2c0310303080b24004080d80000d4440d401032140755008c4d40c19a070400100d103090001c01e80b59455181e06c2c0c142c0903003107a01c1802c002011802c680d0321a0030044040500da9980c42081d00f0b0b920308030b0707a52202046000c0c012050b0340300c1c2c1030f9110304c0e500c1451002401400074146070000320a600d60541d10600341c2c0c50515554004454801d0000000c43c1c0c0720038881c0741d24003c009107031110124541028034090b441608a02400507050360b0103107810b03003403100c01d100106581c01c0200b4881e000e40919000b03007400e20f20303101d000000e041d440006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 559196411 1250 559195161 559195163
    0x120111040b1309051801150b0909040f080c150f100608040f150b0f12030301030f2f0f2b0804032012160b09060c070b0405010215060d02041e0e0109 65
    0xc00c92180a6810441c1c0b601440c454608084410300000701513040ae4102180c1c03244c4244282c001400856980030b015800c41410308c90750303500200d070344c0685045032040305030003203a5206204140c0c47e000c028007084e404036000c1ca02c20080d0307400208041103403034441504181e90202c2040d01d50b01c10140700f200103045041d40e00d03100e0650505000114100308240034491805800a0b5181da03086441d0184940c4100a003191240c10300c2980344a44130689558003a2202d001e100c00b0300b0481c5180030411580059a0075078031600c5c18110300340b400e075000682c69011010110113406401458205062180510b50025040d0012142c42000042c030845050510328411560b03107a0f001100f55503030f40d8540240000c1110286586000d10124204001601104100906c428605805512030a0621540342d002010142d4007007410b200c290f07010b010a84c0550040c0c0010300052500c8000503135810f12151000e400f1380c0d41c03200481a020181c2c50070b515a040180018041c11aa26016078000c2c400458 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 559197661 1250 559196411 559196413
    0x170307020d020106050d02220c020c130510090b060c01050c03342708010203072703081804020703080907050105070c05102a03090f08060711030c1902120111040b13090518 75
    0x114cc039001d40300750f10400b4092400300000d900402e0030075903d0401410014003460348400140001441e42100f402150b00c181d010300502c41d00d0781005141540c00d1040003444595400c3d501091a058440355440c483c0050b41d00c0c074080ca907903040002c20303483c0041e4184110800015840c5c3c0441c0508054004500401e0550385801c540c03011403409034554217010000b011800f0380c2c0581000410f0640001e80000c00c0402420354401440c003000404903486040d007103021030009020007a246805000c5807000f860207013403a80c80c050940d90350345481c50312070099038400c01001d8175180381c240c8107454800609510340c0c0401c0b0f413040c08400c414600c03200c200e07044000404041c030104110040c0d00c1f910b03003101c440b040180038031707190b00c1d074141c3e0400c206840d540d885e840705101d091030300e203404c12000082488000c444c0707910b003000b801030000c440030140342ca03641030381050004484086040d0480b01101c040481054175114014046070320303a07189900010420b4107200c18007080450f010031000004007108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 559198911 1250 559197661 559197679
    0xf180f080a0b0c03040c090b18332103070c0602030c010b0d080301120311071428171f020316110c150403170307020d020106050d02220c020c 62
    0x610944411320048078010910180381130104101c1c1a50341000c3d800340d0000340681c89214020007070380106c0004482180c07500741d250000104081941c0c003d0900c1010603080c45411103900c10200d0301d40303c0c00750310b01e40d1111083d140b9403d44040500035600702a600004000c603059690000950301e41040501e0800e039440c0c50100380e103914240900c42c1d49281e004250904580c41e0040c244a0100341c0e1506030180500014000c0344c1c482d051100c00042e1402140254255030722006100c0c24030b002c0c07616a0842d840c0c03000c1088123060000d07511012981048035109600301c05400540c20a00c460444240c0724600c140214914040c40d0051841454003888281042c1c10501c0103c95645c458208619141c01c0b11003c00f03074904007500941402c0001c05560b074541982d965484408400140510100d01408014080d000d42d05115140700400103200a00100341040c000904400c0d0018000388900f0f14418110b8030175003251140e0751080041c0008005154050601a4540385449115440340c9010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 559200161 1250 559198911 559198921
    0x512070f080a03120e011b020d020c04051302040c021207030207060f170f090102040f0902220b160309051017090f190501090804060306030c0608070f180f080a0b 71
    0x1d00c00000303075090360b1340300e0b0200001a81300e801495016020340740d6548483c00301c9011700d07450200816000700313a8010300c0c001c6000400203061455688510b4803c13030808040c8160343c00503036945e580a46e0122000180500c000c07000764940103000300356800e80303038022880505150b00420854203d50281c0c8981c2000341d0400750869001c3c6510700444240758021010802d400311a00d12030351301c821408001490305441d0340451200c03c03050b90010308016000140782c1416286080c00d14034031740200c2501c10000b800c1101c00c144074090210840d800e01c2d081c400c0030301131520a900100013001c001c0c0002041300d14484005194005000d42110f0782a5801e01190013550000b81e6521007001c4000941000d0310b5028807140c07105030a0100b5030701036403211440713004180003034002d1004091035200098128511700c0c20800c03000156000c42c051180b00806c0084a0381c12441228081c003490bd840c0100301003008040ba40748113a90031200c00c46160340b9020402810000752140b501c0d0151060607156921 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 559201411 1250 559200161 559200163
    0x8180f0102100b03070f1820070f031403010801020a17060114030402040905060f180307020a0513091709040b030d021903050c0109030e040b0102010b1c0c0512070f08 73
    0x16610454016400000b6201a050103a4404004084004d040e1400c2590300c2c907407411540c00341d40100841106003c0d894089030b4051041d000301d11a032003020343c049182d0f43e403034039118041c00001501031048141617000301449003283c02d07409604a81260344030358550302558000c5d006048802d0104408c0e03c100c0b0781f0050341100452243d10305961b0000b449840944181c0c2d5900003a0080b0713001074035940c16000040c0709000961040d0824051034020b8503040020340480056032201404540080000c2e00241c1c5446108405443d02902d0520035080203600320740040683c0100a400004401980c80300a10150010f04005400321810f00064848000700b41e103031302125140c1c0015070f1008000c621240b40c071143d0003500a001381031090030010300012490039140023107021400030305004010f4926241610803034408290170303c02003080c1c030244404a8240c0c0c000002044802030b100d940c1c41d04000d40c220800c4080c0401800a5450441c10704066655510902071040010024580480d03411701c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 559202661 1250 559201411 559201429
    0x90605060a1a09060d050103050f070b120105060c0a020d08180301110a0809190503070204050109020a020a0201140717030402030d02280f080712020601120309090c02190818 76
    0x2941e2804040301202102c0107610340d001007074107604584113012084c0c0441940c4943c3d07000714040c5010701114a0180d1400b41891150b400400709502e080c413407602d15201106090341500d00c26140c640e6152140d006d81860929000e40080d4440304011802c010040705002500415500742507160800302420101802e0b122001c2030320920300b105100c4154a103201d19001c0b500b00790103270f05441c0d0001c0200b4012001d038130100c2d800e66180c5c0c40041d0060450503d44180d500406825104500f0144074001c02911480801c101030b042000500ca411441e0403030b5000c030380540354400b0801d408075a00e83d5120038036800441b402e034820f02407240d50b00859800480c20300e51206500320464450b82c00c850003880711007603035807040c1d070f00160411414001641031001050854010103945d00120492440246001c00503007200c1c03240c5001803021400aa00095898143c0e0140ca00204000101d5a0120300d4412035003001c1000511020201c0140180d20780140340c1000b0986aa25915802c1024803240031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 559203911 1250 559202661 559202669
    0x150928090b1e011b05280201020c013005040c0e09100f0906050f0402030601050a05060a03020d021207090911030c030f090a0210020c1c02150c01020c10090605060a 72
    0xe091103030300c540d0300c0601c0b410480c000014101441d843d804034494444607110810200c0300395005414401400c010007440420712003040500004005450307000035150301601a49606020b03071003804c8207890110300208901c84a01842d0010002c04050f007034805044155810340b000083c01c2008030314043e54080862141040c5402858074072507669840004061002500c074459a0352101c9000003951405168002e613501300f1700040e0303800d00740101428400e043c0d109070302c05e600030101003115803a034605550781b410380c0f41001071b110200a07449030042e00c244a071640f4114003c200300005990017180c01d20580d007007440304016007503110b07181c010688029100c00301060028400140070a03e102d400c0c0790301201100544d40429120380c08505080090241e400144c1c00c401490340e86801c100f0750f02060500300e50030320481c140c1280c01041c48410082043c5008040001d1a0000c9141c2501101c04454110040b94200c4a2850010f4000e01c0c4200086401900b09004500c20785080c1c00c00005031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 559205161 1250 559203911 559203919
    0x11409070b220914040213090b0a091506080a0512040e0a090302030702031002030108100b100c0302070e0c071106031b03060a0509040f11011d150928090b 68
    0x1c0c29469502802007820395850700c64440b10214181042e03006403d81030311074001c0d0020340d041c41e104115035030b40708800c805034072854045880c1c0801c200c040c0032030708455512800035070b64900b420400541c19604565a2042e03042000009205100007445004a40924261455280008001c000c0381c81144038003100c010318130300403800445e0503900029009110307004992901d03074030f43c0c003080c01e08100c400c0f8071030344a13030100041003211810312000300884c0501104201c144002c0300010303030304800850b0040412900b48861000c160003000650f000d400103150402c0f040c41c0030100e10b070940d4091241101c04076040c0c2506101410300c0003e582c0a08465a0f00d00400c10111403003440301e030002411240d00c4020030200181c980c41d0480501e000f01d010b01a040001d08039401d102d4031901a0084032410803401250728814140b224002c0800da8804440090700050070103108840c0c1d018510350340d0383c0040c400c80f403014400d451041c00a115140c0d807003804d48a40d42da1410804503070035a4812508 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 559206411 1250 559205161 559205167
    0x7080f13030e04060e070c03030b0a2d0812070c0e0411010c080d02071a0906011a0306061e13050604080a0605090a05070e0f06090412031a060c011409070b 68
    0x703800303a185500e54100250000034065a10200240c0710300042d2440c90205422080c3c642c103051381401400420f510a45d52080490b2510300790780040700f44042c883c120480642c05500c04164203691510003001c2c0003044030100b007446803807200f207580041001c84907200c4070710300016000e001541003482141c0040085901d031003c0401901e101045050854440b101004034600d00011880030700041409040209501a0301d08161a11080c000e00500d199511040041000440007499890030003d240d01040e220707201ca4010440d0fa01601c8403900e1014443d4085c400d001d020340c00a401e241c42c01b4510720049955601c103004481c82a40101a05600303c50a00340c04150035401c619040803010b030496800c4401c540f609030501540d5080940c100702c0d00814020822590840381d078000c1c0084400340001c4c10143d17a0100c0341050300c1d00034421302d51180c80b2140c810800451400081001a00312651400704001880c0207120340da10440100d2444000b08003c154001440d00580d018868414a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 559207661 1250 559206411 559206413
    0x40e19060e160201090b010b0a110c090c070302031c0906050604290f190602061602070e370606020f0a03082212121b0f050403081207080f13 62
    0x1c000d603200703a500c100f0356403100100750010320340c03110740b85c003c1020b1100c2c140c8440c28030000070052444280703004001c0d0320015031a0469641c000750a03400c030700c0d5002d205a40f00c100c4d180a80c25400780d2142042c0c030b5912099145c0001401703402c0689018842c0004000958900702044125405a4102e20002c0340388070044500c820040700c02c12007c07000608054000b036000c030000e5840c07641f4494250082c0c0345e0784000c20580c0e030100080c13a0044048600ca801c00c5200030402540d541441c41003010307244800021480c1400c1c1300d05c1c01c08964005000d0b00348442481c441d040405018000040c010b90b1520000148061010500d81c0a00000601400002d203580e1811510540c0c0540484a000ca005a0310030340c1e8400c95245035601ca106500340040000c0494014101501ca4031b041510039080407030203514500f04086901141c1a107041c56212175a401008881a004982004000d440c002440481028180c403841e4800c1c3e0880d0f44482c2035075240c40c60714800b000195202611400ca84110300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 559208911 1250 559207661 559207681
    0x21110607020d0f1707051312060b010305100b0f0f04090213030b06030c15071e050a050d05040302061c020903030406080919021e030a0f030e0f010305010f09051b040e19060e 76
    0x10101c040403807c880101d8613501d96900c4154202c108a0307089983d14841406960107020f0390f80c0c0410300381340c82100c0c1351a0042e103203114410395000540000f00010194051000b001c1524041c04030a580dc6480740c54100c0000c1991070240000e45500040354001400d0b494000703003401c500c001c09452004001c50890b110b0203542c201da2000c41d80f0041c860b04210840130201d41c4210260f0094004024494450400c14201030303e15400c80d0810804001c2071000d40c40704400c8441c449201400704084d480001c11100c0280075504c01941d141c0400500010b0321a030003d1260300031410101680c40108081c0443c1054282904000f90000d00d03d003080988402803190444601d8006415500c00d80a59610b40c641d4000415045011586005420945040c582c5101030700d0f8500382030030045541400341c2140c10b6552481101c40207511000082c0c0c2c947c02448806075074030701107107101d0b88807500e4000c892555241110f0441c1c140d110701244092400325401220101c6036030360901540307a22408012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 559210161 1250 559208911 559208917
    0xf03030907090207140d120b040902010c030e04111b01050a06030f080f04050a0b0307020f1629070305030613090b070f0c0213020315030a21110607020d0f170705 71
    0xa68800036203401c1009001401d00076084401c901c0e9a50b48002c07d406a000800c0700d0800ca0480d02940c0ba0800d1100141d82180685201581500340456804c1200700000c000c0d1841c0342840e9142d49020441e5103c400b490400c0c050b162400030300034003c2e5941c0c0c210038802c88240d48000303403007000b1006641001c2079a0720000c00a56180c0e441e024a069100c1002c10700800e409d610010f400da500204000109a05201e0b03494448070700e6016050340e44032001040a0081d45000f40c0c02c8804244648a070504210b02c0e00b0083c03400040c1d003c50321001e05043c0030f88550401c9071054042c900f07128a95602d00340302c0c4101c01ca441c0c2d102001d502903458407481110400400201c0005000c12800038074050380c0c41f0404010030302c80010b00036030b607031609049089802e10850030a038082d9000c40401000142030031104001080c52180326000d200c1c0301d50b02100e0b543d100404041d8076010755020b011005601041c2c4c642034920b951160058071801000c00c403405d8207200d613481104070081c00400d10040c803903001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 559211411 1250 559210161 559210163
    0xe010509072606150a050405060108060411120907061709060c0d0b030109240207050a11040b0a09060305152211100804060501080a02060403060b0a17030c0f03030907090207 76
    0x94055400c10340b01020b441c100c415640c921345012000c5101c042860309100c1e42000d05030955050003c0d050440020744140000b404031881a919110341c240c80100b0b10042e03410484c15108082001e0030700e107010684030a11402a0800904070a44500b04440c10200040c0a404200010281682d03005e80d40da03c0c1e604040c124900d91a100c65a10206540c00d010301d5440d580070740005540002c060101d100346511102d10101481c0c0140f00c1400442c3c40401e10040f0a6007240052100030002c900241c0113011412190b58001241c450100301031035035038842d0060300e10841c101d0300340c6240759088002c803ca0403900c1a29190030f61840080e1048010343d006802c0d882103001400c05c00c0e01c1e20001da9045000200500055103140030002400824014940144840c1000e010701413080e03001718034244a04d01019040700d88400c803820854030344ac003401300108602810501150280007444d6103981c0300700408541840b48424035220720f00301104882c0160780040040850a18200e4520702035000800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 559212661 1250 559211411 559211459
    0x3140307180801020d0c030b0102070501120f0509060a1a100f09030c062a0203060f0c0904050406020d05060a06020714011707020c0a0b030c07020909160602030307030e01050907 78
    0x20244544440307101c264010304079200000d40c40b0308140707000c541205d201042150405092200e00c0c4820790f00404c009060714001c1c6000d822a003180e88903680a462400800394045144c60108a51801c0124015009030bd00002c140300d2900e006103202840c8480c0907960390b00000c0e0b0030b0540240c03070095540c030356440c4060074004e100d15901d071a1841d00c2c81596010101003407141741a00e88100c02d1090085a0a82c2141410b0000c1000d4003c41c2d030750381c00246241c184000c4074000c527410313400075001ea41808200030428031061400c1d103408406034216040c100500303800c00020648510345401110260b5003168001c1006e2032514610040c01042404854140515011600703141c0d06103c8029200e032525800500c51040040c05002c0d500110754000c162024050080c8030510460100712502d00d9011240e008058481201860604111210081c18990640300003d0380c540c02101661092030300d5142000381c8041441d005080c1c507412180f81080f504056820300a0402c01012040700c00d220032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 559213911 1250 559212661 559212677
    0xf05040315050717190606023f0c2d0c0913050a060c0806010804030906050f1b0606040b03150604020c01150f09060902090f130b1905030d02030703140307 68
    0x4c00c903074031408252150052803200c24800d4000f0b10740c502600006005500c0106007a258100010702d0a410f9001400c000158000c0d5001c402c080301c0711311881181070808203030760350b4090040f190303500d1004a03c5099480c40c01c1406034100b403000391002100c000c10fa00541903000030b050800c82840c00c000c0540c1058040070303a001d00440c204200000c5031070701c0ba08000414129181015001d860010b0490b410094184e040100080d8400d900c0c004480301403c000d44c41f00c1034000b8581c8903002c0c580c0c40071103a81c4010309a0f2100d800000d46107000f41410366003003022904410605031034811700d41030300c2c6408003018082400c50030280d005000302080c1ca03000051200605204441c81a80b991100300038122042091200c2d040ea4844d410043c070000c0000c41c5070607a400007250410040f0001c10b4450714200b1040c10800440390882040300c10002c011049241c0c00e195022416622402840d0103440740b090200c2a0f0740c00003084410103038142d01e0341502403200d040080c11551000300000200100c3c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 559215161 1250 559213911 559213937
    0x80403020712080c12070812060a03020607030806130b01020d08130c03030807030f061a0d14010b040306060e01052103040302040c03050a290d140f070302010f050403150507 76
    0x107082401c4410302c1243e0b4a9902c8500c1c1e111603103400304002c08400840030802026000800140071610a4402d003101c1d5075040e40c51400041e00b601c070301e40c03000e03400140004a901c2090751105690384a40750498003008100e07030090710042201c04080030180542d01406440d22894041c0d400c82d9407154a641c55800400605c1d07840d0800c50002d50b104501041c4d02606000d01c0c1c40d09030180140c0000780060400c80c00303240005030b1802e4003418869401a0000086914a81d40142c0088485140480410402c4c1d40e5036880b02009600911055441510b8108041b45c50820494454100d1300003d2100c02c2985030b101c003c0c0d0220303c0c0e080c03d00d0078500c800c000000042c0c07200e001c1d52640c1600c9031000681490400408000d80d2401040c00201034620901031000309004c5496030f60800d81543ea61100c60a20b1500c000c1421122400c1c0d162807103854440d0500340c900064580c10b0740d20030399038903118800c01c40d01503410b40140d00000b4444800c25081a01180c880c1c4e0140e54403039000c4c50520848100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 559216411 1250 559215161 559215179
    0xc010b03010e01090203060a0908030105010302090310050906160203040b030703050c190e04060b0a0c030806040906050f1602060f010302010c031e0c0c050f03030708030405070b0f1c05090d0804030207 88
    0xb1a040203090741e51141c4c0c659080d0700d024845140d01c03c1074a4024084204603540d1800da500c0305020305418190301017400c01003502e0401c20340741c0e2160000f80400003402d202c1c18003603484404407000c40380090008242c2d81014030100985007121586484203045445259095026007030041001840b00e00c1440010200c0e0300c1c0d1500c01d003035003103117440e420b00b030802c0706007800305642003904119907032101001502d86080c0d00011680000e9010300c6d0842254803002d0010700078040002000c0c0040d81410140040c92508680c1ca9000e0102e43c86e044115204c9000d003aa200c15044880300032151038a0010805540941e00d00c09601d442860301341000ea01d420f611140d003801003004040007450071540d000c100f00f0980302c0c01d800341c5170481c1c02c02404001400041ea8a01c500303a0020489040030002c101040020880760b005040c40310009600d980201c200084d82e0380115504141502101d40c1180c1000040e108950144039550040c0104249074001a900814054400c07011441040400546298 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 559217661 1250 559216411 559216421
    0x60d1e02031912030507090e040209060a05040204060923091803121314031819050301020403030c060b040c17040c09150602070f050a0e04030c17071b0608010b0c010b0301 75
    0xb1040500f0b41d000100ba0000408460009100806004a10406106510b4842c03012079100c1e0b4129110321884d500d41011500f44107041d4803640c1c0107030001c034012880e50b412411030741c1641d01c032519000c0f20501e09c0d29111102c0144005468008212502040640803e06800e182448a10302107918000034000348150030f810444d002c0190b08690600c16040107035400c0250088540a0011800c00c20418440c521042050042510034a1007400c9141542e801d0384190008100050003103444556904010b410301010080441e80603242400140091030309214031681c10744076540e4120320500c0126030710b04821010304150707480640ac41002905400070b014440c002074074078914204891401001928003509500801c00050255900b0701c043d449044040b8121201190203821948a6050542d07440d4800c3c007010741039000d005802d9a00301e004000800f00240710b00d0640c5002000e2400c0142c040c102d40c0540400650741130b00400a01c6680805043c5009504000042d00c0b044280080d08440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 559218911 1250 559217661 559217663
    0x90803070c1b170d090b0418090204020a0e1503040b010302061605070303090602240c1b06010e042102120c0c0619030b090712023f060d1e020319 64
    0x10070140f011504403001440003003468520f6081503603140c2e0801c00500c0b0580203500890500003003401c1601000100c9030094580e00350094000c43d600c981000d40204070900b1030500ca40500d401050440300c0e108a60f0459100e80d4202d004400342e642142d082000a52102455a801a070506003da000c100203201c441c00540c0b1a0f2900e0180034900880641002a103042c41d100c0c1114164522121031942ea02041e8001100c1c2c014603901d2541c0440c9c5d6101e50146190178040344108400480d0040c150b441807402207000c0e1030754114001c403c0c41d940701110000394240300183c000c4c0315414903001008016003120f10995050700c42141161000c01c80e503401001e40c10710484840a161018141c061080e000009019542d820841c640510090102003401c0d00b0380240c1940022452001584e4456081d805032003e031a45500401548403e00030007001c102202c0401c0800000c60301c1841c02e00d006910180e440f45907a10301a06903001203111a0f807441043e078041c02003018003069802c041d1205d9a00b2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 559220161 1250 559218911 559218929
    0x80411130e060910290d0503040b090a090e1518010f091a160c110907021c1809020f1207050304050c18180a0c060e13090803070c1b 58
    0x36103001c3e0049450702e514041c100e12128034091001e0a00c00c9686020383c10000c820040030b00b582003030404105010000790014015010114010422807e660700030005840212058920980c4494041e4111070407600d09480c2c80d400680951021404100503a0f0b000c0c04001c1c885c5401e081c811201820f441c025656100c03100e5844000380b007006071480d01c1a84035a1213111003850f6240c07504404442071030040c020424031880350710440c1001602062031306600405070034481242000b4401960f81c403180134608241012020004400c1032180c50780301812036407a041c030100c0c5803400d410040294010207908410b000108251041030b03580e00b85c4103010720425503030a9039a18040c05c00d14200010001d40d544501c000c8006452044114008660040e0408080c0b1582c0410b44a0151030030f10144001040340120940c00030702980c01180c450100141614128481c2c20200002c0d0100da04101001344004014800300d006c0307601c2407088504c8240315440440c0314408041c0c658068410541c04a544 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 559221411 1250 559220161 559220173
    0x1051018062d080c102d0503090f01050907140112020301030c0e070512160c020a080d020d02010e0304030b040302101a120c010f030b13060e0a0c02030a080411130e 72
    0x19103410500c840100785407070140c40400310300d90002d4191105c80c0f5600080110342c0f600140c0016845a29403003910740d0380b03480c103400403070640301034401c6d00100e0b400405401040481465000107002d4548a42030940180400c9410001421589065601100e0400c00110320400103030003688000c5010b1402245410074240c0b41c0503600c0c501850080000e400c0141c180300002c5000c5040304074503005030740813415440f8188008000c640d06c5415190180d88450092000075800c28003290346203c000c450303403e071141448000c1080c0e007078543c0d0f030204c3c10a40c0c2c010401040400e1103040825003151081c41601c2035028680c6208003520410514000240701c0c0c5810407009141601c50f20110503024405405120b15042c0044c040790004410103003416181c56014103541d607242d4a41c500c18a4101e804c00000c4d848041011964074110b030703a5031034980307080b0714401c10318000801d0b600700c2c0243c2e40e1101c9541d0f80d1a41c81c2c01c400c0741c1e001d0803207400911541a00e6154050750040d48808580e40d4000d00c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 559222661 1250 559221411 559221479
    0x312260a1506020d0e040908280f081611101a10050d1d01020705010f110c030d02250b070201060603020f09220204030516080105101806 60
    0x4940c10354640c900e0301a40d1610030401c0c2c0e90041082034441d00c860030080c031600c40110215000d025182c0008040060000d1042d114540d860f0590a010a61084028078201940004d9880c01d03140c00f440c1000c1130a11000818071040251041c00075002d6141c203c59600500d142e03640380c15500008040442e46500b40d03101c240ca180054984c02d940125240c0e0f07a03d06c2d500c50081c01310f1084d8141c440880e0b4450741c15081c3c07003440c03103800e48842590400071541c0702d07039900303080f1b008001103654604000d0618000301d102242980035184008c41c40340117186010034001404009500205003640c0306035014484949040b40010407500302c0340616588282c03417030407280090840b030303542d0001000c0c94414400001704055000c00e9403054002990540b81c5840d9030580c01c040c03000401e00f400c3c4540c0c0009404400c200d00420303c00344400151804440e00340c0c40d910264240e48044800b0740b0100c003144c1c410030240002290b0002e10210880e4001050790f12031400c988010600615a41d01c601510341502c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 559223911 1250 559222661 559222681
    0x9270e0703060c02060708041511041d09011a120c030a200d0c05061606110a081302010503060904021c03020106140118031112150103021309020a031226 67
    0x105160742413000d44441c0c50710300805040c26030003170405098100090115036113811564450400075203441803260b15243d40d401032158650201d15500156100c1c135004c605180414040c0402d44070003a00d1010304e400010090003401104815040243d02c659611440e19450600210100710f0064110010b4404021000101000c1d07100e01280200c0406da406404900100700c4102900e4040307510f640e40b003584c0d014800a071540d03500e001d0802450540c5858121880c0c2c0010100ca0392542c8580c1000d658401e44a14012400200a408070700204001f50b698940200040e50003440104400d83d43c000145501208020350481200035070354407035003441080f120352900c403104d4100b40b81994904188544110780e000403484010156080c840c0d0002d0243d50b40c0c2e85182a4841040440d42403d0581c0c2340300e00035160030b21050307002e4000e0344a15100c0414900a0b110a01d40180400c600e1030701e55910100c1c2c203203010b21484100444640c94a80b500e400303c0411184c010b1800b800103813401c04c1c207103031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 559225161 1250 559223911 559223921
    0x1312170708070803010e0f0612060c0c031c0606020f0a0c26030a020c011413090b03120d0b040b04140f040302010b120c100c0c060309050c040507032301050109270e070306 75
    0x14a20550440d0040c0d27520550000f1281e034801105180e654070769071042492440c5005013440f03000350503640034065444610580c01101107503555421100401e100000043d01c5a00d400005447d03240121401d0040e02100e010600e540fa892215003c0d0b07003000960130390300710b410846a00d00180c00c2155415030303540e40500e24507000b6030031512080c070700403035400c080314072320700901c40c440301c00b030303d0300d0741200303542d07020701c010701c00d603080054416510740b0032840503001030421860f074600c12450610b0f0704c070300c0e4100f52041190000600e010100c0d10344488034500703003402008104804540d2500c44800540d200c0b41030410340903192000600b0694429020403e0780c1403881018010401c4806100d004162100320507000c8a030700c1d0030009811506420114145507030010401d802600b80410b102d0503580c160b000c0801030400c10011300e09101001c4440d06841d10070f20032580001c82c024400e02c030003031950190440326020b203203100300131034150018541600c11482c08103d081e08800c00400c18080342d400ac17 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 559226411 1250 559225161 559225171
    0x615030c06030e0c030c06070209040f0c080f01060603020414040e07032102010614010206040b070207030c0311040e011109041a151c050108070e0c0d060b1312170708070803010e0f 79
    0x303401c6e1810a1800325a1600882e03801034803c071555000b00d41803151310650004000d810280c10b4010584850441d581c41c00035400190031903180c4980010558030071b00c240e4058800070710490101001550800010300343da210040ba850260000000000f00d02d810b1007031202e0085a10980c1041d9098000380c00c4464980c4402001c1c0e101e600b030b4030781607030740820741541c895403210601c40c0c1500c90b5101246000260f800c004e200003244800442480300401c2c0602541d041118248a000000e1003401d003030710300c15003110140080910844020345000d4020804040401c60700d01d14015051001502511401941c40174501c5d00080e103044041072014815030707001d44810309210300d51618020303590b216250304c01e0361400c002c011b0101e01e8080380182151542c0030384000034850340c0d40f2102c41c0440c035446482115840c507004180000d0050044145080b51500001001c09014071420007031b00b9035001040482da03403c002c21030300700003840c5040a980a0010144021200e241c0198000316107407019003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 559227661 1250 559226411 559226413
    0xf050c0a12391406040605060f01170a0506060717071b03080313060906020703172a030402030307120306030219030525050a1202100509060301030615030c06030e0c03 73
    0xd841c160b8030220030842c030200b0405609088030701a00f401d0f503540c00003041e400524041c202c1444180507164010307900030070b0102c5008111041c6100103580022100f034850032010140d4002034021411355020310791180c0d010340740524000c0b0580e0760260385003000044900c010004204042407000c4201034810349030710680c040700e0250444c1c940c501c25000080800000c18101b104803001c2040b242c10241c0a160b1054042d501c99066203400703030070900d05070300d0303608448280000242410134003540e40c0c058651580c0710403180700d11201d000c60150700051050b40c0520040084c070002400c1d211204946022641c0d00007103031070442c4100100d82c503110300120000b809004040c4082030001c920100007060180d0b01c070941c41c41d0014050a0341c1082d600590344400c20300c10009108541f0304000b11500d20031a0300110402e005c6e80195000d005401299401034070030710040c400100e0550000344a80f102c8185103000a560345d5810340900d90681020b00003d451b102c4540d402001000358a071140c0c0124 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 559228911 1250 559227661 559227707
    0x20312070e031b1c06022d040501030e0a050f0304080709020a05040e040201030608060705070201020c090f13031806050403020f09010819060e1902120609060402010f050c0a12 77
    0x14002a83d910104591407040c48042628142d066480403494801155400141d03c00d004840c1030074002500111704401e070100340b0310a1262040d1960610700032900c1c0744024503003000e00384070044004003010b20300101d103441858012008500e040202c180e0b120310440081d0307565800d01032020704043c443c2d030140e0700480c0103108080b500307030700901910306890302240c81842540e11400101e0103094103501090081c0280707402d0009280e400300044c80c41c20300030780032520200010814408204170450f0111042c40b011004140312040d00c00841c003020f40246001d148045c840030350360200007000d03031050000c030304005001c00860400300301c2460303080800c0751144455803403c2c80841e1540358006484c440300c80e42c031615408201d6a940b1801113050000c007202d0030701420a41d05054071100d000240d1040c1d070800402480d203980090f178144546801300c05822940c445070300569000b4000700f040002e02406101c840d50b0800c08105040805005840b0030311107078407220780a0070340c00b000d01c8a101000c11034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 559230161 1250 559228911 559228937
    0x5010f06050931090309140904050d080903190915050a0e1909090c0f1e05060a0e091509070207050108010308092403060f09090d270602031207 63
    0x480081030321680a10480e0f08401d4001c100154440c0c0146040b400600d0010000b041c1075000c0c0e21701056990100c000e0450f041d12008000e0320b00c6003103500034850f900c10880d445903188101051500060b17018112810f0510807030781807090350700c420884400070b400ca031401c01c0000c004089024091485040c00d5261079281c52000741100180480c0f280140c40300052541d0f0456001c4100b00200340e000b03002c202a1000f40780601810415210703030701e4400210030000c1804030300c2c00512488007264030000b440781450401070060230f422508000c000d00001d07102112041e00d510481e580304550822294001e10a82010082c0b071030b401418042c115400064180106e98000584c641900c0d00311280585889441f0b00103009819004c407100c141400c8514282c0c8009421405503000f44021218005400550028894040d00c00c60722074140341d009a2040401d64040c0c07526441c40ca800c2101060b81002d0f2407c402d1400341240d1222005a0000612503c00040a540190003000601d0030700700d840c00c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 559231411 1250 559230161 559230169
    0xe0a0b040f03020628092f100e03150406020405100e191d061f091805040804062102160203150106080f1009060320010f05181c0605010f060509 63
    0x481d40300c5c4c07005a95500b90490501801c02817044400d4040d000074640d0743c4100d904402d0350390728502c159010301052601901028010440340001c004060020201c1d2101080158044d010160054820030350810000c596038407180703840b100b480615200d0031002c0001405200d424081d04c804045500b0380c003541405002d00c0210b103c10202d0b028940e4082c20348a0300001460036044115034410109128003880496421450700412500e194540c000b14104201c01c0a041d11304c00c480041c48200104024040240158180b0b00c01c171001c284e0784101c4c8480c00180d00100d03800b13038000b500d81802c1c096401c421443c040240c40303510110700031059101d500d44a0041d1404070b020f0000381601440340c002070403d452081c01940100300e000024007805030782e0308024030040000110940018480399141344254017446050308000303981c0d0b540a1800c592608514100f1000d0020140c0c010860440000c0075140f01005031902801030f6000540d03945409481d41250380e03a41d01c40824050f0902000301c103651 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 559232661 1250 559231411 559231471
    0x5030904020f16120f0f020c04020d020c070305030d1119050a050c06010f0f08010e0c0f03030c01090c150908030304060b0d050a0f03031a0d060e0a0b040f030206 71
    0x6000e4030096214208007400824500520b00d4529007062030602c00c0080c0404402d0180b0165020745072107031240003041d02150b0100c00349030201c0150b0b000042a40043c14a58020080340b420381c0e00060034801001140303030030107050b42e109075007540c00440d00c0c0340b102e41244070b11051501c0d0840d026141c0044550000500c41411004c0c2d000d2200200d420003e2a000308111001d11080c079058600319a190042c01803512200d015401425485010100781514140308549560407140020185132307207003000304900c0704000c861154050100b4050807400c05001d002e0a40e4551292203504030990500b03c01080100d400703820398040080c0460100074030700000c0201c9820036001080440c440c400c0c1350118404a8206200030081d10500d44500d06000c1c07100b143d240d01c0e500c295414006a00c0045229140c200e2800545910a0a02c0741000003d076250740003040c06001c400c0cc3d1f8000100c5070303c0b51503202c44100c5058501c90f84441c4180b0070554103200040e230210000c1044240c10f081940c1e0780c01525 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 559233911 1250 559232661 559232677
    0x50604080d11030403170c04030302060f18010e0303390c03070f030c060617250909050f120f0301050f03120d0b0f0f220b031504021009030503 63
    0x2203000681a0841c00c0d054024054911140380d00b596282068900100800380d440741c45600304020714042550000c070f2100f02c0303040701d801d40c1c02080c0780c0d16115071411040741e010745198010b40803040a003407000b400303005503046902014041e544900c0d09281c140640d852604040f411100e0043e1170340c3c002160215050313030714241d040c28280c95020154040d46075205610000d049915240800c1c400c00d94071000c00e844403846902c0c00d20903142d0302e00321803544507440182c507541e5421201100d5940d10040c3c0400201144841e01c0b80001c0f40c0c1c844201045406941c030541c0c664014000c9040396860400000341e6240021041030f24059000190001d640818010f180c4109144ea900300c42039070301004241000d1104c070359a903948102c41c8540303100130500c0b50a00c0303000c0c0007051410720703040c9401d9510500310540500b2f00c803251081c014840d6042d20b6540b841e05c48a590f41d5040d2900382d1410018501032000345000801181014010081680c00c0c1180200420840d444148001800801641e940d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 559235161 1250 559233911 559233923
    0xf120c050a1101091b050f0433090606090e07080115110f1e010e030403050c0409031e080a060b0306010903141f0207062004051c0f15050c07050604 65
    0x51107407240380500941350b0081c0c0000140004c40001c564041e660384100c0c3c00c01c031550410039052000b0700040d80c640040e0344282c6240d50b81c108a0440c00e15110f180704c1800e4404e541c40141d00d43c070820089a020750000400540d1829051144c4410140200e40080042c1403161044d80340c214240610310303e443c1c12000304400340301501c810141c10480d0400e001680003e90300410b0060000079001d504440c03041c9507640c01c06400e61401c3e840801247c05803500b1001a00102c030a10050002410321158100d007000b0091011507640181340784050481c4c1e6007603942e842e0906194210409640003034000292a900410901030a80e801c11450802c03258444800c070f8910340e60b20701803410428511b56250728507140202d0360b00c40b105994003c00b20b40340b00345030030001101000e1148960064060903046012002c04c000c0c021468514080107803200c005a03110001801c0b0750b00d1502c020000d4000322003024800ba4801c404113030074012281d014510343c214a00340707852529203640d100c9003c1c2026204d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 559236411 1250 559235161 559235177
    0x6160501180c0527090a15090c051207030c03050606010e0405070516060e03070510060b0405010504120203100c03140c0a210b0619030c03060e06060307031b0f120c050a 74
    0x4c0c1050b00007425035580c007080903480c05460500386560301d41040000403a011208000c82c03c146107150f1007010104e0340c004000c2c510483c1010140300c801c580300e0421410754400c0d1080040001c00d02450f98001d144904050a0305041c00f4001500e1510b001c4c00c120310841c1000304212280360300c031041d503055041040319000c1390109801c1c000010030800d00141d40d9404001018030501000041c035001b18560000d0400000b50f803903080c4441d0340540e000d05070005d20700b0002045a1101c400000c006140020140ea900c0d008007407501e01120000f80c403000110307841d89400e000748210400c186500c59030030b010b520701c2d255450500400c008080c1507540000300c800d018542003031200c1e9004c442e03004d074082c1c0b003070f680d03400891942507400c0340302c00c12800080d0800e9004000b55200b400340b541142c0420010f05040e440b0300e410402c150300300500034405c1560310f81d030140c0040c00d6048001120162500c1d492803a4000900c014031803100b02c0082c51840342445120138000e5401001c8818010042c40e001c42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 559237661 1250 559236411 559236439
    0x9040f110d051b1801060f110c130902040c020a0201141b030301080102130909050c040902040221090c04053105010c02030a0f030e0c0603070e06160501180c05 70
    0xc501000107480ba100e1400c448807004580780b00b4507450b290407216a4100d03004540020b2201c0e034240541c500050b010303100048118082c1c1a000102000c05050f07444800c0c040c004101840c110340c43d540d00840d140c8403014250308180c420840321003568405841000030310703000030300341c29030310703000b280001100003004481813044003145910001150280c0380e4a59403030304a60f0103500500408030a44000d00000119124907105400c1501e40c00b601800129080b81c04000040401103026a00a80c00b009842010444000b0802800c060f030b0f803030b0034414201045038502e071000142e040340c007451411041c01910140841550720107003600c014101003280e40101d850113000740380c400414641c2001c1d00e003000c2c1a008400360090610540ea1211300e032844040440c181c48003110380d2001600440301d1034003642083c000565004407107040c81d604ca1020f150201d0f82c00c0d4807084809030804100319640040110a005072035050b0f0025810760f00c00c0802d0789a441d0031102030b224962190340011000d078 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 559238911 1250 559237661 559237669
    0x6080c0702040f021207021c05131203030c020f01020703091202032401081504021e0a050604090204092313022205060f060a1706060c03040b0a080609040f11 69
    0x60a226800b07403040c8030a00c1414040e801035049040104d0f01200034000062441c0e2000070740c03500360171410180d00c401455500d42694550720803100c20b071600310510804200101005000c51410341700b9074000035410075900c0c0081c10540340c00e465204990040000f400801d51100780390068555004030404058440d00c00030385040b401040d6180c45c20100c092425105c1400c2d148241211444000d40e0b0600d52807000215035498200e030b00a601c603074a0340c0e00744c0552000c078140b01c1c00711030003500a01e05a505d8400090017a040340c5e1044203036030340001c0c1c00e108884c0c8038040c0b0216015000294408030501c081c241804c4800200601e89411103a04c0020940d918220030120070201c0030050140900414000701c09070408036006402078035800c694602d141403200c1190210782c3d0755a0388401460320203034250f40c1c0710401b40c00107600c0740c001d0051241d000030510062009007500d80070141d50b0640080050000039008064030700c41c0d20000c1c00c10020500c5003040c1d412990384003e5406103208100001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 559240161 1250 559238911 559238917
    0x90303070605071112033c2e0e040602160b190b090402061603030b041406010f170703090f0212030301050a061803020d081201080601171b190e0f010f050303030f0106080c 75
    0x40313120720287d9050001110b0541d12107900c651403c002a140005200ca00da0800348003449804483c0350042d00041c08114140d029000c882244192150688069211031012031000d84102803d50040c1d030218500100c02d114804020700c00b5076070344501e40352540018038940030b40c8100c100410710a02901080600c00d81c00300e50f030740400070f008010360b5405070100d8100394401ca4000b030204003a8554011407a0140d810040c0e5018000032040c0d9660312400121701a10100400b1107034041841c4040d8010b0340d80000003d40c060301d90005544075807410040005510065008505001800c201e0b52410807102c40e03d00e0a894055801000894861807c2c006a10580088248034290b98002140710140851605e0480d07404640704000b54280b202c1441e01c440300001c1040d00d014002a03c00c4a03428082c2d0419680c030400b0306040016a914409030104030b800f16070b8100d1400c08071005001e04040a1f404a002c0c10301500191304600e015500081c10240601400081c403a600000503400b441341421 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 559241411 1250 559240161 559240261
    0x613030c08130b130506130b0c0712050307022404140a090905060709050114040905060612011e0f031a060411040b030f13050d0509030307060507111203 67
    0x244005580c0f80318101141c3c10901a0807110409800001800e1030302c4400c0d100c540f12840c1c01920750b20f02d0000c000075242c1c018a0f6a5045001d01c00c070001e24001c04603802120580501e0141d03035515558810001e14992204402c00300054030000c3e60302c0000414292805d45100c82d0b800e51010b021880061140c0016610a00610b4208441c8104119010400d80c1c059078003034860980c0d8980f11801529a100c1300321a4914070a401c0c08204090056034101c0c5400c5035001c0d15440c68004d002100c0288880245c221a110030b950781100c24440d07a040c5001c0b00106850703801c0c001c000d0f0959036201d4a44420413007240d0310b0341c1004041005966198482c3c2d00303240300a14a655505c1c0d40d0000709506400071100d26290a0705c44001500041ca04011031031890381c080007030000c20b450040b01b0750301ea030000484250103200520240c0c0000f6000c1c8900c501034030300d44d15100c0c0080200a56a403800c0c50315003c04030f80820500a0140c60f42c010b2040d40080c01c0e4524200100c0045100c007042d461001c480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 559242661 1250 559241411 559241437
    0x6030f0510050601032906040e0408070507210308091c020c0111120307050d09060c08060424120812010b0703021501030209061e0a031506080613030c08 67
    0x40190412000050540c2550500401440250303999001901120071940311002a10100b155964002040c652001c02c5042d005001f5800c107038680c5480b142050301103400301c0d50070400041020031300074200410340c000c108464981b82824004c40300a600304260500003028040c00a0224400038803d2040e4440d1810400012105da024403100a517954241d10410380071808803460f090b01d941c3c0108000150a074203503800d034956183c6920850301907000e14030445486e03680c4d02440002405a00030720703c1084061740c034800a820702200f00800c40d10100300b40d513001d90a540c0083c011a0070008814200c1b106d11191000901c0a8201004036200b00700c080f030420117000c000820a81000406084100e00076402c4551400c070307490102d80043e000f0702020358000c6040340040c2651a2199422300c8028440021006004004000c181500d11680040300c20014400561508000d07a03c02c80b0700a10190300100490f00700b0604400c8144402103002d0100156194403100b404852400c407181c451740e140c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 559243911 1250 559242661 559242683
    0xa02030c071e050d091a13140d0501290d05070515071505070e09010803030a05040c03061401030b09010c23310b0a0203160c0b040605040305060906070f120603 70
    0x500170400c2c0c049005002594803103144145c0c140650005450f070700401180c89140c020704003060012800007400701140c4c0846540d41c420002042806204841c0030890b0b58071b0a10718141c0c0901403001c0202c08054018030800c0200300c0403450016080c0121107066507440c0c0050346e140100c000d0b41c89002000b91140c00703d07401c40d5894030341e80d81c40f040c4500015524100803d0b003181c20452550000c1c800c00c52540d00600100e0b402001592009401038400c041242c007450360795881c48207481215200110003980c00b40100107000c00894078507071040c2240c00030041c0030190f05005c7d1980a070b103d00c00301200321040c07607101161240d00880d045225034141c5002a042441c40d1203010240d5a21266504200f0b40c00c00680046424242e6111107040c1d00035509000003002c0d0204120f12040c02910b0403c50380f0000520f425100740100050242503807000c1c1d0351400c41c00d1551034118043d041103030380c0c0e000d40200004103622800c003d5100c0c45501e814010414804814070290056410180c20890f000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 559245161 1250 559243911 559243933
    0x30f0210060f09180c1a1c0c080c0c030a0503100801060b0307180f0e060406170a060e030708090616051c08060102010618090515100e0a02030c071e05 66
    0x1402034201101c8a1003030500c0304c521205602d0425503140000146015081c07082880102081c081044280c007071003100034242010701d103c10700030440d0812850b03221503481600e0000c0c0ca505c00070083c0d024040081c59498503080707200131540da1040c1c0084008001011012450b124102510b0038001d090a80080c09507546a0b280200d842e40f003912901302183d40700700e1a602d00d10b25020340348100c070300358800c40700981c0c941180038024000051000f42c1c401d5641b01c020890103081428085000500d070020001045036240200c22611800d84829840c1d009102c13480004040400315411698183d4003d62503014000c1e510043d0512034400a11600a8455018a01d94052003a803031840c491f03644c5014070b071248001a8201e443e18024420032803a40b05000c0d08000c02e50b04840d500303500c258102da1042c8016080041c2510701941c480e0460403d040d01000071103150030f10183c1200d0030744001c61171400c181561488600c2540e80040030800c440f940c0900d03400a110500210b03580200944005440c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 559246411 1250 559245161 559245179
    0x30106140913230405031204030302190f0e060c0606010513121527060e070e0405070f060206090307060902120a0c0807080d1d0f030313090501060f020a030f021006 72
    0x11035a102c850020520707030311250f441c0f85403449070003540c01c407001d146010b00c103c100c0302842500800503810b05030200940c0084142ea080c801c0c0e943c1c4002d503200e0703403025400c1800504903040ba00d591803003072206004600717144d240450410b4004d00c003424425a40d000c03500342c000b0040c0d410317400320301e15461404030399052282204c6502c501e5030422808001403030251081100c940a414ac0c4006c5031000741d00b4007000650a58480c084c641046000c40e07400d00d039076000e0030b400060201d808503410307000000100841c50120400c4005013585001803c01458041d4100c0c1d074034050703050064402601c0b00d60410035503d40700c40c42038402850303c00f6990381102a0400104401080c402c02d1814400c009000810f44000306050009040b10b60f183c4a01d4140000491000d1001d4010030741c4c00406d420700e49882c0e40d001c10081030004100d0384090170942c980314805048900503801002800744004401d582660b02050721005103625040940000c141a2001c900e0098980d814000c250300e0981c0210700394034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 559247661 1250 559246411 559246421
    0x30a060e01060c080306010c03140a0e130504050a031b080c0a11100c06021e0301080607031503030e0603091005010b0909160527040f0c0e010c020303030106140913 72
    0x15030495400840c0c0d0342d80004a40c43c04294601505003141440400c4107503100c2c10411040b28020319280011492506d00c01c90180d00c441e00503804a813450400f8065420400b0003600c000c00301040400141c54240c03201900c0e03000b0500000c0c00c00407615102061003800204007403e4039008041151141501c030180359503460300c440250791044c1010344c0100c26203007881900071040850f56400b5071849030790b80c071030010750060030f05040c040401e203001d100e0a00046024500a2100e08010241410114005001c490f00c038104500d650500040a0010940143c0c0d04450308900b134038006d5407540c1e80100c2d076003440203503100c185401d4180400010101119000f4203d0028200d800d40c0300c544816031606c0110020354460b9010540038002211a00009420f130b0031314440042d00100c030500200f0000e411208115150705034150380322080b02c80c4c5a40320000c0c504202080c2042030b950441e0f40c000075a47c3c00144a0101040800d41c55105100c59030000d80e00e0342680905800500903951030601c020342 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 559248911 1250 559247661 559247669
    0x120f03070c0303080f040519030e03030304110a0b0a0e0d060209120313091b11030705010c0314060103020a0e0f040b060301030f111c03360602061f05040e0f03030a06 73
    0x1600070f40416080c484550b2030a008947c000c00822000c49800f50f41100382c080d003401034090100315509450562014002184500d03c10051804902e800c0c2042201e580090340180460840600c101c0f0580e94024800d50404002151010400c40c1c0503d4100c0180c0f00320010317590020304800340481c80100010190840311405098030090380e4640d03004c542190458403190280f00082c1d0f00100740709000304200480c80382c01c2e2054174074014140d01c600b400d40c1c4c4401d10300f2001030f80d2202600725600003410115008103003482d09601c0d1008a050080500c2c009040180c8284107110354801d41e903a41d070380000101075003c0c002c80d4680d0b0756030821040380d040d1290107480c42d41810305014840d2030581c000300300c00000c50140e949520f4280d1803c40b4000d03440f0780e069201405012200100c184e2050440c8201d04040b0000301201c0c0c1040c0d402810000064143d0354031507803414100124403040500182580d2041d200014011001c078040c6151450007583d05403180000410300202510702d030003400507a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 559250161 1250 559248911 559248917
    0x30f060a23010e01020c1e04111611090402010c03110f0109080c0705040513080304050102040512010c032d0203060a051011070b1c1a03030d06030303050f04020a05120f03070c0303 79
    0x100d0343c58005a803218001c0003256402800c440301c00d6461100c01c1c2c449050f180000d40009132483c0d5914030002c0c240e01c200c1412240c00c101146010420034298182c0381103910650710308199080c2a40042d04481c440d41004041c4002c145526a016a080080150420b5171000070700103c03015061142441e44408603040e01c03401503041c08100342c1854001c481c000e148a03100300719216042c0d141d030f00329a0009082101d02e55000c2000084d03a903031390448508aa11407100000b00c144e8001d50140c100c52901c40c100e42108040301580701c2021a01c580d4502c445e400c00c10141c0d4030382c1c5100c009409480160042a4442c12003602c0502c402c0d072000c6101c07248502401200c4042c0d4071544210b48600842107418411070480046549081640e040041f860000106003040f06c1c2c034400000b030031a004480c2d0603000360ba0302c4030108281a818002e10740c0242c0442c0f152400c0d41456000300d0f00e8044a4080c0a000b81019145005413010030441062411909801d50781c440c402032a08041d050040d100035000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 559251411 1250 559250161 559250177
    0xa0b0a15080c031c02100507110d1d01050a0509090c030603060a060e0c0a0309020d20040e0709020f04030b010e1501020c100f090305031908010b0f030f060a2301 71
    0x40d0540c0040e04800349440103009103079a80034509004405841510500c003140a01b804035561603c81d8001d030b13170203010180c40c0e5400d00c5d0410000c61f4a848a44800401080380384060744200c64a0002020b1101800b881c0c000e94512514000391600e01c03a03880c6841d0440800010020541c080318055409600f0403000d03164a500e4080e9841c09035481800740c0d030f01d050603000220b135510070300500900014105c0e044c042800010b60700010410460401c081d5494030108001e10030210b5428800100c038001244c0030084c1514085040350b07070300c240340141e41c403c607400111000314002da401903400440e440100c4000f2580c4508034045880341c05d54403031600b01c501c0902828158000b03d0f82c00c1d08408080c0600f084103503102c0d8100d822213680c0418106003c1e01040100106070148001c06281c004076428010242800340d0041160354140e000c3c0c00040c40512102e03902d0a200000c40386c03c01e900b001c190f03103991506000941004207030390103595161300031001c0301d815807101c3c0b40090441d00c09880f6045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 559252661 1250 559251411 559251419
    0x903010c080103030e04020d0e0604120806220509010209030a060c080a06030f06110c0307050604021f08040803061c050d02060a020c070306050c0702091315020a09060807020a0b0a15 80
    0x90298001e000041c007140c0013107948022406c1c242d015010b160f55241c0d002c901c00f941c010850b42001d000b070360103130340585281c61011180c0c1d801100344c0d500124280e50355210b088040c507880e17442400344d4200c0e4007038035151800301c3c0340d801003501600c494401c0181034846212492400f0030040645a2001c00030032020000034900683c0d1b8410f003401c89403c2102c074580c043d6250b4400f801441c10014140b03e0303400a024841600104001401406225900401e142c0c2002e00420800740d14031045819070920041003600c00c0380d409040755800a41c8105061f849440d2480010342914424644c103030f00c800c2d03450440040c0280001e01c541641459026641191141d407650360607441060084001c1d540041d00400004280354001a8040c8150580c02e0500220b5400a6501074054034079003c2000b40341c4141092000c06400d404211540c01c00861a00301009400b03007003100c1c54803500050103007020004040178000e00401e01595449203018002e0f15002c40800004c040c4440b03205c44040040d00301003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 559253911 1250 559252661 559252667
    0x1d01060810120f0c09110706050109060303020a020d060e030a170f071e022401030312020306130c02100e0304090b060c0604060b151606110307142b020903010c 70
    0x14080c1d4251070b50700c188401641e103820030b404922000444104022583c0020403a180f4800c0c0e5200501180c0e405982c0c14850030280700b43c441c180c0000d00708a280400800010f90005401c2d00a2603041d10741118001d0301e030400c08010030708202000c0d02c5000000e08a001154014071107110400a00c420085070b4035455520300a04800f1140e12002c80d8406e050120304180302c08441d50181090310458240203e83c003491122602c21003000b061402400b40113008158102031000e07a02034246108604501e0030500007840701c00c2c0944451105543c40e0842481d00d80b09000c881203590740050144071705181d14001a540341c1c8244603c9002030b2403c5080e840c82d207040005c03508d20f000090001c1917592074036120078005000c2802c903d540f0441040e0200c0c000455100a050860000408546400a80d0404070180d841070607240d00703075039820001c00c0202c41e0018005144820030020188d140c4800001e0030301e403501c8040c02000010030815410711101c020781c000301507a5a041d4001d02264003100c10036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 559255161 1250 559253911 559253941
    0x109060c03231309060e01050d0b0105240c07050a0605210711070602070608070503090615041d0a12050406050d240b091203130608101d010608 63
    0x300026007503100210710401c811407400d085400c25084503d400b1008005407104445a4403100a2544664041008a5401440743e00511060710610f414a45a5890702140001405030a00c04c40302c1d914074400400c08a129090240007c010300c540d180c200c4105503540701240c0c0f103110300c00e0181030720104030b403031251050f14502c5014840188d41e20411480e000d40620008140c1d10800c01c2039401844505010131410008080d241c010740442820100c0003095040c5c000c2c410020304c10108140000c040c40004d507150310101080f05416003200120025029210000c0f085200810b00c02d101c4081d04408200304070a903104a18859500b0080182919103024500c44c04000ca80240300d0f035820f0420b0343d003080c030880340420907401d101200c42c1c01c505040b00183d081441c5524001c42c201070141440084000c040386040020b608001803e095100010b03128000c0c08200a4250082104000d00c05090b90203004541c50000300c0174848460001d4002091080c10009030724800450708550444500c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 559256411 1250 559255161 559255163
    0x121510020c131506050705060109020f0904020c01061802181e09090307080304200a0302100e0f15030618100303141e0c010f06080601050103050402060d0e03090109060c 74
    0x151880c4a500310402c10002904a0800d06050b155103042c038695010307050700c801070450b64407603130345411880c03c10781c1c81c21a058221021f854030401c4a030105041d01d400b5a0242681101c01603910070300007503010301611150b40f050622100002c41d16410030100d40161041210020a00d801400d0340750030415a981050040c40641101140d141c0641c10075552659100403d8021a80740a0603030f5102d15103076000b2103090b5101d03604054034036840d1640c030340004c0c2e6040c02200caa540090854002480d0001d908401d5014445590100c0d103d41e103a06550b200074000040000140e5440f40788134030f0306039100f11041481040e00f01180c4102d044828400341c01070403601c00e9140b64508542c2d099a502c5114080e052105009010b000180d0450b00122907078401d211080344d8840b007621901c1429107860254034011039090038414045144001141030444000b40307004600c039100e500100321f00b4070500084580c3c050034001e000300c0911f0008001c041d2008203036205050305070f6581d41140c00c05601e9030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 559257661 1250 559256411 559256413
    0x1030803010e04082205100509010f1b02150706061a070f0f080310081204030b1906080615090a021c050c04080d18080601060c17090612151002 63
    0x10042c8580c840e14084a41e0151180c01050302d08a16003042030074020101c1807080d049009407030244121308040380710340c41294660038400e0402c0d40b076500103803e11521444507000c0011004411661116201460703d81d15005425138080041d01c540030f05881c0d024800c1074907040d0a042c0001601e48091590b150705032070200e421410080303540c4d103503a258220418241d680600f46589003020481d101c00450013180301e03080e1402c5051130040070600b4071801e00341e805481c1109001c2003000c40c2241418560100c07400324007200129800341902d0080c0001e070410354841c8101c400b000050500100e00c44070302d4500702c82c5c00c4142e58546442009a1180100d000d50342c18030200210042c4225400007904501019511814941c40d081c685140264009494002507550302c0500107046c004156000500b0390400a44031560421070082d1008070758900051298643c0b200021003100c0c48410388081500041005030780f141c03400700510540c2c00c00d5507171643d0420000000202407515500d440b0f50201607030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 559258911 1250 559257661 559257667
    0x62203051204080f03180f010e07210507030525120303180209070215061f08180105010e010602100c1d0301090212161202151c0903120b0306010308 65
    0x10003000300081000e8022140c1e00020304c01d03403480205940140d03105100030b0030006594014108590f00c1e0111100c4c1400c0107902d404802c0710b02c80008501c2d101175804600d81a040700807440009550724160081c041d0190240300340102c1004400300b4041c25031621848810034642c017501d0808000c031664811030003a41305c410703e440000380c043e41002d14010a40200d1104002c034540200f00c510008a8007134005070009007000c802c1c404405002034102078203841c9070b070345881000030300c81c8d05640c07040700c400c10300003260009010702c0850000901030183c000300900c0107582d06c0f02c480024010a009071405070043c19280305541d00075104550302d0212654825051034021038420b4480d54981001c680c155413140d11038400350302c94406100c240102c0400800d442c180c04650b820180e10b95401030408020607400c088096a01c111010390204210001d056659100c0e50002410402030344a0310350941c1421084800d041c1c010200c0c001120b40c1e5107003800068000f508140e00d0324001d000060480c0414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 559260161 1250 559258911 559258927
    0x1050a030b180d03150905040807081e070609021003020310090f290406080601031703070c02100207030b1e1f0b0d0f151805040c1706220305 62
    0x64181d600300303102c0c0104404a05039141894207082c038031021100840d4a8100d07071604590101c400030005c2c10320800c1001142003a5503194005e01c509a405020014089690400c1030b814001585190001451060381d802b11442c0010143c040b00100b80d118a00d29031001b220207029000312842500d40c25147c80000782054241d02c0200b0303000042d140d0741a81e130f004803082c042d200a040c0440301150102d0303c170084141002c02c010380380560401f120a0b0841001040010310300221030b034500320b280800700e44076600c03544111080580300601a50000e460030714801c40c242c011030041d0039079019034a640742c0c581d50040038900218024074000b80703018610b4000b0b000c0c560642c3c4400c40401000c02101c131129030ba00b689210640060b0074041170780d07903150f10340c1c0d078110389505c0303640c0d414240340000e80b0705181b401403920760080c915115520101d446000250402140d41440b82c00f071300401c1002c60301540000c0400e55180c1086a4480c249808001c4114150825030b0000c40c0155055480514040c50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 559261411 1250 559260161 559260173
    0x118050c091f060806210d0507330515101214091c14090409020d060e010207050f30091f020d0905240405100201020703020f0601050a03 60
    0x80200601007403000c100707100e8804000b0880d02d00080949607a00300741ca09120b0100402803500f02c644010311410b44100c24004c0780b000c51aa500080c00d030030659203d01e61424000c500c403d514040c000041400c040310307000c082942c1d04810b100d101a260030030055a89610240c0c5500000f01c036141c3c80316201440f5003210340714090b498180c8083e4040810000815011034002b10420f64408009411602001603180050580d001c0e0310621403511005c69602040c40012a12401400500640d102e404080a640755044039070f5080e40d004804014449a90765168001d40181c6011169030107000c421000101000401c001e244280026048015551131011460180d600300481c04151051203101e600d555000a03440c511782c40d50114050b030544500001382048001d000310401d100440030248841e80312005004418016615148050341c2604a2080c0a00841d03001c254003800f038602c41c018060707064000c0c00d0250300c2502160388030952100c0c3c00e526600c090003000d412240d002e0381040400c003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 559262661 1250 559261411 559261429
    0x40e0705040e030c0703030c0b090a0809090a14040602130b040b0406030e07080a0308010612180312060b030c19080714030402210d0816051204020a0f170118050c 71
    0x980c007003c4919040e80e00ea02d507800c0c8a0710364000e901203004040039005000aa1144940c0116902d0180c00f40c0c45480e6100108d07400740031403990158a0010004501c030203268440c1d00766403e5003002e8615480c040c580030b0081cdd80042101c04d40079100000004610301b0800c103480c10f6171490107140d81480e05001044001f822500700e02d125034072901800240901c0300b400310542c0d82c2e010b6a00e003082e540c10030340041c201e034220011b0b08940c1c610380031100300500b46400324900c9980c1c0c18500590150020410310010b01903d40210001e5480003003071010050310040101450060a500641d5503107900500780c60320301d01154284080368081100d04442549180296803151000380300c030b2152070015426001c00d09112540790a140d124800c3c1e40003040c2c0241c9055440132504603022080709809000800c03902602584140c02050040880c04540e03412076201c000c0c2076103800c541810703603842d107509200c1040d55103144c07181e510f03100040040300201c064081903d50028001c0116026074414054101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 559263911 1250 559262661 559262681
    0x90b0906060906040e0a0c0f0f1b05011b0c0c06050915030c190f11120a20121b0606092212020c03011b0f050a0207050303070602030411040e070504 65
    0x800b0130040480d40c5800803032034600030041d44a000404038000c0101410301e0b15030f02c06030300034028401542182a9402502c0110781c47d14140c2c1e00800c06e030309182150240c0002c1001c0784410001d40c0814000aa00013000c450302c07401a11409900c60f0f4604042d1f50501c82c0d040002d401c10400d481c03100f0f20580100095821608170074045183c1540c40f042548461012030802000810b41d1b4440c2072515445028012000b400d80040c0003c1034600899a44030700c6214102c0051000c00e000c0c10510001042c0358141213030f191000c0c0e8001c082e14041141c202ea2051142d0341880c000402640082c00001881c184a13180150051105e0780711140443d802c1d030044460070102d40321100011001880c00c10000442c00384d550000c00c003c41e0b08408160940b149451650000602245449881640308036404284084c80c14000c1d136402282500300d091601e550403803500b5100028450080160f80d5004610030380c00b5611480c082c0c00c00c0340420043d1031004044108079480343e88284400c1c44c02e50f1001e034110b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 559265161 1250 559263911 559263919
    0xc03010605130503070603020904140f130c0e25020f060a02070f0c0b090406080307120309020102070305060f0a0506030307050c0f010e090a0f0b060a05030f130501050a0e07090b09060609 82
    0x52541e0b40002407400c510b1b030300b0910000e40c0205541c001c80c2014014170188800320004014180340400d111048100c0c020040105c402d0380000140c2440004090100134200541c0794110902e0308240000c1d43c1c020030706100302c50030b5070035402801035440072840302446d490007009002035403220a84c12000e0f4220030743c01d4030031980500c09000003544008103403000740914a03015072141e102d4401c100841d503056100c903c6680082115400080504d5007044102085050000d808126400101d2810034143c00040544c45104207000100c8656850203200e840024400d0065179141024140c580c0101c820040540e800102a00402e10304042002c902d4141072400e040048503240015600c2a4259030686032655280c01d00e0401c03030024020b0103040703441900c50624108000b0001800d5100041428a600c803c1c800402c42c10f1042030040b48417250048002d000d030b801c100e040400146192141d02c08544144040082e9583c3c0900500f2030880000703140c06031550f0f8003014000264414007407540c1c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 559266411 1250 559265161 559265197
    0x8090105040b0c010e0f0307050303040f1b0303020109022704022416020a0f0b0f0307021009050c030618120d0905011409010612170a12051503070e0c03010605 70
    0x2054882c04080c11402402500204510071140141410288407582c1c004240d00100024000300b24000b044a4000e5806a0803441070b1a050504a1005045401405443c01c3c0c1a00010905a054000080c01070088584807140301c00c00d254000100c03071030045015844005000200545001d401c4004990310302d1030060785101c555014045d80341e0001c0c40710501078220051030700a500300400c0c4d60014011048026604500b404059101c038054418158051440040010442c80c0300744130498001449040a005003c83ca1500f0340d100d46010340064064424040011402103c000c010789190071140081e01d601c840aa01d05000c070b500c00d04003a100030707459545650028400344035007545c0800b8140201c4180c202807240034203403900d41d440080c004042c4400708000c14007005680242920000d8103035035034990140d054451150300380100514030300d00301c00c0100c40c0d201c420704054100070031010b4810403610b45442c0c000310102a1038080d414201800180221781c012002489030008611034421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 559267661 1250 559266411 559266419
    0x5090303040c2c070903060e0111030613180f02030c04110f07030903050601060305040c0801200a031410061b08160302070801020301080106090501080c01120203071115040b0906130809010504 84
    0x208107021341d06140061710703022041090015074415804140b034060001d08c082c0340c41c098007000718000585014851800c040c0b44107032101e402da01c000416004240204045581410150205030302d40100340c0c06802014600d6410389024032070301c04071028102ca80750a0509408055206422082c07045050202200022002c1101049498001c0605507008038140c982854003049407821640b00403201d0f03042106102c080c1e25816003400c28400c00c04146030301c903140d01c80e04902410884008240782c4d4a198244030120003c000c1c804250b40e565140c085444555210f020007004582101800078017040c41a4501e02c26840d00c0310003038074080d10460707840030707250301d121804c80e03000780e00030503a0360b40d514030400c240c0016016860040540401521841345c0710000070300201c0307071141c0c0c403c0100c0d4000000380c003550141c02c840181848000803100d5411444a6000c550381007540c2c1078444040403c0040ca018400045880c400c650a00703000396002c980c1c1e510b120b0240c00081c2d115060080503c0049 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 559268911 1250 559267661 559267739
    0x1106040f03060b0109060804050a02060315090412080106020a0803060d03030603170a030b0f060d0f0204080a0b0a050c0412060b0f0402030906100e010b0a230c07030605090303040c 79
    0x10041c600401d8000751000c881c000140200006034400d00520100000300008240049840002c80d60107513021540c1b55070320714441c4a082c191800041c0d000c070000303050005002e0382e400100c4030f050140d11100c1d2166201c20080c0d03030b9030700481c400400390a4104005843c41c1080c0000c074164511a080c00b00e0307265200d65a039a40c450010030400064900424080f184640c98002c40b400d405064420380034420b0300d040030038854407619810560194840400700f102d80480e5040b078006145040a130388001440340380c42c984291045e40c2e03600200c1c1c04d00b00810080a02001100e040314401066903060030000d6035000c014103c11034410380c0c4182c0d0500540346d40d80b1a4002548201e00d520060401c03842d11400d854403e007603035000201051006401030000e5503010046403001c10060900005c0c103036002060031210014110710b9015514041019103203c800000e0750001e60381300e00c9040c800303a1b0b0358012203541d030300007107501130300c52480c581c002c00100c4020341d9603401549104c0200001454150b070a8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 559270161 1250 559268911 559268939
    0xc0706030b040912051c050105011b030e030f0a0510060f0501080702101e0f0c080112020609040614150702181e0c0c0c010201200309030403120e041a0d110604 70
    0xc00c01003040081c10351b5000328801103220103440220010803595041400003003040203030210030094070240700c56000a050080420644201c0d00034101c901131030f200384419858400107130046449200d1b00a415002d20a05e01810098844862580d46540c1c40c03c0f004450f4984054902415802102146601c0d24110b0007101d010300351854410318008804802207040300c00d20b039942000c0d1442c1020f860f00c16640285d075181140c0001e001850312100034000500c40d8890581c2d51075126140440c00150580c5484010903030b104200c810410019840c00c8101e228440c0c050029840000803010904a0b0748103000950003c82c142c013542c40900c11100c00c40d2803c4425200c1f64801800420f81407a00e04042088030380c001000c0c8020700c0f1000c1000511261105e0602442044e16400310000c1c002400c100141c60096810600c9550800c41c00c42010b00a05080071109004604292405000480080d050300b003032080070b4590f031011a030503282d0a820140b80b00d00c4c143e00410030440001c0f5508034801c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 559271411 1250 559270161 559270193
    0x50d03021e041509120c03060b0a0b031302030601050109031505101e030b06180c0307050913060509070f0203180a05041e0f0e03160804050a1701060b0c0706030b0409 73
    0x100386460310b401d00068504c4019034058208400c10170484000241c0d61075244013180d074807200210300c0c3c2c540711000a06003c000e800a4803100d00c00300c200f086080311b0841403d49280207409071000d0fa622078004651203105400042c04050001003103204480e4a40d110541c803200360710000c41903503100c20941011814840c4c0f042d41c00c100c40c000610500100390b5815800c40c01c101c41c00941c80020700c3c1c58902c075200c001c000e1010b05030040700045c4224000c000301e1f110070000500c101c1007034030507488040051a180c0940c46c0071b40f06110018080318014030300b00d1141e0419400560402038503101052001400035250b9801120a0400003983c0d180d90082d00f1450140074148085440d0106c1c1d00c000301c4003004102d4415604102d20760800c6500070046801e40c00d010381d0b402c902c41805013856002482035521a9811403000d00700018441030062004402c0702801000703200c1113650ba0b059141500900b02980a5600200b001300700780c0d80603a00c21903611002600100396042c41c0e494074000301c00c1e0001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 559272661 1250 559271411 559271429
    0x1213050a03150c03020a1205130b040c0e01060e0604120f05011b080a1112070903051b0315070e01181e051005040b1206030a05100209041503050d03021e04 68
    0x304410b1841501900ca40d02034540380450408401d1840100f881d01c0ba0031803c0c10721651440403070610b4800c01c10f0004001c2d0080e04274400c50600e450032184100c524411010901e89440001c900184140e41c0d100001030010300050500e4200b10520300c601e1078040044aa81040c1040030000a20a0255001c0000004500140321a4207480030340031078001407108032070f41c2c51b00c0e0500b0b01210a000980e000f4260506038928030341c2e03a0f036809458181c2540c1000c1d11078810300c07003141800c142c981c4941107441030a400381c9190702c4414098810300c08003900d001c0049220b1030203001b21544030746000100c0801409011580c03603500d140182004400d02d4040c0d251540f010300c00d01c41c3d400d0894203040260314601c1e0461810703250000581c6140030f480d0241d120700c448103021030819942005019500d075084025200a4005110b64000940c00140b029000b241005104001d8420703004108003100d03005409001d0041b07508030120001e40c4144201328500400c000c0d00030042c0440c102400291084030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 559273911 1250 559272661 559272683
    0xc031002090a050f030607051606090c0306060518010e070e1806010206180c040b0a03120e1207050a140d0c0e0f18100c02010f0c0521091213050a03 65
    0xa420300082c440c60b90002402081c224990242c66140080c0040d40595240703070540e12a2500c00000051a60405015000e5810554681c0500101c41170500c01c8900c100402c0020580e1078090101c44120100303c0704074400000010030142285240940c0c0c00107103881d00030780500280002804000260702d0400040b01040c042080b19601040361503000b24406140800c5881b580106540c0c070410901003074060b54031350030000c0309505c51440f21809941d201d181c030802c4074000d180080104400c0c55120b88100000b02046c8000a07000c03541c1815502c01800d4040303042d050030f1004c040001e101c40081d801400c00e040190201e109030401c0005409500441040c40c00c00703880403441e51901800c6c0b801c0300701000d10781c40e044590000710896803205001000c00c2c1114215016401046101200e00009060441c18400203500c01d0042c00c08054104003800082058210810300c0380040b0380c140d0380356000c5040341c40b02d50121406080507100c50401c1e00d09850300c92002c282c5034241a032084407088925 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 559275161 1250 559273911 559273927
    0x609061d01091e08070f0804050405181c0207030b060a0b0307050409050603070f170106080d1116060c17160f140604030915180b0702030d0e13020307020c031002 71
    0xc0d1a038264a04010460b025450f452922214143d00c503c0070000d200210000c4210108903070780094030000d01004004101a28080300555903210307610549454500518520798140402608000d11480392a4020142d041c2103645000300241d02a0030603034403490780c0c10005015a03000d0007d5118003020717034032261603034a016502415140090810f600c40d81200e03509029030381a0100a804844002034002c40c002d8008610341e004040540209000e0300511400084468001c1041e1076076440c074000b00d0380d0401e031400319040c0c501864041d10f4000b0791014904400f01d16510030001056401604152500000e100f0102c0803400c2104100c6000512524074028041c00455601c0c1c480348480241c016490565070040c03080865000341c1084008001d007014816104402c0c0828050340d12a403407048907210310b000703003064100f030303104034840e11a420b0703550549403049141015454000e840d040030301000100b0b00d006034000030504421481259000302e01550200030309004d4141c07000340142d0355003034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 559276411 1250 559275161 559275173
    0x313060813080307031a0405010306051009060b120601090e040506060a0806041a090a05010e100c0f080115052b060503010b06090d031e050c07060309020d0609061d0109 74
    0x10003000300c4501e00c800c14207403002c9080b09040300c1e4851118900014805182108030146c0e00c1842c00b09604103161200200c00c100b49030b40302038000d000c0c010100c1c9055136500000b1081c3c40d698095105005020301061554851010a03c0e81280f030505106050075101d95510030b40301801c641c1641e10364441d000b841040c2c205080c2c010080e008030f2020b40164607040d1901004507080407036412011881c8800140c0c800c40610070700d8810750380440203000349814060042c3e6102c4074804002d043c240307001c0700031009900800d0380042c0c060064031840706a0f864014680c2468400c1c1d00f20300181b25040019000b041c80c6500d10403407103680340041802c0c6604034003504080b1481134200700c5c041c2c0e261217016210741c1c0d29501514032044084078038040d1070555140484a8400c180039240c8041065a401048a600040544000c51040088442481d602c0c40101c00fa544d001c40041c2d000000040010081b5005c2c2d00712082c00e0b03009000101754042505035801c1100b598910200c09655960405010444 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 559277661 1250 559276411 559276427
    0x3071208010509070c0201020309130609061715090601060f020a06021209070b0f07060203090f0f330403111e1e03090906060304060603120e010206130804091d031306 73
    0x302c0c500f0300303900c031586e500103540c0b413103100d8449105a50314140c0c1110100340b900b0181c06021010000c0c41129070303445984100f128151507464803401031000d4000c0c0300c132404142d1481501000014003c0364030b040c10586d04a00100a580c0c00c50150491100100c0c00e02d00040c000000d02d013406040c903180010103181081415004100c0d80202001060140c10301c040958541d01e030001c50050b5240c60705000903141c120740c52218581402540f690660880300424280103ca8500785a400c842000c1c0204054580c8070010f5401c004a03600c02007000701740305405c0c00c1981480401241c8407602421400c8240074004011404240e001c450a008500c40e03880c09010310070307900c00c001c50500c40c0010020b4950340008140500130358000c0000342c1481102e4000d00000c5400001040740055a040c00908030140011140c0c05071050b4004251001c0300c118052800b103402585003030a00f0b00304813618001d48600242c1c12010b2410b0b40c0424050307081030000380700b0580c80f00e80303040038141392041c040d200c0384c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 559278911 1250 559277661 559277671
    0x19020f0601140609120708070e0f06010c110103020c062a130618120606030c140d0206160c080a1703100303080406110c06060103050a0209010518010203071208010509 73
    0x40c1000004002001c903030070814212241c101d80306600c41401c54042641c00c010305007200c405114007800001c4400c1d01017880001d8544041456070309036584440b40c07800c0a0103449260000e9149980306010508400040f400030405140c05450008003c14803072400300d041d10340061081030610800129402d010882151401e004800f1341014466204070b40a200144103c01c207201d06840c2c00c50446541c40c0c0c0c05005040010610000b01c21542400402407034540000c94805582d00c001080150000c00e41c2c001500c401060010b46104d0b59080c41840d4014008100c3c072111424415000128104220300140664600a01d808401802c0c07400a070302591004a820038010014080340681900d000c509803501801e0611240d1030f2480c04030020b201c1d02042c843d4900f404106220a41e101003150f41c000d042c240c1e81880a5115168504228411691b80381c0c00303d041006000740c981d084a0300e0400003081401500c0c200592512490260b078040c10840c00090b00e200018000f6142401c46a0b0f040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 559280161 1250 559278911 559278913
    0x12180c04090b0c0306040603080a020303061306150e030304150507110a06170c0f180109090b010e13060509040506090d02150a0506040605040c0c2f0904030e040219020f 74
    0x200150325240050340001d0f0003c41051800000192140c030745402030401940c5c004580b41d80e400c02868003c3d181d8109550240c4901a6526101d2181c1c140e07010303281c1501d401046220b00308507000415540040520307209601404140000221070308856040222000d589d00c03100e036138884514100d81d0307008141148074810030510030103201c503680c040d403000c02c40101405103a4441e2600d1903c5002d034042c007a03031020200400503c1900f6400b00f007000203c9041c00380c0303518208030385900380300080d05c2c2c003d8480c5000500c00c40e1151003500d04009120006440900c00140050700c6101003054103030300b1901611103034001410b010307070b0702c40030440348061700c220b8800f4014110003e401000c4800014140c0c81c00180ca400c045010340d502c0d43c1c816002044006c0080155071070200000e4500300c0310440a844050070032182e00080791071078200c0031090040035010b205d110708000401c0300282c0082c00a40400004104210b61343e2218402402c040f840c11800744d82030f0180103c000d14141c001445846a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 559281411 1250 559280161 559280171
    0x6090509070806010c030509211c02030a03020912030703180b0721020f0d030c030e030f040504090c0b0c010617031204030e01050c06040b01080c0607200612180c04 72
    0x1016401010143c210300700b460010000709042c20100e0391805900b40d0164809a48983c02541a003120395980580e05458260b60038500b01c4c15401d10440640c2c5030080c0540c02c1041200c44140c40380d4000d050142c3c004010300c80b44041114240c2c9036801c00b183c1200031843c28214551409600c041401c01005c50b604607901e00200780d61a00c2206d03401c000c081201c1c0d40440e403d504c035039000348404200c211800003241d04a4024031310080180c1801c40240b40424500b9100c60b100550220032500200c2c9100041480c252074401880024104040141c8034800064000b080c0562040010407244c000c420010a42504000d000c10604200d407000c10219841040b404003602c5000d030300340350321640606200003618074080059446114491940760740b40514001c00042040d50320123507058075940b10458580760260b0060102501c41d81c07801074845d80454414841d6003202c2c0300e032b186543e64090640c60401c41e001d01e8113003055600b65a1107210141d89840c00105190400503095500350480742845 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 559282661 1250 559281411 559281421
    0x12303011e0f260613110d020315040302010b060c010f0606050a0804060e071a03040611030609010e1b120405060705180105071a0103030c0b06010305252706090509 72
    0x1c15041c2d912540034003a080040d00341d0300343d500c00d0b0703003015203010041030300c055203001e024041c2c40b503250450440d10b000d0f4001c01c9190904081040e07403400d56028005000140320440d1290a0b003034018001c8045648483c01041d1a450780000b4020f0380b0040c0c4004689140b551400905562054011400704101403040d039000b294000146d40e04a60000c20003c0d103d03000e09405c0f424041150003c111003441e440c003a03009010144021441036005100030041b103110788814000c1440b0917030b1040c0d0702c04500c0300113201c21a55009081d801100002140446038001071803030f41540c10040150100811100801c424840c0031320202d64021403d203045440e010040b03402d103445d60f246140d040d040143c0440d82c0c0040040752060381705e54420321849140342d50794902d0028100a0062000c80e110b40c017240200d600e550090090341d000d4013480900c0b2403501d490720702c0016000e00300202d64003002140e4000b028201c0016880034058140c1c1c40b03514140a043c850003030000005540540d01072050141081 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 559283911 1250 559282661 559282679
    0xb030106020d02161e0519091d030322050601030c0e060102071a0f0f07050f070905090c0111030d0f05010f12020607030509190b07030f0216050f012303011e 69
    0x18041d517182e1418600c0110204070482258500c1d41c01250b0843d40d140c500010030b55100700c0b16800c84146c07210a0000c42d0003105080060481c4c02e0386203940303034003c0c03020a1030500a00b031a141904290702c5c0a50380301d92a42c503424680034081c1c1c8281c503182680101482216000e04000d94000c000f800209566454441080c1801c50340d854045085000800c6030fa86401c1410100d803010588241a280c031496513007400303030b00c2c2c542c2c44d2211440d40c85039160005580e0040e000c1c0511504540c0b010b010803091030300040d501c11010040159144c001000050b550b800c01e4401c8000a001d2510000f86660603c0501c40303400d050341e007140c54408085056500140d40d00c2e13040f941220b074140b80040c2c44800303620104551b00224030140758a4182848007140d403130001c2025041d054003d83d80c1e0607007820170120598a880050741b0300e050390320040409010300c0c1002040c118401030180741070030165860300d40c01849401c1c1c141d0903075a1003034000010070a080f040030100300c8064a0224080f00700b4600024a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 559285161 1250 559283911 559283953
    0x506030d0302130503070807080105060d0809060a0909050f010312051612140706090605010f1d0c21041403120f0403030902180711061b090f03070b030106020d02 71
    0xc6401c0540009030400c2042d0b00200440c000e240240c129080b450701c0b044141d465102500610005618100c0011911302e401650000a2904a0301480c80c1c8800c00e01844030546c0460007440c10722401e481d0014403d04c080c4240e0744030300c025100d0110554194600100c9140c4042e040c1020000d047c061145450b0140c4240c4582c190b0288a5040d03400b10f00b042070303801c4005400010b0070548040380c1c000c180069a008071107624400e410420003680c07074003049540840c150003044d5990485940c0031003081c0b902c0030340075006600a01030904105000d40c0a02d080202080203000a402d450140020489410040c98100360340001540c184000143d01c20704001c0700909002042c01540081824036009612810300660054040b940e400203890903420114001c0d40d20b04d00040e9085613204004101203405800b038a501400c00c01c15110013b40d038280d07a00812003950b4450440041c0b104150b400b040766000401090107525100d601d8818083e080c00c2c507107000c460035900700c4c02006078111100480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 559286411 1250 559285161 559285183
    0x40f050c01020d0e041a03120406020c0d110d030e060c030d0e0d02030901180803031608070905030304090f060b040e2d06210f010e0c030c1305040807080a0c15050603 73
    0x4000b6510b282c4080303104504903842007054240c003235081c080840d0314401c0014030580b044c40d000c41e021402c4400900070100311002c0c01030100390500c1d56807102031500311078a0300281d0103480e21303081003400b00c0001021a0300c07801003000150720000e188c442540e610b000d451090407c05010384442c0e04038502c060341324410311408504024110040c14036285000340c0000c0a0312143c0100c035140d02d00132a484044440342d8a0690214001c600000c0b100b41c4181021010b40e8800741c0554200792424900b800900840002000c2c4191684000b242c54400b10300504010100181942c101c0c0c24400030307807258104070030460407404103081003003102c0c0328015182c1e60b00301600707a4040c40c80c8880c58140942c0e40360752210140315802078030020055008150400404503c10109803814624000101981d234070f0041c040f1038001040e040350860711103465001940c010f0051030100d181c0100c958540649500450b041d1000c9107403064803c06100310044000240030b04500c082000382082400250740d84101c140c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 559287661 1250 559286411 559286419
    0x501053a06091a150c0a0308010317072609130c0e1822050d021606170606070f1a0f0a0501030f02090408040f0f0806150109032603040f050c01020d0e 66
    0xd04c00803514581c000710707000c00d4000000e4941c500464600200b283c1820700c0141c80c620310f8074800501c41d0390307558119044181d12506d120070f100d20380e1074100d0300b105c0c8180000c2800d0b0400d009c0f41c40b440d03e27608803001200d041076500090280a2900c0904100e034602c9101d4000c0d510700043c4030114404d03010b00c58101d00c0d4005000280c001d01101e40044078141e1800034203c2c040c004a41400c16000252400c164814160301943c0a4444604030b40c609200d074404140d00003401d01080d181e043c00c5008141403400b80c250360280e840b06445860000341c4107140300182c14029420054690000425a1b401c0005204240003230351441e121403460750720401020b48a0101d02c800300c1c0030810850126001484042200312000395170b2090444800c0603481040050701564000403403d2203605002041e98805840e0b02d04440c0c15504c907800e580b122540b00c0c410032841024020503448942020750f1256104100721a103000c5140b4080c0d050541c580403950655000800d640007030bd070410415a40504199 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 559288911 1250 559287661 559287679
    0x60f090604180212011a2709040b0108060109020a0804080d060911090f04091a090f01051602010b0102070e06041e0504060509060f0c040501053a06091a 67
    0x2800194040c412070707002030440501034140001c044000e4010703041c900d482100a0b421680d03071700030054610103400303140e2044480c00c101581030707070200c0e206a036100d501581c0600319404a20700030508001040d102035500203da000101300c4c00208001da14050300d1421010b40c2070100240014040d554048c02c01045403601207465562101035500100c0202400311060201202c65601c00080e94809100d0900070107070840c48803e5400e00f40116040710b44d0285410f0240c080e000500d40c1148406084900c0710301410058499a030300034011280211500f03032112603100300700f150107400c50300f6655800313056410080d420400c4d402000411a4001010348000c1202035a80d0041642504940c0c0f0000181d0302d4401484180709a69018520508206003100c0282d140c0078820700755808102c818a000c10001c110520141d4802c2c0040e00304241a940403624440040c0d4140c1e182d0090090086018a4120584203e9010034014000106180d44041042c2000035140481a440d002d54040c0191964 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 559290161 1250 559288911 559288927
    0x30702211615120203090a061d032b150510030f23060307030519020402090324010902040609090b01090b0f0316081303030507021c09180605060f 64
    0x5200c1c02042104500280422644461540d903505500384465400901c03520741d62054140e1034400c59004544a40080160721300aa4488001d0722180c90042d0400000c48002d0b400c40c2000c0018125030000b6480071001d000704048081c52804034900e00350078207401c0c2400717402104151100c0000342d401c140c1e07110108410060069001d020100310025074145403890044030300f0688460203000d0300c009101444181c81d07400030141e0f42c0b81140400303821a08401030b642c500340b0107aa6100d00c01d610280001d0300301510f08001078100300302c400d6103a58a03250a00c40302100850100d409015200a2404500b0142050401044c1100c18081e0407c250741e80c0314480d50030781c05100914000c1c1a0081078981d180c03c00d00000029400a40b03c40710700c002e404448440450091a41911445912046070f98010858500b1406018003500c0c2c14154000da103000c90f081c00141c040e05417841c1954039003c4540b032600700360058403001c1c03a451440142c500801440681d803500c00312182e40c11170580c030740d8560300b82c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 559291411 1250 559290161 559290163
    0x180b0d02040e070b1b060703090506010905071806030e060702010e0d1b0b0705070c05060f0a05030a09050304080a02030f010506100f17100e1308030a090602090303030a0e0f03070221 80
    0x741d0304901c01042011416141006090f600705d5000ca5007101a12941d8959803020303419203046260080c203070b800a200502c000f5071241c1c40641d1100e05442d215241001083c90405010320302d400c101d0020740c8034451000000b070200800380d0400c6103440201300c1c0341c120240d03860311811910300ba6400c0000c04030301c040d1348a40d4002d008a9550700b01c3d050105a00745030f00061305d01c0e0701810303080360304015246001580745041020358101d4054001e0721481d01c03002c0c010403501035000070800300029a8030012a0080750003000504040d181c540010324102400380101403500c1903880001703400d61306043c2009150b4030781e0310b040d861801c0c0c9828a08140380701900300351902080400310240f41680e210801c0100c040e1404540f04507820703c000426640c899030550307010042d40c0240a091540c040021490b50709055205000b218050707500141010010000217056510549022000d552203d03a61902c4440a02c20348225148590042d231610100786e000c90800003002000d1528072031448445860268 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 559292661 1250 559291411 559291423
    0xc02040902060a0807080c04030515070c060509072d0e04020109080a031806082403030d051003021908190c0b34021c08120f01180b0d02040e 62
    0x50700510340e07a251458420b0080402c0704c11100d801c0010f4209000c02c40019140c422181a01d41007805070003c849410008201d0210103000e001c108181441c0c5140880c1c5644116400307146090b014041041c88c001c0c40700303415000c1c00c0b404041d001c04111840d0a40440744119800c4a5641d181403201e030741e4600040c2c81d01300c0580e22125290003141042010540d001241c424841810705071480c40c5902d4800c2101e034a081111505020460301140c04002c6042d40a07e051254000b01280d00c1c00c0c611840c480252141610006c40c0c840c40c5600c240214902007500d82c50202d8400a418003245c03626007010358030311a11200d2607001002d02c0001d0217010401280101400103807403050381c0e0342200c00c0300f10703289203a10125000e20511402c40411001c410700c0038400158004005855540f515809886c1040c0040c0080b100080c0c1000001c00208446c40b00c4c0b031044200b1000c4080540c0340c9480d014410240c5900144002d01c0c103100f400803030f55410110b0b101c4c0c94044c1e0700018240030030805945006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 559293911 1250 559292661 559292663
    0x105040609030224030a0506100903050a020d23160902070b01140f06190906180e0901020c060408040e010905010605030f04031215090b03060c1b010609020a0314060f060a0c020409 79
    0xb45000042001b000a0303034004a010754000d4401c1b01d81600340c0807048030204850700000b03003290400c045231409440c0c09140c00d0851070203000c210170096900c0c109800c3c490a14142d1f0710160f0070000c21100040c1c1c1401e003d000400211505524000340d0365124007504c3c1e0305005d000e110200c5203001c450140c590981000005202614050b0b036000c1d102c100824966507482d030a0000748400341d003c07030f54604c1020001540c1c0d003070b40c15030b51400d03040008400500f00c000b03000300c0700e640d030900088100761800c0040301c0c000e60081031019030755405c2c452410907400c016002f8080640c28a8010441c042e8840d040ba5441420105088540e031590300d812501590740d0141d600e1410b041805000e022a000c09003003040303600d403002c100900c018540903d903c400040341c174800c40e1001448510507408003420f00409000180c8000a002511111148100d800036502e100029a40e40a054940241542580d030000c0341160600c003403280e00000076406214a041003410060b10250490864480c2e4001072003803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 559295161 1250 559293911 559293979
    0x621151c020f0301060501080a0b0310091b091107020d0f06050403030b1804050d0e031e01060e130f02060a031103180d17011415030403081501050406090302 69
    0x11290014450312260204402684101101c4403014000c0c50144606021100184c44445095580590660042c50028552905070251001c1d03080c130909144180100d075032041240440440e5640510710018101d60002840c4078035100e541c00600400100f40c42c2d000303a0442c0c1c0070260384101c1c680a04c443c2c440e01c4006040e5400d242c00d00007015015001000090030030754a2480d2414891541d401100c030550300030344660080000340c0c3c030305440348154801591001d03007251301100b00c8044406003000c0c44605400c117a59900014045034154088858000b84005105403822420740c4980700b500107c6030b0028410700f000074209050600a4000f603142002201e01d0689a203840d084402c06807448202074010780c007a1000d41e650450040b0445840ea42a18071248100e030301748030b1021403000d103401d94641e003d00d00e2103518081480c1c44000b144200c0c46580e407105981800442c00224500401c04141807000511061010355031000100040700e0b0105c40c1d424040c2400440108154540000780301c132 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 559296411 1250 559295161 559295179
    0x706110622020a1d1602030901050d05060a1a0703020601060e130905011d160522021809070201090c06021c030f02070c03030504320d11030303010602010c0806062115 73
    0x88011380090b85121715041c1c80064840010340408a80300d00c20341c6845408643d051148401c1c0f541c05512180d803220019100e440c00079207801c0b90340c4141c101c8001c400360340034000980000301503040c13001c10700414039400c2c506101191640007800644e070301c09180307404654a07050102402400d400c41c2400070380d03100e070641c4034404061503551076036004e42c0c9014005000c10b03800038980c103002144076417209070714181070030320901607100e000a540214055000d4100002c095031460391604c4199000c5d0983ea000003545442c03901e4143c0852466600c11429034100d802100101d20081c186003403070315070354580011049004410307407000303016061000c0c01700300c81c4000100401da0494000e209942c0d060038000c2c44418000703152400d00103440c0070031041c1c00301405500303254284142c403c24403521400b1107a4084120a020038a075402c242d01101c0180e44507140c1044141d08051003036000002915040d207020b28040d810031241181c1001200000c0c1003600081d503825010000012210f030003820449 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 559297661 1250 559296411 559296449
    0x2a020f04240801050f0907030233120703060501020d120e030d09050601080303040507090b0d0b0c210c19051303120806120d030c03020405120706110622020a 69
    0x700035080e002c0e10301c40398070f08000704180340d06031030381c96200300040707401081d400d821942841101d0044513400d0f01c40d090310350f8000c80c15107001d130800800f2185860301680c41d0f04213819041d2401c035010b0018018940740c27050620199a02090825550300075081c040014000119818000c148035086c051a40c040401c4441140310340b0b801c85000726001c1d20450307490780d8a88417495103030300c8281c4006080307030322012040000032010b03000a484210001d00740c9075100007580f140700a04070101e81c80184d54a0018900306d03001c00c03047c0510001d0440d0503071a8034501d88400f1940c5503104146c04010400203103083c03c150725100d9400c81d8a44000a980c3c1421190b8038035109114040301c0c103854011070f460340c000503124105507041e507003400880d200400035085050402c2e001002c20f22030399810550200004a441e464841c03108140400c1040100b8074181f40180060140b241c0d50500f2860f604444c040c06028845034034170072120603041032440ea40000c14800510b00e1501940b000c0b100c14040a0011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 559298911 1250 559297661 559297721
    0x51f03050c01030e070819230705130b010c080d02091305010306140c1b0c0d030801031205040e04030e041b020c130204060512190203162a020f04 64
    0x104072940a0302c0c180804844d03c06400d0302c032190781c00b822160794454000000710b089450908481240a002c01c40303210348482e01e8004038161101c0b0007d0304e650054100300000d040c15085a4100c2c031504e001082a4107085000030704108003120042d011342c9001c1100003403400302da4116040045c0003040702184814034810400503202c00d2005490f0719250511410403003800c0400d8030b1003020480043c624046e42685281d804601000b0201d54511851508000540752840c02d00203142c02600c58013a1036149d446d005000340202c00070b44040082c01d120400c11403401e451120381065050402c540b207002441c000c02c00070600c04c00880e810054061484441e60340100e081024400b050f240d81701b0804002001d802a03200328804c1100080c010000410300e03003240180e09401044c00000c4447d842c07060380b003080981e0010f881c940080c40c1681154100d0070740200000f81c00a400d2030540501c0c030300ba005c500464002c8110081c0c040c14021a02c080d095485500141c0030204443e0001d0907411161560 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 559300161 1250 559298911 559298923
    0x30703150c08130312110406050c0712050304030311031e0415020a02032d0601030305091009060210050c1b0709110903071502160b03221104051f0305 66
    0xc00e24645004000585a4440e6100310b118498040d169862140b6aa4040f00c0c3c0540720003026403110303682d026114903005490020b2004203020f9484640768107484280604094496000102c407a240780c220100052000c0191401c50340c00d41031000c03078852290090790441c0300c2c00345507000d40d1000102c1071042409410290080da50000e14041e01101c14103030503a030b110b810030030196060f480742042d0449642035440f400c0560340c1800b54229070500c2c4000c190300d0243c080c1c004030f01045012500c0e07191400d004424031542d019510704a00b10a2a00001940740c404403000c0445c2d8548803070004408202510460b10552800d94900340308084550315070340c0f920224062002c40d40e05140c0214402d046100c180c424490000f4041d0401d140b404100c4680d0058501c0760b0411342c00f0f01d0800b402c0b06401e0310600c9000b0800180300c0307543d070b1512031100702d00c0c0d410100061820218200305180421103004500b012180b00b44d4000925456a80303d0424850340d20a47c82d8018140f0100401040030108103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 559301411 1250 559300161 559300193
    0x519111b0105070e06090d050303040c1a04061d361f0b07171204020310020a02060f191a1e031207030e0414040311010c14090f030703 59
    0x24048580d05030144142a00d000740c074801c000842c0f1203142034440ca4a01d0051001c000e00400b1180d48409568940d8119001121705035103040d60b01008200c550b80f01481d04480b608030a14043c0303002c1c209040505480c5840c4200304d079643c100030080480352901540c10305d103503202c0d0520008210100c1881c1c180e0140d40c00c40070582c0007050f404104d01d043c3d000261446000d0045100344074030708040b4000403c1c0c004410582e071031582c0150380b441c82d0410b10002c100c1c000440950804078035150040c9843d00b800021001c082510401080300c40c03541c082134081d0410600c041605545d01c40031a5001c00d50801c07010b0711360389031608400f01c81066203c550400345070410790b00048005000c00c51b100d01c405940c3c0e101c903050342001003596900e400810007041480d00c00e0900000480082010a00712802c801c940382c01281d2501c04d010a040c0c1080c00000f900240d07800030701c142005000000d18092504001d00680000412030160f182e488084403020718001404070b4510310790380d090000840000c051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 559302661 1250 559301411 559301437
    0x21b040605060d05180d1d0414090d030513020108070c11030102031923010302060307260a14070f260c030402150c07032a0e0a06050a0315051911 64
    0x1000b4070a4170001c43c041803100043d80381c945e0141d440040094180e030982804551140d07852104000c2c441034100100d0044800a008100b4803c420390060219400a004810303100003070f441c6100140e903c403510a601030b046142540800d8001e24040400700001c44800e941940040304000c03100f03802030340c0c210f00303120041e105002e509a0b00901007070740c1038515080b002d4020004014400741c149480215088000c502e4446401e030100403c502c06101380f0070070744001c035076014140510000640212410b12003100c0124003941400d400252000c03101080c0b01c024460002d10100300070400000d2020408000d1035a1112483c003d5240c00841e072007200c00701d2062024811130444104060140c030505482d000090401c5819500c0755090411b40003101200051002d500c0b15102c403852401c0001041c13210400c42e203a050469400e015a0070b00e07041503000d154109820008686d0521000d000e07040c1c07006000641d41c40d040c5071a544071f006500c10003405402e00c4160300701c2d00100c000510b07440c0403c075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 559303911 1250 559302661 559302691
    0xa170915090d060e10020f0a031103060f12010e030c07030c0605040308041206020403023c18070203040806070903051c051801181205120a021b040605060d05 69
    0x311448854050307031280c150001c4a04940c1c100055903507000d0543c01c6800302c02c5030030311a5804010302c11799014141c0312401040124001c800303a500350080c01b90054202424505526111004ca20403410f1084c2d6207200b500b40c0342c0350b010405400e5000441d03a00c01141035980d10015484401d95800152001325003c080c507440020b40b40d403240e030944041d2540180d200c1e281518040040840c40e42020060300d0380f9908000c00801a41c803d20450010101b0034811481e0781441c06e181c01d040d0701c403038003808030842442d5407101e240c2d03a510111000c06100b00307940b04200c0e01c0720b44041785036002d41e410490f4288210014006920341294221044a104000b11001c0d00c0000290301814440e11031460003155080c402c4034603c401207204a07031510070600d071910140e91130480c01c44842240740c0c05041c0c0b000c00525090203028050029041d101011355200349045844d2100940d01e1588a11851031450300701d0f0304600650f9960006001880d008040580300c50402c10030b40300400c810b4031381c014140d0b464 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 559305161 1250 559303911 559303939
    0x1715090408160f0b0a090507150909020a020c030601050301060b0405010507080d060b0c0c1009140d05010f02040602070806010501050f0c0c030304030809041b050904021b07090902010f02160909050a1709 89
    0x180106c0c9a090b0380007019060645c41c0031080c4100d507405904000c1030190880002ca6404101d102501c0c80016960061552800f00000c4c1402c015068000a01a07410310344148400e036000000c40d41154000e2800a5440c01715040041c4907002c1d0b502c02404082c01d004c0000b507841203440252240c0c020110035943c2d034210301c000700306080e07001c03004240214075440d40401151110740240210020050004000d040c1503556641c00c682003003550700b2140d64082401d1207185c0e410085000900040001041c865041c200040c085008183c80e0b5450441c000400c1906208280400142150050b00322610740351039140911058015804440c00349282452035960364110601007000241581c4a50746051900710512020f507120200c2000ea00c200e9110140203540304015104c010b1190074400030b49126140b000503c03e1498203020811507018803840c101c60784011001100b00c42c010200020420300e6071030312508003c00c1745005410080101612114001030320000e05034800211225140c40c0c4003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 559306411 1250 559305161 559305181
    0xc030d05090f010c080c06040309080c0d0534150e1801151b1101022b390507080703030503040219080f0d1715090408160f0b 55
    0x50049070340d40801c100000d40b0756940600030383c0003040c1c000c950291500d4031070ba068501e032840071b540480006103145003c00000009200180c0303004400c440a00c0e0241d15520f60030b580d11020300e030f100b042043c140c08508200e040d0080381102c101110f0300030080260344031241c072610343d004040d45012946460550400d0b18002842e903113451000c0c0b64080d0f199007862402680722105c803d044080c0b000800d80122001301c00d5a0540003d44103407000804c560190000909004100740a031880c0c0f48041407035280802c00c40d0515859408525000004c9046c1955803252640c01c1040558810b10b540c1c02c2e0240b2220007030321141d00e58014412110425641c0c4226592440d09200190000f1011b201081c010714005404001100705d010030101d1b5961207950a6040241000690500b60f021815080c0c40c00c1d005504059a18426025808249828249265881c0f000010b40e4070500c440c1002900300803106040d1840002c5101d403900a4100034a00300401d408544401d852814034240001d0900003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 559307661 1250 559306411 559306417
    0x180a020c0c1002030313140f100b010504030308040f230307020f010207121712090d0f08070f211109010806191509051e040b0f300f0c030d05 62
    0x503070f54000e62466407201044003040503c00320480d440c031901041d030300c4a500d081085603a03507402000a00000b6400601040898400485160600a00f4441080440c0d00040440d501c00d4000303c003000304039031520301034811440d40c0022014000103030514203098100000034003090751083e103811044841d44001079070ba810551140003540301c0920003005c0018404590501c0078125400c00a0505080005070740d0039030011546a42942e05c0803882e48409640000c003905220040e040c0100c050801900051031980006802c20900c03424020715050344801e07401161803031082510400c240b48051008910039800400d0990005150f00081142850082c080c06011003030700001c800c480c0c3c0f404844030044181000010140403c5c04070004480e1138101280280d05000046940c14070144020002158103450358940a51080c40c01c2030a25182e102d05500f81d2125803050024200f03481e400b80011756810401441d4a0044045080311140005402c20240d82d084059420b40c00c00c402d0f040725180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 559308911 1250 559307661 559307689
    0x1005120109150b060d060806040201091401080402060a05130b040612060b090114040b070b0604230c16050a0503131a120a1103090a020108070e130506180a020c0c 71
    0x1803003100210b4407440981c2d00030319400d03001501d1306040c01c1c400c2c81c10504451882d442018107410030303400c0104560b884112000548000405140c28003030340d9000a01c21748000300001c0c042c202c0050a1041c01c1d00030402d82d101e106503070f40c07411196515101e442c5155001031040401180c0c289142d0400b20301140582da05a0368014006410000a84e00440b42d0310421010010709400070440450080001d400800e0b11500a031081c001506001c001e22084480030014200c00300d60b14912940640d03a000c50183e040070284011540310814014200d03a0203414441c000d0640c1f00b9040590104407010003d000c00c01e140303403200b007043d41c0d50750390b4045459400f02010004400420801e09010f249440040d08061407810000e6100c000200c1290075a1003030310340080c16400702140104640c0d00100079035102203d45041c404007100388010403c400c0d207041e10881103d032a440010416150b010890249600c10092101142084030b40000290303c1a03001c0c815900410b04c10100606199107021448 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 559310161 1250 559308911 559308923
    0x30e0706080c030402060c0f0601060e0405060d030c14100b040b010c051504030302042706050a060c1401092414010302010903150e0106060e010318080307051602091005120109 77
    0x1555030542e41c10740c56030004104991011007803050b007803801c2c0100700c01c0c1613903054000100b8065040c04006400310701896403961049081504104060701e6800071244171580c5401c0c6450070203050f01d0715005250004040c0c0c2d4141c46030102240c6210759a0300500300c000d8040c0d4007040044842c0d0700459545c60f1800000e81954091035054041240184145034842e000b031a005003003c0d1109042e01780e0700400ca80303c202188441100ca10212000d2041030010310003103980354005880d089016100020305c5c113010b08101c5240c111281c00050070f411455009501190300d0007508204680d0090741c0d441000c40301081840c050003a0020340109080758180c0f5016100c40075071526550721858414820310b0703c4100941c84502c51408843e0034001c4002911044e100c0843d032240001c00103044910302c0440d008180c0025188c003002c50484c0c822250445414604181c2c0c40300030141600895a58000007500500c01d001000541c0341841d090400345c840c01c0303c42d507001c1d840301003601c0e003a95139a64010b800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 559311411 1250 559310161 559310177
    0x3200a0314090612040c050d080307110114061003090506280501061b26030109141b07030c0c08030d0507110d110a0b160e180604050606091002010903030e0706 70
    0x7103192900405684148180c1c10900c00710388030707804148da50001c03030800c540c24100481848409031b0481b05210000c884080200070b0703000b41000ca280001c00103040785000e4002068400c1900e480307a0043c454054211045601c0c070305000103013817071007080c0000c1025081d100c0c0d24440c0701c403540c3d8042c05040341d406c0d5945585008a1055403042070f69955411540824500100e59002d02404110410b10140e061050384a43c07400c0008410341d111100c003800e01030110001c00c249010110f60028280c0b40c0071515030b4803240e143c030301a1100407200c00b000d0a0800104800030b0031180010040076800c0c0c2037041448103494118080d261150351103030400e0190840f291020f401c0f4414201d08280401d00804c44020045940b00c07400010300c1610000c1c503004240d5842d000c8940c005141d4102e0010a58183d610116a50b4000c0b000c424050309080c030440d151004a0520742c0c51001fa1107001900500001d855004108081c0c001c04190500320003080c28a607038a240d292011901000301c44043c2ca407050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 559312661 1250 559311411 559311427
    0x1614010f09050f060408060f070f0e0102210412050f0115061e02011b080907060206061f0e180412030b060409020318010204030317130c1203200a03140906 68
    0x1d0071503e00c50150006800d22000440b0751007000446c2c01074440001c8810103007001c160040c00c080e40c08500d0824000d0800c1a00c50a0340e0000d50f010b401b05000c0c568000c6000740c11701c0c4480900c100d0b401450054041041c8205018002c1108400b80620704000c0007a60b96111200803122207501c600008180ba1410903c041004220411407620b664400014991085900c01c0d0010080b030000b00000307000c43c0100121082c0c10803c4101402c0d0314002040c1a00d41000055100902d81841d001c0450a0b04041c01406000720304c0004500750081881c42c0064014403a645400412a41a01c5c0d0060b80c4249016150080c0300c1c1010080340500348a10781802e022001c4007030b40c0060540c0c00080c2c42001d4030280740f407003803000d8000341d0703c26903070040d11121203030140140f41d9000c4d000742c1100e0801d91658002845a1502c00210741e41424940048011801d00b66001012100300701c0964520b0044801d41c880042140044c1910984880c0b5000032050400d00c42406801c009540201040100b04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 559313911 1250 559312661 559312669
    0x15160f02010b030d0302070b0618130c1548021909020c0d020309010903020d080d1506020f15010308070807050a0b041a0f0c09121614010f0905 63
    0x1600044140c000800c51401480c0403a1502c00d403907000000281e800308098003000b0899507400d0b00080c08481145110880b580e0302481204050a0701e082e800300031140c1d1f0200718156250708010040304100b0b409040003200302508039140c9548181410084600c40caa600c402d20507608081c81c1403401158585408801040610107076401c10303030307200240c26000c01000d10600d40d40000b0f0f0041d00c1000d6100c8200d20f590310b02c0c10081c03490034019900280058452030340d201011004590f0100c40c00c542490560615012a01c01c0d201050b0515050110200c6000c00340c50b150710072200b0550850b480b0000000480ea256000c0c0018000695541401040400c10b408080d028281c050300c045803400c0300a60b601032400280d1a8102d0310421000104014418071b0b060810039801000c1300d0060619109500b4045420300404d81a840240480c0d040202e072a5400c800c0d00d0402140100d814a044005e040008612544543c40f180310404043c0716065200701744000b1201c689465004000381040104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 559315161 1250 559313911 559313927
    0xc011b020a112206080f0f0601030b06090601030603060f201315091229010503031c320a0903140a021606181a09010e0d02040e030c1516 60
    0x100100840081c3c1d08111100c80d10400004000b281e000b0304518a101c4a00e5040405240320011180c11010040022a070a4180c1990250b41105c0403216669813000680041032141c102800d030320716265100c00291080d900840f40601c810510107180b10309140d40902502c1103010040c120f00070504100310030600424440d4600030581081e0b0300480c0c4a8007188410a140403003512a495419403104500d1405480584100710f2100300344015810080481c0c0c0c0c0c1e2007844d01c10303510b51052180c0541c0340200f55128940003c10808501c981c1109070b6031b0000c0d00c200d9092015005000000071525180c00362094070030099050300e846110190068003070080f600511400b1040d4010f5021200b40082006850b10180140352103032000309104811002040840d5044200114654003100003a80e1094055890100007444e242107007240a0002c03c2c003070503014a009400178140450007004203000701c0a440c0e15a1010f040780d042d5101203e0f0501103000c107039100042000e0080c2071502c0c46100c1d02503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 559316411 1250 559315161 559315189
    0x240112060b07080a080601140f0307120e0c03282604091a01020c0102120d06030b01080a120314010e0405010e070605031005241e0c011b020a11 63
    0x400510196149440315969002e060222440240001d000c43c0d50350300100080c2e04060213182c14084481c1c5c68400307209500c104d40c4103c2202c075001c40000c0d0340078401c401e559820701442005100500d5010340d0b560b03488800304c40c070070312a0040c24002d4402c01079500450384550010302e01003800022075110405401f002e240c00c42d50100c5c6044400c03079004140c0e03004000401c904100042d8038032150302e600060111950665045401903028040c0503a40001c0409401484500203540c42184400e140d0081c64281d0009021541c021300010b001c140226503809464000c001d511012944000101c0446201c0c1c1503d01d2113400b04001804102c02511030654810b110390000a001104100d0360f518000040c1d00040000341c002080150700c011491941c0300a00b002d46040d2203405007080c400c0b0070410309550b601c807925008212683c0311621800460242d5460303540d121740c0c44400c1ca1466010b4400700300010100b0a804c0000c00d00c07039200041c0300580e10742109401500c1480c030030800c0602044414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 559317661 1250 559316411 559316447
    0x1002120a0b18150108182116080d051e01150309080d060f0b0a080a0c17010e040209060a0503030d0b0a050a080309041410060c080f0708070b2401 64
    0x4107400a9040c40007030340590581c00a1982090414000408001001300806c0700084444942001c10000003141c14000f104400d0940307490300035002c42a81c0f4010480601544c8458903244024030072428000c00b10503680704000e000640d02c03514030441c0310354045140010020400010040411030344800c26480c0c01c07500c4c0203d6088956210382e04903070002426a10043c2c1e84402c20071010303002540f4040140342d4542c0309410503110f10005000b0034001014440000d80302e460520206100742080e090250840b40503840e02d5840f903500411044c422101280601c52510129040f86044e416400440d10001d00030f40c0f40604004400001c0d04c0003c50098100b42c0c10880030541e552412405009019858015519041c1040070081903e850b0303001031208164405c144020152031000340d000380d07051802e00c00c10301d603100d1802c80e00034441d03c0302d404034102c4045113900c2000f000400030302c0d0450080d290000262212a40f41403000c04c440b42c461542400c0344480c4409500503824441d10003800700c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 559318911 1250 559317661 559317679
    0x81906051008090307020603011d010602190b06130c021c030b0d201320040501170405030f1303032303060118180c09080705010906120e1c021002120a0b 67
    0x390214207a82c000383c000102b4a014004411880f19a004906004003045d02c02410900d042d540301040008808a000e841000c1010002d1000e4039260300040c0130941c0c40340d04204051100000940f146a101c18507403552001c94240380d00c0700c1c07082c06014080709005110780400589560380248401c1c80c10784144c42c007110402d900745e1590307402d007100c1040421a1000301e000708440040c2c0303100c4003200d045440300010034801400f00343da00101c070848401c10f0f001c0380d040580307407414a0b40c07543c0160101250301c00b070700003080f04022201c092008100c0b8480e48480b0703c03030608030b604803600c0880c1c83c20000482c04180002885507214050545212540c0300000c21595116041e0380ca40c00c42c0952030310245620740c081d40098903401000007000301096005450311030705100008014400502c2030300200080c00360701c0780300a082a40000614290f001c11564030001c0390071219502c0d8990b02101000d4080e0a1070407a00c203282e03008642119515024080d001e03901d0420b10b0300245043d481d201e4012480c2c1d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 559320161 1250 559318911 559318913
    0x18070305070b18040f0506010314040b0402150d06032303180f120601150e06030903270d0c0504050903040803040302040e0a050d11071703090d11060406081906051008090307 76
    0x184c404c5540170040c1e0038001c5118501a030024080c3c0b00c0040b480e901c0314440804000201d90680002070304154110340d40701c1c030b95901c50b01405250280410b500350703452420800200300400c56400410010560000c002d003040200d544075168041c40e5070003c210542180c41c0c0c005803901400045181130010091005a0139414400c4d01e880d00c01d80000c0400b041e40380400341c1d0f8681000c03a03142210070407541c00c2c0c80e502e0650300d820388a014002c0c050340180c031540c59221851b0a0f040b9040202e40c0e020b400000c44030b1550070b0450480d0440c0c0301e068006c518103000700d08038140200855082d140418021441c103441d680c01c0c04000c1c0310365240800749004006108000034014004505200b085075a005490910400d02c01c0c02e088081d4450040c0f0300ca4280c443c00300b040701005948007100203c855540342090b50611104860b0480c401981c0404000780124203d500804964020301002d59011110300f0007100c040c00300d500398081e1a80c803000c240c0c0541d9155206a8240d40d01c010114207070303810071401d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 559321411 1250 559320161 559320169
    0x40302100b190605030108011a011d010504030b1320100c020d0b13030e0604061b020a270f0506010503010b1b0102070f050f0105060a090e030f0d0518070305070b18 72
    0x1c40d0000f000040303000004125080090003018070340280280b1000c00e00900b0700010b48140c07500303203e22070b240c0c0f0203180c5441d26070302650603503004581044d024482c51400b5900041c41ca550250102c0701c3c1c80a04405c1d00030300d0102010b400d24040090201c114064500030250362038148404c0499219245c2d40d0590001501444200d000e00300740190000928010301d03000e80800d00c419401e9020f0101404100246030344001205400b025452030068108c400d400030030f18030000f5410030b0401c0c0c00c0b9015426038041007400b0020fa0313508196020040c4205d4042e500c002e90310291030b81400600701344014031441c0712080050507103541c01c484441348003842c40c92450980e00050020790742c501d00e060b25502409000d0140b134841c00781c008020005481d0060001b51841000d010300c809290707a9104001c05141c007002240c8007400e0800030300c0d4880d01c0d402c0c0050064001150241d006880312030b10340862800020f001000d595002c8041c0804a042c102e25404903085805015a00301003a00e5195a6480d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 559322661 1250 559321411 559321459
    0xc0b0702030c0307031a0c0c100209040f050f19140105090702070807080618060601090b0a09090f0b0411211e091b120c0d020a03140a060f05040302100b 67
    0x106c240d401c454550102c0040c80c403034081c000c011048106040203031107581c090200d80421005851030005880f0350a48000c500200307002003501681b030703282005001c0d0405004100c10b00c1445400f00740c0702001050010a0705075040c0c13900a02c00c11039111f0040c025403500a51080c0d00c201180b04a51305a039403207103024038003102540006002c0e0403840900c082c1c2d50380e0304400c0510340400d800506981c200315000a241045e01c0c454480d100c1d1002c00d88841c0c15101310120700c024903141c0814002000040c00b2440200b41c21191a40b150349403800c880d101c2510042960400c07018524600018118810144200c6000924500131b942c011250310249011107221076000b0701c0140700400c130460700c0c086864500d850b500340302071062844070b4007010111000102000b40f000151ba044404c000d00d803000c519040c80380e0300300a00320008244040b18051000072460a124000c01c014003000f00c4485040044071300036107002c1c0041e007101089404010064210000f80c00d0003918000b00002c6020724039940c1c0d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 559323911 1250 559322661 559322663
    0x31140606071707080c69030c03040807080a02010804140a060c0c0c050a0f1703040806040503070605070503010f120c0902360d0b0a0213060801030318030c0b0702030c030703 76
    0x2402c1d608402400c81840700b80751b41d03004080c1c501000c03e68040c9140d0b8001c80c001054200d641002c5c2c480c0300a08414406190340403500c60001c82e501c1e0030701c600d0425201c0d04240120050ba204440c1c00080700e4000040d899411501a16016010740b1240c0fa10030145c1c02002800c4c40611448041e00002419841056012174640c4c0e100c06034009035103801c046040301d980c000da100b42c040c5041800301d0a40b5a45080c100c03040b040e0601e140402c8034145038114011a070140c10b0a0141c1c07010801032160110061038101d10503a401c010036612030006a03807a000a0103002449101075009009556591014094550080f00030100c0d20f80c0d5003a150040c2c0e48810345480c4005100700c13400c1c1544050b420314000e01500d28050309640e402510200e200300d40c4400d40680342d0210304011a0710100c0c40d9045403054800001448100c44c0c540d40d0213029a4000c0c842107000480700302000e15000490004241526030203040900b81903e030680c0018903420000c41681e1500581a490313101d60360411511000b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 559325161 1250 559323911 559323943
    0x3050705101a0901030c0b090a030b010f24020309040e030c010c030f0b010c0203033106030c11061e0c091e030c0d1131140606071707080c 61
    0x1d6201c507a08416108090022070f4040c5404000520006414a0350401901c170749221923a15030002000281020340241e2005e091511b1980000c00c3d42c0301844081e1007610407650316100c084100c0b08400419003518409040142c1007030010741000c0ca0180c2060f5040e64a2000700c0703041400c8210b480d800c40310300c681c60740c0209607540d0080300100c01071f01850742482c00074202401e2404a9801280c1c42e1301c00da5800c0004807008094140803d214195015844808400001d0407a5107841020b0000e01c260402c90020031030040600d100508005649480340d05055840250f4544141a8440c00c4c400600040c0012505001e08075a584454140760201580030b2078007400118810240350400d40071b6201c180c010511440c513031011440402403021000d009644040341140704046424905c4058191451241020059805121900d0f0850001d00300c2040c401d040540b903c6040204510403407a00030403404100d00786500c0a07017184090400240540501c602c0c2c801d02920380c0b401c0c03107a110f1101882c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 559326411 1250 559325161 559325171
    0x50f041d0702250b03060301150303050c06160c1502090d0809180f0f04020102120a0816090807090506040e03070c08010606141209010b36150105070305070510 70
    0x40e055040000d00140d031020040c111142c0c10080700340c000f8019901400d441c0010001c0412440e172000d501c069075018000600b482655103d1030024083c0d840780110034100e102d40300200c0c84554a00b040c18a0300141340e1504000c0c40015501c050103485445151541030368240b100440b00d48892529050240c481c00030759603113825110402070b0392002406d412a0780c0f05001c0400048003c4a56419044120358440c41c03360341e15440100e2600041c1400000300c41000b0034049015a00042164014098000350b40c0f9400652102161412207510071043c03a0b0f03000f41030400206056a10640e0041d4000c1d002040e501d400c030039018a1580080c1044403070f0101c5680030031560000b8031499000c2d200c00d140001488071414544801c900130b800d154000300702c0c10b0000c102845009d600c005e0a12601600c1c0301d142e03030080303003d440402040d0414081c0e684196000c282e910f002c4c012856100f00d0825420f0790552081400448198000c2ca10840610408102d400b000c24030400c00c140c8400101800403031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 559327661 1250 559326411 559326421
    0x1090b1e010f12140c060a03090212060402030606010c050c03122110061d04141501020a0f030e0102030409060e22050d261801240303050f041d 63
    0xd41150140d1000d0010a0b01e64410300250703012085a0440c0ca4102c1c1c1c1c032040c4104040c0c41241454401146103078050000079503240c1481d016085400502d000b201d07500782c181c1100b038180f511140100d40c000d40c550060740c0050200c0d80201c07004a65103005a04032407003890107002107031618041e1080703006040310118048503850703d030343e080d80208140386543c2d1810b81004440d4101a0849004141c2030100f51040c0084c1e10031040304c821548a40140b081c041030003147d443c80030401055511042280040c0c01981d42c035400041d41c0010319a000b03003160b00d450841d031800c03580c10070780c1c440e02030450100304030001c1c0b03c04d10341c0504005880c0d0003200c0c1d2403508007200ca98103000548451019002d10103000036001ca03002149035945070340207042404c41e10000311424040441d001d102c01c200f00d500403080c802d0704800a00c101140b2071a00008201030960801c480b85a074448010a000c0c5481801b03081c4000b034883c1d0058a01d12008520070750800d51108481418108180000a481e0b501081004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 559328911 1250 559327661 559327711
    0x1501170c0a03050a02010f030e1f1a0108131a0c030a05330a090e01060305010629090102030d0615090f150813051504200d0b04020301090b 61
    0x3498110448080c41150310b95541e89407202d0a0800283c14402440a0482d0140c0a40c02c21034003550b1540581c0c2c0d001909101910030202d4000b00365110915104102039001503510010081c0c0c0c40507117803400c981e41d1390381e000200c03003c4c0040200c402d21081c40d9851601c2c03075003d0400780582d041141c5903890349011040c140446200801c0c10000e9120b11a20032203001c0307030140f185a801003813a900404c0c1c005060100380c800800b40d02c481c0e0a5071515000d641c00442c1903000c0c006991007407000b07003d0a13075079041440e103400815440b00b0b0f5202400744075800c0c1800d204020141d481d07040c0180c03802c0010098407802220540d610280c3c3c105400c511242d0b6903580b040e50714014050101c4503a1440e81803111205121120318880d2081c401c450f00450b01c0b03420982c0061503810303446000c84018416a0440c441074040c03d40302102e581e90303140c8142d03a030b00030030200070514804064110909440251180c2c0380510002d0000c0c3d0f015542d902d80303000801e550000441c89000c06004442e030f1481e00c44028 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 559330161 1250 559328911 559328923
    0x71b1b050907090806090c10050c071a1b0c0a0605070f0b0c09041407050307030e102a050f0711010c0c0308030610050909151f080414030c07090e150117 67
    0x24025000b00c2d041080381c3c0e842340d03804a18030941c2c1c41d0440c1c84070b00f810902c0f4600038198010b0b900301e1340c000110000701003001d002002c101d0800b91074480141d0803003403070340d94036040a41881d034084d04240040c890b10b48520060035030940034079000000b2070b070540c0700e00380040c00544084004600010301c10025060a0243c03000400701c14400c140135280c240001049404081c0ca40001c01d6240d490304101001c00300300d80000180c0c0110200801c88000a81e080e8100201c044c180441420007c082141c50144007030302d241070160300034545000da00d80d990486122042500b01c1c1030220800b11440490010600c1c1405107209004448d642e040c203900704503140b0075900742da000b04401000040c281c1c0e110b1107080750304040c5d001e041d500510f12400024007114503031020343c4211058100100d001c1e03030740b1280e410301a90013840d540500a015100c0d5580340c1c0724010340303021680c0c052071041205494650054010700c0b00f680039503000c0034500c094425606003e9100b03130345991030400e041400c0442804a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 559331411 1250 559330161 559330171
    0x603051e040f12170402040f110d05040605010806010f06050901030e0115060207141e040914010b180705030610110102040602010501090e0304080a140a0209041a071b1b050907090806 80
    0x40b070210301342c0f5800d8003015900000c1000380900c1c1c0302e01d0881c041c02c1c160f0f0400307070090103c006216168000ca4600303800a0004032820b0301c940e410800000b8503000040b400505131000b45d0a0040a1070800c00d00b0390f159404104c07040d04050303840d01030307444402080c45141d503d88402c1807413200f5145400c50007407502616070403103d01902e48055200185d0b903114007075024a05044010350035414450002001084685000761842c442d0b0410319544c10019440001c0040f81100d603c03140c0f96032001d03050b0100c001141e81501050b000c1020508514100c00081038544080c23405a40562070040b819003641c1182d07004001503910b0348010300c0062050b00a0f4410354403418000c1d82080d25154410b0340e51840c099000d080a0562866400015014004580d50940140403c04181800c1c03500100200703991501e040c102411401151406120f07500410b160000400b004a00c00e42d5070312000c0c02c4850108981d1000489800b000401ea21000082c5101d60301a813643d4003460714108801741041c00083c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 559332661 1250 559331411 559331417
    0x6020c0706140a120902150d0f02030f04020f0a080106090204210503031f0801140f070906090501110312090109020117060a03140f01061e050a0506040603051e040f12 73
    0x31a5904002c07011080c1c60121840386850446180c00d5465880180000e102c00b83d08044100201c10b008170810008000160059000b080704140458002c0308a0100b40c034410074240e030207400304d000751511390b00005841600516101030b29644e042042d0840350545d0000035804d0700483c003085814586040ea54a034500320030607003000142d50380e40a48900c002000b501985040d200f50f0010380e40004100c402130203042008001503141044030214592049455040d40040f5200248000d4071035104482221404d80f80d820075241410015500c00c400401e00c110b8038401403100700c80c0030400c0b40d2441e000300c5c034440c000504e21070107000041600d001d14400300240f044941c1807021981701c00c2c48803030840b5040140702c040065218400d43c10000b2821120f85250700b42100401c140c211089180051000c0c200b180440950713a42c02d20413864000d101701035019000340010803002d03000380c10007540035503544c004000101c140281d007440c1440c25203041e2184503c485090301040300c1c007441d42d02c1c00110380c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 559333911 1250 559332661 559332677
    0x18050303030a020c07031209180905060103060f02210402010206010602060f0c0901031b090e0109060612050a060e0c031006030621030905040207060f0609110d0b1c06020c0706 77
    0x40800d03900c0c40050400721000341c1c00a408428081d0902c45e684c09942c0c000d040503080307400f001c8010050903640c0160012004030b401c140705039071018031074181c1c1c0d00d50010140405a20b940c8600000701001da41c00240d03180c00700044c110000000c3c100b00442c3c60744250202e91400c0c9800024507200c016006007040d90300400502141c55816010f09a000621103041680e60070580e00480240500410030800d14070034509850a940c1c105441400387c1e4440d2001800503a6240074030000d89030648034480c00f00300905456200d021450f00000c2d8414085100030840654500c01400013140440300050a032034040b0900a05680211043e8002e01503450207010883c240b404030507030405480f601c4d070780c1d12003529080d000b01070188031078000603e0020802c6483d80e09500780390307018244180f07c807108030786049800b183d0a1400d10403c0c43c42906580c58030f040070708400301480140012015503a104034003040101182075407410080015114200241c1c64001850312246041c1c099045401030200c3c0c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 559335161 1250 559333911 559333919
    0x1050c04030b04230d120b0d02090606040b030106080a0b0d030e091b030702031806030114011b290610050f0a1101020706090b01120c05040b1f02070618 67
    0x1958141ca030041c503142c1150721140f814140a4502038011203650078203031070b040800c04c00424080011400740d140d44011245004001d01144e0341c06500720f038025610408400582001e00d05543d02c541d02510301403411b500c98001c10320a4000364000c03800070740300108005800800b8000ca00759040e09603814110f208050764040c00e411540b1510034080c00042d030010b0b9182c5a841464450011410203081d624105040002c1d200e6105036a04242c0d00000350304000c0ca400c1140859040f5800142c2e01030f0030341105801110309000c02e02803810340110140350329021034060008002219040160807034a510005c07981009003500602640c407640c202c030880b4800c55080f200f1180742c0341d602941c1c01e0f1345100c98142502c2000510414007415840440c0d071400b08074581c1d11108006d401030038150f00c0c42e80e0b20006902c031160b8a1400514810f0001e400f04268201a000741150145c010508442881542c41242c04104143c45000c0180c0c021034003040140e0704194541c101100c4140b8892005040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 559336411 1250 559335161 559335181
    0x307061106010e041b140118031a090a0b0106020a06180213150915052b020d020637021216050109080304200a0510110102042705090105 60
    0x51061a10364455070001030304000c0e2148480c01403010a1240340c1105468004e40070a00340300c5202280410549aa555001c0e0045910b1608503980040084000c8030040801505c5038030240bd0490503200f003110380000101e50700c03040d5000e80103d6000b4080c2c2c05017405c3c50130036104060043d10038030008030980805600c1d0030f43c1202c1c0c542030014003c030320000105c4080d5240512036108408052030480c9070700038000c2d002c0b801421030760200c0e80b080006104a680010003100d10301400203039088041b1000040c144040380e08241da00050410f82003100120001e6544600e00001800214100da800c140e80d481d007072046030401d040b52004100c250001d41826480b84240c584840c00c0d41000b450600070410250450310b0201e40c080309507a2a800d16140180504c0d5003032000054552004018200700d0900300a41c0003194001032240340d000009003c1910075440c400030350380095408100104c0c541e002042021102003d803c0358244003010a201c0c0030403900c0241c03103504540d0504007401a501c01c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 559337661 1250 559336411 559336423
    0x100e130b0f0103060e3607180501051e06072112200c10020a050307091203080103061e02031305120901081803040503060703050906070c1718040603050a0203070611 72
    0x166040803100003030100048104218403145680403080411411403298171b50200b100012145504030703041500d07140340500b0303058407003d0003405c0d04110020424102003461290103100302401a11091030280241c50745514100f5000d28001d4140a072140c48403469444004e8400305c00321008100008107030700802c0c0c19001e0203581c0c166455400400d0200750004144489841d100b40d400c002c550b43c40e4964006400b41c0c00844010002c0348007180e001560b405810603002c00181d140d5200151607007103540d0b4800801450800d82d503002c143c0800005c680306544001d5004106401c010203d055092414510382000004081c08a42040c01480f0140e6003050903941c0010301c00c2403240c800003135220711502d0740c001da60100b03505204040a000b040c9425038450380c01521144203540d0595a43c45e03080e221410750403001002140441c0800356111807560242007240c2071603030600040c0c000100085c00342c80c6140c0080d1456000394041030110702e000c02c0500010501410a20000d41107000710340e0b100d034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 559338911 1250 559337661 559337671
    0x60f09031801051626040b030c0d0e0f06012306180d060218180601020a111207080f060106020601060c1709130c02101802100e130b0f0103060e 63
    0x90789503041d01142e038050016500c1000c40400c40c0300c8110384505045450b41c1c0b002126010200c488040350044074111021601601c00f840c1e28607180d52911408152240d00c0f003442d0528030b69603403043e100a20002d000441c040d100303c400409455050070880d04401203440c1040d40c0c1c0002c0e40184407440d448501c240d030030320490990645500c1a00c20003083d00881c0c0240010b1000d480010b40804458640341528800e580680d20105002215913000e02040c0301a52854007680c4218035400c0003a20308800c0c180a02c5000d0650151464200403461400000741c02184258010784410442e80300100415030040c40148010302e0294500b00001e4172507610024060250400008244509201d80303003280c04402c406803440c1960003203e141c0e64000c1102800d00b10050040490f082d4a001c0240569019011840100701d24901d0385d50801c9200002c41841b1010701583d1036281c1096501c20b0035036008422103031000f290014440b03040202c81d800640c490b03418145011414080c42d0311000c000e03a400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 559340161 1250 559338911 559338937
    0x9070302011b030314190b060414041a0612041a0c030708150a03050c040c0302180d021309082107201c0f08060d08090d15150602060f0903 61
    0xb22000d420300b04c0141c4185841e07140c400300c1c40014860034210240c480304030729030340b0b00b0f080041c51103c800704a918481d510800b50015070406803501c581c94103a10480b20305440da10140007040c841c070017090454102118500341c518003441000240090340152680003000247d00e0149450f101480901c6808050846c0d0204400721001402c1c140903004902c1200307200030043d00f40660740380307841c0e41c4da00c42081d944d500807410900f18000090181c000e4900d404044c545000c1c9034410502401829192010141d9102c01c0400c0d0b005003451151003060441402070840c4c0e036a840c1145804100190015425034200c1c5443c000c10001c0d90341b1850a40b512214030118100c0240703000c954916000031051800ba84101c0c0c06858a08141c001c0804c03000d10880c3d450310740340360741c644040003031510305000090440c99003001f4946072407400302058105648500d0800300080e045042c00030844528918826007841a61418401640c04000880d440550800d94041518000001396264064804410740e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 559341411 1250 559340161 559340207
    0x4180c141305030106150f031e090305040e0f160809100504021f12060f15051c140f01091b0f0509090405011b0c030806010c0303060308030a0b01080907030201 70
    0x412035201d400340080c071004000b8044c3c82d0b15031202005a52929140314041020040c241015a01a00030038003040401950900f413840a2000880500120f05040b0704001040101051240469100070302415a00ea182041c80c5401c5d400c944864003506551418020031400700940b04030700280c141a01500b1002c08070b919115440400c2030b0b084403050002003503041042d44201540d01601d504042c00e00c2220030300c4140d81e01c2c554420506142d00400c01c1c401902001c45400724003c00003001441d003148a245066050041e2050407603201c1c20200d90350030078400600c0700c041c010740e14840c05040b02d03040c100b14646040d0b4005100300140d055200c01e200e078180d00d180c01e2038020381c292141000050041e2126107040e00c0e0590082c01c00d10480151000118010300800303101d0303199100000e44c9615040b060352500c500646040420b02402c9040680791080071000170380810281d801840c1445000c900016030034005040c3c80b600414012403a40f1100381000941c2c2e0151040c080c0c62901240064 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 559342661 1250 559341411 559341427
    0x901140f0609060705061012050307060509031204030309170a080f07030b1002012012010303050c01110714010b01031b030b030f1603050c0118090e010f050c04180c14 73
    0x41d075024032810564402c5000c2096010700c140444d9051140d080d1010301203056032100d52036010044603080282030b0364001d00c000d40000d90305510440e0007051043c1103a0818072a07440b48810040202c40c100c0029841d0308509040010704c2084602c1031408508150030103808050040081d000201810a044011408035040500030f50214aa403c005420444500c030407110217070203080484014510302920010241c41c0000440603a6440300140c42044800c2c1d1031500d040340d141d0080644000c59541c0c5850040c6001140c0008194180c17059006000030480c4601040c00c4800f20a102414103041499000c800810b08105110b0a105400c0020301e8440303e10207e868082c00e140594098481c4d804e03903c00303800c4401001011070b0301c40c00855a100b2116401110801110180f1604050100005000010321500b202c100142440e000244101c104047c6100361003082d02e04001e00030340000d0a010a021242d031991070115500d05c1880f2400071034000074903901c4030f02d115014428010070484 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 559343911 1250 559342661 559342669
    0x1103061306060b0906030406022206030b1207030807300f021e0705041806050c130815010905090a120917191e060218010e0f0904021909150807050901140f 68
    0x8144074ad032621034800b490f031300c1d902d01030000c20000c80c00b0352280700c0c1c1203002001d20000017202c0c404d0301c1c0d10554060070107049558426020540404140108800c10403803000c1c0c1036020340c1c21101c880e941d541e81c07007008161100681041d00c4c1100440c80a8180c080000e0407000000c1c0d460102da1065400150240070401c0401b004007801380018002818041800003400c954806000309640d01c00c8442c044d45d40d01d04400b45d0360b58180805006040f006401088031a01ea0307844a079006d4802070665540406550341c208a03000c41c50500f0b00401c1d41c8402c14051220390000c0100c9040c1960001e2403007a0240446a83c510303a048001800c0780700710a00c40071400c920454440c10715600030000d5440d00300c0c000028541c00250f10b401c1d40062040c118a40d55468a1801000d203600301400450150311541c003442805024101d10700313807080c2080350028007100d4520860320b00c2e50f00c0c40804050346050103001420140399a0002d4031a0f003203a401488900f5110014a0846a00721030180c000c5a03100086 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 559345161 1250 559343911 559343947
    0xa020a1503020d0204030804030b0916030b0403050c0a0311060105100c140c030a030c0201030b04050c0306011d1201141006270909081206030714010503041103061306060b090603040602 81
    0x2c0141c1130b00116002003004485c070b0160003503c0c468514903c5554402c03103510b1f135410256194098a0250110403c00700340744000782600980285806441c1291080c2a28030744107108034200d0000b1202001202c0d1484103004590140c4070464000e8841400c41c030000701542450310004e4040709d50f03002c68050001081240c0c02c0e9465001d820b80301c510a40d4140034000e5240c840042c0d000c2803c10554441d2840d20340b10701c85c0320f0400d0071a25411074230344500440300901a511108011900300041075590b13a101507406060790060400444d4504014205503030902010b04040c01d9105120401d020740d0360030614460008104c240340c416040c000c2c110780a240d00040d404414003505c0c000240042c08007000007000c104800014110094a401081c0366440d0014810500342c02030051300f4640070340c4070320002d40d00b2034050b0300003030980424180040c1c24060256600d52080001d1350202d000c00001340a000010101000004e04024041e40440c400384002007001780155400643c04000b03401110315 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 559346411 1250 559345161 559345177
    0x1140c070815160306060f0e03071e0914060609090c09060a030c031a01020303011e0314011e09030206041e06060f0f0801060305031602060c1203060a06020a020a150302 74
    0x2c440141a51154480b032110007500e00014011080c0301040c04a07019008490455211303a0b58040188141074080351410001001e496040c020207400080001078030801707003070240401000031180d5162040d400c0441c1c3c804081070300007641000400240d6699101a02d02c88441074507404181c3d5140c012801d450710407160b03000c0d400f400100b075444107039506502c20b410000250b00c1c10010640100401620b003c440c00c41603005a01c200014413071084100140c4056107a08a0310781c80b000c1e00c80d81c0d240e01c0d40c103000c0111040c2e40c0d518051528266aa4071403c021603003054010017030203031291402902d540340200040d1000d214410074201d00c0e8003c15140c049950817101c100180c03900d030851184401c07040c0c030614040c0c40ca0000d010600040c103114140c1101e40c000021032901003880d01280c440065800c0503a4440d100380b02c40701d040c42091000541c00441c1048080d038a03e001010070080b100c550f0015011948001001001030f00c1c2e480404080d641f0100031801081003481c0210003134030074041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 559347661 1250 559346411 559346413
    0x803070f11101d0a021810030818310b150c21030112080a1110050910150e070314010803071a09030d1a040c020a14030f030c0d02071a0a0608010b01140c0708 69
    0x440ac4802c1c680b00c60240301400045400000260f010500ba03031060710002c1129642030200ca0740f03000807880300d034000501540068038002a04008060848040d044550f04e18410303009071405800c00d40941c401280c421202f10100c0c2d003103504052aa14101c042c141000b4903041c00000c6a541c818040c041c040e1062211200b202d280e003500040e17107009458166042c2030b441c89031600030f824600c0130740a040d005003c0c280310315922510300122844001ea020703142005150761480b000200300c458403c090702918005008541c0c034902450180310407511060500c031680107110070f00070282e101004880300040030030702c0820a6020680110403600070110b01c0303036000d850400d08039061768010503802c0b48513024025901d40b40b002100c00ea070b200d11a0303444900b60020200009082102400301801401c0071001c1e00604143e001d6480041610010703603290043e0180008101070701026000360805030404074000e0050303143c980006440384072034488a5412203c0428404008042000404000d1a60030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 559348911 1250 559347661 559347667
    0xf17090d0609020301050c09010e1509120d0e060708070f060609020c010b04110a080718030506010b0d0c020a0302030f0715090b04050601120803070f11101d0a0218100308 75
    0x1207400e800401c10844100e000b035007084002080d1342940800d4401c040c8040e114034000001c040100506003440c6441c9490451044c0f141032078589807040d003600c4842881004100d00ba030f8100024180c2030450b8191032050074208011800108000242c40c0d01e10343c080c960076a88100380c940407001e400c0980041103698408604c0b0040704805410041a005090700e04004039039000740c1d2241e041c401c1c1c44c081000300c3c0410b00803940746c500c5050189038045422408490306074803035681d00c2c00d058080e40800c4041c1d1021481c41c1003020300c0d1003055101c101500007080c11080c169408bd449018a849481300510081040d80611900d605048880b0082d400200720000451070562001c80c41940d007036546202d02800414140e41031820300442a40080301242143c0d502700007100e90034a2000c22400b04030850480302d900000070005807089008525010403407003950a800c0e80c400c083c0485d40003480d8000084d650160702d8500001c1c132400c4246100c0c6083d85d45071142103600240503400149841000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 559350161 1250 559348911 559348913
    0x70203011e0b0a0302060a110a0615031217011503061a0d140906010b0307030e0115050102010e190602070c031a090105060627030712080403050d020105040f17090d 72
    0x46404000c641500710200203520301d8400384a0040c1141c00b0007500410100b04080c0c1d2640103001000105141070201e40c1c2c200c1940c0e80344010313680107801400d81c1a204c0c0c0424010043c40401c501d60300f00c01c500d003c4104119002a80b441c211041c400c503010412902000d802840c8a608001701503d00001401c0344018a03004040403036125110000c4030740e290000305154100c014482a004441c540020040b590900c44080026032001d0466014540c0c0d94904156245080c015100220170320103000d54550301d444c0003e0b0a403800740a1a820940048407100301029031030842d00343c03054010100686410940ca8840b1001215070400340c202c0b4a81c1d4091980d03041090310031382c440c552031070092010b0748408081c8480f600440e42c0740724028540c406c40400e1501e05181c1244c49180040071580c0055541e0603951010380c1c1d50000340c9042c14000350910a000c0c04021400c0380784050300c020085480c05480311001c845c118103004001c11246000c4001451001050310300c208001002c0700154056 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 559351411 1250 559350161 559350191
    0x40b130c18060e060715090c0305031e040f0308030c0d060807080706020705150313021005090a08060702030405100311040f03060e06010b0910021903022503150b010507020301 77
    0x188806003034028601c00c010504a1003048001000c043c040c00950601c501c81d5030f0301c0c0001c4001d81e60b0005103a82e4003c0c090228280e14440c0001314051030145658041c95030300303008540d019078840c64407110b00700f0080040b14100312050045079003040300380303407031361106010440700340303e2918003056160904102281d072020104080085a0500048a22580d666807041c0c0e00c400e41c5110700c40d80503440c1c9142004a130250710055600000207542c003000705000e035002420030b81e804540c0c45c00064000c22505154281030003614080c26040c0014241031400b200001c1d580c0c401d9016090046600a84507070a00d4065080505081d400400c1684c50b25290200c4010310b2050344000e441c0242003040b1705124600c0400d4290503540c400954528254500086c03000148034054540b0842c452110b00e06281e22040342a005664030030f50140201104d54101000024128024880410102c50341003000428100e60321a8440303200502180024000d00140c81c0d40c05021000703034042d42040c044040b9200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 559352517 1106 559351411 559351427
    0x190c060c060f050c0904060f03051b010507050712021527012a0c080616031d0604030804051002090114090609060c0307050c040c0e040b130c 62
    0x11044403110111071089604684d6483d001c00ca655985c50140140401400524202091a410b41c4c41e51519543c60720303002d94084924001061469000e80705890800390840d0549a100b07130394034264942814110b400300e1080288400d802d0031940e880081d601c00560b400e1035400c3c42d5410359080003440807855040c1c2c1c140410030003029065803106001140901008469401c07040c0103150882c144921500506426000142000f112044110300c88144410520700498031000544026200200c540d0409045010b504104800e264106130340b68003c0307100e8811640f1090364070b040c1d4400c9000c0c02e4489030024440090203000c0340703440000f0306250200141203907e402e00404c001f500b6980f10180000558101040380800d00c54207105041409202b40c805001603600700c2c40060074600e106060b41c0c441d640e2100e4101c0d0310345500030500b24442004c3c00410180c1c40182c00500746034 = true := by decide +kernel

theorem cover : BRFrame.Cov 559172661 559352517 := by
  have h0 := BRFrame.cov_init 559172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 559172661 ≤ n) (h2 : n < 559352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
