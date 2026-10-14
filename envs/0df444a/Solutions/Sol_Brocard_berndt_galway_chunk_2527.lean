-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2527
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:58:13.696494+00:00
-- url     : https://prove2.me/submissions/29ce61d0-759d-4ba4-914e-749dda3ebc6e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 454316546 ≤ n < 454496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 454317796 1250 454316546 454316557
    0x307091a030901060501080601020304031506050603010f03030212030601120c09030215040609080703020d02091008010501150e031c0f12110703090603050106021e01020c0a080309190b04080307120908 88
    0xc03035604c0d02c0b10008030b650190307148074890780050700030b9818640f660f01d030040000c880c5c0a81242c459a55000401c8995889001c0c3d406050503a00148040741540f402030710b03001c8600380a1002d10028010031102d80c1c3d01c03608039080080c0f6040c01103034101c00444240d402c021941c000a40c031003110414010141c001d400940215020f41c0da80c0308c41d20f0f50f1513004e180c850743e103404041d420a800000c2d08007d03013061040603810082030752a00204a40c0d809040782100d60070307040758488884c28110410003541c4103512000f165411005031566581c012003c40d546114040d24500b40120700c1015903131103010700502c10241020b50703400e001d184905041408517900141c8100c002c05d06003c03020411030712911405050f03400e590001c00d61104156022400340346e0a04500c0d07440d41d000c1141114540091000103007040c89002d005441e0b0502400c854217021070980c50805401490a005000c250b02840741a00b080e00a2003a0780c0d00e0b00d4402080b2111005807164a8246040c640c2990800100c80300604 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 454319046 1250 454317796 454317811
    0x280906230603071710020f16030c0b0a0213060e0609040612030809160b1b0f0c09060f03060a110c06011e0609050904030f0e040617060a020c0307080307091a03 70
    0x1003046446070013503507500740c245244030800d6001d02035906010320658000c0510200407844030742400c10311088000b402060600440c005004100e0850030041c0590540b0f42081d8001025410580404403078000345281d4401c1504110303004140c030146490b9202212007041003e402808119210321000001c00c400711402c500040c00800050600c00010130f9000c50104502010340203580740505070300c850380240c02c105051211a0f04032800c1480b0800801d42c42e0f881a00141c454441c6110801a81002c01401c05000f400e41d07020884580d0b50200303040754004d400031800103040300c0201b0001c80c14050a0742c54800c91090400120344185a00900c030710820340c000c8070001c019101e42c07007103030381d180c107842100d4205520340080b0700001d0240c0d0100e64000154030f440791511055400040a452045c0d11600610b07172007039a0103441d0b60702070000550090481c5002e5190103414002c146e620f2040e10405401e104022010865552188150100802c1d0b800c08845581880500c1d00100764001c2e00c904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 454320296 1250 454319046 454319053
    0x1081f0f1503050c040510151407050d0311040b0708130b03040309030b09010213141203180a080c0303070b0a0e030d0b040b010e030d140c071409280906230603 70
    0x13204510f0b21380100d52084804280d5000f019280007a59440000d90140403400d0000c0303ca0000c07003001458010348046800780700188000b1086400c0901110605003034884030400800c403e003c0c1348031600417658dc295009032003580c0d486903180c40a051503056040145051400420b100c2030642c400051401c2e01e00030108201240c031143d1700381c0d00f00c1c4244c00509401e00305540d01004400108000b40d01203080140450840c40c0f1a5074032241954082312401c409816114a0304100d4140a90300c0760281907090300411410b0881c1e0b00099030307401580c0c0014110f00000b0f001680788074040d00070451810b81c950440c2d031205449014580078000c44401d0328059480c000c1040d205620a2008007100400036002d800f40006030717007046450b554a0000c0c0211103504000f06101600200081d00c020300c400111010a500707d4420000401c0025007442032159844203540c03000300d02642c0c40500c2101107500007030b60750010f181440180111100083d0320700c10740d031440030b10009806106c03803041d2821810b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 454321546 1250 454320296 454320313
    0x3150801051b0414090711250506040305100b1302040305033604020309010603140604120801080c0d0f08070c0504110c1207030207051017010e01081f0f150305 70
    0x9018902c22130304a0403074240c8a41c46818000038443d04001586440100c404162400a240c6070128492240e144052000b0040d0900940c1d8100003a1500b120560700e8103195480f0382d6a90300031440b003442e05076502c4200c046290703a000900d88031080240419520f5030380e40d003085c0351680c1107210b000e1015101c0c46281e801c104c0400905500c0028046c00840c0020720f601e05010081d0001007400c0500c3d942c420000c000b0404016003984048600d40041c00e482c40c152a1800b540d22900f016407084c4444071005010120300825007204151060300c4071001030880c0e050445049950300000f6203041c100090341d07030030b000182110744141c400a0314180318026a41c2d60220b824403c90f0800d00d002e0b00501c2ca491030142c40c6200615609000348111102e4a4072200010300301c19050800d00c0214140c80900d8414600b668080303801440003881c0211198581480c0d180c6444c40c3d484802c000d10b104200c600c4004405500001d1340341035450042115901e05091009220a039000980305442024807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 454322796 1250 454321546 454321591
    0x100605060a0f1d0d0501020904240b0a0228060b03070b04030b0915091b040603030807031e0e01140f15150c0a20010807021b010315080105 61
    0x807900c02400a54941d103808441101c201ca400d8042c1440c802c10340401c190035482c580d507040d20071410b140900e00042c1d139607c90000b000110b40c1e488000542200d0011501c0d100700e61300702d003480100c40400810325520301e0768680c100d0510140803101c14076000140250f812440390804500411841040100f2400801808040d6213890500c10311078104010441480021038031507803075030403040c040704440c40521102250454403000702c91207400c5a1080044031b4a500c2d025143e8034150b030303084ea0100141401e41c0c4009250000040540e408d05844901810600c002c40c0c05072400040c070403c080040c0f0040342c0c1003030301801d034075500c0d8020a0034100101d440188640c00290140c080c042e807030050980b0140504c58025070303032018000251814403507560348900070300480149900c0f5090b065403511200100040d481d21403182c2504014150081003c42600094103245803510841e8880140e403082004a028000160401d600100040400101c195054201c54026103464000404e129110b94 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 454324046 1250 454322796 454322809
    0x31b061d15010b040512010221040317130206030c07050105010f2c0a0c0912151d0c01030e010e0703060203040507080a15020a0306120b040506091501170c090702100605 74
    0x203030040c010f0b04100810413442c00384000d0919000d1100050305105492030340d141c240080c900100a60308000c8204402c056202030210244006603245041d5400c01d11030446901c060900300074042c450000204071407a001c1001e5481d00d0798400006e004c9503840b510783c081c0e103401034490201401c04090000011302c0603036041e5480192a009110301941d40c440d2400e01410440002e40f05200d40c0c1c0c00007182c95038040c1c02400308107000b241c16520300b00549050904813484860b0601d60b5980e2010610680f04021449c00f0540d402403a012a48511200c20f15006110707080042042c1c0c402c401001040000b02d40140d80b082c1e010304183d9044036a18210700792540c03442c1600610070310042040705268a0281d000c0d000c500e07002e1a00290b80c50319400c58500d08001c01c501500d200c081c03c01044108001041480e80c02465000540506020a18400d110030018001c0c0070b140810144511400c0100700710030000c641006001014500b04814080e4071101c9c04072010991500700304001c076003401d008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 454325296 1250 454324046 454324049
    0xc0d0201020c0906060f0a0509010f090e0f0414031606060501030504020105040306050415020a1808030a1205040f06090305031b0306010c110114040f09141003031b061d1501 76
    0x1a0042c140340c611a10401c40302d44001480c4030b60001051107810030201c0d003000642500121a11081c4d6140c04620014081d41d0b4170000c61410011080001c0c07142141c00b03407507141c2044000e0010503068417a4030b00440c1e482c88200c8698281d00c00494121324504d2a0350006070f58500500c400c1000f292104011415500121000b0740401d030100070400008050f0b503c4964440d010302007001c0020a41607511041c1c0c0c3c0604200e0001485003c0040d8400d92418109001800103000940c0307490303100c140103003035402807a004410b110f5480002a06204107410402c1c20786901810030850400e491070050120b0304203a03800e04402944100328844c0c0c044080440380585c005840b80d002214181d5900f1040007841d100300760401040e100da1740443c41408000d000a40307640011412094182010340048911808405803440341c6c01c02885448429090001c06898061034060001a15120350740c0f05410748403001000d161400401c10300d02188039150b844504906002d850800150120450b0341c101c00307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 454326546 1250 454325296 454325299
    0x19020f130e15120f0d050901080f060f040c0909021b0d020708030f0918010306020c0f06040c030308061503011e1202011e0908061006180b040b0d0e0f0f0c0d02 70
    0x40605880a03e0900382000d00e01c0e98000441e403a007515550b60310700302807240c0030440c0802d801081c11001580c00c0100b041d4424414001115645003410001e4403501204020502131a81c4410844915202c2c40b00b40000d014040c80135562500d590700c120010f0200607800403401d01541150032202440030488504407003810740250f0501b512010782c081039a028610f01070380a49c02c1750382a041000c001c0440d40c0218041c140050f2114418800603080c0031403030800480329081001000300086501140e0001c0c9c03038141c60f001c100e40c0d950b100442e000d0b00c4900507449008102100009802c0d001c0390000d160000d40400416130956112141c40c2000c0c4c1c00c541c003d0201d560701d60217542600c02c4402d081850126494610310b5940e48040050401c0c1003510582d0209050150501c8601e41200c55030b40e0780c1e0824800e000c0c495152168204480c011030188900e0884002078000c5004415041031950103600c074180c50070307840140380281d5200b54400c00001c0034040e18100103800e2a0074400c02410680 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 454327796 1250 454326546 454326571
    0x20f09090714040603060c0206040c09062d18150b2503120c030f051b0301030b0721150b03160e18010f08070902070309050919020f130e 60
    0x52440300710380c0040d00b03070003143c10980d1004000702080742070140b100100b0a5402902107400d150030f18114290003070f00702500050030310700100401034070b100b01c0c03401080101e400c145000340c5015860700b815426900084080102c0c2d40b0541103c4810361201a03102d840d821f00340555613440c1850155401108000e20380081076400d0f4a2902a04c0a40d0700d008a22902c0d00603948a159402c4504541504a444001a544010b500340400c0c0e607128281c0c11140401c41a9016299910103503070f14481404001c2041000380007080800b4050213280340c2a55150803040035101c1c0c00003101000701494010781c1118034090000203003402900d804c4a020743c1e101c070316004089501030802c2d1040c40fa5211000d80184c02c642c6000030289400c0d850314060710026608222040c5030003455494003010f60440290140304000300d10009811200c7c03c801c80b00142e8007d10580d071215107544080490b440c482c03111600015400003040291801401c1c090b9103034502000e010340310a62100200b5045900044402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 454329046 1250 454327796 454327799
    0x10060b04090b0a09020f1806070816030306030f0b070f0309020a0b09030c0607050c0a0618050f0609030a08090a17063c06040b062a010f1503020f090907 67
    0x10007074002e881120301c007a19070f40000d556a01e896089070710120442c1c0c1705010203d001c4030201c80c1204500c02000d400c4817003c0c10702c202c0703860325130040c403c03100c00082641d20400703420708050080d04600001c507040002c400092403141055281010101c074480b000800b440805810240039110ba440556009000020701504100341052035030701c00088140d1600c6003d1000740390303680e603400810a151042c03025003014002c25040c0444410160408010310100400300d134485510481c210044a01c100e401c036524800500100708944106d0100c69010b005240f00ba606100c4000003c03e0702400a0303c90002c0703180e81d05202c0058a1041e042004a9000600403a03200e51200c5440c2e0f135594401da904074800043c050011a0385203201c3d94600b81002100b003001203034a4a8854040d070340400b1703210700380381031180d4604500700c00c1188201700e040241183c0007144684250b11081c2d00c034160010422541c1e840b245680310707650113840101e11030750325030a0f4040c003410704241144c003072001c620050084a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 454330296 1250 454329046 454329059
    0x3150c1b0204050702010e06090705010206011d060603060d120201050103051c050315030102041203090801050a0905100e100c0c0b131a2805071805060a2a05030c10060b04 75
    0x6143c090411380456407100e60540320321a080c002903004d410084000d010340c80c81c0c0000a0309181050f03103c0c1044400840031500c4091603940f01c6507004008581481e0707240c0d039800008822448800018107014100d43c00c04001039015841181643d020744110303034820030404044840c481418000800054003800400c0110b4540781e07641d4160329006001504054448105040303001c031060060703000031840c4100f0000b01c0020b1007400e40000d11000103100c000b000d522014ad0b0340c500c550007240803a0ba1600c20f002d41290900c080c0382420b0b4003c0c8144a90500070744010000c0c0c1c00c00300e00759000541c1c0030100d5a414012802c0b50840c0f940921300c034001040c0850000100600108a42c1480c001100400340c49000c4104010544001305000255428007150051444400c07204078020342042580c180001e95880060301ca1485092038001d40c504030701005d003262200e8040010504204800382d40d805c000b0f0101c00703132001010710001c98900c032403220461000e6400310320414080440400041c05076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 454331546 1250 454330296 454330301
    0x150509060c150421030c050f2b090303180209010509040305220e07020a020906060706090605040303061707051804052505011101020c03031812030103150c1b0204 71
    0x581201500790b0314411044040e44806803800c03a001c80c2c240620300d003140049030001d0035480010156240070400809041ba02900f54800c0d0a40811181d401107080307170b80c7c034844640c0807495500420503000a000809485d1001c2c0080d800100c002c42d003440d10100610340c8000c04400c00d5600108401340c0fa910b0705044c083c000707a01800c16420000c0402c071b404840b00380d07140407280328004000e0515900d483c0c20809454114080d000c00210341084c5203040250752080440c0740c00c548101d0758103036103a0b101d01d007010041200d02030040c00182458200010f16400d81e0080d000c5501c00401c0003403d0202d510840c1c1c59954500403a91700001000110110340014400e417503006100340d0454141c0e070984401c01c18060341ca0295680101c030402c1c0184481c0d43e10884043c2461101c200943c00c0a06040640c0c2e160300004102989111205442802104081000d908000280702909a8030358480c02e0090320f6010001030a02548d0502d804078030004d20603820100805042100c020b40000c00c3d030f080001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 454332796 1250 454331546 454331557
    0x40e0f0c01140403080306150c0d11150c1b15060f0604030c0303120b031516050a02060f0403090f080a020123070f1104061707090c09211a09060115050906 68
    0x1000a00400302c041d08c101010010001582c48600500207564109002020750b540341030140080e80149140b5403000881100258029984880c66a2152010031007052024a0b0409540041c404c41038280d004441f20100c42d401050140d812540300101303107083c000e95128074800100028552102000800c0c800d0442203035402600c000401c8250011000924101990003013000c0303181403600780326004410208011050b1002c3c24414103081e18004081e4680400500c0d0002c00100031000404140c81182d21802070302002a12145054869281c165900b04090040b40480c0c0c050580145413141402c0400841054280c21781ca001c075655501286c10030601c0013264042400e1803031048680c0c49016900103011000d100700102d2030324002461400d42c056201c12a02e40c5000206401264400410420707513800000200102c1841015180c1641d1100e901400404aa4540000120418004500495005048401c00c0e40c0ba40b054544406c01c1600210102e0410807200381d00d41000d001801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 454334046 1250 454332796 454332799
    0x190902060f0d090c03080c0105070807020a020d020303160b10050a030c2303010e340b070f0512301302030307060507020309010221030103021e040e0f0c01140403080306 74
    0x20210004d0792810f4003200d0b6034004070b46001000c11000364001e02403190b60f81c0075450389450a41410b1500d80a501c50001d00302c064051564604603900b036460030000c407800400322501400c2000102d081c0407020745801d480040c2d01214612000406182103005401030b00d40200003180c1341490018070035000301040c00d1494000308075a1107601c0760341e000c0c842c01c04041400303005800d461b07800d0200071001510301851204400140003102120f1800e14045e0350030303915001c02480e520a55401c0811031503503a00c4008003607105600c441c14000c211540a400300820038090f030070f000c8847d0403064a0015204c2e07840c0002040c00c0c00040c09120050405086050025042e240780c5403442d2504d00540c4c0341112440096400040c001c80d295a04200d0408041e0705038090700511101080305034103d110610029126443d6000303035072048600403140c005903040003801007092541d0400d070700b9100c2450031590400b501805040f90070710350290214206a04040b120703646040c3c115a5072001c03940015003050b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 454335296 1250 454334046 454334051
    0xf030c0315041e0f05010b0318030c0a11010806090f0c131703040f080607020607260f0714180d060902030d030915140a0c180e190902060f0d 62
    0x140e925284280803405031051079803d240070b007284a40054074040244040001d00d040010012009280c043c0e0b40c014003040c1c3c43e8036410441032081032030341c010001c80380224020744480104000038940a003203420020780382c0180517641c5204028005800301c41c02070b0040015400524030010000050154145600d1181c4046403261054a485402000c060800d0352000400313200201551001400404020004290707900c0c0002009403a40805854407052000e207040600310001000107040140149560004861030500d1a01c111400243c49800120b15214820031801550b00101d46c0d281003d413a401200003951010b124180c0c01c034003400e030303015a9035a1242c4010b941c10300c040b1075000901e0744d001c1a401e015007001c6010403100d007140e000040c94000d01d441c41e0710810700306507403050300032600003030380000e508090f0b070704d4140345015001c0592900300101e0031020302c00c4414012620301c00e500340c25881850346d032400c40f6600300002c3c2d44064103000c8a869034508034000c0c0003400400001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 454336546 1250 454335296 454335331
    0xf020a02031b0316030203090906030c1302090a0306050f0f0a270f0602030f150901050d080c070e01270b01140304060f02072306010e0105041a1e030d02030f030c03 72
    0x804a1014600360840040c0c000042402003485d01040340ad030032201c124050714086040c140001c151159109070300300d8441d00401c0003150f643e14401c0c010003c0d90450070500c00d61402c5129442080e004441010700f801e406400308940e820b240c41003123104003890344210070b05610442ca1020082e680c8030120781199500d0b0038400061894006980503160b21981038440382031003290300c240d114020304c00794050000c94004200c4d60380c665440024054000020669455243c1440c50600e40982c02c005072504914000090034004826250400b20700760b9078200319030030401c0300403003501c0c003a02603a40001c070200311801e29044410001d5401a116010005800d00e60320400310983c0c200e005d060755903103020b0a0800d00a0022a186109154200c002d00743c19814400301d440c8641041c0113031800389543e1504050f5200d0300122180b840000200660351a41e10040301c5221210300c3c5e28213500134000d100e00d0a845e2800001070700c02c0914600c01c114216a00c042c07202d03030503030001441c4000700f002940c03d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 454337796 1250 454336546 454336567
    0x71104150e0112020402130e0609071e0f110a0321150608060a08010504150615210e0a0f1403041215110d090302060709030302190503120f07030f020a02031b03 70
    0x541e1000305026a01e11083d8900b010410042b807100a042406100d1850b4001c0c810010490340f5510b019410306054502d4201103000b01c41000c07100b0800021446000c107188141074100180d100740d0080f004051003c220846180d0040e1880102c602c1240e01d1002424050603004210803580b01c0400f40548402e290384003051800d6410995040c0c41d1103680030031071001d00c0c980c2c0c0100806810340b08840010005d5007140140040003000c2422046c03251910f0300c89000d291604501040f1240408845580015040000c0740c00224901210320040c000e02082884601005650803a80040c00d0841106034039200c8082c484600320a2400302581d07103a00e0700804091001a04800c541400001400003013440e019190075800b4250350140500d240003000040c1d80040c2d400403105610383d4405402145140c80c2c0c0c61070152000e003645059290f0200150904e007c14001e00c03501203658140b0803080788040b850120f01c03840a840006070402c000131403142c14902c14580b03c060889080700e00c0c0140307080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 454339046 1250 454337796 454337827
    0x71103030411180405060f190606110c09010806040f0809060d020d0c0e1320031806070311180a03050d030c0206010e0603061b0f071104150e0112020402 67
    0x403412110140041c2d211506403c2400d20344105031510b00c005200760030991189a40d0703c1d0028141d4885424100005882c079422950200055550b050140300090700c1c0c00300174254a604c00400d403650712801480d240989440922641200c0008025055946540c8c40c1c0c50303070055914100f40c440c0c2c03004001c1a94903864030001400a08214031005031501d0503003054409541c0910001020010f16801c210100d90702c0f01500819010441d8000078030581c0c0d66107a000f40e6654080050384050080100060184900c1030201d12510010a8602030750b500d40d025802c03a200800300c0e44090300c06200c006000307400503481d0440828000c101801d1035590755a414a8064907105202c0003944a514100510381c0420046014100b40c00d0006102e203800300100f5681c10000385181003520340480001400c1c1404021145101d054040240e91119603041544100003000002c5010710314000040c1030151074542d0720816194a074208d02c03241e0b480d001b2803211581c51104c086c0c0e4070039800c00c042c10303078085803a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 454340296 1250 454339046 454339051
    0x507111302090906030a020603070302071b0b04081c020a022e05040f141005091f03062d140a090905010e010c1103091905130f0606030b0105090907110303 68
    0x20259950100c0c40500140f400003a045902a40c810007003000140d680c1820b03a0707409030040c500184c80e0700803424043d90b2503491990341c0340e218a60320408a00c1e040c0300c000400036500c8100c1281c0e4291009008061a10044040100140c000484090041c58850801c44018176401006110940c2204088124600e41c40b6148003003400000d04100d188960380c43c00e4020850f943da40314640501001003480525040d58903010007030000b80c0c902c955a240080350b01c0601c03480d6000c11400c209a00050000d0455014a0040b820740b1103503030041c1e1544400448a00070f0902000040300d2801d91654001000b007803042d0781c05400502c0103e407880c0c50344110b419140c02a8000314119800896840c21110408101001c200020618940c1c00381300000300d4440100c162807a48113400800401d9002121a8000c01ea01c1465514400b550342c906401074200f01c0ba1903071081001a654082c00d6040700e5044402a01007281401620020f01e069501c20758002d80b6810408510010800c505055034000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 454341546 1250 454340296 454340329
    0x50114070b0a09110a060804060b04090b040f030914010f030504060222050406090c0c080d0b0d050309010201060e0601090303030b03120c07030515060603060909011b0207180c080601050711 83
    0x40389030200601402c130310300119082040e2510340000d82840703130050046074018009400d454407081c0c0c0400c0d0392190341c0002e040c0c94104d01002c440f42020319000c40140c01c48013054001400303501c0c1c041500c001010300205440030513101c0380030f225510807041c4c005e08001001503032640d90a110f004140200385540100c407240c0e144410709101d0034030080108840b41504407036040d500d030005e1000b1854114016000359600304041903220410f0300986c1003e411040005604a28544034003401c2000c0000a4040180309800a01c54252103042c05003041600300c6500f40040d800c0c14040011038000e90003012005400b40c15034504441a91004040d94020b1042182a030f100d61000c100340641400415454503000e200c48800e410300c01d0000307410b4000a84a103100f016020085501894250303c0807030030200d0102a481c03aa080c0c0d040180d215980c6d4450005081c64400300003030b5801c1203102d0041210100d803140704081e1200c2c00112000c0c0c00c18542143c0f110032000c02054181c1da01e02264010460 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 454342796 1250 454341546 454341551
    0xa050919180302010f050c0322020406030c1d062b140d0f0503010506190e09011e060c05030304060b06040905010b04060e0418031202070605040f02091f050114070b0a 73
    0x1d036140080c21910b4501c07142e511a8a024140501640380104617a00083c848000c05540e1100c4603a0044254030b840000307621a1400000000700226000c0420850740d51072b04a28002c1468407420103112400c1b40e80591001071a810f8400c03040c9004540001c10352041c0020f011a000c59880070038580752070201c490240c3c0001c045070945584055001c60000c0f23249030503130855140c5408900d8070702070409201d00120803100180a0703c0d10484904010400080002115595400402c170307076200f1611004a0301c9940800200d48580119400c185507540031000b107285540b81d89940e001440c801c0c44c0140c1c0200b0410000a844205000e411302070b228900101381c2e120310705a400342103066109140350140f2f00300503041038680310500581020a030141040c1252102000d1640000d1240000040056140c07405201c140030f00f54400f19070081c429a40f09030281c40e2102e2144801d07803800389491241815031000d00255100d419040002d03802c0c10308890811186035600e0280d414200e9405d4007041c7e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 454344046 1250 454342796 454342841
    0xb03151f1a0912190807031106040c1502010b13090606030f0506010806070f0c0303050c1b1f090507060507060207020901060201050f06041a06091302070c0e01140a050919 75
    0x5400e245100380819142d00810031381d4945421808030900d00e0402a26980c004220f1105050240303c2a0000100000580d82103180034900303944507403402e0040f001986852070f0b108122600510810500440003002030741d1004039142440058010709400f02e55164550000100003608204103009541c454009080d956061144007890b24400428400801c000400800103440d04941d01003001a09403901044a030f85880c10761402d840391000b0704070040c055043c074098103500410803058070800c0321304110901148a50328400ea881e8840017030002c2e00000410045c007800b41004111282c071400015040076081e800041401340240e11140250351590104007840f80d42145140c3c0c06001158100a942c131406130036600302696285441c024080022288081d960b80120710390036006040c0255030310449032500e190100e1303a0748212104000780703600100d90806404003042ca50380c0c001e8000b0004a14110801c6071960010300048480c40e02c108499103885a14003078061012140420744011380c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 454345296 1250 454344046 454344049
    0x240d06050408180102340503030a02010608010608070510050c0109021c1104052e15050405010f020c011d060903011a19080a0b0c0c060a06090b03151f1a09 68
    0x100810f10a6a045400c00c90820000140300410340c00e01400c03420700c1c802c41c460000b104101c048402c2d0411036251101090300305a039941500408140c801d000001e0114643d00c00070580d0f221112b01460364080d10f20b1201d428101c0c840c070042c1c08020322500010844100c950041914098207a58082000401c0401c2c03000b484015403048219040a95082001d46030a13034002c030000106121001100060b950050309481c40c800010016144441e041125105003440c090071a0388103208a6000c12564650564200c1c001302d80d0742c04142c410785500b0085940c001c0180040c203844416a64418404d008403206a142407103040100c2e0180622001400c8820b800c000c551210800c3c2482061036001040c803161070041881d03c020303540321810f562140c4811500e449039000d0000d6031040da12070581004200112500003034102d904d100700800030060104141601c1e5081c0b402101542c00f01440030440c40d0520041c0b0780340410800c2c65181001c0e89460484842981e0b50070080707520703500484d2101c442e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 454346546 1250 454345296 454345327
    0x5010c020904061e05010602160b0a0806120703170c060606040f0b033304180503090607050a0b070906090501050708120402040609020c0303100902044a0915240d06050408 75
    0x1d02b55900407142070030032100700104900707070080040e8050001e441060400e1501040b5140203035074445845290741c494034085080540016a00030018412075003c81e010341800c41c00c89003501c0d00030404500c810304000c112419a130001e4101c00c00c0c1002100f22446500c81580503001c0c94616960141c0000303506000c00c41900e89850344070321005c008800904c0000d0000044690030007003958016154519030400c0d50515499800c040c00c41c9880c0d104004c911988804040d003a1910b03611074060550b11440111414000c680c40100641030030070134a0801110200030aa003d132000b08042161919840c1c03d04c142c1c1c2000e07407080c1c02684044148414080c0d034440d65000b030280242c1c00c5050902c1c20400781e501010b0315860020200c103507020b50195881c0c100305420030440090307907002d0302d15a400702211103040c1112079090f5070251009854107102c03c8050380c1c1c0104072480081901e42050800c80f90700c1020701078126071150403681b401001803001e014440c491401130241da43c880d400d159401d0174 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 454347796 1250 454346546 454346549
    0x1b080a12021632010e0118030606032102030a09030209100503012d020a093f0b10050a0b090a080d051908090304030f0f05010f0b030705010c020904061e0501060216 72
    0x4070000200b01c90f2980703176407000794841c0d080024640940b540030342c040d09103210003007900080c050b9410f243c1c0102c240507000b0104103007100c0c0c0d041c0da020818035200081f0780b280541706c9240001811030f001040940f0706109005d410035841000030320071607079271400203085a20f4220081c040c20703079034030300da41c2c100c200b01c030418454284200095143c419000c02c010041503580c040c00b603004565a494000240400d10011410180020f5440c1c058200d94510140c8072101801111011010400500c000705c80f48052411214003174103c4080c2820045c20264a41042d45082e42200f92002e00041038101005002c1401c1510b444d02e075642c142ca02c0c01101d62440800d0400c0500081906100c0c01c071500004440403a038100400300403884092074a5942d840040b10090040e41c28604026408200c0d58081450118108c01310742543d1340e40e00040d80c45521081d4042d40c030040900014000c40ca16070410582c9401d003080131a480c0130b2a02a01085400a070400001a805202240d160070100001c140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 454349046 1250 454347796 454347869
    0xf0607080106020d11030a181502010f111903020f0d0501140907050a02070e06010509100e3c03190b10090b100e060f070303091b080a120216 62
    0x2141701d603145255943ea449140c43c00c00400c00c011031450300100203040c0c490080c000520182c45210321180000b4080e02c03000440b003284d14a050f0415111110507011100301e008848140300c500d280d0f83c1d400782d00940000420511b40c1e0410080301070b255140d44205e6000c0c04076201c03a14a00c005840901001d004010300901c14420200481c40c1c1280e0006000012203403240b5001d1929511440101d442d801184615a0003000a10304440c103d0380003159480c3c50003050b0380c5e048908204d5528800441022407010600d40f08554081e5105401d094460307903182000380489000c0c4c00f54003401c0e40c0f40358040b00d06851a65103013040c003040e0b4080c008020700905620f00148280054a00007490125001400105100c111403c0d42826255582035900c0f125004080c3d580300e103036a0a000d00507000b4694111044100c4025801d01100c6594601080c1c510650040c40d188000382e940d0cd40c0a041c00c01c800d015841540d0400103001c0c1405c0d01c010103042030351410102c601e00d65442034076a041c16107131034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 454350296 1250 454349046 454349057
    0xc04051f0e160c1a190f020c0115140f0a0b07030203030405010c03140f0604090c0f090e0703080a1112031302030609010606082409040614010602030f1b0f0607080106020d 75
    0x18011076014890345050900c02d10340c042240e02d85c40d031004600303143d00c1d80d140b41c55820310081c45102021540649544251030000340080c0d015a090303009506914000e07a8088407208400c00007a0505200700c4c071030401c01910f8094005e80340c10b84a1466009140c007100164000800c200802c40300780582c0c40307041d0207400c0c280510394044051a400c83d90080205240000b070344000b90a40d1340d035420510b025900000d814020030340343d07917030b8107900740c501e00452203114180303403000b00202000200901141d40041001e8180703034014008540380034110002c1a403e21070f0241c40b4920f01c038040300450250700e544107d0220915103205040c00c1c00380c010f0003240c075a40b50003c02c10900b40c00c5074080d5805003541c5e054840d0065581040301d00e075400d1085070764001000380200404c201240e480448802036441c654191a0790b54038040303a89200d13101146103880010720541d240310710001130040210112390305030703000c05640794111441c00748100e80700000210382c90700410000d5010702428403403d43c0351405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 454351546 1250 454350296 454350317
    0xa03110d020c0c1804021c03030f050f0105032e020c0304081906180c15021603050a02090c030c0403030c0602040b07110907050c060415090f20120c04051f0e16 70
    0x600b80c0c0000504545807000c2c00d51f80320080511a0340604004030106804012078148904507095043c82409124002c0c407640100e062407120141208001c481c581c661554101041048030010f50040000501144000d02000c1118034090044032640008008003c5000e4024203140c425140107000d0754144401000300000424180718050301901c049c070312102c2e12070081010407072901c244d0b0581c141d0b0b40c001c2d01d84040308100010038602412402202c1401c1c00c3c5d295444805c80510064400c240b4080c0c04200420000303004940800d00700380290300044c1880c0e40c2e10100455a80301080c04c541c0c001010040b001c0328a461071a0641090b268604242000c60001d0916502c090180000d407050798091500c544000094004903c11640480484d080c02c0f20307850040540050402d0740c0005088400108101d41400f1080c2103540c3e0078080200074100500b000c0c8001410b001d0b012080e8a10403401100503072100003e203500030811a013000182e49071407020b41c1000d040c0b018840c030412030025030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 454352796 1250 454351546 454351549
    0x9010306050d081e1e04080c01090f030f03200f0106081c03020c0f0109081b0c0105030f090f06100f05030607090302130b04290d05030a03110d020c0c180402 69
    0x3514440d059002c910074001551035951280e41c01258018a07000c2c18020559401711410340c09007003184c01d00401c4030301007482c3c1001529031035070900400c03650380408a02080440c20b0740f004d5400f40c601a040c0340c03500302d00792032031103001d9416400060002e034001c29481d1490b8500740b00300001041e41502500b04009020480c051280304850858105074020500c4c6034911001e204000400303404d00002c02100718a454403c0751a00203690302e14102040c04400241d04802042d0f040c1c0b040f8050351094513643c0d540c14881800c0001600c0c0d5522441844018080000100031141c092070b890041d4005851030400100c040055036041035009800450510440da50401840019070b58112802c4002100d0501040001d00085510517071041c2003c0d901a40718076200d03c0482d03820b4007681c50402d03200c1e9400c207101b02e20021610040855008120360510b0a20a51081450000f000303080c030710b4030761200d0200084c2d800c41c0c070300d2103403a4021314a2040145024640c504202d601340c00c02d404c03113250540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 454354046 1250 454352796 454352813
    0x30e0102060f0a020901020309120105010e0f10030311010b0d03081b090f0f1302030a0912021b06130b0c0d1e020c04112712030c0a1103120c0309010306050d 69
    0x501503c1d03581c0d00422a50520703030082c025900d04d036101900300c0c1080c03002204800d029010130b00c9282c41200244020456009a40100502c20350b0340b0042c2e0501d540c55658100c840c01880a012481c0795600c10b14108199a0a0151030019000f956000140d04015a8101113044298040049880204030b00c02e416150300d04440c1040d1011154446030303603c004041000502c21400001c10b140c8004204548041c09601207900103000d0280230100700c1140c0c1050b80d665103055200314402d99011001012407401c00000e0900e04030301d9200c1d203032a650315992100140c001400d0203015800030301036805c41907484000e00c6e060b0000f03c0707000c1544c81c036080406920b404400f81005c2c001ea072241c162031a6156580200c4800c00074000f0310a251038003044540906044501c00c45116a0640048200d400b20002c1a100d1040041000c0d2911141640d50140306100140106425024002c26694540d100310040c080d000e1200001d19583c00c60340c000101287c046070001445001400d07082c3e004540f014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 454355296 1250 454354046 454354051
    0xc0f1214040311090a06080717010c05040302010e12011b0804050f0a02060307030207061803110106151704050a0501050907062307060e120d0218040902033307030504030e0102060f 79
    0xf40e13040d003400e88034581c1003809040c0e681c2010b0028480d10b0f81c00a011b1300030303c84021418038910000c00001407406802c440c144101c1c800030340025144899410075152101da100d0446100000009404140710050064980410701c9070001c15950404c20061107018445003541001041c054003c850a03a8001102c43c000a4081c2c020140c1c041130300c0e02004400c0d0700500202242009494924165160007081e0368086010300d03031a03500b00040000c2280030111840c444c4812522440708403d00d91010b0305401740e0041041c0c4035481290009004034400f071103050301400080010300b404034100000941501f03881030b0900714017a407103254440542486010f54400320f60048001ca001d040d08134141e41b030b003c1ca07013550708035400002a100500c1074640d80142441c02084450100c000c00e940204021034200c0000a03401d9003005003103d65002081c0c0380c01c080d80c0d0310455540d5806503010012402048200c400d400071960b0f800c180028150441c0b588440800244010899458038020011406101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 454356546 1250 454355296 454355299
    0xc140c120f1f0e12030a0c0206070210090201020a0b070903051c05160f05060903030108120309100b01170103080703030b030c0a06080c04050306250f1d010c0f1214040311 75
    0x1c0108112001c03140303803c866a0100c0803021100942c3d07200343e20008a034001c0c5e6451200303a00d480d00400d0154000304440344508155000f0380503442c0d1442510024041d210070881c1180207022440000030111500c0500403100c9a46001c81c07281140703015443c00900c005011508c903003085620042a07400b008a1380440c550a8004401c00c0d000d02e0400302c91258041c00400c02c0c01244204449600f000020390b040321414030444801c0071703080c0986a010310055920a4003904003015034048080e0540040c00d00d80e80624003c803145900700145680c0c880280c1044900001c001120020f051340f50141188510085000d014461f0190300003800e220f40d244510000d2046600c0020503440f0040e00781e4005110241c01e0b00c10a00e4501f500c00840404106c01d0041c3c040040061500b1070700c5014200c85d0415141c499442c0d442e00c0a90880c1c039940b8000e11541049101300c4843e00140d1820300c03011402c1d109000c56a85418080d0f07001d004007070720050800d22154180010030100d0422040110702c00e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 454357796 1250 454356546 454356583
    0x6020d0c0201230c160602030405010e100c020c1207080f0a1208060f041116060509010c08090303010b131a03061e0d060513050a0c140d030504150c140c120f 69
    0x42c5c10030710f00c0b42c0d0f03060307080250100d8408002c0205010f01034001400002c00d40041d40c0004006806650845007071410700707001648140310a032034504000346260a40d00c01c01d0100c54450b039a8544940c5400da00350010510782c1c00100d000783c00c10104203050305004a60703040440300d03854102c010400301e40c4a82d100030b2040703803034400c1c1541d102c020300d00b2284180b941c01540d0011400c0c50400c2005400c0550300194150320f0640020b01c06445000c9032402200341d03401039071540e480c02001a8868002814003840341d8022280060300e081c407844405030b040030340c50021741c89180c100c003041103404185190010560703002d800c1100f95a641c2c0040d4140551120000601d0340b5070034081c0a09541c43d14008242e441205d810200380300203004c1c200101d400c5400c0b210300c1050054107016217080d00b440020007080c401c2c8001e0020069403403200c002d44015141c41344050b01243c46070039032608040070400160b004807509000c54200041080b03203005c006401440d0a040341c1c1009540e844200030320080120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 454359046 1250 454357796 454357807
    0x30415060513020417060601020a02060c01060b1c050907060e1224010e0114090115110a031d041107060c090f0902040e071b080f0706020d0c0201230c 66
    0x2241588003402038200501005511440361082800a50103030144038022503015501041400300010365a10424040e80901030100c8298207110198000240202d03031552a00004503c0c800040b02600c4c20710003140030750203e00044a610021180080d0402c0210b4003d20414020550031980d2051242010707102d4030512541c5500480c14243d00b8080c1030072185844401c1145200a2050300b81652000c0283c841d081e40d0b1540c035280707140c5410141a40010020004010106041c43c013030340341c2c4986e07040100303080c498490428100400f40504401280d0f080321608602922000b104c104281c06540030030500f03100500c584468016540000c1c006502c550210a89502c100b0511008014502082c0703250781c1c443d2210400b94200f070060284010586000803842403003580207d48190f0b040607141d103564074944a008442c1e02c04820001054070800c842070002d00640b0007402c0000800d003000072200c0103c1402425103082020706044600403c0c48c095244080e108039a0b0800d0000007400e50f0792 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 454360296 1250 454359046 454359083
    0xc0109170102040e100305060601170423012f070309180e030c01092906010309060e0a0c08060109060803030a02071106040909022107060c110a03050a0302010f02030601050304 77
    0x9101c3c41c1c000300842c20628042c400207529017042001a244258151b49095a84000440c0e522426001c021100204000414080358a002c05040011242040441c10010a25209081d40c1001048150340c010710158080c201e081000024001c141c1124501c3c648403198400a10701185030080c170341620400707512840e00b038019510001c00341c0c40382801e40303842d000941044c40c000c0a00410a444418000003030740c12403250390011107681e2020180954072030325900011002000210411181c49590310742042d0712540070403001c10241d1207400420030302420003190904018040c1e2044401d1410400d040c07144090210a0b40c7c1d01202d100801070726514503050005c2d2252004025075002040002e001c103042c60a50450704c04a0700a5502c80820440d030900380304c41186000e0306104e00e401c41d21050085510540076040320501510b1008440f41d154070018005160a6004449546c414481141016020700541c1d00d02181c0000031030461a1800020301184001080101010320303181034841034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 454361546 1250 454360296 454360301
    0x9030702010e0d21080a1517100e0109110d0b28020406050405040c11030307200d0302090102150906040f031101050916090203060f062d0310080c01091701 68
    0x4107401601c0d50070405162119a881003c06018004c0050b04990026070351040c1d500903005c401310f49a2028001d5464100081c41c40c0e00c5000c0d07076100601035030308614210341c154042c8021810b070801c000180081d0500d08440c001d141c144000c0c2c0131303042d00f0200780b0120b0b022041d0780b41e00c21095540310004100384c1c12115030080044009004c014800b14011030016480707070180003a240d05580811900090100c00c1d6420102013011000d00e034010070015140b5441588a0b962221400d9000341d01c10559000950400040c281c0d001c000940c04078220074250b904000e8080106c1041d80c00404170308000c441c0c030341c4038140104050710071500c10592204040c0b180d20284004070298000700114140009010740b50200e00d0418100e0744c07000d64021504444030f108a03030007144014590000f640d15001846102d07080780702565001d00f40d0303409280d00300c1d64020040e840c80c2601c20703500d541e03032804c021002060180e5402503080e0f94014501c810b816604803049030140e07500c051000340c2642041010901 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 454362796 1250 454361546 454361569
    0x607030b1002150c0f070b04060c1b05071502031303061a01050c0706140c0a030914030f06060904050102120708010e0114010c030c02030717030408060705030903040b07030507020a030305030a0b01030509030702010e 94
    0x11072807c01c04200901102c1d40c4484036a02140c0d9850306602c100c0c445510300e241c4c0c40c02c0041c0654101c0c030000c0180c0681c1c1100300b0310240311070040d82e080a038210107050b680d214075842070304c1c0191116a8a1809480420442007500d002d083c8141000c0c4901030407961881c072405208103000715602c0d03c14803882d0100c2500c9480b0341c104111040080203150080c0060b21602c241820034008041c06401481e010401c54041c000b40380041c50700355949801c00c240100d0240041d1215542042600705420801c0c201510807446a00d400d5215407424840c40c2c01041c1c16480640443d890180703050303007030380c1c40b41840e80226058a0300f032081c5080c1c1d000190030940c2c0380e4080002c3c3ca0013150788990001e004000340044072120800d036809680c07800707004d1715148001c031255107181d08104000d00000005030054a481406850014200b101d66404a002502150401d8000c10404000c010561050303001d4109000c40c2032805103c2c0d030400c005a140d40b4041c100f002814000900010a1a522941c42164 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 454364046 1250 454362796 454362803
    0x20a0308030a1a040b10140d09031827020901121806140105090402011101060330020c0307050d081611010f0e060304080a03020c0607030b1002150c0f07 67
    0x66907030410102c81c1c402009840c1040c0d25843d24985090503d02d858400c01741c030361401421603c0d4844102504131486010f689180c61125030500614942c4045071060500c0a8841d460701d0007048100500f59020281c60b0740454554444805260003001030a014241140700c000d00261b21101c0c9140142c0c0d9044984d08052800751810300c80030030084803010403490b068020b010030001d0040f138840c2d00c20f50b0740090154030782042419000c01d0065100e003004141820080c800000d401e51039580d40e14044841180300302c160000d100e0340c0846110150940b48028240e8001040a0601d89020903160781e10361150900c21400080c0050a11200d40f049945501c07001040942c01040c1c4d14016120300c1c404c81c80e00d4001012019211245401851106401007009080c41d00b0343c0d50300d85d1190020303070049205030201502886803070200001007020500541003510085251113280f003c2c0010320510f8207180301150b000e541d207400034038401c912030340d0040e00d0035642d0f81ea9000310074038410300d82c0300e290b1005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 454365296 1250 454364046 454364063
    0x3060b010509220b0108060307031e080408010b210d050a0c05010203041b0509100e0604240e0a0c09120516060320070b0f1f030303050a0f060b0d09020a03 68
    0x940448048104880003e030400c2c8003000a4a180c400450302203500302c400e02c0d0150700100b821b10200e42d840b4841c10003000c0781100854020329964850700300e50032990040923140c1d100c0d00c00d0310040c58141c0d1107042c107407011880d98540c0c5c2180084559104080035800061007000036807140b90620410280d0313491500400295641c0c04d081c508601c50b040f400e04070340c0d455500260b01042500d401d4420303134000c01d001c0b00b03248801420001c187d4031035000a0401f0307071b0055a80c0481d100d50441c48131103030315810303d2000c980c0340e0301e00d0080026554500103040a55151801050101c180e40080b01c450580301512026400c60b10b6614240d854400d410555441160464000180c0194150441e01e1303a940c0f94081e04000303a45c1e40c070080c03145000340000144105501c400140e84408052200d96100f24410105601e104c4141ca1008e1000700d80e41003500020f8480f410032521684501611400d00c1c0f0400301005103518000b0358507054090030300110b240c591640c02a03400e641d1404c440101840d0044e280 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 454366546 1250 454365296 454365319
    0x101202070812010501050c330a09030e01020f4201090c0c030c0204091106030a0c0e240706020906030a0905011802060d0e010e01320403050403060b010509 68
    0x107a51641040001c110003486920000c070781c652192065803102e080a20003002020480400480103010000b46070011800c2d42601c40310030f2150454041c0525880d5500160201d440e0400a010000c1014181c0c1503511a0400140701200040c5c070b60403804143c0900c503801c1900d5020b071090203c2e03844410000310300c0030038500c082000c8003080504840c030421040080d40500c80c4290381c41a643c14015001c50b00d03440c1d005015040a0f080300241a01c2a118102c200c0b55540024540360816a050317650507540714001f14039941c00031307c1c82004400032229016040c2d041c0001d0560300707509c2403007403800742c2c00486d01a041200a40507a03001c100c008142949070324006051000030301c4030071829902c42d030034544844141100280c9400c1c7c850f030085c0410b841d00114045e003c1c080d0aa1000e0400c00790340c0d80480a03c8c0381020b10880000358481c01c40b04070038003025200122040342c03111010080c041c07148248400650414226000c07039a00010218072a1742c400e00680b03440c0038a1031981c0c0c2219101c0318 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 454367796 1250 454366546 454366553
    0x100e040b1e12060705030a021612050a12050f07110f071413020c2a0312120106140a030902042304140d091206110f04081b030c10120207 60
    0x15255000c10540d08404000c1c000b0400d141d545405594071000b0800800100710b102d04039800030700d86c8142e0345602c0034000c4425a034601d107806913100784000045002c01c1c00c5444030fa004900300009000702106004e1400d124044107180d08000d4020b1092180720f403003821401a040c04030081d120003050940c1c0849549030121000f002680c04164481c810000250300115518801d840608e0704a00040c1310420503d281e001c2690118041488081c0301da90304030005990410008003080320314280a51916039003001320304a4001a00304106020b143c10851014121020544194a002d8600860042c1c80c50011500034198100e04013060b0546c40c01000700e1081000e6030302d0081b4810a104d500810001d50071a17140c1c1030000250002800b005002c0020281144498403d02d0280200180c000c5540701d0301d82ca654803018640140d5180410100041c8809000d2000d07405224282038005500500009440320701284e41c1c00d220b040d15940102c06981302d80f10050100742e1082007156180f20b5802e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 454369046 1250 454367796 454367839
    0x30b131b0311011202040e060d050f1f0f06030b040609061b08090c0a050d1b09060f080c0301050105150304030207080607050705070b0910050f0706021b1902100e040b 73
    0x51014089000181920250120b62089804403010387c4041e040b035465482c02c0280c290071007001543e07a4403490440b0354010000b84a001d02d903040baa80d4440b646000c5840040c00d03079080d0071b0158400f61400380100045850001da20b94010781c032040010b070036555403603c3c42c010403000080b40341c2143c0c0400044003064110340c1c4903015032954403c950748a04900100444184580109a0090402c844040004800c0014501110818409070100c2c42e115200302d02290303c0340e406040725200c0e501041040b01d01c1030203007a442d80342c02d0300248029030609003c5a001000000f6000c0000f000000141c05e1501c28400c0341c2c090040441600c03164100701c1700040c450740201c42c054410303008000c40020800b0003082280e101c0603014160502c81c4554000546150300030100f01941c440081024100040340e0380300500680025a00d50345402446104003842c2031a000284e515914039400250301694030400700084803429807500d0380b400c100741d0002c14054034908540c0b54000710201e10420b100308107071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 454370296 1250 454369046 454369073
    0xe120102041d0f0a09050c040b060910050a17010b070f020612010f08010c0516030c0302120f1306180504020f0f030a060503010b030a030804030c0f020910090501050a030b131b03 78
    0x110f6003001180c4608074003000701c039604500103129502c40c01c10b0403100e0030103802207a5000e070010f28560a102c410310115107014030310300000c0001200080c2c070040791600007180e420401880d2690205642c10306c0217880c484d20444c60060000c04520300007004541d200002c4800c24221000840c0c015691050741240711851802222015420603049414151107003080c0c1c0c03640c08500c05448425455914156212511050140c0450203160840060560700d0303002098128200354551360344a40211301d203c1c0c4100c05070094400c00c20f5044403540b10002c0f10080704184c3e6403c40b00142e80711a441005482442240030030b010584022080000d0005181d0100003103580641c000d0200700448004c064551741c2084c0020086404003003c01d02281c0b0481c2e01040840c4920808580c1c002981c0003d40000c3d07088500803003034240c1ea00c091019007030a004190041106071110300e100c0d4119603130900016001031544054111100885c0306000c0864090444051071050086081cbd8490401d000001042d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 454371546 1250 454370296 454370311
    0x2120d0905040c0302070b0c090d0f0b040201020c0f060910030608011e060b0301180c021504260f07060e0304032a060801050916030e0106151403070e120102041d 71
    0x20301404030b090311301a000301c0300d6050b8088840101580e034030303125415030740008042d5a0002100c003e614009941780c0c000d0f0501c18054410710340140341c45d1000a1512a40400c180e0180568031840d11158864a090303031210a0700710b41c04208010410402c0b0014150303a400031515600b4009030303e003410034842050180480751a030602c40da5403246059500b602c0300780b05020000041e507612402a2005500204140141d031054950807a800e140703408008506990640d140c3d020040c8945104103500c904441e1407408007865410007440400f0701280e4015640d01429194a419484808403818070840b0007655008200f0602c4621003400c1081081c182c01c1120305501201c800401c102d40508801ca0403140b00905041d07055560041a0036610042d1001e00145920785200c440400703401e0244d10050107a00601e8000403511282c01040000c0b0001a081c1c200c1c810000e000c280c079440001442ea01209480181d08050b14105503402803040d540a01450140303520300f503029841c03e80344940103089 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 454372796 1250 454371546 454371551
    0x20a02211005070f051b070e180732191e031e0219090c090b07210210020a020d08090c220f020315041b08040f02120d090504 55
    0x1e4003075403402161030a441000c04980e05400359580140b0650040c83c95040001c080c0301d0226010307007194944038142c6c0108440f410340030100902c070000e180086a044400c032000b0300c03283c1c4c0390840300c14045407130364a500c8042440c511881408c042042c040e0750090005410100486000a4505625010790003852401c07104c06800c840441e80e00e0b5070000a40f40c00c80400350f254a6001450748580343c4801d0101d800c5101c070b00d4840e829010040d80d0b40010444050b002c81c0d1070790080340003030401415030040b0068004c00e001001c08242948511079154207851301105200764410790a07498044984016070301c240c000508480c22503400301d085280300c107494880d004030752640c0350415210304003062a607130000025510f10b541c0e4050301c0d4051030540101c40c7d00050701c101071001d04041c0c0e4005c84260528400d8030000910504091080c035078030346000c0001020202a91000030039013040034001400e0145151800402d651f1803a4003280c20180301402c6810414503d40013030702c0d0400d03034030405200d5803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 454374046 1250 454372796 454372813
    0x12060f010303031a0621060a0b0d1e0c09060e0103090f0b060301020705030705030d050106050c03120c160501050405150f1302041506031b023c0607020307061514060a020a0221 77
    0x740412210300b660900600c840c1010ae01501074801080000382070078000442000e90075100c0541c0c0301c2ca070341c0740c544ca40e5814101da041240142c4000d0241559504152410f02c0807400f00b8200880c9a001541c45030f07007031000385c981c40000b174068024100050403c3c0000100101003000010040290100720700090001760f903200c0c1d0545103406092124541900200000d4000154000d032280e030041301c071103004d421b12504241303420441000510845140c0c2d901d8060000f813005c00c0012207082042042d012030186082007a40a070240d0140c00081851400c9083c07404643d51034014080303444048901c800c4443d40d40d00001c1c0a04451030511041c0c040c04030001c5d545501c04a1078206400481010308011001c0c030b50504d96415000d86c41200c08191002031155101c414001a03000300310315802544c4807402824200102d8054800344c488a543c40402004888078600080300264000c41d4002c3e200c5001c21026410030f00351800095106004151241d103120380b46040d66030300c001c50000c6a854a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 454375296 1250 454374046 454374049
    0xa11010906020f1c020f03060d03020708100f110306010906050304051005161b0305041e09060305031902032115042c0105040f32030912060f010303031a062106 70
    0x28813a040074040c01b10000c000040c802d042c0740800e10080c9209104541110f50b4070302c412810304500303400c0010001d03111100342003a0700040c043d4101066a400071140745041c00b400180110711540305803c01c2c000040002018001d00b400f400d62050040074050000340f90448503070406140c511402004030f121030151050000311088992a040d0381512110315041c14204100c04c041049011a0710412441c2004924552680600002148200300031a2a45080c2c511084c050055030340b40d00441d442030101c0c252a07000c140031001c83c840d10090004081c0c4404001603001000c020300d80750810705203020240f8030000c2100d44d14082c01c800a10407802d1109850349400e07180e040d00c0c040d1851040d42c8201000c102a200d0141c1400e1a4800108090310100d08209803461000c4141590750400b10301120702e0301b0074503001034244c0e10042c09402a450042c520b425462010301024041541d07402400040c00b41a510003514401c00410741c603210300518940f0b403521801c40f090010040c102c0000302e0b019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 454376546 1250 454375296 454375301
    0x703030f030507020312061309050a060c020f03030403080f0712140405011808030117160305010606021501033c0804050a08031201060f05120405060405070f0b0a11010906020f1c 78
    0x1044210400115611070784108000c0c2d2325040c0d514401c4580d101107000019504000404900b4807a61021230780414500010341082d0720312101003c550010820030002070f501030000e079030100c0650f0014400d0b8481003c102e0308010302510190005140031503550040810710200c52083c1c0c0b00300c0c0280001d41e034a01100c42145000350004041102c20300050220440c00528049440608000c41d24151421088222000d259a1090712580d540d54014000e843e810702256002a0003049200c50039451650340b46991240110b0b104c064806e400701c41c0000758140350407902e40c00702c85921404620f0060800758826441803182c588034540d407240c006143c0d60f0120540b800001c0b08042410350fa8a807000688601d2801c01c01e2a042000c1008501c10348140c00c440349015900820041c940ca2400d03103042e62629406070002c001d20a010041000f1303400c4802d00710f440e820090f181110204101c0b481580c050075260b480100164000b10304540350412b0031003c1e240030348880d408881c41c4108021100e04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 454377796 1250 454376546 454376557
    0x20706180807120908030a231606060501020c060702010f020a061a030f01060305032a0a03030905250b2a010504020a06170105010305041406070329300703030f0305070203 75
    0x352600705000c7d0740e40356401030b0710150040c800c03480c4d810364084807044a07405603440741396010a1140c41c00001000d221443c0f02d0000544020b0009000c144020000919540580c1c203000b810407006100b00681c0500c2030040b17a121a07485581032041d014001a886000b00308190118041c7c401c0715803100c5071543c1402400112074210028614000c05040400c50007d1040d054050f240450301c0384905886007003010000d01400fa58000909d103890349022030611220b10100c48070400880f03052070403605a199910102c9105410b90340e9141120302030344400c04450714100e030925594a010428490041d0020351290703100710f13200fa0f5225140c410a0701c140070064003100307100d0781a00042c07000d0350080d40810f030047d0041320506014400805520f141c00000ca840c0c4c0c0000342c030b442e404114403540c2e1200c0c00007954445c1303484c0554044000401c1c80369680c40c40040362000043c11801094091540310080c0108403010b441ca015141d05025040e08500401440040d182400241d0304510100a0b80ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 454379046 1250 454377796 454377809
    0x90c090415050c071b0e06180f06030f030c1c08010305060f061f020c040509010b010509060f04050901060203070515060906040f06080d17011406030403030207061808071209 76
    0x707030642074020707094000d040c01001c86025a01c10005075005c15051042d0040600383c200070880c0540c18401100300080024080502401000100702035195040100320340c094807400c0c41e2501580e807400024a000040d035040e41050000280e909030584001c120100f02d801000300200e11404000c104071402c0c1c03401d11000e8030540003480840c0c02c03041c400b1990780d0090740007041a06102d03a0a0307118200c801c1441162405079101a00000c0700741003900980b90b21501c40802046114220300020340180328038500140701c1c000c0040c0c091250006030f0140c038040d04015103105910740e100c01019680c2c0e4800b0005985511807000440700240d803110600e0312404021b40154282d4840700d041c003000d410464440c0700e6a589071200468803010804c420a030142040d40c502d003040e580d0400c0b4103450a0181c0104602020084481c500740e11030104880d00a80e16280050381c40c259820400000c10b001da298480f501c101148000500401d103020b0066540980040d84000c1840f15059803008054803810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 454380296 1250 454379046 454379063
    0x10914070c03031e060b0a0e06091c140303090703110319030c0303200928120c15030b01180621060909081201080a0b010510031d0105090c0904 63
    0x10310000b4030130340010800c001080c0d2031040080380c106601094400c0e42d003005115400105003044590b5110b900710369200815140a8a811000c0340403440c034024808102d040c4406110300c0d101049140c000340200070040c44283c0b43c0780c1c10725000554a66000b8441542c002d00d01c1032441c5038902d0081403841e100c0d00c50f9409540381000310340d0290703941c40e5802c1003501459940e1110700014002e4550031420110070000b1590340748030742000c01445400403a9410001500220b22456881c00e082d168404d440c403200407004031014602d49507240a4a41d0005032203032400760309441c1e0540e01904440d001160907260444840041318000205056500c41c03100090410042e00741c4440c0f186200c10100202c1240c04540320b500e6169103001d032401d264048560300000903080c0c54281c52240643e000d0a5500e0142c078610b8040c2e00e81440c504018090a0311441c0c0054075a10300310301940c0404c804059800306a941c0c6517920400301d000707020880f101c41090040c3c0905540a14010030981d12840e4088500c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 454381546 1250 454380296 454380317
    0xd0c030b10081b01051b010b1305090303060409170d020a03180b0f06240c01150f18060e040c030203011505090a20070b01080d1d2202040e01091407 65
    0x15242190201d03d2020305015040007500c240c14054a00c0d107444900342c2001051a04000301840004648218603a405030300c0d110500500301000710441e80c010b20f00316008141c0356040c0c10301e60300480005e404a00102c500007a038155611881d00a4408000161030800c9400c1c200400d200d072559050000401c5100500c0000b14041148110941c001d031010b4000381e0a55002c40d0104441100120200141800400e400088c0c010901a003130341c0c9407400c990001440d240868003290314055000320703020031a150402c0110138240d50300c89402403042d603a42007441c0c1401d04059a20740c40b00e00003a03000754200306011444103005181402101c1024080c00301c40c3da01d1400310002080503040500000074150208000c800041018000c55030103000b00591303c1d40340449103072a00020401c00014807070200ca190130410100c18920003550000d03200c16015a860401d140b0882410490010000e840441c011480759050305d92103050312481c500800501000c80c00d114040c0100f00c48580000d00745000703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 454382796 1250 454381546 454381573
    0xe070b0d0b031002070b420306070306061b050120090f1e1e0a060503070207080c0a15020705120c03071d060d030e180a0b0a24020307020d0c030b1008 66
    0x40a5034029015115810301a03455080b040c9640c0c0c40e070070f072102a90b507070313410021152909115480d0000700fa400c040001d0351500c2000303000444001034403d049200c1095a6090007000e4000011d005011041d460501010300f154403215040034407194000c688089409035607082c01c0710f004030303060b4030003040c001071441860030030104007281f06001c01000380702001607400c3d485141040010704416100c05880740b030007000082c5850354503030046125501a460035080c5440c1e249184050b11001e10584084954000341603152241e1a440260019918000c1c0c0401540219010080b40c1c0308806942c1c00300d5032020906241c0b561090714891140004010540c030f4074014003000a070700d2103401c001110340489000500d6a0f014008c046810b4600141080350b05ca8061141d003c040400700c900b00311003400c1c024a41018100c00090000d240d240d071034400811402041500c050702d600800c40c60540c042ca182c02c3d01481c01d01d21044426903207010101c1c02041c0310b0032055059030070b1900148480f0348a0034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 454384046 1250 454382796 454382821
    0x30b130c0b0702060904020301031101140a09050402090303090d030f09061d040209010c080a03060302090a0207030f0f0c050f15010611100908300901110405040e070b0d0b031002070b 80
    0xc0382e12200410101c05c080d1a6070014600070750041d001804103a01c40c0001405140b1180707100c09428008018a902d025084000355007595400d071801a103881307611000c28a140700b183c0f01c9a50004d1100d45172820035a01221000e03806e01c00e81d4881080f2a0350345d0050f10382c109001c10880007091500c0c00710101d42017070b6014200030201450090700d031015580300c0201681c40466440c00007510b4802c140b0a6081401c00507801640c002800c61508102d91801081000d03003d211400300b06100c1c0310004114401c0c2003e640c01070700304065a50480010741503603130303c11415800307010808049000090319401f444070700c51410b0f0620041c1464084480307c1d600104030103101220307105814003660340b42200d0540c2c01500e03200d400000c483c0002c1e28242005003060010000142a81061302804048900c2020ba03012124255030101d682070403400c105013841555000303282e0004012410b04c0b90a000d90700404071421040d0280c0b030030000d41400c81c02c287c0c40345d064090704046121000c2441039503601c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 454385296 1250 454384046 454384057
    0x30e060117030721020106050105070308070c060e01020f0d06060f050a111e01090c090c200a0503160c0503120f13030602040803090102151e0a0908040f030b130c0b 72
    0xc25a4946012035486840400c5000807600071882040c04442c0383c130b50240300e4100900b40908006050500f0303580e009080000003400c1600300032200e00004204102c580005800c400201d0007551206d59904418045800030040f14800d1400d0400010740140154004088402140e4503240341500410059030304001010b1200c0b21072040c1e941f07603c18440750f580440b521a240c9030012038421450708180725282c00c030350481c0c04024035120f01c030082c035600f125500e040400c1070340780c0d0000409092000d0f07007805040d2801618500002407800f01c068060040b540344a807285c140d0641d0315072034500341036603810602d4072000030140410400c0f0003004200e003c2c1c41c20008031405c00c5070380c64490340c8200c00d03a00641d0005d10715034000304210745150780500c5013500320481c9400500d000d00c0d00d511a0010240f0500c10f184242c0c00e0740000c00c800300ea0580152000130b4000300640d0355076030f135400325100b44040f910041e9120140280450001d4400c621240c000c240c20130b102e20070b01801c0280119690b07208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 454386546 1250 454385296 454385339
    0x207051c170307180605030105040c02010212010306020702030d0801080d050706090210030608010b010804050d14040b071211030a0e090603070f0306020c0105060d0c0e0a0e01020705061501030e0601 87
    0x11154520002198058003a0050031000e4140c0e44a0402c910081e002c2c6103044c080b0800c66855150500105601c5000e481c1142d904440115110307a0400050b402840f40140480e10808400008000d1284940041410920a408980e4844c401c2c14080300e40b41700038003840d01143c00420f525036031188280f015200c8a40a0b4074001840c460303550004030041c24a120460109803201e004020b244020705c21a420301000b802d001c00b1a04e0b05565158491484d141800c00780b2442e42d1941031907036504d2090b02c0141401000740c2e0b82e04c10086c1000b0341c480150f403122800003076031440c00d00b0780144040166400040b25450b400304403076800b0f0030010142002005180c0502c1001000039000c141c0c05074060085000750b00040c5e0b208040a080703400e454005116034060030343d028005000580d0305150f001203d5541c0c110803025140c0049805c090511f54044402542c008244101400b00100d1001e02540c0c0581500c208040500019019501d0100240b01180c0040c0f004102c580c04022550400018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 454387796 1250 454386546 454386589
    0x6190c0611031821030c03072705150702061615181101051306050f09040e1609061a07211d010203040308090d02030c030d0309170406020705 62
    0x85141840140da00304031164016400b0310390f40b012103150140410800302e00d9140c01026603469010030305841e0311001d896843c2c44140000060300892003140c50982800118810610802e40000000c0c42c20303905000700c80c030405502d9034601000d110748045038801c41d405018103003400c80070400000941050181918040310100c0b080c60416a0751081104061540d0b00203480f50289092000c8519103001c00507050240410110b070200500c1c4000c101160303803a1074410740d07602a07102150110b000750b15aa9401504022185ea040403005c2032040350124504420390309075954080480503508a441100c3c443e910070808081031103030301801001024000c104840c41889515062031000d55510010740c0007400a140040300302d01c0c41540d00d18810002d200660803e402d544400501f403148110a91103104450100340854034148510292101d0040554905400014010723010302000e481c115200d08520340d0743d01c3d103030060005550684025038001c0032400e00b0107050140340320222001403403004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 454389046 1250 454387796 454387811
    0x105010b1201060215150d050d110708030307021207050a050d0906120c0e0f0a031b18090201020622020307080105011a04080703060c111605090603032d070b0a06050a0506190c06 78
    0xc0d009c01800252036125641e080d4483c280e250b105041601e00d0f00701401c540c00820900c020241c0c0040c4101107210884005955000c0d9031520a2400b402448002d01e180a11102031001e540c00404031011185280ca8400507241000d40c3c8408840d6440e40f03400104041c03504142c0305040141c481c82d11464081c1000320400c2d220345407042c0c90301d115901024140d400703800c02d109218501c1401d0b0380d5030300305000520500d03c2c1a40041d4440c1401400d000f06848066481c4040d03e58415132700c101d4a4015041c0d0b0324240c0c481c0c0d1080e020f004240504036200140207500f011b4840c5807012030f021684090054034940703086984890180100c488504108682104004658441400984800d4a01482c882c0c0002d180c00103101e01920300400e034501c40d030002d02200a610004922102d0348020124000c402e0341e00034282d0200600812401070300610f0304101b0440c10800c0c40e0b100400317a0300b04980d034803000c65035230703013004031a108086030082580c814484030390340540182039042d4003a2042d1800708154 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 454390296 1250 454389046 454389053
    0xc0f180e040c150801030c0306110702130b1c02090a0b0103110412030813050d0f0315060305040b0a0e0715020705060307121d030702010507050a02030105010b1201060215150d 77
    0x1000305980985180186800800804603d032841000080b03560030180010343c5142c4520001005611006c0c01403500c4402100381c600e4035100b15120310754000c0800301d201000039034280040c0354a541d0240114a11746440b90300c18440c14440640c01d9008002c0c1c01155120707007d8a001d0034802040310705150321076568080e40d200700c0300a0b001800c40000700300d1010810b814006e10a03c000382c18461149000ca02d64800700d100880c140c0582034040c1072480c9400003400e0128000c02c259640c4922070300e04c0003c0454a039038190000340c0128042c1e0100c02894954112201c2210030307080c015041030f4030006003044200c1904003c4002d1003d03c0c01500c1403603696402203007855004481c3c1c03600207400f0303503080d800705010341c0300380905480ea1032013039640c2180c44840507035640b00b0040041d0500c50086200d0042060420500b20200d80c050000d002130f59440800d8501500a007407180140c0c040712001080d05031001440e5440c0b040072803440315082d1140041203185101c500c0f03c443c1c00c10745200c3c000011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 454391546 1250 454390296 454390319
    0x70c0807080a030807031107080c1e0d02100b011b0f20030105070905010f030f0204050d050a140303150f0301090506070509130203041112031605030714010c0f18 71
    0x701001c8000e01120b03480c9240003020b442004141009041c41c000310070041920040c1540d806590180b40b980e91120380720356162406060b00440c407103850035000c40c2d1514090108040e0412500c0c3d4007100d20001c5c0d410303034100607a1041c00086001454100c05040041e07203030890020490b000b01003000c42101ca03078a070100c1214100b01c04069002200303030b40c0e4849080034030507958848080c6c41e040c500c0c2410039000034540d1003203010140405854616102c00d84100e075040fa40101000cc00c2460060224034003d500c441460708141c070a81c103803000700f400020010003100d10501007011141840254401044a0f00251008503078040d03580300e451000090b400c000860003500b6580700e490300c0d4250041000109110b00c600c45c03410500500a210008010100c50b0490381c0c000c80320021420f0f400714503245540281c1940601c66040d086204050010100042441600a451054800e112952282c4c00d0711080e15044c0002100855450300c05d903c120302000c90a60040300704029542d4440e11000c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 454392796 1250 454391546 454391549
    0x9071202030c030708161d01030e031930090f02100801080c01050c1f0b06030f0402040f0501030b180708073c180f05040b0f0603060912070c0807 64
    0x20044002007802566030f041148180c6c410302541c0c00120f01c400d5110010b1075060240c045010341d00241480404683c0a034012000000b20b2030100e0344c850030741e01c406c02d00c440501406000424203406d100004016050000d141c0403402c04080f4008060b070004038001450581c000303954007900300004a0044c0d0340c3c07242d00b413410100c660f1440c0e055410080e42500701201c071440d0071705000301080f03025a907141c00700f6402404560074007900810390180300c010002e0f12b8001c1402e9807001d00041004002001e800c580c2c0d003d24005d0710704012390008520008200c900078000540540c0540c0c00050010644334902c4001070051425502c0440d5610b440b5480c0c0b071282d42060010741610b0421000001c0092200c445449089130242c544105480114844070b100d40180e000c1c0181d202c50542142d8420381101e041d2900c2302c00104800d1500f4100302100d82410364500c000ca4620101040043c030740003c5660040c5942006810305481440d6166065407140c1c0e0110741d016a041d0300010306d20403e100c07030350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 454394046 1250 454392796 454392811
    0x20106050418050706081e040f021206090d090303090e1b030106030b1c17030703390e221104030807051c09031202010e010e0c03070f0b090907120203 66
    0x1e07004402c03460614140a0140c112a00300040c4c201003040101451040303100c00c0e00c440d54800c80315100c03800c11fa480300c4140da43c06900400042c51a036a01100021014800e8640c0740560780c0c0044801000c40c0e1000641c44090002218580309101d090082c0034229008080d03540d40a00d24610080e81265540090b40700c000032942c2d0b021030a145040c03000070b0402d9031201040d00d0055912a0ba201041c3c0c1c04200c2000d036014070080000b94515000c1c0e4804420001c44c00310801140801c402080742d14102500c000e0303c0f640c041503900d00410f0083c0c00d0030410110050418400c00084840b5500020002210f417811a403209445e16482180000402c061401501800d03502e03805420b103a0701c0c0410900c5803842c151403070390000d80d40383e41c481d8400055a80c000049100b6521109003280942003c451001c41035207001040c0421700d000003039807a6040810b80030349501560316030b416544c4010301c0c464031064400800c0309140d680b4041041030361000355420180e80401c440041030040360411600d41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 454395296 1250 454394046 454394081
    0x71d0301090f0b010f0b0c0d080405030d0e0a02010906020d09060302032e031403130302010302090409060513020a060207080c3102030406150837080d05090610150201060504 76
    0x1170048031708480c0c0c0031000e03007040c21703ca6250039407450341c45035240b202604c890108940da1010500b00319051003250002007008100348299003032070700707065154a07180d02d040b804505500c0000824a001082404c200d83c60341d00c03144d007180e15114056001e0740c402410019070404192014410301d20403203490361401c0b00030f0000303223015085180c810a1108540c5040b1450f03071041c48907040c03000a610b29541070740e5080c0703809625a01c1c0c0c1c00104010700079842e8008c0c105800c00f4104000d00d6904140701003541c2c0201c4280d903070641c3e151402d07a11540c0758081c190040e040b000c1c225080b41040c442103281400c4498412048202000e00c2d101b011601b80e40d80800107030004144824404c8078002c10480900304280101d5640c60440400d030b4800503001586410b103c0b405000380c248100a682e880d0300d26040d40c4560440b003a07850010f445901005004807802d00d840042810080300183c0c992290100102c1010014141580c0c980d24841d50209282199210b16011600380c4940c007a81161f410045c080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 454396546 1250 454395296 454395299
    0x50d1505041508030711011b05010b090a05010617060d05011d0d0e06030f1504241a030408070501020c010f060e07020a08161716051203071d0301090f0b01 68
    0x70001a0b881032000640c0a0402c07040500041601004031916264411031b000e082c0d4803c10300603541c40c1d0030307560b03401c40d100c0220781c3e00000d0000640008000074001c80758154141e4803c8040c00848000f0b02039040010720006d0340644407901a0702c655000341c80203007800300c10007140d0780325800e4918641a401d260b890b20703204c002c07129004000c02150100c0313030700b055845401ca0380c020841074000209020621085c4001151100103801529510007001900900c185100a400258036a00d400c1c0507050481c4040c01c0000c005580c6148880310807000030303c40c1d01e9078507940c445405680041d4400d940745d5501304191400001c0910800220603d1a000030075030519224100e8804400202400f0940d00308a4807a40052040000c03926060749550710720b0100d00c01c070b04026405c02ca510704d2030f002078071001800384030082400c42000440d41c8244101c450b403920802d200c41043c0030a035003c001061781e01200c00e20300c0074500b5800400c040050000641ca4030903440710788484200c00419181c01c80180300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 454397796 1250 454396546 454396549
    0x70204020a17010b1206010e04090f0602130803071511041707030303050f06010818030f130e011a0a0f03090803040b01060e0a050102100b04061a03010801061d0609040201050d1505 79
    0x405500410303889141504281c09175040c0764007140e00500541c1044020f0141e1285030b40c5943c0142c0c08141c03c45a40381d004a800d1409000a51142d08d508801c0001018002002c0c18000b04543e80694082084070f0641100034003d4040c00c0641c11002600005100c00b040c03041e180c08c24078101d0f00c00354006000191940c1800780031036001400da81c00ca100c5103000c1084598200080d20f400003000d180201101e1a2405810b040d8000c4460b951401c00300090213542481c940c40c0e00c1d0f07085e100b040c3c4030076000b030b640c0d00e001d20b07a29140525061024078003400a81101d5000b0640852529554100030817038081c1a9a201695402101e00f1540000c034100144000b650103094030b41000d200f6252100b42909280000c2c1d600d40c1400841c0c0c008548450000141b82c80300d401900040c0900c42090700b8030300d00d16420344901c0d0000d01601080d903180c0000000c010b11260402d03440e40079000e0070002951070b00e070b06002070f0380c000400580c10b111040046d0441e407601c6101c0c041c240146001100740003800c2030b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 454399046 1250 454397796 454397837
    0x2071502181002060714091e121603050f061e040812040312060501110a060515030304061706010c1e050c0603070302040503160302030d0f020c060d0f0b0904150f02070204020a 77
    0x106c80424804083c41000e03d0f54481144400440050100c28100801c113030002076808008159410000c0c001c4540070604041d160300d51100b9a031141060300d1010050541080d6120300860304241c102c1c9001c1c1c100e80d07078010101402500207018001d050b2030b103122200c0103060440c1c1980e08500040c0000300c5c141030030a80f44182406004246840c0b03812540ca401c00d544d40702840031014019075502c80100b255480769109c004c01b03c500c060140e03500c80c0e682e200041c000c0c45880c009402040700740e40004543d584a2159034110590213070313021200e099400549030b0322041c071400456480c400d41040d0800b540d11034001e14403036092903402580e26410013052606050300801d90a0a803885e40500b07000681e00400d01c840c84411a1412801c0f1840d0400c0403458080c078440b09540040f80021001c000410703a81000410b10700081080c40114952014026403400449000d07205861172203170384c3c031080d850f030700000c9080590403009414450190002000c0307034000500ca5000c01c602200c11071030030f034810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 454400296 1250 454399046 454399067
    0x8090405061801060e0102070e0f0105030f010c0504060e030a020904141005013c0803040312020c032e1503030305010e09060a051b1912020715021810020607 69
    0x20b0324010840d000c03104080c2c10029043c0280000d01c40280c40d031100d280d00c00c110380c50040c04c071501c000c2d11500744130030251101002801030ba4003d000d5120b03c04041e00c2c2c14010a650394500703644183c68540780c1382c412182d150309840c0c003a5040c040c820480e009030783c55400e1240507a000b591410010781d006880c031894500001100c2c149141050010801e0042800003401e071341540c074100c800c0b441031101400f000844640f10380c958480c001400803c0508001001d403054a103c0c4001000440143e101a86c3d00c103590080c1a600d54048020801c40c0d6504208104000311241c0f00c598000181c0446070003540c070f00c45480c400d43d40101d501007090507814001c483c0100240d09001e16a810140c800c103445040041801017810f0300e0710086100328180c10080d0000c145106007032500c42103029100e507050422103032140001181003400c490f58100d103208507059554000001d60381c070342d42036142c940030f5040f843c031840c0e98610694420002d5100c030081400c1d01e600c1ea80c060300440c41c0c15140a0020282c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 454401546 1250 454400296 454400299
    0xd06080c030a031409040e030703080f0a11070f060204080106090f060f1d130b0412030c0f020a1b27050112020f01050d0905030c070303090e0903031911070809040506 73
    0x8107070000701080e002a4403c0c00c0c4a10104e81c42c0d03484040d100800c0260000142c811118480007034030301d080c5075020355075500402c3d500180b8881d90704c401a41106542c00c1d465034608550f01001541d00140300d01c002c02071307000c0c03182901500380780ea9074802c1407c60314540d00a602c13040c0c0751011498009068890203001c1e01a4803040c1c003c9074102580c14464080190201040c2020b60300410810515048018a9240d0003c0850704a140c14500081481812548000801d05002055200d9805030100d1041e840099008084002e0039486003408200c2045102c525000d5000c004180d24a003503065144580800d04641612800034100e20105d03034059000584880005a188006a854160b6142001001d21b0003079222000084400002c00b0500030040c85888005031840d00800040341700c004807406a1a10201541d46641c2100003500c101c0f807540160300200005101c468990500780740c181c441c10000200342e03141c0160600301b6071008806031202e0300c003c0360301071407442c1034020305520200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 454402796 1250 454401546 454401553
    0x72d0b0a0206060613030512040e06100f030906110c030310080303010f0506180d0c05040c020c03100903090e090114061206041104021e0d0e031e030612030d06080c03 73
    0x100d00c400940742c50010741160700c0b4000010300c00d5051090007090b6005941c01c03000351b9030750701d070a00580726080c2d1252280b10541c1ca80303180058210300c0c4c1407083e0041e072040c0f40c80d201c2c98200f9428040b0028a00c0b0001100d1550b41c070b14024490801d404082e0412180000c0155504c0c10840200991920168000500f0740d008000503c840c210200f8140200c41094516548641c19005210706010001c0102900044003041913420300013486c0d8018125032083d0380c10821000103e20403600c07406011010703901680103210a010400841c3d1001c61010300a281c010709940c4c0b940d00d04005d01e01e06480700d2180380c0d15407100c001d801000300101074228004440021600c0c1ca11070003142c803540014005000c600d8141c0c0e00e800b540d103654048601c003040460404118040780a811081a000458031940051600c5a0303a05840c0f8008101e4040003100e8508010544084044a0b032a41c0010103c1c1c2c0c00032010808c08085c51810009046c101c0814900072071101d003004002482d200c0390010703440c404d90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 454404046 1250 454402796 454402807
    0x62104020f0a03052e02031e061e1509030d030e010507050a2c040204060804060501090513080904020904090b040314040f12080405090115030605060a051209072d0b 72
    0x1040011001001185d10000c10b42e1032100c008448011035640110f0340b8814000400c004070049440c1550300001445080c4080075180d88041c80300b58004214001543da425444030003d0307242031401c80311400c01028040d0301d84450382011a04040301250004003080d101d0840c2c01114030203005899204410f41750075802c1000c0b290004008403401034030006151b440c180c000e00c080d92000300c01d1800c610007034000d40d41c2d55030343c1e1802401000b0481e415103161345024004035284605008450051501040d0122003a400d600c0c1c0750701a510588001d58008e43c02c00000070691540d0240600031400b58844403140e1400e41400752648803035400020b89503170704100c28003d0000350344141060358001074980c1c3c40580d582c038052016102d29007100f584011024000500030100e8401180d1406c459901070080d41c0d52801071143e540220880307080410700610041d20452078030b03c80c5079481a8854222000706a95180740c00400c101d00016039405030000c040b00781c5050309d80d208a0010320300100441e2815 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 454405296 1250 454404046 454404053
    0xc1e030f05030603010608030307111204063501030602070317070503130f051605010f09080c04021c06260c030a0b0907031202072c01060e062104020f0a03 68
    0x50800c00080c800340301001c000720700e503610309501c00c40c0642048030860703540e400c2805001c1d0045402e1101ca074128400c6160344807118000c1002d54040b140d094590401c00c83e03415050303151404102000580c130102d08002070828403209103080f07008601400380140e0f580800e080040004009000c0424090001d000380f00040303601c0380480f544424000290030003004035142204001c1c02a0002414038440c4030454221700c03855000c440200c070402d07201c60302ca19034880425a01440c83e4070607800e25070829480e0070407500b0b0a8000b00400039042c402d8000d4a440d03505001c0444107541c000c40881c25038003420fa8440d00d10441000160000c0000601c802c004200c006a81d4202c2848000c2000070803201203084c12070200500310185610030307101180f48858000007551409503201d15441c0d06155440200116120120f45c550080040314a000a81c00c1c00001e55200c0120156960400001c100708104c0c42910140480c855807802c483c200581030900402100307056201000d48544a03210040000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 454406546 1250 454405296 454405307
    0x11040603050609041a0a0207080d230103050a150912180b131401020a0b130c0e091b130c0504030b06031203071b200901080f030702130605040207030c1e03 68
    0x1601192264407006d543e00420040a40550040248a404085091341e0000b01d41d4000c54a100144000a545140c0003200740054500a203c0640160400c4101601041c03102400580c0181d003000042642000380e903460210180c0c0d400460005040f000000c03103469507600004e0002c00100384014140009171015080300c0c515442141883c29004c11141e41907402441030f950390903000071030005186007682640d036440742d07080e004503900500b0640128404c29800c42d40e0340191100c0c4002c040c403080490001d0480c905410a403540211000f900c065601211f000f40b0f07001c00015980c20b42c07213605d1071a0412000202502c0c1e45d221380c04ca9118440ba00c540d120075a640185c043ca00b00c900e0544260100034480e442010103041c004008c08115500d01210071003981c58441916010141d130fa1301c00c403140d100d01c801041080d960b001001882d000d031030001402100c2040041d00040e00c0c1d9514000501241d000d0f01049010a013035001500a0212441c1c0250790b0259001c0b04096003503507544c00a08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 454407796 1250 454406546 454406573
    0xb060609060913181b080610061808010510080601290a03060905010e0f0a2c0f0607030902030d0507031b11030615120109080d0207151104060305060904 67
    0x500b82d4180b00d81c00c043e1650444000d059001c06050810703c450b00b00b45059541c804120b203c240881d810009408078000f80d200d10444c1c9003904c0300410b500744201218015209019204d690803000d0021440260170300c0b905014000c0010910102458030303001d2418400705a11001d40103076008440044411080e40c1207080100f0a41c0c8141c0e108071440d4140c000307241c1a003084004078504400820b4102d910014940541825542450705580301140d003810345501000310050404c46051100724a003040c1400d4003040040c0e4156214181c840c2d04551620b00d0445517880005e8a40d03040c0c00650406225103c8580134070320b0034a00d02411514042c01c01c014414100740d0040c640c403030070307802d1042c40c03440311100c00c90050039201c0740d0400c10a49400c21901e041c03600c0c030580e0503914205015405204040503158001c414604004c00f07041c00360000d4020620544144407501040d0303080400c58070540c8604039038400140e448600f03081000303003182c0c001000b082c02500c1042c14003011682560b4010b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 454409046 1250 454407796 454407799
    0xd1115040b04110307180b01090b0c1f330b03090d0806010c080c0d1206030c0b0306120a080409150806150102030c070b07120906080703090219120b0606090609 70
    0xe070040e005011034900086540f007801e402c581c0c51103406c0030480b9908100d1807088240ea81482c1e00740c450814081a00c5031800b200c4003944403808011078402c500041500348080200d00154003103032242d40b40d00c10444c0320090088102203200070f180000c410400c1c48003030400292407a0851601e000d000d030b070f1081072610308004e0100010000f51568810030942d500c0d10340c441d803040d80356900d8140050340c0c1d0300c81103c0400415018048807035421003600c540c6048980081c603a1041c1c0b403a009214100e90300c060080da4200089641c2c0411b440d030208000d10607948a1001107588a29040b20501100d0b00c0d2008503a100901c41408c00800e50000f400542140140f4a01c24584d0310030001030317165101b14040700c07805001c1c06500144607800d6402408459001c2d4250188030401e8007800c4510030300c64054440421202000710f92514460b0b803105406030310152034107010700c01100040c80b04c0c0c1b80c81d5101e180e5454005481d0741c10404101e003042c2d0040c80c241c0b407a41c1803801401c0007031251701500146a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 454410296 1250 454409046 454409063
    0x705040c022410030c080c0f030111070305030a110f0d2306010f170c0a090902070503072d0b04021003090510020a030f0204080a0b0c030c040b07050f0d1115040b04 72
    0x40c3c42c0d08003210f0000b0003550b00400700d4440b556030301a0130f40c4a00f20307140ca40e403050614280481701800d06000d403421500e51240001c0c030308503240da000d440c29003000c4c10200c2841c0c2d450030380c82d00140e169001420448a4406031988503480030031004203580848024981c40080034200041601078604c07019000082424400c2102514010484034161404084c6850601100c1070102e00004a001403940305001d948884800c1c1e224880041a44a441401001d584c406c005010104d00307a4101840e10180440742d1600c00300c108041c2c4c40400700400419102c1c00012030a0100714a05042c44004860b21418140a1945c064450945801008113400705860300007400c041618465407003240400c801d03120441d121a00e500d0f074140c1e50b0080c1842102c03850010004a80380d400240141e91060300d440294514090400030803546581201c44100c41e00d01c10801c04903c41c030401d21517076102c0007469503501020402560324134900361408040e031104103803d40900c00420880c000090703216402400c0b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 454411546 1250 454410296 454410301
    0x303060616150c26010e060d05010207050102040501120902130b030a0203010624080c030c090d06050a0b090114030627120c100203011404050c1b0705040c0224 70
    0x70144048a031440040500100300b42d040b644145580c400f18002c402943c40079001d141d1181c0da4140348004800c62898400703804010801c0780c148444c0075901c118068440401c6c06001e6462900303982180c4821102030b500440c1c14811560701072600a4001c2d00d46605205540c2a9004141c607000c03410070100c5015240c401420f0f154070b04004001001da8060300820a1075610415603160000712031000c40c25408241151740071900c24000030780500b00102080d4a56100c4000407815076020004054102005541d0f00c1e01169a503c580c5200d100d4880c00072803540c1c0b924041003920b01703050b0420304140a5aa20802c0b403910001400c0303502c006a10b96400401c40747c621035904400f41c03c000a0035034892002d007001c0c06c14903040038213903208800f400c907202c00c0081040c0b04182d0009010b4a42c100c90015103911552034560800c0b0380003c1c10b80003480c6045420ba101882c460219442203a65512103c2e04100e0360600c1d1141c035146a000c0e2014219a006c6528907000c9024107000074a00c0010307140c007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 454412796 1250 454411546 454411567
    0x2040b1909080a050f010f0e070b0901020703080a050306121f0f02160302030c0c0a03020d0b0417160b010801090b1807050402070303050603240a020a1b03030b2103030606 75
    0x1889000307000c0d02c00c102d90804016180c080c1da210b4280c14110341a50816011180f00c0040d0b024504208030b244002d08402800c002d800303821900b02900207811403044040010200f180d031002066900780765503840b0b03501e107060003d21000020701103021a143c0d10403404c100640344503011aa002204862380403945041900c031120203402814490020416501d04450030550004020048041c820703040e5101c01c4161020000d0300c00881c4000307904480030108060006602c440717403a50161160030f0034100007400710050300c040d810a09412210f080b8504249050001e10700807030b401054501c00a03c8520940c2c0c1d5000144840900514180d0900d00043c10030030a0a020704009400064011500d030210f0b418000d01400040d200c25020b03014800f002801c1821a1096106418242d4801c00007901d8131200b04000f98080c0045074100288401c607041100c11040001f28240c1c0039a178003043c8984440308200861f4001e14100e010748105114144001da00482600c0d4403240842e202e58803040b9049 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 454414046 1250 454412796 454412807
    0x6080702120a08090c0a1a07020d120206011d06090604020c19080c0f19080705100f09020906010318110316120b0609010609050418020405181b0604030f0c0807060201060501030f02040b19 82
    0x60000f02f000c0d985041001001e80d00080b040e040301d1810b0900088011000019444840306651003500030010341c00180705824150020000261900c08503103490007822215140d000380d80b10222910301c1d0018501150450401400500001c4c000103083c00c4104140500848410721400034100000403030501e050000501c80c201014490300c1081c0010000c08451030010314034244124410b11180010a105502c02c0c85841c6800940c4101940f0444190310307040000b0030032861b159030610803401c0c06054201c0e00b81d41d543c02000080d41c4e101708540e0394a0100d42146c4020040743c091a07a00d0010407a01d540081000b04a0320152000540d81318400d448806007104548081d4005040c04144451141014034034280c80021000351006a40001030b0340345040e000d55561517102400740024008159005031001d500c0d03206024012910340e8403c04113040502540c046000750359102c5080047d560540142207058003494403c51a0a08103400c83c0000c1c010b000c3d220800c1007000740c4000d4643e0040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 454415296 1250 454414046 454414069
    0x8060d0c08070b04030302010f1b03050603010b0a03060b09090a02011707020111031806060f010c0605090a0506042105070b0106030e0109060e07090f11030106080702120a08090c0a1a0702 82
    0xc07041e02c404645920911240d90710a1104400640c07034500818000103c0b0720549442c244215110860521105021400381502511640d070555844400380407955a491688000714031481c03003c198400b003142081039604004010b4962074004501c0d0f000181c1c0c3c410828841030b0280064201c03240ca5592089004000c2050843c0d050900002844414113044401070704800403003003160601c1d601c44080c020414040c5545901180e4010180300c0007880ea608a540e011040c1c0e802c80b00403610ba07495103882e002084c2c9058640280900d4504d800043e1f0406400b8050001e00b800c510313020b00c0c4e5607003035035402c0144031700000c240c1d0301e0907001c0164000390801520150003000605c07c40f0760307000301d00c0c3c0c88a40380d06c22200b0f003d1505810b25010f198070b001c2c00c10141c41140c90581182e18044007170355802c40040c03e00b0b045004041c1e00d0410403000101508450100b5621480541380030420030b481c01c21a40020392250001b142c0801c0758103001c5000c0035810030801c00303054032200e0602c045003030384118 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 454416546 1250 454415296 454415309
    0x13051905150304052104090f060b0417011b18090504030e06090d05101a0405010f35010b0a1409040311030f0d020c0c1c02040908090d030f081608060d0c 67
    0x5e10b50280f45015101001d8410f55020400c00c10880c1d900f146800111950b40c0300e0320300c3c0e250044c4801c1001782403100740340980441d000004500100c0d40000c0c24044920034004101140d414010076403aa0717800d02d01000940304005041001342841c2d2000b4042c0e11300b44113003c0c420080010036110075260003901e1102da035440710444949504180f0000054074210f400c07420245038070340d038a038014549402010304950a41140702c40c064102801c000c011422810180d010021610180d20720442c1000392110100c0754a000103200324901c1c1c10048000c1c00b07680910707109440103410404607910280f10a4100d0350600700b008001c08100511803c50080e158805100100031030040c1448203560000e060050a5500703a600601210f820049445200c0201d141c00100f003454100060600da8020151103000320440e9040441c440002001c0302c018080460024074502940324070f050b084030450b42c0100b6480c415207141402404010801800104560310601c101084031042c0301c210750308040600031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 454417796 1250 454416546 454416583
    0xa140109020a23340302061503010603030503040f14030304030302070606091e0e0c030f0a060c050408030307050f070606230f060904240e01060e0102011401050d0302121305190515030405 82
    0x101781801713501c42d50110745441c10143e800c10710a03d6440d061180b4410340c0d03415100c29045840d170340c4601c2000d000d44c80085070301c0c003181c003048251283c042000d14030440c8039a50250f074400a603d068010b4a2990344500041da0600c0c001400080d044d28402506062801000900030300e4510301c28900800182e0311078050147d151301100b02007011600f80c4e071042c0100c10500c111900e402003101c0922440c800c612070b60f003080c00031810052040004000880703443d00103030704240c46511840c00306ca02c03903071004020702e594480c070403254880d1f000001a030340011900c0991981260700454114843e00202500c241d644160303223180c1000845070601d5001070840e81032661a1280c0030955005005c2c003c840106994500400b090740c0b050203882c103046d1496030400f076180d107080180480100c4058049095000d1218520b01c80042000036144641100d4888904213240a0074403a81e2040c1c40c001d46100c4072200b0040c019616080350342e2141550305880e803552651181440d40c100300044100d8840d03d40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 454419046 1250 454417796 454417897
    0x108011413060b0903191a2e080c0d0c062105041101090803070818130c03060f0f05090106050a050c0316020f010c0506040b0a140109020a23 62
    0x81801001d0242c885040e02195041304180850400301c45552800400c00501f000b441805100007002d8550069026074850071251003d06d01081010b0b180701103011140d220010811140508101e1a4500c00b000e503264007001000b40c82e0a100740c2050b008810a000014000c0303408036090030788205c2010401e03101000350341007038034040ca40040c10b000c1050004a500401246004010084882059020410500d42b89805c2c8100260108d50801c080d0301400041701016114210b000c0e03544401090f40d0005240ca0401010314619051500150480421004140161b0310b40d040c01c0d505588007414645c2c2c4806988404440034800d0b410008460b00003c14105090301102c42150704803403003100d045c5015890384c07004507101107120038050103907440f01d00858042110030303817080e4008850610100e030905a0524041c3e0684081c0d04c0046015400039500c0c04030b0350b1003e0390199005003c071a51112a80c02d4400d84a203018140002040e80c486c000c115044105508080e0f0003800355550303112408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 454420296 1250 454419046 454419059
    0xc020c0607080901030b2b020a180f1d0304090218030a0605012c0a0e0c06040f0f09050c1206040b04060602012301120602070218090f070f05010801141306 68
    0x10b03000f22074101c3c042801c201c809441342c03502510300c10810000744000c401c4080d40312902a485240200c00341d8100340c1a800216202503101064141f01048034004221412214400d01c1100c54904850314898042c8485541c00f004c0031049900701c9920450247e1203801d5030441207600c503a1495010360500c61030300040c04000c1c1c03d0704003038100c420302c1ca22403104201e0080305210441b810581703030004400100028012803100d034401300c2908410700c12600e0b51190350001c1101c0b035200b41c2084202c4c0c0d0110800f0000740b1a500107a40107030120300d0050085042600b20043c082c0075442081c0400003010002500d5030f29075030f00080f1040783c0140103110700c2d40e9640d806402810000029014102207011080b451921089514101d4080c02510403038042907441e40c1d002508850300891b0300c0419952001303281c240444c00940241c21080c05042c0d0b614070200000d00d0200c09a01a003545820104104030303680e080601a81140c44604925900843c8003001402c104110020700708014580640412107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 454421546 1250 454420296 454420313
    0x19080601060809070603090c030201120605041d1c1e05070203070f140d080a031107020405010e010611010b1c02132901090f0b07080421060501140a090c020c0607 71
    0x420340c030020b41c4e140c59205c00085094412540340503087d800164002c00041d40b0542101122440030b2a001600e140c480c00003409442600003515080f83c11072004401240c1c0901207006500ca080c00c2903416520760a01c0540301c40050014080600100c1b01c46c200c2050080080761801980103042c2d4000e29120f0b401a0301c2d100c401c0c0034101c8080e02010030300c8841d00b4142c2ca903442c0690030070400703410320342c010130200c000e00721080c50315104002c148500001601d80f402618041d04004241c1ca03019810158020844c406031820012181e04107190000c840e1101c03900c0e070007401c00d00050078142c1070160000c81c2c403013a039900d0a800050b1914440c0409030318088905e001840c03c900d0f0018115405000450f4281114010074403618042c010800c44054080000c000c0e45114114880c1081d03610040c8c5c0446542050712146c20301b09080d015010080e041c0f0540e4050030500d00303840c183d094081d01159880b281400380861281c3e481d0b00104d0b285d4001c21204003845801003403140d0f03848480c40c020301d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 454422796 1250 454421546 454421551
    0x1c020c01051b1309180c030c05180f070305180a03090e0705040612090606030f060504060f0603083705091212030c0a0c0c0308031009051302190806010608 68
    0x70a10118a8820b6030b50355003200d60310071510a6501d8035038109101600181010900380ea0002240b05414000400b20404400194080c40c00031110764a402c00307200c0c10004005c0c225064a200d5403c00015203c12800e064110005140000b540d60b181c807126408009078030020b45181c40b0b048243c2003050381c030008100566041101c1c1c0a410b031640c206c1640d40f4007c5014290110307030f04200100300527a096102d00745c802d0050340c01066999494a030306003184400346054400d191954204024003140e070140208205038154104081490342c0c440311a503010b408103200448400c1c95000844100c07400c00000c1d1007822400d200d100703200d42580a03145d0f900c4128264000c02400d03e04c40f9040c0d1001c1001008500042142465591800000d1541c0e40c012440002480343d1480058007140c2028801d2026600c81d44020750717241800b00084480511030307404020032504000820481900001c404420b81e81d040c1c0c0e5600304504407004203c111000e03030f0084403862080b0b8000040d0142d00c01101c2d070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 454424046 1250 454422796 454422811
    0x603011211040509030a11070504020a0908070803042411010204060e040f0b090f040c150921080a0c0503070b0406022203050309090c0c0604050c030c0a1206021c020c0105 75
    0x345041c0044041c8015548116400e0505800520070018804c0c041e510741c0088085040c00d13aa00282c9510019040ba00715490440004010000038441520104221800341803210015801d09e80741599584001c0d103901e0003000da00c200c5850007003506002b00000d4120301d189000a545850312408020000801e424469104a060100514413040c0620807070000c1c2002030070024048d42c403480c4e55144100c0c041c00444075510341580008403c0007060207000d068540790f40d03403201c41c1d01c0d0818800d40d9048000401d00034040b2007680c10001600350301150510051414143d81e4550070381041801c60154039000707010300521900704410410141e00030b002030010070030001031036013141d152074a00c1c000c11302000307000e035004110b110400c0c03908024660307000800323825103442c02d50040c581c0342c03c00409981c22141035002c01c82082c0c1900d01400074690b40002591a04606444d0190905000b01c1402c0c01074800d0b54002102c000c200e41c120440e52006c082444299601c0c0751080b00140203190464400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 454425296 1250 454424046 454424063
    0x10302070606080f120c0c0103020918010906150503310206070b100e07080c071e0b010602010f14010515160305180a030f020f0f0d0501140109020403020120010b06030112 75
    0x20800170101c0c100381c03401c9003000070092031201305610054000b507200d80c8515038010b1308d02c85c3c0c60f643c601d800410207028182e242c802141c60340c40d010031500c512250442113800d02000b8003c003c200c1414685028920f81c0c828410421b0060030f681c003850001c264580650080f00009194051114214481d07001724994111006400d80c0d803030840800c044107a0748480003d115130082009009540080c184844c02800048210a505a1600d29060349044200e980307400181c010085240c080c4580e1003e00b05000d07007403003821404c020000340b05905000c1d4900c200512110009140040801d40b903400c1d2030f001400441c545c00c3e00340a000d54110202400201c440c001d07203d001c070300b0b0404030002226071201d42d28160b80f40e56801c000201c4001d0905c0e90b008580300f0310701c80003aa00c1d080b43d41900c80c014800010fa00050400c0036500a805801020b24540100001c0006036840340c0e0070802081d443d1071459040c403002c14941e0240c40c0a40d980d40e8816008070002c101c0c03808990b0494082445034108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 454426546 1250 454425296 454425313
    0x220e0c090907061b022d0906030102160b0405070b0c030705010b0d120305041a01060f031d030909041a01140906041a0613081203041b030804060e010302070606080f 72
    0x10940e07200c0e2540641c83c00500754201400c4020a0102c0c010b00d01c0b48010141d108131075140440d82c211401204104184004002e00248181003070540c03a50031000540080d0300d0203580d00001c4800180c1c0060081040301100d000809220b420702030070024010300b0110a59810004903844c1c1d5a400c80003054400e94a8440f500e2100d2809543d404075490f031143c3c00207524880048240c004000090080c1c4150302184c40da814002003d41301540684030603100c2031003110078050f008045454144080da071007500c0a40361180d8400004c1030703402e0070400b160b070382c1e0031036a4601c1c12000c0340d10b8031179114254040c1c0c900003160813000710100b03844540e015910745005603903a200b04001c0d00c002a441000c40e50490713800410904208c0024201104581400e4407815a110202d524000360000101c030f900340c010040c08200003465072540302071a12a040100030f2401e40e200c110241c031441c41110140050051f0001460b4044e0b01960003490300060104200c960700d43d451900d40d00c04031b0341c200b824080c41d0366 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 454427796 1250 454426546 454426561
    0xb1801020414060c0c1f17090705090705160c030b150a0302060c0a02060f0d0e1f150e04060c0201050c070804180b0901120201080708070c02220e0c09 66
    0x9880440b441c4400c481050308200c0b0078032580ea070280e035548040f401a00c41d03840b125100c0080003811158400c0b1140440c50b40240c1c02805031a0803644205408003c90a2040320400043c0315030941340101c072552295240c0c0c4070181c94070310408500741d24012816081009002c1c030910240204e9014040c11442c03a92138504214a1055030300e200703544400340700c20510160800c0d00c09170070541c1c02902140e507540029000110a070704450116054110f000810110302d14050190030044c0858400905851192602142004203484000e602550740d030032011100244c601440300042c049142410107504003410900090015204442c01641c01c0c103001c140c81c0700a0000303c85007160807449040c10103040404828424500810001240b9110000ca43e4603950b0984940d000f03100c894038915507101a88005401d1240040c012024040d442e000c029000340c0000848100c243c0c1100c10f41d803840d4600c0c002c034000c000011249106e0f5031604000c6118146c0000b61003020f0304048519441c0c80ea903200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 454429046 1250 454427796 454427801
    0xe0106080106080609130f0201052a01200f09030a0f050102030901150f1e0b041d0105060a0525050f010e070e0601170a0b1503060f01030509190206090a030b1801 71
    0x100c0e81000c40700c6c9401d841e000b045511401685180c414500540303410f00c45281100c0c0041c140042c402460851405a0021442407250000801800c0c69801204060b48400b1119005041010f5036a83d8001082003c0d42d50501c001c0c41160740c012501a49466a420824000d40040f42c407140075619100c0388c0342c0080d6580000004403420320600c040400c0c01e03c00403c0320140d8002c03027904a050849004503810040002600c00ba05c27240c10400d006d134000300d1690780319180680c451405803204126203e2019404421586400c01110030100d410700c1c080407103e0300003440c0308081c0c0203009083d14100c0c140c006401c441c1401e00d1200c1210352088d00c4144054007813000740c0d13100d40801c0d0100640c4a5a4511100166101203079100028006110304d002c5401031008503a080e031100400010441207103040881400700900130328082180e80f9080b81880e507203410400403580703040b05012647c000c560310003048818000d17014068070a40b942d64640303048515015549902540d0018a004000e4041413 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 454430296 1250 454429046 454429051
    0x1926090304050d03170c030f0705090306070f2705030f0111030414120c010207140a0c21060f0203090c060304080405010318020904031710030203030906130e0106080106080609 77
    0x15009145014680340400403500442142103080c45007690301c4101060344020486d12032068020016a01c1c602089074802d01000105a941400f0090200d0b0345ca58400055040d0300052078207110081841d00c0405a80540ca9803c41d0008040100c0d142c3c6149440c081040d000ca40061741200c01f988040d8030128281d820700b68000c00a4081800001e0100350031103190b10080d043c81c0103403001c021a03204601e155900c2a110746980b81e40026108040000a03001010342c4004200644a10101030361045421001481140f42c0c04100007000d1503440701c05403035920000d920142c10000000c05c60080d0010350011a00b20030240103491103100d03182001022648101c1e80000104d19082c2000019401004110360300c1c210724102000c8000161513625031240194000e403254902100c11643c001d214200c018803203500c14400d80300410068070000309507510120b085400300d1b2158003000c400c000040e056405071203140d10300390000a40a4003d89854141c50700755580c1011940c0b400700b07014065806 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 454431546 1250 454430296 454430311
    0x708010b09060d0f0f050c1305060102210409060807090609060b030a0504060209130203040501050606040f1a07050a031701140d03050d0e0303180705040509030307080a021926 77
    0x540c0c00050b254035154510340710a030f03c10500b404a013681511051590b04207440110351551160981d00582d1178869520214500310401c140034030701d0032000007074803482981218100c15040c58802c2103415000710680c1c0290548090030003125581d400c00c0c07503842d0440e2003841c0a07140303011400b107400186c0b03000b00b500740c07506098801c2c80c40d140c0b401014010300e03004006a96407076085c40700223065515609440041c42d101d10015889040600b40542111f5000e44254442c0004000400405002d03c1c02541280e9076a542e4a01c41103280d0044442489060801469800780325411820540c118209980c800d9207002c1c0d800c440e0380c0755904001c040c648078a81c141d01c6444140d981c00068420030051610a14210000c280907803403070032a42c655082994221100e02a103584200380c42d40410000c2d000b80002c8030140414141845150303240d10015100004201c00c01000603c13001250301100c0c50300b956581c9000b038842074a02c000703003000c0c45020480c00b54040d00041250407951008040c0c0a1f081 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 454432796 1250 454431546 454431559
    0x318060e10121104030218090d030b04061e0f1211040e1f0606022526030a0807090b0c0601090b0a09050a02030114060c071e090218030708010b 63
    0x185641080308000c6480c001d8000c01002e1614070007486510300800030119008a58a074035141548100801c1740000c51440c0e10380e0003108204040e441e0001014024039900d030900003940c50350103000c82d0103040d941d0403407248405aa1080c0d40441603011400c01221415002c5480050b00d540c1000b14421707060300c016003050f1404214001c5454194403105240740b0304022920120203551000141c01c2451500d94480d0369a0b180c100301160f0107029512042c0b42489000380014070400c0003250128113402001500030354030b1990b200c4d541c03030000740d1910103080204032600e603444241c004040342c00445600340010384400001410400b8401074950716400807016101c0c9a081841d000014113240460310f41c08402540d0024001d8464400c0c5401410b5036540545d03170358100450107640c000302c4000c050007440304110010301507601241c14802c0c0c03441b900c81c4020000425507032480b0700b9496003141c00e20520004600b0000c14540130780c024800760650035110100d55440707e00d401c903090f240b80c03583c2000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 454434046 1250 454432796 454432817
    0xc09090609060a0c032406030605010e1f02071a04060306050d03020a11060904090303091106070c0308090d060c02010e12030702210705070b0a03050f0402010906030e0a060e0a031806 80
    0x400307400000071201c01740b074005054403400140c00b0260070341c50002ca24000303a03248107100301a81030169038042c2c4402c1c01c10f20341c0b21800c500402c1c03100d204000b00440c51261000e4030a42e1b54801d01680000f4541502004403405100e030107030150754418411400803a1421100280500f00194440801c3d50990045c00e0000402c0d03c0f044108110b9244840e170055082040c100385640710303c196030440340a40d400003840d400a02d08001d10906888500b88a06030901c103102c002800c008a40d42a290700100d1140c0ba030f800302004c608640d100840040000d41013240d001c0515905503c00c031503070801340e41110bd01c030780300001c070300b03c43e2105030317000e82c016044014a140401001140d00380c4044007918414039160702520b480381821b1441c2c002d20001100000c0b91941c0c564103008581c1c00484803000100c060030030b580003a1402c0e2141c8152814541c85d0ba0920114410178400b1025982e0000c205120164181144549070101c10b07008501103080c105080f0030071103d092041e03041d10a2038a4811486 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 454435296 1250 454434046 454434061
    0x1008120f0a020f120c0f0705032a0d12030b100f0c151104060f1b1709030a061b02060105100c050a0c06020a0c05010315171203090c0909060906 63
    0xa900c10342210056100d6000310f0a1441010401c92950310010034401c0d031603001c3c141e00f00b82461455910701609500c480418030150350302190f244512036403402c1c1c0000c5410b044524003080028245515031000c00008a402480300344551007079142e100c3c2d9000c115074500c3d40100198440c401c800340c8000748030001c010814034007d440d500241c42c0540000070344104034034a000141c0380c40c22500681c2c1040410700f04039043d0000c026410b0b1025900b498024100c10060036030306100d806001600c0c0203418861074000c801d00404503030901c28050151424807006090080c003519a58544403881414540440a16071000c21058140e582c010b0150300d4514400310103e401580414054a15000b44800c1300300080d5a60150030081071160041c1803455547d0900108600c1c6a601050505080882044071281494040c01c140c460110031200c070500c8a80d140d500e82003a02c1b0000c210b60000006000810000103030720800c1c2601260703440000d41e1031550250b2100c1d016034401c0d4456001e4008034004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 454436546 1250 454435296 454435327
    0xa110109050a11062d12100e06010504061d04020f1801020606010e0a050402030411060d091505090d031a0411030609010b040303020a0f020102160303050d060e060a0506071502030f100812 82
    0x40b119080381703003810b003960340056024510044e2a44910750030300c08020010781000303072612507001c0001d083c041c0c14649401c4014080e10f094104211002c5a4034007040740c82d80d40c40d41941d86ca4803414145036221076050400380c1c01805030040700c6025206440c00a00ca56202d001034008a0358043d0040050904c0c12041c1b2004e0340001d00100ca000588513011a00f5866500181500701013041000c2510100e03800e002c03400c00f8401e422040300e1414002000202031000600b17070100841e40c980001e94070150300c5030b5805505026001544581088414447c10711a00061030144c03104a03400d8440340d90b52164244244168440140940c21012143d030200710315041c0c080c421401030040e69074541110410038140501e0b50001c0380810404682d00c603901e10380e07202d240003070075102018205604000c40091422100c0d441a1485114005404420400c4280700c200c0c84c48141d00b000d40d20703800c1211205202a0045500540c0142440f8001803070610004901609940150b1954075145400240054 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 454437796 1250 454436546 454436617
    0x20a1a0721110c1b1e0d051606030608010b0d0c0312030e0105010e01090e0f0705060a03020d020301090e1b15090301090f0303020a120e0705060a110109050a1106 71
    0x8030700b962145500c01e0304141400a101040030480030f0302e01d8160301030b2181c01d000081140540103080740002441c201d881551103000e20181201c141d02080450300c0d0240c60b0102e0300801541c14954124001846500358102205a40c40180240003503041d84040c040a000d5400024203c814035044c1040410444038900185143c41c0c90003181d04060014a0741c2036940070b078000f06807030041c6c40042000200b03a00c0f62080c017400a05c094054035642010055494109004803446064006140c00d0050300960440b03054000614082d0b46030344c0e542d011800100002ca4162600f406070044021840a04404054103400001c0144494041e07018030b100294028000d01c039095981c440d034010101e940c4500e0022114402c1c0d40140c1d441800c04401454810610034402c091400d011008517080804240e50040d90002d0303807a692501415042200d201d50b2401c406201035182c2040d5006008000c83c20b0b8560b40e000c2c401e405042041b140520025100381781300196204072106000300c00a0a02c8000700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 454439046 1250 454437796 454437857
    0x1715060111011b09090209150d0f060f0501081b0f07060b062b062603190804170901050a030c0915080402030610030206030403050702011707020a1a07 66
    0x9100084009203086652841480a01c00000034446440f59072040c00318016218601d01542032001d588003080350300040c00c105c2c2d0100c40f404120000403a500d50f2200c0d00d9403040000500110b0795031500c0754003400a03070086500282c060400600320503181c2c21a100840000b211311481e091850001c0300003034202c50030485100e80c840314000e0b040e590f0344015051502c2140321022101c0c840c6000011901d4000720101103007418007000b01700c1c3c0d8002c42030103210360407a007034107624201155046034250312480081009540010307a030510000d40c401e882030301c6548a908128180203002205840ea8091b48010030b0000e00d04012a08285119801101c24600e5905003210b240f9100d0b08110259110718a510000030080c0701040198070741000b071690400104240201c4543c11234000c40e4451000502c00f0301400720026142c0c0840e44111030039405000b02c6c261031443d50501040081d1230310b6100d0401da4108039095000d040307200c0915501c40c01088942c480c8404003011100103c0010980903246 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 454440296 1250 454439046 454439057
    0x90905070504090b0a0b030d090303030b0406030204050106050c010b010302090d1407030c080f0c0a0f0605130b0d0207060c0315151101050405010c0906020703020108040b060d15020a020717150601 86
    0x640d41e10b80e40100041c0500c58000141c56150041e2501c0031545801d440512a611100011035995049100340040d00d41600e00444e00118000115011780b21561000f074010340b8120002602961000c090048190a072009000031030300c4000441c00d901a134003032154010b100f07240100000c1c20300206400081d840e0742c292403025030780b510780c41c0c0900d03d5a03000c2d40c00c54121400b580311101040c4901d51600c2802c40c2d444034003909040da1034540c1c4209010300c0e4180040001e107050442e0b503030100d000c020031004050b00d640700c0f02100c00c04007035000140e04903169401d1050046540c0d0207401030141c1c00c044070040302c0078030740750588070083d1421440751031060144000b0704481c400d03020b0041e030f44107a0180c4004698449a407200070840ca0ba540d20503800c43d04400002d000507a8007240f00d58226401043d0801c4071b4550300001404440500b400510005030140c801c0c00f401e0107030700600200e24464003514090340d41c0b8030660940480030b807400040390300040f2140d50109601000c0b5a0030101c1807420b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 454441546 1250 454440296 454440299
    0x309030301050f0f33041d13050604060915020c060a0b121e06280f110a030b040c1d0603040302011b0206010f05040b011d031002210105061309090507 66
    0x100391940e0201117030078242d101c0a24056400e42440f01d080c052602c0a001a0b450f10b40b0340b0003981401070030b5848150210340321401040100f140d410660b0390094000c01915240c3c20285410001413806050440e4288603114061003055014805e4501803501c07900a4a1103603161410100180300c0e01d8001a03103c10007034201550400e007044041482d100c4284030000c162002b01c4a20b1506000070902c40743c0446a082081d00a41d050301d95007401e404603640441c08544400d264800781c1110b6103848840400420a0b1945a60581007a1180322702510704000303406c400a82140c2d00001004895569003880448507101d0421000540d40b050007440009032360325904a0f082d12031840d9065040041c0d2000340144011520801900001e01c0b04075000c000913018400081d054441682074010311956220b0480e00c0c3d91418403800640341e0064404660b241150070302d030f10713014194503d01111001e100b4004103050920200b01c034486400c810640c0d200900e0640c070b100207010300c07980484280c060840d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 454442796 1250 454441546 454441549
    0x70810090b01050913060b0a020604150b01021b1302030703090c060f090e0c070807050a060c020712060504051219080a06030209130812070c060c02120d0b151201030213020309030301050f0f 83
    0x1510f030b040c0d1264085c1008bc145402c044201000c001118011540b43c032824010aa800080340c5108503400d10503035a03c0d07a401c03030000c5d8031850005100d03048140008200248a9815886011043d201c3d4004550940e101c50044a25800d4541420040740744070303006009001c0c2c0035040d40e62040d02a640345141444603a2020800e81048604484690003466a40c08004980c01030350208202d80c4002c0121618007041c21802285801000d410304d650751000c81c09009081c018500b03150200c0032146d950304013800c007140e407144440125400044019020031440c0e14140500300440f900246040740c3c40d146c00615808200349603104a1344c014040180b003080800040c0c0c3c0c0c0c3c0c458016078071140c0d099012801c0001c150b481c00c2c080b490454001e0341070362080200010968440c10441c2c20002995200030020800c0c0204020165510301000704d03070700c9038010110480d981600d209442c0000001411500c98090b03000a031500c2129420600041c4620f0034480110710300103500509070000b2589480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 454444046 1250 454442796 454442819
    0x1f05190504090b06090c0f19020a1b0602120c030912030d0c09140409021302030a231618050603070507080d0605041a0321040806070810090b0105091306 67
    0x40498140b42640f0070080c0910344822115407011038002c010b860050725a80c0701d40b00c3d215103210000c0d80d0b250807000d42581c80c800c203c0203903000d5001e000e682c0c0e0402001444100007105101e940d005108003030040c3d421b202e030340054541c402940c00056040c041010100191000d40b400710780000d00c0305005691003400107006041481007280c541c20705050034040200e0751450241c082170b0180e401c020088005882d030a0202c0700b2a9260140140c60ba10754541c54030280240f11040380c00b100c640441c41c00d220b0070401d8414014000b4021081480c2048042542c5c00c600b440840d0700009110101041103081c104015030740000189081c6190110560310030301550400c0b507a28100760b0f41d0b08010b100604080c82076003010000e051002e40807084407800241d07212410301200303540c1c1080c03009012035030241009031406484100300751080b502d0b1401d00100400320494803103030107200c4840001100221403085010351503043e981c0600c0c0ca041e40040c00401500c0010510102d94ce51a001410003d100d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 454445296 1250 454444046 454444061
    0x1205070b100305010b0a0b07020409050709060b0c160609030308090111030103050c01090801020f07020618040203040f0b10050d0303150b0c03090108103503040e0108061f05190504 79
    0x148622020709045007042c030300710346501341c8090143e41000002c1c404901d03000c0075a4860350341241c011580c1240e500d021420040d940c2c0c01026401c0c2441c0000c5031821504000e80804c280d40c0c001c84850310454144124400c45a10a03807021400c02c0d0030900221388a00707040c0d94030104400000c40c1c3e0341114000b0890f2039100741d0007950103800c01c0030300b00683d43c1e000b0008401440210001d40c10410032903000490340c0b05961009205000014400f48032504846400d03024410040003191a480d0030b0030240403100800404451581400c400103001001010031b0713100361400035084040c6410503560580080004101080700380c20805c2c03000034848902001401c00201c00c60180d5120034802001400745da80240458100080200091220000100c00c1040c4442c051a103801901d8440130440c280c0322134000d01151600001a01040700c001e40d0400700c0c102e858a02c11109181d4441200c40c10034402c8002c9120703503488102040102d8074290340c0e154030312030b40340c1012003580341d40d24001411035440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 454446546 1250 454445296 454445311
    0x40308070507050a062006090c010e120601031a010605030f270d2a020319031403010b040e060414070e0a120b01210503030c0a1416060c09060c1205070b 67
    0x1406d0002400085406060031080319590050100c0d00380b01660076100c1288000540c1048000d61000d081d5980c0c900941418182d403a065800c5961242410741001d18400c02a000c620307182000000c07000c0c85001107911400781c0c0c105074411600c8407106884143d50401c0c100329286074211480411103828490800101d9094440b8000c0000d0541e5000114014103c0356442c40d04500e075420160710042020002c40c0703940b52001361101500e240903115140d141002152061004c000441c81e075284000820641e1000c0e56400851740d100000c200c01e030744015003244100c10380d02011900301ca0040e00d408171807040c0100038010141c0ca606000011800c0b04000743c54520101c00100121111000b080d6202f4030f116245c41d00e80499034480350b54030311010707040b03080003107000490f081000d105040d00c0526003940c02c0c03074994503095405010300c2010f0140003a26030368600702000c107040780030b0101201110150388175a9260b00701c9440f1442c0d0702d071008018000303200003003015000040e50021060f05c10041d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 454447796 1250 454446546 454446557
    0x1b0c03031e1003020906040207141002040303080a2f1b0114071107170a060f0b03060a020405370e09191a1302030709060e060604030206040308070507050a06 69
    0x10560041c4515800141140d00e03005420741e010310140c3c032110b035482ea0100301030b50b000d0780d124600d1401c8069490700c19811031084c00b8403c140940d07440c3e560000c2080300d0007681c07034100686403000650222998000104503401210801138824180c0302401e02c22100340c403403040c0c01c01504a01301e820751b18002602019030b0355110084030288182d0540240c00000b03d1a000300017048098666940b88a940180c00c400e90500754180d09091007000028030850b4071540c24441142d0301c1d500c2c3c1c0045c151070031110307109003e810005080941140700340d0b0110b032070007042c2d00312040315494104802032120701c0c0c901003d0388800744119240c0841c49260700902c80819802c299203482c4c03100c1824116165941d02e04901c102c40c940000c03030580200f2910410341d901070036032107469103809550150009000290903000b050b100050030000d9074000001c43e19a040c09900ea5601c179400c008492080b070000a6101209200900c04203005502a0200ca072042c1e0844100782c1e10350002544088481d404000000d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 454449046 1250 454447796 454447831
    0xd0f03030b0a060324031a0a060503030a08090114090c040c0201060e1501080c0f040e0c130e0106030e160306090c0812041502061501080604140a02030709050102151b0c0303 76
    0xc02c645503441e81402c481c5d00140d89600b140e031800300c91003101c144000c00700c585001003000411075600103402000b005003181e0ba240c00007000501134100032102d00003194a01010289a480c0404040c1d1203921282c2c081d1143c85181801c00004001850000c82150368800b004100f46d014080e1080c01b561003030100c00110760b4070400040c45884c000b4100d8006280a1290b1020108032000341c805450400300054a40c1d0754000201076580a0010950f00303469800034001007050402400505880403a43e040c084030100641c01643c174041000580c0030000c8855003000884d201c0c0c0d01446410b48603001d6001441d90314000c4d14600000340d84000e200c848001800c00c032070514042c80608402c114005441c46280820319007000e1307030704d111a040c10710000300001a40c1d5910b0341c4c0485280307000c40c1c0d800e4040d07040c9041a00c0003500100d4040020841800e0003084c03560001a25950385040d4032000d00240d43c0304800e0606d006201c400c440360090042c04028044801403001c1d61140d0149440140301f00b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 454450296 1250 454449046 454449071
    0x1e03010908070605070906120f020c1b030f0a0c0b0903010e0d05090109050922022d150322030905090f19020c0a0b190501081f06050d0f03030b0a0603 66
    0x44030080e05070411b00c211110304100b0150015107041240b024183c001403140c1b118100034000e445070000da40400e00900e1801c039001a04214200c0000c4410380880703d884403c42d2031280c1e070303c1c0c076120701820310140f8800401841a51000800990a011300003141c250a020103d502d03080c180c8403100c01241c03020401c1d42e142c9d40e11a800348014203086564009070f080070350045803550b420038180f03032403590310541003c159124040c1c2c02914a106860203418000c1c910f46103aa61041030400c103100f1402c0c100141d400703c03114070a40e0700804100134032900760460b0440d02c04205030310031401c07424400c0041b40082c540d551050b80900c502445080e80d002807604401c50701d6074030b1861840c2004071344188000041d1010002d64614a541c1c407021000c0591661800c21041c0b4610b8030303c140c2d0807030600c2c1c00454203410110b500a441644985034a42c44440700c040c41050b1a81405541c0d002040c548400012894201c0e00c1464a406814001015140c000100d80800840e80001c804079481d4620040344 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 454451546 1250 454450296 454450301
    0x1d1c08040603110715020a0309080408030405011209120807020c041407020c1801050409020d0f050c01021b011407081c0203070f0306080705090603031605010c0801050d02010e1e030109080706 84
    0x80c100d40f0034030914198850303881e401000c2440350055001913010035800c007018000c1d030100c20400d03081a2019211580c90640c2540da0f4403500419000804001c2c044c042508a40910402c080e4403102c128959a030301202111441030040020382184103e071180c0b20140c485200d00c61965206003d1000203160901c0043e00d07102000307401c1d9026244a00a80740b4042c980045603055a50840e0082000a0b150000a01088003290042c100c80545c11240003040750000f062410340c1800e0f001c1c2c880c2e102000c0040c215481244035602e0201d6280c6845501c9400c10750001c0900c40e10030320410b810070100d035001080d4101c2c2c04a1029a0326030010a20240a801500c2c5608504841c07509002e51414008000d0f203070302e0b90348100b601550021011410560301031099480c12244080c07603035240011814990b020380a665030f00804100f072940007060904041c2c902440c03498068407490303004c01f84101440800d15108850b00202c66101c1c02680740c40da0203004444004c0d00503850309881e2025030900f5400c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 454452796 1250 454451546 454451561
    0xb150d0b01031103060a03031b02031006060207060c1a0601170f0103052e0b060c03070c050406051c0318120b0603011109010c110102121c1109011d1c08040603 70
    0x3e007110a10822003240da80c0e2440d08107807681854610782d03c42000c01c000c2010300c0003900003035140c040c4410a140b61b482c503500c450100c0710281e080b11045a620001580d10815808000d042840c131007080680d00680080d1784d0303801201c11315040b00c01c48106251490300d0082510515080000c0304010014010100000781c1e0442c0c1d5000c0e8411402035a16040070404070350300e981401e043e1142c42d00c103526a1444c1c2901ca1888005040c2d070703a10040c618100e00080500e0151522440ca06180400c1d181800b2504c2100c0c0c0c03002d408801201510f0340c43c180d80c03005024501d09006002003030301041e0389040320f050a043d640f0600d000301c40703400c00108150a503180300c200201c01e004180100001aa800340310500c1041d002a00c0400c80d01c84040102c0c01e1580144400c20600b000082e0501e99500c0e03e4a0301004040c880010000d40c00d40d010400b4603489008106400242008080c44224100d5201e107070603440c0c018400e0704a0b08490510160a4054507c15100c0000200c0c0030030509400d4001c0c040b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 454454046 1250 454452796 454452821
    0xb0907050f0f0411090307060203220b0702010e0a030213020a030f0509070b0307120507111006050a091a040f0c110c030706050c160b0c010c140306040b150d0b0103 72
    0x205010030450228103803000c0307000c11a10075500da03150304940c03920f01800c5a81751a406001d46c1d80258480d40c0103952a4000f968800403c0c40d0a030341d025201d400d040100041d11000a0728520701001a00115141c1980641136070380b10300c0100c00040103035918141030054681418000d0307192000d03400080d040f51821401501040e040008124181c140819490151910100c5286d2030383c4170b031107049825041c1d00e030009c40c1051030a014008440d40000741400c071041c2d164100c500c4009030710012000c0d0b59092140740d420041c0190184025071441d0410f4686035500d840c2c0c1080c02c0e41440010707056450008c814900d0580d41d610280c00107901813003402c0040c0c2000024002d168070440030a5076000e66200340310404c900030642848002d0706002d803801c1600312502c007803055a11050701c6040c9500c420310402c49c035071814a0304800b041c001d020105502914091060950381c80c10f090201512072540d003a6440004281300c40100030200002e821502c2d04803030002242100b6400150442c1c8240c8030f03d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 454455296 1250 454454046 454454059
    0x406030c1e08191a1e070f080714091309031701030f0b1008010903091e06021e0c09011d060a1503201210061b2a030b090705 55
    0x34845804000703444480c0084084032000c20400d1400c29a091441e403801d03803c0e881d450300c4103004d440c000205d0802c1001d8454044140ca0751140e00b001c1c0d442c174406081a0f03012461030400541d000d07001e01d0901c030000300403604152424244000040a4a840668803201c031a629090b900615034400028000c1c400c0181401d2186d50440c3c50346483d40c0d50070310b40103040c2402034000644035282545428014100c10000f03010006591402500ca540240185c20490181504c040c040c4003503010b4030b0049411940281400003601d009020117069003400100c0c16108100200c0803c1d210b641442c0d0007014900414410f071440a00d107810b00d80b40180c0154441d006d15a81070003110300c40020b0103020740c640d04001450248140c1d03480d04074040c00f1032601e0f0059011450710714101610740f003148250402e007002e4600980724003040d103a52582001c8141c10f000f28028210016070001184004043c9003d01c07840c85421070310724090000100d400c100c2d41c84c0c0840c8140001500708014260103000c00315000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 454456546 1250 454455296 454455299
    0xb010302071a0415020f0304060506060a0905060903011506120e010207030e010804060e031801180b030403110f01020a090302181902070201030b03160e09030702030307150b0406030c1e 81
    0x50142c21104035007408101c0b025000400d00300040c481d8003084645100780c041d074592040340440c114a4001715000c0e15450b0070f2800203525417600804546281007982c41d00b5141700c1c1440140000c41e0044010240c15650b03e00d4a4010a10591400c00c01800283da0762003442c605990b9520554050010f511081d80c014040100080c2d003154010320f00f41c000380380030150b5581e81e050040141070f09804c41042400700140090044a0b00740001110702c01c01e032030320000050904510240300300c1c1441600c2c0316180c20b00c04540064440e41049640100c0c1d403003244e1304442007200150032030703010481039004185505010011814038414400d50720003543d4a03a05140740a05080c100c0040400c0500d9031a507000070030b0411a0700a07840380070401c0001d800c07510410302c41044c40d0440c03030303c50040b00d4221200d0000903032041c00000444650301c0d4042c000e1806c0030b02503503990b1b0005c000ca540d421200e07600c607441c1c80c101342c4642c0b16510085000d120307070420052408550700d0580b000c0d00380140e041d40c02c8280 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 454457796 1250 454456546 454456553
    0x303020c060306031c0503060a170307030c0201090e0c031e251809051b03040305121302030303040b0a0615022a0607050303091014280e0f010b01030207 67
    0x942001400054030500d6583d90b590000a0800c0c0030303099101c2080c1084a00d20882650080c00744d403056409440403100d194031114074005100030180c01c000b003680b0400000300001c0c1f181c030b1843d54140c0b042c1445041c55813110360071602d442d01190707071104807440401009400800c0c80414045038600e10107481480c1000050341c0603035081d19540031041082c3c20445580c180c4a000c03980d030000c8003524241c1c003158507451010044c000550f038005500354040d219182d03080c207060480303011700d41c1034980c036240280199060b02d41e00c3e00141140800800480310f40d0241c4c4040c40214032951095403510081c0c60b2500059044071681d402c400102c102c5c0280001c80f0742d400081c0261800b1580000c003060084100d1680701d00000041d0b201c0d0131200104001c0108071000010314013a0740d040041e18030f41100440e401c0e048803082c0401e00042501900030a844501101821f0801040301841d00211241007641100b6034620542444881e4480404000301030f400b8442c846d0a036400346070941c03410003242c9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 454459046 1250 454457796 454457803
    0x30f184d0f090f370b060406122003040302010c020f0c01020c04020c0102090418151404110d020616061409120c0a02100e0102010b04061a0702061b011b0306030302 72
    0x400c0e034065064014007042c0890b0350840320f1401e890180b0384401c0d100e079a13841c01c03041c061804401c12070564201443c480c094500001038030f0540b05140e550752900280315600030041d22401c04501512070003c003440d42c1244c828001103100d180a900041070141e11888002c0c035142d10001c0703401094008000801c2e1607039000c00c0d0100d4102c070444000d40c5565000030384a00921441c00c1e242d5216151036400e51000d4840134440c90200d00031f03129420503980c250020000d1b240d0160909140200860018000404a400e15400043c01415005070b102c4144d010030125402001c3c070880c281c0c0040308400411003140110018000915800c603101d040c40b2080b10380d240c012070301c0c210800c1c3d4045264400c40c0c80030001c0c42000d40d002402a200d402c102030b0080c2c810258180741ca4010f500b0300800b9400c5040500403001141d143c02c42c0c40d00004802e0b5110b120071f801602080340d00103000c1142051119410310f5a40c0c4c102e40340400000c1c501c50118480a4969484803910705040c10b08070100080707500031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 454460296 1250 454459046 454459051
    0xb03072303061012140609070e0f0d06090f0b190615031d03040603060e0105030d0e040e01021605010605040507020609070e0408090d060c030f184d0f09 67
    0x9032031024041200710f80c190f03041c5244280e00d0f00c141c4d01d8030100d005007500740e00d02c0e9409400d0a071100b0a154407a0041107980d400c1c01d503080ca80082010500300340c1d5080c5034060401d814050030000501c4042e07a039560081d08991801501e4500340d00d010301201340d445040c100fa281141040400000703207001451002c03d03134401c001009140e81c8180c6e001c4204000c1610f040b03110020029265950744840001e00140414043c08682c183c91600101d21400c0000309400414810303226000820f104904201c0900179818080c0103e5400b032150300002c6001c050700f103100c24402c1c0008250030f0700f880144801c85400402034801c56001078140700d4400400b1a032217040d50bc00e008400110795036410680780303a110301c01100360003080040e0900305010465120301a80240c9507010f00c41805040240810703034030b020304074907a2059400401c0001500e044600c900807202001000403540b8611300c0c1d9441c0404141410402e0060441030405611103000d00c0d401600048409080040c4030303c02281c9140c1c1e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 454461546 1250 454460296 454460299
    0x103020603040c2d05220f020f0a09080f010504080f0c07170610060906051218030c06070f03050f0403260a0c120905150c0c070b0307230306 62
    0x401c0501c0b024800050140200901c02c00c1400e5138a07031204100c00d20310710000005034031900003103041e26001c041a62294803c0440400d0710f00c80ca00500c0041c000c154245001d01d60801a01c0f02c207942d48009418010301c642c5a510780c151a1168003030421030b040c014a002a4036000030007000420724426507080d404000501c03520390a001d0a061f24004040c0c0003190b0310361054450014842c00003c46d28407803404120f02040642d40c4010071f075030316070060140401184041c0408000d001d1500e44242d0b01c0f80c604510780e91008146003480742154003007440280d881d04180f04101026412100d50000f00c0d00c00d180030452460f0010710440086000f0304001d0820441503070340c909244518140031f80e041c1f00300b401c44c402d508021201d4002001c1249400d004034441055540c001c009503c076000100707801c10044e207801c2501824009000c00000c221b00b000c01000d0000c51000c0008102c000040c180e51103029a0300c1c140160047c0200105d51200c0b03211a034501c4100354501014403d0b04d4019a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 454462796 1250 454461546 454461559
    0x20a080616110a0c030c0302130902031b0d0210050c2107030819050a0609060501020318091b04150305060303071106030c0c01020d020712020f2e290a030506010302 72
    0xb103003030005041502c8400d000e0808504504084144803030040d94200301c2e4800c580610481c455100c10300280c40601d40065856000b0411a480c40c9082003001850920000d00340030012050b68005a0f03444d401005441c00202e0100344800b280c3d50401c03c1c141c40014802501d12403003010354038001c840c890200000c04005211020031941d81100c0d0001043c00813250050006180003400789004050701c1c0b15028840381416000103065001000302c447ea07c8200500d0a07000000c1414000844805400d4890300c61014aa15400c04130282c050005001c58401d82e642a4551500003010f44501400103132290300200482070010b00001c00c2451401019180ca98990340d0342c540ca1841c500420369020415400020282c074000380319401800070620030100c040202d0234041040740d40c5d5003069404000c5900030391044207a2052181c0744140c100750000408003010162541300306840c440710701d107401040c0c5102c600c0203d0b0300e60080498001d60540340181902c0c42d40d00d0f29541e400341072201901600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 454464046 1250 454462796 454462817
    0xa020c09130807031707030c02010f020703051b070b0703020309090f0906070e040b04140121080a0c0602090a1e0602011a190e04151a06090108060117070c020a080616 73
    0x10b00030010041380c00b0140c1c030f9405c450300d0030040103409849824100c02c019440c1107211103451102e4425281082d030940d50705801c000c4075428603000c2201c4607074601d10501c6061000074000880c00010807010340319a01940e2100629000d000c040403000e03080e40c044440345010032400303030780002d0503603032100261800280c1d840325070001c00d000300700d00402660000d007440d035148560813050721607904a4800120b00b9920003251041607031500d010071030080c1000c60411028400c11304c40d0f13100403205130207a640140340002507000911080040c2e848080302d00011140342c00d820300c032510140004c0038940000e1002100310754440d8403080d0340604582c8a400242d038240400f210700040c2d40040c081415200488d07090a0612140c400d4118402c000c940d41850303068921f81080c1c00b490b5001c3c1d00c000d0811414045d5200c0152240c5070010011810403624080c07401e460740e41002000d010750300b40d131250100c5240301e00500074502e41e607400c02031060340b06c503040c0b0942000c0d401014444000925044400704c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 454465296 1250 454464046 454464053
    0x4030f0f09150f020f06010302010c0201080a241502120904180507030b090d0e03030414130c050903011d0703080703090b0a0e0a09050708010b1b01020f0a020c09130807 74
    0x1d0741034214151181410b04500d1026402031201d0a440c4860f4080301e01008680950995945090000a001855180000300154081c400702034014a0417000418404121110341d540e2074500001c10004816048003042a03142c810800c20203d107040c40a40600901500404400e214015a40303000716a034500d10800c1c0a4800a186825070b840b9042d1040c96039030f8100342029000a4400d40180c0c00b444084540040c05009600803254019003d141054600f4520b09002020000300356080f01416440440d182101e100340e001c000015101d46842d400b0090600d400c54054040131140c104e000b45440d03901010000d400c8040303035400005199540a9407804803295071789540304003529140410078260b40d81c0c2010101d00700110580c0c461001c19170328058034080c0d4a0646860022607040001402641c2041004161502c14410050301c0450844603d17400c990104404e0001e06101280600d40c0d994144002c641c0000c045a00c3c4000d410f00001c5206000c203c46001400004002080c0701003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 454466546 1250 454465296 454465307
    0x90901051c0b040c0f080f0718020f0d050a1a061213120906020c010c150b030f151005030c0112050402030a06050c0c010f02040b16080409060605041d04030f0f 70
    0x201a80100311800508040c9005403c6044d50301030b0360b01d04c00720400701180c0100c0000f4448104003400f001080c50601e080406c110303c0c2c075a58001d0b0f50b010740820102c9101001000101500d89200000056920b41511803070100c4080343c60240c010710003001441020754840c002c0da40388a5424900b01d900d0340303e505401402c6590351000030101102c08140100c415003010010045609580995031900d0b4074900443c2c4040d210980101102c82040c2c100e10f030340115a101040702032001c0d044548080002209514200c800140d500c48030303009004000800000c4880301006020a50041074007402003400600085070702d442290703089953718002019903908114203920650415010031960400e000d04107030700d50148080e1a255800c0503450345902d40f061080707074102c8414071511f60070280c040340c404203400c2c003040041d036902c44280400719041c0c2c024410f900080c005619291b0303666142c801c1038007841010040c40c0c0c141003c07410400c00803981065550303410441c80d152220784268030364401d550 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 454467796 1250 454466546 454466599
    0x71e18061107122004050f0a0914120c1b03031e0412140f07050102060612010204030803090102090a09020702130906020d2405030a080702090403200307020f0609090105 74
    0x1800941200c4070f106000d5140b003c50b600145121601c040d604075101444144d03030054562400d805850000260900c699502844400748150203290012a07030604072858003a24040c809a49007000548012840007003080c01d8030300c01c44885103100c8a5443c40000c0e03c1f80141c4141840c00c00e00400e604846030304440466000d0500519400403074801414984c0c038030300c007126503240e01c0c0c469035810301e0400340009519011508141e0080280756610000d000e0b200004800004c2c3c0c940d001d000200c00908500059031103440c400f00010b0b00d859000007040f030314440540c000740c0c01501c100020001360725800281010190741d011b000c80d0a880514026000b4450440480013580c680716141d0048507000c1c6511001038006140c0030701031a01c607010540c07561082840140100010030024006080030b411050340319000f810b00c02820394010314613800d00301c40210b07110352a0704006002411454a0b44010724120401c0d19218100f0005e6400b00d0b071030041c10302030540b04008010400e041c14140c17034007001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 454469046 1250 454467796 454467809
    0x91505090129070c15081014130f09110105040b0d021614010902090606090105030103020f01020a0b0403020708060a050c0904090204061d100e060108040f02010314071e18061107 78
    0x2699421581005403440e41a4090900f01180c0000c0c0d50750224411b41910380113440c1d010300d05419902d40b80c10902c44002020f401608001c4000c1a840100c1452003a1804811840070104030341e48a4a019404c01309113600481c1404030511050002522007019111000c00000b4016500c0c000110301041c0c160350050020000c5443c550000215030b01900109075079842900d000b20240c44a00800041d03024100c1044d00003074040c8010000f604d880300c081401c21406005030751280e09175440351000c000c02118140e000d640b006200300204502080f41d9684200c0714402048142008480d0314614401e0301d8100e44903e0b06d4003440015581c60758014002082e00900310012140c14545c4106001001c50f4510f030000d81c0c06034000b070245941824140b04100c1651038800b03694544d95810381d544034800c01a8101580c58281084590400914901842203502c40d94a124440a0600c54418101c0c80c03003002c001001005041d116000000740c0c05555041c02c10126400007944950301d000f4141d0f0184 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 454470296 1250 454469046 454469129
    0x102031e0909062b1e2006040509073603021206040506072d120507020a030e0d060b0402070305040f0b03010332060901060915050901 59
    0xc40440c0c804800400c98000300703540c2c03000e007a81c800040183d0240d0318407100c882000510b480108105801400b80169846805c0015804240314001c041c8182412022070b0856181148030590b801c01a02905840004803280741c6000e0506002c66031400000d005101880401410a18400404400307608000d01950450860f41030868404c016a038440c40305a0080e42d403070684501203080815914030460300322005040c6915081403c4940c10042141101c1d0740701510000b0502c01c0e03100340640c046070900c1d0340d284454190f070b11402045403005014802558031038007036100081d4200380e441680c400210380d054602400ca007403e4001e0101d102c140c030360007071000890504054105015100361900b00c182c0401d459250083c06016201c00e00003d800032004520101c46c2c1c0185444100c8851812660a02800c0520354014a45002a9610601e03a5110501030080c007405201300001c100705084c911540610b400c020482c6141c040c0564408032148010f800b03400086a8528101d8441a40700f1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 454471546 1250 454470296 454470337
    0x11030c010e1c0804081602130501060309060e16030b0a0204030b01030f03090b0f0f18090f041104020906120a0603020901030501020a080109020306010f0c0204110f07050d0201020c060411010203 85
    0x90540700e069071840380542c0803140e202c00184a00c00c0008602c5103520004840c035102d510300e0159465602144100d0744a81500c0303c41d5503085070750040c035008000e9900c0100750b038101451305070305036018400344155960000c0c410a5402003003d10203421a6002683c01c0c1460f20b403d25000064403c540000c0d0400c0c8440000004000c3d005005d048024000d507038a564150700c540d90080315200340250011150410701004500c003280340001c01c1c0010821620f15002c0604001003050640304481d0400254540010441440794520314030b80c01e260b085804500d0301c6070a030001401c40c003507041121a800c035442e000886000d4140c1c814006550010001d030507641e928a0518007070b40c004110307100021a040000a10ba0450b4000e4a00501e4141c440c041c849107610401c8600c5040034006a80c0561590191b0f54041503c000500e1811000c0f00e1095a441c0c3c036060031490000220381250071a881001904e0790300c0c4010403001c1c0c101c0c0d40700ea484003a070010030004134518080e810108520300c216002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 454472796 1250 454471546 454471571
    0x70804020141040f060503091c08040201120203010803040303211e0b0d0c0302090405071503060906080d3203070503011d040312020a02030c070b04030c0f05030d11030c01 75
    0x20040c0b811000c0000c01c20300c0e4440350030190940200e03c100c14001c80c000f41c082c080207001c1ca0186510801a174200c0383c000400d159040c1c1003003000d040020214070134005200540d607102c4504102ca80d41188103501d154503020066681c2c0c41140f201404000320141045407408480c02d0855101c40b00316414016032070040c04d551040c1b10b903d1000b500003071410f0503070421402e08100998800e504030b1342c0c7c56546032454003800300c4050000c0080381c09004649011801c01c682401c00080343c11580d4000807280d003007103a1081154034940103080d19134019031303500242c01da03c4a21940900d00c40510810074400800794540020480c1c0c18000013410003004004009030300401441c121213001000744646548403111000120060703602400040c1030360102110202170760000c10180c030b400c2c8122894040300100680c205000d81d0021260754000080810034048149c1e44000030f0b06e242495143c4252038000003aa0380c18804c01100c1c1448206005040112003e2050b00d1417007030140c0003071206c0001e002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 454474046 1250 454472796 454472867
    0xa051c0204061d0f0111030c060907090e011a1504180f060506191d0a09140c0a05040608100519030201110102070302101a12010e06010b120708040201 66
    0x5820b0000c1e080c18100405083c4124020110040c040c0c64500200d20240045803996041111038445200800051620000c00c1000c58407070855840641412030510005000303a6040c1000500c003a810040c098211058065210718810411102415058420031451a26002c0c55200a0303242e200d50703400900b0309031a500105031422880c201000340a89a42c104980d6000300000166003140540320721062902441c49441e609821401b001c40400220340052008081500f122041d192211006214001700c0740750341d80c001d0180c501c800c1c1000c8500320024107a00562083c0b030b0403c4280b0b404100c0700c0b0700310b036108405040c01800b40910091100c00b072800003811444100d002409542c08005280701c18030a840026901d54060b044500701071502c04094601880e00034140c5003844125415551717542e4050910010180c000303e121076541030744509200d0143d104841c0d00e1401c000e00d404441c050141160701c0a590308022180d80c884e4001200d99245c03a041008154281702c10112000e003980 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 454475296 1250 454474046 454474049
    0x5060a020c100507020312180a050f010c0f0203030708070e0406150f0203041a130e24010e10121506021b15270303130303120e070501050a051c0204 65
    0x401140c42c031010004080301100e00403160390700143c009200c204030707219110b159150010b04501c076000060103000e00c0300e41001d1a1403412030300c0380d1010044800d414000e018640340c29009007403034400c42410755800ba460348001002c58040015400008481c58080e8060316005003014004004841e1217007016a0051200c0001e88003003146076110101c010310000484c2c095550001003d6101281c1c03000c40301c101e13040148903100c9100403600101e15090300d0b46080e44030b200d00c0d01007090140a4101080c10614000b00703403904002c640140310107562038009201070740302e62515080c61400ea0181d1041c0c010a030040701d00700c1110340800e000803010f074001002c00000004018641c0d608080108100b016214540f00000f201014010103d13080303a00a000e258500e201c0f110070035102240d03030000341560300403a400b544480240c90f090042c140c0c02019440440076296007006507507012702100c4e61350b4800f4072038507040003000142c0c000014410804d503406604080b001c6544002140d44030f0300a50401d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 454476546 1250 454475296 454475317
    0x403020306101a07080f03040c1e0302060909090a020a080709060603230907030606150f030207020112180807050c12120319180b040326150d05060a02 66
    0x540c1c021400402c2e21510080c2200c0b40710b05240003200d8411032407055504008410b842c41c40c4240f080b0308201360780360003d5118500c620b03070500c100c070b00701000b10940b2040441c0740c82c1c1903d170310602440182c0b14082103a8940b00c04440c0a00260348010702c281ca40484004001e4000600d0600040c060100141c1c140907181c940d40c0920400340c5660045003180c00314140e180c580301c400b9940c0d603040010101950782182e1900247c40340d542d1281c69540c1503c07000c0c0d0000201d0603d40080703c0701150300929401d5000018501035140203602d400003403401c1c044d940e0542c840d6079118914040300c80d2403682002e91917800b440541c0c5904441c10503e407140d40c40050706010f8201030042d40007200c40415030350350402814101a0a503120307803844c1000c030171504160070140b607034414550b00003448138054a0083c42c4640d00d60203040c070305441c0040c8441411001034440c9684030a41260750003200d040c40ba071002d0f000b1a050050003034440040c1c1d00c0202c401029190f402880103002e05519035030002c2844000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 454477796 1250 454476546 454476553
    0x51f06180f05091b12010b090705040317030408090f0406051002010501080706090521120408010c031505060403060f0b1206150618040e010f020d0902011101050702070b07062004030203 81
    0x16440a4951524060030407852552550400e0004034908030b24174a00822549000240c4908940081000303030382d00342c0f000000308501003010400c11206030908a0695142000036096080554804100f40915002140b20300001ea48041440c0c5072980301800403d8003c180010150460501178002c4c0000e008400382030207202804070340f190140c20950304680020b04000314040c90385500045441048812940500500b1210a40030854030040d0018141d014000200c02d102004003604484601650314020000900204640e681d07480030303141100c2d004080071566503103151040e801402032800715980002c0b162600101003000041c07580c0306600000803180003001c01801c00103140501c0c07980000c11440d504844007542000d8101d13103a8080fa20f03001040c4420468182405e9070040894030441654800341c07101950380c045000100350344814020031050510b0348009444081c00c2c0502d450075000080c0fa41c0c100180c9a1000c1d200703c0c000c8042c20150410003103442c1455100e072005034464030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 454479046 1250 454477796 454477801
    0x1518140306010911030609070c2f0108010b041203090b04090621230a0b0103061b05120a1e02030103030305160f02072d0b0a0f0903051f06180f05 64
    0x140f0920500300480d40907050b4174110f83d10711080080b14000140024104100707019a030001031000341c4480d1108040180d04511000f41421203451a180d1000c03650401400304010800f244010303007142c094404198942061840301d013030948902d40ca40d03000504840c000500060381c410f02d98001e10903281401c41c00900308680c0046841c1001034014042c0440321000c0b00704100c044140d2410741c0d4020140140e4448040a45801d030202009920031b50381603403204c0051842c0c40440e1410f000c2e1042d01d044c03440c20f0207259440c1d04003010b4018001e6407601e0b95006024030400002041c0c4410842c5240d0955480d80c6030b02e4001c000d4402540d0308160200d400000014250203600e01c648001003990090090500c2c06045001210800c00025900130ba100a10401c510601c01d8031406403441560195481c1d1202c50300030002e6030944015400c12840c1001400050000306041702c0203d0400c00d200f456001d50900500205140c4d4010652014100400240030303d0300d821160111142d0b00b0104000e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 454480296 1250 454479046 454479059
    0x1050301060912021c05010e0706020f07150507120507020307050f06031302011101090605060307050405010b0a0c02060d050a0f050604020306100810120c08120a09151814030601 78
    0x140000c1c0a49000309400410502c190980303050754100c1c0710300050035100000c400070500900680a01030036680e44c3d458544081c0d02c1d080802444c001410184000e04c1d403001024070254545001d4042c40908a420101240c0d0980c4900b095400b8190440503e040302e1507a44c0f40a080c5902180c1d00724040e004032000060207140c42c42c04890019070141000e480e40c0e0301c01021148141c107800007281440100c0c440c003c2440000d12441011502c69a4005150705200c0308051034040355038000c0e4801d0381028018400da0f9405015544020f29506121803880907600c0012094052003d1888402d850203041006155254005e4243d90381e414904000c40e49501091000381c1c4411100e854228041d90703d028030403480345035010b5000007901c1410740d810703441d0f1048c1200000c102000f51491a105002400460b07410b02130b80004174103800c0c0051402c24000b001404000c02c0344038213041014800ca011000c6402007140515903014828020340041e2510010003400c183d01c400d1034002c0c450030f000450711 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 454481546 1250 454480296 454480307
    0x3010803120c0f0906130e1509010b0702060415140333060405010c080405040207030207030b0f01051c150c030c020c0919090212102a080f0901060e0c070203070501 72
    0x240c014100c0520381010481400b40d40c1c0c6c4580c881e0b910001654400080009844076024018490a9040a00c0302007400400001c04812f810003019031008100e100c006a440300200d0f41114908004000300d00b9508c41c0c06e0b600c5442c4003000814031800001002440300c501ba1154036080180702c2c5001d0b01003000d0300e5410540700b2000c80d154020074208403d00031507001d580c0d130b5071200d845414010300d819210400700782070b42c100540032400f50713000a1040c000c00195102559010010348030840a943c0340500140d020009aa544c2c0e207c1c258040032241030280d0700c102d01c0b882100f07002043c0002c40805800900502404000c00c006020703ea02c41d00c290720300030842c5030148440b14440d8203980c07200c2c0c0c2034034003d0032100d000304e034008080c0c0505041c103030060107045802c014100002441d01d051488000b058200e25146290844807030240d124480d400c150040c2d045030404050b1111a96021203080c0140a03540003203111290700410403000c404460300400c5058400c6d401e80700e4455170341005440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 454482796 1250 454481546 454481557
    0x15040609020a080d0c060f0204090f09030905190302010503130b09070f05040c120b060c0d08190b1f030b0a030503030a112b020d0f0203060406080706020d2303010803120c 75
    0x41d05c0c0726a84004c6801500054185000500018501307a40c074050703141101c821100f2100040d4903144101e00781604110740e07000800c0c0c141c4445040c0d80c40544000030f98051070200a06004001c400300e800a20144400030283d9401100c08100f8108094650fa58400c1c41c40360300d8103000b0105000c14a41018003c00208542c0b98483d03506502054030220050a0a0f003512504280b0901c00c481004408201d030106482c602e4441048a041115424544100300608140c10b0313414142101803d40b43c0d901c00c43c20b40390b440c031000480c000707481350103e0141002000003644015200d5000c010701c03501000a5014511407541006128001c01603d0041e0145640d44104800401250b0621705203481ca52031100c01d08400040c54a4030f2008001c0071202c001d41c0e2950f900da804820000305003014800d41c00136001d01c100420f64286811402556200d1049014040020040c0c00a80500078034000c00c1d50001240309680d00c0c0e6842d00350700c83d80c0f40c0255510442e1080124046a04910381104a91 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 454484046 1250 454482796 454482823
    0x141e0307030b060d0b010e070e0609060a05030402010e030303150f0904050d0f21020703030b04140601030b060c0d081009090503092704080405040c0914090915040609020a08 76
    0x1510a1a64036040c0408400500464002d545062404e0000e40d64081e15400380c0710240ea00c2c40d41e070402c41e80050003c900c0f200b2090090204102d420580e695807001d56015400d5881d03d03680d65509d41c40103c4844682840460f0507110110600100c20500728038406915800c0e9500102040d888041161058060710064001d4204c540c00d15443d511680b83e0440c00100c505080741e00c0c80c00c00c02c0314010241c080c00080c000950100d00303030041503030600800ca202c2c0002ca500380113010b003660103120700c1030010740342c541817655805c0540c0c51a101e00c4140c41c2d000f10007a0030340d0300281d44880c000c2d181c3c07001211609998886400c000c610b0075114880c15004a412100450404e950780c4144404c491b6020810032415600b559201503a661080616102c1da20076405107031514580001d20080c0c0f40d10840c0d510070301928140070f006502d040c6000768018001124400c103242c03992840300c0e042c0b2107030f0003aa0910515020411082c001030b40c2003014410b03c2928024200d90752084155101c02d81c5c0552203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 454485296 1250 454484046 454484053
    0x408090619032438130302010e030a2003150408040608011a03040204021602030f0a230a021e09070c020a050109150c0501060f0807030b0624160804141e03 68
    0x49004240c080c20700d9010041344012918400640380710000b441c2c2100b13002610303020410300c00f8821560300c05881c000108098004104101c69551444841d0b9451000c05190440c281403001d55960304010040d800c140e0b800c401611400c060070185440d44c894060348020030120800024403013684070b40b070300c030070182100c03003038299100c070350800006e5801080040301210703024a401003d030f5018022000c0000400000b404050010325000b144100c24520302000b8080c94032111207607070380204489041940c1241c01d0b410056101075110481410707d803542d50400317619820444182e070049801003c56000322904001c55a4490046501803402d00035444852040c214141c0c01e28001d0447c6000c951184002103805502c61000040389540381e031185060303a11600d0100144400300308601c1c2c100c0d0050f650400007804100c41034520352103200d001c2103c120005540322940c0070350381800400e25804840c1e80d0342d4640c0c981d0f236800599000c5807601c0c4190629a000c00d6100c1c2e00000d00f18101902a018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 454486546 1250 454485296 454485329
    0x190f080610180207080909070c03020c0a050d1401090503030c131401050a0c05010615020a0c050a0e070810080303150324340809061006020604080906190324 69
    0x384406500005400c881c03511046c0000005665000030091017100982d0340c2480a95007070800030f25107250744140c1402000c0140003408541c0f01c4074180c545503600030a204c1034541d040300f00c0a00401c403020300035002d40804024400c0300241030004162100752015200d107075a0301c03266280c0c4e1404030700c00d1280c0450342c00c02801c09124001c40c1a0b0380d155010b00c00020325280e840340f100001030303403145200340113800c00c00303815080000740c00505001d044156a03036a246418810352250403900a0004802d00c8034190010702614800184100940000310580c0d840c0c2c140707909079544420031485c0240c402d000c0c203104480d600d610030b004151641081341062140b82c071000c83c0c01e903804030290403a030307207403048000d01024800740801c3e600160b0701c0ea55607600c0c041c50700c0384c1e0903030902c0000345c9040c1145040d050308102c00e642c0003429039000364010083c00d42c0c0d01702d0800000e4451103084580d403a03180d203000d02640e1046e01503101e0319203602e841240c0d102d807600081e800041400c144c02480c01d0090b00f80923 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 454487796 1250 454486546 454486589
    0x121505010f230a06021f020304020603010b0702060408070e0402010f0807020d050901110a080705010e07030f03030f180b01090b030d05040909050a17030601170403170402190f080610 80
    0x14807a5016100c2070b850710207003040010401440194004902503486418007942da0303032003101d105646000440701142142060b0b80001d40d80c0c0b00c10310405030203010100b842c42c1507544001c110390041640e0000c80707041d43d40d81d00da44100c4040440b4280d011a0100642c0703c3c002c6d0050030070511031105035001e05140b0822480a031101d81080801d45d0400c5205100b2011410702000401107250080d0040c43d00c540c50b80c5016400d441c07080004441782e421a00c000c200186c003c9924860140d454200401d10401079200c0a0081091400380c0c090302103030b01803040c103000380301601034141c406211042c84910440f40034195907108840c61107002032010041080101c0950740b00c4d1090520a20940b80d40700126141c3d04810007180003805154071001091110540e0065507034183c0540c98240c0c6000c40c41c1944002c0c1c9030814947c0104000749100d00080d045546500c0d03188003a6001e4500f40c050143c070350390201c5200140d402030030381511811021a101d480c4082d110406c4901684500251807040344 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 454489046 1250 454487796 454487819
    0x2070308190e10090c1703250602040311030d11101a0607080a1805090a1503120507030206010806040f380a0f060e070e1207121505010f 60
    0x10100301d44641c1d80544140c00c4409000300d144496a0b00004100e030a464117001c010b0040d15840748444404041c20601080c00c0401540c6001260b0620390341d0302030f501c00700f003803000d003036640300424082c8000b501200300030f044001381440100a80880c0c0d007266203a072041d1001d4010314001d1016600100481c080c450140d0401c0814043c02140040090300701c07808550140c0000c04201e600b0640415a01c0ca110360008455030b802e18401c64540204d803600e00815005040600301071042a111801e840003020a00411402580e020010700440444508d0040040d08981c1c0c00300c0c01030041a000088244000624a01941d080488040c0c2c0c40d4550360b907103001850071105040d0030007488550b0007880000f640c04003c60200c50111000515002c1011000c48082c0c003ca07203801c078542102404200c41c031030a030350350240300c60400364564615040040c0048403101143d403c5841014004140c40c6020048108640d205134a8010f01250b02c0316040305030341c401d02481c01d01405e1064100107841c500c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 454490296 1250 454489046 454489081
    0x28081b1603020a0c121a06010507020418121107050307050609090912030c03180d0c1b030b0108010b03010b010f020607083c0c090f06031017010e0c0402070308 70
    0xd00480d07403d04480c1c0d41d140307500003070380e40701c4002d00003540e80c60002d00c1803402c00c01906c600c001c202d0020916080c80007a03c0c60103124800790150b9a144c1e00341881100003410003252540005410700024048600141500d0098950100364001c0d42c80004a80c2030000b03560045d5a0001d040c0fa0820b49008184a13001d100103000308440d02c5901d1040c08104007400003140034425a01d11907550317290188003100444e8040e200448a0340c0801341c1d0440d2140c0c0705074000700843c0c4c041c1444d81c208000f020b50f01308580b0640c002400010b03a08000088684055112004c40c1c14160001d02038402410010f49c3c81c3e4806600c458056040003000a6800e886140c0c901ea01040c80300040c4500810580b031b0940e04c10314403182844140c00304032880354040715900443c0c4d01940011036035284c0f510200110390443e480c02d070801c1c0140300c0440849ca0a02c81c00e860240074100b00c1d00c00402d400d503c42440d0b8068110302031412528010200c080700310341020300071910400d030140c69011550300c5404d2011800c0409 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 454491546 1250 454490296 454490303
    0xa06020711120c0f0906010519090f09090203010e01150b0903120d02180307051011011b0507060c08130b06010e0306071805060406080612010228081b16 67
    0x814a074034a0a5039a0711401c515624114000d000c1c0284074420b02c001201c000c14460710480703410381000102d0780c2c880f040395622400302683d2039030320030708440599415490740c0020f011031400590110b031594842d803140c108540218003e00019804040c010b080703d01203403880034001500101440000b0211000b010012400380440300569410700c01d0026903000000740303040c2d1a80025030b002069130707003504180380796000310040d251091a01000a0320600c4621580d010b11950003128038000c0820351050310214000c82000c00c800115800003070065114101c2104c1d02031602c050b10003418454485d16101e0301e1720703801140c89000540c6600b95900c0005241c2c07810041a070340315180a441c103025903800f441403910b0b0a4070301e000d10a040d040000365a08541c0c001c1106000402176281d024040036005a0262000045410400b1881c0d0180c8111140d440c400700c0003290900501d18494403404c454512a621000c5541703a9000b8505110103100785400c040a00b4040a0001d01c1d0032042401400d10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 454492796 1250 454491546 454491563
    0x10c05070503010501140301142514030c031f0f0b0c0102070f111809100c02070f030b060108010603090213022b1a0a1d070c05030d060602011107050a060207 69
    0x15141c0c000b82c2520002d0b040125140740300c0c00500401d04003401074481d0081c0c08801010307146424000050708112201d40702100c5151510700070311042c00b9080c00b540801311490000e0741da14114a5513003480d072003540c40403000a465503000f0016034151600000f41c9a001800b190650b25065003422540c01020901000d554200604070000302c0003000c8501480c030440e1844a12810b440421030321926000d060031041c4103100c01c000c0400303004943d102001460a100150305031300d506d0100e1a00c04550040c040030303a044100401404032602000b40b140c20300342c1c0c1e410130507030700c42e8003c03000d4039480300300250491903408480c44060007503005882514801f02c0c06402c880c5844c0c0101c884140302c60003d40003a036450110381c4801c020000e00245070281900d92118452404485c0392890300500c01124803118480085110580b2403d8980070f00313a0440c0c1140d80350301c0040c0c200c600800e080cac41014007562030310750710a0f42e00703041d0401e0303401050b001005028041a19214000698412803088400d4507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 454494046 1250 454492796 454492799
    0xa0605030322050103060b09040c021e0c0f01090617090313091401061b080d020f0c1c0f02070506030a09050307050a0b0a060f050d05071a0c070b0408070302010c0507 73
    0x440c00c1010b41103460010003250701d21140d040c2008035400c866000a81098109403083c0564405141203a071100380a840026810030900300823400e0202c54407482e440c014505079100320070007002801140c0b4400896400540b403e14000542d1414032130304c60000800d401000328221290b814081c5da504c40030301810b503450003030520407603c0b10307400c03942100741d21540c3c403500120055850009039002d004982400701802c01c0c0030061202d007000c4070500070440c1c200041e20b500c2640960b010754138001c850000e00c44d283c2c030880303c0007526020b1003681d10a1102c1d10b01d04140130b561059400d45400c25040d0023812007141090306105040d80024000c411003901c5462020010b0402c200902da21402100a0800c841003480c04038018000078068030040ca052080900034001c0059122040351401c031035a0f20401c900d440c043d400d0000d2a42311100e281150000700382c3c1212508010308640c9002820f0310130b0540c55a090b0070b0b01c0d028a004061042e40000c04c03d10040d40602044520140a182140c19030b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 454495296 1250 454494046 454494049
    0x70f120b120f031b121e040905040809040e160603090c0510030c021c0f05090d020406170d0813030509030708010204060504061b0b06040506040914010c08101202010302030a0605 78
    0x30444607014059000055284031101843d00c6074020200c0040502242c503048907a030750303050203039505d0340c0641280e05c1c00c00c02c0c081e81b05d0411100100041d400c140f147d440c203070400160540140344001d00a40c10281c0000d0783c00e10204c0c10308075010058480050071400c0c02e800301c00410620104980030000c0201c08545503660b10400310454020343e4001c660070740c14582c000c0c1400c40744d03213140e01c1840840030a61040342c1c010400d46c1d4858140c0c1340254940c00c0b02400111141aa1031000e03401c58509180814486001822240c141500e0001c8070500131034800111001c3d1400c5801842406c00311080c0c0000a10440c010301400340014221fa03405500d40e0100d0342282c1c015480700022500000c3c0030410150040c0d410b80d6045d515142d207814500d2251918040e40b03400514061049a03141d0004d655a41c2e207511645400390030080004a0b4406d14200302d00800c05800e0040100c2c0e001070000d07800e09004801030083c0e0302490404400c000c0f0b15030042d0301a42015024184264503607a020486 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 454496402 1106 454495296 454495303
    0x1509030c0b1c0c120506060c1b0402070c06020d0210021809040501060f0f05040506040e030a0f0c02120a02180c040302011d031501030b070f120b12 65
    0x866841111010510b0072403244414250f1421114031905607201880c0c075204503601504020603102d26040080c0d50181d4600300d0f8540c0d018200411941880750241c0b554050b000d04054104851603445000c5100340b40c1041c0010307480b188823040c810b035040110b2807000c110a407045141405030310f5503544e0002c0c0382d08145d004207155008a801c10109610450041440041f82c030041c0351500281030b00d0449601c09d01c0d11a5003030401003140784c5080e104540082c848a0015440c0544c440010b484180d0740300c0c05041030001ca0450039015840380002c3d0600f40b540b0102502400b040c600c1004082c840f500010b86503001c40d4403c100b0000324090480c1c041c0d070b409081081a05541104503c03401c2c5d542c0c8801a0180140000801c5020040307031500d0589201d0314503178200380d4516104644280c040310400c2d0025803100400380c11386900e0b5100c40a80c1c10040d1a441c40346000d00c60342442c = true := by decide +kernel

theorem cover : BRFrame.Cov 454316546 454496402 := by
  have h0 := BRFrame.cov_init 454316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 454316546 ≤ n) (h2 : n < 454496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
