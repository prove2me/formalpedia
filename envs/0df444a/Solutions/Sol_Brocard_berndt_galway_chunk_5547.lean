-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5547
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:13:49.690145+00:00
-- url     : https://prove2.me/submissions/b1447fba-f877-4514-a2c9-286c330cf54e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 997482014 ≤ n < 997661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 997483264 1250 997482014 997482019
    0xc050306090c030606061c0e06090f15010506070c180915142a0c01150e01030b060d020406050d0302100c050903101508030d060f12080d0e010b211e0303160c02 70
    0x70031104604d40110f601c0d07208245000880d0101e00502143c41d99504040840100304410331006020904c1c4c00b41c01020054010102c3d104d150383c0380c00192103000510304a556080780d0341d00b0401c04001a03007000c80c401540c3d40b0000c01030031a500384002201d54006013501184482c07903160004082182e40c1450344914680d0540e61510311a100d03443c000c20020b03851801e8101c0030000010306000c00c540321416240c3c85181e600f12a16507106120f84950794000803644161140808180d039141c05d05803d0100340298000c00200a141c1c00c55001c84111031504010000208140740c4140c5002519848088040c0310006500100041d107003040702c244d40040105000006440c030000149800c26010703a94031032207042003190340d1a5402c01d604000d5500610784e440c180040000307100b199001c440c2d8206494000f090030b003d820f00250355681510034020000c0c2c0101e05104110340300304550b0300c961651000000e10104080b600700e50781d00000380820741400c0c0900035110410b101d2845032900c182d01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 997484514 1250 997483264 997483271
    0x4080a0e191701050c0c070303030c090b032502030915031b030405060108190f141006170106080610050904031e031e060605030c0d06030f0c050306090c030606061c 72
    0x21040d0b110103000c03046249030303219800c2a0200e43d84071464422507046240010007850801d00d10743d800c1c2c6c05008020308000a0003020305000440080142c000c52003441001c2260305516610003880c0301e818441c218000c1103600074030000440b5100c6400c00f004400307221140c241c0f02e60b03031034410244581e0101202c811100020062004021000420300d069034031000650f050805440086001510798541c09080c0c0c050610310400424955040816801d40381015644d03030150740c0c0d03403c10548041f6840700125034a0241c0e4075407808028407880004d400d204000c0c00301810305002c450481c00c1c650045511802544005c1010140100107a50000029860101c802d10b2600070150040c0961034000380600309100070f0040840e180e1103040d007600c419071a40360858581c100c080ca02c1307402030908240c0d030581c0da003070110104013805448101140700700850880c2c03d0a00c424107060883c0900313034540e6940700203c0c00595a80c003240325a880041500c007141c0300da01d042d45008904c1310300e4480003603c514 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 997485764 1250 997484514 997484519
    0x31104030203030c0a031e0f050c010b09010b180d02061e0c060901020a0f08091e0c0607050303040302210306011224060905010906050d0f150e010501080f04080a0e19 73
    0x20200c1c50041c85400f0b44c0711000300c0381071007900c038010401c8042c03031100203148e0311158843e80340100c001e00f030320880120000441d6000d10010030b680403002c1e080302000081c0450010442050b007040d0901c042070903910030300100d000c1d41c04612540030b0360300384a4005029481c544030110061060b1004100b0304011075155090100e01c0c07600030740c001c3d0284800100414008044140501500ca02401100c0001c003804a040071140c045040840780d84a2a4003d40120010036070340d080c003a00300b09010b58003569580c1054903010740f40c0800d6640340c049502c411883d03424685818025607a02c4002800c2041455000b041d21600812046142c2c81e110403000750609868511016414286d030310300d448140e4995210001174840c521070b8172803c8000703842013101403a1424540c01c40e401110803d400410b00302040054015110881c2e08001220144400100003540e442040d06421102030803004400f81001d031500c42c0c443c850b007441c14061113219007c2d200c054440c50080010301052900103800581c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 997487014 1250 997485764 997485787
    0xa0207180212070804120311070b0603071517010504050402130b04060f0920090f0409020a05030d02100f02040501090308090a360605010e21100507030f05010e010603110403020303 79
    0x1900344c0301615509200c0c445601214000d10a085460070082345032802c0c4a882d0351713558684103008103815098042c48a0010324034840450300b1000d18100e840e44882001f105291144070b000503408540f0941c01d200034040075813034261101c4a4842c89030004201c0054040105020300ba96902407107044060070f40004e120301e0694042d01c070703410030960400101425045200114000c40e00416840301181c1c0b01c4c404031381303003951085141e2840a07100c495203541d9200041c4c1007001421409001d40c001d503d14034515400b511558542d15050304085042a00f0000028041c0c0310601000b08a100300185900007940d07110928401071070320500c070030b07104d6491795004903265501030138085003800040d80741500200d1600410054801c103a542180149603041003142c801c0d04888946010606c03100003d6607400d050000180134600c00e14042218149600020222800309441001d0503240c2401130080c54251004241122060318001c640c070302020b14541c2e06031050342d000030747c14840015403000c100f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 997488264 1250 997487014 997487027
    0xb0916140907080402061c0b090c1b0303040818011b0501060801151401050a0c14070e13120315090216020a05090108101109030a0506090d02030a020718021207 70
    0x1680560700504603490348003054500400a80b40294410814402c0044581e00740100d92907905d903a00380402d8085003040800d8003048140c40072105503200141c0d0802c01d024554010300105640c0d0002c0d07180d4030b000e49608030580210f000d400c0420440e1092210345070701c1450101244000d0f621495420032091074090700801c03d03803251100365400c040110340700002c1248080101c40a072500307408140701326401110302e0382c0a5072041c006d00000d488840701168080340599180b6110300020405582024036284010b0070042001c41d00a034840c0c90b01c030016000c0310704030509850a00780801c00341800c0344440342055494000c2007516101062000078460205010701c106070080d00c8401009848100340000140c090080c1c0c0c11980c0865407141c0680042ea00c80c0c98204010b813011401c0091300c3c3c00080c146000c0003002c0d1200d900403c284025008140159082944c141c0021440c01c2c900c607501030340f50341d05c41c461560000c201c0c0208001411950b0100c0d551200d0f0b00c0081e140603d444500034155 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 997489514 1250 997488264 997488299
    0x3050307020d1a072307030207210b2a030702031905210a0b010201060b0315061b0d080f090c010804060f182901180b0402040b091f09030b0916 63
    0x640130a480c03400c03002c5c003406040703600443e0980e01500c0c4490a10038074011442c03030024090f04030b000900d00030000c21002071000340a8101030f0290000300c0345003030b0207060b4030020803011700404104100780501c0c07540020480748000301d513641401083d80c550405447da4043c50605040c2c04010307441802201503c112218070840e12440c080101d880540012402c03280103021308440c0200c104080780c8695107a42c01e0300c584400c010103040c0b43c5080412000e50240325982c2e81e9505034004041100d10640040c0d4a82d0301a502e0b44a0250358a0322a814075518504d625203641444860030201c0c0a1150a403c615560100c0c030405011240032003550380c821a1040c041610041080c5015880701b013010780d060f0b2401242c3c1c0c41d40c0398840c0d08041c0d02070183c01114081107a40c0e0f5955003940c441ea241c03800070f44010545c0210741c686401082082c05001c003001100e50007000b410a81c2200e04a411070500011b40303400c031002107065695542142e1030400c01c24200d07100340d000001c00003072040c07400102508 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 997490764 1250 997489514 997489547
    0x2001020114091e031e0c0c010309080d180501021206090106081006082e050a090b060f030601022a10030513150f091a06030703050307020d1a07 63
    0x10301d5080c1e18414400010544075602c1c00d40007071903082500c1e89202e501000c6000250709a80c9400d1081100342101d01551130310300d1040301e003c0740310300040c0401e00c40600500402c0c07d0502044030303641d0300c01403142304008841c549141d50b070706500a00840001296001c3d40e001008656400c0090b00a0206201c1203942c544560b2929001140c110320400d202c41c040c0c1ca2648a036118241000c00984091800800c098030508100c1c154201c107014041c1d040403a140d811a040c0341507800d0806020010b90b02d504070580702070401c044500719444900c201c8401043d289042616a182d090040b4282030120320072202c5058001d0304064403030303100c2d000c0309080d62045850f410785a00d0f18205400f03580d070848c0c0140384500c825407404d010513018007d41c444260301e010300003035104060402d102101c402c4201626002d2200b90051074824020000301e800131003c40090582c2403442d0344082c0d5074403070030700000d002c0c02071504924200070110202c090383d0340090391114039038039080030010115241a5911781 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 997492014 1250 997490764 997490771
    0x20a21091101021962040e07090803070c080606090402030d0e01090801020a0c0c05181506580207080c0a03050c010b01030204230d20010201 62
    0x6001d5800050b680c0500070116040444095240d00c41d4480d400742d9004091061030590408184059054410303c1c0e0442106801210881e4000b95210103c12480484d65100821249080180420b0b401e0b20304481090041c0740c403940da000720485000c92035600c0942940300c00702e8040b04001d00c400c00c039020303070310b4403011100c84d0340e1500200f003074414050340e000e505034102c141005040c2c0c1c82050010a0ba010606054090f1aa02c122860880c0c0c043e01d10307100000e401703465000400c24845c91020040c01d040300c203003504001102032010500b8002e4498403114800988915041e00c4d24010b85000c81c6041d0f41c089403601d1090710f110504110446000c003a000c010180b45941c1501c4a684058114541d0b0390824014422550320300a40c0140425205620f00740301698501c0030030840954414404e0381c0703103500c1d01c42940d49982520380307940c03486044c9401800103220300005002100007a0f0680c0d41c61401103401e5201080302800080001b0b848160741d42c0f02e0720014181e00e600300b403000d0402c5e030080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 997493264 1250 997492014 997492043
    0xa060618050c0913090311060a0e0f0f06070f090305010606050414030d140901050d0e0c090f0c0306010f030f06092906070b070207080a15050a0b0310020a2109 70
    0x442ca1081404503a4000c030740300340d00c40d1341c0c104680c040d500a621a0070010486001030b6000c80c40c1242c1241c50b4040540c0364200400c504030103005103203c3c4640d60340181612521180f0885c3c40d50802411b81e000c00c24500c8550250134480c0c60080003c0d5000002004501c1d01c0d0840180280d1141c000c405440c80700d508004900d06002617201100d45842e81c0b100c440450351201603260750700070350049041000520070104945d0080c80b40103503d0110500912203444410144a4400b00c01042516020003500c01c01503403241d2101142d903c12002d203003448074414145000e07030040466059880708185002408144088030754801c41c81030185448a48600304100504411030005620840c1c00c0b01c400d010090000d01050426500a03406005881c080c03519003140c03510f040c0c0002c0701900c00d1014004075039000c402910038640c10400c012800d200c000200700219035101a80300c0d40445807540000d5820455200704243d134100804420004207550144071220090503510300140c60190400088 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 997494514 1250 997493264 997493281
    0x2206060e1f02060103080a050d1d120a020d0e151215271012110a0e060619031d070305060105180a020309030702060a050d0c0e0a0e090a06061805 64
    0x56074000001c0d5000b40610b070b0950b6503100460700072070150824030074184204810a041030007503440c40140160f211402c0441c3d506c410740b80000091905018880801558a15071341c08940740801c04050704214189030a84004a2418000070140c0c182e464008221803000604100129000e442004240d25180c2c640301c0400c2020010010031501c1058044000c96000c01c03043c00c2030350b020800b1154403035141d40e070f2440f48500038501141140c40b42807403408881e0501d03065084001428402c82501224a400e0021031828403980400254801c14107440c1803060344280c004250820421000c40342458100b020309984000f80d010456682c01101d002251905082c601c0c150100b00c6e41d4a202c0040e102d8000c0f803c001d51001d0542030490000300720400158444500800e00d407051039444c0c0342d8902c821559042200c4260300356508021030504401030994136000c110081d03804100c02c1103060f8031246034031460400a0700c00144460705007000054a0124580c1d01c110040715480103000982c3d41016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 997495764 1250 997494514 997494559
    0xe0102030408030d090c030503070804030b250509042c071a071e02060f1c2c011410030506090303040c03060c0203090a09020d06080c0604052206060e 66
    0x8003202c0d50b00500c140340419407140c02c18840140500e2162609540741e885440c25075001301e0041e1201c03403001038108100043c139100c0542c0907a09040003800d00b443c0f01000c41031627600141500800402007600c0c2a2550b459008a04508109030705040d007102648101e002c00804418205030b60044400000d00c9005004901e40c1d92240b50310103a151016580c1c40d084015906070b00510f85000b982d00c2180180c440074000c0260304580380c40140c81755010040500410003c0614880c083c1c2016846071401810b144049540081803001003100c1c80100e4000e0b004107000141e94a08031244c40c188070001c01c1d107190314402e5900810684045070354050080f03549201c2179030024881e00004e00700b000410f8a542c01004496207510681e0b29143c1000c00242e203810b0740380c20065060740d00140d503102c546203911640004150071009002e904410b00000346d024015403245034040c07000c615210600c0404c1c0074001d500440b0050701002151b8482c04014101090805480d019041248401d0a403482111 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 997497014 1250 997495764 997495769
    0x706021e070e04260301140418030c02061804020d020721170a02040905070216050a05060702041d19060510030203030703030b151b0c0a261f09030e01020304 69
    0x301c10300d02d1a2074564a213800c2003904280c43c070903004040c48502c200440c0c00700550003840003200a09528900504120450b101b8901c41c1e07200c2d00340c51550712300003500803c00c00003803034040b9051501e4070754100d100403034000e048110f107501501c005400c129a20b41540a810341c64001c04030f40500c844406039041490780446108008a0010220851407144140105078080c82801026080030340c1c0d030240c101501d00913070703070703c400358001c01000805591603140d40d80040008440d2040f42da40b1300000b1a0040c4a2424042d000d03d840d00b0302828521031500751480d019400d017003180c00b090300c2540d001e42c00c4c080e9203400301c81d22410600414000c0101082500903039400034091480c0c5500c550f429801080e85400302ca400c004084c0d0300350404404c181c0a40366000901d104e001119610900c91230a04203800306551050090349024006008134100a56045074442525081d0780c01403181c0d2464010350756410f4400b01e4009103a800d18903481d80000040741d1180c0c4030030b000101d502006a860780901e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 997498264 1250 997497014 997497029
    0x1021c0b091f030f0503030f0901060f06030b0d120c11090403080601030203061f1d0d170c010f060914150f0d030c17040e1008060412030e0706021e07 66
    0x50307010888000003a400842c2c050b48050151140560725504c1da0244d507031581e400e0b203198201004104d1041080e00c21503a000d03803c0c0c0000c029030350600b880d1007142e80e05402154101582e030504c601e4a5240c4403017115985801a01609041c00c03400e10040501841c15801c840c40701c50100030006a040441416000b15856200c1840720340e10b9400440c02904000c04440c1c0c000d1100303186807424104009500303083d11042d910104008120a2800340d001c020000b26400b440800114001140c055a0300d254803c005c0244035581e00414a08280503008100510590301e02e000300c001381c041469407196117a01400727031102c260313641d940c0083c020000701030b000d054214000307661a08007494034541d5119900d110b828022440304c100e0f16440c2049001280d00140801c002600703000d514401d90a40b9448484102e4500b212070400010769203661300039200411501c0e10300383c84000d1900075044100b0140540b0304440c3c0c040e030389000c000e40c2d8841c268207001c00c4803054500743c1c2c800311001c94450103542c0c48 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 997499514 1250 997498264 997498279
    0x9010e0d050412060b060d110c010b01180b1b030a050a030f02030f01091815050103030908061902031312080403030506040605030a020d05010e030d0c021c022d03040801021c0b 77
    0xc0d902e13410042c0104042c0b046c0d0011040003029082e01a502c5149460400520503d4440c2c0f11001c1450031142e1040320b0505200b840326450012098449100080e80d00c000742560301e40c495103121004540844400010714040403c841640c1030380324000e4410031a00741d4046c000703101c0c200c10711402c81c40305076408480c40301c6a20040c420380f813554201040b100240450b2128440c803c0d100c00350445040d001c0240341980b1180100141903001400201401c2d19001410943c2014121541219038107400d0b04d9215402000089107a180d9405c0300000c150080010029081e044100408040c0e0845048010919080201d01c0d5030800b8802d407400e03114042c0003010640815001c11658039030f503441c220b40c10343d22080c210010180c240080c08140a43c8100070420302481c1c0303006414012050550102a4224001d11a519600085403054824030303450500c90117032041311088120904ca00142e02e50b1000140000f0349810550081c40f041c00c16895a0201d0480b03c1c00c0e03d000d5442400245500561 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 997500764 1250 997499514 997499549
    0x5090a020d02010e041401081c0203250c09050f01060f05270402131809030522173708030c0403061e0e07050306010b070c08010509010e0d0504 63
    0x5000c030000030107900504080c00030032044c00028060301d0941160045003400c0e2001000b00d41070400400403051680000f840c90342c0703018a0025524024030303200d002e1080d0704511035000343c0d0445940d0240c264200c51544274540d180c0031110041d183c1a6081e0311899088000000e25510074040e180c160080c6030b5540d858182d901012000c13281c1d000310811581000b808030220103654030300c01890101c2800010500e25840c203501e9807070828603e98582001070a106480e0000b940c05000c89500c1251181c060010340c00c00d00484e018503c0d02d0700b00c0d15030401c040340c070440c010500003141505030b1070041d0301d02c903800000c00554901407910703904180085540b096903000910a2000f440c2d01403801170304a800d00381e0780d132105019542c0304901c900c8030b01041d0b41c803104c101030302e401990040a03c080040803105d1601d0042566107005224119541c003003c50032104210b641c420700740043c100c4000074070482c2412024240281140400c955061248020b2640194000d00c25a822940300d4274110301b5203075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 997502014 1250 997500764 997500769
    0x12090a05070b0c010f1d07090603031209060e0f071a07080a2d0c0b060105030f070e060d15051f05030105130e1c08090114060d0c0f080c09010905090a02 67
    0x1000703604186a0f079502c8002c41d0404054a128010340644403140400240905000c600c0c1004025000b015440f804d082061011036000500b24001c40800e03800000c440403642424001402c1000c0c5081d03003030180741749101c40208005020381c20b8595440051003401030001c6000240c7c0b280040050030079205000c0404000e006103d0404d001104102040d000c80200350a01540d5111280040200d00340301d0201003071002820840d40d0120007800d28925504000b880c0c8810500000c1c5007000700310540c1546087d6403102c109445020700e4041d403d01c0b07d03ca088162841c03800250150074002c000c5980e41040c000e5001042c20020a5a40c46440c0b441e400c28003401821000703442048042034440c0c030205d10342c4108000000484e8046800303c1b82c1c0d00c204d500020f103811005800303141941c0c107103204101c1e12411802003507081002201c039007a94050034034102e006420315078001001c5005a420011303100d0b2000c0348050019130704a989030610384c3ca6812031400c4980650307500c0c41c2603008201100050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 997503264 1250 997502014 997502017
    0x50a180b01030905070b04061805031515060f0706050604270305090901030510050c040605370c03270605070201090e010f0f08030406020c01120b03010207060212090a05070b 76
    0x2448180b4020814200075214285086800d50140f411307220001001c010303855020300c807090600b03684401c0b0a492454200001c1c0d0b9a4222445101d80021a901050820407140d0f040003443c500a080e05803611b0303030002018583d4000f030340103480c0300742403500140051800d4481d030301010b44100c0c862401038101c070459180b610030398a0102d040c840f0401c121041640c4004e0958003d52240004200110008080342d06941c8050700c0800f00c41b50a1000f40041a00070080d41d030801807100c0050002c0120004040d604d0542d401180c446140401c0c1c08440c0c10346c4010a800401d001e62560002a1380c4558014a420100314014018241b1074038240079142c841c40080c0303802d03801490a060003580711480703612018420380c041d024210340701400b0050b614440c82c83c0f100914012001d58206840d0080c0652a80080181c540c1080724036621040800b4003a44011610603014000715100c0c0304a1429600030b60084560030004156080001c5005000184809041c0c0d848800341211034582002c45846 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 997504514 1250 997503264 997503281
    0x1b03021b01061208070825061808180316060206010510052104020f0901092403050709021b1002030717091c0c02030616090b04060804021005040308071b050a18 70
    0x903440400c1450261036080300c0e0500d80d0039051f00140c51542080c40d00c0c20841c5c45043d84130441064007500e1130040b82e04030090b80c43d1403100c0b0b00c28110040241001900b444040c0342c2050342240350940102d07034981e0015165050b60401d860900c0b000c1ca0000c400d5035035025429034815461601401c0010951211f0480c2c2e4010784003030400040c07000c00000042c1d0ba000260030190080c2d98034842c4140103c1c070303000d00120b041038a0384680748a40c1140c81d100c0d1900b00d1802101101034000034502e5003e00c0340d400b00055203d03040b00781da42e100402c264a1010f9401551013200040040207624240300074460490302400b800d40003003110310f0060822078080e100ea0400f110602843c80c030b010b4003503142030016505c035044004549044c0d000c8020041d00d044c2a540200a20304014041071060780c0c0c204000b680c12580490722242041c648200440300c0e40f080784c00040401313002054960420007154244814441d410b0410341910f6201c2051001008151158034185001000070505030909540103002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 997505764 1250 997504514 997504523
    0xc061f0306090c12060b0f10120905150103080a0201110f031b1b030301090f020403050a03050310180207062706050603070b0a0c0308060121020309011b03021b0106120807 75
    0x103059079200c001d1038810303c01c10405d5070380580392003040315140345c00381c0312000104044a01e401541110b14004100040707280740b064650b6901e10b5040e0910008001d607214101d40204d64401640c2c4074600161260042d88443d07001d5800d007041400103201c010280d07801c0e900c0c0061418119907030080300c03018000c0303000700b4501540e0042145821100340c201036046540c8030700000b103030780e5407600c1e15072802c4640202c42c2c2c4039403c4c41440140700155001c100c03500ea080e010b203440ea442c0e4407031042e40881040103500440204074480b42a02d0284859009000c02034041c034410004031110820218070141183c04032215015000314110006039240d1103160410405011104859142c1444054a41c4459000030104403c42000701c04c05038040507017a4011420710b0400e200d15194412027101d1414461108480f5801000155a094095000d024588003d002081d908a802038024000350b000c94102090610310fa05103207078a031014010841104c00981039401001850f0b211a039694110100c103d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 997507014 1250 997505764 997505783
    0xe010f08060a180c1706031207080c07062001090803190e0a080417010905030d270804090614090714070804030b162613170c061f030609 60
    0x14030f1604020649201c0812440009400e01441102134080e8051594220201c5000020000a910041003945c1003606009100703458104514007040d1500908003a1412071154010018503c0d5020a80c4000c9282e10300c4682d405410380c02207142648ca044c6006000c8600c2000031944402101c00e0004120203100c00000c1d010302580d0176a81011054036007500c4001c00400c00340445190180c2250070f81020301d000b00080c1d00d15030b580c06d45902802000c540416900c0390604001440311255200a01c0d118001441a00300da20b41822903130024092648020700e4550041549a40d00d02c01494841d00180b43c0c880c20b070780302d0340101c90312000300d110030b56249810f001e2a00042c00c58006800070350700c00c070003101e0946041400c0303440c0034144190030001c02503110040d18034101c60f000520320b034000c0c002522809545450fa051244600301200411007140d071203d00c14041200c80207040501d078418260381c015280c1c0741840c0f0085440e001c0c075251003103130300a003000002c12075441840900e20505218 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 997508264 1250 997507014 997507019
    0x21b060c030309011a1906050f04050303070b01140d0c2c1501020d170402090402030f10020d2301120638040c0905061c1514010e010f08060a 62
    0x140c00e5400549800f034980c0e4541c1003281d0322618407074004100c9101a105400100c2c1121046002240c4500c01c072400d05c40d001803802140d4801030202e130b01910016085940e52040b40c6041225010240f055090401d480c80300d02d0111300c0d009089844503038003d14100507450a14140c1e80e00d034144891a848140e052808400300300501c021258820084085d9607603d0f04681000a8180009045000c0030440343d01080344200c0000c0549640280d0140d87c0f4140a46e9284082441c0c4102880051000d10a80191000c1c01c00250014141c1c141d0301b10090201d1a051100c608055603d0744051200e100c0742c80052000f1401c855442e01e415004a001290480a0100040380e0320040000d2030305a5050100d0050281445440b803810020169020400b810780e04c0030050010b003050154500c203040c0012928a0381c0010042171032840c034000300810142e11100712000c0c0c2c1c180306100d40320340042d00400c54407241d03020f4810102e070341c4c0c03040e1242996180354190860300000d0003060642e0000718510301 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 997509514 1250 997508264 997508287
    0x7050429061201031a0601261e0c36010f0512010b0c240c0c010b030d030603020306181903210c0e03010203010f03030c0203070e090307060e010c021b06 67
    0x240343c000c50080641202c103080d00c0000c0d0005176001071980d07041c00703045584401520000140c1ca61001802c008002c80394540d2401d80b048140c085510603011134599060007242d11403800140002600001034a26414440070406000345604044035811030b2a510303c9403095014070044030000d98903184c05440e1070101030b041d98442c1001e8104d80300f0110085031840ea40c03e8100a01c05203600111020781400744211340c400c1d00501c1c0100b11001022000c62400c00600003500300c01110440141600c0d501402ca610090080070144800d034031030710982001c98020b401c60242d42d4901f641e010302511101c4142c0035050b004290704201102004040701004c0342000c0ca061080c54880100c0e500410207500a001c01403120702c01e0b1a0061080c0d10400040000070720441d07065044903458207103d42e2000c02400002e0130944994400c46c0b0302d01504003042030004002c0000c142c03481c0708507010000c0c61010f00006088510000c040000f590125481541606c44100c6101c0140d0004203850310380300d459280c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 997510764 1250 997509514 997509547
    0x4090e241306061203110f0d0509040e011a0406150c061d0d030504060c0e09010306050a020f0304120813020913080d0f0e0c010807090315110403050f0705042906 71
    0x20401e604034480c85140c08040c0e12000010300280d900009014151a03091f0154681548506800901c000099541c034551140c3c1c0140100358107130307002000f0310a00201e02c204603099840480c1d104510744240031507400d0510a00340c60080180d6030301c0159440c0750380c5240003014083e00110340808441982444182c04022140c1c10f100700da82d02007054201480c024003a5a586c00d0110b05100300680d4643c49500d03039242140c1142c0d0131100218668994003480d0000b07203d8803d4548411500104000c240200a5204d200c000800e0f170317400c0c603543c0c1c542c000c0d810042600c002c0294409110008560143c480888105490340986505882c0110501400c012102440031516040341ca41903500e02c444418800f600c40b1301000e0812041914255200500311f4100380401852056400001602c40665a01c81580c41900307401c01581c8548a0030041d559003004030322600c0c1480340d0480440c10707050a0003a02004601e007a0b0f000c0f54581c81c08043c0030340079401c02c184c9030842000c0c4116040c0d1400e804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 997512014 1250 997510764 997510769
    0xf0d090602270303090609090c04120503041502070501080412300510060507290711010509070308040b090312041d0c130302040b180c04090e24130606 66
    0x100502c400c01414004044030800030540d621a030000e00c2142096200c3c902217a41001d802c8420914a130703105041500b1902407178203c002c0080e4800020310800c030000004005a680000c80311801c542d000c2ca080740da884a500078030b400165584046400501044d890001603111401e108000c0314566800c00c0c6940a641d80c00c400c9507143d0a010600c002c803500c2040e0304600b4081401040900b41720018000384501c450041c560b0000b000703501e200410300755201842c500d040902603014280741000420072025007110b80599446c2c03d0209560000c001101030032281d06c850101e0a1515044e440429a0400001c10b03030103005241c0d00003d102c00200040c4090040408444001d40c44d8000c1910b500344020050003c200c1d04001e4900b078002e11250300001c80703038120350101d42402c0000210b0501c03000701e0081c00c82c05000c1d07014042c400c8403984c003030000d41c1c1c3c02500402140c401d07020000d03990b0000c0302c41e0076801175019052401c0000b00c0644a58440d1786440c04103061052940c40008031303102507 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 997513264 1250 997512014 997512037
    0x60c0812070e011106100e090a1509060e1605100314090d0e03150c0304030e0d0302010b03120a080c0a0903050d030603110904120f1110050f070f050f0d090602 70
    0x2c424500d119030700201c42640c40282c04000341000e02e410010795010040f280983c450000042000a04d0030004009010382d4550191408a10f5680c3c1801d140c050424030008945450821650f01c103600c00c0081c207686c45c000c003480300b0340c90f07103180105100981440569100815480e1181c8608003900032249500903544d8000810030f40395200c1c0c008008400c120002032003500a10700000e42015001c6d00703160004290360b03120340d69072940c0c58159041c0c06a0b41d00560007010208215040c50b40640c01410300c00c4003a0141c80e910021040440040e1003a44d0011000c611048013007426130004101904546000b4181901041e07266229186081034001248001035142c60081c0708010090310514002e0342c0560b0102c082d41826035500303115240410b11001003050f0b5040810200341b01d09420000805440d054071103202c405035051018110455882d11040700382404106000e1050344243c481401942e80d407420081c103000c3c506940d9000d0103400c01d549440d04110800b1078990f10080c020b000b0351 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 997514514 1250 997513264 997513277
    0xd0305090a08161422020405040903050c1507051b010e0313032609120a06060b07110904030c0f032601050906030f0c1c060e010b01020f0105010609060c081207 70
    0x4603031041c0121083e5004180041d0132900f0048050320340380c80500518000303000300989500306110340c0c03000703002c0e039440654003c1c00c01c680041416008001001d440f510b9500362050714a5114090008200554110000038020088907448040f8420000c81700812040081000030300022840c1c81c51b000001c0071a2500102c4508104018218207280800030341e4054001c2003444482c042c400500134440c0860060412018250600d2010312080522950140040100c40d031510b030000101d42001c0e10490f04120104030030036081c905802c10300c0c459981583d0380c0000e001d031781d0f484010040d0803880c02c405121000c0610b101d03c80140b4400c20a000c002c180b5298207600d000104483d0b128080c100c1402508942c1c0310000707000c3e002c52a000310101c00d81c0c1082080400414030341788810407002c003519141c170f480020409084107402c0081c0e4050240d0840740780030321040096080300c100380f0030346000c074050300700c01c2000c58015103c54803040e001e07030074181c2441011240543d4040b0109c80c0304001810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 997515764 1250 997514514 997514533
    0x260406021c0513080705010f050403050c070504020f091c050d050327100e0a05010e03030907061b020103050a29010f0c03021506030c120307020f0d0803060d0305090a08 74
    0xc003564038881c1e52460a02401181054480b120052094039006840c40b840007410000348003003501b0801101c82103100410035482e00703040c000c01c079400c8480e80900d58012807000007014500384c0242c0d219840c40714031051038810a1410003129406480c0c103070340414600604540400c0046c06032142074010340c0c0b0340c0740e07903490207100900d46240018409180b403002d03640c400d00c0c3c0310320019409a006d2107412000901003200a4240c2c80d1092001c4020113030341c24070018020b0310401201440c0208103510441e014a034440e070b01a80c40007138600b8a4041ca442c4282d820000d98840e8208980040342001c0c002154140c55138200b412428025a40031002c1c10090b24604a59100c0110b0a60203128505a00c0e45002079030300a4a4291300c4405e8032074140080c02241080d5401e00c00a040b6030b40003024000030b039180141c5a5180e400001050384120300f800325418090070150380c00c00aa0f44d112440c0392540d41c0301000c000301c070300618405800b004400d104611564440949036000b03047c3d000001c0c0403103071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 997517014 1250 997515764 997515787
    0x1f02070f030609020f0117130201021638071209180b010906021914030c0625090f0612090209010906090f062115110a11060c0a26040602 60
    0x4031070175869410000340501c240c4403031006203003094000c440c0101102c00d41240d400100d00d84140300c0030005102030340740c200240000340e01c03220b140150031811040d1b413002541400000c00b0b5080d52901a8102d2040100b0300024594401c011001445400c182098540b00e540849005403078542180540383d56002c2140c403503070800f0b8101c0080c41c85100901c1354140903080c2c0012a43c041d400102691042c03401c100c1800e10600648401e600c0400c1150640d280000d030f13004d007110008811206030040c580c2042d440300e00c1003132458181e90500303101021003031030f1160448048040d030340142e2041d582c4190402c0182d03100310026000740417802c004514079081500000c12030b0501c080d0f810300d06260030010480300044040e6422000542401086c4103e22803c3c005900703107020000701c1d50246007500410511300340001822400819a6407000c03240040300f402a510360060720403035900c8000788641140c00d849a04d1a001d020b895403030310444c0d030f40008051141200c4c03e83e0112040d5402040618100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 997518264 1250 997517014 997517029
    0xb0403030c050114011413060b0c010b01090f0b1911011b090909021806010c150c0e3a0602030a090b060d03080103030305071b0312050903091f02070f03060902 70
    0x4213a1404800b0313440d450300600c1d244003100d4070f040c10f000c1c1110600558281c113540c0d00240040040c030110542e82c55140d00c07110700800d00004194003207900190301207000700c4031a5055017940c0c1d2400900380752038030580182d03088540c0441c000c003c2001c0c400071a0081c00d020b0040c103800d91461069036418050343c01d4041c00740501504503030000307864802808050780d60349600e421801d00803d5030118685842d00102c2d05550001d41c0a09044800310b4004512103032540000c450140a80d28004c8081625041100f18203d09200500c400c04601d025070754124043c503074080c2082080501e411198540e03480c40140d07002221380a1501d41c0c0d8485401c107006c0c0d00f644140d0b004208845035440d62002e690041d08408040c0805810150ba410018024602482c8c20010070300001040801c06540f5103002066664400e10715075106046c1800b14200080000039240071050090075180d070440c0b2002102d03034084030b21508008500c120b2000064681c2054900405580103c1c000700e0250b107a0700501c9440c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 997519514 1250 997518264 997518281
    0xa03060f1a0f03060d170715050609040615091d06010501020a020d081e12041b06093c080c06070804050402070c0905090f0f0606010207030b100b0403030c0501 70
    0x2429840840c60408110388111150b516200050903201e0300d070302004c01e850306041100180100b8110003220810441d000c00341c9841ca204805ea80030741c81405802c40141c0f58140c40c1d0f507402880e46404200082c0090308007401c50b4000114150b00c813680c5000750300c01d80d103c02400c02e100c00c0081e070369068041c1c428031409014000030b00081200c954650301203009181c6844001e4031040700420300172448020f00402c418240b0380070344550340301d101d0058030381c0100c04180c40480b0146000161149520300c11181401154210303111a000c00303140c00e41d10b040000e41100b490801d21a61802c4d140c0c0b02c880d1a1041000480102100103854280344c1e403d0b00d881d5400100e01d2140000b4000c00740040d442c103088030107481050790096107440481c5401c00f01e2200750380061042a0414080007861080011101302c25202c1108850207a0481d00241344c891006440f030350b0050700150424004601c001c0d61640e0011980c00d100e030a407036915900740c4080d401507042140000d1a03016081e0074400300340102c024 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 997520764 1250 997519514 997519529
    0x60b041e0911090c030c0d0603020415050324070c14030301060e030f060907090c0c06090b0717090c0108061206070c2d1401090606030b011a0307120f09080a03060f 72
    0x3c06040c8545041220b0200801004104000082d6480315500707980041d0000c581c05007060181d000c1d40304402c000745901d401014044e100b400680c0c102500b541a092500084164403c2890f44808a0407952072410b40800c6d034650301e03c1c0c80d80d0381c0a0b501c100010b50080071141e480000003502c00b4105424012031485a8115a0100003807115800c03000c1028422510034000001e000009042c06540c0b002003040041c1146140481c05e109000e892000e03248605400c4e610b070301629803403041c80c42c04040305441c1c00e00154081030f1407911a5001d03507041c1d81c201c0c80040000310040406040b2500c0d0590803900400001c60b000344d694200920611018900900000d80104d49a030081d406004000c9030b00014000201c6c00d218410261360a500140926070070240500210791242402158007a0a2251100f07401408182007030901084055034001c1100c1e039a0201c3ca60500310a6030080d1258100c0c0020031a030341d02585000844241c01018041400d0702c0105225203000307030060080195500c800e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 997522014 1250 997520764 997520779
    0x106020a0b0112020f030f0607020c010201060311040c05040e040c080d08070e090a0609020408160b04261005010806040b06010908030f0d02130b0c16030f060b041e0911 74
    0xc00103040c5007030903042da1030102100c01e07851118000200c001581ca41126014024086612400e8a012405922940c2203400300c03107a42c101c14004a017241c10501c4041c01048020151084510f055001462044680d00c0c1c00c505143d152030000f0b40564050b28116a00e84020008001c0322070b05018050a41c089828040d20b5480c018401601800006000b40c0c404d800500000d404074600d60301c0600609408081192a55183c410941d074400c2c024000503241c070a00ca1000035124500011201a25a0701d0100a180e0503141800c415800701c180030000303140120038800220111302d03c1542d008100220062646080c681071100012101808403410000d81c200244071b114000012510400e0203620f6956171407969040c80d5000380a04000d502030302d425031b00000b407480305060142c200b03080103405903490010390000104407010244401000d00e9110030b007180108000d0740c800980b204003e4030210b4610302030411300c0b8101c021000900c509039510040d2105104404850380d031a042c003500c806 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 997523264 1250 997522014 997522033
    0x5010e0c0f03042a050306010906210507030512030f06040c0207060e0609180106020708070501020c04020a02031905210c030a2003010603060905130c050913020d05010b09010602 78
    0x9005128088820038001d2000000c0b4040006040204078060481392444c142201e451401d02d0705084688030b090311a1041100100c0c02042c244103884c00c0b92a00c54055110244c540100710f4052036200042d03889000d038a400001007601448094109041c5441d480c0d80d03882c0c9000403901e600005420180520700e4400c100402c16000103040081d115a81000820600b02200040303844c49100042a04410f2132080c20051840c015402030685d2011740a41e19034640303d09070710790341b20100e1146d94016400201c0f0180d2608182c0d0007811800101e1042d0307481c002d07061032408800d4003181d90450003d6000103080f1240b2208108103840308100a032132901c2e0b410b04101c03000f10b5001c090310601f060ba50b0b440c002c04141101c2000580440030055000c2d8407580c5d2103001500030075162041415040c00c0c00c0c00200f00d41203078102d0210710b9500c4020444031604102c2440010310005081803228102c240c2c01d2005640c420405401152040c00041403003041102489036011040e40400c05661118401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 997524514 1250 997523264 997523281
    0x102030409051021050a0b06120a0b090c01111f2c010e0114010e09030408060106120506011b0f080c0a110a05010207050a0b131505070203010c05030106140309030d1503030305010e 79
    0x3c003600758000c07e10140c0c4d074603080c0002d6080e03403038110780040500c1078400c0c01c3e040002c0c1503000f0f4451010101500c100200302801511214005102500950000900c1d04102c1c4010103004541101c00030002a03040d101400a0048214046094032500038100c409950304a00740500c07c140507001c00244102e4503080000030741c49406001d07010802d0b02036000104000020010b036030051444d801265185d503541d07500540840310030b000052085090400040b550750255581070301140140c00c0210550302e854440c2840450758a1040340e9140c01000190381d80c0004000c2010194001c020030304554031400d00b082040451540401c1c15500700c0e00c0c0800c050b03602d81d2154404c0307840e0080ca4a90f20444240c030845210b840707030007500b5080004035139139400c03590000150040900c2a0001c010a80c0003210544e0703035004c00d101e0790f80044e0f400c103402004904081c0186800094000450b0b0900c01c9109020003550b0030302c0191061110842c0e02081815498061203004100081e035101e51420003044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 997525764 1250 997524514 997524523
    0xf05040c052b05010207020619080a0b0a050d06090203070b0901030e01180222060b04090b090903030601050a1b050a0312020c1b21100b010201050906060f010203040905102105 77
    0x10b907a0640d0381814a0300034044290112400c1c0d13036000f410559682d0000c2440c111540a00c00e038500040c01e05000644c0c102c0c403500c54000d220b0310040a015039249024100300c12000d044d40202c50340b0b911141d10400603102000114040c2403e03101d120b0f101c070390110004041315890354032112981e04100c090f42c008104410603407106901903603550300e40c508051703e442d01c9001d036170120704546140000002d003100c040302c050007d950110905200c403d11413010015084010f40300c03100290400c0001c01c003503600950007402103e0107420a110303540c080300c83c0c07640c0390400700c04103540d21b810000541041661140c280018030b02c030200c0450070f09003680380342c568070501060150a601e24008852845503940b40450000344500d50b240d0522100d082200c98840e64220b04420780c81c0e0403c1d600d1201580180240d07440352400c2e00080c400380ea141000c10091100015009040d07000030480401c170030702140075182c4560150410040028036007110f881c03e041c1c0700703004003500c00072003441140081c40208 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 997527014 1250 997525764 997525819
    0x30b011707030f030818100b1305071d13020c060405011b081b09090a0b0907030207020f0402090d12030606090b0403030f08060102070801060e0402100c0203030d0507050d0f05040c05 80
    0x174202c80d240d81d40b22140801e61410000b001118411101c07818840f03000303a0008000e800090b50364030400c505111203801a2041514071502003400085141030360983c0e49041100354400034030442d4028554000701d0200c2c8d0101c40284040c3d04000104001e00000740940743d02402414030f040c80000c68007400800c4c451018060045450314685820038a034440d105542d041480249400e6550401c502d000c0010300d05848528022942c020016100c64060f10035200700369000f900700c10344100d003030f0100300095100c90811a1b102449130307400400300700010b200b0039000007240c40c000366140c00c100024000035040d0384405e424130410802880060f030300410440d9000210700308500c240d202c1d04011707030929410f40c0191819603c0c20070005244060442d40f02c4c0540c1c025111880860100c10040b580340400b8400650181e10420020803142c0540e804290301240301c1c58200c1c100071220003007109591811a44290040d214070601c03083c854101001fa004103011074400b81c0c61564480c0000050a141 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 997528264 1250 997527014 997527017
    0x80c0a151409010e300d050a0c050712083a05180f0d03110a05160302071d1603092d080301030c06091211040207140106030b011707030f03 61
    0x314000d6007903401619103d003600b40003024070709088120351908001036044480070281c5c0030469440541050085800c0c105110b05540d824038000c21824252070b401c0b801c6c041110305105a84000034150710b004c5403002c00c1840381c0710440d503030784400394060242c92200700040b03003050060070b0b08003c0403d40b26011b10151035009c404525560703021704c14000300e8201c1041c84898010b2507009004088040740300e021842c055141040608207003542e2146138000c01c40d003040442c40c104441001440800c0d161a129031080c4100d4000545a07a848425a0081c944050b48040c5510030b010340b01801424005d00720040385010421000b060300c0c0c02101e902500801054200351400c220f04c91101885e071420595007040b581607613075a480c41e00000c1061a4480c41c00000c1400703001042d00f40c072010388080c81c140c1000b40c1680c03269903441003200951100c00122045c4644400203a10500c082c042d250065006507960003040d0f240045040c00d03540c22070790710320300d80d045842d0900020f1000794481c102d141d0035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 997529514 1250 997528264 997528267
    0x1b01060b0a1715120c0d11030d080c090405091006080705011409090619030503190f090b190e040c0e0102010f0905060f04030318050615090f060d0c0b04080c0a1514 72
    0x88912541005c0301e4a601e150820000070460061003218480301d220400241c048a54280300c807442202c240005079190329543c0020040e00581d03140581140341c102501000b950b1011a40800718000c407000d540c00341034250001081080b1642e003011500c0074000d1607501a40ca00302035080020b1000c1c2d80208280e03c61540041d000941c2e03079a400c40c2c3c001440d0b00c801100c0d0303200282c96052101c03c0c1140e10346030008030715a00ca100e40c41d00c40d003e400e048a00c202e48907800c0160b2468081c1591002c103c0400400203441c5070103400f80e560b03016441400324183c03914001c4000c3d050009003918101c88002d0312450422080c48000750000174000d40c00344403890986110f44492400704d018169400030042c0d00b0000d2152101406804a43c05d030043c11100c0c1c420088007406030600801c40e4045a402c10760701242000641c80342880c0124280302c51081002c4c250040e00c4456030400358010740c00c040404d0307010711800710440c10000d04040180981c0c805021b43c030a91054001c0002e85d0002580180300e40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 997530764 1250 997529514 997529539
    0x1031103010c052a07090c08090f191101021501151d1e0406050d120305090115030f110918120403081c061a070605130c0b1b01060b0a1715 61
    0x5000c0340d4003402d0580401d109203074240c40010601c023025a040280c40c040c00105103030364000010340d030740f400c2d4200c80c940707281c40425125041d400d40c41d001d40b541507014047c1d0306484080d4111241c0d01070000560200032545485400515080343d0602c102c0010040c1001443c59130b8034207201e16815007019860144c00e40805010030b0244c103141c0c0c4805e130080000c819074400c03c40101c60312060180b26942c01c10580d40c6003140315090f5420310101e0074010240b210140049403110b001c0c102d4140c002c0080c903040c60800c90100e55000b030304982140c50044050401d009020b0305010b0801030908903940141480c2c02d40c1c0391301c2940d10801000b407140001c44200020b90038051780101001b01828101d00e00c4130000b19964090310f500450b030480d100c40c81c1000117413640790300c01c0a004a0395000810880018284200540d00740d104112080f8002d0340b0f01511400310304240a82d0003e84081a041500c400345007002503c50144c40d5204c6440d2841a4100061401c003001080b00301581200c43c4d412400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 997532014 1250 997530764 997530847
    0x50f04050d1d0d2409120206010308040b0702010c0506160e010908070905280603060b040203040b0606090d1b080d0228030c02030d020d0e040b03070b09041401031103010c05 76
    0x1074213403010b44029940c0440d044012240e403240e4240ca0041045d429800c0780c842c0d089842c0c44007400024100042808288107070b421100141c0340541c1b06041c910345000300e58031218904001100d0500c94100404c107200302c45a40410021401700003801c11000450508480a0302c5075024001c0401c0b09541b0717800190001c0030005c0001d16008446800c4c00740c2c9291a284a0190100740001d5a200f400e201141c00e45044c42e100301c9110b035070400c1e0003803420344440040100642c401e50f80b142e480260000d03140c010821211214030f10300701042600070302c0341c64034410354103104040c1c00410554015407000b2150740c1c844001d40c10050300754408040c0a600525050342c0c0b039803584501075010b00ca2403c60080c034a03000204244501500c1d2078091040000c13504100c243c40d51145580e0705500208000c101105800c1c0141c03101410013032001c00da550580c01c1259205209034015955200d01050044250400784240310b103540d643d14045107004070300401c0c02160880f00d40c015012801c0c030843c0c1c400c1c06 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 997533264 1250 997532014 997532033
    0x391a0c0a110414090604031805030309010807091a09030c010c020d0303090215030a0c021e030703121404030203030a050a05070e060d0905030a05070c080604020f13060306050f04050d1d0d 82
    0x8403d444003812a802c10b058030694800341110100c0c0800d00701138006580300702d0f90005904403403000b0000e501e04000e0b00011030304114060101f00a205100b0b4021803038041d00030111a101010b14132103a110030445003054500400c00240c0c6041c4603400c114580540c80b01c0158120f031b9901400c020540001901c0405c06021038401740489044009c000e2100d000c01d40c2d00282d54070452642240c1d000b5a00d80101020510074031582c44e43c95100304010000240103210209040c80300d000700188061016108010280c011075046005030800000c102e8484d00b00d00c120743d04503194600801c690b242c040f00150a01e81d050b084a44215004200d80512722950740100c100950320109032a103030a0305200290041d0003400049030810142d0300c01041005002840510840d0001e181071140701c0700b1818003103556400542600132076119440840801c1084c010240546451000c0f03064520741810402d0400d8195101001009541d100041c80c03c1741500d11940a0f00c011101d01d003072480c4618141600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 997534514 1250 997533264 997533281
    0xb090c0c19030305070206090d09180f0f0203060a12020a2d091a06120106031104031e0b0105191703040305060c030103051216391a0c0a1104 62
    0x1241c1081451040550680125001d010f00b502101c965031612440c0d2500d4410703a089030400034052080800500f82d40d0585007580d850780c03517000130701342010b40c06a80035200c0c4151814a125000000d0110b2400e0400c413181c0184120421070f5001051640090070012251140c0340d40c5000c0d502c8141070020700741701010b81c1c62041840c1109503503035171b040032130181c0300301c2c4480482c915030380c1164001402c02c41c00f1160688220002c400044c1c0c00c19000760000d0203c0041001d0b07000c81400301000113420711b00320081c03882c80c1958004aa920178076205840d070605800450080701d0340c1e6910303007400c4d079908804415030743d502240c1140c1c0c0c2c0c400000036255000d5030f41301a10b18030944080c041e072202240011410b0f2402078054036000c0301c20084c081028030903040c800b02002041101c40e008503c0da0300e000001d40741c0001c0801c070503241080d074400035003076158500707508a404603004002e9844000b01680c90340d00c240b504641403030261703100d094079000840c0001d04000d030701080c0c080c070503034803680320300c88 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 997535764 1250 997534514 997534543
    0x30f23070812090a0201030b1002031210030b0c030f0a020c2d01020423040b011d010201020f0d240f14120d051201050f09010b0a110d030903120b090c0c 67
    0x1024508800155a10985130006a02081c9004060402400c0ca04105406030a40e40c00561500007200c44030b0020542c0180544400e01c0d2420002c00001c4216054034090854a0511900c0b802d1030302c3c010481030303005009030718420320400000100740c0001c14488000c0300c00b0240c035500c0c031040781c0f9002a102d000704501c41c055480060081900c41a00d5210112841c1c130a1041583d072200505010860b200001c1443c0411136125606441d9061300525008280043c40054101803e61412043e0380c0c015001e806046912450a0804440c201400f000f0503009031500c0b0a666180080d0042003503024002d4900c6800180044856a1a41554007002c0f8020b0800ca41d10001240b0700182540c00980103040b2181404000245030b04e070114409502c484000d00d141820f900e803809140c5036030300141d0f0180502c60040c40da80a020400c0c000041c015031291404180c449845c5402021a00c01c0c120031800b4629000071003a10340c60b106281d60b84401d0400c0e509646804c02441c2903e0464495081c51 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 997537014 1250 997535764 997535797
    0x909040b0a380d08040b0c01140a0603050d02010c0f050903120a08061306030506060111210c0120041509030c031a0901021606051f03050a030f230708 66
    0x41070b0300c981400b01c0c0304201071100000b4072008500070018a014001d0020381031100c2400140001c0c54803d00900b90107410200004091541e01007002c5010320449900c090300380c0e0f41030700f0030038030000703000c200d454000e94130003049010801080a00101020024041001008180c040d503c0d2400c0100f00701241102504a890740b244c444001c02079002290514003c20424200c4c1503109803900548040e2036200000d411159507230001141e0384144400b00040c00d10a00e042240c40e52885070420060700040302002d607985c260347c003045c0d09480001100240c400200701107100c10041d158142d6040d0380b894061100344a01245048807140820f401c09000030044000010400c14021205180900c43c01c030600101c3c0c2c0d880c10190300300d004d00042c00e414002100d40300000210a5400503038003216524018019049506042304458a0b0380c00031141c55100b0155901410f410449004200c482032912090605881984064041800c41d060350b40340b1008ca0a801003015050903076038032000c10030f84034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 997538264 1250 997537014 997537061
    0x61d15041e0218010f06051204030f0909050f091603110906120f030c0c060304030c030c1e03020109110d030c170912030a03050c03150d1509050a170909040b0a 70
    0xd41485070a2282d8000c1003058200003900c6c60040d0151400110202800710050b079481e1401c2d214000000040c50811051100200341e081035481200d001e190480c1c429412071600881403890519604071301000d40403c410b00300b000a0b04540c0e00c0c141d526080e90412196216035000c510a0171040140d11103034024a1405500350310000080c0a685c0100c80865001003c0c141c2840f040384400d40d800350003c0c0441d005000821302515407117603d14800d02c0360b07a004c03280e6041030403400448400100c0040c2d4550001c8014495040241001400704a030031b9140c0711045d80e006001040310380c10062003d50708038400441c1000c02000e480c3c280d04060070800c91401c22100094681e4043c00701640420b20b0310b8042806401e00000342d13449a6000b08003200d154103540c003000403000200c00211031010807480b080e42d690005024405009108500400c081003403860302c07000101000c0061980d8800c00d014900c1a0b540d2a201c03603403c96082044039150351118218440a4503095a154a50a1044800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 997539514 1250 997538264 997538299
    0xc0a150b0607120f090605090d0f080307020c0405100602060f07020f01090809010f17060607020325030c06030507080f041109040308070e061306050c1009061d15041e02 74
    0x60244110666511450440c4e91030b0103643c0a40c640c014000050402e01485089041144a44004034008c14a00c0c00c0c0b41a2641c41103070742e5000b1200940160011344070050a41058000c09421034460205249070b40d05210300299680c500410410318448200c000c140300d98002e03c507800010750702000030310170f405450134500c81c40d51090003490300040811724644481d500c9040701034500d403150000860303551618070410680350800d1605030383c9070203040046501024041251040c480460591900941c0345d424103100c6540d169100a061605140810044135403000741c46034090507103c000305541c1c44904040e550070041c01245604076007c00300b400207050308950020702c0f600150741c5400085040c0401d1101034015032103001158818007a0501c40320f03001e00081e1011090003011288007011000040c0e0903502254030607900d240e030f1400000c04007450440c001402428940c024042400300044044866030024400780030074040c114908400022011403080c4030741c00500001110b01022503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 997540764 1250 997539514 997539533
    0x612060109360201050904020f0c07090b01020a2a03120e03060703200a050c03031302040b1e0f01030e0a030512070c05070303081003060921050c0a150b0607 69
    0x20b1194400b01c000c401148182c0340c0c41c0c5903a00016552020194810b038015251074220b5020503034000c0c2c09111850010501c1c01c06403110b0014000142407a5180801a00032201c94800250440d0413600620000ca000e003194014904003141034520b0a01b40c0c8801022008148e400003030480104050603d9501e501c01009650034404500b034401988420405800710740f2400c5401c0c0382e05400c00e0a51002010038005801c0d44045c5040040c6852010011242540e008450461103480300300000019424640b181c007480d0501990740c6c460310030000707030310280071410f5540d4148a05403100c90040e45901c40d400c0300c15110b11210446e40050380924018103030350013000d04003c80c2c103c298005800709210f04082100d054002000e4a005425604e04481494006000046e82540302000000190b15482107020385130142400100480384820046484c10810681c8030030007000303001440003102d001c9800804642d03c0540801036550384035000020300501100107900040c003007618000e2200204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 997542014 1250 997540764 997540781
    0xf0e0c0103061e090504050705030a050f010e0c01120b0a1e1a09061204060e120a030e060709120f14060105090a1a01080403110a1101020705010c050a03080612060109 73
    0x807030a00c0074a0710740d812080f102c00c0c5440030305903614404104000106070355000d02d40050069003075030200f81d07c40c00400e24100201c002103c1d00d9020000505040c0d0f0203210b244201c2056801415007200e4a000082c00d80281c8100b80402e20b41e00c10b03000c40c00350b03505040c160061075290080b244107014040c54600c8070506103d1510306070b00c00742402207803840b000115041100d0090200d03091030b042d08c04040724035200030300c211905640c0d42038610607a0b40402c00e801958003072501403036852400480080950b030309200740c8145513100009000c903191b040300480d4140c034240c4a41c0000040142050002c039208011302a08122107066400300c0c404c00803c4d003034182ca00580d28482a41c9421602c94115641d000c800310040b207404800c800250720585207950401e0003450a4030082000040315403c0030700c1c1d0b0b07000b2902095a161811190750b014030029008000909284c183c00055407900c81c0c484a03251001410040d10f5400580c8a03075a186c0010b0105c0940d5003140c1c601d40c1c41e007140400038000341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 997543264 1250 997542014 997542017
    0x6060806010905060c06150a0f082805060f1b030c070314030705220b0d050f0105030c09010b1e04060302040806060d0819050c011a100519050309010f0e0c01 69
    0x500b0110b010b04140c02200d81c0410303004001d0000340e41c1d250480d0b80300031182c0c4d441c2e0751080041c080000c84001c4034172200090a03451001d0105203036461081030620260811070b504640343c80f0f0038032010800c081002d65010410b000701c9031441d41c610f403441081c00148107000201450100c1840042d94040300508856882034403101c1c0118544100703041280001c442072400154204902101d40a411160740c0002c2100482015580c0c0c46401685103a044518a0280142d803202000484520108007500401d01a0058003a48070031001042580301e05001c2d40500c0c110000710003603540240000400c03405408243e25880700d032100d100030082d42c40b44c440c0d2001845503d0200f00d1628000300c403c600d0540c0018010b00d000b03e80000600e07a003982403036000a0000901000c41602020301403603010a010648801c51400c07003504104082c10402a0002049010b1041d03070a1401c0c0301003101d00c410303802c0c148203072213640d14580f00d40944105049440902d09140175185041c42c0003071101e2203a0b909 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 997544514 1250 997543264 997543277
    0x605181008060c0f0a0e102303090d081302100818032812022a0d200a080d0614010e0319020f031522020102060606031305010606080601 60
    0x4403482195101c10a40f00e48480810400000d000c48008600801d2441051300b0448240107803400000c01510965048102041e840d0401500030b01c244040d01c084800420200c034114108040d080740c1d20303030204c442c0e0424085000045001419103c2e8602002035000348500c4800c030311004000c220103c1991840c13040c109a2000c9401942c0c0402a6500c050b0550035050780301d1460042c0381c0c0000040060001404004403070b442201e01c540c0005c0070102d98079100018084100c00c04c981d1030000700c0320340e1305098003e036005500d184e900030342d170301c004500f00909010b801c400302000c0c5040401441c0000c02a12000900c2e44010003960800411100c09038000001e614001c80156428158011300c50750541045414564602d0341032583c1c1107240c00a000b017aa40d0002001003450460050070500560452400f0824036240025204942d6222500c10600880d016070020f50f0703a440107450705105100120014981c16114030f00000c003190810024400241c2e1540050a052030903a8918001140d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 997545764 1250 997544514 997544519
    0x2c0f13020a09060e090c0f090307060306080d0e061822061a0a080106030e0a0615050a1a0d020d1e0504050f070806060402031e07081905040201081906051810 69
    0x41300000b440783d02c060b1140e0b1040d030700c645a80360103070b024440640302d48001340100499034604221010203000340d9140001c4050408519a03d0280e0640000d0708000550701426041c2c2c440c20103554207501c0d11100c0c41008c04101c00041c00300780c8040d1454001c0100f081e0400000c00458020700101c0f903d4540941101100242c090740380e1140b003080c0f201040c4040010810a03110340e1100c124044110141c03000304481e6550401a1a41c4d0f9200300c0164005450038402860020080070040110f109940b4058445a10500540c01282d10484580f540414289a04041c1c0d40120481103205090350080b003062104040c0100380c25502940c40e84145da440b044c030010000380d110192215400149402c2c2d80d10804c0102030f40c0003e1401003000c2407400c004012102c09000a030044c2840c0d190039050b4540f01070004240d4030000d40c01c1006505144c10310004d40d03001240e4a8200d103040601002c0440c035007611034003820380e507400f150708000c040714103180010b402038400340035038000e03218001c2965 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 997547014 1250 997545764 997545767
    0x9030a110414010518060a0f030318060201090215090a090504060905011a030717190c080c0f0d0f0c08061302090a090c211707122c0f13020a0906 64
    0x1242401a15041001600c141700000400003402e6440380c0010174100d40180c03241010b42c6034103030aa00440c0400c0c0292000018000151402400781903144004c1144105070340018101140340d00c252403400c10300040400c1c850710fa900c107000c00382000303101c03c3c00070b42000c3ca0200000c2ca020841500c6551800306141d04130055524a0b000c000030040040c0001c0d81822024035200585044042c56480386400c50000500c41c05200514503029942180c1824070b002e40c61420a800710705014031450318401541c00b02e0780c5900203841750a40040750000921024580242c1421841e00001040d100760020049c4101001d0f0580845920075180392543c4e84452010100f82c0c1e919590080074001400e0003400040640c055956a80d0003038865907160610640f03810020382040700140885c070000090f9081485007201c02007070500780c20b26108a0101c0a08510f2060072141c2c1204090a09404a0b00710300e503075902112214148020145103403204201c0e4000000d6116444000110700510b00c00079903103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 997548264 1250 997547014 997547051
    0x20f0a03111309020d0b0402030f19060209031006030c2d050409211d10080a0f0f0f09020a0f120303090804080a0f1704050a0311010509030a1104 64
    0x803544041c81451031120032040286842c1d92200c020344003603881c107240002d81d60311840313012194010b180303020130f42c10300d801030508083c0350b8964061982c0c0101d004100c241000d00480e807507990024001078550400c40002820140119081705503282800404000d1081500d4440d0844075404000b003000146520409842031240f0681454038040510400250805030040f48401c0c6c4142e1140018141141e041d0002c00a03040d80f400000761f60164a101c482d24099031250b0410040720014140d030b0b44040300410584000b044610b000b5110500040c50101e60782061141260611b42880001c10b18080c50008059a4100f40e11920880c14009005840300c4041016100c030203502060b62031594a040e000f038128400e0480b5064800c010000c1d1040040c49a001150721030368000c926804c180c01d1405080000c40c5001c0564031081004000d19a02d9192410032030b40e10450741a00c90740d0003c01a110382c040d403004290140195100345041080041c400404e400301290b042180c0c81d05101d20380c006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 997549514 1250 997548264 997548269
    0x1005010c05030403060b0420070510020306100c05101119030b06070602030c0415020a0311010e1902060409052e0b0a0c05010615020a05010e1b010807020325020f0a 72
    0x10b82c104120a10219445070401134840001030b1011846c9000d07000348604926400504551055020880c074080142c103211411200182610550443c00c0c40c00010728001030311401c95050041c1e880c3c25a00300007042c802ca1980e101865020000e4107607505410003290b0050078a0b690303d0310002c0c1840e048601030320a44002c2800070300000c0c01d0209a0340c0d00c0d07009500240c00310401120501c8005103130355040c009041d500f00e06502420040d001c0b4600601203489802c8408056410f11101c0c900c0ba200015038240e40e01d10040000035850880d0001c601d05115a4104000840c24401004400c4180d0030079282c0c01c0f40c016080c007000c2c000c4001c02444c8290240500d160700d200402081811610a514211000b0b00810002600300e54a201548944101c0058100560030504182090040038840c1e54184040c5402500c11402901007280c142c6074032440081c1072040180210301494030810980d2035000741c440301c130b61408072000107028164285810403403081c800f5140c440c8280c14106d500008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 997550764 1250 997549514 997549523
    0x9190b06031e0702100906141305030f091c03020d0906080f0c090103020904140109060801150b1c060f05120309130e0109020a03060212010f0b0702210d03051005010c 73
    0x11040010180c140101c0b00505008210311403aa20101081054850103240300d100701000039400088209144040000810f04c1c4400c091024400021460200444044814203134810f560b8900d8100050050390381841840d280e01c0988607454201500082ca10b18a90601e03140c0f10009542c404044481c45012604021000d13850b00c0828001c60084d006022a80e0781410058104a000313004101110350700110080c4204041e00108400641d500c200c102a01d1103100901403076a8082105002e540c841c4a5028490300c000b0b070a424402c4248880c20741c1420b4070b0000c0c011942c1d0380c104611071150740d005d40c91060a40502c20300e1200c0c00041206c90701d410181c11041d08102076106030700180000e040c00c4609540300c810407001651107160f07900145204803030050300c40d110315580e440c18441c140c204803012050314405202c03020040c010740307400301d41c101c0c0d039014242c603015800d0001494100700410a0f10801c03903151a16609504a20b10400030414020a42035880b0011244140c8407040a070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 997552014 1250 997550764 997550791
    0x703061b090909020d02040e01200708040317040503100b030d09060c0308042901030515090618030d05180c01020106050a1a0f28020106051e040b09190b0603 69
    0x10b08180e000f8074001070006041d10a01442900401c058517500d070601c0848d84d42d1421382000d2003180c017507901951001c0c44512810080d11b0780d200d00b441e10607400040d01401002c80030031030151140007124041d00d405015141d100640301c2403c400380000b425558424010100000060762003080c988003295406d5441d18041640703620192610780c4042c2050301d440c0e59185801d410041c98801446d00d40c40f055aa543c2a50326506105080c003d200740400c2500c100b071000d1219a8500141e0190050b5a54101912210440803c6403441c071402c20564501800e0004000c4c1d11000004044c0e400082502600c685600d000012800ca40c6240512584841d040c0c505100342c5111440c00e0722042c410000c0d00e4680015158440c0b41c60304800c01265002c0034030035116480a440c40f03a5099000c00600081c40228200400545e00c212411007650070108610706403036450755150040780c60404081e00201060420007c4036501c01481e509002c5220705107007905a0900705031040368410007a600d29030b0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 997553264 1250 997552014 997552019
    0x8060607030f030e1903080a110306010f110a150e010506060d1802090c04030c0906080d0c0f020904060f060515070f142a0d030906050901050d020c0703061b09 70
    0x7942c002c940025410100360b80d4200c0414003000030020f43c011102c1084c941c582180b030314075000f820184000d026030f1000341050080c943c40101e00c01aa038007c0001d08011910b05000407044605689024000a16119520029042c018001d1200540d08001d410600940900801c11401e903082a80d00719008042000005003451050388213101c5001d1070390b04d082c01007105400243e0100f41c1660180307200c2000103002c10812a00c45001002480c180e20103000c074034681b5403000d840340070000d0400148000c42281c0010802c0e210299800349a0090811001d410b0500780076005111840d45a6140e82c5450000300d107928010704140101c81001140300e252041035a41c001000307042417401c4910181811008019003410710403910300542242e02c0e081407429050100d000c40303400ca4074170f50080c2c0200701106e002c00e50000c0c140c0305652160400a960b64400c0c40102d5442c40b1b0420303013074407c0d031003c1201101c4200108006040342c1c0218414841903d05218075412003007076445c013401062100404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 997554514 1250 997553264 997553267
    0xf03150718050a03060501090b0d03020705060d020705100b0102010e0a0506061e03121216080604050c090a0320012a1a090a02090106051c0b06040f081c0806060703 72
    0x1c0d6444a9000241c054150766a040440c0414025800890f00c40d500c3d0310040c840c1d48040c1c452540c441808484001d258005918081d40b1039110313009040c002c004c002100400300e15103804031050103520400310381c4243c6003007200e48000c001c0551001e0065003802113462210a00054070800780e034010026000f5906c5581c10411210602c020340f850300d140600a06240e0b48e03081c4002d05880c0f084551003503503405010030481810b0b00007071002402c042d4500740f8035007041e8002e1200c0e62000c42550009a107491f44410780d255802a00949940b100c0555404010410b04442041c4448c80b4050140c10a060300001503d00c01c1d2070701c465041e12a40754006841c108500000d10b1805409620182e600c41040c0c682004000802c0b40d600c10b203135218611752001c50602044150043c8041c3c80d105017058065011950031402582e8030007405034860a4503005a40c684046030001c21908410b00751031755440c200141c581c0e003a0803440e0f20b0400e00390244000c085c0074151152003880d000341400d2914516540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 997555764 1250 997554514 997554527
    0x611070b040b041202190b0d0608060f060108070e090c090405162109060908190309080910020c12010606111603200d1103010b04021201150212070804050f031507 71
    0x1811781e80000d045214444088030301c1c58040141c6441a50795944410050f0050150340407a8041003080c0e00078070030009080c030801800c2c2e8101200b4a030070081034603401030031548681c0c1d154040d81e00c0000c550621503481075a40c010721250754280d0f03040c40740755664040c616040c080909400c0c00b00e03010701c1d0408081c0c902400901d40101200000003403441d010f80300c440490302c01e902c1c1121800fd0001390392884100403d6080c6072000300785030502ca20516940d84030a40c2c0901480e0314050305030203140c500d100d402400403601ca070102a080050110b01c0b510800d020744220300c01c0c80d0110f0740300e40d07003e0000900400d401100d01c09403100c1902841c030b56981c003085e07001e43d201250781001c40c0020640e01c554405c404100200d000307615200f00c90b00040201401c54a0400000740700d00c1c1304116540004c1c03a83c00410b41140c1a180c000070060010312001e07401c00051240b0720128040014000c800c01802c04040c0c0b041c0c40007a40c1134154004c081090554800c194006100304070348813800510079500c01c56 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 997557014 1250 997555764 997555799
    0x3020f0907051201080304050a350a0614041103060103050c0108191b0e010207030b06090403051902071a0a05070605183304020a140f09010611070b040b04 68
    0x10b40b1034600010300c0c50058100b0070030380000d08160000a020041850002c0d0340078043d1104034042c0700b1004000c0c04840c02120b840955244e1403001e02103981c40d00c402401109503451700007000b0301c041840894040000da00407501160109490600d481f007074100011100c0c1601e6200d030042c10182103200040da070845c4010b00030100076000301d00030101c0344060300817141b900706000351b41101c0c445030352405054000e00740180c40c11580302d114100301007602ea2221580215094a13030310b0842d292414100c80d01c2c8103540c120513492040b400707640d403c40d42c005819001c6503800c043c11110307115080b980082d64800d40340380a0010780c043c00a040030507410b0740043d821400300544182c610400c0e4001d5400d20b1080070610041e402041c10074840c1031600c00180341c00c06000020340710310740303080d5000610150321800f81c1803903a00480d03141507558541e2042100e200c80c00404020141d07a6800c0020321490281d00c04e9007280c020701200042d40a4501c0568090341c40d00003400b0f00341820407081c2c20281c000c4a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 997558264 1250 997557014 997557017
    0x17070215090604121b0608090c04021c020412050d0504060503060f0d020310020c150c0a0f0309020a0b0c0c03010b0303161a010b041a070312050a20030604110403020f0907 75
    0x108400184c81c030071505040c03020b52191a0102005a02c1480c284c0031000e10f60003e428803641900300220080c010404034045030003101c0041e1144511299600b8140500381030f400811b00c0002e010952500c84441050315900c02c00480b615400480012a001c0c01584143c501040f001d0011400501d001d8010000300c01014248400c58034403500001c0c548400c503211001441c2e030001d29001107010500601803071941d410b41d14019820400b401c0c640030b10400451000b005000240f0a140340e10030b811411005170002c20724451a6151710100c2601d81c4021070b104c0d2075104011540c1407500303042c06a824810780080107581803241d102d220880380c000c3d01c0c0c421100e1915032000b6286106403400f00c0c6000e4003100000544480c20a141d40c43e502901d070601606184050220400090344000d0003032140c3c20782c42c00462141c80d54107018000d441c42c42010742d0344841d80c1c84900219102c0d00c02841c401c000031207062052100000d4411000d11a500029412a00c600705401d0f80e41450800303160003801c903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 997559514 1250 997558264 997558267
    0x10e0301090611180406030c03020103150b0a09050f0108070c0b070309080c010506011818020d020705010c0f08010506040b0d0c020307020a030605043c0c05040612170702150906 78
    0x2996024100c80d00308043c3c2100701d0380070900180c95180001003410503031040d1810000a41182c0760b803001d01c003036444024101a140d190354102c80044103042d030003c0c11000440c584450300e01a020306410002d00805000740c1c0c2800038800c1e190300c01c509080c09806d9940f690f011040c1d403a112024254001814601803640307550388503000421000041c0b19844000e4000030707090400310001416482c4a80031011100c0d00080d05102c81c02c80da8100c8044071154000041c0d46141c1c01d01040302038095440060141e51800d500c00d04860380204c44004010410754031358006070b80b19001c11440d400b0304e004040800000f8003003a440011640d002c0303031048070140122403d200c55580010f21604c0e0342d4108840e045e841340f060004100001125990200700300f86500c1c0d440002c060600300300400c0c00700c4041501030b00f4040c0070500440b20f1130038010742405403040c8a00d0351140b07082c1c0524513021071b0440d454040c40b014032104003103900a840c0002c1d401800e40f00304600b0a202c0d00015000a800954807110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 997560764 1250 997559514 997559531
    0x50705131a10090b130314010501030812040302162d0f140f040234020d030e012c091f03032a201822200a091a010e0301 53
    0x940001404c17190040b0307041303943c0541c20341c0703000f008010745498018000d030f0520700103000040881c02901e0902001c0b03600300c1001e9565003002c17481c01455a47c140c031810704091001c10081b400cc0175055503d59404c0c1d80b50484ca450003e030441c1009584212080c20700c0700c0303600340000000580031403080301e401020702003140700c100c00242c00c0b64040404400188080c0120024000450310410b4210301a4400c115511a864011500c070790f050201c001c0801c01c806103441d19907802043d030384558407002807110f0540000340300a907035a8188225118851068440003400c035010310070321400400a08041085000d255690580712814280c1200c43d800c140f40d2201c1d1494030fa0705160852060150755440415a98030a6400612103040b00182c0960385c2c100307035086101c651102d02c0303401c014090000c5d18011030750070303081485d0685160004c07d0342030100314450002a40d0699a83d03a00310440e40190069603411400044a494141c60203045110b80840403040d8007409148a640310041c0000c9011070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 997562014 1250 997560764 997560779
    0xd2d092a0303090801090803150607150c02070e0412030203070908030708041a1201062006040507050a0b03090d0813020d20060703080f070c0b04050705131a1009 71
    0x410384a00e0880410060800c10078143d00080340001451124000c015080983c0c64403c0c1d240301c000c1c0580c4401d00314200c2c04095440748400c5500480e041608410504102090302010700100140310300188206000809e41c502460410b5000760362025121090810604080d8042e400040114090003400403000070400b000f03000501d03040f4070960303006540e5410001c441041e54054046406005814400c600400300f44150050550b0309608200440c403d103a200356544042c0114208107502480c0180020840009141d505030345003140e04201da5030711a081c0a5090001301c3e07445440b46d001405010801d4090b4450540256844000340185d081980114171810002c01040710758440d000c1206090341c4080700384001c40c1008482441c50054141c500408482000d810440c169800b880464521401502c040d040594043c441c00401d1425040c9162914034074400e032802516052150041840c0906c42d414545001a01443ca040094420301400e06074191098041c0904940040380c0340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 997563264 1250 997562014 997562063
    0x30b01031518080706090606050d060b040b0d0203070e061c031d0f0a06030b0d120f0809070302010f0c03030e030f090f0409030804170d0c03020d2d09 66
    0x86018004900200308000c141c0d004a81000c180d00c030011040e41420400510b40d5001c0f03a1103e5001707980070900320303a00c0c205640104559440380d07610000c50b051075030411039660040d51040c1c0c021203040111014500903c80c0c03944414500030b40c1178000384014040e05103040e40c45608404040c10034500300014400c132411041c1010801e44c08600001c0c003001d04810500d02d2800034203010344042d00c030f010003013000c10600303003c40c014031090644550300305011340c8074500c2d086030345034001d181e401840c00c0d1200058204854103e00d800005c202400107100010001012000c03a90b06a4600800500f01901202c810701e6115003202007503154102491480700410250034201d80000100d03a8a1000908001d01c080c1c12030004c0b4000c3d82040000ea020980103056160320680245100000c0b04aa401f440d409200300d400f5030070f0b0946016007031401c99625601070103180145402c20084692684125078220681c290081c076643c5094500801010064106045541c8100103107a000c5480c14000800c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 997564514 1250 997563264 997563269
    0x6090402060915042102100f020d0f0c050d05031006030e0a02060a0c0501050906011502060405060718080f070306050c0c06150303120c070c170303010603090f06051e060f06030a15030b01 82
    0x3d45141ca03681c17015407924102c0040a02e16a08200104014100020707403600c00c10411501804000d20070030b200703103014400841011f81d12005442d0111112203020300203820542c3c42c0100f0b40c50206c00410818028880c0c2520808003000401c8642615400c102d8141c1c821a0301400300034540c11000c00052090080d00c0c060203907000944000c0d81031152812800803051319040c1198820b0040c0b002003540030803ca90821514945601c80c80d02c6406403202c41d0075564848040341c400c01c041d8107150080410000300341e91080d031040c000c07511900c4408000e0b0080800744005074001c0800709141c1200214481030000e0041d0075282002120901301c2160f60003100e256401d02da001400034100004c04100001521621318110111186048402c1d07484c0814004e1105069840d208181440b11030f2a07030001c1158000810322192910041003400e05c0200c0368458001203524000c140c0303900c0c0c81c483c40001c0d00800f401d00341c00c6031381d2442040040d000a28800c18030422505001c80840c0c10320186501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 997565764 1250 997564514 997564559
    0x100c0504030f050c09070e060d050903090907030b010e150d0519060602010617010603120e1908010b181323030309030a0906030603020906010f120f090203060609040206091504 77
    0x444c07902c41c40601603100d07001040203003003107500344d03142039140c2ea60f0081d14610791030750400041b00d40d2003251040c0742d4491081100d511144183c101b1070883e6164100c000021000c4ea11109401c080906020412586840380e00e20002e00340405401400b40fa400194800c0031112030300c2e0310036102007032a02210510741080005035100c5101b400305111034103d03c004070354080020040c0724607641303d01c096100d010100d181009440800002c0c5955854030380d00400580d040505082c45c3c0d02c4240314020030041c030205024038424003040c405080c0311801c840c801c1d000000c1c2003980c56600d03546c0f0380013003614000c0c81c1480740c1d940300c2c0442c0485040018501c01d980c036000559075030400000290480480f584a03601f09030500c1c60600c01603d0340401a600800c00782080b54941c1e01150040c4c4070000c0102540046a19204601040310400c1c0c010340c1d082c074001d0f000e8801a49070102400780c0d05200722406500824204800549030404d0302907886802040c42085040c10344542a1074811070002142c0103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 997567014 1250 997565764 997565773
    0xc050a0528090f140f090a03050708121003030e011806050a0203070503070813140609060a12050403050a09080f06060d030c05010606080a0f1812140d020301030b070908100c0504030f05 81
    0x84e4034032030a03800c00380c0110025140d201e4a1401a01c0903a45560303402000f01000000305500c41041400d01c256000540140c4260801d440c040c1d010885410591106800150520f2000b04055000c0d0900c20001ca6a00940b410030509004080d18550f211907201801c40c80200300f08008240180040d0249501c1841c4081ea103024651100c01004899004403101c0020001c070003080da41c0c6c290440d1014881030714042d46820b0001400e540e8406900c1c0342000c0142000d0400080580c0b100c010b041c86456030b19104031658650f40115560900c0100c03100113680000e010030514900f11000049541c403030315014159411603901c4c6400d4034402d6200368003040d03000d002d12900e450180150440715103805401c02800031100008042002010405040f00c9040d20195555a10034915103101580f00060180e40d105680d0089000b94070910058078115500b2000c1051284600ca0302411504c2640040042c1c407000700d94400189009080d8000f070080410000000030556881600b80a000c0d00c041c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 997568264 1250 997567014 997567031
    0x8070c0203250b0406020c09061518030d0e0f060d0213080d0e120316170c1b030d050703030f2c070e01230d05030c06040c050a0528090f 60
    0x190190440c3e00420041807091000780f0440781e0000c0c0d12400240121a440c400e901c8400100c1c40c0021008044500c0100010710304204010007240c28030310110540403981400525174003151600300340c02c00703558882d0510300951618508140078020a072041c001c01458908805130b9000f401c3c040c2d0b449452142c1184007203441054000d1702e4802d0304401030341e04a0318a040310952380d85903c40d14158070b4450b51911031000601c07040d400030380707200e00c800c0d0a0107565051400129546072680110815400c0000b204030f1010b09021403032400c881300e2511001c1c2815601d6405030042d1400701e145204155542c41000131103406c41c030003441045c0040c16142c2070344602020f06400c000d8550413040300d48800c80010410030045000700d64806101240b040110341511000440e208407000d03001d856480007190024a00300c0200d101740c0101d112351004100342c0e9545040c04040c903e02e1280c6e84d8007051000b1800e480c2c2030a03580c09a202c0c001c844400034142e890307241500c12600d500e8600b891042e52440030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 997569514 1250 997568264 997568323
    0xf0402250b0705030106050904050915010b1e0c15040503161a100b0405060a020327130501081005061f02034515031509010608130308070c0203 63
    0x7050300240700d46011807466050060260003840307040561806103542e8000a482108103000c2480216004032501c5019690b869030801e8540002c400c03070f241403024207030046403031251004a0344500380f0100075000925944442c030f01d00351b03001030003541e690104118508249a20300d00c4024458800e1504110f503010745240800005001011822040000034090241c242c42034155421210202c0b0b51641e5121010710803400c50040f0080f203d05216002d00c1c0c5188400030506c4840018000d590900c1e00c411042d54081c140c64080c4070341c14503900038540d031b6403002d03005400c91640560054842000355a07140c1b00744e81101c2d00c0e04001c8c0010b800100b101101a10044006404424030420196113800e441ca80d00d0704507610710a01c10090506072906a01da61100e100928a052110195980380c0c5001c200b40360b5261603816010344034600b030000104d1054003035683d45024201008140400a103d6175042c0c2e040080903040b50240175900c0241d00050303404210480c0e0f00c04000300c21600300c4008145 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 997570764 1250 997569514 997569533
    0x30709090c030b0a140f0402090c0c1e03041d0f0406110c0303070e0306060117061021020a030f092f06071109010b121932060415050f040225 62
    0x2e8010504040c409100243e5548082207400c4550ba0b0161aa2825502145450501c03245260541004888cc8401d0391110100207001200c140d0b407421007800d6018aa8041e120000b01c824000d004100310102d00450f0b5182e0215440c5007500c8061032070032404100061464008403240030010750882e85000c42e6003810f00059810a80a00b40642aa0101581e61000100c014080e07801090b920089001c001d11400740c3c544180c01c45091074a610003d03440b000041d60040031450082030802600d150070b00303241d00c602a05c0e26040082c000c45058400404111580c440c882d2000d0b0a4142200d0406652104002c003042482441c220703a0f80460801070040c1040305a008048030304081c0321001071982c1198003540d105c85601d40451050038881c0d1618014820081c402d0f10404600d1900781c0d00240c40300100c0e031350071090703521182550759903000c002c10b4513244000300300192103100d0108994284074913500030802c0000c10140c200300d031025a4400a4142103c03450321310841d1008102440007900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 997572014 1250 997570764 997570771
    0x90604180e060903070f050a06050103050a0b011d010312111b13050106050f03070207030b040b01141e1014030f040227011a0c0706120c02010b030709090c030b0a14 72
    0x1d014140c50310782590116228041d0540103044040700b5590503040290901c10b481119034081b10400142d6100d0500a944480d040c200b240c1d01002600042120a2a4408010301c029001444503d40e03007156101501240d035420517106020708403040d003d01800c1444100340c0d003000b40c007900c91400308600400c07480d503c4101c2070105c2c2c0d07450200180002c9034441c00b120020340c400e448083c2d0317030385404808902e01507281d40094409031003c070501007044002e0603d00c1c129441c0b0580c2c54148484201001504030074000020025003050449407040c2c00c0c40021807121001c07e00300001c0040d4034014408160b403044030703090030034040d0a0800013141781c0808420724000014880301341c1d0b048480e46d40761012070107018482d1640c0d0601e010403400701041080700c00400d00e0001f942c1c0340e180e4a400c0074007010a40005070300084c1c14141711019142c41449241d100d144018020903940d450410101c2c01414201001d407010075030001d0100100d94040852030142d6414400010301448140e40e1070321080025 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 997573264 1250 997572014 997572041
    0x5190b040b0604030212100204060c1110020a1217150103110f03011208040302060a0c0506070c2a17060906100806040b06060d06060e09010e010815070509060418 71
    0x9400400c10740b42ca1050740c2c140d03941941d80807074905554540928181c44004000805800003402141d030070ba01450340c000342480b45080c41c0b10700e41c40c3c0007000035040581c1e51610060f40240c2409010842404250340c04903002e003860034400180002c0b058102c0d50440d22000d09181c0000341c80740c01d5078036100720301e011150101458201920b201c0307072042d14030062150161503c0303505082c500b0300c881001210f004540c0240029551421454041c00310b1401100039900c9008200000b450540500349a240359a070054142100e20048800c0406028102c4140054001c0c00300012641c0b044804980640e940540000c00780c51a00044940c58010024075003102d0703600505003000640b40025119030042e03480401d41c605a03503000f001c50084d014240c1082c00540c100107000500b0754010100091250b802ea8885070b050380c0300c81d80751311007200a01c1a9800755010302d000c504000c4000250a80114483c5040d07894208800d0000d4480d40181e000b40e000d840c1c1c0401d074486031990034812024550f110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 997574514 1250 997573264 997573271
    0x1503150509071a040b0319050f060f01080a1b0c050708070b0706050a151412010e030a1b05100509010f0b0a0b090a09020a200a0b010b090d050105190b04 67
    0x4070420b44030000e0303110b200c03d042e103108190610402d1050640d0041d14281c0d1445880c0e190240904110301d28906d0491b9045141c05d020400f00f040203011548104400b800c05421720759070303100441354141d004010500c9a580e854544030500728007440700340c40744142c0d41e0320040c1044c2400c0c25402c14049902c03154550744008070412504148405465489070401800102ca0f0741d00104030010308540c030045030705007252000200b00d03030100304005290348905507002e0891070a4006002d080b550310481904080e4824040700c0a51441090404000d100d15000b0b015201040d0307540c0ca140040c43c4d880c41031401d80780c1d42002000302d024828140e240c4030144040c4548080d60000c22680426070058442e03600001643d2041034031801164801826900011075481c0c101c0b05000f030249403050106100c0c00144114202c40d2030f0002410680710b50014900c2c2c499900e0811500340c1d47d0b00c1010281c0c1c0288056140c0408200284070355840703103088500d040c500b070070141c5000c1700300c4460780162403040d8503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 997575764 1250 997574514 997574521
    0x20327010206010608040809030d02032d120907091406090721050a11040e012c060d150e0c030606040c0818070b04150e0a0e0403030b01050c0115031505 67
    0x74005032040c119009400c050200741c94501b40410140b0034a4546034042c0304611705002d4055001004095205900c0701c840300002541c00401c004ea140301110403004002440740301c50850700d508031b01c3d07044040704085035600307941c0f80c8145060324031241485400c0200d10081180c941000c01a050f0700103d5407510740740ba000996180a202c0b100080720385881540c1e44009001449243d2040038a07050080015490355170b03031110b141d101c02007401000018281140b0703001554003c0500703000443c1e548080b20109036548005c0c080d035113a40c00d4017a110080c02c0000440303000c0f12845150483c11080014100c1d204007102890700e40000505540d00461805c803000200c290b01600c2c01d034005030061164070038154414202444c21000750004103000c1800079001a8085d03201c000b507600040551101504000c4d21400c01005607083c2c856041c1c000400000240000c0c4641d110030304407001418114200030b09508110f084800034070308090071083c010024001d000d400801031851101581d4288071616 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 997577014 1250 997575764 997575767
    0xc030c0f180c020124141c030507080f04081b011b03030911040510210b06060706090b190f0e0a02061b1c0f0906140715050702032701 59
    0xa01ca4585807516070340d140803a0010610039040030a0342904032081000301c0600e080712010301446807241c1e80304034611110303004d11801c240502d02d01c0d090444c0707058142c40350345440a490650094004441218040140030048014040a0006019264020b0490701403400c0c0c001c030803904c2c141459041c0100400440d003061082070039200790f00e03030614002c00c40380d000780303000a40d1400d2180070942c1b1a080c2401c01103d082c0c159000d10488803d040461388160b0b941143c980003007203d00c0007030010301811000500504041000700f102521483d800180504141c80b1b080e111041541c0f0301c8040c986c07c031250304041340d150044130010403064004100001d01203007126500d10301908028090100400c50080c1d020010350b8050f91602d01c581960035100d0504a01581c2030201400d40e00400c2c0c000b54282c2000348100c03000300584410b901c3c2c20321203160b20b51070100756400c00d92080b28070502c00200e81c003108045000e0307a80120016001551515419080461658406104d9400007600d0001c0c0c141e1300c1c2e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 997578264 1250 997577014 997577039
    0x60e041a0402091201050f09060c1c0b011101151509050609010c05160324020310090b0607020d050604140a0b0f0a021204030e0108010915170c0a030c030c0f 69
    0x1031049400507654405500031910860710420495120752130403080085952200000600c160000000d0301d0140d40c0740c9a1081c1c00307001e04074400840d040d0341404036403c82c5055002100234041410655540ca50340000d050035201e0701c6115086200608104120360003240300900620b031401e00780740c418503040030080380c40c50044600445c100312240301c80307c0c1846403e000581035480801440390210b6203d0401980c0c2080280107403a00d19140c40320800f82078034510a5a01812010000324003030b91030014400050002c0111159221000b0022200103079070700600d10700748603c40c001502651505041001403114059500c000d9a04404900b00014500c00b110300d03030044201412040307030344603241450b00038014032080b6850b08485506101c01c0c141c1105000c200c1c00400d98074800c184e0303220b140c00816100c244c498402110201c1c3c3d07052003c0381352a03050010540034501103441c0c2c040260001014155960700541c0c4000240e002130003404094900c000c081c06200b155002010300c1c04860f07401c031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 997579514 1250 997578264 997578311
    0x507080c010318021912050309030706050f030402040905030408150117160b0d06171b01052104060912091401023f0315030c0406050607031103090a030804060e04 71
    0x1200309200343d2140e900701c1c1152101404400810205880f0346d846c1180d52a44540f9100b8440e2041c0d80c00029102c0c400c50803184050b00204545080d903c5035400c5c0000f070002c0f50421070f2b43e40014403011980e41010000c1010140780c800c0d44040755454400c80a01040c00e0040100c01d68124405641345100c15075481402c131590449043c0e9111260b032a0341c0018070f40b41c0c002048214032000125000000050000e18a27813640d5603031342486101600651712032203000540d000020b2804c4245a084004421841d4480e0182c43d010a000046503200314240c0440707803085000c100311310010300443c49411b942c000340040c280001c080c0035541c2c007040e0071000303454480034550310303011075041c80e95500f50304103a4041400220b00726203d00340300c000302e04111070708400b80740603106450b20811549840e0096104540015010500e80511510b040710b49400f00b41991810788420041d5686944504140000550007020529151424058010580b8204400042c8164100103015001c550003a46103481e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 997580764 1250 997579514 997579519
    0xd0e2407030b041107021903150c0201090209071710030b2403010c030b04110304111018060f031d10020d1808030907052403100308070507080c01031802 67
    0x106540c4000c021005845810303501a00316007058508103c000e10440680b54040c4222100ba141e00f122415404106000d03110140950540c9000502e030407840340e214140c1001144000700d011b0317609802262520340e09a4400c40000da0404601c1071488100c0c640071f4211038655450246649581c0b120b1144420142540c00f80f4503940d81140b5101000703148500286c5406402480f000c0c80b204405030007070402a11031030180e800e0034100c41100c85c065003124132459010400000110f101024406c1c0c2e602c0c021040703001c1c424014118401c00c2012501d860040c001c503902c3c04500e10010340000c058500850705040e140000c0d00c00d85085420209141200c003120704070040e05d6060014508028142c00c0c0280c04d0420352542c2281d00340148400114411000d500498640320340d1041484040000b158031108210260440c030a555004840256007060042101111958807925105038a9101074803c039415072107084200f1180400b8454002c01a000b400c040040740035821031443c0e4881094002403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 997582014 1250 997580764 997580833
    0x140a0b06010315170606040b010504050a090c0c0506010b07051209090f07050417010e15010e01090203100f08030712020601060f20070609030605060319081803120d0e 73
    0x582c2101065680d02c0213200c1003609103040f00940c500300f034581100f514440c0c010303814100c0304500c3e54002c00849017112400f43c0741f1a59285000301314001029424550341c100903100160b080071400420100c0e0180c046003403d0380ea50051803400a1904210140e01218074105200e02252a41c440c00001da00030080e400c0b107941603540250413680f621990f0010644035103180f01034401c1410550119456959550441d030020b60410094844c031002440784c4069a0080c030014002c51035a40c001c2c0d50402100402e0b07010607602c2d0340c0c00341082c80c02c1741c1250700300c3e604c085805001d20082600492020951340040c0005504001d401401c0d04148140001400440d0036000310701c01103265545503203c111801c3d5003855071981c0009000e00c0b070350302c0709442160500e00410400e1034041016118000f188a802a1141c2c0990f0ba040c001c0c0c0110040c0c1a00238595991000c4640f424400c0d5240b50100318901d5a8803007074152010100c900800341080c00d644241840904802803090442c000c604c0d410420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 997583264 1250 997582014 997582031
    0x30a02150433030e10470d03110709140609091c09120804080f03031312020c090411030127060b1f1d040203090d081b03090a140a0b060103 61
    0xc2c0ca40341310040050105d0b49040028160795020034203e0404003203803802081400d0201040344226600021a480400280c40d0210300c81d2410070b92200196102e810005c66084941280c2c80c14104241d00411515886c1c00b5012255140c0c070491581c800d008894888203801c2407008a591510030140c910082901c1d4080c0407071603030080208a00800d403401208004030203500d064070642e0813500c10200c141c424100015941003020081d203110f4a20001da604076481d058941030548010146480c2c01d600420300f11421548441d81c085101324050611030310100a0f000c24182110700f00380c50401141d400001009121a0324401d100310250002004100c08209100048038801c004840302d1440300d1101f44203940079042a04c1112280859050612002001e82131000303900c4100c800c2070b42070708294070201890740034a844980044906c4030340b01880500500b64401c65200b40c90b440c0e0503034401c004400c108010521080a40da0445000d400075020558503c001410040c100724181611140b41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 997584514 1250 997583264 997583291
    0x209040204180209043801090b16050d051606020903031303060509010b041107030305090118060e0c1012050919060c17060a14030a0215043303 63
    0x1920098450001095051803030301d0b04400c001c1d8814a00e2502881c01d061041a180044800c0314100c00000989132180f042150301c0e20703080841c1005694180101c00c20049640b940c0301c0040d014000504540030120075a0b4245285064000c4111104005081100000d201441400101041d620900150312000c10800090a40c050a561040c5240d030082c2c0010034810f0a400240c00750031140004c20030008440f042c1300c10740d507100300c40c26088032003000b20b440083c0c480d91081e07074445091800020070f5900003407002c0c094451b14805540c0ea43e00c0781c0903441131940500c40803a420ba0101c034140306518403600007900c096040480b5510f0035540e1400200a4603080c85400b000850026084400703819500d4200c0c0144a4407940900080b00c8080200c200c001004440d4003074000101100380903880c041624071009829070015800d801000f80b105c0050320350709007000074400590a116100e60070940880c201420a14fe1460000416803500c520782414658580d03c118461901044d0800920407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 997585764 1250 997584514 997584517
    0x11101020f0d091a070221040b030402210f03040515030f01031b080303241203181f05032a0a05030a021b0c030705121b01180e22110402090402 63
    0x44c00350001845000700414a9408180d8540c1100e079502c035204150100e8480207001e026a0080a040340c1080022030054500b6820500c0e1500b0010803501c00450094551410850a032103d062a40d1000c10b041c0800d190a141c8081176980030410303982149850581d81c011f80300180300180c200c1d440c01c4d6401c0c00003242900310501400b18181101d40e641007552450182a100c04104460201d01c1c855411242c0340441a20b0025203c0d07500460524002100c004038000400014641c0113108200304503112011826107840840e25032942c90322454506800a40c04086117001b85030106100b501460130120541a030f00da090707040c41c01c0c1c2e0312a520faa45420081c0302e03547e102080800440f180c0d0100301c10001300c48150140a0b010360b642d1035a542d09104141000340502304003038010340c440c100c0400d00ca08044c1c3c01d000051500c112264021120a01040c14540000b030314291046c080003c8054616807550340400450401594462641ca5074a070b08070114000358810354000542110b01e50780c0b40c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 997587014 1250 997585764 997585793
    0x21c03020c070b0306131a0f03030705060114030a150207050c19062001020d09061b0507020609180a1b0c1212060807120515010806010b0d09080414011101020f0d09 72
    0xb01040358049090035080c065802100707444c42510108c1503046542000f00540c1d038410b90142c002c294607401c052410100100916a054141c4110b03803089001c6041b08040101c5001e003032000590360754032400c12034108520082d00318001d0f18041c00729108078014001101c2106e0403454400c01003220104400202011081c0e403c00b1036001082d04104124030340e102c0c0f00b820f48682c03003c001c40905050b9550070340145031b1100020a405004200240c2080801014040d0004000a140380d400c907024400c0d1080c190341e5014036a80c0c8480c0e01c0703030600106140d10421441810208484101c6070380d8100c0d41919600b10303d0801c01602c010034016011500910050005403065900320b1b515248062150703111648103981d10310072142d076010541200b0b0000340c1610880d0000c0c1040d40e09000c0350600c2c5d40c3c0400801d0001e00d0390380b10103101140d840703805003015003025070328003a0854852000500e4201d00302c8880f04144d20402115840c040184100c0d00000c80404001c100a00307a400c1c01c1c031a601a08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 997588264 1250 997587014 997587049
    0xc0206151f1106090c010c020f030a080a0804110409080702040e010e030a0c03090b041a071104060312020f0d0906032a0509130905211603021c03020c070b0306 70
    0x34040004242e4010240d1019030151404603035803556401d40c0103581714402600c1c41e0100b02125000700142c240381d04140580c00000d0202c41082c0b03100c0d6035030101940003110f0700000039008410321040140742040c0364a0b01c03d0454042c4509442030301c03400100c0c4038120001384039560700e0171100500701e8207410000c1400c81032010340341c585a0068010b011411116021030010f2007443c00418000c070680c086e10300b5101052118190002544180c1200741e0101c241076502d40800c04450019a495004400256126100c3c41d0485880315001030b00d40415038606503003a4103c1c80e40b544080382d1105401040303a105140105000610812041c0310380c01d07140300007450450000c282e8000700d0300700b8000c03c0d03103c80c10740d003450070340903424401422500e045030000c100350006d01c0703220800341d44000c825003410800000e151900482e0003070201044000803085000d40c001440c0ca4011044094941e0103c0748103080a500d000b50411440740c40300701d1409003200c0d100380032010805d241c5805001244c0c20580d0f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 997589514 1250 997588264 997588309
    0x9020904240510050103020f041e090c0c11040b061e030708010812030c130503150f011418090309061b210a08040302121c06090c020615 60
    0x24100210241d00c11100300c041c1500091a600c1c0071859440b0301e03803240b0401c1c04602c140320709010044000e540203c0c1d90214115007404042801d404482034a982541c20f0419006520b2420401d00c003541d90001c15082400101d84424002c9000410340c2040807400311030018890640000041d01070003400603907000d0000350342b48041c24206640066005900b00e13190008641e907544c80203a6600803800c0c0d02c0c2559502840451541c1c40108090b118030320400b0840c403d090386070310100307181c0b81042c0d48038102c504440d0140015403d4008000d40580806990440e4800161011454184110801c2030178146c102000958079001070041da41d160000924255907042012407032501100d0445421185015241c400040500141041d04070304c9036800445041a80349403050301d681038014829029806242840791940062000600c1211004035401d40b4803a4885240c038210f035a590000c8050902d4030737100d224082e8002070140e61019401c054600960943d0700030980c0f00f0b040003602d030304d50100b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 997590764 1250 997589514 997589521
    0xc050c010f0b03100204060c08070203070b0c010207030305061c081e1210050405063f070929100c0c0e07030f09021e030f070b03180a0b0a0f090209 65
    0x121500a0b0784072a408504442c90009107401c80002c038400d42c42020046a022823900001070341040280c41551700060a42d0f0765a9035498080c1169070141140d000303565030025000c4105a0180310307081d008402501d8400cac011a010700da4620988402030050300301440403070101c001c1180340d00c0034003924a00b95003154a4001c0b9940c9110700120548281041c0080240302103031900345449110300c2079600400c01115605048410001c2102180500c02c6900c480340b800400b0a001c5250000d08540c6200142146850010301404a410300160100c498010000c56000b550800103505058074085a0054a44140c000191200b203a503090080011220003400111040c481c0000d621490329901c0138450002281881c02c01c44542c190300a40c4180c424140303501d01044c0c2d114159880b140942115400d40b900d51f5401d01e05901035004c844110400000c104450300c00c081c180c0c842131071400c0281582d003daaa52000404070060903d680a5903850f0241c15500c00c0750042c0104540140c0500218103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 997592014 1250 997590764 997590791
    0x7020a320d03060503120f0f0f1b0f0c0d0506340e0a05010806030d030515040f0e0c0105071208061807020c1507080313031e020606041415040c050c01 66
    0x30b0f40c403a00f44240074803001200c0000c4400c046420b0b640f4411083c51810522940142c0701d50000c2c071190030703101c5050104500b901005d800d08540f00d07400c54024004545c200d01441d2400c031085e9040c130f000c0c0310f0440380d410004000140380c030b8010340d2040d100c2146200c034908240150540c0d03500186c414080250301c3d21142d80150710340c0009181599100020354030349005550000b03056405a4241d40900751980c0320510950045030080038070040e42090b08015000642036801d0490070714585a524103508107040341c20801604070003402c4c01d000c4c0c2400070304d454020b403000811001105200c82240081d1681d0380f803414003180300c000400e00c00314034100b2140080d6940c00110b401d80c040e2100c03200c0403800803035127400c0d2502030b54022032591440d590740b030314070420316030602d412800e0060000104450948003011381c9a41c41403580241000c4c0b52840800043d1140f07441c02001307240300345042c0a060b10400341085190b41041d100030a003000c152034212081e128000440c2e5095280240312120300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 997593264 1250 997592014 997592021
    0xd0c02060c0111210a090f060911120102032e0905040503120106020c030607050c0307080f0408030c0d0e090103020918120301090603150507050403140a021c060507020a320d03 77
    0x141102e204c0c49042d13440c103041404440d2117070009407200d01452110000a8426040007803400c0c8512604d010740b01039680401e031811088000c0525907500801001455249032000003071409000501080d2039050f81c0100b402c0f42e041c0e00840d5503098403240040e0a000701041110b142500c9980030160f41d40e55182e0003911401c03014031052180c0200c6012a071038a10900aa43c1101d102078091403402489503515011071748460746400c50b900d404d00c40002c080b10184050100402c10030041d00c25001c80190081c41c1c1c54466210900c90041000140090703100c910381e0a40c0003a02c17604090f4040561034046291071603040410341521000000824010403d0300007004030f900c12000780c202044030005080941d0803c80740380000617003d01007040403440c4800f0720483d0741c184100b691100c96458022904100c42066034034148100900020b082028a10a242c0e11523114409409040040d40d00e000403601001c0480300c0c0864450440300e0340c0c0c0921400000d1264041c2e040b92440050083e025007c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 997594514 1250 997593264 997593307
    0x120c020d0b010306050f0106090b0919090b1503040b070302070f0b07030c02070f141c05070306060e01080d090b030606041724010f0b07060609050403200d0c02060c0111 74
    0x810f0a11000c141d00c03011800e06d20b41a10711644403d05810f04021450321541c1000414aa12504c0007210320001d80e0310b51208800f90505c800041504441d80b000d01400c0c0c000c1d400303440940c4808100708008205003082c2c06070884014500541c0c0c1c3d188a09080c0520012140d018201c036a18006003c0d109030560300c1107544034200c2d000e07030307001e29910f81407800c04883c40d218528165500f0710700c0c19141e15028400051b001d45c0c00240400100080c0c80b52854a00c883e001155a03a0b501c40060100380c1501c540c1078018038001c0024000e10b444640c005007004618881c0410700940417010580998600c010b94000e03040c181d04490794000c41c1540740e59142d0204008500717185400458040326036000c00d900707061b04c00c024058490589044000c0c002d179800b200c01134030391643d240d1707000c01c0d84480f07406801d02031800784d0340c0d082c0c50f07484c01101801e900d17540650084960784003900881c1c0d0301d600312190b2948107404070381003610b850070922a98090010504003145810000030482d00241400403100340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 997595764 1250 997594514 997594523
    0xf0603050106140616210e011e050d0b0a170a170c19030c0c0b03090c01030c0e04020904020415050c06072a03020c100c020411090d120c020d0b0103 65
    0xb09030745105911202c10741c103071902d410071010080d104240302e040c0540c0480b1442848036502c0f000500c03207040240d408604403200040c9505035002429a07124078118465041d074502c107221075120840151091042140050850b6201c004a940660300e84101e00b00600b440c4d80c4040240400e0800d4a44807281c0786c804480c0411803d0146448031300d100150341580d44650010101c8002d070300348440c0702180d162011010072000b0b0240d040050304802152006042080715103442e41000800c1034140702a11a515040514001c203100c10a544020b0070f0000707040907900140d0790b144040104d000381c481c41e0802e81100d501c000050707046d258002c004082462031503042d03500b05d80701d203130045035000b48510064001720b82650001c2c4a00e05000d4130445600e2203070040314405108000400c01c410050f03144c14000c162052680019400c0a024005144031000301707540c944100d0b00006880104001800f80c01140e562000c8103500d40140c0c508500c00350000c101e10444280f83c50524510755003400300b00c0303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 997597014 1250 997595764 997595771
    0x10e030d051e010b0c1903030506011b0c1a090a0b0a110c090609070c0f080301050a08010501081207031106010e15012d0201060f120b06010c0819120f06030501 70
    0x40005031052082c11242c2c140c1016000980d203003640d41c1d24a90450707040400b2a0240b0021104805400d00c60410b986206e51004100c07032030a0000903000210300b80b51880d0030412200040d0006548280c500140c030003400805070300ba144460b1074070f064025001019080081002d0100b01d50301000f01601c07500e155559200080ca00c4405016207503412a600aa0040c025201103045482d20b00d502550203035162a01075000380094035a058900d202100550f4001030000c0144514200301480c0c5e4060501840207219a5150035040b84d61000459400081a640400c2c400100f501c0f40d001342e20270f550850100c900e5940c5403841a41045019251310081c1000104208595401400080b4940c00c80346406198000729100b482c02070001d4480490442d5a00e8002080240002c0d01e594007030000341c030612800c0c50140ca0203d0300d800010305540d0603c0074080c0860006200b0b08221005c44c80401c103c000031185440068821410754407010644504044040f14035684640c00030048900035802403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 997598264 1250 997597014 997597021
    0x609070f1106010b09240301060305070507060923242a1804060608060405060406050d0305031006212c011b0801211e030c05120f07060518010e030d05 66
    0x2c11b5040000200030013000c01e02c010406503001c1e40c84558803803100d0500511f0075036503aa4403000c035510300b0422507440d481444003612491070464000e8509820310020007000101d889040c03615184103000750011210940054018000116502d41880d980d05a4010f075041080c4200c1881d00861642d100c41101c060240c1d0307491501d07001748170031504203489500d41b40d203484050001800e4010a01a041a1140d00004060f11071950341001540139944294403030510310312124450b8a00d61044c01004003608044190304503104245481d66004100056983c00140741100ca213004995025045901901c0d000c05600c2c064120032402200d87d5140c651079000f00005030742e00343d07007030142c0c0c0b880268208014902e00c0d8401c800008160007001904031184d4510400c3c4030008580301c0c100c002401d031018460412100b0070582c0d410140480142d41406003650031804c150103038601c00b52607151554081404100c6080503078100d508002c000340300303001501e0a125900c0e801045c030211703401e1600700007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 997599514 1250 997598264 997598299
    0x60714030f0109050a0e0d020304060e0d08031303090807030c1d010f1208042c010902211e0c040614130b03061c060f0b03060609070f1106010b09 64
    0x880380704142918403105240d082010110084c4070003807903150310703030b60700d102c40000780801700460000001c0d1036005568840c02c01c040100107032590300f90350340102e13000340316080010744c5079050781c1d40180b1842c410014048a414101c03400c0b0000e40c8a100c947c000c00070040b0600a00d0070003203066030fa855007804001d00048540b540400001d1240040b282841101441011445c4508403041401a80c2c0030741840c0d103c584d03c160001d0401034040c00000101102500640100340560062100c3c1100314242401111302c01039800e141c490740d00602c0c0f0604001441d500b004011044140307009840d0210501c1c08851440c0c203036000b8042d860125810394011080d1610031021a600c544130f4220354110f05180c500f96007489e41000d08055880403408020450f00c81c4101120105680200c2d80070423080c0311070094008486e4801041406034200d0020000c031134845400350742c1c000e64207140c03900ea5261280c1044400c035801942c040d4090150400024803510b41001034083e42d10101d0300c1c3c03c0307543e01386101c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 997600764 1250 997599514 997599517
    0x27030c290c0c01060308030a020a030e0d050703180308030f091911060d020f030a02130e01060e1311070c0e060a121202030403080d020703170907030807060b12060714 73
    0x885000000a500041d06110703000c40541040403100c0b001142407600e070365840e001c5404c11215003005036808944220841d90602441d100c07814468060144200c003e00c0c000d10510543c2801b2301070000003140016000044c009460003940c10120f12074880c1001d030400d060030342060740c1030001841000490740d4502ca1003200d003510741d54001c0c01c2016224002d4148803940e0003d840d290320007a030a0013a907081422a4006500c203400964005039101084100c03800b2800b49a00100340c0c0440403401800155000005010412000c40399011500c10701e0030b509000e00207650a00b5070794500402c4100c100813031058078405031204401d22401a80c7e40c10b0620400403894402e244d01c150341d5489081c040f401041007945000c02d5403041e2880c3c20744946a00c401ba03400400242000e030350000304030040c585e01c8485d00c41d0345401504600c0450510009240e80e60345180006806403400040b00c004103c41a8868003810401400b07030712200e90107440d11034a41c00c1c202c0b411070102d0810640380301080703008030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 997602014 1250 997600764 997600823
    0x201140f280e09060d0b04080c010f110406030f060f062105070507020108130b07110d0806060a050d090606080d021908041401020f010603200d05070927030c 69
    0x540b84007040742c9090800c1100800074125a07004000e84ca0b4040100e403001601c103100718011182d155031203044050f21402c481c0d0300e0300d0703840f4203501d041400300d014000311040303030300701c0d0a10300e000300b420514960f240d801450140d22920003802041c40c005003181c0c004540b49840190002011503800200c46c2c0c0310b0590300100c3d000d2001030703c10000c1000541c018507925801030004422800c00800d44e82e00c100000100b5607403003010601403003581e041c1d02c10030408c10f2884141403500d19103a09101000c24a00d01414103d007050050100e01c0c2d55011100f82d01c11410b0b0b03a0080c900b801300b213a0b2003c14544695402100b000140505458014820207805840c1c0c83c0c2980301c1c1c0c00a18062402106042d9040058051411401420900134105109000350000f460088001542c280349840c8001d04d040182c207000d078010032007503481c0c1004c1900460040c04689888102150a03070203258003400c2c0780c02c42d08040703980f010031010000a042d801065441500e200e116111144400345900314201580390 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 997603264 1250 997602014 997602017
    0x402030604020d0c0e010e150f0a090c02013306021501031106071b0602010e070e011a040f060f021207050303130203030c01020a0c0c0608160c0201140f28 68
    0x650128005090801c20343c1c80c541c0c09900c414081a40b0383c030303811200b88005c2e4841194071280d4001e00000d002041c0184191001c110340c6c40788005080c20204100c01c05a07c21110015540c0812444c1c0900030b41108072a52915024104511900c1d04002e0000318001041140010a40400b091050000074082c420b403502950b14450340e861950350240c4140703850034498100600f07000e041c0005850308030050100304c03400f4030441c002d03042c0400213084a101104001c01a840031a0400030b0b01d9003d400399065854031012a0340d10450380135604c040d4840c81c0d00c6045180d603422800203501e54844060041d101c541c0c1d09407038012400503400d092034055044098520b810800104100240041c03000d041d0303034400b07002e40c1d050551441d01c003400c9030003444079180403401810041c020020841c6035840580f4060038007003d0b5003030031640300304514041ca05807414020005ca092066a01401003036060380c9000558650766600b030040c02800703400450008901c80d080c880310340040d410307690140100700304030b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 997604514 1250 997603264 997603273
    0x80604021b0f060a180609020d060c0809280816020603070512010b0901090b0d110408100b04021204170712030e010b010c0b070f0c0203010213031704150c0515090c0414040203 77
    0x45496000c01001d040f40204d03803049c800b4056400081aa0084038000c410340e440e000c2840c43e011846608208250603844c410148405440d8562049030f00004005074000c4115900c2d40c0d6141e400c074a001d1101c150107540000007004000503103a028004003803500c0d442c0c000c5050399a90f0514281c05014020443e400b00740c1502050040803228400381c6a481e070784644c00300d003208204a48000c15406038205615039000300b688610341c03146a00810896180a076070452400110900c1000301180262004220814810690884803d9030307041c1c1d01c01d070350020025107000e4039415000d4001c20302c15900c41c0702c0b0b50904012004940c0107003038407008640c0103d038290135a510210102d814242a1202505008020306610090f8400348060090031010544684500f1b0450410400084000100c0031205200f04420b1207030310304502c603d5170b40ea040f600b4504040401880c04e24180740f4005032800a0200840030080b00c840c0c0041d0105100c2c4080e102003002e0140740e0241c3d03c030807000f00c3d80a03405502 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 997605764 1250 997604514 997604561
    0x20a090e120304111002030c07060e0a0509041401020a02241611010914030c191104050c07050d02070e18190609021e1c12080604021b0f060a 62
    0x180c1c0001c550040c45003440800080c1120b00082c010701058480100580c00402c01c480851300400c0b003600034120a00748001c000d16084009464042c82d800b606d401204503001040c1044030300340300740008500d220b00075501d9400c5107100075520301500c1c102209002c005280c12111034025900720b0300400c0c1d01c4424984a416030700d401d54400c2c2c00c9900c10a0340d996212140c5020500c3c0e1246000c4050803030b000385940b803800075661860000c2c1c480203080708101d40300d2580c0000d00710a41605080c030702500d0104072a600c4280c0941d071401808005000ea001340c05460000b581e0203d100c009440380b00301e219445840f0f0710a00400011141e8000c0c0499021005100c020410002074803542c1e840ba15000c1409076042d4017060408a40d1450a0301c000c07480d00411590745000554201c5106501200d0801503515403101080c812901d241c42c0c05001c5448042003040e241c1d83c040b52a41c942060b00d40c100311990f1400107a030342d40124a046164002d000100b00c2000c0300b8002d040c041c981c002c000c00385045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 997607014 1250 997605764 997605793
    0xb0114040b100e0f21060a14010501020d030e0c06041d01080c0a03140a060e0303010e0604140c070201030b060a11010e010c0903150e0714240d0b040f1404020a090e 72
    0x103001d01c08562003a01c5d50903a101510700c1203240e860240e10b18024004a003016008201502e000c40c1007c55010844001801306907400100d007902c042e118680420304407240e60400381440715010300103800c8840010007180070101c54601c1c210700700d01402007200076aa226181916080c05c00d600710b601619444040011032007a00850920b22502e600b80d6001e5009595002c0461f0400d000c0645c0d1500040010402e072420300350403c2e0300c00301c15a410f0115400d11424081021802080e00c12410700c041040e0096911961040c0c1070040043c00850359003181c080c001e0480444255038140d01d600300600703410300c0c41040c000c9428900481d180c0c80e2400341075075908000c1009030780585000360758034084c405080b034040143c0c4006280341041c1540004d10b0900b4400700c3c3c41c0740d07079401c00000c1070170322410b50000845c8115003400b4490301c400a00400120002400740c5181485103901c981880e0304440c6031449034088a000f1031003128184202e07682c0741c3ea02c8c07050b165a5440407540b0303045550000c0405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 997608264 1250 997607014 997607029
    0x2e050a1206061d03071211030d08090a06050c1b0f1006030b07230d0507090608070906051b01090503090109080601081902040b1f2606040c05070b0114040b100e 70
    0x150f070050543d05079503203440078511140c0d00c81500b40c40e581c2141d0304110a60a092050031306411451074080c0d43da10701040210f81c1c46814500040000d60380b0030008501d4220380040c8d8203181004142d4001c942e41400d4803a9403007100c09048000c0c2c0c011541d00c2d17070160261788a071604403607014011001d1a620388201b550340301e00e4050355030700040340c003109904a10400c400906880c0e50b000b60020b690b05110000900c1d91540c1e400120030701110005102101d80c003c06002c044490f1464429603900a5901509080c81c40d001c1d000c43c15800c01201c101080000f2018140252081e40c0358480e95030386a6005030750780e00c04e1060000f44c0c2c0090541000e041c90101c210050f03640060b0000c6100d001c500c01081d908030300350b0512050080f240084447c8182c3c000f500102d1440d12500c040b09031458064140180003000d885144216130340c4540d9030070503008205951006805c1182c0703e54540c1c2d182490195843c0003084544524900001c0c00c0e0340d1b01d0a5a4000d040030700954980301d04940036400d10504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 997609514 1250 997608264 997608317
    0xa0302060304020f0a0b03010e0c07050c091521010507050a09120303110c03121614070f1a01060e011812110a090902011806020c2e050a120606 63
    0x2002c0f5001c4800304507112403104a00411050000e180d40758540400b900181d080905602510b2b8070030840c00002c140001254404200d048410410540764588540500c0b90704c2078146800030829015a0507001c03000b4030000d2070075100700082c0b00780d960f4440700311114480c812200300828016003081c0940780d800c0c10348640340c0c0d10a040000705d82000c2d20100d17056803c0241c0d424041d038000940240a80000c0d035105806c00e2a40341c030005400c0b81c40070040d0011030001e84001d1404030115a04041c4032442018401c4590040e070801c4841800701d51102440381d09000300808942c1422150303450b5403140568510b401031341e00c80c40043d6418501e9200c4080415001911652171190542c50b6039924800102d005000e0003a00107001801c510003d45041c024540008034400a100c04100e095008180420180c40891f08074807003100720703403d560b45c3d00c41398115050030116601c1c50341000c0e07030000c00410010b001c0c0d80b1003c54240d01b00303505109503105d85c01102d0015140d000410702d00d14000348280f80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 997610764 1250 997609514 997609519
    0x1e120601050a0621151e05031b06070c0306050106090b0408030415031515090806041a04031209030504050103110313060f060e04230f0d08070c0f0f030e0402090a030206030402 77
    0x3d842d0080e040c800c15281d091044401100c0c12104c20444804101c800a42d442100e45814640501e0040000d85880c0018030b4040003000403d000c0c9c5440d6507590846235000c0c0e110401003580707600c1c5e0a00c280100b01c240120f001140310b40e1404200007030b41c28155811198034100440c641410102400f40360441c0d510f8003002d040d203c44600c0b11190003050b41c1c03005800c001060b0a04100076100090000049511020658000c1c2040c0408658611241303201410042030329241c6403154034040f00c111021480b00c5014a103802161010580d00100070006c0311000d907018050307054204809100c40c40f003a585e41c241404100d041e80b001400c030350014049101101400070b002c0307985003d80026108100e4040781c1c040c00f060080070282203044402e010060141d0001c00904e48450203080e5211b41140c08c00f014807000ca000910524868001841c1c0c160f80000c034106210b5041c6085a802c10802c002100414000700705204941098400e64540e00740003400c20305168a95024000240d1000e070041c0e8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 997612014 1250 997610764 997610807
    0x9030c0905060907390b15090c0703090b0a090803040306060602150f1303090906080a02030717060403120b041e0c0e10110f1f050a020301180216021e120601050a06 72
    0x1c042407003a41024822030504403450787c026801002c00c010010000c1480b00040014071017480800e9004806600b80c80ca418503042d40c4142a08054079203440d90f520207c000c1c4000a000710422010ba00400300311640d0340c00300c1d0030071030b0300c003154102e103503402c40d00340e2102c026004c001175640320b844404c01001d0b0b008c1d041040e14540c40c3c25100043d118527400c446200d900807a100411030804200283c024500640c8142d04141d202e002940c075507030060405010000c01d00d038080750b0030301c45512660140d00000c004001e820003079508180c0d0355000f4040c3c441c0281c03030252002180c1c0c1c0954654507900000611200285c044508191041c0420300c2000c017051240c000011302c021810020b090501d00c1800035690310045111384407003641d5004080000c450b00610042000c940d6060400d40c000c059080c0150701d40c8100c41d4411149850303000c1c02781d440030186c68a0198260310042c00000203100380ea1099894100301490ba65414080c841e03036400404801c020445644694001041d1141034009070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 997613264 1250 997612014 997612127
    0x120f16060b060307200102031e092506030b09010609051003021204082a070923150f040908030402010813080f1c05070e1009030c0905060907 62
    0x1440b607810072110140130501c1d40440300c9404092503450b4048400d00b0001758a10718040d114a40040d008070a8001c41c8040312000c101140c4040c440f42c10002003900310414406c03a282c0804150311090b10410002c6840c100c940d1142e8106141c3c1385058458940321080c001346070005005440c02c03900300400030142e0a100d222441d40c880004a03000700c1c0a40c980d261180d00b41880d900a40c0c41c02200c400c08038040c00120303241e551002c1000e000702d80781d68200056031074a195002c002c074041504403e1500c80600c082111071000000f004503912400d5881503c0310b4103210a12044450312100506400d60520000d0b0042d80f00b2000d003a445004140d0954880f0401c0d0703111801604641d09a41e0000c10100302111450710702c8100304410160303d4000c2c481d909210401512044030002c0c210700a291040410640c24002c040f000d00566000d400d521155944075a00001404141c48607441031201da40860708191040c0c0701d4000d0500c2028143c0f18500901e25140400203054400400d4680445d019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 997614514 1250 997613264 997613269
    0x10b0d1115040f0305120a080705070c0b19110102070201050d020f0c0304080a0201080a091509081312150903050d05100510080f101d090715020a05120f16060b 70
    0x5403000300108210400f0003411481c245003482d10711111042c50704400e04c101c40b00d06e030f4001040c46e0040100c0c1890740d034450751404c203000d41400642080f241030100061a28450900c20100c6400c200a903680708100050019068241e10500d1000b0340000e00078841c03481281603980c0281540340d100349505207442000c200f850300b10f0700709910007801c82d000300d0012400e650300111800ea02a144041c20070840e40780d50b6403040b40400541600d000c00e5600d50000003003106d8002241c0040c40a07096002000c2c0d07030340e50000c00325807404000320f4800074140160408001c850040c4c8401550684406051000380e9031580000d2200801c4020070038040a000107550721840d500c644089003959510341a498030000300c0a1411005d007030100d80e2890b04c04100103c2c0908000511850700103e0610041c0e107075424428500300d603d401c540301000884d0409212030b034002a83c000202e1040055591025000010106134040c0e1924490810403c12114006080100a034440b007449000c0c0006c180308544007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 997615764 1250 997614514 997614517
    0x212011506181707060305090309060a0507050c12070603061409073006081e0c040c0c0b010e0412050705100f02071a0601030e010513140a080d1508010b0d1115 70
    0x704010f072500440018000ca83e4540241984251120011464456a84085182d510805000504000010640404100d4207111007444003000410a501525944c80d0140c1ca0b280b03588103103404640782941c0043c2800c45480210014140200313000002c0ea80d012040e00d0780c8507a001e43c18403021902180741d00c4003035140c0000101900c6e412002800b9810406803d20f80000d0700d405400d60243c800c40b090341e1500018071603604d01400c4d07d010540418080c41078401c0924903130000e008540900002c1507403100c111642d48281c4c001d0000540e02c0352030a9068a241c8101d0802800356040494180c0100a454025450541c0140001880d00006445401c15600ba40700000410b01c030320020300c842907a041c0502c2580e10303100b500812160400c84000305a250981070001c2140400e009410000c03502030000c403001580150445590742c0c2101080300042440c20900d0345020307420b05d4003003050701051060009000303028041400c01155a02e13101c480095001c880c0394403025211641025101050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 997617014 1250 997615764 997615799
    0x7060e01090201031a090109111b2d030406050f0405041b1e0512041a040b0a0612050619110c03090a051c0303020a020a0210020604021201150618 64
    0x100000345100071440010260755101c10642c06016000100040a9031007045007130446140b800c3c00507900c4075155445001c1d025904400c1004464041c00e03c03001200462041d000001501e9101d403501c01e0746498482c1625001a15445907000707000500166020304c0090a03100f001e244c0c620308113540d600000301039490180303901c0c00309800007140b0148150403034071403884140412084d80300c078001e03400f00a165001c0c0c0c0100c5152a0324005c0031405211040122008030392411094024501e020f04080d40f001c00d055411148a601d04080016404c40c4400c207103003020751101c040c0c004c90300c0c2c5030700c16001d0882020040b84110b5540c80144545100000282406643c0700c000d10b490b1040e4800304a85e4900940c0080d0041e01e0034180c00da0348085c003c50b4420417a5050400503211400c44400300c0c03802076810002034116494140c852919600003601c00d11551003243e0f1340304021003182c2a41c0c01d0703071f81d1005125981c1c3c5091b0010700c001802040071190f642407d451088590750354246026103105041d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 997618264 1250 997617014 997617041
    0x501061a0703110105130f02060c060f01080f0102072a0b03010f03110a0302030d0f0e04060902070209090a020f220c170c04030f02090c071b090e061e0c0706 69
    0x1078420708040d0041c0003c1d019003501c03002000301c2d240c014024408100001e038014095860881c85070301f159640020b69161021a41c201c8685213030942c03030b600e03241034203001b000c0c054810711246850340e6070140212824a07500c82407161504441029076006c150030710b19a02418100303000041000c1c40000069802840c00000d040020340c40d6040802c414485c502841d07002d410000000d1000d614001074401e510328262510540441d14030070304655016426134440c1c0e1180c2400c0c000110000c40d50050083c40b40201c1e528031194403001e80c15550760040d0b40c40203400442104400c03820740340004078101100080040c1c4001c668101f0403910071103400100c00c00120301e581c410400c500c1030316030b0540d50110582280d00d00d05420341c1c80e0056904061030009200e02150070000340140b00c1c0b00282c1d1901d90303001070995040421091609a514400d0044000091400c0d10b02c40ba80d000004241d806147c21f00e001030030800c60b030703101c01c1ca00200c01001400d01140410000340081c24522401c6680f0044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 997619514 1250 997618264 997618267
    0x20409030f1740080405011b1a0604200a1407030c060506060c03073e090c130306050f010504050903030a05040c0f03080d1b050a0c0501061a 62
    0x240d03000e00030500507607035001e45008190400c03603d01107405074400141c400a03038429002c0242c40a52400c144080c2c0550500300411418808000b800400b80c42994030903201c0c00c1c0010041c0600385910f502c4120050640101001494a4101340000341c1d40c1118028102003160000d41941c5c0014a00400100c514a940000e400c00d40c0c6034451030719880c202c0107c00072860903819840044c0030034006c035030140c03e1503520310201d004caa0321841291f280143d07660036280c41d8003840c141301450384084040d080b00c211b0015001d8024485100003034049800100700030394400c48c01002c3c00485500144090080e500801210460358051020710b00198031130140440c461811030a4080ca0800c181c4c4814042d500702000d00460f09004402d6a0380681c28410010b01940d0302d0a0060108029610000018290400100c02e01064800805050540c020144950508807820190300e84558907035100083c010310581815034414202c80b0b00b501d01603000452200c0c2c59801c00344004201440f8005860300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 997620764 1250 997619514 997619537
    0x1d0d030804170418150e070201020d0510060f0302210103050703110d0809010f1202030c0d061a121005061303030e03060103030e0f0d061b140906041403010902040903 73
    0x4040303900482c1d80c211050142040e24044240e0800110002444c0e00c031a2900300d824200c0c641540c945c00200800200000d0505044201034000d60000800c00d40c103030b0a2000040b1403881000c504012500107580c1c1d80748102c03006404500a4020b034240740c202070010500160780e40c00340340b8000e020714002d4020b440514658580341c1e40c0031b6050030016014222822603172000c501e800c000c0d200f000f082070030280c1c2064000f81c000c4415100e8024684401742c0b0100500c000d44803070401074002405183c2040110030f442c0e140c00d8404101d142c0702250341c2201080440f032091404c0300e240790404003624090701015114000203095410642c0403491516007140300b0014181e00550103020060103070060080d950440c3c070010f10210894003054000c58074201e9140c0340d902c90040d8071030700c5604034404004001210706080601000664420001040809110700b1407440d1001c80e10300d070200500140c94980f8001e07012480c044210300c5203502d0b5507103100010160b100c9014120109200782c2e1007990151 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 997622014 1250 997620764 997620773
    0x3030b030d020d0912020f120f0c2d0a1805070e06390a0b07091a03061309151d0f07051c0c08101b020a031d0d030804 52
    0x3107070350040e0001c5520890000c2da403580c01c9080700301500c0c8560f1382c038100c9002c18000318042c0c24003440b0058010180d0901c07460360410104580354800011015110013640c900c003001550683c0c1d64803640c6404401c080303069148010142800907100285c440e0b204a0347d903684c0e1130290403800040032072160301e6108016015038080300403545d6010844299003001d50034841841e02c00200b581074098828403c00110303402c7e840100001e06400014111542a8924501404050010b850040114170610000300d0303006100502c00942e07501200388a0f04603600c1c0c00030402c90840001c01400ba0a0f5078200d94400f0495000103070340e207400d40fa00081210020369003407542164994207172030313420b03000401c084190802c0410307150b00300c0d01c0803920b1601c0c0b2244c44490510050400307600525101d070401000540f01ca000c22850102182d00b0002c005030840401241c1c0200d020710a0440103070000481c1300c000a00035038150408440c1200c10b0381041100301d0226104054020050300031030450030800c1b0401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 997623264 1250 997622014 997622023
    0x15070b09150c090108270c09060306070518010c020423070e0102070e0a022505010509150c13080d051b010903092606010e0613090c1a040b0703030b03 66
    0xd5100e0307292055103240c20046401603004084801e41002207580108501007860703049500480ca54105985c1a800e16419040e40c4100c1e20340c88601566188000900b149004204188247c00c191180c91034a44079aa1400a0024181c40d041c1808801c0d2401009600e40f44140c0018031820b21051345551400ca002e04080d01c001400c0604100c0040754005050340e010400404131458145044940d85511702d84401078040c0c01d8140c3c1500e4485440e0388189041c1c1060420210300400003003090380c0780c60080b551240c4034988145170304401c050100d4405a070b40380050080305200b403c3c542c450707501c542c0c00d01e00f09021140401c00061011500b41c1034504120901c8090480303100082002410f1583c000e803038030071284030700d403c18440c400d5000c45007244003160301250045442690810340c1c45a80403034012000342e4005005083c8034520203034481092140c21881c5070481e03030320001c0d0741c070700b0245c3c902009014001401a08040c0300004210020740060300309644079440203d100381c011001d00d842c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 997624514 1250 997623264 997623283
    0xf18090405030a12020d090812070801031e0206090a03050c0a27020f0c030d20120a02030705132c01060e10030b030d080103060606090e1515070b09 65
    0x221405014000021000001c49070b03a400541000d0f0320201e000301000009008003a90114190700740f019040c1048601801803030741103210b501002030740e01c0e0b60390100c42000003400020b149003440d100c035034102e01060800c46485031009010b940360007130890220f0300c0d0880c00c0e401110300303500540d00c2440b00d1501981c010098000d0041d140d18990a010041d402040111000c800a41d400150801c500100b242181e011405440469544030450304070b0000810040d01c00c40300383c2100c92000246c0c40081c030121000c00d40c0402c50107400f501c4401040c4025032002e0048014000200641e0560721402c0070380074002d00b190aa880c41407050030805442c21105080d00500321030440b00140541900f00b00f150361003c0d02601d002d03c5005407081c06500901d01d0858417035042c0b10382002d4489413a0303c1205507050b40c4c0f0501090001940c0d4110681d4410503900411100504d0500000c1034500c4803500e5401d50f0b00001e140038a03100303003029142c001f540080000e880c0720843c2c2c8100b0140300e4080111900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 997625764 1250 997624514 997624519
    0x6180212070801200909070203040f08030316052b150e0906130512030406140108031c020c0c120a06020f18031f05070207080609010c09090b150a05070501020f18 71
    0x148054003180c190f505d200b11884c0ca84100e040c00b02241c003d40c4200b0940e00540041c4480c7c40d05181c07544005c0d5580d400440359003a280480c007240e1102c039440344040c0c3d185200e85040440f041061701c07940001c0e0340001c08030b10400303654545103541c803402c4100100c8010103001c2070b000001e090085501d410a40001c011060f141040041500000c00c0081d10400d1507200e80c0082d500c81c0c550f860f00342c000c0c00c0043c46810141060034000f04556502100030301c1010748403505252101e01005501040c2e015042c000398081e0001a14604581860807418582d007038801e0951704043c4c52907850100f2078000068032074108402048030140c1070b0350b210103a21a003c04800030181c00da0000d003401c0780e13544000c003034000e2580c8074400300302001d00810401018180600985030300b4940082c0d181e000307040c081c80410018820303040c0005c460b0803d1042e80b40c1c4440c0981182d182400010502c200c0d80d00224400013001810004080820400c0c40a80b1030754005400d881d64030790090150403010340b4400301551 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 997627014 1250 997625764 997625801
    0xc0e090f0609010312020a05010f050919150c0302130f0e010801111e0903060117010f020c0c060702031014010e070e010c030e0d0c0f0303080f0c040306180212070801 73
    0x301d2a82c0303801c10b40d811254800a003203c50895014200d00340600c0d030394003c00640c03c145105034074a1442e01b18600ca484101c0480d040d9048d00045a0041d003c00c2c403001d0300c003110300d0072641e038102510781003a20b2400d243d00700503207030000c4480c0400c1d4841c8954080c1018655412080c02402c8100e4003003030041c03c5030310090004040c0342103000010701c264100c11486100b64640300d40c29950460a07910380001c01015140c40b503a50321210301540c4c40c80007411b0a19480c158007010310b48050b2017901e4900b8102e40040c01d0510780f40c400d001842d48003034400c0e80c1c58458039908241c158850f01828002c1d44480c2c0004500754074000c2c0d0510715005c00380241d4240543c0f0307401d91038140da12102d40c0d0742d100d80515000851404101c0030031103c0d01002c030040c01c030072409080030030b6003102d1688000459201e40d41c0c038015580c80c40380c0e00c0311000040d15482d8004004010030804108690014200280c41d040d4101018030310b5400690300c4440f290a80a180c0c00005007000261002e00c02c00c800146500ca250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 997628264 1250 997627014 997627021
    0x60b0c0304050118030813090c092d03050610030203100603051908090604081b150f031b040618050418140c0301090311061f03061e0c0e090f 62
    0x2951039000d02d028550402c185051800000c14030007034000002c0d90000c3c5069a200101002010440f016005000c649402c0044086445110710300340030803140800042e03139006040408041c03d10058240c603150300f20901d80e0201c003080e01440790601441141840202c520714503c185420291400c0015000e107180c51002c0001c6a000f1846180c91054503119800f11910f038940ba40081c040d10028a400507808540422503900014080c4004041e4581130301c041907808081025928148064a0f07420405100310580d44100b40040d6410800c3d00801c00b4112001c80c03c071400c40d41065000c4000116a80f564072407501c5100d05c04000342805a809100c15045042c1c1000001c90141c0d000300006604200d4140914003808030344014a0028002d000ca40b00d6070400500864815800c0c481901840002c1004094409640840146003044620006166403580401000300b01611951101c40100840b003442c028460b0a103101c1ca01d840314144080150140301e00c051005103c60010001c0c003050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 997629514 1250 997628264 997628287
    0x1918140a03050d020a120f060f0b04080a1401020c1c030e011b110c03060106051207020d0c02270109050106140708120c13080601170a031d1801031203060b 68
    0x22207140300f03140080540e0f40e1140c40001c4a044520b42e8001035030381d01d1f14214030200712032500300601f100d01c0a11002e49950b291110480984103d2080e525a5071001c20201e0000390342e42c040d54500300802c1c0005091507030203003900d41840c42055400031200c8400018110040d09880b07400c0d11100101c000304040c02108844000d502d50300c503503400038010300c1180310031844000c10002038404009400e40e8210359482070040c016800c820200304031520580001000e0600c0080c2041020400341d030340794041c1d0200c0c0c090002c0000005a00c080c2c43d05405841510f01400c02d920500814914000042d2507240044c0108040742020303003c0c40301d400410481c3c1c04120300c44190341030708a60040380301d41510340145030601449044610058001200c0000440a4012611504884150390103088080101540c151030700310021008011800441e000306541c40d24503074030003c0200150000c801948001c05515001d14261b0045421000103225440c1341341d0b15000c0c1000400150810b541002c00341082c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 997630764 1250 997629514 997629517
    0x131802031303120f06140a0e1905040f06050f0403020c0406060903320309042003150a05040e071502060103020d06020c030d020403060509121c051918140a0305 70
    0xe001d0704209106803050a440d0b03ca90180c480602d41501c20007540d641d43d84500380d0801c5404140340300e40b01c800b00c0001c416454a01c0b540c4100c010501c020059859903014900800001d00305550b811fa5201c4130f035000541c60300c52240903510506895819250510b4001d140100305400540114141107081003000e80011b503603425241c0c802998454249102081403144c184010386d58900352032000305100642c4040010914020281d03012701280428844010350040341c003007140c0c4040000c2000039074040080d81c0b1620407000041054044503070700c2000400796001003400120a40100b601005007061b20707941075007841035a0002d08459851500010032460359090041c3c42150005240c15501d0380600880b0054211454119280c94803030900c48000c0c002251410210320880b010402d024045209481c9002d480c0811445200c164455140107442c0251460b0300c40ba07200d1803001485562409003001114062401035a800d070765050629001c00c52001881c030380c3c1c104900d2280404d03449030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 997632014 1250 997630764 997630801
    0x60b04020c1b0f030a0b012904140f09070504090e0a03020a14070305100903030f0b0a05010c060f0e030a08010b0310030b2205070920030f0705040b13180203 69
    0x44100049101c00c0b0108450035500c40f6066494001d0058204c100646103c0c014113807500c0904580c180c100b0b034040514504000030f1000742d2140e06100070054020f4149038a0720711800a0004104110100c002c50b140c03400503541c1e4004030f00d0106061046148501c1030031100c50b9000000e01e0741003182d842c048c0d11061403c074007030104415075071507003000300f020083c2c24002c60340241103c002618209410303000b00002d100c1240000e040401c030a075081300710b0090721103c62004040080b800c0c60b020064518020080c41241c1890f2981ca10b913105400c0c034801c0c0000720207808099550b03013542c580d00400b442e00503005050141d406006111200985401d22002d0f258810031403041910703450004004034140700401c00c0e0803c00e8410301c1d010003d01090050480303078840028049001d5a44140101c88040c25500c0030351401031001401c80c1c0b007884040c603003000c0d0318103019150a48a8010015a60210790818200d02000008008107a1030303801100c1c030b601540701c0c2141542800b50070b840d040580e40b07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 997633264 1250 997632014 997632043
    0xd080a030203180601090b120115230411040e01120b0406052e0806010b090619090b04060c0506070c0503090d032a0203070801050403140f090901030f060b04020c 71
    0x4000100d41e0340700310141600c43d80b4030710112003141da51004448060310100780c0309405801c00203c038100c2201c05000d0050307080082c2558825481c20400c0200c0080008a44415850700401d440a401d890711b00c1072b4403884031900581a80c5500742400140030140c10703070081400d101c1316080b12010508051500c0d1700310703500110201c0d458a0300c10280301c441c20003514107010039081307841000c007040f044140c010480c0c80c10070990b0580d0717980302d9010030a4001d94000a800c031104114407140c1c810345440c8036426801a0a050001c2c507120204180541c000e0340140300850402c0e840d0390b060080c00c2100503449141e5140c103c0ba5800d1070b035100d0b1744034040d000040f0300070580c540340f034420103000711461541103c688107100030311900300c001c03410900082c6006074000e000b4020701251100e418000d49100d0cd4150f251681e074424016003c440d1130784000c504490b0351310188113101e0035039500103003240290300a0003150419815801c000044510b500001441940704025894050a000c5051042c003400c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 997634514 1250 997633264 997633267
    0x120406020a020c04050c271c06270507120c060503040f06021c06080102030601090314070b04030c090e07031e0f060504050f100612020904050a141b0d080a0302 70
    0x41c81c050f031074030580b0308010307622504100822182e4818030014000060099850305004842c01480342c2c0c0d05403056407025000480246451040d0344d0614500c10441e2082800147e10028921030541c2c100f25441c3c10742c1009901c00700306062020800628004c0c100742a464000003590341d844481103a100c0c4900d80c00e100e030220000c0c0910100f4208030a0541e00240255640c101d412121003d0b04a885c0d5002d0102d8a0500045000c2e4414420345e0300c10131040e119001c1c06400d5480703501e00b20213107021108051040550100d105414403014000441c4a9584070081c181000440c000fa1004d0040e0000701c0d0344129400c102090720741019a20321104582c989070003c5103800e146450fa19910000f800c21400c1100348010403000162044c030b4200300c8000d407002e90f40c00c00304010588020b407064010101207042e46c1d40240c600a2202500623103e801203404964107981c0d0103444810b60303c1c03401c042e500001d0301217072452014000068110001c035040c2000c0c8456507200b0000c0c0c00740d0703038041c400c140e0b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 997635764 1250 997634514 997634527
    0x50105061002120307030e010f0905160e0103080313020319150b090f0a020d0e0f15100f0302040b011205150102100e07090506030109020a0b1c0e06070e040204050a1d090312040602 79
    0xd0279440403d081603c0f50017407089210a082c80d640c0c1c2c904642e20701282c0031581d000011218200e510b0f05060b43ea002441d145181c90346021040542098074060341e15000740e0200d07011020030b0001e030504140c1305001c1c078100310301024082001c6a0a45c208140202c400004020901450244142d88042c40240060701d42c9001009940200405182104144940541e41c120410002020301c0c140d00240908802075540d4203036220710440b2403207200d604d006c2c08a0702303000500c0c03c2c2e08004956441850012501038040c80c6001c203030340c1c09480007600c1d600002d414203015607060001c444e6090190400340425000300c3d0815a071100c0c1440b0781c03a912039842000c103d1075a0700390011002541c0050001d0800e644170001446503034841905038010301003040d17034070203a00340381d003e0301c20b419002d0070180c80d665032145c01c1510120222040a40e20039802c01c00031580c1d549400a207400740003040d4400d00180300503c0480803250018044903440d0344140700345d965000e80b006110380d015a1100002d603d804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 997637014 1250 997635764 997635791
    0x170609060f0922060f05060a1203050a0201021c051e06031b060409110301210b07051309060f050102011413020d030216060509030114040203121c060305010506100212030703 76
    0x40c0111a4040c90f010000000c509008454100304c000b044441c03800c1000e03444140800640079003034031401c684098110001c3d4040713800350001c0c021800943c00050320b489600b0008000c0d81040500c6041e030380d59030f4414032506c10a0480d10200450115442c1c1c202420b24000007552585c1d4000501940300c10750301400079030340351407064a0050030031180c1848bc40c1d86200322030301e05400034003460a602814000c0408498021140d04ca00f07160440541c1c10303d40c1740c40d01c1c101d903907500c4042d00c178140c0c082004001803038510038400c510003440741b0307030440000c0d6052500080c06d65603c980d44451680100c403c1c0a09582c59011485044e58110b03400f0113101114074040c3d0078031241d40880c5442603403003080014026004401004102c0b03080380200043c648070b001c000c103812010345001e90180c5c08103100b00f00081d1034000812041d549416407500900f8100c20070012790741031790000c994994480060105a003083c400010380341015001904500340022101240c1d800002e00c0381c010162189980c00503007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 997638264 1250 997637014 997637041
    0x3071505150901231801032a0905060409050709020910030e0304060503040318080c0109050d0314220801020706050c070f02011209020301091b09020f0405040e0c0d03170609060f09 79
    0x440050304281c174043c5601481c0c910440244019154401d20313030fa050000c1c070081203445410f007194045a40c441c2d4204120704e03004200040c81d003070b0070644d160ac2c004080781c0d00300f000c5401840030302c1d0b01607610342c0c09100340b00920b065501145c0c1031600f444a5200c0c1d600001c02a05e0035a51580b81071916940e56040031280154550650400c101c801c00e400304d504180421003000403e020380f1450781c440c1c0d556041c40341442c070790031001d400200d000c00560148035440008080c101031003280400344d070940128040c20b14000b60f000e82c82c141c0d0300007040c00401203140103030755020120b56050390502403540c8803904034084481e0002d040005480c0c60088a000d143d004090264000e00200054105441c2801c0d00e540c018424a4469084110001d03440c1d040303000b25003180d052000302c0c81c1010b20300811701c8064951440420a02d006e90101d02199495001200303d07224025a601c8800c031f8411850f0b0004400043c00c100c0c041c0044004105468451001c0c1400160040d203000c40c0702d83c1c41c15030300750f250f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 997639514 1250 997638264 997638329
    0xd27120c0308030c0a03110c0d081945030f090e0f06010e120c1903053a0906120e060c0901020f07030512130803071505150901 56
    0xd00c0402408144c3e0303405005088002c06544040004040080c000300d51805026900c0700180c1c0010315070710304184100101c0d50003403a00d0071f05041c0b42981c65502000c0d101900c0c050003ca032040120380744a140350090b24138008503e10342c14036001361400340403a08800c94520180c01c0c04060010709084c54894080c010041c03117000c01d0180b0382c7c141a402900303115000c0e03488a00080c42d00c80c2e540d0843c641540c40b24584041c8800038025103070030714184000e48100748509017180300382e1903000000c41d50910001e58213500c00040030385500320440c11032401c40c0f00d807144003c0c02120755542080103500000400103440090914105d40d005903242000941020005242c0303500410081c0304190f5000d0003c0c014241090f02a80c50f00407020300403950703c01d01413201410030340c081241d498414001e0801030010103003007a03e10340c40c01c0d1605000c0380703140d2200c0411070350390341d0341117174200c40c10094401c0e540c001c1c041030100300c420301d040d500082000006000e8001800c3d0880d00003825142800201043d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 997640764 1250 997639514 997639523
    0x30f0c04050a1401170f01090f14090d02071505030c16150c0912110603180106030b04020a06032904090f0606080d3006030b04050d27120c03 62
    0x9080d40f0303080c4418a0b101082c80c1107022441d075160008031000320142080c810303848080c2c4030f21940e20300240080940904400b1280d1940e403042480c00010101d4860342c030400e003400040c1200c0901100083c41d010392075020820907280b04200c082002d9100003141c1d0014003480741203032901032800541c69000c0d14100002e002142011014a0f01040c1e07411228885c8180d86513400301550710500010f02d603025480c020a60401e500010003140303021710145411116540000180241d680398840c00c481035038000340c0700100344070101300442c50000e0440c03010304030500e030600c10350200a00307030036032042103c07910182801075131502c01d030036251a0700000f00075821018621240c003041c100000108003d0059080a018844004550f00c5c05450b02c1845902801c00c1c0e1440701d8418410840c00c821038006a01280d03444220000c0800e6454802074007490158000d0842c80c020150090a1031410450b00442502c0002c141c00b041d20101c0303030601c00c0ba50b00024482080c401c1c0c0ca00a0300c540505e400091 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 997642014 1250 997640764 997640779
    0x1080303040b0103060c05300c0a08130f080d0609050c07020928110904110a0518060d0f1410050310050a0b030105040c06030e03030f01031410230c030c030f0c0405 72
    0x100d40044180c3c400d4820400d5402034049d8842c46a10646440b0b4041008046128a030100b40124001c1098608041c015641c0c014000c1c0309680711007680d0300c105250605c0988400c824494210944a00c40e0080c0115081c986000f040350701060541030002d180441c3c1a4403680120706200c400e801c20394100d002014100490f01581150241ea40c010007401405140f500b14004940303190241214401d00345510ba0b6418180102036115a07903004d907950b03542084d000c0c8007180f415000350040160207030220001041e0880102c00110580f00300510301c51050000ea507040003203480c041140d2101c00c1d0400d1021415982ea151044090141c00018030f8240d031801e4104801c2c48005240e94040c0c514030b40e01400882c07050300c54655a40400c0d076446401039851001000001e500b003040b50542c007124003d444003d020140c003041203c056001e01801800311914085030104030750310641c1d005508081090440c00c041e0030040240c0401001198030710600c41c00316010141c03400c00d8800600d8003d00c000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 997643264 1250 997642014 997642057
    0x6180703090c0e0403050927070806041503021c031b03081008030901021e10060e01050f01080c0a030e0f0f03040f0819060f14150901080303040b0103060c05 69
    0xc008000d1618181c0b5001c28540340414491082149540580d40581e501c82c2040c503100100301140e8032800b004406068841c00310200a5941d141061081c8180c0d1680304003447d1501c00e1005942d025081510000b420000134001030707440802800c02c2c0c4a034046501290340306864150307242000c2e01200840d04d41400480e20070140e00c0503465120341a0650400540c80c0d6506075240d4901400e00300c0d178056046442924080340400e010450070aa102c0d0407079056004092000d41100c4964000041c42c3e0030038401030055051052044280420a103401861782c03405258140c614000d84141404150300d40d01d2504d5460010070002c0c0302c0c2400c601c10381e05141101c01600c0c0c1d40e50b200307209605451081c07079800100d1940c0403519944401d0b2700001e00ea10f1030303100e43c4c50000401521040e202c0c103966400451071840032003004503108000b0f80d03804011540e001c004104400781b0503402607045500406c1003000144800a506046a0384180c010070320350681c107003c1d01c1130700981c0042240c01702c07905840e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 997644514 1250 997643264 997643267
    0xd060b060c01020c0d032304030f2d0e010c03020c0d02031f05090705040624050c03040807030b09012a0302040308030a050a05011e0b1b01141b040e010b03061807 71
    0x101c0314040b0090300c04100820054112011200c1240510111800c0300e90000f00400cac002c00d040007401240d40303000700760303e40d0f00c001c00c04e601c0300418429082c5c020f4a01c0c10070344440d044064880401424204404c070f05690340da002303541c0c4018035011030040b180c211100045440400c00d1340c4003140e60750009984403c050030000e004107011505c401d4a07115140c40000c113410907202e0710064604608080c2c1c000c0d0b541c1a000820b604055513a40f0401404014500c0d04007420b1010b000500032413006071000c0d6244d410701c064001e00280007440182d141c0502480b2120050140c95030310114492091400001c1c0e00301600280207503840900103000000c1000030b940f0071039002c54481c80d83c00300c040201366200d010880f80128038002000c82d000c0300c0e000901050390006c010b000c0e0981880803065017104141209070035941c0d00c502039452036140d28180241c401200c150010320342c0c20454680e081629114840054581c184100c51000c0c2d400001b180a545070340b0384010709000c0028010304142448031b030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 997645764 1250 997644514 997644523
    0x10f0908181509090402030708060705090306010b090901060f090b030703050f13030210020c0c030a030c03120504030912020303220f0608090a022e030614040b0d060b060c01020c 78
    0x1000c41c9007482414070740c215241c0001002080103400e41c072a400d2110490500200140203070003640d051041680006091000701720062151a0765038850782c8a444550606241007030680108203802028824003115858014035a811104585417030124403900359025180149150880c0300074220000401c2002a090303003065000741d0342e4084c90041541c46116000c9000c01c2406d0050058000409000b20010190050586848040207640c03515042c0b90020b45003188401040300414005c003040d00c1032580003207550021009010b01400039140c96903008009a050f0700076030740410411403983c800d6440406c2035580701c107070986202c246003d881c0c0c0442d5041d440761103141c0030055241008544d05e8403807000c00c0d00a50070000144804440d5a08001400f003088031117802c80e030118902e00403da0340841d40000078203800d450020380141010400503a20007003405841c0180c3c1040c20802e55a128040c0701106250021000541d00038070341c0c00070b1454410300d04050003642c00450464201c10740400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 997647014 1250 997645764 997645777
    0xf04140106060816050c122b0510050a060c06090c05210120042102090403050d1505030a1209090603051b0405090a080d02120a1e0e0d11010f0908 64
    0x6442d41c4d0b0680c12a08454034441d1160280b402d41051007040078001d4040040c02c50451249141d451111006481c40002e560558103000101d4940b410302010620380c641c114051300d0103842c2605901c2c14040054040d400d4014000c06450740c401d507800502003a0114103001e00300040180207000031048018810884a50460110394600300c440d410720803052086544810b5001001814540380007401c40d6958600c0e402135004955011090005980c1c0490040c032451181c1c44607038803408146103100c2100d2410b40b409045021050042c44542e42c00a580d24450b07034442559100f0400400003100ca510040c2c4c0b00c044480e040c244040304102c0041000032245600106500015190200b000203a0301d081c1e404000d950440c247e19804a40c0c0c2c5c03070040c15400b03c00d02c0098985020034038000a440000c07100e9402d180e0f541c0222180ca408000056042001081401d110000ea1180c00c99100c00301c00d0300341405e11903104400b0098070030a400240182110507010482c402150621104990144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 997648264 1250 997647014 997647031
    0x50a0f1a0c1915290d0c050316080f030f2205210105060a1a0708040e0a0e0d0c0309060f09030605090c10020706020d0818100b030d050c060f041401060608 68
    0xa5450302d0810b9042030701c0343c10b41d00080b0584c0300d1002e820a0101d000955101030f0b48003002108049042c0d10208a1803a54824a190500c980b0b89002d1807103051800104011a40c0d4004109803420460988181d40182500d4000c1c0c2d8004800d420050100c040d0641c0110f4120803070240c00503a102c000344500c0010542c41c0001d0100b0f40d101400c2080041441c0903c0288620050450300300c80d0951010300b041d144034407102ca240580383c25011781e2401003154070254150729889000f0f200ca0003407102c034a47c00480d00301040400603968001d0606842c6004207420170040f00da001020031700c9403240d5001141c1041041040c0d0424808464030b4215654200e402583c7c0f544100001a10001d001002c503101c941c0a0103450400f51011259608094410000002c1401320207881a2081c0100c82d81c5644000001071003030401010700d401e10708184a00401c2c00410b211850b0f8401003c9040c03644801992402c04040d516071a090b0a5032200a140e09810341c41c009000c601c03d5040080b050186824 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 997649514 1250 997648264 997648271
    0xf030f33040308100803031315050f04170403021c03030c0906020a060b0d1a1b090f13111206010e0d150515060d0204050a0f1a0c1915 59
    0x801104005061041519900100d00400001c01282c4201c41e4241c00c5203086440341e4845a580c0d10007407035a0016512000000b1540305c0c1c21041184011000188980090741030000d840d0015809070b01c588010b0001c0d002100303281c0303551303a852043c1e0201c4001e5503004011640703c4001c0c100241e40710709a040e0840c0441d19005500807222f000e070500100b00c070031b42e9006100346401962000090141c01010035002000390f20803500240801640000da0311154001000034601020084113115a40c5d40035040541c040040105c20388030207003c8180d00c01c065a105500f0500000800c006003040049103a032000702041400c1c90080034104d00d030090310700366602d0301d440202c1c8040001540340d8003001000c0c4100c1c03040001c140e203115040305621541c01002188200d0329580822034941c00613816180d00c50340028107000519000c100c1c2d2000c0c16000030108162403c0150181c20071026800740100041d001c1000a14408100030f401118014919008148605441d0441c1c81403036103445080709504 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 997650764 1250 997649514 997649563
    0x1e09060f091309051018231e030a18120503030f06030c062205030d0302090418050316140d08010312030e0c0105090a0902040816060306050a090b0f030f 67
    0x42d0b8018a005141c021010b008207440100c0b201004020104262545460300d0540d400443c004403000040f00c070510136540d0f114011034083d90f00f040040d030b00d5a40000e4801d841c0c2501307221300006a03001c2d00d03030500b0482d007121115502d03110402c545910075641d42d840b5480799000c0000110156003d407100400392804e07a00e95904242c2c503551142d100c6030b04400203000c5030090a0070000ca1130040c28880e800e40000944550109003064214605840400e80000309200a0305051141c048103800c8080003c3c142c1c00542c0c5c5a64803803041013035180c05110101d602e8814400252021140740040b88112042d8450301c1c0d0700500304010074403081d034041c10641c501c1009076000e03000342100c5140d600d001c0c1000d41401d90040d2020b82140e400a90808030007600030a4451181c8000d1015201450041100785003264141b00381c48d04a401c001c04040c14180108115160500d114051350001280030928803140340104503405104440ca0f6454880c03000e10008602010501c0d0045555a5124640c0b80e032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 997652014 1250 997650764 997650799
    0x111e04050709300210170403200a1a07120e010f05011d0127150510140306012105040b040201030b040207020604090c05040807030c050102150c1e09060f09 68
    0x304048070707000800d009882c280010300d4081c05040d28240070741440440c02c008002030746c1541d80300711021000301e1400e01030701400e41d152800c403848000c282001032071860825544c400c030300385810b241050462001d5001c038410300e014004c0d8031120014600c0401c80030420062260103002c840c003002c0c0c0c450b4074050000c15070300d4001c120082e100e0014407014241d6442d020138502c04140301e2820300103403a000c18600b480e03150306015849802000029402e2070354200b20810503c0b480d9080d074002440002440c0300d192100c80e50640354003100c04d00b8003001803041d05540840340b90b0309160700039280d850602000b0801040800b010b000f5070003031380c04004095800301408200d100d0003801035440321052104105015031608400d01003a25880c101d170515a841004c10324100b800d40003101c4c400e01c4400103000b5541d0401030090392030600305112003076050aa8507428284075442072503400f02d45034190840c9102d004812142c1c00040500829540e600740004a4a141c000304030161048078004024404d56 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 997653264 1250 997652014 997652069
    0xa0b010e0705090114090a08100c030b0904060915110a11010608120310030b01150e0402030f01140d05100c02070e16081902041202030606030a111e04050709 69
    0x40415480e2680380034543c500646030b42c1708880003803a41d0403040040c4017954940c000d0b41c400400244000b82160007503120301a064900c142041800c15242ca01c403600c00307580701c070501508a50030080000e0320b0002c2e428980d4145040c040b0300501c85041407402a0204901d03c018001119507954101e07011400c81407040c01d8030000d00c00c06006600c1120141500b08600d001503070003900310f03048941c2040d90781d510850325403002d9020303041007001000c042c04010342014032100c04030001c0742c0440c51494140c681403030100f010300034512034505103a64190503031206020100529040400c84550703942809008010f0031784940d51500500410301e001403124070700009176026564084003124124007a4030212503009008101120743c41e00141144100d0754684000e001804c0007540f04411410280140b42c902040600800d020394442002c10003c108070580510a0f0340f0100c1d42c20040035042c0307450031300c3c00071502c60700e41d4010300d4107040c03001540c0c100402c43d0032a0b01e000c1803c20000c0c010211403918 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 997654514 1250 997653264 997653271
    0x120807020c240913020301031704080d0c05030c1005090d0203030907060f17092b090b0f040e090c032406040c0309050d11010501120213020703020f030c0a0b010e 71
    0x5816154040003601d0041c0c21280c481c02d12204041c280040100058000b0403600c10340f1001690010050061100701e1602c440540d2595841324030f414a01441956186203115648040280118000d42040418001c88444680800c201d410701704054242c1c800401e404e545122051245001c1c1600e007500120507203100d441400060003001d0711b04403094840ca21036109550401426440d9407005508280c1c0803070103400014010000d00d501c680c00302040e40c41550324541c00390f44c44502084202da000020b14141c65141e2003003501e8400800620020b401141c00c421a604581c40411444041c00921024801c508400311a48420301c03c0d401c000f0f8805003820b094040745108001070b4242070503008040803082c980ba000440c0e00e816103929052004a5454200080300165445200a024020f040c0584280e00400e40e11415543c002402400300f8401e04441503000b041078802d15009004406401d01d48038103417540c030300700807809a840704254002200d100600c2000400c820060003d110310 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 997655764 1250 997654514 997654519
    0x20d02070e1503030708040905070504050904030f050f070302030c0c0420030709031403090f0109121b12030c0b070206040c03023106050312070209010512070b07120807020c 76
    0x91141440015026880002c0010410300034410044849840c2000104030702c500034400aa1601d003845983d4003540d01c060720385d404020b0300784401d103e180e03070b001821500a685030a100c00d0440a201c400e80d454010007114405661002c51304405164001c4001d285145c00101036644041d0400200b1003215021401038500c038841c1340c0c1ca44a50350f0418002c1d0b03008081030518007642941c3c2d50b83d441400f00403010208064001040d45041350900354400700442500b400c0010600f03040c401c4c003010352002c468010700584008010000c02080c10a50301c4080d08513144188810106410080c00c450324540f070032182d00045a0018407154808503240d0f00840d4000070340d111851540d003c000095054404c0a0341d440d9604c0c40800d10a07150a414580070451060f001c1061450b02e4105800d01030307604840c410100d410000400140d40b090b40d002e0650398215800495001c02d9143c4a140c80429044414481c40008860040c001102c0d14403c00f1200d40e03803102003990b140701040740c403421190794407134 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 997657014 1250 997655764 997655773
    0x117014d0307140702041503120305041515030b0702010203180c0607110f09191a0904082104081b2e0b060d0f0506091009020a030b19090b01020d02 65
    0x28100e034442c542444450f641c2103582d40c02c03c07003e50005000c03284513500301000304582c580c04004205580b00016491406070408121030f1034161903140e00c4160072070241c41600d5887c00361021002a074003521000e56003107008441c1501d811800a07000354016103501c6083c1c040112080552400018501681d4a01400f00ea0604c0c81c10341d200005031019000640c0d000a0301e03000c6d11403503202d030701d0150300c40c3c445a1441c003584410384041100721240c02041c1b0030002800d03c0792036520f13150741031015001a032090040ba541c130129422038182841d2415400b215808030400c0c00107015202024000c00c0460304a00740c0c103407002f0441540e0703a0048521491841c103c12a160541d0321f003821002e002d2480a0b070010412190000c00240c555018050b80000c075031350f44c4030f018203440040c4581d60b0300803030540f02c845550a1944021000c10741620594410300d8000440507035451090b0032640800c5405000340707660b4100d65081c0200b07803401c0c5c00703012001880c1031001c690301e601c000f0301001c10740101d40150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 997658264 1250 997657014 997657021
    0x4060c09150f0e040f0c020a0210110c0d0c0305030301060c1a01081908040503030f1306090b03011206060e04150e0c010903020405060f09040b10080c090117014d03 72
    0x240c030f5880b002c075a2244d00c00c0e61800103d61000b49401111060401d550140c1581000ca10400503c200945040790800001402e41c00341010001501e01c000441181c071088412400e2800101c03940054000031b0090001000000343c164000f21454960b51013000e00c003c0c00c0510051042142030248141d0907550710119a1100c1d00301400c1e660320401c3e01450740745146c1512000820700e1617110600c02040c40100003803d140000080b444940a4480c916020151078a45209074070b843c0418020030640440c2008202d00700081940000020007034408482071924040c107107a0091481801860700b5142021601104c28601141e041f212020584071030344a5411a02440001d0070010900758001550010040032070380c4031620248154802c0080c4030072451b20711640050329020b03074480d000c654018400c903c802c0d80c0b100140c03810b50390310300e9000240f0980c1d11b44017030250411031194140c64002c8240600c45140b001040a480741c0d0002034580305c08422951081c0d0480da820720140070740c1c000d2000c0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 997659514 1250 997658264 997658267
    0x607080114032a0406090b0d02060a0210050c0901300b1203030c03011809020d06241502070e041e0f06290603060a090b031504060c09150f 61
    0x24903541c01c030140c22a03200d401518a6042074441012107100324006404448000d4a460301510002c0c0010f00d800384400c805c43c42c0401c00d04c03400104024030030b0b0804a40801c10fa8406c2160580c80d00034400d0a0060342032000580817564840440c082c0014841c1e0401c0c03042d04c002e1440c0250505011401d4510301128002190082c510902031a0303102c2d05002c00c0144503801000518020f140620b189a6a5454110034a0b18007100c400c3c9401c40700c0c2011011000740e42e481c405802c000d900220041200f1000c40740d186400e440032845941010503800d4045013050064046000350000f540845844a84480c1082c0e00c02c881140c1c001c21005880f01070a0b42100300780708401a29201d840c0701200b03110782c0d6413007100381e9105180f455207010444210f0119010410242c00d40e4181c240e5129107182800350201705494012300a00c0442516070304182e4540d14104103005040400e5282c00000d41424038240018200e5101d000000445001c008940c10700038100e04030544115445180071613040c210b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 997660764 1250 997659514 997659539
    0x1203111501050123041806240e061c05040204150b0d0e070f12030e060307050919090c120e030c0d11030904021606111c0e0c061605070806070801 64
    0xd14044410207046889044c00c0c0751029002603c00d0700d80742d0751640c00009130f80080301c0305980400784410b403078400c10080524807840110100d9040ca4041400c0f540e00d008206144108021200146034060b103169101141d43d000900070f51080340c0502c140350380002e44c9068488540666030001204121070f40340d03075410f80d004140009900c0242c0f21669560703425050704060541c0080c604103440c41c0300c101007646c4100e0301306822038119003180c25410542c800403d0b45c09146c01e440d002d01080700c022804011080140002410012018006a402081d00900f00183d0301182c0c1d00b45414642e0110103400301105a8031070032407140045c00c080c04101c0040310101c0f5441c80380c02a0303000800c1034a20603200c9000030080d48158001d90b0000c00c00d2443d000741103441f20212122004420b011101403000c003100907846070702c203500c00425034854a20181d400c1c0603111100940c00040052074030074191a41d40e4036941d8030700800c242c0b14a29510298151612070031203068001030310301c0b00140b2405030400c0307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 997661870 1106 997660764 997660787
    0x3040602061e040303020a03060803030c07020306060a0305030307080709030510240f140a09050f010e01142b0b070e0312070c14180112031115010501 66
    0x2c0e000d00035000c094001801c00d6000a901400107120303800001c081d040d11000c0d69941c0c00c0030141c0c00815071040d48100c1c06030041c0000038001d86020404081180c0d0040003442c40c565642c082118031b228024a486e00748000c002001c000304404005e4481c404003521800941002d041c3d9030009400460700d00d608040070841d0003032040f00209030400742107841c07070481e00403955405000169900c0c41a040403101510305030810001860f200c00860403143c40c1d082e290116600c0e2110b00c20f8144180c0340c0b4940003200d01c0b5076425400c2a01e1580b107400528148500318441e50750745c542d94450000e40e004000190006201c0450340f038240014800c0e03858444100d41b500f0201d6860890088151281420100c10000c20b2045a15400d01d040b03034010003480b40f12000c2d0303160b02c40000034080c1d042d4103a00142c0c0c820130901d0305050000700c9504140e000d000c010302580c0b8000c0112002441c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 997482014 997661870 := by
  have h0 := BRFrame.cov_init 997482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 997482014 ≤ n) (h2 : n < 997661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
