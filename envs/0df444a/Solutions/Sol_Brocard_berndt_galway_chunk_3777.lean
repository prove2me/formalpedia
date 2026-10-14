-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3777
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:38:36.925359+00:00
-- url     : https://prove2.me/submissions/82849bcb-2d38-4f18-a9f3-74929346381e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 679136690 ≤ n < 679316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 679137940 1250 679136690 679136701
    0x90c0703180b031608010e180307020a270606050a120b0d050c011d060306241306090e0f0c0f16060e0d110712140d0c020a09200c030c0303 61
    0x1c9030b4003c0700c3c26951800c00d5040000c2e103605c56030206048441c00210020b6540300c080030850264603d0b90780101d00d2100b44080c00243e5954105500240500360000035640181d0180410f40e0000c0e1010018403403070b002040242c60380150449240811911309600162aa91800310080c1007484035230703801c07609150246040000002d6010400c08007600c54003461044907450100403180494000e401c20810700c003040c0349080100808000203020042d5203a444000c0d14504165006440401c000d6442c06108100c000d0b0000400c07400f4003110081d94440e481d000014080441f03001c0c00c075140500c40000d420640e900740105a405858050b20800a08002c03030400c0c502500c10001100c000c1e00a0000500c03549006846400f62100124040e151075854000c1c02c0051400304401070760a03d40c0150b201c02030201c24002c942c82000039441c2d100324169a401805800c1005403c0052003514250800e480c0d065100720358540000070300c628543d10018203403814154041d10034401102e1102101303001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 679139190 1250 679137940 679137959
    0x603060617061b16050d08221b1a07060b040501080309010c061506030e060109050730110c0606060f07111908030415030b01050a082e03150902090c070318 68
    0x94011b0fa07250381c0d111039a1940c1c90450ba102012070b81040045000c42001c100007540c0354207900010400c4a0000002c95503030320b040818540c500c40384100c40c1d00c001404400c00059215001d030b400f01c07c3e5400c00c079660410100d10b03940d1040003000c606118040004208100300780d000414003480c2005000da0081e6945000750140451045601c0f290040d400046403404240c4580340c480c09103076540318001150040d039510002140380c001442002c0c0c442100c2110080c90050405c2c0c0310f002c0514035079031030b04200d200d4280440170300340d948038000400c000d28816823207005075403050303402013000a813070840640000c41082d280000e80d4401080414009201d44020025104541c0e102c81c1812505a03c508100c048810206646003c900240507550440384900f1515501210000c2110b14404a168a03419041107280d080e1500c0c801d0b02505104200c0e09850b0710114580008051000802c20317400501d44000c010a00e01c003240340800e0b110245403066011390480e40140310b001810540355249134 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 679140440 1250 679139190 679139203
    0x1f08031c0906201c0b15030c091f0206091f0209220606090807060f050306040f0e0c03160e010603051e0103120e0d0b0705030603010f0f0603060617061b1605 69
    0x4c0606804e0062070519038440c0b4080d000c80b81d00020311422402c051407903d0f80403078002428116500d1814004a60142c0792990301d60f04403c41017541d11103442c005040285071403c000e112280d02d42007509a068030510241c1100050000c0240c0980c03070307628210224101c2800d0102c1086482c80ea081180c0601480b90300a00944030541e5a1941e0251221384550ba550302d94494900061100140050b1092061703000d107030480002003011400c5032200141c2401e49001080307028040d04049459900343c68200b04418901d000b005482e4038183c40c100b41d81c8920003051140382d092581f5203000038490111034010061052200c0c541ca01d503540c480c00c01c1080507402d040d104011800b00825080030345810181c030b5086550140c044d10b950303940d481c03080703620b904040d209940541d00c896582c00ca0903458020a2050303050008002681c61440c113200c800d80300c00f54800402031501a460790510300010900d10ba201e000c05560103403600441001d000c0520800c5e49084c4241a8403601604002010603507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 679141690 1250 679140440 679140457
    0x2071a0108070b0f031504060e0a05010e0709060c0809010201140c0304030906030207110d0804080a05100b0d05070303030c1209061d032a0f061f08031c090620 70
    0x40700e6140e9100c00d0003e10f14490a48000007a0b42c0c103200141c0d80c2001113080707030b84803000500702207400c0707964605420341e809040d2524450b09481d030005001e40b542070b91001c0c0d841002c5191922141d80317050005481c600c04014007030002c4000148006083e4005d40144402d003030841d001d0f0003c0c2c13070600000d0410381c0090741d007140020031524002a20b117229009592030550004441040d000301d007010030801080c4080105d6482e0801c0c0700018659005116140c1c9040c019805041c804041c41d0480b804c4824541c1000c0c4103c2901200c00081603001901c2001d503a45030030001505030800d00196000400480c0c20a0305034207021040e400c000b2107410001c00c05085d4075031208140020403085d40c40c0d000360b00e41440c60a00c040c1501518425003503044040e21410000e503482c942413408540c0c1898000c0b241c02080b54a0f080c22410118840111070340204011806182030070700000d0400c8003803400c0080c0c004055102c000110900089912401502603242c421036803100002541301003d4021001d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 679142940 1250 679141690 679141693
    0x105010e0f060a0210050901020c07051807080c04090c0914011d13150816060c0809010806040f0c080714030609060d081219110c07090e0102071a0108 66
    0x505940201015900000010a0080c5190300001842041d030090074180003103110f01c00ca9014501910701c5010302502051002607a1800c00e007010302c0c501142640440d000f504401598485070081d1009517400c10078902d042c890341d465401301808603000760b410040340c03180341c00e100240c0d0703e41080e07440301124540309a80081105030030045d02c5200350303043c099a81c0e400400c0d82c080300d803501c02c4500c00c90f1184c5003400640d8110082900714107030420707004100f030740e0300200c1105100d04080d41000c0042c8404d14005a1460703059540081a000d044000f905000083c0081051642c45804c0002c0f105449402040040e1500384003c0c03060005a800b140482c4144090030f10520000003100d01c100d802800e2101c09450b4034042c0900103d074501d00382c589503c00d0001c11124a0705c108141c0c010703006007400d0440c803955152448111403803400780c02021309c2d0404c074814203440042a0740702101ca80c1c04000910b130700b441c10310701e0191040030301c010203501c180201c51807041103110580741611402c50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 679144190 1250 679142940 679142993
    0x303090a120c050d170c0c0c271005010e10020c0415051806010f0e0a051509130b030606040501050904020112020f0d02071101021f05090a0b010303020a1a0615071a04 73
    0x200d2041b114825400b0305116500000410007035070800300c610007000308040540c2c0d1420183d1400c100641c12094840120b4103003c84410400d230340c0e221814403a2071710b0896101c01d20005595020b0759507205000301c103002d10b80764080080400840c00050000341005090300318600e510300d000c01d207202411030b0f201c1e010504203030460314000c2c07003043e9280313003800064000e00701d081c1407408202411554243c5604804403c009540d529102c0050704402c0f0f51170f0410210301c81500e5420142001c80007020180103500e45401004507649030400190420780a0805460490a11011501a1180c1c080c0605071010000d8207a0180b081c59000300180d50080c2034981c5003103e01c0f801261540705035034412610300410243c180c040000c641c01940c000095a08a0380d6142c100c1c2d4581a03001d200364001d0b800b58210703040480a02c0880c0c030039510014421115049149420360001c0c890301d02e141c84890311002d000c641c10042214107501c01c00209080581908545068a0081840600b0380071508c0b101e984075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 679145440 1250 679144190 679144201
    0x20d05040b0f0d090c060206040605060103021e030603012909100e061903170a18030206160302150405060405100e0303072a150c020303090a120c050d17 67
    0x4800303803425250404949403a100e04808040465085010420549903440b100100010300b08108000201007507009000b9500d09401c1041c12070390003c00303103414140101300314105000e074a201034407035050341d15006460740c9401002c2070060000ea0b0620075600030000f030703031001080090f84010500b44220385612084d521440c80b075000700b110f03114006100c5c28150100300e592610f42c010311101088071200f00c9000e81c0e82c1c1c4601e03041d8004031000ca28a102e00040701014103600c600305001210b00d16840484030b91030344d40031511511444085a0803001c415148008262007844141000d41500103d0b00081c20b00c0c0c01c21584030b0009813000c480300d1041040601540b21503001c0c00c8060540800514190f558142c01940c00440d202c03c00c035445401c8801300d01500308000001c0e40c49600410000c0c152011542c000000c5030a006003440c01c2d58014010446612400108001c2e0581d010f84000029004240c0070b50f40790310032020013441402000242c1c4400c0e03500403e615180c0d41103150102064480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 679146690 1250 679145440 679145447
    0x100e01090f02040504170a050405010f02010207030c02010f1b230f0715171915050303041206021c0e01050f01030b04140c0a090e010b040c1b0c0314030901020d 70
    0xd000020490780300604814094540b0358011070b1701c180949074141b20510048504202c07913000c101500d01090005c101440b00d940d12074000c180e1031a441c0000c41c0380400e80c1d02c000e89003140d410b80c001c0c1007040f8645045002e501c03600900c120010001d4005900c14081e1918503016540d80d000e01e500303280c0c1c400c0d405560303000000e0100d903900180800f5060190a280715200e090300720100c80d2040c050100e0345030346001e0040c000c25108408402c00e47c004028581451400d84201c40c01c100c01074104808103103e99a008021039080300c0c025020b840340e0148a1401d000a0700502070000e51000f03c0c2040840f8510180e0440070400720350700b00030090b96480e40784841c1020002e000282c0300c40d034207400084c00249180040c8409c41151001c40303a04142d0180000c000042c07030341102e50056102c442c0a09074040074028101682800c4034180002d040340100100024088130b250405082204240c0e828840200c00b250f003d1608071481d020f8901c0e0702109599640e21052000b401442803180d4154000d21 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 679147940 1250 679146690 679146701
    0x2030f04140312040f090f091a071418060702030111030f0f0a0603170d0608160303080c121306020d2c06010608070507030905060c01050718031208071808100e01 71
    0x28178200c2c10024200100070b0002c3c507c00900900c00b5554000580c00b0580001d5001e110491280e0004100e28004000800305035090491848248017070221924848022030004c41081040ea00c051701c440190002a01401c480c20901042e42800024000040e4964102500c01d04c1d10903044034140d203803ca0410101d070190300c8090135007240ca8440c8040100b072071001305505411094041407603a00d4041207030925258074000d51410382ca81d03030b00700201a0003007022035001c01401e00d51818900420404102d10000502c4012034000d8803460310704100c0c0c1603040e47c01e203942441040105884812980c5110740d58605041001c40441840c69029440014214140d40c219a2032448684408200b0781d0f0a4104a0301202801006140803455449010103007100c0310402c800815141841400900b4a280c80a0945501c0f16140703c14004540c8141c0741012041c00c43c6803403420303942c0f044400c480e0703210155840c42400e200b80400184003a0000381402110070342400402083c2d0b20221800d08856 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 679149190 1250 679147940 679147949
    0x180b1b1b0a051509030f0d0e040b030c100c0501050126030c10020f0403052512030801060c060204080105070f0306061b0b15030303040f0506070908100c02030f0414031204 75
    0x303007009024000d90030010358544000819180c22030400200000203418540501008070b4143c0c085c41d41182010340c00114a07a100368285d80030040104d01e1000310380c680100090350380c02910710020b082d02c0b20384120034070000c0c01c0e0010000c000c02e503180d84111880c58580c050304460410000c64403080510040200c03000b1500f5140142450500c04000030069000150440c4c40213600303210020200c1e60910060390445801c4800b102d0b41c1e8520802890442500e410100e00107d8061312400004d803c01007403810768006051020594080d890203001a00ca15000f02105508020601030034503000407440c2e02c4819291814401c0d95119001290b100807951548058016024151008a50103c1e09260041c00d6842d02c0244500e0f0305010900d140d000317030345c120341241ca8038841506021080c420142c10000170729190b9800d901d403844056a03607001c81c103a40310540d40c6014034102e081c000c2048601342d0041c498817a4565039241c0c0240c1309040b0b4000e07802d000303009480c5110620b400700d4040340c0566 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 679150440 1250 679149190 679149199
    0xc0a140a1d0f22080405180628031a0603010509010209010c020105090301060803030f040516140118052107090501121217040803062e180b1b1b 63
    0x554070070002c9071141c0d1015040702d903000481e0700800c10381180e010043c0c00e80c0b801041070595031131400040c005030000301d0b076180a400d101101031191680d54501e10500e00540d83c18020740201074401080504040b5604c01005800c8400c43c84068641d8500400d10071001203000700941e90300c04000b10b090b4072500220300c1c001381e640d4051300015802035001d40a100e00c0034000040c05a04d42d00032a26690060303c020704c000550350100010003504010301d0a00ea140711051258541c9424034138002d84007102c016505018041450050f5140c4e8103905034024070b001411984070b4145002a001c200030902c0c9032008900030f444000c00e40003d00e0140328100c451035904640b040020382c440038110241411204204000201c60004440070180781074065406520050703682e050200c2000702010611040c071102440000c0800c2810321101c900504074100d6082c2005428051501c940c8151a02d8000c00810a400f00304030f40c4500b00c1d13078017200381d9031703203d208413501c0134074500c40c0c60041d5079001e210940c030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 679151690 1250 679150440 679150499
    0x31a0103062117180a09020405010f0e03030c1f0e01050606070b0c0f0406050d0b041e0e0304080a1103070e010e070e0103110d0c35090c0a140a 63
    0x1d01156030001c40c40240511503a24071203400d10380d070f950f040d4004940c00d401a07180076280c442500e018003c010081c09502c00071440e0920749000038240722016a005c205200025202c984903842c140b049803504456442603948185601c1e409503984080030340e201c502c075072030002003044680c01441043e000700001484c1500700b0b156640d0b04142c0c00300003420008421010321580d9014001b0710003400207480302d91940b84c0c0314100e10300107608884099150328410b44c2003482020202c843c5010402c82c03034520700000300d01160016101841c0d80b145601843e06442042c60700700a2010209011307415020440c142c41010789e803130204480000080c0950403c50311850041120107000f000c01561001c0103040114800c20369104003000c03034002d60a980c2940f0f03265400550126845440c1092070f28014952000051194540400b0f94401e0b200700341c4e5001d40f030780c0400c181e031303004001c0702c0000d94008040c80030303c544590b0a404180400f01e00315008860107600481c6403010300707000e40c0d600d05400c6141200f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 679152940 1250 679151690 679151729
    0x2121e031312020f03070e0a1506231e3c1e03070f020c03030f09010507110a120311060f04110f03060a020a0810051c031e031a010306 59
    0x1200c140b0060100e902058800d409040c645090165070010513409045450601d0300f0780041050358040d90b030103802c8010402c0280302007600010918070401148008010b901c240d06c650320380a11132800341cad000c17001d01414540100c00c003000040240007000c00c00300c6040046180b1106100901c8a44034051001d094100e00007104100080c009962013100103204490802d840c0c0c0640da4000e84403040007a07401c026451020f0303010008032040e007205400031850038280c441408058012110715a040080c00960b000074400c2030b102c954806100203000c1d46105075980d007142c200a0803660210086061200c1c25840c2d540301140d2540700e031540002c9a5007941d2580d4a0b030000161800c0b0a41d031002c007140e407074142910108071040c4505026200103030b48003503d04c0081d101d48030003011004929035104c13081c13105440720b000300003813080c190f60a64004c460f185030944000c10015441c9a080a00c3c514108403107926030012400c420072141402c506481941c0110162440c074041d007000c16100c0b0300c004070b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 679154190 1250 679152940 679152959
    0x50a0b0a0810030609030804061808030a24080a030f08011206020c15090d022b20011a13140103140a1a100605130506031302121e0313 59
    0x19800301168000b091240e481380d0790301d002c44003840c40a5000601807410803040000e03038802c40b58102c10f0580325242c0d01160341d481808d1448024142a00c0c0c50f1107103440c0051030030021010507901c13039000001c40e1841c0c07190413030f9035102042041540050350702003800312407502811104d4181c0e01041850006070b0525100c0ba4041c0d844213000c0a101d1064035803030150a44044070076030140c170b600e001030108800840c40c000d1600021550600d14100c2103000c804071072958074865000014036050400900803200d5144102c0d1134008916015942016200300f41407441d0605a500c0c1c1c10b049811032280d11810002c0412903102070b17901800342100078010b00c049071b108006100c46011030030031a030718402c00b0b5440c05603654841c42c0c03159000781c007202413100004605d60f2010290800e0b290207400e14881c0116070906190900ca0316028820000114107071150080c2c0d054001ca4020b400030071000180d900742540c440b06840c00c42e03e0500d90541c01c5d602c4040200c00c44104503d6503c1d01c0c1c0246060143c0e02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 679155440 1250 679154190 679154207
    0x903110d08030403030905010506060906031512030a0c0605310501060b04080105040228060e06090915030601060306060c080d0b0a030305040608090307030c1e050f0102040f050a0b0a 80
    0x4540c80484080268002400c03900203520851203a074001c40e1070b03c1545402829100c01508062203410f00384540301603910b50a083e294420446131078042d0802c2d030507012070b01144e01881044481d0000140032501603400401c4400d4a43c868801004155101e4030b83c1c51003401100d40c1d0542040b05c40c40108025443c100107401410f01035400042c00f15a150000c124682c8994084003841c0d4580342000203600d00107691404401207810000070742c8800c4801c0d000328801ca40540d40a0107852900e00031103803501e8050b1000148003801c90700440c1000c0064006800113041340074030911582d800808c8503442402100100d030000d45505010305215034464040d5040314142140c0d00390360f5140341c151581c5d07080d043c0000b54004e844d00750f0b4507400c000005040750002800901785a00030030801001903484a07142c03010540007440c2e850380c090104181d580b000010f0728003078040c3c4940041003c41d8541035000b0021100000c8016400079074030410300091294500c141c4419107000e108441c00903000d082072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 679156690 1250 679155440 679155473
    0xb070309090c030606080c09060f180405040803151005031504090510020405011d0303030610050705010912110a051b03030d0e0109110405040209010501121401121b060903 75
    0xc0a515611184088122070201c0302c8840069101c031400c0124540014103203801c0366001130385a10701460b00001c6001ea06c9404005007400000085005104040e448030109503103000b4001c0c00542014140225660001d442400490500b06035403800c9240c5109101600413054440500b19500c5100b1100e141601d075030400d412a0312002d550001650601001d41116000e103030050320f80e403e03c00010449180c409941c4103801e10341c921080640e40001c15a544000112201030451020210849140c06042001441d940c2003000160030006e031b80707814080c420040e9889802000841d00410360700c002d1604080d045401c0001e5100700b0a155140c080075025000d800c80307240500061005d030445002944030b46251359a122001e04000d01e00d0035041c00c40404031014011f5042580000341641301c1844bd1606000c5d58104510a00c0d400b90803c036510040894045081d42c0d4600d000703040040100002c499500e0704030201104034500341440e109a85c620782d116015a811075031a16003040c0384105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 679157940 1250 679156690 679156697
    0x30304031d100c1e15020301091b0504050f0607020d0f020102010b03120d050601110607080601020c040204051e150c0703060e160b0a0210020c0309030d030b0f010c0c09050408031515040b0703 84
    0x4d00000c5110107440c02c1c2c4140d0f041e5070040c0e0300d41c9414180802c49a20b07902041900030110381e00c0c00201d40c4041580e01b55141199200300b038904c18000a0a94418800000e4100c10f80c0007080040c812407441c1400c0c458000e070001c2c0585041c8c2c7c0109a00d6002908401e9210003051103038101c60b0087c2d601c80c0342e004106041416509041d80f1241d4640f0204a0b16940054440820003015503418088201c040c001950190300309410100000c7d50304001c031b008840365144044002c1c501e43d0320110f1a40c5404907551f902c41c0da4802144810303890701031034082038030040e06020407440c03200d60000c1c4101510035088140003819081c002040156404107064030300710b1050340e0102c0b02860807840180000102c0340000c1d0703681c1d0714500c241030070203d44004100506242c040240350350703259888404944407091a102120820624010041d0056504000035944c900001c02041200c010000c50090007103071021b812000ea04402c00c91000b011020240030f02c0000d0204000b07203020b031b10107401c07410b20905 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 679159190 1250 679157940 679157993
    0x70206013b0c040609050102060609010e091c0536010f021005100608060102010c080a090501020f030a2a0e06030a020c1501170c0604030809060c030304031d100c 71
    0x18022851280982e401d2001040c00942006a80c0e000b60903040202028005022180380c0031000078120501441342d01c1e00200307c0c1c800540b00f0711003800710f414050203a0b05100b908105015000b4950382100003095840c000c2444503404158801d40782d028900d01844e4001400000c0100444540310030180c041d09510036101c001c40c2507102805440d12132080d4038406844030b0314100000306002c0c00517103454196450200008000741c0d001e8481e0782e000c4080c9a01082e500280e1402c90300912582c0d00d070803400b0b071005c010300ca01446c05422540455034502c22800042d81d0031052850450614102800400c2d01c00c81d407035610b420440080c0d0390000704044010308100c007556090b4280403107420800081a180070040c44030643c1200c5445a02c4d00f00c0e001080e0302003440d00416070b0342c860b43c040981082401f05012a4643e43c01d800c440d602d051420031340740c0740d080a14000d4602044034070989030b000e40781000c440d102e0400781c1074204248056950141d842404d52030f41e0301d0142d84c03d40a0001d140e14403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 679160440 1250 679159190 679159289
    0x11b0e150711040b010e090403081504050f0f010f14010c14010905060937061509090309090c080f100504090302031309060602060414031c02070b07020601 68
    0x42018205540c019014030b00c0246103401000200c540c8030000905010000203a040d1175215100043e80c883c0e0300d41080303006c0e5116140c0040f442c030900d9035925401800c0034200862851115071042c010410300d090450740d039880b640706440c080081c0c014410780350118501c540352584a08400b442850051140c0200411603650342030035160000030554441d44031000b4405503880420484052540c500c102c40c0c001200210454001d1407001c0e103e00001001c6981c1800b230194071303445000211014841ea090701c1d64cd80081101904026400740c01281e40000d00060182550003220803060880d91188041e41d142d6203200850600a001800d2101e0584d401003460340b40d5200304500d0b079000ba002551182c0c1901c080c4960004560018484642020010084990002981354220b580111844450520603040303604c0e42c041c0119014240180708000740c5884266401058118010817215040e5a0340d81800e0707990301801c0c80f400c0011038480041c01c800302003000c4004682016108a00c400d030288 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 679161690 1250 679160440 679160479
    0x30715150b070c1e03060519020a020a0c0b0301140d03020a05030a021608160b0a1b080903160f2c0c04051c050d0302030718090507020f011b0e 63
    0x20303070040c084444000404400303020f400da28080090070460416a003443c090700d500d41101c00d0785c0c4401400b198450000c240b4005002c82140c0c03010b10305100454580841c40c0009644014000059554444640c800308606802404880c180c4030149040404440008244110191414816021802000b0440000076001e1008000152042d03004010706800c60704060303203002c907541c40325500398804e403503010900340c2c04c80c000400c0701c070b040a000740c880318500ca00f9212080c20884400984c0e00c2c160041003000318000c0500b036929025012143d40011454480d00000468064501003078130007407080112a90412100d03040140100f280388504a500c3e0480101d881c0c2541c0c02250304102180a000904100301c8000c404001107400d481e4022194031003641310340c219030f2110300b0190000009211140224000a2000d2046c6801040140d80d440c10700010325048d141c14006000d80e440c03400c032050050181640181d10404910b40304a0402000c0d10b43d000b620044d26040f0182e881e0040e400381e030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 679162940 1250 679161690 679161731
    0xf12020c0916030f2009061c0204090c1d09060d0b0f06010e010801030b010e1e13050607030b060d0e010605030703030e010f0c1a06040608030d02070b010611030715 72
    0x45800c0b00712000d01d0b03010029040d1015201d80b691243e1402851601081040354106060745905102c0d5079122150800324109100d411203041c0c003242420400064910030303900030000c4500091701004064a00c100c1251520052460307d40c0e044d14032581d6000516002e000c058000c0340003881c144040c003540d41c843c4140c040c1241c201e2801a500c10130001d095800c44c04403180b403c02480c09101d6981181c1e46d010000c1010301411560307404000001e041c80c030441111814022080312030750007505d40203000700c041d800c005508032428012200840c207214001d0081c40041d071001890a410811101c0c40d000003001046960941e56490b0000001d590701e080c040384001c0e40c00303645d030f280301d4100f40c40014041407a090403510401800132125404500409451401d51f607000111415584594000402a11940e08010554040041d68030404146c540c01030501c0d5200340c4851b00c25a0361408146c445107581080b460300f079001001400001000f80b540b500e814080c407030000845800d051103002c1c6021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 679164190 1250 679162940 679162951
    0x61312080c1312150c0807030b0607020a08010f0b04150b07023f0601050f12120423030c0102151b04170c0a0305210d020309060103031403040f12020c09 67
    0x103240f602e404091118011030400140d003001c106000d40365521100a01001c4014565010943e17a5190840329550b101c04440c409500101a90f00c00c6417500300d42fa0081649410310b4110600d414265541824180904605110b025007070f182028605400700e0f400b80d0103144203d1340301ca0541c2900a4200030035141d84021481e40b9020a5400c00342e109c805500028001c0c0042e89900400040000395102c00c0c021000503026207505099030b1030f1181c2140f4007007441a12400c40c0e42e021401140384481219040070040c4821084075a0f14404001d0644481c05100600d0058120300281e0a90114220f442c80d088540d2216a5105d440e11030b000c0945908140c10210302e0503004100a82c151800700400c0500346402c45c2c80740300b42c0e881c0d50f80746540c1d43c20f50841031040c10080760103c514074500b0401d4801e100c0f83e43d40b01b990759241c500712964881c0c1c000d0004034041440c602e04031308031560f04400d50348034941c071840d400b004070919210310700100502d80f4240e08503c036100781003003540c407098a52405207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 679165440 1250 679164190 679164209
    0xb0d021807020d11121c050c03061903050c04050402190303080a050f070903150f060914091626011d0c030307030818191103061312080c13 61
    0x50414410003418001182d03843c03010802d1440e00104005408601d0015070050901d0040e6524440e80c3e08a00c1c1541020318070003085d03d00030030800ca4400c0c260096202d00340480e0400100035941131040d03044d1400e0700028082d5032084a414015007410350085400a0000380400310580f440c080b98458010150400c0300040c078402d05001d110002c80c001e0b250031181d9482c0e80c0003240360100d802024580300e840702803c070710241d030101d0100e98580e074044020600045c1c07061000302d40300c61851020300000d0f00301900f031180460002d103000300007003001103450078540c400c118018501400072010758200ca07007509002e482d1000300c81c120003013445040d000d48080300c2d0702500b619009200506160000030b501d0700940040002c0c800080d44900c59030b6201080750805030310030301d40700c0300e0928100a588000711109511502c26092003002800004068411811507003280d885a1602207902c4c00c0c03a074024803c540c04403407606030038051003206034440501c0400d5410400a50b58021042c01c0c640e0012200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 679166690 1250 679165440 679165489
    0x4060b0f0c031e120646030c0509010e070507110103140712050106050406120f0e0d020604050f011509180803010906061d030303010e040c050604090e101a040b0d02 72
    0x1e8045068001e511180486564045800d01502c41d00d81150300301c824812140c68906034040c002c10360002c2843c40801801b1201c013640c503407500090121050064a00c10207940000154203024801e540b4071a0401340c0c3c6070707801c0205640e519400504401135641c14552110764a8615021213a0b81d07902c5111942d640006a08072200c40f101200c4c01130300182c5c00c10404010a000345504080f000c6052807142000054107412050b40b60020409043ca660183c002c800c2035a03070b980c1c1d00203078a80c0618015025220034070303000c4540908960b031059001009218450041100c0360655004042d103c0c0e40514141d96054280d548041580c406d030401d03d0030503552482403000662011401c4150300c07901c1a145c070740c41f00050000c0c0e41da020504c644440c1c0b00c1282d001400300481c03030521400070038000d4405134540e500d890b2000090f1440d902c080762113104502c4040245c00c62401180d02555000f140d00c00c6a50b481000d01001d81140508039030400b510500c10b00050b1103a03101410812030302c03915400c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 679167940 1250 679166690 679166707
    0xd0c0501060b191e050406110a05070e07120612030302210103030216271e05150418020d200a031511040e06090403110a050601031104060b0f0c031e 65
    0x103140c0703044130103203c1103208555200440d900081258107450003410001240755814603031034502040c0c0c0301b0040c0355028000000030009550009227004040540360b00d502010761403a450100c5800748a05943c3da0410400380010900030350040c15441d000c801a182c07040d541803000141e240081e0f1040380180c2c40300e400450307c2d00703008640b10082c104040701a032031780500c0da6580550050110f403425841d80d0300c035615040f40600740720000483c246e04d8410711103440c2540f04a47c8680301900000d01450400c3c0421846440302d04205420650080012503070100b10389038114841320145000360181c240342100320503030756002041c0c00154800e61890690721003803451001954a8064502102d031000d00050103400e130b0340f54510b9400306081d10b042025030342c0c41c2001c4940406181003100c89000d130304080c1090140110340d49060724040d1407030281040105040c0030807030f400352242590088050207040446000c642c02002c41d44e803902c040381d04149000801d6144551000100210040c00242e42c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 679169190 1250 679167940 679167947
    0xf060a050717161b0605090111070203101d07090608070e10090b0312030c0c0c030d20070f0612061a0d0c0c06060b040305010509010501080d0c0501060b19 68
    0x103520003114038229000600050b07140c850200080c26031022110761103100c012103403107403821240d40400c08546104030951820680300038081075400429035400d14500540040c44002160003642d0b0150060000102d007610000c01440c003d48480780034100c01000c00380c45141045043d000d01003c0000141d8640350429440c40c0c41c015a1003000035003616020446401d00740d94402089608586022941024100009081010241981a4620010083c0808011542e000c1d04041c0d10090440f00452681010160f80f5090190100300180070342c3c80c5540c91304004c2c075281500d10540c5084680640d00c941e01281742c00b075560444d1300040e0482c80f01041e8442540990802000d801c1c07146404d21131150001d080300c3c0710340080f0030701490300d40070708401c900c0c450b06d612082c11b80c00c0750003007090720340b203598030041ca501500c81602c00390300f00004244140341c10700c40c0c241210714031030050459032841c40090710840303002d11040c0d0315556226400030b10640ba60f0020311581041c01a044400b088081002c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 679170440 1250 679169190 679169201
    0x70509010e031513150504030905090f010320040605060705010c170601050a030c0e130218010e030601060c031101020a0305011a18130f02072909030307120603050f060a 74
    0x1a00c242d1022848214020003e071040b42c1000d111440f1035840055400d001c007210140c21440403000e86060200300600d940a84480e054940480782c803a8184c841051034034504000f03010151207200341d4004601141161000d4481114000c1d00120780f86a8981c0004d000e5006074101740d6040c3d44421020a400d80e1049a44003802d21241c0d100d50341e418a140020018000c43d81c051050540ea4641819000e0181202100c18000140031307031021003207401580c000e50041202d054852601103101ea81542c0038a49100c150f010180040074241c0c68540211400b4208000030750502040c4104801421007e0004085844513500c000c03078030703500d80712525410403246a68240c4c4480c3c107206841080d004800341e030b11010300c11134031071541859070701c02d10008080c51032000d510148001142002c104882c008500807103002c401864a1a8403202011440002107840d000160000c00000303003e6401342882e0200402141c0000940325102d0781ca0b80d140503400006801240d1081003001412000c60250 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 679171690 1250 679170440 679170467
    0x504060e060c0403110415030807030c03021c050d150b1909060f050a030e0f0d021005010639120503090d1d130e01050c0703030b0102010b090a0f1407050901 69
    0x4052415140d5101c02c0001d80d1045c03546845640c41c3c445030131412140e02e00000186411455403907440c003c61400cc1c10420118104070007500448560b185400e40c05031003605207140d540c03a82c0b442c2c0001510100000c10b18611038400401c400480400e0354034440000d004068220980c143c112030030303074a015200b030340513500c03180c20840c1440046010581c810144c0f408029241000304040851a1b4070300d00305582078040c050107100e248140291103078009480748040803010700400141e602c548040342c1d010448135480d01c0000c8040c00c0c103008842100c4a0303921020a04501444c40c0c5030a5507945800c2441d5040080055804818818110b00600804940880a040202030381071000c820810003200040058407a03030320f0480003c02c0c0c44540e0046103c89210600800007481c10903880950b40e045450f0640000b40740c0701501503030f540148260044444000c101c01100d6a0700b0483d48044c0c001c01802c0e5000341c0c4c03075103a0500303581c03150203995014901540382c10b510303034111178001407201d040d9004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 679172940 1250 679171690 679171711
    0x2808010f050a090203090705090709090e0f0a12050c01110a0e040618090201050d0903031d060405071401051e1b0c0609090402010203160f170c060105060c100504060e06 74
    0x28100095a9002010b004460000300c0240e2a40d41c1c10036064100640c5134821038000211004005181c0e620040309420b8698018080288502031106680d941c4251205000d1560110542c1c0010071207e1404440d810307414a0114641049840201e094402441c10049243c4020030051040c80e00150203811454040e60300b0041e070b503c1d00f2006000280c95008248801d030b5074454070829640310b4012100c004030400c10501201d42c1a150080c0101400c002c04840101c00c248000c03401880454024061900000180b01860400d8614600000001e800f81e05105080000c021803048070301c1c50388001c00d000c4840310b03140c448200e04132160981c82103185040b034100003902c109542d900e07000d03254800000c3da01c2c49411ba49610040c5d02d035100e0f8042e4242001d00a40c1310204000428006032044d92052514602c2c00190304a01c01103401544030400307040d04543e006001605104026011003025041160030807280d40d8240002c445060390700340d071060303111981c15162810821040e504200040b2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 679174190 1250 679172940 679172969
    0x80a12020613080901050706020403050a02040c020a05100525121505010c0f06091b030312020909060f031c0903300e0301091208060a0602010b030a02060f280801 71
    0x190806401c0210100400d007003c0400e165909034403400c2a84c20782c0745d10040c2103503655101e049c100c0d40d0740700c0d400040344101e04000c880000e483c0701080c07481c142c592010042c40002c40c140d001e20040d03c80101018200304d2280080d550000400144001380402901d417844003207084440001030b20320076110100300a49811017002541d1380050084001c50700030034821621401450148060701c03c040d001b07401c147c025058a50182811200d002c11244217844000301902c48401c030100307034042c22003210351111036107000ad030081c14001032141e4144401415600d00203207800c0304005030004034801c0e02c0003444001e0700b88100240b10100c00c001054000c00c40c241600e0000b204040584403031030101c104941c904c1006500d4900750016100036510006440d40304142250003480150105c415a125113100640021000d0040c450395a0b2a14007a01805039a0000c0d02448080d80c042060080e8551082080c0c001d40f0510f20710b40b8103c91324542c00e011030501c0c15200146000b00c1078000e0501c091015 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 679175440 1250 679174190 679174201
    0x20d08010b07080309031308030a0e0d0b040b04150513020f0a08030405060d060305030a2c130207020a030614010509183304080c151303081f080a120206 67
    0x1000740c49080d640002401c0d075136900c0b0005c040c154040d4907e500c02032a4940404125a800403020300000039065548500121b40c07282002422001c200015022000c00030129003c035030580d140c1c0b0741c824014513060745015440764225040b100e084403543e40380b0004529103c11854003964030004014200c1e55aa0184c1c14015001e23140d10891003101d1107004000f52240c00e0314601d070041001140c000b0240c9444901080d00581110032040040d043d540c10b040084010300400a103c0e10081c0020b402d000c800c0c141141400c00a6024280a99000e0428a000000074a2600501d2110048200c0f800384a526107403d00240090142070b50082c01c41d030701038485074140009214602125406c1c3d00705000c81c00301c0001d803c0c0441001e100824081000108002e01402000912120141004507075843c42980720a030301081050312100618800c0710143d00120388501f00d0241c0002c01c100c209100100020b8100d600040300340c3c801c0b0281e401c80b48081c424020601c441c800e41c80901d0001c2d01ca6450203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 679176690 1250 679175440 679175459
    0x1c0503040e04030207090515120d1e0e09010909020301181709041b030b01140a02070302130212090a020a0f181e09050109060f02130308070201030902150a020d0801 72
    0x100d00400c1184141d40d400a01418420020800201010720040142d403e01d4014120300e00000c0c03400314001c241c03035250003c0600c2d0004a884031001c1980e074000040c50340810000301c2b41c85440d004000c2110303000350001150340701104a4020320031500001000d1000384149800e4540340403070301c428203589128000201d01340310b040e81120040031100681e2070300714400003402008101e51030440068000c0c0562080e07a01980549454002620b4106a030780c0d03070b07491b0040d6a00c0b03164241c1c80141c000315001c0005040c00d07034218420714191000541040307205c2941c031143c101d040b00c60401c19440080902c0035401d045820034064400450356007141c40c00d00340380c2050b000321f14010b60721040e42c4008403c000c1c600c3d003102c000a40000078042c8202d01076410000e02030b048842040d04c02500c0e000d002c03000d0712407030702c219001000c0c0b411550034601d02c4d60b12014443d4111031010380c141034980e00902c0069542d440704860060344075520984904503d10002d00d085a060f1007070050100c042c0050114001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 679177940 1250 679176690 679176697
    0xc0315040506070c051c03050403020f06100b0306040207140a1106091005070309090c0e190e161403100323120721080702060c0a09060c02032a1c0503 66
    0xb03036424010a2604c0030714145140c00c3c1080c600c0141101c0300b107540c2c058194103410072400b56000b80e0807901a00c0024000c10340341e000a032038543c00f030201080100088104c10020303546c0003400034001410440a078580c0c0c0d00d1044540008034058005029490801901c000c104000c81c0d0161001410550b24101154522241b41200414460081400d03170405200d80c02c000701501c507180703043c42030f0742070309402400022982c45254400c0b032143d002c000186400e03001c80011250483c120040c1621001440180340030095080e40c2040055414501400d200070000c6008403c802d2283c4c00061031070901000c0d4031004401d0850100100710944800c820004621070404401c10000366107030796501d09840c06601031280c2c0c4d801825074100c0032946641150807544206a96000d4a02656501c4040c0c401485084084008904402400d00c00305100d40e1a02440c1840a0100d6034550360321181d11549a10001c0702040c924500f0500100c1400c1088499188003d2079425002c0f2040035911503840e8003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 679179190 1250 679177940 679177951
    0x8070609081c03050402040e010e0303151e01180f080307120305061008060607021210150b030714040b071b05030a08041202040b0d0305120f04080a03110c0f0c0315040506 75
    0x44c1c41d8400328081d980c89a200903000e440700c20007004898000c900d11901c81c0c01c21180000588a00401c07990642401c10a015601c642c204402070f41e0903000d001554500007078040c60089144c4260041081d500f0224044081c0c10b1803402140c651490307160184200342d6078499103040600b040240580c03515808806801a0490304140b1643d5642c41c000c15080c0c00b595034003075440080f00c84103800308a00440d8403621038a075003000303102e0f6500c2000c100250341111b01c28089540010000161010b1140713002d4510300011819880c0703002d503150b980d07407890340200d84259140318000701e0010007044551080382c001c0c1420b40140c0a42c22540d02c07006014000d5208413803404078104494001c5550381d501a40055400a29481e03103010141030080480c0c010141c2083c3ca40074080218940c80c4040e118076204640c01200c1c0c91828102140440c00350460508030801140180201683c100c010b108840f000c05046e80100180d900d803004041c9080e10320440d48410000420038030010440200b015944803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 679180440 1250 679179190 679179197
    0xc0e091c051803011b050d0b06030606040e04020607020d141501060f0c020303040302061c0c0c02060d18150e1207031b051515030d0206061e030c03030408070609081c 73
    0x7031640d280482d02405d00f0035410007004110251899007035401c40060152042c80703410070000d031540d0205124140c803064504652104050204101002e030050510b41c1c810303c041c103c00c1c100f154942c04501c55002c0c1c50412500780c0181000f590391000c0c10403040c5558070050b042c2e407040354580580a4a040140c180ea0401c22070900600025500c00b002101e000303560107441541d44040c18510190381c0e8459821002c082da04216410045901c1210b0781c4c01016001080c19260141300000000200815442039010000460300b600c0030910388280048007441c00c04020030b094801c1c45201d424000c0b440006000d42e0002c0c080b000109610130302c4400170036104041c1c00d004203482d09009141810741c950058a000009082141380120804002c003010f00545c210b0305914a404001c2c4d80320801222500d8004510305190103401420180c120300302e20010381542d20f40b0600301d0209045901980142c3c29641c0300303810800c038299002d03020500070409640035064100d19600241000d804140000040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 679181690 1250 679180440 679180477
    0x13020f0a030f050f062407170301050109060801051503040f0f031809050408040306110c0d0c11030d120c030207020411030105090609090d0f050906160201030507090807031e0c0e091c05 81
    0x381c042c988125044aa000302c41a02da11841a0b23070801d00307600c01d000c1c0b18005001907400060160113800c180b81680c900a000007805110442c107020281c01c010310940e000c3c0f202100f140003041450340f4441319203019641d03e15103000e40c2a80c6400440f00e40d0b018440c01c03480c04007007001107944a4182c400b540c1c2d1100022850078158880c0c824a4003c1140c0703c0c072030380981c0c3c0301c880241c0d03002141003070700b40c0c446c0440c20f094141302030030140c0701d0900c14904008204203017039043c2c041031a50b218010b031015600b401030030850075030041021201c40e119812090b41d00000140000c0c07a10000309a806a004c03615132044c0d2401d41051926003030343c4401441805072520031100381c4d40c01142070383c00c84a4054251a240c6620090094801d83e8540f41030340030030b02d44004107198910885031881962400801000c005156a807065810b004075002c0769070011200700c04074006254060303c5001001002090341450030504030700f50400396085812000141903000f5000c080c6d82002c251006092010f800095 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 679182940 1250 679181690 679181749
    0x6031e02090a240605130b040b1b0f0111070219030807030c031728060f030b0c070b0f09010506040207030e0118030605160e0a03020f13020f0a030f050f06 68
    0x400c0900e0074001c40380c0d0310f0001c4081400c0e54080041c020114080d41e000d8510741c2c7d030f07812032007252285010710800c0d00c00410240b1001e0003004002c105100c0654201c812000c92010f242c0d00f11100d45101510301240040c80c40d0940c544640000d404a103e0b41d05001514619030741c05c51a0f2098000007400d00041b5805901490b001d03030b00914152555005400b000d01d009006182c040f01f459440c44404850501d4404100703a2500c11603050381d28038003611400c1c03415611a515400d00060921014120030041880060741c950119070041e2020b060300c0c182428041a11401e60318001d0400340030360b00c18011032012035400900c000c4131900a080c00d44000340d0340700c848a00c141d07064102400c11424039052000c0040c00308407495400d030700c1c1d650700b103d203a00c424204000302000b448041c1d848060440012281d00d44944628404c00040900501e8200308501d41d0300980c00c84071013800440d660700e21542080c0f0460150710f03480b42c8420300c030300142c4c41c4c140c0c002483c001e8076000070094154140455030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 679184190 1250 679182940 679182971
    0xf0603070c03260f0702060a06050105041e05130204050a140604090c020a020d140f060606070602090a030c030f0b070806030a080306030307060f2a021c200106031e02090a 75
    0x181d040d030f089200c40c0c1e0310b0700e0b0205110f00c95103002d54038400140318940000360004114452101911030507501c0358501442d000051815a030022408503450b8940800010140e503100004611405070a0b009a01ca07494901002b43c8106154000d804901d04d40f100e4407281c4d940c603400c40e03003a206000d1300041d800b401c012040740f5000075088003d40200041c146c1c141800000f0702500403043e040b40450358441d20140009803111b40c141c0714a50810300600032000040d140d80c0281610700300140100100c59aa0f4a034217090011944c4159412040b0103031402c140b02900d00f000b030707000c080c50030310920904081d0046952070000401c0a40510004400301c2e1403541d091080b6201681c00c040c0a028001c000b02a000c000e042281009a007110004501000d02d1003030102001001850b0700a40100d503030101c10700c640e00ca00c10700007d0070850304442100003031a884600c44500040503000080640c02c5142c001c410f00c105486070000c0300403a840da080142d8400000c29840b411105000c00d0304980d643c25034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 679185440 1250 679184190 679184237
    0x2060a0f1404060b030d030911040506040e030f0409050c161b0f0e0906010608070225050405150406080102090622050d1203051e06010e2206050f0603070c03 69
    0x186000d04144003804144a0f69820088200400303c042d600f85100840703044d000c03a0f2100702c004200d00d041c07004017846031509500c004e901c0300015001103010000711b2815400c0d0350214940c8082e01d500840c0510010f0300c0d07403041551100d0107043d250720302100c400e114140135030750ba00c1c0141004484005901e40a4640030ba800040c03c40c0d505011041d80c03101c035000c80030301088460882c40e01c916400003c1c1e0510426480780520820f07000f600c0300845a800c2c5121170443d20801c480000c0100da00001c00ea100c0d486124810080c01000d503145500d180c042200380c46e100d80c0802c1d2581e006000d0903240782e03100000c46558241c200203080e29950000c0c002420690190320041e40003e01d0b204000500c01103010f070085850241c0c0c1c0070401980c0311f070114200c0b071030249920842042c0c0c620000b0b603d54000c07043d01030b4806008000b824003001daa48548000310300000880ba002c0e807030741c2082040d814800007501230f500c03048171501d013549046100201032190a10014040001c2e40c1080600380b4540c0503074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 679186690 1250 679185440 679185461
    0x40b03070908010c11011a1c030e060d020d050f07090b0a030603080c16060309050c0103021819052d04021e04090c1d03070b1b15070f0f02060a0f 64
    0x203203c41042c546003e4001d05c11002c0ca881503500381030920340402c0551020080c8210001c1c80d005800c8101d0200014501410178100c0a100540c440760a1a42c2c4100150070040b00b0414052307038501d01120000107448020b081d0a4100e00c0c96400d0003000c83d003104d40d260945450310100c0f511104400411006045c0c2644094114000024100f102490102e400603050b064419020724441e501e4104a046803032543c00038200f5000f88814258940c802c0c0c000380007400000e01480203007070003400000c0a8030030543c0710714804c90050f113003040f550034442a451611035007114007500b01850090920380d0440e485070b12600c1b0341d03400246926242810160b021800c8642901207890b191241140401046000704030804102c41d0010914034038880110b014070303102d0180180c442c40b4035020f012200c0d40c20070400d1005141c521410b00d000c901040020b10089000c070110b107042800c0c0b000c0040c0620941c100e503d0100526011401211500041d0154102803044c600040a00c4608200c0b402003510f07009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 679187940 1250 679186690 679186693
    0x10509010c140709060b070c06050f04031a0a0501050f2107120c0e0c0f0904050a0e01020c03070b100e0114040219030c1d0a1a09030a0b07081308040b03070908 70
    0x811400c642c40051004240d034046101040003a441e001c0c074202d14000c1c454010303d645507401c4280f1526100f680541051020404254101502c81e5500c11035041640000881c1016600030842c090710345010741030062400366408141e00d80320402040e0000707066000700c61403444404030880c0324a0200300030b200403e102050b502c14441d05181403085030105203d81c50800c40c48038081340300240054100c44201c05018000307841c0a003060148409041c2c02084200803540c2c0e4441000b9004080c0002c01590080034080c43d82c4a0061620301d0072044098510b90503000070301d80a010500c0d10b0595181520480022809451111000074029204200a050040c00390070001c500c01078240d0020340010895031240710b0034180060720030f00340038000403c41c0d9000049400401079082c1505200c00c44001d050200ca2401150001181c645009004200d0b01e005020302084420359001502a40045200942c1e050400c2d4a890320500390145010310704141e03000201080781e85010b2008070380100702100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 679189190 1250 679187940 679187963
    0x6021b0313030b07080106050403140c0303040b0d060b1608030c0705070f0e0f09060112020d050303090303061e0904081809071806170703021606091104060b18010509010c 75
    0x46064507140c948000c4800c0e0150102040c0b0700c60040c0344040c1078502c1595400c2c14649591140c4545954a118010039801041d4034030382543c074140001c01c00380441400343e1303a482e4034011908003102c0031503110300390810040c04139003c0400640803d1f02140d401069441d1603494440922146100300781000f00ba91140c0f40e000920700c407008041100700c0d581d6007800c100135a110fa500d03001410307040350036600580000c4014450006000300c0034001d070340043c1c03441c5a20641669154a954016140c5130103a60021041201034601580304512000c2810025861a0740c440c020601640e0040c100901e442008110044810114100002c076030b4002000241f190400240c05410900180d80360181c0f0f41151102041030380c01f640d040700c1c5044140c40f04003034075078450a0440003500800c1045800a03444034164011810a00030980514001c0200c910560070b0403041008403900d80c3d0003000400c10a100da03140030113404000c1c1c0c0c840352003030a0255132001d606004a891038008a0300416010788031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 679190440 1250 679189190 679189207
    0x909060902090a050423121819030323161a100f0e06120d0302031509040b0604051f030f0221030a21020a030906111606021b03 56
    0x503001060040c1c02a0350031440380d122110080141c8108940280951410b01003070000b00d030842c00700401d00d1200380f0a407400514001c0c0c880368a540b144401392111100d18084802501c0d0144550944440c0c1c100000d19461030b5540140445040000380460481c41c03e43c401200300b18802155019109030b104040407003028503042d803c039100340541d2503812540c200001d80701c1100350840e01c103070341800c03d0010500345400349183c01c000d40140043d4218400200c0e0002d458410040720601c0c122944002d40c6a00c0d002e4032014294068149851050104006201c0460030b151b01003034110b00c081c1c07404142c0b591110b89040c56502e0501c100700e00c0c8038a003007002003801100c1031600c505510031220244168a9802d04540d1011802c2c1c40a50b0f81e0000c002c41030000d40905402d0000e0f0810f1250030b07612180d40c0a6900480e000021040c02090b1903007801e00c00c00009102c0c40082841d12808142060003e455a60014400ea00d00801c3d403a8001501601440b0710040c00d06d8940f20368044070364a034800b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 679191690 1250 679190440 679190453
    0x3020a05010b040203150d0611070b1602070f120219080709060b031509070e030d0819060f05061b0d2001180303021605060106030e07050126100909 65
    0x240019241546445080303962403906000b10780c003d421075210070a1910321217040007480c000d4408111000b6651301c0700c00c0030761407166001c0c004560041002c041c1d189400f00c82c090020400c1c5a0340011504904030511071b08040e02010310944007a5095403e042c204d07440480d003900c0e07100303404031598416030300009100c2c0000603921090325000314007400900d503105650a000c0c0019140d00015101a011040c4142800110641c1c044918a00185d071103245402003030800b00915007550000d0b11201c00c21000e10425801d00701c1c0003440040c208101c41c58400307924054841800313172030b115100c0000c24400d0400140e41101850013003206540c0000d0f41e241c1c000c1c08035040001410058130003101e140300d0300d000c18420551401c681d01309018640800e0340d4200e0081d8405c00c2c054908008a000b081c01180f0100803c601138002902c0004402074100c415510b004881c0d400681000500810580500c0e41c40041c00270b05141d440c03000c1116282c1204003080c4102e641c10043e83c6070f2802d40302ca000d0062 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 679192940 1250 679191690 679191703
    0x304170c043308071406040f0b2a060f0c1308030301031e0302030a120e0d0f0201061403070b0307090806040f020907050403020603041b0504110903010b01051c0e16030302 75
    0x2da00300740c01402038000c800d441c01c8282e11400c0f240d6003186034100001006640356510700c0f28004e080c540790071b40b188a04a0f50034880d40214000d504040703003407a50494440c000034500b400704849000c2010020342e501d030340e030b030700060030b542d130342ca140c4802700e0726039008041522001603202c070218141c6916544020ba90760030910042d180843c1c4014081e00c100048c68980480c0354156000e54900100c074801070703a00700202440030b4855683c0c3e800142c440030082c4548284004e0603500c0e503d0604401c0002800c0d611690800001111a14400e0b88103590015101044403c60484680c41e03a4888e00c080d14441441c5d4800c0c151800341c02c00700b108120300c44880c1100d252007205c1c2d1002c1c81e102c0400c200c81038011404000d410500c00c20100d000b082010b00e44013030542c6442d1482c1112500c940225054071100b0720110300d032460114810005140a0140c00c031024000e1038564184142a0341d140d801039071048503006159920888401c04500a0045161804414881549440c1d881c90029641c11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 679194190 1250 679192940 679192991
    0x30c03051b061501030908040608130b01091a03010b010917010b0a0b070302070602190303020c0f0304090f06290a090b0f03041e030f0e0135070206090304170c04 71
    0xd0400c11903c015600900c01c92030515041091a4142401c0200556100300302a01443c2c004030484243d0000804800459019001808000c2212901884e02003002125021414400e0341030004040190341d01c08900300c2280c0032a5820310807089007242080c01440200905600103803111004266801c5240041c0106403183d4211030065585d0035049031148038110454030220801010701c80403a11980290110139804020380d034141c48a4013905181d07500a0f84602590342e00e0350703e9651900f0b84d5126a0004290486070300c081820032120040d0402c20403680561054804599500c00b03512440c4008050b00005054958036903c118501410303400444040b1074405121003400190202000741c450340310b0741500c03800501c0a100100f5901505e901c0c20071810003240b900c92800c80c02c1580280d1705400720940005034000402402440121402080b0400b503500400c24080818000400c40702240c4105207903601349007001d5421400c040c04507007400d90281c02c1c41d50b403541c4980d03126140c00800c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 679195440 1250 679194190 679194211
    0x1d01120507030b181c05030a020d021c0509120703020705060304050f16081011032205010f02090f041a040c020102121806060603040b04020f0d050d0305060108100503120901051902032212030c03051b06 88
    0x401c880070704853f0f803151400050050b045202d0802c00d078100074010f0340d0854400d0056802500149100a181c18440c211454245000000401c00d40901348180851605100e0040c00031020300b1140070321900c000703414800110b130341d240d6210340200107107905255a03500074028440b204003012050080c0d04040c198a00c155082001e542032841c0901ca0f174200480c0c00206145e0464600d0304200c003c1180c10b100b0419550200311070040030b011529690b20403c03002210301c0d0786030050031445141503070061000e4007451042046c84045007020003251750080e81103032462900c03c88600801c8a075080c0040040044c0b1500810703d56032074054000a102d4142a070303a030b000c01c0e030b01c0002c0d44a0240360380c0f24a5425030232070030b4050740d001038040040030f1144060501031f240c00c1c0c00805401b60b0b540f90252100058101085016180403c5025080d8005460818801142c14410300c0d40b51040c4c4083c005040c449010361081c101401241601c80400a250899800d040000f001a40702c10080700c401c0d140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 679196690 1250 679195440 679195453
    0x10e13020a0e040902011b050309120f06010801411e090105130f0204060521060106080105010f050d06090e10061d01120507030b181c05030a020d021c0509 68
    0xc0e420315101d1302d1901e68059598031950440c60b142501c480031540029035441c001041642d5080e02c881c42c0e012303040c41c1c107800100480b844040209040c010180c0150010b07904040141c7e281c4104240140354102c00780091040707183c7e9203007607141003542c4460028010400c803410885d1000841580c0c030380421000c0300c01030050769008102c6c3d01b219403c4483e04050002000c6150211b5000356818848a2001d0300002c1ca00361610000388038040601c0c4c50100818030440b028a0b04030092200a0040142d0b040c480ca495041c01d0029003980d070b1040d14001040700201c2e040d140319401e500b1035001012030940401a641c1185011074856658107880c12007181804000226902d40c186105c0401d0751f4101c0719105a401c0c001d2000450f5000032041d110740c400c07002c020011a101c03010041c02030020a2036000c07041040000d1a0503c041c40a0810703000000312842c060b410741010132254020101030780141c0e0b0f001c000740503800030700690b500104031220880401d069a2010b41c4a24000c25448044452 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 679197940 1250 679196690 679196717
    0x6180603020f0114040b09030a0203100516080606040b0703021906150509011202090405100507170705130b0a11010e0f0c0a30020607030e0f030a0308060f010e13020a 73
    0x641c61300050b120303288000d0811042285240400c043c1520990040940e0342043c407e4000038680355841a00d2004d0581d03580078840b00da15a00245040000c860522001d0707850210005409800740384501580018001800c2d4101746c030a01c003261940c1c1c80d8408600c0d4130155400d1120091074410f1f00f4140f0f01036806004600b03443d0401c3d034141213650b04600e1134107520803a420b100d131140010348212054030522000050014203400b03810310514103a0b80781203020403564003003410140083c00311400c0c03120804c002440c44840800060a55100d40740d9641d071100c0002003294164011002c4003000c0d4a040f680c1300c00040e010401c0c070382204440c0c08a0307003400025420010359810728484d00d4501860602d0b41c00c0402e0364402039001c0080006a800703840303080d07500401d0306030303000140450008851040034811484c2c03e8051588090064000b0a031242c03181e980a051804060700da0f600c42d04802501d080a45c0c41682e4005003014003504840800314107000c200d000c4c1d00004000c03404905808050f14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 679199190 1250 679197940 679197947
    0x21091c02070509010510050f0403060506150306010806040e0f030a11060a270c0f080606100e01020d0e060708040f060201230f070c050316060e0c030703021306180603020f01 76
    0xc2500c4006058803d140d02c0c0c4810400031141c2c9104400600009000b088100c6c0d20007409440114060840030609180c400c040002d100c1070203002000b5204207000740711460341c0c440e941a07030019094a00164440d19070010074503100c0b641e03d45e03103c0d070301c40000e054201590150611451751800030440b1408e483e160380c660107a4218541c440150040740400980700310307646414240300d5004404001e440c0d0780b1031201c0e0705884056040346203941c3c8900103000c15400c10a40082041905e89000d40000c6800350000351500f242030301810400215503051369860751070f441100d00c0968004201c07503960390745183c60a580b407954400d24015501e00811012402c11100e00804030052484824950b41d0340c0050408200d6030180c00d850411961740403000000d00304000602d5118040502c40c1003810013031502d4425691803084100554000042d0720200361400a0101c2c00c2d00d0741120300031603424540740340c03000408040d44511442c421000380c01c803460110398030cc00c0580e4025580d21244040704401034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 679200440 1250 679199190 679199203
    0x50301060b0a08090f2d0111091c0206092202070317090c01140d090c0e060f1801050103020a0215041a0703090309060809010209060d02091c08030103030521091c02 72
    0x150b01c0390050b4000b040f110620480b21b0b4034a09205070440201181c0503803440c00c603505010b00c8c2444e404002420850381c602500c044000000d5080c5501d4107c0c03403640800c11902544040c0c1d8010907501c017801e07001944504c1803008400941c2400c40d00d81d101414001c1100c584411160402100400810b85001c4045100d19965006071914030403c0c0b048200c1360850340c0980d040c100c00f02d54075041140081e00c0c0c1240c4170020030707254141c4909400e00104000e041e5844003192441210181c4c008030391403494104c40750440b602400c0c01600d50a52502c140d01701420a542c8544001d410420042044100a00085250540320355880d1030740ea800303030640464100320406400b0603d840c03001c0010b1403203200c201d540505039100241c01c0c080d40744040b80241d0000407588031000d4001c00d6849090601e000d000c40e216080c03030214140b00005441e60042803106010240400000141c040305404248446012261f4409100101490b00c2000951541482c80c007510b03032807040c4011924103500c0050304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 679201690 1250 679200440 679200463
    0x5100e18060c070218040609060c020d020a0b06030106170706030506040902030a1421041406090604090203040320030309121e03040213020a05030117030a0804030315050301060b0a0809 81
    0x4000c10786510001040d03d801212040307a212000f2039201161140e00c1c03500502586c0f1841c8041a07903095443c14105650450aa11003150b003e04146202d5690001c0c0716100b554124482100e00d460f02c801280c05003010750440010007000d14030b0104100800100a0200e4010b0b603010403440c0c5420042109076a1004400380d80365020b180302d080424038407501010500d620004442a125690309080e4007039040d95500d21200c40c0118041150307103d0380240d45450034084400c4c600d4200402d00090f01da00440c0107017100654040005401c15004800031040342c44648035011500d01102044d41d0340780d10448850f00b49000c0c1031400040082084c007a1400e1a03203200c00c6000241051003100520b03000180240d0b8000c01c03003181940d00300e1441c80108102c8050340e8a07659a581000201d81307000c41d1440e14801283e208001c02030b18180c1c0141d42541041c0d2600c2d0104101e800e41d0300c0d0008800302b070707000603501d9481e1000009403250984000e040c6a42c803520f80c5850759591400e03090316041007426 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 679202940 1250 679201690 679201693
    0x9020a0e060327010c14131a0403080409020315040501150c060b04020408071d070e060f091206061201020f0702010e032806051f0311030703020405100e18 68
    0x101589031900155602901c01210a40c00c41c48a44003e10460001c0e80e000c2c1c240e941d119943c203200e0303500450070130f030306108a84d0041c074002d4030803a542e11001051142041d210004a0304140c00d82e4490215001103400c21502900d940d21120f08000035842070780d4800800000001d04901400c19008290480c5c4121200c0c100c0f0203110309041d00c654003c0e400c201c510030356074030f9441295500c0c1c3c40030300701500c50303031004008031420b1000650390307060000e0015503c1742d50942004030755035111005207000c0d40250b46440c1c0b5501c00d101001d04a001c0c41c05d5180d4880051b10807444412000298288104012580744a200384a000c41c40e08034400c0155064a40208114a5001d540070300c200f000c0304a40601180c01d06980d820081e4403000c50806449002c800075211042030103001e02907030b90011284040b20f42801d800c0c5034541c4165841e0300c401060b6819020100c03d1940d02072018500840c0c010b4420b0101e4501041080e5881403140035a2045201100c003281200203420301d1804901d41c1c020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 679204190 1250 679202940 679202957
    0x70c0602030a06090609050711030711211506030615060301090b0604031401050901050a060e070809100c2703020d030c050a020a03140d1d0915030105010b0409050109020a 75
    0x884120280d03000901076090300d510f900e00012051010300c594002450b4a010020341c81c20f1080303004004039600014034095601c24099a00862120441c50007960f001301d0384c1b45003544601644c0200c03d0030a8008111902030000600042c0ca05416640e00c00c0c0c208a041d510682d50750b4281242007081141096041036040c401441280b84070352000030130000041246052a5980d038038420004121000002580d440702c00740711400e07809004482e0000b0030480140682c0b81060200c00000c580141031504100c1c4885c00b00d504020140145804035440b0a41032200342c0d50480040e1a5081500c209010041300c0300c2c000301010803c0f461130303055903030007017845001c1c41150b1000c84131010030380300a840c640650814140140d4806a04000452081081c8124041d015100b02c1c14480d2480c4a1010301240010081c9400c800903320060a2002c555406854540e6507080b060000d40200d40e9405600e44400405d0b80d0307400e10040c0048a113581024030441c1e896485000c16800b664021310041410324 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 679205440 1250 679204190 679204193
    0x60207030b060f1507030924030c17070e01080615040e0c041517250f030f05041a070216060e0f0312030a060e090a0f030221041d070c 59
    0x1d801c8940050004020701034034a40d15000440c0700c964164003c035041c800045a03803c00d81c000e40d00318002c1c0404088801d091404503203a007901042003a400042540d280501e40c4401c0c0104803165040b1060700d00000540343c540405005c40d440182e030940481ca048000441c1485c2070b22600803070103648942c00b400d140c86e01096242401000d440c7c0c001544007408041034118034882000340c804002d40c1c9a00d00804441e208203040c0d4000b8280f1103622030403030154408500000c10390341000345240f410001d0145a89001c4000b014101d40900c0c5041c184801c0c88103002c0045980d804070686084000704944810005994a42d140c0c141c00258600003001040564003c0c1d920a0b00c1c0000940118503290100002074105032104010000d03410003c0184011200103210f520081d0141c0940213001d0305006030056a50311020300c0007808901060b540c1400c141c0700344400c2d0ba48080240c200c00c40041c40141c40d0309150428020140d06000302a1850502114038000e60b0083d14541c0310100b010405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 679206690 1250 679205440 679205453
    0xc23031c050f03090606010909141513020d020915040303140f040305010203070309170405010e060310030f03020f0d09050607020904060204080a050312070f0503010b130317030a0605060406020703 86
    0x12522403009011051241880341041c2c02c00841c420b0130310402034126468088009820b801290700312180407850031344240815944070584641151140c5c038543c810103008400507a42140c0320031401580c50001c14000c00e0a80c09070050706494204643c540b807680c8030340c1c4140265005604c03018000400c0002243d80f1400c645006100d10541e540317030145405e889131202d07426684143d803140c3c00607540d079050b00f080c0000c2c80c2c010020381040c0034103d072900346840c00080ca44120008541d02c900400402301c2c5a9451400550006560005180d542d030a01403c01070348814500a1280c0680900340c44148618492541e50094030401005603003051101e4007844a24980144219841da500b0070002c2044d2004201e05034003a0700c200015a43d542180a404025600c06010705040c00310032981c8800150f0450190781c107589281403410346400154220705140d02b140e40c0090301c0e00803400c0014000110850085210b451050800e00415a44509100f0240310320300c180401a0081d42040c07002490 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 679207940 1250 679206690 679206733
    0x60a020c0a0605090f0705031b1516050a170a1d0a0314030924250c03110915060912010e060c03010f1a070204020d021201030c2303 58
    0x440c4022580341201c2951030204845054558160550150080c3c10413441d08000708005000c05401800700804d07040c01022800003d040a544a140040c01c0503007a603042005036200c1a0302600b42030107410039810626110088030500b61a1000329202206108282404071032241c4881c1c3d5844042201c40c801c0c00a04082c0164196845180360b07600001084102200d10a03040081000d1f41e034801d00801041000714041141003080000c485003101c4584c0c0c96001d48010b10390405148000702021180c045641d005280010302900848038044103100312407003d4403118000341c42c00902902e1346a0b50040002082403800d5020030100617202c2c082c10061144480c0886c400c1c00490402d50381003441c0c1c2880c104580345004000d01000400001180350020300042036012074641101c4285204c00b039880c454070f00068066600050220381031342c160750403140385c074182ca1140b4080e940c480c0b40c40312111859118903240e601449030103140b00c80c166016841c2410006004001c1c954030550086031494 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 679209190 1250 679207940 679207957
    0x1104020f03190216350c0d020123060a17070609050402120a0f060513020a020c01090b030f1b0c0c01080a0c0806040917031e0c0702030a20060708070b070c0203060a02 73
    0x1000307005c00ca49000541c04451010a1a030081c5900c0d030140d9001140744c504001401c0c0110b83c18900c03400741d450030000915110307081600300782c0000c2e560300c0041500c40f03886502c10341d10300400d001d0016854801207462000d5841640e11400c07401c0e40c501c03c01c01a40074614103003a29501e1a00030502080c510342c802554602c10f1403000c0303207281d80c0e0310020303450b48c104c02d10034143e59400242090280d54144503270515a40309081048c0800d041070040241400024140c0003101c1d040808143e5120f4150303070820b0000c1e030001c402d95945800106094075001e42d4112140403074505800714045100d00c0c040d05412144640d5003181c81c1c2e603a0360410018060080c0c0648903e00003015000320301d104880210701c0380002583c206070513006006c18070f03104503004006d000c2c1c01c2d809008800050340c010414009864001e000c8031541c4c280681c02000e03142500d202d1982c0188000b401c03404100102d005040d14038000e22303004c0840d6540000684c8d062140c1c0e84000c1d1301d40c10000028010032600d40c003424414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 679210440 1250 679209190 679209233
    0xe010c121101230103060b0a0b03072a0312060602060c2502040501120b060103050f0412110d020109050715021203090102041e09200a03091104020f03190216 69
    0x4036800801100006110f1107154005000030042c0140b0040d0b024880c4c240c08181c0714071098a1030000c200c603032404054021010415540e1000e0200c82c044075892600640304c1407442040288d81c60054548100c402c0b000200e81c0c00d1003000a031302030002c41c0d090b01c2121f0740040b45140010f11010043c041c10fa034090b030506c500300341281d880540c4461203407a0203070a040c011101a82410701307110a00540c0244902d040508103820403501c407507001841c9401a91208280302030842e800400d95130524a03000003103052140314070b103184041c0c0c15002480c00c02e004006882d0160748900c80341c0c06c3c1d6000d40d25440050b80c400c1150841141a52008590003003000c0001070801d41c5444900d125854501d00f11080c003080d044042c00b06407124415001880c001001201c03225800109807034160103550322203000d02d960340d00d541081c0004120802910baa00800442d40c4403144e01d0420303003075041a911011034009d082e444c1440a08036208845e8000140680020100781039a07400c074000280c8413024400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 679211690 1250 679210440 679210451
    0xf0c1e03030c010c0203031f03020f060705011d010506010e041a090c0408190b07020114160219080304030e030303010f0b340213021815280e010c121101 67
    0x5070b0000e101d625a041038a6015680d207041c06600813698000007d102c0801c42d41e0007508000603950101030090342c1c042915115200d2101d800d020380140080c1c040404070702e07440c07a00d0201c004810352000e8850130007601d0303000c901c1703501d101840201e520041c5039071080700034180d14900342c0c5401c44591340e00011100304035241c29101d110040c14034549003d5001440c0302d40802108000c50044125404000c500c020080703000d040300002250440980086a041510f0800c911407a10030712a9000c040c0c000407000749044d86910303114215620442d4181c00080300009040420f1030040100d81c101c40b0340422146480381041142405984008081d280c110070b0144035001505482c880340510300c0100000c0320200751070b40144440c400d215081000201d10401110480c603200001401425809a505294142031043c003107a991050440d180007000507050303103402c2040075140704202c410046c1d84a6508501800043da03020580c03001c018812143c607000000c00511401c1844a28103072500081071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 679212940 1250 679211690 679211707
    0x705130f09140606010801090509100905010213170f01051311030715050d0b040501081b0f1908070503060705250c140a2301140418020703020f0c1e0303 67
    0x14003a200400b00c1045401400030040c003580c0001145004004010703042c80b036440e20070603da032903e4101800300d02541da0342d08241c0620409505440c3c112025480d0f2006564540007802048040d03100f0a16451141072044100c119040c02614004c0300b40c0aa81d4000c1c2c03805c0e903607640034a00c1350404c254051240e1240000c811540071a56200c400c1c06855103030382c0f1403940044200351900c403106580184d00b08001000700ba400000e080700c01c1010b10000512548409000452076060941c031070750302c5000381c3d500041c0d28415401030403c840f80c45080361407041da101c0505496400464003440460018845100040c40300313040d00c02124112140040d5480090783c84100840b281e820504521030700310350050312420400030400c0070b0100040d280340441490b40701d000c41b200d40d4280550400c00c030b8000500c00b8440382c100303541c068501c0700c4e0390a0b0000b075441c601000941140805800521540c002503034070547c003040b40e0020907409048010311961340c51103000b0916850911a0705840200710810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 679214190 1250 679212940 679212953
    0x3270706050712090303020d180b030108071d2a0c0f030316020f0307121103041202041a0a051c0501020c0d171501030c12140a0e0705130f09 62
    0x140a4034003600c41da038075003145081124001000314005000d1140c84031092000c039400090401c01c284151501e000b0760341c40c202c0c0c548503003482d03a1b00001c4800c074040001319158102260312000d0f00c1204410400d101581000d443c142d8105540000002c07000c2c100c808105915400c0300354660803541070144c07501880344450b0785451001441000c280d0400b2091202800c0b20540800701e1558500c02002021811000b080d00c81c41506c10040c007200800b118a1417450250b00da01a000039442d003aa0b494503540d01410b010401008001c84c810361900003400310000895122401c08135000d404954041d05000074030103400d003040341d4406d10000c0601e0900004909000520203007091001038100c1c0d151502c0e02520051044501f140301d084070703400f000000e810301e21100d000da107070918020403a000744030710541c0c55100342d6030f05501181c00c000382110007200c941c1216018070013400d0108400d680c50b203003468584a89000f419844408600c9440d03c503100741d0003540096000700e40c00101e80341550b4551 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 679215440 1250 679214190 679214203
    0xc0206090a081e0c060403050c0f18040305041401050301080c090702030d0204080102180301020a0503130f020a0905160504121b0503010e0d030c0206011202090406150909061b02030327 81
    0x10340401c0f40d2078500c046000007440036609000e415107100342020f05587d1246d46559640c0302c1c080c0100b003c0510315507140d42c0d0341040c3d4641500500703541844d0401e070400901c283e0160050746403010070740e064021903500c28000c50f030407039032000081c184001002c0c0070040c0c403403405070401d411071105001e102e407000d074540700802c01400b0200c00181e448499010709400f2018000201d4420f920500c068400c0070340000480b0b500c54048a0103c1d903907942c516000307000c02e40b41c04000c1e4100c03500c807402151400b601e40c44140951030440b20181995a940d070221421b110358000c0036940c050305090040014000702d2900d140030b000310107181416440341c000c00c0c2144e240418034007690f0b2083c4804c001c2240c02d4820b2489216031072010307110300d41c100307200361140c4d44428200a000d120b6070f20000c0c00340300c1c065000019a0742d9840058090640d52580352014240041c1d09403012490121400102113049000d01600384158002d58215904c003078401c0b443c000c034804041b0480c6000307010072128003000e0010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 679216690 1250 679215440 679215463
    0x11070612050403091a04180902090c07050a05030f070b1609140301111306120b0907140702090439050607050a1b03031d150306010c0f1415070c0206090a08 68
    0x2c882e2100d00d80701d0b6001c0d01f09103000801011518141e50280541c5403070b40700507031025000f040c1541e02c0c001407400e5450022500b5014107580800b043c040303203034203a1000400e1444d008152111179a15a03041000b40000082c0c602e2020460b01141000308d030b0901c8220719201c2100500000301441034003944030a980c000c100400000a55403024080c0ca5000304c2203181444042604115020300c60380801c07000388016105000344110346c0325054242e1603c10403135107030b25800340500d002801c040c6000d280040e080b9111090f81c00350b814180003006c600359a14803038081d5201074001124039082c280012035000402c259154094060170401041e1407164040d0b40780802680d40c50107500e5410002c12050f100c0b080100c085031001c0d204402c59a07880e41d810502d030314104143da625252000161025003d01c2c0000b000524812410300a004040500c0c03229188807205031041d40200c1d180955024004503040e601242000480c41c026040c500b002e80315460003d40b00d00c40b043d88032700f0514903109200c0300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 679217940 1250 679216690 679216739
    0x60603050d0507050348070602120909060102030c1608011a03030a0305060f0312040510110619060e0117010c030e070e0619151107061205040309 64
    0x41002001010040300e090304141d03182950400031140e544984038859060741101148030941800594011000c0c2c40042c00c5c08200fa40a00c3e4115450180540d0001041da415500a940001070094000304d044412901101009803800210104100c0c40c0500a003e00d411440b051014441041d01000191b10502e40d0711800c078bc0c5a0b00c0d15000c1825904001c0c1001286070040a000c0c1190f100003081d907030401034504000c11140e9441001c03605100d032007048a40e052142d20b100c904400404002801517403002d0b01c92a40ba8051a902651005030350650b08100b50b00030030000e00c200c06040103c410070494401c000c103107265205200d080000c000c0e04403100c2d100d01032a201c0c0c4840350034031414689004509082c0902c0e1040c0e241d0a454150a2040d013821070750480c0010348c0d5545042c03004400a244500c04089542c407000c0403030032032000501402c0070400080243e00e04550006050040728110707900c40301c581c442112208080d20020740110140419080081010840b0f10703c0303803655800496 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 679219190 1250 679217940 679217951
    0x3080c1915050903130303030b220915090c0e0403050c06150f0916200303100f0801050c0d02090402130621050f161701030b040b071b03121806 63
    0x100700c8011a0b074007401c2e82000d0340c03040145201031035000c50404212038050800050102140c2c3c04503000b0901c000b03242c803c00301c5592003142c00a82c00c4e804a036817030303000310300444262071000e8042080b00d0042c0301c0034000b40d044640400140c1c0719400d041d80d0040c82450f0890030880c2c41800e4a00e458030039220650a40c4c40b0320b501d0092030500c0364400003e8841220000c0f0176003003102190742c2d1440c50001c02000c109144030740f14007048802c40c89420300701c0c90b9011641e480c9007840d103c3c401c841680c044c0c0c0c2c0b02c0111054000402510501540b030044a18455640c509104520200020740c0090203854102ea000e1000e0b102035401c043c04080106510385840c520142c40c05001d0760000d2083c5682c4038071924003002c0c04107000c1200c5040d980419403000f120711b101400c00342504c1030b820b6004106041c45859002104002c800d8607228050f601c074030090242c0d070325411000e40d4203108411030980c014030b0380c0251501080c03241580341ea0f40780715100002120740d0001650300c403202803004140c50700d0b034640c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 679220440 1250 679219190 679219223
    0x9020304060f1103040b0a0c1b11010906020f030307030b040e0f0a02041104061b06141003170403050c01121b020105180a0819200a020f010306060903080c19 69
    0x1400703075881c0c3e00500d60b01c0919510b07043c0e481080c48880900422005035407241b48203081401062510032a898003001403003c1f02a0b0319001c080310761b444140a000840812000035880d000081070a1508011005542955035461080b0f0041941001c3d003a03002d03403103224450810070280303d10340804070464060018010580140400d1314220240c0841d1458104400c00c4802d43c841152030121891118004081025040600142c9914152000d0210000702030000584010101c2c000322072042c1498074800c2402d290a2405004034800a0256005500c0d603003044c0d0320540ca034016a10381500009820180084144003055181c10b2303144c00741c1c0d580d00c241300051010400008000665100402500f08942d0343c81c100c42c003850035a0b20301c400003032460400c2c0314018900e011408005040c420b00041c180780c072207039803405002000c2e4052142400326000c503510900038403050741c10a84a03c0c00702491a5140074150f841100603120900404140c80080304d2041842d90241d0f000385451016250b09 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 679221690 1250 679220440 679220471
    0x209011209291e0c0f190207091a0910080303070216090c0e010807110a08030402130e030412020109121b0b0703080403050313050604150c030501080a080f040902030406 74
    0x40c660360310282c1d001e4508100691000c22040c03200242040369140b20354441a40820150003070080402003079401245a24061217141556880782d0126400c44004656403104041100c1011400e12503803c0d8003030081516050050f20550440403105011800c2559202c0c1c603800d5800948002006030404a204909040c07801001c00c081c06840e4000c01c100d0465001c0a04000c40311848207061020120004050074060b200d6040d0700380441040ea1003103100c03840c01207e590300864040348100058000f4441880e0280714200316104103d000307500c0d00c1c0c18007042601800707440c20201d04000380c01c81d000c01e04200c05a00301a80610601d04000c00d00200d1001c40002c0f09035030440c80c40c080c4280100c1c00447d902501e01d0f038015800d820b09a5407a10354114071001d180da007140207840d520030b450038001001031400b0402c15005a41c030301001444030b118811401d540c1d081c45001c5a0b903211030400c501007890440242202845078807428070f45503680018105036002203d050380d00a603503c000303100350f060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 679222940 1250 679221690 679221743
    0x7060c0207140a050a09090c03080a0806011d0d030809010e0709051503060c091905062208160b03071806020a0b0c090d150b030312150102030c0a03030209011209 71
    0xa0032503040304864200744c0821010402485030415180d1111032160601561211002c080c541007251540d440c501030501501c81302d4203844440c005003e0b24030b041042829a8980c1c6800c203001403503100c00912940f03080703d4141c4003500c8010295a00d502a440141c020000c190003000f05540200d9146448060311000401c4011154043d13080002003003410306111382101c21640088414000c5440ca448441e049004582c0025801c60b030f0001e00c0c043c40741c0100c0640f410b0211070090711502e942d140c0c4540da464030898008006400b4200506221803070b1070401940d40070300285444040017004008032034103a01203510960150300f10070451414400350740c1e880d40c0d119142c3c2e8007191404216201103002c011a84501800b03000d00c0e45084100030580d80c200b03202103071005044070b441d02d03054994131201203406c1c4d5114009107400c07030950405500100c2603440d440c07207210140c480000943c505401079403015280c1410098500511001a0036620400c0740d01d50141d00e490314882040c0c41e8a055180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 679224190 1250 679222940 679222979
    0x60c010e060105061c050a06090519152603090306011e0b040509060103020d0f05150a120807080a0e030709020a020f0c1e030a0b0405010c0206010e160e0607060c0207 73
    0xe100700460004a02015170120480240c614000b4103507440504450041400d60001110a800d00c2c06015000412184410009802440c10010004031100440d840d076010310403000d00210300d44840110380c42c0031208400e02c0c3c0031102520f1502076603000080c02c0080c00d82201410b113900780502417080c0c917480302c01409000c00c0e487c2c1510300340c20500011071000b8000c0810741003540020701c0410b900c5c400d4002c4c5000103a1980c0a020904015240c0c000000d44a4600c50007100780c140c0001d4040b200c000140d00140c2c02c194854641080340c0c44201d1030368040041030040c400401c103101d0007034504000c280d006000045d4016218101c414000b0305201000c00b8681d42035001c0c844200701c55640d0f00382e00c6a100701644120303900b481ea10b80440e00340703841d02c000580b5295558007000140001900440d600b82e0300b0390b0030b907002a130300c7c1c07084420f01d0380c0141d03282c4202081080c0c140c51600d000e45001e10340c500008000d642000b036903540b0748054804640202005810903d001c00102a86100700340044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 679225440 1250 679224190 679224199
    0xc03200a17030714160b180c06120f100b120a1b09091512140d0207030314181c050c010912120e0a060f09142d060c010e060105 56
    0x1402d203080018030006800070101e08420000803034845e08011180c0c0a011194001d0342500c2c245400c054089a00310314100b800d01901840705000d0780c40c07812004851013580400031200c40c07601d81e0140c58866810050065082488022000c0360482c20203025002003107142c00105200c0c90640c2d4104145c5102d5801140740c019044120340009400c0000982901c680c1280052084010007200c440304002d41c0c031040c01c2c10344c5e07158501c05206841d2452150b0108120440b00c01504420080340e41c0c0340b00384000780004000101c0710301801c1203500180000383c451090544c0e14000800000c2600c134907071a50400741e0011005040400109008164681d10b09007010402c2600d4a900e80c2c1c44402814001440848800801540c03507001e03442103020188041c01c01c600c896150100034041200e43c1241401040d440c20700062010f41c900c030403800c04400980804030011000c103081e83c1070f800d0130442c0c0c0c100707081c0e00c8550f03482d0392200b2000d409000e9080001091030249100c6032410020103030419800f6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 679226690 1250 679225440 679225447
    0x40507090f050c0711040f1503061505030a060c0203210402040605032103060a030f2a050604090f0b060c011d300f04181503030f0c03200a17 62
    0x5205406613001c5035003102003007821080b1100000c00610701040c104600e145864440082030f45104524000c0d81d1154400f007100100d042c076040308982d9688182ea03816880003035181d00103082c0d070b00300d944c04031401d00441c1e0911808000a900780c000c0082540301802c5c4070b90800c400d601d041c0c001e003801018154013903d000c0c200640482d9001d1400d501c90b00400c000040414059102c1064500c000c50f0045440e51004944d450628811071601c900d846030811807010b201400b4004070bc030101215402040c03103141918054004015012041603205482c0c0e5400714800701e6112100144019402d410001444402860001c00340c4c510301c1c4074034401540002801000c02c0c40c80d203d102c1c0040100d5205136042c0c44048424042445205050307408908080740005124503072902c3e81400000c40703c000c3c046855030351300c00f100c00b01044c0310203400a29440c0d40c40814500a0701c140103120700038a85800340340841054032400400c1da40009000d030703210502540c00e000b0b496140e4441e845a50414514 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 679227940 1250 679226690 679226701
    0x8130806360d0e0a0b0c0a02031b010206240907120e0714040522030e0a0b030f1f0512342c070201052d1603020403020306040507090f05 60
    0x103554514200d00024007910f00e48668040c1ea904102030010003201c810b490341c0328480101079803035140300b8408a000784607440015510070f003140300e42d10414078180d00a01155441800441d551560321003500c5500c01049440b00007900c03000034140c03003a112911101c28036100ca6844008503420080110100c2d0450740043c800e070017032900c000d10300c05400c840218068490041800400c2c5081d03074214826048074407450201500a01c6021004108807424410141e0b40c0d120242607100071074a03919085940c05c0050030516a0002c60760584c510801c040f802542c4900204081002c00c0051317089540c080a9103841d034110100c100040c81c2d40300114503840caa18100c03040740c1c1c1700250141125407140c0541d071508001c0c036401c0c0c0801c10b0089101c9840541480500070b402000c0640b00080500c40300c0001e00081c0e881c0110003220780000083c001419070b202c2403170308560f699200d88401055020040000940c1d0704011060040c1e0040380505140d41c60446510f0840340030b00d0351000b41ea41400c04201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 679229190 1250 679227940 679227943
    0x3031805150f040f060905090a06080c10020c0a030b190e15060f3d1205060d0503040b040e01050d02010516030927180f0813080636 58
    0x340d07400d400c220351940794001c80712012682d000b2500040c0031064034140029946070b00420710401c5400079a50074003580c0b640c0403201c0603070f103083c014103446038803804141e011414042d62418078010a44144c6540400d0300d0b0000781e21100c1d9034400e0b02d4091190b014001c1c40010700c00c042c81c00110f031100401440c800510525200c0e00e83c0003001021029040004e400c41e2903c104000c051b40b0010b2008154250b1105180d625907503c44c0071313020760000300c4959814440c801c40d00448607100c544a80d0380a9860304d070804040d01c0d00408003500507003188203280c002075080024002500808000d56180d030304180c06140f000005070f1085111740d07001d000707440250f600902101c110408045030103402a44600f01911025001c1d401107141c44451001900308028110b2490007000b4036a03800c0c00b26030350001c024002c1034800440948041d400c00d01d814000b8101170b00402da000907a41c40460125038070194142082c0381150784e90b1240c04044003002d440c0c191044942550280007100340642d0b284818a00e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 679230440 1250 679229190 679229209
    0x30604050a030807051e12100308160f02040e1e060601090306050c1308010507020c010507020604121406040c0e0c072001110601030602040504060f080c09061305070903031805 77
    0x1906001100e804544001d00c91000c441074211202074003204c2d64404465844507a000c0391049460220000c003245586032420218230440790032200d00d505040b001500e40414501614085540d9080d02c2e20f4600180c075140601c04140ba900005040e88452103405075108041d403d07465280ca401900420560743c0e00850420152a081031000a06035a0040c1a001c14030400700c650401960141c400502540c05402180c03181200c0ea0940d5030344101c001c015603042c007401c40000e43c098828081400f0f00aa00040c5210071400382041140f0b4104a5002c103081a009071340c155039000c026031080c005c0f50311110b0080c0d0040c03140ca0b801703480c0c5061a03d0361182454042810030100e42ea61030040002d0384a024554001440d031025600a0f5940e031405130000d5001c0d108483c0201d007070100008020100705200001ca07001c0001511000b01e0820400c01401c07001000305501070306d000301c80901c249841c40741c42d119506507202c140880382141005020b0510444544081030032115052059840b8036846 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 679231690 1250 679230440 679230443
    0x150f020607030f090b19061415031f0b03071b0b0406090c081b120304030201120c03020708030f07121b14041d0412030506060304080c011e09060b030604050a 69
    0x5103c01c00c00c05410142c861903201600f961225418008850203608000c0d01440d0b92040030010641d40345a80780c4408140c502450303000da6030b000703d02c5e400103582000b998000c11038140301e00c5409446840040500d180d4200c4c98200802000300000359400808408204078011480404850507a60b2800080e80081c8010407403070710351a0035010003005400900c090050740094648a00748000034440d00003005000e640301c0d000c41c800d940041c4034048101c0d81a42d1701030b560703a01c0c1a080703484c500020307002411400d400c00d03908010a001154034000618040e1003400d001e24801e091403c8001c1008203000c0c940c84200c1d00d4040081d010402c000c1d0441800b12041c2040c072801200101d4a4900d0300841e4440100d0010a800d030025100107020224481c03171094803445904030b41034000b203040f034800720751440d002035080001c500401c0c2550041c4c05030402400001c60020b565a140300c0c110558040c000000c640c5452942c8200203281c001c80800343c0742038004003000c0c41c01c0e440782c99803400401c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 679232940 1250 679231690 679231697
    0x30504030c0f1a09012d03060b130e0c090604060908060708250c050d0807080a050f010b07020f041b090506090607060b010c050f0304260d030b030708010510150f020607 74
    0x350729644e640500c00c03c00300a85071100c4410307005080341c41c0c41e00c1c40c001418000002442c150300868204c0040003540c054480d03002c00940b00c28244004504803401c05890301c1e0080109012041032075403154010000341480d95141d2040320b2800040350300c1c048002d05000140311600040103400a01c1c00f101d40b000c0c2c1d030300300404154a24840700c1590a91400039010740b807402001003003940160000c1c5658015403c580e5100c25903510450780030201c442c2510302400d140ca0020042091410200c00360070b0380750008200000c08400480000d08a807214110650441a800805030f42c1a8001c1e44000040034240d600313614002d9280000350840c4100e50009124036a1117542c000982d124a1518141e107a124040301d000e550301c903d0840d52900300744503801a190280054480d2080908a4803a000c0600e81c0141b82480740b038502034000c2c04900d030480d601441907080005078a44240621800344002542d0f102e0030340d0070b00e0200350b00107954074450b80c1070060070140220350650015205900036090319 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 679234190 1250 679232940 679232947
    0x19080d08061e010e0a3b130605060a0806070f02100e0a020d062012060a061e021f09020f030d0f080a0908121f15200a030504030c0f1a 59
    0x3c001074410300c0d250080310261500c10808011000341c3c148248540d00f460a10b0031007140d6086d1020f03284841283d0003044103c501981d0f00006400c0d410058020384014251000140c0300c04016180001c00c030b820100281391030078905c4000d031701400b00c4100c41803a41000d1140200100320141e4540250304024042d40c4044420000d0002e141d004170180c1c03c80200340c1341d04c01c98040d9200c00c5034000a0081388006411400320f0100e1809051030021520316882c1c0e80c02d04080d040342072a0060501d00b40000394002c805405e40c40c6140504030b048002010000010303c0c0405006102c80c2c0e00b192000c0d14000c0d805903040c040056080240c2821901c16480c007401d06a440c1007205002d41000100105903c80100320301c8100c50000441c2c0c3e118024131140007070282112a054180c618291042e1105404c1c09151528060312800062041c2c140500409850076420405a8588419030b2030680000305e01050504c00c002c2c000091a0040c050100c43d0400d103420301007550b18200051418101003031001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 679235440 1250 679234190 679234217
    0x1d030304150f270e06060d11130e060a0b1e04081e0307031b0f120507060f090803271b0a090204050604050103020705101a040b0108010b12040219080d08061e01 70
    0x1030445091011f0307c102485048118410001c50703402a0b5461840c2a0001001144625581c0c207142e2007188002d00c001c0c100d500d00110103266512902187e140c240311885000e0b003030038601c00200014840a001000c0c80040316104003400903001d640b9802c241c00c104910030100b5405800b2581e803083c68601c3d00700804c45c83c82e02c008040c2007034800030000f8400c1d8102802c8250443d0281c191075010324070a010440d049201981296030317410008110400510100307480c42c0c220b480c0f5100d0b002000343d60a07040c0e07a01640340b0b40340400000144003040050844500ccd0b5007018180307203004140d9a142076003407508001c0000c3e41030050317010f13507410154045a90410b116082191140c01c0480035000c00c086190100400d40310662008a540101c0c2010020049035209012250407140d101508505003c841d402c07074100d9400c040c1040c2d80c4003440601e4000c0c01080f03803c018004000078001403001d4001d00201501ca282d0082809100b05000f1110000e41c1c000c13008004921746007480d00300e00703c0008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 679236690 1250 679235440 679235449
    0xb0603190f1b0f15030506010c0b040b1504050f1e1b07080d1a100513120c08060a09060c030603020904150f020d0e10020a1d030304150f270e06 63
    0x440d03000f2407a02910f2503002410a00c2138108a507500c1159a06001c41e41e034001c0150382d035441c1904010a0601e00c0c20018001c5214a00c88540002c5041d000203224030300d00380041d041e40c42c103482011a16900409005800d403080311010500d8071080d031050001d141440e46000c569502c509c0349200084001100010015510100d44400d500c0007400c029051140741c0c5480c1410204403864083c0c039500340140d4105000350247c840903201951146412420311804404c0300d007050000305d07800603480c0000f0400840c02e2107002d02c14100c942c40054107503113501f01a402d40b41c0f03104000c0c3c1414940311f410700141e241e203681c080e800f0741c000300340514480d0080c5581005002d0201581003640c03004c07031510240001034208010004e4020100d030005a44c6502c51001c030302c01e0718006400705503031014480d00a000c0716101c20103210020180c1c0d04203a51800711000151202204070005140a0b2528a4039a00314114906003150500d00082d107520220031b4024803010b60041c080c03007105840004a03d40d45 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 679237940 1250 679236690 679236743
    0x405090a08030a150e040213021c0905160618140927010e0304060306170d18050405070504032319051606110d020609150703180b0603190f 61
    0x51305124003a6240d9910444403260009440c01c80c0720300280454034400319440d0003680c4c91140d500c02130070060f00c00c07050384c140100440a022074460003440079036210a018030100c48014a465129441c6000190281484000c010b03041049003440c0740c520401161241461590302022292612030280740c00c1c1341450b8101d80d6080c0404156003849058600550080060411035116444c20321041c0c0c3c403480d44003a101c007209415042d50340642290301c0e6051250241d2603040310b005054001060301e440c089030640708112000c0700807500001e010000c1041008603600a43c003030360108004503240c400360700c0d165a026000c0e038108007440350302d02052000a0100c820300052000d40400c0159030b40744003600303016000c841c25019004045c5001751940c00070900d144221044400b404141015800c59030b103100c000f4091108241d41e072000c0b40045600a00482c0d03516000304805070062401c0c1081628000714450135420140b510206440091601c0130803410050740410056610140c0054050314040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 679239190 1250 679237940 679237961
    0xc15070506091c08061c0201120e011b3b1206160206090703120909020c0c0909011a0d03030b060d0c1403040803160201061214010b0405090a08030a 65
    0x500401d00c4114100003d4100c0d0485080e011000c40c041510ba00b81e03040c03182260f01c140c01013001c140b407900f4400d441d0540a083c501c14117050503501c646107120002c56032610a582d40c2d60b03548004980006414440381450b411082c0340c03010102c14441640342d50080d04401940e204108620b1050014208900004190901a00c00954607124080159903140251280c00c0710300f00010f020140c0d04e2010030710b1341c4159010b10040035424610394808260041018010b002c012070042d000c034000015000511403c402c5000600826005038100004410062721100d00ca07032412514240001d403c224042140c001107905003030081c001d00301039000d08042c41c100d941c071900008a80700004502c1e030006440c49a55507d83d01a00340c0300a00c2c0c90710703202c04c3d1809000e032a814000121000040c1d150340160301107034400400c0003580e580095402c01020f200c1240e1640c40b010810300702c400d0910808a900c1801c940601803410080e501c3c58403080b01c604d0203020040e0004c0014408603954003c0340d110cd = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 679240440 1250 679239190 679239193
    0x150a140d090807140307030c0f02040b090403020319081612020f0a081f061b060902120304031502040609210f110306060103050c090f030c0a0807050319050c150705 72
    0x203080d10b8907007280e80c8442e104580d155a030303600ca4558154000203482e045685610f031080da066190711a02c2e02e509040000301d074002e488000324031054882c4000940a10702c00c3e0015070b22440b00320155450600f44a54400400c190041013004050200052883c4403007141004c6001c0310030140040068890060100d03d400000030b45140031550003082d403480b510303000c10040750401924298403075030b01c1c03a80700f903000040199505007440d9060040c0441854410b040c0091169103641c08038290b900c034004002e0b05a08041000c100740070402000000f04103130aa01180f81c1400e02c0c40141400807240510945004000302140b801d104440e01c1364020741e00701c0300c03099101c49545041c504107001012414001d00540c000f2403402d501900643c0e00841c900e02400c0d0910000b8000d1208050740721144a900d4032400007030481540b244400c44d40604030f03100140c040b107801c00041c585041c1100c00c044102407801000f5502282011803613a00100044801100b425400b900141050261003c0640107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 679241690 1250 679240440 679240451
    0xc0303030506031b240403120507031106010e0a24030803161707110f010e030a140a09090b0102012c06010512030f1810020c01030605060c19022205060a05150a140d 72
    0x4076001004ac4c5041c07486a80c0707501d11483c0800300b242c2ca0380002e01c107002c002041c1c4404174801d11040d4100b9810b40d030401400c002203c240004e403191b1809a544190f90900001061089070a45139008200c8455107051410384034402500f030802441000b0004030820020048980c1c0b9204284900080808007400920907413020102c15903d9034401000900414252240782c090401e100b02942c0d500c245540750400b81a00d8501904094489520241d045550f04c03404206200f0301d41902492642c000c194140d02807c10042440c900803043e00082d20505000130401c0140304008100d47d1a00c5ca82001e107925000349500c2e481da01d4400845043e44280d030342da428402c00d64009009003004100345d90500c180c551301c0c0c003400820320034644260195000310629019a118516042d03101c0c0b88054100d05115407500f000041e0721498844420a03181c59105010351464030008a0018113401c0310182c0036259180309400051040104490a002c000305403000405040b4003aa04c5520540c00c09005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 679242940 1250 679241690 679241723
    0xf15030204050a0209090702101b020604030f0504120b040c0801090b130c030c08030c06010e15040e070905160323060f0a03050718060f060504030b130c0303030506031b240403 77
    0x403681d031405c4684201d12b00e0140d0400c4181e2504c3c95511070b5440d02d401030300a944a6072400c40e09130100c40f03081000d100c004c010015407941300d904400c44160103031031604031031300f0076180c604a44015a40680304980c1808203a10215002d0121581c0066481c00d45d1022141c0341c1c0781c4410f640300c86900181041000402c00110154080014501800c07903a003070300c542d0307030720b0701c81940100ca020b58841e050b0071200e4640c3c00b89810907510220760040d8110440d06010b60310802c0300251802101c410050554540b130740b42640d5054080d2500202018004205024103a81049040c02004042921480079071518410399229554600c0103142c03c10f05444c6041e4403540400c103c140b111802c204034525091002844520381780240081d11180c0d134600345010b1a40e203a00d10020720182078640039101101c0c01c00e0010703040100d9140291f00c20f45020456240880416080c600c23042c06504100d8445041140c0b540d031141c0000004511100c2d200514610429041320039004940004100900034182d403035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 679244190 1250 679242940 679242943
    0xe04030314130b0705071a01060507021005030601050d05040201030b0909070f0501090510030e03160f020a05060909070f12060801060e06030f0714061603120f15030204050a0209090702 81
    0x141d410740d4001d5007409070320707050705507418400c072070001811030007010010948140c4550001c0c285240180c050034602840b150200e0740c0c441c1c2c01c2c2d0002000c9000003480500710304114440d9204000141040c90031031401000203420342c4100010100042e5071440001c3c110f80c004c1d0f116051a1101a201c05a070b80391911040d565080140503120301c0b001c8400d000110740d84501d074160f041d104007622030f84003094a2103054001c2c06444031280580e010a200c1501d102402c00390206803180181079030100360320360b80140503d200302a00300900409007004503c00301d4452041c1190001c1440c5003241030155001402c4900303011f0040340c1e003031890402c000000d11803815005001954141c0c8071b039640984500040640d20701d804c1078403c003d038000300001c00514054442880312503001030821490b0042112516440604a5004402113200ca41c4000c4400c07090707214804140100000c10003403000400d0b1407420140a5200080c402c80c3c580001030035040c4c607074043e614114405007034403040d42015a80a07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 679245440 1250 679244190 679244201
    0x1020703030b1f0512070c08161a010302010f080403050f04030c0302041d071a04050604090e0706090f1e091b030b010c12050306010212040801020417071a0c070e040303 74
    0x1a8403401c01502200aa2a060103109010751419110f89240c40c1210202402c2035100801d00010710110b8118140418412401009149c0c92902640c540340d00234a082c0da40700c1c5c0304015000f400c02100e401440140d8002c240c800c01e100c500c7c180b94089a1301c07072404803002d10400744100311401012030000100810902050240d82c8211014040761203074042d5036208460848038101c450b80101c004104452000c10003903900134004011a00d4940c842010a62641c03213540511045a0707140c0740c4a4542c0030a000d610b010700320a2420a021500d890101341d07808242d4011140044426200c24800800283c9403c00500c91244148110103451104103019031700d020f908c00110341803e0031010a036218201300ca2040e98400c240b1500007046900481d50780d003006001c94194820201522800d4040001410081c9010741c00540d54a00b420203802a074100002070f048264060071081c00000701e001401203d8800f042c10b07440d140d015454440380381107216400039200105801c1030005159064124 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 679246690 1250 679245440 679245461
    0x50c1002010b010212090f060d020409020a09051c03270f030311060a1503140a051b031603120806210d2007032003061305061b16140102070303 63
    0x2030700d011131409424040f40e41b0850340810790080d0b01e20303041c155514109010f0110120444001403c2545030350115080341d1011000b0008201110303410010b928000c42c010302e030300002e0900340d46c0031017155401410100e03d05070320450105202124600062180d09107200038600510000b00307150341c80c140509682440001c200d81030140e180003030000000b138010070440c2c2707803c0c440700c1c1a110303d1500c860141244015968625000310482c00010580070000c0004640f00e2040c04d40c0183c1e000e104251811441344441d00074110809400c0020800c07a068840851341b1a0808012a0f034804000a02291080c05511804002e2880300e100c0e4000000e008121110301d40c64200b00043c00300301040c0e40c03a6403020010b050303500c6202c0034000281c591172104800c4a13070a900205065403140000c0c01d001381242c00001c6404060024420700c602000001c1e04804614040c0b40341c107603464200381d0035100f40c03200d4080c16100d2080d88810001071303050303000c0e0130400480210f4603203c0a140c0103018100c60f036913 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 679247940 1250 679246690 679246693
    0x2b1413030206160212070327080106060314180f060708072a060f0605040c03020306033007080f0d1a09010609030b041e152a0c050c1002010b0102 64
    0x43c3c4420000c8007200c150944070340090260808074191039640c0d81c0280d8045007040507462003101e002451002c180541c43c0a040146034050030700d03030407038211516a4441010581030411031b00c000380c50b14505c4e5412010120392410300c1e06140090710301e00048410609001d00c00c0c2030421600c554000502ca016900c195542c1c1001d030050b0300324411802c1d00103010f240441010b140300c4001507043c0c0c07202e5400100008003190682d590300015084540502d13031003001c240c00004000091500740841c00d03800c0b410110111200340c1e40c880410b41d0300701c01800041c2c1400e00240110a000e00c0c801641c0c080401071449540d103010004940c809801d40d0840924040c08444443c0c0852420288081c16194a0781d01e84d00c90341c1ca151100014210090010f031202c1480d031191164040e0310b0035041c2000d42c0640001614940c0340209003080717503280e030041c0801440c404500c0413400074101400e1100c48142c0b601c80c005405a082c5a418000300d04040766101c0e400503011039a058064000902440d0300f40c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 679249190 1250 679247940 679247953
    0x305032a0f0a0c050f07080114090601170a050706091508042f06031501080f0105151c0c111209090601181211090a022b14130302 57
    0x4034a824030002800c0c104200392030911044112020703120103402c1003a01450200c3c3d0b188800d49409040c403200804500850704807a034203002c0100240238403440411345124030480c40c5000c004864990031306000b0100d1100c0384082048100b102081640242d5811100b40c40c401552090090700b510010b200c0c6c5480704c50107404a002490203078000c00d01c01c9070031810f441c0c202051101041c5d80045000d440071521080001101001e89940010354890402d0520400136252003d001400d0340764010107505402c0310442c0103108036100e42c5000041d044d00d1005041c0c4500b5206201301001500d1200001010302e401c8050341ca2640c0482e05006058080055a40081010400042c00d01c03510000c90740101411012a040e54803e21407001c8040c2000344030580c198403206c0a216401c007481c0d098491490080c00100340345490816103800c00c80c5100214a0040d05c082d40c10710b03030807000100030728020a002c4e0503440d94407141c100410f224031104844042e8500b5503441180f4042400050b4014419607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 679250440 1250 679249190 679249231
    0x4090b040605010f0f03150f081e030c030906030a0f050a0614030a170a03020c1902100e030c0f0613090219080702030316030f0509030a11120403080304140307030503 73
    0x3034050325043e40490b901d0a140301c0070500d00743e0261804021001000d21100d80004c8c601407d41c3c504800790a640c40509010740389860504980c5081c0060300b4404d400400031121740100c0041200c2ea454016541c064480da21010100028040405001c00c214108000c20000000541c003a90030b4480821802d0b0114090406041c2c0c0c80803100d0300180306000c200815460140c440025282c403100515000d454004424807950400700318003000c81d2a030541946000862810701661002940c243c0f40103038104420000080c1c0d20301c040d80c00d0ba40513400b1203281c0b44035920313032400b11041062070f145c401150559404441000703501c510000c09285100d42110011070748a10782080c0141d0682d4000d6003151600000e03100030074180c0c01914281030352402d0070144007c3c00d00030580f08203000000b45480d640030f020040e051155019842ca44c9030041542c180d0700c24030001c241c1e070541c0c0c0c100145644950711440c09200c1d04034004980c0c003041c4804a541c0e000c00d46c3c40f100441c03148121494080d1303e91400c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 679251690 1250 679250440 679250447
    0xf050402030d09151101090c15141201060807020a0507060f12051005011404050306011403010c0206160c03020c030303250207030201080708040f0c0602030c0f0304140402160804090b04060501 84
    0x2603020b0460181002c40c130300c0120303500c508081940c24561100000e81300c1615600d40000002e940d0100c000701c0000d8a07408400c0da00710840301840c0184412032803411000c0c50060f07030010b0b814000c9200b800103040c00300d01581e20030001e1680030350f4000b0403130361250740f1807a0241c450103000d147c510000d03070b036940441c0c0030150343e00a290160700302d060306641c1c0e94100401502c807185180341c0811900010b00000850b039804000c8a8000c10502075510803500080080c542510740e401c02207000c0d58400400c0c0f00081d01c500c010450008218a4180440300c10383c89c08a0070807007581c2e5850380c18400801445030f110100300070a1804100100c5018403e40503c800741c0c1c613130f41c1070300c4007038040340310800002c0c166400350ba40c082c2d00c07d109003801280d05050b41d44440c00b41034950091801a44007240e20b003c0305034200201e40311140c0041c002c0d070030b241c5021254410603540b0301d000b500540c1c0104681361800050042543e015500070301c001c0d1119100c1c18240001c0c4a24a00e4611030ba082c5007000416501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 679252940 1250 679251690 679251707
    0xc0906080a02034216050304051507050d0516030c080405100207080706020a020d0e041802041104330509062b0c03090b1506030711100f050402030d 65
    0x1805005804100d070050b952654264030344020300d1500710315003035540300204403d84c00c0e030340204150b4078095a41040d084034600320442d0820310301404400c00038030002c10340001e01004684640c02c51304042d99100d1341d003102d19008461650030003d013044284410504580108030720f09440350750810151020384822902d01105440281c0982c125800e02d000c1a19035800500740240103420075450011a40d46410890707000c02e01110058026512889040794800101d030f80c80401198184004c440c6101d051140d1801c0b448002d108a645010002083c24418282d4004029031590301041c0c441025154054543c1c2c0340158014039503543c1c400d44507038094400c0c2d603081400034009608145a0050035640f04d81e18514110030706031040c8981100b850f250054848214983d900070500c0c25280c0707845000c03104d0143c10351603220305400c0d40030490380b901015280e00807000c2c50581d204103409002c5500740107003039442c0040707103040c01e00e008141102070300041c0c040c43c400e404464015589981c1125031a8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 679254190 1250 679252940 679252943
    0x30e0c03010213180219030b090606030115030e0703050114071202040e04080d0603080409020c0c06040501020303190e03280f050d0e01060b07050105040c0608040203031b0307050601030c0906080a 86
    0x140e02e650502120461099039078020b4030444005241c9440e5038240840e0303681b5800c03402c00080e2110b0880c0e2050418902151300000140c030403030b0071175041c100c00900c1c14080c3d0031108101960b5501070041c1190400c41e0310001c5070010000c00404aa03031f043e61400d03100403680c0c10003156000a0000c81880320784204c40885041104004907a15207542d480400d0703100954687e00c0f2503c07801c012020a81280c0140014903e501d0010383c2e49281e246c0c558140380c43c14a01d1445010240800c00851360040100c0754007001c0500120b200c0301d07a1085000050080b451403d4940c070012880d1954150079007410608500b102c078100ca2414401107003201c001440c290140d00260080c040036503421103581050803603001c140d00100da030f60b80303403c1c41e8480f43e00060001d451a039103c009100500000c40b250601402892400466519207900802c0e07076846428002c031b203c1000f191402200e800148292140c0c81e0b8003d06603080c0d5607407810602c0380c180c00341c0a1041d07060b240080000312204000303100e11016 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 679255440 1250 679254190 679254217
    0x921050d050a0c0810060834020f0705010219110303040b0a020102090a090b012312040c030201090b0a050313030522060206011221020c0316060905011d040c1e030e0c030102 76
    0x5582d1548c1030461015044000250302401c0b0f8400c0d810410020108803607505a80e0003030265102d0805c002e840d10310541d0240381990008411850b024510940d00060b02d90070020001b041c4201e080400e1652040d680445004640862100a6207506400502021000300c4a44c011207445e000503008507452030440c00d01241086422541600034096014410515800d20a0801e4001c00342e1103e1200b0855040310303c052800d10900440d030304040310101070030b00140305031305001044102606030b20000c0c1200d1458458881460b00301882082141c840d10210540314500c618608494110346516000e0400036005441c00400c9000b0030a0000000581142805000b03296013401d5a4042e100320f515401180503110420150b80c904102d800321466564100208a51802e03000412072405500301074104203540d01624041000b0351070b82c10b80c000d8110340001d892400840282c0b0212010a002d145840915140052068040d0f000c1c101900510058809201c1c7d0380341098204e129440101551 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 679256690 1250 679255440 679255457
    0x1050306070c021906110d0503130807021c08070b06120a020f0423040c05030102070309051e040e030903010e010c0203030403080c0d05040b0a0f0921050d050a0c081006 74
    0x5441c401c50202e65490b001415000c80f1050910484040c401c0580140b0040b80084101310682c02003082040012005031408a0860406814000c043ca00ca0800541242c1021a4070401d640e198088440c0c955403524210151840502d0700c400780390060b030025522804104009185410000381c2c50141c5c40702e0001500d045403441d805c1110429a10954070382203540e407840d0f02280c8404040703070300240d080900c0c034001c2458203150114110101d6000940a81d00500c4100002074211014400f90340b4111010700b202c1c032241034000c034040d8130380c1d00d0142d010313040c01c02e20b0210910104c010800450194002d101c0d00c450741410500f690f0a00400303d00507402040041c1c0400c0c413035085507410908010400b03140a4411050b10180c1754245c0f4107403510020703442409038100041c0304848003140b64820038048800b1a48507114008030301c44145041c44041d400802c549449207040350719990300a107007002141888210813000300f0a50903d074000c640300c10003098089041100400c00c9504582c3c510b481d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 679257940 1250 679256690 679256701
    0x619180608150115021b1507050a05010b1e010507060e030c16060201200403020904050a0b0403261023130e12040f0501030c050f0c0f0c040c0909021810050301140901050306 76
    0x8015807c0942865010f0900039500000c5040c0062203407180a0800414484000000c1248070382d041d8a410a0819084c00710120a9030080c05407600c0ca03030031548c000740b4002d519149905510a040708072009016405aa07001644412025829900782d0f0780200503204242846502c00603104002440322103085c08104018904101c0196002e0700c00c0c001d5a550f0784890365561503a01040d64118042a00d001007031720040c01ea000c0755030184a4002d5454118209034208241c0308450380035020200a2041d50f00e802174054415610306148058002d815940d10702041000030009a0103072400c60040c1030070408a1071224090b80c0035200d1200c005002d041c41d2100540080440070004000e004080c02500c2200c4215000341041417808800742040142440c0d0081c2400b032134614462049240c025a80c806590040102c02511041c00f401a582c1c4031902000103441d000c107010540c0400c01741d922403006603000c00038504031004202c05a2414680800300643c105003401a640c040e8030040c0082c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 679259190 1250 679257940 679257949
    0x2806090b07111906050d0f09030e04200d05010f06020708030a03020c07030807081c0203190902060f04081c020a030f0309030c0204020a170619180608150115021b 71
    0x21400c020090002c2403c101e411440709088400350712400224070302081004a10354580104800c80031006000c003e002800e54014080f4034000e0541c0d40900da07a03034a1400c001c9522403a01f00705c1b80303424001c1a00d8211284074600606001d00503101032031010300380003a00d20300020b0020300f5514440080c500b0200907440490094001e106a800c15104840000010402d000c00409140e070080c08565502d96000742054100111119102c007043c1c810800c00c90844d042d00700c186e541140081010a4450440c00040c1440c0142c4c010102982400140050140000035803018024003110004641d440121426a00c41700d210303001030042a203207806044500e01c070341d20200c40c5034401c4c01c04044c41040f81d004034049070403080c41c0c0004200b0030000d842c00da5074080100c0340e1010044640f44003c000311888911014a244640701c2c0c0d071907010400958802a0341c0010340500407180480d032012426030074035141d011080c07090300001041c1c0034900c6440341c40442c2144c5100281d02507600a1260f010502 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 679260440 1250 679259190 679259213
    0x10050919080f160b100605270405071107080d140a0c0501061502010f11160305160b010f081605101b1a422806090b07 52
    0x2100c0c00041000310300340c030300b92082c05400803680f06626501031000302e161404106602400b6500c680707110030800c000f140d078002c0c1121400f20728040d040072031701107a54220310084820f80d04217901608100802c035400b5031000d207125031501d4110842e94150359409140c3e03218101c20f0700d2000041d808100c090041d02803030004121280d0b00d86059503640c4500d4171030304c0c2103992030f400803840095100b01481c0349680c240030b400e08284003d00c0c1003102181d0748221020071311814400c804030b424115808014980564180d500c1000036007603845010680b86041c5000d000240181e42c400b013059038012480740780000310348103103071410002e48640b00d09120400031110040c283c0001080310415141ca0006080011142c0b0144503042c50301d4640900c0801c103010a5000b040d0384c6086902105501402000c0015407014807281000c00c10601c0d09594a04000001c4014240e0003010620b002441c12000903134001140702800e50301c9402c542c8445040352200c4040c4298400320303505101d414081140e52008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 679261690 1250 679260440 679260443
    0x4120206031012150b0a050310050601020a0f141507080a0902031002120115050c0706052503111606020a02060f0d0c0206070e01020703020d06051902040b0a0210050919 74
    0x1410800c03940c851a1480b0083c000300b08544004020300349501c042c806015100b00080120391020710715040c040800d035620b00e200114004aa02d490101d000c82e4000d2000380310440c0c0068602c4060030480c01e02080114100f0b24507649032181d12689840c0860500300302c0e00a20841e552200c803503d4201001018150408081c0e074035004590340344156841070303c010450a081488072a8140d032500841c64000420210f0310f0051203420402d2031031819001c600716042c0c840710700f0060b403a00030509070005858120b80c00310a02d09003012034a424503801c805403030030034000002120410180518810ba001c02144aa0809030344001007050040c50034001400300d0204055115050852800c40c0d40151205900e1590150b0085014400b030103500000792200b0b0b003800e00050003041d295901144410045440103001c4030354850105010141d00c0b0b58643c2c4250f100c505c199110b94403007140d4081c0f0391111000201511401100f59400b04c1f007809903610501940e170292601d045c603c60058903011100b40d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 679262940 1250 679261690 679261711
    0x5030a1a040311160504060b090603011503060302031504050c010e0306070f0e091509070801031a0423010f0b031515030a0506010f0314010b1e031612060b060412020603 74
    0x46154140750100041c0f140740500c1c490440d4010300e480d0506c81104c01d160400440740004000c1c910301502e80104890440d403a045080f600424042c904800a0201e600003e5040c01a04407480c4c440e00320741d0fa010300444c01042980c0f885040d1100641320070a084010342c3e095040840003035222130181c0144281c8542605100c4100003205000030703001c2004458990b103c80403464400c40d40d04040100e03503480645810700f40455411a203960007100002c50054000d01c0480000804001118041d03046030b02640c032052403405c09450aa40c040e1401d008031030009440c001c1154018a40000c0c000c0c610f483d9103204000c0390700c40104590040781d402c803000760035114000e510b10008008000080c0280580da456443d0360741140380600b180700c0034500f02d5031180c2c1800350f2034000d607072411050b0780303000f480c151441811400200841c0c00c00d160480e03a00c00040c1c03101000204a6420808844c401d440b0348020003401518908200c0c1a01941c040e000b007801c4420b1580c801414103200460300403401c41c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 679264190 1250 679262940 679262957
    0x20d03140d02040f06022104150917010b090c0a080406020d060b03010b0306032a090712060e1803072402090901090c1d10080408041e0f05030a1a0403 66
    0x2001003060781c2c440c0e070000030b0600c03004c0e40803c04075605101c01c00e101c07440d140d4400c44401c03c000c000211801140200714810b14a030b140d41681d0b5018108000080c0a08000e83c0c80b105080e040c071900a001c19a400c5018ac2078040029444081e500201e508001c030544030000d59886a41300d0070001c3d0442600014610740e242404614110340c0c0015500a001c031030080799a910f060814182440d080017460020942d41c0b84100f242c1c040e151040407294803054448010664584508643c210459144414a11300c1d2000c00b041101c0840c140600c20100203803152a05c01020aa031035403849139040103421900c4280b00d80302d2050000c8d00c0030340b400002031005810903a102000a142c84400c1c0e1003049c003142e980300184540c64100308144011b0075100180c82680b00343c400800c202c0320f55070498100b04109000000e00708082001a00e020b07207150740b01e021444541e0402e01817107140c1c43c040c00e0518882584002201c0c5000a1040c0c403450b4025282150f840145229184050016004800344038458 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 679265440 1250 679264190 679264207
    0x1314010213030f03090608100b0a140d14010b0c072106020f07030e0306010b040504020904020c0a0b190c0e040b0111010c030b10080121020d0c0305070f0909020d0314 73
    0x10212a0282d0700510071040c4141c0c1a28001d4124600c6520210030b12001c1c41c10061347c1650213900a046507001c06c1d4260341e0b2000c3c95403c07542c040d01c655482e0004440405e607d003145400c3d50014440c0304035072101a035143d03243c0c01c074207010380100085c1c0740403076011a206014022242c105100c202c800f00b2408807403881c5a96130038003641c2250f4100d210880c404030303901d0180b5900050381c580103002035014180e154101106055030303104500407640525000102541161607a5040300c3c081404142500e81d540241d162601c0d13000010f03079504050480c40341d41919070400e5031250440a651075120080c0d24400c484c14040a0300c0705185036030503c000c1410070480f0440c04e00440340b0440c0030396000501c04140d00108544151200300c40c0003000748200041c8111000000f0107e011418207860440d140c01c51b1000800381440c1e440000c00200c19408000100200066030710192920004058049a12043e4800c00c5445829010354491041c0c040d50010a02805040350b080419018003407604118 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 679266690 1250 679265440 679265467
    0xf090e09060a05060409020f04050606040302030609030d0b010f020c0f060f2a160e130f061401090b0d170f041206050903130e0601050918180613140102 67
    0x4685162507038201ea4104102aa850f1003403590040c0c0807a81004001c55580120b080a001ca200a5018654910208003a503031422306540c0110b0f80201120000c2c0b42c01c0381400d4aa07001481000034050501c844040c2d036602411303010311a015180e0040c4402030500d0200403102c40b1952045801030410050304034040c181d01d00818014810404110301d9010104900e00e00c00902409401c5980007074a07140824002c0d81044d50445074424280c29007603c60800a400601c203064000b81041c1800d00d1031000c00000750003c00c203002d0b105201030020381c0c0e10b80d40f0109580035240100d60040c1225580b40000f01200d40c09260781510050791410182100500b4000c0d80c0190040b6a0000801584004102050248603407080d031340d101a609048495514841c1141349008401600703030300c01d00252181c0d1054050340d0b4017600081c44082c0480392415980c04210058410703c100b20084144800f00308000941e0b90300607803062044004a414545034944048411002080295020440c25849076031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 679267940 1250 679266690 679266719
    0x7030b0f040903080910060b090402030c0d053102090f04050c0307140405010f0e04120c020402030703062102010518040e0607110f0a0519021c080a030c031b0f09 71
    0x4283c8694184d070900400c42854180c1c17000400c168582803007803d00185421100340c84a41c07005540240c0c4984030303020015000e010365120030100a140c4070402c000c1101042480f00c141551074240e0452400c090000c03502d59181e1000690012104000304d4511040d001d12658010f0140041e03d10350503c402c0040e00f080d210b640020214000b016650303540740f60a12519005040c0708500501d032501d050040d1111610003000a480088281d401a40740e5014101520307640d0f60040c0111342c0c07440c01c1c4002500400c01d80c010380c4c4980d1201004811b050501211010035507070161501824801c2480c0404602d0243c645030315041038460421100e4142d08110300c034014101602d0b900c203029115a0700d546858200503140440381d0200c1c4c5680c01041340800c180b00f420b44010b0645801e5216400810741901c450b0501e4083c41c4070344d01c80312091081c200083c0c2600c2040340c1c0d0911603201ca151048041d1075031038245889001d0a40f100119207800381600707a441c003c050601b45c0310107a40c1c82101c9442c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 679269190 1250 679267940 679267943
    0x30b030a030e030c06090a0b0903100c0804060f02090d0b1801110306010e09010f1211060d090b01050d03080a2d09051c0c11130908040810020f0307030b0f0409 70
    0x2d0b48a0b081d10124503003480500b800f00026200c07a824035003500300080e01d0a4840c80385050f543d000160400d82518207000c076050003908000180070300000340c1c1c0000d10b4110304032003d1700d0540c507103500101c40c00c169008566001d4002042c9042c0706030191503090740550050683c181111000980ca000a41c081c021740c440403101a85440c1c4a140810014102003002e0040c1c0d40715000702e2005204c0c031060180e0200c20f55541000c0209850440c2c6025034510072200203117580f189000c11003000d8040607421280013940304054501942e680d400900109080c54900200450540400500d41c00515402061841000040d8031110b03c442102150490103043d10000c10540342d60110080c003104200480c0c01d45041d0004a14540030301700020a80070107000c009000754825100da1440b0380d9444001807042c003c0720820016080b480c50400c4681d1b101e071045050502550300075854404403032096580b1000d20655007442c560f0703854801c5004002411031658868184101d1502c20303100c0d485285040c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 679270440 1250 679269190 679269197
    0x203280b192102100f05070f05060a060f06020c120a08070c17030307050d020c1f061d0105060a080a140a05090c031b010c02010c050111041a16030f030b030a03 70
    0x26420071048080b01000d00e061001e820051506200058861890f41c041e5204d491405a0f9600a520422607442c4281c081c050038581d80e0060fa441402400300d20103009500d5640d04208055548200342c4400740c0910803003001da00310444000d001d00f443c1010044010301801641e6079003031036568405058111140c2914000d2940d00306000303010000102c00309848030040158114601600c004040788540c0c02c0c00341001d0b03000300b400205010100050344007a099610f12039528658007c0460090906110300040040c0700030170443c00d20744d003034400d605880c0050041440c20501080641d1500000750084442c1990754144042c55004000d81a011b01d00c052400b041c14244889601e14000d0307a40101c03442504042c2031a00c0d0b44024172285588600282803021540305580016113001c01d6070007010b841ca50812030780b503031000e8007200104240d0391261506440c0701c50503651040b5600407007032400069070005045001084c0260343c54043c1d50564030340400d0034103552021034207003000d903203048010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 679271690 1250 679270440 679270489
    0xa0501062706030503040b07080d050a0510050109031a070207151707020d121d0a05071d0f070e28050103180b01121403121006030203280b 61
    0x81e00e41206100301c0950700381070900c00c2c80c2c19511099103e01c241d100e004d40050f0002307840403c001010007130b9801c0684e811800c112a01c0e099803120040e040480350a44968107005000c54070798000c0c0074035000e80b600485015070603a01c0b550700084001001d0070501c15032159240000301c0ba003039802c95410301d0500d5500c1b0500c052505404902c0382c0310240410056400c100d554100c045d90212400215101d460790104d02c1040d83e0f1807240c10303001f89941754112070060305403400900c480040c0362821140c070045151500380c034010741c070001d42000b52a8001594840b03c040340045214040c02c40d000c040040609030002040b14000c1c1404010b0500c020b0501c4046408024543e090b118a00e1100c8024140d200c40315904c0d603c020f11420140180a80d080c941c59400d01032014822804d180c0c07200c203170f04583d5100c20101c9440140039048412101403810080b011444038803900070341e0f004400103091100e0040d28541c281e201d4219407000d0a411a41d14818041559203480001441100c2022001c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 679272940 1250 679271690 679271729
    0x603210206070503091020131403031c0b011404090f0b040605151e0c0304030b01080a0b01051215070e04110708040b03130c030317070314180a050106 66
    0x41207401442c070428040b0500400030985800b0034002100d103113008001810a00c03c001c0803201d0311800031100c0200d8808a6070101c50010201c6042c16a007600300004140041081010b940b071003a42c113400003150794480c00120903d15600294982c1c1c0050400348004060f640c0c0003c9075800079842325401c0780c0c4031740d000c42c2c00822500c950f00da0f0301401d0324240006402c0001096030301c602041d100040c1000000d9440103440c84a80c1001044500300115544180480545039240c1043c001a54814891000003800c1c910000342d06451950101c41640280e282c0b00400403401001c00c560010750140c0031a00d0b07482015500c5040c401c600e41c0d201c07242d40a0016041c40102c03181c1414658448404100d603202142c0404c0944040340e0000d844541d0700d81d103c2f04030003072419047c28020000314040c2804070801d50051192143c5d01c0680c2c0140910350f9800004409540e440481030702c002c4110380c08513110100300220342c042c100228003101c14003e11991410b08442c0c1540c80325038644c0d4101e07a91003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 679274190 1250 679272940 679272943
    0x80d1b061a090603010e03030c07030e09070e1306032103020c01090c140303070503070b190608070e070c0b060111030702031504030f0807020706080a060503030c010b0123030f040606032102 83
    0x30f0300040c0c1a00200710100300505560780c1e0f8400541343c100301180224000040501c2052241c0300b00d0b50180c0b12560b2030070603000c060000461094294800c1c001103d69003411340d818450113003142d0f00820400003180100601c3d03000000b102c50b1090405400300a41d0940340003d001e01d40c001d501c200c4256003042e245c07c42c1411015002d40840744203802c10007040001c128008140c4a450341c01c10010151034030b9030000c0101c41902410b80802141c20320600054200000c207a0100f25000700e4681542c0350f981038803c61700700d200500010851544000414040d5105081041615805c1402c486c0307440f08980001e407415028038502189003d80320300300b0040552003c41582c0220b0f113070420400303500b04181d000c0c1d240d0002c1d0141c6020804000700144484084d90485001040050280c994510090540a02828000300d419001c2120b44015040e09140d4402c2d80e90b81e842c0c81c1d00c1d0380f0b0442d1214444101010400f61060701c4068a8a10110202e001005c00c0b0040078003259159100d031640440c0030303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 679275440 1250 679274190 679274209
    0x40603360b090d080a02031f0803030915011214030f040f0302040b01020c0a090506180406020a0e01231b1509160e01140a09060803091306080d1b061a 66
    0x307080c2038000c07480b0f440c6000d4000354002c0e08100c1003400542c40e551380c00014401c1500c010850880d0b0a00d1500004000c08013000441c02049020305450464003007400e11100080203210b03110000540030400e02c0814242e02030300054602c0401035038a0f15401c20030005071500543c01c2868010290030302003003145440d104000c0e00081c00e001400f44502c85000041e12400301d0310800701096119000200d00b0703502d94040c405c0c1c5c01e00ea444405040c0c04d00d8189500250000100c00c400700c0c50190020310300750700440940c0c4280c43c40c0c58658080213140e42078000d058000c8034507620510300401e82201c120a09010740030f503007503015240020a2401508007032816400c10b8084000040c85c1c0f4040c0403640f41c03941c1c00d0b41558540e1a2590340300700030f500032031280d001e00d60104080341e103850b201151094000c4004c02c02590129141c0040070340c040320f8030b0201c601520855055034001c100c1c00341e14a014802103451003c183c042e00d0003400301c64840c0c42c00d842041c2114040001315401c10034203464844010b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 679276690 1250 679275440 679275451
    0xc0b1c06050414010b0d020408120904050711030d020c0a1406041a04050c0f01051201033e090601090909080403060501080c0906010e0301180530040603360b 69
    0x40c04000300c40d8040c08800d0106004110702014001007140e01c0001c6d0b40c0454009142e0403040715190342441041240541105801c94072442c1401e001c01d51040c85204101e4203142078a01451030001980307000002940180c0e01d000d8240a8411808040b40d0002c20b001150b41d0340d90007400c985c1c40c041c50b02601551403280d41e03c10700c20002c414003001c9200050303d941215000e40303043d851000000c005031011b00a038404c1d50489500c113400481046000d81008001150704e00445001c203403942d1140c503100800c039080c58128100c241005101c4c1ca404100540c1200042c1000300b9031742d403070b680d240c0e060715010881a030302c05400040410030000c00b403103801e00429401c409440c1d84062035000448005020300502e04004503804861419502075004104c0d24a0004030500c8c214a1072602e0340d20303004510500600490715094a070000c500000343c5480b100b02c140e0301a840c05091050940050504007141e0100c070704142d80d444400d400310507404103098070420b500d140c4c0c40114580300c40a000e00600c3c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 679277940 1250 679276690 679276699
    0x15030803100e10050936010b010507050c0d0f0807030503160c02030309010807180e0105040c230c010f0f0f0f0c050906161e030201050109090b01120c0b1c0605 70
    0x10009042e611690440503110101e40c2c44026489045810074421007824048a41544086c0180c1031281603d0540c0b4190075900001d01900c135003900151014040c60501401d203410503698642c5600c0c2000d0b5110720640301d0a40110400d25640324846139070081502240403503400030a1050a010f605400f91400807170f0324281d50059650341c08241c0f40d0090402c0f480c140103038040483c034418007880c2c0380c0c2030100300b00414880d090303941c1408211a080030322a03540901d2a004440b40341030b02c1500008500e940d03d00b141c2c1100004400380083d00d41c0301442c0394406568510b100051082d0703500070307140b280e074003840f0220700a1280c0004e44100e900b090b6036003440c60700c1d10382004103081e004801d8403956402143ca480c1c45071514100d0301030250a40400905820007080b0349040e050100014801e468002e900801560ba2940442c0c0c003101d0303035041c1c09816050305400411006410005c4542d205203e4420007510755a03d000014031608041000307484041c0050300701c02150740790b104840c0281003c98 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 679279190 1250 679277940 679277969
    0x10602120f0a081911070c1211101704110f0d0b130c0b070501020a110703150c03091403030601020d140a0f050f12010302270c0a031503080310 63
    0x107520120920851000c4020b02000b000041c0c10801030004010043c4d012140612071030300b201e510303d091644004021242902c06040c0400c1e140b40606010a20607400b034620f00001841c03904204c00f01c04039008981c20004224096903040540340100f0b40184c0c8a4906002069841000c011440c1d0507950b00700d0090041083c2d1002141004100350740010078070018410303968940c100043d02c46101d401803940e43d0300020350b0310204101580180380d11000d507514075a0781000002c41985500d990300c03003d8402c01d0070100080c0f00302c1c030b142d0100c0e01520b514207001412400300c0c0da0748002186100b1000009810100800c099541c040c48a03c4000300720345450301c0c1000c0704c03581024050080301a0b10080002003e02188202e006001303c90342805140351140c1c640d10880c0380182144002d0108034050a080104010019050303031011115500c2d452110010303513102c1c141c0d0640c6411040f0540d0401d071b1210001003014070300c4203013500654007c0c0000c80ea64909041030308d584c01802ea10050354610400c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 679280440 1250 679279190 679279207
    0x31216150213031106070503030c0a090f03080403030e06190908010b01020d02070e04060908040f06021504030507140111040b0c010c0e0a0e0c04150309060c0f091a0c0a0b01060212 79
    0x40d15030940382e1001c503070a02042c800c0302080eaa8046e01800900740d200001c2880442e43e04030f405030100100580c0c0310403001d500e80445071040c0d021481b004001c2e40082c0030510000c0c1c0a40325082c4180000b9101c02c0c00c09603105101e20007140d043d401c0701d0210b80d0350721090103203000c02c1c040c4014840c3c0c280020041010314000c000d44d21a103900c2401c10303070055140410300308480c642112080301d42099a4a403540c0d10b500203401206190300c9040c1c058030032089803440746031103011464840c1780c00d078840e90705200d020303182d0052240c125048100d141d561000d00d401c4089152015002602e119503543d92100d4441081900b1264084102000d01c42800c00c20b2219a5407020300105a42c4500e08c600159203c040c5074000ca40a01d402056102c0c040c4220b41e100b07241e155000e44000f50142500740300030303035402c802514040e8100c04884000b480013141840100340006900c407103100b043d0500b910740545c070314611b402c0800100c01120001da1280c0100301641c0d040240340740003160680a0f41ca41141e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 679281690 1250 679280440 679280467
    0x30b0306060a23030a020406031a07140901080702070e0c0901030b030c150726070201030c08010f0b0c151806090f0307060b0d0c27180f020312161502 66
    0xd81103d1074151501002c20242d84081c09180005540500180000c0d40c0b42d2030314081c14102c60424101a182000c001030f003552140b89546100c1d8a410b424624011300b0200450b54100014010015446569000901c10340114115403040840400c025112846d600c0010140e80000c06414800d500444031800c503942c8141d08109152404004950355000b5171501101e5940c00100e140c0004003010030000306803000c0e80017001424401d980800c0f520f0b101030420f580b80e04081c003504c00d00c2c0b421340500f8880348619100030130420420340d0450f4501181c0300140000d50204981c0500641e1805010002c40c107400c1100c030b41c2044d100300242428102c024030103950b038050070304090711483d2143d02c90000c90b1074069200b038445030881103080303880c0c0d16440c012882d0489006400c0c08a14888002540c060681c4120404c080150a80061034400e40d00c4900e00140085d0301aa2700d401010100c0300300740011401004030080303c4503a840703004c0306414101c1c00340740c106c00c8081015004000c0140414607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 679282940 1250 679281690 679281719
    0x901020c061c09030c080301060f082215111303050106060908150c09100804051006052107051c05060112030c0b070302040b0c15090c0d0303050c0702060a030b0306060a 74
    0x4000c00104507038070b404c007201d401441860144c000c840020011681e964000f4481d45075441644541800d52504220075a601c1c6070084614000310b84286150001555410300202c228085500464024845620b00b41654081ca41030304d900200202d00300f00308403003801180028103407410035212151030f044a260302c3d0002d00400c00c440310001e07000a0080030080082e221304d810007910301c10504000c2d020241407003d096a06480c0c900c144101e406c0e510010b4080c050a80304050541d040742d441440e90750030b003000c502c01c4446c841e0140080110341034031118a01440000e07a0040c1680d1100e890800904051040c0c206001310003070b6020a07004240c100c00720900856110071944400d0390340302070480090040e90010803161500040c0501c014000045002d1459080d401840490715002c986540d512401280c642d0400c00011003480807034060b600c121790248081c0707840380c0350407002e81c00605170358001912540403a0351805003003030605042042e11ba0015058952249240c00d260510300e0064 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 679284190 1250 679282940 679282987
    0xf04020304080d0903053a0e03160204061a041503060f031209050301020f07020405090f1509070e0717070c0c14040f050a020c0d0525050c090103080901020c06 70
    0x1030b1070340e0300c0f1400c05219404451000515a1f43c1d004010a0262411303111001c120503075514100300ca40d50013203000c0710300c504070802d500b59004620300440c89041052111040000340d90223942d4590006802c0c81e201740c8a01e084030000031550f0343e181040c00088030219415890360406141003818440d5030342c001c5125043d0fa411a980e500b584c1208641190b000c5000d07005603805500125680e582ca810b03010180030b2980c802c450034803456981f81100384d80d90044d0300f5681c01c183e005181c0204401c0f036003003401e5000200d040580740d07000d80b01c03441c03507151107000d031100000941e1a0381070b00c018400c3e80c6c841981040c001e203403034480000c4c0d580b1520010802c40c00760000d0242e0f8117207046110303920303580b0240f1a000d0700b001c1131100780b602041c0744000350015201c0b0b030060b00a000032061410b121740219120340c0c1c082c1500031000d0f070a0403004c0d841c0b40c48240c1c04441078400e41e42024143e98179a26003e0086105248031541c81011200080c24865607082d01e5010311000c0c4468100318010039041c000f0030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 679285440 1250 679284190 679284217
    0x6030b12100e1e0c13090501060e0610030b0306070c210e041a030c09221217040b040b2d0a06150207171c08040209010e060603040f02011218020f0402030408 69
    0x381107104c035245c000e00c1d81880041c080e40c030305000015010300b10740d501441114210340c4594004010003003501a01d400903000e661540098002810582c00b906000391428005c5c0100034420a140c403108660000010060010403440c258032641450240201110080c59400107d00c3c0540c0c00040395413114080c220318850341c0704400044221144c40202884205034801d1959982103d051400d5100f162110306000201420b410100c81c0301e0641102e80144e40c00300602c6103035079403a11514002540030700100c0f0b01c40e182c00305280742c034140780440107481000081010000e040c0359402100b00e411941c00b500c81904801110842c40340c000c20740c0011030b81407240110700e203641e0309445400c140c86500380c9102c030003642c2c445602046c1d012001a108510036603620005980360000c035004450100c40d0154046070410025000881c5401e45800c01072060402c02400c1c0340007100a0180c03820500060300142d400c800c14010f500d40055403140b00c1d101a90700b1403850034240c0350700c805031003180c034844680d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 679286690 1250 679285440 679285459
    0x209060a150804050f19060c0504120818090c21060105090603040c1505030702121801051c2d2f0706020304030806010201050702070e0106030b12100e1e0c 68
    0x1441000d100b150310508900080d100b01084000c03d041c40d46c03802e40340545000d4940440245500c0c02402100e00f607416030100c40070251030503959414207921034600d8522210300600c80d5103440d04c502440707501901c0201565034a8141d03c441c17000510046000762030b80c50040c20240006641c000b400c55a161300b042c3e40c016941e60701c41c20f00d40500c244503880480d4800d0a0100741c01d64a5000000d140103c60a909a034034030400207581405a0145000030940c140c032502403d807013580541c0c010040807003c2641c1c14000b14404d0382d41421181103c42810080b0b00054415050380313091300c9204510300e030052003080a014207003a0580d40d000d0f00d03009212403a00c641030340510010010251001c82da4418003c0d95a032405160040404805803103440c05517082101083d60580081283d0064802c1c400700c0341c0b00c44c1e180503400c41c00b80a078464502d40041710b1603d29950312005010200c001e120049004c548081d264800ca481d100e41042d01d40c0e100403000352034900c14440031411840b126802ca640743d80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 679287940 1250 679286690 679286693
    0xf061306080613140d0f0f02010f061509080111090d080c011a0108012108030c04120f02030d050f03240d0302010c09060212031b07020306040c030209060a150804 71
    0x40c045600455900d1150004110889554500c141d50f01446030f2100c120401034000890341d80c4854620792408102808a0140400c1c4600c44078840301580784004901d491410702404200c421075003142c24699200003808098503003200d504c100070320711180204000580c0401d010350302e00a601d0003600c54201890704205001c2900d0544c1d6082084900801042c030500c894a410740307251342c4240e8040ba03140300002415190b00028070400c010f10009045038031240c3d41d03400c038003a03000400050690806000c08510410500e01841d803c03071085800000c5010329004052400c0c1e043c0308001c00300141081f02042129100f01626004120390400052000351041c0092006440b0004107802500c00d036920800e140c2d0540008801c03a81c02c1e1196040a512444206d80325410510762440c100740800101d0b030711a01100344a6840101c82151034105002d0741d00090402c00207950603140d03080540c0741070041d45085880da68008108032085c88650b840c21020b2800c003880194240c040c890820000780 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 679289190 1250 679287940 679287979
    0x2a05061c140c0c0705090705030711160b03011e121511070812150f091305120c0105010b1309020a0c060c030f140138120103030f02060f06 61
    0x20001c50a142003034068580340d40c10800310b401110031408240b00c1e81ca000030b032038105442c0c401c1c001c0c2ca85550312851995aa203095030201d001d0aa114a144640f42004e26041840101e001c040c1549152160b0360794904901c40039160100071000b046912002010400d90910806401a15030320202600901d05046650002081150150000c4032800038045080003c0080201448a00c4003100405619403552640002c003980184540191710000740d80c03601c0c81c00f1040c0e95441405031a0406c1c000e82aa51680e0905d20a0f0405a001150214412a010400b80941d0b030152840381031103810004160b0020130071090502c41c84062a07400601782400c00e03c940741c61241e498100304184200c40041e0710080041551101c080070851a0a01041500c01c80c0b041040c1242c0c0080c541d00646454091980e010150070010345026090810b00d1125a0100b007015054049503040c504407590b142d41005080619100341400448d0004d104200152000d804039a800000c16140032410704401d01110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 679290440 1250 679289190 679289201
    0x100f1802220c030e0115062304120501050105010f020f0d1103130f1406030402130c1b0f29221a0a0b030706080109050402040f092a05061c 61
    0x101e000742c24012240710064140d04580007580640008100c0002e5224082c00501e03254012a030020300200c0f861402400d40c0503641c080e15140118892038181d4603200861342c2034502c9000c540a94441004018642c0c020311000b200c0702c070324009440e4000200c801c441e150303003400400c0010701018580c1c1102900041003a503540c00810080c40d030040d0346400380e2412402461180b19001e4914121400310f500308542079a004543c09460003510000f451290805042206002001c10040001038040f4440048203400c1031801a0f4040e84035042600b88200c400826108030400a4044051200c4180400d04016885601d180024070902d54680610a02d01e00a10014124043c550311860300c0c0700070780c40740c82e000762800b8904008541c850414162030f1151845680041031050700100038603c101d4004a60043c80207000059410f40048900c08803440c000081d40c0403082c030008ac65200c00281f611f0741642003241c3c1030b0307090b8915160004079188651160500d40e040103401105c141d20341508907 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 679291690 1250 679290440 679290499
    0x1b0b0f0910090e090a11010908150402220f231f050402120f10030203070306111204150506030102130311030a0503040612060b040b0406050304050f0d02100f1802 71
    0xf0640c60a1440b038043d07441002c0e10701511003443c090350a80c2c0c00c3d07008801200441c0c0d1264007916810007840d842c000b002500500c16a0001201840b009020000096038039010650301000601803000d1031a05c42111441c1145c2ca4282e1001000360070f000c4200e0410311380c0400c00003e0300c404040d41e1007118014071030550000750018004100c0100451012100c18421240d0354000d101994500c0c0d4144011801b500c00650141c1182d1800c0c0b02066868000740010760700500359071b03d0540b00350518a12002d0484040c2c40040d8016512807240c00d080c0601c03900528110000d505240b40d81030a00e010a1940c0f10041a54a81d015a101d80da10706001e4071400356003080540383c5550b51080c01400303c00c0c03600540080c03540f0340040480c06400ca103043e917040e604038501a50902d401c00320705842c10740c0058820f40e881d03c102114510b03078070010410504038265690251010501000d1130fa02992120201081c0d03d81c00e00103030700d600c0e00d8a82106660b25404491407120710002209281860310040c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 679292940 1250 679291690 679291709
    0x91203090a02031212180a05030409050f060405090706110c04090c05090109090c1a0702040603052104050303070206071a280c091a0f0301031b0b0f091009 68
    0x400c8031290300401c4115500703000b41d0503500c0d003500c942c1c00f030301c4a4819120141c1e4804c8006000c9000380310746400300c2c4100d14107241199191303022910340c0e070710710f81241c3d00500700720b030702c0d0010840c01c54420280c3c9904000181d80a00480c180681c80c5500d070f542e540540000c00400400e0440b0b001020020854000b0026008000c0d0003403d0400846000541c0601c84c05603040200000b003603205407040643d62a00040407034495814000001c8900c0307141203c8003550441407101e00c000d42d4540c41003200552054004001e1905803020780403480c01d0b04000d00054800034002000180c5022040b036440c503a0484400f540c0342d0103807030840a014800008011150764102c10000c0809242410346008101020303100e05c0c0d00b0341ca036a65002d9400142510000840c8403c0801000b0008986c44060903c412445424481000106c0391550401d900640c0d1506150301081408a20394902e14040c1c80e030260b265203404080c258000e214464500d075180500e030700000c1c1c010054806c80b280d401800f60f0b4807 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 679294190 1250 679292940 679292947
    0xb011b060b0103050123090711010f0e16050a0504020d02040b0c0f1911010804260d0e03030402010807051e0a0e0406150f03021308161508130b0912 65
    0x1000001084407640c4540071a143c0000400d91402800407034640d0300b2007007903000400240b0402e01c160034070003812482c14081c07440c000c0150000d0038020030303a9000004100041045203030000300d1070010807045140c40b0b48004603040c0300c6030300d07000e090509480098401681e90448000004028816540001d42101e804601d610800601082c0864101000e1089400c64210b0940f42880c0115030b03280100100f6402c00070050f994080c3c01415070107801102c640149400e14822101d00d90402e800d080c0c4040d00004030b210140d0020b11a04aa64074414015411460f0950000e403018030b010b0410402e01c000401d2510504100710110012454000d445944a0702d2030305000e0305041c2240c0c1014440c905000c0082180400b00d01040c2103503080c1d41e200300d00304241c3c48017980250b02c1712202000d0000409808250b00787c04008140100100d0003000c12810b20b0441003c003407400100f16182003044d800e007032103580320841c1c801c0f03140d0542141c0582026106c4448851800f4441c0041d201e102c1e2000c0f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 679295440 1250 679294190 679294193
    0x90f030109031d0117070f0c0b070c0b010e040b0606220b0928170a0b0108060f0708070c030f261e041709012d11010e0a03030b011b 58
    0x410303600c004040c0d10f0440c1c0c0780c80c0c80000040d80d42850084000300074032202d90000d40c505215209894040e607613410022500c6525444100d028a0211944004508000490305c1048030034589540107101381120308416007415518001c6142018091500c5000c0111f041d01e4040341c00d0240d4000121901203004405907500d400c10030640042100f644100c4201151410948175400b414856490111031425043c2c1014180c2c403001407000720344000c61080c18800000a10348040c16406840c03040c00405c02c80c9000381e0507414442700100900b00b00710100040c03209854101d49205106949400d0112502107c404c0c11a0a0402004101c901d00344410202e203020320044005809103955198400e4028440100b00c00a0003083e100104103174102c61040805140f0070303000c1d004800f0145401511000c0c9401d0155000042024070b0003801d01c6180c440b5401a001007420540c0d14030380009114031948512050f4841d8681080541416164200011941e20442c848045071844002c85905400076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 679296690 1250 679295440 679295447
    0x3060e072c070c0c0905100b030a0603061d06040b0612150106021e03040504020d060807081005060d0809190504020a030e0f0a0819030b1309020108100803040902090f03010903 77
    0x2140300400008404001c0b0b5800c9120f4000034100c150850301d200340300741c9090b0702c4c04001e110081c20120342d445540c4c004641d00d900480114060756070b48101045150460030807e045580e500c9255010701e540c1a030f8a2018540031651503070043c0c0085240d0b13500d42d90b000210b1000064a800441d06028840c0c502c2002c3e008104018180c0c0c140750b0807034054a54011000c441c548140103084010f61041c00100098030301031b00104260800d070440402c440380e45094452500d14241c002480070741241d410321121880320310600340e10a0f0102c5400b1192401d0703031650300c0e03103119a0307030303c9401490710303134807210f11070b600343d56900001c10000e08110741e01d4040d000c0040040540031000c2400340114180b0383c03441500000c030206c0d225007000b80b0a10f050b2072042c95000c038840540741c400038503858402002c03045d900da01041c01d079801d0010021407000020302c0010311404000781100e1740d54094070402d2164940c004240c405507041c3d610016980c261020009410765050316000c8d038558203040940c41059031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 679297940 1250 679296690 679296749
    0x90d0c02060d091a0709062a0b072604030c0f030306030b011d0c04050f010f1707270e191107050307052b05160f20010302070c03060e07 60
    0x11514070130f181585540004440d030841c0b0f4072a003400142020f844000204a1503c542d8001c9440402440c5241c199541c140711240c040300c1420110300c0c82d00242d89008070315944a005428851207104c07903490540d40c041d142081e4000098a9220081892400c041c000d0b072040c1c01030b540040f4868450742e500c1e01c41104803080c81c20b0b00700b410640000840d028507900019642506c100a001c5a01c00d0000c8004443c41002081e14108000c0361903d10742c4064400d0302118020920703546c07480e0b440c2c13964591005016040142100c0b00140e4144c1c20404180062140c42d00280134042c070301d000112152003580035000050388072405900005488017040000002461468842c40944201c414203001084a080c01d111801c400c4140c0403825480c281d02c5100209000b0003840084490992a80c685121040642134102d500314801214240c603081c3e4841c95241c54082440c05526050b200c0d40c8007020101c40f071200a048035250300008a10800034448480544103641c008402d042c034046115450b040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 679299190 1250 679297940 679297973
    0x1e110f0105071d31050c0d060e0702060105041a030f150f0c09040522060b040501050303040b16020d02030d180f05220216050106030605010e090d0c02060d09 69
    0x1034030192003a0f1281e603050074960302000020039070003407450100301c0b40c081445103d800b0540c11040c1c44140c052402144070b031030300038a10a00d2158540d54100900d03011543c29070009404260742608000905500055603415030f20b0603500410000450745000702c0c091004520b09905000d204038001e030003140000c0d0300305429070b40030317156030700780c844c80214401d03a4425100e000c40c40d0380401240403a4100313900551f03001250170352003a100000d03088184c10480300c2000c0413101e407a00c840840d40c1d14541070040b40d01404044010750314052402c2c00000031071245000b6412000408800381055541c3d0900002100b40c0140c02d803485c100c0c0032180108000007242100001d040b0440003c169003072440800002d440c2c0150030034802200580b03811100301b842d64001d40702503408006422001c0c9503100c42c48105ca00c21800490719500f1882e005054030016013100158001c0c1a0800c40d200c0c1000034482c0c070400c400d003094540007001c1d0000c94881e1240c4d51030000850f0406c0040b0b03040202c3c0c2283c17084801c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 679300440 1250 679299190 679299197
    0x20a0c020901050904030c060203060f0406060206060111010203090d030b0406090606090807060201140601052b0e0f0a080a110705090103080306040c03090b15060409060b030601090603020a1e110f010507 89
    0x41c2c0c0c8502c2003043d192400c2d81e000d000626402035900c0060ba88d82d00a5400c490000c0512900b00609070001c3d040d036440381c0001c00160009418441d255800150760481d81000740000d501f1490003941882c0d4425428a507482015100d141500071500d40758014005495061030502c555516072202400d0034020344180510380c0b06e1054001580351061141000b8202c0e07032800140582c4a6078011215030300404407007044154103203d2401051084c5244a60501c4901e90108000805202071810440ca03100b06c81050b03048021500b00280c4107800701c44d5149400d0501242d42450b45a40c1031910380b45400294026550f04004030a0044850144d03208d154112414007080343c144030214207541d1500350060800050401041c071f04143c1441024000c41c0242100307003003e0740d5501800554007958861481c13800c0010600ca42560b009241502034502820190316100001c3e00051140c000445403070022080100094240c4e4807500018522502c86001c54103c42041082240280030070344400c00403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 679301690 1250 679300440 679300459
    0x2401110d021c02062a090406091d06010503190c0f0f03140c01080c09031f0b0424030803180102070b010510091202090718030614100e16020c04020a0c02 67
    0x10b510002d4010b11170500410180040c80420030703d06407042e01280041070b889070a10504046131903a01c603040003400d402c5800300300e050b43c4211070103802074603080c2c031001500800c005004039140080e18842c5090b030b42c00500704081c01410a903d01d40b200b50000d06505003100c0f000515801c8000080e42503034007940502c2288419046081d030344803182901d083c041400c610022300744000c440302400140e0406026200b0b240d40c12004100c8921100200b00d440c1030f0b0300d401c070005908080c40344064035000e10103180c0c110076545109a003166083d00c001400244000006501e0011811110443c0440c00c0c00941d1645030340d24000382001000d006072030064603600080c168291140641c0000c0720300d8a1410024980d4036000d2101012001340f900c001e101c0307010312014401170f1034903a4030015400b0b4003001807402c1680c00c1c5e00c18a00e001406400d01491107510900c011640010204d42190105070090310400c0c510a0607400e00004403081035029101040c10481c560b0440310403041540300f01c0d02d4401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 679302940 1250 679301690 679301743
    0x103030f02390f06070f06200d150e01060c110303040f050607170f040312031406041a040516030b030a03020a0201050a090503070f0305010f052401110d02 68
    0x605000500001c84600000c81101030201440400e01d001c20300b000d864008040306083c08900194008002119182844550704041c41182d12030350610000c2809004980206012841e07801d00641445106590355400411b120a81420b542c4001300181c401c00700c5150b80d2001c0180c0505030081043c3c030170001f40d134255212468007004490503202442140803c687c140030500405400181003260b10100160603121510f0a5030301500c04003103000780d5203a99034211b140000d0300e40c41030321204084c14144840300a0301079406071801e5001e0015103001403869644400c05840b8400785400740d41040c504028004000a02c1103940122416a10306200140c2c2060525540c2ca550040c0500140c114403800001507204500034511092580751040d0178a031030310300007420f0405a9101c580c1004542000300b003008028000c0020401850804200500d403180c18980c4010303188405401c40300000c203030032015070301500303200c40310491181c2281c42d88841000007a40d5010981c543e4481c11301c24001e07044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 679304190 1250 679302940 679302973
    0x24090305031e040201140703180f0614070f0f0f120e100516080c0a06020408010c08061801150201090c03050d021504080a031e021201050f0a08030306061602090103030f02 75
    0x5000344c4e8103940b003070340307201104850310140c6e04460b004a040003080c00c07000700e020003e40714000143c030046100a0210346081c8001e041c000124001d246840028820705021440000e5560707069074201741c400c0e54180c0d45103080b09030411005001840c09102e0103040c202c0d11341c040010703444518260b81c2c1501040515034103035100d00642640200c41d196065095002900b0480648001c0c2072907022692683d0883e5200380a0785c00070b40101d6034a80d990009206082d60123011640c012506403480103444ca404503550300806014010410100c58444003400039034401d40c041003a85400407400c40b2003a40701d190840d11403880030068401031207039603070f807031040760040d40c02600441d84082c0e91403503c2c42000003540a48503c858200c0c2c011030300c84807500801054001420041c04484050101d581000c0411007400b5620a000d801120480c00501880d0000001c581d0070a00c116140703a160505818400654081128000d4220325807900000070160400006420000c09800b0b460620403900e45030b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 679305440 1250 679304190 679304251
    0x3090d060b030703120203030a0c050f07061536050f0106140f0417010608010b0105120402060f04180f050601090506070203100c0f090b0c07032409030503 68
    0x554401481002040050100d80c07020142000280a94400f26500d84076a4811004ca4802e607000d40c2002003001041c0c200d51013840303108080e601b0318074103000d01d25100c04a2801000310007056103566064200c25211140b10342c070000d1007143d02c101030800c91072014054a151100f541640000200000d1001c0f24060140e944201310300ca905000c244c0c6046411182204a0b04020794502030400400321106800f40060000e46605420a04040000248103084940503071009071640d150182009403a0b80c450200e6545035180711828003540c90f6400099110301c01c0420a0591840002d030001d80d80d0410301c1289200d242d414001c100039080c405001040e15405c68035540002c240710010310480c0f808030044c02c4682e00180441c0c0e2481e00b1102d0380d42c216070340b54114a012851a01440b02490361050b26a00509035980100781424106001280d07510601d0000400581800304d01200554091501c03c51140d00ca90040c000f00e80ca600f000352181e44240c440b1a81004040c0140340c1180d0b000c01c09 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 679306690 1250 679305440 679305457
    0x140f0601050304120309080a030c0807090b0a0e15120603070914190b090a0b030d090b0a0c05030c01020f032401020d0503060418120807170610090b0d1b0203 69
    0x1018550f9503030780c0e1a007006603451310020007032650720300200303001c07035101000b40c400c000854600281002d1840f8002e09003e600400c0381040102c400c3c07040c000c3e0002030040e250303007a103507003068450401c0c081e000078a10400038162206004020420070740c00c17240030011901502046c1c0c10345001c241c6808040c02074035005441c0e2000450000c010649610301c1f142c24400000070048009550705011000420212081e120380c192241c9507100303084146420701c00100e000d8400d080c9000c0345450000c4000c040d00442c0c0e540d0040c032a122801c001400b2040c4200c9040c40c1140008658480c855a400c62807a0029a102852079400410050030703016840410103052505070010514113118800c100d030190b1004002070380054468520f0500483c6c02c05940d084684541c1391020f0190600d0002421120010140c0d4100300441c50319014404c400c0100710740041c03055a4101d440501f020044d2605046988075024a5100007402c0306003c4243e805403040300002da07040b00000ca0000c0d01241c1d42e0060100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 679307940 1250 679306690 679306697
    0x10501020a050d0507110d0501050109270b04050703080d0203150d200f180a1103060d0f02030a0b070c030e03010b130e01180f031205070905090901150603140f0601 72
    0x180f604803d80268080c2803114460f845046103c0c4081e408202c6a5041c2e150886072a0b44542c01802143c0d41e81c0030704042001d50f0308800c40000d900d1440b12822802031000a440960120003280c00e01c1030612014020b5a080500d4956440c040c5500500030340c021122074450350240d007010800392811440c1060f025400140725181c400c840d00e80b1040e2001010741d1542c2c4411017a442400c80d0b00c92486900c1020081c0ca5049003d280c0800b08906032195160b0b0f0300e041480420400c10b0b40c1d66507190301d03400950040050b41e0302d1b499030300c0420b29081d81088040c0020300c0c14406c001c45158401e00300030700c8504c207641c2e48101c810004145420707101d12640d4107a2040c0840240c0c1183c0205a114a0b14103e0140012800d0154412002d527003d0040c1000d5405000580170001415040030300903100c10400c08080006c0c1c03a10381001402d100e00d90190a00c5020b03d00007003042080250000b00901260140301100141c1c3d6030070150040540c07500c482c0c0016040000184106842414a0321440d0181c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 679309190 1250 679307940 679307953
    0xf081501032012010e0601240804030c061d0c01170c0703021609151706130501020712080115170c0702030f0307080d050603030304030251010501020a05 67
    0x741c4000c0c0101242c0d038407103001018050400b0382652055250880201d052000085100350100070070b0a00c1d40503080883c0540084041030b10282c2c02e2090b06840c41514a085010b689451030304803006134007050007410960408120701020310000007071040c80d40c150300407110300003030003001512407c00d0046120380c19540301001507202c4140c1c400400790103200f48140d452600c119502c41000100d149c0002d401d0f19640c82001070005000d08546e00a80003001209103170035540d070360f4107a54041c01400c1c034005400780302d000c80400009406a6a040e540189083c000d06010714004044840900c604184100310b000030b842482e001c0c0c210b010740c0740d0054a03908801c0c1d1703410003541859030002c01c00700d803d4410003187c62540a81403000d0003030385100703600003547e0b21001c100d410140c03040a4110b511030f400400511001070740001c4d032681c1a0914480f41d030402010500420902060010100280c40601e106d1040500d40300041e584221a654a0140b0a0f602e03200120707590041120020419401107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 679310440 1250 679309190 679309193
    0x150303140708040f0f0f12110105040306090b0702120c0715020f120c010c030b031015050d0b16030501030b010b0c070510050a020c0303091c0c031b0f08150103 70
    0x8003560a504100140c080c1d18045056407a0000d9074802d500100c030921101006001140c05c00403003000501d0038801204241d0304000d841c040c2c9889010000f4041000c980e0b0315489139000301c09440095030040300c100709203006820104900b001c00c64142c0018001c0840010303800d0500000c3d1079040d080b00300140515410001c0940d402c4c00311900c900c0643c03242403013071009807404015040107a03184105094031000e01622490945030600604001c0c5814410000900e443c00600301c845400000d2000c144100f081400c07d407052604e030412030f00321540145002c14030503240c407094020b15688000d12100c4182c148114100c0d00d0a000061041c0c9251004000c040c85a1020b0001c0041050940e0f42241e0b6400c0042c08912030080300c00c001c0f80002c9510301d541c980602000110707180c1500075514000c1d801c000110104c2100c2c4142c0c041e18061031010b400d1004004e40030000e143e218801a50150b0310b50b403078414141c1325109005181071103d03c003080044021907001c518820200c590700c416401c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 679311690 1250 679310440 679310447
    0x2705060613080f060105031b010c020f040501080a0c08060402090105091012031709010509031b0a120e0306100308090f031c0504090f020c03040302090705040e0424150303 75
    0x9002168444000d00800910414903038000004021040007003c0d90340c1030700300d8642002030503030040744650404c0c502c0c0b49001a000440c215120400d29040e060303100c1e039100042042c0e40408507540c21074503140011661140c0040c0c0044080d004e41c01e885102035a805000343d80f4001150025040322a11004100b64200201d0203a04103941100100c10342e900c070035003013040c0a03103a1000d5001402145e215030703901c4e81d40b1008a81003110304000b4040380c80c1c820f40e46076036885407203003d0800c0d1401a4120b09030560500c085004c140d8003010003034a0340802400182550540d5000c1846402142c0c0411070f0360343c501c11035104a82d440701126050007180001c004006040720031446c2c15000d102c070640c442ea90300302001b880054458407443d40b02d0381400071060441d01c079000e8101d88a8410030016144240000548003101d904983c100460350740d201c1c0407200ba020310b52050441c40da980301440104140c4008240d00c103456054901d007140d954610300d40913a0044804404442c024007020300101c1d21 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 679312940 1250 679311690 679311701
    0x8070219020616150905030d0507020604020102060412050d06080304080708030703080406150e040b190603023006070c02090a1118060912011d0a0201080a0203220b070927 75
    0x43c0340115a03a4040246032829500080d40442e15034200003031446823000580b1800790450303110302c000c103032925140d030001c0c0d13641e200036101924040d01c2e803000c8158140704004640344036201c80f01c14803039256904180f81d40e83c1c10900901909000d910700205444200000344c90000e03030590307540c0d810f0391078984880000b4210081194901810618041840b00790003c10354040ca108128060551030301d6213601c0090401c19000c01a02820007108102580e6600386422200b028003e80420608611132040c48850742d403c03121000740207900070040450380000003034203400e001307441e045040d58950b0301c60805c1b1085010403c6c070510040c040003280b1400042c0e000240c034405042d1901e821036260000d00620b205225120b45691205212002e00c01090300e4482d0186170b050040400c2c04899002a00c524402040241c15907404000121b00d240202142074240d014182107007502e1005040420100384101c4d00003003c94055000041c2c401211720b82c8210703945803640381c4004100303000c003003401901 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 679314190 1250 679312940 679312943
    0xf0305090316030f0e09010609060503130c06050301030611090622081f0f02040815070207051503330d02060f030c0417150112050f01090308070219020616 68
    0x1009201d90241d038a046000c54a82d03500940300d000e2091400e070030090845103082c1a0780c0c0158a014010060260000350000c1550300a0919036180c0d514200c080001d44504038014281040c40300001849076004001181600d003c0c40c02403001040906003807990b8421050310540041c800c0080050301002d1400141202400a440078400d6660b4800311740b802082011030b0740100307039043c049180402c05100d00c12001b8410541075080c03078a480f20301138807041e05001340c0a40012800c00620341d50700c217100d4000580f00040401c5002d6900344206141c0390011507400c03203180308201c42c140e1240f1402580c500041d10071743c4101005001d000900c403201c900309008a070001f01c1400440c0a02e104d2170301a505c2000c0c420056912140f9103651418840b00702100c8001e550405030030701f05070700310314800b00d410344108030380da0040082a4078140745019001010007100703520700006482010ba010801c5130040a441d4222490a826038000c40e1310450502e034025070100d01001980380d2040c41801651030f06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 679315440 1250 679314190 679314193
    0x30a0b030d110c0d0501140c030703061e0306021b0601061805010c12050c03090409120e060715180602182815050705190b070e031e010f021303020319030f030509 71
    0x406410301f09030b40c10643d008180500d0201c10819125030601c5000c0050404100420032802040300034281c40c24280000b80c401030b0000b801406000c00c009903080b405a4002c2111034943e9038110080c40202d0f91010036103034040e08000080d4543c0b00c0c421010040c0c1e00500280c6040700c542000740c40e180d00c040d024a480d4081440040141d80d41c2c0c3c454400c4150082004440300340c500d910081542503802c903140c0c41407d0900c00d00700400c2141d03441d8007000c416000700003080c0e0035140c0004407006a5400083c041800012040041f83e01000034454104044c2e44d4008007425080400c0411402404002c056030840d000c2004103150300b1000c20680c0405003016450300700107448160a281c80c045e054107034903021114440400040d200d0107a808100341c0360044c100b00f8040002900c8031811000c154280600c00c10702074001000794841f03583c0c240800e804541c1c5000d21180301204581512050748280030320320950f8a52000c80d40e109501c1c55242d520341d400d900601d0003c0e8001c0c0400b8060503020b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 679316546 1106 679315440 679315451
    0x50616021f1503080304081c0509190f080f030118050c04050d05010b2d04090203150c0c010603060e10060608070c02010311030a0b030d110c0d0501 65
    0x384820300d400400d40394042c1802140b4445160405481c1c507000209000410041030700a112802c3c1510044110900b618000c00071942c00300e522170140e0b0009503032043c207407400c41e00d82480e451141d44900180d004a480350007442e0040349075048c41447c00001480500904101c140d503610464005100301d182031410032080740039610a644c02040c107440184104507080d0440040c50102038110800c2000c8040c400030080000700703e00b600402105210301c454242800703440d203620740240c02031101400300e078925440328000802e200d0903900b003804003100d5143e0a00803e8025806080301203100d2883c00703659400c1100020070351900c2450f200c2d0802040d034015100d540d204559040044182c5190700060b00503000001100442110020400c07001124a6120108442040c0c04403242681e04c4001070b15001e444448040e902e900c19400f030207407481c11440c43d00e55284600000f185 = true := by decide +kernel

theorem cover : BRFrame.Cov 679136690 679316546 := by
  have h0 := BRFrame.cov_init 679136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 679136690 ≤ n) (h2 : n < 679316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
