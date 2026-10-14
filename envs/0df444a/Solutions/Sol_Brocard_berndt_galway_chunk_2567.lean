-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2567
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:05:20.053347+00:00
-- url     : https://prove2.me/submissions/f2c8cd02-47ab-4dc1-a78d-059f34169f84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 461510791 ≤ n < 461690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 461512041 1250 461510791 461510821
    0x150c110609010924260105060d0603050607020a150c05070204110c03070c091a0f01081005030a08030f1b1c11030a0c0e1527090c0a080601051c0203 65
    0x70304018010f00f00240848000b013406a0411003611104580201d2011003c003a1044640c1000b4410080d00104a9810300000501030313946010300014210341c0380e688150a0280c1030b1001070041c4e1008036080c0a2114101c0c41d003201c075107042d008114101420340050a00d005240010744215507515010f4558030a8600b1680e00c09600360560f076440c40c951401d091a4402c1d4000c1642c1c1030b1501d0790f0302e6103000102c422680540001060f81d1203d08401d4011240e042c030080901902110050380010551010001c11120921072340100f5241d10785014403e202030002440301246000d000300c140100160071003190700c02d6000203104516014100c880c0e4010708119200540c02000001c04c1040d1105698400280f5980c140c0d90702015105d600308100b01c01c0030501440f103502a0070046942d0085080c00e500c2c0e2a01a00000c07000e55004507400101481e500321f4070240c40710400244c0110459000345042d910000c00d0078401d061028007002610b800301b00c10301011103e940000801c0c0506410001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 461513291 1250 461512041 461512049
    0xe0405030d0c1e020105040c090e0f03032d04110d1109040c0305010e06220f020411070b01060908030409050903190509150f07061107060203010e01150c1106090109 72
    0x7051001e000088001040d00a58001030200f000c80f41e43c1d14095980b041c006d85002d560428441100c0c9400c0003180310080c001d50f202091184540822581d2a074001e0003d5440307030582d81c03520f07610355070382061400c40703019101c1458800c22140e004010018402012880c06100161500c2880f03224525005400d40c0c0c010b07013035541c03001c0d80804100c1003215416141d004c0d0f07445038000b404141281e044003691802d00392160785210700c4141c881040342c1c00500c440c80c802da005981448071200c8a030007060482d255461a812007800000b40741c030501894021150041c070251900311440c80c038062502c0c2d1030b401035025801c10b15449401203803601c1002c005580044481c1c00e680101c862100401810340e90000c4940e03809003514540142345002c41c4816103132911054540307a8070305891540d854000b4040d580c1040407422081c4008004a009032000d14081c103000102c2d0b00095040c081c001c0f03d2984007030340d03100c100100018100001101000c1c0c518402c2c00071344190351914942001600e01c0481500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 461514541 1250 461513291 461513317
    0x120a0903050724230a030f05150a050102031c09020111060a0e07080d0203160c1805060a091a1e030d090905010f05010503010e070e130c020d030b0a0e040503 69
    0xb4041020002d032140b0b6034250241200b01c46080101030350665507020140e40c1440c03138502003000850901510030080001d90403924001602512078640b50049802c01d490720004d4040310880071099090041000006e890309000550a00c200b80c541d02e003004441c07030042484581c40e01791643c1164043e5039481076161807002526010300e8020303149001811801d669a246200301c140c001040b040100e07600b00c03000d00e03a5001c0c0d4035003104600208440b404803c011100d40d5010140001e80c202c042a661425200c032240c04105400d1090400009450f0303900000f56042c5000c0c1000f036002000c65511150040543d241c404806c0428200c0030500325508405406000b8580300034030140d44060001c2c1038a400b008200f03e1642c8440207914491454051507011540400051007950740c0e001070580e12820b6807070040c0880b070000d0045071036403000b12510241c031900e9126155800d0303014045c44851aa11780b03000c00403240400002400b12030a4455103a01812080115050083c28011605002c5100b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 461515791 1250 461514541 461514553
    0x70f020a03060617061b0901030e100903090303020c15030105040f06031b1a030403080403050c030903100b131506050717070b0405070b0301081002030604090c0806060120120a090305 80
    0x1118080701c4c0c814007003110350781e4007900000800307101d440c54510010500032080b090a1845110041d0010042c401b088902d40c40f03130b8414000340318058002d00f06450310955032044010328500d4007030301d04845504070310711410131801c4804141c218030098904444048401207080c1e580d10701717588002c00031500013030000340d8203411111819004814503003c1300d0048040011460100c0000d16103408141d074010001503001003c01c0c0864450406400c0940490081d24601003414000900c0c0c075600da99440f49407500c03184c0500c031503d044005003140c4602030005101960300b20071191501100360181c00180400401c0c1d030010b2244032030314146515003035011703566182a07505000c01a444116800c4405100b4824040703801c000c0300c020349040b940a44000c1000e400000d4a120180d04001d06803030300581c0c0c6030a18804149126400c02c0105400ca014012a0504070001441d007d060040034a8580796030303c800110308000214140160303d1050403903101d40007c2c81c2110f82694560010349144104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 461517041 1250 461515791 461515799
    0x702030a140706020309100c1a0a060947061201050a06110a03030504210e090a020405060304020f01030905100c0210061401141c0b03010e0a0503070f020a030606 71
    0x4584203004003258040728902c590f40c100032aa20f20032203005903000b9005030700c000c50003400340038641d0a0310f128202c5150300084000207001000000c807607003800284c403064100b000090504c83c2152440158982d00b20000020b40020b00c42101ca04644081e0401000d058280b454a1201a44072070001080c16989c0c800411241151ba4400c0c0101441000803040020703002d0300503404030030400f50380780240600c0c0c0140c0c0c81c241d0007058020010f4131003181c600d000d00880c141070134001c3c0b086150b80d1590180400d0b03100c1802014080180407200240c1304000c18091176560300207495006904070f51002104d4001c4004030050310485030006c0c11845100f0310802030020039003081c0340340c1c003070345e401c07550103c1e03064a021050340c0da64420b40c1111006c2241d4000c01d54411401c40c001ca0300c00d0307815186800e440402d040c40d01d6008580c007045ca181e8400c4003001070300d001c1c081c410311040030000400100b40203883e002d80368407501d0380c020040783c0800e010300110344454250b0401907800075006c005165071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 461518291 1250 461517041 461517053
    0x80d0903120b101b05030d1107030e0909031b010e03130e06011403160314092805031603020a020316090e011a040b061608090a09110f0f0702030a 64
    0x1840010101041c202818410103050003500612034034000d6840b00d102e030911304040124403c8400040e18030340010402680b151200780202ca6004650306080c0e66200030900380100f4000c0ca0300710082c818100c410900c9820540042520305058076080c1da2690000f908140ca0300420640080d20b119000110b18103d001d400d60305141d040350f60182401c0308603602d000044555103440c41c04852041024804590b0f001064015900c1000f154240011020f5403000c581c80c440380219031401107948420583c507204040c00c100da840514a045125000b90001d54803075890340210b200c01c07440c2c0c0b04108107200c01c1c18420040c02210b0358024007510798209002d0000c480621302405103000090030103072503000394001480390300740c0b2003203940d4010218280d10003080042d1201a14450f40040b040c805400302d10310604619511340c2c819080c469803051107000340600003845500038a6028607110754207040c0031340310049405900031510b02c60b555013480000502603016040703002e5010b204036080384040140b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 461519541 1250 461518291 461518307
    0x6040605090d08060d0602071a1006090b0c0d030b130603030f0f111203070c0204050a0b030c0603040c060513090219020f010b0f0607060e0307120806040603050a0f080d0903 76
    0x14803005542d0358915044003518548000d0300c0322601320241c0c1c442070300400d0203580580803c520640b03281d60180390482681900813410b403000303480e80e10007140c200302c3c0c56000940600100341220829050590203828546c031010408000402c1c0754440008440c00e94460036014601601d8480c01c0042c6502ca08004018000544010b00458644a5040000c0c1c1c0540c040d440000e414000504240203801311910322600094004010b0000320422540140d5460094512603546084c0005280740702c00201850191103226072405624204140000300b201000e808090b1101c42c149075545075110001ca071145030321648403402851000c10304031000399950740c165010302d2059085642d02ca242c4851242200e07503045c000d6500061002c072003145030910401405801d0b018a0002070720340480c1e11054115440050110348610b001981c002da1140c100c1482500281e003030350100402411503480941d81d442844c0003821926aa0141c102000f0405084910143d400309050224110300d1801600381c0c9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 461520791 1250 461519541 461519551
    0x901020a02010b090613200705100c03050c0409020304051212060a05061305120f0102040609030b0f04030f1209020a0f0305060109020a050406050d0204090c0518030a0302030f130806040605 83
    0x350815003000f810389000340b600c03170080c5002007481101c1340400981800800040600c0a0300924a92a00c0521411038024041650095020b454200311031050a021100346a885405042c43c20b4240815002400280c400b5113518000c010791301d440314101140f421070484103031b202d50080000d040502c6002ca008180c0680e009882481c0919280c60811036070b40209240c0960181c01c0010810252800c2d01c0f0005c01d450085c010f0718119196503144909a138060742146000c43c05182e010420400d074030405941c00400050b10034050308156030000c01c550902400c107803c000001b143c20030120340c0b0b0340c49040900c2c5e0080051250326900c07503401040000303610046d601c60044000000b00302d102d5008880024016680d81c82c034113070420f00c1c1510507030401c404c0c032034145509000118440c9001d1040d04102310440e2102c54407500e90010a040c11095440464002d80000c0b10440009030004281c800e49180301440c551030702649240c01000350420760050140d44902c10500091002c141d1185000e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 461522041 1250 461520791 461520793
    0x80f0904050a0e061b090307030308161110051e04050601050112051e040309080316062d0209040f180507080601061b03110a11190f090e12030901020a02 67
    0x20b6841c40307010021100707a408242e40c40d07044030001030300c0584aa882c8228201e80200001d040030f00240200b403a0516079041200800c402c901072110312413180304411020307486441c080d0039414070710103101e4031000800408000f86461310b005c01c84000720384200c40c210b1040b501e0011130b289018140103603270300da0a20640b4089074044400c1e522481c050700841344941c102d0a0b00d000229981200729540e190010003d408010003581c020552500510040c00c0150100020b24040d840d28100002142c1d00c96450b483c4035005032200c140e0283c020300e5110b2014510640068580b07200c003000c80c01a007102030242c1c40e4549800901441d070223801522250f218040e0040390b22281e140e07a0328a40e500003c1c0140300104948103021528080584ca9101a0b50301c42d00d0461400e0a144070560324100280c401100c00641a00d45180f95082107400c070003d4030b02c03442d20040201e29004031184031035486d001c6d034a070702c40d10b4011101080600308080400f11310030740d814590364900301c0700b814000e4208034602801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 461523291 1250 461522041 461522051
    0x60f0e030a0615051512060d0c06030605010e100f12061802180616120c0c12021305010501210b032b081605030907050604180e0703032a080f0904 64
    0x60600d4450b24030b806194060750751400400700c1b1300b4065040000e110307541c41807403d801780700000d000e90041002015191400316166050100242114058542c4e05024105400055602c00d40c02114490400c010342003003c4001524031a146c06081580c05c0003013118600006112091490780c010100303105001c12410121400c0803c00c5183d11900300b524822a21030403814001c0b544181c0122113142481c103062111640c1a13807040d00b4000c03a0782c442010000d0164050081d801c00007184580400c1c4410104050740c140030005e4440d08505441461104010240124040725036102511040000303084862183c04004c290a499085051580e00c8200c0d04c1000c0d0701ca94000d01c2540d0141a8440c010b203080c4410030411126508000c04841191081c8100084c1e00e4a802c0020000341000c2c0340840a2208030b019017900740ca10840786645503900240d400c0020a6000c203859100035006680517845000307040000d0454000c0e00b0028181c07000000d2035181c1c04420100a002c10f450548041c40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 461524541 1250 461523291 461523299
    0x702331302030304150e13020d0e070e13080c160314010903051b160e060a081606050714060a0f050702030a090509090f010e010b18010f060f0e030a0615 67
    0x2200c112860300082d0180d1090000703100b800c0e40841d9010340d10506240075005c84450303800180750a5080e462101b94281e00240f45200c0e00da0502400b10a0b001580080054a2a20703991240d82038001305180703101d04010b000311040010700c1c42128100164681103e44449186001d1044183c8ac0d103c112052150000591609541801807244c00c03030b09a1903190600d81400088400d09a0101883c3c4003802260142601b0344008000a8090041038041d40614a400c0d0700744403401d000c03038012551561203084048040040d503003003d0140c0784c951030226121001d07403030070200d84200c0200d580c4c820b000c3d0000f0085100f1560380001000b40380000b0500042d00c40701016600c0317204041c0b400d03000403d0b9141c02c1c005401c0000d2040e4102510300211103040d11411000d5084030031904030000c490351a0700302c504040c40d00c00d207010980f1420707002d07201c1c1d20f5240c04170703044034455984990b6091051401c1c0b28244940600c103d41411000501074440106071854010014202e61304400d80303049000314041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 461525791 1250 461524541 461524561
    0x1090c083702041b0305240d08070201030e0613020109172a0a060804120302040608040f0203211c02040b1c02091c03020c030114040b070233 62
    0x1840e9010200011103944840074200c04410607200ca099030050f4542284803080f40e0410203441968403583e41c0026141070000303400d503038005140031100c2e02c4000c501d6001117079910100e8407003009610031811940c80c0755030310040c0c0c054030b1000315101e464082e20b410030000d41031804203002c04d01c1c0300340c0c2c401008540724a9507000b04c10b039220b0700c800c2a51000f01404d880d034034190f180324100b0001840b900720410014000500f0048140c11640025506005010411141c5808009911103a017001e41c10a402d2260003000b1035001400649810000b440020640d1418000c0600010001220080380c20703001007004415440464074500c000010795003e940c2030b01c54402c0d1416190b503118424600788a00c2c500092803183c0c000314040b0f0507030801050007a0703030761440c0c5c0c8c44500c6004824480c200c0301a050203801c0c04150851140a6414190088158071304072070419800b41d80104d00c3c01150702c460004a02d0714410215040d05070b131440d200d0640e0000d400848000082102c07403150780c80d0759001820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 461527041 1250 461525791 461525833
    0x10051b070803030132060306030703060f020403170c06040f080d06031a0721020d0b0424092a230c0d11070b030c0c0709060e0112110103110c01090c08 66
    0x200032400e4a140c05c0030f40349004002540c10050040803a040c2c29200d458030005c0b503440c2c1c0301080c083c0382c0c0010b040040040201c0d0020b0800e0100701031340d050041038012561030b001c000740010a45292045035030100000d010695030704111450301000641e490340340044c420450881245100e0541e540040c110341d124501c4c07058032a4001c0000f500e2040c1c05207100c006900b01d0368403042c2441c3c440b070030758056031200d204400041440030850380340010401000002041c00c1e17001500c20301d0408280581d240811003001190020004010095200307070391044542249000f01c071090302c0c1c02d202160b011a504030000d005100300c0182540e0f0a0043c154058034502138094020003e0740284804201e410400405503509c442952190791905010ba00100d0615019800c46c1d820255030f00f00900088440409980c050b00320907603860001c032500c0d103418dc074001c8503100144c101a250b42c03c03900c84c42281c01c01d5859110310080244000541440c1c9108007480e41d001d07488291040040e030800703500610b4a9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 461528291 1250 461527041 461527109
    0x303090801020304150b01090314030d050702120304020f18070c0611040e040b06150a1701120201120506040f090f020306090c01090312051606050a150510051b0708030301 75
    0x42d038520203010200c5c1038050b104204917141032208904000020a08149000c10340b0050307580607642c0c40e613a1102e05000c0302c0e0064607050441d0300c0319851003501c43e40c25045a8109804807004422401c0b0303c00090002c1c1341d0b024049481440b600148107180c0e400060700342c09648503134000c0c86861405400c40d80e040c080c2c1e00c6090300b04e8081401103000b0030720702520075400200240407641580c2402c82641c2803030740704030600d0300041c00d4a500c84200030310100541d0b0240981400c82501e140c00c91300002c1010948000d0300641d03030382e02d50103e01240c1d2641d21081030b912828005100ca4160b5003040030299100c0d06083c0d00078050f840009a00c0003001c9900f50480d501610b0b4407182a086407940c0b41e680c2c542081010602404010342c00d1080c0d512080e091150b031088001080624190130004181d6284440c5141035214204c414461661204403011040d03e1368a4242e884003d00012080f140d480506814428012600f020481740d238040002c6069a00f891400b0081c0c5201540d02001c0340c4007104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 461529541 1250 461528291 461528303
    0x6030912111b1f0305063a0c030f08030a060f0510050d0b030609010e0f0106061e0921050f060c03180a02040c050919050d0605060105072a051e0d1a09070303090801020304 75
    0x1c9491a183d12180c0102d1f045070007904d0502030349860740e55403503a09800d054240c402010120400124912034014540986840340802180394541400f20b6070151040c80761400388200481d20391081521580b20107407512000f000c031202030416074190303802896080f01144c024000c110b8510403011050103071501311050ad0ba41e40d03900e28090004100c0601625044c0d00400c420440002004120f110301440d0980aa60034101070282d6445d080d80760a1000084005d65000031040040c02688a004da03540301e42c1d2202c0640034a1030441a40e41041841720f00294803910380340302440c5407540034001d0800354005032000f030011300003d03142d85002d44480c07181581c808596440980094030365001903400c288181086810300765160b0741c004807900600802d002404808103038810008003101000e00400c030541e0703034400803040a80307007072926190095014001c7c0a00410801001854081e10907811013003030219160781800c4aa4070703252100f911094000410000c800728407900b061088034001c0354025 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 461530791 1250 461529541 461529619
    0x40510151107050103020714070b1201211e0c0b03010905010501080108070302010e0105070b040b06130b0109120203031902010b0a0504020f0d0f110406030912111b1f030506 76
    0x42e0045000c7e5002150486003449140c4031099451020072001c0c01600b00503a205807610086508009607100580c0005800c0c007828500c041380070320340d00300109600c0e04207200f201002071852000c8910008824010100c5400b620006402c40b20b14001d1810303161180028061030740c1e01d0004580014080c000c6585175048240300708015805410402400b04040c10800d04040791511000c0c0105000c49056551345c00d00020400646803135030072081e031124a21070402c22100400002000845a0f008800c80c480000c074000c41176590800c00c2d01d103103081640894868a1107001c00a010740201c0700700c0d501600f00c480000c1075074501402a02c04ca00d810700043c03070400c03103a0070444014103c4400203108841ea10382e04030040e003400d01c0040010385060b440100f40c40300d1500d40096080c207810841d02c10840010351038040b52401080d42051907186c1d1070070801800f074010000d80d081d80480c3d12079001d03180c101a451036003901a000940300d107504844064074180e490310340c000240005040d85004803c0d41e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 461532041 1250 461530791 461530799
    0x20091003060510050d110d09060b04151e0332120d0507110102190e060306090403080a0e0d031a010c050d0507110d06092609040c0e040510151107 64
    0x2031000303085006172040b004503404d0b0240c0012001d07640040d0b844007507244c070b49004c1c0c0f0500410340151402c021066404000c0c01e12803c4004402c0720b034070700620100410140e602c2c21a0800304929001460304100701c0d50b1818440c1040c1c00e03c100305103c041041e00f5030041d00552440010655002e60743c03102960350700e448900b015140003440000d040b00c09026010000da000320409101600785140311551700701700081503050140c5110090801140324900420402641e51100703c11940c00940c982421030058031040c05030f001034070003080c00c05141d2103140f1900c002540d042d0011070040c9028541d0307400fa08250001101d04c5103201d5805042d503400321010b1114244650000c19095005c0d038549221249540000ba40761418000142c42030ba03214410202071028035802180c00c1001400040c1045a1820f00c43c440d40c003031034aa0900c1190780b4500e100c0720f1402844642017840000b00100154540303818900c00e03100e070701c1c001c0c64420141d6941c94108140910301c50568524601c2c010322205142c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 461533291 1250 461532041 461532047
    0x1b0b030f04060e150a0b0f06070206070201170907060f021626011a030c010903050709110d050a091401020403030816031b1e030b0d02040902030120091003060510 71
    0x5001110b10300c0d900c2e6480407403c2428072003003081103c81001e244c204c0c02d0094004003a0b9551012041c4100741ca0549400d00b5598201114078407581590701d6038031411280010307500b0403110600405820014070420000c0c040c0850350500342d07502c40d12a0104004040002c0740c2e0746801132049402e0301c10f0840113105580c2014050030070040c2100c200c0070031034440c0e0421820344d48440d60402c00a69001e40c8003d61381380612150000000a180250845145440e45a034802443c0324071a1215910b00c0c408100c0c89601e401ca07111200403030418045e5040c011001c00c000d14680310f0580307414490704940f9804002c10700842e8100c90b0540e90380c1c51180c80f501c43c7c40d4061101c903440d00381819580c0740080005078104507002c50403102e41c0c4651000c80c0d0388007100b00c0d030b101400412804040c42e048040d40d246c2e070745c00c1040d4082da406550001e030744402c6101186c01041004040030142c042a88051200d19641c0000c28449a0580e10b480c040f16440009409598690003101d90141c12140d4142e580c40c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 461534541 1250 461533291 461533321
    0x50c09040b060f070503042309040b0903070804120201020c0402031e18010603030f020f030301030b011e08010f1d01020304020a062105010312020105160203090609060d181b0b03 78
    0x180103002c0d5190101500701d0034401c0c1d00091044900341c0001c00e0400007101d0030003040030300c444981100d41d80c3c07000d003800040c452400200001e005504090118010030001c0065841c1907520240151f07440ea114010341c5419248844202e00620840440345101e091074000d84e8000c0f54400000c2c00784d860402c0007c040420000c041e039030041d140d01c1c0040d81c0e625090241000960107500c8032007008082070700081c14524015100d0700c1513881040104009401d1981740f03811104510401c1c061061210400c400c004035136400a070180d0b08004154088400030303400003581084a41d066024170310301c003185078240e001c02c4601a40c8404c401d40700300f00300750141c000340c411614030501e4060000c0d1007100803c112842030700107880c20350300440d810400f283c091107440d030440300442130880256110403000307550303210313031200640603500101c1c21103243d0f124442500c98402e06801e00b44003080091404102d6020304a000303a82c1030020884030303032180300005109003e5070580c00d041459a50791440c9007800403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 461535791 1250 461534541 461534561
    0x40614010617070903050316050102092707020105091b011106160f0905060703080c0f160b330604090501090930180308070b16030b0102190303020c0a24050c0904 71
    0x9502008502019915050f901c038048e0002c02c00c258100d0800c2e94dd5030146400206114190381c50070061150800c400581400c440714640000d000b100c413208012521403e81b04001243c51140806000c902e401140030034007945a0343e52280503882003060110ba24000504c54160841020001d180c08280f04004070b65200d101c07044101d10301180214000c2096003c0745021074109901441c5d10200400d0100d520b4002c407409555084440d44440c0c0070502140c401c40b6412500080c2400030040d07240c5605550040005041c2004151b94030201ca40103480d070420104c8403c2180c0d42c8202050100c00c2c0a0700021184d00e00c100e00c05658040260b070010707050440d514041490801c000000340c0804000c10001d403150307515424904160740000d1090482c16050014542003c1c0d60441c2e690303002400310702e444400b600a0001e40c0e42801c081e0004c2c41100c04064240c09141400001d10032800082655608006011017600c40c113103155008495065840803c0c01e00c0400c210059403a00c1e40101580d2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 461537041 1250 461535791 461535793
    0xf19080c010e07030b0f0112151a04020c0f0c01030e0303010e13080304061d03040605162d0309090b0d060906060b03190e060106140304061401061707090305031605 72
    0x81030031003030140341241c02e52041740d0900d8a00100b0207210443c000d0316005184000e51095180350594402882a5030f08004081300381d580c1c810b1007058100010070143c1458041c03c00c40da16041408129107441d40040c4d0f00d21148191500419194403900c581ca99510384170b4080d5066909200340c158604c2c001a000400211321401d101c00810030200003035010b035100b144001550203000d84d1981440600d150440036641050104000b00d43d00300040700e59001e0704143c28a04441180b41c01c0a4050400c6589800d1880401495400180c0c0c6000400e13200d01a460305c08105950704201000d40e0082d514298000018540c48000154079400c99412140f045901080f41d640340c071001801908101c403900e000104042601c941100b1a03c00e18420721444400b41402c1d42c1400d101900801c0c010440c3c410080340080010140440e0f41c0c031201120040380030240d09946e46002c01841c90b101c0400300c40c1c00c51a640e0100e481d0710f0044d041c0383e01316039101002e1828212002c110300d80522801c0c8050b151 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 461538291 1250 461537041 461537051
    0x6060a0e07022a0108070c050304140a090603050105010302090c0901140705030c0d0e18040c120f080703050316030507080f07050408100c031112011802090409060e0f19080c01 77
    0x48041c0106891a0f104108a0344103242c5083c0001000e064000c3e0090082c852900702d481d0100c0c00100072581510940000c40d41c0030121040030800c04440d550060b84064030b483c40c08020031506404c00d40c1228001c40b200e2141c0d490f59034401000384109480e02d030200c0ca40b03060302440810704202500c81c0c64001e1094900740110406102d00340300c4554003040c0007910b480c000e005c40745000750341d02c0c064044000300008940f4090741c40329064403450282d049002e403031024407010030611241d40420203a202e000b860f01c414062401400c9500146c9981703680103244a11503040920a200d120310034460b65866515584901115180f92940036140c030303040000801011500c100c04200d001c0992410340400204c00f1101c2000400708d44c80c007814100145410044010340c81525282c007819220001e0b040d090b200719800c02c20009200b1501c04c80d80140c01d001c0c0072070034842194000101e8071800410303241c500781003071001a02c800c02c00f000c61041e1f00d011034840380030552540140103141042000020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 461539541 1250 461538291 461538313
    0x40b04270203090d0f030207080f0705030705070801051e090a060b04060f0b0c071505041404060911120106030509100b150309030705010f180803090109081c0b0306060a0e0702 77
    0x1607070320071244000207511000c1904d016135030001042e281c2c061a40780460500c08076070f80340300711482103610f01f13580c02001050403010b0103424400c449909a00004035040a50b8884545000e46801c03100308010110001810220b0340b400c104080c419080f130340140c0505c01300781c2d8403c401008080f0b0000d40060b07940e6000f103002c001c065403c0b0083c000140c041501c1d2000401d00e94913045160704490320070403003103000840785038000041d54155201d20303140c9500103221a0100b001480d0319400302c01e206042034503a2040804000081601c06080b41000c1043c1c6c0e00d6101c1581a51802d41303c00c60203900c0285d94000f00070040c0e0007088158401007502900b00025042400a42c005070368126076034000046a1003081000d01c2001324540da5410180011703130300e8902050000b204000040c3c0342c0440040010a0107000398003d80d07101c0c0d0301c1200e0a07120064181e80380c849123404554070304010300d0052013a0440c0740016255203e100000c02c00390115081000d4080005809080081580300c0e07119002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 461540791 1250 461539541 461539619
    0x8100509071d06040e0415090614070e1206010504020d1e020c1005040f0b0702030904060803090a08420403020d08072c0d020d060906060b040b04 64
    0x6004925541d66120382d03035060030321082800728211400d4803406082100304102c002d5101d8160740180c1000b90b50700031140c445015400b4002c9804c0c010103051400d840d98000c0e8190540850194010360703078103c4080322800a21180e040c411000d210282d20250041110b403405030001c0111744a015004148210840901500b405000819000b1590017103005030202e9010800008041001e44c01488182820380302c2031102001490083c1c040e0080c10001040c1c0e5008000315003c00e00050402c200c8295540c0e0b010744c5030f030818040c40b44030700741c1c4040001700710f00001603d00e60104280141707100b036800101d0900c00d00742189144d0400492080001d042e580d50580c40358490b502a40103410941020305004200c10001001c030428040d106094001c09140820442c2c50400390050310080640b0240004c2d02019607054029031100d6080000317000c100194014030036091043c42c081c860300e900c03000c450101c5e0213940191204c0c004203100070041090400c0007810030b07403c0b0100071405a85a440c00d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 461542041 1250 461540791 461540809
    0x1609020906090901140108090d09090f0209091009290f1503040c0906060f020d0324090608160b0d0203040f1401020306030c0102062e1d0f0a06060c03081005 69
    0x11103000000042c0324069600000c03462303031014401000e89039440458101500304102d500542101e00d80e0342c00b0300c03404400b040d4112654040020700e101030915241c0040008074515014450031182001240303132204001c491402c0d488001000720300010340e4540d06000c0d01c03118481c074040c2d0100c1d20705403c17a00720000304010f5004034000c0301340840260410004070280d41c0345920000420802c10700450f0510760101c0c40171062030003482c001c503000f01d44280950708240380c1d0050002071807080c0070010b0807007120750086c41100c0d03030101611701e212400050046164464858101580000c00ca800030740074050703008560140c1300e40c043d03126003065500c2e40c6007800c0198800c02801e1717600005000052404000c1e141e1010800d200070102840c1484a4912a480030501401e00401d540d440344150020410900041e10340135100e9006000c0c441e007020320000044d00d031030545c10b8000340807a59454240c0540305c10b44820b031b280d44040d603d00742d50485100c44000c3c200028000043d801040c0ea81d2a942c038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 461543291 1250 461542041 461542049
    0x4030605090d090f031e230a0204060801060b09060c01060e13260d18080f130e0c0301031709030109030504050301180b04020d030c050601091a01021609020906090901 73
    0x141095081c00b4000303070240156801074000000c01e40403c100094410400303490300e116141c021080c20140c0c0c1350901da0320b00790540100380750700b509903a401c8600c0002500403510f8001c40301846a569542c1080c1c0c200e812034003804d4280b80082003540c2441c14004000c1581404a500006030346540d6401c940c901d69007951541107501d080c000c0c150030300245020244905c5500c910400e0315010700c00c3c203500c840c410214a800555181e40080f000c1495a0b10348148148c0c0040015650b0406246507000307590003020803c02004140c1408604d903111610064801c2c4e00b16510285180d0954549904151051800040051040000c40b07029102170042c148514400c1e283e15807034070300300300806094415000c140704c03910420359480c0c80815152030b041ca0b000381d010350b060800550682821911750031040e60203082c3d0700c81d100001508200caa484060f11004984483c51211110001240c8640c0e402e50380351101108034038141700c606903030f600511500070010008c3d0300d4405000d000c6007002c2400d81c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 461544541 1250 461543291 461543293
    0x605070210020c03101a191707150e04110a030e1902060f090607020a0305030405090105060a0c2d060b120102070f030f0903020915010f0f0c02060d020403060509 71
    0x151480440c01d2400c44200e40c0a9503001414038102e241c004265111440800415182c0c1c50303540070030800500e1808056082409400300d040d040002c401000340840742d00c10400c000020328865981c403400803a00c0301c19142c000c2c6031604480e00341d0f40111001d01e00320428071b03805961600c4a1020002c1c80c8010b04542e071540d2008101903641c8410b0900b81288078070071250004028405000507500d130422100701c085030401d615181c904c4540840c00602034008003d4200c810704a01005008002028008444048a4120b01a03072903805012040c025860003c0104088004540c002030180300002c880d268000c0c8a0310f0a200e171107102d00c0d111900202c041c0d0f82503030350381c41c001040c1c1030070a028074031040c0080007035141440582d2070050321620034801404000c0344011641c03025102e070300c4400085400402d2900709040001020301c000240086081c00b00b464007410030483c50165403000c4910b0216101d14400c14025024000545d00071641c0e01d20940d400c000200008070700d4410755010b41c1c4010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 461545791 1250 461544541 461544547
    0xa0906031a07020d0f080c0c0f0a05060c070230030f180303070305121008100c020c010e0a09020d09020301050f0105090a020301030b010501050f070c060f030609060305100506030a06060605 83
    0x20003020041c010181c141d50071500030b40040c0d12400d403c000c3d01c0c0c000101d1450300400795075969900c20414024405080078a0045100c2212050000601c942d01c0a0280058945a0700d81c04000c941c1481100f000a40026064580654249000b050401c4241040303044254040c2d12130f134020b0865200740c030040880131010486280c0c043c0c0b40244880e00c05130950041d880c061503602d001d0143c0c069100f0300341d9152050300000f6448060005403170003c1c5075480032611604c00e45000340d0007421441c42507100503c56101e5407511584515018400074401803c1e400c00306090041a401950000340380e0b06159071561038040c0184c8092040c0c521540c038030414816154107000404c140c0550280070301c01d0181c014401800450344016445045030340900300340c3e680300c2c10001441c0b114003800b01d0240c5508000c6000152094001c4600d448a0050342d40822200c0e496144101c11210680005000d5a03c4030040c031408003a26488250415801400c070354102d035041d41c807541560450780203900022408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 461547041 1250 461545791 461545823
    0x607050309160e0621030a020601090b0d020a090f0617060103050c0303071a060a050d0506011a120610030b100302180f09070c03120f020c0f0309060301030f020a090603 74
    0x1d0201e5100b01c0082c6941d441e0303141c50403040885001e805010507200b00f05c0c1490039400750640091030000e240483c0203036034860340358090217510b42d0400d22640407070b0f60511818101c9c2d0b1a0a101e01d54515600420403180c080c14000480000c10b20540c09161080e940c96000ca400e8003901109039070300048070018502c079815407401609001c040d0841e94021b1b4001c1c00310000292030400c881c03e00d1003500038241115a0342138005072034130310603034440c58200301d401204400340311021403c5411b07154600045802c0408500c0100d907980700b01070b10380b1101000e010100300c5d149082000e000327040030a8900401c91a150000168840b40b2a4a081c008264001101e4044240031480c1c4a0343c1002211883c29186941010440c40200201107008011000c05000b04041c0140d4000030780b103081480030403481018044c2600254002c1d0090310341441414a07540321800c00204803804000c0103440300d4216440c60307407402c0010700107030012a0300100720200454495214030920004502407040403984100e2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 461548291 1250 461547041 461547043
    0x9050106060306120b071e0f0810120303021e0a050a0207061b0803060301090c1e080d02150a0f020a030b04050a05060102030f0c0c120601080d05090108010314010e0607050309 77
    0x140e0750080d0140342c01c1c49002c210044004d803a9194882d0043c0b501c0e41c0c550341d50001180d03421109400746115001031006200d01e41e40c400d40203404100180c8614035251640c05285010035040e200d00b641c00c4208080303100c002842500503080000302010800c0b003c0c1106540e45005800c000741480010300042181003083e503040000000130100707030070011643c4207141c01921010b100404c018100904c008049401920250301c050462074014620805098481d41c2c55540c4203101120803010b9407400700c010a2298020400d00c032030302c0c1c05400800c2401c0c0104061401100020810107107540d031064036010100c4540020810440726580004180d10068108403c840c40038108001082c900010049280d80000c1152900c030040404c05840d48008800c081c644803820413000d410282d24900700c01020300015000341620445070640b040d40391065000c490a01400c22014009070109004101041e1484212481d00d1109030010a55005003a0140c1c901023090716142d000890000c100480504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 461549541 1250 461548291 461548301
    0x61107032a020f12100e011d0309031005070c0c0e0a111809060a0503010f09030807050a0f0c02042a02010b0105040609030209060d02100804020415031a0a1e090501 72
    0x70340c918168820b5000315805042010f400c6014076150b0300112081101000368000c0c0340d07201d40341481104980d03402c0501a041c04c807407094031800d001c041d05a13100e102009444808034090020240e000c204c094010103004040c1c0f941052220f0710010034082450003100300050702c1c5035458082c3d6070820305440022141d4580600519903000d011f818140e142c03480d100241c82c0300840e890391258542000140f004085584034603815840e0906803682500d00d03800022240d406078403003645641e00c0e1070041e13620307210302004a00000e0261011041d041e009900d0081e410780060b00c0018249007e0031841540301c0004c0c070f0181610030074280c01d40d40c29424040c0b040201000c0c41d00e81c0c1400d181044c080c008001e80d010091040005034000303801903c403014001a41074005001410002421038040c00f80c1c802030b40c2c01d900460400c1d00801c090480ba120300c50441e1b611020750b41c003031a0107a103802c400741009800c00700304680b1004845182c201c0c1e150309001c098100070300060a807040f4901682155 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 461550791 1250 461549541 461549597
    0xc090705090d03201f0b010c080403080f130303031a010203040807051c0b040b010f050607030813110a0b0d0e0705030c15120f011401030912030906110703 68
    0x84010403070300d141521144000c0310320302da043c2089440d0441c0039002c1a1000594240014030748a04501895440b0640441c81040705022404004041c2d50f0001100c240d01c40c250b01825100c0100300c10800a180d00c8000c0c45040d085150090410303880d00214401d24040e58400e030002a121a9030540b108030807514542084400d00086160501d0b005031507844070300070f00c107031407241900844006038861b00b00150700c24143d0203800c1820701d00d018600305581c107000f80602d1141100c404400310b1709040000807a08510707015119a80c00750f0303580c82c00407800708490008550004014400501d141c42d00f0100402408981110300d07160111040d240048030611400300b600c2d40d0101d1410040c60310086145034641206440c00c05c11054007900d013854510841c03051740e244210311070400003140103242006041e5a4080d182e4a10100200e00440030b94000c114090203c100100218511900952002d050540f00c1c4101041e8840d02550b544010341002006801050300508140000e501000e9035440b20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 461552041 1250 461550791 461550797
    0x4170d06170a0b06010e0d080c160f030503090d1a0108030d0e03040f0b1612020c0f0d02090601031e0f0510081203040f081204030c02040f02040b0304080a140c0c0907 73
    0x9020b01e9116040f41000107040389050000000c40e804080d101d429603030940c140c04c1a0102d65034913481c155265100084081c2a800d00300c42900440d8411f240003a9004413a048402107080450f8003040102c0c0c2001c000040307a0100000308554000b072401000c0034024011040610303284c201d02907056068441c00e44903d040d0390401c201c00d02107030345801620350a5400c10321159494051181003141c500000f0a805000c020101c564641d40981c0028054081002540c14610409607402400090f08540500951000450001aa0780d520a900c400300e02d40c03c1030001500c028032155180c00303d80c50903004a1620f6120000c0100c0c4d8082c40a050000308010401800000043d0003034002a00000d0401400a80a0841d4030280031510782aa00391607001546480c0070305052030302604140809600324051802d1003513031500b400451003a00d0864100c1c20015203199516aa64840c81d4004a80c3e0000d12444000e0b9802600107040034005503200c080082c180034007914104400190002c0c00c0d4810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 461553291 1250 461552041 461552053
    0x2c01050709091e0b0117150f0a031113020409020708070c0506040b0f030603010207140f010501080f0a030e0d06020307090e0604111c06170a0b01050603091504170d0617 74
    0x544860b5401412001d43e011000a05a44000048421062100982101c40d5001d418042c1428514000c0303600054110744082c0c40f21300700000c3c807203001a40d200181024814120036500d41c108005c45440c07604843c5801071805844150140c02c9801018003070740c0f40c0c28007240b030001b0400b050212202501c0d0440301f8a041500d440810300a9215110080c120214088046915a03c003501a620303455803104c0d4030001413441904180d42e400c0e62100c018102e40c01c2000000e106080405c08000d98054030000d402e444485807425035070110b010101d583c210003060b10000203d545071010314001c03011030b03036909400c074500b40f418621414050102840b4501e13100c031400c9043d10103000c48440304010500111101d03d40143c0b10028480c6034042c900b54040803240c050b01d02c02c0440c590240e1481000100403c1e40c85001380803082c00100d071080020390040b09042d482d401e0031b13050303aa48684120500310010300740d450a400590842801d00e15101c2e20b4640c244504401c90341c903180000315500c000d1030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 461554541 1250 461553291 461553311
    0x5060d0803130615060f12060509070e0102150f040311240c1c020a180b0d0e1903090303120c1d0409020316030b01060908030d2c0105070909 62
    0x400d0311001e050a079140c1c610302a03490400c840c0750010030300640d003805100340c4e0540d1400041c01e0079a0007078034503000031038900344003072804820301c00d0700c09a85000c0d05080e26aa5958819680e08542c40010b50640c07140c944203110300180d14100b80c0c410300ca0104854a10706091801030001035000002640a03000a071000800316a419002003140c0f440350040780d11511100803c15030380c0314080120401c0190095014031000b015001454100c1d0360340e85051040e0041141a030080045c0d001d01c52004204000215480c40141c02403c0b00d1103405040d94007012114005441c0c614101e4002c8001c121070311000c1085c160001c060320030703007245c501c01401940a4840700425084c2d00300d940324040c080f40c00400559072640d0f40049901030b8090f003201c4940d10102602642d1380482e101c11100302c4071142c00402c10360321468032801107400590003581480b02800041001c1c1c0140c03001c6812030000c1100c686105958180c1100e60342040400000351070821b18401050302800e900418412403d0002000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 461555791 1250 461554541 461554553
    0x90705091c1a160e2d0a050f010e1207120c081e0606010c141009050f0703021302071b0b030907060f020d03150e090f071e05010f090308030c0d05060d 66
    0x140c000d4284c43e00c8800242140c00084450302480350000c00c00a4422844000410007540b44015960448003000d0440d034032000c1018803505441140d000451054411260703040414592030b011070a20705072a1000d0f15504548049000c0c4403098400c440945000c118801b8107100c4600b0a0880c904007000f00704050019070b584100152000381040300f080389040901569041421405460405880192080060390b9000e40240903054445000b00c041c425010031001810b0000c03254080d22050021800d143d11f8002900540b005070703040c1a0200d031980804000201c120040e003403405641d5140e040c0150242c0c6070130201d410040c1130046060f5500c010f80d80024000d40b0b080201e15000c075041e80100d5a0b00c4003150990b100e02440c42e842c005114000e04085014802c1001c20011210019541c10a42140c00401034100032800a0b40c101407155500c5403034200d019070094203042c14440d69030788d42c0c0c507440d503c00c41d0860b00c000b00120707401c51554064002d10742c00820850b040c0c1d00c0c000b5140c4940c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 461557041 1250 461555791 461555821
    0x203040b150315100f050d02010818010207060203040f030f0201090503041703090d0602040302130519021602120606031213060e120319080105120c090705091c1a 71
    0x7402035450085075a030b030200000c42d04200154000703601403c184074214100c200310301401c0d0540e52407100c0032501b803c00404001080d90140d64410380b94941c03405415811003203260b80e840c90354007046000c0c00310704540019401213100750070281809a050400400b814031140700e000c01c5904024a80703001c074400000351010b623542c61031504c001c614040f46d880e14510442400c1600004103914100a220407580030f8011a03000382e40303c0c010b02c0b0480748180c0403514201c0c2c826010f0f184001201e418042258040e110089800c0c4403a501110380b50002060300280355004401507001c002003217200d04007030000004a02d1803241c81418030380707020303803941030303c0102d018101c100800800c400c20141d580c007034070440d6511090300782c81e07540505114002c0020300d804807001c0411105c2c1c0000809040000d5410603100c207040240622142900401a815001410034000c0103001c0c0074000d010b0303a90142d01c000f43ca1b0074514056441c040d924003000c60543032080c000c15650800780d00b0820a000c0030807507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 461558291 1250 461557041 461557051
    0x3060105090901151d0c030124050904050a1e020f03041115040308130b09030312040804050402040b03041a06060a08040f062c0c06180a090e0a11040203040b 69
    0x50324032642d444901550050080080502c0c10603007243e0300180c1c90b580d640301c840c28040200c0c410b0705281d403550320080c4984005e02c14102e07070b5504070000c0d4812402d100264040500c01e40b410600d445010000502600d00c1642c0700000540e0303039240601c00100320076030000c4c0081941429401d1200c070039040d503164007004001038861000744c88410400e0341d80003200c17040230740703001c0401d44c0700c0d6102c0c00c0c4484a5040040c1c40005480fa620002c146c40385c2601c140c552106005000b1842c007801d104041e14003410103001218110350611012071266510300181003e0414003040c16120702c1c06060003101c2c6516044814000c0e1001d0003444540c1e00d9130b20860300c401c000b50504041c50344840c80c080c001550a02c3d4003070151403810106040c4500502d00302d079501c0c880700d41740c00d0440d055003148035100c1e100090030356403008042140b640130b9099100d4481d141c40d0028590405d555489050000351038280d072110030103403c056192800c00119150784818000700740c1d401c50640c546a51010000080941 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 461559541 1250 461558291 461558299
    0x602120f030a0f090326040f0f05010b04110703030506060405180c040b0f07061b1d011e09151103072a0806180120130b0a09050906030c03060105 64
    0x20018145821940100d00700c542090010060000305040c014880d07001e1b072128005200d02c0001078042c280c0c6243d2080d0040b03400c100003104007511a5600500c1492454040340c40d5501c40d480040b240e0340354031581d448140c0d00003070b1958961075890000c04858004081034401d001c10301c000d010603114083c8414004c140701405007210749440360310714801d004030352040001a4000405445042c1c144000e80702d46482039109100111200d40c10840005000403242c00103508412103810a00c00a003400404c1c2c0c0040c14030f6542603841d40141240c0952050420000c1a100d020401038810103204524070030300240340c52a10180b44c0c942e010b0b10303489100400b401501403002c24800610316010f42c1505403a05403011844031ba503405100e62600821200c086080c3c198010201c6c52070790600411840c64180611a25414036003006050b40e0f030002c025080700091480c2c004102c4551200c01071045103115100c0d12503241c81d21b42040542c84005004034065000f1400c00080380d10000303040341c10b59400329 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 461560791 1250 461559541 461559547
    0x120d0207051207230c1e120f0102030106080c03011401080c0f0c0109050c0f030a1e0c0b0c06100605160819080103150207031d060d060902030603070602120f 69
    0x4100a450082000b006000c0c42c0e900241c1d500c100080c801c80f015002d10310405540c1e11a4200c0c4403683c84100a842d42900001c01050b5041400348442c01b15201e6100100102d60580507010f0341d07450300c082001d228400da9400001440745540150f12683d001407024141e92544d810000004088460b203441c8505000804001c075160700c04402c00e4030381c94803058030480d450321440d41c1020701030100c00c1c000f65a2806a6408440c050400c01840d05a945018004003004e41c82c0744e4034854110020000300001c1540d42003801c0009601c444141c0c01440d031010942e444032040c0251074100000170b0f0070100120100c0008001943c0c003c815205101d86800054000008500308244203120301422420310382d441035802415070f9009a03d40d13050324000c2e01040d80c0a03141c7e030303283d00c101d10030361201801190003e5480341c105400711140b0781c070001028140500b050307a855454810740b89603400c109621a008010000b844c2000c0060303800a0590703100509405240361b078401c410740700743d1800200c08a800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 461562041 1250 461560791 461560793
    0x91003050a030350060a03020d0203010b04090317010b0304020a03032106060f0305010b03010b03040b0901090c12020909070f0506282a12030e010f050403050301050111120d0207 78
    0x5030400240c940050081004071101c02030003682100f080d8075084c0540059a130b50b0400314040029108820140c1280e8180b401c41e02000301c41c4080850880c0c0c0f643d21039155041e00d84039030040a0010703101c0d840d04034a4080034110781240710016000902c20034014001c1002598a01035800c0403680c15041042c004541d2060722a1981921183c0e020414201180004c0540e40300780e2601d078a1010b80c0d020051a42c03a9811402d60307100a10910300d10010134000300d00400d001d1a00a80c001c600d44000085580c03079562149203400c0300c0d0703000c1003d9110381504074040d401c100f45000e44c80ba03130740d5001d0010701d424510a20224005070203014016200420700b60b04030004188100f0000301c203140c1381d40c80f40001640060130624112030610001030000a1064050300700030403180001d61149526a80c05e030342c1c480450080901c8075003036074a507403100d0b9440c03121181c602c00c2c14000e0b406561210303640d6041ca800541100451100c240c02e5a012a43e000c00344e0140105440e80324024403005a0394400c9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 461563291 1250 461562041 461562071
    0x509060a0f0e1504090b06040305071502071707140603270c0303070507091b140322030f030c0507050c2e030606030b04020316031515030209091003050a0303 69
    0xa07801d041d0405441c440b95040d00c5070000182003124180d05c2c041c4090032030314051200b140950300c4010070aa00000c018008c10514001e40c0301d1030240751040f21003d642d03c0c51032040e0400c12502071581a0482e4100380040c0f028512118001c52051310b0442c91400d001e04403005190196150405c90000381000c0d8020540074003145042d4031004003100d40350f010500705035172079030464031030914250b00e484010ba00b540e42984031840d072050a42c81d0000c0c02408a1204d03482c0d076200900100900b4403061003c2d4000c00080f1083e02c0040c069a182079102c1c03a0b503400a0100d400d036560300c0c01409028041300e0300148002030480c200700c009540104400c0300c4814a144114001140e000c00402c985403038600550341548071808503141039905000c141d0300c0d541404100d200c280c8a101403e0703d21458060000c0c000d8001c041f03051031500d52500d074556206012a441d070320b445e400100080e0006094200f51800c4100c10350800210114000c0d044c0c5941c2e00c15a88445414004003815106c0d510800c4100c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 461564541 1250 461563291 461563307
    0x6080103020f0d051e03040e01080606100f0201110408012f04050d0f0c2d060e121005070207090b030105090304061101020903070b0903060a0c02070b0c010b0607030e0306070509060a0f 81
    0x21000c68070351010f0300c0ba0b5005c5890740c019000b031f0181c0d5501e040000414850002c0d0141c01460003520300c41c58000c8076102143c50300740c0c6020000956413200900c1c003040d40c4083c018401055440c000060300180f000c0c0f4104080c1116101182c400c820b60b035040c6406280c90125811104100d40945203140b0340c3c40d03c4003041382060780c013400360440444000381c02d204401060201c0712888803605012200c03484140c04641050244c540040c2c07070103404405a0070700c08070700d01e00c45001104a61b20008000d03100416a982100c01c0340058116510401c141d0705a8001c050712150120000d000a00d000e40d00b00d80c0e070340120b12540081207056040c4c81c200b0310702135040346e00b04070001c1c099a4101e0b8480d901155a580480e02d1203000780f050000052400300309119407203048841d94060302000d85800392070f08668019803844921556640103000e00b585e9810002c0880d10310175281d48804240c038400701810800000c0042003880410448105140d6410040302c000140e18140300400980e8502c04458683d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 461565791 1250 461564541 461564563
    0x603080a1d0a090509071505090f01050c010f020a020d0c02030c0f0a0305061003170915090415080f160b03061c0f03020a1101030c0203070b0c092806080103020f0d05 73
    0x34403100070220f080911504550300c6101041d046854541e9240c03c107a01c00c0007110b50f882c000910034040c0d08014549801107c051080c14035295040c030122000007401c441f02e95a20f030500c540d00082c40802c035a018080c01840c15520b0500b101c01005540200c1d4417400d0055103148074090080401c11581c1d10103031620061504601103d0107490b0250070720b80354843ca0f0200f66804042c41c4541c4249442107411241c80f190301425a06022040036400103035508444c140686c040d46580d42460008648503188008000200c018102e60910407002e03820b00d89402d040a650a0007030f50148000d0041408807500900c09480c0c1c03000d00960f101c100c031465100403030000d01142c03444030400e090642c00108036100ba40034100c00c02c20314010b54019000c8400c01c040f01400350b0030612803803022807598030382103501c03000540a252601034058001801d0381c91034035a690112029180880d100045500e114003d00668201151f240d411a000941114a0050014420406500b06100b0003c0a0090040768 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 461567041 1250 461565791 461565799
    0x1090e01030813031407230d0b060f100e0f010302030408161509150e0606030a0807020607060e0f010f0218040207140d03020c190b041407030507030605070e040603080a1d 75
    0x2081660881e548a4001c3d07c1804030b6680034407140d00c0c00c00c512050490498000504c0700489541d540d882000030302d802403a20307a00002400501055071201001e500101041d6502c079280f000c8098200039480002410090401d03205000304400904002c0c125026416100d000e5880f54a103407409402c3c01e09860001c020480c280710101040100c148840071301c14803d00030a02c10f40205a00c09a62410122030142d8140d002444070300c0031550340c0c402056618009030003149407101c00c4d00d428050f01c44003844003100750300012102560540c284200311218818407415440c042c41c02c20038120603190151b82502c206e90020742d49081005400c0bc9038034080280c0d0a03a215601c2d00e01001c0c009420260f5242d00d18090f0000018500429813100340380c0642c0000443e10b15110764841148522034040c4818841c454500d010000ca481004000011480b0f170201003040d140800d8014100740d079407105980120700f421028400204050240c0310004228648811007855028041c2c000c01c0704000703480c0d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 461568291 1250 461567041 461567063
    0x16080903030a0503060102010c0c0206030604020703030905030307050a1206030209070e010309150b0f15030c0c0a06051f140a090f24030311120706022b0f05010501090e0103081303 79
    0xc2d8a030004055171241c4000d030001c21101c002e10300e060700c0c2c07080d035000001e500200c03c0001403500d04c4c0c60741c040d01086000f0301d8006081802507450514690003a10000701258002c10700d841e0b196481854003c509111a03030600505c2e1943e404900181406008c00080c00000c4142c8212031744651b020b0303d0444e402806c1c14210f0051800c11400502c022600c0c180200c030041c66840042c00d00d0381d85041e0f012000c00800b0303d19654403159409603007044094000900a98603504042116402a2030046550244030070068003d95080320741403200b54031040d170051030300410382c040d1f5544030350b40b604844401c1c00106a81c1d040160060050940914401031181c9481c05080a10943d81500703003a20f10a03114084240007846482d507990b0b00c030300449102400708010b030f071300010629000340003404184154040729141280000701c0c1240601d0380e54004507615070b4641c0100019001e81030042100782031501c0c0103414200070440000c0140006071040300006000350f048144288910300440d001590070364 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 461569541 1250 461568291 461568307
    0x190312111603030816021504050304031403090f1002030d0b03340801050c0a0e06121e010b031905090705030a1a160c02010c030c0c0b130801111608090303 68
    0x8407892050100390700040c002c000140c019580c1070410381580c81a0303001404119400200c0b4444c42400500071541c07804140300c0080051140d01c03000400900100185484d1002103080c0000d00001c5140030b8403d080c40c03138002e495180c021045842c20211185e01240341001d20002c0383c949000e1003854441c00010b031504040c00c000304400280e445a1207074820384070b03c0e41c883c21182640c40c11354010602510412901c00440d014031814101074502500c640d0404601c40003120007840300719040c079000040c1e0164500c0c0943e8029080c1d01602d088400c0c2da0550a003a90140940240031400202c055500e00c045028020104400e0008203802411a20360b02d01c00d1806103048a000c10a01000003100700c00324500214441c189100d28820341c1d212880018250011103002030303507400907424020302400c0c140100340d82c007242c4000b404c85220510340c0d459020b141c11030501007540c0001c403036034580010f0110000c4194110b0704000152810380c0002c5c00c0764140074216200314074200f51706200c0015034003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 461570791 1250 461569541 461569573
    0xd080a0306030201120522030c0b24010305040b271b0306070206070c0609060b030a060b0102160e15060f070303200909160203090402070b0406050619031211 69
    0x40a030b074803ea94505404025003090402c1da03009a51252421070f0343d200e400c1c4900e442c0c12940c84601e00a01e440342004c041c549800501c8031046d1a0131052410201035007181480f0350010405060080c40c0820540c86c4c40c0d1121080e52070098440324560b015598a40f000780401c00c44141644401e0050b104541c204210303031074058500029090003809501c0014034014000b01c1c41034031418168440310449001603a820b0b0041c044000112071250340c3c3d90b0781251740e440c1040005801e03845450006100e00340701c030019182083d14081c0c00c00c4410014014084840010810780e002401d040c90074090600ca0341c0080c0b0240110710415556110102c0e03003409050f855040403282c0001c10200441d64441d4488181480c49105c41990708040d2a2002c1961024041461a0386191901c10b4a0900908800140680e841410f098a4040d100320034402031198612407140c118000301c0c0e00740850f00380c141504585030324910004d8400c0600f450503500481c06071010411a000314000d031102c884508d03c0007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 461572041 1250 461570791 461570801
    0x1090503030418050f0c03040611070b0906010302040e0102040f051c0813030c0b0c0309010e04060506160b090f100b0303091c061a010507020d17070b0a0e0106140f0d080a03 76
    0x8007043c581000045607040068140042c05025140c02c0c16145a03203035143c2c01c010b00b008401e101d0019204014400c0410240d141c1c41d409500400082e1016526500411080d04c22001104965074030411040020081003a04c802c1122000c1c1d8040d00d440b01d100014200d449040744002d0402c020010b00f040c151400c040b078000c1680e115181c0d00018075242e08041601d8012100c4002d12039000708640c81071907001d018a40180800140003203085074079400495040c0d002501400e070083c0c0d201d040102002428a8050703880181e000081c40840080c03941325640303074a0800c03101c0c1440d0f601d041c00006034400b441180c20a20018100c11841e00d1102c441c82040c022140091b5905440c4c0302d040014480e44040920390850141d6556040a00300d4080140380380320300d001140e12003106c2150003641e030310722005404a02e004040801725407034500300210903100d503001507070340c2c0d40d00d008411b0002101500c48960650300640d201c0d040c1d00500d1022030a00f240100000c1c010103070125240704055816000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 461573291 1250 461572041 461572079
    0x1e0307020d02160b030411032409120403031107050405040f050d02070513020d1803020109050d1b0314090406140f0a14010f02032205010f0c0c050906010905030304 72
    0x855800e420144000c80c0ca0305480c5184420500c0180000c00540d010813001e1904a4003940713800701c0380001c1c41c7c0001e1429103a0301d40711124011580300e84900340c507401c0410383c1c09241207025041030b1008a410300e400303206034040107040c010f0a44030801405010480c076409054044c1040006007020304080400c0c1d400e0501c101d03581d11030b5006001d250b42c404038000d0112030029222014503030304c144800019420800c45010100e5550f40e1100742000032404c5485442e0103600005240d0155040c07540c18400301403ca003041c007540e40070304402010481004449141c040c604048a5100c0141d40e102600c542100310307602500703100001c035180500401400302d01c88103c401610031407281003030040b0040c0d54468a40c044040b405940d241354020705d58401441d405106032442d040210092040311014a82048040009410b051240c0d50300526400121303c1c0c2402d205402c665203503595409018140103080c044c44000000c41c009034000c101c40005000300800352500c440d03e6581c503e034520003d140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 461574541 1250 461573291 461573293
    0x1204090501171c03090804030c140636130e0706030b0a0e06030703080301090b0a0905060d0f020310060608240a0e13020a03050303060118061b02061e030702 69
    0x1000203410010b01d8090108611038070040d288166003d0040d003800b44090840c0f40c249a01d82e221680024070203001080654810344403a501d603404d0400c0b46410341c1070745451078060781c0d0400220080c9003075081403030421201c0001302440c140084010a00000d910f2038403e4111042d8400b40c85610385580201c030340c00c01d1410495200e56074815044040e90440c440240d0041c0e14200c6c10321880c0340603a41c072640f1880140071520201c0d039940d41c00d0740c1075200b6886202c40981e11a286500c3d0b26060b81211300400b55580144400e041000c0043c083c1c015002c0003d09a8451301d12420031500c06205600006000380c000f0045a130782ea15000d000075004440c410003041c10304424090720440000305001d14000070309003811483c18180c00103c09500030340302e40729040300c840d294030042e550381054002840c403a1015584034189000050710449040c0d02e94000004246401c0c005983e000125600905c1b9580780910540000e00102d11280716070544200e0388104036021040c1245004011070248110368 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 461575791 1250 461574541 461574551
    0x20706050601080709141201060506070f0507080c060d1d16080c09040803010e0c0f040b0403030f2109020418060b01170c1605010e010516090b16030309030908120409 73
    0x1040b21406498003802d19046c00c041c46031282414080946081c03a41ca00000144240d2074400095040d08900003c940030800202034800b04042405000300804041004288000c079440000303240c0e000e43c100015800359504050000c9601000121419003440f00a483c40c0189002040410800e14000e440d014815150341048a052140d0740b5846030381c1183c0108d0859080c840e054580520143c20102408801e0021359922480c07000100000c24802400c1640c807859450b0143c130110064800005100d1203510400500c5404d21016004c0300c1c60080c00030b200406840018001c01d6000c511034054800800313400d040105c2d5038403d100100b000d881d4800201110072210081190483d5412340542d801e10004411000c407000f2803001500c50300010131001403900f002e81c21070b54210b40c403e40c9441c00080f05081c0c903401242481c0a01165a00d5600e4140e801141e11032181225100404169070b40c1d0a10042c94071648000010301002c6040c4c1d010b02c0d101505240e11900315014000fa442d00d40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 461577041 1250 461575791 461575801
    0x10203120a0f1802100302161a07080603030c280c0f050111060405030706050c1c05060a0506040303171e0a0603120801270e03040803070c0e0106080c071502070605060108 75
    0x1001440314071980240410807111610000f10048d40051810915200580d810540050600d6a0b248030304403280e00c11001c85c1c54071480080c40c400c0c0160845011307800030851600201404960b1035564032049950306036607000204084030f1100000d8015290b440c7c0701c03c01186403c4082c401c07100711103017603031092251031800c82c080340c45040544004165a0040003614001342d1150007455011031000340250800401401c040c5180301c08000840000c0d035a0030805c003190dd00000c00401400054400605017819035a010741426103224445403041110b10002e442401c54016820504000090607911800c183c1075941c00780010340022100d00044ac0c02203421644a0142c05040300c0c50125107040b05140311039003220358021000d80301c1c1807640319096059150030400c020001008140002d6655040c2401d04c0300702d4840d9a040741c00c103400d440004114003944010405e0300440c500f40306a80d54003651a003040c48101080c80d0003000e07400403a0b0310081c81190352105d4401c030b1080c1c035215520790361 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 461578291 1250 461577041 461577071
    0x170f0601080115030605090718090c0602030405060a05090a03050f0313091104090b030111030106020706020c041a060a031e020702040e0a05100b13090807020102120c120702010203120a0f 82
    0x3d1001003040e428910361003000890581d0708415005008403007903030513039034845104840c51141002200003403621481c02d24104112010002c00902852000e141041d0409000503518415240090200440421800010340e00c00000b50300560340a801c484075812000e40d0389850ba0404c29001c030480b0080b18000806800b940505094844060780d80c901c0c150500000300f0062a607100d190f90107668500d021222500071314002d5001e450769400170304043c1d150407002850301510b6125a805242000c6840e56000911824124030200803501c03d0748074040d84404400501c0e020880a00e84403031003c000d515207005500034940b07130313009480601c0303080e42002c4250350321072207030748000c0c441da1161a038401c901070190702c54003200d48000e00c00c5449550001076081541d03e0001c0540e58040b0000381c100c21580c04000d0b10386511007000700307141806180c1028a440d10305440107800901400181c1c403085a20038812240c21801c6800340b0307000360402c1e0150b18020200d014058200a10303045c907051641038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 461579541 1250 461578291 461578301
    0x609160c14031315050c0a1403120405010522050304060f11060a0212011502060103061e0f020a0f09081f09080315030c040e28050f030703030507110c19170f06010801 73
    0x4981c0c4010003c901f00361307650400105001c2c20107000c9000500003460544500312081c2e0042e0f000e0400400e00b8100315642d070702504a0360384075051800800c601c900004101009a0302254841e0508a0602800403001d844441c0c0c1d6924208507030080707008101e818400e80c0c0c0038001c0d094500c50003800680e00d99489140c440101c0c2088000f43c0d0101004000041c031940180d00c0b00402658840c0440e031106080200740da060313080301000035402107034003d01c00f640458003802c140380d0303450008020303450070219984812404080748000310700003030640e080e440380e9001445c8003544080c101d80c0c1ca01d80040e50860302100340303081c144a0300403184003a0b124501401110b0b4186522406031000d00086110f011100c41c0003200144182c240311500b002040c0c042c0b1403070f1004c10642d00959500d040714900101203840007482542031000d0301e10b001080c5040002d50074182c450554691000b69101c48071050600d00076403002c0c0c002c0c0344001c41e102c0f0008020841d101c065650204803070b005c1e40c85049280c00c0e50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 461580791 1250 461579541 461579557
    0x1061214060c07031205060f03010207050c0315040c03030e030109021815010503070e0d0f020306070914041506080406090210020c19080309100302040e0705030f0609160c1403131505 80
    0x78900c1415017580d07800590003030343c024800900c090300b00c01b980d0010a007a03800441c0f00303883c207030040e00380c000c418141848030020700000b404441c607c52a05a5078581c01101500024007003144c6c6e0f5107510066282507200b100c0294005198400c0c2500c4e007089201c540c00201d03044400319403501da549040354040c1c0d042e21f0048090751607454030f0100c140d00380700300140301401c01c1c1c3e103203400a4203590140c3c805000365400b4107a00d0b9120350000d8100380c3c040c04da807000410528010f9140899501c00070400c02c4a00d015500700e0700d001da0341504e560a040c0007800c28410040c0d400741c441c0044031007480e000542c90380d500308159620050703c0c082404400000d0424030990703040b5013080180007260318003502c080c10a4102d40c240142070648903482450400411991540400c1001041c030000b0102c1250315640b00c541101c81d15800e191903489001401608401103042c004803010040070400007544224030030135000d08a0b40c44554841d0001c0c2c0f540814030580c40034410045a01450a120348100c3d0048 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 461582041 1250 461580791 461580797
    0x10f09080901030b031f320f010f03081927090b01022107030c0507060306030c091e0506040b12010c030c020a03090509040809031c020c032d01061214060c0703 70
    0x60440c1034406c01500300701440c1e910a01d42e00101500d48003040411585078001e1034090200e5181040030a4002c800607000812403003070300755041000500e01000c4504250000940e60100c000c222000c1d94095410603900b24554006141d01c04a40050440b600072100301c040148103010140006907180c0c4400802078885003800045030544104000082c4441e42c864a0719941c0540c003500c50900789040380c2c0020700001e8440e80c04005010b20b001e01c0d20040e02c040b8008100007003680804203440654000d18407400307034a904c009012503681d50304c580c610241c01f40c00d00c44401490203803140204a000c01c540f01203440d00405d042c0d1203200241400480c0c1e815120802c04c2400c02c0c04020034090003c20484003040f08120b05506900c00340701380c2c1240200745501d489481d020a1020703080420300020306009601081c0281c000f0140e0340070850349802000f40401182030800790b00c83c050900e6403c4080c611250b510704000f00048a00a001c40803401c005662064440f102c6903040791298140242c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 461583291 1250 461582041 461582083
    0x9060d021f0507020a0f3204050612030d0b131b0c050a0204110705011b051e0403230c030105040b16020109233a02010f09080901030b03 60
    0x704060088030185101c9060036800c141c05a400100a04c100c0d80010b444074900d920304204142d80d04007000901403181030b2802015040c001c40c0e0780c03404040403165102e40d0f140e402207621900c0e5180d01e034150440d1f000540b99120300b036407101d034094900040340900604e0712100a000b00307805c5101d021440c0b40e041d40d040c102d5900000e4102e64149880405403a9030007000c0b96840140d60324810b04840d1102042c00c69240c5496041c190308480100e800503559800c610140d55030300760b000301155840c0780d501c003400601c5400c41c00030510301e00458200811080004411030302028840c803118507a800a00c04881040d0f40e02d400341801c0c3c490a031002060a0541400f140a6101c1e400003074494407818400040c44121948480a17a040c1406920741805045010045a500e06014102c1042c503200650b00900d6078443c4410403045000503481741e0080c881c022840072910039000346000c81003071641400640500e00f130a00455114020140c00700e0720f0110307660030504000c54000c050300701742c900c030b060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 461584541 1250 461583291 461583319
    0x39090e040311030403030804020126070f031d0a02130603080904020c0a0203100507030c08010b0906032505090111010504170904090605040b06040b0d120e0109031a0609060d02 77
    0x2000490103041101880a605807a01810004101900080d8040d070b4465005080500001d010781740b130b180c1d0080301e80a00b00c04482602c100c51100c50f40146451506400b05d000d800d104400910303c1d80c0001660a0100c8045181581c0004910454070f008a9078040074601542880b002c6a41500c401410910107010310810b80c034080e405405a0b0327400c41c082e11404016a0700090610240c0140a0b4190744e4600c01d00c01881e60500c1000202c2e069414064020350409203920450300884100b588600c1c80000090441142e00101c1c90f00d8001d1307003000404100c1000b1000c1c2081d04071440c4140002d0440c00312011400701401a18050742d00004845010400c0e0b94880905602c145840ea8000d41c42e160201c0002d003003071242c280b140d07002c0c100000440c140101008291000340003454464a9844d08003000315505149411003940c0d41e0425900c110500d20059500005c00d52010302510101c00c501d41c1f042480c1103009104400c21601201c090340ca10041000f1114054000780d0002e510550ba04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 461585791 1250 461584541 461584559
    0x510020d0f0906060e01080307030206040206070204020421050d1704020d021c0602070215040503060a0b0f1f0809033f090a0b160503070e133909 64
    0x480c210320040c0440c1900469a02a042c0c400286084498039034900041000c02d0105140c4ea01400501c8003039031810501e600d0096a50102070f001920035840080c0220031540c0300e0f4100c41c004d18041e4418104010204c004998501d207003601038800e030040342208140d0b00c0c840c9046001c46080d0300c80040064507560248034148501160482c1c00c145400c00e03400c16074010044882169100e074030b000d80c0e2a0024414031032891107082c0662403140b42444180f00b55640855081d61010b8803810000b9415484c400103003407660710300702c0700382c0100065410000d910000508062240802d4645070100c0e00c2e610012992441003d11044015102101440e00003126034a41e0011400540004c12418810509803d0440d0280d50300503840d4415200710702002140c500c8281d1105c108d0100a84d190810000644075101c01010042000f5107011114016a5501118040a11041d5081021070796030440080c0588400e82d500000059101e50329034043c2150210000380003241e9541004103141c00010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 461587041 1250 461585791 461585797
    0x161e080408090120010c0216060f05180d060f0b12030301060c060204080d050c15150f03011b030b0f060702031213030f0606050406120c170c210613051002 68
    0x2d070401004690503003901040f141e441009164020001491070b803c90720182c9483d007407000381400c50007046d00c100407060304640361161003ca5401c1517a40e0351185003814000c2c003c8014145d5124402c4503c2d003040c000d0310f070302440c3e02d1100b41d9404c108020074042000071b41d24580b1030030f0680780d0080005010380b900c41c01c4076440c8948212000741c1401e4451404600342000380084400003240030070340004000081080c10030124440c2c5e200750240c10020054100c14188141450050b84480f803090040e480035449128008104015070486614410008010702810610b40e40b07c0d00a00f18000113901c2e100702220780c100e03401001031684800d0307c910300540e034106000036650300603c15800030102d50644034412855114010008140c0c1c140740801c801c50710f0076040880c0039840d41c1d0702180060060340003d001d903038052501403d2040c0c20200c4c1442d02d0f903015603264001e61030360034100701440401e54500d411458a0207880266940340d240501c00c0201c508040c00d1640154075410120f10a0303401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 461588291 1250 461587041 461587057
    0xe06010b0a18030803092107230d0306150e03060a05060f090a020d060b07030c02010e06040f0b070515040f030f021c11010c020111040509130605161e080408 69
    0x510101034005100d0103805561007954130100000c200000644c0c1400300d241280c08494004040f0388540c40459854029071600500c2506407803c80b175605c88103800b118103025007090840d00181c1140e140103020745054854001050662010611101c1c01442e5040c24040c1c060000e241d10394036000000e001e0702d009003513150085015032101e0056254100d20034803400d0038500150380d903036040c10707008205d40f45079208181c40e64003030200c0400298815000c0d441a9024606250b0002d045000503405100c1c1e640301a9010000200010720407044402401d0072500030025540803548894208029810458000700711224459000300044e004003014510300440380704a41e00d0b160003a21095041c951248040c2c04111301d624490f00c45035003402441208002840240218902292000303400d0280380981b610590121000416035039013003a0008a0641054081c8054100781e05d0400c0c6103892410b060700061400300003e101c030843c445100341031002d540ea6804071540c3d652100c032006c1d000000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 461589541 1250 461588291 461588297
    0x302191805031510061e03050405070b0c1f11030c180315090c0f130e0109050a0602030621060a0b0607060603030906020c032a01021204270e06010b0a 66
    0x103804102601c003003048400b18848500d5840450070060f012803448003055009508002e00154544080c400300305100340003440c0342c10003150039251841c045040809035040705840040c0800c1c0c08480001c005907409005c800104203420240d24030340b144080c0c94849242e1070f140e200c1000030030380c4a000300c801008040389211402501f00c1110000a0602c800301003c0c0c020384a08100f40801c1c030105108003a500d60040324000c05254006021403007880c181190281c10036030300e070740c0c4950080003034011001c41c55100701910318580c0503143c00030080d0070556030280104100c4042c060010018201c90117806000002001155505c1d400381d40901084241d081e04520b0920401000442c41d01401015522a0302c0313084050b03040c0f140092401c001c40003814444e502c444203001403e50b01100c690500d03c559101c1c0c80081500100507840c0410b061500c0b480039200003000218030039658011494141440c0402c4011141c0e012941305a895103d5040040e400c400e00400403095000c006011001140c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 461590791 1250 461589541 461589587
    0x2030a111c110a06140402090703020c0a03030b030a0b01030b0108150403170604061701060e0a02070b0f041721070507120e0a0906060206040203060a0207050a11150c011b030219 78
    0x6a00e0341c003505c2e032450b802e26505580b0340c2803100f14034100c040241d000d00300f8076085051003451495940e0302d01007920081c041c150f03103030041003440d00d0a00c0000e082030b80150401031a541d4a2902c0c4209950034800d07600f2500a59401140030302410b00d07003502440d059030301c524100d408003400042c20b07900030308181c1e48070342d484500080101144024100140d6482d0000428525088182c0d28640d80204805221403040010b10002141544090b40182c5c3c0c41d80f11512603034407031500b1140a201e614905ca4104c6000c13591042ca40380500c8580c03050406002400099100c01000740c03034031300510034001c2800c4900507210010510a1b984c0d1b041e0800000c2c01b80082c0b07941c0383c079804100c96990700000c0040c0c0083c030421083d41070400445401034522a8118601001e5844958545806204c001c03c034201e59040c070001e6a50303000102c000001d502d03070000e54619485e440d0750f00800400312954120350f452140da60700070b4000e100350340c0e0b21010603d2504100e100391030101c60741400382044c040354003042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 461592041 1250 461590791 461590793
    0x2070b03040821090c0f01032003150607080a021207030c0b07091503020702090c091011011415030f0706050910050403050111071b0807030f020105070f0302030a111c110a 75
    0x121070f501c1c05808a14090496051802c007070103002c0c21a500800c5c18141000030307503802100c0c00c01820745c2c2170010482054403a11666210f03040034110620f810b07030201e0b0104c0e1550a00c0303a044006e2000e8100d90f000c8425030261081081d8281c01984800b40200d020540c0190201d102c0b61442680f010341440c0440d0403d4540c225800c401704d00040d14000030354080742007002c60a1850440c1d400c818104089800c001c0d034600020f0640b00c21510100030030800c2c003242520700ca0709401c0523003010350b91130421900d490006000b84001e042c00c5480c501c00d10880c0607148401802041035010380d04103540d0585010405001c0c0610a080b14081c0300401204000010104000303124521203606080c503100d40c0c0344020b0400c4003401f060881414600382100d0010054020005001000c99030b00c01c105140da2001070005903080d001d614005022501d40d01102c408069010000702400300c00342d242c4410071031a501c4007555030200858510780c2e2020015400ca0414091904a154281d941044804010003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 461593291 1250 461592041 461592097
    0x613050c0f092e0905031f090302071d040b0c031915090212010f08030a020a030c020a0504020a020706030c02010b010827160f0b21040503040803070f0501060602070b030408 76
    0x210300001d000030f40d805401040055100400350001c14048006010612029140d8401d081200b440102100c0d590040802014024800303517004046804001c1c2000c03d280403809900081124200c544c50072410014030203103902424ac0b800ac0341104160f03410403043c49032110042840003d1030b6038182071030b000022418000e000502d0032945001007000e540d450304074180031040d40358101d05415042406442600c40c0d001544202c03030303a014074108040508600204e40640815003041c0e07080f07400012440456500002c40b10202c80c032a550030020300111031400c1307007251088040c00b400225003102280410200f2400400032a140d20100300559058841c0e4a181040d0a86008008060128100b00d40c480003010000101107a4007242d14000c961101e0349154196600203982c480c41030408182400702c104180c40c0903108240440741d842d46542820841035000c448100c50755804c2210105050b0300c0840c0420882c0e8940c00035038110b440e03c1e82c0e01e212030b400c03000c0c4070313001c04004820100d441c0e60 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 461594541 1250 461593291 461593339
    0x3080f0921040510090317092d0109050f030a02060c0f150114010c0b0a021e0d02180a060905010c080903070b03090f120a0e01090e0a02030613050c0f09 67
    0x841c072075690358a00d8002440000030300903046030240011603008001043c94035402500400960400c155500b41c4400000d0342041c0c0020358901c160810310150f80c580c0105400d64401100036241e51100e16556010440108215002a50580c00451602d401030810038060f140c2207030088140e030740b1240c1107146189403c00864103514204030300b2004001c1d0b01e841121201640301300786440301421846403a0008078980107003412041c1c5e0350004030b0322440a01e648094510b20030488030315070703603158011115002c0d40001040704005060858800d916107400704a41040710304503150441070f1844c0000640f0740740344601040e194014204140ba240360340510603200601401408980c0340e08018040920740740b08a500f065035940034000810311010b4441c2500c45035040323460210301d1415810f00480d044071869108002520851050012040c80e41c0c025510030300c0c06a61020780c0c0409005450142d5001780c03000b503505841080030343c0d9500b9001000300091030000d0102d504040c03200003628040c00b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 461595791 1250 461594541 461594593
    0x5160602071b08010e061302030f1f18050d05031008010606030606080a1a0909030d0e0307140a0b0604090602090607030809010e1b120c0d081e0703080f09 68
    0xb02c00c8101d2422040105003503440940500002041500a0014000d81d14503024043da40207458841d50402159410007a40c00464028000c0d20303190840c010503d0103581d1280501d0202c141040c08c0030149019148042082a411000a125600f0028001d5440764005801c000b1071500030305010a03696800d000c1c100041440f81c0c4c0010702036103482e0008245900c080d110440c458100120808001c2c1c100c107480c22440c0c82110148195140e4144052444c8100c4087c0c00310903060565040c2003140101c00f07419264015010b10f00400707450340055440707c202d000c1c000d180c1c00c03030720001c111542090390081c902d03244992801031410b580200012005d81051308100d00140e41c040800080710001e00403080c400c2080d800400c09030780c00350900c900341e581c201000d60040548200c0c5d215034090400034186002009011010810858100355010380d000300301c4941c1c820100d041910742c804500e0304039041160184c0e1002400d856408056850342e0f4083c04402c41440354241c0c9003084003001e00156142 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 461597041 1250 461595791 461595803
    0x30304020102010c09140f1f0320031b030907050402070503220501020a060f020909010e0a1b0e01110a0206040b0715050f2d0703021804050c0a0516060207 68
    0x914003403000a0a450104213000308000d4017603020402440000e8000c114000d08442d01d01502c002180804c00c4c200d40c40407080722120700541d1904070700e50140c0c40602c0407120340c1c4024250048683d85407120b0712064807083c100e20000050b990007200d5030b5001d1a0008105400e5910080c3d482d000901640c2003500b040d9080c2d0030000d41090300308041030300400100400c42944180c5498100041d4582560380da02800c507a44800a00f840311200c0c0e030449020b24001886411596100e1114101c2198110b4800e0009071411a10000240c0d00c4803024170045850755600c40200310b01c00046030114445184401d0340d1180000080040e41d400b009070018155011905423505114102500b07114444202a40d030903150005102d000f08040745925840181001504c1c00006905522054600c040111117a1101280140500f065054009100c103c00d220510b0801640d602c0400045038000e5550383c0000030108489000d0500550250481c000102c101a65038011503c0d004181c1e44400421111 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 461598291 1250 461597041 461597047
    0x140c18010e16091505220302120a0b04032607030e0705220b0a080607050306090702160e07050d0203090307060c080c04090902060d020d0b10050f18012003 68
    0x3120714504201c40c2d1284a0364140180c03a89041000351121a0302e01035074100302881e4032158445400f91003160052143d401c07000003d42c16244240003681c0b0741c1d000481c0320b041140000300c20403400042c00e040641d000100303034001c0d031505d03075054800c00008a568500c22013155548295034140e2041e00340300b84060f80307010403600980d50b09a402c10310300d6000a4400c4e01410358910650240c400b5202c1c0400e50000c00007040145000042e0704007900784c1c0303e00c800d8030410082006080d40300001c3d600828054800700f01c143c5510b5002e984031340103444e00c40903500007018100100380750310003400d0b0010340c0340c2011480c042242402034180d83c011152581c5a600000e903032003c11269101e4140c02045c0351510220606100c280200284202d2080e142913580f12400c03003065543d81030407202d00c0035002d2011555107030701c0300d00c05024041c0101064032070040350300900300e5140107004607070380480c0c00b56503589860b2094000c0040d50040c0e03103000d410080d04188030614035000614941d8510340440007103071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 461599541 1250 461598291 461598299
    0x61e060a030626120f0912070509220b0402120a031709120d02130b03040b09011a01021504050708030f0d050c0a092108130602120306010c140c1801 65
    0x81a10a0002d804614090b00180388400404a1820305401450b8904c83d90b8a681d9100103c5502030f1450090b448403010701642c80c5d00100050310803c540081e02c0d05c1c0400e41d00d202103200101055540340b841003151810b0100040c07962800650f019200403c072442c42c00c105280700d4070b85800c0c030004a0114a80688400440766000c0e2507690003034180000304207020100780100c0950080000b0658030b141c01003461130000d05031000c610064098040c4180d264a49410144101301041c0d82c4184c05500c0c00a82101200718800b08030043c1e80103800a12803203214844000c0c107000001d1041e90705000703800c00411001411700040c0b12945040b900d01e41c690105800d420304486016240f101c007080100044d00c02c05170010214000c07154145580c205407407a03c6200348001c2000b401c0102010400603c95034408a4080d640303040d00d0b4164200e950302100392032808803503c01601c006000c2007403130804100003903c120310075554008401c107450b107000c4414013040d05001a10300c46000a0340c2100148 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 461600791 1250 461599541 461599559
    0x90e161107030c060503040c03170a18030c1a0c0601080322060e01030504080c07080f011a0d0b3103030e0a0201080712060b040909121106061e060a0306 67
    0xc0e038858591409881428556a1031014544031441081c0501101000050510031400144002950829004c2c0c0c84100c820045007100d52007650302602182ca40050054908011061402039a07801411040369900300346046c1c1905090340003070b0280000410102c0e800d00e60a0141500801030440215158440c0302c0c000e1540c8400d1900c0c00052440048040000c0ca03404800810004401c0c20005415191810820018816800e03403524611a0304400110480001a00b011140305c42000f000380c0e49600e000703524050810110254060315001c0303800c000c81e04106099801640303c1e9000e503002d100058000b030f0400d600c0501c1c0144813242500101c107058150050a140a030300e80c000d0300111181d6400600000b0300034000904200f4100c2081c000c00300d641c2d00c2100503040540c1002e840f503940313000c1d001c082d242111003268410010206c60380005d02a00c2d140c0d24100d0440b01500c0d03d5507440d1f05000c55031100809510680c4200c400070a05034031070400900e0f502503181d6012070030030300f0030780d01c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 461602041 1250 461600791 461600807
    0x2030709090b0f070801030807111206100f0f031205040e19051605030a0f0b06040801150b0403020a03080306031641040527160b0f0703030c090e16 65
    0x22400f2294808100015030750700c014aa410b4a80c080e40c41d40e1034200a0501c0040003141c110402d400212104c0c106000c1400044c8051150307040304d40c0140d503652140f0102107405000d11451100040c400710500c0003400d129114061b215082c41c4c440c0c2003654603074018484030070a80b103501c072910910303400b25500d00181c0150f031750103480804030301502407078030728020010b00c0b005006a051994503014415511810740080c2000d450060081d6102ca499010300c40c001d100c11035440d903201201000004a142e0071a058808403070300184440c03403c07465078680f10720070340c001009507a0500070200c0085540d400b2403030000140400310a1184200c00c096000080004103015402d0005540c08111096140000c804c2400c10815140440ca41d194141ea0305a039107041e100700300341d040c00c41030203a540b410b0010748498011010740e5003009030b1b036a44075161071074841c61108000524040100c003021034002e030406560581a4504900480e9071082c00c21f143c802c00744d810180d00c006200d406280c1a61103070072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 461603291 1250 461602041 461602051
    0x3030f0902060909040507030605090d170105031509160603090203160f180b061b28142104063509100f060e0903070c06081302030709090b 61
    0x1040019520703000070340680201900e06100b404800001030030080140180d400a5034850720038800c83c00d0101c000e07522503450000da4400224520070004100d040c60401c0c2c0d04a44001d009001d2240e0217400320002008000c1140d41107101e014500c0410f900201e0001d0010005a58001a40d568902c10182000d61135810f0203a80002004148001c1410313101303600440d19001e485040f80500c04503010050000c03403404030340c804130224886200824903400c41072a0242802520100d4041c3c41480c070751005140e000900c0d4481c8117407060300140d04500f00154000203a000c844843c044400716124814510701401021000400e0400950f03800541290b0a400b00700c440b500c200d50a61150413110aa05021001036500480070401c031590601c0000c40e00002d00e18144000301c5400c81003c05045a40300300c00102000c00000740308140b000c81a201d101c0e030302540d014180c0380380131030440d0f032a803011700809091081084a10010ba40070040d81009080301003003c201d0104509100500b050001c2c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 461604541 1250 461603291 461603321
    0x1b03061406030705010f030906060f2111010503071704060905010501080f1903031104150909090b060409031e1d0102010608030f0d0b0a081c0e1e12030301060c0303 72
    0x911085650100e0000107843c3c003840c04c1a030301c1b0340f889400c4018041340d02d8040c103100e142c03100103e500d0400d410304809541c40801d00c0a6140d4184143e000360b0b070101a8080c10350842100c011503d503110f00c0c01140c200c622490702d100c500e040288d070025a42c03801e6030300b1070752150b683d400401080380038024207005120b00809071050b1030741100d055131624184541c070148001514040002c250180e4801b00d845074a90444540700e507158086030702c4030522001749101181501000003880b0101d400340b40c01c1540c0c803141000c200e03200d1034280700282454540c100e0074401121030790800700c504a103a5144e49007207540c17414004080c0160404240d12403524413411a410003405002c444000800c5441004000000540d184403c0f680741340107045c50050b960f802040444001a80ca50008130070a0703032041d00314911b602144450044c0c50341c01d070780419250440112801c2031002420713a804501c0341c1001910041c0181c212007042415640700341c101d600800c224161460070305a140c403586018018180d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 461605791 1250 461604541 461604581
    0x10602160e01060e0d26070501050108011a04180204020a0521070203040303051b01061205010c17011809020a081501091518020d05040506010612090b07030e07031b0306 74
    0x81070400501e6000d40a00d2032176100908001003020818007117040c1032400700005078026401851644086c0341903505600300380011942403010301c504003222898120f2200c0d500c40041c1408042e00c40d00d2030307100303495400c4d200b03c80140e01c0750300050110040316655640c0e5250728003001c09110068217031120924a1a10400c0302d810b800008441c146c913014209181c0b660718a000c41d2150350840b000c0840c09500701140054003c411071000e00c0c020f07200350028000c05011190444070b070105d5103601c114111008004005212130380313110114401010b00d010030b42c2c0c491a000f00344414400d41c41650658043e240c0243e68000826195015242014003030201002180ca0348461303c140303004400704680c018a203041c2d050b400364100c0300c032516103e1080c842d0f80b520781001d40d1284802d200d0304000c01c070401101c1500d84094450f81c030351a6070201802140d92500d0400b107004082040071602c40c0d00c69a20044003050410401510f610403000d2503441450840c0b80001c141c03000c014458808500c61 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 461607041 1250 461605791 461605799
    0xf0e0103020d110a080708060106110d09230d080306040513050d18091506030c030c0c060218030a150c0302031338010503011b020703060203100905010602160e01 71
    0x76072885842c40d80140043e4030420540340003030441080ea5010080030b2040c0302000031092004a02e05041342c0303050f00c1e403180c50070407908400c1c2c49684021418000840105003400102d205981c000598840d02e03603042d0520001c0004a01e00b42d4203840141c50900b804010015140f604e8000c141d888622451003411419440c0e40343d954988004401c5405c1c800f04107811707881c1c080b03003d00482c0241440c00d018003c40b506507030079102101d180d001d0700c0c001900b01010f0f511103500038001c80ea107124071599058078041264868100039000308685114912548404600d66a420081c445845006441e4004000030150b100c07411104c1c00b21101041c5401402040403c1c1c60500d00c2e18041070304241030007842034504030495110200c000800c0e000301c103040f914210150701803490905035081038000708002080708188444c4410210240320060340444810300004080d6009150001c0701090110241e54071942d004090324404d030000300060340b00a250b180ca400b41113280500070601c445000307030307d5410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 461608291 1250 461607041 461607049
    0xa0f090f0c0f031e0303090210030f0b1f11010f1407030f0515060307181205062a0a0302090307180b041a120c0a030b071409060d0902010c0c0b03010f0e010302 70
    0x2da5800801407001301c1c0c20020505010b600304400c02540245412030450700c040000d4010140442c1c1041510719242c41c5094a0510340103003c20103001000c0344140c1801410103d5194852244405855495100012051115004006504a900c0c04404462030090001405c441c0d0103001d5a0301c03507050105100440e00d281207840d84000042d1030560760b075510018142e840010042070900340941c1604001800c8407a9021091194030a600355041e80d2a03100c8045c5555026000b2000c80d03200075280303521100024030042920051500f0090300740a80310002906100d05c03540b1418808610004118003a04e071440b800220840458003009030741c003000e80d0036040e48051400c05000c0d0704000c0f1030f58a942010800c403039024138001c14142243d0b13201c1c82c0000940105944820114841818078003481c1d0100041d81c5103803401801a42c2000c480702021030242441c0d6205134180f140b5074001d00040754041840d40080c0c000c6020440c0da95140441c2d513101490194425002894840010f00c01a92 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 461609541 1250 461608291 461608313
    0x7030c11120a03020f1201150207171005090a0c0305030315030d0f0509040905120c0c010f140703052101172808120112020f0d0201020d080a0f090f0c0f03 68
    0x258540141c40380340c005c2c4076201c00e116150000c2080a84800005035004031485c0000e51185607900369101c0940d03402c0300c003c03013a201c0424001d05400c114203510f1003800b81d030b02440d07000154400b1a22422016102e08003001c01942068940b41c0000080021000180c84079050703081050340241048408040c00a20b10304040840304100100020f03c12060740c0c5981142e00d400e40c02006942c1d100030840c45c41241075002240807c15801801c0060803198061120071010000d540c5583c13044910440403011158048c800c00c074184a000e02003140c12120700600c8160965545083e5501541001c11903c03402d07181070391842c01c60b40702c0001c00045e4443c5080754401002c924402b0500d6440c1c1d480c1c02400d5003e00c202081c010002c02000184501c030007100b07000c21600954000050640c142c09006182c0035094020780540e000b1400c40429500c100b006a0340040901030010700c0d0040c0c114000305480000c002520390f10704601903c4140715003c1401001800c800320007030502031440e580c440c44c0341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 461610791 1250 461609541 461609557
    0x50604080303070828020702100c02030601030305070f0803070f080105030303151309120f1416020d050c150405031b090403140405060a030f180b0604091103030307030c1112 76
    0x4c1040804a0751503034150b0603c2545c44d506000c181400000c0e414002d009400c0b5a000b644640d030034070300840045004615003040b132034016020b0030040c0e0031341d1029603281d0300805c42100e0220104100d0004250a9000707180144159600c00b10301005070b0340018500c00040e08203d20a80040060000c00820b10f904580ca02d00e0a48104a216683d81c0084005040b410b001502602d900c521941c15a6440284019000003d80303450b0300c2401c10580ca038680c0e018031034000103134040c0150b204c00580703003c84010443c548154210703101042d0315030200da0046a140214040ba00c4041000e01040c5014001400340f010744000100f40410507100040d00410040e10280500001c04141400e021200d0211000703424003134a69503803440c031114000d004082d0345d0101c110b11444d0540894190810b41d108003a0380360803940500c0f1586890f410807004280c4030300201c4040008254100140d00c0c1400550310907010754a000404e1003d4010280680c0c0404c0d4608586811400c01a0a65419401590445 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 461612041 1250 461610791 461610797
    0x605060306240f011103030f1801110306010e060910020f0c04090c1710020c21031509150301051815010e0a05071101020c0706021c0503190605060a050901030605060408030307 77
    0x500361240141c1d0300e00c1d17003851045620700001042041018540d80340034024558000c24521300c1500312070860032a0103540d0b012a0455082012500541c441e40b00031445220090845181440d500b0001d448000a0b40c104005600302d0310600c0318801c07040c801c500404c070741035078240a03100e4656242e0f8405421401041c3c03010700d641807211070389601004040b0b040720f6410002c41d550a032400d2415a164080240f6402200d400520701c00c00502440a49000700d101240c900c1082102c0d40402602001c003d200e00804806500400c4040c0e500b401001d02444078280011240e11102c094a4241240040c1000046030000c004010025000328181d6000084400001d40f503280c0e03003000ca400380c5100500000640c00401c0c0142c408070085100c904070350294007115502e8500c41c07540109181d58454202c00701d2814000168102400c4090340502036080000040f44c0d500e4400150442e08601d90318800580003040c581c200b940c2510480c000741c141107030028181854145c0c17103540e034032000b0600b400f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 461613291 1250 461612041 461612059
    0x1061d0402060a0c050601030b190e0d0c03110d08040c0b040e0c0a030b04050f1008070f03020d14031c0f1107030e01020a120201090b06090402010203070816020904060506030624 78
    0x4244c0300b84044c0b600140c2c08020b41e10207594034185804c02004c15180c000607000e0f40005203102d2543e6103c1c030300c1c9030840040942030221206505a50507664404190203000d5400030103440c99105001005048840d0707110418541098204200890641d4008410905d010801440b41d07c00034003078203034000c019402e007665826104500710082c0c40c80b4034034141c01c14104001e200500c9882140319108007014140340a03e260307140700c1d1590b0381206104031ba00c140d480c0c450920140c2800c40c03403122400c0c05105103102480840c028035203590303c1004040805c0018000fa03991210040c09100940c1c80320031010f000301d480c44034114225208031880142480b074035103614100d0303034000d1240005854020303030980d00d01301440e4030180c0a860744c02c504940101d80300b80026624070741200d80c180101d0701030b8000d504182c13455940d4001607010807100100482094490b00041c4c0da64407580d031156101d404003245606110702854030b841000781c42070300e60306903000254003400c000d410005042842280c0540c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 461614541 1250 461613291 461613307
    0xd030f0c050f22060507060e06010311060c070803191e140c0f0105010b0a0e010207150c080412110a05060306090c09060c03030a02120106050c0703060c140c07050301061d040206 78
    0x221140a40d03c0040111510f0100020b8050700580503000c1c00d401500c2c01e0005504400a480d2a07042c00d000080c120360388006001042e0415038041d003250406902204c1c034070b0352202c484618681040c045114902d0844400c0d024090380511050300c0c40803010f440603199581e0100141038040258500140c40c00041843c12848500308501c1e0019001c01c00200407a58480c48841034562055140c000844c00060f20180076504c006030350740440701226944008031403029000c89071901c0c81501903620a009000100702280d0044140300420311600c4004181c12412041c000c00c0714103940024420481802002041d8403240c140c1380e400000c4c207549a40e105441400a0a1809030b4038070040b6902c404000c101c03418035681e00505a4500640002c003181c3c1c0d0300c0d0411561445100d10b03000103600514000c1000070741300d41003c3c0751a0000e09012a00504003000c464907500704101c00b140b1a030000504001c40d050031711440025203042400c1075004800b800603540314030400b804c02030180da00050040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 461615791 1250 461614541 461614567
    0x10f020a111903081c0506030d050f09030f070b03090601060f0203071b0f0f091103061c020f060a030507030e030a090e0406090b0405030705100b1c031106090d030f0c050f 75
    0x40051540070030071356203c40c00d12540c1c1001c807100842001c2010b20700b00c081802450b001a13404982d0045940f030341e281c24000c040c4c2d28215000044010303010b1281e402d4401c00d0b400b041c05508003500c41801119103c2c034000060b186003d0041c0c2c00001484041882107610b0f550200c200c800c0103400c004061a12484000040a1303c601540b080303400b00650600801d118446d50003a9007218940c039018060340c00300445881940c802a41c03060340c051107000c0000d001305001814101d5940c00205007a0610003140701040d0079500031141540001c1d561010007a52503014404c00100d0074820001358100050528003038031242403405410300e680d441200250403c18103401034600c0c184c0c4880002214180b40c94540d56070b0700600c004071440d0040025603000304c05d50f4800d98002000c01402c0c903d603085541001e904c0140d10703d03826420442a06001801e0003401c00c00140107843d000700403d00c0d041030000080c102d8484001c21400ca500b0301d1172800c2070310b900c2002c1c1c801d00c0b01c0d0616441d81d80c000d0b260300700d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 461617041 1250 461615791 461615839
    0x60606130e1e070f03061a071b0320100c02031f15080708060108030a090312021507020c011b0c03081b0709061d1905070e030601090b010f020a11 64
    0x140ba00c0c4050b02004012980240302c00c2040c0f0942d2003c0c0107090303d41d560083c05e2120f14109102c0e9920038090b18000c0341144030309a01c21510100103080894890b151300101031002c4038804c401001c0c1103000c0da8182800c0268102541d07213458140c40c114807607400a42c0f646c6600c18090742c613808002500340c0110250340309100b070240b0394401280d00b1366142039841e22920544140321690084100000d0031441c048101c1d01c01c0e40300d035a03c4e8911079085689100c1c0010603203550004600c5986c40c180d2a0355010b1030181c0c010b11640d00249101380340e50000602001409441000003501032521f5400034640d51451016030307512102d01d03511009100862044a1000c01c50600d10b44030792000068401e41c513a126005070748042e090721000549281409603504d0b01a01d0321102d1900c0c02101c0525504550f024a40004c11450070b00f00c2060100d0010707203440c1003038005009a59a5034031b0340d50745607002850000c02e42d001d400a04980505502c41d4551158005101d034014a5601407501c0d03003a40035094 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 461618291 1250 461617041 461617081
    0x40b0a05120c100801080d05070c09090b010e0618133009090b030a261b01050601020c01050406080403120906050601030501140609010c0606090501080f060606130e 72
    0xc061111107070030280e55255480100c0d980102c81c41c1d80040d1040e4031a040307150507103041400504140a01d00c800701d82960003201c003501d06401010000c122101540500c44c8a1406005915415410b1140c5a5100d003400b5000c02c0c0f044d403640c080d44c0102c3e4ada00000551203a0b9110702c16404a269040803400d0000c450007445110400d88214035201116003003098000541d9540c8146294a4180031411104034004031a8540d128403560800103071507001d20300101010000f401d03203080100d0f1681020b84c0007030171182140302c0301021683c820442441565071114091008100321810040041c019209074050001000075040004080c10b01411b42d5403c081c1180c0c1d420800f40d002e9040200c000e240076660300d80046d00b06800010300a41c500c1e035880c02c0640042c80b540c54103003204015690a40c42900807241142c4401c0c00050249481c4a054002d040840190107544c48190000c4d080c44001801d5900c01e0700c051000c1d0b20b000800400000669620010008050f00c03608071100320200003804c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 461619541 1250 461618291 461618299
    0x309070f060519030b13020c070b030108010609050c0a170702070806040308010314150106030e0a0602130f1a030115021c02010c021006030503091903080c0c150a0806040b0a05 77
    0x40000d07006510000070030014a00500b19900240107200c1201662090300416a010364011b20400e2070540030350040890341866812100f0b129030b40d0302c207650203400990060400765981d071801c005104003402400c0d030025240d9400c034a003a01c03035540602901c10003000c451250400a0005001c40d008200c00720184c4441000c035429407605240c000d25904013400205e0307400110041c0005401c20006d0b000320380b460b90140301c421710380c01c00d07400320014540d82400d00c4441c45107030340c0c21003c90598402404c0309075942c07030b4a2920908119408600041c0c0d54000d115000d8a2841404008032100c140d0f4107441c4c180e1180301800300707120b10403481c041880071a1604440b207001036160640c0c05520400042c14940c09441c00148006070002c02c642840c4000341061700104140c1c001403601c611805008641c59001c45004c549a0710b030a001354202c04603d4500f90f2007400c420a503443d00ca0b18040c080c0c809044000c0c40c103580c1d032800400c260009440640100c3c1c5134072481181e45d444d4920b403006488050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 461620791 1250 461619541 461619569
    0x915031118240603160503091501032603100608040609150902040501050607020109051504080601060905040501170d0c081e030a0b0d0b07050f07060c120b04180305030907 75
    0x12805203807001480c015888045409100c00c070a00700101078903c140c40107042004c0c2280505c0081c1c2e025031000300103014a000c1c001b845421a02d004103113034042d50140380080c4a0916149144200328a1149088849030b014005c001081d116004040260342e4103103007030356260f100c91800c1c0018003040c00707004001328242d00d000b000119035a4450301000d4008c0b1810300440c1da0701c0041c45000c0c810044040d00140d0a00403e2159003040525100800681440c1ca0701e8140da9084d010f042c17003000e0b00100300061180004105524090060501400082c0f100c0080c2c0c2ca1204d841b1940c5800b5485010248144812188140902601500c9851140d400a02c502a02d415030304040d540c02222052a03240c54655041c081c1d0420b0f565401c12a81d10030101050b136100c028050703a094101103030413006c0c42c03030820a41000445a0242c2e8481d002c40d80c03202070b121030f5034030092000e803420200b01502683c603002504c00765481052654858030340505000b070b0b9075241c17510341505200680d008980742e40c071a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 461622041 1250 461620791 461620801
    0x60301030602090f04060b041a0c0a050f0708030306060a0f020c03120c01050c070b042402040f170f0303060d0c0530010903021b0402070b09030d060915031118 70
    0x1d90010203004804070307003d804140d18101000202c5005001c0d4a140131030a01040c44aa4020940142c1034910050005c1c14001400b212903d04010b1340c0040307a60383c10010405181310b10402902c006030591304065402c2d40f401e403000c10501e0043c0b1803914204440f51010807801400ae10000c80c0124000c2c003650341c0c8000380441c0e401c0b10303804000356030815842c0000245507200c2c2802920705460348401198556102d64960b00c0111100e0980666001d003000807040c0250305901c018402046070040502007d450001c0c1d100c0340b0040c0d843d003ea036541091405001040713011003103d61140080307a0000ba10485810f010483ca01d503a007210b034200128140000c540514180c010b4840c18103095441c1d2401c8040c8090790a8904202c402000740c0d010000713451002d81000001580510003a0006003403c1d02c6071100102e1000585803000a07410005000b6044022800b48c0d0380605580f55040c02004141600e010400e409403102801d071070101311000740c00e0742d640440b21481c01643d0110070040c2c188 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 461623291 1250 461622041 461622053
    0x10f180614040b28081e07090209130501080601061b0f0b131403040801060605040b030a02031305100501030b13020306060d020312030106081603060810050a020408010c050c01050f1012030e06030103 87
    0x45005c0c14007103208240300d034170105105006011201c2c00d168050103403245030400c0344000c1e40101021a9101100d42030f240c5845589102c0e142c001c20450300141920351401d10040c00000b41c60314003070701120a034180c0c2c1d8041096a4030b80000d4550100c6c011782503a681d028504500480c60030001c1014541d50f858941e0400004042d00903180101d000b005100c0d40c1c0ca000b42c801c0d02c950b11a80055100070700008401c0304680e40074560107100c0050f85d10768070f01d05541d12400c0c07514000c008415103503100014414131014050a40c2d0000c029030361180700c16030030340000b03580d1000106031034818261a0320f1030045490500900382c0300c03a4040300d00f980301d5071555000360a0080445284081300104280342d840c0a10a0003640100e449034005006c04400c0075860070701810000b00100031050302044000b8a1000912900c522082c40da0b07512500e8482280e8220b082d01c90140600150303005d00c000f8800d20301d5007451001c0c220340c14180c95200c2005c051605031400c5026080e50355101c00080000014041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 461624541 1250 461623291 461623369
    0xc030503040f0c0b210c120712150603020a09060801080a06020c0a0807030c05250902070309050a06030b18041e1505010605370e060909010f180614040b 67
    0x210601036002180d0742d0701b40c06034007402611480c86005e45118007184c2a640240340706003018800900101e031a1500300c0707a056081e1595400400000d038001640180341d54403080140c00b1300340528044060794035210704035654400030000501101c0d030015400001960070011034620701d0b400200540c03503049606010b80f1954036034038192082d0250103001942d04601820032035140c007142050810317030f1381045a464004e400c0300008400340205081d012885a441801440c014140c1e581d0128003e000c071f8042c4600074045404216004107004d0611001406051284a01c031001059849820103a420700482d003800c0d226101d50281d00e00b200200e00c00da4444014664000004600078031600855400d541212036004034034030f1000c1d6804d0605c034403031040400c12080030b0010310403405c2003001e40018031419000e901c07540741410600c2c4200004607046108410341c20b00d007407003040003e280202a80c0d51840c1480038501c107540e2402021082d40c1c569818417200c0d0502c01580005072110303400005022 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 461625791 1250 461624541 461624587
    0x305180d1704062006240301050103080d0b1203121e0c0304021503040209160908030c0705030c0a0605160606080a050105040303180c150504051215070c030503040f0c0b 74
    0x60900744009207a50041140e042113a140103004100c03907921040030b6071284a1a8401424140840c00d080303c1c01d035001d00070039010314014080956114080300b0030104039294200b03040d000e544228240d0545403004001c1d1512100d08841032901d81d92112800048a031a802c1c0d6540c1ca2043c400c1030241c9614001c3c0510701c0303181f080d914171070074140c0a03030891514002101c0003940301a0007400200e02c10000448464031310400e040c06041242c0760b80c0020700717603040f03210300c42c0344c50340914810001403a01304100e400918080d5401d585441c1440030050992281c2c8280d200c0d50040c1d41420800c0001e0380d40403200414088065803c0c0c20b0080ca060380c0681820ba4040d80001d040000070b484000380c1902d002c4130280c2c40800e40c28101e1070718100d80484490000801c0a000c004c0c800001c0031780394204010084025880607111300310f159110007221845c060158001c00c20004060f6000a811400b220381041d0440c858600d80d480b00e1409005d1b020f0341d50410505203001080d01c0044a05e40b043c0c40c0d0f150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 461627041 1250 461625791 461625797
    0x80c010e0d1214010b0901120b060412020a050103020a080112020d0204050f06010e0609030d08130f080a02060a022a0a06020a031a030c030c06031509010609030515040305180d170406 80
    0x503c800d00c01d11034524203001d0014800c030204101059580164003046000310440c0006c58032169031000601c0580280c1d001c02d01c490500380c9076a00b14502031018038050007003420b04604213010210020300740d07441409584010814a03450f0360070341da200d07070310355844c65401482402140b0341944100040c01007602c9050204004400d4032100327203040010b42d5820000607009141080e2041412502010f0103020361016401007003503000401d40e0f50881800c16406843c0e42950b80f8111030b402468290000c214140192050224150b80c0842c2c0d050010f0111181603040244012420b100d81002c4040e41c00602a1f071001594021098164200c25181603203e0304084064003a901417548503654880c40399410380240a100f1000d103040006903400600c01a0340c1030b0740c602a4008034070340c00340c00c0e040a0045050b81008001b0800d0403c4039500311140c0c2000c04034141042d80c1c015102d0301400034209884141e00a448915441c0c0400c445000c0b81c01c80300ca400180081c1d01f141e2500c0d40305008103000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 461628291 1250 461627041 461627051
    0x71d04020301090f15060f0c0c030506090307050d030605030a030807210e0d02071203030203220308101e0509071101090609110108190b040b210c120a080c010e0d12 72
    0x5048031440040c401c40303284c1d445003042002d1400d8102d890080f070b013000715124802c02788040046a0304000a6200360551402035a66000504000e85400288268002003608068040c01a92000300b001180e0300c0e810305010805031580d143c00d03205d005110006410003070181e445100454401c7d0004402213420b40140c2d421a140b8090132600c3e080140a600d18003c0d40550407000203209034003e660201d042c4c5010207106181c0e410344401a02480016030001d000c81c0c080c8903880f080d4108110081120341d140d641c24609000b042510351505100e418030078100b02000a24041c021102280110380c4000200421040c0d4070303004004044030b107003d0b501f07580c4100200107954010040c040c040e001c4200203265542d8400a1031010b0071200c8402c5400c9501c1d02d003002995103c40250850200500f00c005908105500700c00b86001c204412240c031801520107604440c1602280c5541c1c3e00e0340121556603201c0c040c200c40760142960350242d556511401c4c0440c8482d56024112440d114000c20040c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 461629541 1250 461628291 461628311
    0x2010515120312070306080703111302030103051c030608070e100b040f270c08061e150c0708160303110a080a050304020f090c1c050c03071d04020301090f 68
    0x701c000501406248a500411040128030039500f103560780110f491401181c2d113a1100981418154603500854519480644102461600003180064011507110860031503142d0f0300d4083c0e80b94030400781c01c1d108515489400307541910a03013040000d03080c240112064240d9030000c00c0c3c0000c100b10341c4810300500411000c00c0483c41e000844089440b0680c00005040c1005080c04840b0f0f00f094100040b010902120b580c4034580380500300d1086201d07200c1c0303019480c0903014440ea0b80e00d50031507009400104c240360001c954a040f0f400c001c0b01c484007005901c950410050b41e01e807480e5900510440e03ca801a030740d400082c0003407000c094a109554100c50f00101c03a00c029a200c1c94041e008204400c2400260405807058000d903902030300061444440c0b26144c000714060301b0041d100d90003a40382c002506c40c8016510114001807184d034a000300a1071071300c00c1480401e80005042641007100205440d64859440182c1c2040c00b40010030443d980d503942c480c070700700800c0100d130135269150400c80682 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 461630791 1250 461629541 461629549
    0x3090c041406090711280302010f0c051b010603050102160c12080702041e090503090f0d0c03170708030c07020a050f3a080703080f10050d0204020d05040302010515 72
    0x50140340c0240c01c03d031a0f41c43d80358042c0d03031018001c441d00f0b05034883c14091105c01400d0382c4500b81d001c010703030f0348000d0020250700340242500c1001d11a101900d04000407903c095070300000f1502c180c0500c082008a051003c035409000d051642c0c0040e010350300110740b03115681e580840c1c80c81900e2007009040900360340cad801520144904003c000c0d010030b6050040c0c902500300307501b003451081c01c41c506011800b03c0080c101002c1351050402510a60320109400035036003801da144200c2c050701101c1e918074102643d42c030480d05104c203000040080c1d05600c2150b8101d0030740d00684010540c4071072101d03242d142c01e44522000d40c1210100b03030301c1400ca410340000c0906081c40d188903080d1019007112200d40190140b0340d00d02a601d15146000b01c000d400d5034400e0306480d424840b60a04c5050050303030300d455a081c024003a204c050021400031200000344610301e9041e45c4180200c0f1000e0724800c4180d615070000038028000c0c601c503075007000d046c44100410194103600451260b41d4410000382401d009070140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 461632041 1250 461630791 461630831
    0x230c011d06060913050a0204090606031b03050f010e0a14010b130e0105010b070f020f03190f050105011e0e0603030909090a150203130b0c0f040b0d0612020a030201051e03090c04 78
    0x350a1b44c0124140c4409030034144c00c2044202d00401c40854015070f02e03600c0804242a21720381925107545a8400c4c41004020300c0384a283c452a540240034034a54101000d0300d42c50300400c024410b5885034860280e0700029009004030940c01400c1d1074084880c03a8069000d0310910481c0c0e07070103500e4030f000030810020000583c4d8406802c4074403040c0015403a801e10480c200400e43e059407502c5100490f504000410721449004c17031040c5103032540c000d054075100c0d00303448040c2c108103000b81d80c00842207103900400d101d207400ca0300d4000380c90485031209400700341144101c140c000e40000c1004100f1070507800000d108a5101d21032641d81c0040700820340341800320b020544000c0c074415031001d404030125440c0d40f00700d030301700030445a0075140801c20aa041130541c8a40e2120501d1400820240010071180c17158200400020001441e000c1d016400964188280d00000341449030119002150050a0310035a00142e4410309542d80c03410301e14519661110200c0740a44214180105c0904030050340040f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 461633291 1250 461632041 461632043
    0xb0c0f0613021905090a02070b1029161101080901050606030114130e01050906010807030203060a050a0915150603110912150f0f0106230c011d06060913 67
    0x842001c1d07001e500b0081c420450345110025a840b0010200c0e15540e4925028081c5c14030340740041c5d4801240c40d1590040c03a0003820070440d011444c07001c00445c0903910303101d60580141087c0303100754080c4040c06c9006000e80c05208a050200f41c0d030010800046001c1c560704040240c03a204c6141c1e4601e180c103400e941080303e000d82c020100740010489100d21400e440b0180300d00070712900d642c0001d403020000302c23540c403180f10416a450f5014041d40c00d1062150310f02401207200900300060031078000c207603684c10190074a40d903103036a60001000e0851507030005855035801101801100703d00c0e44148050702c200301d0a28696246204006002c6000348260821801c4100c2c5890030462064100003458804030020b080324000d0001c1c07540c0032000a80c07428814503041c0030202c02400c001c5110450694160407180034001e510410104102000070940550344c00c81c84803582e2401c104a100c0d002d000d60305403080d440c8014014102040001081e83c5100d05c078296041e0082e0703981c20021004503260908 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 461634541 1250 461633291 461633311
    0x3061f211e0f200304020a080a030c0b1308070311061003021302090411070c030501050c1204143310030c2d030302030c010e162903010b0c0f06 63
    0x101039681807482e001485500544007000440c4030b40c10480075000c0d0484809a07110200c00003c001c1103182603080480909502802482d000740311b5500030f440500b000e0400b03420780f00d01000103100c503040381c914510b0b4164000344050300c480302481c01900d40803400e0380d401a1801140300045a104030090814103c0385c001300554403082c2c04100ca68000c0d80886202c541194490101008920500004120302441180e0391b012040c51414003d0031502c01411160566204010021150022a0500d60030a402c07801001071081030415451411551039402e40710702c10303012061030311044240b10030604003a10b007a01781c1c0741d5a1040b0005031206403034040204040c4004c0c1d000c2c008240075203c034010008050b90310070f414001d002101d05200305144d2045005900004600f00112020f0041c182241079040007010300d0007407821400742d481c80c54000c9802c29020300380d02c1040c03246140003403507407030001c18207040d62540c4407038000307401d54840305100c612072081556010107040001209032044002078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 461635791 1250 461634541 461634581
    0x190608030d0c14072904051005090601060c080a0e0909010608120403080a110307081c0b090402061b030904240f0f0b07441201030803061f21 62
    0x1758940241640d5030280b8400301520424001031481980c000900460203407004004d11034840c0410000da60004083c18403580022004114058000c5074844226501c21111a100c102000c0100c500d0f49041840d0f035880b002c0b0300240306810340c1c194481410b560791901510106012610030b00c11034030403444001d0080e41c040142c0c00b01e1a10440e04907444002c000162450090585c580b819240c110b046440070909400c01d803040e203040b031441403502100d01950110240d14180d00017440038050305880505070404005050101c070000e00c100c035030803000180b040161180c9080c40720180d45036061030400d401c09160000c1074103150410300000f103400138250540020304220740c25005800c4140121440c000881c003844005903030240440b04403604100702e00381c0e201c02e0341c80981d1212007074000c0c0b00b41034010440002c55200c1110340c241940c0c1c1140e401c41c0c0c0d82c2c540601140200c12000d40300c0f281c22510304050885143d1020b41121200580e000d4100c01030914040b850865407002000c1c0d500c09406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 461637041 1250 461635791 461635793
    0x40e0c06120601021501061e03050411040c18090902030c0d08181518100c0209010e04020f03070303020303150108131218060c060606050702060f03190608030d0c1407 73
    0xc0701035100406206885120003041c0390300c1e0350300c0000e800140c04640d0341c411328621390f4840406401002818a428052800c01d078540d4900c0d55821f04503d4002e9440b084806038290103085201c0f0705a01c20b003014522140e88198200003422140c0040744640903008440c0c102d880c02ca440e00340400d0300090101d2034094a64441d00c800700d001c091403900b09107500b0366010a00d09003c06008400030442035001c604500108000d00001d8040d4100c1c18000d08501c0c0300d002d80c444403222415142d031101503003004d442d540001005002c2d001e81803a41407141e01008010180d000c4081c5002d050811519141c140c448401035446070822184141003d8109420070f000c41c201801161810390b19040414130b0182440805a030445d04d90010408100110f810000f00711051045000600161a11034201021030b4002030041c07117064502c12010801001090441d4a04881d0210007085030b1001c00119640700c00940d2079422108800300e050f854080380c030030aa0300070014001007040c40d0000c030303141000e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 461638291 1250 461637041 461637067
    0x230f0d0c0e0a0603200405071e120b0301020708040603060f150518060c0f0c060301151112071217040b01051c050d020601181b0302070809130209040e0c06 68
    0x8180402c0300c2e840707010020100b041010881d2420845400b280d414110301d109010035120f000d4090820418810058085459000703003a01c040d0040d403a0500fa07409800861602800c2006c0d40943d03d035100240c0310701000282c00c020800c96030f40e03440034405160b6401e0100340d003102503ca08400390500302c1c03034042480d100740000c08140300184d20511706a8140c1020901303c2e0852661008c0540c00303624001c0f001e0b2020084030b021640e0480e9190f00d503604090f5030342d0032130243c3e002d248184106900720a010b01010300c02003016090ba1010140c540b030540c20500d441903202003032040400c08070b03582980c04a407003043c65442181c0045c40740d1026460903081c03082c2d003004401c201000340d1310441b21710001041803100704110081640100360f95410b01140f805640020030103840e03c0c0340740c580e40307140f9030071604103222011646041c0187c0f2020b850038045403a00c1200b00003540450f5022114805503015405006224030580c0c003004848140d030706043e56441c00d40103559016000b07100c41203462075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 461639541 1250 461638291 461638319
    0x10060c0501090f0b0604270b060102030f030a0501060809011a21060a0f0c0207080d08040c0b12010f0f0806010506030603070e0c0a1e050a0c03020304230f0d0c 70
    0x48a10000224140c082c2c07a0003c0340340038008215107440450090142501e00b50003201c0d4601c8010201405001c01000924802d20f004400202501d0303188000403107903070003801629400c00120340c03007590700c0c1ba04202540041100340101000b1a101c40302059605105100308880d41041914140b400070b24102040f004802003030312001110f0b40503c980c0a8074100f44500341c0070300e8802d2004906207280c03811550079281840c034400e0031580040c0d010402ca800001b008034120410742016007440d2201c0c140310407252000d07040a003803500002104040d490000000700d0480e80d40703003008241c85440711064240364540740700f02c1296a010500502c0549803050084ae002900202107584032540c038041094803d004a40352082c0100110300280d6090300720842d0310024584148080b00352a446074048e2407402010700035020000c680d007280e000c15008004940107003200300f0b41902c9c50900b181a061082c50f02104407401041407090f440324909014441c03d00f01d980c01507001840500381804002852 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 461640791 1250 461639541 461639543
    0xb03070e040b0607081207030b090106030f0207230d11030909130203010c120b0a030c0306020304061515090e0105103509060609090309041517012310060c 68
    0x603a803602c1078080740d075411004203440c6105507801601c0301e1480b80071075020f4000800680c24181040c01035200355845c540940d05603440c6040028052185d03844240c000c1c022110300422402c070b11000f9080c805103543e1800c1074081d80130201c40042d0b40305201100c80f03c4102c00902c520354003d20124130300d0f14041e802c141e44000502039403681c018250700000d0075240c4805102021440d0200310f251b652010380240400317202c0c1641d21000c1d07a495030b40c629800a07014480581120f502001050420a803500640e52010000c907840d031300d01d0349680400400206100c00b00700401c5140800140d11100201d82034100c1310001c0000010504000090f20f80643e80c500d414a41010352117990201c0300c0301c03030301509940c450100b503080138500020201d24040c000382406109001c1c090400a98010000403641006025a0301140050f484000701d481c12446420422580b000300ca40b28030078290560101c014024140001d0250600d40c00381c2c1c900301c010650b614281883e11000038040d481c003e8403220512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 461642041 1250 461640791 461640799
    0x10228030e0603010303090602120c03030a0203070c0507090e0c0d021c08040b0406021006170703230604050c01260103060203040309240908030a0e0405040c0302030607020105040201020607090b03070e 88
    0x1d4540900080660344241c1049001c07400010003800002ea04114200c0305650347c0110518144d11402c0c015a00e0200404100840360004005200144140131020b03c89a0040484070556160b40864002e00200e1200c4040351003100703c2011a481c044212a0020750068218503000b0340c511414620503000203030130340b000745c400c001c005082050000200020100381d07001c0c0105000f50041c400a0ba00191311402030b40c1000380c40001340760000b1030020112031784540c946220103259040800035203050f20a00000c0c1c0100c4041200b440004242c40307002d010241e0f50080541c80d00205002c0700700701002d910b203480520a0040c40000e9181d401560040d000e030608241c0c9640d280d20483d8441c0b022040035044204a00404c5083c1e500a090800a002c00c003001d1802e003109110001c0c0144001300c2824404d40c0c8400201c1c0030300111107207036005150081c00307a40140c9490760b0042e000e4101558124014890b800c00130b03041074421350152051b41c021071542c03072442e00d51540484e00c450003012860f0740 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 461643291 1250 461642041 461642057
    0xa020f120a0915050103020312040311040c030e12030f090f0604031d04090f12030b0f130b0603070507050601060801060507020f042403060509010e0c0d05030f040b09040b01022803 79
    0x202e00f403c2c0e14a41c0050090002003141e42c15841450f0401d0b0381003500701504081403205100151000708400214801910005211942001d045014203641441d21819004c0e0691131070b0030740020001507106415138110000a0344400450950b0b440135941c2a4104da0020008640003038403c11954412a010030800002c210f03190700014100e40300170400300c6440d0700840141c81042190601030700c81400030b09007084504000c50105241185044400d845884d10142c038455a1000d60300c00c0100e944040c20050300c03403601c00e0016089030300012040d6003502c140e000000b4070300c0c0302c0c11030070781030b20900e0f41c5050130b03c40f055091080c0f030b001007a51590301540750827008954610184010ba804403e03d030f40c11590701d2441c1810720468401408031071559040c41100800c1500c0003888504130074043c5c0c1e11411500b00317800d00c5070840c0610030380500c01d07500c00103000801441c50000341448032400c1b00d00300000610301e001aaa16840c8070003003200e0a141c4408608030411500b0b400d5405402070a0600f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 461644541 1250 461643291 461643293
    0x30a02190b06011805130606020c0103050f060d0221060712020708070303050c0c0f0d0e010305060a1502030d1107020406060c0201081815181c09031101030902030a050105040b0a020f120a09 83
    0x1004211591104c0c46d0580d40e003010804540d040106041c0040282010002030410340c0c82c3c2884110014841400b440c1000305003403c6480b1100c90200c043e0202003044442480101c1c1c1e903446042c01c1d075001000a004d04000d148018680c401c40d800e487e8005d21071460b00e15556010b230003415004020a049840600080e1900c6c6007e1180307000d00305041000e44070018820b00d000e00100c2580381c04030704040c9001c0c200700103501c178080302c80183c8010102c600d1102214040032865442540784881e0503505000203d501d031044d8801410707010b4400c84043c0101034a4400403140c0322004800030307000507140004648004964202c080038500d2840c1a40c06a0300a10320f400e811003805c1c1e8092021a05864109902c104180a402120260306461030480c0c01d421000900d502000d00018205118565a0303000b207038002e61200450681c041d09860520144c1d040c514020203046400b03840d80d000303003400600180b807079100302c0741e1040404c03034454103005240400e140e511600501da402015a1000400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 461645791 1250 461644541 461644549
    0x6170c0313020d0b070c15060501090b0f0c15070f03050903092112090406080d050d0203071808010504110f0a060309080d0e0a050c19121b08030a02190b06011805 71
    0x81c1300e4521038031480d180c00750714640b407d0381d070705d501d070303030000403c0c50110180000d80c2d004480e1001c03101c081c804681c454803c5162000d0520803412a00018860490311f01c4504000f01c4003688580c0341c54440c1d08210105800540503140c04440e03441c4540c1042002520a203069483c0c0071441c154081510710b062412111585440482403c00d00800c20204862565280a01982c3d000d0008000604900b014401014100d802034a001e407422540200010f10000c5c85280c800856203003600c00072255540d41c22885000b032809079419202000c00c511121803a090001d69041546005004040480e140c040220010061100100c40c490000c208400f0201034a0142d1082034048002901d20303192140780c51031601d521041a80c1c0100910f030210b20900820301d034503500f00c0350514228280d04c00149020f0a51a12004e040007520480c607101050400000000e84440c9000d5021660b045200c0c0e400780211180802c0014180c41020340041c00c07551080d1010540e20303140300c3d0340c0206261140001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 461647041 1250 461645791 461645813
    0x522092f0a082a0406030f0b060c06060d06020d09060504020111120901030c0210051006020723040b0102010e06041b0b040b18270a0c0c0c27021306170c0313020d 71
    0x21707000094a40340c28000c0d00c1d0040c4140d210140d0101c0726a86888400b00e0180d440b540300420851045c1c0416484030280a80c40d01107540c1144c880c4410001c403051440e00307030028501a54140e0004800c4410551552400560310041d10b58584445003400009001100a040301c2c40d41c000850040008129451529000d0903002d03c1141b858103078a14144413000f480c052075075000c281c1d180000102c4940170032180c0c0038003800b50700503100032a501d00c00d000184c0c0942072200e450b0902d44100b60820090140703800c04452a0805500c000040381d544800070304450149002c0c0c04601801001496920b0444c1c002419400341c029014242c03400a082e241503080380866005064209010208903512140d48100b000301501410700703070742d09600341c0c540039403000c0103000f460100f40c09480d2040d5040d0302d640da048042c03603940d40150341d201400c1c06100d040300018892000403503501c9000080245006507428411000182d0607415a503410054108200d02600f00340e0300304404003000c0b070114011000f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 461648291 1250 461647041 461647049
    0x60c0507060e0d1e050412081c0b0f04090203190609230705040e0d12150305010929130c0e01030311100204060522092f0a082a04 57
    0x142c501c074030210f07a014084081800540743c0380410b00d6403c0c2a8990420151010f5a4001c014042d40b0010361510380702500c01d0115240343d0110001c40b16140f40c400350028807007224252001d103207101c2a80140300a4980c0e10000a5154001020408480d01c9124000413002c1c09804041104a015111101c1d0711aa180801c20102546912456490b404110802c0100b0058408003e40c0700283c40d56034841c40100c6040042118540c01b00c800f4005580040d4484005010848100340e0703a4508280281034102c0100c0e02e50b034010102d2081d00c13051000c8092045014240130300e4640d204c103100d00091000d50030071074407000c44540c00b01d2120600110300d13001c0e5100f500c504022142403c6114075200020480110f254010001481116801404d80ba960815031201850039006da05648154400a4100003055490800c611803441d41c00200c03d582c884c026170400e0038520f22807a40c02214450390450b0408a903800002c64100703007007045122640003031017410070150001c0420b001a80d600c9a40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 461649541 1250 461648291 461648293
    0x40b04060506071a0112020d1b0503070b04030b0c03011d04080f0d060303020c1f140405041113060801050a0b0307021903020705010e030f0c090c07050a0609150c080103060c0507060e 80
    0x1da10203c0850f01c04d02140034115001d000703054650030303038000b406641860500030000d40d1a1644082c0c60400c601019000d08802416101016110082d0100503001031109039210400d01e00441d91801484046138140c8004280305110035110749007000c01021b0180088800060401110342d43e104000090400e00e0034038007000c0f84c0740d8030b1420000c0c5401001c00c5d11a10840784180e08a4181d41808082c03120380c1076a050039040b1080c1224121114040da030b0166800ca4182050084421844001000741080182c1d007640240d4032603d00300c0b800304c0e090007130700d07089804540103000800621000e581d004030b482c0b040b190440f10080c1401c001d9418800c0480141e44540804c0c8002e41e00014010345140060707000b0010083d461420590f5034a02681d002e002d03462a2010542c030050100c01c480100740c0003800c45000d50a60300e0180010968a44180c505450760524404611aa070107090590070302a49c0b22856a425a12840010410308110b0802d00a0800410000030024012600360040c004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 461650791 1250 461649541 461649563
    0x4060e0a1d0a140f070e031509030c0601060c051b0a030816062d0504050708120c1207030e0427060203010e090109030c0807030c0b01121502090a0302040b0406050607 73
    0x65002d82c290b841c100c2c08442e40c08283c0c410009203040d8861325690064551429400b5400448007181c104401f001104034401401000c0101c3d0880010003031000c2e0780c42004580e500c0e80e13200d1040b075071180c11450091054001c2c0d52800f032030100ca850380026644000b030503c40301c3d83e80d0390707928142a03210b2003500302c568a81905020034003103180708100d070400c8808569030150380798001c0842e81a06240810b0744541d5504041014840200060409444141e085481c0c12225119111880d04410b961200c20311030f05100302070304000c032000d42c0c035074580c1a2518614043c00c10200409401100c0e01c12003201340d2491000403e80c12460490081c1c1c0c025900140d882d4100100400c540700010076210950303040c480f16200003540075000300d01039900510110f8496100f450125169881c2030800f500d403880910000c0344050710748880000c0345204442650260032040f072504160700801c8200365001c28070100400150078103805c0088090b1005100081c00c42d1924000707609504143d60659050242e5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 461652041 1250 461650791 461650801
    0x50712081315030b03190213020f0a05030a0c170c18040c09090f02030108070612020d05040309050906040603110402090406181d060411131d250b04060e0a1d 69
    0x507229026130450b0a5000d410003080e90580c01007040350044009010b100303880c0003e44580342d19416940d07028000e80d503d540c3d81c04510401005a00141e030f0200b0503c0c900480140c2c818020740142c0c0c80e000e04020403c0b481c0c0c0d40c50300c80510540003030170b80c103280c00d1120320030031065a224400d00a440007181c441c0003699003001210021980030007132148501c0c1c070400043c0503076600001c1210495005142180c0014000c0848a001c2e01504c910134030003034203040900081541000d42e0f902a1031059a03001010340c2e418081000f40d482921010304501031400f44510a4201a0002c1500c20b001400101c6c421381c5c2d40090340c551810784680c50303810b255184081c80e64441c2c2803003d5025405a880200300d0313400c150700c071901c0f00a500300d4400e12801401f40b040070004500d40000d4200c0389100608444032001402d01911120390f40c90517039002c0001290b505d40403d5a840310005c0e1060002000d040030300b0a10300795000c182400003184e01032455a400244003104141c0010740c41880c68081c070f454200313 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 461653291 1250 461652041 461652047
    0x816050a26180604110f0102031c090303050a090b070e0d0f15061a0d0c030b03030c0a050c01111f1e0906060927080f0a08060906010804050712081315 66
    0x8032840340b035050742050061202098111a08200d41c03202142c89100703001c4a500141e14601c0f0703074000c6207411480041807041060203a800403492038002d803010f0000340c0d0f410310000101c4058800042240f9118000b10704401c3c440d00340b1514030324010b03081c0f0031091201c0e101d0b1400c05000d42400c03074550540b001c000140c2000c600408005010121202007103c05c482c00c55050340c00b42e09132000c1001e544900ca20812442904004c62515000d415607582c2d0541e154030070345075440341e9801d94041c13050f54000728181d4807410610007481c0c0088040d02c41d140c8100c01419407150082400d841c1d9545400c807140142c05005001c00440307201d00d41c001800341051800200703482c1c05a0140700c0701890030ba910032031241c01c3c662091000000e064818030b02c8880c0c0c600030702140104600601c29134004928011030a4101191a01441d4122004500c0e6a2954011034040b041190001c0880d04208001c200900c021001d900c0d01030302c1142c00904004900140100c0c5008560240001000c800101c3d807020390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 461654541 1250 461653291 461653321
    0x90b0c0c18070c03050a03090c1401021e0a0212010b060a18050402030103240905010c09050f12070b0304030c1a0109050f0702030f07030302040506030109050f01060816050a26 77
    0x248034554100325140201c805011030f00c60b01030143c284078000500380035080c070a500485081e94081e603203003403c0d84c4401d08541c060343c1d10840103016119150600e80452902c05007140404003c130004c01680c02d00754284000084c0d0050400e82039900c45810816130754900c0080c1c14030200c43c5d50341e5840000110303d02403249a1a601071802140304100510224005141070610f40e80500581c0948103000d103410740013008919006802c0c0d510749110050380e03035807241c240e108a030800c860f020004405942042803000380d1001c0032802c0e61007180704006000204020f0b607401070003800c0510050340c0d40e454520650304002c2203c40055810790041c400a09284281c0e0780211006e9403694013403410704c40107550307841aa8224440d500010818804051280e01100e01504000c0c007901d4403542d4841103000601416124005a541e001c40045044d138840d0718201d1060070160141c9080342250b41c4241d54540c0082003e00c108542d480c00030aa009110300e1224080100313a02080052405400065400c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 461655791 1250 461654541 461654569
    0x70914070f0f020c0d020d120f11011812050d0e1c08070212220e1b031506031302061c06080c01050306040e01060f0f080d08011206050403090b0c0c 65
    0x80d1000704184410381c00030302c5944c4464240d407000140302d400d00001e8100044844001e20072010041d000707945503030190140c00441038a40f6505034841d220001e031401e0b5107402000305500821b410143c0082501c0600d001c1100c9580e007000f0f498000300041440944001a61140e03281d4400c03560780c1d1894400c0e41c0650048070b407d00c1c100c0050b05100400030340f1a0f00c000140e9011000115001207003128071780503030b803080344000809014140d6400340110b891904031b0f004d280820000c0c20300290001d141c412030313108101c00000803d2001001c0c0801805030006001562071048041d61040141c41c1c4500408000041080b440100d401c00807001d41554920381181100303400c00c110b15205a41c00c0000c0d00d410000445010079242c00307101c1c6042c010b20715036210b040e03065003241d00014103802810004041d10100d030180e40242c280d0140c2a112040c080c800c220701d80c040702c00144045001c0b40c0c0080c0c1c01c40d22900d8007102d034503581c0b040d11095800401307004886070030040001c2110700d0074407090300004d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 461657041 1250 461655791 461655797
    0x3010e01060c0809120c03071e0504090b1305070e040501090c080f07090e0a0b0c0d0507030c0516051c090f05090c071b0302090f070305100302061605070914070f 71
    0x2d02d841d60302e450f12030041000c484d014281400700441c1e040340c203221146000f440030301203030800d41da985401c0784e82c80d01400020f4240400103001050505041c02510302c19070b000b0070103a0140d01ea0300720902c80d0454001c01074406004070340020403020700b14910b01e40140d0285001051062841c02c00040581241d4000f0b0082d92041803103102c401004540c1e942113405a68000a486402c0c00020341012900344008108240c40010082e1595042015108851764654208400c2e41c03139a5080d000ca0708012303e20800700c0d106101100582d8081101f4800007486001a41e580e4014141c1b041d1140c55421054008035001072f00034080030003200c00e01e90040400b2034180c1864140044112110b100c1d0180160070000c80710200c13a54022090341c0d000045501609908240c03504030401c0301030b0403080e15000002814400440d01071b088240100c0140c0707400a2425150082d41151744030403000440f002c5a00e406951800198419944075295101c0310741d4010004034079004030020004e050005800c424 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 461658291 1250 461657041 461657057
    0x111b10020c03100902010c0c0603021210060e0904051c080612120318070312020a0308090c1f030b030f0705041b050d0903140c070504050709060c0605060d1703010e0106 74
    0x450b6400040030381e4a030000c0580040d00c1c040d1400100c03107849401c07002905d0102c0410001400781d5151340100381620075202d1680711500da4180f080b00d0300030305110300400102c50180001180c94450301d241c0c3c015205034101c40b0010015000d90413421480c1801d500030034103140c10080700d414010010801e002809020b09501f0815880d4076915000280040071207114160120012040030800b44000e560009045110f50391a260000c0d42c8404044084000405480c045584000d0001e0540074900c0024041c5517440414840f00901c841000204020543c403000d0b0f03484907440521440c030302c82054001a148480c1010f00b800180e0fa6091440c0d505c02c0b903a14802280141e1101c00d9490090781c100010030b0101c0c2c1402c00712102001007100c0c00100100146040c0d9108000501c481260000d076814001a0341c0e840b01641c10100d00c2c8104d0b40400c0c4901c0010001600561100d0f078403110043c250741c4032802540320f090300516401c141c0c2c110b140001005216001c4ca04074403600605070347ca44a00c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 461659541 1250 461658291 461658313
    0x307052808090106031a0705090d050604020a05060703200322052b1b030c1d010602340812181f030504020a0302041a0112020702030c0907111b1002 65
    0x141d1b20132400700941c41e621000c081510a4450303003c0b03c0c91200010304680740d0113041d00385640c4400050324100c0c440c0c0c0001034006000d04184094071201c580644940c0c80c180f21508207160749030459103280c6042d02040001004481c118140c1c1c800c2d880c03d041c8020300a90400d0284007003060110b0b4038058072840d860244600c0c1e04180381020901e54020100c40d20402c80d112940e911451b10781008100c1d17204000040780300000040501e4201405803e8413480b0791303981100766240c01d12902d0f0464200706038000c141915011144100071b03443c07155014040d0300c0e901c0200a050001c48a007181c52098009140ca0904103011580044024104c44c0c180900034106040c61807140c040b40e08206041c1c42e000000c0035580d50020f914000c41d0054010f1081d04081035050709001d00917905031f404034420300d1511400350100d2007900c126540c003030024805800d2207800c0044003240203004400304508401400384a48081c44180006001c4886146501014104100301c00020030182d42c2150b00c5008014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 461660791 1250 461659541 461659553
    0x20c0a1211271e070f050c06150f0a0305072303010507050c0d0201110316030e0124090204030b011e031209090e0309130218180402030618060c030705280809010603 72
    0x4d4200c6820308103200c032032840e04819250f501403103a14182c54004c00c4104281000802401031200314219a4107000010610070000000d0440c040030748150300144042c06468901c1940038038a444243c40041005227403030001e400d45104540c0c002c00200c1c00314408400e681c00704115403d800351400280881c400c1d54920100a00005200000d2030b526007502010303041c000c2c0c0c01080542e1580c0001e00001455102c50f06d050402d50305c14562a8a0b40d600000d1450042d100340c605890380941e1140c460b9113001c0f41e007c42d4050010b20040a811070303407000400104d0b0600b400100e02c0d966152814440d01c0c0c00c10300421640d40c64421215070f041000189040c1c0d50710350301e000040301803803c01a1038242203190320070090300e402c070f040c4d400000308110041c0214850f481103129906c02c07400ca50030f40e6580504017501c035044911411032a4810004281840e11031006540d0101603854102c3c10400c41d0f40e07410000d41c00340d113804084000c5030100f41c564a6808a01d095120000c1002880032500d140ea804c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 461662041 1250 461660791 461660851
    0xf0512060406020f160c0303091d0414030f070c140406030f0f051905100e010b01020307030e010e04060e04061a1305130203011401060e01020c0a121127 67
    0x303102c40d50018000b0b03507040c8810140c0701260f102c04912001e4074054509040844c8aa000581c0480c044400004902c650b02050302080703210700c16000d05513210355480210900c06401c01c241e89000604c102c200000d04a000382ca8a03900850008240d40d00e000310514651030085481405a41401c0b030030302c04515000c01700c180507607126010440041440c00c00c142403a012864000c40f00040441003020302400080b28052004800b4081100c501580b01c407500b02e501d10010580503030401c0c0709450111340a50314040b8940b00604281c04e11030491070000301110032540240304d00b03046031414881805a14840c00c1c0d140c4450006d2014070841d2640050783c400a1051010640398603840002d150f4904209022142c0e135000e0001d0103540300c0c1c81320b40010a1024001c05001880744401c5032159880003602807402e01004d4006031070181400a040401184050213031036000c02d10f0b800300042e844160028104c502c5440c0701d01180e806491444d400328401803c04c104a807660702c01150342800c03507a04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 461663291 1250 461662041 461662043
    0x1020d0903110411191d03250f0303030204030308150a530c0108010608070c0512040501180305070509060118062f100203130f06060f05120604 63
    0xb00004011041000601815641c40c07050079070500803840b8010240442c1c3c50010441d6076407030f610300b251001d148030114605e541100680c50f6010740e0466210040890303a0b031403000c0d09a160b20654585420f54480828000d600441c0080e600140c20410f0561040c002034003d624400890030700d20080000401c0b111490080d41c449000100300310744524030000240c42840075186d194102d4031003409100380c031017980421500d4801440d10407054240008a00d5010300c90050f1500038069082c144200d8800d60024810014083c2821440703020604c100040001c2d1445081619a55810701000401060701145450107100c1507441c10320001c3c0780411108103880080c1c03034038103055503800c0041704e1078070080f83d040400744180311003c510385a02a030860390341000c00c00c2c1e0351220070b44688040301c1c2d00740002c1d1f0003074107810158100010416603001503030041040c06540c2e1404d099911382c01d070b2140d44410100c42a131b5880c0000c0142440c00d10813040281310880380002d03c0c0c06c43d503035041c0e154000104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 461664541 1250 461663291 461663303
    0x80d120c020c060d020d06170607080c03040605070c05030d05070e0102030c07030611070b0a02040305060f13021e03030f090301050601021c03090f0b090a0506181e0a0b0708100501020d0903 83
    0xc0361400d40c411076041d0350308855181403e0107608d681b41011b8101c02444005420070340903001c00624514040d91849000b0742401031203502e140e8958076018010900602640100600b1a0381700e0b010400410140c10801c1c07201c800015035040c0003001800034030301c00100030306540081c0b20040c5c0d40d2802142e41811079030021800705400c40e64a185030f0091080042c02046a0120014051050025809070041c1c0e4400c1007240c0154440c03140c3c101043c48120b81d030740240849000c01170014140480c0d0308450114040902d042d50728200f00080c00d41d000450070f0403080401050003580c41c40c003400344030b4002d2020300192101075021031144042c07103105483c210905494410386420030111050f07003280b030f0f604905406424205800126100d0010520030b86c0c00b07210710004280314000c6105013100c0001c141000708108036465141822a0061002c070000d140560400d02d8081101c2c0a080c5208040540d542d290b9880c1200c211080700c1e4840c0c004a04650107010a00799154100d4044010740b80c0003a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 461665791 1250 461664541 461664547
    0x603050405071a040602010f0209150d1e0b03150402060406050a050705100905010f0515010c05010908280c080306010c140a0303020a030e030f030609040c030c080d120c020c06 77
    0x10070700074508042075101000383c14802c800c0300c106181040c05841078a01c103a000340031a811999081081c3e004c2c041c0d000d58808821001c08080540c0c0d0320050461241e00d42011801d181c08d0844590603000c0b03000d51100d10383c0c9860b500c2c0e142c0e2502b800a03042e40082c1d07684603403ca0420b03030007266041c040c6000350310512100180307075113006014100b9201010780c00030490310042a0b6880e018045d00070421304039810b60910f2040c888015440c054240f064048554840b601c0c40c0500045842c2c030301040d0242c0da155039401c43c0601150890f8000c00102c0d02c220360700b800083c1240c040944401502850b2800c1003109200000066940000c898000c00246400c4503e1501c0c2e00380069203081c0001a18580c1c0f01d0140300d00d0805426802070074401006490030418008040c0140d5140e101e03000400038540800c00010f51035142a02c00560414001c1c01402c40d080c2e00e075503c0203002107a542044c17140781d000e440645c0c000c507031010744440101040707441880400d11071007010350340d071080d22422071080e030b408 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 461667041 1250 461665791 461665793
    0x311010c110d0c21200a1101030b0402070213020304050f030310050405060111060f071805030a02091e070507061b1b0303021c06050a0e04050a0b15102d0906030504 72
    0x34007403141d0741110681d1034607034018030030301c02400100c2d59042080039408095407640321405d02240e03049200d5002038600028120040046000f040c1030020141e01c15401e00c03c0b6400760b2039410f00d00a00c0e0b0300e01c800041c0c0e2410603040103440c2009640100c0303002e5104000700001c04681070340140c100d420940b404905c0351035500068991000e054801c444c00d1090508001400d111405490f010b00d80d2a11020360300c040c02141401860b00c80c0c000c168040e4011016840141411000d1503402100b00d501080d0611602d440050000e009940c040d000900100d44032042c000e1714490391840c217110740e9034a0806c5c286c0c000094039802500ca800800481141c289a09040c001e404503031084524070801c0c40850107040800005140e14045e080c080c081211002c40d20b26882d420442c040e503000401410422440d0340c86960441005003e50349201e0001d081b418a030312416803180c400b0040c0c2d201c401c50540801c09000c900c0807441c80210650b483d15919100058200d009002075500030319001c2002d54031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 461668291 1250 461667041 461667053
    0x30c0e060112020a02030304140609030f03090f0d020a0b0703090b18010f06090606080a0525020c041103011d04081611031203090f160b1b07030311010c110d0c 70
    0x70240801c00c060b0000844d094081c1c1c2c00301c01944128441c501c481039580d036102417141d842200321214551580b04020051964a0340070107164896031a2040314120000089903505040c155400c03940543e0020010400300902130450f65401005803400304054401c680300d1403c8403801920382411207080307245100c101042034011000d0398500f1074040c082280c0e183d0f04680188503d03c02c040000b102480410340240c03682c041c842c002e0750001400c494503121201c0814401500000190551141c44042d0806071590b020709131408642080c03841d203940c940003016840740380300c0141103005039140f000c100014a15a06682004615030300128011801789814800c12800044a55051140c040b0709042c22030801c000710300c280c1083e01a960f0a030110340981c0d40d201c2035640000803800b0480001c2c801507006802800c040300c13459194081100240110504245154109400143e07080030003105c428400d02500c820303440d407031810550000c00401d0280c1c450a2440700300081002400c04031041c000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 461669541 1250 461668291 461668307
    0xf031c0e190302160e190209030303011e0f08010f0e0a03090905070302070b01082b0f0e0a03140f01110405011d030c03061e10060804022202220f030c0e0601 69
    0x204c0d00d441c04801d0344488010221000448112603050134030b001c000c40080c0b0307034003e461110b1300290045041d03034240210340380c406448003d807402c1c1050403040043d945000c20030000c000c1c00303060000541048070075120010350301e80b0900303402d440d800300e460100020ba102c00c03a00c0c02c6601c107205c0082c4940b107034141240039100f201000380940c4101c0001007510040401d0544d1441368818400040c0e0741404560b4040d0784031071400c0000b082410f0301c0714081d22300606e098003406000501120786142c4a80e2a041c401c110543d070104580c1c00040842e9101409124080c2685400007c545c04c04e4a440002840350b0071744079040c0e5000c10442c200b110507071020800007041c004000d0660703449103040760301e200241d00700540a00000740c080020680c0100b58031540825150150342e0b16005e983c03140c09126620301c0c0a681043d10403c001c0c203820183c0940c0c80a000c500b05440280607a00c1480c4224071822151a04103542034841c00c2d00800c00104070503481f5048940070b80000b4003565984006846510f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 461670791 1250 461669541 461669563
    0x31801090f030311010b19121e050a0506062b08120103081804051e0603070f06090603110307200c04020a121503031d030a050f031c0e190302 62
    0x71049072001c010036401c10b40308040708000c08000c022061184042000000180c450420094261042802064a80c0180441050140d034002540f141c00078070b1400007a10300c500c02d842c0b5400030001e41040200602080b40c02c040101c0d121075111364150000d100140c111040e00c803482d8500b500d214100b1078180c0903070ba0388038601c141d1241903603903074100080e266001400b0700d1180c009001e01711a480c6030030b100740e030701604000f0028860720f00c40080407560301c580900240d40c075104100b000220300d80340390303100c1c0c0c00b50056944d0804040e103440310103000d4950000d0100c2c4030241c2442008181c0c1e51081c4540380807144020340c500e00289101400c0c0c14034840d440da031900280002001c045854201d0b140300d103182c1c5445410400355814565184a019503408001d0002d60400141d2200311108490207445080003810788214034011359800345030505d07c0322704810b5501b011071445060440d00705040e484c9803402c1c00a1191365030b43c10516032143c1c0c10070010290446900799031001e041c820420202c0301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 461672041 1250 461670791 461670809
    0x6160c0312051b07180903050c060c0a0f020106140d080d02030f25020606091801021602040c08330613080609070f09050901020702150309150903180109 67
    0x21501c006004095034480070000e00c0c0702024400780c40311000000398541c1201d0001c0d07042124041d4251102010700361207402038003081418032110302038100600100d80640c50f11082a561904141005084001c001145c0d2056914000c41000314030300d032000c0c070800e50b00c2c02c885490002880e45070000c640d01440e515245480d10110400c1380001100c0321450042c01c01600c0c01440101d0150300401c40e8801521010040e00208045038003818290b07402500f24410000f28000240b02d1054242284c10034042400c072100303030324412429410301d44281d0708400507034540030546140c0460b10f40b031846503591745070180074504401d840303007043e840030300000904008101503980d100700c0780c25400400c01801031000a015090100e90044c5002400700300700c0c0c61045511f01e090789071525000c01000000c2500c0da055400300000320069a43c0800030303480c00400d00d42c03a520b074106442030600c2d1002503088208020880414003403240c6000050360f120601d12101e03905e200c41c1c40e04c01260140e02a501a40700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 461673291 1250 461672041 461672063
    0x5180c1b070303020d090e0403051909120c0e060a051e0406030605040305072a050103020903010207120c0c061b02040b040912171003031b030e130f05090c06160c03 72
    0x101070780450245e81c806503c1d074951181a8940c04100c3e8082c1017924014003250b0300f0840380c01d0588100180000c142d9842c10031000550751458100001e03559828101c0b000382c0701311000d000c0300540c0810182c20035420389419082c3c90924000c01d0b0305c403c640300030704580c52107038003c0c40c41c50352503400c104080c56004da070610240c1824540540641c02003582115017814580da0045850441442001c614507032100e10f00115140100540003580700c4496281c055408106c4000440c072185581c26616050360744180b40401c5a08082080348050307001300080000003803624510040384406005c0503030f0121000030b07010705450700140003845180401002c00c881101800b141c9504102c418058014180d16900d090352400c01d040920103107404010082404141850b42a110000080d81201d10904081101c0108000012030300f1074407400f102225521108100701011003800b805410606c0c0300010020394403210001900c5004409e200c030b08805290401070103000e134950b00400150f0b0440c80ca408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 461674541 1250 461673291 461673293
    0x509041104090c080606010806030601140102070812040614040605030417130303030507021b28081c090602210903190f0302070f0f03120e03030c010501050a05180c1b0703 75
    0xe91030701813164803018061000001ea09502880101d441080002c025028076030800c2d0816030400012100c05045210310380700032880c2e0b60b041005c00400802e0802071900d891400c00004c0c01e036070b88034544440403801070008000040e000b03001d90382c10a911040785039460108920544050181c1c2c118403000d090120000030a150301940040d01032007055003a66105448004000008140301e5242e58102e0030506910140075608084400d0f00101c40550b41e01966440e0400d51034146500f40021005000c045001503c90b0032980550041c412800a440d8a101c07900e1181204a20300c00000101c1c8000110f010302a0ba0078021310903020b0008440d2407410700682407200e080502c100088001d44036070000440e11028904082e4102c41010910481310360850b03840d940c0f05c2080040040501448031a403640940d010710151188981c02e00001645615080400100500661180b40541d0034001440242e0303551214007684a1f0411800c181e440b0201c0488210400621040307000d50f010b0203030088 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 461675791 1250 461674541 461674553
    0x8070602120a1b1e031506081e070c0f0804051507060e01020304170a17040f050d1b1b0306020310090c05131512020301080d120b010207050904110409 66
    0x80d014680d140ca0402c5964001d145041050720401c000030007060300644c0d0f20605110402d100700350041240340211300e10804940d207402070b242035045800070038491002c03c8034005541c12440c0c03d180c00c081d1407e0003400d126038090407070950200d0140198601a0020041c0400f00e03040320014074000d00101759030207550032200c003d50080d18040300c00604125103031200b003e0500a0b213000311b1300f2008016007100d80d225000540e5000511707240904c9007450100d9089103440084d284517a01982440c00d50068902e4083d080c101c60349082803c2c410700e20403803880c40d820a00e254040c035a115a00d1070122049441034010130b081e41c4e0005011320f00000c1040306403008007030200c0840c0d685440c20710010410b4a003d45003400f0345031002c0d1807008403103010800e40001501910795100c15080c0000c05211140c2d001d400daa100342c02c130710700c0340c0e03c03074500c04d48035130340c0104002901d050802c0304100d18130000c03000039202c0e000e5100d1103126140c2c101c041420322000e40a0301a4104000344104500d1210340703018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 461677041 1250 461675791 461675827
    0x6090b0a1509090b0c0304140a1401180c05060c070503062d07050f0304110904081305010e090109200d0b0f12070512030903030c010e0c01140a0302030408070602 71
    0x1a081c0318110580c002002d5459000c0c2c0700034580d004145441d00c0d036409141c540c20b1380004000f03452655400300740c051030440a00c82000450f000360782411040200400315402c2d6507036070001c2c10015140e9202503022441c88001e60040c6d81c0f04a8060f036841c019550b40910742202d0b80c0085500d8025001071000000d6003103a10403c0c0b0700304840c29003201c0c1c1070031407518041c0400c03104000800c0c000c02110344420960360081d40c0c02032007005415104a800d80c00b01c1d40d5158100c030102c0d40100005a4a9160900804818007e20003442c10180c0f410b03501c004a064004180b0076110802c2c2c81c1c1204050400c900c0030307800744000101c41d29540310041045030070090a080803c513402400640603100703407403d003c01c100e2419620b100040101a19080a2000403001100b2060f01400b00740329410096a05200600b402d010702c4001145035210f03074001501b40042c0504041c180400c0507640c0b10144402402c0d56041c0540d03040040c1c4a13501c41c248820740b03226000000740a288005401c80d0741e41e618400c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 461678291 1250 461677041 461677061
    0x4090e0a0309080d08041106040b071b05040b0d0b0a0b0603040c09050c03090d0e06040b183a020109120605102903100530070f0b0706090b0a 62
    0x40802d100e558207111500c1e0845100420001503003000003501180d005c0880500b1044050003183c6010358800c000300440e0408041100c0740d0900075074038404540b03048405000380c10111000c004070f40c0d6802c001100740c8110b0200400011070000010551a120342c015180864060003481e0399251500d001c40c4c43c2182400396410079032408004c40d2400e814002034034403030400f803070080004009030002945c5c80e6442d4a102d83c3d20143c10000844e15607034850140401040c0c801801008a080004000c000740342c0081c10301034903440000750071114480c442100041d0b001042520122041d41c0012a84031036650040800c46c500401c00104000140e48042c3c031515092101050300d640f541a40d060300b16822a000c08103104c80441d089800420b00025500041a8001e402c000c80c1c1e0344000c02d4001003143c503001c0c03900d003000b10030149104205500d07502c801d00308006428482c0c10b00c1030581c0004250f000310345c01048081403900400c04c59a100da4102a00f100030b40c50b40d8600100d1200203004d900720 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 461679541 1250 461678291 461678297
    0xb18030c060307020a0b010f0f0b0706150f091a0105070219120b06011106060a090c0c060c081b07170a03091a0915010b031819050304060e060a080c0f04090e0a03 71
    0x6c000503034041610018006d8424210300b01c50250f180403108001c54003c40170540d030181e503401204000b00a403151000003005560400d0000600e01100ca0003100c00e54244890304180b104c590b060b1581e845812206200e9048440416000a078401410419016040055038002440d040401c3c4070252109a1240509a880b100b5280c0768407203107507c851050380c2094111503401c4040c01441240d0b002100203101618001049603440c1d1114402d94000e010340a0125480314148003107000104130384000310b000085902d00e010150f07581e01036040780c0701503800500c00340811a152010f01c40e0308010f0b0301070340000903000c3c950140d82c4081c000e890251081c0d1b01520075480319008495444100358101c6021213801421680d47c260480c50b5000c020b0120030300d5000344004103114201c000d4400706110701a10045031254141030000d000d54000003000343c403030201800101d0f0703651b0b80281c0e00e0b9400401e502600383c0318484080b000c0b040d8051750708030400c803500740592541400030015082c42514001e036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 461680791 1250 461679541 461679563
    0x2010e07052e2a0b041e020303040b040608091606120207080d0621050a02040c0509090403030b040b01031406130b1201050f0c1204080c0307080d090c0f0b18030c060307020a 76
    0x40c0c5094103c0740900310040c05800c0c1c800019002c1456080e40010304800304141120500d07840d40000d040d58442d4006540588020405010481e40014400c0c3e0040e01e020080c48514110382001d00c070f2800c1841400100b00210705540c50503007881e01a940c1c610b0f4041025610f0324618000b82c0054095809003240e12000a03012400c2403000d145a1100c1d81d4204010700700c487c0c910780910000c0c2254200300814048100400291620740d017030694442e5010b9940010742440c041c0400003600c3c540000181014208403a04912101c1c0b4850960001c80c00c554a4001000100350a8043c155041076280c2c4400d4442c0d80c405081c60641003203101b10054800e100701a0f480810110460242941c0d00c0c8034103840900040008105800409441c04464102ea0900c510740d910b240481d441a4580c0103000e459911280c00c00400c512114041c0440341c141d4050582000d40c8900d890080031203e01c10341c6060005000140c40500000c00780b0705000e000c81c2d50780e281c40b60000c1d6541030750800484070400d0031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 461682041 1250 461680791 461680847
    0x90f03030310090b040e150a0c0806100806010c0203030c01140109090506310606170f19030504030213060e010e04020102031c0b0301141602010e07052e 67
    0x10044030b20a41d454403141c0c50407070034505030340b0080c20850030664006030386044002543c1410004036650600c0780c4121039480c40c1507645103007541d080800190a018410b42408500d44d90400040a9103440740b808082c16516400125801105a6006501800002444d04400b04d064200200d461586403074400b8a03641c0e029204202c0e140701d4400380498008801140c01c0b480320b01c10140b81880d45001c07041010341c4003800030710000e600c03034000c8070550b075520350810041503556110300d4019115006001c40c03001d03000e40d079501c40c14940c11250000b88045501400c042c0130300103540c0a547c0190100103602441d0540c0310080ca40c500507140f40302d41c07010001642170301c2c29102a109a506a01031800c2c0b0400043c190380081e17803014455074240d140c000241d6a41c80910461000040403c01c404641c109114050b1686142c3d00310071003164103080c0311503170700d03800020114111041070351f004e1004210a01c4c1072940c0c00b003410a2b1803441420174841015503910444907051b081103e07008840200d08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 461683291 1250 461682041 461682043
    0x70e04140f010815090705041806021204020414040c060e2101050a0501080313140d05010203241e060304020a231008010503060609091608030304061506050712030f060308090f03 78
    0x4c50b041707a0b0301c1d0f00c12001480b4034201a0001c076000d0a070040030050201d4141d0300c1c10140c1e084000c52130340b007940c01c40401096107094055000014081882c0c8007050409031035804100da082d008003018002001c820074000c0e02c1c0c1c071505070b2408484d0082c2040f014440042a4042c01d820340d6040140760610300080b6011102000b210740340d030413007000c810a04c0c1c941040300c4580140d03141c0d103a40c00841c684419000c10030a0000f14851040d00c02c1c0b0208603000c4042d0840c2010220883e10f01914400d02510f1b8480c5100e1400c800700407088800c10740b40e135102c1c0f00054085ca01900202c20386401c0c411480300291902c01c500d0030b1140116044c0b101e10a08041c11211074001748a100c0d8994000303400b01c5c0c52400c1060200341c00c40420407d0b10b0f504442601c0700301c0e211481c0e070301c0b00140740d1000040100b440740c2c83c4100c2000344024905a030b02c2500d0828024040d02038100086d01e1101d020076544545c070b0081d8002046003034424003d010180ea60f051602c41c42d080100030307900502c1448045001c605e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 461684541 1250 461683291 461683333
    0x606030c06080c07350712050c0a060b060f30070807231801080c0430061b02010c080c031503010f0513021003060e070e04140f0108 58
    0x511150903080141c903071511064111003405c5218100e0901d01d20019100c07100303143c00c44101400b00030301d0b5110054904141403128060310a810403005015940d0205404100000a69000781000c076140d007020002582910075100d0080700040005a07074803000190018140e03115080101600341803c02902c00c00c104d5070201e0740d04001031086000501c21714040c40e2074603104601e2440648407601c10f04000d22007903109130590b13110440c00040d04507445da403004486602898041d41141491310b40400b0010005c44000702442e070342003042d0950160818400c0d0441c80b150009014045001c0c0b040500035050202e08024005500381525201201c0c082c1c00e41d28001c901e141c0816155590b4280c80002a103454210740e5419501c078002c0b0281c030020b50151038004d4006c9a00f020700c90859104010548103903015510a06050940410070092000807456100c03816050400001e141ca200103001091148003010607103c21030140590b4400001059041c1e480202c02c84403070180102803050880 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 461685791 1250 461684541 461684551
    0xa0503030a090302030912100617030d1119080f130309030b071110150611030d02030406090204050405100b042007031107080c1c1a0606090d0606030c0608 68
    0x94020004555240c203680e000e440810301920589081c0080d42c400159040040e41500ca80c0d58450154002041014407032080180044d0101045000350000c3d0581c8038001c0300040c61155540d0360008850850140481760801c000c8842e4504941c4588400f505280701500d400c02048038540c00604010001110f045103503815444590403245140c1c0ca0480e1a44001c20f04000c110040c01e07241c034800c400b00640d2041803c2440003050303403106662020046500c6a2280c03082281841c0200c0000c1c0340070003140c2d024048060050f80c0d039030b0303282840303006009913501c006c1d006403801d0204405d00034041541c2100080050081c001000c4010030017050311030710381d000b0903413150411201e00724088403001001c4440c0b085c00c180d44d02503003100009003464031a80c00844160450380f401141031621514401c080c054031070b44580b07840e03082d4480300115203c081c2101d4043c1c450f00701050b01c0e40d46090603290b2040000300482c4000b61545403450241105100854a59401c2140840c2c494010220140300d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 461687041 1250 461685791 461685793
    0x1c051b061c0e030d06080a05151909110a0303180e0108070b13030b0906070f030c08040f060f0203010b0d0513020609090709030c0b03090c1e100203091c050f0a05 71
    0x100307031824100c0100700400c510070a521080014621914090040300003d0020700c02420940913035050035803c1201508a041c0821455420001c0003c1c42c0050303821440d0342c060000030403802502e409903281041000345a0f21506c604400004c056111420340244076011021114607030342c6a0960008070400e001381030f5190001c0005028102841004d011410020320b12000019a2500c9030849020250780c000000c1e0882005c100c8125084030380000c5090180c2b0702000300361740e020001000500040d100901c41c102c01440a0107101403900f2440044101132401c555a5941d01031070992a8489065401c045007404e00148100d1250162960440e0b00034003610300c0d091104080100e80c40d0300030841810301c84200c4012000c2500e4080c0c0c100507042442d00c1568034180599440e18144400503003500c100c84000c1c9110030f071418a00e03c000c0c4090152042419010030110503415805504e00d2180c100d108000c000d8401e1500ea00302d6460310340034500b9142c5001d0010095602c4d46c80c4004040c001d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 461688291 1250 461687041 461687077
    0x40e0d0e0f0603151002210a02030c070b0309010608060609010e342a03050d18110103060b0307081311030d08041e02031b1c051b06 58
    0x856000c0c0c98485030201000305000c0480396024000781e0b090304280c80840118601e440c40080d82e052520640301e83d481a030005000860001d598641c030032106443c40105940e0103c1c81075030242c02003090300c03050000c4506a03440a42c49828491040d00704441c2e9a50a43c242040024a8039002c641940181c001400c801e8490f800c00721403100348080603060828410a0094a11103440401c00145456900f4a02e50214011814000708001c100303034403800400d10303c181b00d080e5050a0f024510225585403c05071707103071404082e84100034002c0315620341e043d000c961580030800c800071181c2c04114400362801c005091703c4468400d0240400c9031a580070038240c001240c48180f0300c480d980c0c072152050807610750b00c920030360209003440c4900351000045416201444100050401c0c47c80d00c140341100c691002c01c09540010313541d40344401e11845e40720018407400209807100740301e0b4207640504840d000a1030806d0b1510580c3c07000c03100c0d1203494030107100f50300c040c06140c40e000311a020b40190400e8a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 461689541 1250 461688291 461688313
    0xe071a090607030e06031018020315090a060f030f170c030703050d1e1409340812030406050105090114010516021903021810262a040e 59
    0x7803280c0c0081c2080d8203205280940c01d2142c2d84070002984074009030400c6011507407400401c051024511040386807290700510802601413980c4250030b1607000202c50380307030b40768940c00c003400010440b98020501c800d104d40c401105200750450311001d050300c180c01c030022450042010385c906e03000b44201030061b07400c2000140c0220748200c0260a11141d00e8a0002e001c01c00c244c1d0107560a60403600000030340c1d03200c40180000045141c1d11950000500d806009007511400385004660b150f541a200084014400703140a1032054003983d0240036114100c0f40380403a9000e8615140d04212011620942800001300346800d140b45168120b0314515441d8102d004100015903107600185a5071025030107031548003025a44040e50301000c0b8140060342e240444c1107005001c014504034a003a0303002c08001d0288082030390700b510003104a8144801a030798000300e031081e2007000c4201c13220720742c5d080c8184d0000f00d00c200e0841d400760b030007060861443c641003690340081c002500d0003038200303550581010700014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 461690647 1106 461689541 461689549
    0x1505180c041b030f14040809090112030509012105010303051e040308041e080f03040905011401020a030e0301060b0d05040201020c090103080f0912100e071a09 70
    0x110804400302d19120600c80b05903600700c01c0590b610a902c030320001c55880b507001d0380a50303100c424107400d250414003d01c0e00000c3d180361081c4150400002ca044018011049941e490b4641a0601401d0001528504180c5804000d0200001c9400444200c50300c82e40740613510946500352129070700c45441300e903c440c180106000c1c03401080180041000c08042d0f804840da504104403030780c1072036a0101c01400841d801881c140c030400104408140010002d0030555100c3c0d03504104581e80c50200206003511a10700341e0160b0403411054000c60b00c101208070384014040c0c004140290350300342111959102e417030110141d80d40c84062004543e414020724441c01001c4900190550440d1250120340c0b044010b4280c0041c00050b0340c00703507a150541e105210b2200ea0003a80c00e102c2c030303284080c006850f14062890090013603410100c0e110001c5050300301c1005407090200e003001d0200303082c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 461510791 461690647 := by
  have h0 := BRFrame.cov_init 461510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 461510791 ≤ n) (h2 : n < 461690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
