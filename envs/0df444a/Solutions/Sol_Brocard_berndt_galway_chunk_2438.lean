-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2438
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:43:17.982306+00:00
-- url     : https://prove2.me/submissions/0d7dacb3-41ca-4d2d-85dc-8f3d22a47043

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 438309352 ≤ n < 438489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 438310602 1250 438309352 438309401
    0x5030d051803030718290d0204080f07051009120305090402190201060509180a0209060418052d0309040f0209060703031e0c120c0507170a021b13 64
    0x10b101842c0a48000d81d81c0e284018001510001d07040080d0300000c03080c82c0c06610003050100c40c80c080c0080c00115125894072061a82c405a001703004561040d030080c000c2060340140144003180d103200751707201101c01100c011107065044503206014010100404804850000407074020809030082800040c005031034041c0e04446002b0980044181c600940e44425090000f0320300340c808181d00040c0c2481c1500348007070310200c1c155609215500a0b0180441c00041000c1d521030740c110001080008914030141461840c010b581c0351200c81c101d0603d06508000c403808041101200c59090b031a4100031402c2c80d6586e42000000c044c0320003406e241a40c2001808001c1c0c4a0320013401030f060094070000b590040243c61104905041628100b60528150a180c0d0007030b001842420a0040d132000010403c0700c88600351064850b884c405041071842580c84040002020003c0112603100d6090320310f83c0120010108102c00e40406850744140803000d80c0481c00d20713613400a5a13180754007082c0000c03447c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 438311852 1250 438310602 438310651
    0xc070825020d060c081803040621060305030705070b190e031614040608010204030b01120809032a0406060e3a02010f0503100302270901020a1b05030d05 67
    0xd0b60b04200e0301180c480e0100c0710703902e41003038034103521a80c501403518038900071804040d102d201c2d500540c018408184050309042805c4558000070302da8200003041056181d04180b07503203400c0180e00f21070030f20400070040303007400b004403d0301c1e4a6000c600920241c90340e2070000342c07510240d034948242c040c450108510010144081400014882d078034502e01e95140220074030098500c5a0082d50f066801000100002a5041c91080c1103030400c00c00c10214050300d10b0519402d110f8460b0301c41c0d043c45480358080c0c40b581c0000ca0454154108209020458502c00610044e5100381c030031b050202d0f40151440005040c00c1104c005a96040c1045607002c2410110b03540d91030480d032010144030302818440008550300085912802d03030481c10301609524015820b20507a03001408024051541c020801d522039802000c010041040402c84035224034060144a0003034005c41d00e00f5000984110403000c0301142d10081c60a80e40d00240a103242c00340080408014010103441e01a4400c49208102070240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 438313102 1250 438311852 438311869
    0xc121804020a0c1a06010f0c050607030b030f01060f0f06031404060b01120212090f06010e070f0e1e011b0b01030605060f0307120209010b0f03041b08070e0604050c07082502 76
    0x1c0c0d00c4a05130b40f40e41040c0000400c09000c1c0e003070420034403941e445d030302010540c002800ca034029030703174503000c5a03070405400801c0c01c00c014941001c81d00e46c00e0801c0425a40c0c080c0140780282d0310303142d10502d4802c1d03481030204d081d141c0105840c04803540c903a01107130114140d600b14100400040c10700c3c0940d240c00c5142e04049901c043d54100c20280c295052040c070010621000d4900f001800080040394107025103100e07071040142840090244581040b1249805500408000301c00280700180c03034000c0102d42d07004490341ca100300b40098460303842d80c030f84070700ca08100800da25004002070120b40e0a541d903d0000701805480b46920001c26184440b460350100000806403601300c103030203003850661040c45800c1506130041d440094060000000c0280d200301643e5110f80c0040d059a180000101e41901894542d0017400a6008041e0701040d90030010103418040c1c0340c04d94081100341d40362424030990740a0704c01d00510105042150681c10610314a8144050600c0d1060740c2803140b4a90006d00d058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 438314352 1250 438313102 438313133
    0x5010c02010b010801031e0215040803180d0201020607080907030b010321090b180604050a030807061406010c02060d060801050a23090a0305070606080a0b0a05070e130c03200c121804020a0c 83
    0x5130310015100c011037840c142440c50f641c82c26641d0b0350307500b01150b0010b0b4071504000d00c001c0402548000250308030000700a00f500841d0408041c40c0076585a0400c019075080c015509010380f1154500034100500c0341030290308880c0040c1d503050400c41c1ca00306119201120910300c03a44544c0c02c0c40081801da503010710000055100e520456600c014a1400b501629442c0b100e00401e144517001304003040c1d800c1f44100080984c121201907681c0b40d80f821791700081ca45073300001c0441d032030001000b110101035401204502c044028003801a800000c1e0110014011904515140c0000d080f0300d000034040c1018102c201c2c403c0c01c0101c2d01d141c403054040c0ca0040b2540c015514040f00c0380c24040300281d24842c840d00305001e031a0050f0440005070210b9648501a89500647e41c0d4456030021840d101c0c0d0300680d510070f60034402e1459030025428010090300044407203805130140c0b0702c107010454200b008851120440c90002400d002e2031100b00f1000b504041070540c14403401c0709202c4005035541f54030042c1c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 438315602 1250 438314352 438314369
    0x906040905040c0605090303040504091a01150e0618090403090803070c0608150a05120a0b15012616050c010f09060f06060c08070311060405010c02010b010801031e021504 75
    0x1540340c142420f2900b241a54400d00900c4030802400c0900d49003c800c4400f070f41c00a540200703902515191240504588000717140d070340d43c60b400011481a100d01e44580031314182d84d03151840344c2d050b107081110621401d2044000800d0f1212043c055052000031258003d0180c100016010b80e911801c42c2983e11041c0110f844580360300082c411140c01a0305190407240310380c0c40194080058001ca01d0140c26802600d12030404200b0703000313081c802041404000345e031000022813941891b01041c02100c03410550749010840c000800980d803003440d110f4900301030b90180ca183c403503100d08641c2680e01c0c26550440007002010028010300301c409000300d048000d41c20200094034a11400c080c0d04540300c000b460519039046c900d0401c4021f80c4200d8514032150407a04417999000c0c546010303070301c42030359616840d4540070344010041403240c1035024641d80760482c0c00a01100000d0801100d12000c24003000b00013005032441d1040d54040c168a08040c00e202401841c0903035500d1944644603006944803051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 438316852 1250 438315602 438315611
    0xb0103050c01091406030f10081b04050f060904030c032d030b060301260a0203010528060f1205010617030705251503020909130303050f0f010b0a020309060409 70
    0x3540d40d02100e0f580044c0101c90100144070142800644d1600c4040d00220001d0f181c04042040c1500821030700005280b05412586104d0403c18030a460303900d8106024403c41c80d080019225540700b004031845031320002c0000300c1980d80d07503a040d91803462140083e000c00c03101c1a42c00490345911401c01040994035005000d40c125406c8005003540c9000c0c8003103000340c005100402c00e00325400703488542081240c400d2100307050b034164403510780080b41c03070040c2d80b660800003031154174504043c1d03401204010600300d022804500aa89003590b81070f01c0784047c5411015820003480303050305e4440291a210714004101d00b5500c071003820291541c021030300c1003600b00160004c104003003000f0301c2240303010007440c20204544c60560044110b0715486542e900d0b054001a158400b8420b5040320707100340e4010041e003a00e090803505000e03c02e6802400306e010038a4007001c20b100d0041000618403811021300140700a0f8201203450302d05421080e001c00a42c0f000340301d500c04964401c03010b00301410b0350030300026 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 438318102 1250 438316852 438316873
    0x5071a150a060207060e031606050405120703080d0b010c0501050708011502120403060e0a06060603150b09030a03030c02010b0901030602130605040b0a08100302120105090d0e0604030b130b010305 86
    0x2025051a0031880c03007154007003800c00a42d07070041080f0040310700508100e00e2003964180807906050f07405080301180200b106011502582000140082d2401074600ca0140882c002400303599840e1804081c180e82d405000740991118607800c80308480b04103140c441020001541c1e41801e581c42a110900480d0300000140401081580d4060b034190711480140041039490034502000c0c401c50001500780d60b1030399003003220f040c0c081107003c601b96800a81000703c03654920b4018018074a82118901c041075010b8009801005d86045d5401c200b0014040c02007883c0d80e0303809070020008000c2e008155501d59000e61902e83d41e0041c9140254010b40000d039036803001c248444000401600008140802031000784070182440056502d255424201041c66840340c0804454484d80c43d40001e500840e11815100e04100640000f8060f2040e0030444044c441e00d40320030781350040c0c800865030304140140802c10200e11442c0c40d8641201d60800502e0008a40c3e4940e040006001d80099850ba4016440740 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 438319352 1250 438318102 438318121
    0x3150f0f0b0a0b0901020a05030d0507020c0103021c09060e010609020d06051002030a12020906071b0506031b181503070825030e0106050a080109050606040e0d0c0305071a 75
    0x105000034995400308090000301c000903551200a00034450840c40100f29003500d0303402000100d107102d170060210390302da04c0e0782d280040250900703c03003480040c010350940700000c1d4000c2c0240c4410081c00c00d146110707070300408500d03802851241c07000e440c001d03160408400c02c000d083c40b440f4064143c002c030240e6914000705401013666456802503014140c500c510b100c1c183d9010003551510b900c5440d00a000c030740d413500d40b400a400b4070303802654040000141d1404011038503003048080320001d0070114107070b5070700e400700b2050b40821168450300002d95000c3c1c030080024040141406501d401980400102c43e001048000e010008502a882c1c1c00000784210680c2004144c4c0d40071010110000031454110144806211020468010f140e144c4010064004088d007003480500f0002e49160f895503940d021807800b8041019055600317002d03d8004c43d0050070240600c464103030b8804001c2611954401c400c548044c06001c040d003c00c5800c0c0003050003e103501d80c99000342030442006900c0c0d41440d0f00d91 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 438320602 1250 438319352 438319361
    0xa0c060c03020d0b090402090f04080403021c12090602030a27030b0402120601032f0909072310180b120708160804060b030c04330b04090902010903150f 67
    0x80c1c1740f007440d00c0c408110045e51001d801a5111006110188940d00c442c6401081130040c0c0d0002980580f50404005c10001c0d5802040d10351800b0700f040c494840003440c401c2d6120010340c02504010b8004000c9100d1041c01911640d403100c920024040700e0401c400c02503d0b0700901a00101d41040c80d06080c4015031400c050392625030304c0c40384050002035140d0341c0d03020b0300d09100e4803003c50782e1001e55050a0708070405450100180f607000d0464541440c2180042ea1910014000c8541800346603c8002c0c0302c0001841c0024448400307000c501844210b480207464800d4400000b030740c000020b000c003069040000c4060540e0626960303803c0264207240402030417190009100183c041c0f0404100500305601480040d040f0760000f40c0014030403405404a030608120000c9a070b0014103010f6500d44203e00070081c01000040c03964258081249030f01800c0e00814240b143c6004010f043c0014084043d4039404a002c003441410441121680d035916421002c011071000210300340e0302d041d1032518641c3ca004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 438321852 1250 438320602 438320621
    0x80109060e0607020c0f0a0503010f0504050f0f0709240914010506070308040204052d04110a080304090225050a0507050f0303040323060f180d140a0c060c03020d 71
    0x1030449441e0a01000f940e071000c5c1034441e4031590703154480c603d46856445103030f00034090141c028000c900c6500f55290103000c1c1aa0111400e11a591044c820008086101d100e02004070010b8040c444c9400c8036039001d041c045909034110b114030001c1448203d4207041c0a00142900700010030b4044444443c0301e651001603010a01550003080740c20b0020394088242c9a2007581280c000920b0f0312011020a01c4034031002c110b4003d0744540481c0450960a114100e00c03c40c492129181d042e101d10007840007004280c400c01007541d10501c002c2c440c040040d00a00030280c5404613500205104851015000140c1c4c071095a2542100d14400d0030300406100110107040107036900303500d59505102007543c0b4480c500c0043d00c0d14100c2416030b040c000450b9418a022140c881c121580e600f40010484945a026998540c0490030601400d104500225400d0031075010307a2a42050601d03035111005c1241c0c01461003501b0401c1c090011800941d40348110842580700350f41c010307102c4003013117808000c0b01c40340300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 438323102 1250 438321852 438321881
    0x61203090f0f0b030a09150f02090f03030a1b03172809080d0f09020607060203010510030506030c0d020f1e0a050117060d020114040e07081f05090c1308010906 70
    0x2e014041200030303608503508010902c500251014086c10030040507120714501c022101c0c107102d400412000365801a1102e100115181c51120038400300705070b40c83c46402102e1021522952000c045207415000b40c19400f030003401c0c1308154916944040400b400110b4808405140e01034500312070100d0000c1c3d0310100e5540f8a410420f00619842d90080d90040104018041e80c540c0d11007818070440ba00009071003903005c2d001540f50201071404070060340003402401d0103401139402610310140b09000d803901580c8090040c00e1400b07215070030b010f4501c0d010301d400d0307030084049856820b1540304e07900858001203030344400e081c41400e64002c04c5003485442d400541000444020118804088280b49400071001c4a05a002c00118030050f5244c8407210341c405200580447c00003800d040c403484e4640309a8403035a90503d1a030b1221803001c09161012041038420b94602d0b020b0041d410f00c0d61540e504a580c02024a0800400e03411016654030b071034115608030f94480a002e41006011300580e001c0040c0302 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 438324352 1250 438323102 438323129
    0x207262701090b0a0905060f071b0e011203170403020604030e010e060f180a1202240703140903101508010c1209060209040c050a1d0a0303030e01061203090f 69
    0x450000b030200c0260300485401803c0012a00b028501810020740102000f030035031920b41105545544540d08007032020340340c04403080c6400c1d4070b12551211203400d4074841720302c4010036401c01d0081172000f605108101e040c084030031028400480d00140540c8103601c02d5005000c40d26140c54000c1146203860f98403414400e0304150600303696542003d0703c5500c46116010340e12a03821700c40072030398140d403001c00d103800500c0d10300302143c0e8042002d10045000d000307580028102041c071645000c40e03015003124132001e0505001c0080040d20904081000507010305e045410031300c00100107418107a0000410001070795a003a454008441480200e0082c9a0b10340200111600f04001900c0b482ca06a0032001d0709659180800c108081071741a1180c0e00406001000362103800c9001400070380c00a05c40310081303403280340c26402009000410100c0e410003d0802400c1c0380c0b440d5030a40c098017078402144599501e0b024045000c5000040d00742085002e50380c0e083d18545014404040c12005801280030f21814 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 438325602 1250 438324352 438324427
    0x40501120f3e16060b03011803020601030b0f01060c1b0f090903170f0723071113060b0901030b0a0801020703050a0f0e0f0904020103090507091509140703020726 71
    0x3e0010a0b150190465800b09402614400081c01001c0030080c4141000d141d0f1410740616a00103085416a0f00c200c503a10429128400751441e210401d125141c00182c800061400207a081100c0d11106a103d442c10114542c40f840f00017900741c00c0340c101d0000c05540d80001030915500c2420446a29003240c040318807410f000c2e8030058a0707c0010030760740c28000100030110607401540500e907403141113500c0301350f2190124904004d0488204800351710510040040030800d80141c03290804580e0f084854038504100d2800640245c400445416031160224200007480032007030000b070081038840d40e1180d50301c2c07c294a000e0422100d010000040101c001c2c42c8005903154203460481c0c08508440000780c950340c52004902605402d00c0081081c081e43c0b800265407001074000080381d8400e6141100300039240c605c900200c03250345448003840340500001c218414005d07801040710a000304001c030000c65802e0810b510011510301c4a062300400080c00001140c0b60384209840c04181241107201d00e0711 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 438326852 1250 438325602 438325627
    0xe01150b04031410020c010f0b03060f07030507020102040f030c060314090a030e0d0210020a02030712080f090103023a09051e0f07030503091203040501120f3e 70
    0x91400300030036800e83d0b24000710a2060400ca00910303981c12100540d55800c1c2d0f55045806000c464141e6070300e03a801d01600880a00c0d02061031480346142c015103d049682c0e0718000c0f40a000c02030020425950b0030040400d00c072074070791040c0003e136029170340e2071017409d24252008040f40d9940d040362415a81d21800e104a200010078020b075007681618102000c00c0d0f262000615901e210f8600a41c000302c244903541c00c1c10340101d451001c603802181034502083d42e50b040c0350b031400c0c000b52005210b480204107074007040014101812410703030306140041c01d11490b1958240344200c408010b0f050800c4464001c00710f09500303480c0146d0780f1070604003030211484e941e0710269100ca01ca050000105024051443c0e0714104208038005003232010211144107559082c865104d17030040c0c030000c4c05040001d18a0b54400c40010896084034410303543c820113024003103c29802440790304500304005440b9030000c0c4225005c0b1501e880d01c0c60301036401c6001e01101007544000f401001c080715080728424000e034002e882 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 438328102 1250 438326852 438326857
    0x1203091d04020a090f06120b091c050403021c050703050f0601120b0406050403110118030e190b0f07060c0e041401061d03010f05090a1401140c0f0c010c02010e01150b 73
    0x4841e11300c0410003205d1210700300b001d890b09070401d016038010300142e80705000d4800c1c5124040d40d040015a030040a90ba500303030301c4441006400784089001000300b00018280348010803a42d010038030606117a0785042c1e59503030420308144e00c19203895101180341440b1010501110780102aa041448401c484550718840c1b010b070000c0026041c140d41e41e0028081c0750059180c50354906441000300300302c0e030815120b12002c1c00c1ca8a025000691013a9901202c2c0c00c00307403507200c1c80700d1060a00d44805460070701c030507401d41d1107920542102c10f418440d4a0004445028885c5502c4154881034849100f403028001114441a0054810009600100082c0350880650746880c1301109140da1701c40380740f4001c00d0243c0441000084418030389800c0104040c070102c2d0051003e4030515181001c450089507250a8605d006603080400d8562008141c50001d4080101140a00300283d03070708100005ca05a400c5440f5400c0312800351f5100c0d4142940c1c2582031244143c2500c0c0c000203c2210343c10305075940c03542e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 438329352 1250 438328102 438328109
    0x91403090a15030209040903020304081006050603060904030c050307050604020f18010b0a0c0f0b0604050903070c181b3b060f0f030a0b0a060309030203030f07091203091d04020a 78
    0x402c040a00988410f01c6501240c01d1104090011301040c2c002d4500250740c4c0e4850f1040086070301270205e16248010640c0101400c070b910003810113003140c8502c0c2c2000700282002d0800c90a101c1040907050008400b031002d005160701600c0500300500d0a401881980180c1c918140e101e0105041300320502026040d40c2c6041d10000d40305281c0f62004100d00b6140b591203488003409001c1c5054010b810801450030721841104103440a100c0341d158070040c0da83d40d02811000070540329050700d007800040c9000c0904019281c00e81c03004a00c003110b40804160010051800c9030001d1071000a140640080c3c02c01c52081102d051000c040b014950080410100d0b074800580e445100e00040024602150b5001c0c1e54000c824204e50b5070f03503410114811802411f00e50821405954440c90002e90b490192040c9204d07150035402462456035034420a540480000f0141e4040c07104102012850000c41d981500c4814801d448071400340341002002c041d007403680168400c40d841c8034410400181c4911141c94100c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 438330602 1250 438329352 438329369
    0x1030f0207022112040b04090b060403080a030c03230609090601080d0806040908032502121c3b0d020c01081e100e060109140d05030c10091403090a 65
    0x2802d08049007141084c00002e9000c05045003c1008245041c03808000d10840700c407003030b007006602c108009100b840e0056202c0541480340c18040b040341540a82c02410542500f807034000b66400428a808102c496880d0000303818224002c09c00000d41400f00039903030080c0d1340b00002c24440d031411003507035a5400400c20308400c02c103d042c08164161a01d80090052035400301041c0d841c5d14010140c014840822205181545c44503501016028000701c0c011203500c4d28490030910b083c003030800705e510309441040d1601030183d079001c00b21000a1040b09001300091440071040c8101c6801e40b841c00c4596007840e0b81c920035000007c0c002140ca0b000990703105007840c00c0c04d04c0650307950707611881145803080442401c6501a54004c0103400e402d5040d4007030954170014039001180c0c482c1801190380c45c01500401414800300c0c0c5c80200140b0340940790240261144046900d080984010709060070f5541204030901c5489801c484c003000600700c460021201c107000198102081403000a1002c1c1d0301e031280041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 438331852 1250 438330602 438330649
    0x5070b07080f0a0209040f0212040203070603021201061d0307030506071103040b0306100908010513140102090f28030609020f120d081003080c07030c0501030b1f0c170901030f020702 80
    0x7016116904200c01344074041f4001c5403240948000944000804ca5080b40f107030148060114115000c1d100340d4100100c1071030750340120780c2401d0303050717440b0031345480d0058905186000744807403543c04101c140d01861098000c0c06d0181400384005e019002d02401840e050341060006015008070102501c0c2e010350125244c1c0c403c140e4405080d00c5003103c94208020340e50908040000180d803446c01200c04901c0b4000c0100c0702100070200c1c5080b4000e8000e0643e10203444d0403202c22604c0c24208a414160183c1c1928100d5001101c02504990440c2e100720f0742d650b1500a441d0561400421603540d50b1001c1c0e800f145008404da1000d40c40e43d02010f40041401003140c0460401c00c415088500556030003100c06a9541e074684a80350f880c5401d1204959504e400d19000c90340354828001c1c601c5009001e0045803030b0440c6010034003403030180150010104080b00c028080403d00d0501400000040030141c50b546081240c001016648504688405140104101c00043e103800c542040d181107442c07003880 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 438333102 1250 438331852 438331867
    0xa0b07082104030e150a0c0f0501020c07060e04230c1602060705030316031a041a03010501170c01080106050417070306050a020a030612020102071514040605070b07080f0a02 76
    0x10000e44015078a50107403140040104064010480390700c441d1049410404041d000302141750180304034020440041c07a59808480003454030101d4469441c450790015080c490200041490010b06a0043c00060004038220300642494494040b280d0b607680000140314000103c010761419000e8203038400d05d1800200c440d00000e4803100c0d8000d03240c0c004c2007655500075900300590b0f642c10940b810342c420104070a00941c0240240700341365400c141c0c280c0000b1540f5a8204200081c402401403600d150034000380070505940a1140354003800c0c0b401c005181504c4544100d034540311018a9043c140300c184001449110741280c10342d011107014080c0701602010f034000c89070600780c0580c401030046040c00203010703170f0b003050340c026200c41b0100d80e404204166441d69590f0b988000071401a016800241d0148250180d00020981c1c125060500c0e42c018504100960040d610940c8541c0000308045200010420350b40440c54014a00e4902040c00d030500501c4249174410240031202941d90004024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 438334352 1250 438333102 438333127
    0x1090b040b3c0418050f0a090f02090c0a02150106051e09090c030a0c0306120303020a090b04060903060e011e021303021906030c0c080d1107050d09080c0a0b0708 71
    0x2022402080000c0200380b0202010500203500540520401840e0300c5100c9042d0001900c02e0600c1106c4138245402140c407203011120003868491405c4d24400b140307004040240e03d90400d9140282640315160355201e502d507400a0504402d6201042024144001001026400400d90b607100010f02140041a28082c0f9000c506100f01d066194104040f401000b843c055010702441c03003040b079107000344036043c04203108808580c0280181c081d4588000850f40110b8841d9016100748a0706041896600c1d843e1802c07080740d0741143e0701c25030000f41002000c0c81002070742e000d81244000000c0007408001000e04032444c4622410407184074095010400424914092802c10010b54014101c0c0320402e51040c0045d8920301c00e0f00601002c05c0c248440304080303521843d01c0c030480c0341c1c00001030740c18060329a041d000a40700c005404003d070442400041c0200d0414070004480e210b603030319202031350380ca03010300340c6c0c103100c0d2008860b4840ca03035405040000c04140c004a41c0525400440c0c2036550020750341c0e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 438335602 1250 438334352 438334417
    0x301051305070b36120c0108010b030c0403020d050105060307050103090b1b09060703090509220b13060e0c151314150a0513050f0f0d0f05160501090b040b 68
    0x1030780346503112180c4c106070b400a0032140d40314120944904118000d100c1c0c11540d0b501c01d01181a000502903030041201c0407120015540101001b01c88c0ca142c1966a000903800785151102611181d40d2802072104d9817808014000050400703090620460754540c0b04c0609202004015180343c0006e403040000703030b20801003243c1d41d0400050090340c42c6c40c0303d410b0050000c00d081c040d0310300032aa8040419101019054102c001d0003c03d421002980d9407683c0d112400ca0000e040c1d41e5410100c0300c81c00d00040c42e50301400840c4069040103088440c00303402001080302c0d440c10808450740c0701304580c162a01c0946142c2d4180d03820310740c4400c45801c110020900c00d05d4041e41c14590f800001c01e41c031840c039a00000814540d801280b004c00002d88034400c204010255065a540c805902040300e050360511f82080050503000e0205841030f0416511001d0520403c0c202440200ca11510144550340c1c1000344080a402888040b509040c03c160b5031034080e116039001042024802841200c0b0031000d22003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 438336852 1250 438335602 438335647
    0x12050c0403150e0615120606031e0f010212060405070f08060d02010e0d03051e0324010c060609050709080f1b0a15120509010e0606190e090c0301051305070b 69
    0x12501e0b05e182c5131900821705510070128a1244141940003c21242c00040003030040500401401803020321000032080d040d895003e03583e0300e000303245120308006000e01c09011036036158101c1540514000c0100030031141c0042580f411b000400d1003058140d54800c1a8030b81c4100140e031038001010036400160307104500b05585030751000180c504c56041642c8400a8030f500041c6200800b40b00100d5490210346d400129450320000c01903107030060a40c54154644800d040040c100704c90649a80d4031001c0c290f0b1101d4100c4941543c90b0424001ca0980c04648000244400030261030201c082100140c0c4074264144040f21010180e030701c0c0406652075004800050000f1054280501d401520241600d00303050030481c9a1458180020048003040c0942c00318005680d01038003036a52548200195502d1030180f0315079100d404400481c040700b01c10031143c029039004000341202c401e90001c050945134020000403220001020070000030341c0004e4164240d41402041035210102c104008102e003031100d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 438338102 1250 438336852 438336881
    0x90c0114070605010b090a15020604080a0e040e0c1309080403080f0417070806160203070b09120c010504050127030509040b0409030e0a08030307020d030b0a030f0b0712050c040315 79
    0x1000017561884880203001016042e2488003c650b5a20036491b2504014504080940c0013440040c2c0050764a40c010040b502c4241480c0e84840700c103502003030440e01000864826640070031600045850007001e4001d01d00400789040c008030459649041842c003903071000800340071300890300702c4120013000f05035005415490351200d000301002e0102e60380e035410307440380075424001c14020079a072020003c101130381014950002d528101c52640d900d0501c0000a241d03080074007418aa4084451a80f00100750308030024001155600b45800c00508446114480450304000c40780d001c000700000c14004000141c050900e5a01e9025507808500540900d100c4143d0080c0b034401c13410100746c1c0160303090740146020ba400c00301c420b46451186540f44401d0300d144002d40d0204e9000118541f09400c00428031401400c03044010780c2d00d60750481030100940c4100c8001c0c030564200204940c1c000d42161a21603a804240003509080d144211030340300354000034020900220710042e1041d01500001000321290 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 438339352 1250 438338102 438338111
    0x8070b240d08042c090d05070308090a08042d03020a06050304060f1823100e030c030307030501170109030801050105030411030a030e040b030312150d05100504110108090c01140706 79
    0x600c400071305012010340041e0b401c841d40c0129810481c00602500007000540b80d45180100742e460036150000000d0100c24548180c81004000540c0340000d40020318076020540341c2c030041405001240124243c044100760704145007040580e88803c45030742105e40a0038166600d0319a0704100d4007501d002d150102d0344034240110020300d90143e6050601f5540141e10750f0124121945501c0903000c107060044100340c0c4850421681080076500c07804c070502e0040120707481c01c5140c200240c2190070442c2c90305d010030760300e4004124810541d903a02449003102c200802c03100d00341e50307006485d001042c082c10f0304100340400006c0821074500c0312004180c40003022140e0349a66071800030003034800c485003940074604050000c500d60400109803500e10258035024000350381c881700001c902c14400a150741d400313280c440010010610500010080b00e0071140040341620b400d0408912200104998a041089410410074848000300f04c0400400091800052081180015001d01d00030100d020704000d140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 438340602 1250 438339352 438339389
    0x1170304082a030a02150c0c150c060129031008190c0b040302090c090105090a03050c03060615090904020a0801020f091801060507060507020709050408070b240d0804 73
    0xa203694a004110b190403a44203150380400f45510f4901d01c8000a4014a5203000054803003010000342c16111820400c07594070f1030350300c000220446e80140329980700d031200064004040c0010300442e4094040e00b844c98045860510306901919182d04201c600c40304040049141c000f4042500d030000d000003400c90340008000e048100c0e620b1028002241d4944a80b600000d02d5841c4800365000c50b50000c05801d11666181c020041c07551044103000d04005003004034a4890742c562940b103001c0c5002d48001c010418060707060519041e0058405c0f8465101d82200c40c5c0e404502000301d038200381e015034a40d10076448038400305100c104c0d40c0d08130001c90b50010820100d0a840000a0b103001141150083c4450010000d0390800f450b00303014601c006070040007448080790340fa40100307400401620460b060103030381c0e902c0942160000d96044510720800188602404100802d103908101c4001401d0300c45981800f03420303c10f0000c580014001d030507008421007480045010395000385400811040322001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 438341852 1250 438340602 438340633
    0x1b030210030e010b0f010212031504020c07080f0309090402040c0c05120a090f03080328060e0108010b092202120d0906090e010e07050c011b050a020c01030b090117030408 75
    0x40a00e90b521190301c1c082080c9124541104000c0c0608410f030050002c4400340c5c01842aaa44000d16070f40101c80e003c10480c3c01c98440d803008041d510074041c0600f00b12170030070321018142045500f1600042d801446545507070307558054259001541103400040d82a0389510030b030f842011000000d03045020314000700e050510350360700070104808582c1e2020015034a071040900440d10380d000180c84c291044c4001122007021050346101039000d188081114803d911030181684c50503000b1200084012004100000c8240100c0d0442c0b03c048030922194504180010703150a1143c5080f60440c0b980710641040d500c82c103041d003c8010454054605510000c08068400000c82c81100c000034848800002d0410280b44850b058611003007491466440b1b0b5402240c09402189410302d043d561001c40038180010a041c4021030700694440365286c41c04510060304007088200b507141414100145418079654000c8100d0644040c1070517101500b40c440310312407940c021030b00108158410003080444514 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 438343102 1250 438341852 438341861
    0x1051005030f070e0a0b03120d1b1b020918060405070509060102070303021203071b03090905150603160e030d0206060901060f0f120b0a1206050a0e06041b03021003 72
    0x4005404903a86041c00d010b1007a030714019072048401c0003043d14041281d226190b0064403a060b401022101440f81d2448154015030200c0c0460080c5070b41d45c03a80b40c5420240b0a20a2000b0b1350b10b00740b190181340c1180201c11400050300c0300903c16190760300013481e2240070745034441808001400703d40440c9010b10308581e80d12507038041c0600c200141c0000910701c0d031000031207000381c03507141e80504181e00304002c150645030405460300080c884c10a04501c80142c07941e100c400c1c160b01030303503070108a946410850340440b0009000e125101e00704140c0701c841c649520742101d81001d480207a00840c80a219401c0702c3c64021143d903a42d060180f1070041540690002e1410700034041141c02d2480307030f6070328801601ca401e40480443c0c081481142c1c500c401c01d002c0e40c4030a01c2081b07030382c9020801403550700c0022851b010703c0d00725000102e120140c01c001e020461188961141030720f40c04100400500c10020368030140100000d0000e04c13005050003404283c540361400443d4060109010455203110240240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 438344352 1250 438343102 438343109
    0xe061807090f090603140c1e060f03090c01121a0d020604082e02090d0b0402010311040803040f120f140c04050406020304020310090201140a2c03071a0909060d05010510 74
    0x6e02c0c81450702c0e0304692001c289100f902200500100040c00710004100402c00e150030303055400780d000e20081c06c1c4c4407001802903203c4c0c1103140107458644602d500161006c4502045401e80500d0101550007404202c0d0444038100300c103c0300a8081d4070148000f42652040d42c001040b00e000f51074030a14505100c040c05421031240644050b950702c5c0015501080380180051141d0151080c901e41000ca9030030580c551b0001c7c01803401050071440c036003041e800741d44240d001c2d0303020f580000f804100f0090000901000361414403012180e6001d25101c0e000800f20000019155000703c69100e01c0a9808000e4248842d0010708244074524142c00c0c080d009401c04c48042c2c2c040d000f85004569001c926200d4001e040f641611072204020180104140c240c01c100754940602591144044a1040c0000c016600350115088440d8801c512070605041100ca644004c100d201c1c041140104051000141c59030711200791121002c6c2d546010028420f850003c2c4090b140b94640414021448081d00c50318054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 438345602 1250 438344352 438344363
    0x20f130e100302011d0d061d1e0606040504060f0e06070905060309061807030b0906250c06020c07050d05060601090e09060415022104170a21061e06020105010e061807090f090603 78
    0x100b210900c034825100741440d0007030324185c020ac00082d425140c02e2b0f00c0705400c603004010000d5a003840720016800c65810303241c10f100551004041045070382d80300c284030780600750944880e07066090030040d182d5955030290040001c080c4181c0083c00c40002009684000e58000c0c6100741c0509156403816100c1c441a00c03a0058406d08000100d04a455a0101180151280c4c3d80032460280ca456280081d04006411181801040c44c0054140c1c0c80f1580026110f00841c06080d55050090026103030254561000d008100e00d00700304040c00c400030460310740c099000503c0340d10f600c048100d03100c020310510024064031800d0802c18030407004000d505603c130f0307445954034146281c040302210245000d2506e0100c0051503442c01103060301004c007608841803c080c20007081c0261681c1c0c00d484840c401c00c2110281c0d0b40a060100702c060341c240180b038018074010f4040c50150818101051b580f005040b240481c046648010070000c51003903c00c40d0042902200340c10030716465444610140c00c0600c019540c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 438346852 1250 438345602 438345613
    0x15030105120a080d0c14120f060120011b170f04050a0b010e0a0608070f0b0f0c0303071e0f0507120e09190501050402040b070213020f130e100302011d0d061d 69
    0x225540804103c805259804000901c1c5585220000c0d640c280c0c0102700300e04009507a4144040c5055202000c03500103043c0001013240000b003c0c426510090581e04030741008404900c002801c2000b42c99250002c00c12206051280d50b81d0811030b14220404000800c8079041c40000107000807601071050240103051000c0c000c555460070070660f209440d01610781c0c07082d5100d100f00482144280200742d421465500079040031803aa61890440e01300f12001c20105044240030927010440003900c1e64018468103040d41c00d0601600010960700035880000c040d89036140c2010341e00c5000d0034003e610600c0042c520761030b91902c21200321446028070300c296001403c100021a03149060b00036141034130400314015061451540030020b46130001101000360b15420854104210301040c0240460214680b90504441c5030500403804400e000b4500034030f8080f0090b0510043c2c0c2d202030b400d0f0029401c00f540404540c140070019a1624005900030401d42c40d2940b56002541400c0440a401d4407440c107558 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 438348102 1250 438346852 438346877
    0x3030e10060b03013302010605120607050406030203060111060726090c0105091201090609020f060a0e040b180a050a06080703150917031e010515030105120a080d0c 72
    0x3800d4559501419528140501c010f001514a80014240c0100d02d00c184c02c401c050030480792041140d07024a0000140d468a00c24082030a100710080d0091b62004001c10075842c01c103000400e036000340c2c015507080680000c00f1030150385c804d10000041802640590b6900e0501810152001070003891510711102030701d98440100b0241d611252250201402400d01148801c0044883e0392020540651014000c1c1d40c900e400542480342052480c40303039000190b140000e0042080c0d41d078071008cd1603c1074000f00301c0094400d502485540c406841a14082070a048200000d144a025810b2021003007246508100c40b11403540c101e54011045848108030362501d4280c600d4032030b9440e00003d0075450031102d4282c440113055001440d02801205420544850107060700c006500c2a511b070301000c0c0c3c140f524030a44240380102103005000840b88000e405070035010440541c0014840c40d0310401c034421402c0300c4000c3c14080501d600d540044030b103075078014400e10b200c001c0c080d02a42400041401c072905 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 438349352 1250 438348102 438348133
    0x5070207030308130c0f120c140d02040b0a0503150a0c0e100f0306150210060b160b040623070801080604020d1101030603020303040609030614010509040b04050f0a03030e 75
    0x3416690507a50320b1501c1d5541d1007648000540740c0600315000102c03a4400288042801022806080a400c80400d10043c40c01c080c000c401e80c0b82c00228014200480d0f000031b030fa0f20300c0c01404115a0642d001b04441032001d0002d082c000b071a0344800e400d4000d588081ca007854100c00d25512402e0200802c0194890804c8100d0b04070350000142d82c5c21450720b0b80103c034101d00460318900304a80030b140204001d03481d0191040341e000c00c1e0a185000da07008031140e0112403800c0c01084050309440c0c61560a06030b04942c2080f0a805030032010304a01880030110341807180301c2c5c101c8040b202800c0c0803d942003a640c61a40c0311990111849800905804000b05e1000342c0498075070702403500108078041800d0191905480c0e00c03160203c19040c150348100000040e1014009003000300f00c09c2d1580003c00b032031401e042c8191048004080e0b081c010800040c403466503400b00d138641007608200c03c0b00003541c5130310b0310b0ba140c00ea0180b000744552080d084828100741d416046801c0c649540425a4000030707604451 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 438350602 1250 438349352 438349363
    0x80a090201050901080c040f181d0601092a0c02030d3902090c04060210151703070f0f0c060e030a02190314060619060c1104060302090910050702 64
    0x1e00090b0204501030840d841940e5941d0011581480b85292580e9030b8012052a03409602000d43c826005180d2144203a00d485100d0070003415240f412808031042403600d840e00c0c0140507d90506981d8180c0d442c03002207440c413090710341072604c84080c412100c0d2003020303080318402d80b41203119108248000310307064420010360b40f03040c0500004500e40320580c00d1a41d02040305541c1c0b410881528038142c0e0240c1e40b01e2070850b0050005a600a50b00d0342029402401d00901000c0c8064407810400031008591160f1180404c888008901111131485040341e2420b51142c4000642400d0620000b84244400c3d6540c000c0d4251050303c0c1c04098980d20b5206a42021102e61702c0760713040d0000300c0803d0142c100b800d0b030418030701c08103e003001c4131549940e9030034035000c000d450b4108542d00243c01c202d690b0804070b40744001004140c5003004403d1a2044c02440e40070401c074020892409400050a9a03d407a00940f015550007041c600151405d19583c0790f688101034410403180e41000b0200f04090300100f035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 438351852 1250 438350602 438350621
    0x6050d0302060a1d03180a1202090105060c0f030c1501060311030a11190314070c08040611070b0d02130609050607020f120708070608010b03190504060e01051501080a 73
    0xe0000365a4181c0410b0080c100205054410384c9103032078648038144180000c101842624541542d40c0b481c95003802004216034220710003002003074411201584d15004014111001280c91035550395211302968100540b5030b02c64007942c40042030012422101055252040720391300b45114145c1ea071a0000c600740e45400044d000c8030801040410500c45042e0004e28010b40b940e101640b40c00c840311317048101d0015041180300001d0307554905520900d034080000303030410144d02d4224054021929403186038841e44c0f003050140030700044003151030300051040c2030040c45184c6580b07454001708051003001e50310100b02d884403400d6035031000c11601d00400c1f56030140c0708098403050038801182c0c284803404c203600b200607611503052461090020400c2250038050708151010300030b100d10703140001c0d12010044c1c000361051213085c0204131280c103214000c0c0300c9500021001140c10f0b21241003000041c0394105c0012840d500b454104a502c100424211148030f000303130b85152940d80c8154005007207411445 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 438353102 1250 438351852 438351857
    0x15030506130905070e1024021c02010e0319020f07080c0607030504030f1112010b030c100e0901030b011a0c0307110117010305061b0c070303320d06050d03 68
    0x400708546602564492801103202d0340840304a6030300c034000b185c2d0701d420444000c0c040c0083c1140c1800f850500502d5440100b45000d00002400781b00200030391204003800c50064001032889810000d40c0c401d4103d8000101d400e020340b40d488030b804482d01d045c5c0c60340524450151144047c10041084002480c404807600318001d0b1140300241030400049a0041c0b038141c0401c0004e000c044089480139802004451054811000302c1078990709000b1252030b015824401649080c900c0b860584011a01040200c01202e10750300345080c0c1c900640e0128503007040e8503041281d40002108000e031003202c0394103942a0000c081003040d00542c0281300d512a000700e881c603070f0b00309100308000180204498044940141080b0003854981c1640840c940001d900a8485500c404140b044080107004d03044140e549950a140c0f4181c641d4a640d0b60740d21040c07000604001100c3d086010402c8954031010749011020001c5d9003144429422040315040010122200c51500c58005224074010800000b45941034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 438354352 1250 438353102 438353119
    0x1020616050d110309070e010503070b0708300403020f0f0307080a0516050319030e030703080a020d06090e0f0a05100b0a0b0301091406090108030f030402040e0d050415030506 77
    0x20480300c540014140b20340040c0c07a68890070364094184065441102c224009101e6a0302d45640107030b01c0350b010f0380014000e40003d5030900c15501c1480072190300d240c01018032035a521a2408400c1c3c0c0b9254030001483c1c401e54240c1c5c03c90404400014180624002d6085501d0070032200c00054803150582d082500a500410100f00000c29400c080c00d169015420850f08050202341800c4d00340c0c02c41c0348200c42e1500000b940c01c0c40000c804059041692030762908208640c004040c0559078418890041d080c4000c040001e101205103030102da0302000c40610601c1f4140d640c1c04080c02401b13001c481030045004001810380c41038000146400c0380354000e8010401c00e980b0300f00540091070004403664000c20020004160440340000650080007140c1d400100300d0014000c01c503140703501a04240c841c89014004003c501d000000f601c030f554540b410715954948803480000d0060419001610b41400740d060f28403515500040a40221202071032069002121100100c0450300300f101c0065009009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 438355602 1250 438354352 438354391
    0x1603020315040e0c1f0f0504052209170a08221e02091008061005010906030b0a0f030f021203130303080405010e010f02090f0103090c06081e04051605010206 69
    0xb903000380c003029103000151100310240c4000301e60403168030300d000c5c200107001d0040a07131200d911101141b00041c561510505240c10315000410300708500400e20740710707460300c00041d00c0081983d0051000031341c0400c0081d84c8118603440e12903031350030140080c4041401c10300050a1070301444012498812030501c0c1800042059a1b803c0155498400500050411030348030340040e160103491a0040003075511340032449180018903403400740f0043c8111103c2c03918803401c00c400d9030452189002d448050070041410106a00450503c85280d03200031000950300c0c900005005440000c804000c0c001d5490200c4581805582c0f039403032160001c651428641e4001c1040820b105905580d00580f04000101e109104d1055850a443c4048000e00d90b065001a142c501483c0c5241c0755201c45100f1f00341804030b00c2c016160342c90080602d01ca48803e0103c0039001800c2c002c0d2610040389240c0c1c0c901111407070b41c00c082c1081c0e950b400c450b201c0c008031040d040360081307008d40c0002400c6103c0c0c540e0441d841c1d0b6034101c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 438356852 1250 438355602 438355609
    0xc03020415080109030503040605011d011703130e0601141e16051506090604092609150715020c03090d03020106150203030415050903030411010c080d051603020315 72
    0x10001014012161615021600b040c082c020305034440d00035900d06803203040504111b411036106074091198a14401b0141020000c0340d480c85044648400c1d001d58007072950040c0c1400e502c5143c00800c5841c40c600b40100e22260b110314154002c0c4820b9030f0302c46295410710002201da06c41c2c506980380c1c8044c000118152400900010214101f8148141103040f5050b5030f07040c544031200408060580c1c914042050380d044c012443c2d40d00c00c00803030342030015030030a440c0c0700d44503140e00c0c01c01d01034a280800e54140d4050f04a0480d4403901000e002d411070740c042491155169000b40c10b0403669441c01500b5000c003100310b07000390340c07110300703101c002d185456141c81c20005800d182500c11030a55482e03120000b089002c181211044004640296a030303450300d0f01e4000310360150003c59101c0306291509024103e00d00009580d03019510404c0e400411b030481c00180e42c1c504640400070400e00f40000c001c1d0308010250001ca00400d100641d42c00110492030065050340070444250400c85042140700d0024035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 438358102 1250 438356852 438356861
    0x90201050d0903021203040b0702010506010513030b06030f03040b0301080c040605010905061605010218010201231b070605010909030215090d050708041a03270304030b18160f120c030204 82
    0x14804e004941ca00c058800b1210096001101d0655080341c0c0d100801500f25020300031140d11290918200c0d14191840500783c2c00700030103020140c807500d98032000030450707241080107044501d9554122518dc3e0765804101d40d03241c1c000d0080c00640c0c02003051000650903e40101c4060b00c105071502401c180c10101404400e8011071000081c8020000c00400410310a1000b0719244011030762031859084d005001a0035100088403c1603044468250104075012071b0f402e85400c01e0303e400d096803078203821600c01e40c428003d40030b014201074170340030000807100466800400001c1c460707000d41d20b40207151901942160421688084aa08011180d101c0948508020300034944104c101c02e0926848040000c58442d8100803110007006c0001803106120030041d840500f040341980700000c3e00d07101ca41d05520f07405184070040c54400200e01051550401c05241940d04620500f00c1d5909038007420700601e4580b40b4170801468141601e8003290300c118000315024856080800303894100c0c5141d00703000040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 438359352 1250 438358102 438358121
    0x1050c190e030a080304031818050c070c03050c0418080904110d151403011406041e0509100605060c070509040218040f02011d060f0703140d140105010c0f0210020f0312040b0109090201050d 83
    0x1031010000d0702d0010350000b2041000e580101d00434507001c4012014001145c036801c003c1000c20086481c4e4100003141d0b0000c0350b107a10340c10b0710003166805c11610980300074003445080824641c10f10019a02c1c50741500003990890f0041d200c1c1e02c9081c601401807608882c031000c0d104540f07041c03170030010720b544c101500240200c0d8410544c4082141d20002030104483c401d80e1303c140540c02a076240022881c0038025140900401c03602145482c21240da0301c1c2c1d0700e0905100f12401450340c40300190943d034400b81281c0c80c48500701581540c518140c40c010804551310310049000c204820106102c1191013001d0300f5070354201500d114500080d0039500c40c4141c00c541003c80070005254079482d0044d0648001d819500300010003c505a4603081c01c980608005030416810019010240404281001d1032404659015203145080280031032040f42031a0880e02805000d01c40040c96040942007840c5240c4140e004458014450342c076091a90256402079102a001500501c0300c0501040f40e540400d800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 438360602 1250 438359352 438359371
    0x2103181e04051b070605150f01020601230406061101110c07140307030602040e18010209090c0705010e0708280201020a120314010603091401050c190e030a08030403181805 75
    0x1032081e00f004504403903100d600100e030310f15114400e00241d101c3d102039150020108503180f01100c050440001e5a80b001446510302c00c0324140d071000d04001c2c40b658000842c0c04084d009004554991801903c90b4882031180401ca41ca0002c1c0800086400401e0f68056914007018245070b40c54003480070004084172580c40d5050040a40000008107140700030320041008040c9008d040c0780000c2000805400702c020640744c1d0740108401d1002d5510303412103907070240d0f90710021134580c085414454010b11605144e01214440c0c04408600c1300000601000300440030803884609100c44181c82d0321412650304c0c0203004da40304420303042c0050030341041c0c80314100d02c2d45000a403001400d1118103038084282e00110110f681e0740c001c0e80c107201c41000c5d1140c0502c06000240034030304060111020034418680c2c2c0a0201000101c642d01c00f85c40b520243d5462840102115001d040720f040240c5130b6401620300f100032407000001c01e105040c5642020048808181c1c4090f50415104c01c1400640b5005200104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 438361852 1250 438360602 438360631
    0x60f050f1209070909050d050a0201020d0905011a06071203050c1201031a010e0f0a0f0e0a0c1517060d03090519181e02092103181e0405 60
    0x9580d030340380c006484200705601928866082c004009801c11031140c1010b84614107100e2007034041240000d940c0c2141c0141e03c2c0907651601e00b9502207009020b0700609180190820200c0024803030150440c49014080d01c40b800344000d006820803115202d40f8400805260b400c45400b040980294001a0300423011182203113000d070ba0a00c810303c44502600110380e074840c011110b07420400410b44042c0074006c80c07414001c041c00c2901d4601541c400c0100107040083c0c542e001c0f035010103081d030008008503541204658503054149008100404140102c2105900f0701c000441c4851142814011514107118070728000d071110700500554280503c42038040c440c0c0c840c0000340d0f0740c603075540707030000341400c0381d240f810a03030800c3c911100500115941643c1103050080014001c8901c24050300c8241c80700c100183d540b0740704000300303804070407541d608460b1340880301348900310300008401050b072541c1c140914082c01244e01c04204030b0b1045c0c0801c10070319040189c50404076084c0f0f544400d401c00c1c0885170b01c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 438363102 1250 438361852 438361867
    0x6081b100509191a07050a0221070f4401110a120635011d0304030605090a0b0402120f011505090609070c030f0c0f0b041e0507060f05 59
    0xa115243c12110010406034040c8200564503c21a20080c140c0782c400080d458440395440e025680c00d500780c000ba108964941d0b0840d4003980390048002060859016074210642e02c0003030104c0c0200a104400210f160385a400c414041180c80c14100483d00e101c0d07010b84000040c6c5800f145400310358203c842d41d0360b01e40c120304450b0302c600050003401c1003d41c3c0300100c0c119071001c10015161194000c02c810300d110b01c0d1140780b42c465010b8980000d0a50384844410090494840340501380e42d01f48003891181002d180725503410040300070000c1e20300540040c005506d404016030340e20119002c011700501c81d98008240149401d00c0000e18459090044420000000980a003104c2101001d0410b4041d02c04d010452402c01e542881d074841400c58a46d0f0080c80d2008019182c8400d906000f000c0000340401081c0d01c6001c0c0450f052070320b800054842010326030345080040404151801d0b100207032031a110480c200306200810182a070300c10081e0050610b020400d9441e00450075610b02440710900808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 438364352 1250 438363102 438363109
    0x240b06030a0c03151a1c1410080f1b130c0306091d0a0609020a080d02060a0608210a020114090604060c0513150c020d050c010306081b100509 62
    0x65008200d420030010302c2921485002c0c040321091054015140d46002d070400808144010703031840b114250240c0e5070381b4004000440d40500b07807080034084040c68200000b0441d041c1d228082d20803010b50042c440d0003920340d440d0590f80c2d0001005000250700140c81002c1c018940b0b00f50070303405080a081c50b0740d6218031185035002d03101900d00f910300190f03070790382c040022550742e0195440103c040945d800c803540110040584924030050003900040e1a030030703e0350840d1200b0583c5001030000400356071019002d40c000a446602c00e50317071000c160307041120108000c1800300d0710741c0095210030071008020541c04012032040c1c00041100c005d5540c3c40100084000c4006107440c403800408006d0541e5250900e400b41c00c441c00d84120601f0844d0522115040d10302c003020000603285d4803121030803800c0304828111100e01d001c04009400c842e60805907000c1140004491400d01000d8030180403154482d21401d550316800e100c61001420a0360810005050695140d90380c8140b51900c6480c0c0001000030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 438365602 1250 438364352 438364357
    0x601080d20030309010c0e040e03041e1527140d110d1b0b0a09090506210a020f0f0109060e04091a010f050105040b032701060603060e0a02030103240b06 67
    0x1e1344203d9460310b051071481c0b60b0201c000200020304031810000d070801410300035624080d50080c142e003e8002c9082e000a680e180300100d000709098540c03001c0842c00c8000c002d00210341030340704006480340d07030480900145032580c0e242d05442c1c0b096100e18100d070343da80c10010700000d551400d54071480307243c18400032500c3d508120820300c1e00071300d107400714010715040c007000c035212560004e01000d80270b0000e410907a5015040f43c04603210080041541d0711140002503c20702421a010014141031000e11700080c000320761407151034000c0b60035000400e044014460107045802c1c2c5980001c048807814014140600d191070007644024000007441109680d800301070f00014003030001140c421000403c00303007880c241441c01801c002c0c40e18501385458030100140d5408054013107840e4503c1c030300e005842c500d1907144441c031001d040701c001d00c0b03c0341e6114000b4008060038060311429130380d03d4000500610a5000f128122507004103068210800d68410005403030b0b0304c0401d01606900d41c80c4000581d030760b0202 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 438366852 1250 438365602 438365611
    0x9060e07030c0f060801180e0706120b1806010302070f02060409051803040b070f0201050702041b092c1e071701120c030b060103140a06090b030601080d200303 70
    0x10300c0018118180140312801652109905100540d0188800c0e580012240d0440b103070f00e003004500030522070011000c2c0c05140d4609200c0d200c0c045001808680c852444080454004401c200c10f040c1081402140245000e003075007034510007804600c05510950041228501595104040c20032503800034141ea84542c0c07000c030a803501c903c2844070041c00c100c0503400c0405542b0080d85010b00d4004020035501410030f016045600a14028080da40250101c8000a038000c0081102e407404c0380300800018200ea5140000540551001c1580c030380f601c3c0030703e8201c7c003540364007007003c40041e040c0001c043c4001c1c4484290a03005592a15440007603c07000c2c06098107480e440c1c2c22100081d91405050b405038000ea4640c1060ba440c00042881c60403d081131302d8001400001c0e69540d0001680680109100300c40140803010800c43c0c00303107a90340450181d80210b80184284511102010b03520700084c01108075035003040e070a031440315014202154065400310340120030788540e910071a0454008a5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 438368102 1250 438366852 438366881
    0x9031b0a050610030f03032007030903062d0b12060c04050306100e070f05090607050303010f0902071703090109060f0e07060302180d150c050a08010f12150906 70
    0x40c0008208003050061a81c055000900c500c502d9145440e1015010700f0702c4c03006403d06070388008070406145901c00a03032400003042c0616547d885c017480c00514420307140c0b00c10f030790aa00e00005243c600b07400b01600c42d10741c66003091600340300303e91a8200e00104072000160341c0c03080350b000503180c400d14140b12181c8500c0c48002d805031601e02d414141410100007c040070f1840d4200d1000348503102401c0303403c640008082c40d0415201c600401e0035039461082400a680c0300c0b20200e0364000304070001000b14140c441882d040442030742e69041e03e40c00c1c0c2c05102c10091555155100c0c0d000100b80b144080c0d5405040d2170000724070f450381c03521000d04aa4946100300c901c1c40d1542131072541200100803030b20007041d0924046141803100644803401001d00703410b0510481170500214140301d00211181a404100341c02000410021580035000798080b140420100350707001c00014005000504810880300109040c0310174494507a100940c6400110315071340301983e1081303404046409881b03442c0d410042070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 438369352 1250 438368102 438368113
    0x141608070b070e090c0a020703050303011512050606070807060908031009200d1e14060306090d02070324110c0111070c0302150f1813020c06010303050309031b 70
    0x2410304451070000200740105000312480340700710544a90100c1d42d8021052041d41e034031040d62001c101d0500b409503002408a21002c000070640103160005003580d9103007030302c0c1c07413501c6800034845505440b000c880040e030000e802e001c4100441d1400d402010300c50b200b20b00000e10a5a2640d0701500d9420582d03010301c610312411000d000c0c107034280c850f002110407424429803440319031503140c600e40e108003006030b5031042d121643c01c2c0b44001c000801d15925590b5034800c0c840060350b40243d46005408031142d41c03207440b47c20302040d000d42003c0350704450418594013404001d400c64035105c01500320080d0082c0c0f504070b80400d022205c0c3d00b07486140030702c00c1001c0344030b03549810302601c00e800d5500600c40580002c4d01009400c0000310388210046c00c50340d05407202400d0110480030f0403c0c900842038100c003407150014131000f9812886501e40030030b041c00c907680c034415440e521020040707004209005c2c0e001e034807140040c00801e0194001e5503029001000700e9103480c0da02151480e80c003600e1034404c010783d80320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 438370602 1250 438369352 438369367
    0x90209010b070213110c0a080d20120c07020319020901090b2422030209070914300601030c0b0a0203070b090309210607030e030406141608 61
    0x1110050042240030401c50600780c5a400085590050354402c0000540e11121034509000402c251101c80078110280d40b4100702a00701b100c600d42c48048012036441c5050a051020050a0102500c03080c111100c80d04040020b8212041d2410140040e81d000805110380030043c0e07030803c966809052680451080d100c40c40c03040c40000300c0180c124400041c28803445059980b02d00d02c211152901002021150203050006418544685000f1001684d00c03502540510f409010580302103a1003aa03503a80c00d03035180b10b02100c2e0075100e8095101c0f05038a80261003070a2a220a01402e16444540c000c14400d00c41c98400980340060340c3d2082c095000800100180141414880014440b00c041286004002c0390025202c2c071070380a0090080740101d0100f42c84402c1001a101c20040c080d0008028103180b03099130320103488144010790184610300011303960b01d110380150048841620011070415081ca2416500460b0031202c243d0a01018422750501030001410807040c5405114070350b0f46d81c0b45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 438371852 1250 438370602 438370609
    0xc010b100c0c08120901080c0421050f010504020603010e04110a090e060c0f030c0f0d050403050304050d0f0f0509011107170d030513030e030c12030a020706080630010c02010902 78
    0x1030b81e6006041a4112100c035000d14060841102c006500904c1c1c100750302d03a01c400301403d883c040c5810441c44400402d40c3d880040f501050035184407401641251804820949130509880007220f00035000201880100145800944090b4200f0301c20010041419004004215803031102c0d440a082075031074a841c00641a028090700e9008180a1030540c9441e110480c085940d20002c0c000403980c44001170300f40702145401081c0e880c5441c4c0c00c501805a030500d030600070b203e60400d480a84003406910301184140380242100f01c64486140c48018000341c6c4094262010b400608009060000710f500d40401c002c0c007480144090f014030b9103501d0b4081d1948550a181010101014041c5481d003814000341500e00ea1020740700300c2d810300c1c00031010701072a0003003810200361840741900900c2034106402c0b480004006480302c98000c1d42112040360b941c15003115407080603a5010707000824003058100c0d04155408190400001e20040a06d20032400c0d83d4a0864641c103144100507590388072141d0031480c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 438373102 1250 438371852 438371873
    0x3010f140604110c0d080709031707020a0902091f0311041d060105030c0f0306010504080312010e0a06140607110a0f08011401180e0f070303030b030c0913080c010b100c 74
    0x18483d01c6114284034080101c0342d62070140040110034007900e030000565446c403907200d550285503c101c845409a91209040240380c000a07000c0303102d20314010380420a0141d0340f00340c03012080c0080c00402c413010440340b12501c440d0129400700804d612215408034a11214005100420007541c00d003007803402e80c034001c1403a05400703040301e0b0400c0003c0007482190b003a400c0540d800c0c6041513951940d0f075212000165500e10440e404500c0f82c1c080400c1e40916041030010180c125100c0c0d503140e1203a55528040103003114550700901e0156013000c7e020745901c0c10070001503c0100c1c8541d88000c80620488005200349145520440c900c0750110001d00200c0f10a004400420b61405c0001d40701c2d504042040c7e28224440000c0507007940d440c00c1d8822000000c1100f01c02c80c22105007907504035a00d80c01d004003d0100c03200c50700d01078803410000e00080c0c00d1014903640701d162aa00554524201c556480c003040d840300c1c84581c0e040d902c1d510750900342d40c2c560955466116442d1114a00c118003440d00b20b5649 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 438374352 1250 438373102 438373121
    0x4080313090e07031101120501090203070305090c0123070f0f1401092114040611070807030222020f032d0105010504090c050409060b0406021b18040203010f140604 72
    0xc0d410b01038114418940002d003c800c1d0303940701c02c1c0d0070303200818817004984200c8660982e5080c1803c100c00041c2409540d8000e5009170300c2ca035018000c40e6515000c1c0b0742d56891078008070b0700207584501400d0300603040c6102c01c0501c01e10044a14500081c40e11540745181d404401958860070a0b00c00d1005c02016036221141e40201d02c000b0b0140c49007070744924a001c007403100d81c401040b5002801c4480c05200302020006500300c01640d60720b03036854a80040c41d610148084000342c1c40b82020101c1c00080009079842242d0f4000c01240081460b20021031143c0000d00340140c00607003c0c040046180c950101440c42100110107001d41c04990200140300a605006540401d6103400014003169a1000858090700e03130819021802040c0264116102c0c811644026056032800e44042240b0101c0c000520403140d0740d030b08036060402c1495451070010221a41c0036032000064154603000840e120306250301c11700081c000940da42002100c1030a451800103160018658441003250702d282511070482310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 438375602 1250 438374352 438374369
    0x80a0506060403080306191e0906150e0105160b0a0f0b0906060310120f03140a1d04020d020d1b020a05100f0e030c010218010f0f0807050f04080313 65
    0xa90404001041c494400d50001402507800000050241d0700c60301d40f020101c11440f05011a8160341c0c962100702140c91001403041003c0700303040011001e403240542021364402c0d81070b80000300c6941d50281c4401c1c000c5061141402000e11040461043c07120800d45000d003d02601003103480d21649980440700407010041c1c0a0740303804d0302c001464036480240c6070304c1501901c00c0f80d565115035443c4141d55440782d10088045001b000080108043c035081f40342841e1203a01e40c1810711a4904580c0f0040c092280c0c10800604040000010f140140c1c003001c10044003d8070061610803040400c4090381d00c9562007040e026120342c0070300300c0b2004075016000c500b401ea201400a0450507a181c0703441c0d414120030034001e10f803145520704500d1480c2d40070720004003450b02241e54581c0c003242028087e40040d6500c05800c0c0800a21802d5540207040c102a5044956070b4440c1e00c44034000305440c202005000345080200071301c0f170080c02c1050b05c030080028140c008000c640703400c0784032801c0508541940003102e030f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 438376852 1250 438375602 438375611
    0xc08031e01090e0a0201081b07110405060904020d08070c0b0a110f0d020a030323070f080703050705040e040312021c0b03011808070302030c0307030903021e150f07060c02010606080a 80
    0x2d540f980411841441c542c2460410915101c9554002c003695004d0003801c2c3c40c3c1400a107410801c0081c00c4502503041040d01c080c0215680e840400000e407000301d4010b1340007140003601000040701d040c010006540328070007005030341e51603038500701d0b440e0044030a0001080328001841650310042180804162104005000c0031480d000d0003515060b07c2c65000301895224120080d02c400706d09030a800e1181510080c4240e841d0802c0000c01c0a0040030007100450012030200f01c6040c42402581d11074001034541d685040e14020000d120403800420640400c17a2000c40b620950b400b60008100035140c12030b249c41c852050b40000d07001c0b41c0d00160810722030781c502859034140440307580e81903010b50f8200900310784500d13450900382e045201d1030703440c080d881c0000035055040541003100072081d280207480c000d02515480352005494442000d510781c3c009407a0502c91b204982d040014400329480e034589074240720580c0d40d00d0040c1c649188405001d83d44590050001c540d0140440e6880350407600c0601 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 438378102 1250 438376852 438376871
    0x902093a0f0c1d132103091a0601080f1b0d0e0105090609011406030a1227140303030702060c0318030c070303020114071d210c010905010f080112030c08031e0109 71
    0x718602079040309104c801c0261a03481721124003e502030001076822400100c410b12010398844048501150b07180c0c0410619000b045980102c000d1140c401c000c0c0c0c030b8440c81b8880309c2d0080b0705110f4000821460445807981541c01030100203000d010301445104000340790302e050610348542036400c11052000c900c00310703404202882d500060030340c09103900801c522600c5400e1010450700c22240d0040312000001e0502030302103440540d02c1140c1290b0b5103440c0600786180901c2050f88134402611070000680c40700b030200320390344400001150460800b070707082c68802c40c0300307000c0c1170071904285030a6450b0b400003041002817603020f0250480303403807102180e00002d240c0b072840507207104240015415400c0b04000c01a03050b403182c000c00c84160515079001e00030404100320050303607000c082c041c01e4009076098900060650142508440800142d101c1d2095a800c1c07818002c01078070039036001e504006844142c05c012418803c0114040c0107514001070103e04e403c584c2c500d0b00c4a040c1d01c0011224940543c91 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 438379352 1250 438378102 438378113
    0x4020f1801083615070507031403040305031f180905060f010612020310120809120d351905060a0e041506030503040902093a0f0c1d13 59
    0x210300d115554071000f0110541c02c81c0c0741c0c1c5004402140030b1000a1418140080304d038110000d070070607922a81d64903c10342d40000150303080340400d540041c0411010b00104240900310b03000d00f11010b80181d006d0450341d9440c46102d207c4068840300070880c075036402c1ca01d018450305211040d4010400c000011072545443e2005041a1500c01021682e0b5404804105000501550500200134582c00045401c1c1036040c10286540101c0405200340359408000b01000030102c0d0800005170b194a60700f80d4078000c2100c64081000d2440c00d51001072079021104080e080140c1c426001c0c240c1c03d4a4608034403a01100d800c2207a10141104d0310481071800c0c05c00c1102d010f803506d0360344241d0141902c00ca000580340d0000c00752400c2d4100a001e404007080c003150301d62169025004200701200c01c10305032440d00a0200790244800094000305100e40c955000c803070702100040801e14414900070301c1c039103003584600d80d00710010707000b98581544041d030031080500428115500200c0342281d50b003618889030f07a00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 438380602 1250 438379352 438379411
    0x9030c10050c161e060e01030908070b0403030204150c02030307060209010c0b0a2309030d0b0a0e10150f1713020a0905070f05070c030303020904020f180108 69
    0x1880d204041046185004900c524180d07516902901d00312400b01ca4042c80305021107086020364030010980005580c2800034030b0599004a802c10740707078100156202801100a015400425500c012041002d04002140f07550480e2040d4001e0f80c006845a0400c4080d4410804544540e0200458840601e01698021048401c0168004001a85c40201400503140c040055002404000d284c4041000d01c4546410000851441d54242c2640000e03041034140ba5070710544910070f0b09d600c1070020190034040c82d80136a80e1424010b0480d0016542c8900d0100c08400807203961400550590040140024141c45101004603504159800c4405104001c0c522944000001030090170103004c1458404024003c100c903e4028002c240125241d94981028200690300c03107001414803608810b00d144a4801d9031545984035420180052071030714120b0182d04802e1001b64010750030401c0c04206d000e020000c003a0b02480902088400707000a00240145000070034042600440c001c0f810b0840ac4107615 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 438381852 1250 438380602 438380623
    0x150207060f1211031302040c0315090f0b06191b031718030a080f01080a03080a050c0f16060f06050307090218061611100806010c0312020414090603030903 68
    0x4100c415948240140d60181c0703c0318510303c41e00c040c000240105c00d078000c5c00c200d044a00030f48041c02a0703007a2540849c1141c004034110050303011b6400007408050100c3d040030f03001c0c0c910980082403505129000418540c005600e843c0c458940c0b4803038001c0c158200031103d14400c103503030242c1c209100c56100070340030109218020142d020030703200103028504101002d1300c1c510481401c50351070343d05a040160520109884050081048070000602c02400140d41003030070340d0541e218106030711910800e0015003c0a446034024001c20700c40b4019003001030010340404030f0107001469155403e4148141100d00c00d19462442501304503060102d038800042c11012200850720059982c06015669035281c12440012a481100001d0314401002c00200307241c04c542c001d503440909484400b00704407610440b1082070000c80c480a00140980d0b025a03942d00c01c090107420a040740545000c0700b07400700d90003500001c81e042c81201844810f402d00740b254551040301540150705e00000c180020f591110f5040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 438383102 1250 438381852 438381857
    0x204120206090a091a120f0a031b0f031d0409083f10170a03030c0c0b010306021b0a02130b0d0615030311011404080921010501150207060f 61
    0x41c464041c0d1140b043c50300040105480030802405408406207503c85d41042c454407600c001024020503500203d0306540c00d002d2100100706681d059541a1038405c1c04203145907000d107111303081c400841d070005005050703940700740e83d1841c010030f01e0042c42001e8520303070024a0250707190852020001d000c1c0003c6580d001030300c88000030490010111500302080c100c90300403425214442c2080c0b080100c001043c0101001001c203c0c0882e12400c254038030340c00c0c4071417201075a80700319030480102e8001c0d4042a0703680114a045040c0c0e03009621100e68034007081e88100c41080e8001032080f01d10300100b0200807003144280241041c2c036043e8001907034403a08050560b01082c0d4901010040c1d5581b4a1010b50607940306409001e0500f40c558960726544040c8016400b05d44240c103620041c05062140b9104071121882140789500c4680325402c0e180c0001010b5030700003103d100b22892896034141c0950b4045403070400803c5642c1403141f00c4103d0348000c41d40e034065510515042c0b0030280c00c40e0a0b40c80c40480d61 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 438384352 1250 438383102 438383107
    0x1202030606240d0213050303030408070609020a1707060e150414040612050a0507050904021f1101091b09020a02060c0d1805100605030f1002030405072103120204120206 74
    0x119007054080060344401c482c194030008803902c890b01e068028000707011140c0503060b00c0d01e94441c141616444101c5d8010100281040b60800040d02da82c400d020060001d400400001c0d21119810b000b110b005e090b8441a41c403058040190710ba20032104a41520f043d110500d144121841205d100d019070300030001072081c038212031462921a90b10a00003041c040810405419440c20002d803a680d030700ba8107035041d0061607000b242078142440700c04c1c001d41e8040c1c803170101411402c0c410031003e405074410f00100031000c07000100420b4240200c0102d01e010352603a11810044280c007a100101030f51000b4502401070200414664010810760740c4403400c100d0140e0780f220b071100000002c1c02c0c8807404007140718000190005000c3c0003d075149141440d5481044101c0d280c000300340d80e40941304101d10440e440364003409250240754000e182c1051191781251013464880100c0384130f480c0a03240f05469050710040340810300d58444540c10300c10744004402c52405d828100086c281024440d000307801450700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 438385602 1250 438384352 438384379
    0x3010216030822230601050609010f02070519080c0f060313110d030906030f060509071805030307080a02120307140a1205180c0102060114040e0708010e0309010305011202030606 78
    0x403c5042403196028040d880341485907840c0070300c41415180311000010f403003049601d0a540d000201c890698800030001d5061640ea04011150a40310340c50750002c50140400008031a11914441e06070a401e0034110000c0d907041586c0f2a20708890310310500e200d20402600e860460321034408694200c2c10081e564a03941d4010308040d14940200401c06401810504025050651041c0888241d801c0749d5028042d4030190068074064030300a00030b180c1d0213031850020032052401a02502003104003d000303030744004c0e642c0c2d0010341540c102c0c24058903540c00010b00c940246038140b10300c80044035061050350030b40c10070340c600901b2000042c00d201d4100b100000c0700d0403498007400c401501000c1891061210345005060340c00300d400141c1c07800d04244604071480030a980089001c5060381c00031a500d4038407280d548200405086001340c81001401100c0004c0340a85081c050301c030b00da002d408010740e075600300d40d000101110f405a20201c40e61164902401c01a07402180203a0010001c45550400040c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 438386852 1250 438385602 438385621
    0x30e0a0305071a27030f0d0c06050105031615180e15010915120e0d0c030219110603060d02060a05070201260a15090e0c10170103030c050106030209010902070c05030102160308 77
    0x1c2c000546d001380c410303001401c0d0a02da00031885800c41d440703864240940d90744c600c249070352150580c4181e030680619881c14070802d1030380030078210103203020b2034040503c04102550300510f6a003500603250004110b01080b000380c03180e007440c40340c020003860142c005c1c41ca130000e0a0035007950075040008005006668110b411460f41140300c0350844881510305d074140c051b030040c0c414001d515044000d8000d40e044400b511814121008040303400c03030702003802200d04104104c4154002010300b40c1c000003d50b510005038035640042c0c204680305445560b03641d0081c0c000580605125102c841c02545030b00e1a0740d02ca030714070211180d04522100004904140c0050f10300d641411281c000454281c5007451010312400c0005440340185c6c4142c41d100ea405c0e41c038200450304612600c075100300071000680104002841080400c0740907000340c000060480d160713400101c24401c283d0026401903004603101302400b1035901044020301045008618005d503013902c0101d1030758210405410711001c6000281101c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 438388102 1250 438386852 438386863
    0x620091f02070f0b0702030609010203070f181707090506030316061503171210050f0d03020a051b0f120c060d09050105070203070b0a0b090f04030e0a0305071a2703 72
    0x41c1c071165203000303944130401e01006401084050744288100c0011884000043c802c4a0044405a4901c2500c0f95070000c01d48804c0e9030700711408542e009512001808071911510441301c50486009030190b18940003036002900d030080c2c4124480e410030044038045e6440d00d52910500d039480303580030400004810401140100700e62015150710b04140760504204940c0005104144003101c80c00c104d600c84100840f10911603005003a000844119640c0c02c03850424251213540b4032a00c11075805070119580c483c00c0284c804090160b04c03c12984124640c03134200360942c125042500c8100d4040c004403002940c81c1c401c50303c000d000e82d800140c45010292160440203056412a00a0000f8100721b04001d603a03610002043e00d20400070804180072218a00480d8540040284404404d40f20746a01034140324025008a0a0040d0b051468606480c5c214000740294061005080514a403015000c40308240184514144804000040061240f1a2584510701e0070580030007440c541e01c0003092800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 438389352 1250 438388102 438388109
    0xa0b0a0213080d03180804170316050607270e0702010f02270907050d050703090525170604080714030d050a0605040e0a060504020a0f030620091f0207 66
    0x19104000440d80c0c03000041d1000180e0090f1340c0420906100300613804020707050120007010864104002c2102180d24400d1091840d40d49080d80d140581d02c802c5c580c070b03264424000300e4403a0000307020016003503000b420078407130651070346140041501700b9002c000c0f144080d030042d2000741c0c03a083d010440c910b00c01d600c041c400c2e4100d12800c65071440c03941650404403450400d013120151002c88a100039050411040b07004030a40c0c2c441a04105285c003203403014110040008042680d035005010114004000e04482102c40f40f03d941c002c07200c495107820000141d50002a031045030551820f0303e0480c0040c1c007683c000e4100c0c0d40580c0702c4549113050030400c00c100c50b0b18181444046404030000b00e03268492405507240b62410007009030f41d48180300903200046400185038021010400c041007540e0031440e406071004200e01c24107038590090849800c0a13030001e40741c066803030b40c099004a0303030852090041c1c00340e8128203080607510000125409001c0021000741e020000810910760300070410a00079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 438390602 1250 438389352 438389377
    0x130308042f040606030c02121e0703050d0c03020301080c15041d0106020c090105010c2a06030209010e150a050c07050406090f05060a0f0504020901050d09030207170303090a0b0a02 79
    0x10852001814207000300041c00980b00301d103050f01c0041c60784c0c028032a1402d400f00036001381000d03e140b042841501d8000c40441d05000040540c1c148041c101c82d0000c00510340700341c03241a00e4403140c2814000300c0381c040903100145403041006003d1030304002100c1801140032580d50309000800c001d80d4025000e6a480000c0601d00d0320304100004140750303c070606230f81050342220903003010703242000426502032055502040e5954082d134080b80a0f6208004800f48a404080c9980c180309003400350039410343d000100095022a0340c140560f4084052a101002100c03280c07034188407090f017001c803032103090b00420611000150380c0c4682003003401240300500006004000e81952480c0205c040c2080d01c24140b4002e14001c005200d40c58041042e074142d80c40a034640c00303240c0c10902400b00079031003a0031090512000380503441c1c4424090240c4a0309034444c1d40a44215460078507694044a000d1566505640050042240c10540025101c030b1041c3c104402c480310b07842c1c2089040091040c0c9440316070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 438391852 1250 438390602 438390653
    0x7120809310c050f07060b120c0a080606060a0503070908060405060711010c020d4b0206010e040f1103100608120705070504090602040b0c07031a13030804 68
    0x701103404603803076100d8104041da80c4403040909200c0002c80d8801c0c042c1d00d0115405200d02c1c9800300312000079289030381c451503000603007032403410003e040d000480c80d060803950300c6000ba404a9041480c3c0304002020075000502d6181450f000080c61030040308156030800c4030100000d210280b10700741c100000c141120640d01176040c2810200d45840341203400b20081040c02c58121614003052041d1181e481c03042d8050640c21802e40400c85103034084500301003a512054100709450a41400d0100644190301951080000580000c09a0b039924085040654111100400841641800c0c0c079078041d60000c40110f2000162420070307508000d01e102d4035054820402c030100c25504a500000607103850104582d1500d0070500910014402e2880c002c0541e0030031070080006003401d0f0044c3c0c001d40e00c83d15025060a4444420a00c0f036041380910b002542c0c01050f042040c418484052481c43d00b0070203001640c1c1c50007a440002c6196000f900504211220002070b0601965110100040c030580302881d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 438393102 1250 438391852 438391879
    0xd020a03030320090906010c051c0302030a15052211030103050303040309050f03030904020c0c030d0221130b090111060c0a090b16030f020c10080906150307120809 72
    0x38000c1c01110b0309450f40420242410460f10500001c2d5800c826004000d03010942ea00b0004464003c500b0302d003100c840c070806800c5002c441c1c2210851a44102c1360741c0040c0c0700e18204c4104415504448410b406401d1a18018800c0d0744460031020714080080c0b16103100d0700003540700c2400404100c1740601401c8800310012040101c040000d6001d18000d9440900b01902c45041105000551000e0341e4180d20400c12501c240c10701e0307005400b044000300709603190700845102207404c20224806520040c0c1081790008910a180000e4640c031002d4145401d08207402c0b4049244030384200c1c01420035401c404a6400c501c0d0788600408003a80b0104402d441c00b900707200410800da5003144001402088106002184025104050b544440401c2940f0007005a20717890940320307008007640c02001c50154803c65a51900c822840300345420082d03480001c030340b40610000d410030b58090a0703012901c075801c5907500e07140d0340000c480043d00c0302001e28130000282c0b8640105c00f1712074506110b40000c0081d8010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 438394352 1250 438393102 438393107
    0x3010906050f0306060a1809230d110307021c020a060e0f24070c0b070317130f11010c020a030f0201030e060709122415050a0e0a0504020d020a0303 65
    0x480c200c40041e54020b82c15500201090b456500840b01a40c0184070b0b183d00300035550285095620b6219601e2000400341300da0388034200512021120b424503450f44856115031080100400111a940340c9000001c100010360315980745e1142500191050500c0c40007541c0003640c50801c0d0200b15030052042e48010356904011386004004104c140c0f0425200710500d00a0400941f090010320440c071040000c5407104580240903005108241d9210900110101c1d180000b000140b081c64003035219200303c00d030740300307240000448001c20090030440103184000001e00341b50102c2a0840e801506000720b44150401200c1600d21140080d5003c05507140002c148032811a40d03001181c001e81c2e040c46000c640e9143e031991034109072200e000050440208100c40c0188100b81c0e012584551104001510003406100400c1c1c148401214460350300c107140c24000c41c460245500802055455000c41c0d850200c14615802004110504285d140c20018003103595200480c0174581d401000840d03013940302d0600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 438395602 1250 438394352 438394361
    0x15041407020a020a0b0703050723030c060604060510021509030d060b0c0f0109080f0706020702040e1b091b0d060312020d1407020a15031d0c0117090309090405070b030109 75
    0x43c2c2c000d000c0d00002040018019007100c80140e050703140c0c140b0302201962492200703000f1585e8981112075000706035036000c07802d00042c00e495082c0c2006054a0500c0b504000440700c26501862048160700f02d04614150041007203a5020505e00080d491b030307945d010000342503101e40103011107003618250300865030140c502c01070324041d030b0316408580c2c4900059410b10300300c0b900c2c840042c0010000388800310140c03502200611110744075250140c00c01c046940820252090400842a01e40004010703035000e403080c40d141c0701c56150480707414640303080c036100d180d8082800300b41f59401403500241462120400350085402940d06c004020480854080001d4a40c0700000b601d03030000300d04076162aa501107040982c0c208540081c0505419032500c001010b00c0380c25101e41006164540503000101200c0f03104c0c40810b400400e016001000c0c0d6500010290180c1c1e158540c500a0080180040c0c16000015102448025102c1404030746881c10407520300550755101801422000002040c0f10145822 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 438396852 1250 438395602 438395623
    0xc13050316061d2110020c0a02120a0c0b0909070807051b010902150c0706051c051e04110f04050408031506070b191107050d0e1302030103080910020607081504140702 73
    0x658102c11444045c1009070f1140304504c448986c4103c141c1e101601d8010701d181c84645098084840044032642c811411000c5035110f0810b40e1400f188084482c2403c0d05103a80c009110300d0400705034a805003003e0100d000d18420b9490100d00e450306068a04025841124125001440e4681c04040100c035100d05902403c0c0115140c041c174030000450307a0080d002c0e5080b100e12151504030750801907050030002c1200805c400e50790124511a01169684141400d0042c0e00440d00c01e102c110700322040c096580d47c10032205014a14000810000c5802403042e40d4010794143d0300406010390040c0000d50303500030040040c015210010030321440d07132803038018170113040c029600c20b100340d030405550594607008068000d4050380009010481281c400e005c080d408900080036a1940a084000c41040b40c209800031180c000001503038048628010f440203c00011500c001c20f40381c0f5104030020302059010704100440c04040554510a58883e0002c2c01e00300a860040d0f1304615000100960340d10b120344 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 438398102 1250 438396852 438396919
    0xd090c08060f1603020409020a020a0521030f070e122b020a030305060109091a0301050606131502010f023106021207020f0402030c13050316061d 64
    0x880016000804a0928450611451966066991a88508000c8110207105820990700b008003240d8466648043d1112200907401014441c4851401c0e501d04001c5203e2086807180d00a1006041082d00702103d9100d8125954440c10361105c1c8415104000d01d1900964060703021035507034400d45400030b014561845503c4100369030410f107940c0901c2844113400c1003001030b0001184540030034003e800c400d4000e2070602d801d0480381c0d950103191003110b10321040398000c201e5a001046192034240111740d0000421200c9900c3c00c0f00c0c083d41240d401f2140e01c143c240c500c0b1001c800c1180740703001794051140c1501c070038020340d902c854000e220350b40c03110301c01c1e006591030801c2e61000f550190852440c0003958006e070002c050b029404403c50641c0d401000013241e00c002051494041c940b03480c00550b0003894400490b54a820101d0101401164940c01490080d40020f06400c0701c0310300003400303904030344060500340c01801140a0300c50010310b0403641d0390b801c501d403404002051241c001d804165400c404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 438399352 1250 438398102 438398123
    0xb031009020a0e2709010f05090c0a0302190e0112140c010207060c0f0f1212020901170612070b030106030b04050906060621010b07060e0109050a110a09020d09 70
    0x2a5180c1040b4040c100100b80041c0042e81503461500744203401400428078202d500c00b5055445450203203518044680041994654080c180ca0302003d020f06d603002002c00001e41224555030b00031401910f200d2101901c1444004845000d030403010441b9405071206e82001981f40d87c4410481111081030001296441e140080c2440c840c500840c00b800400c005a0141280324903188045030380c1c0c500080291401d0040c1040d00c1e001620000944c440c140c840c18108544d0b8a0300e04c0041c0c95031990b8140d8110403801002006401e0b80c2c0154111818485078843c0413840d1100380200b40303071011034810b2030390a00c151030021910040c080003035030482c0c0c0180c3c0c1c18065010740000b0300c81510b070151224180380c1d220307401140d03607443d280d00a803d06400c0f0300318000c003071111001104d42c0c686003070b80401540b001c0041c00500f84041800340c9845400d580000b03110200040d13545075940d8668400207031000030703d150411724940c0d40c0380e07100c0c0c02400003950070f54588507038500c1c1000405003001d0440e00c00404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 438400602 1250 438399352 438399359
    0x510050a080303040c03060c0e03150601020f0303040317070c0f03030b1e09241801180603030f12020f070b0f0105040504020303040303030b0f090705030a14011a0c030409060b0310 79
    0x880340301d1341e808400006190f01d150340e600b01401c20f074000c020500002110340784107924100000d400700c1391000040011818900c0001e0300f011502c00115000350010400c000209410130700b04e140c914181907502d04195a150001c031142020304c03100420021482903460145640341d00252124102116544010125650091800c0c0040ba00290308000950000303000c1451148040281c445400c8001040c000e0808c00541d6810a211025900c0280035005000019114504025010141404016913402c0d91006850f1802c41c0d101c05040018070841c00c92400e01036015242c508455040d0652520160701e80044804d02c219441c400140400000248c03600c1c09000d028003581c1c000d0099440c2500f540c80460180c0310f18180550044030010850f40035448484d4824400d464503545c998480c1003008141c000c3d03071801c4c02000742020960005001c0549841b81c091500080c40c0c1000f9516030402d41c0300d40c00c43c040d130b82c000f050307103450000b0000380c1e100c103900110311031040d111f200744000340c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 438401852 1250 438400602 438400619
    0xf0f03020310180f020f040f0b0f0909180f1e0304060504030b0c0f030a0e1b0a1502010e010c0509100201020a021b1804030201271205070311010510050a 67
    0x300302d4140300c15942c040c1c010071a00a01030324103610200f08070400f06014140b41c00342403d9902c4070340e01075040c0400080810081d00b04584c45001380019840c4145440c041c12440b0103d809040c019510402d2404080b0b824030800c400441d60030701c0e110080d1050504403060490325004070044094950204100412003144048201e805030744080c0c031102c0c103107411611072b004d040c07800070401459680104992501c0355503270000717940b2030a5070f517101141004190800a007462055566610102c01100d0880096602d00031110143c89055010780442d200000d01207024001c0c10700c1c1d9181c55440c281101e10816070100c005c11140d102600c003006050b0741000b0480c03c0303126001c1380500680084032180d040c1c1031030703807100c00407808020a1303a2584110004ac4100808061341d0803009130b0f41d50090a03001100080d0702d0400703858140c60b0007420075050b4403694002e00000c1004801c00600003603c40030140944000800b01040d500200000e1411610f42d0f01440b0007406514414003c0c0e1100094282 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 438403102 1250 438401852 438401857
    0x709140c0c010b030f210f2508070602040513020c060c0306040b0a12031112030105090711030313110618060706060e0103030509030111030115120204090f020301030c14030a0807050a02100f0f0302 86
    0x5080c0ca901e545841c1e156900605803614130700300d0b23081095030012400b010911030302c05400400d02644005075101c2c40c1104004c00780701d4001c10466910f00600c038900d8900004185951700c14018124180e42c1e590f100c0000e0001d0050170505548820050320118035080420002c20706580b00b900e42031104645003001c40d42c0d405006038841d5040f2020801071207907040800c100c3e41c0112890900242d001060465682550021600c0031075807000754046e4400d0221010005140c1071003960903030701c0c01c441008ca0180e44c070940c100080c01941c0004440080081d1079100100601403400d0035026940c491400501c1944003180481c0700b582032480350302c04491039008076030403141c541c810002040035041042d503200711107001d1700042c15802d101c000b80174000e500403505480310b521001130b903d605600c1c01c00c021004540080c00c0d220014400b06003151030004101e8805038103d400306480704070f2032510781d1034a03042c148000d42107620504071100603908a800c06402280903190480c0c00d01003040124100d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 438404352 1250 438403102 438403117
    0xf0801020c01140906072105041a1b04091a06041205100c091214010f0b040e01020c060403050d18030c03020d030c0905041d12070201020709140c0c010b030f21 70
    0x2904200f011443c0b440c041d6020703c7c0102145060601c1ca030540c10040001c552044030151303041813601440c5503055a0400c40a40e020059032030080c070308015002c408885010794090043e140e0350320b020318400032141100720001a00010680c41c0c3e02ca41300c44104080c15210001243c00f40704025503100003540a000c0d600c81036003556030f20a806840c00040205000400d02e040d82c42000200890701041001c0c055951004ca00c0403010800b89080030620040740d00e000301001403640705019070641494082015038006416140450300ea000500021000308445400c941401c3d072000f01110415401c610050100c40c0280c01765000440d80205c04d809543ca280b03514000260700310401d200d5441c107030b8041c03034021420031140000030200c000c501d0700d071241d60000450400f40200b240c40466a040020501504508800380f100403c2c112000c41004000341c4101c1050750003098504015500f503100340225000142217907101c051802180ea1110445450742c0c0740386095000054904882e0320458002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 438405602 1250 438404352 438404371
    0x80307290103150f1e0507020c0103090b0f10090207030201050717060916020f062e24170f010f050103020a020a1101110601060815040b030a060b010201060f0801020c0114 75
    0xc914074405000140007a4940c00049036880820f005c0e102c00c020080908034064a400050504040c0400380c504040c41034000c0c105801c000c80c800008069100254025841001c2c60300036441d08800b05070405080d41160361200d1001c907580d0709256054101c00c0c0244442e4448494003c0000032011a00901300d81d041d4100d001c0202083c90900d216030740003140f42080c816600e0707100c40d80e80181e09000007550100525031303d0040e410030040f50480c6070034030f0840f020400e024070340c5040d07000824204101d4001d80700807140012180024014903903140c551030200074005861404030040c0d204140203010b039089082c02480d0200307865010b8800c65804440a40060440c200155540030ba00321710345103218108403c000e0842608001045040d000e001e41d5290206589040d40e05041c000c0391009615200c0c508110300b00c0741070703100452091300841c1c2005000c5084d803403140c0142e003d81005d601145803d0045100052500c2066010740683c1c4075800c024812007901002640800b2425200d4286 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 438406852 1250 438405602 438405623
    0x15040603050604111306120b060117070e0d060507030f4505150708091b0928060303030b0906210c1c0605090a030f1404080307290103 59
    0x21031210784084622a100504103110445059251006c5e80c0460380030050207102022504100000f600c0c8065000200f8a001b0754010040c1e03404002d4028058440f030140710350740c080c40d401c0c1e843c2c1c4060700084d0b0b90020001d10060910440c01001441c4007448a114030b454610010b5284129000000221400c0f40d100c0481524070440b074142e000503022103003007500707107500c2c04c5e400100705118120780400d00c11103d181d0380c60002806040000020301000040c3c200c0500040403002e88112150228011707107c4940341e588000313620f440c50011344e864000c00009070403040102105904540152840713503506011b03030884c1b2414040090001c3da24103502031007220701124444242000004009000c404803054459150003242e42c5c1da03221500c0350761022002d01c00368140210b82c00394030b82025040c070040c44924219280280503564128803003040214030007050150304103020a07240034000c900156a6180601c1ca0400440741c00100c900c42c4040c400c40e06e628140e00201e1105040f650030180004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 438408102 1250 438406852 438406861
    0x1180b0d020a110d0207060809060103051905100e0619050c07080708040306060905010e09030a0e011b210807090828060e011a0d150b06040e0a05150406030506 70
    0x1a40100c1082d808210200c2002c0c644103e00700001140e0184a8010f81400b0781021402860130200604c1108a988120010000038600190720700c09589034101000d028611072400c182490700d000081c0b0310320707400c1444850384180c0108566010f04a0300b0f00f0031190130704600b4050150b8004540345281401c05100030000725403c0320080c01541c1c4a91181850325442e903449078202c98454001010b410354070710051000b0711402a1294001400c8030042d4200030f10104020208095410f55174100660621109049180980301d0701030113504c601c030f07a0704070910703400813a070003020000c0d500000640400201e105c1d44d028501e00400e031140c402c06400c0011a2042c01d824044142e1065000c0c0c003a0b20040c0c00208203030740310382c00313010414030300110341800007001c1c00c803c41d480440300c0e80c4208001204100062400911142103080c60302c0c1c040390080d4001c0c006800d60003640d10502982c071100081003c06641503000718410232025140309140c0600c2010302084800d603010040660f0310140200c0e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 438409352 1250 438408102 438408127
    0xc021b031b0f0307030804090903030c09030506060d02150c0f011407020616140313020906060f120604020c1207061505210f242202150d061401180b 65
    0x9451042d001d41110f0301c06940303130744012140e03101e80c2c0203201e100e0342d84421004041e45070080c268a0034a501d0070914070790540e280c040d2100405842103214290b000450700454130780c158041d118810000314a522031030030003003a40d201c2e0a079a181d210b0a503c0c3c0103064100c1105002658007800c0d8aa005107070300d507501201d44002d010210b680c84140a0680384444074011940001c61081e03003170341c001140d0700109106001e03003058060b08840c85640d0500820550080c2c03030341501c4913848010ae141400340c0310400401c00034400da41c010f04060040001104d403464040005298103403054804000c15201482c400c04d0118040c020f1070351040d032035a180702419200908d10030358000030340c003501c40160480650a00d800c14101400d0980202c0c0c01c600880c00140f00aa80e90007510354a03101243c581039408505100a00280248120036002000d904e40c6080c0c0103030ba040000c0d070341081125546840118260480c10703110180011217030040103480042d083c402d40c08070349101c071000b410401d28a821 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 438410602 1250 438409352 438409369
    0x6180b1306110a06092301050105030309100309021809100203040809010807110708060702160b0a08040c120b0a0501060302070b28022224050d06090c021b031b 70
    0x10b0303056108540d002008280b0b60321810030094407480f11594980c46a160f600701e80c01c000c2480c60080d901d882c00400454401004444410b031084480d10060408420140d000304103521000e9082958122003e1542644544043c0100b602100316060b522180941c2410b0744001c40340202581400d11043c03a465010300502e0b03800ca002802c000750703511001b03280c1c0c928100d00c80d40071102c02c4e88103c0034010241c1c0c06003e1124100e046080840d40d0030f003802c1ca8149548120f00c10a410491400001b506106d1144083c0c030140c66603c3c8070f0862043e0310308080f0283c0701c090f1600c0e0056440e000002900500034800ca50030503500030605145075603046480c1c44002c0a0090840844a4402501c43c0410039131008005200c0d41c2c83c60182c3e11040c900440b00c420703200b604810056141c11602c3c483d40d001c607940b603081420b880e1500c130b82e5400da580001342c090b260540c003240586007407a07118183e05030081559039450400309541080f0380c2506041643c0c400c2c0b40d50a071841e64000300e01050172070409900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 438411852 1250 438410602 438410627
    0xa0c080a052a030a03120501060327140a030507021e01080609040503160b09010e030a080c0c0a0c030506060102010b0108100b07081908010e060904030e01180b030106180b1306 77
    0x100b402c1c400449000c02c1c14807542c1d80c01100051603a05020241c4401c40c41080d0150800b8a02041a800084d1b504d05280e443c4001480007038030501106001c01c52140f80104001c81c4a00a540340c002c0140f0b0060301c140c00c03401c0201d205101807640b80c5800741c0c0340d000200b80c04105a6a000c1180c66035810310040e0f480140003600c4500040114401e1854215030180d030a6106448101803464403444031402c6685851010380395420801c1b540c5c0041d47d0002c1c140340c0107401c0411403542c420440300064a0450315440044c41400611400000d114000c14a90720651080c0c00030b000d80c11081004485080c1f04840d841800b5540400c1400100b002c2e80c042e001c13184c482c0342582d2401707848400e1850194940c0b000d074400603038154014271402c0d811020340c0b40c00c80c1d416030764031410b4145035601a1070103d01607041810005101410704c0c0d501d2035120180d0040040301c0071155a07503140c4800801c1c040e12550f4811104040c07400014401c0405001c84500e50480003122000701d080803800c40d071980c141031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 438413102 1250 438411852 438411913
    0x31060f11010204230609060f0c01091703011409240105042112080c03010909051014070e01020c03070911070507090212090f0721140a0c080a05 63
    0x1a2144803162092000340f01502000c2401c0307040c00342000760742128140c50740410340116070520030755000c0d817035040640c1e101c0000d00c0d840c1e503142d00c0d10350307000d07401014079403009000c47c0b810600c5014050300050066041e0307000c000340e02c10281c2c108014482101c0041d20b600d002010041c0ca0072803140c85400e8a03e128080500d0558523140d9a240e031462860100c5d4241384c000d8140c072000788100442280706030600b60181c14a0b1101e46045140103483d0300051142d400301c02d0b01c40143c01c0401c40e00b40a00c250220401d5020403666400311540d21856000700c503070b01c0c003250071440c2c9030000d0742c0000388a05000f20003c00500d1541d040a04020180c446291107003407400e4240141c2c000120280302400141c0b903903034401a116004060307078608480015050880680141c08031882101000c9981015104110b040d5540600c0c9001c0c56949200c4050001e000526950000000038201240b241c901c1c5000c3d1051074156a158020991129406e140c0100303994040c41ea0040c01031a0141528225014039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 438414352 1250 438413102 438413117
    0x30e040b190306020f120a0b120723060d020c0c010e01020c03060406020906160602031f1d04080f280203030106020d0e010c200103050901180b151531060f 68
    0x4418100c5c5624050300c1f61610701d500da00c8010861b003851084a01e040b2856030091440c1450310181c08000d00048650b24030300d1558840610040d15070000301c84a10999460031907403100a80314064444c0d418112030341c002104a0380702241e940c40014402c030304040080240072680c60316074030381000350b210880e03080d0801e80c14041c0c8210f4075030b2082d94040d1640541d82c09aaa0f01d401e0301c1845d02000545035405061001d581c043c81251a6078020206c030030110400c174038a40d200c6042160450103511a0880e11600018070111030805000311082d01c10b44d468103000361081041026a2203000900440006a10140002e061144a01452903158030181040c206140742034540c1c160280e00c4851320b0b400c1c241000f4002c41c039568075200e095801000d000081100d0410414071034500542c5a2001d00329081e0706000c110700c5100001902241c500092034007070307020b150405007042904940821070004150300616002050b5400b0b0408540c1d5410704010401414420156009014800e00304204001c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 438415602 1250 438414352 438414367
    0xc030a0c0c0b1b0d031512020406030b13020f0f18100509150910241107080106061b0c0b0309010912020f190c0e04050f010603030e040b190306020f 65
    0x424010310410300b0141445540b01c0301015118540500707003015008046c54028441c1e180e103a450b844205640d00311010481d1000c039070000030040c110a82000d49600200c0080c800d807400100940c1d8040c6100b0340709151003e410504100420409607009508900d400303000070b030007419421605600c02c958100c01c074151601da202146015808545030003200303017615242041d42ca0315101055000a000f18603484c941c1c108644406449100401070111070f11580b00e5110f554040c41514003461564011510350a99810b0802d000c1d180304e20404011a131840910300020640204c07140542d60050400441c03203290401030540b0741d0005081c0b94440d50307203050090005500e80d00c0c4d0340390184154020455004c0c0301070928106805680325540742d5040b00304034000038403400d00d240219440f80c503003441c0c0c0380c2c2e89041481c00c0109002d2050059441c4c4000031042507001020a52005c40940e810011480d054080c0720000c0b080955400580420748401c100140c425001881c0009290643e5400d1129 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 438416852 1250 438415602 438415619
    0x9010b09042c07060311070c30080d150812090d140d0e010f0206060d1a1003031706010c110a08011503051506090103080711060301060e03070501050c030a0c0c 70
    0x2e00d0221601290062039040107900d90501800c04003104008500346085402d50311081c815040e03115000010420032107070703101501446203004040281415201c905012407401c0f00751a40f00112000d10140380c8041240010380c4010f9060550360110000c22003540c0304039001003650171003800c036039108481004a00006018256012a421154000b003039445029000a0583c0411401490401c981d400c0030001c0c0350317400944245c01800682c0d164004003241e05140800d080c3c1c0720038040b20300d80d1001c18041903200c1c50354081d085038080d0380c4550310b070b10038601c010b4101102651001e001900e1718100e400400c0c013448408483c510005e181e82086580c4580da2070030740f0496081402c400e114030000f0008c0c41028000c0d26a6811050405041490400001a602681800060f110365000b0507002c0030464148a0240c9044005040d03584030740e99280000d01d0841009015070203409840c50001c0c50354007480c151291240c1c05406582011003038803040ba00151248016900740046e031400094208 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 438418102 1250 438416852 438416921
    0x50c01110313031803151b030b010c020d05031201151115060105031306111206040e120a03020403060f0b18040c050d05150708100f0302090402121c0e030c09010b0904 73
    0x45040421040c0c03010005d03101800c0107d48400038541880480c0c000c03682d112400d06003845d41207075010b00c1944a41416440c602030b061064820304080350001c03804c0810322940c11000f18542d941c06074801d0241c0c80281d01c40c00f458a101c0607900c88100402e1056006030702443e40134124039900140707034045844450030f42d056602c070201503000010b000d100c02d0107040300c42d07940881d099a05110b02081d80482a40c2c50281c61010b1444060102c0e040340881d11940482c1c008503007100092042181c2d04000c4002030030f02001c000e01c0340c0202d8510040b00310080f206188501e400c85c01520b030042c41e040902084028081003110700d0300a412a881d8207a090140c0d95014400950791108117103031030010347c2c000c0c01d11500314006000c0352690410050f0366116925510550546510341c0b10442064030f18903161021203074101c9038218038801d1801591007861091548412000c0303807424071861040c00700309002030150404100c41007000074041d0034240c20081c00c001b0400510340781e191198a4004000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 438419352 1250 438418102 438418133
    0x903092d040624091a0a0c0b1501081e011806180605120a05070620060403110d1d100c0b0708060405061012090c0b0703050c01110313031803 62
    0x50744052501c002d007600450030240312511401d2000200341004044c01c880d20442004909034040000c12807440b510482d00c80d40001d80c4868122380c6800e0041c101059120030500300350024450070b00040c980448141010300711829600b00d68042c1e401e002034010b20f1000441902015600c03844000340c4890700400c041207028404d0350018109051100300f0071200300c1010b1440d119440086008003281000c00c131001201d14030f007829502e24020092000c1054610017a001d80e0b40038000c10002859008103803400208500b405540b03074003400385000c0d200310740018290803100c44101d00144031400d00e0304128501d00468102180e42d16115980c0c0108000e0440362a000030f09103c05000300c50805000782e41e00000d0440b030f43c5c0d10162001c0f03801000145810342c8410b0654441003560180000442240060800c41c85a1544d503c0f180c14013904a40c421030807030980758030b00200029210f05800c207480c0103800050006d8050b1001d40c5003240c1040d15424294141c0c100b1120010002d0b03001d00a4a060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 438420602 1250 438419352 438419369
    0xd02060604050a020405130b010c020a09050601020c04020322060e1c0201060609030f03030902120f03130e07080c0a02030c0303071706191a0412030c0b0903092d0406 73
    0x214900038080c4015140058005030b14140140000c5c802581c0307040f4103021400d803c40300000c0600c1943c00490301b0340302009001e50812400c00001c1068001d0740c0145200303520030b80894030090804820b0100b02e01c02204c1780c00b170381c4a8000311216440306000d0300c0e041c42c5020741e40100c0d0100e0108900b908020b00f414601030040111b240e038402c2942c0a0040000070205404c0500440b85107455840d200b06a2400090405a681801200319650350325007d0304029650700300c503070701c0d0780800f0302907600d0744292503134640803002c4000007031100c152134078040c492281d503521030020341c45002c0603403400c0e0010420715083d40000e01906031640c40420103140f15000c55030302c522481d10020038000c0d0341107019184a00a4402c0008044000300c0000300900b10785000440c001c1404151035840224000c9400c01d21812080d842e1138000d155001c031441540b82c0c0204a00185134a40f6820700d07030703a88030380c170805074120921800c00551041030411480500140307440e90721501882800050440301d440e04414031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 438421852 1250 438420602 438420613
    0x2090a0b280e0109060608070e1309150f020705030403020402160f0c060f021504080a020102040e0f1f06140901140a08040c29090d0f150f05060913140d02 68
    0x5a034071002c11090060240040811005080607030040001e02c0003865401400420714001600d5110101c0c2d5682c004880001007103030041615100030325031074401050840c1420021480b410a0681c801c4a840c0d69209006501d028a59402c0c440a9040381c0720000c4441240b028410105d204100e61140c003074441c00182d0a11410b00328080d10341c40304811210704541c810000c0c81c4c10001c4400200e90410f070003070907681c0c85002d403807412406485103401407000400424280b02c0905180300c00c090003a5203140c012900452001d09080c02020280704480c0010008642589a03d0300c40e0000c0c06842410314224260400d800d80c10851a88030095000005082e40c00300018066609040b902a04400036240303059184080b02c3c80180c820319240802c0c000c0c00040301c0d10f190760707480c0c0400006036100000820412103401c00b00300181880100110050034001c2202c0302c0c00ca02e00c00c1d01d105038402481e003902a02c1c0d80703000122248110204503142c41c090341c4c224580c0c000400601d034842c0c031740c0d078010704 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 438423102 1250 438421852 438421859
    0xe0105011806050108160512070f2d11211e0f03071404050d05100e060903070212030d050709030b0c03040201052a0f0c010e060306091b0d020f04051c02090a0b28 71
    0x1400d0b08840d041910001d401900c0107141d403130440b502f1000d0402d00d85802d024051015005030308007281ca021903032840c0d40c0c80909a1980f1144400740880f461900014483e881011840b1701c0240f081c80d0340b01e60307000f070f081001801560189401906803a0540005800e05440e84003040852403018020342e450b50201780020303031500d03041c09000c2881104001400b100c0c00d002e514560340c0e0080300c80084c4103500c13000c00305c071444c0020410b8030401210364009000d01e0503c944050182c0781a40030594100401900041c032582ca0306003140d002c4c50b4107a64152900800c84000000b0206601d030401a082d01d4003c4107140000030001c595070b41401d0005401038100c2c020024121000c500c0b403860182c0401d2080044655480f1405640040341c281c98030901c42282c2410541d0744501229941e06510105540210100c10b1028200399001900e191800d10030021212502c214a4040298029201000900c40503090f4000c1006a60040c040441c410480c5603007902181b41411840042c0c01c0c01c2c81f040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 438424352 1250 438423102 438423107
    0x51204090617010e0d120905061807080c0307030611070b0705090f0906061b070e010b1201170c1e0604030501140f0f061c060e0105011806050108160512070f 69
    0x10140e0042d148003c0160040300c82c40076850300c20402c86402401048001040b154010350003002d4210351007800e8807103600e8200a82000c6004007240c42d0100d200b070582c080342640e0300007070500102c400107008103000f13403441c4e07140c1d4098900a032040c0410394051002000180051205034022880c0391543c1791a4a0700b0b905020303403100182080c520611404080c08459152013044500c186102c1c81d141d1f803001c0805002a2604040b0f0348114500811200001201d81c0d4220240113a5803480e40b03c7ca407240d80c0d030815244c0b000a809000c000f6500290f4080c412843d0219110746c8400d548500a42c507902e210340080d809400c282d206071416519011005011100083d070550312091488005032a81441e8000350102000102018042d401d0300c50180c0b1108000c440d243c003c682d00c000d080c42011071088155020f80744c02e210719409000d8580e15000c000d503042c012802a00c2c01030b914880103070f9521040030100d010041c46241402020080d15040749103507240940704407115200c040d0780f00101d1000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 438425602 1250 438424352 438424379
    0x1806040807080f0a0c33020c07050a03060b01020c100f0f0e0301060801020c01240e060a210203010b010e010f2a030507110108040803060918030a180f0e0c070512040906 74
    0x2500c01d1b00c0c1400b1881000a44040003001c465103003001611103402c803280c10b1400300140c21055010b204801c0c0082000050f8004268810b005e0742911049070081040c480720a011103140d1000c2100c52018a502034440c2c1304940c64000c441c5880540914102d0200f4210b80194005003440e9400081c540c100010034020b0b840e052002c034011802842603c070005030400851301619080741d1110010501301e03074a56523301d018001030280328125002c00b0401081810080a0480c0603501f007402c99000c0398001e00a513076540b10107031980e060f50b550f559030480c3e604075440c0300001c2c2c203030103040400500c0911802c0b1349074a074404c2e12540c5e07507104a4200012401e40b0f180760b50b03041104500c00c01c4001100002078a40101044d0341a4105445580086128000782c0500d40950320010030311401c4960700c0700600030481040440c4038040d40c1c89070040082c1790034a001d42d50b18860600c1c0480c1c84669042c004141d00790060081e83c260310360500041c00d00c1d40c05a40329080198407060140404090008c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 438426852 1250 438425602 438425633
    0x9030a080115020c010c0c09050a0e0105070c0506070c1a010b0703141306260f071103131203050c0d03020405040b240a090b0c010906051806040807080f0a0c 69
    0x140c55100d0814524000e51391090301102604008509403240104205141c184000d0300d81c4c44c40c2841140307420030311000107006221505c030142d0301b460041880e0900540c146003555411034081e11440c0c5d00c81c40300751001c4101500480340c142a0030100e20603080706061a038040d1002004156407031115080040010301c40980e0414a89010040d289501303030701d400c1c80d0040381d01900701003400c4030902c52201c55a5104210a403024400c10341004200551200030500c2aa00c3d42c880d0000c0380030200302c4a580c1e00403815584200c0303c1c5100e082c0440c4c1e11303460790380c50164481d10f405461304c050343c848142070880210030b8030042500410144491310740b600400c0c621550583d0001b800103007030f0390b00c0c0f1101c100d80307088010740c268001540c080d8503106d8a00d1001506071102c140ba0380f00f2404030300030b0007411506825100d2030f01d0038000c03446074001d0000c08003100c4d0b4200c00500131038540b5250181164846501280c2144040119484425040c03020b44041c01240c1c0340c03c010b43d411410310081c80a000321 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 438428102 1250 438426852 438426869
    0x501090609021908030706091401020c010606080108070e010512070b0d020909011505030a0f0f0905060402150903120f0702041d0610150c0204202107080c0c1509030a0801 75
    0x5010304c0b11400c004140d0b64030507001100403900c0309450030300e080c500209d020000815400085d061080c0f0405412400c12a0442c0e554081c081c0e80c1c401d0881e4945da0b0034014400300d80c00b581d00402c85d40c0380c0207101030744000d801ea09903002c8954921400380c040d0300c0301a03808517658000c6440f400c20300e00403011a0050103040000098501031510040a92000800b00c9100d07540c1c5a445480e024415030200c900c0180a9001300601da00c6424078681da41c0c0212401c0b407090802650580c3c0081901d0305654104802400800c0d1181d06070074900352907004801305100d014814401540940c1d04c5008000a410990001000250080341541d00b0030000810750080d040b0b0645040148494610f408101e5a9882c80d108840f0746162000401806c80d00603400d030112880c110300b040c941e00c508010b280030030124030600000110004018407901007103551502048117540052031200b922401005261082400d44074a8080c00c11a01c01c4003a0513120021143d0000c034840c186140c12070001c038050240030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 438429352 1250 438428102 438428149
    0xb0a0b01080402010e10030b030d09031b0501050418020f0708040303120e062d0c2d030601030908130602060916030b011401180b030709090b010e090c0403050109060902 74
    0xfa000a4018200c0311101c40c010301d0100c1c2803502c0540310303a026150030b10004054581080e0041c40050910155000541e0000200400d00181180e4030403100c04440b010703160141420314205001c645141141c7c01140046e40800420000c104090700406a40d4402e0f0309560301e850035800c008000c0240400a0203d191815441c441f0003040002c002da40a251590030540c10500c0144481c032061142400c007020988800c1480344404031080541103142500c2903400242520515081740b03c0f0400c841441c003d1800c01c081941548241c020160007401542018944080c14000100c2a02940e1040740140c100c4000c0c001d00110511603410840507440c0000c80309405c5444100c0c040a040c0308425100e400d1180710001a40a12403c2c00e40c0c11081e10758148150fa1100c0c00107095104a070000c00184210001240c0e607402c5228071050010107940303003030202d52007506000301c9140c0605803c81000003480f00100144090042044851081c6030103e8400824418415100c0d00d001000b4000700b0071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 438430602 1250 438429352 438429361
    0xd090507062a12120e031e030103080d0f09020d050106060e04060b0909040201021c180617190219090e09010219260106052109030f1c02070b0a0b0108 66
    0x1000c01244a80341c021034080383c60035041034192031006144628202c41400d2518144001902001506001c0f109080140c003501e4100391500d164402404020b002000c00c1c42054180600c0b6070203400000602900010124000c0c0c0015154540300c00c01166160346406040c0144c40c1d003c0465075188205980c180052414202e420366203001b0410100d0040c0580d00000b010341e0b10800036903a00e86060b2032140d500541c1c0c41c20042545001c102c40e64480000150b0004e42e0510071251603040d04104a050205615007140019101d5164914114804d80910111017404048161514078024980750508030b10715105c00b000d00024002c00106441c1d105210300f0b1035200b0b090340c180a42d03a140c3d2424640c540e00110011028035102c03100c0f03250200c4400004540c0c140c003d00144140c080340c80b801c1f450302620000c008078100d021100f00050b90002d0064800c2c070b81c11803003d0500c4220940c01c04405080340c10710007080381c00c801029030b246a100014007a11401c68031840140b01000c2c40c00f0300d0345180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 438431852 1250 438430602 438430667
    0x6060604061101020409020304050a120c0b0610090f091d010204060206070c030c050109150f06030201090506161401150e010308040e0c07120e010207050405090604080304080d09050706 81
    0x1944508410721440303082d9403449071401c0d811103003d0041010119241d04250030159542d03895000c6c210392801c01d0f9004a446070b4080c42052042030b030b21203121012135569200740401d601d40e5110003001c0c0404a5004504540610300c0d02025082e030841c000b8850741409440e080000189842c80d0b2964410482480115408150168032240c01d017488002014186400c854003281160081c00c19440c00540c882005454030b03d80c10040c1004205106130510308202e241142c829110090210354412420006414184013800425828040303891403140d031034480d548103400701c407660601a55112000800503012003a088050050040c00150540c19541c43c3c02145c4a107010340c6160070203050004201e882400b0880d100e469109150303001180c81d09201606500c2142055800342c014020040341c0380c01c0038030400d4882c5030300800604403070f01c4584801ea915840074200752400c90040000c02c56800030f0380a55540320b840b5500070000c3c2e40c80c7c034200420000386021300c00c42900c442d5003e886c100b07d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 438433102 1250 438431852 438431857
    0x29010c02031209060c0d050901031103090717150906090610030b060108040f05010c0210110f0d02070c051909050c04080c1318030302040801060605070512031f090c11060606 76
    0x500040801e60b070f5605000010000d00a401c1c1c07802c043c1c480c4011505c0940d0f031050207032940c85000c1c0ca00740403080c0036040181541c041201c6216041d401081e0802200c0f1109018141c021445030542d4601052088075012080b000c558282c02c0b644008184117100404200f1590300ca200040c01143c981d04544e100d82d0112800b5000c42d0401c40408080f13014400e1060b264800561b2107402000b6820301c0f040060f4131284c5800c04458500e02d020310503201e42000e00e00300ca10413000b08020914040034002101c009400168058809040c80c2c1004561511070389000110080b446a8940d00a490301042c00d05980300241000640c60b401e0008201000380010352142c005c500329039101e005203100c17000070020304a8522804e10851900c0528003032580507801842924038101c02030103800d403501d005031114130502d2001415070340000c652940c030743c40f0f160145070082e074030f12801211b00c02c0800640c034035041580c01c0303414505e40da5086202c1e850742110380038203110100302c054036061900400140250 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 438434352 1250 438433102 438433123
    0x4030807050906180406061103160602090406060818191e082a0601080312040c03150e010b031606030f020c03040602010b270105150d29010c0203 64
    0x85081004626140d0194041d03490307845000c0d00498a408100030710320030801e4264041400b50f0315080c404100030b84291129403252a0480c021031820444c0511075207980c03224071054a109509100903040c1c1d943d5400b500000300413550310540070b4140b081d140200100041031541032070340000071280075220140c0c010181c035604800040301561030303241c0b810726140360144024900d4100142c0003503180454014850300310210040c1030860001c281041e680c7e02003e0040140740d078410304c46244d520340007500150340284124848040c030340d40d03a40c0719543d0465104a16010030344407400b071154400244030b014221442200105100d410441e803103403142001c0d0040404050f00c82022a0845860360110340510400741d040f2590b0b20f64842c0000c1c02802e4070520b03e4881d844c0041001c5206518110004103070814500c000e40c264a0041000040c90600e4039480c40d512080c4140d8489041d14403491003681a52560340140c0d0381500513510f126054013511030f0500030011440005a01e00040300c4a42 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 438435602 1250 438434352 438434357
    0xf03050304150c051c0302070c06200127051011071509170a03060f030b090114011a0a140a0810090903020a11040e03070507060306090c02031603030221041e0b0403 72
    0x17400d40c007901c103c000e8412464080c0c561740300d958000030360320ba21154400310200e82c1c40c0303c10b82c046c2c114001b0034280c90b0460751821202040301d04200e09000b64640c040c5025200304202d890054104da1040c064030908100400c181c10042607190138801c8130b0403600070b005181901001030341020303552584080000540078190540210325903c40703174001d511800150035406801002542d0ba45406150100c0c1255100129400c03c95145906041451800d06a50a40e00c001c449000ca0b45440d07880c903005010040100850742041c11a890a030900a00e88100740e9a60b10f2140d1a0200451650f0f020130360200c48100d00d080f620801003540850000d549942c4040da2803e005a00d2000402501d85041251058040000e400082203800240d14003101c44580781844541e90300c01c1a90100c8480c81c0a810158100300701a41d2203c5003054803030300380780c86030800508103050200885500c1d100141d0f80e22580c4010004e200a100b047c07005510000d0308810203580302c15460751006114040544010103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 438436852 1250 438435602 438435643
    0xb09010f0b0d0b28020309151e0a060e01060c17030106020709110904020a051809040201171f120c050406060504121406040309030b06100503070e04060f03050304150c05 74
    0x100400b110650354201c4e508400065003840c03907031480001d5001b41c805954512808070041d0303400000800403072041849401c500000381340911300d00200800102105a050b507500000301e019402000c2c420701903c65030361940d03119422071902001e414550900112107030350520041003000d6000038900d094800714840030070708810b58410140d80d0f00812058a03881070001c40e80240956002000c3c1c02284454203080c1d2100704000244186288155800307800540c42002d100460170201c0d41031504000341040c8024044591601d040d1951a6904413000090840300c140c014452480c907054041c000481d0100030b254178000029040388103a225401e00302d0b4561204805106c400006000c03000c0c544002d482c141e1603c0c1c80d0003000800e03980812103d00e14a0008590541081804014054015192180340d034441d1041076070b0107018403203050b030702075140c0030081044440900c0250081d032060006545950500c0200362844090961010420a104c030b1007a021070b1000401440d50904040900c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 438438102 1250 438436852 438436861
    0x9020703020a1e0c090e031207020a141e1c0c030c0503040e0406050f1905090a050f011b0c050a020105090109030206030907060201113103050a0b09010f0b0d0b 70
    0x38145000032001030010b90302c404020103100001d004404200b0f100e00b40b0303a0003145d11180720000721090b42d5500c0d01c2036441846003091810a5a104540140e000d00440700d8048180d030b070344184124903d81c0c1821b580c0080c4400f8601204480c5440341102c2900003508900ca0700c601c403000b415805503140b000b0006103442020a0600440201c11081e03040816281e5441d1903c510b100804000c1d00c7c12030b0114070344000681c4103041c6000880c090403086060b00c4205450840300000f602e0082e004500d41d004000200300000c800704003154601d03800d00c0010440d0b403100c84c2c003407442c0d00c0e880c2c3d400000d002c1150070f104001100415882c0c91103034242011503d510310303100100c84001d00c0fa000203400c10030002c280400c1220001c0c0b4032040b58060b6000344141d45220f05915014051003900f4115000c1d561000c240340080e041104c1c24029a004240282660700d4481a00d0850303880340a55142203d01c2c1032066040003800340010031080041d0501400042c4400f00d0400d186c1c07030383e000e4030708122100840c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 438439352 1250 438438102 438438107
    0x80c0f041e0b030c06040620010e0706030b10030c050a0f090e01030305130501050f0403150902060304230606012115150305060d05030f0304141c180f09020703 70
    0x45020090386a125040101000a003100410310380c42030382c1c444c0c0300350160142d0307528000b01103c0540307003160303504411440c84001c000c010a07007413403490b10255250005201c40e10801c11081004021503a004100c20055200f444010b04400106400301030404154051450f0007004641a5002d28901200710190b00402103d40249540005940d44d600400010901da4484080c040884000341c2c0e03842455500d0005485910940c09480d141300420700c420000b00711740043c241d11160703082101140181482d0b0020742ca07a8004c03123045a40540c9080e628807520b08400c116209034420348000c0c00c030340c2400c000203031100303501d0b15050b540345405140341e404032402600020f00c0800c400342031414058603500c00021201001c840000064500400526103140c0702152101554004001d94504031180700010040ea10041040c4d5035801d0010b0007210402e0304000c40c80c128920000030700f541105610004201c0d0003104200c00006180b039009208615018020324110384ca15040180d6030315052070103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 438440602 1250 438439352 438439361
    0xe040f12080f090114010b1c02370c081b0a0305041401090513050603031b010b01120506130c020f0a1112120a0302090a050907030b0910080c0f04 64
    0x1400950390306102108241c004035014000c054400d1460225a10460003500f21440a40c0c001049a403441c010481c0015000040004202c1c803046400c2c03003646000d40c03170242c0e40804104818070000c0120b044490754004203403400381d103c6d41c000712000102c034840200501801e46010344101000603402d141c21601d210255a218444020348030040302c5818044c0c16604103105c0d080c07040c01c112004012542c800c10045081d141e00a1416a01c0045a406c030001000c0c010b201760380521040100300c0c0e010301030f403840d401e205000c800007103401c02d0f0304000109441010261a80c2d0030341130901380203199642450048099819000002d10a6a0391000304c0c40c4c4420290f0241580c024199502c0900900d46000c000c03105081c0d42d6500051101c003440365640d007a030041c44210b44804d100d01243c0c0780c401d07001040800001807070070041944035400104485025150302e0042582c52015180301c1c10284c0f039642d400b100c2140c40801d0b26260003c041c1d10750100303e0f4068812000c5410b502c90700e5845a10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 438441852 1250 438440602 438440633
    0x2007030207153515030f010e031603050c0703050a060b0103050112020907030230150306161e32120604020c060f18241005030102160201120608070e04 66
    0x40e1140c1c50404c8544507000c5a410344030755010b80038450b820384103000140107141081000a0003107203030240a17082d4240000190720100c041007001c200b21041013000b0080c060103140100080e02c0440c06500d030903000c480811100605050409004000a62821800444158064420f0f0701e082d61407001c214006e104100b41e41c011b000c8003440c03644811000f01030818903000d21248000d02a2114990042c41d040d10503600b652692103c40014030007401032209400603a281c0c01c20301c200424201c910340642000111010004015503685107480090104240418440b00486002c9105a1181d00c10500c5042043e050b815a060040758083e116076040f41d444c500d007036040d142c080c03c10130803c4541000c1951200301030700d086038040c07101980209000c0440309200c80c10009003242c07200324041200c0e0003062910880c18910002945403070078001460036245010002440715528030014106001b07040380000043c0c6024424860200b00042180584040030b9280910b682c0754078040103407015508 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 438443102 1250 438441852 438441947
    0x3070516061118041103220807120e100e190b030408090325050108040206070b150a0f05090f0c2206030c020102070b010308090301200703020715 64
    0x404040402c450030203081045500c44034a000000500200425900903903401d4003003003820030200300007000c45d0100404c01c694620900041005a80345c1c80c0b080c2e0416a015141d00348150f104040d02c50b44206840c1060400312850112b00442c447c0c000d0011384000c160b54040d400c503c26041c8032880c1e802c4ca1b040103000d88811b960b070f285018070342003d16801a00506000e84100401c6044203801420b00510b0004644031460f40d00e890038004451089001c0e200b80c1e00590100160004544110802d41c411100c03040704002551000d028800000100c0d8000512800141d100744000e40d1600003054011840005000c0b09480c2c0c0107004003180308100744051030f00032000e049001202618256002c9608540301000900c0511500b6400d0307203c1e83c075005080f50130322001400082d940c00058242d1034400b0740000307010440420f507480311805044c55801c43c5140401c15000700369041009001038179800c2c9500b401030300701c184054540c002c4851900c00302c5099444900510f29200440c000038038044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 438444352 1250 438443102 438443111
    0x110408030c160501091a13030206030f04140c0a141c06060501020106090603020d031d0301020a020601050f0102030c060703020a0c1a0403081b040e09070306060f0e0702010c050307051606 82
    0x808000d50b503510a60710702c0101c10402c0c000010590b019060000c100e40000c50001390f101410400480c00f81d002041005040503104404805619074002951040703942d101451504e0909081440c3c4c5800520286c1c641c903404003420700203a481c2d001c03400088a22001602094500180004080f00c1c211b00100600300c904016444c00d00601d90040d40485d0400c2e0000c0280039100c9020600b1b44403a4003019401001103142440003c1c410100c0c0020180360510b0a0403102c0c0000000b82640e004000084c01a4043e034018007541c50240c8200c00209000d00080d0b19086240b901c19444200080c10070040c1a804500c0b000c10074068807201106550000400c2543d100078016134070391280580302900041d02c1400040c4034241c0940e270100c0c48442ca0740d000c030300342071070882e05103140d000042c18010540140d420000005103640207000240100c0078003440c100d81800d910034082c8030000c244a0441e0305106148440a400200b2290004014540255030f5808026105c00b04020b82d440141a907182 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 438445602 1250 438444352 438444367
    0xb010e101a090613210b24060a0309060501080708010f020304050d14070204020403081902121e091309021e0a0b09041d0f0106090203010509181c021b0405041511040803 74
    0x8107061003145d91085001400f151540a000d043d1030034000019801c2d0300c4120039220042c503200019001c00d4a044c075001c9071500303a9540d0070050301e001781c0c0403141c640e0295105004904003802001d6130784910040031800d61805807915690f034407580c2e03d08814004581e28080c0382116071000c940032950050425907803540e1f240360200c050741c01100d003206d2080d20114000615031001c81d2108041110509450500c140d004082c01d4101c0b00c00c240c10060306040240001a444603081c0102c8036040b41d1000906480c0c0380144280030740001c09035502030500f038178040d403943c0e00e858224090398103043c0a241c03141c06400c041401844044d410704d81e0f24140c04464400e658001444001090300303240280b2040750b461441d00b0036400b0038058254441800301c0041e10005602c042a0038100d000c0d01141e120701003100482e0301c2d101e091010800160412909406494038120340d83d6090b8106903800c00140c030301900d801c1c08626100030141081c549070240300c803a483c0e0603802d4402805569042c0d1380e0f83c00c030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 438446852 1250 438445602 438445649
    0x160207090e0a02010905220b0a050301060807060206060d0807030e13050f190911101b0f1a0108031605011b0908060a1b0c0201020a0b010e101a090613 66
    0x50b5901280011080140841d0780d09000c0c1c002802c410001c0c65402503004019104d0015040446102e504400340d4000000c040c0d500740030360401040c4100c0501034681c14404000e0810400800187c00b807291000a0703030000300d0043c00c69011030707003502e0b000c400d00341440c0002e000380ca10103840591703850038081813214000d11a5055809001d028010980b0320030f80c1c211700c201760f6142d09006414161016805101030402045800c0e211003549800030302e80c4d40310301e0800d0b0380d26100503007074404002ca804140100015907019442542c2c041808406940c500390909070340e4131945502c071401080042103042080001d4218580c0712240c0e01d000b03124090b030b0800051101e9410300c01c1b1180c1c0e00c02c170f00203d00480814480d104100050410106c07018002510503201c40101120490461003501601e601081a14441c14040d11306c2100204032802d01800105031004181c00c40c0c552603646800300380c01c0e2011441225900034050b81d0090301d44040d0340401d152102c05910600058286e24007444d03070280c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 438448102 1250 438446852 438446863
    0x190614041103211e0d060303090905060f0d11120601060309061805210c07060c061a010e041518020a0224010512010e0a150e0114160207090e 62
    0x1401034048480010242c0800310000401544890420f24101301c0262005008a130410520203981115840c1003989000b84040311415070042c1c000030564041400345401074040c9a400c0502143c0c2c1c5d80400b80034400203000317000319a00003001c0c0e00c0c01804010301911a10300702c110800c140c10681d040340da03407454050054050354030101e0f40b59140c01510504540d00d50300b0130700402c2e0000000e011081c07000c0599000165032400303da0302d200040c00103040c03003c1e041101c1c60140c01b0560302c0c80300380c40c400c1c900041a241d00403c00000c04c1c1e911002108680d80c80300e01003035511012600401d10304101904c0d00d507510140e8000c1305100c402d100340d640749c5009070380050407604066400c441107250102c83e403c44a41c3c1c01840d18000e07415120040080f40340c0080e81c900d60450070800090340409484c0700343e24110005408403001c1d80c140e0005000d00c4a50311640180303031a018000c0c80882c081030a640c0340c41c4001024a0224035400e0000640c1c58407c10003e40505400b0300200700d0740390400242640c0b030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 438449352 1250 438448102 438448133
    0x9030905040f0204080c0603190204091506050a140f0c01021603090e0f0610030f050403020c0411040515070c080601030f1e0209040609020f03070b120901020c19061404 74
    0x158144425001e000c07440b40f08490444003041c0140184184100401090707900140896080340054100460240841c0c40100300905000e01c0c00511400034150746e001c1d8101603404101845410704c013110302580c01105102d4110030301000b45a072943d50001c1c00b0414043c030170559081e58130110f600141c1c6030a105819094038081c0c0c0b20b83d080c5540d108074100d0320304021540392a510f2200000300c2c1c0d0740d0070089500386003c03141d03042c041500000101c40c41c04807981103409500507407004208240900f81440354921210070350304440e1416041c44045001040c030b190300075030001000071b1100e041c000c40c1ca00320b102a0210070207807a02d03965642005540d9440b00b100503541e9090322800c1c0d4004008820038909a59030142c0310f2007441d50740d500c0d00c02c020301188000380d03002130060846400c40e6909100c045c2c0900b008414003a01c40091901d82c1109190080454009a204010f6200c400703c00181003000d0f00c0300030403508486101d134130301000079000b584403540c80390074a00d0038081080581e5030b410340d04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 438450602 1250 438449352 438449359
    0x20409020d05060a050109030605070c020d030309120504081504140d0c140606150d091205120105030c0303071b0e10031b030818010c0503030c07170c030d020d090609030905 76
    0x450325403004200c00c610591040318041f803820482000081c8154204a610020504001190380c246402040c5101c041601c1180020341d900d824904020500d41741c0380000031149402c0e81080d041c41c864981d94203d050720f149050000d0800a010004a480e610310740300019000e83c1d100358a400d40140c200c00081008880450072050a0582e0071000160701e03124603c0240a004440942238419a0a50205d460310720070a4986c00d100e004a2080301800b44440769642d00e89945080510091924940c103030444c0340302e030b082003540348001d0f50008141c034215504440c0041104e0503407100640300484962094002541c5042040684804030340f60404480c000e140480020180b01d50101004545010080002200780300955500420415041185c4c0c0c040c1002803401000d615030310b15607001205c20000d2420001000030800ca05c102c40c50762056081c43d07189050038005a603643d107034042c1500312401c050340403a070180c0d03d400341e4009100260300054104994103c0e8100181404014042c1500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 438451852 1250 438450602 438450611
    0xe1203041517100603090201030e0a03120e0610030b060a03050d050712030b010206010b0c0109021e0406060507050c010309030e09130c080c01140304080f0c0c0f061c1e020409020d 79
    0x103010006101c19031240c1e010f50042d504603410500158014900d4102c1039041554451b407400140404100428401d4001d03101e08050a10b00d10400e002d07500070700165846500803606025090181116040580b58400c1008140d0340c0c41c43e000c03c0111541ba8400360151080d5207095560070f070064005c0441a00880c00c14048095190060b000e4491034041c01d401a8012001044007a1810018110170f00241d000400e2101864000035140314180203a0382d00300381000c8020009250a11500d801001141031240c00c21031070340c0340c1944900c5441c003035034107041d102d855480400d0700ca110b941d84480002042000c00741480c26040f9404440d100040341d58510440c00843d002c000003400781003407113050f5070303c03c070802154802d0701c0190030280c801c480d586c42c203005403240040c41401404525035004020107010010301d0400c000d0340309561080b800350740c0c02c205066000c010030406410041088030042446154907629120025111243c51940d40c400304000c101105240c00078180310150344014070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 438453102 1250 438451852 438451877
    0xb0d0c03030c170901020c0907050f041418060102060f13021503060102070f1206150e011701181e05070b0a0e0f0a120b1005040f0203011d01150e12030415 68
    0x43e9110300c440d028096840090011028680540b40300d502030080c0c0340c090b00b44040d0980840d4550401e03089005188400300c00c2c803005080a083c50040d94130070213440c0100341481c0c07001039103900c400b806040103c0b00f82d400143c2510300c030000038824258042c042c0741c3d07030644150410525400c00d0320840e0040c0111000010342140f202d0780001030720040031038641408510f40e00c00e002014115100c1d02c29201480000400e1451108001e00070000903001c074081c4081d01c80c0280c00c68030810548400a6050980c070b80105640e031400424101894115890580c0c950070400e107026030a5002090600700001e620440592041e50038414000640d0114890032940041050741022801400b40b07020013440030b480800c407045026a04000b00302c200c90491303034036000414183c2d022011030005154001004000000045207001061010a010700115504010103100f2103041c110788442000f00c040c8010b4000e546847d108190381600c0d10489980715514501000034079055100900840c51000b1100b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 438454352 1250 438453102 438453143
    0xb1801032f192310120912050319021c0b010c17040503010b0103050408091c0f03030618020a091a0f0301080a06050105010c03020a1b09050403030501080c030d09090b0d0c03030c 78
    0x9500d08001441c0c00e010002c68203040300d001010750600e45d503098491381c40a010401003d030810301c41f4200c3d600d0b42d5991404041d1000c1d822243c2d18148041881000120154144d105e48440450b04924001c5004040b000048441300c138200000390025044191401e20040000d00900484505074000d004011000c001502200c41c22103014241d480b007080411018540450b52020407c0c2c04880c0414405050b1144164154072000c124086039440c02c05001108142d607000701407100f092400e601d0180d20800080c54030040c0d10903418910f074180780d010f68100074078091740c4c0e94104040b4100e403a0b41e9100003540d51074424032010f80f4413610384030000c02e5039446540300c1d010700c41c1c164000700168080c2c0c1d52035009221203011510495a800040405c0e081c80c0d070300a05008074003d85e03001c102c84d41440340603070070311a0880b00248261300103040110f8807038000c501003048407030454000541044020201e044610075000080861020050103c10590404580340b03003035010f4000d82d0100312500641 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 438455602 1250 438454352 438454409
    0x6190815060a120f020402090406080f010f05010e010b070209092a04050c120f04020301092102010c0e0109090e070503070305060f0c03060604051201140a0b1801032f19 74
    0xa813a04041d20000409401c068000708071080000d480050610b0380d80c0c41041c10300d42421003030300580e5100c0b808171300030580754041c20340034150b100b61911043d40360800061444c8109840203004242410000303103090410700103621f92821161114841402001d1800e083d0303020395011920940c9001c0200b01d0103021401907070300300301b00d55900031071a841e480140500c0c481c1c0203208a900d1340d201e01c8480b00140e013402c180d400c021251500c0552b1101000340103400e448c00a08540304015001c142190207a0b40a0300314001c580c10180c000601c410341e0303d0314606040042d0070080d05841680400000c010f800900248181030743c086483c1d42d9103c41e80186003520084d28502d40c044024002800f80d031a110101c00030325000e9078000503048551074055035684100700e58600d50300385d0b1001c000b0b1060512175803071604002c4400700041340358116a2001e90000c490082050601642803400103a41e4074030201151500c00100505000c50504110b030040310b41a0181d010002141714154221028018a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 438456852 1250 438455602 438455639
    0x15050f07050d0b030a0b010801050601080705300c0a1806020309060a260601020d1b0b071b0c0906080c03070b0f04090203160219030806190815060a 65
    0x521889485400003190103420850004201a030744118140e201d80c0c0400420b001d085c0708403a103500c0c6602d003102490840e41c000345224140020541005410f5034088101d03021248211100b0800e11199103c160800c400001a43e40c46481202800308001421001d0303d006c81141c1d641d079210785880d107800b142e00311b05440340d6000340c0c0c0203000082d001c0c030b00900640028503031803030410b5a611486010314800418030a9908002d003130302e01031050659040c00800d44040040c1804120701c070025031065a07070151a90080c001c83c0c445400f00e11040d12440c56001c8010f02e0588420410303181d800c101c0c0e03a103001032040e08a07032882d01030002541d0402254403403c80d200200603040f00c0c1d10705070610146510000d44524034440403c000708140340c0700d00c080c50081b2801c441d0465070101c0e00700003038a0082800030340140301c1c4448004400295101d60406c0d8003035003d03150808000024403003150f0a0340180c120140d24000c150040c200d603581c5251961040d482103c03481501a03640079146440091040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 438458102 1250 438456852 438456871
    0x50709080705060319180c060c020108130f02090403050310150f080603010605030316020a060c20030c0409060e0d1404050103091a0c22050607030f09090c020a1505 72
    0xd041009240020246600803444405e0403040090aa0300d101183c945444c001c0d8091141415a01888a00340f07106c4094042c0e408e00100300045030700040e00c408402008954456502000c1e00c003004092080721a1456010b8203172406030801d45400780c030642045900a915041004000800e601241c540340c40e40c80700c03034a4049603000700001c111501c101c0100200d415640312000018170f62030410003400c0c9030302800000d0300c11080c244100030484a8540c051800c2125009900e00407404150303014081c1c036140048002c0d84014400480d00b040c1030703041c041e540705140071040c5052101580095404d004224252001081044000e03100d40850441c082030000003808180401e50003030f4030180090703002b100c20b40c2d41c6218007040b03050031490446810542c12408581d21380350390a584170b113200c50301007080d0011fa4a4144404540c480c01440300c0a410000b00303000b52120b407170040f0a64005070804031010301c038001d41d100c800f81d91800d80d0721040b150307030007124140c4014024070301c01c00e4010303000b19 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 438459352 1250 438458102 438458113
    0xf0c01090312140402280816030605010b0702031905160909030e010f09120305090621070e090c09130e030910050c1c140313060b0102010506090109050c04120f0605070908 75
    0x400100c400810b40400310746c2e004d00710850110f41c000040016005100c40341c0d0014104505520b014800c0d1501a80648000320b4213100700d20050f640866407070050302d2040040c5680d0003003800d106180121110400c4000c0c003064030701140b5040a038200b1005035010b82c94104030020310b1001125415a84100c01c800034002290520115051030341080c1214043e2a0981c1800e01032800140d20354060a4540d1031007980b503500116085240d001d0592080150030070b01c0614542201203401d194000f48010740071030380002d07a5060707661a111240f22816810703400704550702501c120590b40c6d41c44458100d1140300541110321100380f18104a40483c0010000380c8940c0c41e03400340440d10181a050003100f404039000107000d0544d815405180b0400e11410b05007a0020b041c00d041c8104c40b40700c40c5a2f41164144010424581c0780d80100030f0440e0b1140a00082c2a641c0364850700c0180075a070010b4686560803000d01061000303460100f03910b580120420403076606da2040655005400f07100311074064104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 438460602 1250 438459352 438459379
    0xd1a010e0d0b130515071701030c1a0c010c0210061418060111060a0b010f1403071d04090b190b013603121e140f0c01090312140402 58
    0x80c088102d07080309038100483d9248405540c1c0b00e0401046510180d00c00b51540104075807030780d001c17044190b44558800c030352480d9411600d684410501d14003a0301110f40055409186c036010700307801c072101c100200e4003c203c1305030020b030003d489849030b0b030103120024241207012640d0302c41c994000002100003405030201c0c500c0840c5d444c14844000304454140042e507690011048014000140304009541c000070344c0d500e000d40094440290303001081c2c04c10038250440f000c2810307200200c1c0d800042e01d00b00310340700c0040d4801c0b00031806111480323360001c0c1020310724020011442c880d0b6008600348901282c0400301c0c0303d100030845014050060000e545800002c0203142249001c00d882d48800051090152096190940c1440141d20480d50420025038000900b03034008652030041c42854655001d440c024400101041a01a01c0800ac1040051030041c4901c562003101d41c03010319a40240b1030780c2543d040242c0107072800c80800907902e0030070aa072401c0060142541c0d204a50007070a00f50204603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 438461852 1250 438460602 438460613
    0x1d030d0804150219020120090915120304050319031e0c05010516080a0b150c070f06020f150c180d02030703110112050c0409200d1a010e0d 61
    0x30103070054801091000d8020034150040c00200030503031800c14040e00030740c506000282100c0101701c80070381c62059880000740c60040d010440310702ca00c2c00c4482c0c01c0c0b05d132181d4503420054581502015030144920381d11030100380010015208581e0100c05441340124032818600c41d440120000030000354a56014a4103040b000c00090240c040c1071410044560701c0e035560b0340c21240d060300c1c9031544800e084101c0b454298481481d541c06421f108040c030000d04001d004c103010b45201c299104c841000401c40c480b2080b42000300400502c402d03040708004030742c0c0c1d090203074880e1080c02520078103026501c400c501c1131802101081c001c80401d00b519140400000c0c54022032100403c04941c031100c141508000360383d040150f035000c9c501450300510540740940c0050800c0c1d40c0081c1c114000c50078001003092048003003080e03d04075626090040b036044114610a104440515015207102201240d4035600e9009980400f4401200306141008202c2c02001583c5032409881015400041c10404400281 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 438463102 1250 438461852 438461867
    0xa0b040b040e270307060f02160b06041806060f0501020307120516061e0f0c0804020d0303020c0a0b040b0c03010503030a0c0302010b0d0305091503010e0a02070c030c060f1d030d 78
    0x88100104030080004440c03d10900140c032050380ca1540d00218100341444054070507403468400466085140140d5130408000040c00084081d20381e140d01c2c0002030701502c07030390820708112100c10b000c182000b105280030380040c07805015660075150a0400400c25500010803200d00c80d801c500c4904034800b1918048400344e1004402001020100c0ca046d400a005070054400e08883e1842d11103d040d0065602c008071103100319800829418428100062030300208a02e400c20f4060b102c4024403101410250003a01c07400c062641317140b085030300c10700030702c0340100381a40200e1040f020b00c0000d490b44000000140801c0c044d481d4590020895000c456000301101d01d48544a80008038a4196000002c2c4003005000c034181e000c9032001071106910302c0e100e00c2c1c092088882d9500c160442d41071402e04048500b000381044107151740003840c1401c0c00480044000110b0f803203c142490725840b0100201451700706031180012a00c8400f0010103148048003014540314050024100d040c410001102c540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 438464352 1250 438463102 438463111
    0xc0804030203270a180e0115141206070f021b01140a02070b0301080a1511220542091315030602071e170f0c0109050105060a0b040b040e 60
    0x4400c405819043c5440700684c01d402010003004225039070010f81ca40e03200b9109a0281e40c0c4a42e450410380b90030038143c441a00301a500070010484244c20200c000c00c8031402000380980c100d1240340c04002505130312103280911007a082c1d090381c0c8400d201482c203880c0c1e2400039090030301080e800d0355420991481c420240503503c585104aa401580e5a080461079900a030454105608024030840c1800010441203a006040260804c111072407041851000d005150000b03014803030247c1d0000081ca012880c40c40070b801c2c0105801c08805012245000484982810f41c00c8100101e2004400508444200a84000042640340340c5042e00b41040300c0100c0e04000000d40c107954044868000862241e50405948584001a030724170003420907074142d5401e04103801e007581581c00c154002039010050003640d4032400c1001519580800241c1000c0d00911031003031aa0346c83d019004013441415007041d4007607035091310060946510b80c02514024031440c0a034a004450800041241c00741c1104000d0f0301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 438465602 1250 438464352 438464407
    0x1c11070303050a051201090e07080604051b010909060e060f06160303020d0e0105010e010905090615010c031106240f09150d0206070c03030906050403051c050d09080d0c0804030203 79
    0x4203101c0c04c117050210482030b04121032681da13520700f0440814080003018060140b030790042c016403900c1d540d10343e620725034072001268010f6601d41903085640200f43c90005060b5142081c0302c002d803200803003243c0c0320080700c0d002e1144880f207281303801c1803c020007144c003201d6669200302d046003181d88042d8040d601811028010759540e08200d5482c10080c4281806014009402c0c911549040081d80a80300054440022504454148841c0c1c903202540e122044000b802d0800800410342400d41d002c1c0076084840f01503000703403002c0041c4000141081400d1001e0a00e80c481a80c580d9018054080000b03580242c00240c81c8003c40c1080b46403d5034640c09002c000c042650003446580170440680164400310307410007643c042881015040003e00b0003030842c40c1f800e94103041c510f45a0030f640c1c94030341b5070450028000d4800455014862000c841c2411344007401840040741c2c40c50849032aa2007035031101944c6181000e00c010303007881203c1c40c90013544c02d030380254180103401d002d4820540c3c805509041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 438466852 1250 438465602 438465607
    0x110109080f0601080d0207050108010e0901060b0a0e10051602010e0d0c270c1202180604170c060f03041b180b030d021507030c0201020d0204081c11070303050a05 71
    0xc411000300001018040008050202c65150407100d0b4a800746041c41102503403c0000188056680229038a0440e20180c0b18440952152081603004101075049440717808400500380c400190000c8541061080c1650300c00d442c2d4a4680d0111103034042c000c50780e11640d044a42d4a000340d0f12941c1e003100d00c144010701560200c0a640da40c030a4084850f4040340752a84950070b4401602c1405040c458808141c4400303101e0102c00e05001000040484040103c0d10303404108400c980d201e0a81402d8680c401911896480f078403855038403040c0c002000c1d40c401e50710449580325481e0030100b0540f84040310582c01e203801c68541c0c0d030340d0620305102c41410f100da4503240140011802950400000f00a50001d00090510900c02c01e248c10004002541c1c0c1c10342d030060300320011300e1180c2100316520401a1400203040b41152800320302a210f4181c011180900110b4081284d050114a40159100c0c100000e10a01d0078990180c61107502c3d0f05c8205603540102d034003080401d00600007041e18002034600f403817 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 438468102 1250 438466852 438466859
    0xa09080c0109060c1d01092d0618090b0a140310020a05190206150f010e030604080c01150f09110d0f0509010c0509060412050c030d02100b010e0d110109 67
    0x1400c541c120581601c0f45603d0786804040ea0303801c03025000e40c6a0564181d461100c03400000688410403500c202c5802e4444d0320011081032280541a007400c41140104c00c0800b5a07604004046600812180300c40030000000020130780c001c1e1250700c00ca020050280b000651802e090400e11122a1b0700135034040c015030700b4461116000d440141415803013529003c0c1c654100c0b05801d504000202c040b0000e562103002800903440c1d00d11281e401114080b100d803d110220103004032601c0380441c140303980520646050104100240015002252200c0020010440c02d5000510842000c0c800c02080c100e26580500522890381c1084441803107031003009103401100e24100080307070418115640c415940b4003d025005500303003d601c1c251203652401c01d05120444001505a114a12440a03a89000050700040180511030265212001003e07103014501c0345501035200c1502110b84010580f52500e810358660083e03050726003100c0f0250080f90b43c0704c5c00741d0320500c04140c20340300c490501c1440ba0002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 438469352 1250 438468102 438468127
    0x1b0303040f06090303170702061911070501090b06091909210e0a09020901200c0402191b15051b04060e0108010f3206040611100501030b0a0908 63
    0x120010034090f507807100f05034510b00300200303038000c000c1b00c403007042c81400c040c0010164001744068101281186107003c44100c111401c00401c90f118031405a080301040741010b01c0b00660100c50030368003c111040305c5555400070070590394011200c0c030500100300c0500c00c84a607429803000c0308a620030345480d802c0d03102984245603e0500c81ca41c43e800101d1103015075000d810304900440c01000034070340950811450303100180c0a000100c2032081d01400e50503c00070600410072020220100282045548110315034000b1040f05685680b0004a030031089101c4c4c0c9a01064100c040f0b194000000e08650301103004841c000e0a006032454200c2c0d2070071000510004d0301500208010b181d662108100d2a55a80015106032416409805d41d40c628140170030124104140440000c4190b155600e100d121103410000300c500d80d6001a0340041c40402d000c2409a013003e001c021200101089484140e03840180d50180c0c1c1d400d000091401c040100441c244e40c803281c1207010385511515405040a0020002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 438470602 1250 438469352 438469379
    0x131505130204150b19050702060403060518031c051302120610120f060b13060b1b0a03020c010e0102030405060d05010609170703030f050f031e060307081b030304 71
    0xc8803400030030280000031480c1c240314102c207442d40d480032502c10518024841416000e074482c042150b1190704c40040c002c2d4442d10071030700c00580c020700701501d80742c13281400802032104452412401010100c8000700040c00000e40340840d405441e280a201c10902040015101c0600341c0f080100c80356030b0160043c0e80700b00c2c01103c6440f0035401400c0c45c0c03078201d04005182a1a60000004a000d14200700100304210a189040c80e0081000300f0703841030901c08100040d01e000c10000b00d80745082d0010030032000f00801000c403e48074441c00c5c2c1c6064100381c84e40d030312000c0c03d12000f0f01607441a80f000703801d54012102c0c0300c0034440c1401502d0402e56510046035095100d021003088455807000140505034002d50380b038000e895081d224103005071294440c1c969903045408080e0502c4200d030381c0034051320f1048040b2540098070725059912420550503501d141c4900417480811940428005111824001411821a00700c41c00802c2c3d8048401404240706031304009041e01400100808a04070414841 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 438471852 1250 438470602 438470611
    0x40621030507080d0c0f1803170a05090306010b070302121c051b0d0e21070305090a03080412030806011e0323040b040b0604020f04050603090a0203070b130902040e131505 75
    0xd4101031b10000d084000c0948140c04c0844802d0340821105201283d9000d400600345603601090590380c0c540f00d002500c00380121344a66030700d40b280b0030000c103070741c4281000f40c0301302071003502110300190505c80025003602a1002000400400f26100c08007000303103410113070700b003016114080340005001c01d0139a0158800e03506980055190582c440030102c1c1005280b800b0318040ea400309101c0010051030030184079404018081080c0401d01201a5a5103250013000310340c4040043da480303946c1e800c1000c40d4001c055098011414020002d1685c1d4040c507150940150f0003160000310f44a68a404c1e401803144d5181d00740c100100a03004222802a0806103010741e010741c01c80c06042c0b4041c581b991040304010070f5580994010f001505030750880c1410b51301665800c44102c0c0d260f0b5168005640750803403085001e5454420010006407840801c2c0007003050b210201107140b0440d40310361801080e44154440c02807031175449000142c0780d100c0350599848491054580c3c0030350301c169114840588a0507907 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 438473102 1250 438471852 438471857
    0x20f0301050a140f0132030a0c0602010f1b050a0c08070c05150c0309120a050105070906110a0206041223010b041409120d09050709020306040621030507080d0c 70
    0x80d01c4003507150344407000f503500c116844014902e541c108540884c29122140100c03400701003640341c5890b210f07445000414291405401c07207200d12040c0c117050b007200c03c0600c01c1c5000355103450703050901c2c56810b00500c200d07445664881c040c002d120110845942c1d1080c4448801c011800d034100b00040d9801d402000c00a000b11120010641413030100f20600701ca42e050300e5000c5000b007061040d4400007005980d00da55045806841c04000002d2040c1008070390000104594a003604001d500e5421540c1001070710032a507104100e070313203101c0d8200b540da01c0e1400c0007950242e400e020800240d0301304800390a11078464070320380703900c03c05401161648458101304590165116204e02c003080c1050701c00c242e60003901d10500041c07806d100c800252110651016601001400941e0000804143c1c00c51071031640d00030111a0019036440d440402900b080d00c0d491311a0741080030010f04030200b0410781b036452000c0b80503150410b1f910303038043c0c50075448154103d0b908038003402a10281070843c803d1849542c42c54 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 438474352 1250 438473102 438473111
    0x7050907021e07170613022b0b09070618090b06070c0602030d0f061805040618050715111b010c15090c0801060810020f0c07060c0303050c0f03040609020f0301050a 72
    0x140d01011391101d0507611041c164000801c110710a501c1c900c02c40307900d40d0182c541c9048a045000282180c4a65910a074400c0030101182c03010004140d080501c980307580000e075040c01d51640c4085808070120700600b01068520882072101c80d069500000c01001e005201c940380194655500c603211001da8800005600702050303201c40e1001500584e080300c2c00751103041240905000050801e90004103c1d161030300c0e600e40c001010480503a00c600f1500b660340e6030703071818107000e4a486079440c652802606034030414807581d4400c42d402000b207031900d146000040e10f800443d07204031840300c2503104c2803181001007040c000c401158103154031212030131403c030b0301081c20302d850300740a208504e15600c0081030340e00d004410400c600d008039110114a21812026030740c3d18001208040354040c41100c0c0b01640600e1400244d040d40224807840c801d4866241400706d0340d00c202017040240240143e40c910000200000340002d0081d600002c048c078401400c0b00d0517095148042030860f18110b400c4120300307681c3c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 438475602 1250 438474352 438474359
    0x2c03070506011e0902090d060f0b01110d0c020d0312060f0602190816020f1002030a1b1106030a020d0f0605010912080714030c0d020a0c05040504020307050907021e07 73
    0x10310401c2c1c0500f2203030200d481940511120142000b04620801a000398045200c041c030b40d43d821142564a0380044043c060005004161401810200340941c08100c451581a419610100d03102120003900e88504441480a4003030180c0300c2d40420701141000040020f0035110b20140c869407024001455051a04a0501c1e40180c5055095084900c480c6c0ca003544c2c4800203041c1108039070020070070848050200c00184041003071988041c40031584550012000140958000060400003207542c0d82c0c080d000c0b1100c4d1040c140e441c41c82002400003904540180d440f414024010341d00082006001460509002010740c03c9172000881103850903142e44d020465582d1121801028041424500b02c1031040d40e900e603040d505c50414000c1040d05200340b0089081c8044c001c0d90402180c15040e1054403080c407030b00035200c1d445800200c403601d50031540400c3e5814117210700392040c0c0d03000e8001c1442c5400c2c202000500d0200410480c11441401c403001c00b50700c0109a4000d441d480c2c0c0c0c1c01451550304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 438476852 1250 438475602 438475613
    0x2106050f071106160f140d05060103053102010c061a030d0906021b010c02031f061d150f0406060e040e06090709020702030312070c0b01080c0f01032c0307 68
    0x86600c4101841e90003901401004040540140004e00039070419680c031144202003611058001c03541010002e501150500c003008a41d040640301386402d0b6001c0240d6680c04651350613800044446072008140010000204c016840e945050280141820401484240d41d10025615460700300310002c0d009604a0b02d09040070810300c3c0c000c1400c2c0c2410000340c0c1c10108020354440d6012144191550552181185039019202e010441500a02680c034212074040c0300390300030a100120883ea01c0e01d40000000c400402c2407404103c0c3d5000340c0f000005407038000d501c114840245078150b502c441403031000201e40c1e455206050007815603403101070450045404201c02c4600d90103070500c8a41140c020800001e034042121800d031b0300c001c00016103642060001c00e00d1350281d2481d60b49014078000901c9045900f040002074031b41d100d0600466a0b030780f102c200781d40303461070403110356006140907403030808039030182d0448009070800b0403105082c070113040007010070505030a0300b4280c1500001182c805000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 438478102 1250 438476852 438476867
    0x3081602030c0121090c0906060f021b0d0b06150a030e1e1507030912080402101110020c0a120806091501020c0d050309032a09040c2106050f07 63
    0xaa0908152040070400030045070004c00310710b486600a56103200f0b10040050340c000c0c0364090418460100410354950102a000e03804800004015100d010545d04441e02c08205840c0130201c047c0c00f00c818022280d5031002d80080c05030449503c8030b813512050041000d198043c12040c10ba95402180c8041032115540c00c1c05400c1030700040301c5520310050546480006040c0c2d00b855002950030800d83e03a5500c0c2200107003001c0c000209441500c0700030306a5980d00107c01030249000305c400400303207100c1d0442507610302c540001c24041500300c165480e40141c2d459010b0092051041d00362441a01c0b20f50b10003000700d4101e5044000b0400030300c1400b0840c204100c1c650361004044260440305080d000002c1d41c3c17401c044c0c240e1072150030205d400d40100002401a1007140002034202c4611001407000c80b944607003c090841d4000580d0807200c1702e0351a003028040d00a5811080381c25105040c17a00000107040b002101580d03100e80884008001480c52041034031542000710341d0112810015002010403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 438479352 1250 438478102 438478123
    0x1a37020c15041d06121603210f14040f03060c090e041703070905092505040b090d060b091e010609080d0f020f190c12030903060f02040308160203 64
    0x40701c090005000f50301440303520741082500c0300c8404007196034003400216641c2107081c1d0b0000500643d0044004002c04002c05425a032082c0a940c000c0390500365101e5240a0460344800011031428404007103a00034851400e1504052903554509601c80e50400c0502070264030807070740640c0c1e41410000300d50b40b000c1c012000e01170103442c40c102d07428a80c64140c044203404c81141e1f000400040400c65146c000c0380c00c407000744400b038652110751812400c03244181c0012544406c460071205850020380384210101c80a485190079614100808042800401c49400c5030403156155500d08502c0b4a541d0700ba40603109140000f5501c040c5080c03200440f542d02c00c181c0c0610180a0140e01c10300c81c00c0c1c400705143c1c414500c039103400f90341012184412460300400c1c840003c500d001e0441030b80740c454102002c0090081c0030b52000b2410300e540e050a1920b01c41d020101a000401c5050188005070160700710385c081901c4030f00c1c00b5080588980340d02400d42e101d28500e240c41e0b0003100c6000f086050500110804 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 438480602 1250 438479352 438479389
    0xc05040516020703080d02040f08030d050a0203101205031b0303190501051e0409021e030705150a11030c0304060c031b020603060d0c15090f1a37020c 66
    0x450303074a49001e5070f507885a0100070906800440d80c61046001030f070654000300740006441140c942d0b02c0c14815100d034050100c64180a090800150784a1001e0080b41e020b0f104900001100b13500d00905900e58240c0c0c80011152400100180d10510f5000000c60100072701c058007440d601c0c00e01c01d90346a0214201c0106001d001d007031000400055807001c07501640d0b817940220000030034981c0c50000d80107184c1c80400a511003100b80c0301412582d000301a460301c0741c80c03e4048403050707512030b03080198401104807100a4800c0410091884500c55000c820407501090102d070700341101c1c0483c070f604680254001500180a04e03051a0525500060350b005003151024100c281c40e0141e0041030305031100400141c003070380e840355410041001c00d0000900815182000d8000184800c2008107400308620031241017000b10807000c03d503620b584000c51510000009010b280c440c800301c0710f49c094244240c04002e5490507144604440c1001822141c1002440d80070340500100103040010360b15803c1d04581c0c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 438481852 1250 438480602 438480631
    0x30916061707030f140a1e15140a030b07020c0a060807021c180905060301051806040b04020d051606020d020309032503020d0f02030c060306010e010f020f0a0c050405 73
    0x1041c081c001e8515004201d601c0d000c51080c11039440007004d80f0895400306409504502041304000c81580300340180220b890303000c000302811205080549100c4100c56031030856481081001000c241403000c4809400b81480070201ea40740c4840301c4003442206c00740050303003043e00c071802c880c544000400c000d0880703030402001c2c03800c4c2200300950301c0080403941c410102d0714a81c800c90301b50040700380401400750285004003450321350921601406080c2d846500940c01c0c2404501c0c0b01d000c1c014002c0344c803075045c8010a6184d40d075803100903131140c001e4810b80c3c019040c0c00c0080d01140e0144a551012032004e000c1c100c1007450020000d1070300070f01e18005400c540041c03140060541d000f00b5841d05003600c4e140850400c3d4088010111803410940c0300a5118480c00070740000c00242080b0098424001c4040c1d0301415030b107105228140c4022a6480e0025210035107001841d8001da4038420901c680344101c0b030001340c0902a00303240211601081c2c900e041481c00070000307450180030365580b0001c0d0055031403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 438483102 1250 438481852 438481877
    0x1611010915110f07092403240b090406020c0610050d030c05030f0712080108010203010303080f070c120201091103030702090f090109120e10031a0f04020c010203091606 74
    0x6035011503001d80c400c0004031080422024001c03c100c140b406111000d86541ca039840c982c02c0d000b490b0a480041c500988030581d010280001d004220441c1d40190b03100903561a0314610026070900c3d00301190700c0c80c1e07480c09040c0c61600c82e008003a102d01e02c0780c10010380e92190003c0386441c00f41d008012820401a03075106000b036440b00480e141002c2c1c1d0500f005003c1e00302d00d150090541c090b00c9000070b83c03813001240c13140c20f100c2c0948402c882d2800c29150b208150b40c80d042001d0903131100b404040e01290b103940214580c010b0900081c3d80c003210515241ca024031580e5252042604900c9103100107030f450b80d4420f41404010050048402800c40040d80f40c4055540401c681c0040144040740c4109443d000440100e020f4003d0030440d0380c0000d00310242d1245035809040343c500385403524050032001e0b0050030164002c4c403078003130742c94844041542d40d24484804c028105101070b400641154007402a01031011090000d14014160440540002c00c0c0c450030b91001180a54040c00c108000d604150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 438484352 1250 438483102 438483119
    0xd0f050f040629060708043803151005071208100e010e0f1308070302031b010504020d1403040902030a0b01030c050f071209180b030613030503010504051b16110109 72
    0x20058100351059071700d800442c1045140d40c040d41d40160414105800c0341d000c444e403c01c0c4403003454280c40300c03800c2a00c60000320b00c5106002c101c422401c804413a04040203240b61030080b8681c00005450b085103403001e1503946c0c1c00b03060b845201c071401181c43c11080c4003408625040d11000b0340350740c0b8010b0f25039600d031000690810001400200b1402d021202007603040ca0718004600d22030750004040341c0d541ea040d05d0000d54a6200c529058410400d401d032002c0c0101c01801450700079500101401021280c5449600d0941d40401c0e03a03074210b00c0304000015002040b400034502c030389d030b58441c00a030120a16002400b5202001081d6041000030801a13006180c6001030b1220700350400020107100030380490a85029040c0c0e04015a58010100900b40c102d8164000c88100617042c1e0648050351210b104105001d00d84d8840203020540a00061086003807640c881544401c03480c07a0000580c0312079104403501e030300942d40c169404c81400b03e81401c0c0b2071b0f0304200e400208800e11785048154030b0075210 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 438485602 1250 438484352 438484421
    0xe01200403021306030506010b0c0723120c03010911100f050d02090a0b030a0507200706120912050d0b06090d060b040914010e120708030105060d0f050f0406 69
    0xa10843c1e8a07490a00400706a07032000014641c40b104445840d61502458900c0d1b07084190f9980f024402c103030f80410700143d00d1a500e401015480f00110516840030701b04403c4090062820f1150f120340d070322880060f9001d000c1c100c1124042c81c00f61030f00c034510009120903901658105c60a010341881c24000d2280e101c130407501040303071030200141c40300401000207060b0541c0c2e601c02125800044148090004250301141c0251001e44503100340254541c001351b0202c0c3d10004801705500038140030004180104140c6541d6004000300049400b180d603610044610346170120310001e400440c180000640b184201011140211819070910100ca030001d41180c0c0341141c010003ca07101c0c52904541d0701c2d113401800156078001c080c0150101075128060091a0103145040c1c14402c00442c10f0340b80001e40b04490b0303256008030480340756a0800b402d114282d44411802c0581035650216141900c030a1b11503103026040c1c81c0d05000103400c150401601745c400420881d801c4800030f60400000d006885003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 438486852 1250 438485602 438485609
    0xe040f0c050316021207030e031e1b040b09040f0b01080c0a170309130f06090504020603060907050c150a0501080118020415050913030f080103050604020913060f0e012004 75
    0x3041c400d580c1a50f00b0480c10894100f42d0705248940114440007010740044087d5240d000c06c0e42150300035030540903d0070f00a074040c0050581034029014140540c0c1500021018100014101003940c24040d40490303502d800c01c480503110200882158810824425042801404014000c1241c6001000055200007181c810140c0d06403500f600c601c44a00e05000f030f00c40c0100000c10070040c4641c0e2094070700250074261100140c2c1d42c13410300082020092403007018026a00034100c0790456580301c0a01c103490303c010f801d42c801e0000a00100c1d4800c0010400b50760000d551a1b1050413a00700801740100303442060b0003001d0070b64104103030052039440d020418030145804442c0441d40b6001c01c400000c20807001e8110a1f00050b102e000c01c10f2780c103032031698054424030a59035100b80380a040002c954100c5c003808003c3c1107800c40d202003005880d040c0d0034950030500143d020082c1d06c0480da108412241c8003c004003d603a100c4c200c58460507028401c92084540740b485003080400c1080f1f00c080180319502 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 438488102 1250 438486852 438486871
    0x603020318160906060f05070807050a080d020a08060603041218050307060315050105030c040e07030b09040b04020a090e07060c050109080301031a16080112110306070e040f0c0503 79
    0x3880450541c1c24121030090510a842040842e1400ca0700c503003005001d00c908a50500070005a00ca115040c3ea405445869854509001c101c0d40d40d40321a51103500141d0b05031180144060111304000001e00100f10641c10060365007124000203403481c0c000030030907441960180100b00218030740d086195500714180c60000100b06010140d10400b060507004140c25204011002c61806d0701603100107412314a0b4807007210707000da9800c0110351910040700d070782880280c2484208031025012080c1074001200e810085513510400010403440e010880d001e4a06040240600041d07050020071000941070320001402810080d41646540e0101d07841090104800800d2110901400398808515140e1041c40d559507941e482c200b82505030846130f00c0700480128038000c2581c00000d100c42a42200d01034844040c680e01c0e04083c5c0241c0b40802c40c040d02c0b40a800645007205130b400f8007400c0d11a01c138545903040e1101104050000301c403d0230240300c203d030780340584d580541600070058036449043c88 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 438489208 1106 438488102 438488107
    0x2010e0615010e060c0102120c0403140604030f0f18060305240d030507020f120d17040c03020609032103041202030702010909050604060503030c0f07050a0f060302 72
    0x4078541d03404190340d080e10080e00e050450180c504100301800046c2800c400c024000f01d101c40071910120fa8010004040c4100128040010a410300d0302000300224a065078001c0e0980c004410100240840510480d218910950703014004a089080040116680c0c0310060040c5c2400d9490700400c1240c1c100e014203404091030074040d00d07500145410000401750b01d05940903400b01c60145d030080040482c3e40211b03118203210090790b090401c010004400302c040010300c0c40000240b03001801c40c84105000119a030400c2030400e49404403102981d60790407900007490003010a5206603202e51401740d15002040c09009140b0681c05a0108644050014009c0b42c9a120310600280420284d2809000d1512541d021541c400006080020340548039000680b13550401120011942d000d000100401103040c00084000c0509440d0380c203801d0700f05107505404003140c0c0500020907602 = true := by decide +kernel

theorem cover : BRFrame.Cov 438309352 438489208 := by
  have h0 := BRFrame.cov_init 438309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 438309352 ≤ n) (h2 : n < 438489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
