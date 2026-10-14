-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2298
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:23.715468+00:00
-- url     : https://prove2.me/submissions/3f7b526b-9690-47e8-a997-f0bda9a2440d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 413129496 ≤ n < 413309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 413130746 1250 413129496 413129503
    0x1e110702010807110a08090405070203131203030603060903081803031501120b030f031b1b09040611040f0612140103031d031606030507020f06061e100504051e0d0209040201020a05 79
    0x881c41410a00e44d81d0b82d20300c080c401030349da0280842082d0b51041c803a40c402a024001c1000076100c040900e81e1549406003400c902801166001030609440e101d0083c0034164484c0c06180b1402c40740c0561082da446040c6500e583e44401c4071001c500c08106042c24a0940c402d049421840954180102d16803c2000000b410000c030b135010900b066000003070060040b400e01d00e00800c0740740400301a01d0101da90001e03e0080c6040300c80300900c244d030340d040010208540c0754060b9001018a0041d2512503450764510341c82d0b441c80340103842c0814141440881c00074107500844101542076041110145d1940d94160766040307c41880c2c0c4154508000c250525403000c100510811030480b041c074210324503000001c6c0890301c1c060082e030110f411252160300c03200d00000d0131640241c4281c07449020400d0211901c405c8100440540f80d11104036040d40340c81c0e036848800341054803003c4519004040c1368220480c14020791464290700580c1404010004d0301c1e00c214000c3e400780c018016102204400ea80e114103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 413131996 1250 413130746 413130763
    0x4060e1f0509010f0809030d0507051306050a14160f0f080a080403030506060705061605040306060b310303030c050906160b01090207150b040608030703031e11070201080711 76
    0x510302255160080d84c3c020040b40032445642080592824100c907110303201d10910384403800194603200400c1d00c2510170380846143e241c0d203141d6407440716100c0e20010050341c81895442c002407160040150f2154100303089a609442e80d035080402104507980b0f59078100300040083c4c401c1800780c001c010225069400070043c070030f920768603e0050300d018a0054102c031405810540142400d224110000e50b001801a8211070050440076002000b40c1045496100300c0c1c100410032414404002248445503001d0080c903440464040007480c3d400380c1c0490403561121444511000110082020078000d1303119001c00140340c90120702d0110b01d0b10110715551302110441410000c443c0c1c0c2d640921074845003841c0540181c04040d40741031510348421802d000c9000740802c0140e543e0a943c1c015994640c4240300505801059135100c601c00d0070054002d0803052020980d02c0e680e0222480b01c6a01407044101d90401000c0203828520f264004540b1480024500024001000f12401d400c03a000c000d21103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 413133246 1250 413131996 413132059
    0x1050415090905010e040b0402010c020f1009080f01020306150903010204030c0e071413050f030c180906060f130f060e0a0606110c03060105090405120a1d0f0604060e 73
    0x403107600d0b00d100c0e01c08680b016409410300c000d00ca000e002c00100441e04060b005602481e100c03160528a00009052180c95a1000d0f480030b4019444503000e0380000c0030100315080c16003626068039034615810b09034401200c449501040780741001405101940150101c0c1d0b0003d400181450340303d82d181a001e41894218920850600081243e2107600035000d402c00d0950001140c103000181c034051304100c820303010b240d01c50194590781601644003009002d80c5070b14001c3c40714600f54202410000c9076007050b207001146004140010f4014200304217078142100020f4a03007030100241010043c001c1084c89003e075421902c50500117081c804400580b4018138803900c0010741280b0302040039101d811010b05155041d04082c3c0b2602c41c595001c56000e044030000c0d105d2061996452030018100b040e883c00190013540042a50100b81307034044020500510030301c01c0d05190140100400c8941c05a912070795500c801d080000b401400c0c42411030181c5040040c11500200220102400c00c0071440c0e512903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 413134496 1250 413133246 413133257
    0x7081e191823150a0b0a06081905061309030207260d0c030c0c03050d090603050405101a0306090d08011d0c07020a151709070b090f01050415 62
    0x402440c5541d21441d0300100700548a0008a48142d035800854080c940c080199240d07a2100c00c00d4082c414400610386150518840c5030720301d08116010002d1003540e0100703005c1c0300f00c008041005d80c0120f20150107007041c2051045046258202c003006041c0040003150003548144100410706828020300003058843d40140150500700344681c0c00c0c07110010080d40051403c004110841840030a414110b8a81ca20303113070380f480085040580340c000481070000c0c030308100e0313400000c14480b0100d2400b40f0000c1076500c5005803a0b5130301044003955410b440c06020340c0c111136401011154554802840c01c1310581c054080046d105000a0911500312410764041c0c001d00d61103202103900c04000340c09400a80303a070982d0001e60b40344e0048409001402816500c1002815209560364241c654004098400c154010841b540d4001042c03216010440006a811400420101000844d80c10700344c80300d01c1d9aa0b8185500d01c020418100e076030520f039506101e8100030218103240301c5441a4507540e51910744 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 413135746 1250 413134496 413134531
    0x1b01030b121b031603060209010309150b090703021c0528020c1006060f2a05030d0c02190312020c19050d2a02040b03100e01051008030307081e 63
    0x422819035800500da202c4d8101300d5441002c000703000e141c2c8080d00d81110f00183c031519a000160300504a01c407010707103403035103280b40c000c0845030640014030129000d07110280181c8070040180c0a074040c07071041e401d1500300749140c510b411a80703500031540704201007011b41a02c86d5031202400c110b82c0b00722564035650740001d52140551001c2040c4000c419551908002e99440c101001389060000c54040c420840c050301e207055044440285c0101814014891184010341c41c03601d80e0380c0740e0100c2c80b030f00900c5041890031046140041808a805100b1200c0c5820314055540e0403180d18038010f005201095007408070805440040203441ca40d102e101800d40d904030303114101189401c828405a20400c00708441005100d4100514903161006000b581e088912076840002e0151403046c0d9040c0d0584998024200700d442c25400090b140d00800c0f00800103521014040f251101b01805101d82c203610420104001e540f1070301c0440d40c0f0010078600c0b980b121002071040c0081e50340603180051b221482408 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 413136996 1250 413135746 413135773
    0xf042004030c05060405030d0f03020706020a0c0201080708042d06020a02010c090b1903230f1b09030a0f0302190305030103020103141306020a05131d1006021b01030b12 74
    0x2604050441201c0c1c0d05c5c03c081c68440001e0f92410110400c004002120001d01d034030501a030161040c0c103500c42c0056447c0c00e418035008001d00380ca5207090b80014251004903421a005048050007141c1010101e42041c4482c003d81c07041c8036081384140f0b528000101e20401150062000d0015440b0360380c0046160056104000c0c44594980c001803000042081142c1a00b240420092603030b5249080108811010040703e00c0b601444e0b0300b0494241c03801404004d054800061418880e031500d01c090307081e00d41851164091801000704091700340c0d0012048001051081070342e2001581f0038030440e424202880840c0d030a10158410440c0880c0c00403005004540e0140180c401c40c4200ca4034050f80f230300e01500100d10b804191b010160003c1e43c00504d20540798814022100d2680d80720003041d209a5031208607145202c44d240e82c010150140c00c010400d011400c642160482e05190700402500c40c4848031813015000022074141456030700c855103415516141001550804040007034465020081c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 413138246 1250 413136996 413137013
    0x9030909010e09031812030c0705030d0908031c090203030a081e091c09170304030c09050402030618010b0a0618091e020c10050c04170712020f04200403 67
    0x821840b58810060b040104000001040d2140358400e40c90146400003400040303102510750f10010030607804001042c030007501c800180c0004441d4141d048a100320301d00384d001c50b802c0c40710380134046107a0030410040405207040b480741441303000564400140410a40d0009145500c801507000c00314055400304114400400e92025010440742e4240c441ca1501c02c08154072601c080e00782d50203034030140f20503051142c402c0d145200035007802a02c442c02d03040030030020b07542c3c0d402500c0308580c8802c100c480460354103000e00840d402503a01a0041c01d040d214514207130b03000b10b061440c60340c3d10340d601d003910321080d80c0b02d6102c40000c0109490700601c1c51260030394912059040e41102c07003202d06001c0004004002000002c503a51103550300141c50300b1700c501c038050500710351f28640307101c550800301440001c41210000748100d8061240c1c8020041c442a10591103440b144518095407165071040000350510f42156220ba0000070000556043e086c80c0c12000400110195268240c002c10b040c001c001041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 413139496 1250 413138246 413138249
    0x10e032e0216030f0e10110a08040801140a2711150301060e120c0402071b06050910020105060918010f06180f0204140f18042f010e01260903090901 65
    0x14581034154000c54004a43d03031810301d0300b09901f04501c8003420081e41e0b07828032440171940d0340107100c0c540c0e4554400320304d40600040491001c2200c0804041882c010280c450001085a910301c900c04000000b11015401c0c906188241c90008181031850343d945e41c0d01400314481c500c8003451036143e504240b0002c00740710000d2410b5004014502c4580760070344c070005640d400c402c0102c40242c3d030b480c203900d0075110300528400880c09003141c0510100d441d0b50001b000d4080300f0800d4522035541c0300704103c100e007070315420348100346c0013040030700448d1000e00d8180136030b103080081d0400800c030b41e90808001411902903030701c100c8524003a051001e101d982c4c103000e10076140502c2041581094104a50042d0b10505e016a151084654501e14021926220306906d118007101026003001d18050911200c0506420020024102400144007103440440c0007415600b0040e511810390412020040d2141744ea4001c3d03200300300c6c3d00c0460080c3d081000445140c82000d40c0c5c800745882d4103540c014419141ca06 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 413140746 1250 413139496 413139527
    0x601050f0d0c141303120309020a150206060109030c0302010c030302040b0c0105060a06050f0919080609010f0f050f1305071509080f0102070803040807170a030c0905010e032e021603 80
    0xc000b07220300980103007507003c1170b030783c220140303101d80d0b14015070650003001700e07010080d0084808140001e4000b0002601c0e52662026020f0390001d544003801102c800c6028040100540020300301440954403607410300070706a2107400c005140580b216025004c0d43c101840030b440980d190000c104060900a006c800100001d0401074200140f00c2600000d0340182441c0e00e00480e20890406980a4540c3c034207001840c5902c240c1c2d555041192545011b85070b060000e40400d0300b407018900304084d980c400c0d14030400e41d00212141300d0721104039a200380c0074803100c10f03909886214408503281444008000d0100700c15114621543d00e48001581041d0203404041040d03481885118042503007141103c4e0302c05d50143e5000d03a99801d41c0340c4140404c0034429840c140e42e1010565a41440d0907a00440f0b9090003511140302d0640d86500440d00c1010380080c00350190002001000c401d081100841c4403240352680704181600c1c0304103d10200c2c0c0200030440044581d040d195014550028454692840d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 413141996 1250 413140746 413140787
    0x903030f2205100207060804050a1403040306141005010c11090c09040f1b0f020a0c0b030a1a030c06070f2a090504031e0201091407080d050c0a02090601050f0d0c 71
    0x41000010391141c85c10300c102c800f804611000582080070a110503640c583d88106107000c551021410300d5941d4100d03000c101c07500f52802070300c100b109130040e403c5485500c3c514162410181080300440300480c404200f26080b07001c1d0180c0a400703070b03108044680b090115058094a801c0c1d103030204800d03107a038141e540310b480e4501344004800100c40002d903591002c140c142415846040e04c02286000c564040c00350101c1c04602d8003087c55100301d00154050141d120050000300c0041280484801349041c920f40d060384110b500359000e060500103030603c0c03030040002c82018461600d0f0600101103041541c0340390b081c8245646031407a034084884024000018dc10401e0b4982a58050110754a000d00510401031500c05040c030306200b50040825250b001021109030340340184002d40e607858a0240c169103001e03a070304ca48001841082514000d4050800a1900c000c0540a00c00c030050041c0c03245041202c00c000241210001d03000030040d01100342070004a14499a000800f4184220035104140d031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 413143246 1250 413141996 413142019
    0x31a04020310060e01170109020304110306060306060f180103050102030f010e071710050402130e0109020703050306120a050a12080c070f060e031e07121106010b0903030f2205 77
    0x401c26800070b041d2605410104103100140c001a51240e503450207600f021070104d800071a16003060740144d80180c0c0f05111510815403007108040d10b800d0122601509940450000b40b440d107031a101c00c1c816031801030805030101ca4200c400c4607440350300341c1090307801c3d0b074000051014000a03218068010080310501508504080500404002000c86460180c41026021402c9034101c0c0d07180070000c00b80184115969020700304104620071003886500c03507124540e400001c4071b4909008a0711800d606070380d00b525607a90102040b6040386034608050651041c281188002502044841000c9024828000d40d0715540382004040d254000c00300b852000c07003070200c81d00180400d280032040c95070041000c42d2081c89010010300d14040e02210781403c94042480404001c107071802401c040340032341c40070842c0e10014001900c515194005010076980b020004000c40071803000030300003411000f03083d6894402c115039403074034a8100341644003900e031091b0300405a105419031190002e00c070613242500c0c0003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 413144496 1250 413143246 413143261
    0x30201020d0f020c1c140309010c03030e0a0209280b10082e03170702060708160c030602090405150306310c050a061b060c120606031a040203 62
    0x28955541c102051090040c0c100380c50a000340a00310f031419010305a2810809856000c0c86034403074804007910115500068070f1a1504c02208a804084040e15140d04100490303608030020300110304809654014a102c2500603a41d076043d545c0244d004000200380a100c015128481189614083d440c0502d001d4480145403100c50003000640800c2c10440f015a450300c0450103182d004041072080d13000200e1802c65103a031030b100c1d00001d5030701074843c114000000e41c0180341a032013541c0d0041e60103041801150f00281c010781c010481c02100422100f170003040c0303a9450000d80401d4108807130860b00411288050b062920445070710002c544600c1d2698040040481d0b100c18000d011031a40584100c000c220004001c140741c4461030407a00000b6440405003002d000c1c105050140601c107207000c480c009105407050856840c0e50001c010b01d040090710301e984010041000032500710034090101020300040302107110300c1c401002d0395200860400c0081d10b0090140345540800da2140e44180140001d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 413145746 1250 413144496 413144503
    0x6050318010c120509010e06070302130f030c2c0903091e0904020613051f1103070503041511010906050907093803030309010902030c0105070305090915040c080f010f03020102 77
    0x41c1d080300c3d0b00010703540c54000301e590140c051a1076048280c0b050f00180200d0a0740360740103001c04230064105101c1180c40307040301e11510280307210141081e084d00c0000d1250621140e8011540c2c000d48900f62005400f0021460f40d5a00481e4920481c0d00080340411b1681450011345840b5103402c040b904a05104100217804204041d2000c1c2c014200410b4a52394510800b11020207003170003e1001031921015429440a59441d41c03100c03001803481001c4404040e00081a00d5107594000301443c1060704004034a4002d805044810341040075030607d048020000b88038070401a40a10004605032519a115618103c0d0940c46646454504000350411840300c040007035400700f103502600c2c02c1e03446003480320050149854541c2d038140000020b0204072441540300c070385d4403482602034520402c102c03401500c80e80100760700500459410441030703420b450007080090b400004401207030b418050800100d000c0b60800c44884010030085401e01400004042c1440d0050070300300c4d884400d035811030780000d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 413146996 1250 413145746 413145767
    0x100806010c1b0503151e01120305030601030605090f072012070f1a090c030105220201020708010e0705010e0a0b0403020d150c030204031104141317030106050318010c 73
    0x250407281e0310101d440c0040b81c014040100002000c88207600081425080c4d442d00c2a1100482e0f035180981c4122071540400d02d05040302d440803100510b4080a40703003940c40c0d50004219034101943c034a0301141c01d0341c030400c1c80307409220346032a144081d2500401c080c0280705111000c810441000031500c01140d030000b24046088910034000303444058a14142c0e4101d807000c20001c22418140c0c1042d20440c1c1d11040540c820308900d011a00038003022024076080b10001e952010400c0040386a40d8294035103001044070710392040c411180540daa4456640c01c6540300c02c1590859004914104900c0da40490300680b160300448925452900d82500b46811f841580b00080c064800401d080c014044035010320311000c82d95020601121465080050003503000340401c9542c0c0940c0d111790b130a0782c185803054218000c5203d407030b940b06495032000042c1139141090203c44540113010340c880301d24640b0b4040d500a20207912180d44a08204007030112600d030a00c0300b05400d030b1407c4485448254003109001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 413148246 1250 413146996 413147003
    0x10e0a09061d0307020109060302070b04080a11011b090518041b0308040b0d180506190e1c020d05071511070605040c030b010803090108040809010306050d0302060105100806010c 78
    0xd4804014a0890040e01003181042154007040c1c8914030400300100c02031900038801d0341e851b90f0382e540700e034425000c034000c10001625214035080000c000650391401400142e0b454248030326182d0250048a00395401c8060301e0880c8481600b0083c4056007080481000d40000c4a90801105091024400b1080001e102900039002c00614651248000340003101658106012030394454403006070340b0403944100041d00c55580340070000f1800d000741b0f403020000b03c0e5004002e08050345840f6030018148800c1c21280c0100b55841e5114000000c0c00c011200250510003003005680c850758101905001e0104000c60500c041003110100159903588034580d490340c006c0d0001900c0750450351144460007520b00003040700b03142002b40014001000302c0e4004991044500c00b00c16a00d484005031240a00002240810f0500001c10000345c03100300a0862143c041c5400603101d40c2c0c070000211819542c50054015801040061166003003840c039601d075107840e5040005080c14802c1c0003e00b0464020b1300503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 413149496 1250 413148246 413148251
    0x22180902032a10030606090909020d06050703060b040f1427040c0b0a020f0c100c02041d0304031a070c020a180e101508070501141b0a06020d14010e0a 66
    0x3108070a800b00403a41080300042c00b401811014000d024000307240500840700440c0d01c4450003e5825034901541c51401d80c041c00e42c0d03440d0a059544c0001074100984036a013410b031100710100d0012601760141009044e0004589e103264030709031604000052000503a4055104100c113a00e80280360540c00c000110783d441d010516955070300b0010f4a81d10541c00c05002c415000408c2c1744001c0c0d00059408402189805070341181d004041007000c1480e03d07200d0b00000c01d00c000505130151405600c80482d2100c4102d4444006042c46499400c43d44140c208564082c4102035448a8104064041e81e0049990920b4940c0d50034540006110035120702c560702036400a4403500008002c070380c0090015a003a64100c95503141280c01180c00b42800800d200c03107050315200001603a0100107000c1c0210350301a100c405600004d07040740c00e0030380d00c800f55041802c0054180360250001c10003d40c0c41d560f0083c040140c0781d0b0990454101035519403201008030f59540c0c0010b11010800c1c044880d040099200300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 413150746 1250 413149496 413149543
    0xc050403080a09210209090c0102100c02030c101506081005060c0f060907050316030c06050f0f0f0d060801090201080106030f0b030a0b010306060e0106020c010c082218090203 77
    0x21683c1000d960021061480c068807405a0264003e119034162032080700c4014280d9100f25800c1d5669603403048060041e80304001d2105c1691182c1d00180103500c10b4410b0f24036214026041a05d020b500a00a1503056965010551800411071514000d805985000c0d205410300b0840f80300032500c9400744600c6004009a02c00300000d08200d10405c1c00607502c01d0751418a00320040715190081441100d000e402a00c00040e0000f0800301c08400396030384003903125003150a080040725241c0041c0d00e50008290108064407040e90064090000d030028200348964440c02c01d820001510b00c264045041c580c145003c420050b0703005001d4a040d91058680060307441d20042419010704030400c0031039010300075040018248082e0f403030303182e0599000d510f0521103170742e60303407501043e04000744101030040e000030a4040341507121342c1d61400f4807800790424038140410300842513061082c01c0364100507203000e02c204110361528030072005040f0f99841000c20002c0d03070ba42c01098407100031059125942004089 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 413151996 1250 413150746 413150767
    0x5150105190e0a0f051f050d0812040c080a080307021006031110030b041109040c020a0c060e06042d051c11030f03030712240302060711040c0e01120c05040308 70
    0x4c0821001004801e0000d82440d20f07000d4540058010002c00c4106049400b180d141009908243c20365842002d072440c00b15810b014461070745024200721070390307940f125001841d01c00c01c00c500181c40c0e000f3b885060781e80c02c06c0391001e0f2500e1001b400c8015068100042040421102c102140240409440c60566a50900002c50050040314011980a4a0261410400e60703810020b40b2120320306540411252020b800244e07610207003084004d1580c401d00006201c2c442c0308520030540b5010241c90182040d445608142d0036000640e0502c0c0d074505c40d203e40c01e00e04007840401200070b20702950840100b0f080740c4000e14207004401406009400c100100401d0790724100105070f043d1102b43c2c01d032034407402e042c1001007070401e04050301002d060804014680d20b80904060606542d100d00180c0303205441d40c5d09001082d084943c007600c60004184800100342c956001704a0070303a02580c2c91020ba00382d41400581684501c03001c1440e00c6282151a044468100d001c890583e50070071007081e12181e0025 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 413153246 1250 413151996 413152001
    0x503090705040e01020a0e04060e01210804090b2e2703111206100603110c0a0819080c16080c0304091d01020a021b1c05150105190e0a 59
    0x1446242c01030314156110f80501019409031a1b1803031540e4403941003558000400c0709541d1680524103904448200402800d0209110401558580076800d44155443d807902a942d801036070003010b2007610b4203080f0030319140070000403102d250b94200420607013500340c0c2140e60440f20340d0004030034051150401803c0c01d8484209840f1201e6034404112410348a103020320b0440e04105010b4010310803658500305110300450944e110300d400600949420340342010850190000d9100b000b88800108000915074005224400b42c50b0702171840940d442c1440710400c541144480e4010040018800610a03002c108200300c90001840140f118130900079400c1840a034400c0601e464a80d1000040c0040d40c0c041541258405080c21080440304580d01100c0c1400d0b03100b4a036502c2c0060f0400002190320040c003c0302528000005800c09546031101c4915190711010901c1c2501c5d2036000780c089280c5100e9852506014010503a0102402d0101400d003103841c5001d1300802e25140c076100c002038007130007095 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 413154496 1250 413153246 413153249
    0xb0604050c0d061d010501051c09031b0303090b06061206060d110406090f0b0c03160501020d06061815020a03030e210904060504050c040302130f1d06071e05030907 72
    0x9490402403180d5030116202803c104c03051a2486041841c00001d0941c0240160f07403940f100424801d02c0000c00f40c032024000c001c100b03021000d02c090090710110014016141d006914869100050444003d042640b541d29008000703511490b0104420000300c2c3c0c44c680d01d65000541903406644950242c010080900b5920f48801c044600116000550701c0d4080c1c1c4403001c4821809610031515112000e00e0424401e030440c070456540108010a12084607000103901d9901400005081540011044099460380ea20010000e8115a80340d403a01050790384020041112280752107c40b90000d101a460b80071000000d01410303503840c0c01c150108420b111781860720940c88520340503003544c40108580e90b040044264003031460080041290b0510b03110f101e000300d652400342c03410719242d03900700128801c7d8268410702007511806003c504c55801c2c02020380f40c0b81b03000b00c00061500012400751408400900e200c041048404000e0200128090755211020441c0380c45540c03a944e403141b0902c1d05085 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 413155746 1250 413154496 413154517
    0x812070336111f0807080f06090a110a0c0c0b0301050306011e030204110406080f0603030306040905070f240e0f041a1302210c04092016140102070b0604050c 69
    0x103a842e800040b88003c84102011601c4e00e90300074030380f181c62084030b01d424202e4074a03060034183d101040592600340c48a50703000c40fa80c2004200391203802015902c540000603c03c0118040c0c4054108000c0e03d40d41d900050103100c801039055614080c006643d490040c4111201001040410782c45400d44a0840e4051900580280030f248008860203c0503840307449500700168001011508032005404058081c100043c029406c503101d40c000c0000512150340b04135054490408000390b8403074000c0300e0f600141181c400c819403003490310905032042031015600a04200542140717640e60b42d20307413400e005c0200058800042c0c041c0c03054440000ba00c00d1280c15940592341103003045006040e41c005100a20041c1030261100000d601200160300c402e440c0c01f0307008107045c00244007010a940c0701c1854480d5031440d02c03c0e1203401442d0201c0c40d038400741000710b07030403140e8401e4410b120000e104400c624103984e00840c03070465141c55441d840f0402400c498412610b45005ca09401415000d86503480740d17 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 413156996 1250 413155746 413155759
    0x10e06130905030d0b01020109050d08092503120804050d080604090b090d0f020c030c13020f1801020714060d0b03011e0504020906010804081e0403081207033611 71
    0x41c6040080c0d0300e41007180346284aa05125001070954810b01072541040c1e441002003000e00c811020581d0180d00c0186002c010b4810350f214015075810482d801c62584404810310217a071420341c185401c0740480f01e60614180711520007404005200010301010001e242e2520360025207400c40060041c1003040000782071900003400340980c4280c08240750205107120303100d06000e102003881c04d0ba04c84040401c4294540c0048007003004500304444403000b004421030b40145040700003005036056400000f0340e0121008142903903038495804000140140018104400d2a10800c4c0f00140701d80c801c004c20340d601f254481a215066480941001268258041002d404070310100c0c001002003000302c800760320a004c0c0b072022428950040010900441e0021503691902d519101c207003503450303485070301d12207503850400000011901d24006400120607804000750203052518004059440c180c01009040032101103950002002c6401d0b00d540204084603035842c042d03035080560551403500c030015008807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 413158246 1250 413156996 413157011
    0x1c0810050d08030f0901150515160f030201050c030c04360f180f0b091f0203010801050703050108030412080f030c0a08130f1103030d0905030901030f14010e0613 71
    0x2140400fa5219031145000c50b0b1240e0f890038031075400c0c4c07041d8a0702101c511040030418803050070041c2c1e102800c030b0101d00c1641e180c075041a180d040c0d4100400e0040e281080320030104003c060f4203000b0729402c41c4840c2001d50075810458103103440c9204500c965821102c0d01d000c41e0141c01e88200c5050311440040004030b0106411104180250401d580089121444c140640704408109113800200c140c11180c0d5101c1d2001d140d482000d120130217404900350344540310120451a0a44c1e40c04861904250009030b142e5150180040c00d40d80d0203008174007810b09090041c009410700009980c101d43d01c5a00700c500f402114103118540e8031a0402c0b0155400d000020044502000340041c64840c08941e81d100950f550154204984284001c00030040006942c00201051445002001c4482d0050a9906d40040e2400d08400c445a0203403ca6642c0c20215004a080da0944603a43c841c1c070040a09110f03d01540d0010074441005006955407074520b64045281906d525115604442c0855000c20204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 413159496 1250 413158246 413158253
    0x21040f0c0b04051003050408030f1003050d0203070c0801090203100c05041809050f0a03080a0203040c090e0d080705090105030c180319020f041a0d060213170f1c0810050d 75
    0xc0d84a40203e40c0070700301e2094561035040c400c0c420503200387c2d040600c450950311541c404001f60035010301004c105d018054030110200300240072101e481420b41c1c00443c0c0d07800c810701e44910304040c1684010103607450030048801507100801c120100300d000c42d01c0041c030900c50190660340c034012600002180c41352a00c400310440e00d198480d4100d6405071080311b0b03004481e92890350342c490110f000100001c04100c0400c6001210790095038010b44125640c2c11083d0301c4642c110308236101400380c05100c1e8012118400000d421049041d0003196514020b480c02640c4000605144000380000c07000040c00030b81c2e070046021880701210b1640300102a5072107200c0c60322601d036095060000581c45941c01002c5180c1c0f9103064455808985101d4800c0800b100c028000c102081000d05400d885030b5800301b04e80c0c5560403902160a010b0080d061601074000403a10506103000e030b02006105156200f40e0001031424070b03212540d0002100c0c2d29110026550b10f405500403c00c080e4002c90b0080340c44066203040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 413160746 1250 413159496 413159519
    0x1141324030f0209100b160201050913050a05070503130305311d1302010e0d140d1d031c05040b0f090f180a0c0908102021040f0c 57
    0x4070f4002c031007052840d00c561100c100c0b03405091140c010540c601704415030380390308500081502c0500504005080402d2a000729100e43c4402d02c1c90540195903030100240810035100d89038008119250a904510701600d01c2200c05805540149c28051301051844044107003a0340d5015007298441100c2c180e85a0084552406046002d1840314002100b10b0f4120501e0a4440a104c0c2d171440e0f8903150025583e40040d10018214a001504039044e0b09501000c00c201e003906164031450302d80209152110081d000748803a5140070b0726100b55002d84c119169aa41c000fa403000b01b91030b01200e00480e070384900030917603192041f40d208007030707100e00810600b034040706480c007074000e11409448042d0000316980810a002c482104005c0d01101442c010400c1103070554424144024a4284a041031b612803c603103292120311f06131020b029440d14604a2030180d000d4400b40380c506411a01810508500c5c0414040003c54844000d00c038442c2d4002803d1042c00d41c0c80e1882940c100d60420f02c4036445415840c40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 413161996 1250 413160746 413160773
    0x40302030708161d010909082713050103023f2d0a03050c0a0507090903170415020918070c0c0b1812030405270114132403 54
    0x9003002c180d800282c5941d5030301089520144e6104003c909070300340441d010041440040c01d0303541e8501881351204080c01e003611241c0b4105040344202243c4000c0e010444032211f0a440300701c2107800c0500402c0181c0300c040280e4100385c180c00151802c6e80d0210344152141e0080743c181a2010f00000d50001c01c1007000c12a80c10040101008400321021084020040c61103240c50588991150701448003080c4544043c01900c0b21070801d4806954403915030500d803101c10340044da00ca599560b4040100350704032604000d400310384032082da0780389010303110b203014010b00807a001000c940000e098122581d43c80e43d00341003a1054a80082141407002c0018071b0706000400440d0103142c6144042800d00c888002c0e075501c1200f5074a5141410050300c00d01442180b280035140030f034030041c0004a01a6100c1034110000d00005100b11400c1c10701c00d401894400e41a84103805180c0c80c1c403a651882e40340d00c140064010315600c0c010617401e000c29201114170a6070399440303013251007200002c8208a0301200841 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 413163246 1250 413161996 413162023
    0x5030c1207020411040e041b080f0f060f04050d0c06060f03061b1110180b24010507020a1e0f0803071502180904060608030f04030210020a0305040603020d02040302030708 75
    0x4c0307600d4440c2c1352200c920a42c0245e11507100c0f14000100080c40601e10541005294680d003841140e0f124070043c60107803007a18103050380c6c100c01088135100404010030f940c481a01420003e160400ba100d0507154201880b501f02001140ca01c000240300c01600404000c2146241100606a80c2d00344a0700500703040310000c00c0040d40c0c07100c1102242c46000b094902402840180a007400e4101060004049174540784c00780c00341c0021804042641c1405480c480c80c03070040c40c0190450552070300307030001031084c55180c10f00030140581e0025031941d410a0007a00e100403100c1c83c1001000b108101d040076240d200c06217000032020081441d00010004d0311019100d01041a4403d0002240f402680186c0102c01c04d081d0011b20050428500105800d4026000e01f00c00a41745840b500030300c0c11507001b80022940c00000090800450512921880f180c000b01e201601090103d40e9000700300e48502e01c80c0d00e04242c0c0201d4fd1a100805c641e04076001140d00600b203850041c0e07504007407600d800b400c0a000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 413164496 1250 413163246 413163251
    0xb0304030309030f020d082d0a0c180e0106031d0d030b041103010b03070c0206160b15010309030914130e07050103050606070507030201050f04080a11030f0705091305030c12070204 79
    0x51605d00000d81c1c90754150203602c4410b200d03501c0006418101183d80d90101c01c00d000300355a80724041440035418029514413001203601e65000300c0181205134040484541c1e2681d19108005400c821303141ca0303040da80c00b0301d00070a210040d0080c08400101200e0f0894550069003180351045416a1014080741400e840c148540f0300305001c0b48038180024401d2148080c01080051959440f5100714801148002e11a6041502c8201e80d00b0b240e20a0328022110f00c200360052246020190410f070135400c00920f0140000c0c100c540c0c000f070698000d4403a4078860310290010207155a2040340000002013132210802100c50346040031a52000c8602c505400b03e4a032101203a460f0400b82c0460b54496040f40c000d140c054910f03401102c1a0b4082000d81042030b00c144000b1513034800500405c6415402407405c18180024a0109402c081d4100c01840069014982c10051500d640b40f1142d8000400003064032107003054244281988a4160031540600070b03ca481e82e55210080083e0604a0080d6801c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 413165746 1250 413164496 413164517
    0x212100e010603020f040903051e07051005060f0405060a15030f150506030f0c090904060c140415050904060b032d070c0221011a0102010e1207031101060b030403030903 74
    0x40d8202d81580c08040d4110080455451146c10f181d0814000d00c0e2107444c00178645400c000400b00e004085081c4020060740008458091000030813491542c0803515900300440c0c1807182c0019500030580c0c06617801ba640b1040092a1a40d8034000c920040603059402e142803070107158010003c01c0900d1038100010700d821107040c084241c0075200f2090380ca018111610f592107128030003254900c003c284400b4400200000d80300c981b2201982ca004d2840303108045881c82011002800309100d4000c200312404050200700444080710792800701814082c18041d40d43c490101c0801e01400e1260010020400000144108500e04884022910340b03480302c140240c244005440400e810300340c8a400004610000da4130162030400d4501e5420306001c4680034140c0507441c80203080d600e9040c14003c800c041c10130000d800c2c0d6028001c045001c840400507000c014000c0d00b03001400d0249100190801002441d03043c040a0250300210191107075411a42c4c0301c0c9403d19004010f0807040300c00f1030000307800d0351b02c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 413166996 1250 413165746 413165771
    0x50708060402090408031005030304030b1e0609070c060e01140105090703090b150102010902030a06021b01050c0d051f0e012408010b0c12131409070c060504020d021210 74
    0x203005004a078000c000014684882e00c5a450540010308021100ca030540c200041b155406c20051000314400c0598010a10b80603e50f0180c84441484204104110758100261a9500d2090913440f50150804d03402450584c1030040c001d00d4203d100680541c81d0002d5000300d03140300c0c405103040b14811a209521956004001c5007901e0407010b0050980910700c010518490183c1049078542c030701840002038040b066000645090007440060b51a02da0000b0039207142400c242c2150500c0c0072060080c0050304281c0441c0e0110b20820346035107001c1d0303500e8020540d440803190040030280c2110514000042d1950351881d40c1403002e2207045034000e110180c151503556220200402901c40b621042c142d0b07031800100281640c0f12204c1d03845c40c0e02030b903e0010040b000200241980c03960511441d0500d50420349640c1c21810012a030701d2041041c0010440d007541d02c00200c1006590042d80400e564443d440840c2805071031181c000d52118070350a85610740080058110003180600605121443c417552 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 413168246 1250 413166996 413167003
    0x10120606080d1b03210516030b220c03150e07120b010804140f25051207140a18050405010507090b0f0f090d05100b0627150d09050708 59
    0x30800081030074807080c28400710b400350212440c0c46901c00176103c40f8503440c0810b0411a6401ca8010700095106060214090307031520980920f40401c0d118808542025030011040001e40c01d5040b0406441d5003401060604c290400024880807d10040909885000c6200220030807154000000e23510007148055a22a014640c140d40041c2c41d0341600d500e80741c44072054981c4283c80c0000b1407040c40c00a401d4010104945404c0c40300100038211800341d00f5002d201a0b42c159030025110b400701c0c092400000c0f1012a0b11812140c1c1035000e034041100c00710208480703404583c8004840b140d244050b004aa001d60000707071095108034000c21960341e540609640490f1140209100c8540070b00585001003a040c0041c90034841402c1d00c40e05140010000480d00f80ba507941c100c6458201c5100000d44060300d016190905804035205400c10b2140000d025080c060004216551080101c01822a8642801114003039046034086555180c8046800340a8503a00300100c50b107120b014070000315800040f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 413169496 1250 413168246 413168267
    0x302060c041d0403030e1902090a050c0a0507050c040501060903030e120c190302040507020c030601170a0816050a031d03070b030708091f09060b031b04020310120606080d 75
    0x100c075040b0903407106000c0c801d000b03004100301c0a060381e038030701d40c480c00c5810401c1190111812810105020345031050280315480500352140703060a01d02801403a503c0642031700c03030801d101c1c941280c0303801040c141180b5100c130101c440ca4000345008008518260301604207030640e0b0203a16130b42d90600615007409181c0f02007104014858000716841c000038a40241e00010b01c1c0e045190195903130b600d0b80c0000c1c049900a942c1c00015901c102c0f9071060604040c0003460040c0541140c5070601101e000c142900c1e407211103002840b441000400c2c2c4500052420282c00d034540000480e000549030f0301e4041c0080f803449128030300608401d45944031500c2c2c001303a544141c0b400c4030342150443c0ca8400040d58030013000f4003120f507a40904414241d550400d064200218241e080d000f048604450814104468010010314020740011422480001010003d040903030700c10b039801a6a90340d000800344104059030403001c0d8110000d1404410301650360849000d03103039502c0940d401c140202c1002e841d0807514 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 413170746 1250 413169496 413169509
    0x8030115020f2808030109060305061f05010c0c1503090213020702060409180f05330f0405071203020109050d03020901080406050615030702010515091b1e160302060c04 74
    0x10311054428a024000d10107880d40070182c02c8000a003c55680a00c160001d803c030502482d582d8101300213101d0200a0590043e10074403c09125a81071010242004540e004443c14070901d010501d0400c1424040080104841600228800301e1000005d001e070804850503840751092101140842c2c071988219140164001d128170b03e0980303480790610180c2003489004040d80714a06810020400301034003030001c244500054050849580f4035a0b134032000d8090080007907080c1d95008030880d6440c2c00010b0304058140c04401c4160351f1454400d1401440c2c0e04514444921031201d0410580c05401003007025204205a900d101c00d02d100882c200c0c000c041c4020700040c00d480c0400e0203d0015072080c2e401510140410301000045841d440c016070040d00c006005030f40d164104880040d0328240d0840b841d800b140c110f262400e1209801c0c410700d041d10003080003c20000b905010702c01d40c1d00c1a502038124265a032030b8403208000c0710590001c5e800c2d18282c003d40103910000300c11680d81c9044a0a680c0c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 413171996 1250 413170746 413170753
    0x2150a231504151a0301230109050405041b06020d030501140a03030f02012304051b06030c090d0212030304030206090d020a06020f0909240102123408030115020f 71
    0x201e241000082c09045002481c9180c1d40328020882410341000010071545080342a5034a51404000100d40030704846580300340d030354401c00301d840b981e4000c501d18102d407011200802ca54031141008841400718441c0544060082040002d00c15008500c00c4111400c0b0303202041140c0c5e076540103055401d44003030b01c294050f2040801b440040c1c0a1740412464150610000442500e9101c03008802d82082345588001c1c0c0390300003000b007006020440203007410000d502d01002d200540c80890b070b10340030181c4403905ca2030b0f000c1805406501c6000c200040a0340051803c0d01c0000b0f02803030103403a80c0c01074500b540180203040c000341044030300107040380a8000300da0040c00c01210540f508070003504652004c2d8203a21041000c1d440503500d00e030b4003a001e00d4101c202005107500c440d000100d10f80700f4200d00d50540d0800901018021060815a8081142000c402c025000020040c20718a0200e102c00100000108200018042480c01031030603203100400b944205040c580c41643d40d04840c4040284903070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 413173246 1250 413171996 413172031
    0x1050d06091d0c091308040905010f050a0648061b090b19050405060d14070c02010c0605071b05010509071a0a20100209031e0a0b0702150a23 62
    0x58a041040407400343c0c1341031f41410f85818040060314001e9001c4c0580c0030b9000e00c24805840c0c0284028010440d1341481c1c4402c4003e040f907040c039940440c070044a9140540100c0040c2070240120f501e2040020744544c62400300703841d1080041c030141005050b40f0f6108280030f105c003400358040105842c641c418181c14080e2142d0300c01d00300308400d01c56408000c2c080c880010340ea12802e0180034040802500801c10b510310714014500400000c0000c4108441c2d0b40390000580d0300309100000d1640c000a012030140d0700c01d90181c1daa400c40c25280d40480d8454082d503414803006520250290503a0020788601a41d260740b01040052040c0038861032440801c130407004907004506051241031a4405828061080070000b0308240c110303410000d40b960001400c600a1900340204000450110003050348981007504030350341c0d40880d140c01000d05404034042480e89008011003c881800540060460b00e804940c0c0c00242c59020030381d02e40c1041d103035070307080f1010424400d80d0711039141c2c0c0150720f2000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 413174496 1250 413173246 413173261
    0x3150604031505041a090d0305150604050103020c03130b07050c040c083904080c0a030503190509040207061d010506030c011d062206020304030203120901050d06091d0c09 75
    0x382000703081216852005c83d83c41400001d01144d10348102c0030340000d800c103d41d0294001d01035a41c02002811600b07234413a50143d50366a080c05450a907002880e00584030003040480230714621508040080a1340d4132200000d02c560051b004104407841801510600300742c0a061100b0780d2120511440401e400f00c001a1444d00301c00004a081c8040104503480311400c4642e03080385103890222808500320002d000d10100034204070803c0e041000790381c112002860758540c07584038001c0c204504071090300220f030825218401d100356005003d000780115595080382c0b8003403004101a0a50b400d6180460343c0709026428180708251040101501401341030031554011500c1c2405c019841590110349110b007002038941802512034045020300308250504000c01440752907030a40d00950455004000c02d00040e00c001c20340a0200c02c003803814540b20a903030380050b201c80c061044644200c81c0b601d080001c020100e60041002c80a000b442e90b40050701e42848903890361094402e654010103130101240b442c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 413175746 1250 413174496 413174501
    0x6020703141603030e2701151e0f09141e012001020403142b050f0a0806011d0f090403050906040e1f080c010c050f07030602031506040315 61
    0x100c07000c1054035044901d00d910004881c405800c25000034849003820800c6082000c01414241c0041140401c0008040300e0b009580320140581c1050f00080395030510424040c03401c0584610b03a0041108400481039801003c0311545d0880b070002450003030b800144e103500e0700c40320350008902500b40d2008114000ca60181c01400007001410055418520050010602e22811154a18500141c1d4803072440c248000c1040380b54000f1802500885081569424641c00f03200100d990090001040107000700b043e1441d00448410000c0d207100051590b60059109210f00d104401c00d80364140d203900b0005020700544100440d058100e594021030071424a00803d181c3c1d441842850326a14018030700e00854185d820991140341c207401e1081c00c1c040384128950361018030052109040d034035281f034802000c0c0d44100b00442030303050080424184081c0501070021100040c0482c04503800b41d5907925080d40254001c56401d402072005402c025002d1a091044904a81d00150380c12200329644400200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 413176996 1250 413175746 413175773
    0x9040b091510111b0a0803070303090c053106030f15050702061506030c090a08060403030b0306040b0a0c09170f0106080309010e1c0506040311010b04140112030c051b0102150106020703 81
    0x138024170140d4006800b520800c0104500351003940d0110301581a8a882041c503a2160000f0744114400c00c221044042c0481c0f0000c88413803900d00802d40030540d048680c005195541000c0c10f1400391001c80000c1c05039481d4407074400695500200580d03552036400b2a182c180a9a24900d0f00144510380102c6180000103540c100e070b01c01b4481703032800e941c81002840e1421254004541170b00b05c40100000e140c2c1501c103500103d00150302422031480c0550b80c0440440d001000e8281855a03a03140200744c1c0d00c1081260080c02d50181c0040e08000d01400705513459201003030510b110b43c01c040c0080b070500d0010040c0d411481060716240d01e94a00b02040041800300404220241d0f0003944e45440495420024580100d0103600c8510f890017014106d1803d41d0000d0000c180544d0902a20010219003100081d0441d8a006600342a0300d210345411105e429903083c0241c1503206411000c1c0403c008019015007420098085510190401c08440f40c1c0b04c100f407185c0400350308003460410101d038058503040c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 413178246 1250 413176996 413176999
    0x7022b030c0e040501030c0e0c04030f0f081c020c190206030f19020a0e0108071716050705100e0706080c0d05061f0f090801060305060c09040b091510111b 68
    0x1950b82c0a00100c0c040314004d0f40151100d0b202e46c00300700202ca1528a20fa0b4102150b88a002c0c6080e0448e01c2d42800003814203c010000f854410400003800f98030720a4540301c50107070180051069900001c8006074110081000440c010360b1411a00745800b0742d240c409285d40944114119a9a403491603aa503c00800c080c00c041e402c0d0302020340c807080510080c414400203844400b280030b0315500040c042c0c04010b00303803018440c00c0504102030000155803190b0010040b4081001c4001da16801c071894015103000070001c0c0300b80e410303900900201e60048803400d480001200c1407640e5850341150320032000e49403001800d20400c03a00c0704009468101542c08030026110280a00e108020170710000c45075180c072170004540d980b415000c0e6610120050007442c81400034400381d411078a5107500c40d040640404c04507200001c1d070500640b15508820601ca030010007812981c6032410f103688040460110942c815000c840d0010b40141c008c01c4001140b8151000810404042c4c1828045000307000d070030760b0f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 413179496 1250 413178246 413178257
    0xf0d05010e0601030303020d0b04050601120908040b0d050603060c03060603070c11061902070602160608151002060106030e1506010503040201030f2c030a270807090507022b030c 78
    0x5005074100103003030081d4842d590041e80c03240c10380a0a0308465142403018490b41c20a0144000341c0c8c1d01543c004490341e0080400a6601c00c24900741d40c45100b154031041d203914010600d542441c000350b011606c60302064054820540d00c1e00300103c054401181d01c9544400148080303101d00e0711880480445611420a80014403c20000920b90380c112080b444c540c3d40c041c90b40000601d40c1403007030800808050004040392406074404a420841034046d410400c0080700002c5c1c521281318664040f0443c015046640c410580100291214030074001c3c0004681821083d00c41007000041c100ca0030764242c00e0882d110380f03504004660741d61000d402030b8101622616042030560385441014452240c0c00060000c17561107820130001c621252100302481c0d003040c0410102d00e608115840c0da90300030249030f0101890200d1403060358043c0c64020b0036042c13040e4503001c100c241c5160300c518000c18a50702154019a0400d450282a00000d842a1f100c64500c82c0007200042c000e0f0441b2642080d1405d28 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 413180746 1250 413179496 413179511
    0x160b160203060f1e09071e030c0906060f0c080409020d0905010c0e030c010323040f060213030303060905040c030201050d2d1b020601050f040608010c090f050a050f0d0501 75
    0x41e19142c0180c0b141864010100d060100000c03c003030f5441c00b81034101c83c9251480c600920000c3d01c3e04120300c1520f00540209072034645c00380c2080121006903074410680d20045803503407204402007071a800f50078040b403050343d0805140c0e03008001681005034011012072606040520280280d04003014041606450720043c200040b000e001d001c0c1005000d950b02d000d440861000c15140070b51a0300c00d50b05051900711080c82e9100ea481179089100c0e1841250140c0d900c651800301c9151214440c06440030344007040d00e00d8031400c3d40001c08100d074080da80600c801d07602d0780401d034125201030360b000b030441d00c98400410043d4019000b60400200d605000030b40031849640325900600306804240e29254002c201146a2025200d5281d81400c00d4444c0080e20103940700103966107a06005840c03184000c05901810b47e6940d401450181445d08000c1c800281e9000700070749844a00c2c00380b402ca41c1011070020500e414071600b800e0840f04c00a00002c021007200d428442008280f50042e207465407a000d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 413181996 1250 413180746 413180749
    0x2040302120a0203061e01120302030c06040b06010e01092d0f170f19030e03031e090f03060c12060402161a06010c0305030105010513171e160b1602 65
    0x75800ea89042520251207a0301281c0f0405007040780040803400d0750312402515640c4480002051419680f00d01808030b01458036040c182d01c0c6000303601101415102d1803081100300064011000e018283c00e03243d10086600d100f0040d600c054036070080d00300308920701d100380d4142c3c000c03050f80b604030000d1480074000c80c6440d0b240021584a1513084080110003000c1c07090242c42d42000030030011100700e0081c0079114a09150000042c00750403014082140500c448200740d6401c1c81196641401c01010100782c3e8114a108601c0c1e80000581c0d42c42000070500522280c14013140c0c5d24130603034030b14036014a09000d0011a8410307a0780544215003086e8203021001034410315442c220311b114020500080c00e01049114243c00c01300040c40c50b410071040710303c03410000c0d800c2829603055904c01d00b4110b0b11011007100700c046c0302e403055000030030f20380c0c05142003c40140d0104400c01c0b40806149210051240c6200e1150f994010100300482a070380240d0800260010501800854201c0308822801c10303030540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 413183246 1250 413181996 413182009
    0x5040e0934091b08060607020303042303010513120f0210180f0b2505032e03080a1d1f1101110d050105030613060e150408071b030c050103020d02040302 67
    0x504100140d00207040f600e1400d401420880d8402811100589016001c0d40031030f44034052031180d141d1900c02e10103030440b441c0b0340c04840a02070700060000c01181c0f41014054009003002102510f0744c00030540500200c030321500103c4484003094004195200403081c51100820400401c0e18082143c0c49022000408240c1116081400307071840d0089403e00b8030101c0d000060380c0324848502c540c5040c90b84d0b005a00705d41031301e40c005a140ca045110009405048024040c0d5008840003030620400210030030208101038487c0460390f030754403207002d0702000c030340c2c000349441c0303c4080e9008100484404c50095200c6281c60b4810351460b00209401118409038250b0701200011190202c3c08140f4928410840c401c050040104400501007030a0003402c10100440c0440c020703041580b01c80c0d2210b40800308010303440071100700c807617003410918050502d00d82982041c1c01c03c0740d040d5a43e0070340000b07426490880800342c981240500301c5440c58400190000c2d84481c0413170760007540a1100201599511 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 413184496 1250 413183246 413183261
    0x414150d06060e1605040303080f04060605120109050d020f060c1b06090102030103061401060807030504050f03041202040506010f080c22080c040b040522080408060705040e093409 79
    0x160b1103c520b0402281014800319000164010000240020808031764000c1361035401200d04075082c071542d2039071f00b4684090301c21a00a83e0300301c508a40501e04502c01580030f03090480c0a5020703141c41d07810308141241c454520035400c2241d030b8051804252030000c1100144403030603c2c83c4404e603003444501010303070800d081121100550b96002c07004005002c81030296808583c4a48006903a56041401c060034480024009108060342c41c00040c04020081050381440e8034a0000c42e0b4841e50781e00a81d0006262106040707020b10704201c0403510329400740c4081c081071007070b5485242ca5039848514400c4d003600440a00411a07a00100d464a190400940c0c2009800802e0241c20300e005000140805d0b00c1200d980607004070324180801802c00d00b0040ea502c0108421041c2ea0010b2083d81403068441c01a03800241743c41c040e03403043c0b00b040da030401e008004950065900601c10b60720480320f243ca48541c8601003810340e00d4401411411001c5442c150828000f00000c3c0c1070f42600d5146400171200c58 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 413185746 1250 413184496 413184509
    0x1e0f07120c080622030905060c0c0a05041104030b090c0a0e04051515010302090a05090a020415020102070503030601080901240f05041109010e030a150605040b0414150d0606 76
    0x1a56403503000e0088412052001e00b101030010480c5092405260f0b0f403a00c45070008441c00180e1041e108201881a01408018000100010740f01c040c072010b0a0f0700c0700c0e441c6102c03500c90890f0354400502420107002d1501179500341d141b41801c0a203103807030b5184150b02c0140410300a020b0903c0d482056940c181d2070304003410940303044014034905071501030304e08500480d0598100296408014035112000e00c50580c402080c138000d038803086080003007107c00303031180c101c503038080d50020030007071007040340c4c0d002c0c2048882100c08500c049201040613403c074400e5590250840d082000081c000354020201d135230700803000c20b00004400f1110380c842121b140b4020004600d2601812040050045a031303003c00241c00212800c02c6070411990614809214859056050042c2e28801500d250307400e009074032000c0d8010300320180c0175420400180c01410b081c05410301c51464500e0700d04a0741803601c81d05103451840f43c0354107a15100c42c0c03140706001c0071941c0c1d500d500c01007a81e05a0b0000d1024000c040c000d081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 413186996 1250 413185746 413185769
    0x14010303052a0718180314040e0901020a090b071203180501090501091101030e061f050a03260306010c06090204020910080103050601061407080309012a201e0f07 71
    0x50400800c010381405203c21300d040c1c24800c000001c00c0d009210350104603030508140000810300c010081090040d68022642d07a146002040110304044d0010300b00d400056594202329501d8070030680c058060b885d80600100d006c076036124803403030080c0d102001140c50100749800004640c1c2c1d455082d1008144200c0d81c9945416442c4100544034500e000301c460242000d100d10030f006400076540e008001d011403560601d10203082000c0c0c1041034a2806450043d048480399601c0f0f05014030050100d84080d2006d04110114011141303101c1d007034074040c40b01651940c1034600c0300e44032400900f0101c04140d03400f507400c012000030341e500c030100e111004103142c84060306980b45041440c101101640180244080c0301004c1900c1035004007124519a0301c051019101c0d01d5131340303450740148014400720302003400c00b070100b04034003005da840c01c01c2c41810369860400340b040060390b001d140c40813225915000e502a0121241c940d0200f070705a407010084108480c048485000480d242c103c455100f04180748 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 413188246 1250 413186996 413186999
    0xc020a0b07201507110306040c18110340050c090103032106030c03150f0615051e030114010210050402010c1202030c2e14010303052a07 60
    0x607807451441e412003000c0d01e00840c100402010403e244001d6000071540800010620304001c00c1c00d1300180c0c0488040d0031140d9070315080c40c000a031078101d40140d40e8842d148001400c0580e665005100940c40080d000c81d0031603c41851821601012004a0b174200c0381c00702c0b0700000b40c1c5884081152212042c212822924600d0403e241400c180061040c09180c501005002280d04403100c0c0403412111102d807141c541002c10701e000100500d4100a10010440310300006003c9585c4c0784141d0b039031001100300020780501900b141110060f200e00d84000b560340701389024a90041c009058150440a84034401218204030301005910907000b8016024410840251035641040210700141601c0000c0165040c03030307000a03000c25030109009100c20654a05004aa40f080c02030756042d0800d80c0071100002d02081d64030f001300080705100903c81034411032000029149015030307240d00c01d00e8a43c10483d0703421514100d955911400c61400c0782c506002e06001c4610112035100440304404c0c01401819 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 413189496 1250 413188246 413188253
    0xe10170910110705070b030603030f0d05061e010f0f1202190e06030c04050906010c06090f050105100303140d0b19030501050a06080309012102040608100611060c0702010c020a0b07 79
    0x5480c0c034410070701000c1081c000f071070024000040304070036501101402030700c83d500d60300001d00d140300305030121650311000b080c5030781103072071302d1f001140542800c59407203a07402c1c01c0d0302444981b9048200c0d043c3c00509480300344000d05001c0d0085420b500340034500b01d103d502a04d064142a644180fa000071020705221160b10016030000703016041c40400c8034141e1460621048241e0a07019902942c0e116001c8080412160781c0507907603400c2140e9000400707001d0001e5904009103070305502042640c0700c0d401c000c000742c0111107200000302500c1e89604d961060304d030040784080c00380d00b1011000741740c40d070b840d07150440d1965002880120342a820111040050552428600707440010b0704e00c1e01d41c40c0c1060010b00c280b48010081d01c1224600b0f180100f115241421040d207009900d02005030541e10020700421107650010020703200d03041e5081c0140b40c0c0c80c0e075040200c2d072110305060881441e400c4600071400c071605c0300c0001c1580d1030051604021a9007140c000420320955a8084003c1010004000003007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 413190746 1250 413189496 413189501
    0x30606060f141c14090d0905100c062007060b0604150503060315011d15010801060809030705030a0e010e040e030405010c0311010f0c120b010e10170910 67
    0x20300316900d0328000c540c600c8000a0460203000e81c0c0500d5000011403011070000602c40401011041080c0a000c400e0003a41210141e010503070714808640284c2c00e2501c0018003850841d0129000940b204a400340698402c507184c1c0710350001111915140c10345052451709001640548041500c202e640c0cdd01082d06e4890120303000c0300a05d0b0b00a0f07005100400003240c2c140c1c0d01500c10401c508081c0c2d565583c402c002418002c079a1601c10762010241d00214031018003180080038107240c03440d5100c09481d03035600c11110742d40038031701c1074005103041c0018070540d0b21812003d900410720208490522490b83d503010b095400900200c0002000c41450f004150381c8280116441d00b0251000c0282055041c54203440348505c0c00344a062100c14100340d0109031050080d091200c445400802c21640c10303117848000383c05d1070340800d400100701b8504c810000351584140c854440c03051311000e01c4015001e091010304186a0101c41c10303c800007002c002c034061207803281c600c6048104042c0c44144d64407002d4404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 413191996 1250 413190746 413190749
    0xf050313090506090f180604050304150305130809030f010e0123071e0c081917010b1603050c060907030521041e0b0403030f14030f04021e1207030606 66
    0x401410801800f10329110300400700e811141075040d58241c0d6660361415080a055600f0040451044008000c18800040b014005a03951482d801d128007061040440075103505a0f484070074050316011000016003500b004100411003d0144d424415625034500c0c219911200031404c943d4640e000e120007041400d5103a40c1c80150140c0b0609642032070240141155120726070081500c0b010710035001142d020f54101c0546a900088c1c999641c5250b8001c1d406111854141d90007003412685039161000c5034680803416610741c00070b101e080c491311640410000d1000c40307040e003e21508000c1c0001c1c80700c00b8811039204080c41320061144503e90b14102d80742c45050b03245201d03406c0890505020626412040744c0c111444610724800240004006020b0b5070f00a0707100300c3c1023481c001400001c02d90071000d400302503e41030302d8402080e0601050402c0910080301d03103007070000072a0005001858202001c0e81416921b10072040c0340b0190f8808180500c41c60039102005078010441003080107411b024540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 413193246 1250 413191996 413192009
    0x11e03020405030c10050a0342081c080a022502090c1801031d0a0309150201090308041b080f100e0307020108190908040e090d140d0e07030f050313 65
    0x100c5e040140c8002820b074010812910101500c81b550303a00c0c00780e108445403021400c480848141ca10605020301046800c180c1c061120b4419410002040c11001c0303290782201119020640120020140480e1804402060b2800e01ca03424004241b842c1c510105440c1070510310308118120b4030f00c600400101c038000501c031031000e140030802100508010b9405c0740c0382410a08000c2601d50000c14040c1180401c645921403505c52000600285a4440148411603055501c0305071110381c200b008038266004801c01401203a04e602c00b01700010503050080083d042c0c1e0108142155858500e150304041003140d4407810b546c40302c5038100201d24244030341300c40201c00070015443c0c42c09a40c0064901d1400a00e60180201c0c01c610740d0941000c0c581001c403940c0c1d4808a030035666600d038012030f81441000d40d5048180d2051105d200541805109040c43c4940805c4d000e6040000180301d5901401c8240043c0d2003601175188008002184d0b548641056403054000c0c58a420f40c8a91440b544070243c3e0005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 413194496 1250 413193246 413193259
    0x150f03021f2309040e010b1c03140c010b030d0908070e040213050c070b1e06011d120115080c0108160906050310050319020918071202011e03020405030c 67
    0xc40419401502801c448002100c14032005a50307140c440149000b469a440e41107401d0130612421014190f1060005140172030707802120047c01c8c1e0100d00c100c45a0710004000c41c14950303c500c035041d25400505548014940041040c8150101082c1020034151466001c1014510f080c4107450043c0013a00260040f02442c010034900341d000585548816a900040c031640c410108410045c0c81c02100c046941051b054401401c0814015440710f02142c44540706840b0745020442a40c494180e00b050b580220300d0a00e000f04488080000811034104100c3c095961000e59007840341c9040c901078010440c08029091158046d0000b40c14440010444000b00c00c100044030911030300141424180c5e4803a00c0c0060700c1c1c1e6181914100680507076040a42d1500c600b014041a2815014040340e17078610a40e00c500c0340352200071030300040024540c109441c0b504440000c0c0b2020070760b00300076521503005240c051055440700d080038030100c811410080000740c00040511282c14200f000852807030050716130 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 413195746 1250 413194496 413194549
    0x3050d02120906030c1b030315040c1706011b0b0109050703090c0e070e3c0d141507020a03030e03030c040b090414070507060e010603020603060d0303150f0302 70
    0x1070103040c8214040d803071041c00040049072600303003810141e50f803c40b18102c0108182c0031510341540d4a400860b462900f0030458180144a81064015111440d03481c0d114a00b00120002c503000c00081e006003002c3c1040104503550b4503010411541a00c0d00c0c0c0103140c410310030350500d03e4840c1a40d40003084039081c1030502507403800090b880e80480045504109a159840e103619000301c500c805030802065114404000c842b45494030b011000d100ca00d00e81550708170f1005861340c502404049101c0580e80312041d81062004500001010f0000e40c1036a400d0380c00c921011409c41500760401e0f140d0340e0060b44529580420543c0600c102944108108001c50640c41d082e804450350348124000d051700c06002140d00302042d1900c0e086a00301803071003059010030345420f01c401400c40d00129001d50364107042c1010319256510600c50383c01500d4002c0c1543e8035540d6402d0920000c00c0e04094102c00700341d0755244140c0100e12106189003e0440d2482d00c2e40705a19500402c0803410142e5814000c00171180031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 413196996 1250 413195746 413195773
    0xe0c03130b07020309101e0903111e03010c0c12110d050f12070302131211120f010606020703030f0807020a2405040f170316050d180c03050d02 63
    0x90684240d100401c0301c00e0355100e090407400c0d405902e203801d4011403100800182c5942064400341085403040c16030078001c8410f0741c1125022403511001d0204080b002080d55182440034a18048000c100311050303e6844c0400481e08654014254100154404550b0000c00007101500408a140b9142124400c100c121480e030b16500c45020300011310000280e00c0001c048220240e0310064034403541d00740c0b94a0031410140282d4484285402024004100030a09005140300304d0311094201e2f202c00c0b2464605c03018001526038520308611144510016a01811402d014a5015080310380c0a8980680345280c09030050304811410b600303020181d810040c080b44d000404c4910781d6003200203070a807010128250761100703060b4030748004010308100c00c01c001c0c031a000340e09224070340c854000c0c900081003051104540d400161201c119040c1282903400c0a5031285015200b49a034001c0e0000340b5074650407000a0300700400b0701c12145420401c800b0010300500340407a0448001d03c2c001780c85913040c14103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 413198246 1250 413196996 413197021
    0x140606040c0f17040309150f090801020a05072904062003090606010e130e1b03030a09090905150711060a05060d0602070c0905010b07060501080c0607110f09100e0c03 73
    0x1c3e101d489200006081c5446014140001c26070f15030380b4000c2d155420002070014000301240c01c04203141c000000b60f924814400c41304166115a1424100300305955556140410442c40e01e044006814050040d034900c50480e81c0205d21900d800214240c510100a401406507208000c0840701801007200750100030400c0c43d0300444c24a000000c408a280004280304165685001d02a1501d04060350800c0000384441d440c0b8003c10301d00860900c1841055603902c1244208400128980000c2049075a140c014980a500ca0b40c2602d2184500682072500c80c00e00f06c600000207250a8441c52540030148000c1d81c100c40e00000900a51a007040802c1444405904c001d0909a0000d1400c0c00d001000f4418006042d003240b0510036540e40b06844070940d0403c0b141a54560300e41000000c803244005503030b901581003d4181418190541c4504001c84601da60450b080000e048000c2d00c80c4d030340d00001c58803a28203155421019402c00801d1030540301c001307098400018003002401817441404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 413199496 1250 413198246 413198267
    0x602100b0a230d20010905300f060a061403060603120d0b0a0b07020310020c07120303020d061701060905090604140a150504030806030109200d140606040c0f 69
    0x2d810341c4028218400800d8261641e40d1016010b00c5440103183c5129454074941440e041c0c003641d50403400390b01c0fa8100060b040080040342c8601c0301b002401420500718840c0103032a824102c0690700a41140024141841d004407002000d0f00d0b602c0c00c1c140080900000514a0403100381c0080240c0e00c0c110713000c26641e00850381035504d540740104401111a000d41c21940005001408035203080d9038a00d501250381e04030002c100e01c03d0250450300c0910201920955141c40c20517401004454a00b07900480b82d04000c12043d010036800704000803600d0910f00850000340426a00c40c3d902044c0c0390314141c210361140e08155a49401c040c244094440009800f940150f08041c00c0090f03101e01c044540c1c0741c031403200401080681d2a4803a40030303105895010a10560107900e0b008c01c60380e030f031000301400c8403c415030081051640885c40d4010030b81c619500860301002034003c03260021039071a00c0c010380041031040c040c0d030307031140302000384c01d0405000d0141141014201448111030f20070b4060020f0006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 413200746 1250 413199496 413199539
    0x1a091c03051003081207021c0c0803070306030515070e1c0803090106050d030e0324161101021b120f030a0f020403062405191a090a0602100b0a 63
    0x180c1c1c010039881010b100c0701a00542d486655a9070760030701800b00c8100d1900c22550ba002601507c840483d501e45060200840822555100202c43c01340340c0e01d41c1a0b54102810340020590f8a02020000501c01c00112041000c4651740c42064548014020640d4161900081c0580740806140d00000381d10030000400591009a9039140c1d0b03122800329005062540c0f00359402640011102b003819040303100c04044c06000d905491002408100680b00e0308008e1b220a9007500b104000243d10448190280c9040e280c145040d480e400201c1c210b1909a0b00009030106001c0d0510603814602002040510b10070300c5242d036540c0c28907002c02040301260100808030581e9a0f01d83d8406e0b41c02d2a25581100d018640c064010001c0b244032107005500600b420510009207502c0e41d1307012a007031500d000d01c950000e100b11100807400b401e040444440e0220044190856a0248005007481e03030ba90b01800041c104a034001c101c4008080d0000e002d44080f00c10180c01480c000105005801540c860072880310913 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 413201996 1250 413200746 413200751
    0x702010c020c1c02100504090b06070c12060f060b1b012d090206040b09100e060d0c0201110a0201051e0402030a06180f0c0501020106060201050c18030a08071a091c03 73
    0x3ca00303071400300840e0342500c02544940c84d40c00c0d01040940110141007654046442000400040820300140e4031031124058041e08000c20100943c0c002c0000c2d002410b03200c1c1c0030114104038051400816038035280c1025520000204240403026249070100070750103034200c020f01540005145040010180080322182d1600e2024115100e40f07194000c110b8a40d07001e02956074480c1d07242c1c134883c8a50884458184601c28500103030b044144607480090b00048010140d61a1203c2d20b4448801003c2c5500903806554070340348101004200c00c0094000d18001350008074044c41e0000c00749500031007484500390b0444a000901c0003507100082c03a808901d5008a0008208624220343c19030428038442c01071240e17510300c035903008103e068501001152070a070000c0c005c0684aa5060f400e8a03c2120420035100302844404155a00b19032607104409000e07040c2c40e10180e107602c850000786d0007110155101a00c034100e000c684840391805035031001c49140688506100954510440134480031484c04164 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 413203246 1250 413201996 413202019
    0x305130311070e070206010302150304170c1e16061103090402030a0e0d0e0102190b0a050408120405070e01060c08030a0b011110050f01090203011a0a0c060207050c090702010c020c 79
    0x907400c00810300642941d2210030740794940101c00966800c42400120702803000c001200c00403081d0441a20301990303108072041c0990b00c03200030314003003030300300021011062240c0c06003184100c900781c05c03011003001450003401c104889000f518000c01c420b030344020104190850281268900841516800a821140503990b520f1310f9141002400c3d20207000300e01d6019800c010ba600700d40243d44002c62440a0302550320300301c07000c0b0700e00300e400907904800f40c031440590000841c00d814503031090b5802803058078040c0c100504a48000741505048900300c2d100d500040e4144011507980c40d400c3d004001a162070f21421100d07945100c141c1c04098000d81c4042d440380e04580e8540e00400c03000700c0318079601741102d50b000c11884031007002d000301381d600001e174505500000c108680b2500849040c1c07090b01550303200040391546400c0c0154007010381c5c0001c001c103c81e440c41c0000e0160001782411030083c0300506440c2c0781c031810040c81030f00280041e41568035183e542c00b02d0580210b0303a0070f01014116894007161 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 413204496 1250 413203246 413203277
    0x402010e101817070909020303190801180506150a020a0b1006120203060607030534231c020309060c0d02061f121e060605040c03051303 60
    0x1400842038095100300e404400600c650341c03201c034610581c20b010078210000340d0342e041c04020071503108166209030342003404d013400020220b400c00d0410906c042c044910b8a20415944098120007019420000c2c120600400c86030081c00b4400d09910090402003200d8140b100c0000c03101c1043c200380c0640e42030302061920b01980244503480c14590442c0305062680380180300e0b680782c0d0707095020b1072011501c220090019140c0310310959104042c05040280351041c280c5064500e50402013481003034001403100329203480600c510306032503090058403242108400c0d1030800c0e8130070a42d849040c40d840407690784902d0000009480201041c1d40c218170610724000c000304234110301c030312541150001800180140d01d0302000a104246004a60984040351a100510005060003c0006002c4110005e05101403600d03800c15440e40c0d4450340303105200709038030074804039100c1c00f0760025114a075407104104554203007801504440451881e04110500d00601c3e1080c4964031650040d00b002282000700007103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 413205746 1250 413204496 413204507
    0x70807051201090b010305030d0f0e030904022b0f0612170c030702190f060f020a030e040207060906050609100b040b0c0309090a05090d110319090b070501061d0402031005040201 78
    0x34035070020f1400d032540d03840303080899480d8420781a135207249c1e18150f1610040040e40c8101c0414101900c091890554880d003000040d410141d45003600d4402d031031440c40d413140041c0b1003101c00c015903000445c0e8103601700107030000c1b102e20b9030240d0b0500b40d160700c2d5440020044011000078040c1d80d14800d44030b00301c100c2054614001e0b00d01c025001410700c5090700c400c0c40b220f1004411901050f07400701910391213001c1280c0220f0b00c2940c1d000960b1094606034002030240d1009411008042d000500f0035200d03894030000e44401e41d0003910966550720901c50a818203141c002e5001c11803040504890f450501004020300c5a4450f40b1034040020032501040101801210b240d46401841c0e000c8600300b0390b070558020071040c1d490051070300c200700b550030f1454007071032500160344030800145050000c1242c1c02c5002140407025401000340c0e0b240007007010440b41015028560050340001850790400548060541144000b80c80c1c00d00034404000041e68000785503420001da400000c035107600c0760710040e680c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 413206996 1250 413205746 413205761
    0xa050114220f09061b020a05340303120f050105011b02040902060309031b0a020105090103051008070815061801060c1b06051206011119020a03050d030b12070807051201 74
    0x2511810194032005001300d035001148850780b00d198200602090107010790741c030140c12070000c05a404c002c442d941006000c0160204540c0c10042d613a01c1c0c8021300018105541080e001213010800040803d103041c8200d1060301c1c0780f40010030007040785505000020340030300d00280c481a02d043c010076110085454503040460f03941c3d4090041a12818030316000d60f1281c02412100380d00881c000811202c0d07120001d039001c106a0117866042c03401e5080d100450103020000d203501c6c1e00143e80500050300080401001c0001c286070740241c008000c15001442c0c0300b08028007940c0c0b10310454202e40711421880c50f4030604443ea07904083e80a20120724003030441c81010030480c0000e100030000000c02642084c020202200768a41d403800350703600d0900642d1400005466079010380e00c03900003504d100d00d042c0c9040e000c1ca40001c1020150070f541e503072030b5441c0003141c920b51000607445804130002d90801240034031451580b40b001d0480d9905140c002e988e50480fa200d041c0c843d2041303407000784801c8004c0d8445035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 413208246 1250 413206996 413207021
    0x23030903060429060f100e090405010b010906090b0f1b070e04030917070b091203210106020703030f0f030e0a030914032425080a05011422 61
    0x6049140c5424103035003c01c240409500c200e0016400d101c50070041c1e1101501c124401000038200e003070507000b40400b4401140941e0305100c0090140c0010350303a4042060f20032442040042460030f0250001881c1000b507034440818491005018400342c0f0b003801c141c0d946003181050441d10707201e41c030b6032003902e40f80000701c50480b138007944001069003125030000900c2a07029849210b030403035079500c21040310000307000105004c2d04290000d100580b00d0340024440040003c1c5200c4c281c4c89200100360950b03101c0c07400110b140b040550b80b555482c0030501c0c034900600b07060000c0c000003440c0d51005852700c0c2042d803419040020110030a40251b0081d48820f0081d4051011100341c00100d2401a1403034456001d0300c09440c4d0084040d4829140c001341100c1036001d04040f080b55070595444001e046040a000f00e040400c2199080c04985200c41c00041f85442641e9508030306d00f031401242c0112403042e0000112480030035010b041540311241400c1400c4039401480b019038080220200c0108181d48170741 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 413209496 1250 413208246 413208253
    0x9020a0306050702120c03070f02220b03011b050304060b0d060207030302180604140913060c05040e071b080915030123101b140d03050405010507080423030903 70
    0xc8207100d002d5101a100e9001a02203402a5000170351401d0240203104d0195806c0d401084050006017241036010f072079500c0500007900e619044e01c0000100b881c0d188840e4082c56035a001450a03250074010303104a103141c445121600402060001c1152000400c0900280d45030341c6c0303015090309da4a0503045160781005086450b40e11a20740103010b940b01d825865000340c4012040d41c158a44001100c04403904100c03080050740c0b00d00c090090b00070008240c540350844c1c002401c004120680030740342002d0180d41d40d240e91982400340c140e08442010b800d1008001c118062102c0410039801520710064100c400d0b01c0d22404608005514401100002d00c0c0c0c000f000b000004a000f4034010081039079203941900c84140b40380030305102c512260440304000103840340080c9140400d80106515804c0d0041203d0703044175141e440c8440c50416071061420000e65603900700000c1c071a0030320407a81c0000c510301e08251181895200c007000f0440704484c10f8645003d81e80d500740308100c2001101c1d105d240c0038054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 413210746 1250 413209496 413209499
    0x90615210403030b042a030e0a0f050a021003061a161a07021203041104020c070b07050d090506070b0604020d060e0c0703080f09060103060f090812010f0501090b0f0304050109020a 79
    0x1405800b0018840740218180344070011b030b4078040003000c100503015440380455200c10107000c8014040c8511880303128040c081200f004100f401000d145954020001007003030b40785c14414804159401c2040301300b0903140420070f1214540b54003c040d440d180c41140c45403250160914400b248408110081418604000040b0741d40341c3d60401034481e14581d000c0e10a41c1001d100c1c10201d5100c1114014110180c4030300340b007110300d0242d001d80442e0020808a0700c0d0540c407102014004e1340195401d0350341c0d078401508120010b50000c500005410305840d200c1c00e0660302c1d40c03140b8100001518840c492a00030800c03c0402513254040001000402d81c01d0b641400c001404941a034840401036000812031070029098200b10000d280c0140c030400014501c50b8178649482005241030030005491584940100c0017013941d404c09070061414042c00c24203e545001c090740680800f42e4055414411803140270464001c0e0541660b40350100111819030320b9559182060041c00c041c1d200962044000380d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 413211996 1250 413210746 413210753
    0x210090b0c06160f0e04050423030415030b300d05040e060109060813020118090c0e030c10030504020d080a0c110a2105120f070203010b0906152104 65
    0x341c1601070000703003110640240b036601046600f031001e0102c4c440840c44443e10100c41d4180380d4019540b05000d00042041401d0703407030402540e541c401400004a03400810184007003a01442c61848001050804006500c1600040b618640c00b501200307a150340714840308407140c2141c40503240d07159044416260042c10783d40000c4e2030350b0080d000c1d450541104800156103540611480800c1e81c0042c4c46007503003565410003450f0455020041241080112807a15609500304003000c0083d2080e180042155403c2c10001450b03106042981842039204100c89413060b110590030b8660f10846190100c5c00d6a2140003149400d00100341c001c0c00781c0390004040905640c041c2120f074481c1c0c850600841c44103035050801040910078003420110383c0c0000c1d11502030302000404100350741e20610a80d10086c480f80d810103583c0e0429502e218481b0340c00035034042146401c0c031641c060004102d070540711b46e003000008101000048242c0140c80c680c001420560014000c0d000109000b107100001403a01c3c203840c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 413213246 1250 413211996 413212003
    0x1701090507050a03112b06060806072f0106210c0e09031c15030b07110f0705040c0c06020f12010501051c0c09030c0e1b0a0c0210090b0c 60
    0x240da150060540104591402100344400c030ba03082102c0c1c058460042040080a001d01b800103603c00c0100d55010350924480201c007072000340035400000b0315514202405090140040070305013040070980074184010103000884032601d250340c000310100c950011303520340140325540100c9041b0385410f816004111819007110082c51050b016402030036035030031208003d99400c0d58001303511340040c00b400b505201c0303401203200c184029004c081400040400014180d0039250400d4403808242410014460b40020f00c421110200300020040360265960f49038036601c880c02164800c0f901e03400c1d452000d030301c5006655000f58002504641e100c141e000c00781d14a03404420010364542001000046540c09641924002246043c4031020052029044002030a8034094001488140400800481c002030a901c024103d8500840c201d8180389c0120322210a84e81240c245044080020581c41a8041c66200e051641510120006030303c1010a96010740385411101c0c4401002c16400000728001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 413214496 1250 413213246 413213261
    0x901080a15050c0405041109041503150b010c0f1101110d0804020f0613270e030a0c020613030305070203060603010903120504080909090d03050702070605090909030f03131406040c030b09071701 85
    0x803101041051b550414892200c2000e01c03000c1c103006e24033912a444000340b82c0000d52200d405250543c80010940e4608003034154190081d220302c40303051110a0903582103805103290389070100091175002d22150b00146a400d00900007401000c4c1c8402070583c3d034913510140c0b42410040850b0000c1c8c1c503181c1103e0400c007920350411080d4800d80d100b141682110500c80c1c05204000031025505d00801c020003a504202d400d08126088603007089110b010201d12404000554440e41d1126039500440c010107283c80380c0980100d100b640b403d00c040f40060380105054900c6403081c0c1011403995640c0c141444540600300c044c3c0d40003241e032020464010f4020400303008251050b01e040220b9294054100c0e5a80407500804010407420040c943c0e80c0d2810050003684480d224007264034000c011520801c05810030303280c0341415001414018100501c0f1800c6401c192141d40080495161940f1607241a03021480050f113070700701c01d41c0803c04049d0280300a00c083c104115a000011081c000841d000f0702c81c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 413215746 1250 413214496 413214499
    0x71e05030c0d0f03021c020714030c030406030501080106060801050d06140414100e100b13020f070b0c0a12390201060819030807170a02030103020901080a15050c0405041109 76
    0x144460204498041e20a541c0c80f040e00c5207402d03540c11780f41c86c80c5c41c0083d8040301c01504c40e5210f0203002e00d5a40010001030800d144004061526245010806000d50740181c00550480c0d041c060103000e15988490207504445003140c04000003402c50620400401d0040f0284503c50120300c20002400384a071000030040107101c04840c032103401c52600341d04a550203640b14800c0c0d0801c0ba20000780a00070b400c00c0d0740950004021aa04a020086003001c07640150400300301400042010000c0c003003101d04c6160700034804d01e08170b4940641108001c4c100104203281d10704007555441c40c1c071858200482c50004807403442403051465614171442040c00500ca401400040d800c050010032650804141510750031815880c21440c0866550251084d0310018000380c1004040c061580c051a01c401d151802070f40044001a500e50550044c040407190580000009a100d03104610004a0f141244048081e410f20006085d444000700b1007511310807644001e40c06801d21035429000b03e17081005200c07481c5c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 413216996 1250 413215746 413215757
    0xb01180e390d1d0109051507020a1b05040207110301050a15150216030f0302060c0f09040f110c06010504060f0b121b16021e06071e05030c0d 62
    0x80c004220701c0110000a001d40755101c00035044000c101d58090201d034250280e020440c0e000c000341c40b1072850301200040c2c3d610b13034540c1602e000b402010300101c0c0e00304a84490010092410000c0603527507601c002c038001c0100a05008501c4d003003251071162030107040020030940d1348442c0341c10318070030940f4000c1d00d1911035442e1401183c0480001d1003046100356483c08000f402741d1820301541c4007580c004101c1001e43c01801480c000c164140355810020f140310320314a0304c0310328541c01c0091400d00c2c000c144002580c010858419040e0410090301c01e03844080b0b0700030030154050342036034000c0e00401d1110284000042a80100703004045201816607100355020092140d503942086154034092007040e80700001040700e400741c190404151030740400d11a08540305400302100074080c6500c9007441c0c502d0200380102500442c0f4241080d10396484256401036610310000300000d10b288200c58009003c61507008048002c2103e0721080400e42d03410105894660103040c08050710360569014a100140307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 413218246 1250 413216996 413217031
    0xa06180806011a0306031c0206250804060e0f06010f0302040e01060b1c0902060f030403030f1a120a02090901020318061003030c0203030d05100810090210030b01180e 73
    0x1074680c0c101ca04071620003949050240100d00c590740050041500360055000d0090307400040719807140030150f9603005015500e0400c4020054150710610805500501c0c066800f815074041d01880e001500a20000350b030950841c012454a91203808650250251800018050504407100002c4038002e45040c0503a0b201044480d01321903050286030201a82486514540310b04851003d0200c696010001031000302d60700043c5250b0007808000f40e48140000820080541c14041d04540b241005024401d5002068021084809090030301d4010841e014019440c55420002e43c6503039a0042c0849040e8208440381c10301030b40c01102c090b5000341034010140c1400d40e00081c0544203544840d90980068210b94048864105400003a41d243c4000d1140c440c005600e03204c0c650003240c3c04d507001c03038095281130b410304d0914090800341284145440003c0d805078480210038049410341d8540041c48904100059070703400301000a44c030151107569030103e80300700b40a011b540100c500d04103010441e0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 413219496 1250 413218246 413218259
    0x9050129040204030203060f0603070308070f0c050f01080c131a04080606150405130209040c0801061103070c0e06243703050402010509031902210d0810050a0618 71
    0xf07101d98800290103900001c0000c911480740e01d0030a0700108001d0942e1156aa41e0b110021650844201600d180840c150700358100125042d0079030041c0800d44140100c01d0040c000a032013650010258400b1443c0040c90b0702442103d01400400780503000901d16512310840c4a94010740c005004e501528860380d00483d400c2e03d000d10500f4000b20b01003100f1031034103040200744002e00c00c0c0022030800e800e0f028000006036076228028522216000e40c4c4034a222343c0350110091403120981c039403104a030020044103002c1581e584440e4107035865000e00000a48134040420600302940d07a0b41241c01b900901c40d80c948020340f2000705030504d83c012a000420b040182e03201c2c00b00c07110b054482c122411a80060402c00d000f6040329901c076005041c074500f00071a4502003810040c3c140c0009c120742264902100851078001d0ba4442c4040320f46d5400101641141c078007594904a01180c0c1040c821404d002503400d841d0300403404033412014011440055841d00d016046034140c040c01c00b010142024082420b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 413220746 1250 413219496 413219501
    0x30c08120f0a050d020301090b0f0a0b090d050a12120b060306010c140a0611040815060904650115050f131703070506190905012904 58
    0x140c21003030028545111810201200e81c44001d50700c050202c2408440e400d0a418405035008180e11000811130724079200070805070790100b848a07403141440720820301410700c1010603180304d1581940d400c802c600742c45c02e06602d41040408010103801100511500c4594000c905c5644514002d03414810f620760001009028001255910b0000b10f0078050013001c00c072188084c2015107841e0040e10320b01441e617100c01c1c9c1078411440400c0050400010104640c1400b00706540c0c0c01810018580c000e03040c0031001421140700500084c0003000030b405200c98030400000c0400856082c80c1265210405100401744180c615003026443e05440300c2e031100d9003040c00884042c8841e0f40d500001c3c0b89a081c80c0030840d4440713a00d070740c6000701300c001d215080400c104403005007940f8003900d0488040506d0308443c4078045031201c07510a0713190814010700b80050300003d501078000d14541d022803484281400b102d00104401503010b0125801c00f01d00c10803032130100d022401071000031424031902d10740310700c2030005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 413221996 1250 413220746 413220763
    0x6030921020607080a0f0f1e02040f05090c0f1204020901060804020102060a0f0e15100f03210c0203192102122d030f1605030f060a1203020304030c08 66
    0x341c2c00c0344000030a43d074480c40b001c9a0089090030005200c80c030f8140e5010469400f00324441e401e50f074034503060003035000f1b1000b500010f450b400015441c250070710030300400a10891040c18012444ac00c041241d003c3c000c0c1c155020308114400342512400000e800243e1500d042d20140e0041e1a04400818010301ca001818496034042e00100b01584074030308990020f001040200c0402981e885800300141402d00411441c0103441041591a0030f01102945489540b0b9105080c41c008200e4108005101454210711031030700c040c22149820801c4405441843c03240d81c00940c0b50280694942204c0c002c900c2c4805041c0c0201d002641803121680d648004e82445d40c00400581d1080040b0318070030304204000d01c12410160050545100c444e250300a104030030840d203080d150300100810440781182d09400d075004980610007100d510701c00802410a100c00b50902020310350b002d000a80507100c1c0c800400042c40c00e01d00109024030141002501c0b500180801c07201004102000544080c001801c000e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 413223246 1250 413221996 413222063
    0x1203020c0d0c290109050a0b0102101e020705030d06093c060f09050714071112031605161511011506112407030f1401060309 55
    0x154500000300c10b8910858465045821443d100304061480d030030b9400b01401c0d820b02520500d169414011140241d60004290b641c0540c40d20b00c00004603a40011452002c1c0c0c980000000ea00035003800d0745d440b404c035451442d04500e000003580070400c040003000304603103000f0b0715003007094a4071042c2c1d05094904101e5072895080004e401180a00c0381468001c10b10321000c0030000603c000303605000f003039414650107407007011800801004412614020207030f102000f0b00d00404002400c0342c2d1000e003402142009440480411103c035890f41701ca1200d00e091000c04421a503ca60450300400030780314800800316014060040a00308481e402c8060100703592144040150f030091a800464180004008206080d0b4a491858904241c2046030102800040c0e5801c0f0002d40102d03031441c039001615026008841c0d40750a03201d8031030315981034a0307000401d6203400f040041c5a501d44001a0a02c0034801040c0e070001c0000007500794041d8403130303000c0b140301d108080702c690080e10307400384002041c40214 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 413224496 1250 413223246 413223253
    0x150c02030c0406030206031506040302040906090b09070602030318100e011509180308070c0b0a05150916050306060706060b040611070602030712031b08071101020c07030f170a03091203020c 83
    0x1000d201c03231000e80403017910024094a050030b6803500041c0640b010316000303030f031040d507a840204184002c01118903844400d0070002c01e4400c2c0b0f8010029600e20005184403001a400d03000940301c440c050200d01c08009900300240480044204010300038140f1030b1910240d600942c00024407070301c66000e5a08824858100d079248008103450545841100a04900800c96a0a42c1c100025004c8502a00440340c11100203824a402030150305240302d031501151260f1100000c00003003004000070481c01c540036141072910394480e1000700d00385000f0300c0001050181014070201d0880d203000b0180c0b04869603555610101a201499281c4610250150b0350060b081005a100031407015140d40305038189502c0d00003114a110300c1a4480244040381180000700c4c0842840007681e4801c0314000030b146410001c6150180607080541e88203c2c6110013840142c030303802c001080c000ca4608191417200b200109640c0c0d030f102414001c00405103000b040b903070032040d905441d465502c68826620f10320b100d103009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 413225746 1250 413224496 413224501
    0xf05041401020111030f0a29040c110a03172505070219060f030b030613030c080d06121703040f0308092d0c0d03090b0c0304150c02030c040603020603 66
    0x20035034004000240a042d9920344072185400d5850f04015485035516141c40b458500309a00d903001512164400c01041e151a00d201c182c880700406200d10b18800f085500050300c11303a0312070641d44400c825034000c03054007030300d4140303401d154000c9601300042001d035060304800d650314030944001c1e0702483c0b50a540c2c030060311182400540034200929980e030008110a403010b81e041465000c2c8141600109d0014032501c214404454043c081c1400c000411005400203140800c281c0d4402d03241858040d00700b01044480c081442010021104440340300d1070240440754407000c840310a04c02070801161045504454100ca9440b5002178a01540d8000c6517a80100501d4400311174010000c0d181040d6409500e2040c116410b200b0000c200030f6020401da00c24085151003854280300d120f82a150003614101c0c113440c00203a00025450a90b0180400340740c50b00d0300c5400343d038510b002c0c9803c09885054010b800000d560b42081104101c0c0740300310100c409141d03121040c80b081d1140303844001c0d00035009101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 413226996 1250 413225746 413225759
    0x80304080a050c07030807060b180c0d020d060611101413030e03070311310c020313060203030f010801022b020c03070803040209060319030302030402151314010f0504 73
    0x10050050903203811420320784041e03007450420b804c3d54400c6840c900006859410400075015a048142d41180d80d04000003541c0105403220344004c2c0000350b909000159000100150b9061323840088401074100400b644a20015104146600030102c1500c10390550101805042c028102481d122901d01c041d6a15040e10421038406103150131403d0002000003130f102030720104021001540908040c9114074259030a005403954035040701980c242c0c000d402c4001100c241017480640241100c0000350341c550001d1308900394003c25000104000400e0f00024646134000003650042e80c0300c01c00080ca503660303240010f080384076a00d01542200c40c403800340384907101b1001c408001c80c0c540c20809403520791946209811940810400c460002000c01840294102011940e5102d0404e0f0000c0c420058000300c0102ca074815000d0003410150000006001c5441b100007141400207a80346141d20355100024014685006010303030200c103061400d8402e00c2c0c0d071041491580d85000b40d2500341c602424501e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 413228246 1250 413226996 413227013
    0x304030605010b0a0527100906030b04140f060a1e0305120921010e031605190c290c060906070f090506031807030c090606030c170403021c0309021804080304 69
    0xb031b0080030f80a440900c40e14540c40383c224412950070103640b011811814650050216032580b0b900c00d00940c50841c82d0480202c50003129034202c00d039081c00001a40c0c0b8040041d4102c60a5046014001e44100c5810000b010207040441504c0c0f1880507074000800b2660010007038001ca500040c0e00070340402100c961020a6040c2140d82003000f0f002140324900c10454520710b61000000c3c80d2641d460320317014000d106040c404110162030301003030050301352960389810038100000c0c0584400c10001c0465800103400c01c02c005520210b80c061600e848029a040c200e888440c01c841d49511400340e0310001e40128400c3d02c0c406010b182a84405064505206c140281e903040207260200e40c000d20240b03183c0800c2c00b002000010342c801e0403203051650503d0f10802c20381d44158801000d0600f42400d4840d026004015017180100c00030159005a8550800701e1034100031140d02c2110b0892455201c1010b40c1c16081110194020b4841d5243c82d80884440c1d5940d450481d40030b001288140003190000340d14a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 413229496 1250 413228246 413228287
    0x606070b0109090512041509080114071202070209070309150b100e0a05151902030412021512010605040503011a0d06051807080a060e030310050112020409020c0304030605010b0a05 79
    0x7041101c2c83c08001d1981410181d001d90002c124440c040840461f44a0b40001c1507030250402c6402071180103500c6c515250003103c00b4158034140030441308007410204859041d6000c0c02e40041a18406040110026004054601003030f64408a0241e003100041d6940c090050b00300c001520455913010711810071101d41958074030040c0d0100c107410340040da5130b0390740e4002451080074009046d6610007030207003407241c1a208030380750301950000e200c2000b080c21545c888501321134040d244e0394a11140440c0c00000c1d8400c010584141461050002c039555134050040c00544078103070300030000410240c01480c01c0c0382041310743c2035004100300310382400980b035900450341100301170010414108a40400f9420100c0c603030000e11b165072201d0708080500c003040c05110001e003902d8000e589142022109001030700f0042c010681844400e410116114040e81e04860042c998000f0841d11f6a6160f11425184d521a205c01e4410a0508001191210f80c2000f1109000036540b9010315000210600600e91840c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 413230746 1250 413229496 413229503
    0x50a03050a0c0b0406020910020601120b0714031312020c090615070506090a020901092a050418021b010b06041e09020c010e0105090c0a090b041b05040303080606070b010909 76
    0x1020032820000e0340f0150707010b0085100b448056120881c0b03a0900c880501e440f080f400c11580100010060005100030218446070440d0484400340c2d10315806444208000c240000c1c2d002d40002080000140ca528503402148034041407840c5a110110490b510381c001e10303000c3d41c0a410b00780401c3c403e02d00221603d210412010b00705042032980d0301c60300d04048d01110b00c0702e01c076001146500210319240e404035016085200040181d210440601d8840c0781e207100394204440547e012200d112401082610001c10b11040c500007821101407a09000c0d40040514840780480d2042a107803022040c0104074068902030455070901d858164000001e200910315400c81c1d9440c0c64012400d80040d0005012500786200007252840900c2412401c6640c02040d003038442d000610458403e64076982541d04503915240702190003204100050f00424030b0504000d60510750040345440700c3c1d0081c015004483c0640c803003070389503940c181c280500352090841c000c11660400d40140080d0070603500500c8181d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 413231996 1250 413230746 413230757
    0x510230604090f031d062701110613021f020a170d062403090201020d0e0114030a05100f0b040306020a05120f09011802060a0f050f0304030e0405070c050a03050a 71
    0xa640f0380b0812800d644905900103201400909580c103101c5c405044111003d40304140350030ba400c0308501c03a51404080c107952200c0c080e9500e0003541e105544c1e04020100c1042942c1060801c1c2c10040c1c8521155001240100414101d024029000c0d0194081045140e00500201400341d6655000300040c0100c101c04958140234200003075885206071009004040c0440300c030349031160310100340145040c001c002003600b07081002c00140d902140506034050103003047d080800f041c000580d08010303a5078552002003404000c000015415030801f50040305517540304030b0140d0310360710804030440050242c6001440200400c100003500ca50050100b00348500c0d0860400f080b82c0300c803103021001621404055030b020824001540d20078480c40356070060001c550b850000c1c5503400305201d40160410307001884200c01e14110b4241c0120704450a00c07229080f4599246058580980a04136800c0c0d550b00461420000401c01070240d4012990b043d049402009001019034040701d07558131002d558000c114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 413233246 1250 413231996 413232011
    0x10f0203092805010f020a03061202030c041802040509010b120d050f071a070c02030706020120032503060801050601050702130b0402091908150402150313020a060201090510230604 79
    0xd02c00c5c80703100100d0070215400340e994400072800a0513210b0640014000b4130682e003164006a4001844494182054801003000e0741030107e02c11400010190107034000703041000300180c054042d40440340800d800c588140c0ca0b000d1001d0000d5440700c0c030111100c0416410040402a0b0400d40b015281c5140f01d04800d03043c58480280300c400399801070380d0000c04100810000011442d09100c0d0070b0152140344003c02c4581092010380000406c00186800304480000100b01d610944c0340c0050f80c80a040c81e852581d428001900600a2070315110b0381e200741d442c0201050b190361044084448903034000301200d99540c0f00c201150000c2501e502400d621903808c010b150016200c46819407000d1036410ba0b151b0382c00e4a07045170745042c0024420100c1c06c80044000300801a035507500c0e40c101c003500000182d0748a070f0b58100b001140c03100c41400a580422200e02c0015469815008002021312403006c0d81c0320b09010f80076a4003662202d8040101c119003000110102054841d1666403000e40140042a0794 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 413234496 1250 413233246 413233253
    0x31106070204090b0702010f0e120c1005070c050105010f030209150a0806180f010b0a0e0903070b0114040c0e01051e091f0801080a020d080d150803030108010f02030928 74
    0x142c200483c00c41d94502d011080003629034080c07048a5908820200900c8024241c2070b10580b50421a44c49802c07425001c16580312409c810403200103c0966804108003e060014002e810141d200703004840960030700c000400c4054900c04080c00f2640d018000c10801d494415004800700d40d00c1c044160040d14041c00050b001c00e003001600d00465030700c0c00f00d854992948056a003403a102c0031618030b40d603040030bd005240f511442301c0e410440d0082095914141c90702d409503400c520803000301a202008020010905060b0604c0b4002d000c81300725030030001d182020509407a58150f40c0c0d59140407074418421801d49081011500030900c49548a040c600694200003401c0e100008601c400c0d081d02085280541035084001e15025028080003043c0018491380080c0400020307440040c003007000481e00f20504503503500701a510041010420b01c40c00d4860325015134940007445601040c5d07080000d4004904818800ca0b4012100440a40080b034645442c2c030009800079070404c04207070403110150010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 413235746 1250 413234496 413234501
    0x100b060c0d0525080301030b040804090606022b090510050405030a06020403030f171b0d0e0105040303061d0105060c1603030c02031519090606080f15010b040f031106070204 76
    0x90561a450302500d0344012418200c1c20791031000360f01485850b000d052804901c030300c4180ca044035400301d011051541c4074a44200c560150342d0000514a040450210f0400d401182190544003440154120705102550354507004a00b6841c0d01c0204a00c844107100500384203200c00e18031021400c0c89480d05a8440100b4506003109000b034542980c04201441059440400429100340500d030000285d1908c40703030300c60100000380140e4070300c0c200c400424240011203420b5a2003140c44080c100071400b9004c22a078042c1604660450010745460004a41100c01800c03070b141103582e80624900d079a091030b081c001f81380e0207810110b40503c1005040760310134441c8a18240650701c2175450040402091040c1445c20b103100d12601503080f103050070025410204000f600d0041c07109a000304e03103003c03142081d0008004540198119000742c1070300c2400040c000455081d4802455070012541c0e90300c0c1c03003840c2d542c05140a400308204100000b08081400f440f00c100381202c0041402e86803c00c5a1f000904 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 413236996 1250 413235746 413235763
    0x804061a06120405010506150a080a0908030903070b060909030405040b061303120f0201140f041a090d09081b0d110d03030606030c020607090b0c15180d0c05100b060c 73
    0xc2d40c0c80c0c0701080004001c3c0a02505030444000d07142d10120309000f00201140f0301910b800c05081004040008208800365000041d40307540082d40b0301c2d641d00305140015104d5014000c2500c144500401003941414020348131840391411602a40c01e040c207060400019220a210066210034140305a809142c9040d48000003035100b8201401d8002e1036503000341103c2a0f0b01078074010740e450300b05090031843c1c04010311588003000c520000700c180d469190004410381c6122021205004600c00c0080c0c040e07000460040000030390f00c610400c0c95441100f2655100003030003201426007043c041c1c106c07a04000702c140c10706511070141c0849282e03034500410103000c510765040d40040d484100402202e90544206002d024161000e44100e02d088040034042040e244141d4049240000c0c11516400051003052031740b03201c04084055609003000b551424244a00c8109400c1c01943d4150341824002e65001000d40c3d4003070081d01401307006a15580040c07030080a440c0e08004200200360110009000005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 413238246 1250 413236996 413237017
    0x60109020a050904061e0b040e04060b120d020d110f0703080306210109020f09061e040906240501080103122d0c0b0a09170c0307050613021009060804061a06 69
    0x1b0064444c480302000303c1519580304a01c08a001c00042c400a06582a48c6600541201000c0796140300c6102191602c0d4000381c0c41d0195000300000030012640c045003003d0030500c942e031290807607002426803d403581d00e10382c01601d03698811942080022819070146900c041c00030103400e05502511180303212035280d061140324a96446420b441140361502045642c0322060366128000c0c980318000c10362160407036950f44a0080d02c1ca2910301e03240c0c0d0b55000f900d0021740c0034400340a5220a00e2409000080b14186001030321050313503011a255100c0c01103a4100d03900500d50070301307044040505944030a80c0301900c000400c4940c110b003c011007414a080c060010f030341d03034001c08540c990400700032580028140c0c0c0c90383c44c1000507400114542c40201100c1504000409a480600821031403851103299001041c9000e00c2d02001500003180d205500c01d94004d50307010380b160b138100c0012514484540038030004607081101007004603195a02081e0600509840f1115400e50301000034000d420408103807 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 413239496 1250 413238246 413238269
    0x10e090a180503130b040815150d0809040506090f07080403020c0607051f0c050706110405121f0516120f050109020d060807030215030c070c1409070c05060109020a05090406 76
    0x13056600d400508070007045002c0d0310a0910f130a02008940300c40b03c481c0b03031113610714000010582c03820b1309948080d014007004105400307175049840c3c0310240d0340000c108548101d01c0d00c0000b03030072410000c0c1040d10032413002c1c681c101c1d1503681d001c081d10481c9010b001079045105612081c18240c070740c0c0000b00403080c0600014600c5007c4480880803c2c1528003c402000e4100305242100b40d030000c0584d000c0c42d500400c04200c1e100c3ca1182240140581c0d4401503000060b900d0102d21030401103495491300402a290079040b01000740c110081e503c041c0c52190544111003005020b40d0700c2000c145604074010030022480d0b000301d02c5c00368140c90081c0c0002000c03035400214414040c141c4d11445004146032009032a2261950f00040e11a003100e17043d8052201000001400041141048408540d80b1502d8080019280d617010313800e031070380c0141d06401070790741502141c0d445004004601c1550b9208005040e1603090628040c061b401503190702007805400d000440b8540d40b20f00800c8003500c0c10a404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 413240746 1250 413239496 413239507
    0x1207171c090602030f06010e012a0503040e070f08130f0204020d0f0c0e120606010f020a051b0f0f13181a070201050717010b0f0d090b06031209010e090a180503 70
    0x202543c03110046c01290601100340b4032500700d42d030044181040c001943c152050101741c00c16000019070104040104140800030740410307000001309040d8024600f55803081050380e88002c0554210031305440c0c1800450b509605800000c03211580e18414902c06030003d800c210514401c181038401d08580ea1644945039017070701500039400310003594080070031510309114801c496403070b944030100a030a090400108800508205000b005499511644442101e03c52030841c01c15156800031860041d11a1001403008110345c500607113001400d10004144441001c420804c0074001c0108401010003403212030040c6021480564910894052011050312140341886000b421a500241600d042c051090054007022403a015464155840c441409541c1c003203461010581d4000d114103000072504105040042025650300769020300c070254100c4800d081c03601110219409040c0e01c05001802084d458101d52600d250155000103000360006564081040c10808544866405130760503400043c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 413241996 1250 413240746 413240761
    0x308030a0902090603011401050d02031603051c11100f0b0d06020415030504120c0c1502030c0d1422090615023d110a0207030201021207171c09060203 66
    0x3207407503010100310007c20100700d24598900d400781d0180510760203680300e45d6200c011902d00300680d46102540c00d00d0003c00f5641da280c01641c1d08203218032003599030b40700800c9112b00c83c044c064107160380200c2c0d40a003501410030490030002b000c3c0305600c10038082d00c6229800041c0c8850180141560003620013581d00e40c1480d82070003017811a84a0002003600e031500308804030701e02103895441c1c408036280000e0385080d103041c5400480081c0d00880c10054940100c996a00c2e0000001c00402a03400d042d100028075405e01503400c1c60a00342e07803511070081001030300305c02590104404103582030301c88095011510340700358004441d000d07040089618a0a01d44845403901080009410582c46828000545440428001da81c04032503801c616800141120310000c0309542018201c0f590000d0002d4451381c090100945e100030f1880268094050f110525504d10560000c803011305803c811080314221500050690700d60200c00141d07106403200b250048000c050b03009401400b400b5040150712420042c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 413243246 1250 413241996 413242009
    0x40c0c0302070b0910081f0603050403020618060705091504030c051e0a210203150a0c0801081903120f02030103060e010e0d1818050f0c0f040b090105040308030a0902 73
    0x420211003d002800701c041d1075a0343d810503280c40fa5032441c0114550b21001c110300701c1140b08400810025074181008100c46034181d0225204a00940c02c90b44151113400410500003000300c1c40e001182c01c103000082c241c6004000804c6500c10180181e5010012400e043c5500d401c1508122600d0504220401c0350b450115010706032802c0c0c0300e0044c400d440c080742c0094400c194a2050544061085e00c101801d00000c0880e85586500a016509001c4000529442c03100c402c440010301149004034602c0d4262003412070905850188006205080c5808801c038181e002e410011410400700f144085c24240c454064200242c400386030141e01c035411483c0420079112264a49080d60b80b40c913400350204000054162030780201c03410305140841c44003840300e9001c681d641005240c000850354074800030526a01c03041c4108054003440d400c907190140450b00e0780c410747c005044407807002e000c01d0200004142c02400f604105040c190b1600d941c0c0da031465560741040f40c180b01d00d60355030511907040d0b09081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 413244496 1250 413243246 413243249
    0x705032a0604120605040f1e20241309050106020d03020a05160212030711031501051008090712150c0201051b030402032506020d021501091a040c0c030207 68
    0x12035400b420310b4245416042c03010080400545826151004a401c0c420401c0038461584d4020041c0418500207001072139050314411000c84a00b41925400301250703054074070741234102030b0003003100c120f4100107100e003130000f074190160501c141000c02c140001801d030321038180010031040d400441d0544c1340c10700c041c1c201040c440401080c5401001561201070f03020044551500f004808200101d05900200d1004400d440d041d40c3c80d8840042d04100340403505034107910a02048007101ca548045201d1218032240030311070f5580040d1030080c004002c500411005602c0070080c01242c442542c1c0f0301c80e41585505446c0d040c0d0b08d2030107144031900c9400607409040400001800240140d040c0415540c1c4c0044000030107001075600030021404541e001c0c0580110007180000840400c1c1c2100f011060003c0310348201c0c4003511640d107100d03403030074004514040c4a4100303900c2e86445038680b1385000040d000504074401c1c1c0b0b00f00e00e00c02a02c0307941d852090713207154010307640d9039a8018510728004e8509040e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 413245746 1250 413244496 413244499
    0x1003050705010c03090501121b180f06050f0a020c09010308040503011a0a05010309020109030204060b0c060f1b0901171911040b0f0f16080702040c030b0f120705032a 73
    0x1004401011031780203016201200c4003880c00454000e03500c008200249012001d5095146803203410440d241e602056400b201c590302000303e502d050351142a01c8035031150784a10008902d062103400c0e06c0c8ac860a0103017010000d01c3c0142c07016a10120001481418243c0048401840100d01480182001d01c6211120034080009054101001d40043c140d080b5a120b010304040d210341a04045910403084000210790280c82032018030340701c02070114250001a11615544204400035940c004074031903050044401c64111301005008004900e0194050300f2104d048c06804140d04c242d00c6040030420388a18240719120f2198818010002c058608803070748c0c0014070500303010500c0203c01c00000c640c0d400070110130740e0b03584074075261005469000e50a08405500224400c1c04140000074000b040c00910071181004000e0102005030100c540709662310344c0000030800c80004c0e50510b114041b0a18850030210f4240310341e9040060f03c0e142880b41060b9081d03038640f451003044c071032000094000810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 413246996 1250 413245746 413245757
    0xc0306110a1d010201110f0711032a06042301030c020c01020c060a03110706141b18040f110909070801030b0f280b01020d140d0506040b09100305070501 67
    0x6018400406103090690741620386055010a00b1543c0c0c000d500800d24003400640c2a502c448180c1c40c100b8842c2c0003c01d003507400d400358240042c0700b49030109a040040080b00c25102c624943c58052040d400811000c4607000a401c002c0441c500c0881e4801104003040d030400c89145090035400101903500e07200c074010566012031003030912686c010401c09040f0f14141c0c0c07455194500c41200700c02030922003040040c0b101c00090505d042c005a90805002420041145116038982400c044444081c000e0800c4c01c0607814401580b10f040d40c90904000b80c0c20041c800b251410b105000d52003101c0640816511611000444103410305103c08030581c0440c3c03d08080c8241d6255071036100c0003d2004104090741d03000c0000040005007c00c48820783c464924140402043c0070721850ba0051100710202d40c054800d1400e8a600300303200328890107405040030501400c0178488a12403015000107400d10ba4495181d180f03405194445c00d00840c070070100c0306540032689103107080581c00c20441e500040e04000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 413248246 1250 413246996 413247007
    0x603091e0c0a0501050c01020d06080d030e0d0f0302070c180609050c180d0c0b120103140d020319020106031b05010f03020c0703030c03020c0a031b0f050d030f050403050a0c030611 79
    0xb91652a25802c075442802c2050780d4000142c801802485a1070480d40340e28a000d0703010840e8100000c017803507403d5031602e003084400c1003107101e103076100c84004518000440c02005880402c3c4650041c0051622401c52001150b40b40c0700500c1440d00201400c4521030b03074a16003003216030481d00a294002c171700740348094504191101c040c903070b807a0800901402201041a450304012121a005c2d008195640300705458211003160124900700c04c2c80113451112070814224807441d00898072891501c06134004501c4c0c442e101043d6690011881c1440c42555a140f40010200b4594140c1c089802550084486d400d802c110025101d41003412200c0700301803041c80011a90080000c52005403601818508502c01d4140350891070449001c1a141d0004440c1000208000905003560805510402c2c041000381d00e50b601101603010501c507003a0b10007502c1183e140880d00030596250407880900e03205142540784e450f0b03070385232510f001411101d9201925041040c40500d200790061403802418492400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 413249496 1250 413248246 413248249
    0x19020408030706020c160602030306040b010e030706120204081209030d14030c0f04090f050402040b0114071e0215040801050c0c0a02090a0e071d0c120f0601030b0603091e0c 76
    0x20300450000801d0f4a41c006180380e900d039410028011100c400f8407801d0b0402d622400c0094403501b094030541e0055040816404440d03020f0f000740003d408014000708005480c0440403901e00c20803140d003540302c5074204004100b0150a0001c0e0420300d050503c615034030b0308000c06045ca400c110160341d4042000d42d59202c24103044072022241c010402e900340c2c3c0d032228070074104001a44981c2e40900e4100d45030202c04044204581c1140303116900807541003100c031400d100103590020713040c070094004100030001200000c800c0d9a40c1501c40000203c15043d8551a602040c0745014204506490440c007040401061400340112940690325000d018140994140e000742d03101940b450083c07103001601c0005800c43c0b0b00d5030040310944042e900302c0b1540c6545400f1080c0c1c1620039012246000c0c40340c00080c00308105038080300e68455071488403171813650381c2e40c07000d032403480e0042d2101e810951604140003156590002660043d401080648911311064128011440882e41109119008190b01c00507a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 413250746 1250 413249496 413249503
    0x708060906220c051c020a0602030a0f0c0c03021801030c12031715090c09120a030f0809030c0604060b01180b030c18060403061d06090a12021501060819020408 70
    0xe08044000c03050b0402603140c4038240900607085503801c1403d25044416400004400c2c400741c0b40280c0f018051035864040498507803044920000106079228030280c4014892002890740c24022090074072aa07489a0010b014480c02c0c0640c103150313100c01d01c014070501090460440c000c10346401c810003609680c0d50044e288904d101d2800780c05c041d035280007032010521050000101d41c4018440140c601d0403045a11301500051003040c0034642000805202d4440015034066960701030b104c054007203125044c00c581d10107005042e0b01d0103001c18085000030a0702002120b010b60f00c104004194a2600e2000401911182c0428002141c541508000c002000d40440c1d03003128030404001e0355070301c102e00ca080c0c0400c425014107412400014001040c0403d941c0144500030300380c0440c50012100106407903840d1802d03145001240c0001c0032040001d000111000003441c4140180c0d00c80c001400d81c80041c00109a2004d40482d0f000020044461011082c60003546030313409045042a0230300304030654 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 413251996 1250 413250746 413250781
    0x40309080c03101a0907030606020c0402091c030c080a0206070e030316081e0d0b040b090f0c070f061812210c1110091e020906010e01051306020708060906 68
    0x42e03d580c0c480da00000c01c4000200720007100c2c005400d4030264184110024000e081070b2160b803005020340c124098242c5031074000c4684110000f00140c540360301c000181c040c2c1c2c0d00c1151003103041c0071a0600700d0000544038030160848076a683c0103842c1e245000c500180000c0c403034040851003900100700d640302c0c400c401410101b40c03a801c107520f55203500241c0850f804501026410302240c00c00030072440d04d5800f041c1c0000f00011002d0700d051040865007018030030340210566510000194010018107800c1030300d005030104130f00400d82c3c1318001519440341c40448030f02d120040c2c4140034030441d107000c0c40005200701500d154146810030820030403261413a4001d90b068401402142c48051100c00c1ca8450603541914640d40c1c003c0d120800d0103200303050024001b1520444141d0380443c1010210302402048100300794014100790300f599134035401141c0e0010602c603c913041c09001d20108411000354170080001e80541c1e0000d180407414201e01d140380c120b000303141c00c3c02c82c1e100e9010428100d00e480420b40c1b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 413253246 1250 413251996 413252023
    0xe100504091509020a050316031e020d11041d030d0507020319080c0c0123100303050f030a0f020301080124030f020907030e0d031b020607082a03040b040309080c03 72
    0x207000100f0740300250341c03c9280e5220036030511905208100080c18008100100ca1040721118103008141d40750340c20305070030100d000e07511040850140c030100311000c0e442060070400031f000103007034192030400074104800340c4039007581e40e8408901a0108602440b0303054200c11640001c50920206520030b14501030b0ba590b0030820002c0d1900828510705414040c4d03500311600074000d008616007200c0030342c983c0f00011924070659014034045a50540d0104000c01a2038041d51818030b0011100c3c0c10102560015040e5a07031155210310f03580708036605102441c06002014004200c503040e00c0607150490048040001c000010201d082000480d203c1900d115a0390664220001c0d54400c2401e49c0102490b83e413101c01e5000c0c0c8a212407456a051b40f03d201c00c22001c1c3c401d0b1810031080c1d40f04a175152002c68000011494940115003615074100c000c0017070283d4401c4021101080c110b082d6096001968121030500c0450180401c06400c244a40080d000315001026032030f0001000940d40e0742d0748001d92 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 413254496 1250 413253246 413253251
    0x1140f06060d1d030c1e1b010e03071e060813020906010c1e021f1205060f12011505100f0e010c0209040b01050103061401091a04030203070e1005040915 67
    0x101002826074000c40c0340701c906800450302401001c1d100d542c40f070344904440c118a0042000c0c0300c8000501c80e21b003ca84110150080288112040710030081075410b02001e4140311603213911096942e002c01120b00940f0215100b400e030461440c902c00c0750002c00e81c0000060000e010104022410252907c006c802c5c0c049400711043c0d1910801a9071070b9000441c0502030221070248081d007000c040801d5030341d10b4402d50b02c2c0303201340071480c04410000d0544c142090000310f1001c03072100981640d4102c66080480201440391400c8801d00080700c84800750040d0f200343e516110400950322000c0304140c000e1030152608841206002002030845800320504000d004910001040341d902c60609800c10039809070400d00030381002d04241030400004d104040c00030b400c1403008a44d400301d66044040031f02341a111040401c0c100840d04d2042c40c5550a46074804005020000160741e0403c80c81d4020100103030751400c141055400c44c9a0041903400280c0140d041c00e05050014241040d905040310400400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 413255746 1250 413254496 413254507
    0x2090607080702150c150105181f05060406230703020d05030a060905041505060109080d08040206070602030c0409060806010e040f140106091a030604030206040209250c0501140f0606 80
    0x1aa01e40310315194861125404034120070f080c417001461001015003514080e05c6607a840c800c0025000700750500540c0401d981000c10a03032035141484141d284050816441c40548600100b0707419002580020000b5a102d600f801c00001c03c80407030005070700c0d03403c1d1080c030b8984107844c065a18030481001d041080400800600d42c8150340e881800074040303071b0000303200d2030801d400c101540c42804000c802c807192030400031803100e41c050598581140e1170103028041000c440d0106880c0f10600500581e00140100811000160184000c5102d0078800c03220640759424024100c1c211080398102a0660348071100600080811099031540154000514248840030f0301e800c00c89001408184000c5600f0145d0100c0d1744407068104400c2000d64201031605082c900b420583c0c0d600c016180940560042008580581010f0b416a50f1200340c50301840c0c003c15050a0280400d10310f200802c00040d028034840040140a024070003118180c0d581d5200e407820410131591085102800309489082d00044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 413256996 1250 413255746 413255749
    0x70e1216050d080f0a02120f0c0105060103090b060607020607020a09050115090303020c040f0902040e060a0f140703241d1501020705010f020a0605040c080715020c0402031b030403120c0302090607080702 89
    0x300c014221b11f0500e03415100e2003002c0c1c4448035a000044075011a5085ca000a06075500c00d108070001c16030010f9181005854040501c9003e902a0394180c3c1c010b80e040000c5409030303c1d92002c0d48010404244002107d40c0741c80ea0902c042c640300740c4103000f0000c81280400100350f000505120845080750300044104d00015400700514071400c1c0250418203190703240c1203202d40892058071444000005210640c943c180e9101110561902c0e840600c21881c081504984640d103e0306e41002d82071206a070000d40080700031000092a480503d01c0c08000e481c2000d1215840c0c081c0b03030084a445a20001d104000380040e444604074040d5074100404006612020f520070440030f84d14642004040016081070708150038400b13014003a6601300d100d01e40c000146806581e100c04c5c03403207001350302030901c000c241c008100203540b000d0300f4150075081c4203080e10103c0941d400190701942c0300c0d4841da403981810407a0303281078a20f503049400074144140032490a03921058101c40705140e001031016640c06c1280b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 413258246 1250 413256996 413257003
    0x9070e1326120405010e10140406050717010b27030d0c021f020a170a050301030609050109060507050304110901050a092301080f070b1c0203070e1216050d080f0a02 72
    0x2480d151520544103110600006521807005015100e05803107150503154040803d0750f442c402042303d1001c0c54000140416115800355412a1181c54a6001a1008001b0150703880080e0080d20750b024001031140c180003048030000707882c07503c1c20071442c05064001c800242c807a40c41c0c5459400b4880c5a4510340d0131035403070403070a21400103031a448103486141c2c6034000f56502070380c0600f191103004000100c20b200d200b11003912507c07801507031218075507802c40d62414040c11140808032010742d25102030100048503800f9080c0300781425500c5076202c1ca010300b007400c045601c100080e80074001d800d0040c066a2070b800c01c01d509880d4004008100359041d82d944a4005541e0b40c00e1101061040c40007054070000880c40e0f07200000d401086400054031400c400e000b6205070070811101c850455110501c0c0c503a42d40280d6072007000740c28a0980c42c0c0a01012031060840000b01e40380507041848588040c40c1c3c42c0302c4035000341100f680d0444003116260b50b54020b502c907151815805200c00f15820b2030b04c901c01c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 413259496 1250 413258246 413258257
    0xc080c04121112010c180305120c070b030c090108060d051c09030b040c06120b0f1201140429041e020a1208030414011517030403020909070e1326 64
    0xa000459a0340ba5003c00500820602c20400001100c0d280810000200c10b00c40f0003c1c5c1303820602901591110511100f001d034030180d41801103000d200340000d0b407440c04601861041c88491086940e0b41c0b5000e00040035158010074003031045144268900215400181800c42c0e0291140040040000340000f503804458542c00109010948002c120802c001e1920381c03012500c4a8944c0d410120320b0f0307001c00c1e0a55034484100b07500000c02c5859000f55150030343d958800b000d08040005031103440c0c00411000c1d503104070307010360701e00756281031300581c00101d42105100041c1d61040301707040c0d040683d1910b48580c210032103805c015242e140b0007825580c8146408004011204014100e41803914101c061504101d40035070302000d0261580034041c80600600d070420003441e10742075405d41071000c54061101c29604155140c801400084016150403050501850811000b440582c3c540030b0070680441000380300f1072448002c0e85d13007400003070201083e402003e480c09019010320112121140c0702402070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 413260746 1250 413259496 413259499
    0x1e130e0106140910270204151e09060207090515090405100c080603030304020108090c0604090605130b0a0e060319110a150917011803080a0c080c041211 67
    0x74031100041003504a11101001802510b81d240507503039401188102c1c0210384a541c2011204401e402c1d0402c3e4034201000c072005441c403005003000c0d121918405c1d2034a0089181d008142040c80c580c1460341020980c0100c100742e4504004100d04144000f03440d021709114030f0f00c080780c840000c070700031112807004000c000101602d54000d40c0f030241440da90b075122141210b29035503d0325202d40700d818851b1030200d200d031034090300440ca0b50b201c5500440388004010841e200a002e84000c1c14025a6402c0c0103100400701c058020a20b00e090004000406800885020015240032507100140e10341203221011161090082503250380d40c140428104544201c5058038458503c0c001409c00001c240c0c101d0f1051015601c10b01116200c00005015001d01d1203400003085038958200001500042940b04003041803001183c2104d03074010181e8000300e1241c0440201e02100300f0804091094410fa20324400203107071a0400382040c510800c003502c06e50003141e189220561400042c0403944e013255448080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 413261996 1250 413260746 413260751
    0x90f180b060c0114010e010915060806180c040501090e010e0103030c03140301030309090c090b1b0c030d03201810030227130e0d08060a090903030204141e130e01 71
    0x48104545503445424086d090000082100126500c0c040e8800e41c4401c10145840c50076031380c03d1003002d42d404c81e0020a080e0740000780ca825442080d0380e14a030180140409094182c03210b05000c00904038044540100e8a103800d5100100041d0f00714149070390440780c050510030082c0e90142001c48440d180c148600300c511790000000420941e2100d0b15004640c081c00042182440c8038104032004070315172060b0300070000c05000034403141130301c03044103991000301c1030880d00841c081c5000700e802d0100c0306207484082035441c840d400c4119046183c1d00d0440000701801c40c500540d02e04000101c0d030005051601403004101000c80041c020380c100d072002c1d00d005000004089601084c0c2c0107086508005074051412240c00540101071400303072031445070038000a4040e00e00c0c0300104952552004225540c000424000000c09006c80d20407071480c3e90085c0c0e005a99141440c060700c803021200803090340030b03072a00b8840c483d5a10520282d0002d8240c04c941c82100f10103608802c801500e90300e00c800a4552 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 413263246 1250 413261996 413262011
    0xf1f050306190b041a0915030c0c060a0b210d0f110a05100b18040803150904050109022103220b0408031e0c1c0c2001090f180b060c01 59
    0xa503c0300034004684e00d4840c2000c1c1480c40c1c2c2480000342c05108110307038018280c5109460500c8810020759800f46c0010034440c01d1018510040e843c08100f03607a403030342241e9203e00b40f148500b00016a003114124135080b00540308014900039a070707882c0860351041000040c1c03d2800400d44240c501500c1e4001000454041440600b46035854404202c400500c1c903140c101c0441c2036040c01d41158120141318542c1c400c6540d190786a2003070560004000110303102c208603503000181d84a09134107000f540904c000050309092841441101100000d540194400620384007442403000011980e5a4500800300a907010400760b0a2101c0d00340c58100341a2040c0219000c986800c000002c0c02d00110402d01241003c61054034240007881b5102c2c7c920081d40140d105460714404103405014a81d10710720f48280480410745031280c0c0c2515003c1140c030b50354004846000740d507a0207220903020780000080688480e18149084020403184800c1035100e985600f00148969100000d8400d01e02c0040c000340001c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 413264496 1250 413263246 413263259
    0x6120f0611040f2d1a0706020c060c070c0b040308070201050703031d0d020c040608031603021f05011d0c161a010b04150f0e0609120a060b0f1f05030619 67
    0x415400d20f418841280c0003166008140c801c0c1c1c04d03508880415101424803030300142c00407825401200191034060302003002a01c01801007104910a24032625201c4e01c5c0c0c100e40c581b84801c0b5410f54880c4c00ca00c50107220610101d68000111003001e60309003407144d0744028a24003070303001d011f41da206847c400700d0381004259501004102c0d02c5844500340e090f564090900002c0004441103400342034032590090060380c42d90f0840143d0380c2e01090007401128010075407070b010b44440061055a050001da203c000400954032011802880e01200752040c290900e0700305074900490160520322003400488103406000d1000b03005800d280700507801c1c40090a0f42e1141c0f0490351035801392081c01e55180000c240340e24000c6c450000b140103030f54513a41c0c171110aa116001c100003500960b45072a404103501000070403c00c41004541e022510903407010038080303000c8040049600c58140c19500989508809000e0525108030380d040080c40c07401c0007612500c1c0c500200d09900c0301002c1c80112594441d8011400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 413265746 1250 413264496 413264519
    0x130f0509030a0f03090b06040914030d1a10170a0b09101406070b2716081b150a020a0804030c080c0103020a210e1f06120f0611040f 58
    0x907602c954603079403c3c039005200100d0403211042c50240000090102252451805405c441002406641e442c1c003c50b000703510300350171580540b01c45110b0030b0392100c50f200000c41607004e0b1081c82e401200c40100c09900014050040c0d042c2c1c5404c120120244000502d000b03807203500803401d6040c080d089080d02d10304580c01c00c001005030301400d14259044100340f502460448215521749a100030310300419194000d00c05510341400000c00c02494240e05003101c20b01c0c0821803881245e40c804c641203a81303450b1000e21410291030001e04004254002140e20030b54451400d43c003010700c410111365603160100030040f030a016107080000d020090000b40082070041e0348040500792060321040e074050821081c0103404034864500034401080b2804d039841c1c80b049c00c0000741d1400c081c001902050f02d503a0014640e051042840040b03204500800a100312450140703d404081e000c040b600301e0024000380c982c07002041580308002c0501d031301e46000c507860103510340545005012821494103002d0720f594140030f8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 413266996 1250 413265746 413265757
    0x305060307050319080c011d0a150213030b060f061b060a09031e110319030e0d050316030902090403080a0b03060103022b0503040b03071d0906130f050903 68
    0x4a48034952001c5118030b03010400804031800b8203a80366021040e1750b00e42c0d4458220500d002e42c55580c1d804c15091403101010301155080c0720b1400381c8005441c03031600d40c0174000c1e01102c50b10740a10512002c0303100c2a8940414050f2500800120144d0343c0d0400001c1185006130291904000045414810080c100080c1500200c0a4003510140e40c4c030311882c94201c903481c0802a00003445044000741c00150300c3c0a0402c01c3c0c80501d03110780c0d402d40c2402014a1a0301c05056045420000c69101100c90f50521a42031416010b0000d04803122003684d006000380000703851045603004241240d1400c0d4003d0307119001465000e00300320858980790030b001e000030504403031842d0810b00b021000699441c0c0411068141c8e075000b40b0b802d010b0025a107840701001034918402c1c030006180c00890000c00d000700086d00c0100b540d0341c082c175540d02c0c02c1140244040380104181207140d0030984a4901540c0c0c8440565000c0c0b07040e50600b8442a895201c81c01400d2915822030031580340c41c045c012803c0010000300f9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 413268246 1250 413266996 413266999
    0x1e1b070606120c30080a122a090806070509032a0424031e06020c0705031203090304120201210506090603031c051005180a1a01020d030c02030f0703030506 68
    0xd86229038800718001c0c1101c07180030001113402114030b600016804c4c0701401e810b107101d15210095180c4c500c0640c0840c3c001e0140c0b1081074503001c01c04e0f40c80201080c0401012440c1c0e240c1151105d15040b0126540d0324007030018070500601082001e29520304110100c0e2004036406224580020f0814508140018848042c021030a100e410040180030f4050080c4040c0c042c880044000e25644642e2603180038100502c075642d0b03250144802144040c00540302000416016228181ca0101054544001d07003058800c0e8660038410030241000105c10f880403500314400c8140c00d025540300481b41c484291f02180d4010031207219444940c0001d42c0002d102e07000c04e40d25010349494000406980780900d90340100c000756a81031500ba0704120360400ca40107010302c0490300180303072901d0008000990980000a0300480c61042040c88800c9005400404001101400c508090000002d4584982024942c140b54540a07500d840b071f4401c104845101012059990b1507080c1d074513004020309419110035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 413269496 1250 413268246 413268269
    0x20306040b0a051b0703080c09131401120f0f11040509011401050f060702010c1e030203030702190b01032613050a050a0501090612020f0a03051e1b070606120c 70
    0x11210703481d42070201044e101c00f00c00142000c10340d030350490704e218008107100788070a820702454005869061806092214044010403100040041440c00300e03016031100500d103404960280c0882d121401c00b05090b500020090054000d44c01c006840282120b5410f801914010400803844810b5101103104009100b50341d0107a6a95000c0000b09102c105199a004600704400c8005602644580e600d091103801c103605c102030321280611207800791640a40140e0400010070032100da0522008500300c0c0c0c00c09180526410686a4002008050000070171005004c0030628408508401030090b91400c000c500e59180a00341f0b5038030646a091048a000c0c03035555102080b20b03d455075219054a0042c0d5402d0340b0145415011102e542c070034008903c0e0300e6800c00c000c0d00301c40f201c0b900400c3d000d43c0c1e81e240403442d804c141a0304041ca494207100c0300501c008001c240700314444540940401c011030b00304003d0300c03801c840c14820018407682d8040035006034011490b070100650491010112850400c0d06c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 413270746 1250 413269496 413269501
    0x41b0e1303030506032b03060902040b03060306100b09011103090405151011030d020a18090c110607091401110712021008011404090c0504150302100e010228020306040b0a05 76
    0x307140d518100300f0700169054030300b1244114030040341590306c40c40341d13094900814031903070302c3e0b000c0012a81705800986540304000208910350408210581c1c200c490094900075140c9024408078181c00342010311810000405010b6030790820070410398000030340c0108200300e1800c12807003101e4000049032406e80a00c0712800240081c9001d01c01030101e40842c200592b18203020a19030310000e40c0110b40c030105000c0d4106898610b036024000c2600509440e142c00985800d850101a1140850891094480c1d100360b04100798a54450314100071690720240e0240150300560043e0780c050080c8400504900c0740e40d00005a5290080c00e4145c102c1c000d86440c00050b0054101301e90000003401202c502421103840d61000f8100b41d845090241e004810708500c43d0b07200c40015094990403940c010703d03d1041e480c14800c0d40f400d000c10010080707250070240b980061001c0040d460381100440060468108000740030010700c000031080c200c0394000c2c162007440c505460003d540140580b00329010701e103070400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 413271996 1250 413270746 413270749
    0x30b0102010b090115110a080a0201050c09030c040c120e030316020f07031106070606060f12020a120e0705040204060512011a0712180f0515090108041b0e1303030506 73
    0x2d001c5810b04081c00b00c4040e0f80c00d150415800c0c00e20490178004018000d151094006410b100358040584500e44150b80c40d0002c003002400d40300e0190507030090030010410a80c0e40c0e0780000345040030b0700d0282c44c0440c0e088013406050358203100051420b0340b51800e004680c0c0d18807034080029446284824004601c20349124412030781c646082d25061801d52000303c041c00031580c100941c03100c00d4001030a003407410280380e403820300b500d0b07a81d4480408a004004e803440300341d03084140104280c115074000c6040848a06e4001c080d913010207503000d0400d6803514200314405003441880c0142c000a0801d5654946e1031500500560102d218950700060150010505190548520f8100f40202640341d0404610391a43c405032440e003801d40b02800b2041d1302161005407900034020003081c0b09645046c0c400d103072006000030080c04141410500608020050541ea044640590059081b2502c0960408003615070043d00f65142c10034084159200c0030030204081d0001c441010700d100359000d1010392107410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 413273246 1250 413271996 413272001
    0x200a06090f122f190303020f0a030806040b0301060905010e010e090303090c0609040905060708093a05070f06050a0c030b0310020a031509020a08060603130b0a1d0d030b010201 77
    0x10b60040508141c080340e5402841003110158030b500024031426000d14076803002404031440c40c031101c060141e030b0110810505806020801c030a0810754080c282d1182a50340083c00313080001e203814400c950760a00d00d00c2c60b880c01d600c0b030405030200308030410040d40c60f5038005807800001d02c55280b1081c41030001481d00d103008015640140d4848004101c1032800008107d61604000400340d0007603541c0401c00d000c560f08118135800b03054152161209401c01003010b80c145103200111180a1031622951590300480b501010522448818084441c44090004031164803955201828001c003001001302400001d43c002070007415400003c00c00030456040c15001d48406107000e550503000b000d03161181200e2600100142586450005440a095024031007003c485401054007594003048040d0308940015219400501c1100d0aa0952a00c1c8100c0342284011600c01400071041d40d0119514040540001450390528407102c0900724440780c105680e14203002c400e500203400c1c40c80420a030750041c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 413274496 1250 413273246 413273279
    0x1006170703050a020411070b18011802180c0c0d02061009060506090111120a08040516033c05030a0212030c041202030a0b04050607030b0a0b07200a06090f 68
    0x100182c81d84400f140c08000043c1080e01038444100000c0180200082d901541103200e1081a1311401080485031304c1c0d82d0850304403115007010755080034818409669006030240132011900c00010071680c40c25954401d902440702c03507101920030b03800c850060742e40104885226142c10000c20203100d036070b0b4080e04140d0740c1c1b610805420200c100a41d1500354071a55225407a14a810b00f110076600b80102100520b6000c10202d030700003041e040074442009002d0000384614410030800900c0c142c04c40e25580183c0030340c1411684008040d009640a01d1a420420b00f07510041414075034401b0040e09140d500d80e480a2076860047c0100d0000000000c104002e036409180b2201c1800c0c01c1904015050b0b0b100641036109071f07403502c00c540e80c107400a03080705c032051300c00c500c5040a00038904040401174190341d0070080c02840f40c7c4403010203020356440403050303420094000103440400e050b260300c552a0b01c041401c1da503410074001e40c0c5c042641ca81100d418001c03948403407440e8410a0f0703600040c01d401c80e0032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 413275746 1250 413274496 413274503
    0x40e010e330708061503071713030207152321091905030904051e0702030301150509120d02070f080a0c060507150f060e0f09060115111006170703 64
    0x250700482d244a12a0304480d41c0000c016100186140c0c90052009098000b214500001110103d03203480301d25842000c40e81103541c0864011004034166000394031161079029049503812000540e91815104da0014140051520b1004880c0c4030100ca41c00b015510030070800b4012100d608402991042c2801c0040c804c43c01e150240a8050812050f008041c0c12503a040e40d840c88103000000742c0b84d0780c612409002c0c0360340d2100d41c5c02c2c0b440d1840c1c5459506500600003001d541061004200c4506400445051f00c9050310b40780e5507e41c84400000e403d01c1c0005102d82803885511003602c40303103400141c0e510540d615680c484d40116640d0081d41d598054001c4003c00908881c20308205190041001e008902c0c411b840046025040a42d01011180d03001009480151100802c000c00c0420b28a00341d0840300d2a2844c9405280810420350b4408042c42411a6604004610311011388920380342090030010006aa03950460500b03490050410303401120306203458601041c0c600500000d0f4402141d50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 413276996 1250 413275746 413275843
    0xa0209091b10050d0e101b050a230c0a0b01050f1315050909010c080a0501050904120504080f030c0c030a0f030e01120219030c030e03040e06040e010e 66
    0xc05405202d00c101c07010b2401c2051100a102e202c5407071440b4050318a0b5441da0200801040c0c40406102c820b40f080244a11041d1031071213404050180e200c000c48084940030f0414621800c10f1051103540c6405c4121054103206012038201c16080c4081a18000075018590810041e6210010010003540c07840086900054000080d1609083ca402035054101c1040100142030390f0769000c210503200442700e10601d45d40d9040d07550b00b019046034415405c85c58000b4200180d40c10400441e54004005d40050321022205199903411031203101102c0203000d000e015180041d01c0e00d81d52a0790b94000401401550282254060060a0010b41001d0329a04525008100d50f01c40d2426100c110748011a80c4c10400d50b41c40240000103e4001801c2c68400c2483e42c6642c00e030714400040460b186646900101030800ca21510500070004c05d9400703640d0000b0402da560380340c600024009282124a8240701e5007441314024103868003003070a440058030b004000041d000d10380303c112941555040140034050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 413278246 1250 413276996 413277043
    0xb0f1c0b24090c04050a060c0611040506160f02040c0c050c180c130b0427091101030b03030918040c0611060103030305150d08030703110f0307080709090e0a020909 72
    0x38140c82403036041100c25000600c0c050321703880400c2002056400800c045080c4481d1942040114400c0c1440364007405145402e090038076002a88510820a001c0c60040051f200072051020a035004080355500030401c0109150680303000d0001200c0f4401510203020321a107000c0203003000c2104100d514440a850443e41c1e9884212440e943c20485411940200303c21010801004000040c00503058020032212018420b8a6070008099800d070b008101a040c5101080020380e42079060007030317460900f0041015030020020a165000e02260740d0760200c1e41100760706068614a5585004034042c1e000c000350309464900030782e161032401c40500801da000000420119200e035101c0b54101c0d441c0001e030800b89242c0f0000801c214015502a55100c0000040c0f018050f0940304142c60b04c0741115500e800d080d40c900541c2080d000081000d000c1c0080540040e2031140310722010400f500f4110010003840c1039400c1000d90f90b1140101c200d0252103a080441d028500004501441000c507448264491 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 413279496 1250 413278246 413278249
    0x80901230414070b0706150617010611120d09031b0b0c0313080d06060216080709020f0f04060509211c110304031410050115030b0f1c0b24 61
    0xb08030510380910b00d40503409010400c0b10180f0b00510300700d40150320100e0082032410035555004001e030310080c24401015248548100c1c05c0c10182d044854a00344002402500a120303400c040301010b90014901c00001c422000c075660f9400050004d020b0759980e20b4040c600030000b607403040000341c0541a0307820a000680d2007420301009590020801000c064a2945503a400c05160800c9a0481001c1d840d400b081c80441ea04010a845088450b0b40c006012480e00918948828060282c1900c81da000658401d0311001201191409000b640304e2664456a900c2c004181c0e80014001610800c00b800d0f0401411440003400b9801913000005032841a080400612590803d110743e0f02c14440424100800b0140620103000110701440c2c103419044012501181084100141113100c1403405006000303e024640c000c2c4410700796400d002421118282c005483c11b00b0802f81c1030340c0540c148035495541002d103081284218400c2003a4403194482c00083d110302e903001144100258285951a2a035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 413280746 1250 413279496 413279513
    0xd1413080a18030614070503150f0a0b1303050f01060f0501051303060513030207170c0d030203040b0f04090e0f0c0103021b01050c0307021009020a1814070809012304 73
    0x1d8940e1810102c41e040001241c805418110b9442a100d00795590180a14180c1c00301c601540a0140c1c540030f07155240c4807000020024041c0c0c1c00500071841341c035542c80c40361a1150384001a0503854800b0391544401c402a1100b42c0e03882c00210b515002d4440000c51700d0005008000c203039042060f20000250038840115a1604020003150000f90b031a200003010859500c01c0c980543c0d50041242d26804040c280607150070041c2c1d1041104621040e500c4084440100d03d44100b0348040700c0f174880e40c004904089145024540001c010404005080e001c00000d903002801210f80c00d40050082d074595000c00c80e2118507145141c801a0085151441250300c00d80c020005001940032550103400140d04140c00c4031000c64000315035440c004244242243c0400882c2c0d50703003a440c001404038041c4c59020500e0003800b80314030000b0065282010340c424a0a8006502008c1c004001e20b10914040b903000f00844400d41e000c3d00e06501c1c00c2045503281100801081107080035800210345034885981c2c080c80c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 413281996 1250 413280746 413280757
    0x6050405010f021c0e180411040e100c030207120f02061503011104300f060f09080c010b0f0d2a08150f160e040c031b050d141308 57
    0x214024080004074011031984444070304d80ca07660305c0e8001c401507141404031304c55114130030a215a41d01420000001c0714904006000380701580c0200d50501c220030614079004011000c207000360305084055132043d074164081c00765907004803844808130320580c41c1510a4075101200c2401600001c0004a0f18081900740005101014000240f0301c0803030410000181c2140d0001d00303000c54030542c100f1104135052400d84081d0301550f9101e0000d0b4403a5071710408007403052802840c3c29112a281500003016500040c00c10780c00600c0300f9078030700c0800c1819000f0800400b070140310703805000a0000c24140b8044403520680e0100402c1403c01c0040c01d02030440280c000f81260b540c2c9001004503040307500340b0004040140051940026003402800d60720b09050007800421042c00e05186c200c14a6440140b406006105450006844518a40480207010500320105214004621044100c0c1c1c0c850018019448609000c0215200903034045900b210103a683c030006444a000f00b5001c984018000e01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 413283246 1250 413281996 413282027
    0x80a1413060c11030f04080105060105030606120408133507120516081b0f01120b1302041503050f10051201021e07062f07020f1c031106010605040501 66
    0x3c11400d105494145903034404844070003050404502004942c1c1d090040942008003401c02e0b900713501d002c002007910ba02034000014032804d1000d0105040c0000e58007295030307000c204500c1130041d50712428183c0400100c5810200c0c2c0342d1181780c07100002000c5888000204021340e025043c010b1403c80f0b55124200d01c6030007910700d4010346215900a80d101c80d4140d00501929000c0c010f00c10060b05203c280360403034424a4000c040c14034040565a034465036411900d603003004001200003d02010524040b186d000400500c0e02c00038001c600b454295800500700813440d90144429a00c9130303040e5028800a59800074a150b001030706008914000703d0004620301c0c42d10006041c04041442004200c800144d450001080080c0f423070140b08440c0203150a00307582018000e4a180600c02e00341030201003524092500708042128001c555604461200040b0010800780324020f151204401d1018903110440128002429070480d902c80415180c1c12550507443d42070500e45004015541c0c1d514802c07910 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 413284496 1250 413283246 413283257
    0x30b1f18060b0a0201051f050603010b0c1903030510050a05060405040b1f0f110d08010501050a02010605030f1023040813121b0b0405090c0a02011b080a1413060c 71
    0x1150b00b100880142055501c80e60010890307080440c40f00950020790384102c0c01341942c1e64428807003a00d420b812241140c000d000001c1d51212905101c07806d040d42d0040302044500520702140905a040d0000d42c014800c59903506001c0e0359600810003d03800612845c2e030000000c3c04100001d01d0546d2000c40e10b03400141c220450390303500b98900440080100a9000465010b90030f4100b0f0f04d40c0701c40d000080d03002c49070051040d013a50440142c00c3c00780520031a410040c1c0010030380302480c401e400140040c500641225440f1610b0710a482d2140d00384c02a83c6951490007028030301c026080d94480d8109071420320100c031161502d1729610f0107640301c110300c2080000f0518000402d6035200350300c0112a4010341552803080d0f105180b000c51010a80d001110018087c0001c1c045651100e01464103c6481d442c4070341d90f81042c20307042c4d0160828034500794207807100c1d40110390850b402c250743c40d1180c110b1203404c000c0d2079a01103014002c140160f8541e40c102d06905510000540c2d40e511914140e0000e0504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 413285746 1250 413284496 413284499
    0x50c0904050313330804120203090a180c020d0c171c0b0108070e0a170709060e01062c01081003080c010207020117011203081f030309030b1f1806 64
    0x742c403c03040203030b8007054084801d040544609420080d24901406203030f000c83c0d44e00e8440c030900070319844015002800800040400001540c0204115030f50690040c00e0201c0c0581e0325402580001021481407042504004240d10414070103e800e401041d419110203d61280a4a40880c090394034000150484000c01815509402020481c0d4508250030030204405009600040c681d520140c040428408445004116035465070646010344072817090411504180c034181900e032402c1a40312100c420305e449004a86d0b8201e8010050607568942c5031000203a00b1a41e018524601c201421a001c45402d8001c0f0300030f620070b80303241d60008030a500703082c0591b480344c8400c1c0c00d5900c000c00d00c040e00c0e0f50001d00d803800c558104240c50500300390282607041075890203614508140c8012001010002d00c400020303420081d0710707111101c4111800f41b6451301c1d41c50349806001d8843c28042035858404070000107070f51480f83c44020aa90240303880d40040c20340790203000e9900d4404620890070141d2240130 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 413286996 1250 413285746 413285767
    0x403031803080d1e0e030a030c030219020706080c131203050706050a0f060e13060207050a140c0112020a0e100207030f0b1608040809090a06080a030306030c060c050c09040503 77
    0x24100000c0260360000c0c040324505000e008801142005413030b541e003040540385900d90044140c0d40c4611031820042152500d5050880003846544100e8062046904d1880300d41ca60000b80c1005480c0e4544071600140c540754072401e40d034002c03046480c54510519200b4450b03040840c803150180f07486030801e02d003841c03040d0340c038902550b01c00c0715004070180e5944040c889989060141400404040c1400a0503061501800e03000c0300c400c45002d0f1002d500016004100241001007080107038120400c4809a04012806178495036601c10250005601401180b40d104143c401c6650f252180e1301c40448120420050114008082130800e040d03015824002012420a44429210600c1242d1501c4140313011004501d001b8110440780c010800c400b01003000103180c200c219070b00b00700101d90044c01c039500c0961410107028550440b5050303003c1c503c1c1150400d9050f030064810307240310355520b00080b900c0d01c608071603208500c080034250754416480c1c0030b11418802c081640041c010415207103405407a10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 413288246 1250 413286996 413287013
    0xe010c02060c161a0306190506032d091b210609150108030f030406060f0b0d060806100b0711150a02010501080303070e0f0102070306050a200405060403031803 70
    0xc054009600038500102c1070409540c842006031401004c44d0031880c41d100e01d58040f0740801801c40d4003d8407070105842c3c0d5003506504c41401007030000c0c20b20b83d8900d0700c00065480b8052000340c20083c400f800710600d58500801c5002441046404001c0c0f8211086907103040070850b20314a6541c00504403861800d00410042d0712850800a10006010310309046c4c28040c94801c14941c0d115000c040707800107100141011049942d10240500c038161a6280c40c1040402040d080d0b125103060400c103600040d99100310310103801c200c42500001c2002955816009441704411604000c1c600310502c018005445070202802c071b000d0003003170104151104038010550740a00d090f202401d8031008609a01e030603a0900605000d804c41c1400b55080d42040c2c04050150078400301d441d03100e00c01c003087d444400e9100300410030083d41c0141d406e01080c02e0401155004040301c1c0c003074403040e20202c00c2d11440218070404560440303030041c000919103850f40d10100c89129484008425402c0112000800b091121 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 413289496 1250 413288246 413288257
    0x9070306060806090915180604110112060302090c0a0903051e070801060b0904091b030b15030102030c090d0507030b0103051e010c020d08071206030b0106020d08160e010c0206 77
    0x15240025080e040080c042c002c40e00003803c06200d07000800820403009000b1400c807032610f10303a6000304040d46841c0118076003840c03001a00a041d03ca030004200074031494104113124254207888044481c890b4207204000d6802c1ea002c0079400554040c04605202d0149004000e6145d00789021001507440390b882d142002d100d0544440c003e440000712a00201040c4003010040400308020441c0518011401246000741855248681e03926045071003070107000548903401a80302c0c06502c20710b40c0c4a01d411003240c1c0b025203c0038040482a129800343e42014800c80c0c0c001c2d4100d841060078507503854200400d80c000b0b080708a415009110000001400c0c640c0c0050196101e032001d0500b9034081e000502c1c603400707680305800907681800f01e0320314540d07004180d01c074104184d403801542964500d07030700b95101602c54901c0442c0038030700354002081c0108006080e0680c3d51541c284d0750b214440003c2103c11200a49101c40c84007980c2400f40c24260068036900413800041c1480c5c0c0ca641600d400085464000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 413290746 1250 413289496 413289511
    0x6010e060a231e041d0f04080904060b0d05010303090803040e0105040b060408100b010f210c020f0703050f0c03060c031302010e0909060411030d090306020d0e0a0c09050705040b0d0b0f09 82
    0x4036017801413421031810782c140b00300d030001c40d01a2407030080201c205001e80030b00041d15a0030000365031130b0305403a0f0350401c50250a414400316503411005030340c00020542480283c0000d0182c44000ca00f02c0c401004540449680090b504180c0e424001000020404250120f5100904000c00a91a201840711011102000900260320751081300003400e03004180300300f1001c00c4200e4404400d25074400160402a0640c001c0015400c166150140d207000054400580c1c5441406c100004000740040c41c008900007000c140d40541554130180350303480c481a5500781109a050000030790031085082c18400450051400f22307044aa07041c046192003805880c00c010b250818000c010601100e40782114590070141c0040200c1d980881e40100160040c0c040100301540024400c2040d00441d08040d401d040c1c40820b840381107040d444c0201d03c5080c6489080e85032410440025a110300a03801e60b0200d40c88450414642591001540014141d0906150703000ba8075802580d1070340c03640c2c05088d201c0c462 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 413291996 1250 413290746 413290807
    0xb0f0d11070311010c050d0f0b120c0406090b010203030103080703030f060b04092313020a05030729070f11040f0906020301080705120d180305030a0806010e060a23 72
    0x249410010b050040d80f5003140826810510360030012a802001c4503001014403030001121135031040c401c4050007141404a6002000000084079620b020600034142030003140c0070842c00e99a403a60700f0a40f440c03401580e015030010b00c010008101640002c20380d1a12a180015a09541000c0c05040319590782008801e1403011505120560261140e00c1d060a9207207034520031035461551303403031450300020410040a241c504654045403070360b20455020348801800c3d00d04894a43d048181c9100c6c104855143d0248003804a0b09101c401078100d6030125007240035288041400c0e102c0e040322981c61100a60441d90350342082c603c5400b60b100f5041c1c198803c84001d40ea139454124503d107420301640140340b1901c2640b0001d81880d0300014980600300090612030010b240744101d445004800c1e40c0080c00038040000c07400070a65100c0262407190ba02600c440001002c40c0c020301c09140184c046000c045101415403e413414000820313240c0c4040500350162504001d414000d4200c120180d0320030300302d81d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 413293246 1250 413291996 413292007
    0x30a080f120f1602010207150f0f02180a0f441b040c0509090c0405030f060a1103071d19032904081206030102250b0606040803040b0f0d11 61
    0x207002e0b950b1640424904d01c001c0d4106501030303c07400404a0300112240c625647c80c081c0c01200c0c80e030f540101c007910200c03140031900c5540c2c003a605100600d0091699100d85c80a01002c21403000c40038046041e1040c036840701ca1006107203250408406200c5a40e40740181d41e5010381b1015511820000d1814100d01000e05007500300105d00c21038120404000300c0c880c608080780115069403001c07d568040d8011168080903884103500c04203d0b03c070729000950940540e580505000c0c000084540c0124141070b02040b2210f202c9403c039103140000e072080000590003c941d16101c80a001c10400503000041044000d02000c1c4a00701c440c0320958412102c2c00b225441d46611341c0040681012840ba800d595880c403840c1590347d100c1c6074803504c461001c420344103074082089500c00b50b0564502c02d414402000710024000e90032403681c400b80f02d044540c1c01055001401e142040c509640c1202d440d04004c50809040c40b01c02e9031b640d00111024101140240080c0c003103044503000e9000541c80d44054140e450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 413294496 1250 413293246 413293261
    0x151503050115020a08070606031a04110f010e01050a0e0901060f03060b040f170709020708190c0c050d020d050d181d040b0c1201180c0c02030a080f120f 67
    0x1108142c2c01a00c581c040e80c5902d070200303074001c00c0c2d840495074480003060741c41406161038002003601d908050082891326000c5103496400d004458000d600408042d10035218074803c002821106105050010700c00840555070380d4090741c042e2051110b54201a07407684a05c00c0032809200b001d0340200300103240300c520807011603054401c840107070414404041c60f050904401c104925024490700d840c6240412005031203050501c081405415040401e659940d001e042411700c42c1c21402c5a1415a108074980226080c0100460000c0551040d56016040d26000822248075034914041c2d0b000740c021154040000c0c1c3c1880420902e403c1511170400d1540c2c00d9810485c0d00c0b0a40d00305010780c2c124099940071603075603401c10310f500580c0301101034601e0f500c00800c1d140502441c40803410101d04100086010341c0624000c1c91001e181d99010007144006440443c0e0640302e40d00040d400d50420740c4070601142c0403400401308150608be0041c900500c80d050154442011241c01110741e041c101401083d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 413295746 1250 413294496 413294501
    0x80c0105031e040b220b0c1308010e1c020c011205090709020d0203010801140702060f06010924021006031a090f06091f0903081f1a0304150905030f0d151503 69
    0x2d403441910f844417001044d6078241280c01e02400102c0c006201280da6a510500c405444015007041ca00a002440d40c45c5400d1b60750340d1400d040c6000c200d090003105c514191001510b0981494142e581b13418400070041c01c94000d0002800d040024040c00ea008110b0160900041c42c1e00212600c0043e80da41c0b411a21900310351000c00c02501e01c40c070003000d010800d40d002411a401c40c0320845844025100d4000598410103903503c031500c9aa2001442140c0ca000074a0042d4140016026640c0030301400c844201191403074000244003c240198020f8180c3c94a050301c0c2d8031681280c2290f91800d2040091458114216650352043d40300302200c030071003094070b000322030b02e850309450500a80c46580d0700075121035002408208104000e0005002c0401c681c18174a0041540c004c03600070020725180c1c0021035500c2254169510210140762092040e1244182c00400c2c0e00300b8095410400300141e110055403240c5a20b4501c103442d20003210b111030080401000030052009074060740300030528003805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 413296996 1250 413295746 413295781
    0x120a09030b130201050f0a09210501060501020f0a110a0b0403081908040309051e04020408010e011b09180f1103040b06102f0601060305071701080c0105031e040b 71
    0x410302c0e441c003207100060341c200d0195a4800100711880e0b8481c56151000c40300711280d40c2c03218032028108001c1b2100e20b10348800030700300300e80140002d000c01500c07a0010380c0d0b034242c211000e2109a0200d00e140740402c0d0805040c400802004000120303896a40c902e03103085422031341054074009800101008840b0402601864041d2603041c0303910703540b8203a2400303850641e6520400780510800041412482100e401840c02060010421174079140c0f02c0e003006000381040c0811036015881c0c04840314003e46800790250300b80140f5941c1400f640c0c10800100040b65a548100b80c0c095180c0c4d144148000d40381c0180e090b688a6002c4441d20f80c500350410003081803000e03003554059100042d452200319440803454405900902d01030401c61080700802981000d10080c00000c0d0042400210b040380e4940c001a0003810b4960710a09001c540603910721212100303104610f4654011700070341540d035006202940d8407400004041e50603101c082402d40070350000325022102c00d0b1100040140c440c0480e03883c0380c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 413298246 1250 413296996 413297011
    0x305090405101e050a050411091503070f050306060f0a0207360207020306010306021c02031003110a15030b130c03090201031802030c0d052e110f1b120a09030b 70
    0x10f464680000306060400c24090719000d80d1311131000d040100c0c01c45048488441c1c1c0039004a40796488503d20102030f400680365a000030b00882100c960480c440e1064a00822000b845549490405c4290b061998014124002503004002c8001b4100d035000c01c41c000c04883c80c500e1520040d8804614074003d0303042c49800f00785248140300d00409a180000c81c541546d601240060340e6040e019104d00c01002d028010205550000007000140d01191041c00d04503407041421920070301a5508000c9810524001c03606014403134070742105041e2198110100888014100c1a25440703140c0203141030b12802051580481d0312103200703100f1542d0610607107551906108035008580c00940c0001e8440165100306480b07000e203180703210b013404801c0c403600340c2200750304004c010a44d41c042102c003100c26640d40c0748404945480e440c40035040b0308400302e030002e03030f520304402d40351000740748001d220210b1000c030001c520300c41c44024452b202c0c0710030000c0803510f4050b120948030900d10324014803030040050442 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 413299496 1250 413298246 413298299
    0x40f0c0b0403060f0c0c0605090c0a081b0d0201121104030c090e060a0606090308130b040810110a0c0201050a11060a0e071707030308040f05010606080403110c0108010b07030509040510 81
    0x481d20264401c4d208016182d03c11000315058031402780041c98506802010ba41c09800382500181d10b400c00190800d441c2082c0d0307848542c402c0c3d04405c0158018608070085e011441c0c43c02d40c0e044591950f070100c0303002d203c000710260074035031240c0316001446003e0700050031a907035900304079070600350400180d9480800e418042c41254140a8010480740e41c51000038100c0c580403d0000201c0548001d4001800b110081c1039125960f484000b40d4840d551804004020724140410188564000455618210a0f2200c02200c0042d80c01110303140d01040303aa400f04031720f100d0480b0340c145044c002d407401450100310224035030448640c50390030041a40d01107040403101031a4640418404035011040300e4140c01d042805070347da41080803a91006910041c107030752034800041000c41e000720700070707000d0b90085e6a4140700500806100d5036826000d41c00c180400c0400c80104121030750b1030002c0c0388140c4030307281550601c0105c002050a44e58184d5030090580c4034100305010a4002681e011880100322046 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 413300746 1250 413299496 413299511
    0x1203040807021836030a0801050a0605070503090603090a021f0e010302070c1203170705040303111b0f180103050a0215031605070201030908121005010f020c09040f0c0b0403060f 78
    0xc40c642d4903a04a415046101030202c1c0b10542c404444480c1c8000c0e0081d4117482d07846413600c0c801400350009009807413140c5114900401d00760b228105544c00d0650250080d0b107484850010014960030051028415226507a0040010f0b00d03030003d0f000440d291180754034490402040c01804440344542401d042501c1486410702290700581c0c000110385440e0790315250b410050400b1500751242c1034101c0f08503c200c07000d00117560ba000006104030b078042c0c3d460078845184015180d464a8507501c03013503100103203842640d0003807900c13003001c00c0440e400030300d038141041c01c21820b8514098264001c1e120358200703403021010360601c030078491007800822900ca440c42c80d04916a01c0d00c80b0b4211050020084082807020459010394404c82d0400d412076803054490704e003103660b0354441034200c80401c001c00c004507002807154010042c10040c540310f034001d0115500000280a42082c0c014020b50314802c2541003030000c0754003032100d80080c10f48122045d030317600c1c11810240b051759403c134004d2810500c0c00ca034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 413301996 1250 413300746 413300761
    0x12030509012a14010605030d1209140d0207050a171515040903020f0d02060103050a03080702011401090b0a080619090609080a050a020f12040504050a110d02040503060109060308031812030408070218 87
    0x2018aa0030341c82c2700c00180c02c0c101818031059120b0310640645003803003003e80414080d40c000603108111601184e01005090b21501208030090f1501f010740b038a81c0c044541141d9012210200c6c42d4440507802600701e4280b10305001a09071400805d0544c05a080311b075510038580c0091001021101060000f040d065140d5910203540742c105002c081c080121800100c1c032403c0c0301b900b0a010120402100070710558490007000010900141400e00c103008441000429007400708500307104515540003042e01c10703080c00019001d8108003608480039a580c14900001505400240242101c01e03a07406840c0d061312180039240c40031181650b0880d1b40510310f103e241d00000740440c0c003a1002528081841e44440c0480000380c10645c111564282001c54243d03d0300344260301902c00c655044040715000c1e40d9488060301126140d0001510910042000030140e00807242e0070201c82d45518101c40360210440e180a0080c2c000380c2e0f0131105e9020015404041d40b91450420010710707189564054030341410300703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 413303246 1250 413301996 413302007
    0x3060b120105100e030106060e01180b0a032307030209010801090b0a060f1e0f121404060902180f010504050a05090606040c210e0712030509012a14010605030d 70
    0x42068807416642180990fa1486a1408150b0070001790090048a0301c400740540303040101640c540c00601c1070112480c03030350114401501100d84482c0107900d4140d81c120118040c152880500c02840c1510020080c3c03070144540031803041800e65001a2244000c0000518504069004030095420b0036020021036440740d019038116661803d1032003920460b8442600c844c00c00241d0100780c80086200300c10742036040180705540180940d07d12012024854440c000c0f560b01c03100320784904d503072800001c00080303580e404100c029000a0215440e490008075802034601c00322008000c800c041c0e80100000d041030300900383c0229202405000515100c21000d95030003000b0000d034800c0c5c1c2c42d40080714506000b0186800c0d0007884c1141c0c0d0565208290300c107406800c084032110241e100b4800300007070000c0781941400050f6810703034070140340c031045000445030503041c65850003203208244045020b01c01015100520207119041001140302d021030480c0c02c40d64030b54000c5003e5049000040030080c2c0c40b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 413304496 1250 413303246 413303249
    0x10812041404060e0a060e100e1603060305060702010609110a02060601030908040902040902030610030b030d0507212303060d08030415020310030b010b090607062f0a03060b1201 78
    0x200e04030500881000050b000e03000c1a4441180581c0c103005000c0f0ba04810f40100c0c09a80c6103200c5400c09840360419038610345000e111b0821209280350214607070314138010324081030040d245004a03032642c40303845041c1401c005071201c4001d40c5d0b4031042049840d206003c1c920300c5e07508201180d070801d11034103406911004020f0400b0b040680e039003400c4041040c20425100544115074085455903255200c00000750f006403140352184404c4120302c082e81d4400d000e0741c0d6880c403015000c1e02180d208002f040d0740981100404030b58540d000c40110300c08881e030220042c4c154100759181e58512404c1c095801d1040080195031042d16420010081981c65890301c8101c216032042d15941e4075600c0e8101a101c007940d41e195040c9450001050141d4580d0401a180c141d9001e29910040c40e6a10800c0006070303c108482c03a90400e105204200101e02158050380d0011101841051409003c600c100211058080c86000060340855000c1c81d450303062089002400f00700c00c000b40743c07020311100002c034072005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 413305746 1250 413304496 413304509
    0x30a021009080706020d300f021b06060a051e04090b270c0d030c020a06090e010b0909162001020301140306010b18060f0c030307030b0103090308041407051801090501081204 76
    0x505031001785c00d01c9142c2c143c0c0d00c200007d8003c0241e40500026500030790703c8090794184905141184180160b80031607518001e00004042c03480700c0e40b07484148042c50b40c92403500c0d607200200001502d11500c0d240551035220b0b100384182d01d0649811031035a610302d2030303060180342c0d00fa0003d2000000e0340c00009510b02090000c46509000840303510b803c40740e00540380b1000350030103000c000c0000e20541040c400c0c425a85111003aa11680c1c0740d0648103410300607030b00015400070400004c0303005800e1400c00701d20500104d01e0f04619901451088209100e0707403060713200a40e980080100f03c0c04440f42820b00291104070013601c8154501020020b241c01030101d500900c41181d000d500343da6944008561080414031100c0352100031030307400070341c0300d070021584c9001181c01c1440c2c0d0342140d80b0901c200040150300d900c40c01813548541d151050924541120714515105107480820140d0307035094101c0c22000c5c2d004008650b58100f41108013a940107900c001540d52080e90300614403101c900c02c0e101078894 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 413306996 1250 413305746 413305787
    0x9121501060e1908010b120307030503130c080f100c030c05030402090c220906060e010c350c1903080114040b0a12020405060a0b070204020306030a021009080706020d 73
    0x2c400c1c00240a05501041402000404980014020b441034002882e41c61046400744144640142d00540340e210340341000f00000e404000080c22804098580744e22203000c2d01030010f080b5141c45040c0d00e4200e0b0602180459401808088003100b20381c0124421001c0e00e1a0501c203030054020041c00030700019200910840d15200003030030a541d0791064501800c150780888084040080000c841c442440c0900040d85040c0040450020b0048101030f6182e001a51010659045501c41a2642140d55a061001602d07540180782140c50400130001003600004000c0d0303195170bc400c00e2440c1c4080000c4200b4944074556040303001c2074104004504560100080e10303202c00b1a080028000c04011000342e41c0200c0007407000c28910909100100214802d490070092603c8640030018940450711410540ca40c1c10001d030001802d1a0f0051600240003802301c0d04103041e5a8006103442c003070845a02d0001e00100c400b0031682600700880780080c0783d0f03400500301c27001c1c43d00001002400c909100215800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 413308246 1250 413306996 413307017
    0x40b0619170a0b1305070605120402010309030201200c012007080d06180f05130c09020d110726030411040504140106080304060201110c0a1112010507050912150106 72
    0xa010b0102840155120305401240e140807150342a40e01c0c0031040955851003203031000304440e800b550854081d20302c40d19202020341e41b00e0f1300440207004105012070455486c2e480e0840350b1074002c0b0392010b00c0c54002500c1900c8803e520f60880c2104c00710f90907000c1c200d555114900c45503902c3e80c00c44102603040844590744119441a100c080e0225600c40386102101e00102e00e100c03030300c0e680448030703811000d038051005850310403005c0c408000700030300a000d2541800741040300480981c000c0c524204e5440c00440c0303003a901d6030060380c00d402c440401d8445c000c0f440041c00d40c042111010540c0c00301c03440c07401070940c2031a0701c4161a2039a4010a00c0c007503642c2d03501007014407140c2da0702c03803240843c00b03030092081c55140c0002075103a800078481d100142d03081009526860456a040da2081c03140d0f00000c102d40c4500345c8620f0034030407841480301e400c000d070304031034404102c401e0081c01d2140f00b45482d1159120000002d1050540340303031800b240540c004003650140d11101d0740c003280c11030300c10389018007444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 413309352 1106 413308246 413308289
    0x203031915060807110a08070209061c0609031101150f062318060408160f0b03070e030c03070801090c0e0712020a020102070602030f040b0619 63
    0x304101c0209000c500d20400b0225401041807422001141e100f640c01400c00142200a40d400707900012207200798108411096041001940c000c0940c2043c0c0114001c207000d110300040145803640c00442c14503115884482c480101200200201d03450100402c14009113841030104100504030001441402000084101c110800c180c0601c403000003c0c00701e1a40c04454000705019448490041c1ca0b00c5440182000d007400c04001c2c0052940b48051041d0619298002c0120045550301401200003400a880d00040f50341040f02c1844001400030b030402c1c1d622038205805205039040080c01c2c100c15008030b5903072405410701d10041a100c031401390011008841c0c80e004581c4d442c0d103d08e422165980203160424061000500308600c0e6502d90041c2c0c0d105603407008403142c52400744020300c80380001c6030b900200c045070034420b0321000d08005241c00c4460300c9180500d907440320542150 = true := by decide +kernel

theorem cover : BRFrame.Cov 413129496 413309352 := by
  have h0 := BRFrame.cov_init 413129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 413129496 ≤ n) (h2 : n < 413309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
