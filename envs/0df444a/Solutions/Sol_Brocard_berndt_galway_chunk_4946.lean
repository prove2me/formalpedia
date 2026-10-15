-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4946
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:14:43.366359+00:00
-- url     : https://prove2.me/submissions/6fd98f51-949e-4483-9441-94e5a1215523

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 889388489 ≤ n < 889568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 889389739 1250 889388489 889388491
    0x3050d0804080f03040f23011109031207060609060b0711030d08010510090b0d050906010b0a020c090406290f031b09040203030c011b030b0f0a2c010801090309060c240e06 75
    0x3088581c4051006000c0e400f400c40c1c2e03c2514941c6020740502407000e2907a400700b010a01205403000cc19a114602c1c85c2c6a4011305054024401540c0340c582e000c202002c00002508900e80300f6005a076485a00000b055561440300c03041d04001200080140041e0a248401280b8804141420303002e00c1d4440011a20300c0d08007006112400e0303039900800c10101400c001c05801080000d1102d89400603022000b51200c0300700040c98040c1450703c0100d0204005da511642841c044081c84c0702203001c1d14060080c007a505440c4030f5101e400418502881340c038000c15091900c482d0007007401400d8072551306000d002100204140c0c1e040c0028050b010613681d080c020030440c203140c0085805d0468405202804513003024200c68080c1c03113007521901d16520b640d1101d03c1554001074608460003d44506841c00c041c03044e1982c2d803043c0c5010000500c00c4015082522814420b071192500c035a00c0c0c0800f213500000241015110324001ca52000f01070380d041003c18003405601c800801c1c007041e5180d2441c50604 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 889390989 1250 889389739 889389773
    0x15190b0d050d09151205060109090c020105070216050604030f030c080a090f0f03110904060e1b090a050408070807020301090210020303161d130615050403050d0804080f03040f 77
    0x8400c181e8842e030b4028010005020140910008070031142e1000b80324115100300350800c1540c1d280840c0443c1e002e001410024565100700344910240c001000307002e03100a41e080e501621030524640076050340085200300350f030409481141000c1c0340d81c030350100d01c1c1d80054055051003400038a10000c1481c40c0c0090920600079140d00481d54500703200d00c0008217542e400107003400c0e10392005000090071052103800040040311820300c9a02c542c00c2910041c2443e01d40b0034018480c2e1a42d40700c2140319038a081c81d00300d90484842041c0da540e0030100d0282c2e00115002070141c3d00421400c0d000410860182c098540081d00015680c0c00640c041254040424800d4026910200400c070940040441d4a19410310300d18180142d01c03100710003803100d4541c04c0c11852042410300303072500c00710181da486a001441211041c0c1e040c2c001080014104c0d92042c082038981d03000e510800c0003070f680680456400740340e0014010785040d008280200b580d42010300b0480c3c02504a403c0c400200704d100f281d5210503a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 889392239 1250 889390989 889390993
    0x70609050d200a1d010b030402011b3201290108070e0405151c110f0303070b0703020403021311070803040f0f05010b040e19060e030c0703030c060e15190b0d05 70
    0x1820151240c80c0d11016800b6901c861b17420010800180da01180d100130809400049003d1040c8500d061010910711501d1215002450380c444074401036203114403000148028020000e8032003c1d0385142454078403034803034100c801074031100e9600c0c1e520400c00d442d400001403821000350340d1030500250640f002623441e01034a1907895100481460030035107503100610040c008111401d110f54402e01014800701885201c2d07060a030070110151000e10880300f07141e6208108420501d072a0340050020b4000303003c240e004840e031510040583d2010f201d094000e03540c1d20b0900d41401502e0303540103440d0740000d00403207190b4400360784280018206001840b5407131288002086103a0184240022500009100d996981c0148421140046a117164040c89600700c1070100304000e03c80300052540c0304040c290702041c0310310000041455808516021580d1180f00240310b281d20023011944d56440301040d2880758050580480d001c2902c04802c907591801011020411101040002d17103038034110f00f410741d455 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 889393489 1250 889392239 889392269
    0x14120d02010510120b071b050303040c0806070807080610050706020304150506061201121a010b070c0f0e070e03010f09110907030501030f0f02240c070609050d200a 72
    0xc0c080c10034548015050040e405140061203448181c8503817400742c41a000e215050510303000304a5020344506040350000100d90352400c16107081c481e480000e1003468154014400070135801481401004c2c05004107544441c5c00c1e072112020000c201c412120b0390028070004010400000c0c2c040d0014510850207000130360081181c41903640b050310300c020041441030400b00701443c0ca583e041007465042d103294090800c258241480e00604021801200c501101c141c0000064480c1c2220010070616101d10b99410701039507100c600c28142d0002c1d0040030080d220a81c00550134a1007135801c480c01c40c1d0010b00101d50005a00c25480464040090030303503c0c00c6002c0f149120906010741070303540001880c41c0c01c120641c51502c902d8440f0015040040c0304030445a80c400941d601c48030f841c089800804082c403203c26106030745c01030075030200f200710760140901400058142d02908e013602c101e0380c000d8140c00c50a6450f641e1003003ca2100425101480c004010000641c0c544500d00d03c0035050000017404a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 889394739 1250 889393489 889393501
    0x71103030d112205011b0c030209040f120c0308071b120507050c090f0f1504060b03060f0f2101150f05090c03060a0e070c0210020c0114120114120d020105 68
    0x10f50250310310080d5041030b403e4020861a40e210241040701c1c0b041c00840303d070500080c40c0030000461990700103540882c1410620044c03001201c894121184200c115543c0d12995000541c0d06811001000c0d0105540d10001011140513680e050015404040310790000744c900c0d510030b07048a09500a040018a0100744001046802c000c0d00d12150344c00c4603010300b18500039100d40d0100f24001e01c0c10314a00c14010101704185903060319a005004004c005000780741d121108005184c004651042c46034426012044030f500b012109100c201c0b0010701030b00c400f07640d000d000d07031115100d1ba41c0720400303990b0700d92640802205c00b45040001d0300d4100170512806103071208118107505c0162500c0340d290340801c184101c0b80d50f050106421282040d103490105d9568940070b4440d0321205e00040d41201d00490b411000d00e80c04a0003002d94074090301c2d81b40340800505401202070003000341011003132003081e00500640c264041d07000901c0c00001e00f03200c10b80c00c0400d60641800c07018104840941e44450038403007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 889395989 1250 889394739 889394767
    0x6181207050f0105040b04090e07030b091506120c0105180405130605101202010c240501051203182809050702010b060a0f030f0b0a17060906070203071103030d11 71
    0x280b0082c246090380c2054200f496101c603a11861003482e40b030a558103031b002400b01041c08400010f60f0000d10104113881d02c8040039856000c07400340d5048911013a80004c11a1078540b02a910041684004149031800500103407481e1b4895601c0c03107a4003030028912007884d40e8900a2500c10420080320010004040c030380141962006080b000c0f24030355544080c040181d0805440510a03024a010341510b1342d50304110030361304905003860b0200804a91402148440e60700303c241294801c4e19a91041c68100e00c4481c0c6a0240c004040d000707030314507002e01d0704900e007141030b24940d2000e0000e204d40d4131208680d0075480c0b4003240c1c0700c580000e48402c20400015020f00c5906440007058451a00c2d01040160090a80803095003183c140341d0390703101c1200c1021590f404485c2c510b4000d0710b1952082c0d12032801008025844003140c10f684140d200003410319101003415405000c2580003141484441d0b500c03044c08809101c5101d4162005104941c040c071218003c520300700860304c8a050751010706050940c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 889397239 1250 889395989 889396009
    0x280902040c0801050d1101050d02120601140918180601030311070501090e0720010f290d021509031911010801030803070f120c05040f1703090618120705 67
    0x120078010b00100402c4641c80390460265010390180c290304c0380b81d0300c442c010798050140e9582500454808641940b00741d01d001e500c1409010701b6242c1404075030400945981d684250703070f4a00c4e088115900400d0482401125050b0001d44034034958541840143d00d803440d14109034070907800100b0f55090603000400030302660025210a1816a1a242c03c26030340d080b41c120301400d000c00308003171070b0340c013007210401c00e82c0304000300c064400280001c82107000e010001d015070801240c0301001d6074140800f1a0003495850b040284090503400c6040326640030840e500316034048c116004001045228074641d000d2103440c081a88140d80d0095004560614441007603090300c229040c058080700504c0880e500d02c054039400030680c40c0c032084100c4050030484503d03015815405106041181c03002c003580e0800c0140060701d6031031545400c01070351200d00107101c198409060410f034000300406c21071801c1280051002640c0242031030000d94405000c80c3c82c80e08001180603581d040030300b0074000303840c1001580c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 889398489 1250 889397239 889397261
    0xc08010c03200f0f0c0f01060b04060f170a02130b07031806020a0f02090603070e040602180102070b0a080403200109020a090207051902180405011e020c0307030828090204 75
    0x345040c2003d1010302201d5100b100c1008844940108025090920400200d8803036100c440c0244540d50340c56803c15a1078006003d0080400c102410f9140880c8c49001c110800012100040030780380c0f50f90410030025800301c4403440705e074690b803100803a085806500038007520f48203a981c0c1e110040000040d8040c040540c10400c110f401c01c800301d00111340001e506403013058044030b24000700c0e2100000240390203055071000724848a030004010a001003a8081d02003000c0401d03030720807100c03008070049840300020b00500425900902101071001d101750300607940a1b00c41e00f005585102103d0310315100007802600c1c0c26842c0e444e00320440071820b10b0010034004000c0312034294101030107942d80d01d80396012030181e01c0c502c900ea440894155907581e01c40401c00c0c0c80920710601141407d0038014040d00580d400c15003004001300f01d4070091002842101c1c860a4550301a46c10a180da603002c440c0700502502c1c14829011261294403004408104080300d905000300001e6040e503503105110550b601a041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 889399739 1250 889398489 889398551
    0x1908010303030f091104050c040f030501090c1d04121403040f060e0c13020c011b0801030b10180b0f03030a020307030e0d020901060804060f02030f01051f050a0c0c08010c03 76
    0x65100152a010180311503545c21200840d06071303142c2c1e05030080b40c01140e02c0003e201c00b000e1800014001c042d488006424010341f00143c01946461b840c0c6103150801c2045101004440b001402140d44070551003010318031890203004111003082e01091580080c1c40c2074401d404080601c10800c007161103103180703004604010348041800d10000900d05e88502000305005600080c03d882c1d074203000e5100100070b05481c042541c06080a5000070f003003503003d0000300c51160140011031417554010780d04100321100d0000c80400c0114107003401003c0d2076203c40d0181c1014902d203503500380307a074184007800000c1c1c45680203589820041c1802444801c8440e100f9000c1c1d0b444140b00000740e140c00d240b03541507030140d0501d81100c2e00d603481c00c0e400500e8460099220750b0b1010081c0480f0190351048075049440c1140c6103c200154050070b0114000c44403101c0011070010440980703603900032152428100d004040e02e0724115564002c2030300352031845c15200002956200241c02d4100000b0015003a580c050300c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 889400989 1250 889399739 889399751
    0x5070306050f100309050106030b06122a013c050319050c070804030f0b0106020c0306060f0f03423c09010f0b0d0b0a021908010303030f 60
    0x30100b0004102ea5100c0c40c012645140d070507031810702075003040c3d0710160320100801407507a07241001d0749007400945026114180342102030782e0b002000100e91810070644c3c0c88840f110303400c1c44441c2091049921205040c4070200000e6030380b140d003071902080e034035982500a60081909075a44004003100e202c90350300b030003018000c1c841080c0c240030600681c1c000d040000500f070786500c03405d01c8241c000d581d402000888000b46c041b08110160400b840928810f0480c483c1a0741c81d180181c0c0c0f074145050740d45405d540b1000010b8050f03c0c010040c80c1d00e580000d014000066004804a0300b001283e4009088076032020f00501382d821950801c4011080c2d460000032010302c40c410198427a2400a098030b26008000d03401d29949100e01c020284452050700b40001c0c10b028030540c0d1b014801422134003011154600b44280014042c540141d4112000007441e241c07044205035036403103003040041c00c0c0c00041c0e6402e026880c1c201c010450100d54400c07080e1101d402030340c5035142c028141c0300000100303012281454 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 889402239 1250 889400989 889400999
    0xf0a03080d2c1506061c0c110109060203090d0230090a030b06031605060901030e16240f080c0a0c060609090215090a030206070f051b01020105070306 66
    0x15003034409408a6040224802518040102c0c82880c5a0201d8004010003880003102050000c2c182080d90014684442a0b50724074007084070501500c06510b101003d81c504008072034840381c0c004409030440b130800240f264003503001c1a003183c5004404581d0b083e0300000703100340c14a0411142c40302042d144014110b00d540c0382000800030900c060464804224072107580354400c21402a00e0301e0300c4020301141c0c07110b81e507810541c041c2e03101076a13114000c0c0150740070303070010701c0c5440b41e15400d440000d44014a070860300303801140100602c02810041e03000d503142d59055a900c400041000380300c4219003e203504c0407031208035814401c40c02184103100d0742c820086241034000390b0a03540040ca0b548000d0700c40e4201c11087c2e801810345080280318524040000c64000e0995028240707150007038a07050807161101244481c00e1090384140c44d03100c0e0140b0b100300010720b0320000074040745115005040d038211403540c034545401c1c580c8a4584034040c141d080d40502e540e0901c1410380c0320000d4601401128509 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 889403489 1250 889402239 889402253
    0x140d1509020a0f260c03192f220515030907120317010602010c02010b060906041a04080610170613030e01090b160c050a08070506090411180f0a03 64
    0x4800c8075402e10030200e0994100001050b03203201c2e08207101030410564681040740a81741d60085400c0c01308601c85804076482e01000313100d00120381241114100010f41501e0b03110301580e41d110010014207108100007400c61404e00540b886054410680041c800e00740000c21400080041c200c0000140500c20051041000a00d800889510485003c1c2400c4c003810300309c1d100b00040d51110700b040d82c0900005420f580c1540540c180701841d90003004003401e40002c00507644920f80d15958894000c4c0310900038800309124408003c901900b0291a13741d490410a003041e400300c8015038240440c0108100100030411144030900c0c080000e058130380b82c0060a001866200c41c00582040015104500da503405904500060010505c150740c4a03908640040e1a490051324200c0c0c584c60482000545c6d400d0040070b1105481d41180581222400d11083c44103681007100011703806130b203078903050318504202c2e001450449440440c1c1d00400701d5880078480b10104802943d030140c01004801c00124034a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 889404739 1250 889403489 889403507
    0xb0d05012106150e091c0905150d0e0718050601050309031204110303070c2105071a0f030f060a0e1b0d0b040516030c08150d0201140d1509020a 63
    0xb101c0d4000503480100095001141416001a09840a400300340a14030100080300c070002c9650446401250315207043c2150f03038001c1441602c0c4c00244000310701191406401c003030b00100c0122100040c0c07900c14101d8032171a01c10982d00000c0d050040e00190f02d40c203500c038014164004400c1c00d0045c55418a40e04559580c403c007907091034007043c2c20300800c0800c0003e4980900035140101241d4440070030f810062104020b5201d0078484860760302142c15080441c1c12004996078011020f8200c452421903140e02a02d180e5403640410341013084083c41101d520401707035000781c50f0140d02401074038200c82807105214061b040489000240780030403400746982d250510401980f00c2c41180c55080710729002e8081c000090807980c0c06401c1200700031958180043c0c40042001c244d0702070149410700d000c1a524004142c031156042d0740c0e0300e194803402d410900d804010080c130601d0710b4900030500f071502e48002d401252000c28025241c1704032041480d2020f0130700c0d010384420501145064902580075115000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 889405989 1250 889404739 889404743
    0x606081302090406150b0a0305010e040c061b2f030703050d0e01051608090102061303081302190801020d0c0905061206031515100e092e0b0d050121 65
    0x1c01c0c0b40040c041124607008452a5a07540310115080c0303403075040d120040c0d001040071500007481e210000400104c41b5084901031600f08007440c4110f07041000840d44100b1481038549005500b110910009a03030840320480c14140344007259000302c805550780120300011542601c03d510480b414804a00c01086200e80c4444604000c01c80c00c8500c5c0060b42c1601800c00500c1c54580045080e1041c00030f1100100b1146030241d00383c40040c1c2d1003c400a0301494040c9001d000104002e0000c1e95a90400c02002002400100340d10440b08441415200c040099000902c1c075035004122070341c1e80c14981c0a64107034440d050400748081800c0402103201030040d446010824400e510109049440901c0b00691905820f00c9818081c68801802d112103911195814040c0480403c1c1419061040c18000d010103002010005a61104001584004800c80780889030504082030250046500054880101001c0301007544034990501440d00b1200b05902030134403001c051265512181411000012142d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 889407239 1250 889405989 889405999
    0x20717070302030330130221100903021e10021303050304030602130509060306040308101e0e0a02090102030a0c05010f0212090c03010e3415030606081302 68
    0x50a0424051415849a0019405010015040d6050440c0c4601020314a1880c580300000160780703a00c11000c00c1c01111021000100d15140000610744000c070901150841c0d805c0071824a000883e0b00e0401c0091040c50891341c0d42d4002031003c064040c00241c40c90800c1e894000d5800000000c440e80b10410b60755a14419640050b48181000f01e110a41001e181c0000880c0c2e100c41d181c0c40d0480c0254401e42d20740e0700303400034148001818908a10b03810712070f03200038003e06450b40301d6030303800c0c1d414a6010b00700d91250400712901141201c209645e00080c03009051000a21621b0807500d101c142d400075103030321241801000000ea450f41c0000c111108c0c02e02ca45041d10340741c072071420603600400c041080300b04000d000040b1480b0400301d02e0205070007501c4007c29138a03080006010142200c0d0032401510f55078120100c050200691f00e03028031160b040118111502c4125000c4090300040f044c0c00c40c88164102c40201a500c544c9841801301425450804e42c05e2800c04210324400080002d42c002d11032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 889408489 1250 889407239 889407269
    0x20c0f03031201061101060504060506070204180204020a050405040e0105040302060403081b03070e19290409020409090c0824090c0406030c05191a030c040329070f0207 74
    0x9500c04204480e8030380d014400e040020350312108001c100d003412a010095960909001107464a03107032080c101110001850240b41c0000c50b424000508691040c050005516018020140e00d650005002c2051503071f94a036640c6017044108412a01100c6961055a14240030480000d03000588a0b030000c0c0c16081000c810307036480d2101e810b0304100e00d801e4100c1040c0402400300302a0010742091080038100d030103020141c0ca484181050802c0c0f4400c0407401c012030181c01241000d0071030003005004518648918064484d0022000d13070384180d000000c010396480190081c40368600d04003025041c018040d100b9981170b07007000c4103008800d6090b02c544101e0100424001e51040015607408030700a04107104981e035038108156240740c04c1c42040e00404c2824208080009299a00c600340d500d1940c1030f4401d60510503130304100313402c010442d24011400b08008004990b4a20b10300034200094200050311100f881402c5072884406403408003408285141805900c0d00420310800351001c008041c204 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 889409739 1250 889408489 889408519
    0x203100b1b0109061a0904051b010509041407141303030e0d120f2316051908040519031a101703070c0501020703020109150302120f071707020c 63
    0x1086000d01c008100540c42c142e41d400400204c0c0d04401036085a40e0f0402c40202d604070140041c10904840c01000d0b50018800c89844102c136203036a4080c04810300d07101d41890300702000308085400c21400040200487d0f01000782c4940d0280b201d2186043c80d010741d0b42000440400c40c4051000d5000c0101030000400e042c0d411601c0d4000b180c912241c025008088200c0c40507000752034020711300924400600d8660380410380c0902c01007035400808003001030515102261030a030700c140d420210121404d0041c0011a0b031040c041c08580b103d164050007074903aa0b64540804c101800400481e20030104401d0792003000480d6482801c28074081440c0b650024a80e5920300c1c0d4200c650701904130a20b002c0b00130140051102c3c1c008058421144100840c0f62065140c0c801a0b940e0001440000d00060354882c00f4880b07c0d21018164180d26250300b009030822581d0f80c030110740100c044a030000c03816420010405103640c010301c0082c1034803440c0701740112070801200003911400301481c40d83c0181ca8020940300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 889410989 1250 889409739 889409767
    0x40602090409020a030602030403031505030a140f070806090f010501060806010c020a0b0d020c15090604030f032a1d0a1a071505250c141c09050a090203100b 69
    0x40e00f41d00410002c00e980d00c034580f550080d0006d079802d80c0028a00641e4500406c20355200707909440001f4014401031b0415506c0400c4101d0144000d00d140c064074262030565082040114042c15a2501400e110300e4401040c0c0e00d00f4550032030360451a03042000403c080c1c2d070407049003a0000b1003032030074410900180c00810f01c05511980b041401010005510102d103070f0030b9025080115402d020350380411030010b010101008151800f0703007150051400f090000e0302880580e21070894500300800c0410b5010b49035079440c82e64001d000641000c1c100c44941c0640e000c0b5010f081150005540041402e40348040b8405410ba401850300d000400813045440c040b45006841030301b075110a020641c0491181040f01034002138544018030750554003d2001400b40c048040700100b42642c64001171901500c0b91341c0c0391080480425840e00030380104c1d600c00094088003040081c06a01d030010554680010f00041c000c890b440f00b440703988140148014020740d0201041111720203184151580040f0030010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 889412239 1250 889410989 889411001
    0x1b01030f0e0d0906110a020310021b0d180915150302040317120f0405063106150b0f090609010512010807091a0117090c0d030206061311030406020904 66
    0x1400d8030800421020b050307800b40c000c0c010b65a256031440041c2082c0410565039200040000f507050708640c8a04450030400e80c00f9204d0001881c005c242100f440700d60b1f4a0070071050420301c1c00056208410520b401008501c10801480c500108101014090480c6007880d41035020f441505084e00450050b640d02c2501501c02440e0808103101c881007605078510120350290348280320028200e00040d114003c41c0344940d10954104018090503034500d101008030303030441107003004078a03800328a081c0501c1c820421031080e10300c24500021440080046840503802503448241041000c0250080003e80d560a5030074a1600341e504544a040200c01139440c0e0142e04000b03085404e09000010342c800f03001551101711003134032100b0003a00103004985003540500c0703644140442c1060075900c84e1290b01c800450740c49100042a90516041d0310009a54286103000540050b4040e0052201e11700c2c050000d406800401802005220101c031814a042d00001b03001030203c0e540440c426842c0d440e00e4002d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 889413489 1250 889412239 889412261
    0x2120f01020409061502160308030c120103050109030314100506071e0503040609082109041d030909060d320a0807050d0e0306220813080f1b01030f 65
    0x25901c40d511081c5143c01000f403072045801070b802c0b06003010b4095002041d80c9591505404d49542141d045071503140d000d51000c4d055014224041000e0200c02e507113412400d001e588150004165883c41c1d04004055407240720025504058070703006e000300f144001c0030300e0046940503604140c65061a0520090612110000c0941400000401000c124000c40180f081c1c404d680c03a007100c05070b00c0320300440d51040e9460b07252484211003428043c4220504000c0c1c061020700600124210025029652400e000000181095400458542550300e00650704607400b07001502d59445100f40b507200d80e94084403084048681402c85840c0080400c1c40d240030048a000364000c41c8d414034200d1510940369401180c09603194068404d0901c0070b10b10481e180c03040d04100800401c09034580c4100d0a060341e2940168640d11030b000600c5a00140036031010701082103042c03e2183c1d00b245014076490034000c09020140c1d0a400007889002440600d40c080c008196080c81d00280c1c038140000c502e00140354807216 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 889414739 1250 889413489 889413491
    0x11090901080f1005063a0803061005070f081308070609060f0302070309140f040e0c030c0607050601120809061c1127010e0a090b150c0a02120f01 64
    0x49210721000441100c0b080c51041200c0300c900590038400111907007905c2a40e03025045445000c8641008240180d60700f490742e4030310010103640900149040107003801101c2c62070005c4200402403410448907560460039080645c584000c1c0d42c4c0304458440c22490040c03c080002c00c0703414681140510b40809044418100c8002c0c1d600e0b00000b03425102940b15040024403001000c3d000c4920900903243c486a05403100c00030542840341805d2030301d1105001503002420750a0000c1103540318090b00303814801d50b101500e18154408241401c020000c034886028400820805001540005509044849a410601c000c042c2803802d04884d210305a6440c0d4880004a440103030925903000c40304900030148000c1000503c01d400711049130003039100140421021110000715458010642c42002d0b5051500030b0f00d0345c03c8200041c101000da90081c0e50820360700c101586560504002c0f000039034000c03c0c645410325401204107541d40200c400024069240b5880c02d9408403030801c0b21280301054200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 889415989 1250 889414739 889414741
    0x6020f03070305040209012310030f0c0903020a0801200307030b04050408030f1602150a1d071806030c030809131a0f060a17130503030a0903030e1b0103110909 70
    0x20018003503d03054600b81c2c07250045c040006950084030041c40e10124625150052000e5a001082010301290700700d0410315880e05405c0316060154450480884110380310b0518460640c018495408078542101d89036a14203206000c80ca4a039650000308800740e4041d40d030f0b49030340d03905048014100031481660460300f480300740402c0240ac100512722031000580c00b4211030307131f918003202145407540203014050380182c0c0c2d503e56040e03081e0701041c1d401217002c0400300c0c41300310792150810301210080c25008290000c0c801030151140c9442c001c1070451040c43c0503c0300a0460f110b8462880c0300748030050400000152490664454007035800101000d454208044407003008000342010300c40400c24851040441d8081c4146030001c180c03900c060041c1c0d513003c3c0303c000c514040310080c034010700002c51403500c404111002480c200011841001004408200701e15941f901a040c3d42408142d203100d901720034610b20798480381020f0701162100919011900704070200548240b0b109002c00607420403c054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 889417239 1250 889415989 889416001
    0x1080115050906070303050f1303120e01060b130305100207030e06030a180501020d061e05010f110322080a0308060f130603260a09060806182a071a0406020f03 70
    0x11f03100a110b500b000390100b2860340e50020003ea100e00185008001c1a518030707c640d2000b00c1d6900008400c8640b0740005402038491b1130100c4181c02c0310080c190760300349400702841041828020442c858113003010035400c060a540d0301411310755445890f81c4c080d00000c00040c0114549800a0300c0e2012925030f0483c50841ca801d005000c0c0d0b0020182007026810200001010114003072100162540c8102e000411030408004451140300c0350b8070b400c10000d0300860302e40201000c1c0000e00340724005c003100d910810109484000c0c1490298440c03d01a00b01324031110210390403070080d0b503204900b00e9441b07a07880d058900003900c3d00880382d55500c0e0b1f03e240100220410103280c2400000c00e0140044c1022040920614065840b031217501c1c500080c0d200408100c03080c0202c40281e08441e0040080944051002d0230100c03c003811079080c0030fa0586858a540c68806608120b60100002e107d014682401501c0d0300c4a04039074044020f13900514800000d040c040d03143d056030104440c0610041e0baa0600c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 889418489 1250 889417239 889417241
    0x203043e101e030e190219030b1b0c0a0809130204050d030f02030d2d06082a03010513061514130e0d0216090b01080115050906070303 59
    0x840e030400d591040041491280703480c41265010420580e40c40c80e00b0b5800c4141d50341d959100290050900d511030201e01180b040520002c8420800320540200d40080d0f03004000c102c0b1404040000364216500c000c1c004a134480100f66841541c440240d0001400c24481c20224807503040000d000d0f0045440c0d4908101d100b01c02010549003c55141d03c0d80c5145907000c4007240700320710403140d00c030101140c14800a17000d921070b103280500701d0043e0386c1030115901c02c003000d507040c00e20959511924440c0f41406810036101c1c40c110307101a194100f000328140702d030556903602c00105000b40040641020b104240030b0244c840d50007000075000303000f2400c00c290310102030107139140700305d4215081c120103580021704015108202d4070340c40d540100c220003400c2840f540c046078541c07082289403a10080503410004100a5041040740e60040c400e0300c0448134a0707a0a0a0301d50896604681400201940ea0b0b070b016130308906440c0026400c6d610154071000c00d170354601c40c1c1c5614a80060f03020404105050305 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 889419739 1250 889418489 889418573
    0xb070605060f03190503070b040602042918061e03010503100c05090f0d0203062809051e150a0c090e04171809090309040606020706080a020304 63
    0x214440610407600c40c50704000c0709011655010340c160b44440c5060324443c2c02085402010b50080c41940c0c5440b10702e071140c4401c507204580580d49540c001808002e06400c81400c04003540c041d82101502159690000055120f9051002c261000e0b950152a1594490f4110380420014000003401d50842d551014115042403050500c280600f440f038801028190007191103241c0d0f680d69052822141c4810824442c003000d40c4a604003402c3c1000f0300c0107803030800069000360304880b18080215032003003603180303100c4d10f0b101e60044036403c10b41203c0c00039100245000c1c0d91034440c02d83c2c1503000b800005c0503141003081491211650203000501209203816441101e0b03001c03255030341105403521800003010050303040e80e0082c4412080040b00f800d842d11000a803107800e581071401d20f6103400b00c1d00007900341c040035940a03095801c0014822104e203464402c80d4020802030014010710f500e050070140807004010950028150004006400c209440c4042c2c44004440e0304aa0402d92807041d08840c1c01034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 889420989 1250 889419739 889419743
    0x7090e0708011508120d020405030a030216121a0a23090c0109083406051b0a020108040f150515240702010c08070512030a0506010507080a030c1106010b07 68
    0x4604851940040100810b120549001600174540900010301c1d43c0110b0b032146188140b40356003030001217201c0c0c4e01803100c18101801f03a80184070114400b9001815590300380e01400301141c04082072000650001d02560241c480005410200e41d2290089400350803084c0e0500c00080c02a07141d41d84406039016003e000d031410340100c07098000004019140000d003030203049426400040b1a42009000c0c03080004a51030301c0e00c03181b003c403c6028682c00005210380006002c40c00104910b80c0c0e0744d40c224034800082c0703813010080c00405050340018013111009000a071990541481290901c40345901c1d0740c1c941d00c1d042c0c008200e149440c0340303003841c1d002d44070070000e01c00c00c4250101050742c2403242000704c030070103007002003803424045500545a0a505c00400c540d0082c0520502000c5181070018850941c01410b10740d030b8070b1030410043c0048800050515051000911118001c03a58a4081d40c4101020b820000f0750014501405d03076030361030386010340c103014414200003042c55039040d130160041034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 889422239 1250 889420989 889420991
    0x30c03051506060f040311011e02011d0a0b011503020c030a120507030c2a050601080c12030c0601181b110c040506180c160c05101d100207090e070801 66
    0xb840c0c880c20070803076104d1004400050031043c0800d2012500403411030540c610141050204070800d28030554050106040141c09170755104074080d00c0ca90008626107122100c100070780b500e07181559491154007018000d01e09450800c5030b40f0308000e802507040361241520107045a840b142c81311b00040500c10001c1e22901a1030800000c10955030180c09860f0385464581c88960b01c00100000e0482e1940782d640300c131803422001030580400702e98180300071806043c1d10b0313001e00f00b541841014040b0001c4802c01c80301d11a801009100019100031810a0540749184400800048114074950180c11903009000e6020300c1040300c8040c44d0341001c400700c1c1801e42d500695042c03440c442d08000403540304980c540d40008550851a010000f2032200590000c1c80300c640c1803d041c14203180c826069503103041200d0b04040300000340201c2c03510310717074540300002d980c54140c03507030b21040000054500c08604805e00580303260440703006c69402031101d600a0070f860101082140c101c09207050b6a4102403040c00695 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 889423489 1250 889422239 889422241
    0xa1823120703020922050f0d18060e04060b0c01050601110c0a050f120607020328020a14030409020d0b0a0902090d0305090d0f052a0d020d020a030c030515 68
    0xa41003032000c0180e20380800014281e9940341d40c0a0280e0380d04020101d888116a0500c41c0c104e2909803485c0d5409140a0700c003d101d00b0000170111840c2009100502c01405080c3c5071a101c01d60845d80503809441c0103151602302030114102041c09440507800c006001c0340d011560325010501544000c0c440d01e0240da46000c0c0c5c4c40c80d141500e45a43c0d084c52800d8114544032418403590034440da020711303948800b82000e20a600300c00400c0d030804170103441600c016000000d090415070302035042c54910151681c10b0213280e40070341c0c0d0041d5460780078882c02130020604c82e000c0e0168030024400d941c010311382860190750710300070080a01c1c000c0c5054500d40784039200384100459030014920988031408000740100c59688000c0e00c06660340d81203050295481b0118040c840d000903880824554020321400c0100302401911700070b040b00490004100c3c50b10303003656903d00d0382551007880c020b80c0e064054a04036180c11306800814004c0481d500040c00c280c0c1ca52500004100000501c0035420400039407400703103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 889424739 1250 889423489 889423559
    0xc0f0806060f040b13080f1e0c010f0c0218330a0501080c0702030d0e0f010e130e0c0a0b0a0f091a09031011030a0b03071503020a18 58
    0x40c02200c9140003001c10612040c8500c1c00c40700010442d80c05c0c400391508070960395a6041d49080c06d1081d02c908079030400048490144034204015070016040b5000d881000b408000003010405c04080f214101b042146103071043d0740300c080c0d2903030395024030924084691810091b03480c101543c1c070f00f00150681a00c0c506840b491000405403400c1c41c00105070340c80b42c518041c011074070750364090500c040548007000003100507030302004010f1001070396803280c81d0010f4525041004410048081506115480e000c0c04015038940745100c50104042e240001e1542c86002e402d490500990050360300980c601e8404144905581c01a0100b0906650b0b820300b42100c0d800110b490030303000d1098110304c80d01700810400d07100684015180c00340c40541200c00400d03420b00c0682c20348001c200d648903108000002e200400701c407402041040c41c1c041e001045024600010040c902d00030a61030010507601041ca1020648241d0100740d03000350184101c6690f50300c8100802440750025040c0442018a02c21511 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 889425989 1250 889424739 889424749
    0x8100608060105010503071407060c030605090402150a110a0c17120d1e020703080a0515281a04090507030513021e1309151413050a060c0f0806 63
    0x1040c0d40500000d44040e0b480d1500540703440c0c0014002800780b011850459500c401034038040c102e0140282c0002c00c1d200c80c0f440c00501120426007101d40640c140d64200405626001e03140600d0b24401c2d001d299032424020011503a403425441500c5d0300340150540c40090244200442c4282c5080151086180d0010719400e40c2d6510400050910b000e002c0c00450b4091000340e100042c6100c004110b864440d8036580f80c01c040b40d0010b507048010492210a001d40d0707103100d100c1c2e194031050300522403214103024000545042c1c81c03044200c0b044800c41d402c480d0a011000400b5000300900c001c1c2d4000b4640c40c503c003408681140c0101480c603490308000682ea039100b801440d0054280014a030742c0f51089400707010810010100c1c4550500480c07842c00c2942e128100c02150301d00018400044101a5260031803600c40c0b00da0604070041d0038a840b20b04076030103220354107401c880c404000c01905001440d100382804103203000940b485140089803141140c000001554a00c0e9680e40da990a965031341c1001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 889427239 1250 889425989 889426001
    0x30b091501090b0307030f0e1b040c0c020609060409140403020f150c070512040b0409110f030c0a11060a050f1003050d0320070f02150403020904110120070810 70
    0x15002401203207081111202e000004d50f00a1000d14020a00c0e1150400c41c2c0e0540f00d8508001301c0782c0d4422000f035803445e920307085403512240084406003c1440319000c002c0c011490319001901c50350002841d1012540c0e00401c80d001402c403d44140702b000381d110b000f400140c000725007d6000d40942c88800b07484800100e40344441207030319404182c0c103464204035403c0507005288116003500c124501604c02d0020300000e440101040c003200d0350b8031420311403408280d920300594030003040001e00807525001e84007011b0707a60010381007180b0794841a003814101c8100d40d00c1491880036001e06030a00805110a0304154460300242c3c0c3c840140d03072652006041244420711000d0010381000c0e42800c00c052098009403600008100041d030704500342c0a03001283ea01002c0308807940c07140e200c44902141031801a9050407580c094005003080e10f16004a00c0106004000901c9120ba44c07a544003e40e0003842190300310f01c80355003405110754a56980d10394032600d078014000c0b43c0c41000604a958007080c0221 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 889428489 1250 889427239 889427281
    0x17090d081005030d08060d051b0324010303230324060a0210180213090b091c050901170f0103060b040e1c1b050c0a172a030d030b09 58
    0x140842a40c60b002194000c0001c6d20803079000c0380704078000340404c03800c01800d0104403020b03402c001c0d61140c0c1e41c101403410380c8160300c1d1200c4020201c251103a4080403941d090450790941840c1845100c114103481c024920b208150500b11800300511030a60008007481c05010a4081c0d088440c041d0042001078034010b84480100580c0480507205500c0c0740c940101c034560458526681e40048036034000b82014004441e103484607641e60b035420062082c807035a0550002c0455020300304485d0803c011a0308505800d1343c007010300800040c591042d07480b40c1d4070750380075501c094410620360500018484420b0001e02c41582c40e2418034991070940e00c0c1ca80b0590300b400c0306480c02454403183d07489414260315072b02101c02c0706002400192460a503c1012040c55079441180a01303801c0325950104054100c20f6001440b048802c0d01601d0101040002c22050305424840c100f00c0048681e00080b501480041025070507003c0d6503640300106800d500815a0480d045418041c1c955451000034583e050a03400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 889429739 1250 889428489 889428493
    0x15030705090903070f0c18050a0f060e1602070504110c060106030510030204151d070212040b1c1d030903010524091f141002060408030604020a17090d08100503 70
    0x94400010303400508841c04d280f1509000c6c9040f07558050030311a245c2404c070307030310251500c42c0200702e1752000e2403040d044a004c0b0392004100c42c0c0d04000b00c03084041001418590310500d0007504a0410380200080c00043c540184240aa16024202594240c2081c0102c45262144200128440e802030050034032800c3e8a0310200c06007451902008060608542e118070440f111540104405000c84400214260407011820036424075990091418400f2415007245507418403061000b81071681c101d40e03000794108590050f40c0321b80420080140742120300c21b01d05042d0071890901807800800a003803604d004900030080c0356116107264680d200c00203010341010750f0b070051040c82ca02c0d021816035084901c1160644030070754040021806000703141c00074210210100003048641c949551810000349107440540034504180c1d80b240424003000d00054401c41e00810800c0c2e100344070740d0600050001602800406080641100782c5401601039030100041d4000c0004500d1122810020b08840b00600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 889430989 1250 889429739 889429747
    0xf030b070806012a0c0f030b01080706120b040e0a03031505371d01032f01030b03160f06020105010b0a170c040b0d0c02060a09030915110615030705090903 68
    0x4d40d00c045920007444024842d04070001000c0880d04102c2d04001904d400801a444607040d424507031401901640148c41a511214051181c540c0c004440b50410f61480c1d400702c0e549a82e140064007070103850001c0700140c4150f0240c8020716034141c000301d060014444144c0101911942404043e102e40c8070b2030b5039020b46105000800c0488440400200880300348074106a80d04d61649195020351101817602c1003645100500034411909400040d02c0c0e601d800120380311403444807086413802c9000f080d6050580d1084034511640741444041e007410380410000e00542c0d11502c1c1000d880e8824090380c001503107810008980f11014400701d910600d0341d0b0301c3c0d40c240d8905152800c0c1740c1500080c0109401e840910000414005050150020001904003c109105d88141c000d25101c8000e200c0c800300c2d0300344062903001c01d030844860002d4484200d078035041944080e805071090700142400002610404007000100c1841036200c1600c0c080c200c050328512580c0320104043c50400761803014250f00104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 889432239 1250 889430989 889431017
    0x6030602070f031b0206090d170d0c090506180d0507080a03090f050604050306040602090402041a0a17012108070c06020a0b06060a050f0304030201060f060e0a0807062102130f030b07080601 83
    0x408d1078914548244022a0190003191b03c240603034200381012401c0540303d8107a00c00d142c0d04804514003412041e210340c0d0400440d450100c140b4614240244d00846a1a030440240a01444081302426038402140e15511542c81d00501c202c00900c500d00003449400e2001c5610300e01074007101c0889500500400403601c1d642c95032402036200010266003d5420400003403885140c3c542c1c248120004034140b600d84662881c00350001305640c80c4034101c401e40a006003c3d00013500680f40c00c4500392823000c4082c08003407521848605c0384c40c1029007a04020304000446550019140b40e03880d100b0058600103440310000d1020718001ca820840116405000107400c1e0b400c50405554001d000b440040b445640d80d044402d00c030351041d044007001912080401c0c4050070304450a200800f056802811941c1c9800c2c801071400d603c5075000c9096040d00040c405414180da01a1003030281c000d00041c20700f640d00c0074080c495a4070f6103c02c5039140f112900190585001d03052292103114181c40c1d441841a0036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 889433489 1250 889432239 889432249
    0x20a0806010e0414190c260d03020a05090405090c01020d17010e190e1b03030c06060d020d0b0c0304020114090a0e10031425060509040b0406030602070f031b020609 72
    0xa890780350201d200e0390042c1d03801101841c91489005c2c0c00788585000081c00c1c000c0b071481e10751192509484042646201500b14000040c1458091900380340c01600c41600c060100c0f8684200000f0740c9c0d00c0f83c10312040c010000d002240140c2e02c502c1c240c0840d01d030601c0c5180c0613139064004040740c801c031220110040007080340c000c40c4540d010040b03601d48400c8018a4030500b00311005400400540c1d400300c40d440517a101d895504000c080e100318000c50a00c025400925900e040082405005100800041085450300c041624406501101c1080c8500c1c01682c07200d00c1d50001c0794140d00107490543d140c1c40f41c0040e9400c0f60042c000140c1110b982130700b000a44070240c10003038840420440d01400000100d10400401c26071201c0c05009070003131550361b03213918a29030440d0028098504040300e04000c895003150490701668825030300850401c02c5400020005c10b060b82c006804c45000141540800181180960090b80710342c895000c0090340c10154851a4603042000750803c108208481c1c151920b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 889434739 1250 889433489 889433513
    0x21030903020f1503070c0501060f050901031104450809041113060801030c051023090409060b1f0c15061212120209012a081303020a0806010e04 63
    0x2400d1607402654100d40c2e00750f240c1c0115480d200280350000440c0400c0380a0180c0b000412817840f45d540340741d0500340080c0d040d0606202c000d1903281003105180c0c8580b1550481c00d401e0980c0f500c104800b074400c1030a01c03c980e003400c092580d00c1c2c08003c0d80a1040e490403020207942500200340030b007132003911810301c00104141c180c0c45060413400d101a1800480385035100018250030f507510031155241d072512850008198000d40c2c1314040f421949900a54440104044550000f0910034002c100c2403c0c04e0040c824654aa0b800500780001117040c80504c0e003141400400039601c1c10140b0b121841e03003c07034408123165a900000d070608034903404110147ca200380d21040010380080c90b1a510900c0540c01c4015000888400240b00c00d403003011904504003203040100d02c80e09514000240c0002418480c0003844064000c812401000050413941e9005200b071350f20a592940d2403030707000d00400c0c00d0100c9104c100e20400341c0d644040346039480400c4440c12903c40000e1046e003030b02e5550b01c156071804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 889435989 1250 889434739 889434769
    0x8070f05031f23060c06071b020a090c0e120309220c020703120801030c03022256060c150f070305040c06050a020f030409062103090302 60
    0x50040900079200a9114038803004200d4180c885118800000550f51040340da403402e0380c840c510034030408031400400720300542c2c80007507464401450031070400c1000c2902c241c0c0760040d4210310105808168203156620160706220141c955241d1018000100a080501820030980c1a01f060040500d282010b0500606000170382951042082601c2c4180c0b0403078103507069800050784504020005c0c490003900c03a005100645ca0314030b20640c1141c4072404400c120340b10082c06070580c0c1e00741e411140800703441702c441d400b2181d806201e0b68406401542001200c4d44101d19406800c20154070703050030f5440307518130000420b00c055600140c220550280c0701448904c60b60030080402525a4042c03050160200918040324040000e00b00f6101340d502c01c10b801090441414941300900010445080955080310340714981036698030100c600403810945c200322590064400401d02040ca15840c0d0403403000d840902c0604c0d5150903c0c40790311040c0340010b03500a0302203000000c00744007504107450b0803040c0034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 889437239 1250 889435989 889436011
    0xa030c03030513050a08030619030b1302040b0319110a081903200105100905220201090f03030e15030f4c090c0e010c0f020d150c08070f0503 62
    0x444680360030f410004000c500306c0350144000200030162404055107101c9084010000030384034216502c1178141c440c042c280e050401d5660a0340401c5541d5034209201e1407a000e010358401040c0d1400c40f5142d00b5108004494400364030180f1581d500309400310004580010008086107140030241c000e05d5491810158208154501c181d40fa418108039071407100308880000045a02e04a018400a020181c0008840707504040a109184000301c0b40034000307103504a51740c1304403481440180c070762422652010819600041001050540181400d207480d0720230f4412404440c0d07102c070402c2d150702c41150100c041484a0700815000302052445040c8050030403c464031044954038032400da840c1e1011804481c1c1420600b120396400800a80700040500306424080b40c00c821001400c0b01c0c8480703d0a5040002c05000b240511406030083c290703403078000d0504240c2c0440f44c184100d241c1d80811450410b10308042c807405881d885009407a00c60141c1e91340b0000c40881086040b641ca50000d40112001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 889438489 1250 889437239 889437271
    0x403021e030d110615010504091509060b07050c06120c03091204090203090f0601050120120f0903160e01090504030512070306090e0a081b12030702030304060e0a030c030305 76
    0x164404110b8401c01c84020344902d8284103000c0c885a1030302030010449942051940e040300c3c80c5903000404e840581d00441d80104089404241d03002c019003c0da0f20452000f401c000c000202211010000c2000300d0042059400d00a400e4081c00101c0c4a54040f95003200ca02d003000400e11a085406190482441400c0c0c0740380703141c04400c10210380c01c0b41d000149040d50010034000c49600c104281c00d020700044014009540c5010000307071002400460120443e9481c1c050a0070b09034050000c2210603841d29601030f201c9001246107040303900108411400303481034030748003000c3c0b25a0205003822105800040c01d02c07070b030034030310b5100141c80094401c805201c02803000c100106d00780303002140b1031021640c00150407450248160107031010104600000e4102d089014041400c00b401c86142d0480300202d52007280307545062030301e00313007442c643c1c07054490300442405107a540c08801107001e140a0542400f000d413052107000d8032240c0c3c0711401000300d904030740610300003030003504101d600c0480165615a2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 889439739 1250 889438489 889438549
    0x80705010c02060f060301052806090906050a060f0b0304030f030642020a060c020a020319050c0402090306160e060403030903051e0304060305041e0b07030c02060c040302 75
    0xa6801e1100e80c507025030420010403101007641800340360f0020040b4020711190418441840d88105015420b00e041c1f03d10701045400030010f40c0100c0000c080986007000b65081c5070600900400f01500c030307c4038035410404000744c1808290700000c00d8078500407a003481e60f1583c2d0380540c0c04580e110740380c400707164071035500092481418014042481540000441885006600c6141c0107032505c0800d00c8903031686c0d030028549a00190036030407298003240020341201949400d1345014108240250705104060921582d041c0c040220962284610204c41c01090088100420790241e9601250140e01c0100003454908091580102c240e01070b0030b01202c411403103030215103154025001540801c08000041003004020001041c582d41d4606064141c22000040503440b442a0300c1070a0405444070003007800c2c802d8140304a440b0040c400c5e070150340d2032914681036039100070480388000800d1801c41550b0b103403400840d05910503206213a610f45400c0c196402c00001078002500c081c1140c1d00e120341451 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 889440989 1250 889439739 889439741
    0xc0c1504170c010b03010509010608070b030603101d0c0d030c06020319020307030209031606140c030922150321021e0a1707020102070b03150a0e0105010f0302070203071208070501 79
    0x20100c108000100311152000189400e448010b01081160380c5070ac801003018210105833407066030740150349203640380c41d0040064681665103076000020751400c940700710f01d1001000d4a07030740403800c075042e031b0343c5515401c04109035403800e1600603000c2448608030000141081cbc0c000c61b0300a241d4070000c400a1700c803501d803008036001215640c2c0402e900050b01c1526240410544030008190032060500d542000d50081000345040f0b42449200c90201c4c00c00f442ea281441510349c0094082c2c003c2d041c444d422030f1041c42e428149025401c4240c81c0042602c0406815078841e8256a001200030003000600001c40700070f03c4160700c5070740031070107810503e102100800111044d070032641c20007086004c3c401d0170802a0076031080c620a0703805601b0005100141d0300031235000111340c10181d84a803695985001002d46101120482c0c2d80003844180104050304c020300707001d050356001c0c0e0f41d50703049401852054040f8841c801010794540c0c032808003000b24040d9071642e610103e01c02c1c54203505145096403240c2c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 889442239 1250 889440989 889440997
    0x90608041b0e07090909170c03160b010609140d030e010203040515090a050303480618030a0c06020f1b06010312050a08061908240c0c150417 62
    0x311140b03500704140582550700003901000791018103001c11443d100d5a40c0c05904c5000168040c048810201d00100d07406810300c1550304a41c07021000030115400303481d280c59103500074055130000c40d8048402103556140f0901c2851950400342201c03210341015101a50300d0032845c00c5e40d50440c441004040386548448507001c0d203080680240645800025080000c040c2041d003020740268001d101015602c401400721b481403104000e0b810b4001c0c1d9030101d00238030b1803070140950200b4141c65401030a01d020b001581600c100798681d081c0aa031441890300c0c81d201c0c403a0782449800a031400d07001c40c01251540d40205a00c0c1c8200e030303d81c0e00e0100c013400e0100142180310110b0306603401c83c6004100f44030307502074462010b00e22440d000307140200d4061b01504410020b0300c0140913980c640341c5026000d000700c00900c060703c030a204542e2480d1908456188a907061030002a10383d250b140030442c030020400a0f02c258011441c040e000f0300003005903141e40254014816101d6000c24800079000c091094010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 889443489 1250 889442239 889442249
    0x60321042112080f0c03040804030f051b310f150e070e0a120501110309010e0c100c031103071e110a0e0a020c101a130606090608041b 59
    0x66036207000c4508003544511030000b80c4a040c803141c1c804004503010326001c042d6209050140d22031b244c0d102c605001c2c0003809160402030089112540800c14007000040181e07a51a98a0010550b02c043c1802e01442a0402c80030b50b07003584c020b41c101c0a1600e49000c00000070b5000040c002080808004201e00341c5501c181544400b400c150b409001d510044a000c5a000b4810b040070007603c000c49000c60b05109143c4294074104031003030a0041040f0f403c0d00000c101c9520035650a4480c02e01071000c3d8001c00c010403c05010384103940001c011070401842d0044400100d444400380320f0050b413000d440c40c0030b00000b009a40c3c00104641750000340003106c070030401000c00c007640c0003800c10f91074141c030401400840310f4411810b441c0108006500c0d03406580d804a0403010168450b80d01012444c0b80506100d058194103052500041e40000e1801c00c01c892440110340b003d80810341d024040c03045500a028000000715841c0c0d05101c01c6010f0544142c1040c404d80c888060441880307201610705000d5000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 889444739 1250 889443489 889443539
    0x60503040b0a05070801050d050c090f060a1d0c0c2104150305060d03030c0e0d0f020405070c0b06040510080d0f03061706010315060312050a0f030506032104 69
    0x28481030010800d60142d0104100b10708000e181040180906500d105115080c49222080100000c00000384451801060080c050481070705000000b0045000201c80940c061401c081c0c0c00551103481040c600a000c520030000500d5440700342d201750030303036000c0241540c81744600d2840d40c08241000c44646800c07105d24840944031810000352040c41c849d503181c3c2400301802c0000b8004166205140350007242d0341350800250355184803106803404004202030303e51000d0079101c0b42d801c0c040302c7c0201165140c401c8604024503681c0e07100c240d42451800e8406030134090400c1c0000e000b400c2c2a441140c002410000d10f0b411144d5a4404900d04440d00500c0f00000308600310b8006810703014060100607002104800f5000910300e260180c3c1c0b4501440050540c10480c0005851781e1101d40c0047d02847c1c0000d1150081d005034800941103034040890200011f803003030503800981d0f109102d440d008640060184c00e030b103a440c022155040503003412104400030104400070f036651240c14103446031401140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 889445989 1250 889444739 889444741
    0x100621110a0311031b180403030b030d03060e130309090e0709110a03050603071208090a080312010305070605070b06131b180b0f0301050105131d041b0f09110c0601060503 75
    0x3c1418203201034030b8403c11002036110f0742a8030076520b00c028000302c0c5400d22400105985c641c01c084002e048402481034050040000085a40d03a054000d10151140ca16010425884140750040c60001d070080150009034081c02c24800e01c001508070a403010110012103080c2c0380c41e03440400850f900d810160401c0d240025241222607018044c90b5170010040700500b10952404000241c01186844d006100440009100354103981e41c0b03441c8405400740c00f003180d449224804034941501030a000580b0144101d44000501d14440d8040343c0401e42e001000410b030741c40350428801c0c1441d21003e84801151203104020070250075a8182c40010341640d600c0e21421048071941d0b4440342c998200c00c040310810803038200b90303450300001c484c1190b2080c03034520b81e15034180010240d0303801660042c0c80c1000799101250401c3c44a2800e060041d80078580762031680c1e0404455040107a00c911a02807110080c5504206180b0164000d214079600031005904e40750043c0c1ea100d050800980040c1d011903c00706c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 889447239 1250 889445989 889446023
    0x27101401051e2b0603020112021605030706051902090303250b09100c080f0f0403141c0c03020a080103060b0406170a050c0d031d010c081803100621110a03 68
    0x20050114041c3c0381e10411010b0309640001f00a41001d02185911540000d0149400d50034618440b8070103070480140c0303448190503c0c00d80d000c0c03d0103480501c0d4507584281101510a000e10071504440c5004005500d0b001100410b044003000d40140e0301d03031561b6003640540226801e41841881100b0100181c0780080b2070802280482e00045030036002c228945e010081c0d0103072101091038100f803580b51040f02e540c0e80d40c902140c410740010644039051001066402030312002c00c2059142c4103036444284460740612500302d00300c1c02442d05610020724803a0042011074220740c0000718040d03029201080703141c6c07203004560038000700c80b684080d50b41c0140051000d0010a00c941000048120740074078036a0029140100462981d52150a07050300c06d1030021003d03809096240406540011003903150f9905400180c42c0d10103900c800ca0081c00744581c1e051034040b00b80f14800c182e44003d1030104002d40e2040e040d4018100aa104039801c03000008440c1d80c42ea145020440118030030494403119120035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 889448489 1250 889447239 889447297
    0x3090510030c080604050c0c1204031e02031f020d061404050705070506072a03020a050705030721060e0129040605010c061a27101401051e 61
    0x24102442014a0440b0048601c2d511208254220340111000324040d00d0b0700080d843d135031040e88480e90092095005101e1503108a00181040380e0144101c0021040216824a14109465002580354100308a000c2452101495040300701e142d0880060420801d40400c400300c59480e0054800c1c00a61840020b05207000c1c01640c0e03112015160080c108060780e0f482c42e545180180103d000d2040700200c00f400e140c01440740f0f24840200c111041807400e510301b4040d4035252424025a55402200b4000c10281000188801200d4003500b0313191020301a12000d00b0400d803036030022500d25443c3e10036046040000d004403e4840c030304000e00c0800d003c5900308120b103401c91605490042d41440380810080c1c3c0c00c4410703118443d4110380b02150100c1401c0c0c1e044160b071528403101e98804c492400c00ca091065000059240550003220a44161215481c4920260440c0b08048940a10030311180041d4412406009100c0f500c002d154801c0d0b4182d41d0040951f00320800324140c28564140858007a418 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 889449739 1250 889448489 889448509
    0x60114040e0a08133b090c19030302060912031503070518011503090b0103081b0a081c05060a05210613020f0105180103021b0106080c09010e01150c0c090207030905 72
    0xa403400070303401755100f2010302000301030000d5040c107040e60a80c0000e450710018841030807447d500514000c0c603201d5802d5819080c80e040c0c0000c1d07005200c2e05002441c001000600c250550b001107400c80d0071555030b00c0d10000d080c20402d500c3c0f0b826010310700c00002c072900c410f0b003050060070190048001d10341c101101c034003001c084698440c08250401c1c4035203010921203800380b07041d43d4000302041c1e03071203a45801008448500c51b10904051080c0e201c2e280620160401520742c0044030f4003160070013040f81c00b0003411740318240c540a034082e0220f101085a46062103504078051021007091101728009880365060030004c0b5000301040314100120b104614100c8641c61030b558090030103505200812115a030000714010126041c140e0000355600f01201c40c5041c040201c10b081d000303100c0c5945644009031202c9a2001c0c66000340d00203000443c0411860030114141d900c002036416442c01649003c84543c1105074051314040910000890915880d0004060042c0242c841040c00d0b80f030138050088c6240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 889450989 1250 889449739 889449779
    0xc1e09051905091c3c031d060a090f0f030206040c050604241101150306050105040606080a0902011803081c0b060912030f1b010e060114040e0a0813 65
    0x8038182c218161030101200d01039802461504200c0281c900d01425444103041c01000c088512483d08000724801c2c98105c0402001c00e99001c7c44000c0b00c48050001310000c400004034580c1142c0002004400300d5808640c03064061140403010740303082c4d142d07030342c41050030001070340140c10400800c0203200d01da0b28228024031060f111309282c41d1400e207140c02d1681554240c9500e4619034101180042d104020325404c400c4000000c1241d6005c419a0404000f06880125803007802c0c003000181520b1b02e80700301e0044508030703103070350103903950700d5440f500203050500c81217062004076800b0082c007a40c861812405144900801035603096215805c13071b8040c00d020000d407a0030f820901e51648a88031041520048501074035001791840892150324218040c008404017040f801044c072085005041d000741c1c981c05100710080103150b44900d40719407071701c90034001c0d400780b080c0c0c1d500031441604260340240007048500f401c2d01c508aa0654804005500c41c00030440084840034003407140700c1982c0f00e9a18401d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 889452239 1250 889450989 889450993
    0x90b22080a210804032001110901090506040f0e1e040f051006050312090a0b0d15061b02151c0b0a0518010e07051204061a010305040c1e0905190509 65
    0x2038461400821083d0700510084c10080034640701e080c00e40002405000345544800240300ca9a180c115410b100c1c2c200b003841d0343c00148008000144d0b41042403c4509694016200518050400e0310017a00900e0160240c44004c0c0c5c8620388089420101c4c41e054055881a2481c400361a00c60800360f1800840d859500740041c5840c1e403c001d41e42d000507503268079247c024215621001c4000024800114135400310000c4000010000b80e801c03d294050f140d01100341800782c000d5034984600315010802d26400c9407841c41c4011100b405481c10013040200d1200b80407a182c60300c186410203c400303c2c0c481032030703100d0709446000804103490640030130009401c095034942c07000406049d10701512581032194000308901c0300c0200d04060310070800c48065000354071101085003030624210004142d00a500f0a0440c454056800705620901429000365044001c452505084c11400c040440b0b500c43c1c803040d0b00c909000d0001e040e89603030194520a00040c416221511445054042595401410b22f621a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 889453489 1250 889452239 889452293
    0x1201030c170a170c0f06040b0c0304080a0e041116020909010c1b050f16050301050c09010806040f0f1d0c010507080a05071a011e05060406090b22080a 66
    0x4001218140b05030054141c100c0110001480a030f90300c01c08044c100a40103040e2080302c40b0703000084880c0250304c0790001014507924031000421500050740c000740382020070041450b00a20071107040c113050742c000303100003001c00300440d07441c00139400030047c1091a00e200044405502d0308404042d802142e080003401101003020004101d4404c80316002404540d40700700b0004d200c130800c8140705441201c0102c0b51001190700c2c55510040313561040340d101e50308180c00610230018078800d9440c1e03468180c60310b40d4141c88007070030007003e4400000356192040d6124851010078540d8091041c1e2500342c4c90788080c5c108558003801e420184245c1c0722506106003040715400091010044844020700b0b840c150781c443d0340324a899101900039106402d410500030303001180050f81c00b040e0102214001d8040c1c80265601da0a11480b030003184295408589251020841c441000d0014440d2424005802c3c07407110b21011160f00c0c0b6805a08040841c1d07101c000c800080101c5c4984000040144503205240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 889454739 1250 889453489 889453529
    0x509132a0c031d0d03050301081b2101110f0c1002070804030b0a020d110c010e1506120106080d050c060703050103020d0215120a0209010f080c041511031201030c 71
    0x10100c0400d20003010000000c00c00ea0b00f0054031030101c0d0860038010211074500d04103082c0180550030a001d40c0807a8080c0c80804800300312100c00e050607d40014048104680d40d6040360300b030382c00e00c10241c6009552120941d824000c011402412001050601c0640b1088038000b580d03e800ca00c2c0c281040c48510410403940454566801c0d6001c80e03a0141038282240e9400003e078010340209603045010500b0a00b0014444810f05c024150712074800c0020050302c010300301c01c01d41d18000e000c48100501d086c1804030705e55040c0400c2c450f07119864131001007040c03981e5005040c60902050041c200140010642045510301480a2508088103140c1442613505580006101400c1c01e440240700304c29000740c4074640402102510f50b030780e2040c00c150301285013200c6050081c1d8000840321340001d2030980c4640f10b050151078410301807806408481d080a003800081d11804142100c0001480101c007510402c00708204010f0640549040d002238595140d40f52a410a05880d001000e8a0b241c522880030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 889455989 1250 889454739 889454747
    0x121e080115050c151b0d020706050a1a10020304030212030301030302060f16030b0a1d160f020c0d0203011107060e0c150901081b040f05090604090507060c030509132a 73
    0x3541326203842480c2e241d40c4600040d202c000b107645100048100f03000c40c0c4002043c4696014014403801000140520342d03843c82d40408a680a120030309400c01030050303201d114209280c090f8050310b070900450b45899126000590900c40700085007513140d00001c0103104050b41031103107640000b0300c0c6c0c50054240c20401c1c1d841403151608021002010360302e01e60903080d9070782c1c0c080400c01000141074401d1403183c449012a1500b07002c55480161440b0112121209403003082100304052117540030309400c00340e150811600540581040c0c0c1e15640b10308820840d903820000a00c011842013000141c06005900e682d420702142d241034a06ca01e5040d41420081c1d5865030480b1182f02c0f0074a071642003503860800f50f15280c1140b15070740c0c06460010070f0214400780040707808400d81d10100d170151041da44103400c0101740c40d101d40e0000d003203800110003080854001c84034212601c0c07107401d105040031310080205010369100780300084c12540701c81d200ca1880000301540d254640c815060191089400e4138090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 889457239 1250 889455989 889456003
    0x31504200108360102070c0602060105100c0c0b0f12010503010603230106090501090e07080102040501200304030f030309030f172e14010914030a121e080115050c 71
    0x7140352455950004043e0056102503428040c1007064604851152140c0c000c4d0030480341118907041040020500900004186041742e000601000c0b0000c0401c030121592010a0301c102d501e04541800822104901c001811030050404078003600d8050b02030616100c1041030b401980283d262200c1030002c61030800382840c0114441b03507000c5004810800e9240102041d9020790f240c1c0e0b25010000c500308200d60814551402c10104990110342c480410508038401c40c0310f850301240050502c5220741c95200200007801025005480c281513680d10781d8140202006021400280d454000c3c00400d5088006000305d04000c0c58035010b030500898210481c0c08002d031100c07a02c0034000d11092200c00c60303035503d9880052225a1110079035511013400560b21700503100340707021460200c4085452a0540c560111403d0020010981150f2a03244c1c1a5400300301d446200030881240000c208544560051009825195032541c0280d85040541e03a815104d4591706c6042001c204041840147e00042e59 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 889458489 1250 889457239 889457251
    0x1a04031e020706050c0c040c0e040c0311031b120106050319050405061f0f030b090105131707081210060e1923031b0a0f050d12030209031504200108 65
    0x41c5e60b0742980b141980c5401016841d00b03034400e007030100b045020b540c040054540c1590545090020941d441d105400f6a9404007018040340c00500006828008045c1d5080124a0384c10a2910305202d90b9440d5080c49400d8208501244c0c00100740843c0c0c103280280b000fa41c0000d00170810080c2000da543c00c0c0c032424090200000c41c00382100024a044151009000030104d081c1c1c680e840903540d242c500e0f4030400c1162011034035440e0400003544080301d06a003121060f4030100b2080707038562805c501003c0c1e030460a0191040402480151650301902d0320712030040c1c50001403404040c0c90302e1300c002e0404401841c51401860b5100b84101d81441c018403800568404400700f0381590480c180344592a000300020390f5240c41036890342c020b01591b400d40350b03032030b00b0301035507002410b546800e1004040c014920034140c00041045400000c07920462503000007400c11715025182c94402c00000e40380a60183c144400300c1c0c0d5100920041141c1040d030308140f01e8082003140e099000d0344e00043c014000081078 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 889459739 1250 889458489 889458497
    0xe070c0c060311160c09061e080601080a031d1c26090607080d240605070c030b070c0203010f0f240501050705010209060301030b011403160618031a04031e020706 71
    0x3040d04009810440b00040c0c102e8840400072260b5441403000b47e00d250440e0041c8c200042c0d4000f05c0c1c81c0e003000c907a49041e60340d02e03401028000607a5038110386014010007a1f1010403414510f03110b40d40d4403144003215032886411401c4420a2900f058415010296140311200c0c100c081440d10242c0701078140e480e00d6204803445505d40c1d41500349040ae602ca0903104c40300451410310b055003200248908061140480340b007451045445500560b0648a868009480024400d00820000e880b000000c0da0013843c3d071805902d856029030100b8291141200708040700382c2c07198043d034041c4142d40304540d40743c0055103a000307101c81c030745101a9500d0918043c00c0c1c10080001002e509200c2d003501110b0200c1c9003e01155940d603540d0030304064a103020300550150369400c5800f51719516002640e400140020009507510925280080c0c421514a0004200d900311340007000010800d5040e02c2181049940494a810701e003d02d0300914034004000817180c0c2d804108561994190b0001e04c0030180c640302e084c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 889460989 1250 889459739 889459777
    0xf1b050a020a0b010b12090304180902011701060503160302041203030b0102030f0304081804090c050f0d060e0d031512060c03020c100902040e030a08061003060e070c0c060311 77
    0x3a04034109212510080d000c45016000082d0215020004001c003120011000c001925801c2e0903e85a11640c402c21300c0701e01101c0d0704030b003a1804c00e500c911442c9105040018030315244400110301407009034032038004587c0200c204890003090314140321807410302d441c0443c909070a005600141050010002e0f0800d07a903041707000d8699000300111554010b85150301034581c94549480c40c0c05500030700b40c040d00c4425140c102040c1782854090b040a51b58413030350203000c8a0504040c800745081e02d41c01141d000c1c88415601011460601c43c1241b02c1d825000907001e0300310301800c0a0203486070b103000f85038500e07d142010016541d210102c00c0b0140d5102d0000b0030342e00c1e2800011006401485106200c078010b81d15419401a001e40c03141c0c42d4603100755014001d000b0b8048445460b030082000c1000800c0302480054070501d407110140743c084205c0e00380011815200d500e07286c4004411103511003c80e50030701550050169420320840140000d00d02408850700135030a40700180605a510303007400381104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 889462239 1250 889460989 889461007
    0x80702210712110a050a0c1d150310020706360b0a0609020d0b03010617190f0804030b1005040501061b020f03010c02070f05060903210403051e010f1b05 67
    0xc0f80f184400b0142e14100d41e101016420b1182e00d0305034070581101c4500340307220002201c00c10411502c2403240042040007040d42c0b100d440c0d00f20614101e000c5541401442000c6503146114405014100c0c090000010481001c0203c0450b075090203134a0101c0102810011901d81e64030f8624049061b40f154981c80e05403100c801c103e001d005550007040c009030000ca1500503988140e4810404131004170000e1001e00d9407080d2441d0a51100a50348201d50080288440c0d4016078806d500d100700d101d20800720541203242c40b04500741d00a50001c0b0364610000040c8004626003202010213840c08890401007949085c03c05004c0641207504084030429410384d403c2956298403000d4550f8401400070300c41240020310003034640754240500d5900c21915600800c1074140102641c41400002c0c001301846410702c0c0f96000f0015a5240d6011811010080440020010311204081d01280440c2c580320303070308801306142940d110004480c200da1070b204001d4601106240f0340a07203440c1d10306009584036000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 889463489 1250 889462239 889462247
    0x605040b03060f1f03021819050106050405010c1119360e0c03010905100f0204050a1a0d0603050d0806030d0e09062d100f020a0204052203080702210712 67
    0x1644043c0d4007608450034800f80002510407c0e10403854502c034020510b11040b140000c803032089c0141c2002441c01e0105000390b5028034a0401c00600480c8619a41e1840c1c0001031142c4440301c02c06c54001022207070821014584418400c00303100301c182070311828041e004001481100049a15414a4840360a00000d500c02d01c42c141d0605c10240003170008501c0d9003880d40d910142d85158000c1c4520381701e52a1004d9038180300380c9003070f01c000030302c1d10203440e1801c03040c02c48881c600d025041d2484010001c0b090310850a02c1142c1c0114416030140c68145d0300e214018004c0031000f80611b0103904120f51100c4480d91203020903044010454400300c640d1a03079004101032100311049109608803044140c3ca6016070011001e070443c00840d980b02c04420b403450200c5440ea641018400907074000204040145850340060f5880a650840100000148240705058001c0880141c0100c0c001005010f052035061004610a00080301e000c0d01300d81c2d00c116030003800e104403040540100866030381c2c6080c0c00c0c46 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 889464739 1250 889463489 889463551
    0x18030806060a2d020601060c150e12181801081e16060207140301290d081c0509120a0c060207020a1e06020105100909020406180605040b03060f 63
    0x15070022441c94201c03d01071064807000c0c502035038054801c60300000f0b0414401e40107104045e5004000f010704010f000301c0000030300380320f5030742e80d42d1030140750a0320403400300810103400c10340403408600d21482020000e01c003e8081003646000000368000052010120001d40d40d044916405400703114000321f410103034204521140041c827203402d0305030009000c0754000f5032201a180d140b0302500c04131014000b01400c88002d4605010701c1c1d04110b00c4291949680707201c040782c6402c09040041201101d0307135440001c0c0e11006507804c242076850102d000300c480324400c0682c462829002003a8808003d80421040e0090319003090400a541068104108240d01510121680a45071003805a10b40c0400514025000440f1051841648002400340c5c41406401c6c0604e1001d445400d0050821281e507001d06021141030340c00640315040044c1800100d640402d100c000c56100140480c109006c000566809020b4103200358407010920840d141e15684240d00004102501e81d0b030b5409034999080d00300c1d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 889465989 1250 889464739 889464767
    0x1606060b0409021c0c0801030b2a0a08070c080f07151109090a05150d06021902070801140603070521030f0901110d021c030b0604080304030618030806060a 68
    0xc804500082c02030303441c0c0c001d41074603410b5400c140c56120720a071000003240d041003044400205030000410108030003880f240e41082c9002103101d2220b200717900c60341404c00f004140c8000344000081d9804101e52016803260841e065180004194243e51145000e034010900d01a9240e100040d604080001141c907011842014110902007046004c80e0310b011500f0500645004008200005500034400c2c41594801c0c0b030424170b01c01703801c1c2c103680c10b010080100305001c8840c5c5508005114420007412100d42c160806039000701a044e06003400c05003503d00c0781c100e47d02c119081c1e10038400030760b901050000c15114240e40c181c00100054444100000750710314000098040004d04bd03e4100026000b080304480c00c0e2154500061a2180959103900041da9000142c110901c2c1c03000303140b01d040112009450074503003c10b5194645000403c03942c040c1c0e0241340260b01c002010010011107004951b0b041481a081144030349944c0ca014041c4c0f04003c01c418440d400000e8050085405030b414100e8440b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 889467239 1250 889465989 889466009
    0x110d0f030617060906071e030c0c02030a0c0302030c041a0d080f04060f1d100806041d1e030901090b090319060504060b041e0504021c0b071202040308160606 69
    0x1801c900140781c40e550250342c20b09450140c10001070001c0d009000d01c0407c0789030b403c80400107000c52031049000b013003219a01020401d41c0c001c02c001503a420415003400030b000d0200342d41f1003407451040600c1c00010510389400b503400e042c4100e410104005406100721030603213031011200401d140c4000c83e4030410180d002445804600410710700c1d032140503104d03440000d4640c0004901c58000308514079400400700c0e03a00059031200302000c24440c11440b9007141d00a41301003014103042141210b12080c180154115070b00841c04000519001c0810305603e44510380074514044c41d5a00003040f0b920b880c05000d016640005c0c13501e0103900d040040d40b81001c0c074403d0385070307542c0140d2800c140a00707001d0340d0582d0b00a040c8003c80c1c80c580740512814102198002a102e06084891418000b07070070018010303640140c0c00300c1032701c3c500500c1c02d10814146114000d090300b20b02d0018030103003880e911107001c0c469080c41032006000040c0c040049400101c4403500d2b1081d0320b0190728001010740340d40e0b00400400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 889468489 1250 889467239 889467269
    0x230c06070503011a2b0608030c0f010f0e0a0308340f1826030c0a050d020a12030e0f10020405040c0e090c090a0306091a07110d0f0306 59
    0x810781c4072020314140d465031400b407030000981200e88400c40c003400032888a4101d152605040354088000000c8001e6401e400101d40c80b03584448550031a00081c2c1000d01d940c00c01003da81591500b84030703480e0041c16819003008001903000ea503035a5a5a407140040c18045141e0100b03040780040c0003800701c1444444030740c01c03002c291942c00c81d910f01d07e031119030b030085242c010312198010300540111007070740205412005614905120000360082c1c0c480380d501251090341c0d52200f800f40c140000c040c406200c00040c8005016444c0c0280b80c61607040401c011500488640703400111040804041c01007185008245540d80d550203904103d0650302c0440644940b4035040081c0c2c0694021b00100c0b182242c040214080450b0300756981d0300780c9c91000380e22103000c000044456400300d028020501000d801d640c2015200e580b50700845901e540b040d07440b8a0340200944a90408241aa90261207803a2240510b5680d0300950368501024031350606024080786030300d41c06486944000d0007000301d5003c800306 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 889469739 1250 889468489 889468501
    0x5060402041e1a01200d05090604090504060c14120103122c010809010b150a0e09040605060306070e061c42030203070b130e090303101401230c06 64
    0x2284a40604490201e40b0900940400086a0303445c01c000300c0c0c1e0780000c0d1960302890001115264072400c8491360200007808040342d004100c1c17148500c160f100b1030001030354075504000a060300b243c1d41100c1e002e40004028034440c480011071094110b0b64006046e1244544030350040c3c440c40098a100309044454040002100f0308284035680d041c01e003030701c4580903a00c48122941c01d950105110a4014521080c0d1444c0341d107015008240f04a040c6c80c00d010012846000582090741c10349040d103c01f901c0d402031104924050003d035801180e24240005001d89640110f4140e00404031803160030440210701081d402519000b40c081c00c54881410140440c1140c020b07022641c01090703034480710320048141c00c000340c0300d68409000e40c2e030010010160185000e90409141e40011481e6030500110800010700084410085000d91008809540c891131710310410103c0030031070f40c004501c02c0714035940307a0032590300842505a0350030846400700c80000405003650042c8110302203100b2510400c010488 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 889470989 1250 889469739 889469771
    0x50705040e04030c02100906020a03080402031501060c0309050f0f060304050a0209010603020c100c050412060b030d1d011713030c080a05070201021603020a090e0c0d060618050405060402041e 84
    0x7011905c00c0b50080d0341005452400c5504e41501c1c092400560311903011540840e00a42c016540320b44010101c0e5405840b5003c0101281d500b0f90007400800e2030302114804064205403444064002a40c074440c031111190001078409001030042c44c0180c0300040807074148802800b2100090f81c001d400c2c100a940c2d141802030003580700f01d207003901c0781c010607080800c9140c4034020032628040d150b4071141458189614901c10404020045403595540c0c400c3c1c1e501520107010406c0b9030803407505e6845030000034400007006803076a0440302e0b0400070680c147c002c9003940801e2580c8c200341340075004090481c1c103127000d40d06504090340160200c0c00c04500c0021a42d4800010102c0034030030303800d5424910000700e01c00400429408002c0d032040d0a0001404100c483d45d209042c2d04040b40c04941094100c940881c4804200d80340542c0d4083d1180b80602100103040c4103101d0104503aa0100010301c1e198480688980010348024451a10798210360751040086850080c10781d12a84100715040d46016492 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 889472239 1250 889470989 889471007
    0x19050a020405090d0e0406030f02090c07050a0819050909012303030f0310080a0f0224030f0f070c150b010201090212031914030f22080c0105010503070513050705040e0403 75
    0x4c0052011200030040703084c540079450840380d00030341c16001900242c0c20440c92950042030180100da041c030a410100d0020803140c06880e02840348181d0703c00c0112203110502c61008040028401c0030010b5640d81c0e15450600c504440f49c440b00200c3e11500340c0c03841c051501000307603d10b030701d1700c80803a21484000031400250b00034460001029071480e90f90440c10344411504034060554080014940007504060000c9585841d0240900795207407501707003a82c00c0542003a9208a2a25086000c011000c4081154130703421445034281808221490f54442c10841040c1c0ba0f007008a030340301e0070a03400c11390003500101d0085e640144000003100d440c0d03d20960365000f082d07040306000401110091203c0c05140e000540e98680c3c800c0310714541e9114011488014081c1ca4000c034a819030032120b605400d041d013000f4080d845208442d0351506014622800d4910603042544285c000751000c11840e5a00c009a0029031110b65001c5596a154281607509016542c00b842c804181042040101030340080c0030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 889473489 1250 889472239 889472263
    0xc03140c032212051207021c03020a05010b0102011a0103200f0a0f0512011e08013e04150c050d030e011a0a05060f070f0507050907020f19050a02040509 67
    0x20500d42d9078031240d41840b4040703075000d813040d085000f0398041c2e0b11012000f40955400035040f04229059214200343c00c035000501a801070708003e80c41c0c03003007101c2802040d058060900c000e1164006180040c030740034440d140d040781815512400801d2a00c0c4407005180c0000c5200d998585600320019002e00030b60024118400068442451125090041d000d40300605494050982c191303003090914100c054820750080c2c0421a1003c0c0000c160b102401040d061043c90380b00f410001120b008900c040c400d100c0054100b102c10f802c0100601d00303181094038100c801e0011480b040102c00a402d0340c5618861201411501400003e0000550190018070031401c501008020030f0040180508a503025403448651050040f081001503140a0010344100c0f0301241e0701034904011940c5003040151181e808032a25003289108016514080c94403561003c028006002000c07904420103403184481283d503c3c1000480d2590f105000040081540d0140d016200700300d10b091840d5120b40c1c507898560700c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 889474739 1250 889473489 889473547
    0x1413050d11060606160203100b0f06041809030c08071a0f060a060f05040e010e01150c030210050c1b010608061806010308090117010b0703080a0207030c03140c03 71
    0xc602140c403826990041c0c0c2210800740030661a00410841c150b48188144d4280203100c90300080035030360034800340d641203c4907400001c03418204801d0080b5010f500400d24400d080c2440308100c080b212a0750071082c204a8900001c0700079552070140c03004030440341d001c0d000034404900041000103118007138072050b44074800d40420b59521000f203070159400310f43c09e07500811890010040c5a0044003102d002c4c1c13041d410054103141d1100c3e210702c140c0e0004d03030196083c0040c040041001c0e80502d1840b507000681441d1a407111000340c0c9010b075450075240c4021a915503504001144000d0307040503181c280c40e0801e00401c011030912040c9001e04031034002d0701024024000402c0002208030b0420105400c550060001a0304c0c50329000100e41203200c10324180300100c130020900468a00c5c0043c06040d8200403142c4418107030034002d00c6028010300c2003941c144100070020100350866500c0780465418600000680c0003240700480d28050000d10419031706c00400e034054905400345510661a6000030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 889475989 1250 889474739 889474753
    0xe030c0307051f0501050607030c2607020a0f0b1e0f0d090c0f05010f051e040806150103090f1202010960111c0b0d0506060f04141305 59
    0x20750f0070850741d003072203401d600c20020061480080d00a192042c84140164100c1703446121011002024600820b000c2c440204006841c41c110710b0001c0744075028141071b05020503401e0825407004040d100308a8428040d00145141101c40d41190f011200546281c04426440d141711074202000360810750070444040e004030901141800c4144540800c07100140c1d03c01d2806040200d00342c66940c4000082105168003c000825520301c000083c001810404020b0616103480705240c88800100079500c0d04041c00c0074046400704070f03055030220405405c0303411a880268400d0040c1e006014855005198003800c2ca020000d01c800403000c0156800a4000d8541c1d000c40b05114400d43c6800030904540325010900f641000301365040c1d0401403040e00540011226401854805560001c818410300e4400c03d24116100420038007400400d0ba07803e03101c21100044a9850a0301d035940140814040e03100d00849117841d60f0749070080c28100b64a2000e034405401d01e14595101d01c07078005c1c0c09403001c0c45660 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 889477239 1250 889475989 889476043
    0xa0609080f1b04090f050304030503070c0807061202030c1c0501050f03011509050c0d1109010f02030901080c0a1206080a0203060906090604030818010e0a150209130e030c030705 78
    0x100c0c031040c00d000580c002c0d007001c0024208000041ca00401c06032000c00a6410340c50001e0802c000420207540154021a01d86115141440180c4a16004022283c02c440400c0004a80044001c2a8200040c2002d6100c5e6180c000708031103400b030420724a028035038415502c4010003141d0700c4181a03450031740b08074000e40080003d2509032140581c154030302803011039040000c5940356001030380102c2c5a00555140c0f903540321851007595110000480c002c0c00c0001d90007010360b0801a000c11107400750002d9401c0055240010307001150043c070030900610005868541248034450300000c80c0f030884010031650f234580c541c088d560901a0781c200c0c0a4868500031544000001903c00d201e0f441e00b1004050f540d89035502194044c80c060722041140441248103c0d02c02000c0c00381001d00032400c402000340b0487c5041c40d5070042c41d0801c004240a1040003020591b844000c01511802803030311010500c000b400d20350700e242d4842c548000e522400046000001c001e00400d4103c400c1590480c074400c45c020300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 889478489 1250 889477239 889477243
    0x3030a0f060b0f0d0b04110c0c0301050105090f16020f03070317010603200d15140a060305100e060f1801061701050a06030c02160609081501270b0a0609080f 69
    0x41c0f4248440760809000251000c041c90700103140440700074001103103043c0a109420500e41250600c140e180c0c010b45641c84103400c00340f00311801000116442ca400341084481c8603158800031740b409185031b912000304a1900c0c02084803070780700d11140080301e0399408103040040504035911550031404a1020000900e24464003400c941c103c3d40d200c90030240b50542d1002002d030307400380c0a0820195140d00c103034140850803a8060004151009255450440d031404010010304260820024036203800103026512105062080907100800c0ea8a070154507024006824402e0496178075030b0102c01d5003006440c06d9441c0f04800e049442c00d448010040c01035000c0741c6250242400f81030307003102040000f002514030940024401170340f1030041c1d650661900210805c40c21040d0810b9001c1b400c003100030070060804000314840b032002d94007003400550408051f400e01c1400c00350f031000807000c0000000d220a003550701017898154000d201200e00c9569103809030500d0a10303c507018240c0140d40401102c0702c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 889479739 1250 889478489 889478497
    0x30c0212030706050c0f040b0d0f110406080f0c03060d0c171606021218040b1914010801050f01081009021801172e0509040602032a030105010f030b0303030a0f060b 72
    0x3006c0550f03170404e414031241c40003503085922003408403030b2120080e4000d20120312640386480c0400703024075512418240c0252103098080d25116540700c42008001201000c2c00984c1d4108408a8000c10b0081c80d03401c003012919401e80100b04d00c80301d280c0511001110010f034030303c0900d0f0310807841d805060f51804140d032120303401c0300c4c4801c1043c000c02c841111100810903007000100c0007000029000161000316103580d08014282940044841c0180f0085c005040f06145802d42480c100d8800c1d0304080200380080070802480381071000104c003140402c2c2c0d0301d050503800341001820840d150030120f1418008036941d840d04901140c0416014809000c4442c0d82601c121541282d120041600600c404007920440e40080c2141c05403c0d40030072a50303240f504c90740c0124064500036132203041021200f0307002803450003031300c02d410381c996010f049010301442501d046403c2400c0284a07025940c0040d0064000c2e610260340c1400000100840c0c1074640c0d010714008a01d101c0200003a0703445a0721100c0c5442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 889480989 1250 889479739 889479757
    0x15060c03020d0819090c051c02150306120d03090c06050f03060d1b03031709030901080415200c010e07080a1103010f06270c050d0504030c0212030706050c 68
    0x3000601094940c00340014035003100210342e80e40d28543c0900000004c951290004403000c4440c404101f141e0301d001003203507032100180c4503600302c0c1550385e60024415090180c203201b9202404000296503503104242c0c8207030a10110300f90f80ca07c0b0312000c801801808450800c0710070b802c0327410000c1401d91003681502c05034440821010300d9922010700300040b442d114081103503940c1111314281021031100341c04000841c82500d403888003071440940c0e00318421000341801c40139841449004141d81c3d200440a070066000100340d104400c0c01d100c150082c00d621000d003c0441c40d0382e04040180320220000b13210184640c4000c01c0a140000d403280d481c0c040c2403180000d1503101e100d0300004207003c1d002c3c1702c3c6400c0000b00006036004d10040c0030b80c20750303101d644012001100c0889816011450010180507050b400608204200c40450003610700e00841c800020200c0c2e480000070300f0980610302110001c0d80090410303950000581015641ea0f110010803140c2d40c0c10170011401d501d502d0415208011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 889482239 1250 889480989 889480993
    0x902070c030609051c051206040b060306090406060308070809030c04060e010b09040e0613021305010e151903050609010f0e03030103330213060f0e0906040b04020d15060c0302 77
    0x41d00e107881d900040c002c1c6a0083e91035000b4520903401603c420f2443e0304891555031501602c0d01d0f0b4a4520421249004010034000e600305004880f00d5590030084a030310640444001005491700d040440052115800041c4510400075050090180c1000a090040303012400c44a20300c1c0010140320546e039541c814180d14041000c0103001c18000e140191415610203800001c81d9048440c6140c60300a0903107030b0008074012240310400b0760800480c407940d094002001409154136140c0303e800140c10080000f05011128040501a50340b00c02c0d0030301c400d04910505114079501c03401d05541b00c51080d217541949600c2c1483c00c11008400d8017810501c0034450f0081c40c1503a00e15290310311841d4240c0d41400021305204407110300c0c884c60303401144498804990040e101e0000104901e103291241d000038050140811801220b80c0e4406080440100295000142502c80b00d01040280c4074000c0500c0d0b2080c000301c0c004810146c580d001d440c58501c01207681e004141d5410080c1d418640040b406801a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 889483489 1250 889482239 889482263
    0x60a23040e1014100e03010f060e060a1d010605030a0e010c03060f152007170a0b0708190902010e15070c0608060105120709151d03010c0210051b130906090207 70
    0x200d011710303188201c0c40c0018002041007022600c60904407009900700c40b000105001c180038231401d240e8000740141c6020344064a520366001c5849903618014450700080040000010343d01040720341180c80c00a005400a02c2a4107104001901501c1c15001d40446186081000070740401603507902c84900c03509880b01c1414a501c000450f04502c05100b420840f44140500011414100f02d160400e250f1080058492034101e8a024640e803540504044100010380050001103500c1c0c85024101b1040326000051b001c03014070041c0d030703000307100980c0a61114002c0b0b0f0a05c0400d030300c0c90050050500c581001740715180c82e140c2c16a4400800d07620240016000d2100c405841502001190000c4441c24083e000e0355940380d00401e0002c0c410341c072100261000c01c4074507542151403204519000300724000d0110800c017210081d5a404494989034031652a03001160f41400e000303100c841000800c2140703d95a22038840c0c400034903100d81c42485885894031000041d80045403003034074405540440c900e610 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 889484739 1250 889483489 889483519
    0x1101091d150102241806070203190507030e060a030908030109020a0e03030f0a0c050c0d081b151605120c070b0f01030c03060e031b070801060b09060a23040e1014 71
    0x40d240100105c041c00480360b02c0c130302d050f00b040001c2032107021a940110750b40c01d82c46003176400384038002201e401800028085180001c0c0c1113000c1d40483c102c1a13800c80d403502d0b00c0203400c9014041c07020019000c10301c0000080340e2495540c00078808240d1945174103a00c00504414155244280390b0840194002072051003500d521908480c0181d50140c1e0403507002402100004080c403113074030070844505000080c00741011043d5522050001515806030030307141c081702c45119090000a20010040560750709400c003140c022015210070341c0400c140e801707240c9012001c40b01a07902180c416102c0c00d0340c3d60005483c803810400400c3c10380342d20940b800c00c0c01d440c6030350b80f5002d4101840e5800450105105021041c2c0c22028411a941c03c29801419014503103402c803030843c0d0858121510500702006513212070388940301201d81c0103609180948018802c518000708003007044203040c2c407100d00001d000860219089900740220090b1360070152175540c40c00c0070b6240c829000304003a04600d11150303181c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 889485989 1250 889484739 889484803
    0x80c0405060102070305250e160318060501171203010b1602310f0207050307140111040609061218060c0509060c0f011103131101091d150102 62
    0x81c2241041c0111a0040e40b203566007030400d179056090081a0200034113110440105101074002041111805240b9040c04080035041e090103a014031700341515580b40011100043e5615840b694128004100c50f5860f49044d010640c020b480c2700f2040d11074181d04402c1101c0c60400c50341200e007041d102a18180300c408000a21242150099a1140404035500854a500d9290480c0c07281c0a03089081c420a1028096084030217540c41c03003070b8252040c445140000c01c00421901040e8010303c01d4211550f10040c10350240c06458440301d1202004100000c1c12500302c0200000e4070351546882809400c203001c2203040700c860100141c4256035410300e00d008503000c0c2d0311400c903046940c0350142c605200400819070301d40c450703400d070916a1300800b034a1036000420b110303450004200911451031400c1c200403486c00c0046604000d01142144075644c8906c1c1e0003000c03140c000742010040b0070940d041000d5201b190100c2100c002d880c83c60302c0c15a621320b946c1301040b0022008241005800390364410b000c040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 889487239 1250 889485989 889485991
    0x506010203121504091707051b0a0302040f182d0c26011506020105010b13150c0f2109050102030f0a030902030313031b0b0418180309060f09080c0405 66
    0x44d002580c03483d04d200800c0b10301607528010400c1520707855862402d46003403841c0c0038040348070900154600f0048800c136662a5840400c4940469001c1781c1c02d1041056000281100da0b0050401902d007140002080382a042410540281c0c1c03504070680b0b803030310040c4005600d198100401a80f0051418001c00144501409100c04080d400b00c00402c003d481c40350842d0b60341034054100d101c840780c0420a9550901400c1d000d84401c0c0200d5040c1a041c2203074000c1c0035514040e0343c0310034500904101c0f40ca486000c84000b060b4002c480510785480c00d0801c0c09000ba804159815041c55401408030040e01a9180c0c00803504181c0c021403030098034500303090841d005142c1480803d620b9030480001345e50104081c02c04004215000760085d861803a007500e10740303c0f90450b02c608002e01401040304000c07400079901110600c000c00307002d0807450440303100148600d50f0502921500600540103041e408105034081c0c031034540310151a4118480c003650801d0040c0b150850307aa006003007403810f505141e0045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 889488489 1250 889487239 889487281
    0x227190b04090308010810151a0c0d030204050f01020a020f0108070e0d081312030516080417010516110a0f0503040e0106080601020c0d0209040303090c05100e0301050601020312 78
    0x80c51119a00014041c2c82002406400113a490401401303805030500c0380031013144a103807080003100c414070741c0c196001c140380c0300708420480c12003440c071680362500040712280d41450342a12404500b07000060020b400034003905000e040e0049080703205500020303c5941c0613800901860301540c1d0b0360011114000020205020800008540f109588894030860401f500c501c403026110807a014030203100c1d600315405000120500910712020907004000c0701d0a00c000b00b011344003000500d0800c007600c0d01c12680304e81e00800e24091106032034003042d44a0b45c0100540003a400208000103c1207401c02c100300503842091300400fa02c4030001c1c2d0b000c5500030045100d1000e983c1090303950345189400030b900b40d20160210f402c1c0300c100a650740c0d045c020701d21902c0c2c2c121660724641110782c000c02c00e00c110003400181815600c041c400280308684140c1401002e004114501c81704412a004164001240010f8002c0d800d0002090302980080300756101c9103102ea04403e01540c80c0b181d801d611540040c09 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 889489739 1250 889488489 889488491
    0x50a0c0936090803040501050604090b07030e12030406090308010e0105010912050f030309071d0705071509060c020102040509220b0a020702030601120b06041103070c02010203040f080604022719 85
    0x8041e5480d02a100c0114000c105164491606060803800d4a43c0140300e280f00d285020404030004180003011074024880785030014071500309403c01c516146950481f010b160b103012040004100e085d8000307801041c0320f552000c5c2c40c1c1e41d982540400d4100c0c2070054078082075003010248038483c48104c40d40c00315400750045552032001e0100060843c3d01c15915804280c2103a80280f00c10383e0701d280940c440c401384039034600c0a03113401d09008046014085004001c0d4003141c2071001385c0483c40d04804252600620100318610310080068000c1d03000d40b1540e07014880620000f025002c5511511882c0c800700d1800e8014840e40307036219400c5c1174008081a42d05507080c0510405600c0801a640c0600603501030031600d480a03040c00e020b0786000420442c851820700505102c604921350030b40790440200d0034440c62010700c51006034114003540e04442c0070504138000009201600041710b500550003511410032400c2c85084c180c01d4030f540c06543d070740c0e01021b1324082031a20204083c510700d92001554 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 889490989 1250 889489739 889489829
    0x504021c0203040606081209031509010e0706020304140a030215030408120f04060b1e011d090a050615070c050d060e011a030613051203100b0a03050a0c09 68
    0x20340c40880e0000c0c1c40555006039510020301c1000d0f0100000455110030405840c103040c40040080e5540321924140100c1c00e1850000c502980d100f500310b0002c1507419010342d06c07855140d0400a50f80d411510644440c0301641c0d600e07a03200e040046601c0282c83e00584a03044030a440c6030b280031980c4c0050b00c101d03401c030002c12403000c1480310048083d010322040b902ca2005400e00d030800078151100041814401d03040410380081d21010404c1105083c0f1080c03c00e81c50710454180711a0000c800306103000d8001c01c14008001504000c0d6001600c181400c0b125000d000348181c00d441641c0c003a9841c02844850004400d00c4a880d01d4040c0c81e00c0540f0401c00407034554220801907081d1182004107043d001c0da4100341c000302d40740c24824168028010a002c8240710481d841d8150307030b072400d2032503410150800008100c490b80000e900c0000342448000540d5150b0401c5401030040404513032100d0382d145400703141d04805114040c1e482c1255401800d444001e01001d0340c00c9400081c03070f11726920b1113000032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 889492239 1250 889490989 889491037
    0xf0c070807182003151c11090708011203111e010c080718090e030c0312090f01090803070302090d170706051024050904090b011e0f050402 61
    0x2100c0c0d006080d40003071810007070320b0703420354030095500000d070115a42c404000385000c940c25210990394820440303245402941201c2c40421108540705030710440100e042ca0f002003d0018040c00b01c001d21005a41ca403c0c07039518440121003a640c20300800c1480390f84a0123210101c0e1250109804034044023040e180c10070480c04805c0034080148001c1c14072651240f8858000c07940104129030b01c01e90324100780b2881c00030384001e0b4410009602601e1811039891150542c20a010401d031044115410201d0b41e032030540f40007162002d4012a0b0054684c8144d04074800c40190602645084640c0403c0305400d5880b1410700758041e400a03c0501d80001c4200c4c00e10011440b011500e00400780d540b0320081e46c420090504000f0344400405452600c800c0090070001030300209580c20b103941d0b800500102d904070282c0103c4940c820182d106902038206560b0505000c01035010303604841030740e030404000d0050b032000c0b1803907131209200740c82000e03079403850421031403e01c0d030001e001901c255403d481c0e12115030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 889493489 1250 889492239 889492243
    0x714030313050f010b0a0915050612040c080c0906010804080706090606050a06020703080901031d16061214010510171302190b070602211303080a0b03030f0c0708 71
    0x215215440a80d040d11031070705018042c00410b80e8008884002e01c90000380b04045600310070a44245003a85541d840811403842c06e090800c000740c5030061032565074030b221201d000c454000c00e55094410074101d07180080c100d500020b41144c4100c020b88600c04540d158001900c1310080200250b4845804215080c0080c05070b02c81c6100c070b60300c10f401c005295414081400714000f04d41e0081c0301550700070b000a0020034280001d81d0910942441c01003007030190040700308541041506581000d00c58221a11410a8044c0d131540c1a5070050f5940c1e041510315081150955080c2c179510705400c0640c0c030060141d400d2100c61503038040c244d800c001c81c41d603100305206403403440e04507400459005500c540d07000b1450702500250b05038120070000f41ca081d00300500e424480c480c00c64003c2c4606d50001c2e41012070380c001d848a8a8112400021310468a052055001100180d40c0103c00041c10f07070300080d20b0704800f407042a050341b102400440c20001da0710041c2c20325a101d424050140c0c414210001820301c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 889494739 1250 889493489 889493491
    0xc1602040f0509010c0c0c031515080615061204060e1f1e0603081804090b0723030705041403070305160609080d080601050a0c020603010b0711030f1207140303 70
    0x214240c00152403070402035581c212845c80c00080d003004488404580403600c807804001c203481c2c100c2c075210b8070b00c2074000d1990020008110b40300a8419066400100090040349e0300381300c0c080c0c141c2900c4a8507400c1c1c00708540c0b0f104140c0c0d2030038034410711000b00d40812030941c0508100754403013048900700c0b88000c13822241d6200c9802400030484d01e074550542e01c0044210604623901107000144140303030a507940d10210b405010200d0b40d51b00f20035401d001741076485400c0349d0000b58200c10840d400341060080208582a45503031f4844810b4a1510000e4900b150001c0703e2003414036030b58103400c0c02d04000d1258083c06148880c2030780b5115160002c40800c209000400fa04e89400503140302c01442d0a0002e800c0101e281d00056198200c6901e2900b0039400041b4183d05c138000346055079413503060381021344800c01d0181029400040220001c01e900a4140003049140d0045d85242c0c0c0c1d070800704042582d03070f844032400c150031900300300c04101d00480b01c0c00240c064103218150400b00c1070882c3c4003852450300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 889495989 1250 889494739 889494761
    0x30213051b0f2106060a0c051c030506011b080a180305120a0f020616050d140c1b1612150c0215060d030c02060a0e030f0a0302060f0f0c160204 63
    0xf0392141581e0141144a8808281561510f00340c5003180000b080d6016102201e4140202c0124410410800b03000b03c0740000002d106001240c1001d00b0000d005010488045010403003641c1d04a1000701c5001440b0106540401060718050600f0400c0700e040601508541c00846582c602000003001400400032000384014140e4541c9041003000f8020349542100400f50340005090020b0b6014150b50075444d41041d007840781e9075a001840080050844044d4205090401c02c1801040000f01d00101504080b090b141110034401620301902c84400c9201c41c2c03130403000c0c1ea90800441003901100264075001e540d800f11103a003a500210f0980d01020507020050300030011082e160100411640e4100714141c0c0d080d04126002e9501a24805490b40007910401c80812a00c15180c41400e1a0700501d4000c0c05552171482c04100c1170703a030f07a40b00030004c90150003000c0c0082c10100307102e200d84d44165000c2903240150344511840500580c05003044c4425504059081d4000da00c960255000c40c42d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 889497239 1250 889495989 889496017
    0x7020307230d0f0302070501050c070b0702010e1003200f091c020307080c041d0303060103050907050a1e2106090312060605030405060f01050d140c120a0b0a0501030213051b 76
    0x5003c504c2d0007401c00102e030704058140141804284c200d0000010030340141c60f041d620099407080c290005a0b00c40745a2180c0c140c0c0242001c4400104a901d07400a004204821400034542251000c04070003d0050152401a444090054131703110700d0058886100075a140003003643c4249181c01003400c090180e0808041035000710032400940c1814460766081c0c0da12030040d40541e1a2601c201501d80c031001d041c0c0c0e4100358807070010901c190741c280206401004010000d1091564900c42c0c00c4489903118219600c0c0c00703543d4070029400700e5010000804412800c44645900d00640d036160052040460a504002d40c1c40d018070346a03001841044040c0c11035444a84d12864545003c0b4034241e001054070112440003401000f0a8603041420007401c1e0b4003e4140409208005071103141c10490410b444d400392150f030358003c3d10103021800e011000d02031010021266100090101607400a2200a41020224802d010503080c01c1e4041c3d40c00080c844035400d43c40750140c22002c80d5400c80c90b0065602 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 889498489 1250 889497239 889497263
    0x301060b1801030c09231210150312050f040f0b09040b01030915110f0d021207081603020304051c030e0c220e0703050102120609090307020307230d 65
    0x48089542070100e010000d00e02400008001200204840e009104e07000f01ca0305080300c5000c1d21840c045140c410300b100941400f02015108101940e10032103410411b485c2d51420b43c041c20008039a8400700c06507174100d804001d41d165004400caa42d84e100000001c51f009082c0400303d106002c808907880102403401085403142c0d240003c000c101c5421520a0381854907042842c0001150801c05203041c00e18140001801c5c8030300c00042c0114030462007051461100014410ba200c44c20303601134040d800417040041525641c1c4501911036804c00e446501c41c0301d9600301c6002c0054031030703001507600911038410b40c0c07089903050208a040030002005a80801c1d111143c000c2c10b10302c20406099086401c03507031104d0860843c50f4108203203070304026249034191296a5225080c400300700840003554084004c5503660844070306a51080d106980743c510410100d004075460160001c141c40c07610b500280540219494010820504e085008040d2020300e00340c03e04060b550b030348000c1d8140c2d40380a49103404038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 889499739 1250 889498489 889498507
    0xb0105010906020105090705090c0c07090606231c2a02010516080c0901030b0d08091507030e1011070e0f0702030c1c020a211d101b020301060b 63
    0x80c89800d82c008004680c580010000d5070000000d24104580c0e06640c3c02c0c0c2c280d2514240003000e4841c0d6a050a243d1160010015440c05903a00610441d008c650b01c0c0e541d9081c002114442d274508030206801410700611205079480b0302051480c41c0343c42008000152409007004054a803c41c0f895408020f00700c000d840c00a142e028024958803a4411100b0081c0406144016000500113010880780901c08500503e80364081e0f80003c000510041c000f54a4000d58900000030b540704094480c081c14014001d6010020218251021540c0c1605d0319008034105809010301c0c03c007008240e400300030000700307a0b0310740e140184000c0000d000c0c0402c01c642d01e0700e418181c800e50410064849003c5500c204030740312503401d000c90402c4405034011401401030078030345000c0f03141c45903941020700ba50741407070246828034102821543e024003094454030404c101d814050071044012840c40c3d500048403e15000c0051310803010400d85102035610301000a0035078000c2170864805800400c0c6c85040001e007614 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 889500989 1250 889499739 889499747
    0x120a02160327060c231c02190206180d061109040e0a02060307050a02160b04060807030903050d0b1c060b120f030406030b010c1a010f050402090303120408070b040b010501 75
    0x5090300705450144042d92070a9070041c0042d450f060050068021244502c0c50000303402c40f8804a50084c10455075007a11a20204030481c4000405002510403130170688011003110312a03910a40c0c0080c10b89042c58001e00d081320a261000c00c0150388841d00e480304d000001c840c0e116810f800780311012041e0700c0344009e40901003211041d03803180f004d550104400f000141d603120200c80d0310951500c1c1482d25a004040c06901d0030322210502c07062902201d102003640d0700703108090000c90760540e40768025920b6103074003502120a035030b1014000402c03c11844880d02e034560801c0c8080300b03019208210000490700121b24400b4040011140340340c88042914407407601e556480807850110025090840c00d5815990b0b4030700c120312840d41419110300104500e60f00952112480a40145252242c81c0044445c400f204100f40200c4801b45084540854103091610940e10810000b0380114944034602d81030b5014107400910486059900308422000a241646c441d8050351140c1152000355040100240c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 889502239 1250 889500989 889501037
    0x50a12090e0105060f0a181202010f05130512070801061805090f0a030c02150a030c110d05040b1e070506041a040b04020123120610050a05120a021603 66
    0x404a0312140300140b05030741e200c1d000c54013a107200c500210341d50052104151901c82c908034507402c0c7c41a88220000700c0b0f000c0c81c1440d510240c805d80e2422203452031800d040c0c84034001c00200510300d00c1060014402c3e400c2029040002c900420100c2d0032035a5103110301d1b4203446058024034403002031843c0302c500c001094050141c1254898003c1c000c00e10044101c03e541c0c640241001d4204000b8103403407415034940302ca0307201c440346130400e580d56141c081c0344000e0040c00000001d800007650041c420001920701103003003002c0d0401551201e10b45850450b040c101a01710384400a034450000c410103101c0200a001410070303a10400c042c1c00030386000d0030300440c0c03c1c00080103210060300c0714080100144a80100350340c01a42400d0510032405400703c0f403100880c0c41d00f001c02411800080038940340c804855510310429003210003003070813259507004039814041c949004010881c184020320600e50301e840115803103000401700604080040c0d02810b04a172000c4819400f0a000c200500c2005046010354 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 889503489 1250 889502239 889502249
    0x39031321050a060b0612040803060102071e0b0309010605030105011712090d140a1217090d020a1e0f0b011d10060f211b0f1b020409050a1209 62
    0xa90038040c2540c94158a49010680040019549071034002c895075600040e52070f020500310303111745e25291034074104007181e20544080d030141c802c0c00300025440701446162200c190441081c03910031460800c0c3c040e42c903080074060324100d5484540c0482c540c0c40905c143c500a140b5050915600c441107981541400643c80c2a501d10840c100302c14549626610102118181c3c0a21098107000d405c1113001c1c282034060800818500707001c040c43c01c48640c0000c071070140041040100d0071917100e0b0b000f83c41e40c4181000303003c0c0168100b10000004a6050314440e01d02c0306202c7c643c0c50071601507035111b4454040e5420100d4118928900500c82d0b95100c2c000c0d4441184070a0000c0c2c0c1504040ca4105c2410780305100310390400101c040c15111180c030400c08258071244101d1420780c1c0140d00c0788442c010b40000c4e1400032211010700e202c45401407284076200c40300c8615441300b001100412002c2e00300d05802020a076002919580c5c4400000c0c001c000b8110403a002d80e810403048107070444001e0060f04a07a01c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 889504739 1250 889503489 889503539
    0x1706160504051c0f0c240e100c0c0b030408070b0109090c09240b04051c0b01121a091f0209011e0c0506090a03030c0302390313 56
    0x203000646a03810190001c00c00d114803a0782c14940b030314080c4d01c400d0344201c0c001c00c5c00c0d02003c000141c4070005101c494124a07504182d403001000781c18201c0e4610200e41c0101e034001e0082c5428002030380655810000c1c54040c0000205660301c0307000000c1182d00c1501c04540c540300c000381c05c038188049035000502419480c90309100401841d224003c840445d8010541c446550303080c1c42050460f054401e02071481603d0311019880d607031b489124525005482818002c080803c4040c140e084000c01b000110b5601c40d151120507424103840c0c280d117144488084400001c401840811103403550811072040c2c0342d080c000c0ca400c656075004030342c0f85035454032200d41a5005010303008490703810820540c203942c800140c245a102410b841152602a11342002d005400340d6021b20032500800b14541d50214003036242848100b4511400b20101d00c243d410200c4c1001004012251844c070010016000082c1c0c941c1010003890300c001c0c05c1e401e5038440c05507500a288a003808111240120a52401d036258400c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 889505989 1250 889504739 889504747
    0xc020904050115060c0308131a25030605040b040b0a03150f020706020d060806010b0d050c041205100b0f0a0504020711091f05040c080105101101020a0806130608070b0d0617061605 79
    0x3030b460f50074521940c0c1c201c1320a1041800526032ba000701e40c19010180c0045407865008076980e034094020401809840c0c0a030f07003081081e40b8582010300607804514006003440c40f41c18a50345990f18500f2203107100c040680d44420540380c10388018000742c848207001e07200c01a40c0c2c13013208601ca000c880c1e40b9030103a4241c0e0411001000f0b0b444881301542c0c81c0180d1a24081401d80d200e01d51200300e840307150800413948407045000d50070300c84001404046031150400030490280414100010a55040b07005640003450000501179070800b41c003d482c00c0c030310a07104121160204400240069000c5600d50452210391914040102d428108080140400d880410902c491114018010b0205010303d9000704580704980400e40d2180c500507080f0100e500c001c5459a420100c0141052410369074184240c040618130b00c0c2e050032a10880040310541c1000301100e0380380040720242a0007c501401a83d6a60720300020484010702428000c0b01062000c5c07c181c0c54580400c00318114515161020082d041c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 889507239 1250 889505989 889505993
    0x902030114040f0507050a0c0203011b02150a050108100b0105090d2009060a05010c0f080304200f012312040b06030f15071803120c0203010c050a0c020904050115060c030813 76
    0x308030390030050b50f413230099400650b5002283c050080132603c0401076081c58800c0c46110b5003c61002654040c28004079402e8489000380c8040d03030000e0050201b20381015820b04032011640c1d119034041c00060401c0743c1041001000981200c3c0ea1610a48844103401108821506a07100000510000302c9620b16181070a90102e17030b0b0320440d23001d41414003500c12141410312080070b81020550754006000f0b560b078941482c000320044015582da00a2034101204541c8910713200b02c0300a8540c0301a502c1441d650300f00f0340316041d240540070221030400000c004012289802c01840c0e40701da030184609024905205080c5441c1c840c000d51169582d4201c035020480e2001c00ba6240b941204d00d84c80c0440525007211a0300388111000d41c40148140302c14818003040070f4001d6942c00340b145c0200c0c020010300f0903134007068820b8400c4040d00d00001e408001685d0040c5060381e4415001030145000280c903400c0020040095070750354000c1004145200040030805a014001a6000990005e90035000e4416 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 889508489 1250 889507239 889507247
    0x108090d0c0b270c1503131b0b04030602131d01060c150207050c090a050106050d0207060e16090e120f0c0f06150a08070621060902030114040f0507 65
    0x1d494002c04104a8101049002c03560304020240c040d5142890b803000c04804508035031302c0f144114558058440d14203020092004501920f00c9507021030101030b04442c0681d914a1009400301c0780015001103903a010803031501640140c0082c6210700c0006030744a00d89181400380c01100d0b48005840c81d44850100003107022101710504403002c0f07040a0b00252407a10701050a8800f14012a20712480850410140300d40041c110076035120079600030303185440d1000424180c0c4d0090240f580400c10030010034544c416154010b200040c001c00001800d000000d28190400d0740c0c000f910440e00030480d04c00d000c2c003401c9200f203055203101c00e0003c1c0810004040d40000a0181c8012200c80341c0001c55003507001c4005100140d072164000040d40c4041c0303014505804e240c06040784483c040d86042a020510480008a801c199042e40e00e44030650310b8085e001c0f4045c82900b00000034203645a03900014009140e00256010301103003c1581c000007218018402103e00202c031036500d0500304002e1011540e00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 889509739 1250 889508489 889508507
    0xb0102071203020102040b0d0506040e06090d110f011b090b0405220f060e07030c02031e0a05070c0b0405180621070f090203090d090806072019020108090d 68
    0x145100c061880c1c0031400d00f83c1c0280600d51112032000c0c800203410f120200c0d603038001846120100d0341007104c2101007504a40d01d040854540200d5031286c25540c802a004180c0d80522442e00001c840c0307907240c060302003801d5501d00b42c0f2988800e0840490812902c2c1c006800c003000d03144d6406e005007040c4c50100000d0701c4904c540302503240000c0b100e4840b2400540c582100c458901200d8003800700c0780d62041411030342d80e0b00f201e088ac00245041c62100b84644040202c403111108600070420726803e0704c444611a27480b450914040c04410400305000030a6442c0d010020b0504e54256921035161005100070002e0021940540071141c808110240c0e544502018010503184103401507070481444162070400c4a4100701c58090000c440005d00380c2c42c5800440c0b0509106050310401d40001400b5901050280565007094000c0c100150b2003d10070124916400d00b1540c00b803d400c40002000b5040032114407803482200c200103155420365030000980358002da00080107080703060f541c040080203664 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 889510989 1250 889509739 889509749
    0x1e2e0c05030d050c0f12010627030821010f450204050433050303030a09020d020d12080c040515072901090506031b0609010c1205120a0b010207 63
    0x3d40e40d80410f415032469000e465444a5003c280d40d42c480c2d0042452020300c0d024850400020041041c07900c5680c0b641120050316400e165071103801c20b0442c1c1e10000280c010f40c3c101114940008950845850001410340c001d0002c054030000c80c504101c007d04c829a1503148801c40c0354002c54505c0413007040c6408400207400b2002c90140501032502c0e0344006482107074025940f09060000c109481180d640c0d1340700840f00031081c6950701041c0080b011010b07902920640b540b50b00300303100140640107282c0203c0c0015100400c0d25024800c90340c0010120032002a003138a841d40c04200d607195042c1c02c80250b030b030003000905042d07007000c2c07078440050029580711981455180d004980c400400209003000707a04a416159500343d40c0304080780f11751064900748900400c060038080491907604000c240003441801d0214901c54044490080c08601c0d0f006c1e1071072604210303803d003184000c16034101c500d0a0151080d561540e80c0d031030b107155420505501a00198905141001440d9580e8001890340c080320 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 889512239 1250 889510989 889510991
    0x280906020d05250506090706090f0602150c0d020409291f18080609120403080304030806030a0c08032a060610090b0d060501111501051e2e0c05030d 65
    0x15542000525510f590b0600180030b48129414003c511501059060035514150707500c03081030f03503517252050085285210700300141e0000030700126080c1300e011442e54071001da5490b141c86c02d903543c1444e00c2282d00c81d5200c0c8505a6450142038000c00801080c02000e40002c140b40710b902c41807400180c00c4d400c0a4102c042a05020f8240504150090402000c50046036102140301584e442e0196180c80003111100168002c100d00b078105c5500340825101641d0b004030540781565a559015501c2045c0a010290b0601c280f003c0000010004200640078165520140d601c8814661804164103400b80101d80b10904458504034190f90004a0590200040381e50000022100006440740d92154018585415000400d4074512003150000d84c100c440a0381ca520701d0741410f0b91100c0c0c0392000c54101300d6840074102e00410680c5010041d444072644c1c800d6100482941c440001581d88000c0f0000c025990f0f520603c074106100c0381011142c0100305400c3c884402221680c03070544a01c00c6a01881c901 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 889513489 1250 889512239 889512277
    0x19060617060a051b04091428020a1106130b010b09031c05070507030503070203060a1b0f09080102070b0402040b0409030f080907030212061501050f070314280906020d05 74
    0x13005503810401c4101c206480001d50700c0781c0b00c2a400010305001501210300040800102d46941040588081411f0781011072548510700c02101c24007a5021652803c1000f42000c0300b20a0100c00b44025070003103940c2c40d03041444042e6880c00382d9600d80160320045000c4070030f2040307a449481c0451b046242e4200490791801c4c0100ea01c00c195a2401800c101501c244140500402004400001444d071107000310f0440758965038065000055420703440f40c944403402603501540c200c500a282a40f10031069041c00034070191640300755070898002c0c21043ea6142a02d2003400b040d030509214424034154152401e0010210a460140001c000e4001c1d00c800c006d01d150001e20301e9442801a00041c540c000c040180a401c0f2094690b070383c40e829259621100080c8502c0c0900b98010401ca4031420450140242010340f00e40b0151101120070548007031800017009a48991100094400350744d450f88251440740c4d03001540014258034040c1c01103410b560083c40301c9202190080c2c140c03070180010803421205 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 889514739 1250 889513489 889513501
    0xa090911040306050103200d030c030e01120f02040302040e0309060a120e01050f0405010b01030e0709090302010e0a24050f0609130f06020a030b1804030e011119060617060a05 77
    0x214071a5a0014061515090000c801c001c5000c41030b281d00549510b00c419110705100800140300e102c07079001004030b0b0031010560b000a014000401c0d107103105041c507010819641c0602400c0c0d5902c0b07c61441100c0d07000a05004501d86403003041e030107010741c030011341c1854001808224103206401c1c00d0401d00441039207400b500801071f001522000c080000900242c1491860020707010000d40b800c0361554203250f400a1654460320440c4a03c0001c1c00007080802c1c50400c00d40018038140805504554940003101c03181e060402412400d9841400c8414800751601c2c0c04240680074115000002070600701405188003405035941d0300100101c0d0421078540344d102d080207000c0302c950001002c0136000c105c10010310886502812100f50203032014410410032200708916444050350f45c2d011070280c1c0d00441c001c24072440000c01c02c2481810700c1d4500761120300d0b04030318000da00c540c08801284070025803000c11042d4000d50008100050030104a8031642d509561141c800901c0c0002455072000000c107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 889515989 1250 889514739 889514771
    0x1a01140708090913060615030b0f0a0933030b0106082e03021009090f061206181704180c020a26180306090d051806070b070f02120a0909 60
    0x1003c1d0311440030481c6555510740c43c131010070907c0e60714003ca450144000b406081c440106808484020b05901e2094200151400202a8401c4160301400d00e026600c1641810125036400700c0e2006101c01c0c02c1528500d020320001d0700c143c00c904100b040320024000c27034100d04860a44001a18450068500d4111896072003616040d440031758800c0038800c0c620a030030f41200d1003400b900c2c050041884110700050b900c0d0161291842041c2c50408421007401c04100c1c103600035030781a0301d5100010300791940f41d212100201201405a540d2500000381006042d8248002c0d55035590841c2e824041d0310050140a920ba01d002c8c200640825a000003522041c0c0c0210126401c3c1c0000f1203040c0c7d1201c0e201040800c2900c003100b51107000340b1421010842901000558208a8203a07950b8a0b04d800f1a01219000c8001c80c031310420340166003404403000043c0080031040c03140440c0c0d500c0090402c00020000e00e800c1c014490200d0078802003000b14450740d8407030346010a44031000c0c40801e003000347d40c5102d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 889517239 1250 889515989 889516021
    0x6050415150f140417010b040209030c061b2b0305060f130f0204230d1e050f0a0f061503031e021c0f0f030614010305191a011407080909 60
    0x180fa030078002a0109140e410466030350a0503080400803c0740d49880c00c20301c4200d10480003156030540c40041d8030345442c0f41100040c0000035003105911140c07e0004032107403803c0e05d1461008080749200986044480074000040480c24241c582403225040800104040012828400d030040111004001c1c010006400420790562000710455840c0d5507003004041034030380081c0c03118050302065140c0b40d031840c003154410b1003c0d800802d20424841c2e9290342100c17042c100c00044030580204280c3e8860a00b007445103225041c096080c3c2c00200415151207012101c0b0704104034500001071a0500c0030a5110224244c14003035558035082d048ea6050013646803001503460b4a05202c060510103000e07d07413002034040c089860fa212600c44850000e0b00760180d41d5103015445424410150803e50703903220341c0019030005521030505207070601c0c3c0f65214050f503400031000d6000a444810a420959102148440c41d0810990306030030503045650f02c1c02c40c6d2003905032080c810344889000c2a034840140c5e540c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 889518489 1250 889517239 889517267
    0x1407150b0d0b150126060d05070b03040308100e04050c1201061a0406030b03030705250512070e09010e071511031206011805090a05070504170106050415150f 69
    0x2485626108020000c2e4514050107580021500044004d00d00700c04c40760011030b48600c0388400080e86e584402e1105100203e5415900391080500c0001e25042050080d03000d036000f6500d40030146000544128843c44917845078450080e10000c02000c61004100c1410340b01c1e007140e800302d010a0045d03855025103000c1e0450029103480c00300c1410003407400d80091080303071641d0300c00303201d000c545408140e164080c550007c0e01310381003108400341c0b00c1c40080c046241800c1c0d01c840560000e8441011504544504d10801181c0c1e0100d8070500451058080c640e0384007030103c009010b119500f00c0c40940b0765078280300300310031289100003041072940a12030300d14080c2e540b141200c3e191100c20740040b0380944251601408039008030154002d0199a13600c0005444c8040d04c10304060315010104e000034000144224100042800040740c09000b81d400810303090000800812080c1c10201000102c1e1022007001d82c1006180c90300f009140ea40c01d5000592807024280031700911240322060b100150342e4201 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 889519739 1250 889518489 889518503
    0x80408070603050906060d0b0703050c13080f0615010525471503100c090302030118021f11060a0e1e1c110102191407150b0d 55
    0x80401c5440c1c0c035610007840760038220204e441d0b9494150601c41e0101c2050405081c40e41c0240006110b24003d8000680100c0f00e11803a40c0b801c11885800c100403043e54001023181e40146100d11a401d05c100302450708450542c070301d8035071100f070303c0c001034030502c581c40050144424503c0d6407a5500004007031070707a0701382d00a000502da4074111104201c0c9008181c484525006000a0701c070500342c5422011004080d00700401d05854442c84d0000c15200301007402964144a000282c00c0c60007014003415131440d100341c480c4501c103400c500c100b50940d540c0740740f24040b03007685682000140e56882641d02c070401070700c5124010010410411111312140880242542c0300d0302050000701d4289510400304003024a0a030340044205648001c482c580040c00750050342c0c40918100c1c14442030194900c900c41e280d0401c0d2007299580004542642c04c0150b0070301c0068186840400e4a603002081da4262600e01d210031464064583c0d40c5241043d0300c1020400307000e03640c500e11181515548851480d250300842 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 889520989 1250 889519739 889519753
    0xc020a0f0b070c080c01050313020d021315050f130b012d0314130b10050a030c060e120a03051602030f0f0f191401110414040c08040302030a0c080408 66
    0x181e44205a02440d8211084540030380000782078000441c411040d00016502d55107140c8461400c01107601e001c1405a0f80907a0b01c82d83d10006940351f0500d28030500d8903000120740b12050481c0d032121040683e01142c000c0d613400440034103545d00e6039030070a41e44035170210000300800000e004031004080708403103801c400245800380da080440b1112801032019103030350030b021114029038081e82582041e1501d4110702c0c0f06602c1c18000a0074440107a50141c5003d06680444d613940c0005550911036a00507074900c05462824030038180c0c4100d80c0600301e02c0c107640310640040e12900d459070300c408944000e003c02002282443c44148100d100440d0f01d50010f045404800e51520140c0e1154160386040a040c032032000c0c82210010045030084030300c0054510b03030100040e652221980c040c10150240da055581d44030705441c9400000c0580060652280d1240300040c102060108880c50980c0754000e1107034000c10000000e17800000c41d166492180b809201e03030401480c01061074051034000e0076050182d88 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 889522239 1250 889520989 889520999
    0xb09070806090c0a0906292506140f160201060f06050307020d030608120c0f07150e180115020c04020d09030306120b0412020721050615100c020a0f 65
    0xf0030b4030000100329100900650ba410881046034110720407120701c00300301c040e0321207001c0700354100c1060121944a07041c580b02c881c0300840b054150424035009850807148106050201c0ca22889000c881109500c3ca00307401e00703d40300e101540004000c42c403036503200810006078034800e4000030014019000b00003055034a416010740b03142c0040f42c076400140f28141d5050071141c400e02910301101c1c6e20501801e201120708000c840298000200e00c0d00c5c51181004181e03c03030000704180c000406403041a69801009079000411a0390040d401c3c1d8800c044080154024409001e1010704480d088c500103038030b503104040d050341800009003140d6032140c0301041d1448440055001300c56001c3c8203580802002d0384403140e8800f654100c0381d01801d03030140354000400040e04a049840107418900460b554a69114003034012006680300140490b00b142985108010301000000e07003114a514812106407a00f01c0400c8130445181c03180c50030403401d43d007088195224000e22402a003a01540380c00da050b00c903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 889523489 1250 889522239 889522243
    0x1c050a12030207030f030c050f13240206070c0c0e0402310b010219020405060105070b13020906011d3303090c0109080601050906060408060a05161107030b0907080609 73
    0x46030082d0003285c8207070484080188a4400c01000f2070260716000c1c00c0c00c28061070302d801d80c0c20466100ba100003000d003002c034034006080b6082d40004085000c80044003d04a4000d00b01724001c1d18090603c44411400c3e00028440c803a90030a0703809042205849940700d000040c0312840c142c2441000b40c0c02e1200181d2840081c540e40e4100e5040c110301800301d148a10f004a07a03c2c15040c044141c510980b81c5004010300d0107800560304540c05141050618040f5182c46008590030341d1507840c103910840a00b011403c14040403035103c5400d00b0302c2a15291461103111894602086c01c030700c01c2c45d041080070805600360812007101006610006070100c010400324017590720aa40b064150310a003a5080101d40c45445110b040d2a500e101038003050744ac0c0024802001d401400742c1d0741c448410b000200b01c09804004440c0309040030b4001140300c1c1842200203068140c4052407000304440c10503480403803031002402208495111509898a07075034403660030b0910045400080b4580501c0040c05000b10700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 889524739 1250 889523489 889523497
    0xc0b0a0b011b080d1a130218010806130504021c0501060f12171c022a010e07030308180f0604031d010c030302180616140703021c050a120302 62
    0x802c1c0c854a07101c6205100c8441e2039108030304002c00c150f40c200b0006440380819003000a100101c0600d02030300e40502070010741c54002140c000c0d40015400700d0440b80354540d8030103000c2a00020300784441c00e820440c1c0030038007a813071610b140140c0301d4645010a044cd1940340d50060040c4a0011840c0035010072710f0018040c0c0568411030004003900200416a00c000901e0841031a5010101104480e070b8500700c6074443d08811f42c1c0b4000c1d84114919a6100356041c0018845101c0030010001d1156241043c04100005000d140040d685029200d202c0d00c2000107102003501c3d010304111501d0303503881418040c504207510034a0103a019001d5441d0b034804000a4107400303107120b611580395840e104418004103603800360150b400245240600000f0078040d5008040844540759148151810000450425400b02d0405548200f044680e4010302040e0883c090b00e1500c0c103400307041c1480c40c5030001030b0381140c03188403a8288090740f4001c004014042100000c801d03805140621001a4181e0150003904 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 889525989 1250 889524739 889524761
    0x70b130b011d0c0a0206010e15100e0405070201290f040f05063609100606091d06090601030b06040819021e030a06020a0909060803040915030c030f030c0b0a 69
    0x30026012407080f20140e400d840404441d540240056031901e020300c0300030040076021085200b90303a1101013940d1160915034019103081d445040501d00204140812100000c0944086924000c00120340c45076010414030304a07122401d202c4042c0a81000507840882c0d40e4405d03503c10318080c070065131001c0a401091044c081180c0403003c6c820300d80780c100d02c002c4010070300d4042000f84086034596074010800341a0042840b2085510150004003500100e50b010b40202000c00c0052604000a000110078580b4005128840014905003203002c284800406006c02d030500d0340740c180051940c2c032200c041d1401010300a04440359110ba004007840d84600c0c4010a81c01038490004404c1c85c034900035511810003a014000b0711080401e41c0b101c90094000100c0c8008000d43e102c000581503c1c680640d00181031101d020356529490114908100c0301083c100014000c2404400c02c0030032007480303a5004490700030a00c0082401281b42c106c906994280c402011026085c0a02c011281140d21040c5011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 889527239 1250 889525989 889526039
    0x140d03050a020c06070b09061b031902210f070203040803091e101706060301032324090f0708120c0102040b040311030706140d020c0a05030c0616050906070b130b01 72
    0x1d09d41c128082180c8c06846501a01038804002007880450444e003100d10394040b803100103040205a01240c02d24a0380015080c01c156500e1060050201c00000660340089d860700040d40781ca490002c0242d164000ca00c00f0700d1151041000310403d4100c5030040b1088002c0040c403905e0700c070000380405028049152011080040b281000035541e0800004580c181d0340c001201510303103048020a9621042e190074401003034028880500c03170780c081140c102200c045004034000c0540c50020f6000307240031484802c20045510105040182c0c04010a44404401540c034509503914051030750a4003910807039103c0101c0d01400980041802454450410040780441c1501d0752555184e0040b10711202d0165900c2c0c0311a400c00084041c200c00d40e0060220306d520714156040c41c5c0d40764032028216040003402510340d411440030051140303210119540c4118290138014100a26540480c00038066041d005114070414408102c4807440c40112019040c0d020008d100150384610340c88444038001e00e0310340106 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 889528489 1250 889527239 889527241
    0x8071d0f27070e030a03080f04060e030313030e03010207020907110a0507060509040c0f08270d03090311010c0207061d09151503041e15050f10140d03050a020c06070b0906 75
    0x80e107004074000f844186c051303440302240c1e01c0390401d0010501000c0c1040321255981c00428509036002c0c400f0354800c0c074a41841138102c194506010b006030501118640c031907441002810016504d01603850f400480501d002d4400318201c6018500e014003001024155110f049c10001d80e07503500c00c0c02848514801d0741d041c1f01c502041d01068400c900b1120781d10000c1140a80050116a1440819580410301e003100b9000d08441c0e011a07420500c10301020070010740c030303185040141a00300238610802046a4000c0140e2103a00314000d4840b1040e010780c80410441d1055825183c44c1e4030700780d10403440003d00301c60b024141000d030007848880c2d89003500d01070310307140901d80d003400c11602c1502d104070341000e02a940d10b00c001c86000d034074028a90b4100c54450324440307030700310110715032040c40c0c41003c0402c1d00000d1810410180b4281511592050000e03136a00d0503000c40988270b500c1420a0160305040c65070702ca40d880d80050b41802e168240c0d19070080300c0802c41d14240000e00c100c0e103000d50300480c140c40702 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 889529739 1250 889528489 889528517
    0x1005180c1b0f2811040b0105040e01031b0821030618160306080c03031602040612240e190c050613030b0f01050d1202011d010c08071d0f2707 62
    0x43c1040202400e80341d0f501c110341003039003810341140c0301504052405d40e180c142c5985c18a010b156080c2c10903910040a4039204860204200104000e410180300070080490039000259076882039030240d40c007084000c4003081c00c645803183c0a07a528800c5044181d240c0c903007039131152901750055030300400283c01c0010000780c0c0744001c50140320215025002d10318004038101841c82001c19a54220707080341d52007200251200200400d0100c441c411a21a2900010350b9200c1400b540b903100e040303500520b8242c0040401d10700007907561404658021300a9003007a2401c15240103410340c1d016540100002861100d03503240a40441305a03403207841146c405441d12151030109205c01d002d00c5400402e5404910041258914540280c926500c000314040840c0c03034a0301305149200011003c207179141e910741c15080750007044540d4028031515114410015105010b9040d1455283c80ba02800d40042420910b48528907513140070180e8070180280729841090b17424521900702e4104000400d00303022900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 889530989 1250 889529739 889529803
    0xc060f060a050d170f0415030b1009032003033009060106050c1c0e0102011a0a18141e010b0c0a0602030702030d090302061005180c1b0f 60
    0xc203590000d0b14454030700b4965035550030342076018a40f400703001c4c005005140d09600104002d0001c0c00303514810504070000050003400b560034920f40703070b840303072914030280c014044d4400c4034102181d802c010300303a0f200c074603514916506004039202075405000c00250951515001360a8600102e107208800d03c601d188104641020001650022050b400010042011600c113001a01c0620103400584c1c8182c0075203124011074030035082041d004103196003446511582c080c8105c4001d91141d404c0352491070780060000b0810b030b0390390007660041c001d84010b004d5241c181e548840c10501e0000803850740303424982c141c20b5529a001c1400c030728070840300d80003191462200e019140c00e000c0440090040400607581c00b4040d41008104030110300c01404150f09107500c1e401521320fa2402030300030b41a60f007407210612030b000ca401e030042c5c0d0084003003c0c2020039120b4000e02141c0d000001c000215280d242c541c0c411140e50f882d502d00583c444c824001d06600c03c00001c5280700306048a0001004a060349505030f02d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 889532239 1250 889530989 889531009
    0x11407050a2a12060905100c120e03031006031802031204170f0607030c0c120c0b07050c071a22180b01120522060b1c0807030c0201090504020c060f06 66
    0x400303c509101003e400064584d08400005480780094400304001002504221014140040001850441c0100041a69106070003982032403501540c9145000c4000303d00400651081c0410141e480f082c0034050141c0c0c400d03040080d58014140c801030031001c0c0c081222a0001d00074518000194021010342c200001605408040901d02800050750783c10015002031070103104c103e00b40000c080b10040000c800f0a140001024152942c1d0340500c00b50500c200710807070051600c014400c080128414001c03000508604441c1610000b9403034803402c0c00c00701814010310b89070148a05041c0301c0040304400529406060f244910703006d01900490140c848251910760781c44502054220902d00a0700e0341d41d810965100c004860528140075450240310301e0107800c1c6205441d5980d40700c040409610f0260b0300d0780030f416030704080c5410320601e0ba201c00d03170244207002d001400d000c80000010216400342046000401d0300410441d2030f51140782c41c00c0d032642c0381141c0410a404201002030001d140c85030341a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 889533489 1250 889532239 889532249
    0x3150406061205061f0507060f0507051b010e0a0503041505070308130c081914031e03100503011104052404050d060e0a030c0b0903030103030806011407050a2a 70
    0x180e2451050300b990700802001c0c000d42d800065100c0505a80c0003084408044203040307581e03007175840515080410445a0b008042040b80b41860306103c01e0301e9103d0103940301c2c485141d800f11545490460b02c0780c010524104000034600074181c03854180310300440078008540071034181004090441b8401c40b964440c100008011030544008201c902800d45200d407081d42c82012101c402c1d0307440e07404c0c4030700d0014044903480380c1c20074800070141003110003400c99400400c1c20004504200b1030394130440760742e07510072130754001041c003c000a03400340300c40c180e004001c1001074000c02070b4590250300d0340c5056015003e500d002d0782c0c0c05884120a06144a00109a10b024440d89401d1a0509082100f11600401c05581443d255145521413900a00880039100c1c800d440324510358003140b4041c0c242440c010310300f41042d0414001000465080341d807440d0301c06400d00e07001c443d090010500d8407103070042c028054184d00c01e00b48450200700c41503034070b6403441000303250b4641c8009122140403684501343c013035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 889534739 1250 889533489 889533497
    0x3021003060b0703111f0f0b063408040b07030905100e0103151703070b1f1e030b07020c010305101211040908070809090c071212020415050315040606 66
    0x10002084c403800040700140c9500080d1105c2e0502914035007200d1090900c80d60a040e40c0707c410f03982012140c440d031325040805446043c10822100c1c3c0b4040c0f04859213408440c0d14081e1120340914500c40c0b10b140c0112548400442e03121511030268021a03080350300d088000c43d2440c0d501040d070b071401c01e503461050103c0e90303540d62201076003c2c011006851030400c0040380411600010900b45144201c2ea41d5020210005544810f514141142409809400182650500c600d0000310440020046064440109e04280d00f11404d256941e4011045c0d0f1000d400b80c041030051100c0554003141d0409841400d03603040c00300e62590001c0c0711704d1642510072041e000040400020000740355210900e041c0d00010000944000261a14102a4003400c4120b80c0f9800001c0d00344c0c524a410784ea260341041040007a54180303002e56950030001c4204408500c05e02c452500300340c4111580b1380444000d401e0a6601045a2900040c05070080c0c2045e10900700c01e4a09208a82690500784500d00440e0140e5039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 889535989 1250 889534739 889534747
    0x11b08091002010e250b040e1303200f0c0a05180907080d080906070c150506041104090b13020a090b0a05040b03010e060f030606031b0303041e03021003060b 69
    0x104001144101d400c0c81c0056549400b10042e1134001480841c82c00f640c1550198040c04040780005102e50b45170300010b55151040c441071103040380e0404c0e00c6511070820012660459140d0409079800c408400c0c111441042180c0007030b40241c40415140da51000700c00440d000b5030b0b40441040f01515842c011f4030f412982e44405128030b0311540103c01c1d042810a016543e07956190141d031410180042c004501080110041c01026030007045001e5020900f46098108000d5966541c417544c8049503203040310340d85500200e5410790b101d40c030613070710104900700056807941d443c500340020f0410f80400e50b105140100a640084009000f21403c420481da2034070040b030309281110819402047d000e0742001000e0001050b440380b02801140a0032280001040740d00d490300410117103090580443e8001c0c0c01034400d0000c6030701c0c0000d28440d003014804102007070315011000319195000303c0e44080d405040000041008c1000c140b002002e980c000d0314845141e07405040f003075003500d00c80c0c803131401d607082e00700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 889537239 1250 889535989 889536007
    0x8030604020a1103030903030702190309031217010e0a0c1b03030c14030c0d0c020114010b031302090a05070f0c031409040f02030a06080f0c03060a110c0318011b08 72
    0x68010b28401800d0f0a1420f42000300c0c4410510b1a0001c403102600780d0710001c00d0100b40d94041184c100b0605881c00e600d01c010440c0e540040c9003845034880188143e09011a42e00003e018249040e83c00e04882c00c914415a901e590200a900c415500070082500d028001c00419205401035000c0c50601d00c0c0701c0341c0940781690700714010302e01520142d0400150f0403011014070024401036025034481000c8a8032041200c24100846c0c403500040802d580c907081454032a0103641300c016044984030702c0402d45950341d400100c000f03003c040f08020b40c400201c2041101030800303544002d0007501c01c1da4132072030314424048040e5610000d941d0b020b030100343c8541022841062490003040c0450b070140000c503034079500c0d00c582d1081c5c0e0401d681d000b00b0281c8a22040c0302c0003030100131881741c807154800144000d10006000c45d1f00c0c0c2002410900c80c0c507031661080c4203d2202442240d08000c41001201d9a4954488422411044041c4080d00003400403400800d500c1b162601910b5154222050394130b0004a5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 889538489 1250 889537239 889537241
    0x804050d020f2101061502150907050d050709230406091a0f0609060406061209050c102604110f0d060c050406030f0e1e0a0204060303200a08030604 65
    0x8100c2e0300c407122480c900800d4940d00035120892408601112840c2c0c162980035080d56425000000c00110340412180c2d1039900203a0f1000e10720081520020b10b0311403054250038040150002c1d0f030071045074124074041010003c0c90104407a503000c81044801120801060f12044514500f009030551001150205040c1e13030001213128403401c81c0503402c40c0c40243c90b00e155001110302000580100f4100031050400880c400d50115003100c1c1007004070b0078200080e0254001004400d1095034482c040030400500f088079a454101c001c2101e0020394203108006d28030094541e0302c420204004200c89448107a0645841c0615071006100c03c843e03840d10b092010503c02c16a405a0210010a00c00c0105900f40715541601c00a90b4a80e50380f0b90911001809031512040f01910b00740c9004007044080c14040380f0382014601c1c00600000d44101b42403200c0c81c00305a085c0195229203840380c00404c00d90031100d160304100b44003100c0c0e0300c40c095299940d500c41d04020740182c0700d0501000010501e06e41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 889539739 1250 889538489 889538509
    0x301030521071b080c0f060307210609021314060a030b0120010f0c0525080d0f0b0f030307020d2a12140f0a0312020405060d090b0112080405 62
    0x51480950b00303050064446294000344680200b18120b1058001d022404044c0000c030207082c41518100d640c404140007082103032000500440401101601401080c03001c0d2030a20105c0f8640102400b0f5961102d000c00002d500a220086010405d054000b83caa2940c8102c07281c0c000e4000c00490130003005c410700340c001c1d051580a160410a8000e000d400e5000c0da00f044090100b070071000002d5150b105842a021104404102024400d041c40f03400444211000c901c050700e0708035100c042c0d10800c180b828400754000c0e40011903030141044862541c21203280c2c80007581030000c413100c06909002105260300c0b886000c00185d0865549146403010039107901024900c01310142004400c1100303101c10313002c0300a441d00120f0b510703480044050288440003061480703903a0804041d04000c04500c2c0c8283d600c00d9402d6001f000d1041502d144194800c450f41503034000c1030064896a52600c0d0310080400408483c501202c00303a1140001140704107145000103a400e6000c503043c1d24041c240f400300144544 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 889540989 1250 889539739 889539793
    0x60506060712020105010603200f0a050f030103061a181f080a0302030319020f0307120f110a1707210b030102071b06030507120b120d09061403010305 66
    0x11080040d5000a01c032072003154000840b075400041c07a5410603500505440c81007101702c150345080a00d041c842a0001d08a62954070003158007030384c9002c0058162040d004503000223042d0480840008184481070304a4100140d0030510f20141d50740301010042e010f0f00141200c1c00b41e0100a000400c1d070092000d031801443c1d01c0210459503d5640e004003413900c20052002c030010b07003000c02030092104131a00ca036001c0401128007941848000b040c14031540c04024803d408221001546003a141c03110741c032840c080c0041078400e0203a11213a140f55401036201c0403a4000140444c90750003904000103807100e02888060381e83c0c01120b0a0003070140707a903050140a40c282d65588100e8a8080e61b024401041624802e01100d82001401808000003840503800300302414240030421440c960b1011000d540081c0d0311000040300141440813900d8403042c035400e190103201d800400c0c09981d42007401070040350250360340d403020015005e504e0007040c0428030004241d58007052142d03104101c1c220030248851 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 889542239 1250 889540989 889540999
    0x305160c0c05062d07080322051c0e0102010e2509020c1606020312040303050414010c080612160b0c2b0e03031606110c1c020f060c07060506 62
    0x140c4070000101d403580001c1c0300c07200008108428001c901051302c807403603070200914241401c1c0101d54030780f850030307100c000c114044118505810b000c0c03140615030b40460150304036046520240c41c0b40100240fa450003244c1034080740301c03004c0000c07040d0720500448010085a0002c1c03c40c8445241c81c0380c5a0602ca8161501030580c40300c2c0104101007644041c1003456003032801006010101500340c14140c086411410441d00308010210102c1040044941c200d94146000a80daa0719801c2a103101d94100c01502104c2d42003618203120035a010500b18050f00003224132084401c40320943e103a07507088003032001c103004030141c40400400c0e1b1080d000d0820a440722041e0740d4842805468060b0a0b410301100081490b03c00000e40007096200d00d00740c41c840c400364021032406203450240c0304009086e410083c8143d0712044101c039000b101e04182c501500c59041110070340b60001c191203143c140c4040e00c03e0010b01c01c1c0300c8400c0e0100c5c40081c090b800b07000301034a003602e000700e01d858110140400078400c075081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 889543489 1250 889542239 889542263
    0x10e06070f021c0230070602060c0304230705090a0606080408130302091f063002091c060b0a0509040b060a05131d030903031b10050c04090b010305160c 67
    0x150300c030900381e5440e02400f500d004804aa07031505c660303505588501e68030380300d0388509410301120360002000b64106021008c990345039955890220a144d0b1b5840100054103807842610042c40400201c0303009a400c2100c6880f4941c2d01e0600c41c03803c4440c244191000500401c0108000c40e480d42c00410034004150700c2c1d100069140c1e0040340b00d040060310b0414442241045c003948080c03100b4070041c0038010505d0403080c4280404101482c860904040341d415048081c0388103100d610581c12100c0000340074280442035031181020900384c0005100a55180e810001d00c1c58880c0791981040d425964010481c00268445172200c002c104c40c024402504003081020118882d070340c044041c00c43c51384c40040030412480900b90781d14030340204c411704881c1303510920020550303540210584000c440f038080100d000546480a03a0301c1c0c10304400603800700c01d1400c014009281d4540300200203a5840340c00c103000044050300114101c8900f254440303000c0c5c0944964141e03080c80b66010401e01e5020300e21100c04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 889544739 1250 889543489 889543493
    0xc0a0206030c120c0a0201050c130e131203020901180b04064b020a0530040303020106030b0c0301180b01020f1b0a14030706052b0902010e06070f021c 66
    0x11000f416503040d200c1c0b80003c6120140c5036424001d49501a0740010240c0c1882c0c3c0c003810b800c02c2a001400340b1411180b00100081c0078040710300d04802d90540045520b2a009603095000d0300039400012001d00141c0003002e100a072264240f100001c0b1001a84054038051501d0011254010503400f241210040303041041070300b4501a802074420703007264001c2003021120b0041040c801840030b0200007503400002c4040b010440101d000300600690424100c0541503032640740175203500800c1074581c2c0d0000171802009059055005c0c0d01503900c11042001d02d5150489640c1950009100320b0007540111898101c000305075406c03814030414103004807000621207044040c108100c0c203294104803180c000300040c00345081d156400041c080c403840c7c00c400001c04000b01303498581e14010790341031081c0011007410403103508508c0300b0340d061741c2d1100c000140800038403000509140a0700b40d000601e807010640643c84c0400485070090b0740f01d00c0000400545a0902054240e140b000220b00132a8141c0742c80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 889545989 1250 889544739 889544767
    0xc050a050105010f090f0c0207090f06081e01110c0a1205120403030e060a0204050607060209150726190c08090a0f080601120305070618020a030501020c01060b0c0a0206030c 76
    0x8080d00500c1001d00b280c0d03040c190300004481c8886c52089804d410004a12296500840c110059980c000c0d0f010a00524841c880d02c00b40003194031501cbc0c94454607041c040e8440043c1c0c09014036612441c020f11014070b12030354400450141c450032a40a401410508001500c0950210802290383c2811703801d010340049642d550300000c440580100380c4400e443c014208050111a5000c80550011802c1c942004040341302401341107c0107041701da0000d1114415620000e24510074070b244030302d0725980c5410389412140b00c40c0c000e25843c90044030250000000800780280c0341924404810100c034994406c000f1120000040300a40d5220790070001d1040340d490704605040581908807814032105c0c07a1170000c07803404030164010f9542074080140f40740065401000c50f4145c0c5c1e004035012510103003c0707001c8010311003002c5000b98451140200002000019006011214104402000019501e600b0000ca52042e000b4030903150300700b05440001032034640080c4d900140481c002c2810f12111003840b003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 889547239 1250 889545989 889545991
    0x70210050c0702010e041a06090a080706020f210a0f030b100f1d15030405030405060d1406090f2802040608100b091c050c100806010e1207060c050a050105 68
    0x41c01d1004000750900030f550300000c0142000c0000c3c1c0f010071a00c1c42c1c03100c1d40c4400120703000d1464031405c0d0004420300243d6490030000d0280884100f03840829503900700103991528440c80e18aa50701074145070b040110941e00f605040c540701c1021151070017041000407070380f044c106845c00040c541d0f070b01058a900e403940841140507110a4548803101092500040c01095404440001c1000090070016003030700d480641802c0c0c402002e50311034403510340d031400500718011500100e401020129110004900300d0700302c0f030701d0f84805503004140f680350b00341844001c500c21200020050cc00d00c2c0450310000e05200c8455001c0103010310b440c144400462007000f640d01a5002c80d0014420304180f0125800789038080e8000c142e5450b8480c0307001c06101c0400d000c7c81c862a401500d9030602c4c0e4041d020310505201202c959a0010326562124088a1001d0014241910151b00142142240490a091080401c2001201c0a0080008078584142110701d681c0d00720701103805000e9401d612000907006d000312 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 889548489 1250 889547239 889547251
    0x30803060906031c0f02160f03300504031103011b0e0d0f150c0912060c030207060504052b02100c0903050d030e06240d03140408010f05090609060c0307021005 70
    0xa9001700c1c1e81c07102c001d1074002c0e90761100200c03000d0143c04010446201c2c50540c12039500c4040c51425804955900310b004041c1c160306440307013024145803001142d11a004005030391241e140591070320f0180302410300300d07400b42d400c4108800c004032004005030b004d0004001c4400700101122000c0d01c1030303a035122690030000400c451404ca90340d142c142580860103104a51521444c2100c41c40e8600000848003030b900070300190066984480668616200390100c0d01200c1e0482e4003030110341810310b0419034030184c00c00ba23014194201e110800700e022614065a504859650041c10329966a0060000901a0684213024030404503c000002501400100c058412070385001480003a800503c0b81400c00003030002046007050800b0300340807140107059050031312003624420b00340c41c003500d800d495600001d205c40b4080031000c2800641d000d8150042c2d5580c0d550410f05100c0c648520a83e01d075509410b07643d0000d0754104600291680280801841d4824041e1045a0440100c019040308a070340a8480d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 889549739 1250 889548489 889548497
    0x406020912010213172a090705120106020102040515030c09121b0f0904080a020106180e010b090405150c0904181b08060714090414180304030803060906031c 69
    0x82c0c0084d5154185200004100e0f0301a02c1414848910b00302c1d44071441c0c081581c00801003550080900d50011100c0c06a0880103009414142800600540203030001d990300c11144e2185000440c4244c81070084d201160f201601054400d03080707400d034402c0d542000f048400000301c280122041984d0301d845203031400d01542c0284c00d408003401103040501d6401d800d40c9000d17244080c0780e0076164444482445e030141e004a552a290085a08103d001d42801c0c1d0051000c03640c09403042c060719185501404804849800030401c560b1a08144520440225000740aa4110210146550152042060f03100300c1043e1035500e400b43d403400083c202c401d000d900b50340010390300361510104144c0700d01e00040c2540814440101030f15041a15543c0e910013003804d01044468842610030300180c1301030b034040ea41d00800c2841002d01c02c012964150504480107951402c0c206d030060102e2201204540503a030300031040a10b1a0768880511910301e4001e0025034041c82600701300b600030114011507206c280d06540d2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 889550989 1250 889549739 889549747
    0xf410f060a021201150c02010815210f160b3106030e0c0a0626040b06031c080a1a0429060a021c020a0c0f0f06080103050a0b04060209120102 62
    0x150524480f058000700e19400781544110540707a0000d4901d040e141c1c2c2441d240000d980e50003140000201c2031ba42c2c1a03000035104034016029041c450324104018011b20807181c07500c401003442075641442c0c05141d01d1000201c0000d100710349c200c50007071174212164410741e180d8050510318518001080c000341681480210801e1110580c140600f107000c104020050044246c650300041600349a07100300400d21060100d4442001010003550204240442002105107400e050104040740100c0d11148a400348001c0c072021442100c0f0740100711091036079071103170070340c2d4001032400241049000c941d8002c2c1c0c166680b200a9403039000e2413841100d500080c001c150041c0382d581d60844445070420744110350500240c14215070008503103900e0501031500011000c842c500030780c1054a000c0028000c00c0312180040351154030072598004950003460b9000c00d042c4d03140c200b00c611603001c0c0001003054100d10b0000c00826141d420894000740500720052800d87c01a001401c0c4020310341011b0880d94000c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 889552239 1250 889550989 889551007
    0x11403070902040e13050f010908120c0a1e05070c0303050d050709140103200c150604290102010f05130209010f080303041407120f410f060a02 63
    0x1000c008020900000c0c1035003801d041008030568440300402c03030800400f44a0803403090001c1080080c8400c43c4e0f8030f008110300100c50070a20055070055003895641c08103040401c07880f100e0300c011030300c070616030f83d45860a10003841c40c003101440245040c00e08025081c448030340400c500810290040d4841d889640e60703a0901c0f460042038a41c0101a0014825040810408003c1060180700c0c0880300346070004000849410034940714001c04000b884405000c150400d6107200080c0070070a420480d0110300d003a648880800098502d01070b02c42103994003802400301160200b00d03408aa19605000108101c4408090a01116012688410160000c1040000f0340c00d00c00d0025014125a80d50340f42c1581c00c1030110743c2c0e20301c03014100a050914800440f4030b9031009200c0f4002608040603120319605d0f40e404e280403d1300c1e15210a80314803010208014501c205030018081340c8132081c668440b4903000c4410643c0b011806051b000365802000c9002d50413170b805105651141005040042c1c440650b9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 889553489 1250 889552239 889552243
    0x905090f0606130e030403080706050f0c09130c020f1c0e12030403110d12090312031401030201200601150e01090f0909020a051c030e240d0e06011403 66
    0x4031030018455048401800180e80701c0c42c040e820507400e595400f00303180c2400d4851525511980c0c1c40505003242c0419417030200545078200500030200c0c480030f0261502d481900e21051321410099541c0b1689900c8648400784090300294078800041c01039500302542c004500d03003090302c500c2501480a9074485c8081e4101c0d088031400c3c3d1341d910700b502d0410310603600c0c181d902d5032403050303007c042d102c008034940c031114598490603010f21641d4030284810042d544050007414844c05800121790300ca140601d1042054841c4c4030f00315450905003150901c07030340382d030700151501c2030034800000d56824180400a500e40c0c040002a0082190014000d16080368160042041188080c0541045034100c0100700d90b5928242c0c1c84184c0e05200c80010340c12800d84001010380b8030b03541c840e40c0c0000e508010402c80e80d102404607000c0d18060344400c20081d00d440208010444071070400720342028a806528604017943c800390821520820700001c21642c041a01450103d090b80400c1c002824100f840c4012300382 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 889554739 1250 889553489 889553503
    0x18080d0b0405100e0c0f13030303020d05011202030a020d0302010f021204021002240a09150f060b0427140108030307170105010813111e0906060a02190615090509 71
    0x1030a083c466942d0820301c511440c150080e00c0c030040900c003c100c0d0208405000d0850b8690b0000b10010f0b0f00c0d8031303928a40500079400101c28621a603207044000262800011440c14603d80c1c01405818020400d6003006285081641d06604542d42c070003116824070b51a20080c10f4114a031069054186024030402201c84000900d00307003107400540d4038582c401c40f00f1089855803180c0c16900c017116038422010f074004080324040604251100d03140040e802c03130607601041c06407000da6030502c003e03620303401da464032881248150f04040c070058442484038500c804c00400191001da001040b42c1c0c501c5007042240700420380162515410002c103010b0740c2600844902d0406482d13042e200c25640c07610001900d010001021480398503040c1c030300d071420440043c08030300c2c22250051420803041c2d1900b044a180705400080140141200404244036207400425191f401c0019401007080c040c0c1c00700c0b2604080e201c0132080390303001d440307154180c04090100300e01005000282c00c001601c1c60700c84070203840d1100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 889555989 1250 889554739 889554751
    0x1409031e180d0f050703080406030b041a150403120f1701030b0412110607020706170910090213050403051201051e0907020708030c011d07061218080d0b0405 69
    0x1005002002009500070241401d02141c034100000002d041c00c61410300c07030210081c035a000d4000c011041080c104090700981e900c0340d40800c1402e185074203100446100e03034055250310321003546500313480c508660340d44c5e85600080e00e2682410f990f9a120101c03500380b0401c450209001d81c500c05003d070703405010088401c02588581c81c41d545035445885803000040c00142943d1407c0d6446042d1713902518501c00560100300844565244c0400000d4031203000d030140b14000b0341840c00105804103400035090040441c1c901820700407150220b810000d100215007240c101d80001c4e4181040c849610a41c0e2040d4003a4a4150396442864500c1007004c0058002a2080015500b1031144407200030300051410000d4a042425032a03035041a442e098660780280041d100005080e074140906401004142095010410094807458907481c0c540c9014010303400020064600c0e035000c4506a00070903070b509115226081128060748540c2c03966404644030403d1251601240c00f0b16050502c944d07a4001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 889557239 1250 889555989 889556047
    0x50a0801060509101a0901260708090a030509040b15030c1218061801020c011d1209011d0a0f03110a05240c070b0a17100b07060906140903 61
    0x2030400071445c1010810603441007600b000855510b1099004000b2128010b0700d4140d0b40c4040c9101009403034040300d084540702c000030414030100c0d46040b000600a84480c0d03050311000d0800c0c1048081c0001082503d1845500050200384801400445d10096004503407588801c2d9546c2c0712500c11414070000545107441000011200464521001c2003d5030070200c04542c80146501503100240a4010714601071055440d11071041d5805003051904a01c00d41501c00341c524149100c0c00b0040399000e00084c2c1804140c0f4004c00c020b078900d420710000e42d00b941c0101a411043d4031802c014a0021031500110ba01403118881c0e14030910b40214000700821046607c034141b9404851032948001d041c00c0f41c40c4030002c0210701000c1041060040001a00c466a001600c1d450442e400900030440c2c40c00b08182e80360054045a88400544a0102603403046a405443d00809507202d4004120710b003016214a0799884070700c1010b003000c1c070001d4001c0d4070150003140c4a55180f180014200c2d407a041001e000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 889558489 1250 889557239 889557271
    0x141306170712020d060209150f0408100b010207030f0501060b19020114070e06091201020304050a120807050304120e0d150c0c021f0909020304030503070f05030603060a0b010207050a0801060509 85
    0x5a5078900313045042030340180c0c0075848a00725004a030240564031480145000003107411442120050040d004a440764001c4a03071020f44444600200c500e0382904a006800c81941440418001c00305c00030703018400c000014801e640e40c920122543c00005141d044180e84140b003e0300b12390709000b0302401c1017004001c0300e4542440c00001e4502402c5006d00d50055002041294103507491051350342561300044000e644d64078041c54a0360302c07192003490031a00a07440141c58110203110707444040c865140b40d00d4a81c91500c3c0c42c0c0729011140d607520074200402c24101d60000541e01c403000e5040d42103100f02c04416116100011100c2036030501000801081450840358001da0754031000220b0740d41d210a8015002c183c80001160b4402203500001000390001092204150f405002144980d14070f039110400000070003030440300d80c80300b0380316a981540003902165131045d40d9403203542060702c140122400d86a540d008207800c82020303409a44203035580c02c0704000078104480b5182d8040e00b04c400c08803807 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 889559739 1250 889558489 889558493
    0x2025050102060709050907020114040b2e0501080a020d0c020d080a0c1d030a080414030c010801080c01110c1003020d051f03030503060d14012c07141306170712 70
    0x4d130380858800c8602c1404c1060100e81c0c40382c000c0d405001c1c0c0610700c2c1c005441d40c1c0760508080303040510a813000600c260504c440c41c40382d900000130000f1511140701c00061440e10b080c004582c400005080c1c0b9614960070443c05581002c248035a0030b036816107030042c101c2c1d2204010b0140c20607030002c01d1031070f030700c0d00f45840441d00a81c064031a110403108120410080d0b000c00020902d0302c88501c0000b003842200084c00b040d80d20030002405400d407011002c8501800383d500046942240c00e1051042c01c1d8040b55075003070f056000e4030400c51420445411100344102420010344805001c1c0c11030000710340d00060b2420a03101e18010f83c1d6100f070007518a00058001c4c801012482c0b18a44405020000d000c000b041c4507985082a0303a034110340204048444948071410346000300910681c11400d400544800d00d58401450b4482906481c02e04c084c0845a00c1c11070341802e40c0098402042d0b1015690807030461110041c4148405059200f02c450503100c038903250300e0700e000000d4105244420800c030744580 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 889560989 1250 889559739 889559747
    0x180d0f021008070f051b07240c0201050703050c010f0f02072a15091a0d0510030209010b0d0f090f0c081c050c01150618050402030c030720250501020607 67
    0x3000c0c28507140c006e80d0749044114181c1c030403c0400742e0880900400d000050501c20244c4040e03000d0392000258902890030440070350b00c80c00c8405009010030801c0c03160201080c001c0000d00440d10440d000030501601480e600c504540c004200070050301d071301140c1c2c0c405020400e007114080941e018440d0342c00c80300c80142c05801072107500c0303281c2280100325071040c0003601c2110520300a20030025200c40484800460f00600e03040743e904004000e20748000180000450440001102c2c1c01406d0b5091036400c010810720741703910084070032800c0390325140c002c9400040c074401c652000d4051107142c040c02440e0f14040e1320f18002c0c1d60185001e40c2c050005603513030240215460401500509281755101c4c3d0705000307513003d0080820b024002040c00140010a5a0401034051996007028130400f26140c0311404c00040b40420740d001000e11006000081700e41d405440f407205d4090504000d117081b181241e403620b150a22980000c3c4040c21540a0031044060040112010308002d001400d4a450440d00042c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 889562239 1250 889560989 889561007
    0xf1302181504051c06050c04151b11030307170904060e0708060d03260a0606030c09180b1c060b04020a02060412110102070302060916061202180d0f02100807 69
    0x3034841c501e440300413103041c0301130100b1502856020005100528280c0802005c581007031080e0300e04041101c102c4082c0c43c0c41a48a600b00300d019802d040386464803510741c0c031248401c06214603014841001804081140c10b5010610034104201c4150345c1c9013010700f44020303034040b40c0c001420851070400f4841c490382c000c61400d502440c21764405907802030030700702201d0317030319041000050204010459503002d00f00641c0750751086040d104184292580c83e80100c045650b02500c1d800028007000040c0704505140685080d52200440b01040d00c4181d0b030001180240038450021402e0102c60140042110900505040c1081103c1c11070030540d45c90b40107510b48400a000030854002941c1c21014680507200142d043c0800750021502e0b20300b1858044d40e00c03030094501c070b0f10310302c01c8410148402c05607030040f0007540c080d60303200283d00d500030301c00b0400383d08549001600b0004212101d4101e4643c00c1d030011009003d4150340b5888800c43c0103012880340f070a102e2600f0055a0f604100750541c211101d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 889563489 1250 889562239 889562249
    0x6050f0909150a1e15050307050607060905011103090a030201050702150105061b0f01061e062f0d0f080601030e0303060d050a02040c09150801150804020f1302181504 73
    0x2c95541c071401e00c8014000c090390850b4004e50014060400b400a40c0704081c002e50b0f103402d403030f6403507180c8081559a807620300c101544101304004650008240c0d4000030184e034410030001c00c1c41002d2a00306580341c3c1085031101c100354480d0070003009046d42405881d8118405001410803d121a540310200d41c0c014002c85006850000303080708400d0701211741e00c00702d1138401c003692641c18007a848135010380214458015600409050341c4140400d01d90342d0401c807401c648a440703401d81864185441492090280e043c400d54010408040c0c880500c0702040c0e60000b07550b000c0040d00d80d910302410301c2d10041c1145041500e000d107640492080003084036049103085030308100e880400d280052604401e220004d4009040c1440704e0056608104000155035000e08803030241a101d4a084030f0f80300c03091140700364860713034030304035500203805018034a0b0841c2c000b03081140400c0001000c501c0784a407241e03100da44a03500180313a0454004035612034000000445105190041692a00220340501d01134 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 889564739 1250 889563489 889563523
    0xe012003091c020411091201020f09040b24210411011202040911030709120b0622090c0e060105280e1306050108070f1b0c08030d06050f0909 62
    0xc14030060786200c0342d950a00760300030401c1c42054481c3c0080001e613003029148030f00031400700802e01d0140106009480c400daa500059904100c4600100030203041503c0c803a2741c204610004515110518085510540d1a2049140d6603440b20b0350600c1e0341d58000d420216158000642440001100300035009028170302440c1040c80c0c00041380d1039800a1086500207010035140c0303070340940700482000185108410580b82c00c426140e54000d419070200101800505a03039401000890624100150040030707180d006015002c0795010702030404980001d0010307111507041d107002f042490450044664072400a10301a818071583d02c10001c00c400459013001c2110604000042d4001e01c12182181c030b0000003011021450356400c0d00100606150280038000b9407100c00140107107000f2504400703a0708841d80c03801441e181101d212020343c0e540342380c100c40b001080d034000902d6003410005040c0c00c506041000505a15050820407103003080812a03001b0044902004a15440032505100742004001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 889565989 1250 889564739 889564759
    0xe09070804032d1101060506091f0201091a090c030c0a210206070c03060b0103020910050a0c02030106090b1801080601050d0311030f0315040b030c190305010c0e01200309 75
    0x80401294580c400503120340300306020b0200f00168440035034a0914070b060004c00440b5160400d12a480c030907485901c1d0880140c0d4040c40d15101c0461010802e50b00610000078040c80694881a0561080c4298100f500d900018056004002d1001a5540100700d00a16407040c40c81c1c0840d0b07407100d052050019171101c440d41d003c14034950011005900c0d900070001030391103072203143c42c22011082d40026a83c403841c02c140020390b0b50191084030a01032009003212a64403005400312416480f2514800811080c420032000580b0b0901036a406085524400315040203981309000d45907001d14021044220220010000d0740340110319a0305490041e40c48400000701da040a554070071101401311040c3c070001608071100004003001e14018550071406c4100240c03d036040006849042c0c80d00fa50542140300810740310702c5c0403001e0f00c40f42c40e00010011803559072511f606085440d09603500c00451680c8800800135030707120340c4808282d54000c1e4485480c007840c0640b16640e00801c45100e014402c804 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 889567239 1250 889565989 889566017
    0x20f0d0309050a02120a03020d050310121a01030b09100506061b0316061d0a021503150307090f0509030a300c020a030e0604140f121005070e0907080403 67
    0x8401e040011384c02600407421000c001c0001130342c0b04405202500140603118118540c00c0c07103142220702030b202c18080b280e0702d9810078054919240c9044001c43d81d20344a003031001140c90550240c84e0086000714a02280c82c5404103103a07080800c050218009507140c102001000d0b9542c40030384088d40240c900020013810304048c00344ca07510807200480b015009608812080110b150424640e40d03006102040c0c0d40800702c07189603903401c110a0001d611008c1405810340740080c120103940e000485408942800002001081c03e2441e6034011101440e01c0307400c1140108558000c10350003804640c002c43c9400b5049000420705403a10b01010704801c90302824550340411007040588444400c18104400c0500405c040d41c2e8079006071040b00800c0c10900740d2042c914010b8103480c11602200d01606001c8a19010454442d00b4460056481007096050792130041003004981d40c801f0407103a0006490a04980160030304030610420b602c20001a0108040294018810754205a25041c0399440b20184 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 889568345 1106 889567239 889567243
    0x106060807120c0e10080402090f0f07080406020d05130b060907051606020d050108030a091a092e0f091403030f0711150408010b01020f0d030905 64
    0x14420814060226800074400c80c0b0080c41c2407542d6941350710001c4c85c0303950703e60001c2e030004100504000450038140328550300008648040c06251410001042c021013004004008200111003c9420800301e50103640340540b043e5014026807903c0002e81410b103003151415203014000201007852070818001c01070050101e941ea4503d01540040042d00410318008102c2c0c0550f400c20040c0304883d840c1c0f00303040c042c007030100145590701080740c8000c0411140d40c100f81402103211811a10361003051003141c0d4201019180e2092000d8192403944c1c80c90452600020f03823001001d01340c0384243d440710781c1c2084110123440c2c0d407010603200c0b130504d0450400890703c980c055008000441e40116064041d11803148030392200c502194000c00420040000040704462996011030f0500811400b8000d00f00d58503404e00c000c0003480400280a5510003c031400c040500d561001403034140001 = true := by decide +kernel

theorem cover : BRFrame.Cov 889388489 889568345 := by
  have h0 := BRFrame.cov_init 889388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 889388489 ≤ n) (h2 : n < 889568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
