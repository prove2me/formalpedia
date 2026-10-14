-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2261
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:10:29.798992+00:00
-- url     : https://prove2.me/submissions/95c85d6d-e02f-4e8f-994e-2438d71d2b84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 406474820 ≤ n < 406654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 406476070 1250 406474820 406474889
    0x9011d0403090909110f04090c1503020909070215010b03060303030f181f0c0315120201031d06040c06050a09090e010e01050f22020919060302190321050301 69
    0x30301c0c00c0100000c100b604140f01400d44e00807a0300c101c1c00c1001c1d00807c800c913a0500c50062121200f07010800002c005400039400c21a03241c100141040c02c01d0002c90710080e000c070754241c01a040101c44518074102c01403800e000d800100c001d00c1c11440c054010a41d28031014041692400a040000d0020281c118240c1041c1044109882280c3d002070300d610382d03a081d02005a060300307061240300c021403407082c441c86401c4400554458104c5203040f110b4001002d888000341d04041d1198030301502c0d242d1b010184c000c071242d0000180514506400c1c0740500012a802150401900300003440d0716942c403402c040203076006001c0004560424022240c01003007804490301e5107500f880c0c00c200c07407055034083c80b500c142072100780c801e841c0038231a01d1840c00310b040c120020b6201c06604007046140b014004600c038411441d10000070500d03182d40000390301100d00d07091000d250128644c284200000396411081c5440c040350f0b846100341d0180030244c000e020500448181d04003101c9500c0000d41d10190ba481c41c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 406477320 1250 406476070 406476089
    0xa0f1d0f011a130503120406022a0d0807081204050f1204090c0c05150907060905090103031b0b04080915070b0105150712120c020606030601030308060a030501050f04060b09011d040309 81
    0x2146c8995800e070541181c410700d40907028417070b4090224840ca030100b4400303c00004410041c000c3c1c403802c01c0444030f003880c8141c501d0344c0240610f000084a100081c4682600f40d04035504601d002c1c40c25600d08054a0b452405581003000015200c2d00ba14007620b081d910201c0021a4140c407403002150583c1990502504611034140c3c4542d615844040540c090f1a03904140d070b60702c03500d8250550f40d05080b07214241d041041140100082485420620705004403041e41e030640e05078a441d038504802e001d450a480c00800080c00b403200303142c88140301d100744400300360f243c0c1040640c0d22504a01c400c140300300c1e405000d0f155103070f41841d40d80d03008841000d030380800c240f40b101c14140401003072a10084008224185050081880f00c0d0000032018811400100240100da00395030b011070701740c400a40782640180403c01d0100004100b0301a40744186400c180d082c010b45001d041c15070603107c03026030a0740107054803001403001d20703211b02020240c8400208034540e65140d030314007150100381683c03010710712 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 406478570 1250 406477320 406477333
    0x210312040f02090601050301120b13050a06060806011d010308031e15190b09010c0507090c0302131203021207022b0501050108010c0f0e0a0f1d0f011a130503 69
    0x4214284249801c2079000383c40d00320041d69070782c00541b500c1c8401c1c010500c0410307690482800140440c035101d136200300d12010210404003903a80c0d031882d00344c100004440c4c0c41d898081c14010b991040218a00400880c591206002489020500d4917041030101400803c40000000d202d000c0e03205100c4030000d00e4988003601450224a5480700d10071341c0d5403d41c40351100700843d01000e10950703c44015205403986e21881e0000ca400190340d11059141c080740c0601450340c3c00140d000d030a106030180b50360b60342c8016aa600140c0040c0c2c201d503099420007040d201d101c140c1a03000c03a80c001b0b0b8031032401c40c9a80070941d6505a1740005024100085410041e036501000c5229a40001d40c29a81a00c0c4c4600c1c024070850b40c9500a160a840c900c0600500003200d0450062a092041d60911355000e0b0240c030800c40c29840300c50036030500e17070305030401d0b86815001246480c1d442800d23940d040c1d02040c3d91040501550510480450060401c0d20038030400c02c0110704e0020b00b081d082140d20041100808850303a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 406479820 1250 406478570 406478573
    0x24070914040b06120405010e1515010c080d0e011b14160204090c061b031b0c09050c03100b04030b040602210109150e010302090414100f1a010e21031204 67
    0x22684c0c04440440c0c00f54205190039280b1000024401c4404150320400c030034507070350141a0180750300301540d4141000140c401150200e002c44000300140f121a80c4003069241003400301c7c0703095401c00300c90100d40014100e83c0d001a680c1c094030509009032024800b9903900340304580a0300c0508070860280d403080c68000181d04000f15000510103c0d00152910011000f02c07604607107400c058101c003d00424134207030400100d00704001740210624440e44680440c0b0b61140700d0f05041341c40465000150000c0002030080216113600c0c07582c01049107841040c030300781c01c6544441c5484005007008002507004500b400700b0490342000741091001d840c01c12825903a546070700e54042e000e00300c449100c2001506001c90090012201d05042c1e0b9009800c1c0b0007161596650b078001040210188665030150b2800c001112500f806803403110514140003080806101444000c52101c415507030f41440000c15550400707884242404420008142030b0030b0400307903400f400a0440c4650f041d1684091004000c010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 406481070 1250 406479820 406479847
    0x2031e040501140c071512090606080c24160b04111504030b2e060509010206070e010f030b03160b1314090a02160b0924070914040b06 59
    0x11100c09a0f40c04400b00c110008074441c40c4540e6100c1e21160704858014004007143c01000101c8180924000b05e14000801700242290301050b0122a01c0b0b440d88010403012030b04110000041800701c039510526901000078040711411070410300550301e80030171032403408804e00d111030238225000f1000d51402c2c0340900c3e00c0500074181480306803264880301c5840c1030500c400300a46064a5006100348040d8640e011a2120025a03500c885080c8004500070b903000b0285c12072030310086c249600d6454480c2e049074001380c24442d00800c17080420607580340c0010399a9000e410407201d0009814000344600140300446c0c03e107004000e4130400c10608100004821003140000c10038582180c9000e8121612084069104094200501d9104000c000490481892a80284507202ca142c201e280014059501d01582050417074031100b540e00843d21024581d001e0781143c2d040d01d9281c038412449032502650240407029180201e03010f006200b1130403c0e0741d0700c4580c025504001d0090141c0e848640011404c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 406482320 1250 406481070 406481077
    0x60b0117071b0b040303020919080c04021614070602060f070c0b04032a02040f2318070b07050c0307050a0603020d0204080316020102120a0e040b01170a0e0f07030c09020a02031e 78
    0x5070082d41f08010b2504c00c2710010303070307103d0950740034038064500703640d503081000040c0d00405068481103aa07045a00005200e016101c0c5990003000c0c00350000d9440d01c1406810f280005101988032040b00c0100311200e940260b50400c440d80c4504080f500d6269820f00710380402e070324059084205c10400d01102c0c02450600c841110f140700300d40078000d0042100004040e9290b080b43c1d01c44a60701094038042d030100c03109203294002500603291561602c0003819074542022544150700c0e101002804000f40310f014048603155090580081407203d252001285424080c1d10640e8109540410328000758006c2c2d8040781c000341012412070362261540c02d04802c10f401140c0080307016110746d100c0d40340040d4050050b03526012058a641a01e807259509100c040c000c98004d2034104085884480c42481d050800240181000000095405212804240b4154000030300c0400d5038414801000001c5070389121000b40c0700e201d00d01584404084034260319501030300743c070a50071005c0803a0980b000c1da80000035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 406483570 1250 406482320 406482337
    0x120504030e1201020f160f080316080105062704020d0504050d11150c0d060816050a0906052b020303041d010f0503100e031c020304060b0117071b0b04030302 69
    0x5842c030701c22041850500f00c2c0304286024692401c00d104120200b1101142c0050b036600401f141d0709070100650700d826181e8021610411102074068110003d5540b002c1e94130301508055414501c0c110300c54000c10300c103203610564401a600d152200c00c0b0181c44a8054440c40080340b4000c0c0001d040034035005481c1c1e41018120f4002469103001c000c04050300040c00f04414000248003107240d10b410100150a50203410b42d106074640b9102d00282000080101c43e241100c011a07240c0d123a401d02c0c1c2003200000e43e681c011a090340c24640240320b40e0742c80d00000c5000400c042070140b0070b07010031903042001c0110000c0107507241c0000b180000b10045440d02640501c00c08901071038880e0707282c080c1d00c4100b2026000342030b01944011441881c0351101d500c4000d02640700401c403801c00e2440e503001080c5013248104206c03513a800fc17090100300301c11400380003448082402d082c89106132a1900045c188001800c040c204040202700310f0b1068500104070700e955070080f81617025483d02e41405000f039400f0280 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 406484820 1250 406483570 406483579
    0x20f030a081c0213030f0804152607020304050f12010606050c15040309060302130905070f080a021617070807030903111f030218030a03080610030209030a03080403120504030e 77
    0x1401c1001e1600d100700d135413908800e00c10f151a1800e40e00c80ba00c101591034021200c0d000c0811001c01c0b0a482e003a544407140c400d603950440c0d41100008010018440e0203030441000b003180c1c00303000d00c640d004803d403400da52056035801a00800940042d07200e608060180340075500e00000800c00740d500c100240f6003030f40d03200101d907600d2a1000754007500040890340a000200c0103502405014030036001058980921100d542c852902d803a401d80440382c050f51100040783da9a140700364a140c10620701c5602c4059086c0450404110024402141200080040904000c0e000500320a11140b0903500003c0c0c01c42091525107030a4a000b904118150009840c500c5110780d11454900d401c60007100c1110f5502c20001151030003807016006508100d01440c88403008058029994900f0021140c42034040d07650030078641402c3d002e1080c2d4800e4003004008050040007103003003039100080c0c040c0d0801da140c5000003107030791541021249280d8a402c1c1148550810052200303040c0d000b1211003003014102c0c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 406486070 1250 406484820 406484857
    0x307140d05031b0d0c050a03110301080c010c02190605070b01050f210f0a0606030b090604120c02010309021c06050105030d091401020c030607230a0813020f030a08 72
    0x1559654400308000c4290000d0410400603840c00d0590602c4029105500c01050a04071204ca1000079510400d00c1c1e10000381c07001c01e914055581c907008820301a80c0c1052403e18550411040c2d80d12800441105414010454030700d038215100e90200081c0c0c0c81140d900d2406240d00c980c1e00800680c4211003d4455054a0001041c0d5150405101481100081c80e80e42400216203030b9064a514807100e18417107000e19910340d01e122724188010b1800714800d80000440c40d09614003101d000304058104040d0364455401c2200240a4030351b075140341142800c2c880c0c492402840120f01421040da0700a40041c115120407548502e00301c0c0001480d842080e0078045030381c8480605503280008807081e00040c2d03a50004011211414a41460188043c41030b141270300c4005010034985034040e5002c1001a010304000c40140018001d1005130090700a001c0b4546181c420008210610290070705c1410b1a10600ca001190f4410b91002e0740d20344050103803418001d003424140440d4021100d030503408903815 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 406487320 1250 406486070 406486103
    0x20304060f0e0d1206080703050c0a0608010302010c1407090c03020703022e050c0403060510170d0527040606020313050901030f03110a0209010905041101021b0f18090307 75
    0x74020b40070400380e80c02c0104a076001c404000c59070040b006003180e0f025580c6002c08940c8500c2801164040c6000708014200c43c01e059040c42904581c660180041108520040c40140c0e480150919003603081580442d007640d120381800d081c081a64003200500d4a8903d018110070707007680142c0862400b90b029181e485021201c020300f03250040b54140d900a403112220952a04c0e40d41c070240d0044141c41001c0c0c1003070f8403580d0700b1044030340c1a1501c0300c03000c540000400c4640c2c0e68401103002a00c483c0c0c0036154850a000024001d070080c2d032100c40d044c4003c000c6108039200320100c0b042d80203c00030801d00181d5a9040043d480303600c140502c64094804007004940c5050451641d81206d5000056010031850381c1c9049841c82c0240c0d08400c503501544071a8405a0b4642c2c94290103450014000241c41c141450000404005038a101d030544d00701c10100b10326a84605d04000c0000029200320b12900300c4080000c21840300550820040e200d03d00c1440708020740040a02034a42c0700740107009006030407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 406488570 1250 406487320 406487351
    0x5040c06031a010806060a0212040902091201090246210807030503040305160c14040c080711150a0c030c0212030a0b011106130506150f0d0f0b010902030406 69
    0x12054086840b08012400a00f81b100050a6000c190310540f801025494400405640f01d035110341d0310b003030700450040c0705882d01d6951501d000e60b401000300004040340d03000c94101e40c41c04080c044150840d000b282c1c4445043c0038040504541c000c0d0b003451500002000500d0150a800b503c160708011442800284010002c1032031102c0d00000c80c2400d203080d5940032141a40000c104170100041401690214008030b82207511452080c04070403030b41d40c104504465254420100c3c1d501c15030500810307610302ca410500c0e19400c20001c4c81c0c0140099105a81585000242c805030400e8200c40c80411001030705035845105103103110750b405c1c440c001c003001c0e040384e07545919000d84680c2041003022071201001ca5100d1f0364448010f0400001e00b0f02d011075601e080031021180602c0140c0728840c86004c00c941800455800a46074901050308a20f800129064a1040b40744c5400b40000b03844400500140b4111034081d960b01c40b441c0c51aa40e100c1000001a40068404480c1c00b03003420307125640c5004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 406489820 1250 406488570 406488611
    0x1090309080f060c130506031003050105070e0f090a0b030d03050a14040804060503060d140d030b01180902070602091f020f060f061012020d1e05060f0d1505040c0603 73
    0x803041c0040c02c264884031344220300340d0710028048016440d0180c3c0064640c5428002d103108108202003e4041d40c60f40c10841d083d5030004144100700018a41c6d207901a0b550314031003624402065038038030160f03980c19600790001e003448a07069604d03118124140d403c4d194190000d03481645030203405c4c44602402d0000c1c0400d240c06450051450b9020310007884414403840207564820342c0182403140040c05600c401c5000c0c040310a440c00d440d04105d40c07141840c4d4045c0501c207580e0b0300a19141c014007074202c4584002c5241e074041c1101d1240c000078844140185c6405450700700724000e0140d00022200b4030b081c420099800032400142c000d180141a10180c00b20b80a0b01c604c82c01040b074251035480c02d04005800c0121032540092000c2c102c0341f00c2942c0d500b0f202801e0f420950700c800284400204001400c0d9402108214207030500340030070000719490345000c01c0070944098982c40e10b00c0d0207070318010791030301e02c4159402201440c080c208800d000c90302411004550150b2010400201e409418507103204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 406491070 1250 406489820 406489843
    0x60f17550201050703140301061e181205070302040e030c0f0109020117060d060e0c1e0a121703040809041a0a0512010e01051602011815180209090109030908 69
    0x11403180c1100140d40a0b00040c090944a46802c40d8520f1895100c040590002e8108100182e98840046001c000341003005203041d4640c00c0082d80740c00e110200c1c0203443c0301400b910394190b020009000401ca002c01c10302c0040c5900510900407070400c0c5400541d6030304508620b601c1442214080d800c3c000043c410802c3c1c1c07640603901c82060f00d84907101001c50101c007400e0503800220800c00030000c9540d520401d0640f110a83c003400320014510304020032104d0041c2d54810f50742c0c46044c664401ea4079100c9003004c071008426209000702c0c160130405010000f00551a00740340000041000308944400101140041101c3c10845858aa940c0d00d1140c041030041a42101000b6400d1100f4901004603110441e036240002c54511401024a4291030040e00c03100b2148036400e000c60380d15902809110b1403c80e203007001042d41041902c8410991009103121080780341d803190030380800303c034841181402d1074028058541604092030000e0007408418800d8000400200c0702040c1a070340890400c4924 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 406492320 1250 406491070 406491223
    0x91e0e010f0204140306060d0c030b060105041e06020706050a120e0c100201060603050a0203010b16020f100206010f080d020d0c020f1f1e020c0913290109060f17 71
    0x20360552f515800507140c060300c01814800c050100041d010100d000c1102c9034090740c4011006c0501d4070030040e16203401c070382000003803010605c03d4980981d44a003048441d04000e800203e0344442d502c01490412160b540b119030403181d182019158550150000d50031100c15540400242d511105258100d010a00868a110504228850200f03420f420041180f41c002461814124002c40c00200c141420601d20405a044600100000c000b4019814020000b10000d050070300c0d401400203494011981c203081c00e03c00000f01d42e90664642c03805e4500c3d101d034054042d00500300800b40742d01c00130300803020348000a00640c05001085054840d14115070003250001c1564084501c200009500300074070641c01070000d00282400700e015141c05802c040303010724680380400171642090300200416001520200d042c520204801403032940c42e0303000c0b5443c190f0301d4500b4001c6a81964182540c03078115403107030803402c4001d45440c034601d070401070702043e043c00d030190741940b105c0c55021780c52554104005a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 406493570 1250 406492320 406492343
    0x9060601030203190c0e13092a120302030408070f090b0a050604140f060d09030f0e090408030702100c0210060e010b03070c142401091e0e010f0204140306060d 70
    0x21400540c00280d000341c034500701840c0d07050640010444881f070414044100584450015041c01416030040501140600300c10380c845954540c02d0302c140f03281c0d21440450650000230a800c1c94828001c0d140500304440c2981c10559503075460304c030a01c10f80d01907101040e03c0c0c0504802d99140580c209030445001030182801c280ca401c241c01000c1c14074010240d0400b030120000501961003800800c03101c0c07695040065541c0290400a007060302003451102444185081446155030394103481d0b501075440704100b6540d0f40c820780124249107840c0c00441c40c090038660016902c54000c44c04044160302c1d6581045170303964929803105240c03003e203d5964038140400101e10180d12612843c00903030300070003101c0c6140e00700290641c5441211654078058034448a00f8402200b03884111a00510b140d40d82030002005140348445441480700101045640c1d5540c00a2080001c0d002000c40c48004103045450329a29200003a2211440121902ca8060240001c0c61458403480e1030000075000f1464016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 406494820 1250 406493570 406493611
    0x3061002030a08150310090615060921060905011419020403150e010204030203030a0906081302031515150d06080f06151914040b0102010204060e09180a03050309060601030203 77
    0x124044e60990158060050f9480805000114002c940d082803003458009440001000704c3c4400464581000301000403803034080081c0d64100b4981708240005c3c40c620603a1110034a80b2000809820300014029428528031081036540c40709054451128180102c0c80340041d0311000d0100d1046010042541d0341d481e050061800c081c0c0d100c0503c4800707801c00145050b850382c00081c81c50f0880490000044d4081c1ca05104203907100c2d00498103c0d200980180112400f5030011f41c880c0d0325401c0c04c1c00d04a4210300004e4035018510310a01c0001740c064110030448000c05621140c1c1da0114a110034002d003404000a0a507200140030509030030f00c000603080648416410580d080e41c40ca03845944086240c1020f07000b081060701840003045034520145d41c12940e442488190b0300d4402e003041c190792060108100894110051604100d0201e404420b0381d656441c10102440d054104504207100b039580c04001c241d040740096011320b80c594219180355a0f80030045040e03100071100c54a000da442002c000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 406496070 1250 406494820 406494841
    0xb03030706180b0f07031107080703051305100c0212060f04030503330102011b050901120204030606030b0910110d09140109080a0e0906090f0606040b0a0503061002030a08 75
    0xc6101d2503003008411003800503120080c0f101410348021144484050901180e25010b02c2801c10701081141d28900b0407080f42c03604240c80c090440e0180c10301c2030004005021080e41c2d681c0030042c000c010070000e00070881d04001010846148001c03402100f0035008010406000220a8400c212340c0c1160303072030350703070365550407500380c1c0010f0030b039134402050020030001e64141c410216a80c5e14112a9040c5c000f1034440009095420081c40039440110100144403581c0e841400c82d4040c1c034080c01e150b8030740200c20486200134843c81c0e0015040301e01d004000b208100680b01d4040c00780078282d08a4072801c19850082c4100c03050302c680001c0f020b5041080c662030000c65002012060b001c1e0341d102c02c014111039819070030740e0320449003241d507548005054402c0d10340280b0182c03162142038a21403044e150a1000c141c1c0300c00080d00e01100c0c19104c01c0000d1107a03580004940c040c103e120200340d00c8007a01940604540c0094039a5441101880070000c00c461002040da101c6007040e6860900640301c420f00c0c907 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 406497320 1250 406496070 406496081
    0x4050319050c07061805060c0c041d03070c0f051f12092103060b0a0c1e12080103020f2b02040b210c04050717070306050904060506130b03030706 64
    0xa1141c240050381452106100810080016840f13031050f1900300307405491007140f2a000b407840780c0e0060007841c807245400603841003144025a000104801030141412508507030040c02e21051200262134000c200d8003003181d20403107103118032604c401c40c4c032101044110342c0401420b483c40307410360420b203041c18450700ca4072408284900300015240c410f030325640c940310f158030301d6a1010b003041c01084a40b194503108020080620403003003820a1003502c8000e08295030b5460143c25860030401000c48520301680da52090707548600c41491813030726080054000c1000b48000d07485104618040f50260406c00214041841041c11006001c41d110400c4011003003030704d0041c0e80043d45e800204085031950007641c2d03a805400340d07070307524546c07042405245040c0d290000140228100741c240220340360042d248003544a5501c415826a907240324080780100905e6219a1780410110144400c0c00041c2c2d0001c5d0180d10103440c60141712135036a40b032006175010200b001d030301031340200110030100300e240c1d104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 406498570 1250 406497320 406497367
    0x308040e1b0307032f0a11010b010e0111031225090e0402010c05010608030c0c03060a0606080612030f0406090806102103030605030111121302461d040503 68
    0x469070b10f0107078010314480c00759031600c03c181810700090803103c03947c00c030424041c011800030007848800c0c02d00e4002800d80804c000100d050109030080250010f10601c1503c01c0c4182103c541d82007440c0c076030b0400c01c05180cac00441c0d680d00c150404105c0c000522401780700080d0345012340720f00c00c551260750044910a60409055031076542c1d03260080340d900818001403151031510700043c4640f480c49005c250405201500e01c0c00304610b0035008210f032540110100368400d0302140d114000041e4003816608502c038014010a207074000103804250580c12418503025542041c7c01c445040d42d13900c0c0c0454180240380030b400f4404102c443c040e50440703038001e00a42d22501c2490041042603a03400482c2c2510003a58220040d00400324404406103584291140d011606400349075a5010980200350382c099040d07500d1810000410341c2c4d2143c0c4190040601000c00c02c9503500050654030702d049590740c1c83d18061500602c904000d020180003c00134028000e5401801662510043c51001030807a00700911 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 406499820 1250 406498570 406498601
    0x7060509030309030d1d0d020913020a0905190c111f0e0a0f0203191101030c03090212100e1f0506030106031a0702150403120b190308040e1b030703 65
    0xc50f210545061000d50240c84098403043c0001c018000d03403441741c8500400c0035003e0800002d00c2030140c1d0718a803802d41c110000f039030740d030100c4074482c0086400d260094010f03020315070529003880200040480a0900e440700380c50104114000c00104543e0700300003541e510550341c0041400108500c007104001101e80c088180040c2c4071114603401410520002c00669201d03020070000d00540c101071041502c01c903002c0981204070f1280343e468030702e4110390f0300101741010b59032510205228040d9010014481d0000d0150740300d4503c034545250781c0d2500541d034070303050341c10300e42006052100050070300c1c0030700400c00c0100140b00041824030010705005040507070640d06c07604000301095403e402d842004606101e100390b5403920000191170b09202c02202c4120500340c400700808603178060080b806292010074080340e580c0800b00011804a0f0126030342c40c50102d41c010000410007110020b1045450f0720202d90940c3e40c900d4003614080207900c4000c0340c00941040000d000764460713484413081c803500d0b20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 406501070 1250 406499820 406499827
    0x60f0709090c05030402101119060f0e030a022b030f1116060c08040f0602070c030203120a1707020a030f02010608030a032c030a030209130c030b0114040602070605090303 75
    0xd0450007a5544416442c0c0810320000600041d4104005140c0044840342013441100c891600300b1552845008920a02c920809194904110441e0042c0c1040c03c0e65050a021143d80011780f00c1d242c0e0300069110000d44104841c5150348400c8802d80d844010340160448440403041000f0b0f005440c003196500301c6070390340340420302c030824054014095061030801800300ca40b00ca454400d040359450807404061140f40320402000410290b0060070759548044056200e02c41440c0100c1c800200d500001d605004403008a000f810040c8003a00d00b407121540d070480000503c0c050302104a4040e10b1002c01600260300303a1340460300800404110b1a01840000703026a80d400100b4255009420100002500c1c0c3c0c2071402c105668039000220041d00300d0b03407450490168044c5980d00d21801d0700754800d00d034020451404c60366560174184e821805205051296100c4204000c0040c1818007010307011035034200c170321814480100103032000c0d0341d0250024150a0f040c410151150342103ca4103d80c540f0080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 406502320 1250 406501070 406501079
    0x6040c0909030522051207230619031e0b0d02010e0118030506100e131b091806060608040c030215190807030c0315050d02010309020307081c0e03060f0709 68
    0x40c1c50440c038138240041d07400fa00345410440501e000790f150b030f8240c1d030003488288050f40031108084c0448500d28000c0d0075030308991021501a015543c20100002c0554400074100c1d40c240c2c2024441020729503403d451019440a45400c403000c03c10f00d943c02000040303501c00154000c401807240a1b005050145040821600400080105420840b4070750090824444000d1f4503042090152604c03034078404140c5401200085c400c00c5605000e030040103240805c114810810000714027418490009200070f407050302a0118048401d0f10465035107250280010312144034403d03890045e68012114003501e4615002c0200e40000135405c00c500010030003203a041c2c0802d50350b0310310807600a621040700320310382070788041c0c00c9a070450013800505040581c410b440f440035008110079110111001070650100303000481c02019814002901841441c0700890500d0000901505041321008002e4803800c0c550000c44050304210b0300c007500b6500c280c000c900da0034880d00c150365014403603150054140341e49 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 406503570 1250 406502320 406502347
    0xa0501080f031809100b0f12011a07030f1817070504020703080a0507020c0409060903030605010203090a060302030c09151e09100302031f06030b01090f0e16030209031005150306040c09090305 84
    0xe141f228158090014100b64040b844101071401080c0300d00126000504d035020150461080341d00044c2008082d86210140758018000c041e050404452418600e64079642500001c00b9100e0f0b101c60b4a10403420001418030f054000c4071412507041c1e403103901686400c04e000300904000f410003000e500a255054086440701c1c4200c68101d40900b901180040079424081c046800340d80080d41150001c001801c3d02e42c5482c078118080307660a1400594039611300b100101d550240300610b5501003a9662a403444500c54000b03840102400000c8034800744079644000320510405c3d809903003110503150f59460450199000c2d5500074507800d2688000d4030b40038154400302616030400c1300170a079151084806943d0004a82c006004030481904006040c1410718580e0900141603290300880307028200b034040e100350103a403104074001e070849180e0188281400050001180e1100010046000c00c510916000515a015903000310309419030b04d0402c508040074000c1405c0036024801e080003841c45d10b226 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 406504820 1250 406503570 406503577
    0x501050333070305060f0d200a1205030301031406011413090204090c06031a09040b181507030b040c0c2006040f080f0f0c13140a0501080f031809100b 66
    0xa81c1d0340005461401750100043c643d80c4011180c00740c1510f941001c00200d0200c0c2e18120f00702d01841e01034554200500050f241c0d507030b5400c0200040b140071100c0c6c0402c00000701544c1600e100703d0342050302040c8204000d599120034403d0554450070f0907140e04640c244100c080d0402945842c0100d0002d6071900420165845050101c4003c0c1240c9010050036170b240c4a03031904103c2007092400a549240000f590f004400384c000f40c40c0084000200b020b00e6010444880b031600c511059804940540880c0407404508990b8031021a0801d000304c109440c151040400903412504c5050030a92980c440c485103110315149050501c00c00b45066074941c0d5554040c0005040c0000d5114505090615081c24a0903140c584400d0364003102292200010100e10481ca0070301c2074501c02e10103090340c0c00600262124100e180101114a41800320003500d07600400c1c1a03403502c8048800f060303800104260380b03100c0c410998171a2000c825148059182005409400403211480141c82a446901c0c0040560 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 406506070 1250 406504820 406504831
    0x60509040b041b050618190b190c02090f0403030c0c0807110406050a031104111608030a020f03090606091810050615030106021501052d01170106021f0501050333 71
    0x1b0084001c1c21071914001c0034461141300281154030361140341c50003980942c000d004010100305107620041c1e04e540c1c4500c15041c1c00c160000c000030380608010625040c96001a1001d0380040e0500280e00d1070580260910341c000b90780080c03a249003034020340f03030180380c00060340c010395001c1c5d100d02c00042c0c566100045600a5030080040c0c1148000c44c008000894800c801505010700d0203101c071a40011a100303075140d040c1d80203203a4656a599480d580402446101e081c44612078003c01803200700c2100080c160710503641520f0300d0503181c4840c000d40f0105444c096420310300340c0c028080c1b481e00701c406400c05030700540c020f807010075080b280c04883c0e503064209802c4400107174030580d000c4070710f10002c076a9075004140c140c0701d510344516102a6004031480651000d0605100c0212803596a4070510360301c4068422500c20310000e5854120094460540913032034800d507001405081d80d6103205114680c1245c0f0300034020f0191011034552052000503404a4000510310055449296500c3c00909441031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 406507320 1250 406506070 406506097
    0x307030506180f0f120a0509090c070201020607020c1f0203120702010c020717030a0503040f062c0610030b0c0c0607030b01110f07091802060706020d060509040b041b0506 75
    0x9403007190b60a40b0b03160301c9940401041e8011041013480880c00300c0e00c8413210382414252942c42d01c00c1c0d1800d9449101e1414a150014042d1003005a20034000010b80080ca200b6400c2c2c81f181d40b240b0000726075039840c40c0203040e4050328592034228114001410f05050300101c1c01602c1c2450207021718a021684221040c40150b5142d000b00346886a050004901610441820000c024402c0c01200d070381340100007003141400b20000c0800d043c03000c40802000700d187d02000c18040c11400c85004103426200065100c1e018540000007181c1c20340c0450003a220b0320340641d1303469400e450340c0c80c0d0541c2d0540203444001c1018027080350940e81981400328074802c0e012500c01003074064040e4001062039030740c030a80a10a030045444031540c0b50300410260206c0d0a40503011810008401102924000d0007400a500910001d8104200720594018141c0755003090010413269681d0824401070709002c0314002d0501d41000d00241c009800b081e807001401d428140e0200c8810f84403c0812541d40c4107251800c43c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 406508570 1250 406507320 406507351
    0x52d0708090303040506010e06010c20271603090506011401090501050c0d0f0522030b0108030702091f0f12170a05040501030902060c150907060306230307030506 71
    0x40e400400450700203070030200651462400d500c41035103480041c011002030700140300c0440c0c01d60703115200002d10180c1101c0103405021890407408100c10076074440c0350280c1c40e4070f0300e044260081d404240800e2003044250101540d501d4400d0041030031414400c40c12b03d0340e41d420441c040b420030442540a010900341c055000c50380c4000240c00c0b9101c0e40d0210341049030030002c1004080307004c114011230304a40d0611b56000035848606689a0245098507062621940340c0c590390368400303013082070450f4012221883d0f139036210320141d6101d1246050107900101c009011551441da910010b000c00c0c0207106078805880d803100c0e10b0165480003a8026a404540d0380b08413014061230000c44109540088499031a0021840025240340100d220b1581859500c104440554136a01c0c1115003400480b001d4590381c44502030084044141078a01034618410500301180c45802032041c0020785082820000074a84284d120429044440c804160107018140001001950800c44d05005e81001030700d6008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 406509820 1250 406508570 406508581
    0x90406090c0f091404031d0f12100e241306051008060702060f071b080408010c020f0705150c0f060a0b010e04110307081008030d0b040f050402090a052d 67
    0x1da400c03010b00381031040140b1003030000207600141c40d01e1180e881101f50724145040140014000516034400355000030350200020350100000c100a5500411242d040002c010002039459848202c000320142c11240e400c03004d054110500c203080c0c0d1254042c84480310004055039064190f9038280c274000e060800104090140708820701c5060380c04401c0b03200401482c548040d5620200c1d034060034582c01e0080d20548282079958030441040440e8201003103e0340c550307888243c58000c0140110042c01806008450352054501142c80400c50310000c11035400601018982d20060f846044803580922600545c85403e540c2842107500c40c01c1c010704001681c1c480700002500e07541e1948400d52043e49000e483c440142601000e4071303084030003880e001d40305540b04c080d00d022140d903030b4009402602c00401c20a4090340160032000c006003041c1d9040c8012448542d6020696001b9a4006d60040c205000070b00703c600150720a642c003056001d680340d4124541d03000301c51030180011581151020750000c224 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 406511070 1250 406509820 406509839
    0x60503040b0705031509090f190b1b040519080105070e010e0a051e010216031104060e06030c0d050304050a0b0c0106080601050d0f051609090501060e070e090406090c0f 74
    0x2c1d4481e80da8240a4514503080b01e8441a00010a8400d4400c0e15100003180c0510310803c0a15090507a0a0403682e940c14200d00e607a01800300450304990103003000001800400070345100400c503aa100000038102401c00c0104a5420080480182026000e890008050900b401400c2c0162060f444102d60204410001403140b03c600c401d880c0944d030315140800032a00c1d0702a43c900750021421400c03600c0d42c00440101d00b400c04a58034419402e500300d1020060082018031008410b01c12541002080e070345090f820701407003003141c480da0326401802403a082e074100710f0b8103d10b40a2140c03050724501610b84001030300703003440da82088a90050101d86130106980074859007001c0c10180004000a62405002900390100398100811042047c0854000c1080401c0700140300248007030035220b9961a00210002030032000b40c00d172210b41c200003000030f004100f640040c1c000d0b0003d603079160302c904240c0e080c0502c8010140044850aa4441c0c881002c41c5081244401034001982d0071001140703040743d200c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 406512320 1250 406511070 406511093
    0xd0515010908100f0902100807030e010c0f0e0316060e1305093414010e04090201080c181507023a030c020d060f0608120f1308010606050304 62
    0x2038148960a101030005a40025110b00510010100490100d0303079000d400c805030250542c025000244038041c00403044d0045505441040290b504201c01c602d0040340b182a211440710040128107140b15084000d0b100d0030000000b004c02504961160346d81c0b5003030b50f41b20600b40e07011380000f51301190018168901001c1780641c0c4502c4003400d102a0800c1f110041d1a6451001100881081d24003840000440001c11584025140058262155582c941b4103821180b0224141c005404080780711000e18041c0b03d03020007290103079140f00d0300c0d5464103204a020350011038180c0b88110b100c407249529580c0d80b01450310a07404803d5554071805144180300f0032003201302070b180c0c040405840030b12142903078015054100100b2140120013648034242038039a0001c40c080a500040000340070003e02c03075181c122801d003e401c400c08002c83e83d034034401903840e001d0320141500d8090080140091100011019005480c003160046400307039911030301e807421034020f58003443c081840801080288041e4104c071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 406513570 1250 406512320 406512361
    0x30c0615090515032406120613031b0f02040c05090406121406090604120527030d02030c0604080c010b12010e010b04060b1207090b12161106040f020d02060d05 70
    0x109940e400501c2412072034070709401c91707140070109100050030b90750703130b0361642c00d003248250080e110541000b140d07201d03541001003004c0c0c0c0030900349a21002007604180c809014144c1107486408803054a600708009400c1d03105040040000034070001e80356a4a9100304801001400030304044c03400d0318903005181000c10560b20b0303102e800c00300400a03c100041003040d8055801001b100b03284045000548082c00341128030340512010034008520a01d100d400c000010904501300d030a1624019822a928420841d00f02c001e6000100481d0000d160f0f0806092010b40f410008100b844000021035410f01d0318a80d8480280c1d104c5819580540e0b00784500321810740141c2d8144051810842480054801c804100c0c1e0403090020004002e036220300d071030340301070001ea0410907034501148124800100054481140714803402d001041c940340140d0a41d2044040701d0701401e00c9a9070798680903004a401ca0042e40c010000e44507250042c2c0d00c10009060581c528440040c003820724445060500d880c81c0f50 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 406514820 1250 406513570 406513573
    0x7140f090f010b0c01060b040b0d0e0c030304210206030702060406061d0c03040611040906092f070602071506030308060f031c09030204090303140a0612030c061509051503 75
    0x1480444020850002d05556140786420b9840c0100005540140b0351a40207900411f00807502003086100f02c001031141b44000c0b90b0904c001001482d4068a42100c1014254160301c100404c2188180040c0390103812040265240840b81d0f681c0c000c02c000703600440e80b850044e0040010402000703100d10500c00030b8008400d800070351228160561140d65000344c03c1014001c070203c0020200002500001501d09400b0242c54070747da0741e081130102a201c64007a80c8801806c025440c60002e0740c00e08400d51316481e591000f03000c0801d400700c40200e58490003060350415020840c01c000b0500c458584003801c0900c10001803058913604004004a03005040203100f58090140310385139580000b400820854064198a10198070200580b0b5220103940000c0d08103081072080ca00307054041d403103080c0c2d600415040359070760740d0b0722800c510072100b031401540040e0b00d0a640c20404203108400d030002e140d1180b03c0c00508001c91021001014100358001c003c6140c0701c004000f00349190b08610b070300e810001e40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 406516070 1250 406514820 406514839
    0x120c08190e03072003150a060b0f070204110c070e0f091b090601031508011401060207060203041203050d0e07091a060904050705071205180607080901030c1107140f 72
    0x111007985911071440c0150100c03042515942101d0391044c5080d60200d4028201e50341e0b94800f00315450302040c211210b110840c60440c0000b407943d002e00450b04c0b500c640c00c203400d00d404800c1c0d0030000107103100001d481802000b03120451502c0320800441025000d48605280c60340703401558011b00e60401058854180c014940b495403d07541c4150350059007204803003d0000f6552040101d00070041c054030540714401c4180000740180c41984286e00a0460740080b0340c990380c076040c00b45d0743c0324060302c40c1400503031040100b00810182106e560008500c00e1402c07030316042000c0d000d0b0041c0d03110f141080301d582d0040902044240c0c114442c1e8448116100340f44104058004001141401600303011405540c4070f40c00906554410303021510b500b5407040d100015241c01c1c11000313005030020b003044140d0000046414017245000700a650701141c3c8003c003640b8201100e001180075100480816080c4070241c01d004490450621a00c405000d1443d003020054007210100102001d1500010340144001d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 406517320 1250 406516070 406516091
    0xa0305161d010e1201140a060f0e07050703140307050c0f0105060604050d05120a02030a0e012d121805100203010f031713172a040c120c0819 62
    0xa0a00c00001e80900b0302002d10740c8041c010601c0074a1141102900d0752070f01d1803854101c40e481c95642e00130755207c002000602e44460b019040c414281c064001010043c00026140c03610174001070807164801d2030440d0800f482c410301c0741c1058000f03484500105002003900740c0388035003c0240c001d89440203402805681042c04c04a0440d100303900403280190b006070030036000d00504012282110001200580c0d50781104031000b5201e03000a42410005150300b0521140d540c810b0550041004242814000440d071000b405094000852070b130b40144035a103620703007089120b6440b68203803203100c4a09032002116140b41c041d003021303400441110703614810310042c0040c6a0b260b01d54016240d120301502d90302094104900f50900807240d441002100040020540700f51241e181e280c140341200c01c9940d207604a5442800070041400542c20031400428030001c203150607080010000d4003400e101c2806505101c00105a0301d45038282c40c00b0403400400c0c444006d20008181e00c400516100400052551 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 406518570 1250 406517320 406517357
    0x3151909051005130b010309020d1109010e0103020108060105160b07020d120e1009150e0304060f0e030604170d0203090d020f1908030a0b030609150610170a110a030516 74
    0x2074005116581d5aa4017030b0700790740d010354040c510b29031300149050010780c0c40e0300c0c0124594500c0402280034100b6a0000604a40f0501109050369816101c4101d20307540c0714011500ca41000c83c0258041200001e5000030401091410b8050303c6254040c103003422450030050a072460340012020024030300f41c503028200c000803403803600520500801192900703070350800d00c0020308103200d00303000146005621100140000000e0013125030603110f003510b407048860300740e81045100190f01d8060f042070001800080c01400340701003441d031890040d070910603054016412038004660303040c1a944154543c600042d0101b284c40c50304424103004202a0002400724030b07246d00020002851000044013090b050840c0b80c0000780c840070301500301d414516044446a41e6a20040490380c103814074a4007142080c00c0c20200c0d110201c1c40b41e01d8503940400f0f49050000c802800800707490101d0355940d51184040c0c1031400a20360907003280c2e0702141c2030409041c502c00220b5903001a02c18030210004d0919034a06 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 406519820 1250 406518570 406518589
    0x13081b0c0306160c060f11030702030a0806010e1e0103060b0d091703010b0406030b010c080711150f0f03130f0b040b1f05091003080309030a12020901021203151909051005 75
    0x90054001c1466003854106c50060124240107658942020040000c0c03a50700001500500380682d0b6440d5083d29480d00658170060095481c0c0c2c0c000405088412080da103500140003800410325000075100d039180200c1465800c03010030b150884d0707211013050040c08031004004001220341c00400c1e10315450000301c40380720720840c400d07802419241d03036460085030702800801c1905034100c0c1019a441e040b40c644002e4501c41c40455620032440c0d503060000c450100380a444402c120078540380e2820302c942e403c029080e040108103000300c00084039140001041301d80c03841c03400c80c0320700700e09006030030240340c2141c6c5100700a1810030701512601421900848400741242105c406581802c06500e5a8049144203052900f016001900c00000e000c090180000103180d80f000699034091001d00c402465800c1e0b20655a8580c0180e02008442e088220f841001f540c00282000e1046440c05420000c200180c1c4075204c0302c0c0303d00242c450100903060702c4d8000e1940c410749070406041618107240c0020503800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 406521070 1250 406519820 406519823
    0xa0813030309080f07150605031207050c150a1e090302101b0c060e0a14091008010c12050a05040521040315061a0408030313081b0c0306160c 62
    0x105000900505001c2e50010400541240046640358a0308100d1010369105202c102d5101c003181440701c820307a44610907002522001800f4003541c4003030301c0035110f103900b040301c040c0d03164026170441c07084584e58800c441e03c0c050b00c4840199180c6240d0800030700002107101c0003002032000d02c0291001982c0c40703945081607070f5044603620714604043d1003c0b03c4040b000d074125040744040742e02c83c8060010b0b00c080c040072108643c0d560301e00c0d003a904060014005003031003018010b81083d01100340c145844e101c01079202655001c548140c07551601c10b107007511200c112607000705491075400020b11020f030007041d40c01104290140814101a910b039a601e09400b007201d90f060321088019400019518111002581c000c0c450010780c0c070882c12004010026480350100c040403c042c4004010142020350b401c49088402079410f550341c1b804081000c00e402103007107411840400c000000300524511040c2c0804660f80204110010642031524122000d0040e940b201d00d40b04008050742c4e40001e100f50701e039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 406522320 1250 406521070 406521091
    0x1b030a1b09031a10052707051c050a0b03150604061a1e130801050f01051207061b080d090204050a0b0f041d0105071e050406050406200718110a08 64
    0x16030701d03c1340d04602190541c0009602c502c041101e4880d100c01d007880d05125a284054503103a0f03441da07880a880758800c00b4040c015481c0102618541c01505a120030b600c83d000c24004108440501c0009080c00c000f11301140c0240d002a0500c080c034103041c480d82001e44039800100411500d00088024036005204c070240c081604403140048100484090740e1030801c000748141545529490480d01070281150703901109041e0b10000144e0380b400303516030180c65000380064840c25003400000c4800c41c954803d6480100d030002d6040c0700051015005110855220350000748c0c00c0300903c1080b05448000d40b2071110745041001603042ea80c0c0c1c100d0001000c0c40304a41c00902103d40c070800107847c41c20886514001c0d4a03110402c01d80c9030304042600e10440d00502d50548030051030405583c0e41c0294041c00000074400d1206009550141440d010b0b22600f041c940c0040d16480c2070011b140c010960040081c1c0b01d88901c00041d03120150003035040d101d940310005803c100c1301c01030007408840010490740c200c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 406523570 1250 406522320 406522373
    0xf051b06070206151e0d06060f12140a03080610020312100501120c0e1c0606171603030f080406021201060207061103030f06010c15090602070b090c010c0b1b030a1b0903 74
    0x1040250f80c42340008009034010340c00126030b01c0351000340c100005c150544403840722410050b0024008640001c25592548800350551242014444142c924111600c258481041901020a400044644940e4080200c045c02038140b000040004124511000890381001e1440c0c504540007804140c0c001c0d02a620072502841d483c842141c03504803900050106894540e0100f5109900451210020100b40c221025015880f0404554401c0c070f10001e40014032451441c11618842d880458009000e500f01504101181c0000441100300fa03100c540541d000304001c0003400d03001119142c5581000016608618048401501403807000307042030304100780083d40300d041010044040004412442040020880a2034150300a61006005032103440c104800580c0c8107000180d401c2d0344a8040c0e4540004040d180d442040f0020087c0103c050146545ca2100014900402451082a09040110b4541800004003003c0320081e41981c0412140c4642030001c03030740c018505036401c040340020810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 406524820 1250 406523570 406523573
    0x90d03030e2401030201091205070605030703230709080a03090909050f100f050f0103050c011d04111c020f0f090d02040c080a14070f051b06070206151e0d 68
    0x1c000032600140b220761408a03420700e880c28140c0265040e00e10070b0b20f80300041903c400e24034030410038021004120f9440040148809407141d030165400c0002821f001c00c1208894000c0031b0b042d40c0301846051100c140360308010074654405103000003003c00d031002d04100f59036038400421004440c054044220380b5000c642e010044200664079682e80804181e8060386e685004c290082c006100c1d07901440d508200224100f00e0b90595141d0489074801d0003071280701c17213090040d034083e141c483c4c43c1d80d8011807039064400c0c00d80720342c001c141d0081c4050035600c1d42c5107100c00005078498030142c1c910103042e20600c202c902400180d802c42c0c01032607010030400c0e01c41e03400c1c0000803850054142d00035000380c14050740d0001182c00150031801949481030900c1405001c081e0401e03030140c119001c100042c03500703042d1340343c00303002d40000c1c060a03144101701d0b0081d00308840007514240040d200c0c000180d10000401c14004201031014510300d40441c0c11030707400d0001a00c580000c421803803900d481250200c52000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 406526070 1250 406524820 406524823
    0x50105062416140706090f05030c010828020f07060f18260f09130b0609120a0206190f0309261b011a0603010f090203060622090b06090d03030e 63
    0x100e1000b241204c5070240c0380e00c0000c18650340c5104000381c01091440100e06440c0204280c9950f580c10703034401d1800c0d0b0320b01c41ca8600c65182000595640e803040c0c1c00070750345014035000400c24040c104c0754003580c0c1c10b040d213062811600429403407691a81340c45021039201c0f58980341001e03000d402c640e80c3c1c103c1010345c0c0100c13144c280100b19000c407058000607100d149036107184050521000e0844075003058035040388403482036400c6004002e510110070072000100c0e11f860943c0701b809046600440b0340800e11341d80850410347c8406000b01240c06102c007050309290b88030301e02850459062030140321340441950349032003050040940c80040c8520101018503501c8050035149000d01401e1002e08581d502ca043e540208008850982404008100038000b07003802d000300c81c103ca1610445c3c6140620f0b20035240025000501800d52241d001c121055800310755680c59807440c00800391005805144c50744070707000c4070285145c090060b030301440031a0596440b01403c505180d010308011558240036071119 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 406527320 1250 406526070 406526093
    0x50a0f141005011401031b0302160b0103050606041b050a0f03020d0c0f0923040b03010603080d0b030106050d030816020c03151f0b0a050703020a0c03050105062416 72
    0x4002885101c03020964403020340c200b0390403158600141c18102c0340790401102a103c0c140e01c000c515140790250000b5162296004100d0490b00400c24a1030f111960340d0011441c4003a403056803a41d1080092000c90310303280c800c01c02c01c00384249001c0c101c0c1c00c2c0200041c080e270051190040c10300c54114114105940030760100c5013840c04ad500d00b00280c030070002001e80742d071a1000440c0c0c0001d600041c041595841420039004101c2c803550700b01e00c0140c0e804100320146c0007a080f00303038140d52a044d0000004280301c000d0040340340031682c08913070540444245400c4070442e600241c455944507490901017170700310342101d8104e00802c20500310082c00030340c00ea00d0420311391010394151280c032401c0c8007488d103c21041070044031a070329448e81403000440b4001140106014007040007404020700012940150300401c0c81d18843d0050700c0122045480322245003000d42e1055a00b45d4480703041002e20b1520032414612200c2460700d140800311621a240e40d1800341d002e070a0070a00054606005001658a49 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 406528570 1250 406527320 406527353
    0xf0624030a0b1e0424020c0a0f0203030403050d0906020d030b0d0b060a150509010206061207060c0c0506072010080a1a03060a0204060815010c1e0c060f1704050a0f 72
    0x15421507050a1503c0d182000c14044040658000f17140b24101444142c002c80f680064107e00500a0318001d0311111004080b2030000c0f61700d44801c100000006030240401c6120b07000507260340111918000b8081d003007911035206102094940620311065585210028103c0790f08002c00801d9691050041800303440340e0340000c0c2001c00401310180c0b00c81c2d8080010000c0c02002c2e03096869580f03451090221250111502c01000c1e0080c800a2200754480e00d640f1882902561107424440da440020440740e520450302554102c401481c803080c0d40700e13590340c49030144000751000090070448a0b00108462406464041480d859120340f15101081ca99800031a103c01419203c05041074090840254040d00c0791401103100c0200203100d0a0b203001d41408401d030180c5815012503503503541d041fa6407141800c1d000050280c0740008011444d4444094040c0560f40c440d510b1508000001401d461440c0c42d070828000954402c00c00015030114042c21401d50151b1520024846464801c0802404601 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 406529820 1250 406528570 406528621
    0x60906060b0d0b0d050c0907090f0605042d06180b2106061c0c090b0d050708011403071202150d0203100510050304020f120f0624030a0b 60
    0x3008109000204000c200d100c0751500304000c100da824051005145864001600c580c000b003175001d1580c203040d1582ca60240461403c03041640d01d4071710703d106100040d00000700098010400f8070004002c11540440b51801407154111180d07005214100c11445002c0d80c401c00546d28104610101004482006048000c080d02c0e00c1da0b00b013444d05882c0358503111500c01d1122503040441c03107908188046684c000760303080c0c005594072080d2100d6005007080c200c2c50020000c40e40c0c40012111141406040d1000a1f100e000c01c0c5414500002003071a40181c115421511464010b00080d980c0064010100c030300c080c070505200d107100e00004003003c25000d034510241000090410800c20300394001c5100d048800c1c0e601c2e140705d407110140814000450740310303400708908101040251401c4000120326150041c0400c0b03905180200250412210100c0720301c079940800140b140071480000a049180711002a1125844001c0000303541d8800300b1802801107840350000c280c40300c0c0c0d40c04d00351001c100002e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 406531070 1250 406529820 406529831
    0xe01020f0d030203040218010b1b0703020409030203030411030d0c0312060506030c0d050108030708030a0b031024051504061101150308091c110f0105130906083007060906 75
    0x41002e070213540100c2d012486100c00d00c2100c407c01001c0d1459074143d9a0040449003091032095000034100b80c0d00501003258481c101d00000140d17105d0103081032080c842d42c0550307127900381450440510b000c0c0c4903480b44280c115100c0c0c050382c1b036801242c0c201030f503426103407030717040071019070380c204000c0c1081d400c100d4106000000300582412190300406490400c01410442aa6128642c6480c1e000c0d585005242d90350800124000e0b88030385d080405900c038000e0a80d808100d41c180d14030700721894041e01007810b440c0000305202044c4000800c01c002c11007543c800c0030b86501d0400d1500c1e284140d0082c0010312000c1d2404621403102540311004403544d81400160098680c1020342e0260061490103115020b18070500260f4440e4000640c440d0754054000c100301603072720080107080113112000740d0402c042032104240003091004424000c0640300c000140860400291034201000299201a03c0c074200c0045000b40c0601c14100b0b034801561003100c0d84511052810030302410403407401416603811310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 406532320 1250 406531070 406531093
    0x303210204090e0c0a06020c0a0b0c030c0601170f011803081b030a05180307020f060a12090b060301050105010813020d030509060a0e0111070e040803060613090608060a0b100e01020f 80
    0x501c461850300490305e0b0808140d4030f11040b0b075140280e01c040d03504180380042c04c1240001040241282c01c0014094074208004240c5613880e0035001d80c82803400100240b03c88104100500060707030a40390a40c001e00010309620001301000000c0e00c001802c00070b02000050855802c083c0c5848c82c0d04901101c40d40c0c908090b40e4100c0980010365804034074890000307015180c1e000000885200d113078003a03c2520404540c100708103041d0061380b0700300f0501042c011003158503072061003210f101c60701c145101069803c2c508140350840c0d4050700000d05101f114402c3c000c6c850394814090220680c111079071002d68801c1d18044915000b2501e180303810105c08602d9501094104061491144084e07a4400011075402d00d456503502039846087d0500050a001c1000304114800a503441031010308404e142440e00b030b4021281c1000d59121a02c01c6981d440140000b0006101c10f58010400150a001c603c0c0c000d00012461103604901c1c0f81405041c52907152207900900420094510142c00d0750100441c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 406533570 1250 406532320 406532323
    0xc0c0607020c040f051e07030e010f0e0f060f150109050409031d0306010510050c010902120d0207060302030c0a0804020d080309011a041505120a29100303210204090e 73
    0x203154543c4214200403030900c1ea0944c501c2001d1060f0410031854241b0400510580c00c04000640004201a1602d85985890b0024040d00c40c42040624001400e09051500607081100208860034230f03411038000c0c044104041d447d07141e00101c07038128960300340041d034005a58041031640b005820071f0400035080141038115040302d0f64804d1042c1302c03014442186003055240d036802d004a0740d01071080c406080c4124810340150202042c42e0300000740c4014140c0024280d01800aa07210307190344040a510807481d814840f2034001d1001d41415421801c0040c441240d034000c45070303484108071074003002400b07554078403417043c0301942c01c91001e542e2410643d000c01c0c06031100c000d81c07180d060703c01d40394041a81040e229a441030032094a80102071424a010090021012040030042d0310807e10001c011864519280003100030001ea0000d9104e91240d1120a08000034803e0440401c56041000030981040f26a60010141107025040000c1c039010b400c020f0185403c1100031034540070305154040790 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 406534820 1250 406533570 406533583
    0x10120617190b070c05010b060403390e0702031b01050a0e0a0f0f0c030b15040b1212090d0503180f0306041703040305040308030a060302150717030c0c060702 69
    0x9401a81c0000d603000001106034445030a00809080b0b1860001d0802d0f442910203c002038421000800d540d680c000010382d05070410f8000ba290795200e1500481810f88a075038204250415103081d031440c0401c500c001e207042e13110784108024001c2c00c40000d44410720900c1200c1c42c20420801d501000701c1c13105043c500074202191050605454482011200b00c40040c0c011000390b40400841c80b1003000b50f44040e800050084201c4031110b6048000c00020090201d4511810044c203a0315860340e1000200010345440c82c60441c00703564440c5560104038004221010031200c02012103599984900c00306038000e8807060042c240b80004501084a90003219581c0390b154000c6450040d034028403410161541c0c1c081e10b004001229485402002514000c050766000e4003c0c101036007025a2901ca041e0140e00441c1d0000c4959500c910a10461520001c01000800300700013103400c00d012907658211440101d01c0c8450b6214001c00010440c081ca14201c604c04c0550405a42d014244440082d40d101c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 406536070 1250 406534820 406534859
    0x908040b130f06051204110a05030d08040302010b090103120315090e030c010f02031303030f02070c091b0819180204110301061b080912010b030d2003090906101206 72
    0xb210b64100041041c81030003a502e10740d02c060503002e8070341c45640e10084c5403242141d50b81d400c0881d08070300050756501804141200c6610b81c58100395890700b443c0080c01c4807882c82e00da0b84a08035000040c008924503140002d021b002030b00b030000c1d40104a00040d1002601544803020041c10240302a9904d4400700180110034041c0c4024400450015000700690000300e440c9080713417030315220b0100400c0c0710b600803000d160840400140b4102c41c5031929072100415422002ca0151220b200e051081e8083c09007030080b031468541222582805e400707030650701c8950201c5140081e01d40500791306150855030150042c9500610030021104000b0482140c0d030000d1040e0000700d00344038003801c1001c0300404c50716000ea6105400d140303084010ba041140e0440b00d41c1c0c21040315940c40003074422513102007000070b14074246030311105000318200d00c030801c0801c11916105402d400c10300480c42240c843c28070340c40d008001101ea5401c44110382034205d030031000304139120070802d0070036400060315489070b4203101c07109 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 406537320 1250 406536070 406536089
    0x90703051002030124211b0f050a0c1104050a0519060501092c0403030b150c06012108031f141e0613090203070f110c040908040b13 58
    0x400610301c069080780024458007058403242e01124403224004c8103da14082450f0a001071090140070300313803944000550900d51025642c04406a00c59060315500f01d0000c01c0c3d1030806001d42d02080300034564003507510b03c0302c00e1283d45441c0008101c40d02421003d403840280c001c10040c5400e92110014190a0307505c041541c3d0030101c0c1d120200c003140a50b0054170010f844985a080c41c18014020030140601218002032005540d0040040818605401076003c3c2d5404030700d20072600c0800c404c40083c0082c4041c40e84041209400e50b200201e009411186035903e0300c13685c410200a50b6040099120009000b06800010031800b2402c2c41081344c0b000d024860541241500d07140205e004412076501154840008045d070b0a587d00c5101c5210b104e240007410712030414803c0388600d00c04d10305580203400010b8010081104440d031100e00d030030b5141c0552a001041100801d08151030f040ea0340c500e0b902854698043e4002d0260180c102e60040002c1170790301d99544c00c50031446800a40328013405542 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 406538570 1250 406537320 406537333
    0x9101b0809071512090212062d0a20130e06040e0309040b030f0106060201020909060f06030f040c0f06080f0108011506270605120105150906091809070305 68
    0x60352001402d001500c02400c03800c0c1c0440d02160064600100a0102414140d154214400140c41d1607a0f02e003101da0080c00145214180307180041c07500070b0a00020910b10919a03e200da034001802c2c001d42e003004c025040000c03041ea1108003106141403409041e01410301c0000d0100440da91041d1082c00c6504648a28100351117460400c1700b030315030030f0032443d10b10380c82404001614582544400c0100304001c0445000c12031020000303080d101a5481400940d50214880c4410300340ba045040d4011070448490000015400010300507010180040012000f45c0b00040c00f084000740b8102d000e807074482c1e54690503030340c1c80d0401081c2890072280d4032a1181c0e01000003c0000050084600e183d8001c1d5008204c84d040c40c0e400c8070039281204074111982c081c2e5040343d4240101445c08400381c11690f40c0c0300e9a42c800c0f660791892100b8180c0c402c40c05050601004080d0010314016a042900d040307500681d12001c070f000080c0c2030b03607501040c941405030031400e00c0321102000a20b401203c0c481c4060b0740c003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 406539820 1250 406538570 406538581
    0x11120714041a0f0f031204060e0d0b01060804030e031b01020f010603020907050d02040f3302060a05060f030615040b010c0b041b1a27010c080309101b08 67
    0x15100780344401d16600c082015199034a01c3c081e280d0849000d0050300c0100c69038035420009181c85030740b52204a46030400101030010640c0980c05101c40c00c41038400182c0312541d9940c518400c8014440d00e000c00050034042010540316200140a18800804503070700740c1456107448100340040c00806015100341910180f000f2010700403001140c1e0010501200d507039030070400f55815400181d0080465500b0000402d184400320712000c05004a1120410700c0c2440e148542c03803404403001e03000c03072881881c61440d818503400a02258021400bc02c023140c0c0d0380702c84001c121280103da40695150240c5010803407001002c003d040b8950004540610404003c6001503d100c00d00c51170182407041013000042c003080e0600012140741d04017401240c1c4d455920100d00c00c3d0f01004007400e54081c440003c1e0065110814100c0108031070003001040c5184820f50f002808210100c040145003000200c005034450000380000540024210024845007140c207541e0307490a68124074a0f404175156801140303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 406541070 1250 406539820 406539829
    0x708010522111c08030103060b190b0d0f0e0307060b190303020a0206070203070f060804120305251209060e070605040501200c0a06050c01140702031611120714 70
    0x103205542001000b09000424010321001039842c0c40c074a546400c12501400c009004000111300035401481d002a0100d0500304200d55541002c422003a041481102441428891401c50b500c50b80010800260701400c0301003500640184961510103000c0801c000051004980050080750000c40343d00c000a40480501c00080001d8080500141c0c00740c030000c401800c014000341162400202242c101c035983e40c41c0d422170144290800d20000e0803800c240020045400c3c1101c0b0072001500b800e00c036a02e440a261b00c5111351407a1180b0900c0b440c0765412210500400300006541801001882803592030708280c0003030464070544140911410700d00046c0c0c544642c00b5034041c0d1304165140c600d4000c2d14034502c0c020f42d0900c481c50150b805852182070701139a544103008001d21507038458580b11803504902c642110104849854017202000c02c011460780e0105c1141c2c4481f107280b88803600d40d101c81c01d110a15941a080301c58008001c074880b00780842c0b00261010466403540d4104540100ca6020702 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 406542320 1250 406541070 406541131
    0x3080a030b03030c0309040f0615271a03041703282003090102040b040603090515070e120f0709020405090c0f090909010b10080a0b010c051c050c07080105 68
    0x44c4080c1d0020f102010042c81c058001c0c4004030144100890196210640341e4400702801c41c114011403045100f00c20008680e1081d162810008007078654030600c0d00c030f444880c10090101800110b000040054200202c10903006d6203241200e808944914140d116600d087d1b10f408900c501c0301103504518803104101e0b001e946007828040e181d00d4410480c81c00086441d41020b4403101e030390754003804081903800640004e40020041540d01103903520450600b103082441581c03412501051140802000a80264210681d4401655114032460004000b10700304038903032280c0c268501514400107a00041d540240064400403112129035031500c0f01030080c588160034882c4c0b0040340a00904c1c4240c546900750545c00806070b0000308455890350001078891140700360000c04283d40000740240074400b4454854548800e00301403c40c036103907031989903440c2d10f44200d041741512040c84a690882c4188191079070380301c6030001c0f0b46180341c94070748042c064071080b5040c40c030741c07509031b510350300c1341c0c0b085140303c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 406543570 1250 406542320 406542337
    0x307050607081602062701080a020309070302060c0708070f0e0c0a0906031e091a010603090b13050708060a023f06043207020f1c140403080a030b0303 66
    0x20b49290012260744100c0300c8aa0600c10780e840171091180101010b80da0286203440e800441098400e20034110000d0400040a804000600d01c140100411648006022411340e42c0442e8059218104d071a0203030314004c0c0607000461140202c640004e01454000c5120090701c00c0c1c2c40740c24010303903282003140c005405406156400030740340b210100b060034020b5104610f1200c0359030a150f81c01244c0c00d0a49d0a48110a5007198071518800040800c00d02d0000110b015045503d028411000241c94143d0109409030a94021601040ca00000c2060410019000741980c9081c2c603031510b01603038014000d402c21001219041c44110a00130300c081c00100340a04286e1002600c0b005101500b421a2041c0c0700070440d54010b03582d2061307088c80e03c103401100e4110280071302c0300c40042c02c04e43c10290202e8134050030303d00031b65001e103150903482103002c10034426a4540406418500100030300880c0d0380602d1001c044042035000401006005483c001003000d84919201032040d003804a040c980d0303d1082c0040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 406544820 1250 406543570 406543583
    0xf06160f05011116081303060203090a110a230a0e0f09070f0e0f09070f080c1c030903020d05070902070f03020606010908070b1602130b0112110d0c110a0b01050307050607 75
    0x34400004290001030146d158400c0342d041141500e0342d8a0008907401619800340300d41c0100b10f83c10820605940d5980006400d80b0800c00043c54600c41043d100c1002c0c17608a035051794001d495169445203020640180707a107180750515818080c141c0300d0042c40070f13150394802c0e014085000c2564046840714004640540b103110f01aa614900c28442d60000540390820600444500041188000b940d5070060082100944486540041000f4140c0700d614031034048810301c250003902181d0403103e0002100d0b01621010540020391803c07604020064203c00c5005202040800c1400180c65841c18902d109400b15004e9440d80001940c02090522071240340e58461a410701c480b6814101824400f05d480c41070321084079055000806641d644401040d40c0740d030b2a00c51071130561f4010014160300740c142004001d14401d80d0440d81061080c0980f00140540f140c0c04911410b208501090400803800c1c02e032621582185010715802600f031091a122344103030030300401d140c50980b040340c104560008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 406546070 1250 406544820 406544857
    0xb04020402030a020705010c050c0f0619020a1b0f02100c0b0402010f110601080f07050604120305090604030f050d021002120a050702030c0601032a050603060f06160f050111 76
    0x508100c00782d031004210b1455a074003804000700040d03007401111940c1105460b100d07214141801442d180a64951182095038005030600c0b014a625007120002c015400f1005651422041c4c03064605414000b51004a1001350f5021802d104842c0550203565108035010000c140d168007048480480800e4081d00343c100180c0810015030250034145407030116030401e15100c54903020302d83c2c208842680620102c2c1c0005900760504681841481c1c058041111b00d40e003080e003000101c42004444c1d89000b0300f804800280448142d42d11015a0b0081d5400000b80e602858a440c090b41c503400e21220341c00c00351254454140b407900c140d002740c2e9401011050301c143c0035910301141e44064000507002906602081106240d004e0742440058082d50040505103c92101c60f201c1c0408480d60003009104035604040c00d10065960000b12a08040104c444075500c080c0040003070f241d40701c0c241c82006c015848400500403c0180561000c885029800030000001a041643d150b07101d94000b0341042c03012034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 406547320 1250 406546070 406546073
    0x507080c13020c060f0a0b0607050a020306010801061d07170903070204111821030f04030b06030706050a0806130e07060207050904110108040f02032b140301170307120c1a040b04 78
    0x6605d0140c2c400c00c800c5010405c00e40341004103041e80e001c001d09071015000100c5803001d5003801c0151500403c4840002c0103038a00d0100f010400709000c0301c0e40030002101d00041801c40e4410070b10700c480e281e0031000c4182d040c20000035036503982e403020004a00507030401c2016903080d0292030a4030b441c07141d01c00e10544548141820000851454404000b080c16031800d02254000c0c00c002034a0300101c450a0b1035a0303282181800c9402403002041c1030f00c20380c401801800125440381c140c07050603400741001e441e00d07107640340016110391411040b001303400c1c41c2c01d490700030301e40740019488121141c1c0c0d020781e4650750711182488404601103501501c043c2d4500d00c5049207503c501c2000343d0040c020761002e0315943d031681c0020301380744014492102400480d01e900d0a00b141c000001030f6502e0f800e041910865201d1402c054a0b0b010502c40e20029886038040101c1d4a00140116032060f50300500200303640301c011030040c0881031102401e640110220b82141400c2c0140644c460145400151615460b51759 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 406548570 1250 406547320 406547341
    0x1b1e090c09141201021608041a0a023f1306030b210a0f1505010b0a09061803020603010f08120c1c030b0d0b0f0c07020108160c0507080c13020c06 64
    0x100d02c0e10f4440c643d82049564440300c1c052081d000341c680b0869845550701d161004203d00144030402c2a5050310b020802c5038604c1d900016080c86242800140000c242d1880c4078040c400348134400c041100746d9400ca065a181303090180101060351000d400c141e07031603072691012011203c3c0001058fc0090b040b40500364412805003900003010510000c03030344100011358440490682007030040b101c0c0d00e4041054130054a841c000c40d40908164622a4117202a10350014000803c510858003804002071010120040010700f60000e03607005803e0301c4e56035a40d0186511400e4080c841e50b8214003500030008a1501c128044416007100c001c01005c881400800881450081d0201d24040c0340d0f9502e080206510b54140405149002e50b40603869850108940410310074002c242d1600c6440401c5a180107030b030400916600711802e1070b00c92400c8000200281d0b4403402540c0c0260052050903800202d002c00003488400c49002030b00c1101540524a0354503003640101c0b105044240c01c920000703055001e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 406549820 1250 406548570 406548589
    0xd02100f091d0c072f0a05100516021201090f0204060510050712020309040e0a1106030105030d030207080d02030f091903140702012a02011806020303041b1e090c0914 73
    0x40d152120008900e035880b0080341e2412880d400c4c800201c03032080141740c0f6000c000c400040c201030300c0490b000e42134000c0c02409407059415411051043c2d6101000359240e05001c81c4800340400000c1203040034500308a112410603240403072149050400200302410100000d07902802117480da1404e2004541d0340d2820f04080b001e1100440c03105018140c3c0969440c010901d15620305070140003000404c1c00d000342400224504035002c0c000801c01000542c40020726180e503030b0403a00c3c0050f1580114035101c10540b10700c60032001410300200a000e801104402074038014203004088401300030a8021407901e52000800140201d068600f80540e00d004100c01445030a1052600300551020b1941e0009039108400403d0142d0000c070b84044110b50b003041d410380c030312040c010500e0340d001e2600a00a50341d2000520003000c82c00d451400101c554079204424000d00300302110610800c80e180e503211440d421510501c0005420044500b40d8640620700c0f40e010750b442d242c1d80440b81c441200c01e1001180 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 406551070 1250 406549820 406549823
    0x1e05070b0d06050321072405041509030f030c0e0a0f0501020607030c0206060108090a0609110a0504020c060403031e18030f05070f12110316030908031201030201030b0d02100f091d0c07 81
    0xa84002c0b801004808040d4110695102000000d00b4142400e01080d8802e02b4801d800394079240600c0800840d4000c410000582d616203000305103448125422a1811262484607400c003021010216070b400800314803800f40c0d0000c6e800c6441c1556442c000310280d5611081c0d240140c1c0144003c541caa52040a03550f07400070b0f4540480b0004a81a40e4080440704400d000740e40c09210504054030602d001ca500c03400500b0111801e5041c5803880c80440e8540d0800f900041c00e0691300c1800724101c1c1d14040203000d050b4480394040081e84030b0304c8055204540c9211040b40003d03001445000c0c3e841c0604c0598600c55009400c09420484075070320620400201e61456040c0819049001c0c15440708100622120303500c2c03d400e042c0305111f8580688240441d4018581c00d4009104840304070b40b001003103604603902441c011908003060004514440d03100003003c0e4200c074400001d0540e040c4c10011081c80503400c0c0c0c1e110b801c01a81d0b0101409880c0c604180c070158070310310001046591400001802806 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 406552320 1250 406551070 406551083
    0x506160f03030e062818020619030b040e1b011404030c290a05090105040e01030f0b010504050c0f0f0405030f10271e05070b0d0605032107 61
    0x100203448030404005000400c4001948818441d0420181404070907080744144040c0c91020304150341000c5031841e4800800c1c000daa89032000024014600c0c0180c200c0d68010f05416a603040801400840c0d13107030b181d04d072070229050513464030850800344148800c2c000e402e405040301191ba000e00181c00c05a1204c014100310600301c4900350742c0c1a200040008505c20200c14054a20786000c00340c40e402428600d03602e80d28084442041048060111a140003851400d55598400c880058403a4083c42c3c004408000b0044004410004c00d4031412090902070005014140e130303a60704010507250b0807100c100400100b442851020b400c40070281c801030007031100c2e09003000d81b076401080ca8401d5400d4245925403100d064400001c0c13061046982d400380701c0004201040b100b1841c118449100c0100805c00401c0225051b400282e112070007080c6a44031050340d9450303a0340e00903140c3c9034000c080558165403502100181c140b80000c0c03007421084070302c0800d407480000b08804071101d400c4003c00b9200d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 406553570 1250 406552320 406552357
    0x80402040b0a090f050603030c070314030c0a030801080c0f010e011404030b0a0219020303041e05100e03030108010b0a050a061b0f030f260606030703060807030533010506 75
    0xd95030381c1030900d01030f0039182400265440c880c1c503c1419150003600389402a00100440304e000c1030041010416a41c02c990f4a44880e184c020446207544603907000318049000f00c01418080640c840321490484000300c003242e229501007410040c1260b0384c2034640780480c01003014010194001c8607605001da039242ca182d0700702592a1a2851005401c4034041401a8009401c3c20150443c2880c0400e124a51000750b0a41c5401d544c0c807003544d14819800e00010480c3c04201d0200103040000010100c48050300b0b12190342072480d000ea0b41e410a02900a6139400c0c40d000502d00d0810219603401c83d2801000350701960324100c0156220f003c90100e400100403030b40c03599804075441c5090701c0748a03840391380c0301d50407108803401c0140704001c140d0412a0701054400400710000399001c0154001c1012201c0da0780c1da0b142d0f13080039801065580d1168038107008484000051200200381c0c83d800c0c0c1c1c240d140e80450345401070080020b40c9441b10489810612100c0180401e0a114015040540208451850 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 406554820 1250 406553570 406553591
    0x5070816081902070609030801060804081213140a110102010c0818011d0c01090f140909011d0307021305100306020901020c041415010f0c0b090c090c070606050102120a08040204 78
    0x2d80e8013050083d9841602c030a4110205984801014010131152401840310308007503581c110680305847d000340032201554007040c01440d151109260f91036010900001c02c80380c9004040c1c490082c02c50076110b1441101d0000b0aa5006000f400215031495480e44019aa20380002c030b441480118920f0b0309642e00d4101d0b01c0022000e04d0b0901010040c800200b0f60340e00ba0380c00043c00c080150304202001282d24204020b0070b2800d800950311400d049821041d6030b6610315a29004012644142032181114030006034402404402041c0b4503009440034508100d0244d0307111300b07484082d560700c405035855030410808a42c442c0c1c080c20a511052054030300058000300050283c0e500ca82c1c101d80548904014014000b0030030184280e112000c0c00d12480b0040e0307052010b82000600f66001e4000045c03240021310070307907080c0640b0303586081c02800060744c1c1c03d1510040002b40c00c08601107410f1454504003003010342c00068420010140e401046150100b15030044904c0940580f00700d0308152103503684070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 406556070 1250 406554820 406554871
    0x7080d0905011d0411040f1e03030c1b1203110601030f081c05070e120d0f140f0307050702100801080a12110601170712080f0304050a21030507081608 66
    0x2c0308a01c0c801743c40d1303251414111000060351890f03001c002464020b2010b07080c21010f00c07403210122501800c180d4451442402e000002c0d921031080304280499210010552620030f0104021180c045c1d80d841c004a4a071404565403900c0030f000180504a10000c1040020b003813000909042041480203030b01c503268959100b0548401341c0700d250100e040c042d0030f50340380c0c1001ca06080052210400421040c142a100a80140e003c1107848003000010f03400c4240d44e9181104498980c2a46207850740d40385420302009002c1d820451080780b040b40e82681480007503214085440c1070301c5803038014140c01035150340d1310030800c01ca034400c41c0306101e004107100c000c10780d003071140600074500107452107103e60100c142d6504000720b582101051031205680100450107440030b03150031030554100641d8030389860410750304d451540000105104200c0c8460440300c009040d0402c8440b120352410301590b00c3d00d003030035101100200e40750381c808068443c103500810b11841e8026041044210400c014101044070382 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 406557320 1250 406556070 406556081
    0xc07030b25030501210c060e04060b0705010911060f160c030506040302061006050c0718110f0705060c0414010309060e070b0301140f0d11130e010e07080d0905011d04 73
    0x49000c640d583c001004440b4041030081d0252641c020102007081165446052002e19030040c40208456030f2030755804c0c0e40b142c0d88590040d2050403001d50b01c1c0e0305145041406841303803d008880040354250500c83c1e40c00c100081e51404c48500c99040c5c04c1a01c60040304005000c6403800f5181a182004000041401409a01c0c01903000390f000d0101c5191802c10002043e903580d0102040090070480e2845024010510905403440c030f41c0c6a01504100c0904a005407010343d14038040364900013419000c1c55100e00043c034030f5030307c42c2d03050324225035558861485034000c5d8495a2510040200034072506d6129500c10301c500c51182c01d0006c1c482c0d014440701c80c60018503801c03e503643d150000c01403100c0062482c0047c0c5000307044480d04016102100420032039100d200004040d4600318034101866034458992880784540340c00704000b503440c100a071a019010b412010700e4180541600443c0da418045140305400506881e20030740c261900e4011a84a442c2401101d600701c003001d0500c00301da9450059 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 406558570 1250 406557320 406557391
    0x10c0807020f130b01031a0a031e0605070c110114040905040f121d030f031603030209041503020111061b07030509180105010f0513060e04020c0d020f070b0c07030b 72
    0x44113841407001408480c2c0b001d0a4013030004841d04071400d80d640344d6804806403507000450091960600424440600c0c44403001013286081608000c2a107502501545036107000c3e804400d0703540d66200c01510115800061040044001c02090003c10902e800070360700244a00000000290b40e40c880052000b540c6418600007441104500c01d03014140d9082144404101c0c05445c0403036018056543d40d2041d901107904020a00045605050080d41a180d1000014005022444540c001c203412520580401c03400300d081222520344000d800079240340704035180a0b004544407000c2d044280950071020341101000820070400b8113544405013801109410341c0300007612541441c0014215007a1000c0810400800740706400701d03800101030100c210ba48505101c0d40940d41d1402050192040c04011401881105503806a103036001420711070482006050307803038240d1100d2004215201c0c0319000d01560340076601c2840131840a0b80c845130000c880040805658104640b2500c068150982 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 406559820 1250 406558570 406558609
    0x10512040602090a0503011814071203090501030e15011a0c1203010e070507080304060f140f070305160207140102070e040803060315370f021c0b010c0807020f 70
    0x112201141404056000a400c0480c02448100203074070041902050b4064040e002012400004027100300038020000588000c0005401032401b50401404151103481500d0010f480d25034080c68205021407141901e011058a591340390b4a06080e01c0d0008999549800101c24200a2480d856404124144141c03000c030358825120b40c501f20b5450308002c40181a5000d201d02081507000042012044990060f400780002455155101c1420010562909a840d007031410900b400303940c0c0b00508c0954842c2070741380e070184480d80e01d02c0c0f40c01071583d440c001641c015074030040f010b01402258a50a144a40040c8125203515540f00900e81c0e00740d03c261401e41d040d000c00810701841341004d202c0c00000c407501d50740403807140c10aa082e030342600701c68640548081c0001401c02c0e0740403c403030340031140c05074030b00006021100340480040000d5001c50030703414103001858907411492021b4000c103018064142c4415652030200c0e1030305007030b0b0b5011034012030b4403201d8112041280c1c0d0b0ba03540080441c000020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 406561070 1250 406559820 406559827
    0x90415110d051006020f0a03111203090a060e0f0d08180129010302090616020103110c0c01081e0103120e0d0c0509070914010309020f1c210f0e010512040602 69
    0x80103076241c3c160081c0b001c6400a00c40e400c1c44840004c0d24030641d55051070200150310501003298140480c3c1c050b00003012100101740403408100081c8526903d002c1ea50800118030011089036a403080c880c4410416042280342c1420b06011f4408a640308004844040d00318031008c01080c01c491040b40c110411076004925040c0c84001c40300b1b852404034080c02d0862030980c0500004181d40039400c0243d51f803001d00840241103901c2900024401001e5040b91030310b030004000d50a448403404882c042c0041c80050010303c401b2914070102d05202c07a4158881790590030b5454035610390384558118420300c2030341501d02c00d1688661040000e00740c0242030b00007003507043c48200325803030901522150030014034543c01d00030501c40001da0201c10f03000742000a0b9800700c40c4046014150f5a00295a0007a00544200c00082401724901e1940d03201d800000b41c500d007a501000c0e020301c8545600c0001403e02c0038020000e03030040110805c461030505009040c510701440390020f0b00c0e02198200c030100e4011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 406562320 1250 406561070 406561081
    0x307030305031b0c060412051207080115030203010308090f190b0a030c030902130c1205040605070917031e12190b0409110906040603020909151302090415110d05 71
    0x8407908001d0390402e64484c0741050101080c2e6a40c400603001030b0032406d20384810f406650185084604078041c0b011009000d1611120290000c1f0702481140c0b25007050804440c0c1d480e20910840341a07a074400c04032800c0085101c140513041910401701500800301881c140d07852060745095500405031001c070a60380d0382900720001d042c0c402001660060500340340c02000140d8400c03e0703490581e00080000a04202c0010040b600b90f004040d030001c100b45002c081c40103108803508414450411920b407004850b0ba00c406031100d10602d1109100180c1045c04422181e9400c290000781020690481604000240801c211188002c0d100344080d0301c1c0c900705402e5081c84500481c10700b003004035001c0150040580f00c60100c9203104a0181c031070742e4910001841d40d907480d0b0184001e95000382c00d0496a1821112166540140845c995121182c080c0080c05400c2c03480707900c020440d405051030000e500c0310398800500c0071640440f0452580c4403a51250b0342d044d24009421941004403000c142c81c10701 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 406563570 1250 406562320 406562341
    0xa0b160818032a121f0b04020a020102040f080705010c0b0a1119140a0914031e06070210051605090f060a0903020f030106030b220b04030f0e1906030b0f030703030503 73
    0x2d4a40c0c0b280607540004c48004450004295003104440f10111103041240c5114400010405900b09075407040c40801c5a950b01c1c1e078154054000e03500c2183d072109817540c9482c00540e80345d00d24442c003800101000c12040c00034000b5070382580c100702c0790080841c6400041e003d250880c0c00c4080c40c230f280704060307a1801e05066800001d192881e00c41b85000c6180c0080c0c07000042c4802a079020b42e008003c0300c005442d440e500c2c01c001c445c6600d00241c8680c440423101d4844135880b0ba0041d1000070052244040b4140c00d000d192007000c9c041c000c8030250707c040c500c540c401035406410803002e85170300c1660384003800345949601e8000c244190550341d07804e000380d06507c104240740d00410901740c080c1e07240a01c1800021241300982e42c005468800c500d4961503549080c0301c42e2504210000c2003402c1d03501c103000405800c1040010381e80683d0300c0b24642d80d010305041c031250910340d445502c0c0404402c10308105050180e442900f07541005000310a030582944007191800034540d1044001490000030454203045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 406564820 1250 406563570 406563643
    0x70c03030b4b0103020c0703140f070608010605040911070b0907090e03071e15020c150601030e100203180703140111030f0103030e01091509050a0b16081803 69
    0x300001004114201c00b42c0c0600d07600e140c942c1241410350004110002000c10000c0000441d07220446820f554100d407036441d1601d00e10074210a0520a01e0000306246d17005d04070f0f0b54162101c0d5541c1c0b508185c134040456001e00b0035000c1c903083c0004100004c2020880c203401052003044500000c120062410806008440070340071310308441c0e0000c0c01850009425100500340541e440404910900004e0904240d40e8809441d0040d00324400200c00c0018400070841079404c0113150080c91036039946c6001582a140015051020b941065002e45890300703082d8080e5401c80794060001544804041c022031034180581c000740c40300d07150a00b9207024404240505148907141481c1d45040d0306181401020245040c00010107000c550301000603103134401d104410080490395900b102904024001902d8410310340640d6000b99050038002c203a00320850100c400042c2004008540c0000790780301c10303c01e50801845502c03403050311600c0b00c0d00c1e5501003082c140701f851b62402100e402c07045104520744c11503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 406566070 1250 406564820 406564909
    0x20c0307050a05100915200307020708010b0d050a06050901060906030b010801061e12110d20090c0d0506060403020301060305061905010605030106030911030111040602071d070c03030b 81
    0x6040151440c000303510101e0400e10009103540c04900c1d5481f484207210071800107281142512004010000c0300b907800170701e100490341039200800110010809002d18040042e40151565000480001c0040d51742c0d84820303840780300072000003009620341102000769040f5a01c00c1e580209401c4c0140280d8100b032041100a00e00c0508031a2100807103640c031032016886211781904001d44c5a20341f8184101401c881140380710007001c030484640e00d41390a09401009103610001150100c11080342d0303045c16081d407801b45290048150400504c0f00c03007000070746001008580c000e40244070010058400340a030002640c41180540203e02e440018913201d455142c0320440d03140d00b010700410059802c00201d03810b42d002484c010074040c000e8140704c00302441d8841211b40541ca00340342c0c1e40720b000d880c00241081d910140e0a46071055610380c224800c50318110320040428950b48041482c081c001d50171055514428280072800c1105030000403a50140c1e0200040c01600c66940a41040d0b65002c40ea10740c0d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 406567320 1250 406566070 406566103
    0x11203021c17041b0f060e030a020a230907081902070206030c0d180c0515251a0106020705011e0801090506040b091e0112051002030a020c0307050a05 66
    0x141440701004000089820030103810b41c84410100d03090082051141210707211510000b80d1140c2d880b030740300d4400106441200c0002d100c82c05951442d240215045481a0b0005c200900f120304000306800f8000007291545400fa5100001000079210f032004240710709a99200c0b810946003401a45903242181204001003c1c410481100140d03103d0302a00e4001c02d8500420761108910a01000186500c1c1610b135880c481e145c1c00c0c80104440c403a80c40045d0f6000351240882e5102c5520158920b001d501054214004189010102c40d4980d10b40301d00001d00815601144200c41a84803d03980000e8020b40016084800280188c1d6000321840c250040600b0601042940300c00f4000c0c0051018002d24041070f4a80b00807441d280e48a0f0010401c608000b8058032361070402c6468006050800b5400c041d46c106a60700000e42c540d800000621126000005030032030062171382d0504000e510003407441044a6007803100c02001441000982003a0b84505c0c02401d01400c82d0800c40e203800c40c0c001642014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 406568570 1250 406567320 406567363
    0x705011404030f140c0a05061609030c030f060b2d0603161409100507020f0301020705030d1e0615020601090203130f08040e04030c060524010c021801120302 69
    0x1d0f8040e4001c1411400e51401801041045800c41e102e40304460058113580f046908003010301c0b0b40883c80074064401c8800740950012718141c15900324400e032201400040306000d041005c584c0c1e082091303803d60322901001480c0c1000c000040e1078400001d01600a65007403013003c51180031482840360300c03414120303180760a500d0050015000382c080d50a400301080309070811301c00c14039040c0b01a1000583c3c000c200b08040350740c1000003440d82c2c0049000342d103e0103501c0394003d02030034103100b02ca03d81c58002c400745103405d109900e40710240c80514101c04c03810b0b095203100030071081c1600c04c2c44003514000c080c0c10001d40721484002c3c80d00b10f040e009a58454810000d0202212000300b1092559504c0000e2810410316418101e903036000d26400710501a40c203000b04020168014640103881d440340804105e2078841c00c3c00c1c810603c0c0c1c011510b860400805031a61540d602400303030540c41c02d100802c110404a4054110322204000384e0000d0f005081f06c0c0310102c10103406100003900da5100c003084502 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 406569820 1250 406568570 406568573
    0x906090a020904110a0e1609090926040504050103030905090609161404090c0809100c050a05031909060f06061106010302190b0715061418090703050f030705011404 72
    0x2a6060b0191000f488040039202c900c595855410038080200020412130a4511300b00071444080034680016000280d08003402040707035980b900c2407a41c2c01e60843c0e5072724480c10307400c0c40d4110a4005804e50b074180302c0c4180000507a683d01c42c0600d5001c1d40c440da45000b0014074150500020b40000f8000310710800301001008200e200180e6903124100c0c140c1740180d01d4111030b4083d01014810f54000d400030740e050020301c0d80b81540040300c0c3c0340583c0180c02115040b400e010b00841c102d5a5242144000500800116807034078030030790285070010300440c40c4564960f072005001d412109418411259140c03200440c0c01000c1e030740c1c13003910f00908842c1010144417040c0c041154a4000500009100700740b580d40c01100d64812106c80c8000c2e01c10045113654802c1d00e410030074902c40c07000817100481d40c18500007040706540038540341c9075500043c100458098049404600c074420051041142e40700e09200000441d00401011138508481400786603035000d1402e0041c290780068101c0c000d4010074109000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 406571070 1250 406569820 406569829
    0xf0e07030b0306070f03020c011a0a06021209090403110313140303040503070506030c0c070b0409050109020f03040f020625140307030c030c03170106170a150b0c0a1a0906090a02 78
    0x1580004c0601c0e007404000f4803e07005400a00401020b00020342c07a00380140c810070206022981081000c03141c40c1c03006507076400d040342d5404140f164a410200103001d40078041c2009400d43e9009071107410f00ca640e40815140403459500000e40010254404070010000003811398603005204a007940030f54540350800010030f40c0c0d40340d40d2040d40e004100000c0082d1000081d2819100d5010508003561101d91395000000000e0b081401150780103407070000000b4100b5400d100b00da45100281301440c1c01c40c0e440e0b0700c8401081c81c8040060360444003c1244a01e020300c00c21914103654903607900110700082c1d03801c003e40304000c1160414615841001200040794012104842550b80f5140010000f0b1482c5400c44000629072055500041d0103030000c03800320340081038034440c20000b0f90402c00c155955080101aa00c000341582400740d100307041840b0501803440208010018042142da00750390b581c0e100b00505082002441c8015216010312030003110074441d00d80c100610100800220a4a80005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 406572320 1250 406571070 406571083
    0x7030605150f1c1b0314040b07080718090c0306080106032303070203030a0804031b080405120c060a050c0709200703030e0109120f051e031f0f0e07030b03 68
    0x41c401110046014080003c1c6940030008101000c0c40c14013062000c4200301080d803003d00d4804005ca8245500b650810305054201c0d8807030f1ba04a00902d15036101ca620a4442800282c4501e04010713034181054500300d200c0f41240000c0034103040001e074200315040000c0803511107800886080e41400420008110710782c07000307010004d5a0345e181e640d00d405a144285148504403000703401d030101055107802c0e250809041840780c1c0c000d40351294210720344008420810898200200001801e00041c81035042100c0801c801d106504203d40300c2507003000010350190001058100010000141d1440e07081081c0214001000310040034024038940c082456a045030900c9802c0e04018041054030034035100360401d0509903840740081020081504050b2155401310004d800172a480d120141c500511034801c5a400a0845140d0314800b00410507001c0c10780d0020780800000744c00076080052000c0601640001411050860b40d20703545840026600e011f40240381c8400e141c80c0549507000c070703200441c0e0b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 406573570 1250 406572320 406572337
    0x601080c042009060d09060b040b0f010f0305090102040f080d0f0801060c020d020a030b0a090605070509010206060f030f06090609010c030e1b13020d09020f041e050613020c060703060515 82
    0x10980c03543d41e10f801040c001d0103034190310b0a426040002d00e40034405107034080c2400c01000d0320240007147d01d00c1d0a21007100c00d8000154005803401c561034040700e1196010582001c1c006001500c0c3c00d580f540c00010f503102d00d40080c01aa00410b41118131140c10aa1014050120307003414965507140c01c00207402d150385c0b00d48c040d000d182c05203440c0007159152003909014542c0100040000e0501c000c10400810140004903a030520741004601107900548c1035071a1072405034001d11300b03070b0303510307418040347c5c0b102084550f070184210007503a010101c0c2840114859003100b0000c09231881e1002d904c0b0309640700d01000006041c50150104444003010940340114842e4030100740f074450708840450030402100352210121480800c02000d034100e550081c80e0a82c1c000ca42c0f60140f810001d0800c001c41e07030701c407241058902403182080042011a0401640400c1c01001098500c11400071001607a1000c0b124000c240c00a1003042691505441054040c14098039420007050715200b0b503151901c168540c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 406574820 1250 406573570 406573631
    0x301051509130302030f0a200303060a050609150301030f12090b0d0c020f03130e010f0609150215160815130f110a0c0302060a050c070602160c0303020601080c04 71
    0x1890024513008200301c0d040e041020349181e03602d0040c0d1100a0a01e11520301542020590184c41004a03a0020580703000d01c2d030041c044041d031440c4c00108040f5900003a10075412100e00e03a4200c0000074102c014500942c05405201d84100e0b5a00d0040c0d000074148014034140309021006000350b003420420360b44850142c00002500000d820b40c180d01c1d01584090b0341d2404c0c4070000b429410000c002400c0802c88480002c50010341e62119033031400c0610030301441000030315003801040f1602d2882c940d6240001c039401079807400e2018010700c3c41604d03c12280300442c1041d0301600f5420316400000c4d541d0240001a1503211000381c0360008041031030002c2d808107119250711004e0f44145644d0b111039424003a880b900c03903407802c40742c6018010059004080e8050300403500000da20200314003500388100343c0398084900d04506030351000000d4010300800324900c15005964800207010245060165019400a102a600d04048203152000d02c0d2421409241070a0380c42c580781c0f40a052041c81c00b2486203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 406576070 1250 406574820 406574851
    0x60706020702040603030e04060605030c031b041d060f030f0607032d060f06021606030c17130c0b07021f0516210512060d0c0515090301051509 63
    0x246600a4090800080d40c494030f00b4038004109500144a8904490180e03401e00c00c650307507280141c815000c21100103071281760400000b441c0d9405404407010787c14100c1e90741401c154075100c001c0a00c18056a0305004030740b9000a0010a04d0180325144200008030003c1400044100002e602c45038040c2000c018184c90740c1d41c44042c040301369502090060b00c0382c18441806080e04114018041503c5600c150a0415001007003c0c2c2c03020520031004801d015071740b86420314042d8110000d0004000542c2004081402c42114190103d510303409401c1e03c03407040b05000120f0034005a04111503108442600c0c0800200005884103020b62451004c080104450500c0d4944290303203a10508070b41c03104003140b500700700301003084003800a030202c0000d900010418000303200035a810320604000078044016200011844c3c83d0251106034058800c07031803d07820654510100754403800128805682441c0400c080c0a541400d20816602900c482c0480c6001700e103d10116140384c6026102030032030381525 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 406577320 1250 406576070 406576073
    0xe190920030f01090302060a14090d0c061803050d05160c0813170a030e0a12060b0409060e01020c060a050c030c0a1e0807170f24040606030b0a081603020607 69
    0x2c0c0141080780245000911014a5601d0004d44501d02203c8100c01a0f1510303845030504229903e0413841240410000c014400303000c807080c4d4200c10120303001c48000380c482210b240c0004204400c09a0640b09841e60394035001540c003174106545000700040c005020b40c1c03141d0300d08107a00580c250f0045e904448695500e40e03c1030f00c40c0300b0348004c17908545032680a071030381008402c200080c035554687c06560359801d181941d40800035403103250b00c5000c0000c07147e80b036200081400360703110140b000c90041000401c038a05607202c40c16180090310341400d0341d5010400d07094040051202e10fa1001c9459410469481d11841041c8180005010f010280c4030104020306094050203424803003e8170708183c107401c100110f4004100d14001c843c1d00d1300241a010782c6007280c03920f0b5101c0c40d01501003084c080102d03a0b41c0c170b1006100580c06900b08a1050307200781a029440d29648500c101804840c0d8000c140c030750289003800440d003090382c44110703150710114080c0d030f6400940410b0000d03280d0445540d55030b101e45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 406578570 1250 406577320 406577323
    0x803090d0e1c0503040509010605130e01050d060c030b03060f160e0a09020f0708180f0607051005060f180a06210f0314031302120703111201150e19092003 68
    0x5d9402498010306d600002041700e0303402030003030060081c1b1035034100ca0494036100607603a560828440c03e038200c1b98031201e083c0000d000341c020310078625140c580040d043e140e00340001d203040c1c020b5070211503800b50b26081c441a5508107034080302c003112030308081030044070744004205000131910620807456400f10303520241d500150700300e800e841e41024295445155421820400c204140c200034401d10048901c681b80b420048140c41d415500b0001419440d642d1145032405480b0080001d0703440f80c214803a00b0b0156550803003110840c068000e0900d0545407898031102281c050f5040302d540180c03074551307a52038048500881d20410341d0110310140c0705120780c617054590740d4002a891035000c8000c01007252480010b9200301100e802102d8850508006403140c0391545954000034100c0e0010004250841c01d01481440e01510340000001e683d40000030070040300c0f00c268101d420300c42459024414401030141d10fa41da0402140c80c20001540300d40e44000c503440040c00c00811406c40050000e05540c0c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 406579820 1250 406578570 406578577
    0x106021615180311030c0406050d20060c102f0f0415020303060907030b0d0605060d0804030f0b1b04050d0f0b070c03030f02070b19020904090803090d0e1c0503 70
    0x6501c0010b01c90380f070749006242241c0b14003416010348642c5d030115100346001e0240900304c0b0000b40412142c54040d4036103c00b2600000041740580c4040c45895155880d03a40040180a140c8005070112403a0b002c224815581c1030b4600c0e20307107902150907441403130902c14000d100844510b03000c1951640360342c00844a5000310351242c0c03d580c880c1c91100100c2c81d00480210f110f100115800d00c50755881d9102581210301140e8482d4201ca880d400a000261300d540c0a65001390009004222106156a41540552140c0c00441d8a1750b80b4a40c032500f0000744003180c5408c078600f6041403481c400300342c407104118004c0d486554481d001103904581404a051012001280c018000820910b0f01507401303001d04240300401c5001900d450f00114016296109852a2561142d51b200d496104c001d40088142030304401d40381507560812016007155500e10070000e01c6445141c0d56604d03454a260a40e09124000c11240c040c48609031071907925a03690310415064110b41c00440c0001642410118a51302 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 406581070 1250 406579820 406579847
    0x2180d030c0c060503040b07080408310909030f02010209030624181b0405090703021b0a051e0d0e090903041a0c0d090303020705040f020c03071202060106021615 71
    0x60b100ea801242c11680f00d0029441140182c1a440040d1540b01d800c40c8d00c00ca046402901701130301884203a00e2090150582d000c609031724182e00343c0003502040746c00f44607101940300211041d5a07003401c00030503800020080c0c0c1044d060008504006418010030f40720310700285082c0507e60284900040341c0780782c4904040920300507080034011001c040704011102e0f401d84004000760a40e107074000045803548112800d86501170f00300290703600e0f001d800750065006140415061a100c8441c05a420820820324910300d00030401010300480c2c406c548079408413840149045070b0450907100d4002a004035407a00c5c41e00059459074103594480741c5590442c019034001040354444840d005107241d252002a0000100d440b06a8200ca01c40e054242d41c03c140754440240982c102a03c01c10561409034000f0541140d41c400c003519080b040e003040c07815940700c0c030411100301010307515080e1980d41c104402809401180018130a11000400e08201022240b2804800100900f9540c8032f1510404000358400d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 406582320 1250 406581070 406581083
    0x3081c090f151d100e0c030f010204030c090506030a030f14130e012c0901110a030213050603071403061c230706360906090b030102180d030c 62
    0x12000d601d0001c41c591002c841940e0000c2c00d21040c802040420b82450800350200c0f0000e041100b0446021030103000c6030641080c950240740602c01d8075480a11406004555038000180d81e01d08614140026480c00e82001250501d00020007a05450004810030426018148002140c0000381c1c00c035180d0740c0c808180000a100402e41083c48416190500300703980c2101d01010060b0788804007942d1603100d110f2219000c591002c15205061030144c0c2c0c460308260760030004a446483c450b4503004a61081425400103580010034080f40301071400c413200500b03404c4a00c40e2650170003010003170000c1c1e8207014600354a0000030220b4010764800d624100ca0519030403500c5034854942c01c140b1503100c00001100218150000d082c24501d0000c00c0d648252515510b801d05e1080d80101c04c600c680e100300d5100c0d01d820131038030f5800c059002c403c502c4100414071030002003105400c10800200740e030b10b0102158002e0780184460501800c1030946d000c451107044c0c58031038910302103003012103480e08075140c0a400c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 406583570 1250 406582320 406582343
    0x409050c0613170312040222091109090f060a021803010e010203012d06110f06150109050114030c030603031b0a020a060c030207032003010203090d0f050403081c09 72
    0x2502c009002ca2030440351420036625240d81d502100319180d1044100060000d0139001c00030380145404c180c03040d1100c22440005803041482d1011904484220000359406c00d0740650a00381454403107121503001005502501c6e640301402d010341d50b01d000280c514543c00d600401c1e4810202d004504140c0c1140004000340440c41200c0783d203500070740c401c1c003e051007034070000000350700e154020840c842c0690341c074944083d180d4a80002260205201454018280921202d140c160301d010844980070325541020840c00125190015001d00402d500a03030601050980002c483d00404050f25400807481c034006680355160390000e82944142c076071414940d01e80f00c5040c41c02010000301084800e00c00e071002a07a15482d59001e41d4229102d540040c01644100720900c0010868504074a500c1210420301c16080c0f4000300080c07d9070011134981509601200c80c0000300d0b075102440044565140c104070f4500b03070840d210003886104101c1c034403228440f202c40c0030b0748884540c0d1104181c1c0b900a00304401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 406584820 1250 406583570 406583587
    0x905030706050406140f010b16050313050f0d0b0a020702120708060103110f0d1106090a08150106030b0907050c190320061e090a1a0f1609050409050c06 67
    0x200001d0f20f0507110207181c00b80900d10044103030500ca008140584501001d030786803401c5001690b0041c41c440500444140031580046c1041014188025924a00c42e0103103061000380700302000308403135071441900304c110030300085101c0c0300103250441301d050b40140c0d4802c1140046400a1041019160244079441e0b00107034a40700401c01605880c490a121629080c141701080341003400411000d500000b01850000018000c4000791401403020f88102e00b011361900020b440400340c0c3d4040300e0980c2202c3c28a40c0350301c0c50419004c0c01f50175241020080c088041c0c01007485118024582010300200080c0d0b00e040040c1005501021007408007101c0d1015403610b40108a085500403070301c0b001210352070b81e4421100202c0c82c58400c4098541d60103c122160807015104400980514010b004141842c0003045c00300950203074603020001030b00c05a041108401c000108000c01d014002e8648c0b2144603c03459000041d281150404c55001c6100001810980d050410b5454000c0c0c2c0700e03900084000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 406586070 1250 406584820 406584833
    0xb010b04060e040204050a0603090303060e090a062703080c1c020408100507230705030d050f13080a050309011407031a03030304021f050c0a0f060507170103120309050307 75
    0xa481c11035840d41039260300c1506020580c0114060030f030744550800c40a0044501c00d0340544551402482c0100781c10380c1c0d501d00c076040004182e50428480c1c00010342d1100340035542c010700c82c405109800361904101c1c0840070b01001106144001d040002c00400714400726821000c0d5049441060b1507030b0860048100d035100254000e00c0703040c819004a04100d03c821303046101da54032030f060341d8903841c2001c0c3c45030380c141c480035600070040324001005110b5100071030020000b07040f030031000520000b9642420220f0004c60000241000142c0c0128540305001900c0c940c20b5030380031280c905100e600d94690314103d5003d807081c54100700c030140c02070082100255040c0c01110040301012095150780c0050024581c5901c0105c501030740203440c0c20301074200c40e4040d0301ca00811513000e1034072505101455045904004e2100f200380d0341c02d2028880a0280320440c8505e0380c101c482c90400a196054034030301207503010f90520025001d848524148082140a078100e064056408000c0d65981d45180c640b80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 406587320 1250 406586070 406586077
    0x5090105070b0703060509070c030e121204090f0509160b07030c1a0703050901111806090d2006040806070c1e081c180f0f02040f050f09010203060a0306090f0b010b 72
    0x1e40c414407c032408204220302818161344c0003909036848850104030001400790600c40070b00758911901c0368000000785c001000000e003025011a0602080c080300725407589040d100301070008800f5400540510103804d1540b0030304801c40300f00c004695160103c0e414107440d03060312107a020388030059502c4140003100d0161b111074070410080c2c43c10055078a501075264200d407400c0071440001d610800c0034950550480024515400f00140308614052400340814911403c0450440b4010705046030003810020b219500c032031000007a40c0445c1894902480561b55a0020700240705024038088040c1c20710510702c8180b040310090a0a02400800a25014100ea0b011800b108501442006084a035203420f00030401e00c4601c0b489281d54400c0191100c050700c2ca43d013070301191440340c13000c1c003180141c0f600d0089025821070490000303a40d2415900e00c0c1c4950400400540c0c10f644100100152940c030724616409a07904004005401d040d01e00e00200307034250f00040a05036682490000985058a00c0103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 406588570 1250 406587320 406587329
    0x6021b151605060c1e0c010e030a02070314010902090402040506120f10060504050115081009050103030c0203010f050c1b070306020d06230d080906280f0e030d05090105070b070306 79
    0x86900e2581c030540d0b0781010b4085d1030105502c5c048103c2c0c0240b140111007010301803204440c000000d4008a4500c01071031070344640203540140e001801c040007407054070b01e01d1b82107020f26a80203000d080140d500141c3e08840040c0300920556031503000c03500c0c0d9200d440d41c0c007034800b40c1001207070701a4440200483d03440c104025003021003400c00310b0126143c04d03e801014100e031540b0303800a42ca10070b20b11058803d0f5000501d00c00351114210400a071a400500881c2d0085001c1c0d10380380c1c03072000c05005050a64000c1800301e0800b6052030107000b20303a03980004072080c2c20fa01c8124030080340c1428a0243c20481c2552001c3c01c0d590000c141e1801c401010742c03118080b110f949041648448000330300c1400c0c02480c55020382c0c0f00b0400016000400d03910030044c400032400401c0703145010884103100840c03c0301c04041c4d04030890095030a942c100c0d0442001d0340b81c4034413810203051410031140002d944649807078622082000110b032a41c01a4000d4042d182d0480c0e0100c0c0b66090351405100081c000c0c00c10744203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 406589820 1250 406588570 406588573
    0x30509030d050a0b1201061203050c160e070908160311010e130518071409220507080c060c122b0903030506060a0c02010e060408031b010f0606021b151605 68
    0x104000511052147c942100d42c2001c0007031090040ba01e040c1e4607500034043c0204980518401c0c0c501e008803440d09a40900342d00b070403c1640341400344000786024141c1d0007078002940441c401c0b40c10440070015100440754041c80c200c1080841200407581c000d8449043c60b0000f104e168550b004003825000588508042000070a04d0b0604a030a140d890a45200380750b414409090109000d05002d075540b0341c0b01d540b4450300c1c8038407502c20030100d100b013000e40c0080c0c519400c0b1f00300500c0030000c00c0c0300c00a1a40e00840d04541000440d0703500940718000c0e0b401c4403c01f08000116440812010050624a01d0340e0360301c0312000a02c084000c402a011403d400c4000078a0000001d505140403400d446042c0c0b080e0b910142d005006500544000b000c010609500c0341d0280400140e0440800040c448010110b21081c000c81c04c43c034003282919100c0010104040c03c058091000c503074001110004484d041c50304a0003d0120b07000700e40720380894801c0300c0f054280010005001c68045181e001c42c10b00c90740 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 406591070 1250 406589820 406589839
    0x609060510180b0d0219021609050115081503010509030c062406030907150507050705120327030111030114010305010510391703041101030509030d050a0b 68
    0x100226850344a18003114104000300405100421420010386062895844010301e403880c50000d40c42611100c0c40c0c001b0050b400f003031740480b081e030540c0141001000f02030002d21407035041039100000c0e40c400402000400c69040300043da9868440f0090503c3d15016000b0030213814401c5c0616103940c810441803981e0300c5801c0205140082e00000c0c1502802ca10860b40200f0025004108880d0f002520606ca5881181000700d0600c0140415901c50440394480c5541c40c03449160076400c0c910190710140c13003500e14480b50034941c8004400c480302c070914281c4548030310720307022007000c407803003410b01119050340c80c11811141d40c503117070001141070b034480c00b013544204401134004405980b070074002c1035000b541181c080d03070070140a15000c1d02c0a080c0506035030340182913946106100480c0165000c084641c0348500d100f4080c030020440c40d4802c05020107480d510b002e4413616125941c0216060405903100001540408180140c0b4140d4961000c05d00c0507003004207010700078080e00031406104402c0314 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 406592320 1250 406591070 406591099
    0x90317040309080618030417010f1409070e0105030606010305040f050303040f0b1312050c07090222150e0d03202a0a0506030a090f030f120204061706120106090605 72
    0x200301c80702000030451700640c501070511007a9960030782c1c20008041a07640b40c503158150000980a0144410300d20002c03031120303203000180f0601e040c2c450703130020303038400314841c014885030b2800700360603074000303000c0c01c020a1584a61070b020b02d201341d0142010780745020102c06e010410000c601c4500e4014010004641141c4900154412401000b01d005100c9249100da1300c00b1940214060700c40c1c401004140c4490607030301ca140c1c0c2c00340d03440126042c1c2c0048903000070031085c00a81a10402424a45031070800ca08985140500f00d0055545607510480bd402114800c061181c0396820101c0200211f1041d2014660301035030342c61003000709480c03001680d84500714002401400405103090b00800405074180783c42c0c2400f61690018015031100d5840b44103100c04204c0f480c0c4124001031003640c4045000d292484010074005000f600c05000500401c001c010a541c0038a00c440691145d002d5070310b90b525400001000814148540405075080c0840010030020b02e9111034211031081d90305042c1e10304103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 406593570 1250 406592320 406592341
    0x705030703061706070f0e04020d0b04050109060324110a020604140c0a030303050a020415050a1b1101050a0c0507080c030f120a05030a1e0c031803020601090903170403090806 77
    0x1000c07144100fa9010380f0004403201d1154a00c500b40e500281084c0b0040d10740c0300081000e0740e125840000320b56481e8800f041e402d04103480350707a0040201c148200043d60a581d5091460300400d100d01046061074495480d5044880d40024102c0c50710801f625a0340c0d104c120041d444003811103068626a6094201d1185400701042052900100a00c906030007400e40d030b4160300a003000307007282c500b080c1d0038800841c0e60084c00070490b05c0c0c440540c035180e444d4681094010062070429403548200e049050b008400202c5040ba68100c0b11400d080498480309450400c841003000410054a0f03807082c034400241450000c00c00c03020a040641c2568a49030071041c04035a42e0118078640321182d14204403425120307105101840e0402d0b100f107004524984240035419001d42d190304c4814039280c3d1812510440ca4140c4100d0115080a0220180c40302c13160718080d40783d81e8144180c000c1203440300038103000c00d03101c0c004505205980401c1625a0b09040c1001000c0d000c00d4043e17100548100800300b40c20245 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 406594820 1250 406593570 406593599
    0x50c0d0b15010309230f0303091c09030f0803060607020411040518040b040f05030d060e0105040501090b010f080a1d010203090609030c070b0a03110a0809010c0c170f040e070503070306 81
    0x20400c06a5150741031400d1013020208450601e41424011b01010240d084000c3c001140240c100030010700001c402c50307410318240b014203540001030000380402007000400007030b0f0342d1031325541242e4101d440b640d409012462500c00d0f102c009500c50b02c4e0071005a001c0413510050403c0d180705491050008540c80031303041e03d0300c000380c40c05450320002400150005600700c0701150018454030941c0d0034041c4100d040402d68030944c000c050b008010300700600c41030a041c41641d00500d5200380500c10030381014006850108041144800c02c214030ac00034030b1413101c68000d0f100402011803483c6288403076080d402d000b904140c807404c0c1d05005003404528031a1001064408a21100300a0842d81d860700d11a890702d81e0203968003105154850040810080c022401f421100440d40c540d03441a02c2c0c201401421501d1100300750081c04812280c52003c43ca29007035200c08007840400d0540e44226988009410b40640d52009004401c20800c01010b10fa10201940c0642c48503101130000c262500100110040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 406596070 1250 406594820 406594823
    0xc07090e0a0b040f0303090b070503010312080402010f0810050607060b2713061407020c01120c050405010c060e03071203060e010312030c0e041a030f030a020613050c0d0b15010309 79
    0x92420020501151800b00782c428205d101741400a12034600c0d50361b500b180c040840d444404910040300400a11032008040044809145090f0401c0d150603400079041e01c1404003100200021003000034401103415004c14003400004058075150045440d02402620802107a54010140088010502140f040615200100c0390081c640c1c01c2e40c0e07407000d000c0712110b141d1040d60103640b225803024140e800b01642078000e081d107a025004400c00300d80098138000c1e00d80c4d00c004116140400742c80075641d019080c0d509668003443d092807080f10030304105016000c850740d003800c1c41c0800541d540400c16003010300c14402100361001c1c003499a8581081e40006003d11010b41846000c0d101101c026100394041406400f01f81070240b00001041c1c08142100d454100e0024000320403096107183d440c04200b0300c031b80804444015880d00154140094841d0701c06814031784201002690321040040900041c0c05400001c0e045c0030103105503040041c1540c03410703100b010303e4030040244507001d94424001c40290310f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 406597320 1250 406596070 406596083
    0xc0f17060403051e0403020d0b16140901110c060309010624080403030c030f0606091406090f0d0212030d0f141003080f16050a0c08060106020a061d030c07090e0a 71
    0x943c500c40e90007001c1a410007444c401310b03000c100120050799030100036560b20307026580d0041946000d03610007402005010a02d41404006404031404400740348c00c030b0710b49890a02e030000c0f11206100c3c1c0b43e480d20100101c91640140e01108200740c51405502200c110b4404d001001003007040d4180006000300801500720008503c0c1001401083c0250814060001d82d49000910a28814540f0040310002c0c3c0107180001e008500400200ca4102d41c1151841d400700c2c0c05920784052400007401e0110080115400f520103001080159500c52a0104504118400352552100d0400100f0700512454a04c10f01c41440c1030040b940241a6060f020306c2103030401030141c0303468119201c0120b83d410548429a6031101040203203010a03d18031000e1000340b0070f0008100401852811411880b45a080360140354017290040041903030005128440c00e400c1800081d035100d54002522041c414481d2080781480300240c441c03208140003407080d00f00d6640c034104100a012408059071140c201e845d010b403e5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 406598570 1250 406597320 406597327
    0x306070c0c06053103110109080c09061504090603030f0f02030901031512242c070306060b120901051b0c0106030c0e040606050402030f040807020d0c0f1706040305 72
    0x20b10340a03034020b12013070035400c840165510706260030004100302d120b5984800e0401c1d140400411441d94404940d803102420f01070645814154455641c00c503809186200e6941480410080d890f079041e440440c81a01900550359600e400c0714030040d0034644000ca00284019581d151003921800b0110b03064102980610725144d180e100442c003400d01031194582440c1c0d1031000040d040281111089000d1041984801c03503050740b040c14070468004412042c5242c140f4040c0740001300c0d14208140e80101c15240104800300c0c1200081c42c01e0b80ca500014800fa1500c607011a00d00c091001810100301f021081190076521111490300341c6c1c40941d00a148131084418000030445100058155459540700000725a82e0781e40380d500300d804c81584034422501240040c402444a64080c40000c1c00c0191415455410b00200705001c01a00400260030001d002c24030004541d600c5000000c00340d003103c219281c0743d0700c0340840c2c0d070201d03a5842090300407a45c81d03200085201c80410110b01c07031074154942608 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 406599820 1250 406598570 406598579
    0xe010602060610030b0f10031d0f0c1302040e0f0108060a0b1c030314010b0901020d050403020d0605150a090b01020c030109021c150e01021306170a1a030a0f020306070c0c 75
    0x85d00a0408140c0e1140304280c44c0b0f80d903519903002c41403007058107030741c040340c3c800c3c100d6400380b4903014070320010145402000448a05c0800021301d446100400c1c2d840f440040c0c106400c0500a0189410800a051840c0d00f44107d000001407001c2c1621045d000355203668851340706040848203c2552540c0040c20034041c0402c2c034400511595819000f42400700d0f14201d0104a6101d07884260402c4032040400700b402e0036503503410080c00808000d9030401500c0d03d0b0070342d0005a50031040400080c605911540003845c0c00318a03003220b405125020300001d1155840f070340101c02414610007020f00510920651201074901405610b0001d0b4015080c6c0003103c01c810101c0b49485900c02c02552000c00f18018421035140b03e100d040d506480b440c00060312010752038005c00d0300d008107510150030821076030340e8119080c284008068020030801000290500d9500300845203240388407065a0500032a2901010700c1090f598181600388200d0688400d40d9490105445810000e50043c0501204160900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 406601070 1250 406599820 406599827
    0x702030a170f2208060c03011806170d110309060d0207020d0506090c01090e191d070f090c030207200a05060f0a030605040203160810031b0e010602060610 68
    0x1002452415005882c00740802e5900c2c010703610035a0030454154569508400100c1403c03003d0b80a4084400074205a0404404031030a6002c18003400400b0012009207001900a5500010061440003021810a501239245e16203921108505c8404a4804844002164400700449030300e450020081c40c28120b808a0410094000744001c03a044804510072001049003040354038400c50852001700040401c0100040c0b010125510460034007031000f0074803440c130180000307000710552200d0340094801d8092040c054501d05070303207002c5402d0103015800710710359000100030b0f41a208100760600c1240d008040403002c07032003081c0004d4404000e01c5150080d12a0128002d036a041008061808c0310392150b0005032198407030018070b00c2a03080022140c0c01140c05000c1c200c001e100c02c4500b1420741ca44040c01d02c001810240d20002008200c0b00040c1003141540c02000186800c6140034a001105400031000c22100b40100340b00b0400c00d800000b03516100141c1c0e24415800070f0403282d054101d404007075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 406602320 1250 406601070 406601093
    0x8120c1603080c160b07170f0f04050a080d0c091410121e1d010902061b071703070c09021608070807050a0803060a060203070f030809120c010f050c0702030a 69
    0xd01c24420f0820203000071150341801c69030f0321030150400c0119810600c101402507062450140c0410002d001080190002002020341c001e0010482105a40d207030f16040c0d05200841000400141c00891211415941d03a4408668400c01b504d5211103107880710354040b140c04a1451482c0e2000c141d1150169462044241c0500082280c2012501c02e28400c800707100c03800542d09048105955101940403580703840807110544413000001c0012100c2600458014480c400c411070581440c026844e081e181e040014400400c0d90400e001481201e4055107500d0350b000d000140c48280350f0003c0032031103860030300c01c84044211200006481d42d48659551869401115081d6003074581403050201081061180e010182e110b009030a07a2850808c007040f410403a9900680110350081c042080000c200004000d440750305230030104481d540e030124841c40c03c0701050200c0706c0b94102260704000c000c415001040c600060800902440d07440091030f241c00c3c024168041d506074800e5503414041030185801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 406603570 1250 406602320 406602331
    0x5063c0606070c0f090f0b04020c1510030b09100509060f07030b060903160509010f0501171f0303110c011d010309020102280c0801050c1803031608120c160308 70
    0x2c0f020399540d8001101560701e503544840303500d54507000510000340c190300c12540803082c112021403c180402c0c1714550354555008805802621030b602140300c403840c11126400460703028100028614000403c25240d41050140401050608010403041032010444ca4030032042e05662100a60303c03208200d02402080304940c1e00043c040240038103c5c0c074140440c0f46010044222446214641000c2c0140010140d00c2080154078406050000e03030b070b002e4a032410100400c00e6042440d02c8003022000b050a64005010900303c62100000030140c0205440c0f07031440d419001c0e1000c0c203540e040199800c9424201404004240c0103128510390300940c00403c10f14018812108800c01645402c0844405c03d03500e40340041540460301c0400000320b8404014042ca58001c0c45241802d0b903019010f4010421144078612030b40f0092000c5460030015225491129002116408181d040200755603001021018070a44514005000170341d8000403507000a414240800c070704003041d18202c902c0d1170f01502 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 406604820 1250 406603570 406603583
    0x40515091305010b1b0610030813081e010f06030231020307120e07050117040302030702192301020d030c021c11070603060308070303050601050705063c060607 70
    0x444004030010703841440c0c06000e99441c040c3d0b4901a005401802e50003c0130301100c2c940c04007007003059103a003801c2c20f20200c0e40d0203500f02e601e4404110030301500741550380180c20035104081016540003002c031000b0f461a080700008100403100d0b21003001c140c0340107000c0a5041f03080a101d010342003126105215514140003211041c140034a90901c060b41d1059a464002031381c410502c6c59641414818445645601401452480e2401002034103400d034041001010300744c40800034050600a008880f00258020042c0703c1d20b4151015180c202030890051042005014001d0542c0343d0401e00a101c140505800410030314401c80c008a010349801c51045045024568002d04022800383c0842064041622900141000b902c03496250068503480641010304266080020600c0306085481094061902107110b50b038040058600303214203580101503208031000c02c0806a0284907032140c1603000f00702594104140d4034100860640f08200c10440c034006404200c03c1d150460082c20f8003031144c203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 406606070 1250 406604820 406604839
    0x9170708072012060105030106080f0a121211071202010920180412270513230114040e030405101421070f0e0d03030b04020c010e0d0504051509 63
    0x1c085402003c000104481a0780040c2c014026443d0a000781c6002e041444004d06034441a541040e41e12035940310050640c10102040700a440c1c800c0a641303941c0404441c2c24010040c504240640c83ea10220b42076468560079034038003031010320600502d045160005a006401003511a14040135491222843e501c8920f2440484011007044642880f481c040c480c1c0d02c0215841c44000361000d132011000c0011101c00c0300c0c010350f0b00968564440c0958106840903905211082e004a0007020315403070500c10000d08100e80840183d1003801113042c0c0c2c0c450740300004648200800c0c031080d503003100d00d03d070071079001404140802e00f80f003d007032845c4249910f441c1100b00b0407000020003a9000510b500c0c40034520402c84100202c0c40c032030f131035000b800070315007055284540107000303002071400004288540c072889503920038907110360041d440121000f0411075541d902c140e05c02c0d0080c0140b2510140502400c01c465070018040c0741500d0465801030021035002020f100f00320344580c8a0240981d0008c000c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 406607320 1250 406606070 406606133
    0xf0a0b0f03010915200a08070e0406090f0606051c0b040626070b1e18040f092f130e0a0c061b0c09200a02010917070807 53
    0x24000c064049000c0d428030340750705448030804130079101c82c02151400313441302d05074501d640d112000494039a20541c1c50140000d031219001120854006d01105074854244200480c01c5c03500340d404a546c000c200c801c100b0000307564400c1038a030382c0200030741c0e115001c0d8124502c01c030f00c5e0f0068000480c035484c01000001c1e071944494501c40544220030038400b84010382c002101e40c2d850108011005058080402d81c1800c1c002110600c8400300401b0071a00380501242804030340510680400d03021f1001401031040441d0301051030000c09001009407100e01e08030101381d1039032543d10158030358030f8803e01d40b902c602110141801204134510400701c080c43e0782c40210b402605411b020b80c5081d14400c5a2108543e40703090310007000210b81c494030303021200d8010240c07400500c00c0100da808031100010040740702b100c0c5103140c4544423014410b1007601d010000d00740345c200c0c1d07040d400035001e5481841c615100c006d100c80709424a01424000130800e0348200001008511051542c41070002c0c0ca441c3c480c69030194 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 406608570 1250 406607320 406607323
    0x1903050607050408060c03090d0c05010e070e09150103050c1903150c0e0102060f0a1a09010f080717030304030e060c0a050a1104090b0412110f060103030201060b030f0a0b0f03 77
    0x300d030201c0002c2c0b00814180a0044284580c1c0e030004034154203641542416800c164940710180da1075407e2101106c21241000303c05c2d08142e11002d0142c09640007990f95030129200348100f2171b8404403601500c07040081100070040e0b07503410f90f40c011009008410000d1305000ba0841070314004c000c006011800000010000701c5030950f052f011701c7c1301254001ca031900240485181008607415074020404015103401e98854242d0311642c5460040b44030010181e0001d03490721550401034002e52044000310b409407001481100307ca0f182c00c204c8002941c1c1700d0030109402e502c5062001140c004002242c08a44202110648100028070b400d252580b03a00d07c25203040080d01045406810055501041c442541403044d41c2c080203450501080301c10340e448800d103210003000209500c490350b45406903240b154008502945a0700304480c2d403440c80c4640966540c3e402d10040300158200440440e01e0104882568003c007062211360b000d603180d00c494080608001e070380d05904a0b000e0414004942d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 406609820 1250 406608570 406608583
    0x60a09051f09020f0f010804020409150f021b0d0203040b0307021e150f09100f0b10110f07150e01020f0610030c0f050a06050a02010f141f060905190305 67
    0x107503a000040c041c0d0061044c08402d80070040c25074420f0401641040543c1d812902d01d0b50701690445002030296194604039441001c1c01d900185043d02d040046031030b40303095900500304211034408804190300003940e1b9030b41e100036103031803600160014032007003089036401005903070403a10a0054070805d02541031010b1080308940e1000b49903030f1110300416001005c08110942007881d1103038001d410b04c0d1403c802552009021107280311603984001d040000030340c0c0c0d48401e0f405036004165012402501c200200100840b042c0800c4c1802190544000d02e100040c0740f0080f110001c031a894080a4007005617601017158070000e043d0b0240c0040e80364900401d0100504c145c070f2010800c846030b825410b2401d90040c0035040000210340e042001d20440d996000e00390300b1070b401c1d03182041d80d07804001822809009404402d0410728108560700b48030341707510140f95108041d4181851109130400c01174030f01c60a1688285008601c40700c4c028002c42c1444c0002d800000003580c44003c0c003650382c4d40c48500c0d004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 406611070 1250 406609820 406609873
    0x1401090b0f07120c0504060f05040306110705071409070f05130f15030605030a0b0c0f04030614060103050f040b06060f0325020a081204060e0d020f011d060a0905 71
    0x400c00041040c400e403c001032802c2c51410800410241c0c0314000d001d042c3d4485c90149070284001507031403185092181e4100c0e0302440e0f02c00c07400e015803107000c0b41c12011038204190850329070041c000c020070b00d81c04001d0080400e40c0c008000c0384036902d94800640355082e89030444401c12034104940e21401001044107002403072403400b942207007480c2209140c0b880c0d405d00e041208041c20410100126030300042c0c49011a0741020401041351600740424200d8490000010b041d00740100d00003060007460f5001c2000316109a5141c400c41d61381c0d500440894500b01d07100d00309840e40002040101704040000c5500c0103005d04500c2c90001d101406216541040302c01d550b112003079002160309081a49000707004103180e40002d1144110503512405640a040c2a51000070040000101403041603003003034490121440c16241800000ea47c02901c41598040e280d1042d0308041c1041a0030328010081104c48248101401c2d451322001c40800162130031090a8401d8030590201c0030804448148007020078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 406612320 1250 406611070 406611091
    0x601260c0d0213030512160b060604050d03090501021603020915010e1e0a050103020c070e04020f09090105040c05031c050d020d050702060a05071d010c170d06050a0b030c071401090b 80
    0x10b240d490720606c1e2080311407503150340010038040d100c0c09170395a001801041c0c0d0301003100c40c01a03442e10045140c80c061940b01a030301111022800c000d042d001800b000a03240c0a0342a900030300e1400b44120140c03042e0717110003500090b040c000180c080e14021603802d08040140b51144108041c140005d108006a06080e8181d604019107a4480e10301030940800900c020309066040c00e0701d6040c2540c032412280308000304e5200c1c5000180440d40c3d41c0d4000004210700030502d200c1030030008442402420100c0d012034803040f1160300401c081c9000217050750080134110b4104241c1c0c3c1c2484007224250025100348004d95020b0140f51042e00440c05528031402160340148040e00d407607480e003002d07100e016041c51b0a00240f2a452101c060ac0910100b212840a0900c900107209034544a81d00b98080c0d403030031110b04804038841da0b0304499508030008a60040f288500b0080d247c00f03010149100644a4559280302088454006224003042c81000400d02e0300014820003251600344e107918040300c4403d01e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 406613570 1250 406612320 406612357
    0x306071e200304061e0c02012106090509010e0c0a0b13030206040306090b0a05090c010e220f0b090f0f040213020a03020912011a01030225050f060601260c0d02 70
    0x307154440700800c2c0c0d001260a1703600d403c980410010300248006030000e0b040000940390b070241814564891021080315900170082ea96503850080c0060905845d80880d035400d0440e010070605000884110624000300050b5400340361583c4092650300801691403040e202e18000009030765400060001140903c01c0800d21900618222007001b00041c0002e243d0391500f0180800d800000031952450902030034600f40c003011240020b40380201102d0340d5400d8030243c80d080c1012020300e81041042c04a041401e01c4242001002c1010103a8212441503d03030341d080000442d414402411182c1260000c1e101e0b00380c103080041200240d81c0540c82600c08640c00065024003030400520240c41c1d082d502c03008001e0511041c0610080e034000e0b58025040503000b049007100804002d44442c4111070a52034031000360418605a9110082c1c02e032484810701401c0005060395003d240b008441c0c030003103240900c507842c1042210342c8002019100115a940c01c0c40026104041b904c002e010284201e40300e0f648 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 406614820 1250 406613570 406613579
    0x40303060b1309020901030b060a020706020f0d080a0b1c0507030b0c070b0403030506030102220515090a09110f121006020f151503070e01030309050306071e200304 72
    0x25a100c80e4866000058108800780c2403502c00e214200c16a0703c005030141e904c500500049000d0415040e019510090001e941e2101076000144041210130759001d0f02c4400c4075400481d601c6003100501c0d04046500100000c1c81c1c002180d001e80155400100002c00e00140601c0010034403d4168003110340382d00030b035000e0090000d0294050740c40552043c11900c0d018070f1f0b0790b81c1510080060402001e2580307510100307400e91f8088d01901c044142c1c0e40315110203060000c581c5200c400d414491240a4440e002c0703c4115011110121060ba04004d000c092107149040342c9030340202482118201e550000380015070303000004000420203c00100d0908070075003003000840070080003541c810825980407004001d14464045801c202d07007081a8484101c41c2c0d00c0c049610103a0300103014080d450b0141c0e00b008164482001e02c206d040e20300076515503042588170814540e40c0d0400342e42180102c3c040346500c068003035088407400107110781c5141c42c900c000081802d504004203000c500e2503480d08082010321 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 406616070 1250 406614820 406614827
    0x9091c0206100f03020d080306041b05120c0a080c1308070f170106080606010c02130504060912030509031603031b031d0303010f170a050f070302040c05070515090f070e0403 76
    0x600106041110f8080c070f594000303072005080340e20040c001301c00030001610f11b40d0303968444140c400e04000c00d40402e402e0300b100201680d01005440002c9041d6401040c03004040c0816180d0001c49a1606000d50700c0e2080c0200c40c1e0b4101110092520000040c0031070000300a214070002003000200340300c40c035818a100e01941d03c02007880807440341c1c0341100c01c1201c2c000000d12103030089030030700300428080503030f00105000c007030702d96403000c0700034104024481045413581c03010704154050031541c040300034041021000e0742d0064031090002d44c000d1202111300107051b4241000c041c0f00381030015020901010030001850082210008030707544e819048030210080103c1c60b200100301001d14519070400280201201c0d2074000d5890b954154101403550b580d00304044060300d9006800c071400001c007030213032030b03621180e40c0012030160382421403121403940980240c0d107800c0d51280107803465070000c003907100d0181c1e07009014a8a0b0b00c00c11402100c2c0c40000d0044401412461003240600d141ca403d015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 406617320 1250 406616070 406616101
    0x712020a060206100b09040e060f04030e031c030c0c05010e060702071505270d060b040c090b070209042904110a1d10031e260909091c0206 61
    0x41d410364101c0d40400c01d0403038900b541c03801503566061140342c031411018082801030441481c00400f502c9060180701000d0b0218900c0b610440c46541c07022401c0c0d0b20702d4145512540880322012507003500c401c0e400d0900d4000d4124151034841890300d40c0c980c03042500d0b401c0c25075004501c0358820360844c0090000d8140c0c1406020041c0c503255109009100c600e1100a009218030010040440861461103d140b00c2d02c0010300c054100003440b0002e81101801d1850040a401085500c604d02d41803411352802e005d02a80e2080f00c0701c54034854217241003502400080314004201300c86a0140b402d2134031004c545001d880c40b80c0c0103e60740c840c1d0316250500d050742036643d21050a40c03188042e80420040804401d48401c5060b070301d9101101a41c59800060f40058180d070001440800304102c60848d00340701c03d2072882002e0090096060b141d212401036540003004030800303812500100036104903403c080c0d603c10b40201c02d04d400c8a444103011811359030304140341d2255030f0042e0403c03020310140d0810b49141 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 406618570 1250 406617320 406617329
    0x30a090209041a0f090c130603241812111c0f080f0f0613020f0d0e15010b0f0a0c080d090506070801080a030e06090a0e091203090a0209040807050712020a 68
    0x58903411305040e01040da81b45810b0749600d119000e019910300d040300c82a004500103661192800115a02038564a00e040e40d0200801c80c01b01d00d40000c1d240300e920950244150507400c180c2a8045070344001c1c0403600451003240301d40d1144650721610066510809541d0340d591f050360b60700c41e0800320602c0b004000034800f030300c1c4039170310303488079007841038000144a20582001040344e813542110909100e80d0007034002e000c8240b0780e4140100700c801101640e5002084080c40003019120719102c030418aa007246030a00460340070030001e0284240d0808500001d000070555418503500c0003000d942c071400e180d8044005401d034580c0301c13001003082210400146400420741e00b480707070440d810001c49a65032035a41c3d0b800380c1008864100101c0720740f02d48046171060768024003115601d03512201c04543d096425208900584140c4102d144240412002d8900564a40780503251003407158080080341000034005403403100040281500007030381000900028003003c1080c8808920034010800c09142c41e912 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 406619820 1250 406618570 406618591
    0x180f020f0409021605010c0804150507090512070902070c0f12110d1e061407020f1504030e0901170c01050c100c20010b030f0c0a0902030a090209041a 66
    0x11000d50400240c15541a030b900b0300d00060b01c8841000c84030741600c501d11000361040d440c0c40b4244e00243d500060192045006610f98148034913000550b408a440480d200800142101d07810f020514120000315a04403254007101c4465484a100300d00320703131282d4821142e007560300004200702c110411f134030001010302d0031019101c0c40d000d8440f00c140b100302110951042080c0e403003210420921030319071300280300d075108940a40c0780f03079241c06002841c3c02c16400355080e0b103100009940904c00982c90302100074403009086805031441400703141501c0900100c0c284401c07151100d8a940301c0c14684ca0081140c03050751141a0f0100e010241000401041c0a041117010043c0072030f1079000007110321500340c2c9500000340c4038404207401c8a02598040c01442144407941c031040e040141500014403941048050302c08074008159103d54510f94070540a8202048074000c0020b5400340d4080c40d8002c40c500008101050b041e80000c01d6008120743c22600300a240d84041d8500504075205a409080c410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 406621070 1250 406619820 406619827
    0x2010e1b031203040f0305070501020409050f15030601050a030b0a060e0907092708030402040b09070903031419080705070f03091d040c090c05070f0501060e280209040213180f02 78
    0x8a03011146001c40c5000b17028000006003235010801e0950480b00280385088040016040c02c0880c0c0c500140186c1f2004045640610f42000c00d24000c580d89040700c20041c90400001d00d142c2c0d400340910030041921081c283d03038440000d400540518440d104142c2c900c080d1011609242c50b21007160012a200350348004100c10700198050201104040301e9004400e41d03880360350700e00c0010043c0031204030f4180c014100c4401e0210182d001f00025040d60320075220119148124000007800703000c4c040070038086800d02e5000c945c00a0042781841d8001106107032252900885440e00c00300d0800d4060201c0000f804442c0c00c01641343c0848048941140005143c916030038180c94043c0700d190b2034026101e15503601d007040c00c0f5190051045401513a0700000d5620062198106540200094404c0c282c403018001f000030040c0c1c10a0115030b2046000030a00d03841540c01c2c90306100250044041d9980265080111002c071120038406000184503110401646200c00c4902009590324111a03915035801807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 406622320 1250 406621070 406621073
    0x910090602030412150603030509180c0304030f110a0b010905070305061003020906120910050609040b0a090222050925120201050712021b0108061e0102010e1b03120304 74
    0x4030464044a401407284d004401c207a04007443c203112819a40354000e890712500000301500040030b09484a0708030390080c410584800210000034003219800c02140040002400117402818013040038a900d1500c40e807100340c0c00d0351540c03030000208000d40e00c04a180780104030b00340c1c55000349544812280f5080c406410000f002ca50f405041072460024540c0110b050350f001e46600d0300341c0b40240c1d40500720272003500b040301c0d6958403004441d81020445041000003201e074100f415182d800746510020041d450b50f03840c0b8004006020780c0000301c0c1e204049443c207120f0090100700d280134685002c01c00044508040c0e02842c6007455006412040041d000c1c0114240c03d00440d4440c00c81c3d07070110320329005615a200413529440760010041c140501c400302c9901c01540051510080c200001300c0300140441c110040d208000101e90700780d84055180301241140544c0507014043d10411300000c1a007090062596052a0040c2480c0030402c8010b0a0740844d13181c2084603000407800c0d00405442c5043c036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 406623570 1250 406622320 406622323
    0x20303030a1e020412020901050d0f120903080a0302030f22030e04020405120303101202100c0213050115120c0905090403020708060c03061905010e0f0d02090c0910090602 75
    0x400c04070800795560440e120a00704028182918001441d00319941c0d5250101d80d140754a10a6090303018280e100d00103d11030038980300704c022098004510340784c0a19559298441426420292010898014000000514881d01504101c202c0c1c3d103016840749070145205101540c0145030f4070312000c0c42814800204842b6940d103400c980c040c0780040e1705072012004100603201c0c652105403c4221907501c401c0005000c00a1030092103084200311410360351b900c000c0c00b0b41c0c3d180180a90b0184488042c5e039400c03130013000c0b0f00307003100d1020b82458011640500c01d4401c45d80b00342d001d01c20110904103500f203090b0780500d03103980008041300c00b0404010882030080ca28103450045078050302c2018049428580200201380003402002d044500340d16154000c40c42c41d8105494290060300d010001d0042264880ca80d60190769042c0e5a00d450a0310a8080003000141003912941080e0300d03135100c802589854019600c100300304c8140641d5141c80a0611203412480c4464004008020006000b0a5030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 406624820 1250 406623570 406623577
    0xc0c0309040501171b01050d0209040e0f060915090d030506040b1503010815130311101a010305060303071502090d050f012a08010303080612030d0b0102010c050705070b0c160e090105060409020303 86
    0xc8c040001600c8514004c045001400d103444034000621807000420350010001604501c1040c00d80d050340c840006070801059124005c2d250a540c0b5081808075000040c4250f05c29035203c20000c102003084450f400105007041c981e85070460075080000018041c684042142c403103248040310400d41c05141104419002c0d2001103802010048604500310030840d0403c40b0441c08100840c0401c03000142d2001c0f542c2c083e0b503100c1100d0109052900041c3c1e1442e001c016511101c1c1c01c980e0440304032a404894038001d51000c4000da501030130b0300722010089181081030603541d1040d000002184101c40191850940c0d1000d069544c2c0241d1904284403507a11202690450364541400d005c142c0b1001d00007542514012a07111091001041e0b040f4103121540081034806420707002081180b1503840201c5c0c8138490b021000d0300340c0e489800108038404051000348403107a00340054410340d480800113504620300d01d42c0500c105000680502c030900b44284100c07600b16108a0f0100110309040e0302003500d0b0b00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 406626070 1250 406624820 406624837
    0xb041a010504091505120105070315031a0718060507051e0307080703030b1806090601090605041206020912150c0304030e01110f061003030809150c0c0309040501171b0105 75
    0x151a21081840f016a200013400a08001849400e0070b9001107070302c0c0d0080100b210720000003402d00d140880010301d00302c20903094982000e15107044251402011034128405003401040110b070501e40419942104902800340c4400c0d900c107640e681d401d04105140c4990011010058006400078400881c0d0000446444940c02105603403200294202540100411000990092400a261118004107424080c45800c08031009e5016403a000c00441d002503aa01498000c21001c10040c08100c05810200c082c15200c1e21016240410500100b1728031008024120700fa5440700b42d080e20f5900c22030640e141c0c000380c0d245050f03007180790030703103008014086442d28141440740403207040503048400d001159550360b4210441d61542041c1100344a070380e2443c4001e4001070922004562000e0001c1000141c8000003401485291034400c45101d1076803001041098030f2008104503004d5440381d024440c020100018080104480c41e00880c0c1040400402e48440c0742408600c921161703080ad05581261 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 406627320 1250 406626070 406626089
    0x2a051c0e01080c130324090c050d1515170f03030a1e05240a03021f021501080102091e0d0615050d12110610180f020d0b041a010504 58
    0x58071907407031030201c5118000ca01d5800424001c0c021081c400b0301034206c81c400c1062a0100c40200d43c001c0003104a40780b40000802000b0f5040041040e480e1540070003040d01e001d80e00c114a849204110706045421440310926001d1001c4c1041001c0c0c0c645030004002c100418000d041c0380080c108000751203101c02480001d03c1540c42c08103017030011085081c130211480345102003000c0c4c200f02e541c9050840c2a80250300031940194041f40075810700e2414201165405890150107042c5103402070046160109420214451481c0c6050f4507140c0008440c02003018200040e81c40880d0800d00c201600c0c00c803061005010201030310340b000d80300c2c0c2910f40d40396a007111001078540414000240c00c016140c0c00598032041064504050010401c2c200241c07024a0321003000811429941d41d80700d02041314569071a0052007000c0000541c16004841c507090070714400940110039400b401e080340c004a41f0b05400c03070340e0b4500c200303004d0400d4031620070700d4444403985250300b104010000f01144541d0107a6040c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 406628570 1250 406627320 406627337
    0x40b0d0c0e060a1205060604210201050f03010f0e0112030203090d0203070b070305040e0a0506031b1c080304051519020702030c03070b070606050405070509010c032a051c0e01 77
    0x10a2140c0d00e803000d5040700900c600e9680419203001030554050300d0741841ca280c9440007140b000c0ca40070044500b1142c603003e94000c10320380c82e2a070481d2142500300607810700408100e8604800b903e41d000718041e00c1c241288100403400d1540382030414505070491518440500e6055021070740000669000400441f840003030070321a48003007402c203101548000500040070034103d0400d41c0000c082d01c03d8440c00c40c07a030080c61703450484600c19642e040d14000e815410410004c0201c6021841d03c100c1200060303c04500032000b000600101007484400f0ba0b1002c501200f4001000f900303019008128400055140040c24040700205aa641c0e0b10304541d5207982c0000d5010445d103040c030610020520040070743d1800c95803040301c400c90b40e0004d041200e0a91501401040b42c4c40c1c24462680518207a0362498101080e510054400c50740071070b01035007400b0000102d0300644d07c48880c12001c10741c4900940700340e10781c0307490440e1410b0180c41014a00c03c6802c442ca4120326440307622480703540e1007440c01130301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 406629820 1250 406628570 406628591
    0x901092f0901080309030f070e04020907180b0a0f1106060118080607050903070f080d0318062c0705100f120f0204030b1e040b07090e04061b05040b0d 66
    0x905090360034889401c024a4000010b0320000131000d04407900b0150281c0f1140008220070f00d4441c0d11500521000020f8480401d0140c141484c0f41d0340c0c400010308111503003041420940704207000b55400700002e103200145c01c004107940b000711200500c5860034810482000d103400741d40c5445001341035a0420091546d007407241000382005500900100c800e445540c200b50700020140e90091941e00e020344644040041c03602842490780046403187c101400d96120210300440250000605203044241c0c05581e50021800611031044402d84089044036502649040c00e502c2d04290507118090f50018141013202e41c5540d1200e0580e404540703046102e124402a0540b0219001e1403150103462911110100151466000f0800c1c2c9000d006d10190f02d43e5101c0385c9202e00d940900c040d10360b10340e905001c00e0000343c1a0803126000441030410b0060182c50701c0b03c0000401e0101c0d03007611410384400307104d13825101d40c400414007071500d803800c5898681840c00c110080d1090800c1784d641143e0700c01e1346a2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 406631070 1250 406629820 406629893
    0x3050903090a090c020f030f0f07020607060f0b040509150c070c0e0c0324010f140c010c034502031c180519030602031302090f090105090109 62
    0x148441802042c0d103910b16240c42e020fa00401c0988042009442454408078000c1c1000081c1c40e841400410404c0c90402c0c1004946541c1d00070920403030704028140031110004003240580d07481c1c030702b41e104002182101c201c01c00c02650009020340c00c541d084480ca0342482c40c58203107026808000301e807815549404900c3c1c247c20441080d80100c240e14901c40034000315044040045002e42404c5141c224144070745800301011540c2807807280e002c03643c0784200320000c9005c3c0c0d40d50300046e260b2041b4181004441c804090944081e41660000255640b00710070908100e40386503500f016006150b00c42c0140c80021031420060205116000e14241841d1328045541c104540380901100c00c01a210311085860050a081d07428925601020001c51021810341002544419021000824084158610b8580400035400500386c2d001c00044441290050703112508140d00030054400201010314201c002d4a085900140105103264100010840422101c80118020300f0420b042c1c0003000d201c400400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 406632320 1250 406631070 406631077
    0x204050616082506050702030909040212010e0106080c01020f0303091213030c03060f0f0905032706030705070212031606020f09151917070f0c060e0106050a09021903050903 76
    0x2000c1c40d01d01d019070840d60b11101003c4194003449254240500d03200c0290680e1240074000300550050040b000240c09071074442d074001d00350b81d48a0f00005070544520480da094401540062a040d0300242d03c0304040c1d40d04102e01400740340f08001071800c505126024075100d941c0d070318204803a01000b04e02c003400e1017a04255080156881005c0c0441f0666a04d0f090024103410000701c03030344900e0281250300196290040348080c640c004045c500e010b14141441c000d410080782601500100703007529101c10b480e058015405051580c8582c1d271125441d1040043c0d002030003141d020143c00c24030000703004c3c8120354040b0100d5603205501580720110319414450b14040c05400a03070040c11410b04108030300d51070009208003003031151460702100c8180c00944014000c2154150703107000d500c000455aa20a108007480c880c0c3c9843c0085044840b42c4172001900c00d030381000d030b6040c0d548000c10000d038035000000e0f03801822440019410681c2c0c0026100c0800c4d10768003000240343c0c564001880c0c625051084 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 406633570 1250 406632320 406632337
    0x405190b011202032809030906110f070e040b0c0a02070902090d0501021303060c050c0309041517160e0c07110604050604141206060a12111002060910020405061608 72
    0x8540340c5ca04070103c000d40c8000500d902001c0114100307a10184201406000c801a400d43ca81d209441d1400d44211520b4040b4844c0c1c0205020790080803400756824400c0000800b100318501700c044c1010705105400d010040e024255000c010080c00c0030303058010944d142140c020450051300d9200702c2007c24030140580100400f19440087c4050810904543d0341d01924050203080160b813200d240113480f64801c04980c00720303d40c800c2c4002189843c20b81c000003505445121202d00b0190354800340f06c2e80a415035040c800e5908100380040c820350344040c03010001c00d410000d10f2203900744a0307249501e17842461005881ca0708021518483c5403a114111801080080c0c90190b0356503407400d0300188907251a5050348101000c1c030703485d8113084001a850380183d81c0100400a19032621a031540700c4000d204003159130000001400c2d40c10303a2404003e038001003154000d064913180901240b4100b110300c00301044200d10502050100391900307416510502848520b803c490149410019170a000e00e034007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 406634820 1250 406633570 406633607
    0xe011409210f030406021203190c030504030e060a0507020d02030f010608030c0c090106090e1008070605070b0a050606031801090b0a0207062d1d030d0905100605031209011701080c0a050405190b01 86
    0x3100055059100074404c40c0203030743f00d00c0391b08540420004603201c4c55042400003a001e01c052009450010960f100380c520060454020b07000c0a8030040c2950a568040801e41c0c0001c00c040c1e01d07865091204045074001254000101d606001000d041d0f900f540c052030f0a80c0c070201c8005070240850558542c058450b500c1190040c65403510010001e034080d10341111040804c5000c64009001802070602406006000034155940c1e010703640300c003074180d80340000301d1341d21610940c001c220641c0d01c00e13000d25503102000d41d540311103040000c02e42c0c2d2600300100d5035440800400c00b003c41ca8a60000b0310800d046400f065014a1400d6071485541922010500d4040000c02c494417107210781c0a0000b00d0311450079a10410348070001c40303044030007038401e064140c0c02203003400790742d208090028507a51703030141040010354150034001a202c0c070b02604150a594003841030b8820070b2900c0c6580200410303084030244002d1420145e621400e2130703442c00240029848076080b01441e8083c85408000012584 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 406636070 1250 406634820 406634831
    0x412020103021b16170a020d0203070312030911032b02070315021b070b040303050f16060903110a031704030e0d060c0906030c0e011409210f03040602120319 69
    0x43c6850f0b00100360304c454022107840001558480c918030022110f011a4050004400d2640a0114100759000d0403649409061000700002c0c81480080700003e00c0c0b55000a0301c98150310f042c07070820042d020824481d9020700020716401c129000c410034803c0503443d00a006001410717050f031418540b504003d10030140e60b0300842c0b009800d42c3c0a13207040c1c1d03007440e50404c80c800b04242c11901e0b03600e60b000700c0184840410041c004207000320020318840c00c01c0e41007540b41c04e0004000c030343c082034250412140d03240c81c1d101c0c150516130702c070710140e100c002c0c442c002d0018842d00f03590152030101c04c5c02005c10410140d10004007810b000318051002c2250281c0811110003051030300c4001812482d01c07000c04103020031800304400d4482c3c8a4032507200b8079503c65180c400300000056410b0a065104e0302d84502c0300300010b043ea9112145403101c01c0340c141a01d5480d410700c10b0817070f6040040000c44c000c1180e00038402008510744c0020601010035203000207507238945984200024900f401e03c55200301e182800c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 406637320 1250 406636070 406636117
    0xb09250e3405180904020604230d050c01030f02040b0919150503040b01060215040809150d06182315091018050114042f030105011112041202010302 65
    0x1a0040c000c0c400002c200f26a01600c0c4400c100d050310003550081d42001040c001400ba02c4142149050b24076840310145115220110005042d04000394044403d40c0203009035601e00e5815028064002131000025418603040594858490042c00000ca10403420b0000c140040f18800039880054400c1400380243c220200c00050403a500c20798040307440030900b0000180841c40401c009130f9420701d4203103140060311241c6502c1d226820035482581d214800200180c561001d4070000c19054902e441c02003100e61528189409040201240e0406541400c0c3c041d41c52481701c0e810130030040c02c254801c13102c03600c991806400800c06415081d4005251600380000040c1c1410480100c07400d00d000b0140b560500301d40c9006480c030a1041429021108100e2262440c2c180c01150b030817803400900c1059844803440c54081c6286160441d100d036000040184805d50b48584410381d008401c00c024030100201809040141c4a20311918120301c4107610b90004581c170907011142401040f840d48a04003868 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 406638570 1250 406637320 406637327
    0x1090506031603020f060d150810060b03010f030f08160804090b0111060621100b040c090308030604021305061810111b0604030b09250e34 61
    0x9541040c4248a2032001c0c002e41d094036080d1a066903406044410306495000c14000d40ea0040aa040c800544071040e40d0350401d10964031000514611004003080c2e0398441281007100c400d90003030040040e04000500c4010f2100325140203c903408620360b80000303036a05020203e13000b000040d6020b0003401c0c24000c00d120708038000d00243c4601650800140380d810005407130f00c101c41000c45400360000340c0020b15514090316640d00030b440b80704143c40180d841e1844181845041581103840c82d0341c5289450f00c030b003409e200e0004188810b08211015500390b0329206101d00000300010300c542c0c2c00203856000b4080e0000d00c080245805420b883d00c9405107800c0704004500603030014080d50441c0220b4114610a02034420300b0300c223940103005c4800d11f4010202d02444180641c81e0052010400080016040703182107204500e4032010b805000c005000c100c1c52200c0d58404011074500c0d030141403001c1542049103e4100c00c000318031415000b41c1a801a004004000200540340042d0f08100840c1f0342 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 406639820 1250 406638570 406638581
    0x60916021f0e03070614010e13060e030c0d030218090403080109150504021c0507080613021810181a0406050903010902060d0b2d1302042103110705010f030908040503060109 76
    0xe00d40c0c00d5160303807200e041c00f1040c20308030341001824827001054001314000364407240010600005a0389441d425821852500022440c800c0010750b0015003410803100e0510f00442a0004448a005a0400345ca0080400a040c00f400d01044c0d6200e00300c1c10b10400030f1104100511000e8030a54481e06000b606889040314030401c40d00c41418800015a0103201d036040c140b04003002002031440d0032407001904002d4111071001c00c640c0c2d8808400100c2d560700d01507011038000265640c0707810103541d51150440d15105a2001c10301c0c1c10850b8428900707121003800d4030309940d03951a00b903032524200400240580001d08029402c590005603804503a00301c0d0b0400c81f1110415244144070040c020209030200314066844060011141040c09007442c0a042820420202010140c182501c504007548a8a0ba8a0200304d903c0c905c65006410981c001103008080b18003600034210030343c90200080d140c42040145441099a04e502d241c0170054100195030280ca8080c04075030027580c4a0490500505 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 406641070 1250 406639820 406639841
    0x10503090a0c06081608060105041a13080604050d170112051006090b0102010c020f1c0c050d020307120f09140607201c03090b1602100206060916021f0e030706 70
    0x8400301065003406d01a030a603500800040e900d0915003803610b42000700062011a0310359200d8803c01140c1b10900405816801418220011b000d49003001d1a11900d000c203042d640c4c0c002e0082e104004c1c0414074240018504560700002c890902c00d60f64580503081c14259040041100d1070800081080c007000d5001c40e640d55420f80007000782e05c0803200300f40e0740e850095160344540d038442402002541162003403541003200c0c508040c01c21000a640c0e43c0d0401414884000041c0e002040741020b1200c3e03451620140c106c0c5080800100140032001850350b800380c001d071001417005141c0900d140d100c02007122074480c0c104070402c11923041524185141c0c00c0042e00240314050304040f44611454045070800720395410703244c1c0c0b05524500351003411240c1017000340c445610b8011309540e000d40c84400d0300020080450303014084e03905d8100700701f080c1d003003014150701402c0385401c582075407568001403080c440c1340c0240392540800f545048540003030301c104000142075020100c4d2607420001150007141560 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 406642320 1250 406641070 406641091
    0x903090306060b16140f07030f03080c4012020f031204090c020a080f030601111c0c0c090e1005070f0801060507020301110301170c0607050c010503090a0c0608 70
    0xd642d80c2800449900600341c0700313a8210881d03103601c0006800016540c000c2c01d404401d8032250010000340c1410036200764015070300042c0b01d041c11020503a000c40596403000d110705c0d4940c03c0288000d01000b150380c411107110325030b4007880784080d4803d086a000300540d0403100701d01440b007074440c0703200c0c440c1c0503003141d049024007441e03411510329103004642d1003105100c2a405034206490002c0040180c5824644c12055000f10308211000ca08080000c290050985141d03980c1c034180b4400043c50f01c0312429401646821602d145250110209080b44801d58903280400c2da80410782070666a8034490342c45011040e1030b0480c5500740d90300c08640c2140c61180f076041000300381e03140c4205607101a9290868000070300c0c040018807070503000380c003d00090f41c0040c0001a440311041c20b011001d03482a0002c1002414070002c0c03040071641040039011200f0240c410700d0919082e550b49a035210720120005041c0540400010340c0b00804001d0102c034180c102e160003096030343e41c00300a00040016580c16210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 406643570 1250 406642320 406642331
    0x9070302120303040b06150904020d1d010903050904020a1205090f06090304120f140f0606030d030b180408072004050603060f07051b0307060605100804080d0b040e010903090306 78
    0x112000030055a1103141c03c2410340340646d0302c41e0b0030480e0942c212914840d0300c0c00140f16442c0305849071700c003801502c45020000611583c0204400c100603080d455003400b2a0704001c02080040d9001040c0d8070000e0341694003584503103c0440688040940a80c071004803842c00082041d240b00000300940f0f02c03032490083d200f180d1900b0041d26224801d60080441c404c0100c50504001480d0350440c2c00901d0190381180040003034010350a091801c040c0f0190313082e60286d010b012042c5414840503104403242c0c14104040b8000c0e201140b10249202d00342d210700401180010107010110007107031402684040c20404046000f000d003005080c010035a980958a0440014500c0c1800604c607800b400c503069a0710640d9940c80e02c201c03869884640c0400401c015082480903c080070009082c08900c14040414010300f042c1c18090416626034440d01003002e80070501c000314a0100881d038250f108444045082841d00c0c010602401c000300000d07000d0762810114006140d8485c0c00f123000d89124220030b014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 406644820 1250 406643570 406643599
    0x51e0a1a010e10030b041509050d0c03180e130302070b030c030a060902040b070f05010e070602210901080c0d060b041707060221071a0f1005100f03090c090509070302 73
    0xf4050450000404803118140401d0104071901518890701c0c58003040030907514003950307400741401080d0050002040b5000c0c180c40c10507800a442d5205040844010620b1924007205c02c0c413080d07000340c1100181d00812800e60141803007880114082c1203403031800307943c90601903240c1c510342d88126004180a071400f00d000c51040c00d14000c950444501900850900401d501c804a8a0031020021201d0750342e1034404115502c01800004c0c010100c540103803504000403c00a4105440c498030384c0884542001040d1050303030482e030120340165110f03500c030743c90780e0760143c2c248000c15036500709850b04880403400144c4090248002c842c40c000003400c1d501030366039030102660b0321401584074403000340d8101d841d001000d80003c05000d400340120020950300b500100c00e040c046409a8803010101c0301c030410080790201007500d0400501c2c0a070380f40c1d91800c00d20300000b0014000c640c5000101030700e0310103500500c04440a4030000e407841120400135400c0c108001552100c0c6888201c0c0908854040641c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 406646070 1250 406644820 406644841
    0x60703120c0201110319060e070906080c0310120302031c1d07080c0103020721020c1c0c050d080c010c030e33061c0c140904051e0a1a010e 61
    0xa0f5080104d44060540c0c440000c06000c046143c2c4400300382c0c9994200020300b400c0e00061a5014030000d494450035503040002c02021140001e02103401040100203201c0003541d43ea041004039044249960503011443c60100d003075200c0c869454031003c21400045104928a600403821845031041c005014032840d0700c06038488400e44a16045900280f100300700d194060b400400c0510710130380210103143c5200401085042a50441e00e0040c1d22000c2c98480f24100000400203085900ca6608600080e40e50390040180340c3d030007038074050401c0002ea5810005214240d40208400c2802804130303244c81d0700c1c020010811185040d44510030542d0243c0e47e060050b40c11203400210200458040795014110345c1c07400320280c44d1541043c40d180540c10544021028004100d03c620b0f45400c0691401c424440000c0586042901c25450001880002540011134101110716001141c11b41820740c10128245a01e210015140058031a00d4030500c180e254040c0341a5040410752201a0f00c4650090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 406647320 1250 406646070 406646081
    0xc0f1b03061605030c04030203071404050c120402060f0408150601030507030e07050411070b13201804111903151803110c060f090109060f050a1b02060703120c0201 72
    0x16a410784400c441c0c400c0d050f202e2001190b201821109440c82d080d03881e4046480d02600b40c0c41000c2c81e544007139540002e458640512a04403182c44600d83c00c0c100c2c244146150140043c0000703116a800240b1000b00318040400d880c002d1610000b23803041c500201e0b070b1a56003a04220340050006e841d090010710b0041c0248035440650881d04000c06509040c107003800002c204607142c0844034038049c001480080d102080c801c1c80b5001c0103010b540041101c1c64124410211000102c1c10180c1445140181d80c171404940094242d440c0940c4480d91624107220f4014020619031030740011450790414801d4004205110844c0d00c00e00160f8030b030300011300889044412101c108080d078084c0c01601d00100344207561036850b050883d001e4030f07061030310000095115881000404211000402d0b1709804d581c10100160080200e070801e01c0841c1c1454400400a1081001070001c1c40740044403001310f05080122185003607400303001a80e0b039405504014061406c2d40301500e561038101008114034502c18000d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 406648570 1250 406647320 406647331
    0x504030509030f0d0c1401091b060e010f0c0201050d0603061a03100902060405100909020a0e0f0f0a05060f0f0a0519090605030f06120a06020a0212040f0b07080c0f1b0306 75
    0x245080a0400e58806e4441d03805905011001e46d25420007001142107807049880c9400381c2c4c0414082d080c60080094045101c40d000300f810b218207103e00e00c0890390000399040c03419509182080d43c801102000000411264201078101c600e000c403804401542d5a1602c0041c020031800c844034158402001c0c42503c03203a590081d000720b0300340310800103400c080303400007040c0302642061059161201c0b9440c1c2260055454003000422060140c401c42c00c04948580031071a058400c00000d015500100d04040c0961044a028182c0000c4451000450070140c2c0d110810b820b00840c1d0310021210014002c0d0003a4001d0056440e042c17140c00580781c05082c030007048540a0301c0321810341e59010515515040018801900f01d4110030403d5000f038824080010441d10414005894280d01d0700003c0c903040340490f400c10800d204100600c20080d09503003403400c030303204030002c26980d44c8503181420303881c0a0101c0d44000d40c4035800c1c820b0403014011400000c1815411204821401c405082581d103034025541c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 406649820 1250 406648570 406648577
    0x613090b39070809011e09091b08150d06060f0504180f0828091e030c0b0a0318050709140c090103051b070605010e09120415120504030509030f0d 64
    0xb210014104901400707449405040510030304440c80f20a080519a01c01a08001201081e082c040100c1510a000d6004082a406001a018904007410340d507405400f030b54101081c03a9002c441a038070300c50b54078101a404803040c4003560783c59002c054105010f0049522503170610281440102e03030040e140b0743d0383d9003002c01c0041440741038403003c5040c0e1109030071606008100c0204195840d9010034400300c80710300c0d6640d0b40b00a1824a55000d0809098440b0700599054682000071031100c11a030700594603500c05203540c41648450035402041a0001e60510140c4070480301d0601002090360f10445031090000e205410b84081d1104604404481c90003104405219420980d442035010759408680386010454204051480c0c089070340110004880281c0c0303031001405010036120955800003000401850135802494515605000c0c500551907119090801080c0c054465502e40c00700100c0c0ea04104507d00b803900b0000c2c900e5001030b94450091083c3c80c05041303015800180c1500342e92a565 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 406651070 1250 406649820 406649827
    0x5040b0a1e0905031b0c01051e0c010603030c0302070e010501050f030415020f27090403050d0b270f1510030b030d080601180b030613090b39 62
    0x100c21004050150118503104024007060824040700e00c100040039014200860300c8404151011441c80e844e0030100c2c0b401d40180407000316998101d401d80715103001c0705c1c100700840764810500249501408800c0382c16903082a0002090513088000b12000f18025425110540d803210000f0b489664203225403400500c0c100400941d0b01942e0000d035030000d100700201e0811084528021050740c02c4491003041c6024002042025408503404640303100d00401c542c05014200000020001078004001a051003400105c2410510f481c3d80052041e042c01072020404030207949004c03c4405c1c0d594402d050303d003c0c0001040c2045445854a4032078000c0d000c81450307003001d15092010b4030b884a0a0784042c10345918485420f0768040c4848201e600c071540e1417045a10f0002c000500c00c50160f041000300280004040c0012040001101d600140a0f210003540940302c0700841d0040c00c1c0c4020103070440d003e40d07041c8007204688142032603004960081c41c04056420560a42110440c813640c07488194080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 406652320 1250 406651070 406651081
    0x3010b270c0f0f090d0b0f0a0c02211315020709060503010b030d030b2e02150405071214060915061c061a0a0305060717060102060403080604060f0803030402031005040b 74
    0x24504013001400041210b0b00d1039072110b180e0f08003540c14a0341c2d030f04040700b00140821b07244640115403a0a10061182d00079000c1c0003c50f9070500380e5220032044001518001408101c8841001070001d0000090740c0300d0703620350003900d90310725000d961403550a05800040324641401038800b160301c0140540101c20500c9401c5d0020700f4585403d60f0003002994140448007004242d80d03001c42d40612f1018540440120028140440c200610807500303614802d000100307070000f400c10b040d1444c03104100f01c480b03464202b02c0341c5800f1480101d650b80c4108402c201e035522000c030713109906005c81600c0080c0c40d01c0da04104045884110700e1807034210811108900401e0035604a00500b0a000301c58060008088011548102d0a904152038a40c071200512038010f500010b1071a03480c0303d48644024600303001e40002c0d00d503000540085c00700f1440d41e020036241e1392035a01620081890306103007c882691400c0781ea807240c10864081c0e10a010380d4008045450441c0205441594442130414a65641 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 406653570 1250 406652320 406652347
    0x131b030e0606090702011b09050a09020a052203081b01200f0310080114150118030212010e031b061f060f050c060406020301031412030a020903010b270c0f 68
    0xc100101719034840d580080d5103801440b0146080780142e40310215541000c0a0000c1014a503000081e030310710401407600d02542c458180c0d21612084c0d441a014010103152034540350860303802c003411007400001c003840a043d04a10300100c80501c90024040100c00d01e0112600c0001706115441820341044885c4111030010001c640c00340400050740b02d079545580c015402c60b41a140c00c041e6101c582014026100a2a1000c2500e40c1c401d11b800d4440301d15440300484011501e00c002809602d1000b00c031506480d003034200500307801100c2c1c126521340007000941407442001d4460070000d8003035040800d4040300746150354a00c4440c40130301111800c0c40c002040b54081c0b84e40070701c40c040140c1402012441c1d001400000e0045006d081c0258695056042158040480c08030401860b0b0084440c401b0704035103a0160381d03001c0445440181c40e44410300110340540410300c0441d034813620010f02c0985140710701d8000c02d0214410000f107102951142c3d0006010b1240c084030481070002800101d000c41038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 406654676 1106 406653570 406653589
    0x61a120f04080d0903050913020406091a1b07080f1e010c0806010e130e07060e0105030411061608030a0603050c060f04030209040c05131b030e0606 65
    0x24155107840c10b0b0310a0304412000b442e100d004501c10300d4021016115100d41c00b0b0301c0d0340c6c2141c458480100003917002c0d0041d5404561a01da0120f10300c01c1c030354040c0300303900f00c4640700303d00e4401e43c81c1c201a044000c0d01101d006920035000701141c074100a01c00d10090180080040402c150900e0f0300000c40d040d41d047c20300562b854902410002035105007980d40040080c2000c0b08140300d20400302d1b4444d146d68000d1144c02e8103000e918405010700013030600803a2603c1c0e42e142c80d0b04045034011a1f06110660b00942403d0b4072400300c009a14000d001410032500c0080108000d0034990303030f0190140c10845089154030340d02c3c001001805401d0084811944c1c04488640c548007040091240701e000c2d6020190280310b540001030200081c003680301d009040c004100305000010031702c0207000750000003180100d8101910010010a000c1e0140f082d41510b84d00c090000d542d1540d040c00710401 = true := by decide +kernel

theorem cover : BRFrame.Cov 406474820 406654676 := by
  have h0 := BRFrame.cov_init 406474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 406474820 ≤ n) (h2 : n < 406654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
