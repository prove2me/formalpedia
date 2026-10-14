-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1245
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:57:49.790092+00:00
-- url     : https://prove2.me/submissions/7d10a705-ee61-486e-a02b-a128ec00f449

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 223741007 ≤ n < 223920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 223742257 1250 223741007 223741027
    0x1309020402040b0711040b031213030516080708030901020c0411120903090f0301050f070e0a0e0f01060f0f08011404090602190e01020a031b03031b030911181b 70
    0x20760010b9200c07203c64140400c0d00300030481c4c0c41070071070707010201070b40c0c10000390072500c1c0001c0e40d481d548481d041946038001520800340c000b800300c170009960800101e601c1e03011041030703c0c0c2c0a00320038403c6c40558024a030000c07075030501c0801250050401640105000b0084d401048010300e916070f0a0070440c9010044803095000f4403110901c2030034940043c6845003000b405000c0890310000714144079074500020090010460911150003600ca4900010011910800b1494040d003540281c008070241c242040b4050702c2c03030ba035541d050313a03200e50301c99510340106a029105104d042c18103d000c82c00c6140140022512458104061880100b003c194204130780c4544080313038001d000e4038048030510314a20015640102d22201d000100f803008100103416528010001c55001d03441c5400146110400e405051081d04601c0c0091802d4041c000000015103015000344a0180210341409511540912341c0c40c00d400030180f419100c901901c00e9681d4105c603050541407031001003d900c3c10070301c20881d803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 223743507 1250 223742257 223742261
    0x60c07030f09050418050609160b07051504050601150903020105070311030f0d0e12210a140a09030206101d0612070806010e010b03010f0302061303140d030608010b010801030213090204 81
    0x100003055a17424038060502c0c1040e0b0700341100280a2545d51384100300824071883c8001841044400ea140240d89401091511074180b5070b0703540240f01030607403034018841484404a02d06040350707005400410b07101c2e80c00310140c0f4480e0321031002034049482444080003190150103520030418482099904d007410f04441c103029a000303813a011002c15a51805055060070411014503a843c503d510075051000d100c8440c07801c140d600b00328100314018000429110509504000c1a401002d80c40c04010315100c0601002010034400a070014444e08001c43c443e00720f1841d8242c2924200c0e0144520811541c00300100b009010307008581080d0600144212030006101450240404402500e08c65141070304014001006801640b16010704000410045080b0665070081b00e0b03050f520903894030085107004449220760b60004e411030f400c4001c0414280310100d003a029611454600300301d003d448007540750807500340300f175018080350607900103001602d019000c7c1040040342c0d61000ca1540c1c42c40d400700301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 223744757 1250 223743507 223743521
    0x1505030607020703030206010506070c180906110901391110030606020d02010e0a1e1203020a18080c0f060d0f0209040c1701050906060904060b09030609060c07030f090504 75
    0x801600559002d00405a041c01f4440c0102001c40d60541031800c1a1203460202e81c030703031013804c0c0b045242100f8903140382d40a40105d036000c0c3d048441003001c0c0b1101804100c07250302c0500b070103001402c22189408403d010818500001a400c030725112450300810302c0c913408600c1d5410580304040c01c242c81200030703078603a0030703840201c401c5590115540d89014170282c40c05042c01e40d00c2041d64140325605511110009100740c1c000c0e00620b105035144040c1c0c1c0403d4440c244040040c0100340307003950044500790150020816070707280b550344941c0300c0005411b0740c0d0310f03441c1400751950580280c240c1204502c0c0404414002c440010000c62031710340c904400c0b4040303900c0c4001d1502242e40101e400d613458606480b401d07a001b00070341403c07181d803001a44006265070050042c01d12660090002c1400b0313031100300a666006101900030440d054a40701d2020b2107030011400381d2700c02c2c80303020000b07400143c0108446014100b11250141003d40d0703640c064070360203a040b960504000100d600007540c0d80e11070050340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 223746007 1250 223744757 223744771
    0x210e071205010f27080901120216030e010302070206120c1b07031506030b0a0c0201060f0e0a060b0405100804110405010e100603020a0e0114090324010815070315050306 74
    0x301050704900074404d440403010941d499494840c1c0358500301c0c46401240c0b6041d50700c40c91403076a510302c03100180c1c0d500c26581d000344003851000c52020644980405c60f902c0050082e00c40b2030300070082d83d0046080c2d02c50f03000000c2d0840c2050014040711900700f100c07176801241501c1040c1c05d0465600030f040300d802500c440744620b50300115081091101242240f461000d01060a0140c1f60650702c81c910000000740a5030581a600c540b000344092007035000d00f018000020b40e00e082d140d076803e00241d0b1410f003520045a00e610b812070009000124030215802c603400503020703040d08582c590058800000007002921703001c02014070710845948512a5601901c040f052032002410b10b0140e1480008030350300010181881003113000402904104072402c0e21100b442c107803951865100c20b8480c0e0340100300c0d42e59014442c0001c004262081d400403180d92001c40c00d20313180142c1c0c2e15070714250364401600d055800c040c03182020803451440382d00a4542014810780d2000301a0b510710200e0314001c0119052 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 223747257 1250 223746007 223746011
    0x231203041106120406050f040f0f0203100f0e0c06120103030f09080d0507230601050d08190f11010207030504260709021b060f070f0918020d0c210e07120501 69
    0x4c104140e0340b08460f00014205503202103440c055841c103c0300c0b08801d1000d0000d41408040e042103580c204644c0c0c0007a81e121a0500c030303c810381061a406440c60390710b02c08050140d000380540340c0c1004800d46450002d8204d42c0502a4610f03101550070021500510007008081d03a408038a030b600401c0380e014041b20b5590350640c3e074165401c2004040303120301070307010521002012110600c40300144441c151b4004641c6202c4203103c9180000c450722802d0700e04c0c8032025581381e0702d00c4202e0b004604595007070b1040c1c45000751008443c01107402c0f0b100b0004018040f9005000c10700410400b19241d4640102d00c05540c403001c50051000d510f003030103d03884800e0300b60300054002d50411100b032054001d501d0031001482d05050134140a5100d0400030011006c200c1054040d03283c0510072900070303004052454141e8100841c3e085110080d52040485060450801103118403061003444407000c03d40da100c83c071402e0401e6402d2800d000e481110081c04140c481c004000c500004850740b205106407280d000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 223748507 1250 223747257 223747261
    0xb01021002130f09091212021b010b0a060c05030d02030a0204080f0c0103271101030213080601050a171b01031104060512090109050307080903190f23120304110612 72
    0x5244014643c1114403c681805c1c00c0500081c4a40700c06903c4040034100b04105608003007180c4002d0040f14180c24040d8045501d5075403403001940b0000d0310b55015074003c1e9240b5120a4103079505801c8050003006079208020080e81c04001d0360113527401c03010203040507140c142e407484035524000b100070f06c11800780c106100c900d03d03968161003200340898030140840d480084a0340002c0242450b00f00160081018154620b4541c1c442c4c0c1c101e500d07050031803414001a40c0c940c05a5580c0f08401d0281c64001d001132100458036000803400072a0f02c111001c000e11010b1004003441090701c07d02800c0718113168692400b0300000509130050b2014148942e500c0c1c0d110000c11005000b16400581a6001ca914108003503010400c044100c403241500700b4035a83c8d80b1070315040031918048001d5110308104d001c40c000d8404100c00300d035005800a0244441c241d00868940031503998141c0942d168465a00c03104d0340075100c0c2c0382880034541c864061820600e007036411101150890380022141c042159010341 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 223749757 1250 223748507 223748519
    0x5070b03090f0c01140901031517060106020d0201060e04080a120501080c01021c02060f130f0f060c0e010f0c0318060504050907020a0308040209040807050a05070512030c060a0b0102100213 83
    0x32503d49055024a460180380300d804507814051300c03405826504060319200000c2d0401a4510408000c0055502401e60031120703070803040e15880217003d400010700a85c000003141c18030500920301038507018800e800550b1255070382d81c4000d5001c4407442060000c0c054008052100c18440d40d0f00030102c41c4003030000d01c4001030009040102511401c0d1103007601c40ea088510590001d20590b10105800f607110054940b22011807095101c4240100300100600c840c40400c42c4504d50f1040c100d01c204410311144d1801001611107411500503180051000d214146000384500c004c040954020708244490a4031413141381c7c0307060010303000440445c40015040106007071500500e580300d100c44c80030745034211903954000c048040162004e480342c4000c1d000304044c07159074811204415030000807580301a0291500c075855007400d225036880b800311040c6640c600c207004000c40341c0d0214800082c01d003680c8e8513004240107241525a0b141140704800f8800244110341c4002d05075400d0300028900600d147c41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 223751007 1250 223749757 223749763
    0x6030c0909010501050a061d010302091c0302072c16180b07051501120f080918150109050d060e1203010b070c05060903100c18140315040203071205070b03090f 70
    0x282c422010007014601140c0d00c6035503123016080c0b6440918025907254022000140b0250050300d00341500d00740c04120304201a000030350042207a4850b40c01c00071042000b07100700d42010510072008a030383c0100e0b002800c0c8544403203150900d03018134100b10300b54901101215a07800b070382d504010505036000810b00b0a1100c10002c41c1d885441d181107607036003581407440100e40104441d000400d01150204148100310000055034030303500000c1c09070b084448001180f00c4105c91305941c0400b40304100c540c1d0406951103511720806855024044287d24240d994900000703104074482e038100b601400d8205160354000e40b0040d802400c03c00921910b4100d40c3c00e0018650900b40e01c490b1160104028003583da480100302074508955002c000281045115801d844c180c016030450300c0c0ca29528100491071882e01c40461041002c1a82100c83c102040b8980001d10701003900c020b50b15500600041110313240c42d12a050240b80300700282c0b400603646100d00d41a641041d644081e86400044038120026010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 223752257 1250 223751007 223751009
    0x30607030c2714090105031e0a0803090a0c05031902120c090403050a08070c1a0414010f1a150717120a0b040b10050301170a0c0f150503060a0e06030c0909010501050a 73
    0x1320781d2440554036102c000381d91288015811141c0c004014038048804109015001049803c0745c5603560720303e40682020344486241c9000c0780d81070310200d0041140c0c10000382c030485124401c29401c90701181c0d278081241032003801c18038440500c0303201d078031001e10f407580074149004a02c0390311090b0302d0300c042c3d40c80038103982d0380100007004101001030208042141b0013a450200036203076007418403548450030a0000e02c010740000440315800e100c42041300c00c1c03143c0c0c0030b030420b0b00180030748c41e10030312101d000c00401002c0150454614034040c0300c03030000305031800b03690010382201c0500145002d1540018010501d021a40c1c0704c041942c0c0d00200c500c0341031074000d001400f1800c80d0554641c402d02c4801520600040c0a41e081e43e40100260100742c6000300504111140c010483c90051a56100b2210040c0c038140280c80343c4074032501d00403000d94015000d4900612006081040c1c0e1811328405840e2020007c00066140c8a4040c03c03800b40c4d00c6640d00b850041c2685400842d556061105010b806241 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 223753507 1250 223752257 223752259
    0x20a0e120a03020a03030e0c0a03050c15120c0a02161d09030325020c030303040803070207051c0623090c0103060605090f0411090303030906010e0604060302030607030c2714 76
    0x70220200c4000ba502040003201a541814001070361a5a003c500d8a0800c0c50013507550032000c5294088280000016a89200d00c411904500000a40f2074081598058000f00120b8005a40c0c0072811615040014013240402407040321310a004004520304009034543c0481c00395071940d040c5510706040000e88907800782c0344100840c40c50910780c54a51201c0310b1481d1500000c10321028950090b442888130a440c810000c0c12030762681040d003800d0400354020707a00480944101d643c000352604008411707611864840003d01074004136030b19440080e21640c2d205480340c1c1c11a00b03001c400040e050820f9800b58240030010458155654005011039250760040c00034080f0901c003e51966403004502000b02000395000705e032440c0d5050f0480198002d5504665140c00003004000340070200080150483c1e0010782000c24030303180c010900044504900010b90550440f2000070540750113500308002e0004c01c0d10300130400108032262888041000301c9240b12054100b10204042d05950901c1c4500c2d0f00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 223754757 1250 223753507 223753513
    0x6040f1a130c061b030e150f03220201020604121b060c020601080313030f020f150c010c0c0807080a0c350405090103140c10080f1303090b0d0e01020a0e12 68
    0x1130b1062440381c0082120000800b08018140e070405552901502000030104103004c40e03884000700d03c0500341540044441c01007465003070100034100251500c001d00826010b8000d0080e035103031a1502c0740c098500c0d07030320300d001e214221711640d50103c1003250039201c1768095100003038009090b1600a0502c08181e000c046142e109001100d009001d185080c07088a900c00f803151031400c1140b0200d0700d205030000036907502041c1e16915102c440031500040903e102808006c00460610308816110100184805401c0e04014800c03038002800e200b00410b5103075030b02e051601c00c01c1c00755038500742c19280010350903805c12195000e42c40074807048030a0400d10490780ca2010b08060800011520140c4144800f03820f2003066000007800400900c1410005480900440070609110310003404001003500c90300200310102c400981e02c0c98034010416041a81640e03000a030314038210090703c01e40c2080b007900c01071664072021004920405d200030001219180c46400d042da04040410940400301e14044078160 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 223756007 1250 223754757 223754777
    0x114010b090409060b040609050f0703050705070f020325081002070f03080c04120501091e02030c040b1c050708010627020a090b0a0e040e0f06040f1a130c06 69
    0x48200181c446214080da0002424803a034200303240a060405490790b001403620402184188503500440d1040014818100940d102c0703410440c1240c07401c80f00d000c0020000c0c0306d0400050340c50300c0c00d00e40b110700040407a42800844491050f46901e100c0c0e00c02e0b04061042010013040354244425100300880010460902910f81c07607403c1540ea0021004040149a80000304000300359003d850141000c4114843c40514500c3d14600911403002c0070342d40c00e01001c4902045007204820752100641c00b4000d00b60414548007403002600b034200030150302012945c030100f83c2c1442d4134041100c460040b8010002140746c0300e08075003101d4481c1c01c0b500d5031300e003001040d005281920171095080b101709600142e45801c15441182c02d100c158011031805040000c402e00750b039610048018100381e08071400c010502d44000c41c20b0703030380302c901c1041422034201c039000038040388000c4901502240108040344011008001343c2007101d008403204050080c03290b0241051124202c1c48a02803c0c140c24407256034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 223757257 1250 223756007 223756019
    0x60406030203070504020307051905090a0e13020d0816050106030c060801060c0816170a021005091902030a0605010617010509011d15030607020703060b150f0703090812040305011401 80
    0xf46019010380c500440c0c001000c92440c034861b00c11100816880408079618141000303000301144e114080d200e10940520401180b484481008a40142c40c2ca41d0a4205100b40f6824486d0548020341c007515030407814880e240210201100b6001081e110780300010b841810b61410b1801500300790022010014250014052070760800b09561105410440c1c0076241c501c0560700c0c4001d030071600c4c40100106003000c070b1811401a18009031074481d2280d02600c04c06506100500c04032201224901055032100ca10010038200d0f4000c140c441a002038141e51108500c0c4e1a0001900c400b1303030282d400242e45141003840b115540400c4d41c00740c00e048038240425454070308440401c80300c52000d000380aa055001c201e080c0700c0045150040803000d4203a071500c0c034000750060745a001911007a2082c40c14648110801e161141c81c00c00c080c40100b03c00740c1400a00c0100c2c1c5029006080100c00b400811100445c0ba1081080100500d400c0f0345d158681e0b503030451800b10b00b51400c00d40f0b044c003011180c9005001d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 223758507 1250 223757257 223757263
    0x106032a090b061614030a0519020a021e040f14070215060a06030b0303090d03020c150421080d0e0d0e090708070f09030b0c04051503070c110a03060e010c0305060406030203 76
    0x51380403003800c004c03030210242010a00c24160103001001807000080b114083c50b0080c000e8009070194403d496044441854103a1312500d000c10001c0d8003000101d42e490100d010340d000e0308440312016000048030518181c0d0785044482b600807540030b50030703110200301e03503113904000300390130b80a000ea400d211506202c00810b920444601840c000e064030b4591030074050710b0810640d5107410b80100311240016a03410003940340d1210f070180038000c21100b0744d0341e060100410103c90840f000340704803202d0950580c13142c005664451604583c080820003c0d0b14075900140102c10242080c40c025142030003580001a04400140b240039006000610800c6101c2e5040311341294070402a040070ba4440010a8080315000c9160300003d00d00d40c02207042c0140b1800c41c0c40a082070350000d43d5000007005811001c8040f0b03010484001c8001098242541d00050601318000c055402c09000800c0782c0d40c0703984d00e96061f14440c0e10700c02c842e07a6540049900c095030500071280c2012090300d040045c1c0e419a004a52 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 223759757 1250 223758507 223758517
    0x50a0509090403032c070609050631030b060f0d0b0711010b060a0201140601083c0703020a03110f070f0f0f050f0601060504061b02030106032a090b06 66
    0x301c21245200000c051600a8108807402c8000050380495020411200703030300c0150103244034001d841845d0004c20024050f403a0300341a00d00092405081c503010000711050243e024007180b1502046190300c0349008010303404540a10311600c400070580c40c010050007410502c0170f041610554443c2001008034054840254002c1d9081c03620001c1d00801c0070300e190251083c501d890b500040001444000c0b9a03040d401100c00f645950549051921481d004440d0b143c1e0995010381441c038015070188401000c01d81e41e201301801c002c1f14a02c3c10100d0150902140403c403402000302c4c4d0001401d000195140c41082122500f4001d424285804041d0410450107031704001006000801c14100510030008507245a16610402002a079507061814684510002c0c91a415a101306030010641c1d0340104142d506451980d510300400f8848012001011540250241d8165583e85000f0002c591003040451705841700a4002c81c0c14088a00e004281c08c3c41035015420441c030b4a4a02800c0c0d55440b800c90f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 223761007 1250 223759757 223759759
    0x6070806011d030c060f040e0105060a020c220204061d040e0607030b010c3305060102060c0a03090c06020c120604020604290a030504020109091e02030c1606020408010c050a0509 78
    0xd03080101c0100031078136014080718180d0380030402080107050139100c40020803e42e0300002050407640d9a920620a01740150110007015801178403098200381440b40c0622081e0b01401c0c20f001d451040129901d080b80d01641011000640c12600c01084c441010f08141d040c600998082110304410355103140c5030180549030000309629800d40c5603850384581801041c2d070790000c14400003000b00741d80340901ca4001038003e102c10003c0601c9510013002070300c55544100c0c03040e000303030085030b40d80401c2803200d07403001884405040d5104407880200700220812006005603070014560440898100704001c8030900b541881c95008104010041e100c01c2c040d50203c900c83ca407041841c942c5501030703120310790000300d01522440011503413550351036054104900440c001c2c0ca07210300c0c145e00c41080009503604480504502894501c1e1a41c500785207600443d884450308141c81d0400c003620f0102540d803c0400c3d4192440781d00480c050008040a108646072640e45d41005403070181103110142060003218001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 223762257 1250 223761007 223761047
    0x306221b1704031803150504120c0803041e05030711031207150c0212030408040302010815090403120b0a080c0415060801060e041806021207030e0312040c05210607080601 75
    0x14a101300041d150002c05198081d500d484110b040102d0074000b09002c460540e4405c081501d02d45243d4019248045400d4210700090314555071340c1c0340c8420150210268440f101019840070000c2001800a0700e07150744903041c50520103590508142c54210b4845000007000d004021700b41c002110681082845000a040480d080c03596240c1a400c200020b5000808071200004010410045000600c241e9200741c88203001501d03001d00003610404488403207a04260f107400410f0109000302241212850000004111079001401041d036440b1143d000e84030650003100e003000c1c2c9141034065510003684855030f52030301c1460700780001d1040c8418841d03103090042001e06da1585447c0d94000120140300220100c030511003610307148009600c080316080401008001141c40144a80184003944511000541c100503040303100c3d000701c41c400746c0221410140494000b9007601c82c15035510344100c984042c0e102006000308880c0c1044c03030040400081003034600800030700b0b030b03003240c9a810740d03c1c125007003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 223763507 1250 223762257 223762277
    0x30218090c0918070311040b0d0f060305010213091b080612010f021204110109080601061803140a1e2102031204080406090e010e06060306221b170403 66
    0x540c8106204403000b03550001c46a18200e0985449400c4003802090540d40c2088000480984141e49014a00407a040102d0410000348d1022503030b0403000b0003001e080790005d00c40d5603c1c2d0380c5c01d00f241d0244d40d500c100d01d5510720042201405600c1800d40000200e00800707900a40e4040090410b0b40c002d1109108004025980740010425070020007004030300344085507958481902c4030036000c41210210f603940541c00038171490b075208110311021600401c009045590900c20141c41400c80071188405605166038008040f0b105025800403441c0c000340074091002d65810000001d00c01c030412051030410104503840005c410700b844800003c0540722801844c1a121030480c110311646900041004014090106200c00c10004200700c0303c0b11f403901c5031415520021620041e01c02d100d220382c4150f1010010301c5904029005650080d4000c1a4903049070000e40000c044241210003c20300070741d101c1450750011070740310340c5040c0c1010b1424500b10a20240140001546004000801f00808256 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 223764757 1250 223763507 223763521
    0x11a1507050c222912070905060d02280503031206090c071407061821020105040e0f01092a031a10030e2b08040309030c090504110103021809 62
    0x115094201d060b480090010034011450307080d14401d140500000134140d10381c10040791814101c820080c00c1044041c0840500c0c10301d084c002480014003494114080142c010010395406403645046401102880e1340051030040341501c80d40d01c0d41109000b81d2040056281c015500c80c542d40d130203881212403050f9561129880d41103030290410041420b00c291803600c1050f0804240c100c00c0d2007032070b509c07074081040c81c201c048a0180a803103180203107541849400c58981d61500c84a8400c0c1c0103051003450207039a0002c030058a4000c851241c01c0b4841e01c001444118218011481d40103e003200615000d2484c1c1c2202c041d5400401c00c807020f06035140410007034146200c003000c0c60844000e010a103a0b011840000c0c003c0c00e03641129508078001ca80640a04c207031050030340c01e000c1514100d1461802d5200c40240d039000c5010380241c05100683d040080001c4052044102500641030085518142403800c0f030900300400c0c4100d814180180310000a582c85150040d46842c4111510740d12603c4240c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 223766007 1250 223764757 223764799
    0x507050403170c06060a271d070303021002130e04020a050405070e0a0909030203040e04080f07150b180a020f0c010906020705070b04030f06021b011a1507050c 70
    0x10780014003003000c0b81c072000c0c5508181c902610b044540a0241c85140d610801003208072100e47c007494840a00140c07020303401e041440021030f092520b030040007441c00c59181c004031041d90756040302d00762944034a90520800d80d0610414030754129040003542131041d560411100d11105004135440002c105000030155965a031683c8002d000c098020000c90410390304c01014160b80941c240e0040c0c802c10000075005440f0310585541c0c03038041c3d001d581002d0400b41c030700a540c20040d009440c881350030312070b80f01981c18613402003680c40e00c07541982c03101c0c0038007034075080a455003410281e00c01c000c13400c03503e240d401e800030702076030f008a41c000e0042c0e0700c030800f8885e8980f07400303a20001d103541c0d0311300f0041908200040e801408500d010f0400c40300e901e552100c282c0a184524040203000c03221020141c000900c41d6000b910210069100c0b00b2241262500100c2c00c54411080741a501c2c428410444c1d401c4c24180554090360a650184a15048294451a42d20380001800724051b100074034005580138501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 223767257 1250 223766007 223766009
    0x8150f01170126060108030904020a09080106080604150c0e06210f100e01150f14130608011e1e170d080a02030402010f2a0303151a070605070504 64
    0x214030740001c2940c407043e4160712600b0078000d45041c1811200252003a050016009040f120488011494a502902440f0280d007100d14502c00344200e1040201c1e0444081c007401c0b02400b07112000741207629080c203020101280030318945054920f0034802d8002c0507400600040802c50585e9090340e102040285061050b4240040ca910180200140300024404007070103806504d0030450a244a0340310445201c0c48042841008194440d201f0340021060184001c0403001e403150820728003494a00aa0101560003885103a8403540b401009006c51500103112501402c480307811481700222080c05d00078417840a02403400e17101c0c60305a002c2c089044209856002e000400d40e0502c8003800445a00c0d5200660400200403801000c002030003920503209903885180c05079100f440b5000d0780c48041d5250305a49039003c1c010480241e10071a0400e0041d03000c4001440390750000f9410284400300803031181e803230b000202384850350042c2400510b8100282c0d451140c01c0f40000407152111a819181d074803a07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 223768507 1250 223767257 223767287
    0x30e01050f1201030204060806090a062c0129030c0111101104080606030c010509040e120c031210030302031c060807030b0103021903020307091a2e08150f01 69
    0x115010100b442c00c414a048a100341c6045c030100351150403c0e9101da00c100c07003010f050391000c3d61200114450b500500c1d41e03071103489071003c1d58852850528507021300d01070b0303180c0050b0344410304c003820312010710f910040907200b241407940ca101c000c400284c0c03185c011845450402c40490300e0640a0241440042c1c15202038130402c0100d44031032070171840583c1043c481c061040c041c95001031105d04011501c5400080140d468501e009280000c110043c42000c114010600c03e2403241083d80c26907800400410400c1002107445400080034100c91981c000c00701c5842c9803080d001040040d40002c152041d000c003801c1c8030266181002d00c810010f0015030300504191199500c00410b001c10075103454140ca000365051002a0070582c03040c0c141e15010300c0300075019400f550b410841c2100550200c0c005d05503e104240200725800e0001c0d05911008180d080b00d248031859420415100484007915056141440c14217803911800303030041082d900ca8464040c03901c1c1e03282c00f442c0d0f83c480c0205410800c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 223769757 1250 223768507 223768537
    0x1807050d0b072007120809040f06080f07080316051906050f0105030313090c021014090606010f0e01080402130e06060114070c0504020d1116051b0d030e0105 69
    0x400c0c1c100204042415900c0c81c0c0840d50201c01003204120464001c2007060200d8010300c45603141280c24600c1845080098410b45000e200e1054140c0d41c1d40a900c1400b0060740b800714103e42041801750501817645001410b540c40740b0010001c2040200030b07103820411340641c0001c00030700c50070007604180300003031f0107411440300c078036036a04104840d1300050184549007404009683ca640c107144d031f01e2280c88101068205450300403c60500b06412120f100c640c50b2054406104408454205072591811094840b1000000b00403940f0400c2041690100003440d01080c522890000070300b80c0c00d88851520f040080d800300180030b645400c1c280b80d159803c000d108100081c40d1164403602c9110a46403280001c0b0a80c00c03022120580c0b4083d60745454001140c1240d00e460042000001c1d803281201c0c503040f0761a00c2c001d50380d01c0e544e100a45000141c08060314007a0f809440c0c807030706020104140f004590078400b1054402c3c0c071050707a0101916030504201086042410060f0362170702510068182d201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 223771007 1250 223769757 223769779
    0xd0206030405061006030c0e0904170a020f06070f09141f050901030e06060a0905090f070303110c04180212010b131e0207030f050f0909130b0a050c03180705 69
    0x4200024100e204444c0300d2084481107459140c04c4055443c2c8000300400a0710440300c40c241032405441b42d9402a100b945038001d4504000700381902c1c0d40000c0070240140e002040d240b14000010f000071030703120440c2c2c40c08540d0940000d130041c1c00000c2074064170760a10104c464503412074803045546c10300340d40d660100448804013000024410742c08026090b00084c01c1c9104480c1a00b0001442c50042c00d004080d07226060518514a0046c00b0050001c0c40320300c240140340c0300c48441030180c44095070084c2c4c2c4440041746042c285d01d242000a40009008900c0d100c07e1103072840240c4000c4441c194105c41d505000740c0030091f6140902801c810150348010301c040d601c88079100c540d21400c0b440032400f07910411101c48074071000480c00703560301c0540410038641d80c00365440d109400403c05c09074442d50b10b9003000760000100c5e102e40700c22210100400d140b02418024080200c2d07c80350701c0784c02010180040d107045041080b440c0006080c03a100d6000d10101c2e040742c03803001e003c49005480c000d4032000c068 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 223772257 1250 223771007 223771013
    0x1003031b150504060b311b090807061d0607082b0b010201090c1707030807230123070504030602070b011d041101080a0219030504061d0601050405060d02060304 70
    0x2418290703001c607580f0b881c1800c1c9415600300b400c10921400304400441c2100f0110000c092400e500d17641b440111555201404002c81c850300351a07610001c2a40c1d6080c1c01942842c800d43d10741412038101c0018440744001400410700c00b1000c0a402c00c40036a28552900554a4280518010000782c14a0b240130085600302c80060200010032050100d0414004c0514032030041e0b080715040e020241260465007402d001206c6031544000315280c0035130441d58025502d0320f07098001c0e0040c100840c0c84040c1c6021824a5158080035120b107411550300030410036000002180e8070302601c68210310f40105440002d846507008600380c6000f181c01080075550790605181c0320b45280b009020300d00600c0404411a0543e031003083c4d400d4030465008043c4031864090b0801502c10800090000010a07020095002008691460701c0088952a1030124150809140190036503a11054441f143c5001c0f10f01e4040948001400b141142c84c15280040c2c19210040460232400c030130b030400394110b10000705000c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 223773507 1250 223772257 223772261
    0x6090c0c0303050714030f060d050f0a060606110616020705030a1a07030203010b0301061103131403060f0c09060c0a020d1a0a110702010807230a0311031003031b15 72
    0xa024402d039001c211507a6403502c207a40660784036600d0014020203000240c6158604140035420140040041c50300b480300d5558149030004401c0342c1140c9801c0395400c10100880c500a17140a0060317400c150520740340e070700c80c81603071804010400803285070301801c028801c80c004c0c01a10080d080140c00c1e585007200e5030030801040520604101c41d014004000180f03000e10a2082d07d041e20422200305240d646810b81c102c490b00a0b95100d105940004c1110302e00b0199100b00b1031000b80f00b0f072607012100300c010307501701410f01e00020b00300174403464184100a01121001c081743c03107004041b24516281d40c551100d05140540051009402800c1d003c1341101340102d01000e2044000109524080c07139550204110548812860b442d1595401348a2000151301800041e6030102451800041440c01d0024844207a4081006040d140f2070000307540c10410361500840c1800034204109034918100f55100c8001e1089501c4041e08000c50f1004505104580c6c4110314001a0480401d45840010101c0040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 223774757 1250 223773507 223773527
    0x604200d14061512070203040e041101030c14370203190203071104050601050d0c0504080c0402030f220501060b04091d0a0222020408011409060c0301031506090c 71
    0x14203405003800104a480c00c094000f0ba005080d0540b80e052180c0810741100c2082d02030902c605600052101041000c1c20502852140703008240d01902c215507040058200c0b8556444030b0200014000101500f003142c03401c407030543c007140c140c2e040855000c8903040b6007564200301490743d5061901a10321303441d0380000a03003003001c040d200c5c41d0a80840c0c801d00380d9580c403c04100402c129503034209007443e8500313980309035800700c0e0604003a440c00982c10406012140c7c40c04000005c24008901801050b00c00c101e04114148252170443c40c50030145181d400a1b100109241c600401c000d40303c4660940703001000d003a0036480002806070907144c0348110400e4200d8000e003403d071481c24803030280382002c0508014000301080702900f015901a001c2c06512940601c0c1c5604078205030a06017241c2505100610051003a20700008046d0241500300c20826400340408505911141c148002240018216411a0703070103241c0f444c0800701644044042c0000340d2014121a01e07201ca02848240c000401c51 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 223776007 1250 223774757 223774781
    0xf01030b07020d0807030b010c0213060303180b04030807171219020304111011070f140301020304080d020705011506080708010b0c07140409080f0408070e0c030604200d 74
    0x40d4007552681d00803681d840c0c0d0080c03440300040040e03000c28841d0340254490201034a040c540702d40030005503000302d0510f0300400c41c080441566450204241640142c105420b04c2c104150481014680148041789000f82d001c060b100ea100089d42108000f04140e0000403061051801900e40600103207011610004071450441c41c1414140803449289520840b4850f642c415148000e17000070809101048802c555900b0500c60038400e540340d05030003003201700c004060300c01032030500034200303400300b00a010007000c214003d84c0107006110000f907003001556043e080040c0010384504c3c441c140107024010401d40a42e141e1014000420069407181c0b00740d120301000c2d180c81181d645c1c5c50454400f94412034100d0f400c0340c0c001e4201800710714010b040130701c102100280302007002007641d240d481e0b090344221410f03401d048002604005400c01805000001c244070751020b00070f031411143e00e0500d807200070400343c031030366403080176a848058071008840980c0b5011036054940c1d100d50030a000608280802d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 223777257 1250 223776007 223776023
    0xf020409180303051b0307031806050c0a0e0f011704171201060e0d02090106050c0a0605070e100306180e0a0f200306190203180316111e0609010212030f0103 69
    0x40d02588444041800903001c01c01440c0c030f15921f1101c2100100720304010100c040a600130320b180865007500810b40900200126140d40e4502e1000250125444034100345c000d02c81e02040c20361681c1c10500034908051301201501056546180c165001c0c074401d40c2010500d003010400d00d102c1960760200d141038902680b50012011900010456031103004031009510800540050103824454005032038007101c1e4408488020340705503152070560344115450701c002641013410f040700f444d100704550142121030030100945420419403000c0c0d000303580c910f02001a1150400300c0d070020f0030040101c001d600001042d40c060b0041c688044103c1485619080e6503050f58103040704e40c60042034643c0201d004030480210ba403c0d03800080003940000b4510a1010015130000604103c180014440d02e81c1d00100381c034482802c1d141c106a07c10b644000319008440960030703c00032500d4190480c00f4803030202c60b00341d1281341e4540100d190540395007111080c01004414400c0050896000d0383c103880c8100d41c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 223778507 1250 223777257 223777261
    0x308060a0504182006070501140f010303090605070305090301020703080708010b0c070e070e030a0b1e0702061306060909030903120201020307140d1401080a0b0106020318040f02040918030305 84
    0x20001a180304583d4072050400071100c803800114a06041c0421088803039410314800c0003100020800e40041e4010740f6a079440c0c512210810b0035101219a1003089032030402810350654034001e04000769401900c05105000030001c09050250040e00c8000d80020025543c50095180c001e00041c8203031412000718000ca030012030403451000c142c450044441c4000d001c042c0c0740440c4e03e02c213584054a641c042c00006d04841e02c594030709000845405010b04242003260034070034524407140c15214102020010380d041405041640420392540003091141e80c15a44036580c10850028025a400009000d240c00d0141c0105a08144680212400760382d0180b140298ac0c0003e900b41e100880b040c0000818402c601764030b100081020300303038042407560001005480d0706034003503526070308ac1c203e0a0f0542c40041104104030707103c6c92490140503148041e504246100460900d06004840c2c032900c640c1c1c03111240b4040181c550b041c0c40c0140b030812424441c1c610910409800c081c40c41200303070300007810500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 223779757 1250 223778507 223778509
    0x151f0609150804111008041106031303080702120a030b010216030201050406120204030f060f05101a1b0105010b1c060b03130f0f0305090325060e0d0f0308060a05 71
    0xa01082100c8008900d070503800e594040032200744000400c2260b03982c081010118683d1200f2168005421580c0c4420a150400d03091821510045102552090381d0410800640b1010100700b0503e281e1325003400b0015859025007070382440141003a5240e42c1d50045001c98401303a250700848505802078081e600ca0342d059003009481e009540c00040d020400130042040994407c3c044130300031803038000005080a880340d840207501c1180c1102615010740700c10b1585e11400ca50b204a0f43c00c080d11002904043c2d01e0003090590b00c0030089108403408001041c0c542d14072040c036100090746449280208035941e11011003140ca83c000161080f5001d1505440040b4000c1c5442001c041c0e4011316002410b541c1c0314008a041400c40c84001c445c04000902c0c9000041c03404596216110710030b80b02d040c0c40d28001030900d80f9008201103515000d00044080e4440c0c2c0341c0ea18000819110b042c5070a43c001741c0a2400701d00e521604084c0100b50380f050080344420300d0b5004506500542040303030340500d01d07542c6034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 223781007 1250 223779757 223779767
    0x504030206100504021e090105040e0c1c0e0c1903061d15090a0609020607050d0c020f01020a02131802030d02031305010509180907050604120c060212120702151f06 72
    0x400581008030310801d1b102c102c0c07481ca40c00b4041c08841450001d00c0c282c2c803000e0f0584520b9060314001d400520100e100007915070113500400900403071500070804500d0748094107944582c40e003405030041c1c91040a002c0604002c550500c060360b0810002d2000104411110364811600100300d01c59002c0c090040f4440216401901d002d103003014000c01d490030343c81d10703080001c02e20500201c1e4014810000394001960900caa402a1501e585424680e4415401802500307030f1340e088040e0440d04240c00700b4006a842c41e004800210415500082c206008031040c03810440300600a5854801e40318041e4929600100a001d940800702c081c9410959031303030055500703001d1995466400891846400800c407103164031a0303401480c41c01261550f982e00d0000c40c5407a4440d81100d02040b408078018800e0000c001100b1001344071510060a0405107140d4281c42d42c0525607810110300170030804171300c40c40c6c800c110074031254207982e007401440e00b0007840d03201c10110080c0c4085400001c41c03030b0002c0c09a0140c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 223782257 1250 223781007 223781017
    0x509090106231f0c0201120e030a11070b0f030a0b0d080406030222060512130201091809020301020a030209030f06060307090b040e301c091401050403020610050402 72
    0x1844002e005080c1a9070280d1214090a030705420858880068082041c08980110101d0098403402007540003400014052294941c0a1901da4180006c10600003000012138014081c40c0c90030452401241c5100ea0404500780d01450241d0804203a078252121030b9070040d40100d020080800009141a080c4250b804140001a0681d4001e0100b0080540250010b085070000e80404415101c90342d1104c8004070400c1e0031020003d02e0220300d90000ca142070064903008540c000340c181b4030501c00d50001f0140e040901800524613801c0c2078841d45101140c100c13100b6240e009000b903483e403121460080c025048009200d00c0381c0302c0c451020700454808210240150800340250032080e0400c10060068032a80346027980180c0d540110086105e4140300351003464580a040903505c40459940b1184a01d1228880c01a400100188055502c4050207664001c030122008906100c1c1e07030030203101140a2451510b9a5420002040101907000c0748461184403206030040180d600e44050008a02072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 223783507 1250 223782257 223782269
    0x607030918090c06050f070204050708070314161103040f060c0c05010f020a111203030c1b120423040f050402031903020601051504120506010e070512040209041e0c0509090106 77
    0xf04205001c210f124200a0a5942000b0041450441c243d03002c00c0484400321650400564107009002d1800d905001e0804003003800001e400b024248003548085243e1101c50003801d0058a4042000c1c2c050705100759001050380741d100d0b00d821a03641c64054807000151204440c405d40b000c001295941c010b07090100461101e900900441c900c5a803000700c41391106050a61101c0000e85217520340e181040154859407051668544038408942c0710308260750890301c1845107070003290709005075817220800d50701185c5110105000300f0a21417000c0c076142443e42e4015030060301f081c0c001c90035444950441c6000300c1c400e5040320803140d08041d1038140c01035000d60080040c3c100c0e0380104241e20740552003aa07001d8200420910f09070381c40d4204841000c0f81c4108403515002000100928030400006039404400c5040c4580f602904248840c00c54030001d1000f4410200d00c40800e051000c004044580c001405c0a54000007009041146c1803e80e148910380c4181c00c030030001180c9400c18040c000844003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 223784757 1250 223783507 223783523
    0x9060203090909100c1709010e2a0901030f020f0603010f170f1c0215010b070b0a060308180307050a0302060307121506030606020d030e1905030702060703091809 71
    0x8450740c10040c1c610b01c0500310071150b00c286040708640c00d41c036200d030702d0040321702c2e899550105503a0f00c04402200002010003000f0307490500e0309482d050380802d142404d0351044405007401194107170203400d0800c22000c01500310074818008410032001440c00c01d80300d80200c452107200d4a1380d404100642c0703c24094250085040075040007070099041c07824900095044c281c40841c02110710181c5469440070303440300c174042e848034000e00e060f40500c19514040d4502081410941c186807035080c0768401c48030014045492040040c003c00021b5100748044c50340065066501d003a00100641200d6401d021030703101e4041c84500240c0c5146c60103a80e421668081c0115042da82c5000007610540c001c40180700909869032071207000d01144200305400345ca6607840016950b824894002e10b010109210072041c18584102141040c00001c4c0b003000701e0b07608035684110b980c15850124118068558002d4204a02040c1301042641121451003510011080c0c0b98005490680300d00c1541e050f0103010382149 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 223786007 1250 223784757 223784767
    0x50114041b0f09092918011a061b070807260a02010305040f140303101d010302040b0a0b03010b0405090705040f050d141507030b03160b030403170114030c0109060203 73
    0x4083d030013852006004240074210700c24060804072141654401910b100010402040819001204005030b010081d0340200480f100f102d03003200f0203001007034585124420209142e4a020310407118060b40051100c1034030800d0307a81d00c5041d95584403c5c0200100c5010b452a52140401d04030080060350f84c6500c01800c001800c4d4006500030000908152801a500465a00415038000e03060301040010401165640350200c00c2c09450380660b044114a00c981c2544002d01034401e0351524154ae404450000b000303500540022807001440d40308100320540400002040031a00340a00100c402c152003079426552824011680f5204a024059010320060410301083c01d10401a4160078400c50740c482d480d40004002502e00050301885d09440790903c0104aa1954140610000d1000603001040c200e80800d00f41900d80c1050f00070490012404000201850b11499211b0811004c8203551103039942c49003901402ea01c2d00c041558000d01c10740040c0c1c04907500c00c5032140200c9490354055401c0c0b07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 223787257 1250 223786007 223786019
    0xf03110d17011a040b03010f15050a081b0409090c090b0f03070311030c120102031005060418020309010213060c17070b130f150b09010902030103170313050114041b0f 73
    0x4010403550f40310700440900c008a101884d101c000c6000e40302d90000c25100d1403400c2051002c08090418917803c2040910040c0001e0380c0100c00d80340c01c28080d15003c922002c09690b05003c5024039842080b14905100034002403180e803002c2c010544040342c1c010300018100500707014001408501007034160340082400c101050903440e44407101c7d01c0007010354410812080010354080741e5030f183c5907000c5e54000284041201c2c01556a4001c6c6002ea42e4142000e151100d6401c21881400039401000e4000002030724200c0207604485682604081c1e2118450300c0f108001d02003481e0100032192034580745103500907031880c0c40950308441d60250110310141c0c0ea815000020204411045400142da1105200016460a4140403105100c80002841070201042144c0001d060780f045c001280704000510100f6140964100301d0881404415540c0d01c0f459481058070f81005400350195180000c041c030042403801045016038000e288880c8011203920b090ba01190185c854090504080d000070012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 223788507 1250 223787257 223787279
    0x807080a020907030e0303010e07030c030507020706030207050a02270114030c0d080705070801050601030614060703030222060906030506010203190f0201020c160510020a0f02011206030f03110d1701 87
    0x20003c01c038503000c0745120340102c8817803941d0420f8200304140d540c010100318220f54180300c0d10503d1541441d061255040030746011351036084901881c0d0805d17400041c0007092000402c1042a00e940c00347c040d410450862040d004840036030241155911004c4d8000100324241040155540d00700401506140c20040e00b040511000c4079011500140184802004a00244110002000d4020000c6160314100000604883e1580c008614482d02e0003510911603e4640980704180c0c1d044c00c006a441e5007861044410100011703089284c5441004003050955000b0b0b184400c0700d403251010310030ac0e101c0030f0041ea00c0b40500f0446c0e41200748010f12040781d280c45184096801c07031041c00014a010141c1c11018103184a0b00f18011044520030020495070a11041c1e0041e0002d40d032001d070480c10029507400a0b03420402e06c02074108018104440c1c01203c055001c0c80040d41d105194100100c0a071401521031148481034112601480140c50780c040d001d02c0c1502c6510880ea003ca00d180e070b003000c0d4010b42c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 223789757 1250 223788507 223788511
    0x4030516030e0d030822150213030c0303050702040c03060b09151c09020f0a0b0f030402010201020d0504051b0a05060d0207140a03050309101107021c0512070c0807080a0209 76
    0x401c00440103007520b010340b42c0081ca050641d02a0b5a002c0e200c5ca040c141d18040e01d80054136420401d443c008400c808107000803d50401c1d40a40301c0007682d6100d940441c060000c0c040e42010740150b003102c6d000000c06070451700401e46103200b59002e100131040404142c003222024410039013102c10030400c800c135030f1030103440c842c0883d00b41005035424450b02e00010100d040b50f082071050116611080b860940c54100302c2c402200c0f900700d90842c9414240883c609440c01803001d10300030544c0c044041303021a8001e4050311240d0a0980703042160340b80c94100389070b84a4400d038565a07107034130342003006d4010f040c0100d46038285c034400340c1080d00d07095100000b44002e50001c02c0544011a03e41c01805a00f082030141c03034403050103a0344040d03c078282040d059042418190310700080a15200b42000704488003c141c6102c0350301203c091610050002803002050146107009000d401510701034100107400f10040c1c14218050518851020b03180d401c4d9a50324240c80c0100c84171035001038500d0006242c143d407180d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 223791007 1250 223789757 223789763
    0x312030b0414010906170d0912030207150305010504050a091101051c020a051c15140103022101090c23030c0d020706020307110a1203020f13090b03011404030516 71
    0x48076010b1034402c8922040a07007080c0d2903191070390b504000035000d0040050300c0940c120041d00c00d20521040c023424101851050741500f0413580051340905009000940040000701c4400115101e904401001090240a614421894800070518201c0d03580b09800b920340d80102c40f0580f0255000064a003904089849e40c80010142c10f1060201c2c00c03030011b800400905d407a00d0745ca07141c010030f1251203141d2004180716050318081c80000300e500e603000720308110395180c4401c400e0b03240c001d40120003074030030340c5490b0640c108400748001c040d10f5105c400f18125032000f01c04000124803c441120303d05038007900c4802e2040304031000161000c401d0011900680c000f100a8601b400c168090b1060780c01800e415103006901004000480b40c20110200c4155403101c09444c40e207407142c0d614400c0541d60500001095404907000090780c80b14400c8603014482c071100c81c103d13a981c4203207440240c280481c11502079424241c08640c0403c03042c1069000fa40d244e12100e0038450400d0840d032030811144c0041d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 223792257 1250 223791007 223791011
    0x8070807080f1506040902191706060d0e011a0f04091104050c1908040c090e1e0f0f07030210051603030e0709020417010c021b0f0f03030a02070609050102070312030b04 74
    0x45060307a5100001170008155141c005601c2d01405503900345612400410041070120055040084030b600e0542280c1c0b21404881403615440c005401c1c00051041401e0410150720705004284150580c4107500c200c030758115805c1c88541c0f0038100344015580352090007000c0c0503640056400c240b905070001c0340c0c0400303001d0506040100e69200d441c521980c40440001180c910030610041c000c0c1321010002170020b505040c094031180b60451030fa1190400310152141c980ba1340001d0480d0b00900030450110710301c100700d544a40d61210010745800c6607201c12407080a50041c14490217000d00240c4090050b962010420b51442c2c0d1010f030b003d492901d01034010350007004000308a92041e480034102609400a011048a80c010b8590b800c54900c2c081c0c40c025903000150383e140040c03156800c440c65200030b640d00183c2140100c0070503050703403904488951502000c900c00408990000c1d9540442c0c030a640da80079005c2c0ea482c016038641000d03001c06028006600b11008416000e41c00100c4004809040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 223793507 1250 223792257 223792291
    0x30a09050418022e020307030905041a040e0d020105060d0b220b010e04060e070f0b0d0612030804020a14010f0c15060906050a050a0b031302060c0a06020a08070807080f 74
    0x2d141c807244000c4154401c0303084240d5402814070f0304d0800c08024140c00258907000441e10701500d40c504a114451060f80c40d9050341e407201d410001055580c120150060107040450008903440790301d9103002800643c600400101c50303180c079030f07140d4140940014100b440b54407401c51100c059580c5400100b80d980d0030300300b5613000502400340c960003850012502010b5041c54944002070f0344a0154038590790f030040c0fa05000410010b1008411520300b84200380d03451201210382005003900390b0080880c0052515000c09140d005800188105c0c42151341c00b242c2500c41c4411414103002c1c030142400100c1c10500020254092000b114034180142c4921594030009c4092005481950700144451903d81340100501c2c2098200c1e100580800c4494000e41030030240c490305540001048111440300359400c0d01c041d52560000c580c5420021030680700c1e0044142804c00203540042c1d061000121348030005030400d80f040c0c0d080d41c0112100d680d05082c9071105407001402540160021404001c0303000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 223794757 1250 223793507 223793509
    0x140d05030706050f1f051c080f07020f0a1a030c091e0307090c080a0906020c06070305011e081905160602010e07050901050307180f060e09010e030a0905041802 70
    0x10192070a80e110760408079103441c00e0305a5145441018150403442141c2c000c03040401910061a0015206c090b107c3c0c0001001ca40c141c140c024041c1c2c0e078060312080d40003030300e040000d2054004140a6000b80e4540081c0c06501041c4032070a040d40c45601210300307110a844042218074001990405260140d00703040422400000c1c21000041c500428801512104042103003400d1207070f44000d104800e410002142c044c0009440c880c40200020700c240d60ba010854200100d03a810f0710342d040f02d04000c4400c0c0c2c0c50700f0000503008010038014044100b6500640c03902c0c880010851030300b034032000e00152401c0d01d00c4440c1c407402c0000601c0d0403941806902694001411003046c07040047c1081d60002c01c180c029210480d0a10f40c040c1c010034018522900140581e0300d00107401412031f80b00f690b01c120305d43d12001c0100010075040c484404030a050050010b0004a98002507015022120003006600c3c01020f6040d41c9103d21450400440c2001c03204000341c3c0b400d030703000d060192101c5604104504880d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 223796007 1250 223794757 223794763
    0xf0f031b010e13050601030c0306120f0606150203030711120f030406090b0a23100b0a09050d030e030f1b040207020f04090c030b0c04030302030304120203130b03072601140d05 77
    0x1803584100c59a6101004071640c2e00d805901c0046045027810030284d0f00740340340301040b0854010b01a054103c49103180c0308204c0d45a20440c01045100700000d4411a00d600017906d0707a2041e07801400144403008003d0203200007040d0000c0c44e00121001c1d5141504403208409546c10041c4213a505560384d000300300c081988140200e01c01c03041c6ca0030004404010b500c00e07041d081121403426840b0194181040801c0d41e1410104042c0e07000b02510b1a141c040344281150307034500f280c000c0c6403c8020003c13407408160300003c220032061303811020384123510a00300c801c40c0e0300e101c907180c3d14445501130102e65186080c40d81c010250540003601051001161038042002c1d02e40c2903004446540020784100103002e4000c469540105122000c0c0e0725062850714000e60703900010300003500480071074030602d406074003c200319600f2540700c415982c1001c4d510701c61206580c00840e56140030072541c800381510303280c0c480484068021031700003600c5242d0a22906041c60741d5205c1c10503810420007000303030700461010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 223797257 1250 223796007 223796029
    0x7020a02090c041a070b01060806060c0f0a03030501090216080c0a020a0b030f070906020604060b040615030903020c1005040312140705010614010806030c0d0c1802090f0f031b010e 79
    0xd090420f5541d40b814600500444a4101c150184030084c01032800040c0d05040d40385c1190fa5501e1318042d56211a400030f1042d00c54400c02d01c80381d100d4500300088241c00032030410b480d94081e0b1401c100b540e1360b0f10b40d628164031514480704500c0c07048419041c00280410064803940c00501c04460b550300c0d01d5404900400503d40250300c00c80000320070032940d03a94440300580d10480034a00300f1240b13490568080d580d0a409000240756030744480c17108009866560118006000202c00c1003a107a02d0b20401400500c0310940a40043c000c05840c214542003a01645021220356507a032071510f465a1207030071b003080205410b0820440b05000641d041506000a84140c6000f0000050b86a1909503c503d000700d20001c1c80d810300c0400020840680e50200702103442c42019035100c1c03494034061800180d14410340c3c11000e4411903100c1209010011540a00903a49040d40e00a03011190312041102c4600309000d80c2e54541e00c4011143c900b64040c5081c1a036003c81070410701401890390000030005029 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 223798507 1250 223797257 223797271
    0x60d0501020c070b0c07060306030c12020d081809010609050a03060e100504140105100e040f1106220509160f0311040303050703020c01140921060a05060907050310060807020a0209 79
    0x4c042080340f15401d041c0000801030541d81000c000c0e9601d0f680d2150400c454030f2151007484a8074480384019911824a81e986595001445648e210383c002400e075111603003a02124004c0c0c1c4c070480042420b038068400803040d140010940c0e00942d103941c1d00e110140c035002030744e203c1e02d000b09100c424002c6114082c0500451282c3d80d1a04401c198022880c00c444004014500d800360403901017004410301001c132074009070400b120018031205424488280e1080040182d00000c00242001801c542c100d06600c15104040d00300c3e10041d604c604105401805840c0480a500c00194a00c00c05010354024200d40f9014180841d081d0341e100400c190030f4205074801c0c4e0100c1d800103a50020513605008034180d4203000d09026103604d5540c484c09015015076002c4600852034080300d003110002c2c51000481000350401140c003039291850499000e8031040d030755127004804c214041400180940c2c00d69104101035548403100614145040300c4008010300250b056014600110700940c98882c3c0b4139200d4a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 223799757 1250 223798507 223798529
    0x9050307061a090c03100315020c0a23060912030601090f06021b010f020703110a030b0a06080c01020303091c1407030207150e03100f0b030a26090108060d0501020c07 73
    0x5024450f4442c0020008140350204004210007040166001e0090f00c5d0403428010041034024031500c02440769116409251040846c0e0408103d52101ca1880220301c0c529609921f050400b503442d52001c06480c11310303080d00b0605d0710341d41249a4001540e4410014980000302d99a1a841c0701440302980e0006401608164403446090380d60442d4410041070070301c0c2046000d07407200e000a454401d1404002d0044889984050050341c486540c8005075410411560303182c03c041844030018089441000130034003512180341400d60000c0141c03880342148102900004044444000004602082850a01284007030100e003900703061001d030003900e02c203800802039107040224940c490925130312000100130912001151903100440c100925409881d804a004045640010060200382c441c1603014440c81b010340c401c2c07003050b210301c4003149040c0f00d041e10b1400d08000c4100c02c074030982d100d0320302081c00302020544506081000140300741c0a03000040c1050680d5059508142040d0301c091501c01e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 223801007 1250 223799757 223799801
    0x8041203030507090e06130906200405090108060f190216030201020901020105180d030506030f010e10050f01052b14070f0801061d09030409050f0414120d0905030706 73
    0x1540003130540740030b4600540050354a10700b4034001440d5011814000c81e01607140d0401c0801c02c00b440c1c10031201c15004210b8500004451050800d05170400c1c8680c51149003c0e1000040403000400c100703001c1c46441d00d030401207544000b4100003040c1400b182001d03403907081180e84c40c045007400e0200c501a00c02d90002d07989141d0303800020709496010b010541122008502c0c448202000107024840188a080100c2c980d40d901c40003d0038000609036483c455401c0600381c0c4182000032400c0000107214000c10000c50715070a200b140749007000d0140580044407800856600e014850072803206a01824500c202480d03c0c1d503480c0d0a00702d41e0842c40740203601c0000f092003441c444560050141805030020000799203426024015101301d40312032101078500c230300841c14003801402150050140501c1c00d201e41d04012140d540c542908580c203076900300d04410b0f07098500e400410402096003a0840c11400c0612001c95803005003958041100c2505c010000f103000582c1500966107000f020040043c004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 223802257 1250 223801007 223801021
    0xd0602090f0f091603140109090c06030c0207030f051009060c020c120703170f0a02070e0603030a08041b080a050604050d0f14090a0b0324101b080412030305 69
    0x8602001c103000e00c00c2c4400c02d400b03031003a1030307800d4815800310842c02c5540590310000c40c00c0d401002c030002c811450748610000440c100115800c5240418800c106100c4456956082101119407204103280140c01c9400c1c00c02c08117101c00b489100050048042d00d542e8010100d541c41203030b01e610000c84e115600e0760826024036405114090000d2130079078110540b80031101005454007030a0000170204107285401d00d83d60284801501c00c440b000c3d500380799848004400196460a2030b203d44403101c0c880d640094100d04000c416121403810503200c42c070183c0c545540301d403210700001c21441c0d03180780404000154113001300440c0c0446c90245010300000e040c83d003440c600340380034845410184442c111070f4121096002c1d02040000e000b00050300c0e140c142080014000907800d5000d114180030202c20f119842801c60020050814070320000c158000c044d00c00d10551034051a2f400d4045503910004241c0a0100300001b42450321610704589066140c2d0550841705040403002e60000b503440c0c007080b4071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 223803507 1250 223802257 223802269
    0x310090c020f06090d0c02091008061003170c031206030309101707140a0f1b060e0d08010b0405040207060609021c061a0f1605060114090f012108090d060209 69
    0x2041c21342002c2c0100c6500402d01420014510070000d005200c8030000500b0104410113100140c010700040d243c00e030812016806d0754000900054600116014000c804842030900b2241c940000c80c2c040c1d070600c110f050300c9905000c00101445d8140c001009040f0080e0b40d0b8161104030750301141c4526500850300c40c41d034419080300503d02d1042c0100498501107040c444419900840080d01c0c1c80744d042c0003010821900081001c005070100c01150300703403508000f0280c0000c1e0a81881c84200c03205111a1a1b08403181d0000780705000c00200d0030030040c80203080035001030404901483c00400c0c11aa2441114126409986068541c4034039180700b5044a0881c0a0100102020382c21720034101d4036625140c1e603a204802045080c0c107400140241846022144548242d80110039190b1540c0d40b0041450f0020148543d81d1145065400140350390f4402c01000c1d05948200c600d4040c00c2c1c51400f8400703804116141e080d1174100041c000350000d5984c091030340310480e2082c4070142c1c03116050014492 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 223804757 1250 223803507 223803511
    0x36030510060521010b0402030c090306240103090305161101080901090b010b07031b0b090c1903021009150504150206091005190509060402030601080f03040b0310090c020f06 76
    0x11401c0c01c024042150341c1e29203010020700d01c1d00c01d03100f15030a0a0496007600503c010f8041c1c0d03420034004800c01500031000c01c00307004005410303801e4034199900c1b030083c0d0080b1f02008158424850620060b941e07594806d80c00650014400d0038400c1c41c1242e9400740e4984841c44c2c210454880803d0441020203580c8620801c0e003041c0080300034055003000da03482e251901014000c0808881e00445c3c1c031824035104180b800e01ca2140304441286031241800d054180320000ca84140c01c900c98040119164140002d121400286600c1c8070307000a81580d003000000961901c0b000701308081c180001ca003400c000c844500040da481d488481c1d84d180760105880c0e003880200d9110707080d900140108584404041507281c0c107807000d81c1d400202a91006243c45c803000c00031440502043c40d040800c50f40e000000398080c00344d4021001c81d0030304da9030307841d80703a43ea01c403035440300c241c0c5030003d0001700813000c08000910307000b09010205c1a98285c07964858801ca82c5820b158000507071040002500300b51050003615 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 223806007 1250 223804757 223804783
    0x1b0501090611030d1806021309240306091703130b010e04030e01120e0d020303041709030a030302070201030b0d1b15050f0d02040f0e180a0b0601360305 67
    0x40e4560000b2010700f500d034007404182401c000e03120211640407060700054a507010358040030854076101d40a90f900b80340c8030140030b00c0ca01c2d1490304260f50507101e007404010200d003502806134030030642103a50318009401d03420402c8401031040ca4030038401c001c02e10061841084240007020032203800341405001c0b07040c10b034080b03120401c00b80b05100201c0c3e4414a410280c04c420300301168094842945080240816210f001590060307204e065591a4080b000318000c90046241c1c0040d0303400c158102504d4401c85495a0f0b0541c131504040b00041d01036009008001d0050400040045110b0041041c00d0b081100841d40150300c0001ca003131401c2c207410803402070034102200d03080804003108050020701c98004040c10141001c04c94490051282c0c0413a40580f91180f44d10a0b0203039500e403414145002521000d05002000b58107940c0e400f800110840d140c2d8100304082c007582c803401c005580fa001240450303100c0c50000c50300d0341504c07400006210341c281c1d11030f0342281c4110310f507040103030808484014007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 223807257 1250 223806007 223806017
    0x604080d1b020a0302040c0c050709240509040f060e0303010605030a0f05060f0d0c09020a090501120209010f0c06090b18011d0304030210180807180209131104031b05010906 76
    0x58405a2140f508620030b80e641a0380009007582c80480c1038580c44c0c1501c40007080c52007000000b1440503908d400405d41d41410304900c400140300b03020300b4100f2029038082e05401c458000e0010b00424110115003c4d45030040a00186140181c10640c0c01c40e44260086004120000f06000c081611b91246143c03004000b0401c0205081c0700d00003483c03560010742c400f841085035540d04420b00510800210040c2801d8a0455603601d60b8000500350740c5040c8166404554154100c0711110458022142d04c6401655202ca0440c4180403d9541560080e01512066039800c040707800a01d495820034040d81802c1c00c20f28a81c1652002d076400e6400d504104c0c403103941b140348220b0083ca0008141c8060320382c1101c00c24403002c0501c500700c42c01094048001c0300e00440000006602e000032510b03005640e030071900511080a040d0288084c2d01c204026140c124007030180340c65400e52070b5445001c5244540f09010f141c559252101c202d40c10b032143c91003468103c1482704200d0703903030050b00110080021f4140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 223808507 1250 223807257 223807307
    0x3090507030204050a0b030a0f03090602030309070b071e06050604050603160506032d0405101437020c0d08041208070915020105040605100f1e050604080d 68
    0x466486403003611000b80551380364404588828240e0300554040900a0201c540100290908040a000d020000d5021a900d030b0000f28001f480442207030710621800004002c040e24114252145900c900b4040c1e821610200c0c1005000d121030980c0c400c214003403940800c050800100300802c5a401500c050300c2540b000d540086000c4507030070b0359801c50340300b16515601ca9481040750786405051200b50b0405180b002140d0a5910201800c1e03401180a94111016195814616411a9041c4005650a0701800b0000320011440005a209686041a015000129004a1546101041e0100e01600e40108140303e80c84000c101901c00c10409141140660829854084d146600400c3c1c0b0301c1042885000624058041e0315024014800800700008081e4020700c0207000b0803050324100c805500380000300b201010703400c038450159000141e06a09151900080410100d00c1c01c2101d40c00c0145a28005026600d04010b400144008009400e07017080a00000300300202828072002c090b011055 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 223809757 1250 223808507 223808513
    0xb030c0a06020d050f04080303010602061e04331a0418020a05061e0f0715060303052710020a030f020102160206030604241412060c0f04030f1b060309 66
    0x1985805460550034135541c0d0f807509110031409442290080d84282c40000000100985d0025226101780c3c4201e10807040094414580e55007401c0c2550098620028070110304c4210240f0721b10b000300f0040c3c80d143c0b04540b1501401f0401601c00210150b44000305000502000303080a00606c06a080700045074204802d56900094000010b80074890043d1404103007581c1c070010280301c000b2068085040e00303032114003100004009522080b1f0458041c1c442c848482481004d502450058a5143d140d0a05140ca0480e001c4541909101d0801008402c5006951140c5445100c168000c55540c041d000318455401c015040e010b0b288012402c580c0b0412100e00f105131075054500d4015412911203039030b91242c0300000c01402d0341895035003c0206c036545514981580966a0301111081c0360349012442c042030030425080c001001c2c0d080107801c03810004581c0c40c510b600801310100090009418191607440c0ca03803c141018a08844103100f086d0700f020f03d62040301040d03008007110b140520071030215a03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 223811007 1250 223809757 223809763
    0x60e0f0a0510180b0901021b0318010318060e0d09061b080a0521010e07050408030f070c08070303030609050a06150c05070911031501030b01051206130501090b030c0a0602 75
    0x20302c841c081660303612403458601c603a42a81d81a229000320000c2001e0404c840114000e5004000080512120940e01c078203246001c01601e0f55158040e10790602c0c02c1400005401a164040e45c4000f440540740d02500018420300c6107010705200800106a090315950f4042c0420085070094410b010140c41c03c0480c0c10440c900c2184180c0c0c2c031109807234442d041420265080c3c0120011034410b0028403a6111850f0407550340e65040741d80c2800340407590740350105e0aa94030304c03681c01002c000e5042000410002c0c020600200b01051003402e5008907140e55055803400c0c40065001100000c2d1508404c00c0036400c14040d09030060301c0100100041e51522600803215004090800180312b10380794028117110080c032070314004206a4805000d020001c0201403543c2d4401c40f0700e5040380034034050700515944640b1818100700d40686030356240c5141500c0b21480044020725040c2d210780c0c412003c036805040c9010701e5000f0041c07243c01050309180b810805041c610654409405840506401c1020907400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 223812257 1250 223811007 223811023
    0x31902010e03160314030c120f041d041a061003020318071706060f1c030311030c0a02190b0f19090b150d03050a03020904020408030406090602061806040b070c0c03060e0f0a05 77
    0x249440c2d5950000109440001c1c0555440402068400341d40440000002e12f09603202d03500c10001c0d142d14010a00c00c800842c041a108107800411481050b0720f000d000c0d1f4001c64001980180844010085c9074001b480d04c030403500b009642c2d41d03040350200c004041c1000100d0704420b04503580c08045061101181c030400da00240c8214032076116008000b85030290b070014400b9181440101e0b03a0340383c6552401a940e1080e00e000300144a010101000c0e26400300314040c070b069100700c080d040c1352202c601001129002a000d180c9066101c03502c80d002039040e218030b42c42c0f1440b40600354030502c1d010501c01440d41014118034080c0303075180045400070b075001e0b00b16039409819080050300c07030b03040740c011a001340100d8000089600c40000e01040854109200c0d508070788550f4210703402959400080d403032100c6100c002c9002c80e44200045000200718840301c0b607201d000c5192242c50105680c503446100b0b06d841e4826501e056451031501c0280d481400800301c1804040001c283c00c0540d80e07601070392030f0a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 223813507 1250 223812257 223812283
    0x703120e1519050106020f0d02010b0a060f05220302120a050c132003040606062d210504140d0923030318010f03060302031902010e03160314030c 64
    0x841c0015198220740680003801d41000ca00400c4190784400307019554003104801003ca91140c180c000f440d0b81d10500a81448482c0a07048800c0c861a000c1d0943e400000301141c0000d004c024001e01d861111070203050403c55180b01c500300300c003c0c6107005014115020070b01d4a001500a00c400d0b001240c40080c0c2c244c0d100c1d100751040c1c18a50141c26400008044d400340f044800c402c5d03011140c813050b0007100514020b0b80030b140304200700c9544034420740341c8001141052602c840c1c82c40c0c0346c0e40c00a000c0c105000d9116058182246203800a06a40344002c1001010141d00d543c0d070800e0009001641070042c2540100000400e540c1c60008030103002040300c0c6c4194401c52841c1c0c1c5100019200688034030110113030190850751038008a1050310200d030f07040d404045c0001d11140701a141c1e903100c2d0054104994005d4003406100408005a2003103000100c01a81440034644048015840c00c0190744919062689404404c50551500c1035052000000380b88650703006103e407000c0104045040126034030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 223814757 1250 223813507 223813543
    0x1603030e100c11030f010e0102090f010906080a02071502030403020d1101061d090106030602070b09240411030106180b04060b0301031707240606020f010c082a0309030703120e 77
    0xc50f040000380303000740c0290b030140d041d42441009079103040c054001d45020340044508039128403c180044403407078014800c0e5400641158045911110194000c25280d0300a10410040820341140c0b90309030b0b8425201100140e0001d07082011140d4080140038812070782030000d00110785040c0b003000d4010181d11010040c001c41c8000300303011060951001004550101096440d561f05050039100e80c03004443c4240203019042440c20201c804201199800500090001ea541c44039166020196054090711b9050342d03803400301192180002100a1013803103400808500c4071140800d0005494280c0d00400103070702c051005000007020a04502d001c02214282d0355260b001600340391420041d40404941710f040604a201c00c1c255041d00004c09560207502101d11414503103140e0340c205d803203841020000a840c80c002c00c041c1c44030b641141d641c4811090100c50015190a44802c0543c01518030400395800010b81100700340c0c10a4000380c0b40e811084040110403404001030b51155030500150720b402e9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 223816007 1250 223814757 223814783
    0x503010c091a09030a17190f02030a0804050a0f0c150c08070305070f080d090b0f060d02041e020414040509070f05040c051204030c031404060905090a06081603030e100c 74
    0x24408200500c2d07941d410982c005112101c1e8100d41b50103910520070158940d40a0800c5038503640100a040343d0003100c0c0e401145014a085030480707150308060f104135005e0143c02c5180c0c5c04250001d58039552980542480b641c581d1400510213400240a074480781401a07900300d40010916410a503107800c0d4250600351354900c007500d0160556024600000e00d003001c041213420350088640d00c48450303a4841c001180e245d440d03075180780a49035001c03182e0380d51080f4281c1001005060070781011a42d0000414140c014101290708141660030076008036185c0c0621043c28540b41c5001d00032340703800280ca0806480c0c202c5c00c000851792040e02500619008540ba40709800540b40b0403011503e6220760710345800500c1c01c19107801801003c0f0710409400064054519444217413413102210708489180e00c3c4c40540e580781c4401e0203d8488000d003880c3c9116519100003c9210042c4421098400060300c04400103007140360207041d480c01c80840a0107803050ba0b20754004150001540300c160b070b405c01240d15617a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 223817257 1250 223816007 223816009
    0x10e03040b0327010c02010f06050906040c231801140d05090a020d03050a02060f060d02010e060c01180c09020a0909091b0801020a09090b2107030210090503010c091a09 74
    0x2080380f02e070340500b80312180c1e103c0503e43c035041d8000220748900340c3c002d00c42402c00c0101803040c0d034424081c0760b074406410341c040340b514a8181d1001040c03105a0910101001c0242c2c0e2449140351102c1c48440ea414001842d031510030003a120800340c0020909004607081101c9074105618045d071015404400e03503c0021614681003041a0011643d0040a02ca000303240ca24004015410502c0320f0005441910081504540303040c0703680d881b0b6400505801d0000040d50011110707005d40d00c40d4240c021504104120b030b024000c2c041c1c902e42c0701400c00203e001621a00d0000348414481d84143c80c00d070310501c144052980c0c400458400c6602e801c43c0801c0e40304140c01c28440c0d20b40d1003003e890748185901c100264444064003e40f0116010351035070500f4a81d500c1440098400191441703504c1418400204810003902c4072443d450000b4404030b4682a8a96006c680d5201c051100000464440034042000303140074090021012900c0c50014020352030280081e030310b1007030601541c400e58400b00300500c0d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 223818507 1250 223817257 223817281
    0xf0a031e030324060e030703030e06090a0504060906060f0c05060106030905030909010905010602010e03070b04081303050a030309110d03140c15100312170c0310080d030c030e010e03040b03 83
    0x101c140401a00303d085032840b0000c03000c1e8840d842402c000c21100f44510341685400b254003001c580e010b480346045448100100300c883e5001e0b140f845d6009074800008160b54a0f0752140c4409442400d000240d00c0741020000707050041d40402e0300c0108950701e00b26800250005c44c20504403241800c0220302300c002464901d003140103a0b644a50401c01c00da00000369605542c02c068105c0328990003c0142280c3c10f050103882e03215071035002d816810080d02040000d8032580003840c00d00030f803030990345841d52a43d854500f0019070100c1035001035100c00100c81848041c200380d02c50840c04550401208009075005001c7c80501ca00c0c3e8464801c020601408500090218a0981c20400f507040054500010324101c01d0142c0e000a0760100b072200c0e00d540856000f24035059510300315205003901c603030300d902c1c03604e400c0e40c8010075103a111006070000085415003041104803041454902003511990694000c1c1241e0a0005403101681046031542808101004880550380f61801107039a81e6034280f51480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 223819757 1250 223818507 223818521
    0x30200d060207050a0204050603151801110406020a0b0606190807021f05150927070b0a0f1106010b0702040207061401030f031106150d020f0301020a0e0f0a031e0303 72
    0x4441400050b4590410002107918604207108480800854507207905240d074134141d0151002e5440742e181d0100d400c001541040f07250513214900040b0300301141d00300d1040c0d5904603520400c00342c0d0101158800b04007040200c5544044290f840906081041a100200e0810190b070380302444801c101141d00e807072007440321000e04800e20400c0c101c41d4411107a81c0d402040200ca05801ca0804451003000c03038509044003900900040b80c1749038a20196250301c0300c0039148001c5809240c840c1490000311045020b01410810340d01d0384403102c01c4104100040c042c10421485c2c000e032a080000141310301044e1034162071041713030117072001078032000c0520b0040010400c07640d2440b0811802c0c2c00000c100900101c41c950741512071b40c0e6460706034010140d280d40c4c03a0400e690903101c0e14001001213905013404241b0840140c0002d200000000200b004a1708aa0204810b04002008107902d41c015080c0b403440c0b40d08000c4151440d540702441c603110101b20960903503191002d0007a00302040245886900100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 223821007 1250 223819757 223819763
    0x1080106080c0f0d050f031c15120201030f1e0f020708040e090705040609020c10060602120f0c0307051c020102040302010f0c1505071e0806060702150f1204060b0301050613020a090f30200d 83
    0xc0e0100e1708443f180040300503c02c1c00c420340c05c0840c80001e00c0628004e0301d203490b5205640074141401d10008803410340e0010000d040610802500051780d5490f400303450000d01032820010307030710034030440790f83d04001075402e49207049070402c001003121550000f18902540d1109004a441c2c00b0003598540c0300c0c2c8036012080003248404280001401004a4200303040b03001c02d80c1d03044002072508000d85c00c0c0d008511019010540f039003101c1c0b449a02440030310400e288a466480364040e100243d4108880040c2d03074290001e0f6030902000740044a592030035554170240d0400d411300b4600840024161320481e10006c0c0918100c0382c0640303240360440240d400030110103a1a6460350300119003c1c06c4510304445c240c821508192504031703642410320a40340a960041c0012003098131002c0464043c1d030060b41c00c0e01c100b0480d044001040c0c003002d03480c40c01404210000460440f032040d4680d02124145d00c0c0401c0030305541e030150700028086884040300d50903610a45150000341c00003d54a01800980a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 223822257 1250 223821007 223821011
    0x20a03150f1e14041a040f020d060e0f12041403030c0f06041e0506061504051002070e15010f0f0309230601080106080c0f0d050f031c15120201030f 65
    0x1da004030120700d5400018003144104040485415003d9844609903409070403007003001e00c0000d45c004090744150740b05e400f444444070b440349240c1c081f0301020002401a21070960303801103400c0400b010301210b24410625001020118182c405414040c41280b107120388640c1c0c50ac02484072074909100340e03888030840300140c8400703100182c00103448807000c03601105d01200c0403018501441259040100e07040e0003000074000ca580742000d00c040c0001c0101c8880c0701e2281440001425911039440103040203060f800f9201e0b481c81d2005001000e04058510740c0104a16054040682d03448011414008007030310b041e8030501c8003008164020000d051f80030349082c100a030014040025186256884560708003180e40a07a030b5039800d03908985d0325014040c0c080e001040004d24a2408400603441c03c50010710490003082240c2d1044e19200c00099074046641010800f452600840d120b01c009590031003400340401c4100305009643e005690054000805580c1094019a44242d0100080015038001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 223823507 1250 223822257 223822271
    0x50907060c15110301081c0c02220c0309020306090106140904080426160506041a0c030c0609240106030c020c0409111e0f04020714030f0304030f020604020a03150f 72
    0x3c400d580341e00c01d02442c445841201940d40606554008000394808103586240d08803501e50700b0002001c02d0029800018500181154030244003071107500c001d1040c0c1d440000b40079000c7c0c0305140c18440c0c02000486540d00d80031040245000e60542c024810070210341000c410b513958038000585004c0c0c2d411169240540c0c0308e03044400c040d142500c590f00410f200403a400301c410961360b10210034050080582000080c0301c104410001c81404c44621800c2c2003005041c4a002541c0c949503400405401c1103e0348a003080c00079403e000d2041020b01d40701c0140c01c1241c051001d1040c040c1607010b21514003010f9403072029429280c400d11580d8103510000b0400d02a005075420854410000701141510415000014190f41240419201100304001d0410020182d50008200c02500f20134025107010789140150508000d040c0010a1601041881241c4900b450704004056103103180104040d58414011f000c056034502c05400308a0364000200c03100259030510104c040c1800b08107241c101403c02e40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 223824757 1250 223823507 223823531
    0x181015180303091d040c0e0c160507050103060b0a05030103151d0d1103040e0a110403020603010e0109061a031f081f0c0c120809010617030d0b04050907060c15 70
    0x505038210f0740301400c100b0030010001400e0701139290070350300180680e06100003001002140c2402c0d641c0400100c61250429a1000f840c49160254132000c889681000c10b0901566030544a00c4000c0c02c08110803a040c2090000040d12030b00c418003024108610003106102050090313007005070140c0010707041c0780c0b01d40c104d108420369480311a595540818030071249000d207002e00109840880d03d0b030200c072040300d8a5501001e4024444442160000d2004200202c0543c450b08000e6000317084003c00c0c804c56602d03180d203901c00c5598581007602c64640320316080c6030350742c0c50005494000c21400f2506c012841d4059070b00d6500052a4084c18241c045c10f400303011307a01803044204000100e406401d102000d031040c0d003180c0428131800010b14030300c58440c101c0000ca1043c00d0956000700030b0400080c0e210785803400b8030140702d2042d044c668180c0c00010a02e103000070074010584403041c21703241400b890514180c000d466800e2401040c08104030031281c0380600101401c000d64894250fa002c11a20200c49 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 223826007 1250 223824757 223824767
    0xc0f070f03080601020d09060c051501080f0f01060608071110060602030c0105011203020303010e0c04050d080912010911040906020412050703140d1d0103091202010506181015180303 80
    0x1030094000c21440c00000d0559400402c800440000d84e9880d1105541060403ea03500419a2801d542500c109040c6081446d14007004030301801c402c00080c0200c100100d02546415a0f42200307003500e03410204100140b035000b042c0d564100225040c030800d01480c940d00240b1303060095200160080c14254001000d94010000b41500c54800000303202d503a03200e5507103013548641c183d4002d005910400040000c3d07000d642d0040d8000c0c10611456140c031350f481c2c0000d0050a502072068401c440c00094400c001e02d000f00c4003084403203201d8000d000d507000b203440759040344e400c1c456214080c1c0e071900300341002c100369a070403a805850010324201c40b02c20f00d42030160f92080240000c44a031601080c0e07841da201000220060078490540c1c4201c07421403281480d43d40210383c460207034145921401c200340043c86500222908200d16400042d80c0c0c41d1100800c080c01d1030b26030344075240012907401d00140c0800c614040c0269100791601d800e0001513100101c80034101c0524003458090070700000300c1003603804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 223827257 1250 223826007 223826033
    0x60e060f0c070f0504110c0a11060c06102c0106030b040207020402130f05061204030f030902131a0616060221040507050405150d1136070302160b0c0f07 67
    0xda800300300303c01c0214030310755551056044500840e4012050640080e07201414292787c028041d0050b03007460141043c1d03d10b0400c003903e0181c104031303100c01e0a1001042c180c1264a80e8101a000600305080c4014030390300450040c080e8a00301519920411029107684d0101c81e50a907001c0c0046642d4080d10340e46018500c064026201d0000c00c1d054002050b1421400766201c501041341e0107032007511255415a141030304409030344180340d224070107200548d1322005440350405400c2008903480f0818a1420440e1000b102d00034800c0400f0301a00340c50b2140e0303c41084985034410300041c0e07a203040403048107070764a4106281c100c01c5844000c1008000d0045100011104180c50a014031f8550006100b20b07440d041010982001841a1a0010400d6128107415101c006070419449500e03001142c4a04210300c0d070140d41c42d0512040950003c3c2c11401c4280e8821054501181440f0f81c0301014180903520510203010b0000d1107000c2400b5034012012918041e0b08850300c599122a1854840350300805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 223828507 1250 223827257 223827259
    0x5010c020108091c050c210a080406150803030406050609010b090103091a0717010609030f26030903070203060609280b18040213090b07120b1e030f07060e060f0c070f05 74
    0x1030805000500c6940340900c0b40340d01f03c041500e03030424200d401c08807008540100700390f4070f00303803103900104024500f52408009848950b016581da0b20303040c1061015900064803150240401c0310042001c1000c1c81c0c25030314841400d10340803589110f241000d442d801d840541c0c0141102c8284148a244c82d00190103007100f0f202c000035000d060ba40e030402981c0c00203403884082c084c00248064000001c014500c1030740224901d111880264030404007041762130b0000c42c1c4142003548005480300c25450100403a580c080e408446628403441c203006030440c0503004441c00c0b400b0903800d1105144200f400c0d04a038000f26400f03050b000d00e00300681c041e00c5014100396002d070b00a40c1004002143d42503075011300c01c810794000d00c215050341c81e50001100d4414454030781e01d491503a545403001440e5130f4508568101c2214401c1a03851196080c101401c05204048001c501d0b400705c03000700007071a00150000c0c003095003200d889844002d1480c0208061066110390b401314003400c0030100e01082004401016564 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 223829757 1250 223828507 223828513
    0x60c0a02100606020a0206091f0302030a0e0303060d11180708040c090b2809090b181c03090309121202060603010b091306020702130507140405010c020108091c050c 72
    0x201e42005a003240c120b80150300040c0c10800c03070240981440070080c10b60880c042d000410300410102e0407100c0e846c10740c4e00c00000940010a2200c1503609020f510404405070015500d14140030000650031440c50000406090800101086981e600441d06000f9042c0d100351006e40e00c0c0044c030051011174125003c49581142d02070205100c1031601c00d001b0410000b0381511040703145848a08050b0118034070603071841c840044003158440c8a0301640c3d40407880341084146909151a00c0038460306001c4d94012a40e05c03110740150f880f80c8204200f1450003490500007280b401909040391282425000b1600307039500d4207040000c010041c03400b9100130700d05509603441c039220f0000301402d888503010315541c40100305011411a0b8040031a0038071085c0b0030000103113804456400b003003050040d21007214a5a0381d82080013806a044880e400c081941c1c00205440d0504083c00279221508200000c2c0c1040808800904040300400500c80c600404e510300c1200503520500c018090360200c401c81c25140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 223831007 1250 223829757 223829773
    0x501021011070b360c120c0604030f2a1401020a17190504050604061101230406050106080609012102030f07171c050c01020403080703090303030b180a0902030f060c0a02 74
    0x45088014030352051412002d00320410988040100c2d41c00f040c6d100c58010300908503140e4181c0d98400c020720086102d01002c0c08941b030b090900b12000414001c01c00681100d03624940e04042214030200107440180100c000c9142808004034506204607000412030007840d40c131281c1500000d0060082041d036110100011907035200b0442d614010313480b8280d00194140005c1c0001405065080c3c0c12600c07031000001c51017510a0340c0491a0346662074071114138994004d0000b44800d5014142c0034000c107081c404200d00309000814100304d0148a1555900c110a030724002280060001d02c002d180c004048542105d10a04440d841c0c0c2800c1c800d1030b10b4451141c006680308040414002020f440d60102e007100d22405035020350305603018001c0344005540c208404000180000003600c13050740039030760711364400d810b40c500038080364822001684148402d05889402c1d200d60900f15900c690380c160080f07903c01c05407000c203140c0260141c0086a500840c0200006260503d008d060030008640c2114214 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 223832257 1250 223831007 223831081
    0x6040c0e0603160311030a050103030207060c050c0f03030d0e01021305041b0f09090c031508160302010e0f040207111f0e190806090d0e06040501021011070b 69
    0x1608a0340c030550401d1007400050f03151081e21020090710452801e010614410340c0038043e51503481100c1480900b9a42c0c5c0c01030040c10303810003a6901820076802c01c01c0d07440d007154a5490b40c844060030743c41c4c481d034001c6d4480c40702504c050042c0d944030361001a0601c501c6800801c00c6000c1d40000c44d04201d4101d4031840003440d464240213031011011411f50700108100e2583c022101060521050001e010141c0741c005041c0803503100f905000005030b0740008031f01e400740e00c4514031400694001040b603885550022031220294002100b03d0380d0900301222140500e00100d94100100803115900038404a146010710031560488c175605c00040b159a0001282d809420490b2034050300701d04002616180340118070b00b050042401001c42c441d050542c13040d80c41c0c5805140020446000210b90400e610203625180c005040d100c1e04801202c13032034141410403000079a90301c880701039003480c1a1500036420100818004650b1318542000c402c4000c0c0c03800e00b02441c000b074011600c101001910065580c0a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 223833507 1250 223832257 223832267
    0xa0605030c040c1d04060317040504050f0601171005040608030705070b04031205070503070b18060109050118090c0306020a020a11040203041109060a050a06020d02120903030726070b06040c 83
    0x70b0f900c1c660f11400814400c2204c154246100e5882c00c0d600540e8400d07010011070340c1d4092244480307510f46422a0354600f042d0030320055440207004100000254824005603a8101001d054604140042c60341c41c0c0e5180401d011032030609501c1150000c0c544107011458040120042181a0003030301207441140da90711119005206600c40038054a40c800144480f5078070401c01005c80c0c078020f50860382003c0098451201401d401e4820345503034440c0c0b02490f00c0703425040c05100d0061005140420203585000a071144184200d050701c41c200c0d64034416141044020b41c0308401560700300108548502070305801968030545400252135401400d404100145868001c0b41d200b42c1d03110604030f944252403401d108424102402c0309a2084898034040317003c0c0c4808003808003c00e019401050075080040303010707041c40d80a401d800d4039184104800d5149417000002c80340d6407580001d0440c4032125027101045c14a1540002407018840041c1f19401d0241c4294031f01e01860003150200890581074406580b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 223834757 1250 223833507 223833521
    0x14031b030301081510051f0f080601020309010e0d06060b0909090307021c1110021e070e060d080c150406060e0f0f060f030118050c2e170a0605030c04 66
    0x3d03e942c03101058800c60342c1040c145540010b0401800c1d60101e85600003d01d9190f50f5090075210354090052420803143c0c070010048488805061003201810f0080000b91688110035003681403080300741c1c1d009941d07201c201500c052140c12980800c5400d44070180c80301e0560003813010340d114401d060301103480040080121003055500a080505c2e104d00022402480a00c0400690354030307110180041e056200d031883c000d4268242d80c0034001525409040521318a1001078116003548244002c2c0320300c40148800540000088581b0307001421645006280e51041c3d4004000601804113000c294490b07030600a4017440c414102400526201c040d0500000000c6a001e1040c0c1882e0001c900c2c0150b450100743d070040e2014107131400390705007080440d094a0846004c1c00110003885c1010081c03250500c2094120181101c4444a407500802800e0148400c42412140d045213180344403c1c0c0e5006104048800209030713059907240c684240002c005100e1440b40303901078002d1080900701d520301481441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 223836007 1250 223834757 223834769
    0x5060a080a1524020c2d04020d020c0a0302010c0306030f080c0a0f0b1501031a01140904060b03060f0f01140f160b09010c030506030a0f14032d040b030a0c030914031b030301 76
    0x206d0b21814000d10000880c40b0340a8031504103508004001050b032544c0010403c9141c1800140840002458020f00b1140c901000300b081619055050001444508240c103c0c603401c00e81407a206d450090700c03542020540c0100401c1b00d0f03402200342040051012080e803050048035820160500c03040010f40a0320003000701c03480d5402c1030002c4400e1641c011484a2945820a5015424010b0000225040b0344182e0440182040080200880d502d00b0148001c685401510655030034410740300042c0452003901004954030f14046020b82034120044140d922044000d03104504460b22030030003c0d040c4806541c48900365003004000e884150281c0910b038042c14005e0014150350b00107032503c00719420340040440f10741800c00030350409003008101030901100210745e90080000031842000d03210101803429040c038013090204129009003d4142c9600404200300860000001541100188002c0d04000d15450380c01a1000400400002611146502c02d030b24241c1c408025201c60f6490109115034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 223837257 1250 223836007 223836049
    0x90703050d030516030c0c0804081e16180f060e09060f070e060901050c06090105070906080f1918110a12021f02031306030b04050105060a080a1524020c 67
    0x84044e68481c1c5c0c00400389006501e050841050203a4510860783e01c0780e0f010480302d5218480100e07001e464000d50003031411041f001403040301424251000c200106115800d08412041031080001880f60071402c0410300b1200200020380d1100c64003a14000d09407810542ca12420001542d40003c0c0d08007140980500e44031040048074250401c05954060442141080f00c1031100341d400400800010380100307070443c0040780030302e0300e00790040100e115980120200511803080c07020055440069903004084c5c503410380b801c500400210000762010104181c07222040701810f80c00e00c1480c0c07203081204c0d9021203015034901d40c0d5800f15140450030010296100c1c0400591f2004c541460b030b0717031400b0f680035170040d2410304154500303503551031401d03520400200340c450040c51800d1419108407400b50804940081c1041e4000000030200e00004007114000c2d65900f00c0c8024401001c00c410f00281301c0c00403c642400701ca2510901c245c240c1c82403a401501c102c241c15040c500d000c40200000408801003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 223838507 1250 223837257 223837291
    0xc080a06090506030c061c060e01061103070c0902072307051908060c0702030708070308030a0516120c02030f0f1b0d02250b03040b09070e0c040b030402041103090703050d0305 77
    0x20400e86e41d02c0f002c0c1c1c14610480003800c560314045c03907003d82401040251000903156240c2000035043c483c0f00095104107400c1004680006590003620348141c680b01440181c03120303e1032802d41103801501c42d1080141d00010840503d0320720000e00314040d60343c01c1c1e49a014283d501c45121603c4081401040199003120000480c00c4000001804a040c0020b0803200480c0d5100c810030b0421425800c1603410140000411400402a0060a0300071400481c4680030700503501d801010012481c1000c2920307600d91050300c60840c800c005071160091002c184071307602c0c0c010240c040c0320340e802882c01d960802541c801c0d039039032090b02280c415001c03040741e000340c070b40e0203104403204035100c54865101c1004007241001007914003100c40550701c2a482583c004200d810203419036449c0c0100c0d64040070f61580b0802c00c105407030340d001061301d0440c0c0b01c000b0900c0d100d443e50b200250141c0044440100c0640c80403080103180000014180c0449000d54103a4040100c40c1c1310403816540304075040700a04004d440c0e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 223839757 1250 223838507 223838509
    0x1b020a02040b061b0307031b121809051003051e07030201210501061d04060501051b150406061a040506070209130b0405070501030e0610030b1008010c080a06090506030c 74
    0x4036402c541c00050006140916401ca0401000310a1203180800e034804030700d00c401c050304200c409421562000140c4901800b035540e12909440c54981d000130810580c0d603500c22a5a0160148003410509205014915010381303c18149911440296001d00c81c900300a000960b03400020803031800c00402030402c0508503001500c450f66050a03420007131507003600750035044040f0710806010340842c1d52501c0003a10b249021401000f80145118807851030201c00b00306680e08001250b40c0c005c6010081d0416004402c0b55a042242085698200c0302070740301003104100d82030303000f0010b0b50844c4441c0100020005402c00d80360196005a64204900b04001e20141c41c180704d105034407405801c09000c0c01c440382c0e81c074203842d07036001d03101241da5900116041c0301a680500584881802c0c030390081410340b0b4031541405107800544000740c014440c10780410345420484141801070140d410085c001c0c40c1200d82d0080035100c00311400940c0e42d00d4550040340424407400b900b405090014014502c00070420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 223841007 1250 223839757 223839761
    0x160b190207150b010c06090807140d0903032f060603060106020609030f0702061c0b0301050a09050a0204051807030b01030605060105040501020c120c0a0902040806060402030c0a0f140c030901031b020a0204 90
    0x261910305101942c803045c1c000958502030290010b00c10b501071501c0700c00c40e00e420110b10145030443c0300160840007410f8002030f400044d00d011aa0075260444691100a005002041c0c0c04101c21540a00c803003811605100002075140c00b41c1030680841700c09a070707654012a01d8140503510400150810020b0f02040c40d4403001a0a03400d00080115161840640c13100b40c00c10034030b44001000340c0d02c1d888610054502841490360107110f042c02804001500d507101134a507925400020b1045a031070000c1090309500031901850100c0002c115852030791281000c000030a02403108540c910708240000700345500c9a420340c1c04444040e001411103000000c104228800305020001d014410043e80400603501d07075020400500321110010f0ba40c5041080703080c2000070003020786008a00400610500b0003c030b03002c6030400d035114980074403440b542da0f20032034840c180b140b520f0894000129500d40c2d040d4002c402000540c6098804000c00040030f018405101b40c015500750141c0c21031b40000e00982020f07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 223842257 1250 223841007 223841021
    0x120c0108011e09020d0c0e0405100b030408040801020703051c060b0a03021c020327190206181f08090c032a060a020a030215010b0717160b19020715 65
    0x20802078182c1d4480d00c00000f00d8001c0700150568a0716003030b041c41c4c420381000364400710341c1d0151414000d07803800010b501e000d08190b106a061507580040054244003484080d10041c20320a0020340d070310390b154100181940c010416a4a00c1d180050351104020b91510961040f600e091042d5070902600c1003041e8001c2d00041d080020b180340c10458a075540d05c05100452040d116420300710b43d410950f42101d0110381c0035112113040c03944680025080420343c0c1c0141c002c40ea84c111030f125500c0103485c06110188203270036495078020b010000400c0c2c21800000c02d00e0040d0200d0303525504555181554030790740b692621140303a01500921180c0b07801a8803140030001003081d401d410140301c1b41c0d50002c1a03403a4060004c02c4016009100301008060341400032002038960002e00b2100c0f5410030144e543c603813042040041c0442c6111020750034a0040c0d00070b9946988441c0408425595a4103060406800485000107480440c800d00c4e10b8104041c400e644e1841c0d00803201101503078024040c80020004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 223843507 1250 223842257 223842299
    0x60301020c01140a06060207080304050f060d090f06111602011b020d0f110d11271003021201290d2003070501090303050a0e04060b0406050405120c010801 68
    0x811607200105000d000d0701c50711540222501510f8a001d043c018216400713500b1003021508000c80c2040f4002000040d03038280c441c01c840030f081021020001400c82e209030400d00e0201401c005900c0240401404002c039000e014038030a00c640c0d4491002d02115114030120104104040302034000994880c510a40301c00c1c83c6d2004294065810703030001100300f080c01004450a1320481c0c080e03000c00020b08200c0051850907074915204548581d0b807020014004068180140c80000001540380d4200705601c10324418003146440506110345000c5200090f0300003a03000300713070b01b0360820b000d1070051003007800b02c0d0072210003542160750110050780820003000c0595030080081e88500e0100f940c0008010203401c40344008020701d0494414981814503c0d413115041c0b0031255000c0010036006000c480c850040c924100c94984c03030020000b0001c1003a50051920b071000400c4c0880d4044d081401002544c00807908890195841c500056850480c142c425000a0007130004003c2c01e501060380c0d003441030b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 223844757 1250 223843507 223843511
    0x7060b03070b070f1101020a080f03150a0b07020f0108060a260319030605010c0f030f0924140c0304030b0a0e0303070306140337120903150204120803060301 69
    0x140e00c070044601030f000340d0000d80d4518a010000c408000881c4022644d0b40c1003030000d000f9904881e11401c60900840708842180c09000002036440c1d59031901c000140382005003512840c6407201c03055444c41c0c000b40e00c12070090b840244800a00c0d8040e42e180341c46a00000e10768080c032800e1403031004400c04c6003851605010701d0300c1c6c00c2186480041c40546006001440300200c6614161030003004c0d50000d5000c681405104200800810200d91040180f0350705800c042440503d590011200340c40f0551203c00500701840340c43e5000c20300f02c140390b103c90406541d15150000329074550010340c8034000a0207001d6104001c2000083da00c140560703032003007032443c2c000782c0c00713903003004140c21544110303925800a9540c480500841c4241c40c40c500c1c19003800c2d0300030304a201c82a03121921180701e202c2c00801240042c00003032403c98605180244440c3d10004c080c222004550000d841c03045117000072542007100d100c0c1c1a02c091003500c00d8804581c1c0601110035203590f2620703200c206078405000150155 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 223846007 1250 223844757 223844759
    0x90c040207030c0605011403060c03010605190e10050d06140d1106041a03060a0621050c0d090b10080a05121b0615120f0705060903281101080105010507060b0307 71
    0x2138102e00c0b94034020889a1060f5009543c184101428128024044002c00e0020700060000a6200003900e003140e03ea003420b041c4003249a003040d00d45810201909034001141882c505600da4807002030040020340700f4060003584e8032607141b05a1010b4030003040d0b800011000c0382801140625121401c2044094803076464282c4406200805040a51950703003215000014001141845440700000b04100d1900c4c500c90031071055800348103c45081034100b4540c5483c0800c3d100011345003111109031b51004104250180e03860003121030722040303c0c1c200c2c02c110540360016540b2030100e2400c2d210344e8050094050f83d151030a4040c00358100e4901c0f603d2040c0c98482403c40841c0030403180e0f0180344c0034014948511500c03404c100400e100480d42c025944c00400c40001c0080002030010705444080720507540b41d51411010a15200405550381c03507182c1c0f0780b0500508494120b0720b175490b0b0340c021820401c00703034540801982e40c500280705071400101c0801400c00400c0c100d074080000c4083c020103a5000c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 223847257 1250 223846007 223846013
    0x40c030216050106032105031305070504090c08120703090608101203030504051006050604030807060b040212010e0705190e03122106090606030c0d0207050d0e030114090c040207030c 80
    0x240e00d4521040302d842e07548a01c01c0c0305001ca21340d101c0e8085950981181000700d108040201980005403882d02844000310300201004400d01000e0040d1a000e0010000300419042c01020055030b80314480c01c80c01440000001e05652504642200d5059150f9155461501c80b045030001e800502c00100e01c038620720017149030401c01c201548154000c0c0c1c1c0100b81c0e428075061041c200025400300340c2c0410310b009010410b54441406403012260800c1403152102400e00b000d0020381a0080b034a90b2041c40001c0341f00320b1141b050340e100e05854084414003d59a103080c1c056620784034202085593744414482004014491010302c1e0304040060180c4032508620445c02c000c9130003041000a003020180010000a1403000e002d070f5000d001140c41c0d0029007003034408500e4030b20010f000c40a440b00d000620340d20701401c03a01101c81055119044400c0c03803d6038400100309130f1242d01158483e501304459501c001080501e05801500f00b10040e01a9000090800c0000d50050004805000001c8040c1c004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 223848507 1250 223847257 223847287
    0x4111b1f020c0d110c010c0809060c01020a120506031905031b0705010210110307081f08060703050a090b0f060310022205090c180a0801020c1501060e030c040c0302 72
    0x8244154480540c0b5503030b1050b0114142401c280c0a4010040c4000842c0403420303000030802c50b9401c00382440103040101d4282280d45100e9200c4198210b14001450b1402d2601540289a1841700d56102c102840750507404e00286c4505503070541d03042c0d04c9001b001407c68082c00408201c02d04c680203d9240601d030008082c42801100314814441d0440001000b8558060101032409801e5071020800100f10000d4880d0a01014002408000c0c5150000316001440b00c08a4400401c0d03440b031986280d40d0341e06155654ad001c603203200010b4284004940750018078045c0c540002d0388030b05000910b0380c640d198428044001410f250f8903100306d0081141110040c4014040d100c84403000507810350001060007040c408070752240b030056609204124040c956802565042c0da09507038080041c44e0b0000001c1c01c441905d411a03007055100007030007a00c5080010f1030804841407101407501c503a030f0342d600907107518182014050b010340000c2d80031103280c909075124403920a224240141400c10300300410007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 223849757 1250 223848507 223848553
    0xc090405070c23031c020f04031401060605120601081f03063e0304060207080301091a0f011403040c0f060f09090b060f090310050a02120604111b 64
    0x1011420322502c90007400350384500c3c051148204980011410401d0390740c240c0d42d120f40c0031310300e403404002100100d100c0d20799011140805030041c1e00d50380b01c1e6120f003810032011010200040b0250319082c4000340050040003503e41d02da0f100c7c07024041d1075a42d1070040d40c0803d401810b070f00340310801c185100c452561591900c40a07500071100011030b0080040e4045c0c0c4080742034a0554000200404554981040841606e0b259003441005844c0c3c0c8a500c1e203c0c0113030003a91002000c203403002c0300116030b4100c5075000e02c058804902100114842000911042c015040782841c0000c2c03004201340004801c0c1801507400c544242183c05070740e941d60980b030600e52119008480002c1d1090350462807981c1c0850604080c00801d841040704844000009401c0d00c00e02001000c2014045010351480c2d40620040c031900ca203501041c4074525144000000a500031101101007062480c0480c40c203060911a0341c50710003941007414541308491081101c282c0940c513413012980f0801c01c9000703190054000030a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 223851007 1250 223849757 223849771
    0x40303231603021213050d030e03060f09240115090b07080405010f03050f0609180706051e16060525020105180c0f1003020d02040b070309120c09050c090405 69
    0x201c60044280781c0203007009104010701e01801c0045c80358188542d43d4407501001c95030700302c440d6001c04400d03103015500b82d500701c2c9150303a140c000d2408001040e0b010707407007480c451505e81064039894000b8003000c0c04440d11481c00a518031841000621101c042600c161000158900f400c81c50302d640d070800b0500b59071220b0380488842c0c201141c02c02c203d58200031441140410781c1014006803410140044100b40c00a02140c0f00d500990040f5520b18130f010405035500f010181a1450146c9600300585507074081c500c0519510115100c2569010030081514032081c40c1c0040303140b40003030a0725604040c100180c0140c64019036103d4141c81404e81c03070980581c0040680000c0740c6031030b014103041c00c0040c0503c0b0742a099002440030042e0dc0d540c41035602e0030f40d03074200d40565200c248100c1c21402070180d0640c01100910003c0c021a6031a804005807080034031a90700c0300c00725601c03000d2400b8000500080144000c1c690344007032184030710030b40100740d00001048000342060007a40000d429240291150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 223852257 1250 223851007 223851037
    0x18070305100b060316121e09030206060406081f0b1c02011812241d06070f050412031404120b0105040c050d02160203030a090e15010504030323 63
    0x514281c002d000b0301c0c0c03508208982144c00d52800c2004c081a41c03000c40c41c12410020060f20300300803260346a008213488040c0c089820001011134208600038201d5042c291b02504ca40c1c1d00081c02490070380107600a940814025021010b1040b00480900c6485e0030084201d40d01c2c3c0a8840094a60180c03403403040302580950030040c5943c4c0009004800303448404035104003408018455280c0e4901602d07100c80e80082251440d5034800580410303031a104141040e26800c0c80d003940903070111903265050380081c0e10b06482103a140c844040d00c1c22800501c0b5030021440c2031204010218440d512682142c2c040c1c00d202500307c201483c0691698400d40000304c2042c01d09000c0c10034808a411018090801550b0820000c161440041c00a010720328440c1c100301d400241c0c500c0246a5048400d402c103130702404aa88034001048064480b9200e03001e17105c094903c10000a11411650420011310001a10b6580c40e09045031001c0b00c4540120707014070206040485088841c0300650010038090843d0002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 223853507 1250 223852257 223852273
    0x161e172d040909032d0503010e060f040509012403030c0201140c070902030a0e0109030212210103120809160302040504030e120102041508010b04090e0a06050702070302040e03160b18070305 83
    0xa03d4602c07803800b401c0c451303910304d0000c0c402841c903001b10449041d22614802251169154800920f50250011075580c005040209104d00c0c44015040b01060007040041c503003940b015a81982004101d610000e000280c1c1c4003a0700000d54011215414803185450340c181c5003c2d22010540e20300040740c0d010700703400340d030003c108842c900a078414180758240f080c000340001d200d1514000d544084c013859005403000c00081c440002010181815100501c3c1c940701c071610340e0369007402000030213100030890110b1040780015207100404110400c2d40000d82800404c000d08540a100c0103140040040b020700140c0c140c901d110395200b00d464000801d0300400036a4590515210643c900402440802440707124401484040300c00d0083e9030940d5000e90000642c1c06484440c3c901d8a06041c40103402e1600c0c14081c081650323400b14600059a00a440a1001c0160741000550b0307403180c5180400c00521000c800c100003085e49100740e421a01c07030f00300154240d28440801d4144001980210780c15880070034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 223854757 1250 223853507 223853537
    0x30a050109031e08090d05030711010f02090109050907020a3801050102010f060e04080901020a1a010806010f0e041424090c060408030d02161e172d04090903 69
    0x84002c2c050f40749450000c2907410250303031150b038451003050b20905010021001500c8184541c140805440514009009600c40c220604c40251f01c015842400110307113240204090501c3e94446000b519964010f00e428038840c0c85902e42d009100120505000c413003800315080500204d0400032000c00c290110711254034200c00682151100040120f503a0300f4140100400302407070246d50f038490382040b18142c0e00e04906004030f04100e04030718000d080d0403100c0c110b042c03115034101440d07040e204281d048031001d90700e0320403405a45140f40b080c0303507149404100081c0040e490002c0702d0741d25103000e411603801d0441c940149480c00e03807000102402640d610104030b08980200000d210307140041e5140746c40e0a06141a858992040400e086580f60700094514100009031203256030380c40c0c209485840b20902c4e907400e0103200c03040c050305507034020201d6107240d01d201e41361044404041c1100b14201d10300b4080d61030714100005c2240c11440038542400b00103200502c60003284d62143c8030b65070f000c0b40c016a041c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 223856007 1250 223854757 223854797
    0x120403090f0e0a14060d14070801050c0d151208160c180b0427030203120c0c010e01050c1b03040503190302060f011d090a0f05070906050f0f01050702030a05010903 72
    0x2070484c10000c18541c1c10710091751290103401c50003a8202d180d10032054585189286010480d0380140101d61900c4208071981d501d04000d48400c0c10041c4043c807001e14010a540e40a40725402944244811000d0450001301003400070030410b044007040d0b02510056448501d900c0156500c2400e03840030030741c160070307072500d07184106034104204460800080c084181051101042c181d00a031130301d01c0d014146401e2500030400c4c2e07010881941d10000391441c2c8256002e81542240b1a4011250300307101040e0390101c018010f851040440768003441c104804001482c1080144041140450004000c04240e1392401c1c0119103404a4030307001001d038000149002850050010110035000315002c0060114208440039594030302991605105142c036092002030800008e840000d040c1d100e22141501040310210b81802140d091180401c282651001404161000e0030400765000100325100d4003198040d501600c002030000d4100c4d0000011550340b1421605025010345c007051540a9070525030400e8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 223857257 1250 223856007 223856021
    0x2502040f050a02031b0705030406050a020a061803110f1c030603021c0209070503010e070e1c0308191104030b1b0301081c03020a02030306240a050d0b0301060b120403090f0e0a 77
    0x3200a81d1b00d403901a840e980e07242c0c0203500a41c010800001900790480e8400c20800d881c8030b8011000f0441c08030070000c00c1c015030b02a0030085011034240d01641c3c20104010844011880384a000f62032520724000901e21241c1c0e8078442c08051580e926004409038850019400490f90150546601c4404500402049004c02040002005402c01c01449001840403505030084980e08018468000640010303500c00c1c00802030b0304da9a101c110080702450307485072889000c0c0d4091a0050002510302500310709446048110f0125040b007004200006022220480c0e84504903c150903d030031301210541c0e1036a0301c03c0e40403191560180340b5132921031140b4410f24140f02c43c1c604045240420607880070351280030080800344901c2c01e1141c82500070814081c0b4580200c44840c2c107030764035900c06d0009892600118031301a2a01c0c0b5050b44e11002d0b081c148210025150f03054842400c1400300d082492251400400481c200200d444000560010900198000d4040c600042d5041e20b00504801c00300c03100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 223858507 1250 223857257 223857301
    0xe150c0c0a05090c070611071a160906090315061a0408150105150703140d0c080108070605030103140f100501090f050f0105041d0f07031401022502040f050a0203 71
    0x301040c8081c4c40114000c036916a980050049000ea01d2424462003038012108050284520f05141801e1100c004480c1c61040c045c0c0901000a82c004110846600c2d101d03014140115042c04824404078556070340000741300c030f0024400b0400380c0d00c3e0100401e00000803401c131109420085010f1117100824005041142c240c1704026443d9171402c0c1c0050303030300f081c02031765039001901c00a6250107240c420000d020404101e4606240c1c0c60750031000200090004d80c0038030001961000c0041202c803c00b081b408100c0720b0341d9485a08690840c0c48140040c0e45680b00584103203e040c404a141035414404008030380d2601a00003120362400c54440203903a01842d04c0e4001d146885d003000307550b034000c3c25654152401079400140c00d9000303a52081a80b00c4c00da07001c1107a841210203680503010005482d1050ba88586c41103500d01400c01503281c00d0b030181801540503c400310000ca00803007010ed40c1a1a081c0c0010030101da0444148048400c07100156105075602d500003003006100340380a0492030220031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 223859757 1250 223858507 223858519
    0x50f0d122c060a050a0314071808030f19090e01030602040e09031c0b0607060f050108120c060402090c0d240609030b0103060207030c02100e0102120c06070e150c0c0a05 74
    0x40701800140c81d881841c0440040c0302c07001c20204d6460340700380d0040409085030b42030520941040e45001c2d1641010369289542c1c54520000406e0002c2c021055401344489200401d081c4003820311314106d089965444c900030030a12507000950000401c1d00e142c002c0d40138100042c0c0c1e41e81025403580f81d002000b44601075070341c400c02c0745003841012030644007d00c40d1403090001d444d03482c59000810510941d14040d01c51828082c5c001e685003a00e620080c100d40e40003045940c10b414a900346440c40c0500c0b80081aa500528002009424518409540081485206032616001d01ca6010480b0040c3c510350005880f034030350b1640b5401280e501c00b40500814200b07904003a165546071744002005000081c4010380100d100c0d801c06010311071016210f94000c040018400d2945002804d80300c03640c650368011303c148a0395141c030110301b00032105465040f07409041c090b62059000d071f45542d014010715400c046450500380030042200c002d080e0a036600c0000d0031310b407840701e1700704010801240c00c8544140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 223861007 1250 223859757 223859837
    0x703060501081b04170f0c220b01020703120e01020f1f0216050f0f070e0f0601030b010e03010203090c01200705120f060f0403121401050f0d12 63
    0x180e000b82c4582e030b2016080001c840481c4146062281c00c1c00355070310142c0d4030390079204202e080c800c01060740d6111105000480707107210001020060381c05c0c07142c1c08821100c86a040003170b40d10718082e04544101d40060044134a1141d590ba01c6061144005e60001c00041c4412400340e010369060101c001d40b44442030060038543c00c0e41d401603081c0c0c0403003070a40820a600040003405c0c8040344031706007011b54008068070100309a48400702d8484900340c040528a016100010842c0040c01055034082c55907c1d20004059031100c00641c020241010028103102c01404000c1c903a9400340010740c0318411800150050055110000d400800131000c40304040d0001c8100700e40023500003034202e003202c904480140045511341c01c06400c00c0d42e0300365038507094060301d4100305076081c3d1814954022842565141c9034041c0340400d0300c0440d0368100fa1891400c81d26001001945020060005503031001440481400c0e41e581d540108032820008000c04200e00301804800e510b07811507010007119425620203100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 223862257 1250 223861007 223861009
    0x120302010608192114070611191707020c0409151a03120304020d0b2205060106091e0302010302090609030304030f020f1009181d0616020703030210051e011401030507030605 76
    0x1000a0303441c05c0e079035000400e501040c05895042401c041c81c0782038505580b0170448013100c0460714510030181c0414112480603076803540100302241b041f801030b030150103002210030401001d0706030300d04240d400002050701c00b4052480d51143d1403032000c262640c41da10303008050a02d41001040404a25030503414810000541c0b500000172410b075078801314881d2265075910104625403120f60003a02400c140003410b80801100103001c0781078882a450707002100707a4542070455200c251000c9802ca81005010400055000750003601504030010102801c250703007030011070703d550011f03071054a07194004103080040d41420703000b240b201030040e100a00c0c20303100c2d0500a0702100d082d01c90301c3d410030301001100942d05611f90045e00401003800c1d9190091051642c2241e50300000c0d07401c1d41c1c0710381e04c44130700d179025a000043c0b40c1d0489500da00503117001c8554101e424001d004c0105100c4c6802d03e035581038208122050390070340c060000446140c41c400c41e520001011900300401484c28945071810903c11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 223863507 1250 223862257 223862267
    0x30f09170d0e3703051e0c270703020c0d0903060c0516080a0c08120403110d0f140915071103060f0604050702010e060705040815010f1203020106081921 67
    0x1e4841034540301d18052020006412051829070f10117040d9000c2c1c810490301c1e0090f0400384003448904481200c1c2d66a0b118802c0041d4802c2031200c011044030f40b264030b0411a2400012280d0156860400500705400c140d406820302001c080c070440000c0c14201f040c02005010f1103085960b1800d072070300905003d0f00e80c4034850700420b121806081608049016201f040c85011800101580301c826640ca590550103c2c40d2001d0095602b103010545a01c0d00703241081340003138550010f100c00d035140d107143c0d69480f40a9543e20001411205890b40c00c1113848210385860a01d8181c0c00c018180180e070315170703080c14040d0202c180d51040c94429001700b01448000e20610040a4000d0301c21600041c1d50b448124040c0d0040200d403101b0780d600d000c0d000400000b030390050007900450300000140d071313001c801c0818076100a030f02c00d024034444240110340030f00c00715000c044116920761090000059994440c521613151001980086601c1203440300301d070313040092509003074002100b8602d426200e00303160900500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 223864757 1250 223863507 223863559
    0x12180e070f08090709060b191403060f0303040509040809091b07021003090501050a06140a03120813080f041802070c05040b04090204050a0c020f0a03020a030f09170d0e 74
    0xc02c020880012401c0e020003070080100034180740500f08280390b42c4454904958004107900760792110f0181d6a00c00fa5805400701d06600f40301d42146c0382c6156166010050440a1501a5034040c4400c0c0008501a243c0b1000d07180101e0050349043d0311a0608400c005507600c00803e103000303d940045500a035100c1500070385020940c11074104800e10300011081703000780340050340608030f50700300341c107205400340c0702c0d4051000e0324554120303072034100002414003010003400e00c402400ca41200c100c401c003052041d801d040e0001d410003009034107083c26444265858000041c800d03c2c6800024081001c1005620401c802c06401141907042c0503403501c603504d407200b00c1d200e62400380d0749941d09000c0b40d40d504d80c080381d81e86078020810046418000c44040c0246216a00d10300503120b411075002c6000c03c002942800550325500610800300320323640458602c07a2080c003a07001d01048400215045401c003a55585070640c0d00002c010451091000502d491100d50882e03000c0e51a0080309020100b4203003c5013 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 223866007 1250 223864757 223864787
    0x7050307080d12020c0d030906050a0e120a020a08072922080c0106030605040209010506030402100c060b090124090807120809060f030103300c05010912180e07 70
    0x4200f0342e0042500f58080c2c400c2034580c20050080060008200e038245d801480954010241004a40d0300d1044250844540c00030703080c0a50702694410074420f00d080014007140f18688103468205900b55245e40003a008514100e607004d0f480c00030040a40c0c0405106114480c21848109030b0f4205042086900d11020340e03101c5800704011300080c1806440c10482d140c4400c80300003001400d40e2400c0201c0204801d07642240700340d0001c00005903a181840540340990340081190000c040141400c0c0c94640a491301119400c0c0c6484450803aa03854040090007040c0d0f1041c403185611030b039036804400800e4050f4000500040c0b401c0fd10050b400010b00c0c10680d03010550072020401c3c9030404140501030241110380c00000010039503501114038002d14101c0e4800e031f501614405031032081814028210b58201c140900314869011030794881c00840d441300f4020000001d100c9031584074a40025401d911050100d80b049085041c00c0001c5c5186030300420200d090381c00703142001e02004001706901c1810b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 223867257 1250 223866007 223866017
    0x803180a1a06030703290903120f0411060a0903060b010c05190507081209130b061804140c0a09090e06060d170c0a291b040305010e060907050307080d 66
    0x900c40d074030b003048010080e640101e80c4c10000040800c0186016410010000c0f41c0ca410a002c6140b0b01c0d0000709641800c01c0b8240012270320358542d2342c1e0150ba201c3c020302c240c840c04604ea0b0401d0481c2c4070070000b484000352a5590b00b04071070540c00d00300705480490f17440a04000e15041032201051000c07800920440c4410030010f06101c007414251320b012000d402030f006900404c509014a030380380034024402c1410a5521801d400c003258a46000c441c980154035070050820001c16407400301c022050000c600d801000000c0c200c02443c0090300d030560032255101e10035000a0300e051040d401c550558014034420f2030904c19a82203000c413589408001d005a801a1054000f0a08218aa601f48a0104200340322242c0715007961089685d2050143ca0958602540c90f90261040f4031034003003109000c030907000904154a0f45446c006041c0d041c140c18502c00368040c400400002e0003030040c070103141d0995000704071034102850b0729030600c081a40300a11030340c0155000c1102480218420f10b0610481c100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 223868507 1250 223867257 223867261
    0x10e06071109060d0c090903020706051903050408070b10090e0109020117090c150d05150916180b0304020f030616030b1c030503090c0402030c0f0f0909040803180a1a 73
    0x1062004c202408018200c0900c1350f0b011580d80c01941c02280342d0b50203542218003642e6599803d81c0c19103d28640000d01d140d904c000501030030300030b130412030304a0f01c00d450251600b125601c030740c03000766003c0d180246903441e11481002408082c0c092198804e1141000300a400e00075800a00f072046000000040145100c00240001c00305106282a10001618035828000e8220404030302303a000755000014589002c01045044540c602e666034681006890186242c90300c0301c80350742440c201580407080114001d4600c440120140301d1000a1280080003516410140304201038982201c0794a4081c0d4444820841c200d60400c07140f20351210203040018940c9101c40100c0c00040b06044400f01210303e00c1090000c1583c840c00542c460ad004e4416114500e9403202048140c2c4000c1e40e001c03180300010301103088411550001031410410708648603207401c4600010900d6610f0407103090312000340100030030035038585525500c24518083d00c064815011199261030380400c03060490f0014800c0600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 223869757 1250 223868507 223868509
    0x30308060a0321020f03271f0203090a080309180a0e19150b030d1107050325060f14030603030d0f0b01090608010e0a180609050309010e0607110906 65
    0x401000516007054815207050b1191440c0080d0710312041510b030040c482c8210010f0320b1340d808016034603561003542c8442292090304d40d0025a109032103407c154010000c0c0003040c0d01c40a070764001c64185181f90043c3d5140c9000108101d0400120303030203038507960010031641040da80c62104100c62100815008409500da1491800003444070b0b0b08022410300c1030400100a0f1102e034a41c1c90112803080d03000b40080208548042d055078521075200d9010f5002c043c220002074000c0980b00d8217001540c040340c0c0c0c003580d1040001d1800c41c04941402e00c41c21007011100300b281c04400300401401c11428401c0240c07948180003891134050503000722441d24003001107641582d040c811502c0214503020103001640e0841456001420b460101038049042048001482c03406a00c220341202d110160080380c5544181e64800548901465200d10b6401800000d0002e80d1a00ca42d08441d4040d500940d102e00c03c01002400114400c8000d510444084c030a10b800208180c00700304110505540d00e4090b601c0e400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 223871007 1250 223869757 223869769
    0x1e030d0903050d090507090509030921012c0f0304080309060703030605060a0801141002061f0812030702010f050405100f0b04020c03090906060a08150307150815040b0a03030806 78
    0x102d0f101480c4c02c1c492540140031000030010700361102a1410841f58449440c0c0e03640c1d030710410084c00d07000b84003151441c0d621900c01c110b03080d40f1203800c0000b148000c903582c41010066a04801c03182910480f11003c4000c54041011007103078001240118a01424041035955901138440e0a9106080000d618020548650801c030010704000d8243d9403240500d0030060140707002401007003248080104205424900340d4180c41018065401500740c2e900e84a0014a44540a800c0c400142d12069800101c0e8401040074400300701548a9551700c80c10b2008000303094498921b14049200c2c1040c0c14040814004100c0034012400348500040c050391203103510028041540d4a0340d4003610226003880314000110040104660450742c016942c1e0303400c003c00c110b43c000e48004800040191001603c01c86a1201c2c3c800b6480f801422912859a217003419003101c40b0395583c802c0041c05850601030030200701d02c407920703249200702c60a00080921383c02085960595110143c208070120000c1405030306d480c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 223872257 1250 223871007 223871017
    0x405190503070b07031a091905090102040803041206050105010c0b07051c060605040503010b09011409100905070c0209071e140d0908030603070f12020105090415060305091e030d090305 81
    0x9180f40225280c5141d0180042007642d081d280c107281c40901c00b2055282c4100420301c90003200400224203000d101040d4014940141611002c0d90300300008103112500f00081c0c0020031400b0121030654240d460007100340c4e503060307020754180020204841c000500380050181e1100e41c5280c01515004d200085509900c0d910004240151910308041009948100104103a820030303802400303000098801e0100642e82446062a0000809100c100a242040c038a50300072060000b18036107280c0781c001d01001c80d07800387c3d002c0000c01c3c450f001003800c42c104422803e901038018141104103902e990424070300306038240300007400c0091004110150148e400d05484510001200800c840780c003504d41403403c1d0b8810b5604502c20310a8010024611402c0c0d10110300b5114051041d09a020b05640151119005548176581c842d4442050072420b400341c80600d0300900d5290f0b0082860704200a00d54140044200b400d0141c01c54145000d4010380000b084034041001c060002aa480c12402c00329218007030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 223873507 1250 223872257 223872263
    0x6050a030b0a080d0f1103070f0c0312120606020c0d020603061c060608012409050a020702090a0507030f0207020105090d020616060203010503190201120902060417101103040519050307 81
    0xb40c140b001c502d0880010302440041c1454582e004131601289069035844075125003800340c6d42c01040702000041001c5031405450348100702c121101520780d03540003100d054640c0010000303030101c200030700d0780c0319030313005903001000f10b030002d800700350f20309800304081c11102c10010303020b80c0c0e001001c1107064035108555061a1600e41c4aa80b010344030b031404401810052094100d0f80d800e1580c08081d03202c0d001006194243c2940c0c460601c0c6150650617000340100800d000c1c1816420b000d044007503103560b004984130700d400490000b1140340081c4054100c50140180a5145106200101c0103076040f100f103400008007100c106501400c1d51001030440d00c2400c11a8210b2020a2503400c00c002480c0c0186d4180ca030100c095818080a00300c03c410440140d0340041d00040400402448520207a4401480580080d0032103162980316540c0c680001040700d051030702540015030303081d0207500300e104404c03254054481c11b518601701034a8890b541c04000302002c00d0b55600a80880070814100105c0c0c00d4168 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 223874757 1250 223873507 223873519
    0xa0311030f0406020115060e010f0804111e0415050f0904020d0f0305190c030c060c090f0b04090b040515060a050705011a09060a08030307050906120406050402120303090706050a030b 80
    0x10b201c00009020300f06c5140441c90350324100c00089500381c000d0307900078415081a55200010202901d04450986d8040c000351908000c400010040d0340700c01c10380c11010103983c0c20700711039a020181070201300c072100c0490445a819054003404070b03a8070030413400c48401d0308442080480e166400060203c40940200034607039024091000c00305500718002d090500c40812048000444600c000e90350138281000c02400030302d11409080003e00715074446011010203181100d1800d48410004818818503000755030880008602001062154041e0720440c1303c0581d010b10250401c041c55020000340c512102c0c0c451280400d03150103842c8030f0070546d140d45800c60000e0051a5200c2e00c0c2134009050f9411240c00b591506c4001011414101480706c201c514802c015891950740e030b10110303a590082076040b540040100300500c80c1c096291121070259018010002c0c1d40d08181c4100181030840c1c44000c90903801c18030812111800c042198000c403032582c24040c3e903c504e044006c40041c45103034032007036005c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 223876007 1250 223874757 223874759
    0x220e0106030605030f07051003051312052d0d0507050f0706050f0f070f0e01020f0109080405121606050f0f030a0504060b03010605150d090b09030a0f090302030a0311030f04 76
    0x107506800c90000c69034154180c420000350b046845484481a006e46a040290303000701a039018420b500440c1e00503408000d01c20350900c0c940d2400c14146000030044001040400d00c0c091212140c1d96a1580c0014065092801d10000704040d005015100c0e024010700d07070782c2c00064010b80c00380381143c3c0c88074107000080c0d503543d0280c82d08000800058545460303907946840010b4400d00042c0801e0f008a6060325001408030044008613601551000480d0460003a2085869680d00900070108610b02c2140303021384860900041c050000c0c030100010840d980241c640c1c2d0004a000100003081d1143ca18196a903413081c48010441032003544107041d0400300c000104080c400050307000c14000c5125110910800382c0a4040509846141c05a10b50180c0020b828994001c84600100a05001494007040004450300c6d2144544401c68420240e6000002c94111527a07010305800c2d860029401c1200c002415500846d0707480003103007401000d005100c0d00366640b5103401c0003614444528900d04554031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 223877257 1250 223876007 223876019
    0x30b0303071b0b07030516080405041508061608070810150302030f0105060906090103050a0b0409051b0301061d040c0510020a0309080628180309180c0203220e01 71
    0x200610700003805840da801c24003081c9440c03c441226400d54040d59214102112440f000d104981058011200304804000c0000c60340c440b80600040710944005c18074050b40340c400814180f07100100b10b0340c0c400102d080101c0d0320701c2d041410b1641000c5545400700b029580c40e510b07a100e0741100c0d0007280c015103152181c1c0a9480d4903400661096864180c0540c00342d07a2802440654000c0300c120300c2d031090701485906000c1d4881c1e480035500050045012074422502001b00701103d841880c141d626810680f9500c900320100b8a03d2091103a041d002000002d01d00501070b00b100c80010701d09090304c8501d40c00b040c207010001c52800003520300184648034011007000040c0d514046174004030041141c06200054074500824000e2160302c0d515030b8000e2621010141500c04440300f1003000341143c0d103c4400c15400f0b00b0303401d194841071003600c030301c246d490030084406800e862030444040460300b400c403a091100c0e80807081ea6a5502141c0802c9440c010354414649841455049105038899040c000150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 223878507 1250 223877257 223877273
    0xf02070305030304141603020307090c0c0606030b01030b010608040f06180606090f06121703061c03030c08400b0c0901110304030c120c090e100f1404020d03030b030307 74
    0xd40041704445002d03807501c1e1001e400310741c144800b0b50326405c0031600b08500041c98000d2240113500b0315000c03c0341c0109507105800c540f0700746c0003074802c18281c1005200b0441108409400340c40c0c103041402c0f9914140d55007a001d0080600002c040c40c0d203800b85c4000780400b1026902035103a010f201400000d0b21f550002d8010304000711801c0344039060000000e020220507c030a04403d400c0840070440301c0146a2032031042d44042c1015400c2200c01500c0610354034140c4260b0800c510a507800300d00c000242300010a11070340900030440e66003001c0000391a01d4504509400c1c44034801ca90001c0f6a15100c401c01041c148183c0040c00c034003c08800c124003c1c4100c0000c28102c80c1c01d899162925120361681640c030701543c08000d0545504034028001c0d0203072000c1241c5014400c80940341d41c1521000901d0a403a400c032881103c1c1c1d03215402d1408091000d0040da080c58503589002c0086a507802c24401c0502400761000e4081d100001c81c1d0420716110741c021034807070328001d02141c1e0342d09041e00d41542 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 223879757 1250 223878507 223878533
    0x609080d1b030b0d0f080c190c0306050601080132060403050c090f1b0309030d020409050604110c031b0c0d03050a020d0806060307050903070317071103010204060206070f02070305030304 82
    0x8002490f2078990882441c2a600d03040084e41c000003000c000d42c0503940d440700c5903448203080c01c1d59481190501151455000840a84207109032881340999241d4a00001520300c040c10060500c2600801400001080341104000035490400d41100c0e40310307440142c2d078001641d100303a504440b00007000f000740003000441048a03a0159a811540e503650509a0270b01d032002e84080c104100e107a240400c14600d15030280d608500038000392450680c2c3c013050300f03007242d1090f4060400307241c441c0c040014074176191151a46102e242541e05141201c1d039911241c8a1042450303580c8041540c2e05c600743c2c10101049030030010180500408030f40029401c1c0500f245d000300d0020070041c8101022501c03150303c03d20310b0340e02800c0041c2482e4296242c22900391410b8002c6149150188100d4034000b0100704041d407820035810100e0003c603510b842e24107001d118046100b1001d8000c1c1e00400c010454182d00150a9600140b10b01c0c0c518105408a41c0072810140340c0c2d0300180a611003c000c1c001801a00c44400d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 223881007 1250 223879757 223879811
    0xb0f0405090a1a010f02030c010911040c09050907030c0504080102030c030f09150103030c062405040e0105061003050c19031505040c020618011d0106080706080f040609080d 76
    0xe05a440000640c1030318030658200743c000c10765460002c40d0354041c2224050326001801500c1c240804104042d08407003072810300740d0b215803066416031090300f4140308a501d40da40616000703400f2030400e030126640c0301c00501440c042650b02c41b1203481e864842e0301a50b018001c00002559242402841c940407500180c54002c15035075540049200c1e10000078180d10141141007182e005a86552016907024150035002e503050b503103440401c2000d150740100b0140b0180c4031099511003d0030002071200311103c0d45246100c0340c0c505400e0000070398501200000b005101e01d00450f282d600c0d058070315143e000e58084000c0c140c103025007503c80d45425801455107801003034650355400c2d54440402083e60a044032410158000001045420b10811010811b9100341c00001c41c803083c00d43d00240c5000d41c140f54894959650301014482c20b88113000c110000e20030b038540486103062600d00c600192001070030003003003156038081d04000c10607050265000b1040001e0104420b00d10044405d500680d4944c43d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 223882257 1250 223881007 223881019
    0x17040602010c0c200607060c0f08060a240302040503100522032712080310080106061b0302100c05131a120a06030b010f09060b04060e09040c0b0f0405 66
    0x441c06191140d00034408030340d041800490245100108401c01004600810303803c00740c204642d0b00469201d010702311030030283e80d0310750f24100c150840003401c0035009030a0600c40d03c6824400c000d00a24191011404041c00380321501e0b420003e0300c2500240300e158031060b018001c0f84401911862254001441100090130306004045150514001032080e0040203010030f0890207100c91503150251130500400c502e1407110005901d508849a501e10050411580342000100f044002800f0101c2940142040c1009105450801501401c4c10126a60901483d40604116400c0c12300c01c0040303140d026819401007103c0700100b0300003880c550003113003030a90304d80850b100004d80000640c00c0b0a01c4901800c0214140020755402c02400352014001034141901c40b000030011400000865008101058204410b10b01d0a051101602c4590381b0043c03014030248403c00065030018100d42d02400101e030695050380d1380c0e2401206510b00346e00101070604c07010900c0c2e1041c0450344000c0c01a10070803548 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 223883507 1250 223882257 223882271
    0x14010509030f0406082e170a1110050f1206010f0e031009170a050304030206090606090408030916030309050406080102160f0213050705091e0a18091704060201 70
    0xc101e0740ca204040c014000307200c040004001a91080602d241c101d40700c1103407055026405d101e044810139036003404008039980030b101001300d4984402c001c1c2c40c040000014000600d003d40324071f802e915002a400c0c5c010389a075030600003058070540480e20000d80c40c1074071b0fa440b000040001c460075042201c03481e0100c0c07180d41000b84081d001c0c160352544000300400603d05400c000b0b0a003006000412002c07030312400112544801c080e0824090101c0c1d4800b0340d41c0541f00d14103818001d103048405440d0810729000001030008a4486d00d4070903a10075001420503070760380c98996400c1c5c50802803006041d03205c04500004070400d688078441200700c1c0c0382141e0a1042d40d456a542c0c500f00e200b15002c1c107a99121285107000050f1144211a2001f03000a00c068004003a0107440419504111080800920002241301051404900704500c20318540403e81c100c500c1c15011629040003805028111100301c42c40b04203000154002d6144194010004561240035801c090519049801140301650034010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 223884757 1250 223883507 223883521
    0x10e04110415150c050303010b09090f0103120302090d050f07030b0907140f010c05070609090f06060c0212070b0a0314070318110102010209040216050601050f01120b060412140105 79
    0x242c103140d640d810400702e5620b0b25000e80e203150b04546024203428061900b10407004540c1c1400914001c1c800024815900c008460070001c102c41c00600030300004c1c81c0180140041500c41c1d1070a0000300c20303810011f980f414000c2c0010751070300700030200820a10520f0700c08d0020340404a010750413a88540c04500e05602c41a2a031525101a03009110101c21400d402211030315000c841e200390034806040c5509403100545981c0d040c440981c020704040740604108022009580c4142e1020849107281000b0850800500402c1c00c03440c41d8002c0d00c5606100e5410800100601200004024202030b141c4c3e2a120301034060044d00305400c0400c420b0b40101c00180c100350080c052001d40e46100807560382d4162a550b5025220609042818110740d420701c44240c3c0703500c2d079100034070b000110001071110030b049501d440707450154160090750003a02091a290280d0b608244007240a00c81c0000c080703214076240b40400c02c1c0740190790024000c81180041c4000340412214a0656403884200030b000550700c2032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 223886007 1250 223884757 223884761
    0x3051207020303011d1b04063c180803160c05040c020303060d05010b0a090b0f0118050d0609060207030305090f070305030a110a050106090e010c030e06060402070206070605010e041104 81
    0x44285402e0560514506406402c0b0075070f03040d0320003041d03041c19090007181b05040100c1d410541002d0007050000e081080110b90040c00030141c0911001c69400e148111490700d04201e440c00900424800d582c0160351600e840b25851501a1091030101d0780c4940f10f1000003145c2c40d40035101075400c449004030201d07880c100f07801040f01c80c4c00913800952850700e4510510190040c400e0301554030303542c1c880d6144c089944110070724000740807100c00441d0f040410420841200003142403581803080c4d210203d404c2070498000030040340d6003220020710490795402c000c4007404400c40014004c5200040c803004264240d44958001d0440a00722031035a403501c10001daa070390460002400030380c41401380d481818480c0ca1540d80d070b02c80101c103070f1300503014954503107082d1516074100102c55600c1d2041c044641509114403401c2e201946010700c05038031080d03c3d6a40b9950050003050186400040e640c2c1591039000c203c5022941c4404100705c0340d80e6440f421303401104180c50484482c2060b102c0303480249030074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 223887257 1250 223886007 223886009
    0x30c060a0b13200c03160f0209070503100306020c030d02030408030f010e0108030f090f2e050a14030601020a020d0b010303080114102a1103011d0a0605040318030305120702030301 79
    0xc841404684244002c0039145401c0f69058401303078442017100080e1040640d4100034000d11031804001000003030300c100611100024074190400506000700075040e55200300610071280c200c28010b96070900e04802071f045201f240201c00c038450001043c003081090000c010b601c1806a42140d12059880c2d0b1a0260426001e12078003415910911500c512000410010001c90740300804412480c08a50042a240741e05942c0340800180400c1c607030003c41c0a10044c3c371440800f030b440d0086c6882c05000000d481d80e80d415800030319640e00070000030f400d64000c02c034407644190000c180c18400790003480c0c09160041e090004074001280840005400c101100c01c10b844104000c160407507000d0001000c48060030413040c45040c1d03041c00003401c170324840c80d14090b03070005002c0c004282c04035054000345402e4581c0e0b1b4041c01d40c01c55145204c0388000c000415042101a4001008a000d88170350404641240a03a10480b040c000c441070f0000c1059005001449020407500f50207115959213201640c0707901003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 223888507 1250 223887257 223887281
    0x106081b1804020a0b030a02090a0305011506081e0a020d05040503070c06080c12270706090f05030d11120d06090b0a05061801021504030917010603080417030c060a0b13 74
    0x42c5850505c007294450001d540e000b0000a0010304021440f000a113640c800d551040c0c4803650341d020400121003c2c031307102801500207404e09001c0e5041450007280c1e0716040013501c042407045900803400341c410b07680403079060300c001d000e00f0310403800c107810300756181e9201e15411542c0169186000611a0154108512824a640340c80d0f08210801480c0c80020800901040503201c1c0006402d031560b040345011210781903010001c26080c0d00345480074113010515003226034010f00103c0c0c10082a42c0010b546020a0150314100d1580640b181103039223001311081e0400c10444010401c0c0340d8444043e0b0100040b94010302c1c023444003207419424018400040e005086d04601c08010000712155441189480030806104845824035592248074804c0c1d01a0360890014101d00010402001a1f07040c4466800c000310081080e1403459540704428031413485a01505201c2c1403110214803000d00c261081003840c582501d00302d2500c40f14060040250310030091186c110401103008003c1c15101d0000c2c0441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 223889757 1250 223888507 223888519
    0x1061203140c011401170307021c0203070e04030c0309050418020609061c050601020d14030a1d0615030105010b1305061b0d050d180b06010e030106081b180402 70
    0x12240c408403801c9929040c8003a41000030001440c0c120401d204001004482c0c181e010444d5050101441009503001c250352801d03802880004003590310840c0c210140c20b800d0141c010300421034400b017414030046900903551241020b00b00810300d60400c1450041c54441d42c0c9400c0354940300d204000480741c0849d2424004c034201c80542005080110003406010300c0140b94a0922002100307190b5a404001c840ca440e8548407800d0240300d580401c090300d42d048183c10040d80c81100e0142510450200904c40e0a101d5118145200003058a52170450f42181c544103072940361502c2c000368080c6101c245c031000d004e9860070000040300324000041d0340c000001c1c01842010383e80340c80c04000494000c2c80740e0103880d0300c1c003116448050404001c110051116921100c1d240c000e200c4000302190002d4000170310303008924075440c0000b200103061a81c00042401c041290140346008070f801064190002c1030f0328465890303017503103003880c2401011030044100e44214444d541c0c030b26250b100c40020341e0001d400030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 223891007 1250 223889757 223889789
    0x2100513030c060e030a020f0d230a091d09150c07080306030f011401090501090504020a06120f020c0a05070f1409040809040c050307080906060123190513080106 71
    0x40d00c255000a49a0301400011a80710290700070340b400c5902c5039506c0809a80896800c0c4001c480910100005415504005c02080408010868901c3c0404c410141c120380009140080d5401412004041d00b441003004030125840c00b01c5c0e81c50720300191145100c40c0302c1c070590796607a1075034403800348c0c843d6810007280c0b42000415a29040581c0000e441d85516025907444109655003d12440c0020002c01d07a900c0003e5140009540407508103030898105c0c41d0802c41004050b031034404905045425520700804d18100c180117000007061406011107141c7d00005414184150004180c41c1e854003c0c401e80b40c0103642e50002e80359088140c46201c10b001701c0c404881d8010305e440c0041c00d900c14023600549140402480c002801c80f139010910f11302240000c0184441c003071b40f1074545a0320030128002441c082c10200006407030f800942c0304841d488400b4403840c0c002d01031100240c0b01c0d01512400031294a00440c64003502070740080750400d1034440d41000016294205000e40e001b10741508030403032010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 223892257 1250 223891007 223891013
    0x140303191b0203090d021206070201020703090603050c07080f090a08100e0a0c0e0702030c1501061e0e042c010504020907020a03080105060d1113080c0402040503460302100513 77
    0x740c0341c5c102e07043c0e80c0201103824442d03403403c090140f98070418407680016581d844501c3c0160089140d0b0304228200f615042c10011a01700100031901d01c2908400070540741c0540c440e61031160301c100c03d206900902d902c500019001c41c0000c03485002600c8003014051603219845065030740c2c1c044a00038295800700720301003091407810118030707820040034415030345850307600d5454520f880070b1104001c498128804c010460350ba8444a04100c15442d000114502860302c28002d1440f10354020030b5208550f20810186130303003100c440d8070000c0c2407030700340c10179000d40c0c41c1415070b00821085400380e0144040340d0000e24594804100a0411075040e200e4204036404d01c014070809070401d0281070b5109035250611403044140801602802203da42c4000c90300e818514445c0c1480c00380c070351960180d030041c081405513540c0400c40701c85050b81c44038103c40450020044030120405c40440c00360b0814441d9203040003269451018a900d070094088a00d07038014000400102c40e4112204560201c0c110050000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 223893507 1250 223892257 223892269
    0xf080c0a1202030102160b010812030f041b0f08011b03060302030d0c170c06062404060509130905030324010f030507020c09090c0a0b0f07030507140303191b020309 72
    0xa864000f070b0005003030011a0020740601c4104110580301142d400340108862041000064240c044001f800c42c01d43c10103903004900d40d20050402000d41112408281123140e07a0360018008001050907004140d41d01c0103400e0090550f039404209a10b00801e81d00500303406800341c001203039030103801041c903940300a101301c4918011400c00c0f0303403614900550341441c075086e8005d0009091000c0140075a42060703002c001c0e0b4221500c1f8035000300aa209011000d200c401000e49080321000e007440360ba2141d20720300182e517909820220a040c3c9151841e03079014070a001010f94071032900d20341c480140b540b03003007031003d02d1a0505c00b240c4e0000c2d000305080342860788660003054201c0c9071030044400380b110b054005407407080211401d40c401e40c40b4990400300792510440c1000185501c1d944d40345807900c4094000128412038034041c05000313001030140d08010152460311403c40c0e0444c181d80d1039080a5100c41140070300305c81110001410040e841c441210b85591911a0f8200d540046103400059414404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 223894757 1250 223893507 223893539
    0x905010f02070e0c09030c030609190201110d0e10140403030507290a2906090a08070b03011701180605090f07030b07020d08071b111201060f080c0a 65
    0x460090200c001100e14912810f81d010348010300540b91502d03200300034035240160301003075a80709500c208140090b02401107100025071701c051681060b6181d181c00145c1da065070340c032a00c0c0760600c244214829074980c014001c160004088071401010300c0e51030303422106030310303495460f00c04010100030410029020f01c2c007c008141c410900b58003240c070010300750449204188100d045803200e0004000b041000d0384650940b020442c603414069860b400000000581c2c07425006004074400100400e01c0c1e03640c0c09104001b094603074101c0e4002901c0d8201c409094000380b1481c0080d10070751420070008801800340c140d150481030256914404251a040003511000e80307084200e00074410703e00800303031043c003d000103503000303181d004854180020000e18002c161183c0a041194440a0145590b030002c018100016003070511544000355040a001880746100150303448031050804810544064000204554105a950003125541d4010649507440540345030b40c0040d038a4400d106c04010400b00b05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 223896007 1250 223894757 223894787
    0x6050409050a09050f0d020607052106010309080301080c03160308030f040303060906060804150608073b0a06090204080309130603050601030f060c0c0f06020a020a0203070f0311060a090501 83
    0x814101d05035104c00f0b04124003501c1e21000c03900407044080c2e8035601040740c00d80001462422500e4884c0040c0f03040ba1315001e400996200c2ca200601040442c2c0c400e4000d00401c5030001c0b807160fa83e596900149980c0e4a040481901078083c8032250040c4400c075080c0c40c0220b9410900c80362459860340754190f18017030000c2c8101d083c19039846001c42c80c1c0119104400142440f43c4480500e1b08181c00c0010702e0141c154034481400d07003001414030040758080f6644088400040103406141c80c0412000361221204800c20340408481d01400b442e00c10b650302d950300648048274100709403503c406a060591107207002d1000300e50303c208404841810268041e0154543d801000141c0e00d80742d50368107090030020707841034501010000c0039005000591042d0311010b81d41c0d003401481180103a4035000c850114540161005a01081e0700c070249009211110f241c5d58010140c0324240d40391148510a003100f40020380f0001c2d18014581d0460500c00200d81030025191203050005190900440351904603031031070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 223897257 1250 223896007 223896011
    0x150a0b010c0611091f0504180207061404030806031c0507080712021c05030103030909020702030a020a0306020a0e01110709051008160e150d1712041506060906050409050a 75
    0xc40c0410903a10a660b4485401e0b0a444d81c2c81008008008070890003000307554a050000384004110b0341c0100444080314508194003580c8003800102100a0003a081c01610181c14049400654032440d03041c84d2065100f911103003d262500404c1c10f50350400700c444862405281c45201d4110b9000f40050207020f4842c824040c42c0259039554510300c401007400810241c1e00c03252221244482d00c1001d400702022a141003030856243d610011b1130f030b85080c17040c40c03c1654001442e4003591400c0c01060f0b8055005852907064960380d240c440e00030340c04005070030001820304941000319803149030040b852526000088c4a5541840d1014005200c050b15040c0c080c5001400050741e490b0070710804038541d100c1010801218a44640088003070070080082420b86030580d00100d0558405810a0040e604842c84200d104071403103030b42e80b1602c210000c003401100c1103000c22041080c2c02030405101c0d041e580d020f010166513207009550045160140c2004240700b84401d10a000c4031350b00c810f6022240e9080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 223898507 1250 223897257 223897277
    0x3060a03140a0213090506181b0a120b060f0301060503030301051c17041d0613090201030e070e090d020c0105030a0504030c02060f0d0b090601051804021213060b0102150a0b01 77
    0xd168001100005801c070b6220700e881c0c0c040c00707800d2141035881b903c3c130852646822204480d0b03644500c1140d044205006050709942c0310780c0c481c2400c1c4805000300e1640c60078001e6560502842c8003100b241c50300c0c85033b0741481e91840641010b0150742e0445e4005402181182d00b04404c1000c0036205042d014541c44a0803090343c04684502284072180c2d500c894083da56504050700502d20100760540041c0e407800103028800f803901e8a161104c2c450220090014a4080702c1c8012800303050b41c00c0390b010f060300c1820350109820f40305544181c000e422040480d102070031440401c1ea103034664201030701d000c540184006484000917402241e4010711030320b04003102c01030650003e52a50004407865070f030700c0c5010820102c070b031a8500c2a54400c03803040314005660b02d0301c00b0008103540b00d501c07003068810703100d42d2201c00f69444580543c0c02010118451407540e02c0e01c141c103000d01154541c0d0643c1c01c1800c203000d9610307950000c1044102c81c1403001c1e04940c95580da030401d83c050840b16442c241003241d407120f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 223899757 1250 223898507 223898509
    0x91e060d0f0b06270a0317030402030709020408010c090e10120501140a02070203060703060311130204080102030a1b09060525240b0f0d0b07021905070f090203060a03140a02 76
    0x20080909070200401d1019050013222202d620002d042c04160040c1c01e10542030002c1003102d48205480f08100c04002e50303d0303a0320320200e0b00386100e60744100b00c528004100030038280e006401c004c2c800c804a40c1c8400c2960f42e1041e007012a5181541c1c1211080c08800b0280036148002c00c60f5403825006900214407603800d015000940707001150740c2d0181760741c0414608110301d014840280c0000c001d1805100c458116180c284000e520280d1491140901d800306c541d800301c0325010b850007803510030000c5469281c40c5500c40050144000c0803078029401e01c0c610014240a40c560308192445951198282040b0010300301000300321240d03500c211200e800c460300010303405903200404d500401c180d49961842c00c100c0d078001c0d54480740c038540c850000c18115000c25140c1045410046402c490225025280c01c04103904003041b0f20004001140c090001609100c40000d6001c204e415000c0c4900d00c4a0796002410200e0100b902c1060380050882c81c2000810340b104000e48c0c009104006075550071200754 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 223901007 1250 223899757 223899769
    0x1c060905070326031e06011403090304050405061008010b0d090203190212120315010e060706090b010603090809040b0a0e0709150302030739110a0503030c06010905100b0a0203091e060d0f0b 83
    0x5541d00c00302d2f44001814040e5003094010160011401e0f201303480c0c8071035442009041100140203000c0325020124800075100c003a03411100240f80c024082c0c4001c0410712107408030383c0507040030036400361a403012000c2c005500028842c052016404400341180c0386c1e184544c6540a0a02d0203c0c1023090300801c0d4011641c4070001481224170070b542c0040c2c1c000712490b00381e81240059100900303261a200800000c1080c22041760305980d81160002440c1d4100d40c006013140b238294100e000065515401c12640c00c0d0094100400e46800b1946c0200103030506c0e400314180d2108032000c1d4000b61454030b140998400150b1106918050340700584440502046580c40c0c6001806064a02201e218106a0b20341810030b9110042c1c20250701461800b0b07030000301155500d106200c0c03d00c80645d01d400060341c05005150440c080c00c1c4811205642e84010340e0700941d20b800503445184185400440d400f60300503166a0040007002c05070076142040c0355800158000c206200324245071035100c1c1c154514540e030b90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 223902257 1250 223901007 223901011
    0x1603090818040b040c020c0d150e0f06010f15030f0e1002120c0301030f0b07090b180103050f061003021b161d04021c060905070326031e06011403 64
    0x1081c268204250080401c81540d003036982d103d0080d842c1036945e80d03040f079010564040b04070b0107444003207500a1618200214400c0042001c550f04e00d401a001500c0d100420348151010007201103421301e03603c40c0030b0009510321a00c9089903810f00420740e00d0700ea0380642c2080707a4031901e1801c0061041e641808023400c07c40c0d90560204426400103005c2c2d24801c2c0700c0d0100d03811140010f01c890840d0704641e140d415a1030298805428801d1318000140717814440c921a80c0545002d040c000d481c0c0b81402d04481d071a0421032090390120b42400002540c501c03121480724030407400100002150803100c1c074241c0003035000841320b0f050002000e11205036404104505094200e56640c0840d02c3c83c581304440c801c020140a6051200f8107070000d20026030341d504080c994032110041221000c0ca11071a084004080d040c0c0000c0240c040c00f0300000038804080b103403540b91b00c4c01d00c200d108581782c12042d40c6194481110210400c40207140d11080000001364905c0c0d00c1a010305000310840c1164500c4e03c00c075001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 223903507 1250 223902257 223902277
    0x1090f0507170708120c070803040608150105031b160f050d03050903070f020118030209090607020105060d0804030b0c040305030309010204080c0f01020606240a050c011a0916030908 80
    0x1121030100030203100b941c40a240028036001401915007460902500c840c0c0c441d01c1040d402102041c2e001b820031060110500401c02041240d65a60b6144009850341c00304540884610303440950310321081d401142100d104510120340c01c110400700f03109640301c0b0741000d42903142802c0c034451a5800100c010361141c941901980041ca5224400c0d0070013015228003d00010041e00184511740010340c05011240b00d0721360908215006410107041301038103038415807000e5400000e01d801c2c0700007030340c01260a41c040c0713100d40d009001550785c1105020450010f520002c0c039140c010801000490007840b61242c20110011040345440d581361211480d507041134074080010795002800300b0407041c0400200b481402c0a03603540500d0078440700040d4849100508860103404e0032607600741d8181181240403541203d503040152508496031004041b0380051761100f4481d844d100c00c11804480b0b02d014034034030a0000305021030503136611414940303c111001c0d6200516484840030b100180900c8058010085 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 223904757 1250 223903507 223903513
    0x6060c051924020705070f05150a120603060902030d0e0a05090406110a1107080607050d0b1f0306030b0606030c091507020d060c180806151807080f01080706051b01090f05 75
    0x2245c1c2091070620203558010140e54000c13682c2089240c80c3d82d107490580070b04900e10581c85080428095444022990001580b1440e0003408001c01140e41d102443c0c80e8000c1c1c044501443c041c517420b4482d295406561907100001c40340421032442c0800a40e42e105114910100d00032903040d00030502c6070009203004001c12030004c802c1d42801410010368004001e400000c0c081d905001d84c02030902e00c594004022400d1f12201034007020307102c2c0c5200701420a03541c603200d522018880f0b0020000e002a0108030b80780301c0814049841da140140642c0d004821800704585480c01d004100051403107040300d1070104640a003c11030259481040d0b13211030f2070040c0c50214075040000c03002403c904002c01c4800d00c000315480240f219140004850381e00c0303165040c901c10f03c080031500003403c0178010300c0341030681d120001c100010558000585402817031404015500c698903040300d1a00d032003c502a440006405001e500d100301e2842051800c25900d580c0001112030060300c03000a42440c8080651f5036038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 223906007 1250 223904757 223904767
    0x5010206180c0613051005040e06010f02011e0203011a04030507090902130e100e030c0a0201140417010c02010507141c06030206070c05030d0f080c0706020f190306060c05192402 78
    0x4185500c0c0c40120304658604030723240c1030400d80c030030340c0b590b20180c002070401c00c6010741d0003040350003548402a1011031403101001840a92102d002962003406101c686d0480c140d204e591a040700002e4400380c2e42c7c0314001c2d2a2031802c21150400a1964190070707a40007100440b03c181030500c3c0c0c0f103142c0c941c401b031030080c0c10403401c404a16030544800c0c182d03549032940100110030300d070413012601c0030000d58240fa1441440f811900420210b020341d0300001c0d8101c62881b00c50300360040560010840b003001d03400074072980d505d1f03000030707100e01664524030340340078404000c2e030009146445069544425a031400151440d240d07000710340690007140c02102c544008030003d200c58134040190b03954079881464130030740070303000100010810f2202900320a1000c101103040800c2201e01c1d0141c4e0525110800100d480da100b410781143c500c407841103214082898500c01142c141d100e00d00707008120341c0101c0201601c50301000c051100511101c01590301281c20004440642030041070414080d491260141c1c8038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 223907257 1250 223906007 223906009
    0x240d0303021e09130c02391c0b06030a080c060405282607052506080f0604090501050a1a0402070203070b070f0606030c17060105010206180c061305 65
    0x40d5a80740c41c0c0440b06030910008245030741c0c0c1e0030501c2644035442c80102e0404080201603103051024204c0703881441d43c001e1814514038100703041001000b24404c10014080314001071003028040001034445101c5c800000c1004604038111240c0c00c8034002c1c00320b0ba025407068a0300715503508050a14100b40d0814401e01c02070090030072003010300e01c1d0503100d070b041c00c0c0034079802030801c040c000d4800030004c0c0821401c803003417a0701d0111b600c40da00c0c40482c2226540e00140c60040d88480d2501280d0f42c01d110200f02144158003190b10706802d503003841d21510390b80c1e102c142407642004d0380107000d6a44035440e406035200042080c0102c07809a01400070100300300d1209284600b2b030740c0c60002c007980268418007041002d81e600140b1001114000e0034100e81e207480500b0000341041007100003a0407035003043c42c000104083c3e1040c00044444c00f42664108100916006071a50000c0c452103005038000000308001c00c04121407071000100d040c04558000d902c1d2400316015800c090140034402c90a21010055 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 223908507 1250 223907257 223907287
    0x18060a08090c1f0c0c0b0301090c09080109020f040504110a060815010203090a030201050f160b061503040c1401050c01060902030a0e0a050d0e0a0518061003060806240d030302 77
    0x1103207404951403815643c1002000029402d070b400280c040115040c806010300074103404407005017441280440d80da60316100749101030481440020006460200002003041c4103118580350342c1c5d40100f4080c078490400301080003601c4c010308243c82111025a011403581d0340c2d2580f0400a02c46501c0c1d150103440c0070441d12007a99805201c4a040d9041005605869960400150292942421300507207a29101d00c0840d2980261816041c1d00121814554140200c2000152044904881c0740c4400c014004200100c2c0c00140e0f4010002114241d041c000d4460000d6400d12070710044c0340050900740008040ba094030000c0d03000390102580002030080c030041c0c81c0901c40180f0003142c02450130b0701040d034070313541e4031142600c0d200204150000c50401940d1511005801084001d110503024108030810b410303910010750786240701c0c554421050040318042c0c0680c5003120a075401820541d41e680090202d460f420562391249210000700030145640c07000840c01289000c1c0c0e8005071141105060142 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 223909757 1250 223908507 223908523
    0x30c0b0a021e03090a120204050a0b060d0e03090402070606050f0105030c030c1804051914090d03050408090d05030c060106031a19030c060c05010515010f0518060a0809 74
    0x4900504010854140780c0014010050448840b10300311601c1c00300c00c07801e05501500341e0241d0b2007003643c800060f2400304200c031888085c2c001c40f8100529119607070b507202201c1503180001e0b00a08140046107400b080c40d0301407500b007948201901d10340030002000800f241c1c860a0103d034810f942d0138040c8030a0501e440c11040303820080c00c00500d5070510b40b03038014050200400c0403208420014118200c02d0b44a107103208100c10151044c401414840a442034100780b04205520745c600c5d0001e080124800386611900a14404018140c910b41c0383c44100d014000041c0252404a4200490b20503038070303103055200350f050190780a140c5440050f0516402d04806034080d40401d0300341810a1450102d1402c00221a01c04803100e40c140040160758041caa002d59002410960108200040d031a400065440400d0701c202c1c020040b6035640d404200308505100c1103540000e88038403e0001042c0560300a100f0120018640362901f0f00d50000100f40b5805030ba01c101c00210007a081c4220f1080030040e100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 223911007 1250 223909757 223909769
    0x60711060a020a3e0102030324150d0c09060e010315080604060204080f061b03130b0a0501050a09020c0a0305030606040f06120507080402010c021003060f081b0d0c0527040606030c 79
    0x41c40b42030718600000e40d0b80c0030280c14009c0d0f0001c002c038280d070b4000e80d0000111101c1d01c00351459032104140c42d01c00006400900c07040441c1401e210107401560b12440e180c1e41a100c0d16250b040c206004040110f0003804841050b003103004149201140c8120208403680c4610300c1404056500c0d420580c44d6418030f034449280b610a0340c0410141300300780445050030803040b141c102540e6100d41da60200112001c1034123601500c041c0400b000d2100313403140c9410286c1070350415039400213003550f911311480403032046614000711a0404001c510009200b680210b070040c1c0014403050500b61100c0d009014446190f001c0d00115010390030403250b48845e8003c85611042500303000c0341518064001a19031000d141d0028404d01096074000380150080e800000a0000c104400072041c0d140c1038501d51350f403c1c0704550320b070042d440308035000d07685071442c0c00ea400301e0341c400d46d140105403800061014045610320140c0b0107200713078422143d018016038000d40c4102c3c003401011030100d14505010032240c1454102c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 223912257 1250 223911007 223911113
    0x30509040e12040f05090c04090506011b0c0e28090f02060a031a04230a0213080703230d0c0206070213020d0e031911070314070e06060711060a020a 65
    0x11090b00018030548c0d08491080001069698900c8012030b050086003401141100d01d40304004c00380440c0000c1708084c2ca000c14415092519881a400400482d1b6129100640d000994074007021a4a81159203d01c1c800d801c01c080d000490f81c005906504100110000642d54000201d00640f01300c10384501c40c0000d440410181c0520b8146500c07500080c0b85a1040c0003840010800040e42981114482c18030303480854145501c07400001c1c4c035494540300035119002c88034409a551011440804140c01150004051990320007606880c03031180c0800c00c1e0b034410401d100242c0582c50300c52201d0031010000300010b80d5204820207032400c5a54030b1000800c507178014400345040340c40135800c01c0306044144c10607031124044410898a8415241c000621a17031100e07902c0d203a058000100201650200080105242d95003014801507016400c809001c1d44c080440c0f000359811300303200400d0355411a1043c4c1d42410030946505040403603c152004414000030a18041007440300902208044c2d0740b01c02d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 223913507 1250 223912257 223912261
    0xa082508010b0a090509010b07140c0f2812020315160c05030c01060e040c171c020313081e031c0b010c060905010203040b01080303040b04030509040e12040f0509 71
    0x40c00100140211454410001078003076125015a800380c00400009050b40b07402c0da10b0f00320421180d00500b200721b0b101e02914407075003200f101c04980038010900103041440c1c3e001c1d01c9002c0118480300c1e142850028409280b22100c00d0745281039a401901c44425810248080d500c1458a07060065110100101c00034042c0070040b0440345089a140707030a450301840505c07a40c14140e00750322820301d8a500302e601c0c0840c0029000500c54141c0d01c07550145d110640007554446424480412003c0b0076034950f000381062030301502171004a00001505441107900f070080041c9245400d01d810342110005610440c442410101580c5030068880030301c001035820106a8400a500c1e00c04103485801070746c0e00c3d0201d15810380d2159098001c12a00501d0a1007100c149042050003540300362002d584001e25003002041151002003100d000d1541310100c1d421030b58949e20100d4554200a02481c4d002d500d82c822152544000c1103520300510b0020000c0b07584618100340d03c43d620170310f039104600500d05101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 223914757 1250 223913507 223913581
    0x80403050c0129012d05090316090e030c06060103021606050403120c030209130b0402270307051e211005090d03060510080403031404060c0f080c25080a08 68
    0xa1007600841c2e024030031001045c0900c20030744850007a620040d8051082e41e10403002800e681c06040704940014000300202007011018039141d00c11034a4038101c55011401160403540b0960080c500f403250704c01c90b0700c246401503813018181e030300507135042d400118030915a06200c0b0300c5106234900a4054101145081d90500c041404c02a4200e070060442d17646284514041e15a030301103401d0403200040a50024400c640c04c070481c0030518039458000c1c8a4031074007044d07504180b000d0f141c0320310103c0f4024020354184000c22030240d1350400308446261541c11240a1a101041455040c0081c170402040c1071900b11501031400c0c00a108a000b0541410000c011544a6010301d149858162620007442d547d0350038150043e00d0b000003240d00d07040929080006002266110405400d45c82d51905170000c4207070740403699408140d411600f81c07402004900b0851f0005040f014075100d01c01c80c4542900866225140503402414100011480180030402c548070450183e5902154511394404402a685 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 223916007 1250 223914757 223914797
    0xe07050603090115081c021204120c0e0a1d0105040b060d03090b030703020d0b0405240111060a05040c080a0302210c0a030908100506060901080403050c012901 70
    0x442518040c0d40e000002c140760040a40043c01078880d07440c4403c88a9075101007059075400484c1c007004840040c00e1400345111b1001c5198078030140001303074040c1014140340e001c0724070580000080f00e210501103800a20f1600d40298507225443c00d220000f0307141c0802421003c032009003030352400c113645420304010000e020400840e41000003540c441022919928040c0d801c4041d039001a240c1e60781c003000300100c150303064004040c403030403440d400e108403141d076403e100544509841c600008000d1107440105200d4146541c01c468905142ca4446107041d0001d140c10300b801540d1045406446001704024041800c401e03000402c0c0140041c0444003007038400940711080320400801e0308260508048801d00d2840a0307031548000d9005441c0c0c6d0050030700c2c000c0c0280300c80c0c1c811a451400b50041030f032203030710342803082c0c520590004e032841e407902c220344004540d111707402031007203091050601c10700302026030910a004120702c441114100c01c1c15004007042c9403010a0f9040c9040080d6034600c03200c1300d0b03002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 223917257 1250 223916007 223916009
    0x8010207020a030f140105090307020a0b130306021615020405190e0a02162102120403031b0203160e01030209180a1704150207170703030c0f061b030b0909010e07 71
    0x1c0f0302080d071003a620340741010f800c500311720040c01290709002c140a2018404001400c00e45e108696030081180c1d507151621341400362540200c154030b0348041c204003080c41c9400801d004070000c501e03100c0400965071100b604240d80005002c010764041010b100d02e04080d40d1010b10580c441281812080c50100140500714000340602c2d00b0980104415103d2441c6844194006a0158844c4410541c1d00004900c18003072441210044c820705503032519010850301101c094a0305695030b880140303806074000c042e8199182c4205e8043c402c2c0c030340c0f1484034907189266101030860507040800551443c01044607445010f402561199210040c030410b403000001c00031105a40541c800c080d02011102c103a0712401164080064a042e40c41c600700d400e640031860500b980e10400545940080094400fa9a407a5a01004000c100d103103040d9808102507411140c9003c2c4210b90200e100c1d02e40c0f4552024200e204095403000c00e84401c440d03401880c0410410394041c0c0b00e50002c11041c540344000705c0da03a42e22 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 223918507 1250 223917257 223917263
    0x317120103032a0f0308010504061d041e0812060a120f0203010f0e03040602071d0f100f0608010e070305040203030f0c0a0b040c030c0b1201060f1106010e0a0608010207020a03 77
    0x840300f0b019043c60007403000408989400c0d6218400100f1401c101030300ea003104104400042c0d0202c0081100c0c9050711540058441049803401140118a100c00f02e03140040c009503018405a0303a81c0070014104c00b0b40c071986510440301a9240c610700081c04517003150142805100300f994140911071001c590b868442c2d82d1344c111030340b03000c1c090060001ca40141400510094118100070079805600e00c000000c10880706607608841c2c0c41555440d10541d00240c4008035000003520501140c0c0c0f10540f80340c7ca54000103c004030202e02969800080b0300700006902800c04541c1c02d03401040070f105540700f50390f400f076803609050046150580c002030b280c5c49007450603492003202280001003548104414550030f58061105100c038185800d0180d0012010700c400c69503407000c09000314001c000070042e684040c403c40180222a401c00b2400c0c1c2c2c20401000701442045059248110b0074402000958000c1440c90814415410021101000d41e240c40c4c00400c2c01d0b030300400070080141c80701642c500032260 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 223919757 1250 223918507 223918517
    0x80303090d0e0f030111090f04140f0601090b0a170c0307090e0c0f03010f0312020f0309040b0d020306070e040c0e30030a03020415090e0402010f051b010501031712010303 75
    0x202e42c0b00010500710922042540540c41c0480d00345100d000b400090030b40c010100d50125128022108120558a0082020b0070383c0103103001007004080d0301d03092960005414101801105d1321003c0100b00350308000c0c41400014101400082c070140325203180c3d41c10151a51086203507141c08417011740280b80621034444c107198214000741508405400751200030b8045080c0503901c0d42e403840f0040d104405400300381c0d44110400c0000a5950000070050040c8007131074080d500b00180c00b001c04c802807070010022504401401180001a40d0900038107100303c1d210b4850709440080c00081c80121460340300702a0500450000c40c08569503608004151951405060540c9810356001060b98918181140c8040e100c0840c0703160b036080e010b4002d4000d4520018844070a41c2135048101d80d0441948195218400c968020402651082c80d0618040090f030901c0c501e4400300c0d10240568080700c0e07500e0046a5901e03030041c070030040995030500301c0940202040c0d040c8222040982950b10041c40020103100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 223920863 1106 223919757 223919777
    0x81306090302090c0c011e0207050c01050915160c0e011a03010b0a0c0501090b090705090604140601080717012d030b011703040e010609030309080303090d 68
    0x980080c403203c03190715071451916083c0e003d00c401504a54072a0102c0300d840440494190703034401d09200040c1d80e0507480c10b1560800c0c2c01102150304000c003c0041c08041d54502c0c2c41e0311040040d495203166500644010004080d00e500d500519031003601c507002946100718000c0740d049405076018040003e4a02d006800c031840240034071024084280f200302061445245c000d0482032141c400058546c125840714058031401f101e00150552201d4014825800e01502c16600302070183c909004141c0681d104080e559001480a410403400700005210148104030f4080f01c200029810310b9030356161141ca02d01104010780381000c40180d0140182d0300c1c4018041078003202d800c800b01d13124a9081007010b001100e56210400040c0c882444003085d00b1280d903450b030703000f090f1035110800000e00e03510f40036080030840d52020004d600180100854000d021801030310f08405450941282 = true := by decide +kernel

theorem cover : BRFrame.Cov 223741007 223920863 := by
  have h0 := BRFrame.cov_init 223741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 223741007 ≤ n) (h2 : n < 223920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
