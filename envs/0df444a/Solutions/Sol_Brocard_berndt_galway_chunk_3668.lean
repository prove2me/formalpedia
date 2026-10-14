-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3668
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:20:04.429666+00:00
-- url     : https://prove2.me/submissions/35b2d181-be05-42c2-83a6-d091ab6d34a0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 659532374 ≤ n < 659712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 659533624 1250 659532374 659532403
    0x10050403123f0c116004030e030c0d080310050303040b0a0f0f0905090603070315060603231906120b04030e04091110021c0f0f030e0606060906070f0c0f0b040b0d0509 73
    0x340c0803244185103211a48218008c0d42c0d0548591032190070103849405e0780f0310156100c1d43c2c1c80390100114a41e00001c5030400d110202c070401e1030366210003183c11070700f09520000c0e4600000c01e4800c0041e401a0f540e26010303140340380486440320340800c060041900341c01498010042d100c00100759071000c201a0002d542c002d036245a5550b680d540da20050113044c000c0f100002c2c01c0582d810010051800d40150a240c10035900c4425911849075210308556100d01d100d0340d41d2102c400145240c2c1a407805009a03016606034103980c941410090040441c02e046240580c0c6400c804801048580c030300e1f2143e0000480308130501552410040345016050132004c0c10301c142407215100d013190055080d1011603120340394103c0e205140f00e000d0702113a0481e040c801031500000c0018030203240c24402464000c10040074541480d00300d488849048603503000407650600280010300944902c60b120310300500030009120300e003508100c0440c2c5136014140d40300340ca1580350004640290024404071030500e869 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 659534874 1250 659533624 659533783
    0xc020111012a02030408061602070e100f0b0712180308040b04060806091e060111160504110901020c040903090510050403123f0c11 58
    0x241024031640d001042c40c1000700d16415407402201d0000c029181240c20820140c41d050303a501c0c0f40c00107008580c140b000300f14007404401154000c0000d0b8000d0142da125209482c8450400e0044440e041281d0018004081d087c040700c00010f20064480001020518114400d5040030807007600014241d0801080c44401190100d1810300c140094004c0310500c0d918881c0e0764a4600030f11002c1c40c0156803041d0034030110940038600e04c0000d01000c5d003080040c9024420640b1702c68501d402d00e104003001c142c0004010100b0489442c09004060f94101000b200034580302036800007030354442481c401103000359221401c0c01c082c540039401c403500806020301405001104050000d000e6801400110742d42d08100e98004445441303519500ca60742004031001c840903075504202185a0301600079a84802050600740c6035001b110301803014001125201c0300c00d00c000a11850b424004401c05045106030401c1480032440c000ca0050300f048044e440407001041c2c0d400c104c0d140f0300100001d075120350010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 659536124 1250 659534874 659534891
    0x30d12110d02090a0b1e0703050d02030a05060108100506070b1306020f03040c062a150227060c0c01050d0605040c09090b15091c0f050d0906090b03070c02011101 71
    0x1ea03400800e0400700460320034a0040d02e402c03800034140501c0d0b01054840c2d4440d0301d404c076051000c40040c2001c1c0d000781807070750800c001020102c1c01da0b80200c0340450050307214014020b555820409041c4c1044035204807001540c1004046650b6001d42030002e010850f0301008600741c10748482c0300f492001e400203c2036503130300c42d0100804145c1d07000b074a0440d0303000503041000030040d100b41d610454011000c210318140b00170080700720046640440c0203441d86200c400c0f0f0000300c018913100804011019140d521000100848040900550b48021034021402000b00040c100b00c0855519205402400d00c552240e20300d0346c00000030f0007240c1005800514142803030f074409410002560489411001c24030580507800e080c03101c0a4690410407804401c2808505800c0c0b5200c10780d10380c11300c54880f0b0342c001141552101c40c403082210b1030550f000d410000f550a10f080e400350b01400941200c0c100020654070b002d591603c00e2100030060803c1000d010021f5007160301c500b000e680d40b0709401d03009208958 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 659537374 1250 659536124 659536147
    0xf01050a031a030d020105160c031e030f060e071b02060d1508100b090606070b0105150927061008040201050706090818040b010309083001080604120e030d1211 70
    0x9800d43c0c411403c8c04501c0550b80302c140c032a0025001d07103607065485800d40076011140e901c00170300d0181000c2c285621303689a0181d0308030600c1040000c0c280030400d80da00d402d090902034401e1401031042d400080510807100050303244d20342280d08040314031000182200030b0180d182e07002c50190300015220f00403030000a00da400756130030620080c0012500c007a465141d490804c40d0f140308054004115504001c010405840c0160f4050b8010f88101e41c5a0701d00301000c0d000909011929182c040380c8d10070810361001c048a14000d0313a90041090302c1c02c02928a84c40c1003e401004c00400080c1081800034005007000046d4208291256101c407507103468440515074407406034818074005015901d0f01c818441c0030340c400c2c006d00e03040c281c0085940340382144600ca20318502110048a250800d0103114514420503400c01060090401c4001382c0410f041a10b0441030880888541c80d08005c0c400c8203e0700ca603a00401c0541003001103041c05002c0c581c1801c22880902440084810035403000302c5d44041c400d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 659538624 1250 659537374 659537381
    0xc053a0212060c220608041203020d020a050d110909040b04061d0c121b04090614040f1a0609010608130506010f030218090a0f03020102040e0c180f01050a031a030d0201 74
    0x4d42e441d0f0182d0f4040f070f07941003480540d644103110381000124448003103000f107900800141c1102d0007610340580ba00712404880001d03039221581840005d000001d628540645611030104014481580c0318034050900d00003c000c4000500041c04015104003c0b174200100d6910000140c0c120b5892001101c02004d071054640b0402400c1c1401f901904100000007500455040007000c040d00d410b4880c034444000b84401801c898804031802607888100324045402122020310862140d0702d0411540c94505c0c1040c8445102c0d100304a911500000740080c1d81c0d01e07841500c4c103403802c503d8017650a980340c2000301e220301350a410203812400307004004074204042032402c2c0113490003a224200f5400003008130b03100c940c0003251404899000401c42a002440c011021050b00c0d01903c005410151101c3d144515460140e41d040d088510004c0c090b901052081442d0111000480300c09010300f1008001034000d01ca042070b84001c1584d1042800518950145c114001c0307140a811149440358100d0068000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 659539874 1250 659538624 659538637
    0xa1502011e0e0d0c080d180f0602041e0602070605091305090105160504420f1d030709020d09060906020c0c0d0c0902030403090806040c053a0212060c 66
    0x603000301007014000f1405000210b0810703038001d00303451400400c00d00000041c04007000b55145002ca001051004c40d0460317505c195000d0081c10300607615071808e0450790390300b5030302420044e608503125410000c1ca074020410030100c031300c5030520b20b45d54945c000000d5501302c0b4049080107000c3c5440140868114150710403803007000c45204640301e501810700142d50501651080134910410085607031400107500706005002001c0458110390700f030540902d855410213021100c1c0008119612410b0382961180450310301e0b80c0c1b00c48a640720761141a0121341c49040c58000c40810580010360302200761030aa004202064101c02e04000d21a1585040c002a42c46104000414429403a0f000c21500c4e11a8000c07010541c8100d4028000346004150006904014001d4050213984500003481003014822180315600c50344240c0b40a1381400200440d00c5082c01c0300c0d00381000c40f0150a4500d030000c3d0561b036038048500c01c29540864091001824040e140b0424035614081d0000b400152002000688039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 659541124 1250 659539874 659539901
    0x3050711010f0606030b01050f0904020d15030501150b0a170613090b010e0105060a050a140702041a010801150c0611160f171e160b01120b0a09020a1502011e 69
    0x1e1001b0440111740340d005802d1030f070030569010407000c00780345480d40c010603c56403040030210b4954000c540c09100c04050380d105407040d9460b2004440ea000e540c18454000d46003502d00c46061007484540140300785000c001e41790200c0d8011300030804550303c480d00307004080d40080c02800118114540011560300c20320a205600001c5000400c65141000655995500560b541410000b00500071a980030040d501c8800b9040200130540c0035171103a000b03a1280703000c0d00f001c501c5840b183c28001005103d0582c8014a504218809542c0e0503904c00409120a50000d0010518a042601040e294403660b207005aa11002c0000d130300030090543c280050142c01015920801140c141d44a422132140032200b411488200b01c0f90514003100402409080607000807807000c40c00e541c1d0b10000711060a0300100e80d030314066022181085144140c090340507032a030a041c80103511903408030b00054280d0190045040d00244c616404601c01d5020030041101090411a42c020501d0008000d0601c60518030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 659542374 1250 659541124 659541131
    0x605041e0e0a170c19030804151113051801051f110313060f031e09050c0904030206090705030106150c1b060f081e1f1e08071a070303050711010f060603 67
    0x80742d503030004598117405400da00c07203100c81c1d941c91380c03641411315502e00d0884070740341c1e90b0036050519041d03100903000030700d000003402145905100400c1b11a0884810034035001007820b0061000361245d002000c0e800386403d1121154001561090b075407144004407440341d07031002107003c80000c503c4c5040e0310101e40854480305032500d07494004809890050500340c1c6000c1c00000c0c107401000c440c0d444151903074000c2068810a2a10100107010340f88140c0d02580113902030b00900003006030620000c4000c0030220001c00030989401c0d440c101e907a020701c401c3c40c14800050548018424a100102da032407800303c0322075050f0780e01e4810103020b06144481000000301144001850b00c45103241310280b004040c031200c10150b0b614800b810745291413103240d038011030358014001021251216a802000c3d228209a074040d414100c0c0540340c0034080c0d10070a03181c450302c482d0025464401048400d11509890089401d0f59a414190341ca41d83c000d5512a8540c6005401100458071f50b0006040c0c450355034003070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 659543624 1250 659542374 659542393
    0x8060303071208101206141f0b09011e2601060c060c0306051306090c02060103030507030809070e09061005120304180b12030d0605041e0e0a170c 64
    0x655074064a200204410003208444414600400f0026407080d8441d1200441305d8a0304920380342800b030140122041d40e1284000394400c10740080d202d9205184511341088803880004a40038840ba0380300b03034034524034000303864a041d902c12400b074001c5084502d0800b4512100000050031807502d1044224041c00002275400003841000200e1304035070140c1e44100d41c00d4803031780741c100003054403410302414160b58000001c2e0903141e40e049000302d200904000190170745002480f1040c0d50700713404c0d540115080540103100080d040001d4070815a0503107000845641c46010f5039180202070380100010503020404c02c401c4e080d00190f15486050040d101c809090354130814040036070880414900c25410a100600603850069a0410760140020700403903c0c00e81c11011503e200120803801c0003903000040c01c44c040a81358019100182070039038041207018814400f80148401d2440414044c0742c48600c0000918000c01007500c03216040310880c0114244d0030302e881001d40c0005880c40450060800c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 659544874 1250 659543624 659543629
    0xa0e04170a140901030f0510030c05030105010b0a050318010504231c21020304230304050108012610060f0803040b0a1808120702010327030e030c090a0c0806 69
    0x25038200c1d089588030422880b000d51000c00c016080070300700c241099914551494000158040c07a800b5852864155460340d003542003441c6003050540145000f68141001044200626000c4480c10700c0145032841e01c2c1c1d19800894a4441954040c4035004e6003801c06010a0000f089500c0142750b26038bd400c00c1802e42d180c0b4a29403104ea2480350804030202e1801549119030040d501412210f80720110740c2d103003055811902040341c0065a06541c0340c3d40b415020084c400e4885a2464598407000086091a10306000202000014001d05000908800045440402841488046c0748d0000c1c00e4070042c8244001c0200104641e10035440449030302040010481404812502a900f40c840c0b46807902c3c1c000f603815202414a2030300600384912044000400304428009990390721001c8480e269201c04600004042d6000c1d504214009403c5009002015140103281c08500358541880070314261400c00107418040350f00c04032034100c2502e5080000759070482e4018031520155440b401b003d902c0d804203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 659546124 1250 659544874 659544877
    0x602100e0c150f1318050f190b0a03050a060f051810020c0715020d08070e01050901211503050105010902090303030a1802220b03030c0d080408090a0e0417 68
    0x480ba04144801c5501d0a00c24209004140003068110781074905038a81c0c0a640030b40000d94020b02560300c1c0b075030440721090312600036660040c40b603070301668441c1800a6032190b010080008044030558a541894040d10303042e008070004c6401c00e05898607000f4500300900030b40403050a02c460a450200001d1481d0742412451840d20404030040807044440c0310410003c1d401146d03d00420f114242d00010707011490114542d83d060654040d01802c50301f104007400c4013001424041c01d110200903a0200c0340d0340001641c91140c02464915030942e007000c012140140d02a040c1341c20982803c0361400f100310005855411244100e0080002d030b030ba01ea04030700807030080032030250303042d082003000c9802110290030603502503079288040c2600c25801d07400510075002c2e040e0343d140d10116101c01c000f800c200500c103070040c00f201a03010707501d0041141c42550712240d00140703850500105002003418004520103550f002200a4107008410740c1b24020200044811501104e80c0c1100e0301d41c10000b03030401e00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 659547374 1250 659546124 659546143
    0x1806120b090c091c0606122904020603071106070c051603030504032306240f131a030102120f1f0e06030a0c2601060812030601090b040602100e 63
    0x200c5041c2400081c000b08410196a04c141050080c940820100455814403560008101c05078900c3e0384417455207000c2000c40c0d001452002c2c0121195a500071702e180140c0b409501c29411a09143c4e6956100e0741940e1548100380c0314007461080e00100301d01c05e9000400034840d9802a812a4500703980107800c41c1e0b08020318040140010401c0c401040000d480f020700320031303c1c01080c0e0f9101036032009000091400070304803486c0020700c110b0401c0700000c4040c0307a88400891000d541106000c84684040380d00089081110060a5581d02c220025040e081c200c80c0402203000b00295070301d80d8000040c506070740c0e081d1800d08440154001060f1000e01504008540c5081040792448181c07900c070f903c0c00d0071000180b50b507415001b42c0845800240e910383d1884060000742c200920410814121102c40040607800b200c407680c0b424105120b00f00700050300118801458411035036a070b5448004903640d1480342d001d04402d407000b04000ca0f0081d00400c50744c41c180b2000808003c80818080d045640e1110311 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 659548624 1250 659547374 659547391
    0xf0608210c07090b0307150306050f03030c06071d13060e010524030406060e04060e12161211030309010506131406090402040204120507050f090403080c03071806120b09 74
    0x2c0042100c402e6079085821207010003400d890115585500030700095502d10700440010756140d00c00e020710f1803d0100c100390f0803010f40007142801c0f80d8050361951100040c15003005d0190275480c090a40110188100c0e45180c09400d040e5a1000002e841028000f103019120b0200305000004c5414100404142c104030700b8203011001249040f01091000d07400604150b42d03280d02ca040118480301c1070340d8602e0046110f80740c006400c040c0360040c00e090801d0300701d0380083c0710001c02544241d000c080301d03039404070f580007034601c0946a0600030603103c0031000709080300a80004010071444400640c0a0351040c07030305480c045002c124100f500750840700a581c02501481299000c9001c80c00e113418074035881b81c03010304014602a11205400c1204498110440b05d5902c940c2040c01607042c109842071050800741d90744140341c00d2591b80035001c00382c01058041041c0001c0001403c81e44144110411404002c008072001c54441400400b4101007070003004001d82003600b15001818000802ca00c2101c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 659549874 1250 659548624 659548633
    0x30a050912031612050412030e010b061e09030a05031803060705030718050a0803070314030c09120a061409061003050303070f0509040513021504030210030f0f0608210c 74
    0x44165000c0581c0441840004105509900b10046001c03131003418042c1f40a00034915161012542c0202035440d100070b40704c4580d0408020340f80f140c803020140c0781035907a0200300d6900001104841603490181200e2180d151080b0002d440030301c5008802001c00c0a0f03408154034040e2001c81c103141e9a200192040000507008000060043d072291114242128a0842885103280c1e1940020340c11201c40d00481c840c1e8000150600030107821620b480b01d51082c4c18201415868050f8121040c4e00416109500913900e0b0200100b80501c10702c07420200c1039001008002c00a00c0070710003054030310103da4400032071180b800420120344c8550000c0c2e0441764081c1c004c1d4075658075040c1c115036003c0350076074002c2484410f001298175555940504cc0c414840c04840c05401c01c0240100001d840083c6081c0f640c0750010001400540c541c001c240313085030072505010134500c1102c0e030808000d000c10020018428030f85280450f0500003c41c252080d132135840f003021140b20a8558040c1e00e03108200e0700140c0b6500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 659551124 1250 659549874 659549881
    0x506030f2a19060f030b0108060f09100e0c031501050c070303030b0d05061501093c03140c03010b0609010c0f03031508010c0f033c020d02030a05091203 67
    0x540c0742012012220150045600b40d51a4940c6814001240c108401145410f000e01035000d5141c841c420806009180014503800c101e0301141103807032070400c02e030b028900c1d45002841800705000c48400400701d5040114440c80c8c403134003080130703600103641000c81c10740404030a8186620900541e60b000c0c03081c20103000d408d461640c1c10f03001000c100300c10581008070302007444007190013400030702c0c401d41e00c02c440e02d003110203c80c0004100c68207a40040100c000b0035140b5900d03001c030040e082080340c0300403c10f60010810701174078505612a10351004002c4d80040c0200c5080c07120200312446c43c0e260070740090061500140800c117940c0501802140002c200f03002c0340c80403607140b2000f0a156030203401e0020f40b09000506404400c8095007000105079140c408a0303400b1540003181e41001030980c80c04010800074407000114078080da0188a103071141040e1107102d020100e80d081401c400e140b0b0011565401440b140c1000381d04202c170850445c504d0300300001c1d00c0c00d4003c01c24019001e52110704d9840c554 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 659552374 1250 659551124 659551183
    0x180f05010b030c270324090304080d050c01110712020d0e153103030906030504030f0e030c060a0c06140708010605070f120c02040f0b060423030109060506030f 70
    0x3a45501070420f0030140134660b5080780c8041c07008152464503813118000a001d0842c2d606641c0b5400341541e07500f0392042000b001880404030303031042d090b280c52400d203650f0320801403150302605000125000b501e400140b0142005540110b10320180c00715001c1e1500e1048442040c5c46c2400120380c100d803c8260040319800700401040102094184c441500c116000c100742904c0015110004503191501c1004084c0241900009180300a10861805002d10f03c0c003a9001484168101031003000c2c0302d070184400c1344540e070500c400748102c0700c0540910380355088004003d102c212a04001d039606490020f03000c00c410305c0301e02c030701d031040318651900d294a91910608a03080ea128142c140e4801d0071599800d000502032541d42000801c0310360340c501c05c0e41c00600401c822510041c00184d1024602402c1031803d4860100b40c80031154200e0b030482111009003003508030240020511940342d4608122034042010f1540403601882d0250100c448a0070448152039943c41d01622106040c0c01a510801848 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 659553624 1250 659552374 659552407
    0x1e100e0c0d0219080c18060307030f1a0a0606030e0c061204030c050f0d0806030f061b0c10091703100b09060403060f090b070e010e09040606180f05010b030c 69
    0xc2c8054010910400d0040d00394600f102039812005441e0040800c00625107024a08802a40203000762404030307080c8036001a9880e401840014000c54030304070703170009000b12000c202810070110010098103290107810140141068082c00d00441c0c544444152215400581402e004402605a0785452511403001c8036141c002030080302004203000d960000180c05102e511404c00009005251100c101d030307400760907100e00503c11030182e8855402e141111000048a07504030903600e1301c3d007069034032490507116141b00e0a070b540c80d200d00c1408004401c0e007407541c0c841041940141111020103060704007081e201d00c0185c4442c290319101c3c90061104803850300040c000d110004080741c0c98540e5954501d815194020317000c0d01500d03514005c4009011070412082e5000c02180741000c0782c0c0181d400060084020455658080e5010000050030880180e1111028141c032004080e0441180903903000544601d0350000c408505040000507200301d80c05c2503a0003090021001400c1030ba0000c410f0165 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 659554874 1250 659553624 659553649
    0x807120218090c060a020706020d110c0103050421080115030221060d060501030b1017071a0408011b020d1d01050a020709020a0e040605090702060c16051e100e0c 71
    0x5a01800f00401400c4c2c0da1003005017103014080c1c018244044c07401c1c0c80a400c24448081507070520038440081505254003041c4020b6642c000d090016903a250760820081c41c0c540c45842d0400011803404500b0038030f400001c0203048483c01c201035460071128100460a9019070224079904a08a40010b0004200c0c6040b040c0e015101600303c20f42103000b074403140309aa100ba03105507400e0340c9060a02101181aaa840700500302c0000140303084881008159076400c206d100e01c0c010a90300d90041390b03140610b801103900030034000300280114450307a4442c11003070214002c103001601c01d50035007146560064807280c0c2d48a4801e8411208207007908010b45080c1e114402a00460042107408600d4204920160880c080320f40d0b42c10b000380b8803041c2444100c54040c1c10140c401d9620b00c00300280550300251041e4044c8110610301e03141d020741f55120030100b064460091280c0a454899541c040d100c3c02c1c8060910750040c01c440108400c80d00c0102101c10511401d921034101c0f08040c0351a0406902da40d60 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 659556124 1250 659554874 659554891
    0x6090108071b080307030e010e0309040f0204241d0102060c030a091505010f17061f0906090b0a05100f050a0e090117060702030a1b170d05010807120218 67
    0x301540b940042c0400c0b402c0080e412240390301c001c814840d000354544116102c410780c202c001c10283c4688900030b81d581c004d01079403070b01c03d907141c03281e00c10780301c80540643c4d0062840350011204045010041800b0341c03445131800c0001460110081c456003c9040c10f20351409040c1c019065a488000300d0580a82c001408800c04035243d4900e040081c060700c503980b00403100200009101d506058920049500507480f0b01c51064841b51000340b24103000c42c800b134100c80511300d10072140c049405151403d051b41d91101110506c1c006000443c004a60050700c011141101c4034540d20b512441000a03e4403030403128400100d1920744011414050741c01000c0b4030040307041030341c04138141800188200c3c000741c00c000740756003019201d0a076041c410401a0303000805400594200004130a0007081c0316224500c009000c4003500104040c880101d014904001c0c6e001d07202d55035079108401075005000c003803281ca2601e21940c4000103000c0c102d00a1603000c02e600902d0070040010100d20750f2140d0b00060400388 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 659557374 1250 659556124 659556137
    0x60b01170a1506170606181e15040b03060f0a080d02030c0f0606150f0405060301290a0f120e0a1a06010302040501090306180813140d020609010807 65
    0x161410000e22074401d101c081004a211072038070240c81d08080760340e80a002442907a004591000a422051552080e4190740d103517203c0b06280820602000c400c01c405401010314039107800b2404c1c51302402010024141e07114200681000799480c043d2082d845282940307001030010680314580ba60803d0070342500140f43d80c40050310342c0d0a40f800c2812460600015910029000200300d00c10b1200d08401e07045900030380b8882c42e000010a901c05d00a4850800409001032455030190750b81d801d0360301030300000e0902030300e13503071540c484c0d001041c54500e04041440f15206000000030300ba0303081710501c0c17110f1781c0d40f90042e2116140c160381004241070000d00c0d1645452411070040000c00c00321202c54080c00c2c0401c1c05402c6000042c5e044080548061304040c0100010321079a42c200c010481280c1c2d102000040326190340082190640722090024010400007070000d1301440340803c11030688403011040c3c10300c20740741c0b13007003062050121000035001001801443d08541c007668002d6800140c504108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 659558624 1250 659557374 659557397
    0xf0c180415020d060e150901050132070302010e0105070e1207361401050d1a190f1509150902070602121305060a20121605070f060b01 59
    0x120143d070000145111002e0340d9803020030004200260042e0407004c80c1500d82d45401d61200401d102c0103050046605005599403102c20001040002d040c60300c1010306c4041c40c1c1449151000340503031210206900547c00c2c04d03514200c1807c1032289a0141e5000d071038440d0394074648020f1040c810380c0165884031034010068006030040300140c0e800002c4c2080c0818402d19401ca4080d0201300c24007074101d030081850312040e208076142501065066440c100d483c21450880b52030b02c880c1000361001418842d500b400f0911844c070342004071100440d03014500601c5184004e11000742150210300c2505204c0c0810340007002740f00e51651040d41010440d40341524110f0300ca14030700d0b050743e20040044a00340c0e4002020064003004002e401e40111082401c1420903805440382541c0ba40042c2180e4405035543c14584440e101c0b01411400e48401520069126a042660b1001e10b0310300300c031400c40305480342c3c0c004030f0450300c0342d01210480d950040c0c200c0080d0799991102d4005050890100d814007241e040302e07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 659559874 1250 659558624 659558663
    0xb03010f050f010e240d0206190806042403170403050a080405130501060512070207050a030302150c0702060f0f09130516020d0c17090d0b07020f0c1804 67
    0x1914402c150110854a06502d00403041c2030700403000701940082c0750703d250328041302d10103000741c14405801151128545851400002c0c407600c0f078501e0054200b801500041111904181c1c4d091056208075020042c980320300d10801c420285402d0b040a022519600034070025044580484c0d01d40b062840c01400c003074581e65514589142c505003911126004141000a441d000040c5282c12000740c00c2403115526043d00503000c1c0c040c460f010742240d82106c0000b0314070381c400c201c101c0003840003c00c684101c950768100651070318082c440344041d101ea4040010000007101088170407560713000e803071b4525040c02c409081c08150071040044040721000c0041d0200c0b03a54402e695080340c030f8248c00010b40780c14004103006400d01c5d400900019500094504248035400072020901c26801103c0f5401e1078107100c4100c0d4503407084111007503000501c040100305022080403200d03c1103005408940300043c41515050340d5071100480f840c0d102c810035540e41994041100351075005803080713014040c500f0204a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 659561124 1250 659559874 659559881
    0x50f0907060f1103131707060903021e0f090a0c1101061d070201061a09010e011701091d010203130201021528091218060c020f010302030c160c14041401090b03010f 72
    0x82481c9003a4410100d000e11b1b803050052200620060500160380d40c41c50b4086071900500d02e40d0364100780c2d20b103104030a160300c80300d41c40c0315a004014500d40c81440d041c69058018689205924005034070740c00b000720340700d10520845098481010f4070a0b07480d00c14004400400000410150841d5203c0c80c1c0003510906802801442030b10900e00b00d84c86078a001c00051000c3e0100c446641004440b8141c403800c4040c030b10100381511313081400072911442d0f03c440c01b009001c41c080c200301290310000400807034208951484642c0d510036402e88602c03284542503010210300980d805106810b2020b41c0400784031207c11405480a20303001c000c02c0f4100c582e180c6100e4104040f2000003c1032040e103014003032244516640e4054202c2b4204010300700100e801060040d009054810706159001011a8100c08003800340c42a06508046140d64140945040c0c460310754540315500a4407860001042c944c40c0030701400b1840c0c0102600015140c0c43d10b00d0160203410361012081d099541c4030080007480703040c0e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 659562374 1250 659561124 659561129
    0x2070905070e15091e0f03150108012306010804020a1e0e06040905070918020d080405010e0409021c0c1a09030f0f06040b061f03050f0907060f110313 66
    0x1141c40b90640d00c10000c0c00103e19290750702d40d039001010082e13600e6555880080c00400b44089144000320095000890905607226880e10b905121340c1807906030300601c1c0d4140905a41a540c028444050310300c444034401503140d02d4451a000307840000074025440790501c641d02600040111661540e40c0b408219a071040c1c0740040305c08551071000344074030030000713000382c0c1c000341c09460030041c01c846500d030700d502d544450040002c2103032508002005261411588007240340c00520240b040403507850100c0c850307401489041c4c08103c10310004986403901c3d104281d999500581101011520b4602c0c4441010080380c003201c40b034032300c020013040d24000051101c000c3c003103010103107640b13901000030903161501020300701811703501164081c44858400710340c02ea0403580c820b17240d6560340c0341e1200142540d003102800800c1d942c940e0481a05880c0e264120a000d00000460240c158464a61181d1550002e0181102040450b000643e9081c401d01400d00c1c2d01442a06580c01c0075010300c005005030107940e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 659563624 1250 659562374 659562377
    0x71b090902010e010206070e1e030303071205101d060d06180614040206040608071e05040626160c08180a0e07080c0901030b150406030f0207020f100207090507 70
    0x4003840e00840d40c1246040307004403024001000313a40340c40c00000713101004280394580201c9288050101520402c0d20202d22004004c0c1035a8807441d0880d8001d00340100c10440030407842c08c210101b020044038121003015542071040b0b400498109034219010a0805025560460340c2d03036802101042d00c0d40f007803105a0120441010910100c1c0c01d01c0816941003560f50024050b00000f4080180d690804640440b041401c3ca00300d80e40c0c40345000e6900c42101c06202201d025454600c80400768132200500566403291601a030803a6014024002c01d1002d4030019040003034000820080190403089071300682051a000142c0e0400b540c03880400d4000c500303010100021081c200c1264900a24610b0103014141c42082191516171401400004094801d1075400400500000564800d81087c411b03040040c0000080031807108002045501910505000a1400000a03131001c9603008850f0620340041490b00504d10300f008114003900c0031300c240419442207280000d81515240202d901c0f03900c06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 659564874 1250 659563624 659563631
    0x60f0203090c01090e16020f070603062615060406120c051212090d030e1206150a050102060105040c0302040807030807150203040506130c081204140102060405060a02071b09 76
    0x401c048525142104480302e06000102d1000e20a0000174612103a1115081502400c482d09004050b0700b01860740501060034081c00d4404a07034190075401500c06c8804041d40b0110300e210054600d400b000f80100229034039000701c00e114988140b141156500008010310000b1074075995249840c52000e18001154a081882d10800c6246000a42c00e203014254402030540800311151400507441107000d801d100d800b00035466418184206188241c40101401c030b0f24100c030040000954030741007280d0038080003021108040380d604108004c44125101a0010710300d41c1d007044d0402000d00443c16000c03080603800c0c0310008492008000c2c00e8011401140c290f075684089080503000c80c070044010380070310f5004200348400200c002886544c481880000c01c00c0d04001440c05d0080048658860fa041d4410491815181d800b54001402111011100540071042c00001a40c43c0c03502101e02610f103401c050001421007080d0340041c9149071080750100f9081d0031601c00880b0300300a54001281d01341e513 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 659566124 1250 659564874 659564881
    0xf0e130c1407240c1e090e0a0b0306090d023012040c21140f1c020c030d090501050a0905030a03030c03050901060807090e010207020a1518060e01031107060f0203 71
    0x102c1c0b00103440381c0c0d2141682131000d408080c00160032400524942e440a09480c1240000280b0654492010f03224050046104d0304200541c1005041c2c1c0c2403003544a8000e00020422400002403c0c2101d03242700d40180c40d515206019800104105040c0d40842e0390101040e1050796081d0300003040f849420000612603030030301e4140503800c1503507900085610091040300c0840303094a03070041070841d5881400444100718020072181449088541a5000c4c1b040d440c2e015a0f01104914445203040c0e0365003203841004042d401c00d0759443c2000030705004907905080600107544a0801480c1e00355040c104100a03558a0010070725110314a6000e5000940c0c800415121540c140075690b08646100003e11080f4203002100303071154201d1181c1d600080e607403409012040c4e42901500c03203c070740080050396079641e204000d41c00c04510301070319000500581490822008140b1841d0309890050f40c403021103402000065009002d60101407000f80f205116502c0056102c0c014001c1031840c5400140c3c0700e08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 659567374 1250 659566124 659566163
    0x80a02030c0d020a08070209070c060e0705010e010302090a1a12010609060813050727090803010504110310030816050303130302120c1b0a0b0c06070f0e130c1407 71
    0x80c001e042c04000c6400c01252580400c80c240103440a044c1c0403141d010302500c0e048420703511500303407090040445e030411200300c4190b840070071440300701d40027038035488a2140c804004501320322400c0340322075000080e024280304d480c801d5103003511810403103242645052298208182c401e40242d00103400140008014130503150304c10a01500034018030201c1c00003840d81d5a51680380d2443d8007501d10f104503140846142101d0203110000b000c007903804200904030041c10078955580c0240551801103003015000401011a4401c591145141001e50f494460550351210015448a04d4443c07072150f407000b0080128009100650142000c3e03141d5034980e4400b0b10700607052240e0350101275000d440901640c1c25580000c41c2c0c0c060103454403500d4483c6183d611000070000080c40d001641034950108210b0b61600d80022203c1c05a03a1130f44598410002114048418a40da030150980008840d0700c84070440c0c20b19000644014101c2c1011100103204800403840e5401808040d151400304404121905 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 659568624 1250 659567374 659567383
    0x301140c0711060f3106020c0901061403130f0213050f1b0a03020705031e040e0916180b27090f03070f1a0c2521020703080a02030c 58
    0xd101540c0d240e0500c94502c41110720750150a404c803c04060000e00080201c24030317840c00300707040c0824030f1011450381c8644000f9070711001a00e0180c01500d080f800820001d001301e40700000348000300c8000345181e551590b0102a2481a0700459401805900880c01a600c1900c4041c407590001c20000740c1e0315108240d050343c1c00c005002c4207410301121a880040034120b04c03c4925205150a0241e9244050314000b4558818004c204c25042c84681518000c151220001c104440982a8601ca56183c140074a902c416103841054000700c116801040320019000c07819042d4140b070400080c2d403981d1040412101c90784245c80814284d94030f120360542c50502a85650000d40e00e130300621845008410040d580d200f08040070740554024108002081402a400440c2003401c1d151403019040c24191803103a43c12051045408541d00c404138440c0c16002d550310200179812000e10741c000000d01c078030300d440403800142c200c00310b006104011001c5102d201c010021780c0305580c001c40d5901104450f86050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 659569874 1250 659568624 659568653
    0x6030109090510110a11150f0708011703070611090406080d110307170f0f0a3c140f07050a060c0207031110120905010e0609010605090c03060301140c07 67
    0x14180b41c100a400d5503070018017950f015600e1810018503d0100150761454404800103043c06030040c0020400d1006011003058080c0b4100d0300c03110300e640d880b80f58100080c180071440c0e1501e40d009205040c049a820b40010440f000c889120a14000e84200490246d44507504800007540c41a04201542d41d03000c605951008640d0b8040c5040c0902682c483c0145481c911500b80345001c00f2402142c40c10001049508104455000c1c6980744170240c0d0103080e9200031444131801030101541d110001240c44015403210048051034151082245025501c02d018001100f003021810b20071020521b80610007440102e00403401001c440304036103010350558081c4500c0f00c00310f40014000300009143c80c450448843c80840380305002c1001c20390100d541c02d50004e49112000c1c01c0000103001c1c8541035202c0304c0c101e80b00d14281d50701c5650f000911426941544074a940014000d00001d091180b00b00146420290080011600001c1e40c4000100700300c068a44d8800900d001035004104420218142c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 659571124 1250 659569874 659569903
    0xa06031a0103120903052d06130309060f02031c060b04030803060a14010f0c020310050f04031416140f061816050d150e0f01021305030106080a0818060301090905 71
    0xc130604603510591504200c0700200c0b4030200e45258003449540c1b030034403d4400c0c54401d08640c503502e0888614082290a400c090b400725a200300040f800034404c03c2900f800400c6600154500030414000c0300c4004004003402c2e01440e0754441c040352600c066801000258040c144881d200d0800c14100300244009a000d100000305400d5821150707600b1250754881c0464508045c0400c00050012034102410400810b0701d15260104205d02c5404000949001d180250340d040d4481381012a801154850201090420215101d600c03000500240b1040d007101c4c80c000136a5080e02d11408160304e046419280380003141801c40c501010030320100171154420a846100c2e10303025181102142c4840c0f43e428014003124101002090022aa50001d01d96440c8481c01c943c46000b115251034004d40082103602c101c1c5100c0500014540340c140034413429982c0f150054050201c0c540d84000d1558001d640007545601941440031035030340c90b44080c1d8024180d901000c601c144e504d240079800c08050032180407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 659572374 1250 659571124 659571137
    0x8180a150e010305090a2607080307080a0f0903021e010e030339070308061f051c06080c0108040c12080a03060b0a0e060c010f1d071712030a06031a010312 68
    0x380880c14804945054001251480761441c04007001d62903d480b4021001d0910100000bd000005502c0503803030748100401001000411085402001902d1400b039000c0c1c01a030018410f03a50400c0402d0000031030310350b401c000042c510f01c071001103415500100c494070100d030143da0030080b6100c1101d0100310f006010381c40c10129401d5088504015004540c3d0260410498500040207911070800b01d40cae0b0001e01200042c0503510620001f05070b94031600c2c03922040c012800c00ca4602c0b40681c000c4209440c10000905802070244004503185c0c180140161902d901ca205d0004800f8a0340422880c1d050084000658840d040325001c0c0540e103145d807008080860070000d4918269101080c02c0c80301c036044032550381e0380b608040c540d405441201c4051b00014a8401c0b029129180c6041c20b600c0b42000100f030350300142c1e07543c402c0200c190390f600340440c0a4111b42644030710810080b0003180e0084001c02e00051841c2c907030b2074240d41201201f4800e01b0706041c95006005002449200100580f21454100d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 659573624 1250 659572374 659572393
    0x1208060316140a05120705041805060c070606030b0114030105010b04060c11121f051501020607030b0d0f050109030e030105010f0302130f0924020708180a150e01030509 74
    0x81c2900d041e40c850300e03901403050511401c00355100c0d40054000c1400034107182602007070030095034403120140700d034a124070714014049a640c001d20100d05031a6070031034040d120a69408540c030b10309510039001150015590440440000d000008141c0030300b100c0e0010500c01c0c05020309040c00c6500c1a085849a03000600c41001002d40c00b00d140d44046501428010b000454500402c42c241060740e10258240100003511040301c5042c00c0c88104545135400600180d00d0341c105009032801000c10042c0160000c2001600f07040c0250804129410040d21078000c00070315848a0f1003130030400300f0032980c41e51244c8441081c158440103418900c60304030000c21455160044a4401d07003490f2000a019100090460b00281c4940d80655058020040e05210049582ca01001020740c1d07629840101600102420301300601403003620b034095031006d00031303152101640344030307015100440e43c8030b500090710b642c04120f000d1100c403525042c003c0c0307032901d14003e44880700140c20303214002c00890941c1d1112540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 659574874 1250 659573624 659573653
    0x91b04060809063d0801020a0f09090e0601050d050f0a0f020117070e040c02010f090c0509010e041104020705031b010e070b0909162303010303030c050310090507020a0f12080603 78
    0x580d4034821002c0b01084c1c1c04240081c8a8403610425070200089520210300400c9040d041400c41120541954909540f181c41c0c4c0942011215240941400d540c804d400501082c00c01e0b064008565000300d080b542c4800071074500d5803500d8410740c812140030a8525180c821035800ca8280d9403400360b10400b4070034618190000801e0a416411030503c519211248011070034000e40c00951203050940c03043c4107000c151b0070a402d001a5510607d4003640b03900c4d000203240500d00903001e010f01d510070780c1506144c18500820010790030020341611540401c22001c400e2181e00c12401102d03031a80360000c205000c04103140d0f0700700484c86e404441c803001d08010400d11903a074801305d603901280d8142072030781036400c01201b240c0b800c2c4c9110101c0510988180d81d04008500c0ca0055412030b03100740d80908c901d10345030404444c1404295803100031200401030920182c6c0307080c0c0000703500c07400c0c40c41110382e081780c15100d205100103640e00685641c03e204d403068849560080e14030703034400030503001003d554504084 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 659576124 1250 659574874 659574931
    0x40801140105091b180a0f080f150105040902060904020d09060b150f130e04030306030c0501260a0b15030108010b060913051306050103060c0809010e0705091b0406080906 75
    0x3000121a0400103062015032401d0081c8040031001526010103281c0f0b811b0844071f1100c481c003800342a4810460809010b52000400703481701d04000c84007030b90f2a4688814400900300c0d11604a91285092141c04020f4665101801107410445d501140c0c0b0071890a1100032070314014503080c01001e0244801544a506004413640680b1009950b035440e0b02c40d032035962008143e03800c181a0074280e4400e200a060781074219000341c038090982c03410a00d039603100640311141002a90b155918505400003d00555044220340c072080c0c001d0085414103890001600c804050728103048456408401030090600c244100800310382c080d50000e14000590000801420200b224031001603141c00008070302c0d141100300310034190340c07261080c000e658403840c00070060701c0c00c13000c1580002c0e180720000c0c0c00680c05000b902e4481c5c149a001d00356103400d1100340054114001c0400c903024001000e1001c1100d034260080c40103142681e40c20b48241840f120003030a056002e000458000f034044505580300c1d19140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 659577374 1250 659576124 659576161
    0xc0e0402090d23010c020a14150f1f090f05012907080720030c0a050109090f02190203043201031802030703050d11010614150c0304080114010509 64
    0x1825038040380900782400e001c03c0a404120215400c082004010607000110740301520310400c106c1c040c4200d65000340e982c2d64800020441044402408030387d515441000540c0c00c44242801000282001031103d82c8141031540415601a968000e6100d24100c5c0e11803135016204115a001b2560031250501c0000c00c82c004036130342d001000290400c1006000400c94451075489440e800704107440800e441c80310151135110f0360003070046501169180c41c2c2200074406441d8141c590045490900c4450070090201320080001c2507820025026140e403021003180501020360300841d030b11814000400d0000704031007031420005000114160306003800580d04201d1620a103030005003242000b0b01c240159000200294050189140100c240320340414041044001c030340b625040340b04585080c40c00c07524940b140c04d1800c850b9001e6040c040c50300001c2035540804686a10b4101855454041d0940e0301030390141860340e56640ca03103105503042c204018010002202c0040f590328001d5042d000c40c01100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 659578624 1250 659577374 659577383
    0x23090103030e010c05010507080615070218060111151501180e070e06070507060e030a020d0b0405071805011e08100c050f1204050111030405070611100f0c0e0402090d 73
    0x102001d02c240d01c502d4800c01d40c05d0b0400020300181c20085006403074200150350540c020312840100504071401c450484040c9940500030101c0f4147e001c206a0390980047c0400c0d04220410000d0403018400304540000076a4071a003101041c100700c014400071088107081c4506001c0410b504220031007494803a03400b11135445043c01403c4d03541000807242e49090790707841c5500042c007003081e10034410001420003e0390043d0301da5200e1107078660105641c41c9808140203601c0601c016803540050584101650050f11072411100388031f48590b040c400061103264403a0026540c1c00c0100145181244580d450440c0100024080c60a003c02e8070744070410b15442d500c07025166120b00800c18071440854880e6015540201c0d22103a1500d0303042c07610803056506840700e42c200b601e542c11a5600d18100c0307009642c0400100103135890b0074019640041101700f001414002c40903074102c0004280110240103102a10001d81076280d80406080000681c0000740a0f910620000703055031240705510150a410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 659579874 1250 659578624 659578637
    0x307050705120c100b0306150f1f02060406050c0307050301030b151005072303090913050106030c051804051b0a080a0804031a0405060f060423012309010303 69
    0x264180545855010080c1c851200800680448140c4000c1390080d100005441c1c01e10000f4054000c0565611041c2c82c10981c084200c50171005070320380407840e98405480030703001c201c1002c84494060b43c82c110900408005d6080203082004021041c8211540021009541400c50400241c01031581c04140401041510014041106003180d422501ca2840c0b0041032407402d5884c451000b021500900c5048070700c60300ca04101c62400310302030341c84e2410001590096040c0b02d0202c0c10442d26880c068180c049440d4150107050204000780102000ba5005541c519555850107007440f168074071105401d903042140c101484000b44010070728440c4220001d40f04035410072100f00142e0502c1c526407164041c0d2045100ba20200403112002d402100c0c021403440a001042c807036020241041228020041e411000c0019500900055560f03000100580700080c000d851a0030303d401c03900d01e0300c201d00315140d406004110404100e5003848038161040c1208021201460208820500600004050150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 659581124 1250 659579874 659579887
    0x70b090418020306040c061815080712050408281d0f0a080c0f0114030106050f04090203040f0b0a020405010915050c03040b0706060e0702060a1a030a03120e01050408030705 76
    0x10201d400d80046030010103540c0d403801c06191100c400c0c4918400d080c0842c0c0706100c080f4000701a000f64000b1030b40c0f48800074200710711400f02126225001006003081c046581411a2202c1880c130856202d24840c000180da110b18015400c10f02a0031324080c079a405003000b00c140c658950060700305c0d5449200c82440c90740e4019942c001807807003401c031b03140c103402810011000800351000070780550550400d41302800c0b0a41c02400450b54901441c0d580c4a000b0010401001aa0700c40ca00901c5244081008181000d8642d8440310581c0d100391400d483c8141d07050940000c0c800803182c1143c002c0c0c448170046180070301d04000a800005e080c031a0000f0825030280341c02010340540100d441070018007041c0c1e5a1103890320405e040941140c0010b40d0355903e42a40420214000f0704090b00940703071038008241a07900d00700790602030310040580c4450300340034220a07403940e05d0401c5104000c620944035681107031202c14841007107481210345407989a052405000c0415100c00c112a080145450055074991 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 659582374 1250 659581124 659581151
    0x80c22090206211602060c07110d020d1b0f05031f020d09030f0e030105100b0703020a02030613140109240b091e0703050903030712090605010f080d02070b0904 70
    0x690303c6600703109210850010010040c071804036200c1c0410402e54030303104002c203504a0380c6450448980c40c090400b00080c0e000b00760301503400d00c001d08004008681c403405641c0861b034512502c503c115018041c454801c408515082c0000024081c2440840005843e0100296070f840c0d00e8820f80c0c10088080000c01c2700c10f1400d80403100d11500c0b5407170034020230050386801001420026228000107108000c406032901d0306000d22406a96940c81c54004a8200304204035103500c40e800440c00d611507030041c00e0040c1c4083c05007038070500c0c0d62409486202030074240304143c9142021150941d13454191080006105441170a810f45c2801c020440c0700c4001014403401800702e405e203540c4c4004603008001003201445020100b91440c00b0070341e140754940c402c00741c090360000d0715a04480e400c180005020984100004580e040303000c00e02051100d19500c0329000ca03802a080040700c400c05080c1803040c0e502c104141e190a590034030090910901e0031079800c045000704140c01307224032b403204804034550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 659583624 1250 659582374 659582377
    0xf021b0301020d050405150a140403080601120f150503070f0e100905042f010806061c0e01051005060c07060e0a0b0c061504061a03090f0303040606080c22090206 71
    0x1406100f420049418582020343d0b030760480f0a41c59010404410001d22407105901a011041c0420701500e48039441e1a902aa00248000d180c03604200c5e160800d0303400c840d01c900800e503c10300109c000082c0302a815194040c0d0a10a400480c041e0340291b0f02000344602169014040700c0060301c17043c016403210a91405003912640c4154240e5007403c0610052122080c0e65000201da000481041c030344214885a520b028070424540c0418007440000311541070000050560901d0840d001780d1181184059400300e546650023981160340d03c400708600310296080d42c4c40035100c100d50312410000449441640c0300203601984042200749408021961036829000028043c4048507a45500501e00065030f01c070000c50f8030007a54801207000e0059404c2c00e11440c010344601c00d107148031200045521038000d80c0003800c4482203100d004068007201a05101560249108040200e002d510780403a080c5001079803048140b250100401c0184a80a603541e200c3c103804a40001240c10030042c000a800c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 659584874 1250 659583624 659583637
    0x1090b09010504260118080304061a030f010b030606030105010b03070c0c030b0432030a08042102160e100312021507030629070b040c05060406050a0e010f021b030102 73
    0x500300c150f144180a45032044d07081445051500208035107000c006282005055030030000e02800d004202290124041c1d811500c03207203d11841540c0d08024620200e0300d4056804038004a0765034501a80b1290300d0180035060704600110b009100b2541040305031902c620000c0d00f00d8090000c00c010040030001c0c01007031040252740005480c00c0901e4141404560742c0003801c1905500500d40500500d07496180d1080750002c032014000310f08185075014145d0321000050000d07241c200c4200c98001025103020052403190140e503000d08a6103038000c61851640f0a5900650030b181c00380401c2103183d0303c10800540c03c0307036004841020402c0e003c0c0e20030381c1041f04034161901d1743c000100800c081a03815800ca4011180c42041c2d400d0b40aa842d206540c2c4200c041640c0d10507040200848804640c02400c280e410034052524103221507503c0b0001015a485070380710360040f41001c1500581d1582012820496203003e003480040c254070480c0003500c802c101c01d01400600300803210300440f41c80950581e2030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 659586124 1250 659584874 659584889
    0x4050c2703031810031401210c03080a0f020a030c0305030402120607020105150334080f0607120b0f04110c06010b0904060b040e040f020d0b250c0201090b09010504 72
    0xe440039240103140107101000d443c2070254010799090400e0368400e01c1030454808100c0f4500d841a400e00b8403000d0706010300420100c00e04c480c8441c03240401c580c24003d0b4011485a035103241e0f0354081410142c800310b40a40c0020940d0803005004010035003241c1c1c0751a1a60380742c03038596943c0e03a0358030004650514002c0c035030065200d081f040020503a0150300486c000c070071801e2503030401c1c08540b040650318500010f5913205140b0610301c41000445a000080c0d505a0b500705210700c039a115104079140140380102014943d12100510a006810a402c10702028081c20140f010700c1c3c5080100c2e0002171013003030b00c60060340d13aa4180307889004800e0581c0e00d48000c080c16100710b569506d9811400343c00164801d03102d2450401e00103138818031001114116090f0440e2400d256031207880710211031301403000598010103103900400004236003941c214031580054550701e0500e0b02940ca050f090303030000e4400c9024010707140c0107007001d43e80098120b01120340c0441c1141d0303a00019801250303d0f008903030140c030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 659587374 1250 659586124 659586127
    0x6210402031225023006090313090b1c050c180c0306090601020c0a0305060405070e010810150302131e020a0e040203040606121401050a09150f110c0703020f04050c270303 75
    0x1890106060b28000d00c050781c80d045031541d0310b8400489440380309e41c404114041601000421154805402102200c1c1c0005d10501c01568201da2201c88401d80c40070468154004080034002c0e0319204ac4e4400321528510840e1186103451140401944030250500c0e20501c91500050b065a1081156002150002e4060102180c0c0c2e0300c0c000e9680d82e0300f0b1301d08036264000c041010820080a00364941210003180081c1103211605156038002c044144254446114a00c1c0200140c2c0310584500380c6c000d0090000220340245407140140b110b51001c580c00c42900402504090950044c0c00b54440c3d80101c8005903651640e2a0020082c42a0361142104d50f9510b0f0700300c401d00a06050354402c035800000244803035510411a00211891490028000f4803240b843c5111403445501808071290098800241c03035952a144000d03540004045200d44c1c0c1c402d080070300441c1410407074141c844a007500c0600c154141601084a87d00070108c0055407482166181042c0c0c1d041c01a540c0000b03107025065a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 659588624 1250 659587374 659587429
    0x703030516241a040e060c1608030c0406110d0f031a040f0b090a0608070b03150a0803040f0506030f011202010c1b03201e0621040203122502 62
    0x1c0e00546042c400f045040010001000e80c0c0b07040a01079002000289005040755559044450490342c0048203044040304180000c200080c004100840c018118008019162494924010180c1d441980340345283d40010351045040b581005950070351000f2400c0c04a481a01188000000900310303049507072203403c3c0714820007900c1d4681d02c05134001c00e058440504954903041c0d220103039500c2d0b00c28000700f640108000c0000041c40005550810480300309114944503000015800c0c03c0306030050035858000040820050300b401000c0c500424059070118218500038900201892052041c684403a04103115035003161300c18858003164a60000030007031510300701c0d11040c01805c00b0380804c84803008110f18611010903d08042d039441381340101564040c0840c80801401554124031154200e602841500801c05800441c62140d200c250402242c03880c050041500d0504040781c600d410480811820322503010000c03100c540f420111032a50400748032407000c1040300e12880400b46d040d00d80058030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 659589874 1250 659588624 659588693
    0x712020c1203040b0f01060206010e0c0405030a140615060904020703050f030f06090c0c0d0e0a080d05030a06060906090b070c0f08010e0714060a0309050a06060602060a0e0703030516 80
    0x28600490080201c000c4e565143c0500c3c03030612a0038068080542c2c417a000402001e84540b50269000001c4000c01e41843e43e40c40100303107440c0380d43c00d0480c0c40002000c10f44400030400c01c541584004804940d166412540010995600c210490a03005980000d114028540100e0840d0140306070492365a541e890300c2040d002d07081000b83d8030184038104020211b070000c0d0005040d00d5000b403c02c3c024149031480064103036003030103560740c0f01900150032540005d20203070144400c40d010017143e11801c1d039078640030602d40110741c0389801060500a50138030600030b00f1b0307205902c801034030f1044000035601c82c0503003044600b01115134403081e104058040041103202041d0001e414143e401002c481c0380c503032580140104400c0c1107070310039000302c014011450514426049200e9a43c0038605507500301296846800c1920b401d500030102590001060086c1503171745215a2505c0d120450140c4101411a0340c010824441c1071000380c411048035106105014068118510070415820104c6440215928 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 659591124 1250 659589874 659589877
    0x6070c0e011403031305060d140a1a0a1a07140604060617071a0a030b0301020706020a021c0c080a050d0603030809100204030809060717070302330712020c12 69
    0x48402030b06195194103003070f0400005442400507406011108a4140400c5c44600e4021560080d138050f1070300c00500e55055600099400b0b651044808031301004106010702c0140d0b94201c041c2c2c0280205407040000c900f44051001da4080e480480765903603081820054402c1140c2003000255002e5407081c80104074640e48900b0441e8000802d030004103a1505149464020f18890348619820307501e032382440c210452005152810050500080c8040b1480c0072a089070030013041203c3d450303400520b06030007940410811564200c0566080c00d0b403a40340c07d0050004681a00c010007814005c161401c5441c0138805584160000790420880c003130b96402c0c001d160030801d980c0302c0c0c5540905860a0040c507210b00844060f81d80081c5210f1401c0c442c4014040c030f0b9400758a0035100302c3c1040810104803601000113150050181e401030800790502055466800d1070560013102d007110740c20f82100b00d0480c01301c2465004030709060100000008c04081c2c0041c1c0310300c0c803414446003c0c0c030391000343c6000e00c01e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 659592374 1250 659591124 659591129
    0x1f080a0606060305060d140f0316020918030d0c03090b09010507081807030213060314010203010306060e0f060f03121c2415031512050624010e06070c0e01 68
    0x12020300840b40c2c0c80720281d00f15541503800c141c020844079119000b10b500203111038100052070b0226002c40510900081c103540102c18902d1810b07101c07080132020b40c503004100fa0703000701503400d150158034841d6a103250f0701c0c4204081903c46989034860072540c103009900c2000d00c60b4110307a41c0d0106180a60403030303000f4007040700c1080c040b07100c0c0d80114400e180486d04a410361003d038401402e860303040d5000c0140f0380145010b4002450303140e950110016140070190543c01104c1c42c0050717240d506518241081c1d41d1035400551452840f40108034007074a07480d8103260040802e40709480d4074011a8042410110f568182921040e40003030041035040c80041c80040c010303411041044940e050708802c6091b0003c044408100500c501001d12803148001d0901200d1100e5003800250a03e005005000000e130396840b80c0450242e01d61503000748030007802920340c05440c9601c208244600e80a03d000509070350b819881c100150100161599110f4204841d4800d800200f610718a5a54296841c4212000d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 659593624 1250 659592374 659592383
    0xf0f03040c0f05010f180801180b0708040f11041d03070b0c030403051b03041a0406030c090b04260105180d0203040303051e07021807090803040f0501081f080a 70
    0x61070000380121010020380c081d0b8105030755401da8100c8001089609130003488205003134011060300010604070034445c3c440381030031300c1e05010000000743c1844122014010703e40c000b4441c101c000c1200081080c00b45542169000d0000c1a982d01c5400c003007030040c44510052100207051034040108010004054201c131482000400350a590780c003d500b9241c081a10300401181091103034a000f19078004030000b044402da07040324105541c4030000750007070030409a808a08800000c0a01c60940e240c0294803401441d402d0001d20f00d480c215000ac024820f61046007074a4044000600c0d402e40ba600201551303005020003030006040c00c01c1c40400c1080c01004100f80d5104103a5000c2484d40003009542c02c907078241e1141030030180d4215280707055806080004c8101002082030b84016940c4907030344035441c455540e070851146080e6074054031139281500200c0555205010030044048180c180c0000d44100380382c80c0328980c8459488280250500700c076804580380042003c5044000020b0780c50313190703004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 659594874 1250 659593624 659593643
    0x17070c060915022407140307030507090806061f090b030c03060916080f04021201050405070e1b0d020d0b0d0303020d1404050a0231020702031006150804080f0f0304 72
    0x416665100c0e8134000100041001d0f00300382041c2154450300e5409030301800d1007041b00b03a0709030140c25140c0c070440b1108046a40c41c01401242d90703200c041000901640303030040100303090240001d48125201709800608184511024441a1142100c031000703103104a840ca480c1d0406103c000704903001114040c0c02150403c5c00140711454825440d00c6070310f687d40712200d4640780c80804a206040080c016070b0010b00b90040c02890b26000d20a540c410303070144c0c0152200c13500700300313103400000c0001d40711418200c0e410311480346001041d41252529207044900580d139445065115000d07001c0f0000140c2c0c040310380c0342500141600740d002028480383c002804c200740158101e251000102c16940031300540d2128010f800103003800b0081c5103440c031080341040b5103040250079441040300709081100802c0e4000c2001c0701181010450180c2e5100c2e40b1009200703090410b600300ca440340001c06150200100000860b0602a03d40200c619103103220079801d80e9410040c4020300540e20542c8c08803100c0d100f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 659596124 1250 659594874 659594909
    0x6031b05040e011e03080a05031503030c10150b0c030a092718140f060a02030c03161101151403070f0b0903010e0a0f1505010501050717070c0609 64
    0x2066045406480104035030402c01d03400c0143c41c400c581300607655800391080340356010010490807005001c04d040c041d5981ca0303481c5040680e086103113034807601150083e80240b203881c0b080e20000c80d60080c0080800400104844c481d468510074100325805403400300d400007074082d20580007000800c042c4d01f00381c881400040d80c1e401c20520000d40d01d0700540c4080c0310300340c01260142c0780d0307003266441c3d00c41c43c910000d034a01d06891711100405050102d4200da801a0080c141c803500070301080c0c0d80103200000441c114608010403800d030703200060240c1a544030000002011b9405122480d48089420f402081281e07270307882c580c1404518030b0261414400e901c0c10010901c1c580007518409480c109040c00c0175031440c141a03c0205d4000700c0c1e1031a17141d52a0000d0440140080121043c050f0190440104d80080c604018900d9100d0428200e4601c0c201030040c04039036002001c0f500d8056100f603604541c2d0141d40000141401000e43c002c1c8110011200099010352181000c01920704840c52580c6c2d080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 659597374 1250 659596124 659596127
    0x2040e0c0306010e090c09090a020307020d0c0b15060d0207060204050f0d030f0302090d02130f0c0504031a1806101e050307030f060e071d0f060603060d11040606031b 73
    0x3048450750f000030785810300041681450b20090350014010702041e8180a1305000003440c4403011207804568907400f104001c050799040040c010b04451a0034201601d000701e0304c03884426480100f8160703a00f404010b022900d515200129000020040421500e90b080c03854a20040d6005225561060089401440c102c0ca8000c0d0304840c45549a26803510410b0310002c180c000e900300c0c0f078400f0f901c080d0300c20042000d611421140c64414102a00016140490082d8a000c5401e1140d8580400c84180400d2002801a22048501640c80c2c20000b600b6566a05520204078a1840c641594010f032410700c440e1204401c15441628449050314600c41d001c1c1040420201003131245561540c0a20010008107088480c2c10900030b0103000c001ca42e44400500c001d00d070550503444426401f141e2207141801c002185800c07074200103204042c0c007076402c05a000507090301019000c68401c002e40c695070003c2003c40110060f000f440039005215181e0707034250250080000d00c0340d00d0002040c005e00440c489 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 659598624 1250 659597374 659597377
    0x20411030601020d0f2601030203010f1503140313030b040201080f09030d0b030f15010906080304060e12010902040c050706050a0c05220506040e1e041104020c16080102040e0c 77
    0x7200180d008041c0f10301c85000843d000c05515403550103002000c02150040e08042c9003424440300300b4003452a065255105050856012075809180c8500d0000e010804102083e415400c81ea003241007100e0703284201c060641035114000b510303000509401400800c1143d124150340c4114000d03240c054082c0d541851000d01078600302c0d20110943c00401c52007c0c0100c00350f00104440308040c0880e5001d0258030300381c510b05101c0007100340d6042100300040004242e18010035010b0641c4001035410039103421402380406483c4005203114140340500c2d407255103000d5204030300003030b0000c00c14422444009006841948004400e589032030502c80062044a0f03540180d810030302c0e640c0d54540c6001c80f040c401c40c059020b115082180d5045180c80003400d603952030054400380403030182044440c14210f010342071a829450140c01603502007410400402e0f441e58201c005003c040d00e02580d5007039240407450404240750341041101c561020081500360056000d003099540c19544465182c13100d10030096103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 659599874 1250 659598624 659598631
    0x51f0504020f0904050c0d03050d1a031b0108060d410f06040212340602010c0e01030b06040e1618030809130605030618160f12020d1403040302041103 66
    0x40d401b8aa40380e44034104201b034007102030b010f8030b050750410307081000003415a82c804080840201c0c0903000d00304e0074903083c4aa070500c4500320301d000b0085081c140c00a050b40300010201c510401050017200203000030228810780c0c80910005601103070110015404421101501e06059070a49000e5200501d50004241c0705c003012002c01800e03155250760804c46105170008140260713014112201d69801244040c481460261f1071a62040d004a19010759000026034003c4045a0405400d014980d1b00710b9400d01c1075910a02e0045820038548012030400d204640c0025025000d0000308150b400099801da0868144c541d201c1b1403440300f84102c10515100c0d80400790a203481084100342500d000c0010311034141b6483c4012030a5a40e41c4c0c002410701c10100c801b684103210402040c80140b40a01c01e00f200c80059605901180d800d20310001d812080701c0c0039040802c0400e100c09001e40d039410441c0313034185900c0381800d00b80d40001c14440c1e4a940140c44101d00aa04142c280c1540201d010242c81c40b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 659601124 1250 659599874 659599883
    0x40302120f03160e0a0914060109031101082517010510080106050a030912021e07060f1808011107060b040c050a0320040902120109020906040b07051f0504020f0904 72
    0x21503d40c00c0380030251643c200d81d040e0500503030060401c035030389401c5050001040004000030f04c0390182100e400e080c1c600104040e0401c41141020b000144280f81e420503942d1007803070654413560f10500c51a41580070655003c00d007100034540d92072000da200300132030005103081070040c00503680c560500030001000f0040c034000c01c1c581801032160703500c2800503000e10803040ca8003007000c425903103407200301d0440301e40c0580c0160040e450494281a180751142160030301c00005198151509000401d00300c0c61007010810010900340920821080c2102c4d80c0c09080000020001502540d55050313250303000c803000710b4545080c061500d5071707482d05124180b51020380303072292894189080c6d4118001c0007621241131070200340540b0701c855421944003800c0540940349006031f4500000041d1180c00e10142e005214940c01002800002d8507030308155422290540c5c03005031074101501e80a030238800960350320310300007880b0502090504407940001d40a14002d4851a01c0b0f09008400c0c00200e06040b50080c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 659602374 1250 659601124 659601127
    0x10b0a080303060d2d050f070f3501060510030b01080402040203190f0507021006030f14070e0a061703032505090d08090a080613150f14040302120f 65
    0xa00034280480302044543c8220390032600c01d541c42d01172490300700d00c280c103480c40b001500c0c40d00c1003000f10070052441030000c3c850082000900e000750403800b20308507000384400c44a8428414680e910042d1050f40310102241c0784100340d4000440c0c441c004c107468070440d031103064042c4280c009507000c0d2143c01400780c81070352805e0040e60755400b803002941c8041c0112150040b10b141410558055105280f0003003580480440e1609000c40000d00d044031104018003458540030003000001e4130515a140c031640d1140c41e40340070f00c2c440041075081c4100ca50000081d066902e0400201010550040081e100540306021945410400003a500d0000322b511400c80c80d07500c3e03000ca8914000b01c00c0104c21818610309079113400300358408335000300e4590000b11410704003c41c0d0b400766071a0402c040400740a502008012515099040c0d944e05141078402500d07900e4028000c4099000542090140d515000c50511020b4480e900300040682c2c101d50940041c05520400826514804200e801c01900b618105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 659603624 1250 659602374 659602381
    0xe070810031a250f090f06020a0b0a020c070611010606080105012102040503031c0f14070c110a150306050f010f0509130e060403030c0201050705030a1d1b0102010b0a080303 76
    0xa450203503000d440b03103a851205070140f88400d050340241c0034040c2429540e03441981c1c0c100f10060a500c18980059148005600c42400441d5000030460546078200504e0800da40312084a40c000344200c802526480c024980041205500401c074020f442041d080200072040c0e0f1a00c04581106c000c0c0615800250baa4241480c002203035200a5000b00920b0001440c0a42e00d0300020316551100c3c40381002c581409200840c1500240700c0c0029034098990306009298076041c0000c110b6400402c50010b124510403040c05102100304101e598042c0038080c0c004841d150010103041585520449000904240010079203041090030b2140c02c46e0180c46030b80441640d0b41081d52207403c02d801081e042100c01745a01806a040d000e905146680e881c050100d6081909008054a074003590003429a0b0519060103105d80d4004c0c12290700c003040080000d2900307100990142c0d46040c45541400c0c03442600c03100c0c42b07821119001c49510400c243c00030803500659005104083c401ea1140824981061000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 659604874 1250 659603624 659603663
    0x9221103010f0303110d142b200a080403050705031c1b030e030409020706020d180b0705070201051206041b0914030a0b010b0309190503130b03040c03080c12040e07081003 75
    0xa00048144102c005143c0000501940441a01c000c1d482d500184c441102801802c03808582204103a8031727924580c41c002803000058007001000d000181000b42c002450010301c1010301c240e41c090a13401c10f007070004a0880e00703a08054001900c00c92091640030070403000d81c500134484ca0036440c0c0a00c000e141007900d040d42e841d000390446102500c1c262703020881e040e20704e00f15106059000c8104a10096401240d040034009000028080d60512070100500409030703030088103440e200a18000c41c0d03c0f05036a001c0200d400b814094145100d00c038680c0c032082e110030340c0000c204c1060354101a03070841002d5107403040542d2017924500161413680c14100620204805a00071984542c901046406402d400c47c07246417101e9014100781c075160000305288214940c500e00e19801825401c581d9411410117403501e6140d5046840024451900001d5031802c548090150360703414031488082948903507a0303495842c4d4120007100c1010000d0302440c0011415000b015070041580d411440c210b5098002071803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 659606124 1250 659604874 659604877
    0xf1006050913111224010e2214030a17160824100c030206061005090f0a26060609160e060d020408010b030106080309221103010f0303110d14 62
    0x244641007403050b090942e501c0b004004225199400c040a42610b08400c04480154541a000145401d0b1b07d031080c00441079070703203100719450034040c080121058030a05d4840121040c031910f1194901001c503018071131541203004801c0007420a41c44041f55070f80d40c14180e440302c4070740025502180c00b070b80201d00c00503041c0000c40402c1070007455140408041c0b000044420b14040603d100003041803c40c4010558140b14007600614162442c1505640300c04000e0130b0390250481450148000c540c60104030740e2000e0205004002d05d01308120603044051841c1a0741180c011a402c1e540300c0e44003c103000c3e01384201c0051281d0302002d0301140c00140484211110003007000c0340c55112000b8042281880814030040008043c25400010014094401c2c1401d47c0d04c180c2c408211030f00140000345640d181c1c50b406c40704101e480030041c00d43d08481e80081c4000c1100c55201d101015010001182840552030b410054074003a450303840310711041c922030f56500c0e810240340900181c0d450b00040c8202d1030600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 659607374 1250 659606124 659606153
    0x3071a070f02041112091501060c1b090203071112030c07170f030a09050f0601080d03020f0f040e01182016140c010e010908120a0c050f1006050913 65
    0x1c202040c2c11320a00521a01500500300c011104140e00044c0302810204015110380b903028800032015079032404502038405410050050100e000c00c0b4070300040c8001178140c907405820006004c5407a4182400000c000103a50490a01d0521418910b101100162020b0302d02c10b14014901034903110060b603860011b49140c56541804580900141220202d181c0c05144104800c04000482400030b0030100d19100d00c1c6008580c0c25008031006211412000c5556000c81c5200e003005030707070741081d0401c0c0354180c4100b550a110014010a004c01e0b0221a4200203048512a41d5210740503110201e40030106c88070030f201e280c9a1a103400c500303140c3c854180042d0220760314000800c0a40441621242c120500300082507001d6004905542c074150380165042100300d00c20729100b040c05d0304000b089130383c0740801d2414100052012510304c101520944928101c0f941c041d043d2014840004039181d69290900b01c6c00780300700d08141001c1068140005003070701c1401c0c041c4980c883c0352015110554004e002e02d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 659608624 1250 659607374 659607379
    0xe09070c140303010915090902010c0305090f0a0b07050106060207080a24090f060e010e0a02090c09060a050903010606031811240309060a18030528030203040203071a070f02 76
    0x407019030840850a10165000705002c41300802e04082c1d00040340da405109401020001d0f01d840603600150740d0154070380071445d9150402e0760307650101d817000130800490405150b50080305000c1c04079074650382070060080548200f00074400903403611820b1781c4650b1103025001c206e03800852410007091030380860805002d10225180841d02c00340d60b0701c80c1035404101c1c081d14220303800d400040422000703225600301c13800000020002c030b1305100860358a41c81e00c060040d200380e80700d00c0419120a4584100c034060304000b4801d035550b200d030700c502801d55041b07007007200d1095180000c001099400780c010f40c205c003482d031464000011856035038041100075455280f80c020110814503070780c104042c100000b000400c050720b162a031404240c010f1030018001c0409100b242003a10442e1016060b05203400801d9160a10984614a0040e01600031840c16400525800c00e03407e2017941603096401140114002d506231040151503041c1c00498002c02c2c5409101d498007007111002140b40041d84000d001d200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 659609874 1250 659608624 659608643
    0x1091a011d1b09130903020609010c05120915160305060d0f03031a030d090f05060f04030f0807150905060f04050d0c02030a151e11040b0a020c041410060e09070c 71
    0xd942c0804d00800ba0001d0740b02190703955520700000d05404005407940715000000a0009e0114588005e10178042c4055a0250a4a0002007403109606110f00c07505106401125104c500d00038440300510400c8030500000300740b9010208005080200c1b5511201b42c00030604200380009a40480092107425100040c40c00e000c00e02015503601071006818150751696078800250602e540703a0400902c0791300140c841c0703101301700381c203034082c00b00064408a940200500c4500c0b841c5040004451140610050030452941100b08032001e1070b9105960704c5010380116051561880c1d489154180c00307076406041d607480280c42c041443d2048811b560a2032015082d20400d808650302e82000203c00705640c1c0c0d14588640c3c480440c40311030b00c01001d00c014010024081000d940e18031410754411801200b04e10500020400003140c020464482c8410010340204104240700b41c00e0000968240c0e0b803100000060034000a840c5d208001400b800a002080140c040e120040240d58516001c003046032120f01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 659611124 1250 659609874 659609887
    0x20c0111010e16080d0503060a0909080708040e18030c06061e06030c0a030c02150a0207030306051801050f04020424030603080301060c030306050913150e01091a011d1b 74
    0x109006120300790354103904a1042c542070603051420030b445c040d01841000000d1003002419502e40c03410700101d500c90003001600c081039080c0601d6074454124007070f081000004001481c01c1e070031007600f40f01d24bd0010000c40c0058000303400700d4407841086200c5041d82d2064000c90440d1034030040c0c002d141c0355003160080c0d00d4207103038020a016801c201c40001040c24042502d50940b5014022040e46409520141402890710340710300281140150124000542c045a40001c040c0680e104002400c0020020031032400400e019829110017401950300591150903043d0240c01c083c02594252030140c82a0494400403401c10042c04164000354030400d626840700001040800e4015030103000c1c07139541c010464026050107000e8820342d500640c05240c0340300401c44c540d12903d10503012140d000752104101c610b0994601d010b00a28030f01c04c007287d46424004002c100002c8a120850448207a08505580e030300d81c0c1e0b0015050048030048000c2c2a00000603024010180d400d2000172103403560740b400d010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 659612374 1250 659611124 659611151
    0xc05091201061206020702030c0102060f19090204020c03130509011215090c030507080d090b090603090a02030f0a1a040308072d08010303030509070605251b1d040201020c011101 78
    0x900c000c40c113a85050340080d009040d42028000f038502e061081c002442d66040c1241d445500c0d140c000d01401e56102c049c8450380b40c01c01190410284160028429911200202d241c1d41c0ca039842405004110100c4910005450403d148850f049441e103004604403906245ca071600c0e0700a600813007100c1d003561101100c0000d10162802000756010708000e00c40c00c0c1c1092103551401c00511a420b040c00390050301000001c002100b111001d04094448540365290030b40e41c1c81c54048031010080d031500071580c9200d400d000000717a000185025030270840c464010007090259104090701d000c0e0016070303200000780d44079015003800d0040d03214056600030b560855803491b20411011105450000d00500010018181e141c0501d0303411808140140ca5101e14124002c1d0051080c10400100300c0c807a62914070507081c50045140da00c54118801c40c4500d20171038039400142d0424015a140c031a6148040710300d9034410202c440c0f040782e042e0020203d20300c0e078100541d022010300700080c3c440d640727900558a184 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 659613624 1250 659612374 659612399
    0x80c01090602210412080a12020f030109111b1b01050f04030605040804080607021f0213030210030f06080706031d03030c031305100c09080a08030126030a0c05100c0509120106 77
    0x750301517800f2541f111000c0e01d0082c030602e14405ca01d07034224014062485c03a0700c07092003145d044546a2200090a4442619510720b40c0190441c1c0c0c54540036000c1c04d541003080110750015100240c0441e11018036141e001076130603000f000c01d80100804207010a100160450740810b40040c0914000d6062654510802c2d00d0454112038240042e0401ea800e00c209000c44484c040c00707643c403001c0c25401c1c4820741080c40031007040c0b48400382c443d0b51a081c03030440036406980002c0780c80c1000f034401d00c481a21803900540e07800c214803c00c00001d150959140138000d904540c0c03020101c2c803001540ca5501c0c1d10605142680000d4111200c003c00c2001e1940000c1d410007071020507412607100801c244a109201400c1d444c03103a808103445401515028002421036403c41c0e055410b500e14080072145080e02500d6012258546600c0354800050911681a0880c00428003184144200c2d0f100013025881c980a403a10449502d011950a001c01c3e0b041d4584100c508000b5080c5c0400001c030340c1d9071003603104282e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 659614874 1250 659613624 659613659
    0x9030b07050f1611010c12030c03021303030903020f06040b30070320031605030a140f04170a05040b090409230c04020703020c1e06030c04080c010906022104 69
    0x10460b40f01407a20820844a200c024100000d08050002003c4d40d02e0303806800c907050380300b0020150780d558404040ba00907415158021144245031490325100d25010340b1001e40e0b4041603108940608004e922071400380200d07426240244d08950508025109925403000715402d145070201002c84604404045c8440d50b038072801e080e55000c104100d5070840e480041c801c02d4a01250403200308200b181c0a0030000c100c1c81c10034168982695241d95047c0700000800c1800400510700d10b05405012002e11161080c900881c0070b05140d24090000715206c0c0068441c4c03600480104400340010409444464003501d1892409032004c610404a55500300250107202c43c00d800660345441c0403151420100060030200000b42d400718907100721503c2c040d580740c501a040318821901050701d801d03c0961281a56551301000d0b01068032410541034041e1940c1040c05030000d02e1055111610303c962040010704100c1d102031300500020025085035040d5010201540c40d09040c04120005418507041d621006 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 659616124 1250 659614874 659614897
    0x80c010806090403091a0f0f180406081903030b03070905041406040203120d0f060611070f140411131211030d1e20010902120a0c0b1309050708010e09030a09030b07050f 74
    0x645103210350240c038402c0321210027140624603112051041c02e000003810821180f182d501103007407480070f00c0c045000c0c2c8074100d2102c2d014014000c00207030441030703a04100c2c0590b100e001030100e00d0000c101c0072a034802d07007254040c0d03050380216001e103612440c9000512003469001008501a08502403d50640d03126503c0b4400003050028140b0020f034061000102902c0282d8103584900c0c509005503186041031240640706030703960340c1000c144c20701c20b40c02c0b255800450650503881540e240e4100801d602442c506440d00c0c0c0d5140d0300e0703403401d16011400c101009416203a0110708549418255410448080000103000a0000c040401c804480700003071041c820500100700c420702441800401898403801c040660301c00c522410000c0d0314450f0403402d450b40100c4481e00d8007010aa0302958552641c014a0f0a40c076142c244820709502058180c10703a4808614524903445810b901030b501e1042c0c2d0b6414000490031202400010700d0b03104001c2e00882246402c606100f0701e411002d50b02d6018501025 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 659617374 1250 659616124 659616127
    0x9030a050732040c05090306013f0f060f06120c1403030a3014092d0705120a0b070f09060804051204080c010806090403091a0f0f 57
    0x8610080002084580811401410a600004500004480b1242181c10f204640300c0d09001210b0b4400c1080d142030b000c00404660865030f40720811030000400c03400190313901c000d4002020f0300c05012000000c4241051407405520990b580710480345074407259084403110380742d0a2065404c4500d00400c8082e1031042c84074040102e09150140603806035500c16041021070741200070844d900841510340c0301c80780e03041c0480c030404503c3e01c80b02030000020150a0510b03030031100c202204016401480d0940c0304441d0a0400e488021025598203850320022009040110448084180700a502d00340002c40d0340440ba040d0703407601c000408041030481a20b030294131504011040c050400181d179040815807c0071414002035482c010541c0d00d540c025902803000d8007020070100032040000080380c80034031041c0b6031500d440301203554031113051003565400584000045021807802c0c000c0030340999455201c4105076441d065000e2400303010346114921030744c81403154103840100318006110003044807040c1d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 659618624 1250 659617374 659617379
    0x706030b0301060617090f030a0e2806050f0705010908031f03150c0e0a0b0d24050d0312051e0f040308041b03020415081e03190509030a0507 62
    0x508994a004240d4800c0c2e062107004c0240341c0e040303090309002a400c42001091696401607461405000c407401c440240310006150045030703800b011221480c4411511011107142004120210829a41c03101400500009040011500800003405c0f50f039072410149080040c56203801d4211401c0040c1a6840d840c00402c0000e0307845140031600b40c0c10700000450080701c2c1561121300381400103905410009545000c41d4406074010348180070020303001070004d04200c0e101c0c5010445500410550042107080c006c0300081e20100649503208250721800301c0c1f1100f4a40b400300410181d00c10320035818003100d2031005000001038002c0a1145c201501032022a550020425103200f0f80202104e00050b00c140500000a0340a01304540154001004059101c03800004008207251799100035407051408040424445204500380110b413001e01c1030b079a54000d420041c041004e05804542c0240e00308001080300c4940c40e12401002c41c080340391450070880c45001007845c01000f50001ea0f2142e100344000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 659619874 1250 659618624 659618627
    0x6030605180c03060f0301051009050a0b0f0d081e030906010608010608040b06010e0a090e0105060303070812090a0c17010b030d0c06111e1905040b161a01080706 71
    0x4920081405480c0300c101810005440c40e440c92024000e03100e07441000000c02c5050b5954412030350003000041c000c22a074205114051413a8030280319942240782007100290032509139100d60411070b0806081a0800207900781041002c070403510303044500d40018000c01c0c10601c3c000d400e8102010380c0b905a60369900b4000d076070a1070800141c1c0010200141180140041c2d5405505a900144c1c8480e10307600581724440107031594910600040c1e00a1030061001800e69a0744e00101c01107005c01c002003140b40c40c1c1400745900c03403040f1403014050328020842450890102c246813030780000c0001c01c1c1c820860340c690311080701200e10f5101c0c9002e030386a2006601c68600178400e50580328001c500410018611010140041e010390b44040e0141da5520782c0102003a01c16011a8420316241954440b0034100c080a44600d402020030302c0e41134191120024070450144040f2421358050b00d0056003020b110062800d5004c00c001c808660f12400d00800807081c40031064040d0180c91410301805409080010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 659621124 1250 659619874 659619881
    0xe09010b040b0d17040e0106090f09050114010302031008010516120e0d12020c013908060f031e0106030c06080c07060f090203010c02010209011704021f1403091506040c0909020c12070c0603 83
    0x12f40c82c220703d4100100200769042c0144040e0303a4085c02c0140e2255078505001b60102000e51040c0301e154200350420551a000c80004101d01d00991600e01e040c0c0c200b0082a0111040d003d55207070b4a40c0300381e07400100360b800b84c1142110303404050f03405482c2001d45059182902c1018260b940e58400b02c5880d0354202d0340d415078070241c0c90614103d0440c04081008020f01040d005031205010f185051480030b840d0328280180c1c06c02c140500f41c81c001d080c4c02c56000c94020901403009a61030700c8501c0001ca0b03aa07215400450180d4011820707a42800c40588409004140344240301e0036607680c80d056000182c41c01e00030b882404880f900016100c500c14800945401904c2c80900e040b0301c910301c100401a41d0700f075001d9030700a504070f0740040001c0d40b0000581e11041034112901030400702204005040c1000100c0545074425031821480035202c600600c4140c5242c208508013058a1000c05e000c0d2115a0380602540d20a60048030580001c00101121a62050000f62605120941d00b48a110340501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 659622374 1250 659621124 659621129
    0x1d1501051909090f30051309060b030a0c0518090604330f060909020901050f040f03050c1203070b040809150d051e040305090a0f0e09010b040b0d17040e0106090f 71
    0x944052110100c28001c2174079011643e60301480340204e502c10800a171080504003800035500b04008481d100c8000c480903030000c0300c030143e00a04140c50341c2c08151262096400ca007286850300c00c1c030343c60060204181000c006100719003184c0c5e01d101c00d64003524521180c9411682ca081b0440c0d11030a00031914036038410715000300d240c1c80394808080015036400301c5590304444404000503101d0b51040012681441141001f41c2c28040c007080104001c1d80c100385070b070704882c4144101e8800700008400c0c410008000c55907441a904180072001c085145150400e03803191044607150700c0c0403906000078410381407680c030315142c542020034400140c408520449030044492540d03480180e041030070030380020314000d01c000d04215000c01c1c81c0846480d00003c900282001da02c01c106920740312905040d5090040b62592102c0d0300300145c13444141004e1040380660200600246403423609529040c1518640f00010717180414108000943c45030a540780d54060982541d80001251924810348428034194 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 659623624 1250 659622374 659622413
    0x20105090706020316050102040f0f08010b030118120c05030307052502311a012d0e06090a12031412070809160303031d1501051909090f 60
    0x140c07082c4070468001041d60502c2d0154004001a041d03281b85c0300c3d001e40559401004140200400401d02d056544030300016925144000c112179000d4400301800c4c4c0344400c2502552080080a00380460007400820744c0c460b441d130820055006032a621303580766920485820000500c00300d400da8150300e00d0a0489030006041c0100388050340142c001900143d80800d00809050034942045111007101c84078103c8141c030f05c070041010750305114418138040203c0030418001010041154100c1010b040b030181c0051215100000e12400104160b5111055894003030740403806200c4240d1580e10140700c3c0020f0042c48507003590940580c60054200f160502c0181c0d0410001e002c45801c1403804004180d10500520302401c0c1703501e80c0381100e81040c0e03400203462007a4095480100505030580c00900300c0455030001016401c802100540c0c0302c2807003c400342102c0c419003004004c02c0c1b4080b05d50103400700c40203951b42da40741d03501c4007440c040b107440c150120340c4503160602c500d040c01080c2900c0700556509 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 659624874 1250 659623624 659623633
    0xb030304051507240f0b030303041101050f0403060e0304030311030c1b06070f1109060a060801030609210815011b0b07020f15010305011a360703020a02010509 70
    0x82400040078040c400403041c0040c2c6011408400b4406050100d5410720300c0c200a0320a218450360304400540b00d045904903a20341081e22907281d40c02c1c00422248541c3e0056a1540710300440c000450700c075440001d101000755414032002c80401d240717116540075a900c0b00010340d521842c0d45005000001c0c000741d03000305d541042c0304103400080b000c50f044903000f80f10203110b04c0c03002c00c90001170b04038020300300090043c0209403092030401420890a00c10354404640c51041507582e00108024501240280400034610100402c0040d040741c000b0a403040c400c010741820404519280c2450780c100d081701c0340002e428041801803c841c0f200d10030807400828601401c0b0a00781c00d01e8800c912620b25001840e201041e40000e4a40303100b8050f1084403400201610f03205240100b6240c0101c1083c00162610351078100552050b40340c40c074038142200c0001e00708900c888602d10302800701c82441500c18541d500e0564903408c0b9525240c04262080c09181c8005132580945d0100030b08480c0c1c000d00c12880c9501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 659626124 1250 659624874 659624879
    0x50103020a09030f02011b030e041103090a11060d09030c0323040b1e0a02010e100c200f030a030207060f09050c060d14070801060f0207150c0f0c09020d0b030304 71
    0x3840407442080c1c1350000420381044a103407004841501d09402c4240c804c07400920800c1c100350b800480c103421094100c40a101c41132041c144a046c0307220031740342c0754000e5000002840003c0e02c40a807100140b07038002c18090074030158442e240c040d40e030b0086d003ca000400c0e14020004043e00061070300360314070101c0e00416009001107400e05040c450381c01001120140400c40c10139560b044d0103c4102c20340100135007038a403969120081d0180030380143c080c10500890807141509129440340c0714400401c0c1c0e4178511582001ea042070034103401e00d54052030700d00925680c40d003444410002401d8440041c0e030016500c405a0406008030f0f1452800b0604050030a11650085040011000c4806004480340ba680384104c9084200605100c2c244211051070f0008000d40365400c02c2c4214120340207030325924001b20707580c030089031122070710300813900c5034005010b030036151500c01c000240460307100700d049000300b4041d500c9528002001c0d070310156103541c00294881c1495645c0c01070320810501940194106070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 659627374 1250 659626124 659626127
    0x80a12060807141c200405090a0b06060f03091c0e0f1e130501031406010320041409010b150408060c03090c090a0c030b1e091f0b070507050103020a 65
    0x2c05902c68001409003034201c051440da900c15124040800150b0041c6620b0b240d45841c006aa444282840c0004004845040f8a043c80d015913407040c034007200a0111141e1a54981e5440d0f1000750901da08003005014109000c0c00b00001580200d80400c024180d07008402d003043d00000000c00076500b080824107042419444030085c0e0840240b00701c0304020440d0000c0707800d110342e90591044a9003e01070100c1444d0888255000c0b5050b68066550500905540015555105020700c07008080c0c80003050071404d0b4440b40705c881a1065030041003c2555280502c0c80c502118090742c0284503079660354004641c1d407501444440d41c030400c0d010b0050909107480c40c4c0b191074001c000c040c010103000000019540345014403461140c64401809044282000420a030046c0b401417001c00c0468075001d4003160034500040041624141400d813120030441401c01d202030440042c10f02086081d5409104219221506918020b005e004200c01e032100d440c1d05105140c12429404a81031520401c0440e50303c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 659628624 1250 659627374 659627383
    0x2090319031d19031a0609010302060d02030a11030a1b110709110910050a090b03010b0307051b1c08010f150507050c040606110d030c0206150f060304080a120608 71
    0x40d03000810120200b0100c0011682080b20841c14011803805040c022081041c5001c40c02ca240c0d45201c0388596a95030f05003441001002030001070740c000c07414065817280c9850394000710703400101c100020818448005030446942c0090f5011107110b6101c1c1500381c50401c040c1210450030310146001400c01c00074034200c6481d0341c0315000f00004546c40e400c11542c401c1e4a82e0865090740c0018003840b030070b10460341c401005600a001000000744020500080e03008204064038161040c2c1103a441c0355854600342030f01d456004d580400f1525190f408102082c604c00d000d100f0300c0241121410b84000c22400b0003c002c244160000104092100c0c41031000c0c1d26002c0d84640c200c545400c01c81d13960101030524034a002c0080580350361241c00d115000c10b0040c2e0050030647c1c0c03c03e0000031500040020641a419910307410740c03110040c2e1054002421110601b881e0511551010344441003114200c00490703041d50040301e054958410000b001a03e443d44402c80040c852400031040000d2414400d031f0503100c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 659629874 1250 659628624 659628647
    0x219180c0e040b030307050d051306031b0e130504030e030c0607051b031c050a12020a08070806060409051602060702070b0901080a020f03150301110f030109021b0f010209031903 78
    0x4503900e10603818641c13800c00c1206d00c0729801c501103546255415074010160791281161020441d0710442c000340d00d074040d0203600c0302242d640c4001950050203200841d2110380c91110107610083d01012012010000d204460240380a5610a225410040b09051914461603482d038000e000400142001c5480032685039214105541c002d080400b165002900c0c281c010105610205501000040900d130054020900310950742c580241c0484040c4400080f03000301034070130010032151000594202d100e00b03103407984268010319907820035448950340001c48108464040b43d01200361108000f01d901003290039803060940c401004418101102c80c005c034012480f0042c140311100010403110301031901918008040317040c90649901d0400301c91030b513010703007546114069440c05aa0503403a48000048420102d20402c0302842c503440d0140400003540100c103081e60700c240c80310100707034400d0040c040100d941500c0d00001d40c40b070b00f9510405040c250701c4519101a10f03040201440001d8200620512 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 659631124 1250 659629874 659629879
    0x11010c0f0b09031b0a03170f190e0a0804141009062d0f140306011b0203010612030521070c0602030a1418121e0304050a0219180c0e 58
    0x354942c038141900d18055501d00c000d03400c1c5541c0e140714440360000343e00c08403203000340e0b5001c801c007840381000800840305603000344428440100103542c01d10160402c6003d0003d001001565109010265007048501041194041d0b00010b0401110801712880200356104075404d5103014180359000e03000301458030401062042c81070440700c00700c602e6400c3ca80700224299203200404070b00034000304881e14031000d410100d000345801c881212103910a50b845000103850702201c1202000341810003140e100741c1243e1540d294140407402c000180405000c440c42500c1e01612800350b01162212807030006404103150034180d00b0042c006600641c912000d50b040b80c40180e60b5118800d00d10081c0c46c282459a000f500e1000501c1058200302c05e4030f1102180d806c5c180c6102240304034a020303051082d0084080700c514030840c1541154900d200468005103c1c104480210604d0b6011608264140341d07003100c40348030310104000000c41141c0080184002e01000c014140010304090f000c042207410603030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 659632374 1250 659631124 659631143
    0x302090a060e01140102010f0c09170f0d020604020a0608040302060103060908070b180106060c110423010b04050f01081306050a06120f030e0102030c0715051b060411010c0f 76
    0x240080d0345948544050010504407250b55a119000d240350364030410140c80c0150319186001517807010341d2080040c00c1c01e480d41e8500d0164500608560400904808110180144a04642000403c115059000c819500900034910f810b00400c11040b03c40d41c040c0003404102400c00000a0740801d140741525800580010403400c1401d100341140101c0100a000220203403d02c0080c418048031000c825440741c2c003c0c020340e500e8000848082e50301202c010801075140400350428509a0031401c942010343c0000c0084608a80c2d00368006502030f4050b180b071250018041c02542002c5115070342c1c0d002e0a081481042c00d022041007451190201c1c0a403020780d84101280c0c40d10007a0308801d000b406803003078007804105a4246086d02d443c00300c608401151460907103810550000c001d513000d074030002000e450824904134540383c40d10105281981000020001c2c030000703110110070b0708100c15590700205210318080c60420240c0d9641da500ca418000002940c8000072140c01c4085041c41c0e10031803e1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 659633624 1250 659632374 659632381
    0x1503050411060706051005030102070213090516060810150206070e0604050d06020c0d0c030c060f15080a050f0111040501050f0d2d051005240d02040e0c13030209 71
    0x7141030500c50480d51000b0002011000e01c0300035040107008400b2098a00003d6a40780c007050308034403554078025008003600b10221078104966014514041c001c00039654450302e44000030203069034541110001c01c40c1d200c14802107010170055040980300022101045400380707000603503550340003054502001807100403081e040c0c44e00c905030340040c40c0181032903292201c1d51620401a40240c1050901c91068401a001c050720820410081603003640310b5880740c1141d134031518003030001c0380b60304000d003070300e03400b80d007980c0800090818000d1100c0b5010307246900991400c24188000d0010b07a00c81030b81424548000601070200316000c89500b42405030f9138240e03405584119002e2030303e0b10302c100c0e4a082201c1034038085011403600d4840d403066145010540302d804050403500281c469001140500c20140321504007840305844003000c40c0340345845091001000f213040c0d80100d000d00c06494000c1810070041c00c04801c1c680c1c1121a142082e401e1084000351000c41000f5440064450107005012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 659634874 1250 659633624 659633633
    0x901050f04110a1d090c1c11070602030603010e07050f120c150702091b0f0702181005030d020c062b0f02120705160b071710030c0f15030504 62
    0x2d00c0180d034a6040450315a03c1c4298080d010020504d0308181c158807120301e0044a240085109125143d03511609052070220243c00c04178010034121040c009613984060740700c0030b80c19400f070a4002c0c0f2500740982c0c0d80c60300350141030039200d5001103160303203600001080c03146640350300e2110b99a0006541c0d209002130000c036030038500400603c0702c5401490a1480e2410040f803400202070403802925441019201c084203c13011401003194820541002d0146281800b181c00003811a07a0004000556a5030f48403020b00c4080307800e55119480c0701c55560104403a003803c1c8013401da0081c050024000103207510340850842e100380b0041030346040c01c0e5010080d0351a04c02403007800c03540040e40200440320112007180029403140181c1080b8948400020b03d0302031007941114800380c3c0c0d4040081c2e02c1d41051780e5200060038040c0580342440705070040094005041100703288215482c00c40c0144462841c2000108901d071a04034060688403a0414005000507502602c0300811a180024013940c80d03040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 659636124 1250 659634874 659634881
    0x20601031e0212100507090602060a1802030d0e030d020309031b0114030a140f04080d050c0915040312050f1204030c0b01270e100506060f0424030204050901050f04 72
    0x7009500414004941d800c550740002c50840071070740d0f0f0004128070703100d55a0684103007041d403181000503071101002a03100d240c941c2140c074040020116201250080e0382c00a410103422441c1d020006080454171403203403a08100e04542140640042c501e841ca6410119460707038554041012084a0301c0105041c59120f46501c0540054008825407241000c2100304d010f04a241c4034814081d080b8404101a40200c0c9940d034040d941c00840c0a140c07441d001080d2000e000001d0510b0240e500034455402d1580390109100d14000324a010580da0340e0941c07900c00c0d45402c01044480400009001c900409811001200c441440347e03002c450480d6190b240c00c88d103031004184020040003a440001071503c10850042c90030600100d0301d0f0b603181c6040a10070003143e1441c4410f600c1a4013110012041e1600b5070320141e000302025041c0b514020f1078404620752a8480d5204d4030110542181c0c13400c0c2651000500340412034246019881d00f8503000028004039010700805109502c1031540ca0681e980d0343c3d2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 659637374 1250 659636124 659636183
    0x50708030c0303040b06030c09010e07110f07030201090b0901050318030d1e051b0f13030215030f130c06032403060b0109060c0b15181005011b0302060103 68
    0xc580e501d507241c4044a45039081500c0854061541c9400305d801c6207008501220600b00141559540c1e0f0b18111501c1c0d66590090071380d01c04d100c42c03420100f0000c142030001c01d5440c1c0d040d130014051179140d880010088511548640107210052107020362582c0e01004070780d00000e9101c20300034900b042c1c0c040c841c158841e21212b445e20030f2910b140011070f040c00000721503a10403032030300c10401d0b03544c0c0749810500001c1c0000140c51005007040103028000b88030000c3c1c0307450f202c0c107070411034881e0720b03030380030480d1112110704211039102c000c0104100d2003140000594044071030300300f0303102984450b9140b1020310540d000d40400d058860640d403021510484020140050500514001c80d60320b0030414000c1002401e0300e40080e00320312000c91054002e04c1c0c500400c503401200704101340e4801825407000c05251502c164031081d6140003008600151900070300820200b045919410318046c009001c0c50000c044890300001030040b9940429004150b00b411250417107801340c2e40c20002c1164403000c0320002c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 659638624 1250 659637374 659637389
    0x70302030409151406030603061914340c060f090602070f03030501140904021203040f0f0807050406080a1203021c0f0c051e13031e06110307050d090507 67
    0x743c950028407040380404403c4454161840420041050900c00709210480b80d99415601c203101040310414000726240c0122000a000200103001007600340c200d44094800c0003100c920318144001040000e00c1c0e01c8080401c8019101d9054084c4101400c54002800c000d40340c01d65400c03244078409203d40290215550041085603181518503282441002e254015800a8984400401e0b00b030100c51500311080c4004000989550b103d0f802c114102403035100300c1e070540c0024803002528180900b6604081c080c0001001070032030030485554941805c07548100e01c5141041400c000352540410300203401900901800002c800d01d600550280c440e08642c00410001c0d004c00d06401a001d5100840c1c070344d02c1031030501c01c1303041441040742c1d24003425040408100100a005030f05103450801060310b541c1901c41d813410355907642c48002d80c584800500448429500c010742e07042003c188200402a58140c0741241141068080204a80540b00c0c1d0b14181c03d503039000b0701b014020108800d000a1222 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 659639874 1250 659638624 659638631
    0xb131509020c011508150906060a270c02060405010b0a030213050601140c0d090b040305030406050304060b0607061a0a03031e0306030b070e182a070c0f0f0e06060906070302030409 79
    0x10b40d80e815985038070401601b11003075080300210b0161500440ca440c00341a00501c200c40d0790f400d00292000400481c6c0c0386201402d034034021403042d81c0140c054001c002000b0313000b030030f001e2074603040060a6a80c480b0003584901ca101505100681c1d8005001c0d0112298800010315562107000695115900741c1c204e450150021981c81007800c1d0000c0c924415003007a6130303245001076851161061a014a0200503c0c6805c14041440414854009150f100c2d020700004180c0c1850000030034160b502c4240305031409921003400301200340e441425802c1904090f0f40750000c051031510018034444000e402a0309842d10703800301d2414103109802500155400c202c6003141400e100b000506400d045e081b510f4058001c0c59000000021004601441030701c0d60407000900881c4030060301c107071085003040c1e28248070b018810383e00032550a80860014000c40ea09840e150350070b00e1034444211101d54840c0411003030344001c100c50b41c5c84600c250742c42400c0940309541c86031000e04c0c09a086005a4100c1d518541c41d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 659641124 1250 659639874 659639879
    0x607121107090203010f0e1009050601022404060c0c050c04051e010905060307150c03030b2d1912020d051f06031104020304020609121204090b131509020c0115 70
    0x942c0e50066040794220601d0152140e510740e10500c0703504003200d000080c100c1c684800c10410415400c91944480c0510540f400140440b402d4489029a1017485480013190b404120030444140b1403201205680e0404a8545190b50348031356603100781c0090280115207a1000c40d14500040442095001456520140968441d451140282011903406109215200c0b000490604840c28000001e001d50350703a01c100348154800380c0240030f50b0304080f07801815980506016036240c104040d04039021504c081e50801d241401c10490030f2070610031003003d10f410903082021040d4600d051038265030540f003000c00c14516040150400100c50609500039141032521140d502c442e5001b941901e01c2200e494490034410350512089000c02c81c2d0080d000203007007204212516120084000702d8a9400840300881403105818800d90002d5210110441c0c64035541c1c504c900c2c0107840d4135100d07410010100000806030451400280d010300c65054103960029041034440400e400c0300f40c0d01d9150055401c000765 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 659642374 1250 659641124 659641139
    0x50303040506060a0e0a02090102070909120f050f07060e0c36070e090a06181505040209100f0c06061202090f06060a0e010203040806010e1008010207020607121107 72
    0x2442100c0489903030003550005942441e22031080e1042e1404020403050b143c1d601442140298040c44070903055221b180e0000402c100307070f8002c15039824841d003500054000000e10150969800e10f208406024040c0305c202c24400701d0030280c03003140342c121070007150001600e58454184981c4010302070300244c2c04540c0500ca060404914142045a0501113185e21050145d400c22210281c504c4000103c503103240d0351081c5803021406410150302440000c0305555000070003070910940c04418030722500c801005424041003450f41e0014070080e01c055282031005400180d041d0414441c4c68103020440c21061240c5101d81d09100c080c03640441c0401881e03444048080000c1083c4904038405c0c405000001c0000748407411090040002501181c20048000000e40f4080d810070603a90461100380800190752004100c114000c001d40c4082c00241d0400040d80c2c0d8819009411403a40c83e801008150016146c6d0000c9850b516000801f0100c41151602e0456003803403882000d0059201c0c0071008074103603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 659643624 1250 659642374 659642377
    0x5090a050403110a0f030f021e0616020f06010302010c03050c0d0203030a0f1a130906050f0105150304110603040f080c010e1e0a12050f133f17070503 66
    0x154080e0700c40038101800101019a2504c0d07801c1c004081c030100199040c0024000d105409072503015005079011006a0200d07110202084204210a84d105400b40500800c02039040e2400400e030340f018001145002000c1951444103220003410000840401c10505101e00155542d1000001c15102603001c0b041009641750820b4403402e040b01e1800400d04e0441895100d512140c00704e014502e00108080c500b00035401d020407809615090311900400001109882907502c5910882c25001f15541408180075280b9041190000040801c0081c000401c2d00452610140e4501b01e52582e0390303036103d2070041c1540c0c0803000010400c420104914600c03c1c4107411103100440080129940d00020000441d16100e01050428503600300b039070100081804000080504001404d000d49403c0a4900c600b0141e44501114034442d08040c3c03082c021003c042450307100134540011080d180070780c1500c0d8400d00e1000c4118180f04580c0c1d45110b9000c000a81c090003000c844402c00c0161110441d06001c1c1d280d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 659644874 1250 659643624 659643631
    0xf09010216030c0e0a0e0619021303140d020102130e0910020a0c0209160e060c01090506040c0321080106031e02040906030c0b030705030f040c030b0103200906031209040605090a05 79
    0xa0042d620010b25080d14522072221ba8103203c40003054a82c0f251003041c00e06003241051003421940805c0b0145050348000d0b042e00045100c0d02e004030b1004411001c50f42071880c07044401003164010072034915220b04c152110300943d104105100314a4540c090050301d4003440c1e01040520900100307001d0342507030f0003600e4443d48600a9804405070369401240b03c080c0541014004042000319555100c1400c007900984511810070000151030303245620740d40d1400108441c100c0d05204403000500820207561600000f15144401c940004004108050600c5005000351001c1607603641003210640f040020321800041581000c641d0b170f0352102508005044507020a450171440e1303c0340055510b07410411280b00f400302e540e4060950321158000d658400303024100f80d0303195810130008000716040800780360013540715800082001d20392200c01c41000300410100c40c400e0200e00c1c01c2020940700030a940010340c520580d80b50f520003030f0100140040c14079401c5190002454002c0000c6040168440d600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 659646124 1250 659644874 659644889
    0x1090c080f0a021309110307030c0602100c02060c091306090f0b06070f0f02060705010f1a041e0c05040b0705010e071a09090601030b0d0f061a01050f09010216030c 72
    0x40d1065509030716601c84019030300070340150030200348004510241d48162440e42c45003030b04010040084000130318125903a00191140e0b0300241c1c08004094040103a11414080c2c11014060051604000781d141c1c4002008803015100006900000341d50301186030401c802445800c11440361544403550040011200303000b0755070710340902000e15150000c1621a05680000c1000c40320405640f252070781002000304a0b080002401001c000510038010f5141140e00c482d00041c85644410050304860a0708402900803032900c0b45003002083c00400c00070b00d0203643c0b900447c0b0050315401c100c03854032903644150300914010406001700300040d0455141400381d07808441e4a1a100c80d0b207450800e20401110105480030044c1c0c01403807c0003d80658808014100000c011a01d5404900b801a10980440319200e081c0d940908015140c812010455066000001c1c00c606d1030001a05520851600d61001c00003c1510051030303208012064200d6040b00101402039528038021350780701d101d40079010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 659647374 1250 659646124 659646133
    0x2010b030f011a15120402130f1b090e150303160f11060901050702040b01050408012a0306080a14070e040f1a01230a0308041707090216030804030306030b0c0a030f020708191101090c08 81
    0x500740d521442f100c3c0c0644c0c00703402d020103d41d02d5117206180f04842407007030039030180024001442e130340503068081007805000e0448104034004030300d000300403500b0149e0024410710090150f0b00899900c0425101103690580300020f0403405200141c1e814002c5901c0307505190b080800c840703d507410944002446602000c004a00d41200603002c0e4143e840754007685200e0341c00880c03181c020940e105450702d0120000300a640c142030b100c03d80c843c0200c42c100c8055404501c50141901080800c1758070074031010b019030710b0a80c254100b2048c081e000d050f4a00300000e0000c0ca101b490314590318a01200c00450f80a85001d40e103640d11707046400c1c4a214501c0f0030a06e4000c181000550005a0003119051a4030340c01c0302c40e02c0c5010755025120740342c010300283c003056034991000c0000391150012500070420103840ca6221040b504008068a851040301400c1c10700600000c000641908150b490310b04900741d89840340002c0320000c0303c00400ea2410502258208850b00c800d1107030481c0700d4015107c81e8401e85 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 659648624 1250 659647374 659647421
    0xa0b0d0f050609040803071e110c15030705090303040e01060f020d210519050a0b040c0c020d02062107030c2d030c02010b030f011a15120402130f 64
    0x803046071011a0076030f0304a07000c9000180015a40e90080d5841a00b070704200398003607044010071107408810701078040400c280d0030940c03040745803c10800a10280854900a0400e43c41d800e9800b1800017030300300005c4c0320f804201603038607a4050040c1c0d805031400c070f90078200b55a9038100040c469541a0101c2e0054000c09189400952041c9000040c81e920081e000b20310900140c40340008100041c03408205c0e60038200900300b41200c5016103030041a044c1008244c841c00b071001c01003201d90080c2c00c0818040100348802c01a1039001c1021141c580440e16151100f1820600d050149000f0040885000c035940c20031011b41e0b00750b03010380c05038101a81c4038031604549090700d80f8240880070741d107505d42c0c82004190039040d100390410513070141c90744000b050741005180480e103000e0121a0065041e51140d81d600c0d02c034800301101d405100d80440301c60100c1e580340f01c0f00102c141314601164005119a90001d4155100c100384002e091202c1c00040201441c074420110041402c8080d2010000314000c81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 659649874 1250 659648624 659648651
    0x109080d0b09060604140d1109070906020f0f071511070f080105010f0302030a02040c200102040e070503060114090402040b12091209010e120c040509160618050d020406050a0b0d 78
    0x140c17815556a4044017241491410400c800c1031f10b0400116403190021404100d1a250a011640189100d88518100780c2c00c104001e03040c505403450b007103070310f0707111407c1c6407900f540020f101c0c400c5030101c00741580c282e01d00c0c00301202d02c4496002d180d80385e440f03860b000003030406580040c0070456800c2c40080100340d89500c204000a4017502c00070354158000e80601c0090b1a003a400216a50b030a0305280e01b114003001c403144503800c15485410b1030359602207410001001206250b6070f100e082c3c0d160192541c030700400080d10043d80c205c5165880c1c507011030040c1c40c5444a60485002c0c0101b07080e03240e140c0d040181c1280a4030001c444d403030398500070041c40940b1000484181e80d4942c1c0145c4610743ca45402c2c1c800d0080c0111080c0208031540314003140032025880d10311400c0c3c0074034800805040d40c452035050400b00c180c00380e8015010020255040c030a0080c80784400c2081c3c50003201c410608a08600001e0090800c1d27800895001003032500014200050307100038136188150170010321980809640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 659651124 1250 659649874 659649877
    0x601030c050102240907090e0a0302010b090402330310090e1f27110307081212070c060f020d11070507060c08070501060e180105040302070b09030109080d0b090606 72
    0x2130300183d40c031022854102e02554007006500c0141c2c0e034101c5607075940d00d2803030505882086001d4a03690304407001c580c040c07607828002c07210360240a45004443d0304083e070114074400b003480004030a10391a80300030304010300303d810003d40459100c03070050340380c1c20281c0d4110106491485801e4215103841b964460908021a26050b460903003445600300c5280e000340f10b8081c060592441c1e45111040c0030903204160060101030515009031085030341c0c15030031001c0c141703080c070a50072000c1d041d48600c7c1c074000c0140d03122007100c84401603080642040c0d181c00038103460254003050003c100c0d5092450b04584040c450f40031348101c1c5a028011301949000f150f000500f03200d104c9010300301740c02903036084c0f20303080c001c4054040c810b21500d051844e00e00c45484103400c542c00e5400c00c00c8120194001c0c080000f0740d01c41030300c0880e114a40204424101658080d555500604c11120010808254060140c0d429801011045e801a03440c541d030703a08200011000384070342c420046c8916001d40c0400d40d142001e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 659652374 1250 659651124 659651143
    0x1e060f021c02061915052206030f050c01080121060e0607080f06040e0a021509060f0403020307050913030e12070e0105040c09050108041104020d020c01020918150f210601030c050102 80
    0x30003d01080c207100134000c44140b900741c147d000050340210088460414814100154000c1800082802443c034006041c00c490412030b5042050010050041c044600400100c0040f03105d2321074444045803512001a0500c0054540c050007804200000c0d150864051441000704d500450503d550381c40030070041300d88001c040c44155021280c02801410591106020701e10902e18060070003e003403000641c258080810340c080c480000c6070400441c1400c01107000546011100b102c914038084d12005c04660455501a04100003901c00310103544582c3c0e100c101c0c201440c025104500c1c0c85030640661400c1c04c3c49614025480c1503010351559208800010550701c05945840d0983c1301d98956505622000d44155841542005074900045640c80101140603000b8005602e5040c202c0410404200c007652601b9045000010003402421801102d1b0040c074040b14001048540780000c603034015803500c1c44002c9294800c0307904000420002c0c51070b049900c114502035031032392148012a15021400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 659653624 1250 659652374 659652401
    0x60a06030c0f231b01050f01270e1903090b0c0601060503070e060427060b03190b46060c051c12061e060f021c020619 52
    0x788200309480344030b05403500200f14609212040074048016100c0e4410001403031001e004a42d030802011081c0102c9a0041d0390b86080a441d6240442c0480d94000b0501d0710018180d400c00c0308081c02a16a001d0405a0040710071103042c00e48400222079640c6410350141c000c00c20360712001501d200b4550072180c02e106448042c01e0340e40d01e071010a0740d140e00050a04000e1000c621840c4030240c40d100c1c082c0008003025009405004035425901030805110b031081c0e0382c00b034100502881aa803008003140d41000038a04d64a091700d90b4410890010600ca1103031aa018410040180d00201c0c15180c80c2c0b1102c1c03d240e400e9442c4404031140924410825400b45041d0304a40d03020404103000c0c0801e03040b95406203055401ca0000c1503459026001c14100890200f449003113141014001c0b8490b807400b40210300000100418040e00001146600d803044034208070350480540e5003d442409024000c10520106e1070800361100c40294031000200c60100c140c0603200c21054496285008019405070712 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 659654874 1250 659653624 659653637
    0x50901032c21180d1502030403030b010c0309050108060102070909080d1407020c0415091506120902030304090222080a02012a0b070203130612060608190509010b041103060a06030c 79
    0x5802c012031203d0f940c400c082e0701c250400c100602042000c940d025034200c001100594915203890090308171a10400c0050403ca000790a900000760007030350300c1e801c0c0e030401d09000f01d041d80e88400413850128503410002d440c83c01e00010b4400c200c1800301400240407084400e0024180d020240700c442c0c002101c48500580c000300303944105003041e50144000c111401d03411420746481c1c90012083e10240100c4514480c0c03000c1c000c1210076403120012083c492100c1040c4580c00c1c4030727000640e80f4002e0b030007080d09a95000a9500e4400070701d540d001d65048403844110a9540d55102082e15500591010390100701c0c04d154400d100302c4a2a0303042c60203042541040308003030301e03605c0310704d4418001450281544000c00205c2c1c85500c001855100500f02a547d050340905050b03108070644205600ca03400b4024144144a036180700b0040132000c4101c54000003a482c0c0c0d0741c1c0c1415014052030881650400e25020381d002d15070b1840c2c00210300c640030640384058455130340c078000c60442d613048541c0e0001445 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 659656124 1250 659654874 659654887
    0xd05030a09081e030a060509060d060e03131701050f0610030c0201110c0a231908040b0307050a030e0d050412020301060f0b030f18070501050901032c21 67
    0x116588028036480c003400d0141d08048207040f400e0040362401000c480d90440120800c1100246800781c280074000a039a01c089505007600072444075400c409005000d99100e0a601c103180c4804c005a821030000b07403c4250301c0b9956003880034254602d0480c00007265003000c00041082076a16584c0b8014070018004c11840d0324001011402025240d20035070031552070f204041120030403c406030850030500c00142214481ca450001040621960381540c03014a0041440b02241c0200700b402c0341b070701c106200d807041c038080d4501198244259000041032101c04422b01c05903641c000080e0034014090f46003089400c6281c000d282e030701c15041c2e2901002440400007400710b00d400d9800e01c104244003400114a0a0300c0390740c220305254094210720607100c0e02108200303090f1541000a60445036a43c0500400c0d1007001c041d6446140c10f000d541d0501000040f81412640b280e405024a583d40310070b09800c1c0e40703164141045031505c20098501c207114141c000c200e861030300860302d1011060b00d00e2243c81d062 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 659657374 1250 659656124 659656141
    0x91002040b07030c0203100501030507300b061c060c030f02070f17090303120610050403030905060a050d14100906050919090c030803070816230405040c0504080f0d0503 74
    0x50032a0201c0c1c05004070347c4c241900034010700800d40a140b01360701510780c04c0e00b415030b9135400d01800310f02040e0390032444a4070310308103000000500311903404c280e119080b07a807000081401000c030f07085403140d44001180900b0601c22a030b0310a0016801554081c0075002d160203080040c1c1c0184040034040100900c11200080c0355036407442070050050b0401400d02c424000080c2c2150020070080c0001031a2100300304803450011540c1d000c0c100181480741c00c1c00d0468400804100301802054007500c400100601c42c94043c505680f0304250000e0180009142d10200c491224800c1d00c100f40808410703000070a00c054075000b14401e865010380b2001141c0d90300442d841c0641480341151028560307803640c04020800b40018800610301a0360202e50701c0c1011321004060100c0105000c811601c2103811009450b800725407840c1c035452085884842d05a007002103001032003507074032a40e802450007903001840c83e0480041d008070303803642c8269030810241140c0c04e80c44000396881000001c104100180410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 659658624 1250 659657374 659657387
    0x50426062404020f0915030c07030c030c12020a111002101e0e0d0e03070609090239063d090504081b07030302060a2012091002040b0703 60
    0x140920040740305507040c10114080760b1140d00c0c0b5a03880d030703400152801d45081000340013403d402216201450b5161000881100b40240d0340f0082c10400000c500400b40362041c90f1210420790015400300141c010100069a40c10f8031240c11203c1250035407200c0e40381c0c43c1044007500d852407545c003d842c69403284a8404003e001d1180101440d0701c1004800024040c184074016802004800512880d4600c0c6d801414440a141d1154400e0f0301c4400c0c24000198041c840000b118080c4002586030740500803c0b542540a01c03c52019407500c445030f602c03884080c6d00003488000482000d480d5141c43e000c0b000400a854130900c0030860320f958103c01e24803120301c0f0b00d5100071204188060700050300d50b0080c4041e030320306680c15240c58a011412a20030411881e41c09003a13003a41e001801c146256a8000c0d4550b440149840845541c07170801074211a10107160079058041c1e40c00715542d442c0d624403201503800094070303205c00320302c928441c10400c1c1d03c00c0e00c03c42c2d0a40707964450366824200c140e42c0031070301c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 659659874 1250 659658624 659658661
    0x50f060d080c060106031508010204050a03060b040f110a0f0908120c070b0307030b040e0f0a110616060f051303021218060d0b01020c0a060c0212031905042606 70
    0x1004810494642c503600180720080c040c1605640124000c009044103420900036a086450742c0c0c0d1040008105036130303c15402804980c1d1004001ca0001780450004e030003464886156440d481c107041c00100d005007100002c150001c0b994507507150050020b0b41c00c46104244e80603131041640944035008101010a0150405420982c21034451544445000d84150815541c10010030f4071085461600e20b424050306c04a0010680108881c0403144101a0388200c4043c000d06003c7c41c80340d46a10030b40325002102d034924105940c0c2c2110780b2040c9040e0008002a5800300351240c40c0401064058008514580080750141d00410303040800004201c020b5105030140305442c9182d500315a103603191a0003030140d20000600014000780d514001a08040d24405801d01c6a660b4640600007260040e80d09103155805540300c204e240b400181c0a07107948542214100c080b4000e100c0c5080c0158002c0050042d00d5544150f207078401d8011212032018180c40341c0c92121508880c1c0003c840819060640c142c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 659661124 1250 659659874 659659883
    0x50705061e040806090d03140a0c181d0a02070c060810030609030503040515060d17120103210c080d02030907030b011811040803070f05150a0204090c0201050f060d 72
    0x40302201c40d205030754164000d03402201c2d41d402c5801009a00c00c001d1040341d410309070701e0809000309021600750019070709000346040c02c02e0780c1d21007030014941c0c0304014031600d0024284688aa064844824661040c2030031150b040c1c01e4866000500d000e4014001d45030015404000c010116081820075100410000c2005c3c0101c05251400004100e0900403600b140e4065180ca80da20b04050415034140080000030300c2780d8086900612030b003a1141100a8862904521034840c2d28411804480052180706404191880300100200602100c4d032407a41e6807102c1c40100d4145d0050005068403054070711000034008800078048810103480640043da4090284000d80e000d59031030759103c01c002602070f005540000c0070700c6040300b0ba00305d9600c28591508040c0f24554285461304c40d82c40d9a03489180002400c11485680050420400f0041019164a0058080e00038940008041f000b0740061140040035400c02000d000351034018400c050194070b03500c900200030707901c01d828041060390140080b84d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 659662374 1250 659661124 659661157
    0x408070b1b061e071814041b0806031b0604031103010e010c0807030e010e1c020f010507030f0c0c02090103080c03040e0c030f160f0e1f03090309090905070506 70
    0x440c00340050040b6031041d44015802e0160645100303425407042002028202032003500503902034443c0b084843c20007213603517220b980b5030310006400214000d00f032008220300081ca41d15540030701440e0020481c1d40b1030403054040f142000303040c0c2c88074054540e00844058001d2400c1006001041c401c40d00c6041400002e40046108854026000d0844521144140015850105108106a060183c00c2c1a003040340b001384401d108003041c1b20349400b40c0080c655071404014a951611500a001d090b40701c915100c000c11140c98a03c002034040d00118216505492515040c092001d0040c10714000d4950041c0c0441da03142e095030781e40f0071035502c18103845145110522000030512121400c0e50300c102d0060102a889040807007100058441c0031b04400d0452181c141c00382c80700c583c04800c1d510081818504030544100030f001041200320617100210022241e4080c00c10704070f030140c06c2209014807075640c0740b00c500c1d920341c1c2050032180c801c0c01c02030098000010400103490001c003e09103003803042c40c040c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 659663624 1250 659662374 659662417
    0x3180103050c07080d0501050a150e06090102070509090a1203050702030a110c06160b0703050103121211270411070605040804050604031b060203070b06040c09030215090a08030408070b 81
    0xc54281c5c01c244da0900540da101c8005100074182024110000c00e0701d020517142c000e451200192000318a04012070040b10b007c1090700c05a03200300807040040001404405031820080382c84ae85923241c414003a1041041d4181440c00d0f03078864031400b48116081d5000c0c605185250004586a40300c0321103d80043c8030740000d0301c1050380d03448004e0041d9281d031507050000c1c50b0f071403611006541000340722070241440c00d401000030840203008240680f025152030722136104031505c840018401c20741d0684040601003210300f0b4030b40c0c1c00108105140030701000b00174802035520412003902d1f00c0c400c00c4601c0f140284a0900065a0b45e04002d4100b48500070f950304003500d943c00704485800c2580f05407909082007401401c008007480a15000d0170451005c0c40c034101407a110f083c59000b0140845014170303900d0540083c82c0d0320a0030b20740091079000300750700b48821060124440316000f031040c080c401c03035007100d001400e000000210303022103210001509010346403065270041c6030000d0901c1c0900311100c2d03009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 659664874 1250 659663624 659663633
    0x1e020c0907050d33300f0519060f2c100e0c090a0501030f02061b1b01020c0108132a060201020406090b13230303070b06030d0203180103050c07 63
    0x2480c00307010454000d03034040e43c00f00313107a0808004150300070314a266040c541c041c2e51071301d842c0940300680080803883c01030502620307242c043e81800759406043d500692840b007160340034a0a94005c500d01a034018030003200109071800440d00c079640211003182c0c940750b08404407c40480801c0c00e0004050039607800e851944410b10686106202a0760141c0040b007000c03e140c0340811882e43c000a81c201c00b009150305541c0c0321420711030140c00c042e01c07410000c550100c0020b41c0080126140e9441030035109414901440c3e1400f4170903002d4031502501400941c09440c0d48900c98091160385a19685010044e03143c07500e4441c2c081d0144c80203074590107080d921310740c00500d03c55034004101c59070006071b84a1511000502c800c1c1c10381c110708080f1108010009103060f0341040c240a592480c1016903820121503141060301081124003909400045800400d001100c41d055224160030340c161411900c428004036228810603001c800c00d501115034800c215440f90340117035488644030100d640740c442c0d5501c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 659666124 1250 659664874 659664911
    0x709060b03010f1502101505060a0815010509010e0f04180b0403030f06050d030305090c0a080105010f05030102070302030a0e060405040e06190c050f070c03020405071e020c0907050d 80
    0x2212145620001c0104038503202c42c034110004010003100d184050341e0502000303440e002d504c21040070b00c81d201c1c00d80348403e4560b822004000c14006081035078403500781c1406012a603040358840392485c0f843d44101c0c10313540120215400030038140c1d2a112020003c0d020040400c503400800ca4009a403500c040ca24020100c908450050080d0f810300c0d02890300d441c0c020152500e41402034041814080c040060f51240e04540001c103515040115060b03a407e01a1441c0960340307004e890b0310508406001641040650210f8143d5102c0d0240380d5005440710b0030300d0700740e00c600e04008006074020018001079920440d041024004011f02d014030380781c3e842d00080c054600d81b120040b6150019014040d80c2c0d60707661032406001d404c00e102030110b02400c110180c0a4015491300c0c445c003040000d890350801c06046440000f45a0061040040e81018000101013202e250701302401c461001c85101c1d042400000d09010108008001c0a0365644943c2d00b1502030b00950700040c5515151805003072203503125034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 659667374 1250 659666124 659666129
    0x9380f03010e0a180308130521040504060503122a0102030727030506070f020a170403030f0e060702040f022a070f0b0a0305070c080304110f0f090a0509070906 70
    0x404842e03207042003400802104d01281c0320214002c03210104900181d04080120f80c031522907142050718a45030700703100c0d09182081d0902ca0603072000c0c072000200004150054000e0700e01c15101003024540726400d02d5910384142c035180e11040c0c403c2c0000441c075000402d001c241c4480d203207500840903104c000c456003660015114407000c50b0915520f030119088200c044000403419403600d451891640c2c840b00c0d20313a00040c002408000d040410740401031300800c0340c120415030000518010395440038801100390401c0c0021000180052825802648618520224450000c010700e1400000303508200080854400400069800b40f0001003141d680403401c0c5101d004c030008040f42d00080248103418140d01d9003010720742440b03102c0309000540e801019a01c1510b0281000189511002d1040c0c07a10b501c0311300005e24080d0004204020000342e14200345040f40c05403000c8014140741070802202c80d55443c0141d81040882000445178007081d00550382141c100f40585044a80305c1b20b00c1c50a4031300c00e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 659668624 1250 659667374 659667389
    0xd02031911040c020102120a151802040f06020d090e060427060b1c0b040f02061801030516172706090c090108070b070303021c0b0109380f0301 63
    0x6240181070341800e001d01e40b0b510700e440c4001c500d4a1103081110100d4817002e0502184507a0701d1000b41c81c5408170b6104400030702003c06039402401c003400c0c0042d019510034040d80c410f0301074142000945900000c0e0208110701c1c1921902606401e00d002540c0c4200b0082c9005e5100b40c8590b182c03030340e450225100780300c4c000c1c60111000711440e6900784082583c05c5001d4440c010040700000c0b1400018030307010304004551061036040141c0726401c0400c1b1005c2ca100d0003030340c8900700060074140024441e070310341102d041c20b807002d201903582c100303e2100c110300c40b02403100031601008039080084004428190b00c5100541c552160300809450044000c0003101c40321750560145050100101041007040c264400840340382c480766040c0094107840d052684640c414060001c1000c00c01c0600075019101c00c0303c60a40e0056418040000c00d070301034100c1020f06408280c0d080000301d581d441030314111a68401803d400300001d0b01e0b8000c0300b01a104071a060660b64181880078451898101c40254001c1010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 659669874 1250 659668624 659668643
    0x602070c17010c080105060319051021170304030c031817150f060f150f030403080105090f04080412080d0f02070c081605010327120f0306050f0d020319 67
    0x43c600b000e407100303006070042c92040360240104483c1c005000c000748044815148046034035140d04c00407031300802490300881014101c81c00b00c01d02e100307800c42010000b14066020300a90111400050181e84019600940001c0b605052031010138080d40f00100480031181d10980074a070780d1400402e070361440b5840c0e0f4101d5006031504485890301c400c0b240d5001003c00c01e16400a0500b00c0000b044d9001d00004079000740c658403080c603900e21000307007552201d0503030641190b0f070b034901890000e01030f100900603a442020604040740d603a0303c000c00d4242c0f140780e000c1c0c000c0d0b00d020f04200d2505000000c90f0780031111740f00c00300030707a444110050261902c0307105030713010140e2039044c0c62500e0401d40b1141d0700440c000d42e20244984003150751480601e0b04454003030030000303101155200c0441115002040d0300b200100c452101000b0008402c2807001007174803564403860000f5001c202201510301610070306a1250b40b100c01240285441c0080180c440e01c010b044480d8001d44651000e02d40400c00b06c242c41d0b207002c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 659671124 1250 659669874 659669891
    0x31b020f0a09200c100e12070b0f070c0b040318080f0d0e10080103111201020c0a110a083307050711041103191107050a0203070e010e01030602070c1701 67
    0x440c8503c1e01c150544a44641c14030406034000d40e51a80203042c0000b40d0384c0c481d182810500703000c0c4043c003076a03001c540e00c4503a12001030401901900c819500180480004800a203540d40300d00085031880e80d00c40711001840e201d50b14100c134800b41d20321140c0060208208005044002040344003201d141c410040d0402c1c808042000e050030f88481c000e00d014800c52120b582805030b1002900381521703400760800381100c0c4c044001c0b580c01a900001c10065603c0041c4540c02d03504c000075001d240d24407500e4409100030307281c000d204151310144104400c590203103448041c1001d03091140386030500305582c0800c2c0744200a4034488030f02c030140c4101010540c0050f8400c140181c01e00804d6802a00755824032695041e5054201e181c4802086d004107a440c03640100a801019000062803480202c0d41544079107440c10000d80318496004128828800d08600042038011081a141214000b5603e0310a40e0300e16110a0041d62011108582d2507c004c1d0f00441c0b112907160b6160040d50071003000089108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 659672374 1250 659671124 659671151
    0xa0f020f10022503060c030e060a06080a230d0f08090d05030105041a030609010204051905030601230a0e01090507031a0f0d0204020708130b0304031b020f0a09 70
    0x444030500c18050358400c03242009407a00003c0c51003e0b0030412241e80b52203440c1009030300c1d484030190001000e4601740248410180c4c1d05800c2407a20091110070303502c01e5110b0340e03800c0048485920604070503420042071040801d004048010780003880f0080f11400104001001d030420030340c13100041c040b40d140100f00a50030741c030104055004420000a1480b103089600141c018001485050304c907940720900c9241200203c20352142640000d02114128100506558043d4000b4003440f07000d01c5801000145904d41c0891074401c403140a8083c00c901c0c2d0a104000864858042407a80c8844003100c140150743c80d080701440c01010100103000e00b550502008070103880c00a05403104050803c800807002d03000c81c18414008150482d405c40300c0346c4808001c80c0c21613080c250040d500034800301c0d4010501105070300820034610b000d0019001e0b0b60303c0340c240c800c0501043d00c1c0a0002409806400000702546840511460009065002100461000580f840401d400622092b612400b03140e1301d40d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 659673624 1250 659672374 659672389
    0x112030f020c01230702030d030506120a020603130813030c0302120d1d18090607020d171b0c06090f01050a0908090d11131b03050408030f0601110a0f02 67
    0x8045510203810910380341400280b9224502c0312440b902d910b0f40350b030b80d0700f40420001110305c1c50340e025095038003000560300003400800d82102c00750301542c20680711882d201d0000c507000155a900409060035901d80d40407450340c1c2c0403030010807201c10130304000c01411860b42041c500001d61041441c0340c000c40c04c3d44180920a40c64068290301c07580406481980d56421014650100c10104445021781010600107070341104030032407035103c0042e61000e1080040e030128040380714000301e030200d40e014048034008072081150726401c02c81c408000000300d0f0186402c0881c07004111202c100807400d181c440c045036030400d0400c1d40ca0340d490f030740301e204103032910502070180c90b51104a0314001c100c0c4002e103485d404054450000d0180c460005c42400d001005400c220a003c501d4000d001c0c80540144203030880f0062984001801d0042040c250850302c0d40c0c8240100da1041e503002d4822800e50319a1842d08011000181c8403034140b00940e044240c40010070800c0200040c00350002e441c3e4542a40140940c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 659674874 1250 659673624 659673647
    0x30603010e1005040204150b273609030d020a02070308270603090307060513050f0a0611090105090409020a1a0d0b100507020d0c08160602060a0b10030e0102070b011203 74
    0x12181500d00410100c40f401041d0780c895040d0b0744004c01098140307031740c102c927003102d407520180c0c02500c82450301c1501d51a000b0440980102442e0100e000b642d05010804040c4200c48140040d8010404103080780103940181118040500441d00301940343c3d9103110660300705401c4820541a225007803241781301c07030305144da51104e0103803109461410041300c855102e101d4800b01502d956140d0b03020030302c95408401d01d989055002016100507201c07404415407140290340041e561b041c140b07403102c991650084115a52400140c5501d881c00ea51441440003070b1104080c140d912011169001804d290062a904654007200708002e41c1c03401452159412030346e42040f094014690409110040c40d045000c446d8450340480b03011002c00d17100e28101100841c5500100b6039409450301c802c1d40409400340c1403090b244203400361906562003005880496620f0b14940750700005100d250486075000b5400760302c04150090015281101070f0b01c40340c0034080c084e80044020304440c1008024140d004000080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 659676124 1250 659674874 659674901
    0x6060f08060414161803030503010510080106020d080a091a01060f0201090b27010f09020126040210050405090903070209071b12050918090607090614030603010e1005040204 76
    0x2180c0192500c1540343c1e802000c0f8851a0b000020402010b0301460a02c214002100076039200d840e182d160040054200b1700c240b07401b803001c102e4090845400b6550103410784141e5030003044c1e8a014100200c841c0c0b02d001d0241210aa5214102004901d512a03200e101817038590340380c2040d5240c0080107001b800815014011a45088203010001e0b035201c42160700915500c0b80151440310b02e09099031200c0c00d001103e800da61030107022121040641c0c000600c028000d032103120681d0f4071781d00342030783c0141100c06680c90034669034000340c010700d0003580e00302d200c080f1460468209503d400100b1811001902e240c0300740d83c0f0101c1ca250031803401d001348581c000c0080c9444040c4840090700f40500b4030780444000c1c0a5540c2d800445a0703d4070450a550300701e0001000c0303402d00c40409002100307086041d2141c020307600070741000942d8240581c401d18100c48107560b404410344415149183c550b0409081c03654955214401c1030f40f954401c1060000050318200d00284c24102441000f040340d015590781c0c02c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 659677374 1250 659676124 659676131
    0xc03060a1512060b06071a1e070309060b030a1505090f07030303020c0102071524050310020c0c0a061106070801051e1306080703020108010816050d0c05030106060f080604 75
    0x11000d071418031102120000b8072040c1c106141c1d0301d00200601320050050f074000201086002c1480b540e003d01e406c01080d0480c40c1c04054542002082e14a100e94058404d4071000380041060103200c0c0c0d2250120a005002c0001d24148500020f824040c5081c8180d88101403035031300c1c0c480e0700d94600c945ca0700400070400414000c1202142c04c1c1c1c60701c00501c4013505040d40400c441c11894400e40403a04d40360790028190300d210821406003c02012018500014611104000c41d46108448019020740e440140148101100602e0fa40060b60003800d00340810301800422448075243d2858280107030081e911840f0040c03414655a0b89450780003031401d0f0410080c0c100402c0325465989440d01e11950035400c04502500c000d0104a044610030400086123191480000b4a030700086a0031050364804d03615480070b81d81c2d40411507500c022201c10211813402e204010040351a00f24505582c02d44603503c11001242e41703000290864580794030120104a00c3c1c40f6020042d030340101803590002c0200d6041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 659678624 1250 659677374 659677391
    0x2103250308060111071d0403030c080c03150f060315031908120723090f0109380f1b060405060106050c0106080102040b120c04030f060c0c12020c03060a 67
    0x40c556007010384420305002c00d9402518071907005101d04000781c6214131420358600720780500001352903011282600007a01d801c841c0c042c268840c40099000f4444103101c035085884011003035520440c43c00c1030300e80c4890300c2c450710405030312074001075131052090911040401d403117401454100403402100007140440d16207888001200c80c41580c0007992600103190032035403000426280c2507040001700c1210006520084000000c03000100491001500c2c4141d2548408006542089160080407034001385220301140f147c12001c0e40900c0c0c0c0584642100100d06a07546002007a03110700124000c0590000c5c8402c0745544109031615001c1c8010300a000b1450700d030311103d84824060207290200400003130300e6400002e003500031a0250071128004c554441e5600d48517111a40300b004c000081d1840d03c0c00040c000c0c940c0009407011603030803601e10360840200b40d540384018040c04004809000140a07540701003600006104203101040c0c0003840380102c2242050f290440040c082d003031450809603074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 659679874 1250 659678624 659678627
    0x302012607050d0b030a05060412020111031b120703020304260d0506150a0207080609030a0903170d020d050f01050f0a03020405150d0b011406090a031121032503 71
    0x440768480c05900d44035480344100e082820181030035809032a410320400c0a4881800340c04101e550149204110802c1d55034003d0800f60309031400c040c0030a800030401c0c00040c0c0c400c0340d2081c000760901c07003a24000d441d00d10760303501030643c00b00c058514a0000f9400310801081115114449811386202c1c1103020100304c81160b0510148544a04690800d88072404100242c96580c407218050440c10070854071040400340c000d41e1044588243c7c4070070301c0756802041c0d00d540c001c41201c1035803026a079280015421a2036072078803510080341c1d615107030404000c10310444c022031014003200341c282c503c00b04090900c1e100207004407034107030001841a00c1e00602c0b44c07808d0f41d0f80143d6800f01c0c3c3d0f042e80c000c0b0b1982e41d441704e07070746030300f000040038903001a61103045400f000441c055141c16510824600c013551348442050103400d0141e4020360340c0244001c1c1c010700205401c820207001c003010040c0710b00300d8106000403004101c0315405201c512544003240c0035958981c4444050450f400801c1190300f9401107440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 659681124 1250 659679874 659679947
    0x12050c040912030f290108100803030f0c090904060b040c030b130b0a030b04120f050304151806151401081e0414030c0a020f01081509060303070605010f030201 70
    0x429200f80366489204811000e019000030120f000604100058001d141041c0c48605030ba0b085442d0003d4410400254120a40d24402c4181c514010086003140d9aa8110b2482060040c10700c40b11040180008482031303641c0343d2a24802c601c0b03254007085041140302400151903141c132000c418541400014121501c075919004140681401d010488075075020100d010514180c0010746000050320402050258040b90045007001c81d90310011410452001203c00e40400d40d4020b00d640c49643c1103202d8418030b500411000d02907502003014903220381c3c1c5c6000c1151001c4002c0000050701e03d40030000640c0030b03c1c6040d122402824150744500c1d1041d1400000d03003104d02c0c0705010124003804903003403240528100300d0034514a006c83c2d41d90604614095030b11408840101d1080420130004a01ca51003810b40d0750103000c4150300c4111560100f0100014080d00804050f0180b1091024002040300c0340502d81c020040d074482802400d05500005000d14082c1060804500c0c81c00e0368110240d24406 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 659682374 1250 659681124 659681153
    0x1c03051303120e100605180f07052a1b010309050c040515060c06011a07020108070f020c040606080108070b0403020916050f03092a0f131512050c0409 66
    0x1d000031408074a00328403001884280c0c4892500e203d001c04181302031059a1050f000c2e03407801c41d00c3d009606040c1c9410f1101003c11a140b031003840110021403500c0380104064040421902008000180442c0310030304028050242e04640340d210001300200141d17003040c2049403100038030302031140e4135040d140c00d40e48190003411540960341e81c1c40003a60072102d00c0c41200c2c0b0300000800302d41c0d4820595481c82c0d40c1740360a00903031540c1c6050400e060307040341424003101e41c0b06c1d5041e1940c0b2001d40d1401410381c0c203030403024548800c4d801842c982030f400355564400d010280456854084065041442c080d1900920b604452817616003040207001603035407001481e40c011000314040c61003060590b401c44860042003081151580003200b80000d1030004203013030702c903804208109032032944912001205e0b120355001040d088000742035021010308000856401102d15000c0103e40388804d151f80512281c110b80c41012070508841c00d40c41008024021980049001c842c2032003421103640f2000d1512203841c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 659683624 1250 659682374 659682377
    0x80d06170d110c03120408070807120b04050109060213030501062913050d060b03010c0903240b09090619060b0d020918010602011508070803030f070903050a051c03051303 75
    0x1910b103900d0700b4104124180c40f4800f40a49440c0b20180000100a070454040c80035207000b0400041032003000000e041c8116801c4125000e0844c9403a1215120b80e40041c0050b156035403a2600340021400c203000a09408920303503803004c02c070343c80c505105003102d0751600b080d40441400e00b040d4440100320383c0d0050440b003c403124142d8514901c40704000c10403c90780000d8116118280503818080154000b0344041d00590084c85840750181003240c0070801404002c1c010071240041c280f1504902034444451742c03050b00009440f5240c11300080750700c8821a4421401d03404201046180742c2c0300b4003c00e103a090901c00074000b10b41007040b0031400e4001d096141400c0c0b0f50104040d501a5100781c44d201c2d103022441c2c050009961500d4000340a02100b80e08840450180c4000140c401c00005103a021210414044c509680320104030039255040030349080c0802c881d1800100114a0900a41c0b02c002d1142c0d00a0550380c07429090b240c1c500c00f0307101d424020301d442c0000b08140f03088909002d90269506 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 659684874 1250 659683624 659683637
    0x18060b0705030a03151a030a1b2a150c0207050306040b13080706020703111b01080a090f0206030a0b100c0209060906150414190317030c040e04080d06170d 68
    0x10008004402c01b640f000845240c100100044219401c0003180504120701007485042d0580039800100e4030219045000100e2040d2100e041000400c240342c840c88041011010206542d15040a001c0100c808030500360f949042582040341c0420005000301001d40c00380c07070580707803540340c20b86045070060100c00c001880500c80410005500111541c20343c1c001c1c011512043d81d810002c046000b81c88000d4514802c45c031b55054070214000848411000503540c0920320382e52a1176100283c421241d08039401110108008010303911200074610620b482d120001d40c2e80c5101e8208000c1c0c2e00200e08040910030040241000b507140c0c40d030b40350b0384039000740c45828042e00d54001290022203906100000c080700860b0118141501c201451400754044484203601c1c8483d20604490400c903100044c40f00c034080c021034038203011610207144d1140113001414281592a1000c2007070680440d400c8a08110000710581160443c3c401c4ea0094640780840c441005005070200380da4140355040c0c817050150 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 659686124 1250 659684874 659684891
    0x110f040519050d060b030102040e0f04051e250803070312052a03090a0618021306062a060c050702010314090309042f0c0706030b0112021c0618060b0705030a03 70
    0xc09404039030090201078070111251406038558480c0a80c1500c04498074080c40e02b90f0003400c40c412891584073b520000c068010b055030f0000c103600007149111040d58500101100240320101880038000040c000c1d01c039000207850701d41c412011100000c04e20084542d545130b080d24448a501da14143c140725074840903550f500c500c00d4030352411080e448020220350818040b01c40848450704000d00141c8223460721051444030181c0e48064913418003d06000a112924564043d00d1401400c000501a1801c1c1c03041b8000d00d4941c141a01e02c041030580204400054035011564548529070b076200d03440307038156120708001c01c038071761644601030460344140e40345e0200503504505400ca200000985200e808880c8021051a802903001025050400c0c0508640001c07003900a000d00d8503d6a0140d4460140c9071079140b2400081d04041040e40c0c0c103203042c1c5c0c0646642c102c64032801e40946400c2da94480c12a8100756040300382e5019801c2405076040600c85600051000000e4540611071401c02090044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 659687374 1250 659686124 659686129
    0x20d020a0515151201321501050d0c020618030a1202030601030b060c07300b0c0d05070c050d1b1127040203011505010e010f0201110f040519050d060b 66
    0xf0480354145074882da8508940200002c1540b00c0f60f5490144000602c410801c0d4030500c884020545c100c4490410100000384048000340b103001c804c4205041840c2003014511805084581000f103041c050381c070030018001442c04256481444121000095107001d0f011031004088030820210046140c0d004004034055a0080e0804010034030003030145a00c0c0d45120b0400750ba102680d1103142c80028020815401c14071807045094540b90040312146001c0d0180d45c1d034150101001001c0802c03111051200b0450740c05030740140c5024180d6903650b0042101c8a0400c0303410048030010400c24408100c1480e080301c2d0700740c082d080e111a04046442c10b201c0701b010110f00380c101040c1c0543c03490b0001043e40110284116071243c040c0740290000c00c0020603621181d07c00b40d0403402014003050754450140e58a40c814004400156414400818030451810060b14190400c4513124014000410300740328504013041c038020002604040603403040e1815010400c03900360580050000350b212585524642c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 659688624 1250 659687374 659687401
    0x60117031b010e0a050604060609050c0307050904020f0a0810080708070611070e1603051e150d12020d030e0106050108130f0f0311010c0e030d05070317010f0303020d020a0515 77
    0x83c881c80341510841c04142ca80945c50300d40403601299090302e031050207c0c264a0900c11184240300c02601146141c07240c01058503160071100107954000e80800c40350f80c0c103d0044003e0007103501300c0d4480e0191070401c0d10051680074a1500048001d600aa10800c1782c003d0010300c60301101c075941080918003000e4032115081069503040391001c40c03206c00510410781c013107080582ca03e0700540c1d0104182d451321520300020301300300100580f140308414082180c1a1645040602c240c0c07000b08410114050f984d1b9012050008101140c0507070080c1d40b140b1289a014010100340b4074200008210081c00d000000e80300f074001500c009416010240801c1c20000351502001400d504900544d07103010705890f00509050303030764204a500f5400c1c12100c91b445030064802c06500719008010704810308c60014111242c0c0c000300010360030026160b070000c2030b003203480154501074580d0b0060465003a055050191405081c60719180442d84075005130300101c2c00c0030a183c0c240d1102a00c0c0e040b13058680e6032040020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 659689874 1250 659688624 659688641
    0x15020f0304030302030c0601080706080402040209121501210507030f020112060806060a12050a1b0518040506160203040b0d0e1606140f0906070f081803060117031b01 73
    0xe1000160100038190000081c0281141050403600b03079031303291802e158070fa80c054415640840c01003804280103140c190090000810080c01c03011703941c00e00052040c601588594450350707080e1844018040901303c241031000c560f1400ca0184120203180c2da500e551081c4502c8080c060001c140d00c00c908580c070801c00c100d807441c501d000030300a80791140309903500c5d414255003075071045483c090005a101d0880c901182459040006024090083d80b92800b0079507004148104c0491001d002051503034a03008001ca45c5c4401a0344001d040c80c1900d0024a00980604005400c089100c2c008807013541c000120740c1078400500708a030701d030800b0692050143c400b11310016450300414200101242018511100325031141e51040090850800c800b80d461040102c1c0301d031141010001d010050521400802c0440c2c411190f40304821040d8440260b2600181c18052003c002c51403810450f00e0b04000c01780c05089851042c20300307440404112541e0348038103541242c2d501c00c00c01d9983c04505c07003988035480c1e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 659691124 1250 659689874 659689903
    0xc0d060b090103241e050702010b030a1a060d0224090405010b0706050f060d031b1704030611040b070b070c0215040305060a061226040311041b091502 66
    0x1070307540c40e031034560014500c8062810070900d6046002e00400080c4c024242400c0c007500c1c10314a201c4095004d00c0180900400c00b00c2550740b45e000c0c0040980b0f0402c05021003900a02034001603480b0050162901c10780a404d00d03219403582c00141d005030b61764400c09426031200100505c40441c01415003122070145440207a07010745000b000041e1000c0e44002481c01c0c07031098008005580e540300d034035451210107646250300302043e440100d00180c012200d01d030440c40c4a0543e0f148a540c103640701c0c43c8150101034000c409031404601001041072070701a11000244170282c0508003410306890307008238040d550002e8400104030011820890244841074107054014002d42d07400407855420108a81c014801114a84100000600c0703c030203c6c0300f00020707640c45268801c4108120345a4106854641d200400c0514000d80381c50095804072000b0300c010b5214030100c9041040c0907041100300e500140c01c4c1103d9000b10580307111850303441820001940c5011050200344076180400701c0c43c09403040310002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 659692374 1250 659691124 659691139
    0x309020d0809030609011a0d06020d0e16060f02030a0c21081501020715031104210201080601050909010b0a14030910061a03150f0d150c110c0d060b 65
    0x5007400128002407806400550803180c0326110384000c11700703e451a90380b12003121210208051585000201013a130540105c10150a04912038074500c1251207074810340c140c5900ca002d0000c14030714180102c134000c10060030007881c9400100e801945a20809a0741810803000c0d40054003004511005010701e5075001014406a0388580406408071400b9141490b114100c071400306030315072001600406440362026201c90860251401390060920320441100c182c0041c08081140700242889204104c00704041500c484c0d92400003400d01440030341410304002c0200240c80700c517140d21040c14116180c4500d403640d20510b09004454203214001840308420000085c0300e418800012400c1081c01d094038100101f650b112000180c44481007040516058280000341c40b40c0e00c4184c0b003c030110740260888403848101000104840034042e0210ba0056011000b802c070491a8402c0407401e00e0035050041d0749003030001c8101d07900c0c0950039038a880b41141c0c010b020200203054000c601d9800001c1c0c50070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 659693624 1250 659692374 659692399
    0x183408151308070b150f060706150317070c090c1b05030c10050a050601030917160b0403110d0f020a14100908190507020112050709080d030c1d01140a030902 69
    0x2104e0005071020040b41755003509118083c07411680140800000034900e626180300c0342c0e80e2074043d141828a00b03901404110000000c00e0200c0d0242e010018150100350b1b540c0d00c1403819407030b1141190404d1045c41c1c1341c018032a0302c003a0801900c0900010002c1c0b0580c020000346401841c3d03200c2d400403031046001c2c14560000b1a10b541e0040790050710075900c00d000c0796440c034004600703c503030100024082e0403404210050200f446c800074121201c0c40c10480c00384602c1511f860340d07401c43c155411800903c07000f401c650000018400005040420b242c1081c1c0b500c0b2041c4001d6031505c40e40c40140c8810305503c0c2440c0c8103d002c06c500107000301100024015440142001c0e07a2580010803d00380f400719007814500d000b0b00c10707411103100b01d42c16190502221001c4036a0303401004010305200912030015000301d0305040810542c4140308281d1781c017051403500303e080203181640c1205c4180d940c2c038445140c0016aa041548011a45039030701c3e54585510080000300c3c0601110840a500300c034440010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 659694874 1250 659693624 659693633
    0x1350304180e03071205250308040b06190510030e160609140112020c0c030a0c1d01030b01151e090906051e0918340815130807 56
    0x1d1500c080041020024038503128126500d91192100091016284000454120340200c015100c41400f02480d0311002007000c0707079484084181201034001c18001c030100010801e1b500101640070700e0a0f50008410f926481e005412203442c0e0142a2090b194031a10003001482548107940640e00d840071110540c0b401ca0303454844201a000f0304d00001d031213003c0410308900c003650070000b4a40c181d40f4800142003540a80d0000d400034003007582140100041c10b0865501003000300701c654080c10800794070526220141d80803417441c42c807070041d00d0142d07001000420315a0100b181180d40e80d2548606a080409049540c4040b4440c00600181c3e0104040c0000d9070201c800c40c190754260300704008003a182c0d01000301480005c01c3c084184069070315110b005040102070b09421204031828011a034401c0f040041c14605186240c500030b148003c0a2019107200c4555229a5a0316464282541d410314110070384400441d44100d40c0154120086410010010a08000300307401c2511244c1307807400ca140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 659696124 1250 659694874 659694899
    0xb0306060919090e030c1f0f0c09180605030303061905030a0b0a0f0b0f121e030c06070f0c0b0702071805090106050a1202190503030c0717010501350304 67
    0x1042d0f40c2074980700101c40f074040c0000498510074500d00c024412038211100800001140000049110340c0b101150741c0d803101f0500580a0a58a81e00d98000d02d9007403510301d5890050035481d0205050610f2010806038401104580e001041030f210b14405846091031140111301c02d41c0100d030144145521031052209041d1494050b80c64880b00703022804002e950001525803c030301c071943c4122800403c01c00c80c68200c0104400d90008001ea4401d17800c0b11b1a2508031180740b0801c5030440d04000f54460b100c0300203000b4a90b0040d41410480050309c2c0a060003003c001c03e005008005101d0540411403c40c0200b2840e00101951030070b42d040501c408030000d021303280560f58855298200600454585407441107001941e41414014200801c02d408012030203412100c02d9820907500c10000c1070b00d4a00b803000740011681c0100404186260900ca21341003030000700040c405915250060065210240f01c104160226424601c4000d200340300295014100021802c0c881c41300040019282c0500c80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 659697374 1250 659696124 659696129
    0xa0f080d0215060a060c06140c040608011d0402060d020f0a0306031a070807140f07081c020f0901030903050d0c0f0f02120a08180106090504020a090b0a0b0306060919 73
    0x1800d641c01d221a038000304030b900000780c0364981c0c411400d0341c0a02c001d03441a0705009040e4010300021800d102e001c64450050001078480800c90640002c0078421f00d90001039082c01010303144c004a0090103d28081690b603040504020700c034400002c0c1080d901d400c00e4050341c5040d024201c90030368405181c07030040d004103024401294860218542210306c200811f40846c800c2c8210f441e1108a5a40e02c08111a18000c150302130130806000e20003524071440342d0019009061240385015034501c0114100c1041c2510101c120010a00400c6800c031008098419a0841b400a007000b0500c142c81d0328054600c0d0246840011406184c0740d041145640d2082c0c0000b0600308a4540c2441ca00c000c207000c0340c440b0282d8004885484c41000b50f200c09078803e030030b0b45a01580140000400c119002056800c1d19000d520102e1351f95150380510041d0f2500c20b81c008010b24070600100030310035407140480d65002107803044006626010002070143d440d0340048400d00340c8001c291380c03000385892082910008050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 659698624 1250 659697374 659697377
    0x40e0a02070c05030f0a08210a0905010b060c0307060c030603020d0b0103020913110f0105160507151704230102070b15190b0309071d060111060c04060507020a0f080d 73
    0x80300c005002d08005c200000c2e071940520290172a090140c940001c80d0344820100740e043c0a07540c0c5003481d441c00808029010340c0c01ca44003c41c0d0003500d13061480c00e513101c00704214030551080145072101d00001084a100c0796100201003403183d40388409500070b01032030740065003001c02030010004200165442c0740c180e0f882100c9170005600c0340d96039246000c1004c1d400030800548088501070703600c2c00312051402c0303000c1450020320341418420030000301c080302c420494503503010f8a01402128070241090100750224074040761322408007545240c2a03003001c1c10160107030558211078050010a52502c0402c0c14900c4029503644078546055043e060302141c54412004100328090b440780b400040310007082007403403942640c850400d481c00342c05600181c81c2e040d85100301940001c090408110501c45540c0000a00c0114684240050031a076858051141c0a40003101000030102094003900c050300c060b40b801c181c0b11101840401d101280740d401a184140b002e1f40d00240a07180005d0004541d80e46 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 659699874 1250 659698624 659698643
    0x80403140d091401150b0304261806030c0a050c1e03091305040b160c0f060504260a050706020715090c090204080309040b06070b0720030309030d0b06040e0a0207 71
    0x42850a0817030b0961705101c0428414100c00300012908180a0354000d8090303c10104200080300c0d11864204156605141c1c180303003c150110020752491040a0010080e140b580c5903182c4100042e1040c800c04210f00305006000c200081c5088041140084411403100c3e180300801c2d80ba0103899490b049210014071031142d041d896a540710701801000c1c081d59001c51401007d455040d29540b05501881e074420070002c103030160074081860503610402641c000d010014003401e060800c160034050b402c050035184464000c8071420303200f140702225015040c5d843c00c56250059880c042e4045c0c410100c01401d450300382c000c1c00d102664940d00040d4035900c9040340346e144c5079450316a201640074a2040000da500107000c81022814190401140c00000508051901c80e00e5640c2030055642521910300140c8100c18618900203941d0b241c144645800c4020740c15440c2008003269a4840c8440042d4020b403200024602503e81e501680c01074450318082059515008003610022340010000b5540c0e03a04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 659701124 1250 659699874 659699903
    0x100b01030e0304050603040213090c030215120105042705010507030b1905010305100e0403080f06030712110315010b180609010206040f05030c010903180f05090106080403140d09 78
    0x40e200d5494003031540400b46040078900020042e00b80c20081040c0d800c051050201811403181e0300c03400c007403d4420035241c1d0303015003180107000782d205241010005101042050711502610700181e80c0c1101c44c01c40f0046010150317480494080c2e0741923220f5031410000d8403101c2c4100441034000c24440d003140e542c2001081c0200e01045440340049504100d000006541884654030a420a41d80a502600b2006009648000b28405c1102c02c0700c0680024590f0000d000f0020300314817a2030340180081300104801c604101d0b840480d1188000010062416040c81a802d0b4600780104981c0440e0341c1346420456a60f80d01140c00c0754000390300313201e6403001380c82409424504001a141043c1e4180e0083c28159210303692140d401141410a556a20060100f18007100090203203420b00b5200ba40e566035520201c90424465000d1500b260200c102031a00c01c0c0b2494603988542411a80e551402c064a0b4580c0e05007510065802031102da607111001943c01c010080c15000103000ca803159132000300116 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 659702374 1250 659701124 659701127
    0x903030c14030d02131716030605100b070f0203160812091203130614210a0f020a03200a020a0201050a030b0d0c0617010e0106032304110a0b03010e06010c031e02100b01 74
    0x1085181c035a000100c0700304244041112a4002035101481400700400d5984586071041c1741d37080704204440e10307000740d0185000c50509102c7c003000b007201c100841640f2400c2c49402911034200f03245041080c4804100560569200d003c00e088062440c030603290b84882070481c529051480f4041c01d0f01003824086520b40a6022008a4265110068074240c0d0320141102c5188140000740114405a0304e541201030b040006100400c103500c01d645000540c2020038540c00070410081d05082c411a0050000c10411038011070070402d116030900e412540c401100000f54003c05058500a030800244204d943c1041407800c072540584880c0e842e51501d514010b6032131460b5003024000e405070114400c00400400f03020b600030b42a83d130004038012402c90083d50340003803000c004840640d0002840885141d840c140810390700e029050194025146604103540c80c0901240681551b0401288001400038103206900a5115000360b601c0341e0303890000d1507802595000940070050b501d9181860070b82196 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 659703624 1250 659702374 659702383
    0x9070503040506070c230102180301090521120c0d0f0911150d020c160e0103030c031209080315040f0614150415020106080d0903030c14030d021317 65
    0x7140d004000741070f16a91382c44110f03480e02600c0b208840b08100c05050480c20002a09610b502e0303010180016111380d440e0070040321707201c06c64503400e000c2d034074068400c000f050011038407203040c600c26072505400e006049038081d59445000100e200b2a5100428000b442c4c0104005003844c0c01180c4080c88038160504000301210004140204003d0003042e01d0030b40e0741040120080d1110720000414204002c0b40300d01d030241d81c0540140000ea4002010581801c10482490000f50042a0140340a581156009000c42482ca6005400d0140313140340d030340580e407076a04928200307903000394000d440341072003030346200c0000081940c544540e092240c00944a0540e110f00030440703401503001280c200442042c48070216601140c030f540380904100214203d942c009580c10310000e15400040c2d588e240142c1d890408400c002500104a40c011341000441d5000c0f0b011300202c1d82200005c21400044211680f0f0340c071a002a40701900d00228101e0501c4c0850760030130007101d91240c504442c910070300102c02d445 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 659704874 1250 659703624 659703631
    0x2203170f13020d0201120207061b02120f071b030803070e190b0306030304030c03050d09140108060105280309110f010c03200304030627020102120c01180b0609070503 73
    0x5140c4407040035001d458a4000c4002160040c1040041a10701c0d1000a042c0d0740b12440548035981c0300e0140384825407895200c21205060392016052480580ea10300381d261040f000720618a407804240361040c0001801e01c040f1601a00d030b4a48040c036a2454201516042116070340302061200702c0c0354101b802c040303030100c41e60190409458102402e100c0040310303907080640690781500c0244004000a41d49240050103035001c1d038010562403000d450010400d40c901c0d00854021000040c002c105030760401102504604242001505e402c0000310320482884d601c4140107820724444055040150150b0046c41000d008445024840480e8014081c1c648256030301c841c0001c50040002e0042881005604c000a004410103441c030100320381981d03d0354025401c107407003050307490120101d80707501205548940015015240d400c03c03802e400103520b9000614401c100610001900c000543c0290f002d0b043d444020280300b020301c05641018a001c540c100d4010b40076030b2908003c520381c1781c05803056a20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 659706124 1250 659704874 659704891
    0x7180f0c0c03081b16030806030f0f0703080304060912051902010608060711190b060111010b030d180f090b040501120f0f060b0402030a0b0f01170f2203170f 69
    0x103c0f901d03040c800c00202002d210011071000024050307020ba450800701c0c90304065000e640e501105040031000c03d401c011140845110642c81108035500c122808030b4082d0031a40c012300055183da07034a090500140034120030042860000c0a0f5102e01190000c003e0640e8440c186c0103000c0e00189100f00780d01306c40890040f950158800c400040c4080c0c070619180384a080c01001303403064068643c190070700c011500d91048a044484000300807455130b100d20369071003c0b11900000d201c004140c00200e0323200c1440080346c1041042c5200f070880000b11411000e40140172030460a52001d507100441c00040c00c480b41500e125500f01000040c104000519029690b500304903c0d00707418440d81e0314059485808817007140d1203034503941e801300681e6861010354499405203201040c1007824900304501070030b42e0a8041d040c408903c4070345034280070040e960342c0d2014110b00700085940ba0414840300c0e0283c40000c29007903100c1d85c0e00d008205907005030b101c1c0f801e0b80c00c50700c2d8114988527110f46501c041e808a80215 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 659707374 1250 659706124 659706137
    0x6051f1203050d0b0402090a06050d0f05041a0a1b0e0306011401050d0f0f06180b12030a0503100e13060501080303010605070807030909060b18030606012007180f0c0c03 74
    0xd014910303a4403003644c1c1d8500510041c41c0050b00404039503241255484000070407030110305603a000c4141d0185420f19000f201042080c3d142690390310084589004824001004100010704105807039031242c007007280c1d080b644000a029500e4009c1c8500c40146c0c8150007030055000010301c1115165620704240816102e45050421041050004015104207800010741340e84c0b00413642d10061060f1070190030901d03003116002c89401d0059058a031060750741805950890025904480c2c080140c6e0000e800d2481d0003980da0b00c9282c4044003001e03440d00080d1502c0607040134030140740d00217038000c031902c0e00c209428001a070303031980e650b13449000034814280480e07403c20000c800610786000414042c0d10900300b070030119403101d1495086981b80e07040443c15440010b00030044607511100b00411500480c010700b01c9181000000780a04208103400c5200b0301030f030080b80d892600520403040035003203a00300034554a5040d082d85d4041c0481c0c111205030746160401c0b900c140c6100790001640944c0586410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 659708624 1250 659707374 659707387
    0xd02030d0c1b090203070e0d0209010605090a030534060c020d050f0601170c030619090f0807050c0a0618031b1205070609050d150903030906051f120305 67
    0x240e5524540c0c00d81201ea030034521108189850b0140d018402403c1c0801c40161280341c4007601405000108103403602c503a442010341d20040c1c0d540c9039114103642d03107440d110b500c40c6000804a07207215415000100640030381d005440202c540c20184d034540840142c994458220114110482c41403113000351000681070008200c0035003048008880d07100d220310f0443e24050051a481c6080a0080e0801514100301032041800c01da0108800540d01c081140503200500709581c07600c03444030f00d00b0020180d00343c031401c012062009007030013400280d0f00840700f5036803450306103002900c4010170f8100b50b10410070008080f0b070707107407240c00b030003450f03035480c0060007038143c01d540710b0f807180241ca030300038a001800182003c10001c81e1400d025442c58400c40c010440e0700d0402c0800f40c08200a500080c1c0600e022040d0b00003c03030041074407501c10143c0c140000946003003070f05088000c0c020403080940340c54104000c0c4a0610100c0c804540301c056610a80303000702d9103560000c0b00c001590380010740015000c3c4800c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 659709874 1250 659708624 659708627
    0xe040c0b0f0c010e0d02060109020c0717032b150510030506031e030706050c0901050703030f02121303090b0315040b0612010b0415020102040510050702010306081603060b0d02030d 79
    0xd0942120041c68a810b0290021046003914103100c40f10400d41c100004214100f60100492030140c03c0c40c80041d814803402034030304c641c0d0b8007442c458000c040301140c1c1d0000b01020144100d814101c081348600c0c0905800e0b40e2440784020820700303070644107442c0141d0382d0070200251203904143c0e1801444c00e0400c084101e81140034001c09004903034103010301000c03015240900031800000d02d035003a014580b100c070a410010101c50009000ac908007808001c1140c07160780c001c08880500344d141c1400240ea40401011100a020302d072200c01c1203848207014820540c070b104805c4d006843c440c0e5131701c9481c035884884084aa020580e03c0200000c0c88224030201486c0035004a507a42d50b0280c00d06007004184881c144807101c082c1d11003400d0040c0001c0c03e002030b040f461400319051400d0b00003075141611340400301b0015000400c9034020000003107000300443e0310031b80128000340140e00489240c00203425400003106c086200490303009103031042c0c9000b1307824104042c0c002c45030028042e11200141c0d410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 659711124 1250 659709874 659709877
    0x9060903070b0d0f1503030504050909030f0738060609010c0b180d050c0304092403030201060603061a03060402031b12010317031b0f0c0105010806040c0e040c0b 71
    0x5103581030207010804104a000030b000303442d190840d20004914909038107003040865002c00c0030448214100441403010a4000048804460042c1c0c0da800050b034456032a00d080d405108117844c0180800903100c018008401d40b034a29110411302d510302410f0300860a481c00f4074201220480d882d02120000d500c4c1d28100002d880c8510041c105a8038001c0f0695a02c200a4412943c1e0580030090050b1040c80910401c0090001c980504200e482c0c1103e6404036541c0e17014078400d110314903843d401380f400314088050807000c448000c4985042003d4072454081e010f0a8580695400a03150050010343d60403098440305230740e902414940e185803903078810702000c1d510050524640c05954084801041d0340c1d03034010025433604910320a13540d4114a4024207076604031103043c07094481803040c04540381200c40c3c00000010b0451003150744240007100c0d040e0b1809010610300881d460000000750145c0c000c50741c1441035108581e090f03400354899860741340c040c0c03040e500a000c45240342010b2102c07408440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 659712230 1106 659711124 659711137
    0x130b0d060204034b020603041211070b04050d0f080c0705180f07082d010e06191202040623010e010f0e0f040609050f070e010c080906 59
    0x2030100600c0c03028850542041c1011184000305132008442e071351055005e0650b945910300ba0500192128080c5550004209491030360260564007240707440654110601d402d0604c0d00f0201440b909051400b82120610003816192000c144c48038007a18040134003500030810607007403a0500c0340800c0300d84041d001821958080c0300303c03503510f409220390007056807800030340c25641d6502185032139000079258001c00752445103092601c9254500c90b8140c69040b80912542c0d1121070602491150302c0b5610300303011001000c14803001c81480c02c1c0560b414001000403901384e48801b05124801401e11414409500e840c071845682c0d40c02c02d0005101d41e1003401d00050714841040c014110040c1c401100b840b03085c0b044a0b90000d951951721910203030481c84800c0000e45462030300c13030300360309070035603c00e004110300c40c49003852580720b124174101072036100c2c03403031030400c0103200500803640c0100 = true := by decide +kernel

theorem cover : BRFrame.Cov 659532374 659712230 := by
  have h0 := BRFrame.cov_init 659532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 659532374 ≤ n) (h2 : n < 659712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
