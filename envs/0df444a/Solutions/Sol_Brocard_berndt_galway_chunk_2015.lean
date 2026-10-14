-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2015
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:18.940191+00:00
-- url     : https://prove2.me/submissions/56e6f33e-649b-49e1-b9a1-601c783b241e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 362230215 ≤ n < 362410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 362231465 1250 362230215 362230229
    0x11209021507060e0d11010b01020609061b0904020301030b040b1b03010b0f1303060c090803030c0403080903070909050d17040203060703050a0b060f030714070b07030f020d050f0619 80
    0x1c07110006000e4960009000018070800d408a42e01100c1103807103107003452040031800081e1020340f040030039400a20828028040a03c0905400d20708040c549660701d1010709a20321744500051a075038060f021a01340c448507135009000703650340d5940307003024054000103507002e41e8410400d4000ca03281c16030318100f40a901031a9103003103045a01c1c00201103c035403c2031110740b4182404121941d00c030390500030f805d0003640c803a0900003030024580b41c0060544900740c000e200540c0c010401c2c0041c2c40e00c04001d49040b00d40c405099a9038440060120381488141d80c4410012400c00e00e48104101020441c4c0d41511000d0ba80d039105001c5519100c1410042941e0180d0180c01101c04614294821741001c3d50140180c070012a1030643d480210341154409244d40c1c50380c180200c24002e240394462078a014154a0528080c20680343e511811540207000c2e040c1800c6c1517440c48458142549901a501040203500c1c0c01c010f203241140085049040c2114614810044082c4164000081800f05030035a141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 362232715 1250 362231465 362231479
    0x41509060b121f09050f01032015090f0307090504050d0e01120f0b0d03050309160305190c0e0108010f0c0305090a14250f06050901050d09020a08030a090501120902 72
    0x83c0042802c51014001c1070a03c9908810720b01143c00300d95405201c0c00360381400e244981c40d602d03500b40815010f90220040c032840d5082c9110700e407159120744000c413000c1a085609030352903250f240010042c0c241c072032200790035002c1c00b1030006c0e288070250b01661045000c0d000b41d41481540718411a140b03215029520302054031220110803000403540328015103506201e0001d0407114003070010303d200d92043c49c214005140002084079000013800207544040303207164000013030b506582c1d5981c3c80d281c548120381210385d0000e8070300741031080c0f29664800a1100c841003004030358440340920f0191400d140d04400c80ca05207040100b1841c42803040d50b115070014030180405510b50b41d02c035025849841c1000c400740c892080074924142c207500400212900c0c41c0d03031f030f1034001e890b1034402043c07035170168424028004207201480b40d0b41d804c007040321000345011000180e00e1501c1e100282d001ca5850700b01c01051701c00400c00541c00c0d1b4002c07041c0c80a4075400d0b21841640c1c1c540528403400d941690000a400c096 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 362233965 1250 362232715 362232721
    0xc020a141c08090106080106090c0e030c0325050a030807060506010e061e09060d0615180b030a090c17160308090402070305271002010509210405041509060b12 70
    0x8800c00e4955080710f9000c0010801958841c0e010342541c0c041d8004001c03c03070b0b580c4021404203810110703418124200350090200c0407262000a600e5810f00544022400300d003001c460340c480c000484e544050000100180c003281c0c1c507401c241c40a504081003c46d40c1902e8400413076030a40c002d201c00c40c412031005002605d8148044500c1488820b025043c070501a0240701c0c446d540d50320080a060007654686001503503900e040040c003003015059030341005204012300740c00101800400e2040584030600d034180d980f9202c282c0c01c58000e00c4510070151880500000201e1188003020b0031f05040030300350301115076000010303585550041a6110050000b00c080048521030300382500580138250003402c2c401e042c0090500344100740c0c072541c0303182084c0a00c10103244000b440e0408503d442508070340300070000d0303203406407141d039541f104070958582c150059003ca1405080e404110360207010080c0c424004080d10381301c61740040c0c1d040d0141c2c002c0e1a0a01202240401d580c9056490220315a28004202e403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 362235215 1250 362233965 362233967
    0x1509030c0a02120c03150f0601081605070218090703141603060b040b09010306020c07090c0509150c030c03090a0801020c03030103030c0c030c1706070906020c060f0d0c020a141c 78
    0x150f00080b0440c00c500500514a40e1030380c1c14400b202c02c1e00d8140303560001a1909980348101c004004045505000000060040e01454414807280320300a83c14420f9540002e400011552440e4140388100103200b13170708010940c000031030b1034030840740316940240341c10130031841080e1544c0c180d02d02d0b21254811a801040890071a41060074543c0c4007400000c0d8050a0f9004540d05030303026007041d07400c103400180743d504403d801c1080d2001030070495130400412030303040070081c8148250200c0c5442901c0c40c891a80d502e94020381210360700304405040340d84e00e43d0285403050b22500071116980c8208841d40c1d0000d00c000042c001c843c0354010f6280030318a56821560240d03a00b6480050a5a11002c0380e1030210000c1c0c021030030400a0640c00c1c401c0510038030901c0c0380c50b01c1e11200400c08410030118100030011b581c0c0004e14511760140071108561a10a401100d440c0782c0145003040c80038904160103070305081e030042200741030300b8012064003051110f48900603984404804903060b208000b10b5155188d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 362236465 1250 362235215 362235229
    0x20609030a03110f071a070c0f0206030702010b030609010903111507050a020705130204090f14071b0813031208040c0504020a0201330807050315061906021509030c0a02 74
    0x500392264001341411950070f10342036541c020820484059010a24074100641c0040e40550320010500c0d00900b47d8081d80c1d00c84d0018003241d04000c2c020400480828240341c000c0d0010307403040b007025044540302c2c40e00f40d841134049c0595000a40108403000d4803c083c405000c16a50503809900201f065151140da408451703a511000c90b00301140a910408141c0759608210440108044000580c45500341014001111401541e104c4803500d000d202c01c1e858109444115480105402c002c0552142d407141c0c8401c0d0020031300018100c400000740101c503400240034040903a402080c1c01e82c8100c42000d03081c1d4842105540c045c00c402075503036040165140c5a0002c103110045403002041d2400e03600246802c141d202c063f0181c13108031246114136010041c0ca07804006001250043c010031b0303e0600170a486445c40c0c03081d01c525400d4400015404e8a40401000c40005000b0320607814554401009444000502ca079502c480351040c0451403c0400000342d410b5030030003034090600c12185508012075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 362237715 1250 362236465 362236481
    0x1503032012090f0d0b1f3204020a0c03030b03030d14010f050910050904080403290a06030f06020d060302030d050d0f0608060612010f1a030c090408180a0e010602030c0706020609030a03 81
    0x710b1401b00c81e0100e100700c880d480c5c07128090718104220b121075440c5001c00e080c0b4501c400000e1700551051040d8440c0340da200104031046505418002017a80065002c03d05501c59000c2a101960038400588210000c015001c1d0482c4d01c81e00d00030800340c2d1110b0030800d07042c0059030180c80a140e219014071191925608083d0002d1140c0d0040c3d150960341d503210340b8a8501d4041c8241000d4001d200320310300e20320524040d64032180d103040030441c0e1815565125022003000740003902080e4003052000b485c2c03985e03500c0000130750340081c21904444800c0c5001000c59105c1511035000c4e9007498500e0040300e505024030001d0780e404501a020760380d15a41400300e084101c0d60340501944d00c0c0c4001280a45140c4140d09030152036582036900300014805043c80c1060440070b0500500e1054108400711b1201c100740c0341001070301c40382006a62940d0700064480440360304603000b400058000000e141e500000105505003000d0152503e803982c03150b084e602c2e22012034404407907400c1000304003149482a0f109031a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 362238965 1250 362237715 362237761
    0x30a1104030b0a0902010305090309130f06080a240203060604140f090a0b1206040c0b032d0103031116121b06020c131503032012090f0d0b 61
    0xc1429500e0300e07114034038a4141c8550181c159100108400e559260180310360141c0b804004500d0000381d50082040d010071100d80010650b502c500b48581c000c40c03070304240d00038a0020121550310310716040244074074a0b40f080a0901c051030b41084034002c01c5500035244904001880d1a042525040c108055449104e1045500c60310210303803100c003607a07008079544c080c6021150001e1058503c0c0144071000300c4903020440c01d45e02107010000018125251002642d084040c0380c2e46070788a80520120108081010a0071012940e4030003640f0500a40c0f114103c0e80030340d4030f56030a403914812640d1100031031080e180c0d508030101e01c14001800b40307518841c50607115100811421901380100070410409422a0005802010302183e01d460441e22188450210701020000c50441c0502c1c14540d01c681e00c002014085074403010041a184410b000c1180110407043d1f43c000205610101a590b0040c3c0301640701c1c1420500280d030900b484041901c110380e0002400000e51217501e110b8001040d150320540c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 362240215 1250 362238965 362238967
    0x108030702150912030406030e0a0b0a091406070e0f01110d08060120010204330f030204090509060108071401051c0608030c06330103050c091005090301060b040506030a11 75
    0xc1c0c1c03613150242c002c140c524404e4061034685003003120040541c1e6602407070003403d5000404040c00701c0c0a035464240c02018031480059184410302c3c01031000607041401030003c0c040c513420050055084101061000c034100c50103050049602c00540d04488a801c0d252103562011464020050180103403640110050400040c030f40c05140c0d501c5250030441480b181c10780d401040410041d142c400c61250903030b0090402c000d0781c070b0100c000c0c1620804161424820031010310340b8419640c1c041e5040307401401042c1d4082c0485c0c40c0494940399140400c1c03042d450305110301c940000d49100d00045103807038040305a54941c502015420301210300040715516907511b682d280f9000401000400041108840b0740014081501d406a50104900050f001c0f43c5044900741d540e0328072054400c0c12130380000c9001d0070001010388401440d003c0900601031a95000b100d1024019203190b0000c0c0035043c1c03500d08030024044140c40e184c51295a028511407160411001d002280501806801501e000c641d854191 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 362241465 1250 362240215 362240227
    0x32b0305191112071115150a06020d0206090111120a0f06080a0c05030c061611040519050c121308070203011505031504030519090314150a05010803070215 68
    0x441164201c1500751000500000c0c6500f6210802c1c11075035110050342081104801c3c0d250405440d00704040c5140040204a00040c3d5060100c0514480c904809800c1f1031501da2100c034007941e116100004000903202d0840001c0450781e0501951140c0c041008800d403c000081061100e0900c000e001c2003c51138031040200407030490303403090100030094031004010300000340c24503950485e583c0d00054080d1300018201c80d07164032404100c0e40e4100c829802a1090384031401c0030350512100c60031583e031050400060006604181d1040605245910801c004c15191403294684911410040750903d844100c009000300364444c0c0ca03005503c1c0607038822850514140d0001e400c41d040c40103140c0c0301d842010000e2105080070030000301419070b0004880100c2c20b10340c902030020b02419a500c02c16080c244040c18149101c0c1a88000641d40242603c1b0748412603000282ca9040780c00c03440d8140c212610010313070400258010346049800d110003a510f014500d03002d114004056001030704907080204a8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 362242715 1250 362241465 362241511
    0x303090d050304080a05031306020f0613060e07080d020d0206130803040c08070f0f090b130522050105090105060108070806060a050c0a0c1403010606090509090705060a030605032b0305 81
    0x209154503106e10f000d180d03202d00000001c0181002500044119030100c59280460380c0001a2260015140c0342c02510740e80041c58203070b000c0c01d000d0000c001c2d180600440041c861000181001180c082c03038003a00d402e0540c0b000101d0703031428103c91035405582d0b0003400ca008140300800440e0031a000704524118075441c1c9045500d03207841c650003000071110180041085041d03080305c02000e00a01c02c028040b40c02800d00181d602199403070a00000e82d620b0010464035079500400e003d071900d40035022411205541000f81c000e140840f2032001d294204000110f2661003103141758070820280e10340e510300b03480300d0003408038035009000000305020003040b06040411302080400e03055442061002c0c06641840c0010556185000c8050f000343e04007801800156004019901520429100000203036a90380703442c3d1a009056000c960130040001e07407032002d1503160700004c003501c1064085616840c0300d540b01c1e180491031030f10000718a218801000005510a80015400c014031084103681501c0c1695 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 362243965 1250 362242715 362242723
    0x60103030c020a09020a050d05061f020303060a1a0a1b0c030807031706030a060209030102040506070b0f1e15030114011203030b0d260706050c0304060f09020303090d05030408 77
    0x5a010588200003502186421080f10307000d0407030311006506002d42c900015006001c1c590403c1c450076256000a0590749a03080c2412415450300310303081d4800660003000e5140ea1050b00d1050041b9011403021600813180c1040443c2008061040384c90300a029030b0460b031118181e500c1c1010386e09610540404120300e00d0b0840b000d18043d5150346e988184903c6e001d0b010303040c0300860103a4039020b0001c003c002e50380401c0100c481e54000c0b4000d0b982c2c1145000007802482540c204542c0000045826800e0041041d5140d00c05c04004990381641d441d60b04c0a02e552010003241310040d500f1280000c0e08002c0c00c8001d4005400c030190004c118030100d0042000150000d800c101d052800c48072602c018150706010340d607580401510701980450380e903101c08500c000007850131100c0c140b8400300302c1d1180c240042283c203950b4010504200034201220030003143e500585060761024200310040862a1042c82291a200c0c0d00a004510f400d0f51402804001c0c4842503041e22103002c1131100003501c250501c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 362245215 1250 362243965 362243969
    0x50a0318030e0906010206090715020a0501110a1805031b1903031d15030403050309070b0c011a030c0112051509040b010302190e04060f09080c0106230d11030c030601 73
    0xa110b0b00052242601404810040100401d045512a005000707071882d001ca50704043e40c03040b8544040c100038058060f45440c0d03020000074403542c44e168182900040f002d0180c04004a661b88040e0703600d08140c00c0400b2008603028180c0d0603000540040d1368600e00710582040104082c1c1006200000b8040603c14001d45500640100314003a922140003034001500780c00042085815003107011344074031207a0042c00010b00050520400102082d02900b04010440041c10b085200b9940c50b0200288940038201034801c0035140910700c01140d62178034011070800e000880c1a0740b50115000c12000000141002400c1c16810f80140c448254081d101c904070503100e580101720342c980c59455071042c08804545000510316840e051003047c4580c400c0220210380245e0000703804241d081824804c0310080c80c5420000303105040004101c5004601034220f0400c840040c0c1c440401502d60300003010143c0b400c21400c6602504100301940099100c1081031507001d0003400b2104120b42d080c0c0820301d031010a07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 362246465 1250 362245215 362245217
    0x100b07030807080901061a0703020a02030604050c01091401120911030a030305041202030f1207021204090c17060a0302120c2107120209060913050106090f0e120a050a031803 76
    0x2807000c01c2005500715550316044203e6a00800c001c915102021850b4540b024903281482800540c42e410b06100b00450f801e2550014182c594605251401950310301c8600c90b03190114110b002e0010312200d42d00e181c0541c0040603169080e4400f0450141e400030f00ba0030360304031920114645926500e480422104c441148261000501414542803403400c0c001c00c20405400c641c41007001e55184200c45054030030900d0307091190b034082e865006c1c090341488508800009401c0c00890700141c030300d100f0340212202c140c2c2c3c0d803244000704600803080c807165541260415000f000e1042c0410060510509283c01e01140f18107039032801c80d46e00002660140440303007600d4489000944010300307000c00e110310b00051030030458800d29481541d01081e5170301e90080030688148075050000b054000034090418507540c0c0308000300407040d140c10354070006040002940240390f140003151002038400088000c070084c03519582c1801e242c0400822201a03000c4881c40c400c05031548120768040a40d2611a54030b2486 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 362247715 1250 362246465 362246477
    0x9040e1002040914070c140703080f031f1a07060b0604140109080102040501120203040503090d0c140d15020c0f0f030a120b0a1a0c030c0f060603030c070e100b0703 72
    0x18011000c000d1301c41008140315460040424400c0b1541c110b450010350581c1b217045074031442e200010075410041d0551000c0c013440800a155181011791500941c0b00d0100c40117041424007145181241180140c040d140584010222541c00c0328419005004181d101e03030700c08140c00d900c0c82c1c00318151b07410076480a40900f01d110000303005580c0000e05107006c0c080e004000c41c10140303440c0c00209181c004884d4105200d074000003050038404148212010404050b0030490034100c2854020200038480c4241901c0d80c4640703408003a28604100700303000761900b2000225540c01e0001c1084020b5000c03110b440d5841c400c014106522520030704c8403880d005d08450142d911200e91400240022064500c6400c80c1d919003400045c80341d0320302c2c14201c25565001c9190241c017904000080c003030700c230303001e0f0140c030a120104182d0203110001912051002120041d902180c41c0e510034542c1d04d0040040d5800d094004650500c601015206090342c81041800400f4015a42e41e01c0f01d05654881901a400a26 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 362248965 1250 362247715 362247719
    0xf11060c1b0909061504020a12021605010501080d0c020f01181d07030c050a12180b06041d030714070905010b1201170d0e2725090b09040e100204 64
    0x340c00c901e641d030f0007080300300038150074500f0f100c1420100480503840ea1140c6c0e80460900d03640ca10038007290020380541d9500b1542c1c0c580008103030032102c0d06044102d034158205030000c180d68801040146844425469030b1091301c81c16801c01c800121a042054108104040000c00c0000ba081c6d0780c000800082c9101d95010554403848007001500511890505041c50500c1010507030020890303803e084030380ba10036450f9035107021200291803110018105040d200710400d043c421030070a058000c880c12141041500c10061030640000c00343c41d000080c2d50400c0c0724802c081f40400158144850485003074440098440a1a0341161002e8121290301000400c2d00460001c1089440340584405c2e0078040c4103d0040808a0366500c8640340a420400711040643e0713a40c07101b03080c824001550070911030310000c10300d0410880d5241261003403070b545d210030943c450076004030a00006c055001d9851408550820059544690040703100b140c00a95600d07065216500521202111a249080150380d540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 362250215 1250 362248965 362248969
    0x1a0612071211090103092f040b090105090127020d1b0206091b031e0a150e060103240515010f050f09010c1e06060e0906040f11060c1b 59
    0xc4940300051001d10308180d04044050002c1a608101001d2802042440c00c616010014880381b10000c81d822080003000380703182d40a00c1c120170000e04103581c00c000f842201401c0000100c0284200b03904480b9040051040942400702543c2510403007841454000360710501e041280e0156000810281e0381b5141d418420404401e02c3e1801141e5100800c01401d001308400c1d2107030100c03074041000b54411f8010b01c9aa84051103455290181101d140421f942c0425000e500d603005034508540890303801a81d0000c5541038450111201d07110380042c601c1da0f0859a40e041c400050000c2003560081110f880100658140100d6201d1001e020301c0c000b150541200252840710204207500500100b44101010044401d058424400702440c20251114281c1420b001d20307480b5500ca044840c0020400e8418480c103600300c02c0854601e01c075411444d03503c641d1060346031a0140c1d030041000410300103031404038040240b00110504020b00f0300f481c1c00e4200c004645050043c0c0e02c0102d8120b00111445924 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 362251465 1250 362250215 362250227
    0x180106050706050726060418050609250b03040c03061b02010e0a0b0406090c0b030702010b0a0b040602061315020c0c0306090c01020a031b0803090604061b02030703031a061207 77
    0x41142d0174942c0104008241e0328000b140602d94000c3e071040c08500051031962550040720850008803203c54800c0c040381070560300c410301100d0102a504c00e140d196036901d09000b4100759100e243c040070000050800301c010110707a002400585012103d00c102001140303a505ca482054004c1d00a2807030b40d0828a4406420754180c60000c01c1c0c103030403554002000c80d100174400b680c403075405600040d9181e0340d86000303940d0b03032090342000600d020b000c820407134103e40540c0881e41902085030400003080e5180710f018014801c5000c0c200c0160010340108501c1c4030b0305c0103040c000c140304180d018203482c082140b47c0120f801004d51080c455022020000b690b04082c400c240d040204000a4034170316125a001039602d681c0101e000701004811843d000010240c04c1c401440c1a038008086a41d0b4100224a66923404040e941030710040e1403e8000407405802c0900d50036180c540e90095400d0500380e8a080d00188041e80940b40b616100b00c10660303450307490070001d10f403496080c0c1c0740341c24508010b44001d200b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 362252715 1250 362251465 362251471
    0xc0510030212090304060c1103010e0111040e0c09180a0603051009060b040501030803041403130603050106081305071202040906090b0712060503030301050603092a031b0a09020918010605070605 85
    0x30f02d401c00c200c24082c00b9805070541c009035402c017903017600400000020078010704072842c0d0b41e02d040d4600201400007803ca840104100d038103084102500352940010003c00d072203641c090550150404443c1810302c03201e01080c0340d02c082000740001d8125941d8890700c0c02c04410311140450a42e54060007020000c0500c40c0444410041c3c408000c20340c11a95129054440640058900000c0450696101c0c504104941102130304001c442600f958600001d005048280214000f090071032001900c8150000010562140c2100060980d246803d0301c10360b1000742040709070381060700c4000200c04101c05029803a541071048551950b60b01d0403040051096905508071039000703003410f508101c2c690b40001500d041d90300440b0125a2512040300c2c0d10318100c0400b0303001c40b09603e084e00b11000d08102000d0851524000e0b401d458150200b81c41c0740e00c40c81d048041c40d9a005264100c14050300311598007034020104090600b801c07000b5010342211a01030709900603400030704005810700c101f141c140a1550 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 362253965 1250 362252715 362252731
    0x5070311070206092809051b03100303030e10091a13080301140f031c0806061e030c0c03040f05040b2b02041e1b09060f0c0c0510030212 60
    0x3041420503800107020340b040a807405c0c403c01544108040100c01100642c040c0202480c51100790b42c0d0b03505850300a06000c0781c16504d503286024045211202240032a4410444c84025075040c504607501034005046480c0000490320803000b406044000900ca2800e1484c011184488400c0540c2c842590114004050600410940003220002070f502c50984e410740743d42e4411580d000382004007140c2c042c000132a2507a4940b081740802200d2900c0c244026052141c90b980303a0002e580d80c0c1081c41100d11503241c01c2d024104040000200441e40f074000b07107400c8a84901000c1c6441380c1012030030700c0c5401a0b00583c5980210040c1000030340b5140c8100d8980c004113540d10404150880315a41c13370409540c100d007000d805280c1c84402156120741c08100300d00e030030001d0f24081d00701c003091103c010002c00c2101d801d020102046611642d00030340c3d8110407554103a4038401c01d0a00703500121f8504072445c03000c4661102401c8d0110b0070744d4a4102c01110410282e82c01030301d9822043c41c00180080190490b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 362255215 1250 362253965 362253967
    0xc010e01050f090718020a0210020409090c2c220302070617010608061e060309030a14130b0d090b01140316050108010501030c0e031902210c0418050a050105070311 72
    0x11030244d4030a170f80300d112009450011b0b10707102c0d0701c44183d00700000c01903e0036015200180c041944582a4412000107008112005500d921781c14481e13907109804d40c41d440d01c03840c0c074006031500f09003000250b507100c0c24084407505500d40c002d00d0400c4004001204401680100c0414003143d6801040807944030710028601c0c00e154034254010f445083d0191541d0b0040c1300801650340340d0f20100d410031b001104050861984c03882d04c46041c2c0e882e81c014601000c00109410004c00041c10740b0025148401a4800038440c5285050100d0392594013690000600d2a141c0c010746000c2041c10700c1c041e00800c2c1001c10380c41e004900c142010b051001030107503403002500d8884240405d990000364681501d80a080000344440f20201c1528003044c103c0100e540b603c134203038180b61085180100e015105109507007a110200382038500c603461040341940c0f800b030ba41c81a4650300d814030f003c0e08401401142800000d07500f12150704c0c3c050518542400c15540380e9120030074040a181c1c18420501c01405440802e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 362256465 1250 362255215 362255219
    0x51c08070c082104060e01110d0306051c0b0601200d0203030f0609040b0105130603050712050d110a030507110907080f0a0b090103141e0f010b010309030e1003020c010e01050f0907 79
    0x7000c503c1c06a4003a8034100704071941684c0e000d034007550b4048c0c100c100c50011901c1010402c88014050400c60080b18020011303018840c018400c0100340810303407548410002c80507901d0500440d1398418910080c0030041d4160342c05100e2800500c25490240300c07623400785070750349010b40d01c0c038120150240c05d00780603403038940801004c107200c4144241510411640c132a00744c00180d40d0000585481c0e01b01600c6030086800c00100401d940400781c0c1194400e80036103079401b46452041d1100302082d0040142600681c5d40c19000038030460041c40b8051040341440d031228080000718180d03040840d03410004ca03404070306000710740081c00c030015880010003505012825a41d00418a2080113110003090000341d58001d0038494402d00100042c90f030a00030006140c00c01d17a44c21959800070040c62855940b07080d5010030345503c2402560019601902c5445101c0b081d0710911003602c40c4180c0c2e4604040d0300f8001015291000e001d8201203004490000c2218201036130004000c81004d420014154005101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 362257715 1250 362256465 362256523
    0x30203060f1e06060c010e0a0c1502100c020307140a03030f0c050a0305040c2112140f1315110106050f030a0f050109080706090b06090907051c08070c08 67
    0x2651082c01070301e011580c1c54440c000030aa6034091390a24420035424011364180329100001e12442140c002c0c07203441740c7d0319a9803004c81007680a5925550040c5c0046407030b510044031a41201d040c2516620481e460600992a518440c1da2542019286134010040c44000d05a25000311054418074610400001c14070341d2000d0070074810f551083d0141911240001c0c144058489110700a00ca0002c2c1c0e07204820249103c051484a0007000b159052541c0610007542c9203d543e950741030482402e0710a01d48a9840700e880e039071350019402e801000d5102030b40420328410005451501c01c02a40700c900f0400f4401c00007600b56440c1da08624010401045850166a8002005002c0c95049003e000c0c0045090030001c0c0075020625000e024040002150410851180d0050684500600314284c07151a01c0042040440d81a20351841650050310180064640744104100c3c1940010300000500050b0f5207411040e00144415104c441c0590320030030082e0800e12003420002210000c1890310862440c0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 362258965 1250 362257715 362257741
    0x1305011d0a031a1602030d0b13020f031905221b09060906060c0c140604090c1e020d020604080a0905030601170606030307031d0f1f030b270703061a0301030203060f 72
    0x4031421039a446020b01403054580f41d1000e10f150042060941d07968005045200441d40291250f0283c437044010f40240240c8910070b86000d4040301d18000f00e051030890301c00010919140080e200400c0180345a80d4502c2812801c100a1146100104900340340903014011200c441d880b0009110320310003902c0c0000e114210301800e503040342c1b901810040340c24000c1010f40c025504038240c03203841d01441880050b0070540750840d20761000d00c46031281000d07107022600c480010301c00340e015910610201c2d00088006025062a00c1d071031078003510305507880b13001904e010707401c7e40440880200c40b801d215000c102801035030b5004006900030352901da02039500510f004004907400001c20b801d10160f03001a5a0340e12826001600140b02101541001400c00c2000d440071624402280c61302000036000d0501c040240020022170407941c0c2501c82c018141c414440000b001030701019620200440c40d05000f402d00841d2000d040019500c96045205042c6408000b8189941040c1e2807800c0084130032500c0c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 362260215 1250 362258965 362258977
    0x10923060c07060b0a0603020324010c020405220b100803030f0103030c03030902130e15072a05030a0801030302070801090f060902010c060e03090906061305011d0a031a160203 77
    0x10001c15540d060500344000100304140c855136015071041c1c0c0000b070403075240c0c0155014041034000c460317400718880028526082c2015030103010070f0100440700054a0154012a48040c85d54404000d1044003001200400c44807074045900d54080b0040c4072a034051202000c0103000b141c0c00451075070170640403404288070144002030400c03700802940402d8407030b40240c482d01d80e02400a02000c1800c02e6241c010300f8008008007200c1c801c5030b005182ca00d0042000034090b040d0341c0c82d02c42400c04002250000b2a0200760030301040903010700c5890002c6c200b0801404000020f59480015504500d402030404403036a1100710644c1c1499000c2e03000c100d070300c0070f146075080d8072201c0040d006107a8401130318400f1404001900c0549803c4000c1c25141c400302c018003144100320303000c100380d17a18601001010302030382c0301a0100707401c03940b4207200303075409001c034074008151100d0364003244802d2000049480001e50001c0750317084003500145400c400403025040c0c00c8024050308400680b84000d001350740c3e0080d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 362261465 1250 362260215 362260231
    0x13110906010918020d050106120c020105040201050a03110c10090c1205030d2408010609060608010e0f090717010b01110312150105040803040914010b0c0a030f030e0a0501092306 78
    0x30080d00707036207851341d040381c40c0d0003600300040c0030707940e940c3c4c80107800d102100800d00d002c0360030943c54030b44d0144180300da548140e50503184c207401c01c0da101504400420800901d482c65800801110505000401c981803d55491010200f520a0346150580c9911402c0e8481c0b0080540c0b41c5030f17000007603404000e440c0c0c206050400000d04802506042075814030440f8008010b101001e0b000c82c0340c5406404c03203426580907000900c0041d0b40c8500403501c2903000d100c2d80507083c0d180004620440c10b00e441c00e540120019003207541480e202c4d20011032200710641c0c2001603a56800235500706581008086990f14801c001441c1003001002d00c040c24010020f00c1040c3e00c62000615042d103a011b4010b0b5400f5004030403c8a0719141ca13401079100600c00086800000340080c1c0002400315111021180b1701d00381040a03016485090341c041d80c2e0410f2030240203080c113403100340c0c50594a20411940403403500600004c280076102e420002500c03d0034200c901d2490050b440d040700d01400015166410901d8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 362262715 1250 362261465 362261489
    0x60a0c021e0d03020a03030501060f080a0b121b09011208090f150409060305120903030a05030403020106170123060109030201111504120807022103100e131109060109 73
    0x20310119441890400340e55a50b0002d402480e01c0245640064010441846501e08101d00e9132594000d554012800000c9000590035030002652100c468008081619000d4031900f802030722030004600740030001d46c0d2440036906a6000381032501c0c041b43c00314010840682400c2c844040c6445c7c6128500c41ca810340b87c0183c1ba83e80e0700c601c940d00d0b100e141e66102d84402c1700c541e844035110325000000d040a840191003520410720104401c074403c00c129840b01d40014001c40c6030191160099a503a00010010780540d5030325507001a0164844140114940100000043e0a060040750500c1d5002641e050594000c80000b0040166040540d0346c05890f02400d1030f040c0310808503407480c5050940240e10b4683c00342d002c1404108540052002c4007202d45444816080c2d40b004400c9964070006a8480c0045114a09400d2211007200055401c08848400307aa540d40d203604001e042c4180c251010002d40248000d10806e02554802c078000402040340d0b054041e00340300d00001d10301c9100340034540545a03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 362263965 1250 362262715 362262739
    0x602040b070521121b1b0f061314100c050703031a0618040f0c05040602060c090a170a0c0f140d0f060203250905090a020307081b090301050c0702040b060a0c02 70
    0x103030a40c40d20100c080325030310880da40d1041048007400b4503817620341c8018030700c10041f1032070140c00c0210b0702512808081d02600c2001d4a02d4071107002c0007484810408050181030f0b415044040e00307028248011150761200350361403421b89030003002c80300886810b02d0010308480c2c040340342e41d85140c00c03140c02ca0030941e00c5d0f0b0030b03103031001002400400c112400d46005625010349042d96981040c023400884100d40c003034481980e80d000c814000341c0304400c5407541c485041c50061092841303011010400c0704511080315074600b480d41e1402d281e0020703a004080000700c9640108075084540700c41c2301d840f480540c0e001c8503410441d691525620507024008040070303008800030f00c1641c0a2a40c800701040405003d2000d210b10080140900d1074034060503024003002400142146541d001b141d01039000381e507a05c0f17250f90711411300040c4c00b09030851413128960100003100e01303941d003401124000c1d00b071130003404e0f9299454410001202ca1050480703004003000c0c404014025000388105405607010380e0b00900c80340e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 362265215 1250 362263965 362263981
    0x20a0c0819081819050406060206220c03021011010b0d0305161b15030506040e0a0231021b0a02060406030b0a030b13110103181e0602040b07052112 65
    0xf4640f16821549440180380c0d00c0001d1689082103c02c00c0c0c0c2d04008290725140100d85071041250002d505401f0486003040c4130105405880205028540b208401501c96002503030003c0b11010000c005027034041c038460060403c0c49080100c40040b5020008540c8a5a010785580210081c45022542c8002000c0030302c14065100405052542c13480b481450725000000d44000c042050003000918040004806080a118505d00c2c0494a402081d82040c5036007041406140c0046404010304000d0309a4400a000c2000c1c0e400402d02880160b11444e010840c09020210220300c0707059680048614800750710b9120441c0c003510414600440c3ca00b40400109000300000d0b4001096007004004018020b00340780b092105051040e441c1c80c0d075400159004400391404c1a103141e0040c07003054101c0000500107070350dc54442400c17003140d000300c007002e1f1182c104a810907403040d100c030840011410704000050001c0d0040800180d00c19111842c0e4003815621801008288007026030f4403808640c0d80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 362266465 1250 362265215 362265247
    0x160c0c090501080f010e0a11040e070504020c0c04050603030f0f030a060f0e04030f18090b010e06040e160908060c03130204060927020f0918070303020a0c081908 71
    0x5008500400d01c4156943c4141c01d0381c555414035101c0065107800c1904200345004941800080d4128518007038484038402008020401c0d820f04110720f03c240c07240003840351a01c0c005002c180f061000641400e005c0841031209440000b40290f100b900100080540b07072011605861792070341c00034492030b100e41d01c0104a9004143c150030840070407140345030000b1441540c584403803240e0700c00e40ea940c0c0c11428494084e03890170741d0314071a080024004801400304561070380c000b21518005141030030300e00b458500071600c030354006e411184009064504200c031800c90f0030034000c800a09840d00c0c15900307151584550b11640f0280c002c452045000000c1944802c0361648180720640080c002c200290317031008000e008010000365514000120380800040d00a0080e8810003076801030948001003803080104414035038000c0001c0c039000c1c804000460007480c1000f40001440c0300b600141400c524505041000c0c501c558090016907004020350721003807880d94406030b0303296440300d40140c40b42c006c25007100321 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 362267715 1250 362266465 362266469
    0x406050402280609090c0906052a0f07051e0906010e060d0b030d02070303020a0204111e031f031e031e08100b160305130506070809040c08160c0c 64
    0x12191500b1007480e030010107100c10100700c903490303200c81c0c10040d138890094050300d20029182002c1403a0f10000c00507903008070010440c6907038540d07401c0000f02c8104e00c0c21044200020240c481a400302201c41036030703c0200b20b81e0000d003104a07603071008088072042584900d1180720415000d0204540424107690064800c560429070081200c1d48440d02e840072500149003111203180700c0d10803110481180e80c00881c1e0042625010350103080c1683e140e40030320020b0540340d40500ca001c4010044c08901c403c11304481c0c28143d0000202550700c1c00c00d640c0c2c4086a82503002000b0020819030020800104041c40c8403408080840c00070f9280166401e003564222401d41c40003140840d2048605191039120300301a100d607448619802d074a58880f111240c5600900b404459942c248581d076001090207040600300951681c210308200780d444501144103500100402c50701100040344902403032401e401035030040d03c1189401d103a00e00c0c002141e6410000c18445090600c1a484110001e0004500c05040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 362268965 1250 362267715 362267749
    0xc08010f181b0201050601031407140f070c060f0f03060b120703090804120b09060c1b01090203030d0504060b0d0203060c280203130b0306060a0f03020d09140705030609060406050402 80
    0x15903a000c1c00b001038080d10702210700d075000901c0c01c842d4020750200c5028003801612195514141c1507440240000c8540c84100c024034907101c28880340300080c2084100c04041c00e8190307204102d42500000140103406203445050a141c1001d0040c85000c07064025501215814015190103480d2028143d00130a42c03100d0103801440005404111011000c42401c4080d20444a204048e0382d038000b85511000d041c0d4070145501810400b8056207861110301d010b00ca03100100010b240c0142e0390000f8074543c001c050f102d101940740d00404c000c3c030400c0d20900d0f2061400759840410303600b6560000f503c46600406108006c0030100e00d80b50a100a5980703180081c3d074040c0403040304070703003a080a0765039001004c4501b20001034580101d440c10b120b4086ea401080083c00c02c60a02e00d40701d109413035500301d03134500004050f406e0000d12039a060324055000403a01424195105c100b4020069080c01802d82100e4042d9110b00188107504400140702c0d94000d80240c0d0010f940d0312503100088880d0400001c4d58 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 362270215 1250 362268965 362269001
    0x2100c06090804080708160603150f081506030d170c04090609050405390411030a06050102071d04020409020d05030d0b0f010813060903300c08010f18 66
    0x402c000710000200161619802110741066960303160b9a5038420414100b00400030f080030410005010343c02200341c805003070070700c05c128070748881040d00b000400758051484e940c00580108a80c844140d6100d800440c02e8000d802140070401010b0404507012400d40e001c1029100050810381114098074040d12603080103100c425038480401c001f40405132015a00360284a01c1a100124400100070102c13201d80c84280480551070f0400c094455040e4141d81c1050300c1da1503c22021a601004500c10002048001161414500020b24007001600110649078041c0007000f2101480008150300c00c2d030444011840c5d07107452001c039290f18800c5030010414440841ea649032070380640c0142c00c0c0d000c016900b0307950b054100340044981800944282c03200c00b00e44008400070a80d01e4100e10501c40c080d00305005840c1c941440b94941213000508160369034100200d400e590900750240c407042c112940746c000c400d94100b01c40d288059200e0322501080300142c0950515801603a0003080103000128440c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 362271465 1250 362270215 362270231
    0x90f01090f050d052109101b0207080d141303051c140f04060806030a02150409060f0f060507051207030302031e04050c0d020f090a090311061302100c06 67
    0x10180031140c071a401c071600e01466081c1401d10384104103a4403590420070003016031103140300320300c07102400c0500050140d010b00714841038501c01c54001e4600311a4501d00c00419406480f000034104075941d0451812500004041c40f4025804107901142200414010355103007144c40c1100d1030982250b01c010020b01461105518440003c620100c0b008000d0f00e58616842e0b02c41c1c59030816118950109200340000d00c010721155100c0c00da541d43c00700c4043c040b29220741460300065440d2b000c201c01601d4180c80081e041c0103c0c060740c0100d000170314840c3c2007580324a082000c1c2c0e141200050140000f04040440c1103030621808001000d81044040086980c0304080d0030024081d40c000ca40c00b00f100da08410b800d8044180b407000d02d52060b50458040c100d5243d944080000328000710740140d074070611444502215a89050500303008030200c14000809010500e03019104042c2d488503210381d90070000030084100e801000501070749504542c4064003290040d002d0301c0d400c00d00040a00407520308004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 362272715 1250 362271465 362271473
    0x5010806060102060705131818111018031704150201060501030b0d0213020d06050a0803030f06270c1b070906050a1404020705010902060d0504060c080103030f08090f0109 75
    0x5054081c801c00e03803c0d5080c541d076203c0150b41c140b14100d0040500c003c918000c0115a2032083c441d0a070411aa070003044c4000440c2c4058003509441e41c040d40d0800c010001c0c0320080c940001c06140460550600001c0554520382c440910841d40c4400b4081401e1010300d200d0341612038003254080d100c5140311203034a11190300c0003070080502d40180d0740840d01d00850031480380340c0700e11042d840c568001d11000c1c0302c103084003a120103500012070869819845070000304c1c0c0c5942e902c000c1405840701d4001151245401c0350300000880300030340361394010f04580d0541c00158a050380880c00091002e08a500c1c1610b410a50000501c181200d11800100c814220741c002400030a05c44126804188140302e401c0e160700820208410074860180541c404501d1407a25007450b402400c0614001d1b40009225030454020441543c8407812040c3c0d125503440c00c001c1001003c2c801d40116210b83d1901710781e658115500548000005c5e02c50314140604140040c0e421202000450800761080001703000501b500d02d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 362273965 1250 362272715 362272723
    0x207021c0506061e120f07060e090f07080c22030f031d0a1404140f040c09020405090621030a0203070302101a100201091704080607030b1011030706050108 68
    0x8001c5910780500d4001c0f481502d445000709000107050100c15105190540c1044842900c04084212038003c50b403401c04400010b2101c50001c01c0c3c50b49a00004070078040400c440c004000308005565098401403201702c582c40500d00303500041850040341d540159148541d925039020540c80c82c0f15803c900b011040010014005249d14481d03200d14100008580b01034800403d030700706450b00a00e54070002c109d80b542e0031400c041d80d503401420000e800511075034040070760f020840c1d245a8420006090000b0003c05801680041c007000b5021414a42010b000a01c4078601500c003074400c44554411943ca00620700320b046101c54800e0071a50f40f40000c00019449800014054015028004094520507400d010340d10f111800030700703584032000160081150014107401400110f6503504028000514440c4e0704d83c0002d50100000d64441e4606841a8a0500000c2840d402c040c1406421032154460040f107440664440c01d02d20340f1004004202c600d140a00000501190300f81000040c070298089 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 362275215 1250 362273965 362274019
    0x50607240c12060806220b0c0a0f031e0506120a051e0613060c051207090e01081f0b0402120408040306050117101a03010e1005150307090f020702 64
    0x284415503422200b01400b800c41d000d40c49401d0f825040f1500180b410700500340281091114840700d00b580c0003983d01c840b80c032007008550014603103400203540c50040e9004107021aa034201403a00703000768404c0030268100003121318003d1424039218408a0039980d1810348042460f800c54088694541a5040c082e680b038014000620021002ca4220b0740c0070400421002c1c4190050384a00c001e51005540c0d100007448100c0c2c43d40c0c200181400400c5065054503220750041a0b555610307507031a03040050f01455142c2c1a030180c0620360100042c0c6401800356004403082c1c1c848400006841065030022802034801c205148106065a104000c100300ca40ca001d802038a004d000c0804c00c580c3c0300d400702d2000301c0703204120003016800b5400f59401607819800c550540c0b68201b0040c1e1000c05040301003406c0d1540c038441c02169803c0351902e019059401c0c491190b000800c030b1151031182c4034080c04213449484a02a01c04819200c444101c100303410703030b01110b1040742d01030a500e40c00345c03811506007680324440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 362276465 1250 362275215 362275217
    0x80c010f0b0a08070e0901061d060112050105030a14070503120706061a0f0d0624030b041112100506070b0103030f0839190915020601050607240c 64
    0x881c4100890a240000d1015074200340002c00116040c0514544039076401041001c03a0b42d245c00c030108101d0051500c8500580700281e2078511424184009031240ca001108201880e103031000401044c2d50024068600c41d0308a9100c01d00120030003501c03804c1c00c00c15007200d40c041c410383c8200d000025140008290301d902403042003041030b442e441c051030b80004103007100036a0b9200340450011060900004c0264070481000040c6455a44011f904011a00c44614a0f200c1d030140001e40e180ba01344c05140400c10046600300710607030441d003030300c2e1281c000c024000540441501c00940200131201b2540c000d00702c02411603407105400d10300070324100001d020403000503001d4040c0c404c4a50007181411701801c01000c0135200b00881c1c0c0c420500072801034400c152403900030310444880703115100040a08588216903034910101044010307000f48000e90040010204462207074041c29030205109040da08103c0e82d030b90340c900b181e051030760801000400c1c0304079034088a0b40801030403007103521861076000d503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 362277715 1250 362276465 362276471
    0x22030e030115170f0304050a051c0c0b0a03051609090e0c13061a07080409050717090304140d020306040303150f06032c0d1b080c0a02010e0307140609010903080c010f 73
    0x746010a0311381c002c3d4891a900501c80b40c0050040d4604019403140b460900080c84561000940b18030b034506114cc0d11901c03006030005041401075600d80a0a80d0003102040d1401005c0c4036904e0040000c0c1d120310132250350650b11625800b02c4c810911800118400050030740c1d62110000c050302004083c0340c4226201c150000795a901e0f05200c0b1026144100d1300005000d04051400c9019009440010050004c1007150304151240c02c40d400480c50081c1e51541c025a100c03030500d0035813444000058000f521400c00341d100c1c0001a44c000640c10741c0540c0c9032602240f89501003c060421129541212414074451032000c40e000313034580e014440b8a00c0c42103214014803045000300d943c05c04980a03c510a400c030003150380c107181c059181c82c411007591800d03580c040121034075241d50940240402c01c045401c01d000000070356030b0201c0340300603180007200540740080c50140c0b50201c003480d60700320b03c0c000c00000c2180a800d038004c08500c8000e68200683c0da5a89407003000b114020004074000341c44c6070345 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 362278965 1250 362277715 362277733
    0x1150e0c0c1c05120f0709060f090603090c0305011508100603050c0f01030b1201140c03090c040504110a0b04170606090f06030a0f11010f050a02190204230a0522030e03011517 77
    0x1311038091100b080309c0644031300c031540e41802d900301c0281c241c1007401d032101c4c95548000000100309204d4070b0b20300302e017001106440d0ba04010041d4141070700308840030070682c10180c041c40402d01c0403070300941c00310080b59072a40c0c0104410060703001e0200b01070120b40c482c80044115101c0001900000604183d0540e110f0050780ca07500e1031030060005450041151340300b651116010f041c0382d8006500f150003401d0760007044198500080b980361854000c600440800704080100c60700742000d580c1d00d070900c28007130011031600c4800701d024580001c00b0803c0c1c40c1c50710004a425610103110454880303401c1070030709002c0c00c41410a60049100400d00790b00280780340e100c0821081c8a40f060b2071080080398007400c3d55204180f1020716810b06900241c0e031140e550000804204000d000000510008200d001218540340c0500e00c101c3d10001c0071200701514450540103010003d00031006d045502d4206200c080a86a0210703005001000c03000010b8103000c04085141029281690640346048088550201d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 362280215 1250 362278965 362278967
    0x100e010e090d031401090c03270c0f0302091303050903010203040c08210414010e0301020714060f010503120a03020d0501060e0f0a0b1e0c01150e0c0c1c05120f070906 73
    0x261045082404041c4e800c0300501014466812000782c510b11340c5408503a540c9941841050f150090b00569425881002602c0c208440c03281da100007800c12100d28908645580c02040645800401c0031100b911854900c000f014094170980f03800040140007192280790901d40320f10001100c0c080e4011511401480300440c140e40416044280c80142c8501d05291803c0f4600440c40030802103603050240018002c029614248007500c42a80505020782641c48042c04090404d0b001800166942c01d0940040c4442d46000030b8181e12401c641c0301c890b565a0f10054110020700580400a002c103051000000d00103a10031302d00303403c0748000c48002d144003200d0070400c5000c02e0385103e911120002441100901c0941c40d810040381a03c03e40c5e4a460108a080c81703d085440700030301ea65040240607000e110401c40310203c141d00002d01c4900782d25003451001d08640d50130a00c4406090140b01c103800b10109807050042e0b400000c840310071824030b410407210f810304810003142c174000000c040801c000303011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 362281465 1250 362280215 362280221
    0x5010612020f030a020d060507030e030c0a03142805220932040f05030f0c0601210605280203010302091006140304291602071a03100e010e090d03 64
    0x13140e0700820101d4045e5241e907410018000041c5401d042c191313a510380d00c018203018001491a800300ba40904400601c1d40340c09040058015180355134030400b0f00c940d0f0b03422020501f080e90f052002110032010168241d200f210350384542103960006201003210740d030301d42c09001608000d031440c00304144140010001100d0042d1882040042e8104241c0344150700b50003a9030781c19030000d0243d8280c284103a010344885203198481100218407440000f1440c142030000c0c094580585020030458041c2d001d030076030403801c002030388002402440e038440c042200d1015030b00c403140704103050218003072031520724100160094000f403009a0140b6401c0700051020401842c4120a617180c03501c44007800c1558000311646c2c3d070130040c021224042c01c2d0f03170403d1008942a5229450092804a601041c5400c85240d034040c044400031506540c046030b01440303100080092041c000c404800044c0e120758550054161240266204400303050719540049205800011654030400c142e008076807040604000407411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 362282715 1250 362281465 362281483
    0x70801020f0f13050d0506010303080609103503130e01270f020d050105030d021c0c02061209010b0a0b09010804030c0503070507060807110111070206070c0305010612020f03 76
    0x300c000d0420039100c40d820042c0c0508403d40c1c10103081224103442c0c8010404c603911114094072164002e5004008241d1f00c41f40040d4007201c20b8a444101d42040c1403009a0400c9501811040780424400c84bc40d00410248000032058060340c40f5086410980b0700030b03100d6001181c0310811010118004c43c103580d105040300d0484c0d21030540705c0e1800d1001c1008030410902e20105150f070544071080030710646054000b91100064544000465524140825242c00284150207040d90044604480200b0110b4880f6a400700c00e800e018002280510000740d5510502840c0b041c9403003100705001103170230705500c0680d01ca10291200c0f814142c0302c001100d0306010b0395408600140c01c0c240080d0000b44610000f03070ba0359226a00322400c0036803a0707640700d0800316540c0102c0d00145021080002555000e060003c010041c1002048030740148038007050341d44181c440190003094000f40a030304005c03c2802c00b5008541000003040090703140e001c20007841022640c01c0c0d00c183d0b041001c9a0041c5808654060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 362283965 1250 362282715 362282737
    0x1807031505030313060e061b03030105010e09061003480912030e011b032a02030a020918030a02010e07212a061101150803030718050d080c07080102 65
    0x10170715086040302c8a411044246802c2101404001c4080041900e00c2e1114410381000d143c4a60404c0c00043c403011356014100d101c0c100701014000f140c0c545080c0100511007501d000704032020254110382002d28009224102d01401c00b04487c001103080104131400d241401c13500b10540741c01101140d8403441409505186a11a02540006030041290b040c0b1b584d41810650081c494040341d01c5860b000f0040190045400a00d900c9486078010780401100c42200e00300c0714441c1c1c03040d0003103030741c0b404880002030003a803840d00460400c460703c05102e003419142c90112551107003003900003806019403543c07100e0306124160b40450a0021101000b00d03017440b0a10403d0794043c03c1c0c07102c07404503088041203600c00281e0100c80c80d61503001000800580720340d4560356180c00d240400c0908590032000f00e0307004200351a905106880000c000c580d080700700d5103050b8a03000001048042c032600d05500056001525500d00d40c04c01440001a203e081440710586a255695032000303400d07803140800c065 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 362285215 1250 362283965 362283997
    0x3170a05190207240905060f0d0f0f02030108070e01081f050402040b0907031d1207030f030b03152512020a02150703140903040308030a02070218070315050303 70
    0x8105a121044480100c80e40c1c4101c0744015500c03010300d604c0180503650702030348401181c0003815107508800c07290700514054884601d8691034400c1c041d018013070440051080c5441e1010400e1100b016041242c0e00d03904802c0c115540c0d42e4a1500341e41c2e4085a105680b541000c5200002c0c01c00d00114148070301d2466180242c10048140342c290004000080080742c1c00355481c00015140c1d1504640f0610440705620001070030b003c8642c007280900b140340740318421503115802401005180d41c0a40c0da0459060414850003058004150041c0c03503407080890309803181c003500010412400503042d01030b2030a07144442c0382003500440d04160300401055000440c3d043e00c00500c0780d45842d070042480c81c000b0710544d629a0300400c0c0607081000151189400240c5504048000c0303201211441d80081c1900b004520302440d6603190b0007207000080261400a6010a09034290b440f000380500c11009800700340145031034a110050001e181259282c0d131040500f19000c030380c030300b0000b003103e030701d1650f0403144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 362286465 1250 362285215 362285227
    0xf04030c060305090d0c031206060f020f010b0d0602090112020c03030a0b06070c05100215010b0d110a0807031a06161509020303040b1317010902030606060301180c0e1002010603170a05 81
    0x54a044050b0706e402c804010605046418801451040700007815650740c90b034a440e640e0700402031400008060045603a4900340100d006a6180703016070100030703406800942c54003941c0006851000b25205c40d000080d00000d0100c0d544003002c00114400c070042c1d03204015254456060180e075010b02c020081509841032001c0c0040d150145084814510790310440e442580c00010703180d1074400a074001d141010002c075000d403030800b490154240004105121500346000c6d208000d20300103004c0c1c010360515a0f82c0520061144ca5014115a05103000d0051540e03136a81500c801d1041043c54410b41c2c0e1402c811003c01d20b0f0640d17500981061580040066041c14144140d0700080d41c08100040310304502c00e440003401800900a0075001103514000041300d04480c011b15003003100040c40e1600c60081007005114074141c0c41c410900b14080b600000401500800c02661038581c0305440c1a8003c2801c001e01910303d505411003003d6a105210391002040c0d0a00030100300c4c0071b03200300311012800a00c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 362287715 1250 362286465 362286467
    0x2010305061f030516050a05040b1c1103040b1014042c06091005060a1205010b04020315031c0c031b0807030503180703171309020f04030c060305090d 66
    0x10300d030004401072006003900b40807184400545450500500401d071641c04101c10241007510502103900341d030410f20715046941c80010214440c0340900030b6551004102890001c84042d000541e0303030501c19041240c0680101d10725002e070000c0710221001e41810300000c0102d854405140112400440c2091001d4880020440903109941d49130b0038074030f102c001c4110702080c904400d0381502d2102c005800b881c20802501030509145540c1041018144001d000c1251120313901201100d05510308211645400e26000e0b0150050101d902d034094004400c1c40081c01d41820f50909011088040f42d0490302002d10f820740416940f90040003142c5548100c1020900800c103020041c0b8013580001d1200300c0c42da8841d9810341102c80154001180031040007260243c1c4580d03107800703060f0180149000340c2707584d840c95103003050303801c0c2200203a102048404955900d9142030010b030011940a54a40c40711780c2c220b900c00e40040c403050f00c9551000c07900280ca1402031007810b02580c004405484110a0610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 362288965 1250 362287715 362287721
    0x604090f0e010e0d140903060a0605100e0906060a02100f0c020c0301051003020d0203210304020405010509090705010f0e03060103290c0702091803070f03030501060212041a0403050f010b01030f0e0a020103 90
    0x1817240020904008102950380c090160b24855450000f000034620b003418144501e1000c0749804405000b0030301e03150240f5030f0300d00b04859440f007412a1303440e43e00c0e03605080407030501440f10391214009040c0036640c1e00bc041c0d135400041d00b00030590308030b50a200d6004101400d0380c2d410f036401c0a076038001c8a0f0920144c1020b0342600c800078006021580c2c03c80e00d0312544000000705a007402c034072407000b105010461509000380b40c01403004494609843c1000c3e4107050b01c0b240307148901d0b410701001407050400d56002e600d1481c0b0b03645005003503820703e696078280394608020340c14400040c2480e403040700c104c4441c4000164003440003c22180c2c00e00d501c6600748880d1040190900f0340c0015181c016091000c400c2004140d0588030b1040443d40e03480616010f425110103802130015504006e0008540014203400e0b902210550f240b8002d1140030448083c040744207981029196000340015162220300540002911100a1340d04003c0725518241581c04c44007852080000342d00304a604502641c0309030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 362290215 1250 362288965 362288987
    0xa0b060603130209010905040c05300127140304060c030c06330801020412060f1d07080708070b09040b0f120a02010e03030309060103031803020604090f0e010e0d 71
    0x2e11109040b02243c00041260030309034003a00302c868a0702c0070002006036141d090002814103458510b41c0b072843c0140703000c06640300002d51034446140c600700d0381d03207040942254040e0320303010b500d1120125a80102102c2e820218900f580c000c12010414104c2c00c000108513030440c2c00c07590700c940582c03075950780894090342c6000c420b1754040e840c0c01c00303840700f9548007102a41c0e218003d01d0241c04076850001c84440b440c42a0b000251726441840204494616500040205580301d100002c8900701d005240300180400ca040c1c0880e41020b4142060440c4000754503001d8641601c1260354041c0e541c0c0c0016500c009134007a8040d4504140592102410203811004030310b1402040c5c980f4103094a800b241e206445d501c0c0c4032200394018ac0d043d00c290b503000a61003406030b2007503014514600d403040b9869603031001844000c040082d0a4107404a42e1403410a45025547c010b00d280e603515520f1100d40094182c14241603006890444000080c0750140715034840c40e030036280600509402040241c40c010208 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 362291465 1250 362290215 362290231
    0x60a14010f0c05070e011403060c09120a060204030b2215050703142805040c12080c010e0a021c0201020a14031e030106030c1403040f0f02060c0a0209090a0b060603 72
    0x10071095400283d0a008010180206240001c115032402802440101030000c1c154003a801076014409000084012070f1003230b54090340c0d5610310003403060b0701615001005401400303861000c2404010404030075481406805001d940c2200c000501119410040c18030034010621030785200b15510704c0d80e00f6040a6440503841c10009004005640c1c0c0400b440c3e030440e2040100e14030409a80301080b0f00c803031000c207001e00184041110340b909659400038101d032806071101104101c141601082003140840c1e55441180c1d000b4001100203030403042e03464464407422842183c240400d0900c0e0424507013610200d03a0140d00a14841803075480700c4a032a040c1c605051245c1c08200041e04003e01c0c00c0034016041c102c5080707010303a0fa601d000402403c45188100c0b100402400031000703a9030740040c0043d03a40258110f581e002c500720003864660b4021105900c0250800408200744c00901408941088402c0c02030341c00307a0441d40c03610a0305031909008103008060328117842c01314259080c2400516482490 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 362292715 1250 362291465 362291477
    0x5040204061e0e0730110406030f0f0209061902010608070f0305010f05040c030809010207050901030f03020705060a1b05030f03010807060212040b070201030b04061a04050306060a14010f 82
    0x680000541c124a01188180d040394001003c02110440e410080e0380404145091030100c80c01400103c000b1480c0b0709940118541d00c0d0b0007a0761841d02c0c0d400342e0035080d00c50320b079683e03030b69030740c02d0b0203809090f18003183c003a0b6618140c01d103800600c2900071280e003810000c3c803152905558144564404980e44180d80440d9030301da2020035074510030407000020b424603400b4814068518903180742511010b60103000480e00b440240070004240b804440141c035400f16486454485c4000102d150400781d600191307201d050305000009100c10031198000309402582550a0252160301380302c002d2080041c140300080c86003c01c00c402080310f010350440342e4851300a403841d140f29080c400380590400e0f00203c03410f0300144010800346404001c00004480c0e1040401e051074540340388405030340942c0a02130305250b04e825110409070ba0300ea0001014100d500c00d0303000301605401f4114101e17080303030151500900c2501c003c1943c5241c03804106003190700b444112041c0c245240c004450b00c0075808640ca00b8401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 362293965 1250 362292715 362292719
    0x150105190906060518181303050f0307050405030c030a020f0409050a05030a020c09150d03032c03030a0f02041a0714070e0f070c05070501030b0307170c0a080f0607030504020406 78
    0x200c0b40920310040c0340907038078503840b10302480e24624400407116055102d0654449858407416220f400964488500c42d0a01d41541a605013940c9038454201e0a4142c0c0400108010076103403c0405030054401c1a021103070440f0f04481456036030814100c020f54002a12507813032000d803905030050030506100314240d03402948160703584d528540200030141e0141c1c10882d034040042c2030002d452640510840c8041c107103000110081289201c024102400305a160038406051001c01610451503e11090314070818148190700d05031260801c2c3d480a4410b420003000410101c03070b9000340d5096072001107500c258580e03c0c01851682e940544c5080791207070150300140750b058030140180c10040840103000440c5241180d1442e00c0b0b80030040060003401410401440807440009662068075800e007400103c200b542c1c0300091170159603620409401c161480140c440d040041081c14080c181910300b101c440341c480c507070301c0e481e2802140050300315403101d400942c021313100707801440e0040c2c000390000034555 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 362295215 1250 362293965 362293979
    0x1409130f02040b0711090702030403031407020a0305162402033009010f05330a0b0d020414150304030c0602120106020604051002031314030c1e070815010519 69
    0x500030080176503d186290001035598180050200d92041c11480558070b07250440d500941820301c01040054601401f09940c1304545030306403c1005140c1010071148c0510707000031001c82c0c0ca8550701881844100d9141c0e00900290407605684c10180e0b20b80245081112000e2409206d44103ca1903402001602115805210400303c140340542c040f9800420200741000308501901c00c09008140080704107070075207440000100591200080d41c4842c20344c040003030000200b8a10b01e40d00090540040010780081e83d0003254001c1c0700710f40041c0b404140720303540081008840808860752500c144020800030300045d1281014048003880b480d401400d081c4191000e103000042600041c01503444131040c042071103000c00c030745084010f9038039042d407640c034002e40d40303d0051100050050200006a4000800740400e10a85101340c1c0705c0c200326915540c100126481c00e01810404600318041c81c000400e03050b2000c03540004010038502c5c0214641d2800c000c0c040028100380030047c0040015001003904 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 362296465 1250 362295215 362295217
    0x60809010f02160c050105040b070b06030a1407030b06060307051902030c031b0618030a030c050f07120f020d0e010503070210050a0225020f01050a0c1703071409130f02040b 76
    0x6100c000e0f0010280d914a460210014110390b00918140181440200700d07070090310084030304851703004542400907194840481d160258000c40101070344000b88014200e07001c00034910044038007a0141004507190141401101e101c195009000240104603c06241c0300550f070b0003688140c41c0c411a07242404030a0300c14115005803400340384104160780102d5206004221450300300b64002c80c070541090302d951903a5903d20410003003005140d107815040354094045d005880000c0703042c0e40c480d603680f005440c141d04007032485995140401c8421503030000d024030004a80c001010942c0361050b58450200c01510306400013441a800c41c8074440350854144002c4c0500d5001d5862102d003d03850312210000080b18814010701c9030720044038031072000d02590f20382e524007090120030b080103640c0d0500500f044400b000c283c040500900740c0d0362411083c078260180154440c15041d80c80078400315070b00403007440c0c030322036216035503405404034500040c400381c4c0340d000f4194410f40c3d1500520f059a04e031038032105 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 362297715 1250 362296465 362296477
    0x71a0618071707050c0a14010f0504140d0503070206041e120206160c021318050303090303010305010c0825030e071e050a030206030c0c070306020f070c0504060807060809010f02 78
    0xc1c11240c64800030300b104442540d0004007a04295043c00e211103909952040088009001c00444924001d01c482081d881452242900d100070f11440c505801d045a44100030031114140388500844409070900c19400c0da0300907442640640b01030745541e141d4040b170544004030f41c14400e55401d240e0001510000c984024009560050310580c0340500c1202807486d0800e190105200240c1640c00040c0d03207601100145101c90840002c03070036811520260186140240105144000001d01c42e11460000285040b240308900038425450051001c981d807040543e03080d100c0e5208002d03044403d00a1a04009103030b140d51400054900440031401c0c42c050055004540c0d504c011145050214411310544003d010103a0300301c7d04803031030755010810070310000302000508000810380720088e040c180010401590420310654580e4201c1d000f0304401c0c0c0c03100000307d40310a006c00300000c8c41d040c00e000380340407280208003408142d4680720080c0c8000d100184900020f540c0c45000f07156102862015001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 362298965 1250 362297715 362297717
    0x60a05090c090312030f0a11041208130801110304061113060302070302150709030203100905071a04050d060501091a090117070e010b0c16050915060903070603020c0d0302071a061807 80
    0x200714203180351110112121400413000458040106200014018014ae410a60301c0340250b517640840c0d005440245c861600f0804480d400c0280081000f007140e00558002d50040700204400f481040301d4076039038496a400b81040440341340003000780350700035409001214020b0050b985845c80344902420ba0307000481d80c2c500405d099000c00c0c010350a00304801031201c1c016000130841103204e03480b030f196144503500c24403407056500742107619031502c254182c400804001c0c0440300c1240e03680c6050800740009016040c10146840f5a0300b110181d0101340307030028200900442c010764200034100e20f00084118012580d440356000c0055040140d510040c024030403013250710b86038141030070168104980c58544030440214200701307100c035680d403004a42d0481482445041c20070024000320b0128029450981da00d401440c030001030741909600202110001c82080c1d030568445d120707003502203000e04030020380b840e11002010355851142608068005000070844003d00000400700d00700580f0881d9800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 362300215 1250 362298965 362298991
    0x1f03111c23010e0f0309151603080a050c130302040c0903050307080901021c080f070c0506070e150f03010b09150412050c011d090a06080102041409060a05090c09031203 74
    0x303000716020311030440501c40d841d01900140d00881c0800d944c80c02030110540c42140c2c480030711011490004101d400e41c5654107240d41d1610014107015107440421214035800c1c40c01e2000103045044a5001c44c2da403071101c10254500241560240801003100d584481c0500207551008408a40100040c6c060341d440340d45026a0340e54034000080c2014604004a03010f101603602d440001500107002d990310800003000a05d0070780d1410030869521602e40c50150480c020b90083c400603940c4513403c00d607101825104001e00300044036820002e8803400e44a4844010240010b0240c075401d42c0050100c150010a01b000042e80b9004841141d801076000030380407001c6502050800c22305122983e8548000d00300000c1c24000d42451020019903100c2041c4526000c40c001145140303517034030203800750107800000c5403a552921800e07017100c41076500301c0e803140118000142e194540f02c0c0d80001583c5010308244643d840c1c01c442c3d412036801c8070b5200350b41340c010700e421b8142c11a4070b40090341c401d031001070f018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 362301465 1250 362300215 362300273
    0x3030f09031e0706210c0e120303011512060512100b03031615060320120609120d1107031d030109120f09030206030108061f03111c 58
    0x2514103480340101001c0e030198011801c9061001007024021280103040c1000e0017441e0039401c0f03440c16101030004036018a0190546a040e9102114060f2a03000b5220030b01d40d41d01c03854940760b8a001c01d00c2200110b10044050007096031203070300030b080d030f00450390000b140c090f8076440041c421606200002202d039209100743d005194143c0111660340d0401e8015614043c505a01440c0d4400c041c80e000c1c140098685661201c41103e9200100450700220380c403085041b6081403100f012003007a03206d032003140c444440016031000841d00341d001c0e01c038410080c1401c034100c45908086400003250140010358605807030209800fa00024410350344290764205800c1c01e0070000000f00c2c1c0440341820b02a80c1345c140e0b9200040c2000c4500c984030312040c10000d08007500707900c00b1074442100b07400080d080100440001040d820008120303002c0d40141c03d0002c04010301c000c0070601c0b0202403102904516100d905038001e070030300083da030840d018510011b960803034160715203013541c48021a500b01000d01c40111 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 362302715 1250 362301465 362301469
    0x9050d030807082a18090106090503011a0f0f0d1203021e0705060f09100e060601031803050301060c150504051b010306030308011412120301080607110a06050a02040503030f09 77
    0x3110381c091400b00340070362403018442250007004001281000303641e000052040d5071034000c81c5c1811004100510725211503031600001450310704103118082c0250300749210710f0611a003e00981845a0019003005a101c0c9600104417182c0055540070740c12131135034119140071440a00301c45c0961803403520b0142c4e13070341103215440904542c851840728440e80248141c00004001103052030b0014000d02200d00162101c4d10102e080c0b80f44005038040b00c41c034000c2c00c40d000070004600d480c81050309803030401140e00da07016118900184030360000c0c00500204010b100d40340c05047c04207000b50181c87d20100b509c3c0440c100303000712082540c043d281c55104020484c003030312445900a5808000703280070b0040c00d02c2d5603006050b802c01805110751000070f400035500310385c4580c8a90b41c40d03003000c04102c0e40041c61100c03240140e41d000b800f800e002030103100b0002e102140140c0107007481203140300081003440101c0d180d140040202505140000d0303020400010541c0d400c0014041581c01b40798660742d622003a80c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 362303965 1250 362302715 362302727
    0x5010501031703040b070e040e010c0815030f1515040c0503040204051807090e0f030703051803030324030724030e01091a0403020c0402040b03041e080d09020109050d030807 76
    0x6200b50441c0001c2041200107a0200c0c1ca440d0440e2075800d00d041c0e02d002c2d101c0041c01522105519034046c1d842c0241e100c1c0b000d540156114041c006418498181354000b50a0680382e03848603800250030b501499110031b1035a41d4000c985d41c040300d201c1000140e50b84800011b015642e0032000e007000200c000c8244015460280300e0705070403920a40e80c0302c8280200c0182541c6500c040d00c03490a810b552034201d000300b404d081c4045100c0c415290282c07983d40d4007518025046420280e0030f582115080d1400200900f00001281d000d00050311080d2803040d00140f000c0781c44140e49000d25014064440f001420151410700a008482c0402c0407000705050440020101c4005024665032030b8185410362000c50584449045001400311002c10503503914182a40b9017580810f080e5081440041c0c00100740e0010005140101d1141260b001f6500720f1505040391b00b5640d4001800c1841c0800000c84041d02690161a9079481810003a20080da10000104290f2550750b00b50040345e0341d00c3c20000540e41c401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 362305215 1250 362303965 362303993
    0xb061e0c0a110907020703050c010f0302040e0f100915090203130501050906061914091b0f09040606080403090b090a0e0f0901151a03070504030f111504030506161b0501050103 77
    0x44014640700d403654423440c0d81c3c0d04017005a0781c10301025a40340103074140b081e01218054a50350a60514034200b0500c482042c0d60100c8088111003e0320f240411210f05601407184d0b40442e100380d070401c2d1410080310400030340c005044805c52400c100c42c400d00049003800b030385100f580218003600725480c2940620801030520207003401d103c0a200420b1084d08400b10103070301001c0d030640d8040210742c0c40b58400d5568507070362400348210b05008600084115030180091800602c1550203100c0141c3d24803083c1c0f00300b1403d0760020042480301400344151044003020b800804002411001c240c1ea44501304180c00106450a0b070350000b5130810416801c00900404040040d644000c060075840c018112009091440c058907038080c0000100301024440c002380c4000e503412005203249000b061501e01c8d94605107074101070140700d5943c0f482c1c0503129000c2c1a50200c3e40c0143c00345c01c40da641c5081d0000c4a41c86840d8140a0100081191500441400783d001d0b04511440000405504506103030540c0b05c041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 362306465 1250 362305215 362305217
    0x15024801020a09091104050a1e0f06021f0b0a09020414060a05030a02071b1503050105061e0705033901020316030b0f0402030a0f050a0b061e0c0a110907 67
    0x1040364410040c3d005007144221a12000e00203100e900240901103280300315440180d10011815001c6a8048200c40d26032402e00001800030ba139030f607925050111210144141009071304481105500c034803001001c002d000d40d21031000204903c3c1440010520b502d030f600448182c03540070a0901015400d507000321248041202d64500f00896001d00a01c980320041000a149802003407074000c00542444007066810b4548825060a8a40c1c22000e203146c500b98480c3c00080c10000001001e0074250115000003883e294207801c1c00e501d070b0510382e003580e2001908039001d110420181c04207520680c8d406100843c6418180b040c1c00c01400c0c40c0e510341c40d41c8100700c96a40d20400920060760032500386180d641a40d402c0119959002d0700008210000041d03005030014000010001139917034541c4110814009841c0411035620303a1015402200c20780711000e80c001008000841418804550310840d01c0c001400d45407400c5040c1001c1c0303050020001c1c0455042c40040c4003480f45142246082c0d40c08201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 362307715 1250 362306465 362306467
    0x201020f1b13090213020703120c080a1d1606090605090a030f0201120c08010915080604170c01090c030303050105092a160c0602070b071502480102 65
    0xd501084041260381c030307514031406540303200c44403101d120740000c258260010940d1481142106414010307521044007140022580100743d0001d2a080c815403c0b903024075031303c8002a589210040c801000f10514000081d00c54010012007140704100c501d402011001c458031840b464140c000e050189140c0120041c440148050707505034403008407080859401100d09152203d840c001a1120700a21000000803801d10b0241c0b1a26604400c41c1d034121050f1000030065031f03078140b494512100181c05461036941205c000300b0040344542c00c4040160580d1140946400c0190107481d0031607403562800c89005281030402c1041c160140300e0b05005100c16250b035006858420f01c07100507052503100b4828055601404030041018002c10f0720503e1540c0801c0744a104054102003141c81b0b400d11842c00188907003400491100789100944203080e6102d203070700545081c0f6000c11000783d00464901000701440054500f0410006590f298848000c0031064208220403489a6174074982000c203918240c1c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 362308965 1250 362307715 362307733
    0x200403061104140f013501050103090312020706060b0d05010806060a06020d210e0c090106050c0706080601021219021606170606091f0e0a030222061509030201020f 72
    0x60201d0f40d00c004482100c10b5426282c203000161400d040c500d2016444040031021005504845005030000c1640d200305a1101c2e80da5074011400e03607071100d8004000402403a1000b03031080c0305401504010340700c0c2030302051050b180c01c40c01071590082004c0c10500342d100e40c01080303808c100b480455000070b0250340700c0c00d030300741007400103541c809141c0c0726139040000290b0803100b105a1402c001840b03190001c42400034a80c2c09050300e59400a07072046d18440d65880e0b00020303420740a40704440940c1c544001908c121850040183c44042c801018141076000380307040e01410800c00340007403000400003c1f19a182124544c0b000340382c100100030300010116840306c2030142c0d0783c01c00315800180b000348010a0701503484c01c011980c0d500482c5681d9411924459071103450110180b401040107507290358980000241d03100b000b508003120322020f5008400492115010f03498410a862444040b6401003030085d03480300c0c6000c0542c60b1904174800604813820500031582e0500120311034000e10802032092230 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 362310215 1250 362308965 362308979
    0x1807090c020d020f190b0a0e0a1505070c0b0402010f02120d020c0601151710080a03030e010c08071425080306011701030210272702072121020702040e150109020d200403061104 77
    0xa03000b3f44040c1c10b10030074000602000d4030800c100c0b409000790100c1a41c4558030102800d0103900654030011041c06200000301d84101c0300040c80114006c55a90350040080000800162000103811202c40350703c640c0020030f90030810081c8040c070610a6400040040b07115100600710b5400d440c070f0408125090701800500d6502454a6a091602ca498103541d010441c01e00c1980c50003d003500c00300072030007208400c14014502c0143d4450402a280c0a00000c54074a545005080900000754403820007000150741904c41c8200740d40740e0000031554025841c0781281c036241c941956000c40d03076801c101808080d81ea041242500e0003c0501c1d00258241065507413003401c100342c41402c001c824481c1c541ca08032203a105a0030b48030907080c2c48101c0c8800d400f010140c20082e43c00a001039010702d0408036801441c150002d201800d50105291442c416401c25102c1c402a500450160348000d4403101c0d00c00940d10410078400030b03100103100c1d0300e50307981c41c51070f10500fa24000c41c40010040d00610003000b0756 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 362311465 1250 362310215 362310233
    0xc031415011106152e080717010b191b060f020702131b02030702090a090f02090f0a0b010c080d11040503030d0504020f030a0b1807090c020d020f190b0a0e0a1505070c 73
    0x1015410400000e40c0e47c0f00742140c100042011584d00c1781c20301c60001030b411020070001c1c510003440d207940403046903400d0360540307080000080348800f8819020070030300442e6840d0300207400d014071200017510b003c0c0f00c3e030000f54001030b0440384c0815a5a03240355034030050405060007a81c00c40705001071030400d200c640001c0d580301d0000b054107010710385960329402040150940c1a02d4250300502c04142414040031001c40303040203c90300810546414202c2c019503000b03440c980b401542c020a44c80c07408803138041c0c0324003500d480303000c1600c001014407001c02c0c1a901480501055190410001441d1078540100260a031f1402c001a0007a04940302180102d8000c1c1c4500c0ea00115807484800d0f80201c0c1e07100c3d50300d4040141d0101202515101844030840c0d030100322848040d8440e421940e0402d03082d0f03402c2e900c42d101d042c1102c00c0001141c000000060b01d074106030340c2c07010300510000381c1d008200b4800c50504a851600301c9110300c0780400d40064003614418a5045200c0e032400c042c43c03100c682d030b401c068 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 362312715 1250 362311465 362311549
    0xe0a091d070b160c030b0907061107032109090c0e0a21080a020a06020a0809160b031503030d111e04030203030f0d230a0c03141501110615 61
    0xd181d01e00f03601c40f0900c51040007000007143c1c04203180c1840c1c602192140e440301258041c0d6000115182401104c1030710015802040da900141c400c400d074800250302d64a0f140703000d80350009020529400090f01c81044c4038000c0210940c4c0c503103500c0303c000c6000b00501d01c0d5064104001101e0100034003c406103050305c8440f1b1666200c08116603e55008809910300180040000d192900000355141c079264080642401070000504551480002c0c421030303507900101c5c1c0603e1800c0310f02031000646554410b40c0010300d0100180a0740c0c90105150920030030764494030003503450701c00005095840e6080c225040c82c843c00703d407103050b07091506560000b41c59118901d103140011201103454080a00c0c1070b408441e18401011908212070502481c3e900500c00071113160f0140d0340313041c0101c55060302034006c0c18000f402e41c00803074541d070755150318800a400f00e034041c060422138800c0800d003541c08100441c1b130269040103003504421440501300311006001d0940d16003d0600b081c01148401d200040d104c1d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 362313965 1250 362312715 362312737
    0x31b030506010512150a0b0928090203040b060f1906080c09060304031e02030702010e0d08070515041e020117040602090303070b1008010513030f0e0a091d070b 70
    0x603003a1541c2004036190700926045000c13550311002444141075222942501500042d2a80d150451b6120401b4156009429030030f0b411000b489140a0b0f940a4444107001080302143c0306031040381c60b20031600498004840494038804030006100300c80ca020010b0a410203000c56105556094141c01c50401f6400d9111b0300085c0300c01c0002080074041c00600341c68200d28043c10041d04d034501820014020b161100d4500a210815908540a14804403c5826030354060b1544642c182c1000103004e84007003450b0050b22506810301079040011820302c101e810001c0500541c4003541018140303440c0303d4590a04480c9010880071140e40180d8000700c01b91800c0030002040b05696441d414400c1c0688504090281c1c107020028583c4100220b160340389024030100651461480c4e1541045d034206d60081d00e15546040c0c0c00c041c2e200002e407049108000b800c50900d022001484c603170010400c07078840c4c0e4104850007a00c0700702c0003548014041d203c4648898203401004c08500d02a1030042500c200b0f00f9240c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 362315215 1250 362313965 362313971
    0x3070207090203190c0201050709050604080d1d061204050705010207210201090f290724060905010e09100c09120201030905060c04051002011b030b010e210c01031b03 73
    0x648544d20490350300112080030402403000d030080d40d030000d00034541250210081101d00d807000c2400d0030461306407020740320340a0042074040c0c103626058a51400012005c942d40110310100855525440c0c05001d5507040700509150506052410310300b82170854102c24110351010ba8100b000503125070716060f07010210689038000203035500040f1241d114503000741143d0380d840c22000424514100807a0490400034a481c0103200c100f00401480b0702c1860400307010441c05c4403100d400ba404a0651317035900d0b00c010800003052941d03482681d003a580246c0c0715a00001d68801000514081071140c0c0c040e580350500c1c20880380381820380c050704860700b40c0551003500b581000c1c50011139000382d101c0740344150480112182e516105103400500d40c4a801000e004130400981400014014090302c40408050b81e03c2e44204812854102d0090000030f20040c1040b105003000099601c40302048141d07106000d050f40d00180000440c2840c28030302d480c0c00b0341014079001101c0c0c2d90000303625007000440c2c410321f404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 362316465 1250 362315215 362315221
    0x8060f1e041e03120c1809150e0108010c11010e0d0f020f030c01050103030e03070e0a15030816020420030103020909070b19080c03060f0d02030106170c03070b03070207090203 77
    0xb02c68111002e2a44514490a0000000b410b81280304207210baa90130105000c400440300e03080b42d1040011242a401c0f103503400c010b00c8981d19580000c2d96054801c242d0218040c0c0e5010400041042a8410f220320b03503403104103500d003a038010040070140c0d61600c000d110704040c0d181440c2c5c0e603003010b420b03500401640381c60741d0a859200707004420345541540201d0783c0390080c108015000b0714082c40120040359004504410b20709010940c0c00442d04c0d03504d00c150070780ea0f846001d0805404852000c05006500c0780000c40014881340160201c62480720419108140354414070086401507100390b0306100460100c880c0c202d08d40d0049078107590741550b00b06440e40350009041d2030940182c00c100025a004504540c40e41080400d80c02d5820740c0d40e4545000d0740718895003080c640700c19900c0070b400c60804550f084041c106007203c4c0c0c070b00e1403010307000080c07566441c13800017125103582d0800c4126030082040041503103810002d00b00a0065030102500d103013040c440c044e5a1f04800d21400394015004000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 362317715 1250 362316465 362316473
    0x20906030402040504051002070c05030d08010f1e0e07020a11030f070302120f193003020c070e13061a0f0907020a1203050f160e010e0d0c08060108060f1e04 69
    0x2480030207d012585c01d6449822034500882041130a0003075502a201d048080020181320703140c480c0c1282d840c000c0c0740c00307030307074106010301e0804035045040f151450070302400000c0f00c11450036200d1103610241d020300000780c80303450010140c4645046280c40380d07010b504e800406910100d612412207170304035042c21220b00c02070040703402d00c0c5020312440c40758055184105403640d81ea9480d0300d6802e125400d40004201e0f00301800c00c242c1c826881200b06c0b00110005d44071142c0c0241e00070480c80103903078102e03101c140d40c9184082503400c1c2114846c110ba071141f503802c010844075005d8080c0b55040c013000c920409a8207804251082d108059440c406c0c50410b001c52003140c000c0c0310129525070800741c3e0b4a5a089540070140c0540810b031031080c4c80041c000001403041c401e50305a00341c42002999009544101c01d001140c42c0040302c0c0815501c840b0395032207000043c000303600313950040a02c0f0b40074040c551315101009050800080082000190b00b90400800c8420110790749070304c4070740d141040341075215810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 362318965 1250 362317715 362317723
    0x60132070c03080403060b100206040f120c0c06091409010b0a0c170f18030a020102060a15050603100501030510030308060607080c16090617100e03161505060402090603040204050405 80
    0x1201820f0700000060100c2130101c2600308256600c016504134040e51040700c07040740c3c0c07028110b070060306403085006110300003500d552542c00c50741000d103820407441200e83c0700c50385100b0082d840740000c0744642c2420440320034241d60f0388660100803540c2e031500c0d615004111049205454044040150304400c0f4810004003151075002c41713070080d00035622001503c41c0042c0b80c0e844080d600442409071440c0070074502e00001c0051406d541a80038000303d0f150448141c01a150010285070500e504a00200b04c644588010f035210782c003103c1980c4410361801c0005801c0b540050655070100d8005039081c40030a402000743c03038112034180c5800343d07614460304140303c0340d01a064921071640501103450411041c140c2605080c0c91025504004070b665404003c0f504080d04400c0c0400740d00002941807800903070f6844040c50a0a40090b40e2900d00705046d4000f00301e001480442d00d40400c03000c00c0754808114841c2c5540500c06407011440c21480000240d814000200000e101d540c981c00001c3c2049403c1c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 362320215 1250 362318965 362318969
    0xb0c1c02090411040909020913050a020405190c0203030414070e220b01031104150510052503050a09090b06091201090b0907080124260312060132070c 66
    0x6035284c9840d22100c0c010080e000ca003106038818184080400c184c803010103110700c0381642c440010410a0125030911014000082c00190700b4194880c00900100740c03400b07564950010343d4007555680c501450251b810044480e000085507100081c10301200c040c01441540142d140410b0440f0040d80c01c1d020120400701d007800503c00f6140c9000002041052011940e01c2d00d42101c0c05c0c400d0b02c0c0113115070031001380280319440c3c0c000100c114000009000e0300060406869080784c0f4400702d400202a51500c0316a00b004500190340051003000980c3d0012001001d0311200d01c007484410005800034243c1c0c0981104107108032540705800038600030035400711889030341c0000c1c102400d161084009440d1542485942c02d41e5080440060000d1503200c04c103450210060341d404035003801c201c940205041100005542022a110908582c03030080000d400d0322448400444401c0ca0624001400c04010116001240a0314030b450315400009181c4000004000302c0c021703403107145a0500f03010316450342d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 362321465 1250 362320215 362320241
    0x110d1401020f040303121e0b031905030901080106030c050d02030c2214060708030c0a0c05030f040302011704020d11040f06180c08130305070807020910030b0c1c020904 74
    0x241c4480e08032402400f41040301e000b84c458148030188122510195042084e0740728403252001d03011100819154008840340401030204d034030548030f0b602c0844811040440c2030711140e00201d85d1030440e44c2d02601c00c84c0500720300d00e000d200c0100f1000d40038106000300c4030b160020035004000075074400d03800400d07035808a0142ca03002c680b18041c1043c401c000d442502903d50310708483c44402d510341c145142102d95196008060903c2c3d035841c80f800c030100e40c0005600c3c0d410005040b043c0c4c004204204042c1200c4200d103502581e8452462001500d8984d03e0403070940000e03903b00403c1301503910700401c4010302e40c0000401d00c403820f4020010740280030300140e00b03491a10f808004a0b90540b4807003200010300c901c1e002001401803401080c0c0381d459084036203800009050b240d10001a10610280c1000303441003910900b4590554001456054100d0303851000c500195010001c2c042885442c44e005104032900c21314008213410880c90604001107542005500010900d07a0f0303071a180d01c072009000700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 362322715 1250 362321465 362321467
    0x415110f032206090311060a180f05070e0106260f04110f1302030109110301081c020a020603010305060406060b0906180a030b0412080108011107120e03030a110609030403110d140102 80
    0x19142c0a001d541d20101803506d107214000000e901d842d40e911a2007415084036000490091480ea106240b400e00300e00c04a83d103004d203c1000860049040816020f0319440d208c0300d07442d003242c07925007210000d80705103d10f5800d482014060181c8900c40ca1076045034021201054a0302880c0c0407a00c0075114020854000021300079004040b19203601650585a10b810144551404800082c1d8240403e0040c61440e8004081a600590702c8400030a183d86e00c03401611a0b02d1503a4000032483d805c241d1065565800c0030b010001005018807600c0043d184070b44406090501190110f500e502036104a01041d50107414034440559503a000000110b502c01c0c440c001a01d414504144e90300102d01c3d503000030a14100c000310b56001c0c18000c118841c3d6045000d06d00b41480ca44400307229020740d0703a1103c00e01540c0450081992414001064842c4190702d41c00c021010fa1001c592804100a00d098400c0c6c1050005100041d149840642120030440303283ca5011070380d0600c4c50b4841c511900030001584 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 362323965 1250 362322715 362322731
    0x103110f18180f0d03240510030f0606030b010e01080114040207020a0e31200415030b1504020f03011a1b1f05040308070f05040506030415110f032206 66
    0x18000351800040c882958280414940341d14002c0c2c0e9811b00241c0030707180790350648052205003446803804080e9103440c40d000c200c15490703000783c4084031201d401c00d900090b241c0c04035818a50b081600030516040a182c1105a5032401012410604030006428030860300010214155a9000c4071300b0050903007410403807a542071030300040400d0a12203409840e10001c80398101c40c10200d40055446407034010080310b045030041c88903441c5809420691650290f5a00c0c0c98925040503014244050341c80741640d201f4904000441404540120141310b110314010070042a02300203450507281143e14001040301c02c1d0000c4031003119180540084000007498a6100d814110f000003007034080f0020a0100750200320910483e1b41c143c5104440c0680410108000700c0c54a6100f94400c1c10041040d1802074101a113031000500c1681c41900c00391411140d00712044000c07070981c0b190b20b841148c074214081c40c0241c803100020707003400b0003407400e2028044810211a00004101341801c0b4951041c01017107426 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 362325215 1250 362323965 362323993
    0x20409051e0103110118120303050906220803070201060e13060614060a0804110d21030c1409010c060518010b0a06230c0607080103110f1818 62
    0x424200c0358407198006011841012030441d20009050300c1c0c1028004034241c00c3c1c0001584c610107000e6035400019190340d00000d06140d66510307448a1840307541d0109460a10a04503468001e01400c4d655190704075000301140b041810158601856005900503120b503103c2c40140d00406180d0710bc858018096010007000030042024030040e10720503c2d041004c1915100ca10441000031000c01e50804010000d240d6400e014400c0e103940329105020401100340348401103581e80300e500c1e0044403103016680306507601c1c025201035030454030040c0c501044403040716540100310512030514851004800140b05466901c1201008005130304503505128500b070851044080c102c10302e80741c900551901d40c03000700d02d10304072000f1400c440f080d43c0c07070390101305908514511b00e9400380c4030206011800c0204502118050042c0c40c1305044640b1201c0d042d40c9107081490f151141844035911075400030062042d155649a0b051f4542904000d81d9881c5944012840d0481e18199106010610a00300404051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 362326465 1250 362325215 362325221
    0x191d0306102705071101061d01050f0d05030d06060311070c0e09010b150a0f030e1c030b100807170c030c0309101104060905030109020d020105070f0b13060c0519030c0e04020409 78
    0x482c5c0c9100003000b06554484824054500e2107800906603440349004200b01e14150748129200040203080d00348580207a918145980d0180b140084620f407035600400c0625090303c01c8541035400c0255040c5044513984d030700c003d19500c601a404081d118200810b4003280c0941c49014a5840079206100c2e00c40034000d100b01603040015080001000c100884820600c240901001e0105100060140f40d1906440700c15032100c216041c410565280090001c079038515240c0a010445a12051907900b08040001c02480324844411540c6003c501071081114425040301e50212000031040c1d225100c80071114101000e03134120b5040c02c0c0c1068001c840c030501801c01001155465100d0103002030342c079828140bd0340c0c076480f00658400c1100c461400503502650042030382d41c0c400c45241117100a640d807564a218400c0e2101e500c10808500c90804200341440b901c4041c8183e401e12900b40080d512450082160f0000c080d001c042d00c90010f01d805d41c9c090300312200b0b840b000904c21f5450710340700c452070002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 362327715 1250 362326465 362326487
    0x506010f230108190f020307090e0f0609060105190801060909090c0308090105070203101b0e0d02010c0c0b0a050c070b090123191d030610270507 64
    0x4225504000055010241c0822031060501c00404800811020006403810a001401407024000c241c01c07040060300144610151032089040043c1c0700d082c40f0200400640e0311b500200c160962401c10700100c40403403243c43d40d000008484a00b8180e030303503400490f01030148402c0c28020349840104400c002d40c02151003070580b0103d0b40c03040c0d0303556582c24100b030540709140c2000d8002c1c02000424000b05074000001e11f030000040c14818503202842c0c3c00b09240c0500c80203600c0c0500d80e01e0850307000698080401080c004003924103025103c0b06a4005045042c55102c02414850319119080420800150010051401c0312540d511840780f8030340944640c5c803040d50840079004880011800b04070310b00644045070410f0f0b4a440c4101505105420000006480140c541d8400d0110242d200c4100c2c90301d45003500d131641d50801031640765110800007024146000e100750040010401060081c0300c02a00315840846810b6100c13056182c040000040c1034a0a50b01900b000e0411500382d0700b01d019000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 362328965 1250 362327715 362327729
    0x6030f06010e0f060711120304060c11090613050a0f1b02070b0408060105010f050706020f041706070f05090d020a080d021005090319030216200a1805090f0307050601 73
    0x4414105001040f482d100c04100350382d80940c082c820003002c03071205e02a0031030050010f4030440303c101400c1c0444d842d5030400c1e4858000074028480c40c0040044580030144440e00580c0c6543c124188840007900f0000c0c540503c0780c606a489000540061458011001d03100f0010410011941408074034108400100324080162080e5080050100d002d28120b03011114401c014149503404c103801161489000c607000002c001046c8120f2020500520051084a17644030a403a40d407443c1c442d892144d500d003500d40c04070f40e030022420001c506801000038542600c082c50305543d944984000148800b440c40406500801c40303001c00724440200180390310f905c181c640c00710b07080020016455000d6503401c5840e01c28942040c4201079980481140030140390000e03060143c28643d0414507110346000000044c0c486901d0040580d9a0b0102100034241c00801030f252025a0b50411002c903040245220200c0100340e81c91000039080e07802800a2503500b1001416650b4500342414143c0ea2140c082c0207400c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 362330215 1250 362328965 362328977
    0x50c061c051f0812070b0606040e0a0605040609021305090705070609122d0509010c140d0e0a0b03010b09060405030a03030c030b04050402100c1106040f030b0105090118020706090206030f0601 84
    0x40345403c0f000800101c52442c00401d14a8418150f480c440340d02c4028203a103400074001d000c00301c0c900032a8030589208042c913000024100e85420108010b075403a6900c0200494810401803800d0b0004000d5501500d00c01d903440c05043c1c48030b8500303e07014860000094006132a00364030608000c1500d5440e183d9600d0740d0340d80c035025804080c55801384494001c1c59400c0d40c413a9044100080d004030040c1a1801050409620402940d2a0030404984070f4030483c80a0708400c01803c3e500c4d07004107000e00360060503619075440a040a1301045d01e8407060003501c242c0a4040341d10111036684d80d0455002e00b0020342981c0ea0115585009400792a0750350b41c0f0004030382041c010069905091103050311079500102032001c1b0406140041d94068400a41030782c410134a1304d07460301c1c07075100d900090004091560005014074618280001c0e00d000607000305108100400041040051491000014500d00c900c010399906540ca401002031905490007504000e0220800203038610010076903124400c03c0c2caa078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 362331465 1250 362330215 362330219
    0x30e030c040213092004170d02071a07050321010e130b0f070e03010c0e011202040806180705030106030b0406051b0d0e07050d0602040f060c050c061c051f 68
    0xd03801a002014a00641403100304000c40264011404803030b4001c0c00915641400d174030280c00c940c0140c020345014030380c0c032000c00c0d050300042101d48155845807010b48549030a0101e04070b05849618141d551020300840d501d000d104060080302c10101c5080c00c1d0008595807100818002c07042482a5128170b041180000d1021a0818000d40c600b60b00c00c2d07460304180e981d407180c3c1450030303805031a0508121050280d00401d860074401c200d4094443c0d2544007142005000041080415000c1042014014442008003820004d40c1c00c0c2c200e864000580300e1a4045551646030885a520155056003000030020130700c00400304042c0a10300410061040f5502c01e91024022080011030711845003003000b008440880a07481090408011820b44035190340d1500083c4d403007510014207507050307640000c04114032070040921030000c00701401c10300f10810041d2501c648400c9000c0d005401960300140c00001851620349260003014181c50400c40d40c02c08180c00621106198215917592002140c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 362332715 1250 362331465 362331469
    0x3010e0618010e0c040207030c020901090204051009083a2604020f0f0d0f05100c020604080d0203040303060803131e0b0403080d380108070c0627030e030c 68
    0x41c3c3d007020103804000707124004130321040c040203611440c4144c080000c0c0c183e031040160380e040e16a038000d1a02220143e03c032400c00b010090043d801926220038400ca50104104201001c2080d204800c0244009800c003410440c40340e40101c148404100b414210a1070000d0307642e04102c0d00c006403110950901e4400d405049011030882040c2c6010f54071062611341c2205c0341c0740c03100116048000140280c00c4c031118a82e22922245081801110f0b683c0201d40e00403a00400d502c10381d40b012240344001e00060400e621103005911500503140070050300007000030145802313500a80b00609002c412640e4800e98805405c20a03d218040d0752400400042c0e000c6100150824000030b550321b680b2400e01e041c0c55035845000c1c0340d11901c000e200458940024403051882c03142000b017004800c107201e20703040c0c10a2105481103002c1c02d030304505201d802c10600580d1a48900b210103803682c04500000d01c0e1307005404818015503e0000ea4201c1100c8000000070158070001d54908000103608540c986503424003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 362333965 1250 362332715 362332721
    0x105040204030305090f0301020d0905011d0a020108010b07020402090d05031905030702031c1404031731020409080c030d0506030a17070c030c030c210b071d03010e061801 75
    0x40b02900003402804018102e10b4105025036002030001c00052410102c0e010030026156001d1081e2402d9640b148034503012101c000103450703200c48c25005440b21550a40c006404402c060203807800c5004040380320011074403141e04844101400800e6039103000c800740f8042d56281e12440244680e03141501858400301e0084003030300e010741d400f90041c50030980e01041c140c000058042040c21105c4d01d410b0100488406022400d016a00947d500120010401100b6010400250800b440d0304047c11000840818030591001c0f10a07403e2501145106180001400f0303140c0c51401400c495400980c100028900200a0010f45900311041c0200c0d07480d01c0415450b001c0e6040041c0c001d0001d102c030108819100d40c01024814480c2289010072038594950700f41309401c9400c103c40b20081c42c41c0c1403001c13250510203010b1180510410100503071050380c2c0c0d52108a070240014080c803900c06440c4a40a500c00800d01030910003070001c1180c8600c084281d9590f070420b0320507031100e502101c01c0700400030042c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 362335215 1250 362333965 362333969
    0xe0312100806040c2321030712030b120307170702031005270f0715022803120c1409030106050d0501020703030605031606200a030f020d05070f060b031608060f0105040204 75
    0x6d103005850300c45103604e00c407013400606803a209404104000000107040c030120b498003d84541d0001410360010052020500383e00c0f440c0f000c694001c0c031201d40080d50b604403081c1001c140406180d1281c005d80b0100c1d281844600e42c41803617500b001c040118040c0b00d018109440e80032494290004490141d5041c4c0340c407001c2211401c1504440c6050103201c101d402100703003180e43d510446032000164100e00410342c455858600c2e03480b90351890001450790099580c224480c4040c1c0030440c884070420098603410a15480e500c100f580890071140c155020740c0071800901000c0d1a01c20710071402e1412078001e5100c800101d0100c0e25260020842d41800036403004c00c1140c001e4541846400c0540c15034055200944ca102c11000180044403801024095940c20900c00e0f102c82100200100c03020b800c05044040c3c01040003002d010300004507100d00340228000d5005480080c468600a0100f4209010807008800d14010940001910b0720005070b0184106041245448032340d880304100001d912441c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 362336465 1250 362335215 362335219
    0xd120e0d03022112040b06130b010c11120709050105040e01060605030703090c03080f03070f0206130b040f060e030705070801110406030c0c20040f0e0312100806040c23 74
    0x3103a0b002007110f0301d4207406584a0f54211055040600d4200c00e09821101294201d980d0000c01042c4103840c10030001582942144900c10300204906000080c4640031580c0003a1030148a00c0c0702038400e031956030340501c802d40c01809854015440e0200303100136041c288101030140c0d00d0030310802101841031041c101590340d00e585961942d19250320413005011403200640796640d80070000000614158001e0014003207241c1c0c10740d1a03180c6402c000d012401184022029900004e00704121140300d6070441005c00c0c1d2041000c43c158a9a0500c0400050345d007500a000c50700c0c0100040140d040000a0080e0622400444000c03030f031103d41c82c5081c1ca0140f228202e180304284010320450780030741c000c52015034580c42c00b0900b12042e5252a1440030100700d0340d040e44262030315a4045828a406220381c1d03080090018044a040005250381c3d034816a00007442c502440004a448030701c4010142c0000c0c142d0300308540d003d042a08101315014654030544102e40c03245040340140355000f18110940b0040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 362337715 1250 362336465 362336473
    0x10210050f0c0f040513090201180e07050d02040e010801090c081501051c150203060a060801050916020f0f03030a060905060a0510030b0402120403110a051c030204050d120e0d0302 79
    0x82e55401c1d4a940d04081e010084101050002144944401400400b401115240414131201a00025107450840110034118941555082c400d41c92072004031500700305a460100c1d03442400210380c42c024000c0380c0042100441d1640001030029054100c4030426001d44415564680d4070300d00a03075507802c020003a44400140d0070040045103004510300c0400c640d000e103c0110501c050f03895012000e4901486500f441e400b10a204030740c1000381340d130f01c05010701d03040c083d07465410640000e0803000d0041c0b2088508202900070b194051007441000b140109075400c881c01d10440680003501c030703001190721410540c508403000500683d24002c50380075240207090b03540d1050900c0d09024581031380300040010705481d44460644c90b15a44028000d4400c0050040c1d15401c2a10300200350020191820a1540c031075030f07510380807800204001602d01c4a1201c0da20780c0700505030f401d801a00880d804181d01100d00c00440e401c2c010b048000d080f806c0c80c290380e00030502054808120a158145801a0040e80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 362338965 1250 362337715 362337721
    0x90e0f0a03030b010c1203050907090c1d01020a02190315060303051905270f10021b0d120f02210403021c0c03080d0e07030b071b050615010210050f 65
    0x4029400a0f50a6006240081c1d581c18240c550303500300c03034400c0102c40002c0d5891082040d002c0050102c034002d401c10007000d11160340c8420006044420107014940c03174000421003024240e000304042d080d0f0310380c080c061006203848a00101140c4200348402d0343d00040d4600d000360404a944500410390303078187c90310350801c0081203110311204090024041802000c02000d40400448003100c400442c0c80d140340c03042480e140082c0403240c00445c8e001d0b0b0044000351f501b0000c46401003155105071811121441818480c1400607995068888000e4201c84030401d1110351184d10580c00d440311226034003100c0c410244022040c203207600e8059400050311080c0000d1005103400329185807003004406298500e03a80070b444009809051358030407036580200003a1002d0202d80d9001da0a440d42804c406000c621f861740d01c44060005c80107140c1c01c1000a070800300305c080320b6071035032000324a41c02008640c800c1c07401d503070804c4543c0803d89060380580b1541000b01c4013411580981c038410f2842d5103110359151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 362340215 1250 362338965 362338967
    0xb0406050d0b15060c0703020102010b100818030706050c0c0c0102062707080f01020403020a0603060803030c0a030f0c090f0b03040809010c0c0b12010f08010504020d02090a180c090e0f0a03 83
    0xba20803460702403601190f803030aa899402030518030340c1401c080c0104c213266100290071107040c81e0b01c850082000c1005000255000b1000c20ba000700ca40f06990241c8c10358240d050700354425035200401c1e0300d03e05014411454018406002c0c014020011145800d608000590b41c84400b104c0300b81802010010002259160413100c41e03901d40400115081140c031280c103103041c04c041200c60030f81e91394007080c20800e518011407040024415803c040007528140b9000e25120312004002e544524000070700d40c200d007440b0381e024109038000078001b00540350011074000c007400c440740700302808650074a1020680d50b07111003c0364002c44d0f00001c0c4030701d044040001036802c5501c108055550305007100f000244018034800a04800e41e000300d00701199070500101604c0032040c1e4101c030406a2510301084010380710300c44c0010000c0d4040301c1006441d0b41d10b46405025081001c500380c2c0380340c11100c1e0b1800300000303d8486d8050b038880c000144260034404660030f07a075404245282c10a07500c0519000d01003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 362341465 1250 362340215 362340233
    0x201b2401170f061816090903180b0405010c02180415050106020f070323030a0201140a0e0c0103110910090914070f1206090606020303070311030106021b190611010b0406050d 76
    0x3440000985d070110f0410482d056465a40d6407103e1b0a80c2c3e11528850101035001e80d030b0700c06040d04101807000b45400c1c8024156903004c0c601499043c80341d890a80400e55554540200c6884031085a440070b03403600d440e2240c1580f20118080f185170713003058000304000c1d00116260101228007402020118a191520090b0880144800200c1259961603007130301ca00c10b00c0249980701e001c0c7c0021a9241c80f0500607a841d110041401748890303e844e44401800c3c1003c00c0c2c0000250b8246404030f000d5003841d50414080c4207a04816600085860b45a0140d94000d00d40301d044400040b403c0142e00710301002c1c840820b034200d41c080001800e101c002038031136004039510302031032444a5000420544900c240d104907840f50300002c015902c0402080101c0e541030044101b18a00070031258107551508402941c1d0742c1c05c0102c600d64448912610764040d840700c5500300ca026250400c00f00c201e03592604060a1100d4a4940a003075508024600c3d000742000d0040008460010306000d9000800d03403140120 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 362342715 1250 362341465 362341501
    0x230310021c090c08030c1e0319030b0a050a0920090f210604030c050607090b0a05070602120408030121031e030902040507080a201b2401170f06 63
    0x3c211480c15000c54200800c001601201d00600c00508600c46050554400002d54180c81942540700f00411a4040048854951b0602c9141400709401380e11400196a10b0340d01d4020b160419000080001d403841c103601f21555903510803d807c07821085803104000c003403181c1c000b095044411076854504500340848030140d0003078841450454100d180c0300c030501703104043c0d40a40c0025460401c85050001c1402041d42001d00c6050030003c00740b500b8580200c501512100a05100001c04c00205000d110b0f0110303000751003800c8030200146000e15108080307400a02850a40203042048800b0555506240d2400b940d0951514568040030f201840c040508500b504410180c640a4480048e00d0354010079008211070303242c21000340b41800c1840116a03d111203940905c0c1d4200e2450010503075901142c10700c05140390070070607950a01496521341900301c0d0264601c40c00c90403151441140c2010140c1c162030a20781490342100302d4a220503912800000020344980100001c0303081c212001340c08802c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 362343965 1250 362342715 362342723
    0x50607110106082806052403240601110f0304080d050c0309040f0f0903080a152106111c14040b0a09050f010609020d0609051303031104230310021c09 66
    0xc0125941c4c0c407015604e060382c0031101e400c1c17100004900d20ba602e07c6001907000301500100010030080c8403020200041020125090404c0740c007059103a4860710189003240d1059045454101981d20b800750b0b617034068400c101c500d0003540007079a0700074490740899a0841880c001941404464401c0100816900400021881e500e00d43c0708925400c034000d088003c0e01030f4550300034a1912044620650320001a844080c01a1036000d20160391440303050310007811680c050715a00902484c1910090840c441e40d102c0910010a07600e44c03180040d070540c1000764040c14140201381c160001100c0844059800601c60044c0b0800209034150650002c40154061400c81e02402045a4550308554458126842c0f490b00001e000100c04000d0003510024004d4a00402c0145400c51703104041c9510740038000d0805071104141503000c000c3c84160340c040e14400300000380000c0c044120004055101d4241c034064041c05004c800400100c0c4240c5a42c0f4001348020b001540700410010b0040a031000100c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 362345215 1250 362343965 362344033
    0x504090c120e06070305060108010f090515120604050f03041428090c081506120c0d1a030607080705040b070302010204090504080c10060303050d02090d020d05060711010608 76
    0x2880070005001e80c100c41940c90000d0100c0d0b0501c070310000d06039040100300b24140301d1311100402410395000e60a43c103c4042d1000060a511607500d1107101c000003811b4681c1c4410740c00701868080c18003003016402507208100310707031981c1d200c02200782c0c40340942c1c49000341003111400500c019013000040100c0b0382058a2421100011205038000000030300e4110b80780c3c15075920345000d01203400c5403080384c220001d0b03510311000381d080a002400701d00c2600039a00e14801c2020101c3c0b0800600030031355030b4904c0c8514052002d003100011002500d010f58032a18428814080488e070441d0040c2103840c0202099610649071500b04100845507a100e101d00f28210341d420000014441502d10455000d24418240c10303a49040580c036051410360350f14204024940303440c10420001c1d402000b2204001000d5a000d601c0d80090300005064042d1488040e40100a1140d00410048042030186c4030302490388880425002c1942078600b2500580101200c07648400d488410554400064880c2d00441d44a0700b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 362346465 1250 362345215 362345237
    0x1d0a0b010917030c1002040f050d05061b0403080c01090b070f02061b041e0f15080712020c01090f0b01080a02010c080304060b10030b1e0d152009030f03030105010504090c 75
    0x41817414101182c0c11400360b50214060012201300d4042e40014001200c004e002403e1340e80741c25440d1600600301ca50400c1c3e56400a4195081c40e400303a90007150850300c40394464420717405090180401e02c1c000c65000e00301c0c0780060380090083e030000f0020040d540c020042a51604117485800d12604d0008070112424000010f603161301000554030018610060303400c1d02d10344003100701c200d200c1e07400c90b0080303620454240b0001c80d481051325502c01850b241c40c1c44421144484200207200c1d905000e949942001c4280b42403103000903c2612a47c40749440c0c86d0140e0380c80501540701d13612440020700054032629460081a442401f65030041c1c003800d000030300c121007130300050422804000d908000c29240c841800c01e0385401060701c0180803080c0302c08201154084001452014a11401422080c00c074148070b41c481100c1e4000003030008000d40402e0800da000c00401c80f00d40120b0354651192042441140b007412000c400d403812944103848103410141040c014202030803141c0fa915041003520100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 362347715 1250 362346465 362346487
    0xb040b1e0a0e0714070f0213150905071403041a07121b05040b0c010609060f050901090e0a08031b03010e07080a090c210c1d0a0b01091703 61
    0x51082204400010301031100d80308060090060066025280b49081001004181600704020f80400b0751001c48442e5141143c4c030303003800741c11030400d0b010b9009a81c0707600303214000c0301c6a8810881c800c010116840080e60750036000c0c055400c00c90b05640050300800c0c41038448081e84000c0c40d0018451030100100c84041c00f04001000b0040f51f030707440010f017105042c3e410242c00c1c0c45540c20211404004d019102e0810300081e18900c0396229030100d003000000d0502040d003007135105401502c5802d100307224441d03407040840300301005030040e03d1060003880000111341e00d852180d06012603240024100311100340d110700406070001440c10100200036a0b4000e40c00f14028001d40c064581c89413044086d082c0348200408081004204260b91450070802e02c01060440328600111000340314cc0125800c080321041d40005081305c0000d00120041a0100d00003082180e25000da21003500c20700102d80d529046802582c114486081c007050180303005020041c81211070002c01514801140e1070f01d045600c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 362348965 1250 362347715 362347729
    0x30209100c0b0a0b0a0b03190e010203010501092102010c0206040e010b0a030c0201050411060d110f0903010b030d090308030c070803040b0103140c01020717010908070602180108010b0d0b040b 84
    0x808400011400c45000007041401d00c1c2c0660031101d06542040090007503c04078181c12094000d03144c0d1940c0120008100e0010368942c0c1c01002200302043c0909149044918081e40081c003d0a003c00e11318080404c0400c0880c0d400550000ca10b040340f50801d0080d001581c2a01101205903000b0200700008180718148514050007403d03003032403c1d6929131f170035100107041720b528840794030459040805010100d010701ea9100c415110881c1d5956903108910207020040c1400b078442403014038081001d20b04103001401601601d40e00354024000f61fa6124109511042c1350b0b4252004602c030082c05001140c49400a9940011102c03011494421980c94070505034204681c02c40300c2440c1e900050042000303506400b0342c44000900148159030b00000080d4507403440b800362651000c0980404050907809410040e409a000514240d88002d1410540041d5208500040540071504140c7c5440d520850340e280c101c580090780c003810b0281150200b006131000346012540706407a0310705003c0e80d80d9620 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 362350215 1250 362348965 362348989
    0x60105270a03050d080a0516022505190e0c1222150f0606021f0f09020d050f060108160506090f090a0e0705040203060a0e04140d0f0305181c030209 65
    0xa01d0b41e2141c1d103090300740d490a42d0710041c001180d9110801700070299a400180351030b01d05840c0d5100c0044502151700f00c030142601e03a03103c03030b9009000c10070880c1c101010080f02020307a00d80cdc14034859950b850320324400d0180b080c0110340781d9080c114400940110514000390020101d1118000c56840e0326441c1c42e50346810301401b01c4a0240e9642040c0c25060240c403403000105070f01d0000d0541ca090b9071a00148a140e5601c00010b40341d200d0150907400c0c04a07030b12030300c482a03004004950380d40007401c00c5940e42c410f10035515041e1040d80000314800c41c001545d038501501404d101d50f00a42810b062007400d4025008c9260005154040d6031801e0b580d210b481380c1328200700c0d0000507144501801051030014070750302c0a03011368810001e00007540c49142c102819252581200141c4d030f02c0301d181001c100858040000001c1c0100b8240c400101c2d84040304400c403426136982070200340c680c11070541d540c842c130091480160b40704000200e07030400f400c401040041920300b001402c0103892400324550306030074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 362351465 1250 362350215 362350217
    0x50d03020f1e1504020a090b0a03050d08090f070305191506030305090a0b04030f0602030c070503030c03010f06020c031005070e03120a080f1302131d060f060105270a03050d 76
    0x200a101c9803101004107840c5600514080e04044c14243c0201d000341d2400d00800d8070313540d01d91039a00185e444014824004541c032030b08540280c698810000d04030003007624101101e0190002c0d84482a000043d94800da0b0b0300300c8090801c0350b003422514145801c0c100001c0b40c0400c10302d44280c54002140c420540290b000743c03111a43c952000c0300300038410065412410443c0010300003400803903408641005a25480100140c0c0c90b03c0340d02d13100c1c0450084d494001d003607200c0007041040e9507104101450484a01405968020761540c005984540c0f4030216182c0583c08006c03041c002088503084150400c48508001e0304260060300070030306000200e030003000c201d440012481c0401da846801c041d848502c60028800c54200b02c006090a0303840c1c8070001e44290040c500d910f0500607241c3c060325402c149482d6500d0030494101c0c1558882c0001c0b1203001e80700020000041065004200f1212001e600c000300501c120065580358502504048481d50084949040880001e104005504c0702c40b5031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 362352715 1250 362351465 362351503
    0x50a060915031209080a08181005070204050a061202130b0a08010608120a12050603100603050a0b06060f2506050c120108070b03042303040603020a0e0a05010207050d03020f 76
    0x40d0300380180d41443c181507401c2013001c2e080042004100120768046c0c3d5a03489601299a40b04c1600b00e00326103d890103049521201040c0445010798004000700600352007514103220700d5a40d40351003400c032105481a180c4021500351007400524007880851a441c1b1009000114200d1020204101d003005803c005540d80d5a030106000382c0004100b807008903461901c0301071400010300001841002c2c00265008603075201c1e0080b414a0f5010b229031000b19511b42d002b000b580d5504d007801542c0e0103038000147d60000d0b0120106d500390404034220b4844441c4040750ba8503220f0b0f40005200000d40360300b5440410149038845500043c00c5001c0d960148000c0c914640e03d5501e40220410080d006a01c084410780c04000100f00501521341600e038842d0b0004030094420041c404a00f00b42c80110036214114080010041955a01940a456046140d545001c030001141d070520489400c1c80c01824050381c0160700400091520340740f000c446500c41d00c16a030004808131126464090380000340c2c844080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 362353965 1250 362352715 362352719
    0x20d060203091e0705011b054603051c0209040903020102130e06090711031303050f070603051009090503160f12030c090603020a0201061a0d0b0a1503050a060915 71
    0x83c0841c000200e55611070060080c041c038010019142c2c0410b80050b02d4100c03504c0351f80a003845801c1c0480d10f22a095403280a0508507845100c429818a551007070b001e24407041d00284099020500c0f0350703a4943e05860312840c0920f03203031003140340c020394191907000b650b02008890219207450254200e6240300703400141c7c4640d40102505552502a0055160042c2400c2009916518042c40790b03040300c800d04002800084082d080c60440c80f405007001481c00f0398800010404c000007c420450b80441c0040d5205030f0340342c050482c1035850a942c0200078010103a01440074406d19407001c480305100703908580c42c040c0001e82110340080030780000d407000307130344100b14005200c4540981040c0d040549010408141c1c00c1030054a486003900900307040603404941441254000d5103c0800b421964920b0310300c100034805001480e0740180c2c1e003143e8560528105580a0420321211402d580b20580080303802020500228000d000c0188009031050321000c1c00165485c051260700d00d11036420001e210124 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 362355215 1250 362353965 362353993
    0x31e08070b0411010212090d0f050a200103060302010c0809030a1a0601021e0a030f0207090f02250803011404020f07060b030c0f010f0516060203090703061512030c020d06020309 78
    0xf820441d60281550440856051051903600444204690498038440c07540c449051050919070407d100500038402c04c0207450900c1300c0185d0711940700420301c4402ca515240000110151030880c40004d0100c0c0840d950000084c0121000d4420b009001e0304a840341021a11084c00d01d0603880c1c0c58810034002807040c03010395603060bc44000250074007469507540d90301c040042580c41650780700c0542081130100c2c0b140303041071003072003401c0c01056a2601844802d1880715000000c2d802449440e02c2840d41000d900c203100d00261a102c50700b900300322600d00310b80c07a00820704154120420182d034002d038200f01044032081c40001070800c0c24014040000c0081d0202c0501d80740c4008440824820b0711084013011650703a0144074480058100d281041c2c9030362802c480126a00103c110080a0314008001c00100c0d110006004003101c2c040c14042c0b0075800745140010f030780c50f56805403052008401913503402090090090701c0d1074600c0130300002012500790f2a00400c0780c200b84c880e800359400c844000103050b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 362356465 1250 362355215 362355233
    0x11116060c031128110303180406080c030a14010209030106030b2e0501050705010e0307290412030905030702090f01140f030717070306050f04020901060e0901031e08070b04 76
    0x1141d140c2000304680f030075803000c002902d600444144c00034001e13000e030340c030420440c6540c07074801050250440352280301c10041110410440d010749070080c0d01d0080001800100054084c1550b41d0140180c00c20070034a484050074404001058a61507400308021002a1403d124031001075008940c407040d01c0c10422a040c1100840e1290724109503490011100301c150000303017400841e0824282660b45100c079151144c09040489a8154680000702d0024240900354a00d01c007003100d842c003843c031031704010440242840fa0588010b011844003202c905d41d0507010b68000058a802a01207909040e0a42e001441d103000803580400640800fa0042101601d0010016006282158252808020306000c00e99404981c07203201450361509400d44c100b44820301c0244095130b045403041c4074919040c504118002c82c02e071400c0380148200c000004056105025141c020800141841d84907441c5407503c1c26007240059144070301c0030400b90340b0030004160200804100c2d00c2204200402d24203420003c1c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 362357715 1250 362356465 362356487
    0xf030302100f1b030c030f06031b0806040b04030c0f14010f0b0117150103090b040305041406041512110c0a060c030204081e0c060301181b020c011116060c03 69
    0x1401d003020f261202c0c0707162203550241d0000d124a000a10030500d002c01b213001c0c2c0444900b90100c10302e41341000c0140720204c411000da0280d2070440e6134005070307a00440e6036102000c4802600d110400004600001e20903a01800114081d4251410707035101c80e1203202105000c6040114160b64800d502c00121446002d6410b81c40e800342132212001840c1c150140300004000c1074008660b81d03003840d100290380070f40e0010703813610b4201c0e40030ad609240510700603105503c0703401456020580303c2007030009803408004440070799908048801e5008500315043d10000044010301d2501030b1560070079880d44900c10080c00d0303255112401032070b031581c580c01c1050844480d903408600301801003105100924001505c10724141080f203040320603d40704424a800d00807203805050b844800040006418a80781040c20100c40f1807500800041107050348a801101c00540b2407409600300d20001c407400c0d80a1981094541010420341d10000c44d815106a00c0440175008180031600c90410041819805101d400e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 362358965 1250 362357715 362357741
    0x21e090108010b040f060e040e160305060604060f1514131d0106050a050a050d050408280e0d0f060606080723030c070305071a0a0c02030717130f03030210 68
    0x1c43c05041c1600101e1600c400e0146c081440070b094076410054599912078801c0380d20160994601d6000111518600416484150b91920452011030564549481281c2c1150060301040d90100c1c688071049443c010a18814010f0100341c03903000d040c44032880020b141c0c110f4481092480300e820b001003943c651341c00c41e0b00011600610001401071a80101c100c0d1042e005904009448028400e0221210b00c200350101c0752840c200010f0108200d240c3d4007400052100c100b4046501660b080f4281e80000041c0c851000601050410704a600306004040c440c0307802440100b42100311307602c0344002d5408a9000700e001a50b08810800c0c09a4000e452900d030329049540d503a450f0b8034860b010b607103600010b030060071450400a820020103004000300c0344c8240c0c0c08484003120960390f20710321030403100865056201605001507114011310120894400360340c0801041660160b0300389a1845411210308020082034101c8040b8521042c200ca11008505c00c2c0d0060810708200c80c070310410382e110400c41c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 362360215 1250 362358965 362358967
    0x50f0d050304150b060d09060507030f0c171e010b030a05071106070e2d040b040209090a05040c0b0c0303040302010c0f0813030207170709050903040617040204021e090108010b 77
    0x800015128032510032004141c070808204c5888420000e186407251a083e404030518203040041000203036003040340300c0c26842d1410007842c02403001c0901a038800d401524009210900111952603090480a400040180c2003008500d03500000c200500800e0300690130100000c0100150b480305805501c0e0b02c00220314002d20034083c15072a56940c0e42000e44200180038102d103488006e502c0342ca403210340c0032025001c80e17034590280308a40504a00b124404901450810101604508140c022513004807006001a42391303581c0c000a00005281c0940101da44082c02c01d0300041c40d0b1800405040c801403108050b640d241031a280c06403c464400c43c03070b07009019013800800003858000c0107442c1d10145d6007140b180751320302c603160403420006290042803c02e41c4101c00c5001c103030800078280301910000d40d0308120645909601030b540b8004c601c01e1400080c81d5200f40e802c910302a807a466005840544050b00f442080c5000b0b5580c49a2124403101c12a80854149815a44802c0f8980180b070404802 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 362361465 1250 362360215 362360221
    0x13060905090a02070f0b070e0a080f030a0e0402070c03051006050a0b03010b0d09020a0609030b100503030306100212030c0909070c051209300607081017031303050f0d0503 75
    0x41102071400a01c0a5442075000ca00ca405002211191700b08003a4441907112003840c081030050840910080e80c5c0e070040717401d0403000c0368240c0d00103001900e03c0c3e4214020f6003001000d10049541c9401c400140350001e80a002c14400502a00409070180d803207000074007481300855122034100d0301d0350b80c051449008118010403a0581c20001c50781590800c00445584401c10360b1001c004d81000800207400041c0d4003400036078258401c12140a81c0d101c0c500c002069101c685802c1020003090003095850f0f0001c00104940d0700e405100401c1000c194016500d603805020601d0b2981e40044070341010b02e0708005002034451500000309980900141407581c840651521442d070b035905820182c5505040000d000031865403004c440d0211100c4031001440e2101d900c904403441e030401100040c60500c07504022480349070085042c2e520500350614041c582030b1070103246601628a41c40308007100c0c003040114129400202148002440c00b6200401d0102580070150349420510b10072041040303024824 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 362362715 1250 362361465 362361469
    0x1060905011e0f0309110d0507182a091d0717090d050f0d3603050a120e0a12020d051206060c0f060403020a0308010e13150f020f13060905 61
    0x460310f095826150000e00d0301601e180003240111000407040d8054103080e0010100000001d840b800e5400200b808001c412607580c1181c00c1d159070402105000c6114250311000700064241c0d82c3c4100031a01c6c250b8070041c2e441e0031011300c08404060042c48044c0383c40411503940c0c1c10011001103045c0072000c103102844c00118040d00c52241061000801c980029966820000081505c00f42c60304a081080a07841000c64042182c44004ca141c40080c08444030801c14180600c43c401100d4054a80a14048960710100c2e00011181c401819003903842d240103494407010004207c01d05e100c1d20542d68004c0004d28040d290603500f8040d2030402c00304001c0c8442d0f201250700b5242c3c12120964405c1e80b6440704080d134038284113144041c2c1ca22849141301b000249513000580e4101640291103108090340c03640000c8010920850301c0d090f04902000310180081ca0400d00000045003201c400580e111038181901e0599002c960740c1440740101240403501e1a802d404000000c19144c01c0681c410341c134000c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 362363965 1250 362362715 362362727
    0x309121306172e0f1d090c0901030305030604021306050d140709050402090f03061f050105040501080c090d0503030c0d06151704060207021801090b0915040e0f0601060905011e 77
    0x1c07210984003280c03c02c400d4449065440001d00804070b155004a03440e80104907409013940115031045034001d010800079200441e1049403200e010700110036503801d5860945240d44050001034209034200019800740c540700d035035100500266a6120380d141c80504114045e18404880c20100e980908180100c0d40d4011881208980050f00c000d621074418200260072800e007070100d03039090b0040c401081702040700382d80c803c445020b598421a04890702c3c0c0f001120280518054a8085203101001c07850b0003c0c004050071902e03a0007060548412900e50fa050b045800c20366030076407501004902d02e00210300f01d0088101400d62410500c50703101c03040d0030003040c00b6440341600d0550042080400c003405004d40480e040f01c1d40140503410702c1540c00740d00000301c150034400d500b03c440c40c0140d80c201d903241c4105035074080c0e83c810424101141c0c00f0002c0000500e5101020903007440360824480081405110060081c001c3c2d85908801c5481d01002500c050805081141c885400300304681050750001c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 362365215 1250 362363965 362364001
    0x3050106021b04020d05010e0615030912160f0311010f0905120a120e0d0905010806130b0d0b0901390e06070812011404090c0308030912130617 63
    0xb6880040020860302040c0280700715401c45040c24144000401c0b0070140b00083ca01903801540c810711251140d01c203c1780c05000913180030040f9041803007e1000c07020b0480142141014810742074504021a649401200c40b030030500f1404030381000c0301c100008000303104204100da0820380c240301c02c10550f503071242c0301c003e0404540d220b00c50100700664018070138015079076030422043c41084503481070365141d41e4a01181401100050080f403020803254450308402d4000c0001600300440a80341c2e9030a40302412061080640001008c01d002e00411000314285000fa54070100001c0c80e201a000c014000620028640280c0d03050b04203c180b01d1510200c0481900700503181802d20f0b60304040000300ca500c1088400b601da03400204034019400803a403c1181215040c52680442610380c0040c8810f54420300c102400d81d500d5800e00b040851543d40080d6408031100050b61408014036071000e210740c00003110300030380400c20081440016040907180000c0c002191300e04180e46030910031803079226054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 362366465 1250 362365215 362365243
    0xf0504020f031f0e010806040b0c0c0a0204090602091c150b10081e090114010f14010302160c0e040b072a020a05211e0d200118030206070305010602 65
    0x1c450600504041160f009000300f404030300d5070384d41d407294410b58918054a041e20117100900108828403d82c0c400c5991101d07c9101038035000b00e80b03800300001041105001c2c0d074596000c00c00301000d80c0d290500440005450022840765032250b0a0061528030b6a40007038100c10303e00800d152040c3d59908000c9445689454090355940d5140d441e21014100c850403041c8000c0031034240141807a041d0488682c0c041500b500025903031360754050402d044028800c1c6084042c0d103403e070800179403007034008201c542c03031205141006e00c64a54a01070221507545c800b040c51089082031004000904c1c02d00e0360014590f2400c08442c035040c0c00d03c00381003c0410784030701d0204185007807042103440740c203103c60080c40d0040a18222107818284028500d11040c045007031401000c41080c040d1810040e480c050190f048020b0421000040090310300c01d1243d94120000c1c808281c920400c16001d0007140c81c02400c0f000c074103142d20110728020349003901c00f60070f610506040100505c1032550002d17045d200014a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 362367715 1250 362366465 362366491
    0x30a080d0b04050c0702030f0601150507110d05010b0310020a0509040e0f060c03070306061b060209010207090c020d1d0f090c09040f0504050f03070312110d0c020105010f0504020f03 80
    0x100d1405140100800500c0ea80c00c1400d1004110309411000c0c0640311607402907050311011241e0341d0046450368024002c4080d02c540351444900c1c6288900003410b85284113086020010b24400002240301c151440103c07500d03074481c1110750326818248a0103030141a8200250308098905001820728059040b44500072035a0b8220201036101c104080340d0a040104180c1f56642485540c0402d503500c211010000302c0d05006000078603d01c41c1e21030312195100c1015140c0327000803076664a0041c4d40041c8080341188150000030482510a01c10541805016001081d40c0d9840b800c0c0a41601c4540c2d1070f0140d0f6000300407120106840780d4812205041c01113803441016030f1002c03500c020074064803025030b80151502541c10a5100668896409135014070301301c40c1c4150601107426564404d60700002c0c002111740030702c2042100e007904418444c004441d03e2034100322501d00c21004813940a21500b006030b455030010492203030002c10780c1014141c282c40a61400340b210046113020f00c400741c126516989 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 362368965 1250 362367715 362367727
    0xb0901050d1116020a060215061c0b0c04030c1215050a180503041d1e100308180a080d05070219170d02010c020a0b06100228030201060e06030a08 64
    0x8400d0348061074403030b04900301985500019940549408160000300d02880164501081c602c1c0002510071090125002200580c1c3d151000d0040d9682006404e402074a034400f0b282c4001132070075504902c101506503100d503e86145041c1002c04802503881912203051089910000c00d1000d403a0000800403448041000d44503111070310024510654a442d50802c2403801904218022000b07200b2a0182c0b54481800507070819240b074060340070344066502400000701c0c664280e0401c0542e6034000d800440e5100000c0d13076030b00c524105074000200b0400400c400b0602c0c0c081442c108581c1c4014002c0070b401041001403568001c0e0581c458030002a11a012030090880000d00a02d640000782c01c08450028114081c911801d03074804403e0506009035003460b41d618030241c030001d901401e071600901ca44940e038407110288560b041d5021128411070044014007071000804020072040c2d01c124248044c15100d142c00c0003802c49000d0781200c10b82414050900115a0707001440903d000d40105409681f04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 362370215 1250 362368965 362368987
    0x4020d0803041106040807060201050c030f01030b040305161a160518130903030e070b071208130c150917060f0c0c0106032006030f070e030309190f060203040b090105 73
    0x7080f03060246601c882c0004000c14248030200d80301c4100d600d550002d110700c0d281d4988040c640e0100b04c4a503240c40402400420228584861560b0894001c1c105603207025002c000c416540700080405030b501d44070300c69429111a40400c0300380e900140e412070f902c0c1200e24080700141b035480790a05e04801810005240095a0340c1c20080a0303c407022120100260b2006240140181444101541d903d01030100c002072401e010b001111005540805011203150080304107a4a00344054019000001c001900000180310182008040d0080955861600341030703110090038041190025201c1140e2106d0600105800142c01604107a2941a0440e603940300e074215959402424221700066007011780000500c50501d410300c05c00fa00b020360700102c1d01000c03000c0c00510300c0161501c2d0750416040001940d0148a000301904070000181030b2850451342e41c00103203140a4603c103000b001002c100301002000c5540d14410000e040303c0c0041c600702498a0341040250181a402c44d05001d00007a64000c44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 362371465 1250 362370215 362370233
    0x2010f02121201030302010c05031003080d020714070906060f0c0f020607020d12030507030902180a0b0301060905190603120503060a0f14010e0906030a02150904110307120504020d080304 82
    0x81148000e85842e01d0940d1209400707420284020f4016500c2d081c492034065120b081100d03c20070003560f16204140c80d595844456900c1400082c0d242c9038240720920010384104481459161418001d140c0c0c0790400d4600001c0355090b41c00581881506508204880e800c040f00e00e00140d008100816480d61600100b0414410340400960008680e40e03030004200303900a00700d0300c1501c280d4080110f5500d080e02502200c2004101031340c810a491a801d02e45100c0320955a0b03c2180c0315004540180c02da800f107401d59a094100d05d004544900800008100100e01c00c1c0314400c807240184000e070b142d611155600d078105041c0d0020030038000000b90b5140c03a1146420700800e5040500c0390040c0d40c54800a0048050080c4c131800100e0b0006019004e15100d0f840d0390041000a0140421000301d070700b00034a4080020000c60180e506010302c41c0d65030b465106111400d00c8409e034090b0349103805e210007010120349403001340d2090700d00300502001d40c0f100700100b403005a1200c0c6280c2c0d00c0d02c4074107100980f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 362372715 1250 362371465 362371483
    0x15090405070b0307050d06080c06180a051302070203060a1a060a1710150908030d1503050f0c090901110306040b040207050f1c1d0d14070b27090402010f02 68
    0x721800041440004e590000060186c070300310100800c12144c4959003d0340b200190a02c00764444410302c034001c8c00c1441700660000040d0b0052200200760b07580c401198020760041481c01c04c07903901240c0402542001d00040b5800b588524003000031030107501c900b0708117401800400703004080c08258072498900590142d03600c0034100c611501940740004880d0702401e0f29004241c81e5441c0458200180390140d0200c3c402d850519000e582802018802c5100505008100c2c9410102d0fa80000000c45d0040c8140e1561011040141150b0100503052000301c0d04044c010a280781e240540c050000303d800415a60841c6007118042003008035100010041d000307440c400b4041d03004804000380c41540004101c07c1c858013250003108998031000090704c0e50a4100c8440c42c50311150420010240381040003111a68801ca4600300b60059400c081b074507000564015000180c030005003001c0b55500d02c00c45009040b0640c0010888000b0800804c00516007c1d20007418446009004e070f104900030b000c00302d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 362373965 1250 362372715 362372729
    0xb040201051309090201090915050111160308090108011217070804210201120c0207120606270f09050a0303051b0d02031519060c030203040f0320091509040507 70
    0x41a00e0b01c940c4500700134940c41c1d07403c0317020480b10f000006542c074542c0200c40700303442240408201503242c80c0054640b4145010841070754060024656800b81c42040b00c0340103503008214458850f060040094103000e4182c100180902c1508001c5000440700d85012481500070070003182c40740100c1c5481410ba0081c0d8002d03404043c0b140b040340b20540810700380d45200c2c0f0b00036601c0d4141d5851400f5444200c8038100b90100040c0c00403103045c0600e6001c0e442d900c10f00d51181200260b40f030340c1c0c0c0c0e860a0540f0749004c0c000d5200c1c44102110b0004940900442609404a0004100c4200c256a43c10368811201000401749038551000412040d109903c0c01c91280e00e00b2101ca540d1320205d80c06d00c0080d48100c640c501800d84070a41040541050f400100c13460784d0714940041c01d50300b03101094610b03010001007141184000c02021a6415140301c2071030095102e00c41400c0403503d032040c1c40706c40000c0e0a0185005010140c01c124580561340003450440c07806031019000380c0c46604045040c403402c0d8214103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 362375215 1250 362373965 362373997
    0x40501050d330c020607080f0105030304170a081b1014130507030209070f09080607020a03140c0a030c051e100906020903070b03090714060a0806011707091e0302030a0b04020105 78
    0x2d10f001e40c02064143c0320f4206660798002c00c1c1e86622041010010038055680c250784180820720965801511449101106134112081e48603590354500c0303035038012008421865846040f01c0e08404081150040c0990049804d00c405405c10620030f2001c030000307214025030b611045141c000c2c031505120780b001440e005003080c0c1c00c0340f40400c00a4000c61b0091b08401c0010706486000030003c101054080c010455070380540f28502058404540c0a002e4440e0810904002c2003008500081000030205003032281c2c4983ca8441900e040c01c46c01d000d01100944451030035036481c1141c1e43c40100d01540d0040e1050b00c0081c0020241c105000207018007001180c240c852200d0201da509100b81c003031489250050103c031401a25030203c5020450199800c5400ca58140a1686240d0003040c20b1548441d041c900701d01c0b440c88025006e0851882540c0c40d1001c41d40348142404504428410401c03c50020070010200c9451680807941d00c0d24120400740c0f1220080c4042011a0302c1035040380e600c3c070131400f002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 362376465 1250 362375215 362375231
    0x60f04021c0c0605041e0b09010507021804231606050d060801020309061501020a0b13080706021b0708160b03150a0f0906152007180209040501050d33 66
    0xa000c1e42d0143c01280c05014001c6d000d8070362640d040940c00c003a9410400c081e428a04c103540151040d4120a0040307038844202440503c1004400c484140b00d0b42c0940c06644900e00e1841e944005040c0c515480d0561b40c03c50318603c2a824441d10703000c001c54040e4a040c41c0c1d01d612003094400200040c0d00102110350000051142800d000210307903000b8440b0038050100481c1c01401a65034500009000b02000c00d603c3c0000c842c3c090044040c0304042c00b9212051070602541d032101d0403039005094400c4404800308206c0054001080058090201c0030024409024040c50100202510b0300c5441c54410300000040c1540744078483c4c10305085030280480d036845450301c000c032400800d5402003200d02850001c000540c00b0341480341540401580c1c0301e0301c0c0c40c0c500184800e2142080700c000d8221500c03c0600c0081d40d40342c448205840300c520601c005854000c500108816660181d008a10038910654480e001c01c280d50030040c500b210203444500c00c60f2400220040c4040c0484c610600d4604d480c1c90 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 362377715 1250 362376465 362376467
    0x10315030506041416091a0405070c1703060d0f020402070f0f050d080c03061c02130609050906060f0112060308040b1902120a1101021e0703090602060f04021c0c06 72
    0x2e142c0c000c1e84144500c0213140201d0361240d55510040c0c00c800001c881e4500100003c2410364840c1c003145e10190ba200c8091700e81c0303030085002e96106440880000e5990441072091100500b40c400c22884108001b6141d4145000000e80c9110a000d005d08203440f02c412000441d40d071713641203a01305640b100c0380254902240c14560700d0b50544036010b484900078880010348140c402c640c0c81c0d2048005510690950715444140600e05038041410395105124403056005aa1580030111000840f000042141d900704000c69058a0300900003107047d61242003440f00f030ba990020186603152080c60300c9c01c0803010104650001c0e002c0c0d940f0141000100007004100c45140c0380c0140601c504064800c01a050b0580e8200c0e40e1b22038424501d4080309060015085151203017141c503001c00d403038034005400d04070710002080880c031688800c8414004c00046110405130011310303440c02002d160024003000d18000320b01d402441e4005000034890f104110112b07107514900e502d90b03440581c00100980031540c076800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 362378965 1250 362377715 362377723
    0xd060501061403061c021210150605030f010306181703061c020f040c0905040e0706080115140306010c0f2d0309180915020301180207051b0103150305 66
    0x50400010701c8196401c1241c60b0001c11603008560141c03081e544014038022030803050780010000c070392151404d150849412070400c040085007020300340000e00b242c000c01108110000503408803060140900401a611000040c02c2d030440c1d81110012564481d03140011141b030055040c010078414068200440100c051405148925401e44000710132110300307502c02d175030400c0d4504000e621941e5510f001c90b2504058004061504845c108440310030f484000107000da54002443d00c4090f0300040007004901d40c00358400b801010700008181000c802004010030543c05401c140c2d0a040b80003011404503403143c40601c1d60203400c102803034070814042c03501032900d80b0f510b0098480c210300d0700030040040c1100d40c0300b0400e541d03168a4100341603103840c0c1020179848030011226000d5903500800c40100300c2c40b0300340542c5800c51800041e960b40c108404642e400b09032840070003c0a00c10700084000a10004d407100741c105020b008440301c01da0000040b0045d024000c450210900c10a40010402030001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 362380215 1250 362378965 362378969
    0x30c16050a03091e290c0f1507030b0306040f05070e010b12010609081509010b030a0b1009290a0512010f060b090a060c0305070b240f090c090105090d060501 69
    0x40c0341040c0e000d010071100c0103108228000e038481440140d4290808a1003202c0200c03001131701c601101c0c01c040e035100115091229030220340a460f003018181d40c5d44ca8a01880c0503a1244241c20204244c40a05000c86c0c0e0b9112f004100030105014a00c0c48800e002041000c90028445608241095a100c40318455150010f01e185522a90040008510301e40207010010507114080300074040b000c1c207160030840f8403002814642131556601c20402071601e0038890070413035a018442c0c10310203091801d004994292a035000042003483c1004201903e4445091134513071b0b0708400107401503240074100090030a000340d8800e661080201031605595401034101d50071584107500200b0030b850341d84140844510918180a0740641620424450746001d600742002490003450301d070342001200e66441c3d180706002e5900800306200c0d5501c4030340038505016404000303501a10604010844000400c03e1806c019160144003280071074004c0c203603442103003581e540c03400c020b089010481150819500a140078 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 362381465 1250 362380215 362380229
    0x408040f230d171c05011502061501080402010324030c210f060c0507050d02030d0b060c060a02090f0307090b0f0d0803070804020402070206070b0f0714030c16050a0309 74
    0x10500c5612510381461000c2038a03410140c929900f030103040ea40c129952148000c40194401c0c407504180182142c840c0e1401f805031040b003030128a10680c03020385008001442a514825480803411550b6444a03c03039400c15420300b00843c000e02e41484a0306650b032100d00000b807c1c42c3e552000401c1c004103010920855015030440c0400361048103104020000e81c02c00900307030070343e994031500c00030701590f00900c0640202d15225090008665600d41040f900000400040e807010990b0050040d4901c14603502c0081180c80610300390003c0e50319034442c1c0d00100b446425560114444109441e4209134600e0000f00134140c44609442d080d80c84001c12842180d2070017001240000c01442c107000d002d801c240c0d5008002c060643d600d14004450555008100700e810503001e0000000603196000038080c040e12906c0b500d0382614240d1151141c0d0700000345400e04002c0d0070000101c80780c40e810200d0790000c0c10310324003035641c0c100820b070303032558040c060780003040c034402c2550000078560302c0040c0c40c00359030344 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 362382715 1250 362381465 362381519
    0x1b0405070e10180b091f0216031a060405010509070c031110050a1410090c03020912030306031b0d02010e0d080f0c0606031c0305070908061608060306130b0408040f 72
    0x8440b130440060003180089071b006a81088041c19044000345035042e0a08a44101d601640c5000c01c0c1d83c840c40810340c4101c501002008105440c400354201c0154040401d4900b0061980b41400041c1c03000400390291050050004c40c0c50285481100e00c4021100b188045801c02411001a9401000115542c1a8007407900115803080c5411820040c00340c21400e0804042605045941000b040310070803003014503508101b4509161204940b10300300000020181d03450389051014141441d50302465884a05002c10007000160b40788808103c00540a01c0d000300441801c901060003c0ba0780f00019051800c0031800088240d0064002c5c61400060000c1e5003840c2c80310000e15035a005038083e44000d108504c00c01503100e51087e4402a40a003403442c24044295031201814105031041c0c5e02c4100090540340340800c1c290f00090200d8101000350300402d1245000d0320440030498102400805d00b0301d01c0303008541070000750000d80d0060800c070800c2076a1965100702900031818801c0c0c0415011017 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 362383965 1250 362382715 362382719
    0x3010b03010c080c03070203130909050c0108040206030109090203070b0d06050a0618211a0912090a030311150106020a031101021c1e060906171b0405070e1018 70
    0x2030601036165842032640300c05000742c65110f00749009400c01426182184800d0015040e02078500221100070440200b00141c04041801d280c1e0030802c904044d01e060201d10018000142c4540c021a41120071b20305000400c03030740070310009042c004954060207484501152000050f10b10358480400c0701c20446241c0d03c49070f5aa00b0944208445091410260a1105007002821070916000b913074003000004e030904500c01a914000301c00226900507404110f080c0410443d4041001103c05100003c0c00da01d0030b143c400f40005448680c140001420065a2900031b02218001c0004000071180344061401543e1210b50095071002a10425000100080798490a1103010300c00c1f04c0b080f801c0f081c001403c0758240c40c10880981544d07058040c461908080c4010072442510468016003100e07d00410705910f090341d4040c400c900211107600541044e024038a0706540450038000942c800e50b03011905036039074802510b001700e00354070440d080a20400c1c0705074110741c842036400e586150656140f00b11a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 362385215 1250 362383965 362383969
    0x212041104050112120c1e0c030606080c0307120305040b030a0203090105010e19110d02270f011d040f09080705010c0f0912081308071809020607022205130203010b 72
    0x1050000d4040c0175800c5241000c40d0f4248118008546280540c4441d0008880301c2052030034000808000c0d62016840801031007003080038040c0704014000400140100e060b208006512880303544103c140120022200400301401102610018030001c420281c030307454030b2680c110203544201d81c0900b071035280000106030300c06c100b4800e0b80101616074815004030a07440c1010700520045503034403111202402605210050f83c002002d080003a081081a002c14050303509000f000c0025040740326510300103c441c0e40366401204100e4820345174204000300c3d000500444c0040c0814901c0d40c45c1c15080100c00c00521990754000d01e0124071940081011116150044980201040c01040000c418100c00c00c1142c5250045240c042c2c004d00e03115180c1900007040034038031401c942c0403200c650005c103801c01000c01070b200c0c200340c0002e8592080c88200b080c3d034005141889082002032007628810290795800c800001000b18800b103504081100341004440c030500142140c0e022403080d030a01508280ca8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 362386465 1250 362385215 362385239
    0x110a0e0406030c15030b060a0c0c08060702280507030b06010f03140601110c060313050f0a0503190201180320120f09060c010c2c01080c0c0102120411040501 69
    0x694120fa00c80310860708044104000c0281049036500701912225160101c0c0d4a0000506c00500c203603d030f154010b103c7d49450190070400d6401100301c0c0d04110104203455070046010300d000d074110600c0304640016551000d4500b9419100504607204160001c403c01c61035019a50066100b41c0701c8412000b540303c030850079104403036030301c031079090301c03840401c1c01540114131054080320508182e500020221020403c203400480d5a80310b9901c40124100a00105000c5603500307890f40f1014001c06901921140d5403407240c024200c804e4000c581d03045003580d200b076011841300180f8548924110201c0d00b001440105181c8120181c503004a004c0c8001309000514500c5071140000b07010306085218802d6045a0800400d40da0400410030603d40c007030308207118130030115445444900303588000d40c0031160814007800400035580140002140d43d07a03040320385203520103001101c0583c0c0e400419045806406141c050803841c6078850f0134481040382a2040d81b42c118000e440c04c03c01681c1e511000e10749 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 362387715 1250 362386465 362386469
    0x120b061207030813030b09010615020d0f0e130c0207060f0f170703110304050f0c0a0302010e0904082101080f010209090f100b030412020105060301110409090c0504110a0e0406 77
    0x110307034000c40c01000000c0745403002d444c552800d112101d0102d907072078a5601401d14202c07414500f03a5134421081c0407050182054102d000140d02c01050003540f000c0d0080d00a42c0c0018124062045070a011003065554040c0d481c12032004078005d1041551408010355204020300400011800b04010050f03014424180c200d07174011180d40380030074039035151528422004098110000c0540741d10011000381e2400000718000d910a6009204100744404200c1c100801c00c070403644200c00711036003040503030b900c480c402d10b00400480b1a000c01d03840e5403404980510912001d421302500a0f501140304802041c44107048880c248107171460f02031588002401c038414001e00503813066182010824850034105103e41c4001d6000505c1d0079640c803180012640d41040b81e08940c6000c80a81c142e031456428000d1a0704004180c00034012031011669940c8a405507001d00b02400f03503164007140501402131500001000041e00800c1b8080c0380c1d803006072181d0720281c608800708090a2040400741000e1280c2d2003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 362388965 1250 362387715 362387749
    0x270c17091c1209051903080c070f24150f090c0f080405030405090f0717010609050f04151d01140a03030509060d0606030e0111030103080711010c0b01120b06 69
    0x1d2004503206a81c100c1069040c840300070359420444001079000c022007102a681720545041441062030018900c243c0102188016201802007500252190760010070141d071044941240d00b6440303a800000301c050f0400d910a8a04040280740c0c1281e0800280c819550102040c02c0c1050f160313103428054070300390f0003110002084580b980c8041c0348140c1c046a005031181e010f0700c0c6050354400004202a400740d9031080e41050740c4040c0580c160b00480a0000031403040502d041541c545003001d4003401c820320825005a030400e8007040d066860317612000d0382d44c1070140203040d03031034403581c2030306094040d000203994141a0000106821000c980403c4228038000c0c40c01c5621810340d13070111500c1e040914400d420190500100d0411409030040f5030190003150f41c00100b070300c4080c1200b401d40341d804080c04200c0340d0420041c00880e404404407414280c0000150003807220140040f07401050307911020781050540c0b0000305429041e6201d00502c1800360221140b42d8503030720100700d25046259401c0c0303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 362390215 1250 362388965 362389003
    0x150b0a0e030f0312040c090203010311010f02010902030d050d02040b030f180f120f120a150902070c03020409050c030d0c11041a0904050c03030a02010207061a0a270c1709 75
    0x15184d400040d00b0b0a9220703102c3c5045544140c3c0e01e000e06026a04282c00c1220042d0000d01c0c01c074115603000c070b074500b01c0903010710090080390919000700344c6070740c081880c0c0d0007005000038198040710440d07011140140004440c1c1a502c1c40d000041e50007591044c0d40326003440c0d504200c0002000c4d1b0010707013142c021800001510780d00c8408000404903074003e500307080a05409014031281403ca14071218800e059418000c100007107102c1d00030569802d0754000c45011841031001c080407038100007200080e00d9041d01c00203142c24039030920903d08240a8103d650600c6030059980445602400040d0010301c0b4007840081880c2142c100001d460803184c0828080000381035000c4c4603c3d2440696420901030015140e2403001d007008617040d0380c4600c0403400580e4001650104004151058440c001707005a403031035004940ca800105140300c580724220b190404650380c0e4a800e900208900003510019100300980c0608000207401040021420740c950112100020200100807620030075001e0044400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 362391465 1250 362390215 362390227
    0x60b040e0f07020a0b040302010e0d030204060905091b03041a161202130f0602160e07080103080d0e0d09030204050610050d230a2705030403020d0204150b0a0e030f03 73
    0x1009100c500902e510214801d0b2520140859840e00c20f090142d40203074004501140090105c91614602c4400c410815104110400402e603010b5545400e842c0c08407240b400c0758845050403140c0800d850061000e03541d000040c00200039420090f0040902d003404403598984d20f04c0c459044032500d00c0c0c0420042604140c440c1e92000703980d030051240c52036100504200c0303610740510200845079074001d1000350780040290680448038801e48001803081440172002d07442e00d100010001c20041c03000800500c800310304202e92040d43d80007410350030660412a46610340301c240060202c00d951001ba801a45010301140450078403043c0440b0181e40e58484078500003201c081c11006010707008083d110790000400480c80324070300c3c43c0e02c0c1780a1000f07580c0c0400d0075600d00551101400c04400420b102a9044c415a00096404800e5400b01d80d0112030026814085002141c054a034241214005916050010498049200190038102c1c880daa60420f2070030708105040e924007a80002c250076500c24071032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 362392715 1250 362391465 362391481
    0x60109020702060c010501080106050f040605030d0e0102030708030a15211103070b07110319111003020412061d03281b0b010e1605190e0307030b0a060b040e 69
    0x1010389602c081c00203880d104821000a08581d0207801c107040d1651900000c1101d40ba00e01d240509504084400b0441c0070300d40800695959903105400092000b54004848940c0c02030059401c03098028403002c0e82c910700780c07810034000c1244152440c1141c02d016004100c5940280c146180c5600305903200010440c180c5803188401d000c985e0b07a9a044c4124100400c0f02d0142c04081d00c0d03c00d101d11311034113408291404060801e00c2d001d44038050002a50344a00c0412120a081c09002d4025210364a0440319032000700d020f0b02c641c0c1c0042d8a40d041442100301000129440b04050f041888040f001405142f01080e0b1a0722408610546501162240603002803940c0c000340c83e6a0f85034105001c00480c1c4641e05c01003440c000300d068414100d01001041004018240070754001800b10b040e00c02014002d401401c10301501c00008850620f1203107110110b80a016800600761004007100c2c03005903245400090044111400300c0305608080c400990a0b901e030058500340c400c44485580c280e07660444e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 362393965 1250 362392715 362392717
    0x31608031204060609020403230f030f030709120f2105041809120504171504080904150b040612050601050910050702041506030c021209010f0509060d0c0206011706010902 75
    0x202c01d48050356600c0c0c0016040607184014002035200f011581c44135000079803c0360071441e10011010841d002034078981714020012048500079110007140c0d54498441180c100d920b1407164102c100e140c170740000148280510080032006040c41040f10388100d84001c802c1e000e008829400b01e2012800a04c420302866025020b8a5403d400000001030025455201c0c00c4415420300c040d0780100d4000542801001c2d0845042140f0400c404000c1c4000c2541850315078144000510180c540e110100d80d00810b66110f81000d0005083c100b05945400d46462845910354002d02c161404202c4007081d804010031507000d524882d050584602d818409000c05004400030322016810030007804001000c0181d48902c1a42c0b00d881e21003400048203402d1a502904645c0494004415940b100f608040c40a4034642101d440c920b00f032806103c1800e408100f643c00f4010750440e42d80c40007001c00c070f5100301c000d1640001c0c0b48400a03030803070b01540d9942000e4030035a40da8061192443d0040b0005120403030043d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 362395215 1250 362393965 362393971
    0xf0102010e0d09031505070e0f06090d0302060a140115110319030b010906020c09041e060203090606091b0406181701050a24090903110a110316080312 66
    0x200000c103501d41c24420752814494100034080214414480034414130a91441c00e001c1c44c03400d5481000b260400c0840940709014401e0464427501009440b24040d031a008203039200b448025000c0005002c1610b0080c2d15040115032814801d032801120068681c82062454101d42440d6401c0c0c00710b00b002c0b0b03000c40b100f002d240354545030b9120800c5614102d60b0b4502c040c10b00000d80355030005852803039100050854803107a00040455220300c88084040e914440b4050300309510405260b03003204092590720403800b51000c0680360600c00700420506620110341c41d4071070402140d00c2540b542e0362a5004141d40071f00390088038007a00030300c8180a41070161380074808481c0d05a645c243c2c020b9884541d0701401180d400c1000303040e51140c0921507245007500800c50034868104020007114121000007204004511032150103036210348401741858013030020f42c00b1151040d0150351400c0c05500780500096140400c4070f000380b00b01601d068159030002500802e9407900d901a515001410f101140c240c0009 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 362396465 1250 362395215 362395217
    0x60315031e050a0f0507060305010b0c0d0e030c0a0f030c080d12020a0306121202010f0b0f06090402130e010608070503190b01120c09061d0d0201050d09061e2301050f01 74
    0x83ca11900400d142c1800501600d1003400201255428000c000301130b564181e0220880203414003c20100110100e2030307946a40291a000110590410000e49002001c0b8241c5801003090344001c256600003080e48800d4a00030114403217070310350301c408040d13413204032a000e0b400141481e442c40303480b1812130f00200740030358052501180d081e442c0c03901c0100503020b02a0441d122240e08450340c0c94640c0a0103411040340c06280c04001d808205030101d140100c2c0755080c60f12481d4000707a54030301c1e40d440c0d03810381d17600c1300d4200e421200007603e03844540d010031000c0c010580880d001900080150313109004507881882c02a1011068012400ca85d001078102089854140603407024820b541300c0d014424282c40018641c5d994030311519142e0007405040c550549401903031f600000024030f503100d00403079040700c91707080c82d0866440c102c4d5109a0300a2001180c004c05860404c20342d600c0142c07001030724420081c0100c0c41005000f0000f4810400d070a240c024803180c0c0104040100198680b42c02510080c03201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 362397715 1250 362396465 362396473
    0x305030f0c1606270b09060d0f090609031701050105040504091a040303020406110c09010e09162c0906060105030a090804030f142806020c0f07060315031e05 69
    0x20082c41099500700354000341c000890901111360152201c400c01034400204080c9a8585402c01d00501458030404007031034020000045c18003240080c0d54003459440c0c110f0354040150003418606a000b60407881d50580c0001c00c4013028807803058070a11103604890058444504c2c07d032a01d0180710160041140554040004424107603400d080751881c1071040d40f20342e0b00141d07201d06140001c0c0800d1003207400c00e02260b04c030384400b031001e8852402e0079055070070b454510f004070f60b90190384519100c4521050414844880703c0011074000b100b886910300320800900583c031030240c407040714050408881c00d00c059031100000c51050b5005600550b00040b604c8004190001c0c81c1d1518440b035402a802215401c203107640c01c0060120b008420702c50801280301030b0003040041490301003042c01e0340c0714600da0614015024020040280c2c103e81030010081c00b80c84e00e40450320007803600d400d00b61003604042800d108001c088202d5031110700040d2580700501032030490030401d00e058403030007101046800b445 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 362398965 1250 362397715 362397733
    0xc0411040609050d0f05010f060504050c070201170a06050604091406060a0507030c050709110d11030402010f0e130501060e0906040c023708041814040f03140412110a0305030f0c 78
    0x12085c0600d4154448c805d50105080b8030b00b40c280300c2121001440764001442c01e121f4100180c0c0e204244041462458074030004940f525507141004207050f5200a52100c00010f0004840c1c001d6040208054101c030103003c1e0359503070a401c1c0400c034480c142441e40011700401c00940001d0085018100c400e01407011a4141900c07816060b049548440074400544008188050084003601074400e01102d03684030542141001e60001c0c02c0c08085c0c1c0810f0060094003010340324076442d2401314120603031070102d040c04035503034454002c0d0841c10f00f883c045014a04440000340c0500f043d0050700c100d0b40c07055008010300c0300c0740c45001d41c0c80071250301c00064825a10808150308004d0024030350100303000b0101c3ca50384e03501e84110300a40c454004140c000c0b990800040004000110000c19427160b08000c0304803420407c0e25003152901740c4d600111100350300104000c80c0e1140d28019181c0068407600d0380701000d0030108101b0401c0d4500d440002c00310b0703108102c0d4001e0066032a002c0c1003600801802c4503d014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 362400215 1250 362398965 362398973
    0x2010c0e0105181018082b1b0b0106020c09090714040f0c02151803030112030302190e010e01030e060106051b0a06090303050109290315090c0411040609050d0f 70
    0x30300c4134444800060109000700c043c2081e8601140001d20700880105a00156100305000d00400d01c004e1001c11003028880080080c00741c1d00751248024a402c41c50388184492070710340d074007100a014460041c0b040741c06000250420682e5140520442d400411079030f854100c0758101034804040c0580c0003902c9440300c0a1880542c05480d211552540162140148078803206020220040100100305403c80c0c1c0d905440d00044201da041d14030000d0b0b02ca400c1704040c20203030040e10504030303104030200761005c442c1405070703010104403440c0f0300c03d984040380044007000460a0b10162038417011a1740003d0010003010340108000e00d00441007440101d100c405031031015082c80c45c41c1000b0740b14152244102da040640c14420107024040c0c1c4241004184011080c0c01d0304030100c2d11800c0102400c008803c01c040d6010880b8410022102440001e80e240800200c0c0d20350049070580b0b40103034205030f0490804102c1d0303400e41d07041d0b0700c03240d0300c07212003500d01010410074001080054401f00c0c1509050401700d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 362401465 1250 362400215 362400229
    0x1060b030108010515060a0507020402030a020909090106050301050a0902031e0f0a030f030f0204210c08031308150609070f0c0602040e1905090c040504081201080d030b0102010c0e010518 82
    0xc01002c1d00015442c604040f5680c10740c904001c40034424481080032242540d0050b054910540c1c0640780141c40e503a0f100034040007440796001c3c0c99031185910081110010054020f40241d0314142c00900ca04d49601d24140141d5004040003589508111740150015803003a5000c40c0500000c070442e003a50030901c030a2810722903e00016000a1f081f40089802c0c1031305400756120502d0f603090114a03080c94a5041c00d05820301c04e11040c0c1002c92510004240419283d06101414a502c25070342e40da0614000f1228110242c45860f115000d1031450222060135501840c1c4110409040a8501d0f038503904200d42c0d0302100c035030a07818881d0104190001c964284040c00290141030054640c0d400d1591003586e00703842d0218200c281c81d0414007000340d0250301040c10803603c202581c01041b9529285000d045d00c1c05201e00716851501040000510000005020300c80e02180d51010484850390b5001203090b280110b04c0c540100384000602c0314075502c9500140050307802481e903c00f1080d500d1000030b0203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 362402715 1250 362401465 362401469
    0x90504020d270506011d2205030406050403020a1a0a050c01112a0a05030d1802030a060507080a02030609040321091529120f0a031806030c0804120201060b0301 70
    0x4500c0d202c10846080000c204501c43c09003841041a13020340c0703100410103000f5203004051006022402c1c400d40783c400c00c010640388403140e0140581e6295525118001c060340c0040c841644a80940100045c0c2c80b040151619030031004281901d1800300500000d8486500c454408085590380d821003100b020380c20000342016528141c000382c4030f500161060344581540480718842504903406500020b0800001c5420015130b00c070000c912014854040039a0501d010f00294160280000e1801000040c1c2c0c0403030702c01c01c1d03281c5032100c0a8482c0034607c0128041158210f410080c0c410105011901030206e4415441006019820403643c1c0c0540b90261600c10404480c014540a440803140809010340489004a94002000d08001481c0800d0b4114074120a6000c0d01078600141d006020a10054140003048421680c0d00303440b9141c020107903501d00440542c2d04181b0f1102050841c800e004a0382c40c904113940350b108944a1352906112001c80341d10900540d1750fa4140010001c142c2e001443c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 362403965 1250 362402715 362402771
    0x100305072c01030c02030c0c100c02040203091c0207080c091b07050606040b041a0d03020733030209030a1104180b0a0606030507020303042a0b090102120a090504020d 73
    0x14010701c9a4000741c10b0310360903821241503420500c003090000031b0001e17012150003000c60b050740310442c0281003a144074455035030180d04103000204000b003803c03001482d902030b2071442e2000072150301c0226040f44c4403809800307802001e40007600301c1c41c03091802c035a2664001c124564035030244d100e40c0645603403952103113104580d15007021040013918a044d2058046009061b10180400c02c1c84081c900c15040d9803140392841500702505580a0620800c03014024044003482038515120500d0780041c030700d020006002107595500c5003150f000b8400e0081c0e40e80c410026004141c10342c9540d403000b0080406030f00e030703030707009543ca40418101e418403007029009140a0704c050340840c1400440c40d0243c0d003842d0412402d1608120070b01840c140d00004490780607810a240701ca56040c51103990401e80303800822991500c414102c0070410403010001850440000d8003100d118001c4144e070003206010b91520b090205090500170049800d1680041c50907010300800028001c202140310352502c00c64100800d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 362405215 1250 362403965 362404037
    0x118050a03090501180303031e090c030b0c1908070c171e1204030513150806010314070806041503020424080a050d1b140303091002040510030507 64
    0x24140c02c19068005081c0a05c4d01d512654109111000008101e10000b400c1691300c02d00c0d1813060341508a00540c405003203500384a80c0700542061a40300301c0c4d5010545e40c1500e6900402c0f14424941c0440c0e54041d0003120404e000d010151041c0c0e124600285190240051008104001019281003400c3c00904810941e00c5296408580710302c0c8030a00b088600120302004604ac0341280300061035407155152504540d40d40e449180445804d00e60b41c04880390303e081001644555401c003001c03521500c3d00380c0c0d0420400b5814000303444021001c0d100c09011030000c8003c208a814550061725001e0712021402c01803d580c0d070b0205044480c0742030007181d0641c040d001c620b0703083c01d0400210001c181c00d07002495542c0c0f050315150744400c90315480009002c01304001000d0b110040070744c0a009a0809800034944156100d4180c80f82e01c100c441c0c3c4014000c404a00c15080e52034400c2e54261500900010107000ba0313810203a00a2001410300002d11881c92000e5240e010803105a80d40300900c4203960b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 362406465 1250 362405215 362405233
    0x905100f0c1805132406080109050f040c1422020304060e030301030c060c0c170606040f1a0402130f06030902030c0f010e0906061902010614030307030504060e03011805 74
    0x1003400d41d00b554042c85002e1100d10411642c0c0c0d03007035450010030404620015001c444a862540002180200080104020721002540e00c0e000142641200c00f0036205202650703e03924010001402220300034004600c003141404021080d02090282210281c01003030390685603180c902c96107061000d0031480f29000400c00041290a0140080020b03402c0002e508650440c0d841c00d80c50425405650100b0086900d00024081503072044c10040004207400703590241100e42a40c4c41d05000c40b01540110f090051f0004190124400c03003082517120860002d82c810710303e0410010354400c005030701c0000d913241c2001c62800080d040c01c01c01060b06840c000390b000c29500c113250500c0a03a0842038800c4900c140c00c0c07141030342c0091031029030714030071100341c4000da6a401c0081e07218001d80d0f0a901700e400080c0c140740e140301d805511103c03e845403500e03840c85408580c01015600c0c418040020009503082c0310804c113032070144024011104000b400804c14880354075450402249101c8191903a502003949 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 362407715 1250 362406465 362406467
    0x903090604170c0a1a03100b120a061a070201030213152d05070212070801050c040503010e010e03090904030932030d140702040908070b010303090806060d060905100f0c 74
    0x405501c00e030305864044c0094036000722252030407011001403852800c0000010280794850205030094091f45464035203852000e1001c1e58544821614941e40c946419030126404000c8204034019060302c020240c0740030041c0c0e004401a4000c511151b10310f074075a45002c511407003a80410410741c021941c4042045130185003103004d806034416180e0480341800303d0080d02c030b41c1c020101c0751020f030103840202405c803e07148424909940c5610030011946020148130a00340907200030000c540d8210000e00840100004580c01c03a5100e5030400c603141c1c01000300c564142003a50040c3d038010300908002c91040d54442000712894014031089a0a410a002100d038000c20303400c16002580c0140d00501c6800034544010300385110140d0400b208190104000d001c40d6100d4000884040e8010120b07038a50f44c0d9840c01070300b50a02808210040345d1074000100b403d000c0020302910480740242046840d96164540000070034400b1002c0c1c0381350180480f0555002203a020f5603500d102c1e210000104a03d10b150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 362408965 1250 362407715 362407723
    0x6050915061b03190c030c03050c0a0c08240f01050904050a08120f010e040b06060f09041e050106080705090d0309050904050a060b030a0302030d0c030608100c03180218090309060417 80
    0xc130301c4188004200c0309400b003603004a083e0f0301c05500d420b00c20303070300c88a83c0c040c1482c00d40f100300001e10080c0140404214124003181a040b5019410200a43c034903541841c200301103400c0b51062150501c10004120341d20340000507a81060043c415240000c1c420f40360f0340c1d90323a846a084480c098281d03106104113420300030f194034010032141e039807114141410741d03a0849240c1c0147c0204e2080e5004034203080b0508101007185c0e0035100040003001900841c5440600354803c6811126006161000000d400c0f40280300d40d038402c0400341d5542d80760100000812502121002d425000c100001c1c1010030340e5207469528030700a40c0604000e2070000d40c01e2405006460324101c0c5a4040d401c00000580000e800200781c4100e065a0300010800c0390031b03480d04a004040d264840101e921505203d00e10101042c2d101075400d041d2661b013801084503441800100300108000250007000c11042e058203840501040d42e00880c4480c252131030030381e00700d0005181e46c200d034000b61085800441f15102400c2c0800c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 362410071 1106 362408965 362409007
    0x901030c05010e2215210204050108010605030a06020d0f09080702030610050f01050711031c0909091505040321020a08060909060f100807061e0306050915061b03 71
    0x240741c0001d541b5403003009a01031468003001080c14601030203201c080d984081c0041407900030f19a1040020340c006c1a280402d19514038003080842654022000b003903024501041d01d918840c010581860b10141510840c008102c4080cc5281c07100304090454513000d091180d1625401d00307102c0003040d400d1030b00075418051040000c1c01400c40403450482410565241b806079522415000203e4403119805405020001100001d0944641101764080d1091032b106040000e881c0f82402d04001d160790000c1c1103500030501140c0760303520054039580140f003110509201d00300301102d2a01c50703002400d401c001d1520b8038009130b195401c0f00c0a032801400410100d9209590741c1c5030040140301e400200212540c1002e0580b4001440307405a02c0035540c000b00121500c0d222031141440042d81250460f40048090207042d001095103c003030422009020003940c0e541030800c01020f0003500c0a = true := by decide +kernel

theorem cover : BRFrame.Cov 362230215 362410071 := by
  have h0 := BRFrame.cov_init 362230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 362230215 ≤ n) (h2 : n < 362410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
