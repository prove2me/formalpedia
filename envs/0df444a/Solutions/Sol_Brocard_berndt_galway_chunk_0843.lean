-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0843
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:07:14.159667+00:00
-- url     : https://prove2.me/submissions/8075fd45-f9e4-4579-955b-25dcf215d289

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 151438848 ≤ n < 151618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 151440098 1250 151438848 151438879
    0x120f120601210f050a0c02060708040c0f0b0901020d02072d03080f0a0e0a21051507051e1e0a0212030a050604140106021b0102010b03010905010c021506030309040b 72
    0x240d1103240000885a44284500c919001803181c4e41e03100c940c6003001c2281201d4044082d503102402001e0104118080300013404000010802c00002c007078940b0041e0305a901c030031a000440d0000482c203801840f40f10700c1c0c85505840080c1c910104ca41d1000f0300030944a4074160b048036001541162280c1e840c00032030000005d108140201810301c0d001880580320a01c00ca00140414441d4050074402c01d0054800c2c81902e0039000321106c0c03126068010125607030305141c0b0034103280550385103841084995040105843e00304000b0100250014000380745141c040c41e14121500504c018203010420000038454417040d144020702d801a6140121505101c0d070303620300e6100b90710403500e50551980703135414422503040600a806402c00c24a50818840d03060600084da250800f41a4480302c190020210020342d000b076014010510000d0000d210314440d5003050790280140629a02c018032420708100781d040804240700380140c00040203140f4040c1420204000f501464140d13540c07142031a44408074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 151441348 1250 151440098 151440137
    0x70b0306011419170f070f050a0e10020f070801050c040302060c03070503030a090c080d0c200310090b060109150507080d0e1614090612070f06090503120f120601 71
    0x2483c6035a980c1d02c0b1503074030b4003120000c40409401c44211a4602c0140300e411508030320255849500c03441c0c059110310f01c1400854128511003649038100e1052000708055503400b16501c007803a510101110803680d80d4140b924201d807011070b2804544001844180014940a0000e01400808000b100d003090041e03203d142c103560094846000440d034803041c401c1000041d00051000b80300034070182200c8510359174058030103e00540000c1280c66106c1d203100e003141c0a26100140e1440c00790880d09403041c501103040040603082c20030b07205201c1c9031001544540c8201042004c0d03a045c1400c40130310210300c0409032444e81080c14104c0300050244a05400d445c498458003540c555030344018600c00030348000d20200f070506a0048940b00201001e040829150909141d030403880a6a400502c52001c0302640d0501119400030002c00d401c0e030310300286071a4014581c00a60f04214141c0d20b4034801c007000c404881c494004204c00e2090144101ca80c1215000388640d44040103051072120360b02142c00c1280c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 151442598 1250 151441348 151441387
    0xa05070803070215071a0402040612030c050708070302060a0c031202030c070215031302060d0905061e150904030f02010f060b040306110310031502090d030905090603070b03060114 79
    0x2032a5500c08038155080d0301d048220404011a003516940c40c02440d5143c24491510084418440000e484046411034440390702900041183c90043c1c4659082441e00400c2041005025521486000740224010101142880032698000c20091a207010280709030b500d1100c049041e001e104869450401c0d1808a0000f03500c0b6030a00304013075540b54202d2041000800da031070791130240d842c000d00802404a124450200599030120f40658645540380039880140c206000010082c3c001c043c00d02000c0c2d0490319090030f500c41070700d40d01c10080d0f90310702e0142c403e0311300d8404455100d001d4002050209001d6142c00000010314400415891405003281003654005d41c082a482c840008042051008500c03031840c0041c40e10710400d1960034520398030004910310b4080541a01d0000c540c2c0c41107103a00303034112204404090301c0c034015031001d41000703070007960f0714230803603014100100c0002c03610300c1e000c2104002d45080d607524600350744940c001100c040030f1140034240e184008003e54251820a408001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 151443848 1250 151442598 151442609
    0x9030204060f0e0415061505070303051e0c1803010c03021b010b0d020103050901180305032403100b0315010801060e06030604020d230303090115120309030303091104020309061807030b04140a0507 86
    0x249c0d4410003490001c00712540104034140c00440241010102c0c41da0405440d00007000340ca01a031240090070707503070009500c10a0748580c9903207441044415990150064007148000001280d94400340343d00403801c0c0c034294802c0c0d551100c0409a10001076000707501180e0002c0d0408000204040741c900181042340c4032010641c00315030003204120b400304240c4407100310310380e01c82500d1a84103607d4011982d0740e82e845a501d005203407039290521303580d00c04005016001100d400d581429503591040640201114010300000f4200c040014105040000340c0c5402a0781c0504400d034511a140c40d07909100c8840200703c0711400300700b00340c0345400e1001c002550083c50345400000c0c030800ca841d0340f14083c11159000001488402c40d104000c6904251080212034140c1000308081c1c0d100d1801d03040c98203110081c6607001d4400310034002d83c0b0354002078046c4107000d082d40b5010380c52030400c00a56186640d05c0014004041c1e0800038001884000c0010480d210001c21502c80b0744040d030312241401425000b2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 151445098 1250 151443848 151443857
    0x1206060301050106031119110a030509090106050906180a271a01050a05090301020702060f07030207140a05040b12011b27150c08030709030204060f0e04150615 70
    0x14025546828031035a40102124181001070f8891071030080030a0003119441c008641e8410840701d032040c020507025194044d814113403070101d0780070302c0d02602d560001e605150141c145d890006c2a00d078000e004650751054000c01c01400c0187e0744005095180c0225045500404a802c000542c0391400c0d02584d81c0529280e04120300d0030f4515245001c0791074003030b032224201d02d4484031240380380d80001c1101c200e02d101d4030f0a00e80c1c507040354020a02903c0380c00d0009400480004080d40d80128000151445030310030350035201061380d126a60740064514201072a4032080d00c800030452890650b00c8224004c030081c02400503100780803d070608460284908441c01001042c01000d629881000b105601180d9103c00d0390600070036102681408050240c00c5d003d080840121303840500401c1445c00099010400d20f549251200b4000d20414840c44101c2c011818910040380d40b820821840c001d641c0d401202000c40d40e1140c0342c180d41d11829050b0024a15510700340400c00c0300002c101500c03040303e50748a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 151446348 1250 151445098 151445101
    0x1e0f030a090c0801110d1109090c0c010908030a0203070e190b070c0b0408070303141207030c0c0b1006030b04060e0c0f0f0403050114060301021303080c010e010216050f0a0f03080a0b1206 82
    0x100010303104103201f0b0402c82e5404101e460700301e55425803c96084411104000c3d181c86080c408a80140701010001e010450003004002e107040664000710710900c0c0300d03543c003902414014144803561030000f034400e4a8500b000ba081c0f00c62021100a00781060143c0f1002d081ca680e50b0380743c000640d11035004101c158020310024001d0642013a0000060303107115181f1850000c01d89840d03450b050014104c4800c15803505901d40c821740c42825484c96440d0081c0300e41195052440d111429018030f84214008241814980c04c00e61605101e400d040310300a0017071200603030782e14400c0c4065900264003148090002c0c081c42140c0e8244034040e01c05584500000682e01b02018040c002c6004004c084a220342e0040224203003914554003040c00302c2e584a041ca51310b0324204034100340074010303540342e42540358400b04041000b0200d4015540d91240244181c03240031103030b200e026885072011940035206203610401d101c00a449007098503401480c200303001982030760304000111405000c461946880e0b21400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 151447598 1250 151446348 151446367
    0xf06030e060f060402031018060801110a090b220305010609050a06030f0f0206090d050604020a050102030c0d050d020403060e010b2e050708090d081e0f030a090c080111 74
    0x11600d060803180000400c5640703807410314000b4065005040b54050b94020000c900001141e0440d02e002e808880030000d02c4000c1045a200241100d2281d00c0d1213600701082c25100e030b1552011500d00150300e41e03400c0c0c07640741003840080c8140c0c06501e104441e03401401404c98200e0815045070701940c42074001040da540381002c140152030015110340303121362401c03000704006910400c000355140c1d4006200010700c02180005060f038060160401c0e00718110010f0324040120105a00e0b00c03503803003241d075101c100740c50f0f400480e50381c0102d52607030000754001d140a900190017440034210600f030382c1e4000740c45c2175100e540d00003e0781c498025000590f0344600301c0c2d40846c070704402d071010700300c0854401035540e0815a841440c0304118003030030310a00070002220307400d10481e0b0080b2001030001030803100058843e4900501d26900090000f81c1207056103200440c0d80c4551821500407400b100c1801c1e046885a8003100020445014221181a40341c0c4000078480000c6c0641d201d041d5072080b00d1500d89403d00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 151448848 1250 151447598 151447601
    0x3151801060b030115080601032d050f060303030609090a020307090c0f020d12020702010c0f0b01052106040b0601030920030c040219030b1c05030711120709050c130f0603 75
    0x980100c680c101c010b100510217049800303030000c1c0c040300390716011045455650060740100300c1607010179001504d250041d07444042540100c140a20021410000c3d9520380c4001d050034942a5080f42e419002000031070300f285072401e449500130a40000342d60032003510740e002902d0719006901c82030240341c44064006115410007100d05858942d0f0000d84002000d07913800610100c3c0c280010002254042142e6040da40301d0401c8081d10781d0b1103441c4581055032030030803a01c4079909106107842021101d01000040512038000350050f52031800a0007580c07159500c041296138000c04941c105551240e15001003407031038842403100001e010443c05443d08110a25003898048990f0902031401001590912090300015554145261400142c0048000b0004d5800401d00858284440d0880d0743c0c0c00c184203020000b40841032080c9030b52001d012411042c0000c1c1d500001052881c2d4100d84420005129a40c01c00d940c011410941103180c051000100101c60586030080702100500d0b040920405415 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 151450098 1250 151448848 151448861
    0x31a040504150207050604110f09011701060506131a04031a06040906020304030c0b0703020705060a020703030b030604080409060509160c05100c02070e010f0e19020d0f05060405011502031803151801 87
    0x25549011180429000f003502902b040c410003100d541495607510070003200798072040140c0002400c259503425a0164400c0380300641c0a0040c0c50702082c0c9030b42480707081c448100d0b412641d11180d001038400c00d0301402c880115008159981080d2102085000110b540c40154400c40c8680c88071940d0000030700740800981c00c02048541414030401c002400315100003406544060080030140ea942e500f45400c8010340109000290144180340502c02080020000b500948043d10400c00465590b071b070412482c0541a03c00d40200780b802400030003038138842e81c40088201d00902c00c80f03103e00c501c8011001110120f074190030040c0c100c44030600000021940b0b4034018100c050380c0081150814041250b2440040c02c00c455907505e072174415109203d290181c0760841c0d82824108180c460b606004070103404200e40861217646450008034804000c003000400d07140496009500305080c402021061818006405626103e00710056060940c904200c03442420654815082811050445401d4460 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 151451348 1250 151450098 151450133
    0x40302010c05031009050c0706060b0309190804030305090118120209090102130605160605010605070201031d0d0309050109020a120c1401080703020a050c0706110d031a040504150207050604 83
    0x20204180821201074134403c20645508103000201c0c1e440300c80e418031140c8140d14000b4802802d1050002d000020000550300c142e8541064a080b0300e0308200162a601e1415401402c3d88020300003440421311450140c0900303003060521848116107405c1c8440e017001e040e480404007200c01c500050840c14004036154021807910025401d09045802103880c5034520f01440c003c11201044036074090380000c150350300b500d4000400300070b156180c81d002840d65000b5407099000ca41030142504140c0e5401290401c4200c4100c068400300712001000c038040c1c0800e8a044d109076480d1416000540c0e242c40c02c081c0101b501c4d00210035580c01a244c10340e4140d50950150b520800a2402594203980050502d0f60210f02494010303520124154182c95900400c2c40355001031141280114030a5000b003162592451100300b15140000e404c102241500d07801800000c160941907802012401c050f045940c2041c498009481e12542100b10081283c200f00720582c8e43c3da200710148002c2c40030121200031580c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 151452598 1250 151451348 151451357
    0x2301021920060c10090503070b010801060e01080a051e0304050402030a0203060a080f030d0b0a0e0403020f211902030f13050a050f0102031b010e25080105010810050403090905010905040302010c 85
    0x14200b010f540714110b4a442d111643d03110054041001014411244507940c0b051240c050740d6124035025009002038000c0e0348008102d00d00214401400007400c4800640c0040106408111129280704c032401100401e5000e103c03e000101d016030f00d43c00690303c104101440140c803454060200b181c0d880140d070041140c0e401c09001c000503588044120707038598a00321004951006000c007c112101c010750705c0b420313044044406010406501003940c604003002c000485010440340d801c15040c151081c466041d440310700300800c00d040c0d452100700c82d0710340ca11b82c010380b0b00b4124900e660b1901c0c2da0102920121042070901c00b8426841d15503545400780c10243c81c1401d90801100001c4c3d44e900c59074110291a106108001d4400b0720250800750030902440b05030381800144840b140416075680d613000141655a41020811a005100f0141220b401000078600f405140c0710410040c07001520a50811141300e0001c280092030b03029a80c02089129800a00b6242c00e080003400c40f00c0c050b840c2c40410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 151453848 1250 151452598 151452607
    0xa06050105040e1f030305120c090d02011b140f120f040605030406090203010c1706040c0509150d050403090503010b0a0303090b0f04051e090c04230102192006 70
    0x9076401030a41d001d561190b0078900403902c803650035140d0801040e01031100691820b20210070182c7c0040506010500341207508266200c009070450a0301810f503130241c00c4281a035038075015620800d05030b00b035004043c9140261080544811900001d11114541c299108480d4440c007000c0812280241255100090742840010461200079200e00c1c441d40d406c00001101050a101c141e510540340c20b07a0080c020005644c400c54050001328424912103d039008003400983e80c1d003083c0c002c1100901c0c0c95a145450101d0102c2004111102a641c00d8136000742841004510340e00f900c00c1c036000714002c0c0c8039601c17040c0c039003410182990350511003d8006c0c100d070101000001c1c0c000d0408010313944030810701d58561440c00e852004a0050fa80100d038400300d282e400c4446900017900381e510b28a82507446515507901e403d0100384510851060308600c01d1800440c2c0c0024214500c0c0840e03408051040d2009160040783d0312a1030705035000240d801400c540308c0719078443c41c0905164131464041d119181403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 151455098 1250 151453848 151453859
    0xe01120c0605090303091e01090e04020a052806050409051e0c091302163c020f031f050901060303090317070b09010501180207050c040b0316060e090a06 67
    0x480d0300341d206003030074440c010800395401c2d80c0900a03588580400f500c40c20700980c3d401c1e180c0b203070030707600100c03803408589803a90100340c0d9128040300a10403a000381c1803000581c500418000b11720700b1071100c0744002c060306040d5604441583d10302d100a041a0b170790151560f003402e00c124201c42d07010b040000201511030755880b02005400240f41d1080710040c4807603c8a071034801145418401401d548882440041d8840c0f8000c410030390441040e00440034038000203680f100780880d45a010b012511024443c1c0f4075240c031000310889040d0320354405050f4180d05002d03000441d00d01140820f0000051020009441841846100e600e078840ca8900081c0f2000d0f255072005499440e82d400044c0c4180c2c011003c2c0180040d840040340c0f03011f43d100740700c03203581d15240008034020102800350a007141491030f402014880b0a0083d60b82d16900507024280c10f40000041100070411101c0c1240c0502a0310b0301225544540f60840b80101029120ba080c07190101c010060024030050035858010301d010070a000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 151456348 1250 151455098 151455113
    0x9010c020906010909060b1306030606050f1c02030f0f07030501140909011409030406020705090f0a020306040902031f050105060a021e0102040b0a03060303121b05070f05060a060e0112 81
    0x11500d40544100010780c40300c80040f160341146801c243c500c5818480000b8003442041d00405501040315842c0d5900c03a02c1c0e0b4000c4094480501c07410700018014000091030410400c018a001c8030001455041c2c1c14030742441e0f009a0f00216046000d9208010401452001c44030302d06902c50710b50301d020040b540c182104c201a0b101040e041c940103090f840b002601c132100c2540641801108900d188285107810814185e5a60050007071000500490000003aa4207190028500904d1500e007400047e03601e54807031310b0094000402041e4000c0d04da249030409a00c00b40724201019000407400c003903000304500034609403441a400180108400c01c010301540d90702084101d1070050040414403a1410f00000c203029000e41d401c03014404800248131604243c00d54030500c1203910075142d0310b00041203100072908079003002211450007064003050710744140c030407401004114807500324055400340c00e07120b8078035064003102c6c808038140c7c1d90b840500c0302140c43d499407401448040c13910514460325a5900c038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 151457598 1250 151456348 151456367
    0x6040c08011701061e230a05100c150203100e0103050303040803060d0b010609061403071409040609050406090203120a05040e1008032b0b0a0b07060209190e0c0901 72
    0x8120076006552103000082c2908010020190b400710054915500d00d4040c0e4401e45030b20a400144050303c3c01d211010903401282c090703c0c40001d1400452a00d00800e10140d9040032005504000c1096a03c400041c020007083c2169802da510060701c919044680e100d02e1055030304012030800f0b9080c0100005200001102c0d8081d41c00213920791280c03107010201c0d00e111a5403030700401e940c107103200109025501086c10b0084845555441c1181001c2c52500030309884141d44075800240307400d0101c98420b110302d008040c121809400024201e64a00340c80c001c1b65004d0320304075000e940322813a01c0c0075481c040200d43e0040401c020520328002620501600c940300da0710a80c5090380c16400010b80314289607001d8001070007034109490740d075206900c0b070310103042c04000740c0042c11140c2c140b0080e0402c01c610408030403c001a1401003880e060415048540e001141c0c101c40e515002c004d9215145c5510030100645031611549106090134221112111300340200212003950060020b40c4140c1c1e0300c8041070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 151458848 1250 151457598 151457609
    0x2c09010b131a150906070b04051605060a0309030e270915010e09030702091503060c040f090509010906060f031203050c070605041407060c140102030928060c0302030f06040c0801 78
    0x283c5030070141003a050754001c1c60210350b4442c0c404101c0e4010b02c00c072100d545103c0d500c16003d8507588401caa64040ca6050796010700340d000341c030038000c000c0c006019501a02c1828080d080030088a0241d0b400a41010348540111003c000e440104044503814010781c01c0d00301d0080c00c007601d40c0c40e00d0342a00404080051040c00c0c2000ca403140424401d80052040391007198014020070200d1400452002404d0705036904a4000c0c4120000a42100c2441060300c00355140c190b03004246d01d11741000380c00600406440e0421035542c40000100080d024030550005141034824203010038610b0610250444041101e4000e0604002c1000648d070305400450700c1c015072049001803180c54038100a1000284070700d000f0200d00c5000404a03034075420150442c0c12501c250030b01c000305413455070002e09074001a119400c0591013010040505880300c1d1414101340d401c010100307820b90203611402e041d40c00302e0903080042a4000144950544500b084940c00901900c00788014241c1c44001070400c101445003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 151460098 1250 151458848 151458859
    0x608070b0306100e03010518240a0902012a030f081306022a0708010614240c0105100603050105040212041704030212010608010e070f2c09010b131a 65
    0x2005180f601600044000180103030013048245000050801c501481c1c811484691044000c200c0c2c0750001d0000351818024994040034241e1107030b01040002e0065081e04034140010209021444008c00c00941c541802415007040e49203001d09015088802d43d4110400700201c0d02d0030498174503000038200d01341d503920800040e5502d40005040f04c8003c20444003201c03076002a00040d482050007e83d210a85030740100070001c5580e28a081e084100d40c0351305145d0000c02001c0c8001c858101c6820f901403410824609a00d001c4003c2121400c40e04200e079043c0d481c16121809204465062203041d025210070350782145004414404441c101400600081260042ca0b100c0c100c1920b014003981c000b0b59020b45030b01138400500c44210b010704058001c21b0050762030050000d40e503803000101a000ca0b52101c2c90100245c0c1441b4035030400011000b48010004401a06503940e4510401554420410000002522007004c01002091701001700800d2041d03084c54003050007507980006001d01c00310100d45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 151461348 1250 151460098 151460119
    0x60910031a0c220302040e0106050d0204020d022104030813081902030d090302010204031104060b0f0a020c100f0f050c03040e0907050d05100e1902040207060e060c040501030608070b0306 82
    0x40080b031502c103641d0340343c400b5108a01c98290310300c0c10681c20b1003903a1007154284005488081103c3c203c4055204039580300e4485000c0c040903062950080c4401266842d01510303101107071500f4010741504051030044a444481040b00341a800400f007500710711602c2d241d105440b80c5071110402c50003080c1244885048840e02228018002c10803912524114041448801088d080c0a4001d40240c030040c0c0c1c249134050f403c00711601e0700388100340a80704c004c0081c50500c02c04000c0c1d008250403100780c0e1410351240903a071720300b90b0b40c0350011946010042d41c2d40c1092010481e000500546502902000f4800305100c1007a4609010040e02e0507500f428500107001e41e5602d070043c0c5072520740d52103030703030050f000d0500d140c2070013000310b80c60030424244007003400b00540001c1456038503881b184140020140e410700f8280140340c5500104030786801407502003141d91501c0e0340700d81401425188804030703880c00941003085503058003d15004040140c0901590342c81c10b1b5541d100d52000070042845034660301c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 151462598 1250 151461348 151461361
    0x60b01090e09100f020a1b031b0b060f04050408090d021c0501020406140403050a03050d020c01060609050f030a020f010c050a06150504060e090703030311071505060910031a 76
    0x31000402451400745149050404006294540b1524840c21018900b080220701c2d04145a000b15074180e0b03071594070902e0301d60701345441b07100c4101031010850030010304050986503660b0040d103164040c2e0080310150083c2c05c05c401000800c10b68110001e0140707040c04100400316401005440c0020310648101c1c41110040c80081c541508901e186c620801d200301c0603100384035055000c6c01c00d03100c00f0f807110300041e03041d2020301d0071902039880004d00b0b56110034a01400644600d0140941b104c0c04a4050704000c545000d56082d0351b100d40091000410000c0d007041a86032031540c0382c522100940207001d042c03903141c010613070056104c03003400c0c140311140580c00100701c820058405003e4000c40c0400c262000c00c030610601d40814854a0710441c204000841c001c0101c030302c024010008a80100a25455541c00780d001cac01a85212100802060182d680410328140750200440d2749000e00007901d1404508008500e0006042c41c100394080000500c00140c4e203502d11a00d030036216000c0d01c0c0a540e442c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 151463848 1250 151462598 151462607
    0x1081605210103020324010b0d09120e100507020f1c05060a0501030213060803220503160f080106080709091e0f0c06110c0103020711030303070908010f1107060b01 72
    0x10507810300310001044407240c1d07080d007460066040e03d2085040d0344824072400414031218401804406601070500c0041008010035001030031124107082c000b044e00009a214000c1c0b4900d2002e8400110300c481103007030b0403460002c2d40920b0845150400a081280540105000a800c1c40006004000c40564031800c541c4403a0300c100745d103610004407031541c40c0004d00f600142c402072000300c1c01429007a408203207034007442c011181034a611000460510300c1d28a2244283c40002505c40c9000f4801000425182c5042c001441001001160801064540320070780400484640c0701d4046030f490400140b10b0540c021551004660801c00007040d00503c904000c102e0b60282103590f207222405003d4070b030401024040d1030340007501541c02c03a203500740d565a040e221040c0c1312192941c15000002a41070070740c00b0b5405007103468003e040c0340e40f0801720403012a02d5540300340d800300041290210204175048090141026065403032200307210300d280071548014103004521009000d0b50300c424441c42c160b4803a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 151465098 1250 151463848 151463857
    0xa03020304120f020d05090f0d20030102030f0f041113060f051203070b18072301030b01020c012007120c1202030c0105090d05060705030a06140306010e090f10020909010504050601081605 82
    0x521655441410b864140d00110100c600300380c00c401c1d8584ac10f980c1f460184203491003400e5610603200705540f082060620414000c204840344080400380300b00c580c848201d84d8040540c0c00c00001001d506090a019128201d6030026205001202c40c05c1201c05010090b14292035101b070f4569941e46a00c10b400002161441c80e03080c0d603101c0e5050000c3c007803400b00c1866548400d0b9580c0c80324110b04d8600110240c071542c40c1d07000d000da4020880c50700503500c19007800700c150005034580c24803e100c0c0c20403030b403d01a0f184d000104480e8514099400d00440c41548030040000d0504500b0944003640402d45034001298a241404404502c80c1d000e0740798440b80303000081c2c1c01816196286800c800c09070540d0403d4591460f480d10b04600071135106800415104420704c02402021720341e00e0a0106003a06100400e8801035004400c012201c3d19820803001e0b01e9121034090160b00d0f140351400303119100070164403c0b407150703080200340702599030000b03249900180d03110400021009902402d031060300c203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 151466348 1250 151465098 151465129
    0xb03060a0305010c0309110105030618090f0601080c030606060705070b03042a0e09070609050d020105190f1805010807030911030706030218040b0612040203120a03020304120f020d0509 81
    0x300a541c0c103071117905500c4081c82d42d1240c402600d180c1c031000f004540c07500040b01c10300d400050940c18440f03c20500380d01541e10864000403180c400300d0103600b65003081c030b0a030b1103608640d00880c10452945820310101d43d0100060300c1031400c1000075150f996581c0d590303100d8040f48100c000f0114041c171030029405600c031811148043c5520740f103190940c010700c00c02e110f0a12201c540d003000c01c80401340030842e40d044417181d940b02e03d45181040100501241d011900300c0c14000200f0070507900742d00d10b00810511282c2d03a2a04185c24000780c0c4090880c0e0b00c4003000a508902c103030401e0140b81e8104640a03000340b460300e0300080c0040c561400030660010502c9460b81441744040000300c031075050f0000d0000000c0ca52090550308408000d00040d5041d100c1d855600510911503d07041d80001d41540b60320a000404803401e8005501c4040c285501c42c2401e0000250004104070a00c03c4004000380d2058240c03900300c1032901031800007500d0301002c0c20103004021000402600c15070318042042e05041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 151467598 1250 151466348 151466351
    0x18061507050c031204050f040f020c01050408030115020109030f21061203090503030403030203031f050406030f0605090a03050904020d1d0d0f0c0201210e06090f0c06070c0b03060a030501 82
    0x590301e081103030341d46920b080028403030b00c1030070075200004204078296022540301070015040e080031042000068100003104000c281c0e0b007400079411510090083e03d024501501d0070b1a625410540103030070042a5059a0f41960706140111000941c45500e0303520882d070030714000d600c0c0c45d03d044000c42c90f10303040c40c0c21400450134003201041440514441610f200d03c00e49070410790704e64034820315490303004621024026810074030001d403d00384411110300400c520040b072600d00a4032140000c04855464001f0788616a40c0d001440c04c02100741314840d00030890710000c0000390000d950003040c81c816810160301a036000315400320350b00e4017034110040c001c8000020034021100e580e1083d50b01d0200740c0481c400204001032040e034603801280000c200c1601039603050800c80a2582c008805000c07100f500484aa8418100420705418403d49000302e40c048047c00329070700b1040a052074240510651071096508100d9900040c0400501400303e0b9a4022416101e0b900c030070001e03144a020707510282079035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 151468848 1250 151467598 151467607
    0xb0708160605010f0e04120e060c19151505130603021807021c05030a020f0c19050f010c0c1b0806040303050f010b16020d060204090921020606180615 66
    0x841d940e00154162107000c000c2981681d0b84a0001e0034088050380c000d0404000180030a050314840c69007024100409802507203050b101c00f110350b18016158882054100081c0c410404200402d01511060640060284080241c402c008280c41c0228400c40c3d00c00c580c5021b4540d1746080702d0300460000d41c0c00414850350644103402c1c20203003600c11034101006000d02c13158044404e0313807529820034525060381e0346401e40d82c3d10011a0000c1d80180011407003e44240000c4810307a108124550f5aa00712103000030b0032441c40c0c900300340b41c81105103004441d80d040240b090100e507800500c14a445800841003080d014503568a1080f682007074121440c0c900803030f01080145901501f082d40038490b413520302e4001e6039841d2860300e024024111405840070700b07104c1400c05850b0000540300054051100146001c2e030380c0440c04119031a102c01210100c8803a8440300d8945c8410309003c40106060010300507c0c640080051000c041c40803540310148200c07404030f542d039100c0c945040c40313440031110000d558 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 151470098 1250 151468848 151468853
    0x23071413080f0106082e020f130b030c070f08090a080a0b06090403050a2601170c0405040c050d060b060d050609071e050c2b0216030b010b070816 64
    0x1902140d0080011034821503001036200b03201446108121220103001e428000d84960072005844094408090000454019120400c151380300514000744010013440e03407004180840c5240392a142d0003a030800001b4010440c10041700e000b219951644191b80485100302403414489030f01410704034541012400e80041078845000030318101e1240907045a01311a5200c03c1082000304085600a000138001d206003c8004c1c0180c807070080601c0810b42d00418060054011480031400344d0080b40d44030604504010265400d0221401202003510244401d2a040d11703000c080b1580c61107030f207021f80e9248030800300f84034886c1d0009901c0c1400901c125a40c100640c407034009017000b40c800318442e007450740110f02094002d03c1e41002051010398900800002c00c0402da0b01900003a1604440f4010710701d402541301d00001d40c68548100c01094003041c2d0700303400c0009107031594078407400380c046010220038001301d0781915045044a524140c801e94810303080c900403645016400c3c00c0300c101909101c14904 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 151471348 1250 151470098 151470127
    0x50708060a0f0305030403080a110109050607090801140426031311090f060423011806080f10020a0302090916080903090108060d080702151c230714 65
    0x28400855140d04082e40760071625040c2041840004c1250b4400c1004000003036000004d080380e00143c0c200b602c0022240070145003501d0700ca0790111500d8114030104040207402c050418098103a140c02002501c444260700d2a00c598042c201134009400c10038040140f00820542c6140c0c060701d840c2041c1c40e41005044c1c002c403800c500404940b150f485107010100b60400480d1180b2450040c2c02102060725054103000052070101c0c0701d4102c00c194031441410440341110414001d00600b01064242c48041041c80100ca80c20782140215800c100c072001c42440002800160b4042c101c00010b941c1c11014100340d000b031140e92842c0b50414031750001c110040554940c543d11152041d29070782826561031000c10b449100d450002804215514041021130509030b2054103058442e104c55890b0040d00d0300000c20420207918465104000080c8008503100a04c0b001c800725140480c0038040c0c0c50501c1d10010142c0001000e41e0070901c04140010000f0f4810031182030144800a14a9580e81700b4120009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 151472598 1250 151471348 151471351
    0xa08030c130602010506151614010e0102041d1b0316051c09060b01020105010522200712090302010f030b0d060c1d0a050319030e0310050f0a0e0d0e04060801050708 72
    0x14030800d0740c6500403d804014000711440c0c0c081c0003032301c060120015500e0310684245415000c1c0300350350b610189664001c09100500c0a0202c40b21040f0414070040e1200c0c46101c0018010000e003020752000146d0a03540806032034004064011013144502000d604071100d0290102e01100d140042840c002082d5490b400507640c240a84000e016a00702e98005900381e440a1003450b40020315084a004a0751045048a05000c80e4813804200082105110509007889801180d00201d0000d00354040101d1860480300a45081c14450082851900041d00f008103416504087c16152040e0880542c0c84452012810b584010b0400a00c1b0b18010004c00403034400b0340c001100c1d10341c21052440c9282840c110012214002c1c01811401c45402184d035110280d104101c082c860b54134001e801070794061102054824038900001294504509000c00c0d40f01c000e0248110b480c6040300c1170030840e40101d0070600060b41402e20a001c040290301280003004a80d0055140d54688402d2204099020384002d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 151473848 1250 151472598 151472611
    0x30a0f080d150314061006030b01020307060207210c0b190902300102041206020f0f22060c0f1713150212130509061f02151303020a08030c1306020105 66
    0x220002c00f0206481744d44000580f109000e074484508200b01c041d101b50000e0b03884ea0300602c10b803420041980c0d07038001642c0001404940001c180301031084800c403000203203441c9041c02d280c102002d5015450303000e140c40c400b8041d00c0d550142d142049140c04400e400100b41c0f02e0740a003a00c45002a115080c1c0c2151814001e40c1580482103030b16011180e038140240d5085c0c9040c29075046040c640c684e1440001d40c007240d41034440b00802c3c0400d030201640313280035000d0200c100c0c0c0e078801a403008d2182d29000002940140c0305000c1280856800700710440803081d100c580c02a99501030590044141b09907000b54a4804c0181c0c520700000f045600782c1070400945111940c00700d4070808038041c000e520303a000c1d5007487c8c1c040c1580602d04001a01d420b417003094110401400103080c00c09540c1c90f29500700140501d11000da03002d0f00e012000500c400034425841070503407840500d00034581c0d600030b4039914100c00c064400c101c08008500c110491030116030f00201c414844c0b112080d41c1d03240c0031340a00411200c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 151475098 1250 151473848 151473863
    0x80d020c091024090512150c030f0423030c031b0a1502030c090d050d0f0e0a060302031807080a050d080c121f1211030c030a0f080d1503 60
    0x2c00c603141142004001900d050102044403400b6040039a005440c4107220b4500300421450001240e8a4505055600004004c0642558801c0300c5442451060107400c1c52000381082040107503070355582e402c080d002507212015401461500c42c00c02c520350b5aa0015295a00000612500c0804004010848000c11403141e40803841d14030303000c2da100c0b01a182d01134854502c40003001d42101c1240e006552114103010714500b08044030001ca0321010070307280c0403146544003200500d58141c01c0602c2038003510641c5442e5028446081c00306514800038860031003455000705c013068000d0801d040b072260700161701003151070b43d5039218005c90ba68044154151042e000c0c001508581600c0380b43c103d8031407103c403c0c07040d2914501030130701d40011030014200b05003184005400000b42041440140040c001c58203050107104981c20403020361f07041c1d103030300380c0c403940c89402e403603100751400701d00b060156030070a541304210a494282624148103000ba400709951810440d050307074a030400840d00649004810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 151476348 1250 151475098 151475101
    0x5070507050105180a0b130f03030c0e0a060504090c02070b0c07030c0603050906060108040f0b0108030301090c03061208090607080706061401020f070b1e0f04051c15020310080d020c09 81
    0x148440ba800313101c0b510310640c205040c40d0003c1489400d42e9500150b080600540e050b9417074440011103080c075001100041d4840007410140f0340c0c00a020f03d5500ca080b91840d0342c1501e05203019041c3d11030f03840350007942503c0340b1040000900a00010004100000015070340760642103880752280042d00088072100b085079000325000e442032103600e20410360400141020b44039400151130301038008204030740d4030078078170011400140d0600c3c65a0007440500004c6441303504040019090b5001002d141040501d44213007004020302350020b80300c41942000031180c3d12610f40c00411164480c0440203040d10720002203050400031240d21540803500030f025030010380000b42c0012a1202909503907420700351b01601091203851340c1c0000030400b2560f070901c100e072000c020424858503500a400502040480810100140c0c1461491120344000100c0705905d244020b80e507088400c100d07101c203030210707a0380400020012030340c40a2400c048e02c50302d02100c02c0d484120100a544002c4040b1040c0039000301030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 151477598 1250 151476348 151476361
    0x3160614011a030a111b100b030a0807060b03010b031506100e03030712020c040c0201140601080f0c03070504030b040f060b040c0c02040f02160b51030105070507050105 74
    0x6065075404610481c6480c515210a41100050304041070f018885d070000f040950b4030380d215605141c58089191000c1d00c1003500200e980d804403040c034100c140c043d400103610100000e24070400c5482590b880380300040c0b048005000b20380104107400d40709815100c1c0781c09041b4500035001c140f500c103941c11600102d110507482811100325650700d0440750580d00a2000c680020319512000b07910703880c0c500c102e41800d0313181400181550380391082c65000d48d566000e155694030041c10400d80c8070200b0b0800e001d5908007150b2031080e1440007080341150500210105061922840441d0002c40e00705824521a050904003181101e44c0b2203c1103480300d1400700c1c49502d9040c00d0045000340d00080d190403200703141c55020302011304000c1542d0003030580c1c01c01120050100c2003015030301d0280200f5400a0503d06107920300d00c90180242c0544074180c4001c00c00746030403142141400c0f4141c09102102d1028041d0407181003402d8440c4165600d5400d00d000c02c170540754800c001d46103090183c0020300c0142c03900c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 151478848 1250 151477598 151477619
    0x105072a12120c0c030305090d02060f040315090c120f06050a0b0916020d0e040e0a06090b0f011413091718010306050a0e04150218040e15180316061401 67
    0x80c2001070046500d804c0400100e801100034110085028029640240a55001a007071754881cac1c010080c0604085030500611a0002402e140545802070400102d4140d40f02d02c400c07010588150081c0c100810b00c0c000401a109401003017840d80071106100a0500d010f521000d8541407110501500e02c1740f00286444002e11030702001340301950003509120003c61070440d0841c1c10841d1740d0390880e40300c42e0200d002c008100f26030000315006a000003228003482c90030a0317040601800d1038007602d03c5200180000d05113482c401380941c4048a01b0349034800702c40d507420085c1000700c01c0501b180c102c0016000241c0321500090139030848403000344140c042071a006400301c424900456030016a04507040c4420503409410f141c129001e540007000d10fa0080c510311080e613012644043c02e030002c0104031070503404d140c000d220702040c50fa03000c3c040f45950803040300c140c7d0ba0300400c52807012410000700b0358001411b1040340d1000102c1040c80350b41c4102410850f014114005010391010125400000c500c1c080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 151480098 1250 151478848 151478867
    0x30601110d0f030b030c0d0602090a06050414040b0411030702061504090b0a0b030a0c080d08130302060a24061709030306010807110c130510090b0105072a1212 70
    0x65103402898002c4540124001d121800140e50184500316aa501700d0740e45000102d96140300f0140965180300300000d110706685145d02c101c05120083c0014094000900300f10300c0d0003102543d0004c0c11309200030000f805415010021100200b00100740034030f140c0e01140c090f1040004081c0c405411740c4e24002c0c0b104545044401405103813450001c2000a0500d030802d4940c044018100c0d0000450381c0c40307803c0303100c3c4554000511540070b079601501a1b034000d140319901c0b49092069450303224007524040c1d10340000800120794aa903030043c041050301342c0030701984807c1180ba2562001d545824016001e01c03d52482c0c0c060920300f1400094010000108981c418507069507482e085403603124064480301c024110b6140c0324003e1036842e140316294213800c07901020000c072001c10382d405c1104103d40c00b013041d40c10004c403290400c0a00510342c1d8001d4111156160b1240b0aa492030801c0c030703e00d6010401800403296919040b62001441401100d500323b03140e40604650b0541030b07003151080e9500c420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 151481348 1250 151480098 151480123
    0x1404080306120f0d0324231012090201090312020304080c040203250302070b0703020304120206010312051602040603030c02030d0f020703060504080909101401020303040804030803060d080a0503060111 88
    0x30103130712000d000e846504075185140000d0f21203180700c0842501e030718101e20300c0e4001100c0c9004409900321b0000c5c204c07a1041c07103040e0031b6928059800d8520002400388041c6a203034280140c80d007009004592107070440b0402160040528899282d103900002d4803a4414494080c15101c1d0346120125441c152089a026081425400d84c0c0154282680510a51030750380c040c2c01e01d5402e011803004500f0500031244212180e80d40140c2d00e2601b0f281203011115002d0544013190720040051000414014011a001103281001600c40c50741c1c0812440c19207a45400940050814a00000305900b00404031041c510031401c2d0341298100d410116503511020344282c0040e401841c003040800c0959001075009030251414614119060380416011502943e40018600140c90200144035800000707940a40d001d102541c41c608050302d81309158044c83c0805005c842000001c40d42c0c4d07a81d12510101c1c400d40c04140a40c0315844c521003d0700075041140c0c404c1c04140700c1c010b51405003402240c0c103050b000303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 151482598 1250 151481348 151481353
    0x30a110408070524161514010506090f04141506030c18010909090c05010207060201020426210705060a112d0c0106030c05010305070207060f02011404080306120f 71
    0x40c40c1000b0403010282c0c0c000c50420940f103a03048401507140702e6004103d034450081009801285c140b626134240b0704400401c40b410380c9481c00c0c60040700c900117000c030704417502120b2440e110181030000942a65918480b5070344103140903600b24803035a664001d03911461070450f0810b070108501013032114911040320000c620f01c0041054110301d60031401d80c5101e0400616091241d80e440310700c4501190400c3c2e4003a140001c3d10b1408001c95030f030400140f00500480c0c4000d605007032801c1f42c84030b0b110740184400c4c1c8611442900352010304004000195402c2482d01c0e0000b0b1751003010100f040142d0003160251841c0c01582c1c0060b114000701d000d8240303050741d10229203180182c40005c805040c03160a00303075400c580c2d07088440100c001d50b032405003207225078110002480614625000d1490455540281d05042c105010850150303008074146040743c2840c2860b41151703110300f034101d004001241030441c04803050b4044c0b00910100d10080c6100741c3c025030b41800c4081c00c5c2301e611583c40303154440700755056 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 151483848 1250 151482598 151482613
    0x4020c06070302070f060c050c0f010c090b07020301020c01020a0f03060803041206091401020a0f030b030d050720060a050d0f1a0409080415030507020d140706052a030a110408 77
    0x1d0744030307500500480f801180343e00c01c210442d564440c00d81da01e441403040040c2020600c0108280148648503640402c40020081464600b4001c0c1c1110080d00c0ba0941c662004106032041d52401c1d011191003840e064000c41d0350781c030030703010240034480001c0c840000285041d034086801540041124145c41034483c1c0d908580390590b03506006480f81c01403c5a00a440518002c1a0b800900113802031000f1030311000e1180540c401c0c0202100d0740800036034400d03070041c1c1c0c1c50310b003042c0c10200701c900c3d040c1c2105071042c4413034082c0704002100c0003844c003150300b0103000192162141e60160150500c8152260140000030060300c0d040c00740c5d07403e61000d40c40c01c19600f1060515103040d510003041c481c031800f07401d4245079480c3c01e001c48074403103035900c2400f1945840401940c20780c180a10152450385081c00034400c00104400d6000b8024010018200c07640d500205100407580340f51300344030100c10382c0d000008a078042d00c0004950000c0d0303544000b01c2e003000e5401d46003a442d081130700d080e20300500040a84 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 151485098 1250 151483848 151483861
    0x8070f090612020309010b0a0b0d0b030a0f120504080a0809091f05040b0a050405100e0c07050604020108040f081b0610141009050904060c0909020901021917070b1504020c06 76
    0x3584003505c100c1540d942c1d0b10601e01c00c2e0315418101801040750f10001e54480c0c1204815205940f0800e40c424842c0d002210014001040d25007120a4150010902503c5118425003070340c84d4030035a08200c405220311268181003140c128010050603070305031006085500c6002510352074009aa40030307805806100002c2c020390410744c1c400c00399040e000781900ac2c42542c0390003180440e001664451016000500107100c1441181801074200c40b207480305c030780f4142c100e44503551100c50140c0001d04220310000418240040340c0111081c0c160000c95550340d0b02c4412045a100c42501903813107041d802503d0008a144031403030801400c44500318241c0c0300e4072200b0810008101d180c62400c0c0c05204a1000226007074a41103007061107903109090002e0703c2802401d001c1c26007039450303004188440c0100800700d002c3c0d90100e91080a0208181d0f91001281d0601c9c01b0100b54002d100388000200010a01c0821700101d050300601609c88040030305140d4154109101c141d120f80000301442c2c1e071140700442c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 151486348 1250 151485098 151485101
    0x50703391a040323160905100b0403020114030a0609050a050411010905010e0405090708071d0606090a170a0b0a020a090b04032102070b070f0203010b01090302090610030905070608070f090612 84
    0x10700784000042c0e400c5405c008424110a00325900680d40030780d41d4404200340f880041115401400301c10300c0071402c1030326550000f095505e480d1651202c110000c804680318009a40105001d01910041400a032402d02811801040100c0d0151b9001284101403c0b06500400914003078a10694600391000104818071001d010050804203442c81880030001d2034100030700810014102214100088881c3c00c11200c881f900046c02030340c07145030300b000641107a41c1e40c5040001210144d4111400f090310740746003d41031154008018000780e131603004120800c00c00d03500602d810341c91904c601310100c7c4c0726584000f09000f01e0000405c80324405903500071884010340e0a03000e41c00a4412a00c0d0182ca400340c0c0c0065407c5070008941c0d85501290701c1003103140c00e01618449032400c6c070b40103d52030f140d500010200c00025215501a2008001c2030a9040c401d400c045a001c1d00882210102551072800900a5400325403501c001840039035015080b52013a5680d0084569075030300c840500344582c1c0c2c03110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 151487598 1250 151486348 151486403
    0x1a010e1203031506090307031a010b0a0206010302040b0303120703020c0d0c120c020a08030a020601030b15031e0c060708030702191109180f0c030601060507050703391a0403 76
    0x2e520044c1071003001e0701603a04109000c0a03610039400400031604120040744030304010b80105000c0b900c280414102a540003d0301411a50112808500d41d010b0f03001283c01c0d0f204108a0b960194805820804100d030075030010000c10120790103c80d00184030410444121075545d60003012552070749190890340e44590350059460707000400c2140043e40c1c0d00109840c42d07202d0849030015810a030b004005104c42080c0c0144d000f680f18032a500300340c03001d01c00a43c482d114000c400a40c20004250f0109464080100034030108000e07140c07079990042d83c2001e6a85410032110074005100d011100b40580c2c0c6588041c030001903008840c502d502645e24100480e0900c018101032004032204c080f008041005c00c0300202e025200000340200c005c1702c60030b0504041050300290f040c070004104c03003800950001800d1048941144055070032160010022a50080107841c648209003404c0c9001462104400b2400032149811040441441c11002890850240340b0010385540740690820110240301041c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 151488848 1250 151487598 151487641
    0x1180303080627190b0103060305030d0c02030d021b0f030a12090809091609080601061422080708070609050a050d02120d0e130e071502030705011a010e120303 70
    0x520051016441d1401c4110100c3e00c00d02c0c1c0705091001c1815120185c8144183e80c1801c4c682400f80070b04603103a55a0300d11540c84a2081035640d002e40d2919144240182c0307003031003c141c0c4150f5440c6401118010344d807202e0003503502c0c540968a00b10820940c000300301c40741c0d4405a1900d40d009660074402c04001c00c0d445c04183c030000c400b00f10a231240d0b038450341010310555500110b9001240c507190010301c0c000c02500f02c0041c9070300c841e005000c0c0c540c20143d0811f06c84420010303150741342c030000440d00c800c449548501c8c122003018074020a2000300401d0340000d444200d003c480300d0541c0d502007110802018403400790000a40d00e0107201d2403d01851064085d8000742c407140d014200000071320710340004154100d00143c000121b8412514106211080520701054240007000030072000b03d864403c0c501c2110380481408100d002d080b4000d006850301039800800810113039000b08450307031038642e007101028002481d503403840303902e4038000e91100d0600301c201004504640e5000c0e1500038481c101241f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 151490098 1250 151488848 151488889
    0xc03100c0f1b0c0303030212060a050114090a0b04030c0e07020106050a031205160b190504120305070207030b010f1a1204031805090108070501080906040b060105031e090c011803030806 81
    0xb03940807480f109102402507209650041c1e4a06609030390203001d00d40a800f861007019a440200000ea900030340100d020000719603001e6a45198500040e07006140da400458071100129001060244103440b100c1141c0004805076065130350309500702d0880740ba034041c1c294000324540c0288081000080c4006c3c03400f01c0d90a00518041003050003045000e10040100c440030848410003010032402c4400e4100f003603a80c00706020f1800c00e591602003882940014008041d82c410020707040f2442009003400440d000000c00126584801c000308088400340103861031144c180d40c0816401c140c00c800c40c2c1c0200c41c07102c60100c094850355400c64260450600610304c80a0705a004102c030b680c2c24180e540207081210003042a00e1a040000d09581c000810103102500070070104808200102c03200c60780068246042962981c4055021a10380f403030760202e500d55041c090400c0100301d0002640380f200c3c4001d80381c0c0d007000200c180c0d41805011241c0802000114118007107031040c1403c035000a04540403c6a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 151491348 1250 151490098 151490147
    0x5030406020c100b040c03020405130b030c180108010b180a0f0e070e040203010c080903040b0307030f0f0c090f0f0501030b06070501020f0d0f0c091401020f010e0c03100c0f 76
    0xb9841c43e0040d03241c4400c1c0c441da92504200d40c685082d1003484040c20700c2d0f007070030b5043c00d2401000032041030325003070003419140e1242c0c40a8404c2c1d40c24401f001c02c0d500000e0607136514031303000b00d100100f112007401030340004d42c03a00035401d01034a80070501d021502e4910320b007401180e0707031107c0742c9000d008000b0840d00c940e515802d2081094034203120b80d0002d0a40c0040c0c5801c1458540101800d42d00e104120800b800b408500340700e00c2030703008802c441c00c1d1140e2614050b41d070b4485e08021402440150852404103182c9a8403441e0380a050300300742c480d140569581e40c0c40035180c44442c0e1407a1140d2192480841e0f401d40d0070001ea5000360801c0c844140001d000500348503064070f8081c2643e20484c0ca0704c2c032115000401e911071003168403d200321018100c2d0208113440550b500030700340b05140e01038203c400c0318000403610168802c04c12482850145c1000f40003c0d003102c0c1031161303518603400e48284a070281d8440c42c1100c0310148504451840140d1711116810482503040d182100c44080a2068100040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 151492598 1250 151491348 151491367
    0x11030610050a0327050c04090206040e130c090c021c020c0418050a030203030601020f0d050313060b040905010c0e0108060d02010e0324011503050907050f0f03010e06060406050117070503040602 85
    0x3003075040001c44241d40d130866070410b842c3c151b040c00c0308440607600c502e107810b0f8480c0150b180c1000782d03001e88010130a00d5401c1e84885c1d002ca0704c04183e040c4020304600e8006400305420269400c00c13003d100050b001c980781407485000ea01c4008901c070b00c00c0b50051380400040101440c03c0c1c0c12255041c0d45020250640560a441305424001e00e00d10903000b50303100006100302541d04100585034000c101000c0d01e084425014010010720010300f030144090f813418090424000d0340c0c3d00404440c1030003001003022180c05d2030070a001e000e109443c100850100020441d0a5020b0a2894802c15006085150200d020390041d100384041c91040c64162040440600d90540315142c2d4500034502034503611040c1d80342a1058810a680d080345c802058289801c2c816417800010b8034800340d40086844504030b000700404103820f80c1e450a4815815828075041001c1d95001080050103408255418003505071100c006542c840c52000e800d401d000c4480000030b1a0740e1080c00655006485110003600d82080b41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 151493848 1250 151492598 151492631
    0x2010c110a080a0c080c10020607140910080f0717190212090a0b07032903011e060311030606060a11010b04060305060a0c1b020d0515010b040911030610050a03 70
    0x100c80459103404d85413410710828400b00054445500202e5649418801d1500e00039107520000d4490028420a002c442080262074030035141501c0000d44140301050158000410b140410385400b00911010404a40100c0c0700b04403141030344400000600860f02c031200f8608000035405103581e511982442030400358110550701d0340c040c8030404000c04144031343d401c000b03550040c050329210a144c5410141c03908071105006200350903265488000a2086910101f405014140c442c10080755074140d2039404d03040c59a200405880c02182c2003185001e90606050b070f5010301341c0e412940711000f48031900c140c42c4500300304c4160500c0f80001280d2416a80d0100d03040d2140c6030821a03581d00035208100180b40f161081c2282c252b9140b074031042c00508000c06001c01403140b1800782c0100907811001081c4a82009083c0741880e1341703003400d0300c1580d59a2007078400380c0060003021001c038140300c0c500e540c0c40c00b50019a8000d81c401000380008800d40c02d02500c80d940b020500006064842d1000108081b14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 151495098 1250 151493848 151493863
    0x110a0602030408041a0304110d0311010204260d02070b030c0903070e061309020a140105040803040b09030709090503090603180d020309012d05030c12100303081302010c110a08 77
    0x1c004141d100ea0500d40350620004201c41a0301c5c0b8504184204001301e072031288500c2d12260251002d58032001c2c1030034119901c1007203400074916980005400511480c091003100045000e030305046105d1040080c18544507107c07198002e0050380320400502c0209020340065400010700b01d6024580390071000400d040005590000c00e044218030100310305800d02018402c2c1600c1c000804000b408110f0b400165043c00500601d03503d451315600f4441d00340d00a000321000703403404d4400c90303440d241c1c0d030780924016511040304a4020701403003000040342104e40c0035a80402d07a01c100070318180034105003404000c1e08010001b40c0c3c1c4600d080c0800d4107011090000e04501d07455031b4061980c9031144d400241c107510050001e902244c03802080300c1511080e80058510034107031860410fa9070f84590412001d1401074480228546c4c5421081c40541c90300e8081d00801c591107526400320a1780c80c1d000481e1007900a00f800b0b40851604005900025688044602e04d1000142003602c40e90b107a8800c1d5140029 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 151496348 1250 151495098 151495103
    0x803090319080709060e093c060109080609061f1d0105011d01090b03040303060e070504031a0609061002030d06090614030601120f0501060518041403040f0303110a06020304 76
    0x12030340b050041642d88810300001401450800b1012202003001241d02035000820b100c000b8585c58641c1c5d5100342000000240d40802070001e01000010b0042420f1110020317a50306011540f20a40000e0800c00404c07010711804c5a08080c10490b61040d4111040050f1460036220000e032120002c26103541343c40620303903e050168040c40300d640c180710000d80005a134001b041c0c040d8038061405603550380c0c0300759400165809501b00540b80e448600e0103801a1805810884c000c50303d0b0000c011401da8440007402c210b038010455001c40c86c15201311942689000c2d5802e54005400e1800100306081101640000c000c1c070380704407032404032545948022a22150420f4105c50b88a203020045c2c1c43c5481e0340042c8000c8210040d0445d945441d0100032100720151004002d40c0992440c0e9007442829800a8020000682000800449500302505054085134200c5140300c0899105800a00c00010788041d07420340c4102000c0142140c8060f20b003903001c00703080d81d6a80b0501c01d41d0400618640040c40c0141e2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 151497598 1250 151496348 151496357
    0x1e190302100e010b06042112050703030c0801030b04021018060e01110c030307020d08090a06210e070b22060203070209070c0305040b09040f15050f09060604030803090319 75
    0x502141c041c02640ca0116203016103a05141c10403900ea03503081c044404850344502c245003900d001c840a840004100800642183d44196043c5900d9421800034034442d84659010031170300c0e1038041c060360a00403e0201074140302602c800600181041e06005c400c1a4050800c20100c6c04554286100c4140a800902c0010001c4117030b80d18558000c0310001c83c421414015022043e0180f0220395a070203400400b9200d81d500784000001e200c415000c0b5125890080c2441454076202c80e0080c010901c10030725281030030380c1d2402a04140c0c840d8465080140c8104000c2c0c03442d140313071078007807038031074012452200f907501614001031058400886440005e2000e60099a1100700600420041240080841d03041c00711083c0c2210000364080d0031101030f10217540d40a41c0b00d82c054004500101036418400c2076103841c011030991004078102c990011500121000309010b850901484403064068800c03d8100e070003800107000041840d005140d12a030000116401c01d5a01125281800000e154820105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 151498848 1250 151497598 151497613
    0xe0402010e12012901030908090f0109090f05180a0b041202151005030d0f1e0504080d03090c060c15051b030a02040f0603110a0c060f090501020d0e0d021e190302 71
    0x10004120000740c584e60034201042900c000e43c41d50250380c401c50a40511510010004014584c01010040080c0807840010801d01c00c1e465401c800425007a034460746032906000f03146482800010f1400c200b1039121402c01d0386504c541d03039220000c000001660042d0300400c0341c42110500c0e001251403151100f0706040c020341d840e100602d800d01100104003020021400603100105401810503008514002d403012107080b07050b0800c0f100c1c1d0180c0e4114135494082c5240c078135200e0780d02d500301344481409041c01803e461786d1000c050307400d0044038074010b04942082d180743c0700e1001203078030045d8883d41130a00c0c09540b5010250607401903008032240b0140c03d90100d02804020440910300003c0d01280c1010030080864040c408020b0013004180820460319440042c20042c0a40085460405041d8107210214181c44e056001c2d401007c80c00c4100380c60065070181c07403040090f40b5404074030a80c003d400c4072402c2e83e8016038640c43c04030240001e0310407154400440c081032520014058003a50150186 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 151500098 1250 151498848 151498901
    0x11070803010515130e1003080a020607180501020d081e04030f030e06010e0f1009020c0708100203010e0105090a0e0303100e072c030a050f06040c0f0e0402010e1201 72
    0xb0007456003001c081c0d00400d03c40c9450131030320b1030441c40130b440c1c1c80d540b035006554444c6035214540885400050201001040000c649030b0002400350040d4413903211140e0040e030b103458020100b0f11511a403401a8090010084140d0107190200d80050369126990030a009512500503c242c040d6002c40015101d42880005190b040c42217551009114000d40b200d945040b00300040c1d848090308521303845070910089000f0803043c0c1000401060344210940d02c5640407800d90761640a40e1107410742602030b4801c540c05441c014800c03039059a441c1e107a1550f09900780002d000b50100024aa0f14120740e81e005803040d0030f40e00b00040d5200381618101079139000c0c201142216210005804401400780c03950216019007200f03004800c02c41c800310003080040306002c4c0002d140c4089040003400714016200219621a0701245640c841c3d401105c01c40c00b2160360314100b4179120801d120380040c560340705011400540c45000b0700380349180b0003454603559201d88142b240c00c40780224008c2c00700d0301060522012 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 151501348 1250 151500098 151500109
    0x9090702070f0b040807050603180d050a091a0a050c0a060915060501020f0c090907050a1d09030307021b0f0618090601020a0203030403060509070803071a1008030a030c03110708030105 81
    0x5810300100d0f46091515040440741c0e192090301501d0302c02d090100c00500300c3c48282c0328030b80001d10210221454480900340c0075109a204d0030541001a26440c0086044a9504e003420002981c00300440e00d0403504213021a5240c0140401400031f00400b5401000301d10107004541c0d10500420090021881110340316003150250350000b4195086996181c540000209094103185420f40d204e03802e9540d4101c0c0c090a00e0300580007070741d0020600307002065200c0e07000035001d021b80d07a074883d000407034880700360295403030200726002d4005038000f480c051002c003140e03411600c044030054036440b40103424400051861300070100c02c0c19003000107802070805180c0741d0911500580c1c2800900070070b61154001c01e4491003507000c007501c2c00c1c0e20f0b000880c2c40441d0401100f4010306e1001c2c00da03615030b0f100c1e10342140000d07030601140310130800c0a0b000c1210111002510b50441d100c00000f1403400ca10003e007900540131039601030051560310444001c0180a40b001441c2d0207101c0c5085d1aa02d60400d8108074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 151502598 1250 151501348 151501379
    0x1b0d0b190609050906040219090e0a0605010609080d03091a0a0903020c0a0b04140d06020307020d080c030c07060b040902060c010b01120203040c18111602010f0206151002030909070207 81
    0x5880ca040c42c1c113100c4201c402060036600b25805a4687c078448500600d258000c44140d4405000f4a180607030488200001161450b000c900c150030921090b40e0b03814003100c00c0c400303501910b9030340c0c3c01c1080d0f00b034200b900030390216401511a070708200241c52240071038241120100c400d03822030350b10b91103054105075040c084503401400c2244d04040c0c290500081030b0441c025402148090f042e00000780104e0340d118a1502421035200700c06650301e1501540094480510071444404601ea84010580501d211405d032440f46442d1031010703040183e251901d50103000707525040364206039240408805a107410006224243c0c0c000300102c0d0502d5000001400b49000303080b00148d140c418000d00001036a504464000c035141825100c1425079038038a4000240314103d00300300c00305000034a84803034031841405130051324001d80740c031307551920740070710980e1500d40859002c50000f4928100000c1464108540140c1001344c0c1304481c204410720004c101d0012080d0f50000241e0310043c000c102d00851300c610103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 151503848 1250 151502598 151502609
    0x3090501110705150f150619170c0702030c09060103090c030308090f0c030a080a120218010906051201030b15030111040f1203090b0f0c06070f120903021b0d0b1906 72
    0x104c0e140d24002c80303030f08180351001e42103403220549008008140d9980505890b58007a0a0000126243c40040060950340d6420703c10300c82000d59a001440a02d12101594291500900035004410402c0d0401a00b09030040c000360605035101c080c4004144005208009180310b0f450f000600d041414040e850401ea90311609072035403001280851507200440d501e4503460340054a5904c0d0301c4c16040c180c1d66681c22400e28000a072020030114941c140342c40300c1c24000320083c2c852002c0503844280489e020301c5407580c210240b64001c00104001200d5900080d8000c0104800010751003445000a00f5030305486091800d0f01300100e03082c00085104269100103000e48000b49080c011030340ea02400903021407060039203015000c550700d08045401c1c1c00711004204820b09680e82403030b01800141000c1d41c00b151210000d42241110004d00c0750500c1400031203174041c1c0080080401041c2d19503003081d01e036501284c0014421030104000f0b40c0e1403608900070440d0340c0c1419100c43c04611203500b202d00b02d5101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 151505098 1250 151503848 151503883
    0x30513050c0409170f07020108010506160f05240a060e040c0b0f0417060703152303100606080f07050403030f08130c08031803030f1903090501110705 66
    0x20400015000038540000403419a80843c1c0c1041605206202e80306039080804036040c0083d880c40ba6400000051440c54400d032940426a43c0b0b4401380b242034025001c444034050700b0440b01d10701007058600445103c9104508881041c80324489032218428100803101c114490607050106120b0300d80241070150800c16400086464a9119040d0344440c91040e250400000100383e15110000021240070340452500d5416502900c00030320f80c0c030740d412030305180000c1ca8502d10741c0300343c05080f010301c2c01c60340e501441c0d10450241580c41e0758a240e5a05085615125043d800780c0445401e0080301c0081201e40c031440d80d58039040c04440765040b0300805000401500f0441800000d03040041c68003184041e191652440c3e5038051801340300c810680b0050301c520095400002c5041c8000000c00c0e4542c0c407005450441000041816039074054815284a0080180001d00c03110943c0407040c0020001440c0c0412110601d480380c900f110600302088965a02c00582941848810448101d00e01060400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 151506348 1250 151505098 151505131
    0x3200a080c030c0d030201230403030c080114010531080f01090f1e02030f010204060306090207020616020d08030106030c140306030d050a21050402040c050304170d0608010507030c0305 81
    0xc1d0701c0f40c42e81e29206100d00c20519511091510035480003500d1015440c200701d140c4c911070141c0503401c6003107804400203420001d5500d1018401c8c80c00764122540c0009a03c031402900006460503040b04801c00e0f00c1d046c1107100c6031000e490b014840070090b0120706043c10040e090070025420010402184043da0303040007441070020f581e0a0f01c1c04800c540015003080c1c50030784082a403404440c0303150302030345c90310401d00c160342d1011066004004803291900c4c20009680d4900a00090b401455006940010180829008001410003901c0264070050000041003501c0d46c0d510740d035030030030703000000000e6649040740d801c2da40007030741d410a000a111181d410740c41c00c1b0000a80d120028030064040260100303080d58018003524603000e40002c60310102d800800c184502c8001843c1c2203c080e4130640c2081404840c4600801c22640201e41004041d0350514442c1c440d00315581c0230914064490b0b507203c030001203425013840f4050259101e50307004221104001e2006007911005400141c40a20900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 151507598 1250 151506348 151506373
    0x241b031b0e06030c041701050f011205120c030705070303030911010809100c05091e090a02040305030427020d1a09060d17040302090c0a0207080303060105041e03200a08 74
    0x20380a1503025080b11150364995441050220078000c80e405000c80645400003810041019080580701c3d1580820a9100342c4c0c1e5040d0003d030f1115071380c001030055000300820703241c0010050b0052000752202c004403480d1a109540d4107181000650064001030781c0c42c141d800410000450800c040002403030042054249003d603c0d840e040000c1400300e000e035039510f085058502413400d0300c000c1d001c000d0103c219a1052b03081c01c02c090900c0340259200380c4280740059012121403007910141d0b82c00400850a00b410311000d1b10001e00c45410859048203c008448450283c0d80001e184110502c580410443c0341040408812190980c220b0312500d083c10400009449084424800c10f400c42042035458111a030104050302c1590406034000c2d0000d001c010500003400c0051860203041d600b15105180e40e40411a200d000c140d078104d0008400304001c200d00c9002d035403000e881400240c003040d8147e659a03a007440c4401c0b0039040d075580c0c900c030031560000b501d8081c05079401400707480090b00c1200c03d40e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 151508848 1250 151507598 151507607
    0x190516050901050705100609090b010e0705040312120507031b0207060e100e04020d050108121312080c150105010e04060812250303050a0c0f0c241b031b 67
    0x20324126042000c0460751303205120080002d10107009a00074200541c0783c80312811805094001c1c0240c2c0c6e80b0180b0800010340c002c640c0c400512070f1030250b50f01030a0a04582d142210006040a042d04110800ca00308400c9901403103068040c2000e0b031800550f20325214035181c5000c80442120f029500101c02c100126508000d241d100a03004071200c261800519109071495069000f030700c3d400c03c0c030206110725103a520394000e0f030580b01d6090403101c00c036075082244900c52007981c0500e00c110591502c2080310041c0d07151a00c001c244154800d0341003448413940d59141840d0300d407032440829903c100411255800409003042810162020701c9002d09020b20b0940c1d4003070746210211045000141188034002c0e810680e0312010b1031041485c182c1d0440d0a000b03000e000d094a05103d920320f001ca40868180c0903450114404445849540c0b20400548512050b1072044004281c0300e03040301101881780340e0314800c4a000c5003020112648409058000804990842d50b15910340c410a50b00414602c0c1c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 151510098 1250 151508848 151508857
    0x1050304170a05040807080f120403081614240108030a0203030114010e10050a080a02070213050403020f1203040b010608060a090e010207080301090f0e071a071a19051605 75
    0x1000c0c40c041d075800340b160048500d840703180c1c0500194001c80304041031659011482c1d480702440c143c119080c035070000118291620552000411035102003041b0420160072031301d01ca9150f0b001d140400e030144500d42c50f05003026034400e03c2d81d0558044c521a010081600e055290140c8a10ba00540c00e003c0010800b942d82e200c1801a51040100046031902a82c0311340302510a0b40c10242142003c14042c45024003a41c02c0300710711402250102000079003880725407083e80c1d1900d40040c074169810510001c000000d01001e001507003107000b403440c0300700407080070004400709168890360180e51749030900741142003c1042e048641044884000e00c038103079403a0b48454041c0c0d08151400907010003420f42c100e00a12880710010016030020000003481800c0e64050b00903041100c00030b024510904140d00e4855041d401100126524603101c08040914030016207541445034840408804041010034508101241c4a206a0308810700c500074520040c0a141d400402c4110781550900200c0c3d00640580034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 151511348 1250 151510098 151510133
    0x702161710110c1507020a03180b0a1e0201090b0106030b011103031608060a05031f060f0608010914060105030a020d060306060803190305060619030f0f0b121b090402060705012901050304 82
    0x45509e28500419001980800200500c020042d613800c807941010b0569598503010b46c0b486031140e40c00c26266401802083c1d40c0f50b52044061701c2580c24620b05400501c02e04400c00c0c100036503c503001c4040b0b80100000c60041c059000130030a0610b2b81100101800002000940142d0111000304116180015090030f507060300f40314004e04812082d0414010081903203e501042a01c100002e0900e13002503006049e501600810300c680d8203401d58080c40d20388241c3d03205e030014800304000784200c90070354080cbc500742c11b4292001c02d40e01d680c1e44a05013a503a45400c044880d800c0000c0c805a1200069074803100c46440342000c0c091454920001012802801e0700d9554007004a8019002c0511aa000880d80c0ca10008104020800704180000400402c1e02d124011202c0041228900d600044c10303142d5801d02e86c08a03a0301c42013030b9051041a180140003260400c03403d0260000040c0280140b07a51001000c2100e403014518440c546100403000740070714180201042804042003424150f02074800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 151512598 1250 151511348 151511357
    0xd030e280b130b0f06010807021f15090906020a23040b070c0503010905071e120204020901210203041106030408070201030504020a08070f08060702161710110c1507020a03 75
    0x10b4800c5041032000340b07901001000030032824200300120a0440310980204005c0c1c2e5030800399511414182e945107020446016902020090050f07118959000f514101d003500740000180c030fa542030108141c803d08a4200c5400343c020440c4109568451240e080c00080541444c0c079142034141c01e035516110f14000c1042402c8002000014401124202002410007400800032a480d030300b4081d448070700c10700551810140d031400044022000a20580a83c3c14114140b02c000d951a403c010003540050703c031506100b417110301d0002140020002501c01c0c2c54980001d03a0f01e00d0185860b4003500c100c0011944604014014440071520480988170032035420309000443d6162800012011442548624003a200e000c4001c81e80003c003025000031243c014007200c00549821809907107840c45041d8500100d07062000c20460540e22032240d900c111680e50540d5031002c04904003005580840ca03440c0b10034500080d2a814410003040324503000c00403407101203264140000004e40361a540f18024007040f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 151513848 1250 151512598 151512601
    0x118060506040908040312030c0509210a1a150607110108091e0c240a05070804050405010b120a060612150506030406090c080304030503070b07050c0d030e280b 70
    0x180c48540c0411400e84d080b0446a881d540d40b0714044050068509035400000c1c10708980e01020303405401640e49500005240441c164201c94030422031000560401c0c1d002d00c074807480e401c042000082c101281110328802d0071014074094469503241086501d074103000791030420204000c10001034100341806001d1800080c561900d42401d80340080c1420322248004842d04070141d50360001072000040c6c0002c1d6200560310b02d85220b0b90406100308801e0400d02001046183c20003803003200103202c5288106010750400d0784610100b0207e8a090b002804804000503419521980e809071041d42300c004880309000e403c3c00c02e5001801001581c0f01880900c1c0c540b46500701c510301c0310004501820f0301a203484d07100e1500c0e0030004041c1602140a40d07005240390000f0505e08404000c0b07506680e003000003185045410380e16010001c100030000b00400901f071000880002080c498102071000f107940104607555505002810010a040d0444491000c45456440d80e41540442a0184d401064101c400d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 151515098 1250 151513848 151513861
    0x21c140706091a0d0c031a06090607060207020310050c120a0b01020a020609040212040f0210090b072006030a0e010b04230406060e0c0c06010e0408090d02030c0d0503090f010201180605 81
    0x600452011104c0e45091540620001c1d9150380220071090b07250b01303c83c40b95200241030110314416070800b503401c8001000700e440030400513001804d22920140858a1000b001c44460080f2041601c1a23100124005441011003288a1120f500800703114405c000000c2c1480010b0759849280d04005d0141c40c3c04140c440640c0d4503a03054800d1100e24440407000e9160614001a22030b030903200407803040112070340841e00188941c0b18001610405034419182001030303115610b42e100e424107040488580308881070322646a602c090b50048452603001705071045411411401e482c84070600c02c0c0140d00d02000400786402003034100c08011032a04a80b40151034904107480038200903040740143c03802540500c03415641e0200140341c0d00d040d0f0000e6580c0e82c1d0300c516000720014416600034192420602c411001c41c90002c0c2030f280071034402002c5a1240410701c02040e201920410300380c650f0b07000864208001d003048000c81c10745076000d1001700206402d6a2503c00d24205402020344596a0703030707000485 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 151516348 1250 151515098 151515149
    0x91509070b0d20040f0605030603011112060102010f0c090306150801051e0114010c02060307120e030d0b061e1605120405030c09160e0607021c14070609 67
    0x600010314445035100300c2911034401400e011100c03610300d02500e122402c45040c071407003030702c0039030303030b0034403144070011b140140071100d5400191155034907541c1c41704030502030705041c4000c0c00d0034542480d1200980c50240d002900316000b0704210b000340e90900900c40110b56120340440190b81c0d000c03100082a03000d610014141000301c2c2c000070305543c61300c010301c5088240c072210300034079081d00c105117213103a038894540603008032a030a01d150100380101c40020040c946440034543c0003a1a1420f0791f500301e0640f4254066038078016944001707400000e00e000a0843c10b0203903140d0304505803089840e000c5221600c58031404c08005001100d500401d00c5c0101122904c00e200440303810070210783c604100420408001c0e0700a2003007521070b12640d0a210b50b241000c0d42102d01c28a0f151004400d410441017050b14044d80981c1c640350300c003c003003010700c0c01a900c00344031a4489c04840202c3c02c011341c05140062003c00c4c401c13400078069001a070100201c6501258103c20f45c0c15050650b0345145840440e603a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 151517598 1250 151516348 151516363
    0x109050d0f02120c1003140c0a03090b0403050c0106050103020711061b06070504060813150f020708070b010f170a1101050c010e010e0c0d0f120c0f050604050105070503091509 77
    0x203601c821861254071000d07100041c4a075068131304031040c2d00c10000c6400c1c02d07400c071103401b1440f80150049000107025000c003140a84032040c0c2e5403c02040148072a030b140040c0300c200b16400c502140c1d001c07400381001c2600f4031813100500740a080442c941107042d16018880c3c52926540d07480395200145403103d400c020009080504500c1049a0450400400c0681603411038010000001d50200010b40c0c403902141803a1810340c1c104005210001014030640d008d0042461300205040c2c007005080300164810000780101c5004445141955041c07454400c120302c0300c0e501c1275145034544140c100c00010b01103105098151321540407800c0264103001a101406080300000240d480c0501c1c99600300c406420081041c9441c2c01641c550000301c200708011403001d1140070f00b65904090203440018002e030440b0f031140c0018249040340040396500d17000320580c041401c8611350800030900040200900a6640000075400c1140c00c502e0004c0d0b04580c0c5a040c0885407070510f88980200f0041941130041e00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 151518848 1250 151517598 151517603
    0x30c021902210313030f1a2203110712051011030109020d0b060c030903010b01022109130617100b06030c030a1d01090b06180105010c050304050a090b120109020109050d0f 75
    0x13143d2071580c07400e100c808140d07002004d0f41e6a078404084034203108010f80b10184034102c1c240a0111801c101000d2020307101640c03008800b80304000f003c8140401d070400030440100034031400030b14810760500c0c100e81408840840c0c1620315060040c06005817003140c064034113440c24801c0050712804060420302c040c000d001d4200ea04280009080d10078008080000c0804000a03002401a481e0680049a480400031000003104107011030843c11081204002c02145000510b14075801d03071000c180030200c401a41c019060340742c55280c1d40d103200d0004c1c05505011441880108032803092400032882d04c0c0700042c50181c40d40000030019040300500da00c0542d400c8090b41502143c40c141e03410490081014080603079540744810006511440d112440c80800c07412020552026481c1c030380159142841c480b4200c501c0e00061001240c0b0781c41d07034100c54004080d140000706800600505111004034152001c0d402039060002c1c10700943d0700908460308039a8140e80c10b075085034403400c1c101071407045045d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 151520098 1250 151518848 151518877
    0x70513140f04020f0102071503090218070306080706050406020706350109061a1204051f0b01080112020f01080601030b04060b070201020d0f0c0b0601050c0607030c0219022103 77
    0xa0160701d2180e1403032070748100c0c42038a01a1101d40b070b01c40103a03903680007441051526200d0010784440c15201c0e070401070190744084c0046101e10139030001109991021039030840040d43e03600e82000340302820084103004005e1030402510b091300740003000f502c6440358040c810500070f4040300e0350009800000c0c00b200c82954020520000408240310700c8540100380320340044641000000300b00d0907c1c0c482000706481c0342030803036850140502828044c404005000b5600d9010380360780300b40b1900300c800c00b8481a034903903100099840b85000000d0b040c980117810581454840c25101c2005899105410820101c2401c1c43d214075954240100c01900d000004150824104a00000c400d031041000c0d01c2da00b4402d80076140c2c0c8020700f0208540f80384d0040f00c0300002818040e80800419280009140c0000d8107161552030300500caa45203141500648090001940d100050280c50398180000e8136405909070001002c00140d40003e2401622901c4080100304d0107000100348440030400c884846400c60303007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 151521348 1250 151520098 151520101
    0xb0403020409032c09010803160f03020c0306130c060903030203070b0c09040e010e010b04090b01060c050c0405010305150a0606020d0806040e1606030e0105010317090102010f05011514090307051314 87
    0xa407424a1098444ea050060141000100c1c01c1000401503070300b00c2185000009010520761615030b0403142e604815401d6014520b0102495142488450301c00c41c074002e00041a061a8078001c0c0801c10306900020400400305801d0001030f501000304c542540d02305883e2104c54545e11a036441d14031501c80c00683c85450700406d00c60099047d0002c10098042c0d2000308007486070760042c007068030003400d80108414940380052044c40c3c06908004442303401001200c144405040204003220020703042600c440d4003010348401c2c145490f2101035400303071500c032050000500e0301c03401a50f52103a1603000b1052083c04800651151135981c05005440880011100140723032340451403c50700310b6800303400000b9040c18011599284140107180c102d07680300145940078501401d006801d908040f0005045540301c198103c1200e5050240328080c0c85424158400d0000c1c64101508034141c2141103001000c092103142025900807841604407034041c0e030000f050180403e00e040042480e42c2c4941c0072001c8050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 151522598 1250 151521348 151521407
    0x103200d03030903200f0f0102040506040302010f050708040308091311160219030b1605070803060607080d060602030a021608070b0c120a0513090b030601031401090b090a0209010e010b040302040903 87
    0x340c86d900c0c40d280d030019918201188444513090388031318000c540d0404400c2004100551145d64820b09040892810604104007641c5821242e8800d0b40117075154400400d20000b5446e0043c54206a0304200c94104080748442074000b003280502c20104070b5000700c0a26503815920341d01444130034103c0d503a006075240380e264513140e05401010340b10200d102d80c00c5024882800c1c014030840c0c50840d0000c010509680d9100104841944850800c5641c58000c1c4003080400156008a4002d0700c42d90700596104c0342181d40c001d20b0141624848801e400c203080d0f00300010b1a001c02c0241c281c859450700c03145e03070f24801040300b4684110489008120070300020201142c60b03000018003050f80c40106082105580c481641c000c2d900d68483c41581600034000420006004114658035402e8603800800c1d01c3c83c01d40c4650103d032400310784903456504a044190214a004038585000d80340322402c03400340d0b5060a060b000d0318021404000d000720703600c1c0107003030034140200d1000c0728400344100f40303a10510300728 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 151523848 1250 151522598 151522603
    0x3010509060a0b010908070e0703060306021204030807030b06032a0414091e07080405010608150f0f0910050402030709050115140a271d0103200d0303090320 69
    0x12a0344030561440c0600c0c040403588a100d00c1c1003101d01b480002d00c6040c1c20044407a001071030141c11a01807542e50071001000807918006801e40306100c5086801a280030700f0040c040d0b01c802001101094070f068041440c5549440c1502d81120504202c001d403c401c59500c040440c000c48074480b503800010030000b8611038042040c80128000b6108413209450380d101c0a4007011040c07100328034010721200082d4401d0300c80c106440d031050080c0004160300b41e44103241030a154040f92079440c4003e025003009605001500041d4010f850356400403410715000b20311a4607444107140b00399490703448202040640d981005010b02034008000d04100950f500c01000004020014481e03001c07500b07041100d0b40c2520745009640b502061600c0d28100b0280004914074a040f100c18091410100d01c400401c4c3c1682e104100700c3c610491111540640d4110304000440c160780c8034643d8007500d002c090590310798484e624483e2000b41d1504010489041d103180540b8440d21402d0a0b425421600f50b803901a403000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 151525098 1250 151523848 151523851
    0x60303042d09180201030b0a090f020409051003050606060304170f0306090a050702070b1e0315010216060f050c030c1c030b091303050f040b1305010306290d0603020301050906 77
    0x41c101c01154503568071016815903900380c80511007090b401410380c000d94020b411849203414000c1c00b1804c840d8070781c1c1c162003c5404c1c404144800a43c0801c0034880c01815102d0395802c680c094400c2800189103954243e524070b00149068047e0f400400410100f1502e010354206e942c14030446261105100411400c7c1c6070002c0381c0d450300c604603401c04230b80050502d105441c0a01e205030b000d0311440342000090600c550104118803034a0403804019404e01c03600c90701450040c2607003080c0032120350050780020314000100e08a80c41d0300503100001c203e89a0041600291a074040c104141c03a4031409520314154000e04a12140a0042c1408005200c0040614611080003620100f01049a84003449403200007107540b00200c0c160400d410020a000b140603081c580380c0b002c81649082d4030703040e51148a8225181d80f40c160700040c80140207a68150140380058800c400402e408420500c1c820f90391440a00b00c0098074036800140c2d0444050142c00650156030050003e215604050682c55501c000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 151526348 1250 151525098 151525169
    0x30f0409020c0f01060e0a05011e051005070f0b070207150801090f06090c09030b01090204060507020603061c03020a0204050a0203092e1503020907020f0303041b031401020a0809011107080306030304 87
    0x238000002c9103074280003804000c80300140d607002044504100a001d00a03034045828424803000340401c100040010109280045c8288820840c034103010303c0c080d01e0f060203500060018101860f0980c2aa03500c201c103c0e044800e00880450900201a5128018a0303240c00c0000864201041600d40641117901c035403c6034807400300000c10360390f90389080c0203d00490156400080040003914050b207000d101440d00709000a01c8120194419148140c2080980307170104d0168025112170030a502c0d03d13200b4140d01a40c1d020065165180c1b124840c1d40341c4004d01c9028400c0010546a070160f27000c4000310300840702d52075004111980b5100451001da01d0140b004a2045814400203550544003240c03484241c0103800003103003103484696034240c44030084c21000e01140c0490100002044141030016200c2e01007400060f580c107440c10340105000c00007840800540e05010000d10656030b00001c64840d580c0043c03060b501c80d215140041d04520456021124a140411148000310f8088084444001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 151527598 1250 151526348 151526351
    0x30c0a0323090c09180a02040f060f0806090c0a060c02190801150302031006050612041403041508180706050c1f06050306131a0a021c020405040e030f0409020c0f01060e0a 75
    0x6480d1042d14085ca403042002d000c0d15040441540e0040c00c01c1e8214140340c03950404040b9005440c0c14440760010125070044065611103824000d03a91414840d071000f03400c065480d000c92605050000d055151401c000900440034031656a9111460494500281290400911130760035410894402c40c0800e020992180c02290f00c0514803017001c0c41030794200e601c044e14142c2040c04a080d00e40c0c00c0b00740244182ca03100003105905501c600f0074001070003c0c01807246100240001400d00505103030005000d1800c0f82080c0300b80c005110b0300050700d8001c541161600c2d176a182d9007040c5680c00d010241501c00004c00050b0920303460301c400d81e080f001c1542e005800b26807141c1d032032131500c0d103400d40390030b40c05025100b00c07510f500c2c0d5242c1d80d25000384e031010b01d008000d45031402d214614035411203101c42d1a00650b5003c2030912103440c0c10f001d031007603101d2004c00543c101121100803501c544070318800c00002c00d60025103103040310414018100340704d8580c0300801850381d86214003480d40a08540c10400103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 151528848 1250 151527598 151527601
    0x2402030d0501030606060f020622030c0803010308070c14180a0609060f06080f010605042303190b010803040602120d0b090408070507170c040f1d030c06010b030c0a0323090c09 77
    0x303520009c0c0c100c1c42500c01f0b828603540400d0480d811000a26204400d030300b00151500410049080c503401140210710641d000303a42d80460b4181070030703a0b05a81e08214006004444281840e81d500c4010944241e40d42c0d03060300c40e40c1c036806500c03000ae0403241d011240d146d040c1003002504a40d41d01604017200d406496200290761101c903c031554140c02d00412010640c03c0c00103012010180c0700c05800e20b0395959010881c0420724000038580844028000c2d440c042d91a8490100a84840d40a00400c0301c070000318100703070034000042c1d110425481c1320315a0840105000c06415110f0304141903108000c1d0050489042a00304801e003540800401e40300c3d403144500002c0d07405a1720f0544151000c5d00800351481800c0c1c0c00411000d061611207030002c1545078038242c0e111104540074a04504520401540d0307400c0540c0955040650583c007094034281d041c000c01240e01400c6080325014002440d0014a050104045034100c14503403200c540318800007010003043c6c1000061001280d007080b10214190b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 151530098 1250 151528848 151528877
    0x50c12190305060d0803060402040b031311090118021c091203050108061003030c060f0e100f14060909071d0708130c061409060c160f2402030d050103060606 69
    0x1511401c1d202d03d500310400c01c42c024003090742c1c000556005080208054501941c55007a02e000340c0083e01c2900001c8581101c3e1810449190030502018030f040e91030450662500f0414000c0b1701401e50a00c0f69a80c00256480e13402c0000552102d8020480300200071048180c01c1c170900014486c4042170202c2e107080008600e1000000e60580701e0b40e005243c020b013180c2182d900315400c0840c684100c83c1181c03039002c00302c4000c505001d040c150141d841c0042034a20480f01c01c4506403400142c00b03103002854035038500c04c070141c07407141c80fa0300100030744250758030b516240d00c228602031050380402111300351044180101c8071807403002030042d41079030395078000e540368000c41c0024416a68802000340c450010704121182c0036210544011000079482410027401c1400301d8800d40c4007103861010307a080000300607c0d01c1c0448107090085c080180e00003844c0c0c2d09010381c1d18401c640100114a4020510f003040f044c0038401c00c202c0d05003d28a540501903541e5a1402801a01950003904003184110302c64404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 151531348 1250 151530098 151530101
    0xd1803050a0303020c0115030803061302030108030409021308010216060b0301020a08161103030c040603142802090d0c03140d02101112090d090501031407030b01050c121903 76
    0x1900e800030003508030315546030380640082d4080012502c05548819001004441706244e040042d1f0107014015500c1ca002420445101005005104042e20600040c010400c0010a44e811340704c944500503503c1e0001d10003c40780d0a0305500c85601c941c000070b04400c0e080075680b1001c81c80c40c40740205004808900d02094244c0c02010142070020b2000000159541070030a1207644040b03d038102101c02e520300f010402d0543e0310858a14050180004007006140e80c14401c2c80401c5a400c25a00d686081a20b40c1310b00342910006086414900040c0440d01c2d00819412114264030041402e01c2195152801655850440c0f00c1a122120740080d2008504408600f1810105d2140e016181052560343c020008003912007042c040c00c035041c0500130105c0140191240100c001034004e045c0e014401d60028900c2541d508036034101814090380011341006c10383c03d181c000b503440c00c0200d84014810b004840b180200c490280607442060807640010302440000e020007152003000703041071400740c0402c0c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 151532598 1250 151531348 151531397
    0x803040f0b0c0d0e120a1109090f120c0c0603130611181504030803040b011703090d080a21020d0b040e0604120c0803010e06010e011d0607030e0a0303020d 68
    0x3442c030b0b0806565108200e2103942502c5130840000c149600d051400d000052a20b5000d4004440c1000420107002c1c0c5450310a1081d40e016140800610310216a000150380756440c0c215420400f03007010905001c21207080c0503129000034041e0185440380780c40b001690104164403010350b6854038000140c01211220780455600c0582032011004d0b00782e5841c01d0195007031070640b017400000b8092202100040b40c10f80254010341c000e54510940354107203402070036a0582004402e00660041060701580d4694101c0c40039001e400000c81ba85461200c0815901c03003e02504145000c9180c8600714000851b0364017030300250850031010450545a0340902c012a0036100e81a400b07035210400190000700c4407502c0680c0c000c030324074001c100c4400d01c1e5a09001600284c104048120092082140559101e038503004000320074a40002811040b1040c024000d221661b00c0d4000c4000254190500d07010760407404c840b60001e0900b005c02992800c00a4541000c0d40302c860000d40520310080e01140b0214040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 151533848 1250 151532598 151532617
    0x20010e0a122006060f190b04030c0e06031e0f0a03022103041a0c120915060d0c03031b0507090e0706020f121303140c0f040e0a0206070611040803040f0b 67
    0x10603440d00e4000800140c240e00315640380c0d11030706007008061001510101b40d0f000707218894003207456504600e0018103280041d04000d02da00001c108000c9160780008800c0d200c9581c00b000651103150384a81c0e2070400441c551240b4251043e8071011003050b0b800548581c0d040040d01d802e1014034680b080403000c0d0300c820358018002808214084496040302d456498000103503c10305854882e095044c031280240840b185455170300900000306003a03078040c40aa0f4840740442e040200400740b582ea910740206e59010140406c82007009a0030000e560201d440401030304031084603040b65440218201526002400000e0f5000c1d00000090a6000051050302241d01c5030103000e6014050072021550b8100a000403c0341e02030b620004045242c1c1080d2030300480841c4003800c90490004144414011841c14040c007440c546078103060381e22008190f410110b641219110350320340440c20043c01400720300f000d005120400140005101d05d0000007441240c02c0d25604240a03503640c1c0c1070b00c11398010103815 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 151535098 1250 151533848 151533853
    0x30106030203030d05150316030c0b0a0813060b030a05070302040608030304030824040f0c1403161d0301021615060b09010e0103140901020a0e1020010e0a1220 70
    0x1135802d40c1c5240c0140f9888020031310b10415084100c80040d04d400c0340d44d448801c14a042c0e96050040c03080803444000513208a4140070302e040c2c0d6000d40240750450051946d5100c000569006042001d1504405103461009040303504103075441c140261507017098807017280b281d40f800c800080e032701c0c2010003600d1080740c1540740c100f550b580707004500f00107203144400d41c459102080100142c0755604c0c82042d942606640e030008460442400c00f40940d8040c5004c440800e101340300f001003c412041041201404514204940c020705c007000b03009500c1030220b8140e05500200c0c1441d010703507050103409081806525025054100e0f00c4850007251a603010710460031100700a0142c055004400041d0504810724001506403040c02c078003501044195101c0380c560b5000079076a003981f6404955200075403400c4810580c400410a0080c04409141107040a14190000080309071042035202c00300b100690010b5615001040c900500440400c41d401000b20b4203003030000c0e80b80000a003500c001034444000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 151536348 1250 151535098 151535107
    0x6100e040f050a0f0b01060e010908030a0e060708030108060412080c0a080411031f110f031b1209061e0708010b09300c010c0302070b090418030f0e03010603020303 72
    0xa8407800348440840c00d403818814041c0140018001c0441c0150b0076005103500001541005001807030100e0070344178581007104da90070a20100c0004000c50313040c900241002e8400c00b99410100b020b5000e07a050240c110100800001010000412954400c030300c640c860500700c00c0120070946000c001510003811502084c8844041eaa01a02d641504039000d414080040403062001074500300d082414170260840e0486405520707140f41c09012120055000da09080030a412108026400010281c48414a1307076864802084105000c480107020045018040c9242501c6000d9442206464207221500004c04080c401900b0950090041c182681c5070700300c40e460860800516003154609640c8403410b050704209040403180c0c40056545503113581c2c005042046134041c100701507685102c1c1032000d01401031000943c0403500009440c1c0312100c2e03d484010303150105006101403145080d46009164000c800d040d000103c0315000c4805d0798402c000021841c09141c261802880000e4060b0300912 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 151537598 1250 151536348 151536353
    0x19030b062d070807060902011b170a0507080403030e0906040b030d2706030e0d0c05100903050f07060f0f060b090607050109060603030c15060f05040b030c04060609050306100e04 78
    0x1000c2110145900002801c00300c00c0d494800040e8011381d002c03030340d140d962607142017156000300301c002d1001e000031244201010291104c99940c9240c2c206801c14040000319910460701400540d482c0c2c0d90000f00c0b607030300c1e26128a40035240d05e0a1135840ca10405500e80010424541401922110800a0040c0203030001c81c1c0400d42d1050391500540b04012110344c8402c01100c1729010100c01004227560108140011040c0241042c1103c641a010482d80c1180f150100740e00003a6415020700c0c07018001055031250a0407607803400390000d9402c0f0031900044003400d000e283d0704144e21080d0092030402180f01d6540c000811210144101418100103000708402450400080c000e201e00030400403801c0011941c58100301e500c40d4100320f01184000c484401440f09080400401c0415540d00b042014140020548042154419588940d440f0250203800707072014491011001400740040c8016a11240064899680d6024840c0031388a174500150709640140d00e00421543d2510486029403600c1c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 151538848 1250 151537598 151537657
    0x10903020d1716060f09030503160c0215040509090c010813030c05031204170a020705060a03021b0607030f050c03041b03080a080402120f0c060d0608010219030b06 72
    0x41041d11495440700a0141d000ea61000805001104083e44031102d000c518020003154440e800d1850441e19110202c0002074100d000c0302e4010240040032100038168410440d401d49160000a400606050007180e4034500c0c14041c1c400e13210101c0e03e002a41d40d5500c07426076600390344202ca0f0f00180c462008a805040480e0511500c0e80c000d1030300d1008211903807110b40c51a4010303282e0514910365001008140141502c8448103510001c040300e00d04004944000c0d030301d032410300a0b103105100c00240d0210b0640264103d80c200010000e0310400c4c0144507084980b158030484030316002c64141002c02030004aa88a0140725010402d60a4107580307481d1200003c0302c811036911314140e09005404404603052070040c0c101116580e8a1080500c0c0034814401c800407201941d44c0d095102240000c5005004100d4980540c020b40e41320f91501503101040740070f485640d1000c004d6520025220403100244445c00d5643d40180c0c509100c9901150309000d00c52083c0c0300224044884d20001d01c1d08140203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 151540098 1250 151538848 151538869
    0x240903080f0915070204140c0901120b0405040606030b01050d05151305030408071404050717060102071a0309060c1303060c031b050c06010905070f08060a030b0702030a1404030201090302 82
    0x58556403400d00042002080300f554400e040390071a9200420741804502d010302402d000700c0d4040c500c0305942d04141c42c140e2640d001d0030416074103104207454100b0390b14405500c1a4001300d00100f080c04281450f0811400404946c00181c41c03c07810354002103201e0a0600b01452941d034880018844103901803d000307212280034201c0c7d140f4400c0303411a040862010000b41000d0503030680a404805c0c900031410040d40160000b0600131410301042200302500302405484900034088501900d47d01c03040101e0500c0302d190003502065050b60b01ca460050090806141300300b100804a401c181ca0301d416041c0c4074002d0507040d003800303c005003003800002c100da0018501d40f020b500b804590a0030707040ca00c5804007003000c42c4100044000c40c021a60765800c100303c03401081081410801e0b410900c10040a82589002440500100d440441d000b5164061403400664001d1916845420110700080d00c07544428000c400050401d4240890241e050088904503a4142c44146005266500f0300404802 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 151541348 1250 151540098 151540117
    0x180f0f090a1b1502030d0f060509010605030709170c03190b040807051c0503040203011b0509011805030604050105160207060c1202010b0d050d02010e01090b010504022503050424090308 81
    0x9400c0005410200f0400c00b40001255000f55449660800c407603401c5030020b01c0c03002c4905d4240542000a503d8030300100f81550f00e41d00e41075070344e50f0b01d080d030640302c044007580700b90100c4064040203000603401051174100100708030295041800d220042100092002c40054107041e0f01d0008a000940c1c800000c100003440340e410340d009101080807032403007035200241030790115000202304001c41c5003e1282d0840024a41921910890030b920000c000b030140c01c1625050042c03084005030420320342c3c0b102d00c001b01002000c07a0300e5403502d4944240600303010f580d04012201140202079600340041030410640e65141d130344007451041500c0303680200c0b015100041c01c0d550390710002c404549800c81401340c1640a04000c040b0b04c500c602e4002c3c21150b81d03038451541d6907d0f003000400012000300700941110411500035031108145660364201c084030301204812182d00422060826800101520440300100e8261081c050f10600d01000c400546a401000078900e000c00d00006070200054070404e503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 151542598 1250 151541348 151541393
    0x100531050102070b040b0f040506160302071707110d0302121308010504030c03080a1e0e031c05010e06010804030203030703090c210c080f19060b180f0f090a 69
    0x49880301822030344107042c1038900d800f002040200380f080311880e00c0e801c00c1c60445003858526040d00c9554072490042c21100c01c8041100c42404401d00c2034040c0d40d44250131840303020000c51000a80700c00713035004040441f06290603400303c032510300d062400961505d4054010b0985c84655094015a69018000c054800955070001107407800e824401d442c81140f003511500c88803001401c01610102d0002c21100e0254203000188000c0d002d81c1c0d401c0c4800048012000c5031400c54481068214010041d48c480c00380b11540c03503403103d20015080305040b10b00c4054284940d8850070011180e104044601502590041000c0b0f854507120b980a1007040703018590340380a03a43c9a800c100300026811031400030200640c1511014031902c103800b000203111690040803c0d10610741d03403070740b640c500641d000c00e101d000400c6801130158070b4000c40d41411000342b0003181801c41000400d442c0d4010b40b140c1d510030207040c000400c0138242210a0b1301458480c40180400c0e45d81d42c1d07443c40b1810f080000c807500315 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 151543848 1250 151542598 151542691
    0x4060f05040b03122d0a0e0f060c0705010c0f060513030e030a2a05060c0f010e0a0308070f14070305040314060f0a0c120203100e0c090109090c0e0a030501020a021005 73
    0x121085c050b0141a100343d40b0b0664402c542401c015080c0b02d010340301792140d1010030038000c004070009107940440b0030a00b88445008068203180b07443e2241c1c1c0d100940040d04080c1001390b8000c0e5461131001a5110b80c4840b120030040030241039131002501c078000c10940e6184207100d0030030296400c0d2281580b40f0110a81240e0316803000c505590080c00200c1843e50018881a0741003400380a0728081d6441c0100410800c000d82d1801000c2c29000707440d00302030001500310302e400a44609120000318544481c610381e5284180b0340102030713512610055444081081d00040d6a81c00414503900441c1d0715840b48030b864443c00d906038001d10b0030b00c148101b03001041c24641e02d8010311b400591f00c01e500c085c8046690624011514600340f1004000034100c2600700a400701c541c0e0040c0000d801e4030051480007440d610f804000b610f8403012024071542c0704005400000401005400401c400c1a8a03402d484695010304503150580b101510400881c80c4003444403006401905003100c80445645400c240f103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 151545098 1250 151543848 151543927
    0x30a05060402190e011724010c060c0c0c0b0307020a030e0604030203060f06030f0a030f1211070605011404020702030309040c02150405060108070e0402181504060f05040b0312 77
    0x340da0b8034000c07240106107100050040c03503802a4400700d00344c40c542c4060145290000079103500000015030301f15842c09001c6900b405922485000d028aa48039008102c0e5110034603001d41038040b058002c45000344a0b4030045184c1040f40709881c00390840380c0007440388541035a402e0f00c10903040c1c0300302c0390084401c2c0030000142e5001c101e440c2c054100350b9021000c030b04148080c981441395a500c070105a50140c034080b0002580031058800390040340c6803044850034060b40031400703090f144804150f482804074200090140641c0800d04944181284020030105c100c284400e070300170380030060340c1900140050f952500700b54000c580a603d4600c10341d04c041e00030041812203204241c0e0160b45640c130803401407010000801c004d801809072045181860300d031650000b50003525420300b030384818403024003092030162068044001c1060090091100b035880c2c130058104425030303228203480780b8105064612207080c0407541a0240007503400c003d14107640c0142403804205403141c14064610b802c54000308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 151546348 1250 151545098 151545127
    0xc020d110f100b0a0602010c02030f03040507050a0e0a05151507140105240306010308040915080105130b0c040308030403140919180e0316030c15090302060a050c030a05060402 77
    0x4080b1403000740040c10380140c6052042188081d00001700f5603140000302c4000365000002d885440c8a008003042e61b0f6078440c50824108076217944180c0c1c0284d0710b01804501881c1e404103261040541c48000c10065a40c00e142e00008410100e42c1c54000c41c1215550350040a40d2004183c8039018040c07140c1c000b81060300140c21144212002c00b83d4a0040107210400e000e00c050f071242e40c00f800c40003030496504586809503507204074400c2c082c01c2a40c030400050207481000d8000010310401000308824a03200381e074400c90030000c02c42114204050f50000300203408020603501030703a0704002c01c1030840e40c17165020748007449a0302e461a02080c0602441c1d0407540d605180210314044d103a584003201d0305c4c0512030b1614400302d064500c03c042c10003822902c0040c000003030342e85441124102800700103490a0540e28036018080c050824100c030241e110074080c180d0085101d142c8a903084940c150b0b05c5d8a4014100c807801e5407003806000c0100040b40f034820454200a40090b002480145400380e007820480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 151547598 1250 151546348 151546363
    0x1f0e0d0624030c0f0605030604020a020c0307030b090c0405040b06040c0c12030c140c0a200a1202010e030d050414150a0e090a0b0d080a0311070c050301050a0c020d110f 74
    0x28101e03080c1110900030055003001c804024030013200540a501d04041d4090000d0100038462800b4550101c0c005ca4030074420042500b0250015081d94035041d00c0741003a504a10303046840c40d074680709800751b5106c01e0a0903c580ca11840c2c20102c140d910340c64400400000c0e00c02443c0a108020701110980c0220b1640020031131204040d840c000f031401c4101c00d020b01034051802500304c0c000c5042c040010f503000d0100d0300c5e03c0d0b19640054410740852005549103000c42c0c06035001a00b000e080800400c10703218284d4042c804500036265007045a85040c10540d0f6103140d801410000350f41848204410519a803400c0c3d600c00c8000e111907107100604419500c40d41140d2107040020300d0241800c466410815100742c0c22078894101400102c9010022489810101e4002411080c001400505061083d0301a0340c1030301030080e500303942e4000f90509040c0072401d802650310a510308804101804000d104245441445801801c3c180341700c42400d940c05c0e040c840c141609405082110350b02d000082c40f008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 151548848 1250 151547598 151547651
    0x10f0e150f0f04081b120a1407090c0216051507110102120304060b090906090a0b09030f070c08010b0d02100309020414100303090905090c060c1005151f0e0d06 70
    0x3d000c205040c0c2c4091132070b400c005c05194056101405840898080403a010041d6604651b5220180d4041804603240c442682d204180940c034003418222807a80c04240b8649070010380305038200003500c2d1030030000004011501812a1b1504010702c600113440c50140820740b94050054030000803200142510365071088604a038401d560b1030302101c0d285440165a600001c5000040c501c40c178000c400c46541719200000607003940c0441c00000c2d241c1d001041124201643c08041c544c0f105035520304034007181c04600030001c540d4207200ca00030302400c0c43d200c02d103052038000300600540700007800c6c2036004119000701a43c025071641720009081303244442003401040c41180400750f8620390f003001008200c032032b00702034106403c0905010103107800003000700c420701c82240d280395a004a03020140ca0814548032400c8494248810401013510891082300d281d9805c1e1040045005c2c8a8100030103002c4030074189011271001054a80f0b641403030b0b4071801c0d0b070f40c4c4100000544054011554402d013150b441c0117 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 151550098 1250 151548848 151548853
    0xa0515090a0306020903062413110406030c02060106080c04061101150b0c0c0f06120619030804060f0507020102070915080a080301060f021536010506010f0e150f0f0408 74
    0x407602c0e08080000d10392013040d9903030741090180b504409250b00b01800c89840c1c4127410100300ca000e18200741d07000c40e402d030b07058111055841d541d440d4042e0240109038010400760080000000d0340e980999100c034031502c0c528103424034143c203110041d61a480710b043c05116941da506c038054404060803401c84050400c211803e81c80e0a101c1c3d41c0c05207030084401e006802a5a9030500701c510b500d898041c0c3c0c2103800b80800c41c83d515074408000c51049040c2021106c003030480743c4000024080303440001d0055910940d02da12580c0013000d001c2d03a0038410004004c0c0143d108a00400c080c1807646c1c00003600d8051260301a1041c3e5540c07652178540040c4550039600340400100401039a90007170f40d602c43d03200140c0080e156200034031711500b00c903103802412441d000d46032001a441480341000265841818405410030805011030b9440c0200b008580940c0811280c1300d000c0e607030718000c0181e0200800018100c404080201094100c00d400102e2802c1181e0801d21120540345511300c09000503000300d400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 151551348 1250 151550098 151550107
    0x30d050c0c010e10380d020d03030c031406060d0c1202040801020405040510080a030c021309200909100f0f05041b0b040b0406030507110601080a020307140a0515090a030602 76
    0x90000895222041c80542c5600c09809000f4031241790a5102420304e818101c0910fa03120301010400d04a041c0e80000d500448072501401059016802210040659501001401c2d00d6400030560301c1c40035661254020400e000242c2da454a98000c0040f5400a15220340d151105170b401c00c059802c150480a90341c3d401050510490800d8400c42e90f014400104142d07482d881c1101158031034005040103002c1040e44103804096440e1710303200ca00c00c0c00003000e003007002c1d4805081140c428a01e03d000242d60101402d0384000030715200420b14040e0414078054015074030441000c10047c0b0002c0511408280c40380d07a0101408884e1040c00c0c4114010101440f4070008400700c9070321b00e5095000780785c07402401d2005108000100c030649094400a05000600b500d98030401d8488248402440c1d00501c10f910021603060404904c42c0c1c00d0501c29412261404e40743d4204100003864044815007120047c1804c000c0341c039015003414000040042d0240c40c00118501180a0031099041501c680d5000039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 151552598 1250 151551348 151551373
    0x90702072c0f0c220b0d09140607120b1c0b100b040305100911030a0305040812030105030a030c17030703060302130203040b010e09160e04060c020a05030d050c0c010e 73
    0x15586a000310001d20089151401d80c4030310409000301642c44c0c01c20408103950141c8040011404400303130101501c031646503040030f107201700540000c54003191007224032203142d001340c00c00240301ca00694450b00e5003414580400c3e6000020088030403a00c0e0700803c2d01d07024580031404104c0d44407039607004101c155210f10f0300c0b4910841020903503100300440032013000100045100030a050a0322003444401103442030550500244100e000c4440581c18051080c1c0d038010541c22000900441e003c520a442d032505140307810711a940030911620340c1680100c403004000a120300d6403000c4003071184c0c0315011403491109010031150800c550100c0440c2e0746032404e00951800c905011213541c1040c00c154911b243c9a900c40d19a01818072400303d00c240e0000120701c4010061055004294191001101c00d0b56100c154944010090320700341d03862850030705014110351010070b101b4022500400114a000da00e0000e5070b00404008242001c484428000d14001c40020f0103000301c030a046034028180f030703101103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 151553848 1250 151552598 151552679
    0x21060603060609010608010303030f02190c0b010b040815071103040801060e0a0c2708030a0804060f140f06040f0e0606040c020d02100e0a081321030503040209070207 73
    0x5040c1a200c3c0c8034a800420065500c81078080c1076941c9071401080c4407038850300b2280680550714010302901c49114003035040a6000c0500c203a058080c0085414a9a803005401000e20482c001c05d8400d07080198942005407143d4680f98100c8018600070711070750b1051001605580040e04141e8459450b40020062608401c640760303002910004100441040e1420240503c240c0440f28121154010881c0c80da542d0003d01001c0181510825642d6642c0c1200c40145980342c212001c0b149503280c00d01944901259128074412802080c0000b01107480b074071404281c44071700500c4158816155003d03401d0b0b00039507026000908610400900b0281070440412007501c030104080b00071503010082da1400c00c1d500041201d5100c00180c0f00003100040c001c543c1c0e0070441207800141c0351180002d10001c00a80d4620384100721248412020010405c4040781d4030700b00d0000c000500024800d00c0400c0140c03808100d40c0380c00000341e0040b01c24866a44442c400c1c80a05581003404540d445e41002148030740300d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 151555098 1250 151553848 151553851
    0x60a12050408131d1b120403090906060f27050d15020d020702031c081605040b0c031b120a050306030c0d050c040f060305030406080408040e01090b0f0303070b060f2106060306 77
    0x14140740170b032481a11104101d0074018030000c0c01d407129680c40800d041c50301407420071010700509030080c8221515040c02428851114900e039002400f04050240c0d81c4203c1c0407039480c4404400c40750300f05589481d0800540e018001c40648000251120540803110984000c3c180c44a0000d00582c0307801d1980105401c0c050798048200800606616014501da8400c013070b1540071074420f40b0100080b940940403101d500840e004140314400000300e11602500020290160242c184480c84498422198072510b0351101c552404841805102c1c09008074029409990301c40720203400c50341313045d0720103001071020451014280d41c960064840cae10b203181014080c84170056031040c0103002d038528603a40c0d940c0d00d10452088e42c04000410003c1070411952104480041c030b024031842c6d002e541c41d1000d040050810300a5240b2807000d2243e10962410080180d819098000c038080303005540d008140711601c003034494003983c01220780114420100350706080038500c1603454001d0030b845c0b500364181071900c0c90 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 151556348 1250 151555098 151555111
    0x10608060f07170601110c090a090c0503031201090f020d050f100b04061d0d0f1208011406030604090c0b070f050d0e060d0218060409050a0506060a12050408131d 71
    0x412004000f03205445100c981c03c04000c0c130f001084c030009040107904003003070740481c940d20000034014010f2684064114045440c000c15007541c119a60743c08251340c2c5d00c5030040c0c001c69120824010403912070f56500207441d03250726900140c038103640b858008003207810490395103451075000000d10462800d91001c64000d07000c07200400349030509140001e030810280a0010316651207281000c2180d4440c4003407070210f141c0c05120200820860b15040c041072110003541d000165100c400028503112040c0800d44981c3c018044918607250030303040c030014008840c400c1e2007901079080005022620301c2c00902c03c0500400b010032820716503107410380c101680d4031400d00420110540303181a80c0e44450480350120301c14000140d03281000c0ca0007545005480d001c2581c07101c00807400045d0100346401c5a0b104000340c0c1d004200c15560f442c204400c60003144007c20025030700c030341c00d000c05442c02d611003600705000312002c0c7e080a503038211904048180760491013908842525131140f840307605480503000700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 151557598 1250 151556348 151556357
    0x9020c0d030b030c240c0f07140405060121092003010f05010e060105070f050102030114030115080d0c1703010623040e0c0306180a050610021f020318010608060f07 72
    0xb00000039130240035000d031442e0f00004059904550000c545d01300c07103000300e00b14142e800da484008541a03c0b08064400c03445240b82c0070011801c1854184100761081d0b00c16140d1040110306181d400131440c0c090105190840e9803900b00c1c0c80410110f100507000c01080703c1101c12180094404c7c103080d100228000816a42810010b12104003042d82540d48424286001501e800d15030414007140c1c030282c0005095544000000325410400150000840205400921011448100d002a90050f03485440302c03a0300308465403a64030b0b100b0300340030005030301400070301c20024924101c0c16965842a4403110120b030003848100c07100c080c43d58416982074280c4d004213040c18034160b0100380ca0300b8011320308440c001e40040001d08503075a088403407aa0340c800d042c14410b1440c0001010000f80019106c840c800c100d410102c1705014800200c08201e0142401d000000291200818010307400c05444540c3c0000d0004420000d000c00348030714802481d8072001000642824040a0f40380301010f0088030802 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 151558848 1250 151557598 151557613
    0xf0f0105101e0f141507050d120213080304060207060813020d060e1501050a0801022107020c121606050301030f121b0804051003050708010303030902060409020c0d030b03 75
    0x1071892840c822a801d0300000c1900380e0054845400401d90354200a00c450700b00b1001003494419a20311400c244001d5488528607005605a02290f0240010091007540b01070010540c41f803003507010407a1100720320783c00350400083ca1052010181143c02122240e071002c1400c000320b66041040a0041520341006102030402181482c8500c10822002c0d0051001600d00c1003001010b501c025256680e04003030300c4084000c1000048542002e100d6030b031141c1c0350000d010510220610840f640c29070100f51514041001084652044500901600550240196804c03c2e40c807900c2d240795098400c10050000b00b102c1d44030313501800c0b0040e084003080100500050000a400401c1e60f070030183c0040c100c40244441d13443c112282e41c41e542c032031310000c09401c03954000c2284003000781056900c03c40c1d890001640c03021040b021120b04440e890001149400100042030080d070010840c9400a00100d10300364491100300240da011600d1406a80c0c0420182c000c0d2a90622030119040c0c400c50141c502d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 151560098 1250 151558848 151558861
    0x120a14040c060c03051209030a0201062301030504060e12030703180206041206110a0504030605130c0e070207091b030c1e0f02010b100903020306010603020405100305180601080f0f0105 81
    0x9008103006a800b4454200604400d0500800c240c0c0c024094565401b801407810702c401c1a00d03038001d10f42c00030166003410f20200f04080f2902100d44002120900031000d0891500110003034a40a0026150940d40c0c68094036681c4060022417206100703041596a02d0030041d10040031540c3c03000c004030101c0e182120f0000140d640c0e204540c2200c2c2240c621103001161401c001004101c8608030b1261200d00084502c03503070750010090300841f801008100016529071200103210040040c000341018000e48007032040618040c1d88540009140c81290501501da918110407540c1101c00394146101c40300c08a60441c1d414058207440d000d00d850700e408040295207401041d007200b00c80110500c8003895403107170300d00c1c402d5101780140d00d40100503240b0910003420280c6424034a0206074000e00400c40003040d064008d000701c03000c4441c05408004003035440401140100000350401224006140e0340c6900c1890400ca1980600041b4020f80030300e000820121303151a480b2002c0c01c0ca80c0e414103040100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 151561348 1250 151560098 151560113
    0xa080a090f06090614040b06010909020c0d11030c030d0501050f041a06091503010306061d010303020a030e01090b0705010618090206180a080304090b030118080d09080906120a1404 79
    0xd0703042d031001000c82e803010301d031801d040a03048140d44543d10701031400800c0140001e04000f10301401c0d00b03880301c0c003c8070f807a480201e0a078880d05a020400f50b102e00c03003032040c0911450700c1c0900320b6021010740c0c1c20011211001d50541d41b0109007100b00310348680042c4a1071400d000c02c0c90321098201c81c104080c50481d000b03d00a603603c2c0c52140c0c4541c20124030441c00e034990034101c0b6640720307405000380d0362580c41b440c10300000c05050255400c5002c1c3d030851711910102c4440c100d41a01e415400400c0b0030701840e90102c2d440c0c1d184400d00d904106e100c0e4000038100380f01c07d010703144140c0b003080081200d60410440c1301e1802c5084401000d56810a151000562a003808880c810611410031030304020881c0c0224216004a80c0480d074a88800607000034429002e520003e20341904600910525000000d9001c100d061a0b5002c3e006070800c01c901c1c580b1591b541e0003800c40500c038403045410b040d0a0400514241c010355000895403d039007041004001c030700d1046114802c0c260850440301d09041d02c2e04803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 151562598 1250 151561348 151561373
    0xc011b08061327030c05070e04030225050901030807020906010315052b0305030406060f05010f03020d110a11060604180f0503070503040f030506090114070c0305070501060603020a080a09 82
    0x4030b040e55500782c01c280d02c0c0c090a980f04a01141410b50750381c43c3d40c1e4074005041030340f0440282c6a5005034040422902d10900c1c0f40f0b80283e4040d80140303c900038601c0a1303903103201d0350082ca01c01280c0025000440c0e4039140349590003140200c02d40fa44462040c0107105030b040d0010000c4c0e0400d40784c00354003e030881c1601102c000340c481c00c0e603190400c09072800c0d41d52001e04145220100521750b4004940406a02c50002c41c4554810f00040c808265103001141548110b03009660204074241103024199220f5406401c2c003111404010071720001454068203541e210f00d0141001441c0c4480c507000a070001c0010322380007042902c04014a46161000c5100310b081e4040c02085001c01c0324090090103001c00c1602c0701d03207410400f503030380c2c81d561000b01c45110f02c0b140c402101c09000350070002c2c80d80d1506100300e00845c2c854407840d000c0399903145802c03151400c0980003242405410702110011031b13000d104031009450181c60059070341070b40e990301505440004000341e0005007456401000035440074000d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 151563848 1250 151562598 151562629
    0x8010e01090b151305030714060306270115090501020c0f0d02010c14010203060f01020102070b01030303110f040b0a020f0313030303090c0816090b030106050f0d060608030c011b0806 80
    0x14070001e06030002000340e4450f07042c0052a52021942901c0c69503c0f804410445104404075103e51b5030f01c1c0b440a0003844c40301c00c240d5200380d0a10007d003c41c201040b5078007211070388003140030010054140034051080280c00c031001440340443c0b8409419044540800034100c01d000800100c1030020005900303000707020701580612a224000421640038400c0312003489e40c04000080150b04103100d25000390001c0b14000e11071150071450f40c000394010b00c00c854025402184204180e0f003103132420b8010300f001115100850030304100107041c2000078009440605003007503a46643d60a150002854008102d14401158000304904807110718803100000480b40c0c1414046030903012824102c0501d915035010550300c9c0030303880224102e0350b9042c110400390345810300d0402007640418213050880f0401d02800d60009190f81021215140100b40d04241c148100070105990340c4400045085400082e1651156034680c1922504848442002183c3e80c1d414500044c0d14548400092002c900e0f81c80074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 151565098 1250 151563848 151563851
    0x714010e16090903180b18040b0f0f03030d020c0307050607050a0801060e04150905040b0109060f03020f03121204170708030c1602040c090f080a05060408030a06030210110d08010e0109 81
    0x4150041d00d0503112020300f01c04040c0400d83e20240031b031b20f60f440366a013020b0101c99010681c1040c60302e445444946100649a441c0d00c07003643c13051048601c450400568584024041401d03042403e0005280a54981000c0c6498107410324115141ca1005020701041c408240083c5121135400b201c024111011803030400080a84000811b00034569620002d0081034082004941c46629812542c05a0320800030b00500b603a0724012541107500d107015038010303640104010005480d0014140741c0d6403c00400703070b500350340c003504800646611845510a10f203a9900c00c01051010f81302e41d0307004610140d0003031403614245507603900c2544001040381c007a13000701080d03005107026002c07503034070f071a96000c1c2082240f4507040742c0180002e47c0078420408450407102d80411490800f144003100540e004000300035136103c6030780380c42042d00001c202c5074107182d0780c04000001da070b2003041c0400405040e85070301901c068035540c601e0034802000150420f02111000402141000c1c441150454010050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 151566348 1250 151565098 151565111
    0x20724060e04080c061819020109180c1205060d0f1b230f0303070f080c100c03050c030f04030809120c033a05040602040302060714010e1609 62
    0x1048014603541d001180c100c0403080c20401005110b500030318502c0c0d580380c00c0f20700300d580b83d25150340342c3c1ca105010007a00b9001003a01a0841000c41c161412051050500625070b944650300681c0c246a101030b822405625540942c1c6a940c1002403205002c1304803400b81300300c0c41c00344c0c0454601d060601004044111a00712001404013407032038105c440b0b80401581c10282c3e5500c1010241c04542541c100141341e00d000d90855500d401081950b001401901840c142481034075210510300b074414081d20191002c01c00c10040c0e5506000c40d40b410800c0940006170400305050050407140010000d0710110303400c0040c00384080421040c00d0740150325252000c02c540c1d50a505c03904003d08040e83e041c000c080030a02c0d1074003920100c042c3c1402c0010150360040a01c000700600d900440780b0292050580d4031079280700702a900351b0131a03503011b400f61001510f850b583c4da01080e00d80e44020000d071070b504407804100703242e44004c2c080c00700400ca07500021304000e080700d0701c040d000d100548aa16035040d5100d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 151567598 1250 151566348 151566413
    0xe01060e191203080403020106051002060a0203070302070c18061d0a0c0212040e0603060702060415050405191a090606011b11091e1f330302070b09010207 68
    0x1036a11010b03100c2002d440c0401c41070b501c1c0281030000c0c151070860255003400c00204e168102044483c0140d081a8010240c9890304c3c0b10107002940050540c00806400704007003004214031008200c001c00751141c2d07044084e000401010100c56254200716414201568903001a0802e0925103030406c40f68000020104109502685000368006e280858848081000100130300410300c0030b4814482601910010b940e0101d040743c440c0000c0700d0050840402244c1e400c80510158841079109105400310341040f00b28008075030304088403030011100e0072090003c15444c0ca43e00c000c41a040490748005022506000002034501d440001d414010080140e004400f400004000400203c1c0003621451741744c1460108920302d02030f010146628a00380304041615500310b030001d4680c0d500ba8442c50b04204d4107007035254204500701e0010b03141129030030751106004060107442e901d400031103440040e51814680b808440d2148014010308860f441405040046202c203220b42034041c16012443c0d0000040783c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 151568848 1250 151567598 151567639
    0x30d080a151a0a031e1d06130b0907091a030d1107050f0609040501080105071d030a0b07020f0105010b040609080c0a09020f0f0a080a06051c0201050315060d060501090e01060e 77
    0x1d184100200301800d50b540781407045d0380c1c4020541c610103404019019171583c0c0c807903520f20050741d14140240b0340c1d4403810041480381400641080a5030191504030b035540520400785c1740b020380040c4503c1006591040c061400f005141c10146281c1021698900210032154613440c003445598022004000c0c505819035510b4111015104010401c102558485160300e0080c481200e024003c10320540c00110a1307049000113403c4a5401402004044915070f6900205000a000d00e420761180b140350851404c800c0c0981c5000c0e107810004030340c81d2850020002c1680440d41d02800c0301d41c00401440c00a42c55004080050320040c400141c0d445003120b5111000c1e114060428070f446101185441c003032a84100b409010386400d41d02885815100c4080001004110038800d4a01c038008030708000550150014580c8082503050750121100800080b0f0810b500400803000400e030ba0b02c0003800250303080b00c03080f030140845c2c6003400002e45c103007100507010358034a00400d4842d0b03480307558808084090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 151570098 1250 151568848 151568861
    0x10204030609060504020405071409040903031d010b0f060c071202060906040603060e0c0a0804061a030106030309090c0206010f06051e0d0f050c0306030a0f060b030d080a151a0a03 79
    0x4000300001c10050505000500041d80c04a108608242c045892701d032040114000c0d0b0350f4614403040c545100142088014841c0381c40c100c060503101c1903c1281c4a00705900340e61030803040c400110b94049660200300001a410307174030302c2c4a400300744180211242c001800000ba01e040032480c0281800600010f1694000c4104c025403000300000c0104030554160010022118107500c0000b81d03407500c01000b05103000307680c40c5d800041d03540c500240114030305400c940c0500ca4805001080c03103044801007400c2d50320980059001c1003a807441000001a148144255151244040c158650500c0c00001e1481440e10400c4c00700200480c8032517603610380d050300f99096100360b0441030355003c06e4202d240141901020041c00300c1d01c0e03c00003d81c01c000a40c1203c2c49100300a024103003c40c03aa40d50303078038424a40342c010303601e0a40d5524070070642c0e101040404024030076a00c414915203030401003141613500b0300c5514881d82071806804c00600d10319204d818072034a0102c0c0d05984590800710224000c140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 151571348 1250 151570098 151570103
    0x1701030807121121090a03080d050a06120b060a08060a020c0f01060e16111b120c150708040b03011d07030b010e06030403030b041e360201021f05010e01061106160201020403 76
    0x46d009800420464100010b1900421040c02400695216a0340c08104e413018030520303803440c0801807941e0000b8100001c180c0d20550040501c1180d43d1035090b0145848011640c1101c129400501c503003400c0810000031071038a640d80700a118040c03c0003104104420080c0003030151204a901c1810035a014115103000c1c070f0840300488070290814239810301c104818800c130394019041d00191116101011888080b29400604400c140001c00d80840d522a44410b00a0311001c074180b201080ca00b4104c0c00440c0208a00710040c1409210080012a50007003d0044003c3c980351401c090496604402c000810890854100d91690345a08054001d0a48030a42941c4107160101c4014030240410381c509200d98140000c00c050300c10807006940344c0c80003800c031100201021469105082c0800802c1c007543e44107205032120700d00081c280c003008000c0441d60a00340c40d150300060080c00740d00914940101000c2c0382c40311403598440e84464440d035001c2d04403445102c51490007603002d030003501150000c65 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 151572598 1250 151571348 151571359
    0x110906130c0206010f08030a0905010806060708040311090606030403080402010e0612040f03141806250b04110627010306080f0f070f06020d0807170103080712112109 73
    0x34951007000752102403d0040d13040e40000c500001c1075400000055030a14003036501c98285150030b00b001500c084800800c1940c0c006003c00c15400050f0f1210040c00003107204035040414541d00c41c00300300d40c2950080c070060058109008102c0401d9000c03c09540198080c2045030314050064045100c503c01d0410700313290503c02406001c108112075601c942d081c0c1c0030f0b540c1e002901c41c0350240d0400511031104000286000c0c8041c411a0345400d20041a02c816405031541459084018051030610f00000548042e21403070308100c1445444038401690740313800c40c0d0240c681000b20545d020030846882c40c56201511803120200b09034000e80c4084040e0410302e0480c6d480c07000c5541304a50390301c01c182010340700d4002c191000503050554810401034401940103428096000c4108a070358900050444d810846455504da50481e42e402800340a1401506e80c103a45890380c2c100540005066040740701000320300c90021001107004030311000c00c0210600d40080601d5400300040785030107980500c1c0d5211 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 151573848 1250 151572598 151572611
    0x90207020105070606270506010e011b0b0c0403030219150e0f0102041203030b040b030a03050a02071203090e060d0809061b03030705030702070e07050d0f02130305060a060f0311090613 81
    0x40c0d4840b1454542114402c0c062080c06c07040b0a4140031754a0603250940420210b0056070002d47c060302da0718010440f408514070b05038a40751540f00307030040c05541c441c03d0003200240600c241603040c0003a0391a4280d403091000f44c00c08964410889410305542c0e00c01380b56952030b4050041100788030f004003240320a0000c2d074035152074080c0644100c28440d011030200389400b51006890906015004e130300107000f030140401102c182c6090320f0640c419442041140a000b80200f40b87c42006981105c20307000380c0d2005407030341c1081940503440c040501000d105518144111000908520485000b80c1e0b05a80d00c41d15400300341c4c817411109007121000d81290001108200303010340c2c49400f56100e07003600e500311412241d5400101d00140c01c00c0d108440055020880c242010981360810030b1a240030f00c4005192a12080303c0400840d119001141c81d600510180304418a141c011780d005003104954010040d4656130711514030b0440b41c0603442c0211010400105a596000d01b5950303c100b03440340c01d1200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 151575098 1250 151573848 151573859
    0x7080c0a06051f1203030b180c04090f1811010e061803010b060304080f0711060a02060405070f0f05090423072c060111070812030a0e01020f04090207020105070606 72
    0x580000c03039400d8410a403443e2440020000c6441e85022a010b6403401c0c0200340301c50b00d00310094030b200d0502ea500164900e560340140309035400e0040c42a444001081e40701e0313007050929001d4500b041e2030f144056050040e000402104980030f000346030380c82841442103040c076a00581d01100c44006540d48414046003c40030340712400e4285103100411002002030318030200070014580001d89001d80181028414005000640402001a1801a02010b10345101c940015039a030f4821181c590042e0440410b00c41000002c000c3e503000b0300b42598400301000c1c00d115241c0c804038200e1240620410352080401e080c843e00c05148580d03200c1c04100008245000380035150760b04110710944144141244581d080d07000c0002c2c2044000203038808958140d142c2e0301c011241130040c00508001406101000500240200054001d404054600a48a1800c2a481011280c0090707510000381d0040148920103100b4000700d505076646c0f080300580f00c003079500048a1074042c09000818030351609001040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 151576348 1250 151575098 151575101
    0x1807110709061a040e010e04020301020d24050a0614030a020903030c070303020c060301060504050d03021c09210b0103031101090c0608160c0203030405060a030905100b0108010e040309060507080c0a06 88
    0x41c2d40c480d88190f010b61810070303814821071080344141d00881403040f00500810f05c0401d4041d810500040001d400e11107980e50a104039007100c5001c044842e14034030106074445090b154213005140c100c0c0c0f4800b54a00d40302000d001c07200030f48281c0003d10340000c0060500c80c0e043c1d05407403907514094104da0700c41d40031102895481c00940010707005481f0703054901a0518104046a058600b150b42d0316051a10b043c060003003001407100d044040d405440d128080d010904441403c11078510366801c01d032a0700d00b08001f20742504d1003950854034860803803c1c80214040030341c1c0c5811030b60305103081c481070100d81c503c0ba8018451160001c00c0406043c0000614a030f00c81c04d035038010103000c40104818041c02d44140c030000c00c03030f03030000390560010302081044d8034101c0c0c080d008504c040d00f004120b043c000d58503a07040050176019036424540d10303110600956445000b0b2405810b10740b829004904050302c0282960489110786c204001002500c0c0007003000c028151807903640000d04892410026281810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 151577598 1250 151576348 151576361
    0x61b07050a0f15021c09150c03020301140d0206030f07020a0503070507060e1c060506060f0c0a0b1b1e04050d0302061501030c0c1b0302060d020301090c050304021807110709 76
    0x10f811950700e140075a100e0025100701e50310060781ca0001055240c1c0903441a0251414503c02e603180540000000c40080390350140d07134a440d80e50760380180e4170343c186010126001140350300140604c0402d1748020041e01d98070300312908030500894041040c1e176610f00892030542c020100804a00002c2000400c100d00043c0702829141d05807100e0f00d6100c810001d00010034011607003602c4c0c28145050400105805512081d00210054450f61030710b000800c100302c05910003001c0807595800010840144072444a9803504011410b10036031100d1640b004132103103409141c035052049444d000b4032800d50408035027107600500d0041c1c10304014800a0034069101d0004a484421501c0302c04181e1040358800e20400350705400c10b494004800c03c40c1d459047c0a00e8140001c2d4850028114002c00503136030700c2c1c000e030501c052403a00c003503500e42c107090000040d20b000d0300e401020700c20240300313000041c1d96000654440c1440c1036203c1c006546c07800c4c01100e450b154500b1003142e80c0541390002c50303200f48640101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 151578848 1250 151577598 151577603
    0x60b0307170c09060f01020c130e0a1b06050708030a18060c030e0706020c01050a180305030c030a030c26060f040606020f07050607030f0f0512132102061b07050a0f 72
    0x8050a44e214010b009107582004050303070040e00019408480740c0b5200d00000740b103074909071002458005503040c0030300d485070914050340c8000c410040ea803084000421004080c10451a142c0d09220042c0c0d1881154000540040805034680091408941c03006164500e46904800284161040c114020340200050003481710315000c0c0241c00304819000160302c1480d844180e6410f854280c400348200c0f04ca610b003c40b400c04400540c0400030200740b040024102100701c40700510b6650070b0003170001d01100e4000d030003002442102444003040700d118640700c410910000c14081c0c40341d034407080050134403400c9407c107561040c0f0709003012603003d50019100848480c1d0000301c0390041e13210780410519006140c001400507803901c64040286200d52080f48030840e85090040c280009001e55491030078048030f11802c02c000c202d404000340202c003048244000c41c900901440c244446030002c0d1540e030000c0c40c0c80d10683c86920101c1c40c0584036022915815041010b03602802c0c400c1c50552111848000705 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 151580098 1250 151578848 151578859
    0x60f09034b0908030408030301170c0f0d02030a02041401050a120c141201060803090f01110c092805010503011415010c020a0e070c03030606020106030c03060b0307170c 74
    0x1200000d0300840000e10007544211542500a02941c88900c50000344451990412001003400580d505080010b0009005c554000c0d40e104e40c100840446001d00d01103c40005a0040a4500305511840040f0300192410b0b40c007113540c54642d00110b4a03110803454000c0d0804e01c1e02c0030322440e5100c0b80d1480c03810303240100c0e1080090f5030b42e50070340315140c0450071016003c800d04900800072141c001e407486090700f0016116101701040c040080d401c44806034030460041c0c00003c2c1528580c1742503100318540c24001d00306038040c4900d030001d650343e604642c8001c6000c2c02203007001c9280b001000d010800720281143c1c4105c00b22103800443e40c0038250030700c9010700039030902c1140044100340c11030042c030400900c84021048200341004603020b80850005a070019003441c0007140902402807501e10a6880352100e030f40e04402c83c60b00604035606907012400b107900d410380510024500f40d101c90126904400003213104417051000070300b022520740c0151980340345648008207004c80815421140002181c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 151581348 1250 151580098 151580147
    0x50703020c06190608031c02030403020a080d020d0b09190b21010f060905040510050408160f03090e1e0a060923060906150a0315080a0512091c060f0903 67
    0x251755546e8051192404101a400081034001c0d00040d406164080e010b44101d400c030041030340b9028017913403214105030780190300040c03405448038480c02000380f4008161003210039440c0c075007410556035841040c9600450346801c0e480010744d542031413440c040142140c00086605100700c0c0076008007041040600c09904000c1c0c0025510f03503511400b0f1240d81c22001034402c0f900180c01c0100203000051007115074040501116440d40c04100020b548544a01c2c04618a1100c9040142c020f680c2503000342d0381c0b1654002005013420185540c1810200008440a02902c80700406005040981c00c451026442d0503a10f26401e0400c0440741200f2090b0300480805458402c240b01021004440340354000160744900e081200d03a2070000c1c038407801c05d403400080e0300c80c55000c000d0300e030700301648071000c0c0c0c1d800044c00d00140300c000d202e8400e40030f49100b0b000c1c1c80c1103000e40204141d50035401080b6901240544050700380191900181c0c803044884200f04103117107d901e00070b458408020b81e0400803418220 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 151582598 1250 151581348 151581359
    0xf06020106080a0507030201210501030809031c050406140d0504260f04060509121020190804140105070513080109050a080f120c0c010b0a0e010603050703020c061906 73
    0x75512600f031360020050130340c0c541160019601f0809490642c00050004060019506128071034180690301c90700f5955502c601c50b004061901c0c895515660b030b0700b1803940d45811003d4101c02100c080f00c0c06403c1080c03908009039414112401800020f00c152801d00c0100000c00c4690988201480d140312541d03020003081081c25201c80c0542e115000d03c443e803c0100b44801030141001c0d1030030300e80003081c01080801410a4506000005078544481c80d210000381c0e0400d105c2c46101040150030002180c2000c14000c0ca1640391700c03c03180f96109004088001c00d00703001d4024081c100f003840d200001d1105080c00400248590f025052018414820000208a0f0b46040c0684c0c1c1c40da5810400505940e981510b840701558402404e0f664a6002000041000c08071010954030900130203603216124101c441c0e0040c291960f101a041c070556050302c1c18041c1d04000056117041d03805074a0b00041d00c0c1d84004040d0028891461895941c3c400d0100300704903114202610034047c10034860510440c0d503030740d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 151583848 1250 151582598 151582603
    0xd030c020f07060e0d020409060c1b02030a11210d020d0f080f06060903071409010e0105010903030c06150b0a020f160902090a0f0e04050105090613020d020312040f0602010608 77
    0x4425100c5a0402c01042000703901c1840b015002d580010001c000803151540018100e89080500300d40c025241c04542d00b40c203400c801860203a80d40711001c401340f01d0030741e8000390b2920000d680090080c0d00c01414914a40c0700c01c24010701e900d4240c0c102a4808101e10040d82c0d450707280800320340051041002c0c000d045803007450311040c2110151140e0025440d403880c550391500c40101501c2c3c1016090028001c4c0d035408120b11401094043d060360014081e2900740880118160403002c4001443c100402c206d90348003090070100d03500f5103050003140b03074907107020801b82c40945034020801f1201030703001c29103001050040c04c0400164086600141d1303088102d5441d102d89200c1000d40c0400d0701c104101e580c12580080181364402444641100e8590203c100c900c3e609030403804072800d000003003100b00403091081517005030f0030000600c01c034034041740b40364004040305a000f4088c00d1090818801c5441c1000b500341010a42005680c03143d490f10762410341028a0f2085100541c01c0110000320040301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 151585098 1250 151583848 151583863
    0xf040606050d02180414060106211413110d2118150c0605010902130602030f0a030e0f0d02010b01020d080103050601090c091203050d060b090109180e0307050d030c02 73
    0x1c4c104641030f02c20b001d01c0b086140001072003603d0104680340300e1050068140324590107002035845100030080f680c100e0110940c5104040700c801032411140b280340d074240d0032a40d5440040d001495680141515205548050003940035030001c00c0c540c0c1d041c04001150101c2c003c4103285440c4100000b1261104840341c0307074a81d01e0344c59003140d030007014405600171024561790000c180c100003440f40301590303410040f18007d030710010f5169030126080003031000d04850301c0020007582c070040d41000450440d12025120708440001415564505000d240106010a1350310082c01002d54401601c50400a806400b103001901e00601921007103004003070003800490305a03600030005181503804c0c4410300008100c004140018410300c580005411140380c003c240f4200e120f44e45407034403a4071100120b410348010390030080554030107003c1094540d070b0000942d000c07661a50b5036a003070b0b07003460000d980c01811000c0c0600214000019400140000064904141c94107660104400300c0046401c0b40c440c0507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 151586348 1250 151585098 151585103
    0x40209010b18130506030706050a09050402032805060f04090c0e180a0305091906081306020409020a260705031602010b0d03030c0e030c0d0803040c0e0f040606050d 72
    0x50040060140a450074007500112640320000d03400406001c0004002c103502091103e4026100c8040003094102030142100814490412078144090b243e400351848500740a079030301490b03000c0b0001d07610340c8110124140c0b8400300e0030301211001d41c140440c000b801080b40d006010341649044c41386103080c5407007401041e5400040c102d02250401c1c1d20716800800242c981401e81002c0301881022400600a020901e84039031a42e0303545071820700901c00d4844800f080710054000440d0208405600284113560200300501299800d003210700d4a03600034025504940d8903d4404a10390600540128040f074800340c1c007600300e0b6011013045811040342c6904a039201c00040c0184089082c40700f1811100b0311085440c00045030308008103001c11000151120142c000a44840e030f020110f070f81141500003000802d4010f000080040000b160301500031aa00800011b400000501030081e030700c5011005e0410019110054245200d0601304004c00b620b064440c0b61600ca0001101d28200303502408065 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 151587598 1250 151586348 151586359
    0x60705040b0708130305031308060a151e03080a050409110306011b0c09050a05071707081611030705010e060f040b060607050102190305090d02030c0616110a08040302100302030402 79
    0x420f0358404000f90883e14224184140700080030001610a0002e000c81e00007501c50000c14a203414426031030588060030540c6854a0f01d0b0200d40d4078440300701d4030800e840d401c141807001ca2541d07101c2c021210780c1da40d001402c4400003040c415446544800100304590720260107000141d00c0e0304910500d88015140540801c0e016104111500f41100610100c5400303602c60b914140c2e43c1d4881502950030441320785100d01d607903400b00820640c02c64035811200c900c01d0f10413000e52030512009400d001c0c0c05480c111021a5190b030340308003d4070560f041641d0b00c9580c0c05594623929107107021340c080d0040c02045107142c0160f0700000c40300b40301d2034034a51065800c0784441a80343c40701c1050020a0703000300001d54a0b55020040001001c0c500c03000107011900c1c940d8001064980001d085040128a01c0034408542003004040e1443c2800603040790009200d40f00d0140800d00c014094450015104503442e040c01181c20130010b100c0c8070405401103a00035075084444c1044110202c0c100d10088800a6100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 151588848 1250 151587598 151587607
    0xf0216061809111813020a0f110109050706120f060f0914130213020c062a04060819090b0a1406010504060c031409040e030408070e130b04030c0b0414060705040b 71
    0x580d9280380c0c0d135000e00c2d01500c940d0308a0440e001d164180c0e4844141c1038041417504556100c901e9008050302e915848010007080078040741e90b12551507501500c074200800c82d002d07440001110720360b40030b81d201141003c1c007001030a03919442001c42079250301c9601c13402450b0060124192182003200c0d441008083c0d4490918503640d03003004124079400c4c040e940f50603824000e008050208100460203080525044140c07004600d44003100c0300000e1038281000343c0180f100304009600b1030f074a140c00ca24064841c1091611141101c0000c190b0600042c11010540007840420181540200b0750120340704000c02403907076424010358192149101c0d01c0002442402e00034046485004003035000d00d200d0624624040700200020199040443c00d4140d40d04005420408a00301f0003010004140c0c11410a6440c0741606074030a80740c40114002c0c0150310803100007000c26105500291400e0780c0400c004545c0c0c141410002c08056054101d0000ca00ca0880410b80203801001030f101158650710000b441e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 151590098 1250 151588848 151588867
    0x30207060f090f09051503031e0903030706020a1e02070b12092a0a080601051f05090d08180d02090a150315200f09010f021606180911 59
    0x44118010a041042264040422622201c5031800c3c0100034025001c58503080614418090900200300c07144a644200000390b02c28a00c981c0e44621544034030a0603498101590100307003588115a00100000d00c0060b80d02c01c1c041e0003076280404000000d00410003a800400c0503691400b00340624100540148800502c0314000382d2182d038015650001e840200140c440c03948141c0030000080b00d0b540c90305010220050030310032040401816070200500705075140001003400a49000c00078200c1a401c0c401c0305100714095004c40d4a450000b0307014900e2001141032044160700020f619501c042c41c00c60701103031103103060301c0000b184e550001c20400c15070300d8101c5250000e20700fa04109050040080001012518030080900e08845904010540c50400c00118155600071443c0846540051100149100030401074601c03140c0c00707081034241c07401001810b83c03130b2040070019160b00715450580800c2c500d0313201c11082e5030070802040030351840c0d40350140c2e8001e4a41d0405480e13102001800800346 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 151591348 1250 151590098 151590107
    0x6070204090206191e0206160c02030a05030406030f050105030c010f05090315010b0309012019031103090d0813051c0c0212030310090b010f03050a0e0708060105041803020706 77
    0x2280344003d060a203400041405589400d00842150012070070300d060451810100c0d05022200c503603039101511251900c0d490307202c105040740000d5010071006813110011514108a40d041d0560003000b102d0300c0d5a5076002c01806071400103071440c80e15040000000d558100018650400c280585810210007034400044403142c20100304264180f0490346600c3c00201000300781030184c06031089440e541e2070102d03d45800d440420b407549001501c2d80f2401c68105460340c054a50120743e615100c4810285e103001200682503011452800f0100042849030740b050005001d6514036003a21a2007050b80c1e1011a800744614181d0050580d412440f4080094242c0e20342054071003819007481801c548040e0007141d85501444008115984004280310f42b0000303244004000749802101070000c00f4050340001c11a4500317190079404d00d0b4a40010a124a0172034000c40484c00d44002107400b50f90380d6542d880e076503000a1045d00e01032407074000944c03604e4a107903c10702a0a901500180242860650b080b038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 151592598 1250 151591348 151591361
    0xe010e071101060515090901060903030c0b0c090402030106030f0b01030b01050f030c0d05070503040c0510051206030a02040f061820072d030e09190f0207050109030206042006070204 80
    0x114955070783c82011071141d032801310902101c408a0701a0ba00d6044c0d400900110000681000c0b040c40f0300c0c01c20400c0020380c0020b00c1d9001a52201003046542c803000d0800301c280c090600a03c0d40700307001000100d01954154440945c840102200b030003800d2500c401542101c00030111580000e001b00600c900c030500c1c1100554100c0c0c1d241042e00d01e8405411148000c540055070a1000502c0000900c000e0200f43c11001c00500700c2214188220000e40d44040c2c102e1003504a0120303201c0350440001c01c0c03660305111a80d18207030094001e0120a00819510006211700d0081c6048038201c00d083d802002c6082c410076880300f002c15040500c0450424a0b005240c100c0403044410103842074030004400d1807442400c0301c100c110f080b800380144680c580039101c2405496014000c221103801c0019070043c0b40302030078100c1d50381e020010f403541c0710304007401c068402c3c040007401960130403003134804240e80010302900ca1409030540004400c05455511180190f04100f198011400e0010b1005403410f6403018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 151593848 1250 151592598 151592627
    0x515090a0b190b04150f0206040b2a040812030108030a030513060905010c0318020a1509030f080405011b050714180a0603050d031404110301110309070603060e010e07 73
    0x1100b4000c0c000ca456031508002d078000d4856642c0219081000007105142103242e05450308100c8600b1b06140350095823018000c20140200c200d45021a100e4000b8807480c0c0d41c01074040064903c243c0c40c0d585100b80c10340c064400c1b8460b600c1000342e902c800f6184001640e0580343d00b840610b01e0014a031508a000d0200a0000b10410700c88146000002e51a0b114003000b05100b08000b04030b0740007884000d021540c0c3c0c10140344001c0c5044880e000165138030051035090b50501c4002100d152501e201c104c401a2807600014080c90f1420310304400d00008201034021514240d980000c1081c41c0802c0c4403030115100f074014610b500c1504180301100c1151480c0c50300b60070103030010440f600d1030031405140003410b9540c401d9461741d40f9000d1003400410b00c00b030078148080341024400c92070080c001d0071803042e0043c00a440d10010359141eaa00355029040928550802100c040e10703402c0507100b140e11405c69100f0080800d242600009007001c2c66050141250040802c0072840c0d03440d80e8003980c1c1d0301c403209240d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 151595098 1250 151593848 151593859
    0x8060d0204090218071b0b0a090c080a032307020916050d09060b280b0a210b150310140409052b03060f0b0903070503060903090a0815010506070807120e01030515090a0b 74
    0x309041030708000341e0310f28901075a21510070824111a40d24140480303031410301c0913b401c00401c40961a8181404d42008809086100f01110b03001d00704c4141c040c60340c0c80c1c130005082403040800d001503a00329441021040314901004807c00c041c44bc00c46002950560481c1c818940030004c007240c020291100250600709103020350504a41850341200b44040032081b290341e0712500c08141080381a2a2009400d51003991860070010804400c000062041a00c005441d200300402507e80e5081105215401011910715140764801088480000ba03020911841010420400107100b4052202180c040003500c00382941070001c4092258410300c030042e01351188980000d070707940742084041d01c500c80c410040c54440381030710300f00504c43c141c82c0d01c61411a4882c0c010780308001014071001c0e0450394200d071b055507115103601c0c01c10481e011b810b002a2203146c026898050b410b40100c04c0741d450620982c1c1c10442c2d41d6810800130251030515106a4001e42d60a00040014010741c1c0320341c4424400402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 151596348 1250 151595098 151595123
    0xa140c03070608190504031b060f062405130905130b090705100e03060c031801110901030c05120f0702101109010f0203040608060d0204090218071b0b0a09 68
    0x40303441d0400300d5010320700089401040001c945071040043c0484081200d00348024241902c004084049490a86550410b00c00e030340d41c00c0000c580e00120f98211405000d0148683e03c0c824800000741003070000d0748083ea030040c0b07062464030400450301c00c007002410050301c070342c01d00e440e4500601001305042c40c85419408828007049080c00840d102d449c11100a20310701d800c0405005400a034104100248201c4d4a040125550b003c941940d1088002492507226903a683c0b403203106105464100030309510380303080e1848402800008140071803007070300c0a003c2146024003c07150391169445411000381044013141f0030342009400c0642140c46841110803050314443e202003140c10000c6100680c8400007505115541c202d0181040d640407400610b041c03518182d80540b826600500540c899001c00d10038204659843d40b0441101d43c0281150b07541d11207251002c0154201a40d048010450503080f0509030200079106009072a844121107400c1d4035415401c1000d01040001194855201c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 151597598 1250 151596348 151596373
    0x10311040f09061a0a0b07060b1504060e0a1a09011437050408060a020309010617030306040605030718050604060e10030c090c0f050705010e01060b090301050604060302030a14 77
    0x41002d0507000c1d203c00200700b5082d5440c41035094100903904e0285106010070454100c0c000c081c0c1d030507150030010128880d1408000144005003038034920078254004100410419440f0010050405042e9040c1601c691551100300c09045040314040d80380e00c040000e400031b94880c8040d040700780700d420401e5081501c6c4d01010001c1c41500401d00c8566261240c1845801a000700c0f1461020141d0400a1070507003007030416a180c17030f0003d0507201542e070004049280300368258000b0000b060b0341c4520300d10b0414007080c480e807a540b040e07684a20803820190042094500414100c044070030040017610907a82c1c1c10344110180a0080c06c256100b83e81d0080010700c44138240b8070910610b05695204511410b600d066520b00a07aa0000e8440c14600720122006640240c3d400c40c07500789604250391a280b0500d8280d01500d1035801d01b00c0c0303950030403800040c016020000380480300c02c110001e0001340d5845041c0401c8403100e106c042e615034811120700010550b181c0700c50103044c1440d01034079807400020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 151598848 1250 151597598 151597601
    0x51602040501120512032e090906050f070e0604060c030e060417100221060d050f0601080c040209100e03100501031110020109111302040806040807020a050612010311040f 75
    0x7640181c0b43e40c03d805018204101051040d01c0c60048000c0ca036904604148000d801c175600002c0d20100340b40130a8010351026000301c6100001015442c600b4007a030250340c40d010300505820340c1d00a511001c824007013803c05000d820600f890150107440c040c103042c500308044540c990100b80950074086c02507005040750f1586e50040016081025024900e50820f5100a241808406a01491a105000155210b01c071468050030700210052455201d860306c600041c108080700000070118400da0b940b03403006500125200e4104c1c0c207402c3c1500c1c045030280007804140e00c5583c4046621080b10172034603544500802d01001ba445014044400000300c2e150b0b564100c80080e041039840d101d2282d088003081ca004000c5040b0000725100910061929541c1d801c48a024074400a100b1044015203208010266050781d0040c090b600c101d554034100307801d01010a6022660aa02921402c40c01240506010081b140c1c0c9a202100c4425660b285444030558141c445151a5000c0d860b400009425001c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 151600098 1250 151598848 151598851
    0x30601030b0607051c11030909060402160309081c2106120308040209160c060b041514030f120f0c0a081810020c010e0108061206010e0f0a0207120516020405 69
    0x21304024500f903203405546120308100020001704000400031020b00340c00c400300590381300103401d40d01400ca03a151300d00010301900620640400707444080c0c07a1007081c143d1001090f001c403182c140540c0e049800b00c110385d40306800428200404036a2309501c446443c0700185601000300d145190000c1e0301511270028004020b440c010540028841c5000e200c2917203000c2c92015080a07920142450100e07500e0300180102c0c101c0c01e805004280c1c0c8001149031a1140c0d000250245128041da040860b11500c00c10070620042803543e01a105c2c400808105050008240311040110ba40c9141811852114250290300c00001c618250040c0c0100300c0000340c000c07020389507405460a00c0e400c42d290300c00601c0007003120f12200c0011940801d20f141c1e440c0c2d0300700e403807d44a44001e28180e84142d42c0e410124158a140421001c0e080c8101800042d94021000400e805146030302042c41050325103901b48016400f0300361014010440c80500100c1c114040c02c010081e4442802941c02c1c06162a000142103a10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 151601348 1250 151600098 151600103
    0x6090301050f010e011d010b03040318090e0c030120071704090606030e0105070807032706020c06090d09050126040510060602160504020901120c020a020f030a020102060a02030601030b0607 83
    0x3603000600422903280c4d00d142c00341400c04408581c60020140c8180d030b0306810b00c284540c003d8000081024144121400140c641c001c503000400705a4036840113000700b01d070150040707a034040e0392541c200034a0103000d081ca482d1a90b00c0f1051f0561400003500909900410f02120b40d803a05170012406a540d06001e003009003440140029018601000a02a11072028407021103900d400c040204268100c066160041150700e400904840455052980c2a44060107464400241e000310b070200002600207044401e500010b50b20241c54a0b240542e640c0c41e00c041e208081606003005210300d510404840980b03000e8039110700303c4001220340326008150103807400d4a55820003003041d540400355018000041409200038501c543d070018541084200354090b481c856500098281200da1064030303164041d80c0001d600700301e040c07080075001e540c410314940300724014400301c81f14903020f02d004600d030300c241c94040e00900390b250341d0000c1c0c5600941c0010b01c000d0526950320183c05603612948007802d061403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 151602598 1250 151601348 151601371
    0x3120c031c05040c050303130b0a1403130c0b1303020f01120e06090d140301090b042d060504140a0e25030b010509160e030a08030a0b0108010b1305010e0609030105 72
    0xd03d401c2265002e40e15411180c041d0740704200c00d8068070300342202c0c002203400304c1c0ba1054a500340c019088a455030b0900540e4140308000c420b001c2d000c1c45e8510030500540c440e0380005006a070300e00010015009414003c040224204020030141c185451064614841450f0804460068143c4281120300d0898403514650120007080039a039010410100c00c0280e60911401d13000801c0d0b44a0400e200c14010440c0f0640c5802c5410700da91925001150340c802003544c58601d911011b41034800c418944986d00300c403d070600400040500341032281505400541c01c055041b995004810b10180030184032069035031181508141240c0c0079401c0c04410285a100c0ca00151440c41c180035034004410f8002d9403260001c0403e000c151244200b80345d8148103e82002c1010030503e40000742800e0108102510f40b00d0b00204000000201368400700403001d00740c0303070a60166250b500d02c203600e028030741c10902d840c0c41c012030501003580260f407405100440185000d1518072100c0c00b081c25100c0030741d908400310 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 151603848 1250 151602598 151602601
    0xb0c0f030903031602060114060d06080d0c1a010f12020a17030a091508060d05011812030e070f120f0501090c031a16030c0c050703030e03010605040b03120c031c05 72
    0x2522030480c0c0c800d08440c1480200b05030f50500c4846490340100d230500d41c1c030a0600007010001c51040340c014074000c00d60760301585d028119000029213030310b00080b021510072103802030600712008440c0e149030684a40721041c2d91810704004010701d0301c8000342e07426a03205c0b45400e00011800c0d00320070700391a4528000040c2d52600c0e050400540100c940c1c0d0010040110b03080b60800200703500c071074003d510203000c44518522080d18108680109030020301c5440c103490b48205102403040360407540d41d1285803554108003110280c0c80c09612200580034011120012800401c804404800c3c1c4010860203450350841e00041a99030342c0c02c540c00104202d070741c22201c1c40208140306a8030030340300507444001840c038074034a032040300050096500380c0450185a40c5180201c3c1c524410200104031039800002c6504030350300c0e402c006e041c40c000010024425070803c10081001e090500502400c4503000c2c004100f141981c58060200740c2100041c89501e101c1401655900d070143d00401c16480c5600c0c40c000303040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 151605098 1250 151603848 151603861
    0x3090a05060709090605030a0206070305031e090705010809150a020a2105040b0907030f1b080a0b04060506030109030207050621011203030c0e030c01081005060a1d0114070b0c0f03090303 82
    0xd0b05c0d004c2c0e02191007900303c2c200002c0036880790345c119142c0e207505181c540e54a03650410024007081001c198480107040d0034041240d50b1a000800c241a100d00742c07990000c0c2c0c0d8a04a0813aa60001c1c004207480005140c00418130f4074a0a07005024642003600700301c1880003508051a94140700b102c05607000544441c148000d11541d0841d0a0f007100314400504144e1f4116207541e81d000e0078001c401440613911820704d10703001c8891038a0300301420312081601d04411a07801d24000c14282928141d60081c50700300890460302d01449134500c200c0d450303009881c0d614500010442c043c2c0140c1c07285401d039203200044050301ca600e1049140a0318400f19a00c090f0f8402d4280181214842d031a06c805004240030040d00c55a8006094944c525003480c141805030f9402c0b0090007015016840681c0141c0d000c59508842504581041a00d1212448103000b0301c5041c0300440d400c4d03806181541181d41c0c00c01200c2c010840541d102075202c412400c215103842c14a0b4104c1c10203900803550002d01d41c0001c03042c4480c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 151606348 1250 151605098 151605101
    0x50c1e190b0c100f0501030201020604030c060f020412030f030c0207092f0a020705040612110111160501080903040b1215030709020d0b090907090e0c192d0b03090a0506070909 77
    0x1030040c00c03213004025540c103543c000b0b9a03820001c1c10150500c114a0f8480e010002d940e0428200c0400c003507000c0d51030300c3e034485152903074030000101100841c81c82d20090301030503c02d1007942c88480303640c4d00034490709181c10003040c010031003c01840028130800e0768031044206406180e54000c450412515620403504400904110356034100d18415400c1401c00c002d5600030024400c07070300c0e8001168281c5c109114005075402810751514947c2c901580040746c075800f0809000d4000c44400f070301c038448690303502c05a082d02c9200c0e034040c8000030201440f103080708040c59005550f00050301030100c1940e10b0b25000292030055250b1080091a4001504914402c550300504001c0c840c00d4401524504029075001d40324100c46c0100c1c40303c540c0c0c5000b0303101d0390101001008170850024041d504100402c0c034056540c0c15190003941d00002c0400d4200d1720820241c01080d002c2c500e080d965415503801c3c00c901d81c1d2958000ba10412840c41000c407003c4c042a000d1249034003c602a0b21417601480c9000344140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 151607598 1250 151606348 151606361
    0x90c0a14010905040e1005011403160513050417040305012702010906030b0a0902070804050a060804050d081005040212070e060406140703051b010207050c1e190b0c10 73
    0x58200360820040310407660003014010544104880220f150b404a5035014a0000550122146c00d170600000248046140c003100208200503001e40d9555000030898034403d03001c80c404c841d002013030003000741c0b0a042654000768205102d071804100015505001c1da846820a4006440c1079540e40785179900b240030b80b00c1b9802011000c01c0714028400c00307600040d00b643c0080c40b80c002031648515640305240c0c1d4803003417540030b4591040b085440d8400c0e81890102a0494065030340078060340031000c5003e50241e21441e00c119400001040c0040c2080e104035542c0030041c111040e043c00300361010440d0b81c0e490010782070252403101040345e01c1c82d103404d000b4440d103284400c4070b00800040000703101c829400040c0f55141c9a24051a41c0c0d607642d9071400301d4140c80f8a40321300d0b0304006400e8030b000c0b041c0340640050003e5806402110003042c00002040080a20044851115140400441ca0341d040111059200060400030525203682c1c822900c5026030022417110025000802c1d5081d05c60410b10404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 151608848 1250 151607598 151607609
    0x609060d030c02040c050d0c0c171e09031908070c060809070b18040603030809101401050907020a020402040f061103040602060f100305120406110c090601110c09090c0a 74
    0x29200300c1900e07140504085105080a4050307030321440ba01c105980684100d99461142d580100012900504024080240808116007c441600c1c507001c3d60780c8002c0560361140c10618400c842c280c1c802001110540c403405445070980031700030364082c010205010710350b2047c3c0600c0039103031713500c519181c060f00d11401c0343c000100384503006041c03001d045000660070041d0740c030740070000f683d8455045003200304541d0b10100f154443d081c402c1c040201584110424026044542141c20790031851460300140c1d00c1c107000d882d03220b4040c10010002d51506070210f5810012174015148080421340102c0d00380e81c81904142c650140c104d104111256000c0140796020100c040a1401c060410100039140c08020700190b074079007a000c012600d0810102c1d1070000a6030301a0440c1d80d20006071001d40610b80103881035102050b022612001880c60101d9510443c5500900028240ea0345000641d181e990708850f10909101d5024503181a40701e03001ea0a0003240d048000f01200401d41d401c2220f9248180c004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 151610098 1250 151608848 151608859
    0x3070b1e040e0405010f0e1f06080f0a030906080c0a0c081209010515060306060717040801020a1d030a111c050a05010f15030c1208071506080f0102130b0d020403020a0806060906 78
    0x61f00750140001c50740180d00080900c40007020304c040006a00075049640001c1401d000c1c8901d41000001c0024211820501c01d480e0008060380e50a429207080ca01200c4012088804000030a50300e44100301074455a4460542542031010030100c0c00b07600e0504596840315617664400740041c00c141141c0c4a01c41020071181a8614641600490748034081c40c2c000070403601c24804181011b48002c000e0b5800303043d20600031500c8080d062401483c42150542900c010610508080350a08000c10405141d540005202035076500001c28401075520304070943c003d050309040c807400041d0b018007034140f800e8015000403582c21500800300c0c040b81e0714040044002d403095802000003070032900400d4200c40c07804165003481401c0d42484c000703610030340c62f0003401d0103903403c121180c8041680c400c00659104004aa2034030b10401c02c0c21b4201c0c81740c1210301001c40b410360307001c20042e14808020714040000d003c025003481da9907070110310389481ca0307008071010390000400c03ca21400d00e0748040f0380c000001c41e81d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 151611348 1250 151610098 151610111
    0x20100f1104050d060605060c0d080c0405030a030e06041a070b060f090c0319090b100f2105011107030f1407030c0305030718080307030311040503070b1e040e0405010f 73
    0x55103645441a4841c039402500e01200680600c51a507100c007004140150045950b003c40c0000b090b01d984400700208081150385000c10601010078065074203a0b40d014000745183c90703054034103580640c00c111090303030b1080080002003000c2491140d016425601079000d1034481c5402c5c40c118044a0000f42028090b60394a00364012130703030362205140e410645080c107050742d903180d00704041c00481816031440049410050b1210801c81001c0020380b044142c080a4110703291a03048001c00310016100d1410382e402c800c41c000000310320090417903807201d210f0400056411000c44124919400446090300822030700008401c0954100b424000710782c802d171029616041055401504448030b5180240400c000070000425150041e504074440030144846000c2e90796035808102c0e543d80c403104003180041d0400000204901e9244281d80c20340e580100900140360030030482643c2d079044140c0001114a0202e0011684a4400f0052001d0701a2030021b101c00c1c0b0305404c000742580c11548020f42c80624051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 151612598 1250 151611348 151611371
    0x30b0615040303080925090b0d030203041401020c031c021c0c08091c0501020406030c17040f0f06060b070314160b0603070b0f0d150b03061020100f 65
    0x24200c070203495250400c40e51079110800340380d11b01101e400f100f10540b220200c0640040b41e2140c0740c0000c03201a0841840021100014000d008499040090143e07106220174081148003035107128440e4018070440e4103035846d40700081d1802018490755050041c20104010100394103004424500c50a031084007180143c002d0700a09a42d0b400074090407058000c1000c00b00d607a15402038900c01c80c0c8426524038504901c1c14414000c1d030045c411100841e1400c2550554640640b01d5204180541c0d8208062a96107489000c0c2c90100400100c030008150460000081c4d03291040c00c0c040d044100c492500d6042d03034900501402410b01031010002400c1c05203400d0340d1050029008a141c5c0040e00601684035040400e14112481c1c1005c55004008515480c01202c038034040d180c444081c86051002c107118401d842c00c03440c098001c2c440c07000d0007003002a4a904104100c6e5592104c1d5281a45608071105651803a020400d5021480d070780040300315040078506400707170350050f00380c0c000100040072421 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 151613848 1250 151612598 151612639
    0x90615031b0702450c0c0a0b090c0102060708040b06040c0509040204090b0406090509100207030509120a0b0106020102031003060e010f02030711190b0c0c07050a0807030b06 76
    0x1407240101c89072890042071080300750000d035102240e018180010030702503010248240245800d06000020701d00d0103260300d016a0742c40041d0480d6400700800e05a407259854078015034000c2c00820242c1c0702e007072803100000f80074641c120304c501821000341000400d004002424608050408010040284140008101124011900100129000a101080d4510a0360940110303810203034458400309000503040c049402600d400780c41103404011468440100e40d003211030035610b45c401940320380056144010107a00400249000e0300745642004001c00004020020003501e400154104035103034020032441c140424003616485c00203508628003042d00381205541480040c0106d9141c0c1608040c4000030340c0402d0743c540c40c7c450255035920b0a85005402009900308840e4144600601d000442c079002c0001c5c4a2580e200e48940c265859110003078010360408511411940544807001803507583e008640001000c1e540b018025152850a040441c03900013850315000e035080607030702e0603d000e44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 151615098 1250 151613848 151613851
    0x40f0923070e010909060f050306060d030f1404030f030f0809340f0b0a170708150609030d02010e070909050a0b070203040f0b090a08010c1403060f130b09061503 71
    0x82c9401484106410012034501000e81d0026580034503102010650301c505c034a00030107442054003110000e0b2a190140414444a54809800503404000c8580c01d58401c809540d42915420081c9050030784a40794482510031a42d012000b140080310b20702015a04400202e030310840880103800602c00520f00f07205c55103940f45540c80380854441003505074501d40740c00c14018107038800642035520303110400510700c0d0f88032203901d2020a000c3d80a819050802c05d091304c1c480d107076941d2402e8054560700b40030b8640c44003681c44190703c02028048006180c9003003141d944040516800425400902044541042100c1d0041c0c400740741400356810100e400055520191070f80244c0303800c01079641c02d204078218010b982124410103601c800c00101ca0344814040c14446008581c11031382070b80d4a40100f400c03500180320400100e0f405c0540f041643c071001d00a154402006086140243c004900080e00e80e034160f01040c1a1a030f455070030400030304110302e19551101098510b0541c0280000d5424560b000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 151616348 1250 151615098 151615111
    0x170705040203061c11090c040605040b0a050c0f01090605160c020d050106030c0e09010c0806010e010c03090b0d0911010f0804060209041805060a0e01020412060917040f0923 76
    0x8002001c1041034664507404c068428041d140c1d0600c069242c508072503140600110b2500c6801c44c2004200b082d86040200d5084034610780740c280c44e291901c680c2600d103800c40084c3c0402d0100c203100c0d440b50a07000b4008801003d0001c0f00005458120b45072850450b20050040724611011014000380c581d00300342610350b000d40445e075400c4da00754030745403041c090881c43d00000c001c80d820310400500005c807220001e02440e030f1803009000340f4052a00456188108440e49800200c400e080c695407540140c0c0b901c070019000b4074044158035104e03d141111a84810000c13419680d03500a10800e0203001d41600443c1403007440d00040350450084020003103071014001401044e40080c08009503550b550110034803819003041d20444407001d040040e11400d0488000481c641040030030142410107100b01c070152007403680d2b203c1d010b04a503150300005142c0c5010480d000aa410700c807070f0b9914010340251005000750380e03070341c14124280b814440c259041240350003800d0030a00f0341b544000d00d0340d050080e0b0114 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 151617598 1250 151616348 151616351
    0x7050d050d020609010b100539010b040515101101020301060c0201120209060301210c030b070e03010b150c01020c011a100c1502210906070201110c031e07050d02010204050a17070504 80
    0x7410034000e000c2500c260590b841903000781d641e20740e1655509c40d503c80007481c03a901c020400c103204c3d10700303100948104641d55842d258403022404900d10f8100c120603511009440d058280c40300c03141d03034242203034400e810a07000b2900d4a40040f04560380040320300a1607845007400c0d400c3c041a480855481d00060190040100446003200f100f0305194010044090308034042841d41543c81c106074030840e2040e03400100240c4e10071035912503800d0500600b2040c4d40f015281e0800f0240030251040301e90011200003044d550200480001a031090107500d00d00b4219400e10a0081404020441c6105419882400b401001c2e5142400720351201103c581d10030f0b040310096940c6c0000110b002d68010f40240c491969100607051110bc0071001070818411000d9030001c1101100d2401800043e0252042c0c020341035100b044594507080310089040502c0c0480c458250400401d0303907450b42000910582c10b0010f030b5020400300018a4811110f200902680c1e01705441040750f240034944510325806814040c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 151618705 1107 151617598 151617607
    0x7020f06070b06040e0f0114090d2316020d060b03010510050f130e060115092319050d0501020903071401050313020307050d050d020609010b1005 64
    0x41e4000702d584065030b840000300702c081c004500c48a000790003903201001e01d50009001d03410070181c0b02044070b0720703030300e0302180c41490b05480d580c000040000e06040b001e00c202003031038659034084140291980c1c40c489559030703181d0710b020f00c0d42c001d4201012042c0c8900340203541d402012000c03c01c400900c11501d5044842e4403041031401910780c000e1b084070800d196031510100640c1e8107040070101250144110000f02e0034940241d1104841001442003581c0e1581c0c00203202c0042d010f4900c4241c02c00242e821300c49101d0011110382c501902e5030b10501044803501003d014000e0ad8000c0c6540702001e42440e226000c5d40000341d90600910480c4804a4410f4102116a03800c42c0f06a40c0d0314155a140d00001c0c0c00060443c0d070680c0c040c080c40202184988400a000c02e426000c2e00050908954504000303107800341c01044c103e07203030f494403c000140fa0f50341c04e0001c600d00c0d081d1500c01d07103c = true := by decide +kernel

theorem cover : BRFrame.Cov 151438848 151618705 := by
  have h0 := BRFrame.cov_init 151438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 151438848 ≤ n) (h2 : n < 151618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
