-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0880
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:24:34.776411+00:00
-- url     : https://prove2.me/submissions/57fd0064-940d-4447-b5bc-7a926bde62dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 158093525 ≤ n < 158273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 158094775 1250 158093525 158093539
    0xb1306030803040c090203040b01090902030c03100b0315070917030909072109030914010306120308040b070806010c060b120105010905060f0402090f0622080607031a0d02010e04060302 81
    0x100c2402000d0000b540110703c00e120080d0310070b03621183d40040740406c3d200181180102c800410203d40c0c1a00a010b1480c00101610049200d0780c002901e8104c114544100d00c644413410b4503080d02d400d00c510080c0d82c00c104d401e000c0714030b40040000d00c210160302591590394241c1588081d00c800400550304914400703401d005060404240140c8940c0d8502c1c0c0c4001d4030030521400005841850158044066141e00e901c0401428540348040400300e4050b8903041540d59040041d81e0322285469040300c40c025117403141a4241130030f0aa500350001420101446819000e0041699020309107403611500038000149540380000018a01000007402000079800e0000115044100e030703024500402c41290400304103040300f002c1c401a4010341900f190300c101c40c01c07000030550404600500101b951290800c9100e108100c0c180781c000714136040660640d1124081004054261089c8040ba03403e1040c28210740742b0240004401081014000341005104802d259580c1c0320303178220340b0103550b009240d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 158096025 1250 158094775 158094779
    0x70803120a050703150b090d06020f0a140c06130305070b1602010e0c06090409020a03021c031205041e0501060b07030512060f09040b060d06090302030d15180b1306 72
    0x109091000e40d19120094940300102e01c2884c0a4407601491740c40c0c0340789040702d1624250300e42e52660049181035070014140c0d020303e03001803198401411149000061f00d81c880a074808000c00102400c0042217050a01700984880304000180c15603102420149c00c000101c19460101c5030340c020240700401f94040d00090210880c4035a20b28144841594020080000300c141119a10301c0c940070758a80000e030800024030f42d0306064204015950010f0301e041055580c07680400c05c01c0d030070440650880c40f51440604100360744a1031780d80d14070075100d40900c12400d0070740710210f10340521a00019606c0c0c040e14403c0403c40e0a402c80002040b4442c00346072582034604003d40503074802000c80d0a81403150340041c40038074004001c004450005030413412655500e075109154504090b01c4141c0c0000827a9642002414501030307405001d00c250b02a60311041da0004041c240c07141c1c0d405803018180c201c4800e20040850300c03000520313880b00c0500419050151400714200d0701d16804618a00c909240d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 158097275 1250 158096025 158096047
    0x1401030b0a0b0c121b0d03050c1b120403030206040c080102030106050f220b0a022a01050a0212040f0518040803070f0e060304081b010903050901050705100f051006050910030e070803 80
    0x1180d117961007641503424590000000f1400c56030100e995107030580d410b0041c2180c41c0036a0380f044401022a004a40c0d0700110465460007503001079004800513441001080100079034038040000074030a40000b94159410100c1c054100e025003011010031040c0860004130090002c4441d00340f408140001541960311600c1d9004240e0040e070040d0b002d44504031806079030341c81d1071003041440540301c660030602401c00001150f1036440070041204500c2500c03040121084c988008000030400030350741110481c81d103000d001c0c4c00010245200c040c0c00c0c440c1c080001042c8a5400c5075449001d5103410300500300848429038000804180141e080300021080108009082004050300c10782a080080b038100e10350029400e07a04207140c010b00041c028040c0a805501034406030420031310403030581300c20000300390038181281c0913051500ca407291100700b408240080030f03007254094003241c601246440d00c0700d07000c16244007005810104042d510b06d1000c180c0442440b420300545413038001e50b41c2c6c480802203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 158098525 1250 158097275 158097307
    0x9080d0311090a291213051e060105040605010c0312270602070308090f0703030c0c1e0e1501052a060a0504020f09060d0b07050c0a0c1401030b0a0b0c12 67
    0x280b0110a800401e800307a43c040e13501c400303484001c070301503000c09045e0761481c40e428507480045a003102c3d01e110b042c1206c844044002e01140d03003105070b10b00030b01c125858801004203850b9181c0c065414005024240408071f0750081614804103d000c1c0c010a0a582a214800c0d200b4200103031646d980540d45442d800b04043c40e00104841c41c000d545104107611031a0313003581c41d0140f210100b1000da210f00c50410003c1c0c0108003182c8000d000c1d45000145540d62107a16048014001213404050940b1005102004a01d0141038101d41c01c07085030904031403072400203800ea116201003010030007000c0141d408900c108420200002413200d040e100141410303500c000103001c003035a040744221100f4400c031400d400e21341c00702071103a000240415203801d019250310000007809000441004420410444034090030030808400340c1c07080106082d450725000315040302d00c034400e003c107040500b012440b05855403201d03109001d5800c000d0841e540e030300244082c2484c0c102500d005042104020918040300c1103040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 158099775 1250 158098525 158098559
    0x306010315090609050a05010b0c03070308070215040516061416020a0816080106140d0f03110d110606040c05040e0a060518010504050601030b0109060c11090a1b09080d0311090a 78
    0x41b07400d02c030690700c0e018105c0c51b03409004140c5815900500801c0c001c81c0c400d004c0c15800c003d80c0d0040d20050700950004003d60041154291002e900042e8280c403035039240110751004203c0341c0742860188004031075802035031044100300690412800448400c0d540d074041d086c4014801b510856200150040e5151403198003481060304551034264001289651450f140000b0b00c0001c244080d9208150385040f0340c03100b42c2005600b00107030401c048100a0701042810100000c940751101c1c00c9602005040c681603000708244e0041e814120003010b05500310041d00c1c1500d02c0341403090090380d5140c051000421ba41c0d4407044d40300e002d0322045050640d11007451410f07640300391000d10a031b03554200103405550100d06c0031360004041c524104226072042c10a00031b102c1c4610b0900c00320300540c42c0050f002e94001d86840c02e120381d98000300040113000c00401d840380c1c051400c1c00e40c102d6140c20070756078440c8a40181c00c0d00785a00e600c01c00342c03682c0520741241d54480340140001d00043d120400c00a07146100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 158101025 1250 158099775 158099791
    0x512030c160f0609060509060d14010b2a0a3c030305090a020906090a0609110301150807020319030204050303120f0105121b0303160609020112050408030601031509060905 75
    0x1103600403903c0c620603001030381a1051515150328041481c414131900e98040e403030300c0b03a0325a6105044510500c140d0515802481c003045410303202c4400a01040211210981107184084850001e4662141c0411004a080d80010002c4503a486158510380001880f1241380180c9400c2c2c10035031884d06104070301c4004c02d40a95820001ca90b02d0105550b9994017885010f984051700d00c002541516148641c2540035409030008150141e80312140000c2d6222481700803020b410110051100340400c030255804c800c0e081c0740082075410a954080e40301e1180300c08440b0070000d192194090f15010381c0440d00207102c00782c1201e550b440101c90b1404032100c107440b403058001d001ea00004e41c519181e00101100102403001e841c0710108603001d041c4200703030500c00f95050301003400f852601c1600030110340c00040c0100b42c04a0342c400c5500c001840f4051650f02c3d00e03a1540349c9010302020404140950368816801e0074000740f0400c8403650041d03040c585d40d1007010000c0c1810340200d103410198010501450300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 158102275 1250 158101025 158101049
    0x80105070503150d030e04060e09010509010203190203070c0f080705070b0a09050d0f0209270a0c12020a0905010b130f060509150403120f12050906010512030c16 71
    0x55110200c4051200b5115058440600460f112540c80e200f480c805400344a4100107440f00f4407040443c09a464a5205404220320282044030b405400c1c040d40c1c0e44010208021442d5291007201c601d054030180c00c80c283c410350301000003140349000e440d112200e19001500e40c100703281c881c13170b2910082d803180d00121a513006610340080d2040115051301d201d190319450710440503003030405200d2021350451050712007003108130b45440562502c4442501840c00c000002c403c1c0f1792000707210040c6654031140860980e001d20700305008a802921a102a04c1358101c400403500410b00000300002ca081c1c0040b000c1c240340c6800091020740d40401008000f0b00d0401403842e1035919184041031404d2407143d80e01160007000600014504000c44080c0c6450001c9041d0810b61640c440c0c041140c40381c01c00c03401095208544120b2a40c002c40c29550b02900c054041c0304a01e020303250b141d19120706125090080035603c3c01c900c8104028026a41840180b400321034640c680301504c0006007200e0b200341c602c0000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 158103525 1250 158102275 158102281
    0x1101030b010816030c09090203070302070c140a05040b0324090f0c150322060606030b09090a080c01230402151905090a0909110a05030a030e0d1e030801080105 70
    0x10007180e01500c125107003c6902000b080d00c00055018040031300c07290080205202d800320f2103000310b1003c1d500a84096400685a00e810315000402411a800641400b900d030840c0c02c00c81d84d90301c01188240c44054602244602c081c00110780740c0f440f0f020600080d52268a07440301a00c4045446500c205c100304200d031301d1620001c860399155004400da094000101c901980c1e000d071207400080d80c2160070720400e80078100e604054815203043c41a03003211066241d000803c101a410f000e03520128004940c08103040c00c01000056540c007142100400700c0c907020800b803884020030b610020165041c00c0f0304071305900032042140150001250228850341d0800c2a12090000c1d92003561099807141191305c2c1c2c0c0801ba10820b5a40d5003007042013541c8120301e154080380c95186402003c0c83c15102d141417901070f010910801180c03281940107a070199000003046008250b00440d101e0401b0401e540080780f8103503d04218066018840c402101d0f44040710000b0109903011000394100c454100007004191 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 158104775 1250 158103525 158103527
    0x703150f03020f0d02240705100e030904050402130e03040f0b03040305070311120408030c060109150905060f031618050601080f070c060501060203040602010b092a0f03041101030b01 80
    0x140074000a50030000c1c021040c1124186140d07588440f900042c81c0c0e09805402c16920b8140320125185203500003401301c1c441080050030403803005072141030841813290403840e1303441c555240158008903104940320b001003415074803500c1d08070703000140c4048180b10341140d10492541d41d80c003600c1484048011120005624801780c000c1d640200d80c1a940c061502086407412a0340c40c040d803050003028061544114030580d08403000300000d00550340a1030700c86030403418190501d5016808a9400350a060401080307a0140004106954881030001040c3c1c42d494049044011261005a0140301e50580b940190301400c0002040307815900b0030304515003444e500b41041d40c03000d0b10350310f001c9610440820711610907000740b5944260700b490300d03002070f200c0c50b103031402682d20a90108016070000541403040b65828012400038141c02e40740c00741c1ca41050340c40c0000801400c00e410b81c202555101030003800c404e880441e5007510944202c80d407a0f00302401c02d032283c0f4010464050209180600009641d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 158106025 1250 158104775 158104799
    0x51e0112020301120803070e1309060510062a02030a0302010b09010b0f0406030c02010207050a1b06080907060c080c0706120b0d050703030e04181b061d190e070315 72
    0xb803030200a00e04101d0149a41701e0b1030b280c01c05000c4034140180c14221221503210000b251320082d41c07520000c51400054246001154005040f08000d042e9881043c4000c0f504568100c01822004e04200c00c04c016194548240f804100d40082d803500800d80c00c007061540c15003203134500407000c4582e01026661403204200d14460609100c18150084c0710030400b2030b001c0e5000e62800ba0041c000586080c501d50b40300307410710481a03401ca0341114802c45040d5044080404400604030070b080c101d0f60f13800e01c2c200c0d03d5500c072550300c074040411142c10b25220070481c250007a11000d0361110104d618140e03d0b000050401c504200c84007055500e000b02e941d05520700101c125281c00d0700708000c2c140341400c3d510100c2d00440d03000c2002d40c2103030712b45902c04c80840003403c5d032075000da019070b40461072441043c2007201c0040d541e038070400400c01400441800c0c801034400c5581c1541040b18060702c01d40001003018000489039110501250381801008603032074040d04104100310211060441740380c1c03200303001204 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 158107275 1250 158106025 158106029
    0x6150105070317061512010303110d0207050f060705150f0c120a0c0504050303131401020106081504151802011202190302070c05030d0f02010b09040f020103020d06051e0112020301 79
    0x1e080d403070f107401c41c03a4802d281c2590418005031890450404260403001d0b2030340144000c40a000e2600010070601d03038402040d01000541c0c130302606842c601180020341e1b0300f081c0e0040b24800c94240c2d170030188175901c440c125034103070383d00c0b1040d100d4103240c806130f43c83e00201c1161061907540340400002e040c044510100c6e002e07100114840015512642c400b04000c05c00c84c502c00045c00010070010420780d50070006440d0114039000441804c1d4103001451800401004210341960304003001841020004551103618014074a205a000c4e6154100801c8442c0528490403080b8907050801c80110003200041c51424000e132203e07180041000103280483c03044600003140f800c428000e0320320851180c0c00400c7c41700d00881c440000640c403200042c5c24484107203c1c50000c11504101205000c0d020b01030324042c5541207607507508525003511010803000030307004020304269001421003c00080356000202504028000414801c6015030f00c1c3d031891301034206c06002c900a0810103103404146d000b1641 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 158108525 1250 158107275 158107277
    0xd030b0f0105030406050601020703200a170d0503040f0804030609020306100305070b0a030609020d0b090903030c03451509031e040902030a0906060905060f010809010905030c061501050703 83
    0x110f9952603480b000010b20703002d003501c0c1c114001c51000202155103850b0380c40588241a400d0040380404004100710080c10703500030480155244c400c184800c80204400080c4601424100d980e030b5594a42400745d00c0d200b420040000d84003040107c1804115406880064800c1e41140e00c00c0d140c0d400d1680407090b4600c8000c105a00030ba03018401c1d10011400342407603020508000ca20681c59440c40f1060781c10007110704840315034550800009251041c022078114540074041c0d40742d414603805009042c44000d011115031204080818407081d070500b44000411080302040041647c400189800e58200c0100708005c0e205080481040b1001e0300505400350030308400031890032102d15141c0304500c85182d050594a04203000010f0b695080c1e000442c821035601c1c0c00040e150311700d0303e4220201d8640380c02c000a1346141200f04041e0ba00c0d081c500513601c00c02424240016540c1100403809400b0802c4000c1150001264030060010002480e90140b505001003402440c9a840112139038054110050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 158109775 1250 158108525 158108527
    0x120b09010927060b0f060f07021011010c03090314040e04110402071b09060e01031a040213020c01090224041e050d03050705010506040501140f0d0b090d030b0f0105 72
    0x144801c16408030ba00154a201c810035011070102c2c0242021148000543d086610748007586000d1030b14000b01030301440211a072601300181d5120341d81c05070041d0f0394000c0c0200104500c43d0701da80c0c0902846402909004001c1c080034601c618004d01a082508086000c04c080805805d080400041901c0076141c46002580241d034883d00d81c80c001c09444000150040d40c02c200c10703004903a00408142d0721120800e0065041850072024074100c884580c403d28400818200600009605030b542601414600748800c105454600014401466036285281c071a880040c0c02c5001c0c55045d00301c90081030003114a0300807140581020300100302c4200c01d041c40c625081005001c3d41502841d4080c901c0802c0000004440d00c810118048031813542c0242d0105401103002001c201003401200d42c030290640e0284810351600340240d00c15070201203070a100d1000c1c0741135019141c460f000700c405680d800058401007410300b844003a4451601001e200b001904000803501d00f400c048484508aa206a440c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 158111025 1250 158109775 158109779
    0x14041406030c0402222c0708070507030e040204121a01290903010c0903050f010b1f120504140709110307030b0f09090319110a0305031e040605010303120b0901 70
    0x4029071140c52044a41e07a0388400d00303081400c605032035030060a01c0c0e01241261101c610310741c103041b141c01407801011075850020840410b0b40300c000c507504840d040c00c100e0b0302c030f0840b4a4162100c2c000d039039400ba00b145c4003240000710b1720320312090b4840d0b65006041540404c00008281449070109014064440040b020802c0c40c650b1640382889000541d1031030a42404c0c8540002400d48880c4911f0400080386850b040c010301205201e80204000c42071b008112285441d00801c030301007441444100c0001c4110700d82c8a0890013500e281c403900020f81d104010a01d4245000704034894001c0085407507100740d9401040300785451080b68401070503103006c0d03030031035440400c1100a03101c810071081d040704c044d201c030b0410b80d00c4042656009059080285468081500d401d202c8041081c40703a00402051590702d21200c3c0340842d42c2c8a90640625110b940c9945164840d084110b43c903111076000401c0e0810801440000d81c40541603901c80c1d59180014407820b600e81040da1a1400305582c011040401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 158112275 1250 158111025 158111029
    0x5070f03021204022b05031209010b1e01090905090d0f0206010605030f0c04030210080429060904080c030415030c0512060f03010608010f0203150604030503121f14041406030c 77
    0x945072940090302c41599411240075200c401c000e0b1070542125a5800070032230f0f004481c20729059a9100f6803001c000c200811001000442e100601881421003400e49004448603900c107612110140c02c00301c0c81031029003048409036543c1e45034802220300280c2074805800c03101d407010451504a4419a550311306680351ba0920103007000000c0c03e4810803910800000005840380c00c0c91024007103107030700ea40c80c00745050304003160089050002e0303410300c9400d00205414040c41c03001542d04164181d0700b0718102e80d12450300c0c0700030340715020715142d4072310010900103060850780301d000a51380202c0ea024005c2d0110701100703960760700400ca8040400801600001c480e810310300d4818076000401000402e20681ea48440c5007191594607040c1422a000000c00084d00002001c16401078015140b05291038599140c0035224020660345165040e0761001180304812503170082d000d8000800c81400741169180d22603c0309034004483e050203030741009914a094188059818071440d009009032030320b03100b8102 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 158113525 1250 158112275 158112289
    0x90a1d0106170a0b0103090b1e0105041118040213030c030c06090b04091a1905041103072c030304060f1701050f04110f0c070518041a04050c0d030305070f0302120402 73
    0x131040c0c10166200680c102083c40800c0542c0104241c410a85000303413055180d0030071190503000103014a00380001c1d1600304101078103c98100c2c1c1110360a00a040900000a0180c4a22001d07070020109203040402030100d80c81c4c450045a11405290179000c1c2d0362601595541a5407150242c1c40405110400114100750000000410b01c1c41c49080b0229200d80001c103070218041120302160140b00342408181041d12030a003041000600142c110326000310010081c550342204591030700303804510450414092202410290780c01803d690301c3d00d4507658007d00b00440e01c003410002036900714242c14241c3c02d01d40703841d040e10006001c01e00312861140500c03001e0081d095a0140d40c1c04104551610410307600058042d040b02d40000d442d14502c0c00003040503aa8020142401061050042c0070018844d1405c003800d01c40e810b0301000803940c943c200542440407a0300c0c5660080d400014450401d42c1c10b500240c419000b40c0c94452502485c0d0318210700720300907804452403091391000420050301c3c00e81 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 158114775 1250 158113525 158113541
    0x60702040e0607030e07050409080307051c061d06040c0c0314040503120406030b0118030f020109030525080313180b150301051e100806010203090a1d0106170a 70
    0x2800208550300e50711a194609041100c03c400003954a200300c0c180c000341072050300001e02c0202c3d0140120605038440303506038803001d00100f0900a0018a803054014101c496035100910f248007040113996030b500c64000c16080a0854145981c034000150301d91070544202520043c1698518a0030000ca07901540d516101449071348000d03a081c00000369603501009048030501002c00c8403506d8a18110025003a2400c5c031901d1410310030100d10f90040503034404a4107003100c0e0840c00d08800d41d4100c3c00140c0d980859504050881e0042c61f50b0240070501d0407941d080000326600030703003905607502e58a16440340941032103450780c440c1c00341007040075859505031440403a0140d50300140c024078500c001083c0042462032268200c0700480100252700e0004984600800002031034441340c480000010704404011901d001400b0201003c288035034800c01c29a114040040c00304584603444560b0b1621110600380c0e18002c0101080002c200746105041c14501e0003101100034400780c54881845028201e92 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 158116025 1250 158114775 158114779
    0xf06020d030b13090c030b100b03070c08040e0c190e010507030806042406020c0301051006120f05100305060a0207020a12150203040b01090f11040510030b0a030302010b011b02010e060702 82
    0x49180c5801250991050b007010328030582482d01d859155183c47c9612100090442e141c0c0c0802038400c00501c0904c1d0122940020545000046445c032032402d140c00707003e55006001c40179101070420541110000081c018060b8100f110b103214100003001312040030042020230b001031014800100024010014160842c81c001e01c0801c02140005000043c1c071181040e292810f07140041c01c002ca140c050142c034003204010f400074402890301080c1405c0005483c8200d5003001404801e41c4004165a44000a1140d80d20303c24003407030401440189603600d050205807858041e51010421a0391144205c0c0c20841d4013500c54582c240c502080031001468011050b11001c40a4103402821030440c4011481a48280c01403101541000e41010840705501c000003c2180742a01001088044c00f050303030304032081214018612003912004030b02070081480c0070f03030701700310348071808410160190401101008203a0f2940790307040d6040404d02e01d541e044940640882d002101404d041d0800340010440c007400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 158117275 1250 158116025 158116039
    0x109030311013b121605010b030d0201140106020d05070f11030706180816150c08030a02072312030a11040e0603061e0a02030703110d09020a08030703051903090c0815010f06020d030b 80
    0x41c0c41c009c41d090840303030078004d40181d65640d0780d14a0402880d80b01d9026004504c014044400c8400303014000c1d12070068040c0101d1000d1004400301306001d42c41c2401c2c2040901625030182e40c40601420403560005841943c0d0801c0502169501d00000c0340f01c000e01d4091403050f10b840c80c10680e0000e21440900140400003031800e460f02041c0c08400560040490700d00c016a1030281d81004882540b4496050610780c44202d540c000c0c9413000100d42007807680ea10b8600742e0383e85424040350f00510f5445040e250b0054080380008500c1c0c5e00301e625034442c01096080d0f1310580c2c0c4840c220110620504100e0a0481c2c14001045100c400d940c051584820107003000510701c480003200f540d40d60808400640d566807148660f00850a20301e24660041140000450400015550142c01c60081000449402e1910003424140c14826042070000c1a08a58042002901d40c07503a0390311740f20000300f01200000c6079000000c0c10840c684584040358802c0d40038002d0010050401c0340035060b170100c4a0750001da = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 158118525 1250 158117275 158117291
    0xa0302060703051c0b130c03150b0309010f110a0804080d1b230901031e05010e18030901050f09010c151d0c0109030311013b12160501 59
    0x2602002014014000c1e11210f440c2c000308100d200b000ca00c0310102201d138034140280f02c5401d0b2034960004041543c002e40218864196803000c0380103102d140d5025107040315001001800c8100200114000d00021009200400c8800e030b43e4000d803889003503181e10203a02041300c2e1f011f00344030302486500b0030302c6640c503640b40104a48a400c10b4402e550190301a58111808101510303811000b0403010140200001180701c0c1d20800c1c5410602540c0c010b1814591140c030440303008600001240241010104100aa075844100000b040300341164032500182a001d91000340f88070000944443d540e0596500346401c00d20700c0750b50f4003a004407241c14180035a440303409002580460b43d6504048c0d1080e800514540b20b400c0c1182111110202c01c2c515402c82c50f400005640c1c44810ba8054030f425040445107040401101801480c4910000755400702c003c54040501900342d00b201c840320707841c9030848066440c07005965124490840051401d240c2004403403080d000b40c0043c284011300820002070780d10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 158119775 1250 158118525 158118529
    0x90a02090402191704110409080c16331b140c010306050103020c07170f16050111010515120102070f06020405042f0f07050115050103060b09010203030112020a0302 72
    0x2811400504001290580c0c0c03030340744182e0104c2180c50500c00e070440365425040549554a51800c207905160065440309103174018000224100e80d030f401245401c40d00c14035528041c0040344100c5004101142d203809640c0300414200591030390040310190070b06c100303c0701502402d481003600b2104d8001da0009440003580414078801c3e80d03085800e8140b014043c0d074000040014110b130800e4002c0e906040c414403a0b1110503100082d000203441404810303c3c402c0f903415209900d403c4d0041920080ca1141c2800c82c624044052a0383e400c82c1c03802c0c0c82d100303610a5580301d014242c410445503000070185540b4240340c64581094000103031014080018a0280240c5a1444091094a05840c62600001c04008a050a00c2000542600002c2900011411f990304020182c400140c00306200c2000c03d0b80940090f80b401190701e070540c84002008250325491001912141c02e20509002c03a03d800700000d000e0301c02c8404c541080d00c05034051850350707080110030300c04010003102c284e82042101d44003000503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 158121025 1250 158119775 158119777
    0x40816060905031c0e030c03040504050703090b010311042d09020a0f0801050105031c051e0d060303030911010305090a0803100e0f040512090a090b030a05100f0515010e090a02090402 80
    0x2440d4885011030a0316544c114003000e85078400280342850340100315850020201109640c01d0341c008441c003103105c1d00d0361a400c402030403525038090f0107208a2000001000040075100401070070958080c01640030024542c0f030742039000c0302140143d510350401401c40c19156400300c080c0c2c610041041d080c49071a031113003464108840c0c0001b41c19a56038001400740d490104410084c1402310840e2503050000c816008005004599032004c1401030706500002c030103101c40c296117176103d0090082000595904005025103040c50040d03031240300b14100c1580c207503c40e00805201d003c8d46070003400c0c00003440d0b503121613942c0000d158242d031056840011864042800b26540210422102a0300384e0400e400c015040012440d55508102c000b0002ca0f901c0da103d14404804580040500086032900003000c01d080000030315004143c1c5c000c0300305e0075030203600b40c1e4081c40241c85011020802943d80c0d05161a01480d11000c46020038422a51003a640c649501a546c0c088140040503052260b0140440c040e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 158122275 1250 158121025 158121037
    0x20c1509070806011202060703080a0b0d060209010810030521070501021201080d1106010b03090f0f25050609040b031924020a091404091707050601050904081606090503 74
    0x496000020100482e10007080f01074094040c5a00382c0c800c000e002e0340003460610514400405101c05403000400512480e88940c02c00e83c005004000b414600345040c0e0f000b9404070050386d002c1740c04000850f207568a074481220a40340d204005042c0c28000745950b050001e0340700e40c280111a0200039100011750213001800d9000032281c29000d0550410310342c107080c47c08100c3e848040150004001842d01c000143c25030444405000495607038032494100c500705aa00000d600181c8221314442d8181040010010403403004862148807a81845600c401205594070400743c3c002014040f810b1946003c1d40044208500101210210000d402c004c040b4803600d21019501141c0795000c10004503020070400682d2110b81c6c80442c9031140c0494080e000d00018000c3c560070710040d000c0400182c403641d00503040d141c1c001010721104050440c2c440c0182d40161800c07203a40c0160b6000003105d080401d011030260358003541e01410503400c0c1e04a01124071798003500f03032505512a0b0702d200c08981300b8401070403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 158123525 1250 158122275 158122291
    0x100302012111040801062c070e0d050f0c0402070f060203060d0507121101170f040501060b13050a050613061b0c0e04020a060906020717100c020a06050c120a020c15 72
    0x3031151314020b0080d00f10f0b1030300d03448422040c080f014803802c1048025990940b018040c81401c00303c0d00c0340c0000700c1312640b0000415400a00007035110092000010380368501c41e075240126540e180c00402444281c5c0181640104181a45500d4600042c0e140c0c01659104901521160b024070301500c9a03480c200480c0d0000c100072039840c0b8500e050242a04140e080c0d58800e003003c500a5070354100703070008884020805200940040080f400f04202904000000c004d050000c40e15004002d40e2001c1758030042c03007503600c903643c421800240303400c0070016548030f640740900d041d003010300e4598161500581d003540102d5490362401c1c4500002c48969069024003a48814900d036460141b052240c11203940d0441400d12020350780400c00503500007107100549840145014078503501c8200f89250081c9040d125904030708040c81d0b103440369400950000040d0140ca014406921203121003d03551183c0040b07100750b211003000103801802941c000b003084a8041041f580c0500e140c0c0070010107080b095034041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 158124775 1250 158123525 158123527
    0xa15030c0801050a090f0e0d030c02070e0103080306120304090507050405131b0c0c03050a050619020f07060b0f030105010608010503101b080601091a030109060806100302012111 78
    0x155a915100d09586400e0a04040c0c1d45541420700161074000ca522845440c51b440e1500e50700104015003140d864440d9107011038102c00b15817513014010b050403000020041c80b5070540042d1001041034054122a08200f45034516110b00050007440001d0642c0c1a50a20040000007841d44803482000d1052825176603450300c079410102000b00020f8507200b1020030300d05003803080303064481c1e5188804244559042401c0042090300c2c0900007034160740c0c0042c1080c05009201c20900c10301146003880751032030040300000d60001e081d1400481c00b41094960f9000e00a109000c0020301c0d507400f00401c500014248125003460200088c01c0d03076000d80000000a40310b000400581c2000c04c01c00401c20340c00c18041c0701022518590070381e00c100968000013007142c0f90300451116402003200a01920200c0a0f10b6000003d000283d2002d43c070030f00c282d5640f1881c0040c0001e03580804500c49004a8801051440607031554004655031004d15001c1c0324260480110004094264842c0e0f1a080640807999 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 158126025 1250 158124775 158124809
    0x1303060b04051f0504180803090303061207062a1e0201030608010204060c06090816140d0807120905030412050a06061a0d0c12020d091101020c030d1202090a 69
    0x1110503102c0c003901c68061564070307244842d20391000c0c2a002c1c040c0c5006031400a0241402955000300d060440d9021b0110030b0000140104030070007000841c880c3c0303800d9030755181c7c0545030700354690b070f824482c031039600010310b440d20120109a01c611103010300c800c80d01415490340d01e1a01c84035040c2e003004200d8181005d18060003011540c050140300e0003050329200841c01d040ca015005892410b4083c0000d00f21580c903001c04003000600800e440c020555010820007080b5285480c1050003007150f8941818410110200070080c41403000503c03035162940c4100004208000f82405402d02c98821074541c01b0510010a840381c00300540302c4500c1c00b4a00401d80c40b80141407a408407120750700001564060200300716001070880c4d080714905880020700044428655400700c418019640400c1001c40c0000b84504c2e8a0a4a8105c0c80801c2c0c022000005026031050040e82c1c0c9040c000b02035a0581c2080c68040000c6000d200d9100c2d0100301c00c04054540030205001a40d20340c103c0e00480c040071a11448 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 158127275 1250 158126025 158126029
    0x901031103091b091006140c0102030403050304060608070b04090b01120e100522031107030c03060204180c1b0c030803070c1401020a0914010527030d02011e0b061303060b 75
    0x3d54600210030746a06076181801e07a0702c614050058042c0c14140003480b41c1060074400340e0022142d1507240c0c10021900c0e0f0803c0e1900409952081d54141d0740641040c501192000012940004465181e07503c2442c003460310110202901c2c40b40365403410b001e5490402d1829101d0f9000301203643d5044405030042d030064862200c12110050300540d56030180007510010f00c40784900c20f005c42c98250401165002c054071342c1615045d1a40c0001313111191045000003004038940151050318440251542e040550400800442e002e460300b40e0b000030311074010080005084940c200d882400741a2106015480b81c030354240c035074000d1f19114005407075000c3c07000901083d08010204a05040025494032425036401441040707180500b14906640e0540764400368041d004485d071a080c1022030000c0b103000941940c0141001e035031028040d000d10445140d6070352041c0b04d0041c003c0d0600711150410070b140c0031410000c09618074425041001017107010f103a0030040c4d0b120001144140801300d80c189103402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 158128525 1250 158127275 158127313
    0x15010f030603050d05090310060603020a030f090c05131112041b0308040b0a05090d030e042f0a0c02060c0706030b120a03110102040f0e010306151a090103110309 71
    0x12840205441c210041c40020b10101305541190781600d0000e84a400c0d000000781403980c04070391400a240780c0040010001c1e0590003400d051122601c0401c03240210328412801d0303c4e80c102c0010581001540140001e1821030a00b0020000028002440c0070107101c40c1c010079401a0445419103003008100030030082c080c4250f002c101c41c86086c59914034a16134407500305000d11f0084030003c1c840880e010508a10130383c03d03154003075001440000350780400e00340079021240c29461103004905201c0c070400c00e5103070341c5200030a1159005800f140d00d5030b411104902c6420409010003007025107811040565600000741180f000c804015040d40c5140840c081c088411400c105402060301440c0100710410101d0305118040d01801c103c100c0040c0d03161500d00900c2950441c6c1c444031180d2001083c44410000000d0689209003410003a0a07080c800e02100308072a8420f0300f20f410311200c0280f20200e44600980268941070401080500340002c00c00c200d070300115020401d40d44080b00c40c03016420300030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 158129775 1250 158128525 158128547
    0xe0106031407060503070804051507080402151602041a030114010e0f07050a080a060b0301150206090a0827090a0515010c0b1f05030610060908030903060601081e1501 73
    0x21000b080603510b4500090241e02000f001c400522846030300180c03d110091144444054020341916010f2030a208003a19041c002d54061f030003000c00a5202e42c0c3d124517582140c203095244c0d0f0010584900960812028125210a0310740c00441a00b500d5003a85003400307400e14800051021070101c0d03042600c01028500010020f021110305841440500780d009030880b20102e11a01d4404001d903104e9008402609580d4442b00b0696000000090142425030f40300c0828100c0b0390903241541c91300c0c184980e5a1128401c0074019040c10403003244203584400311000740560810300d52802162420015421074030484071102002d07122010032032484c0c15038803c3c04650000742802d81016401d40c0b10220500d60092034400d0300d07009000040200b0b10846001c80081100070112807042c5001c24a4604000d12442014007003042c522001c11050000320035076400180280c000c04659881d4001181d0031000681042811801180c01401c1c030070648080d107100d82024403201502d60304010005020308890 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 158131025 1250 158129775 158129813
    0xf0609080d0810050f030102090a0303050a0f0e0a060302220b1b061e060102031e0405030c100c2301140601020c0616020f060f04060f020616050a080a020408010e010603 74
    0x100308004000460202c0c0c10700341d500079103085c100801c000004c80e00902c11180c500d40c0c44240642c0020405600ca0020000201d01d9510407610024070801901c025070400c00c10759121f00d45610a0140d00c2c482d0380503040e8101e810b503842151144241d1000c074400080d4200c10956800005d02c9a04154403244810540045000806003850102140408000c510010540000715000818041e80c800c009841e4810181280e410313445210b1007140d07145030310074490340d0300a0158a202034440d1500b480e82c40c0c0c449009440e00c03402c55000350b50341c03200b4410124025103a8400521580e071201800d20682504020b010780c10b41d210b0400e240064600a82c54800c07038418582003082ca0307080302c44004210400e550640d0320540703107034170f18000501c98000c9101c2e000d04007401250005040b86c0c88800c40c150050365809440c92074a80314042e01004c1c54101c0c4040210350108401ca0701541324509443c1c1c0400e5035100103003800e480f00c2d2404e09554410076807200796910340e80107005101a03281c42c1c1440c4005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 158132275 1250 158131025 158131037
    0x40507050a05031f0503010f0203010e090604080d0b04150603050a0e010c0c0605061c1a070e090403110a020901171605100f03060803131503200a0203040f0609080d 72
    0x10781401015403100900600149411500750482c03598a00141009420018020b100c0444405c442d03c0094000340700e80d1818280180200d94a42c034003180d07140c0142d4100c2092407401c4a048100c4000d0642c3c8150142c1095507045482400310a1224150103440c2c039603030100b000c2c10611005e6003652a0b4203481c03030303040c3d00d854810402c250300310451330380709603000c180481c07103684250000d150814a08440204400c55540f89020050544006d0b1204400c0ba1509600e640703850104403010410004419000750701c01c1c002c2804a8041e507003034080031441004031580c541866022681c3c0345030a80c0442c400901410004009800900c04100d01010007421070403071628040015040c940040040014004d0101c3e1451100f44607420060190400d0000c40340d80b08c094100552280320584500015034003120310742581144240103820307003070a84650200340070f42e0100c13584215912403403459080d44020400000e0118919403810018007060b2101c060700703032900c00c01504186941d03a1703107010015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 158133525 1250 158132275 158132287
    0x9060c02160524191106010909080d050c0c160503120309030d050601021903080604060b070506190b1c110901030b01090908040302041b0e0f0108130318080c04050705 73
    0xb10748003428a8090b510418003094a009199014584200015241101d070b00107402c4503840d40000028100c104400100c1340701d80c0c1c8c2d5201d5501100c588000c01030200608100221003684982c00c42038001034070b01f604501d04006140d070149040c050207604800c0c140101c6080085180521482c0c4203e9504000c2915600c0c11403802c83d1203101c1c608109100c9075403032000ca03c05034402c000c01880c44803480b100c0b001d12861070402505030481150b00318411410110007280e803001c440241c0d01810f500030018400380e03c03810080c41003040c0403c2d803050703000c3d45d80800c80310956403d4039441204d2a200c0b4042c4038034285091150070380d144031f2602405070801400420004814003203642c11180300800000f6481c40500c0c01465900c500c2e807001e588541003a2900c1c009400307140c079524072034000d61910482c064010b020301450840c01e80320240420b103494000341d00214204041c60440c1d1291400003c05a0300c4003000b201a031840c2c02042c0150b00510b00120300303040501c2190380005183c145a41004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 158134775 1250 158133525 158133529
    0x1090902010804080c010b06030703090b01210b04050c0d080714062202180a0e010608010b150708040f0b04090e0a0b0c0a0c060e0f0c191a070609060c021605 69
    0x180c2c1c040c0c8018009080002d1801c8088420f600c0500e925000602903540ca041c804c0004000e005089010340b854041e0500020f40d01d000440074510401601c80310566001d2151175584078140001c100b41c500d030007a10b0f548a603e54401c411030011510949030160ac0700400e040c0a602c4020fa107148180d40e030321040510042140810b4484944047c81c5042420403d1074404a8518000408070011020340102841400031f0315811001c2405201ca0080101660b80c1d1541400d0300c1740c41201c0fa4000318000c01c0417150002c490300501c44107005040152500d07030381d00c2c3c80000300c1c4402d03032011020460200302404003030114010f00b20b6511245004250b03d000707586036000e28440240a41d034115000190140405002d40d03101c0c00e240381c0000080007021401c803281901c4c0c4825140800340340c0611000f507082883e2940d078000400940c040407074000d5041122100321034292030041c81201070103002d0a0b00144450050107005071050a004c9803408070040040d14004002c0314400c18004425818013140e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 158136025 1250 158134775 158134787
    0x1e01021305100302043f020603190605060d02070b130c060f020f0d0207170303090d0e010c1202010f0b1804171201080a02030d05120a0207141e060109090201 69
    0x511011a90351140406140081c0d00910961b84030625610459500941c604425403860f44000040f03c1020342c040d04450fa005444101d94070000d5100000b44003040b0404100490540319903105100003442d40c0c0c5460006580380c000b8030528465640000f038010401c008001c1541e0003400300751130050380d103046985090036840c0c0c41c007030708080010305420040014820080841d40005060640307034020603d180003510389245008030b4840032031410751402c50010010031203106005100251054103610b1408845c0c840360190b02504103c0104290310104803210480101100d00350000161580c1200c08601503a000000c043d1103803900141d06410340e0709500d52141d00952003107403c087c401220b55031250500031201c120000d01903a0340040307038071600000e4844199000700d00311400080a210b0840c0c60380b00d14003400301c03800c2104c0041212440c0e1900030f840440e100e03808101000400100540c07a001010320001d0030101503440348003008006101c1e0310301600009030140100c610b030f43c00103450 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 158137275 1250 158136025 158136029
    0x3030e01080709060e041103090a170901090306110c07060203030708060d020d0b180a0506090c040b0d033507090801180b100504020304080a09050328060f0203091e010213 75
    0xb4417030201c006081c0c0e40d56642c081d1100203441100355440741081e00840b40c1ea1441a801125100d8281580445945c1f485098035100441695411b0318030781543e90b00405041c2210344887c80c0b002c01d104070303400c003041030000c40d0103040140d000710745a01c2c0000000b4100d640c081e102d41e004081c2c1c8000c550160b1900d04040480300d8100c034940a06494146280c000010899078036032003801407159910401c10049015401910038a044070b50b03d0b22150200030407580f0040c1401da1010f5848070440000740540b1103049400c0010703140034100e540104541c08902003020891144c10340c0780c410492002d03004541d40d8050401e1a000300035400d2004140c00c1c1c1171083c41c6000d405140b24500280201d103a01c200310000d80b9004d842503440e400c140c03034564195000403868102254400102140130300b40020b10340c600540b03021602c00e46001e030b822040410310301e40609a59494803454820222551800114012140a8001d1503000030700700d80580d00754580c12502c9196401002108040c0c0b0050b070350042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 158138525 1250 158137275 158137277
    0xf0106080411010c050706031a06090916140a0e0306090d0221090307060512010e0907050135100b120604021605010c0c06050610080a052701020403030e0108070906 72
    0x103141070b002c030043e0703058250410300a0a52040420111300b05070315402a12180c00d02c0600d0f403848641760380411145001c0d04281d243c010a282d80000c0303400b600b00c668040300b20034509282c02c04400a0104c1c0d1100d60200400d640482c84648200710795060400c245035103c0c4140025110200512000948855203441e80301c8020032480b039040b203103c001c10203c40352048010100d41c2c07220340e40d440c00303401038200708905041d0441c071b1000020700400c119400341c810030713404000d042c0c3e0030b007840c3c0152044414070052554200841610440207019540d06c1c040d400f0fa01d0101413443d00e403003d41001c00c1800c86d002280b02400910021141c041e1000340307550891400c07103015880e981c44118440051108100142c140c0d030811003a40404e43d0400c200302c202602a5101f407080d9034410060224501142c0d0749000041c8041000070740a40b86540150307044424440c10518501048815811103100e03014140c6569600040400c10035401c042c0c032007001c92003070034841c0e00e500c3c1c0780c04040c0c00d0200510802c3c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 158139775 1250 158138525 158138543
    0xf1203090b151c05070602011d030301051005041707052115040317100f0f03050d0c050f0114090c03010e031605010b0d05010c020706090f030602131a0d050f01060804 73
    0x2960039a148000116400441d02c0249007072030084c20410380c1c0c0d0105115079000340d480d007440c501441c4443e50300a0b020750722080045203543d1902042c001601000121203040120900000c1001d500521402c1d440000c1500103100090516041000d800b03642942c0003a01c414002c203061140c0c0020507010028082d002448810390780b40c0c00c0540b182c0000d105000301548142c4200215000c1840452080d039044041001c0310745d4884400180d001340e580805890369200075000780b03826202e4242e2000c8288948180c4460110400c0396900f503508980700a061404128100404400c0800c042448035104800a10100c035902a44a03160321407042ca401034004407407805024803609400075109224003503c1e00521001c01e00380b50340200b00e05a040d50041c010307400e00081c1ca52040300c3c130800341d60364102030b0035503d8510782e10a00298409000162181000391000502e80004040302d00e0251203568030725900c00000c0c00c03044c02c0b0b500060814640a94110040c040e080c3d0240140754000d500c18505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 158141025 1250 158139775 158139811
    0x609180e0309030105101703123601090201030f020405060a110f0d0c05150f0601030f0603080301030c0503150717061807120f050c07110d060203040f1203090b 70
    0x307030440c401c80340c01a8166003850103101000791072041100403100841c1c07202c0800c03801e101401751648a8440040303501002a000f1800791100c800ca0700c203a052154105c80354000c0304000c0300310700d462011210221a55146601c00c2596010300403480c402c00301600031481e040c105000030b4464080e90100104002c0078407092451000108400038104103c0030484a000200e414001c1520141c2001114580111019048511030300408a4000d8420071501c805035505c060044006144480d000c1c42c0c01629644000041070503e001940139500400d118103480b070410040c5498401144812203c294a980c108001c003035002a007024806160035402032a40c982400240340b1071404038201042c6142003051101841c1c11590712507040018040521900e07a01c02149000c9402c2222001000c480c200080000180b980b0b6182c01002402009a10708a2640d114081260030440382180d4114900c41d00009200101d01c5003240b070000c500c1c0500c195040c50f5601030500d140a06030490440700c034000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 158142275 1250 158141025 158141051
    0x40b03131b0b19080601140d060b040e0105100f080402040908120a140601020708150711100e15040f060e100207050106030c0b130b0d09080406031401060918 69
    0x8408001e021110028040c41d03194054a445540615245541c5400043ca4101c01d01d0107446480e100d400c050711240307613003c04d0b940c410055070b1088101800807980d8680c0800e200ca0080060009010f4a01541c030296061205100ca580036000c0c40301c0c14080000340030700049034048185e070ba0150b03040d1800310302c20940340f900b02c6250150892034099840c0c00b9040180110159104a12140303400c90386072081d45941c0016038842c9051f02406000350170400081d00442041ca860b19040a0140b504048444e0800e50035410489111180c1080070f440e9510454a850104002d1000c1080040c0706186030410350f1701c540036440a11801840d41c0c3d241d41043c070b10004140072050951800c107a09650b01d0075989807480c0204000e020803a08014080d0000c0b03800380810040d82e20203140703c08450550390404520840d41e80021144050345074035840301d0070009880c00060b0000380005c3e10049504098201c5207002481c05070001030030000b0b00d076001c120200f20000192020200000300045001d481c0740 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 158143525 1250 158142275 158142293
    0x1150807241806030b040b121b0a0302150304030201060915060c03020a05011e0510030503030f040c1d0117010c140a0201111308120c030d0b011b060501090e03040b0313 74
    0x8a04032900c510784500060440d09170700310803000802100d08001022074041040090580551110016030080482d542c09000c080840402d1100003001440615940c0d4000358610564075000642403801006000425409000300720181c04100d10030b118803042c04000c94000b020602c14241040400c184050030306000b801246d44041c0c100009101183c0001c4084c801d8004d001c5094000340c0c90302000943e8a100700c83c0c148141e0354040007441c91922214460000f50700c0c042c1c010364401c0f80c40e80d800551964110f0f00560040007000d2240d10945c500000b81c0c20081107807000e82080d0341032100a900c0c241e032103541c40110a4001007007548403100001c040b401050011020030303200310001076010102980c6600ea1080301c200400701c9000050010114909010741295241d96900c14002d0149204041c0c0080d41d1801040c0340050404007032041c1c5e00711000d0607000540720b150745d400050040d800a801140000c03220032004510b01403501c005d5035094400180446101ca1100107101c0400200034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 158144775 1250 158143525 158143547
    0x1c021005160c06110f01020f04090509100c02060a0f050f06060c01020f212212140706050105091005030a060216020d0606181802090c1b0115080724 65
    0x612401c0440f5260780300075000039081503001e0712500c030b200c0c2c04001200050084411120200d00d100b42054581038402c07014050280140c0c203039004070b850881140440e803007941031b041c1c115030060078581020b104102c00c5071210b40001c03041034203200c1040019014150550303003148048d6030785503031030808050303860082c0640902c20160100c001107400480341701445405684418806411140c6c4941004542030407508102c41c034210b0401191001040316104060551220b50038908810b2501b161003c24030360001204880c1030b075423580140a1070030b04280c07584d4014402c070654681d80d0300f0000000c0c0d440004520041c007082e00024460560301200b600c4280241d070151081d20803147d6440d0030001b4203507038080c4806108898090f2a014980740c002c00c03468980d00f200d0440e110400d034080c0000e821005040342c20b21941040842505d55201040e5505252003000006001c12811050140b81c07400d40d01101c802e5000030350038000300e2441310b88003034140a403a02c102030303000341c014040d90611800c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 158146025 1250 158144775 158144783
    0x2060c0d0203030103120822020102010605040204031506151d0301230f0919020105031003020a0f05030613032705130b040b0111060703111b0307021c02100516 70
    0x114000140580c0000c069030603684146c00b0f42070b03e020a810111038018007111070854580c000c24400c0c6540d03012300c8580e41101e0040c80003081c0703142c032140410140c1c0d2042d44100d4554a08060000500005104c1c0c1d030040c2c40c0500d08880811141c00008190044020381e2107151003002d01d0180d980e42c7c00750301542d17800300e06012640c0c1b0b00200b5030074042514812103c9440c1194038070001070460b680403503000c1008220f10381c0402498a10b400449840c0c100030300070351038158058400b00241e942c003446d180040c80310100e041078060400c0107140c10600c000e0101407440c4000d20207000083d4101100d15001000015000d100324051402c10200d03481a60000741c2041c56546210506e036599003040d44c603454103032010300413044040011518600814120304682c0c00c007401064800c0d1094000011300083d1056640c204094400141040c0c4d03103080010320030303038030005000003182031042c4038000bd88600c52030f5081c460003075004030390400c420f5a00070041140002c0e150b99903115000d41d400d080c5400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 158147275 1250 158146025 158146033
    0x30106030b0708090706090b03010b0a111b0a0b040e040204090f060903260f0f0703090204150305060105061908070c06050907030c08030a1409040e03030f010e15091302060c 76
    0x5020003030581001904d61138103c1c003414502081c0140079804020481c1c2c1800ea0346031640c0c1c40d00954100a40120b0854410081c40c1c44c400a0b51710000c001180d8164402181403002224000030424032076002c2e48075041e102c00034030003003014118160801c0c0e4011b4040d00c01064441c6030303244c0700c4280646408004d15851070100d941044c140e1001c266040f108603060000894415114400f10300d010071138500716403084444c00265045e848010305900a40c1e81d04000c01c2e00000c1d54001400d41c7c0c400300700c0200400070301c60b013001030240030000b950050170180c5000d86490904000341d80d09441c254101002d000310707074001c500524499803925205903007200c41000241401d01003162501c10a04c000d60b94081050360203d04208080304451030195580c84100d210300305814034800d55008181304941c01552100c0701d0382c2c86401440114412221542410341c1503040ca02840e1084801904030400060f0082e4440602e4445d1507001e90410440d44440c16610702510014030144a028500116805 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 158148525 1250 158147275 158147281
    0x1080709050d0f050a020918190f030c03200610060903030f0f020c0d05030702120609070306050615030117010c26130c060512090a020a06080a06081209030d08090c040209030106030b 80
    0x1001000c1d01c60708d039020b441581d500700082203c0c1901e040130302038050400d1025101c050002402070310582401442410442000300c0e096124000e20b44050b07115000c0c40c0c0120b02000440300c1d014500401904040c1482091036055440040060402151279018442401c49840c02e042c000c10100e666100c00604c0851482038900e009512600580d400b00d0080780b00b1401510301100200745207114014040040c500c0b2403840e215000a408050181500b1980f48850030499001c4070b00107502801c0020346080c442c0450703900030740c2184d880f1801e000401003e4540361600c8401c61070220200d240c0c0180050440d203a00c030900d030030900701e0b1800600050710900300040c00e0703822001820b075050191000d0905607403076110f1507490340482d4600135400f81845d00180000ca0080c0d01490300200111400220151a9084a0326240c3d1381e4680f10001e00002c80c3c024000e180030421078846c05210301c0c182e01c5070304008007142d507a0000507607503d00c120340100f80d8007100c2e103003507014900440d040328806030300381 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 158149775 1250 158148525 158148541
    0x30403231006031e03050d0b12060403020a141c030b040f06080106140901080a0807140708070e0105191401110102041206060f080705271501080709050d0f050a0209 72
    0x8491100b03c80800c0016441c8001102e4050314400051705500e03a645416030749443e0700c0c0140982040c1e030350310103244144101d04400421203244541d1298000b016002446c0c00c3c06203480303002c0c22030305259a01c0b04c1c030040c0007a40126180c40d480b130128100454151a6100010007a0901d030b408a0322652030303d40002070701d0f10150014000c880000d01c005248203542c0d001d03c001d4480c00d000c6c942455100100000018084d00000d0110394064445510f404d0702150b100350500e0450780c00141c80b0f41c06040240001003842c10100d00505084519001d1000d0000d8030700c2001450788a005240000d601e88503600340d01440300341c0400402c0e1002190344a451380b503151420107801200f80c40c06450801d0108a001c1c11580d558191690301001b01401c9141c00d082029462101e44803040141110070070804642448000c40d001e80a00003a85c1c0c4d81070500380005000d48001480b4104100460b13508001c40c1c0c441101104400d60072441140500031107040c403900e0447d50380d00094020301d08408100d020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 158151025 1250 158149775 158149781
    0x9030f0f06051515070309030c03080d061d0f091606080f070219080a05040f090e0c030c100c170a08070f080402011202090f0a09020a200304032310 65
    0x748100000c00643d19140080300c60303044143e202c9608a0000340c90000400040c0000d03101e001e1107481e054a55035165a503410300c16120764000c4601900108000c1c0b0405194041d50018060000041c00002c4046c1f030b041e4111403001d01410b882d0596000856560182071100982201604403544a0550384550080605d034080711b0b03046209005101140315544089041d8804066506824908403000d482d004865880000c000b4240030040000140028003010a03100074a0002c0d400240440c20080503818101c2422a02d4440e411800701c180b503658510f94012065040d925000c0c01c009498070f4070a03c030385144a0700100010010805506c41948548114410169541c501c030420048440a4030100000d0344c4c0280401c01d48003c81c45a0340700c0f540503003201e01004001d202c0d90030f144c0022800c500340e035800146c5010f8001031400d400c61b0700a6042401980b02c0d60550341080000813000c2e4482c0a907001c0284030204d4211045003410003211809052501070055503d0302e52403080e80001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 158152275 1250 158151025 158151053
    0x109170c0406050306090a080f0d110301050319020a1a0d020d0506031002040b160516080d030b27040f20130b150a091206050402191202010e0109030f 66
    0x401d0b030030041c0109081c1408280540900ca040009040e0806103545011300c54100900e0040c5800c07041c01098000b03540f40c050360002050f5850025079a5041009041c1400b0050740c080002001400d48107005884c2c1c0d80e0f182085400348605000304c4042511070740050301c203884281d000e250020504644107200d03503000c14000c50085088480110302041d950040c1e0080d44102003401e42c1c24030280c900080c04507450034118ac8144d0640c0c001440e0622030b1141c401d02600004a2a40003401400301140c06114100e11400b08440300074000c1804036095444210a080805030301601c4808201005080202d00c0b008591007a440545c821407681e40040c0304001050592142500b04440d01c0c0c06a468400d400700d100300903008075000c01030303442c01d0075031a0f11202040d410031140350000249e01620407101d101e91031041c0c034085410b040c5030041004541400d00c0a2120164500042040700e6649049180720756080c00d00c800b1a803a05801aa000d1150351b002a180d0307520044054104407002d154410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 158153525 1250 158152275 158152279
    0x30a0609052508070816050405060a2703080405130b10050d1103040f020d05100e07150f08012d06210b030a06020310240e03061b03060109170c 63
    0x41034007480100c450400030765041300820500400700d00c0b00440303040c2501c00194a4200301d031509907204041655940310301260b00c0080c1d06066981c90310603800c0001603407003116280c0b0401e200d05503154540300f4462403062620580c0c0c2085510386074041600603d103600e1008005081110f81c508028290313034400125034031114500803101c940070610790156405a9001759031400d1007070640c0e084c8203c0c81041d030404c3e51648180c43c1c0041941040703020300d41c000d4155074060304005281400a6150381c142142d43c0c03051003822104125a2503100c0d6405045900206510500c2c16803032081120304104464080c2d1b82d00140700000c01d0182e0440d080b401903e051044038810b058400c7c524038201c1d90340c540941d6160f04085201d601181340c41d00596003103d0300482214400b581c801c098483c0c0750f0300320b124008001d603103210f07a8100341d00088900c100000c103402900051a1903075159540c0311920000400d111004808038076680d10518486002e84403642c10885910904051955100c0c18200107074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 158154775 1250 158153525 158153581
    0x230d05010c110d1e110c0303040f031a041a15030106090c1209020a0b0a02010e010e0d09061d041e0504110301060b07020f040e0f03041e060221030a060905 68
    0x495803140c0000075240b11301d20309803c0002d407400d808441200158403285028171848020801c00c4d5014001000101480032070301440e58035501d40010700100c1101e940f00351035504802c002c0403504510b50608407600c40d00c80d5911179a1211807852504021600c419019860031101250704400303030740001d50641c1c0395110640040b100c500b4401c10368441e808001d400000307080003000b664080d0805808165458000420681c40d00103040c2e0854942a50020b00c0d9884240e20101158020100001410315131170840c00f034044408041880004101c0b6042c0620b680d030055061840120000000d01241003005120320f06203410130000d00f00d00e40c2003080c801c0d480c080c1c0018501d200391048511a0368050321006146e400701c0c041100a1680c4500d04203640540d1289a0700b040041c03000300098104444030225141200e0a512503a000c1d030341160083d544a502107520003003044000ca54440090084141d07030369502c0240c0400380c1259030100c1c0841d424181804904080e00020b0010030002c2e415034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 158156025 1250 158154775 158154793
    0x71704051c02032109030303310308190207060e0f010b0f0a1e080a050a1b2d1a041802030105060f07020a0312020f010b0a230d05010c11 60
    0x18807010118044003d500d5444807007000501d48036100000450842820300318246190580401e007140e00480d02c1c41b081440e445941e4501c0800e00da03907503503105601841340b03540c0003480d0303030103080c004d0f0280003520100c0d0080c0a403680d000071303501100c0403258031550a0203015590072070255110041e404030100365091290403566810640321000ca4204d004080000c164a00070f40314494400c0fa841d000c00c0342402d07020206083d8010031807503e4161080004000403119070924124007070320900052000d40d11100104000003034030345450503141050306582824407509070188050145c13540305640c000d401700382e03884584001602078003c07140050a200c0002207001d070700c40d080b44401d010340c590009041c40707880400040b0002078507800e8400351044040c152217403039111500c21110020001a8421041010a80001e003c2c2072442c5000f614444145402c04001c0103002d00d40c03055840341d00080c0303800c00d4074075a943d0000000352604980200040800200e004201554001170b40d03c09110345168 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 158157275 1250 158156025 158156059
    0x90111120f01092d0608010203010b13240f020a0506011e08011401150507080304080c151b09010c02210607021c12090c15030606030522050307170405 66
    0x9580044803007900c440d0b4613000001000c01e01807400480d50043c060780e400c000304500300244001e40c003810042ca10241c030f0301d82c0705035241c1410019400860109070342210482107403c21101074405c04950317080142d01b08461041c03c0345003426240024003d4864a400000d1042040d03140304100011402d000b4030007500c2da5103850030707542c1e03035145440d110752804010081c40005a2008491240350b10300300e4900740705912110440c2d0002d0b03034151398003100082c803d0501c4e5400c01696060000c0c0800840c001e00c0c0841030441d00f070030a50b1402c0c0e0b40717003000103000380260f04c942e00c0404202c0e401880c0c14040c4035416000380791484401d805a05034822240420140360000030f0400308880c0b48803040c401c04075a208121281d528240907258025100d15100000401502000d0040c0c01500d0080074000400b5a004007503c40d40d40c021400e00d80b901d821b001018042030755014600b0603100d900400e8603a50300d485480c6206040003c0c0072081810f0f050060500c2400050007250001c0751602404038680d50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 158158525 1250 158157275 158157281
    0x606091908121905030606193c03020d0b03030c010b0a06140904090303110a020c010306060c02010804080304051f02030a060515030a050a0605040c02160b090612090111120f0109 78
    0x2c8851482418a0029a44144e00075544500301030021030408a0402070502c5103011b607410040400c05000d80d07010ba148200709200644681c2c0103280481f0a400b05500e00581041381c540c80130150002042c01694072035030003808a07500058202c0c0d60760741000020500070040020721a20071982c3c80400100944600000449001205005031404541004003c024000d20030300314141522002910241185080903051028480c2c026000c2c0e8200c400c0014105c070701c680c01540900400248002c0540d902480c210740c015800955150f49841e18202541b6004c0c500030b010038801d00498002c0e05c41100d540103503001307240c212010300500b0744407020000c0510001e07500c025007140501c00103110202c00d40046030810304040300040c40c240c80d40041400e07281c488408201590003000101c1c030541186a0759001405103600d21400c2900b070100041d00e51007900c03d844140003124002c103066401c20760140c114070f00000c4405030b80d40503240302c004004804460a848145100f8000038145820380 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 158159775 1250 158158525 158158537
    0x80a0b1302030316030e04060303050a08180307080c0c0a0b132705070c080a05040e1006050418020f042c07081b0c0f0717030a020d08060609190812 65
    0xb00a1414205083e44840c402154002c094041000410022020340ca5078030500c170166000c2e90b81c103595204022030180074140e01030310341c01002503104103122050f2404026500007030f9000c00c030300d9a83c51078081c02510b8100034641865105000b1000001e039054040c00030100c07040709100e800e8a055881581c0320000340c000d82c00d070498409242c099040040d0303a40c055680001282058100000385845180d4160050121200407440000e0300b40080d08e0301501042e404003451405481090030000000c2003400f4910958640310300044100c00c580c41a5019520040c3c001d4055540b9203a403201c00e0014408154a140100311001c10006008124100c140d80708401e20b8441a01940f50318062780103550030141011031a03202484031106001092205507402418280240551030500b40762104018004d0000e001a0b40104030b41e540d07058001c900c0030322441440c10b02a403540d0303c2c038010440902c01c40703501580c0100c60741c41c44071068041c0382c801400d4840074821a036020814180c5114a44109 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 158161025 1250 158159775 158159779
    0x30302030a030e0f060f1f0803090d17070f03030b0603060f12010209150403050d1b031d0d0b0403020d0c08070b0601031b090302130c21060807080a0b1302 68
    0x1c0000c07000076030194004030701c0b4443e043c045801808011345118202442640c032100764005000500550b809808441c800301940390909450344d0307103080764950783e906c5444106805040c841ca500820301103626690082060a075640035540c50140c6041401d00e1646401140824506a18031031a0b090000070740b031184401810f03100e07242001c2801c20141c6400c068500b151507408000c1071040703031221400800b03140b00d000001600ca03402d501d01a030408465158010130031964036075420000251145441c40036415080ca04898600003100f4400d058203e02c0d4507070000c910542c0807041160020481d48100d009901313a89013070380c00ba0b00c03c440083c25050080c090300810b025103070104420303440303254000405050005500c050f81556004410001c5c181401003079040300d08000354180044d2915000400b01b404200100701450003402d10108440e89240f454107191071780250060550140001e00600d8040b1104c0f41c0e036513160281d03100120b0904440c4041a00007140c20b6144126132803900303e40c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 158162275 1250 158161025 158161027
    0xe03010f1109010e0301180303090605090102162603040b07110c10030b0a210c09090210031a03010f020c0f070302010c030c06090f03050a020c0a061b1410020703021603030203 77
    0x40c1d001184c0c00714914480c25030555868403406501041d519612180510940740490082181d040000450300024103100040c0d0040025840e6240f281a00d1049103a020b01b0022000050380720440c500601c910602050340ca001007440300b44040b10352894495841c554640e08640460f12102d5200e5511044d4650041c4a0400c40300009019420202c040340000e4030390b802c0c0c29580c02c4081e42100e41d159200c1080c42d00100d4a2090000514058015210f400800e200111240d4013203101011b506402e0820160384200400400120198603000c0050040003131181860311000003000350b200078035414161103500011030801602148507021a90140c403043c4601e400358a00b5619110180021200145d5805200002411385070390000700901954415841d4956850084c2c0f81400031101e40d0300c580c401d40002c0000d10303401131513114007c05000700810700c03847e6032918609013550858990858014010341c0010720780c0d103070b02a040050007035080301c5101410411810400320280009001604 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 158163525 1250 158162275 158162287
    0xf070b030a020a0318060c020d02011104090e0a020904081801080c0409110c2a0f0901031211011a030616120b0d020301140a0510060903110303040f060e03010f11 71
    0x141c00da0181010401d40c1c180414610030b448100c4142d40140507044032110366030603c40c0b4a03141d04001c0310044d041107000800103038044550f029007901440c4507d40007503840f00301002188800340110360160b9400741844500307003020310b04140d0540020b10a0044407045d200502400e61007044e001e400b8180d44420145002d0400d080752020b005014100300502c1c0042084c41c1c403c01d4100030308040d410b01c410600801c0da048801c1380d101080b4080c2801e00c54010504107d000fa03990090042c1101d9022280030070044801906403500442c0c4110314034954a0100809144a0468025100c0e100210241c9040c0d540314900d40420324020075030080050002000416001c1c5a030303021049042c00202700c130300000c2840c3e0000c2c0c2580c8000e072521814500305024000541464001c07071b50003d0901c201d901c003150619500900101d0107105c0908108089040c030b4032552014412140074100c1e0300403816403642c8484025194202081d44940250b00c0c000c1450300444d054032903030b003a000d104080350749055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 158164775 1250 158163525 158163541
    0xa0506180609041a0901050a0614131a120c0306010806130b060303070611090111010c1407020a03050312041101050403020a14150a0309031808030919081e0f070b03 72
    0xb0000a0040340c0075807810b41c6884411400384601c07841981800e0000c41c00c0c0c907000703c04c01c060710740682c02907081c91600802440503554010000582d0109206c000442e8680030003007668684101300000d810101040489004001c0800c00c403883e081c0503000c55411f640e8030640700750750f08001c54580c0144609840042c0c00201000911900800e00608480c180070180d240c540132210500082c2d24801800100c20b2095608100b0791084c6101d614001c0100c05003003075000c0d2217040c02c00c2010300401800218141103581c0c084906029503003120489480c1e04d10000c40805081080d101076615445444900320150701c150100c0c1c0070740c2d0380076002403d0310f441c1008511080303000305026648014081d2030782d0645041c44000d07001c031032600e076408625000c0030304019000003540101c003240c00c0314812091060080010032150112800d540d4190032006c034444100e51041e03644c1286072a802203007000003002854409002c10216070005840500402c03000030755581d14603208600504400784005410340c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 158166025 1250 158164775 158164789
    0x11509050607030e031e010c0e09070302090307170c0114180909010905010c03052e0e10080607080f0a0504120e040e010603050312070801230d050d080a05061806 71
    0x116200e13040040c031601c54000003c5c00d0651440c0b8020b050a80e100b0074443e040d4007401a0034481159041000511b0071010215007004001419a424150002000c00c102d032400c03c072800082c0341e82d4000010445400b84400d40b208a11344210740050f104e01105081a031a035422560b4504402e07802842e2403800d10203100942c54000c0c0301d10000d540c0d07403009401081e02070080c0c000082103940c0c001210325000b2103071000c1d805c101100340880307904407401c01c1c61080202c8442c0161501c210822010b41d43e40941d040414416811000950003112300b4041d0454010320941c0c06886040b02170324090303450701500da003260b104480c06062031001c130700c2d8440c0b01c03402900660740070040940003081c0d510383c40d0000b50a41e0401d03401141e16510018543d000c2415030361a040d081101450000c455500d403046c41d410024003680d100703607034151100014141e541c9110300c1c0c281031742d8070000792210420325a202a180f004105d442c120030307600b40800208103180400f409401030203c054210040d8884006000b58 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 158167275 1250 158166025 158166037
    0x21040f06090f12060f150801110c0a17040305030a02070612090201080a09170714010e0105040f0b071e03020903070803030105011b11030105010b0c1b01080103021003060f0603060305060115090506 86
    0x310365130703400e031741502401030740540700980c0c580249141c1c40501d41200f030b030300b1100d40b085580e028903010701440031424004a04e80491030f0b080040c4e0485c1c0c8c500c3c0368445a25110f00d40c0000c005120008020341111340124002c422500a510394012400100c0b18843c191500040001d00003903c45002a4441e00c50b94011416607005040d078100031206a48121400c4d8400b401c16a5060704244020202c44001d01540f079844642e14001c2c0058141503483c429015035000d00200980b00241c00200c00034824960f0b43c03050864a4034842c1c49145003038029000b94403540c5424083d000361000802e0480000045038102c4906942c1c040414054584045485140d814100c0ea03001400e4907c00b6a0f035400d0141074042c0c030b80b03e40d01541d03641c4004591403901000d01448801c2c8884540c003201283e80201480341100c2d015074068041080c2c1c0e140840081400b60041080034036420300100e49258961721a9050364400d004652140e605c07600001264000c0040306400181041c0c000d21442c1001303409400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 158168525 1250 158167275 158167283
    0x121b01090204020d14060d020906100e060a030603110a0303051c0905030703020c09090105010317540a120206040902120a050115020c04050921040f06090f12 69
    0x80346009a400501aa80400c04000d100364659803425400c00504900a412078411213a208040c50300390702080001c0300c024502445000c49600e00c21106004444c50072140000800d560b07a03d0094200180c01481c05000c2611444610b22210f00c0b00c0c24040141d41c240e0b03400d41c80303641c14580300d020350a1400e000010700d800050381304d000940001d03208001801207144281c0103409640180f00c18414448801003103011a81c1c1020010404291182070300941c01c2e001406055035081d000030410001d103492184100409241c01515141e04800b0003000441580006c002d250782160b071a00200c003800c00d00005d5072010150108002d85405405443d070340e184080e15450400b6541c0204c40700301d030442c19840c2a646000000c01003242228481d1034003510380c904420036842804100290b8030701c201e0707180700e0003a542c640221f0780e844020013840c085680c1d02c2184080c5a0703800c07001100039411500ca00c0102582100c1e0200321140900c0e0408262400c1c1d0303029428092800320400640b00c16a10251303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 158169775 1250 158168525 158168531
    0x130b1003050a0501020c0111210705040302031b100203040302150309070312050301080c010306060807180b0703030b0901050907081603020f0c0c0a050411070206181011010509121b01 80
    0x800200d042c80488200750040c0700060301d8900b40309089083d50200e20071400031a10810600032490089404d5840010144a40c03074290f913159202a038840c400d54201070351510441c051095459041151100c66100c1940c00003040740c4005801c0c0e03a82c0c016804025400054241903000c0301c03c40c9405180d1003031301501140e081943d252500d440003901c0d0380b00a40050400001400803034420018004860020700c0c00700055450050001d2041c04082d010760100301032020b41503100b206079404c00f0054107034000c84981d0b0322102c1c6005001030406d980c00d80d008030018400040c4a24001205c240704a42c9522000025901c042c400b130300ca40f604040f100c0c04d042c0d0901c0002e2480180034050f00213442910b004100d400d928104100c401803075640582d10a50900d01020041280c00b020b83d128543d0517102c2c1a220314080d005440382501071901d081e0484060302c03010309019131240b1880b02980c07c000c0200081e45a41d414240c495003c50342c00c580240d42080002007200b08211624121202c1740000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 158171025 1250 158169775 158169779
    0x3060f01030f090b090601141806040203060109090c0e010306090b0a030f0602130f050909010506061806040e0c03010f141e01021504030306060e0108092e0e030a030e010203130b10 79
    0x2503224100b0740d100c05c6198461001405100080b50800c2404807003280c0d83c0ca0031200200c08800c009c0001414203008070740210125080703074012615600a09101034080c8652042280001c000801c2700b840180002d0400000251a0b25180700f0480314030000b5242801203811501c030780c011030f48050011144550308015000c1d0500c40711003418043c220709018069039514010400038a04009405080144d24042c103203c0c1d150f80c3c2a048640c40400515460119000395000075440d0260f035014010082a600400c130f01e0084500c015410ba40740043c20128a54a4400e12041180300d904911b42020300548142d040303048503410b00c1c41400c0140304486330078040c1c1d804e0b00c1002d04140d03011008a07444080a102c5070350040711491600c2d10a2824a00302e00d44104032036900d8020030b08444403959403510003511002811002001001c0c1e0160074040700440d2410581c0d80d40c04101c0160000f407400c00030f9a004201030003100d001d4155030449800014168892001e1288042c01310301c2c06107803207500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 158172275 1250 158171025 158171033
    0xf110f0f120901021903050907030b06040e01020c030306100513090b150a030c1e090e04050106050307080304030515040803040b09010609112208102d020a030605010503060f01030f09 80
    0xc1644291841e0b00056140c884102403480d62400300d004440c180f504081c00c00c01820800660041181d42022540c4441d498540214009040b40c840c03070780865000041c41804401300000030741c080e40040d80c0d9040c2651440304100c1b000c0c000d02e400c0b1036040c00314010400141c061500304190794080103150402080c000c02c3c41e0700550b840051907802007502d40d6424400182c00c80e82c3e201d0101c3e83c080d144400b2900208005100c0c2100c0e0007500c40d0081000c0205003405030941c4800080c280c054212002e1585801855580307400510007112030348601c00c044501072404a030081d01079503000100700c0c2980c039980c1e40c03d280c149009060140d2503685e480d000828841340d009506280b80c07544071041e41c2d45880500000b905291040801d881e44501e401004410000162021004203043c4006111346640c0810b014580502c04c240c1241d000d00c0c0c080c9201c44030654018101d401541d181001295034440064440740021981541d1143c4051380301252940a80c01c840440c0000c3c4171300145075903865603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 158173525 1250 158172275 158172307
    0x7050d09030c06060504020910030e0c030106030803100911030a020c0a15020c12090121180b0118060308091c0803040c1d190b0303070203060114040f110f0f 69
    0x40c0c001940c00b0414034288442403058001406040d075043d07142c680c40303030041a0b481600b051f14404060b501c4100f102c45403010b000c110360780100200280210355590a00f004c5641050711203909400780014001340d421001c1c0700b00c1c0c140000b0308400509542d0b075504146c0003500220b02c4000e0724000d00d4002d800054180314811891201c0400050f15071040b1a1501e203403c4603072240c1d0761416020803005071140e0f005604038180f590b840302c418000302c5103061150040c1400d2004150061032590081c810014a07110050590300c042c180745142035a24004941500c00d14030000d04072220410038000c440c141803404070310000e4680202c1c2da6000440e5111605907208840c140e9a200424505100e16442d4440e1502d008608070492500d504000c8036482c54210314201154805e5964240b441054400703200395281d01d50010305641d880e40c2c0d6107440c0c0d41d02c0c4102504a91040d03281c41c03480c145030320b03c51140d2501300b06001142400c01070301603900d0712240d20000780740c0c0403540184040c980800c1660303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 158174775 1250 158173525 158173541
    0xa150c0c06050a020c011d09190f0902010314040b010b0a0207050d0f060e0d051602040e0f06060a0501020a0503040e1305030a0c0b1b09100e0402040e010305070803040303140307050d 80
    0x16844503a105503d4400038100024858400d0400c800c032134500040200c02c0390088510801114100001d40714202c010305102d0800800c0043c00d42040710703010417006607a0205242a0007a00c0074000e0000c182e5016564a000301c0b0002c1a6103008401400000d04001c050404400c0c0760046a00c410f848400080441c00441d50880390b03540f2140d070800401c801270013100014065240100180010120040c08600514007000741a040403c3c141c0c09650f204e82100e90104417800c00e0754490040c10410688a03e4225100340c0148050b040c005020f501c009076422007550014040c2d42480c1c00d041c141c000004000c0c00400110a42d0007022000c100c041c80200b40c0c1204039141e200c5208081c0c078010313420f150003c203010300068195501000343c020040480c2c024007001c88002d00c190100c1201502d0f941c850b410000d811520108002c01c4d0f590f0241c0c03055059034083c00807903c0d12070b502c00301941d4a10950100400040c210601009071200f410060b40c2c00002500300320b401c1460302c5010004030741040d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 158176025 1250 158174775 158174777
    0xe0d121d041103090d0801050604031403040b0318010c020606010c2009090303250c0602130b0f130b0f160c050301020703090e161b020a0f0b030117010204050a150c0c06 74
    0x140002d2000c104030382d05c000545818081055031414002410301e01076844007403c1004403195007004410b0034002c0f10042e00c074004c1c513642c49050007502441030f244207a08904956103020710001e101e50000480710b104006c140e50f0b031561921190b4840304283c0750030544205842c0c1d011000380880d620803915074425a0790b00011134507898913501079010b0310400301e01004109105180307421080da20104840b1160740113070016030740e285442b41986207803442d030f84000700b0352802080b0200b98200c00ba00600804000240c10300030300d911030016246c180304000e900c80c41000c2c100085241c1d140c810015045050161510002103550b48002c2420790703002681c100c0c00030318480014480162039803415504442890f2952410f001102e00141c0105c04000c0c800700c40e10743d0000fa42c821076441d1003000c0068104204001c000f1a510039040030150001c0c0920700f40380c10202203660151005200b560203c5000402080f40d2900d001f12281e060065044071200704100240e02d40e02003010100010001d1000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 158177275 1250 158176025 158176027
    0x2070213020301080a02010f090f2c040501021b0105060603060f0607051501060813121407051204060813080406030b0414070801050307060c030203091504030b01060e010e0d121d0411 80
    0x41792000400300ca5000e5a114180400c510b400e01c0b040c5040c00c070038010342c3c40c00e600c0c03484182074103141070001e0744000c0c181050340e418180030030081140640103040341481c90b421b510380003005900385600380c0f4804c0f5841d5800c18424000a07515140444142400e032202070328203894016252981c0342855891112a00304c807106100400140341d02407000381d03202030720340c68106103c46965540065402260085400c00c12a0000c01c0803048142d030449111503845000c480511101480703810301d42c0c000b4031450010a04010002e00300d6481490a2602031342d02010946c542070a16005400409110703802c05d8101d903503075081c8500486001c607030b10b006d808552280c0e1180d40c98041003515181050b0440307030410506448200010703400000781e49030380c6401c40b1049070124503601c031215513016560014040c480c1d001e000040c103942014028140300000e81e1074010548054050029005070f4413001005a60400c1c1400c03c0144604008500070188480c0040300d401e1041c001019030318800885803501b54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 158178525 1250 158177275 158177293
    0xf1303210507051e1c08040b010503010501060906110c040207050a0b090313091812090806150105070807140601170c04090512031f0b0a030b01021b040207021302030108 74
    0x140505400440c0c11032078030360300d0031410b40c0d01c503501c0d040200080d100307141907520f20510130300c1d0034130440c404080307126a004003205541c10003e10380401920f065421502c0703440046510304040c0210b90589040d91682c0400c6441d00034129900110082108014000c01d1080b00f0665a81d000518856020708003c0601c00c11504204505e550080c00d014a07540c801c204203c3c400a50401c50310440e400d100d400110307800510300403036210f010b54400612400b17003101c1c07802c0e4003078210141c0002d0301e1154044541c1561034052000e04800016070740c030b002c5102400058005072240300100041032044442125540100354404e02d025000e0b0450040d085401200740c5200c0000c0142c60040701080714207100c45c07200b68652a4a500c52011a40c0b61014000005285030140ea2803201e88114100300d600445580c0e8280c410340c980003200000000381c14101549099880000c0c103440b40c501241000c0142d0151908000082d0302242e0100d802c40e08010320000d002d1030700e1015600a180450107011449 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 158179775 1250 158178525 158178563
    0x20f2206060918200901030f140405070f120b0711011103010602010c090506040509090f0f0d080105010507210309060204080a11060a2309030f07050a06020705150f1303 74
    0x2884455030780f20400e00e41a44034001110803040c01561402940c10640d6a01c0240c0040f0003429004081c0b14525007010b0300303500354150700410700e03206074007950560304042c0d1038450101c1d4403651440b41c0561607501e103403894080b401011000e60443d20906180d00071144181005003541c08440344646806008001005410f0b020302500400785140c3c5006048203050800244440c0110301500d40a2090140014103a8004100c030400201405084840d80e0a004050a0351403446070300150000d0a110000101940641c09888555910100d0030700c04500b80044040710b202264640c1d020540c80d40b5082d804124035200410250100706d0141078407103e00d08180e1801000485040c1c05140308002e1540d04640c4020801d90300d40d900c007498941070400c2d50580415000c1e0059040d40750250003000840c02c4000101081181d200791038000708640d640105a1311000103205558000b00c41c1c09101c101602064010a912520201005c3c00d10928211440c45054250422038007005103c542038100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 158181025 1250 158179775 158179799
    0xa1809060b0301020c0304090c020309060d05010303170403120c180303080108010605150301030305130f0905072c010503062803030e040203040c061101110c1501050409020f22060609 80
    0x10302082c2c009605d400348505205640340724a01c40c803c9542c0d900c1741c0801ca058801e00494806010040800340c50700300c82001c040c0100303070a01c8118042142200b4401d84841d01708841482590561201d00030001460242c034013810a10070002c003040b0143d41040c0700c010004401001440c000d556445081d814284d000742102c0044d0480351141c03000c000c1840000782c0c4c0c0800c607810350ba0700d85451600c401e420000114100b03410341106280700312a1202140d2400d6680c8500d01c5131080780c0d80c034074802d00001c0d41104040701003222401c00080841c0e0140030b550041d002181c0003e00940810010200d9003101d07140c0100e4220520600c001003203007007040c51750106c00d01c090480100d40031850f604280e50703141c0c612880343c401c55050002402513003401d40829031200c01c86002c0c0e141e565640b10401241d40d521415881070490134101d01c0000840c650400b07105084c16503034040d08000b140501c2008001400c401106108000448000e050604440a001e50001400152950340712030741041180c143c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 158182275 1250 158181025 158181041
    0x1801050606120c0f09180601080a0b062a0d0206040c08151902160b06041104050a05060306030a0c060c02150a0c031421010e0c03070206150a180906 65
    0x30400042c01000003180d02d88141079000f801090046640c0e1107102c43d044410f00503800801d502444101691030501068000036205003426a0b03203551030781c0e03160b41013012184803030f401ea81c110707006004ea46480b80b0480000451081401d0041140c209002c030014a01b04000c0320010040c0c104400f40010040920180c01c0901440720140060640c1c0d01e1124580d2040100804510102540d101c000803416a0407600c403e040442900d0f600c0d081401d0074203468205840a0f0300803494080c0591008204106550607a0300041440c10800c2c07900d82046825080584070701c0c0e040c0549524900040c2c5d228500500801d402c1d1101e040c1c01300c51f801040340d07406d81c0140c2c4145080d0704100030001250700a038494802580344c14010060b0082c600041043d0045029001840d084402c499865090400c021070480302c000394405d0315580d4015482d5903600082c0e500c0e10141c0e101d100405c24110080d00c1e10204004e0142159030241c0e0303181b00140d07090b40d10280141800759500c80080a0100794000e0b401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 158183525 1250 158182275 158182279
    0x3060501060f080610050705010207061a011403010306020d061d010e1003030f12020d0e06090f070f121b060522060c0807060b03120a09080d12090302100518010506 72
    0x10141503030361806031003450024205172140d10213009600341c460080007910802504000215190398082c50444010002c952400c00c82406514000c00365601c81c41e4201c06808020100a06692031942c510020350407441000000640f0f130900030403940300c14001000f0302002c85190000c0c81d45001194200090060f16144014418100501c00300390401c0328000300c0c80040c5050620709011070742000081c00b0768503600d06410f0034030843da0f0710f0000c000349540c01030010109640700c01140c850070a030796040d24482c0807441c034401034003001200010040301d03110350301841c11502c0da254054400350b00242141c003d0b9001c204045102500220024555443c1101d601105140c1604060028144a0300041d0050010701c000810f242007180b20b0304002059480902100c440a018680c2c81c030171604019204000125035a5002030125030010782101020b03200d4840000032000e04808001070140c034901034040d441036050541c00b00c03500b0320500f4841c88500d05100c400034001c403041401d54802070300042c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 158184775 1250 158183525 158183537
    0xf120c0c030a090e011a04030320031912020c0d0503090f070b040e090703030206180a02120d02060a020a08040f0501090c0303050c01060b1c0b01180e01140402070f03050903010204030215040306050106 88
    0x1200031b0f040078080700c0980c1e4060a2035204684d1000c00051800c0c4215030a042130701020a819400c85a504105800380c0f1054560b0071100c0500000c680490090200c00c8031303254440b0001d400a2030080300115040070004065640e03203040703c80f100307280c41c4940d80700000c5000000380c20006481d1034121756401c640c801c00a000500d2854030001d40d80c142c00344c6498007402c001030b484289810f0130080c01503811340c040c01c02c01103040c3ca081819200c141e010310100240c0500400030703903440805c0c401c0314501800c6454400c950789440c1c40310540c0504091003158151742e6500384801103007102e00d94000039480303039841030380c0e414000400d6400d440351948032006c032030024042d44001c1c0c14042d0008111100e8072030002103c4100b00c0048440ca21410b080c540d21075a1000e000c01c03c072a807020f44c24141c801171603480340c621000f18180022486444070180c58a95032040d6000024412070040c200500020005400d0035183e40001703150079044500c2c040c01c03520005041040201038050f00c2c1c01401070342406 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 158186025 1250 158184775 158184809
    0xa11150705100c05130e011509030b0f040602071e02041805120706021216030c210e030c1006030507060503010e0a0e0102040e07020a02010e060f120c0c030a090e01 72
    0x3860381c60641c8900c440039180c0398004003c10342e1041040c0d4008031072001c400701d0115900c0700d40c10000042030182c42038a103806038544828074003c1034a030741102d6011008490340d076609003816900700405842101e605408000d00d0010411201d02e00c1a2959110035484482200d841000100c0b90440b80d0302940101d52407206010450104010100038412149580d0b12141880c058000340b0a180e900c0d10b20303c030100244420741c24040c41c0703c0e0b40c000c1c00b91420000300f00482415151101d0581840d00303103026014440081e040550001e000302030344070007201d040c48203100c1c1d11401d180895000000091381d401d810003c6c80810400724006040c1400e042d8a95410120003203001d6000510f0792141079101c101d007440c4080e0960446004008a01090700309007401e160007516486070120980c0018000b0040f0401c0c1d2401c04200d4280b407418984040c0707070266401100c0c0350030700d00803c03c0032000018044c00407490400d000a10013503e465403640011070404032001c0c03202070186c0201c2c10b4020b6040f20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 158187275 1250 158186025 158186033
    0x3150106090905060a0e16090f0f051915020322050a030f0305070609030509090a05160e010c0503040b12070c0c0308161703150d05030414060c0a111507 67
    0x1032010b450798004041020f549000214040040e107500259110a41900b00030350761b0030845001070f19070050358a1001c81941c07045443c00442281c0510814000c034031908018620380329107603040760705a00d114150346d541d688c441403202c12808481c880150f000021299041d40750000d002917a00710881d0710790320311814800824412025808001d001641c520700030000d160207803058480040c0d1059007800030070002d190081164118030364240c0200090004254244100c1c084c5520605140c120580d40c0258103900311f403000e074080c0d51b4505003c0ca003d501d8002c0703a42400144040d1030703290040e59584c16000313550f81c40c10708020441c030304000c100081340d0005240c003100041100c0d00643d04c01d4031104034442850300b00031b000b10010a50450748500825088014000d148520203145a031582d0500c09024800856031345900140280c0040100344400039031600710784281e44018280c00d09240c4030310041468260700c0e20058400030740702d15a0412914102e41c40c2c619040e0811840d0b8140340c0d160361 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 158188525 1250 158187275 158187287
    0xa0f08010e0c07080c0d030b0a05010206041205180402030a0903020601240c080405042f070f02060a0302070b0702060411060415030b0f0307030317101214101a03150106 74
    0x40040a0800003d401003881024019500503d803040156031a11540c103e01900505140381100d006400e151000619580045500c902c6a0741054046950342204d00048615610280305440c000200810703c890584441c406036219003100840001e01040707600b400b0f4640741c41603101010071600d8804da40d58250000c4502c0100c011582855404c201079440e210a090003582c03c059001840c1045040d00e5118104c000100600140c1c1c0342002c0d2560f0448121861084a001234180c0d015400d031040103041000c01030103100c142e442d0060400300544d8581c44540d10940d10b40700180e200409010034003202c1840032154510407102241381230700c0c18085502c107078459200c0d01c00781340d43c41c2c003440080d8861840030040404011b0a9031400e613181d01c1c000e030400e513222244148111001001808168800340103109031003410390100e02c80030044c0e13221214005003020920450044000d41a0042014095880d004c0c040b100c01c01e800e801c000c2c0906240079403001c00702481c100c1c1c2800410506030060 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 158189775 1250 158188525 158188531
    0x31d101815090602040302040515040e0708030901050f0904090f0b0108070e0a09020a05031c0e04020703020304120c031509030e041b111c0203041e05090a0203070c050a0501020a0f08010e 82
    0x41002c41c0310a01420444024000c562020b50010700301030420801c2c4100021003140300b0412103003003109000e0291020740e11101ca000742c81d1580e10402c16a100c035030048000c1c000070a4000442c62514441902140a441c10344408481c880c0c00320b05514100f01103001c00901400000300203009540c501483c010030254050a150700d0687e4520f2264250b440b402d094030007500c1e019080b50b603012a140c2c0351403541550300310a480010425100702d401881e0a00841e00070507050750042d8201800c1400411000c40506d4080b144031400900001c00200c0c4c24502180f0b8503022080094204190308024100c40a40300380341d40b2031880c080c074441c03038000c40d5825480a08110714084000c910f41064035490810401c0d100c030461071030101c030014120b81c000002c105440c440c004e600c0324040b24480c21030040185005107a4420305150000c3e00c003140d190702565000c482485d007803130886140d8496909010404100355038503500021001104c40d0019024481d695003490a141ca640c90000465204500a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 158191025 1250 158189775 158189813
    0xc020a02010e130501240215010b0319110d1109090a0b040e0303041101020f0609120915120402090c041a07240506030d26040201031d1018 61
    0x40d10042c03516881d0581240007074940c070384040000b96112030040400400c06800c1c150008568000c16000d01c0c404660b0340c10310711064010306a1a400c00054a0042d00010007407410084820080d503000c5005005251802c040c90002941e02d101d03035030510060311040940c4440410302000107203041e458000000f580102c80000001d2a01d4a4130001805428044003080340c0b0704c4040309000500ca90303419003948409003602114150418115200c2d103a00c0120b880c00c2e0503400851203160b138408801d008180c0381d1001840b080300e101080809170240c1d007050390760031002c03072017082000114105100c200da044445000e400d800e1030b2500142a4aa01c103180102c003500078045420000c0107500c00203021119074800200000c08000e0b942d000092030101c49441c42031050b1103040500c20b0254840050084282c00020070100489a0b01070443c1d0014004074101070781c9a030044009500301905261040002c0050208041065421804d94001892110704050a070310204000303031417811101941d40072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 158192275 1250 158191025 158191037
    0x1b040606030506030c0111010b0406090b03010b030f28080304050a0b0702011506050d020706020417060a0207020f090907170d030509071202010f0c1b0302120c0f210f030a120c020a0201 81
    0x1003910814090070276107240c290050300b003840100e0400c147d904100868401030b00204118800d82d400c040c0c0d04d22420b4000981900061a0000c2c442c1002a01c000d10b400318102c02c01c1b03900c07803039910b40300e080e482210240c1c0c16030015243e80c0c0821012442d5650000241d200a000d5007034900d40180b2800124812042408000640d040c00201e843d010b86188980000d421074031146e40300c01e84c4080c98100100c1c1310603030081c000002c00554052007683c140c00e4001d00400d80f6014114203001c0070540142441c001445441400076400d00001e8104a485100300041c0c002e8a500c91006001c2c0c3e5005024061650001c038414400e0500380100031840a40928086040e1090744030181d40342c0301d071488081d20b80c4814030604030340b50300e03000c25150881f4030a49100078200a00384e0301c10b03190345d0391600341b039444250144021910301c0d0110a05007456a105030201d03400900111075803404c0302100c0320b02d100c0c0c3c00c04076201840c1c2d034002800b0800c0401000051100840300307100251100031a05009040c044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 158193525 1250 158192275 158192297
    0x1207093605040f0507060f0c0b06060c0d0e01020c01110d0503100305010603081e09030d0f050f0c0a0201081b0307030c0c14070f0f03020618060702031b040606030506030c01 76
    0x11140441036108024400400190409003041050003039880c006039a9403042480c00603a0b1480303400508054040b964920003501196900d107802100d01400096014a060003a060100030a00041d164200c154403903111080e42d800019051200b41d603041414400d8044031044120000304071969240594600317280e503551910302000004007103030070107046580b0f030400c080200034204d4003e119010540d00c02d01c04918400c00c51032000c1c401c521009802d500304000ca51109401500c5039100301c05a814200d061944689484482e07070007110030740a9590204140300c040d542c0060620b500301703019244120203408600703e0788250344005400501055074481003004224440d0040f880a95804840c4c2109140c1504409076038450381d00a00810308007008002400281c803622001c210303a80640b1603401c0607118010501c1452243d00d42e80d030005820030284006036814000400169911080c0440d03005070f01082c4400c440498010405161400080c0b000650300041d14454401c801d2030600d4480d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 158194775 1250 158193525 158193599
    0x609040203120708040801060504020c0d140d0f09020f04020f18060d0c05090a0f050307260607080106021504030e0d150e010209031c090b070521120709 67
    0x24055203180d03a0a00c80100d414004c00c180000140b04860040c030003802090740f031340d003088128425003510203140c0d4040f0700d060048901902d20507250120108500c0e00740310003848640192081c03c0d4000c10280c2e990426281149050b007401c0814240c03d5a0442c1003910f21000341c0a40c3c0b0903800696544c81d006c81c454803885d42c0e2102125828500150709201018210102034201d42207280114410440d0000c0407940b04c196000c040d04031480100240003243c40d02000c268a101461107003501d1a000c0440e0300c00d2244100000703802a480f56a50000d03e45c90008000c0c10641039403614140301e00460140310100e64004002050400b003150102e506402c14030380754030103000076041401c0b42400c144a25401580643c003400c16000c0982c10b89071348020f8804001c05080b5404400380c085403580308280100400c010140100c68030039821100f56030095000c901c0810113224001d8500b0303130000b03034051302040608135040c5c10003942d00300718908074140f403051100c0c050003482141c49444945040003100b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 158196025 1250 158194775 158194783
    0x110a0309053606030c030f1c0c0606270203060a03120203220f08030c0709050402010903051203010504060503010203060d0605220c09051602060106120e0102181203070b0609040203 79
    0x2248a01c1040442c4008000380c40c0c029a0220390703140c0b207030041e80a00c0d1424103000c0707440d5146a80207000f810b4101c1c0c1000407000d42500f81a515810070845810701000541070748a41070240040218031600070200c14a5414400e001d94240b802c00c6005009021030354582d030101c4415268040144d4044d01a501012441c5009240030103025412503002e0f408220a20f00c0304509580300e1111207200242c031100c0d0300382d0320300c5000c0030090a903001d03400c1008044c0d0079500081d001441454103529203507407503c415103046140d580c202d21a03000040100024901342c46510000c1c1800d80080d4214680307a00000d01c1136800300c401a10381619000051324024950b0b400800000201d00001c0c066262820100c0c0c1103d4a40a4850120701d01004a46900c00e10200f0700b100301d02941c010409603080c040d0403280300c5091030380c0c0f1075015155001c002c00d119080c0060816005c03004000101410780004200060310076150b12007003030704100407400108403245043c80d40110140d904043d142c860384042894 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 158197275 1250 158196025 158196079
    0x5070b15040203150306010602030c15151002010219170402100e0607060618020403020907050703090b1207020d030506240d140a0606080f04020409050709050a020703110a030905 78
    0x442803000041050301311010007280c40c100d006500311181130b0f80701c0c0e505a0b580d109040c003d107090b5101000103412001c00d8280c0c60f83c410448800c2880c41150751010800038501d1540140150350007141d803c0001319103215100c20000546468a155120b049803001d050801900290042880d00b100ca0030003400b0f900902c0254078081d040d41d960301c0040c02c100c00104014001c800c02d40d103401d01d100c0302e20000340c001d54003501d800503c1010107445488080c0c51580c0050011000e001501d000010301c21181c070003030802c94120f0164030b089864940c10003810600520400c500b07041c608000d1140c1911164140100c0c09041d040e0804034440000c04030b2800e014140c0e1700a00242000c94240070b1041c4000c40034020390022405108403a21980d0a98241c41e08650b40c1c03125180b407100080241c90240c0240c0c44c440e0041080c3c03a00e040d10340907101e0968901300c0d501e00440d600001c15004140c1e000440703c182c594641c01414407400385230380062107409244151442140142032021044014200e6a02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 158198525 1250 158197275 158197279
    0x4080312010e060d0210112b021006030804060807020c060a0906170f06060f0c0105070504030b090c0102060604020f0909070908120408030301030224070c1403150601050c010603020d0501270305070b15 88
    0x804001d542d9281118040c3c281010042c02544d40408ac1440c440c0140020360f58845d001d28181418000e040341c03107180040c100c404510410504c004c01e0b4649000911120b82940d136040b4200b8180140a003103542110081d2a030003072408100080c0744110120743c1c0e0014400c665184e503580e0b0807000c42d001402915500c800552a01d02031014480e0030500500c112441003407070000c1540c520301d036203850704402e006c200d0141e0088000074406207083d500503c00900780d0ba00d90360404030040c0100e0020100ac960840c080380c01410188800a8204031200315062210b6180d8170700b0303003000c00340d988a0006100081c0030f13500c62034000c00d03150030b1009043e05052034212826211070280c00d281c201482280b0802c500c080200b14503260b641008180080c0101814060070690340340c90004484550080b00b92003120355903240040010781d02d461a030302d41d8500130340c00802c01c08190483c0928402108030f420a4039078500c40e64400003170300f08040d0b480164100035007020076a698404144c10225001400d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 158199775 1250 158198525 158198563
    0x30307050f07060305090a0804090c111009060b0f031c021f23010503060f04170d0506090f0405070605210c07050714060d0902030304080312010e060d021011 69
    0x1503086030300050484110f40c15903400344010344a02a01c561035502e41c0d10003900b0790300100010310143c19650061440e903849894540c07241408820003d08043c55405080d02130b9031a01d031510240501c9010380805000c04541241100e42100c1c0003907940c04031942114403101c94142c010504500030301105404100c120303192038101c2d500e15604001003c02c0e60103124443c07041c40007914540b00c5a01018143c45018005202589071410340881c8808020011200c182500c45032000000b801d1029042d443e00c10613000c110707428480e0412440100041040e01d61034404030070480443c00000710300007100e000b4100b09a0f118105035103140340420183d122303203201c0840c030240080c200400b402441c059000d40140e4110644030407950710f000005440743c030750200050000c4000018140e119807022440241107a203041c0d42c500d08ca50561f0882c09030f41c0854000c1c6001000621071802d006030f40000300b01e583d0016084144d0000700701038480541c02080200d0138030103100c089020400340d0b0070204045a01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 158201025 1250 158199775 158199793
    0x5010507090e0a021c0b030a1b06110a02010503040210090e01060c0b07030b03071e051302070c0603050606190e09040c060215010312050304050304030602070609060606050903071403030705 83
    0x340009681d8425203540705000000a00c84207854426a01d0700c5c1040c040400c04c43c0c1000c0c1e60000507043c018001030b07042c003906803510002545c0808220604064102c90011140390140107000040340e0101d80b030858110203515130040c1e03404030440fa403007941107d0f42400700c80314240484d0781080030313086084068104000851410740140074210b1980c0729080083d01992007076000c5054072400880c0c19003540c0300410a000401d4203203001c0500380341a489090600380c3e0f6600003075050720600e2402d07298580c002030001c240126440240b000d4440303070138240b0042c03d1200200d500b0f440303114010340b82c4007990b5409403076040c410503864540c07000c01060620750f81003604102019200380d118110252041b030044050103034a00802504a940140c44502c0d8000407210540b000d0703100900c03c5030b40d400200030100c00207440f4400b81c110240200c8000030030425624000d81100e5640d00404107020702804940800c4d9000103001003521061400004039070309480210345103024100c4000d196016400031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 158202275 1250 158201025 158201027
    0x30106020a0605090c031b0102160e09010608060f0411060d0c0206060a1d01171f0902010201050a060b030a090507151112040302010518060d0f05060a210b0402060705010507 76
    0x440c070034030b0048004028540720300d010349554000d00d0000c0303505600b009112880c01e0030032001b40c0842d1003060040d80c0110f540340004c000c503002560000c5090b00c84010a10456084c00d00c00ca0018110881c01016035040000b101141c1c2d03003004200070450a40c0c1e003031090090321030600359a440c0b08010024001c45603844c0021752035900c1122028094000740d000001d21401e10cc400c0b0454211200819800e40d0800f546803508a41c04441c0c2608c0d4441e40e00b290400030605040700300c1d1b0b80c41200e00012203619038030009003510310261402c052907040130401e0203004454070072660003416000c0e0021f480306807490680c1c24508ec950081610b0708600900340b4400b078100c40c0b0010380e149600305441003600c84010765603143c0142e000c00780c0001c00071b12001620311044502c420103504020040b5040034410000401500c0e00ca03100f40c180785441c1d1044c030415041204038072000d8071200d04194401c50000c01503122401c10450007806030b52622012a0a5488203002c440702030b0340000081c00189085a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 158203525 1250 158202275 158202283
    0x51012080a0305060604140d0503071403040303020f0d05180301090b070c110a0b030c071707212c01030605061b1513140c040c0801050118120803041703010602 70
    0x304070000ca030503d03000501c2498010100d4080e61884c0345840d90144041d014004003c1d0340300c0c3e04131254072003003040402140070081c0450240e2450401181d0716801c43c90000d05249418524092640c8100e00c0c0007400c54000c415a460b5201d100480c015828542c00041d000d01035000c00540780f50380d003406000711140d000303403280c601e940142610050703001a82d00b4840d02300282c0c81240c03d403a05c00d0021070401c00d100c0d401040101d0007101d03900201c420342c500810482d80242070458416032100f26450014540501c0301c0c0c0345000d1401c0c9036038034103128114003e0104a10300c00c2c550b400c0235103400004581c021762210010b044d001d0245611500901801c904407603c2c43c107400201e10a40d001402d10b0240d03003046621070b111120742e0381404041036580300414550441e4050310703409040c88000c403e03160340c4540502c0e56a90354510409501d400009080130f054424020a5a20310a4090140e16510303161031954a900070180c9650307030342c1ea080103c103075001d16400179104c010000c000220340380d00007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 158204775 1250 158203525 158203537
    0xd2102070b090c0a0f050d080f0c0312040b060d02030d0f02010f0e100e120f07231e0312010b090d080a09050301060e010311090a1503050a0b070801081005101208 71
    0x40c1305494842e40303910380300540e51402e1141c0d680c08101c0a0a00e0006555240039100e000b9a8400103401c00c1090440c5d613095410206554038002000c4d0204014480c4803840190020015195030407500415004a521084100b01c801d040c01645a0324421080c401d5011045e031180444041021038401c404158807800c1d0700c02c12a100c030741010422100706001160030300e0817101005150345850898100300300903812918082d100708100200f020500c5080070001e22200240034003134030030040c004805c0d54000310302d04001e0303410354030500601c8203043c820200d041c10340300748180326070300c0d4159000081c401403840840101602c50100d2815a103982140d026820f43da411030003448140c0d111521112049800d04c0702600d55401b0b01c1a04100b814103019158000921140104803800e00d4070360000c1c050044e5100326000d46c0034a00722402d00203119100c58210410f03150115055241c0344100d40e03166180d40100103126a178901241c511042e8201a4009088140805403524801d05203807200d50081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 158206025 1250 158204775 158204779
    0x280f060e0301050c0a050d09080904060b030402030d0203031303030b030a0c030c0315110d021c0e0d0e090f06010f05070606031a0601030b150702061c09140d2102070b090c 75
    0xca1007801030107042d01c12917065981c80340d0611102c0700030000601501d5100365202c0c84100042c1d210364980340111009005048007290381c03030601d88103161804040e0f0510100319081841801115181403002445003900351502007103004807440001c1c20500b180f04000d054059403e40007040000d540c100600320303070050701d01700c210604140412040da408001c141d04010801c00c0401c440d404298094803812161140800e15800c41300700f8401269109101c840e000e600c030508800b00c680d0300c41480b1140b081e0075101c2d10845c0c2444c244501c0c07224005007241d410300c541180110b1410384518252240e0b103400c0380c030500c101079403410310848058840d461061494230900c00a1720035400b0f4004c403000e60fa0301900c10007007402c11841c80c00381074005910403a030241d170400540c070107075402d105160990380c002c0e1000160340019281500030220b01c04800c1006e500806107020b105034100c0000400741a1760b044807201001a501c40380c0c028821610014070013004001444201600020529516801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 158207275 1250 158206025 158206031
    0x106020c01020f0601060f0c03030f0509010b13060b0712023903030c060103110102120c0708150f061e0402070c0302010e04060b0f0703090b03040501051e06280f060e0301 75
    0x180d40d083ea1200300c2405400041192082d420140511842c40b07492540c0c081e143c0060765050600044040e21003d60300b1110b507a4642c26015480d141c0f0f0320754134640c81407000c0c00300400b41c03600c01c60030080d005e0048058a0b614684250001e81030082c404200091840310080101d10248040c50429842030000314454510380c4000c40141e04001040301d01900c400f8000301003503840c40c0da0390b05211541a04550441c011208605028100c0101900c030b84489003018028143c00e00d80d20350b1503d003810030440d0303280c0000d00c00e114590101c4494141c1000050303441150f10500c070000890040a44076a064200340b00040403c00d024081409000b0b80e03100b40e072a00400902e07202008251140d80c0a4a03044d010100900c40b10f00342e5000007051f8180c4241096200c090ba200080015900200e50a072844d94580c4104210310008000000b102c881c0200340788810309081011840c0da24540c00e04051f540d00326000000c0e401c00744040701c2d00031714000000703103c8242c40b010001d2540201e24001d500940c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 158208525 1250 158207275 158207293
    0x31903020c070f0b0726040e0117120f090d0b09010e010506100f0810081204090609020a0c02060318030a021b04020406080f100e0106050403052a010309080405090106020c0102 77
    0x80d00d0305110341150740c0c080300c0d03900300b40641e03c03100304480c2166055940c0700c020203010416046c81c0c501600080c0302015a807140b0358980602120f14403c01034180c1d1043c0c1005880c80791042801080c2c6100301500d03c1265290700e8540c010411200c2c2030b00e00640040788000c20030aa901054219245100843c8028060340c4c9544050015200740040d4110200308055503000e006440f4441e550762148030100d8482c84150750309103140c104502070300d80d0b070000000098240418101801100000d00c08034800318944021584010040e07111040020b10450000001c629400d9013031b1803200200c0f403c041603c0e174400810340c000e552140480d0b0741c0c60308407040c0401003105143c14801c4d41d04440040d00d445900b6600c0091010012230010110001144001e1006c24000c013111491130207804180c5030f01e41d0b01c1e41942066880d1540506a028a03010f1004407804180300071501c010031240c0a090100d07030000c4901e4014050b003d950000381d0005800d030000a8680d038009607840c08040e0070707020b55188035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 158209775 1250 158208525 158208539
    0x30606090c0309032106030b0a0b01020f07050102150604020c07090c020c0109150305061c06061a0310090f061e030201080c25030e03011b1103040e01090e031903020c07 74
    0x550307003ca024003c5142490402820094442654220000340b2030026406489590769840c2a00660304443d01559400032582103503010800c0080b1500740c40d005104a0f850400000d6a4500311050280c0059400c0041021619290140e80041411750160f68116807602d100c08010170030024000c00500c104a410342403940100c94800a844102000051000240005601900010b01580c0d00300c81c0f6110f016076908510b4904007103041c0b007524081a1680341c0341c03000444000714020740480e00c0c000c0090020711403880c20b8800803164004000309034049028580401007000d980320710540ba141c0c03120304413400c551340d807401c0c20b4901c03d8803400e4080d01c40d1101c4804030300030303016038036001551780e0310b0b10f007005803100180c7c3d0343c03548a451319940250410000c03e01f03585d0381c8e90034200c80d000d940f241d83c86800d13003202c40392001c1082034000358141480c004e103138400d00300306124805c90182d071000d40c0c007400c0000b401116490354590340321075920121441d00a00030340c0f040b05802164010844041490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 158211025 1250 158209775 158209781
    0x10504150c02030d05040503160c03020a090506062703010f0b0915100e04020409021b0d030216030c05030409050c0703030b0604050a031520070c1706010612020c030301030606090c03 80
    0x1c0d240a80c011428030040c13003040c3e40240b002401c00c0e20544028400c20441c3c00c00005401241c503c1030841c03810940c914414040350140c90342002582c2410101000515202c001c1907800c1ca05210554440c41010a103008207014006c41d1060340550a01007906004d010980142c3c007400416102030720710f40c1d0b94000ca002c1c89854454082e0b4060815220380310518400d101e207190380d01c1e00601c014502130f5102030700c408903031207440d520001c03001c043c00c80500700101744111070034089242815031a15894440303080c0103040303003030f001024824541e49075014004108155000340c03018500401490504103030415107a002070030110b000905107009107005007041c1042e9000c40300040c2624031100d080d541e82400c0301c081c3c41b80d1070880302d903a4601801044d1000b00715110a505100d10203548a03401d08101c028004903800910f10071207540b03840003603000c00103201e90445550340b52a00e0803007208e03a01c4070b010380700b40c000b00b400c0c1d4171002c000071041c0a00e41d071182e03045a500d6036040140d141d040b0029000d0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 158212275 1250 158211025 158211041
    0x901050607033e1e0c130f02070b01080706090807170a02040507080105040b0d080403020405090f0703050328080601111002030406050405010c020601140409140303040501050415 78
    0x40401c0c070040700000d004820403041000c0e486000c0e00c20f241501004180100098a03400f00c4030801c2d010560a810103000400310004501d1140a98403110312169540e403048824241c01000e018049020ba0080b80d8000c0480703030b102410075941e450150810006960082c003901401d0b00940303000051060040c50440e04449030310002e05140d40c0b80811064100b0020382a8001a020f4081000016030301c61241c0d42c0f158090f40c66058031f5504000500086410030014180038800c0d048200340444c140c0b00030f4400312641103d0203d001d580740c0c0701190508144ea1120443d911440c3c102000300f15010001c0c08001c401c8495010001e0100c801d03c170701a444851481001c12038000201c0d000394440c1512010302a001e1007284e5540e9040c81d14001241d008540c1550083d03a035606100c20030030280603030704004081f071000301351039414840d02d900201c0c084903d861140360340b42d05078801c000503264401245207261054a469140a00700680070704002c8a00b25070b4148039409141d10340c0313840d01c03407070103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 158213525 1250 158212275 158212279
    0x3070302130e0d18090908210a0b030c1503040206090d2406120b092109030705010f020706081e040b06090a060f03030503091207050307030807020a0b0406090312050a0207030e090105 80
    0x82e62174400e00740c00500081c070081d2009003040140c3c5085000b002e403129401800c030000348140d4902010355078211038005880c9446600003209002d00ea030348119920345150060503503a580c80d1100d02c00a801c03031003110303540350304403a0b01580340043c402c00c9400300350700702c0c0d17140345005013081c207100240e003101c0960007002c3d080c035a188411004640b19003a00e5034881031850450b200d40742204c0712401c5a2016a421140c522000140d8500c40c0c00c05002d40002008282031851a401c4180c00103502d80d403c0d4002da60401140d0800611400b401040180c888031031321050350b21504042c141000e440708101c920138040c50381365020134081840c0703200e600d0440d4450320b80b0000b400e003142d40c11580c560024000309858884e0f0501a000b684090004100a500c2400195a01d45051a001d80882d80c000d2045003075421614400c00031a8148000d02e5000d580320300c0004001160b49016a80c0e041120414000946000c00304410078031290300424605000351601c40d400c0c0101d00411000d40000d0140075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 158214775 1250 158213525 158213567
    0x603010306090f2001120509060105010507050703240b0a060f0c0305090909070e0a050f0601050705010e060a02030108071a0a08041e050d0801060c050c01050903070302130e0d 77
    0x10205880303510a1500b03c0c4184070841860006881ea440e08041da10190031944d41010f001c900c0369030708100028403003d08050305100302e103000e0001c00e4499205105803418008005601c4080050502105001d15405245143c1003220403403210a100010505c0c8120b2900d400d40076032861401a4640301190071a81e510355030080300b01011580ca4080300002c400b072103c14030905540c0e40d99062118855000300c002404824984030b082c0c0e000e40c0b0050181c00348a45442c05026100e15000e0069504c07100030f00748140d94460074501940108142098200140109800c0c0030311100704c0c0d00218101c0e6000f000300c0e0700f1240c13190499103130b0310f2000350840f22541c03040001c00007642c000c0803050750050081d80341d80b03d030f826080602c064000b48008100d85c0d54002c13003040300e09250845050380c00b4180600d41200216440c0d50b07215600e0450050881c10b008000ca00d90302c040d07400704021000345602800d080c084034103484a80000d404240c0c0c480764503029a100076108588280d028401d55060303051030f1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 158216025 1250 158214775 158214779
    0x9091407050f040e0408220f03020105031915030201021606050711120a06020a021b01080604110405060406020a15020a090e060a17030a031a030a0b10080d020a06050109020306060301 80
    0x41d1226031040120442420080c48002045000c03450058410341c02603d505a6440d044803440c041540d02c0d002c200440c1e91600c4092001800d010319a1041d20750a080075980d0303480301d07041000b02003440001418000d00700036014408030380d42c10040c000c8078030030780890b21003d071622144604220240500d2000400500544001c1a000e1410710541000a059106041e03036a10000b03040c030914860646000c0d8000030100003036a810890701c4016a401c3c500700c0ca240401c3e2000a04902018101901c2140c85400800c2c00c070303921404450050100410103555280e83d64000b940364402140141e81410a4010b0f2442030a081c0c0202c8611071042c1d540e0201d0381d801d00104001c640c0d80540f98541007285020003080d084401c606008182003241c000310303100c9a203036100034203503441250b04900c070b2032911180c1607090320006810308045a0107d106c0c482507480c4102d5181e20245503000915a10400044480254010501d9242a800741d10240296a01d071000c9505a1009940882c0c10000c10001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 158217275 1250 158216025 158216027
    0x2190302070804050a0303051c05060a0b09030106172d030306120c090406020306100e01020c01050a1404030303020a021203040c03030509040b0a08010501090e01090b3105070609091407 81
    0x41c21154421500e080c20b0680703500c04030342a5030030741d0400c4011400014040000303003012030360002c0d03044054006108903d40003000c1400c80c0c0742c500c0342e82850300300400d524a01d650203412481c080e0130032811103c0803020503c1919a200c01c0c3c1641c203240c108103030348a0341c00c107410a40e4041c58030b07860308001c44c51070311075005100204d2081d580c5001e0038003409407810810303550b00100f10700803802001c0241e142d080100801c03c1902c8201554420301294509030340d0a43d80218000321180000d0901030340b50406100d040e00c04000c043c0380e454442030000390100c200b64250f0301900d040031140e401c860259080c4198000544000d032400382000320341340c5041001901c160000d18078100c0292010482c800f254000c105141c4164000401907512000180120b072414030903200c01c0807800000740f01d00b1840b9210070880b04d0005d07107007010184906030010789504001c01c0902000d0a4400d91200c030150a00b01241c442e81c1c00e0040e240000c0240340d00080ca020103009415100004641145840e151808 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 158218525 1250 158217275 158217277
    0x20307030b040f0c0b030a0b0102010203090a230105010909050c100e220504031d01020a0b0f06060403020306040602130b0f1812010e16050402040b04060804030c0b0717090102190302 80
    0x441160f038906410100d03c0094001c4062400a0040e030294640720b0038503042c0c1c4026140900e160b80e04580c818070810010002c00034004481d02c0e00322000c0c2402c2c408003801048480300c0140d5007407a56003400000586851981d000410b81400350b03041d6825454448200034400d50350100e0f90300000c44107079030311080d40b030006080003a48520843c8039190608110603403082d55011607040d00072503404000502c40d1281c0054440010100340f02400c1108000d9480032040d44011b0110202c0509110000f0403d840d0b4104440184d5002411140c0070300e824a8104007030740c4005c16010b070030307841010b000032005a90700c281e031000394003400f5031ba003440f5440c4840d105860003c00b81543c07226601c140c4614200b420311038950f06562010180103610042c8104001180c0c03a540300c18055441004100200c2c1d001c00180e40541d0b20a1904014649076401e040f29400c0e05034074041c002004013802e02501540102c50845420030011500c660366843c54255800c0b0f0040700100310040e4104410441c0d4039100c1c0d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 158219775 1250 158218525 158218531
    0xb03070201020d060608090f0d0203040b09300c0904080a05030604060302211605010507080a022b0e090403081605070501060f0f12020d08090d1502190507020307030b 73
    0x310005040c9600b60303c645042c1d8100d40c0c0a5000300c0e03600c500344855000c0600614101200b030314000c02e010802080006d640e842107100e00394142c8408900d4100c641d603003440501e020030a41140696043c02d15256551a1a0040c1d82200e80c2c8034a142030911800c002910502c00d94016a401c0d0905002803803d41d150b5100901c096841541ca05000c401680c43d0942080c0c0c01010404d056100350400c900e4526009017002a8042c8101f20f090400c070701d81c0d0002c12658416405840140c40b0002c400050b854100c5151001c196842c8500113000c03000c1d174404220103488443e9a880c003420303000ca400c2c40010074003510041e00140a600014010300f40c0c4003282c860822443c03428620f0410341ea202c850071a14144c10080003074003004000c01c40d01d00011300203c050712012100084245899000a0303581000c201c2c01011b1007230116440366680c0d92400404012a084001115031b00b1101507004001e5102c0103810112900000030604214841d00c01d49210550140082c600c90341180c0703920440060003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 158221025 1250 158219775 158219777
    0x60e04050604021b031b121603021c0c03090506030f0c0a02120c0604050c150403060506010c0204150e071b0204090501110a03050411010c050c0f01050d090809040e0601030c0b0307 79
    0x130040b0100210351101d0b005030603160380001e984c84104044d0040e031100c149508205040e8805800d25288503100b0b1f00b102d0100044880300f000c108401c4c03900341d081030043c00b60f48883c801c0f6840040c00f00f640240070032092a2003540c410200c60b44400030040301d4002626028140c0c2492000038500350740001c0104055111801164a40c0c1c440c0b24445925074403500c129103464000c001840b00f04001040450104041140d105080219131607111546020702c2c071024168075206c0c2c020902e964000c25050712200c0d006442801041c1c01100c5038040c0008521803a1704c03d803c0080007544c0e183c81100901e4808014088603014007050707400300030207460406403d0300c1c1c65584440c0c5000400c40d90005250020b00c40e00c000c2503030f1a09060800c5034018150910707040c401e90740100b00002e00d011807142424070040391102005448140101c65600401c643c0c01c2da03091820345142c0a102d0705401801c0007100484007440a18001c401007a100c400038030006001d1090040123015101c0000d02840c1d00c0886 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 158222275 1250 158221025 158221027
    0x20c060412050910180e01081209010315030501020714010209060706050a1418210d0504030c05010e030c0705030c100c1b0308090f030601050901140a09050108010203160801060e0405060402 83
    0x400800076407a41c02d004e00c136401041d0b48040041c2c0248600d88002e00030968030101104643c50001650b883d100d1b03080c0585081c01c400a0505200d0f8000d42c031034130883c64000d48a085060301d0785000c5000b503000348000c1d100940c1517074031001071140500883e00b55010240c82181851555502c13800504405000355003150f071104810007401a01c0090b4902c91130304610b20303420542e0403000084c00d045444007410215001c6030103c02c01210003100300c8902d20858800020581d07103d040c1102ca91040d01c0b4001c100d942040ca00345114107001000e46506841e400503106150350b02e038100340d9030340c00075411540c02c2210188411351141c082c9002c48100e50183c2420030002c4501491102c1030000d54008586a00b804243c4c0c0c8641c0c1050380d403d40340d0310300c29402002e15504000c00907800e06814810a960040040c0c1012029110206448010a0903450a01c01540c40703185042c081d4100b152001800f103c0c9010300c03100d0600c9501000e04030340c095117900140c85070036030600015000c014420781d002a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 158223525 1250 158222275 158222287
    0x50d0312050c120f07050708070602071505070905011b0803090718020d050f040c0e0915010e0912040e270a0c060e0420130509040312050a020c06041205 67
    0x40c46004452256210031545907440d0072544030002c650101814019241603500200702d0095008402c031001c031904031101c42d817034505600c1d00002034460308800a103940031110007044805910340007140920303da130701c0b0703004d990340ca54004644030b003502d2020001c0519940c400d400484d4442c03006581002d510000c1d5a0150f0b2990280a240c14000824410060303001410105030309189c03103010b0700001c10704004905400e258540d0355610303555020754456031045071f0102e040950300700580b007135450f08442403108641e56001001e041081c100c0e4081d4060044800013500403c098086500f40c6aa180c00320305141c07111303c030a0307060006400502c0918010240c541081d01010041074280c24481c0681c0c1040c2c40c181031005000c55921440130b4007072414079010091240c0f60360760007001c00401c0209030303480b01c14041d0102101d003001e80c0802d0b0041d074410300b0720090643c4005083c2040814040a01c00c5e5201d40e1080c074100d205004141880b0740065010400042070703102d801c0c0380d40f501c44c58064140701d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 158224775 1250 158223525 158223557
    0x5040b0916170906040c1a0909150d08030402090a05060d030e010203040302090a020912010b06120a0b0616060c02150412021501170f010203042307150c02030f0c0a050d03 75
    0x310143e6880007250300080801c010054010310b10400380201a106000c0c044140d121614103001d00c01d00640704001c2a00010081c2c2c2508541170304a1000800c502c4144102e810b11a000d9402514141c2c00b540a13040007909131403460240030302402c0007801c894258216500d003120144401d041c0e15046010030003000015949540703000303016100c80351005980d0031030103081290903824840001ca00d42d04120700d075a0244e60314800d8581d442c1c1100703900c082d0381d928401c1002c01040101c0724903502442c08581a404102d0b050001d0f0b0300396101c2d42040120b21040b01d810780c1d0f129045444070380b031701011800207000a00c1000c80b804008400740101d40480c03881001403100d5010036081004070784140c1858141c0c0c500c1c10400c0c00684072956008600e1400c09468120740c09000389007074613118915849401d0310700010001c14009117030070452080081c811001c02402641a11802c0e84a48912240e91a01c40c40c042144031080b0001404003182629080c140001c0c10301c806802c5e000d00c103594406007003030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 158226025 1250 158224775 158224817
    0x42c0102090312040503012004260d110706031b0507030e03010603061a0d05060a0519052403010510051201061a041502030313030302161b0f05040b0916 67
    0x41c1c2d203c440c039140c13210b00b0407090508440106030175500c00c5c03090f01c0c0c3c0340300518203800488084c0c5070380402004038000d40e4628841c84a581c99030a2140344945801c2c1c01c04180d00169140e10b002060b42980c45942d40d82408a0a59800b854444165410510007911050156000b4a0101e1190406040c1c813030340e0318000b030308652640d8420344200d500c0751521155000340c2800c40b21203007030484a1084d0b00015407102a95041d00500340b214480d502d00206a281e141a0040c411804480e44203200502d40760009940991414101d0841088075000c003003418541070164910410003410300c0380c88903103464100080710700038150b403880c15503071980c002c90341e040401c004c0703210300301035121140c1d4030381c504040c1910f0304020019100441d00188140150054001440020345806160150711044c200d0a06006404280f400401d9942144c0e00703940e0304450f81c1d2554048a015100d0102a15562014402075552a04488c0c0d4481e0001d40081e500b003540801e03508280b501d62034803c408220700c405111ba2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 158227275 1250 158226025 158226043
    0x141c0b01171006020d1107260303100602010522110a0902120105030f07120b09160e15010504120204200714060901090312020307170109020403020f042c01020903 71
    0x240b1088040038410b0540402058290403c2440c05000c10012241560b45400382070162034490006500b291024075041c24015003000302d880c041d80d030f481c100403849411104007481100f000d5402c01000890b01080d180609203c200b0160445010203000d03680e12008400c1500b0701a881940000c002c0307401d001710b1025003a44d40d0881d18802041d41000101840c04842a42c00c1d6650f90002c401840b140e08914403018810303920107104026030301c0b07010145041108020b00e104640403034404c0000e034118108141c9000d50848a0f01203103400032000111440d2050303004081c4c0d40300161200c107005040070307030042495004c82400f0043d4040726a41c00702081c0e010741c400b50344036445841c0030746495009020303c9801080340380c020400034055981c0544504500380388403160703070740c040001421309000b251805c03600e0f0020f40300c8896a40e15241201d009410a000a87c001c030b4180c80c3c485902c4c10144030707840d00c50003980d0040032043e0906546002d4038002007850703e00d030354080c00011500d4404110081c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 158228525 1250 158227275 158227291
    0xc111002070201081305070302010c0305090916080f28020702090702010504140304031709010c02040507090906090209210f10050115020606130b040608060a020a141c0b0117 76
    0x81c0d0758025000040c82d2601c003a0001c52207903620900c0500040c000074141c0100c2c1d40c2820507080301c150b01c0c141580c45010300b0440c0c5070025400d5082281d05540c09070080020103441c0c0316091591038000d1201441c0c0c204032404000209000c861030114007120110307080c03031405c0802c00b42c90594981c0c041000588291b48910143c0e440e101030000b040120783c40421100c60440082d030405286403600c0239646401d21582244030400100d5181c143d2082c074541c0c40841c4c01a0051045080402c0700520340c100328840d41c1c0700d0a103415408101d4a034240201c1c0c00701840245490f0113100c601041c5903044211040e0213209224800321011816801d0084e12841c40b031117440007641e50701d001c0d41c0d131195985032a0000c0071504440204032103640d0f41c04011001603103a0000048503400c1304081401030103650404a170910840c42005141c2c000c0c1d4000b8240d10780140c3d20520402d01581b200c2c14207011310b0003001c0b160010400c998200c0e2541e41c0c002003100c5814585075143d4540e945d400d4414580650f1508 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 158229775 1250 158228525 158228527
    0x190305010207050c0109061404091d1b03060a0614100306030b0109020309070906051008180328020d050f070602040b0a031a03070f0909050c1801030b0c0a0804060c111002 75
    0x81041da04581203c0c0201070604040d5a1800041c0005901d4071540c00307441d02c115501e4290040c400bc40060b0014601052000c0701c660585503072000500d0209114903170711234862400000e10408441c003c0404513014180031452105668041101c1e140781100e44e03004140d03a46000101050720803460a000300560a001031b03490410203a903505003809038210782c08190502c07000304025150a148000a24094984442c4944a4000c010b02d16403a403514210030340320111320001e18000b4412006000d03030403c3c41070204400034440990310f40c04110300200104105118010511803108000c01c443d40c0308080040c60140c442c1120a50703901711040790000255180080068982101c3c040c10388000c00b100101022458600f01c1d40b0203045502481481c56168071201d01004020402804400402800c0309503551002480d0004d4401c244015117401c01101c0c0410306a654080407103400070100d5407418034984e42d0382c585e04060b10000716034138204130b900701d01002c40a409100301c10407480c40d04009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 158231025 1250 158229775 158229793
    0x5040b040c2c0901241e1202090a150b030601080907230105040506180307061e03090320010218090105281805060418020a030219030501020705 63
    0x240d41c1e05055802030744441c180001c09096401540d44809401c2c0550030089030070b40d48000646024003d00d0035155400300b000301d11400360080c00f001040650310686030f00b0101501402000f001c000c0c1601c113610882070fa007851304000d410a452559444106200003068410750029078040c5903042d940603400406010050080300e6a10441558001e964400101940c50500514208091024194814010421603d641203900030f10a44000b050010b11440e2901000c1d200001d10a40319100300b4440c1c01000c002040150280c4964070701c9149000790008a031400300c006038001c0070b504034107034140101c1008000f0100d241c45900d81102e0400d80001d62502e0790600401224070142014074801d548132401440240c694164400b00720100001d4070391a1000220318400380400c40c4c003d119041c0109980045410654200301e0242070141da007002200c044a03525000300302d8510b002035100c1040c650400141c600780c130f030300c6110340e8507641d020740c14a6603a500d050881e40554400c5805030041d000d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 158232275 1250 158231025 158231033
    0x16150c1812080f040e0601110d020c060901230406030c0203030c070f062c0c010c050a062729010302180402010318031206050303030708160201021b0115060e030705010507060b030105040b04 83
    0xc0301c5680188c10020f21403c201c0c414040d4507000c450403000c0c041c800206441d4202da01c148007803140404c50114040690000340c0760040c05d54414003415000c01d050007030401c8420710000803a4420b030b80080b160717420042103039111009101c48804c2640c07100d0700c03044400320780520000c1d5040e0510b840c00118a10f100e14014040c2014078440d60341c0d040c40420f00544c0081403002c514480d120b54455000105461001e601c0a681940303010500c0c1100d132003006407404c01c00301c4040078803100740404002200302c1403a614000d14243c2404000e420243c8c0070682c642200b040100243c206105040105420180b0840c0304020108040103a0000fa070000240200c080c8511a181c003802c0160091451450542c40244c0141e9001c0e10000b1401307026107452050034030030341c10f603040f040c0c0c00c01c0540c030924190b50740140a0180b115440c83c0703540c4660b1002238183d00a6055a640d4003002c0c0141080c03501d4800196415088100b050380c079981c80703c17160701042e6130038403541d0f101e2445030072440554100b40c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 158233525 1250 158232275 158232287
    0x603011509050307060504141c050f0601140a060c03020f01020f0414060403020d020613120c060807030501080d0e0414040602070309170304120816150c1812080f040e0601 75
    0x80705501a07040135000f4090103600c04119401e81d0f840500e42402c02a018001c100201000c07122180001088400c1c4010050042030300ca01100c03081003181c056907203e4210800ca0b07194000143c0c0d218190788810499280250201140c1c1c5000340162084407000c82215802c0e60f204900b46030808000040501400c0c003940001c0ca2b90700d1050303680c0e601341403c56020030380c801c01e02800a40725000119807e8000b410501410307000d02144140c0440c4044549803000300020103000703100c046a280d10008001c035100e40305941c1280c41c0b02d4000c140c24688984140c13565041c10310003c1e00a9103400c40382100201c8003403c4ca0159101c2e40d030050360340049003001000c00e003403070f000038a03078840c2482d403103c02c0403002090b24240c64109000242c0f00303855181c9000035205a01c0b00c03640090188106400744407000c03035240c126480c16042402a803665080440340d4100c0048a0f000c0c24112440c240105c0340383d0703c090500e080c800c005691411460340d482d1903143c0c01c180c1c880644050035a04001c61568084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 158234775 1250 158233525 158233529
    0x603010c05120402060702030f1516021f021c090c0905061014091f1701050d0206041701060506040e0108070e0f0a05060613121a010e1b0403020603011509 68
    0xc90710500304803904481d11080d4002800117481280013103041d41c15543c3c10300c105101404000c080b01c07032040b100e1a6008400d002103c0c82c540745941c0820007184076001080700010500a2904100d40c1119007144e0002074200c0304d205800c221407000700c400030b541d1714402e51740110b020303c02404017189400b0b1400d058440050005000f1401000260303070f2150050a907140b060741171070f03503e03440d00104000708291200c01050f40d551003030f07918401d102198000c2104d0640b000d110b010740030542c1c1c8410038800060900200250810030802c001c0006a2170f8800c1d0356100c411a0001003000395035040040d035a0381142d08407440720500c030701c010002882c04010050041c115000c002c0390928103e402d082c03842c18004c0140c45125103980008209075a620b04880d000d07461084000031742c5460311812000c03ca0941002c03295119010404080d03a40e568010b64121039025020802c50b85c1c07031851052211042091044680f007060101000696441c1c1c00f03180a082351040c265130754907000700c004118504903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 158236025 1250 158234775 158234777
    0x30513030b04020a33050f070b090706021c030209030a08071a0601030903050f0706140115031805061f0503060f0a0c110c0618040903091503050708010e060301140702060603010c 78
    0x1071100d01c0b8030000b400484101010102c030140c03441791181d54040d200d0384940707a00800800d00004040c401c01c41d1103031985014a0800040f10415a241c40b030982c1d803105200300c0f80440100030800e405889100b5001440601000b80c1910390128030f03036440391100e4020b814105e6400e20765000e69501b40c503124910a1341b0a209180c03c1c0402c01d0940c6000e85144204170360125032400004104062003100e4005540010180740121110360391038917603810645a9440b0f11000909200c900d200c07248009100994064102028180b140c4400c1d0802520b451100d034495000140c022001a082d5020301141d4800c03075070882410751510b000304008049655810802c414402d598245d00441c0e00b000501c0c0d804128250b8015945010041c0c440708403400c0e0b040d0310b582c0181000340c0c4104140d80b25500c4000c490140040f0140307102c4201d815030030340303d003150309400161100c0010000c400034610040c0d040030b000b234000a01a000300c10001c01c01041280d042016074002e1f070511030710f41000d108945019100b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 158237275 1250 158236025 158236049
    0xe07030f0b04050f0a0803040b0a140702011505180c03190c030c080919030f0e04060906090510080606060a110a120206180303010b03070e0901080a03030f06030206090409030513030b04020a 83
    0x2a40c92246c42e01014201030265030103c00054442c541551100201807102c0f2010300c0149400407009018040c0244040003500e540c3c0400203007402c0ca07800307010f4448041d4030130365160396801e00f9000c420380000701011a019500f0700c90b49030307610f80c902c50710010705242d175800b0070f200c04460340241101501402902041e808200d02984041d0700d442c140720a00e50610708503801c02c81d408421148118010350b01a81f02e03141c42030010f10b50000741c1c09041140d00c01042070205a841218600da001960b2140c0c2100b82c2140f00010a1840c20400400c3e910025080c8155005041c40d001403600505250403904080c070803000700c0000b501040040d0303020031502d031403403c03000410400540b240418810707000103a10120100790414024a0700501c2d14001410341c005d00e40e50f4030200e51b6283d250440540100b1701d0055a90002000c50060906980d00900518584034001c418070008200c5240250b040090501c14a0040f640b18618100150302825440c1d0003030401e80100000038555901c50001120 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 158238525 1250 158237275 158237293
    0x406030605030c0907120e0f0d0804050105150a03030f1407080d0e010c020d03150e04080307030b0d0309060e04110a020a05060c07030903030f111f24090e07030f0b04050f 75
    0x648170800c0804810309407030201f090011703090541e191100380c42c8000c840d40a02c6403018045580300c2c08041c469405000284030646810000004081c15000300580100500f00d00b07001090207400004d03024107403071415000200c0b0030080c01e4a1600071107400c071140240028180410303042c9008040d00d50944030b000304001d0411f00c001a40e98400000904113154551a03a46044000c0f551000c00030000348030354805030308d400e14218a460307000f100c00c2c0e400309250130140012810031840440751554185c40320202541800303010384072484100ba030a40d02c40e440741001c1542e00b0400000c7c00c8050016001000303003503881d1a1181c106240108080100b120501c1040b000c80d900c0440c01e01181e8050810000c0c403485d1080440c1c10f448030455075101d5201c0c02628041c0703040655044540005109020458800195010083c584c000403c4190f0039405410a01c81c0441d96032060340001002401c5070400c5559036244181c81020041c03e9408031401c20420042c4601031100900c0034441034081c0c80410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 158239775 1250 158238525 158238527
    0x51911091503160b0d0c03061508071107060818030c0109050f01060e06030d0305062d0a06110601060509130f050109180b0403080402040603140601050a1a09120109080406030605030c0907 82
    0x8000c80f400b19107220348480022400c02d0203a4048c1c1c002c0e003088100041e40c3d11b41c2c01c2024020007815030310100062400000d00c8001040400c0e288240d850710395a850380e0380c4442001c4034492030521401c0813103000400c2030640120092080051403442180a45110614114110708480a030b0b8807040359612140200616130b41c1c08600b01c2c0f401400c604000a890f00e072a03011071020800c00b054400c24031b4000802c1d01003070782c180310580e0381c2c84011290301040c652140c50880f0248907550508280e58000c1c4018000d6074003500c0075201000004c0e014044044c0103800010540d90b0001300c4d007012907961070040c01452014000d10f40010301122005030110000d41d81c1179001e4100510240070092a80e0200c2d0441d030340c50304900f00a40d040036440000c1e0006e2190f00351156402c0c801e181c401c0254040008225007103000c2243d00c0c42020300150b050045460501908892185c100c00040d541c5003203140010f072049001e4405482981e8000441c182003009141c9002030b0201818401e07004d000400c044a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 158241025 1250 158239775 158239777
    0x40204210503040e0103050319031103040f02060d020406030204170a020a0603050a14090c01120501141203040306020309060405010623130b0603011d0a0504051911091503160b 77
    0x140da4000c6000500c00c90a0807400d60003039410051900c0c0d41480000140b01340000030f0441c40e42e11121800c54401c9142d0700343c04a0ba4800c008441d540b03000d00000380490301c1654a881010b0029040501d0843c0440302c000c1240c1c840d4100d01c010981c00301e001d11034900d0141d404100021600300401383d190203900012030444142c42a801092340b118000f810220140d0014500f03034101c2000b5040e00d080c0701c4681516101040c070182d00048050305449000e070624040c49040703d203d111006060507483d4180080d600d40625110024401004000000b0b03030b8520003107104005200c0a84040c0c10b1600c0c06c0b80c01c1d12121350200304400b9503a0804030118440f02908840c841d01280c2801c9094400c118043c068201340d46150740c4824080000206501259054200c0500201e440816640c8d0840d80300100c6400351409809544400401001c2821351040c06040c18000d480300000340580c03800107004910704031941c0c0c0040854006110a03030070200716204030b001a480500390060308000c446482 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 158242275 1250 158241025 158241059
    0x12060d020607141f0b01030b040b130c200d0f080c0a0c02010309050a060203071107030f060c020312090703060e0d08190b09011e05100e04051506120403080105040204 73
    0xc001c41d00100304000002000758006142c940743d13688204ca16800341d128002c00c0340885240c0400d00b01b03d5140c43ea40340c0782c030480120220003846001c0480131440480018840320100c481401511480a91300120380768040d19015610401400d140b000488010b01c0c007000d01284206004001c2d042c0900300503020180c1d00000090700e407030284c10b00540012005084c1854014010b03005194403401480b0b070b0780d0000c600ca03910588400145180032040540d07911903510010b0888403140310381c40b0025400ea04910700c810280c0c8122801c0640109001c400550240d0b5411000d5204420402c1001600d01600c6060303081100a0180b8446a035009066808010143e0841e41e90345500c0c410000804c0e4000c003404000903002d00040d41e1214524201c8040424030000a118801c100255074948500b860580104030741e515030f602c800300000e00028040142080c082e03450910380101c4261940030140000c2800100380c04030b00e086c076040c00380a170340040e0040c50256004002c203102101c900000650 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 158243525 1250 158242275 158242283
    0x2107030b070905040f050a0b0105070203120706020910020d020c0a140d21020c030111091012090602190806100c142d0c0109060905040905070305011112060d020607 72
    0x100740d596040031145520300c2d81050754403030f00d40030020104a42c1035200300d11400e500a0304101c00c1c0a450010748060056181c02903040e805408a60651154034002c1c14445100d2030001d0300345080d41c1c000402241c5540e20140060384070381c84001020798100300305c04c942c1c43c0a9503000841400d0903540c1030311451030744400e802411045d281f035003001520703509000300304c48180300307504030022204000b5200c10898024500c69828860060302d035201030000c035170551400912480d45d9580440060303030780150000c13520001e40d9a0b40b1b0f00c20082026400103010900740541d11042104c483e18010788526009442c003401416102d200136015a084180d015450350452400b5140520b0f40061520700300510008102c0b0041040c2000e58184a071711113205107104c20b10a84030300741c84040044900c01c40d5031040400241501c10200b029003012317800040348600640c15509540d4403500d580d4255240c142261401d400700041402504542c100903d4024004540030b0100c4440345e00001c45901401d40b01070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 158244775 1250 158243525 158243543
    0xa14070c050f030a0c08011401080102030c09090723030727090908131202090a0b0d080906070b04080405030f12070b070c050d020109060f0203090a08090103180c05210703 75
    0x903603076410011a001c459001d01c00031211741d100d8540c64041c011804034005010724110010945040600a07280b017214035680c0700b800c0405d5101002610340e0041c102c441400076410250286280a010909803482c401c4035440da6414008802082140f811418125100e01c02141c0d07451004840070b12421100c00b1040031545185a017007200c1284540034100b40004620400080c5032210101036803c032900854031741d20b090b5030ba01c48040c1034039000440380394051495502c0340c000aa054000e00305040c00030301402c4c205800341d0b8864800c500c00303440544076280c01040030421450308100d0b005c02201810040e10007014407200c10001406a800003c01e0304d10b00c0700008048a00c291402d441450b0424106e407403554421034064000c01041c030054400301e050008160341c106c118021240079030789a00003041c2101c00c0f521504200d400029071681050340b51520030100052081880080324080e8000d404c1d520324200401041e288a40084076030340d840c0214490001c1c0000c25a1800c0340c0d0002985 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 158246025 1250 158244775 158244799
    0x30309090a0f0b0603040609060e0a0b011a0408030309071a0f07060207080702030307140715230405040f020c060609040c090c03020d230f0603072312030a14070c05 72
    0xb1400383c040d014038107811080101c200401c0c8140c2d500a540f03864055841048a2610107681d40d445484140006d803085030024010440140c04080c46002c24107410000c9090de03486581060540d0300584da000005c3d800400c050003a0312682407103800031428170511914010840c1140b410a0240070030140c0380303540c0030841030140328000040701c1c01c41c0c2d8000c090702d94501d00d0745010000502d0310b041800092080c0341d0003050000c00c400c42c81003162400e844680c0b234010020640100d081c440e07515a000010240400581512203016100d06401d00c21005a01c0d0344803001100c2c41c0020040016118440f45010700020916a58422017038800c000000300f21041a0b9000381c0191240e252024417080c6014007401c46440d01454442903c60007500b130203c03039103c00864200c2e80c030003607400c0c513499000038008015003690800d88803110080b51742801e807800d000c1c100080301c4d42603084519401d9000000c66445480e44200e00142c0182910040303800d01513161581d00e080155401100c2c0542c0f000504 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 158247275 1250 158246025 158246051
    0xf06010815010e0f06040609170105060f1908010c02030c10050c03040f06060b0403030e03160810020c0111040b0a080109061503050613062402030c0a110114040602010606080105030309090a 83
    0x244c40950030300608260340d215910358009141424500c141c03450081d00042c004a500810f001c0d0301d015000090048c40d10a800004105001c02d4115480c0c807890f000c1c0400085102003805540d40d00e9030340d03030060b43d00d130340304202c1703e60500c4910b5200c241000d2403e030406c00c10307240301400d80390440d422078001014440d86141035001046550001103449001003000030415a001000c8240d00c401501602c008003da0441c5450b5031096020b40d03c0150048070210400c0d4406174060441c00554074000324404164043c2c1500c07642c4140c102d103081600008150940a0300071031080c0c01072020580410455140c10b0a07031315022126040c000403d030300c48020808135621543c0d1083c0c00c0a4500040026980c3e811a9801d070100080150000c000d0200c40741e04654000300c19241446041d0000d05185070266032a103041c0210f14040e2414032a92400041100100c0e0300600301811003500000b84103800d190010b040840705901c020302c41d1b44108008120380d00c4000481d50040040b002c082221360203a40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 158248525 1250 158247275 158247289
    0x203122a040f141903060216200a050109030305070f0c0e090a050c0a06080105060c030415031416021e01060810061503050f04030c17030901050f06010815010e 70
    0x1420400308804140450b03042c0c0188008400c49035900b0b41900141c01200600c00c4561005082c0c500c1c010f401103040000c03405c00d400800e14645044c8804511420654455044c204220196000341e031400c01003e5442c10086038440150009007000400c40d851540c1c01040d9200d034071401030590568405007410012031003e0070300900301000442c0c0e01c600c9c0400300c403603454140c4801550a442001d28813002800c203954080c09640c0580c0d20b26002d6800c06003031080f240d002c400360f1241803204210000e018034801e075540a43d500243d6011070b040080c071841800710341014009042098040303010400050300007540140c03c4005c10a40c1a0100382181c2003401000e00354810300c1180240031a04c01868151390110003034684458800d1410000000110b0840b2421584108c0c030f00c0412000c180424001e0781490001c078030881c0d449040ca0134200d51074505400680e00076003582e45a80500c0701080d900c1d9012a407002d000c0c42d107000b0901d0895000c00c040b05031000502c0c14015020294206038a50360 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 158249775 1250 158248525 158248591
    0x9060604030f03032a18060507060b0621011509050f04050907030c08010c03050a0203070504030f06091a040b060f03070603090804050a0303050c06150a03060c031b020309040c020312 80
    0x41031808803c8101c281d1240c980b24170b01009001404460588603c5c580d00c0c01c002054803541d076210382c100922640c51400030401040050361050040c0086408102e4112004030204000d003030030303460703545420713120021079400701440c00034000801018002a2103242030300054020456000c40c40340c682c60521410910b8540001d4448100080d020a0f030180c1500102100300310766404110507941c00b00c0b80012400f050b24041c00107101007100300082101c00e041000018000d00f4001040043da541e040c2030b843e00d07110007075503402c6000c08000500c006000446d51000c0c00b900d416040035a800b0010340c40f12101c0c004c0509140da10344041c814040c04000340c8000e028040c290840203602c0c0e05018000d500070207810360030392150a00040116411103040b6141807000380410580d2800d40c1c1c0c5400103003200711078000030160b43e84511083d9080c00340400c05086400d402646e076544258045c0700540b4004031745502958420000004682d8844000d00c3d0b02c400b0305014450040580a42c0c001402024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 158251025 1250 158249775 158249801
    0x40905010e0303061c020603040f080408010c12060b07230a150b09130c03061e0f1e0204030213020f210105010e04050408160809040e06011409060604030f0303 70
    0x414881d460072000040118002c08003104c0e00f66803030300903072981c0ba150050040000c0d00100240081030001d20010300185145110f03191071070800c0d803104c040ca8211400354a0440c006a042002c420f91915103104560140102401c40341c502401916050740c80d184109030350054292000ca03d900711407040c0700e4001415800184001200c10000b07100e0b020309140c6024a01c50311480c00800d1248880100701c00c40c10307502407107100c511495034130f805004160550700070900000315403440344002c8091042e45402c0e000f0280000c0c8a60000c0724041001c45245156010540f04010501c050703559825012452603041c00701680d0340702030300c6c620758640c0611014001d2076500d20050f110071580301807040381030b40c80030307a40c40d18058000410441620390945011b00103000421001015000c0803d5004015028510b41850803200c5400b00301110005090001160007034801405003038003000400d0602a0202c54684090030030400107400e42c490b42c40001d00328011245a0000c060180e048600500b801c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 158252275 1250 158251025 158251031
    0x909060902040905060102150c251b090606050909060604030606030b0f0703020304030e040513020a082a0f1e090a05010905130c06050a140a020102071506080606010503040204090501 80
    0xe1984860003a411500541d400241001c001031030ba9480001d100c5521441c0900907661a06d5144104504d03500c802c2d40e4130881c145c030000764040f003d40451f100030000e215400140c410581c0b4042c400715a4980d030000b010f883d007001020865030741d00000f5034280d0310040315513412589a03140041c01601c6160b10003407207607003840070000500100750411442000a0106081d081d55810000c8040b0300c01114010041141e50241e24a98180f82d4402548500726403007004041856030002354041159521150070340c0e006d4024640810444d03403040d100014011021403c9079155800180e1420111214a00850070306551070762050307440c50310681b4250040c0c00000d05061500e001d002a02c424000c00d90b4142c00c290111f16140084941c6090180c4c12200a00c11941400d104940b9940500540d5040150100c4a801c011080c80000c000580182d00016590501c514205122101415600e07040d1458940200305000002c244254410802d1a083e5582c1d611440020001c016042c000380c8250320b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 158253525 1250 158252275 158252279
    0x50c070806090715030c080a1a040e061b1207140d020c0102030f130c03031d06041409060105031e06011709060105010306050402070320030c12031006030509030910090906 75
    0x800454400c0548000c100d61441404d4500415001e841d011031342100041c0318200054050303941c2d42e02c14402d4240c1402404414400c10f00002d040d602c5101c1d21002c80e401c080f0034007010b411404c401100020702c3c03038080b6003040c40020080c3e41001d401020785040c0410448150300040b03551003251005044560115211803605e0b617854001e4204440503041e03607189401044c2043c2c010029003556503800720305c5041e80740c10b503a012208101c2411030030601c01c46050400d1a07503581c04000e0070250001101411815241d60708100080034043c05003818800b003003040c004030081000044804c1030700280c1204081c0c49000040741e20b0300d0301b003006007070043c010310601000307075804a122812036100b641c2c180000350303c84041100701c0c0328181004000c204082d10703254024a0200e18280701080d50b006890910342d02041c403d04040780302c0e0848111010002c01c203d540090303441a02c000d4022880c04200529282100030b41c0c0780702e041000e5201d0001c03008e050000070b01c506214006000742c18001e0003260303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 158254775 1250 158253525 158253541
    0x50706050304032a200a090509010605040e0604030807090e0a0b03010c0e0d1b09051e0f0f0c0706200705122d0d05071e020c0102030a050c070806 64
    0x7400503035044000503198128007446801036110401c0c00c3c00e84240f0109240391950f9410b446502c864503200c030000c507071030845140f0740e01d10080034000c1210480104641c5446c0c0c2e141407c503400d0b508510701c0f0f9442c280540301c100c0000284a40d21662504242c6040c1c1c95a80f010f41d804042540041d2581441030100b14034111543c000d1444c0390400e038002e00481c00905800d94500704090035031074005403d15190004201548080515900010b0104130002c2e107035180e04041c1da42c11170320b041c1c1c440c2c0000c0c01b071240644078814040d4010b1844448400c030b424050040b40d40400090f0107186110800304141041c00f0190b4040001c03208a03064000700800183c60110481e04900415074180c05840c0c4482c100707141035070803a040450000b24408408541b401f0588850b005134815102c149818007422244026a20030306004241e6070700c0c1e503035110b90300d00c05403010112409008011504481400c1c3c4c0a640c00105941e68049641003c54884407441c07185d80c94004240d0211586210f81001c3c4469a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 158256025 1250 158254775 158254777
    0x141c0504060e0c090103030f120f020c0105011a0913020d020c0a0605150603041205030910090f0605130507030209060f0d0c15050c030306012a14010507030902061903060305070605 79
    0x3803031002c1030324004050030b8100031041c8400d02c001750100d144410025003013071150000c0c1a100a406800249803c49010b12404030380051481e070650369510030041c041440d00c0e41001c01e00c000c100d4615482c000300d00c004105840c0300043d800c10640d0f004107803a03030301024940503160400c2d04035085490101590500c2005410151800c0b5880500aa03540ba01414520b044901c02d0b40c124500504600790076408640c02d50000345880d21500404048240204181c0107445680d4000c6c02d100700e00d4801410041c0880d400a03180200802001540383c00180003c40d521003120380496195505a450b54003088843c6140110a41d11070900a0340004024202d50601c05540201450194001e1550004e403030030301c11403500c2e809a6200f4400981550311407180200460943c4481c20881120181c03010011681d0110458030285841500c0440007030034031401c1d9000c64149818040e00c68541c01040b076610a00110281228100000885542c0207800c104002c560180c11104440e1f60380300d004003d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 158257275 1250 158256025 158256041
    0x1103070c231f03050c07030507110d0b01080c010810050d0201140c030c0f0f0303010303091202040f0c0507020f010e06090111030708160c0602070b0d0905010608191110141c050406 79
    0xb03e49003101040c030301c800748419a003041740c5c50789030039107805815201e038006c41c0c14905007103500000440c80c440c0000c06001c03c440c0201606e100800081c0030403000506518402003040b042000542c80411140d42c4100509100c4e40c1c0a00703181203840907240080c003092080640109051100041040c000740e00010f00e1030a4610860940d484c801030300c00c18079103912003880090001890b2041c1802080c5241c0040611148010000280d82000f01d0900f0140c0720185c810340080348000c554202507041c01042c60144100918101b0b050013142c40c000b6241d03000b010034042c1001204215420010410411645503a0304880b00d40d4603007060521101c0c204c1e612920407100e50500090000d92070b800095500c050744c1280710785a082580341d07003d9000400d01d0410903200356482d9031001070000300070300038413031b030040076a616410820031800c0c60200307000a140c80354013520300c3c007180044107503200c541e80d0701c04854030448541d1110440c0419850100305814850054500b40c01c1c4800c0203015844828 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 158258525 1250 158257275 158257277
    0x7150b0a08150a0b1503130c0909050d02070303140903030c0f03070c14060d0b0303130806091513240203010909060606030902030a02090a2a1103070c231f 68
    0x2050b03986918040075071303042c01826078004a1403515520108441e20141d81d0182104440d04001d82c15515005d204c3d240550228980560341c820441c240082030201441c25640d50000303040851850354002c0203450b1003403a020301844041141c00c0d065070180100c0d00c5d4408000300700c4505001e5201c0c1075450350b108031000c80340c91449810005400702580714000d00d0002c0142014200200541250301030158000783d10b5260100b00113403c0d25005d4070141402804005000f09144e14081c403415140540c150030744500540101c0c1040096540955041030450703006c00c0155040f460070f44013441200350074005140c1e003400400041204002c1da401542c4a600405082c00301b42e68a041c103a045608805019403d0740140c100d900242c180700c0c00d6a50420035a050003d030040720901008104211801c00700c1c1c030703086110b00c031172a07560784100400240240310000d10b180c105c80ba92124032040003807042032101c1c2110101c541c0c04e401c10304205c440c240350140062041101c4400846024803070580060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 158259775 1250 158258525 158258563
    0x15061c060512121e1305092a0702031e06070e0f0f01030902030c0a030305070203010e010c05071407050d1505010603051b0c0f0a03020703060c05070807150b0a08 71
    0x5007034030b0601c121242880d1584060052002d140f080c8501e1680301c55210015084000e0a407410b40050380f000308010124a2545482d140c14441003001040010f080e0740c119811800f05810030031001150f03100d444280b00008c13550744400d0301c007280c2428a851040b03038140790961400d02c2a91408142d0342d00c504000d540d510484518502040002481042d88581000d1010100078003075009510031004c840c001000c071000c0009841c0000c130440384030f8000300c2c00108041180f408504003401000003040004000f03200104004100030001e005110011b0003c05c646401d54050050901c0300402800e030241000034400c84134200800840035180c44101e19500c4c00f0000689617100340304003070040c5030400e00703402410440715416482d900440000300c068084d06080034002c0004100000b140c900c41e4001c1e1030030500e94105034040340e000740710344801d1110030803514001441c400b085684035640040a00322071050952060014030140502907003014042c1804205d510b00040c0420300710384114012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 158261025 1250 158259775 158259779
    0x1302040e061b03010b0301090e01090804080d03060b0a020a020d06020c070e0610180605180a061e020303010315090f050d0315050f030a0b0405100213030212030c1515061c06 76
    0x42c105520092240799101e940030300040c00b4190858106400c1c405aa00010552071815160390ba40ca0f4802da02c401b2056200b0356151044580500a000080240e000114141200d20201a485495145000744502e034900e4056007007040e60741c15280111174007800c40d02030907102c0600c4d0326204801d80c0d40504c00d44a01c9801060346100b1268000001407031825a40c066181040c1510140c01200c018040c81c0c030420140c20154451035040c400400c07150361800078070303018031140c20341648101c3d44407021500b04100500c04512030600152007083c070103000040c038201508110f2a02c062003030b8001c00d01d000780300345e0364200b035030641040070070b000380144441d0520303078810401031a002020081a01030308090140b0010a0003c0102ca5025010380c041c0d9280380700d42c280c035004aa008100c00000d101800c8401d0040d81444038090a1a4680b44c0003585004a0352132482d070344004418480c00035130100d07000103081c10341031241102c000c14050580e82d2106650084000005944040084058941400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 158262275 1250 158261025 158261071
    0x907051213060b100f2303090304090608031219060b0309010c110d0c0f060219020718050121080c01020d0f0507020c090705220b0904061a121302040e06 67
    0x6102c0c18491035894000c0381500c82c0c00265070f00155822034441c6c0070a4038540445600841d0000c40c8103030709071401b45a0303d0f81803c43c40f004543c43c07500803a401e50300600600d90309101d1450215008a40c17000d0540452120400301400341c8282e4218500814000c414080b030301c0015004802c0304901c58403803e9502c0201788207155140144156071000403158445203002c115201d007581d012600614016207488a54141c00d8048000d4610704401030f072101400b0091080c004c4d1100c09441000d44081c4030a514080d021040c402d408101e501840300304c02080740402007800300302c44a10201c40000e6480e204000c241e04010100d106450310f0480c10480040e00d6203102240c01480c80c140140500500c1d110a50200e616030080c01d5003d00e90b82c0a010007401c86040300c02003100504415038540d0356040c003c010f000c2503506551015007540031860081d295002014255258900c0040d141402965400d503d59220207800030041d41141c5040c034500d0600502184461090403845020740290071a100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 158263525 1250 158262275 158262289
    0xc12100e030c030706020c070f06080405061506030103020f0a032004060e0112031112161208040c06050a03020f13170303190b0f12010209040b01020a0506060907051213060b 76
    0x1c40340303810410141001921603405887c201051100f12206941c88140d16110303812030750030150100c2d14000420081000c1080950341c001c11640700f140c801e440b4040840d10b10301041c04000d200c0e000c0c40403404402c0d12002c1e4904001c540200c0c0402401d1410109440390400368142a4091810300b00302061790700800764607034101c42207810f1262030709020703442c22985492800b241407407d0007400e0500c202c50000c0005009042606c030070f100d231421014580042c40c90103500620044c01313a42c80810002c1144011904c01b11099400c1c10f9688d440030341e030300b10002d1103000c00b44240a44003058101c046940680b80d0010b541c454002e1811482400158070b80d40e000440b0b41c0c208206027000c000ba440c44254200000040d17002e014480c0824030380000400b40a4110b18007200745c2e5012513001d84070710b01409603649011007800503044030a12500c030035403241802400b4900800d940800f20704030521400483d0000b4480d2040344080e400c00c3c0310144550707100ca0209840b9241803200340000f80c54188 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 158264775 1250 158263525 158263537
    0x103060302130902192301030b301c030501050603041e0804170114060a030302062e08060403180e040210051606050609090105011d090c12100e03 64
    0x10b00ea8501ca10281003200081c1c410098200c1c0c00140c041024444071070b5480c1840042e20451940307050404803079076213400c07440c11030031118100340c2002c4840c078203074071880b000011081210a920004000c0c0034001c1584910a186509880c801c1f084000c1950851200c0c802598025540900850b660360040049a01094801034101d151000007521f068004221400780c4070300c50100e00d410030f60344002d00340c501c0060081c000810b94448420001075412082c0c1c2c0b030351250302221020400350864400a40e0b5240c010000e41010164070610105003051000000f1002c83c01e0308521140758035850705984070b54040c0d8088021070321541c6500c3d4071944801c00003043e01d0304101c0080c0700c0c1c3d6070391302000429005207a0503014080100814200c0c0707010140d140a802e40144c01c045140d050400c2030045155000308a441e0603407508005208165246000d6a040c100c5810105100d8607002c21850034808100c0080d9442400b0102da898204800f05928a01819251040040d00080d820381c035120300c908 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 158266025 1250 158264775 158264779
    0x316120b0907081b0307120311100c020c011b0206030403020304030b0a02040302060a031e02030c0a02101505010c0804090609050610030c050307120b0604060203040e0a06030b1513110d0b0103060302 87
    0x8910391240d00c00b4090380e488000c0100400b1103141b180d580d0000c00c048004e2000680c0090f5401c030300c6020002c0100113a1703042d0804040c0c10001c080c80894003d4485840540701410060303090642120508007d111922646d0014034099581c1070a144c06540c0f544607110071540700e00b0100010710500c0f42c40c8295011260041c09980c500b440c2c01d1012801815540c043e00e51340391700c004c03480120301010f1014611413610302501720360310404004007038a040301d0071881c1c0748500c0c1400d4440040341c4900c103850080760000c0c03c086183c05075070301d4078411a02980d001001c00620b442070000700d100050300428040c110603a180030b56166100070403010b42d02100000d40100d10200045640b8500c5200b0190003800d00c0e0340001180540100002d032103500c5a4000700069102242c18001d150190b101070303801920752482000301c1807559488005131540240005a64400140ca003405510f4580c1c80e41001c1c2e4041c40200050404111481402d4005204006495103004901080b9500074840d074000d0341d0700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 158267275 1250 158266025 158266033
    0x402120403081e062101051513110d09030c200a1d01031b0f0e06011701181e0903031d0a05060a0504051203010605040603200d0504020316120b090708 66
    0x4034001d1024585448240400c0317500c0d1070ba2600e0700c3c40000c0c41000d00074843d19003c142100c9561041028450108100448491401c021500481045011281d2451404602048405035800d00b541d40403d6590301500e03191940c5880010680280004030001904940e0301484940b540e009032002c1d2403064100c210401124018400f081e59448281906103504540c4c221544d00da03814880250015445651104d036000c2c03c0c42110740c0c1040c043c0302d85d949a90301d0a20030350726103195558400c072106a4145020b81e00c40c46040f10240000081544d100c4070070782803100030b41c5403800400518150340060b800303400d0300caa050f00c000300c086200181c10703130403000a0204d91202e5071403400809010b4022215481940500081d5500943c0a98003c140c2ca0700e0f010b8840c1c0c0342040190550324607860112030980da5000f14041c01d0040c400f51004000c410000051980d42d900c082494040c0c00c05007841b04000ba22800242a003d0307a034624801c51040d0581c0d01c2d20f0325003642d810794842c201e0150a0440d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 158268525 1250 158267275 158267281
    0x903020a0201080a0608100207140a02282301030b031c030e071a04080606010c080a05032a040915061e0216060807110607051e090402120403081e 64
    0x3c407030f02419402518903400010416501c1c0300b02480d019107001c45032205600405d4000c1486010307107015a20b8400f010183c070200c140c0364000b59020303808000301e24101103031100455001c17103030114040180071151045091202c0f036000d910b9440f21454400e60000c0c2c00c000901c4428107020650f10400c0c05005924000103c2c012810b80c0500703014844241d40744524540040d2640b446207500280707000d180511031740d03141040100d40c200b40c0c0081445052280c1001c45100240c60300d000ca4002c00e005260994a80e15110180e5030054513248600d51a1142940c0040100d80218000c0c001c4400c0994108505420452102103500280c0b044801250300d200c6201e00b0307020010074800c256030136807040e90304c1780d5200c40d81140f420040d50400340000d000f28040000198005806400f150620750081c035007841e200000403e01e06c02c040e640d00c01c1440345059581c4d4a00072806035082540c000300305540310380b501c2c6840c18171500d04850650000d041e40380411603201040700510000c050380d4800000c1a5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 158269775 1250 158268525 158268527
    0x130306052809060209030a08090910180b0d060603110f04060302090117100e0a03080705070b0105060a020a290f070206060d0c05031e0106090b090a0e1f0b130903020a0201 75
    0xc040b100c41511096002c0050121565003032080c0c074002845811041e89a4041c80c0c14000344c0600180b014100d0181000e06100c0d889540342e218210b4031008401007541e03294500402c0200e210244014856070510402004200c10a0007100d0f07002e5060750010007016030a400c21003034500c4c9102c0039400a2100d4010312109000c0c0300764071240400ea0003100c00d8141d07401c00c3c0104541c2c10501448298000e41e030101c0401d544141019001000d910300503003002c20304e03124902040c00c103128047c03040d44002000c62040e802403000c100c1c072a41009040c2e02204e420320300c60041007100300c2010b054141c1e140008034581413609445000302a030341c5c000d04850341c50005100340d02009400907034545058600010b5142d0341000202404174ac8845c038450a030043c0307100903007541c5031034100450190400464205649461100f80d80c8082e070340201080b4100c6602d492810100c5441000504250194203110b0b12140c40c1c01509020b2015100070400c0d43c007e640001c2154280c41000740140c00244101c4055 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 158271025 1250 158269775 158269781
    0xb04021315031812030506060711010f022d011b02070e060a1715070e030c0d020409050706050318030301050109060c21030b0a0e0402090402150904021303060528 71
    0x10841c181400654501e01120040d4206400c0c68221204034400305101e8020340e1500415800820540f01d00b802d00d0308580d00c084007606800391803410098171120b110f0b240340c420400803001042491082884403e04485410541d114040107811503081070140340c1c3e034a1800b0f02c0c4611041d11903004d040c40c0c5042003801c001c040d0000c0d10f0103a0007203811001140c260484240e0040400c9910000d120110900109070712a500041c02c00003845003240b503400d20342d100400d25407034100f41240c10119120843c030002d00240f01c501805480e6202e42400401c00d590880b0065020b0144000b4034102d110202c501e207503480c03009020b56400200301d480c0030400700d8060880205054420780d01844040b01140b50383c3d040c2c0d00300d0321007200000e8440c0c01c20842401d05c920703039070081c1500c5451200e9a203402c0c2c000c04d143c3d10000c1e000a004200d040305070340305810b0f0310080e607000e0381c0010401c9d580e80494041c02c0f8214001400f05603120303413511020030308464554a4200d40c10a04400b4940440d00a410400003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 158272275 1250 158271025 158271059
    0x6030d051c02040e0601021b03030a0c061121130302070b032706010906050901080309060c07030b07020a12050901230c03030c0409050f190216020913060b040213 71
    0x340204007080721031114100d001901c0506000d80b40c074100c03441d10b03600080c640303d9190030004902c820104903d0f4184c4011045a06101c194200041c0c0340d05c0b03604d0728100600d02040d081c03500b4400400d1000c408900f0042012446030381c2d58900c000d5840d6051110a5000071141c01409640205010080541540040c0d6400740414552070b5186940405078484003500540b002e400c4c0e002900180320300200391180f5400340006682c0941039604104655076079200b00c80c0482e00c1002d0100c1c0240070300004001c060051680b1192221160507c440042c0d0f41d1400d03110b003141d0010030b000c03900300300d01d100d5419990343c0c0c4016555064000c019810072035022280c0c0e400c0d22140c0b841004501c1003001c081000714020300200208aa44c0c40c580880601203904c06040c1c17071190380c107500a0000d952031120380c0380d8505402450043e503651030f1802d03128a0b40d1203017100a400950000400c00418a04198002c030b803130281505102c26031440c0104030407072180c000168400b24070f4150900000071100d00d9402c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 158273381 1106 158272275 158272297
    0x4051005090c070f0c080d02010c1e0e400c0203030f060301020405040c02010903020c04060f2c010f1403010b0a0b0a020a1205040305060f06030d05 65
    0x41c6400c00606680baa5000c045a100305204003441000100c40d8016003007079040741d40e0128203895072903140c5440095443c260066442c58010406445075a11448220814008810b425140800400c2d5040c2c0c00c040300124025202401800d052038140911400460707201030102040048560213031041001800c000f44283c2560300002a240c001c100341c00808460794031100428028040c0f94002e660150030020038044064040d48080e0340305020b603092f00e403608520380c1800250351241c803408d800c1d410351890400c0204500c610340d0300078404034000f00c00c0361109480b20400050013a04440f1229500c1c0c80d0402520741403103503403001907400390002d200c41031820001500c540010320900c00800e0000400f01c608078070074811224159400200c42845940340d94000f042d40d0403e0204480c0d5209080208408261038013402e849070000900a0440c05130b088821186c1350400c08080e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 158093525 158273381 := by
  have h0 := BRFrame.cov_init 158093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 158093525 ≤ n) (h2 : n < 158273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
