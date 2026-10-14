-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3116
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:42:23.308609+00:00
-- url     : https://prove2.me/submissions/d6b70933-7d5c-4539-85c3-4de1dc6d0b02

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 560251798 ≤ n < 560431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 560253048 1250 560251798 560251807
    0x61e0816030c02010605190311030721030915020d020f010c1704020a120b0403030f020a0f08061c031706030f0304291b06331306060203041403030906 66
    0x18040e0344189003401e107030310020481d1031b04c80c000301d12000c0001c00f00012600c00500e042060203940c08414004420032409802940d2078902518414070400d45c1056120b0000c1070744004050140d0300c80e0700103000011800c103072541c003802c020f511240000003000250098040d0740410b10410f100300c1301d280303c55480e19040352041001041d981e40005000720f03000390072040080340d40e50000c108841440c2c030030f079500c0c101803516190090a8400c0046280801801404100040fa41080a00c0c2d0269494074001445641d1980000c02401b210060090f84002c208401401d0560040c03503100e900420134000e144580320035052561390907007001007280e2600180402e00c000c0500c4511540480c80210a80c6540ca59051418999038041600007140c880c080c00400c203010030501c94544e0042a04810100c901060b044103240403081d084954141c01807140e282109644000b5800c1010314080401c00c1025100d860207582c0360703c180598811503066019120312071500004449003004040c001c00d080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 560254298 1250 560253048 560253091
    0x1140d0504061428050705040e09010b041d061f1a040f0909050d0801240512072616050f07140d120204080c150d06061e08 54
    0x10500a001200d15640325110b103001c14400d008041c0c02811101130f07a0841c02c2c2c038990109190440855004811802c0804024803242c00105603800c0783d254003045d41d41507682039031550050100408072544580351103004102c00f030440041c8100e850003013003161865111a000c145040810240210074200103103010304c00000c0e030054809440c50700303004a501b0240c0311198882c00c01060f8001c2e00401c2d94442005052240401071291401110b040100c8070b54142454101d400600040050f42545c254100070501c13403040c8101c403880001588000141d04010034002c004030300c580d580c800700410325140c10101c0c0080303400040c012001e1990380c08031f0000594060360607400812010810301028042d41e0040340b0b504000d07002090484005d0542403510980203042c900c10102d00580e0240705000500120707100044040c010201295089840f030307004645120b0621681403031601e00c83c01c0000001e0b0b183e802807960780190040055030040303486080307001c849582c0b04803640310804018140e600e00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 560255548 1250 560254298 560254301
    0x213061d120a030c02150c060f0a050402010e09060a0f0e06011103030f010e132301110a020606040f1107080c1c0f142110172a0d0501021801140d 64
    0x84291000c0c001c0c2680c1c00a1400d0706d0035503000040c121169400c60420000a0740c075000c1c00d9a4040110790041000d401d250b00000d004243e000c401c0d9026414490205a46039240c015610003850140d21040800380c072a9030b0b40c0e00c100c07404c0e0f07a418045100c0002c01c2e0b91100020054074401c241c1408522510b030303e0509406981e90010341488000d07081003d48402041d00a54000c0c0000e2801c40308042801441134080e0855040d01146030400318103100600c2c80a030301041c0c0d1078120700100d0700415070025a0701da200080c901c4003186044404005148410401810003602011140d03c3c280c5030800014100700d43c80510744144080001d020302001e00c2c1c054007589040000c942030007403c505001d50340d8120010030340d1800c400c699081c40c0c0b00c20000e1315456681110084c082036080000810031036212555160101d413a11074503401801451000c0000c40b14036280180f0004080c00216038003401d21500030360010340c58103003e11281d40030300700c036500420304490b1000740848110303d40510f14030b1160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 560256798 1250 560255548 560255567
    0xa03180f09020405150715182a0503060c0a031a0402070b09010c080f06240a020703051e120a0309080703081509040c09020a0e0a0e070f0807050405130213061d120a03 73
    0x81c0130080d114240ca021419114041c9000381d0304180c818011300a50001d180310303142d83c0d8007041c4283e1021080101003131101017910148211030a011aa50900115901d00c1c40202030550d07401c1407000c40d81030705110140002d140510521340c020000100c803454120395a0317408440d00f00c040101200441c800381484408034811004a801c4601680e00300d4031b9061582e44410354503001640400818411f00106011400d80d144010000d640d800da0015400c0d608c64440c40d50f01c0502d030002007104840e482c002e410113104141e215410950300c00302e61502526000064445525280194020300c601d424454889409117801140342e050542c2342c0b91843c806540410000b104002c03510300a4002e907211102031501500045640c1d800901e402c0d40020603181a8103c2602000300d520300b03111041c0e421004580580f4401d90300c00c482081c1000242d4040c6c860303181918840440c01c2c10015040d5804060203620350f40c40c41c0299407990005003004124928013a003000c4607005200080000b0340200d4888 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 560258048 1250 560256798 560256821
    0x1c05041e0201120510140609030d080603031b010518010903080103080d06030501020c010203090d09060903080d140a061403240a0e1207110409050a03180f09020405150715 75
    0x4401a140354011340c0c10076580d400d0484001039052100c0c04180c150003c08410982c1c0d1642480b40500001c1d6071145c082c0a03000900414901040327841d1401d0085412000d03150702c0d141280e04c1c880900a0007803004440b50583c22180d0720100c48110340600404542c0c2d6010395501d4034503401d54440f034605901032010f40d901240d0358070000000440a0003c0d001c003807884c000050722803800149a0781486501e510701d108202c0e1000381444259080001e0350242c03600020655101d01c0f03484400001000d003c03151455039100d134400c0090502c1c2541240090350745d9503040074052103410080c19652010703501d40a04400c0d004030341d94081404211142d41c01190100b0200d503140c50328007181d0031709200d070f00414043d0100140d140148021021081b81ca120260350404c61400c079138445039259002610004c0c200032521503084150240d950b12040503242c11825031101a66a08041000394054440d503400790a441131403824804040c000d4401c0c1d2074001000d40c036042c07143c006900041c445c15056 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 560259298 1250 560258048 560258057
    0x130b0c0408010c02030301031a041e020103111218030301061b020a050409030f08100608070e0102160b04180b090705130b0d1e09120e0a08030a02031c05041e0201 71
    0x520000c0074000d0b03516400c03a50b0007079030342c1f5411810300c0130340c0210040704101d00c00e940038288030026401d0195201c802c000c9040b906104000c1e840101d01925400161407007482c004285444080c52001a8502403408464006400c000031020152a0b0101740300300000700b52094094400e030b10a0902c1c1050491005003201d14054490000904507402000181d0000d01c01c00700c031880d41c0b03130015201604007155242e1500c14601c7c04100414003d0020401810002c803841c4800e0164002c12130b10b2038240394019221031050720f41960080e207402500c9003002d61511041c1425070030b11113101d09070030540090966506603581102c10344003940103c420101c2e4512505002a2042d460800b40c2000407140c000482c808078819112200700b551166100b04031850070361030000164662814252200c81030404001400003103000900742d18690b840380d038503400002a41c0d25036a90210040108140300308032002d010b0b0f12409201c04844084400404003c040c0c00c01411500101c030040c050301e40705140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 560260548 1250 560259298 560259307
    0x10203040b04030b0f011e1a070204060e0a15081b030307140616020309030607030b0609060327190b3103030b15040e040302280c0608130b0c 62
    0x501c0340d082d03105078419a2542465428041c41ca1040c04519004151040b002c5031810b0800c0d0044244401368803c2035018220703003622101102e08401641d204030740080c004c00080d42d03200b09841200004440078011145000c1c0b0704004200c81c025580c0548800c140180503540c0d01009a00016205846103541440706101140005aa8200080d031801c0500098007883c00d0030040701c13003482d201b0750b000c0701907410901c220074842d10005a001d91081c1e840c900411002e040c0000700c1c0040c0724481c001e680005001041055210b03054442c40a91643c603441003660300b2400c0040c50304d40200241c2d20b55104140000300000c40c4608143c41d410120140e407400b81200c0c0304900c4a036040314180f0400d64000801c0c20380c41410b405128005c4002400d9481e0030562010700c0e4125100d109074041e5200744070101c0086004e02d4400c00c03070300082403041240a0100000c000c0340300b01d0112540000c94441c003900901145192190841e1030042520000341422104c00d130b65080c128000081100007249414007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 560261798 1250 560260548 560260559
    0x1210507051603020d1b0b151906080f1303050307080405030409061404050f01060207031511120a0e03040e0609040f0c0b0c120c12030a150f0504051302130b01020304 73
    0x40d5050303810b0b4401d030024000ca000b1044081c0100c0d1907415590841540074a500307001c5070001044d20350100c20b8108801d0060a1200010302a0a8000450000c20b0520201092a5402a00c040d0061150f040382901542d14181200c00f00c44203200010002241232021031046030044210a410901c21820350703041c662100c0c030780c1080302c0382688541c007081c41e00d95155400d41004d20030a50844c4921003400310350342c1440c4000c1d640b400544401407a80507040d03c401000741940e8850064400c000c40d90540e0352a061184045404060307403507550f002e01d03100d9014a2071a001045504a4030b04080020703040e5149820400c645900501c142c90444007443e0040c000740c0c260f2000c5002d03220b0030110a440c0d6101003009850010a2940c000c0361007400c00c80c0007040d440003e246d1340760050035542c0540ea955002e00c600003078a0b5107104405001c4404401049906081a10790103998060310208055554040381c1c503003403516480301a40200c0401c0c00c0040101c0d00e90801a00480c060040340c0c64282c1c0d54 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 560263048 1250 560261798 560261827
    0x7020d03030f0240170102130e060a060503060a0b03040213050a050907090b090c0a02101b0807020a030c080a0905090a09062003360705010801050121050705 69
    0x4001e030400f02a05180f0324258074441c0110408060300c400c0d60485540d1001c00103044885103801600c0800800f40640d401700802501203070b056440039040301e4200c039610618640c00003070a8a80f9842210740700008200d1318820b005580c440c0f44000e1060040074030740900b4185662003c4c0c4140e802c0802890107134500c0f0300c580a0796024050780d41000a5504d001421542010002d80145080c5814004945441e940e0007210640151280409994521179000300fa80b4000a62051804082c1014507010359201c255141c02e0800d20700f0703101e003080380d55011030898480710610b5004002c204401100700100c1d0601026040d07000715424103040003911880004e08141c012202001401d488458140130081d40740521152501d1107101280715800700f19040031140401000194114030701800d08004121040c2110466440407006142411018001c60b07240e000500400b40418803810001070706500c52607040c00301c400ac40c00c070030440050121110024203800f8026000f002028415503400b403060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 560264298 1250 560263048 560263057
    0x50d081b071404111c0b0a0815150102030304120201060f091a01050c0d081509070309110306060d020402090d021c050607030b0a061b1b140d0807020d03030f02 70
    0x2040003011402e16115841104680c1100742a00483c02c040c0c0030454002e8034416a046109800341da218002412a001d00003000401c2c00c4aa0090007818001440c980c0801c5107003400040c03895009081d80c2d1340c002c0281c078045440e060350041c1d001700001400b1504040007114203000501c00810b420355030340c0036890075100b1034000c2017030030b80d817410129056460a201401a05070a080640c208440071080c41e441d0554003012000b03000144000420a9198020f10710b0090b200a14501d818107000e02c00400070b00048504654402c03240e02e1404140ca00016a544540401072042e6140d4105a00f80030194115940d62034010b5846030008006075104101c00ea41e1a5000031903078520f506078144940792000261500050501d8855640000d40b200900001518002c1c200004914622000983d62210700d00001e08400103012000313403404a060090f00c2180c0584031400c000412a01c200042c1d0f9808250040000404200030070060a101c02103c0c1464000d060000d02104522061002c0c2d034132 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 560265548 1250 560264298 560264347
    0x501060b0f0a020c0f2101060902190206060f060306040905010e030403060b180609010e04030c0f05031908160807020a24061205060a0b060f1215010f0504050d08 71
    0x105182d55000e904006111616808885032449400f4403400b0403644160031a07441501c4550304500d403840c0360250010001800500130466070703000108a080d80c445031003041040180902c40104540385040280c00958801c000e007114a99240e400c01c010051103440c8080b180e5540300e00704110304010900203000198042c1c50045250995403003040180d41c05061403912a00c1010140410364540c1152281903c46807404001141c40f64101030f20389002441c1c00500300200c03018104200500800031389a200742003074142d4202c4c0e0840b05c043e00d941d0700c1159140a07038644040780028042c8240c100c5a0011000d0058400781c0719503440b01c0b01c2000341c04040d050801d00307080d020014031030680b20784001060700c900c141490040030340c2c90300d44550015000d0086291240010440390751244120303040440d01450351a40c134000851008001c610855194080001558100e10194082c1c0c0b44803e818580307540d001d142904040800410020348181a54058030901402d4040c080c1c19044144004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 560266798 1250 560265548 560265577
    0x90b180607021204300f0b010512030906130b0301062c0f0d020f190509010815040f03020a0602040305100606021c050f0c0a030c0b0a060e04020603040501060b 70
    0x181009811880d0000280440c811075100c04030400310a0b203030a082d41e00355000300400601c0400e541e032565030701502a00381003182e250014070403010050b42c2051100f41e240b09002120040c0c3c0c0c1c50381000248200340180005941081004002611704040200b0180004034454403145454441e0078445820903080078010840c015080c0306250b044000d440e910150f00420f00c68405074403000304425080701007100c0c0c06a03000c42c01c100b086503100304c0107403081c5034007500503104c010001c200c2d00c210310414464140906950000800d4400c070116030880c3c000d4a0600781d00301901c5981e11010040c00c00f807006d07070840c02a4003480b4001190f0b030006100a41c05100144941b02d00d00c44070000b1a00303554020001d41d84000181480070241703580440121401d4100742d615a03160101203850f0b88201c1821148a0140301e440108041e0400c80c144041d41c02549854242e9035545003450480d14a80241d01c000300081d00040e00501d0500300555100748104d001203042c2e9a40d0151008a41048010000d40c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 560268048 1250 560266798 560266831
    0x40905070f030e0d0e04020a12050c07030305010b0f1b0a0b04080702041d0d05090d0203011104080d050c0c0405060d0b071110110409051003080703030c030e0105091b0103090b 77
    0x1da6041c02201c00c4407a086010b48020714600784041c041d038241101c020300440e00405c960710654029491110842c0b8103040901651414003090311031a80090701c2140824544030001c910310b8565010703244042001c0d0f079418946000030b101d101403417000c40012201032048140c8103000510782d103101409a8401d815450300c2c0c0c2184c1c8108400d8030364841c004c06041e11911000141e038070700020300000b0204107041441c0d8400740700c00841c06100081202940641c00c20724800c5603c103980000704112603061003501e138000e0209208a0341c9100303900188440741d2040c02084000c0c54a07601c801d07008100105822610b800700d5a803454001411101c02000c00c1021100c031500300f01c14021078100a520101c06c1059a5800c01844000d004038060710030490342d61000612404d80e41404240915002500c2d6500c0f6a814076008002d407030085180d4000a080c203000c850440c805004580c000c5600001070701d5003181e885680481524031645c03a5040648980d948404950008005402007008c1c002200c1c0c0c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 560269298 1250 560268048 560268077
    0x5010c0c0b09010516031a120303010303030506030a1502130314060609070c05150601090803030906190b030604020103050402010519020106170601030b0403050310030c0b0705010f0e030702090c04090507 89
    0x1c04008044071990b0341040b0412440c850170402901482019090000d01144030015a4801c6110f03407407481e402c15400080030090b1840040512b048030311a65051140d6a62001030584440e00c86074010400706a54284186030302c6160064200964001e030680c008683d292902004c20703ca05082215039003000d802e12490f030500b0018242c0c440d11034140008821400e594440d41ea0701d103041201154880703a40070550981c0b00d5146a801441500204c94990825040594446100755103d10401081184c2403254540e180209502440010b01500c49a07075690010b50160800900482c1000742c104000e103518240721b480381545503007541c0000303000c4ac01d2400d0f41820460b0314104440b07542c0100300403c002844140d0300c69016038103150440d120740720400c800c1c182d800c290704018010890020081110075480001c0e00c0400d0203507000380035681fa0f81c14508115401952206496082048400701606040251540104004403030900e020f039213004030f0b0102d4005890280c009814031068181 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 560270548 1250 560269298 560269313
    0x210e03160809010212090a030818270702120a0509010c0203010204140312070c030201050a0e040203240a1511031908250903020d02040209030106060504260703140a05010c0c 76
    0xc1c4c10552205007480e10408400040c054111440010310b50680010203244010040c0350503500e003035002d0041e00a80e08001c08070981444002d0340be0b4020902800000e4036107100094040c011607410f0380451414075403540480e482c0c2c0c0f101d2502414070010901d1400140c6003440200014048c0050000c411442c0000b01801c0201445170b1095040e030500062002c2600180300c8421664242406039440040742c2c000e0b03540b8151001d900341d10078400f0041081c241000c031403114200411b42640908608503404000040d02c26001e01c441003e04a08001c1e6507030b004103045a24027010301300312810b2909185829507041e802060400c000f50340740003800039050540701080c0c1480350f4200e420485094040000301000e22501c4003a00c501186506e40c000d54941e941101c0c04644040c00030301201e030325520060800e5100340310300c4030240050890400342c0d440d501c0f0030420403540b620103460034a2650311031594941d80740c1451460f500400c000c14001802c00d00c00e154980e801d03031711580d40c1c03803090f800d02c8031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 560271798 1250 560270548 560270563
    0x60216050a050604090213090603081e030f060103051005040e070e01050a1d1306020c0a02090903070b0411031e160b120a0906020412060219210e031608090102 70
    0x501a40360788100348840c3d641c24040e00c058a030940b0006803540d010014202404d42c03e5404458024075091020050000031001001d42d40b101101141e0341080d01c1c0c2c8202840e01c0200c485100c0c090440c0081100c5603c81c1c2c10290b0052802c039800e066481d00e40303000408541c0c40e10500d07107041d80920000c0102100c4001c5a0b401000e0880d00c00f0201f900c0c049141501d1403254140d0041c1d01c0003180003400c4050401048514690084c404540b18546100c07019a01c291051040e481060450001615000000211841c0c0d030303070000d0981502d0315265580400c48020446055141c020080f4400d40c80c1c009120380c20701d400e00700009109440d0807000e00c2006d42000c0e00109004c00c3e04100d144401019603040340d8001d2240030002580340d24904014001780510f8000c5140020301645030410f20055402030080d42d082a1140c400410b6a00e90a0359400400c0f039440c112030150321850080c00c2856405040000d04401c150fa107050110320303100c640036044401c1102c0c02c5801282008031560704005d5003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 560273048 1250 560271798 560271809
    0x1b021509070305120c0a14010209010e0a08030409050c1908151f2102030a1a031b010c0f0501110403050607030e100c03021207260105010c0803060103090507060216 72
    0x2460714505640b1a140c60b503103060290302c2d608000040590805600f080301c2410b0b55000040c10751034020040186001c0e500181c0031b507000546003100d1581a00c0e0500d05072088411800043d80b078540380c0038082010302002814403013140303000d100900200c2d0150507810400149035681c0300d610314207140000307848040360150030700503038071403208049814884100c11342c0c03400036003041c040a15038048003a42c41810a01c41d80e80e81400401403081003a12074016011280c4501c503c4581000442d090540d00c2000d0300c116001e8158240001c616035018078000b00e45d05000309000070301c0350b0b40380e02c4850030340b4800f026064012200142c1001842014400150858201e1605111520a40003001c2e941e900d040c82c9960525511000e00c00e050340030354100d9440b41d01c04004c0f01c3c000e00d84a800607045445181440b4011046054042180d88401c9035040c141d4030140c64a1a1044603900d50f151143c2006003810306043d680d6500c240410000c201c5180100301d2540201800c0395480c04120b200c81c62944907 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 560274298 1250 560273048 560273053
    0x40b0106110c0d08090d0602090406081911190312030e011505060a0210050c0306040b03070609060c080f03180f0a020a121b14010305010b0405090604050a1b021509 72
    0x480000000c040b41288030301000701d0380040c652a550030611502d21400c101642e20200c40c0b43e04c0401c0044a070094110303428100c0e800c08c0141c1d0b94044c8162030701c4034541c2a01c4080c1039000300a001403101038220140340409418620078200366141c0f1107403000e1980040e52595034102e10f0040c17065242c06880007018590009010315800e03280c520260112a020343ca20030000820b141103628800c11007240003e040300c00600850400c070b070022449034019900c06000d182001c2c0c04031004d040005216044409c1070342d4410300c651a0000c00c84180303183d1903084440380010803241e5004410304007d0360151031040540c0c2175180c01602058548401c042e001c92503a0403d00300e07480503070b843d20300f51803c40d183c04c95044100d10b07a5142c00801e00d01c10400f6030801e28448400400c0a2031507001c0f02c00410802e1303d04002d10b903264021244203000354410940e1003a4200e00050007410917402c440e4001c0c071041c1e404a000c0303058501807400b010f18030001d4070060348040200040d0314083d004494101c4c00c01c102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 560275548 1250 560274298 560274317
    0x40c050c0d1d280603090c1401090902040602030d0605031f0f060302210708070e0601050703020f1b0f0604150f020f06010914060a0506090111120c0303040b0106 71
    0x411a44a10706660000240300107003001110300050714110901108000702a00142c40e074040d1507000d4115100f540c1d03502d1005034080071990341e00034072860091540062600c018145041600c000c0b000003c105c040c1000301107000001e0200503030020340301806079a0042c2d51984000d10328681252019800207202c0e500034a0403800201101540c01000e609004c000b060712100c03401c0c601e0152940c1d900082d048408025207107440c81c04503c18401040d102015650348607540d5004695400351405949030030101c1c0f20215000d52700460003031400318800d00540d000348440c446001d0800140900017001e0510b042c0c1050301321b160001500100800c03c030b9160b8142800c2c07001c402825200040e0100c1484001c119406e2030b02c0c003c200521000c04041d04848cc0c0e503031104030403000f606d150205080c9101e0240007041ca00c0c07500a038001c050310400b07400c0f10300780307103280c001100c3c154031004c1d044a1078080c40c0300c420841e10403440100003e841090041d83c3c0c90801d0701e0229628141644148100b000000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 560276798 1250 560275548 560275567
    0x50102011514190f06020c0108160e0603191409010b01111b15030403182c07110a05070e090a031209060e010c08040c060504080a06050a021308010b040c05 68
    0x10b81c10100605072070380703000f0b400e005070a40910422034200d960207191288000444c02d034001141c1d642410301b81e03038a00090b21441501401344c43e2444005c000700c1d035041103040b0f960401d01c001d190300c0030045040314031410194a21004598024040d20700340c400d44410401c00b14402d000d1020f50365820b181044054107401d2031592992a070003401d01c40030f00383c40d80080c0140e490b04050052081c00c3c0c8082175407170030a4036024100d6400c2600902c0401641e03140040e0b01e0030904002d254000300b03e044400500381e840c07904045140020704610901129008041416504114024103148204002c104503410301418500804001b004940184e01ca001c504000991010428660b86250743e004111030601c0d00d002d4014000140401d0f5080d846c0c00500003605601c04a558082d500401800c7c02c8131b80c5a201c02ca6051060340a0f60314075034003e0504400098641d072019501c010300c0078006080452400b00410031030490341c03010f00d5036034460304008042e24251003280d400107481d0a02e9803405100a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 560278048 1250 560276798 560276819
    0x40507080d0e0405060a051203071b080c09071e05070506090118080d0908070615060221090418030f0207120c121a09160e10120f0506010f0501020115 66
    0x141e02c15015a4130764004c9100360320782c404401c02400e80100380c010b010800c407118650325000b9410943e00c0042103084107120032841040001611016030160012a0351101408010400a8804400c010304e00318a01e65000d00c45002600749541e590361113a4602950800b0382ca030690103442c10038180d1504104000b400c2000c058840242d0b882506591a040070f07130160341c0100340940000d0107610002484800300241c40e403040e01c512402d60302101a95440303182c120707911000c00d403424081c44e550b8200551075040c50006007070030402c01000401c0070030640307007029265034408500300d01040e0020055419150103100c80400780a000b6482090191a5115200005028454200300e40409049201400600c40c40c90000290544600c0c0d418248500c03000d54500503447e6030a030040300e42c0c0b00031540c2440c80100c21b000d100c002070b43e4a07140381800000c801c680720040003120000968090700c8000380003030024a0081c208110030b5880c0c14500000039003900e0700031541041e102c2e00d1142c01d01c94607002d0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 560279298 1250 560278048 560278067
    0x606120a0f0302010227040e0105090717191a1302010e040203150d0c06030c0905060f0c190b07030e151b0c010207050109120503100504021602040212040507080d 71
    0x41c0103020044550909134028810341e2240c0c00d140100054450081044100c01e00001100f40c030200503072600101e05900f03d61040d680d030046a0000501000038442c1d41c071016107082c0c0d00b0740030366001c415540b00f85500101076170b40c103c03040020b0220594464980007140d41d40311158503c2c01c43c0781d8501c1d500013081060348201c0c99114960100c00300301400042030120103d1000500035003540300c01030030a021600e040b8801e8900107410f00303500c40a0745100703141141c101d8002504090822a45940440e80e580084540c00442c0c810b000b100d00404041c07050101100e401a0842d401500b050080241504e480310074090150340b0065a080d0420301d0088159841010581e4008026020380941720940c81042841d00e01076001044440c00e000041d0f0011140c5031042c00b203a042c080380201d040e51240030894410120429002c1d04201c035040c030360002c003028004038052107503941d902e900280890f003190300f440c40c006044904010130008104130f0000034007114001410380c1c0782d4000004142611 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 560280548 1250 560279298 560279303
    0x30b0d0b040f030318140709021e07050f120d0b040e15100512150907080709050603030d06031a0606271c030f0e0406050d0803060a09110c0606120a 65
    0x81501209003850b100c0d42c42110241ca0011700c00346502c0440c2031002035a121460b03d0754090186060000d1640700070b1084410144c0f940f13441072028042064242c00f40c3d041080c2c191440c0c0a02405140050340911494114812005240c2c0d01c6e0340302914980e080302d5032148403a00651030a41494941a00020f040c40c1d145400031201e0400d5980381000352201a4070351002e86c00035051950305160140100c1d00c00f44d140006003174100d865441440303190f034840e0103205121341ca800c0580300f4009014130f41c01ca00d074407101c060103c900e00f401410840c021948030741c0c020768440c02d101c00000e4014410480503504800110398a60034a0113610340e01d00c4198011909501201844c880c0c101c0790b481d1031005c100c0c5d507900c0000300324010055040141c1640341c0c440c034180001e07100403200162868907210b140280c0b81c024221003034a9010b580c5c2c5102660000d0b2406030f000340b0340180014a520180140c14003038183d0821a900c41b10307010001440c044024154900c0744800c0a03c0020041c0c000035149003554 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 560281798 1250 560280548 560280563
    0x1a0406180e0a091a07020a030e03150105100519030b010809010b09060d0204060b1617030c0a031a0d0c05010e060c060703091a040605180105101404021b01050106030b0d0b04 76
    0x46562401d544030181303100400c0d01d02d991110401028a801090b5103212034066190f000e5020b02e072000b055120008200399a035242100c1005003d20305080350f8508a4130140d0800501c0c1c8aa4405a12a400300c2c9280c1ca00000f91113900700360380355a00c10340ca99004003121000307200d04000880001c0c246900245418040c0440565190566480303800400041450306007650f0303685000c0704020744c2e1000e00e10703040e01e00b0040180030100d4010818220b0344102c801c2c400d440d003800e100003821409082035031480c1c5054a60f0f6032b914141039580c0102c61a009200b5228001d00c64540300015050340004880144129030070310074414005008548a54065098900042c900c0c10501d054144800b9440f0003105082c0908104001c02c00d40d03038003c0e80240d1800d54200000010300008078241c8104440f10401c6000019040004104030b04010403041b070300800150a00480501c44044e4a41880d0500d030140e440301c6c01040750940502c0355950074507091b22a90203800f0300382c86450303041030040c00042011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 560283048 1250 560281798 560281811
    0x303260a0b01053010031101030906140708010e070216291803011404020f2e0915020a0302190627060510060c020f0a1a0406180e0a 58
    0x140e115404450b121000941011540c211680380702402159002e10020103120750001700b8000c2c0c100b01d9074901207960014144500d080c10100440192203030060032100300f41c450043c6c481c3c510701611494407448213a0350306c80d0103601d801c900200002024051100795001201202c404c01c46202c0d001c0c0a983c40310800141400c820403000d25205509031000b9031300301010480c8941044280100300001100702c00a000d2254114062440c444090b60000e44c4940380700070b0f401c6141845000d414042d40425029580302c00803540104268401102c3c0000050f18480240481c6450440c980641c010303e100410102905640c003941c0e40c50021500302c4505890000c880030051a46c10400b91030501c2d40b106000b00d2070000c60304012054680c002c8504600305400100300d40c40c051403079011501c083d618104128000c1c0c0034442e004d10100c182c0303034100c64400340116010740110300d4800b0700350001083c9a41c452803d90300401d5000f4440540000c103251a031704001115880301441d800108a00c0005541c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 560284298 1250 560283048 560283071
    0xe09090307030c140f0a05070803090109150e060c0f1501030f151e0207110904080a051b07030c06021006081506130c090501140405210709150303260a 66
    0x301c0141d500892245d100b400500500c04078909000034030640444002e6a00ca00d0600c1e200e003c0c02c007005000510b988010880210354080d00d0709040d005040c10444c4d584003501241c0320383c2c4141c2e071200d41540702c08034002d424841041102040c0c2807120f0b0541035541103541c0c0d003040c1c480703d01c40030306164250303004246800c00343c2e80840c03d0480305501c0300c01c01c1c0030410410701c00303900401402d65440796118a202c07582d003019a000ca105a9100360301a1819128030310070354440c1c00c11902d40040700c01c055004100100300f0004100694001d0f41c400c0d5005190070002454003613000e108009242c1840d4042084200004611007003c1c200a007441c070310742d10040480c00c3c10813610102d10155050281044245400c4400743c0e06039002a681c010311107120243e141d0862149101c0d26402585c84003203003514401842e600d4001c0b4890000f581c102d59902d03032080c019200307054900c1c034a0580d050300402c10550416904403030584642040b800c015015482c00d880103400a10035981991035104e507005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 560285548 1250 560284298 560284313
    0x3021e011704050d0f081302150708030a090b090f07060c110402180f0a0b121b030901020406080a06120f020613060201062306032404020a08070e09090307030c 70
    0x40404004214000c02e1605083c0541d445050410344404201c4694241440a1042d01d807140b05100c00910084041ca00340d00b4404010718406074500005024404d900018640350001c5001e0b890400c0b000c10b4424282c10070494500c1d024020703040d241d000c10a000301290002c204042190300500700040e1010f0b643c00d080b003400c1d00c118121580729100040c0c14407401c005500381d4030680419520030101d041014240010031105003e02a40d0070020700c444205004000300c1c140e48450501011090b004004040390480d4100b510421100d940224050102d182e001c02c1e4650b010303484c4c02003880851f18242c020380c1d241d003c950025015180b4602c100080d0b441d00b008450b43d95085400c00c2481658405009000300150300409102100390f00a0140300d00c0c0190f0610030030703840204800c0c81d42c5c82c1d485400e1111003000046500c14030491a1401a81d0f80c0c1d03102a0440752500c1c1c072071006070f15001030001c08003003085066510031818107052141c001e00020640382040e0381418076246c070810320b007403200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 560286798 1250 560285548 560285567
    0x12020a020102070b0f09070519140a090908040e1509190b060d0c0207120503030f0406060806010b030a0f06030c090c03200702011e0f03110d060b090a050a03021e01 72
    0x1044d402001e8188464001d000460034418002e407000d40e5178a58450040011160807501607004003d034840041c40344598a0442d840c074680010031880c200b950790f2030310a0a0300d1306000e00340d030864004502000708034003082d4225402601c07160b044114541000000e90407820140041c016144541c44002c195402940310b0b42040200404060f210301c0b10000c00c10281c80500340220060190a0002406060200c1043d60712079105010354195520b46400031700c6110010404c3d1b5905071603c2c0c001615090900106000c0e004901c1d4241d620b10780007031080103440320304000088061070004104041903101c400a0140c03140f015012800120030309044000d05922000d20a0f404110440c040183c240c0710001c1c03803030510030b8a13601d85201c3c80c10741101420f102c6055030f402003461600b00d020981e11980c8007034079054644d05003e0820070a1620402200d02c282c0000c1d82521001912440900d07040f0300d11001880e00f1944880e203a4199070201d10f001a0010205860301004000030790160300511410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 560288048 1250 560286798 560286803
    0x90e070c1b05031009080703082203021b03030a0e01030b0f09090c040e034e04020f0406180b030a051f0c0323250908010609020a12020a02010207 64
    0x16509010551041036901c6540b00781e901c24850b05010011500395800b40603141508004220b0414100391400d64241c08014507000351440c0915544813101300e01030200001c6402030340100280d0b403048907140352241454060f00c4c441e61040c0b0a4031f01181d0311001701c01038820280b0f408908034040c0d5000c0b40859000101866001c1903210420071207400010392803418000442d001d000c01ca80710650940c480c803400002c2c1c244090744c000c62031000c00c01b460340d4582c0c030155100c0e818444150450129401210108580c040080c194217110540c58488180e001c113440440741040702d02d01d0401c1d00551603100d00041300b40d403504c803201511180d6081c045070014070381040640d040056104601e80200204103d44000c583c540240e000729103200e44224061a107a41d107441c80d030400f180301c01c14694407008101200c51041c4141042e421070041007030488041301600c2d0101801d00300030480c1c0c292841d80d0800c5c2141403061080c1c58003564080741e0812110011000103984600a581c02c030702920071502c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 560289298 1250 560288048 560288063
    0x4152007050a0c090b10030b0f04090f030801060503010f090f0b03060916080705130b0409050f030a110f030a1d0a03230d051902190b011802030403090e070c 69
    0x216014040d01255010040d48038000003003140d03440b02c4841c070841d645003917001d40046200c0850302101d402030f80600c007440c000030903041a10078454009400d0b00d4206200701c034001d000a01d56810982c000003039601518060506e5402d40d81449000a116a2180310b81280141c070340c0612014856681e0008a480b040a025280c29243c008201035891710038000c0400d00500302ca000048480700032442100b550030003040224003101030400c1d400500b600d0194940d0043d510050349001441c10401c501c841303201c0780301a40d01c4250488010306014074002e1150356640148010080a40e80030003212403a0301642400b048505410703941840c0034841d50300b4140c10004544011051080c020165103e50114031414440398820380680f50f140e9114811104c003245060004901c0350203c0314000804190b240304a0b40084151604625903829420003500d204504074018020010012151031850040100642c5581000e690040030744110780726613030801c2d000a000c20102c1d031250203818145500000d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 560290548 1250 560289298 560289307
    0x607113307030c080c07031e030e060103060501080d1d01081801050903090a0b0a0f080a0e0303250c0309180f091a0601020a0206070b0429060f010503041520 69
    0x8003a009050401d41040800e04180004040d405150129011b540e40b560700c50f801905011802000c0c610002400000d05440740c00c104103e440c100105802513004083c04102940f40191407401c0c00040700d2140c0c00c000d07049040000c8001c450010901601007841c1500c801c1c1c0d50700300c003000030007502604220b055007000c0a006103000000302426180d1821101c4842c6c10b695039244100c42c1c46132891540202d02041411100c10380185580c0341c0c081080d02c1c001c0340003001e08032a01d0a5074400c9034100e1608008001c88410300509a81ca0b001c0008941413a81c1c5100c455100506400c1c41d61081c01c17916003c03114500380306a00d54010b550060704029003032003801c42510741107800300c10011951413110f04050002e916984001011070b40302d60040c021a103003481d15141c440d1041c80040c001e6901c100313508110038211142100d00200420100810a51800c2c01c1081101603009409010b040002c14400c0c0030209030742d0019a095071005c020009000c80340c4100b0860841500c0c0d90050100e0320129 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 560291798 1250 560290548 560290561
    0x120305070209070c0c23040c03022110081f15090e030901030c09150c080c120d0b2d04061503023105120a0c09060806071133 55
    0x10504280a4803a218142c803040e200c0740305074808400d4010381101c1003541c6c82c41c401503082560104220000720314001d40f900c0900c524000c804803003008924008000d1800b0000300016000c4804007604604001e0310b00300001d1000181541440380c0c24841030340d50b80c84407281015440c6031038001496404000c0c41203d802c40300d40d42d140d400020f0f10901080c100078980b8a103510914801c03090b1402115070707440010784600110b442c00b4542c0c03002c0341c1010042285072100c1c10f040203007101717000c00911007940d0f55640001000c250f8008880e01d6024110410305100c9010010a000301c9514400101003451011400010040c003503030f034066050b81000c56a41c030b15560780343d00240004100084122542c03880208000e9980100c0031712294420860b9005203d0391811071611921164500110f070102d000030340704e0101c9594150f10050708160b0752981008260000d02101c0c1d8414400d0401d101002c81c4c151341540c03550152400c5080282c0b8500c1142804100624142c2c0342e6550501e0451140c54602e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 560293048 1250 560291798 560291807
    0x10031404030f18030c2603030f06101106040b040f02130b1002120306150409020415090e10050f0112140a0e03040b1e040305100c03050604020f0412030507020907 71
    0xd45044000542501003d0480301c0010941001c40e035100045a200d64a400075664928807031500c9444065119200134090000030005075006103034001e40c40c40c007400d05408000e407a0000e52001018081005481c2d0312144010882c2688641c11001e040794030781e101e2518549140390600001d42c4000a03940b003020004099004400100302031760621100c81c64800107a9071510002d81c5203a02010800c0011060300309205240343da40b40e00d030b00050802e61103080784000e907001604200d14481c18440d0042c0880d50081d2604001d01442c40501e1190501300710f40e01d074601c1035000d094002c4c4035400c5408034503481055004290401950204aa2a81c0300d505000780b640507251581040c0c00c1c15041803400c80c010080f20102c841d0b8003001c52038000112070144084494608140f10700506000005c04208180501c1004414103400090a1f00103114040c5c21200c001c0d140d1800385106109106100404804442c15a003100c0c80c4801c980b0401d01d000c60b6188505070000750483c000800380138240d90003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 560294298 1250 560293048 560293067
    0x910080103060e12090621091c0f081b0c0111070219061e0903020901080109060501060806010c0206090d0204112512081005030f030a08010b04050109051003140403 72
    0x5440510814001c3c60816540b184452644d24007140304102c152807a10b0310100500050101000e24442c3ea0140e43c80c0404180c001c50710b83c2d055410404141e51a088582159808034415080c07907031000380203d0008015100051585a001030284106101d540745041590500181403009100038030340540340c4012604040c008a00501c0b0f1101c20170709205122295800f603a1550f0b4581c1d02d500c20a00e034081118581d00000300c02d02002c07020200c0580c640c00c00d124003806203240046400182440c02d10102c5038164451001c015211043c400560791101070501082d8046030000d072200c1105001503032042c04003000035401881d01d040e0400c030462150141002c0c00c1541c849070920411401c1d00041130b1401030f070041107243c524030816450f500840708580c0111809851103842e035283c2011a1400c040c00e01502c02c0d650021608090f032070f511203a65130252400b044dc181c142481c080c00030781710130114041c507442510030692140c0c0349071090f84030031000b007200700b81d00805062900700034100303030348 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 560295548 1250 560294298 560294303
    0x6090e0a020f030705011b110612060102060a05160f181511010507051c1803030510060203040e04060209061c09020f04021e0901020c030a12170103031d01050910080103 74
    0x14800d8142d4403d240100b80c401c2140c406840355000554043c0190081850021044901110480b00004661070701c0d0040d0182810307000c425440350400900181c9011402408250180c0c00c0204005540c0400e41c4144810510360902d0040d440c3d440307500743c90390101075824030b14211890100082035800340d41910442080c68407001c81031710700b2000241c03d1f10801c42c1e100000c20f00c10015040d540c292183e024100d002c4012000400c01b41c808200c0480d00c066080503000281c480d17050140d17100e201d56180b8010f00b2940021490640781088803055004024070250680d40d01165021450300c074039049407040010550709481101407111403800400b14400d003680036a03c42d624415182c20280308a0740f181c02d544e401099a40c0d01c1c1c13010845140c1c001c00c3c00c103045005100849483d070f1000c010805c40e13203104011803013108a105c240203209514403000018080f5402c0010004203401c55500b1110a045003103d5503240c03451b00040e122032062001c882c2d0418000090b1010706a8001c40c854180ea1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 560296798 1250 560295548 560295559
    0xa0e060f0703050c030903040b07080702030d0305040c060c0b190603140a050c0a030521090a030c0311010503060a03060c05070803180606061809130b10140603160806010306090e0a02 80
    0x8448061603101400105c031b02207010360080100740f022502d07020181140703504c601d11461400c640756000c281007043c40407600000ca5200d0042c0810007100316042005417001d45001000500c180d01c3d10501d407900648144046d01540300b01c008800c206400040140d0340141540e519481400c0913035549400c81c40007544d49001c0c4030b010083d6454402e40c183c00703d98006008027808104032206608503010703595140740a100400c04001241c80c0c0f02d80f541d0086010b518129005440c60514051030b42044031014104041041000346139070751002150250381e000480011403200c1480192010701c2104005010390201004000e001c0c1c03401408200c02c40c4042c0c06031080f0b520b48009218450207054529040021010615110750034180d807610b6204036844008602414251521480b50301e098070031007903403d04c504003131041a01200c2c044445403030986400d03103180380604409005000e007400c03c070f00b000101008981f80e0f80c482e4000d64050722014904001d40300002c40415070796816030400702c0c00390 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 560298048 1250 560296798 560296801
    0x20106060c081b0c04060b1804150e040c030b04060c1d0a33021c0e060403030c0203011d07050a050a0f060f0c0813061202091005030a0e060f070305 65
    0xd01c10500c0701ca55079030000e805410300c80700070840c5150340d00f41e45044071144198641c1c851180e0782c0e8081c2c94003d05d20341a1050369a481c1e030004842004036134140f00c2c061401c3c0311506000d18040c4100d1004c407410015034601d541c4841c5814031040c1c600f83d001410300700088050006001c0e03142c2c00310544010b0b07601c8480c42a40480303280320080c006072010550060100004201c50002c2c1020740c1080c0070b18428036400b48109100380e0442c22007031401e64006900020001d045071062450060b89800c0070304081400c40e4990000500d00c1c400e9000040400803204048001c6407425000340d100d10f08076040582c3c0010000c41410b680b09440d110b80e44c450b040200000420b401c0a15100054608002c8642e030040e050000c02d46450b5100140c01c03040001642c640d40100b0100070140c22503a0380003003559059440d008000700000000c0602c403074000e00c1005814000e030b9401e514001843c442d401d00d0b035120740c1c981c15044000d080000f440c81c0e19004000c10403d000c00c00d040060b04c142444d44080286 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 560299298 1250 560298048 560298059
    0x120102030c1908041205032a04031101080c04090902010507020d050d03061409040209040203070b13231f050c0f0c04241202150408030310080c0a0501080c07170703020106 75
    0xf001040d03c0c05800158020100b03028144036100450f802020b6904603114182c1c080c0c071051f050701d02440d10045001c404682442080b00c0c03584810039000091030401024204038074030240300d01c00c51140000080ea40c0c990354085900070300595035078a400505004440085050260b1161000a0540d000a2412001082151240f0078207400c400340549010704959455080c0712181c10081e00076a414403460a00042c200300b15002020340758400480c0b040503d1502105d451041e00e811030740d400c6041000700141103030715808071a890a2070002081d00740d2140c880400d41e0540b24035841080c20380268400f825800e9000075245045010554042082c0e45100b9006c0081010f90507604040c03079030384c01c42001550a00c030111a0507034002001c207203240b884651100c480790f015901c40340c080e800c040208000c50101c540840c000b40104030140c410a44900001180900580519810f01080710003240e10250f500c02034a20720340d8804108170f081d40754040750003902e03000108201c0041d82000000710306e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 560300548 1250 560299298 560299307
    0x103060e010b0f16060216120503010308070b07030b120a200f0105030a110318060601110c130b0909010929070518220f0203010b040311120102030c19 66
    0x4840c1003882e0b550900310300701c4001616501103001058120102d12103040804da1754801012440c0420220240000103443e084169084554a810074400c0500041012450340d4040307401072988a043e41071117039900b08041e80244080d040081e040509a146820134800000c2c901500310701585e0490381c0d50740c010000844618004d2017403900035581c092120384a5028030301841d000743d905103000ca01108140c16030081600200c0b005105404101c90010990800740440354000c1c1c028a8203000c2405130185641e40c0728441c07001c05001b122402e010107180405a031242e417601000800c01821760408440d107a006c0c0402c008207840c0030010340240302da1508021000301e0602c494045da844281c2e120700c01529143c10070604548001c03180c41c020450340d61100c0c4c4a00d503510b4840c40300070728503c11402e42000c031071100c15628501881003005102d0780c02080c096904591f404401c000e40481140007090380307a03ca01c042d660466002209001c40302841401900c0f42c0211070b140b226001358418070488 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 560301798 1250 560300548 560300551
    0x108070506040b190c170901090b0a080105190801110c06090714091005040513031d010c170f12060f040501030807020d05030f07080c060609040203190620090103060e 73
    0x640007508115401c074422040703c0c070032044c0303002d4246002c1c071950a03115103003010840400100c00d038034002040240c0e5a001200000684514030b100b500344041d460001d0003840040c000e80f4842d903c200c2a801e07644030482040c6025081180c02030209810f80c80c2d4400e000e421806000710b80d4041c0800044240a001408030304550043c042c40821401160038010141d2002e0310310102d19405080100c0c0684503070007003600491158412070b40b00f28079820010060101850400c0f42c440c0005844841a80d0018030301c00e61a070070040e5420f0010040092907140e11584c1c0d01080f40c1074001c074184000003501201d882c4214001d03100b8031031014060301007004454003400300504c03150062103484e0240c01c15506041c030044c1710300c0407603250030402042d031a4141c10070b0404842900001840020501c1e09101310f0350800001d9908a07440d00f0141d0000c1d454214105040c810055950022400e100c10f0b5040140c0441d5400800443c64030720b8064545180e01001e4200d02007402c01800007400100725007a039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 560303048 1250 560301798 560301809
    0x230601030b0f042d08120703050606130902030c0909040323190c020d020a0f06090504020c1e150c271c0201030f05130b070804030e01080601020a0515010807050604 72
    0x366844134003841d000f4140ca45019004103403003500388181c0001400e02d00100707040b2074000d500d9107207860400001425640005c0c03213140624800c2c4421071a0f600850440c000740c466407540075840b1342d50358500c503142c0d00442041030f42c40006c010600080c1a000b9082c002e1000b01400c0d480d12281c040b0b030341c1da141f03407141c3c1da5a2281420b1003002ea000c118811b0040f505868801080d090300018950002007200354941c00c14840780315481e401f00300711030f007050300c081c0284400e40d0190f04103180014041d40341c6c88100b04001100a401009000d001024010324004600300b000b00c0348541844038030012182c02807048440300caa013029030340e401c2e006c483c06882c0c0b02030300041540355000c024054220240140307050423814075460340e106202c00405405100c5c8031714075a0340d203d0112509070402d1800214040c001e5000d203c000814403010035440581038104c41403c3c2410200b5454420041b4074007403103a6405086401405180742ca080c1c0400382d168102c4260004440003551035200b0003000c0e1055210705d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 560304298 1250 560303048 560303063
    0x91104030b0402010203090301091103070816030201210204121a04051c09090203010806070201061e12111e040f1802040f0b0603250801061b230601030b0f04 69
    0x1000010140030712503502c94410710640c1d092602078008282902c1c56030108840c0f00c00d200040340005d0908100070002884104003c02841f00c084c43e424290b030017540400383c100301142c14402480b070010100703010310000703145085550342c3d41c44003141c0054800b5042100c0c0409008042500e038107541652034059034202d005001047c4e06048101d00c0011210255828881c0300e00700022000c1032840618001d100810141000c1e26007000021b01315111500030148902d40341004c50f00255214000c44255141342d640945100442d0926846060468100550140320b941d00c0d0181d180c0224680c000624007501c051115180802000c8103440b0314a0221080345020100c0380058034094002260030059503100040ea80c0803500854401da004803403e0020803000a200080204808003d0f0103941c0d00c0d00d0300107555410034200800e80e481c00c624604141c1c00503034440c0f05000d00d180880c0344914041c180401200b43c200981500d620b424841558090030001c0060b0020340403110461003640e00c01c20 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 560305548 1250 560304298 560304307
    0x10b0312091008090f011a03100203010b0f181c0201110304080a24060e01030b070201061523030a0e1b030606190806072d0f3509070911 60
    0x22030321084000d00341da080e403045c0c0900000d40b41c42841560418194240d40030b02c400042c2003818a402e05842200a8151041004000d40902201a07032110407000b0b009598584038200da170074a407620006207550203104028400b410a0b20355041c0c4400502c04e0f00c80c01000340e0808140e540f02d0007140b00300140c0b41c006000c0c400025400d070a0401940c2c031140c0b015005c24080d0307194075044484503000500101d0100e0014400e02c81d0040c61140e00a20600c003d2181070b0400128400901c00c24800c0000c0c485007503d400115911b048510751409060000d4a4a0b0b10780500d8000142900c009038844d6400303882000d80d9200d06407072130041c4000000e401000b0640b5401e0a200e0702c00002c0325a04c02c5c5001c80394010840301c00c107104180c040ca466a44404c80003c0e110f8a403582003201c4814002c01510380b091000e03442d030b040700804040c01c0050401c158034030310251a040f90046000e0340c2807030030100003008401012000f50705500400c0c07a641240d142d039031900108800c0380c42c0700e18040f8004c2014403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 560306798 1250 560305548 560305579
    0x807060f02031f06080a1d0d09081603030221120a020d0b0d0b0606070c0e090a061d1507051201080d0f0203030c091003020409050a05061207061d01051902010b031209 73
    0x20400c0c7d44241280c01e8000c661552060302c90f04007040307540b4507030004441c2c003000c0101820801c49012281e900f550160b070100e2031958080d66401308030a00412104c840594503440b6016601502e140e003180c1d5141407458502280100000e510103c4000c00d001d19204034030050781040901c9058540e030040c1c031550a91580b070100140c3da00300d220110b070040003801000c40c8028200c22568040c05014004102c24082c0d442d203842a00c10a0000c3d1010740c0700b040c01940a50400a8080c00e10040d00078510380d0741e05c60100481c0c05109611141d004229803400000e0000c40000c0d0b9a40c84001669905590a001f0302c0c3c01c82c2c980c07109440c00303050b064007484000078929048020042d491070b181070051a00c2c1e510700604081c2c410842e10800101d0303032802001111b06180b0b00c017201e002c100202130000d1a052142c003810f04090101d245944080158001c26a0303400741044a514920050403600d40200f40c0384024040c2c21079a000d1402030044a861110020000b000d8804d44030009215004c45144074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 560308048 1250 560306798 560306801
    0x50f0d09090b03011e0f18050312070e0406180e070f18090204050114031203010515130503030c0a12030213050112061a040e09190b040807060f02031f06080a 69
    0x2030b182168103560f00e00f11407143d41e001c02c21940d1071807051074000c140b046030303013038100c0443c0d00301c0b0a012040c02090789400c0009801004541c2c0c1900d030f04c01900c41e07507140c5c1c2904840120079040c0b5607411600d846404951182c00100c1060415002c40c01030000c0719082650945030070103407140880013a040700080c4169825424118103901c42c0711400a00e0b00754030b40014003521403c0c0e2254802d0507a00905400030700f0280034080075081d105054600c0c5524250120710030100d01d66898191000124040440c20741c1d6200c032500916004084039254803c1400ca507446400400c004c48508085a040401c00341c0a402515904420300c180c41201600d00001520701503000f00e01d0b83c1100e66030301e1011814407480e001001c42e01d0000b880103902c603070034065646158000900504441d607c414500c80000001d01140702c089503124000c00c6081d199490702d42001c1c0110b84004055508004580c10446255400f442c4110240c5005080f0004d0074004506440e580d4010b1100048401d00080c0521505 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 560309298 1250 560308048 560308061
    0xd02010c06020c070f150e010e040b030a0f030305061e0f2b06150501081003170706050f07030b121b0d020604030f032007140d08070b04050f0d0909 65
    0x6884007500d41580e801038a424180981c000d0405281c170744005001006a4009000c0c0e64030190606207880d4400400103003140501c25040340c0300c0c903100c0e5400029601e09001e61520ba95001d9031041d2148418034000c1e0240408581705e5009040400e4070300c210f4502400c07162640000a029038a80c500d030a818404c1e4544482040c001c04800700f4052041255005072800c031140c05a40c0004042800c2000a80701c0b40c80c0d80c0c407040c10003030028140501001d00d001070000710380e44010050b4282c98640e540000c0c1e0700640300040c25080c5420208180d00c4d101e60702261217030140303544c20003c0c1c83c07400c03080240c0400c0d000105465a030144a580d0081c480c0c2c2c074046a09030b40024800b8440d0b98007035000540c154071540080360412070b1150500205070b0441c8154100404508000300f10000d82c001c216529003103845408021412400f00500549a00344028241030704095040da6403000f5080059160005680c219030324411140d110f560550301081880d074402150b91110000e5140409a0340903008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 560310548 1250 560309298 560309303
    0x1406030705124602040f09020c0c10080415050f060f0a081e0708030403020d0602030415060b09010905060f0a0c140715020c040b150318100e1603020d02010c 69
    0x503c0c91001c00c50030780141000c5482c45404442050078101640b0340c0e8452651104008540b0f401404148603d01209950b03c080c0c0d00c04220041c1c44000740081545001c110807045500400081400060194854207544c070460003841000c2c00d0811f02c001c0d02003100e00454002440d40b56990100789149040d0342026a480d100038031706c0080703c0e2180e00c01c0707042a141d140e102c4018122440c1c1036150b40b80a0051f0002021908069401c0501e1030300401d04101e06c06a0007804d17a540040010104070929680d4101400c00c0c00c4200700080d1604840010355103c0080342e80071880c0310000082078070306141180d00981480c12178905007981b00d24241c400281400341101e05007e844401280c041c4100800c0004000041c00145005030000d40030b07091031f02e28541e031400b950400b03440c180a5140c50340b00340c080c040c4100c00c25540b9038a070203091035100381805d000c50b1380340512011401c601d10960424030a82d616802031712000001d4000a00301d481c607512009400c030b07066003d900e02660040040384d4a407030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 560311798 1250 560310548 560310571
    0x303090902090a08030309010e071706010b030709090606110c0a05060d23090705010f0e010c140a0c06020c0f0103061a0a180e16110705150c070f140603070512 70
    0x103442c0d00d059170568104445a204581d914101d00c079010f042003200d0001401d004000000492103c4015034440c0014018080c0e80325000011130030003407050b55482c00070040d00008101060700d80340700804000803c02c405c1480d1080c41c03c40d003654070381070481030b0032a00028071441c030b880c004030349640190511008503000350040c44043c80808a541304443d00c20325160010f07017a40c40c1807000240041c1d911102c00401c21604a01c0d20b8000e0360002c10342c81d14250008403075103000ca905034481d40b800824140c02016003418020000390680c0018060980b510121140d60940e22244011004c9448601c2803540d8922820403000005907600c0003020560310600e040c004114194a280f8100b0440d54840d8022068a0007003056010001007045841c01d484c2c82d000001b101c3e4403207816928011401f0702d42c80b502500d0f03014802900588200d0304402e601c40261500607946008a407000041441071a202014500c074410f4289880c6003182c0c45030000791500d5080c1582860030503901e240013400050304c030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 560313048 1250 560311798 560311819
    0x8072102160b04060501120503070224070b0403030b06071502090117010b03010e22060507120f020c1608070b16020d0f02040c030e120306210d0e0604030309090209 72
    0x841c21080d090304140565981e00440c10a89840d40031150142d00c5040f1140202c040013000620100032140500e80440e4802201800c1c03000130b25500400c0021003091807000a0001e0802aa070704030395200318080e40301040003907800024441d8510860000422003005a503c1d8019104a64064501c00006161490550541c003640003510f80c000c2c0c0204200800100041243d100c2ca8400e160b881400c49184d640c1401c41c0503482d200181d842103004000c00d441c0d42c0082e8100d449900c900028060004080c01003c014000c440c00940c4400e521040303900488540d400c2c0070310301100d075004a0301d03400000d2280c035160559900c45900032958045c05071480622880150351503e82c00c282c0c3c0346c0164840c00200c6054810801120a80d40103141418102a40d10054003030102d603401e00350640746c00040c1d49540c0e40f800a011002546040a0054281810780000040c0094590b800c3c0c205c6884088645070058200310150140b444014001030b4801c3d018000c00e14150040d018070000079000180d40c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 560314298 1250 560313048 560313067
    0x5090d110d1a0a0b090c030711061306050f0f190b03030409020c06060d022b0212060f1f05061b0703061e060803160206040e040309030b0708072102 65
    0x104034001d0040c0c8521810307030012a40c0d984004011a040a0204002c1080c107503c42e0104035a40340040c040d10030b50b01c000c0b00203000e080c0100504c0400404140c140d0b4002d00c2d04800e4100740c2c0c1c800100c1501e60f40d1a10000130501c008940c1030f1070041c0d9165002c103400d40e0381c024140110303545c4440c40c21422a01c0b00e601503442e4a003040135101502d520301c40561190300801c0e11502c3c04000620540c0b1841001280c540541c0ba46140741c105420b0082c00385611301d668404d0504203501d111402074118840c5100100c946c280820b6084c001d0071900c1e4101030640342c0e1404104509184110307944640c20080d0100858501100105100401003000445030712080b01030a0400e203082d030090f80e482e5110604103901041180c00d201003401045000c1101d2407c0c9881c2590701d005015103814500c55403c02b400949d1740388410754004183c800d00c0701080d807030140340040c0004214032040364072141003800b050880313010705103141c480c101a644460421f0005100f0281c290000e883d5a908150300b08041103a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 560315548 1250 560314298 560314309
    0x81b060f1e1224010905040507030908072001111005041a0915070302040308040905061203071a0c03150d060e0106060309050f03030723130e060102160605090d11 71
    0x1030030030100103900062600740c0c40f4242d01c46a200400f8050507620010500f2a03821003d0a0150b0380c0c1a40c1c00241035441490a130700030050390f80050100d22010408a041100384151152010a80d01812200402030b00c01940c4030031242c54017024a410201c01c814034103c240d8000b035130290169240f12021030701e1503094050040c040c1c42e200701c1c94221540b00d540c429140311080e5040303e00c40c90210301d801c7c034644507100540614003c0320140742e125004103c02c0d40d20b8005450b01c5122544c282c075031303501d4186068030303850083d904100a14205079000401c0750140b4000d40740704104440c522201e5540640c04c02a400101e0401118410380d110800903003407000340306201c00b0745041e4500050060703940c20071500c2d00301c0350401031816600410801c44c0c400d601c00e1003480110266915a0010300305030b00e201f540b9014060342d1240440d0110300000b07801203134221050141c003082e000c0d070380c10800c4d2654106071120540680b0380800c00401251907941000400303c04290700404000704d804246000048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 560316798 1250 560315548 560315557
    0x6030b090a050708120d0e0a170c060714070f0203101d06090d0e010c0809030a06140f1015021606090e0a0c0e0f060702030105010b04081b060f1e 64
    0x3100340d000424141c01c12808202400c098500140107000c11044440360055502c949803492a1180d00c2c0c01c8000c80014003003064203071b500c1c0d110b41807800307852040e455010303a50080d214a40c0148030381000302c0d9402740620710100c4a604440034030341ca8030149899a000e41509064126094400e03482d01d4081e00305544907414440300101c400030b00041d81004920301c0d1403c00b0300381468940004250000c60350b000007941c400b5940038241a040554141081700040c0212032040e07401d40038544803602000351940c45030b2544c800e121103080d0140c0340c0580360120380d0003c0b9103034469401e00304d10074002c0c2c14154101400694061040301c02e505258035007032a144901354005004610a200c040c40358a2540034200d070700c6006040104100d550b122401800075555941840c010040910000c155803a01400c4440c0c0d01d0b0041c00078400c6580d6805420704580c82403040036614020300c851080c1d1040350380d44011865400424560820112403070a03019544401c0200040300701003140ca1050b250751038081c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 560318048 1250 560316798 560316811
    0x13030b0106091d010501080408070c030c0609080c100305060a05150901030b01080f152b11010905010203040509060f120d080a0b06070b07120e0102071a0105060712020106030b 77
    0x1111154034000024120300c11941103a240f440000b01c04100604200700c0d01811104246065202a1100e06120082c0d02c03803490301034000310b501c182c08410302140841c040c3c1100c0c030b10703030361601016507800459468810910503281c0c841ca40701030300307600c0e64400c1e007140f038201e030780105002003040d83c410001e40207201c01032142d250424040341c5a6059038051180c40400402824100002d103003c50002d200010001c0600314145071840c0c85e0702c030a40b42c410365801c2c012454902010100b2440300e0000c481040035204458481d44480f20100342c0d44241904003c4450680003103052038140390802c104a0f10090503d43c2001203403600d03206c035540c0c3e1035000401404060107420601c0900c0c0c0010183c4070000d0906060343c2c100100c020494031550b04541c003c03904283c81c0d541580301c80c7e0301107441100b401c021240843c208220300003503e40650041c801142324036010a100405007840c0c00000c4030034030403560710903070500032a004030300d0803000d9212010362480002040c1307890380ea13030021b000015100c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 560319298 1250 560318048 560318063
    0x61e1e0c060c08062b12080f0603010218040506030a060212012c0f1905010b0c010f0e0a1b090f050a0f0e0d05070201032703090902070c03060c051303 66
    0x2401031190901c01d4400441581c900480c1a01d13000002ca52000782c1d403018441c42c1602c5811244500020191106103250302a28800c0c40240c3d0303510007811540244c42c18035000ca21040800c1040ca8140308071094200d010045401640284d800c003c01030000610345500350003014902c1002464510003004210784d400c80384e00d0a9414601000141303483d00c6203c46070080711034041150b0f0b035103820324103074000c212080c11030156461560184a1000740c0c01690806420072001081d4400d00d040903000ca901d00310020072500001300000402e4400c500b8810803d50041c081070b0f004100f444480b100c01c0b240300910529a10395483d221022540c00c0101c604c20507940310241300d0070309940c2c002c550035180ca4030018010745c0c250410345c035241c1c1e02180c90351040c0700001030070200b1640640c00c00008070716102c0380e0812007108280c3e403107040d04111000b02d0000e02c596501040c2601c0c5031007038803405500310b1207a2030721a0841c2e407108014002d02200c042480401d014810f0721041d11200304029510415a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 560320548 1250 560319298 560319317
    0x91c261201061e090803030a0b22051e0f0402190e010e0114010507110910050603090c0102010c020a0f02012f1e0c011d06070503070b100609061e1e 65
    0x2c070f041000b044800c0c03581000340c0c1d141c041007031100c0001901e0304450102d0000500b1603100c0700042001039611030380700581319041c8007a812071221b540901d108019040c001c0210500290400402c2142280e034801621a00d00226000d82403810201001c0744444440004403501d818030402e5140090b80001410507071040103104001c055402c0d0301444000b030800900b0000c084e42d41080072810f80494034050300c0e02c4c4000501100301c0c0c074501802030002800c100d40e40d0400f41005500d03a8801c442c6540590300b0b00c1c0c0d02091003840024010410b68001e4541c0040062541c0111010001c21603081035401c0d002c211130100861504014040212500c022701d103600008500d1110f03900c0070012408160400d0b0095000d5980010b90f1961901154120800b5007200d040058074034002c200700030b0918030000c00c00d2070030080465111809030440440300d85200780d80345030456075800b00b030207000c00050101040b4141d02c81d408035110300c20141d608101841425a031001c403c4800320300184400070307c5500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 560321798 1250 560320548 560320577
    0x1020a0804091a040e190618030530070807020c09090a02180c091c0501060308070b01080d0f0f0e03120a03051b04051302041a091c26120106 62
    0x3076003240101c3c8160390a10602c400501c5082e00d03000f644011007041c10240550008205413036000240c602c840c3c0c46a100000098203009040d40c1000600141e844c1c00100d03408110310941020a01e0a540071240400d555234606044400ea1001340c0010150b00c034420840b0130559681d40e40030311400c0041c00504a039101070041240f4a01d010341e041e060b00a004040c0610f40c89090115620100103695140d03240049a00341007003840ea210018005501c2c101022042004260040860034041c94560525903216020351b921280301c00c003250702085444078039039441801034505500000c07c6043c02420404508040b9007400d51003000c03085007c000003098200035415210f1907400c0100e13a840700441400c00c0440400300d100e20300071103220b416150702d40c00084005804581c050181c40c1d482515441040409840603002500c3c3d00d4070a400807a00401854408600002c0550b00030840111401c1506011881ca100c1039154060001c81048046203801d442d1511600a0900d070340d803500f0071904030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 560323048 1250 560321798 560321831
    0x207080904050a060f1a040f0b0430140a060501030303020a020d1407081c09050c010801050301181113110c010b01140304170c0109030905030d0e06070b0601020a080409 74
    0x10302d1005500c0c44d018090040b481c21085482c251503080794414001070208070301c4101800f6650213994054003c54001c1051035440002e0300846501d440c0c203180102050000b80f840b11600d513010740144480e100b060010540c0840220706461614060314504102d5484000695209030015001b09800044a44005504100c940c6204006d4075201681d410980010364041c4100000941a141e01085202c52880c41241c4104c03800304c000000c01242e00300707142894440ca02d0742100388c08030706035000000f85401d041c0903651006015540700c40190f04140d0b2110b00400d02006ca690b00003401c81004151720640e4841c050003000c15801980c0c0741c5100c11502401c4d80d95002c0154100061500b8007003074070752603a080d0380c0c00503030100707141c110300c40c0d25030200020303000345a44065151f080401c48402e05070001c00c094182e800541c285c5555103101c0d00140c0b00f009400a080350004030401c070540208103444030341e5400c140f0510648140c19955100d001c240e13006a0441418a50f807201c48426903030b0103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 560324298 1250 560323048 560323051
    0x7030209010f0308070b0619080f011103010506310906090f0c02060c0c0a0b07080f01080d050d050a02041d07020c030d0f200303160905040b100f12020708090405 71
    0x20000c01d000850466980305420300170004001c040407a101c01107034540d03440c80030031640200340400c01c1a42a035a070741d035503550303001a0481001c075500e1701400c0401c4031941c104072030503100041c2001d4a041e05059200e0023030303410114000102c06514210b0358010b070f06c841024006016404000c510301c2d00b000f81200c1100c6018003c100e0003450000030320840c0c0d03004034032103600c06d2075403108035100d81101d603000d402c0948000c401444501500c0030000340075005103245000340100e140d18401c80c1e890304906030340c400d012180b241c045001404140059042900681c0e03018070414400b5003010ba60340700244240340110700c0c0800c404040d2007002111503042110890308003084000742021444040090300d4442d80400580c200000444140c0328075103189019080c044a440c02c072503603850b19520022420302c005440c000041d0320118000b9440c03a040c003a1048045004215605101c107843c07040c0c3d1030401d41031641c0c0510054080d2080e1542c41341c4081d014060107440019038500d448402c10045500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 560325548 1250 560324298 560324309
    0xc0305060c1309090b0402010c0501180b0f07020604051f0615030903020f070506030a09140d050d0612020310020a110304080102030f07210b0301090b0a060e011d06011416050703020901 81
    0xf5043c660b0300482e948181c5240c01603028200600c81e4a42820852f0242440ea42c42220200c81710a0440401c0030300b01c0f030180b081c072445003c8025511006000c0343c03540c1043c0c070042c0a071b920540c80e43e141e1170213902c3c000812185580c0c0000b94030765114203a2504070b80203800c0402090b580c001c0c1d0014941c0500c0208108001c0f04054640203003031200252075400040c100150081d60b4000742c07003c0012040e0f0050300071171001c00f2174903030b6108a5002420340e44500e4221200c242464000074017074074009040100c0c1680100603284412040e99140f0003074000c48401420811051044006c1100c24001031003c1d203020030025070b891400090b95180f0b031002802031070400400c40030708030b139008080f9a03140b100800582c001c100d5074402800a40036050b00b10002c0c00d03076500001801024106a0301810031202c0402110f1183d03030303a44400211802460324401071500c0000c1c0000c17803940c411005402c88214003010107007400709c00c0b64a0710301c500c1c01d40390465159100640500c15440c11798030302c070700400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 560326798 1250 560325548 560325551
    0x31608060f090303010f18060306090b0105030d1407080309150103050106081207020d11031608010f05010801020c060a270b07090f0602072601231f060c0c0305060c1309 74
    0x140340c5144005c881d400d62140484418002c03440c00c0b1f2007101500420300943d0007440903c890205400c1c8644040028420a4406d2040787c407443d4041e8050032000c130082d5022002241030008680310410f0680c00101450300c2c03130140705c20b004d8001c91a0f055160280d4082c8000103049400c21610502d002d035a0301c803d24550401f8042d0030016520050003280c11340d4030011000c1d0f40d501ca1070101746803410304008031400803d003000114840c0740540c0a6042074034410700c1031051340d0b42d600009080340b048100c481c00e9508070302c0004005100381c2c0c11003c8001c00c007600c043c00b48040380070100d81802c9851001c4030360105030b0047c000300da40d0125008014001c601003104070b10345041d80c082d40d200c03030510500d206001c48002c07600e540070b0000711041100007074500900c402c0842c120700d20020740036450341e070800021200110700f2115000b60703482c1410309002490182541004010307505403001c204111400c40d0301740c6010000940510035140a0341c0303152105525402086e1003414840c00075080044000e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 560328048 1250 560326798 560326801
    0xd02090a0e0723040f180e1b12010f02030703090209060604050d0b090a0503030c1b060c0301060e01051b0a030f080606030103141009060c1407050d080711071d010b1303020f031608060f090303 84
    0x201790902301180601012562a200c680b20a03200e00e000d4100d100c0400003551010040040540d0160041030500d41308603618581a5100b804104481c000c03409240d0b004000340844100251b0940b04c0d03250855010300c00c0710100f540c0381c0d43e42841c650040303034001801900171607201e002000700c03106110204505c40c0902160325110303a055045002c144944410001104000c000340c0e4010411112540072507040032a104c1d081c1c0d080f481d59a40d0380c1100b1000541e640d40e00c52000342c41340e490704d800b92000400d81071171646140c4450f4010340c001c0c0900c407401e00504001c0038404401d880f50f805918414200403c941e41d90f200e0290520150030020980e21104100c51000100045084c1440d030f003190030884210b80310150700300c61008440401e01554480e400700400c0c50000c01e6403000c00f88405d0140b40b901682c8480744014a800b80b07510301d142c80401c0d40c6007840185404910396850020240c2200d151603543c0402c00448000c3c1d600400c800d8001d41c050011200c040d40c080c0358012103507002941345 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 560329298 1250 560328048 560328073
    0x703090f15080f1003020d08120f10050d030329040c0215041b0503030c030c010f0207020907030906020c030f0301081902030622080d02090a0e0723040f180e 69
    0x52502c003d2112840c4011040003a040414002008010f10303001b810340760b40c595407460032100e20740c410040d6130b224100348000203001d08080d100300c038032402e040748044402c00d2800007030000c08140b6250450915440355605011609100c54005c001007040d92002c20818055092008039203071880c030780c011908180820134281c0c0180d8006508184d0040700c28080070030071540540e1040285d0031099140c00b00141a101516000000d841795038900002003000c4643d260040089200c0c030350000750803070800000034003454081d5100194071070045501600d416200b0801d03600359408503200490070b00012005200d4482c04021290800c20221200044800c03d9000240c0c3d03143d0060400070318142103160409141c911100c1048000e600941c0982c991864804841c06074110040380c03800350058000c0040e91980c02040c4a0240800e905c1e0844010208104200c1c002d01500d010121350004120002c2c5c6807108058200041c2403010718009051f051359100d2013601c071203050002d0b03241d0161100014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 560330548 1250 560329298 560329307
    0xc020f0105211803030408040305160e01030305091207080a0506011706010b16020a0f06170c160c0e0f07081b0a05090310091202071d01060e0102120703090f15 70
    0x1e02d81c0c5440040c641c81d555810390070030221104006509a40004010710041140343c10203407050b2445203049e01d5850001800b0040f100070380748a00a004038012004001181c060402000801d50140c400c8910500910a10786000c1c00f80d0701031f4a855120040d00e00504c9000c0c4111030161455883c2d01080502d8815140d0380d17607406005560b540d40c0d002404c61a001c0380d04000020003907002e82501c1c031880d038a00300c1d071114071510301c03409000c80ca1050b51501d5188011200134410840103406500300a28407001242509043c08101d0b0101150440403c1001040c83c42a10a50700a030170310070035180044005240020262540818070780001d4101d800e603080c0710a031400309006262068a6840034000a89030440c0c90200143c0c1c585050713001028030201310000c0604d010300d07401301c0326407a0707603038403003042030700150b048405058091070042c009503100700a0b4003045041407040b540c01f0129550316000c40d074407000f41180481c10f000d4042180036070902c10a00205481c034071b044180d4007504009031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 560331798 1250 560330548 560330587
    0x9060604060e130626030703081513050c1e0c0a06090201031e06030b1501020a08070215160204060b030618100909060b030106050a03050a03050a02030f0a0c020f0105 73
    0x140300302c0b0401c00d41d458840301e40514440500c10302c01d000713280c4c0d510106004410340451036810100404660002e41c3d800004a0b40080c1d0f2580d54403882d59503100c1088100d040140040b6807101036024072814880c514098180a080d0b0550841da840e6521490300324410000d682ca030545120900000d4414140403a80e9071183c0d400200100d10b00320ba510040b00148104107541c501c803015005002d4840f10340e0b50140c420b503440741e403410042c0e484008108611558254003a401640061801400200401c0c0035041080c405010000000303805001c0d4601901b211848030b09819880003040c1c01d610701030045200600d81c40c281c652a5051800c082089043e80b140c510500e0102c0d800031406041845800da0000d10789450f007084030107464605403001d031043c4410107110b5824004040360920380005e082c0200d13944030000b048c0c0501c0e2035405481a41210b108041036000c07d0280c0c4030a90810801480014020b81c0c400c0e226a003680304000c2d04141c07401806040020610080a280030000c0080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 560333048 1250 560331798 560331809
    0x60f09060f21490c0609150f05090c040207060207020907111501031703130203030d0f05060406080c090a09060501030c0305010e0f12070c09060f03140c0f09071704120e09060604 78
    0x100640c90f02903020389901e42207081c010035040c0340448100134006261542170168291810501030955911561015101e080d12206140c0e04588401501031505a0040c82d00c0c5114031005402c2c03002603000104804411244400031a51844d14403d00d08401d0102036120001202015119415611080002954500d5411400d0000000f00e800c030124221003814880d4010100d90307540203030306000c5003c0c150f81e4201c02039050500000c07620740e20b0a80214030a480c0100018414914081e081140b400700c0540088000d0765260284000301c1c045020f40f9001c1c500844000d1041d074038510300103084800404170326215411500c14881c0700310000c90484c181201060401e5115441d40c18070071030700441948075003819458181300282c040703541c001a8007240e000b0a194250301c0c1040e01e049032240c40200d4580e038000c003103048413040c52a1a0f1212600400c0d81e1601500d107690f00e0b0200c9000000644d4140e90321845580d40ea404d0690080e0180c00c840001d49a08419040ca5000b2554500990198 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 560334298 1250 560333048 560333173
    0x6050a020306150f09040b1804051b0f030c060f0705010903020303041707020a050613080708010507030b0d0809061809270c0a05130b06040308070506060f09060f21 72
    0x6a807c59661800e04085110329031010b210181021700d091075486144a07001c07217018051211030a064604001030070b4400e8070180141406103903a404010b000d40c8001d114440d0040c0510080001c50703001d200784030065100b60000d65803810b040c105a903d8a0704418080c400301001c00a4600507201d201070ba804580064030019281d54031100303140344c01111307500a00543c1c401d0001c00a510081500502c0c020145502c04120080c612010301c001c00003155400b502034a0300300502005802e000c4001d000f410580c9011503040d100981c0041c21600702603c0400d5000c28518100c056424220a00f9007071449407002003444940f40d50100340400302c14842c6034800e0384a9201405196211f4009409172a40104050341c4c850b100d28001007181c001d240150340c14414100088d8090411f4203411030180402081c00403e42e0f01c20b000c20010015141c001a00a200303400f02d0201c02070408075504d500e08101d0003500048d5105203d0b21484400d040001900c208103000c0000f01c00fa2502d020407004032400c45 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 560335548 1250 560334298 560334311
    0x503150d080910020c06070f020f01030509122a210c070515070501090803040c0603050c03060d21120509070617131a0702150c04120f06050a020306150f0904 69
    0x401d17401d01c4a08a03099400500000e440c0d0100b0030107a0f14007204038800c4401c00e4071700c0803401c0110210f80b01150007038031584c030a0b0b070b148080720744d1030015101c107a0341186098511000f5000b00651441e83c20064131150303100c0304803500c070141c040140c900005116500b0390b0800950100b041d80e142000c0c81440d0085038030801d170005d48500e02c1c0850320715681040090003807904919100b64190300803071382a00e010114210116990784039001c0d09014a140610aa0031038490f24204804221040c100b2980b140c90142d0340e1816881c0007028002141c8903444090201960308000010b40710018901001500182d0003801030680202c0305481c0c020a10101140c0782e502c864004056030190b540c00303841c0c550806014580d007281003201501c1a00980e00b50303a00c064106000905400095441840400f0180002d0141003c60901110150302803201202940002e0302c60304111a025034052000c150000104545402d1911754034201e14100d4510500e0302c1d8800040b407045000d03944599104039107406 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 560336798 1250 560335548 560335579
    0x1003022a0304053006010611060402030a1101021606030e07050406080607030b0a0906030813060c0b010b180d1b1a04090b0609220c02071a0309011b0503150d0809 71
    0x74080c002c001c440c8801c450348203131541003c81e55501c003441001c0009440d01d012003404c0c4400b0030f41c640107a5002d0020188a840795031450201e86407890020b045109801c105814520030202c15401000141c80c0011507041c2140c80718140f0310590002401142450003c10403a1000100c13031398842c0315480d000030311080540004030038140c10ba108400d02414020003000348543c3c20014640c8009005c00c195505544040030b0310f81038402d02026190003002001040560b01c10b4004000744460301e070409002000032000902070b003601810540d031204038030f071404809504001303412000e0328240c01103441c0143c0606501d4024840ca004401e40d1545075201084c03551286400ea82c80303018018441c1d5810000740128131401070005190444050516452442550000c203a09050b85c400c00e100c1c0950090305d4080701c1203035102800c00841c540d070b900001284e0703109060240038250301e1641e54503945c1c102040704000d0320440441c070500c01d0349030241d80300020303400c1070440b103807140241c41d0b00d1403420811 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 560338048 1250 560336798 560336839
    0x30804020f1206011e030f0b060112050721020904150807060e03071a19050702150f0d0203040c03020a0b0703080a180212070504050109020a02010e060402010c02011407021003022a030405 82
    0x11b61000304480303085d035034804c104240e03076240310300c0746001383d0343c03d04140c40c0d424504095072020341c1c5640204502c41b900110901c082800c0f410b4405407500094030b40389240c80800e0440e50344000b00341c20103403170707002c00e1040710018000000100810700e00010145103c10009440789194805c207404106103074142c55684071903100303991040f81945a9414008410340001d40558010a0228400d441503003205200f0780328101500c5210760ba58034000d08044050b000c0c0f100035070001e8010f450a170341da810000016940c500d0054007405480c6480da4503920b06207006808100090001202e07103044c42e041d440d0404030000c000d001c0a4044a81e401145007080307425003461076941240340c000f41400004510032815070000c14403040f01c0d5008201d0300d440014059103c080548009000500111013007002d0340c800d40d003d03100200b03c80813003841e007141079000806609100600b480070913000b0800782c00f844141100c0b900c450080100d8031500c1c012000030315031680704500a0901c1120481c0154541e42c002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 560339298 1250 560338048 560338109
    0x70807180806100503010c0305190b0409050105090a1e020904020d21110c0a0321090b1614151b0c01060906030b0105150307051b0a030804020f120601 66
    0x403400b030340c00a00300030b607056607081d40c0e501465000b90308011004848510901c19248586424542c1c1c00616000c0300c002c0000e09041030a056000d42c4492482010031001c3c42401d014020300001081000098503042c612245007500001500540b00301e100c002da2129014170341e02a604583c603a041d01124a010094043ea110a8019003014800c00c0040a07410a01c178a16809107101122404548502000207044180c003000b05241c801903500e00131140000d580b98580c182d02c1c100b00018641341d60485455401c07801300b00118031900004002800380d421f581d0702056201101500c05008000b4001504c40800341912110483e09004921100d02480550b4045290000240030560b034840620020782070900050300d400306d84100029543c0b40015512162514916503241141d4560a0551f110b8000c0300345802c0a403888250f813007442e1030600090812038444d4841288509040c01800f60002c01c1549480c01b40784043c000819020300026020304655880003903034003a41c000542000407180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 560340548 1250 560339298 560339309
    0xd0f02151213020a08010c0e040c05040b031302090609010b0702011101180501060815010501090605090f060408010c02010509010b0d020d140f0d081b070f0c0e0a0c1707080718 77
    0x800c1c500b408003050040b0124585207008442c240281500c80e071403182210072415404000c24160228a00b2500b0280c0080344020000d092040c1003c0c0c2d2150050601c0c1e10440d40214401204001c90085240c03e5402d540c2008055640e08081d60401b02034034014458032602905000302c5454680810a00350440804c010781030314401a12007140c606a4041c02403401074200030301441c100340e0504100c2c9000503040f07800594424000510741501954654030641005802c441e045003100d1854407080c0040002700700d114000145040c40b440000d08440c8041d107202e415906007410a0000e54400240e400002d4040f5060300310030385030340307003a6842004510300d40b101402260141d00919001082c0c00d98914403039200d4a82e159902ca4448904140002c039902c43c006c000e010020221f5454030b40103003c40c0c8641402d00c01c017a180c56244a010504a940002d490303110100314880711303801002e8a007440485590144030341401c00001c1c02550b0020071110400c0000c502c500082d03040704540900621 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 560341798 1250 560340548 560340577
    0xf02030c0304150608100c020708010b030607080a0e0105012309061f0504150c050706050c061b090d051b04050103080405220e010522050d0305181f0b0d0f0215 70
    0x4802203034001c05049030707d0300440036003d41c010000d0441c006000705095290018003410560f0b0782c487c803da441c4c11f4090721110340795a07034603400401008240b1515001e88441002000100401d02078034001c00001300d4183d00520045060010586410542c03000d141c4141c81d6000d06141c80a504541c3c601681e031144104100001e0f0b1522070070f80200001016074010800d461445807516000c0e24248160718150342c5c190b208000003240c078580036a92040840000c0300031807924140c1000101a055249002d4400d034024443c81c0507020624005465262000d031418005c1d9031468031007c500b4020b42c80380501036040040d0070600400600424a008401c0c00030800c000000c01c0f1a0600a10044070f0800c5d211540f01c148440025081094641c1144e004009200740c580380c1d2012400342201400b02c2c5600170740348900305c034071480c148840c9000e00f8a00c41242060412041c00c0010341d07001c1041e407401880010310080c04103500340300d08005903406072444000c04114204c81c41551049459208800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 560343048 1250 560341798 560341813
    0x6020a050f07080c07050102280f1407090b030705150d02160c0302010f03050405060a0905330c0a0203030703110d0c080402010e040b0319170a09090f02030c0304150608 74
    0x1c001c0c90b018121030104c1c102143c0d90161240010f80e41c548118800e03079480f96030f80092070300c1d44a2020300030b4100c1c1d2013078030104800740d0035944510740d4102052900c100c03a001448244a82d590500c99001c49802c00c40041600303918000100760000b01501c1d42e850662000119101588610380407190380c244411154448804103042204c040c400c507000c1240021510078012030213502c07034091640202c0e0460040c0250ba00c880000c0d900800003154210b406001d80c4115514010740340c00b03002c0d4a483d108144009c0d10500c502030140e90040200a00340d1b01c20b00340700c00d49000340d000050300ea101e42c0030b04001850a81c0c901090615006000c42850a2401c12071103014480d8082c010344e0080b4803e03219126511308030801c00040e1140d01c02503c0d09540001c80180722800e9040e044400caa0007120541034541400d05800100d5100340d841002241403414104000c00c00782c4a1110304099080e030460540c11704601803d503a100180019040700310b241c05401e10440345500030001005500100e6850 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 560344298 1250 560343048 560343053
    0x21050c120304091b08130c15030204051203040312081003080d0629030c0a030f0203010609030c0b0c0c0d0303020d06060f11030301050a0b070507030f0b04020423010306020a050f07 79
    0x160361040c0148168641040410105944c1346000ca0700c41c0760864480b03400743d030b4802c04004400c8080c07210540b100c0340001400140d180c90711031308150381c40c10395030050f0303a5909100030301040038100450103406610410041000c90406d001180100400b4640003686446400724900030182039000603184000015a201d10f0031082d034807080498000c0c214036880803100101034541100401911842004200700040c12240408000c0505280c6403c000800a86500c180b5003240c200340c019030017007170f100b401c02c3c400d0258541d4104000d20721140c9252404242007500703a1a40c0151b60414000c40003c403942d02050f01076016180d030303415030200400c20720b96a00c2008016042c00c0c40064003140b60907003001e10911b00441140c0c10b0b1000507004007210761401c0c040c11082d074031640055426000302d420100c0041c6500040e180100d000b2402c0c030809041a00400046503d8001c1c48900002c1001c0c003042d21040c3c1915031070450340c001c400161555400c003000d403028865610640d4100e500002d88608 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 560345548 1250 560344298 560344303
    0x21c021f0f03060b0a140309190c170d091e0504021908010902040302180c1303150b0109050906010c06020c0d0302030a110405180603010b0a0e040201020d080121050c12 74
    0x141d504455505200c081d589418850310b0748241400540040d08000d902c5001c41c1c40c0d54011a0445480405c48803400c440c801605000300c02c2020443d510075181e40c007045400c41c400454443c411124002d402200000c0b03001510380c0c080c0e4800c1d59201c043c0224440c0c803009141660800906004c0e0042d903480c0e00f0515501c00b419001d10145000c03801900001c80c003038a451003520152036010340013401c4082001020601a03400401c0e410102008019083e2800b510505c03043c019841034004032000034480d14114141c6c0c80101d01e142c1088034030b14003008559a40b540e4160088001c1c245400c000740da41c10000b02a104000d8824107510403245000181c036811b500651158001c280e08202d1010b4000d08441a84a00d110700d99025292038805052006941c41c15a0420f00c0140001444150300010072030000326a48121344100c803400070081596018407200c4c04680b140e1401515640c1400f5a54800d080034181c0013203009aa0307d181c504005003008124040c1c00c0040906405001c00621a81e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 560346798 1250 560345548 560345567
    0x60b0f120705030105180c0702040627090b340c020f0a0605031603020c100506040e0d12020d0914030403030f02010501060804030c060902150301090b0607021c021f 72
    0x3844624844002030304180702c0e20503241078480c0200503240202841340490741e0000003030141c901c8190100b000c4001030340c0380c1c82102c000703002c016500101072079441146514400c54183c840b10182c10641800300092100100ca075000c1e103516030702c61580f181803a000a14640002c0d01c1c00003071620840ea90b40b4503800035491902c6a100301c83d000c00d41c0081c84180004600244900800f00e030051002c80e00e807e07001c00c000c1200400074600141044060078205e8500103c440f100601c05640f0381c1440b41c682002e009852500700600300803c90070014810040000c0d400c00400c2c90940d50100303403181a04503d41100ea0525000240410740348800c110446d02ca80c080c2c0700440102d101e03000784a00303031401070241c2412140c468450503000e036120344054505020b07918044460740c0e540c622400041c2d4880b507a2681c868207606009840350b040c09171610890307555111081c81a00240010001a9101014041c0b00390f45000000c01140a034404034000074504e03400d03500c030701c24100c1c4580002e03548a182ca1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 560348048 1250 560346798 560346817
    0xf02030114040e0d03270309050f01030c0c0b060a0509010e0a0c0927090614040c06110304050607050c09040302060f0601030606020d030c1b050c0a36060b0f 69
    0x11644628141c108800c840e465031819007107400c03030700109060f14041e034059808003a842c00051003e0f05929681544140008030403000f0500401c824095400d0220408500600030300301003101c840082805050000b4000c001000c000301c010010340c10b038940c4960900108809408040c955071194521040d41008640200c0454a00311110308603031710510b4902c003101c980900300f5445c203480c1c80011442078103107a803002c11a900c070a61440050100c0c841c003c003001c024004401241814a00300c0d26031003c030b600400c1000080801061320f1000841203400316141124000c2d0340300000c0c170301b00303082c00c0c2049419a8804400b0341040185a00030034070074402c0071800040c84142c0d8800700150b0841d000c3e802443e00503448980084015402940801c07000001403d00892009800900011000407084103d5075034001ca43e02c000c003818030f103d0141c00391403950325070101810b2444400740c0403c203803010f28245490b600d11416101c40b182d448040a016900c81c016a0392210158440c2c1591103090213 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 560349298 1250 560348048 560348069
    0x302090705040b040603090203010209061b070501050f04060809010b06031611010507140d09021903021503281b05030402120c010e1e10030603030207080325060f0f020301 75
    0x1100d16201d0012102070355503081d4401c3c00c1c1402d15408800134910110207c0e01598200045521981c0381d0780903001c48100fa0b00308520100c82540e07500c1c14204941d0166052040500c0b00558401d001800c0ea001c1d1040c40c03170200519510003001501408090100e1742d040341c000000e00c00364024600520701c24100d591120f05042e45116840c908a0700112a072030002582e12006142d9031071104020403208142070740109584207940c0000d040e034001c60520400c2200d048104004600f00b1010401c85240c1d40c884143c290300e8180700600440c2c40c1070940c1180f031300780c2c01d038510a001041d074440c044581e5481c40b04055000c4025002c3c04561081d00c050381315202410b0006943e000c0080c1114406906944003111140d00742c080c08045006169030078140301c158488542c0d140c45000d12882c2c4881c080e41c0c00b20340e2914505000c0e081c6003203a00500700f10f07082041140502000c8031052031010440d4078a0000a0126044c24802040c003130051000003410b0003280d01043c40c40b074010390305030744c0114103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 560350548 1250 560349298 560349301
    0x30103080c070b07080f0715050c0a0e400c0503180c0112021803060408121806060603040c090207050c040b04060f14010309170c0c0a03030512070311070c030209 71
    0x2c0f1000d060190f044018281c04041001001406007140907244451041d00009000c000d0b48200b40161002120071103105040490502030300741d07001081d0604540141c03800440c52030380782d54803588038030344181515901c80562000e43c1d50b0303108020411001c00c0c03400c801b0018082e02da600141554010f40310708800c054203c40d0582c070004003060b61a840601612804e07040019000181c001c0d4011280c0c108035000d591400480c261024044180300728455140c3d0f40c0d4031141d0b03449240c5140000b6244602c0300300100c005149251000a40541100040340c000740c4a03916450660101c40440d0415690540040b800e40104000065603180b41c18007160b0500110074000c0501003190050301ca900103141c0c440104015461000629500c06030040c9000726200d4060345a5103580c024800142c11090400100c0c046210070510022402100446070b00d50300503e03588006000740504001214184a981c0124414034004d901004070455462540f9860b01c1315800c1800f00d061061100fa40500030150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 560351798 1250 560350548 560350559
    0xf0d050a030c03121e0509010609090305040f0b130605031f14031b01090b0d061508040b06060702010e040203100806090d0e09040203070312050f2803090b15060906030103080c07 78
    0xb0501400100a80e0340300392410178484c0c1c00a40310140c0f0411036956145808a10448540104e10649001c0c0d2034940c0d681d46000409070b1070000c56846000c6000c818032003010418865961030741111284d10301030344c503a20380722000c0310000d25800d05003200c2040b0850000d8103224031409001c48900480c1952006003464486001c0858004060b0b400103154010601c00e074002400500003905000c86d0024100b604d414a07000000074403140540400d03d1902007101b00a00e804005511810a0300e40504114103940045c180c0c0b16008001032249401000041704585074a10102c02403201008440850a0607a0303c41d880708446103500380000c4034608000300b9803c14812180c052075002e401424590715580b02e049480302805070040802804114040300d4590a00c098110030070800c9400301d00545403d2184540011440410240350070b020401010800301c10303900d54440121280c80742c4024041340010800c3c492198560391041000c0008002d0210420107042501e103c8006c84000c5620350 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 560353048 1250 560351798 560351801
    0x301061e03090b19020705032a011a06070f0203060109240513050c04080616030b031b102f010c0c0c06050d0e0a0302010f0b1e0f0d050a030c0312 64
    0x1c0d440a040d01407003101056981e900409141300b0720244a100509202c3c2d90b0342e6071800c1d5480f01031004446104045250311180d4070301c0c0703100e150011a1008101201d03d8004c035114030011903400c18400d050101c1c00c0300174401100c0500300141c0d4010305440c80e81d07840d5401e0350010640102d4103e85069403201071420240000488416110018422000d90b4400b948100203440b0040100e4540e140038000007924210800c1f100b0300a071300500303400219606100c001001c03180c4504000348070b9403201150b2401601c0d0401c4881001400f038400f02d124031882c401c107503070140302c0d8001079650310410b00b04003006031b45003510070034401004002030241940c1401c0440e024078801c2006080c0f050340310b0f0f040042a01540040800c0c440b04100400e002e40320090113820403110090980241c1d449480000c52150310744206095040c0456501c0c054010031542c0c1002e941d41c0740c0c040c0b8002c41d014030000e406036440380c450780c81c0c0303e5000d000c8a25200080c54010050f27141103004038081000c2440c5005e0320100c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 560354298 1250 560353048 560353061
    0x130e0702070e0a09030903060b06091f02010c080f13020406080a0303020d15062a1e051e030405060c0705151306020c060304020d0c0305060a0c09050f0102030901050d0209060301061e03 81
    0x640e04c1b080c03080c2c02c54031200b00801559040341c1e800300080100c0c2c60b1580740c4268150710f1901c00354409007a12500d82c00a0709448203407401d40100015102045050001c126220740c0182090104c0b820100c62440410024015600320403414810015074804040d41038004002070483c4403c2800035041c0d404448480da805400b844000c549580c4600c05080031200200003814201c204500103084170b5162011006451550441102c03118100902030000c100301103c9000321500a0900450000d0605500d900803408de1b02d105003000100c02d428031000b04013040240800402c0c1305101803040c8010900365000080c4001031151020b400103049001003546d011101024104501e55075441d403c00c40782c94210501210701000510020010075000c002a51280d2003c02c40014040c0f41c0301c001130059405607000c10f124001c0d001c0c000d009030740d0100613162007800a082054480070002c2e81c0c900a8081e031090590400c40100000400c20750000f80000e652030304401403071400900035012006d07031300c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 560355548 1250 560354298 560354303
    0x210110c0f0c03060402220f0506042d09050f030d0e25030f0f0b1602151306050606270406140307030213020d060f050306250302130e0702070e0a09 65
    0x15800185c007500b030295140400810f5078485a0200e00c054046c601124102c0b803180e000745945804000c03003402c00f4400c0c80325401e40020310120a140d5106100100135194140040190b101c90b4136404000c820000001598011401c2e84e480780e000c1c0519600801ba040b480480500c0782c104104000c4992038411107000700c1c0321545072600360031901e0b814aa40d441010848001d001c9040840c085110f5106441c011040c280c0141182c1e042060000e2403c650182685561b85109045c000000e14522043c24400d51142002c28a80e40d2000080c406004000040d492940315030a010010800e9603950010518104e60410190b51600c1e615248030440e03118854061b80402024400b518246036840c20402589030050700d041202c0d12810706489044d03111404081001106001510381801056840388800d0600071816034456080100c40141d9000c074000d06074005032110f201c06c190000d41024041e4001001100e04010400950398100d92103000074150511000c6045040180203145102e038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 560356798 1250 560355548 560355553
    0x93f0a031808121303020316080709020909041b0b030a091a010b0a0804080d090f110612041101050f03090f10020a0203040b030a06080114070e03010510060509010210110c0f0c03 78
    0x40340f60302402241e1007a0f45050a01c1040c0c6000801660b040201450328401f540e00c00740c03c0c42c6006000381c94080d480c2c0065841d5030051009001c0c0c1e440d18100e41d0761080d0031580c81e40f0303d010445000903a9030290b800840a0540000400c4a60002c41d00300303d003514800c40114500c062203c408480a000a00580b079000004000d2421a42e101d42d0000c0c0c0c02c1070140201914001786180210100d8114200840340c03a04144041c1c400d0240381c0c1c04c0140e00388401d0355081d240c01d00500006410860040c0018003501c1c041210849691040d030940d404488003003010743d0360742800d2a00c160b8070030f04140601c440c4d104014a42d051040c25009640f00242a9001141070a0802144101c81d03000200040001d40e6030382c0c00001c05050900032000c00005d49401c0c45d000c2d0502120007043d119014403824003c0e0705240c140403040f2740300c0c020402111518030304203440ba2083c0004030305041030782070180c003500d08203003c2040c020845001084102e5400084070460204c05110544030255a000c055254 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 560358048 1250 560356798 560356813
    0x90b01050904060b190515040e01030206030910090605220203030a1b020d11090a0b06040504110c010f0608150f010911040812070209060402093f0a031808 68
    0x909010100c103800a01c100c4011072446643c4020503081400c0903c441000618845d0030009030800d4540508103006920505240074200449051540070611000303005060010004403810014450000d02490540d01440840724508007540940825150300c0c641441407440315224030761079008194030f02e601038003541c10080f00c0301054403070781c1800c003a0300c40b6110039550030f00050360340c50030000d087c500c00c101808610720510b06000101e103005156060251400200e0301482d518407068608952044034041444240c9000020540c001e0120101c4a5070038003030403d890042c1d80d00641b06841d007450865541590140315003d00d00001d40d401c2c1c103600c1a220040c443d00c0501c1e005420440c08020303649162641e28548249000c50701a00f089030b0020100b1382c40f00b180341c0002004d80081c7e00302d5065092051100018102440f107410580d487c3c1c1c044004009500040c075040c4d247c4144005d00200c00f50b0060b00343da03441340728207801200081c0d007161918098502c5480100181c0b95036000070f1910 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 560359298 1250 560358048 560358059
    0x60f010201020a0f05090418080c060606040303120c050d050906090c0301090c05040c02070f0603050a0c09030317220b0405010b0307060f2708030c101b140f0301031a06010201090b01 80
    0x44d031b00c01410301d90031a44424a01c030907074417000f500484d818401c0000310f036108544590309080c6100a080c8900c914801c1008001007680300c42007a00d5107854460014907a4880101a00c1c03030301c1f03114002940306091504000d1200e8000c102c1d80c0c80b6003c400141c0d2018203281c0f00305803c03100381c03090051034040c9490b81840700d41000d40c000b400c3d1410b40d00403101e00c540c8540d0403d2041c82030b0b501440c00a91108108050b5604600031480d609180d4107005078600c3c11941c005e4132a06050486540c250072210015883d0307072220001001040c0c286485180c09482810004184c920445003501c0540c2006c0c00e50f4618100051780004950a681c0d41c24401d140009085940000042c0c40b40c880e026401101420307002da9046800040080070300940d82c41ca48581100e007058612010109403600e441c145142c0003504921855403000075180c410150000c64449200c00d0290280108034101c0c08400030040051180c500c003450640c11035028050342e1588012402c1c1d41145100624064161004104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 560360548 1250 560359298 560359307
    0x3121202043006021309060509070c03110c0a060207290423030102030703231513090501060807031719050c0114071211182202040b03060f010201020a0f 67
    0x4405800c0400250090035101c030f4059030814600d04c400044051001c2040442c14070404000308000d42d07045c203540c6818440541008403800028060001c0a8406050201c0034000c081100e103000384480c007005d0b10345800079510441d90003408100240381c1d020b500e09412180100360022081840c0c649000e00344600b112000c600c0003598408561b08000c0e40640b56800e0010798840c00340c940d000109402c2c04038031188203040c14004140740c003c101c0140101c184410030824044481036600100d210140700004000b416001c40c0509154a080000718070241c012842e18103c0e0b02420040010340420402c031107051280c0c420040101214411580b00e06008001409086005000000c1c04880c0c02c0120780069800302c0e0ba03c000610350a9980307a1408192140c900300e0682540214100601c010301c1541d00035601820b20721a00c042d8048141c000100450a4404d501c403510964a43c1e642e942c4540454006841640c840e080e8489803100039403052080c1c54004000781e4134440c1c1c0c9110040d088d82c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 560361798 1250 560360548 560360609
    0x70809040e1002160b0a0b030c09090f06090102090405100b04030f03030b040c0e09090a241b0315050d021e150f0d0e010c0f08070504050a0312120204 66
    0x442c0c0121005004004014400361509210403000e950141c0e000b4905810171245c020604207540e031034a0016116a200000e240e04510416502503820341c507070000341d910b8070703200701080e030f503248900020800d000c00f040d00076111001c01550248070345c1d20317000c400900c500154021a114203d05120810105040380c018071441d074046d083c00124500e2007004141039401d160f00020100b507441400c4012070402d41c828541c840e424801505003544996980f120104404480aa0704144807695640e8080c0550081e000c1e6409003000e00c10799000d81034040d020f09000070383c40c0130035540d51000007280c1c2400f50070a030849034024452003094009112a504c54480540120340003038080700e00000d25060f03100185a0070000f02c001544030b030200d405200580d85014100d80040e4182003103045180d4106541990f991304c40d003800c040d40da44220701200c041c056540080d03030080c805070000081c4485c58140951546c00c9a032081e44254103403458000340e10851140d10409014090894022010406e00c48c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 560363048 1250 560361798 560361821
    0x40b0a02160f0b150603010530030c0714030601060f050705150a060302130b010c0b04110307120317010609150905042c060615030a1b0f020d0507080904 67
    0x69526807456120350151103034490007124940800300902520b802c103482c60b443d10407000c68aa600c1e541c10a0081000c0c1e0f00260a00f80501c032802100071f050807012210500384111603001caa4a444c4400c1301503607169518820340420701d411030308000b151b0a001c9601c2d8180c514684030282d0320b07034000108880e180e1004c44c00365100d029007410f07031150f5408a9111800703810740f0040841c040d4218010084003480c00489407195900d01220070709140d801c81d400f0081c49400040c142e10642e603500740100b588144c1031540b60b250140140100b58014100b25400642e030090f0303540f000800c2c2c45e91203c105034000380209008105806c01c1048022200c1074103595402c40f500d4000c1020355030300080741c1500c2c43c00900c80c140000619160760f0f0040001c4030a4002c00e40c0c00000c0a43c1e041c42404500000d03c904840107a8110005c005040040b0070b821221a5481d01c0e08059030f984449100108408594040100107000d03080e03a40c0d110622071400d9406081d04808001d20700000310302004000d22101c03280 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 560364298 1250 560363048 560363077
    0x305070204090302160501020a0b060906010c0503121b0304051e011d06160503010e01090908070b04050105071d0f21030301080307020316060c11010e03031606060608040b0a02 77
    0x1548010303252801038030790840c400d03001845120a0500006800c5041c1e0300480e0440d4020080304001c40c140f51400c5420200582d22200ea944bc1c410040340c0c81201ba502c060b0603440300040c80b090310000c02e03420074411622030810012201c1400f00c0102203210558014002c0d500034080e41d4865140d200002600340364003000054410000c0d036082100b011551600c200f15003100b000c01002456031b03c51000200c8107854240e10759070408100070561601809100d2005598070b0808042144200444012036009000e000540ca864030b03080b03010f03150481e030507800100340441c0c2015401c0c02c281c2c10503100178020122800001341006125103042604426903000305066060b4108040610085003c0c2032410301440e5205c006005241ca00711410400c0b0a4611040804100113a03002441090341940f1034002043c011641004031003a1080104080d494000000c102403114071000c0a24141441803105024150361204c06482e0b441d4102c8020705540d0038032000a9440c229a4010074002d03001092 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 560365548 1250 560364298 560364307
    0xf04050c09120c091006050a03020a020102210403120e0a080310051c170a05040302010f020a050303010b0919050f0607210c060518030f0901050d0513031b021c0305 72
    0x94003802c01c02e5001e01a030380006203811100c2c100340101c0c41c0d2042d10103042d844414900400240300d0711414446004144d400318118000034800c3d0100c03001d0140e42140d01e9524002c4500300c0607480d0303003901d048011030880c4480301040040c60003078014408140002d40205903103a121940d580e4802080360a84c80c030207020110b0719a98408000701c10107800e90380203141d80910724014100745110408010464424011142c80316800070849090307070343c20300e020721046040c1d02080e8548625083c00500900000c0008100303221424080c0039136a108603040d68080340b0410f0707031998000c4607004880c4c1043d88181407640a007000c50041c600e0070b10410030000041a005c030040003050060302c9200001c1e43d054046010700245009031908000b13860850003034805804c0d040d503a00e1140e02c020400d03070b0101080c1c0c81056030298050305e038001c2e0b140d0010702c66480c01e400c1681422401d24011408101e0518002912400c80c200540115601400044982207050700200701c40c0185042241000b40400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 560366798 1250 560365548 560365567
    0x501031505150d1503030f020f03191b0b0708090132040203070b070302010203240d060c030e1e0723040207080c010c0f2003040b131a0309010b0a03020f04050c 70
    0x103a0f000045001c7c1d07a4245908900c800c0003400d240e18141c5032009503209003c59590800100741641603600b0a0070304c003004240340010142715000f10340014220400740001c1102043d00700301c9141c41441058000c01c06404c5c09080e45440c0c42054200d5401024403601044001100e01000c54016000070100d9001c990703505500c03142c1e03510404046006075004402d00c2030082410405600013242555641401d075902c00104100340c01840b4046d00c05529000d64207405070081d441844010064020744040302d0707503503e580c1e00b0504100603044044c400c801000840d80d03d200e42c0e02c7d0030a11000c0e00c8a0000708103000304000b035089030b2429a140e403000c0145200d180002d100704080c2d140207403990810200b004001a000d40114005116880e00451031207280c498040222401e440343c440115440b1007900c280c0801c56401034100660000c542c150301020544100d01031446003079400020b200c50110a018004213000c1da1000941060410840c91580d00e0543c02c100e51180c0b220501034101031440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 560368048 1250 560366798 560366831
    0x120d0e0703060209041b050d050c13330f0e0307050405012310020a0206131703040f050406120f0f17070b010e13021012090c0501031505150d 62
    0x40e407040750407941c00180da40e1142030034080ca00412100101ca1011030b003c00300701800781e125002c0310801c0183d8950009000501001c251014144901c1081d42850348a4000341e1076500800c06640003c00c0c2e0140c042450030440c01032640c100c50540c1c0d4042a8081d00005171040d1590000213036260044040201d580d449a00c2001c1c0205600c00e5a101c1c6a03c1a14550302c00003a40b0060714002c2c401d03100142c2d02950001040e001c4a03505030303591960340304125003440050b0314035006245041c0411903c070703140e40070003c09042900d02a1080311001c2d0303652010042142c0707052042c600341019542041d000704400d40c0d25101d202e0300502d000400100e09a481c821007a640f9401c0300d60001020400d5020320500002d828050040c1070304050450078000800410200a01c4c0001d01c1a4614074148036060302c140b032540c407400f00c9008140242002403074624a007000074002c0c01d000a2070820782c9007098070b02010031404c461003e08804811903801c1c2c004846a40600c090140064032041083c13501d0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 560369298 1250 560368048 560368063
    0x13140307050114011e03030801050111010f0c02010903110c09041202011b031506020604170a0212030a0204140910030b0a060b0c0309011716051615050906011205120d0e 74
    0x30300b5020f03a01036060003000e145194062000501e6141c0d440030500000350842041415600c0c2401d10304644a05e4091103030262000c09a207640ca6420801281e04164054100e05000c40c800e85078031141201d905031082e5909141c0c0141d6900507000e40104000c503502402e60f5000d161305100100e02d002d520b101199844440398000c4001954421104a0722040e10304000302508482c80a400c3c60706183d11055520902c0100c0110250400541c000320103000300504079814250390902c644034500710f840034000350001c1c4500f50040c1440015505949020b0001912400500710044030460850302c0d1000d03801001007413446400c0d035510340800d1035401040078102c503c0115000b5551040c11400041c021a4402c402c071418121000c240031011349500841d81a403802c0d0304d040e0351580b40340150070074011400c0c48007402200303108107a2058001d690300118030500008044401590703840c0c0d132000c1000b00118014207203070408110783e043c85001100514400141080c0450915030444040e4101002c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 560370548 1250 560369298 560369321
    0x317070b15010807090605070816051902041404031e0207081510050d0305160c0905010e07080114030c04090f170a120c050a0c1407090b040b09131403070501 69
    0x40604004042d607402102d442c0c1c00760441c9401400325103000302c003901e40d001d41c50780200300403004908040c40c2c055800c1e04a0410390000d0441c0d040070a03820300103510702080c030804d9000b2030400070a0411040c0c0782d42024061903050f500d076030400040d40e0100e4544510168100110b0144000006103203d0400c4030035010081c450741c43e2040e04180800710f0030118a903124034055035929901c400820740206c00c1d5000007072100d21a81440c1d020b86001e40092681c1d401c48411289044008034001c0b4003042e4540c410760160719100e03141d0341c03650b4490068107844600c04e541a400010303c070341103081c1034000d494a03a1242c2c0d05150202c40d980d888214002800146181c40c510210742024116132207a0500d5000000103010040c880d002c20004020388909041e0b10184904120740408210808264100d004116400e9943c0c20f6121413501c409001c480480d41e00c039600f8625071f00000d1030007070005c034000d01042240856460b015a1480c1d054003816218010500041c80307420007289080c01072003007001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 560371798 1250 560370548 560370571
    0x90c1e03010f0b09060618040207061d07030c15110a080304020a06230c0f012406090806042405070c17070b0604110c01090501150b130317070b 63
    0x21088000d05086809105544690a060583c3c0c0840f9440740380090f40c0000b82990701d9550b80485055100750515a40300a170340081c40060300344244203041d0310039000c3d4032110301c000400411944880c0e036105a14003002d04204403254003000b1001d400d51008007611b6490070098101c100c0040f049003014882201a980d650b8000108011494890681d2001c0c3c2031a0a040c064043c0c2c1030016000d141d254615200e9030400054401c5a440c0100311070002001142c00900400b86103500411502500714202d4032030812554010038071600039002c803002d42d804a4004c212980d2140c490581d0035540c43e000099010540949014007040c03401031510440d5146c5071031056070789034542a2840c034402c00700d4514000050005400140c45c01c610300703820000072100800e0800d414a601c0420b842040c0c6201015843c20b42c0344410000d042d0092255a0840072800074469941e8901c410180b0a88000420200040c40c00b0f10004540440303020620a60010031408c0070340b0780c1d56819840c030082e5445403900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 560373048 1250 560371798 560371849
    0x609020405130b0a05220309031106210a0908031e010512031209030408030408010b191a070f0204050a020c10180221070f1e050f0603090c 61
    0x40c2050301445401100e4030039405520700711521218854080600070407255078071100403d90400c0004a0200740c5101c840e59420108502e240140000120348006c07600000007415840030361501005031100034400500d86040780a00d0f400320240c1c1100204220001603450740b1000106880c1e2000d5445900440e590030845c1c881c1035090485201d0503485503218200b141d40003190b8603030101c00d903482030000c00d049003059220b0b03915107030850080e50001c021a01c808140040d405a0541081c00320300c00940e951341e000080d08401c40c20650503402405c07010074903094002c04c0b10000c00004c4c80d105000e8040c81442d10403503800581500c506070303410f00c4160b801003181542400103202210b010700100908000310a2488414403c0400501d0701a2003401c0501350807441000c110303805c0d503882400d08260340c00d0365190f07101094901d80600444400c00e03520040d001d41c4c1d14100062500750b400003400a00460f00e26000c201c01540700030920003141c02145142409170711801045040010380c12504070b11b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 560374298 1250 560373048 560373053
    0x8061512041a0907030309080a0f1506150e0a051c03140403201e101b0602070f0b09070602100507030e010603081e04030f0206030403260609010806070e120a0f0609 72
    0x1000319400090594202d103201e100007400da00ca07440c482ca64400c07091112f10424406540007000705520040100d03c000105558096018441c003400350b2045401c400d01c6511030090207080000c000c95008411403000200010902414880000060160b903840c5015142d80d1411500c0c0101d00c40395041003803c1d8900d01403071810081c801d000400500c415101d042011000940a00042c0c14041c00c3c0000008181e801c0c9030840703200301c07000703404c42410b6545c2c40551a1042d107100500c0000d5070309030f44c40300200e008c00c4c1d0003081c4001182c515500401d00f107c24000218003d0002820f500181640c60a50100100c1c081c05102e0055019091503504c81001319070320550300207039591110001c0d02c20041400010003030a001180d40741c0664210380c07079603124a03040e40c0c211010050500c0345092101d06210030f072840d0090302d2003840c0c1035450b04040d03640c84243c40c0d59040140c0d230b80000300740c040306031071001d08140c0b40c21710100e070071030044a244032540d0301c80780500201100c050f00c2e01038461503180103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 560375548 1250 560374298 560374307
    0x1b150c190c032a1202010e010806010903140c0102120a02100c170a0f110715020d0e0307080309150915041b0f140612011a09060d090308061512041a09070303 69
    0xd1000001c134413140c2d012a80001c00b407010501e0303014144000e05000c0307803490344100c1c50b490241d0740c0320198074907460244078502c3da5100c440070300c01d00500c50440c0103030402c5c02d8082a1401c1d46000d800030140b007012400b260001e00601d0b82400e0800080251a1313111141e803040680c01060000e1000a00081d241064400c0d2040c2d10186500e91404112100015000d0780083c4502d80c0c1c9000d0058a80c03030840e840401400003820504d840b8400454444280700d11040110b000f140ca40c0216034005030041004c400410040352040101d0b00000d8034010312088002da600c2d803091044414840c401800003500e01c00401ca500315842c9000d00282c24413040ca03d44402c0000d4420403074080c1d082030490034021a10782e0050080f450300c04000307001c0d4100d4145a0b02038650050000307054984415050008900511040c0800c4c1c0000e800300d4003160480c1040c40e82152407403000d001e507074039140c5101d40245488401401c12075102d03611811101300e0600c0310b0a01c41c05a40b00030041c1480750320b035040007403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 560376798 1250 560375548 560375633
    0x80412121e0b03030a050a080901020910110c0a030c05010c020102101803020609060405190606360603080f220f0f1a0406110f1b150c190c03 62
    0x3c0c002e07070003000350042072a0410255060300d070703003441c2050551b9101c844140c0a17006100761a0780000443d0080a44940c01c03020740040eaa00c070b5400c440c1c126415200b0082210800c0c032029101100d1003078140055445203c203030010b14010b00488654585120410b41217501c039000240400303400780218010141d0621000d038000030043c0c000e01d801d040545640da1074101401040314181800d004550402c809074000c0300c010014000071007000310030740d40072084811400b04291ba48007112800c15502a1081c4161030603a600076000d98104440303d41c40540c1944860085641401c4c0502161081420711110703001400a14602408251901c2e000b0005c3d640c46030409201c6c500300c4900504000203500544044a03110300c0e0140010318101429400c11100e100241040d00412850084900f860f1140504615041d2a0b142000c28461403030f8502d40034064403d04c1541000c00b40c00d2500d0f4190b060011118041c09a186c1c15030340d2030b0760305542e034408038420907058004441c800a03107420035914030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 560378048 1250 560376798 560376821
    0x1022b0c020a11090415020d020306010305010803070b011a042103030c09081b01170708150d15090602040f06111509030d05041403180306070f080412121e 68
    0x2803140d403032507030f070346600c0d0b600b02d2049140500d280301c0020b41881101e40c0950400c0b00035182c215a81d00910b012540031358812500e06010a003014000540320034004100d079801074200303810865503420308144c0040102081c0052000000611010440d0a50f044420020300e840c01c011410002207031070007805a5440d08008001e001074107070204904807012400f00302c1e800007030072500e41d40102080184c1d98039494090507880700303030139404100c41c43d40c11645540c01081e60360200001e10f500d01c41041100d020074500209018a50b001895480303da6030010100244203002c050300304ad86a807400c841c4400254040b80000385e03104c03e00400501e0600c03e4050382c018800e022200c42c80c1c14410980d0368412f940000480959500018090241c030400d04684030700c848059990322219541c03d00b202c0740342c03910524400c1c003665001c14881c2d409a6048606a40f50341c1300d80d00c403940c89071100d500c81c20381454000c040c001130202c0c180f00754000384030f00364034590364003001080101060208002c035003800451 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 560379298 1250 560378048 560378053
    0x1090c0b030c040e19230109150605031008010c020604140102090906060a0e1f021204061e0c0c03290402061603020c060f030103031d0109060f0201022b0c02 69
    0x20b1000b04411907088500340d811040d080d50554881c042e030302c0700031003124a450384128a132101380f20022504030485001c00c50380c424400382503600c400207181198818090b242200c07800300000c00000d4000d101560740b00d6214251007003034075501c0134164259416a0f20400040c0c100008000c204101000b901c4038030013203680211b00700350100010800d079140c040c0402e48100300100d1044141d512542062030183c2020b0181e1604030210740702540b0b1a090100b420002d40902482c400b00ca01c3c0e0f440035a001c40e4107959130800004005403042c85000041e007001d00030040f82503441c0380423b81c03640403d0010340c41340c119400303000000c0070710076030040d80f00c4206140d02d0314250510016070356a405840f0b11510380100030020012031f18080e443c0400740301005812810106013004d5031320700a40550b0489002c2d03201c0400b08508903094000030a003e2982e03d02040d00c1a0007441054491080d6450a01407400018074011003858460036101c001171843c080100d511041d189403d00310700030000301c605036000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 560380548 1250 560379298 560379301
    0x90c0a0504181410230f07050d06060f0e03030c060103140c040e01020702180115120b0d200109030213020a021207052808030f10150201090c0b03 64
    0x61040609841094425601d511000c81910400500519078552101c800590119100c15440d20380050081c1440d07102e00c2c0c02003040301e181900080f9151041c0c0301110b04110343d18202c103120075000160000d81000818800c072004800b10b03100b1040079003c00d41310300850400d4008020800d510300c4151034003d4009110800d0100b10010750f250640c1d070300141d41d0701384545404415140c813142802071075129042600c80008150190f00800f8554000c1d00e824070038440c148404240b900b0300b84540e085128181c07400040d420311036050501c1d070400c59800440e80c0d288410024591494011058070010180d8022814901c0700005002c01c1c0042030821128003847d540000b000100b101c10344010302074000030004c904500c24440342d00b02000321218951546042d040c001d40d101d10bc0104041440e18204070381612040310b40320b071481580c3c0700d00420319558403141c4181d0740c204040d100300c9080010702e4010a004008074849840d1851075030000400100d90b01b02005180c1d00c1e81d0100c640603c0420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 560381798 1250 560380548 560380573
    0x60a09030c1e0b070c0809121011030a15030203150c09101809111611030303010b12010e0606180432060603040201021905030708030a0c031d0d180f0b040e09 69
    0xb41640c2000701d0823501030f03049030b504001c480c1c01d00e40aa400d85d0282498868105407800380b8001940c020385280c4403c0151440020810040c0c07410750001941c15401004091000a224400380c2d500c490340010950a0000b140041034100c201e1414810224503000c07081c2ea50b0044004d00d09004000c41e000c140001407a005140b88144112044100c1c40507a0381c1554090002e8621180302c20440130341180d59a6a44403090401c0350004860101d610030100000035140400703c3e002c600030b450082916180600008840703640f1171000e140070f5005034071600794209501d0207a2806503440c0e4402c40c141030000103610426016800201131030302c030340310510520002d070341d00080112610b406080c000c244402242005880c600900000521440000040081100041e044451800426101404101e407400c00007401848402031030485a80100c000c00034030f40c440d04406419142100c107e0240d241c40d103340c501050701d40e0700541341d4248002010844050003c050907803054403640640001d08104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 560383048 1250 560381798 560381813
    0xc0b0f040209060103091e0c0305070b0405030d030c020712060e0706120e0106031109070908060403050a030605030d081501140708040614030c030a0f180c060206070e03060a09030c1e0b070c 83
    0x10041d0800e180f002070b4610b010803500c5c81141009e1030b04903044502c81aa14101c16540c1d501c940902401b0340181c0000303140031406401400304e140c00f10380107003003054144a400541a095007005494590712445502101c40d802c1c41520003603ca160313985c80320394149049074015246400401d224aa25101041011601d040400c00c0300540c1201e40c483d103929544000c40301c1e4400c5401032901400f80c1014401050b80010091040704c089890138001250789904050b10707414507500e0f600c04601340200040e0341d2211184d00701c2046105040020040e0028541111542c020020440340000001818488aa0040a401180000641e555255141c4905440c003035010240c041e80402d502c0b80f010302254071190308000b80d2803880310035044c0d021030781d41481240080342c1c0c400c46001d809001c000c40e846c3c5210703004040c2c1d1054050000d00d107540300c50046800410000505800300000e0884280001d03940c044007003e40c0401898031480048a41820082810046c000905002e10f480c48a030005a09 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 560384298 1250 560383048 560383073
    0x103031d130f02090a060f0f1704020111100606170c091305070c0f0605150a080a0206030c12090a060e03071208060f060d2c120a0c0b0f04020906010309 67
    0x71800400e8a00500900b10040d0190910071940407001034008251150701c81e118035024880b60340c800b460750714046015600e940c02d06100851003424440003d0155000d2180200490048005c44a554a00d06070328800c0ba12142c00400c0041c40c025043d1030310111a02c0c0382038011291488035407a1040700b00004800c103420341801507030035403900000385240d80502002c080c01c0390440c84010000000f45011002420100c0d0041110030b1000012a4642402c010641c29207842c40010949192103408006035074000030503140201504104119044295401281c01850701500412082a8a20b405825241c8010301d01901d584207000d000040380304c0341c80302c0c0402401070070655203613103d490100e5025810091801c2e0410000104244560309075805024140d010740e100d60b22900714154000204220001d0101c1d2661140340056003c100c8480200000100d9052204d901221a903411401c9402102c404e460101900e00308420b40c14015101603000d4800d00e020020810560b0320300001d1140c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 560385548 1250 560384298 560384329
    0x43905120d1404080714010f08040c0501050f09031c1205040201080103060509101a030c0a03080d18120909050606091f0e0a0906151112070819080103031d 68
    0x411503030b11aa03007403280211800761907031300d007910b1405c1d45802e00088aa03410020141c001001c041010740311500c1080d4141c007840d44aa0001707403140c604401120303280c02420004640c0c480421007035041d0f0341c04001e180d510041c03400c20840040100c801c0940040441c100f040c1e000c17801c003000c0000503a48501130714117581c0c0c0410002001c1d150400581c0c64881d00714882401285495400310001c01141803400500f01d0480440304070704440d07820f00403211118030008201d0a4140100c0e00d171070344941c0100580700600c512032150303031241e40c4400c002a12044080310118076030f078100b84415489405500c0d8880790a40d40185454056000b04a044101c5c00c007100c55040700b54030540303403d071248004410411004118100203a1a45031490003000280315030b8900300039000b6194a4203021382c2c12480c090900c0c80150420711149040d1601d541c1c0002806c031074022003080040d01c0c4281c40001648a698283d03030305001c6604601d009080c0500880264605100c45203503c0e402e6a10002070801030384 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 560386798 1250 560385548 560385557
    0xb01030b0117071a0c0a0c0806070c15270602070c150c0605040323030907090e03071209090204090b030601270b1c0503270a0e043905120d 61
    0x131141940781c0b44034000c120030012107000301e40100c001e0107042400c41c0261030f00d00054507026110031b40107503840d11840c8030050400f4200c40543c01904044d07401160202e0300e000220f0540f418140c401d4250b0000000300f1a00c41e540440d41d070003400034896540000d842a8081d40c0c0f440080c424000c0c040244401000b054103465030f0005041521841b180d80c09a00d00c403030300c01260b80c004004101c11b900121406c07d502e10403039100007a8030405000c0c0d92403803e08080910301e000714646500d1480c04070003446a090200d800e45c001090581c81c801070008101e10200019a5081001014144581a1b00c0614610088801e001e0300f084150f80164500f21109000036180c1c1040c80850840041180707a03a0201d01d04030403c100b4044007000904070314140c0984908080310703034a8540395007019034101e96001400f2110a211418000120903000780c01104001440e603242002c0160071401c1031150b448080c04000141040e1548000240207414116000401034108884156a61081c074141c3c00810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 560388048 1250 560386798 560386829
    0xb04020f070506152b1502040909050606060f04051e03030d0501030204050610021e10020708030718030b060108040302010b040c02011a03010203240a0306230c0910081e01030b01030b011707 83
    0x41003503003011b5a064403009042d515255201104001030a040c0b201340c620303000390000130b4500c1c41c0c074100f1243c01c5104c100b0301600341400d28013802406261031002c01240400c00e503030071100c0d64040001e400c0009520720042015070651040c40309407280a403106019901800d24154a1f07078022854042540140608100e036448045809250000c60810744041a200013008401d00082c4c0d001944182c0843d00c500490090f107418600340c1000f503200141c030803410040400c3c010b610440040740c2140c080d20000c14000004400901125614200d24015039500c0444c0040c1e8404120076141c00e2108400841c154034003414a5824943d55000c1c0d07400c9640e0000c604440755889580001c050b641018003001400c0f107060000d814094400c03082d03480c1c1c50001e00010040301941c3d04031610800c01034040d204200280308244c0304c0744e10151852807132049522603c6080700031361001c0350096018000454540d45075050407000c9690680200800554000a00d4684c40001483c070080311222000c06484 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 560389298 1250 560388048 560388053
    0xc050907080604181a0103140601060203070206031306020315090105010512131b0603051f0305031c06050d05031c0510171e010f0b220b04020f070506152b 68
    0x13005500d0070010000c4852450002e214140914181d0580f841110816482d000b101c07235443c1d94039001d02c222001a8810401800181032082c0038507048951074907144006001c0d95200b00680e00111174100120600b209506403a01e000b0821600500082c20664a807942d6040301d0071140d05c00800e44400c04040240ba88200818000c0e0020300341c0405c61001522902d401000b4043c100644420001c007031410000c901000034020030b0382c1185d0b07010f00258500003880b0030f0070081c1c84466900c040b80d90390342d10700001c80362a0720705c01074181c42c81400038550f641c40c40d200560220789a4907084400515020802500b080c4400c2c44405490508180810b52051407c040e8a001c40c07504245a00503c52500da00c40500305410900400e00d0711007083c0070244a100920000340307a1860b00b50410030054900307040721950340e440907082500140015151505141516110f540441011100d13036001c0707401c10000c0c4401e40020b1610920881d00c07001402058805150940210903000c801030803096004800c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 560390548 1250 560389298 560389331
    0xb27040503040504090f030e03070e160903050d091e0f05240403060b030c011805040218100503060909010507050a1b0204090b060a080309092707120c050907080604 72
    0x3c003c01001032041003c149070001d09101c00304030131004078403002c03140b5a051601103882c03016a4191010707a040c5550704525803590010460282041c071020040c0880421024042c0307142002454458141841c41c045509006505a48410000900b0000103001c41c2c0041075a51b411034034102c1ea1200c10000f50246840d03400350359101070700c580c000010000200b044a4006c03040c285404c03000c1d102211034000c01561140010000000380c5510190184510702c1d0a90103030000d01000020807a0a071801c90201d031074180d0440c0458007086006c0b0800071179107010303824598012040720080c130440c10300000c007a0041c050001c070f5806101d051304246030300c2000c208404c0c04a94005006000464281c1010328404005480d200d00500d599040400c0c54800002203924049010306184015581c1030350408295000c0c0c2a5814140e001244070555030b0410010318015203194003944002c10140d01d4003100034012588018014200b540c100f12034560804c81d0240c0c005030039180402c01c00e40c611240701 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 560391798 1250 560390548 560390557
    0x312050412110f03010207050607110a080f12010602030408100b04020c030307120c0908120c010e1501050310111e0409020406021b0a0b0301090c050d110d0b27040503 73
    0x818003036050702460a00c0000c1c0d1144070746440944220310300c1c800541c103050a0384034040c006003d6501c4140480caa641c400c00d0410002c040003019100044000c0e40c82c0b00c825031005525000781c90b40411540d5513039000c00d42090040915000552811f40b404034620303101c0c6003401c20210811396502030581c45883c1c0c0c4e0100c0b020b480c081020760313075a40b503ea90081d10782c020305440312550038500010700000078000d9288806640c60200200240f0386822520803142c2e04c60b40300c86010b9501c640c08560309400802c51054401c0c40e100040302298104400d041c502002c500304010082d05103054265141c0c881403c49102c0000000c0001d89000116141c8041d4842c0341c1c0045951880003c000412a5000c0346601c2170010b170341c0d22450001208070070444007004c0c80c020240c007040c0c1080100508512036004000d801c8560410f18240407503c801d00d000c407040000b0300030304007400040d510400899803240d80f11109041350306401c000c4200c01c04805201c214244104e00034014000301e811701504100b80e5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 560393048 1250 560391798 560391809
    0x9151005130c1403270309040203012303070e1f0f2904030b0c1b0d090e07020105091009050102190309140615010503040624081203090703120504 64
    0x1c4518250103418000e181044500000514a5480002940d041e50442c0d00031511440b0920360039590401e0405601040c8043d040c0604c0108007451050700c581c0051030091000b032000d040f015004d007400104800b00550020322a0700035080521607817032180c82e4250403941d008491801d51100600c1e0040115440d049482c8142c0b02500001c6d003010f000c4414098588000640c0c0066441e018449425000d680801001e000c100000107241c805080d0151a0101138000d624800c5603404e00a9400c0012032081c020019242000511864001c6280c16800203a01d1000304401c0c5862403150340c40d88407514515142c1615003181c24180602501600d034030060360740510705a03084156002e0000c0a01c500100c030348159225039034a03172070340100344030b0300c80c0000c8220341c0b080c2a01d60b801102d40c1d500041c0700310790096880c603651035070114608103105d40071103690340522241d060407009480c028540a10b02040a000c008001150310041a0b0f00d08481c1e02207040c0e402d402c0d0000c03045d5000e000e190403c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 560394298 1250 560393048 560393059
    0x30c0d0c050114090603060d08120a05181b010f031116231b04020705011a09160219080c0d031e020405300316020a0501050309151005 59
    0x4105110050940d2000c490302601c45018a840c58214410701d40624690710754051400e10005c5c200341000396041c1c4203940304040192810040340c007080501c41003030351031100080d40c0d0410440706040000a98000c842c0040c001e02c0d140030f40350321925010001c05003031410000800340c6054024040d801c10406170322000e0032107489050801070701c90aa00c00100035a01e080396600141410000c011144034503510000140041d81110710211400c020202551908640c0c20840b48002c2007081c0328882c211070701011620074031401c401c01c0182c02d002c0500420a040104004c4140880d00003d158103001040124034981d12880d013840d14040c000c02c0c0700301c401405501c8001402607410b90080e0810307400c458000c46617000440e03a110407400707180a40780c2c1000c1c0441ca070810402180c1c410109450400c0354640061000780c562900716002181032481c07078103060003440110b16154040402030002880c069040d072030002c00700c40e5201c40c0700c0c02c17840200c80060040b4105610070202c2901505007e0038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 560395548 1250 560394298 560394319
    0x112110a0320040e0c1e0d09060f11070b06040f1803090911091201200702031e0c060d0e0a0812100315020903070513020703200604030c02030c 63
    0x50042c0606210a0402803550a80041011121419281034441c14406442c01d0740c1d4a5a28220680c842d46d40c03055002d1040b000344900c12280e000600004080f1113000c2041c5c0321a1400505403a0b91008081e400384c201142c050401400350280c904a58000601200c2519482c01141c020a2034843e03c101d0b860401240d8498400381c840d00006040c403079500c0d100c259588450b0b9030106c49420746840380380e0314200300401e01c03840c2222030603111040c810000070b207000c0c030034007240509036201c140740c070282c4d00220300d07981546020700c03a8080100d141c145e01080c41452416072612280c0b070501e554815140851006c815100c1940241e180308072030004c503640b012050030500c08982001410b4082072040800198009446260743d0084ec0e074081d00030089881c00c10020b1000c0d40110036116050b06c90300200040c6581d078012100e1105500380c50040e903504d03050030020025410780300d5a042d90b08208000c4985000002001ca5000740c140c0f818a24103000da100090420321070044d0306600020300e10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 560396798 1250 560395548 560395567
    0x17010801021b0d090302061b06090f070902030f0601031e0e0604120314040b070509041a09130b1b090612010806010f03020105180102010b0d050f0c120309011211 71
    0x600804a00d841480903000000c40b012600d59030306000403ca07000201e00c40010401818900702410348511180848181341c0384101499141070301c01c5541145a60182c0d014241e0b03458144200d1002c1c0c40030b602c0c20744c0303940340c03007040c51346e611601616103410076230f0300d400010032032081d07100013210540c04200c188210049030f0f050607034920b0103890554200b6038100340440801e00a114000e6080541580040d22799903070b8a81e010042c800030121002e000041100b0642035440d0300c40c4c1c0b44648040c00480100ba070210080c04540341e001400300380c00010081c0c03814045022000c030250b0204054003031080600c031b580c0d50300741e407401109001600014081442d41c482030b00c400703596060328181000c580e4036a0340d940054660440d1840007070302041c401c02103407420b00c00050b20009951018000801c1d40c0310940c001c00c01c1b8042c022002c0e11181c00c40700780310288030018810180c0c3c84070b080f914034124505402810340c5900c18080646d042c09211150303460040380c01d4018400d071211840b0b00c5620740c840b08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 560398048 1250 560396798 560396801
    0x7031b0501060803070804030b1608060907091208210702060c0906070c090b030105060303040b0d0518060403050a0e0306101715011205060606031e04080c0703030306050909070506180117010801 85
    0x500003298030260303040016041cae240c00036840d0482c000340d03510200c40d615441c09200c10b150002e4608030410941e500d000ca50741910240300c0f4074462003580c00c540d0320040403810220545161035602c03404142c04040c04889a0b0028105400c0184141055075502d0440f0020320180700e0583c009246c4100e200002030b440c1c807254404108403105030021b100b15a600c4007055124032860061900c15041070200078040c100c02e0744203039801108100d403080c0a080c02c10315945084c2c01143d04030001400000d8041c011b0703902179102168514190001c01041c100808038240340325440c02241c1008030080f0201c0100340040080d0303140c8035111a2410303400c1d6140c5014090002c4610320a0b212840b5100115a10b03040040c11244100160703c810f444884040c10740d040c0004029209440e000300604c0011400b034814003102c0c0040d84aa240066158030300414401d01002c010701d050400c2e00240000c00c0705403905400c41c0c40c3e80d81d40f140b1040401d5449001a103100f4800141c2e2107440108500200300070205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 560399298 1250 560398048 560398057
    0x3030b030627101d01150e0a020d0f020705030a090f18050702012405010906050f03040f17130609171c1103070b04021504230d0f0506100b07031b05010608030708 71
    0x5013002404118540010300e020b400a911401102040c07150000d0301088450f80078122400700301c1800b00d040000c0751a40380a0743c1005806603503a40002484402071600802d14400904146440345c80751442c0150143c43e1401030728400301d04c503032100c0010f440c051003075101320000b0700e004034817035640c824113803c0c201c1908280c020580070500d4440c0114426005c1c0080d0780080c10300340103ea20b148c1c0d42d070380d600c8a80c0b0300b06281102c8854100301e558540e10030010150280c2c00d4042e0940e6030140c90000001e00c03500056100301c207d030704000c0300c074100f56502040c6031038500d0020300b16141c0145000c004940b0651844403008003400003241e103d040111108480d40514000c440510108100110303000780743c0304c0d0748120700d9091003240d03d00000c0d1002d0010295000d40003040000300c000310f03889501d442d030a0010300719265000700303040140046080d00b21002800004507243e060620913a4098208511404c4130206111102e0080040003000d41151000d40740310300540e034907a0a145028007440d0403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 560400548 1250 560399298 560399351
    0x1409030a0b0a0e1515040e070603020c070504050402060d0504031b0503030103060e01020f0406180b030112020901081c030b0604030501140f1b190e03030406050703030b03062710 78
    0x400d206242e100f00d0004a40b4041004d500d043c10103503c0c1c0c20203003c416038403a001250869140c2c4401c502c24202400340b180100007580300580c2e130322103582d0030341c4c100142604014456840d12082c00056243e41080e03480c02c10042d1000103881c0c6175803d0a031100364842560015801c1c403004031500b0814084050750481e84900c06c10301620740218402400d0340912004030409800034042040924460740c20b1510440c0541c02201c4076940ba540c1c20915a4000d07002820240c94210205007142040820075004268503000340c020340a050b000c2d0704421200c0c04000c010141c503002c1404480d80c542048400465022000b0030070b00c00c1c0f01270300904801c402c0352405920300104000418401c0e0303140070a0404910114030600e003210f141035054060020b1420300d410402c0b070007401c2ca0180c030100000c0c80a000c0549449403213050b1841c00605907000444c03200d01039007050003804034800c001d000c0702441c2103a5001050401d0101d00c5550b00d020014690b107010f150400000440107200300420034142030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 560401798 1250 560400548 560400551
    0x105011202130b0f060f0f04030f12090308030a020a0e10030905120909013501051f0803030a1d0102180f1905010e191806150e011409030a0b0a 63
    0xc4002e80c600d0844070140a500e0700208041c29200091a04d10b000300903648910307540e2403e002030305c201b0894513040340d0411102000e10204400910400c005262512030351880c15200e000e0950382e80d4038060102030072190003980c0100b407503080c4a0198803030400c00319000e4250322280004420050140002e08000e44d02070244604a46014404404070f81006201904c00e4009074070304849500240312446480c45440000465049a03d60041001c894103031072000100d40c41c00d246100c1a604520619502541008050104078222011007034030b5014120705400502ea800800d41c00100b103202940c1c01c100d0354400108005807500410980006003001d45105030360041c80824462085d000130300c0340c0701c807104102c0100300d01d44c45030040000048002d0807002e040c082507031110403060210b030011800c0801403c00034503070342c910317204000c010024403114060812440001410b01054a55118100080d092500042c070b0398039000c42c0d050001c05001c5996400450130082d2070704505552109245 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 560403048 1250 560401798 560401819
    0x41107110603090a030c06090827010306031e061812020d030507081b040f181b0c03080c0910050c0c0f032e0606020604060b01020d080114040e0105011202 68
    0x41c104441968803405821000f44003044083e02c040d55007240c0441c2c2107030b24603240d6401c0310000b1003403000340c99400d45480304084441405142440000903420300c5d10704041c5131000400100e607400c04c8817a02c00d150104810040c0240c2d0900d400584034010340a00851100ca03c001c040001d287c5a034103000c241d942c2a2404090100c0c011815500c060300c81000007900d44001c5600824410050042540d0003050b640c905540d81c80c0c11403041c03071540c0c042070800c044440d515058201324040e41c10010a041ca00402600d8040c001900100322084013400700840c1c0800541c650301c14208450800078014540940d801d0004c03030040c00750b40300400f070079114041d10380c18181c141024880c4c50603000d4010050024140c0c0030821100d80c03401071303004100d80c1e078441c20b08445149080c4100c0c40504050f80c080d00701480d2508040c0191403508903841c0c11540107080034001a54004095030648807400d1030105c2424191001501403d08480d00c689194681400000c0d02c01c1d00c0d0307043c1000e00703109440f4005d02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 560404298 1250 560403048 560403083
    0x6020f1005060f0f011e02210c0d0819020d0b03190c150507060f0c0f02121204030201021909090b0306240d0c03050d030e010b031f0b041107 62
    0x103442090301c4a94010303016109091840c900071520044000042c50031b2800c400c09442c5450303002039070b41c2010340580c0150030204000ea01c418044000201001c0e042440c14204c0310b03000755641200d001c80c50402460102040101403508801d10382d5030255102592244411345d42d00b80180442500c0ca4480e2040e140000710211a003803900743d110b84c020301c280b00c0080c80c00fa03031190842c4083c941d0204002c3c04000341400200d20348540c80031489240c2000440209001d0064481c4c14010581c0c025540310700400c61b4548046421980100c0250301000c0b4a903c540c40c059019001d00c400c542c84882d04040d44154080c1d10010140c1203510b1007a0610070742034001d05264807860706079040300c05050000603170940c005e00903000260604000d450000e040c6085e484004214415400440e0990061519006043d6040c012038042c4c104100003081200d0b901400603617175401c60101c00340c590780b00f5810810801c005a00c050002807000c1e0003400075071844820034a055008440490301c1c80b44040e140c404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 560405548 1250 560404298 560404301
    0x15010f0906060c0314030603010b120c090615030a110408030a02060f06120601051912050109120302040e04170d0e010b120a0201020a0b0a060f0305060f090c060f130b0406020f10 78
    0x2400390075480f080c04005e419070b140041395000070102d5800d5901ca40e88030303025841e95450302c1900b190f04000340c000b10315440308206001d00c0280451b8402c0c2d002143d480c54104e2503000700ca8000c100d500001136601e9980e59059420300559104e40780a00000c030b05041300c1d44d00420f00d5807040d0014921081c0e103541d03107030821103036401c0c20320841d0682d4072420050050381003801d4146c11082250b074031600c04a6076512170b514013070044541142c199444844c0d1703d04001c18040900c4a540f42410f0070340c1023600300308603040c01500081001d0308031903070520341c1d181c5400d0050803544030412441c001e01c145144101c10034064001640c00da4041e90044d0100a513406c004074180101ca60b050b4040d00c0f401c03005843e03401c003912026154001c1660399441c0054200c51000010000318400c2d0060001e0780341441740c0c2d11300b840000b00880c00f250445c0e00a03000e16500c2404460a45d40d548100c03d842c1c429504450000c0d0107203401880d003a00e8001400b21300f241d0009800c12111240744111041403010014580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 560406798 1250 560405548 560405567
    0x4051e032a040518120f070c08030a0906080f040308131203200c060f0c040e0420031c110115080c090c0c0a030c0317010b04050307090216080306010215010f090606 72
    0x1d0480d0030000f1003010b40e0050b180100000d80d80c10007018201070650710ba86013204404d50051949d40d0000800c48103180e04408640010300450406036018507080c1e501c0105010014001010861850000b58140002d407040d4030000c1d0700550750701000210014050018580f040030442c50b1092a40403107844c60440c41203c000403500d00c0900046e803104484525032070310160140c1c005602c1413001040340401c508220f40300b00e00030a1420741210382c0e0b00d02101407014810025000380c11412200d8a0414a030400214040403440c050401c022009262401402c1c102c170804850704840d10300050034a07001941c240e0100302201c5e0885191601c1400341040d00c24050320400c2900b1101c0c40d000403a0003a0820142c40d8002d0900840b0700c8160300141950b0003098020140c1010b000c1014491820b013080650040e003000c0c5411454010548030514001403542d00090080c01700000060f1136034400d212802081c030076910641015610b4610520a0840501500a42a14002002501620035500794 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 560408048 1250 560406798 560406841
    0x1050c0405090402120d050316050c0a0201050d090f1110110a030f0909020d09051e030906070f050d0519140307080702010e030c07080c0604051e032a0405 68
    0x10314262030442840300c1c2c148000d000340d0f0301c0042a00005001075080c0084015005281c1d1020b036640b07030420341980700301e0a21904604002062040030b8951600294004800381c09090041d00c80d446c1c84040b002402e01850002c007400b400c01c0081d002c01c2801c10488402d1300c0308413504140b52011f5002268808542c101c00c2c0d146601010044012034006c00040304602c50360b24141300d000d0380b6207003400e081e40d0120b804004540c0da20320441e000d10909222010341320450110601c0c10301d000c0ca07142c584c0c0b40603440d1860b10962001034044204005541014070050344a402d03100001c420740c2000e401600101c55801c1c10700c480040176012a4441c010101c04042910407240c1140c03103005084400142c010085402d40d03507144400c40210208101501d01d0b405410010004c09081080c03580c184424480340138000c8030184000d002e2941c0e4002c00f20002c07440e5848403003202065400203440c02e80d00d81860301102200c00c600401600c03060241c1c400b56a130903503052000c3d44074a5445e2200b2007054845 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 560409298 1250 560408048 560408071
    0x6050f2a010c081b19080a1503142b1d1518040c05040905061318060e010c081b07021c06291c120201060e0a060506070227040c14030105 60
    0x6082c02c20380945070341908071110707000026244c0c230170304440401040150005c0e104520360742c4040307103450010000500041600b1081c81c44480c184040411007007104003c0e6030500c505505140000002c1000c034015900c4e00a00202e001c10859503010100d50100391140301d400d4407140003800354101800740350f0304900c090b03540a2a00d4078048151004040183c15a83d0200c202d6115441c89001401980b80a0803405600c4041c61014078003642283c1042c40403445030b90500301c810f070a1035000b88409a01c01c4032828160503481090a620440e481002070003035001200e0442c60022400801303c41000ba0310a5130100985007400800300007541c150800035081c01e446080e002c50031308101c0345440e40b080400c181e070600d42e1200e9507240300300c82e09554074100603992541c0400012060b2110306401011460041283d40c2c20b004c08994a17204402010740144508400c04003010f1211207400710045809407038210a0a003441c02e0800c0c81d005100c0c06a0440540364805940d00d010704c1540c1c000c0750100380c2d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 560410548 1250 560409298 560409337
    0x9030c020405072102030a0c0e0306010b091f030603030905030a020901180609051e0f04080403031404090e0d030c170a0902181501030606050f2a010c081b 68
    0x1c20028110080800c4100310040d180a0000650956441d1035030501c000d0158030ba1800c90103174411154107156601c1001a048230500d01600c0205941d030544031440c40080d5110b002c60041041c090180190b05803000100301c0058200d80c2c180d000300144d9200383e03980b4a200743c1e11800c040c3e503000d10b00d4000c2d601240d0f4200400c220384440680c0030701111140008104660358002c81811580e0440340d40410540f54011955515605c000c00c550041e00030322421414105030f2a4115903000b035000081c00e100c8001d0000506a901509642c000d00e5070050a020840480c21035a850302c00c070401200205c2d0600a0090602d4011504542028210351200880355038244640001c0e004007001030780c100143c5c2150b010701c46104485d4038801c004509001c902c3c406010001004c40e0525448102040800c0c4920901b00140b141142c00c0c440004c0b8281c80c00307592804035400008080c03159502503600c1d2494010340b01c0c2d00b008126100c0c0c2c285d0284440c00701c400c001440a40d104855400c0e10856800b40e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 560411798 1250 560410548 560410553
    0x914010e120a050703141504080c10090807051c0c08070204060f0609170d08070c05010605060d0905060a050106090315110304111c050c1012020a0906020f0109030c 72
    0x10349030302800000e1428400a00084401d41400c0c040001a1403d0b000100b0900a06c945030b4100808a01c0d1000108400e044ea00212010042c000d0070082400400041400140c0000c0210224005446c503007002041c1080c07400e080c195110a204442c50302441800e05124070024899141e0140240c656903002c0d80140c0c0c403900c0780d60000c14202da1190340c0d041d0201b1030580600ca4880544002c0d15201012802c1a200111840c2d1601c520803c0c3d501c0b0380d00900c41c01d980907035066006412810a501d50003440e02d401e501601142e0802a0400070100325010303094159081810303004d0283d01031740c20503100d4420340f4086d00d070709002d1240800e0480c241000029030b001c10461001e10b1951b00000d00070700e00709400245030700a8405072503261002681d0382e92441c240d02d41094800480000114200c500e558103616a04800c55262161844a240c588194020000b5941c0001008401c540d139110040014003111040c1c01110b0040c450140d50700c40f10481403040c880750503050789802112420700d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 560413048 1250 560411798 560411807
    0x2010f120905030a090302210a020f0609090c0a090f0e01030f050f030a050711060304171605011401060e090c0304120c1401050601080a18150912080610091401 70
    0x4295500c55a9078503440c07020880c24030207407000307840c0703652103008980c0765004114081a40700c2220002541204504440c000001084d000c455810b942d005111012440010b22500903c6c00c582e030060b80c10707400c2011011008005003401007007a160b252504c0c1d120031030540c004441d405025031000c1181d0045c00030880c1c030320110004034440e50032901da019500840c6425500030700304650210f003002c11042e003000b44c0509034940007241943c21605502d001d494002d01940b0700340c800e01920b0000510344200c055621050081c05801c00003e21101b00754006890110809116510000c7c1e08100f13009078a15100315284d014000355055181107846e151140c0c0c408444058249040c46000c99582000a00b403031181e1001c680914000640b0b072030820009070900030018105081c961614406511b0420116155203034907801c001d50040d140d181a51450050804800c0a082004c8001c400410705a001c0301d0140714241c00e584075158008100000e646140190141902200070700d2140c0d90254400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 560414298 1250 560413048 560413067
    0x17030a1d030c0624030a0c0602121804090201020f0102070b0a060603020a02060c090a0515070c0b040f1a161b060e0f09061909020909060609012304030506010608160c02010f 76
    0x2030036545131040307001002900e84003001e80c0840785400c0c0c8500401200f0b4050000080350729412220b14038000364600714110b0403070b400c0091481540e039108240b0a69208001c01540c90340050000c65440400c0d040c245003800c001c56411121a003052000f00b00fa91081c001c0c3c1b4070181440d00100040d407a8000304076103c0e04441580c603003061052600251030783e41c2c1980400d14175041702d6825a03034922420080340c0103c0682141083d4001004104401da100d48030800c111880d0241c4174807184100328940069120700341c026a450480c0c1d05404060200d04100e442400414070a0b09100541e510b00c15986065420031942e4011401294540710f030500e00c4200ea403000c0c008085621520b4501a50320f41c452494108152055020400c0a81420301101d4990061000c440c02030030b00d000d8000003880321090600c038001c64101e0408040710702d90b440c000e40b40695071000580b0316a40e141d0b04010503941c002c440e00401c607220b10341994442c901034604460800d4060b0760300c0d1320342c082400d070681e030301d054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 560415548 1250 560414298 560414341
    0x30304030804051e040612120f120f0212041211010c050f0702040b09040503090438010504120b0717130b070c02060c150c030106020705090417030a1d030c06 69
    0x80814800940d03545d1442000702821020b00c0e0781d0b080c0341c0c941c00c0404030817040111b003c0074040e80303801d0820084d4000d00082042c0499440205240306410002c401034041c510814050280390000c1c80100404c0142c03030200e4602c0d5603160041c0002280a41c0c0c02c0c0c0d1030400d40340000c507804004071600c03111004010040c1a0000e032011411060b500d0115001640483d8151060703040444d08104529017801088030300028a40e02c0300c128800035820ba9905168000414900ca03020072044a459002c2d106442c010034800110989404c5541040114114200c0f0b06000241051103058044001152194080c544d08265002d003100d4541c0d42940100010740032030148403c9071841c0d030050b61440000d258141da14009010f1004101240e807605c0d0030041e1001e28010340502c0144405580003c0780c0d011a041140c601c2c125896504003000703081c5508074035540e00f00c0d00208100070484c0315040071a204080002c01206071140c01019500c4e8051b1091803152500914080b800c40e081c3c40c44070004521 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 560416798 1250 560415548 560415589
    0x702120a0f1403130c1403060604052a0a0906111504020f150705240708040206070209040605180715081b210603030316081f2303030403080405 63
    0xb00d455101410030b42088403056450800c1075800020403070341e405807100403c03081098040a843c41e0001076121000100640c1c003440c6ea0b40c000850082c0910a038404a207100020480900d082540c42c05580d88002c4c142c10110309003003070008040e8480d880d05500c3c4c0c10344201410a200032342000803220350014200340c3c1d2241080c18000d0080d0758240440c1035483d184010160350305d0040c500740c0d04240d0004c401100510500d8145191007032000411030703002620740f8014005581d5480028100e0140c000d010b13410080c41d00800080101c0340c1d00131030051110754010350700c500b2001c00c020341d101554001c10000d8000039414042e0203008a46c03081c3c102460100c1000c620b044110810059008554150300400c1c01352000b00300c040250088a07000b00003035024518514020803a081324140702075401041144500011f91420945401560b1103034020004000c0e02da81da08041c041140120b198000c060803540b00b0788180d04e000001c4601b100d034401c04c02c0e030400340b51904002e41c241d4410403524155 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 560418048 1250 560416798 560416817
    0x160e06040c090b3402090c031003050115061e020d05160204020d020703090603020f0313030224090706031e0506060408010e011a03031c0506030f0f07050102060702120a0f 75
    0x3c101400580350141c502480104a0f010314103d104240311440080301d0301d48592802c207809611496246a440350103c007000741e1b2525581003d40f1142c1d115840a081546808100c40200c4000c5e50102c0484203141c1e07409001e0900e03051100300f400c1290403601c0169100c00c0f0ba1714030050084024010300604410500402903513a000704081c0e80c0603241842501d540050220304140d00004483c0c0039081c9450118140000608548007a10020b03000394050361000740300c40c007010b108100c00404e10385d0621418002d640070941284a030003040c0e980d16010b000d01324000c64228841e1050a2003c41d40f464101c1e280b0301d5807068080146005000c06400c40c00c20400410114024050348000d010390000018910110096011b94040c1c282c00041c132940080001c040c0381c090241821103d00b441034800a0152581c100091506114000003540c501807c6045036100f10702052510484070b0030b800343d0b602aa5207034000c9844a50458013089511010321004e800c452141c401c48849080030300744003c19 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 560419298 1250 560418048 560418059
    0xc0405060f210d0203041206090609060f05060307090e0a17070f0c05010f0e220204050315010911070314030403050706050a0510090b01091205120a0c0302160e06040c09 74
    0x80b06440751040a40300350004041c08144040040d03d603580d100d440a141003500708031481c40c40c80c10085000c0c00207234941c800c1c00c05101039130f0310030003055510003400c006c042d84144c50100a4407044550382d109002d81940007840c540b40e40500c0d91802441006091107981568840b0b9030202c8030070580150308018003562001801240c035090840d4050780e60000764038030b40340005000c031a0642400781040301030500e040040c4c072031050103140c10003010060104100c2c0c21942c10020300842d807125505102c2c032030301b0303500c0c01010408075410784000d04010310190f5410050012a40300305840280041c41c0c01c1007448400540102940c1c0044c824038110745040c85c0c0b9143d40c820f650040e10000c10381d0340d03030340b047c0202c05050701c800030001d000e428005c0c8100a804000a0103170502c41c49000403180d005e40c01c00c01004414004558009800c10906881d1f00380564020b18a840d0220201d01500c0f03038005140581044010354801c550085400d20034655030b007420b01c0007800b8500341c1002844481c0d0000f00c0e2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 560420548 1250 560419298 560419309
    0x1050a031403041e0e0702070f090e0a050d0309030e1c0f03030b0604060f1e1b150603030512010b0c0d03020a0c020a18290d020111070b03010f05060c0c0405060f 71
    0xc138114494403203001d003003240c1c2c5100d404029081354195888410100b045002d003540440840304943c0d80020030445030074100d810b203101c11100402500401c454a016190940e000080c128020381d1841d004403056014019103040e990140d5000c240449869400103034020990582c03a031181c0750118003034000001040d919000383d000240800c030342c40c0d12002e42c5580210103114611001c0328003061407c1500c006020303c0b10710951406801c8040708040c0511001502c5440703c030a6030f28041000c541d0740d0500a203d90480c2010031604100d4000001d04020302500352921a128000605010f0b60074803407e5009500511070314050241e24843d1402507034480c034802c001807242401601c1010083c80e0040200d8050000c0c151017041c8910000003070720ac600340c140e1114035007501d201594800c00d00060b80e40052110b00d513001c0d88940700011541400076000340d4101c91040c10400c400d5a26441044128058240042c80f1544403010440062415030002070304194041c04401c03c4e817080384003041c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 560421798 1250 560420548 560420579
    0x220c051c0602030a0f0e0109261204050601050a0605040806060d0f050a030e010206061020071802040f0504184808010603020306180c090a09060f0501050a03140304 72
    0xe1145c1c0e00c0c2d0030300d40d4070b4105020b5459402c02080c000c12031910a992003800342181181d00700121154144a140c100d00704808507060400060f511003d285030500d40565116001d00a0318010100d000e00013500500580680301a07a4240e8081d04e140e40e550000d100c0c04091101046d44da0030701c2410500080ba005101c4104924040e649000354400500e00182c03402c08003600c414011600d0038642100ca036072140500d00d40001c030445104141380240850742c50940c1310340046021b2003490070341c0c50302a80c0035402801110984070001d05415a510100000c880c4500b4110417180843e4522100007060301c5200b00c0300c440f040404182900042e1400b4008000310b03c0910328401e840642c1043c0404040320040086c103050703000b8400d203403c40d40480d80750b44003e4116414122484444010310400b88518050b00d10090040000e516122000c480030706080841a15001d01d40501c0c012004064001c042c1650b00c041d20320706403140b4590300c01007116010780201c03039a40414400403e40740079440001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 560423048 1250 560421798 560421811
    0x105131a0409080d061a0406050c0f011508060601030218040203091204080d08010b0405030a3c0b090706050301060f020304080a0305130902030f07052d03220c051c060203 75
    0x140d4445644d841038004890468002000502c155400688014513100031a020340b0404c0c944503840342100188140b410015039042c00a55090002404103144601407110444080c0821100c00e6201c0500540807441181d40100044101100a100302d080c650000c5801c0090003044801c41d5582403aa03030a16041500301d42e01c0754000426905403607522030895400760034042041c41c90f2500c0c210001c1e9640c824404000e0a5000c044110000300c8401081c018480580d401100c0b03490011500c0c01c1c0410800034000c554546510010448400000806000355005600d0700303441d40e424080c05507501598401c3c031601310b05c4100004250302d8018014141e045119032200c0c2d032120102ea4554001c101182c010000051051007000000d412400d001078001a0909100d6650b9a10311a00201881850030110310044140c2d00e00343d00c6594400214802c00725a0003042040042c1030820310702c0c00c80d191015010340d0b0380100500030362800d0381c118100c82c603800907030040340045581e03250160307041100d44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 560424298 1250 560423048 560423063
    0x1b021504140301060e1609170c0112020a021203060402071401050406142811120402040c02010b012016090623130504020103020d1805150105131a0409 66
    0x4024010700c1011140520108030002d0120a00340b903178a803004035000340b1441c0c510303d00d0180da00f13019001d008070101404a0b04400304013045940707184e69813410900391442c0060040d44660740403c60070300c2601c079540880c0e40a000c2c00880030000f5505a0400740000342c0c000d50802c4890009111100440c842810003400400c0e0362505003080000c0b070f10b100094503601e040039020049144060040c1483d40c06002502ca84440d560f0004000101110740718003180c2400012016445290180b145100e98400c032011701c42d0002d000d004030b090301e242c60800740c0869041c001080454814580820000b560b410403a00190050141ea02c4102c0ec698410008640c2e40c8a040c4000040c1c1610000c01c88103605419104544090101d0305d800f01c0b0080c0b0500f01580e85000c1011a8070940480d445846070050030307c900e03a040c00303000805480340031044505100b01001006030380a515681d90403200c00a0440142c203600c1e07407500c40607203007451400a02c405842000c409542c1c0d5442400c00040c001c07540c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 560425548 1250 560424298 560424307
    0x10030f1119080c0a09150e07170405100b03010b0f04020d1b050301150e0604120c030803010b0d180302030714010905150403030509061510020a140f15040f02011b0215 73
    0x103101078131201380c1109089504251000c40c48030b2045000500700e801c0022080350382d54598404498581100003503454481070300e8244804c1c0174000854031041100003c08000c074028000815007243c0c032042c00f4a40110054901c1d5a0343e01d0542e000d03050f05411600e000c83c8002e12141d0000b030100d8004452004a03401000520410300310034101002c106150810000030755400c00018007038000e6226040c02d41c042202c2184c00c200f40c2c0b1340458002c50384080c4107512540c40c0c402c014041d03040b6640004200d4501030840c502c540d06001c0080c103858054000e98a040c1c481d17220003002c060303008000006507403110300600c0060000c0141020601c2c007140c0e00a480c0c00c092800800317a0324050b103940442ea00c0f0606111080d142214900a488021130f48501c01400190003a820014900301c007038044152043c283d0580c0b04003060400010040e64191004a88015041d0910381c009880c09007544801c0c1030550019400f40700320603041d400c0e20051a4088906a0000d12014a110a04820740c1000304 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 560426798 1250 560425548 560425573
    0x303020607021c0c020f012c0102011116020603041e06090204050708091203150402030103060b030f2a0a09020a0c0b070f0215100506040308090910030f111908 70
    0x804140090f0b5200303a1160311200c80c1c3d100602158003010003a200301040300b00200180e00418040486074070000700c814030602ca03c1920803144002c400300c00e02550a0010404190340d1200c01c42e031090b0500203411800941c1a0240705103908018000c4602c40c40c010040d203c841440018100b10078469140440c81c3e00301417041c0b10a0b00d801501e04030078401040c0c28000780c0500415680c4175502c850f504152260b945500c00489602e40842c1648c00c0340c4000004414054260003010a05205408407521604846011a681c44443c400300160041810620000c0300c2070b1002c0c4210701c80001d11035007c15413500a031600326404240c0780c101003a0f1100c4102c041002101c461684201c20341015140c0d0745880c50040d469139080d1991443e44460480050300344100d0302c0c044005400050329490711140c5921340482154450b41c10288101309540c00640c0c5211130051a01c1501d030f200d07001000740c402d11b65402490b000840c03912603003e01802091200d801581010000902c000e10003402c0102c0c824 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 560428048 1250 560426798 560426803
    0x110d02070305090603010915350c04110c0f0c03120901020a0b150f01020705031f060e040f0b060303070309150324060e030606060405091504150519061b080c030301030302060702 78
    0x2607001c4201c01c4000350030341502000b1314400c801c20300307880c0c07609200d031070303271031030019040c030300c545503415881781c64107400304038042e5040b01420084040c9412245901560a26255545910302c0c900e64154080c04101d03030441040c2001d00b10001041c0100e409580080d562000d0f80360086440c00300c040604a05a81c0c1c41c03030000030305035489400f0b001800c031460034100465203c1041d0b4843c0d40c40744c06c098519850008041d4008002494031844d01c01c180e01b0146460024807022400903100c440c044c40c0400c03580d180c04400c580300075503d43c0303075040f09500e00b10102c41c10724004616841030540d2040100e948084082d90502c2c0015a5007001040d00e080c0080540300480c124501800b035401002000120348440381101c0c2078403021241079902d03030707148140f07040c031b807002a00060f400508100c000b801d0442070000500a40f541205c4000c40c0340092009901464014418040010104941440c900c040d41019504c080d024212280c40d0a14103500c440ca07650080c0d0040300164054801c00000c00e506 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 560429298 1250 560428048 560428091
    0x20403050118051005010315020c0703080315010225060c060b1e01140301120f170a030912020d090b0a02070308070c09270809061c150801110d020703050906030109 72
    0x610001700590350460715403c40074044c020090445550015400c6111741d420482038009560000c285030341ca1424455401c004280e41072164094230610702c5d00203c1951030280d00c0d400440000746850f01034500042180c0c6201412011380b9002d40d40e034130001c0c0340d0b2a104c100740254028543d280100ca14241c000400c0a0b100010341703400c070142403005201044600c0300c40d00780503030440d21b01400f12a2a04081e5400242260f049403181c0c030000384030108a030185c102d600c40358054105030103081110f041c00d030303192652920207400141c004c175070174440b0b00d01000c00740a0a002c035104841d40282c90b55a191580d6000080076a40080a05003c0168203141d014031400c240c402c48900389504499100070bd90001180301c000c100081c049505869910340d98140c0d85075410110440f00e0341544d90300d600b40248440c03d00300400e58003d09002c5112a4140076603980d00c0310b404d1540f803074405000703081e01c000e4024103002c03410003c0800c0b607043d0940c0c40380050340c06040c0150340050b41c89110150001c00031103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 560430548 1250 560429298 560429323
    0xa050c150c0705100318030908060a06120609050705060a09030501050c13060e03030904060b031b0903150630280303020901090308030a09023a050102040305011805 72
    0x1042060711900600030030444200c8005660b500d0039601c40390740c10307000f03000c210b00e200034103600b036104880905070301c05c5880341103800e44410b13a06143c17540c002e85019030ba018082c007002e120b100c1c20090000f0b03480c3d40c004059140244260f4036219107503c00039240d07030f011820180020703c00c2c0d0000e00034002e007803242c0d5410000407880103107040a000540c1442400c18031680c0188030703040c050403030b81d03403002d0040710034261005100b00410394444a00f540c0c01e8105a07125455950702402450690710320508450984400070700801060b000030340070401d40580245156000502e12040c0504a005050029400c180e00d140c170038000301003004040e1510800c0c8182c103091101100700905246054800e5030320707098240c034001da41e0700d80c000300582300cac0c412585c4002d000303e20000c1000f1000a06030700c1500405e200f121103050402003c410b42d03021000c241c4110f51107540301107607581001804030a400000740300b10005414990b032611041c0c219290000e012905e0060034044078104003050040b03021020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 560431654 1106 560430548 560430589
    0x90c01021e0f06010f0312181404020d1404201f020a05070303120617060109020c1e1b060c0d050d14101d0403051c06080a050c 56
    0x41840c4015981d400004564440448c840c0c01503800345000201100c84d00341c14040703402d0720310300e82c0341410364019420402e40318145054000c4422480f00790034030241c1c42c035290400305500816004030700481500b102e200b40480da508041c0100c2400c140e02001344185100c4400d0349052842c4c98090038a10178030600208041c0d01c00c2c20b00d02039840061041c4155640d4803520440c1c1b003101c0050800a4219100601070058654050a508186501101c0b894003440c500300e00381c100740700e0610504d60041000c443c25090f0f0021000104203096403035520b0a414103240035111000341052500304103001440314400304a03a0003903805d030340501d00000034504050103080d001801070f228803803411642c80c00c00c100040d6036030043c611507a05903c03041e24003412841c285400055498031120401d65800c00403a0b085010000000302c0d40c40fa400800c0c810a900003002101c20340b000504c141d20 = true := by decide +kernel

theorem cover : BRFrame.Cov 560251798 560431654 := by
  have h0 := BRFrame.cov_init 560251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 560251798 ≤ n) (h2 : n < 560431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
