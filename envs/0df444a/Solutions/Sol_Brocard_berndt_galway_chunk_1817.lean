-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1817
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:47:03.226987+00:00
-- url     : https://prove2.me/submissions/819eeeb5-3ce9-419b-99d4-4498b98d4ebd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 326618705 ≤ n < 326798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 326619955 1250 326618705 326618707
    0x903060a0c120212010302061c050412030e0c030709020a09090239060c030406140a0f0b1507020603040f08040305070501090e060306150a050a1e0b040315090204090602040803 77
    0x1141c050071407480025a2000280100308813084044144030050440394151030341500c071000d401c00300500300701607220580030070b160404100038010290440d260145042d1000c015407004011001c1d110510160160f4150f40305940070000d001d1a540101061062490a80801c0d5180c00c0d05505036800001c041ca101002c6045900a00702c075280c484100001e04501940c441c111142c031315440c3d160007000e2083d012004070010301400004e40000304614214031036480c19240601c0fa80c0b00170032100c40c070800110b1030b140c1035100c0c0d400c040312a903800740324001996040c0301ca40d43c200049540004d200b00c07024140d0044a1000a94400282000e54444d00103001541d0802d03000501c03040032544240e81c0842e0079024001e042c3c8001c9042074002001d414021074035170503807003c1944404d031170b84426041100380b20000f035907000340110403203400c903404048420640d85040c4041e16000e05d0001601d8820213480c0d50a80344502d0f030182c0000d40c4040c0011132540c0403601c0b20400c07a00103500c05041500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 326621205 1250 326619955 326619971
    0xe01090b0d0e150708070c05010615031401050907171803190f020705010905040b01140d060503070503030a0f0807020c0d08030f0a060b0406031802030106060f08010b0f03070509060903060a 83
    0xc00344012020f00e410b101c52040c20349481c00000345000000303407080c400c1c40b440204120038010203400c60343c0a020000713041d001803010814010010801b104c020f140340e048003400400c4503e030004501b8042c00c200e50307640a40451004446c207a03407102404600c4101c0c10b40c01e9488000c94240040c0c503225010000030140303502c0702c480c050521464249010115041500180a40c1c0e8000302c1040507100103941c00100d01d00003900503200500e8464205020890200707011040d01140d4000ca400e40b80150f05440c85156500d007816549e000e100d00180220f02c1690300004118821410550f112001e8411200e0300b0000310007040c05081c2036101039900000020030007801c180e5208039544c01c41c80c401010407803146050940c2d8040d00036402401d0405480d030700c44401d481805080340b864039070000e0013001081e50750b110217050808003a4000005c1a0848000140310030340c80b040d5941e07100c074541f4603495552141c0007102c40394000303440294800d03070034002c40840d40c4003044514811602e98100091400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 326622455 1250 326621205 326621231
    0x80a03090602030c030711060c1b040b0a03080d0c17071d0603041110121a0a06020607050a0e1503180c0402040302010c11040e03070812150904030e01090b0d 69
    0x1031041d04140c0030b541c820882c661446000200710351078250480302d40440b88458400103900c51003004001181032040e07052a01660481d00d00c40018003100f05d40070861100707003006001e1907003264800074185c40c1c4140205604c0c0380d62600a10b1810100307241c000c101425407140703440480000d1707941c2d60014213103196a10800d1203801c00c2606840088500d070b411460b041d699031130341910b0001c50a0080d5003003081202c106004500342c25454483c42e1003030201c010300c426108008544403881034031404103ca000510f090020500742d01561855031500d02d000c001179070985404040c80c011513002034101d0060325503040a10003945c010030742584d50701c076034007540365410380b0701041308202c41d204a10401041005030380001480d1881c5030301161200707140ca661f00004001748418000d04415000011301c0b4020000840010104504505d0361200c80f911034000c180300c82d0b900d105103503410600d07980c0400c010034010f160b14112003005142542509499441e100041e821080c69003103003130703200c40f090075040b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 326623705 1250 326622455 326622467
    0x4090c0306090b0a0e0607030e0c03070b070231050907031703070905030c011d0301150806040507060c020f040902030a05030a0905090f04080313030509030706080106080a0515131401080a03 83
    0x301d410070380300b8000e05c81810262511098050311020605503280d180c542c110506004240e09203000409860308242ea4804118483c3d01585040b0311071b080d6090003c03030002c155a80405200743e4418084881104005024010716001c1c1500401c0e2185c00400000103220015074109540c1840750607490b418001d402801185191f08002d1080c3c108031102c04590340c2c420f0459440c803045940a8141c82e0140f40840d00500520409002d00b5141c00004a020500060700600541c820421201c146950b218101d071042c070000d800a42c03240306109407200310300d450b402010060340000d00f5181d085c003030f5640304e5246030302440f141d03c0810001c280420040c9011500c01340d100000c010100c895140ca0303924400c03a03102c0241840380f68142d450f90304007414454803d40e000440d000d0200e96031603445102c040d00c409000d02c01e400005000d54005194841540505030280160442540340340509000708440c3d0720001e00c56518669607010800500b10400360928000d00c1001c024044041150400a140d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 326624955 1250 326623705 326623711
    0x141501110a06020f090907140f07030c1403190801060c0f03021f051806041a09070b0f0301090f0c090603020a0e040501150201050f01080a0f080f0309010605030106050f01050f030604090c0306090b 86
    0x1440f100c003042440c8d28060310200c500101030b0020190b0350740440e1074151070380005500d02400c550600c000c0901d80c40400001481d8401c00b0300002e0805080501044030540000d00070000010f17112114100003c03400c00303068540038424015141003008607440b01200c0c14140d07a10000094803481840318000c00d82000050707165014020f84450b203066254411907900851560b40f05c924401c000400700e1a003400130802403c0480100c130303611802c0c2e4550040b00e400038025008591300e40881481c0300c407264482c07002c140c0d0b2142c40c2c00b105540f030540290025084603081c0390501040031a12209590f4601c1100d02a081b840c6101c801c800085a00070308681004004034080c142920050260480000790704c090340f0351214440100d2041898010380502800382c0d40720101b8008001d00c40b00c841c040d0440340a65905400802802d0780c0d0707004001d490240440c196001c078100b001a44061107840c802180d2022000d88080303548125a0b9856071074180c95030054a0b000d94400040f400c0007510440290 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 326626205 1250 326624955 326624957
    0x28030c0306120819020a080a030e010b0603070819020c01020a1d01030204053a0f0b0702010203011d04080403080313060608060105060405011d041d01141501110a06020f090907 77
    0xd050100b036a1524540d104010b002100413908030061103001e4401c1100314915503018140170b403180200840580500a04100e60301154202007180b55242000000e50703102e019141c0d55022179032114001c04220204d0742aa49241540810082c06900000d0005000700811517549004815400b804181d40c40d81c0030f0b11442c1010300402c0104555a12138400090001c54102030030121202c1001c980c1a426240c10000c100c6140031004400b808102c1c2c00042c8031900030f0350006500c4e521075034124200e101c00d000c3d00b4140c0700c078420908540c40e50204031603400b80c400d80c40e40e480d15450f40c403490342d00d80080710002c0e0840000c1500348100040ba00821000307008280007044503504050000e08280128040c0e5030420001000d105888007041d56010000c0c00040c1041000d0510387c070704884907603021280c078196507082500403104907859504040c483c4c10840c0c5000801c65041f801102c0c209215500030000f449042c41c0000030a40030b10080c000b415282600641d02c1d001d10003800450280241114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 326627455 1250 326626205 326626229
    0x1911010204050105040b220e040302060708040c140105070501050c03160f0c08030a0b09070306091113030b060d0506010801020403021305150909150a02071e0c030828030c0306 77
    0x2c0240d8005081c1ca09444e100c0701d50b00d0325501c09000c08000f03050786168103064144203a10024a80d551030100c14040c030b019509961880d91240c10660302d400040d18002c4c000d00d100c400400440c00c509010100028051410611b40803450300d41509580301907801100f107400001c24840c2c01c0d0341c2c8100d041450003a5040c52400c1e00345101d4050901c90b500e60018040141c0000000d1019480703a200d14005c61000305000454140500010014006070140d03031700c42440c10703020903080381503041074804485003003e100710030f94190380e18042e11501c0a4801600b0060102440001032024800c840c00f0740044000142c1b164610f00401000c54408083c1c20309240c038140c00e00c40c2d10500b070b001000801c041030301c000d111038441d08041450000d021558407594407902c003d00481c0140da80050038000d0181028150700d02d00b411445120303946880f0010729215540100308002507a04000d401640411001d4005e0101411080021185c0e50001a4006507452624403413858040c130030b000142601900034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 326628705 1250 326627455 326627459
    0x90d0219030207140f06130e130b0a1a0307031a16051602010516051b030102030c0a0e042009090114060403030c060b06071a0915180a081911010204 65
    0x20f916004580502e903a054299001c684040e141e9690221024001411496441040c6090390440780303c2802031611141002010540025034101ca5a240542040c0b10b41e125480340050343d8014030f400e1110f100d60104401c120f440681d800c1c424800154001c0c5480d0b0f04e0b107a400d034125161924000e06104001c190103440c4000e05a2100940d2410480b455019440d41141e0005880f03a002d00141c00e03005605c00044101045004038000902d4000704152025011000003090b003030b800201c540344001c1c04103201d0300401d24460b504c1800c0b004070203403001034885070542e418098220342c28240604854006012602401e18101542c010880701980d0f01400c071685001400d148940c0c88050100a09982540140300d00c5a215445c01e003001400c481da41d25284c41c045015042c05d1441e205a860702c1000205404000300d40360454030399900814015590300e040034a003200f46010b00704054419004c8074000203466400504028000d095210040000d140c401442c0c070b410f00d003040d80281d00510007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 326629955 1250 326628705 326628707
    0xe0601030c09120c08030c0c0405101a030a06320102060105151e0d062309190b0907110705040b031c120218011e0e040c020a0b090d021903 61
    0xa5050740d41030701c40303020700c0c990b01d0a1001200c42250802059400700180318070403208005080100c0a10680d40ad000d99a540450748030003201c9407003a0240c1c6240c09075100c1803c001c000003181d004140500004400341c941c2d04032551003003440882c0c9051754030091140692080618400c3c5401000d2000300099070500d000b10303604000c2c901c1e101031a48404508024040da1040722214000c07032014046448400010400300605a503101e50700108200e014040c021680704d004840c0d032039801802078007140c1c0f1a0941c4800b104210079001002c203551f22002c0030f4641e900c4074014010000e43d51b4610001c0d200b002110308002403580302c00e104074540844203c5944001c00c6d088594100c01c4105c3c03076035a0303a08a007564040c000709028044c06100003810f5140300e0700000706021024080c4e0355804e030b415007441c810208803400c45007000860a0441030b8915440c240d000800340c440144144da0210926940328141d2030360580d802501a000101055a01c40c0c3c10801c0c0d50031709807001d0300e003100c03450741d928 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 326631205 1250 326629955 326629967
    0x50d020d030305090a1a04110a0605031f0312020a170c070504110c0a030504091d030912160e150a05090403050306010c150903080907260703060608070e0601030c 71
    0x1a0081c285030303d80c40000c00c0803000b03111201c00713240c006d80c0403004000c1c000b8070340890303201c115070803031395040d02508038521402c140c054142038800c2c07900e03542d00e140c88070015801c1380c01d03a8210351494903140e0040800014562140c6218201d60758004203d010141d00d480c4440105030403000404490178440390035050800150306048480c191030000d24038084c03940c928001c0c4120300001000e44140128441003607841070041086070810002000451005c22244440e25030542c0074009942c0184039007926890f144500781e044009100840c1e2900d070b40c5051041c440600c9600c180b88140c5110b04010749102100c00b04400d042c4110740b40c4207468202000141002c10241001c3d04112011002442c66401540303e284131a401c654050490300414801001902d80c0d94011000500600c0101e14620300010b4110184c610104510554408003188230800ba0f100404901e49071107030001c0000480c0c858442d0a0140c203500300505000350030484010704d8400064200ca040500d0015450b51041c0e200c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 326632455 1250 326631205 326631229
    0x1703090a06020d21020d0528020301050a21060c020c040b06040e0103150e060a0b040c180b1e0c0705030f03070c0b0904020702041b03110c10050711070803090a050d02 73
    0xc00352585402004c024015940c2c2006e1440c43d100030b02c40340b0f50004c000c10440c802e02400074251401048810b0b401e074042881155003128507004e050084800341454010540c80e15080221401c4803520743c0015605004540030142e04840004486030800340140c416500007502c880d4586450300303410b40e84003c01488007400d44403c040c658030412400340c101a816440790b6044605904064441e07200418215910611039850400011f152a000d25110580500c4043c141d0290b00e260100400c05580a041071105505c03290050803140307644c0350301a100801c080c034000d01810341880d003494900200441e07414800d5006010a400290072080d003001034400c141c0080c0d44a1141202050103801000b800070761203400d049091a582011448102c1c16940c50303130b810b0041092103209400309100d0090a02c1d5550007601c101020030740160803040c0c101c0024a480c04240d013283c650356062058940024000e82c200246e090501e1600010900223031804039122180081d10360300041400d040b103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 326633705 1250 326632455 326632487
    0x1200703030806031524220f0b1c060c0219080307020706090806130204090203010c031e18020f010905030f01020a0311030712050a180c031509021c08041703090a06020d 74
    0x21b448024203484e030704038402c83d050907643d54040c249401101600640103004424038001c0c58081111a5848c00b01c102e0140c08184c407181c80c56116950300c07030501800c03010f040801940304034140300c0510450340494240c5c0328041c402c02d0780c1328200890000e01744452540444d0401c001c817013043c4605080419020f410103001488401d2030422403020401610100c1d030003950552911941845039074250f00010b60350040c1131036501001d40440140011224800d05005203602c18600100050070900504a580003050504110465840f00068500101034200180070394001c0380100400c0e07018010807555500310440340b42140342440c0001e02004060020b0701810b500c0f40b0205070580403070303441944104c3c5000007101d0b604110b030601003016021031208440c207c05400d0780201480d1a88246601644e00510304c1c0d000c0c081e2014105e50303194580c074042d40c04010401c40090703c1c0d41c501c00c030454508481d034095619210340d501003002800b003550052080d13400822a1481495001e00e400c0048541 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 326634955 1250 326633705 326633761
    0xc190503060a09020c010906060509190b040e030406021006090b011b060605060a02010209010212031015170a051e0621031308010509060a06030b0402012007030308060315 75
    0x24050004500d400c00c2e40c090380b4281d00c00a103032401714206400042401e4000c3d481842520360759024080003070001c0380c450701c0c103064410603141941c4250300201a50100240045030342e0304d2402d0a1401c503400f95014801581c00240114080116802070000401042008200103002c91001800001c03601c14407500d83e00c4240744c104204281039010b5805041c028000c81d03103070041e400002c3e000358000d03400c65015105100c0c000f0480c10f00304085030310400040922100c050729104102c00c017040001080e6090180602d032910051204c48243d0707106185262002c40e880c107040d82020241604085512112105031082080c10345801040c025411b01d000c00344048106a07502c094254041d44180560b03910804100166441054100034020520740e0240c4245881d4888050b0803100f081c030004020703981e902d0000e00590700922401104032035140703c1204004104429509281640e0400c0303001c40c41c1c00d0144656030904100030188040d07070340804405401c00d00e00039964400c141d40d1070001410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 326636205 1250 326634955 326634961
    0x81005090a050106030803100806130602071a0a09061b020a02011206120609170418020a05070212011d030c0712030203090a0e06010822030c020a15050c060c190503 72
    0x11040110307880258001000b08811612868202000d900a4071104400d4000000104640c032001c80d8071400f40816024407590107901e550307002c020350802e1106483c0c1440da0244040144038050b41244214910500000c4803625072529400302d410305e00300d03195481081c140281d0130780e400040c40121540c090800e5801080c404601101803d82900320450700d0004104e03a80400031540c0020340f40501c1440c8410440300d0204400350b80d07008a214003d01e6a03150381e12100700310400c4d4000e142c0c0c15114a0400d240c00c1032500803404030055a000c14425a41d0380494110000d001c0382000403902c1c81d003010f14600803107a03c2141e51450b8501407512055585024801014020011119607046c00351002c0340701952040d4081140744201c604901080d00400054006400030940303400302172100300381c1080c40c16aa1400c84103030513a010101c0e0800e803807000102c7c1080091034020542107503552030a0b17694504060603402c00d58060007403e01c1d10f1062028181c01d09001c2206490b44040b0b140c100c7e00d0b99 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 326637455 1250 326636205 326636221
    0x1801140c0304060518010f05030406020f12040302030d0614010c060f0f050f0a0515091501020a170702041406032121180715110c09010f0519081005 65
    0x300ca000100c442900c80000e00140043d0484058000d07028035100c0940d640d1162001510008104101c0800041d801c01c00a07001a0701079003d001c004801a079403905005541c032000c0340c0a001543e040d00980e0001c6120110314240b40241000f42c10500722001c003d007001e0001030180c1000040007420140c56018681c0201e05580c0f100981c0c0042d1a8280300c5030502190700d0444110558100c00b581e41482c1c006188011441d4114012400c05008021995511010652400301c20300c55141180150702c0d07010702288030580c0e555468038001c0d443c0b03039039000715104010840e00f00401a09185141c0410080c1981e00441c40a0181500e1030b004a82c00c0c803800d4000c3d00314492500c00b80c03841031000035051402d8814103002d40c49000c609180ea0f000f42c140302001540c0c0c0d209486100e00101031002e1071400e0900c034807407480c000a480c500b214907100c076000001d081c00200360000042801ca4060800091408071900d000b1041e000c400303445001d04212440340c5810070303840401422511180441c000d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 326638705 1250 326637455 326637457
    0x30112020402120f250f030c030b120708070e01051e0102160b03150405042a05060c0c1005041202090c0706090b01050f01090f0e060a030b0f0103060c05180114 70
    0x204403c1e001400b03440c90308158100c2c84140640b00d59581303494080c1c1040984003400c5000f034502202c6e0b121400340c540e803194200c010300307017090700e80007016102d4106840c9515040b60180d1121081d00103002c40c0c908110101d441c0411540c040551550f40000401041e200d41c00c1315446804400304000700100e410b07005034134000e00780009130a0f8900c102c0300080c011078900080e50040d40c100701041c1245d00c0c032204204c1501e00540d00948034074845651005041503501d102c0c68104404943c40394519654000201d007130704020080852030b08484000790b000e00e00306c8140910301e06a170070b2842c24581050008006e01d000c1520090240c00c03041c0c080351451907200c05442e412540504140003c030100c0c60042010642803003014000c11191414074070f5980165411000d50b9483c40039980e00d01e03c1c2036454052004042c01a6400440125020000c900114421031003054000c2c03040d49554594070340101240c40b0310399005e04201d03081c00f41400007141007180040c9413070300f444c2140c182410b50f4a11165 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 326639955 1250 326638705 326638717
    0xd0e01020c0d02030702031005040812060f1207091503080f0c0106090e012906090f040f180c0803210709050613030b01080c0603070809011b090e160203030112020402 73
    0x71511441840210940d8000020207026200b582078920742d440313410000b01510b0003030741d00901c1c200041c0403c04000304000020340d401800101490342c0c1c91906404510368842a100f454015081218103004051080c020b0320f1041c214003c031103240303074510744130f040081c016110711103520701c0c0004014076500302c05d401c444094810f1500801c503c0d144000e800c1d000308100102c90342c0f00d000c07400c10120b030140300e1035201c1c080741405480e240c607054500f0308101c0b1001d9a0068947c0c01a513504803006c00d100288100360f01c4600404814540d01c00c2406d144402208542c096000f95100b04100203e00000700d00100b03003030004034200d0040340c0721010143e8804149070400340c0c00030f04c040b03102e041e000070311140c510807680103a4809540da602e4150054450450100c0c1c0c0750048410404140d0b540c0c401c5402c40d41c4100a42c2c000285c109540020b0006010005000030005d40d82c40c40a000d411408080c0c0d9400640650a90901d07005080c4084d469000511680744505489002c0340b0540d01d840d012544 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 326641205 1250 326639955 326639977
    0x2010f0c301d012718290303041401231c0605030c0f0d0c060504050907050a02060402010f1713050c0d0b04060b12062e0303050d0e0102 60
    0x1075a0700d5503110780328818100800440000e101e0301202100520541d1240391076460607510300c0a0502c8840c03400c3c0348803e0600010528469500d80040d0034003581001c160a40c04241000c03402c002000d079003801ca24000c0e442c0d005811480a0280e525680c00011502110501d0114003c0c0880000040e5440038500c0584120300000a00248280c02e10100030f000382c07900302c0025000e0302803040340030302120254080c03141c165011410a911500e0158400040b0035030082c04540001c207284c1d1183c0952045901031f401040010800307003c0c501d04842002d90001d094a4110309000e04590001d54810000c1c00182c14040c550a00c411000e101d4841ca0b4180305440c41d2b240700b6404c01002c2011100544141554030780600f0b5690507451528120074142c403900701180707194544958039080000d018440070b15520000e40c2e081d01c104a441440a0f5114a00003500d8894005601010b042102d24083c10341c0300c8900300d01020710002c0e0b0444265401c900d000712000aa5410200c0a14024030607442024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 326642455 1250 326641205 326641253
    0xb0a020c06040f031b080d020d0b100c060507031a0d02010e060703021b0a06170a021e030f0f0615090a0f0e1911091002150a1406090402010f0c 63
    0x2009201c1052108880c0c51302c6542e9045a510300782d1030200704001059801001d1800c200020301c0b4068698024040d88402001d0015009162000041468a4200d81c607404510000b00c080d0500c030a82c8550b40d8002c569050520101e40003c10304c0014034083d0300c5d043d203c0c02620703540c5425139200740041d00a0b10009807100c0e44d20003450070040d41c2d428014105041ca100c1d0f8041c203900f1410151481b03000ca6905450741b4089103581072408034a40c90003004102c0315542803091050107180105010040e000c418505030b964200004200c65190006003252040101d09060003201c2e10f034000350000c00307401c400d821500c0b2540c402c002403c07121694888094100541000300d4010510b1103281c0c001c00b0010001c043c82d280e5800440c3c16a40c101c9010081c0748810311100700c0c14104584e025100c10780910640310401000c3d80030015040080da2500b04030b5a5a0416607501842c00f00f84c4d80c1c0090040b500e0041d02d140030750000f0b0030b031407a000c0450100034205240300d0801c502c14000c1b14204203410100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 326643705 1250 326642455 326642461
    0x21b0402070c051c08030108100e03070503040501080702030d090c0513090809010c030e1807080a0b010e010c05010905010c0305160201060f0303030b0a0801021c1d0717030f040801020a08010f0b070b0a020c06 91
    0x22580d1740d1127515039000e103246416081a58540000107c035030345076004010350300b0245048019102c1e20001081d110030740c001005240d0612642c0d204000b1620300c2509a0821241070a040c0300919686c00c0e030401080c0e28082d9640007142d010805d86010350401d1a08404040c02460308940301400400202d030004916500703240d14002e5914040d00c81d4030255603400d041c1d594a150541540c4c00c1a454034042811107100e500c40b54840e41155500902440021442c3c0c64503995071400c4500020340722001070b94520a1000031040c1c4001d04004040c144000c1c0050b60803c0820070000c08180300040500d40d50356859000c44c0c403007001c1d0310001d19040000315291105000c003108405620b4401c0607240d441c081008052240e0310b140e000038040c04800070961a070a04001c02480400c0b901d140740b007440144241106000c5206c01031015140d26400542c80700c40d00720b0040c8c00d818040c3c00200030f40780007000501410b0154800d50381c9941c1c00c202840f0807600c0324142c85000344140c82040c0014004d40d030070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 326644955 1250 326643705 326643719
    0x20d0207091824051b040603020706180b0129040510111203190504030804060e16061806030b1f0c1a18060c18041803021b0402070c051c080301 63
    0x1480ea01410151092060750380314181e8401261a030300a445c8200d1090009004181c420f40c040c014040c4103800c0060741e41c09110003c00c1c1c140c00704d5421900b00709400014081d101d109860000c0031100140341501000c500c18441281e40201e0050034002c2002c2c8540240d16440340d1180300b4002c40e0501660040d034401601600c0c150700c200d468520b0340d040c0c0f00024800d05e85511603248515010343c0c6150340c40c1c4070340c0e8480380602104801c043c00ca11170340403803101c40b0450f0480e0300001c294a48506030100c0c25001d030320760400d12640c842c400381460b0000403251515100406101c0683d80e00080b90440755403441030700c04001350300001d000315000f0300c8802e4821380c4903480e003406040d990030000d03132121102c2d09203170390303040210340c030602d005001d0049008c043e000c800700a10034040100045500e601125208c950080122070070740059005100300c03202803006031880c0d02c2c0309009444c1580b421101e52074500740e0761114410b0b64040e00c2e0303c1c0340e260081c2104245801010303511841c099503d50703450f00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 326646205 1250 326644955 326645003
    0x11412060f1f0f14030f0a060e09070503010b09041a07021f0902031e0d20010203040f03080916051002030d09030210060806360d020d03060501020d02070918 69
    0xa012004180c1002100e18454011150710f00f0305004070401d180745d99070300c104d8101400c1000d0315546110ba162032001c1194600075040310704c45e050420040c0881441d1400301400d6498030240d050060040c0001d11021034200d400000c00e4903801141601d1390f8a45c03183c105d1400c11901a601000509044888940110f941010035000c0c022001ca450341e0b40881881c0c0314010002036002e641e68041d52506424501441403882038400400600041c048218038003801d80c0d01c101c0c5c00311160041e01c980e0303800305500040e042d6000342c9810300500010304220043e000ca0812401040c0c496211120340071101c5100308200e4a1502d0102130a0254480b1450040d5449000107000701342981040c90128008100250441c4103008800f45d032591000e079508403403441c1c000390481001d090041740c2804070000c401c1141010140d01c0f6030041c8114121024001c0490340389801850454100c983c0200442c0d80c00038066043d02d0b9581c400142540705013941e14104460540003e0060320120042c007690442d0310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 326647455 1250 326646205 326646259
    0x90501090201090b120f060103020915130b0403110402030a09062307030212190e160e010b030402030c010f0e27010504020304080a08041e0b06030705011412060f 71
    0x2072201c1d400e960704d490b8829524081d100325215454140c07400a140c00100b50401500071406040040c40c2031100c802240c0c1c00300030b02144040c10b940006500302c100500f1440c41009280b41500107080500399a82c0000303403120035914a12542e001700104240c0d0710f55500034820b1542c8800204603500c45401c0c0c0b441411405c0e80790a02c000c810900142c4918064000c50304100080c10030000c00d136803403045002550480150f0020003942d41ca84051302c1d40713410440c00d02150610342501080310700c1d0070002282100e05800801d0342d40300500c00e01c80141c50014843c201400f09081a03034003000710510403100604a642c50540c4040b03040d800e80c020b040903c80030400000c0c88580e43c1156a201d50602041e032100780d0303009100400c2000000070003841461401e811a124a9500020241e1050341174803c4176044006c1e00e0341e01d0b0b0481800541c0c0340402c40c082c024502800c050900042d200c50581c020b00804501c050300fa00d49000061741c80d6180c2101003084000206200c00c02028074800f0082c680740b80e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 326648705 1250 326647455 326647457
    0x3030c0204140106020a0b13050106060203030916150302031e0c0c010501080c010804121806030c110a0803060609030f01020c0105040c14060301140103020d0906020a091409130213090501090201 85
    0x4401c129803000300103940e05a500b0f43d0000c1900c00c0341640c7c1c854501000600841c6240811b150100001c1d1007800307848001d0110b41d00841d200d06024001c28144038030180042c00d00e00d00e10300f08004102801d201039403142c0700c0e400c0c016280d90710a04001040000c1058018010015104011060720181d02929020503444001c002903a02c92820a0382c403010b89510a000c07030302510001e400164027201c4d01c48040214504418601c500e9642e52440c07000030380100e004a5103900c60850b403a035010700c41098000c000001030035800c0b00b03074856035850320000d801c090080390000307104411500e00b000319500c43d82441e0000c40d52801507860301d0307001702405d9070f00711103900c0c00c00300014680f10b0b1810072441e0b484000b003802e841c40c1d180c202042c0841c80c0c1082054103054081c440310342c0c03110b0180304507121180108005a500c4020510040500c00b064010f180312181040441c00c80e42c4405103a698490b45000d9402c1010105000080305080d0640d000c0700a103041220000810006411030f115192003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 326649955 1250 326648705 326648711
    0x20904050405070f23090423072d0612090203060109090506060607030806241c0c05210403180b07030306243020040605040909060f0603030c0204 64
    0x21040c0900000d045c405e0490300d482c0e03a000003509186402e112041c0c00c140300f4102c0600c80903407011603003120089000d80c41503682000034104004420810f0a05008170409505141c140340141400102045402790f4020071000e13a41003500410b55a01c282092030300102210010340e55040550043c01001d20115014003030140895000c3c20890251040941d26403030300c02c290750300c210601042c080418080041c014172106568401c401c800010441e10200c50740e0480da990401c003000d004d1b6900500c00100f00941000119035501c0034205981c0d00400c2640e6591590b01d99080072190f9038160500c400e4011b885100008903480040e0091400c0ca00ca0f446c03d0000743d50b642090185a04c1705031aa0b058080c0410900c0541c40c8101c4c45846d8000c00e0381d009440c2581103a030031101941201c005d403840140e88134100001990464030f0b51320714034604034009140a040110084c694000c40c41b0b290001e03625090782004010382c41d0413502003400e03c480100002a520300f4010300203009000264000c6103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 326651205 1250 326649955 326649959
    0xe120124090902060a230a0201090201020601080c0d0b19050709140103050f0a180803070903060506030604020607140c0d060507030f3e120709080a0312090501020904050405070f 78
    0x741d034010102074640007070425060481000f400c4e0740c0c406220000b030444003c8910040707841010100a01004c0c0d50590000411254600c006460040180c125480aa1141140402c695200c81c01d0300ca48039400b0484001903110312184123244040025440c9000d4100010001d01c07682c040180b40499030441d03212421a00410b0040d0101e44068810301003c0062000103500d0100f0b41e004441d9504d12400c080140d038074140c5608409400c2901c1044c0015803c030402c2080c841640981500960118040c100700d041642c001200c2d4403c24100500c1c8011a150389400d10b4018814182584005425103404c58143e103081070040c0f0b03080328030070086890085800240c031021710030480c10450f5200006002e00810210058040d030140c1b41480700c070f03070700d400c0700b80c0c0c24130b1500c05811503d01200329a0068240000064000d045541000580d03502c0004520086030748600903d0781106d040800089155040c20000c1c0a8400c0c21146074105081500348000c02c540010080d0444440b030a804680503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 326652455 1250 326651205 326651219
    0x6010b030f040f05030c010f0e21070f2103090317070c11030712050c0307050607200d080307021e0a03082e03060501030b0c190e120124 60
    0x30200361860540500440002400a44007944040c8081d02490482c0d040a045440880c2034600110b0814000d645420030014400d1041001040280c00d1001190b83ca580c095013205240c0120380010b80180e0301c0011940500c0780c5079001e0b04482c0c8a1618003018025070000c0078020f09401c050450008010b003480101c40204013001601850081c1d80e070301d40f540c04039100ea00c003088400071034279454000c0c0540043c5465038080d81d816107500c5032000c1d090320b0387d50380c0816040070000c0d84818060300d010455640003800d4404450029842c8042e15420191030740085648036842c104014401400001404156a000148144c034800c0d9207900300f03041480f0800650305d0380403820004011440c031901080140100c400c1203001c21201c800b041000890b42030b00a001c0e500c4507401900e4842e070354001402030011103405903501036080300f0000d183c074001110048507200040d401c00200429285c5050107a901d0001c004042c0010400a00142d0702242c2101001c0c10300c9401810030101c1101e0020b441 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 326653705 1250 326652455 326652457
    0x9010923090a0201032c0a050d032706090b13050c010f0906110f1e25050405061f0914090106050a0c05160e061c050606100201091a0906010b 62
    0x101c0640e0080c04400741d035640190050b1290340c2c5614124924580002e4480e0000315090440482110080c40305003102d0078110305081100405070205424102d8070102d8020510071004407591000200e00101d4040c14101d009082c1010001c01d100c200805100300302d42004940480c080c02a0180e403004401040103551000fa44e40f07942012640301b410802c00070b4001e04507000c4030000c1600342c841441e0042c0500d81040f040700c0090010640808240e84010000c00a80e00d181c0384a662003200551410811249000710f0700c161071081361214001819611901c12080810100308009640002020005045c8030028003814614a9540c8407407850341c50071492030342c101d6906846a81ca07040250404444010403450180c4a901c42c001e6440c0d41d59042070b414800400d91845907d56034282401040121200e0507210300e03001441e00c00c40e4010030404200307207400c00c10031603030001c0194901e0400e0740981981c96001c0e140b25000c0080c2c2c0202120719146078400c0054406403011030781c03910514412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 326654955 1250 326653705 326653711
    0xd0f050d0f08060f0301090b1e07140403120e090124030209061603180b040906170c090a0e1209100c050d080402060409020c0a020a08030a1b0c0509010923 68
    0x1401d02000c01c409003041c201c0f01c214034071301800205076081c05131a0b503244c13160140c89a4888210510a20030200d503c40006a0010454a0070003070f80c040b059283c80040c041c0b404080d11503401c03400f00e40038150103070030031020455001e407009003150307503826140782401c000300c41d0708401840c41c04546803d540309101700c45800c80010b0485040c203400081d1829044c00750780741241805144081c81c468020513400120080c8542021507a940c1d050403281d006440300c542c011010242c40001c0e070f820031500803030a4030f6460350235540707164103135152080080a801000d02113505030003181c048648107425a401011202c400748c4046c60314001c008001c650a10300e4800180c00c3e40c00c00800b070f2141a10403215035030014001444141410b40f1081500201e07031007000c03140050390000c3d40c001c08500b00746d10b0001c0240042d101031424a4010342c005050144640e0401241c5400e071808002017107165480358002d48800707400d1503060343e140d000100c004e000c042030020b4200d880d0a82d0458001082c42e010344 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 326656205 1250 326654955 326654957
    0x50102031201090e03090306041b05060a080415020d0f050603070b13120813080609060a020352110a08090609010c170a090801060b030105100e0d0f050d0f 68
    0x50907072a0454900040888009040030b50101b002200c109603810049640158020382d240722007403c8041c800345000380702c3c2e0300580c000c48007440a00c030925041100207034081d42141040110010b100340840083c800d640f2503a04d100c3c07a00c1d11400490040d94881031107050f01360100d0303190715252500d4100e0b83c041c02e11228804802e1103024003c14020f0000e00c00ca09100d041250700344240301011507200d0b0002d030003200f055400001040610342d03040041c1c5070000c80c880011403860a00107081440c000c1f47c88983c00b03044e20411107050422030700803a050f160040181481040c8001840b41400b0340048801d0f45d00050080940f0b400385680120301c102c100ca43c01a01d85180c0412901030000d241c11520400d4103011005203044041440e804604030400706e2903076034556500c0d041001505420300b58100064580c90450188044090b510440b810341d0f0086650303600f100c2c1c000d101141e2440c20704229a40149001707141c4401c002c04131010801b0584202d0075a200e48880c03180445000c811031075010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 326657455 1250 326656205 326656237
    0x62009060a0909020f030406050f0601080a1e0903020c030d090b070308060409060c02340b07080f180a09020703020709050c040b040b0903010c0f09051e1309030905010203 75
    0x199500c0c0c440000d060440c1c1c54102021869600c0756100100d0700032018042000f00004100400c10505119003940503c1407a112602424080002803040c80c004001d0710010360389150b00b58101a4135a54490403844003801400710800f1071400a40700c96160340300328002d115000d24401c0031405049010240d800d4030740482d091191548084070944009400300c0d4015a8030418500801c4160117607003200d0085070002d00781805001d412141401c09400d40c030801071106084450b01c1c10398859520100d5809085440c2c6a462a0500c400544210340291404002c001582001d00c0b40c509540d502d004001c40e0f001445a5503082c0e244103038030480c14000c0040e040f804c010720040a460f88019081385031b84030410304168544ca008050365005402045101402182e0b120551409020701e400445061410385501c1e108a03101409101e4240141031242c494503103a90b0b5007142c07168201440d01e0004181c11003e018150140e0001c00b4401401e5002824112000c44c0e1341d400041250a07601c0381e90504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 326658705 1250 326657455 326657467
    0xc010813050a03120f0903031a04020f0405040903020313080c030d050c0312071e0e190302030604060c03090c030809010f08091e010b03030a11011b050d0f0e070807030620 75
    0x40701d0f4804401d00404d030680d038942405841460358420010001d10a450000f542c40d28401030601006038001e03021301c96401080503181c1131a4150684044900a035004901e9856a207020790550148046603d01038040da000010182c41c000741c01c203054070096040d9190900c1030700702110b5a1003042c00452540d0300c04c1021020300c121000920f54070425500d01000d5410300a541c0359246111181d840001603a0560090214071703003209031003c44201400000061499a404291588801000982920740d6100440001030184d00521800c650103651720000503120b01d0714940d0741d084030541d20f001503403070340b05e6402090084000034042c0d402d0f08002c0448801c031015400c00d0f40f505001c030108654079540c400c4000c2e1005c0000d00390381445d90b03c8000400c0c2c14810102d08403410301c440d42010000c400d5460303800a4210040340d001440740f80000c90803284000380000940007a0714489410320031660001080d450101d0352100fa0b80c0b2542e070901040c07810b0380390840c250305540c1820002160030403803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 326659955 1250 326658705 326658707
    0x6090902091c050c120d140702010804030c1412220524040801021206190f0e0c070f0b090c0108010308040b1c0606170604091104050618090c010813050a03 68
    0x84902c442d44182e0844d05001d0740e02c800f25681c00d0689100301c0180e8410000c1004c1c1070b80201c0c4c6040d05807001403030342d4200111500028080e0b28050400340901c80020108410b0003030741d034000d070f01494091041324000940c2807074141080e488540340080700c030408110030b28804240e07150718089a800504084225180814080261950825116400ea81000001500c40c42030004e0085641c80b40c00281d050300c0c08505200b80d0041c0c482007408071003048031003407002100b48580d00307007510150310314800c02d50b0b100144522079216050f80030702a0900080c3c41c10421410a078141e100c0c2004100f500d882d10014001511800001c1c000208800010302c400c0c00503c01c42405809026502c140428a03584070341c06020481e0b406810130800207200031035444003880003d00c10740d000030b402e680070014041d040d02d81203040c102c200c0281d807189c0d031030340e01140455650980c0b46c4030008100c840c1c0310290a01d41440e9503034015941420b804140d44c1d078001103144c203003201c00c02c02242d0030101802001c10b00750780c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 326661205 1250 326659955 326659999
    0x160e0103231024140f010906050301090c090806090a031d09011401051e0316140702040b011e1d0418080d090f0b0403030b040510060e280609090209 65
    0x8a041c511001c08102440d407081e1400c10f02009212100d551000072a64030b0a0200d1034402d40003190500c00b10000804c40c0c25848130440b81114000c007800103107401000811244680144c2c0014040d207d2a401c1c0b0031061400b00e01d45ca0010305c02d0719189001599041031b82c2d00c40151181d15a840b010b1040104400c013105403161954030310500d03006142c00781e10800201041c100c2d42900044000200400203101455202842c0300e0700141042c084019100d0003030b05140c444c082000380038585484201c030890f40100400003617030220400c23100740212440e200900a0101020000d41c0404600303668603e4100f80c400c0e98548000c41040c004601034071389520002d603002146060406641308008000b00e80889800110244103070311a08881c201070030f0080c01d94203180764041c441ea20748014490310340441e000b803e040307844e1404e00c0c00c0d40001c810001904184e001c40001c9251803150241c10070801d4544444054030620b448100f00591188100300890103005420b540103500d942c1c02c0c1c1103c20b1124 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 326662455 1250 326661205 326661221
    0x20103050c0403050303040309060219110d0501090b0a0f14010e0601050f0d061d09060f1602010b030d0507020306130206180d02120c0f060c0d0f02160e01032310 71
    0x18003440c900b035540c0e60b07004d207154004c640c00d4000031180581408119814403040c40014000c0c030b00c42c000b6101680310443c0c5819401822481410842c01c00360400c0720a40051a209402c01240203a920700070307810101030000280000b000a10b4010812182003401c0c00c0325050f50800c40d01d1254075940e51005403980c2e80001c102c446030300d400f80300880d450540c0c0c0c09400d0281030b090490841c01400301900d2000148050300031402500408100160700c00b000810079806003009840c0c6030504c01c0e20701c09900514584040035014094442c01610454000006101142c42542200e64503601c4007040c11036102e8101c40258051001c10100d031131728205545042440354000c0080f00b0b1901c156000854100040901721102e4108180c181000c0ca88400508030340001a910186400c220400f415103506e15042d50100340040e1041740f2910b0341c800c1140b03041c01d074611320581140075285c1080410100b0240320880e031001d03980800c80011481c1905541d030b01840b42c0020040524640401000b5007881 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 326663705 1250 326662455 326662471
    0x2030f090103023402090f0717072708062a0d021224030a2109050d0b04050d0302070515040219090207020918060f19060306050712110702010305 64
    0x6048504c40c620795150614001c00241103070301d0241d500c18019800b0009060051014880c420442c1d0950000c42082141c2c0c4d09502c0018540d4801d0025180d51122148070141c90301403807075082c540001ca03201c62054842c0030003103a078030381e4421303d1490102c8013070074210411004412041c6080c80c24680945a0394100034405400c100407048a80324101044130440f4000d1502c8001001442041d44400304441069000e00340030113140d1925580b00514014040d6900044924a01c420380304501d594081d00c4000d084400481d0103042000c0e01140030ba07403d650300e000c3e46905510b014080d100703c44d40c440e840701c00781001c503180452503802514014010b03030304115030901c45151508500e4400014202c60100141c0303038111401401028000148210039134103041a5913400b084000800c030341d0003014507420b01059a50032009000f0000c00011159820b0304041c008400c011064112610034503a0307a07280310359481d50a800c4019102c6140d01a694154108400c0c0c0c0594401e40000d0341c40100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 326664955 1250 326663705 326663737
    0x203150901050117090727060b160f06020708030c07120206041e050c0402040b0d0509070302010c150b091303020c01020a0b1b04080f010209010215091e160f05010f02030f09010302 79
    0x31f500c18808400151211420f0f1581301c005080402088138411709000c1c04100c0503c1d410001d483c4004901581d4070080a044803201010000401100e50101c8a1180e840b503155512420f148001e9086500840d008072909401c41c44601e80852000604510554100b01200860307040c517a02024603552065081d14580036180c08207100d42c9450000380000d021041c6a9030b40c0e00c0c0240800000c030340303001d4800c08994000c05d03010405031703a125800405050b0041e00411900300328200c1d00008118401c20b441d0070800c08410802405041a600d00000b4042d40982c0c8105070884012600d501c2120300091560540d00c001c03401c1045006240c0d07010b203000b0b4180c6450503885800782d83c90124149107204481c0e400107121811542e05104410812291039000d21041c1485440c0503100e40041c0065115803440c56074a48107002e0411520300c41c03004254143e03040b1911440300110703100d101d0040602007502144849410b500c0001154039a18070031014500f00024000110007941c071500280c1d5048127 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 326666205 1250 326664955 326664959
    0xa0509040f0e0708101109060c160303051207020607020a140c030307050102130b03070c0b060a05180609070e0d1b0e07030c0905120a060b06040b0a0302031509010501170907 76
    0x302d01c207181100d41e0325002001c0c01e42c0303004101840c001310204000c0829042c080e4050082d42e00c8003d4a16420f0126403d54507440c4607007a540c64000d0000314181e20120100700081030642210043c04500580a40c5405591700d0f1a026a80c030300003601c4142c0141d205407408404a00c60581c0c074003c507200c035420b56080c100070f0000a0702d141c025034015990b40e540080d01c1000c001642910500030034103d4080e07415880c01c08000761a2000c010780c007506074450100022900c0c0d94002104000d800002d2015106110305903000c2144401200c0881c042d071040404035605a000e99518015410020178403801a030b525a260b42a182070120b01c3c0003481504c0c2d90119100070070080b480d1091700966030004c1e00001015000f040441c05610150103111900900d9503170b020f01164000d0242c1d08010007140089000307011660901c5542c1c8450564030f40030a54008540c1d0640007903000790381411170010020014010810113110a1062501180b0070f140700c03c0b031008440c20640c1e0f0045110301652542a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 326667455 1250 326666205 326666231
    0x9010f0c0507080a0b0f1302010503070f021006060302090a05030303010b0d0f180f120503100b0315040f0f05060a0b070209090a0210170a05040b07030207140d0206040201080c0903030a050904 84
    0x4d030301c0c1400c940001258080200302506d42d846158050004583d4034100222900007a010b032002074440410008406100c044440c0204503840e800300040d41c04208030369841200500941200c800305200385a03003000080d84d0300d000070641c0d040e113144916261400c01c010390b090006280e40060300000c80c0c1c84401c110100900c0e0a0810310090003094075044a1074a89028401144800079040910a060082c04000559000800151003500d890035949454410b00c1500ea40184844280d201d82015090190007100344c000c0c903064060040140403d88505040020b9900e060107501070101c024030010015240c0002c00d0b81c2c001d05407005032020000f20b42c0200b5081e01d07100c85c2d0b400108090305018040c220b00c41e107049501111035401007002c3d0902c0e80e00c1d9401810081e2099040603000f18a840a111b00900001c2d03105003003900301d455400d8117040180d01c40508440580c00304030043c2c00500400114001c0350f08903000280034500e04060644103907070380d8010f100300d640c001c0d640e002040304203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 326668705 1250 326667455 326667463
    0x702090a0e1c140f1c1e050403030e0a0813170c09100f0f051203030f01060e010509060c0105151e21010f1a01110a0b07050f0d0b01020706030209010f0c050708 70
    0x441d40302e225040d030380c40301c1141208614511740c81c21211030f4580090301d42c04405c0040c0f00d40c4e010030340c41c41c0851a0341721802c00700d002e000e02e140c0a48840c01100589420803507030400030020805460141456543d83d071101515000d42d85145402540011395200458500382c076405900a100e00c464032245521107100041001c01c43c2c0180f03a240865050030b0085207041000c0300e8103118107100543c0745291003444541c2c010418441d040500175590310301400c0383e01841c180d0b030142d4006001e1584405100155a01030402580c0d00c07600d08140000d06805402c100304120003103525021600240c04001090107400c1a07004144500310303140c52030600340c51038203000721078200b0340104000c5416611f2a1601604801c2c11350024188101c90f400c0142c200c202059424202d0340240c24030800341d9503403c1c107407100c0c42000c5c950b000301c1301c00107002d0030485540d6001e0b600d28a03082e401c03100a103884010960492151072002800f2400003a002d0003001d100d542e070000340030701c10340540e502240d03987e000c00c1ca0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 326669955 1250 326668705 326668717
    0x1d10091701020c01150617040507090c050301090e07150f020a06060e070e0a05030a02010c0215070f0b011217030603010b040f02090424061808060403050702090a0e1c14 74
    0x56500003a140080750f00034003400c01d0b000900a801440d01e481d040000d8000d000b03100380744160b032550f480007800340030342071188000a0480602c00d001c580c04e6900700600e56842402940c148510707101c070359608039000050031002d4450100300100030741c1016000342e4445080041886c118460740c0303200030018209008410081207074108544040c203041c0006041d0300c060b84116801900c07440d0080106580c0000c40c3e1407525020700b840609602e4074004a84410f602c05881d40c0c0811001901c28100007003480d0580219000e03543c1e06031540d8803185000802c4060620280600e050300c01181e032a0400d2200031900000c00500000f964426400800d0a4030074803680d900000780c0c04100491141002d0154800520040750944400041a00e105890030603500811041040c3e43c2a010700d91200c1c84240c1000d49040d00c101c8620349402d103001841c0341d208203000c0703000b80d903c0400b05d00804118019050715204031005070030040380720ba201142e14509540c082d800c00035400f54040c0c11120040007426 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 326671205 1250 326669955 326669999
    0x30a030c060b1516020303041205060403080c18010323180f241b0d0b1806360126060c03041b08030d090606061d1009 52
    0x4042406400c01c54119485002c14034003425101c001c80849202e07400407684404460201a9907454040c0040382c80c60203241c01203000030240b242e00c602841b10001d101c5c0e00c00c610964489421360f6850702c070443c050150038100805840c460202881940c06a0080840c4920720030009810b054402150400706900791028010380c501d01ca00c600303461000b4090181c40a8011004004010014409103c10031050140c0594050150042079900d0380c1640748805a00c6d814040390f072601b103018059001400c00c4039030036100d5000080b442d044002402d038114866040106034007400080d00800e13043d0021b0790030403815a601200c200c5402c1c0007282155501030301f0400030315292807440c0210400100c1c002d0302d10502541c440420800710360044402c03680d1080c1d200e010042e1260f0701a040c4c114440d15a08040107900020404924241030341e440b50005500421050240fa40d85800696034942400b5425199a40c0d550901400b401c028207500d812400500e810030382d02d942d03031000380b0070340742c0400b2800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 326672455 1250 326671205 326671217
    0xd0c0305270619030c0207060c1707050a08180904021c050c030106031103060105181513060b0d06050603060d02041d060f0906010605030601050405010f030906020d020c0105010f0503032502030a03 86
    0x102903d5454480c0f4551000d40d80000c105a5080950180c40c68040001c02415411128a020010b10910707041d691190340c84802c0f03a0030f04405240920711780d040000c407100542c1030190945411715100440d68001c54000e00001c441114042580d550307220112001da03804d1140c42e2010180340c80c00d201d42c000031402104491100f6031914101414031006901c42d91260011120a003190304160000039080580250006c4e00700c0301e0703400420396078800044e103103001515020002416407000c0f0018000000070032010484503844104111844c041514400c0e001615010000c0c014100390340a42d01514039440d41c412020f551000c000e02d4108100c5503515030318901e10600140ca8010001d40d805000282411821480d090000800d280a507210fa281002207002d54401710034004e62001c42c081da00074070f00759510500310042c00087e5202c03003900304040d0310341000003c440d0032501302d50301034580080241d45030406103402e04a44103880c600348a000d200d03051015005070f0b130400c0390f664101e1003a1034003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 326673705 1250 326672455 326672497
    0x405070f091e0c0215070207050a03140f070e01090b1906031415090c03071808010518011802092205060a1b020a030f110a0c05030d0c03052706 63
    0x62812030b0a07060380c0b035120506041c0041080354010a40000d0b603a8803550380803031030351800400c914143c400d034020740d0070000f03000303010080c40b43c00312094403100c42800469040d900810001071b0380340c10354482c03070b2281c0d445540140010340840c0c1009143c600c0060401c03010483c011518000140c40e0380c00800401e540e9030020fa4600f080818203039120542c80f008183c441d1102010400c1500014903080c0001000000120313042c0c0100c0041c000200108102c1441680380d845450090000341d8548501d511070011b0010207201c1401201c000c4805280c00240c1d44541785e09110307c200c40504021001000440c0b000e12690344443d8503100d080c0103d00600303040c1040c8140104945484440020101c07601c1e8180e800c283d000901c15010552501d00440310301c01040c0c04907a100040d9501b064940105054141032000030b5491800f551021016205101250a402d95000c2d0710100c00401154043c0030000c110041704405075054148401d900341010080b000043c0039910811480e00740d00466026 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 326674955 1250 326673705 326673731
    0x901140f130501060207050a0e1b0d0527160905040203030f0a03050417071a040302010b1e03060901020301080a0809010e040c180e061c051903020601060219030c0b0405070f09 77
    0x1411b8024081039540403170040c100b0306080c14144000309030b03114804240103100380c0c161301a0211246a40d121100700124240040401c2c8a180050071908085503580d801c031000301c6011039440c0f80d501180b216052400d1402c40c000014120003081a83c1c0b5000500001c3c542c038031218001d210240f144d07a00043c66151524210302c461200d40010385043c00248501030000c2d04070211b003140c4046130810005981d4492400300c1c050302c002800150402d20114000092140400860500300303000c600769100760341c85480c507a00b01d000134451015140e00c2180c40c1c00100d1006c42c010400840180342650161500303802060582d2046008040051280d200740980c0386042c10000011748000d01820065050140016071800e0a65104007081d0052540010800c07404000e22350740c020740310303807110541011420080d4448900b40701307a02c09401615600a00305034001e00001a1035416100d0302c2028015490300901c5010061003115144112440820296502c1c6010f0000744500c58011079061040d0382 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 326676205 1250 326674955 326674963
    0x50a110309060423121b090405120726040513050412140c011b0207090902180a0b041104140402090f040207050a0b0703021801020c0901140f1305010602 67
    0x60150540e001800000c540d5a9110122400c4030454443c00a480c8500c0d08801440d580411800340d0000c03208151000143c004246040b50340944101810013007610018443c00041c225002040380d0840c1d0341080f000d40c1080082c0c44042d00546006004100380031842241c3c45040100134600c0c200490100100c0c03070410342110f0704810036401440141003d43d22034058150030b603032010034003041210f5038440c503000d0415a00d034115006d0091000c14452010007812050040108005004124000c60a400c44d4010840c1841e4040e1498400426012229898801c080c0c0007101c0180c4507003800c449507a49000b550b1041c40c100b00d200d03036a949091306580f00054024101d0703000354018801c0c2e01c15981c0e0f017101440021401c0c1c0300544d481c1142d1400e1414400e0b0302c80000c1140f8852001d119a03640d140d8042c4c01c200400701507404540d02851f0040ea80c81107010401c40c0c0c4181400c0c01404490740d295103035601c00101502e81d44002c800b04000417030034503071204000b80082da140010804654104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 326677455 1250 326676205 326676227
    0x90303052203200102090310140906040b1609030f0c060f09050904020f03010b060310050a1406030402040e011d0622031d0f0618040b011107091e0903050a 68
    0x1881021540d00c590307015002144a0784200b80e0100022003c8400c004290100d4594a80081c01e80e04044041c510a00013400d030301e80c0c60342502d100c0400064808100180c0d090003540c0003000c000066603407100c65030f800d00361070950204005610704000000380c00100100c3e00544142c6c201c403505410094003c007152541541081080038140c020480b5454480c40250004d4040d10f10565050b1178a012a02500c03141d504543c101c40c00004002015170b07031001082c151403040741e400c12403907a10089100f0400b0302c001000d50000c03040001c10014a0594450741c102c045003000490a4605607240c00c2000707050f10044c10701344d0045410015070b07141c03034607004600c281005924038042c403950b11b00500081620400030303aa03004082d60990540d698620318841704400070300b9280d881602072040f4185600e000d800a00550600554184560181c1e4680d0f0702601030b0b00081c0b00c0107207000000340140000b0b012b139008036452127402080c0700b0300710b0043d1180c0070300076110242e907030500c498014000440b00d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 326678705 1250 326677455 326677501
    0xc090c03051f0303080606120c03100b040b030a0f1415030609151303090e01060906030b0d080d0b04060306090c0806131703060f0a08060a060e040c05040c0203070609030305 76
    0x10385100b03034558540a41071041e030f5007600d01a01656100e81c01300c0c80501c1101c3d01c00c100004c401040209603600c540c001c1d4070407a04010031503002540c03014104803e008901076102810414400102c906915902c9145011244100400c442c1485034140c070720203c00361118076000101421607400d6040810100e604548030340001c01401c00c1c801c0502e94840000340c00000c895030500504001c0c94421203000001d00f9a03518800070f07550b50303803c2c080c122601d80d10501e004a41040a40c080b41d14150101510403a044400345290a80403c1c0c0440200903203e40f8036845a42c1d080e001c80400d00511465480301c0c443c06c00c2607201411b201c645454001d004003264507691b10340e010400018044101042c1c200311640c0826101c6e140d2500058188802c001d006810140c940c200107001000019901e00640302002c041141320344030f0322882070030402101c014284041c081820821803d2980c007080381c01000c1d2068a081518a5031480103540084100354002503c078414014030000c8603000c031041d4904 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 326679955 1250 326678705 326678731
    0x5010504151503020c0f01060e190c0905010e04091505040b010807080307060203041a0f04150903021c03140906060a05010318060902030708011515020f07120206070c090c0305 77
    0x2d40307040108800d1442d07411108258011405094184007001120602c3c0340e010020b1000316115140c886442d402112519011014542c3d15840c040304e512400c11a0303102c0350358144030141040015160030f003003084115041944c91020304081a25022070301800d94184078040380d42e04003400d00107021072044c3c1055035960001c20080020010003c210f6180580c850009600c03591282840000c444800601d030035103441c1541088801030b84218140d110307902c6180391480c20b034018071070b20003244c1c0f04c2031300100507901003083d140b8103a0f403101e62282651003524010401103941c03c1c9454070341006507488515540098144981c529001e48200003525081ca01003007081c000908907404d220000c4800b400c070903901c11049080d92014044070010308980c05c0207002c42c802560241e60303586070ba40310395049444e94410845400c4d10100d0952001041d80000f4000c860504c018034883c21440c500403607210204001d00c5000401040f000350040c94403840c0003404002e00c0101500b070780c030000c08441092213 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 326681205 1250 326679955 326679959
    0x608010602071a0708040306020d0608072d05060f0d050f0408040905270c0301180f14030d0c0905040506010e09010614070b0406050717190504050c04050a0501050415 73
    0x150008010b421100c907200d10304400c560b0642c0c101e4480c031a121018001a80c00540401400441d40050080504100080000a580c2c00003035880300140d004403804946200c200003851483d11151414a55280349032811080d5514001100c651103d814445444c0000c00d80d444940443c0c85400d0b030007040d2a03544c1d00a807406954640c45c070b2141303001d0040c0701c0f691507020500d811048011003040c001d00007403001c507145408148a6070f03040581001482503003000001d04030303460380d0080ca00c0c3ea540d0145a1084c001040d9841c580218040c290501e6184030600c500070000c6182c0c000c0e00401c1102d41c072942c3c00c071800c3c0018401274400040940d414040c1038040303014183c0761100080d044500c1031501c468400d005920008841c07082d50009001280584288020b02c005903200714041c000b561a41d4403020102e0021050b510400c0b149194030320f2080344042c2c040007540d0007880e031192251056850401a00c1c00003000c8400588402043c5030b900c3c0010300c501c2c100341c400d0802c64000e4140020b0428 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 326682455 1250 326681205 326681207
    0x30b0415021e070503130f080709020705060a050601020a0821060f030c09100302060c1b091e070507080309070905060d08090402180a120201080708011508061f0804060606080106 78
    0x1070b0207004a0b509801c400152201440300c00d0080d01c1005100a244a09065030340421001c80320b60360081c002c403030161100020350000ca901c21908070a80c0000502016583e01c5090350040c00004d100324190b0280c08103032400184150002d020316010345c02c0c4142c0121120074011919200240360318080d8460b80e0b00f003503a513900014014030703892085035040083d41d41c42c010802806907d0344001d400c00008615030b4505400440d554040c00d050700140030241c1850403c100d090602030f5110b03c01c078065811945081d00c0c0c4e5030080781c0e0103091401d01d41c0c0361401c196a0030302940c2c421100b002060300150340500036003542d40102e40c0c03c42000c50700c140c2d002005850b00404c52081c0c4101601c00c680c0014005a500f81040c03003070240c000c0003000b0441c0c0d40d0307407078096002000682c1c004034001000c3e04009003685005101030390588600b079074500488807059005885402024141517031208609084076450240400741015904082d40c4010240c146460101c0a035501a04190207110440005101c05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 326683705 1250 326682455 326682487
    0x605030702070e0c032404150905070507080d0c0302120411120708150a150e0403141602040c110132010311060717040f1e0602031b16030b041502 64
    0x203c90300001c0f141e131b04215000d1502c0c510100c004543c1040c18040013842d80305d80c8441b503008650001c0401d01960740c40c445c080382c6910601400920502052000c0003920303101ea03008903007402e0b8509005143c5440c1030b4801481d800304880482d0541e4a9451001450602920516000821100803c04207080c250707425280d01c00c14108011802c80000060082e011342d0b046a012502c0e881c50218002d516414a150f0444088409038003140008690252030300750041201c014021401154044c1ca2090b400c0101a04ad4081203800300040203400d106030701c1c0d0a20500090b20038032036401680d4150403040040381e40b6820000c1a0340540b132001000411030403407000c4407100e0210b0740241c0d12030280c5018210b0003c4044040080400440c000c1105111841c0c01c109481c8816550500c1c41808140c400c1c80075490f0207004010382041c0810400b94104404800d80100fa0f0800d0307445103080b0300008403917581540d1042d100c121502c4113100c20301c40c44004030603181c41c081c20b096180030301a00420440d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 326684955 1250 326683705 326683711
    0xb030c06090d2102010c0f0f023c06070e0d0c0302040509030706090302010f1d0705100921030e0d0506074a030102091e041103010605030702070e0c03 66
    0x14a030140c0c2000b04001e68082c00010464034403c0d8401d4900c4000c000a00030300381c400c2c40b0000319000007000c482c1d0502861041040c140c1c29030040500307a0300012822509801e16411001d030511440c5003140b400103d08607200303a880c404001742003030316107124000d118405003110240520f454404a40c0810002c50407041942d4041d100031881e6160b00b0281480d51281d260007902c3e2034038241002d420194107400c0452089031405050009013001050001c010132809607003845540a00c200708071031705000003000c0343c6500d01c2c245a001a56034164400d18000400c000e43c50345880507800e642055000300d00d1001d081e205071150381a4907480d544042d40c8032006040132003842040b4910721302400300140040c5008031074011080c00d003840e130006070201005a15952010105410300d440341400c2c140b003502d14006000f4514440102c4002c06903501d0860660081d410075107030001040520300c10341c0218000d04503551020b580e0301e0a8107009040840c1038200c90319040b540d0052100301540d403026250 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 326686205 1250 326684955 326684959
    0x4120f023d0203071a01050901051c11010207050402041701060b070c061b080a02152409091002160b09060709090509011b0c03030501140102070b0705030705010f020408010b030c0609 80
    0x180506040c002d91550050382402819500034a0a02d641c5411086240b4102c030400d854482c030036600c5208001400294500d50402d4040c07820846001c00c2840c07503214600700301801680c640d0b58841003ca0143e078001d401c8005003590001014031041401d00c25500140060052a81400e01d40c0d5100c5080e00a10302c5801304204d240d440c804614440c0345864042683d00030204da0341d440c50a00040e454081461781c8010300c03401000010050701c03180060031540740c0e06c01c001c6191150a8402c20802482c050a5944180f03e05207192501302c215100a10032006100985c25254120b85041000a00000c0c1030074803503040318043c8100d40740c2050300d4a056450f20400410143e6034200c0e4179005103219505810b10309580c2c1510b00c0042d820260001116000307680c1400140c0e01d8184068604001002290041e48440b43c2005020700380c0c4c01800c203491080c001e881c40c111141d00c40c07600b942c3c1c11815107000a0350029082015400c2481031072035807841039010b804000842c10003d0094000c27810228 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 326687455 1250 326686205 326686309
    0xe0706360302031b060322020d2607081e07150506011d090402061b0303190c08040201080a0f020706050916050a14130204120f02 57
    0x1848548451004000385641204004194103a41190400000c2284400ea00a025041c010320344c1d03900c80d0051101e140000b03016103140d40c071602c1090b01c0241040f02140b8501c01e0984036500140c0c0c81020079241540508014040c07000e29107050340840791a01407403030303034a40304020102c0000c1001e02900c40c0b41c0c040004004502074900308040300d074414002c0003841c41041d030a9400080e19660f02060050100380c1ea00c0282890200d04468004240300150740e00c000c80000250040c600400141200710100c2d00c40884003440784040b44c0b442d00165500d8082848000145610000034031803226981d801d85450701071030500c6c2e00003074400280505203c882c1e40e260110541e03a440c42e030b0115803846e64490000c0049161580b000c40d1141c41c015402c0e405401004800566440e212085074195440c0d13107080e0001060f80c03805c205443d008840d01ca2041a000e000001d40c8050402e089900c46000d0001d070740d203ea1040c0704201080024031101040c16581c0c1d011600100c001402480e0629010b848003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 326688705 1250 326687455 326687477
    0x40c080712150203060103060902071419020303040b0a030b06070302010b01022406010815060706060906050a050907050901020a020a1206051612151a0d0c0c030804030302091809030a0809010e0706 86
    0x48001d000d00b60081c0c0049c40c00094204104800d008214035882030000035690b840c0f0040340722890742180c240c2d02a50560083c4018009140c61100030f1683c501107003000140c108001c404100305421900f070650151759904509603a5580500080380d402104c01040c0d20880e001203004003941c14058181030411103001c001030150903104501c12a00344000f0500d6899104501c0c0071005083c4a005010074681031000001d041d090801d03c05042d520004e06c440216642c020045400740c126400c1a811403240d8401c0c140581c83d021031400c0600500203e040c0d0911007420440207032240a440d43c180e005428221300041a8803c1c101010400e20b1000429a0120841c00424080168001030b0350040f0204e1101c0120102100404004644400c2844600b0201009665480130301c80d015010403020300008000a00c00d600a00040e00010041111030940681000e01188100d610b10410360002505102154000204c00d6009011070001c6c80840b0301d50600b0b0b5203500c610710070002405082c03161 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 326689955 1250 326688705 326688707
    0x20f062b0608013c2d02040b0a080c16150c180512030f0c07061101020405030c010809150c0310050306010803071217040f020a080328090509040c0807121502030601 72
    0x5a00c1d40388064050003100c0a5200940400004c45c1c5103500d40001c0b0690200c3c608042d000f540c3c12608032200107030508600d07817010354290740e00420a403066541004210902a1040030040505000d242003040c51b00e400b24103001240c12201e10303041440f603018010003d0550601c0c490096510070b031f0320248101100e4a0703a40c95070280016401d84003402090b103503440ba50009003002141c800381d9550b504407c500d10024200d104500410b1f8058100803003c181650042c49002e8111b010f41e012903034048106022040d81200c01d1b00c030702003410700001c244810b1201455a10000d84000c4014100c294504059141e60744514400184080001e01f40034031002d00031a00352401c01805295603280d80b5040c03506a901a4621001700d00c203e4003548045030650300001610300745a5210181c01a9036042c00303a03502c440011805050401043d000c02040340d45800d074409000d03500c5a4400c005248c140000305040503a543c100c8401ca0410020304404107a00003019080210318070b100580d20307110440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 326691205 1250 326689955 326690051
    0x7300212090114060118060513080a0506150a050105040905150901081606030e03030a09021c030905100c1a07140703020a03020606010e030703020f062b060801 70
    0x40c1458200803080288018041d001044400003110b0300400c03070b80d0340c1e40065075004110480e00102000128040c4070071405080240352507500003c80f03080c02c80c4d60340c07034003494540103d0b01100c03960008400c0c00904000d05001c900081411030303901c6041800e060008100703018600c84c00e110143c03528041683c01c0505400c81d1050100074141002540e1281a843e555200c4041d40da0720002c45000d000a005200b84110003090381402d000d18916113070415018054488081c0a0741e0006103c032005000080e4a410100428070944840da1214604001c0120518040c01d0754001d008103a0300b9200003c100400301c002c66121507042c0184c40e100c802c4e0440c0c1c0d2808005200d03201050000b610320038550005000d01c2c456200354212502592000c004490b019500180070f501640010014401880d1600d290442803d01502c514148902c00c070100625820617521081d02c0e40380d10320700f648404000d016040144c40641c0c02485014032850510346d8050061400210180c1c2c0e00383c3e0300d8000f815140d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 326692455 1250 326691205 326691217
    0x506120406150609140103090221070801020313020310060f030b0c04050405040308150a03030e150d060617010b0304021c0816030519090e010e060d06150509073002 72
    0x1034515502030303468101c0136003401040d0146502640301c061550107690b20070701600d585280e0140104111110900c65986001e225076500c48035401400d00200e4548001d101a61140c04035507091107030141c090042c1070030001c0d1900d004205500f008001c1c4008650707001c6080132290300104408241d6100701141c0f10600864000590050802c4240010304ad480240309000c0e20030300508070903611a840070000340f0945448003c011036400205024640303802040441c0e11801c41c10b8652403c0b29282d0500704441740d5420002c04180c0840c0e00c08030b649400110b80c0c1c090090030320400c0c17560406800040320740c615540e060040078030f907401078810031807101709807000f540c03c1000074001d00381e061502410036007000b1b0403442c1c1000310390300c5055100e03c6210b182c4101c50300303030f8041c0282ea420034264400642004042507000420050b1880018465201d2134541550352110f503c1224101000c0020352400609200c040000d001c01c000a030801020b141000880880c802c1c0c081142140c407800064001c035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 326693705 1250 326692455 326692481
    0x100b0717030703060f0806060a0e09031b0706030e071a0703261506040b030c07060e060c030108010617031902120c010603050c0904050303040b09030409020304120801050a0506120406 80
    0x2005004030190140c000d2015100444001c03085c0585074800544d80d1002169440e500c4000c8440c100250384000b80d00d41e40110040064a16044e0048110504104030300c20050056010300d5041000a07410b100b41100b4400c00720180001903d0a08420f4000014901c51003401100084600c20035016191000880c10398441c03490b098444e40310031081003401194031380507154000c0a684601d14000c8100c50a85403140002070644d1a4a8500c0f00290071050045410540e207d1010354111010444144901c0c04840b03125503940c1020f40c01429103096a2240c82147c001c0c1021300040c48000c4141c071188600301003441584451044102d1400c0d42c41d582500a4040014075000f0400341034015200b41e03400344c400c80381e011114100b845507401003181e02034400d070001e002044c00960703000c00e05500402c01c10220303420152542407403c02c80c2e0096401f15001000841e00202c00ea800c0481c0c180101011112510744501d00408101e9502c180a000340315603182034001810480a80e11000521400d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 326694955 1250 326693705 326693707
    0x5130b09180c2a07060507020f090108031c09021f0210020a050711030606061c090510020705010c0c020a060f0c171c06140909010b101d010503100b0717 67
    0x9000c2844164024250042814540f010307204080310058407111840f40d14000822500b440c1410840c1c540c0c0215100302d0b44840c4448607009181e841c4075000340a810050040c41d550b0700d403041030b41c0d940b9414030f00210f440c50403c0e0600016070749903542c071802034510301446102d04000120072800c000f004001c840c0480d1012038001d00d0954004058910f440c800c0c0b03600941c561103002019600d84089810550240d0104000140b0010112010040c03254921002c0b030b18082c1580c0303040c1405816040000080c5c0c5c0440c1000510609000317108042034582008120f214003074001c5141c0980500135001030112410041c1c903114400c0f000291002c0e007191810704000c000e440d151107954401781d03000010304041110710550840ad4071802d0b0450780c4508641400c0080d0b03409110051500601c55041950307515600c100075240c0c0240c06001d80c1103a030303900c130b48044091040300c401c83c40c40c0120360411000303004010740c268151010900380d404e07554060351101184e160000040c00c400d00d4801d14528 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 326696205 1250 326694955 326694961
    0x6090d030906030c05043f0b06041b0c03030209120a1406160909050a06050d06050105100c02090f04050a020310060609091e050601111b1005130b0918 66
    0x3900114080c10b0724040e56080c0680061355004641c0c42c001e07405100080d17208007010b44401c00002c0c0d00d0840441c408000c0c04229615030402c2020314502042c01c0c0d421103180c804006152070184580c014400c907120382c00400c0400010020807042c0241c1c8020241940064842d0090b6585251072501c850540d04a030301801d01490500d82003034404240c0c051520400b4086164410403c89807071130342600b581c07000c1031103180040310170203032102401c4840b01c05e9440e940481c0a4071004502d514843c0240e501140380d51403d0107210003403503070b08194000c1140480070030b03005a94901600d0b40101041001544a807a1400d00c6800c0c80805034000b54540328904001c0284003031a04032108982003515610b0400390f48500b10340507100032425400160414402e0340b1340240c0b880e8041900540103241454020025080745450b2031421007960325809406040c4603040c0c50010f14512498603649001411300320414134545001409004445e400680403551000e1625040c0348035011074000c1d00c507040e0300c2c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 326697455 1250 326696205 326696207
    0x10e010204080a05063409050603180d140409110d090510060f06052d2b090503032a03070c0308090d05180109030206071b0915050f06090d03 62
    0xc4003d0040318503008000004480c9242ca22501403555812812681810f901041014294010702228000e00c40c03100700c00b0a1030f45591014500c10b900c5104000ba000d41d48140c054542190825044108184210032044142400059808458600c074002c83c03114030403901401d150241628110041d460551000709201c400261394040740c0000004108140d180c180828403114036019540200380c04000c28001c0071410134046d400002280d61025003c100d0800303000300e42d03110b090b6a11100c00078050440001200450455040d009410200130003185036642a48a02009003094600390b403521203107034451241040c820320315017402482da5072460004005417800003000e2040e800101600e00041c100301e000200020701c4201c03a1940f50a101580c4c2c100c2002001041001b41007000d1544000b006881d0b60014005080c400c003410f00913660504162000c2441766488480402e041107640720034000d1050120b0b064410690740d80301c444060901003000387c450003004907041641418824181 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 326698705 1250 326697455 326697463
    0x61803060f060e0f13030f020c0909030a1103041d10030803010b0406081807050909121812071404020702010903021924090e13082d04031112010e01020408 68
    0x158289160000c0652520f41884401c01300486184000c14036003410500400d0040c81c0c650812422803044450032442a030101c0c1e42103005450120a03035001144d20031480d600620300b4400481e41200542c2010f00e0b007501441154040a0913518005020010880c141208000344000d0750b00315078000d90320f507540c50459103183c0c0039103d903000260f0311001089078025144914000c2403c50300050400712700b808100000a14050113100b00d80c85000b0924608041010143c06c4010003050703108c8105580307070203000c4000b58400189000e030304400c501f40b084c51486810300101d808165401610385c00244010780707100300c0c241c10196004210403403402d0101c01482411003a61a4080312164210101d1000203564001c11800400700309038440620445c0218014135521080002074489013002e60f44074020745901001c0c2d2078114000355a03c040c82c5542c00308442461050143e402c52409140d5140c07101c4003414050028410b040100110341d06040075000a04440c800000855880b44e4650602d559 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 326699955 1250 326698705 326698709
    0x306050c04051905310e0102091e040b01050306090406051017010504050106060302090607020103050604150f0303020c06070314130e090c010e03030a08160c0b132a061803060f06 78
    0x1041031150b011100501c9800d001c071003011a45645c02040c0442003a050300600204480204190b500f40100301c05941c40d2000c03000c00f00021850000d4003984107040c072040e0341d04801f01c141482020000e20100e1f80301c034010b0f01e0b40940c201e1800a15502c42c0c9020404d400610f502c509a2035186110018010b48198001402a44500002c00549a87d100e06409038010000030030360043c418002c200265000e038025030340c001001400000c0710741c00c0c0b40c2e80c120f21015a070072582c0c80e98a00c40040c0f040680410604500f298200da0550800e44a50b5004000344a00081c01010b5040813a00042a04101c60404041c00003d2401803191419100c40360f696000c0d0300c001030002e0310105202d521400e01000704c80c1208865941c0041035a6031f041154684200c0403064410021114030a5010330180e850031780c0107089039080c2506d0403800341003051011030400614034100c12034440107100050b5102034842215980e050100509000d035024500d03110b4507a0004c1c0503e41000c141e85002c021a5001d03500b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 326701205 1250 326699955 326699959
    0x30602120f040215090103090b0103120207060212090f2101020a090b070506010603050705042102040f021204021002010608070801020a03150e0c0f070203030d09060b0103150306050c04051905 84
    0x2039507940d004555180030095038041d40040c0f06030f900118098400c1e009003a454418140810f045800e076850269a44090b0301c10340b200f0300c21f03c088502d1142c0c18082500249401d00c0100201c03040300085501c68800c150070540308110420750800c050b21130700040c8003c040c4003000f4444031907003020341d43d0103035100c80d80341c2c0c00203030140c100811145118800e0f1390010303402400401c0d450f802c041c000d0f40100f0025010000f0710000b40300c0000c500110050017401c40c64402c0488600c00a140305203c16a100110094440760060042840d4079050001c1c580c1d1260f0101c9003000100c080540590040c0840d800548040c09181c201080031103054006118103895544d08001120b01030307a000e040e490850244109a0500e080442c40501007040070301010040542900e140401c6940040d107194803044500d02a07644a010045c180210b52140901c45242800d0030301074420407203100761080c0c80502009100b240d540011503001e0040700d00380c82c058440074001110080705401460740b061040e04c5428 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 326702455 1250 326701205 326701237
    0x6110c0d030e120d1a0d03090513060e0403031d070f1e0602030a0503040c0e0721180201200106030803040507060e060901111612110607022209050304030602 69
    0x3490342c00000380d40362281c0c5112105428101c050404102800803642c00500324110080b10f50001d90b02c210380e034909036200b51500d9201d2840c041c02d0001602e40b041d0310b580c200b8074280003084001c1004c3c0d800b0750311907898034000a85120303c140c01150403c241000800621407004003042c0c1034a51a100403d84040e425240c030301050050074100082e071b4600400c001600b091103003900d600d025030042c54209110306d61112046494400644480c10304031100c800080b03281c01441030441c040e412a2701c01200640040c019003104052b611958030621000034100310365000d4001446041000c80003415136264000e02c500e554a040001e16600252000d80b40d80c01011070009009000702c8081010f48000382c6041d08011400307005440c03940d85580c40c8081800b03000031a42d1105c0c8080e801101405114104c19091642030401030244007074001001d026203010400034000d070f5140f03404800520704240b045044005902c0b10740c0050b1241074802480da110202e07011082050540250403080d000902c42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 326703705 1250 326702455 326702471
    0x405015109090c0e1c050303070503071206210f08130501020d0f02071802070c0602011d0c060301092004120201080f0403090e09010209190f050109180906110c0d03 72
    0x8000c42e40c0300a10540803441c01080d60045040203548040301842d110030300c2c4405c0d90b450b100c4a0640e88111619000900004100b00b1f107180c025403c15004412511b0400641e801c04103281c803031100c40840100c619400c00a990204000381040d030401c10782c0480300303544030810103103025014034aa02905016004101681640612030300c050030000d00164018880585481a103c0c1c00071101d018103030a0341e030204086004a5409280b0000520b0103500000e1140300c000307490382c2428001c09401c00140c2040041c0881944d44a0589055841ca41000180b8080300521040a007012241800ba4075402080c0024103103280e5009201c124001c0c0c82d1942165104074079150142e2007120010f0216a1400c41809800f00b4507080c01e51000b603031800149001281c40c009500f4000c0318002d407800800e035138020f101c038001f006840c4d4001d01c001c0c01c00401550030840103540714040303955443c1c50240d0303910149080c0f00310b6400c032100760800d119055039210246403e80d40c842d130f045401940071034100380807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 326704955 1250 326703705 326703719
    0x1d0d0503150105070609050604030207050112090830160306050402030603030d110c070b0c0d030c021c03060302040c0e0405180307060b191806050405015109 69
    0x4691140072400041c08039103060030015151030b0070021066801950701c0f20b0f20000203104211142c0118001d03001098224602000108540c8040c400040da9074100f03075a400004007010f0603207000290000707540d05aa00c034090401540003240d80c3c0d5070f0411046a05004c0f0b42d1102c50314501e46040199018880c0b56140c40522060780b109980c01505503008020b0100b801140760701031504200c0054190b46000c3d05075244600d0581290895100c080000070031a03020700c0300700a518416042c0f4101030204954481d0003a4599510040303801c1e43d04081640c2111151003580140040c541c010000c102c0c2440c00c41c0300918254520202500803440c01d00410701303004880440b1017040c0540e0000b90b2401c4503540d50417005d081701070ba0b560313084408c1c06041c80025002080100103071481c0800c0e00043c400d90384030344054981541c080d0f0301503031410006100d02c1080c071207135000c010398a101a058240d41c1c02036558142161001c1462500220351410f882c0400f2221002e40d48109035032002842c0c0d0301c03800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 326706205 1250 326704955 326704957
    0x1401150e0a02090f060a05040806160804140109170a1209050304050607080405100201020705150106300912123308030a020114092a030304091d0d05 65
    0x1940503800e0300d030300025022610303540041c0400c65028000c0e500105100011801c19004042c100001c54800b050078800048200482c42e8482c80c1d41005215100e41c01a016008e498050805000704503020301542c01110250080b00003035602000001c03075410301d10327042c5545070001401b40c0006181c100e80c0c0d0403c40c2c6103004400d40c0580100107507240a10b410200701495102c1d940850358030800744800161030340c070000c0c1c0c04091105a0005a41d400591a01030309190700300d40304a820203c080c2c0180701095018041c5007400404c1c5030b00c007910403400003c401010a03081903050b042c0d420000d49804001035030b00d00e601400700980b6460b401c840d04841d0401a140b12141012440040c03034480ca8200f80300c4040303880c00544070303880141c044e41c984203040c0c2103901c200071600140c2c0d112400e00003010302c1d4140140d0710041e1390340130307280c070480c032160001d0204161071941c1d1a600700031460032115981071048030300401003040108002c842c440c0b0240c40c0400c07050400706407801103400710007055000348 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 326707455 1250 326706205 326706209
    0x9080a03081f17010c14040e150103060509150a0801060b031504060b0f090f061207110115090f0506030109080a0309030212160c05100f08180307140115 67
    0x52034040c850360780d031012244030001040c00301c201902c150360300041940e84100d031450300e022507000200d05500c011300d003e0058090f18400e40d240c58010001002414400a0703042e400c80140d8241014060b04540124064110340e04195806140314082c8070440003010440d6520000565505122650b42d00c026400c9a111384109000300600300700042600b41c02c4100c245684400030f0000800c0f03901c600340d802d001c0d00300c1c40e102840e840000940c41c0d02460810b100180040b1b04036485490b00001c2c0005508440014000e01e0600c5007981080950410a4203c2041181d5456404440c00d640340038440181440c000400d00151800780801c1c005d0806004403c0d600740c00000c036a207048407141080b8001c00207a00d054045020701640024040e1094004000d00d8260511034500d00100c1e08010242149583c4a80d00c1014111005154280c001501003215151401c204501d551030024070070b1075804000586026000005082e01042030a000300080c00030f1010007006050521140c401029000d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 326708705 1250 326707455 326707457
    0x91b09010503071a070813030515060a09020c011b182123010501030807060b0a03031d0f13062405030a1a0a080d0e04090b070804080f030a05040309080a03 68
    0x1010148400140e203098000d0038107030034501e289450020349401b0310b190006241031030b1303090791560304000380502001445142009001d034071040c1d0609a000404440c0c0034801e0104650f00401d08035031000c420350002c0700d0890f41c55616007080341c2c1494000c180c10b20020440d07820103070411002c2690040100007500041c02c0c20751500503080d0742c0c0c50f1240c800418008245d004456100c01d01c030003410a00034580214420034440d600c03810686090380995502040207406828a5039041010a5002c0303c558070700e01d0701003901040302c2c86050100d05000907071520203400501c084803909003241c03903510000c101c4032142c2886132180101101041d030b0902c00c82c1800002641400840c80740c6c08185d01002401c0380600c1803210101450f00801c507610510b40c88405140c000400e10030703141d038000e54040c54552040350700b00000c0d1a40c0e961058404005001c00c007c20061100040c100404001115230120020004944a1502400c00005482e0854007100081e8001e00001140717200040c620302a1545 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 326709955 1250 326708705 326708713
    0x12090504182013110a080c0c06150402310f060c11220501060e1005070b040305091305090c010c050a062004030303020d0b03070509010329091b09010503 67
    0x403500b80000360800030080e90300030b003207584a42514040e4424030621001141d00d00e03031504c95161000d814000020480381d03c944e02003109005994001c1480391f4010000741c00c008051000002040003801a116444100300a4039004002820741c000c40070840c45103080e62041072600d4045020040341315110740004900317240000000913010101244d680b03c80a0300c11504803880902199003001a46c8016009554880040c4092503102241c10f4201c07100b5140103003881103072360b0009d01d1840356000192000c04203102160805200e00c0031a00c1010000340340074100340303c4003107000003013000340e420304c006220b004922001540036144014045e40c1203030280124517035903200c0320050812080301d20703103500ca27000f109680d038411a800b80c40038500a070b40058403035213000b00c840111805660010302c00d0340300075802c0241da50740380301c3c2c241074951148002c0100c03041c0d006890b90311500d096103060804c20910800641c0c0a0001d080c9080c0d0580c03200c0d0b01100d0142c4410700c091014280070345c0b50580c00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 326711205 1250 326709955 326709983
    0x31209190305180607150b0406140607140304050438010801140d0204020d02090102060c040510110a06110d0b090603060a0218060a0206040b07110c040504050a1209050418 75
    0x880c54580065403c00034145502e8228240e9800e10160300c2460700108031a40c2c0c5807101d10a0801c1e20030b0801812403002920418200b06002032545c1c000c2210003800c0e038080e03a031541440c0c401802968014007002d0700c1031080d0820700750500035460342d060020041514010380c0d12440c40740d01303510200194041e1126000d41e402c003d0200b0b02c6220380c0e101d2a0b000090b40c104040161a80c0c80180301604000c0c00051311103001c0c1d00020300b060405005044c4501046c4020b101990b56510842a06203a81c14041d00e0400322640d920304203101403601610301803404417000c0c032500ca404010594210300000801c60a0710f0f54040010904040d204250590b1000000a083c3e01b4954000d06000071b0001211920301100400200168843c024000060304104244410011a1640701da0011800e003826191041c0c10441c4640e01c0e0040010284a591034a0109050200a02c00540360350f802c01c410701d50b084030110015048550074400d250103113241030041c00310604000071203010356034443d0880649038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 326712455 1250 326711205 326711227
    0x30f0c0f0f090301021303061e090b06090403090308160c0e070f23070804091407020a0201180e0405010c02070603020c0303060405060a05090405060a14010303081314031209190305 79
    0x500032142e41c54040d9030030080d059076211155403120040d48281008100043c00c1004194648801c030380c2180210304081105002583c401c0300d240d0310500a54400310240c0d00c506049400c410303598009003600700b00140c0e0703440070005800c0c40d03240c40d40900780f02c1460a54400c03480d51400170484880d07000130000400c0b41c0f111885200a8111070800101910444810101494099108550454040c1c600103000c0100004500400301840482d100f5442e0614062a02946584548000a04201288511100d100c41004e14040600400c50608080785001e241081c028092400302c4c00c05441003480000b8138a1280c0202c80042c00300902031400c40e101c52040c48050100600036a41c00280c0b44130128071915004407052089001d034001300000d0078840600e03412078076a4401d10003001044001800402c0d045840703039402c1040c3c0b07843c101c641c04140c02d140c85041c0c2c46048007011404001804c5400050320b02110340105134130b80550f60003000700d40070b0515501c035211000700842c0e024003100345c01c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 326713705 1250 326712455 326712457
    0x20312070e040c120b01020303010302130b0303210618010f03030305090c04021201030318140f0f10030e070914010e07110a06060315050423070f0308030f0c0f0f 71
    0x8859828050710300c0e4401c0000400755522042c04000040a016032850700c107500e4041c10007003a2081c000355103075504503004035080625007044441d103a5120b446d541e02c20344040048a44d0080c01c990751074448071103c0c680300b00410341581ca1506c15500702429402c00070000c41c41d039040b684c810159820301455543c003500a4680144025058000d10880f10380c035444900051042000c02d80d5403260325810361801411009600b0000c802000c0385003424810038441c1003055110041c00c5842041c90001c00380010040520092000c0c2c100b00400180300c0b8260b095040b0b1300d083c0900c40c06540344642c845e5400002ca420600c0100c001ea20f040340100000902c44d15056088049403601580c4512105411450a62880021100c0d2035940c40c1c20010300c2282e50071205103c500040c188140d0802d500d0b038074019601030800d40400d0110030749001800d0303401c102d800300426422030710705050b41e900d05100d030460b00203d40a51400f185c82c000070340448802d40440d01d01c0a50484202d0038222010b41e00382c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 326714955 1250 326713705 326713711
    0x15040b03060127090203070806010305060c04140f2409100e060304031b050105010b0d0509150a050c070f0f2d030509040608010f0c0207050111060f090a020d032d020312 74
    0x40f655070342c0c0f600016850620a03000039090b4440140410b501d11b14090303107041c0b002854583c11504c140420b020024030841400400340d000c0307900700440250500025000215070b2550b880b0712103141048042104e4000103071885500031070b803c04540d20000400c0c1c035015200250030b607006408000080c0040e018403801c1c45402e030745078004482043c060b640c807400c60b00281c00400740b4000210344820310031b901d4095258000700300b00203800c06075a9400d00b145442e80103000320b480161100002146c00d00c400040d80c0c40c03036030001c4032440d031003441342014006c8003110501903030142052080019540181603921108a9003042030030307130b008641c0e2802c541c640c02c2071075030304c0c0d01c151a4800010038981c00d0198085400303110000081e5422020341c0a0b2800e040b550015040c02030b80e09000c004880d000c5a51980002c644403e80b40e96542e9802c414200728102c0340080d800729282c62070500341540010300103941a03085942c1990a01d840302d4a0010591444ac1d00c2c0046c0d20801c03401030000440d06007160 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 326716205 1250 326714955 326715029
    0xe0901060b0d02040819020105032e0b070c091e0e10050103030810240e040603020301020703120e0a0809060904060302030105090c0a0906050f060a0509030615040b030601 75
    0x1000ca0300c0e0041a4101e90012112244242c1c0220b002e00586030144400201c504544034001c903035200070350001c0d0481c000100142503030240403034040030301c1020a02c1c180c004608034030f000e00095240c20390b01d00135400a200c10b81c0c1c4400c13508004500c620b03151240d990311010010045d00d1540b00c41c2809030141c00c0e006203440c580c0c01200c214242c5541c4a001d41c0d800b0710f209403910703c814900082c60742101030540e407000a0400440388554010035a240d45088030032041e1904c2d50160000401040c064030403544002c0d01984001000002e256101458103400d0b09030000900002404080075a5201b02e031f8040581000381c01c11080c0e171245004001031a000201a1010a099940303400280c21182e040b01e803500c4603080010880085d142205805001d084082e804201941c14400890707421104401c0884c0a850000340c1081d1142c0250140d50304181d00a08039082468405c2041c40e4030800070491a018500745004c8001624021030124103803228641000c912103e02c1c00011142e00c01140040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 326717455 1250 326716205 326716211
    0xb030705041e08010c0c200a12031e110309090703180b06040b1801030201050306130e03090a051c02090c160f050c030708030720031b13060303090e0901 67
    0x644001c08440800b6650404040c9140c0645031441c190b0940c0e41c806074403000c01030b1010882001440c02e104950040c4070740147d003118485604045400c01105401c140044d04001c1c4000080651140700c4861116401b07003440b00e68600d0b440152030114900d410707005142c00610880180b81400440f060b07110a0900e0040341002071001d002c480030b87d0400094444099517410040c40c1d04160081400c503c10a83d840b009041c08000300f0300e8481018040241000700010104100750b9444d10410b4450a20080411070104d0240384169260311010340c4e203006002841d00010300d4a4407441002c1450045440d10004020f590308014900c08020002c1441c0e000c188080c0541182c02c644c0c0482642c4078001004000d041410b2942c5040d80100986103c0c0c2d0145505201c0c41e400803003604c0d0460750040c40307648603551820342c00d004d041e81096901d805100c0c0780e188e00b4500c80e070404028107240c416560b0a08803440c10780b06c03400b07440303282c000540410030b40401040a4060f803102a80e00c0308101d0000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 326718705 1250 326717455 326717459
    0x1d0a0609020a020a0c060c05070e0a1103100e0c03160f030e030c060103020405010e01031203020a0e12031c0e1e030403060c11060609040b06100309050706030f060f0f0b03070504 78
    0x12000c90700001c00c0ca20040c4c0c0600e2203641000203400c940c0024041c00e081c201154036490b55140d54440807030081030042c2d82c0c1d00e008628000482d03005190117003410311149450349412001810004002c7c46262400d031440004550014150422179000d09405240030705081e900703510580d07c01040d03020000c101691240e0342c13941600280060650300c84414040c10043d451401040207403901038202e00c03a514545401080005c10030a10608019007506001d6100c80c0940b2003504c040800d400710642042a40210b44e4518501000a10b101d814640346840f04030b06c1c40b11010308451024440c0b40702d6500a003060b00d241d4415a0103181e8400c1003404685c40c098070ba507140b000342c0e58115605000b04808124244241a040c0031880d4002c4040d034140300c4900e400d40b28408581c0b00a404c05d17000e2440c0300c00520500c0d02c01e0b081110440d8200080b0b51a0541e101d2000307008000612210004625003000820b900404040c07000454240980c18205107040040848840d40081c11500901c0020040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 326719955 1250 326718705 326718719
    0x2a210b060d120e040f020f03130606121505070216140a03060c08060a0909030503010b1803011113060903081207051c0b120309180912070f0515011d0a06 67
    0x60140305080c143d4032038030980f1650302070000303591442d00010082401445201841d10082d0140d0782e222114500c2204c403a00141011801000300b5000345008008140b9124148500c00849524040c01c80704100080d5880c038900320f8640780b81841500321b0f080b02c0c0740c08101d21800c0322942c85c0d900200070544a8900c1c1c0c0d90703030343e00b00b2500802c3d0b450f80880c0721641040314500c0c1c020804001801410030500c66241d090303070004d2551005009401e640c840200d03010010040b2001c2c2c22042060150013088054520304182c42d00c0d40006101880500060034040303185403040c01c00a08980e40300007440d003045c400d02c200307c2500ea0014501d0082210500c09481052086003061480c0743d0010000034500c15a2424000720a00005402003564000c00110029888240c8003051103141100401c880e521808010303401e11200030085282c080d0080303801002e0141d1800c02100141c421340c125845521001080d2864220900c1006600758040c3d89401c10340c07440315611036003c6400c6400040341500c0d040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 326721205 1250 326719955 326719973
    0x6040204020306061b07061e021f020705030a020c1e0112180506040b04121d040f0f090b01050406290c010929012304020706092a210b060d 61
    0x42c0e00c41c10364001c0c6c804000782600f012007050074003a440030070000034015410184d074443c00004c1c9a507400d284a8800e417072810380b03a81507940f5194050b003980d641c1c4240e03200c001d540750303a0b42c60171601c10304ca80b42407201710041c222500c030780711901a11250010302d00c8036031140082418181040450400c0f080304000942d00f845420301c00d9209030350a800382c0c1001d00348011240d05554404007805100c5003540041c0c00c00c803a90030725200f07044a010609640c0b1242240c041c0402e07241c00d035412400c04900350b041042201909058560946082158030341d00d030006400500c1130a81941d095981100321918080d03054000c0405c524140700224025003942c0c0d90408202c040304000400340d18040007141e481e07504400990041410350303943c000010942e94410707806451103820510440d400078140c01003144a8202c0d40350b041e080b5400118014003071000d0070140d84400c1c2190128001c5020104070503102c554002c5100c036000c5081c074441400fa54410f05102c602a10840c2c0c45103002080c00c0000d40188 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 326722455 1250 326721205 326721247
    0x3010c05181c12051207030c36080106050f03070b04120809060a050306030c01210e150c130605121909020405092505031b06190f0e0103050402030604020402030606 72
    0x50703a050b80d117000880d284100e101024240c07404041c1061214a155540a80c0d01d01424400800e840603408860b42c80071018408510008003044042000040703010b810f611242c200c0d001940c0e54070200746a0001c0603110383d554000e104d16190b0600040c05403001c0f82c10030100061090b01845c0c513201380d070030014100340c00803008800080c1b00081049080d003800d02044000000c28208810460280c0c0c0c662841d101c010000401c207503030f0350003089502c0c0404202d0101c1c544810802c1c0000e0b07080c134458540d02d40d44403841160913075000560000715240300380c003200c20407103806039490007e4440d40405229820b070007050060b442d0300c42440501581e42e900c10540220b4041004002c0c0c90400d181240a00c90844103d0030151040070040141d620b022400310348144140c4841042e400c05240010100c0c0034a04560215804100c1121001c81e00f05100100d50310f02c07a101c0001c0a45e02c9001102500d801702c9000350103400c8440802c006007850703005550080402400a400e1402403941c0040600b080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 326723705 1250 326722455 326722457
    0x120e060103060b100909050618040c05030d020f03030c07080708032401020d021f0e060405010509060f0402010f08090102090d0609020a05270c070c1403010c05181c12 73
    0x48004100b001120700c50641c0d881825900025a4444910060018a254032030b801100e910f40002414641d51002a4404030030f007038202402504090800b18520b03c5d46000352406031007051600851a4000a070310501d401c0d101000790314541d540c00c00d202c20307504100402c03078450200344241000919030030f010b144103810b0b0300c0e044200c41c10301142e0191242d1810550394195084072600c0d945075507000c034520f0218480508074048003603014032000010424511021024022002400300700302c0f064000c18001c0c0c0c5a01c085583d284c403100b84208444100b614000e01050500b01c0c0d4111085c040d2030000c5d8041005d000041c108144030300855815072113040103c6542c2c0c2d45183c42c0c1c04524101d4403c01c050242641c03200c904150181c0700c02000580c05101c00c04110351100000d40342c102d824100c0380d00c0d80d408a000040d00d99141a54803070a080315072001d20a500b00b180ea10303031003403148040d0350b02c10381050001421040f11b0801c5c401701000001c0d900da540c04989000704007203244003031421010046 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 326724955 1250 326723705 326723713
    0x3120a02010903090b030903070305091804080d060e13060504170408070801050a050f060d0c090f020307081305070b09010e030102040311090709030b011401110d030e0f0102030c04060e01120e 84
    0x860f2500a01502003a0040d2654060500c280804201d00100742d843c0d4641c18101103a403850000c002038103404180040306282c8220300304000070400b90300050181c44064500501c4015101c94284107011411540d2044c00d0080720100b50114242c0d8110941090040a910701041c01142d2810350076409500941256070000d081040958000d1003860b5000651040030402ca080c2103516119100300a40014420100100441c2c14007100005d0b10005014050041001d848600a071501a42049074640301007a0080002010303c0380e0701465006280e40040a09075240c1042a05a083d401c1000c2d143d04006079840c0840c0c2c0c40d02c00b4401003011310300803c2102d00c1c999480c820030540070001030000c4100481005c04100217030724156158103581c0b81c0710411155528407801262215028082a0181c1c8607510b61440c03003075050f9011406006545c0191000180c130030312294240e2009484008004204010421007944100d581522010051401ca480740042a201105a50a81024840d81d0304 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 326726205 1250 326724955 326724971
    0x170c0406021b090606130f1212300b1503040c0b07030f081306021210061b230a050c011218020d060605130614030303040b041103120a0201 61
    0x180400100180d9400100d42d8241020082e0103c0e469101c0980840d008900108690100400a0769414003420582500680e10741d0f032452034075400e810840c001e90315629000b4001468901ca048a05100c2c01b0041058001c000c402200007103c5146c90300c58102251f468104c400c4640d58000b0b07140c0f01d00d00511110780c0b24181801d007c05103000f2a802540e039090108245070020b600904080a40007131800e012050f5540e003c01300c10202444240100a90b01c0011250300141c00c011420f4040c02441b03000c4074403913445038010780d5181d014160005040681c0b01c40138000904540703c10328041d2400002c21640300901d402c451404804540846141c0c0000661218550744480352048001501c4d00601111740212623444034a500e54001034000c4004804640600001d508800e00a0202500078042146180329080c0108100d02844000452072900000ca07458000152401103402404200320740d10f65959581150840f04181078143c0102c00e80d42c1c80a00071031000c0d01c40501c454001042d003070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 326727455 1250 326726205 326726207
    0x60d020409050a0612120305092b03060b040b0f0c0a02031e0607171816080a1104111b010e0106092403030801090b010302090907230403030c030c03170c0406 69
    0x144450300a03038148098110007030701186c0b001d803c202d03d4050b103003000516916800c05144c20281002030302c4001443c50885410f1012603c48004601c00440ea030422249440707841c0d21600f48100d10551040b20070a002e94450025204018050110820100c3c2c5081c1d1883d03000c0b0381440b40c03000700e1000c0031040c4403070f0400a00c011b204941d0300840310702d4290407050070b1a80210910070098602c880d040d13882114100c0e00c442c1000b000220040c150300d10744525a42d0f0350166650000c0480884049081240140450805018a03900802074420301402d06ca03400d204101900142d030321100f02036485422650070002c0a106010240040c08004030700c0c03d54500a00c80040042881c19081c5460080100007007076210900d41e056850f14003020918840b1840120081e0141c1c010840d480041e44050007003090704988400c110210743c9980854242580c50700412a004034440940403440b44491480040d11030f22424684511909001020b0101c8a0742c0f40c0d60301a044660380c80c0d10740c000806228072 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 326728705 1250 326727455 326727461
    0x504021309151a0a08040b04020d23010c110c0f01020a0609050114010605091f170f072003030a02030709030803070815040e07050609030708030307121109010c11060d020409050a 78
    0x3d2000308515240104a503001080717007400a0003d0580742e20440420115078610101d1041d00d0780103403107a040110400245111101001045015503281200004117236000c0c2421082201181e400f0b0460100907a041c000c0b48108940c03903a0460041401c01c10000d07a0398030408081b24003410000940c400980d044410240042c1c00c10030502ca400d00480d0000d503101011284040c101c55100700c0711628084040c0c500c101e2022403001c0300c2010310100000d02040005c40c41c45240103584202c42c1c90641c854041043e102c4400c0349071030740c01c2000002d069a40e2a001540c00c0460b52034045d00250340d94985400580080e91b480002801c1d00d400d100e001c822040450820341000c036410002c1007a030414150b641c2c4039522505000e800080f8061090350740074001c0e1401426a502030329a03d00c0c00307a400400c03615808a0741d01900749804201030f01e2108100a5a241c01010b8640d2074058040b51150f0060102c0d404034268080c5040028403d11209800600700078195440d002c943c034200410786a0503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 326729955 1250 326728705 326728739
    0xf030b0a06030209060d080d0207030210150b07030809070302041a0301060509101404090204090f140d09090e0c040e07091b08040f0302030403170406030e010608030301050402130915 80
    0x24074140202400940e807140300700b0b40c01c114101c0300749500c2106031400014901900c0b8540071030301d201040031801d258007c201400c0c3d0700d0440000300305000031032038011510a9540a0035803c2d0400b4030610b00041e00071000c4a400060103c110390700d0660783d41c005000c0c1e070700e50316501d0040c00c08030090340310505003402030201420084615a10910b8002c6040b00da000051040da4545100000103a0a41c1c1307466008510460300078009101324021414043c0340301809107000c80c0c15141c0703041102545500407410180c407014a99400071071034605201d0034090708000c030303c51500d03000c1c054440b0f42560300c0b441082c2b03030190300030050311515281c4400725040700c07010380d00642c1c0c1203190201c145410384d01501c071945c05544036000c204400e07901d0070124958051600f0042141002500f070110382c0841380054412036035a40e80c10302058032520b603e01e00340c410070f10a410740d6a000748010b0119103819000f52420521211101540c3c0e41d483e030442054440b1860410f00f090426482404050040c481c5603107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 326731205 1250 326729955 326729971
    0x31303030e010908120702190b0705071d010909021c061b051305150d0903020a11041802120a200f03150c030a1b0e0901060201150b0d0e070f030b 64
    0x21440e1030000072584172103200f01c0300703529008001050000c556411004506040c01d0704080c0c100503481e00324007410f55124190035507081c0300700400014044408682c80d510101c82c403650005a074078094100000d00f12610089070700519130345507090003103401c050000f0f206000e2440444d0001c0c441084007490009040f0100412004220040e09011035428103030440384281c0e1500c24800c1c2d4441038610307074018200440c02a505200c40e8034280342c1c0c0082c21503c0e40e07020714108502a440801044210780500304218800300801d2100400b40c94080300703542200400c00b0560321880041d944155140148030008402800042d071141010300300418103210201c020b800410f21240c01141031a1813240092a49100e0b10000000403411002904201c81840120410482c50030700c0c4000a0310000d076112a850058400d03030300008045e44140900008510b14001c0d0f12034650034000d00324520342c8510f41c90074601e034481c5241200903100b0400a0000c002d040010010541180382c41302c502d00001d80048 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 326732455 1250 326731205 326731217
    0x6090717040f05011a010e150f090a030507290313030e03030c010207060603150203190c05040f14090603120d0e2d07060206151903060204090e150903090111070503031303030e01 78
    0x3808d805003400c2142d00b0180d07150722542d1642d00302c0000a094060300c2d08020014010352000095110010201c4068007024410180301c404001c41050124042203d082c0c4440000d12800340110340242c0640d203100070b024055070302e8a0701040102e0309a900203001107600b41d603078000401c10b0084118140360880c0380c4640940c82c1d4104428052041c40d802100381c50290354501c4c0c00c840607400380301100d0060041099140e4403035903a00e2841e0072413082d080c07000c2c083d40000c00021440c1c54082a460fa01c1400300d5a0035041c02d085c490a03000070314a450714103041d480350781140e21600c05020350120b411000d410b01c115001c2c24001c2e01508200300c40c0e2001c1c09540c01038040c0140007218422082c60044240c0340b228243e8000002d10424031038035440600b1207440007402081409031a0403208620311118120344903e21075080380069120212500403441d0410300c10002298414012425160b440e041141c3c2a1502e81c00043c0c02c0d0713404a58100341000d0040420010150030280342c0011500c00d003000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 326733705 1250 326732455 326732479
    0x6010903170a200705010f0513140306060d03050a03020a03020403050601080601051008010e010e040222020a090803040305060c0f04180902040605040b13020d2406030506090717040f05011a010e 85
    0x299403614136001d4241400f82d400b10051405114500b80ca40d141c101ca000404900c0d9208082c030140c41029103014000c1c0104800110507040491078140c100768035545031840c044000504a0007034002101c0c010402d0307020000000824410800d080c040c00c41800a080103501d0300d000c10805410a0712290113101d00f0b100100b080e520111072507411a84100c100907590303511803002426180c80c52041654040004145c02c20b0012240d02410700f0241948074507010903152040c0a6903401284001802c90307000c0c40015280000000180506174400c404840c2001c0e01d44503280f20441c8810700c0c085030595905070000a61405021f91801018283c804201300d00c28200030074201100d50554040090700010149130034180c41d031044030a490003800500c1050000440b000c03038640144034180010781410003080d043d10700101010700401c565101c541c4480d5224024a9440fa4001c0090350078132116100d200204001f8010107803540c081516007010705808800140030000110380250050000d0021 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 326734955 1250 326733705 326733767
    0x80c040501080414010e012013171608030909150d12270e010803030702060703150f060c06050a02162a0e1503010b060a03020306010903170a 62
    0x12201a5a000c0c60150441d40e200d040c07241c001000324601030725540c40c00200240d495419031140c542c0c6400d00001c070184218101364200b03180280540c1500c400b150901c10040d0405000da011600d504080c01d80740d8481c07189905801400b590340c040c102c6500002125400781c600100113235402041070600d9101d911940c00460ba800c00303a0400140140114010360710b603140900c4ca000800040020648200b407500c801c1440801014420100300100d650004034101c0404800d4031300c503203410381c02400c00b5600c8950031000340041c40904074000c10303420008505c13005080201000f8080720b440d0b11103004060300c0c10750211038009086401403481403040030303001c0c0c400d0074800145503006001030321950100c00140b080054144401b018403070f154500003810905111400c1c0c070541080d102a10024000b42c01e25003aa02000310060b8044010840841401c0c040d82c0a15080501807401002154407555252070f00d640c1c402035030204040c04114608880c2d44062032140000c3d03004100d120050035104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 326736205 1250 326734955 326734957
    0x140f0d0806010c030c060515011701030f081e16110d030503070e2d0a090504020a03060507050c0f100f110d022110030b06030a12050906040f0308090907080c 69
    0x4581e60410103608003e40c14940f0915404598036000102000700341801c46012526680c0d041255003c030703a080780c45440303100592110360304030381c0c0003e90b5508a0082e581c8841a41c1d10960301000c3c2d0404a00c50056138401500107041e02804000c00c1d2a1283c01d1401e00c0c40b44910070150030341c441d1156000e6100000c1e0b116050301d41080742410b00070b40004000000178020000312022520900404450b03441c0191700c01150f408001054490b8030559803901e010350242d400c101c501a41240801c0c0c0104002001075112aa04c6509840c0440c104040c004c80207051801e1070010101941c412420300329000d820380b081494840c030b0400d00b0016070100e40c8940702c0d94051480e801c0c65035940440c0c1100c2403981c04160728905d012100750000c1300c2c940201c03000c101c0080c500080d2507020314040020014240010151480390708020220550129410304030b40c07540c0961246500140300b40000200140c0c4800d00307070003944c0b00701402c949402100d000e110b07900308010800020056904180044450a80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 326737455 1250 326736205 326736211
    0x3090c0a0b181909020309011a090c040612060312081014031c0905060a23030601021905011805010915060609090b04021209061503010b300a140f0d08 66
    0x2959105400002d14034203007150803e64042e0510500000c1003140d94581980130281784410320b000c40000401603814084242400c60314450003500c100001d00000e40100030000418820450129459031690746500b1218201401840421030f07203000e012503141072110f5034015005608840e641c41e90150000b84d603a46400125000184005c181d800c030443c410320591014190240c45103540340c0c040385c4014080028540c4000c110201c1c0c94400400380c100700116801844141e0003010040300304c0146106413810b8100072031f195941c8840c40520f24400710341c8407003003074060400040e0f0b810403401c10101d051540030141101d54034080041c480c0c42e4200465500f0f0760040040006c0641000004c50003d01c6403c8200c442140c4900800c40c2c0401d0000d002d9204121410380884040203080525098800c0551111351000a0004981d8000308090041690481c05c00c0c15840351846401d03100d007401640c40f806c0d41d604005600e1045800b80c20004540c00c0480761004054182e855003002741140806 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 326738705 1250 326737455 326737459
    0x607020c130e0607050d0b010e0d03110f0d020114010518010e070201140c0403110a05090a09051e010c0207152c18072a032303090c0a0b18 61
    0x288800c0707082265408401071101000032503580e07041001c400f500719007003c01c030504d0f91818205071094551150340d1a4100340000b82c000943c21015541c1581c4003401c0c9405211588281d030790800c10340390100311070b11100c3c020707400016070000c07848489100204143c21142c05504180040d4850004032444c0b60b0443d20071891740d1900707845401c0101d024010548020b202c0c400c0d074000b40302110402d08001c100f228407900d40e003089462444140300c8a20a10b200e02039100310250001440100ca50304100a014400d4007500c120081c8402e94220704030254566a17420382d5250312408134a901000303c400645410700202c0303001c05c4001c000601c021103440b920804190301d0340091a0452205030000503082d4014010400c03a40c60b03249228040d6000c0b1000303000034020b25840c0003140d050951310354050035000010036020312a618151140050002000030b607007081d594000c0751000c5200511701a160000152112545250030420847c030a9000502260030410061500323091b005049a604602 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 326739955 1250 326738705 326738719
    0xa270b03040807050703051f05070c11060c03030f0412080412050721030903030c0302041d04020f060d0603020f0609090a05070e040903030b030607030c080703110f07060911030607020c 81
    0x15454442e4590007071070001013051140e01004000c101002c210341d00c4035080d0750800c2070304640030a1000140c8105a494201160001c4c082101044a196179002200406429140ba000c2c040365003520f10342c4116014000200d80800b84002c0002d862404001e002c240d244c6403c0f43d003070a8550448a40740d1800c48000c1c414006034050030002c0c0420120a034004514803110100c07021100a409440c424004a000074500024481c1c028060b1003a913055801c202003a40001410510070340f40b41d40c000c1c00503a0b001c604003462003220f0341c424004000070444a50041042465071041c0722400590078001ca204a50520401e40542c407220191b540c070440d400c1c0301044503201c400c0e0644081203101c1095400ca0f040c8000d1360103060f0140c0090240d10020f0b412150342d681c0d040301c00c900315103e140d400c00008401c0d0000c1403c20380719400c00d02d410843c10100c0f6180c001440c1c0514460f52285030304a0700c10b44c5524285003030014100c60602c10301d01c15006080b1514007200025207910711300c08054400c0365 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 326741205 1250 326739955 326739961
    0x3308010302010203042d030818030712080c0304170f150106080c0a090e1f0f05031e07080102130602192316031b0603090b01090b060c010609020a270b03 67
    0x144043d0200c090280d43e1170b0501000d1f03260705050180d81e2200c0050300c805542a01009180d09000a4503c229849040f99122050213030b520f01c003490f0b1060300c0b8422540300c03c5c80080b4812030200c42051546854100900f4401e4401c03141ca41402070008010719602e4192004100071500030012591140398140000c0d640c011840c0107403110300715a041a00b40c88280400c028403411036a049801c5428400c3c3d440c0e0400d039945a1111580c40d690050b140c25404c440d62103542c0d00181c1000302034170307c20306040d140c040d500c1d100e0103422a00039800c80f0f5100802c440040003455014801e0890003200c00c18449014000354680800e00201e10004180c40307449040c802c444800705101601d015050708550840c17084d034034107090121250250000d070800c850801c000421500030b208071014540d20900f540c00988c6810032000c028010300345070a4000340100042e0403904170a120301c20240c070492a00680310100c2c0b03030009150784a6100a1210041c20f40c41c141361501c61841d4600486640c55943d954980d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 326742455 1250 326741205 326741249
    0x12070b0d11071b0f0509040809010822030513090209030703080d0605060c0303060a080f1504170a02011d01141303030e0a030903020312031303080c04330801030201020304 75
    0x4071508a0141c603403144061a904407420f921844411503040c40c50701c05000b9240d074104a900302090b50020038800d01044031140d954043c5945560101c0d00d0740701c20032000c4074101c45510381c01461718100d001860004ea4441547e40080c83e00e0080c0a08034801c50a00004501181d03460040e8040501658401f0500341141e6442341c2200004d041d014003455162640f031404c41d90340307030000c0c3c3d10345102e04103503800030460300e00c0000c00130341200301c2c08010059555102d03020001080090000c0e2a07428103140e928000f0640d000080a10004135800000c11409950fa40340c41450490003501c4903034108a03140002814456201d500222031404142094910789070980007010310300b80c07040c2d80c1d0141c03e014000303054003c2c008000703c0c0c0c001c5d008d96001082c000903082c145c0c8030865407500035203100c40102001c00d1103014407c0d884000c00002510302031700c2d842e440d07544109000b44210342010514030034000c2031008c1607000c9400040e0030060080e505550011b51240a2070003001e030b004850f001c60003089 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 326743705 1250 326742455 326742457
    0x4022416080d06030501150b0304081210090e0c01030608030c0a06020d150e070311090913050a0b0109150e0408190302160c050f090c0a030e03040812070212070b0d11 73
    0x165007180810070baa51300e1506034040c04501405400f910100700b0300080100c180405c0b24410360b40b02c41c1442c54070300340d010300c2050300034050844880340c00c0b0184081425000c5108900c040c0951000400010060340c0006083d22815006540d09070401d0100c907940d0300d0b00007082d05000307a0100b00035883d0360b855881200203000e525802e070008058160300040303002ca4641d0040c05a0860b540c1031080481803c0404c4039481540c80d895000800134001800d5143d451048041091246054070440c1000e515040c034070a03800e0b0004c40d0a144e5698083c07036504a1608490000c0482401c0b500b0a490a07840c2c01340d490040b50425203045881c0c0c0c0011040703504c03d504884496441e810450324000460804000001140c01003d014042204001c1c42610701140f04034420b41d05000041d19208502d4400c4014181d140c8510750240310600000c60341d01ca0603c850a840c0306d030402c0b20f641b1030000d401000042c41043e90360310f01a400c00c8500f0301c03080403160101e07800c0494004011070810280d00e80a80340e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 326744955 1250 326743705 326743717
    0x20111070b0f061f0309050a0203100603171602040f201c0e1c02070b0720241b010f02120609070e06090111010213180c1704050f0f060402241608 64
    0x850700bc1d00ca00440040604d9004009980c010040340343c0101011820080c948603142c0314014820500504100528281d0080d005205001c1008600c035540c880c900c030840c40e42c1c2c41c10181e0020000c1140c43c945a0031080d55003e030030308040c0c00d111440210030299220310401c502e00c500d0500080c21028801d0003004500010f00070b08001e40da96000a0a1100d04403800b0f070740004a4800031010b480492078001080c102208101050b440e115181c0c0c4030340741c500c0d4820740c1728200900d0482c40404201d8400c0c03090780c01d40510440c3c05a0b944906402111820303800825030740c03082142e01e0501841e99400410310403070302001c2da5503e50324200a00180c81060040d40003103070540c0000341e041c40550782102080c0c111411088401710105c01d4910110a8411100c40c000002d02100c000c040e02d80314424070903420038003810544000c00d410129440c20320402190007189070f4001c0c410b10003181049505802d05007818805101c078440e0481e0100c5e018071401914162a83c4188000001d110010089400b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 326746205 1250 326744955 326744959
    0x130204052a0a1b0807060b0105030f161809140a111b01090204091406061f230c03030f01050f0a0303080a0b190305100b061603020111070b0f061f0309050a02 69
    0x40340134036006007294000e000440d1b10904041010080e54000c4042d00d00030241700c1e00e401d525690b901034480304010540c90b02ca081246840c11450700380106550312010b0194101d0104008407203100d650754008020b0711503200140382401010b56600c1c46010764a0610101c0e00304201c0c100f80c0b45000303000d840302c1100603511070318107000b40081011250000c0d00b0b181110042c0c0e0381c941d4400081080828011a040c2c1e1800b08804d00181c0840c40342005589980c0410004412148401095103a40c0c108d9030700203c017a40004144a480440e44c00f0060040c8030840744156080c0c1042c010444913803a610004041c0729161011480b1421030f074000f201c205001a000344c4d1a6004405802007485052200356464084c0688444c151481030180c3c040c905c10151406141441030204080030f0700583d01c05900310355035020314412030a0900010480607004141c090b40307500b07042060310562200580513a01c1030280401405882d04441c2880c96500ca0394100040d03c0005401d0060404039a001e00075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 326747455 1250 326746205 326746247
    0xa020c150915280b010210050603061317040f08070b041a03070c0210120b0a030b060f0a080708030307090b070b01090209030c04020d0f141306090812130204052a0a 72
    0x30f103034800d540d031102e00044400d9080b101280d815907442d0048400a03140c4540541220000441c006070000303070b04100c51b10a01403102c6520403000f050946402680103e03100360f564103c20811a1010426203005d032842108a0f441c040ca40500308000c8502400031038524040480040d2105001d440515a19a00503140c000c2505030300c80001c248503c40740e4042c098a04d0403200c02c0050a0141c03081054a9000d942446a900c8403000c004030781d01e000181ca5846002d185010a50403030030310101006028440040d0b03220304100710b02a00801640d0045541c50109000c9100800c100e08429411508250340040c0e0340c91000d4003007814500c95190305904540009258909401d4941c485104d181c200340082241e01004800e00100810503100d118038000d42d40390000128009510882100d48100300c0c1900d0101007100001e181d42c012603001d83c60720040e5040ca01942081c0c0680e5902c802d00300c191401c42c0080000c0051401d600c02c40303c403003400001c9401a06980103007400b00415041109070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 326748705 1250 326747455 326747521
    0x1a130503030903031503150a0b041112010315090c0302040203040807120207060f1103090d020316032d050703030f09120b0402010815060d020f04090203010b040801140105060304061505090a020c150915 88
    0x2100e4070b090700f3b00c4109c8140019004800c0c0030f0095128054003140e0100301c00440e60300c1c1d5000c000194001900660f02c941c0104a5140068440c3c40c4484110f9056000f915081c3c0c5044005001d151500c4010000e00420030700c481d02c20040402264168203045510088025107800824502010000c0341034242101d400c0200500848c00184135184010326107818081e5a810205444040c0e1a9001410b60703010290501c002401a184035061480e64a010200c5c1680c9580d5614006800ca100380c81c0c0032405010300c800d6503401000b0a5219410b9038001221140000128a05118941250b02203503030116256228448010450380200340c0907005548950f121100444184d0052084104a6290010404440e004850080d040f144014222801c0d81c0e1103885550141c110b0310305003111a001400089a550b503140f0910380a041c201c0d80068031803040340030107840c00410b40740304040c0c500d244080010592000034100b044161407841c0780f91949a00410b81420311401c2c191004200b40c025030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 326749955 1250 326748705 326748727
    0x19051b0d06080709110f030c07230607171303112e0905100f0902031b041d03070615080607030c0e0105071a130503030903031503150a0b0411 62
    0x4078038280c4210701c0554040a43d600c04000440d104d1700301201c0429030034440d5076100d10406002c0d550094501d11081e10703040e0740b40d40b00f581004414410030042d03801c2459a12020504001c05648025103040003418024000442006007400078014001c44481c9254542014800c120b008a0090314134216096041c907a150501c108038000d20312030200f0011254489222118080d4140050b005809028145181c000c054050b06c8611103150010780c807000c4031001038404002c01d01c0421413244503110050344800801040d155003901c220030306001440d04404504012040f2004140c0c40000040c60902c1140803440c02110b61f4071015660143c40300300304d00142c16401c1048010025940d00e844450070400555590062003005022041c00c05c07582444010041101600000c0503a2000040491030b41c5a51540d4070071140b07050180c1010042c030a01c130340b8016994a024404401905101a130483e40b030088070002403600d0f0364a901d40400c211742d6200c40e40140700e2180128011981c922104407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 326751205 1250 326749955 326749961
    0x5010501150512011511100c080c04061d040603021903021003052701020c010c0c1209030f031b0b040b100b0a140c030909090601030b010b0319051b0d 66
    0x3080c401446600c070241c01e4054401d104442401084000c0700c6020303401e10350300042c40203284401030144407550018030001c28040080c160781d00034501c0c003c50f0085222100805604014040d0f420f0740406110521509801180e4003029090f010300030000401d00300c0000c0c01038440d80d0320213500308601d40700542d5007801d401401d42c1540e00950b808000071920407030480440d9011a00300b8002418407209070005002004d0450301d100f084c200150900519800d41801c4441d8140c1c9080883c507114516000c103d000c4440c03401407141414110100380c51038807001c0d269041900021304000d01203c841c22803545401600d12060380208503c2c20754030701407400105018003a60403450f50b005200d000103d600c007583c02c45607444400e82d254905400442c600c1603070b0707800c110b801c0d00381c9000c18000407440e903ca55541505c45c4030a42c0c028082c5514605004800e1441a00141f8690b2020000c000b06513070a031499040782d0201010004040c3c1d603e034130b401000618074013080c000b80b1002030078210061403a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 326752455 1250 326751205 326751209
    0x1707120807030506030d1706030f0106141f0807050705070f09020d05060316091109060d09020a15050702131803020102040510020f063c0a051302031b061605010501 72
    0x42c408000b0354580e00304250b0b45150580c080800960ba1000001031a1482da60701a0840030160841c1e0000e15005101807e443c07440c0c001a008210340303909202c9a20700070022a552148a8880da803028081d004024400b140c010041018000001440400c200c01003060800410310302e19605000380e111113000c00030f1b5000d5021080054200004120035160100e0032400956090543c048410f241030700d1100036050708010380b88040400d1040100540350a40207005d180000c4070700051180c06c5204111080584d80c000c801522101c4600900391600701080712003154048400c5e490315041c601d44003014290f80d42048a01c0e000f074100c51802c2603015002707801921401c44194880e0b480c0c0c80c0c01240d0301d002c00c8000030f006a0008001c00c0c5180c92000034151103082811001c4215110a190f85031418143c10341e0a00045902c0100318608125118541e00014501000c0f00440401d4001954078140c0a061800141640b100c0c00c4040d40c8110845160060420f42c10041c00c1407030800e036008140034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 326753705 1250 326752455 326752457
    0x30902010203071a190c0f0810051c0212120913090204150305010f0209031002030709030506072c06180103060906090e010606020c06040303030b0f12010506030d090609031707120807 80
    0x7940004ea40c06041d1b0007400c5510a0075910140c0500801100310b69200c2c0240c10345101000580e00410191140c02c07462203008051582c88904d000c10b84184101d0281414590310f550b041a0011004284044100c0e411820111070500404c100d5544480043c226036000942c01450054071072414244041b5010449008000801c00100601c0540040c2e2058482503540354100122654404000b64007441e00700c81c1ca4906103141da03440390303140340c030f000d900f40e070f1f40f1000c500322203d16144901529400f1256404000c0c20b000e007010b050340826020301561400c1c0782b00815195585000764842e03072004c1d00400c0742a200388078165035000010001c000d08007100d81e0320350a00300041509800000e200003c014080c0c840b52400745103032000c0b4000c240d520001c642c0200c2c0400003d0702d65031640341c00b084022001c0000a15400c201c02058900341d92a1007034020300655060401c036107500f01600c072049a8003c94120350303009494031100240d01c2000700082040c0b00c101d0210030700551006a00d8400e10315 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 326754955 1250 326753705 326753731
    0xf060e10060302030705040b0f040504020406171b03060108190216172104060b031203011403070e070f0309050a050a0b0a0e0607030b030c03060a0b100903050d030902010203071a 78
    0x750320085040e480221128404128104004c205030741e1060f0080040140d0044910b082503215000127059a000341d102ca4001030b801144140340000142a0540103030340d0b04276084414010401040c42c50100803e030a051003082d00010744a40d0b5003266107a81e095501108540d551044000158160041c071f5050721020004030034803035208c2482088415401c1c5580e05c1280d060f400c02503d584407036004101312407080c2c4510003040d41ea202004004110200e644450351298149518a80785180e103200203803080e40b2a2504010048580c03c0300c0d82c202c94036141c020b06590800c0019805080d00030300090851181100e00d03414084c000c298840c0c01c51245c900c0200760b17160741c10790506413901001000781903004000410400c03800796201c6c00309480f02400740c5683c1c00d40000082d0810104403042c142c0c9544034942c43d00e0314a4140d204030b03104c001c0c6050000c842400c580310300c1d0362552200011301c285640c0b0402c103c103580c020015140003540c0841c2c0456804414071408034415000c1d2028840144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 326756205 1250 326754955 326754959
    0x170402030a0209062106091506090112140613140c010804060203181204060206010b070c140f04090606090c02030c070326041805070c200a090e010504020306090a0201081501030f060e10 81
    0x2d042c8c40c0c140e0284400602584490b400d1003e100e00602580c001101c2c0d82c5c4221848100d522010300c20284184962401c940102146d4104030341d0f5240c034102000e005412110f2030700c00607038020344815007043d00501d0041c3c9075030710980e20344141d90542414400e02d119070038071045407055010080040c5c512943c01d03900f840c0da99165880c501e0140100c003e0100390800d006001c100f920005d0403144800c0108000a00d4603500701144c101c91a908040c2c54441d1583c00034000d10327400c0d00031000207010711b10040d80f40403040503d0700c3d00d804003030200821085c3c81c09800942c1c001d400f02d2a65a80201e2000595a50768843c446400b01201d4864844201d06200c0003d0181e40902e50581c0f000b50020782c222681d13140e040b40340300316124142007140d001641850204894000e4410b40461000b40000003400782464010140b606000420365501503100010140041c0d82c040c6425820042e0000d2516000e0300007401a405046072a580038021460510009000150840c20717501421018010184890f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 326757455 1250 326756205 326756233
    0x212060a050306040203031b100c020109031409010c0f1a07080709050d0c0308160c06020307030327080304030225150f050307051b070f0501170402030a020906210609 73
    0x3c0000c40e40070b5490f030424005a41c40c01e80714030705080701121000030784a804075002c607404102c919a400490050307540d880703801300b050342088141c400e628800b14242e044c00340d0703180001c020410541c00104001451440d40c0100140c0f0300c14a10208081c0f4500001c41c9055600180045001c0712030100184c2a07140c000f0b9642031889480f1180364112104040a50450300c81001c1c0381d111a4103104c81c0040d1031242d034089101681424050700240d405560f9454890a004083d55610601003607191000c2e420f416403400050703460f1401c1a0f009161a450340d0303071400c040e03050000302207070200b1038020000f0b202e5040b410040075a007a56207002400e14106018201100c0d83c0c82c084c1d034501c010413010400724802c6409036000c0c1c0105103030403080f114081c00c0c00303841d5403e180d20b99104100179004c4101c141300e40c0da00080c2e81c5a180308005d14504151810350000ad85d035071084c80e40a4002d0340d254000c40d13040e407100e10440200c0c01c001381b440b0340e0044194412640d0792100b240e61411501890a041c0988 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 326758705 1250 326757455 326757463
    0x30e070f03020f04051305070320120304030b091203040501050709060f0c0b36010e030f0d0914030c061f1413140702060403090e041a18010212060a0503 67
    0x15036005001d0028185943e01444010080038100f00c28903180e21072143c000603c1001580b0280d4032921902040c2044801103266510004031114807528540800d01011080082644c0889030002407000040d10307520721403803c0c01c40c4041c100240c1c10380081044240801504018051201650385500c142d030b03550b50488004420b500c1d90800038014072400008200c1e80079070070b030b007000004c0c484d052441000b0b10303800d0b030407500c200903829210810700d03c0d401072040c01c0c8075802c11f4030340c440003071480c05900e00e04408480c4604074032481c43e02d0750341c42580203002031a50350224180408080700e90f00c03078440e0310007641c1e61400c031680000305110003240207000e4200340000084940c080c0842c420005c81e44c0c20032070318442c03100301d110500e0380c1c0700d681010f020550b168081c09404250050950b504244c203000384040c0f0550021400c200c880c80a0000285d40c44c0c211849010f5220321b04101a11488d20307880c010200010070a913030350b00104030004480031040001d80144030884079854203e50700c0d03041c0b5407a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 326759955 1250 326758705 326758709
    0x1140306130504110303160507050303031303030c021218041a0a0308030408130f0612022104150e030901180303080c16021011240a0f0e0607030e070f 66
    0xc004951803080220881d045180c0242c410140f18140048140219207160041000107c12582002400e030074400b0602c1280041c000135000355182d4503002c648518054420b140007804c00d6580c07103559148038420b01040c50350b00b41c1480302e240e48c0c159a100041200b44800c508a20aa01d80302c05a46140f40f407440280c1c01c1c0c5000780041c06400d2858070340000e507400042c070030fa40b0084200031200c25040d510f24510050000808402c00060521100510031180b503002414110302c1007000c001060041c1c110305540800c200003e421643d560307d440f14030048805030309003260b400c0051108500c0301c007001800701c0520a80c2c40c4550701c0a144140c18905405120181c0460400c1c404284081c40c070900070800d60301070f550b0000164090303602060440e202036606a000440b041d500b804e03100420700000d0034491003400708500c021420007180240c40c3c00a840ba4140a0b592104141c0800141d0002c07440d205091047e51201e181140010340030b000c40428185c128007469801046d0306010183c2102 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 326761205 1250 326759955 326759959
    0x3110f0703120c051e0a1202030705030717070b010e01080f030909060409031704060b040b060306091801060305070f14090906130804180b030f0c01210209030304060e01140306 77
    0x4902100c030344207403000e0f040c0b404291603a0240b0b81100070600340798003c41000411103001040d02c48154245282c05082124941c1c003150410040240800d0002090315100c6800c040710308035508070078200316601d203c2e0301383c010702103201000006181908080014100c440c9081074650500c40d02a003107850b84141142c8503400101c01d40401c007507090650111000070310030b060240e2400c0a1201801e820341381150120765131902c40703409031418200343c010070101000641c8e003603045041000004104110080003452410954102c00c00051001d4102030010b41e044001c0c0d60001791190781000708030035240114415945804030400e65070070710801e030034801c1c1c00240140ca0240c95054031462800c2c201d59042d1590181800b02140e1500314035224600d2004045001501c112580c0030703d070410705001e409000c039800803010050166000499500385580701c6a0090601e422210000001d00410710b01ca500343c030009c034010079119000821200b44ea00309072100c04445030300c040807100510045681503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 326762455 1250 326761205 326761223
    0x40b0411041b0207150e01361401180503100f020f0a03060f120c06030504020411040b0306040e0c010c031107090c050d050a060605090607060b1c0c150519110a03110f0703 75
    0x1401c01201c60002c10911030201641e6503414421411a80b40c1d00d10b542100c2c8107270750742400c042c09568208084a07610440d980e00d41100d54a0600060303140e541945401090640790116641480000e9045987c6560081e050603124031109400900804050040e0059489940e0300410703002003850002440381e1b4400e20821104d0f0500f0011005801c000c0c0c812600507454078036000f0030761954406440074125101c1010f07201e00d030402c100820341c3d5042d00d802c80c154000c410a018241d901c008512111605401d040009600714804c040c5406410380c08140d01c245080e9004401503403280052122a031084018015602c0d00034202044403018400c00c170200b0810071001400d418a44042c00000340600c400040300203209020034542c4005014204180b1000e46c1008100b2141443c42c0b0042d0001050142d442203462101611620503605a48640440b01d160208014812550442c17075a06079010340b0021003440c600546494052074180140c3d01505400030300f480400030300c2030103c1e50030030002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 326763705 1250 326762455 326762477
    0x181c05060403141207050d0507030908040504020708040b04240e030c28081f1a0d02030a050a120e0108040c06261006080708040b0411041b0207150e01 66
    0x95500007049002e03070b000614180a1032074131820f14000284281516220155102c642620a0b011a40001c204200340741c6441c0b900004615820295015a10180ca0059484455040c1040c0d503000d90f178000108041e0000d0003007880380b00b00ea00c1380000300503e000a0f00800030110162152000100d245406074030108811401d490304500702c01102194940c2c40e60300c0d07032981c1902810801140c00507004e81e44082c1701103440044524542d43c5600c90450100b00c0b40d14040346074004240d00f43c254074810005d03403014806558003400401d00a951040403140d0323800c0a49014900c01c00100e42100106100c90190100c0b0350190125900c50396100d54001c1d03406003460380c10390303410103c00e140c208800d003074641310a900a0302030070841c0601c49018103040654036045d00104010b4000340044100110842888000b13040112815042a03000c039a10301407038028000f280081107030000c100d0f880d01540102d040c405401041d95400e4a41540c1484580c41400074182d80d210700b80505180090003080c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 326764955 1250 326763705 326763707
    0x207230c040c1709070501020c0102030a080c03040c08150402041512150f060b130b0f181314090609031905130806011e050108061f090506181c05060403 67
    0x3054a81074203d0406581c807000704054912540e03001c840c2c926640d80800420700442d80c04000b88800d5800074030044d49003400105004150401c00b07000b900e02d030840840402d00300040200d200002d400300d00210350340d9004401d070107a0303080010744090b4003841c0703485501c8521030403074041101521280103e4451034021966140082039080700e0b201c0155075106000a0480824016080101303249010141c0b40c0c040d03036214100340c2c00141e0203000c1c1c03940300304080031086d11004152450040312814200c2d0702d9081c00085030307548007850000c0300d03141d01c0c1c000302c10700600f14002d10030302a44080040310920b903103d401881c0e580c8907102c4580484076400150507843d41c030030307030042166000741c8800b07003481503071000c0040c034241003a00030f03210005e449071003004054600060b00c001807009190494032801e207800400c410041a540001c403006c0054542480140564100401028050441692004a625211001c10068080b60710500c0ca9101e95203802000800310001c1c02d40203006002d460311142c0d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 326766205 1250 326764955 326764961
    0xc09090b18220b010f0e060f0a0509090f10020a12050105090a200309010b03101506110114010f080f0303062107030605040302060a0b01180311010903150207230c04 72
    0x100118040402c0b034a100050200e041e002e0080c034507050480061401c009030321a00350402001140038001007a401003199503109102c4084900584090b5680e0300d4082c252420910800f086040e244142c502c03002c1c0d040705590003040110340315501c03039070750302c1074085110152842885000d40c03140d410030110f017900e030065100c0000c054094909107809c02001d0800b01c2a6003003104c0d1144c140e50744840014560038288414114091544010080304950000b840481901ca001d00410440e03010441c807c074860941c0940440100c41070038600544e500c544a011503080b50140a00ca0b00404041990108001040e6401400c0042c518059039036075a050982d645d9080d001da803a2803203440b40020116445224050042e802540030345140d14000f400d000a480f110b8110604028a96098002485100c040c00d001c2d42e03800712240c021609100b00490f030301c605a07003000d0056080009c110100190503402060010720890640051030150ba0082c01c030043c1003400b008960b0400c4403110182d240c41d0b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 326767455 1250 326766205 326766241
    0x5090d0f030603140c0103051e0103060507050c010513020a0801020414040b030c15070c050d030c060905012004031106040f03060f09171b010e0309090c0c010c09090b18 74
    0xc030700040c582d03980b40c07100d2100341240e0008a00ea07030000780c0d4034207403035901d4040c03150b10020000d080e001c001d03442d155a07528a00b0520024103003c0e61040031075000f922500c12034038690710140007809241003250a07030810100c58881244501021840010411010300130f07241202d50751351050110480303203070511001e001580340b8641e06d8001e4404401050b55a04400203450038800c14a503200d5510b45005015100c40341c0080c0d205001c22141140000d40c4014500b810650004000c1441c822914080340540041140400300b034844a0444004a0000010307104a0b8002e1510844040410301488028400d80c001c5c0509101240c00602c082022500300d04000c0320188400030b8614600d40700c1440d03405803a10b820380d0740c1d03100050708907032070343c042683c1030801d05100003c2080d0607240015a90b20300c00c00c2e803000e004d001006c0c0040c082030380381e8040d241d912032108028801d00814010050410350a8051a02c4992800303c031104a0b04090b0b0003041c616802005461541d121980c024a40384402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 326768705 1250 326767455 326767457
    0x105180a060e0f01080c0406150521150f0406060203121b0409020a08070201060609150306030213060e0708040c0317160302010501091a0307030303360b060405090d0f 73
    0xc0c07a00018410311904241e441442600480d0b8a5035042c16620341c1492891110700b449142400003e00c07080c0140480c0710f0b158150343c108169664401884111940003985030109824480410418400704065043e01061811100d0860340c17084803003040b089804d540903200c0141c3c410f210a190380012901c24a410000310019040c014884000200295000b9082001a41d4000c94801c010310780140d56503401403458002400214201500240b030015030703124081c4901c40710342c00ba41c00c09020354088006141c000c2d2040e102d180286604401030300f068441c810644061200040856105010741030186600c140502c036040d00d5030300d45944240c1440d110a09050003001042c0342210482d420000f403d120ba000440c0540c502040310046032000c55a40c5080804040540d480342c4d0081040c00940341c3c1818001007690700001d44400c40c01003040c20b0351180c0741c503120405090488207641da04052182c1c003540300b45d660740414407041d40c806403128400b40d071201806040842c05240101c00030169 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 326769955 1250 326768705 326768711
    0x5010909090f02040908120106090e18061b0708031e06180c0a03140a06030c0501030e0307061a06070506010312170424151a0f03011203030b090f15090105180a 70
    0x587c80c01c50004070030a0b4044404a1544079040026070000d1000d941e02000741e01400d95040c014011032901c03a04002c0c9601c482440c41d040c0b030301a801100058030885508a1842926890b00981d6404142068000180b810101400042141c580f100b410b07400401140c94101c0262180c095200310b40d04645030100500d0b031165a0341242494071018140b060324405404500d09155091000d4000d9054100c0c50416040502042c075114000088401485c0e10502c000b42c52840111a00c10007041c07004000e900c01c400013840002d01c4030014021b81038038040d0b4080142840380003003c1d1400084518240303820702540c0d000401060610162200c06180e041d8007042015110440c5000c840c4c04503407030340754821421400d020281070601c4180c02070250b040054a001048038940c40d0900051103806440c44a14401b0001c01d4401e4004140c0c1d000c02600e2011039050501c00b0000044040f0f07138800c2d840000309802c01c407030f150021026048035409000b400c81204810049220100000c1c030783c041c0c41e03403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 326771205 1250 326769955 326769967
    0x60b070f08030a020d020c012429090a03051b04180f02010905060a05040608060603091e0709020a030b041515110f0307050105010302130614010309050c0d03050405010909090f02040908 81
    0x145e203000520105090368000501c0180f5400c80120300c2001001444044501e00381c107100d0212218a05a9004030420b5240452959074250b00340c10b00c60000419040b02c81030000000700b09002413450780030610310302e034032120b00464004d0208070b8410b004008110003582e01d4440100f100320034846400c0c1e0061400c2401c068642c03001c12201e0384624412400a20001010013945512550b4641c000d001100d4851440c20310442c0300760b0321510a103013401c802802000c0c4072064001000514010080d441c0d003591134a4188802030006d01008150030b004900380108083c00141101d1403038141c80d0b2440c130010001b9a40c1e44c5c11074404080185403407481c0310303202110745d00072400c00c05000d0b110701c150004501d0350b0462043c0702c810b1481e06142ca460703a06207503060051503060074840280741c80038a0001000d2500e801d05034a172900e01c0b4a01a00300058160203014158080001c00640d035081c1c0320840c84aa0314014141203841f038000151508030103044460052030a50050041280140700c0941000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 326772455 1250 326771205 326771227
    0x31c030905070b090a050a1a09011803030201021921020a0c06021209010b03030304050d08070c060e01050f1b04052403010602010c08060108090a03140409140406060b070f08030a02 79
    0x255a080b11400380d00c085201d4256107000071131074000e0401501d40456207890902c0103400b200172480007241c08c0501285054041c0d204d030b0650041c0e10140f900c111011a078a00703000c2d000b0341c028803101079030001002d02441740c1802021800e1800d80061a101c9490b007980c03021301c009410135043c00041000035404040800d60600103840310f040303481c10301413060506014050840300046250b074000e41043c0304000219001282c0304000034070340e0804114580c1d80940440d0500c2c01058001c0c015440d00e4650f1040e03001c15403080d80700d0300900c84010001e0721410844e600300700001d080f020313080004204c18401d074108401490044200111810845110582c07800c0264109800c030742c00603956000042c04c5c46130300c00441070b0442000c2c2402d1040d420b00c02441030f02c60501b0440a824840c8800140f0052160401110010f105544081018003144401d51072480001d540039944141070604c00f2503803c091500f00d56455034841442d1b400320b0070560b51101c150300024445002c6c00c5d803d118100300c10b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 326773705 1250 326772455 326772463
    0xf010305090316050708060609100311011707020a0209280b0303070606030b15150f030601020a0c1d06181b09090a02042c01090b030109021005091e031c030905 70
    0x40c510840c00f40142c1401e00486ca0701d040c1004145510136400d0303030140030710407006480d03c400340c0e9000740380000080d0b1850300503517105c4044002c24030980c155000f00b12407540e0201e040900148200c400307005a07120070074900d45803078507142514070710368a92f2000e03034149050b0b0384035400c6041d018040c0c03810b000c41a201c81003140c03406c0c0c1c0705540390726007802001540314540e0500d2000d0a82103030088800d05511060341924052110b07d070152040000100c1d000341e0007082446200b0b64010340040d01c0640700d9054280c0e003c0c60780722070810319616001040042c075011500103c40e444415440d84941e5495900069003034031100754151014080040f00d8413500e4680149119862900c1c01503965490107a40071050549064410341203030404496040a122a071189411a804142c1c080340d9a01d102d00068010809800001c1d03009413502034140c811900034015042d8542e044851286c144541950302442c031040da4000ca40c1900302c0d444030b0903146401d81c0041c000ea109403900091010383c0e582c602d880c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 326774955 1250 326773705 326773747
    0x182d0609010c080c031003060c0c0b0a020a09090203060618150403030f09171b040b0406030605040308220807080c031204050f0c030714150d0c020601090b0f0103050903 74
    0x140d42d4440c0d51040b5140d402804940d00044021400b40ca140340c044c0000c1400311007030000504072621215001c0c2140c1c400c04c104041190004c0b0340305814208071403484029071250384c0140108a07964070010b0751010074401c0d20310425011f45410b01c0d0444582000c1d400c10111541c056201442c06400102d0004600c040c0003e10301c41c0c2c072151a665200100904540c007540c0c084d4200105421074100c2e07500d000316194148002c24000794880980800004028240b40002c1e5074000f880c5c400000148500740d007000b8000c50007a04d80704070540f01c46c01d1032400e8560039858101166094148500014040002850a81d0150b04600e007050601c070320711421360340701a84d01d80e18400c0342030510052010a1100011800003900140500100d1401090b103541c0a0f214a045680c2d2030044941203071285c84020200f001c42d5541d451342c1d0340032000e400c0010711100100354014030030440041341c054030510805030035140c01400303141041d8802004402502d0010b240b42c207140414000c0400c2d1650203210810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 326776205 1250 326774955 326774971
    0x5070f03090305102a021f0b03240705030606180d02040504031d03030a1b050111040308070b060f01050304021011070b04240818010b031f05182d06 65
    0x41c91520304181c00740408001600d03103203e4030140c05d41110305400081c141d0f038a010f260024942440c0c48507041e8010320740c6080c81c58041c05242d42400f81d040f501501504507a0040c99412001d13200c03e0800c4800340400c590320354102e10708100962102c4000085c52049100060059240341e07910f41c0414103448003518103c01060751040e1100000810b03203072407410690240c00079414820008001405029121140303144411041c40d21000e201d03003900028024001000e02c1c1c0c0e0348659920b4040c14603480031000b91000c3c120040460710718604899410718a0350143d480030304684958003040348d8000782c0c0000e6002e0140c816000000590280902001001ea401d02681c6a6141c041c24102110040d40c00519201c0d22220340d421035600a203550f50400190902c0d80d03050900984001c1c0182522000c15070b051183e101c2503241ea684c450400d82c0c0c0d01e10042e60034041750315100341200e401c4d0450582498944c214150b070840c41420080303601c42c40038088048000200300d035850b8a04003002610030314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 326777455 1250 326776205 326776211
    0x70f0f06051f06030b010504150e090702031201061d090103030f0e010c050d05072a09110a020604022202160b010f060f082517070504030305070f0309030510 69
    0x150900000344140e0750710140d4a050301c4445000c500400c50509603d0040c80c00707169603200158600d0b40f10750141d9001e0300d0300162154104070702e00070140003216052181842910302c2c600080f02d561021081d01d042c0c103090f444146c556402d041c0b0944900c0281056100b55800c038044030309290b541d0300341c0203000711f0103078403403002c59000703688001d190234469a0f965060013400d01051002620010b041c1c1d20555103440c0440c1c40b01b0003803030f03c4409044600c155516200035004045d9940f15030300038150442d545000200711103241c0c218a2211402009055005600200009005428030312816181e50300100429201821882c5011049070041d00208800c50031884441d0700704072103d80c00301d002d00b4002d213034018250301d000001060010900198001c008060012803480700140d41403401545040401d405115540136000b4500300ba134107102d84405105002044085000e007085030196a0169039061a129807621181c9103038408403030032420094030050001c007040082c843c0f0b0b941c4000c455008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 326778705 1250 326777455 326777483
    0x8180121050f07030e030904050a0b1032030f0405030c0f01150914130812090c040f05090c0f0d05030a0903200d030c0c0510050406080f0108070509040503070f 70
    0x1001440003d15440c1414070302070785507040010000c10b41e1a00710044a01103802d60f1100b0104000d00789201035250000024503018045681214011507078003c4000103c4407010100265051003401c030000342c201c400104007188403040c07034040303103a8014000c20480b0701d041c803100c920300e103099030440490030965500ca170041d400740d20960b40c080040c00d894106108104e10440f03041030070280a090700c0301341044a100702041082a000345c4001180101943c4114505400080c2d1a00d920310b60a6208a14000300000045502d00c0340c0c50140121400030007240440c041800326403100c80302e070554800800d41d41314001500030801015821140d56510b54140d1031840e00f03002c8011790001211000001407285085034403401d18403003005401d442c0441c21030459041004444d10340b0380207680c000582c01951109650803030001e20031034405613038001c0c40d540c2d050004810810280602c50503134024110820503480d0031600c440e080790040c01943c2c0741004550340c001c036141010008441c1801e0728145 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 326779955 1250 326778705 326778721
    0x605040501140102280807060203010509090d020d050a09080601090e0715120209222408030f07050f07180c021b04020309100504060f11070818012105 66
    0x40d14010401420722444201040c40040d41307410f6882210800c00f40c01070000084419000450700039039412141c0240d1f42d0340141020400795000740a52030240c0362031004200000d40c0020f0b07007581003140703501400e0301550108048901e90720030300c03100041019011000c282c400089c0130300c41c028200d40e1000901500213101c802d0510320b2a1344240000a004a0b40e0400b054005490b03980803207803054016564955030002646854400c51103c41041c20700c0c0601c140103030b183d40b1075058001d1000c94152210001d41240e004440740713000c1d1071a00d4006021440c00250840042c11165109005580045241c0c2c1c4200d450108580d104aa4402c5095040f860003d0148111440061f8510107050ba8011780740340e10390a0903c01c511a13004680c00000144c80c0d9009000d072079203000d0b0084041c412820b15041101c0039000c200d081203a0b50b072901030804200440f5030201c90180e40d02014103400c0030302c07005c0490302c043d170200c49042c1407001840b0b0004480304007641d00c6046800c240d40019803070508a007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 326781205 1250 326779955 326779961
    0x40608060106021504150207020103020f0703030c030e07030312021303140606190e04021e030114010305010b0d020d0b0a1508150106020c010c02061c11030f0a09030c030806190603060504 82
    0x1958130014801e000034000880c50b90b4040c80c107401c0c039100700541d031083d044c80124020702c110040124481c40200d0003a00f0181c0c50740150030750040da554180b01c2d03a000c805000341c0324405480005d0106156540142c05001d075038000d0443d4044064000710001e40d203884460060136001540303680384e00400d04210791807130000e1100e1140090060115020b6080c040c1e42c032201c04e4040e00281c4120304034038000b10710416a00c1400b142d040c028009101c040416000c0c1a6150002e0000b200d080d4201200000702d810000702d03403101c4c26001001c0d800301100d1038075072426030003020300150202c607214002d1018680c81d40fa0980000c0c00b0b070310024000104001c01c02290b10f141a0050000c5400610450140340ea0014248006c0c0b0380441d0000e5440101944402c81420700d845404840e6050403074840d284040180958814103000e03101052540c1d500000300304840702e01d140180031640100ca01004070788580c42095000304007405440d290503a030505c2110b202000d41c40880001c0d102d540510441c00c00380 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 326782455 1250 326781205 326781223
    0x80408120d0e0a120c0501240303110a030503011a1e071b0506032403160501091a0d0b0103140a050108011d0304141504030c0e060f0f0103021804060806010602 70
    0x103002c3c0a212400b40d69020003185024000d80070401c2c00a0fa80d014080d00f07500603a0517441940f0106050040b29990640c51843c41c4801d070b02003000f1640c6689800c0c2d002c94150301e1a6030642e100d5140d80c0c00c140d60300250240d082d0b1805014441840055a01d109500d43e000030001154051501d0350010310b0096604001c1e94001d0810340c05800042015442d91019681c00c00c0744055802444403640002140c000225550b080c1d0610580c859100981e0b0320032241000d446d020b998030202152110000e40c08415200c030020203440c0d040018501c0c0e003038150b0103c0d90782c060500d80032800103140000009120b1040e034010f00d0361030b0340e4001001001400d2140304012403021640c001c03281a00c12031152030340214811a55400e00d41c207003541e440d03980d07541903a40300b41c001c04103252111f84a080c40c0d15818154061002c5110030500420304900d080f6001d030014240040c074034026001c44a004401a4000030242c00c6400140b00540b070b2140c0e0b840c0100307005420312a000b800250315101000f45400a90 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 326783705 1250 326782455 326782481
    0x210304150b0a030303020a2a02090f090c06090f06070b0907091a0f0114040305010c030f060b0d09110414041106030c030f04031e08070207090c051204080408120d 71
    0x101e2080300168484659481c2181e415050040e200c40b03c0c20b4064503501c4041d100360210458070517028007440750400c2d8966009009031450000e5588011029440d500c2c1a1403d030156400f81080c2002c924280380107040b411406403050404103103070300104209402c0508100e64140403401000740760801008110014030403e0020310481401c45881c4600f00364400071980691001c0c034200b213099000c1e441d00905554841e01c030990303903035407030411303a0007130000c85000c100103800d1142880c00032505003d9401600e541a181c68074158540950000134565040225221441c110028145603220f05c11204100030741d03860040503142600d00605144040f00046114860900c1400290100c0100743d82c0c5c0706080c9040034455072568102a46c0006c840c41400c00719850850351036040c290f108070003a0007032403a07800310740365141c544581c842550321031080340f000150144590300c00351000300f410f16001405061151300d40340e26a2070950400b202c00710316a0700707004001841c2e54880b44500c0785004141d02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 326784955 1250 326783705 326783711
    0x12161106070c030806040b030607021605010806011e11160e0f04081b03041a21010e160504050301092a051011010b312c21030415 57
    0x84203001034020b50781228090100300f02c50b0700248642d1078907803000c0f10091008040b20880e15029030001d5503501700031808000385805406c00610703540200e44007405000d05071100b82d041ca12441c202d803e801c802c641d500e0100f1100003400c80c4440030500c86500c2014004e294024940c1c2070030101502c0890203030501e018607145c0070030080880c5101d030584000c2760b035a01c0f1040c000107904101c02c0c95400785401103514114007802c0000e404200200a02d003410b002d010418224201c01c12005005c80248109008200030a00080092240d5203910802e180b031420400e0901e174032070011a00712011041c0131108484032003000e1034815800c04c1124040946141e09020759801e01010800c3c890f103070882c4c0400d02072404501215800c0a4001801c1c1c1030300900304103031150171100390440885072078004415040001d58620380324101ca015214008050301040a07141012100d441c03d111180b240800c454002c8039111030350400c03181c1010104a50341d007a49a2282490306003055202c9074002e08000040c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 326786205 1250 326784955 326784961
    0xa0b04090c06200d0c08040f0e01090c08040203060c0c01090c08060709050d0807020f0a23040c110601031403040e01030809090a230a15080f0d03020717030c12161106 73
    0x14001044e0321003101c9898251100c0d4203514012565004903001410b5001d54500c01103004030114803414101c0b040d50f84184445200c45a060301c0005040d640070350103801c4980003844882031100200031182c030720340001840848940304da6600012a404c428425002003051002d240d5000114102800301240e100c21143d541e540c8030f107114416688028010f080c010680b500950b12801d00400500901181c04031140030780181740c42912a82d002680f01d02c3c40c0c141d02d002810712030144a4201d400c240024143ca0742107031540140c1052101c00060188002c10003c582151482c050702d000311302c00d21a490321350902e04104680107c00800c075402035032404c8070030180315402070f8145000b0a10780486120300c1d10303001c1004001c2d001154282641c415480c41c00a5070042c0004c0340002c080f50042030f1401000540011270987c032035810094001c2c084d101001c0150f018500c000c54100140841e8586048282400c004041c10101c80380009011200c81d48450560482c4c410760040900ca0041c0440c4c0c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 326787455 1250 326786205 326786267
    0x10206010e0c12040f0b0f0601090e0402130e060406050606070206030c0d06030204111312021f0e030613050d080424020403080c070303090b04060e0103050a0b04090c06 74
    0x4014070a24100e240003401040c000030108085882d00c003000e80b0203000620b0a41020b04034200c1c00e81084407414041c5001410020084a5090044405958000035107140c0652401280700180081e40d0101041c03242d0a071201d850f200714030750b03907500314041c0076685071508100303086610003480140a440100801401030f1783d510100e03540454000302190311240c40e800d106004181c3c6410084d001072404a0385600c803280c40001c0e2038283c560745500407400f5140c4103424020020920001c0d0060f0000c104020840d8030a4840c0c0d0444209203004000300b8406000246000000d4440c02c010481c02c01c3e014041c4801803108040f0701403541460744203420300c0d0703540e05454900f080154a600030b1600386030340784480d280c0486008641000b88070351100d004502d0240c44404a103c12004900c0c200c100060704180c42c03042e5021a612070315442503900114005502500d00140147d01c200d950b8003501480f41e84600c1200300c0a405054441100c3d42089800380c003111280c0c007110090740c4518501b02c00e072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 326788705 1250 326787455 326787463
    0x309031603020f1005150411070b06011412040b1302031b030309061201050406080703030f0302161e03030e03040e010b090d0b070e040f020901080a0e0715030203040606050f0102 78
    0x1240c08500306480c0e51036003070403402c08148608510b1140181000030400709584d400c0140900c40b0b51040854411555040004491200e104002250402c5c002800070135a81c46415500c2101810102413803000d40c002c60a00d5441000e041d112813411009100610000c0d2021580c40101034094a445403415000650760740d1600000441000c01180850220749003072060314055140901400d48840c4212420044064240503c40c007492901000080740c4500050035030840e50140c6030036207a40c000b010100c0295010854080304040842e1402c0d0024207611801d091103840c1c0c04006070003503020710f0018292400c500140c41c4d02d0b4010320040c008a80e840c0d150504403200c2c608a16510403140010800d20580031001400000060003082480c4d0340214400f040c24000f241d04000d0b081103410810124014001c000380011109000a0600b016550003000c000981780201c69081da5a017280d2019006600380c80f80000e90044240410813801e409418040c00d41101c1a603002c9011000003983d27 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 326789955 1250 326788705 326788717
    0xe010b03061003061a0904150b03160207051201020711010306270f06240c210c051b040506030a080703080c090406120b090c03030f09011b03110f03030903 68
    0x20581d0114020360945003e648988020640c0c540c2e900d0081c60a03075415809504525000c500880c02e044010419a00d0710201106441d4105102030540d15405030104401d01c4401e038002c19482004d074082103a588404480039204049000580d84851525002c508000125000d60500d8204602401401481c1c40d1345030240c107000c1c40c0c035800c044075000002c001c0e0140050314801540b83c50000304030417144c09950800e12481842d50700d40b908030044211114152410080c200742804080c41c0c141c0c03000340c1580207410701c9901d401e4901e5109502e5030343c1840d8843c40e0802500c960068440841c0c10203006807035000004030081c101c4a4641c3d22403000901c1502c03401402c20407a00b0010310703045800c2e4150f42c40759101a104002e0261608482c14285100031810f658104a040019011100015030204c4102000e030255041010107048150b49400050569040c000d51017408403000035101443c090250180d0f45000b0190803c0200508001e0101d04400c51034000b0020064850000011910 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 326791205 1250 326789955 326789959
    0x18020a05012106030825030905091801060b030916030f02040504030c0b01060c0b0a0506010f120f050c1b12030f1312030c200606060307180306090303060e010b0306 72
    0xc120b10a41e4071040e003082520301003a0340528180001c0706000302140503001ea55031241c0c8601001c41c100420420880400d600100001c29121050205040072000b282d003140311003800c50303800b4410000716800d48601da004050440c03008410041481020441c0300c41480c80b441c0500044c03030a58031100300c14107140c0406806103803a070011604051142200101c200c1d0440110340c003950311094001d14900e402d10084da4070b64400e90100d0020703c0c103403158a00600c0140c441c45a005800380080e5040ca03c100149100302c0d68801e0840007800700d90040620030010141810399652030a49810100404c0180300d00c601d42c800c12241070400d00b1001100c1c0c000a07103007580442607640745105c0548030041c4a0042001c821140300c8141c140d050380110110300001e844401041c0410181e2a1003e29448050380b1a036002401150325070400c7c500440d0880d000b8504403120b811140058107488020760b00440309103540b040300d078003031583c180714620181410410310500c652400b207002c5800d00000d80301e03074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 326792455 1250 326791205 326791217
    0x9080c1c180b090a081e011d0a1113090606050a0e04030f050d200304020f0f0a0e190606020f01050f0606030103140f10020c0c090f0f040c0f0b04060318020a0501 71
    0x3c400c590301d040c20080109203960454114060b800c40d0f8600c01903100e0f54515442d824040c40e1b000214000a0708841d0020b054010328400f09241c0300c55468100700030869030459503800d1203004000c91402500000c6004005c04101c0d58541414002d9460f420f40c010401c561050081c4400254170444280c6c4901c4240340c03490701c545280211000070b0628030400700d0b074005c0d550141400000020041d5110764000c940c82c11103042000180103013500708440280d40080d20b22018030000301c040410700e030401c21000142401001340580700f01154502d410084c0036030b0120a0080d8407410074002c103a444100d560080620341050300c00b040860006001c001e2105074480c0520940e25010486040d00306095800c880004100c0300b401c800a5100901800440c019500c51001c0c40c20013101045c0a0380342110611405e591711601c13082c5144019104170f600303402c0c05e5800525044d0745a9140003412904120319603440c54150060110b40700c805000d0241a441a0300d000541d031103280400403540f00782408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 326793705 1250 326792455 326792467
    0xc03021c0213050723041e050418120c030c0203030a09080d09120305160b2a12010501030b0607080408010f0c020a020f130605090c04030501060605042709080c1c180b 73
    0x8051640115080720a131349580e40300c3c1c0b0500d249007c800b8411298161801c104204440460415080400700050026858008078505403440317040e00d004464000d1506500c1420540c0c00a41542e00090140000900b004014000d0070030038000510105001d0910704085441d0030070740c1c03110b0030f030050010f82401070102d0560301041103c41c80c258580e91225846601d840c11070a03200b0b050003070a002c2c0310000784c00c1c040c5401081c80901103522100910b00800002ea19010044003d880000492a0091001d01c503140005a051010780f02502c500307000410012034254980080f00c1034180382408650251004401588444074030300b100360000e0710840c0c202c00e100001103000c3c0100384d000c1c0350006003002c200105442c00201800c1500d124100174000155a203104480e24051805001d600c3c0407844550b4110811a10b03130741000c40020140403920f0b40b419101c21403550004016103000e500142c28020012841e0198403000100c181080b54004040d44291070b0f6020150180c0050380c0e5001402c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 326794955 1250 326793705 326793767
    0x50c041e05070206071e0e04050c090618091302010509040e0f0a0f0218010b0d20030a150e01120f0f0b04150e01061409040c03021c02130507 62
    0x2140c80000c03245414005400d00d200002c0da0b404045540b60001804a0340c403c040500d9001c110030381106e01c0d941c003160100c8281c1004010720000d004169440c10070002e03260706131108000350407200108110444030024510511400560080c5610515036440e05002c00607a0000160345038030700161000181c1d081ca4030034040ca400315030001210716101c3c800c3e200c401c2240f0450644002ca00c241c0b1003a28104035032910030f0300c0a8080c0070303001d40444188182052644540c2c060300400c400304028080000350310080310056802520307034001060b1602a10303ca04810445610000c104a5000c443c556143c014031120301450780c03000600405202000c5000c3c000c840c03041c00b5010b90000d80941140c00e192800d203a8009110410a020358101404140c4940040c4502803c54034015560006081508104141104020400c9030b18003001e10000c005616904a81c0300e2505040d08595039141c000d004100c01042e0b00c407007941d0164108010800c2e1300741e0004920406803017540d900c240e01d2803c200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 326796205 1250 326794955 326794991
    0x604120c08010614040b060a0207060c0c150807030c08040503270303030a05070225151101060611010e0c0d02040c110d05030609090d091502030c070b030901060b07050c04 75
    0xc4850070035803c084001c25101000700d1501e46a44040b01c00f0021614564280b0405005500c0020050b80081e07604201450203000c5c031a00390782c0308e09034010100b034441d17125428190440b54020b00046007501040301061305441498201c01f1365013000c0c066498107558060341c0740b240b101b42e005061200a5003541034104002401000c0c1001802e9944038503110007000014201103a03850014420382d1800d13034120404c3c60141c282c0d03200e01c42d900208541407034909074000c030207166450304000c0c0b200c10840c00d0314028410b0101620981d503030b155070f82540d810f00da402d4130403400a003540c030b801c20884100540d443c90042d0898907815500440d84500c9100240d03200c07c400c8091155038000c0c0c030703426039040c0d074460700940c41034000321100190741d1915050703540d84c0e001008214020600a40c41400311100c001c1182c2104019841124a441015240182843d03520740c011841d080000c030a0002000b028007400029058031034080e4142503044d1101d99407403400300d100c40e0142e07548110603090b10710072132 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 326797455 1250 326796205 326796209
    0x1060e01030b030f240103030203250609030207050103110406092c07050c06010e0f0a2004031b050f010f120f1b0306050418030e0604120b071803020604120c 69
    0x8003a0782070102c04169650b21000845031035204c5c0701c007160107103c0a200718103009040e2905a4000d5041c004110b45040400c0794030410303030380c0f44031a040b5800300007070750b5008000c1c00500c00d41c040c02000340b800d4009429501c0d0f4004d20803600d4020700082c0100355000219000301c2d50030350600c41030304512045101e448030b1103148440400c40020200110550420024920f0303400039412903095a81c1d0300c01002c8181020348a203a0804081760204106c0d4207076410540c807504070000300c0301548103c1102ca150350b903c0b07a401242c01c06810920766116050500e4048000e1400b52084207070034607451300003401c491313a1404034014085c0580170011044030315800056803207004e00007001b22007154581d03a01d2110075211490006820701002240383d040c1405084440040840f0840c1105540c3c1d9050350142c2800400c55007005081c00000394280b00d448030f084485018499503c602d0410b280c00604800041c600024481656001000141c03a4202140c044503407031150304504035110315014403040340603 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 326798561 1106 326797455 326797459
    0x801080f0a1509151b031505060a0804080f0406030b12010b01141e18121507110c040c050306040b01090e0609060117011e08011401060e01030b 63
    0x40d4000d0343c06140f003500401c10301040c2c0b550690481c2c0b6409020080b0406290305090469054800c808041002c0c1c042c16507000e007044080b9446202e00300d4030344100030714900007600b03000038241940d080d921660400355440e41e81d4139004010700000354156104d0301301090801d0f090201403054000c0910181c481e041c2910140f07280d030350b45810400d506400e0041949100d1049104100100200d580c0d903d50119003014800070b014511000c081e0340d00d003650100070305409402c800b0319416031103010352410542030034032030100c3d07424014503d040903009070424800c0078020340c11401075442240181c408200015003400115903d030814821210034880144c085070160505900c03039030b44110103051454030000110680f5060341026030014000c0d940e8114584804600c00c141e4800a181c1c040c020300142800c90105180c854041c0319070702c00d1211140004003540d000fa0041401b407580 = true := by decide +kernel

theorem cover : BRFrame.Cov 326618705 326798561 := by
  have h0 := BRFrame.cov_init 326618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 326618705 ≤ n) (h2 : n < 326798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
