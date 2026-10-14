-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1997
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:24:54.048391+00:00
-- url     : https://prove2.me/submissions/493f7470-5997-4569-9b62-18d7205bfd4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 358992805 ≤ n < 359172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 358994055 1250 358992805 358992817
    0xb1804110d02030a0c05090109020c060f040c03080703020a02011403060f0d21080420030706120b210c120706080a020903010e0703030207080a031205040f020424050306040305030c 79
    0x703007400c0500364160700091030001504002c8400ca8030034901001942401060700f400751840d0201541420380c91114195118001483c60300403115400118041c0200010104040d40e00070b40c105075a25071600380079541d07000c60741d000c0b4002040f015a420020054000b564061600240840a440d81e10403c000050791040800e44648011080b40701c10410000c400146800c3c25885814080c81c2a081041100c60078840c440e01d0310320260202d4030142d5012070b114090340c9030390601d036007030b04420b1030040b004011441000d07800400c82c200318828004104071050445501310115910280c608050245020860003e000b8650000030240b00942c014075056a0084414030010304220640001038203407000e41d1012074054011103000e1007415818400c80016041c00c00c02070410301d542c0da074000d107240009008143c08a9a44020404020442c2041601c9940080c014003410307071400e0140c041e03031141040808414019550020b110704010440c00e1103140c05480d4103003560303600c80b1030a1082d8840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 358995305 1250 358994055 358994059
    0xa14010b030a0b04020301060c02030c0405040302070e130c0f0513140610030b091806160206070302091309081b0105093301242c0103020d090602070201030b180411 72
    0x1c3c403152210707466a101131030003030505680d00c485101280c0140740c202165448501d001c6c2d4102810003010071b40002d200002c8a000721144142075641e801450198079070044014407601c044c1100146400680340c4000980d101140c1c0e4510100c42180d2400489038007038180c60f004407010703000070000d01e0100142c1c0c6810000f4100410004605000a40f07464070484e10021603459100002000f200204a4558000f00780043d1007088042440c010b5580c902c0203084100701500010503064503100c05581041107480184140840311151401c60b045070000071001c190044050300642030103005000d114010149078001d80582080700310080d0f10f804090740080c81d4490001c50351010181e03a0300d80e580c020b00d03040e604154134884003031091551080c049869400c210013071110484401c07640710541500a4070080c420380c2e401e0320000580c040c0c000c680d03501c03500318a8020344909006994004203c024801d0380c0c1003090005072030411150707501d90086e114055041c80300160025001600c240601640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 358996555 1250 358995305 358995311
    0xa02030a060b0715050a0e10060e0c04062a051005070f02070302010c0b0606130b030709140f0907140c070f060804080304060f0f0e1006050111030d0209060d020f030f0a14010b030a 79
    0x241c04c005071070300c0f003052041c1c843c00b9031b560310400a40304560080d82c2c0110004288502d05450704a00400c040758000085d484ec048000e0391503841c07041035021204040e84541039501d084c205e030039400014a000c440c0311000c00d0815050701841407000c200750040d80e0f4140c46444d4900d0098540200251005241e15041300c0b00b0852240144401610b2200070b21070311a102e640c0b440e01e10001042202c1c20703400150240c6201e0b2161040750760300701e1321070030315074040d50110155500c0c070034100e582c3c1001c101008101e400000780004221004103142d400d8071074032100040040d54541045078102c0080320054500702052000c14005070451308160000d15241c080483c11200f20fa0a58041f00d0005a07149a50342c0841075817000380c0700302c0c080c410050400b42440442100302c0c00310b0540740d00c1480790310f80e003ca0b400145507440d50b86450640d80c109540c407804646644001000300e203c3d031f00503140c0c48143c21a850000f01040b42c5401641d51060401612802c2a440d044d01d60610750005841001d441d03031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 358997805 1250 358996555 358996571
    0x190b030a06111804021c09020d0b13031709070b0a02071d0f1b0f07060908040611061305030d0b010e040e07090b06071a04021203030a02030a060b0715050a 68
    0x75642c003079003550361442d802c1e0030b0369000c90b43c2001482c01c9410080034012030040c801d40503016030603c0700c1c0a815141d100701041c1d5500c0c0b44005814101c029000070240341240c81484909441040c0401c55103100e51100392884d103201c2703404842184200c840140301d03404000d06000ca040c680d0050030420aa5004039422241c81e064039481000e4248072654400d0500010018058001c0d185590411501d0b0100d4840650f854000b0035039104d0140c03400d030944d600040b508104481ea5204144580d00011280c2e11561078103001480c1c021103c3c903041d41c5205010100d02034100c03c540100310b055206000758900440b081400e0054089002903c0c184042603a8038041c1c0d844501581450700c0c81c43c405890001c1c00e06c0304150803100140e103884d0260740c040c490400094510042401035203041002a0713050b988a10008090107c8403206161038040030040c085040403940155001c2d0703190a10501c045034075001d01c10f6160046103c054481551b82000b4060a0040c1c1d101b9600600004000300b8060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 358999055 1250 358997805 358997813
    0xf020102030f19120c020c2205150a050910030b0406020f0c0703060e01020a050f07060b06070b0106022407141e031906050a170a020907020105150306190b030a 70
    0x50064060b0a42e03a101030f2110303005199101112101813000324030100f00d007030b110642c029901e5102d0002540100805014074000240039413404d003148415800520052070007c089003240c07944007403294095134030444040785a00d404070116208a444980c54251079145403a00041010013074420384a07103600b0400f1410380142d000c010050004020010304285c0e02e146010350483d10034003a60300c0140d1050140d0b000040e807000884801600350038055841f407026090070300083c140cc4031410752054001550300d003040240414181211a25000e0342c0000c4800c0142020140031a6203010b020018840080c2106001d40c5895505200161040d410103484480448240c02c005100b5000d400000c4100001141604038031201c07415050810300c021840c00d80802e2100c012401007886014282410b4003d1a070300304444001c4580041414002d407c000c0c00c0070b4000d001c03d503070296803450504c051700c200c0e003000a0a41d0107000300c0f422003040000c01c1c0d842e1100400c030142c0e016906000d0003000c00080b0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 359000305 1250 358999055 358999057
    0x5070f03020d02150c0a051b07030f1205040e0c03100302093904051201140c0901110d09090b060d0608151806070e010c0506152701030f020102030f 65
    0x2403486038005195070440c14802910b00054020b2241d8400502c0c4100036512010030207a0360600040d0a015840b44501540fa02e0004180040071030988a01c2c00004180005a2480e80b903440c01803d02c0c03001442440302c200e42e40d00c1135020710210000200040760b8542e104100a5070f01540707550490340c81607100d50014400b07200c252007005022998041004080c203440d0303241d250f413142501400c3c0b0280f2182441070828040c500c2191310851440080300e040003800e42080c051140506c61604440c50708542a510303d40201c5821b0740000c3c0364000d84007000c1000900503c2d8409141c8074080c105241001900141040038621500500700780b080424508a81c0030b00e402400c0c0304000307040c08411416209a070070200801c0800070740064810742c21000404501d06401c0440c1c3d14000d810320700c840e80107036130981d002c00004045200300000c0100900c00b881c0c0c02e00b1413080886041032404048580350b246081040c00006120180000400c0051051415800c040b03106006890802580000360162 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 359001555 1250 359000305 359000333
    0xd0c0f0512130602060f07030c05040e0a06030309080c09060603061810090e061b0310031406010602060705070c0e180303040c050307050a081e030c0313260a0807030507 74
    0x181d8039010902c0400802c0094259014100510040c449850008400d00104502400740c9040c5a6901c200540c07052051003103801130325002e01c4581050814240c080010400c0d844141e0014450040210b00031601046202d040340004141028503156541000700560000e440b099010280c01802d40e00d29010043c210301c16800b00205c245102e2802d8400c80580c1c0280a0701d0341c4c260003810030014a1fa040441031343c0d2051010382d26540720b54070b0402c40c243d1607106d50006802204d443d80500d6040c200012154182c40d04d59082d64000c6e00e940805440c5030088907401888550108030510103010341c000c0440d8002c03a49181c0d0444015441e00444c00e60b88295429518011311101c03e108508040105100528068500f0100b4a00d44120b86803200640e8501c0c0e155584400242c20302e08a00300244d40281042505595a5440700c0000c110546003901c203610b500c00a560604410f1031902c076400c8a01d182403405007008200650f10014258030103030702102801b109110003004580c001c000040c0d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 359002805 1250 359001555 359001583
    0x10f05060a0608160305041b080319031503080304060f140a0e120d050411030105070e041a0913060e070303110c04050402010f0516150204031208090d0c0f05 69
    0x542420000d050142035481c03508490b060003410380c28420303040a10500c0c12080082450000303030b5078495141c6441c5110f900411003898140c46080401c04007004402001d20058034a920711141050f1003007038040d12005c03840c03044004e0345200e08201203090800119840792007144005080310051903003808490b652140d1540700358450081000c141013030300c11200304052060041401010040003030260b0302c614401214080c1d241c001082c100407042043c00c58105c1c00400910442c507006400510880303064241a12a0341040d803d1540310000800d48140200060000b160640e69185074165010345400101d900b03503034501410000c200b052040070003030345c440e5840456075900c0010f4246030442011391a0f10442c076050034400147e801450b91403c084c0542000703a200d80c00c2c890110700164184501510200c4041c8001c00e00c1100c65000b00250ba1160350000d84d590030691044841e228200e80d4226154412090b225549001c1c0d6958a05c0ca88910307a4240d5075a11a0340c0c5c80d08059220020304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 359004055 1250 359002805 359002811
    0x40503090307080c0a140f09040305310303050a020f070b04060f17010e06010513140108250302032d0f010506090a0b220f030c170a060c11010f 63
    0x4120710301808810010011440141000c401c1e0b40001007895005208503008000d01200790001070315088241301e02408010004000c2c1e11b0182000382c4141c0c020b0140b188020f0803e6443c000790700d418a40202052083d501e090300e441d0440d54143e07100c0e80806d03000420b5120b801e4001040c608204091406480c0c420703505900c0720302d00a809003800314441c1d03051b024030156036200e49800401c00c180b5811500020300f055160b464003401a1384520030301c5d403441000c00101c0c001042c0b41100f5101c42c04214800e0340d464000383d46040c15144141c0310f24104400180c0540ca0422415102e078019540200702c894400c68404202e42c0210b95070781c8440b50523071410034414108841d802070282068014074007600d00e10f00d0818070070000783c01c1c0d50035402000c0090101081d05a1141d03031748041d001401c03060751490a07206807260300c0c0b0007002003d44007c480c1d1848034240407a0500c019455007071a40a20700080110070002e83e02c400c0508184d071080d20030070402072a40180c1035024081c650380240da000d000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 359005305 1250 359004055 359004067
    0x161407180906090b09150601030b030d0e22050f16120905031b0606090108070b0f07060b0d080d0b0a05010f08090f070620010504030813060b03060f0a0e0705030c01140f03040503 78
    0x214006d810001d2159041c10303c0c02061405540f07001c90040000c0c400c40c54400e10400c4c1d0900041e000d0199802c0c014210600c004000403d200389a11481c00b41522642d10082d0741c2d40c1d00b00742030000340b10310f100f0303800240040480c0d01200c071180c1004048a201d0800d4034204107202c07a0f00920183c010207411500d41c428401d020150900d16441d5000d400c612020305031040c24620580d41510880d00b50008403c80024007401384445030340181c11500c1e008261001c1350003181010701d480e412505010034040c0c600b0107440501c0c40c2c00c04e1001d04580c0f0607104c419494031515020343d11340313034000c283d00c80c580505e00780e0b48a106c6052084001401d40d5864500ba80520120000800d400000324071485d60f14000a10001c030b0b800c003010300e0780207103c92080140c048003032600001603d0a000c07030315098495182880301040071440c000c0c0c455001c4030b004002e02c2c505501100d955294074401c140c0c05030401c030560700403548511620210031380203405c42c901c0c055010a01d014590300c100c0d03060b100c580001c911 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 359006555 1250 359005305 359005333
    0x60909080f0a05221e0b0a0f09030f08030415090c090903030905011d0d03290315010b121311090c091c050d0809032d161407180906090b09 61
    0xb15005c1c0361503040300100c105040010050700c6100f03202c840c10074420152140c000240c0b2030040c22000d558080d880c2c407108a42ca15041955400c1a1412202c1c2c071481401c480d1130b540d2900c40d0700d5035160408584520313180740400c80300081c0f000c1d01e401e904158039100e90901080b0301740122841145a0381a0050000391a03880b1810324108400072002c0608082c8050010f541c01844054110b240c0028540c00800b050002032800242c020040c20403540303040002034038900d9101034180d542420014401707558405a0040300c041c084140180030307520b180c03401c4040d81880703802e81d61304c4840d91a00c140740161a90000e816a21560840484074602c51404002c0020602100d60110202c3c06c2c60503a60400070491a2240508801a01d20a00c4500ea5460a2074408001d80c41ca500606006544955221a04e81c2e038150310b081c1580c0f8040b80c08981032038a140041c1d2002100d00590300f412082840c03d00442c00b031f1000304001d0340d815448201d40404250350000090207880030030010120004070b520 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 359007805 1250 359006555 359006579
    0xa211a030601050d0206090906030f070f0806061c110609030106080106050418020907050706200904060602030f0d02030603030912100e150106030207150f0f060909080f0a0522 77
    0x1180d4081d4009214020050312810283d521f440030443d00c0c90200c0d540c010101e890030180d407003240740603c030310200014020000360110381998038110945406603a0300d82480f0800132400c0715284611445840040800c1c81e48981294000b8000c248519203024880001d003911010340090425965452040009240c40c1c400c1c1d030302d540c4421444000c0340c825074002643d000002016034041c0b25002a0034800c100c6181d216420405801001804286050040039943e80200d04064000c91034440042030827400041501c0b4100c03520107602d480e18403602111006500040c01c0302d5003512080c0420450343d65201c034442071070915000140003443c0109101029144440d101c40a0381d001041003800751108100c0241c1501d04130f06015075590b94628051011402c5070625a19141c07400820041c0b05c0042d82080b20090414035017802a5500c4c0d40280084600c5400000d00c0001f04002d510180c00b80c05003e05500080e0717041075410300c0b41c10300c07044521000e00c1844944041c0411400c1c4071081ca405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 359009055 1250 359007805 359007809
    0x6090106053f06040b0603040213020f041512061412030d0204120b0109060506190e180916050622210c150f110c0d0c0f05150a211a030601 61
    0x80e0b06018442070107020030a1403201510180c065201c2b0311801c120341c043e94049a600c0403c1e00039040e81c0d1a580c0f0442d02c80e243c030b1041ca00300000c0d0201e484a698409a0240d94203664200d110495180001c03000c220009403d0401c0c001e031400103201031501d20402d0710150008050f18165051300300f15920b03002900d0801600051045480c24006006030345510065070f03d400428002c2d11701175892200300707039440d0121050655000803508922081c201c02d40d0701b00d9016100c000100c0350039451050009a41490134000d4613004076040c03008806140c445880d00d214500d9106c07a0405007916000e001040c12072000201410440808800c020088085081030041c0180d20400010540c030b000c0041c400c040d032801e0031040000011407138001d140e09000496510b0341c001d1203004822800d1405440d110168800c40d02d584101400014490400071903030f4034070303458210015140c514900c405440c0b500f8642480503801d10000043c003801c1d00e4a01c1002001107101808100902490f02018075001050f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 359010305 1250 359009055 359009059
    0x3020d05100605030313090525030c02161a0304020406080609010204030215070803040f020a0b04141002010506010f11160b0d0b060f3007050d0b0906090106053f06 72
    0x40010041e079110000d40310059409401f400700b03640d222000a640c3c804207031207280c170800c00c0308200401c0ea00c1d099400a451045d4035000e8400d1a07103c000c48450b0741c0c015100c1e404e04d4021541d000d6103000811001540d01131301c010000607815031a03103011440c050381160600c1d0300d40e50001d403d20662400d8000110500c00d40340c032091620060359502c424a01001d000101401310160301c003011980d8100c0703218050310188007007545455460988500300081241c000c2c0c0a6045c140c0c030485490300c113001d010320609040e110034031a42c10443c01121090400700003542540139040c603a034000f90940030602c008080e1125100d480e80c8000140e40b08035080030040302c0c403411080104280d00769403030042d201070812203400740540524988022840b04402192074140341102c00821100907000800b6007031650180c40c04124007008002802140300c0d0959a1692202e40d0b4001000254401e4000300168140d040c01100c000d521206990030403004801c00d1003903c24130354441c02e0650345102c0016806602 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 359011555 1250 359010305 359010307
    0x40323071203110a170901022a01090504021801050c190c051918020c0f0a0c0314010203060108040809041e06060f020109150b010924120507020705010e030703020d051006050303 78
    0x42d036417440000c0401c82061a00980c011034030384291307030081c401142200d0241401000101d2008100c14a0441644081d40804c2000380e0200d42400e01e8030036259418500048160b4040d110001550f09170007640122045120701c2030342e40e000d00020f00306034017407500c11a40340895505060070041d070401000c400e909541c0c03e412040000d40f1003040c80001020b40f06400617990208056002c0c01d050000e003c1c1d030002c0c400c0030010403c02109111000c11240a038010071a105121982e150903031005946c080e0001d0641004a00880c595800901d40d880004000056000b048017110360000480ea904c0948155039450802000b9080a0981b16400c5d1600c0200051400350b80d0b455500000200030321f1010fa40c0b000c0100c0543d00035840540038009074080b07150740c8010300501c004c4101c1c0b01903540300020250741c000079a4003698094540210f6582d00541605c604060044038045112030807254140305210380000540c607103d250524076070081e80900301c0d90b80d0102031081510016070225019500c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 359012805 1250 359011555 359011573
    0xf030d080f0a02070b190b0306010602030a050f1606090210030903050f0f04050303041e0e13020904060f0e010203040c0b030105090c0c0c1c03030b1504032307120311 73
    0x1038460360680c0c0c060101601101107480d0402c090b0000d01135580000c10f071404000902c040c2491a014408035130740030b01018030a8406e0394080c551689002c9c446ca20140e402401694083c5019078050410ba961030818a414852210107508404064403000e4603150b6482c0507903400e609207044900100003441c1018803000d0314942d8000c3c401d1040402c500070b001030100d089080c440510040b14000c0030300404076915141c4540c140e034900c000c0b100315560800c1f00ba010004421015030003141c410108841c220300518210340034800c8404d0010402c0740d6043d9100c28104220f03107107105113804031003082d00058aa01e410b14000e98218480c0d0400761301c1440030700040001d079441004403030707100e02849019610340030715900303192a0105a64501d82d01a15019844801200741c0c0c01c0035110602903034040c000300c407000c1c040c0412803108440b49142c0031010002480803c8a460015602c850141003003a0200342c1d454141e0300740034440d000004001c0c8011038034010f2682c0210341a80701900700c40070b070122030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 359014055 1250 359012805 359012807
    0x4050a060f050103021c060303080906011a0702130905251a0313170a031a0409031b0f0213140924060102100c02010e01060609030203030d09080d09030e0f030d 70
    0x1120a1107801c1c101500015600f84201312003000d030200340506c0c102408000c1e124540030f007450000715030510381d6109600000549050700f554003004010701e00d0b41c0b00cac0340c50015000d210b01c41d0003401d9403880007a00ca001c0180040e00c00c00c444c010185100c02050740740c6051000b0311340d240e203d6030300c0804120405100e904503890090112904080501d1081010300d00e00e103030480054082082d84548241d01180007122550135802890000040b0540c05c0d02c05a1141d0421045413440040030703000030702a0940751929204840300c07541c024016410340c44903034905c1c1e00250960a00502c01d565130381c0c40300c00501d541c12a1010042d0807840e02c4000e002d404074502c000b0081e0912442100d80c160b945840821040e90090046a21011000006000050340c845c80039000e4040300390b6280d655071038020700045075407182c0f5240040c1c0354000c005d54070b030201006441d0090104c0180a072000c8a0800206101020902ca081106442a2100101142403808100041c2004403201e0f000703070000e04959801c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 359015305 1250 359014055 359014079
    0x3040810021605060708040c0503010c080a021305060f070204110324041112090c0102160e1803070c0801050f04020f150f070c05030c01090305060c070521070204050a06 74
    0x504034000041e00c0b21201c802c08200d80385465406081802240103101c40940e02040c2c41d8462402043c82d00d51440da02c80c141030884001317080c03130ba001a60032804106008200c1e0000d010440b60503120b1120f6076100c02c0040e1050f441900d0040c1460000651081141410300540c8a8010741c0e2071524290314202034030b1180345908004141e84415080038403591913517168071000315038061050007602c0311940e101150581c2015295201548100441041198030001da0a2b42ea48180e50341000c0d054900300140150f110082d0524412402041d00c05c1160f1508001030b203901405100f9060085150144140c21a030f000b0782415001c074800d00c200030168460090300c0c150341400342d44c2402d48106541e0142554010074034402070840c40003c040c030512211186420a44000304c1c1901c0210044200541c3c01038024440201580c002800251050802c00c01400c140b60059003520f40d000c2002c14945100e45d01014010305404012910300154201442455408140018100840e03030602c003c408103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 359016555 1250 359015305 359015323
    0x1060e01181121041505010b09120f06090a110603061f021002030108030702010908010b0108040f0309080d08010e060a240903080a0c02010f0903020a03110d05120c0d02030408 77
    0x485858298400c0d82c014400e003151a484061039004004481c0b0300c001e88a0110140c800b80c0701d1900d80204410b40702c5562180c5412102c074400000e1030460341a06104203199410a140b283d80159000b10402000501001c0e12924507140a00600c0c0080c1c0740800100c84181d0703840d4003441082c401c0001c280c64001a00c41030300c0100c1c940606004020508900e0449a41c1b11108114000b100000e0070744400005009035900c00d0f254504590b84038082e0a080b07030200c880d20740c00680030720b002c54040343e405203210034128000e1502d0b2030501d441e0010b0900e0084111903100c00214607000420410340c060705032a40200003140c5d0144401e291680c828401703130510040c07052801002080b640c000340540300005c01140d02849203500d407114050007070801036840200b031317000c00c0c1d2000026400c00d01c00c01d401c001b035030341c000c1000803e18110f8a4412440d840501481d4105e03107601c030504c020038410450b1484040b40c00e8091580c4d01c0c90300e841c5505020420540c041590f00501c41400b0801d00880c7d600d00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 359017805 1250 359016555 359016599
    0x2060406020309030c0703060e0d0507020a03020d2901050103050c090a0b03130c0b1201120b0a05040614090a02100f02100504020301061a030a110c0a0209060406080d050c01060e01 79
    0x42c80e0345070103a0103030952040115248544c450340d40300201b000500d4000140d143c0300401507a420750038200f0240d5040c840d0200095200205100620051178102420b45846010302219006420b10304001400d032041503410108074001640104202c1d030b41801520741c4250350034000d600700140790002c02c1c0030107424003800c2c04081000c4006a01032050039410000260091480c0d4902aa82e2031305040a43c0074202e030101d02c010700b00c0041600c0742c04801c09d10003640c0c4525901d21990f110a1900300030040500200e60329500d45003820f03040070411802d103008800c0400608101d031100c0c4100120b6040c103209800c288200c0c12001c1140075004111140d411703180382c10101d125529480040d00400e125008100c3c10800701d0400300107880e00d1009103104404079142041424958980079070140504240000c1c1540b252103807c00604000140c9500300f24094004180d007901c0e8406d032400c1c00040b424400002e1804500c81040c0c100074000c5c1e000802e9010045680c55040000f0001c00c2c8030030380e206803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 359019055 1250 359017805 359017807
    0x70506040518181014010503031c0b060f12101a041a04080a0804090608030702130c030b040e010b010206060a0311121606120e07050604050d1e030503060a080106060206040602 77
    0x1401c4040311203c210010210001924080c0440130181d400420050a031100c4c90800c280011481d42000411544021032040046c005010b00002080c0a000c41c0e1200503003110041c00aa00c8001d00c1d1000790804201c064201d141a20b8a588030f5030424640d03a0148011581c9105014019001d40d01203405844d817550807940190801940328071035111300e500c00100f91040291400606c050080540280d0320401c00900849a442002035130724015414065405001051f1035600055540d00199210009040200d00c1c40c100380001002c40d80414080315660751103c4c0055050340e07060007041e52040d000c4412042c014110b0711200031040d02c4c00c440b24040c42e02205254101542082150201819202e07009100d03902e609009080402c00129084018200207141d0b1510001041c0b0409654001d8031403401d041ca00382c200501e81d048a2401c0d6021a0f9030380702c19610182002441410030301a442d103554030305042050007034204050f417110019902d0000d05105040e8003044c2560000e401031005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 359020305 1250 359019055 359019061
    0x115060e060a03110721050304031d1207090209010e0603190504050a06020304050c152701030f0204140a080a031e12150602070b0c0a06180f03050705070506040518 72
    0x1a001004403824411100101040400410500c0b03040c0d0001746070105203032a1b001141d840161840d0100b5030300203011441d42d91942400e40c1c0f440b4202c0c003052000030031250591407101d100c60704043c6940c001072003041c1c000441c4c2019580200c0c2c40403089600759401442d52520803031403a511506000c0c400b44032900c40c00401e080c01000c11041031a03d42250003190340b4201761070610341e01c1400f00740c0035006080a800b40c01c0c41d47c802100761503880660440300d4480e2680d20608035416845081c0c41c9040c5070b65400c003400d14004920140001d03004120001d604c5501500411002d07001681c40100346a101104810000c3d034001c056007128000c0ca00c1c400654aa6110103841d518011184141c40c01c0c580500e0b044400c5601c1e403c402103071015000c0d02c104944840e00340c1c3c0e00d481840101d03000341e4001c1500400150481e4005091009000c660820442c000c0d43c130030b1103c0c04002c5059000842c0402e660081c45001e100f01001854122031040c0380510b00b10110348050704d910750b002c80c449014000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 359021555 1250 359020305 359020307
    0x16020d0303021b0102180607050d03151802030105091515030604060306020a020d18121b0b0f0301030309051903020105030a0f020309010e1006080a0818041a030115060e060a 76
    0x5071021a40341041030b0550001c8800f40c14000d4000b072074403480e00915031004841e02c2c00c0600454084542140140c0280508010142e000c0c050b0a504204440d0b000c2000103001084880c0d5034a44070090503015a0301e500d4030f0304002582001411019075038402d010410780702d0350707084401d500440d44e0890441d16680e40000243c0100b180d5880942014000212681107aa02040e0031007411020780720501031090725a4034040d0034900d4001d0706846455501010042018245480c07594100703c14a15500d40d02e4801e09040e44d0810000002c1d00d482c00300043c010941c04c44450070207050191907024064800b2003001012150318400681480750010205040d003040c2d0301320304002d584160040d036590804a1001740203240c0b03501c03c0ea02d00c0c010401c2820307608680c0c1c0038072000c9075005001481005115102e02c5010742c4204003601c10f540f42c0401d100c109803540c0c0980c0c1070482c488140e050700b85008205150035180c2100714603034140328511051116503000008480d003104c068a003035480b0004100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 359022805 1250 359021555 359021557
    0x30e0c030a03120e1207021e032a0628050c030409020304050c0904110406050303131a2106010f1815030f05040c0f0501020604051b1f020d09050616020d030302 70
    0x3001c034994000d01c401c0100340e2217040d0003889014801c2d100350340c3c041d15000c400b130700c0103600120440d45900b2840400c03103c41c101039004892a5081040c6030f024418000024080f80e201102c0a505401013680d00604075000364003001881c05e0605201d42743c02c0c590894180c0700d1046009120300c96901102013000d0140801000c0541c1d0303005000c0300382340d06050420400c2c13000c1c964a22441242400000304142c200407082e100307040c4040240b07101d032170304120102c0140f401d2004180b00443c000c0c0050711710b4000503100c00442c0420340440c6040d03400d2900c00145000302240c0e1000901c41d001c43c000b04117492041245048a0740c00c0103200b6512600301040f40542030802c44840c48505200500040c07040f0410080121080742c0e128030030303081d17440c40103a0b124001281d001d4000e4104501c0c08001ca5403203d0420880800200301200b0810444030508443e481000c9050041e4014041d090443e07411031910009040115061410300d41e00881e402240c49404000078025003100c0910010140250 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 359024055 1250 359022805 359022821
    0x4081905041805010510050423040902030a08090913050c150d0c18050103050405030f032212020601090b0f0d30030c080f0112050a0b0703020406030e0c030a0312 71
    0x51200003030701e2852502e20080c01c0280140c62040c80c20700307841c0d018039000c3c40c1250100c0e55a511562542443d21a1304a000d1034103904094010362075144640c0181d034248000c1d0415403281403a591035110a805100d2010710007010644030500c01b45c3c190022840000d2800c501c240c00b140c00d041c4848402101c2e60319030003004054444107050001122000360005070f00080c59881000080710169200c00441c161102035401030007640040020008284100c00115400b2243c5082700d2125600502c0018076580100d02c2503400c00c030282c28038403010740d05110300c90041642c01030030300541040800203040d85c202031101d140314024108854041040103510202600d03220314201c2c40001816a050403400c04021400f0300003860560b042742114003850029010740a40940d034042c2c0d03824081d070b110104100c602c094a1a1140c00300c0301c40041e03449040148a10440e42c2c0c05a22685011000303402d0318518040041103800c00100501c0319107000544924950300b500c1c000741810003040310507004140d0a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 359025305 1250 359024055 359024069
    0x2090a020a0c120903020108090115150306180c0305090a12030209030c0409030206010e0f09030f0c03070f03050408010e0a0503070209060a08060702070e06010e03070b1c050a050901050f0408190504 87
    0x1038481080b603284c21003004402c0324000e813a008019603036186014225407040e0504030800300011401c2c4002da81040303903499281014140000c00795201c2c492000b046640f494001c0340300f80c0346c10610561541c10b01500340c010074080c0082c00c0d00d8039280d4804003a900e4002014040640c0032803030050035038003007244461001e4054810003a0030610b060007900e4170400d0180103000002400403840ba5008504003510511341140518207103034810480c0582c45d07220038407101c643d1100f031110701c0100d10800c3c00614100d1094507429995481c1541d22400d40301c0440b00500703541c1000c80c2540204e2402702c11101d08a9044400100d6a50f8140000b800702141d034010011034800d04c81000341e0160001a003406491284403400e28680d54480111500540b548016415030040102009540d8001d40074000c0518000300a800034a4280c003c801203e0301207440c40b03012904c900900020b04401e07c01c03280c00100034103108001d89010740f504500b62265031200201521150304c10b000d1544030343d056078083c0003a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 359026555 1250 359025305 359025323
    0x506040b0403060c0503070801030b041718030706020f0601050d06090b0a02071109070512070912030c111507170f03130308073b0307060c0c06090302090a020a0c 71
    0x5500c400c00d00360300305000c112032851400c4098940940103205891103110180c0d0388030066800c41e95401009078001d00308551145003460301e16401c00702c00d0701900d400311940720080d54401c001020940360030703c01d40c0483e040d50407a9050403541c4001146043c1554800e0324001c00903205403400c40000d180328a00078180c0c407031a034103210240700c3c07540091026602402c3c50790500701d0110208070340400d0503a14600420803c1009850306150901100d0f400561070800c048026501c280680041c40590022000101801c140000300401084600700e000010b942c4102c00c2d40d100e85d61481648a141e06c00740c02382c0d110b5140d0a520078101c0c0301302e13080c0700c1054100036224240300b9007158054000c00b40c11000305968500060125103c0c0ca00c02d60300c0801007010140d041119000445007401829001c01c1500d03030110100341c10344081102a0041c4041d58031050000c1d12030800070405050390b040b00d0100240d540003000569549410260040b24008005a40b5401d10f0820740b1a411603600080007041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 359027805 1250 359026555 359026559
    0x10020c010302031506121f1809030c05011d01050901020405310c120e0a02220b0a0f0612020a0203041a070204110306031005040b1501170901060512010c0f0e010504050604 75
    0x8400070001d000385501400d150119640380c111414503940b6029150f41f0801c541c244508c091816040f181801d40281003c1c00640c0c01070b11a03500703644584822800c6980491465060b5040910410b03900000d40802141024180f600052240002e00e203000d861940044441229540e116000c1d29410040c0b10304110f04140d500016060308440c42130050f401d03241007001d000d11040401d0925200b44d00428074040b40350000e942030b10324008040d50300d045598070b01c0c0310100c0380c683d04544005013182032a090105460004010304621038840740c10403440c01484103081e940c1d000030640d0251050f407e060704042a50f0100c40b006809240e1010707500c40c3c10161143c100303c01e072030021400b41e8000d034192010300446d0085070301641c00c1558010500084900001d280d402052150b50521205141c61071180140145101040e901a01c540f14103940d03454080180745011400c1426441204009010041115602601300f0641112408c288034100c000c042c1d40780e11603422280604401007000303484079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 359029055 1250 359027805 359027827
    0x3050306061b0606041413061808070f05070807030317071b031d0a0605390705011808030d0f060504020a0504090b12120901020a0b0103050d0e10020c010302031506 72
    0x26619240520b203401c003440301006d05032210038403540700011003440555403031b0348a00040c00b00c07003840001d1241615801c000560040000c08009004414101401c0310605200b0308280b1540c1c4500810703070020070300b000001d0700080203442c0075070070100d1041503580f40002a2101503024014101510819807007c0c1010b810240c0d001d05806004007100c3d6622401c801d110503845603004103800300d0700c284508000c050360151001c60358103001c0e1604146c0072001142450407200c1c03042144080d04984400d0103e564000c2005c0c4d41402050014240c8900d81400180c5030710507501c4801800303480e035040600d80080c2d40c200e14003e0002800856a6041180005003950010301070b0203625400d005104680e031800c4079181d0001c00300c0c4005440000c1c9182075a105c240e004205c07503410360203400d035600d01213920030114900079405000540940a1030b03c0c0000e040c1c2c0b00b000c0d1b1903489101c030715000e80300a03035000488104449003800c0050303598841c502d001402c4180184015400f00c000075402080e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 359030305 1250 359029055 359029063
    0x30304050a121b0503070b0d06090c0503160c081b0114160e120c12070902040f05090601210c020a050703120f02030c030d0518060109020910051603050306061b 70
    0x4240642c549071002a6502d50503003c0c0c01070351003120b505512605084c840c40880000904605c01810400126566540c0c401e005036013000340c51001040c0e0110401885000c11241400c82c2c038074504d0000c0c09011030303648201d070718000c2c925454000d102003c00030425078000d40c441019051980c001070082e01d4080605040151078091440005520990655003402d10026144e42d5034600070240200600b11400d128a0075004401054148541c072000034082d4600d02c010405010082142c141490424042c00350041c006002141046590065400c3c3c02070200915211080840c01c0860f0ba0340d56600700301d142c4002a04040c0c00b40c09040b00000800c10703105143d5420800585416000c510340d00340070380e2240103110b52500c0c15001040503240b100520781c0925400b09109001124926000407860719081c004d803c5840b00540c00210045107280042401128203400e00d01145048611103a14030b203134801d504000d0501c100800810700c01c1e5600702c19100c0b502c058058295003500003840c0c4c02c4e56 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 359031555 1250 359030305 359030339
    0x51806091f05010f0314030d06061d0f0901050f12030d02041e121e050307050606030106050d0807020d030311121009050403020606101e090f0f03030c08030402030304050a 75
    0x7081e204210305034400109030207040c1c100c0710f081d925040d41c00d103551203600d6005c04261060009010400906103404594441c140141c070007a690a181240c1840d4148101c1410b21780d200e1050296400030203955448a140505440003650004421282c00300410042d4a810307010360b01a000205011a07036941a0b07001e0400c40380142401a80d820401c041522101c001d4040e680b880380200b044800807c0507040e6004074030b91340359181c0701113440076100c0c103055030040f40c0101c980350805000d10501d450240600c4002c0c0c8802c07144d034032548900780c0d0f496010b48202c2c0d4000707024103030050480c010706000350b000480094040c940184d076103803a007107a4600d106003180c2c89000401c020201043e080c009105140c8130340e0381500100150f0701d4050030001400039501003582001000c07100f855184211840d00c01d50410340380c03134100300903017054200d0032450b487e070700654040d416000040000c40c0d84502c681a0355500968415075940313690010a081d4171940d001203800543d5490002000c0c811040c0c01d1030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 359032805 1250 359031555 359031583
    0x13061a21011a030912040801020c0111190305060409020612010305010f020304020904020108090715110124060f0c05161401020f0c010e0d0615050a060504030302060a05180609 77
    0x90090001018144000000e000b600000c030608900003944101c040020f6400038802c104030354101030180101801940207400819181e5008a208281e1038024028004080d030200c0129082445040145030882407415030070080584030300c0070400743e0702d4542c0480001078015249513621030380c02c1800004440c01b84000c0781c0c950700c1e0565016115415200740d900445d4010b20301041510755400446500c10050030101c1207000da1000080e10000510800300c3c6200c0d00c2e2900e03c81c415081c0801802c41c4c403030a0075046e80629a8103440b20f00c480610054044e03c04600304001c00c001490011201040b166030018120312503440300c00c1d000d00c1c035407180c00202d4000c0e5030314501c28480d031801280c50305407807045445282d00c0070f1007111266010354801209484068034088245c0140d444d004145c0e12b03950070807180c0c0c00d55094140a0350802c18440405002d0a00f0002c3c030741445c541c0c0003555600020b022488450f84d950100301c1809012015400040401c401c403051b9060000d04141c4400c1c13582e840103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 359034055 1250 359032805 359032837
    0x31a040507020d02060901090323120f160e06550309050a0308060d020d1b0b0403080f0304170309010b090a060803040e0c04030b10031214070213061a 66
    0x703410440501235618019810b54540b2075035131414003141d04620f22403460003511641486034014060710010301c548034a039640443c0143d4144445600910b48880c42d072201000703002219115a51143c02c00c0b20149814644a1a4000c80101d40c40340c1515001116003c41290300c18400301407030103181d07000240312145c3d158444402c03044200303808a0701c00c660001e0094001400c0d410100c1c1c01241010750204d0042d100844144860340051601402040111208032001005201100900380340304040d0180030044c40c5000c0c110b880708c0d02c4900840800c00085480040000c003084100f04021000d00c1900d00559143e040c01c01096000e041c07001071043c0a241040b0005004c40b10a004003811110600040e600d8103080c0100c1101c81c0d4401045002d041d1010400040014210b2402034841c0b01d10044100c2d620b402c62a0071054450b00031050707002c21141a0181171080003a0049400303e42d81111240c0c00920312448010180401da07000242c0182004e9914455010b5040104842c1004425071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 359035305 1250 359034055 359034061
    0xf02041d0601090f06060e010e03071d0103050c0f0303042907030206060f04062d0b07080d23270d0201150f03081c1e0c020c0103110a031a040507020d0206 68
    0x4c44200c0f0800d114040001c0d00014441076954000d10000907040c901405807100303c1d0b2280d4190b03100c43d401c0c074404403a444400c030040080c04002e0091210820301150410070302d1410341d0000b030740c0e4010b43c05012031600078225501c00385203542544000381e100c00c0740c149860380f01609010391144c1080310441c1c020710070b241c10088286003a11481c1c050365805e48510558035001010100914001c0740c21100e55000d901c00498960a60070142c00000d2041900607030b10070000500f40145d03030000c0040c0440c3d00c05c42074400c42540d05204c0e11039001040c1c090341c9403054505016110890040310142030680117040700300c0b12907941904a058064140c044102400f0f0341c40c006180041600c0c44080c114010910594500c11f58050b803940d401c1c2599000811030544134100e14045440007015000c00c0c995402410701d200d501407182c40f283c41802d003010094041c0c5091040c4941c8a004581c50825507100d081e54050f10640c40a070881203405841007000b4900101f0103541d0b110700c6120f60002d48170380400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 359036555 1250 359035305 359035331
    0x1309020906090405030a0f0905041407020d090503070b03220605010f061706010806031507020d12020909070f0306031a06150a02120a050c0d08060f0103180f02041d060109 75
    0x40b901550384140118600001c4090031207042c4480e18203101006125000001d02d541c0ba8043c0c02c4003e0880c3c3c221084a060100e800f9142800d2544400c0500804660411595074040f0303091080350007a18032107a90b44d0b81c2030003404c1c03044000c444100720002c40d6440d02051110640c80503042c2c900c1c20203804220390703c036801910003540346545903002001803c001001340d44981c2d0b40941050020f400c6880e1108204043e5004480460f22540103a00c20f00842da03800d984400203003501a0703060011454982c1c0310700410407440b0000c0c42c0c0c0302404444941554600d100c1e0748200021a00000b8034500285d0201800601000c20380710244900211054121f08002c0781c4c0c1114081030302a001042a10048004100d49400c2044600f00740113003400783c0704203080c1c20f0010000140e00c699800c0000e140c43d10400040c4411105414109442e0110951032407a4102032141100c1e00031a8010f15036000d840054050224207442e03442c103c01c51000e5440146000a500341030301c850540034030140308500c0e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 359037805 1250 359036555 359036569
    0xa090c080f060a0905031314010807090305030304061d0a05030d0b0609030d1214010806070909050c04060c080c121b0114070507110909030d150b0301150e1309020906 73
    0x100062141c1c1002e804602c008800c1d910901c1c1c01c621500a413801c180707464444900e101c8550784040800504081300d0b80196a0104220358401c00d6820200880c40c196258255203000003800104001c0e13440200401e640400e1a0308603421000000300c40314117045152a507240c1e0401185811054184007221400c0c1c50840b094401004000e0014020001c0300700301100c1d030080078500007045960382c2d40c0255444c240383ca4818007034281c080c0106950700303004800900d0100a40d2010524502d0141807000d59240b89040781c081b9141803501507221170381d90405201621821080c01e006101d81d1581b2020301c0b0303903100070307011018038031a041000c03802562505090304d5025040d51007056254002509050061000d004294015295842040000302c04a20644419a144c0c4000e03800070a410556040350b0040050001c2a6020082c05500c0c0802555203804180641c03840c8c118401c1d082e9541e03510032034074508c03944001807034050b00310115041d180007014040000c2c0d0003900700d1400a04a428629 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 359039055 1250 359037805 359037823
    0x3110f0603070c1e0c0305101506110708010906230705090d0303020c0a210302040e0610020f07030b0610020a230c090a02030a0507020d1d01030b090a090c08 69
    0xa8280c500e10780c1c03500000c82d82411a0300741103c581d804e456481c03000340c1e0398146103243c00c0d119070044104d05003141030107440d08000c200d1003030340c450501c413110600082c0c203007002c001c50701e40e41090388141c03002d8900142020101c0d081080c4661900f200b01003400384c15004816052410101800082c1040075040000c00040300c9404c0848d508104101460400489064925000e40740050800d810341d2000e50070032501820664010000d41d10600d40701d07504003044066119142800c505c0e0a01d004510505494010803071403207480c5490704c03511414020f02a5003503254803041620002a2a4500458092026a1642d00401d01400b082c5509800003410100d429080341800d900b05031440300c4400e541e803a910700895a4081e00445031910307226044210700074200403002688034031300f12800707c3c100d81d401400141154004e061a00c11103401c108a41214240c0e6038000b400c5212080058014218410005070045400d00c100141e847c115404081260b118031034251841c2d03600c6240e02d42da01542 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 359040305 1250 359039055 359039059
    0x9030a150b15040b0d0b0616060b030f0601050d0c0807060513050609060909090106080a050f01051e0103062406120524040e0a1b06030506010804030c11130f0603110f 73
    0x300404d10212000360701801540b8000c91004c2000003402004c518250040011034420f004000000001c000342400380740710144c010303402000d4540b0a0841c15580e03503010721809000c3c000a94800082c0300d100c1031040301034020403003140d19450303581d84001d00907401070414804001a822000c509490400b0440c0c3d919200100413a080400d0141003241810000d45181f115640e90399002408500500503050220f0280000c2c015072002040c5107070a640001b06180e424140711940c480c520f030401b80350306040d65000800040c40300420000145002d518440c14042d04010460015039141e0000c1000509005018248840c0d04c1c6c0303118512007815002c2002d290119405244001810035034482c400000080045a40c2545079855103240003003200b0602120501020041c49840d4160103000e401c000c1c01e00c0e02400501c1e02e914001c0007203140c0e12009140c03038060842e10a09139204ea00c121405407900808004a02090b0254001030099110807a402c070540302c1031a4003860000e10090b544140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 359041555 1250 359040305 359040307
    0x402041d0f0106082212050405041a091b0702030616021506060a030c050d0203310f03030c02012004060906090803070f15090804090f151a09030a150b15 67
    0x981c0800445c01000c1d012490001034a80700b4075030110b403910109409600d200d85400b42d41d241800c0c180b1007034815205c800b54000c41051140d0455855628400754481c034080c280005d134001b81003c560848c4580113010303506215113410f21003100044140c000703040e4126000c5401084841c000d82d2458801150203d60155042c404440107074000d03007005220074601e09c0d000d07241a54a032040c60032600242c0c0d00c040102c5c0c0071640854100350140d00c01e00b5180a104055109126035a5a1040d2500200340142003685840041d0310507070003500441c1e140904010621201454098000400e400c58860900054400f83c00065030901851000003900c03030150203145032019a4652a50a03c2c8141d030032504801804102d2140030054420039288a03c5032901540d40c500c0c00144005803250301500e1400746150403180c16a40c048031110004842046450b40e4210325040110b801a0041c0f11480d40c15010b1b900e140002c000061070702009504c9002000c016070b5150b40300380020000001484414440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 359042805 1250 359041555 359041561
    0x30b091303050a021014091e0606060f09040e010504150603020a03062c0c0307061d0906040e19020406060516110307090609020a020622030e030a020402041d0f010608 73
    0xb2142e0010040d080c0180110f9084140c880b038244116101a0308081d42c50304100140900c0410070710024905010f0204188440c0080c3c03c1c41a88800c80580058480e04001420414542c5941c06840c5010001801040b0407042c0029680c01f074442243c04036001c900c1c02c070340a0b503182040c1c403a80003982d1b000b070a038220700c50941d582d8000038070f540000344510250600900060b0641c0400200007140070a001d020042111004d0501e050304503080001800b05048182044a022108508a04808072098900d540b2170101040c018603002d520a0414010100b10210200c861034285640724820385040003400e9032018115542d000301d03420f001a1481e01c0501e0000b14810000e800000c003001030664400d03503a81c1d04114122285540500403c3c0c3d00425081d5443c0c0d0103105043d4494540590300d01000e0039403100350080c80603c003004007407048610b41d41c41c01303440c10014200f8265029008542c4c5588400c03940307016510410380c0301082c10101e400600882c0c01948802e0413582c40e5195081c55813 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 359044055 1250 359042805 359042807
    0x603100b07020d061e150b0726210c1603050a0306080a0c061805011b03030609020705060612031204060509031c050702160302060313030c061407030b091303 69
    0x540001d4060341d0200d030002c08240401c110303224806140c1c404404240100708030211040680d0a4000740510044c550315080040ca4100011500069403040704010040b010002d03801701c01c61039080841c441140804e504a400480110301c200003a6101c100b0080d50342c4140c0d12007212701c0b40240d6600c9907400b9003d44800680220042d0041003010b0401150a9850b0110146032594a440560f07150001c200c0400505400038908800c1003c090080b00c4401e003403a001078404814440140080840396000c2c0e4103052095100c04042d08a41d00290741d6840d49040150b40d03820700340d90242c031480544507500140b200010449100046400c0c080c01d03079654684900b00206401440b405550104009503042e4130201c4800e4161440c0d07070400002d5a060441000f0314103c15040d00380003005410b0020b0000d81c1d07904040c1c9030b002c1c040a0040d44444410314044480d00e010301401010607062003c200908400ea001c1e0510410b03181d9020044000680100110003005885500582030320f003c02101107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 359045305 1250 359044055 359044057
    0x50708030a12090804030f0507080a1b05011b02060a030b030106090b010219030e040c1e0f080702070639050705040c090302100e01140409050f0f0106090905190e100b0603100b 77
    0x14001c230181c5103c40d0384c80c1c101d5424552a000c0071990390304507400c102c40c45d1030348107040c5028040c01c0ca882c0502c0344620810f00032000440101a11480021620039421f42c40fa421180302030001070000d2054a5884052501a021010b045405402009051004114040c14102d04030f509551400444d504c000284802441c0c8100c3d0141000045d40703180000190069440d644c101059643c0d110101030032034014000d10001d001c0ca0110f4101403401c0040d5507202c4c64032040381c80001e060b004d103c00b00000c1028009880d0107504070f030315010b40100341407200209480d81140c600303a50502c00e6000c407140c22100c00c0020701000350b04c4551103030805512849050664050714060500182d00c0c00034070580c4883c0e40207980001d051989580400c24044041c211007034102102030740d9050300d5414054040c000c0995400f5824410b503451001a80300743c0060040c1d80100181c0c0b10400c000c40405031595194403031803c8024449051001903c494108101160310510300031100d0078096041c50311140301 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 359046555 1250 359045305 359045333
    0x121501061b020a0612050f13110d0215030411010207060f0302031e010b091509090615040b04030c1502121806070501020c0708060a06060c120309050708030a1209080403 74
    0x1c0401011841c801611071a11803400742849844116180840031308102c1640c40003042c400d001620001802a040b0f00310304501c00780380c0d1208201110f08480d6000c1510a0019032001e94000a10b02c90800b0a0301c010380110f0295000b100740e004a800380d8801a680c0e48000c3c40b601f00018054902d040d003035813081c1c1c040c6412078a8840138680c3c100c076410006203659420780100100d260001101c5100f807504c00284408070642103070340b03414141c4810024841d920010007550040245500380070190440e1000c882c05801c09000150700d480c2c43c0d00f00580784140601514102c0d80101009081c0e0030300000d103a251460001c0c0c00145861807103e8200c01c16100a0180b64200c0333010b00902002940038000307030100700118001040590715081085241c084080d0580240c0d0303150081c107200c01507021502c01000d82e00604500c041c07281090049008144100002c0d1050080b00804124410702000502d01e0580e0f036950200c0c0c0c2d102c8000710f1400c03103490b9100240094010001040051800409802 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 359047805 1250 359046555 359046587
    0x20309010c1a0403030605030c0103050f1302180415060806090604060b0307050a08010b010e0603040c0902160f06090201110127030e06030906010303080c030103020310111303050c12150106 83
    0x1489840c610041040b0380300c1550201e0109444100a20003802c04000b04542081309203814400c43c103020120f00c20709100980055022000c45c0c1d0301d4800e548490301e0a8a030000130102d1003c652505062070401d44139184207051a080c03c00c00009401c2c8000500140104401d00144c4078603283da90b200c40061200c100c2c4c05070076000382040041c03165689514480101030f11000868403908103c0010303c03c0701400d1103544100824000d01011620f10000c11090b110b01ca840140c1d41d4012003c50019551a1a00100f4001c2c00e40e24040c01c02415800c50031503070307100380c9860480c03144140352a0300369080040c0440c0b09070701180750600300307080d04407810100a001e030410005840305900810803962044451030001e5100c500100100340c0d12100300c540c0994043c208074115415035002176117032501c10003020b90a07512448808000c0f641842140c8000c1920106883c0306545d0b458100d843e00740c1c5d04500c0d40b24030a10228482415004030307540c3c035591920510307112280c0c2081000d841c403214800715a4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 359049055 1250 359047805 359047823
    0xa06090b19030b1503160f020a080c120c1b0301020f070b0c040e1807050303040f09050a0b04051911030105010c0308130501020412061a060d020708280207090c020309010c 75
    0x25119858a113000c0030580c0c241600207035286000340b0780e202500101e000090400040800c0c00f401194081b40b410b203260b910001c07032a52000c5004000f4034180417112041c8003040700040c165007051000078901c0e50000d501500d551129140c1041501700c4c096020150310000040203914001039032501100d50051031001494100354a03a040e0b4000130700c08541a0040f129964900960032500300000d0000344001c900840c17034107050401000340103080388a0f030f0004c4c80d11040810091784281e00031501341000a80100460326100503d90700c448002d40303c101d4407626001c0384081c512110000c03a0b0503a00181c444c6078408200f0303541241c00000080c040e400c3c20466941402c0011028002000109009075016924035140e06125049070750005100c0780c000700d406144045511220300b6640700e02c201040050320b42956040c50f49084c0b16807019100e00d140440100d160042020702c900d030000005038225400301d81c42c1c18a8104840b00b0342031035000f5a005100a025542c031035014107c20b42d00c0381c103081d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 359050305 1250 359049055 359049071
    0x90902160506040503031b0f0d05090a021e0406050108040f0311031b07051201090c090b0a03140114060a0e19091b0314070506030a091a0709050a06090b1903 69
    0x7040c1490300554003141c20350000814042009482c00020248514042e5468500f04002800102c9132281e000e00c1700c450f41d226400191208418415201401d030080c0c400e0b40d0710013040105000300119255484d21071850500c1c0402d07154801c203455885580c3c060022404464181c9082d280c104000c070b00b58007070388002c00c110001c4000b0344800001880c0600d00405145c2c2c2000d00304805420b41030f0084180b42c0c906070010010950a9080304102d50a111001900a02c0900859484410340d000688a065508540310304007105520031200d030382103000300c0c0440b61220810010309525502c5240104165a004035441c003848200602d00200042d4002503503440302e80d075100c4200d8100007002005206c0c0c507020001e0140080505500d5070380c40d80034008550910307001034102d0001405244015039152405030400c0360080d101a01008440d0314944c681c40d003a04000e0018445000300c900598616200103440390003415603806541c0d4000c1e000381007080301422000200000003c0c002010745612103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 359051555 1250 359050305 359050313
    0x1b08090d1e03030501060804081812010e1f0605090c0904090204051302011707020a11120316060e0a08040303033b010e0f0304030b07030605060f0a030509060709090216 74
    0x14001004000346484407041c41c81d41000380c01c46805074030000511501d00c04100014041c441126070001144034100034400c9000c0105e41c030034144c48807288aa41c60070170381d00d1403040001001200c0c0d040102c101000c001d00c15603508144c85041c462203030841055000310303005161020160a001c0006040014840b0040c0c00080a8400640701c282074410083e080c1019542c0c04041155518400914415207090002e8001d54502d0351003c042e017081d11802d20040c240d0b4078041820340c0c11140100b00e035140c1800500c00d400d820030040007210761516086800b0400c0c64041094102c0030b8011030464245480c40c0c80540c042d18090030349040010801150a28025640040065003000040000c16440120000e1821902c00e0382100e40242c0c00b08281c00b020500c00421982501c0d400030019965486500c000d402070251900000d5009202061600407010317600040d24940a40c2e80e81403100340c68030b0141c241ca07500705548100000345140700c02e0100b402c441d00208071081e10f92400214000c21070320307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 359052805 1250 359051555 359051573
    0x12090a0606032904080313030203090316051f020304051e0a0303031d0c0f0d08190c061409060105270c0403060c0207081c090b130905071b08090d 64
    0x10482d448182c800d0f501ca000c1c040b03c0011802054005410540350400743c44003003407800014042031070034140079421400c040c801c0c42036031181d5001030304959401059501d0b01807807940a010b1540105091404140314400c240c02ca540700c0c0d011500950724050418040c4401c8503035a1240804081460007400180d4884011190095019690001d00404d0900d00c800003080000540015907000b052039030303c41d541c0c08011145100c0121021041d058103443d000c2441d0140c40c0c143c40f42100c0b120580d00c0c46a401c810411a6144a8181044141c001d020000488002900c080720254000ba005102074104801c0101c81c80e0001360320f0710046000000744c01e00e5851f0480700000d1403400801c1c204200b1a8502440d034204820b4005040c082e8100504503a4520140d02845420f4114801000d100c40c0121b0904c806043e100c1c0d40070b42c2e116010f071103281e80050705209006c00c061800b00000c618030b01c038100c1d4104c1c0031100c07643c1001c800c500352191603042d008410050f40c4031030401c4e09100080c00c401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 359054055 1250 359052805 359052809
    0x6160501050702120a090b031b0f07030e040c0c02120f0d090f0b030f070e06160f14010b030a03030e030906030103050a0308010801110405130e0313030b100302030312090a0606 77
    0x40008600d0b468840c034001e0a003010307100122031010042c417080c44a15004086a801c0c3e4250202c20b58480e681c402170703070100081110065a01480c00039101c0100c08040004101c805e0003900e60f40340c4645110f05200869200c1044900000c0d800000e4070014a00f0141c8103525140c41c03000c4480051503c1e00c00780c140510000c3d0080842c0500b981009a6440500100300400b84400c019045140c107401c0440052002004c2108000b202d02e6051034984c0c07144165280c1e4100032050600c0300744146068020a026000152001400c0284507207401c501401822607550025003c1c0c400c2c441030341e0f0141c0c0a00b103c42e0b0721440c0c030700050100ca8103648501001d18000e601400042c141103020f070402502c5004103802014199044c4040089864020310865048400c1600e1040c44045030b0503001c2c00030f22503181c021141c2e000c0041d20200d61104c038803100e03050b20300441d01c2881e9a114828103044c011000d12000350160070910040400015414402d584000700070155040100c4940d50320003150465 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 359055305 1250 359054055 359054063
    0x30e030f0d1403011a0f0d1404260a0e060c0a050c09090105010e0105011110060308090a14031005040f0807051c1d060c03040f1203020d020d050d0b0616 67
    0x200c01e01c0101952000202e840380c41114401c07031841d4100368280c074808421414680c5803020010b00e180c0324031054021500c3d14084000f08000c1d1192286114a03201000c0d40e00380d80c0e02c070144062100222002c504c100b00510800c28aa2401c140080c060380c000c2001c00328258001018032413895608410b011550710039208501400000da00d4400b00070f11410702401c0000141c0c5407000500c04111403100e6541920024241200c55103034800e610f40c504610320f40c9405195041900001c1004090009064503080441e24461030702d0f107502040044000c0040074039030590104c41c510f07000120aa0005030058040c08074a0603940c9907845000b0240d001d031004960030b9000f1003910740c00d014400c00b1038003803d03403074a070440c2103c82c2c05c1c1c1950807280d9850641486504001002c24442c0030410466004210724890217205968401d14585000504007040c0c001d0300844081c002d0440c80854610700708400d6448090501d001640e0500c014000c0b4030f821500040c00f0000244d9002120010311005446 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 359056555 1250 359055305 359055313
    0x2190b0f03090d0f0906081003060218030d0f02061305010b03330618090115171216080306220b1f02251505070314030f0c07030e030f 59
    0x48090740c540f41c2520200303010080c0100d104640c0a9010051800b101d080f0318052240741c65105100c8c155440b181d00c01400c0a100249440c010199820280c1b2090800c0f025110580564102502c110030301c1e02440b401030704950002000401c0e51800340c0d00d192f02840001402032801400f291600e1090094112001c91240d95030340101d102c0d854100c0c80712603010030001e150400b880072648294221502d1400e210350f4400244021009510101d8880c000c1e2003501c1a080c3e654802103c40d07100101d07084000d001c1c02c89800c03000007204081381c0300c3c400308005221245e841a114400f8542000d44019032000740d009443d151030b030706403c91304034910000381d0026a80854404008194400b401410382c240504105600107a4002c14480b60061801c02440f1103848400c040c0c05c403911144d00f0110141800d00c0325403012591040c05048c44070f1083d102c1450401e887d65100d0744a0000b114146980444400007078080403400c000b0349034544c880c0c207203031414140f403800090414202901021013540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 359057805 1250 359056555 359056561
    0x1a160305071520030604140114041506020a14010e0a0b150a030201050307110106030c0807080d030603050c0f01020c042a0c020303030a0917040b030f090d0206010302190b0f03 77
    0x31034407802200180705070ba420020aa01e070f54111104842c3c6000c0e0700e8030648040000794054442c0c1d042460306681548010140d980c40b50300c3d86032408101d0006d42d01451900180c04907680d8140c01c00015601990010a00c21400b640e58480c544100300102d54075540301e0355080f120841c20084019030504c2805c202c005450b040b8040e003114281c000c02a881500440340800140c2d03001000c6039003082c0ca40c0b80c6854240701400955000d0221540010f1015050f04c40000c1c6401004c6a040c06a1b00c0c80b400350b4003a13a202c1e510440543e501800003034210742000013551407501c1c041102c4501158107005445001d0304400c000f4003125213111042a01d000d503c2c501d40c20b001d040002100e05600c080c00c0088000b90346402017542d0f400010621101513036500c2d078500600c01e1428140e00b12411000d070448c0e445444070014500c58000342d4080001700031590128040b40e1002c2680b50108099a00600461f0b10b10340030000406074000745610b034540c080e000826594002d40c01404405242e00d4007543c3c0781 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 359059055 1250 359057805 359057813
    0x50a1a0c1f0b030d0f180302060403050123010e0a0f0e0d030f05010801090b04120c02031605010206010e01080d030506120304120209010902040503070608040201050909010303020a0b090102131a16030507 89
    0x80380b524100303110390084000c0f0fa40b01604001000b00205403403815004141c580c0101c0c545020035074002a43c80400850b001042100c15001628013400940110600f4440080040e010003403c6c014401511280000203001c400c09a20035244410f4030413001c03400740c0950300041d050205059000b00083d841707986000881445000e090f00402061001704604a1552101d074110240a0030080c41c240d00c00c090b04aa091042010343d0700701e6001400d44540d40e818107014541921144945405401807900005a503040c6844040c121035103080034110b122041c0008070024180241129408070320110a00a00c92041000d80f0240c0704018000301c00103801d00401002800583c00314150b2801040140a661800f1515404076405803d00b600552140d10040c0c48a01800002c0e54202841e10b0000051507400188008054003400054086850f0b0000444c00e0303100301c110304261840a80750400003003030307070303000320318121407552051b81c24060302503c1d038051150501015400a100450048248 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 359060305 1250 359059055 359059061
    0x318030a030251070f0203040603020c0709050c04081c05070609020a1505070c140a0b03101a0d05071d2101020c1f0204120209060415030305180406050a1a0c1f 70
    0x184850170024240e29544400a60704c0c45140910400c00d60003042140380d100c810011750010740300d1b114081c40140781c140d017210025040303031058602d0f9100c2c00801c03200c0c294108503140d501000b10341c2c3d420710b07080b021340310600a8045020b00706e030050b51614000800d00d100c411404d0606042d0307035803540e40b040c00c3e007400780d02c608032a008015070140b8810881900d61751041400100d501411480d902d0f03550700100300c60802d640c1d60154421031a199004c00d00070042500420b00c0090751034042000b510344031411103015120580010303580040300041042d07440c0050803a2a819100140c9403846182450700d1803e80e00301d11920105c690020207212a00f10904802c1507442c1e0014074110b007041d180200302d0445540c400f4000e80a0b0b00c04501158207038582d42c10001c25414454070f0889141c5d5645001449a440b154090100d04105c222842c0c051800380100d40444400402c200b000e40d00388240d00000c504040c1000d060340d07108200f000d820030403c1c0140321038400c804620620803012482540c00f5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 359061555 1250 359060305 359060311
    0x80d2f0c03010e1219051201060519051602040230090f06040c14060702040e0a1104110306090a230105190b2a010e0318030a030251 58
    0x3054200351407642100d40082d081d28011131503017400c100032a1100c2800d481c24841d18000d8068081a9400400c0641d000b00041c102c042c0c040c1c0044240341010882100c00b40186a95000d07880e082025050143c50907801130038600cac0d112003075810444010040220300700b40700385e02825880030500421841e04814403840003c1d112002c0603040c64038156440140c85003140c0242c0d410b8030010300a20360142c80b590300f5904c15560240c01000103c03da040708039903c000c1b01e50221101e545160514005017040d00030182520786207542c00d815503c4034420092941401040611007941d15a01c04020000012100400c2002c4103600c213419418403041c410000e80b140c2c039140314050040c1c020002c0b00803050803696200041c4081201c15045020341106540c01d10025440325070900f10f6100140601000800c4028109400b150040e83c0c144c050680b5101c95035009009030700140c64030407410380042d0fa132071912250340441a49102c049505201c4108070101c11108030f081415050440329440100150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 359062805 1250 359061555 359061581
    0x1b19080405070f0303021f1104180c02120a1b06140a20030105010e010e0306190501120c0e040609050d05071203060f17150a0c120501080d2f0c0301 65
    0x2449505503100a544ca500d030280204002204458501505556902c2a0146023840180f190364a81e9004440f41040040758181d20283c540030300184002e00000f6041550a00510203d040820fa143c044c2e40e451809002c80e8201c8000c2014079000440f036206030f503090942e0010241b41d6090025049003110303400781d401d0381680820700d40d640995034560b00307a904484c0c1c03d1070070300c02484c0c14a00407111801c50a002030340500c10141400328050205140030b00701882d20a0401c2607a17a00c04011980c10045140900410420f101c140041d02a410040c0d0388107000380c20100b01995103603a00f074a4a12007107140c0300000d10103c1d0000420085c11510110450a89010b000c03513420a28215406046403040700342807501405140442801403260401e103000406500000d40b03040ca40a1003d400c0c84d000f690009560480400c6c80301c0c80c1480380c02d060340c10020041060401c1c0c22401d85078a00d40002084001c16200401c0b228542c000e000c0108000d00074001d0403409031224241402d44404103007100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 359064055 1250 359062805 359062829
    0xa08150105030f0903091914030304050d1b0b070c03021c050c040519050f090c010c080f130b07110135040218010e0f010605030f1b1908040507 63
    0x150a80e807003020782c0c0d00800040d800108503260544420701c0d6125507594103400a43d410205451100e1110500c01101e1402900c09000c080300802c2645900c10b80c010580c0c41040603c000700441d204941614031440f005c1c0f0549200c503211503c00d80305400c00d030b008542a06400340705108509044118680c00030b0b148072901030f415484e6984030780b81c03445d00c00700328002e59440c0000b0303456401010308080b84ea49114020031903800d01029403800d4050403119200c9038410f00410000c554410480c01701303241c3e00420f42a0812480304c0c0305a00c554001d2482c04910440c0b82c0c00408c008881e400140555440b03003044540c10500785001404010385402c283c41942064180c83c486d0b102c003a010001f07001202c00c0702c00901d40d00c0c2d1000030207080b0320088601c42414400c0c00859201d50103900d142c0076003200400982142e907144012112032008803103586556607290003090181308510030000c0c1100e00e0420350b0b810181c00c0b03580c020140201a40326400190b40500b4130007401b0050020b54094031100d4442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 359065305 1250 359064055 359064091
    0x801091a060310240f0e0112020604060315030b07050a0e1017061c050f01180c0302010f110609031305090103030e061308151905010321021f020a08 65
    0x2600d5903c000d42d1207000e5030b1500103040c0814002c0b12800c003c20240d0450002e15619000440f1207840980103040450b4200c01c0040703660708002c1d4400e08030950061a20345060b00f020f400700d000d8030380411902480b40000a000c0001007180b003c0900c40c0b00217660300d68503003110110080011000d40d403054014000c002e00f41001c0c0d603001c400b45c003c21042c45000c44d0b003525048040754140d0f000700541120030702e0f403002c00d81c104000400c1c05c188241c2450000d02c503401a6603669400310b00c041a0051880070362140c100015400b862420401004c1030800780745400e900604c45040400454464001d074100140c4403003109240340c036410103081c1c16601e4014640c1942c0c1c019000d03104112109101c0c0c03001040e1020028581d48403400948102c0040e24407140068500d0280d00380c007a1880311210300050001112101c051003100c0c1240c2d00b22142d0900000040310342000d00c0b44201c421011400346580d01c10329808880200540c8641d032040042e5610f03210f00c4000d20080340580f800b081c80001c0c03005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 359066555 1250 359065305 359065309
    0xb1f0206150a33030605030304090f0f05010311031608060703051819031b020a03080a110f060708090706090515070501050403030e0c0102280f02030303010801091a06 73
    0x366901446001d22095071891071000204555426400204150088220519018841d183c80248400700390a00040c01d050300300141c090315614001c25402d40e10901081200100365000709401132417410000510b0700d1011800c0081d120260070a407a0a1071007801d089d2541001c0055840800240d48004505410442c6403a00c40b180580702004168540c804641e400b00110702091007080503a003260525070110510007004101310b00d055010a1406054030500e17010082c40712041a4024417a10b0524115a00c83c1c1c1681c01c1541502c0c100315004045c0300395a10100084481c500411009201c90700c0c080c0700082c547da00003403019100d0b4008030000c00449801c0559801602d10451b05c00800c1d0081c1003800841d8011140081c00c10f40c2824180000d143d01036120010407071203107059804e030640709401660384000f200d00e02d000305503400001c0d030900040c42140003c654421040100049500e40000340755400032303008084e05940d6003035942d082044003d01c84c8407981c3c82110071681c80c03400c500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 359067805 1250 359066555 359066563
    0x30b012c10171627180e0303040b0a0f0207150c030605090412030207080d0b0a05030c010207030b040c030c0303170f04030c08070c1a1e03040f0807060b04050a0b1f02 73
    0x40403c82d03400820140c003a000340074203002140d041c90501e2400003c0702c080e1118008002510500c104000f60724181040c1c669140252145400c80c40000c6203103445a0303030342c105100d000034640c040099440c000308000d203005000604003580100402070340c1404554510023112043c010146c140b44c9404400c00403174803a0002c05511640001400d802e101881300b0603406441122001000c1c2e810006e4001c40c068256402024003680690f48108216190024160f07644420b03100c00b1301584c041d00e0204005400303108120b50162241c001441c98982d01d07942c00c803400300c480c3c1045020440845824815134100141ea0358081c020b1070207042d0505141e00d02805007005000080c0c010440041c00c4018007a400704514001c0003122135901c1490a0b45604007076541000489042085120390745000da8015041504c1c01039030003c6500b00c24084542d24603502e54003001080342d0300c54642e88102c05c20380e1944101c921800752a180802c44410341d500b089081c8418211403035200e6840d02d0510000c3d98000703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 359069055 1250 359067805 359067811
    0x20a0c1806080d0320030912280f0206060a180b010c0b16170f01050d050102070c141216060e030f100b0909060412050d110309160f0b0a030b012c1017 66
    0x1d126990349c1561208002840d850400300c00606942d0744030041410b9031101c4000c00d048420f80c00e0b03c050761540b42c104603040056101d2000c0d90881c001005140c4d44d02a03100c42412070050401c0f20f0384016950780c641c0703031440c01c40c1c48402105415007110702c46c43d00030505c014411160a04405646441049419442c0c01805840d00894488861004006003513045400c40c9800c201c841220a54803c1035103040304010a01501814178a10000700407880026210613003072400b0107510100c4c0c105882290394902d04c0c101c040d4140f040106091141e4024802400700304036022001c140812164244141c44c000513040380c0307040d070211040001040c07002280310b110600b07a20f010b40c1e9601482c03a541019000e440d10700032080000000703109039174100150f00c3d2803510f0080440074140f550b1392807520001d1603600c540c110f54a0100103d0050b180720354070003c9200c0e01410405560b034080035414400b1650060080345070b0407070f244183c01c5854904452410191246440c0d49054031050120092610103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 359070305 1250 359069055 359069083
    0xc0e0105011e0f0804020d1e0516030b0f0c070b0f0a0606170a0f020405040612020906010201091a1f080a03111618020904050c0a030c020a0c1806080d03200309 70
    0x1c0c011030b046680b1039820140181c8c2005952900f824013080d085450b08002104840c1c6105904c01c0f600191000a4000106d0740c03c11081e600c4ad81d521204c005012000a1510041ca90304100e003d000a241c96a014003943e000c1400d81440e1400c0c01107002140c045411220503c4840c100b860a032848589082c0e50219100c0f1011490409090424010340a2500102d9001c5d04180020403e102c00a503942e8030710b4000c0703079542441c0d11800016800c907413a100001d00b140307030100a00e404180903551010b402c10f904814100722451078002406c811485604681d00b10380240c08002d05156104010000d0040a40050007221018800f043d905c0050340c4200200c580340b1082694008006605480026201400c04d06c0340d403414000400480d4025000386d0003107071030014001c8090740f0000e101010250300607442c0600c141401000c554400e00e940000341d000b5201c05012801801c24095200142481d44003c542d118040c0819034a00b503442e4511000b41d003081c403c11041c4100010115011596 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 359071555 1250 359070305 359070317
    0xd06091209081218061b0f0c0a0509130b070504080a0c0e090f07090f0902060f040e18031b0f0a08041d09070504090206040906030b06040c1e1b0c0e0105011e0f 70
    0x403181041c0c2d0035600f0740007a48140c011340703508651141c03000c03610402d00c9804480c4c5001c000d80360f500b00700000d0303021b0b53304244070242640c1c00000542082142c0350440e0582c10201d040a549031511894000c880004588a843d18142040108084c200283d0448080b601034000203001070f040302e5881d1190f103e80c00c643c0e600e801d038100000285601c8446002e4001c0d003103a64545280041200c16030051048100203c480c45c00261502d120021520201003514040c5190005a121602d140d80f030020000710b0702d005688007811604020840300b51220320030140d0381c2d02e403440d10601140305940743c21644004907400f800c1090450002c5402016103000f294009608004c41c00418414060b81c1c2002c800189041c901100344000702a42c01c2c40340c0021141800800350302001142c0025145d1201c0e81ca0201c20400121154050b001c08210b02480c0d1345000b03849080390321041651107141d845019040c2820005111a590200900d00c2103981d072800e4412413030b80c08000902c14102c10030741d1000c00503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 359072805 1250 359071555 359071567
    0x30902090610051b0303070212070c060c0606050d14010f110712050c0a050c09070509011e021903050706050f040203030f09010504170102090f09150d0609120908121806 74
    0x100900903130345400d1401c0d00841d4682c1d03a80a101c0d40d0782c0c0c810381d5084003501c14081c002200c1e111400488030700c2d5500c40c0018100f03d107000010340d01824450412148035880c0c40020846843d80006210410301461180318400a40c078501c2c1d084400309101c10a48509041040e40a52528002c032080660b00494051145070300300c004650038000c05003000d40398041d00801100744040081c04000340c0d50122a90402d548805006580d0f034070507840806d000c104400c0c0106c8900c5d13648190b11b0b8181c0710900580344075000c007041d407440034201744a04070003103100461210140143d42c850380e503209590880603052410306030002a641e008070301500048480004a00020b43d1141e001d89005003007800000c545070700111210b034080d4205c40110340c0144441003c010f02031034018505800b9005810b0707000352251200060011035583c51400f5240382e5250107000d40011000800c007400f8020560707540c1803076800c00b0211810320050006a5580d11428810820303412030182e90341030640e408031500c03560343d9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 359074055 1250 359072805 359072807
    0x906060504060c050703050d02030c1b2b080307030e0f01060608041b0302131a0a05010504121106031f09020705031b16030c0f0603090807081608030907060f030902090610 75
    0x1045c280c100414600510381c0c4290307603a03000400f420301e4030300900580d031503003c001340e032010801448012154898001510b8200b040c0305019801104810008049140e2260b9110701e41035030b2041d6203c00c000b90f0340c0c1c1c1d44e0440e924002c8c4a0340354050b20307182c002d000c8245407540040c0354040140018bc040f4809400e0803000c000d65501c06402141d000d410b4800402091410500425100c1c00c03410120404842070046460807640300c10580304140c440a00345400c007050b503074404940081c200d4649400c86032400441e9100c9000d5840f0380d0304108500c1c51031004105c81014500c2c203070b108a200c28014050b0500041c804015147d0ba403103031070704100e031142840f0903180ca0b00c03102c20006002503085410110900010900c00d4080d11011407810700c00d543c1d071302e0040f002c9a40408010b031001c4418001240062500e0006000312580340c04038150700002e50700c1c1c084e0380d54002e83d050146580141803c010890700b0041840e003034030309400c08000c3c03030b541d517004290000e80060905110721441688200e0391 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 359075305 1250 359074055 359074063
    0x181404110c0d050a111504080a020325020f010206130605040c1d2403210f0a0305040b480c0105010302033906070204020705010b04060906060504060c05 67
    0x1000108803414010002c0001d8110341c02502500e0005170160b1086031003c0000803042a104d64800545861790780d40c0d03d070700d002c1d40c00c825110303011030004100407000d80c01d41e060a14004900c522241c1c5405060b403040118034503000c0050360664100350200010900c0414400340c10a800020200c0e01c0d41c1c451409200320140340d004446a14040f030300d40407070302141c403080c03500c6070710300ca040306810308a840e000290210503102c0041d45a4050040ba80380341002c01c24061010003c07241c0d260401c40200344040164011402001c000303a40c450400042c00000302800e07070840440c502402915005c1040a0b0f01c0001c83c1c1d0141c500801c3c0d0300710076450b20350414040040b100e03044500f00c1e00c660305840460f01809080c4003e901c40c0c844c00352200c3c1c0c401c00c04e01d4958640440603d40312180d0f20812021083d0424403150583e002d0000c0c41046c01580311740c00100060340c481c000008a242500003004101d540d5030b0040c400c514600407007801540c0c0c0040844094480d5410075003403002c80c0d45451860 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 359076555 1250 359075305 359075317
    0x509070e180109020a170106090203090d1b1e1a15040b010207050a0b0d0b030d080708040c030510060510111015051003060501080a020702011b052b18140411 69
    0x480f203c070000401c8071b46180da444040340d4a00c000e02c0b04a680d040004142d01080d914145103030004a200e21026001e44000c0600c050305c11202c050721031840e00d0740f41b01c2c50f580201032018400d080d04582c1c1086200c99803074010116110b1100c0361030500c1c0302441c48031514000001d001d2552510445840e038020400280100340080c0200b40c0641c0391011103810b03801c828032602da15410100003200b90700d40880c007010f01c40314680e19208aa954200c08480400000e0425200b044100c40c0200115106000013511803400c5803001c550300b4644018009490451001c02e0104200e0312503030002ca05012444110030a03058501040d640390f20f4609a03100c50395a4015079000c0248000c0c00803258041e0866001c840007600c070310713400e551448085801d034800c420001b40022801104080480d40d541484050207000c1c40407603001001141410310400410381012406e001c07205040800290302850035000c150000800e1a48c07039240c6001d260074003081c491214400c036202c0200400f6a11640b00b030b580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 359077805 1250 359076555 359076559
    0xe0a050405010b152d0d090218270a030801060e040b180417040f03060f0b03030c0105100902211503070609030b0114010f030902010509040905060105040509070e18010902 75
    0x800f003041106810640d80c041826025100c805406400350301418001c0e17590152502e02c41d540c030f0640300003035a00c02825901812a0700031521226034030480900b0f5001441115020703030640400502201c0d211981c0703801459a50300d81c0c40b20000000190b0b12030003d0b8110340440c18007030002c0d039503c0c000a014151010700d003038202100245100e045210035128038092402444000c3c03030600a0b0203001c0b1036100e07902502024600080040000403c13030740c40900044c4c2080c10000318080700e800004d0440d0b002c00b0101c14141c4d11030b0180074241c0300b9194203800038030340b00400b107181c0a001c500400030130710b425031510034020030800050108000e40315070411152000741500c1070181c03100c501070089440c80c08180c036403427443d000204513521407042d04800d03100c058440c448141e606441c12006400203402c1281008010b0003d00215140c50280d00122445040508502c4d810182440106d8400814400c1c582d03100400800580d604070b803140307800407481210b0840d8001403c0304171b03001d440c03000c1d0029 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 359079055 1250 359077805 359077819
    0x80604061503020316050304020d031b0b0a0207030206090c0f01030905030405040207140d020d1b1406070509040f0209010905010c170d0e01200301140d051b0102060f010e0a050405010b 81
    0x1c192242e050340103511802c4105102d0545e100b8881040743c6078001120001d4011800503210004a4041d21071241401ca0b0242c010303261004550368a8903111043d1031500303589401085140070190144001d0364000124001040d07180788200000d1040f01003220858103141e0b4a80005040c08410300864025060152042d0340d0740d0f0709031030151091b4112082400041c024051102c210500c0410740400d0703a461961898466042c03140b241c1d51101d1441e504031501c9414914094440109101491056002c0d45901d901c410f19542030005a68100101c0394801d40b04101448440c0c0c1c010810700c00b41d500070300c1c040f00c0d00389003450240002c000e015803001141c400440c0041801005030040c64802d45a0002404071615403100c440f03a0f01c001d400030030380511052005210010b80e8551001141000401200c100500c6840c0c1604202ca0800c00e40d15410415402001c1560104449900081441881ca80640c5400e0703201101e1340d00503003500b195036103c20201c0c0901000350440c003200c0500912403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 359080305 1250 359079055 359079089
    0x30105090a031103030601050403030e062a0106170601030b130614010f090203370524090f04060902041b0903050d020102090102190503040b0a090e060901120308060406 74
    0x41e615418444110005060701e50310100c0341c940402568003998060f1151401d15040d079609a599003c3e0f0b1070290703003204c018040d00621003029a580607511240d194030340b0f04158601b560310f00b95040c070342241400c154000700b11604a20005107035411683c0103642c091907500e0ba0104c3d00c11307281507031300040c2105040505003650b42c03003d10780c4141240d0417400c003c044259250006020303400120b40c070540f001c4131400100700010240e0700003640c980c0c0040b171340c81000c0c4c00c03d42600c08444003550281c94600840084815882d0900e1050b000c2150840348088240391a8504821100c00100020045912410010215160b6400004141d0960b90f0307522040808041c00815640c9544400d698038412403009200d11801803007111402d94040c1e0181c4144c0500c0311505011590780c88003101e841c8410040020904082070103401c9950181d5600060640f03000004010301d01e01500c2180301d40c020381c1c0100300c8050300348a1010b51a5040c1803000c4655941c200140051103940e0003105400c80f00200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 359081555 1250 359080305 359080321
    0x30c16060c170402060304020904170406030b0f040204151b02060c0c0411090d030e1206070203030a06050a1d06180901020c1c0e13060816090e0d0509040209010e030105 74
    0x1a03a248909030b0b40d95a034800504424040a90081d10081d400c00340400205000d41000c4a10795841400354008129000e04181303d100c0d030394010f5200b100043d6a44003030449501d4224400302000e902141c0a5042c2070078141d2070880101c600060344144103020f03008501d009036061440043d00c1d001031401b503c07802e40311071903a19101504159072045142852060042d200402a038201c00c2001d000030f8074104075075030180c45407e080754903035910a4100c00e0b80001ca080400c03c561040c101580070355240c1c18040e10201c2a5403080c0c010a20541d0a44400d0040d03d60000560128107078200006181d900c1d020080341d1850b569181d980d00030b482c0c2c2000c12404440c1500100741e0784084204585012201080c01400342003400144000625038003980b03042d0f072030456050b604410070301d031001803481d0361200300d60310f0000f090090700071202c1000420400d04269100d4841c08400388001760a8481007540c005110b03210f41000b90748143d90204e1a078103035074464100c03500c00f0320380580200114140400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 359082805 1250 359081555 359081561
    0x200f1e070f0b06191206020909011401020d0804050c01050315090115091211040c09381c1104030218090f03070803070e0411070b01170a0206040b030c1606 68
    0x14040d02d801408a022070194104071300905010000800c240402609209401c1c6141d0040d600c29520243c0902c428503041da01c10382698001c140d00c0c06498103442c901c0d0300182c101780322402d040c02800f034a10308100204d0b40100718103000704400d00c1c0079940d9907100e011000021124102964100169034008a50004506500e01c414010b54451600080e0b8906810740c144048510080c21400c40e05200c007a2400c0c642c20010070140a03047c030b90401342c0c80706650302d1041100440c5040312044036500700da2080041c6036501c45200e0301d440c21440d040c134512502c50010170031000f61945039030700d40a0381c04210b031300301c20f507000b0f194000d080502c1d0b107500c0e1105419006090b0f401000b0780c02860b4001007a0b0100004486905a1091501e811a03580c4541035500c0300810741d141ea04181c0728400442c0c00d484170f000500c00325219044800040d4101074800e40c40b080665038000179540305c1c1d105600565980b5098404464040f1600741d45d0741d0311313015004d55500a110b00045032800c406d020b1070400025030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 359084055 1250 359082805 359082833
    0x30702070602070803310305120406120b030a140f010f091a01060909050c16030c060c0306050303040302040207060b0607080c06060f0117040501060e0a0f200f1e07 72
    0x341c01c84070764a8549110381d45902c030388004006c174503813007544815030008030a400f241c2c0c13400e034100342507003907903607921518100001d0390018601020006424004075403c20107103180441c1c0900100800d14240c008640d03580c0800c04054001c0144400499030300d00200b0232412000c1601c8004e202c0c070510810244040d204110b011224022002141842c00d01000300d02d41c109d618a655500342c8501c1e06041f00300a20307000d840e07111251402c00807000c0c881990082e09540510a564048074040d40d030802e101142d030b41d060b08600b00350400b482007140e40c1d03000094900b43c0381c0460f001641c4820f05c1c81c1a5009222090311150400008188002405001006081426403540a0341c185a461004100c400c080080c600341c0800c04500e4141100140111850791041c41000001001a01e41c5850400010125540a00b043d107454000d0000c034040e014010300d52a04e13801e502400080104030590500960aca403042e50180843c12040071b0030011140d4400c03c9940102e50366900c028181246000070807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 359085305 1250 359084055 359084057
    0x30801050409050303010e0c040f0f030b060301050621010f1a090a060605030a0c0302120103060209040c11060708040f0b040f0b01140f150702060d06051002060c0d0513080307020706 80
    0x10000200c90419000d001c1025612102442c81c43e82413817080c2145c2203000d01050402c0d0414070000c2001e203a1020b0305070250030142c4003404414a0351608100d1100300403e0366000e82d0412080c80416141c00c41580c1c42845000200fa06882c540310041d40100903620362404d800741031803002e1a6540d0402d00d219150041a246201141e45a042070020703540b00313100303610001d6400c00000e200307150b855009529041c120300e805850240d1414403083c03d01c90a030405d6070002c2e800540606035180a10fe2034104d4242c5040c05411094500b0b2038130740f1070000600f000144140840040c00b0001120760b02e080c21039202c0401e08c2c850900d810705c0d400c00110304008640d80480c66001141d029900801068000b0004041c0364548220400b406601151b5422100d0f0408061204800503a5540090950fa50343c45100090aa241004002200048400c54010340d013001051000c1c254800044481c0407030300300c10201311a101c0900c2104040da002e88c000d085020007006020003950b000c545a803c503442 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 359086555 1250 359085305 359085317
    0x4141807030c110712020418050a0f02041122120201050702270a0e0106140f040c0e0409080c060a060f0e0601020705060703030b090c0301290d090311120405060301030f0f060608070303 81
    0x21000410102402340c14000c2c2550307111168a500045070387c40c007000f00510140c00481c02114103540c5500c2e40c0c0101da0500125410f880c00200560b00d24400c15004041948400c03a00d28940d4002a01320700c1074505c003038040d075900c00030040b01c1c1e1903643c040e8061040f220880c58051804803100e0005100345081c00306035508144c2e000a1100c40c0c1100043d00d401c008043c2d0303d102c0907501c1004010103000c5e0b2048280040030703038407100e80ea40390322400d40c2150040c42503e81c0d4142000c001800e01c280200044802031a10105200441819010a040c2c0e090b05085007001d0321100d00503440e20151358445580100c00107624010983d1681000307a40d65016941d0070f0300d0b42c0719806222200d00090050100c0c2100030945c03e60b4038000780140c1000041103442c005d20701141c10000c002562141e40301600400c03a507a00c4501c91483c1000f4044003090a0540382d0b007031609040c0003542a200622001c0c2051742030321154024844040d50342e0107030039400841000b41d02d58610032130f41c139528107110a07030100300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 359087805 1250 359086555 359086571
    0x70f030216050901050f04090c03060e0a1a09060414031213060507030b0105091903050708060925140418060606030e032a07080a03030204141807030c1107120204 71
    0x40c810382c0f4a042c0c81c80203209040800c000c20070f200051030f4808041d1030307602c840400000480e10500c00c46601c2c1864030064001d001481c1003505520348010300e4400d1441c00c0034100801041d020804a4000745d10603542030107803a23207110451650041138001e0b00f40c0511030080c41640304042a8400d2040d20801c13050105a41d0b11601b43d085070308124286010504c00c00807501d02e80b50594290b4241d10000541d1411140c59403070301840c0034901c0d002031030380354440360621003100790400983c0d50071161000408505402400c100348030103502e214061a640001410084a82e9a500b01400b20310018101c800d00c107190381840d2024118521508000c285010b214102c0310001000300c414001e41e600880b02c402001402c4461804844098a47e0b02e0044100120300040c003402035014045c0a60307005605d807402c0442028103041c5444129200c0c480c607800030f00d0403d540400030390b03114506080004910381c80304400e440322031114560100c140240500440c0e07841d801d07100310602e940241c8003007200103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 359089055 1250 359087805 359087809
    0x40816050f030615120a0b01080a022110050c1b1f0c05180102030405030d0816050316110111040e3108070516060206040302060705030106170606070f03021605 70
    0xa1415520407454103504200fa0415092081d0b1700904140d03a4411104d030f005180e29a805194400e07000441181c00491454040d8900101c07008485100380021500328060b0007000c42e580c01c0340003031252180f912800080c21b80a86a415100744150300081c1350b03860008060384503111075075601c03541030b0261724181c0c0c0e075105420313842443c101c44407a4840601d010a06012800070200e60100d481c118802004007050f961002d00500301d402d40d854031209042e003420b100341da00281d001615281040414010040b60310809d10040c9100c048504108101300030720310803280508880300c00c102e00040c001400240700312054001c944641e42245001707440500a01300400001049014031b1300003911a52240042100c1000800400303200d1001c440480d40b0a180c4110710825990019025030040010841030613014441140d0062035490686d10311b43c1440c00c060a01d143c242c000040d203c410341700094450b100d0200b140c040c50b804c0301c086a404a66807074021742c0c910480c084d010001200e60030000f428 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 359090305 1250 359089055 359089063
    0x180e0117010606181e0b070b0115140306010e0109030c26010b06120a02130906060f0e03060a0b060f03090309130b1008150a14151206100203040816050f03 68
    0x200c208461200440d498968032034055403c81d8490b4400c48017011000900c2c000e11801003620030b100c1d242001e220761425502259641c010b0b0a00301c01c0c0407086c5444011152032404599020200b4285015031202c07180c0101d80e00042074100404508802d04086130000c072064101003800060246a003204051050640c2a40c003002c240a4000006115a5542154142d9090f520981e00f0000504204101c50041e9100809a004032401680c0b15400d014040e0b02a030400f40c030f0000741c141140864400d0300400d80c1c8420040460305020b5444003200402e0b078404080f625141d072444400c80d180c0c105004081c0d12544080d203003511481100214030454584c0f8094100841001082c452250f10000000d40748018000d11100141004559209031607503111858000341c07450000714100a4607001c14031031642061481400c0e8101d061124140707031112641210f50205e01540c24100078181c00e00141e103580900d41154081e8051301c1100c250180507803012208680d01110010002c6001009060315 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 359091555 1250 359090305 359090327
    0xd0c02060415050c0d0c0c05040c080105131d030306030609150403051602041e060506040b07290f09071a09041e0207030c0b0a0209030303010303180e0117010606 71
    0x2002040c0020000e40e26031000201520300c82d410308902d0101500c014904154144564502041c24190781c4010b00c04031204c00009030800380c030200422030340c40001401078001403080c50b110704100010100029190341103079459507520307101590100e4401c042552a904200d540314024807440c00000d03821100040d035013050040b141c0c294190b0740c42d10b0f1011201503020f0710800080b05020604040103850710710840300710b0842d00701c40c09103011030380034101c0c10b44205600c440d1082105120038042d814142d0200c5250710740c0318000f45081c0c0c140098000000300c4d800c8503451030780c3d100c50800c140440e4414001d84a400e07030f10f003951001e5499000c04030000b010024a880030780c00c18041d280319810143e0220f580102003040000890f5007088080c81603a002c06800c500027020028803204001e41d4240c4035820069080040d420246400b021907680e020510000d001c11084005601c800707440f40b8003c00c058104090244155030b1078400040e01032204c680c50f540d0b00d6107041000100c0c14816060882 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 359092805 1250 359091555 359091559
    0x4110d24031a04051f1a0307060905010c0f0b1906120804140102071502010c022406190302060f040e060f0102060117150109150b040605030c0d0e0d0509030d0c02 71
    0x24440100c0d01c80b904008004004840728440c0718141c43c0780c1c000c00e462100300064017490106650078405020303222490110741090003a813115070706111554202012070191042031800348110309150400350f610010a00e0081d02e00500907082c805440c540b01c0320030200050740d040501650340d0700d41d07a4184041d50b2840107010684240b006000d07450004503460945030381441124400c1d616040031030101c40380281c0040142c4c0d980d1181d03541c0c40c0c0c0c041c001d10945070300c12001c400000d92030030903000c8089001170029218400420003954902c010308100030156801804a0f0344903280444c410a0319407190181c103940005020010382a4540444040f00e41001a805410141d10b00364822400710440a0007143c1801031010491032440f000030030500070f262059020902110704032031449a6586500003000650007004180720f0140c004003100d420420408000380e0321a0051a080001d0035004c803013031880d0040003000b203c8158404040c000c080740c103d0540349000030801064400c40700030380c0025 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 359094055 1250 359092805 359092823
    0x1b020604090c0c0b09010c020f06010b34050a03080f10050609030c03030d0b1005070519140a110909160e0405010b03060c0c011401120f0204110d2403 66
    0x1c003484081d42c000e114407403070a040070009011a540c1d400000c400803201c9262070380d07440a10020199040010a07171171080c00001c0c004650616510500c00d100d060118011034814140000d618510001d400b10f042d41d005c9122480b224141c5400d0343c40e0484290b01ba00040d00c81e402085040700d54a10359401510b03403403000d1384003c2c03622043c4030305a044011000e5250041c215585603988061009203880c1c102c0d1200007802c02842c6080002018002c50b00d0001c02c2410b02940d00007410000e042c011003000401c00483c420300c00d2034803100201c400048080140900c05550702080400c03400c6e0382d50014122040e015564552940c9941d1f01c0c44812684c1c00258000d0041221a0340343e10550703001030140b400814600303101340200e8a0403206658040060200182240c4503030b60030b00c03030440c1c121000d110451255143c0010300900310710120000e8102c3c500507007110115a52980b100807800a640e00003030b03d6000f5596090b004003c1c202818000441e50885840009541c0340301c442501d512800300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 359095305 1250 359094055 359094059
    0x1c030e03220b07050606090106080f1b07020a0b0d060b19030207110a0f0e130b04140f01060b0403060b09070206010b0f0903010f0c02010c030504050c1201020d05090d1b020604 77
    0x980c014072400e0a018901000c80004101c03060440e0003440700c14040c6004041d10300b010340c03d0100b40c1d08140e01c180c040151035014005c8000604801c15002450104001d2032860680e1058000e40f090a000950208007100002004181e500181c020000c088070f0410646a43d00800c0665100b84d41e001c0003950423107401686207034045c0d8050b0041601620030405a4810300000c1544040141c100c1010072162601c100510101002016403084410703440760700340011641c0d40c4006210150004082d0341c1040750140c80c1b400d0070010810400b4000c0003e1100b1580d5007158050780d80280000d0f140e503810315000001505082140c9401002c1c168000c001907031038282c82c030f07880c1d41004c44144201d45081202404e1550240100c81510302904000039003844140800303403c42d42001d9504007031504120400001c41d0000c5002c00c0400c105640002c8030300d0a02a201d80240708054541e40e626192400307100d44c02000050540d0783c01d41c540c071801c0c0150315000420006182d07911009520050412013 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 359096555 1250 359095305 359095327
    0xe060115051602040606030e190515130c090b0102120f03060d02030a0b010f0e1807170a0605010e0709210303020d09080703120b010306032a0e0106021c030e03 70
    0x20b08144031800760302c031541c040603800a001d480c1d10780d01c03d1000984030340c205101040103200c00711154409940c05008c0c4800c035540c0310307103924141e0392000c5401c0d0100c00048801c940d4001d010b21503a8000c030030380b010301d464442000007880011055401413084a2040c14161311510440d04000c8000e4055800d42da140303000c110010220110498140c000d0300005400a2071007510a806407444402140d811810035580740d0300c9900003030902070f05603410024100d040d800424100709590150044007040030001319024503001c1040300040400303140000000d0719101e012100c1e40519410745d0b485820a40d100c141c00040480c540c0182c0e00d6001000742c00740068001e600810b208903402c480810b00400c262990320094002070700c00d4010404110021440e002e6901c20001d203c402400c0030408079003561104043d0410441ca8100e86001c03580500410009140010000b0041200045020742e11040300a4894400100c1e1400b400346003901c0010150081c01403c1244421030700440c241040480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 359097805 1250 359096555 359096557
    0x30c0e040e032a0d140d200c100e1c080603011506121d0307150207050703140705010305041505100503010c050c06013512070303050106030e06011505 66
    0x2907488001d1004200014120742401c9012007600f4a0041280c1c1040160700980d05003540c150740c43c420001d550091070f41c02151034040c1c0390442071281d0005540f0070203d0366003403500018071002c09085c00c04680b1000c840030010703503482604201c034010321003503100c5203d06990b442a20015103050810645010741e1a200b0000c0036405603000b80040b40710b20218141e010500c000383c02030700c001000780c000003030f4003485400307150001a080c44044000e0454078078440c2c1c881c02140c0005104200342030b0f100c461800b1517015a644241c0100c00d40c0d4103150b03a85045540f94040c121381040a0080000c0010341e903006c0d11580d4420307a003201c0404180d446902c00000205401898200980003590010032070b41c60911800d201100c0903102c0e140d484034081c02c4149031180c1640f00c0c242c03c1e00ca580c411160f110070300581d41c0218001400c05500c5030380b00d6001c542003d15a00701e07417a0313810b0041407a070103060341a08030a049a00a44040190360940c4400c1070700c0703c0c8240107640c00040d60429807002248104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 359099055 1250 359097805 359097821
    0x80c0106051c1211030d020a0905030f0a12050c070504060b0a14040806010302040b040f0603050c131122081902090a02090d0308060a08030c010213241409040f051006030c0e04 77
    0x240c0c1d1a1506d20300c1c05404036041502e400380040c0741c071f0a040c040741c102005807c900491040003015005410741e60410741618001d10413042117400b00300c1d20302d43c0c4401c00c0a0406420001c00a02660b52240f00d100003a130405078074280016404550f80ca08030301c849007240c081d81d03030032806802240c1c21502488041c0801d804201d40160340c0e0b10444001d107200388516000745101d00d02501a030b510300d01c100100d00915090094541d4a0250340c0542030340c1c000d08942e1401d0b200b24100c2d10a407401e9844081e40e03642c941c0004094095503c440e90550061820f4032111442102c9003031642d199088083e01302e010740058150040103100401c00400c3c0900240e941c8110700410100b105922050018155002035026409a070340205901c01500c0c000210038015040c028120880d03400b86140b07040002070051101c0c4184035000040e00c100d03030352240c121404202c015200b44040c0d02111300da000248011501007000c2c10907140089801e92003800b4034601d004071595481e1181600d01c0401009220b50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 359100305 1250 359099055 359099087
    0x903031e140309060906220b040503190201061508010b090d08091309060c020607080705030a060b030405150a0c0c0b0907031406150d020a150903080c0106051c12 71
    0x149614034003103000c041c0194810724a000c0903000c1340c180554010b103025005800f140a060540303488a121703000382c56541402c0c58000804001f140c6450418506610580009030302240301614a205490307015002282250150003c08201c8011003404445249080c003a0140b00c0701c040100c9480d51030300c04d107094803950040c91982d00e42190309000858108a42e8410280d154a5070700385414090148140c83d281c84050018200c64903101e4002062024000c14040a00002001051a00d07000b035009002030082d00381060f07680c2c01c2c903040059031441c410b8503000c80f0030310560000d01c10090f14000c80c8404001600c40852241d816540c000b642d80000340001014403d000300080861400846030800d0b00154000d4611401c059545148031301d0414a524010b0103003800c9407005031510880751080b10608042400380d40902d58044034030034038031351001c0c25442000c24a80d4440038190f01c400c040b035078115036089140160b918072681220744440092f08095494080702801c034054280364a95500c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 359101555 1250 359100305 359100317
    0xa0b0f0c0d200c0706120b030c100c0b1330030207050307050d0c0212070e0403030209270702010b0d153204111c030f050f040e0a0c0903031e 62
    0x10744a1055403d4100c074500e040aa40000320800c03060f50007661110301b08280c01410b0009011080c04250b0340c5451490f924015203102e40241c510511402c05204c0e1181d002c50350400b58203101c080880c0c2e00d150360f0000c7d02d40d0700440d4070302d40c1c08614141c1c6840703c90f40790034004407101c00f026800340d0003074001480a945a01041008030f00190051100798401403880d2685100b840703040c018000d400e02051810510b50380441028008040380c8203100307500591625015944d0a14580410003518081d8100c0c40540c8200040c600c030b01e900c80c2c20481c466030042e80208405800501000003e2a40006c05841e0901c16401861508440c0d040100d04880140ca46021200100d185c040a08801901e410b4130b00c06c0b01c0140001c110420f40501c100c034808581c003403501c0c1d888080c106812910200e00805014205401d1110103004100b502c080314181b2030000e8407140e469400c2401c10804680462200d0b182004187c8005d000f072500ca015290541d66040b140545c080601c0c101c1b11071140c810090000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 359102805 1250 359101555 359101601
    0x10e0d03300207061b020303040215160b0f1308040e10080a06090203120a080f04031b0606080d05071208090a1403221203030f0209120a0b0f0c0d 64
    0x20005044440110010301c00507a91495410424202c0d0503241903c5000714a4044034000a40c0c000705903a040790701103440d1052000710044004031881082c0440b4490030006a031030081c02030305c0000904c580344920310b2800c10b56803050380c01518034801d600240404028802880340700400079885920503000390704171140e140c071440c0c02460041e0f104400c0314001d85032401801181024045481c151011204030390900c07140b80d1010b000303450f004141655541c0b0620020301454820100d0101203a00b81100d0300d1500070505002002c1c1146002c1c200046c40340480300190b192180044441c5280c1000b41080308404881080b00c1e110000b80c0101c1c501e21607079040c00080707404408503c420710308402c0216550a0411941c0c400c11014200c2400161643e0b2030801800b074281260000e00780e45858001026082c02c04000001e00071540c200d504501e00380e4100308451000540711002a015204c03c4400390740d4100c3e030b41b02c0900200c401b01d00c030000511000281c0700e844e03084000c1e00c4440313240e8245001d0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 359104055 1250 359102805 359102867
    0x4060c0c0801090c15020c01080105010f140a0504090b0a0506162a0305150403050901050901170c0307080903090a09050903090d0804050a060c050601030206030709030b040605070e010e0d03 83
    0x1400b2900a4419900d0320f1420855200303003800045c0c10800a001903c805521742c400a4040c07401445982c0c10301c980f42000c0c923143c9202d16a403980704c588003c140c545545003010000c03c6a0401c0c080c4c06c202c90700d8025594641d1400024510072a0300c000c0040d4508620380559900c420103110084681b0b0048800c00c17040d8850341d00e42c01104000c5005403c0303c40303183d4100a4a000d0200e0f680c402072105400c213001c0807a511a088035000082800d04070381d903505200048540d2011183e08c10426403a8038144123500c140f400003940141d841e50340e02881d40d1a0b0040f26912031040350700302548440c0414080001d0211500304603803040114040d41c0c00d280347c003400300d000000046003c58100000107010300c441c0c0b070220030340e0010f4481803400300d50003041940c40594624060101034070a060200015007000e10400b90040078503440038413140c4600f081e14021019150907280400491500c0741c04907403a510614400b0001d4000810603c08110240c03020348151400030f81907822901d200c00441d07141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 359105305 1250 359104055 359104061
    0x40206090d1a13230705041a060f07050d090f0e0a0221010806182107020a150f171801180b0405060a020a0906050a0c060504060f050c03070504060c0c0801 68
    0x51520282e22000c11a40340340004451039121080010f8081da050f002c03842c2c084c009250820341b601a03500140b9081c2401d00301100180c2403101941c41480020101d040d89110005440100d1040c42182c09601c104a400d451400d060300800310881c01c0c09004101c204480c418140d000700b60210018603040030315041002807600c107800f03441d2028000004000e0f20400308141075011410600d0609030201c181000d03074440030449081c07055140380110041000c00311b60b0032100c030340b98000c100e260119035503000c0c020180d4400c200749003c03d200c0c419500030b46005440b1601c28260504c0ba00000b0758070220500c4901e5480c0180703d95541d030352078044101e50070301c20701290810300502c05910f8a260602d88149841c0c002001e4041941c010b010000903603070003420b004190382860411945030001d2540c00c0701d4000910202a1201d4180401d0100b8082c1c1680406050050402c00b440640d540c071a1041c8948402e962071400200100410410b0500c039004483c0010f1050f1070f000c44a0303a441100c0303070039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 359106555 1250 359105305 359105311
    0x1021b01050d09111f0507032717010501140d03110109020901081f0b0f100e0904140d030c1b030e030105090102041503050720030d0e0c0307080303040206090d1a 71
    0x54504410f001405171904100350742403510007000c8a80340c090a035200400030f0144440090504c4481c0b42c290341c0030035003c1d84420f42d02500c00700c030b00c0030181c3d9908001e4107640045c1b6000d00719441c001c004100400c0c48003200110302800343c0080319403905c0b6a0112204054a10080070a560310300160005aa800014500824048001b00b001900c11200e0100d00b603503039076402c000700d0700d08a40905075803500301e5414040301003101c0c00950b4562010040d01d903012002401030f44968400104410064a40d114160302508802100e4051142010540807170b101e80ca0b00c10085588a2108100329247c0c90000110500ca45030034011070a610300032030309642090f80d8610b44d036500428144400c152802c034000003800b03030340303400d001c2400e080304050028801d000a1000c0101c881000d100102c0c8108103c030032209086e5000c120242d027034183c89466140c00029035100303014007040040e510400206490045070001c00b007a1403c1c81200c100301050510120440309194006411011003000c000d40c544 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 359107805 1250 359106555 359106563
    0x50631060306081b0d020a0812071208060901090f020c0703050a05060c030c0304060c0c080d060501090807030b0f130209010608060f04060b2b1d0f01060501021b01050d09 75
    0x4201800c0400141c2a1541078104182951101c2c1e010003081c500f46000c2040b040d800d485000000001d4004520303800c100da0043e440a1291a007881d56051490300240342e07a41c002c2001000790810b406e030481c0c3e0380031300341ca01e19400313400c520042c032010416500851150250719001450b01100c00c422904051203503100350342c5038001043c44810f001e8140078450388018040301c0a881c1d845c000c0340b012480c1c00007a1000e0b11300341c0d43e404440d40003405800c1c080b0540b50010070aa0300c0c0d1715205210b00141000340140c6000515200000904100001c4c8810940754004400502c5a03542400000e00c0c03100185020180891a2012030168580504490217000c41d6038401026240583c18440d00b03510320b000c600d0160f480d012007000262030001c10750361260100301602c4a140304111020103800700d081800c060b0706240201e0162070903000003043c038003002400e0a4038400160303810b01700d00300c503041d00c1086e003d81c0208000c9000360190020309030006c2c0301414041e04290b0200081000c0301c5c45084212 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 359109055 1250 359107805 359107897
    0xa1d030315040207080f030c04030b150f0102010e0a02370905090304140904060f020a0320090f060309011103010f050102010e0f07090f140403020d080106020c0303040506 75
    0x22101054100d4500d250705441c20751070100103a039a001d40788100340c1000520f00e0084003081e042c0340035004907030040d5048510341c615820062000d0030302e00200070259100c0d40d82c1c50b02003a4254010300690750b8000d47c20001d4120f030b44058080c80b40d40004203544405882409142c1c0c081051110301c00740e0340695900d45840c11505213500c14084600151039050291f005020401041c40456140303068400306541c0401c1a40b11880d250002c1c2000b070031003114880c0042103805403c1d5140d44140c81800c20313031080d03a0307108510040035942c030710417520301940103106403005412030304007800195000b0f54000f00018004500111540c034a800a800c074280c445c1c0f055408001540c0c0c240605448803046101401401c4036440c942c0c0e80d103000c2131080d006c80688405080c118070f01240d0202030098030807030315801c0c01e03d01072500035200c640c484002e20101e4091000031a038280b000540d200f510b2009401140303850b040c01c08000c02908420440540007490504502e03085030f040e400709290050100185e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 359110305 1250 359109055 359109061
    0xd0e0604020118050a090c1b110307060e0a060503180d020a17180906030102090405010e07110f03040618170a0303050108030c07290403030504210201020d080a1d0303 73
    0x50004128100fa050905101a420301180d560105c44408075099024005440700e40317440d09648001d001c5401e03028004d0810044001d200500603141c400601c22030a0345e0049403180415a078275441380b1915a0840d0704081d0a10a00740104000d58201460100e20741d0311071065070000780f074443c0f400904001604420500010002445100d44040c0c510740151800c0410320703e00c403080b04003100813a600c02c1c80c1c1800400d07030540742903040710074900028006015541c2c40e02c403102a2405c1c00d450400c0040c80a0310040441c90000c0317841240700c1c7d41540034515042c034010003140d98407040380328100c2040340400f00088001c568000d10564400c45005070403001c01c2e500300501201c034164802c41c800c4d00b080194501141c40806d800065400c06001210107203445240c2100105c0402121500d0b41740001c0c0100134560082c021700116182141c00c0301941d03001c000c00000100c00c0e600c1c02801350703210030b2078070501500072003c0c2d582c414554000003500014880c2486c0070880c92102c1408150000814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 359111555 1250 359110305 359110307
    0x101d0703110301060314011401090507272303071202030304030609080d09061a01050c1504051006120c05030102040608010e06030a0c0b07020f10020316031206060e010e04050408041a0d0e06040201 86
    0x2002d030041104ac1c0041165142c8184098208c0d52800c0c0680c4000c030341300040d113820000003400c46024091080011075510200e0224118034000c425031a8030910401600151410060600300c41703c44d8042d026508251030b503500e01c03000e410b007944c049400c0c0d0014880406000401d12805045501510000c1000680c21050f20000c900800145040100070002441054000038401c03403c8440c00070000103035651400c09500744488840024000740c20f01c0d0b00080c0241b080101c000c803080c01145480821603071102010708174403640c442c0e0804581c0802c01003240c034424140f0701da40034202806a5010001c0d41c0d4402c1c0003485140c01158203000081142c40640c18141612250071a0948000c01560b0240e000030b5940d0103903445820080c2e195003400700405110b0125122401c0f0718241c1480815201c00c400f0f84403440b2890381a0015041c44400051441e01d401298000c0340c0241c4490720782400c2200320320390581c60801d680c1442d00100080450314540b44030b070780c2d404800c24014106c80e040a03c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 359112805 1250 359111555 359111591
    0x160b041d1b0f18042c011104030c060210140c0705100609021305030109150e0a0507121a070c0210020304030503160c08030403170714030c101d070311030106031401 72
    0x10307407280a05d20304003010f0380c41c190241c281c1034050520425809110701e01c20301c09001d426100071204a400300481c0000070071030480d9403039080e100250295040b007244105824100d410018940700c12100000200f44804005002040c515008506942d0030700131117582c400c03d540f031682c0103028040c1d000901614460803854440c0c050071040b030090203480c3c01a200d420f043c04c804030020305855659452103050503820480da2101e603602000303036070841d41d881095448031107901c102600c81e9926040d1050781c01c41d071f42c0340e01d078810b1903181c031420b136621b02a409000481c40d04450703c00942c0f008002c04404a402000036101b01c084c1401d01e0f541c1c803001490045500c100990100b0070380d503c2030005100107800d8804c62151070102d40c400795160100c90030304560341d82050351101040e000002d0001341c03000340464560101041000c043c001440340741c030503108004110b01ca0034200d030030500c01400000d450221100440310004d0003c15815101d860701d0107058490703000c0403402d0b0f40d9180a0004508680c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 359114055 1250 359112805 359112847
    0x4120e04090503031f180f0c090501081902040b1303050c0a0e0f0a06030f20090705070224040807060f17010b0c010914160b041d1b0f 59
    0x51030a00c4420325070b0380d402d0b03035074000980324101000c00210408000c0c000b03520a0001071074005080103191a090880313500501080103c40354940c240301032100c1c201d0003519440308665040c4c1d41c0c003c2654584424081c403070341008800d414039408010000340320302e800c00544810010a41006411491494030038030f003c3e14400e100d40200040c042c00c0050070954103045600115444c1c0401460340c070076190300014041e076007008000019581080060084e404e0b82c2d80340300e400504241c00d03045c01078010010040d50841e140d07000501e00b04212401404e0640140d2110034000400114100450008804941143c2c202c090190f03c40d500c00c00507154010984e1182c803005041410303202c1420301e0710000080050055a402c2000000c1c4602c00a80944c40303c080c4a400a40c0b5a10500d05100d982e6151805201b0001000504800c0030643e800f039207080f0760440f05081001f01803513441c00d584040c41e074801001214507003401ca0004501084000c020070b040c000f00c41507240d891a810000c480107103459 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 359115305 1250 359114055 359114059
    0xc1508010503010606022505031507030e010902030d1d03010615021c0c12180b040f0e010e16140301060c030809061501030b1314010302090c03090703020103090c03060504120e 77
    0x800c0007003000395001f0132011180341004950910f0707100d0301c01d01290b02d070840c0d60040b40c051040c07030304602207100d1542610380225804d50b0240400301c034444165098400003000a50300d50040e0540ea191140201a6640b180c005081c280190007040740010303003103c101c1d5001c607101031f54132030700101c91990501110480b01c035402c1501c10000c12910000b0400d49601d2401807082006610b40525903000c0c2040070080c01c0c25007510040b89458580020082c1c0091140789000380c000400030800030901c821090688182e403055104917550403160b107950510640c01c0106002150300184142d840070001540a454541c4558021440626005011200c0144405420340205090049551203200c101c0040d00c07007440c020405941030800209009034440040b0b0f815072416160f6105104041c12140c102e030700841d4680b001e0b5035001c098407441d00c022296020190003600d0288019030290380190907007801644a000d903162030340e4900741240c600781c5081d551100240404003690394054030b030661480e01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 359116555 1250 359115305 359115311
    0x2a140c03070305060f1008030a0c020406080a0305120c040f030b06010e04050f040b09120c0a14070303140a090b0a0305180708030714010b1008090601050a120303020d090c150801050301 81
    0x2d56201c0940b60f1001600d24403c83c0c01c004040341031340c079030324110340041c0c031036081a039540310181200030b0310110414208901850038031030001400c1c807011802c50701c0d25801d61103c3d80703800741d0a54005074000b0014100707280240e081c040895405915a03100d406907119900c845078070706000700090441180041307110300c1035043c00108010010f5011020fa00320760b01c00280412074950040c2c060034026030403010180c0380c20104a02d41c0480e0000303a4080e00501800000c22001c00d051307845a104c003000d000260226480b069041070303a40620b00141480501440c1892249480740e1110509900810100b030002e0b0700e030360501a00700d40d08014200c18030f0b144001400010b20700f044041d00c074001c1c0d1801900c41900210f41081c480c0084d0081c0c401c90300d0062022030b540c0003c14015090210035203e20029210b040008038090809000d03e200750303081a0031400c02c00607140c0c0d00310007079400120004031054484021000090000c407032035001c3d0041d0541c1d8485001c40d20b0000784060b0050380040e1190381 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 359117805 1250 359116555 359116559
    0x803070327020d020102100c02070501080901050907061115071d0109080d0e01030e030c0102040e0a060b040e070c0b0f090120040e070203120a0b0a060e0f012a140c0307 74
    0x100030108841c16a055804111079800c50006034204080d0b2540040307c01c1c280720f023170b115940c2d0100d003a1040d55000d8907020041d882d03141301d250032150b0480d0b03d0982ca038482c0805010250181260340c1340c0c241d101e0220381584150741c440740400507040c0e941401150208121841040c0c2102124083e100c1c20311b40040160f2038081d82c6699441c0d080b0b40741c414802c2c0411280c00907446604421110240c0900b1207603a514071103607043c001e60140c411003295000f200b0200c0c1d00551503018140440d404c842c0c242d400c1605050400048030009032040701803005403500003000415015045205004802040201345040b0581c42c0c00c1da040c020300c60315030310405035245103452101030613038003522000341c04043c8940e03856005901d0f500c1880007020100121500700865000c8030380080a20300030560354500c1492f900e0030309a40c4442e502d0b4103a0f5104040302502080e0b54803a041720078400e0345092010b5038100b183e079401315044094400648400800aa220b245201c082000c000a59401c0d0001d00d40c0d64 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 359119055 1250 359117805 359117861
    0x121523032121100b0f091f020c031203042d030207090612030c14010204180f1103040203100b01051303060b030601060c1e0f0816030816140c030409060308030703 71
    0x101c018020400904000300b200c000c3c5410305c0042c1e9010b4140608901002088002e44801c01441c440c11000103100b05490300400c1d05000c030321514812400c142050840d180ca42d102100c141100702c121403800131a0441a03048038000c4030200c4218001c1d00604481e03801d0104107015035505800092036095402e907403500284c3c2c003507150010150480448200c885200a1090280c4119402240d0a04100310840401c0b07010780d10641c1680031000080200850707034680c43c4144d000c100c8001c6c0d071603004050103000e01160f54000d4a509101450070b00e15000d20710300d40b4041c5081503041030340c20f0f0f95103680d0000a03050410080d80581800c0c01e0060035030100341d87e400035041c0c0300d4199190740010b403102101000400c1d00406035150303120300105c1e00c40d00004944c100c0100710810580004540f0700100302000e80d2462001c4004101340c0c0c070f091210440c2c200c1681c03d07910044c41041244020480021303181a24130400024621a40c1182d41d02e062014000742070300c504c160005000789a00044021035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 359120305 1250 359119055 359119081
    0x5030304051207030203010519051302180411031002041d04020a0501050f0403240b09061f090308070b01050a06050a02030304020f1807121523032121 66
    0xc90701118020010b4401008080c1007800341d0744025019800c0c9030a01002800340d01001c0c20004042108000980c1c0d0891445402a45994040d410800048a5540d28074011100543c081d00407958100e0820030840400d16201020045103441a8080b60511107031200c501d40540c1c6409c2c80c0410180341c101500003030782d15074103403141506111000030a40305410309101039600554100d865003072001d0001c29981401c03080c84a090401905d800ca10388510320b4200c2e10b01d07000302da000e011705c0000108100008aa07140c0c07591201c00740711040a0020000e41134400504e081880383c903118206501d0b2109011303142e641a0002414000309120080146600000b902e030f0198040726440380341d40c40303034004c17400c0c40c403606130f00301d403018522000c100c105508a42d039106000b182d10020045051a001802c00c540d03454012004029425007070400ba540b0041c800c1404950000c0a44401036034403850040c00312250200c024100d880841d49500c200051030710041c050b500504080107510741020080d40e9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 359121555 1250 359120305 359120309
    0x1150e0615070519030306090b0402160b0c0c120702040e0d12020f0f0a031a010311030a0b0613140a0f03031e2345030a020d080306040c03050105030304 67
    0x5a80200b091010b12100300991084012100020b448220003801d004000d40384501a0313181c02400d02c00c102c00d41d800c00c2c0c400c80309614075102980c401c080c03081c3c1c2d9030940c960014284448030401802000300030001031103421601c100c80d081075903658185106000c00d41b070b03c0801080054110120048010340c2224610103d2084040010395031607410010302085e009400c2d0b49240d80001040c8460040d40580c85660054854500f051015101500440954102c42e000000d02c402c2400850390b10219900040901000200040d04201d2014000c50003a1103641c4130b8003180100b10042032240c213042100b8005003800b51582d408050854502602c0d0b40c800303c5200c96040036002c198000d00e4420310000c0d803040c1c410b140000e0800c0000d88110142d8001d1141508080c40305c11a441c05c01909401044a01501188a110121540e0660f520a0400e0a5500d8040c02240640070046e44c1d00d20100040d2071080748096280c0c00c0460500c411a20203a07105800c0c186008014841980c000042d101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 359122805 1250 359121555 359121589
    0x909060602010b060315270a05010e06100c061413030801050609060a0c1b1401021b0109030305030c0403050a150b0a03031b2906011b0c050d08071401150e06 69
    0x741400e080100740300005980c642e00c1c80d43c1c5d0041c411035001d41f00811842c001c000d480f40500090342c0380d5100e520300c3d50b425160217521000c952200e244450050303201341c1549010b0000094070180e04d03080c80d40013400c00c40742203c88117400961082099080b0225034003418090710140d0400054001060103442b44802c2c010a20100310b6900003000000d807200381c031b00c2d0b0f810301504040540d0313500d085802152060342280503000d91254200351003013114140820460503515020b116242d92400e1b1229803015004810001d020080800482c0303003013002000c100d10070b0340034606a144019800048600b070f507501a200d0b51081c2002c101180c1c0c050300e4041e65117800441580044c440d4906484804a0381c01d503003c0c540f40700c0c420088448030449000d40b040e0340c00c0c0c0303852040d040d0070310b881c00461802e280010000c1304520348c24031590801c0c01500d030303d0a20480c0414903041d52501d802c084040c0e524583e0030705a46403446940011901113a010003080c5d603046c0c41c141806d00600048601076540d038800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 359124055 1250 359122805 359122831
    0x30e01450f0b0402041b05040f061704030e1306080c1e090f070c1b030201020706050c0619021204050604020a05040905030702040b040b1905010f1b120e03010204060909060602010b0603 81
    0x7405554070380c3c0c03000d01030031100003203c007030140306c42d0000d0f080307402512030329090320820000050140d00484804020140810404060f03a60310382d4140c528812904074079822000840d031802c01345886104804c05001400010200c403880d1b481000102e04030040000003030002c02500f01c00903104c0c41549900040f649035045035940e40d209040700c00d40a9124050041d0b07041480b21301310740c5080f414010a590003a400d4034413081d1586410394403441626000100c5034841800641c4802c0c00d82d80340203071b000c1010310251614014107c0005487c0007580e00707856a402c000305001c21885c046030020010f1800b0f58046c0300c4040c080d11034584900070000054d010380d403580c8054941d0358541e440381c10ba42800038072003000000c0040201c0c001c4003a502071103000c240c400304a0f040c1507003e000407204041c4080300d040b400002d03a5681080c030540341c082420900034004245090b40c0c0d801e0018201800d0940d07120707003001d45031200d0401600c00541c030800175a450709034019150340340c4d0812240d00c228080e1841c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 359125305 1250 359124055 359124061
    0x9030a020f030c0d0c0f120308071107051003051801230606040503010c020706020c042d09080f0c0705151e07080a0e030c041b030e01450f0b 62
    0x31908003c00c40103980e1303200600100500421110341074200c150307102101d00c9000700e9200e00d40308560751514480540840c000340700041d2954411302111480c0301461007a10005951000400e01c0721804d2503e84000c42d880d04200b183c80440b2807411100845000700a0050892203010030a455100d03103000b0354003540302800250591106011100140f0028000b00400601907100030740b154024020400103005041c0f8450241c60b040c000c00740d8012100d00f400700300a01050501004c80740c2c110421045d00d4031846c0085c0480c2c15038010782500d1100140d0340756101d184841e01814000960062842261f100e003040341d00c42c103c10240c5007001c1c101c0300c01d000b82c0d1001c004810380070b01455200902c0e0480015000503110742c8003030116041ca9058003203038030a04605040000390b03110005003203810381683d481c0a403828481d030041c52040c045903000080510701c0e510b043c228104003201e420075150411503280c95200001d0901041490340c0604d810906106507108581d08044d848094a04038212001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 359126555 1250 359125305 359125309
    0x1c1a06220506040f0810021903050402120d020601060912050303010603020307230405150a021002030a0e0a050a050d050f160206091c0b090f100905010b060406020a05070b09030a020f 80
    0x400c8040c0000a09154466680e03107184800c0e89150f005004075800350900b18020240c841c004d8540502c01d441029a040c1c4d602c02040f001404014404c2c2c0e4400e61031078000c036a8100910003800301d98256405421203606008026280000c168001060910b020310007101050021055a06440300341c507016980340c0311071100b1904400401010403442c03d0101d0480910308011004004581059580d11a001c041d84030220b2507010368880c00b030158024180099514102c2d500a41c2c0c4109001400500700c00c411442c2e520301070300c906007191581c0c021002101808002c0209070040c401c0e80c60060310b880c980807c140030b180501ca240c44018542c4400100455840c8020350350003000c0600b25030a2b0300d0410b1500322200300749560941c1c221504102044444030007041418100b56804000c0c00041c81c501c50700e50091001e660190741c15540c0c3c174a01e500c81d0340c4110080c802002e4a40c006c05100f01d86080081c1000b0780c81d8800d44281c90100110001503c012661150f01c4d60116002c488000703c03840 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 359127805 1250 359126555 359126617
    0x121803031209011505010921031103070b0f0f01031709010306150f090f0b04210c06020d0e03010501030c0b1c05130b06090c0f07030909021c1a06 64
    0x10703002600c860351004000c200d030015448440c2c5911151145010260f80d100195580591801658400c4100103807034000804001d0100894a00c41c0c038100e003000070004000341c10341c0c00c48102181d40454900503c0340342c0054200c1a60090401c0e41c00413003030352441da2042100010380960507800c00d0003113082805a03009a1018000300500380b1140729100c21141d00401d08241c2c60400c40c045100c408012460303031070310405207041c0c0365400c550900d00f03400c109281c0c01602e491861005d10758454034078800012a07803001c9000074021307900100310304107031408090586515481e13041e000303038505401003002c102140008412118900e03145a558400a20082e00c0909441d2070301d0601400c00c070074091841c680c0c1401700506409a0b940c11f0094640004200c1500d00644008040304014001c081d210029000140001ca2081c18080f00e465552503480c0d01b41d0300002070814207041c001e0050f060a540714041c018075075880303c100e01081600880000c8d5a400b4448080780c203280426815040200108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 359129055 1250 359127805 359127817
    0x70308040614010f051c11130b0411070311010b010c080703030b040606050408070e0c030103171303210819150b070b01060f020706090501080c0d090b0906060312180303 74
    0x482c00164940c1c550101c9008240b0b10700c5018014070f4102045080c1440c10035080c074581e0342c4003044200c41ca02850401400d000070006400d1100c3d80e80200c1c205e26070701c40c03040c0d8429081708400e003900c8440741d05003c1c10000d9605030051199040c12005940c1d03a0780f000e14000c03c103a00181c03543c0c46204d40d0908500902c015806203070018a00f050115040d07800402030402c503401c02d81220012604e800703c00c1840d1070260fa25100311802800107000081984070340700440c00e081d10701142010b61400540d4029440e660040d0303450503292640300320303a03a43c0c0e107600c0401c0e8409040801250400c442d406c1000c840044c481103011390f90301907c42000030381044400c02020001085512050a4107003807020041c207104020114559400c95000030340045880d6084401c2c0340c0f90030f0441031402c030054400000090200c003120b0010001506910f15034417642d10f43c1402510703220840d02d40100f0040c0740000203000c19100364805041409195207110865038282c4209403240300c50100d04000c2407440c0200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 359130305 1250 359129055 359129081
    0x12040b040c0308161b0f05060d140f0412050f0a0e0a05041d0c03070f060305070e060d090507061803080d1103130606150c061802031906140c0703080406 67
    0x40e0900512090414613100b441c0560648481c11000b400710015044d0103109107103001128240030040d61600318007500e0702d401510400b00341d102d4078140c0301c45a500115115100c0ca200b60f018042400500491500550903504000345088428241d681c40c602402041d4020010846107121441d10f4266258000b044043d2051219003103406d038140100404002c921524030480d012041e40e860001484412513144030307c4035940030b0600348100d001d0301000f0070440500a40c505008400d0301c07440c00070140c800d9418400500d45103d031800c0360034200c90394420010840c0854407009212448030001d01100c0c0d2001d0301582e50740075107643c00c01415100007601072007640402007040d05102841000340051261030100106600c0740b039850b40c50013003d896400010212001003001801a52110308070680c0c460070410300034603c1e80040e01d06840a4000c40c00440400421420024540140d00c0010f04850301c1960714500050344082e81e028903240070b010020640c0120f000c1c48641e0b40040007207800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 359131555 1250 359130305 359130307
    0x2090109080d0504030b1014060a05130605040504050f07020303131e081306031b0f0c021513050604030203150c0d06090617060907060f020c03030304050607080106020312040b040c0308 81
    0x101c102d0140507500144020707a034142070300d000544140b20842660064807500c0654a0807101100d0900015402ca8400d12050000420202e900c2416240443c001450159502070342c0c2e9080100348410343d08082c0c405a240550b0f402440020358012068990100c03001c412880d05582038100350071181c0c580025001d0a4003460b02580a22502c00010f09140820b405010811940e40c00d08a0895001d0714411080b0b80c1400c01241c400391180d014118006003500e005424081a0340014040007038041490740041d00003d02600c002481980620090a01b190058189407442e00400d0725800e0707103160954034040b1140020346070a00107081c0c0b0603022030450108481c946505001008214500420b10041c0d07250119403001d110002c0c0b150b00c44c0c1d40c14405445030f103103072079030540b1008400804182580070740c5400301603984003000034602c80c600a41c001c01e16070400361005000f00d0f006070460300454100b00a8280c5070020409042d0300640c0c403104505c0705507518284850503840b50380000b003944c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 359132805 1250 359131555 359131573
    0x180b090102030f030a0501060e03060127020405100c03031506020a0b0717040609020f040b010507021027051c05030f130f0308030f060a15110a0605180c1009090209010908 75
    0x3c5d40c2d44658140c440b40e445100d1464072000c101603407071100b4411044110485a50100d941305003c046c14120a000000541030503200d000043c2000610403c880c00150015615024036605000710000454481c03040b1410701d06000c802500c0d1060860b001d04040300d02e40208020501c1640d003d698282e420341c902c880c03401e01c0d2405002408034144c0c186c0c860795003100c070383c1e080b451305201780016000140c40d05881d18606901740300880480c00709940600c4202c0135080401400301c1031600798001041e00e415003450500042103074802d505a801c0030b030045800c903400d0002d90000704a60307488101c024030545500840c60501c0040c4040d03040311542003a2190b0000070414040040d50103074200a9001c041369aa10041c0b0200758103600c20100b41c0540c15458003103a134010049510320303501070000d0798041c50054440d036003078070001c0d24429240340e501c1d0705030b00c0b120506000c10221090101c550b080082c2c590800141101220b01610070103e5000882148503030203001c0200c0204403100c20384030450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 359134055 1250 359132805 359132821
    0x80304052101090c09230601262a0712050c01061d070f080601020c271f0b0906030106030c0e0a08010f06090e030307030903110303160f180b090102030f03 68
    0x1e8081c481c20075030034101010029508050b40c0310303154101001701030404981d9050011940d60440828110b5201c04907500740300380c9d41084084901c141441c21101c0d000101c208814411400c910107940d042080c107001d000000303450113045030990481840c010b0b84518540c4030450052809510980c640c0301074a00d8003407180b003100440e0f442081e544e15060380d903034020701041c2c1d4903a40440b40140180c0200400580034602100d290118a1042a5003000b00c002e561032044aa0401d130780609040d15582c00314001c42018494500181044a40050810341407001107209070006009003014140c03164a444101445076080030305000004003114030036039032002c1c510300900c101c50aa0ba150350405c140030501050b54001d480415000e100103520b19619014110001c009031001101009140700c0d20b6001d0410810156001d8020182c000101c07021020020700034480711616242400f015a00c54002c0420b01c00009044509a6030f0741a43d407140c03603004074110701c550030441c4030301d26000c81401130749 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 359135305 1250 359134055 359134073
    0x50304091b030c0e010c06020f0c0a0c080607210c0e040f0603020a1d010b0306010e03070b0c070f080d0e011407060b090703020c061501050d1e060f08030405210109 72
    0x60340582c404001d2141510340c2214a49500410103010940d4640d00d040000d6140e070050280e1102844524104850145190308000084000341c1c0c0141400000340500207081c0507403034001c0b01c10704000d100445076201303803641040500e1110003030550b144442031a441c01040c440719034081c01001000301066010080004055030f00090303001e4400c1a0002c1543d2400c90b40c951460781d4200046d440581c41d2080c1c0580a500042c4064100152000c14035419281001414060610000c183d9119a400c1507058903007411540300748000c2c9504541008080e10100781403208002514101c00c00e500894010380c4c400d0510740402c0480000020761806014082d4031194100300101e800300f8864903400411002d038003602540c44100c1e0000310105004c40800204050070900c18144a41481800c1e6543c2084542e4184081c48408401c03a005044010520980000e403203440074502c0341e03034144000d0305d640340214040d00f07000790940e40380001442485001c02c4460b412400090011003c24640340102c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 359136555 1250 359135305 359135351
    0x106082206061d150108071706180c12090a0f260c01060504050f10150e130606020105090d050904021e0d09170406080601050702010c1406061c05070603020705030409 73
    0x25184d0840003075000e942c800da03030580c01030b105642c50740c40c013140b4828110344048016083c168044240a464a00100007030051885050720184180c3c6030007108419004c440001000c4a1980c0c100e0f612180c0000c544074042c1300e0b015001420080c05951810461020750441c2454682c60100866901e02a00054020a058800c01d03203081c00746407101c900c5402d00080035188803120302185541408a00035030100d1152251081ca4011400c1005101107219041c0e502400700616444250601400b03409025032a00160080000d01070350074210802816401034802480c400d9400140440481c0b1845040c00c040c1d0b4070a0f01807030781d40e08400c3d004400074003822600302c2c0c03812545800a10340c1180c130360a480444409403942406613507541e00466241c3c2c0042c900300d040c0207410078a03602180382c241a1580d4040040001e00e10703030030f1032003c219098140c40304400035004080911000654041945011952a802d0168403802180782c410b0441c0903a07000030f00382c07500c0d019103420419465003480c58 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 359137805 1250 359136555 359136571
    0x123004060c021218060c03070f0809150a0c1b05120c0f010503010e01050f01030207080a02011a1021020403051c080606030c0a0c03021006120b0106082206061d 70
    0x80d00282400030900305004d50085a074101d1800c032000c00075801c0c000c00805c02c0446400642e854425035684800350580c007840d00b511888404500a0884c3c108049d180c0701c1000480c0a4505016945100a0600344e928a0051080c2098a40026201d4503840c490001d0070b0010034078a10401040e44031969800406180d611400c90300d144000594010001c0300e040e50010f150800180c1e0030b15040c004001941d40500b810180d0800c40302c03001c140920040c1070743c0342160f4000316009001007210510450108200d078481c80d855044150525044100041904050005a100320900045180080c0600e505c090501e0050051101752600c00c0580c002081000c4e480b00609502d84605002150004480c0c901544908200c03030004903009881d008900c82c801d10450300c03a0080c09034020700707880103a40500c1c11a03403204d42d00000c0200c942041405042e0500e4a072241d854451400203054480a210b0350550060003500410700c5002d0704180301611002107242e404040a02071302e1205142159005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 359139055 1250 359137805 359137813
    0xb0d05100c1b031101140112141002180907020d09060e060c151927060b04020d02090906100206070c0f170d0c080103020105030c0c01060503121b123004060c02 70
    0xf401c043e400106c524181d4aa0f0600c3c04400381c8290780328402c002a00702016000c1c822040030f007000a205000520303039000007036000f02c074500d1440f080c40900c00000e0b180d58190340090210031840c0f40e2142d0380c1c03000c07100c5c3c5240240903000a03401140c1e00b40310300300f003901080c0112030503094505101c18072079010303030341e24881003040c000f03107030802c1007201d111032030721401150303020072000740308412081030f03510310b409800d001070805041d40c0054201d9100095010700c03d03030045001107452820003070b019448041603a404e0b8144207423032002504d40000401041c140088850004184011260030072862035000030742c8a0b284141c2c8a10108580151a928000324140445103842911540545040344d030f041c0c64041c155207c0d1352a06216401c486410000c40d0b5940c2c01c005120366003000550f54441d0390801155840b6800500035800811030b032a8180d080d48600034621480403224102c6510300b40c0310302c1803002e9030007604204082c03060800858808103250001d010500c05e484e4803c42609086030212 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 359140305 1250 359139055 359139071
    0x20d02071103070f080327030a0b06100c0206190212070f0b13050709050a0e10060f0e01060915030902030a0b0f0a0605010801120c08030a050c010b0d05100c1b031101 73
    0x40e655100040c02640101e4100744180b01f80030407405100c0e4070746600880511000612900801d24060491070140e4000c44108144121030610384008040c90140d03103446084481190045212840354450b40c0f0781d5204010b29005402d8401d00c0040b42c400380701044940e0f541030744c0c2071204440d142e10600b5201804104046481820003c500c1c02c0e20345e9000d0301415803280303011104001498000c2805814540310142c1c0080c1800a020307843c031000c2e4026002808034140340054031190801c1d080664091401001407050715041340b04001103880c0c405100c06400c03141d00045000c0c00c2c00d924003c1d00351003034812020400c0a41c0f9800c41c450182c01605a40c240c1e00c1c0481e10342034031014414180402e0b110030051242a2842c000c6048140c0504401100fa50b9a1424549542e102c4482d210010308080703071002081d1000e005120b040c55007164400b0341c045407610341e191205160080890001c0e42d034280c03000540e020300b4101034030041c030f6904000004401c0c00d010f403c0040c0e15101d050194070704411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 359141555 1250 359140305 359140319
    0x60109050a1e05010305040f20130204080706020c060d050a0227040e1b0d0c0314030d060603021207030b130606050703020601151707030605130f0b0a1413020d0207110307 75
    0x10244240d400c882a243c0980460702c0741c9600f209c0410300748140b840b4140e210200c544812038540c010710b01503400160748918020050f4100070f2580c11600840d0411f60400c4035680e1035209441081c80291f6000440d6260104210002e124160452409070079115001c1d08140c201c8404260f034a8003550280b054013503c082403a240c00c003011010000629288102c1d400b400c0880f84003205c00c1c0b05101c0040740e070392642c40d1141c01d4400c60f00b003070310f0640c400102c031101c403484e0b070150b0310041500c0c0c1025030034500d040640341070465004016004055941071721104651b1000403881d06841040f004002c0761b520340317400070500d9004810a0703000d44150310001400d544601d41d2141070108656803c07070b5051f0614107160010034041c00c280c08041d142e48001c03517180d031002c948500c40081aa40054510040b0600c08103480415003c0b0307101c0e540a2a081090b8041c4034107003203030395100311020340340045500d000b02c0003030140081680d01184042604410000c1c4a0202c07008a5001c0f02180e14083d035600c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 359142805 1250 359141555 359141561
    0x3010302180129090405010e0103031404030309090b061204110a12020306011a0c0f06072a020f0105040f1202041803050f131212140f040e060109050a1e050103 70
    0x30960402a444040707080d003d03503c0c8240400b08901d000700140c80e00e4052400a4291202a04540b155110306e034010020541c005440807881620f01400360b081a01e5518003030100d494a1144025840d00c030800c80a15a88030001c650450240081d840424181400c1181075070000009280c001d240140e80410709240326075508031169402001007200c0da0078100340c9015802061007002c4010002c0c0011035a0841c14001e40c0d800703850410003003141c5e2030100002452183c00691601c02107010240001a442819079400f8030b040c0c05a480d010410705c03200c0120b0b41c901c82d551100303492101e6002c0100b50401585e5883c9110340c0200c40a1000880c0e003050a24039030100f000060128004101000e0010081c0c00544035031800e1500001096130f0352002c1031420400c1c280c04541c1049848004070011385c20460040c03101511a4400b824101850105800c0f40300314010110120501e50001d64560311820180b805410701500401c10150388202902203188030454100c0801c01e04540410b0395480b0384 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 359144055 1250 359142805 359142809
    0x908060c0f090607020109030b16031a0907200d0903050c032a0f04020304120f08161101020c0102040b1905180f0d0203030a0513080a03170703020c07060302030103021801 75
    0x811851410b11440d0410880e6072003100d0407810b100f0150030000c00b18104007070b410b00c81c1074885005d0041d5006407400a08980224041389451941c4510700720040d00d03280c4107594000c40d6420070100005242041144202d80281131004510907000c420000c0da901c11111412070703104000712a08030f00107100705501c54847c2020120500d40140e451440d5040040240c3e0744000c01070091050038110601083c2a680b088030156402c0c0d0515040083d1540c0c811003100742503d81c1c0c44c00e030786281420601490110048075151003001211076030040768100a5040b207260702d41a800840d80ca0b87c3e10b4004120b02d0300070540d000b240e0059048190392082c05001100c14a000c03002c048220280c0e84420000c01c070307103400c1d035041c2c100400082200060304d0400051041c0301c1c1c2d9483d440d0321543c0580384048449065046862260842c50420300042e0304410310024034811382000206954440302c085009004100202910f48187c40000980a40650055050320700a60b42d1103070202080000007840c013028 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 359145305 1250 359144055 359144077
    0x80a090f080111091e0d1a090606060306040f02041707030c0605030c09040c030b03060708160306030f032a1b08010c0c02151309060f081b04050c0c0604030908060c 72
    0x4c00000c8074038138100ca6842c000c1040400d0380d941d10742c2c5107008943c0c0d0200710a01154882003941c0d264164130039840c00640d1004880d0000c0c181d600d00b410200c3c1060001418040c0a90b071145200b41014039281c045e80c001d0840b0a40254035041c1005201713580c0c2d10355110075231754a0307203040c00410000d124004803031203032000d145d426140803a9031060000801241e8503034820545d0350303070031406a82d409200b001e004038419035403600035040c840e030003000d0382e4402024181410b26101c1c0400008e00d2901c105942c03660182040300c4503102c15000e01000e081d107a9500005209a05105c030108242e014140000c00c0300e0101c580c06454560305498220313125111480042480d1428040041c40e0007014230303448400200981d402d101d030009001d001d4900d1070308072107149612a24280080d84407206c0440040c11f50000501e420440c0d5400000980d0760982094021501e071400508800400307401c649541384c41134102c07052850582002032401c1441c2c0104083c2d0b0003103c01207081e5001d41d409540102d412 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 359146555 1250 359145305 359145307
    0x1103041101050912100f0b010c0308040b041a0703050a05130209180106050a03050102090907020c181003140d0f0905060a0e13090f0510200c0a080a090f080111 70
    0x80c14015520b039041500da003948a294451144001001808030310886208040c000c81d8045150581c5425a2070100100e03040000c52608140801d6004040070341203a003003800390100b0380702d03070404448024806824240d905040020301c0112a410340c851803141d4010b40d4100250340b40e01d40807482c0e11702d0152001c1e5220780b018000c0cc600c100501d0000c882610004000100281e40b407000c01c001d0300c16030340191066540400c40c603403181020090f241d0f01c60070303a20283c20380c003850b14000ba400070000000c503400804c1c80000151840f00000122000d907401082d80d440e0000300111480c1c2d0b038054050440006081c515003440d66a01031140c6500362340c03004050608280982d81c0071a4a50120b044441c0c0c0700e54101003007071070220b852154458050250b900446164003a08080346440c4100300700b020228078080200345059610642042040d42805810345d5900191960700c1c40c258280e84043c0540c4000600c803000682c005541000700c43e0f0f90564120440c1d03a4880d080c0c00c88003410841e4140a078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 359147805 1250 359146555 359146583
    0x110906130b03010e060c04260a03110a1b03060b040c080c0702030a1202070602060906060109090506040b0a0905090f03130603110c15010f05060c21090405041104110304 74
    0x100d6420154814801a00006a00511a01e0f440c07416005a8100001a900007024004000c00c44102c64603a9150005214841c40c00c403500d03555819034000107000c1104214192413451000d01c030f51b0319141e4005130a04801e14400e48103e0300b0390b04d40d12003103503203e203046005a02810a8020b072003908400d0385a1108940d1140c07030700344030340d40514000ca82c5402107400200000703106001c44140e204241c0d006194007418001c020785010806010300c4a00d034800b0301040003c1e039100d15410305880105001054a440300c03004200508130041d44542e0020040201050b000025400288200d01160450749035030700107242c481c4c9911885100701402030700180e090180304d009030040080c0c401c0c1910440c0c640200303040150700b405c040b10599003801c18044010440303040101408000343c0320484045242c0200c1c0780c0c40c1aa542603400103500d04c00c0343c00304802ea845100724240c4045130720181042c4142d103001c6c94103e01c0c1c240103800301c1344520714185041c1d000d9100c000a5a10031988940e1190101e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 359149055 1250 359147805 359147839
    0xa05010c050604061a0306161b050a20031c081e06090c0f1902010606050a0f110f010207030210050f16080a0f0603110108160f1b02060c0307110906 65
    0x5c00b030240007008943c41c1ea0715107150b94500300071043c4030b0915250000040c241d90940100f03580750090a0080484054503010042040420207a5540d03900c0810921022b1948080d410400140402644d05001f046414101c41c15007801007000002c1d907542d004002c0d0358903a500c4442d946461003850180300c2d114005036283c01d10000c0942c001c1e42c8501c5e0303142090101c04030100d107540551540840301c00003905441d1100c0c3c0902610005d440c96042c614103000340c1e4400148029a590508420041c8442c02404050f005000440483c110300c0700a542d10a01414043d50b41c001c2042d000707200340c2c50700c00018815024400800d009014266a0b90103400fa683e004881801001e0940c129030f0742d8921fa01f08212400c1c1c81600700442c49020110a41c042c6200050400c4c68002c0000140500003544d000340540c0c06040482e40c0001d5042c5100031124404000c1c03514007241400030342180001662803040e040c00009029820b00c00d090120104050600f4046881820b5506540003c0c6000784c00c100d20b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 359150305 1250 359149055 359149061
    0x108160909020f04150f080a0b0c0d0b0307120b130c0528030b060906010f1211040314030c070902040e01060311070605010609152f031b010b0a05010c05060406 70
    0x700b40001c0900249982a8001504448440305034018024003d141001030f00344003001e4100800400010b0002000305495202144030014581d030410140080e070340f044c5030144c2c1e2081d808420050b0480742c20540b19013015005204203001651400308100004902c018210030b0380b981a03501c0390b5800d131050310304030510111142c8802c9402a812a051000c090004100030070002180107113112002418544240100c0000142809041008000c00788441940100c1c8010030440c2180300003444a00a1056142e40d000b0303504014040d607121030181c0c045500000250012844000035640551769800320314080b8491445030501c681010001080424001d50142c0220390604007114908546e5130b481e80708070b40090304030074045207600c0b1003440041c040c8c03030716407000d20030300e0800b80d0507000041010300c88524a00e00d01118295900012038403004c0c10700550f501c2008181009041080301001030b4042c1002c40d0a1500400c0e12002c009143c0d03204004480803190010098007450325103440701000307 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 359151555 1250 359150305 359150321
    0x2090f030c1011150702150112020109170a1a0103030e010c0b16140a021b190311060c060f060102100912030b120d210501030c120303140f04060501081609 68
    0x69010340c0504e0480019250b440364425102030b030140000c0222140200d03e0900c040e002203000c0c05075a2003140c0141d811903110000d661002e82c101091981100642d850311904880040003462204a000c086030641c0c068a41a00c0c480d440e40201088801c0044644501c0c036200646024140d0f00402d1545100c114081040300340340c64036403c8442040150010303036015050003001a0300900c1c500903285098900c1c42403041c400c49420b400e5141105d0250b4140100b804050300010400301550200e541d00341c00c4070244617218040d07850314070b0321038054540d840e0102c2e220380c0503018440c01840d0105151090303521040c2e2214050304480d044003000c50007443e1501d46282c12220500c2c004084038010404680c2502003542c403141050180e480b00c082c81c40c06040e00901550800006000003424080000156100081000b01e0f04c00141000c0300a080d4200141c40c1440c42c00c0c09010003040780b074480c40c0c841d9010350024403150340e0f03171203c80c2d680740c51121000c1505001440144034541440d006846 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 359152805 1250 359151555 359151587
    0x1406031c0309020d0c06080a14091b0301141f0e04030516020d02062205040903020c060d020f04060806010e01230a02010f0507020307051e060415090506010902090f030c10 75
    0x1004d1a660380b1040b000c80d05401480120b14041d0400c4400303181401418a04114821004d1450400c006150303910344041d40d29184030003041c0080d00d00354a00b5402924007424019000c0740030304044003201b0a0300b6141c100d5142607070f1101008a043c0b182208514003031030341562018a8000c54151180107002c150b603080364440340c040302010240e41c500e07002d441107803204040c1d20303005a078500c2c1e4000c035030280c3e0f4045406a401d00300d001010075004204074020300000d55600d665803641204a0700288920040c10030300200104001c25465408414644141c1082c1c855624050f45100196000381a401071781854101c0d4180940c0700c0e042d903601509050711a400081180900b1081c0541510b1007214150010b80c8003180d440140b050801005c2f110202c40142290101c0302600d44903200c00004201a2444002c034034244451849a4042041c690f002004c1d1a42940c40b20300110180d401942c440b880759900d0101e080651030302041d05c103070204004003030302c07800d4440c240169040c0d0400c540c1e00d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 359154055 1250 359152805 359152819
    0x2b02060307230c0c010c0b0c03091009150b040524010c0c0e04170414010c020f090a1409161a070f0b0118020a02030a20030d1406031c030902 62
    0x722400a6540b24150301c0805808820303180c0c81d008022034680f07001030084904000c0c4440d900c1c0c02051500c031405410420b081013a40d6203548681d005450403e51142009000d40781020b4a0184406a54100340f58000e03507800744441d400d50820041174030740944a20340400c034010a10000b24001ca6a040e119100606011007440c0c1c503511070740d0641c1019446080740c1c008040400007045204140c021010440b108140d041078141900c50305040d5101010728140400240c07044250f580d20b000d900031100000300300445a10307000715010084c00001c0c800070441096a008919560404a042d5219020141282c0c0d452443d00000c41301c0c08072001808801144108411004281e81408040d809030054850201a51600492407005814038290301e00192040c4000e40c80c15501104480d142002c030b28003a81e0154444d514402e1340742030307050591503070710000038140c1301820b854002c0594424178000c1804207546140515482e87d5110584d41580300d910102e03412114080ea10a0720550f0014241e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 359155305 1250 359154055 359154077
    0x5120603010f020705030403110306090303041403191215050f09060a120b0106020c0604050a0b0c1e100f060e01060c050304051c0b070212030105010f0509150403022b02060307 77
    0xb0000f240e1080d02c090f5035035040011b0070300078010202c554680001c025001080d80341b41c22840103841f400b010f40002d00520301c0c2031040740302d22007c100341d42c1d900442030b09440d9640c0a45202618101440a1004c0503a003011480a41907031000140b80403204040c0c000317840d0181e180c0070044020b200524003580002c900c2d038007142d05420314145400b5140724840741070310395042000103864031f0600d040700c0b4131882c0100014041c540f02e00d0070100c100c0e0b840c5072855890b031103a240041d08103801492100c0caa20003072907144114000c0042e100084803444c0b4420003804290355041d900351780c6c040c01804145003003403004000d0756101d04942e14a1a00400c184c0f030030300b9150000120b10050462000746554580c0b10300e41c050007102c60055403c0050740c0002d0540200ca0340b2070094601052152906005c0903000006405000d50100c44070040c00800d0680d01c48907241d80b041050f005070100345e0203402c03a0750891410105000b94641401001c45104102c850554200219644002d04480030402c1181074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 359156555 1250 359155305 359155331
    0x130b070509240919080c211005160c17031b0a0e1c2307030b0f0a0c05031021020d0b0105040b0609012f0a05070602060a09030512060301 60
    0x218842c42010810803503554181d40c08100d0840040d448030b841040e4040000c03c0703041c00000c2d00c003000031000c0d0b07030003110217200013104661540340150407540c0340182c0005079420619503110360303c80c4110b801c0c00c0c201024884408c50391000c07003a0000309241d01c000e240c2c103c0001d000d00a035501845181520444030b0081e410880a0f400c0700e011200400d0304000416854640460603100036284903000b50b0039a105900c440000c00c103515521485a01441d000196402c42480707202c008d0758002c42400406e0800a40300784554038101d40040340c1c02c0c07030701010418292187d8210380c003c049403100c855001c6d007064544c4003080c40c40300740d007404440507101d01710068a4100d01030a4180c050a002c00c0e9561400e824482581c0b00700007558816401080710b33141503030708004d29071540032903150b4041c455040e05078a40040352000101d0406441102c043d0b00400100017040c1c01174910aa0a840040e1070b9140000b040c1c0e10b10b84d0703004001c10414492101204588814140d100078000c1c0042114085900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 359157805 1250 359156555 359156599
    0x504020d050a110f0d030e1003020f0c15060306010e0403080c12130302101e110c0109080a09150e09041b140102010e06100509040501020d0216030305130b070509 71
    0x4401c0316000c07101c4800f80c165151030a03e100700c415080d142e00e069030980b6a0010507804400034018800c0b201810002c1d00c0c80e101c0c0d4141c40030000d8030007010340e4070030100b080150341d00f407000a80c880c400d10803800541a803c001c80c00700d040713440d032890586441d241c036a4282c51960b00241008040c036800c3c8554841c2d080443c035000d00510442a40501d0300312a030a000303080442c5403407050312581c10400341c0c00080d00c0019103150082444280010302c0084c241040300c840c81072420380b0350f036076082c054100244413040e0004c10200d4801c2d212042641d039a500c10300340a90b054810b00b40400c8921400720200c0c1884600107500c5031007541003035860040001c3c8401c000b407440e041000c03000140d24182007a0350b0248100b0340010402e400604262804401da003407031454030f010b69401000c0f04c10209041080c2501650b010a40c10b120075501c030b030340300041107048003c00310b425400682450081007402c16517110340100d007500000341d015070b95524482039403a0703448090190f8006540012044010b04813032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 359159055 1250 359157805 359157823
    0xa0335040f05011b120e01111006060810060c061802030607050301060921030c03120903031b030b100e19090c1710210b09150106030c02100504020d05 66
    0x401d4480540d081c0380c00100300030814108041c00610003404c103008200f504c60080000300c0340d07103840c421010700400100d91081c4011000d8056200d80700813110101069080141039a40310b079501c0201c0da5500842e001c440146200d05000329030140e02000110f102e03500800b0003513a40702031640c0200d202e0b60209241070030442e1806c00003070000c001408035980c00020304000f000054000c6180d2801203256011104a040005080c000110751081c20180550a00780d03043c04090b00c10030060340d650030f000e00038201807401e5101c1c03801519200c884045c000e2249810103580604031a8264000d000c00717407488040c0c0741010fa4800c088800c01e61024000ba000ac20140c42507c40106210740300e681c024001a4a040a150013814400e04000750400b210819074101c0b0060614012038003160000c56401096a0001806044108040046020000450080d107042045440e500c0d681d031544201c1c1242c103419001d00041c0c104451143d0700c50f0080d0440d94205000420303007c00c1c005141d698614141d428 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 359160305 1250 359159055 359159069
    0x10506181e040b060a1706041509051e0405060708091606030f0b010f0206042406140a08030f070b0405100912030b10090312030609060b070606050a033504 68
    0x8881c0008141003500616000400c1564250f0a00080010140071040c0342c81030030324244429000200030740d549801ca00c0544e41400c590040581e11404402d0141070116503162200f04410035000b020419165094401c6800202805440d120040100e40391617001c0c200b180d451050707108280240f91a60003540003044203032030008041320798400403010b449003800c0f640d040c00843c0103000c08141d00403410359446580000c810340303004942080440c0d460ba80042c0070359000d14000f008944d00160792200c00f030400007102c043c003c00713603a81c910320b0b40c80c0329038001040307211005c1c000e8900088a2005840c5c1041c07080040d15a546070700e010034000c46160a000340c0c1c05401c684820210140c2520607156070100c142c50f911403404900390050040d41d09444014241c0703035100c0c0e9054646100764003001c090603000d8418400107540d4052490940c010400665450340342090005003480d014096004496200814620140030b4159503403507100781038040c5c41045100000094034420345001480a0012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 359161555 1250 359160305 359160349
    0xd050a0e2a0301020c060c0c010608010c0c050f01050105010516060f0c050909090304060206040b1503070906060e040b130c051308011508150f0c0d0501090f0b031501050618 76
    0x80d18a420720080007401c0903a000741d10400c402d6010160200300305600051501ca0030340c0d6030b803030031103c6070051030250311213107095113006002e2481540c40701441c04904e00480458400034050280b41c2e007210402c0c8201808940c00f0005109032040b003400307001250b402414005140d50305100480141d035044107109000800c0060031707152510306515255040040c640c0118142401c10074082e580b40c001078409841ca02c85c00c0005200d804c1960070384010700c40090306039401c1c15590490800503024034006c240100e90a0704070812a414148a0074006140c010130003607540002800b0040241901a00303101084000c101c0d020700e1905100809000782040000041d080b41c020b80c0c9039a02c038106070010f1005410004100b4220503400b8810740d0400843c0b02000129101c3d24100c2106d072082180910f50181800300000c0e110a01c1d90002d100204042000e0140251250805072149035501600702e503d1558001401141401b001800a9458030521800302c00d101c48001084400442419000c02c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 359162805 1250 359161555 359161603
    0x31502040308040b09190317130b12040201030f09022808060103050705010f050325030f0f090c0b09030703150204030204110c100629092e090b0d050a0e 67
    0x40c580d0f641001c9241001b004080c841c103641c2da1196407881c41d1030241a8120102e51801d1040c9081c03100070081030b8144000340d65005801d21200c5200080310140d01103480c14030000190389960185c4e03541c0c07540c018416070354410380c0f00d07503000070803080c80141841020540e008100c01a04100060107180104003c001c0113240c1400140001d0340a544042080303400c0c0309010750081d00f40d0001941c90030071010201e45c460310b40402c030020700d03141100708041403c0c404904400309882c3d0116000e140a8098100c5e030649842c00590148a03102c0c2c0140c0541c8001010000710301d8107004805121115200035184c95541d0300041c0c252017410f00290040c940000b58410714860401a030000300c041100b0a024442c54403091020107800c141a030140a40e0b1000c4003a41d14505900301c440c800c80c010402405100403542102c0d021140c100a501c946501c10103074510a0700446c2e241c41201d4103a0f4080b07151040f01c01d2482d025140242680454584948007505281c1052140c035010b05020781d4100300183c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 359164055 1250 359162805 359162809
    0x30607080f0a0b01050f071a0c0d061a0a230d02030915060109050d03020705060304060b030712020904060c020f01050403050d36020d060e030904050a15031502040308040b09 76
    0x9100904620b85080c54568058140e0360840b060f210039001143d012a00c0704994281040b0038014241c080d024030f44900100040090000041c0c68580c0420b00304000b6161101e805840c001b40c00004519468014480d22000300e00c505180040402050703802c00e5402c0c840713040b002c65500410561038030b094000c01004a22481003104500c68201511142080d00348500086c06103003a501a0a002d005066408403d06008124600081c4000b1b8442c564914040c10b002d070051000951551007400354600005140d40002c1210a86540042004040751116550305001b00a06031a120641c082d0205401c0040002e10515100794000d0321000c2c0d45000d038003108021504074007804807182007801c80b0703084145010701c000c5102d17841400480e0380c1c04002d0300020340404c03141c2c0310081c812820b003071100103d003c020018206210055400b0702868480301c0003a0b041d03032803041c00d180250750f0400f020008280c01840c1071004842e007200040c545a04ca444040c040e0344240c210300416a03000038010124 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 359165305 1250 359164055 359164081
    0xd11120603010b090109050a110d06050a050303030f0a0911100806030d090f0b13051309020102070e041e0809181905040c1203030b0a0320030102040b1e070203060708 73
    0x4031404074000c201800b1510005451541d043c001d4083c9159680b0000741050640d500102c800352907070481588508020740800054a50740c055140131700d40102001550b4100042540c1c025500c840c2c00007103131f9440700c400c4002800f420406890b488515418801c09445250302c0400104040d60350515520b084001d05150880c0e10050400300500d0300070401c0f115000041c9041500d1403600c3c1c250b82d0341107441c26108140c4032500940d510403400550304849001a03800004048d100380c0031f07035081c40d54032140c50540d0840bc541c05403070106041f0141110300c0b58030302255403e46c0708500041c20885c4010100b11540740c0c40c840307000c24150b03071424411030600c1d5205451219100d60400c2c0940e141c16038441c42892141d11507240c444000306200d41c10035020340c00401080300701414203480c00303a9030b084c4100800400400c0070024920078a104400342010700071141541c0702c410000c1c2c504000034440c054884180e2040d031503810024001d00005a405000e06405043c6595031100d2509100b4015200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 359166555 1250 359165305 359165311
    0x60b070507080c060d090c0b16060c02060403050d050703060918060e030315010c0503070203030f0904050901090506010b07020d02100c1a040f030c02210d020d08040b0105060304080d1112 82
    0x5681c00160f403240d86550741021a4110750320f440c4042a2610b02d40b074450305802d40c0380c212032819000030402001c0701c114210031054503401214107108c00c44d450007043e6241c1e41e0036180a00010700030840210b44c00d485400454214600e890001070039560f40030a20704845c2d548040d00c108040c018810414403095001d12802c8103d0755000d18a18204407010b41c0b04e502800c0d101d141070041e900740302c0301482028402e480034a5005010741340d407400c10341d44000e40340c0d008640007442a840d00d0081408094144666107420780d0120042c01281d007008102000f5400641c0102d038000a45100c0d440140c940020074824018207032101ca0f008003591078650340b0a100810120800a05001080082840f810041207010303014107005031031142c3d60010410380422000035483c501000d85803c141110006100701c0381e103040e5400e40715880c0c00594110380d824800e40e03000d0403010800d0010700c103a203080d1000f150414410001c1600c0c0c5104020600180c0e46c1840403010444004580c503602001013100c0319034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 359167805 1250 359166555 359166569
    0x31113140a0e16030312290909030408060a1b020c010903060f180503030106090b0f0f03070311190207090e150c070203151f0302090411060c2b02031e09030c04060b070507 75
    0x400c40419102c1d15003054101d1f10288510511000700f0030400f02881180c0180032454103442a5150021440c8050b040c4850b400194900b540d841440d50751001c601811050016076642c2407092039503c900700505031412580030260b0b5550210a001c030ba80e00500e68980c2e1180000e1a01c9624002025108288650144042d02070801001c948450403100319401c21a00c0e01c0620b0311b07500c03900401c070020011000032801c0d24100080040700105038046140c40012640d013146c0c0200d44444007141540d1100040503081c0e400903100300ca400342c1d62030303101d58045140350a0b2810244e81c0d4002a00d040354007602540c012400c10248400c00101d1201c1e124464112a0308124035840e550215000380d0004101800310107003500c0d13210850f503d41080340c0340e0348880c50458166400180c0e0b440312040a00807221024901c401c1440141c500110507110780d84c5000c0f4a02e500030100c0c24070590640c1c07080b100ea07603060003410841c0d0981c1e80c4511035603001d803003414051a00c0f0301881c600f0a00d0400c0f01e402c100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 359169055 1250 359167805 359167841
    0x3240601020708100c17090109020301051f0e090307020a0618140906011d0907050901110d020c0d03030f060608010302040b011e030209060c07031113140a0e16030312 73
    0x1004a0070001016280f04134800e000240c0860f44403805c48944000b0719145045169041c24800e04200540001400740c3c0218000c00031521218661002c040488285005070708140300200b100d014024085540118503005407072030f10b142640080d40650081d000100452440400c14a4403007081440c140682944c2c4d5880b218412800c0008a4500c07004050314100513111030040b400d1405901c00500c0201c0150000071103040485002e492034008910180c00030390070840810051500040000c045e000d0b0341c019106101c00c17074051001400c1440825420705845085e08440c01c2a140705d6000108416a40c0c0a09541180704100c141c444001e1220b040122200010045506c401c1c03514492404178240181d4a001440c04110b05e40291200400140a101d10000a104100802c8024508125042c503040141d41402a00312079100016440741c014540005509800d141d00a0395111100e4040b107140d140d00d00200116260b0a800850000d455040340c01e1034940d050050a16040b0214400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 359170305 1250 359169055 359169059
    0xb070201170703150806131e1203021e12010b031b0c0a0c0b0a0206010902160c03050d03110703050304020405042a05010908010e03070f02040905030f130f0b030a1a032406010207 78
    0x187c4010011428003804c00c1c03c07090070882d000003004650200107036203d2016914060400d502500942007803041408122848501c07400c2001c5220498441c004420300058844c0d003085100e1440c3d0700000c00000b10412800f00740e1451580040240407485c403054001d000c0003180e458505083c200540c0548520f00090024124284d0041070050664080307120060725043e010300341000b240305600c40a44031b9074680c45c0100c1840310200f0000791030030341c1e514188803080300008114018404c04030083c001500c2800072400600d819000700d5040740c05a11940d880107460500099041c11040740c1340100c540404040240c0d5801925060082c90584000c2107540b040009072034580c41b03103400046c81014810801002c66503207500508c5415000f60072241c80e2442c6110010180c0d1106840f40e41800c561200000c502010031100360959030145c26607030071515101d0501c00905070701c403030303144030200b00e54401e0703505480810945510f0004d504024103040701440ca0000d4690000c2d0070141190030a0341c1c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 359171555 1250 359170305 359170321
    0x50a05100228120e03130605040b04030305031009061203030f0b01020a15020f0a050315040204050d06020318030307051c06080303070c08040e0a140a0507090b070201170703150806 79
    0x1e10159001c094001c62524140d9100842e600403110742e0340f1407035614200c0a5090f40740e0003c0509400c070313600405001c4203a01e07100700b40c556000e5441981f8081c0700030001440044d104101a5800203082654501003d484110040070b480583d00507035004c0075a0603010060607814003d030090712020000400030142400c0c0000d407144101c070405081544862146c0300c0000702607040f241500200304e2640d0b220701241d80e00404661040e5081b1003001100411030455241034800c0300d00301c070401001c450a1070000e80e94540a03410051452140540c00d029112020000744015032150b011655040e03511003e008104c1d1102070040e05091302546803038410b1005000010450750000000c3c01e010714480d455252452591086400048142c1144010b1090441312034122918080365440803e10396614075400c8411034030304660060025800803810086008044010000d05e8010315040b01e040d544c00107050070280080e00c200000980d20040c42c0170106498543e0310107032255001402c010708101c40d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 359172661 1106 359171555 359171587
    0x120f01060807080f060a0b0301020d0e0102091513061808072c10090c050408010204030f12140a05370206060d1a0c090d050a051002 58
    0x3a001c81c420f08046450481015030000070b2130305580c0d404160000c2c19115084581656007003101010885060003268001c010f01e40001d03a5400303408092016000700d84442144924090208810b60750040e400401160364501c0c0600440d115a0071080016107558041c040c544120100014221959064503090790415900411056030410560700e02c9a0100c80d17601211400d00340a00c10101c0e46d905c4940c8451151030681c6c2040e80320400b260890748184c100784d6034421001c42100412004000151002500e0701c2c2203030041004002556a03070082040d024107015020651000d43d888401e001d020641105810b1521065204882c03250000039400080050041d8030006285091a0880c1800e2135444400c154540400c0c403014940c0c07400191807400110003c03c08039000f80e403956050560240200003070000c050342d034a00b00b850304154100503018240180a80050340340000 = true := by decide +kernel

theorem cover : BRFrame.Cov 358992805 359172661 := by
  have h0 := BRFrame.cov_init 358992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 358992805 ≤ n) (h2 : n < 359172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
