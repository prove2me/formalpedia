-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3880
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:37.541847+00:00
-- url     : https://prove2.me/submissions/d7146ffd-2b03-4d31-92de-0a54c7408109

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 697661870 ≤ n < 697841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 697663120 1250 697661870 697661897
    0x402030a09051b1c03080f0c070503160303063213230105030f120a0201091514010f18090c030f1505150f010f14130e0a020903030712 59
    0x4111100703007054403501a00d082001c410910100c0000680b2940c1100c4c803d90078500065400000b099006849075083c83e45515902c14010841c4140700c4054154400400c40d441c0d1043e02c4070003400c80703d00c00d0b01c081024590341c04071641d40340c1c00e4410300304410344c50310110041001c5601034001d681c10014600d410301481409268110b8520701c1c0d5410260400c18580a080c011655521f400f501c812002800480803040c0001d503201d0146040008004001c034012058038001d400032540c29500171140e091400b1080020340062095407102da980b130680e0000010061071a040007000d40f00c5081604401c04410551240a48620081220440004040000410500361340201001d11520100b011466216030034802e440010707096041c44181780c014907419a1b81d11f0b03507100c800310003030a0520315045107440c140c800d0102c2405011124100144140c50203900c02c60b071f41c05490380c2c104844902d484007030206003240a0801c1042c0c05600800850700401c606058003d032010a0389040d40750714905 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 697664370 1250 697663120 697663123
    0x3030513170a021309050607260a0507020d030c0e010e011e11062d06032a2403010509090316080d2703050309071a181804020402030a0905 61
    0x140207085141c1c000280010440c90040d03401c4050b4041000d0a101c801541e0b1074032902d07030138041c040c1014050448429170b607000c992040c0d43d2660024802100541c43d01030444405013008941d02801800380e40031410382140a03102c6d840c1106010303500c070184030405d4001912001c40320102c4c50305220403480450340031001214200401c54047c0c0e0780c1903882c0000e00e0a185000c001800004004612604100d43c0c0036092244140c1304540e0079a00d04543c540b10007090a1210074044610300d1103080d948541c01c001c3c03600d2010100382040d1914540f114200718101c10b0604c0c0c12194001800080004201a10340112010b400c0011082600d1409044514807000050010300494180c040401c803129802040d00ca0080c800421050032010552081c0310500917000140c8000d00780070010001c20184002002014060484d40c1004107140c04d10282804050b0071001c1c50b5030084410241d07075500382c10325005411040e0304442d00e901e4603458550800003e901700a0100b14895500ca83d9040130075030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 697665620 1250 697664370 697664399
    0xb100806041a060409061107020f0a0b0f0904020705060403020616170109090303180b060112060501020d1d040c091e05030d1b08040308031e0621010e16210c03030513 73
    0x803024822303910106441802803815034940018440d2441d188108030030540c003011a41e59a4035104450b694070741e020b000070028041e10101420f144140c0040004054001901e14040c0c00000e070091154022803e0807690300803a24855101c00d01100010080d04501c0d800c05102e07984a4100450480e000500300385600720041d006548010800f800d00005582107020002110040d8000b0701803c1d0130030340040d41e02e60070a1394120410418140e408150811600c075102c100b039008100340800c0d205400000c0a0713003281e005203000c174280310a140302141c481d10b291404030b41019000e08040c00c0200010380d105190283d80c65848195100311000144059008202440c854000540c985c00d0020400151208890300c0006401c0203000780a41c5030341d1a056401861203030000d58200004400101c0d015100c0c2da603007000b5600c41c21589900c0c00720340403400010f5a00c0c20004520070790450710134140d03004140d03001400b6071030700b00c10900100380b01302d0080c01c851418002040d08995140d000000100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 697666870 1250 697665620 697665641
    0xe0c12190c080a06050303070b1909050d0207090e0c0a060f1202040b0304060b0102010e062a0f0901170705160305090a0906180908090d0f06090b100806041a06040906 73
    0x2c140300204840000c45118550242070154025410321440365100c01320300304091f1408941e02e00d0011501200622500040d41080d4060196040740c01c6203400a1350741d03140d9000d44c00ca140d00f09811107240e01030001d42041c0a000c010200e801003490000140c580601881e00441000107204204011540900003030009041c82c054040e82ca1a01e81400000c86444032070721411641032107908180c001001503400c0d04580c600d2940d1555076034420025042c1500b040302041c5110002c600c104507016400d018201008081e00c1c1c01c0814a507104164202135022207034580801c3d0300f44a100c10280040403250959882403e07c0e607d000704c031100003882c1d0030440d032050109540368142408800c3e49850556142c84601707006101402d4542d8411505005410005001b95424103042041c011070110750402d460300301400700714025440c1058100c0c42000c07a485201c0c0c094040b0001181c0c4800a01c091155800c41c10072641880d8545c1c0c040ea6806024161590160302c5204800100720140306080032170 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 697668120 1250 697666870 697666877
    0x50c07081e1909090e0715090302150912030a020a031209021c06150602060604110f040936061505120106031b08100209010917030a090e0c12190c 64
    0x2c041c003140040c1100035941040c070f80382d418501c14070301e141d8002691006546554400d40c4c2d0f00440607508444100c05a40065803042894101c0c42c1041e088200900c100d640a50340c44055001a1140c03076900e1058101000050784011002c001091081c440c80b694010413020205010b00e498000030010303101950a800c10640700f104030800c100b06171188410344101c074505840114903009001c0d4460b1401420341d80540d07110004000180b110004941e0040d940d000810380351903c510340b8000802140d2aa2403541ca0421601c080c030340e0741002c2468840d20810030710800300603140d42e6000036119100c1248820491000085556903a81105483d0210b003240002401442c5007002e90140418807201c030010700f1442001d000001000c90364045500ba244405644c1b9400540125500c2e80c0c183d21001c00090004070114141901000800005d812592141040340d110385801c40d4004055038803188a040400230181404e103440030040d400489003003581000343c4080c008130240c3d518180c408000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 697669370 1250 697668120 697668157
    0x9270903030f0509070f0302060706110310151407031206030212012903032d1603080928080405030303040302010504120207030f2a0e07020c04050c07081e 68
    0x50b005a4031a269000c84407a0040a10502e45100885541c0c068040139020b40c10009404084c405c0ba90010710001c0794990039a942d17880c00607299203d50703210340546003111940020a034000c170302c121503088801c6500c40650b46070210b10380e400d403083e400c46da0381441059103d51000015035209540c2032003483d070902c00826840b9280e1081419580007042c01e260140711040504c0080d2400070540312080c010825400140c421010710084001c00c0c1210f81ca1488800188200c40116075070000c1c0a451182d22014115207079000752544031b00400038004103002c4000c00c4403491400214103142d4050240304012301d40b070740f124080f9045038002c41c0c041e00581e440308140000c114000100c483c1d50b500c1c0c1d2002d080b02501715034402040c0c21364058050f0030600c0c400c680541c9000c10100009c1c000000c41c20350000070740d8a0740d52194400040340c03030301d001d13000708079140b01982440d0040d1449802910207051401000baa01c0000e2500306c00c54bc064405841d0a10040d20141000100081291103041d82031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 697670620 1250 697669370 697669391
    0x902090406090203040b070f021005131202301c09050c030a05032a03070b010303110307030c060c091a0d0606110c0d0821010e0907060927090303 64
    0x2074801c95408040114810400c11020420000c011a00a001d5180103445490000c0b412071404041c11904401e4914000c140f124001c04810588c40c2944618007000c20303602010f105a80300c551045280704c640f41c1c2d03142e04144004203002d200c840b0340481c406c11030800e40f1078042c82c20545a649082d00a0075581c891400922804000c45121020101c0c0108140021070307032220303124042ca1005481d6050000307100c0c4c90040d50014040da00380080021a52a003503282455503911100b0320080d1301180050f82c15207031000000c011031b041a9010703142c100240300b950351443e008004584081c400c002c0c50341d401081c07442d11548a00d1121511400e0141c17100004003000080f03504070380c0004248405401010380100340854401015401251408000c2151b414040340a00c03524031640d800c201d20030800d40d10842c98240c0c50381a682d041e6000744e078954903803090565039001030040c40007007400580304000ca14111a0042203185402802c007194000c40520302c4241c521078142100031903141e070480072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 697671870 1250 697670620 697670629
    0x705010605060a0f080a0603020619080a23190c020304060f08040c0b0d09020405100303020120030118060915140f06030c0f13030507051903240e0106090209 69
    0x3000d0001203618925102581801510b004e80c507540000910055400051038900290702c032900440d006096036a1302e58a00c00c42c10025603401ca50712020039030781404150a400240304484d811003400c0c40000c001a8214080ca031403d00c01860490700c540c0307046400360f424146000342058035a240c0c0056031524240000a010090500711450411007450100400b0800c02000e44003100c03101c0401d03d985030507600002c80500706d800700294009052070240880180480c4140084a00030750081000d1000c044d54074500200994105c0c46039182800144201d41d0000b1100700040d0054000266059036101a90159a03812100c070074900510301c0f00b00b00d456481d0040da025094201d90941d10201ea650001c2d04900004c0d02001603000e010410740740600c0d04000b21000e2141e00f007807602e90f2660320714200360384801c00e004540c040c0042d00315891010007044600410390354810b040f0045525849860034141c1c44000001c0307401d503201d0791500d208810a100e07040c00b400741c000e005030b9a01d43c440c0602 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 697673120 1250 697671870 697671881
    0x40512071706070807120e0111190503040209070e18100e07020c0a03080c07030206131401050f0915040308030a2f070f06020909090307021815010c05030d11070501 72
    0x4070041e0b000704040154143e0301c2000320307901161034100700c8011642c100700a4020111201001e500350b03c0e0601400550036454044c0c441d135560520f241c2e01007640d0700012925404141c4000790044004808680301070f00516074012a0032000d4104000140c4003580b0480e14101034440b0b59440d20030301024800144804150f075403090840c0000c007131050034103011513220b00342480081c041140100e170030400d44006110039801190010301640c0c440103401c070301940d541d402d846503d04a4000d084000c0f410b50046098a03041602241c5440c103000f80d14080c45081e0301c0e061825242540c04100110000b00d041000c0c500820000e00c000440c5490a40b0b4548012220f580e01c1c824a0f090000488445035444100c44007554003026945603969245003100c0640511140740f68811096010090600c20000203031103040e000300c40340d280d403941e0b5528081c01ea0400f82e0302c104003c4030401480d40554011849400e14038425002c407841c0800c0e0302c1d89882110004540d81c0c20015002964405009090096 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 697674370 1250 697673120 697673159
    0x1201030f05010f050c07120e03070b0c100504031d0315070e01030509031c0f0608120a02120906190c0501150311030328030603020d0f020910060e01050d0204051207 72
    0x4004d14140074074840040e0058210040800c94604103220b10f05102e915120100746000d0100c071450f5440f00d40040c400d801c21036541c1858412025200d0502519000e0036014a40585403200d841b803010300c0c910510039090b50720540510030311180d880d41b041400000380c4254030742c0d0b583c041141c0140713000405030b650103071503005658400c2c85000d4444603103403240301c080c43c240300c000101c02c011b1040f81c0c0007030320340ea0f8440225806880005108500344400401c00c10303440c1d90a4806661001c805941c0d24050780040321380002052081c0c610401318276000100408240c189004003684076030350b590035100c52002c52045030042010402c1003240006805602150440142d0f0070203012840d9000c00d200c10681032020440303001c40030f15025000350b003c40d02841d00900030401c10700307a60910391800b10000008034040d5881d40c000907201081c040c00c03c41910043e550b40e01e2208621001150103420003010405026400c0100151581d51030185200c0034100c50b0107005000c1c070b00841840820b050704c40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 697675620 1250 697674370 697674401
    0x60b10020c030d030b0d05150403110d0e060306011b0501020a030c02011a04092405070807170106080a1503150e0a03020a0828081005030d08010504111201030f0501 72
    0x8040c8140c0d004100703043c82c01d00d41d280c00240340308a6000a0b03415100e590b0013400a00070907c1c240f4035000e1242c03600c0d1296000b40c070350602003030b004152503583c0e441d4020340400249140d81c0e111101d182200080d6080001450b22810b8024070070158084031503030b84800c90740c1c0ea40c00140d4001681e014092001450944c3c00200103414039a01381c0e03542c000401d0040b5210381d50b941c058204024012540344841e071030069807001c8054440700c210000306421750f034980100b5041030010300440c4c440c80c0012426101032440c101182d21300003080d1881c0d0006850b000c0000e441780070300d441c20220f450303940307004501440d0100c08000c4014104821900e0003205008241c02204082c00807030b80004414410302d92202ca01d60b500d03504080503100420404000c0d5a209001c605080c03000341e413003502c29002c2c401c5c2800400d00d01e0f603030301e08041d07440c00300d4101d850101e4101b400410980c80c0591120000410382002a40741c070381502646010180240c10464540000309803c0c400e0110903c142c08000d20707600d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 697676870 1250 697675620 697675633
    0x5130209060d081c45050307122001050a0b06070206030403050d090b0a1406010f1209020f060a090603060806070e0931021503010b0a051b0703060b1002 67
    0x4071640f000e1310401050100e00c401c1c12900c141c088030f1035030000c0700250504c0ea82d2505880c581d0000b140981080c1c0c2c5804081e0540084841403105090b09050180d6002004619044260b80c80d03e61020310170700e1110a200400c00f07a0110321f1082c800507290281403100004851400308480c0c422103d041e802d19005160502021005880341000c43c4d402c503804d803d0698440140448da2000340040c000300511040d4030b0000d12210000a030005840c0e00440c500c011481d130348402c0112078a031618880b10780000c049001e41301680c00303e540210341c0c02c0d0000d00400189135010001c01d005034461b130220400a00a21401c1052a80c0f40c456000500b541c003000c0c1000d400c0607c401042c41c2101071440e44584140390128030411443c000110300c000b41d520306160714042c01e418811804d0021007040c1d0044031001480340600144008907416503010050240c01c00c88000720449980d080400c01031022400d001d80031414003c00c0041c00000c42c41410042444000901484011400500c428080d903003d0b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 697678120 1250 697676870 697676873
    0xf15130203251d010311011107060e130911190b18180a0b03010b0102010e3f0a0906051306030203100b0c061509070203030403080a060905130209060d 66
    0x4102020020110b07440c1000200329a05403100c500d100340d001c81203a4003603503061044400c05598a9040b41d000340f00012100501c1c0c001911130074255001014181c010030002c0c03005600610360140c032614050b14607902401040c00c03490032100c4602068a0070450500492020326120160b02400c182112816482d2860300c441e400c43d500906070089000c020102802010f61140c1c9002110950150414515800c0294000740103003a1841c2250281d4240401040b155005014180c0f4084507000241041c035401350016190038401003210810300321440c101d0115144103120a00e0141880008981d510b45d01d41014003000125800345007401410300590740740d02481030000742154503a0030096a80d503075035079600050640d290401c2c00040f40104000008880000d00c15101c3d1400040c407046182512040100682013243c0580060b0320803c00076002a100789071281d04204462400300d402c50700c0720050026980121018a0390f901c04041103002c0d89822480b0701c0e000074050f962000c242c001c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 697679370 1250 697678120 697678123
    0x204090f1d070305030406030203191e060b1e0315060a020705090a06060f0f12140103020f0a210203070f170d09080c041112010f030506071b12110f15130203 69
    0x1b180b041005056001c40040c00c00105001e050544020185d01001626103011484038143c0c00600e1103c2a103241480102d0b283c3c103000c00300d404c0410220984680d032030510000d0f54455000510016104806074000074103500c0da58003903c154442600504500d170305110500410070300c01407402006030700b042c100704002900103007155000c514502c1c0250f4002c1c134901c0c003034a051642501822030305150682007840400108000c0b41038910840762505264035003410411821441e000350346c030844070782c05080d03c02100c80f60b0f1902064405429601e44681d148400207080c80d4560121000402d540c03840f01c40190140301295454003d410415400c0b0b080401d002c1d86d0345e40304035440740101c0c2e942d00404005da00d0b840584451a802c261401429a1114440b004121031448119030034410000072800c020701440703405840c04401c001036515075045494822008868109007420301103040e0311a00b424105004050461b10304100a007841003802c41880c50b480b100402d8144513154000c00b20005990 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 697680620 1250 697679370 697679377
    0xe01080609040f0b011e0b2b0b04140a0b0d050d0e040f050c07050f01020c061302120129010e030a12050c06041a06041e020c010204090f1d07030503 65
    0x10664800001d0741d95840c0c403400030700c0c0c4601e01a010355400c00002407103100c0d088181c40411200082c2c00095999848001a580100c92034030301442c40044988400c042e56a40e07600d2540044000480d61040c000040380c211141031318614551050501000059407450040000900e004c1d5036044103401c2c0380d2141c58403240100015000c21912549982032550340d50400c072919294040304121600b00000c201d28075500071a03040b603c2d8001c1c8000100000010310907503040c40403142c06081b1a03603c0c241130011624041c54201d82c0300c3c0c040072031441014024456107000c2e44560114101907140526100c42c8174111189641c10494021011203413510046020203a4541c1f00501006440c0199829201c82c012a00c0b804598880c610401c401e00010300d8624482c40750100c502101605d48800340800e03075030610055480e44070740080b80b1103031840d20b038020020240003030001030400e80c44955600c01c0e47c419401c520101600c5111141c2c0c030250200c2400d660001a6005290380d5185a588546901 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 697681870 1250 697680620 697680631
    0x903031116080a0c0b090d08090604081204030908030c060a0f060617040303230a0c08010b030613110703170a060315050a0612060218040b0f15071e0308070e0108 71
    0x30101d4001c5103d402034200c1c00940d9401644030110345030000016a440301d004030440002000a40448e8002c800030411600582d001030700345250090102d80d0304403d0310041c0044082203515440040e20203403c0c4080c06115401001400c050700303000004409640004403950719040c60004d0400c51540c010720a005c01c03004100c100003403a500d6050540c0145103400e00420480d421a00e40f1450041203166980309840306e503010080c500d04d4907011125500e09004415000d1010404110319142940344107400d060701c0d000100b40840c60280d803000c150403d10f0b00f180410314009201c05c3c28451450320581c0441580002c0184c2803440e00c0e84d8010240100c0042c82150791180440c1041101d900b00602605c20520401c8502a09180c00c8000798000c122203013210b514024241820f00d020300a048403c500240b00300c40c0401e018003007120200c002203801c4040d6204004e04000140001a1a0008842c0550482d001102d40c00c0142502c14010701071410045442411b84050382c1220801d40c201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 697683120 1250 697681870 697681883
    0x406050114220b03100303180f060507051015090b090402030c1c050a11030f150601140405031606080a09151e0504080c0c03070b0d0b0a180903031116 66
    0x2440c2c10042c000403812070300302e030b040c1d00000010000700c0050341c8900c90880748280d4452110a4035000318032040f8007540541c002070008544100f01092256001c0c051246c000c2042c0c5e1043d085508a0b042101c070310102644401a041c0420002001f09115031044c6440942d40c40b481842d140c1d000039290b08045404a205403c190414140001c110f0b211042c61603206085a001303100505124014004c0503207142c1c0310788250403100d014144041421084814806074015803911100019111303c10351010304458507100748400107440d40c0c1040307c010502140115804014100390f002800841c1c000c0101007032030b0900040c00b00140303601d030f031001c0d5400442e2400036107078984007013001a04040800f64014242000b0500062103082001009ca50f4045c0040fa031001591800745611044d0505c20140a10814810b01d40004042d800030406404018035852146440709108131031a1072000f00d454001e5a0b800301c6800b0160035101d040004125015007506050001600c840801a8040c008050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 697684370 1250 697683120 697683157
    0x504020a020a080406020307140a0201020607030e010b1519080f01120c2c06121b030a0f0b07080a05130f0c0506072009070c1e12030b0406050114 64
    0x910300c01e0186110840e80440d807590b13556a22400290b40e07070041030042c0c40790810500d011340e55000000b1500065581030700600f05030394500c00150014401c00c504403829540340e0480380c1c215610b400c0c00c1405c2c0e5002c610b000b92512032207114500304516096440341032240140600c16400b8030402058115881902e10013800182d5142c21118104943d12842084221003054100316911100500d0710700b2102c0812a2035603160010009034031040d070742c2810306400c0144c40d184010f20036120140d05902c060120351110940d0303610300120159840307080d2100074030682441400d03603000c480d00b42c0082c1c030180e0511260406034075501c0c2c480281c0100801ca510705a09020030030401201c118010007008002507100c41041c140030480d00e050240e034400013078480d400a9a185401c004450294016544145013690340740e9035070050075404000d48050741004000e103030018101d100c40c4000c03841e09580104050362000c05010580306203030422030520070b46204200450b40c0e10000c0e5040703003c040300e21114 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 697685620 1250 697684370 697684387
    0x5070801140d061b180f17072402060702010501180e011e0905120315120f0a06020c0610081b040e0f01090213090803190213060206190213050402 64
    0x1030072052090b008045038140002484a50380d1141120075082c1191902d501c03100c488007150b181c0051902860141c42c04d01070b810b01621a95954070910000c1d41d804403604a5103854010702c4042c80c441080e19070480714003420b80a0707a41031141c1604080795000902c41941407003a4002c00f92103141c208009595030390f18040d0110825040650140310038040d400c240f1040114100c050070341038005803050300c18240c16010403c069001c5038490620110858004005501000b00b160300a00b0a10001c1c403a02402802c45a41407240e40006441910016640d040300304046003400c03001032404036000f40050040128003000f00c0c1050203e0380c0c0e05200ea2500d1a0000068010074050302035000d14402c00b00b0004000708154071098005000301c2d00c1000c1d01000710350100039070760f2200e401819117a050002c210800c0d003840184800d6140c0700340c00350402e203800115940098141e0720940c01a0720031302c10302200b040106009a041016000d00b5860b0561020036521801018412030340103a41c0058440c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 697686870 1250 697685620 697685629
    0x2131a04061116060816050c060c090111011410050607110f04180c030b01050d15020f07060504060603020a0503030a08060f01090b0403060e0127060510051002031b010507080114 78
    0x103c008a541c441c10165900c03124014030400080303c602003403005480744403402c680a40b0a4402c2101c8013801000c080d600c074811021035800100311207044c421030300c146440c81c000c01e000b2088603100d0340052174003515140306845007e440c1944000c1c041c44c41003000c00c0120740080200c08001200b40c03a0950600001c002041c0104880d051810860304030f421504200702d80ca040e40c0c4200c0f03005a104610b941d8940c800c01400105080c070081116081c00e1180d0301568941d00035114004281d00300c2d80c145001d030385603030042e50421581102c01307a41c1c6010520451402900d520003070f00e4150011406d181d0400000b4010481c041d1459100c0c204070381140702980c0c440c071000d01c080d0080ca04074503120365407072404002800c0b03803444082d202d5092903010801d411284100300c0510880c020a60041091a2503000c000c00c0043e000d104102e0100700e005c585912901c005801c0e9142039402966a45032444000002180510072062903906010501861540c00740c4541d06449442c0c55185440900740d0016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 697688120 1250 697686870 697686883
    0xf0d0b10090609090210090602030a121529030c1209030d1506270303051608270d02030601030b0901020c0a0308071709060109090201090b0d02131a040611 68
    0x401d00c040c02c1c540042401c01c2c1da50040e1644da17109640e50000c01607201d40030740d203000c0640141c00061340306100801405100d110051b0300c0c4040c8c2100016400e10080c18100e20185640000e180e0224203c002490302c0203021444c0600701c240d00f0483c0c19420120b4110100d84102c603546028141e0036800700d0101503080c41210000400c0880800010300043c0070b001201c84648110741c04a640e0580b0314490719866981e503026403203108094601c0509568007a5410740142e00100d0316440d00c042e005c80000c03c3c14004001361000b000202288800402250070f0301e0001480040c0990401c400900040c0c80c001140790550f50b000d03502544076510040490b0080c080c25940107443e01c102d04882081c5500890443d0003a0072540d6424501d0644009411600341e05480f1941903a01c070800410081034194008031016105142c80395400c0e0750780e40700b41000d400070200412100ea00044121038018910100c200404100041da1001711500302800083d02462050700c06006e81c0101003d1005814843c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 697689370 1250 697688120 697688129
    0x8094e10050f09030a05030c2101270605030c04051e0109020a0e040e0c0108060111070b031006090e0402060a09030813080d0c020f190f06030b040b0f0d0b10 69
    0x1166060390100100d500580300a484031240c00a091012944902c0c004c411242112a940c50312031450b21b0b40c1c002008198040c918014441200da8885003d202c10f07440c180d4000d0660001480f48212110242c1c075003150fa40c81c0c040d900d0743c0741c60000c12003524003151040001c5011900081e5550310309540d40284134a1500030080f10500000125000f5215406428644002e83e503041d201d0302c0b901d05100407a0000100039a60360321004100780f01350b110b03480c00380e4841c9041c903140403810241403015261801580020301c1005004c030030401480c40c9410101c0050100d450f000c0352613132804450340c990746006040030780070340380000b000e0b50094004c8600d50010355102400c0da9940a41b89980c21003000342e8000c4130000c1c00751404240f00c0c0341c440e01840e40c4e0342c0d17001000243c0000100342004281041c610721031940d04070b006c00000c5d940381c045049400030249524049544903034581040126202685203900c01e1994a10742c03400340d120324084a0800342c0c85818000c60b40c998010008540303005031712 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 697690620 1250 697689370 697689373
    0x60a060807090f1d01020a090603060e0f0a0e03280512010303030b06070c030b07080606090604051e0d0f0308010e24120d0210111905130302040908094e 67
    0x4e4103460560042c40390302000d07582c0301201601c4030400c40603600c01c4e20800d28070f040a0408100a070016140840c0c200d2150800082e24080d00f040860035604042c007030110300513118034107402130403a0000001c0039803014600189400c01c0c0e8112049184418000582003541d41c2403130915540300d180c1102c42c10382e0400c8090079280c0d520701d0600e00c071030021607004002441c2d00740410401d0400106481300100000c0034141060300300003e00400081407d507582016000c1c1c024026a03481c5c424411000d00c1c000e800481c1d0000c80c0c0c0c203014240d098182d214101005400e010000c0d4000b40b0341888101100d984100a41134044000103100309003400b01c030740c0d0703240180e4000c5002c05400080416035440840d400b0f05c4915800d0091540d0313405113201d80d8012025514011403e43c0c400c4004041e10742450251000150312a001710b801c0328000c15045840c00d100040c582454030f050024030414156240d9030720b01601c01010004100448030398065840440b000080c000e500011056440c40d1a9060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 697691870 1250 697690620 697690661
    0x9020307350c0715050103020109150504050616050d02280311010c1e14030601051309060306090201201b130e030429030103020f0a030602071103060a060807090f 71
    0x10603074105070f20201003100c0f1218490b200b96842c0d1040d00410341200d0301611003140c514a40103d06040f40c90300c4580700100882004081480e6071000c010380f50007400c52001600961039840c0c01c40c901440e0b1068001554018100500c00d0805801030b10014000c01d81001c030300d9941c910341a00d41c0517080c0d130480529420300340301000c9613601c007054801c520503500313004202d080a070301c06030f41c0c02e00369004698840b8000c200043e5207500441c010440d20b41c29003c0c14690566908003401202d0043e0811140907440b44101c0c81550391042c070300c50400c80c1c9550052420542842c480365141c41d03c00460301d080d0240c01c0c11941c0741c1c1d19903030115082c0250803000d0003680181d0a259450794068040c070082d5042c680d0800081080980c0c0c0600c0e6030b0011080546140d080d07800304142800610315007036102d0034070080030001640d03a00181c070001d44110804107094041004040c00c01200500f0120003628040040005140000300903040310f80351800010b10300300650601c07000c4c0844901d0440896440d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 697693120 1250 697691870 697691881
    0xd0b04021b06010515030a02130302030a1104050709050f01030e1e06060a1514031003141f05060f01080910050c04090c0e0d060e011506050d060902030735 68
    0x2030032044110340000e80e491603813548204481900600100003141d1810b100140e241a8264010200105905c80107906240d40c1d0380040c2c505610758100f00e45085110006c00420f01f40b50007956040702c810704160030900d040c01c001c10101c40d9400059810141c1780c2105111250081c000d40031440302140c008515400304200c4c00d80e8482c6d040d02c0c4a40144000c1000080300c01285070003062035480b594032400446c6401d0003142c40342d0809032114540403a8540c00000084540e0001e07a8450703410000b4050b488440350503030591501c01d9920306400fa06003010068156240e51a030281b1050134280404d0079211490490710348900c41225075200361600082c0701a454442024104440c0d44a02c1030040f80c00503242100c0c04a0044801031304080494a0880010843d070007000d0340030003140c000104501070802c1c041004041c1d51001c80801d5001070100381c055418042e0704040c2000c400705500e1410602c1c4020400c08600c01d80000c1c60800c02020380c1c82c02c00c485001c1c0c03c1c2e48000394a03c500c60815 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 697694370 1250 697693120 697693147
    0x160c032304030510020702240c0102030412120e1f020903240a0b150d1e0509010e1b0f19031104180c051318060e060f04170d0b0402 58
    0x10b4041940e49101310f00454400030024003c41b0540e83c2d0180c800c1260320f106211000c0c1016000c11091010201440002c2c620745003440130310f120f14003800080d0800445000040e0001201c0402d001c403413802d06104050000001174080f80d4108120442110081601c01400081c020907030690703418002d0044903c5406040490090540d00000001c012034940d820713004e04580d5008407080d0000c42801803050100d00701400303448046404d0f080413440030f504e030920401020414212501c480e0303680c802d01c0188402446a5400c007410300000340130740207003641c0e60780c103080344c4413401e92185081c5c3e00c0310005525580c000c001140903c4603411690307900c034a4400341130049615140d0240d89441c0025030003014118500781140d030031582680c8114249020702030f984141520083c022078550f01c01c00c90900707800c01c48094090240760300050b4161007003040ba081c10380c00303040801462540e4080c400461180d0a1625400b104c540c1d00035030300c0c03d8010020010388a0310080541c090301c081011780040c1078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 697695620 1250 697694370 697694377
    0x62818020c03120703140f01120201140a0f0807090f1203051c02041d06280510090302030d0327020102070e01030b04020f010f05090f0f03031b01050708160c0323 71
    0x219803800c0c0160034610346c40c051203400c2100c1c90810000e40800400c03071802d003420320345d80050041c0b4141640fa01c1004070145194407800090000801a00170b048080341d2018059070061081e1030700c141030b02d00e003001500d1100498003604000030803049000741054016000c0701d150403610345280703560804020842c4000d40061149030107543c408080000d40c00c4660004611400e0000c00eaa010f1b0002d0712201c0408050040c0e4240c96070320036560214040d66540c0c103070b012030089681e5403d0402c0c25403052509003400c0f581e00c0e00c1458284640005803120031010704032140300029084241d2441800100d1404c520b50b48000e25542c400340c004002d1004c1e20465611803402510080300281071072004640001899402400041d02400410928a050a002000c4c001c0081c80054078440b0400060f0035640041000c600c1c482a44805d212103400070700506a02045904017142e940c0351080d242030b00d02029002840c100042440c9000070113004a5240c0302c120078070130b81c0381a0700b680650700004c83d50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 697696870 1250 697695620 697695631
    0xe06090d0510110f040303030f0902031902011407030f2601060507050d0801030804060c05070f060e0a090908090103241e080703170f1b06062818020c0312 68
    0x1420900340000038540c2d6021942640d203212001c4d40f40c00e2840e10308400900310400969503050b1114035450141c2c1d010010f12401108050070880704820300c0c800540085142506015030003414000320f8042604014404504001410080c50f02210404001c00c162080c2e100d1350107240da00800446d500b680300d0044c1050500c42c40460381c01c02d205001c00c2c0e484840034071000341002d2040000f44600f0340704038141c446640c070500496075400d40b141c03800300394031341e40303400c403a00281043c0703010802c61820690800041500860400003480e070b54403107981d5881500c0841d4185138440580f010035046400e51282100180d201501c1c0f242c3e102d0900c8542c803c034130082d810174410315100c0400c4464010601c0c408a0358802804004080840c03407000c03242d0411030302d120707240c02c081c400c4e4480040d582c520b28180b0211000a400d051801100b04452100e07801000409100c2d0180500d00141f0403800c0039080c0c804d24440e031117900a440c45d00390082e114403001d0000b2400041481001d80c00106102c074000d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 697698120 1250 697696870 697696903
    0x2010501170318040c090801110702090105190303050a050723070801020c0703060e0304050607060501031502091305040615060c060606020303070504060e04060b0c030c0f0d09060e06090d05 83
    0x100325980d035240949a290b0490140c500d0f002140c07440c3c582d10100000c07043c0c0c104190407a0751079000d6403c403800c010000b0510800014980c0171490700b1a0003030301502c070441c2c411820380d030010b0002c00d1140050000906200000603c4969207001e08256081503500c0034000340303086c5204240d501111100960040b881c4100c1300040b642e083d06000342c65000510000400c801460742d107411000d00b54503003604c2044e00040001050700c2c0c4a41006200d400d02034000800c0d03651542c0b40560410b507000003400a114414010000140c2c0e500d5032000c2410214500410242c540b4284100104480050001c004d0307018500010b07090b411011605105019a43c02c1194070365840c0140c1e01da210840d120f4000420030041444001e00404007004001d0000d0320008500340c6a282041d004da1000f8020041a070020950715400d1004100000c7c1c04103845c00548030742018564003400c4440540034a80c04d0061042c090284c944400007030310300c0b502d8024aa149906030a05101d601c46400c0510100301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 697699370 1250 697698120 697698149
    0xe1806042009181b030c010c0204020705070e090d1407020618090a09030305011203080408031009020a0c021f09150507051501060f020d0c0b0601180915061e030e150702010501 77
    0x4c00b81d600044502c94401402420245101d80011034001405c490100c0e40258288400408900d08005100c09400803628142c000d05112050701c0c98995007014020820481201c48480c03090541c05443e49070f54180c1d6400d0320b41500c45401e10003c07031109145600700e0310180800641c0002600403a0f0020300a4600b000f03107076240c41c00800c5e85070703c140700900450041c0d00030030300107038038440190343c401440c0403208074060701c400c103a0040c0c0c2d010362540d01c0011050108001035242415414201120410310702b082ca215920026114500c2c6100381088640403040c45e900041c0210100ca0303142c0d03800010360340c103000044a8041461000c0c00341d00c0c00116405581100c00d400040c00400d080c04a48071004015615954102e00c2400103001c18100080940d018145a0721444140c000d02076456021880349001c6107a0046c0dd00254068020045440c081c04481919070840890382040c4d8038000c00c50601a076a110702d4468001d00320400c0c1ca440804022a0baa81940820306a40441038282d52 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 697700620 1250 697699370 697699393
    0x215040809120708070b1617121f031106040b0f0304050609150402060304020f1008011505130302060309160b070c050f0f0f01140703090e180604200918 67
    0x980e80d28134000c1c942d2960100d0404c3c8900c5600002602c4048006900c02041c0f86003a41c4070234a044e203540800d882c40b00d01042c55051014001c00c0154000e450b1007110703d2011048180461300c1070184400f810b2006e4a01c441d40c801d4403800c0894018000461006075603c80341d058140c0158030031502698240a1840456548403021602e084015101c0303003580881c0d00c8503000c01074554005041280d100e40e4001101131030b51594101e81800c111582c40b0010650326050b201c50000c81548072072000c000003040403091583c48644800c003681d4041c0d9025403070b44e544882491429076082d5006180980c680000101e05860360000c3c4903003442070741e003000510340d1002800f80e0000c0c0c1c0030109a00c0210300381a40880e0600f50208114504d051424000c20342011541400ea98000c180030303400101d03541c0061141c40418205190000101c2c000d0310f605c1d07488110641e85074100600b0061400342d0205241900d440c420b6428101d03800300600115182c01d14000400d605002d00308040e2550160440c00c45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 697701870 1250 697700620 697700623
    0x6070c050115080303190905030a030f020909070305101403101109030a0c1701020f031518070c060b030303100303080c071b051014031305010e2e0c020d080403021504080912 76
    0x1087c01e80e100009609045010000364003501074003040204040d4203104021403a070f1500710311805072416444c00101d500309000402d00712a031540103c0d110305610b50440c03156403400503081c0310740030340d00b2000101048510440e07030141c400d0350340c9503a052003645030a0080c401800341c1101110a001449407804a811040c1400c1c0d000c0c1502c2000c4403a003d100054010010710f40002900d0401494041e1601100c2013188451905a03058400510340d4200c420070845284181c1d092540110015411072802d9202e030580060742d0700006041040c0c440210784041c29200030740e1217099201d480003000b42d80040c803101403c240f503c41d25201b903035024a50340080e4002c40e0b01c006a1a0110b081d00d1856803407049080e00003403800707400c4403150750b40e9028400f010020700400d08031038400010784018224004262800848010007811050f180c50280100640c0005081000e40100d04101c521a500c60a00341e081425800b0b010904071440c4080000f00b04130308004191b0b503030b82100c4420a100c414800c25 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 697703120 1250 697701870 697701881
    0x18190f050307061403061c020d061b09080d0507230d12020307021507020c0a03110301050105030313260d0306050a09020703050d1808070305041a090306070c05011508030319 76
    0x3110131480800103d21942850701201c0f60400886050340e0074001c1e2603020a209080005050b11060380d01c00d40110114041310380c409460f043ca290658015080841007900c411054410100b403020000d0703040100700803c40b508045500281d00b03050a0840d4030012502c5220580325180015a07920f4601112140351090300e00640d00343e8010a0f1040380515030800829000d081b000a6201d4141c0b401d20540d900c0e40000080c44c401d900b498840c1071aa0145405c2d50340c184c1115200b500284000c40f80011407980603030480b03e0301450300045070240c111044595481031080e007041c0c0691802400f5a40e05a0002001c58006540802070296502c0564003240250300c00140003500800011001c4511b0350040b0940e000c50f0112078078004103540c1c40c0c01c40ca500c00320081b0007049010800b08200c209104882c9a4040da048041d450301841000003520340200031f291200b48402c5006940c1032144c25409440c04003280c0b81520b03095500c07003403010391700d8000711100d000b03071800700c03041c92035010150007007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 697704370 1250 697703120 697703147
    0x15030b040c110d0324080106030c27050604021b03280c110f0d15150b09041d010c02071e0803030f042d03030b1518190f05030706 57
    0x10f06600b0280040131000b03000003460f0982522024080700c52411004820340004044030380000a28a00e185004000c2154a912003603109031610344070021041d40c04400551882841c600007a280d68002c00140203020b82e65103c50400318040c0a02c003503850020041402e55103402c030032503180b100c184000054400b54030700c82000a001503ca00d001554100e10384041150041c440c107040500c6038041102d00b02013030004e8540540c0b00340b0710741588a180c484c40700071070400c0c400d40e50441c0c280030f0304104910500d10103600030f81d40c1314920300700744842c04070108400c0c00b44002440140404d1800940d642e900b4040e80b40c102108841042c402c040700140d0301d080b2515880076504641c5c80094103400703094014020f503070091540c80c02e0b0b481070850000300348d0000029014130700040e00074103000742111000300049006d40c61440e545400d802049042d602456240301400480b89050408038508810307c41c1d0b40c0c84c1a0051180200e1035200b01500101621000d0f01200c5465554440c01c5862860f00d110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 697705620 1250 697704370 697704373
    0x170706051605090d06180501090c14030d0e0f1f1b0b010306110f030717060609280902040b0d05060a0608010e0601140c06010f090c0203030a1515030b040c11 69
    0x40e10749401e00701352802c000e90160400103a41c5011003008031503144801011100d50b59602c040d141008002080e000141203461030702d41204040c00c000c81d80d00c45400d81c1c54403d0080301c0500c2c4002c1c7d80c0766070340740c403200c06c1c05004d80d0641c54422200d001e5a000030714841c401b03c0d6213540580610341c8802c038440900758201000e4100c80e4078648640000300f0740c900020910280811900081c0030554005600881341c50303940780c0104004211f200c5140502500300c0e446450100030000d01e42c1d9070321146811501c0c071200c03070404029009200e200c241525a0205004a0011600003a4040c00c10b02504a24940080522031a50b58604000b02041c05001e10404035101c840140005c5403250000c47d8001030605050503901c1001c1500703038081d0081d21a010300c07640000010b0000c43d0006010400401d00d0b0792060181202010002c0c3d108c0c0401030100301f07030301c0e03941e1843c418020803200818010010310f402070009280381e00004000d8420580418000ca0501d0813600d80184034214098414070000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 697706870 1250 697705620 697705627
    0xd0c03180c0b0c01090503030f010e060a0e040b0702070f09020309010b010903050a0609030201021c1b020f07060c0203070902032e0b09060a0e040c050c07080c010509100c170706051605 81
    0xb607400307180d80003811010b080350350300c0c00320800149040000354060700c5100541005e42d07160910000528400905040c003483d4645d00801c0300742c50901c20070f604160b01c20642c2c50282c0d203481c4200e242032640c1d03028040e0b0140c140800541460359500450042c040c0a000f40211042a001991801c0d054400105164010b450741d90100e241c0b175008142c40c40c400c0c400540b525207230045400351310300b10040000d801d03a941c480415035103031030516241c210b020f54000350884606c2e04000c0d50702d82e20700d44100c0c01480300c4134210000f15682881b0354000b500e1088001c54072414040d209441e24070481030040640d554900301c0721440507140030002c08843c4100c42c02483c0012800610405030000407840040c00b2155440000c103a903180207005e6100d81e80e940340e0ba200c41505e8191031901a09a01c0b1084a0700031104070b0300b00743d81c004c4c1103480444c01681d5208076240c00d414100c0b0100360000020700301e13110565440800c1c0c000340340248403260107080700348415110203001c01d4120100ca4240c0c0d01081041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 697708120 1250 697706870 697706879
    0x90f080a020c150306010f0809031b10092307030c03170c010603030f0e1c11010504091506110312011e0314010507020d0207080c0d15020d0c03180c 65
    0x260040010035154030664500c1c001e000c011400c4102011100d0b039150901004015065034401e181400001c0d142c5064030031810302142c01601c80c801e44200051001c001003120040c45001c0003c05100d484001c000c001c05151400d000040402c020310300a118200c00ba0390701030b8501c00003541015260818120a0a1851a03554100107114424840c03030b00314060007003084c901400c3c465500114026100c5546401000340000c0860300d441c50128410041d1400001c407080d44414580c17021070b80855002100b10444005075030783d000f6a44203c0b205800d09144190134000d41810004031030890f01c41e1801d004c41550366a88074001d09440d0f4100c110702a0040110a1074140c00e0a048000702c00c410350b006469449414609414000f003403102d03034549091104940c0e04201c422aa00ca2600c0640640784c02e203080c40d9203840c445030780c50b07218001c04200d00c01807020100b000c906000b80f1751811503a50011744072800160050450860102c3e01e8034011a00c280c040111440d2140c0d4048120307111103042 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 697709370 1250 697708120 697708133
    0x1a090f010f080a021305040903020d0807050f030411030f060406090b0a020408032b1517011103071409041802150c0c12010612150e07120303020702010c051e0c0301090f 74
    0x1c4426202090039545c40020141c499108641e12a4040e07809000ca41e602c4003070142c80000050181001c111040020300811900c00702501d422640c401c040c601003001010010b890030751646da8101d9540134080c180000c001059010070384903403146101080c160780b100e645a08078016071103020255002040469403054104207041110a0050401c58100d814421624216900c142c1d55000c1d044042e542441051221480d00390721a1142000340005021020014003d02001e041d19050062080000c040c42c040d01e410307104c64800c040d10410405040710042003941c0001e810076030144454002881440344002c04035148a04410700400c4140e060609101c0400e60301a100c440e90755a540c00454265a100022107030b01c0d0145a03456600d2104146d09011074072107808807211070380004810000c900d050740da40f078069a05810014bc65040c3c6000607625818015002490350044240c2c2941d010546c0404e0000410103030200d60803240d40c070741810300300c440518014149800c524000320000d80c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 697710620 1250 697709370 697709377
    0xb0a0509160b0a08060a15120e0a0803150405010e070f020a080a11071203080402060702060c12190c0c0308130f030501092d02100302041a090f010f080a02 68
    0x3000c100300c40400c00701074416514084203800036000e041001035521100b5512610b8150844021a8803141d114a031810348080b04031800550000e004200c20000300100d11503008048041e07260003a5510601d440c40c1038503003640202c0b40004a1071030b008000700942007031301c0740c1816900600409070260300c404006842d644c0d41c43c201c03041144034044944000950b076002610302c40382151a0000c42c0303c00d4034101805e03c0340035004100088402180800401c7d8041001030b0880c0d010340d04940e40b0201c038004903409215a21032420703280300d07104000c188055200000c12181d00c003040a0ba0b10941c40ba281120360942c1d1300c0010302080c1d040b400600200320020003d050603103544807044a03665544c81c8907000c1000300d0b07005030740c580d40d180c2840e8140000e9000c40604050300c8044954140810f0311950a40d45030801c002e80114a4865002c0c0c07901c0c026030445002d8501030148a880d280341c8001d90000c1c0d400880428014039024403400300359402034140410785001d68686908590302c5d043c00703200940 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 697711870 1250 697710620 697710631
    0x60f231605030a020705032109160902030a061211010e04020703091a0405090112031e02190302030d060b03180105130f2d170f041418100e0c070b0a05 66
    0x1340d0070044000014400c000401070b0034231503001c24111010000e421440614000c144200e070b41c00003844c0c00413003200c90f00c0007015038964160051306c4e41c40361426031b0010401c58104c2060040c81681402c14050940d0030728400c80d034240d0306c10540042c800184020b80c098000010045405103200703000c8901d440b54016030310140485403d0800b0f0f13440e80091980c3d442a0306c90708101030319403c0700e42030582c0a1081c94038620181d60203441442d03841c50003550340d46001190301c103c0883d00c05000c101442401114414080d4003414070203180c0301c0d0110020396000f40c400e1060f0111002d800d803200c01d13042c000c0b648550a50301e00c801d03155031161540d5074401190202180c01c20f020504010056403071105844c051480074044910300790720352411410003401b44481803002c62013400300380400c034042001c94054800625103120b03000030f8180410540c0c0750060a0340d0510410104000160702480030500c100c1d03000b40070710101074a41e150800310782e1298603800b038860803440000540c024016001944c120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 697713120 1250 697711870 697711891
    0x402040f092301030b1501090303080c0309070b03280b01170c09030303240901050a0909061104060c03020d05030f04020904140609100b0f030307110607060f23160503 73
    0x8406100240b1804002608212058482c000c00e0100c0702219000e4100b8110342820540882803c6072070142c45844010300c0146140c10000024440010900022008000b041040d03526810200f000f0940c3c144030101240100b00d01c5d210740070b41c800311805255001001a11000d0544100341c1045101e4140103210104040007040000e40f561420401036100b00c0c1d0310550500340320424070310700400014030462184200b1000b0018020380d40e0311170a24003205c080303610018140c551840d103140903017401182604481e9020030004ac4141d00952441e41c0b01d4407e6082e2000100001004c0e00c03e80020b40e024018140000300007401030510074801a00f05000c1d28481000aa55600b000d180c201c04440341032244e0416440c1c46c5010f0b201c2e000b412090501105c111070321605a4001c240d030381c01101030141154040340540a856142c0800b180d4005400001c02d0241a4007082604003401c6590b03001840383d40310003101d5800c9500c5100e464000c08004203001c1401600900840d843e400142c4001c022 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 697714370 1250 697713120 697713161
    0x211104050709151211090307090b030a0209040c1a12062137080306130605030a0b0108060106110d110c060705010501090c0212030115180914060402040f09 68
    0x81a803c0307880020004000d545401d018a00302d5400307410382d401d4801d5140c058200703000d01080c50760702040c5070040d5032800c2c00000f100d04408000038608004a08080d42010382141400b040c040207200350420f0f17403485a4000346601c007002c0207400030710030104c1801d032644040021581d6440d0070041441200203100c00d40c4052842460503d04101000d244500060309400110b800e0340c1d8103c100074910086115803600d400d0490300c40c07558601c002001944070351107013020b0318210041d642c0900060000501212841c00e41850940c01c0440c0038040c10116201d50400003c000344680d08074245001d12401a2240b46003030082605d165440300e0360030078503010b92003221405894031400b91580701c1c060b10000c030b081d5260038840021903c0c0f140c0414215004040b16001880d03186040300d0450380c9218810307140d9180d5003000ca03080840741c0300800804c0b02c96200000c00e42050340000c0c8241c1d80500d1070b0300040e01c41c0c0003041300324402c1e449490107500400c40c003080285559400b003410f02c0e0f450203040c0003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 697715620 1250 697714370 697714379
    0x102070b19140a09030b220b040c0e04110405100504050c130915030213060b1207020d08190e282f060f0705010e07211104050709 57
    0x5140e0001c408103003000c01c0c81000c0d009282c2e48910301d1000e001885016074903114030207400a000c120140000741c161102500441d0f040d46035900c1c1c010f004643d95903030402c4801c0c146420b0040c0b640c2603405031440d10307200d0004984849580465401640d0100d034001d80b0f143c154041c0405040002d0030350302d462280a03000502611240221849000b0001440d55aa04094240f9420308107982200d810a0319001001c0e511110031039a04054940464042c40010f003060045000f800300c0f030700100c0306140c011440d5458400c1c00a0b200b030040f03402d03402713880d52150b4525080340da006048031508c0d8900d08100300f0b01003102490f403101c15003000c1501607401041c0044a40f80035080980704501c2c004e2480380b11101808551290312900c0f0a100c0a000f820707034400c41d00b0008400e1a01c0c18a0300c146400600320b40003591b000b0407215100da1243c002e000f1180710210f002d0711400c4510860102c05864100004c02d22484c800e6050200d90062004039444ac0e0301c2c1c24000107110080584050140d564030105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 697716870 1250 697715620 697715639
    0x60902030a140d0207050a1413090305030114010503060f01050d0b03190b1b0a120221070905011b0f0c170709110a08070e041e0902090f060a14010207 66
    0x204018010301c455074401184405a0349080f464041000842d000f440c0140865503c80c510399040f40c040c2010701100a10500000d0340005003142d480100c1490300e904501015009400341d4101c810080810301e804001c0001914a4401240d409e580500c4480301c0102543c010300150841d4003988200140031b02d0b51001091404214501a5441075072041300d00741003018103240c15a1119511f600303d10888a468240d699a000703035140a8140107100080f07511000c8035505036440400680c2c80320040e40304840020f40e40360810f4031074100040803840040f41a5000c1e50401d0f00665182c5071208142e041030701e13415090031012404540c0c41907440000655143c0340307405103188200140c050301d1424581060070084030314903013048000207002c0c03003038041d225085103060343c0c0540b10742048402040f40c0c800040050451401205078036000d00c80e031600c4540c040e40140c122030f10a0703d010300541c4496621801420003103d03015442069100140a0401845800000f0b0001801110040b50311a0080d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 697718120 1250 697716870 697716883
    0x109030302090a08010606050a05220603020703080a27080702120313060e062208010f151e06050a02010207020a0e041109011823090303061e0a060c06090203 69
    0x980000381c0102d44400c16242c807000d4074000308084002000380e01d06d40400949a0b000d0380485005004020801e9440c1c50302441c528a1030762140ea822500c180c2d25102d0140007500301d5641540000d40000002d03101007540d120307842042c68117808201030300d0320303100000c074180c503101d04219000c900a101050040c2c03107000c0e0354044a041c04001d107427500300c22000c503071211000e43e00c9002000003030402e100d000c0e00e50350103d82040760088110101d001414110891400a6901c560803940c03800458402029103075200e07602e10091031a030450280e50302c0402c10303090210141d00001103000c031401004840d018000900e010301c2140005400c100080c0c0024858203100d900401c11510520200003c00101182202c4100b03821103030b5494950604a5a00483e20700350316090245948001424407100c03072521046180c01d180819aa06160802e01c441d01d070b0308107139419400340784c03040e00040b18004203190720408910040c0042800b2481c101003100d01718010700703050fa219035407600d1207005603e0503c43c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 697719370 1250 697718120 697718123
    0x70315170c090705030115170604090203010e07180c050910030504240903030506060a02060406050c040e190c050c031c06090f051b091503040215040e0601030b0423090f0109 76
    0x4e0940701c3d890400384420000e0141001c404004c22035880d0001078889240300c5420100a54001416241d5880441d00504103286150614818000000b41d1b0240c41d0343c0702e0368148403801c01401341d081e0500017a1554010118140d84c844111504251620f201c0d40c80f0360b51080c0102030010032441c0e0340f00c042261014040c00315840c1525034444074240f5806004143e0010000e0710f4452418018400087d01c81c103010744010419911100400c15941c445801e94001d00501ca6070b4600604102c0c10069a01c4020035544004034205801303940242e0040d41580c01040c8038030051890138881e015a0105504001102e8070515982d0341c020400084901c07071a002c204805c4000030702401c0001044223103a2200f0100d4121260401c0500c410b61642c02c007d036007846500c00d145880344c40300d10000c0c0a060444c0d4801400340c402280000741c080d02001d21902400082e2002c202401402c0d0a00042d10384601072100d81c1c07900e890012480b90070301000076174400e12750403e0300d200d29800d01c40c0c5030a42c1c002110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 697720620 1250 697719370 697719377
    0xa140103060b100903030c15060510050d051503070902030c1b030306030c09060f01210e0619020a0509010e0127031e05070b0f040e010e0a05070315170c0907 69
    0x640000b541000c0c10071040d180780c0c81c181288402d1031583d008041000a01d4000c10002c1d4504440002c4102500b1003406060010080c07603820160000042030b5070407100601c1c80250070a8045008240d91024440303940001502400060703042803000c4000e580040c3ca6000315041c01c0160790b14203c0e460550b226240020300c0a540d59041c0781d41007614001c502f40ea4684a150514140322460b0740c2c3c4c400b0020760400031709001c40c0f00100d01d00f4100c190111070b03960010842c2049445680030001041081c41202601e260300d1955888115040232401002048008180c08121188440d80034256031002c84205241078400c0d8051044e14080e00103500724100119408a102031040007a0fa08031550403260568805021981079101c80b07a8943d00b07807107105c50132100000c080c0001080720f82151b000d011310750290400c03035945400011090345e08644891615140c0300104060718441c1c0101d02d82122005507140443c1d0800d52548a842d8640c18140d020b4440d410000c1ca1948807003203018483d840644 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 697721870 1250 697720620 697720631
    0xf13141501090e012a050409060312090e070206010303031805100516020f07092a0c0b061008010b0912010f060f060801031a0622150f06050d050a14010306 68
    0x50a090740c40f15402c450069040c812019008944010759051004a20002540300700c03d10b402910346104d141c000116160034164080280007079100c4103172004106544d4120002c2d510403c0f1091800b00f61030070801a040100100042446a040101590b581d0422030b500c0001c00c0d42e0f5185011401002505515113820030040d018080c07140d05c402e859801d00141c0148501c102c011500c41c9403034050b100040d41d4030340062022900360308103150484040032200000c0212064050300381c10808804961141204001402030300388426000d0031195181c560103007036420300ca050585a04141c6640340c00030b4a421441d0030103c0309000d000110f11040f50000391207400e04107519000c0d070f0150003100c1400000303001080040c103c1150180c112145968002c1c09440313550015002800070842c091004400c122810f2a440969001c00d0a41c00740f6010328003c40d980b203c402c40303200c1191150601040e400d0050080c0d40309035410070380c0d106460f500d00141610100b00301c220400002e0b001075a030195100b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 697723120 1250 697721870 697721879
    0x30d12060506040e0f1026010b0618040506120a030c0c06090602060c090609180f010e091009080904111b120f0c0c061606140f13141501 60
    0x511604018240941d41649400d09280001071151009009000352005d41030008400e0760101c0e03010005010442500700c024101124505807031180382c41c0d009259468042000701500c0d0060440b4440820a000082c40d01c80690401c802003038014801500410a1640920780b5142485580160340c4291100b0743d00c0115801c000c0c081c00900d0b04504117100011405002d203540016540fa44030000312008c03541c0310500d83c0886e095018284102e90407001d421100540c0c0c0800000c1d9a124401d2001e85810ba80c0e81c038602c408401d4020758039083e5030b41144290319010201e94000c0e81c41c080c010a1041e25180b84280441d086440d41c00e00808105800708950601e440142203280c1803071040c0303004002d100302c2e034101c03840030b8490b070041180c440d2000a161140e0820030b01c075201c0612001004991110020700100c00118505501141c03494030744854800101400003c0c140282ca02c200503d81d81d981e842c40c02c171003528061605a840820301000c10040d50020441e401d040c0c00e80d500f4248055250 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 697724370 1250 697723120 697723157
    0x30c0f0b1e06120a0f0f05060c030105011e050f0a0c08070605040201270506090d0c060917030304050c0103110f030103030c1104050402010c061a060316140a0801090b040b030d 77
    0xb40240d8801d220301c61031510992070010380805840d0b0030040451100e0380c0c0b890b02903102060118010024020101085840b000d80e50145040742c1007a00e60465060300030b501d0380304030161405403001150007880352160030351055001c1c26007011a03040c00140c050003038851a003207411655045490341c5d250780800046581c02400c0403100500361804e82d040c0d1007069101c20384007045000380e6010300004034000c0101e60300d440e40440c100360081c3d51402020344880005060803c1401801500102140344c50302e0100300004681c0310313070b1b0840701606120300e00d0b000440c0176241c070f1000303030300e2121083c0610100400c1c0000210300851080d111045040103900d070045607001c200303500a1003249171104101c00f40c2d0f00f0020184509078400000640385092580c00c0486142410617141c00c400084104810006603540803071141c90603807598040d10100c5c180c4c2c50f00700e20031a0066000a01030310010400c144032a00202c0742860005c01c0402e010a100c03010a28202c0c8031300d86000054160024120303070300d14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 697725620 1250 697724370 697724431
    0x1b06020a0f0804050727020d050708010803040e01050d02040b03240a11090909030c07030311100c020a030c02060d180c061b150e0d08010e0a1503030c0f0b 68
    0x1142c1051030031450103440305a1070740001c0c0300c1c0c00003038502148031040300d4a403071a008002c0302e074980003191a010440c88110082204507a001e002c5407110002148546002060b50200c8195182901140c1c3c2840f06010b514402110b00302d802036220603480c01103543c14000c011100c50840c036010444910f00a0b02c2d10080006070031301040ca031070002490400300400341201e20404041d40e45446945541c803180b4918840c3c0c0e0000c1500c0c0c0203c68022040640c400d400c40b08a082c0b150880c1c4032554409071074001c40c0d40315114070001d41d00413404107002902807144004028001030016042500031018102621385000700082602e0488454808120000e01082d014045a1922500903011031548035603001c0307020409800180503065038403c00395190840091640e10798240e03a5100d489840240240ea000e00609c0b1034003d0030340001b14080b180b440b41e802200350303048034012006c0c07450705c0c2503c00182c80c10b01130b0b0700c80395410b9041e000b05000742c11050007911080c907400c02501e0034808040d903d02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 697726870 1250 697725620 697725647
    0x160e1201021914091c030909152d0e191a12060f0a0e0a050d17090c09010614191206091104050f0310090f11010507030f050a1b06020a 59
    0x83c07003401034041944515070148040110b500310f807400c0500508080e2504a0386510208400707090a00c9141044c0c04500d0450890f843d9126200c14540c11141203014107001e0071418056130074020080001e0001d5503a10342d000071340d2542c03050242c5449040314041d18000079200000301d2a21002803614203000d1094034000ca10100504842c0c00c0100d101a4240b10140151403680c1e1107070005040c11606105416040da8003000711040c81c070707403024003030500d4100c54480034a81d0110000149450404030f03240f40140ca00034001d1800d41c0c00c1c4001642e150100c100440e5840100f4000081c480d038044112010072001c54403000d4440000d000000f09803085c45e00f10380c02907410500d1070990000280700f51410ba0f0b00c1181d050002e100300c200820329080600001022190a0a207550180083c141902c426240600600c2a201090728010345136440b13101c4009000500c10845010300d5841a400742601c2e24051500d03d0604046d5500011115081603040d500c2560000b0071b030381c070150000d800c3d0600c3d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 697728120 1250 697726870 697726907
    0xd0c2601061101141612020705060619152a050f06070e060f0c0a050613020312040819060612150e06090d05031302041803020d0503160e12010219 64
    0x80c05683c01c80740009601603c2c01070403000c0b00c02d129101c28006ca4201109a0007107104641300c44203400e20660340c09090301c0080c0100d07402d400c4004240e5020003900b096410104103080800d02102c0300b00c84002d07012110030100d080b1129403958a91400c00350340d041501070340040078242403442c0b0080c01c040000d0035800070310100003442d18071a01c0b00c1c01075948058961014949072000c40c04001d05240d0400c10007006030042c6000c02c0b103000c5c0c180c10b4107000d00e80203404840c01c04410007828101845140140e41d605d600000c49900710380c2c030800110805a105020104150b42d84640035581401049811644503013086040460705a180c86410106031a400003410b1509060b4001907c604601d1920301c10010004000f5112141d1111840302c40f42c4d028104001ea801c08005480d5600c5a0302c108800600035240c9d40da420034490000e4a00488400c00c41c24040c100200b01a40c1c0d0b00c03640c002c0550080d292004418041d2402e2014100c820040d490142c840401142e000300b112008508140c0310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 697729370 1250 697728120 697728131
    0x309010b030d14030a020c0607080a06050f0a050f0d06061203020c030109020d14030f070c030b16051b0c031603021f0f0305091903050c120702060d0c2601061101 71
    0xc9903201d01d00740f00c1801d418070816500e458441841c0d0203440b4148902000e88240c406001c0180d600282403841780b1401a010000303252561b0400074101c0324032030000e40c0310f40882404e001d5880d240c03800c2e00040c14014404408078015540d0307403003650100d074485165000791005110a142c0c0611802c1400d06049008001580c601d41c0000c0e409680d80802400002c503222208810110810842c0c9040103010300c4e40d9120326541c0740a80801c4610700003241c54201c2000420202000340800c4400a43c6a0701d40d079041010850009a0071400d10300d6a4106100f0000280c4241e2001c0c0000101c508840340041c1406086005021143c280030403444d02c0503108610f500c001903400314903070a800d41a0310300842c882e15010701042c5403003191038180c0c1c0c1d005503119048003015000380040070051124400e9810212a43d0848001400b5420b00070350041e40402440d2130303501c40da50150340e401200d81030401a40302084e4501001c10407034600001911071500040c80415044000b51384555035a1000303000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 697730620 1250 697729370 697729393
    0x240b03150312190c05160501030c03050907140307050901170715080a090c24090f1404020918040c0812270105190210060b07050a080a180b0309010b03 66
    0x48500c151500b4460081d04803200701c000f80d201c4d81d10908041e401c00115100305404040e00140c6e1021889001e0220785001e20055125019001e0180b1400c0108040c00a1a1412408000c00f442c04100c041d03150140040106e08c981d42d1320392460190001c8400d01d4070110031a1715052405e40d41c3e40002c85414215010310043c01d0f44100e81c164230241400d4042a0220b480c0741c02c0701036030350680041c407500d040090380d0fa08000c42000303d0380342d1499654a9050142d911002d03020055114050040e5030002c001002030b06041640042c9000040034003000380d031140e0f0380c044404034002030303400301c0d0010668070040101c0351042000503802c2d80c1401c0c04a02d00f194081090030f02180360344030302c0101180311700014007980c0183c090b107807210a4200020407411078920000d4403090545101d0448915103030000c01c2d00348241e4265440c80707034081e0003890540c2840e10f580c3c0c0e194020441e1401000911a420110032043e00c8640b001043d1804809841c1d040022105095800100c0c1860099010480ca441e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 697731870 1250 697730620 697730653
    0x304180b040605190611100905010203090c040506030307031808031c0b0a050105120a0f050901141b1b0109060c1e0e06091e18060315070203030a240b031503 69
    0x2048170b5003410121000c0351030006141c01d01da0341c0c906510f00305141c41999401d0002c1034004502c100200743c01d8a10441c504020402120001d607003082d010303401807010000083c01610f880356950400071400451680d2040028a103910100d08560011a001c01800c5441014040c40000d41d00c216100c0018031b0904000a140c0c0c010040c507170b00d048000344080350380150503502c40114180301d000184501e240c182e90076070181ca4030001d0f170000401079500242032455440450045107051a0240f440c101e00da8454000300124480b80b0f42d0555690406440001c62500c00c1031482c61554980c040420800385011072143c0c0442c1c0c504080c041c07481100c0e51035980e000101e56103140100d9240721305c500b41d4180c02e45010070100a03160400c503400c4c0c840c143c3e02e10418099110310012411140304410318541c00a02c46815200320780540d10a0001c9030407188280c01c283c80032000a0145100400140d84418442c00c0e10ba100044811000083c040300c0c03015180014030240c425002014100012101d14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 697733120 1250 697731870 697731919
    0x506150111120904020d0e060c0415140f03040c0f06030606081302030a17120f2203080403030504141f0506010c1505100e090d030b09010302210304180b040605 70
    0x154130895000038144020030b0a6481080c8000c1140c048824a240268200340307140c6c0705000c0d00c2030518400031148011841410b41c40d900b215840340c0c081c10081702d8903684000c0e82010300211182c1442e01d0b000300300c07400c542100700018580e907070300400c03130500e003107006064035101030207080c4103130896590070000d03840c00034a84541651040c90240380408070ba83c020000c1c0038200b10104810307403200501056140520007036025165100b0488024203092206d0743c045580f40e0001401b2030003680001d00440d01039480540d0042c010445d9052501c3c1c5000000d0a02c90a080b84909840510740c0a100c10b01281c800d00360711083c01e007072030814822070362100901031107404680c00c500e5440d100081c0c0e018140c1c0503250f0040c90500040361550400000da1503e03000041e4480380000d2520a100100b8507200082c0c9040300e8000c3e2811003160003120103046c104c40c48101008a034403007000001a0401c8601c0c01407600345080300d0014003008040300700030503200d244d44024490040d602201c0c100d00c0c00d14012 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 697734370 1250 697733120 697733137
    0xa032d1b060e0a0809040c030207171818250203070615080106080303070f080f0609041109160809060103050303010501050a020c062b0e06010b0a0903050615011112 72
    0x4404060100386041c2001d084482d1a400d054050080d0420801039031601419090104480601c10000711000842c106e00400320080c00300c030701480003241c2a80b080c000429000481943c451001c0440d4000705000f001c0e149030004250000404104001400380d0340d260764103018188604082d942240002d41d0380c050904007030034183c0e0750450100d0080d000c1d41d81100510b00c20000b80040d60f601c455881d102c0c0c20440301500403a446981d020011445400b030b513842203410200c6007182d6140e100034442c0c17035003005008a4040c811540241030b00c1d0340344101c0c103204040348407040d030200000e0b9900501e10b120290a40010381d00050040c40020f1011040c1c1c0d041d10001e19041c0d80729458203004902d06600e0a2110f50000700002e6200307248503000d00b05001c40e241d1400103c00001c0507450704021203004061951350354100c0310041c00f0404035000100103541880c5030135a11315849868a5080140981e8030100f0080544100300440d41c0061003407041c02c1c2e40d0030160001b6070311000a60701c070344610b428 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 697735620 1250 697734370 697734407
    0x50301180c0f050904090c06020a1509020a06030b030a0f1b05010e060703230f27010c02131425170619030605181603050a0615080a032d 60
    0x4ca0369507640711907205102554100310100245942c0e82c201075101d5883da071041e14035080c6070400b9006080c0b94044c000c40130398094105400e031460000e04400030700045400982c1400344a4503130010a81c0940e025400d213000b140e09042d4801e0034503038600c00200c1503101d50b06100f0216010600d5940b420b0640d0f42140c4c150400c00800007864041003600c0f026507018004402c004103042c0455440741000d040b1603e000004955814850b0500301082c0d582d1000141c002404c01408000604103001e2200303030048003c1000c83c25a0310121a00704403517003100e00030140301d548004403040000402ca1960f50030011b0400d4912540d5946e00d8407a075440003400d030740c021480322040c190600340c100030800007150003802c201328a00f000c0014100b090284094004d443c4605c91300172a80c01c480c0c550a0007101c0d441001442914925541c50003e40400a01d0081c7d10303229410010341d0740c1050149420b46031190b6207412400090403a1480042801200c1303001207114440c2d6583d559421500c0113524101040c3c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 697736870 1250 697735620 697735627
    0x507030e1b060403290a06050109051f1d0a0b03060f0402040506340b09070501020601080d110307050d0207062a140127020307080303070e0d050a0b0106050301180c0f05 74
    0x100302156035000c0007040c42c01804031700400003140340d01d0788508151142603990141b455610020402c5c400c100d07550b500700d1909031201c80c0060500540a0b081c405640c00030308240c06041e4000201c203020658849461101c2c000b0400100b0300d003980200c0704001007100c0c21030411f070418010414074021008a00c060f100c100405c0c80d64104100004614440200290560010140b9158004500c11758400e241841161000708442d0f00215019041e5500d00b4020b00f01210400c00403111048505402269804104003010210b1001d004510006e103c540003032880c281390080041490742d00d110042c1d142e1040310f03403084858014507442000150445010b889403148050f42074010216810304294120f81d2000e0050340c1d240c1c904500d02603070b00803000da401090780e90b00c48984a100c126001c4000950403c0c221034a0300d0302c5070a003108640618100d4400102d2560390f640388000a0300102c004c02c101000410251001c10003101d410016468240401c2000100241000c80c500a01c0c00c24001d011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 697738120 1250 697736870 697736903
    0x30c030f0708090a120312050702031e120f06090112020306040b0c09040608010f0e19140a050303090313170c1302160b0a0b090114150d0507030e1b060403 68
    0x405554001200401503900a55900003070142c9241d4102c2c118081240f0845038001ca087c40e204441c07045485402031807401d608102c14408049070170301c060b54030a200380300e52030388590307c014494859600b40c90706c2ca240c0c0c02c203041006550780b4141c1c040c043d8409804554070040e00d02242e41e54116500981c1208982c59645803181c06002d0420503a40003494a03200040906054000c5140c0b614080e270204800480c0010880d11a94102091000c104900f140c10000589441ca28410302e2410760585409030788039540c080c190350080c1e03040703081a400400c40c0d240d000207005c908802011250164030804500d100034648800d103a901c01d40c8503103418040c0855110b9650116200d4078078003203d008504800c2c1c03030b0900003040c00355400d04405142c0084029181444030520b41038804804903c0300d0a20650100302c5182e00c0101c04a000e00020720103c081d11280380a441d001f0086510045140f0071030019007850044814903228078034030103030355400e00342d22890100d5041d00c2d0441821052910b50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 697739370 1250 697738120 697738133
    0x40311010c1506140a0509040b130219080723010e0307171f0e101e060b0c1020090607320303041a0703140720030c030f07 54
    0x74050020300401940b41c101200580c40f80e0240ca6404140403a41c06140050008449640c010170b42c2104080d0081008584030240107a40002d00d041000d040030401e5010030001410340d10b403003080b1608402c043c08100310600410300540040b8900303405e4a40b59044c0e9442e00e100398503c85050041c1e06428007096107061003480054126250000188502c16100d1030f550040e121411160446407a02111080b245018011900c503208000302140ca50b031a601c400102081085101182c1e0541640010380805018060003048100b1800703880e070b02118203d0f030170848000c113403000e1540703010582e1141c0c000e038000b4400800142c2c2c3e40d8586807090a404a0158482c03604054804401c03241d0700000f10a0340903851003440c140034441e1088000000080350f03240010351b030081076212100601c8520b050f07518034043d4400340a00d004510800725030a0180d41c0c00c4240c0c0e200002441e0b040f40c1020321100c2040008400ca0f484004501d09100c1c80c14094aa0140b41c0e040c890b1a07200265142c02d0004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 697740620 1250 697739370 697739387
    0x5091303032004060e0909150f1509040b06180402100e01030e0610050307090b0f010c02040b0d05010518070e010512150a02040e010e04020d12051c050109110301030804031101 77
    0x42c2070502c596181c1d1501d1024140b0082e003c0020321403003400c400078032900d8002c9004000b11020302d411a11945822003d01030445004202e030841c8103104010b40702959903814038501817401030031301d0030f0366042c91003d0002c201c0c03000d011548000c00000070300c030041e1a544043d29800c2024076254031206d102000490240c456052000618840c90b020b001c0c0034030040600740103c0c1c40840480f02d59a95503440c142c11340365182c18160388003401820006880d4020048140c10340c1c4000c0000510321103000018040d4281402c0543c4d8907951402086508040300600b0021a04050300414a0500c2c0c1651040c01003014000c1501980f41842021100c49042081411040075400c80b0f2901d1300c1c00941100007500640300703900711882c0e080f0000803000c0d1850203883c01160060070002c10121030342c0341c00c181d940c9080840f40070010100100c162214045101d2184403240034004240d41d49072048900566000705406074040c40200010000229141c00302d03001c41c2e41c8018040078240e10140141e42d40c2c0e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 697741870 1250 697740620 697740671
    0xf060c100501090c20070b090a0503060a05041509150e07080f2b0e0f360a1404030f0e0a080f0601080706170a020f0c07030c0509130303 60
    0x381030900125524807140c1100d800d82640d0790710500c10810042c04c03040c0e05640c540d005c0140d604500d9081c00034096030f400401c0030520140050300b0075983c2c1d00200780351a6040f100011140da41d5401d00c0b00704000c90b40031003800461108140642c1205444040c000b48150b0a4801e92590b5100f000808400030711002004100312003c3d158180c00c0c03081c0f6140c03038004220303490400c0c0c0c0030342051150102075245520080400e80d5200b0801d50210000c2c008070664a40c009603100300d005900070304240d00c20000c01165201c01e070994030242600441d400000001a011060706c5007000020185410702c10080ca41c42501850049030a06050034107851541d12051a6a04281a01c4000c00c04000005103690014421003c80d141c0781e9880300c0c40e41c1c03102d400d40900400210b0354060f01c0350180e40c0e000c40300e40000710b1078401403421480c0303095200c56500203024003820340c000443c104203100f04141c4c0c0c0e4004217000d60748900a4036158094145007000f1b04002801d16903120203888442921108008030720 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 697743120 1250 697741870 697741903
    0xa18061403100f0605071119030f0c081f0f0605030a0807060603210e010e0112020d06080109050d0801080a1104050c07050d03020d0c050c0d0503090307060f02090a0905060f060c 78
    0x150744880c0005c00b540e010341419240d58146250700c07032803400c15400c13501440d00c0900401800d2811641c0d00012400f804c0025240e02d0416000820104014044910000220036a4034090350035030400c6025a6403034501d4040051030302e0401c004980b002f0a25103000c507480011296502021716011008101c0c5400240880c84018000c0121071490321143e40c101d001919100c1b000440700b0011509900320044481c00503803484402136084030580c02610b401d4a02d280040341c3c40d40c031201c41c58215900c08500390b46e19406040382c0150b103508103201a003d0407411014015605107900c1c0c440b10103401c0c075501e6000d5540c440c00603103100c0e035100540e5a0b0561007020703070340b100b8007188004010b500a507040c40842803030101850440f0740200c00311440090020064401c240f0005c3d400c2d152074000a0403040e80780400c22002c07001480c42d00c80d401e5105280f6800585a0108a05101c2c1d00315190300410001d42c606030502120b95540c80340c041d144c3d00c0455070175503032b19900748102d4180712500c46481d044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 697744370 1250 697743120 697743149
    0x5191b05030a0c060605030109021e0406090e0703021801060c1e02090a05060f030114041203060807060302040906050609030c0f0102011104030b04060c180e070e060309030a1806140310 81
    0x59000d240403400078007907041401717403c1c3c44200301801c0741c0035210002e61000701040000d42c1e1201d04040c1480301e00008000040c0700b550351200d034042e91a94075081c880d0742c102d03110902c21031800e001254540c0c0440028103907990706095002e0f007494840c02000e081003144200110324841001010700d00f20f80d002c1d00251560030860074070005400151409881001881090741705400c0c144070301c50308507206256918030f5840319251258056491042d41d0308154961034003041c0703010204210002015150b40041e40d0302e142c205520225075858001c244110750400c045520b03a81c00040c02944034404445241e02c1010100c0103030b0042001c43d8130324074a02e10128001050000450580c1c1c0f0070b034000c0d841406034181801085501e40b2030707041d094030b18080d05c20007840a2504459100d5105141d0f007496600300082d100000e80e60341084030100c03026400012002d2815034880c008840361800201e8049109051a5001e0452030340e10000e084102c00110002d48050841403805000b030035100151800b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 697745620 1250 697744370 697744387
    0x4060806041d03071e140f0c030109030905130e0d0201091505060a0b03040309051801080f1203150d0215040e0117030a0e06130602160605191b0503 65
    0x2050125092445a840e00c00ca6100008004204007052011503016500d4070302c40d55511606005060a21840d0b1000b0020b0080001c0105018800c80e154200c0204440440e0880030381c54030300c00b2002e0600a03414808540d0000740c20a0300841500d0080311600216014144010001c0c001500d03a02150700c2806003904140d038040d8444442c880c00341000048038040501c9030000e0311001d48005810a80c150002c0045e25072082c040c40c1c0140c42440c0010202e07985070b0000d013410b0625a003400d540a01c40300104440d81b000c011160001c200f400150413840083c0920920034080181032265900c2d03810003402d4150741d564038410850b036005021200c0314108848440d03250b0414050720340403a148800101c1e80342c3ca608a03110020120310011880e02c1300d442c000b00c4da101d110b4610903810001c207001c00b0200100901e40c50000c1c0000d68020130b00190503030401420021564800d2061010070013201102c0b94020544a808544d18145a402c50406204e048610401e1420181c09070202086045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 697746870 1250 697745620 697745627
    0xc010b190501090f0b030610050f0a081509040b0406020a020a020d050f120c0706120204091e0b01050a05041a070507030c081c0503070c110303070804030b1e041502040b0406 76
    0x5450307080c1d80c1c0c140d0f880e45070500c451001c03120f8014841e50250520004070145000c1c03401c2084890b2500d0500d0604000c070803588560707086011500b0208074840e00300964000303000215a0ba001048540001c0d5040c6510380c0d0f880d03018050405404a6000506080820700812031760f2001e07603015110b0800107c040c20403a450301f584500212003030103418114000ca1402d501074a40d00c90100010b000c0301c1c0c0c903148007070b14240f113007103002d2103119000c0c0b000141d0000103100c1c9a00b03000e44400064902021400a40308564070340c2c1d00c2c035052050a104c001b0b1403692010070342d020740f14050080d410b01a040700002140d40900d0200800c1403041e4900030040090070041c2d80204c40c4082e003102c41010b2141d00c88408002e4a6804200156090001034216032041801c804402e0003a02000d014462500101b4155030200c2000d440e26000041c0800c1040180a07a1940c040624091440002c0c030b12120f060b00184041c20213015000e00542d220058001541100c00603d90149821b5135550b90380c0c0048c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 697748120 1250 697746870 697746919
    0x204080706180602011119140a030209030c0405130f0c080d090e070207150f2705011d030a02090702010e010204150f02070b0901120e010603110a0b16080c010b 70
    0x100b0300658603403001400c00d00502400325016002d50056040c907015854040071703051680d5544c4104004c0c10710154686e002c8000504e81c0080a039800340e0745903064020300d450b0881c440441c5d4016864842080403140030203880b218030399441412000c1d207800c582404200a8800d0300a00d00601400d02020700650304000300c00116640b245081c034059803042e909a0301c440040c400d11302e080c0000e40b0001c1c01c8034820401103500740501c0c104039510f1320701c0001d50140b108a030390070014690303800340f4180140d43c0c014070040590314031035039810600c1503100040303901c546a23210000c0c0200c0c0700c1c07404603203024004e4006030410160031000b1502d803a6242090781205903203804120219540c0c40c4614009480800c06c20203503200c032a040351900c14100011600344030727101c0360080c0655490320401d18060080c041c80c4000d50182040d1220040c004d400c0040104455001c00740140b4200802841e10782641c12000d402e6800070005901c03001049586400340c184090b0350344e03201280b0103c800c0842d0218859 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 697749370 1250 697748120 697748147
    0x25050f07080712020a03171c060503030306060c190303050a060e010302060f030912031608010512060f0c07060f02090f0d1e0f05010509100c09080c060d090c080c1c020d02040f0204080706 82
    0x7480c80c1c88842c0d48d8481143d200b40551901604100005426400c0000007445d07140d215208a82e2891080801554042078820b000c81c0040d8684080c4400e00c1c0c00d03401000c0281a401c48404410352540c1e002603400e2080741d0441e402104003000003041c2c03000510484420f0403c00400c1a0f5926203032000a600500e01e000d050046600388001040c03d0074002120a107803d000c00040c030003a194030402e00c95407030004240301c6041104200307007000202c040c0100c1d0314016004074090380340d021020400c00b0100510350300302d01601c00070b1080800301c0e81c00759541d501a940c0e0240132803140060b041024038240c2094000e006903003000188079106500082168504074030100801100460358001c0710020620700c1001a5580060b61050003490b0250091903100548000011007403481e982d100c400003403036802046a600040c01c150000e02780400d401400c11115801246c200d081640014600700d005c1034041d00450343c80003903401c501119411034029080d4201220343c2c041c1e8032440105541c0180c5032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 697750620 1250 697749370 697749397
    0x4060512010e070c11060c0109030504052e080a0906140603010c0929070c030b01060e030102031603090c27180c150525050f07080712020a0317 63
    0xc1d81441d5250540c0500e206a4031541380c40c40782d89610003001103032000319a1140c401c0090b00c0c100d1400744030b0501d403684242c990944441c0b0305400c000107004481c1d210740980e1080088182c00c40400b6007090341d07503165410861656150016000001c18604800810491520b0070741045030502e28400e501c42d01d400c03030080c0080d40800008a410950324031804042960700c105001150002c031800c000701089851005040504540301c8041c04840da50098940351040c100501681b581300e90903400d4040c2c150004d502e54141103109031320b085030080060040564a0800c9002c00c5600707000d10000b4030f000700048050b034440c550602541c901e07803c207500e02d091030580b03007000d10640e68400106c00e5401c1443c50762000c0c940f1000700b413540980080401000390802007100020640130005080010030180c0a011405a151461410415424401569000c1d0b03400b00302c40c40340000c0c11829510100d04404802c0079500c0030580d180181d4000800d00000c10420100030100c440c05492300c00c21a80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 697751870 1250 697750620 697750657
    0x904060518121b1204120510020f09040b01051c0506030f0c0a0509040812010303090306050906450616110c01030218030303130c140117040c0b040605 66
    0x92903861454466501003414144400192071403c4030f841c481c901610340681c4e900f007082c400e50400692294103d12030316584655202d0500600b0420003411113a050740c110f00e050a0341c050a0b44500403602c5031071041c0c1e15604842c81e217034440d800307681c00071030640d580881c500450520400070748000c0726824041c0c4240c0b4003180c0342c10400614600203481c00b400c400c2e06142040d0a0010707504004000f901e00715410071404040310340c04040e4600840c000d541e401101801c5240c44030546d00d0281040b01e55a204c602480b1611005a0746a2001c00c48500c00103c6081a00409041c405440e00b00410421120f42c184a039148041410352080c81442c9820504001201003030f10f80610503164441a5407042c10442400e5011341e00070190650b02020480c401a041000285141c0c401c0710162003076604100d0040400c001d000f03a0304043d0500c44254004512030a000900102010140740e0b02c2d002c642d001705003801011010600503040895125596035100c400103099980020700b8020000c0081e07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 697753120 1250 697751870 697751911
    0x3050f010506122407020304030c0803030f0708040206030a09140f0f060f010303050322020402070f1403030108250f060917070e01180b03070f0819080f03041109040605 74
    0x1c10b01c020201981049003900c4100090024241c0c0d44c0280100d007540310070440440070030344181080f0001c200900c02550340746131146401d12094405041241031080d140305100c01695454103a81d801180404c00003a0076002c1e040048119500c107104031030f14000e44410940d0441c4c04501c003e001000314080780d080da10384400380d40c45c8090034031024000440a2011480744d00c040180d070240c2c40c10031001100c0f510b203c0d800007002c0b41c1c00540d08a510210300105041080040c551010012580501039419585002616a251403000c426035440810340080d80314213000010040d000f5040d01ca8403490f009444ea500074050f6402c1d80600302d900640007040c0c0700c1040780010f400c01500c92480c1c00b20403e03440d09900b000c0303020203084c2e58180700e9190000340407d904c0402942d801030603941c40c8515600c1c50600d1050420300d110b00d01117540c0c075041c001c001c086044c100864450171100d248080d900e98503400c0070014403a51081c4540d00807001c0d424071003030014680009000b11107404a904880408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 697754370 1250 697753120 697753123
    0x3080f04091107050a03140409110406020c0a08060703091b0602010506130510030210021f0b0a0512061b04090e280213050c04050a03051506061c05060a03050f01050612 74
    0x3d01e20000c00960110300000c0000b4844d0a100c8038505000300c41d00e05103903c07400900142c40d40d40b8400c04c070a06010804200c0103604100380b2034128002d03034000310000d0030442c24607100c0d107004041d4400d050321481e00008000001300141211448a052029400d8490300024007030001a00e503a445660088002428141c41e4440c15000310003404080201919590030f020003061100314002c20b40c018099565100b45104c80450381071002c1b0313400021415034450070044600190303009280110300c101c00340c2c0c00b0003800051a03a0800c200e0a00c5002d00ca18030385d10f0010714811500003000d524105559140e40500c00180b28150000140300058080040070f0300b81007030780000c14040d40c88103402080d110020000c0d845150040040c0317090300c0c5080c2d01d520105000403c10381c4103c8140e400a000780e903001c16500c540a4018504507022480e11468241141c0011940281e54a0a503550000b0441aa0b03400902400856114042c0c0301c008000d00e07600e03030091804a0b135050141e4030021242c4c00c0e0460 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 697755620 1250 697754370 697754377
    0x117030c0307050307052820030a0f0210030e060a15030503161703270f010c0903060609020f07080c0c090403110d0302030c0a05160c0e010617060d11040603080f040911 74
    0x4091f131000351003480302c2e120000181e04410003240f08817012044115661824406060201d0242c100103128001920500c01216100f441c3d0320109450092480c06810012801540002010401140d2401003140304000c4080aa000401d14400002c0c48074040d241c229071285018002d51000c40140009040062a03202c11903000f5401c42c032100382a0007080d4414141079070280d44c1e00c100c40d001c100b014150f6085445142070035000c40e841000800c00c001c014022540a001044000c0d0700300014883c08901a00611800400e000004030310b500440608000301e010342440100101902c0c101800c02030001d0402d84101030f400e02420040c001250300074002c83c2c0c004c0d170090351842d15203501024200c8680d000316a4140b020542450400045503280c9080400740c00c40c01c5c07030504c1c00c4d4034041000d02400700103c44a410001410304100890f9a2800818901340e00b0452231005d1038658000078005100c00d4000614000010035090703040e5810901400554840d480208119803069001030010300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 697756870 1250 697755620 697755673
    0x9180c040b0f190e090f0c030703020d150f06060207051c030e01110a151a0a060509010507080c031207020f0105041a041b0b090a051813031205041b0605070b0117030c030705030705 79
    0x1040c40c489480004c02c379100701e07440c880c03041c01e0018910512810f11070644503150f00c1400144d1105109101624103803104800a012155029404000035076025040054000c0d0680c18001c0c0b4aa02d5a02104244003c0000c20740c0074084940001c50203030000d004200c0c40050591b0302581e090107a01034280024080162000303900c81ca81804581001198654889241150b00c0f40c0180080030780c122080002c3c02e40e0710201d000000e900c2c80c00280081c64040000e44592480e81400c0a210100b42a162868146240c1c0d8440341080d640354100344a603440340d994007440906102800003101c40700c4002903c1d03c4c26044842072042c590b00c0003041003001c034440c050001c0d03500304800f0400d440c03003800b44801868030904200000c1d100303a40780700046400032241950341c009490300d071410300e0a8101401025140fa820550b0505125803103542c0090014002c4201c4001031080386804190204152143c2801d0807044039580d034001d1800e80d440380c1180000301c896106000001c029854080885010340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 697758120 1250 697756870 697756879
    0xf0c0504020c060c0c07090203040b010905130305070602070201270509090d0801150c050303010b250b060108040311030c1c0f12051509180c040b0f190e090f0c03070302 74
    0x784c40e00a0903034103d0b441480700400610407081e0000b00000d89001030b510070740c020300d500300c21980340001c030101340c1c0c2d0010060b1102144094403a00007a405c4801c2e43c107103542000b00161280c0e11403006075060952103004139119100d00d42d270403481c05042c040078000d0328425101d50b2219112800f101da51141c0c2510180046a078007801404149504a07400890b9006842c00c1d100d03a10070364403020b086900030381289030a55400104c144613080340746080405010ba88600c17108080d42500d45a46080010f4049810010360601040501d849101c900c440428040242c0e48d484540c158515502c450480c5080141c0100c840d2111001d8041c0710000e08101042e240c500300422005841002418007d100251440c03995250341400e89800300003d1113140100060300289010500007890035810b0114184514200300d803519064442203c1c1034400744083d01c02e12007807101000700c0e5003220026042002040541c00801c10403000004034407a81441c4e81c01074440c5151500241600c800560001a401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 697759370 1250 697758120 697758133
    0x7020706140706110c0106080c012007170a030e030105010b04030213320f0103031b030c0b040803010515070f080309011d030408101b0516050a0f0c0504020c 69
    0x140c90260380e00341e1200a6000780180750501c190790303000071121079803a00d4050300c0c000b0540b141904003d10031ba20190003180010400e0050000000741412200301d0f000c15040e00c80031411105000811442d8080d003d0b00000c000444906181542d40d0050b5440a40000b41d4048050106080600c40c0a040ea0070449040b03240c42d0035030b000d1003c522585400c158169641e417010f64170f01001d9441c0781d6404d031185084800115656401031000542c06462015280d0700c2100400010b030700500c90031120745400011500044082c1020f54035a10043c00c05481e00101004104c10003142a008505844003210ba4919a0941e010048650302030054001c1102d40c00c00381c11000f1030413800286500c003103001c0020038020b509007100f080c0054102c0d41910581e101003010f0200c11428000110150544103040011240120760301c4058080c884482003030207400a0300000c2e945680c911740c1195500501111649403451504682c0c400c9514421360f11240164400704480c03505008407100c08102c1d0005100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 697760620 1250 697759370 697759379
    0x103050c0f0d0b070804061b0f030e030f030a0605180c030a0b0a080d020a06060603090f1403070f11040c08070e0f010917100b0402070f0b061c050d1403070207 70
    0x1c121040d02400d42c0044860350040015000011452140c6096070355001182824980740c419a818203003510381c1100111569000720350b011040001042e003078640422600c004080e20303410741c4034031036141c0c00c1c6450001c10494104001d0700300c1c0307003160000e58400d804602007500310b00c000c50342503400050b801000c00c0842c0580a1035040404550790091210701c0450343c1d103056078a03005041c075150015810442d8007200740003e0b03101e8100240707890300f0180180c80290f510b180e0892103020004000304803140c0000006002002a603412a0303000810b00309800c610b051071390007000d003080a644158103050006000d40c2c415000940254010740328110320302c0c03400703003005034418080004c1e90401040290004a007200c540250002c000c410000d0400c610403070180100f80c40002d050540034078010031854000600d4120442c0f00a0381228980c0101c1c0c0b950b1000a500b40003e07214441030015951041c000d0050210f62255147e03031030b0721070513028075070203003450307424041141d00c080581c0003d00e0411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 697761870 1250 697760620 697760629
    0x10050108120705190302062403190c0b040f0915050f06090310180501050c34050a03121505060a0c0219090902030d02070803090618040c020c180103050c 67
    0x51010300c1081607a0000703800b13003a184084645200150016400300060211359014400080c03841030300c001c1d615096000e02800700c1d55440005450803d100c08900710141072020b60f5842c00301828003903110550740d075502c1c0e003905c16101e118010281c60038940442526030403c5080c20108548014101d10103900c0700340200300083d007050b450950540034856040e00628043d1003001c41d0881c44030561204100d00e4100a800c4640060964040303490401ca070709800f0f41101044060818000c00d0455079030b1080303001507001400c80300d0040052081d1000c83c41015003100080621502c040020040d2010b521240d2103407080794401c81c0c0d00184c0402440040c580704001000a4a0001d019070400b01c231098881c041c1134070700da402986001c2c0c0e1003880300c5c00c6141c184599102e1031070310710050074003605010800303840b8401d006aa030311401d4000766119a1030740c3c80e4114103001c5001081001043c040e94006900e0b0a42e24500502c512041c00d0014030244104003030f070341680c2c2c01c8401402a2240003043c00b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 697763120 1250 697761870 697761877
    0xf05032401030b09010b0309070512060a0203130503070c1404020a140309190804060e0907080114010c0204020a09170d091503020412030e030105070921080c030a111005010812 77
    0x45041640b10ba2030742d54181c13920010710f03000304600d480103070303130b030700d4421106800d02046810282c45407a00304403044081400041d1640c000101c20401030f565280c0000043c51410740707107001000d0340408140c000c140070420501c40110340503100030603106141c3ca4100400c9110301d03c4502c021459000c182c10550a140000c0e6510510340c4084901c06100c070010780341c191112010440d9490b81c002824041594003203c804640c600544006c0685c0c100a000a0801001405991414440d0041b40c1e501a803203000c400b0782858000c0c0045545110304580142040c0c10390044007a860860044c4866900001903c03071548100d690f42d903a8581d0610700035062803035040a003401050b03024003010501c0724242202c450700d94480e0300c40d0368074400300e203060600390b550090458042c482294020441003e450420070850707070300c14900c0341c111074840c0b5200156000d01c964541071444003050454031503070800c01ca00c04600c090000c440e9144070402c07002090741c0003402441407580000d03001c0b02940c1040e1014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 697764370 1250 697763120 697763191
    0x12080408090307231c0b040501090b07050901030501061e05130b0c03121e040f0201021f06030b0115200f06070f110d0f21050c07030f0503 61
    0x1041c5401e6100002a01d030010a400190300205190b41003a00b001600c03032080100308042c1ca81109070030180c0081c0c40001030803640540112002c40014041003c2907003d80001c50b0301014100b8030b41080f000c0140035070001040319002c28902400400e545008003001c0181c0c541280540025441a8408440c0c070780000900a07521011800301040340c0854101901c4181c55510045032202102d1001c00305500001d425a282c000c03078500c0c041400d210480c102e590054100340e1502e0403010501c0103d1404115003501d006030007180f0140603e61a4a42001084a00408540f02140d80703400314190005071030b50320040400c1c40131703800c075081c280d5400d0001181201030341954620210903880b06c3c2010001c50300308000540e0801a03410142d00004241c4400716407400070700402c040c488001e881e0120440194043c40070800d00f0144070300c4c0000d040704610250110500c03040c146020040d003e5004001d04402180d440194114154881c3c0240c1f4030411201c00d4010401c40a42030340b00f60606d50068 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 697765620 1250 697764370 697764383
    0x60f040b060103020a0314040f0b150136030c050406080123060a1d330f13140414031e0702040e0118030210110403020906030c13150f03120804 63
    0x504120031f01000038440c0b08d01d0240c000c0141d40051803030000040c00d002070001d00ca024540b000440c81d40d80c40a80329060800046200301ca1187c40030b060b10301d44510300144116030411182c040100700d14070f4402c0c0110b807010b560901402d174585940600307891480c1d000d407101c0c0014898685c034003c42c40a820360015400361100c540507403244600d0f80c00d500044410403102074154184101d22861071054819030b0703000c04a501c140b0301000c074800c40350480c04c0e440d03d100d4849000e00010303d5881ea0420015112910b17020403030a030340305281921814040b10181d9821052281d117101310349022045410384862240300c404011030303070300032140650040030b0700341c0e001543d540b0202d40001c02481902d0410018040b1444025585d2800078038205041c2e4031121a24100b108020a1910b41e1003074a080d42c1d81240d2000c82c0c0e41e10303500401c0c07074170002071941c590201c001c0b5034010310025154444c12001040392104034485844005d507200b482e1a6100003899a441402904981d500c40c440e6190003511404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 697766870 1250 697765620 697765631
    0xe0609010e06070b06091b180a0b0c1006060503010302061c090609031808030c0d0305060409050105010e01060801050d02060403030309050703061b12140103030c050c21060f040b060103020a03 84
    0x1002c41d8540d00b280e202191281500401c0c08a50b19124107200d0b8031004e042e10b003003002410010702c5420783c02050000410801200612a80c640e1034048a50151090f00c0d00d03203850300400e851280d80c5034100724030b51000a180c002d0208005e03110304200c074140c0b500a82003500d4804103070151300500034070280880441c0e5a81c81b4010001d00180540021640a41e41d03c02000b03085060006202d640f961058503681d0080160040380769010403070030311520341800d00044035920b1601180c040c3c040a44010032552a0000201d0b10b41500c6051307505a550a40e501c1c4041d0b80c80d4818013451201d20300000c0c1d884203083c801000000d00c20380201e003c092248044d1003070b281d40ea94560341680e202e5541c00c103082542541d1144423a9000014001c510640b98003031040c0c0c203190000c40a500010302024080003a031035804000c0c000708202c1c400c07c014015240c24000d51503445170a44040351201908200e0150301f002c14001840e40d890140643d03001028808942ca0710801507009520108540050513101c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 697768120 1250 697766870 697766897
    0x1e0b0f0408040e13080f0a0806030105070806100512160807030c05040308090418030206011401021c1404150306261005060a03060e03030a200a0f120509010c18060e060901 75
    0x18018000010411b41c0e5251203031303132010015042d120010000c1e4081c1c0e16190812040311f9020322460380100341a00d8090095400510480321441000201405c01c4110014010f02264202c95080703145000e58900c101074a0302c000132000d540f03244480c0d1000070700912040c408111408000c04040070000c2c40001c03251884840f5254403021401c0c1940580c12480040105444002d140400c02e4424800b0f840d50840d800043c5401d00c0940310010204500c0d6042c8141041081c800c540150520f450714050000090200502505580c0100d00c420b141070b1844c10341d80c0c400004140c040540c035074040c200c460040036a50307000744801006c80e4bd00044c0300500101154241c4500000e81ca88070020b140c2e17a1a0072400641580c0c01142c6100043d00321218031034940f040d40040e40e82c1403020f46410305243c104958211003d0851140a10400e442c1c141401a80a815484100b60843c0f81c0c0701c03400c0b102c00ba040c01200d840340c030780b0480c00410300c40c00c1c0307440e803500c1e00f840103180903241410005c2800d07008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 697769370 1250 697768120 697768133
    0xd050703020408010e0c03070f05031221090109030e06040b1b0c0a030605150609060304080708040323120315040905032b1b200a1e0b0f0408040e13 65
    0x142d01c0c401c495030300701b0401b41640342014000fa1018109211201d040149003c000c641c0e22140625030680803140852408036408a5000b031564800d4001180069400d1610f800740c001c02c4c8948048010a0500e5001400e508003141610216030b44001d807030381001e1303240d100d034106980108948907445c0501d1202c4411960b802e0108030181d070280b82c4c00951071820b10442503280e01c010640d24440d00050221850303da50310b60450b0741c09544900e8464440b134151401f04918011904010060050340b5400d040340c080404803201c400352400115900c103101c940905007036100544900c0610303041049503046508107a00814501445070007201d00d4061000e01560000c24402146070080b86500888007030842e81c0c0c000c49031403609401b0102d4a100300d11001401d00c0c020036400f0407080013141400319400c00300384080d84107aa00303c1c00c002c00c1554031074210140e02c500341c07804807100c2c05010086440868a40d49880c49641d201000501e07003400d1042c01c0d00302c04401064211150711001210000614 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 697770620 1250 697769370 697769381
    0x40c090c170a0e070b070c0f14130905250305122101050a17100608030c0f0a0b04062f09040b0618060a050702030f070306050106080106050d05070302040801 69
    0x2081d6a03885072404501007080c09550014196060a0b0700f0005403400c8154003060400491381c0300442566518032a240c08000c10140341d04c04184100030b00b50004001109008944004030101e401c0016089151030303690445a80740c001a00c247c0c0000805c5c092031909585214800d00050341700c119a9030b603a03035518504000f22164082c0060040340f1110140800d10780d100001740c105101480646c1041e002c01c000d400e81388070344168030704041c00020071813009214002c0400f11120043c0071158440880d1644c81d8008070304185944102c00140c949100c002c500d00c00f0041d4855110b2206446a450b0500a000a03460818503c03540701107a800104801c03418507000300d03105070150348410000040104545050613814020038042050600c80c0032010400c607102d20003240c0d4039440d1110003000300e52600513610004d42620030f00c1c1c0210001000080c005049034442d402c00c0c009a03032200c5044409000a22a40000c030301c050104809102058000c1c0345e0019980c1740040c2495910540142980c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 697771870 1250 697770620 697770641
    0x6060f040f08070b030f19060302030f061503010e070509060105040503070311041b050d09170a17010501020a0b041401090807080a0905030606060405190302191d1e040c09 75
    0x11075050402001c2000d0016100400031aa8524114a0a08102d1342d0802c001030081103140b4100d2958800d1100580c8200051a0050211280d030202607428594030307a016102601030480765800d446117481c2c140244034100c0900c0001d00035552901c0706201c1c4081024019030706103c0140001300d02920100400001180294040c81202c0804030900003110308048150710010b96004008078203d81040840c3c40517428401c00040265682c01c20320001204920500b18983c4000703014090745510410710b4108407507000111a40e41d0f41c0d140166503031001e03802c008055804102c0010045000e8203400d000081c5040008542d074103c0d03030366500d11360b803090000711402003003c01c000700520340c042541c00103800c4c20381c0108683c7c1450341c00100d0030f014510941c0d1003054a1041c41c2c5401405429400c000e40d03025280b428142d41e04c0303810b074040c1750550155010000b443c0403060300c008422080309004429407943c3c204d116031003880860305658020010742e084c1902200000d48000706114040011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 697773120 1250 697771870 697771889
    0xd2006190e0105061c020103060819030905040e0607080c04240f030e100f0e0f0a14061b0a0203160309090b090603030d0e0f160f0512060c0306060f04 66
    0x96085480c4002116008001e641c2a60301d0481084615100c0040355010000e100c100d5a00340380840c40102c0c0039100701d0304461510301400d20241d403500d0301d085594030413500c00e0700c176000c2007a150824401140c2e81026040c403d03a104d1004607605030b00038200e0036002402070309014078060302c0703080c1000c40303d802c84000880c5070321818154007c00d51020200442d081c03549018849241c42040c00e070703940c0c2ca441d0f20300000144d59200803185182c203a07102c00701030b01280c82038a5120412120580d10750400034001d403144c451203802c0c3c241c4044041521031013a01e102400e45802c6420300001036494201035015010352204221b20b081c0070151480040c4018441d96032040301c1401c10b041745050315440d1f001540039420312403e204282d0b80120270f80308100d800c0540000e2001c05020380300d01c0d0081c00e418190030350080f01d406003200010740c2c4000b42510488000d441c100f66450040c0708880801d8513540740700b50000d030003080406000358021a04000020301c030700d0400c140301e07003c14400e074095403240498 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 697774370 1250 697773120 697773151
    0x1508091c0906020f0a1a041502040605120123150408070f05030d0504080607181d150402070201020c060702042c0106050f01050d0908130e010305011404082b0203010b030601030b120d2006 82
    0xb0b0b002c0201003b4090030f02c440030351a0314904400380d00b0100d041003d50600c41c03c4001c020b50040b51000e01074900901c401c030b040707c04840c0e032544072214800c41401814007901440014840c203500a4048a003240c0c0d0200040145a80703042040700e10380821641005e802d072103a400081d60040b83e00009004001094400c001403c3c001000885e00044d030480394059401803003c1c04c0944c0c3c01048200f1045001c1d20034540c0c4441602c0068010400300000c1921200c031246160b0f030071602c00074282c424000220003006850b403180108525214546603ca0019004001d25025900c56800ca01c400038030a5074004c4c100852203200041c4440241c000030001144080100280b00e002d015150040ea00111800c1c05410320740c60380f04162240544841008001504244240104c000d21070380890070114119100d503140e140003015503000341c2e03583c0c2c002070030804a1156494081c0b000c4040025030001029005417806054503103401341207a1240e0b0106103101e000d5550000c0c406070b407141c0080190f5016 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 697775620 1250 697774370 697774387
    0x605032505220609030b0901090c0602060a0b150f0a1e050706050105090f13032106060f0801060206011403010b040c020d12061508091c0906020f0a1a041502040605 72
    0x20300640c8902e01d021081ea224030104280d0743c114000009881e005100d4940c03a41da00b501540c0500b6441000a0810035482000161b0a9000c0780c00c030300440d400e040905c42c0d40e90b4503080003002c0c8081c001106c4d98500402c2030491010850000b841140102e007003981c1080d2011420402e503000c2224014007003040042c0030300402000c0e114803800341100701c0707456406080043c11011160030080c106070091501050b42001e03d4080c0c0315407400c0511428600003076410400006020307000501c19a40820915408002400d0203490514181c0d41564014440e5131300e05260200c00d8109006442d4165581d2107108000d0349807801000c00304441074004042500d5620001090758080300310307c28440749040d409005190703c442c1392840000c0e4600c1c0000440c0c5a40040c40c1c1000103141c1d160003160020140000416080140b035001c480e659000c2e40c0d60412800c0d1041e48401d00103c005195544a544101545000155072600680540a12807110041c804c44100320b03805a0032600100c0e201050102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 697776870 1250 697775620 697775647
    0x106150f080c0d0207020a0f0603091208040218070e0d050a030e0312040315060b03040f02042712050708030702070503010501150507030807051c0203090c030d090605032505 76
    0x400c0c08039145806201450304518400b0a4011015078100403600002e101c4150740d5260701e510040d1441a07200d4004569a00b4050700400400c00c003207454000c00c000c0342c03031011300480c01075101e03903000b81810800c3e4140764482861a81c008125505220020070303030403560303200d02000c2208540f24400500c01e8408a04000c0c00741c17203452405c140300360f05c41d115000c0c4001004c800c1d141120f5005580c03515440562171200041c1000b83c1101004160101c100010b019042107841c03001130098070200a005a43d282d030a042d07201e00d80e026001d2042c1040725800042d40500d00c8a000c00103440c005003401d10715501c0c1505a4070680b00d03a001a401071030148240c2c1f500f841401e0041007000b0354004a81e051020150880c00343d810060309000c284400211a00e00031012280c85000004040e8404240000483d0094005481c8243c1d14462816025014100020300904064058071340b2120031b480d00d1011621035000501c42c1c5a80c012100450311881409074510b0050040c44d240c02c2d440b24002c03003410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 697778120 1250 697776870 697776887
    0x30603100c0c080304210507170f0412020a0902030c25020d120c0c0909050105180a0f15050a0b01110a11100207050306010e07090b040b0a0e030f010615 67
    0x41025034542007032181d1264218030361000e1554008807080d00c990b56400c1102c0d00742e5200401d054809110302405400b036030f0142c000d1040c0c6120714400100c280b00c1c100d00742014002d1540c032440d0031008100070300c405910100310740c90142c40288603400f520b48800e101d1040ea0015a080358100c080030904101c90621710000a44c0382c0c000000600710602c06400113008540e010300064541000c2c09a1000058414071010311034a4000c0d040b03469172556450068010403000d04151015440c0074080307842c00130704010420603c4600d10090007001050b444452a2040f020022503a85d50700c0c1004089a0180c3d0290b240305244800000174100610340000d48480002d4001c3d02e0550482400c0600207900702c0441d2103521400d41e4840ca00020a0600f43d01e40300c6176401065141c4511000001c008800c40c1ca05c0f44035a5840d0f40c2c0d0002940c1d01c0704a44038030300035801b80881c000c0040c0445034100c0d104520180c000a1f00900b101d0500701d004001c5400c440c155000b0009d0304000c0c2044061403138000104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 697779370 1250 697778120 697778143
    0x20d09121b030509032506030b03070f0b0a18030501050105011d01171302420a3c0206060105040509010e0406021e030108071403062703040902030603 66
    0x600040300845807003260180c00c850040501c00085004500c0e52000c015140403002c4000f40e0b040000f648000c02600e0440c03600c29134000034241600301c02e19060100c0d0031402c661044a40b021414103041400800360040864942000340070819042244080450380c0c0045005030700004107541400c0004010b41c4408410204c502d10708115100c081e68014040108494074840424147d107139a85481d00d030185a203000382d0701200b505040c0314140344065042280c107800000d800705028003008240641043c4800032001d103203041c040480340c0b50080d003c4810302c0803100c84030310340b090980c618142c40c20896442500034100840b0399901c019010451070b50085800d082a605191614000a011078814018510541c0c00d4001150400490350143c404041c0d4125002290603281018603070780d90802d11841c0058446d568000454000005000709a804080d001e07000a82d2540300308000c2200001c030941c4035182144186102c008240043d00103000491000b50380c078100f00341014a481c2e1021071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 697780620 1250 697779370 697779377
    0xb0103050c03040f0302120705010204050a0501090b0f0d020f0c101d0712050309090f16230702030c0a0f06090b0c060708130b100315050c0d020903030d020d0912 71
    0x92180050041c800e80741e205074041054034200c0c6442c03030106d0a0886500021501e06408a4100104001900508180c540c01e9511600d02c03a036820045034000958450213400400c1040741d02c10180c0882d00a11500741c030440003620386003a20404c204654004e4421010350340103224014071a002c240100c1414081d903070024030523a40c00400d0316480c2c079160722403144023460050740c0340d00b04501401550648103005003007410030302d04030b00c5c981c0e1114412210200c602d1f00d01c920001445026800142010101d01c1c0d58107803101500701c00409640c403155040c7e0349880b0340190b440030b6a50b40445813000c0c0c000c00a00c2050700d4600030001e00a20b240d5081002c0c41101400130721201c413800200e05074013080500e406035003074482021200c0c1300740c2440b42c0036055900d213600f00300900181d002c030a000c40e48660690150056403118807022510140c540c034661980400c0381041c060394a4014290508008054a1800100c00080b0741280e104c1600d42d11540e444d0b8003150180f1619201c11440e0001608 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 697781870 1250 697780620 697780631
    0xa06031509050c121e010209010f0c05071211030d030e070605040803070b0618040507051c1205090a0e0a0c0f08070503270609013e1803070312030b0103 67
    0x15a4551248420080343e802000f010f0181c481c25407080003210111000b69800e0702d588202c181e141c2e4040e40c415413005010507208c1c110301c410184030300700c1c1000741901b09000d00215410a1400004242001000d556445415a0305055558140400081c9800b02c0e2030020303902c503e6011041c00d015040e0300c4882408000c0c04200405031020048400041e0b003d0f14200c4e0b140c1d40c1c0000610022658110307441010550420007040040c009600c8003582d0048888404500541041070042d00350400300408440602036441c10700381c021005085442c20091020145c0c43d00e481045c0ba110008407810380f0a161902c0c1d044403116009a5095080c800500d0003c8551034481406030243c4005440b045110400f20181d5082c181c4001842500c80c401d0340585565007840d69681b03000c0d011b0b010603801602e0400b07101c0d400303c81007030381c0b41021051f01ca20807078002d0790010b100140d507800509101540c0c007403000307166405643c140901d001451050314944c5503030000b500014100c5480310440c605061522 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 697783120 1250 697781870 697781873
    0xf240c080924060105221818060902010323060f010903052107080a120b03010606090e04050a020a0605030108150f010902090a0e0720010908030f100e0a06031509 71
    0x58200b075003801c1c0403004140305454580c0101c13600d1050740004110780071040300381b02c0008881c00301c8108441440004210054034803499104070303000c2d104460505420ba1840c4c0d00011200d070000060f01d80141000180c44e645601815002800c0414144a01c904181002520f1800190303c4402c0e150a20300022040d0075a5119682c90005480443c8005100ca81c5010407201e034404940e000c90340029a00c2c3c442c600400047d00341e81d24a102c613982c0c1c50800c041900340741014451402100e0781036443c40c15051070841c0041d9180c0001c1d0090f100c5004d0803120001507200e0344030902c005c003010344e62182d80b585000c0059041212a00d048034849410f001800200b24071081e20300c1c10341d52640d00044e5124100f0000840000259102c450101078140401c0001904450214031400340700820203404a49200b41d40e08031440401c1c0101030703604c10b001090383c8415107102c6c20f038400c2401d03000390034041e01e0340b00e200e91440007240d0011019844400600411a00d800c80d135142104204042c048188903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 697784370 1250 697783120 697783153
    0xc0a180b04020d200304080a2003040b04170109020f0d08040803040f031a011410051b0106080c09011d13050303040b0402040c0318061a040501230102030a0503040f240c0809 76
    0x21740941d4010009021f4011210701441c21001c0c00b941c03127444c110b950700e5940781c00440541d0800d21854004440c2110000c008034018040c114071070780d0091a41060340038000c204a054080300e10240d810004c180804241c40c40301300002c1c006800300c59681164107155140c43c001d08c00b92100325400400c2c0d900c0c010481060150982c02041c6012110344a008901c84400c4525009904080d19811154104208003c10652190f010b0b9000d0030207445840c0003600c10700041c0c0e0801c2c03281a010300780401c1b0300c4080400c40c26115401c0729015841c40d8444442d900c3d004d00d50342040d1800d4420548030420b00c011071a040c801c800340d9260b00d00701440b00080800200c40c049882d9200504804e07201c110200d8601d0b504035009000c20382c003e10070003155842e18042003000140e4030706134640f00c42c8082c8240d02c0d9070001095070050041907503054036641c0c0b03039654074400740145102220f0406a03c20b006444c926080401c101a807291000002c000d9000c4400400c50310000d032402c0b00b1a001041b9000715440d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 697785620 1250 697784370 697784377
    0x110c0319050c0117010b070602071a0f0901060b040b0306010507050a080301060e1f080705040f03050f071a04090e070e1f0e130305030612030c030a030507020c0a180b04020d20030408 80
    0x140c1006c2d40319091401c0c460064822a0801410708860a00014428180d140101e00404004c440c0025a9503211181400c84402c1d02800c482a607052004201940c071401c02160710071010324009090400540d04d1318500b41d070160302140e0096021005026156025489903480356046a00200f01d111030100100840c500448007410400300c01e000400c2640500100d4000f0132005801d03c0502d0354074100702d40c80b400072060490700f501032802c00003a0742138403000d8681c2c030740d0f0024502ca2500d0325114480006112080044005000b8644002201540c0d06645442500d040e891194041e0190960001c80c4a01d038200c03140f50080703c1d06204403015000b0340c51041c2981420503542d680c0340c9200060581c03800002c0c0c04214440082c07140011000440509030650150f00c1c01c1c881c0351039050041e0b8a0f14401040260800d0f40c0d000100034401c1006d094a8901c0702c000b000041020140c004030b81030742d001c0601c0c40d0b001c2c0e1700c507001c00501030b2030a080b00400d032203410000e03411030610796542c20342440b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 697786870 1250 697785620 697785629
    0x30c09031506081b040f0b0306130303060902130611011a1e0d062901020c15090904081c060b0d05060102070b2109030c0a03110c0319050c011701 64
    0x100104190445900d10b911010180281c6030448404882241c0c034180640151900103005606000c03040702c0c03030f009900070707401e240740010007034052030351404c5208525800c0240140c04050b1107440016200c0c0c49480241000c0301a101514100c0d424058040e100f07140c1404080810f07072505403407840c1c1001d1441200c03980700084034031082c155101c030714000d0101b0000a885501c008480c0e900d404000c0568044800c07440c0075803440e1038000c0120310b80741440701108489405608445d592100b60302d04803000740c8400708000007081c145540000812107012381280d003210003440000e0801c9035000c010a8619102012103000d02586040010400c0a070103003600a100980d11040481c059a000b48005006480c60300c100341d80391440414003080c1d01d017402e010020300b200710070081020000c0c048100c3d842460010014894030b90f495034100c4a201010001075500d02600105181030b07036003032180d034003450602c8090194044090a0160910071075494043c1170006041101ca8070540c070038100c0d41180c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 697788120 1250 697786870 697786883
    0xc120b0105100509060c0303270d0c1505070c0209160525150912141c1116050f0d120b0604030605040b07020d020c0d0f05030d020703050408010c030c0903 68
    0x1c2e88019065500b03008025040e039111202189101d03400800201652242149000e501502051291140302d40d884280801005801400c030402c1c20034001d04140c02c005201d00301c0e580202c440541044200e0310f06603031741d00016180b1b030000419031400b40111034001001c001d404480314814200504240300d00c041150074442420b6408a0720020f6600302c40840e500300103600008042c540e034100c01050400790031541005001d40d45280180318103d007081402e03800c00041d01d04034903429000c0c40008220a5030300444d8843c401400c84039401805400c40001031948482808020700d080e50611554035982d2006501440440e41071a9000004600850380c0d214005010b18000010800501c02d0ba040074201d5030070b01c1309010820011016543c4100841d80c29254406001da0049031101d4000c3c01e00e691103905103c021000c41c0e0320000000a440c400c60460346006800d88528080c2e8120080a5002c200003149c104810a001e00441c03840840c035240c2040b1550382d0b4440640441c05600016165 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 697789370 1250 697788120 697788139
    0x30b060607140304080f010207020f09040203010603020a080109051b010c0201200115050f101d0301020904091b0e160e010c0615230a060c05150901090c120b0105 71
    0x80d03258181120002500708954111036407007481503581d40e0b8401e10400c40a846000d41000c050041031090750001580107003415840d400b042c00300050800060003da03415562180b0010041e507030309201d10b004009400010407009440d0a006080840c0a605594007500340c1d810420340fa07074405034801215a0908005000d032440810800c249070a00c52001c8442d13207020721620f06a58912103a0007101c404440405400d490390052202d0280a4803180c1c0c0403e02d456251012140c00200c08446850068001810103440100080540744265415110303980d2114504054140b0220540c002c0e1003400340582d45030401d0031080b01d01c0e070404800c3c1020030003d814030240d5a84500c0852a1164100c4807d1008420041072180700121510440c0307100c0300d10042e10b40520b00b10907024104107600400e0010002d141c1103060314034a003045d10480d407a0143e025520300c0307100b013180194011090300c8000218660305250001060b81640c1103840c030300a14120780000110b1100516048d60001d5500801c1d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 697790620 1250 697789370 697789381
    0x30c1b0203061b0408010c120606020d0c060c030e1b03060c0c0a0b0714221707030f1b0905041a13230a0605150d02090714041d040201031b09030b 64
    0x4444c080c90704400501d508104421111315032040303d141544a00600802100f07039129410313079441184824240100e9040c240d1900412000c0e440120a0000383c00e02042c2c5000d88080c3c3c90805140207040c1e0300b1a00e2041215055007000c11034141d100082804851402c0c840e09481542c8010300b000c01401020000c0c005846240700300e8041c2c44911300340d0402d0380c403007415401450202c5001501c5020001010800250750002c0709090703494001500c02500d000b505645521042000e80788054908419228600c0034001642c2c2c058801044c58002c0060103040138500802c4814101460640d56a480320030310580896a510074130300c02d54860030846125004000e48004061030481c0500b49005440c0300304144105a0045441010b131005030307850080001c4104591441a14030103508800020000b5031003034003032291204420010011142004d90b142810f8007440049000904001100000e00c0111358060180d405010391141220301101b501d884020b0041c4100d02c00940b001d4241808540d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 697791870 1250 697790620 697790671
    0x203012402151b0318010c230d1508030d0c03060b04090e010608061602010e070305210c010213091a130b040912020706140a0215040203100c030c1b020306 68
    0xc25201090859503101c2c0f40291049130340c4980c100c030b101495400e01110300c1c0c1d064810340c003031704150234501c0410610b0201e8154605c0160009844c0a02c2590b44070400d285401c8000c3c440d200405045000719610011a442e183c1030f0b0710311130a442e051504220040c4072003600c11090b50b040d154078840000c2e10700ca141010134013400042c0d0203215503001da2424000b4402e0060324070041c541c040d40007401440da260340710b20395030185844041c00c076400401100842d10303131500612600680c0c0f01c000380d003840301044aa508a80c01461400044500660100880c04150040c410320003042142c00205a0000b004100310f41c42d0400d50602c1a43d80e400721038402da80d43e91003003828640201106054804001c4040e41e40c2600740a0b400120b90419018060340281504661111409a02501004811007242c0355801307400b51040380d041c007454020520180c0700d8420801180d100d6a00840c0303040301c140c4c002d001ca2541c0c040703900b0401e0a00c42c400e40580c40014400741c0041c000c2d015410250590300054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 697793120 1250 697791870 697791901
    0xd020f0d060e0f0a080d05090a0b0a1409030901090b0d110d0c031d030702101b0302010b01080a06030305160602090604031109100302031903050d0609020301240215 72
    0x140c0c080506100c0e0400d10115502505880481e0001ca07010038020080d060341c1c5815940d0024504142000507078500c8019811042d08002c80104a82d0380c000c3c55580d50103528021201134410955420134015014240d40800da0081e5030358018524154500000900000caa40290350003200001032142080d0f4030703a8089a14062004580303920765031001d244901030503035001c0d1080000e041c070050a0a03030800e1440280c440b146400107501d40115a424003100c2142c1c0d0400c42c00f80300705000741245100a107408090540d2180d400000d190005a0014004040141900d60081c0c42c1107000d000194000c400c4600304e9041141c8003000100c5445e00340c020f441090001038000c2c1c408600081000740380d880031219101c00721688400c0d940c07950200503010354203100c041e40c9a80411040c0d401e0b000c130940000b0b000c900074989649040790412181c0140c41042d8030000e8410717400401009100700b46600d082c244004415003501d00500c060000703540f05500404004448a10800300d00c00b8105040756 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 697794370 1250 697793120 697793149
    0x1505040804050d381f0306020327120a03050c090a061205060d02150901030e07060e150703050906130f03030512250e0f180105130b0a050d02 62
    0x14450041050301d072500c4c03000180381000c14040585031076410240390000c070000c40c124102041d901c0c0343d6501c45109404d61030b0649642c81118184902101250690000314480c05100b04c5880300e0408034212040c90480b480405080d580143e090700145100e00021900200c075140780200e00b6481d0300c07110044520480800b294007002000c80001c105400c4100c0505a42402c0000c200303541c0c840c030902101f2407207003030000c0d40400c000b546005454801c102821603c1010b243c0005c9049000c15200d1a0500e1908007d0104691030101001441c00114000c0c0240c2c1003000541000e400d5a03010300070b030080115003441014007090144514400b15808002440c03003a081741d01282d03a9040151951b031000d00d400255003070b09400500d8140600c0031950100108001800303500c41c00641c121035113580c0054840c0c1c0700344900301100030703582e4060100c2000002203024501c15494001040402c454010b5403180d0329041c440202e0081d034402d10014105c603801d49116200c41103510000e149007104951 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 697795620 1250 697794370 697794379
    0x9080a121407030e061b09010f030f0f0b131a091308042402030a02101d030304050304320607031101020d05070e0406030503044a01050d150504080405 66
    0x80110050f4182c00812904030364a040c0c40d51525401d540d481c444124102041000c101004000303410b5105000000d9000700c503140c005601d461088010041e5510748010502141e254220032641d450f1044607a0300040c0b4080301041054248119006400c6884481a100b03d40d102d0014042c1800c8040c0325a000e40d0002690741c1d1152201c0c810080300c0b040d10b605a58480902c48041d809600020468072090556002000b400c0c0d9681068030180100c800d40f04178001000210705000c06080000d103014503c41c90143d0b854600745050f80c0c01079091034003400c80d0340510944407419120f124049203108401611000c0c2d880500c0e0030242d07112410101241c1c015840000c03005c445000750b501031409060a070f981c2419251490741000284c2e02107002c043e107136400400003000348103803100d01c040029203000c0c16850200b0320000c224582003010750a8040c01444582d8800c052404207441901411044076609040201604e4000903c0c408404450000c0d54840104007440301190540700100b60042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 697796870 1250 697795620 697795661
    0x402030c1002030c1203190506030c030718180c030609050c1002242e030804030503030f0c0f09010503090a05010507051c05012d031a1909080a12 64
    0x103000a680344d0282d041c90f2054040c1802034904044d000c400c0724068041024500c1d400d050403000c100082102031300c0182d0511485a0f420700f161003d00034180206109803820b1101d041c0e50f5144030607500300340303502c0c4a0310541c04c24242c00521601c1c1c00c0001e03641c000f640002c1c55072007860302c1e0f0b140200b410045a0700c100b07640d1104942c26400a4442600b00c411401205030900401d00c80007540002d840300203030080055541c401c1e004400117120a9104610390500201b6030341d48520045500c00d800544550308000b0800c00a00701040c0c0326074100004c0b1a1651500c43e03400307401c0c4e2041c02000e0b1000e04104000000c03450a480411074540308580040c000c000500340030001a24640c0f10000c0c8800800111040b50304030b80c1140f0900707049641c00003096651a060310200d0f050542c0d00701595140850045c404400714a100c02540c56200c0d992440d1144c034240841450f00b4003040b5543d66400504003558280000c44130710940704c228086082c400301440302c010101014001c0c00c4006406900c0e441c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 697798120 1250 697796870 697796899
    0x10020d1b0c0909060b01030e0d3e060c0405090103060f1b030f0f020c060c09010513260d1211041a0307030c020f07060c082b1118090402030c 62
    0x1680202c0d0b00f2442072400708a0180705400540a98900d03502295058000c80300401e0340f03600a0ba007030301e14100c0e402c2040c40464000e090030360740c0d0070000c00182907008100b0301e0045400c008001050300b1000d1640b03030b903040615010000c2e80e0000140402040c1c69120610302c40111155000b80518a90f12110000404c00c0c1100050040445031001c000302400d2541d0400003407010710031034011601a0010344075a80d507102400e19260b0000e515141000010040c2c003501d044940341403000340c41c0b40a511040c0709031448104e1181c0c0b002e100c41002640144034070084940d000820030180300302005001c20400e01d03d201640c3c1501a070381c0820036a4440046114a40508500443c800c0c00c3c00d4404028507004240100d03522200b44143c00380d298443c9000303010f8280101100c0c4034003445480082e2038400040316024041070004070400300d070503500e482425502541d01030300d54283c0e440c01d00303541400460680000d401e084c400340c007400744500c5004203043d500c040c0001660007802030812200710280 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 697799370 1250 697798120 697798139
    0x1030207020d200f0306060f15070506100605041d090705030307050109061b050418180b06010909020903030a031d07180e0105041505060d050718060510020d1b0c 71
    0xc05400f10310203007902c00001014035004810600b03082c0040c005010710f90382e400621541c0880880300355400080d94601c0244c4240c0702e0000c2001d184550003416480c200f000b10a4040402500040c081c0002441b040c01612400c200402d501403200c500100a40c883c81202810600103800c12500360100161403824002d054009603c42440349804000c03030402a400c8110240700b00d203a07680000c1d0201310401644038100102480154080e0b000510201d0300b08101880b05160320b004c4500309002000c119242d0b800680400051012440c103600e09170203040040e4980c4103c0b9a40420315959003201c1602581c000302001c61031900d1022904100c0e141e8030f1014401c1208549102002d00307001c90054000c006001720360013503a00403038071050711640341c501101504004000e030303030405060020701002c240100928001000c002c14401c2e8100300e590b03088000e0f10b1003500101e00589180343d0b080280c981c00141184000c00702d1510444c014580015005c06d8095800f002d031009445440c0860281a03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 697800620 1250 697799370 697799393
    0x21e0a080c030f0708070501270609050f032b030207050316052803030209030a0b07260c0a0302071506032d0f240504110306130c03080901030207020d 66
    0x1040b002c65030b005105034520395664100c0d00600c00c258208000420040d400f0799004010710b81e010b2003540b2500c0b1400965140001103901207000510322103c03c12440c1801d00a207171001d0020350160a41036100324090380c2c400f180da0a005407040004040315109486079050f83c0e50315510009a035a1340c5102c03010b05a041c01500c00558460046100c01060001060f04122080d05144c01f00e2704002002c0e10164020740190b140d95801d03004800030000040c202040c00b130720801154403240013505e40150b018038924081d0001c106c098001c103003840742d06230004007078070a011003a00c0c0150760350005150030803030362004140404181e0b05203000402041240340301484444005031b0305260180020100240d4000c6020780030706a200304c0c4594001180021001c1d07080390342c82140400700b4031b022507144030485500700c84c1555181a41510051585418001103401c440c000c0c1c12071400d19241c1d110030b1140c180a00c8002c14100002401b196640d0282e015151020303002070400340c2c03809841c20110803184 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 697801870 1250 697800620 697800643
    0x10e030a120e09090c10170702070f120203030904090309050d03080601301d0a060914010b03030307080402031606020615060a14030406022223010507021e0a08 70
    0x1800040d040b0b48034240011070f00d01c10b482c0c140c02006001041030500810800c086106ea003007011b5403800e1514801c58500c198081c042c0c66006080861070104a050450002c1d0010807241c40340809220150394000156842044102d40c00214074a00740303010382d0580308991141c0d4001c061b00d4079120030b064028034981d115100a884042000c2d11400e80e80b00a080c881c0030001d04840c0205144c1091000c0368051041002010130802642d81c8a6181504d0901d580302c08999803034a89062000700541040d0703181034040600024882e01030744c00c00103512408002c1440082281580c0050b05665040181c14404406c044c1400c15040d100c000c02134071b03650101d4480721000f024100340052800d200003141c001a41c9943d400d04400f03d901c801880f244c2c0050810b80711030f6001d1000d1240010340f50300324440112011810300d0708030724000c1013505c0c01d903205601503904e1300803944d07400302a604070044460b0a03074100c440d010b107068282076440450042c840181d401ca050031001083d0399500086010550 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 697803120 1250 697801870 697801877
    0x110a0b0636060d0314161e15050c25020915091e06010f110601060519020607093305030a0b0a18050c070807081e0324010e030a12 57
    0x90b40c491041c0250030800440040020b0500010203641c0e4005030042d100310f12269080c40c02e000c04d0b64a818a0000b040340429003601010303070403d420050740d180c05018420280506114070718004400300300c54011805001e100802c2080f1400030740320300162800250703500500e50142801c201140501c00143c0d40c001900a000510101d10480c10b10743c03e8160a01803161100303840d54400004552142200d060316050000381c02402100f51420305c4614080e11a682e511522401a906040c83d4030410114040a54000e00c0900403507652080070302d4181c451004c01401c9034104105045650b18040031200c006030107400c0c0c5141115440002580203c01400d07061043c11310344010802c0603000c6102e502c0c0740c2d03861708043c103141da07030507400441d800030352030301c480e070905196403504402da40c805e54040707450b4040003609c0700e01c4004000790a00340e540700c2c41b0401d095280043c810002020703a440701c0140c54220000c031003c2684903061b8a21080c00207000c2e20052242840e0051884100315a0344021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 697804370 1250 697803120 697803229
    0x10e19171924020702030a022803050c031e061b09060318070801060b090d0507180608060117031204050304050a12050c03060c04170304030204050702100507110a0b06 73
    0x200e41c60090b0769244c3e4000307010b000e240c001da43c2004074004006840d45100f442030311455040e01101c1400c04c00850146024100c40d81e88036003054201004900c11098100340003400c0c1958550028039240d00c0b48498240c0e004a641e04001014503000b0641000d0388450000304011400c82e00e0b44207212112260811140500e45548440c0d0a0b511540074240610341c09204000f0549404112043d90030701480580e04220f44414a901140825410080c40541c844204004406e010010a80140200100f072030849405900e0f01e07889100e2000940c0d0310b050704a0114092080034411900103100092032495829a64800300b4081c06404c1002c0e16980101d803c4500783d07080100d4460300c03c5140803040c502d0700742804803050990002d00300c0b81c01076100c107000110050f195849202e000c0c4203c0d40060080c544c10034090405d60310002d0414080042c121a941e580c09000075008440c1a400400c3c00d2455540c0070104150601410466003000d1204403400d440c500489400f01159055003002e400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 697805620 1250 697804370 697804433
    0x14130f06230a050f030a0609090b0f07080402090c181c1718150d0c0c05010b0d0803072a06141b0403081b0601090605010e191719 57
    0x1542c0548810301c000f0490401021100b000b039440150707441a000100050040c1e1940b4020703040761443e92048850015441c03c0c0410300c2d44000c890f0b50300142d079180c19170413031134254042408003401609104c0b8040707000c550260f004540c005996024000a08104445007180c8180e0260707842e65070302030f200300c1c5418000081e03904ca61022035444102d031000d4002c3c12240c0c07009020b00400d86d002d002610000c14001c102101c40395001e40c1442e50080d0342d41103840f58880c1015821510841d10b0684112084260000000c400d5400d40e0343c80b035658201044840d0100301c442c0c612013406c42c0d09282030030900d1520404c110140d442880c0072a0f40d0b948a25659403098842d4650071600c041c01c0034241e50a20040001509090080060311901e0442040205c001c9110b14a130890a0704064011601c460342800b0710750703119401d080d00100895095041180400b41076141080078011184500c030084800d2400400400030300450904c20701c0c94410b08690f038140819844114554101004585401c491 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 697806870 1250 697805620 697805687
    0x62a11040e210a1e0302040f050d02090a0b041508160510020703080306010c14280b01030b040215072001090b12060f0a0807031407030314130f06 64
    0x1004100c02c07003101c00541c0e2810384a4403041e0007503400302c410450f090b4019039030000851940c0c00304a41d04c2e2005a200c0b41802071005581e156034211500958500d034909000d03903107034034400d5040803100000140c84031702030300420081c048580000c101586d95000020f403030031002400c4a24818039032040d1040c1910741c3c0411411600c3c005d4060f0050b4407907102800840d405000458001740c0c141400580700c9215950410884415200c0d101c0a412580b410840d4884245c4411000c44800c61009207070b04907551150100c80041c00085d004c07491040014003191140c203400c110841141b80c05507241c3e440e520781820b11303d90b140071810310000d00000116065019401400a40703580c1020b4a040400806003040b07140b0004246603440050100021040c5d21a0f40d0000f020b0003c040140c003602c1d0450801950809030002c543c81d0590003920200007181d4400c1103122880c0c2d8001086644031104403034180e14601c9030708014029503c1440018505400021400b0f2600c0d5001e00901c03806100c203800c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 697808120 1250 697806870 697806883
    0x50d0b09061518310203010e011118030705040513031b0f0b06031609022101030f0b090c19081005010b1909150503180c0a062a11040e 59
    0xe80c1c1000e026107a400d54140002c110550003c4136071413100c0c2160079451501c0980c54041d07110003034216540113500079410203000d40007101503038800a22140c07901054140e124400e0030b00071200348901c1ca00c416010380d418007000009020040c0300303020600b4402d081c6100340a0303007031045000c44c9031200b0001d2010a45091a034046401030300010b02410140c40e58070060300c00501070b5504d8040d07401c0040c04204005090400b230001900c0050300c03040c8005449413000207005c4810140d20202e4010000120080112225107034081620601070b140c1c0a907140c504099801c0c416404006501c40b40001d00320361000d4030807203815008440340403800300109402c8030380a005002d4902001c000c2076080300c1d01449000744884051030481004c40e41c91044883c0000c0711b0385440d0000f10b0010502115a490f24044444041090040d004986491000031a100e44600ca80c00030700101c1d49101b1036a803050480c9402402c045146026402c20b145030032883e146e844108948210702d0008018410349000489 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 697809370 1250 697808120 697808161
    0x110c040c030b0307061e170f040515011e06020102040b090402070f0c0902070b070e0108180307080408010218010f0206040204090609060903030903020609032d0c0f03070c050f0d1506050d0b0906 85
    0xc032009440e5250002003451004100b0f840368403c1c146090bc01c0d24a2600490082440031900403941140720484403174004958030050440e170040c0b00503c0a1800300007110805902100d00680d50b61040ca0400308144003040041c01c00340b8181d60002d01d41c2c0240e0000c280e40c0d817090809400c150b498500598821140445441c0050281000a0041c4031000058400c140141d41107a041030525590155164815004000540d40103d0544507070501908079904050b02402c211200032a401d500035036500c8003d101a205076200d44400040c0510740e40003410240c2c0140d802e0150440a013400742c060300c3c8002d001c80051143c8000200d1101c4040103071400341d40003100403900d00b82040110744404030b601145031b0819a0800c142d00b4030309010400110440c007498041c0d92220210b0030328640c202c0341135100c40d0280103032031030850bc1c5941e0f114902a42550000a203400101c0c1c003061280100300a0300020380014100c0113117030600c0201c51486220700c801c8411502c182d03036030540303070004141418078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 697810620 1250 697809370 697809407
    0xc0605220204050405010f1a0405011224110d05070f030b030c01140906070f1a010303080a050711060c0d060915030f0302011515020607110c040c030b0307061e 70
    0xe2080041c5080d81086400501440c0045100da446501035400c13115001d001181440803d121801c050800d40580c0d4014041280702440d81e01554944450b400000c40506071042c0c00b903400c5889500540c1e1029503011500072046884101145810000b08420740c1d041c004600e48100c1904110b00c01e0148144242002d0050501d000c1e01c1001541c20b10308031078081c50010420310505c007003a11240302a00d0064003d18555035100110f08103120348441183e8041c2d40701c04a04018030120b500b00d6136031a0407811081780004c040c0c3d1010021609074006003d80c1a05004074414003842d02c5489018000820002d00c0811125990b4408481180e81440540b0581c64903018200040344484940180c0540a8000883d280c442e40c484c004100c104c80d0020002144c180d4a2074054640c1005440d40c402107a041c0000308507882c500d0260b8480f401c0c1250351080c4c0e142c60103920217038400e0700841803e1401404880c2e041c0d0700c07280068910780c01204a03804008440c0003010503113104628001c0708881c10305 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 697811870 1250 697810620 697810681
    0x306061d0310020a0e090a0903080a02070f110607050d03021e0405030d030b011106070807030c0203182101020d0c0e06120103110d02061801180812031e070c0605 71
    0xb241c400a9007043c6040350038040d80106952158035040700305482070025140015085c9590f00e8050a402400f500ca9292035105102c07620001d880510f11045858020100e007196685000000f5001c3c800d071000100749000d01d1030f20840c1070b40c0640250a5018514480b00040700244882030000d009500c00c1692550000307500d040e00d603019038000d200355541890300d06502e02841c0e803d107141040999803200041d61080030003c1e8151300d8810a03400b55481d10141d854a5103200301400808504c0302c510b032007007521000c01410120804502071480c461100259115500d0600c0c1c00010011030341003801182c0c40d14501191440c180040301c145034491a003003c6070742d003982c90f41c580306049a8400342c0c02030850b84014015035038440142c407001800c0742441000c40300b90000100300d08540b0050312100c4030a90400d200e80e200104101c208200d50025280d01ca580d00c41a0030350111101810007441040c100611203074a40c0a805146440c1c010002403105444001040d00c00012841013244202d0104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 697813120 1250 697811870 697811893
    0xc01020d050f0f030a0612030c0512071221090b06190b030a0506040207170715020301060504090e01091a0103060501080c0f120a0213020d0e0a080f07031107060306061d03 75
    0x1840070715080b03c8031440000341b150316603221050308840144203901003440d5a803401c1c1040030030060703c100a00d980480c1420a41250f0f6401c5915200c81c00480034400b41c100c901041e00d00d40108002d511192020a01146c0c1803402c100c00545025681180030f1688401c2614562565030021000c90305580b80c03a80ca182d485d0b01c4804000c0802400d038640c17084d001c0044502007044569500d00000080d01ca071540c4117003529001c12581221a0300c1d0740a1070040c80100075168001041d2022a6080600414515280032070240103100c071140080240a03144105006107400e2001705041e03134820401040b03141d8a074448640da0b03004162400c0c3e4454207903d1030122500741800c1c1603003140000d004849554520b45d00090b81d000e400c140845126502040c034441840050203200d5903502c0c90400341c0b1002000303444040c01c83c03160200000c0800000100b98082500c00d0003102c612501050540300317865210100100980000c1c0301d01000200c0002c400c070000c41e19800655481c0b00024010203815268 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 697814370 1250 697813120 697813147
    0x30105011d0103240c080708130201120f0605090103030915050c061512010f02030613090b070e03030c1506091509040201030c03020c0303270a031403150409050c01020d050f 76
    0xc40e9041c1103412131454440b80c5420a41c05492006813840e01c48070b40e01e2400442c02031080e8801044229900d10030101d520260360410400c3c000310501030f0000c100007003d20385440c0549510351010340c2261003d00008181035001d28908180c030300301390803c01d21a0000310210380350b01a40c0740c0900e0740e0b040080440d0086074101d010001050010380000940c2c40c440c1011403c4501410038040e419400100300700c02403a0a0b891601500d11844003085070a6654440341c01c080c000a00c084280700c0c64001e00c07105a07404206803072490a541080365401501e0b081e4400d0b1a0340c0035500b960040780d41e82c0100f2101e0001c4a0340302031980d4041d01800300f40d82c0e20740046001d00618000a024150300304218580650103100440c800c0c40203584443d4131025080c0c0c02c14900c04041140f034800d400101c0c213240040e5102d1000c00340e0036050b03909940c0741c2e21542c117008600650206001e50241c0b51025443c20000e0101d4101000d8500341c0076a8829540d142d01514144541800d40c0400c0604000241c01c1000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 697815620 1250 697814370 697814393
    0x3080f0a0c0803071701090e120a020102040f0f090f0c0531032a0b041815060c110306090c060c0c0d030207030b010504090314161709030105011d0103 66
    0xc18903050040401503118164942d100380c40c0a0300180d20502d49a2404454101d450300510b007240e01001a0040c4400060311010300c5000ca9074105800101c003084c1b1403003501a02c02901c0c040d00740301c01469680003c4100080c4070311945d5a00b608003060b21102c1c40303141c4114030401e400703500c51034602001118914010390001c050300c81e10510030700c000111000703c18400d5001e9031040044c4c1000541c28016082104400141c02030741d040d1382e140c01e101840946080e1000c42c0c0d400000c0482c0d04c0e45002003003000e084508400c3c91908540380e40001c40c0c90313010782c40c0240300d4012032440064200394010305031140c10885031014203a01016840000342400320041c200c0341303800c20580301c0007407001001a50a03a032007242039005900100007841804420304400d401070804982c204540380c103076903000e0b10f5030300303c9c4580405080010402c0c1c42c40c0040a601118035036409450500f805d24541c50070315154102d002464040e40c0703000000725100e83d01d81540c0f035041c4c010400d0420980e00e10385d00c1154411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 697816870 1250 697815620 697815637
    0x160509070c0b07020a150203150d0c0b030a1a15030112080d0615090e060102060f0403051309021806030f01151709010911030606010807080a060512070602120403080f 73
    0x1c141084840070500310034106005640c0c903405410701000301e003422080725002e00c0c0005003030f91040040c0410500303840c1d040031074200180c070004045581400e24148a110b982d110b10300c0c000000042082482e851303803100451401a2a0400c520328a01041c020342d411191880042d4400030001403000b50b103210710014006124010292405514400003425220f8a80c04800b49001d1524001d00751b6400101c0100a040b549418942030320b06076000035036134040541407601848205000c2014103104d5006c0b45c0d880721640951a50090b80c4046400003940602690181c03005c031a01c0460072442e20a00b12030007420312418134501da07400e1402c05941c0c0b8000a20800c14010031041e4410000700442109100d00290000001c140b462418081007007214801c40320700c01d802000030400b087c0c0e0082d0032107820030035070711b040d0120f03654650b035210081c2195002503600480d103904000360717000005a1103007500c4069090760195081c03640c107040c43d0301031804020035441e4103101203041e20102901811108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 697818120 1250 697816870 697816877
    0xc081608011a040f300302060a091109070207090518120c010209090f09060109090302061522091a040c03030503041106030901200f0909040f0605090303070305070216050907 76
    0x1503840361036001e600c1c1654417505150f0030002003280e41c20b03160040701100300d070000082c0c030040055580094840700c00904000c500740d070350714908080c01200c0111850036003000d84050400d080080020303503100024428200054202030014516011200c884070450a00b4001003220048005058405801808101c0141e40d800c3c800d02106a036140c0e141030043c0066080320380907062100153341006416008030f0380c1d46041100c0440000c1e130009082d40e02a030461421521520102e00080340341210484024507007008003c3c01d130501609034000c200481c8207a010b944600440c0c49842400c841c2200e001d070a440da141010008031740203c00030b6902500c500790002543c2400c0300060007580041d030b0840380380d86d50707186000600c002d500008400e207000141c00078200203d400710150b6500c00c02c05240c2c0034501800201c1c0412400da22201146035110f00c2c10302c03203807401c007030016900e4004407884800241001c1c0411050360010500352000142805221442803d1600740f040c40100541220100b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 697819370 1250 697818120 697818127
    0x31f060c241b0311090604050d0f0213020d051005010c0f050f030d0b01021510181b0c0c0b07232103100608101403030705030c010c081608011a 63
    0x40000901c82e0040907480e480e0b158041c0030300c03503900408407006a448446004000c01c5642103d40d41c04080c0e4086400440f01c900e040c001c5840c0003911060b103410001d40042d06980055810195074025000022001000300180c0d61070390710b0807225000c01e02c94180400e1420a6820118400c0e040241440340504100d610f01c9050103803c070b00d141d21a9210a0206e0340d210303200701042d80d050261603203451035a240010079040c1440d850003840c000d40f18410b440701740030107294007000130b43e040100a000011a89552000248409420039000000c01c480d407081e007200119030b100c003c80580b4402504201086004c4810502402068032924244a094810003405132041c040b070304d10000103103003400c0550307841c1c0c10840d4a40141503100c2d0072000a00801c00200140504c1c1c1e141c0e4201102c000c0292046500d0450010a040d80324175180580103000c00101090020415040011040c1080d42d850006994030b54403070140c080d0407540080041c491200400c400900d00300305d2120f685032031051034079 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 697820620 1250 697819370 697819433
    0x31107080f031c056a3506070c0302010c02030903190809090c04030309060804350d06050906010314070c0309030c0803031f060c 57
    0x6418071211070346150340d100003044100c00066000c6000da40c4803840c0e06200a0500884042c001e01e2860340da9203c1c40050500e4021652680e10030041d19a0703030b04406019280f46001e0240400801804205411000f001040041000781154804c403004040c507400d10f46400c81002d00050303d4030201c032010310142c0c603000c2c0b42001705005150203038130280c0f0789411042c19032030081d00b5502c0c031802940a40d0014090741c030194501040c01c18540b0404e1185038140380711468404071601071441000d810100043c208104a5003140041098078080d494000206036070b418104e0b06010b0880c2c0080c24014040d955943c0b00c41542c0140403108200d1400780881e458014844049412440300c2d00903540d07c0d04401c12442c240f07000400d802940030b1906200c101209510200780300c42c00f0b003840f81007003480a10740c000d0501c11040c4401643e071000f40c401c011607031800a030782d4a40050b581c1010800c01d91044413410701e268100c4c40110f83d0b0741d40360642101159100d40780b428200e44100b2400b0702c0004445034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 697821870 1250 697820620 697820623
    0xc030702180603010b0406060c14070906030c060225050d0f0506070201090201080c04060f0503150d0b06030d1805060a0c120f0807020111031512010c031a0406050d03110708 76
    0x3001d4803481110714040c40c00100301800d41c0d203442c0206028a2034448103010503a44155402e00590b0019150100300c49407205292130b081c0030b0303030100c51090b1070094040700b00441c0e000785c2d004480149c5c5c216030100c8540a01c41046841694a2440900329208100035a0400300c8004220b24003a40e0b140009130559251141048002c450300b00060359105a81811503030002c0006403c04003614107581014142040075120150980302d000900202000050000c1c4078001c954104440103400c01034211070340c0c41d0081020b141520301d070b8030901a000814240c02d1280c80072620880003641d400d1240c61805040c0003481c1e201201050803c8040c40b029400302c0c0d0030032403205022580765184000d030083d060b401080360401400ca48116414000554040030030348042d250420310300e50600703250307a5040001813920226018143c00303c1d4240060024050307056480350140800e150107001d203000950041004980543c05405c0e804203006c0428004644518120b44242c40c2c5001214001070301c031110103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 697823120 1250 697821870 697821889
    0x160f020d0c0b27280305100f0c020c0310020a093311071a0417060a0b01020c0901030807020a030f0803160912020d0516090203060414060a0306020c030702 68
    0x2820301d01d2000440c1c0c04000034407022015110424020f00040c441c0890002c0d607040074072030301d005602c1408040f11024500340201000191b9000040796a0402c800220320050181000031140c0c00e807600018540e2a40041415a80d864004020b0300b90490207800c01002500980c403020100841d081021990b01c0341800c0b000c3c8452603400b5241031180750900c60408041888082d002005a05040441208400680e072801e90301c2a01ca0340105000100030004c0c240520f46c0481e948200d0700307400c0214a03c0204110b40034185101050118030820001640d0b2850482001604040100010404100110050b00c50031b84000c0a00000d07903625103440b80c0760000d0040681e01490b00105104501035468804c640c442c01c3e030708248416a160001555504410300b0f00640034094007a030700c00400c1001d00842d8510141e08040034501a102c1d01c1c628000e400c01c807070300c0e0301a9142c03001000c46000800300086c0700d008020488a4030504540d100c82c065040311034000e90a1000344100c1006a480382c420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 697824370 1250 697823120 697823129
    0x2e02070606140613030803071b080a0305010e01150509040e0f0d170402131802040f061403011406010c030c0203030f0904150510030209030304050a080604140102160f020d0c 76
    0x114241d414040d11021600c0941c032a68841c20041004424a00b02c0016000c200d980101c00b1603101d60b26081d003501c00201141001c0000140c009580c02040083c2e0702401c0c1c03070303262503400304050780e00c80c422002d02880078002c088007042c50001c1000d4242c032802c000c100c00040a0070100da100b400c00107180c13420070702c103265454581012071490710540d0300c8814080a100d013140d0303a0405081c40e801140c91500d12000c41920103440d00c1c40b00c4100b01860041c0c40c40385601030402c1100030180c0300400024000c46c011642030800c0706601442074501402503142c0240760340c01401a44c0c5490f0010358180c0c050360011414030082c200c0b85000b50f502803010b07122640701180304d1665214000c0801c41290a440074019403100940b40901003a140c1042c4000304080a00700140c6d1044007100183c69401141d00503548036004150102e0600000300ea0f103401036100d01103c00303101c1141c200b014242d0184100c280381d030710300400307101d400310390420300d0030034458005020850525180d80f502411644c81e50807 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 697825620 1250 697824370 697824383
    0x1f020106050904050715020a030c020d030e090906060a090b3109050616020d08010b210c091005030708130227100f1a0309030c0d0309110406082e0207 66
    0x1b001703142c4001c2e030012042010751000e802e03800681e1f034014005800c580b0300640946004583d03d03042502410107815032620003000e2040e18074011030402d945400c101d50540c0103100e182c500040082e00c134099200c24980090110b1383c43e0070940e0b6402d20b00c0c40c0115000340c0c9003010519001245c0c1942c0f0a03c00540d00a81c0508031138038000e040c1c90700f03d184018440c0119401400b50100550b4000556410354000f111026615028880f504981101c04030310442c00141c1c0c842884a4144400018680c01c10142c6100c0c030321b0751100d0300613540c0b400200c55010100f40b00d00c0000307000c09002181a40040d100400d110780b100d0b24a90801c5280c11602d6241c1100c3e20100c06200e812410710200500038000341202414544c140844e046c0c8201020704803003039180010002c1020300109209403041c0700a924101c1c1c4004902c00c100801030619800c0c2510f6041004e200a600790034140282d005842007400100780f240694403025444c4030b104c41901460200082400b0414212070000785003840c0102d5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 697826870 1250 697825620 697825633
    0x110f0a0308070f0614091f061e0305160b16020102032a0c1e060306040b040c021b041407050306010309051b03010e0102090d170d0903091e03021f02010605090405 71
    0x1340c0070080f02c14118002408450070310410520010000c0c0d03001410345404136000a90300c00301c581c58048c241075003000c44a148046005020202d203142104c0c1268001c8048501d56155504890540e9005008030000c407801088103804c00010300c80a102c4107481841101d24040105104940b03500800408010551100103e400102820400798642c2901100c49001d0024900c6919400403102d095040c00b8003004000140c01d55034681c0500412103024205002a001c0303900000c1d04c800920209902d2306100c0400340010b4141032280000d04056540c050b0b4558498903030a5856820080900307042545802c2070b2000288240b22010000591034820700007445500b04060030740b10707050f2040000e6841800b030f10440e40e484100e01b0402640004046501e01c000f5180c6403130b18400d52040442c40d038203156000e02010707840701499007251031040d08040f00a0066000300300c203020900c0040d50240c10300060000003100c105070380028425900000803c10344c0c1e600400c1a40c4002c0364261000d40091 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 697828120 1250 697826870 697826873
    0x170a05040b0a05090c0409030224220510020f070609080a17130b04020102070f0816050105070c03061e05091e0601060909020a200a03031107110f0a0308070f 69
    0x5841c41d41d000302002505001614085913a650b8800088558038419529040580c00b418024012803049410785171b8a000e224103421000d680c6503034180c0360014412282040640c1100c00c80880000440c0d108000c0d00003500300160070b5010b900103103800d903030301201041581c00040462081e64401171080760099140d500341d00b405881100001d01c0b1340140c07107401c1c0810100d14000d203082d4003020b83c40102e1114944450004034500000b9811105400412080104206800042d84100d92340b00c43c00c403144450b01c0d40c0044420340907484000381b82c5080703640300340001403081e00017042e0b41307010344031507803000601410804c1a550240c42121042e0400e400c0c4003016000183d0108503c40060300514055140440c004d1504120b4031030800c030302d0b1b40420800003003403260030200080191044407c500751403a041460321000344608c1140801c5c50407080f01d00001007081030f2030302075810203c00e00102310b1140600145101c91542c09038805c03200b038030100c0000c0c10700c0701810440f4068540098441e00c01e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 697829370 1250 697828120 697828133
    0x60105041d090111071110021609151d070c060e1b09010b030601120902040b0a0b0c07060f0905040905031623123c0703120b01140a170a0504 62
    0x51014188040d00c08109005c0170030806817001005000558500300a01d083c081d0481c1006040c00d03090202c41d0643c00001500c01643e04031700090510071600ea80300c280d640b11f1490b195841c0d80149800c1d40c8242d0005861a40508510203803203010b001d0105011411444180c1440b411700c5000034148841c100700d6100382450044140504190074646e4910304040f4000b9108510307508140030981c0e10340c22610119200c5804c14241a5805882c4034a0703151115403015454000d003090107220f01c01c1c080c0000b007580c4034600c04082541e0b20385170320011a0a00b070902c80500403614083c2c2d46403108002d12204100041188003a46001d240c0c0f8034854589511050a2004840380c850040d5003c1980c006c2040c003000e04454041010080071240000e00d115400f89012080401c407601130b44185080440c480301500401540b4402c1c0c0e03411b45044840c107642c0084800418425002a21140071000c21000e26001014035401d82e0030108016808140e80807001c40040b45c50180341c5807075030107000400a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 697830620 1250 697829370 697829381
    0x71e06031104030317130b1504050f06090c13081606110d020d03051302041a0301060905190c021c050d05010503010203061e0a23120607050a0305060105041d0901 71
    0x107060100c540790502c1c42e1801442143e82c2d20489100038624400300e07074084111041814007507031100d602d818510b0945500c81c2d9551460b0301403401507080c60300082d0040d04e107034101031055900501d245459201c008107680c1d01c1d0004030900c211207400308030204440e101002601c400f100e00707200c54048281800401084001403894103102584250076001c505a004240300081c0c113064a000107441ea10101c0195011049000194000303261614640103007000c0714038048024819230007480707041e540e01594412900102d4a0204200c09007000500c0030106400cc013207440d100b40304540250f005520340545081e002d01c90f03030011400026480503c40c51030b018031703801410110000c5056103020310105000000d05801d6014050341c5910020309a038401c415940513040310544035900300e8107101c0a52203841511204c6200308207000010105203000034900b0b2040c5d035182d0341d46090607128007007038000d00f202034002814002e00344404540c4248003408800584609075a00b0b44908101e1115402c654 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 697831870 1250 697830620 697830641
    0x220302032b030b04020409050907030221070b0304020102030c070e04061a2107081b040e030705120d0b150a0807300b06040f14010815090702071e0603 66
    0x1ca0038001000c012070250044088900905000c10310981480c0058000d2203160401200503182000f401181e901c0080d100095a00c29540c0441817000c01440c8001d46041c1505140203a220000034030a20416002654000d4418011a41005402601681085141d8000d03500405491003004148103050203804d40c051400c00c0b2082d4204002404a404803012404800c00b01c0305840003c980000200901401485240149d82c520030041e01c0888100d00258182840382c1d091911410203502e010088803021644500181030480356202500c509811120f010003005a4460380c0c020340f61522100c0140c8402b1402c00140c1d969040c8901411990019109504000320300c1800c0d400a00340a4640030540b555000f240540f600c0241c041c00a0041464090381000c4007080005002188e8070441058a88413245801d480b01d00300011145c3c240110b44a9402c005801c20a002c03604100c40e805030400242d1040e15000c41c1c8541c007011441d10b04460900505019402c1049081d41c14400d00300c015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 697833120 1250 697831870 697831903
    0x8031b190b01061107030c090c02010b0906012106080604030f0f0806132703050423060306040506010c020d21020a0f030f180801020d0f0e100f0222030203 68
    0x24140c8401c0d2040038140156020701041a18a003d031000400c0315200941e408080800803689444d400c1c0042c0801c1c216840c05503081540112162500c1c49890384038480c180d482c03103108211200c420030800c640314003a080310b607502c02000c0342c5c8210900c05a48114020340701c445901b41580e1000786685022342c00d81d010400380134244080da40c1e0740e25500c082105115008541b1404050860142c1e04400703005030040700a1103000700c20103800c00040c1c0111299001034144101241d4031010441d42007400055000c2c0041001a41038501644101d0b046501071402c401101159404950b402090000603110404d8031b0f000d01208101c803080030310004000d8805081101281c0e50344402c0b01903005002010320040e0b420036454103109a40215406061308010010f00750707654802e5000354042d404000e0740750700f072502c0b0000301c00c41406103405880d2400c000b460b0400004180078010301c1c00f2504444015001c003c0003400c410101c07044c004103030030103140441262a501c101071800c44124036603030340d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 697834370 1250 697833120 697833163
    0x6150509010b09060304021201091b0509071205070207090e0d02060702030406080703021c1811011b110f06030a15150e040f02041802030114120706031a0d050309093d08031b 76
    0x643e84491007850620007890043003419190a141a41450781541007148854689444480c00d043c000176801450b07140307602615207607110f64404980340c3c8a107002e654027203050036001c035611600c07950041000080c4040c1802000072101002c1040d43c10024112001051000111003803010704444286409801d0030035000070207107a4a0031504808020700a0200301c048011080c058440c0303c4d40810a9900030605e541c0da00d40750128500402c03207411410401403a2003c00b080c02518101034107080419034452114903000c0c18208000341582884a5a0154080c08001640d694446c112420240b5210000d6160342c10091b4000c3c1562451035a54425078814a40f048030100108143d000d950301843c0c080f4207100070541f48220303091101e602c56000361550380b00b40207001d0040003034540c41c0011102d543ca152075000d440d00f100491108105150041d12104001c08002c00c085010813080c0e4040303034000144d540e0000e9080d80c005410742c2e01ea10600d45031660104005015201452030003000c3c581c41e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 697835620 1250 697834370 697834381
    0x905270d0c0305031b0a2c21100f0e10060509010b0c03070b0c03040b060910090e07031505090d0504080c0d0302011806150509010b09060304021201091b0509 69
    0x19001c410000981400300c000040f81c1501d0520508085c080440b5201981d00e0120400041440c0341103014078118030020700180007002d140d20500c0c18850343c02040620034000040303c07040000703a80d2030244c005100d0688115018855802050300d403000e51600003510b11010702d203030350410702c2c00145915060b24200c2c0c240a00e507640c407545410355200c1c00c089038580ca06140030070301e103210741c3c00c2c064841d4043c5405c0001c8a105640114811403040c1214440c581b0341d078013440345070401600c01001d0240c140c43c0900101c0d46960092801d02d200e503046034207456480d05c4042d55184042602030b8107584480070800c1d0350508002c040c2e01000d451402c80d241c240380900c003548841d1140740b168401c04140c9400030a241c402d41045500a2003080c0d500b0700d0f000c107464003600511306003001e40040705015030001450b00d03040255904171101103401ca413901d03802008011060703100030800c9030700078116103480000420900c40d20101600c101044401c45401340300b83c08940320365504c45441241220100030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 697836870 1250 697835620 697835627
    0x1081608010513140a08030f0610050a0206060f040908031e06010903080a0c020622030b07110604060507110d11010506150732010506131803180905270d 67
    0x3c01d040e000030038102d40c00c0e5507100c080d00340b02a41002800e61301000c02480b9880804001c0c03280904011140c1d403140150303100069400f40900500708000d0b030400310005407582051f44110001c000700401c0003840c0151507640100c40d401c2074490640e1141a400368030050072140c41d81d0b5810503001d003403020b4038500e1680d95001134414070201d03900304a2420f0300d020864036464142c513107030740804940d4a0854903a030f8400355140000d00c0180c4400c480c08020800c014080c403414202c4800d41d0014003142e9503283c0b42c1202424020707100c40c040040400784007910190900a0030300384502e541d5240c0858009074452420b548015150902c607041d0f001b01034440240f03250403100442e500c0350f441e1040b1104038880182d40344c0515400c004001c02d84650000d000d030107510ac81c0c40703044200d03a4420549420007102003102e4020700003003104882c0e064080040703070003880ea04a90454042400c000d947c1c0f148a05829640240d61a258011101000d914500f01114508600c10b0400008010085101c280103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 697838120 1250 697836870 697836901
    0x1514091201180b061e2404050a121203020918131a01030302070b03010608160e130f0f2d0e03210f0c0307110f030c07060908030f250209010816080105 66
    0x40d10124514100d042c01b10b0f480e40a0382c0040400915a11199644038480d0000fa02e045d40c0444040c0b40300800050090b0180c0300b503a41d0550050701c0e911122070220b0b24a40d1007840035000c6200280005044800240c0c1c240000d11240d03245169408154914900039140a0355034200c0b403282c0005100511601d58420005940300c642c6620300460000b0110054450801010442d900103052503000064031520b90041d420b4803100417410025054107014480858041003000d13105001c203100c009004070002200c8440c5c03480c40341e800280070f4602d85001813031075100d640150b08940c82c95015036003030407004000da5404240c1d82d80f0904140350551542c08a4400280b07484180540035000a03811601040180c5003450b14000b2207540e1140c0c002178640e00c030018170400000442e03050300409c2c820408410344000b055121181f90402ca580142d1101201440b03010b201e400c041c42080401581c4c46407601802800440050314900d444000c207408041d81b42c0c4c011007003507810902444000500381804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 697839370 1250 697838120 697838149
    0xa11071a0a05160b0f090f12040504150b07150506060909070f09081204140a06020606010305071115150406050a051002010e06010b041514091201180b061e 68
    0x20701d90380c40c0f028645225900c10048050282c0740c4002c2009044803038004104d0060150a0032a0000c9000005442d0b075070f0400e0120a40c0388a00b03000070030413070a06410100d201103500308001e42054450710061b4071034100010540b1058000040c2c4041d94041340b0540e0707045402130b259245080d80c0c00c0082248240003521410802064804a8550034480c440c3d120140c030042c2d080d00e90a88c400b2480c4000c6030041d014008041400071008170181c0380110b140011034000360090704050751400015001044010044000d00090340c0108455003804d0100140102d2240030b07260312800d0114a41055508081809026625150090025640d86204007044540c12100c07503003900101324040340074103400183ea98051047c200045600c0030014060800d5540e500074403a90b44400c0841200c0c018001e060024080788100042d60301820440464611001070600108203400300300b00f030901e8090950025214643c1890a20030a85011a404080404c0580e00e04909120441c00100000300d20342c02e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 697840620 1250 697839370 697839377
    0x4020607021228021005031014011b030201050f0c03090a06020d151d091b060d0605130606030510050f010807020109020d030504030303291e04020a11071a0a 69
    0x110280d03106041103114880e00c0342e0b00004500e0011101000f03032683c01c601c0224440e200481500030283e108000fa644a10030344120740c5049450520581d00301c00d05148800d04000c030301c1783c91014228526400e001001c0c429800000d441c40d0400c140c104001e809080300c1c14a031070070418080c0c02840048c5995419400402c0181c0d9968560100001490340385490410307611305c2c1c04c000030302010301001c0d0a90f808049501400c5962000780d15600c984180880c540481079403840e0300d0b140c0c2005000740102d40314a050019070036880e000010041480309c0500300600342c48201c207100f099810300a45412007030301e1500e4200319040400040c2284080440c96040008903800221994801d4101e0101c0940250040f6480c4401e0300b4014001e50080c0400d0700801c1c2005102c41d0f500741d2200110740280c00c080e01c03601204800300304000204240001c0f510136190104110340c800d503510702c02080c103956036031584010024800c071014201003d56110340c2ca5155032071010790b1022070050464030b03504000d2a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 697841726 1106 697840620 697840639
    0x320030f0307033905070f061805090705190c021008131515080309040605100203030a0209211b0a0b0403060c0302090d080a090605030402060702 64
    0x30043c00640901441c6160300f01c219402088500080d014280040c00800818084d124001c001d44094000000030080c0c1980d609024005022909204200f0151111012115521413080c18000c030700b140002002507100b6400c84413101c0c03607644440c0c20030050440003001c200481c81d04900985402d01d480b103441e406100e005110384000d1824500002190361640c94000340030120f003402c0e0b905e949050f004d88440b05020701c081c0c0100c40085441e10b185008200c140d41c40c03907101d0f50103050100d0381d0400302580802160340c0114826005a50768a00b140071426500c526084125013114030003840310100030204061900032000020407a51000302c1c010070a06841d548200350740b00360f00300001c000203106c81e00009042c07401e5041c01030800036007074007141c8807940308d1404aa6018000400030316080d000200300000e4002c0d45080ba04500c1c2640c0454a540300340800a4070600450 = true := by decide +kernel

theorem cover : BRFrame.Cov 697661870 697841726 := by
  have h0 := BRFrame.cov_init 697661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 697661870 ≤ n) (h2 : n < 697841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
