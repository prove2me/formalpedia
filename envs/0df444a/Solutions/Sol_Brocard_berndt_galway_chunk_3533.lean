-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3533
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:56:19.462183+00:00
-- url     : https://prove2.me/submissions/06dc423c-3a70-4472-8cb4-f4c61a9f220d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 635251798 ≤ n < 635431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 635253048 1250 635251798 635251819
    0x1514270706090b180a0314150c0301030605040c0b03090c2403061e0904080c0105090d080c0a09090c0504032003340f05120a120e0312031009060e15 65
    0x900d50360308803184040c0150002176060384d20708001c07041c0e944082e118482d60142c00c0003640c11811401060b885200040040c50850342180c0b119402460003c1c4200e43c40000060301003418107061025501c21103d0000400c048a007002c20301480059408202c2880c12018000010840d04076042c0ea61004c001d60320a40c4841e641d1503102d07282407850f0b0034107400064203400d02c0203200801c001030043c0a0110000c1c80740f5241d40403001c2d50f45400060a50000c0c52003004188441516401891141030328035201c2d00c080d440700320300c1049400240302107010440000e01001000560012484d15000350001c10f0b05013045040400d490703181301100311400c2011441c0080f411501c0b12010b41071008a40c0c8038a50494413000340015210317103030003a10b00c10302440d0484080440001f610502c2c0c1030f80702c01c9001c041e5206190076900c640c65103c61903030602800c40908004c07070307690000c3d500c0b030340e280207490039201d203041d900c942280e419821009080705140100152107101c03070a0425000d10960700c0e03001c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 635254298 1250 635253048 635253067
    0x15031017101e060905061005074101021b160b09041d0a03082809030207030f03030b1c0f020d02041d0c0f040c0c1514270706090b 57
    0x20035159100e0b01c1d078228604039022580e6000380c0d0103a0321405044e5842c00c0c00051810080e1030501444000404880c1500c003051007450141144104601c14a2001908581c48200071501c00c002500808141da5010074400740036408484d4107101301c45000701401d0b4940116000280c840014020300c81d0410002440d071003981c40326884880e81b0450110311100c0c81084d500e040c1c1d01c0386900030003a0000741c41f003008508107004840705600c0c0100301c01e46480200d070344039440380090b2136002025819400f80c070380700001180d010342c0e8104199211360740002d001d20201c010081d603003403482d1140b400d8812829118000458a02410218640450304048180703883d00c0042c01801c0d441080c01d4102c0d95841d40d001100c440040c01800f070b0b503001c0756002c03241d46140051004440031240918001501c001064004c20040b1041c90500c0c3c00c0c00c5008281070800c00a1880840026194980003111069100c48022800001d03e00710003925000b400c101d03840e1070001415800035000d10350300201d0001d4840740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 635255548 1250 635254298 635254331
    0x61e14030f041e08071b0b070609140f070806010e0105131812030b030c040e0a0b09030d0513020f0103051b0a091d061507020105030403110c1503101710 67
    0x8204603035031448850201a840e0001c111703085602c08655003070306500300c4112800040401d8054070000490103040103640d4640b00c3c080d04190380280c0d01002044d060114580c010302080310b200c1000030050524501d840415840c0460507070082c8a40c02003200103001d280da0b1003003032190342c08803030300301055141c0210020006801c080c140103010b128054503020701e080d0107800104504030100d054410444a031b40c02c0c4001e0750085540d242141c0c02510a400000702d01300a01c40d041040030b021a420f001341140ca5800700c4205440111092411814403401c525020160305141c00d003c1c1707418001ca09001800200002c00309004540084c030100764002c10611030008500181204030341c80091800c00e05020042160641e036040c041e018013080c200155003800212104c0703541c1a5519441c540d210344040303495841c40100c0c40007a010301b80505046681c1c1c00c55841480400c0e01e04e20b0b17502d0074404030088000e0102d40c420078400d403104184016481e0003040c247d841e04103015011a1480340c940c00c859 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 635256798 1250 635255548 635255573
    0x2030403052d1501140108010510050c1905010b0901060302190e03150a0509160305070302010503060a15020c030c100e0f04110d020c0c010804021c060b0a061e14030f04 74
    0x26803503c680c07202480b00f0003142014904039152410440030591a0800454145600f4011240c220b0030b62240c41c070485102d8402000021442c4058404426007035aa00ca04880c01c810180d6079691600e08060345807070a03546190040c11075003400c5141681100c00c1040c1450080030001c1071140e038580c1083c285e1401d211407804184801c41541d5989801b0604c0802800292a44d400030701c2007041c2c45103441c0d050422141501d0b003100051403030a20311f0f401120300b070b417004010507013045042c14005500c402e1035011482600b00c035000350881032203440a2510300f0905c49207081c810b040400043d1043c81d009400741c0494002540c007112041601301c041005048900e00e00d640b0300c100002c0c00304240d18a07602401d0f5049840040d910710bc80904011541600240e60107507101c0c40100d00710030844440c00113030328200c4c8141e4001c104a502d80d4005101501e2075031210000c5181280c81070091844525440c015503194107007030540ca11060648401e42c003005050018114086001c01e0a0246014125 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 635258048 1250 635256798 635256883
    0xf0212030f12010305010501062606030c0a0b0c060c040f26030c060106120203010b030a09060905010608010207030e0d0803040209070c0c141f050904090602040302131b0203040305 79
    0x1580c0d07400d00491001502d800c00d200583d00c40d460607002140700d0344290f403640b1503402001c410030021890075201d0040070a010309100d0303251013102c40307251861300c0d01c40380d680040604207040303912500581029400d051008140017900c52040000f8850411400843d009486801308003110520311002842c10351400c1c4440600548400300700300a4050380064400d058a83d19500e0b40100d1a01e03031141e2090340001c3c018200b403000240b0014902c0e010780d03484098035034041c0703c000c00c410806440e5282140d1540d00b1046281e50009503481c1455046918a0a110700555254151040a4407002d00b81d000c0988028032900c803240104606510941713480000a401080e01d0034010758035451440c41e407104246143c007480005814009241c502c000010840e00c4940b1081c2c230303003aa03000820004010141c4216030300c9a003400003102680b92901e000c8240c01480f1400202d05c06604c4c0f5809080c0c045169205c00c45d80200018170004501040d0b07000340741c64000c0139503400024203448041d0001c01e440d08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 635259298 1250 635258048 635258077
    0x70516030b0103021c0201020c090702100e0706030b19090b0d080f0406080a1803110f010e030c0106120c06030f0e01020c0c0a080127030905030307052103040f021203 73
    0x31040c040c0a00150b4101d03482196100d0034507095484e00c1c0506895584041d0242e044801041910b00b0071940160307001c000c0348166400104021500c1040340d64540f44e41c20f0300e92128806019958040c498041c20314400c981700c1003c10400c00e440320981c902400390361308068450421403100c0e10307481d0b02d2140302c540c000350407503c2c2c07440c46c1c5c154113540d08a8480c204c0000e4100c0c01140080c41c451244d001019030b00c1c44283d4009502d07840c203440603140c1d2002c0410a01c189031aa1f1701c9401d080c0f0a40d012031313a041d8042c593340d000a10ba86425103055401505208000c02150300002e03500c080c4407003c03101c05042c08202159103144003001004030300c2c600c505a500010306e41401d410045000e4031684822a0100305058940c0c10ba14200da149014800d20b41500700d0950018401400c600d41c800c51007442c0001c419522540400d0458000810407115a408044000c2061032064402c80440361030000040c21494a901c40b00705014120718041d00031140318051106010b0b06100311401901640d08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 635260548 1250 635259298 635259343
    0x180a020a090510090e150c0d021209060a0c0917120a080415061401050304061805030408060708060109031e052e021204020603071e0f0215010602070b0705 68
    0x1240303024100890b80c0f00305103c05940d0100d0001400d104072001350002e14000c003004c0120507855100f2080281c0030402d00e01c3c1c240b2640c40c0502d40742c00100f15040c229a4035400f2400c21441d480e20700b07000070b002c140c042402e182d070360115154841c088500b08d41c0003d2242c212a01e07002011828040352284100d00020002207800ea0b007030300001128061441601e6a00950403241420310031280032340994030101c02098001c4409600c9013000e10303042401200c001406e1411070b402507200c85c4030481d046405400108080140034000c1c0300065000c252400d1902141c80c2c5800000c14510359800000e20421003c0b0700c26a00a04c0444c4117013106501800300c038043e0000084095984402e001800c20014845840695034207150090340d81440c040040040d00c1c2e1580e900704000c0e074200410107010064028036449038a0720500d001c0b076400d001500c50400c440c43c203c034001e0800c001003900507800026140100040380c1c0c0010907401701e400050f40d00392503280515090b0306090300b82d925a174402d000c060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 635261798 1250 635260548 635260559
    0xf0e01150f14090a26010b010905010e041401030605061005041a07140105091b0a0e04032007030b07030e06070c031808030f0901180b070204020328060602010b03070e180a020a 77
    0x542c3d400304c803a400000c5d4000c8020010495081c1c40f400c0000a000850700754041005500504a050707a43c900244040703a401001598000c030150245e00580b08035841c0d00c2401102e081009903140c00c0d8001d894010700d81400c04070300c1c00d41481d80e8540710700103a2001805805001d80c131408401c0005042c002030180b030a0070b0300c003590340d01c14400e09501342d03100740032500102e4501807200b84e04030307922008865402c0e51a40c0382550544411056489040c2e0541c500d844e83d1101880360802961045004481604100c1002000ca4130145104003a0f42e005c1c4051048683d00640e01c004040e40c5890071a12940c102e140401151495a100094602c804101085032524080180c88904400c2ea41c69a05049140d00380c10301a24501c624440c44508102800141c20f09400441d8002c11050281404400020207030351000c00c1c0d2000600034566815050021580c2030040b880d484404030000e18041d41001902545402c1c040c0c00851100c0d0781d4203c1c03801d200400d00071901030341d0300103192032280c0da601d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 635263048 1250 635261798 635261819
    0x1801120827100207030b060405070201060803040b0d0b0f0904140c0d240b06030112030e060406030e07060212091311070302070806010614040b0d060506040f0e01150f14090a 76
    0x1600c403485850444944110742d840014564100d9800500c11842d9840c0c440c103120003050041c10b170404654a8dc00e000c100c500b41040140b008050301d941d03c030364601c0c2510030754040b602141c0c00b140c803c25054000c0c0038a551000042900a50012841c1c800d142020703070001c1c07401403828801ca4021061031040e00c28030201d0190071048a05410a1081292000c2025000c444a10311484d5001c0d100740300501105d0b1a01da81514818802c0c01c003842582c14190001750b96410541c0b04c500065150b007280540802d00340020002482e040c002003c0c2e11047d8099608603000b141107060240380c20603401c1c070340d01045801044010100c0c2c120580c0e10081401c6c000c3d1a0405802000301501c940d0000060300352055003103075140c410842d101400c1038100340c4c00507460390040420280654481030b0100d4143d0341c0340010001840c114018200c2a860a90021046041607001142e240c6622140d69079642c5c00422900c41041249001014608481c0605143c0d0041c2410690020016000071a841440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 635264298 1250 635263048 635263117
    0x6091914030f07052202250210110601090b06040b0307180602070b09010f02010e011a180c0706020c120a05040e0c071a0a09082718011208 61
    0x19402d50310b90aa2040041c0c0e990381c3e841c40f4042d00b00d00500201850030000382130503005840100d001610704100580c0c0e940d56032000c801e05004a81402d8005021071405201d90041c1c01c41c1e600f031807920481c0c101130b4141c84030014440d6030039440d110001020b5641ea004c044501400000c18171035240e0400240c001c0007240c0d000e180c1c05200c606100007040742800040d0050031070319103601c1685000da880c401101e207589901c1c0703420107640d01c035010040a00400e0196502011103601000d10044001082017243c0c1d40101000303441031058070510a420480304120350320550410409680e40b000040702c940741a403103502c8000610300105100b5802c59100c0000c2040b6026411000e03030301e17103072692504000d203d00b81c002402045401d5154054080703840c0d90316400013030b4100010f03070110365449508855101341b00034505442005030201c0324106201042d46200340079214121000500c0800d4103d440d010b00404035009110924002000140700444048003180910031180c02032201000099204 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 635265548 1250 635264298 635264339
    0x3140c04050a0f080d0c060b311503060c0203070b0c0909010e010602031207020106150801030b090303040515190204080f0708010c120e0703080f0c07081605060919 72
    0x1070b42c920004028030002d0108041e501c0700000380c2039452483c141030702d248200c44412a4001e0320354404038615aa4240030f511851495484108108041c1104000700c0d21480d80890001c0d250103440c44241c4041c8040d0002e580d0310480c00034010070769000580c81c50086100091a01d4418001c1100002591000c0c1c00d07030500990b14140d40343d032140c0c501030050380d090180a00691085c0318100c800300300c03c01c1803500103a55000020301680c42d0070321410704440708000c10001c2001c0c40010810010004001540101031034081d60841c10180d0300e403922001e00031555200b07581da490100e00f2500b4403602c5069130b07000441046550790307959000c450312501d0744541002180940840062540418047c2080c0d1484513034840c21881c0780c08013203200501100b21210b86520500c1000710000744070600070544072a96032400c0b42c4038a0000d040c1480d0454540200349150010401d2401c003071041c094a10584000300d03038240e00c0c0c0e220000440d114100c4682111002c100111f40010003504c0c040010300c075440f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 635266798 1250 635265548 635265559
    0x31305070e040f0816060c0201090c1d0601050711062704090201121107020d0b06120c1f050c2b03110a030b0d050d0e090106082503140c0405 62
    0x50340d55079540704191040358080d0020000394200400210700c50001e01c0d02e60315a210108524410780c41d2402110482508440580c0d0b440c403654040c000c8036109140203040c2d03d84000c00c03001144000d0000303503501902240c144040400c2e42010080c0380f404803a08908080c21080d00c1d021650a54124a0700003181c41103900191407500b000b03030a003400f41071110364042e151340c0100706446481200406080ca84031080c3c0302c045c8035000050f55003101c500003440c041d01c88032420741804410440c0a48520310f400c2500d6004080c00805502d4408007030000d26000c140904822081107015102d61043d40076410080c0154404940e084120103000441300c00c151012000021140e48150120f440c11824242d0307104080c040000c00320700c82e40107004146405400c45085044641d18a8902001c5030464000700d4100c84d002c0240c0c0c00c14081160042c512840d0a045900780700189800d2185148540115036000e400c04405050094000c1c0105030706054001995140100c000c0b9265005400343c03070300c9135 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 635268048 1250 635266798 635266813
    0x70813171e061005010e030f072d12030c063308010c0e1c0f0b061f050a030b011b050f010b0105040305030d090c17030306180106020a03081b031305 65
    0x4400040b80c81c850480c401410b40d20b1818400152840401043c01551511500c044444010000d101c2c81008010117006041c1d0b05001d0109d0540b266424252881e2030a001841044189980b5840402c4a905400c0002c0c0c600d01c6420004054500c10820004614544410442c980c401603000802c41005002c69042d4a4403410a6401e860341c03240c0080c0021038080c42c0201600d005003115031440c1c6c0c0702468101c0881555104182c1981e559010f8a12141c41d038100807245c01e00594a400300701c490f07058100103401c1218080c00e0b03400b501010000f05680c4000c860401d03401001c5034503803024a5882d0030002490342c03520030380e03030100024131040769424141002d0265000340c0a48013980d60100c00384d0704145c00c4600d075800925251030281c4505c03107400c070001514480808040044200e5030b001d56034030300d0304000b07124003511500424828101d04800402003981d01040b0307020300c50ba01d450700061641702c0f88154242c100d421100c1d5900b522002003440480038100100c15440e40c40707082581c105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 635269298 1250 635268048 635268103
    0x1031103010b0d0b06032a0a050f0a09112203030305010609050a0b0a02151311180106050c0c130c18080c101e0e030f0d0807050f0c0708030405130204030807081317 72
    0x9041807d5052f9007200d0b0f14041880013102c41d401207040d441c85006502d0400054503c01c0c1419001004046000c1009003010303c1403690600139940508014100401d1091420300450323a0f00d4601c1c4143e00b8441c10108010380298401d104501008a00c83c40341e16450410a414540703030100b084003201c010b00131400410040c04c188003045004403406c1c001810983c6420019110755008030012406030107000b840e8841c40d80d5100f84001e02007003c2d600084d450701200e0003d01540c6d80d00c00c0f1000702e03859a01082003409800584c031501a1303421b07940d490070440c03180004c0d0303410305072042e0b242850710611080e080140e074440718009000c02c040b0201d03003600342100c400f56201c0d642180c1490002d524040000c3e0000c3c02807004000641c4101060303460680c00d004c5031030070090203030000b00564000013401c01a518158076485c1e080a0b060a003185800d1450395a6101c52090040c01004010007080d4164400314181c0d00e20024220942504074a0654103065501e030451000140c000d0b81c46100e01c02c20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 635270548 1250 635269298 635269309
    0x80106080f03092803060203070807030e0a1205160b040203370f020315070201050a1103160912080a0311030f0402191d01031103010b0d0b06032a0a05 66
    0x451200c0030000d14907000d002c0c000c2c030140402c3c10b04c0090380600401180b0004001c4480c03410300441c003580005849003400d6600814805000d0204801c040c1000540c500350400890084000c81c0c1c41040345c2c0401c0e039102e6040d20b45001d0004095030760709801d0b020000b84100200c2e03151003070748200c041d56192a070744101c01c6490070300081804c04070010b8111030740315041e440600d0040c00740a0720400c544032060703900292808500220030148107241c4006c0c00314450b02401201e8001c3c00846c828030490220b401e52806a00004240031000000341d083c001d1614041d8002030060542c80790400c02203100c0c0d0134080000d078000c80c80040020714062604805145080c103a0b0f0040e501180180c0c0f9a403074075000c0186550703461a1285090001c41d0000408411f6000d51100d45103507a11000c60320361542c00c0c5a5070420004603124003d90500c480248190350710503c03041c00d554040e0f0504000d13103691000c246000800c5102250303d0703242d0000081414184112303144240c8084030440348083e214024404d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 635271798 1250 635270548 635270563
    0x603040f121b080d0b060309250801150315110403030c023c040e0715031509021209010b010e01030b0f0a140306010b19050f0d0903080108010608 64
    0x28030880c241441880011003003a8401407000642c0340034440600001140e803159940e2003402c48100400003400f0481c61414002d904650400315134003811072030a11412030b11049419100400d0310905450310109000382d1b0740801c09009110000c100c6118203c414410103011404140c0700740010400458428034a8003900e803035001e001505c181058695903040d150800c40319000ca9100856400c240284980d20800c4006241c40f1010101c0044030300f0f00d007200310340800d6020390046084c41040d06c0341c504000b900000316460b00e203090300080d01d402c008030000c0008a03401114500c100b54005040c1845030040c0a60b004103e0301c0d1009500e88090280c00c0300c038441c004501042c13148450081941c00b039400119446070250003200c0c40d90305400081c911544035000749070307410503c042840d440e0408000550151014030001c1c5d10305000141d140b060343d814005040c0812400040d400d60f403092100039103840c080300040038030201d841441d025008843c01d000702e62030b943c40c101001850740b4002503050b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 635273048 1250 635271798 635271803
    0x601020703152306131118210d0f02010b10260a0c0809060403140304080c06070e0f010309020114090a210b070804020907031d010603150b060304 64
    0x144a42031555480c10080c0d440d01e01d1420615545100c0031100c3d034a0b01c0c140780c4803041099072641ea1403410704200001c8020130703450144031500c1c0c40c0048014186c0c45003142c3e145080961145c1c05d1414080c0058030b640c007200c004002131107840007544140100052042000300e41929018001440d08038101c2c00c07611481d080f9940611390942c403910907401600c50f50108032520184050410099201c0100d00000307407100c01701c05a4905480d41c4080d40300c840d0540142001001e00b48904050300c00502401c6070400c0c4044c07904000021804000050086414840d103e00aa40b40b61500d4400036164000f401500e50050300c0c03505100320950702c280306a0f02d107503038140c4403401035101d00d84450313400340c2024101b0b6030055000c1201250061614400c904002c2c0500103055184080d89400300c0c600802400810500c0607590070301c0010782c1c031900d580d0b80c048a1458002189685111002a1088100c01c4c100b040c2d46018404024000460141c1e001c207a114102401012105410302c0742921003210003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 635274298 1250 635273048 635273053
    0xa06050a050a0e13060605092404030308071704051b03010e100222080307030e10050307030f09020a0f08070e0115050c070902030114040b030c031f1410031703060102 73
    0x1110800c1c02003c0c809400c100251240320b519010400c0704c012034505402c96408100c001c1a1014a45890400c6a44601d0740c01030b81c4131010341c0884c001e0b583e80298000142404012000203e01510542d241c207100600000d80d0b280505160800c03c1d12040c4d09c020102c51540070807a41d00f401d0805004203140300d039180300108a030000d04415000250801551401000203280348580000b0140c0c3c040b4015080d48009155291950301e80a4610201400b03040d018080410300148100d42010699501c100c00d401c01040c003440b4501444010f01486d440294845043d00000c5841c2c3d0303181d41c0f0328050b2000f00341225038180c1c850142070181c0b0024072501c0008400070011005540c0304002034000c40b0702c103030200c40c84151603414444c1030340c000340c2000c0c50242242164003000c2c136060003058108541600500340000710400842d4450064805042c02641d151610406902c0a03921443c0d80780c042c410703c564a41014502514900082d00c000d50f81d404000810340c41c5804000212400303520140c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 635275548 1250 635274298 635274307
    0xf090b0403020f0c092202060307050a270501050306063c12150604090606030506040b10080601080c1606020702010e01140a08192412030509060d061d04020a06050a05 73
    0xc1b2040b04803650b03031803003070a01c48410401d0016107460f400b0f14022411900c1d4580c5a89084100421881c20982454045075404c08558840e840f040c4040058420a1a200d5035036034902c004900603100d140110400c1c40c0360165944004803024902030f41c004405044200c11074012203a0342010f001d843ca002120a9409010503884500030b401c0d81d8a01c5009801281803546d140c014504030341c00341d8011004661500d0400907035203040c2c802c28180c0d410031140c495070f080013114010401c19008011505010010000c0f4002c540d00300c00361100c0c15000e901e88070303401ca800c0c50540c01a400003d030803030120702c080c0301e400c506602460307070294160340c3d00030550305022240000b00d81d07001001e00241c0da480514121042c280c0018002d290490742030021596501841c0728141c00e50307140551004181075920458880041c4d404002c544444808942c880e41700c00010700000001d11882c1c0c40865108039040410512059100c1d6651169000b00c034040c41301583c1e2401900c10303101d04882100003980401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 635276798 1250 635275548 635275561
    0x405060412051203010e040309150503060d05030d020a02070311060c1b04090b01060e1906051e09030a0f0b060907080402190506040b0d05060d02011e030f090b0403020f0c09 76
    0x100d040301e414000c03000c0301c5000c0c2d43c3c00351030165580300380c0020001e071441000b00824180c2001c5031100520164418010024800038000c0660102411191045403201505011702c81c0c1042038410899450304115550448024040d42e04c01d417501c41101c01000c82e1041e2015072418005072110346096a0151403040d1240c6042501000c090742e0a0354403559400c03030400070511401c1e13900e020304666214010600040c03c10417088842da07140c40041c6034400706050003015032090541d404160980c03e50716140030b00e0000348000f4065041280d40501c9000901414000c0110324154014058000c00400b52103003814000e09080445034680860f0b501c034007080040c249428410501e5110aa14504050725400060700541c8240c0c0100000100840c0b5811898800d114442d0400c50841e85d00010711425800680720341c1000752010708020403408000c2169000c1c0c1c000100a14494000b04141070170f6181c001c84003a800d440a5005110386c0b0442c50342900009004051044001c220600c0c994420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 635278048 1250 635276798 635276819
    0x90913030207031205040b1819050312130e091f02030f040212010b03010e0d17221b08030d0c030b0f0907050903060408090405070801060503190207080c0a060c030204050604 76
    0x303403151341001010000081d40525081c007800341c24071580f0324082d40030340540c20040380c1d0000040c00342c48542d40c44000c00140d0385c0003030543c02c1c00c00c000600c561540940c03c5076142c000e40d9588150301c00c610b160100300c521391700480d40010181d01e040c01d403d07540740743c4212201240012200049040390b03441c081005803900d0840d40985030403450010070303e4080070340801c2c00c2d64114410a050b980c0003030955905950004018007001035101c0c4000c4151404034128201449080d50000b2402c0c802e40f031000038030500210010380304104c00721a051080c0e5440c3c0082d0f8075400000c0c0e1041343c40c604159414140e00c24003500124050043c040540780b6104800c10911801c081c1421040c00030401026405032400d0204500c034034040c01d0001c0d25850108140405d8600003440390302040082401408015040002c3d00d41281d0301d650348800000010b00084020311503070002401c101c0011624070304451000822000140c0f0488043c404504000000e5059000f940116680040184000d1001d00c850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 635279298 1250 635278048 635278073
    0x2191d0709091d031c0e03090d060b01020319230313021207050d0305030109050604112515050a0b04020c1009020a0b04030807060e1b09060d06060b09091303020703 72
    0xf10055803a0210b60903038a01c2c6141d0002c04190013401c0c80c2c2d00010140029803140e40c1e00513000c1406140b4105080000907032034400b40e81d0040031603a940c0900c00059208100b03807a0440004400c010720200600d4001d05002c109090100c0c0c428190181007a4160b40c42041d00c1c01005448490780500c5001ea0800401d024100390300c100c584595140042c881e520580b0804445000b0f440d0f1560740e5044c4514941074800061015010b64200000c00c0301124810003100c210703c0e40809110011481050500303034503100c101001d80340e0041c2c8401e4400c00444d540c0a41d0080000c90320411007015400240002d0b806148002a41c0303400009000d1844c030f00036040b2008440c40200004451903d4030400b03611500310740c0081d01e50401c040b8052007007100601c20340e00841111300c014803040c81034102041e000c0e480c11110502800201c000b2900340e07202c0d45501c000495101405025040e150f9100f1281c42d040000c06a10920308003003c01d04083d0300c0c4003252086505070b0701030000d880c2151124542c1045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 635280548 1250 635279298 635279321
    0xf0f0712030507021318021201050f0106050f120f090c040608100e1c030902090c04050901050f040207060504120e0913080a0c0c06081902030f070806030a02191d070909 74
    0x203200e0721581c508250711507110301503451b01c01400f1065450042c04000498103034900b400da07140906100d0071070050400a411504e00c3d1806031f6030f8001c10340c0c8601c40b60046007074590003141e5420501101c01e2300724641d2b6100302e180c4d004403020f0b51031900801044e6103e92003800f403140c01c04070f6a4030442d00c65400c00750144030304030115441c0c0c00034402a030300d5050040ea58140001da90b01c11200031403421000560f0013070746131300d0054140750a0030001000c415061080600c558802001c50703003607858940680319400c0e0130500c02c01c414646400d0442400c101010078000203181704031403030074500c6c0c417a00039402281d4204030a00040000e6890100c0382e4804a10791091040801e500380c005001000c152011385120740c0d81c0d0f0500e080c0581c00d40900b103071041c0004065401841008080e00c0f070001c0b416402115803624001c59154a80440e081103050500031f9001010900e0010b41580341c252031b10111003503000c2910050844841801c0c9120058601034000343c50305000b0002c1481c2c0d83c20541300d065 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 635281798 1250 635280548 635280559
    0x40b180c040807032a0e15011b0b10051c0b0402180c0406020706030b030a021e12150106020307081603090f150207080f150a09050106080f0f071203050702 68
    0xd0321040e00914000c0300e1350045680c0e0240f00081400d514101c2403810010502900058085050849a1a520000810500707182500f13800c00002d42c1e202e0101c070860186180404011002241851034024030b044801007080089010006500c3c05e052101000001c461401021000540d03a07560310b10f1140600260303401402c0190020b9800007880307046006100401350107036035038600350010b41400d0869200405240c0f6040810f29140c4010a40e00103aa80c1154520040103249281d01d140c520707030501580c1c02920840c0841012000040c0070003554450002d501c050741c1c1c1c0c42c0b204a1f900d11421500030080c440922a42c0c5026103801c250038881446400c01c41440c0da00c0321110052902c1d1603000341480001150101a0039405002c0c0e42c018051490241c080300444010a580c0c2d06c81019010010705059070000d40c6030300d03080d0b01000b40b256209009005c0036a07210902940c0b90b001618044d0140610010352000d10070008100d02103a0000d9180c3d03513040c0107070703c040d1143c2d003028000ba60040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 635283048 1250 635281798 635281807
    0x90f090204061d09010b0a090903090b040f080606060a0912030c1b0501030e1c0f020304050a0b09011709100b0117090706020d0306030804050402031902030108011a040b180c 76
    0x1a5181d000d032602401c68030600c0f41e020104603a040302c000707401808220069142142201c9152940303070290058890084020950b95424541103070080c2242d44042c070b2001006ca001302c2d000400400602c2107038a204222607290326800c04011051154844580c040342c5007a4040002072400e400742501503010741402a0818940d48a500c201300800d6414602c0e60300c03495080c001c2c0d680511490a8410203d070040c004010b035005401070480b4107078409401d201044090002ca14820800c4a0241001810300452650313502d0305050541c000e90540342c041415500080f01175045244140d1080983c10000c143c4084c4400c07801000f8400c0098450411420280c0280d0094451203400d020f02c8407840246400392070080000e0401801445560130141403e1040000c00c441074161400d44008640040c0e036501e418101070041d4480f501318000880c00800001050306066005142100b18880c0c0082c10b004030300d042104586400d2000d642c4020128407070b14400107007a0070b5540c030010594816150 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 635284298 1250 635283048 635283053
    0xf09030516030209092d0a1b06030b0d030504090b060d1811010e13180219091a130519111c0e0a03050a090e090a0c14030304090f09 58
    0x2090304410180400c00307400182001181865120f140d4007003030780c0b001780a80030354a507001211018100d121106180d0200074140c03004c10284200404507500c60180000c41d10a00141e0f944516288103040c007080ca4408610350701d0400c1501c500c102d95155580c2c91034981000304c000c00400c4481d420a801c28814403940303510300024850401c400300040311100b16122249800030800004010300303410001c100f091078a264403041c2d030b801110380d03290501003140300845441c1514a80080ca000e940002800304403491101e070300c200581600c081d94410302c18160324800d0215070301d12030640143c02000d4180c400724050301035070200340c202502c15000e41c01c0d809508850025039500201d141650040041c02c1d400303200884602e00010105500b0510010200782e601603141c0106803c0030f0144280052907880d503900c07414108014200703080500e000f5003403c840c0e656850007550401c03100809076034004501e004001c525000c0b075030300084c000c41c43c0605004041c0050304120703155030642d540302c0000000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 635285548 1250 635284298 635284303
    0x308030417040902030903190203040b180409050d180e01030b010312020c0310060f0f08060f040501090b0a0b1206040c0513090206030f060a0f030809100c0f050c030f03040b0a0f090305 81
    0x34082c1b82d002541c545079100140b0b4a20001c4407441720965004120412003040d464050701c051108401480e10010300c884e010034081c0c640c524000301503024003d00c40c0049134000200508100ba5601460100e9455000744070005c40d0038040030b0042c0e0481801000001c440300950a08101c1c0b510503161300c410791030042807400d0900a15000100e03140c1c1030510440d10800c03503103001040e4141a00c00c9140c50000b145441d5800900705284201c0c20000003401d009094105000c0c44da07112610340c05920349030b03c1440c02029009a054030444d03002613000b14125000842c64003480c3c2004800704400d04d000100300303007904512110001c3d90744400c803084c0035030740d03031009036102c0d940c0358025110600d440350400484400940100701c024525803410b2000c40d240900380c5102807400e440110803140100001c0e280301050fa0001024100c00301c0040042003004641c42c50301d10b005900b1148840380d000c801f15101c0c05039000d034407126003040c8280000d0710312071541c03192000d0007404e021036036035183d407502070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 635286798 1250 635285548 635285551
    0x140a110604031d010e1e030a0c0906090b04020327071701020d05010510020c0609010e0d032307020f090402040914010207050d0309032c210f07030803041704090203 72
    0x1c01040603200c07400f40300364524011103404031092a281d40540c0b0300c4070000b04075840c1000c2201e608100501c07807943c039440030011524003641100c16002c0507542c900090018002c0c1c0e0041d400020b060000514030340c103240c020340f4001c800250f002e22500d091034841000c64a0f60f80c07004400c0d0f01c41d030b68001030403c0004150038040c0040d5400940d58012050354903060321010f03070140c6c3c01403c0c0c051540c40c600b80d01040942c9184030848140e0758810b40c0030300480d058420f0030041a4483c201a03485010140c01c054080c6a0545000401505c41c0c004101c40c9140e025004000c0d400c4190403000c01c00c18a019400350358071520041002461074401d440c3c0d0301c10900b000e00d0005140e9400520071050100800c60400340114925050150341100d6030002c2209000d52070300c08070449102c0c4102070100e840d1140485502c4054544800701703640404800180c00b50202c669580e0040d080b41142c001400705034034003507a0700404450701d192640d40d02d034260104031141224400505101c007080e016810b00095 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 635288048 1250 635286798 635286803
    0x9021e060f300106231902030c0105060108150906152d18060c0a020330071a0a0212070f022e0b010e060a1107090c140a110604 56
    0x812006030501c480801c00300b003942811000c0e03044500108556907200a400000c142c0d00298440e0500605104540500400c1104122241002d500030f10361540040905030100d045030003803185881e00c5d0010f451154058503008010503141d0240c6081d420f22030070f000d80101002d041c000c40c105038100d10303050540181e810b0180c0620410501642040c8005e40b43c1c3c01041c40e0400e80e071508148101c1100c07003807900ca81070b03401703070300b0105040d102e0400c14400d94481980140c10341d00302800101c00d8400042c0044100300d5108190f520b2002084001f01c00d9820720781d40076440d00d00300b4051141910302888002c000800c110f03001c124400440f03002c65945401200144c6600200c0c5118060103410110b00081c1c4908140c0d0003c10100d46030700b41c0800c00138410f41204002152019080121500c0719107458442d00114001881984103034800b43c0498131004034015900328940350344c0744600f55204c4016520004000c91904403890b519600280310b241460f003040c14038040d20280c2107003098001c071002d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 635289298 1250 635288048 635288077
    0x30b0f0a0f0614090108060d0813030c090c030b0310110f04030309050f030f06150102150c0405040b010c12081509150301050112030206160908031b1009021e060f 71
    0x20080150070070900f04003100d1140003941818001d50000348891001050144500015040701c1c00340040c8000320344840d0040c40b02005400d8607400c1040080e031062085010403441c102141c142544680b00d0941c2c2804010003410507080d0145e0b200c0003070084503506004c0300504000241407402d18500170310085100ba1502d10041d0306e4841000003400c009034016000e81c008680500608801103100c81e48500d6020f010b020603c00d0000407440c00ca08455010b81462050080c854070180c02c0b03020342304503801201c0c1880313004a208011241e0312a1a003000b0204c0703900c1c81c1e108024600170498507a000201e014003941d08003174500040e00c105026136900e54884e4401590441c80d09081c01514050004440440041800e41d60002d5869000410710107000024007001c81d100d0b446142d00b40700070012241103c0c0c4801808103c0c4140d41c4490b4860400c1d845110b88400086540340688000590000c18400941007900e1002c0d1503280c1480e02d044d4415410800701c085141c4100c00350a103600f0b00c590 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 635290548 1250 635289298 635289329
    0x140415051309090606270f0e030d09020f010c05030a031a0607030e0a080106060207030605041509080307030e0c0108071d1c05010e010612140c0a0329040c0501030b0f0a 74
    0x10144c080751503030741261301c0c18a14540c0310008040300c002c0c039200c524501c440000342c8040c2d08190b00c6c01081000a02038203800300252540d52891503400580c1c03202d0084824403074054180c4015219210f41600041c40da0700284079051440340a540b29a0002da0b0b4920184040d00305900012110b40c42040e0460204100c054440780030308244003000040d18102008100b40c50820354080c1d602c00d010311008041c17070784031000071303003040318400c0d155004d0600c020041c40364803217a1a0000b41608222004400249458010b11580324006400c4150070030603103c010b5a9196190304580c035501c400e050500914041c842e400c81c036150500700551030b8070036400c3c1c0c01c00303041c103850000d0944049441c035280c0b45c0c0c188038060118031a02281d030310446600006503001601c0024500b8140078450481682c4904889800420300514100e4807601c1900c100385204610380d02116080b10030000e480103040c040c5051418017195020307a000742c1c0758513001000c6088152a10002402100f4540c0000013514803184 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 635291798 1250 635290548 635290553
    0x13080d020c0613081e040506030702030c1002091c030c14071a0c0312040f050f060609130308010302240d0609050108060f040b07030212040b040506010614041505130909 74
    0x69107411543c525200441900301d900c030002e0030f000c0c81d07209140214042c960782d8841d40c0d141040390300501000e00b41c1a200d03d041c6801940701c3d000080500072a002c8d039103542c4c03c03002c541d00c21108409002030020386480c0690a181e4010315140034100d05014002c0000b0001c10800c8516002c060118002810b03c0703800d04801203603212107103d031182202818030808200c00c0c03004c01030343c4001001102c0d4a81c103541d141488025204a518090140c0c00752481c1e002c071000c00850f10750304c500d1017a2480749103600c99021300113040c2c081010240019103001c0062005182c6080e0000d09e80c2101c2c016240c0c5805110083c520300d5001c8400c9114403551003108000c408101d004981c010003030030000d1720891074100e62007500301c41c00038001022100c2e400002000c460295054440c1c00c1781969241c0c01528107450705c50748111041d0340a541e03902c0741c2c3d0000500644500000004500001111400c080c5400301c004808416144c03c03174103104050085840c03010f9810a09002058030741030201e0071a000c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 635293048 1250 635291798 635291803
    0x90201030e0a060501151133010e04110619030504020a05101e11030a03020a02210c06090106060509010e030c03240705030412050a122313030207060813080d020c 71
    0x507803032001d0101c610f07034004c1d5100000c1024500103231014010420625003180c03408000450079540d030081200340c030010450005103250244210f210351044c04646002d1030402125018901c0c210300d200107108820060315110744c01140d00184094900d0f0242621140000d8619010103007550002c2ea04032254149007000707a15031528100c941c104040701765096102240c5921441d0300340781c00d01d9000240814403034420000c4100c0084540480b0081009002d2556a66481500219102c0c8500004aa81501c0600c22030045500984615146c125504019130300d00045012042d49030084084048060310144621050940212040d88201209810741da15002c0090010010068180304000004440c986e00c0d046a10650030203940301d03072044900b10b46200c03101c0300200416040122203107060340008245684400e0920b41d4503c10340d01c405141100b40d00c407040241c01030b400712a0800c9420301a42c140d940050344412807294400032601c41201c0d540c80000f18000719540022a4049680b06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 635294298 1250 635293048 635293079
    0x120a03020c04020306030a0221060c0a030c110618010608060a0507020f0d08340302090a06140702102c010801140102150a020d331206090201030e0a060501 68
    0x2c45086045050a4000c0b0f0303030350141440c009020740c4e02801180d84699100c1c2411170031142c074004540c040d113001c01e000405600840d443c8004070b8104120030103d0341c0107100307030040c0c0454840149250b6070fa4803c1d8070302c814000d036147c0e5100e541c2d850010070002c1c800d114440c402c003046c10000c1050700381140000d1030404030310744200319904100241d4140b1644620310301d801c5424990f501c801c014800383d949800c2a199200c84141e81c003810b03070060110350184c01801c1507003002c60b49100c4042c4d8401055813503440c14100001a640304200a8005241910407036a02c280f0501d403400c81d5007212501c0031600e0712603904101c1e11a141ea05114069a48100e50768094202c0200701c0c1d04c800c09140000c0c0d5691141c070440c1e00d03801049000500d84d801144d041e03c01c1010071080900036080c0709240e0110040c0b02d16030118010400c0a008070003d6803000c01c0604031407000c81405190140ba072031b00401012040c00481c10503440d0262450007203c2081000080d50140400141e40c2d4941850804003100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 635295548 1250 635294298 635294323
    0x3050304051f05040302010f0912050d03061508010b070c0f0b0301080d030207020906120c030703030801091803231303210315030f08040830040302100c11120a0302 72
    0x34003100890b119640282030302c04480c2c0c2030030514a40c40b64240300743d5810b06290080c15490070244080010f100300017401100000720391b10b081202648400961100c070104a0b060030100309010010005884902d00605030b5134020b041c1e2524450301c84080500d800e81c1980242d000714400710051100a8040c007011100380d200e030134114601883e42c1d012640c0c01d08028079aa02ca10b403004c1d5049400c002c20702503900d03aa8001000c0e100896101d103406890084280180d800d403a2504100711800e45c210b030310000c0c0c860b805441c0c03418038041c0c4440a14584003e034404001c503400a0000c480c4c07071501405c0100166104000341144401c905240120307680003504120201800c0c580340b41c1a41c0c59150405043c0c98116011101ca580f550404c00b140348901d074020102c03442100c600d201c0388503039100a294014140c40705450f000714010004100c502079800047d600c11031042078400898081d2801290481c4035826a0341e01031640000140c01074295000d03850f403600441500340c2055414000d4800801e03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 635296798 1250 635295548 635295589
    0x303091203040c060806030a020a06030213120822050a060518010206010609051905130b09011707090f1503110f091006140c030304030201140601080405150c07020402040305030405 79
    0x70b41503e071001180707000e201d0304082c0951440801c085840910644000d43e030090100000c00c5c0d5500c800034000e50012400342121040d800b404a176a003043c9810740401903320018030706007088211800d5a442d600c2482d510450162680046d09459010100f0010403040c0c40b0701d0380340c031105410300e045a258000c41c13604640108005101c000d0b001915001611000d4840000e07800216145910103180da801c105d0307208550700558003c10400760440d4902c0c2c0020740b50b001259aa411040f04c0ca50b0360101080e01d55040300d90305000306110703680169442e4200401c0800c20701001c00e500382000455400560300030340600d054800c00d08100ca00c03900800401d4501e12036a1800088602c4100c1c0903000ba681003040d00f420035084c01020780b00343c0e949084044141e03550781c101450080d009002003040042e4801090001a543d5806140f10620841d00100036004403201250300245030f170300c000d00f20301e5081c00034490000540c555101074006144280e000b180d0f40c0b82440100900c445501001e0890301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 635298048 1250 635296798 635296801
    0x5030906160504030204020304080d0b15030c070c1214010e0309150304080f1209070608040807020118090c1d030a0206120411100201020702010314130f0609050d020303091203 77
    0x5040091126800100700c0400000e108020320101c2d8584190b0384081e6105001100740f03c06d01c41034400801c1103243d8440c1c204620242001170100850009200d02011101800040c0030794100f0801003e100d0301c95404003400c15100c0807140e095908066059400c40460b200c03000e0390140034402c1e040313034113900b00081d828245200c0000c0d107485507085110311902ca000c008a4100b1070340d502556590060307418100e0f10fa1015440c0502c02841c102d4a05240707108400c000500ca0b4010300441e401240c006e442d4a18004407600150b8240e802c1c001900380d0424015400280c008092003901c4c641000381c2c2d01e000c0a03884100c90040b0580260a080e8801e030031003400780005984200450f4100138507010f9004144e82c80e4101081112040f441180c0c100003d4200c112140703606600808100781f00762420000404c040c9185a0000411601e1030a24181e0000c00400b260701c040796036100710300c1024041904006559482d040c09020144103015034004000d001c0c155809114240c0c108200c0302880342503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 635299298 1250 635298048 635298061
    0xe09010f0506090409060f020417100605010c02060901140d02120c03070225081504050d1806050c101508060f0702030d0b06090a03051b04090b0c0901050c0d020307060c0503 76
    0x5910952507403034411545d54540c001000183e400440d0505000c03c1d003191156942e201c440c82c036900c039121900c0140204c52104001540b5441807100342e0384181e540046103030066003407280c40d07030108414038103221ba00c101c642075030031f00c0b10024101c094101d000541c54509006100314a101c0103800202c110806100f041075180e400a8203060710004401012002d620022465202c000d158011100502a00c45020300b074030071b0203950502481c41801151001c0034076100c1141c180d9031080b81c1e000c8a401300401001103a20904c080d04c400041182621500001e050741c65048651903114a081c2c020070340c83c10424640e0034404076030300201c00c2803011214a07100500944911500e620b0b2503d09a80d0312503a401510390300d042e1400110040c01c400703803083c1c8a00707003039070b9441803050035480d55901e00c1411007044c20180554410f0951282d00074585849200c00c841d1541c21a965039410441c01f4091900e111100704006880704005401840d80e030b82c0700781000030a5130700d051a040148802003081c00b16 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 635300548 1250 635299298 635299309
    0x102090307180b0a1d04030c1403340803100b0705060105030c031903140702030105040c080115060504030b0a0b0904211b020909072607140d060209030705040207030e09010f05 77
    0xe152001850543e183d5910300c1d090764000e00c8c024024101c40e1070804000d0901d03030000000d1101c9001d803103210002d00c4031200c107000078802090071308070b642d00e03039100050000381004040d50708003044034040880c2648400d14030280390410002500ea1340d028100401660906000c1c904402384142c0c060070551001d024000e0040642c180014204003152200440c1c4018000c1901e40240d4000e009012500701800c1074030301d9070561700070012154a40808090505030030015101242c0e42c0791501c85c241841c64680908141c001802084841c4d1502c001066507501c003e01e20f4030a900c2400d41015200d52800b8150680d081101e00740140b0540c0da107004080124510015907180e41219010a50b980340e83e8583d09040c00c3da4404041605041d0841e0034101003140218000c11044044408299072440301500303c000700089140c1000300c10340710b5004034049400504c9550b501070222103005076950042022680014401c1d800a12080c0c40c40035645000003401d401030000010b0000c6c02400e1900142 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 635301798 1250 635300548 635300579
    0x9211101020c1e18160905101d0607021c0b0114091302040b040606030603050609030f0301290307081e04080d241202280504020c0102090307180b0a 65
    0x30074111414502c0040d52282100c03903410f1038405483c0c138a81022180d00141145031411300c40443d03452000403480e070400e020307200d41e241e190790790342031900420b010451a000e040c19015604103100b0000341015803191558106028124031400c00845490300701100b050380181c00002403400d9283d00c8004a40e1840199a005181914401610032151000078010404c445100f5086418800000f455940580c00700045034014001c4c0e0f4010b035640c4038902e4503841100e80300c0e000d1110610051110b914641e4400c60003080006401001114500348018560412200c1d280014103100400101640303103c14180140515501c00485e42029941d0050500601c1c6540140d240d9641d50b020640410036900c04000c2d02002d032034020f558503065440c000010003803040e4001e10048041c80441510111a05c159107100d2401e04c1c00c4906200801000c0c0d84100b001c0d0a41750f4003444000714039501845204000c095807031001c0c3c54050b0700c444850580d5003002136030717200311681401044070030780c0d00980c034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 635303048 1250 635301798 635301829
    0xa0614120307060f020306040b010e030d0e120615011412070e01121415030303040308010b130b0d0b010306060201020f0d02070f0c0806070306140303091009211101020c 74
    0x4803511200c0860291035400740c6240a051942000704209030b02100d6801140030f04010364060212407014401942c1c004d140c40b81d920703055408030b071400d00d25620950480d8030718000144211a80510755850764075001c81a50aa6520201d240d03100d000c542c0c000411030b14400e07201c003c15080c49555030040c00301c0c02c0000c10039000d001002c20054066846668404240c2044000800416103504042d00594408684682c0c03607850242012041f46400400e407417142e50305035500b2641d682400c0029080b90040d540e4600d0030301c0c0c090780c041400480c00018010b6070700c0e107110014000c850a00014280c2d040b0350b2042c815648104801d8003200c1c4004100c0d0003000fa40c200260b5201d100340781c40d04003640c03843c40c003600c0c0503002c034004100090081605801050269014000c2d030340c855040c103200041d061980c0d507243e0700802c181c1a860a10341028030b03e000e900e007080340260b41d445510000da44440042e420001ca8003010420801c900201a482056000c0c8020010501810041044001c0e42c0106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 635304298 1250 635303048 635303059
    0xa0f081e060102030c0d02100605060c0a0312020f0c060f0c04181e0204030c06030b10090303210516110c010f0c060b0402180405160203030606090a0f08060f0a0614 72
    0x1e5859008008031a0318080d00c50848800c48100781000751a41a00c412642a150414000007194a0b041003680d200d0265540a03007800099680c050b030b038250b4034200d851103980c1c0a2007214058000c0c20301918180480001400861904405a04042c1c1d00108842d0040070240710500c115520003900d26407403007203020000780315000c0000e1480d0b0703a40140b2240ba2441d00006020041001c0301514004171340071070700c1c01c2c0b103643c08120412488405440003800018585101000400d100c0c50f541c61082d0400340d01d8950240c44000042d0030b403102125103080f0154148401641141d2000c44440c0c2c0b004640c010304420445840000c0c21741d0540b001010411185000d00020b2000d10341c4070070901000104210f650300c0030645198850309070400c0e81c501c03841c40d00000420550140d030018020948507409980346135a82c0313003000b8558024001d4550455610300c00494001a0141204007500c0740100811040c40c00c00c1e100d81e902c00000740354151550904500700031050310246017100f4803804490 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 635305548 1250 635304298 635304301
    0xe13050f280507090609061806030302060c1b0d0323090c0906120615010905010c15051302030307060b0907090f121713030b01051c0209040314030703020a0f081e 71
    0x301503280070003c1c1c200b040013030b20b810340000e00ca000641c4200126956103020688008012400f40b08884052101802503002100045c0000b441180207100303100840202d10f03a2070000e868054680702c4030080c3c407404207076a032507001c14650000c10030742c00521440343c9080341e5103056400035480d1585840fa250089901d1404681c040d80d402813031070008004101201c0a52400c02003001064010a400750301040c0461004140e0b544154441d401154000000a0450410040280040000400d20030032520001d035880c0041c1d600340b00030880c40303020303040220390320442000b08440410040c10b0385c414820010400c00c8000421502d1074101c60381c0a0842402c01520704003207403088120061081507100000d011581180585000d1080ea4010162031003241c1e26501800034040d00303200e50400c034520100c80c8000510740711883d503034031602c240b40190f41c281104034040e4081e0800d030780d21408280c01003150101181d1026101014810501e07002e40c5c03d007040f2042c140c0c002882014415910716500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 635306798 1250 635305548 635305553
    0xc072619030b0d0f120c050a030e09012c06060c0708030d05060405090a080c0c0a080f01110a021902040b0603070818150f0a0605060310030312090206220e13050f28 72
    0x42c0158545400c035095486020031441d00502c070ad00c2c5001003d01c50b030886400481e410b0b80c2000c41d036904540c0034160364500c0280103c5011030701c20080c10143d1102c402c000c50000541c003440040010003c03100110b445003034040c4c000017030700c5008040710f0065140c0410045803031000900c160b1510781006005544001152450b424280d03110881e82d008104040001000701001813050700001f2444000c01079464200d2002420340701b00038804006a100d0750341c2d500c040c1c0d240b0701001c22031880103000164995070b010110720550012a40440480c0111042101c8907010300c00c1866142d84501c0500007800b11420319068451025008400340c0200b0310000c0e008c184560f2100018007401000305841e40b40c40004c00c0700c94074039400110005648009042d415401501a405996500808031070034014040903a110030204180051416000c0c802d0000d4100c0b03140b0728260090301c00c44145e900020860415500d02980601192901d5205050002c0300c244c021014200490340304100224001050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 635308048 1250 635306798 635306807
    0x1802190503010212040b0a0506211e0a1211060106050c010e121809010b040530010b0108161d0105120c0306010806090c072619030b0d0f12 61
    0x140c00641d059807000613054500d1315400703481c074401d611821002c440f036030340c3c2019031042e0303002924015040040b0903085000c0340c12040f40d190104420300d0480d41058080e4110508072030143c00c0480c07264002d8a0f10805210941c0c004c00d0744a941410180e0002514801c02982c540051250004108001c141c1640003002900140881344040084031041138050f0303016980340d8840094102da52010318006d0005040c00003e45049502c660107041c1468a00428403d200501442030004110071085111405014040400d001c03080503000251110644c8005000d400c000792030302606d540003401e2040c5465212429807003100319541101800b5031801d00584a9011313480b14082c49142c4041002140ca05a034080c610905007644c407258151100c60030702ca500d000130754281061400420503500810b08403d600e150075052070503440d80b046085041d144540d00004400c06169a2000c650f41142d035040c041d105c40c844085400140e408403540d2041002550b0000013030100030040042c080300d9004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 635309298 1250 635308048 635308099
    0xe0a0b0f030c12070f081005030312091608060615121b19080a061a031614030a020309060709080a1b05150c12161130010501091802 58
    0x490b8080320079810306444c09030941142400a800007500c02c0c0c0021400c03028610800c080b9400a00514544800000b22140c2c40c4c00007080c102d4248641551000d4100d81e04003044020050b100c003414031400c00f141002811040c1100132250180c061000d80d0f2180d44c4002c000d13820a401d10801918501c000c02d1009040c0510340401c182c1501284c00d58042981008885118405ca88010002d407515000c030301d0741030000302054002100040c0002450401c58003400501c200060038001020111204032000b10340c0101d4a04a03d25004800e000600030b0400c406500032900c0d0810302826418400140e07030715503001c04003811980c1c1c0009105140d000055141e0050000601103c0c420b01c500040381c009540329120f41780046c45101301c940550070040040d10f00300703072804001d200c0284281d2504100111150509035101060031442134885001c01c240c4030311400b54810144282030341c914041d00316041644100b201500b0f000b01c190301188a90b02c0900f00e207904450200c3d4019020103c621184c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 635310548 1250 635309298 635309317
    0x9070503090a24061203020a1b0e011d0708070f0c150c0c0512072f0301140a0c1404061b05010c0305061309020a141504150e0a0b0f030c 60
    0x2022518003c600c208036407408048080c00c0c02c24044560364000100c03405c1e852110160041e0810034000300041d519a0065101c2039100200c2e9030b2198031010506007104003a8418543c01e444012035403a10080b41d22956070249490a100750700f440e20440c007500c0c1001d005078110070880142c4c0706000300329221101d044103001c0640c003005100014140909081c02c0b0b40029542480784103120501c0c81851811511440c2d4030048941c0da01c43d4607500b000c4840d50445140c00407144007201c20701292824441c001ca20724090408100303508105004800702c90040c416001042140c01c280c5000b0200c2008440031140c180c5480c070740401c0d03803985407140d0040192005046501b0102d485020b03030b5041e0031260158004072050200703500f6a0315500103c0310b01c2100290015450a41042942003070040c507148210b002d040c60510119003101d8084a500a401c0b00845d12054414035079126030241c0000d80c0c1120a498003081c1c6410520180307258050a0154402c81c0c1c000000600106031507403d0350413800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 635311798 1250 635310548 635310563
    0x120c021f081503240702060c031302012003131e1a1305120a0b0106081509040302100603050609010b0d0201050315010917012016061113060c03030e010b09070503090a 73
    0x42c20f10042d1084d4002541c500005120303550216a01e6448001100d00031802001d40b2002024658015550030b903020001d01211160480340c3d00e1031140c14001000c4c040e01911303142c011030f8200340b49403104121496035003945400d440f100f0310880444030fa002e00c101c915026034a4464140e152140c030079a80c2c1c2d40102d908409407101041c1e0508001456143c40d5204040342c0315140c1c0c94440840c0d2625088136000b545541c00c0b410345a081c204a10b005401c07501900c1581da000b080000b11105584681d0b0003220960301101c08c020303900c13000f0b04c18030b6011541140d5a11041d422030700001c01d40c0c00040c0c00394440b81c9460880d0711544e806601504014460309011146200e002d03481580203114180d80c0d01030b401c1c00b81146450001e1a18112807201e5404c8181c801c10f44411740340e0100400c200e0941103050b5908000d654824024003a0000c02440207948000c10881a0324006051303130b140c803ca485060f070501000b0700d8190344507040030340c0c0541e107441c04545a54980a0f018540309441c80068500c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 635313048 1250 635311798 635311843
    0x11161110050307030b0409030905090703110a090f0f1d07020709140f0601081b0a03110d060602070b0301030503070308090c13051608040c060813120c021f081503 71
    0x2990400082c40c81001d1a4504124070180031044c041900c0700804010700040007100140400d1400d20f0400340c20556600d00001c2d82c081c2c40c90b40c40306a07441a9416000310b6005082000310400c00c60700f2001038000a49002900b07480c00d683c41c0086e190700340740714558809820005481500c2000b1800007000d10581c01c0c0704012854144c80c0c5080803d581c40b4482e50700350400074000d540202c40ca10302400c81e240d0048520468041100b6075504400542800c040c0c0fa16883c4002107920700103410001d80c0c00b1230000b441403905002a140040341d612036484a001400100f004c180c2c04016900000c1d01801c00035000d989480340c07030781040070640c1095800108442507400c0c52106a110720b106100100c18814041010901911404021500103040241200c8280442407040c141560441e24026201440e03c400c0e0340d0703080c039400b109410346d40000c0309007402c03800354608001420204194485048030106510380024020007000340074039a640000059000c0c503031410410440c4058904001c00040c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 635314298 1250 635313048 635313079
    0x60f1404020f0d050c030a0506040b0f1c08070b0a051b0a082d012d052b050c0f0609010824030709061706010e1503101b0210111611 58
    0x541d0020f54008420900e8540000c3c0b283c00c09104061807d05c0080c81c4010f048091010400c0400580210b6044d11804037010070006082001a01c40c2d1441400920364515140d906141222801044010100c06550041035642d240340202e82d62201d007454040c4075035486a403421b030341400758154246007820b16004001e4028515141d2410b80300740000400905040001801206032014800032041c050510308110510b80108000d81e0a51064a400011100c40d00c0010484103070810031366960300120042c54440c60b00d1140150428401c1b11041e06104441000800582e40140041500402d41c12624803600e401c103030004001c0c000504031140c01d91038454002c0580311074440d440100407400c0e014502150302040c624183c2d203401100d106a9512103658400081b6101200c40d014052030716000f144120707a000d90107030342200710340c40c0c1d800b4000a0f50003450030040c0b041c000c03220783c80d00040b1424411441304880004040c2b03240c01c0b401400c9814090543d14800160662014141400012 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 635315548 1250 635314298 635314321
    0x2040f080a060f05010617093906030412030f1104230906030a08030c0903100506030c01020703031202070510050709062d0c030c020a0608060301060f1404020f0d05 72
    0x78192159109110841c0b81d10007502c10340d542805081c0c085401c0416821100d0309140c00c096000c181c5504581d2496a490a1f00102d18000124010082d04c40c001c0002051060303811344841640540305140b5510f01515404141c80007140e000080507200c10031501074181c2070700002c68201e1500995542d89070344580c00c0703090040c9081266000c21000c0307507002c410310701540c0c4548140c0c00079000d01140b100e1581c852103d68401003480c038104006101d00812600d04000e402c000d20040e440004590038400704051610031009501e0f070456024078818400a03900021400c0003a142c000090380700d005501e4090b0601058031340e2080c002c0e00d48810065466400750300041103d010fa10f51114090000c8032030601030500000300c0c40e0003000401c419034424490400c1c0d80f0b410b402458070420a0a4590005d4841c5000ba0312003800600640140041c5103000e208140050200300044000c2c40e00d442c542090485880d540380d80315581c041840c003102076051040382c112482140081141d4030f800c03183c01321f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 635316798 1250 635315548 635315563
    0xa0b03070f020304031e0206070b090c010e0909100c05160c0906050a030b0c090a0803030a0b090903090a2c0106210902031b03010f02070f050f0715050d02040f08 71
    0x8000615564404201d14000300c00c8409403a0401c0c01c5144458600071510140c40d01e6500403a0000020041c000214112581160152070302201501c041d00390342000404088003c1c15652080c611102403040480d030000c1d16490710080403402040300c201e040c0301501c241c0100c010802c1c903480202d11807800c00880c0c40300542540c42e000010054507031100b003071150902a9003c000d00110072000030400221004c8094440400002c4c50001e4090715034051f5415a00155200500281c690140c0f1420386081010b05502071042d000460801c95070400094800b2058072400c3e503034282c195840c2c244e52189a24503090107500b40025901542e50301d40061440014812172040c5803400107402100301414040c09024070703002001071144c1c42c88011054001a0315040e0141c1c15961411122014001c60000d8004940113407a4030904800354104941040c500703100c942c005800c41c901c1803040d410700b80f4601940d0046480d080e6210146220134000030310036900000f00c505000c8400080d51100000d400e0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 635318048 1250 635316798 635316811
    0xa1e05161a07020a0b360c09070302190e06190f09090c0f050318010e0109151b051b06040804080d1d010c1a0106030221150913020a0b03 60
    0x207031459540d00c4040ba1210400340c00180698045c40200d0014080010070401d01066000f0762080400503030382050802c80c0e10101c20060760080326420000307180042c032103503000f12681019407a146000c01c1200014030a184500c040c0010a0b9240340240c880000381d51502c103049818119014104001400c0102d650707072620001490814049030251050190303100d01201e40d102d07000c088040007802d0325a40c20043c030b403400210f00d418001c0140c0a09000d08980c030b1a01100000c1c100d452402c0641c0f96285d01c201c0244502d081612014605040c0103010080041510300035403104042002150520142c0404448500c1914140001d0045000007001119462340448071914144802912101003510312070304503049122070f01c186940242c440c403502900c90fa08640108041004015030003a0a810144c0000e070301007502140b04104208401303120904001e0545203161a09801e03c05c2040000c03d10f00541e207980c00300c3d0a021241c00c8868030301e80c1c02401d07100c4d2151503c0540700d69400c201d845 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 635319298 1250 635318048 635318093
    0x609090c0302150f070201031116080c0d030b090c091c0b01230f01050901030906021201060e030a0503040b180405040b0609150312070302150c0c060c0a1e0516 70
    0x1d140d000c402c00e008070360041c20136041d0241404803603001580281500c2240310203000e41081742d140045044544142d4503841160219210f95180703020f140707824180b10548003450f02d00000c41d0f50955a20364442e03404000b00c0c000984d94140040410481c441103400d01c000d41f60070110107402c2041051646040c0e031894040710310100392080c007816004403120115900a042c0540e0016076500c00e00040110741010304010a001c00c8941d90442264401e45014024000110051145c20740c0568200b12070001280100303c0d5400340c0d02c42c1c03503c910948c800d02d403000c440041c040a0b91802c0d40030050350a100107004005038030f084e007807040c0c490504444941c800c00f0340200081c5068500d0301c01d00d440a030f0180003000040c00880da03144140d40491420380035440703030000c00e4604203528001d03035201c0c0410f03454050715420302802252820071b000d0503400502005100819600d54058000c0c140b140344a081110000c040c1c0205580c0380c81803803030384804003107441881d205122400c90a9000c0c48802c001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 635320548 1250 635319298 635319319
    0xc0f070e01051008040b040b041b030501140702160b0702010c020d110f0618040f1413200d1b0816230d020d05120409050a140106020c010f030609090c0302 68
    0x40031036420000721402041c42006c01c010601240d60488640d501600c2680002d5007410380b4403c01116a14030b5008035416034548200104101c0490800c54010072240014403040b8080d014001126240c1e000360748003071101182c1c000541e8441e1002c16030350394000e0805440d402c01810445601d90301052041d020b4084500300c12098103000d07040f50591032191510f101d20009800401000d00038076040641655140d01c0c4000c1c07010002c1300c03414011030000036004016841c618200c5080300ea06407000390050054140000340751100410f000100390320220800300031846240290040303400d80c11060907480b8005501204a091038019002d0f20345080301500540078090410701000210b84007260840e018100200050a06048560300c061080302604d01d0456180110981500a03070722175084181c4490a0050b0505640300d100b0040f251a40c40000e01c2d0304100002e542c41345000c2c046810040701032111a2054440c3e4442c0c0003802c180746007402840203c0c1011011418203000c00e0b440b825a412 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 635321798 1250 635320548 635320579
    0x21207020f1203060607030302070501060e070f02031206090603031201082406030d03020f1204030507111917030c010e011409150f07090308070f06051b0f0c0f070e0105 74
    0x907580b011124203210281c9195141d0301809032a42084200300c0071f0503000d011500004000b030250034041c01101c42c00100c5031400d00802049150003810351000d40d02b0030440c0c4003a0705c07111881c865001c0d1040c0d80c01440c64480710007191840c800c0f011147c82c142e08440c00403c80c0c0401098503c198034510b28003e100740a0101daa8407460000d0710602d03827692000300b489107007600a40283c44090101202a81402c2041c1d5001c04d1f000030460f02180003440002c0c0300c00070051402030320000c020303080e9072a400341c0e00c3d104035410001c0180d020b00b02c40180c2454450104041c1002102d020b00080002802145107188410b40078100000c00c0d100c2c950003000c0025400a00010b1a0303808140c01d1505104585030700403462901240588540c0820034214004008a01e00c1c100800314644510130b140a01203d5051190403180041c262000044c00380c60010101228034007a50302c402084500d0f280d40d0b89100104503d40400051a44a02d0052a0001035405030113008181290350a444030f403965507600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 635323048 1250 635321798 635321803
    0xa0204050c04140409210c410a0213020306092409061216031a0702071203020c10121a010203270307060c050105010503011506120b151e0315010c0305070204021207020f 74
    0x825903108c0d0010299144555021078a4804021840c08820380c3e803007844a40100c3c40f0040d0740b0114040e00c640000601c41981003d11040d40e00000d40002d030070340365500f5002e090400b003002d02524441c002c1e4102188007940e810f01401408202e40c01120b07840401680700c510400080c5c070050ba501003030403074160081304d41c80c25501e1160f581540070340300f401d06008419101000200040d021440b80a03c0001282c90ba12041c412140302c0b9191042000903080146003030398040d003020745001c5a03a4080e0320044e600001a203900310145440e181ca40d406150400c40504c1700c1c0b060840d454400c1c00782c006900e98200e001d480000f8002c2000b4400ba0780ca40c401d240c203a5001195030b03c0101000e00302000704910410302c0e000d9980481c030002c00c03a41707034280c0050300f44031342c003032688581040c00503064500380c8020000741d11001d158890b040c1180340a441c520b504d41103039926281484520700340001003500c41c90480da08154002c0c011501ca81e42e9040c00700402c0000c41d0040050f1040804c20403020500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 635324298 1250 635323048 635323103
    0x5100203010e1605120c04170106031106090301181419030503040204020a1704060c0905150306060a050408011107060b0916030f06030203010e0a0204050c04140409210c 74
    0x40300407520341d5107501440c0d107040b080c4543c2d80710400c8001c0c071545640900c00008940a20b0254410549460510865500356241010907440a80c0350040400014850100280482c02d003120240d4940c3d0084010a0140ca2141c000c041e413040400d22010402c50790703c000c1c50101d943c41c02100c0c441c0341046441007042504d800064003007001070001400510307098008144841c00741c6440d8652a00c0054a070450710806d030307021141030380c40f411000c1919074040500c80007404211109012030b400140c644002d4880580094010303640090b603c408140aa400c840c01400404000c00060141601c61001600b08081c01c541c213900f00000b00c0130900d045d81a6501801e0400c000c02400005114203800820a400000001c10346564001002d80e4081c031681280c0c188510151051040500c104401c03070300014020148910305000c02d2140d0315401c41c121021000959002400c0c17a11810034010089484603407038110b0f00d5a07442200c1013a801031801c0740340c0b846045005108130702000781c40e160b03079032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 635325548 1250 635324298 635324309
    0x3060803040f051522061211070f08091c11010c050606010e030c10080a4515021c02160b0c040803120907050409030f0503100504020a0207030510020301 67
    0x80c00c0b414841c0749446400704a40401c198203580ca001000003640400042c07003901240003030044c1900b00012038002c2a4004500e43e250401c0110003a100400701060003030740c3c0050000344008100004102c103072401c50740021030050464501c84910301c400c680d200e8a0794021124a1401103106d5203039401081c101c004a50301c00d01400a80e03841c00011140040000201c5038540320300d20483e031041d1034280c0b5100c401c40c074030b030b441c0d224902c0d25200080940b16500c441d103449105216200000703a240031013440d4a6141c0c01e50381c01c01c040f00308003281e1210750040760141c031032040303200c81c03000380c4420740d00514503c85440e00c1e03c00603510b00074203901240686440c40b8040484482d036038001885140010768000803091015080640b944d400b585075401c103981603943d0004d404107200108804000120007440102c40501c09008a035800030f00701d1984007002c005003c0084046011002080d0740030005c2d05015004640303030461100001e68404080c84250303040e00503428a40c1e11042103000b01e074165070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 635326798 1250 635325548 635325569
    0x30209010611070b031f050f030307140f011b030f060b0f07260c1b1305071e02010f1409121b0601090506010e0d05150a020c1c0306080304 61
    0x1e1a104007596440c00c2c802034203440b40103604020a015032004050350041e00c500a840e0404401d0300840075598846421952243c0c0719004400d030540e07400002c0320202c55124200c6494541c0c0c040740c0d5031501c1c00340d1903035240075424124410b28903125045550000000e650381440304103035604041d0300700c83c04c1e802900301e01001085803000b41d0141e003000f40056441664440070403041001c01c0311407030070400e0300c5c0208000c00084200d520305003007007002003800d003454540848503500303000208010307030205056262a40344c500042c0d0f1503008250214003003182c1200105080900f00d0000c3c020708400c0103615155182180750020310721840c8841e0700c50240c020003001c42050300e0020071041d4019a48218001205448a51b052641482040d000b0000740c41d000c1101e0600c07400140081c0180325010707010b07500000340c8601007500040e070354400c02a0814200d10a0325804000d00181c0310320303428085148900c1601a01c59440c8030008070b41d0f900c01c0c0e5070422415489400454a03841107200750420302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 635328048 1250 635326798 635326801
    0x321060a0b0a11060f010519150315032418020303040308070606050a0e0603120c101508010c090801110903030a0f0314070e03060702030412150603062d0501030209 72
    0x860030800414002c02035003030040d00c6101601405281603400c41d01040460409401000f841c240407807400040701104400910440c00d0103041c20710404e880d00c849040580700c1e0480c905904003e505c030805160080c51000003000300c402071500021116528900445ca024040d501c0b00f030004604942c11903000b0081e624151640c0c03561900d98201c1074054401c2a9607031000036a0703685107640800103142c814404d41061905038100b508001c0a0502065022420840881101000700f102d8248450005000490342c0201c00ca40010508c103030011041364bc6040c10000300583c0203120102110304c00f00c000e2011021405400e220350040e0114142c05510a014490303215020340803186e03a1060908c0c0000e000500101c000f0032034a000d49030080450b8a41200381160304007448155801a464001149814034207440f10403001140b58010709441c18444041c1c0240c1e0a42e08440c2c002c41e005201072000f819400d0901001c003100300308111110b42c02c0400d05c1d07901c0c069401141c0c102c1e9001003440203030307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 635329298 1250 635328048 635328059
    0xc1b060203040611010b03010c092c06101205131106070237060e18010f050d0807060606020c0102100e1f0207140d090b04030c06050c0f0601080321060a 67
    0x88100c0c50401350031a5488144414542c1c03024428a0742000c1240d40350f48440c0e2500800300000743c803240a8003140c40d0310003034400ca2511200202c1d82c10500548840b505010034410450b801d810400040c40c64500300420311241c001c16650403500c46001c1c540581607d40d03d08100842e51043e900029040300344802103031840394003000c0c0c8400d40c202e050064540b000400d01c020084804a03040000403800d074102a2440742088401002d410b0f980b00480381480d41066805000f400352481014800d501451400c410041c114040e2650107900c50410310121f0380707514010351200c41d900c0d0110700500c10300480b12010406400b40445142c070140c06070000b0f00c88180e800100b0281080d03060f0a203a020041140010b00a460010711460f01c00041c190070311002d00d00800f00403a903801140c5415090000f030001c01d01c0b200610040710114100680da442d9810304007800c00720124040c040740e016400000500b600f01100a00e0045a074002500308041d10f010f00d280c00c00420b03a540e542001d01c90600b40324 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 635330548 1250 635329298 635329307
    0xb0105120106051c020a0e27010203190b060f0408060f0f071b0c0b1c0518060c070201030e061602060606040608151914120d050a031802100c1b0602030406 68
    0x38050002e03101c1010700c3d449248540412034192170480118841c46d09140d40555508c01442c1d004014000035480d40c00c040512031080103880d181d4061259a8041e403190325074503c01180c1c21009042740a40e255503072800a191a000201c403088044900d41d40000e000480c440b43e4280319038550f480d03040c0c95605406001c000603003000412200310441a2012540b00494400342804032005541240d103402e0813251041502d20107855030b101881c0300d0302d0340c026416001c14816809420008a9603d0b801c0d43d00040b0003034042503c490120f0f0089905115620f050300c0190a0320b01d100780c088803c0783c2c48141c1130020341e20807480303604002503590011034003603685d2500440030108010800846900030036840d15080526500201c1c00c070300030030015800b0703080801200c0d040c9074160001d408104205080503050740301d0141c0c21010980c0d00e17036460100c841030440068001d6000341007200ac00303d40e0319002e0103080c0030100507111440d08210991100b134501a002d800d5640780e501075405c180c5030420507039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 635331798 1250 635330548 635330599
    0xc1306030f0602030c0f1b0d021f02090301060b0705161a0301090216060f0e120304030801060507140a08210121110d050601180209030c010522030b010512010605 71
    0x701001030801c1b105c07851844110180c0010a4035249010b206403c28401d14540042c00704c80c501903400c0f2015005400d0b0000e91024140442d10501503600c0e000c010000c1d0042942d034004081a907000704a107001d00100050940c40001c201d090208a9515130f900c0b60341c00d400d0204e451117920000c0006100c5039902e90050501002c02c42030358133808803d60303201d0f07041c2c0e41ca070b844546859640b0003050369010000c005c002d185082d940480351035400c26450003007030400140902800d204001980104000c480e0a040d00034a40784001d8981590481c0f80c80c1c6180d0f440205055800c9096500350960307230345980c8416048503881d20901c1c8420800424003a021024482c042d92400c41c030040c0d0f129140c42d2600c010502c3c51166025058641c14880005e40050f013104078840500d2040c040715030640c03400210a5903e0209003803443e150104441d0700100c0720058401c9040500c2c0e41040001001100146070307040c2c034812581005e4608041c0f611908a52030b900c19a80d100c0c4100000444c002d09038041107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 635333048 1250 635331798 635331811
    0x90b0402120a0c030624080403140301090b01080106052d2101030203241504090816020111032106060403020d24061203030e031b0c1306030f060203 65
    0x360030800080c007141c194020854508000070348403030940d268030340d140c4100070151404480c3d01540303201d41030103410004c44025030f0205010401002ca82410b000d540350b40e02180e8210f0131a50b0701d60711506088060691480100d002c140e0b035500110b0030501490a8070758507120b17120a078410364002d0349000c07592003140c8012204640104558a10594216840c41c500140d00203010a194034502c185841d014120803519011000c10004552040c108000ca5400c41c0003c183d43d04d80354142c000107402172042c464010000000050480220721200201d591014000d88500000c40c1c90074a42948078440d540c04401c68804035a60707040d185200b400702c0c40c0c001d10042d1805007895102d501180046401034020345c5c20404c1c94060401c9a01d00000c0380032508403852051101c0c2e0b15121410400c1c040c42d07c4020149500d8550010311141300300160340c0042c0200041c07004640c580c1040d6519a81d56260340b41c0959a52170804c00c00a9560182c2c1c41140e1740300c044607080300500d481e524006c4d0400b4011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 635334298 1250 635333048 635333051
    0x4030c15210e03040f150c0203120d0b0d051e010606050901050d090515040b100311010e032806230106051b060c120a110313020409080d090507090213090b04 69
    0x10540c80e20003000944041c02200082c1e001c00c5e400e102c0324a0703043c101140000104a07070004c030880180ca01003a4043d8030300340100f00503159000c1d0000f01c00508030000801d87c0180420042d08103002c070005800001d01661100903020b4001e68403007600ba80c900780114070100341c0c02c1003a80d950703500c81c100a001500c0b050200050000b65650780d1818444c55110148030b05090006110a01483c420743d1500095a0001100304501d555503020358040d4000803203043c801d0009840216450521841c003000300c4550414407110500c5064a08420036104283c500c1807429800044089651581c160081c0700401c0150381607213040011209a801a011480301030a01054200000d0341002490300501103a00d5580c0c0b9200342d5280712500900041a0007107140c01e02d262801340c03504400440c0d8020816259005175003685e070020034040d1000c804004c0c030004000480e80440748565014000742e40c030820907076400315950503091040e80601c060700b0721414100b40b8200901b00d05980804007142d0301500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 635335548 1250 635334298 635334311
    0x60e06060120120403030f0906020309090103080d090b1008100509071203120204121119170a02031b031e060105100905040f0e01050106032f0f07030504030c1521 71
    0xc102c1444c0c00c1380c0d1049020400c2005005a9250407242c0034000d00341d00e100071030510801c800020341140d0107210140c00f0003030002e0300e00ca50403915000701c8002030700154484a40c0c1003401c40210b041c0340610503041030780269280e03440c0080c801d0003081d02030152000100111400c040aa00da0407a80110880c14402c00c2d5260380810465030006c1d2008000781004020041c01c1c504110301d000180a404a100740b41c415004410010300c0744140341030714a03c0d05502d200000c0c007186c0c40e2411596410195151252001402c0c17050824140790701d00800990a41c5d940000003074103080300003204c201001440e080040148031504000a291070303418401d01c6c03c44115541c5002040844454070903550038140c40c0c00c5d40d03102030380090007000d004000500c1c0420011440104c441046011a40d50060050f1510300e090100001001a07881d0040708641440d0740d10214078010341243e11520040301c44600a00340010b81c158500381c50403140d46907031200448504413150070301a01d03001b5002840601d40c1c405 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 635336798 1250 635335548 635335573
    0x6061412070203160506010f06111507090b040f05130908180a090504050a120219110607020a1710020304080a05032806060305090601060905120c0d0c03060e06060120 73
    0xb455131641da40210040c10155041c0b13101411401140c0d0810b0080c400b0380081088020800600c0e003042c04131241e4201071986504600b15909030301031b0f00c040c7c07000c079010401103400030110350000c049800c1102c0440042901e816614282c3d00615070143c00b0300c0d020300c03211102d401000304841504800402c400c05007a16103240e501110011381d001d84041c0d000c804200e04200905407133003a4070701d00c2c0c0018910180c036076040709210004008024a0324414000b480f4443d100c1400f9543c10750350040000404a84620300c20101900524591559109000386810f00c050103200b144e010340d07000804103240c00070f858810390743c40c0d0010304041368151038603001039044c910003d404001d00c242c1c1e5101040384c500c3c3c460000e0030789602800104d016009a4010040903030421480b9080307071400d80e00744442800013034030f060034484c0514010360052800d450400402c00813001d40303416288a000e042002d0f981c03103a40640e8900c821181d0f1800f007060aa003503070151080702c00b00105040c20100b03e0f6801c88554 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 635338048 1250 635336798 635336827
    0x603041b030b041515060c0501090501020c062703030c090f0a0801051005010305130201030914070801060303090b0909011809020319050106050d12080601030e010903021006061412070203 82
    0x540c0142c039980002000d000400c0400e80515655110041052050340c0340034081d841a401c00b403103041c0038800b40750714001c10000b00f0341281501c00d401000031921080240502502c40c03a04071205440c8a140000b410009124806035102c4041381000842c255130351032170f012940ba481303004607070741c03148402445040c160b40d11007801c8007401c611000418913051180c0c03400c003070841540210781030504100c10000c50248a81d00251226024640400d02c0489414040d8003100b81101020361070040c640c0105401005400c10000c4030f10a9480c1c0500c070790707600b408004034028041c03103907031194011004102d0441c111981c7e007030500c0341120006428000d41d000900e802460319a10f20640c00e002c050400707021007885200c000384010ba905103001519942c5240c62202250075020500c02c43c1d00219100340d109511002050310010000c1111030140c1c2800782d9288524080307048070505080e0f000c150b040c80b6240c06000b28242250306070410089050b196001200207203581e08610045c0102c42060000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 635339298 1250 635338048 635338103
    0x3180d020d03233402070302031b0f040b0303160b090d0309031223040303091704080d030203130c0e0702060a023a020415020f0a03050306060304 64
    0x350018000c0c0c041030301018081d10004048071280f210400e5044030350342400a0095484030b41030a82d0101100402218054910012800c103034840e610460720340803a4000490f24152802101201d000c0c504074803161141465004459400a10500d0015100c6c1002d800c580d4590308028180d9080000604c51002c500060000985200e03032a042803000e100b00901c0354094204c890716042c88810760a880140c03074006602d583c01010360307541a0030040d4440012402140f00030701160380d50710b07091030704004000d400d410350181e58100401100c0541055040e00b20b8084403001c4c4054440c500301e40c1d40650082d01f00800c12480c41001c2c1090302c0010351059412009440e580546140d1818a040c00a24182000b0300008885204001ca13080c5180760031911100751032030301e5240000780c07100b8080a56640300f05405c0d450850010402285a0003041d50f802d1006502d5402c4030441d10071440325554800c003072040500854010004114103090440003540d0085c0500010f0445150203400c14508044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 635340548 1250 635339298 635339323
    0x151b011a01090e010b031801140a1a010804050606150d051f080307150e1c1d01180e070c0c0b03040303060b03040b0c03091f060611060705030c0318 65
    0x4840d03450300342581c10080500c003616003190300700003c2d0f040498503d100c0c4070241031245c0c158108101e0401e070440075000f02c0c8011101209418050905440e02009495401030303000c9404c0303681c613002c803640d48200001440b0b00d0300f040c010400c40d02c070081170009866403c103541c1e401840c10440540078004901403907001d81080b00c813003075201d500201c4604080c115034000401c20b800410080c00803078100c486d5a403048110303080c00690800600c820a25100440b413009100e8403c4950602d03055800c90003e14000d410704206012103184c80004440c0d09003841242520303e813071848180b00380c40441c00300c1070b4884443d007407403050740c0180e03140c5002c60301e510b44c40b00a005070700108100426500d405500010020680707183d0460626541e030301242280101808100d800c04400200e06a00401000c1224040c08140c0b01c101e032206c00c17046010b046c5c0c5000780c501007845018075592420740007030075500c42c40701640c82030b0560700d900440708215400a0003040d0003800700c0e06070060850342440341c41c85280c07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 635341798 1250 635340548 635340581
    0x9060a0f1509081f0b010c050a060e0c010509011e0306050312041d07020c010809072c060105030402030a1202030f031608090708150a021b1b040209151b01 68
    0x20034050300030400b0305503400c5850f20342c000e070065010180504410102c4c0c0000b103400800c142c030041d00106c560102130309002d40a88900e0513144103101c400c0e80540c00c0c91100f03c0c00c0da00c5c40030301d102c010b413854410b0726211800611030325000f0b00900c00c0c1340b403228040c101600c0c020420590342c4000915001000e074040810500008040110200c40030a1915030b032111002007400d8580700d00040d4075200e800131700d541800036250020b100020f0a00c807090140009200e2070850700c461015552806050410a210307120800e00030402540c00747e400c0d203104e02e90040c01007041869940d03a20000c0d01510b2100301c1076105c00e00190140b40c0468001d14824000f8020388500746840400043c400c0001510714101904440020f004024021600b80b00300f01509006180c9501c0303035044200244213881e40311400c8201f0302c1040b41c07000707404500c210a500700c441408012420310b00420040744541400903501a1070f400d00414030300c0950740640b26440c441c0e0b10b02595281d218140d64291110107640841e84d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 635343048 1250 635341798 635341829
    0x906030506180a03080a15080f0d17012601110307050a020d0c050318120106060c0b0f24040f050f1006050f090603040c090207080901030f090203070509060a0f 70
    0x89890b9048402001c503110700508414a858801900000024001c076000d82d0f210540c0003601c08001048200815450301100c260b181072480403034031064202704c0040087c0e85281d1880c0504499040c00313060b6289082c0548540a42d900c980d031040000d42c00000c00c9540f12042d120010990300301841c4030305550b40f246a954030700b00c0710007070810901103542070501c00d0540c43c0e840450f000200341c134250384590800050340d9102d00d000408246242030002a00d60a14001140031503014581101c1148211800070503901e540c00201e600c0c5104030382044400e480301048d902c1c811348010801003c80310150000846403030071440c4401b9201c04480b03880c40c440300c41c410b11900c1355841c1452001010b03c0d241c17072410034020b240c048000b445400600c6101d150044049001d2110642c058001003440c61400c55580c4100d160000081e000001c1640c046031400c40b0641401e05640240c101c0326500802a0074501e0034403042100642010b4821a0040c107024000710300900400c41d45405010441c2052118 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 635344298 1250 635343048 635343061
    0x5033f030a0612050a12030e0a050114010509161206120b090c121c050c030a1106061005070201140d0c020a021216060c0302010f1415060f0d050a060906030506 70
    0x151006580040d0309031001003d01d90100b140802c4038298254070121450900002c00f00c1100608940140b903240c07401542400e008125055210800d5200249144061681c3c2c9a00b0009a40c104441c040740c4206100102c90010344220440f051008222400144064036400c021541c090304250444194a0ad00103110b9240003c20003030324410822aa00c0182d40c2207100600e40360010b146000c1d80d00b840c11040403407a83e0080c07094074021410304045a0b1544180400105204403800c0041030600a17400440c00b24207000c811070805030201c0d01d940303180403015401182d0000540c80c02c1c0220030401d00100003911814040c0e010403800660040000d24145d004011801400c20180246540141821196000c01c3c02c488000c8840d14101050070001c141026805005041032043c0c0092606c031352218040000d07545d00780646113103040015030b119400c4c01d05c8014800c070030680c4800407040c04441c00d01f000d81d8100d80d600c00701c0d07404086041a41d4201100070b42e10b841e017048880b41c2000082010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 635345548 1250 635344298 635344301
    0xd15170c18010b040506130b070b180c011d0a030c060207060e1206070f0c120903140706081807030f060605011106010513230106050307030f0605033f030a 68
    0x81d11030441070791441d07540341010f101c6040c82284a69800341c4400b0884c2084030074141c1d5a10024590300c11101d0303680301985020500000101c509503507000301007045c00c07400a0001880511208103851320301845100340c01c200060450849543e500c0000c00d100400000d001085400047c20b0980040007100e04041c0084d04400f402d170881c0d4020f5418500625080b007001070f4050300100e1505010004000d03000c0d080f1041041040040d20318012280850650b0703030710218000c21280101c0b40200c01a0000b044640c0315462442030400188011010074010080200310104070b2402c2000c5074055607030b03507440400842e50702031300741e44107651070008018558101c1004d840800f812005040e4542c18480028684005e9040c444811075440e950401c056403100d1483c2e5800a851300c4400c0903603900c0700c0040503680100c58420000b4140480542c882d440303030040c10191030005020b00021090b80042e20035040c1c0c80400c0b010360022401075041c000424410141e054412004000e40e1f034a02944281c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 635346798 1250 635345548 635345569
    0x10b13050a1a10030213091803080105060a0824120c030c150a03021c09050d0f0c03080c0307200744210702030c04110d15170c 56
    0x550300340d82d07040102d40c59480e003e2000080354181030050301c0765003072809182c4201c0b16803c5201c6217407034640f0317481c5c070340803002c1c5000c48040c807aa0344c80004c1d0380c9074401e00215000f00c102c64404140f0b820301090120204100c2044010b40109014030350308a504000707400c0e001049050190307504a0111020a800c05000b60940600159050740e80c2c45c0304101107414600c00d05150108055005c10300801724120041c001000308100d05d414410721051341845520f074010080a003001c41d10080c0c07010041400b0704e01a520050b0144c41d13414071030b981c2501ca054a50300040c415020001d04281d0305404000744070180b003a141c005002000113a0828510b44640e41508041c55004000e6103805c0709071020011080d0101a0140b01032440040f002e0b4040380390032464019541079100600700c40180e0510340d00600100d50085007168500d1702c0e6082400704545d00c0b00d100404c181c81c200810380403007120ba00440f4820030402403540010b80d03036082040b0032504103059940280c1104940050f140b07406a10340307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 635348048 1250 635346798 635346821
    0x81c0e0d03051609060c11041803080703050a1104030311100501080708160e0135210c070509040c26010f0e0c1516030509031911090405010b13050a 65
    0xe030742c0c1c3d418000301401000c005500142007420b61f062051306a20399401c14101000301300710b04240030031030307250260810b481240d0510009150800040e16078030540200020400000055458642143c4003240c43c2080b220000a40d48640b1100840071805841858003c06001019000660401d0802c60a1141d20740c1a00001c1521260034887d4080c94020507046502d851074445103100d0040d028040e0540c1c403501510031a070250107407446c14002194004105c9801449018090782418600805000703031316207041c2540c0811010b00c01420000071050300180501c1135904030b196144c00c491184500c1c1140b404560200c0883c0d0708a901c1f00b40642c1c06041c00e507500c14844002c58429a039a41d070b8039405107031b10684041d800d0010544c8010111044585e0607404070500e0080b604015145a01c5a04501d0192040f004e00d0b2808001903980b0942e010b502071100c84418941600300408101701a0041c3d9655580e1700100e80243c0e80d84803800700e46503c01201252910b89581e04100b120f500103180c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 635349298 1250 635348048 635348057
    0x90d08030f010510110c01081503010501031212020c030426120a11012a0c0c0906031208090c04090c080303071e0c0201050f0309030f0403151503081c0e0d030516 71
    0x15092441c0421118406c02003881d00f0b00b101e5607114031910b451408102c0464055103401c0000c0240b1010081c00001e035070b0581c0b03c0403022a14000810100c0c0304480100d02c82d44c20900c03061100401d0030f2065014120509074561a601907214403a00f005158081c01141c0c00740041e03035000d1290800e03845903001c02e4150007000044c03c0d0002d4400305045008102040107208541c00f01950300540700350000c0c40d000300907079038039507151103445004118070b02041e5050b080c0020032a40c0d81d4400d044140c800c000000240011058541c1400301034400d140084485206649000c1402a81080075500c0340b1002d640300c6480c0074090840e004c4000b8440d0004041151003103002d400b40c1d8010341142d0a81c405c2201040d900c1d80c414280f94210f0040c81e0842e21550800100041441156103106030b480000d080d042144413050320324550014000c0c40028060001809288504284c403864545118440310000c00e0810303490310b545003000c0801ca10040803940d00c20600c40c034601c0c00e001c40c20f04603800e07040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 635350548 1250 635349298 635349317
    0x90f1c030b0d1505040203030d020705242a040b0703080601090905100519030605042103050601120f060f09020c120a140c211206010c17090d08030f010510 68
    0x44160f940f02d5400349040340c450701c0d4004282151002c00444103450001c503c11921203402d4030b00262507508030b19411820002055001c05414030020740c0600846103648400710a1051015955103010b07030000203503004009020010312240008020900944a5580c410b0035240180001d00070901d10340124800390300e040c0801c0925003151441c101590402c41d0b20440140701000e0201e642c1180c1d400c01000141040140401c000104180710101384110f02d82d94803403810300e401102140c2007222a107001031842e44181c0c09280c140c0d44005840188a18041071041d10389a80c800d03410b905074080000d099000030801101c240a0010315100224145090310301000c80c42c00074401804c2c03206164580d1400102c0c0110008208044090641c240c680001c444143c17004655258100380308602e1500c80d00e400040300b540c441d4400912903076200e9010400196120000100d40d00840130191700403148410400c041549100034601c01c00300d003455a14a0741c1402c040c882c0e0000f95586801c14001c0d4005c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 635351798 1250 635350548 635350553
    0x27122606100c240b0307090c0f0e0901030b07021c1107080304050d060b0d0605070c0c15120e121603020106060203130b0a09090c09060f0203040f0905090f1c030b0d 72
    0xa4002c0c00d500d0350740f0f5031030200050628a20000c00d1a09002a4036120b4070718009881d00b02900036080058240c0c840d11004880c002c03003941c0c1c6540b12509a9030082580b001400058030701003550f038103e0540e1046421203085e42c0e88005d11401c0388280b040124080300c1082003903003403c02c0620050013402e000b131401c4c140b400c00421024440e8060007000d1036158006e181d429100c902d12011856080007051041d41060350740078240292240c410381d191084081d003c41c0311405203100d0075400280703582e0f0300c04514084180c2c0c401800c1201e0b11050a025400701d000c060707981000900841c0058503664070b1041c816290281c2180e01c503500010940d007040c8600a200110480850104d403c1c110b80c5030b40e1680c44540c21220384611b50082a0114070300242d00740555481083d00c2d0540e5030586402400d0302c180380d8140c0e6640111301c1054940d140015045c000f0b644070750002900107078102d0407034244c110110003103414429034101601011450013010048035038140508180118141c5e820031109403140c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 635353048 1250 635351798 635351813
    0x30f030405040f150905060411040501020607080a02040f140306010e0f01060e0a0b210105090112060b0f0d050a050d05040b040b0a0c020901120627122606100c 70
    0x51003580e100307541d60743c004407003005150007081980c0c010326400c011203030b1144411401054103480c0280610724000715030303841081441c212000d81e00e0580041c0b400342d4503040101c82c4160000e10101504d0f070280400121040f043c0c8040029000680043e180f55208a0070b2520784039050340000300e50010310060001110380c2b03005083c1590079519082e00c1c14114040402c0d003050b60b9603c00595940009412103208002054040408401c85404401d40c0d0380d40d020450686420300880c100e0701d017900c511400141c200e45c0100b5428101419880c481100800060100d442e00030069804d5000030f82c1e61400c2007028404040201c0c1c0c00c1c2400f9041030705004400b9094017079801019510388000031814011400f8206030601c1d1940113207000c0480d07847d000555081c1c1c044a400710745a9040042064910004404070919205441c031001c0b411201922908404e130704000054007441605a034145504034007455178280c840b903040b009586401c01070203000805514005020400c60040610320004005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 635354298 1250 635353048 635353057
    0x5100b01031404020f0d03090b040e070e030d1b0f080a02010209031005010e0402041a04090602090a0501322710020a15021c020c060906220b0a090f030e0a05030f03 72
    0x2a46ca8102c030645074078080d114050350360082c0c13220702c10108000513a040c4030030040707210b034040760f0701c001c1c085c5030790400e150b80c030312514211101007003040901c0901400c5c021041c0884601442e104007a60304603440342e4102d640402103040050750000f5000f1914102000022040704200000300160362405100c0300d0702d4200030380000e10031521014240b140c2c2503906000034619900410030441d004003460040700a5001d100301030f0007050000c10008166000e0540581d1007210b0703200181c60b80352100381804400480d081940e9800c102400300700c00020385186031400725003040c041d205007116030307008000005000f0140e03841194002d10222000682c40001e01c0d401100302074000d42c03100081c0c4140040c82414000100181d88041071014000700001507030303402801c00100380d034220b494a0001c45180914024050b0700003c4e9010f4110016400440031503019880324000a0700038500d81e40d0b00c1081c280c840055002030396804c040c04007864404d05a10042404800600401c050140740c10f449018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 635355548 1250 635354298 635354329
    0x80a050a060915140718060e0f271e090c040510120309030b07030b03120f070206280203190c021c0c0e0703020a0912030c05100b0103140402 62
    0x21126041801c204086400d5014008940300510034403c0300e82c580d01013908210303501e03000141c1d800f5403041d0301865414040140c41e11a929140e9402800d410b2001210040003d250850981f41080004841c11000d42c1d14010b506140f00301a410280708451a800c141a194024200300340180055040006030010312080e040d00c02181e160780701c1c9a0003100e4002076101c85109805500b200c400c05510038801000c0d0781c815624072850f0745075028110103d411410781642c05511600d03c03410042041c03800381480a44491106140100543c085022600203051494805030030181d030100410480c4d00c99131008001e40700550038043d60610503e4090710344481c06052180c0640f0103015500d0704a060307140b40840d800340740c9c1c0e51121440c182010498620270780c4d04800d9604042a03d1511034001c03613039480165038500d102c007401c02920084085c0c84403c110140205409003c1c00184144000307602d50b108420005114101d05001405071440c40340001e41400150080000603902c2100044072941d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 635356798 1250 635355548 635355551
    0x1903020a05040e1b180117011406030a02130b120714030a09060b0603070905011803030f11010905010f020903010f290d060513021008191a18040b01080a050a06 70
    0xc0700c0292140d030901032450403104680d000075441e0b41e80522248040c2d005c080031390700ca03031110194200c0141c1070340081c0154a02c0303d502100c03007203c51a00c04040c6400400300c040040ca000400003050510141c0d41c9d211001d41c4038040303a001032260994100660008042c2408000c220707580c0f01041151100074140c10303034141c0da0750f220004e1200651000402c2c4102918160f40da0030001000703030116020744605400034070781c1c0c400c0c801600009640c410031039505480701d40c44050011400e40c1c1c55000c4c2e011301c4502c2e640e507001b60004142c1c00d0040c440c4070390440200607034801d1800c06041c01e45007228448038240d401c10500b543c0c2c890781c05c242545003030710064440e5501d510010000704603108561002d0400b9060006000c00f4248050007041d400c2d1080319a5114986d00b400291680300c8202c81c084041d00c610000d40049403040e0300511504d0102c5e001004040e100000020864405075030014910309042003044200a00303241540c4c0501a80001410707a0b005596505943c1c01c074032000144840d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 635358048 1250 635356798 635356801
    0x80603060412090308030f04061d030d0c032705060c0a120c1b050c090105040c0c060c020709090c050a0515070602090a09050403030c08310203030706020f1903020a05040e 75
    0x243c8640400d001035a0312844c01c0d60b4a080000c506501d560082e501a10b45504d8103000c1070b83e000b110500200c144903068065420901c482808800400941d00564145034960710740c00b41028803d515a000407500c03032083c00e4022142d041131441d18200905001440804121104403543c00040c41a490f6014401c085041c1681c8402100d4180c51402d00020400e1580d608900b0040f010400c1100c8000c256001733141c076a40c500c02c00c0140d54451a03030801050740c03900031001185d207076040a06442d011740100c81c1c0540d6225640411103068100c2512400d40b251000d105a01d41503a491001b000d08803101d07161006000c414907030341c1c0314040b0300404041e80004c80d8001600c80c0300200c0010032484100b00701c00e150508014000e080c10400c0c403c00034402c0c0000401410a04000400b6500700d218014010483d12242130500030b9a200c00340d0b1700d0310050001c84001100c0d80010641c030088a600e003500d80948500760f030300066800c00c2d181d041c51300520040103000d41c0300c0241d90843e8510001402203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 635359298 1250 635358048 635358083
    0x303161d060c0c0904150506041a1002010e120a08010b090105190309061103010815160e010e043308061303120515150f0a0e061b07050108070806030604 67
    0x40c070382003e5890342c0001c0444208410310005404a0f200d42a01c0d1400340541e80d1510100030032a6400c4801c9c0700c8845031541c1c41e040d03a04088140b4001c030051400001082c00c7c034150390926040d050034010041150008603c00c46a41c404502c2c1d005104e03201144d400c0070011400603110b8051100035600480140e20078000c114800d810402160303402503020015003002040b043c10550090080c42c0980c8240c072109001d071482c07540040e104a03000f21070f454040b8070b40141103032134818610710729040007220009030754940e07142c1c4070700c10700342c425424158840b40d02143d0420301c2c8003401001e949000d0081c68104000040482c00729402048104540100d42c07151500fa00d80032594403039412028602030070000f2a0311f0522007210440022602c0900b503010342ea2800010317208034084000e60f0b02092018102941c0182003100c1c80080041500c0e060140c21104041c000c1c0403c5860511507000c0c100402141d604000400d4001700245005082d51400e000444d9803000090802424103000800c030100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 635360548 1250 635359298 635359303
    0x16140a051e03070f0803040f06020c0102100b03071805010303081311010c24050a0b1e04050604090206070c06181203080627040606150207090510090507020303161d060c 74
    0xf821311452802081038855892030381d26003003405202e282202c200030100c0c0541c00000c40c0610342c5030580c02040c0d100c080c2507004024220b01c1d91007070740501c210300c80881c1c540ca402d02d9400d101035400760005519803460800411a000207001929003800691021001c144103003e2142446800e0030426940c2e0710034582070708105940c0030303618400446a11412081c0710345402560040c04904003d11a40c01140d041100c801411052010500851120480c03142070503081780d030b44030070010400140c2c1702141e000b0960b0b41d402041d04070340ca13a040b00d405118458000341414000b0170b14403060704406041255024009000590280600c442c240006206555a102c0d10300080503041d446032480c010440d84a02020082d5012207406080000100d0b85407501c0b08060002c0c0c11540c0201200c2d464000204010036019020303260140b40c0d0340f4003090502c01406600d0190a90ba80116a24609584201da2043c8820342a80801c00211480c1022292101030b5502c21001101c01544d140c481030b1403180b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 635361798 1250 635360548 635360563
    0x11092b081305090f060301110a02150a020405030114041a0c07032706090303020c0d050705060c10060303051c0b0123130b1902030301060516050f16140a051e03 70
    0x25407110780b0f5410412039840d0382d07012a000b10307029070013030003c16500e200c8a0f01c18000c0308141d10040c1e110034181c65104030310150351030700810100001460301d9290b0012900707407000112441340010400d030500040150b10707201c0303500b0720006040d08100c604100c4109080741c880d0903009002c00c4414080c3c2c1215400003100e060051f40c9290b0410b0100f40e4800000c2c1040030603100a4005d806181d43c14000c0d0b08100001c1030056501001414001c0d0030b150401119400c0101c0058141c80b07040c401003a0304019101d004080c41c0652100c68580c240c0301c1d800c2443c00720203009504218140510351007540d820845008881c280e035072005070150380b035062100281c0103090280125a180701030000350110410000c100c40340c0d601013503c2009514042c1a40c0d00c6c4402c0c0b103400b001640400206038501400703141218454400c0b0180c55410320402d0702c603407411a204550840401e150396040000001448185030452800c4d01d032083d12a2504001904039915000e8070500a10104d6a4040c0c0380e50500111 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 635363048 1250 635361798 635361809
    0xa030c12093b150103060803090a15091203170a0207020f0114071509120206040309061803050f0625020604060e030c030d050403030c0e060901031e11092b0813 70
    0x41c40340341203190104100f01181809001c246000d01c0851340000200407a80d11a0015000d0100c561030b03c144004c20014000c1c03010100b0280403804540100141030803404c070340c0031f44c1c1c0d64400421400c030401c1207007030003074030508403e03104110b841c006880302c0009040a04090800e07c014000c1340c80c60200c1841091801090540c400b0ba00d500754080e0f507404243e0103070040b0524500c0e0038541c1c0061303a44140907200500400d205010800013103101d2162280010541c880594900d5540c2d40c445107812451480040d190b040041049007030191100703c82980c43d450700400f0792128240d1000794507140e0241001e007405842e88500c042d0100204201c13000c40907030504a940d00e60402a03048001c000c191004c40000e824544410b02d81d6118507440500c08800500c11031512194100550060185640d40d0164914084940c24003251310320462212141c00b0005a40c4e801941e010032450004c0c4150003000301c150000150840d0800c809443d0400340e00c28203040d60340746511102030741006c465115 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 635364298 1250 635363048 635363159
    0x9030c09091e0c18011820030402030109062c03040b09041104080d08180106030305040b0a02010b030105090a0506010b0a020303070c050304080102030103140d0306080613020a080a030c1209 83
    0xc0e0400960984c1c00368100d400300404c03412082c070380d09501c13825140050b12076009030104020200e5003c1da03100055411500c01030001038940e40c41d90301c807015955010010041c4800002e0446940740c0d0384e0611415129020001d1440d0a04040c3d003200c4030700a20f0007550080d595011004c01076540c0d1000c9074050403480c0100c4054885012005111103000c85d46a0400c84070b08844401030710050003003400b5690700d511034606060510060030102d412034203803071342150340350b994240c01a1020311440303006500d64405004003181c0c50070314901d059010b03440204503000800c8480e1116034080161b075001042e82c94068520b6100e81801403850003160080001948000000002c100c407040261030610324940540c0c10b485e148910990840f5081e102e1440b01d5001000018103c0300c003440c034014404e10091089038000d0310780c1c10f5145040c04001d400c8012a0803281d00c001408140d0a1560000b8000d02e894818a0b05019807500302c040104910207840c0d10b10300242c80c03890000c954a4010740d49000300c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 635365548 1250 635364298 635364319
    0x91814310f14160b090d030324030311151b0c1f0c0f21110c060c09042d09030e102003090604050904020303040302100509030c09091e0c 60
    0x1503c3c1c0710084160b022042440c6414001605071040084d80d200c541d00900c91400420303140c4044d8050810080210315207201c140009182c079002586900c0070b54000c2d50b40f001200c1c505000d985c41c08800750804091480240200301c1a91500078078a000310307c00030002c1c1e4550040c054503614241c210301b50000d14088a585021807100c20740c7c0040000360496036409014400c1181c241e884c024a1111a0b4900700c5030305001001140640140740019080d080807450900c5040600b8140b01e420b9810b003070f1014000807003000c145014001e80380d024102040403004015040d051681d00100c1002c030b200c2c00c40d201c100b04070902d070007500c000c0c00c03121000d0024010166080c500906017244d104407108080e03551060180406000002c2d10007080028080b946854100420417420a400900485c0c0c5484204008030040e11448000e20504515848072900d13481e0100030182444002d9020074024481202000550f9400203410810000342118418003005c2c090f10627410300151409203a0031000c40071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 635366798 1250 635365548 635365583
    0xe0103060603290316030302160b182103161407050102030406140909010e07021203010b1605030408070b030f060904080d020d090203120c01060b090d020907091814310f 74
    0x111701100c54030b40940301281c0c9072291540c841c24014254100c0c0303555170502f81144c40c0e0038003e030008699400b40741841002d104104d2124078550120040d842c28640c0c80022004001115070b111158800c010060070b200307801d10000070343d64011442144100b01101001c42801110300c000c4841d26007000d001c168a640c0c6510007441044401c0d1803920052040030540b0102100010580703050340c3c1c2c207140f00d5140c0300e05542600b160714107240066845020800002584800c100301c103100412031810720039200c0c9422403003044400d8004111038041d08044003044006031030b000444c0c0300203d0314000181c46481c2c2d21803000040048580c002c0d0588900e400b290f16400d0301202030221300c00d0768030003440781c2615049000c101e8010120616000204c500480c00149440010168001090b1a0112503155a01e079400c0c03460b810712030301405d425544c07040310b000e038825034043c1c680c40b02c1031460001c015103115103041c1481801d00c503040c002240880c8802c2c2004420f040340389016810001490000e00385070b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 635368048 1250 635366798 635366803
    0x1e030c13060905130e120c030c1005180303060d060509030d0630050319050c01060609140306070e06030a0f1a1017041716030e0103060603290316030302 67
    0x6000f91441482e103110700001400d4540511048503050201520303400c05040030f26000c42d0403854911003140014800c002e100e020030842c62103500440c2002140340d0802d40482c1190401d6000c489803d0740080007000324586950760311424190307010000081560f51900ea25086004040303ca249440c1400d400140300000400810f841001e1010450341c0d2600300303014035440d8425000000c01c1a001441482c0303070792001400f148a01007250500c90b140400d10000182103480c42d81104011414440017400399001688406d140c030702c42500208a9030034598030285c011340c80c4509562180a0001c0050401075480c3c10442a90f52201c40c184003140e070910f005412041000c402e04c1c0240414841d803c501842900d5041503841481802005901d8585a000c00c01d50301060100c9468070410030186a00d50300c9a000014601981d20700c1030400c40500014151600341e40106c04150400318030410071b0140311f80341c01000e507926990341c1030480031078042030910300c1020800d1540030b60498000203040d0013 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 635369298 1250 635368048 635368067
    0xb151803010e160e072a082a16030204050402030304030c1212090b030412030b100e1224070219030c05010623010e040b0a15090806390309010b0310021e030c1306 71
    0x70903548c0c1c108075a05c21041c0da4415035007480e00f205025182c810409170620394882d41d04140068152072816440751651040b042d9a60302c1401134105141c40b40c018440741c0d1a0040403000185005451245043c424910502002d0300140000781041c00c074140c1e5500030303400b0810480004c1c1c00c2c00d4044c4400e80001d800560703041d441a004445c01c42c10341ea603c05020820500c18040340400404000d11101c00601e809001480681584202c2a5503050344800c842c0182101307100b551000a500d040b0b00d045400e40300c040d80080d01070b2040d006800c0e8030220b0040141082d10007072815030820301c2135100150107402a4000790390441030f1205c0c00300b42034401030090351000071035072501e612083d41c640f042a91007208464117111900c00d85030f00751910f8000560720cc0c0c25800c0c00030310000c0321040e03940c040040d881071300d140f8950381d590100200c4a080500c0000c590403100d030011810f088018840c040c11801c1001c1d103500c0c0300000800510340c0401042030300c928000000340c0440f2030b40c882d00d01416a502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 635370548 1250 635369298 635369347
    0x8090c09163b01020f010501050a032d2f03060c0a030f020307030b01020708122b0509030901090b070203120c0a05032b0b151803010e160e072a08 64
    0x18940f030304511743e0300500650b8100c66019001242891442d00d80d84542d40350f113a4480002500702c0310040c111089200341d0848540a09607454450038464505410b605034640c1101c0f00381c9440d10451020750b00407411a500a05103003690390340c2c4441010403001019100b8407032842505c048248103170aa031503441058908400e80031282402d80302c100565a42608005045410030100507080c4180d60a1800c00905903c19000b18140c5190b001e90341c0584078200d4000700c40d41d10100e0b50103025030b44980070320020140d08007810325081c0d054001c65190741040540354612000003070100800ea2082088401541e004000d40e070301d6820b040b44480d403010720440714044440384810004550450761240d59041400102030b10f441140c010360280b542d4100b0810719500130100c0801400945080c0101d00d0828058006000041004a13548800403203507002045c210058a040200e2203400c0700f500e000350344410b0316001039220120005441e20343c86401c021300d000c0001c109c460700a045801807408000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 635371798 1250 635370548 635370553
    0x30b0604150f060509010c23160803120402120609030408100507050909040620030103020901060e0108070e06071a0f18070e131208090c09163b0102 65
    0x2011038800a1a00442d0066451082c00c030001003191600610003040080b4040c100b0443c10300c41030321001542c040c00411610b05e170b09000340c52000c48609210b481d1910118030764000061781448011030340e9000e00c0b5a040005002000407130195a10015003a02078041902103c0140c980351292640b00d8010344101411807243c1d081075482d0130454010390344950015501d003402c0c0100c031401c0103080325014106803032095030369242070f40520740343e51020340c5184e4400d141c580d254950310502c204a40140c3c4200108100200c4002d000d80e481480d0300e805c400c4510702141c00b0501c0700c0000d006807081000c0244075401c8002501f814481501d0002d100d0781c2039840311191035075002c0304820452506044c0540a0b003140c5424428104c0c21080560003001d064607102044010703a07690500f0f00001c050200101d401030003013190b110010031450800701c6040e5461f035a24200f8420320505960b255400c2001e0000d5030703058800c05e000380f00396181a100304c000e4108400910441090185040350201e90050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 635373048 1250 635371798 635371811
    0xe0a1718010c0503071e0506151309061d010c0905030a020d1704120c051206060a09021308070906080d030905060606030402060d0f0e2a0603040312110d14040c03080a020a0507030b0604 81
    0x581450750272007240602500002a0703010b03804100005041450003101d01c82e50700e1140320303600e1407084049803501d012600001094200c821002c2c05211060380014403c0e80b0401c0914016141c1030300d03401c2d03110761251085210145814140301c41d40035541118082440f414110300a002d4000550402c481c41036407008c41c0d502a02c1c0125807921400c5a600760004d80000301040f82e150349a008000343c2c219032102d03200b070a4485034800c0c00d003220355102e940481e4443e00f084c0f01950b42484520240c0180e41000c0040380501c1d038460351112401030240384512404070000782907444000490700c049003803290812200c03402c00b100c82c00030092005a10028825041c0701d041ca020010036022489100590343c5011129840400060784c0c00140102c0c10032480024020b000c803418010029a001d02c0c510154540640c02050401c4071200702500b1140c243d01d005200c00b150500140c03009581d00500f80660300c84441209900c2c244e039042d00103200e407195a8000050001050509000d80c0c0b0485052004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 635374298 1250 635373048 635373061
    0x52403150f04150b03122b0203010e070206070903023f0601080c01270807080d02010f090b1f1a0c010b03030316110a060e0a1718010c0503071e0506 65
    0x115500800400c2d01070f402503040542c8030002c403020345032a004c07c029462603101d0508403504000301070068110b2240d0007000601a0901000d0681d41c03204092000344001d207810400100b0400c124800a03004010144102a41d40200e04181c10070300c025004204441442c0b044000140c1147d8401c4e5205000704c1e07002040c0340340c1c08961145071420594601e80c01034a0041e03401c105500314150b5454038141e488001503c0d0700e0510220b0000c00c2058007502034810301d054040d09441c0407011490611f0b241000300000206510850b070f80141e086a03019a80c01607204502c8100e000d00c0e000741c4451303003c4079810030300600364400a00c4205e903000020721a0520410034182d407404143c1d903441904403d440d048018920503c80021842c040008403606c00b086511808111a0f646508000e103030045040c10041c0402002503242c080903a40c9141d04d452601804140300c10500000e0702d040002c0da044400c00c1c041d04000381d030816900040e81e031540390368031465141660b00c071100072182809080000bc88 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 635375548 1250 635374298 635374301
    0x12050a050d0801060c0b1e040f03140a0804150603060f0f06050a240c1a0402090906010b1815040602010606260a020a0309050d080118052403150f0415 66
    0x121102d603121403020000b6030380d1b4403203451001043c402190310350401da14010401c0402190149014140914040a5908009110211880c4007101c1030508200d0488802d0340b00580b1036204d0f801c1000581c10150321104032002d00703002e42c005082e60f400c1c0401d4501820712035102505c05055500c1c03c00c030041d81e40d8140003041009200e03035400d4951860002a100c101c000000703c10806034581000340c02000d81d0b030001904000700c1080c554100c15010030086040407c242500000104020b110540c9441d00e09486032240d541c440c2410010528840d0040d2110000f02c8034603040c1c0820140c0341c0b91510301c0240205003a00c20040021800c003500109484100e40c074516481e1602c0620045607151500100a944000495030070542d0f15220803020034014011404140744507920400300d5490720202c00c3c0907410400d2a8070800c1d151a09121003043e8040c2903480310a48914410414002000003a003003507003e004206044142904010700c0f10741c0c40902d907100328458200054289e480c0c161860 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 635376798 1250 635375548 635375551
    0x30e0a11040e071d0106030b190302040b030c120c030d090e0403050708070807030c0308061207120303090c0f090606050901020c04110c0102040e0402130c1205040501020412050a050d08 81
    0x2410605240c00140c05420315411a00111070600e044443c200d64542e084820410f6900041d1a62503804c0010b01103030703074140103200c1d10710011103010300c001c008000d0b0b80307091808501c8001c0c4106e9032110f2072529500d00f40191841c0401c003d00d10f9480703c3c3d600301e10f10384a00140883c03e04c24020386045040180c001ca412100f0742c0c0300f0100f662120385c0d580c0d4040ea900d44c040d45d0b050325055018400c2d140042c2c0160014001d10f0300ca65509a110411451b009d401c094024260621031507000400302400080080c2007c1150501c01400802c0c03c26402e0582c0104001707079002c0c028440141000ca80d00300144a01d078100c849001e01001960307a106000c59060290074070080c01038000b003014400901d4030750064114080a001182d292840c109482400c9074001d03130008498410700020801035242600d0040d100c3c0b440140305010000f0880f1001344940001c2c100702004075910030211381841425810b9502814603040301ca0883d0300c0e10b04000c3d507184030035842250307603208004180144178441e58149 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 635378048 1250 635376798 635376803
    0x612320412080f010b16080f130902041a0d090605011e150509010c14060106120e030703080c0706091703010512120f1c050103110a0801060501050304030f0e0d0b07030e0a 75
    0x1079070917402d02d00b00703010903444030741001c24071032040d50501c01081c5143c0042c01d5510114801603502d410398806140444019403100038021700c144001c0000d9a04145682001406512965500ca0740800700c20004c107640100a49160725210002c20f40c940d4450280e070011400140390792f80740e03070f6030060039000f003d2500c4154006030301888010b00c00d5001d41c82c3c0d4084244102071404000700300301d4a4a140a074264848800103078034a450310041c68191040450f200d08003009145040c21540b000381c00030101510140c1111800280981400340c0e66008511042d4000f5030b4202c0760461410075442a0001c0c01050301c51001142c00909030100010540e214501104005041000d50003072100b040c0c005544007000644a40d01608607810184503d50103144200c1c90312038903400d201c01b44401d500054001c640707070303038901201840b0580c1c102d0240c0e68419810b1610b0901188107900440c0c0d00c0b8041100c0c0c0340c0204124070319030200f12401300a540700707204030b80c1c1c00c100100400605541d03030307a40400301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 635379298 1250 635378048 635378071
    0x5041206020a020f010e15060102101505011b050d200a03020304061103091e040608030d0c110601030c0b090604180b0301180b010306020304050c0a06030b1306061232041208 76
    0x341f0002d40442d120f81da4402c0c0140141c502d200310399102e0a041d1400b540e240c500c01c0c034180c80c09000544e00700800d0f9503960810015240b0604044c1c6e61035079500d9000e180d550034815140602007607603c03101c2001d074000a280045d1a40710300c10b840c0c040e503030750420302826011800c800d0031051034003000401c1c2e540e8580010501540c0200c80f007002d86901c541c124501c0e4000361500d001080e540350400040c480035003000c6001a0000c2002c000901140c4055040995038100100410100ea2060b1030041039502c1400029030740c1e13410f82c0020300284981d41c01050382448501c4055808941039102030365944c070590003446065401140158480714040f401000c1101003801407001c207100f03501456025228030202c4061620b0b04000403189002c82e07200b180000c0c2c0f140e510b1007030307402e03c1d010305904d5241d01c0d03405005090a08801503d00401c0100340e907103640c0d5400e0680d0340800d03103d003008540700040409165004101200700c1e03040000f02d81c10b44010b104004101c004d03d10403e0440e100d403070620075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 635380548 1250 635379298 635379313
    0x90402010e060f040e01150903120f0e150a03050901021312050705092806140f0d350c030703180f0603050f070c0309090b0105041206020a020f010e 65
    0x41d2807000c1804141a00710744140030841c148000030001300040d000203180c0040661501c03005081502403010361030108040304034204000342da01241d9a000e0801401c0401c260703400403804a8048402c00c0240e03520216000517460110040c00062909a440303036824010b03030750781000d010b00341c1c415540703103090b206481107040000c2c41c0340502c0c0380111886981074644040e0b07110005a0b00c0c0d6001c5e9150a440d02d8400c401c100f00c24401a6000172107d103450042c09010300c0c0603030401c8071401c1113101a00408039101e04155581c0c03040703040000585d000002c11414082086101850079620225400c0c002280138a262006015030507aa02c152450000b50b14104007554102d9400700400f540855101c0760030703000b00340c2c607408079008030190000d5600001c1a1611850445601c40c029080b1024428200c0034900403945c00744c400c100b501c880320004a40f0413201001250541302e01d61040d696010b40001190410440c1e070010003040c42140d013207900500c96020364500303c03034800c50381d98041d0b0700074017 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 635381798 1250 635380548 635380553
    0x15010f020c100e01140309060609070207140907020f0106060e040b0d0b0606090607061410090b0f120f0102030108011b05030c0403060b0d0501090c210305040e0a0b030a030206160804020904 83
    0xb483d01030001062405a1014203855000207460704142d59046084c1c214008000c028101354186580c0032145100801c0014504404d240713107401a841c0c40d50003151401c0c005800d60340200003c118002e01e16008001141c0d071200c00501500c0480b82c00c521036410202410024074012101c0c6510680101000c20143c90300c0741040441e03840402d01075042001400200040f404500c0313015030000903424408000c0c50801c041840b045c1d06600800102d0303240c00201502521004440190201d054030f60004a03121604014585890005044615800000041200101074104545400300c401712a401e0100c580401d5655010442e6940b03e115801e01003040422096000100716030320183c041e0406880030341b1040c0c02d40700c4c0000d00381d402d00320141003080070703030481154568980010b08101c80050420391340101203214510075442200c141d01d0110b15468155408802c0c0f01c50000d0894048000c00e14000c0c0d240d8a044403040c00d011940382009140c140100710f80c911966004101c404c2640e03456 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 635383048 1250 635381798 635381807
    0x6010b0f0f03100803030411040b042d020c0109030e1f020a03141204060917160803061504031214030408090409051608030c0c06192615010f020c10 65
    0x1400030301124203c00c80002c48032811304c01103014034040e08280018415803414042075541c104c5165000d680740030580d0000e40003116582510b601003002003d0013941c441c0e5417401038015180e541d0381c40d5103005818030070590890410000e20310165042004d000034410f22a5503103109004180240c0c00503641000001e209180400c0311005400c800b074280b00d01d40d40c030706040c6c081c201c0d03040300d48690f501002020700c60000340081044c1c3d039000c94145440800e8044d280b90003003110000302110f0000c00815020341e2041810003901102526a58846941c3d060003041c05034a00c0300341012540c500303004070552822400b10713807142c1d4211400e14a0a0034420511000300924a010b58440c0140d001ca402e400700340c12035100040c41c401001b552510031580c01075081900400788288502000c010101c0c04041e80380c0107403039a800e00d0030201c03110340d0080e2a4054400d0703140c180c40d52104008041080209200050100d841800e031f07a14040491600c0e4281d0340d071400d204c20b0f190320014814000b841903104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 635384298 1250 635383048 635383051
    0x608060c070606030b100303030b12030919030f0f14010c090302010f0e100906020f0a020f0418060504050304090606050c120c031c090203010c08130f0201030b12010e06010b0f0f03 79
    0x8560020700c81365203071100e0b082001c003503892143c104040c40c810024994913008280f104103040394071203440910007541030b80c3d900c140011207000f040e14004070345015500641840040d0b03040588030140000b40e1030310700200c10014108543c00716034041c80914040d014411403004114176118460f040d81190010740c0d00b41030441600700bc1111404d000341082e16500c0803080f03c0380c001e882e520b200505045010b41040d100c1085a40660702680d10800983c0d103948030305154150070355000442109056031240c0002c904e4101402c143d0811003800100100080140300329012400e0411980d5181d510031111807045048615995100300040100d0b02e01000060000b094924112460044c08000350415505402d08007031403071340c1d600744030015030400b80621051900c00d80b9020640d8642a0a5981840d504250207401c00c06111515811a402984803c5070104010b0090410403045011540030344540301410101d4015840005031100010081d0b500c180c0d0045c1d01c0500b030600312403038100c3c141c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 635385548 1250 635384298 635384303
    0x14070806150d2a091404060c02011401030308062e030b030f2a0906011d060d0501032301050601090e090c060a2a080403080306040e010c050d0f0608060c07 68
    0x103a452544000070005464650381410001d46101c900003000d541145481056200d44140e50801174041140070341503000743c0d4000d40c862800a00f508030781500702e0040c180d075107894110b8920180040185030b040b55150344a6402240e001902076450404900518049070100500d6810b411001c0d00060003034200c00707103902000d0110b5040b000c0b41200c103413901151480c1110b001e858050031419690380019001c0311020141c51081031f42c1002c80009020356441c58580d0003d910000040c0b403a90b666030110342006030810310900140d40c40c0c0c108070684c841e400000107042c107035000b0803204925042c05010710804058480615861400c0c017071050500008103003880034007409030b114000746d03a0318010b0803510156a603961800076208141d030148150340c1c07140340c000c004039600c0e41000444040480341604d901c02c560544a4440d00f010501819900340444519401c1150b00a03190340c0c040054003c0f854103420910084010059500843c3c2860042100300d0b0403003000200ea5400c2d00004003040e61 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 635386798 1250 635385548 635385559
    0xe06070803040f080415030b04090309050105070c05060a05040806070c151109030a08030108060114101d040f052212030c050f21010902030f0703050601090e10031407080615 76
    0x2800356130b40080036800b50300102201032107010f01404c40c99140c412910381c1d00007543c00308844550b5440c09042903000344103160400900040003004c0110130340c4a8402088040c0c1001d8562034001c10103046034120740201d10075807080e100000c850511a40b140c1c10f165820068410451500e894098041c014080980c01d200d1410040c01c80981c504110a40b10746006404040d125418405a9410520184e0007889010302010307665945030b4500d651136045402d10706100c5110072014800401c05c1c0c90b42c8d0104e40e4013510341589184c2c017440070780109200740002c1c000b803500303000ca11815407080802d103040030b00110802c88d0300c412004d000340c0c40744082c0d101d02d0500c40d007820f0242584210950194000100d40010703210184408a80c0d441d41d1409001a10015400d40c03410360391401d00c44070028200703010180c13900080341c081d0340540c28200290581e94050740700c600e0030a910721030b203188600c01261400d8119034043c16241002c500007041d0740380074001c1c1480b51145001c060010511040032640034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 635388048 1250 635386798 635386823
    0xa110d091401051215040c210518030a090905070201090515040c030b041203140c0304061e0e010e070b120a0506012c090601030608071206020c0106240e0607080304 72
    0x40c03042090600c103002c10031840542c0040b110078402640c925003805018451000308400c0c0c8d1000207032070903c5850b12180002199641c5120040c030306841042c800c4900d00000031402400c83d0311210365015203442d01424045a224003104a080300c0c406103002d001a003000d08030b402101342c072120032600140144610490305889403a45111048151412681d80740403003407138643c8a805000b01c04248554654001c111b2604400315502403000800013003c2641d20007c00415866440b88000f02d512519402c0081c548801d0f07e1078020700034481240030764403030390b80c0000c0c03008010412100031680800c8400c4d042d8407401c09840140c48060601414494091540120642036a04c3c0c6682d80384100341070007140740c086051280c0810003404942c10035044c0403003071044000c0040c4c150110384090382e801c51a4085824000000e01034040407070220750902c880010400c032002105c071400304030440d14040d21040700c1c0082c0c6180c0300c1da1324030640080082c400040031520340805554004e0184074242800d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 635389298 1250 635388048 635388067
    0x606100c030c140105161e0c08130b0c101a030a030f0210110306100c05030a0c06020c06090f0d17060f13060b0301090f11031305100509030a110d09140105 68
    0x7917503c100c85041d0352085440740260080e07401824140065800010700c0c500e0300b103d840080c00342c005000090000c09000a6504141d500c0c0c606000040c0381601031603489625100c1c01c00c2e00d03140300084a007185c9080194070003000e80084207259446d80014010442c425032a5000d0f2a1644101460415400f0f800c3c0c480c40300d40703c40d010300e603041841c102030780d66245025400c00c201d00b04030010348810054452000e0001950003c2220300c49840c5041c000d00000e10761401c00040d2084040c001403d0082d8820320442e88400501c5803681d0040c58255035201c02c003000c0c100d5004501c0d03a52001c1120301400031070002d0a14603141020707100e004c0c00203032810407000e90590030b41d00d00350b104c1c0007510400001000800d803144540d01348101144024000600700c0113031a2150300000c0c00b81c030102003000c0075801c20044108400254100a0350090007645070141d004d0340c07030f034014100110220b402d402d6414034201c0b0129a4220500044d15000206402d1005c0507082840d526001810b016081215800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 635390548 1250 635389298 635389301
    0x5090f0a030302071424090705061603110d0905042a11010501080102070c09021318020306030111030402100806151314030d05041206061d090606100c030c1401 70
    0xe046001e078034050782e11241841c00c0c0519814030054608150002d0001104119410300300e9000301c00e28600745942c40c2c956a001d241008505d910080c0c0c8080000364401e04080c4642c441c6842030300988408900d4500010810344943d4549000000281000814130203440d090b880346209003e40d1010360b006540c9400c956060340a807003c0b0f003012961b00e0b4107101001c2c6c000d01a0b01c0c00750400c0002507003441415681c0401d41c03040750243c42492500425121403204400780740c10000d01c860b0340c0c1c0404565501c5035400c025401070315424000c0d400c010080c20500103c3c001c5034042d40e070242c03032801401c0c0310030b0003241c003060b014140e03030350107814000440c0914442502422000c0310130070000101a18180740000004041ea100078066041548000c1c440741c0c001003a601100d82d02030801c0b800f8441c3d45082d00052040b0b0300005416131401c030102c06040d070035084081c81141d48000b101c01075200d290400c410038000031075043c0041c51a481e10030021b031040d0641d2540d1440342e42a1075010840c03400765070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 635391798 1250 635390548 635390563
    0x3030519020703060903020a0501110f070602030a0f060e07030614180411060a02161a031f051903022701050609030f06010b0a02070603020c061602030c0a0b0105030114150405090f 79
    0x20011303070000d41c56005100e27080c80f6000005c01e00d0068945881c090aa95080c01d0140c1c0002070001c603400f000149200301c032900002c1d42100a1402008502d403100b8151900300000c2e00e80030300003840e00c10003090ba0042c0101c87d00000400a003200031242300440c40d407500403001002121044149408403005466860280880136210b8010b0000c14011030003d21800205610400f003001000030301c03651003240e8a040300c0d000903903480d4002031801008243c03142c82c1c3d01d95200a41240b001e100307181e03040c01404050b0b030079a442100c0c003590000043da2450024401078001070300020462004210b41e18001000380100d140140640c0e00d415080300710b69081c41c070240d001c004e4000002410003031882c0e05005410151000e030804505094099902a41c1c40d14024a0342d1000d003940a00200c03501d00801c00e91701c00720305030800c80d05411207515080303182d07031028807450740658240407540d5040001c0e02a170758801c00181e84085244070b101d00c01c11002e060003428502035801107051401c250300060110b038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 635393048 1250 635391798 635391803
    0xa090c03150b1905010e0919090201020a05061005120a0201022a09010f0303020606031b010e0406030605160e0409080d0b06040b0a050909060d030c0201201e0601090204030305190207030609 83
    0x40543c038546030000d822080b40206c0f03241704e44020420080c481006040d02d01c0300d080207590014141110f440140c1c600103c14001500303034402e4008110040c1c014501490903180d051310561070000c5605961a651408100d0080c05600702e25030b06e43c5081030f900301c7c6400c03c030b02c0284071071080700d03008020581d4023100382c201c041c141851420038014150108807003904004150000c00c0d48130700502c084842045a028200c0c100700a240003400700355a83d400007400303140c02100402c5070381464414024000101c41130071001c80c007080341c10200791909104880015070000143d41c03410b01e8410320000106114050325a1180080c000400d0080904018103210801a200c2550fa00c0800c420046d036281d000300468441e040c018403241c0080d621002c003040036a4282007040914207c0030070030714854106008582c0f103114007440d4101804004d014101d0030b002c14070030b44034281d0b210300403075046c0e1260f4040034000c1081084840b428803000e01450703011054510588030081c2c0c899450034240c8481d410203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 635394298 1250 635393048 635393089
    0x2030309010518060112020f090106020c100f0219143f040311032505090a06080c06070305040e040326010510050d0b090109140a090c03150b 62
    0x8000000e4000d119083d000b0305515400c5044018000b003059071400705020703000c0366071000c0e50842c0841d151040b03407541c0d845009004450541e1540c4000b55140302c000710359031042000c0000702c058907005540c0c0307500201c0349034050400518407083c0c0582c1100524412039220b907000941c81c1400406216103942c600804000c48601c12485c000e0400c4401000d000450350320103224020143ca4170036040301d0859511448100d0201d91007800642400c0c00f0449800c0b894a01040401050220402c40400d5420031a04048643c032040084012a82c2902404242e51f01101f03458842380307000c902800a41d8428904030f0302c2c10341c07103080395030110006840450100d10050300031282060b41d6800402540841d00001c0c601d98544000561b07c1600c006441c001c0c03000014498118140075008089640303005030050f900c1e960348000402c000c040203080300c140c0600c85404180308817024041c481e0700ca074010031180c1946007580c44a2024040c0d0140d404545c40e600c4074048003d031a26041c602e4481c0b42d5000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 635395548 1250 635394298 635394301
    0x20c090109140c090901030b040f0b191401080a1e060c030213090b0109050103150305030c0f0d080f06130209120106060e010e330f040305011a06030a05090c040c020303 74
    0x3045a0305000c041d0540740300100130b1004040e6034a5102d00141142d403c45860115900c0c1c03070a00c9007101e0405c0070050b0080d144501000011020152203881106100408004c2001c40c4600004120310a01550085820521031400030800000007100d80d500c4600c4c80c1002c0d40740660341c1e40d00301c0d0202042c50000c81d0f00800c41007003242c010404c2c0030080031101818041e01905800013082c2c2040707801200e040c96034880908480400300c50703140d8090340d8000102c076614182c290750243d656200311a440f030940b10303001400c1009031040344030074024125040c6841003a101d4008210303c180c01e101006d1007440d800d11220500756241441681c042c036814000140302410140024158018010300d1410301c4469007140d0780588035558040414452041050881c3c08a800030100b040d841a11022091201203076078486525460024400c580c41a0020840c1c005010b40620384600310000d100d0713120209000048440c5800e80100364401011710903200c4407050103000404840180709100c006074070100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 635396798 1250 635395548 635395571
    0x305091201090b0a0603081b121309050108120301090903021c170f0105030d120204050406270917130b0318190203070312050708030a0b030606090601020c0d03020c090109 75
    0x390320907000004d202c2c4c00c1c000c1074195141d1100360b120380041c02c84059410034205c1c0301c450091284d056400c5240c1c14442d6a4035910700c0c58404141203014841c680d610700320000a010300002049550031040d11005070441c0e02c2c002204008200e241e10070b40640c05059400c01c2010680300d8158011445600d880703401002100d00704854100040041c491650203800501c5207940c0001c407031404001900c0c0c90b44009014000c030071b0290284da40034503005800c2282c0890a01c0d03090007101050744000d01c026181c0119016040c060f00e8080720081d1a61480030420980e68003043c000700b0654000e600c07008403480d501d4020440940c02203401c0642c120001d5082c5c4000c00c01400080001d615509201e0341c0d2400036000207840d8012884000d02d044a04865020500c0c0584140c4d8450b40d00250301d584c0300d1806c06001c8001e80300f4804040e10078019600004e010b1310706000c03501d000f104103900402d0343c41c0e044018401d00c0620320303809070f0542c82024440c85860303581c039402d07501801c00200003155210707444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 635398048 1250 635396798 635396813
    0x1a070c05010c0309020a21170703020f07031a060f0a0915060e030d030c0207080a060c030b03010203240103140a0b01090b0f2b09050a03020721020d030509120109 71
    0x1074402c4201401c0c5488070303000d40d941c04000c40030b55005240700000700001000604800c020043e005143e4220100000d411440d000042c10000d4029000c2da4003440540b10701584480e640e003c02040e01504000c0520084082240c0c0c541c005005040ca0298085c044001010441c0035405591003d40f42c5030904030b02e64026010900030415410040e03013041915000036150001c031880709040595900030052140e10030402c0c40c1c01814450140c0e54841c2c070f40d082c1440039008500c0001c0c01709041c06070f1146981014070840b4828100411080c182032041a1025411200311907131604054035003050b0b000b0b030315034901d03c60b000301500e01c40090b0614200002600b40348490340321010b1704400348203003840700c0d2030801100d141004207a0540c1c040420502031b41c0744415a5525030852134a002607450070050b001540c050200d02a400710303a4065070b2107d224071800c20300e0250411003c88070402c4401400c0070050400f00d40e2003402c181d03050268160205d40c154403180c8517480313569141c41e400f00a04c40714 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 635399298 1250 635398048 635398061
    0x91206060f100903110307030f0308010905150303182b1103030309030d0203040f170307020f070501170a020409050c18010e1e01090803030c0d0501050609090606071a070c0501 77
    0x70307242c03030442084480d800ba11140081c4006400e000d0080c072840500e03a001d02c1906e000d9640304400b01d1001419090040040e0b00c24081c50b0100d5242a011031131100864080001030000100114078140407911a8a0130203010701c0201c0c0c000e01003051412400c01440c0542c0181080320800c0c0000214505202035403031040c0d81100d0081d08108107220102402004881206011643c05a5241c0750b41c5041041910705d8007001c0d103140342c030501c10000102d0490066018000d01c1e402c4aa4a016190600d51140c01600c99a40412800000c54080f500c010382c2ca0340d44110104001400c040c0d9035000d68098800440700c1c2e203c000b1002951000c64000e4280300005d0403000e28010044400f04804144001244d46a04402c401480010216a8402e810002c003501001f07054985034202031569140c40e410400c9658406414007001240d42c0c20007105440c1c50031070086c8a0401604c0b0745061000c1030780301c4a4142c8803914848074000940d05001400d60040302540e45407141c1c6810303400c0580c02c4521 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 635400548 1250 635399298 635399329
    0xf120615082811280621050f130302160b0a0f050a0806150d0906020306030c150f0c10090c090f0209090a05060d050601030b07110715080c09120606 65
    0x4031410b1420128038400048601c100c402d546040d04090320070005243e00003040030f4445000726919021038a664001c00c42c800320420204160040200e42e0184001e482e1300321040700c0152900b0001400c180c8918803102c144600900640701c0c040c18480301c01180c803c07141c2280f1007229000070071030b1046611504185100c007a03864054100704817503400401d1140046c001c240309400124403030b0310168100d404c4860354040c81d407040010740c01c0b81c508000650811940343d80b1a00412032400c4280c1850440b41382d4109500c2d48440c5402000c8090703079020b80114110010f82c2c400d52814610003491031042c1030320103015221880a0f02d2900c4444800e940c00038451400a50060140510b641c80300308607203412400d10100803540360385080200300c0c0c3c0e6004100143c00e40c0320f00d1000005100034140c2e540e0250303805549100d5983c0800100036030b1801503206441030420401140075465201e2207501e5004199104c2052a00b14040001111a81d10300b04400d040e401c06824002c10745042003c0120144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 635401798 1250 635400548 635400613
    0x9051204030b10150f0323100f05030309100912151505060d05090316060b0a08030a09060c052a01030e0d090e0a02070b011d090303010f12061508 64
    0x504241114603003840044e004000e2181c0b0041425030107002c2e80009070400c1019071004144145804c2c084051802600c1d00750034848004404214120782004c5001614400f400440c94908458140041d40f4014110041000342c01c19020400c400800001ca045ca80a01844280c0203018420442280c200b80314080c1c83e840c85800c10402600c1781c40c00d03142d60811220f80019541c0c0c5550459046219861440b01c07400011409481003081a62117031041220541d61030385407548400304642e60344142e0f42c045000c2101c0c54020031075288103656541507030380b007241552403070302c1d6a05203c0d01003c44462880070f4003081d0b03030001d0400d50307041c030441c200c00070703400c00400340040c6281c0c02600b100914016881165000d1000070050202d58046510056008004145540e550324524030600340d0145110126411440416034000c4d0020649040c1d8440046455100740760200301002c0d000b0760030302103c0c2d464550030320310b5540d07001c1d994803001089a5406045d24050325160781145107101c0d1500f01820 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 635403048 1250 635401798 635401831
    0x11070314031c0c091206060e13060609020906090603102318010e0c09030f0d05221d18071712040b03070507140d050403030905040917090409051204030b 67
    0x560052001c01121114074001200342d40d1341c20f206c00a8403d85d001031203284440b400780031340702d4050418043c280d40242d8013001890b440b203114000741d2103a109519800a0140805039003440c14500440e04101030382e0100c000103070f50310203c58818118100d031424030030900309001014140b4070101e6001c2e501c122001c800d1981064501035003040e001e40a00d4451501082c030700c4c500e440130000c00c9403004450301140e210300c0100c10018045d50042e00c80c0d12000d001c418043d00d002071a42c01340300680b181c499400003d4405140804172103603000300315a503200c00e12103016540700003c1c809040034060040203264a44c40c0d540710030f0718290385d017010302c02d030210304000400c9209200f1040c1c1c2d80283c21031a0256440c241400c2603c3c02040c51454101d0b40d00817401e40c107000c02c0d0804018000c8910a0b01ca22900c030355160b007000119803562102402c0c250403c80c0c801100700f0300c10001c0a0602e4014070005041d4060b0329440d14000b031a050441c802800024240140000d41c0715066200411400e8903c80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 635404298 1250 635403048 635403071
    0x402010c06020a090b070b01060e01090f060c030e0409260726040b19030c09120f1509060501080f03160f02030a0602030a150f0b070311070314031c 65
    0x10080349040161a035030380440c00380781052003500b00c180102454040c03252900c10303c2c20840c0307203103500384249408180c188003e001c1c1035000e5803d02007110054880c05031001d113054000d03956100c0340134080341000304001840f40c1c1d5907290310680c01c40324081e03005800c4480c0c41c880710010600d441c920400e00e51109000040c00200401822406402d02c0000b000344c113040d420b03610f03459001d0b035040320180c400d0104044402101080c91751070161015641441030140d05481a102c4030617500a1240c1703020801100c1021400065034104410f2180c1d450b0042c004095401c0d10031a05000b20444480b078840780104216001000103d810081080145240800d80100c9050081e90508018041ca01d03511450065507014014103507040d412100c155a6480c00040041c01000c8c80440807070b454081300008030740d10f10401d03038250076240e4011113180340014507207003500c00d046009030000c102d10030300c02c0200000c0d045c00004000003643d00300550b01c03040f101d42c02403511100100d4107130588d850015107c11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 635405548 1250 635404298 635404307
    0x403080a02070501300204050301140a051b0403080c1f0c0216120f060219030c080709030507060c02060c0d0c020901080607050d020708070b090c0a06030e0616111f050a05040201 78
    0x203000c0c50388240c0c40c0888009172002c0680101c2c0d1045d13505518100380c3c01180700c540030600c1e1003115498401c1085644020003000491040003140c42c10090a010a10004103000002d048503049642120101450413040400c1d1161407484403500d20386035451440444d80400c4280d40c880d100c0d014402c9001d080980c0c1c10050000c1450107071070080c90000003401d100050703044070901000c081381220702c3c03061010040c0c00f03095100d40140003d60f01a00045c0311508c01c46140c0300790b0750b001001c0c0080300c1c03611030304884070741000e20161783c80350381040084c600d150100150914118a03072580440242640100003000c00141d00442e030b45e4020300c0400000580c400116024541a8000140c49421608000304603000305d18000309031604040038041c90410010b401010b442c000c982c5800c016840c2d4608034103907816540c0f001c45903400740010038014004000c221605465a00d0f0184100503601110303071420281c00c82c042580d01804842d40302c2d0300058051268040382030b0000340310b40d05080d8002030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 635406798 1250 635405548 635405597
    0x80106030818060d0207050102210f0a0c050c011d060c0418090c05041d16060c080903010e12030403030f0e060f19020d0e1009030801290403080a02070501 68
    0x1c0340311001c40d0301c0c0000b0395a00402d44092113126075085481da18a407800d54001e5220340c8800302412503221800c0c6200c4502c61070355100341d4625500c5440c68455803096405401da40480c2c605020b400e100343c80c401030f130901c1641c29035105280400005600c260b042c6051440c09441c003205460208428407021084202d030101119a0000c001088030081c100807080c4422a00300303d13801814000c0d501d000c6080c0802c02449505081d0aa4a0a080b12002110b071402d02e445220007061184071310a02041d0128094038513443d020303001060441e0040219802c0a28902c005800a0000b0086c072041c158184900018450a6241000040d514904940d607a40700105810610345556000400c50070250a04001c5440b00d241c066407a45800180c82024003042c45500d029446014000000070300103000d10100160151240c492507401c00c1c01440c500c0e411a55210080c501c07400914015081d0349005100441c000c0c2e101c5521760701000702c001c0c1021003d602c0681003200c08000504c1c11301e207090580 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 635408048 1250 635406798 635406817
    0x1413060c02031c39050d020d090f05100501050d0311010b0d0507031403040303090e06010c0803240a0509160c020d1202100e0318030c1504150311090108061903030f03060801060308 79
    0x172512000e103411540003900c0f07802404c82d1f940b81445503041c200402842801d0540d48a40151081d181071505c4800840d40309206086d80081a81080b01c08039010701c08055416043e0300010034001041f10118a0014017490221032aa101007001c005001d14400781314089003440001d5464180365445c01412071095014140581e603171440030484d560300400c2c018186a60109850b40c580c5016800c460808080100c405003800d4402c02c0c40d0154035214014800b556001444001e060711010980d89000044035265030501c1450301c5540c026907203c0c05104802841011034072400d00b000c40e002400e10059000d4100e9060a03c2c03540f4074000004001e49440030315170103243c050508041c0c0024035148540e020250015100410303a000021103c0042096a4407020040250040700001b101200e16031111784841100901c6200615840f400186030820402841c00c600c42e0328920346900a00c4150348224081013460110300080ea4040c083d840043c01c009000300b00c283c1c65030310b07002c5180c401e14510 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 635409298 1250 635408048 635408057
    0x20a030801052b0506061009031203020328060302041b080105011b1e1406010b27130c0f020c0a09050901060e07030e011413060c02031c39 61
    0x8a01c52802e0400422a03e180e058903c1900400701c0d040c41e07a10784005407501400342a010003514040b0380613452085c100c07688264411120480746000300c00035000030305035480600a10082404115a46003604c1d8004569a000540302e40340d0310410080303501c02d1f0045189031502a10315041c441c1c1200388981110303c207080c1072035200c55074908000011403038031004051315402180c0e0074000c080c034409003900e544110382030511044155100c42d5280024410700300c002c007042005d180ba40c0d001c2d05a03441e00011405007820a01006000549071a20345440503c0312a91860b5000301198489944071010069002800401d138070a008035460701c1103405550751458031900403a46400095211070000c00b03130421001d0050920801c020050308003030804080d650b00b012203c08a00740600140e07400b4041c01c1c88008809001a1303202000b8040c0d9980d00c0c1c066010611040050004002c1980000ca000300d0000552100340000080e00c1d0004c0040c1007403000c1041841c000310940d20403401d1000c121800c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 635410548 1250 635409298 635409319
    0x1511100905010b040612110a032a03080a0203030f060405012d1508010e22020112060e010914010902070305031f080a12020c030a030207090b040612081306020a03080105 74
    0x3800e81c007400d050fa02e500d4000e0b20f0008002454120140c500c0301881c401d1740803001028142041103040c1c04e0a000c091f00402c2002c0c4823150010181c0d60301c1c12040785882d070030074265980f529480b050350000c030b9080015800c00402c208800e2803c0741013540c04030080740e0801142d410461441c081140140085084e852082000b0900c08000000390004040440800c1404154001c0080c000c2c9028031070382d00310344811408520300820b080d00440f0b070000c0c41c540724401d007156074004503880424807081910040c0d075480e010600807044225517003e131440c03e1010800344d20403504840b440d8416444504034034410311190b0006903000c41126003000814816961b44002d4074580b400d41c00c21503004006910403e001c50041000384007070011840d5042c2c00f50342d801c0300d041d004e00d512407034035400c000c0042c0c00c00c080030b21415000380e2004061020203480007600c00d4503000c000e401e47c100c602301a19900000314a044400c2d025020180140203244048e000d1425541e8010b010302134180111407041c2000301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 635411798 1250 635410548 635410553
    0x1050612030f0d15060309032a02090402040906052d010b180a0b070b040c0e060102060105120f19110d0c0306270b010f06020307200102030903100615111009 69
    0x100503401403441c049800301407941c0d42c9405002080b03034407c101d000c02c58403450307885c0c051000386140031118031004003003181e5420380d800c22910300e0006204982c090341d1540b040380232640500c00c00d807041c0c001c03a541500c098102100050301600c04000c4407030b0304400c1300040c0240619a025512980015600c1114221601d0001142200340d50002d50510401143c3c1e103040c001c0494010f0701690054400303100198840541b801e03102800c03036081e800750340040e00400007420007001280100c180f000544407a00403842c0c44508004564090a0b1000c10601c031901c140b009181c0b030003210308421101c40074414169510480ea17000540b00281003141c0d528031181200d50505241d038011000c5408500090b900d42c40c00b4078005100380508401c03480b460b0780c0400c005000004071081c1a8100c840c00040b2648101400c031075501203c5018114042480000341ea500c0811481c1c8070000c60304400719070b903800c100031921010b124401000400c04041c8011042c0790000c5404d02c90058221404541c060060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 635413048 1250 635411798 635411801
    0x615150d180f030e150708160501020d14010512010b090c0705330a0506030c0607061416031802010c03031a19080f010203090705090403020703060203010f0801050612030f0d 76
    0x1007400b405440c03244100300d0801d54003038541c0110910844a85944508103032001e0103c3c00b0303081c0700820f460410849490200e03005900904520304c585c4c00075250548031058402a0f030240c021301105001120010b0180703180100c1c14844208450000704156100d4000140e080785014104003101c00c0c0014100c024400c060003c100c00401c00e0034501444046005640b40a881c07244108449449000110390b0007540c0b409202d001d41c070001e005003408081c4408000d13065021880c2240c44907a03aa00581390502c9450080e44120f15144d561003e96020070000781c26540c08141410303400d144240031000607038104041085c4560103140008011005944002c42c1c610300900041d4000e41c0102c0001011848000440c2a100620b0541d140000010580e0f4280d000c240c420025540011780c061003d801c4c60940780b540f083c00b038411031303101d45e82c2c0b40c544004030ba100703070011f08140c1d915040501862000f402260307084441650b01100041c42c41e22140e841c1c0c000d000e241000301100294182c0040300e01d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 635414298 1250 635413048 635413091
    0x1b1b03020307120809160303050d0e010f051303110c030a03030c121a01020f0106030f08032a13140a0b0a0507140d08010f120201052a0615150d 63
    0x21400e0b83e00c48900b00f003006401340703204550b044a24802c41159844d00e12410001ca01180d91540702c060074070703551f0380e400c0d0064400b6044040c0344e59614072480003907000f2801036900a2003000d580c14010b085a050003814030120440300d5040e684058108460760b02c0000700c90882d560146400903030000c202004031058042800c640e80b1070780c1404d8010a4902c20b280022404600036003c40da441c00e00030021500b43c40e0240b00280c40d106102a0030404078504d24000c680c864030b03628400d1050240075100030383c2c3c1200000905011240460216181c000090701c0394040c20724003e14485042d10680040d1002d201e901800d04a0000030032003031440ba02490a07140034590040140000740c0108141a030343c0c2c00c880401800180c84c1000006101e070140149406403800800d904191001c03d4005541c3c941c00fa84060520340030754103d800705c000002285000281c040400f400c424288540c1c01c101c094440341c0d40314411401d03c5250110a003c2c04100d4010100c00000440c60805211240160004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 635415548 1250 635414298 635414303
    0x5010c11190807150813020609090f01083a111f05070503090a060506060409020f030a05090d023703080a0e0a02090a09170414041b1b03020307 63
    0x50106030501d400801100000c10303581d5a030111146140e942c80310110b81101c10032210041a411000300d1040140d405c0e0f03a00c0360b540040c107500d26100c001e030301048500000715400d0144000700300041c42140030a0241c00c000ca042c0c01c1c0ea180600b61800318a4420103440784075200544003400242d850700d8021054007078040925020307140395809040080040c0503580b40b5194882c3d140000107244580104152030140302c0800090640a01c0303a6100e40003404094956680032a040c80005161042c6000030086004001d2006480c2e003044826241a90700c003426810301a0010425135100d941d00003036800302d0014499581400d540c080000d00a41400403038060802c603503110810050580014a480c018483e803c02005015012200306440351100203000b5401002c4170049070061819030400001280903242d20911312020f026945680c0e07201ea8000c2c0390200c0c03113950354910303842c15210310361080017845071100121842e084003e00a202072045904400484800340081c10302c00c009844c00941d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 635416798 1250 635415548 635415559
    0x60106021606050f090f0f12010c09090e1c030e030d0f180b0a020a030f0216021e0117060f040f0c090e16140d0e01141602100c030b0402030a0605120304030c05010c11 73
    0x704000c92342c3e030191503450540c00c04152541400100c0395800d1042c40007403900000a042500d90741c12000080c19441c0c1800400c1640355075080161000038002030650705803143c1c000a111188800300c3d000d0300d005141c03048204408000c0040400d40454125038032502c0b46400603905c8110441c10b600030a52044648001d074408039112030108c145003071070700c4014006c5a030810000021b04031511507019813040c00380010344a110b029000a04e900119401110041c03500c031050700201c000c1004c81d100c00d0600340725107807112603059045030402592030140c1091005601d10340303020360410000801c81e501c1d440400405903019003030460700c00c0070350301e0004116a0500c108590340880702e028150711005000155203d0012690100c100c0040c2c5074420650f401500340c40403000c00000040c50380300720207414940c492a02945990300d07807000b188668568540026601d044c40c2c1070240342d041071a10041a40c2c0300300000d00208425400d60421580c00740ba0840017015a880c00c44d078143d00b2081c0310382d0003c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 635418048 1250 635416798 635416819
    0x207090614030105010b030c0d022a01051b0408070e09030906030a020304020301110a021005100807060206090c0103140109020f04231306060e060d020c060106021606050f090f0f 78
    0xc01d041c00080312055822002402140d888046c03160540c8015110103c010718108220031102c0719903009842d0b180034500040b03030340c88003d044d05524283c0307001405006035542d0040002641000c50001c3c20305180e1b030710042c105800d040082c0e50300d6000780201d0144145140018601000030011200e500f14080e0180b42c60303040c0740c4015030280d00203031400c0f0f00c01c0d420000840310320900b0f00280c5126661070b6006007409403940f02d0395002004050200c0785881c0300b92070301007a0306000700a810004c01040e801040d040c0f612224071400c000340e84807100c0c10903080000412140c05c2e030301500340c10749542600040e500d12840500c4000c0d0b05c190703031203c021080540101e5010800c0711a55140c01c000175220700803800010710705902128010301484020480c028104001400e0120180039403066140e4018a8010540d0042d494030b0003d0b440714005a000107100e95503101a048858000c014a040c40c9081010000403a4218050564801c1c09088030560b0628146c1d2800700b54004651701171b01d83c40d190f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 635419298 1250 635418048 635418059
    0xc08030c1b0604260a08070c0b09060d05060312130914060a0315060f12020102300703020a0f0c0f060c03020d0305060310050423150a0222181b0c1202070906 69
    0x2e1f08110401d4620400c180f0002072800d1843c800c881c80c58000400301442e003035074140f40b10000c1030b003c0c0105030540709800c440004404443c000381004070600c85810880361030011901700743c8400300603101001042030203000320303603c80c58100c2098030740c0314000780c8e00b0240d0003403050009c14140d841020014000b2070000f074908407250151410780d000380d09584039000b1848004044103495110305404956001c01440c41440c880c001d004150311a01c140c07031000100d40c965603a03c2203041c5040d141c68101d40c9080146980c031010400040c4840d040403003c081540d1000b070b407210302d84031004050548640c00117007550b9091146820303050841c2020002420300341405c4101d1f8045800c03901034420502c003410710703018000036a2100d41c0900d04902c0c2c403e81e600701100c0040e4210005c03000c0d04610140c6030600e05491040a00c1c003a001401681c400c01104982c82001e03140d0110054024403666070100421960240c40940d016420100c2292805c1c0040022440c2c0003050f031010103480c3c5480070200c2c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 635420548 1250 635419298 635419313
    0x3180603021908090705011d061206030d020a08090f0616060c0905010203040305190f05070e040b060d02100e010908030d0605041b0903110604030c08030c1b0604260a 73
    0x2d01c26018070318442d0201e92000c0d605a402500d91844551101030204010340c03042c203c080f001c0030b48030104199800100c0204049821080807c82d01c044264100722030307801e080015640c031142030b20040440e605180c03103071821441460101400b800b0710400c00c0002d92900d108a43d01607210300400489144e07107080c0500186000b041460000e18035080000d615880001074405594000001e00701081041d112401c021440640484541c006980a01d0105009119a00051a440441c070078030f4502444d040301d20244c024209845107210030540c80158a80005001013100c0c82e0a100c51515a0070f8016201105150300c026483e10000424404400c00b07900074100710350341030301c05020014940d00d298460314120103010b40041c0e0b2100c010408501160010101150003400300b9240c04e031291107480c00c00c21160480b9000380d10000318003014031410003d01c8050007408a04150401e041c000041d49846240300d601ea446646007606503041d21485107010114884e04202d0b40c001900e0f00d003402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 635421798 1250 635420548 635420557
    0x1e1b0807030305010806010501090e0603070308040b0a080703110301060e010c0605130203120f0328020a170a090c0902090a08010608070e071106010603090510060b0d0605011b06090318060302 84
    0x10700003801c0ca07000040c1a100081e1490507200d058446258407800e049241466900c02031059515100702c810002c0030030246001007014020320740780981d9035404c100014000c00405001c2c3c104040c40d040012403071003d9202528195401031410141d0a0468001210301502958000d82503d181100b40403a4804080140a12600c25020713158070600e1140c02c0c0d0901d0040b849032500400b0100f002500b502c4610400d41c0040303c1c90f28900f01c0101008113254101d0300140c1280c40400c084400003403034101c030315507456801540300c142404208c00f039035140c02d2044014851899120340104054601d0382d11030301c42c80003a200702d90007006220758407809903a88607200d202c0c154441071403501103880c2a2154241c1b200c108141700052006902c0c001040b0000c2800100c29034990164040810f80c04e182c074000e1074024003c803803d0b29140c0704e0076400c8008a824590210b41484883c40b51201010044172107250115000400026811000c4c00d05650740c42c0050480e110010b0b0303c20b800708101c0d030940c0c043d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 635423048 1250 635421798 635421803
    0xc0304061b0b0a020c0c090c12040302100203070207050a050f3001090c05010f080f0705213105060406050c09030303180c0a03030c02130617010209041109011e1b0807 73
    0x44040c9586c5109000a1002c2514404800f0008000499a4400800c000ca8109120b441260191003440e0380c039108a8109a41c800d0050b04540b80401c0a0320f44803d51001503c800c40340c00c1c4440b000074000460f11101606020314201c50420804003004c0e01514480c80f40089100a2140d0902494900c2c0b8115542c001c103404a0a00381000110505ca036101c1032280c3e0b242c0007540415218180300340c82c075400250781c24441d044091146d2180d481e600031700502445a071940084520380d11903246031170720300c203440e2300405654481c0040089200040d20a41160300480e0014a40d1105142a0107905c15490062380500c400002d11400c28041159960050112801e890801201c101003243c000f0f00d07071102070001504c0b44100b602614151280703a00d5500040d400260980e82d6111041c045504190400c03116540072508030b15506041c020440b18103040b034030079440c00d43d05070001b07403041b919030700326041c001102d00310018060f003c0c00715404260303200070404030703400b41c0d502d071020fa9a442506c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 635424298 1250 635423048 635423053
    0x1b0a09060803070c12020306040f08070213050709060201050c121305120d0506040b0f091504061716051c03020703020613090b030a0b130221030307090b0c0304061b0b0a020c 76
    0x6200d0314071740d0705c56480c80c5c1c01000b0340420744650f01c075058800051141a1040314003048200300503a070f0840000249038803e180446c043c54020006000d001082d8081400e59041204000305030007500200d0710140165107a00b4015141d0446110246032130800042403031203070311480c01c208142d51000c0d001c01c54a444040c09150365150500007038441004042d5080f040d40c12000c0f55500d0843d105035400070130107a10350b910540205c006000d0701c2507940301500103400e410306000505802d01c0410400c03182110080011407609022411100c0003020702402c000080c03041d8020540b003400110001c5130010304098036009200c4240b10003148078481c900c84503140031b90848181c1800b14800c4001d81c2c00c084418410382d01c44248a810046007501280c0c030900328034141c020802010031080400c4a903400030754981c030b806a00a0f107580c845801002e410f00b42440141c3e05440004200e0741176600900c1d100e00d001c080340d0100400ea20b400e50340200251114020058403003030710781c09440d8a8001208 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 635425548 1250 635424298 635424323
    0x106051002030a09050d0f0f03030519180b070207080102040609060e03060708070809031c020a0305070c0c0302010c1109040312060621110412050105070e121b0a0906080307 76
    0xa0070790380c901c54490039002103410003100308030360300d0258900d845250141c194940705640b959103050f405c0540c06c1c4201d0100e0340c0d407814000303490749040c40201c0258400704100000c0b00b42c0e01d255180303134200315001407401c070078200005c047e00d1090040310000c0c4034000c020b54071203440301d00c0075114078064000e40000400c0040900c04900e000954503000c0e4980d6141e070000f40e20344035001c9800440041c02001148000c102c02485a01121206034a0011320000141c0f20400304a000301560401750402040000d0f854443c408250fa402d40c0c842100d609003403003101c1183c603181c151890040e0001080d4010120b10400c0207242e00814049090f0b100d02000f0840e0700d40b108029a00d1070303005000701c40c10350341d9042c003504201013a80c8251101f40b0322201031411b00d0b0f0b9a8019040026454008031442d94440061085564001040503200e0303104640c81620b070407280740e41968408003042d5100d6850b88030582841c440d1034841c0780e28040c00f0045001d00c801511100e001c1d41d2980705000c1102d070380c0362002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 635426798 1250 635425548 635425579
    0x1a06011403071b02060c12040e0c0c190312050f0412141806160c17120307181716080d02030f1c06030b040302060a0504050709110c0708010605 63
    0x4080700d00ca801c054403140810005840d00103039440c19070a049801000421078580c41400410681e8621460044595651b07410003d219450190140054420740d03403d0140ea9400350707010400c058003910030391272118400c206090403603000d188501d00740b404514020500c50398403001d49100707215902074100124a0074036828121035894116850b40b011807400d2040c8003800186c25580d1100d02c0c00101500c3c101944016940c0001070110000c40e6500d5120401f0000854910100103010601c8809002d003041610801096480010320b25010002403403201101080120240400b51a1504c00351005580e400d00040d03803030b0110651801100e90f1910001090701c0d001892140321801d65000c0c504203081841039440640140b406c0500c2c1c8003c044440c6c032403842500c03522000394043c40300d041c510300705820040d003801e0010f0014810581490101320100da000039000046640c101d10003d00160005130214850091140e03107481c0d40102c410028444405412000c180c403030850390401c10070780c140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 635428048 1250 635426798 635426837
    0x609040b07140409020a0503090709050103050a110402120f1f03171308031909080c090f06040605030a0c090e0f10022809090510030803150d1a0601 65
    0x45800500a149032000140d0080c49100c0041000c0040e1022904140e1034404100c00d80e0004c2d102c1800080d0080204501048200146801042ea0703207030400c41c550654039010340b11214801c0141c02000082072a60301515650304889001c0403615104825050043c503c40c400c21041e1365040c498a81401000f180caa885200682101d40c802a500160003404141508a42215000c0b0300e114884100008003948240b004001c000311340f84111104c0b07109c2c1c81340580100340c96001292190311860f090b5086803950003402c0d41010306001c04903550303560000010003824542d04403681501034229000c04104500003840159101c2c950207010346031040152694815404c01042090b62154003c14134206083c2d00400b860060f0031107600b110041c9208411148120340c0b56240011710316107003000010202c0c8076081c0c210085540c100052440c0d510307071a4050201a1502019005403600300c0401d5507007501e024103080e84003a24400700034801022a00420342200c102c1d000c10b440002610040080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 635429298 1250 635428048 635428051
    0x120a09140d05121005090408130b041404091502070305040806010e0408070f05011b021501060206090d05030c040e0906150d0209040f050c060c07061805010507120302040b1605060609 80
    0x195514941010030720f56100c00102c1c0e001d00b4180703503d42c2c03414000c1181d844038400144070302c1c000e42c06c5540d240340044803000342003000d0340902181034040c402441000780e100300b80710100c0812100030900000070b0828105404aa103490051a80b002503164101038002014208441d411000d65046a80e90742c0c1407640c00d0b10888000300302202c100411400501040c04c4a24030901407400000c901800e020b140c25100c0440c81d1340000341e408020b0030f005500352031124078003500c101e1015210b5828910502591942c210006000784140400054020b607003c109403801444804881c000508000b295540c41d04415280d07440c102c0020900780d071050a00c07440d02131400380d02604006c40ba03a207507160640764003407188044446000c6c4148822499803507501502483c4180c80c00760040c0c03450540e014041c042890010903140c0d41c1d00c2c40401c0305a8002041e03034541500510b03120742141114101728002c0c843c0740c10880a00030082400d0302180031030340b507500555108804403201e5446940810041c40710 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 635430548 1250 635429298 635429323
    0x61806050a120b04050c040603080318120313080c0712210804020f0315190b120a060506060f04060534080903030708030a050403080115020c0103020f120a0914 70
    0x101041c600b00000e2518106a038000e018206036111035022030005001e072002d9600503180d41602000f804043c25407074100d03866103c1d044000384400c556909a9000d2804020804241070b07404880030300601010000b21030451919a0598094949600c174000c8201141c00040c0c840c0b29840d415118440401c444500300200542c803104015130307503a400c005113100b00b22421901402400c07241c5040180800740700340100c2251002c1c0200311050318001c821500500c4a0a209848048030201003e00c00701d41e90324506d40000000c03800c0d6440001050040c40f6100c1d1000512400003400184107a001c0090030001e20180c0300d039903080030b500380706a100500216100d01c03042c0c01842ca00c2c000803015001403000c184040d080d20309103180d988400500303410440d8600d1440e0749441c10401059441800d070342c0900107100041c020821548402075a0f2000ba40c06e40f818598002401400302e207120302914603c0308840000b109510389007100e01b0141c071411310200c507500f44016400c8010200400c41144c01e84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 635431654 1106 635430548 635430569
    0x305160806070f0e06030702010b180907050d08160312060906090c0f05180102071203030209010201420e090615060301050f0d1401061806050a 63
    0x310010845020090320030403c0c00311079006600615100310940c0c090f80c495842a20590060010314441644800c2d05500d8082a407221082d8030f1056151a0549140e507645070103101082031441001441410140590204240998440d02046000b07150850b89924400324403000c441150b0003040341c05407981400e210580d420700950032501400e10300080c2d00c2c03c014500400f0740c014424041e5412500d10244092680b080100e5400b030255002c0941042036685000790095000d1003441d4099400c080c102c1c000840214031081e5506281da400d1070004407880710500907840c1408181d400c04070380003400710750040042000c3d4412480c8a006004500340381d2107a100f0703840744d0a1414410a000c000601954031031201d43d04800300e069030345c4000000300c0d24044000350038060f15822603600e804c0d0002074688030b40c0026041d031061900c04016140e107545c1444007000c071500820840c2c1c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 635251798 635431654 := by
  have h0 := BRFrame.cov_init 635251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 635251798 ≤ n) (h2 : n < 635431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
