-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0899
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:34:42.689374+00:00
-- url     : https://prove2.me/submissions/8f0d92a9-a3f9-432f-83a3-f9c5cde129cd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 161510791 ≤ n < 161690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 161512041 1250 161510791 161510813
    0x11010c0b13062904020a170c0306090a09050c0f01110d0201020304060e211c02041508060312160807050a120e0118090b0a081606030b0603090a02010c2d 67
    0x1140b521960f41506214035250b01141054101041d0740050301d0714400981610420212500c4540d10748032241000003984003500114800c4409840919080e01c42e803d00c00b0946042d103a00601c6600651504203460504e12005007a1402c1490503480a00c0d0720710107103003803400b01001e800c0103075000801c00050001c1070141c014483c0b80c00c8010000640c10b030103600304404651007544080a00041e2002a44150118914ac442c1d94014115640c949d968400050390109404102c00b0a03103003400500589008281110801b010104240c58a03075440f40454054507024022945040c0c144203d201040d0204407100500e031090142c140d100400b90700282c421883d4107852810004140d440d8152a4030320448001120564040401c8210000b40020301d20321403504040a54407034461900080108803800340b04072101d50701c0811000b08408144201813200700d4500310303941d00c01e0a401380154801d9940090b114020146800607032580c105100484d020f401c10602084102441c44050014900017 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 161513291 1250 161512041 161512061
    0x4150204080d020f1b0d060b030601060e03010b010807081824060913050a170d0e011a0f090105010c0f0803040c0303080603030c0705040f14130c0f0b0711010c0b1306 73
    0x3042420035180404101c00c10b80105c0c140680c000705403d5040180d00d0b0008050b80c400141543e0741581c640c10b00420711500105000d01c01d41c20034000340850350246003428010038641d40d03a03c45944e15008004922052285594000e1042c003c45a50900c00111030211000b0244203811142c1000310400034040009000c0c0c801105981d00a00700064000903030601d5140e002c500b00300c071041041c00190280c040c440c040c100242c1043d0118005070410351220f4100500c1d5410442141501404d02c0712180e480c107402500114120018000d0358080c8201c83d00d024850314182d80843e58640d0348903090b400c1034600b101c40854550050041540000405500403820f4005608100c83d9045440c0c3d0f44180d80308250142c0d82d40d004201d618441608180c42c07850010496811908010340310701e000140101c8255008224864007051103a0981025400c07290b100c0300341c600b031000f107450700c440e103402004286040c0566000b4020004c0c1c4a1b440161189030424445a02d0090508100d0161054025 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 161514541 1250 161513291 161513293
    0xc030b0906090303040204050a0603020d0b0106140903070e060a1802090102060f0601050a0c0c08030c061014090a0c0912030e030d0206130b060a0902030924010f030b04150204080d020f 81
    0x1c2002001000081501e034850b804450100745500c480920320004c028640019412101810403941032099203a00316048075800e540740901c9402c000031444445c0209034410313500d6000402c04021844001301456003001c4001c0001043c00e545003004484200300601c1c400c020b03a004141d008003580c051002c1540034038000c59464042c41c0c60400240700f403146080d2003050025a1929409000304034080401a0903008222641d4a40780ca085558490040303802d9100e000c0d0002d00442d070728440c0c0246011a10340030740540c6031034464100200c080d00b10054070b002003180200d40020794804c0c506c0c00c0e04003103019440d4140c42c10700b100145800c0000005e07040d42075502c04018007201d0002000b54004036604101e401196440b2a000201ea104969216542041c00401030082422000c1746d03201920484482600050303400c1c8100342c100034030920900c0511a204002000400e5003a094154014400d0f0f0500c6013840c4948440e9040345c016401220855110301340580c14181c0411000100ea51808 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 161515791 1250 161514541 161514553
    0x60a020301061b03021e0a060b03032802011506030e0606090c0405011d0a0801060611150a0507020c03012c0111030a09030908012a030c021b030a0f0c030b09 69
    0x44090046a201c0f540c00883c02150f20038041803610038049000d11b1a0a0304004620355450106141e0340c030001203040e20340d0342c039201500344989400801c0f01c08284a20013026040300c5118108816007203840040e4007036540b14011045003c040d4942c0b074000d850142c0700000d5500300c030b0210754508540144080d01450b2240140001520342d40b01740c1c0c080f5042440e100043c0880c0000e148040c84101568a0704004103040c045030324041900111f0076960a95980001229458100ca555a030f4070007003005aa502200810074891b035076002998001c80a0040f54074005888000c20300f10362040324540541c3d86000c0b280c44071200b490030042e49540203030000f80001103d42c0c2c41c0030685d00c409001c118985980380d4140c400c150041c640c0000a0000000800c07420988009405510180705002e0041142e480508040c040c0030b4840d0790481c6030f85a005001c2880710b0012100401142e115155052241411a038002140030020040c22846a2928a040c2d491450891000390000d030404409402c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 161517041 1250 161515791 161515799
    0x105040c0e1005040b0a0e011202010f050f0d050c120403020f0f0f100c2102070b060a0e130302030408030d09050705030f060403030f090b0f060a060306050609010c11040203040f05060a020301 84
    0x2502c920541d03e0031100003840f00d0450b40001d007013840d03a074031811400307a0b590000150b0318042c04031455628000c0e05c400000c0300048001b101d03103100b52058210045c00500802c03550000030b5000076800384200e000c1a04d08001d10840e11148281150200c0043c3d00c0b080c0040d8010205000d40e00c1a454280014801c851050010a8441041d16042c075942e507035501464081510843c09040c0002c1c650003041c52801140d1540b40295120310400d40d0340c1500100400d4a81c00d124641c1c20840300306181c141800e895825142c174103840b240c501a421844244008170b1110014801800d000700020302c00a00b021003403800500b1702525030f020b9480780c0c210500030600c003000030030724540c02139051900180c00c0c1414128100144191344002c0c08803081a410006030b078665100c00341c01218111444154180d075a1002c034280d03203c5000b4280c0054092141902c0b0f540981c500700003d9105418003250040380a0101c0c007241c2084800752080001d200c3d074041070000c01e010304c58001c602c1d03000652656040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 161518291 1250 161517041 161517061
    0x70f0602030a062c0c0d1103010e060607020a030f11060c0a030207090e0c13110a0923030c04150914060a061701180b0301090c09110909060609010215090105040c0e 72
    0x44501100c4584c0c03c01e0005900c54200c600301d0300b0007074040d80100910b030840503503c100d81d0424010050100003000100d1007c0c5414001e58011541c020008040c107411540d40700c0040600b448205c5000d4801c1c3c20007051541e4010103802d200f42ca03040100003c12060600034900300b4a40c0c40107000c24580500200c100001042c00c17000391200381c036900b10011080f00c96200428255003502c4560314003203800e00c10541c0c8111080c0458150545000c4d2280382c81d641c4d10080701008444960582c00ba0101e1000c5013001e80044c6081c540d0208465002c1c0e54905810f41680d400c04010380340c030b00f0032408120352854114522000344c2824070f0101c1c070342c0380b0004039429071181c1801501b00c0c4648500c441290203800d42c205155002020700288460b2190346480102c0394940c0c098400d00b10308002e00c040924101c0c4041da22040c00050144065480c2d075410702ca0558021a40a4118003600c80a6481d0710680e00d0860b02400045000082515250824180b81c501c140c01c21966092500248002c03400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 161519541 1250 161518291 161518349
    0x40b060f09010e0607120905100315090507030905030c010e1504120c171204020301060b0a0203040909050705101205010e04050a14030d06060c051507080c0a05070f0602030a06 77
    0x5420f003002c0003242d805a00141c011300548000508403402840107503501984403114100321201546d00c1012501c06000030303429240e1800611f1829480c0d000100300d03003251a000150499042e08001820030100c0d19040c1c03d5901c40610058980e4484181c402d83c40c0b000c2001d0005800e1141328030009080c15510440c0342c400c0c1d03101050400994400e00401d102456030501a10a907907044190384200e41d0b60440015901240e05078869460300400042c1c044144080310341d00301d0503a001e50702d0b1905240e0000c0042250200541d600e203d00c01e03012079540c8502240d5886010aa11400c0303038604a03444450554005803c421032183d4142c06000000340e00103209498140c0c0032614404003808400018034501901c5140c0740058203210000030f1058100451003c0e10707005034141c410b4200200240440e800b800c0e20000d0004504c83c0000f120030800740007070140851145019441d0001079200c1c8084103107410701c1074801c02d81c0042031092441c141d01c02c0000501d501c0020402030000e00c2d401d90031a003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 161520791 1250 161519541 161519557
    0x50a241a031003081e07030f090b04081f020705150103150b090a091406010b0912010204080604080f12010b0d140105090c0901020109140102070c080601030807021203070609060b040b060f 82
    0x46004102c0041d07174030b84002103016034040c03500580e031a00c1d4581401082002016802e8000c2a46100041080e1b070781e400444080d504084028061003820074001e090140e20342407181202a424014100011002c1c860180c40460102c82c0f0403880d411400d0450750210500c202080d910f02d025a0000c80b42c0310301d03401c10340c0300201940c0082c1440d11400c2c40041010001d005030150300880f0b00200c0c0344054040038110f481410740b030400f101d00c0395141c031608074813660240140d10740c440c60008000486000090442d8403602c10800d00f800b00c165500c0b1040c100a030410b91800750045120b21140295204401456803042c1c2d00491a51400021030b5903000083c140900b0120700107450440b41e4000d411450345a41c1c8800303014070f076a0050800e01d000f504143c074106c40b8803e0007d0b000400110015415050f00d030403140c45880c0c503407a41c3c200441a069800301500c0d902081c00010003240d0684142d201c2039014030390120341e90750550300b00821500b240035003500c50003080c003c0b044102e0395602520001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 161522041 1250 161520791 161520803
    0xc070b0301080f032805070c080706031113050d080c07180b03160308030a06050d080a03061a0910141603110d14090d1202030d05010506071203050a241a031003 70
    0x1042c03007176104032002d106026010303080c020b14683c000703060100000c095003142d050381e4041080701843c204040c0944503800190b240001044010300140c5041c0e900300e1407003803255044602e00800615000e0504403554801c1241e1160035400e0b031810703400c0703005030090140b084014020b209070418102c140103c80d4000076190700000b1001078406000d5600000241000900070950000d0303600c2c05903019446000f080d0300090a20300006652490b0b000c0c0600130703c1020150900701000701d000d10000030851051201084402c0c0040200c1524400050807140345444d4042034085060401812040900da40540c0950010080443c21a0301c2001c059000010101c4d50765174000c4a80001d12040080303501408070080341c02c520300720030740000081590342c1d9400c1c01804280e03601c02c00c000560044000207040c2d80407601501c2200c910079400550300155075580060782005181c01103104101c030103c0c011010381c03910010300c074691601c6044d0201001d8851501e1642c5800c41c001009140503100003081e03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 161523291 1250 161522041 161522107
    0x61303030b03010212011a12070302090102010b091f0b0c030421021933030f060e01120605010b0405220b0d06020306090f0603060610050c070b0301080f03 68
    0x2018401c0d08140c50700d19009009540b1144075080780c0c03020403400e1180112015000000d1174144409001b902d0300036520001c80300c07090360b4404041c1c0103588080c681c5070442d5139078030f41e045080c2c0c2e445104074000d429164008404814640c180c035000c8015810801c45403200b170024400050300001190217031045500b154800c10140d43c410100f4400d400802540200000d020100010550f1088000c440c00300016641900e1101c402c3d403080e800302014441085020625000c42502981000608080e0b014000801c0ba0b03440300307242c400701c90a0300b008210440c0b0401e17030720a110040c0181ca02600740031120500e0540b50400044040020300524021071080440d08d294a44d40d9512034a17032460003405103805140149080d10003540115411481480307541d002c01c035551b20708000300784600c0002d40241815219107080041c001e04041d00030080210400c501e41c980d000074081a002401090711464072941440b08260410440e44921503641d8814802c014601300010f02450040c0710b410792141d070b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 161524541 1250 161523291 161523293
    0x305010503061b0c0d0201150b03070203071e020d060516080907030b07050c070b0406300203151206070305010b0f22031e0b1f0b0a020109020a09060e06120613 70
    0x10749801400d82001040c020410545d00468040d0404400501900200350649031218062840d5000640d600780043e030040c04103000161211220b08100b03107004405d0741c82c064095002403c420011141184c0442d1034009200b8850000040d240301c064950400700745500d001c4041a40c5c601103488040c110100c0300300480c1c0e0403405203044075010403001c400d840c8119115407100003680e03c6481100000303943c94035942da80044040b04a05542602103407184020090880c05000c2d4002030111205888100c01a6015945443d008044499a02d025162070702c9d10003400380445105901007545000c0821840c070f0030100080442d0401c6503c0c1e04000300c0c05460320701c0b00c00741200c00d0708014222458540d0041c880c003080102d052000b40b20b50b00d000416600c1c10510805170a03090840d1024095000003800070b02503150203040d84249070700c000920034205800081c04101c0a40c02100550f035100018130004040c03054803540f142c0c0c20b0310188022014400b05680c0c90300c00810200703100271079060b240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 161525791 1250 161524541 161524591
    0x911100c080a17070801030b0a0b0d12030f0c0905130608060406050907051503091006060e01030506040b0d12030606180501030b031c020d0809070614031302061309050601030501050306 81
    0x14026580c1074000030f12610302040c01500d444002e02080d0340d45074403500001c0c00d0707882c240036a10840d900a414070303c031000c140e91420502d214012007030040c10744072408044201081d200c1c80780700c00400c0e6140050705103042e040c400507403039003190228403a050090612138940001030060300030b9404000040c09035a4038403047e04041c42da400c01503204a00702c00d1001c4c500d46003005107000d17241c6c550554002d281d81c803e0f900215540b6202c0c80d400f2500c841d40c034a030f046d03000313500c801e03401000900040740107070700a8005408021900011203828151000112510b60b051203180007605984c244200d00131103810f0f50001d914528400c0134101512260314400304d850900c1400d1000c2e1145140b2082c0d21000c24004c0d4441a548032a0700029100800041480c0c000054020840700283c461004c0c17000e14152001003a40001c00b00b0000c40740e22002603005886840c010500005503c40b0681550b040141031401c0d41d001615036030400d420800140b15a550200700503030010201c100800790000065084 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 161527041 1250 161525791 161525807
    0xd020d050c03090418060c0e031c03140c120a020f040311040e010e0f0c06090607110a03080a09090501050d02030601140409060203040c1d091515130911100c080a 71
    0xc0da801c1381c1488208960b00c101022030071540351003400c090040d40c00d4010b01f103034900100c1650662580c07140710341c03064841c403d01c1c0304107411019180104040d1001c07022201c01c09000c2d1001c4c00c1480e8000345e00205c2001c032040c841d4002001020640c903144c501101a01d40b400f0f00d00000d03080504100341d0b00500d80e115407140c04401240ea00a01c00440c0c2c0c5d946047d11030941007042c941c0c501a0910201540c500135085800d202001082d050074100103403646001281c00c4084a5040384600d000480814546409400b14062562710710305101e082c10900400e031141a48114001c441e645030740320040c2c1c1d0108841d41514038a5181a20482e00000003801400b60043c0c0644600d10000600050040c40384031032003a80d16030880360240ca500c10740c4941078194210341d142401e070050000d00e40300ba400000c515800c1160041c20407403811003180091250250038003031002c070640c0c942d91f0800300f084d01c10600c02007007012160300ca52190758400c068460070503004002c0c40da030000913952010302c1c052101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 161528291 1250 161527041 161527057
    0x100504030b0a0501030b15090a0507030608060f10060309030c0308040c05060403080903010605120703110109090204060e03100605010905060d110301080d0e091e1003061e0e0d020d050c03 82
    0x75120701802d00741c0c440002002c00b808152040320700e490000318804015255080034840c0600020501d9440007401e0000700f40161194007016120200000e0b50381080201ca805913104529426440c140240c1840c00803203181d010800741428841080003003500660030030340403a05410880055552841c03d40c1c0c0c00c1e030301c43d040343d07522100124020041c0901c54025040c00f030700035002001515106c20821401c04400310600c00e80d41e100705410300000d1500d542c0c10344001c40605110440c1500c9500c1c207070036604280c00440024051081e0128903190401655111042103502040038605001c002044a041c50003840d015160002c0c2820404200f60b02402112000b00a0181c4a503154103145440302600030b41c03003000a02101d01c140c078514000f0b00040c0100c4514014840303044141c1c0203556908401420300d8400361240d14004007142c2c050140000214070780c101c104400d02107a00100403510076040400e0395502148c2c420300d0080c2c00040a052941c80c6080c0503840384c20710304c0c420385580b080041d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 161529541 1250 161528291 161528303
    0x7082d0403180b0a020105010e13021c02060d0b03160e011e08010e150a0525050702030109140d03020c15090a060c0509010306080a12110a060e0304050108010806100510050403 77
    0x10b40020100d1610001c1c01c00c444280d802405143da8440c040e005007142a58841210181c0d540035000528160003a04901d83c50150040c040c10126000201140c00c845400d07440d2940308d500d6030b6010f01e82441769401402c69400452440781c100810140502c505016400e00340030142002c10f2003000c1e410341c6800801044009001c070040c030185d80c98030742c86100c100b020b0a041080c080b44032240c00740100351045401e600b503c81d60b200c0280c10000b0314080121098107104080203448050b8900f801000d403901d010349a4205200d038400c555034130b03101000c1c00d800101031061203504440e21001c5401040300c035480d103030390b011740c0c0394080c6e400d080c64004200200851301d488464401d49400030301419605100342c80421801d43d8441203192a64a40b0400411b90084c83d0b0340203a06a0040c5504880d8020700e00440310903840507503c050442d10301ea20030190a500210b0100300d10f42c2d120034a6405042c16501401240c28060760081218002e0300826220700d20600e01070304118400c1c01501c0c01150001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 161530791 1250 161529541 161529587
    0x70b0706021905040b091302280e120a02040c020708030d0e010b0a1203140f0d02070b070906021e120313060e030906070f140607050307082d0403 64
    0x890a1002944a40b14004210803464032520509002d80c081d00c08682550301102e1600041c00d0401200111070b13070740c640c0300d036a091050988640c1100030100920551b9442540803082c0314102901d001d404007201d1b8894400f142422555403000700e11414504d40c117580108203400601402e034105402c58100c1c015500c804621012440c1041e0400068110300c20001c110021060701845041f08150141340c200f60410018800000c1c0700b040300080810203c3d21240c10015a00340410150f0300c00f6007102d80c0c40303401280803014000705030029500500a0700f81420a289070400203500d90020441000b20f050368100b14000fa5036041c44804400344104686503601d1901c0c0303a441d511840c032000181c4041d490012203402001001040b2512200000d12460074010956115420364205460488100d2243c000c0c1e900c103010304004503405450b564548640f649000a00240745000c0207103180780c1c007011034400340d084400e0300c4441480145000c9800300c450760385d405c0945030a1048000100041012 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 161532041 1250 161530791 161530793
    0x40305010e1e0604020d120207030804060c15020c151308070311060f1b160503040303020a031d0105070605041e21020304080706030e070f0e0a0e06070e01030c02070b07 74
    0x4038681d150390b10464941e20701c0c0d036114a511a43ea5604580c0250040020070660001c650308401c08a150759640c812103070307015203c0c0d585814179080b581c80800412000c403803850401440c501c4050003481130141c114100500000c1c102d40d40c40c500300f090300c0071100d0741000c12200403c03100b250200e1600a90065134910162400401101d40555940001d001b00e0000c00c10b1500040000e9000c0c140d86415007080c030450b069160502c1c0c0c070680005121031181d0040d80d0002d502030003d44021170003034019190040040c18040d00f104a805881980088000e00c0c0380d14036078004040e220340a40107500003c4aa031980f030070b84448010007410580c4400d904406004000307400341c00d4882e188412250f40049030103072601f039a880c095401003540c25000b81e0000d01c0800d2113a8811400c420905049481659407000444400f1545800080640e4014000c00c590f102c2c460040800840c00340d40245024601307240014501007148a03070078109600c070303a00068114400c000c0c50002e407a4540e501a03071640c40d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 161533291 1250 161532041 161532043
    0x30d050c0301030605010503030703020d0819060e1506120c03070e0d05070512010902010804020603091e0109020a17031206061b0c24030403030f02040b0f1804020f09060f040305010e 80
    0x340f01c01c589081c1480d0010a02c0d0402100351145194981c00502d00700040c9042036462800050030b0210210940b0030f0803040d00102e000300c10047c07000d50300c0c22106003400780a4003000f070f011403220f9001c0c110800045c91003c0d2400c180d10381c010340b412030045d107948980400b241d904044449040d40600e00175051001d001003c6014421158121003030103019000310320103820f039400c0f468081d020449580020f805030610784021907001050300705032142440510038220107000b442e0700d84001c50390340e00340d04411410000701c80713406070102c64090640020b0303150f81c4959921a0300e00c000306a00c91000401c0441c0c07145000d9618070400343c00540c5027040c1c22181e0319502d80d0b80781c1ca1603106030400f56081110740203600f00d04c0c49680107004075601c0d5540343d40f01600540314844100c01d2045d400c0000088848401c805440000f0310500c07065078030501c1e4035080180d00c000d051540c1c4500d10403c0022003000314035045822005065503030383d0315048054a6000b06000c1c80d44054070b15400c056148683c40c44c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 161534541 1250 161533291 161533297
    0xa02070f03080a0e040b1c0501090f0c0f1d0c0c010e010219090b0c2e050708012309010513060b0d0615020105090d0e12300c0d030b03030d050c 63
    0x420341d985001c0150000108000d6a100d0013041f0703003241007189006182d100040c0041a1140500008602400c2640d6400b038101c61017002034800b11141365040c03000280749808079009010300d8421911040b0004418110f010014180790300c1c08800041010008000390058206056580000c5442c1ca03500400e4200c07603d010803032200054804100403540c40403210680c2e0311459480b004001400e800c4114003400c01c40523030720042c3c00341140010703050420300340101841182075a0f12038065516007030301e04444400020300715419113510341d070080c000c1d19038604150440d00121550f08180080941030402090700b90003070300d0383c540005012080801550440e40481e030150380c59a09101c00ba0404034201d45065510704180e030044c000e0194000e11031403040a0120000b05a1401428481541460004c0d4a25041c00f1005a0242e0841c0d12015000320720011030703070510b0340d072524007124032145d1a020102c0000081c1030f40d43c40c40688a032030410a03500c0140c0b090b0410001c07810f210302c041c03034290 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 161535791 1250 161534541 161534557
    0x4020316030b06010e030a0c050907090806071e02060403020c011b060204090e12070b0103080717030712051608040b040c050907031b0e01080412110111030105040b090705030a020a02070f0308 84
    0x15070600200b05181800241f500d032003500410308a00c114248410000d134030300090000010043c103c82e011620302d8041c48980e000703200701d8964a40658078043c2c27107160500007200c401d0641d00300c50100000300c3e07000309030101296024a04010710700e138151800c000170005200060005403000c500825800c20551001c0001d6104a00300e42880304054030300b003064480c0c1f240c0106a100c252004100142801e0b001d46403a502c1182000030b2a0007000b46400160011502580000c24001003000889807230b1040c01d07084241c00003200441c55075a0000313480d0782c001900082800c10400700050500c24503102e071001902009083c0b81d21414030203c020040c10f9810001d0940400e000121042c59008043c100001c280603140c2500d1030380d6580ba10030788030351680702281c18003004043e4882171020a214030005490342843c074039100d50401040c00100c4110080f400d010750002c03001c0c44205a000740c1a03a520104a440241c1d540031080300c105d007031030001d034007204182840500100401c00c41c100904150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 161537041 1250 161535791 161535797
    0x109150b1e190e0f0115140f040902030a05180102090a03020906041b0c0308010e070c030e040b0a06031a03010204061e02010905030f0a11010501030c17030915032202100804020316030b0601 83
    0x990b22840700c6e64040155541210210304840d00344524504000003500c13001c40d0750301640d4205a40c402c034980a0781c0c002c9a10b50703c10f1381e540b4100080603c14142c41610383c0104002103082c044904d0206071003c0751800064407400e54900001c0142d507858001c000e0700c8443e1403501001a030004005803030608a484124046156500045801c10100c0682480780300d050799105183c07102074405131200303016189143d4010b525542c0c4a11036446111481006040650b40081c840d14000c0e4964080c030004128507100380d0040104002540e40b1410b540d0380344400c201d461070f2510b09040305038010f1100c0c2c400100391740004100010103500c0c84001d04100720321510703240300b090f144d00012800c0711000d002c014540700100760706002001d00d464802d1044282181201c0c030344810310002808024090301c001c851520000304200d281c4550a400600b0749911402c40c0d2691400d070740c0000e031182100030b03841007044038981c00101556010070440b40c3c80101e40480c2c0d507640d5181d0800d440000e001725203803404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 161538291 1250 161537041 161537071
    0x2011b030e071502010e0607050409060506030903070b060a030b0108010b090112170c10111905030f19020d050a09020306070c02060f0c030c0304080109150b1e190e 72
    0x5050007801100701000ca804060701245003805a50098508600044000c644da121095048810f0405c007241c081c1c0401d8980686030761400101c1ca080e1526074019a020340c4090040c408420400000d41d40d0f4503038418130b0110907640702d1001c030790010480e9001070030640e508000000d00031010b5100540b81c00050714481941d81e22950030510324031100c0c6c0000e00d409840044c911b5016441c20190032060a8102590b08103031260b100542074800c460075000500c0c0001440da007a04844440c034040302607141c1000750451a1030004003d10003801080c180d00400710945001e2091484c0d4111600f025080b6410000c0d403c00c1c907520002400c10400880c000c1c8a1040490700c0070f0300603840c81421650041c809850801c00341f51010b5590000300d00101544414451140e5070303281880644054202100001003110311400d054441c00f0503100c080030440d140c203d100a040d2200c01074080d02c130b00c15081788c2d80c00e0703048100414192501464980d1030205a000b012a4511401815078000c0000d4144014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 161539541 1250 161538291 161538341
    0x1506041404230c0d0c050306070f0504061103040b030a0e1b030d0e030c060a120f02030105011706130f020d050f06010c0b0421050a02011d19020607120201 68
    0x400320340c0a45000d00020220b50010303400450401e6404480c071030110907607409210b040c0100e010ba8030711840880354039050b01d50a024904081041540c0601240380a0851040048000d0564817460240700d00304190a03000e408010b60400c1143d00600d51840c1d00c5a0341d142400031440240300008a04039603020b401e5030088451303514002d1580506000700a4a04480151826034844840d824110f07018007484c04c00030219a91403024010154143c1c5582000d00b1100c0c0f4a103044904a6501610700c40c4180010300050341d016410314078410100f9502203a0307441d003c00003041422058074181405043c0306100305100051340250440e0403002c41c051006403154031b00303441940401c07180380f0300240c0e4511108011403804218550000d014000244501c1c202c50b0500321190850704202002c2800040e10081c0198240f259050840ba080d4071000204480c40085031540c03244905d08200b0003502d803014056640307071002ca411b5143e21124102d0460240c0310040e000e010030340c5d008050402086e0490b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 161540791 1250 161539541 161539571
    0x705030327010c02100b0406050303030103060e060906070e010c0501020904092004020315100908030d0b09011e1401020c0619030612080304020d060f140609060d03080c0714150604 79
    0x11022240d940c018000440d481005c0070001e041506509501a8403080d0001700c42c2c0b41400203501a40c010310010030540c18841c0e40500e00080a000451540e101c0802c012401c1d6000f0140c1c0e24090091800c04510901c506105019000b002c1151340d005240c012003e040100031a61012034030800781403582e000e020001000101d0008850042d4450f685000c150340e5481c000f012000c80e00a103003840212141c4400300385145030012200111511b83e82c46002100f40b402c2e80ca50350042c00e401e4001510980320300100c22800c0483c0c81758544403007040405402580c001c1c8602e400e0b0290291907503480d404a000440071200c1c0f050301802c0440e1400c44003113014040c01141450036508000c84505d55120ba078240a003400314a03c0641322195922100400e62589000c0d19030301350420b80070060541884420040a210040c1c0842d201d071032414002000203801420260b8000d00c0074694544400300703424500e0156604e9580c0c4034903401810b40340d501485071401c000f40504010349040040600c589030b12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 161542041 1250 161540791 161540801
    0x7020102040b0d020708040305030304080309010f09020f102007030605010803030c16030302120c070c06020d0f0e03030d1b08070e0a050d14010e0d11011b14070503032701 75
    0x10032680404102c4802c40100e143c0017017541038411004a803078140e0b25281e140c20358205690840780c002000007031042c1da50090044450010170940b0030003c008031540040c90110804c1c0c005409800613151990141e03000741490300d440b07903043c4280c82c14410108141074642002d40401c0320348038a030100200344e80000009481c031800040500c24030701084c1d07000d040c2d04100d110a044040613020804000c00405103901d460052000b07001050700c1d90100e1418400b154119082201158013411001162590005128420000e1410443c1c0c94a01900105c0e0941c4140008119014144500000c45c004050071058540510b944c41111603201c0c44001c8908503114500e5951021001d80280a2131070405042441c045c81080a41044103054044600f5209183c40041058205d8400c0313020494108201041d1101440004c008140c007515442400c524014286001c0185e103444244c3c00d010450100c03200d641e0040110780e2640341000e4255507540410a600c41001c5510600041a031014080c2c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 161543291 1250 161542041 161542049
    0x3051906090b21210913091101021b0d0206040905040305030108070812040902161505090706030e030a0302030414010603051b0111120901020c2815080103020d030903290702010204 79
    0x644400070802102020054007148110790002d000c1045417055074820443c0c1d400c450400c51b02107a42101410094000f10725051400d065402443e41c000e43c8111034210724030032141c100c401c4401007403a80042892400703140c0000035030b00d01d440140070170706800101035030483c0d86503c02c41c2c4005031103c90303c5496100c2501c002001d560107110038000144c2d103401401c860079481006200c0d00e000382d12080d02c40c40200d014107000c980d540c028444121020300a4070050003041c00c061181c00340c20b400107541c80c410825580200f6038044040b804120001e8001d1000d80c1001c002480042e40b01d080c40354a580390036980c00008502c009800340254082e00034801d070803401c0000b0b0305040760203103072640b510341c0807508090443c0a4608840b4182da0ba034144651141c0c002c0500d800c00740c01c0206040700001154103c00d152644041250b01f6165202280d00c2c151707907042e159002c418415107000d0311084180d4200400308010300700350204840e002030700d82201500500c041c4a182c1c0756041d0503401c0348100e000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 161544541 1250 161543291 161543293
    0xa030b0406050711061608011a0417240601031a03101a060a120506040603050a170913020d054602030c03150303040b04030303051906090b21 62
    0x200070408507403010303600901508044445000c8045120b0070032104407078404403054205810451141d20482c821f003d0100b0000e1070030b011140030140c0f501d9020302c2c442e140320b143c250428484402003d00031107041328102204408a581c0f00c030500c440c0044100c6201d400689805038503594030802c004080003407000503018083c41c41003503000074081c20366a40400000c104401002110b920f0354002015000d10300c2d0340b20400038000042c2d281c16603d01800407840380d03040c14414008140049810703a40d1590c02a080c41ca0781c40c030151050014020a1403441d1300ca403030f101403184800a660020502501419401c000ca17941c1c000942142000c03c02c928544c050030902604000404011520380e6009040040d4000c0159400040140d0b4011a64200740840c007105000c003940d10f4000e4490120022800307035051030b04144014035240142d1102501305501c400205648011551002a07414801d100c01d001d01038135038a041002d4018500414003d80c01e91454040e203040000b0246004a8290 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 161545791 1250 161544541 161544563
    0x322030b01050f031c0c0201110f120a030e0703080702100306030507050d0807080c0c03070801060812070602070605161209020d030e12060f040b15010f1b1e0209060a03 74
    0x90601c018003032058031040d01840f51000b0022107a400300c400d2211914586e860b01c894403103901c0010300c43c2c2400416101650b12000c10800798074404200c0c3c070a103c04c005915a2191080740c0e0031809020490300340d40c245c0c0a90039003c8103029622005210250003551001d29550441074110300b1580a44400313011038008450620551411400040b2554000c4c03499508002880d2a0422540d0045403082c40e07640c8680e14484189c20188400340c0207140d102c00800c14a80342600050319403140d615981488280068005c08100c41641079404042c0c11400400c0b02d071400b52880803075205800c4020010583e64410760354212428080d08034941d0f8090686540e0490940e030581c1c0c2030314006070841c1e1003141d201e21150315140c2001310314441e800c000030820460a050901c003160300301c0605003015800ca10340440340300d640c105508641c20603552901c080e0a40080c03906840100303038182d0082c00e400d00507082c100c80294403014201904d000300c0710305a091702d0701020001407400a10000f07041c24402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 161547041 1250 161545791 161545799
    0x30303040c090b01020a060204080607020c0312031315050403030e0c150405040b0a03080a0206150612190f02040f15020a0308010603090614010905091b03120c0f01060303020322030b01 81
    0x2a0042607583e00d040c0104e45d4084000e9640f4400e0f41c100d900110400d42c0714000304200c0035410802c89015000c1a005000039601c2445011102e1000038280150108625000f1040045403018a000d81c68011340070006800d282c64001e0141034507480360002072142411440e040e142c100d00220050401c8010a072a00b4508000e010103400500e402583c0041030a80010101c4e0702500103241c1040c4079030242400340b500200d4080d80005a4000b40c0c0198001e00200032841c001d00e0302160400072038800000340740b418201c08001303005468200e801103800407800061106140001806441d0b01c00701c01c008445078240d08076036801c019040503001990a03001000f00703900a1348842d04580c02907c0c04903000c0d140303102d0001d41070b00a0313100b80c6666a840c0e0800001d10f030144034003148a025808124604404040003030303940c201c940c5072203901e804005580c592068081050510000b0020002d01c0f1565407410065102d4220005055110b0007500e0320014001080702d0700c4d0252980910040780b184d0030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 161548291 1250 161547041 161547059
    0xc1503070314070f030e01020c030c03130902040f030305070609022706150f03040507050613030312050c0a12090204060e1027020c0309031e12211b0a0906080105030303040c 76
    0x84e91414000e950300700440710305142d0901c010a00c52a18000660b40c1d10000c207080d800e09203150f8030118204fc81448103001a4003040a15400c8940501d480e0351108107a0400380010216900001d6000c0c007400d050f0f94000102d0007200e9419248000211000d07510b240602000351004654120680c10810180107541e85c69405142c01a00a004566500341c0b80e00c0824401d50015051a9011080328410010158045601012001000c10134800b40c10441c14100c1239004030141c0300207001c290b11001c1005038017a40202d1806070014014442144d46030403003151070900f990030050740b5050303503c045410502d0f582110002c05414503503038444245001010000e410004200303403240030401c0000c04c181d50030491404d0350303241000d070b5041c140c0240108c0b40ca000300d034181c2c000030b03c14140460030340050006010550030b100d6110707003001613803004040c81e21584007440d0884291004102400019840030680003507601541300d110842c1d80310401c16950740000c4070028040c80700b558042c4002d0203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 161549541 1250 161548291 161548301
    0x108040311010501080312071106010b0d150311040b0a0807050d020d150c020c0f0901091805060c090f01090e071d0307080c0f06030c07140c1503070314070f03 70
    0x201915001d41181003600607142500c400b81d005520303e03417000c200c640c81c8044494445421180c9420140044544541c4668544805102d080d000440210700c0707030800ca080e5013020464201400b0307030011880d22071070072480380c4000d845043d00803850703e107200c0380608180035404140c551910061400c42c3c036010030450000040c88049030040f10300800840000c0800c5a02811072100440100d048a031289c0020b00c2c20840e2001310b48100125081d07285c150710b03000d1101d810351700800000f09490328101241c044181d07464000410070300c82c2c1e030100601a0400710190100c03490031030300844468140c0c0011143c491781030040a000c452080003141c0850b00078440d1801c1162480b04420440464000003400c0c507c0e107034054100e50300a4500c000c2130b403401441d4168183c03411164942941042204401c890180390402403a1134550050103c03486402c00861240d03820003807002600907925044441990804d03a19a0046828400408442c50f1002c04241c41005195251150403000c0d00f0100c010f00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 161550791 1250 161549541 161549543
    0x101e08011109031b1f02060601080a1506050d152c01031505133906080c07050304090c030605031e030f250524010521010213180c0507020a0302010804 66
    0xd0780e8820074905501c8a034845d07104800054001d010285881d400250000000071311095a4074542002a00d5240c4243e00d02c0050340e00354a00940c44200c05d0120b0001081500b0602aa5001c10a8001407400000c048602007582403546a400c00386c225541804081003804020700a10b640405000d4194903a8815075100a6000011004560030348540b10602d11804050b0f42c0030348411104440e160443c01840c517242101e10b00c000300180783c118000d00300c40001d402c0703140d10b071000a9600207200041040e030f009400003950420500203495000b400a040c18070078540240160320280012041840c0c2c000c41200801d030246161128401510585902034404848040c120f2040354000c11a0000000141c502c108010b260718903643c10140b548405206c02404110580401800380d51188105c5a41000c5540000e4400b0851000080c0c06800340c41d00300d901c281180940001e401e01a600750010034102d820041112000074101101ca901c66240c0103500321044540030801544941d0800c0c2c0c0c05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 161552041 1250 161550791 161550799
    0xc1203050d1104080d0206040b0726070206042f010806060409020309030c01050105100504090f2703030507020c0d08070204020c0303040303020c0d05070201020d08101e08011109031b 80
    0x144a451191040b42e0110200b0041d9203000716060164030001c01200351491502c0c0028155031803c0d0f1f03200441c0304002006038080003034441510130001c50000f407403010181c004800c008580b810160095917841c003140d0540d10744102610300c0ca82c0c0600c07180503202c0e9103c3c0c0c8510f040c2e4240403900540722400301801c200d400180801c80040c0021091000d14001e85140d006142d8400740fa504c02030960780180c003c02d204801144d01045095007050864080740c44503940414400c41907043c10000780030012003044a4401180400c1d240203080d0099400c41e40f0a4a04100613201c400741240c2c4e07140206202c0790070a5444403250003080292001d010000c0c40100007610380500d81c00b040d41140c200b0740301240840d401040c9a40c1c5000c051185031902da0f0507107402402c0c401c030350300000d50764030b24280200140300075400400e000c40b03179820310f042c090f1000b802d5400811011440310100f0701410711401099510303062602801680c840100e0382e82c06030080040030b04580100e00b500c880c0440c0c40c80c0c030b684 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 161553291 1250 161552041 161552047
    0x30708090c030a0f231e07031a0a05090601140f03010f022205180f06040b0312040305120403020105040e090a061104090c020d050307030c020f07080c0a060c0c120305 73
    0x1140d40070400e1125440c855413030050a8111481c1c4504600801640000c000700c609002c1e0000c000c1c0040c045844514480c9000d01d0513595000050500d00d6036040a00903030890084482880d400000e140d0183c40c1510303040000340e841c0c038507a6840361001c0c06048002d0110200040305458030b490717565104000100001014010a5404412a4080c061041c0d00c0e405441e503022250400d40703104001010142d8112501908441100d002c100c00103012a681e00f11440c08264107486950044021110140440b080700e01003101065950300184400c4949118908080719a00020400d44040301e5068440500f01824011910100100103000c0106031080100c900081441c3d0702481c901800c2d0020039594035400c089400c0f09480d00024690207642c0aa02d200d11520791080c21030340c3c422a00d1400040c4c1059001d8101d042202220b04400035214000e00803610380e2004c80c5500701c8030803c07900c0c5020b150351031800341d80d590007a00002c4e0420750015420048041c0500001d820b4a100e440c14900d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 161554541 1250 161553291 161553313
    0x20a0b0702150a020c100207050108061c020a06020115081c080405250306140f16020705030610081e03030a020d061707060e0f0a03120302070b04050a0b0a05040803070809 75
    0x5541d80003c07503944016071004a0024081c2410b07501448070f0041c0e480501072441c149800a030003030b00081c05003800341d46108054000582d01203464589075500411041b02141d481c000280a0030900ea1414420b10071000c00168420f00014190b04d028546003106440521480c070a4810310001841500d50340180021032001c0f9003150754014004040c18110080d440c02c40c10020201c40100901550620082c4284520088100b000d10750080d41307031420303a00d00410007900701d040852170760015815112f01028000f0300c0c1e0701c00102d80d007954a1340d001c8a90096299030705c20380016840001203100e40003000401c84404480e001041641d40b115800305901e59508010510076403620311403901500100c505001c59980900c01d9111090126070000311014054001072168525200c003d08240b00035101c142c6280c026019034680307940140c0142a14542810700985400441c41c0448082e60b0900000c0c40c42ca84504c1401d00454105001e90b0441c0d441100c00d59141c84060f0601c1054410851000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 161555791 1250 161554541 161554579
    0x315090603012c0a1b0f0f141002120a080f0601020a0807030f021504150507091404020310051c0303060e07120903020f030406030b1e0906010c032106081603020a0b0702 74
    0x8140c101040d400d0034261482c02c2140c0280e45400c1e04443c140d181144402c11050070324900101007154211200b020360965004244d00e8204be00e082021001404101d075160150450710070380c4104400d014109076a9900401280ca402c621000100162002d200c00300110f4407031036040d0350501003801204d07800d80d06400508411081181d0840d1134200020015102041c0c50060b40c0d0020210b0801d8441f4038100a0300c600001784403024030b03000750380c0440018002e5940c0032401c001840d029005900340180c42d10f00b0050280c5802c400d502190810400040d010840b255242c4a41e41603035031b4503007069503602c441c0040c0c43c500205804601c1001c00b030344007120040c801440205690389000072010300160038030800c0071491a81d25a603184008103411552101c2041c150700c0402403034080c014244514007650240d078080c1c0095607480c0361901e84845003203142d02c0382041c3c23000041280c5944070010380001607900f50b404001d4005140c210100700c50700d2580e001d0b003101c0740300828100c0000c00008080c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 161557041 1250 161555791 161555813
    0x70b0a26040f03180501050a0f03060506070f0515010308030c090d12110f12040e1305010905030703171003060c03091505072705010f12020315090603012c0a 69
    0x540b03941014144540c00c1641004500c00ca80e0010054003804500e00741c0082c0003030145030070078028810f40346003494640b4800d5120704c1c0900001080c0c1e0382c4482ca1070506c804551001c0100715014484c81601d0310503800c2d0348000b5030481c0d074084400c0d803855880b070342610900d030042816250400210700311a4000391084c00818402d0030b150f0798601003041586a424078103403043c0062015030b00301c4100344c1c0310195803400b01c07801d44100e001d10700b01544428029840c5003800b51805042c551030000072408000c008002488068040e1b0b40310f02c100508103450b40607a0704196010032030321000c0c500c100300003801c7d50800c10448040f800d000a6198058641002201c440c0710800c2505135184100030040d03070010380d0900070044580e25030045844113032420742d901a882c0030b140d05011000d90350100441c0304102c3c002407001007000541d280d043c0a18070320710013400301301e0b030740d210741c491314005181d60905100d140d09003000020482c3d42600c0d1074080d01c545460b00c1c0c200c40a01e000309407900d00820310031890 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 161558291 1250 161557041 161557043
    0xa080a03030f0c030207051504110d0c0e0105100c1202160e1e04031b150911030c030f030f09190e04030f0201060e0c1c0e010204030311070b0a2604 65
    0x310b81401050010000c44a41c12411000e040c17050100002060300010007004076450600c081d0000d4446003495814005a600301c19400b03045000004100300b1000f42d0f0000300c920403541a05180d0301c90081158906880c140b03240010100352040d40409c00c0e0160310041035246006550701010310361040c041c24040394200d028912424001d001d0406290160090790201034645400d040c00c19a40080040d0f0850340d400850848500d4040140141000000c440c4440ca01040003e410903151651303070f1002c1d00b005140b0034010030707241c1035075410003040349202d500480c000b5610300108411001080e0708460301e815048080e00062000c0d1150342d050180180c4002c4801f480d4615061400030400800d045c1c0640840e41028000c000502ea800d0300b0940040c80c00255030741b10000042c1d400d00d02c203000030301d0491042c00c00d14080f44c552019802881070701e0181d6180b50b051016402a26903601c040d100c0d96510600400c0b41c41181c40c41880902c064440790582400721075489046100d1881082d14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 161559541 1250 161558291 161558297
    0xd0f0f0e09090a0b0c0405011709010b031005010e100b03010603020d0603121e2c0f03011b1202040e07030b120109030512062e090f1811030906150a080a03 68
    0x1c4842c080c81100404d60341d0146040d0525854a802c0c42d00080c8494a40a03400c1c109802e01e80c04640d410800303400681d8040e03005801c03940b03c944082040c0c8003414081c4524902800d542d00403413503060310340c81100140c8284403019440d40e440c4c204118021361003071313055110f617a584420110004001403010b00f6000c04540e540311a604a240000ca08a07200b000c04505010f15080d0030090b012070185500201c2d6000100f565030121150b01046000c5e00801140d036065180030402201c40d14150300202c1e80d148240e5405d604100b41c02d148404a100d10700807580e41c81500300014890034866000a0350f6100003901e520360480c0950301c0340d03083d581170540480118101190003402441c507003444e0b40c0e01030000c45280f00b03003c480041b0760388041580b03001c0b0252004011030030705400d401400000d00070508400c440440a40c0e884c4405242c18001c15103001441c1012481c0c05c140020609581c041e4514102511a540b1888031404200c0f00390034800703400c824203407800601d0040501c0044940d5000e61 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 161560791 1250 161559541 161559553
    0x1360804090222080c090c0409020304050a110f09060411070c0602060a0c050f070314130801020d05091c0c020103140a0b030f0d0c021e040606020a140d0f0f0e0909 72
    0x2420001d00f5a5090403c4143d025040200700022000010168004201950040e44649400c4a02481e62150343c01ca8000c29000000380001c2040c0002d00341d2a0034001c1201c3c120f2080c03d0f01c10042140900090140d00400c0b000218005140507400040900d0010321030070b01d8030008c0d43e9100307180c0c52203501c0f0320f02580001041165045c11070007100b288090600d401c0d450000103150003082806030f00e501808210108003500800301e02e400c00c51307524182e202c003900784e01c0342c1d240c035202d01030340c8101c0c1c020400c5410300022600c4480009a0130b603d0421481140c2031500c07000c0f800320b0b00300100c007900741c0c10142c4076050b42c05916004a51540070b10440100851440d241c0001c1c103280c000404110009a4002c581c80f460a03680b08903403c2025a04603202c80184400007081120a40c010542c00d0b40907203004000991181c000408019a40c450b0b00d024000050402440382c607201c800a80802040740f0307070202c0c1c068070b104074010500c1141908086a80c04801408a2000c110841c2c0308512a8041c0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 161562041 1250 161560791 161560807
    0xa23010303110a15051005061606110903030715181425050103020913020d0c120204050603070c080d140601030e030418090201120c05030a0e013608040902 68
    0x3150840900d0100100240f5898009565040c41418034100034456180c0e0b85c03001c54040e17160300c4600001480000d10003500c0302c84c41200c006031610707a14000c4038898604810303404847c1c41c91003695401c202c018065424078400e51110340b003101044542e808119036440e41400031409030813582803501d000e0240006010000302c1418039244034549a001c64203c0503008410f41610b0701080c40a85100380780158680c4020000b00e41d140786504a210305c0b242c0045003420021050f41e000d0714001005030b03620000c901082800130100c1c031482c080e00790031101c00c1000454150080341144004e0384980040341c80e014815680350122031400500c9600580200240004d5603418011030066100c1c5001440c9000e2501c3c10f82c2c0036800250101580b219210740e8000150782c0244200303172a02c085160103119000c0302c03003001400d540c01214000b041a1400203000310300c000502c01d00c15046040b540c1c1c504020210913000c445012a52120700500181b40c003040005494480580010300d40100003603110000c07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 161563291 1250 161562041 161562047
    0x30f01270804211e11090f220203070810050106050c06040f032d0e0612041506080d020303010603062304200c0f0705010c0f06020304081603110607051e030a23010303 73
    0x3448040f40e2048160b14148404108003142003500041c0000c40d0900c2000190308e1202c80e04039940d0b000e50315026680340000c1d50800401c00c030000c00f1070240100610380c3c0f0386001752a00e00524001103920ba10040010303000031000351f115807065000703003403404001554031441d0840300c0d1050350780414221030010100030075070010f40109503a2001c96505080040d480120202090020b00c094074016601301c800001402c03a62012015040103029500000800a800b07941c0b81d00a104410000b85480070024401c6100040d00714004140c1d80c2c01c4013082001c8003007102034107900c3c3d03642199032030603043c8019014200d0010b040002542c0041c186640504c50401d0070808294030060500071050702c0500040c01400d500220300d580000016280d0b01d82d400c29540c1d6014400c0c50b108010b914800903020306400c440e1400702c00041c4c40868441c0c2d40e442000311028041c035901c40010b5001040310b441c000b803000d40a140c1c8650702d1980090008030505e0b20800420038402526441203c120041c41070581c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 161564541 1250 161563291 161563313
    0xc0b070303050a0612060906021303030f09060216171222080f07030201050d0b031501081c02060a090302010f02071b060801120209040201030902030f01270804211e 72
    0x141200b4104007507032801040b14541c014285d8001d0a807540d032200c0500b0005a6030540b46c0781070002400c004140d89900e0090f2064480441d038a02050041c000028000c2c800160008141500d4407203200c0603190802c503038a200c010310243c580340d026404001c000416100090a1380140e08683c0c61f0001408010141880e291a003258000e0380007004119801d030000204c0800b241e45c20300e0070315a50442c12483c84001c0060302c4009901d8014003441100f0f0103400705040d81a11240760550351503601e00b10140304482846c0c1d00710f0002d60000c41c0010252801940702000c280d0203800003240e107910602480c401ca0303012400440d821842207800c03404110803244528050421b0b0b04151005504200702005c5241c20850028400c210440001e421a44290029242143d0107421110200b0100520502a1001440700c0c2d00068442c41240e048850704080100b026401101e541c1c03030141440144101f40f07800340d179000880007586003003d002844491100002d40d40446945110342c14914240d41c5202c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 161565791 1250 161564541 161564551
    0x30b0121020405040e0319181d0402040f0e0c06090d0b0c040603060e0903040b0d0209040203090a1101020c0112020f09090a02091c02011205060411070b060306010501050f040303050f070c0b07030305 87
    0x20b44184290091035100350b400556165035030805903d2305000341c0c00c00c030402c003142e00315032070400304130180c8056550501002c60250303208460910201c448013044ca0120380080039242000d90140d030722604a8208880105450230340501043c40015403619840d200c0c0c8000e0b6011210302d1000581008081da05106040141119410041c0b440c1844420143d4034040c4c0e021304904818001200004d040140d030444000c0711003e40103649038a82040d039147c452041003001c0c0d80441310301d404004c0b550b201107000d0782940350503155460002625503080000b0f40083c6803081d0a00c40401c80420300d9a1485040c502c510f0354110096518400d800c14024440e4041d6a400c190450001c000f900503a004418010f8840344650300041c41e076a07184c0001c01070802000d0007a81d0b802c00043c424140490f20000c0b034460788040d801c580e8266a603000440b21445084611606a4810310007400024131480c010710a840cd50010b25080231896200d050002d5095404810003060000300b5500301034150058a902c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 161567041 1250 161565791 161565793
    0x9010e01025401120504050606150f040626130501060f0605030402010c020312040b091f0503040f061b05190c0201020712020102010f05040b010509010905060a06030b0121020405040e 80
    0x14005892030452200b07040504114005000c81040769104044121142c0800070090182d82024280f09441c0c54098403010300404c4c5454014080780303200c008a80b142c0720040462850b180c80c0810403114007008842c907441c042c001c81e805030f000000080205001d0000344c440c140c1c200e007482c0f405608440b820390012501102c0c0740c60410600e03410a003904c0c1d10580a08186101202038030001e800c18001680c0034036014804100030960304504030291130102c4041c1d031042044608100d034030702c0c144050903241c800940e0070000a000903070040b9081009610900e030104494500110a1011040001c41300300001c0000c944c2c080119004218041507004905043d1002049600000e4030352549004070000c3c800c401c1c1025007164400d51100041c0281114100824280340c80c00a807410402c0c401da600c0303400c1100020486034160300c00c0c00e02604c4001c203a0380b80c15151040a40181100300d00050510080300989500b0801d04203581d80c0d144090900140d44a061004104c22691344030000301c0a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 161568291 1250 161567041 161567137
    0x608011d040c0302090903071a010503010b01020106030803070309050a080a030506011b020108040308190e16060212070b0612030a02010506190303050706021b16081009020306040b09010e0102 84
    0x80342e4040c0c0000292070b0180c0f2010400d5880741e507890f1640c41100c10042862800b045000c504c0343c80421514181c410440080c0008131580c0c5c012400e0718034900015200d0f82c2c080000c1414a80240c1c4140720642c818025a40305140940710101e09400103224800070a40380c03410070200c0d60b07000445a28110f40600480903012683e00000c014400c0200018144402c0102040c0000388200e502680c241c81035000b404a2b82038410030300e484545004050a80c07101c103440104030344e030001c141000000c0044010a0401c50183ca60001600d405808240c00004074400000c0344001840106031382402e90b0004602814000103120355522042900d000244800d903040c00001d03800390458002c00c0d040301026888010112401800e0040d01c0e01c800b4061042146101008004150581c00ca41102e010f4503045000901001c0c2035501c001d40095050300040c1c000f0b400140280300f110b03081030301d1000008041082007682c0c2d08a0b4031420340401e011a100c0c41c0100396000d0044503900c840314062014107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 161569541 1250 161568291 161568293
    0x309090c0f091e0d140609030306010c060c0504050a0321020f0d1206051f030f02090612040501140916080c0102070e130b281407030c11070608011d04 66
    0x49035016420510b03203d1900f010311070650030704461010404403001007850ba402c0300c1619020a5246140750310421034010103002031140b020100a503885040180c60704600003460383e8511008084000e48501400424800451240c8445100c0809188170314084800350340203c03042060b80d8800070310602198052500b82404e00d0b80170920014105440c100100f12407081100d40c030241001d500203540000c060a07103908503480240002d520054540c40c100269a100c101d92410380c03003048101a04a102007201c8140444550070f05940217019900020b00000c4513002286414025503075500140c0c0b10900704004401c6120ba20740040074400010b14550201c60300223901e54032a44640300c1152001000a038900f5045c81421450540c00860001c0e50729062608805090881d030364001d400141c0e20a0f284003516600c1040300300c00440d60040c00c169100c83d811009010010035000800c078042a800900c41d000700261809030205480d030140540c1440c4400e034640240c4003003c0800303206602480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 161570791 1250 161569541 161569567
    0x180305150612010c1407050f1c1205040b010b0d140103030203090406060305010e0604020c030c0d051305030307022b0606090609150f0b161407030512040806130302120307020309090c 80
    0x4505d00c400c034511944814250400031300701225407581d081e036800b4850100399144501e01c8104550324a5840c1e1b050000c0184004604031081200c0c01482d603061400184000c800200c090100703a18036800100e401e400c000340a181c648801c1e4000c0700964400f181d018940d140c54000c1602401c46480c040080b9031508078203203800311000e0f08060007164002001c1c40040d00c1401211080c04201041b200400f100f0900240558482e0b901c0c3c8180902109000c500342c0b03400304c11240c1d1190000c1c408440d003070050300450040c0b103542c5c00c84000322241c0789184000a2044c01408010072509400060252405140354160cc6803004224100340e404102405440043c4041c0c0c4295003c405256031a0304000e801c07010082d20740b10010340305602900c50f6014400d0700095050689201d04143c0715100c8054a840c600ea0045020b002501d810540000d45003183d1050804203071802031040394031030083d104058003558400d507058001a040064440d1440c2411030b0025001100106003d04d0914280350038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 161572041 1250 161570791 161570807
    0x90901031104060816030204050f152b05030711061312020310050a02130501110304060e031c1e090302010503070302070c0305120d15050901030201180305150612010c 73
    0x240380940c0c0c1d900050194a5a0340500040c0041400312000b4030050a0420480522844220302ca00d00340300001d80f0440d44c0e4281c0038000d4070a090040003214400d0304000e10010b40e00107011003055001011800070310611070f80400c0e940200701460b518401c609000d204040181c10417801580100b0007860140000e50181041301c500c0321f501da01c0c80c0640d100007800c0c5a0400c80030780d03555003004280305004006500a2800e0140d0180c3c282e00a50344034015103031056400c03002c04941e00306000030030003180100340303540c20b0140c000d007503410901304c08042592034440300840000145039503444007102d2160600f03000d6501c0e06805c10480b05483c660008002c1e2000900c2c203801c04d82c02098203000c1142005560014691060607030f060301d07c0010f089607843d001032104200b00760038202010643d22812010409a640c00342c0001066070850300107581e0740c0d13410011100c8043d8404000004941e0a00a164680c0c00d007070105001420003000304082901355151840450345000c1401121035088805 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 161573291 1250 161572041 161572043
    0x3081e060d170708041403010b060f070303020d0e03120f0115051810210e0c0418050a11010f0809150a0f090501050406110a02060a020d02090d03020a020103060b09090103 75
    0x1c0c660000210310700600d0304880c1071060002000042024010029190040c2040c0c65108201e19100200e440405081e50300b03013903649803c10070400642541d80c1c03a0750000c080c1c140c0241009450030b01001e003c401194203d4044034003035000460302191180904a04a400c0f04039140c0818855060126141c0206103504110381480b00c000b0708440b070144240600360103d1801003030305007510000325028240b03110401105a483d03e01541c840c0200c22144100754402c1c40f008000c2982e1382c44042840010160840c2215507603408010080024208100703000d90244111741c10b55000480c0b074005407400c5080a0120244a0902d0800c8016000082c0f2030515001c4110040c0c02502c9280700c150007001c00003028490300381001d40e0002840b2054010794040c0e071003240e042000c001d10400c8260607001d1320302c5000050b000342c0c0100740740017003580141c40a40d0b10100010300c0c2400b0f030000a01354142c29402240560009200341055681601c02c0070000d103030a8802c0381c0340400c4000051281141404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 161574541 1250 161573291 161573299
    0xa0e0609040320060702010e01020c031c1d010212010b030613050403050408070906050307080304030b010e0403090f0312020c1e01051b01020309060103140c100309141903081e06 78
    0x20005040c0b51156000b525070700000120103900c01000e00240351501c00485100001d90300302500c00a001d0014821a035000344030001a50800d800404002e075042d00907014401c40c542c0720480f403070f0000c0010031025203110402c1700040ea5515890100c40788034405921440741c101d802c0c410442c0f0f9480e0480010442050300c1c20000b100d40d610f140594440c092900940654891a44041035040b902d034800b0054440840880b04815030390300c10305549100c3d60100074900401e9100402035a000b80c5070054205100f8200780c4841e5440c0d114180180c0c07640e501c1940c02030110360303980c0c4016405004003120204c2c259912903131200c22915a1030078401c400303c8035040101c0040c0c0459074002065140e418100480d00a65690800c2002c06565000038082590a110490700e00c40c040300c80020304542422002d00003614000160109600501c0c200c941541c5090490503006400b500a10038000512265200c0310f91401c0907040003050302d00f0090500380181d8440103202002c91458074101d0340003004031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 161575791 1250 161574541 161574559
    0x10090b101d03150a020408010501050306070f080702030d09030302072a150224010501170405060a02090402070606030606060e06040803031821030717060108040809010c020d0c140a0e06 81
    0x6000c01d18000e070f440c0c2c001202c900814103002501409400600880f034902e4004c2c01280d0700c92080684036602664400040b82c2c8444900b000c5a001da01d00d50750080c0a401a01d0808552005850513203030140c0d002c6002a90003e6144100601c070901003044514040004100b01d64804010003004124000c044403040354120a81c00d2620030401c0d5401c2c4264180020f56600c0b0030703200300c45441401c2c010203000c604001001c50401d115810b51910039034104006100e02d0b280d40040000a42c04054010b801c0303a002c21000010440b00c0c007134940114400c100c0054100e20340440140b07086854501d4a10039001000700700001000041540d400141c0054402444640c01e0741e11490009440780144401940c80014504451503a0103544240d07e0b58a0300142000c00c40740c98450301c203080320460701141998000c0ba01040c0310324064202c000040c1000f0015072403e0b00055146801450202c521143d20f160602003c6c411242c0b114200c482580e03400982e50400000b41e0b10401c0041c0054010b41610b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 161577041 1250 161575791 161575847
    0x90f010e0a1d0403020d02060c03040b0c090409050606010f031802040f2408100e0a0f06110c0724020a031d10030b0f010e030d030f02090910090b10 65
    0x900040801400d001c10161040c4006044074050840c2c211010303005401107040110300c0d603002190701489139100b05580340c0b07541d96540c2c46002c07428014198981d5500c00740012186501d80d4440c00303480c1c5e80a400200860714041d40010700c40500b0b05c4880e820941001c405020040503240542903082d07040f10080742001d2089803040040c5100700056409901e4075141e003160020340d5495030151646a41a04d800d03400f0440c6010694400d009407900c02e511440842d00032405e15a842140316120300d80100d440b003041440a000c03500205003000b180c1d0032030300c8104501c0020200d414000c0c0c1542407880d000903010714002c5d4481180c69405414000c088410105a601d1700c564240300c2a0001e14012f90380410710b200a008194516050b8007031407500340c80141ea98003400c44105602c20040040090300c08595044018040c840640c107941a001d01c21620b0550b1403181251103141450599414145440030319010f40d072040182d18000d000e9564440d44940d4844040030115240700c901c1100d000b61 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 161578291 1250 161577041 161577049
    0x16050a0b180402040609180b0f0f010e0310060e130c060521040327080606130f060e100b0a020d0f120501031103151603090519050114010b090f010e 65
    0x80d610701d620500c00034021413600c0d04107084009481a0401e410303d0752000002d40d008aa079441a1503922110790500c1c1c0c011854070701000b4040c040e061400390840402c15000c0b0380b03001220030340044400e0b1140409e0045c07800b4011030580c85448100e00041000103921003d420256034000d03001001800100c3c80004500c61407460010014060704103000e25150070001c00350b05d51011808200001c544075541071508880214050300c2ca91000350038a03807140c400b0032000d1441008520340301503d410825000d02028490f080040c4110b403142c400503d031981d504d4803501581d8104252031a0240004545541c1c0060141080303541e0341001250780031b83c1c40d000d650382180b1440a8424030b04000c0040104210525079003100d020940440380083d4160070b0071485900200c54041a500c948501420a180700e6080304546500a405444210001280d811001d8207548420713203c070b0391680f4103480025000c2c1c01250042416450260030510044001810b68200309011410004600070050076691 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 161579541 1250 161578291 161578327
    0x40312090e010609050a060e3307060905010b060316050703030e030c01060314030f090402031017010902031006060203070f061e150b040303091701090b071116050a0b 73
    0x254004500100790f075204001402c5068500405c1d0255854500c0028100e003d5070041280c5080241118034503180c0100269800f050040880410309060102079182d0000c180100b028074040c180105018940381000b0f407d42d11290380e4540200d0081080120841d000840c0c42003c811601d00255030300e03070747e0604034080d101508558089000005550b5550f8805601039000c8078842e119080286002607041c64582c0550103403101100e0041002845a2a0560085511961441e030f5044500e840707090310781000900950400e0700d2b030f55640040e400d514042007052500307605070788140545414020002c0d240e000300c50000381102e42071a50001000384507040425142e0040040b1003001c107a025200c0060031215641c4003c502640b200070030421760080032a800e8039015107c0d41c8400c2c2c074154809480018001c0f40004c155038806140c0002103401c1d09403409080541e40c1d4038101c11040d0307880c42c00c0510007608075050944510381003101da2600c810150440343c2044c0d4442d26281107000e1101460 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 161580791 1250 161579541 161579549
    0x912030806060d02160309090e030406030e010e01050702150c0304111c060c05090a170604080c030c07180c030501051309020f30010c020309040924020c0f060c04031209 74
    0xb400405d4291010741c0100d03185d0340640c081e40c0c6209829a550480c0da04803500980780c14060b8004001c00d00c240c9010f038101c42922260100000b40803900000c0d407900b101e400f5100d82005030840701d807400c0b145580700a40c64011580c402c109195041a968081039103819111311802400694005000e42078401d2031704e46125080310045c41580d44005c0000d1099011100041c400d074a130120104040c50032010704480400d10000a140a80b501d461300099038208109900c1075100030810040c10303d00c180f01d500010452085007200c420340d800407031002d03180d00071914000c15280c000100801e07a9034210841c820b07803115400150a00840c000304031010110b041c0603820540d4880304000c003032486a611000c04603502c0405a9100908030b482c0d090300d080441e4500140e00a0007441c0c518070b4694000d000140c45400f0f01c1d8541e5161516034a01c85861610b040c507190390100300b090b2000d20900115400c180c01034058003191511441e40e201c0c0e402103020142104078288200d1901d180900d0710300020b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 161582041 1250 161580791 161580817
    0xc0c0105010603050610180b0c070801180c120b0606090609030f0312180307021905130e0f03070c0902030a02071703070e15030a050a02190e030c01091203080606 71
    0x2642e100e400140140c24180c804a0141352001801040940710780b41850030542a641d40d01182843d01420000c03a82151000281da4013807107000060298003449040e4042100a181a680100ca07040c0040702041c0780d84803200c0f4407044112100001c02d40c17040c06a000703004036140c6417507005110115246003e000001c6c0e405102d00058400460030010181005101e0040802d40540e1400f0070440381c1c4d400d004040c5421760041c450600185004403004650b0800d82c9001e2103620ba64000040e4407500c0d1081307102c8410f540f84840c40101109000b0004202da5103c0154039001c1d075592601c070b40b441c0d10b00c00c2c074214503400300c0440e1040096404480805800000c40c89a041d82c12a02d501d050b40700b941c100c40494480e01141020307040c8000c0507043c1c440c2a035100d900356552010002d02a02008007484441942000300e002226150a07003984d852501e13039150f14035003001809052404006007400350512000711400c000c8201400100c001d040d40c1468000c007607031190300120342140103641c0a5104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 161583291 1250 161582041 161582051
    0xc0301020a09030204240e15100c0b09071206090203031e1c1118030f250f080d0c0804030f120f1701050f150408060601140a0807080c0c01 61
    0x48954400c5a1a06907030003114200103c2006502c43c42d01003075101b400100e031079120013081210351000d0792015404170702000000205102440024820f1f104040040b000c203220190120034000082d1030325a01174800c0000340461030904003002c11600305002d000f00fa25888000c00002c54405005851500d40c201c60248003550300340d200d20505070044086982ca0329a42d910940c2800028001c854020b078580c41103520f09030784090251503000d0208a415010310030007203a5803540c00200301c0543c003c941c011114840c81018246203c42e0101c6901128803e070b0904406d01c16100041203800020096040c9010301d419246070039100d03801945d00c0a400c00154160246c140805843d80c03201c940c1d03c9985d145040c850183e016124a0764007003c5103902204940140114103081c0ca40c1718011034002c0c0380c7d218268900c0e404039a154020340107a00290815801c6c000b5550304900a440e000e0042c08199040c008043c400038204140140007108114107400440c0301e40314100b00f114180d80c0803000902c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 161584541 1250 161583291 161583307
    0x150d05030d050c07030f050306010806120a05060a020d0c031e020703090f08030a0306082410081f1409030a0f0309141b0406080303010314030c0a05150705030c1b0c030102 75
    0x15041e004290b040d17001c11422002a02114030510440b40f0450781610759041036200c1509002440e82d0060504a03a881b451091101003242044028400d0890120250741e41c00b00c4500b06056134034400d00d03481414104078040c0000020404140054400000d0050310f0780700c203040895810825902204144201100c0072890403004030051036110119102484171698841c2919903800c0780040b60300120026580d400c00302055001c0740c030b4008031842030340041c0549540c4240d0409002032044880c9501c030001e0015107007120301035210107600400f100000c0346003503080381d500c9100e140b503c0c0e02007240c26581200a18080e0f485142c40d1038020101035424000303440700701d5a4180114007019400020503924401e4689802000b007501d1144010310300f9a442d543e10358100c10990010310f402e41c00244942d80d8103100803c00511524010801032011040d150503451003c00c001d860b01041100c01c10801041200110032140c1e03091001050301010382900e00e08500f0100c0122901e5459400050440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 161585791 1250 161584541 161584561
    0xb030c100807080c0c0d0e010207090c03020306120606060f07020a0f2904180b060702090f01150309020a0608040c03050d0e030105060406060806060a05040b040b21150d05030d05 78
    0xc1d1190850342c076055041d890321303c00041c1e80d001c0c40355089182e42c002408500302504c160b800ca942c45606004984c1a161201640410313584500c0c03102c4002980807041004502d05070700034048100c044405401542020004030303110b4482d0041c5034400c4540080c494086486551240300240800181150040d450300390707013028401e01404444c09190440c0000b0650600c200896085a20744444160420304a6484001800784209100e520090078014480175032507411040d441400c1302e42c901c210300d40c14a82c0c0b07903e101007850140030406240110300001070f1601d180c0e02c0d007a83c8803402c0030b512543d070340c0c40e000110f0a20380d00020420301811311031000c0a60080c1c00d001c40100104c2c02441682d844406120440795248200b600040f041d1010030100e041c6600105182105890705e1403800b602c6451590300366000360300030280d5a0000600200d516107220740d03c0000c2c400c41005250f2401e01c80c2d0449a1465100038461003a0320520f0f01108021080040303078802c0d101220244418940a5088 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 161587041 1250 161585791 161585807
    0x4050f0709050a051b0301060c0302030c0607050901021006061704141e0705090921070807050a06111606020c10231006090902090a0e0f1902040302010504090b030c10 73
    0x2c400c0082c14100070034605940d0842c11101c5d00b00d003483e050308681ca4030100b140d60b00c404c000d050701540410041c01e01d1810091101900c1003000d43c03a56a903903e5400002490145203c3d0385044007403403c41c06104403130780302041001004c6003080c00d103211303101d07030802a07400034200050581912500286030118458099940b809115142c2683c3d43c0a0707803401803141e03c40084454031881c0d0007240b520843c01c00800c0f0707013000c008503041c44c45040170301e907540e120b5240d400448156610361003040b403882080114040c10000241c170046450900d4140008044005041d0f50014001038001c14a440764105c1000094500d42d980c1c8030602055604080a04120085042d03900c204130303454000481000d4443c3d902c004494460f5204045203240000010007504202c00540e440385450400043c0171806044550044081201c10030341410301d100d4450fa12042c81c4190307030200d07005000030001750780c20400761400c40e001c0380d0740842d003100c40a0007e410202ca4a022581c4007203184d000110b0b0755406441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 161588291 1250 161587041 161587051
    0x4030905040b0d051510030503070c090c03060308070314090a0f030c1202011e020a0204050c1b2806020d05091b010206100b0904090506011512060609060804050f070905 74
    0x420481c682c5110280300d07541050800283c00741d0710040d00c0303031807140114440c1c503440100b200e20986802d07160f0361030505562011800b55010000f090781400429800d200d1076500a4207070a00b04640b500cbe6a035184954001c840000d814401203201c6820303c45042021a448480010b2054204076121a084000900280410303210320042d00c0340400c510400014204210790141c540d035010780d4a100040c2d1511040f620740100714000c0d41030f0100140c4035401014010791890492544801079900115083c2c0088600100103510000c1d03640003c00d0540790640c147e44070000d101102881070b06084010f0b200702e515484a041c80d1008105817075401046a28011070301000981d4003401c50b4004990b1400c1c01d88032188007000c1c03c18100f10340452a0000c000090b070251011413060b1103038980301d040c403009a00056500000801000100c1e0344088081280005545c081180ca030821700f0050901301180900000e0140c000c02090500c6001c11240d40301d004800110b940484e1203402d01c00c00f802c816a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 161589541 1250 161588291 161588299
    0xc150c141005240603040b041b0302041a010216050108070e0607080403080a1803021011010b04090b0912030c0901050901021203040602040501080a091a06130e030a0f110601030609060e010504030905 87
    0x83c102e4180380c40011030780201e8100c0042c0d88262525141c081c45401d01e800c0e0040c02040d580d0000005880d6409a201c0d2900484801d10300d000c0207400190800c04500515085110388040c140040d0303070000b00031030b007200b20740c64154503401c103c101140f040c0c4a042c0002d02107080204000007085a03901c02080d20082586d64201c181e0360501051205160340d001c0258000c4e40c0000070003007284254a40c1a43e45840300c004114000c41501240031145035820985170ba2283c1020456502d400304004900b8052201c0c01a2540c900708016812a0040030784d050304000001401c8038450381b0800c0440d00c04000c6440f8030f541ca04140c17921800071b41c440d20405021600d43e500007810780300c0e0352042040c2d0b650000f44000b40c0740b0028100700a65000140266446440e42806140c4251240b25884110240303000840c2d845500c450042d221000c0f520451003007008040314008051804186070341102c0c0e100c0d00104400d42c0624251029000b4403603260515861b010410041c1039002e090300040b940155 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 161590791 1250 161589541 161589601
    0x90109081c0b03030a020a0b0a0b0d0516230904030c210f03020703020309040b1203040b0322021f12050f1b030106090b090d0606060c0c150c141005 65
    0xa4281034685c0240c0702c0d0368015030403040c04103000c6411007400c07541c0b00360003070310000c3d052045000244041c0054030058510303600104241d0040d4024400641c0076240130f009400340c03260540c811011081c1c2c02d04140c1d00038a98400800c0426019181d09142582d0000400400da07154840140800d0060109000021043d00b88507500324068400c8900640d095405146000e4090013800040d1a450840c80d4006115400c28030740d00c0c0c02440a00080d0030a46c03a050f9407410103084a140104200d1035601d0342c1c1a0b41c59180006a503904402c01c0d152541c1d46001c24400c0c0b84040a071444c500006e0405a11824038040001584035540080d114440440b0007031460386e54800f900420703010900900006c074164201c00c0c017a0404807070241801c0c03480100081103421281d40c0c2d0344180c2d0800e504c07500102d030b01d0b00d104104102d54428024041c01c90280b40c0000d240030f20303100604008080c02c010f840010614030000c8213840502c41c00c3c1040310441000e00030380c00d0520000d081c0000c080c00c0e24640d80307228 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 161592041 1250 161590791 161590811
    0x30703020712020a091a03030d020c072408090c0402041508070c030806120f03070b010302090c0a09050103020f070c080d030c0516062d0f180f060203090109081c 71
    0x110120b142e58580203018040d01c581465104001030080c1c9907800651061000429000d81e420001416403940d42640540c9464500f4070140c0b52880c0b98000381c842c0601c50a1410880750703c40d403210316400b861328004429840340d4020341e01704031050300c1c029001400040c02164104000e00b0300c8503080402e030703282d541075901d2000444000e00000d50080010f44070102003802c5141c00070440c000c50f55241c013030792052000c20b030119241d50702500302180c000d2003c800410075403808211855110031400e41c19480c0580d600c1000b4400440d5016031410303d03501103111000c1c00070920130b9440d840d40c40703140341c42415203c0046903078440f0514010390000c0c1c10902012099442041510191120000c030010a043c4d030741d89000180503240d040e00703000951a032038400305c0b5401074512000030b001c2000c00036010b030010441c8400d032081018020020b5810f0214040002c009242508080350032610040e01c0b500c40c1c0c58200d02407c5005c0019080910202c0d41c80305920443e081c2c200d802d001440c0070403184000e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 161593291 1250 161592041 161592059
    0x5041d07081e04060c180e010503011805030f0f070b04050a060c0302090d080c12030709050a0905070804020f1f02030c0601060c050a060903030f050a020a0314060f12011803020307030207 82
    0x2c0341148a040d40103004640000c2550f046400da40c6624200000b10040030005006002c043c4d40c000041c0304000c100410141c10300b0f210340b60000204125802d184001c42d25125903d00c6054148070f072180d8000b4614100c1ea06050079520381c164400c08940c2a800c1c07a0034440d81d150306c1e014042d41e883d03260030041031300c982c000c0c821030340b03109005450b00341e020307907980c6500103990000e07001c451003405401d031201000c90780301c00254800c0c9040d031218000241404280200f0a580380c110a030340e58549010d02002c1904804000d5005a0448007840b80710302108c04140e020400c10b00070a1284404031180503031940110180c408641442d04546150f0f0381c40f1301c110780b03400e22075202070221340207241a030010940d503412544030603010313007004541120303941858030482e141124a50403041c0c1c086066440164140202100c41c0400c1000c1d0b040e500b8043c00095494241c171541600c6451040e0030a03110741030a404c0720303a50080c0d8859440200d1841d0501030345a40c0704075422401401034010225201c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 161594541 1250 161593291 161593321
    0xc04050d06050a0906090f110105041a07060b13060918030c02010f050903060c0705010e01050702030406050a020f010c180e040b04030e1c03020d11010b0d110105041d0708 75
    0x100165240405600e4100082070040d1110282a032694079100100d401e40c02081c6c40f680c4207500150b03040c2210708000b14507160b00880340741084010442007049919a84c00075004810340e0300400d9803968207103010360040241240300c0b40c002c05603402109074591143c0c41001140c142031800d2014800d0038054610072051a0402408100d807514003401552080070074882031005410210300d00500c241c00607150003c225130141e2061400600b01e03041220030b02801003500001402440075080005029460340590f005480400501050015845100304081d0b14542000c81c000c00c440401128010010b501d200010712a41c08100400140d1603580c00e2110300c00c0f9080440f000407625603039002c0302c011100c1d0030816800352b980003a0041d00b0a40354800304110344a60001c1001c074192240103845044462151070a43c1d1400181e0030064403280141c8070446d0344a1800307490341c0340120040c3d4090059030000d244030b0300450100403e0352f10825586025101d50784a800c0980d4480c0e01804c0100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 161595791 1250 161594541 161594549
    0x3150302100e011407150c11061b0f03010b03011406310e07080613090b060402030a02130f03061505010e120102190207140f011d22050405060c04 64
    0x1035120805502041d11824056800b481e05140c00d001c0c411841d05460915000340c44140e80714042e21a100341e06c045075218840d0b0115103402c10034181306010010302c3d160301004240a82e1442c544851165000503142151314502e510500d45032203585038110340009410034014034000c4814040d0302d00451800b02c00b074800c0c42d594200c02d071075455802d40c8078004140c01c00040082c0c50141c6d40010851080c00a401b910403d141d41d00c040741481c020b02000f9040041f0604045654644002103000c00e420b12030040e03025809907801f50342d0740c0742c08040360000d2094042344032400c91003402c0490141d9990340c135201180e0040d5828010b4408a884c0306010b50054428140490382a46001615003002e000602004030030308001400c044261000d94904a0000701e00c40068020701000d0160b00340c500c10141614005450142c4d8199840001030b002d4241000d001d070880c0c00c400a1171910340d441a03c001129400400c00010101405083d20060b107402d450071a1140207580000d04907142d2001520215 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 161597041 1250 161595791 161595799
    0xb060a0e1f030f030804020f090c0f070203160e18032a0a0204051807081504140109050703030302040e09010c0f030207030201090b090c09071106160c1a0703150302 72
    0x1684071403485403281005a45549462020340300c002002c508025070340800d0303900940703c00c4010700d014030400444074280e0142c6842490750100380403018403260151030390f007101100b07071594408441c00020720300b008140040c010441d03d55404920304841c001c889010b8140220242e1301c4444551420f52280070304144048408003101078124403c0f2401c0791002071080039400d84445d42d00726000314003515000c031005020360002d55039155002604103c081c0040c524a009000042c076254141040ba500c041e0000d804410007002a40a0768000c1d4031030f5a28603442822150301d55503d02d4041d0180d0400c1c45a150f54128810000b90859018001c4500e00513459490405001d8056426002500201820740840d9a24964500080c03401981c2c240504200307030003000580d92400030820580401820102046110b0140704500c40c800288213401c240044015034485800d00000c6400108030a0040d050003000800d48560103000100240036032281d40d0f0038403900036118186504016035200003500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 161598291 1250 161597041 161597069
    0x1060c020d0f05010e0102030601020d090e040311070e04030c0201080a050603060a02210a09020901050d0b010311060d090f170c07032d0804080d08090a02151b0601030b060a 76
    0x500d071064802118501c64080c0d00c0c0803030501d40314903084400b40c0703c03060000c1c2c3d0300100f400300940c0c04105d081e281000700e190a50240c0d0900110380003421000e84010b081c03111030300c5c0d511401141400080003a044047c01d52070b0070301d001d080041c6050341456040c0d02181a2030081110b6103002d000d038502c2400c015004080315201c0310b641f20000c0d8010703074482004e001410700c1c03019035904d600000d50013003c01110109444040f401004484541a40900e00c06c00c4450016000549032060031811260884d018509109074078000c605640308080744480480c0c98110365904000d103d070312450044e8010310b4101c00708a15613800072390302c2c81004582540d03640f1490782000066001824502080b00050094021021140085405900315101140c100d900030401340450842001b00030707502c140754070300302d85142020030781180c40703042a60002e13028071f00e008a04101b03850640308035048411a0b2600c3d202501c40741c0b40301034030340f582804101d8440800b01e0210b04c9915201410a098a400640d5000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 161599541 1250 161598291 161598293
    0x914070e0904020613030506010e1521100203010306140604020906090409020d0b04050307030e0a0506040b030a1508070f0b0306062502060d060e0703090519030306080d02210301060c 80
    0x150118001c200f207a100404220f2207001880140c03c00c00294451001803110794103080d60380d0580d0394010240d032894402c48801d42c0c500e80c1c40340e95200460710301c543d200c2d065146042001d4100b410400d11241c0b00c90001000100f003203c9a80044a401d100c07010580300340d00ca9100f000203030f20602400d1503100d5820722181800b440c00b43c0c020411903100522075484103085aa80c0c1c0d184103c100c9040e00c0d0350304049008824190801450381e000c55089409481ca1783c24200065a24040c80c0902511a00044000703840c0b00000c0d423000c0001e59005909502450340e0701c0c615540c2d4045401811851000d107200002d0b07101a1406490092100405240c20962003100000c0c6480303041487c1010100507255807000341e200d140003404a00340340d04d80480c80508104244140c01030142c481002c240c68040428045140880c410030502051800304010224509044014160300d8100607128085d090345800c40030740002c2d031041c601040c41c1c08000b025110240004060000b4840d10340402d0a11020380 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 161600791 1250 161599541 161599549
    0x907050d14071d09072f060421090603050405010f0e010f0c052d071202010204051807020a060e071701020301140d080706020a050c0f07060909060b0910020c190914070e 74
    0x99000d641400d48040000c0341070446c8507156801c21054112005100038405180c9010407040d483c84400c0081c00c9820000270800702d9181303c1c2034105655203021404010083d001040c140d9410541804026042c2d07212030b000b014200003400c00c080c94021400407071401103007a650443d060344900d4510070308078051880041c0c00d402a00016113000c22000780020850359207018107071481e600050310350b0300f80410b0064a0004440000c0031503182c10400030308950000b580804168001000714650005602082c5049203a0f042901c5001c01c03514018030f4141c0550155040301c0644242901e6980c007542403101d41c5403c1200509000002c000003000714074a0303002494040020b14000d8907000484151318140b82c200b0000390740302e4001d4a07040080d03c3c1d221036150040c0858034420400d4a1030f18125900a00c5424440d43c01600035804507a80940240041d03803000001070070f00d2030010500d000b1b1004550443c000d8048251501c120401c0c00d035403a4803401c2c42404075440344c07103624842030200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 161602041 1250 161600791 161600807
    0xf02210601260a1e0b010f08100605032518090507090b0d0602090102072c070201110406180b0a0f0906030b0a090f060302041b120e0c0907050d14071d0907 68
    0x5241301440241160011300c034403048034000c01c2c03c3e082c481805424810070300d0501014440d14070203542841020701c020350380450b80d90706846401032814400401da40e0b0304101021154003551040405900c0f10045000b10f030070040343c4e64070903400d4030201c98030340c0105011101040c0c810360700300c1c582e003542d180010403c3c2d0050034010014011070f01c80640d81d1031411030040c400744042400b1041282c0c0c00c0e180e81c3c0d81c13884035034220481380000d0240800300d031044001401140f2a02080190b140b0b100300e03448030307070400000c0502a13030a1259610301c0000c8014207800d10030b00000c3c00040f0041800941e103403082c0318080e080305004015140311031030b0001300300103001102250794046945079800001030396984101d440402e8080e440300441c501804019042c000c015150004442c18029640710789540070030000001c0c04100d80140d015102c10b07404450034040d2140e407202d01442c0001d519104c001b105d000a03c91500b0b030359608000c0c4142da940e4a800c49600710015084075070301010803000c5000b803001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 161603291 1250 161602041 161602073
    0x30f030903121e060d02010e060d0b1206010e01080d0804080306130903020d0e01030204081005071b0f1104020c060105060d020f0f040e090a0f0f02210601260a 70
    0x85034180300700010030b100c011000307070b8401000410030207040c030410040c00901c541c050f41c00c0710901351502d90341d00060240c200800c4100e114a800080c2c03440c0155056000310302d40c0d079020348007011050188030240c0c0ea0750000c0c01171128400c0c48100000d030360140000d001c000340c1c1c910b903965510703901d803076403400303019000905050382c070049800d0481080200f501c80c40040f58001c3d4010821540b003900d004e000c00d0050b500c1c0320704040c0100400d1202e11000603000c00b8100c01c160300040c80c0d50f9078500480d0f10b114002d4148455007150000001444044ad60210001d40180356405010380071900f000304903ca0004141050f41002c07004000ca8a41038001d0030022124100141c41c1c0031075458114190360040c0082c285220001ca070510001500c0095141d00494980080c6021041900c411007040c41e040700c01441000c81c5c1c0018400c40d201c80e0b40055600f03006a10000074245600d1480d03444032000d0140540341918283c000d070003061800e072480c03032410502000d0043c0103400d85880e10403080c4114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 161604541 1250 161603291 161603293
    0x31204031a100806040c140118030b060402070c090c09140d060c140a08101a120601050403120809010506090114151b0303010f05030d051210030b091b1002030f0309 72
    0x2c00107045541400540d1040e480350314441082c6083c181c1404840298040c210f0411164541c4400000074131001c19041d02d4002868140d01d07134602000502034482c02000810917083c405001403a511b45170450040c0c124283c0301c0307500072912041c080015440c100c07859940205115045801f09000340d1052102c0840351402081d800149182d84200740d101c08684c3c8000f03007000d01040001c0e40c824155401500c1c0c0040320b4040d80c60300000c0178034a40034100100c0903606a29011a803141e0180044070015640310b4011041041542c0c40585295812031f14130b2159403c00313001a415141c050f903681c0c103a445011415213a92040301c14032000c100050941c445a00c01046410200f02c001a0654096200c8400a50340d941c10040e2802c100c1e5519840783c1e0207030703000000d001036881c0c02a05079000040c07003c44600c181c0c1d03625014a00d9140f015400640041e00310800e21030540b902080c1d90003130100c450502c020136106002400140d13107400341da80c801a00f090203080322807111180155044a4200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 161605791 1250 161604541 161604571
    0x8030402030705040e030915030c0304200418030206060f03030301121103030c01060f0605030c0405010311070b0a0c0306050a0503030409020a1812021201052403010212040f02031204031a 82
    0x180c0464100c0da05840c0414240d800421002c01f145841da05005601001c8084a41142000032030400180401391000300844d00314400c2d81142d00c500c1d80d05071542c4900030030a21448080807d8002c221036485401d40040c0a00c2d0700180c007500308011203000700385015004510b142c1ca8602104102514190119121442c078104170032242d4040010b0711801184a0000503000e00d003007880c5841d00329590144092000c14006c12141401c0d010a45044500c282004601042c00085100300d40c81004401413070b80000006001960b46198080120300259440420030203844601300701215499226042d4541c0c07040006000d5005690040c00c241c040e40d0500200700d205018644045010a82000c6507045405044000b94a000c0501481e030f164080c00070841401d00a14400a192003c8216840c41c1c3d0b40c81c2d070207441038400750304407480081010b514501a00742403428081c0d0914200c000d0340310344541c10441911f61004402c031021640c0c49800b07205d09048503900d15404980c001d151440301c0c9440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 161607041 1250 161605791 161605799
    0x9020102100b04020d09140d080403021b120f01051f0513020a0311070b1b0421021201020a081005010809030d0b040902100509030d0f0f11010b1009060305150d080304020307 76
    0x94002c007088244269690030b01c1c1030104907424070300190b4050f110100441d1100348002f29402268001030400c06c0750040040dd24503030082041001550924509880340c41c1022004010660015004000d803291410b40000380d480c050001e9205402881d07884200d404181075030403925801000003004030f080201c2c034800c848004100c1074204540580f20f000001d010030103015418944082c0e91040304500c207040908007007007050006003981200940c0038501c1c0d100c0c0107540c0c0340c0f07030502840a8104001d41d9680066200204101d00c10303280d9120700c030781d1408040340940c0280207061180003580010360500d5410341448001d8809400c01a070400d9888101d0030140e190a404c90100c0c0400e91502981c0b422500141480d2550071201ca0703041000d4035000d010520b40c84010016404004c1c41d00d00071104100844a00401400c0d440d04e0388100f0410410704000d400c4000a0110340c40d54034200f00304c0d03a8a4112600820b009007105034445c000b0480e10700003602c1c07070004d15000350016007140c001d04d40b5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 161608291 1250 161607041 161607067
    0x100e010b03150a06061805040c1701080d020f0f060714073801050906040b010203040504060611120c0a0f0503090d03090515070f020402160b0f0103120309020102100b0402 75
    0x96440d0b902c0c000000b90040000c841038501405006010314500380d605615001c10740c5129541e1409540c0c4140d40f24243d200350070f0310031511019001c582e880303640324a5960b02c2c0303096940c14040d000c0c400580124040a00f29910105101e60340200031000340140e5036641504441107828a640c0030f4000c0380c14807505002c2080123816460700c4480080b1b42d031001c041d884020b280303018518050400041035a00503c455180d001605030800002e81e004030b10110aa00181e003140187e812141d00685440c40c00201254807030a4070031401089400e40f01181c104980003c01031040d90141c40840c1c0c04500d4200c001036104072444402c0d030103801603e09100c221800101000d2100c0c1007500050003a002c00e00c21490420b141a48031005002603d103844403c4d030b80c5145821060b030300644100c0d400b069407080c01d04a0564000c0322580103e80c150289004101018a010f003804151036500300c240d0840317080b80c06482501d00090f016001000081c051030581d0024104203510310741c020b5000d0006803207100d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 161609541 1250 161608291 161608303
    0x110304150203030f09010209032d03030406050a05070807020c0105070f141b0a140405060406050d1202190b06090c0c0d0306050f031204090f0b060d09200102100e010b03 74
    0x5440c1d01031542c034103103895001c50041000c1c007216016441004444903903900014a116055103c102061200c19181c0c0200362170b0100510314141d90100004000401240f90700881c070583e4200303410401d41d29008402c843c103071402c03501c0001507807191212844941c0034502900c3c61034812903080840464980d1000d0007004071034401318656200d202100340c07040c030081502440c4841611060709131032170440150003040c1d030000a507000d55038803008600591610742001024100240048002d81c1c2c0c0303481c0410203043e4040d205801401440802161141d24114050340e864108100c8071450b01d80c0000c00208210141c483c0c0c00b4000d081044100d48001031000301c080780c1654900065091500c000c0c000b0161441c0401e610907001040d21003c1140401c00b91001c0d078060701d41c0002c050a500b414000200400041a030380310030003280007401080d06800c0f21024038810b143c03011401e100b080b4880e91248498882c103000d030b003000c030100039190244c0d48403100ca03043c0c4100229078214401c0101e42814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 161610791 1250 161609541 161609579
    0x305010e07091506180306050403050301030317010608041202150903070b0a020c032203080403140f0c01020613170a030207031d032e110d0b040e030406110304 70
    0x19454480200c145034041c000c1c400249000c0d0700034003203952140c050707241010141c0203c4c0113101c00b200700381e02020701d5000e902c80995417003a800c1285040c00c2c100a041030300b091008078001100044180c010940f100b408038125042ca44800e00e01d911103a8a40015014002d4454110710a06d561018110400205503000740740da10051540d070107260401c0c1441a81c014000001c09004000c8000c3e040700002c01c42c1c112080d01807000500c03503410328406503008120ba00150810344081004024001001c1440458407020401c5401140c0c105000e1926280b00c1801f40c0d02503000200024000f56296a206290510610072141e84441c200743c050b035140c11001d18040083d60214003042003540040308034158070603040030700301041c1c03511000958030b420070100100500101c02c0d180001c41c50103002441c84840d001d2043c483c0d21070b025441c00064000f85440440f03641012000b0480303080c284103500c041a94000035524250400600b91071000c0d100c60b80c101144410400000d4078409040100d19030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 161612041 1250 161610791 161610793
    0xc0607030f09020d11120f0d05030702071518080d0c03030209130203090d0305060a03050601060f030209060c0c0307050d03090b030c0417070302040b0603070804030e0105040504090302010e12070f03080c0d060305 93
    0x10810200502c07620742d0040443c1b580d00d074005444203140100004000200c904681741036070392380d80c0340841281480d10ba03500080301d001480a008401caa0440580685001c0d02c00354062600d0b61400000c1d0b460010160b0100460203103500e00001c68401d800921140308050a425040078048103594100d901c111161281030b0000886148007507414004c241d00b01000315140c50320581140c50b04d80d11001c041c0715003428402c02a00000314140250182e0340c04100040106854080040900da1160161441c05100b4020316102003014070700042e54401e081e0b0107a94549510303080c0080c011503544094114204043e003400001122845622454203100701d050140181a01d9441071000350b860060516205500074010086865882136449038495090f1810f94050b80c01c941c0180c5043c401c80d003186803c02e05020460060540541240c40c0c042c020301e08031140e64402c0d01da4078000d801085800cc01e55010741d064032011901c203115180d0004201c4421526200e140140702c0301700d903080e078000c03941 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 161613291 1250 161612041 161612063
    0x40e100504060f05010e01060305040c05150702030d02030a0f030b12011107060605030d052502130c020c060406020309131103041103010c110304050d030c0b010609050a0b0c0607030f09020d 83
    0x1c00c01280074480011144030f005000a5040441c840d01810050040c0f508140d520000582484808000d450060001411031155994042c818010a92100e80305a000713104002c0305242d80d52000084440070045565040041594480704501400310319564680c010059203282d10314017030030311820b0b503e00c11100c0b04a589804074031305501624406e82c8410702c207422100041440703d4001040b42c0d81c03050151381c901c2c0801201080ea03041c51080031406900702c0f807412449060040fa030b43c48032425000c240c084500d8015407008000d954415030283d4001600144841b683d5800c0c101382c03544c5484180d00c0041081c01c0400c1611450790030460b010764404c410008941a07074142031040d000b00302d40914103800c04000d001840b9643c0d205600c01e2034098480c05021703409042c441e0501d00220307540040059581d50350b03800001d1400c50a801517600c00d1300440c10006241140c1c00c01c80d44e0000e201e401504983d40c0d044c2c0c1c168000d00c0300c1c0100384011511101c0e4003006a581c2041041d04501c10b891444d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 161614541 1250 161613291 161613293
    0x7020d050609060714040f0306020721210b030c060f0409090c140102150c09010504050409140c0109030302150705040512010c03050114030a020d140607020616082202040e100504 78
    0x4284e40c0600c017041c0c044070401060103201242030464080d42d40001e80940c0d01d02c110314043d040455200e600000b203031031600350707003404641c000c1d8541c800c01c02845401021702002d84410f8202c80200d0107140d89903200d4200400e907030900382c000c2c00e040e000c0d05401e24203055541d880d41d019290410707812210451040fa09000d0403060100706c5480c41c500784000c094198038038600d50788054024040c8807050102159050a41c0e01c58000c40c0c0190002070010300280025203050110b0b50700c480c001e621540a594400c9803594031440c011307400c403038050340180401207007401020052580a04110208803007040302041e69110802a2030121084100000b00100d1038040181201c8068200d01040c641c00b10300310b0b22a58001480b41100d42d012a00c8441007015864041550010585001d4445c054034040045050300841c0301c52181c82c0000856142c00170100c400c6803100b200300c9400324200351000810075100004544080e0240c4043d01c0095066200c50039589032003072a42a0722043c64540c01004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 161615791 1250 161614541 161614547
    0x5040608070906120e070b0403110906010f051206010e060a20070609030215041d180d30021b07080a080a180f0e0402010f022107020d0506090607 64
    0x307030700c1401c602d420390710b90f81041c40081210301d5164002940e561564800018001c00b40100401000003e0103240c1e01d60b92850304016a426244480b881240d0000000b412075020360f00c00e80003104143e442c1842c4c40640c03007081e044483e015001c81c1c1088001c2040e079406844040c0189201d8042e5201d1070860314215401a82c07510f40d5004206850304451400c0028036088031000c019607504070b5006802c0c0810702401d02d01800345500ca03c80c0e01241c0e0245000040901c0b4489025910000124052100c5125101c1c6d5640e1451850000101500b85d00780b00c5042c11801d000c00301d2440c60302e4001c40004c4014a80698001026010340c2e80d039001c401c0341d400c4c9420401c0d98000c0010902070800c86880780c841c0403140c0204030002c0180559038420b518070742c2c80c100700000940014403a02e00341e00e0316130b904a160401e044400700c0c049000260925085400080c008107100c11442200701d400c60140c8490400350031861081740c204609042510007e40c09018030303031240e912000189114a0300403402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 161617041 1250 161615791 161615807
    0x509040b090607020a050319030f050703090210020106050a0909030302090d08091804082b02070f020a21030e040b0a1d010509010e01150521010504050a020c0309090601020a0b07050406 81
    0xf000555101312540c50004d5004419202d0304403010000c4019045845010740151800c0c8183c000024604410442600d40540c4070050081c025219010b81c0e4840d8a000d0b0700b2a50a8080e03550311150904040142c01c1080d00005680c503c60b00e03015007005540740109100c29250001200c0b05070f0045104c00c0c607428140140b0b1416201c0c050100c1090521f078980070814440c41c03d41410246000010b80800c0c803589502c8500313451100821551400b080c200f0078008440b11030300300d1040d411050005911031028500360300418041e90318159501981d5000d031103120101144030b03080703034459510300c405944401075540180441503421808900c84490f400f10480140c04c0b046c428080d01d001030100c625240f40c031505551410100c07080c0010006402d56450250660400a92007a003241c2c0d40d8410b180403a00781225002c0c1c03410310403034807250501016400303064103070034242d0700c24418525180343c224052500120180156108804180c4920040900c01c0b83c51f8400b007400020100006030740105a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 161618291 1250 161617041 161617051
    0x70e0f01090b150a1205060102010c0827100c020c010e01020c01080a1806020405030105011706040b060a0308030705090f040b01051c020409060308040e1302010f080406110a020106081b0105220509040b0906 90
    0x2c00c90106030b01070250075000e020341030b080dc500011601091980d0388440403e09480c140048410034442c83c141000900741084480703005015000621641d54050f80c00c1c0344092405070050051160914011034440400401041e8103d44503102c552182442c241c54402050042902582e281c4c180401d241c01e640f0b040e84400041900b000c034201e0808030108400c0d420035801640080d0a03100c031000a1b844000b00d80001d402c2a90001c24011015000f000604401b0f40544201001ca4a2042044110741c41d141007107010810030007642000c8120101c071681c0c00181000014107103912459000100c0e5203940007101d10090005040c0b18011110245540c0900300c507001071588001940000c1a504100c4560406d0103011001305c1c00704400c58118079210344481c03020585401c1c003108024040c3c011403003150190b009003807826242c09990b106501c48008103840742c40c600000103041c24180ca41414800019150298001c0398a590302885640601d002d100c03090316509003100614182400549 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 161619541 1250 161618291 161618293
    0x308091c050a08061c080310031506090c14180a1203020105091005090a0b060f031005070905061306050c210a0306080f0604030302091309080705070e0f01090b150a1205060102 77
    0x1149500740180117107001784080d0f00c60900381d00ca80b034003141348484401c1da400c0100096070032603001c50091066030203081250780c3e000c418800701a44150568801078401c030b2840c004840dc0200d8240304c41458101c0304030380400390543c151142c3e51002c8800245201d40106d0040c0d44507018003448c12410400f00c1800301d9803580801c5603041c40c050450341d84518101c01001580280e0000d43d0a0f41d544449042440018060f00c0903110340554440042c203040741d07150046000303403501082070304014056500c0e4400c03000b00901384ca400d2080c295116007045004400c0f6101d81800a504850540d40d8402c002c1d800c020717595220150714102a041e1403c9400505131540040c410710f00a403000141c864006402d4140180d640c0d8510700030841e003414248001050034201601c0c1c4003000141001803003414001d0040c0d031809500c40a64850104055800c4210700312001c006120082103a44914030051340241002d9440070003105046c982d810125100e008038114403030050741c0c0c0e0342502a030ba40c070840900c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 161620791 1250 161619541 161619559
    0x13020d060806070504060f140c0f0708031309090206090d080d2a0c0305090d03090e13050d11010221060406080f1011070606080a030306080703020d0308091c050a0806 73
    0x400084c40c1d4011440fa03c41040048000a6100d6001e40601c40f0080c00c0407481582d22041c4504895542c4205050307441503101c1c820002400810200030b44001042481c100f4107143c4c508603440c8098900c1d880280c0c4d000c1c104000c2c84120740d0750b11340032403019489a00780d9601c2d48280c0c1500405c0350b600012446a1450843c0450490381078403410280e90019802e2910700d00300d0b10700301122103018000641d600802c9e131605140c24580c00036802800c0b03c608030f001c0c5046540320540e0301603850610707030000c00079030000c1d001c20b220303c0c01085084612628a00010b090102510310135081c0da08488185c00a00042e006122581c101070103600054400d030b60003040d40c0303195400340951b10720020805020700c0781e641c3c01555050083c041201c1800f9080300707082c041c503030315a1452501c8060400b02140440d1a00c5000100020b0100303604044030303001842c0045000d2980c50544040d403000b400d084450090ba41c0b90307800b801c544000001040c41c81d9484540b541e81e507400140c081c82000d40300c070388034036028 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 161622041 1250 161620791 161620801
    0x61305251205011512020a09090f06050301051f0303051b06040b15040603031b060f24080a03050301030b06121204061d0f041d100b0f240903070513020d060806 70
    0x11448480e00c071100d10010b03528145401c084800ca441a08136102d12030400308a40014ad1241d004502a80c90840c0204410f40390705400206580d580c4044130a0388852103020000b207800f600182c0001025016120000c041100e8400e0611034226401c445010841087c440f40300c101001c5807500401c141c0702004540c2c00c2d030320042c121300c807408001403590400d6030035402003041d141c1100014401c03682050100c80720f8203030903503076085840340403d00c0385c4101800000c0c0f00d4030020707407201029090703114070707240da402c1d1303100c82d03000c0d900003072020360007e44040c01441800010030980c211048551070342c5445a08001c0001c00200140c5041426800d07071010a03643ca566074000c10f100030f0b004441c00164403d03001c00d101c1400860302074280c1745014402081711605229041600c001d141281d81d543e42041440400001d40e03203020803440c0308100391000d03811250302c4000a140c54240141220109035072500001c400c4c80382c080022881e15008030b980c45a0740d8142c0114005003001c1005400b5a00d06 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 161623291 1250 161622041 161622047
    0xb2703060402011d010e04150501020d020a080301050f0402090d0501060911130b0c010e0610060306090c120515030109030e040f09020612071205090c010e090613052512050115 77
    0x114102d0050f198403100058080c5e03001e0506003440c100080c2c002d22980c1400c89589040b00c030389104032030150041d48045102244081000e2000c03e52041ca1141980d08040c24002103a04030010f00343c00c0356082110140c580d9407007072400703082489140040741c401d050114010544408220400180d401804110040341012084d401521203a4541a80720030b28074404901528404040042601841c070902ca0000c034038002c0c03d4140d815640b41413081d140d031004100c0c21100581e1414000420721100c1e59100c1005401003500201c844901c1443e80740b02000003821a5002101200803441c855104025070610b400f54512100c8100010808090b0076004240d40e80300f000c00000c1e4504280c13000540d840e000d48407007862103c9180080003640b03050841c4030b81d0b03814819541400300700c5002241c0c1007440c01d0050725204110241100700010300141070680074010180c210156100b52005131341c4641400c0341108822a02c1d5592561b00b81c8d0302080443c11034070b042c0c1092942d250002c1c040790803650 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 161624541 1250 161623291 161623307
    0x40302120c100305010f05010503061810150203030106170402031e0d17010302011407030c1e1407050f060f0403120c14010b06030c0a030b180a060501050301080c190b270306040201 79
    0x7d000e003130603596aa11580003800b200d2205010400a10740c25007440860402d150070070054848400065150f18044001a070380e900003442044005003c0d5000340345120030300c684481e04a803020301220041a2020692810304003411404881070b84400780350701c0b040e43d0182e205407001707164008034103040d411500001d00141e4110781006ea82c4600050540806200f100001c0c04a80c018407000c407203200c00301c0e03a1084126102020b86a0500e224009500303940c011640004886004100c199410302000602c141c82c0c02c552074465a44806100010106400d00900f4200b40310035610345d401440280340c0108210390018000c50030740c4c98206544a60340300c06045035000581103100580f100700c400d504070058102d480b03690340c000c11180c11101501901c00101402001580307018000340d80c40e100110340c240400d1042c080c496020603000d024a00b08075000c2044041b060100d90381340da03112402c2c80566401100d400682040c000030700c10541c140704220800f014001c03000307024603040c182c0000745005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 161625791 1250 161624541 161624549
    0xb040b0d02031018050a0305070215090d12030e0f01090302210304020f1c060902040516020304090e070b070804030c0f0b0d15081b030f0703080301090c020102040302120c100305010f 80
    0x568805100003158074295075214080e5226007280c6000005250023031054008d0b240490148081078034060220404000342ca02141002d46241c1000c840e42c2c40f9999411951080034051590301d600b041c40e41c0c2424882804041c16040c0040ba40d80490701c2c0092504030500f000c03c001d071144503032102505413a10100c9400a4044071801c005080180010780c002d10128498180302e60744203041410482c1c0c9800005440b4001c44c1d040105990701d424245060050025460050300100418024a1120b51082a00d40c40000866140d80d1301c4441c04207866112401c01da07141000464108100111049500c0162980152074860f4030f107000c0c01c503142c50040089440181c2d807250074080c0d90601c040003003070080c404041283e940c03400e4810b0b00080c1c48401092a80a03000790000d001103400000790801c00c42e90702c200d0b11882c50f1700c0c0111040040c100c02c0c0e614401c6540801c00080581c0c0c40926101c2103d0600014110701e0720501c04010200640c0070a45050504240c01040101c00300e5601108071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 161627041 1250 161625791 161625823
    0x303070507050709180b0108030f04031b030605040302030409110405090621030f18061905031803041d070f05181309080903070605091e0619030b040b0d0203 69
    0x242850b10b00141805001c1d00a0b100c07052811001905040e418031589003a24002c3d40c803075180b662610040c40c0c8070322940e8102d0b07825000c10442040001c0000e0000301e00e40d41c000d003800810540f80d541c5c100545a0584003540141d001207018480c0d40316502c502d03a031200c1d442c40b40c1c5181c40e10300b00c01b0880320340d80100107038400d040b0b10300340c180709000301070410f03000d030200805484d9601ca03002d4800c07a5039000145240104009203144400c241005000c44440c82c208200d1040309240e1144119040d50004218003c2600180c400c1d03264182c0130805030002c4d01484120450420745540700c0f0440d00001004d0700700308000020384001e0250400d0844101c42210003110700010000e10100795082001402d040d00a480d00c654070060146c040050b000401c2c08400360b40c002503440342c0846a50054200d0f159201e400a0410142000b20b441c0d0b8010f42d1700007405040c00c0800d10078038941d002e80795010f031202103038a43c0e03d200b04030300e8039114080030030408480700021380205402007946e07054401801600d0f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 161628291 1250 161627041 161627047
    0x302011101060e010e091005010906140406080303010e04080f03040809040c020606090f07090e010b0c01050601020619090c1205010c02070f081f020702030d1e0914010819020c060f06030102040803030705 89
    0x76039420300c540341e0b07580c07c2c2d4181402a941d49040c0f00001b004184034101c21400103050905407807411b40145421140c46130001c0d401d40c2d00700030030403c40400140044038808010089111040140809117101d00d003e5a0080e071260b101c5014401030702d13003805542046402610030445140da0b9449000d421289070001c1d01040d40d01c91006456030201d5411410b98111168000194520070700c00800b4134800103030007400305031644801a41e80768000c1e265402d0111280c1c034085110000c0350300604501b0f02490190f4640e5540e00710036920702020203000c1d10165141d0b0f40030400c1980400194004200040740451303a5450485800c2d156a16501075509000c0c240065100c1058150155003119400905544a4041802c0094002209140c401e0050481c14202010450188901034202ca40074507a07950005081001100d00050044c185143d4090b0733180e410b164031400e4806007c04010110040c4094104901c1008040700d00400c054480d038010002441411030100a4030f4001c0c01c6c80c14040e407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 161629541 1250 161628291 161628301
    0x30a0c0309090e0a050d050306010f12090c090902030f0d0509060904060f15020105010902040b1204030c060f0b010806091006080c0f0a27030201270902040b040302011101060e010e 79
    0x10306000194807241c2d01604155524000c030001081040c5464494011134060b004111002c1d0360b9030004583c0c0c01d0204601c000c0c580e01c400c0c0038000c4103808029807000010f001d040340c2d4940c1d100c0102d6402400000d9030350780b00740c01141400c10991100a03100b20052503024041040207080b446410012401414086036900840d11950030800c0500503640300031040680300c41c42511400310300c13103c1100642c240000040c2c00c00c81d03417003202c064402a481e0719243c1036030b002d180d601c1d10300040e05c110204019044018040790303a42c4101e0340748005469000c0b87c06c40910340010110080130303080d18898500c840501c0041815035055600303c034160304085142e580c1c0c2850200240c002c0c042c2c00058218000b44030680c0759441000c50301100065907282c0c2081c0c50944d210b414650107804024007141408820009c0f4000446406004da2003440c3c40c0c9180b07980300e044103016038200398480c40f0200808a818400c641e088660705070707184182c40c020442e0324038010105c0c500c0c0906102e0000c4081000b1b0100d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 161630791 1250 161629541 161629547
    0x4020d060504090b100e15012001240603050c0421050a03050717070b0f0c0702030a060204050301050f0f0c1b1504050c0303071a060f1008010e06040608030a0c03 71
    0x3001064020820044600282401042a40203c54000e403250a403500491000400703c0d1a40c0660003151040c4801c01e03030040191003e498500582005012455024040e1642405000c500c10114508032510000307551a101c0000080d412090525090000300140804000207440480303621380028032498002d4408401c03500c1c40c010018000d800f81c2443c05041c542c202004110443c85000c00d10042052452100500c3c0a404401071040400c880824030040401c0c10080d0895008103440303182c4075140c0e000a1400440072403c0b1b072456008101040a4502803040503030100002c5500300080c83d0854041030705680081000c40740c80d0022614030340c0745040980c0d00000700800021030320300c82c009607080e0544c6641294101c0d8a0f1083b4186090f80b81408801c0d00c80596110310070313400c0144d000d00c5c40141754400801258120340c1c41a00160075660304010050215215240c86d9025418003d5100f10080c005204038016410400100400c0e4400422107051018520380b9080b0004140350071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 161632041 1250 161630791 161630801
    0xb0603040611130f031b080604030809070b222405070f0602071a0703150303110c10180f030f0204020a03090501020c010b130603110120011508010b03120904020d 71
    0x58240d00c55544000c2082c03130a00c02210156400342c0ca40300e180003000442008030800714054545075401c0710300400c0000e802030900a8200f0003076415149002e441d0b484030a101d40020002d040380c1d02100d004041c070021442018005814501e085400740c403081e0001505503507801c40c10305c08204000a182060141c0c54000707145050740400203564079203090a20140c80d6608103122194074410801040c01d45000348901034003031401e0300e0111116451904c09440c9190000e901c520540078221000381143d554604203401c8a81c03a80301c64050400207804034000c16035a401a0300541c0480c141840800d504420b2811a1641100c0c0984c0d102c0d00c40710100d02500c4c82c0013005203650300105003400b0106064000e071003412002d6078014002d5280f500c0203810307581144000741074000707618112101544500414a00d0340c14025110720303440700c180b10240c00c650600051000b1460380080a00c004082170090b07181e0403104030010030b03d4842c81440c60180340318264150344540d6000413030080c0d501c0c40d40c2003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 161633291 1250 161632041 161632057
    0x6020c010f0209090906061c03020304050d06050412020c0a090f020c010c0206091207020a06050304050f15070905090417090f040908042d14130e07090e010b0603040611 74
    0xc0c00070780381c8491400041d410000708640b1400a0500207074440c1c41c0090054880c4c0300c02050802c0c2e500307031041410035030440080c040e000c6010401000c25030b9250ba5400600292007030100045a29203814011000c101240440c821900300a40e401d280e5a6809008400c2e640b40e0100029613801e6049514000c0c0b0590346d490350305500b40000f004903160041100c0303100c0c24808060701c0c0e0301070b0495005d40e10b078031601c0700080d404940035400f8071500e84150041d41e4403500c80c0e400c035503494044a40380c0349418180711140058041b200108040d403a8028508401050b003580e20b00d0070790506645540104490b0a0700c1c4000c5080880c00403c01d985405c800c044050f000341007080114014200310219a02030b015001d40400700c404003604260b10b00d40100540c40100200010a0307041a01941080001410481c0e02020390aa1240b290800348120303241c040c498030080030340618101c50581500c5000a0400499140100328001503c1c2d00b02103a90040e0b00000000d0000145400b092003409003e170 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 161634541 1250 161633291 161633293
    0x7050d06120c030c09091505060a23010f0c030c0219090e060a0506101704020a050612071202093106080a110a0b040303050c01060b180a05090702030301030f06020c 72
    0x1041c5418000352441040959002d200c908900f40c0d1106240b030152590190f0043c0321700903c8202080405039540300f650002c1005000d1203003141d854207103100c005036100505401c0c40c540448440190f03088031100d607070310303159080801d002c41c031075140a0300c21000204003034083c1c4203042c690085012020240d05c040c201c070306010480c9072405820b142e030340c19040310840400b91900020807001d241402410865020300e99600440000d40343c480d045405001d44101d8118100c100085450350701d044c050800c844407070079110000c1c50130003801010f80b1039075010b41c500140b0400030070680d5250710701b01c510190201c0f0f60762a10070310926107081b010200c0c1e1024903641440c00802280c0224085044000c3c28000c0740b0f04c0055410400401241c41c84c148520000b400080004000003400360001d04003503040d40000041060b9200c0c080b164543c0100280314070038108602011041c03815590600107031005403040c3d1514070b0200c0c0003a540c3c4c401804068041300a1400741c10403c5010380442e194800014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 161635791 1250 161634541 161634569
    0x9010b04150509060a030206030c0d02070f11100c05190201110d02010b090a051006080604020904050106080711010b030304050118170d03110a0e150d06170d09060807050d06 76
    0x7100e000c88400060082c1441400848040790742c0f4500005c4d03a2007640e400403c3c0f50714645940d006a00b055200b40d01e4a503045400b84000c4002c5a100c500e00600d103401000c150405000400400c100d040003489040240803207102c0302c1c804900e0008641c00b0304003020328040b40315101c82c001a1002004400c07040c86512401c05640d02c5982c0c1904098100f100655680215482c6c20b030780f50303059805c100c03180070071070342046001c028141c461100313a604440041c0c40140341c0806100402e0a45100340c1000d03004c10b0310304041c0603800b60f01c50004a14606188001c0140316035040000e0b40702d210710303c00e02d410000f2003007012046d40101c441c0703500100090040c070003607a03e4152506031a511000c80386400f00380b818211000e40042c0200326003030743c050365840c000c00402ca042001440000c607070300c5c1c00310942c0c10702580b04221414840e05c03015001d44800c0d040c062042e407507000d181c0589800341034100b1403d80f804004050700804c1d003070b4021502d4101203445c1c0102040c0b1500800440d4048071410f5200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 161637041 1250 161635791 161635811
    0xc03370c03150320090109060302040608030c03031b0702280501180306020307110d0305060102060609090606090c1b0102090a05061204151803050a0305070201060f0e100807080d02060f010b1209010b04 88
    0x994008c0c01124401d9805000150b40d4001c499140d00410301d5404064004000192004101c0304c480caa041482c41030550410503a900402e2402d20f68280d4002c8441013014510341b961080c8085400800c001d103405003040c03a6584d08c4900800c41448024906500800480c04850141032040c2110b6448000c84484030041c40008024050507100b80b0701500a40c404a40c550a01d40461440760f04500000c1219864010a001c0d1a400c010301400c0b1410003488124008000b01c2406641e81c0c50318000584c40d1004402003102010156000900c15001001400c014210b070394030003640203070880d503542c00801100241c0e0b0050f00000c21b0805100030402c0c0706004150b00040640317800a0256030400c0300b0358030708000340c3c202e451900503200329111003001000003590a081031540301007886000d14070a9503c62030b079490041160000340c110b401c141082800e09504000040c0e00149440c0340c2400c65140140320300b039074403409802c41d0001280000060104800750040b02401c107000d00104005081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 161638291 1250 161637041 161637059
    0x70e061309031206090506090610120e0d020c030601030308061905040203010902041403150115050915030f0a0c0c1424012108030c03370c031503200901 67
    0x150f01e01c210051882c040003c150240c00d0b20401d0300c1990041c000010644408081043e0f1b01000382607c0c040100501071054007422038060103010750700000080890151161019040c0584040d440f03005c1da000e00010008030380c0c40007456070040829030394196600c5a6040f001025070180d0040794010b4000400060202d400f035004004480110070040b012403d1401016100c1444a00081e00004080014005400d111003045002d0032503003840c0c0d250140c200701040528503840c8860001c1071000c020018041c1902406d0384e84400715010400c031404020b20007401a0154040c040c0075038a0b00600d0b103260345000c01216981040b41d6001c0c0428401c01501800f82c00000d000300c0d40c50707885201d0348071065068049180943c55002c8081402e59031070b0303c0c481c5544d42004004441280c0b40011040f50150f082d0160000001c4490894020500c1e0314401300035108081400001c06140c100888401101d44000a0940f82e100f10820202803440f1030070302d0705c10f0500d00030039442280348000051040d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 161639541 1250 161638291 161638307
    0x21809030d0e0a03020606060306060912010605040b010f1707030603210e101b1e08030a0510060206040611090301020a020c040c0504120809010909020a030504031d0102070e06130903 80
    0x2190301ca0901000b00094500340e210098840001c2c00b617402080404d126240881c0a17640c403020203090030f8184003a08002800e00391070300c601c0000c9031b551200103110300d08003030040d40d0200384282400b8860740e83c0714034020404d00b401140902161001e4000c500b02030702c0798001c000113541004003202c0100048003460000113101c41c9990100728800411852410500181c10a44650ba10784404010104400101c014401e0004584804490001c440d214500324541c00c1070700c1c020482d160722403508110000441300007030169590305031202000c101c0300c0d034000b4145500652021011442400b41e0343c03c940c07a0f001d244850750b8035500106040c2d00040d400610280c8c070300001c840601c500c00741040c0990f0380d80b1941c06010402c00381c0c0300e1200c003c0f56006d0000c1c402c000c410714201c1c145a540300d082c2401c0b03800540034200040d40301c0c004d20040c15400004e000d4603409082890381c2c80302c1c0050020707645105074400d040107901620b00095042d5110300003100340525085052200f4803191400401e480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 161640791 1250 161639541 161639557
    0xa020d110109270203130b0403020703031d0d02011d03011b0201050a0507021e10050c121008100c030908030a020a1d0d023d020c151602180903 63
    0x50108100045003d242d2441c40004640c0c40410000400551044406540010881c0b25481305210b14540007513400c4400902c1a40240d0203030010604619006081da185042225030220407410204010b68031041900700083d82424513004880705640e150062520700ca0140e6450751074001d01440000d50304d4010400110248d0080096a4414215100311102a03a51100503480301c4030b01006a089010141496400002182d4101031a1000101a1102140e4a000c03a10780814080c2200001506654020074400715282d001c43c00c1c10503543c1c1c4c0b86203113005000a603884282100100d07009901a00300a07400c03083d42541c03490101c0041d8065030000140030000346003220001e1004000350200c44030b60200074240c01a1680940802940a5511074074a4604030f4014072510030074030290f400170030304035900c102c0305c51100c6403800a418101510040d500540940c5404105018a00104e4200010b1040d54207440d9005d80003240800d5402d0b01c00d15000459801444850807002000d04081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 161642041 1250 161640791 161640797
    0x30e010e030a030f02070506041e060f150504140720010518150f0601051309020d061a25060603020907020f06100302090f0c0c030f0304020301050105010306030c1202030a020d1101 79
    0x84c0c5005042e10120710802002a01a801000c041030000c3c2ca850b8420100c00b030307225008540854907441d03100803210b040103003d110a036100b0003038103903000c91280c580040008a4081001003004240308e01c012070001d002004004001c60b1802c4c070400502c02062402001a00810461606409038003000503000c41070740030342c0300310760159942c40c0504100d144161001419840251910001903403035030807400500c180061000000f2506680310f2000d004e9010740708201048d9145410301e5030844075100301c8c0d45411703103000f00701d0350301441d4007107900c00210001c01948a107154020709145d0014401500000d5000c0b0092080c08005540052100480710000c5c080e00c0650f2202050a152405030340b10094112540701c00040303142074410f00e141d40c4903148144e6a03191140c0c5034019401c59200e101540c09880000c4180429030800344030f810301400702801c1c00c10800381103444001c142c1140e0f1240c19a081c003a210b0000842d2001e11806c80783c181d0140501d142000c0c540391100d1112403080d030700c03400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 161643291 1250 161642041 161642051
    0x501090203070c060509070306050925050303040501110a0b0f0f101d1b032d0c04120f20040f0506060405210601030506060109150504050f01030e010e030a03 69
    0x8110054400c0300d005600c40d0700c2e02110000143e40b140058840100300c040301d0f0082890000c049041c038040e1602c01c1c0300f03c0c0d000d466038072100c1c03691000461a20f406056190f010010522040d1000400c40b400d0b0350302401e19400548000190a19203005a40c00905603000e403000c3c0140035071b0750011513014400ca6031040c54680d07a20550841a04030500c0f945440381d08a010580b495100c055036590090380d00e904200701415440742c8250702d85e00c10f40b8002c0d164001d0100401d29800d45410764600340c0ca8100300c82e40107082078508030b41140940d01a103115070400d881c020040000203020824103d034400e41402d1441548405620a13117a08202c0034080e604146100802c10345030310407a0f12400f0010131203424035007460f060060742c403590190105551042c9880c4400907001304089030007544210b005007403a241c10f20004001a580f540400d42c2c1d41c03800d0925000c026007040954058410940d100003c00030f40030300407409030071b43d007450600551802c1c235002e05500c0084014035101c0c00039201480f03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 161644541 1250 161643291 161643299
    0xe0706020d0c0b07081302030f03090102010c02060c0a1419090314010c080a0c03020f0f040305070b0f0d0f3201060c0b0c0a0314160212040605090f150703050702040501 74
    0x241820034458010002c3c103c079000244068002c4c070501e5007102409048a0f90002150f01080c0303420b003100c604031000c2d803001c41c45050f9583e090040301d0703c83c3d409201401c5030741007000414400c0d00500741c15030b0a01402074500704041c02c0c1501565070754103084501048455a03040064044219400b081c0d65200c6080c940303406c03c80050080d01c12032580da564000159468075040c1c00105254901d1408164003040a4900090007a01911080c00d04c038005641e20751551038294540301725980f020800343c02c14415031a681050b801510500e000342800800c8aa6040888000404040074555030031100950300e01603508100000340350500c501c81c101d044a0340c845006440c1e01343c0d500d000614040c144000210684282c40c080c088070a61801c0c04640c035403920040342680a000c49103030310040380340381e60302461690400c00e80f1004a2888603a500d4a800c201c4001c08521400c40014000c0f060040c02880301c2d124038510f002d40340000031900381c4820b0765260040c41c40d804624264403503818400046 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 161645791 1250 161644541 161644547
    0x70605190f020318011103120a1404020d0f021504030302010203100806090d1803060501030503130b030f04110a030501060f090608070e130602070605010b1c060501091e03060e0706020d 81
    0x201ca40140e40c0003035040c00728140002d4100207021800c02c0c1000039080e0607208001081000c0c0c1008200607000050a20f400300340142100c850790034050700400500c00780310143c0c0303a100c01e00009a80002045010364078030300101d0b14400302c012006290880000b000800e0650650146024400380741c403c042d001c0e60f92900c01e5690509541141d5103030410107074100014001e9469100c42c1d003440088140d4203a0b243c4449003150400d03401582c803500000f41c5070341da40c1c1140c1410006001c1c4459410b04506285440014085c0c004000401092051072a0603407541c8100d07400c4011b40d0701000901c03a01d500d400e040c49021702544079000001c0c1c1001000f00700418081041e2094450f400e00105940ea0351000342400c03019590307820b84050b80e00300720840100d501402158081c0900c0f20503955240d0030b58038003515020080c07210b01480c901d041d0061209030380c0b000700f80080b03a1840070b12003a0194044419440301407030341d00c020701e818a00303402a4507081011981b41b00b25032041d002e5540d407107241c0b4815 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 161647041 1250 161645791 161645807
    0xa020a090c0e031b0409030e0301090311071a04050409081209100c0912240c09050f0609090105060306040f0e0a03090e010e01050907140d0f150f03140f07060519 71
    0x50300c4d03803042c0c1c15a007001c0d40c2081c2e4031000300540246001c15401c02d50b580442d08643c103100051707000a10010b12030001c0f2908002c22001021030a0082080007800c0c20340c00018006c500940c1c0c420342d01d61420b401840781040a944036500c60140000c854140030b02d841d40d40340e1000746038601c0c0d2820084282c440601820748202100d0054040018075002039071580034480510348906911001c3e4004908802418032400d0082e120540740c4490044c109010000703d40c0c50100528402d0000f08101e04a40d21604201c03411900241c64a0340c8a861300320001d03007c0c5c1201c1d0b0524030a1890088032003000d0000003503840f00d05000381c903030303181440d2603080b170790340310b0209004140302c4040394001003003281000c408a0794400c00364941182819a001950503ca500501a203500285c48101c2e090745603510b886400f4201c2c545845682e0214a81603c0c1c0001ca2414403011705101044680501c0d01c8030144010f1505400c10400d6800c0c6030346840024003550000c86800354130401d030383d0310120441c2c013030008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 161648291 1250 161647041 161647063
    0xd1e0f06080f0a11010c050a0501140c0304050307030807091205011b02030c0303011415032401031a010311070c030c080c09071409031c110c0904020d140a020a090c0e03 74
    0x181c203c6520907180c0034218591200424100000301442102140701070021666082c400c00000c21140442040e026000c0c0000d03080d5061b1890400c18400007903000012a11070703a603d030422120700d43c2c4983e402d54031841594054801c1c0c0c0803180d0507408000d810740c42800b2002c90030740d41040d0403e010700d040740e81e80102103150386103910410041c0400380c4862010a0720050003030010f4000404400020550340050781d02d000d800350005d811070302204000d25802c0194400703181c00c004051000300e810403e45031540c00f0b9410300d0b40d1040460223411892040760b512607085080744140da0317034034904064241c415104000c11400303095256040f52070110340ca280102d5040c2e5070480c000c0803d101e1a40b030740d8420011309525200f4071071045961003c3e4650007801e0003c2d515580200070182e0b105604205c15011610700c2407814204100041e61010401d0207541e8020350b040b4441002c18100610b00400c1d098041e6200e255144001800009a00314898000351a99200b00542c95142810703661507246013 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 161649541 1250 161648291 161648293
    0x4050a05010b1615020a0905040e0a02150d0e010c0e090f040c0311060705100e070f080d080717090d030f02070f0303022a0a0b090d02120d1e0f06080f 66
    0x22400e001010701c03940f9850620300801c0f0b4200c1d4404a26084800c903031051000b0b10214151a07810000b40c90b10380310f180040040c45010707004180341a070002d500e940c5401440c07950460081003948891030b0603808200c600510b10020400058440f9010f070075642c50603140d0f48150100c900241c0d2042c14034102e18080ca90004e0320081c42e500b03503941d00d00c0e81550b40050a400c084240642d8011500401c20b03070079102c0d2100c000080c0100c2d0403848070304120305900003492000501008115040c0002090010380c0c4040c908844036031240c02c2c04540020307450f0a141c80700c4441c0341c14029240804145200c21042e581c804019010780a19050145d000380d4070090420400b403a43d03100407900a400901388607000004982851003e0300b8050801d090b04038094209600103c7c502c8200094005495049420704005100403444203d00940d1100415090b04042d54041211f00e0080c0391600036211080350007282c1d00034145a011500010940000281d141d0381c18944009810388012541c5415605600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 161650791 1250 161649541 161649547
    0x30414060c1312020d0209040606060e03030a17101203030509100e03030a05061906050c12121306150e0603070501030209010c02040e030f0f0a020601060e010801091505030d030b04050a05010b 84
    0xc07107550036500f03112405a0704950303008441c0005903981c590380f620451141e00c3c00120b0030700f8030b58000d21a40d203000080b4029401040381c0102181c002003412150300d56110080b02d181e4417840700a10a4034075900407144508010741e000109074045c2c01c140d00c1054400e04035a003a48001900105407440960385000b40d80003000410643c00300e82c4c00140e07029101600c0c00030400314209944070701812035800792001810100d040501644c080c010900286c0e5001541820401c0344032082c050f110014042520340c540b008484420031990ba08100d9a20410480d451112541c0b0b11341d450030b504089031098400c2c003404401051542c044d100340c41c40004103179100780003104c0c0d40d424000208048407201d01c46102c20311a00144001120041010001041900d40c54160025020703191900c103030030140c14040f106610643e142d9200e03c01c907044840c0640d021076440700d0b2001803d00c6418030341045406000300e90520710301c1c40e05600862551441a2010803e95482c031141c0800c0758001c1c001c40030000020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 161652041 1250 161650791 161650799
    0x70203070c150e0a0609140904020f090901110a030603030e03071503090f0f0503040501170702030a0f180e06030f0309150c120a0306031101020c0d1412030414060c13 73
    0x8035004000c0010302c0c10144001d81481000615211840d0b102d07600090314406c091021072110700c0004000754017600c010640d41480c0d07000441030410b000c2d038140292864400600f0043c400d4002c0c0703010400d002501941d0320080700c4000d002d0a4580426400b1621000b6046640c0c1000076441c01102c10841c41c0701a4911043d10450103800d9a0740d00352440c0e4a100c0b225004100390300001013803548588015541d0724600b0002619480090504c041c0030500303141004080c036004400c44001300729615264010005140c410348230a0841d0090f407a80300c503503900204185000720901130140c04100c0455004140110015a59102e507039201d41d0840008144641c0340c00c6048c4c0a440721084000603108040d01003410904250402a0b40707400082e110302c41001400740c0741200c1150060207201500c4030741c910b840403070034a01c0207080040c203880a0010100400b041888407100c140f0300034442941d24201403c00c4d600000c81034400340f80c2d50050130045100c1c031045908480c0040080b00b00c8440035071130 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 161653291 1250 161652041 161652059
    0x2404050705090301021b0706140405100302040306022d04081b0301090b090c10080c09090402060903011103040507060305010513020705100e0a0309050405072f030c030304030305070203070c 83
    0x405044042404000d00540140f65001e0000d80520035101d250190a03084c03c0e03242030319141c060740c003600610207410584040101500c0c101e0703040d900295004104404610f0044009100d03552015200500c04908038414002c04e022403220380d0700c0c6030908550010b00c2d14000d0382510891042a005501c05c2903050349035202a072079180d030118024000105060951110a40004202d4021001b07811510700511940b82842d400b90802d2942e00d000007052404280c03031a2944113244074140314224000c009402c44d515441110705624019009000000413540c006000f074000b42c07000c58540c0134111020858620900c2000e04862000b02422002a503861624000354024a0141d44500900b11200c4191103903004d0051000e14140082c9a08c41090800500c00c0c03034a600464440ca0404c0244000e00758801c0402e5030382c038246151080b00d020035200c500752000010516400c10b010100382500d00307000c00320242d44150b009460600040c8e0b905c900c1203840e03101c0c4410050500c00301ca03d0600218071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 161654541 1250 161653291 161653301
    0x501090510110f0f0d0f05120c0d15080304231f0c0c0f080610060207090c05040806040803160e18130b041407080a0203030714150a02030f2404 63
    0x588801a03d40c086a021545420300d012031114842a40c031920218060960254802e24034071a02c0c501203041030b4204004030381003140504800c1402c180400c1041e01017899a103c600c0414078031401d2180c2e5513580c6034051712034000b07200750011043c0710711201c4190040d0460303440f030f000801030a00100011400e145107036455441c0c603060400c0304100c00c2900042c03100002c01b000d0b00c1100d04c0e81c4445031a00c15001e1800c4801040300c0c7c5035031030384d007000c000070382e00000c075841034544102c008030b4030681095046a19001e5903208034654402c2100f8401030011941c0114041c410b25081a01d01e00b9060409a40121028403002d400010024070b4040810002c031805800a46180c0c40000c0001952a010001c9205032070540350040b076880d6140e5042401c000c0040284010409003006c50300c1500080d4070703801000c80c041c02d040c0080070000f9410100f8050401cac0320314101545181c5003040002400203400c2140c1a010f11595440402c0d90b00241011250307142c41e08154090f0a0341424003408081e007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 161655791 1250 161654541 161654567
    0x90729071401020c03091017160311040f0311030a050d0804060e0a1a1503100509010204080304060908010f02040b16020619080406240b161e0203070501090510 70
    0x50100102500030714080c0010580d820200c401140c680140b5820850326061040024003400074080c040c40d9103c03058100700b94440382c075070074201602c038075100d0540280003a019074640344c5c3d01c00600456009074041100b401d8a01540c1152405149482819511120b040b40030300700c3d038011900440824450201d0303c0d030040c400c06010802010400d101450301d10742e130780203c0312242150702034040c5841500626900c400380442d1410069042c00120340c9400a90241e46c06e01c80c0c980d00000d408030303425011a030042c80c003881101d0b507a5584144c024401c5040c1e0168511170350800c2d0840e01c0b40c41440c001d540545811200c50351a1000103810404c00c3c504c00070003280c0141c0f0070700c43d101004103c2c1505032180d80750780c0ca40d03005525251078070104640c010714500601004000c07410003000d031102c2c00072050b03810405030541c0e280009c9442003030040304520014030384003000e1600111203a9030045948010300c01d0701160f81c100d0f20307003005440220f40c178051150020302d192020030b10507100341e4900d1442 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 161657041 1250 161655791 161655803
    0x30703020409050c03060906040c05040501031a0d030c0b0a0606050a0e03010b03010c090509090d0f0c05070308071a16051e09040603080403140307030503070305041a0f09072907 78
    0xc2d5a550b02482a10411112040460008030030009581450420503901584c00ca07020028581e0722240a0414050307030007418101a034480e041c1d03403511181c240c198001c01c401001c510340f0250328a0000e1010341c010104441c4080900082100e01d000c900402d0151550b03611194100f0041803012682141c119031600d9056407a2040d88405072400e102e083c101140d103540d04412103050101340a05403070b01418a00c9154060840d40f5002d80d8859815a1000d00c00c8c03a0084800201d81400c0f468a81d9540014000c800001002800c018950210301003040d00e071100e04295980d02c1c00410385080041e03002c2004140300300504081a495032003540901c0407031510690621641300c011500b2601d064000b02d0303443c0c0c0c00240620074800c00d4424500036142d440000c501c0c2c011107940007012400050007400606440e00089000c000c500d02244801c21a03d00314800140741c8040c144091180a980ca1983c6000e10900401c40e08014503151241800030085d0880501c0c0e1092a0106684011030503140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 161658291 1250 161657041 161657047
    0x2a061e0601090536090f06010515130801020a02010f060611071712131e031a0408040306020a020604020f0a4403090906061c1a12010608100c1403070302 67
    0x15041c0041307140c04007116072101d4403140c50084c001600c1d02090031001103469021400400c910f9907060291080b510910303110b0b039298070800480010140317039a001100c45500200b1212801c030b43c15070081c14044024803050103016900d032815120b41c0c0c101400541075030000801032000b0f8001c410030b071a00c103403010121082d00104034000d52440d0041c004410203030804040c1005503c04002c5141c064805142080b80c40600d140e83c0c00d00703441804005030000d241c2a0b8000350501a08005036401541c001c1010b558864040e00001c2d100c81c021a0202d10480c000d003000000d90402d0f00d100d005035400d00d8603d249110f143c00c003004002264285182070f01d4900c1010340d0052b000c02c0b805020640b441c0f070007551170340e04181c20800700e80c50013400f1138003418003403058410050018042c01e84403d21144005080c2c0400342c030f04490003509a421320b4011804c0a0a0a820901540301c0012038400f001980d45019103451100c09403040c109649001a00c1d21440500001a070745c003d6410400314140149 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 161659541 1250 161658291 161658349
    0x7140a110d081608160b010305060c0f03070c08090d081306140706020d0b030d020a030f020c13050601020705091815100e070c060515040b010905090c2a061e06010905 73
    0x10741c002810350101c883d46c0f02c0000420070094104002c54200480c001180d0a001114501c0b0140b40401407183e02004402c5442405100464044401541003d0801c0e07600340310500b002001680075401c5500741e07105d080070008038984518248204c1c0c50491000a16000340b0780c64040294100905144090713a0f500080030306035804001250036804030303401901c04081607084c050080b021180d1002c003950408503c6041c5a80c8a04003c0000741c1c20210003e881d40b19070300100d2401007141c0119802074070240a00c160202c940242c0102d4000c0b45044620320020f155049040a1040d01c01084164000000340010414840c526074071443c18980342100c1002a02c07030300c058034010b8030038130455825225640010704050090b607145c44000c0c240a022240381c00c0100716a03da008148006c00303070001c0b0381e9194640011850804080fa001001124400c5104078141c450310281c030400040311888110710707682c01c442c14820788240b40517150056410300c0e120030300c0144146090300c84a102040e2007108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 161660791 1250 161659541 161659567
    0xf03030d0e1501150207060e01080f0a0f09060213060c021c170a030605180402011706010c1a0a05011a09010818030a0206040507050109030b15010507140a110d081608 73
    0x24020040510004d11100101030040d0078242180c1000d0204400700d0002250350341c2250101360404014001e00b1800d954420134000104504a007001e401803c20480c00c060090680183c448500980c642d0302845035940410381d8000079691009401c6403a082c40d15406034507916801c11154026480d10900304884041c0d0704190b440b10b0300b04d0001c2592000c2c14009400c00e07594030105208107066828803800d16800207080083c100010b40340c1d29a40c00005400d0703901c1a10303410301c925070141c644c4000c4194002c403181e0f015011900410382c240307004000074041d20040c0401e2070850102c0d800d07910b4444d00c00011141c48600515481c443c0c00c80007000722804c83e00308010321603424641d020749032a080034034101e410304506501c514100f217040c44060001c40c01a80c80d00d0340040d44500248003007400ba0b40184d4040c050418082c0c000440c13484940001b41c800302d403080409109100103c525010030f41041024408401c02070141441404000c04a081c0840914506130007142407074184082e8500314 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 161662041 1250 161660791 161660833
    0x1524040305070f0f0b0304020d02040b0f0303070c031203020910050901140c0c0414152403190605030a030912030e130f15122a0f03030e0f03030d0e 65
    0xf03040300601040030840c40c1459012075001d0100e6600c030354030b14109034000400b08028080007a00c11503035000f40c4412659248a400700320780018094a8442ca0306080480100d50944800d51321540304442c02c4100900c21702c2141d0546400911100f000480300100f00e800d40c20020081c0d050200d44194048400380b04c0020380b01240324071000345003801d0b00c8014401a60380d41610816094641c0050200c1e0581490009020032415a0549440203860030b40f0200c3d0b00201014100b0040d0020a0084004112008142c11150031030144010381c1c2c1ea8041c1070340e484140304060005111114103000030401c460396248541d0083c50890400242040010189690241e140d01c204d5901c1c54920340e492010b01500150460b907400d802c0701903190070301d50f200ca201030303903001040d0a45081068016a900c10400a0422007012040807516120905500024024041a004642c841c00e480901d494445070010b0141405030285003032559091882000d80300e8421b041d0400e0180340c8861804071078404013 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 161663291 1250 161662041 161662049
    0x111042304050a0f0b0a24140c0f1504080a050307020102070203070b21040b040809010c140604030e10120f090b090102030f010b16021507120f08152404030507 70
    0xc0784044126104c08861603220464000c1d1468082081802c0340703000c039902c10000c0080003484480248000302d500a444285035172081d040810141340e1030800040b494a54580082110b210001d2803810500b012001c880040c0450010070640760020310800c05150841c00a00000d03040c049942c0c002810481d00ba0007078140b0840203d0941c84075011115040080d00b82000c942c0d8050400d62203007125044001d00143c50304600103040449a445024070300040c0d86c01c0920311142e0400e03d0003564907048141ea06a0004800c500c0c081010703e00b40d684803c0b1703050316855450300f000001d070030280a04000c02009035000d40c0d40d03030400c0100d003968a06a2081c00c191000598916000e002a855143e0603006004203080502c0350301c020524203d440b84030183c040b00e41e100314044c4400c00f46040d1046480c01440090340d4600c603c0d07250342144a410f4102220740b103010b04e5583c2c1c100036035125404403003100d5010011002c100b01a40030940034524040321703c9607203882c0503120b0311460710300310315030384 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 161664541 1250 161663291 161663311
    0xb07061805060a2c07050f0307030b090a02040b041b0f0216030822050306040308250206060906091501110708011b0306080604200f1302090102060603011104230405 72
    0x43c4c01e0149000c2200035140d10700095103031212500544602e980c5d0090303015260183c0304c503c401c0080c5543c20082a4002c50340150844118540380c03503100c0c0c0315448100201c1c0220304024101c0c08a250030701030705807501d080d44030408550026500c02c59486d4000884d26080d405082c01030300044c240402450080c5000c3d80c2c0c0c0315034511000b049040d900d640948011000300d0a5070080c01203940101e05250405d41516010035107071101d02d68003480c41040162a118503800d802d03860321154020500511032101281e1400b0b582d540c280500100b5078044030308042d90481c400300324803158040c0c0c0b44800088101400ca642706500e4003d0582140d041c10f0ba07041001009140d244400703035050140001402c5203402415582c10a1b80d10304c102c031a9000300745104901620030742a402e0b01e41e45d82030f0f001a00001e241420b8881e000d40c0d880000d52203004a1401030094800241403400d05014190030490300d0704c19581341910344041c045001d000e000e10a02043d1030781d0b400c441aa5120f008150191003194 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 161665791 1250 161664541 161664551
    0xe061b1b0607030b032407050a02070b07060b090f040507091a13050103140d1202030604021309020d1104180203060315090303010509012306090604120b04050d08010b07061805060a 79
    0x2010103181086c0c1002c028550085401130007580d40d881d0941d80e421031203900b0303c15100c008038402a41048034640000c2081080860004240580354000c40d600c08410384514401d41c48400d100b00052200705d030040c1030395018800070005400d481d4840501401c1c2104041040003a903400150444108009040c036030752034400510030704c000e0b01801c042c11020000217020f180f030f400c4005008185650382d000c0300d1582c00700c001401521386404880801101046002500b03440f100e0f094001d4121099400d82e080c82e180c04590703204802c004403000d91700025881e800300d141004420b0701942c0010180c03500340c000d1003803100b00d10600b00c242c00d01484110006c1d5840398100414800301d518140e00503014200b00c040a0710b181c018600720302c04421000d0b20b05503030303404403e030124119100701d501c000010f0011010f40820b0001c0008120301491090007a0f80f064502c4420803500c0400030301502c64510001c00581000925179403080d00103003002c2c2585c1140281a481c0e90b0306000c02140e2001c0702c980c0324 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 161667041 1250 161665791 161665811
    0x2120609060f04050c0405040305090907030606021204061e0315030b060f0f0d1112030f04050a0512120d0f0e060906011a1b010f110406030e061b1b060703 68
    0x18010941d00a014240b0250540740548840f982c0f0092541c0641c06142d8a001003401d152140d0100c44440c0000340401000e801d1284004000b001a803180b540140940700d56440040014000c4408807174166582200f102911016003469000d0041d11406140c3d88400d011060540c0034007003801180a00039030606441d103102404a96036203108014401c0e01c5640d105144c070344c0c815104503082030b046801c2007500168a0046241c0d5002050480c45900c0003241c0c1c1d0100881550080043e01d2041d9502801179990398140812007001c078244d0211754100035180b19880500e540501040a241040403401110303004ca48000c5403040300507a22035400480400860380000c10086004280003620b18686130280c010354002800395001ca118009081c2c0d10011401c2000d4003c410405808041000341043c10300703282d51079500500c14240131034104103003880e00c0d4902040301445000841a180c12003440081000c64a50114a0100d8009014000741c041d220003008001c1c851002610000b0311a994 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 161668291 1250 161667041 161667043
    0x90e0a02270c1204060b030c0301050a2309060105060304060b060f07020405060a030510020d0213060e0108090f03070206070203191415010803160c030803070503010f06030504120f030902120609 85
    0x10848692601c040143c001e41400d0040441d5026402c000006103101c00340c00040d04180c00002140d40c10341c01e05041c00f1614a0a9101c07400c004101c6076500c0c48842201d001d0b01e0f10010444588a25400c807030010042c2d414144000c40d0300610400300082d120012800150a50b04003440c0d50305e0414020a05808509191280b10b40108040340c00c078110b14503556840e980e500d00d503010720a515401140b003030341d41981501a5000002195000c1105075140c40e0300405004072442c2440c00078004202003224504003050301e8034813503598806589030620b10b0302400100e90100b00300300e0f0580700394005148003070045003549400070300c140765015a4002640c4030a1425044a80301c0b05207041481c01003003019000811030f02c1071150840540b64215113030070010032443c10b82c0e00140901c2000010890300c660701c800198161410b8400d203072022a19581704401311001100d00810000d400c04450791040e00501c1005001c1036540740c0030138003031440d41c08502c006000c9580d280b41c80d40440248112410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 161669541 1250 161668291 161668369
    0x605070504050a170a12030b120c012607080c04080313030221030412020a030f060f06060c0201051e0c070303050c011b0c12050706020712090506030105010504090e0a02 74
    0xd80c0800e5151135442003401074651070000001020707502030000000280780070b81c00608055000070000c2001440e550206501c41a1145143d0700080300d202c54000a001455241285058420b4501206a4864030709817901c0d40003514010300c0c0082404002980941000100824105031480e41001843c1d441881402140300f040060b142e1200009c908915200005031001c40c2c4a401010003800319030300100c0c0002c0040d070000340c804040c800340300c020300c511a0402c001c0843d24910802260760b80f140e00711030b02919500002c2c00200108205103000036080081d00c0c0346c40002274600d00d0100b600b66a107142c0080390780308034042900401c890301020028030842020304014000c0b00c2d0504944d0000802251201d9002082c405025250410302e61090054070794155002c0011581c40034a800c2c82000c1103003c04044000580381e03800402d0a061001c180da049400c103840b8113083c1814012800050185024010024450010324901590b41e00c5440400380030f0344645401c0328881c0c4014485008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 161670791 1250 161669541 161669549
    0x1b041511030a1403062b1118041514090d120501060905060703030f05040f2105030a0c020c03030f0a0906020601080a0201110a170d0609150e090304030605070504050a 73
    0x3800501c000e0102c43d401003207000e98003000c0c90b103140c2d4070364401c0300048481c1081c2481c9002143e240310f03002d04461701520402111070003003420002c0d06050100300400c0b030100c111406150180d00f400301d800144c1e1040c41c5548140b0080002c01d03940c411a10403044c5d5082280c0065041c0d04c00801e008940ba00808400c2d860074090900344100d40c100740025190542510440e0300603c40081c00c1c0c0c00b4036110754040c041000e07660308180218101418015038071980358000f650040044070019080e102c007501d00001900d101d40701e0034215629038810340028000540c0c050150301400010009a503010b00050030113050004003a91035418100004110f02d220341c10104c2075501000061012031800101c1140c950b0342443c2201c0c0d00c2030286007540c1041800130004002c030803c90308640807041c2c081e020b080a108100403c0203159520141e00050741c0781c0030300c011119440c1d81e0082c01000700d2800010380c000c6255003144d1406540b507482a044403005c41c0c4120000710b01190505c00f524040025400034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 161672041 1250 161670791 161670793
    0x30b0301150b070c0819031b05150903040e0108030703020c0108040803040222021801180609031103070803030c0306030c0a06020312190e100c05030f010605031b041511 74
    0x684200307410109514024140318200200b1070004129141280d440030302a15000d54400c0780314003a6030950b41038561812008200307070300c2c081c0c0c005220109a00c80402d0f00180140842490701c0c4514640c0351010b4010b9005000402c000f1135030b1144100628020b00345003000350f07070700c45150400a0070a4089000c242c104200312042c00041001c0c1030aa03508160103d61100404502c0241e6110503c0d5200803080c82a0010403807002c4018001c4e204501c041d400c0c3c0340c003c0c5485890300340c2412501c0d5400392901044045900f070002c0f84e6520084910468080d040310310098540400502d5038204442901803405c0000c20040d4a090030310400506030340070303680d40c0002410000e0103500c900401410f004001d15000c0001c280030740b21240341c0c803121030410741041546900c0c14601e44584811602c0081d60b41407091400001d8402c40c1101e01c60ba2a04d206005107908041c011101e40e4005001e01500e4541c22400c0600715280d10024001450319214500da0300c0c0d4901805043c3c071410b05031821607 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 161673291 1250 161672041 161672051
    0x40f0e0a020c06340c02040509031306050904150f031104110313110901080a0b060603040f080a03020f04090905191e1a0901020421030210050a0912030b01030b0301 72
    0x5500014060342141c0c0d55034a11444501c101928941648200410100303d42800c04c104aa2138021441e156803038020fa80a1010b0740d12180d42645c0c80c4108096001d8443d05102c7c02c11505100d1409000715543c0100080760721140c2800d03001c030306078075600140c00b1003600c0700c01001001005101c4081c01c4400390360038001d41c2600d50001260340401090302070340c041011040f200300190180540304902c0c0003010302c0e50550312440c0072550b4034040402280daa0301c440d0301180840c0751940c01d50703200715032080900f44c203e4002c7da14110307a900500c1d101d20030715400f401000c00311125200a0806401e00d941c0c001407840180c20300900e4220148c00d0501c51584e5500800b002c20800c031a00d0f01d041e07200c104141c091070401c3c070304401d0307403a82060b0820080400000303000c040101900103004588140b1440c1e4848060001a0240c51098100041c0560b021101c00c851260311074210380c1e4000c0300c044c00054080020345500501428401c002d400003980d030290348401303627018464030032085010380c02001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 161674541 1250 161673291 161673307
    0xf0e01050d020d2f0a0e0411060a1101050910061202130506060f0c010614030d02071e03020301090c090f0b1309050a0c0806060f0d03081303020111040f0e0a02 70
    0x80312082049010f0302034501d500509044c4080080f007241c035020490114400b030003071602c0340d0380340d6282e40300480c1c41415950702c001a4454403d60160180d0f4100c2c86000c405c05400b010000305034019050107051201c2d81c0325804031980203210719841214540c000e00580e1103006c1d580821502e080d04420011007440441d240541c4440c46203000307540034040c0019143e100c400001d03100d40640324401a905034005900d6240e0081900060f0407103000d003841c0c001e032088002c20181c440d8038806c5e1400059201410030440e40c4000820f41c2c81c0c03000c880400012054a80d00842c1c2554400c2c4415544100c0072407041181c110705110f902c0070000301034810032500c800600000e6103900c0e500c1036080b1507501c880e0701c04280001404009000e40c0c0c0316009000d6147c3c3c500d40c2c0b0b0f0316410201e41562181c0729600348203a1f241408150300f00ca0503415075440c0700d2a030320340c0d902607a640220442541150b5031100e4164945007004014000380200e00e9104230031070b10f00750366502e820b0401410041e91a00600c0040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 161675791 1250 161674541 161674549
    0x810060e15010e01030b0301020a0c02042f070309120506090c0103050907120c0f030f051b061b0a060e070e0c181017040b07080609060f0f010c0611040f0e0105 70
    0x10000c40024640070a00f0000c22004801410801c215540d141d480042c0a01c030071134000d500709000b1442500c0900540c610601e50041d10a81c1c11103811194100c04940012002d80b03c000300111803107030034000364503619503c02c1501008200c0301102c4d1366200100340030031110100f01c195034201e0f09190501c2903241080c00b5a4560000e031249007a41074940408104016800c07032840003504030b0000322030885036039003010071403070007080819141d41c000c00e4244004030406402906c1c03d030070b01400084c50310080034401c828100c01d4020032405402804540c00011315580111484518804018801a07091082c00c2c050001c2c040e065541c407490800841551050f850180702e82003004980101d003455400c00f055034811b082000050703400903124104810400481d00842c010303401940c0d205503650303410060140601013662020b61090b01c81804032203610745841070202c404011300d030504a0148a0340c50b101558020002e20b1659034010800780480089151442c0c014501d03c42c0c1d405240d45840003217 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 161677041 1250 161675791 161675821
    0xa080a030213050303030a1b0e060315010c0b04030e12031e03060102120c07030b060108100b0c0c0a240c12081819030905040e07090504110a0810060e 66
    0x6509064000c2480c402c51040e00000034010036001e01581ea485c6441c005120003441d000400ba01080c030482481303240c8602c64610b103014180060495459034071240c050b10742441c40084918100951041c015001902c14008580031b284240c8030112811000000c001c1059990f42d20001e10f50301c180588903400d03c00705051184034414008059403900d072200100c0c1080c0609942c0d594898001640110701c107030000c1e4000c01c81c2c4c0074a000e850941c0300c9800448482400b503c28504100b04440203226012401c3c000f841741c041800d0459106032a05000300340045600d80c007078402c0c0544102044165640704001485060580c9499129144a981c421100c100c5c1d14483c0e0041000480002c5e40351078250344046100003d040c1141d0002040071240c81e0202841c0e5000c900180300c0b204001502e0400b070103181c80e01402e0602a1400505200e0f4040041c2401403060740c01c0201c440418550b51941090343c1c2c042c29012000c0e0500b144000078200076645180d0003070110750310b450100901900c0210b60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 161678291 1250 161677041 161677057
    0x14030a02090312070506011805130b060f2206060804020a0e1003020411130501051c0213090501030503030a0b030d080c0c1203010b0706060801090f0201050d0609051501110a08 77
    0x41e100d00684002c6450403654500d80380380040001411400c5c4100020078038102c50f002112100c0101c00c600080040d0b403403c2d20f100c500d80d42380034032500016490135000d5900c910b020300840c2c1744a0b995000255520500c81400151100b130345814020410940070320300151a017400c20036000d04255004c00c0b02c003202440794029409403000800d04a0050450b04001560010b00500c1158502c8900707001c145d011008081c0c1e40c0b044080300107a00e50003039058640b000e101689000d04c00c07400c1d0860801950107181701f1000d1405500010a100c000c501c101406580078500540d280c0c0307050003100d8120340300c4070042481303648013141e000c4a4a60007900c443c1d1101032600035a44804142c0350390f0b40b800488540c041e00d41c2d400400041901d030100b0b809460b58900465091014070764441c034a500300c543c100c40242842c10903055180c0554080c1c3c000b05103a042c8580e0010340c0664441044044600541e0b201e4078440640080c00e40644e4130240301d11039803103034001400d0004003a540b044601d04c200c00c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 161679541 1250 161678291 161678311
    0xd02010c0209041a0709090507170c0903340b03011220030723060301030b0c0307020307060507020a03031409070603050a0b0d0b0403021c0804031803060c031401061403 74
    0x1c0003504004d014419034280f00c0103000e110146050040c0040c003250581c1c01a106100c3ca048006a08284144640c1700c0f5140827208205240d02c0310450840207174400d118198240c840c0e022803660035001c04591201c0011103c80070011400313542c0080c00c500c07805611452820100740014014904943e40301d550150348082da140508104aa0380000b882000000a515001d0b030140014410302280040a5822000d00701d41c46c40e2002100700000e0740000e010151042001e2000203e050009100071900902103004a0341003d0003a41e07250140c0350704a406400581045014004140d01405120100301c02c0d0b0b046038809262100b0b42d2581c4142c0c5120314010180c41d5400304a41c1032445c1e104040c2c81c14050040c12152660742828030070000180c801320b0051142e1400000a4070300d03901e00700440d101075541c10300c0030349039910121550007043c881c001400c03456200010008902e0f1240d0940396146803000b20390a400c46c00f80101041d0140c0c414401e011001c100c2c17483e800902011280c0c4100019 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 161680791 1250 161679541 161679559
    0x30f03060f090405010c0e0d0f020d02030a0507090e06070f0c0201140405120304080f060105180a021227070b040603020d020702101106090c130f0f150509060d02010c02 74
    0x40020384100c12085006411a0480040c0002e04c60190041c5a2100311038441c1c1c50394906003410b1001003003001101030045144511170000519200040340c1219000501f202c109180c07075219242424025840588403540d50b18144d00300b040248866940240c060078010000038600401030981e1003200300080c10000d010f2003605040e0303031800075034000e460064203512000540e07058a50b80c0ea071050007511514030070320b100300c140040006001b6042ea94082d021130207101108080790181d100282c4800d0a040c0c007404581080c03100341c000684a40200c114549801801d00d0440c0000d005034a816005508140c8041c00f142d4000b0341118211561460010390b2081c14400c1d0100034041c80c0070095020b040768528201e079a61050592550b00b0001d419101d542e290049002ea0380c11020016582100d03241226801480c20fa070300081441c4c4280101241d030b0420a0031085c2211201200f44061050451080c8001c1c20800c001d0340e840b81059540b000a401c4503000a88600d8400c01c000740b00b01d9480c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 161682041 1250 161680791 161680801
    0x12090320060d2a090e1005030d080414030324010309030912050705060a0201060e0c0a140d0b032b03110919030c06050304200916020703020306010e01060908030705030f03 75
    0x1680c0c0c104000000e0300c3c0400b0a01001c4000c2c441c525a1040183c90005840860f040d046080e18010031950018000c11500001109c02c1d20104001003041c0c078882e1015101c0c01036000f0602c001c0d40301325180702c80046072003950350310030140641c8072502c5c41c1010b01c0c080c080c00000740c004020009403042c0800740350000728149041c610340500360300826081000410202e52030390b0150811001c1d10010054062903a4550f9101e031a07030f00485211800080b1030500340403005030528024014015510b0000c2042c540e400086450100580010042044d803101915071400082000502c51242c918003402004003126550003036000d5041207a105405511400b40c00f064031184100c01964460391400841d6074500001d4015001100c2c03d5841100f00c02c4000586608100b1005804d0390040503040181c4460745280d0002c0d0640c0d07410800c0d4810b880740400543c0c4c0801010340200100820110198105400184011341c158032440740c650042c03141c4000100c021051f2480c4c0d0003044041074032941c40c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 161683291 1250 161682041 161682071
    0xb0103110f060f0d060b0a0c290f040210090303020c150c12220510110304050a12060f050709030b07090e0a0b030c010e0105040e040c0312090320060d 66
    0x1009460070b42c09000000c0903494079548502904401c054400c00300095540d0381106041031041c1c1d040580001c1c100400c40f0005140003a0002005070502d113202d01d151079500f05154500c400707460744101c00c03134410200021441c141010225540c40e9140000c51140b540e98081d645140c2662001d1151480c3c0a19000b03400300c4200366148440841c0445031048a24803121000340e100380250801000340200014a503001c002804045600240035082d00700c195420448040c0b4505c07070b040c0310b1070100b08000513466540c0b40407603024001c00c901d60040c0007450b05d4402d0480c0c0e4844a03101c0228200000c010406801101c070a0272070b80c0103103c4104c55079901808450030707030661308034030305c03486040e0180056400c141e0301401708000b00350222241840b0340741c01035807072004006e48140042c000700301c203025503000c160300030741c02c24440c00d54540ca580e142d603900780404c1d21001e48940058070002081081c0000c0b2444543c041c07031120000c6a4541d02c08020500e148296500d03285201c8d201c407142022046 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 161684541 1250 161683291 161683309
    0x30f061a0d0917030708010807091a0409060b0405091b040902030c0d06020c0d0c0308090105010b03071103040e2806031110021606030c0f0905061602150301030f020411070b010311 79
    0x203e181811a42da140007074000d01105003c1c0a040c2c0e6603c540100803400c1c02040c4030700110020051140c2640c00010340130030005c0c112101c0d0440e50340383c84840d4001e0a807950301a080c01080580064500385800c1c4044101800b0314400c4a84500c1c00d19050a000d41c601040180700700300d042d98000034040181c2031a0001e03104420703120b04140f1406850a45a40c2e211454001141c03003a074403a88551501c1c0e0019007079480a0040a00640d400c10210301c04174058041c010030b50b413186c02a43d05003a62000e821240312800c035054201e07019030300003c020a512465507002d0040040340d003000b05a0850720390bc0312642c58141c0b20350080c80c400883c2c0440f14020070030605841000ca50700005580c6841c0d000b0083c041c0b01804c6c0c408940e41c80c2d04000054018034a86040d2080075054034101030102902c4044e43e5020382050ba040000030b296840c03c02c50306801507001c0c3d40101310f42403251045105103c02c90303450300600c0300421018000c0c2000200d40b140003038112a049030b445160324441c500014071000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 161685791 1250 161684541 161684573
    0x16051306050a063005070807020a0c06050a0207090f2705060a0f020903010f0e0d0f0206040b1503030c0f0d0504030f020d02010201060918050601060f091a0910030f061a0d09 76
    0x560982c20440304c800b43c0006210304131580d51180c4c44d03280c000080c0d03540c89030500d0091090001150a00c030301880b40c0060000c0f84040c1c070440740060b40da01808800c0701ca625540ba135000d62529008102044503000c59081900b500b110003a1134a91611656203580e005001d00316180c1d16010300154800c0240c044d40c01b803039401802040705181ca00d140030000c1c0704040318140c50b03000d04240040a5806504072060700c020a030080c15141d40d1f9035841022071640244007101c0310420012025254800300003410464000000401c6e01c80c1ea80791b0b11038a403910961214041110400040c0000303210301c1000c040c03040e419255075500106520060303024002540054005519282c603c2c240f90b41c404a820030301900610903034a60740d03210901213840e00744a00069000c03a0003280100442d145403681c40100d5a040d40e0802d0601032003100248054135800082c00000f40c4039000c00c0c1c8540901e01c102ea0051615208180d8400b060102e15503050068005580300260b458070040140045904003010314 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 161687041 1250 161685791 161685857
    0x16030b01020c130b1509010507030c0c0e010605040e09120d0e0705040f1d0303010509060d05011e020d2a0c050337020102120114060c16051306050a06 66
    0x1c903e41a10002c0031304200035845210088403502602c60008100d4000d214107a441c0c030304e4a20b40e610182c444444144046610901d200c0380022a070800b0300c41c840c0070f0a482e507a811b6507a8500120900050005001c150040e00b158800f00c07a0041c0307080466082580c4001e000c00c642c0c1c02c0440035814009617a011035046030078140e18501608059002013a0300290141042a0303c000c0344205541b07000c24050381d9000050400401d41d40e1400d10500803841d44280700103d516030781d404441119421006480d2000c5802244000e810590340c080d03c100703110001803140d83c10700d446041d00c503500c8509102805002c1c1194400c0140700c01030040f60006141450050003c4c0703002c6019000c501c0e503000c00e1109c8814500c090b454000d1041c001c890b00000008494201a402d103910700d0a11105200465400141044010849403060107190b00c6040300f0001038008502c0d050600c86070209591004130113501c3c0c80c01c1480180c2c3d81600500a03544103241455901120220768601610f90300501810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 161688291 1250 161687041 161687059
    0x6240d0b07020706030e010207020a260109051605010309030e1302090a0b0a08010e19021614101503150e01110f03060103060f030b0609040312020403140f0616030b01020c 75
    0x801d40009043c01110640d0382c08004040b41000c24600702d005a0303000035440b440b000d101300309850108002d40b480c9040d180048100703e600004541c02c507404180200c4040e00101c1303143e6101c0340c01941a600078402802c060241c1007003030f94001c251403420101144518201044200d120102d54103584c58100c014043c00c2c0c0081d2901e10f10f14403a04078010b1040021282d8001250104003d141d01340079007154040030810900400c4c0c03400103500494807003088203c07074117208804158001b807640034181c0354001921040c0c000422040070341d0381c0346001840c90b15406000304006507656403904c1108050481c001040710340d801c2d2250140421215081d60b0000114102803991201001180110006d8070208035413603813005903450300c900302c3c071026106890240001d500340c00c001e04450340c042d11920f00001c055403181f02c0d030012604250401d4070402d00380700307204480e801e04108000160403010010240c80c80c1400ca070f160001044506801010344480050715940d00030411007041e441c00424002c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 161689541 1250 161688291 161688301
    0xc010e06090f01020408101a0405010e040203010606030b010f080612030a0f021504030c0f0c0e090115051503060d081c021207030605010522080105010e0f070206240d0b 74
    0xd40d80c0410350348680c103402003100c0601910014400c507400c0795002c030301800c01c9480ca00890001003811542d1240d2000800100c00b82c659108d10980b40608107641000708182020b00506007140c40702e8020005261034941c0d02c1071703281e07009075070548071001e00d1501d01c80d56507a5401050000e100c0008600d01d501c00132860441070f640000003103407030841d198200c03039015241c1141c20302640300688001e8003040220502e2070104924904400855024840010001c1c1c1e07520400721f801d5070b007210b0030069659144143c107548803a10301c1c078200070306080f50007e200552124507800a40310182141b0b110b1980003420804202d5800107454501e00c80103181142c072640130344607030081e40c0655000e8102c5200e660000785c800d40039102e039405840d0103940c5e180c00c01c011145511b0741c4500702041c4284401b640440041c80c1d00c0700340500e0b40a0803160306402014103000f006d00a0442000d001102507401001c1082201540c0c0321001d4503850075031400144050000340440c003010103840c00034280200e41000c00c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 161690647 1106 161689541 161689543
    0x40320060f0a021b06040c06020c01030213150c0f06050a0605060703090b092b030905060412110411070b1023040e01020c16090b06040315050403050c010e 68
    0xd102e0684c80c00d03000d4035000c03003124201c82e2006108020b00c10580d0520803d01804400e08003541018000600d00180410134060305010250401c03004000e240300c0c1e05414091034004c1b0020800c5012418842c014040464492203080d0600e9000105030070290215a00342e5090f81c0d54800e0b15040a00044c241e5108401b26940081203400070725100c0040288001d14203510324a00420340c040f46405400d402451b4002417144400344010401e0303991803545500070a40c4960008503410f003280c005001041049401c2211442c046410300070803860741d102500075140c1c140a0b07600190b8542c01081c0342600504480320b0292085031803a041c0c10560041105000c101001500301400c0c40725061802d50002c5d0a1101d007048003000300000d407200d01c03e00c240e40e682911610b1034142180c464122664a001d07801140c03030760b11070000d024140700d40306981120034810000e100540c1e10a03003079 = true := by decide +kernel

theorem cover : BRFrame.Cov 161510791 161690647 := by
  have h0 := BRFrame.cov_init 161510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 161510791 ≤ n) (h2 : n < 161690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
