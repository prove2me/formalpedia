-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0593
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:38:04.37661+00:00
-- url     : https://prove2.me/submissions/d66fb07d-bfc8-412d-94e7-7386fe15d9c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 106474820 ≤ n < 106654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 106476070 1250 106474820 106474853
    0xc031611060403050d110c030a050109061a130b04020d0207050105060f040e070501081b03010b130e010506040501050313021207030c0b0408030a140418021c1a0607020409080307020307 81
    0x5800b0b010401c00200000b03440601e448250804a40c00106c2c00d40c9607140a1060786410b5140c82400c44c0042841010b600142d00540501e10501c20050f008400d044007800d00c80405070041103e80010b03088040c00c1d840840d15a80c0104003501d0803203c010800242d030000101660395035580e00c2400b40a1030550312607514440c0654090148810b030044040c0c544002e441064180480000040c441100c06002d0848101d2040442a100d5841da01d03811a25001003d4111004107a8040410b40014629001d81218002004030749810b0515004440c95000548070f0b140e643d80d03a12000c1c0059484059003801c13655420020a411444c50030415a400c200350700c6001084c034100418040070700d000c812540d291805041060441c065814007503000d11455214900a0621009601590f19260018130041d1261a15440201c00010406045440500b15070400441c0e090000645007480e00c041d240c104d00090000680840301d0301c504020380d1080700e5000058000081d07580801103030030408640c4c0c1c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 106477320 1250 106476070 106476079
    0xb03060402030d1407050106061e090803030a0c1704140d0e03060402010f020f010c0f030f020921010e0105011805070c051203280b01140a08040206030901020c031611 73
    0x1810941c0100f51290403000c02d035820014240c1d1300080045511089402007a07001000f00070703481d40c440c00204180d14114150744007034590500d40154034411400c0c502514100005580f5503100d510b1440b00502054003404140320311070f2200b03030010303c01141080c42640946400d154001b546400c050800158107030703000501c500088068101d84000882c0b45d0700c02c3d420300300501d170044003c5d42a86030071600d48280b0b445600300843c103a80d503640400d000700a4252a1010701000d81030780901804e0340540c034070940d0805c2102c0742c030a203505849030b0325560000c0c890000062a0a0040700e40c0d080d03400981000075089950b490040c03d2450b1031081c158040d131945015509044a5078405403560300c031003005032410502001054489402c0da40d42c1384c40514040300c4040540211007468054010440c0381c0d8003040900c03000d50b02d20604a07045511102881e560920955a15820024150006820303207400703640c00d200812410304100020901480f41d81c82903441d04515181444490400e0321303406019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 106478570 1250 106477320 106477333
    0xd050f2503080313020d0b070c0c050103052a0405060703021e150f091501060224060d1e06150317040e1801090206030c0c07051005091903060504150b03 67
    0x4502d21505694008040075600d48a01900b800062100d500794603002c0c00c0c050442050011480d0005000d0704820720a1a50020240c1d5030401901122012603030b003a1a03c1d640f0306080540c60710b00c003071052100c100302c0010b4105038560004c0352054128900803000f6a10030701e0b40d2144101e20404144800b80214020409504001d591f0151008c02400201c514240d2101107400207805011503501c10021042844241d0794a42c0001d5840301800034080319142114401e1488001c2003a01e2031050742e01900c0c202c0360120a0b17851804400c0c0074881c24900500b806503000c000364840c050400103070300005020412504604018440c044072141c1104016020041004540204c521a079440b1071455240c102404880c041036000d40f0180d04001e41c0010b0000422007082c82c43ca000d05064581d401c01c89041a0b2140144411065040401340100e0400d00c04090343d0b240c401c02c01104425030603150041075a4a079120750945400365002c071007110358211000400b1280d4840c510000000b10f00074000e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 106479820 1250 106478570 106478573
    0x6060403030e0d080415081920070201050705010c0c120203070201080406090609020904050d0f0905090105040509070801060305010c0e0907120b04180b040c050604080d0302090d050f2503 82
    0x42c840a01262a02500036003003110b0031301106030150740c0103113983c40285e107013000310b41002424402c007100d00c40940b103000d4034030081c0100603105030010314151030540390445080880825141c1c1001e0401c07030410030200400d600059080c001c0c0261040a034480700103404007898000c499442503604c0d402194018400400940c1c2d03c140b1850b0800d030001d10008400d4803504110014080005029400880c0c41081c4001c116002070300c800a1540c998411402d02000321b02254a00594410300364011205001401107203400d070b101e5a0481d4104003281c2d203265881d001d160a58032030703a1055440da5507a0619222150300300308240000d00003203444d6407040c505400080c2c40b404040c12210121503455000b1902030702e4551004400d00d0400f4501d020b03103e05850501080001198202c070424400ca00002d0700341040380669042d240b2000103002e20500510088000350070a03c03082e98419021010600403840500c1083c1c1b0b11442c0d407026140e200007030400c04050a504016803620119603010810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 106481070 1250 106479820 106479827
    0x90507081305031c09050319110f030702040b01231e03060d030309050106120c0f0e040201050d050901060f0308120f091002070204020d021201030302060106051c23011d0606040303 79
    0x260001c039142584004006a030803400d0040130a07400c010400d102c00248c0d0310300c012004220600c5000c1a55132110300e400c544a2081c0c4031105181050388551051210030014602034000814890043c500b07800d044c100503540e09100300d04110b0810712080d0004070b0110359485500c00030700034884070005901c1c0d401c051002ca40d0a49611801030300f01070ba1001e40204201d030a405c42e1004050440480291005504001290301d405120f07050701000b010000150590310b41040a1095030141c6845081001a16400c40581001800c0711040d540e940c82c0811144500c80c0b125018500940e0101e88030070750200340d500e503e00040d06400514080e801040b80010000901c403042c489072070409621402c0038070100b030190184030083c182032800480c16119881180210504807030199007111580e0740d036aa030643d150712070074240604080308180e140366001126081a07407421440342e254401a0001040c1006080302a080400048221082c00e0112084400c42d031b40c00c88411142145800e00e10756025 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 106482320 1250 106481070 106481077
    0x1303030804061508010209030f0105040206160c03020916020d0c0b060d110d061e05041707031b08030a0c050301151b05031603030513020a050402090f0a09050708130503 74
    0x90810038120009801c110198005400e4403031050914005144c4603455580070350420f5889034007038401c2111503601c84c0760501919016540140c2164a40f4185854901c81407040010903203003601d08000010050301c0324140c407403045d481440170410036a4480402820300c0c100315003101c200103085800f5004604080c2d25190000d108403146414404a4900300300d811003241c421b16401401c40f0090400e0080070303040310402c0c05083d18850040c80d49803503c00100c135415600900300200074035421408070036150041102c00e0090404401c42140c4140a000405503c04201c490310b002000340402044030740140030034111301e41440c0d8210740c1030210035442e0051884941c0304024095032421056120868031088d40c540200540341c2e01d0212182d9124040602401180000c2c035000002c0e07000b05c01002c860416513030013400c041c0305034907001c1040065040030762031035844500d4416034bc00981c2d0345140d00e0000c04090034082900c0c81e01c1d2901030034107840100b803481c003001b401c0380102c0081c00200c110f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 106483570 1250 106482320 106482323
    0x60c070501030b040e06090c030105090303010f1a0c1e010e01020703020c060a0c142407050702090a230402030609010c02151b0403061b0906050901080c0f0301060c12051303 76
    0x4007500c3d41c80c001030150071090000c84007401000c043c440e03401008079203441da0301000e81c0207005035150000c0d04ea9aa100900c100381c1c003003c081e44240300039100030034401982742c0d082004d642010f40300e40d425401d081607404c56601d080741030300c14612024001c0c0034021900480d20000c50500100d40c03000303900c2d8a80300510b180309000000d01000e0340ea004407c80300d8907175000201d141030356038041451651003c1e00c3d854a49903000ca10040f214145646102500c12186952203c1c1012210b500b800381c0e10002600240c14aa103410040c0d0311002d0082d6010759054036810001c01c2800c1c140113142c14500041d1040090b039050040c0640c0580c1c0006842c503176560200020155581d507070034040181c09070003807045076181c0002400824003000c0c0d0000c03207180d0702c21a003101c4c441e5000e01c0140d81c0500340d407141d0340c04580e0a010314041580504000e030307400700b03003601c6944c50b2501140c00040158401d0b0041c4000c0ba080302c0e00744042c4418100b18240c091980d080031898007294031850b03001c80c0ca00707210 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 106484820 1250 106483570 106483577
    0x120304060212130e160e04090f02090a290f0d02090103020d060902040929091c020c0604031a0a020705030409020c0f010f06050102150103080405060703050c100218060c070501 77
    0xf424011552080500c0c802005503041c280c1890402e07400c00c0c403c01c0c072030142c0d4400080c03100d800034010f46418031602c1c6149600031152000c0c00703499802d110070010024030b108813155603844d030b141c01044054196035849080c1d000240c420004e240400c41c0c400c2d61106100c0c080c4805480010068503007100081c1541e404540c4200462004d192040180c40c0b688402504903040034400010004400d20000c6a24a00319000440c14030a0300035100100e800c4500a6190307004060900044030189902e8000044038415100081e41074404980709503ca60700480315110030f18120071901ca010030b00d09030405140c000552501d05035880c1e4564900440c010a0b80303079070b070000d08200d1102c4c0411040c60209030f01802801440f1200c0202002442584a540c0c094051a4605046440140703d441e050340d6211001c20304050401046c020242c0010104806021042000320140c400801100c00704040306100907a6610502e0f01200c050b401c8440014080c64003801011110705d008a600416100300b0701c4d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 106486070 1250 106484820 106484827
    0x301150908120714070e010312110607030b011b1b0f060c030806010306170c0a050402091305060d08030108070515040605030a1e06082104030b07320306120304060212 73
    0x100039420032440098003115115608000418030300d00300e51b04e41240c0c010144000107211070079095510001100700100240c1240000035592070203541b00100405041c5454130034079183c50075071216030150040070359555460f20305600c403032a0b880704102c02501020060b0345480d0303d441c1014201901c0d41307038002c06000b04100080c42c0b903407207a03000030001c02c0d9880d0f00340e4000d4084d01c051502d441140286030b025a400d560089124145802260301c5e05001a200302140c01103071410400425002e011203522030101006c64001c144054081c5001c0c1110b100601191847c20040142480580001d000c040b402400208000c070b0300b01080c1e0358004c90f1407c0101c4c11074000240403541c2c4540c4850380c182d162a10303401041c00b030030006600d8014012001c0b000c0401c5035602d1600c219015610006200c2d40711400000d800d41c4c4580d401c4021000340000b010b0301e41104910b074003401034000460f43c0c800c00e00401000713014580001720310b4421034400061450942003500c029140d05c0b80140a002e40322001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 106487320 1250 106486070 106486073
    0xb0a0f0509090a090c08030a120b030316081308060103030804060b13020c01090302060a060b09011103070623160914030c040509030406090b090904060e03070f050303011509081207 79
    0x400c21288003420050000500d07140500101004010810098420401510340802d068000108030384501e40e0130780301e114030004c8040c4041c0c081c200050b40300350103020501c40020203d40b84a00b00444c0e600c140b00742500c8020500101c8803804454dc0603185a602100c01000131a401c41c0c8115001900300001080b60520000800c641c130203841e1018810070710029030b800450006500ca45800c40c800d5080d00c0f52615120840400e0f52014024042e00e0141004007000d158001c0c2c207800340084012081c0d90524079562518021a0b61090190b40c4080c0320f8142180358409007100320364071180050100c0e610b00b0010600601011440c00380c80c104112400d40720101e66030800a580407064010b10a122074035000200300e07180c3e0060710031540880c152060101e04a8080c2d01510203182000c0c0c150030007691140c0320f40c0040d045510303100a10380000c00c00f40000c241c2d44007402c0010f0f800341c0021036a07949030481e007e0000501c481060f04020078403909202c00c10003c14145030f40240c040382da94660352036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 106488570 1250 106487320 106487327
    0x4030f0201090b0108031c02042d09020d02040e0109050f0f090c09180105010501020a12030b010905060706060501020c060405011d01090815011a0304020f01030504080d06120c06090b0a0f 82
    0xb8a8014082c42400c9000084c0b054002009201c99982185482080850703031001c0000d9008a0042441003542d500780900c044174030521a80402842c58450f81086d561100321500301d034400001c1840d941d400203024400e0000b1a4125401080094801c0250b45426820f8600c03910f07010323014101a6a040000c81e0801c03004100f0404080b030024000c5d00d09040107a08000c1d688082c48100549508080001403558004503400c0e404a400550041d080310302e40030100c00600b180c41c000c2c1e05102c1609008200c64540401405085208210010300e80e0304207000a8030302104a031316540320714402c11050003182d034440302d50400c3c11951400407074620440c2005940c0000c03640c20080c0c003440341d54904ca46072200060aa03049810044400380d900c014071020100c94801110060340103100d060240c417580d40700e07900480c2d0203405240389600381094810f1600660381f590b400321802e020702d44c0380c05040c4000c50100c5801414035081c11190b40380b13403202071400740c0070f02c4000d00700b4001807035007210b100f500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 106489820 1250 106488570 106488581
    0x210b04061703030906090d0504210f03030b04050105122a04051608090307081204030c0501050903070308011d04020907030e010c11010e0714040c110307140613020904030f0201 77
    0x44050911104509086503203940343c004aa02d00e242e44074a1010401e0248081100c5548050320354440340b41c0b07070070407100c40060802e96404010328620b492245011401403122426118865a80841c40452150801060b1001a04202d106002c840327003010042d03400040e555a103280c421f402c0351090400c20a8911808460302500f5040b500f484104140001080c002c02340904807500e40008030784503d0600307a5640103210f0018010b980806c942d448820041440176400351192600c001d41884580d119400c0d9042076a1601c02544040350b038004054004c3c200d01d02400c05410348200c01001041c030810700000240010340500254404110900d1282e0062a0413240c0070002b44000420380200510800d14695225039652801c0c0340020214070104581c0f04880310711010001080180342000010041e00c20f409007030000c1481c13130440c484010f00c0038180150289422010220003131043d54246103001307003007000c1c84540b1a55000180d0352010301d65042038040c9000f0120400c00c450a0b8014071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 106491070 1250 106489820 106489829
    0x509010c02130908070c15050a20070308030907051828020a0203040536060423070f0c03081b04121103010b0f090a0203040611040b04050f01210b0406 66
    0x18104800f41e400c0c031550400400307859101d02c2c40e41c07000aa0f81c420f00c4100042c03048072100000c00410403d42d90500c00d165003a010002c45000030b0503100c011000d20714010307542d80201e4020b5000b00070440303e01000c0c44030800511046d031b2054141c0c66183c1d208100f145c002014403c100d08840311800c4800c00e10352002d05040c041d4a0215500c000303682c0c010b940c0ea003181c800c8521800e2850110116036011030354034001d00c03086051100d0b01171000d412101641000401d004c0c3c02a5072103114000540384180c0048001c03240307248c481420705006400a0120031000040e10078030204c0300304100000da01c280b0280e0b200175010300814400c1d581c044404024070842c2d001507000000004a82c06001da901050442090210300801c2065104002d0114036160000115480840e00c1d000910f595030380e400550340f0603c030b000c00240100020f501e4a0080d08181c0000360880701c0402c2c00e00c11420720030ba020580e41000d003407a500c644010304011400c0b03044030401d00c6560b40c56840007a0701d43c407150407a80251 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 106492320 1250 106491070 106491109
    0x8180109020d03090f05010905030d08040201030f0f05040212120f070503040308040618090515120c04110a080114060403030f1103032a0a050f210a09050f0d0509010c02 74
    0x400e0f810010300c00460350107260b4112510319800100740d8000d144040c11558081d001e0b000420680c2c00030794440000800582c141034982140a4080c17005218181d41440000030000d40ca00302401071060790710341003039101210f50140340c44c040441448025034080c00ca04031402561030703040340341243c21070040e6480104490000f250100703015401c03070000d110861403001900512a038a01c91030055401c180c90fa5070224145004105c8903040600d00c586504000804491001c418407001c00d080310b8050440c0c580700d26000c5000503074194000c1d02d182c0101810360381d01d01081e4035000050030601c41c6100080c2441100d00c045442c1e5400341e000001c003000c0007130a480c6c82c0c2c40c1c41d00740c002a2a0700007900001d214a150b0200054400071419580c0c19141550b6450500b5030b81000d40d9660f0344414840115000014207001101c208410750f00e101701040e50000c500d44006240ca54600a0030115880003034010810314441e1550100c10750350f98183c01d1a1031207404e18140081140c8119007929200710 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 106493570 1250 106492320 106492339
    0x903160c1d010e06030c0105090f040e0706020a05060a0506030d050901110d050d0b09040f11060f03090d1101140402100e0d05010e0d1b0807080c01050906041e030818010902 76
    0x1291240401c0340d0494480000c0c5503036030b0340d81004064a8040003c034182c0442d0044c00048414102403000b00340400c0d010f840023902007281140e003071030881a03910044c01a445140801c0411006004441c2c0202004509200303a0401c000001d07103401030b00e1115030030440081040a0300da8810f41c8010722001f103403020380e508048440801041c5034000310b00c8074100350421034810120300707000703004600c01e03904072146140c150b1032665102e41051081c600c6c264841424000c00041c1d400e07550065024000743c000415a0226140010307182c0c1c0101d1221501c1c41e4134182d201e20314030741840740455200e64129100e0210302c16551060b83c1d0f4521584599401c41444107844041020540c000b41603040b4050031504114100401114043c03504102940c920080054202c00070f4250000b60611070720070110340e030505424000a50031540c0444240200d03600c00b8082c0820301c00c3d10008000c00603000c0a00110006c410b88020707107001c0c070207030914049941190030f00350300e00400c1d8040c4c3d203100d0b80289110034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 106494820 1250 106493570 106493609
    0xc070b040b040506090d02070902070f080301090f0b0405090a1515081510060f050f0f0715060e160509040912090603050a0615050a09030209160e06030903160c 70
    0x1d01003811141140c180c4200008500303c0080040c2810356840150b00030403607030b030a001a4134069004040121410b0462880d0100040c1111002c1c1d800381000035000070703a0180d0303104200b0644080c0001c10f4080d914050a00a0380745001c20b003052101e030003ea08643c1c84209080400003012540c0c2da03500341c41704801c004200043e0100d9020443c80b40310f804100c840c2c8501c0e950113026030a5115040c04283c0100d00102c4090182001d0610051612245d0342801a0030943d040b0b154403402c03080314400d501c00e101244100351031240d40064031b085a00c6480c3c0380b40c8418803c1014000300d903100140107010510028035581c0ba00b08007600c541c000210084d542529102920380e0200e405030001180c10724000038007001e4a88181c80c1184d002e6541e0b04c0300d4010075903003941c0f2a8002004103040000a48011000d42ca500b10b2080c060840b01c040f4400c41500804000c0c00110380b4505544101400c0040c401e04100000954100590740c82001c1000c01651514585002d483d81c8408401020300c0f14006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 106496070 1250 106494820 106494833
    0xa09021b0304121502032e03170901032913110d050403120c05040504091103060709080111090904120c050a0602030f0601110d0302030705041206020d0b0114120c070b04 74
    0xc1d074841c81006403c0d6032081042844081e80001c80e490047c6403501c01e00c12808a406110301c0403250509001c240a83e0b1700c0f610342e401c80e0f811b511800034900c1000241c140c1c4959251140c0303810f42a09100f8541311041e110350450340e9001130700c545440352140c2078045915140e2680b004041c00001b58045a580b130202210030003500048ad07080e004540821000c1c1c070070b0b1800b4024030405024030b56405240c10304080030407005005220081d1008210240c452100c0e0720100942e0b40030300c105d502c1d0000410301d0030b40803500b501c50000709801100c100f031040051507200d4040e2260002d034003041c0c5600c207444100d03089801e0220040301814500c07c400034181840740c580d00541c016005178441000c150707207500040d10503c1108111070745130342c020241740d15441d109601442d082001850010700d000c0c0d54104141c0d14810303c8200340c4116a000925005008031031061160300102820301c909101c440302304104081c010044042802d0a01c08000780c035407031840007102c1c80198080c000c0021810f1604025 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 106497320 1250 106496070 106496099
    0x10506010e0901030308071d0910030b0c0c0709022107050405030709050925080d020f0c0d030c0f021309140717071202030a060c050a0212090a09021b0304 68
    0x940c0881d8034500c589040b400c2c080b9405040e40e8054480642c00c1d11101002c45641280300404280500c6080c424896075844000d02401444103d528000340e500b1400c0c4844090800f802e4900050340c01c1041000c001404242d207030403034619000050f101c02c1c1014002c07034002008a16a61400588800c000c4401d0b00440600b05454080d42280c02150b01c410400d011140240c4042c286603101c102400c0310001424428550403100300c207007000c00c56a82c041c0c03031701e802946c901c08000760f000b6280b6445a00404c1103014100741e022900c0ca40d00c20310302d031400341c59480441805402980c0040120081d501c400350405000f400025041000e4022400c119082d044075142c1c03444c0c2c0d40250f040004074101d0600c00820311011100213041114a441810310040c41d0710b0310203c0e0140501403401c0e01003440e074030800c0542034180e101d655480505c80f80c000e003461009001610004018804217072262201040c5105031440080c005940340504e90b00e103a108540c041049240c0d120000b4045640d00d02401d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 106498570 1250 106497320 106497331
    0x21e04031115040e0a09021c0b16080c030916060507021801140409170307170f04170a02010f06080304050a0905011d06060f0703020a020f060315100912050105 70
    0x9070207200c0d4410001c125081d51050444500103100901c105822592004d40044c0e00d5840050507255a6003c50340904841c12143d0845800381c00c0c440500034403501e281c0c6e101464102c59120300550603000350040201901c1001129008000681000c2c41000300811240e044030b0100d40017599030b10002c080750701c615001c9000d01610003c55140c1400140c080c5c0c1030340c001710201440710040307000f0b000042c0281c410035907041400c50a0301800c2c441e03013401580a09001d5442c89400c4182007075114948074040c000816010601d410000404c41c001180707100c8d04c0710504526031310702c100c9800f240541440003000001c9464013100181800000000700f007100d40617601c60346029941d502500032a5000d1248c04050920003540aa003040240307011503014000800d0131342007080450420909402245c1c0481c0907038032400d191070640c601180f058812500407541c842c0b444c80c1400240280f458042c2005001d08008040b072a0403a01540411000d0b208490560031941c00b241401c0307020341016141d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 106499820 1250 106498570 106498583
    0xc0a050106182315040b04020d02030103050f0a0302121e03090d08070504050f06030405120301081b0d020f040c0905040c0206180106030b0f0604060504140601110f0706050d021e0403 80
    0x40b904480d00842014441c007071807041c1c0d0b181c0654400014243c000c4040055617070003907540e00e8106c0d441e0340b180301409144c0020000161030350b0441c9040380c9490030b521541070030b41d03100c22814000694001089001c03000344100301601c480c82c90203245034281ca010100910581c022040243c50200040c507003966405035600d072038a90f1101039044e200b500c01c03400b07016000780ca450a1041203040100c015a0050310400888420102007442e285440d0420713080b00006400030b01c0c00e044000303c09199101d5004080300c0603010703049160300142038180c1c0d82042b41d000f82d88a03080043c2050084104070002e1001030410701180c400707140c00039240c2c50304072442d0b40c20f010407440f00e040b0410144642d4058aa000c8100c44080d1100c00e40a0301c40000140500d038407540707601c00851103440303034054446020301031801c4481d241804800548802000f51a48105901921540351a160000383d003900721081e07802d010f0f988080a00f03120006c0d1003640314031200c2050036184001204500c1c0010005c9034000c0300e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 106501070 1250 106499820 106499831
    0x406030c020105161403090c090709090e010605060919150302090118030203060117070308040e04050c09040b150111010c0e0307150207140f03060106050a110f070303050c0a05010618 80
    0xd1140c0307048107248034500c00003455040170104100020008540081380b80085035650b0107904000707503e0b800202e41e2680000c04104017040b611a4130302903415002c034800024480181400e0120316140900b50003c0d204480960b10454200348101c44000948014000041d50399a0139402501940c084040c40b80011680c6851406501c4c0c1e0904600543e58020003622a0b0b03448c00700c0305a003030010104140701030f0040810010000f0030031340080006203804441e0a80c2440c143c1005400d00c421108010700540400c0100400540c3c9908074079070100c01c28080045040081004844100d0b031240301440541c81c1c40303103c240c00b64001400b0304000e00d040b002c03101c0b0107444408100c114052003c5003009a4840f1000707010b00710001c4030010380640007522202c401d05032a4000b91802c60282d00010100d1400141c00c1c0400e68014400307241100204001c2880303c00340b0080c145d49000034800a41049004141d08003020802c0c001e07a00000d0300310b4003d110041d161410a031080d411014241285845c14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 106502320 1250 106501070 106501081
    0xd0602090a08012309070f030c030b0f06100807090b0318010501050d030804020108150402070c0501030518030708070206090904060b0415052427041a0a06030e0a080406030c020105 79
    0x14000e0450745610108000040c4003d11140740c21000e0141c1140da00f1b020750b14011500c150040b01a0300210300541c1a000c00c10f1560510300c0885802428841c441c10500b0104055500d840c1c039030a10101091421440c00d9a800408440c42c1005c0d0300039500e40d81c0004140103a1040300400d80060342034000007005240d03640c0040101210040c42d0081c081040000000c01560040c8101e40e0b00405462880c1040078401c8000780480c1c0c44404100c480440000c400d0285582c1446003d40c0a081440223100000381c3c24403240d940d00492800800082000451808549401c0207032004400302610b00400d6090600e043e2001d0024405501e00a030b251000e1403440810300603816040700c0010346407134095004e402a03032038120596100c03504201c40801501038441486020902c552082e52108014065036034200010750304403140b103d000014a002500c2300e50307555070365803040700c1440c2000514200c0915015046c00c201210240c0040700c0030a00044541c0c06401181088c0f84030344c000c1100e0780d00c0707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 106503570 1250 106502320 106502323
    0x90e0102070c030b070c0204050a051803030615091302120415060b040603020d0b0a060e0a09020415081003050102030a020a1209051009020609040e07030b01060203040803031902090d0602090a08 85
    0x10700501502400c81c1c0d800400114824035101070308180c1d0b82c07502d4040e0100c02c1d004501541c0059468004a40c2d44070100301e041540081001070441501010f1455414200009101c4e40c20302c4640300f214810004502d00e0301d580b1a0401c008072160300748159141c41d00901c03c140342c2d83c01124280d80f1000e07441e40320302520b80648682410345d013580c501d6038105400c100044000f9007214005510f2659a025864165075800b101c04000340515a0340314102021a802d020394039110303a00c0b6400e2540180414401442c0c0404c2d0402c01ca4014a4502003998030702c203404840000a42c0082c0c5194800001c4c84031191680e001042c0110840e02c90100d021005149041140c10100014000d40c01c9205c9003004400c290700320f61030440c001000c05040943d0300c00040c0443d50b4031071048000c0c0d0702c007810810412100d0001c00b070040010740095410b15150680168032440010b08540c0d400c40f41e100c20806003402030b03040d103100030006451140c09006900e060402980319500c0300e032040310038900004000c0d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 106504820 1250 106503570 106503577
    0x81e03030106170429070909020c07031101020a170d0c020f070902130504020c01020301140a060914040906050a0b03100608070e060a08031c2a0f0509040e0106090e0102 74
    0x58603950043da07490400f15a5220b200e01800899082092448640d0203040b045d01c40c0415181e1032a4110031804c02c0035003d000301e0306507440410501d0050011200c48400030481d00e0032207800400c80405c401049004038201000c00d81d0060001803500200038001e86c83d1405424451600c503002c00c200f980f84e1809980e580031218002e40b099008140510100413950050413100344040c0362800700580394800036060760400b9003540f40d56940400100188100c02c1120111400d01340c03000701c501800c00c1c2d001401d400c000d0240d82545554041c561807180c4a950145000741d40100c420040ca0a010038040007030714001030307160320a00c10b000c01000d06040c81d1003010111f4200c1c90060110a24100c407003c00000c00814041c0d100e01c0c201300c002010f44050009060b400542010032180d0800c4035000000c880c000040500131a0106110503203d810803881c1064107000344c1807901104071541c0003110188140c404d2550014240044003440301c0c03054000c03d0944590f503c06000019035042c0d034600301d02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 106506070 1250 106504820 106504829
    0x40e01060c020d1b150206040209060103061a03130605071e0305070207060e0303040503030403050604150c05070803090703120c02011101020a0e12100203070507050606030d080a0b0118081e030301 86
    0xc070004803040000b4032014041d042c0341000d05019a9135540c0b00c42034481202ca481c0d4600c0580c2000040000b185000c1e40380b2030b40031109080812030141420300e010f80501d8031368140c1c0b0007800000040780d0b4034082442100310403035020406201514000e80014040d101c4e200200203101060a44203072218013a01689118881c0341d4020a60f252400c84101c070800246c070203203905800300b040085155202032000308051401000102000d04052601100c2d0140e020121812075141007080d540300d51340701080320007040d0407042ea6030312516460300c418100000c65100409407107804074025180c1d5040000750200c24000d07200d003840d1142c00311840d0b0a03482600e40c4040000c410890101076807403c5140c28581100c004100c40d04e20811007030b401c04a03441642c6000c0414004120417042242c00c00c01c1c83c0d070024003035001c0c020b0f11203e548082c101362005090046003a171200d9081c010360b44503083c0c5007060381c415030711030820b15a2006029210034100b031604006415603107a80402420000403a4101d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 106507320 1250 106506070 106506079
    0x3010c030c0f0c080d05041202100b06180f210c0414220c0603021801050901080f0a0b030601030f03020705010801080303060907120915051e04060f0b120102040e01060c02 75
    0x1400c042000b01ca8100f092401107601c84400e02058102100c18443d00744105e00c5800e000347c0641003214041e1801e00c16a0001c0c00407800c2802001d9207840300010745049010340089030114001d104c00080002c10250881038100f03100b034a10148000c0310140c08549110b104054998840c00d9809000035240c000a0396414500c4400200326140000021640300aa000c2d000c03600002d03295036200c00b0651076921a000190300420700100c00040000308011401003402c0052800d600c3e080007911035000240711503011200d010002e4010b8000340c100d080600c4c002401e0303580c0f40d030b164644810080c2e00d1080030350040c03080080208995000d890514180d071a80d400035815943c40b40c2c1003049910006207101d0800542e0010409a0702c11030041d8800c661040c2c0c41c40da0403090004d480011200000c0c050f000314159038403491400035107600801d4120343c100402082d40d1554140d035001500c190442c1503000004020400016441035000e4004e44071400151181a6030343e1600f1920000c0b03491020b07500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 106508570 1250 106507320 106507337
    0x403020d08090114070506040510061d0c040f0f0e0603030307080a0e0a06050114040c02030a0c03050f04032a05030a120f09080607090f05090403020a08030a060905100503010c030c 79
    0x414071050140031200c00524001c0c5940c05261110344503074000c039504503600d0344002c090104000b0180140c02141004c1070342008076a00c0d151800c180c0441c81d10119801e40034190208054001e000e08a0300505078080c45c200200e60f841305080078090701c500c94544400801e40106400c1d00e008130899016180d03660362100300d40c460400000007400141c400c20007920910305070390b001400300d003d00b600814410b101c400d00034544000740816140790300c01000854002300300360301d140d98000b504449800d8040c6002030300e80281000c40b004d80c4c4107580000d0300700f600e0482e480100d0022460641011401c000310100d20303581d80c00c00d00d6070744d24801d44000c00182c8211000f03006148505030348103002c4109c7c5080d803036542c1d4880500b400d024054840800040442300d051000000901c42e20000f402d00727a500d005076243c507860003511482c0c21074004002400000108424031800c2d0070003005422034103010051800c1403140700809103094440e1074025400c3c943d80804442c000d02ca411081003280d19020603 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 106509820 1250 106508570 106508573
    0x109030e01050a170106030603050c0316150c050105090705030706020102031303031e0507030b0123070b18071805070216090e0a05060a09061401120615080f0a0201140403020d 77
    0x3000e410400f03c0b50f040158000c2110514070780c54650707a008106030303200000c030329056003013180c10043c201c80303014081e6100d8240500c1040c10300c05482c080301c039411110650526000804c039404084030310301518541c00c280c02c1c016036600105040701203880071012200700a07981ca10a9090340000c40d00035032400507004d481d0300824001d4209592482d068258007100803850184103044480c1640c14000095541c203551025581200d64604a908420a07980115412002036a00c41c4903120000b0007031000440803449000440800260740440710007030780d50098880940042d546100384810280341d0030940403c07989170011a41e005103107106015500e4003801c18105101401654080c5100ba03c56100c401c0c010483c188800703401414409404614411036090a01c143d4099240a40030342801e04010000c403c0080140001640c1c070007000310b070259030442c0d1003036403d203180c0c003c0a1600405c8410b06003648041000d03c1d0f407074400d80f10440d0301d00d440f01442c80c41d40030f5404000e402210311030b041d50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 106511070 1250 106509820 106509827
    0x1140316050105250b19090b01050d08120108030910110309010c1e2405060603190908030901020316080c0409020708091507110913200301110d0e0109030e01 69
    0xc4000c04030381620b80e62030080381300c0c180740c0c8059190541d082d90b0380c1403d000c20f50070b0b1403040604034032602100f03004131540c90310f030f40740100818820303e88620314001d0107008000c000070946203552113050701c040c0300c2c0d07030b440c1e1045403130b80d010454040c41240765100d90421a409060071140c402c0c1e004c00158104911200103441c3d801e2200c0042d40d0812100b00c5118000103154240310015118442c10300510ba001882c54004030502001e440701c0c0c6042400f0000c03241c40700002c0d60361044580c920100126000b0f09040300601401d240505846000010040b904070150001c5005451000c00882100054001104e100d2401d0725407404a0904000400c0040302c6074001c0c2500038000c28110345020240c400248000c520641d1890507881c001c540001440a50304400c819074001340c0700201e092411320110302c01409606001480d841c450108090407001c080c83d00c00c115070303000c2c000300180c0510194501940d0482c500e982e518606040b0106096a018010b403245551705840e4014400705040064 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 106512320 1250 106511070 106511077
    0xc060e060a09030206092e031401030b220204020301030b0702150103031e02031308011409031c021c0903030203091e1b1507030309020a0b070209060108091203040b01140316050105 79
    0x1070303000045800c0d250700d04403a4802e0356011502247c0c0c00b851040c4501e4080c0075035001d00c0c50307001d20401c86401003000c10418a03003298001c15405d421a01c41003003103005000b0482d00d06000e5003291012002004014411100f180150410f800300c500015455010104101702400300800050825660704000d10005e80c01d62481009070040e42d003003040000d1154a002d800f40e11440309070f911a0410820700b40b044000075040f010b0799020f9440c1160440082c0104102e02c02401001d507030006030340560036516598004c107440c0766801032200610074100107000c5d400c25150b0300182d000c0c1c00d1032900220301c2c500703502c400d26035060b01804095102502800c20804003600690b00a80b401c56443c00d0709031b1a0f0000c0c000a07100352000103144e419801071026814054212140c90b020030445200035960f60100c00798841000d20b00306255680d120b000904100461681c414100000f109000c104801140100e040e44c3c00f0302c011000b64100b00301007540da91520f1004481d1620310070350038045940f040e00207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 106513570 1250 106512320 106512337
    0x50403050306010915140a0c0609050601031406130201120e0d030501080105090a050c090406090203060406060305010c1b0f0206090618100216120221010e0607050a02070e0a0609090c060e060a09030206 88
    0x10085490300e827208800e9030900802203070f0320381244006000b085000c1008a1012000100800013803500c5441c144c0c0c40e11050380c0180c140030900480030001c13405074010b145402000c1c010b44030104445071014024140a00440d4001c0d400c0c100010603901c00042d100c0c031029002401400c900003180140b040412020740b0980310340d501c0b10244401358404002c402d0060380720b40f000180d43d40c0707541090b50856010320b5000e0200060414244139503110340c40c0c11204d0a81001e200b650030300fa240300140c0580b0507842c1c41c54000501048002807180c898103818030f42c2100f540c140200400030001203890714541d903509180c3d030120700d000b40300400a105e20107c01c0c41c400b510102111200441c1240186852100203900b41e460340d0041e0050701b8140300c001d42204490429509020451030b01a4650a040c014800a80b0700240043c5000ca15600f1040041094003001c2200d03000906000c10341401c1401604081a44156011040d090400c1186d40070b020507568000c0042c115400c0003002e0b84000304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 106514820 1250 106513570 106513577
    0x6151107050618041e020712080603010b010507150b090903120606040e0f04030507060212010915030c060f0c0206160b070903020a0b07110301060e10050411030a021c050403050306010915140a 84
    0x6180400104e0b0341b00920005029140390f090003205110003c0203424001c261502903410011036400c00c6c0d80140c00d5038070b00c036407028441b1180058a1801e4000301601651540e00200c50030038000744000100c018020b4035450701c142c0f0903030354509051103000d110358032403c80d03007401c05070018038018400040950000e12a1922910303295091321042d0a80c0c00601d030485843c2c2e61000100480d00091045684000003540c0c90a903040c5141c48400c40b00c00544605814440c010001c820a24820b0301c2240c00158000c0665480b04000122282549054101241d1503844100807504d040d01414400d011280d0061501d030015041c4420480309402c428001c9a84009064624006540c2801560301404000c903414840d0b1800c040e00c028005d910350f025034011868101500c0c3c040701064101d0340d024200354400b5980e0381c42c00f80f006002d005006a560105843c0409100805500c200114002e0400366540044540c85520078402c0f800b400d916603012450f00c0070181301c801200d4026040139580d0b4107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 106516070 1250 106514820 106514861
    0x3130f0305130605040f080105060d0303050603150c0c0c03030313060902040b0904050a02010e0607030539060108060c0a022505030709050f070314070509040615110705061804 77
    0x54842c9031082840e00030801040c808981031101407a5071989030001d2201d40d009006904003034021403400078180030042c04242d100d800040031500c003004510440c2c1c04450692419240c0305038901020f80041e8201f110038000d4983c1c99001c0d01d0004103913030246e100c60700241c0300d10710340c0e5440f6001091000d034106c0e0810380320561078a01c0d5641d4074615210714094805400750300b24510004191451016840c0e00c98078050120001183c3c1c001d05446105d041800e04851155494603619035101c08407120402c040703400c6c581c0c84c4034100040765680c100c441c500100d031120b48444254800358000d0f003040400503030148000400c0c3c415458004100c5043c1070080e60211a00ca0001c41c1c103021040d0406820142c44000344841d01c04c0a01801b030f40480d140c034007003180910b0205d00031045880500320b4400c0046c0892440c1440c0d940b03a2001000b02070804010f82c0e281006070020300260708035030350030307105024000000609013400e0007100c0c20041c80b440184100b04820b01080700400d08400403500308071104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 106517320 1250 106516070 106516087
    0x4020a15021c0f02061006050702040203040c030203060910140103020108161e0f091703040e04051f14071701051003060e04051e0d020703060203040f12111203130f0305 74
    0xb0490003001c0216503102245003840c01e0010385408006041c049129060030000c00004e030740001a035041341c0d812500580d80792375509080145c003400340c04c061341c180a05814003e80c0d1100042e14103142c110807000b071014402c040520260300809120113804a0710b040000742c091a140400d10385601c3c0c0e41e0034080001c031145280f035886002c0307442d5110007081c06042d8024460ba0031608040c020614021702520218a11101d10303100d0040d40b1400441c03251440118003041400d2282c40b06821012020720419880114200040e28000408401d0010684045900a40b04000c400300c0c002d600780000c80341e80d180c0300a1219100d030f4010201c1c10076030f80ba840400d2054051050500487c083d1f0010f010090b8410b070340101d014040780801c0c0303d0350b10500035103580b15004600d0b82c00301c81e00940300617180c5ea11070410407901ca81c802002400b0000303090003035034100c0d001704408207001e08500403586850000034a0811030311066480c0c51440000c00d003964006010004100c1150b803103850005d003008000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 106518570 1250 106517320 106517353
    0x90601050c19060246170f041103010b010c0210020a0f08040509100305071202151306080a061406030622050702120403030813140312040507060804020a1502 69
    0x100c000710b40b8a03400103025800300104500d21a02c20070700014025000d01142848804405e6200e0b00c01118040c0614900e81c0318020296a082e07003900280c1c034010381c5804451001d0502c811542181c1020741603180d94042e090501c51301410040c1a154402c40403807035000c0180c4141810804002c500c00d086040c40000e40e41c05030311310064851103055071a942400101b001a44000345480c81c2c414000030200041200050954125201c0d0000c0d41e052410f40e0001c0f5000d0380c6400d080481403000015040703e5071140e100c10740220390840c1ea17000102d480f0210700c1e00c10350b180c6200d00201c0800104061609161600045401410040c5a8007000c2c1d030959490036494040b40705034114691310010840b1070750701404844070603014000c1091901d825a50b0141c08150007420790102590004c481000708020345504101d45e001e06070442c1d4840c80300c070a01c00a010801c46044030756000f06480080e44501a55059006650041c81a00c10600340748a9031002082d0044243c21842115030340b0010285 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 106519820 1250 106518570 106518613
    0x503030a030501080705060a0503010306020f040f0e1b16200307030308040b0f160503040f060204080307020406080a0b1f12030804060c0212090105090d02040c0503040213060302090601050c 83
    0x289034401103070541c5010009418005c0d43d41c0400e02500b01000340022803644441224156a40050300588591011500c06038074015900310310020f60b07002801090b00b001c0d1000541c413814041071900c0451090360150101c9005a100d001130005410348a80c0004001207120341001da84a49080321010441c3d001914084181e4000e402140b80101848240a10380c80d0f5941d04c200b000d0584030b91400c2400c06c6801848561807850100322000c004034040100c680f2400000540040065444940354486162070ba032002c8000ca00c154901130300000c03078034008202800403a4000503c840ca66031410303414540d40f43c00440b600b024940180022541729400140c0f024024000d075201c408601d454a008806c40d210341d0f810304259400324609005240700202102e65022007843c3c00e0782c980d0342c030001059800c07008a0000303501c5400c0454a005555010003d9841180211b40c81c9021160400c0c8000464040d03000c065045444440080c4055008000419082e440c3c0001c6803003064407401d00c00350307182c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 106521070 1250 106519820 106519837
    0x90f020d050f01060f11070501031802030601030506070207050f0f0d020a1715060103050f01030813030c17010b010c05030306040911030a030e01030506011d040c0e030304061101060f050d110604050303 88
    0x50300c2d07005018003030b8003c0e0f180b0546030080c1003011508103019650f641d20305240c461a41095100c00c07809105100a0707014228241d4058101c8a15584034a825501d0744130890b00600107125012000925140c880710700c082611001c0c0042201061280500c401c203992218241d03005403842e040010840c10380007454030908061000740a41828074050500721504c060030042c10107050038180f000c0c100f504d8100e075044940c06441c030756440120b84481440c10341650f0000d03100c0150318034002442d8040040303c3c0c0c8000d0455008000d00340321200151040c200328000504141d1003400041c501e030400e40d004a032254051f004000600c80c0c100b0000789422030324442200042e4030804d0060803940c0502a068220000b401d0108000c50380500610300784001c000c049101e151120310700d485441c01039900c40c00c0610b018060325911521200060710b00303d60307850103410341e40c80d290700080e000c0000400b030002d440006064006c4a07401e03444003e1014003941079281d0280c0d080200090b540e404000908920 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 106522320 1250 106521070 106521091
    0xc0f0302011b080405030a1d1009080d0513210804271806090804030b09070317040b0702010c0204060801061404390207030807060e01051f090f020d05 66
    0x20480b01d041d40a4502600d4525000d0048150a00001070000310503503114080d20702d000c501141440540e010060111039055400c2030580c8000381c07455901c240300c0420b0300d07403c100b1070707402c0745442800315a03c0c8102c80c00d00c40a12550041800403807407821751580d030304000c0040701001d0952070b02d400c80300380e216500821f030502c0c10400c404501a0006441080d107150782008201c000f00c9200103507810720303819400034007281d59072000d803042000700415a0055074102540c4c1ca40751a003094025943d42882c08103440c507000508051061810010455040e00c04200005003040015401500c814540e080e0899100c1d0b12a0008500c4400c2441902c004005010914500003164014030003212900d046218210415000d040c00e200100c410700d099203030300301102e0413040e107a40e081281029145d0700000e06001e80010803200380026a00812031306287e440003048551910141030600c16a40100d00c0d804018030a0200005406603201c40c1a0600f40e00015140c820380c0031801c407c80310200c4446514 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 106523570 1250 106522320 106522331
    0xc220f06080607030e0601140a030f050d021c0c0305030604020706051614090618030f010504080901090e040c03080a051b03070c05031506040504020406090c020f0c0d030801030b06010c0f030201 85
    0x418100300714058203d03049040c100305034481c088a1545400c0e050040010718407404216a45580703840170317000f004581100682100d8159440e00c180c4590380f5910010052096062a03a40da90000868000e5403449031a8441c10900942d0190b51a4000810181d88503a00f4400040441e800340207a42c400d40b0f600c074034441001d1700c1c50000b81400c035403600e40300e41c001002d000c8070203240c95400846003003090303900c5900851140700000a1420200d00040701c41c0c0e5091000340009c12821001904030b07404240c0b22460300c1500e4040840100a0854000c2c194014403030702040455070170001003c04c9007452411501d45890203a98203002614004158000d070300001e4900700b4042c2c40c008000107400e04a001e01015000c3c1c42440d02d60840207490144503d80e204041000c40d40c460f07002000401064006202c00090040060b4444595102c0e010450060b00d010210600d8003c8010410f81d905444006840e4211386403c030450384002e140d5414040343d050101d0200710350000c4022454480d43c0041071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 106524820 1250 106523570 106523579
    0x90609020307080d091202120f0109020f0409051c02010609060b070506010906062a0f08091003020313030e0a0518071106100618050618031207050c220f06 68
    0x1410a40e0b81c0100c020360490841c0304080396000303031704070119444203070207124030a11400018031010a5014448440c0b00d6a8840e111603101034010090442c02210340d0006010090280010303140007010042550f00810403650b10190712400c0700c400358500d4400043d0490300c8002c0342d0201c80700f580040000d418086450720801504014860151105e100248400d9140030381c003078044075200707100d18141981c4030805c100181c0d06620581801d5004140d25004040d9410305105079031280f881e0398002c0c5d42c030f00e2415a900303019008583c098165101c45600000c034540302240c1c02984c0556841d4002201c0100189030356410b41c50702905080012210210b00304480d0280114482002500306600300c0c10400c1200e81074944208114ac0e520b003018640701440308800300460100b43c010903842070700132540c40401540303190144080c0380250229494005102401e1500e03000c1d0100c0201107a00c44030311050b00c0e00f07252240c00c140003c00c504600d5a000c0c034042c680d003511041090500100e580c1c072001c12 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 106526070 1250 106524820 106524823
    0x902030f0c03011d070b0714011d0120180301020d06380417030c0d021b0307030c0512240f060108040c060f0e06070b0115090b09011b060906090203 65
    0x1c0d5501100031213040c039501c1e200005440300d0003842066580300010450038244100c010300d600c3c0b040e904030020480c4003e0221283c0f9000008440c00910751321f07105a80d40e0003c2c0c000794841c07100d00d6012809003090b0300c03090443c408441d00220745416540034031500107810418003d11000c1d02d6007212034030b03403034a039061b103003440700d050b0108103052a000821669440c52880200e5040e12501000e0b2600f030b00e00850f1a518503c64540c041c0e6440c815001c540c030b040303a4007181e418045c0761310201e4966885801001c140c1c5e500c01d81e010280c140d61801a0400891511300c80d40c1d00100122030540303c2c40c2c144600c00103030102d024814400100070742400c206959214070002c0c0e9004009007065030141c10141c0710f8520b4044103000b03002c280400441e5102145014000781014860010095076440c00d2030301c0d00c1281000c5c2849280b841c0d07a01c0745030308207581c1d01400c1004e0544030b1210f881414410010011074501944400000040040718401e2000c110940208a0118002d60f0089074450301b610606 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 106527320 1250 106526070 106526081
    0xc010f0510210809120c0102160501021e0c030a0b0f0a0216030e030c0d140606091e0a0f0e160501111b030c03030a0f030b0307120f03030902030f0c0301 67
    0xc4000d2541c001040c08940040307015101e41c00c01180c100c2c801c2208a151211961041c00343c140e40c8010070040011031140c00051100c9102801e0782610005410071040311f0100c1c1060152901503080700181c4082c0c0403002401006d58066034080741c0b140f2101c0d03000700c0d00740043d40106541641c1000c041007058155400a145c0004901008600e850f13076011171000803074001c2400508102c445040007440d507600300702012a0990007800d100c0e064140f45029141c482c0381080100031070042d10001402e41c500810740f544141e500c0110861240c00c4848080f001d030030010800d06c0556903c041e2010014060311416110b010060300608100404018004514000b80e100d14100104200552140c01700850301d07004408801235080301c01449540000c1c14401030059154140c8004643c00014a511140c0916144065241042001040d10505845407903074010086042d24448145001030f04080f030301454140a40340c0003039a58542d90000e414110341c0000c051080c4d20803100000140703000c7c07051 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 106528570 1250 106527320 106527331
    0xd090b0301030c030201111e03070212010c02030415030222170601050a12051207030e01080c0307050315281e0f0302010e060c03030106030606080108061e0a0b060c010f05 75
    0x2000d04641c0b440c1d0302d4201d42020350000a040000e05110301032a030710104042402050510714000107400c0ca0600148c1c3d903041494280d00c00c941c905841c0c0c4041c0c0d0103200312009800310380c0c050340c034007400c04880941d611191010f2804043c1e00700100c0922015900855602c1400042c00154851078010044c011070b01c030b00100512500320000400c071a07554001654101d44405249074402811810b00908014210780341140c0c2020000b0010109548019094000c0100b40c9811005888645044005000c12030b00800862801c1020407500201054031914943c0000c0202a0a2040d0300c003107050702c114012402c00001c0c0300d0327206024421080c94646926400d50190320314040c80d01031100110560344c80041c1c10f00400e003540383e80c0d503181c40c07003160402310882c0101c0703541c1d5079074000083c0140303a58442c050000b000000082800c440205415004c0d420b201490101d1110201001da012800070b0a4520320507600c4503400410348840f0060701d40400785c0320000503016041d00140080c1c4000604 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 106529820 1250 106528570 106528589
    0x703060e06061f030902041802040507050307080403081003050a030c140a03170a06030f0c050916052a01090b090714010206010e060109120b06040b010527150307020d09 74
    0x1040b110340c4401035044248211103c442070554404603003600104003858010390000e04107820b14441419030710300c1c0019180b0a40e410040740d42e90b2170382102c80f80025030b102c500003034515002c500460f210350581034009901140444200e981d9a42e20b0b860000c0c410b100b1004140910744040c240003401c0e01d0380c21400c06500c0034201030071560390020411180c5000350562880383d80085070000301c40c0d51001005d03503401034800086006501b40580c03030a0040c4030306441442c501f00094521040580c0b07800303142203162692400c010f0902c103401a14811024400d1540f41c04010054407480240203912010703024130f4207480710f4205880c4d01402c041890708550120b2940350032206259a00040103411202d40c889010b040391506c1c80102c030480800d51000300c10050300c02c01d05083c080310401003405190116010000310700c6d19001950140035403001203611a42c00c0100603003904c0ea0240c40c4c515100001d014102c1c4000c8039400302260b800c182e071400010390000d031301d1003507080d0080080c00160007001c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 106531070 1250 106529820 106529833
    0x30801090b06090904060b04051311030309060301050f03010906020d02040302011707020d050d0902030a140607080609060103091704030c030b071d01120e120a031103040b0c0a17090703060e 83
    0x841c259204801000c1d000e014a04c0000341030280036840803800c4040103009003d582841000980903608c0810103170f801c0401203c240003107280020446a040c24090031440c2140c0c0780c6030400520308200680c840d0035540f10161000040e100d48010811180c0e04080162164110700006282510b070003110b040200348e40e41481511f42d00050b403090546c1d03081c40e003036903102c0d860121900a00341401000350188100340060040140e40801d844e00428100211600cac0e035942c100032110380c4400e881d40b07500701c2040c4010170110751283d00035145090003000400180c01051400700350300d51156100703171a00002a1024401c00000118442d040000d6203840071019030100c10501c0c040d405c0100c402d0500865031451150300e400ea42103a10b4000b80c40041d29202d401030911080c159028400303802c00039203024100103000c15010262405181c219002c1c10444e51484111042e90340038850860511401c0084c44044440da040c00340e110f2455540a015050b25628003c01a5041e104501c01d40c0d81011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 106532320 1250 106531070 106531091
    0x9010b0111032a0d02010c0f020309180615030408130602030a082802070b0907080708031c0204050904080c0c060c0a02150408070f030c080705090a02070501062103080109 75
    0x41030711500144956200955642c031041d4800150f2061400c1d0458010001050041038040d0305c5107650300447e4440401c1c441d0a904200e890344111741c0311640c420783c825041a0404110500b1a03481880503041d01d65250103490381001c560421502228480c1001510000c40c010414040000302060300056080c1014650090a07000b0000d040c2915044a004050740ea401140042103014401850455a8201d617050001800750200d8490616101d040c60000d103200340001c0740c500312801c200c080c50520000b0030603a18407441642c040300f103954003444040340640d104111107018901c1115080d580b00018a00349083c4103c0d0410248a020203002248440c540410350391150759044809088400180018134600d00403a0050b04261042403004200e800b40303d4000c000343c0b405407000a1070141e5603e5160740d90603141c0142c3e608040c7e40e8002c10107541d4160054550180318000100740c03207841e00c5800000030303504210703248004150102c0c40300341900034907402d024000c003180c244881001c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 106533570 1250 106532320 106532323
    0x5060f071a010317030a02070b04031205012405030a02090628084c06020c0303030408040b0c120d02220807060f090305120301030b0109050702060a09061b050309010b0111 75
    0xd910141384580080050420700c00382e411103078040e44c00900c050807030405040007402754a00e015022842d902c0d01001040c0510041c4420500d000355941018101000700c40840d929040540903050031a000e00c40c0c0e1199640f454090310b010f500160003140e8504101120b00402080c1500710400d0082001c2407141409542070244015a11003101720031000c00844000d24002c6441200c02072806080307a400c03103088800d0010011100b40781c1c01c41d00005058010180c0740d100a80c0c004001c01c004200800031602c0d144042c10504c1e404c0c00a035400c1028803520700c4120342c018048014826800610703880c2d0500c0c05100c00c032a03006003045602d5500e0824405a031344201d28015401407140030b0380c4442c4503910401e51000690f071f10000752117203a42c0d500e1807860190401c2c001210038641c0ca100100300090035120b12071283c4065402441c40380c40e465100802810080400e407035083d156000328200501040c44421a61056950b20b640c0c1d2400c08203032421101180c111504103c180608010314090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 106534820 1250 106533570 106533593
    0x140f040506070317090601060e030c030604110307080102030a061502190b0a09020a08010b0f0603090613141609060611030d0e0721150b0102030d050c0405060f071a0103 74
    0x1564069030741d40040c00e00761030101313081e80045281100c41003004001c60300800c0b024100c4005072500441900a6001c042e25007181c001100d41503400100050302140b000c1c0c51400d02c0c00000342c2034403020b41e2503450860980e413040b5211064642c444c042080100d010700b0760b410000c0ca6510240c581d10407a0400c0000e40503040c40003803e8a00042e01240703a5601c0c603801504481d074001d10100da0341e5952a8502d01810341303013050501c125000c0210640504000c1d040300c5c4103000140c0a00201e60301d4292190300441003020503500e045000c8010640c502c41000b185103d5810030501071111454882100d00b030301e2040d00448200400e181001d1001903000080e1240c0f00c0303081c2c0c000710b914080761240b2443e10043d9441824800084224280702079240c4880781c415900501c0d00f4024024084890002d554840848900680c0700b0058003080030200e5104c0d5401144403880540ba140e52500003e440b03030002c0f26010559100017403000108559124108000e02d00c803c8d842140d589917440c0c1c1000d100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 106536070 1250 106534820 106534829
    0xc0c03070602040f0608071d04020405030102070b010513060812030405100e060603061b04180b060f0307090503010c1215050a0f18050106020309012102030408030108010507030e0d0509030c150a140f04 88
    0xc00c01c500c0c1c8c22003680c86405980c00703400c0c09002152913201c1410a15807140b828030841e030290810f103104d4ac814041c41c3c0a445c00f030b9100c4000410f29190002c805580c0c1c0e80c0010410785c0c49000d10000b0111503095802801e0008000c50020505420311b00c0c1094144400a000718a00114081e603007072220341c101c070a40f07007159240c0300b02c5200c03035043e410884054080c007595541e005400003070b0f42c049000100003070350240003513645003858982c5810a1608071a1040c05000c085200554045140f402c95004028000c0309064041a1184c2d1103020480c1501d05400c20200100d1440c81406002c40c0d052000d0102e1200101c1403109526042e400f94803449601c0b4024100074904050b01f448440c0941c0003130346407009283c01c540d00d14240c1460000e6400c280074203e215420080401d038158400c1c0150854844043c02800760480c0621081e078007584600c0ea0140c05001e00500311446580da010b500000480c02c00110baa5050100001007480c0d6603460754104007032051212102c4000c02e403003170343c1c10749 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 106537320 1250 106536070 106536107
    0x8030406020c06150f010e011803050622020f040207020607020301050a050106110a0b060607020a0803130302180f150307090504050a030810030b0103030c170a020a0201030b06120c030c0c03070602040f060807 91
    0x1d284c642e0048271103d98800c0e105021800c0e6180000c100000051014400d07094824901101c0001c040708100e05148404042d41c4007482d01d40001061030a40d0040c50028030080c2034500c0c0c040d6650200342910411110b0070340041d076500c010070000303401c560030b00e60000c0d400010b0520441150b4174105440070291a86018030000f1968504540f28550860b02500c089021a034880c5040c3c0d244420841490204070300400e4540c803040c00310105266501c3c0280244c003d612003907a64104038040c8920f143c86c15652512540c41d001546201c0c03403060710b0003035001d00090002c62006080241c80d84002500700c4d81c400d064a1820408610010031260541c2e51510341000c002441c0e051620079241c6d030341a042e0300c5040029040074025000500d40201d503100307803420301c01c8607900d4081000c64042c94000e9107841c40300c540003694903a901c5004540c442849906a401c100005482c1450742d00041c00031590306500080c28800306040d0b225100084c811494250220315160348000c10a83c1c1024002c81c09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 106538570 1250 106537320 106537337
    0x70b0402060702062d1206040921030906060806060303270907050d060f050f12030d050106090906050301110f0c070b0c010c03050a0c020a15060308030406020c06150f01 74
    0x11541c0d407038100c8a034160001e0010781c5130340860460040886070a82d40500060b07428500456030f000e0030083e500b1004042803000620350b0340c2414003002d0112401c007104c000d0074a502c040c4001c8102c08040360000502e81c1c001464045500d014011220290007210b1154800b6003002601e039400030403181e000344500824880c900070f8100980c100c110300d1604540c08807120003000100303580000a0090b08402a4090203403503030700c802c90075000710a402040e40020310440e123160107040c500880035000100d2400c403443c00d480c041091040302c50a8100e000000c4204100304a101d00382c0c0504400303480d00314020845403404909944807480b03040003241d004000414003444541062100303c00170460010001c0e950340c0c1f1f503488280207011070300003c4082403420011901c0012244114040c01d00315800a00840304103803110100b50b1002c03201c0005190700c64001200141c115030195018034402c00c0050380314003c01c01c0c118180240100300c0101d8034010311603a90f0581d900d1040281480081c24071991 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 106539820 1250 106538570 106538573
    0x40303050a05070602040e0402130504050613142e050c04091109040c030f1a18042321070b0c131a0a030c0203040b1e040503010e0a050c010c08070b04 66
    0x1250700503c2c801501c02d41c4041000a1603594030040300e8811407003181c280c0c00c40d605104c040d404441e41518094281c0c0e1002000030b906821b800500c907601e901640001800c941c50343c004500c0c1c16200b0a21036244106050041c41025501e0f160241c2100340342d90911542c90134a5480206010703d2261405054889247c03094080c1210119040700303602070010700950380c024401501034085a1600200c151420000701c03582195a2001b104c0c1480050000c8051b00c49070104200d640d40c05803040e20058145420030710000f00d00344080460a810a015140030039000302c1034001d01040e800b400041c18070400a080000d07041c0c882d11a0311541080c9095120345c031819000c03040a52030f070080d0315203090200b02c103416510740401400300003c2c26507051242c8440c1106c22a12809240314605078004284000001d1111012106600110901403542010f0303a8200003401d4424031a402c06180c0c00160243d0300b400828084019411005c1c00c00004070b5185079904012445241e0000c2d1084844001150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 106541070 1250 106539820 106539827
    0x90a1101050313050d030501030b061e0622080f1203010e0601030c020c130b0306010b040614070f1a0f09070f1703130b04060305130b010e15150a0201050c090303040303050a 76
    0x545203078200f0216101c805e1310000160091800380002d58ac200e4880303001403028900b03d11011200000701011003540d20510341840b2664000141c007a84141c6803101d100d40079900d45c0156001882e030003004203103242401c181d5904203600221480040d81c1d0800042c8098242d138101c05401020a20f80040c0b881171040c402c81c107005640039038691040072070495807880c20760703600100026401141650480d0740d8480c811901ea10540c85232801041d00a54508040c10504020340000c2d07000d80340d0301101c1d000c10781d01c1000c040315882d41a101c1088500030700803010702e092242c980c82440c0c10010100907091045809415402d441884600c1c03000d41c0c004507060505100390b03540910056000c1c10101c0c1c442d510800607030014054600000c0c80c100000701e8080f03020000707400003500310700388189a0342890259880a44024280c507004106041e4603409529102400ba204024400919449070b0341608001d003541d50180400404580a0001e09250307030b0044120f0702129494145250703100c0c03241d841038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 106542320 1250 106541070 106541101
    0x20918010f020406090f050a0602120310050607120e01080c09190902040605070311010605060d050717090303060102070806010f14030a050304031b09020c0a060203070e031006030209090a11010503 86
    0x120000d0003c0340c00100543c00c44641416600300c125045c50b110303114000e205c0510a9449088016070204081c898a028210011a0000b101c5448103030040d40b50404200240d1080780c0031105410420750480401741c1c810310130358141ca000d00c0d284c5a907050082200080b4058600a540718962646a512008516208010051040b105e0a40d00c496607a00003605036001440d00f9004900307590074249558206100300800d031003005101c181080e00d800c002d42c00038a40104104288401c5041034407113084641c040e248607078803c00c0190f41c1d0b40742a100090501d541a44005d11030b910440052120010f4002078009403400c4501c410149108035000070301e0314908000141c0a40800100401403000301709801405031b0964840a180303555400003c1c040b44240c112290040d00942218000039076250010f40d000007181c80c1003080600354100007800d10040002811000f9640e1b0010000c500300303010407946c0480d58401402c1081c1098442c094400740a4509604014001002507421000d8840d90f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 106543570 1250 106542320 106542341
    0x604022d150c0106060f02060c0915030a0b0a06090e130215040807030b0114011b0201180801020c01050703020708071e12020c0a050f010c0f1707031d09010302091801 73
    0x16450344004040703418103a0b5100b8040c10807194205507000c40d601e4000d0381380c03488641c03c944c020f040035942c1080386207083d0400f10050764028040100b448a8000c1c15018501501c400207000800c0f014940030411034105950080051121443c000c00500c103224015a50001c44203e40c407a1030713001c61002800900300c192450391205ea0200d03010503641c0f8001000c4058034441c100012442c0d8a81800860112050500c02d00150f041801d1601e000760411242107041d00c1030515640d09114000c1c50082501c1c0ca0700022116036011440c61040d810034020704d41c0060283c1421807a0210689565009104240000d0f00015071502e90714040070001e60646100e5410640000a84143d0b64009444200f6400101d05c02c11245401040c246002d14682101c403105868030a079103940e0340d40f01307900c0c0f40680c5400d44000c1da0900294200340441ea004101031f51203035560015240c0c0010440c0844421058840e00504818005000507141c020030b9030303000516041070b103168180c03507070b2418050400c0e400d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 106544820 1250 106543570 106543579
    0xc0f112410030b13030905150f070c08100902010306090612080705070b12060103050601020708280203070b03061513030605280c090b0c0615031009081206030604022d 73
    0x101300340c8440700112940b030a40300740d4074040040e99400410a841c6c0c0808002c4034858020031107012180810750050070b40ca0721410b403202415648403030050410300548030325030f11380c2d0b110081003045681c10320805000d8560150204489424160906420418810003c1c0080c100007400720610030100712210003007c00c58074040d65120000901c1c3e40000d02078031407901003828030021038200e6001103607035002e40c1c071500014035140700001d00201d0000c801ca0380001030883c0107495100503031024040031024040102095507030b030412400b40204174039400300010740e09205022410701251409003200889810946c04941c94aa0100001c0b60070080700002942100c002d24000e0703940003942129410700420780300d0102e60340d40d441c405069441000d00310201c40d000400001c03440d080300304501d02a000050111a407851212902c4401c480d0a100c1c00d540c03180d008201d00391010f40d09200302e94441c0342a005000d090070310f0b43c042054458040c184030408098102814080203181c086840040002003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 106546070 1250 106544820 106544843
    0x15050c0d09091a0f01080a0603020306010e070206090622020f09090c09010902131214060a02031506070f020906060f2106040b031b01020a060c0f11241003 68
    0x40151401c052845079400150030300440c1c07070034586840c162200212018141c9000e4a11340d000440b494400188900c80040c2e03150350110242e24100702e454040d04c1e0201040206041c1030001a240940051110f003641e8010b1080048804001600920b500342004402c0031840584c40011501900d13200c00c180c0200d100c85c2080030070720000444800800b0180c46041881e41c1ba02c005509a104545005001d880c1010007048140910b0b09622500c0d03015525405030b8030b046030340c0340341840070aa410f589160f8000c414401c0800c0c8010517100350040444145107001a80c0d07452000c05508468064455400e00e0001481900c2d160119002e502d42504c0f955541d9840904618240100e13103140c1589140c003200143d000d08240c800c1003a0f0190040040034100007070303640341d6541c00046003d036045004001201c80003400d00c0c0655041e07201c1c1d988400401c8021044010845000329040c181194404010500c8159251840411040384102a5003450340e824488581080310390f07000038222521032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 106547320 1250 106546070 106546093
    0x1202031504180209070f0c0b060a050402070804090c0504060f111f020a0215010f03140c030a0606030203060f0f0a020c010608100605190e06010f170c1c020f030115050c 74
    0x1880503001d00c5200300e81c0413540e40c8500d60102c4a00d1015600c04e400704410035065404540d042c0400d69114070000c000300030340c545541c0440d069030400e01084030140d2001c14203029600d110b009259600145207000760800d840c040d001000201410031010a00c000310300c00007503207101400440351855290b401c1a09800c1c0c202d034517000070f500101f002c600600404881c0f10b10541c00e080114100c810884211342802d007592514a0f60401441d0444064802d410290724a07071010f205d80136605025031400030f0b10303a1450043c03505142c0c0041c50380070810001404c21070700d00507215445411054200c00162100c001701c0f40e6a004000c940c000c0070b82842488807c134551040b0390808400d580303003903c4151002d01c0d010800426122903010741152545d1940000780307603511503400100c101083d4a0700100c0e8041c882c40002c0e000744165000a008500001c110455103c0c43c056410b01e0505850300710f107403400c4402c1218843c001800f0711080564000d1841002a104209540b13040e66040d0694900c40c0c01e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 106548570 1250 106547320 106547351
    0x1e070f02010b010e06180d0f0c0e010b0a0210050601020f0307060c020f0a200a05040c030f1116260a030207020a05060a211512021309031202031504 65
    0x48015000560034104242180e5100303c68100f01584064400c5060401c4642410081071900c81a50b4002139004408000305418205030005c0307a005103805005141002115940010160020010442c04210101d811039001800c0301d5902d180d081d00050549132100102e0620f000c2c07080d201018400442c0c0750041c4400c50b0f1020341c4012240e002c0314000e03011017090350340300c085240300170307141c100c09040034402003042c48403d07031107a04003c012030602500c03400098101d4007500b1484001a640302c9120072040444e110340481d4040034020507041002111414415087c0190001c1069110303442403080607021042c0780c0e0002041d10b040e580c032140c0d40a8010000d400501060744103070040d040c00500380c03d0200c1140d01d10703029070790b80301e180100407a0003903509444001080071099540b6001d803822068a5007800c0035141c1032075560b020030003500401902032008000544000e140c40031910000350003180700c0151442c00b040140e22680c50a180b194413560707803a00c41d40c000b4185921135200860 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 106549820 1250 106548570 106548587
    0x709020c030909070c050a08030c0d0e0d0e01080c09130b090708040c05010f050f03060d06020d090311010b03061605090a06050a0f1103040611010906020f07021809060606031e07 78
    0x400383c030002d100f03a54034641100d8803d4104c030040e010381c1040b003240c40859900401075902920b400e05d510703e05003a03003a408040350ba42007130740722054200b460140b4505900040c0341d50849070910705804282810190500c2ca84200b50b40d03076200e003084c85511030041d01030b0703000742c801010010101905458100b4010785a107800701d60464203083c0150010071698012000644442c0c0a6501c0504107140c01702d5201069201404d200e034401550000000020003c0c00104616804070b00301103240d4403140340107410050350380705490103a41090003402003601c00042065001ca80740d190001d200409480640c0c041c800d204e40c09410003904400460a01d42000081c5012030042d03403000b2503030b00d81c0d5008444856840d54068503a8108010800826100c0d01c203480c250b100c0c400000421102ca03540d01c008070713031141d0b0b1100a42000032840d00c0135460010110b5403c0c01228810881520740700d155641c903400d004122500c55140400416594002c025011449541d0311107d407a07503003042107010745041c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 106551070 1250 106549820 106549837
    0x6050907081c111606111002041404050408040e010806190c020a080d0f0e0c1207080325050a06050f100e010302040c050c1c0233090709020c03 63
    0x8a140000500e8800c001010790840c4082d4650070703510b10701003030111128404249544180d205043c1451031031202104808000c24160b00c038003c18070442c6000905007001c0001100c280e83c4103100c20080da01c10303080c0118100104440000303c554452a00410502407034200c1d50200541030000b00b4500d00c0011141d02408181907090000e41040170581b0076510800800340c0140c1000004e840010f5500b8064083c0c0808840b0101da214103559141c000c5500300402c500b442c1c2c4c41410008a642030031240760118600d5036003d49105070804e44465505d21508119144400121201e0320743c8440d800e14503004a5400740580741009014101180508001c0c4c424890700800c02d00425006403a01c000e0790704483c02d0580c5111140c0ca19020040146800c008800522004200900d090101480000e03900403262144088030301c11014000d2410000c13000f0242d984c062003030792109200e02c1c0400101004000f440900c0644d031344010b228200702003907100c2c000041c004240d180b069000803000d4034605 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 106552320 1250 106551070 106551073
    0x3020405010506030402130b01020f0115050f0901080712020d0807030309020a0b1306030b03030903010c110f010c05040b07020a09050a02071e032f06070c0b24010c05070b07060509 79
    0x742d0300e070400c102082c4400d6500a500002044050f00c03504481c0c1c100400c01441401501e040b40c4c404000c413400c0d1088132620003c50300384440180084e02c0c2c400c1c200002d43e139051300d0410b82d139814648134940d65101d0340103442d03030394204e041603100319a01d01c005001e00301c2d40038541c0340d00d400c05881e000d4003602189500b28410300c004c0d94041200001401914824040b2403606005280740c442e0070b070000c1401c1e2400d150540810050070b00152803d0040403044549980d40500e0750110000c03043c02c2c4860001d540c0803690400d200340c1780c51980401601e054030208520142e6034801c61002a00840c510b81c4180300303031070409003000700711029907020300091703030042202c1c003a058a030200000205845080041c04030791130540440e0100c034004007400c2c000e080206880b440b2641034050601e4008101e0742c040014881445400c200000f80c40d11640003c4503c1c62501c0c41d440e01d80305280c0000016040b141049503d0302d4160901204002010040c145c1440e9941e9541807030501c0b80203400f00701c800c02c415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 106553570 1250 106552320 106552331
    0xc0a090519200a2003030402120303010302030c060d2d0b0102010912050c070305010207150b100f0302030c0d0501230312032d07030c090b0c03030a0e0307050a0804030204 75
    0x314107040c0035814041840c114100c0070407020400310200e50300000c110400f04003049440707400c1c010a10354426145000d2030000c54480c5000d104202c038042070021510841e42080c00100010b843c0001c1186034060122101501d4210380e0306200300818440014801a458190701d19019410100404810954060f030900c502c444590069099503441c1d231004050000304824100307164072070700180c0040c03010303541a61010b1b0355075160380c0e013644c01844c003d881e9a01385051010809100c1c0c40b42d40040c901c1a143c582c03d4000c030b0355010307207041d03d0004420117054002000a210006900895402d5582d40300e04224950b1074003c039201d1421014030070015002c8685071200304d03240028000707003640c18040609240d07986509910f642002c0f044148402c94126001e52542d5804560203184508000c2c3d0300000e45610340640200512526886506e1300e6804124190302c03003001008036607204c0c00c401000701c0c502c0c800c00451891031240c91005006400b4030606802004035003001481240d000b15818080c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 106554820 1250 106553570 106553611
    0x40506090106060912051606020303010e16080f250c1209050901090b130903050702091006020d051308190311061303080601020703021302040320090402010804050c0a0905 75
    0x80b00e81c0307409454082181184208060180c0303180c101000d510400070780c2c40307100244180300404105074024502503000480148580108405c00179072003190400100070740a05020003901d003620141040810b055031200081c007008904080e00d0b156003408030b49505020420000502d0102c07030380011a07d010900310711030162440381008a040e03900050000425034644401500100103c00c98180c00080410b82001046040e200f022040c40c040c2c1ca8060b66107550b0300c1086000c020081c0081c0000307201c96001d1001d96400034160450301d090381070495540031415803031603100e40a540000140d01c5100740c0321500070015200220114425116002c0c18403401000c50740315801161110f0114582c2d600004c042803040d0a160313041941070064544041d00c80d0045404841c0040440c01d410350001000c108102000b00075040e401c09004100880c400d03140d00040d5001d0303010b80007a040000180203d07042c024248003280040d00300803c5810042d950f845a03d001e8041203461400d4a000f5050101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 106556070 1250 106554820 106554823
    0xd06150801020a0215060a0611070305030d0204030530130509010312080f0708070309060b1f090506120103060b1c03090e0c0307090b03100503030708070b01051e01030b060c010c0804050609 83
    0x5006d0b40d0020901c0d1459400d281d0101e641c2880b0001ca20003a200d10f18001012880502c02410158100c0f5409a919070550030024a07207103c401d40601c4020107180d800180310804655000c148540050a80e0768501c1480364a4284046401144d80030f10008000410040300d0142c607a021103650b2546015940d5944484c00700d80300451f00b1030040b50040c0d0000d2045031180c1d10291000f0b00c29880024864050004600f490603200403c007070300f003803070010501403c2e04980c041004080485200d1f150902d8640400100d038018800101016100e80c400d04107a41e8220b1200d031141d00e055494080340105040050200b01c0511400404080b0b00012600c407a0680d02100d10500d443d4034bc841d07466282100303083e1f0356800100002c503c21104c02000c2410341d41480200815402a103401c0d4582607181413854407840107a0243c0c3c45404142204486041d03248807004101c1024280025050445000310350740784035003e40c1003280d501c0c00310041ca40b640c20215107406a8090710803190b540c0d41702e15059 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 106557320 1250 106556070 106556113
    0x130204060b1602010f0302070b0411040e0c060f0a020c06161208070c12030e0304030303020309011a0109060513030f05030309010f02030c07020405040c1a1206030307110d06150801020a02 82
    0x18075030004688031010140d4041d030310b00c01005c1d40b14680145401e090b62645603051506640403110200e0009030070a031864903015800c4030420000c080d0464544910004d9902c2c0300f2a007420480042c04074a40e09824000c0c082542e44501c09081c1c2507644142c1039030f22101e454060307003c42d40458200d45802500b803054801510444c19512603004081c00da8440d103d1318410b000d210300825448208030384001a0900203030000794401d80380561a410702c028803c2c20b582420000b21982c80065422540f645e921550590899246041c0707140c0d0b40c0416a0b1031945d5031065040a0308a10100f00c0303000401000000035403041c20a5070080100c100b807031240340280d10007561a48640d0506002040151410764000e070b401500c1400703142130503075035450701030071407415200a8002e1560200c0c0001205580c03003041d96118a041300a549042c103181e455904448120441d140901c0d100e01d040000c004030b41e4850800ca0b6803804001d410142e1703500d6180d020f50f02c089059401401744a0b0440c1188240c2006c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 106558570 1250 106557320 106557337
    0xf0608040308010b03060d02040c020d02011b050306090406020d0c0504030303150b030a15050d0c0e0c0430061a0a0f0e04020609033903060708160302040905130204060b 74
    0x214942d99281c962903280580010b400303d039002e00c00502c440010313070300d920070001110402d4001e0000741c42400c0c0041d085a0070b48808000c1c030081d201e40a10a40d0303020302200d40c440030445a559040d00d032400d14000901451021440880c5800101054660400e01800c101c0744241d8061180310701020011030f03860454828200311a0050020422042c040c0d00490701c0c108014040e0110b282c3d84000240340e0031892082a144040c107000180003c0210b4030320030b40d03c1442030003c54540381c50041100342e201c2003803401840c00c851a0411929072900d5a00e0310349641e410000c1404140000391400c0c04424010528510522040d030f40010301c02c0140710110704441c28240181d110b039403a0740034010b499104a03992a4103004820740d0306192a10080103122020348101c00e00d15210754200107407030b1718035000d50a078400d84c0903c00300a052503100c03500c030764000c603020b02600e54081a01c0c029000b90285402c03840b052802d000402c0804200d1450800c41d07a402160284100b5a80b40c2509110f031140000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 106559820 1250 106558570 106558577
    0x10b090a2103050c0a051501030b0c0c0a03030c09050d0308010906080109020a0b0a0302250c09021c091b0305011a010c0c0905040c090f0506031204120b04050f0609070f06080403 78
    0xa0034000b09010300d0151810400d828241ca10134140c0b0765409090900003001d00c059a4003e800503c140481d2130304c1c4a501c298114a8030b40761000e001140ba03621001e400c0001c0c100343d2103040072494240300368403c2c401048044c03c84541c41c4443e00e00544500000d00a0980d010325003000000c11507014001c0311030060300a040202441c2c00c01c564500c0c90b51203418a0801d05070200002e003840f80710b00e495058120100e480c660a00080c42ca807100c90b56800e81c0c402c04d450381c014003641e019015801185104008041c00001d9400d07079a25065244000030501d403249845035420000c1403203019044034054158204000301e16108400c015582e104041102400004605900388a04072540d40100d0308940140454448160385010702ca095901443c10200203036200c0041c0301c2c075410204101c00741041f074094001d00b0a801c1c001840d6810200c600042c1c1040c1c9000c021805100c800d001a000b60565181550712a180c01540700c1c1e6241c000d48200380d4800c1c140d00e170000f40244515000d50007180e0568 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 106561070 1250 106559820 106559879
    0x601080610120f0e0303090a050d08150f010c0605162604030503130519121d0f060f040e180102040e0f0403110115090b0303041206091a010b090a 64
    0x2d01c1c5000400780c902c0d40400c96503a40382e502c4a031800400156118907551002005800514506a0304112100c103030700c5d041c04504070900020703140018107107070215000c3e203110000851040040b10884c441c2c05018010070300d4202801054081c0e0481076007034402d691989030300c02c0f1080c03e0115441000e0107051303413001035450214002034400e000942e0080e10f001504000040140c56403410260301c0704501c1c1140d40c9488298041042500643c102c50210b401d0080344030b001681802c0001031510701c01c1d84282e524540300340181c2d40d01d400341c0304e030242d0340d003802920307140c40308207000035900d090b140d07401007500003804c419080a050080b20f0603070741034590300c00c0c29403101102040200c1005d481102800064038100f8203511007403003003010785011500d058401f1842c1525a201b11242c1e00700c3c40c9d010342c0042009011000b06840b00328184d507401034001800e07409605000c042001d2141014041100d104000a1850110390103018444403c444d013400c03883d500c0000d01f40032402ca4816450501c40c60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 106562320 1250 106561070 106561097
    0x100804020303071217010815010b090307050105160804030b0105091308090405040201050f1c05160203030c030403051603050405011b050c01080a0221010f0906061d0402070602030106080601080610 86
    0xd1003486a01300050400d42810007820211075140c50782604000c000b030380600080204d00d034030780c00340500504044065030700e09101c101c08282c80b03070142d018682c1400000600d0300c443d4a40340c080c06940075000407000d07444649918042840d00420700c5240d104600403000b082d03409192256501220380d100f04000e03c0e00c1d520206003c090680200f0076070601605103c840d1010b041c2c0070040c03d1079001d00c3d00c0c2149112141031003404440016000701e4400401d403400c1101d0980000490b83c102d80b2945000f6103aa40740e03e000c4445104008001c5d10032004890725104050b0050302810560300246c851210030381041d400718050502842018001ea071001000e160f107940116200368106a0504000d490071100341822040080c01c3c1c080343e00100501001000101601e82801001e0080d041060080a2404c0402080224240c001180340718010400c100d682d60780c2e504a43c4032552040c015516583d40301405860700720304803559804190f0860000341036141c401c000246500c4d082c1c82d081500c1513007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 106563570 1250 106562320 106562333
    0x2040e0a0b0102150f0412050f04210215030106020d0e0616060f051f0902040e010e070e0a0b180a0b031302180f040c060302090307060507081603090510080402030307 73
    0x1000300680c107501405140d4000c0c0120700107138901c18401c4a00420490a180c50b040ba5031851a480d550304004c024840e00302d01484000403601115801c002050f09000030350f413a04c041c1e081000d40290721541c002d050000c40100040036604039a50350b000c0e240c5091fa0300c001034400720710540141d0741c081402c005503c0908840140000040c0c019940003900c02600040c520840d0f80543d4840d03488505840510465420301c2c100758081e1196620a50800e45042c101d002404810b00070040c01e40c0c074078400101e440c2c1c0704030a000c0b8424401402c0521160b0b540514411582c0080107a00104940f00c0706000581009242c2d54110b038201801d061956540040d500480007801c03004a81c003500310000e54606405c1121994000c2200d84c0f0040104c1c142450455620700780c591006081c10300500030522182c0c1d010442c242200d0490510955440f203514002c0080d100381b40d180040000c240f00c4800606138000740d5101614810749440d541e503a212502540c502100f101d000754550b20030016a00018813 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 106564820 1250 106563570 106563581
    0x30409020c0313080102090307080c0a031e060911040507030b0f0405100905010305240103030206060d0311010e010507030e0c1507020607080712030c11100e19030905030c030102040e0a 81
    0x15a2800d60b0300b440c12800e00d404440303c2c15400740b10f40b07039008100f4070002d280500c4018014140c000082c041817200303c0c00300e00c032441a4030003d0619401c440d58520240b8264401c0f226480d84a5010858a1960701d08008580b1590322030034021841c00f80010140c1d400382c4103010303030650001c0140300300c55080030030840034040080160008403c200400030312032100d03001c2c050107075100c1c102401000d42080c09204a19031809900c0d10b12901d2000108080390300802c0068000205503008620001d40d4101a100f21440065103401586800d070b101c041d43c00107510007405140035a03030900001001100075a5550480840103070701ca4844140c007042d011a100c01001d4070751010f08130314100095a11481c10642010070242c4d640501d2101e65035105070f0502c200c900d440c6a41c2024000c490780034042660300c3c90203181c00d54a8540d90070920703555a90810003500c0106402c9610700d550249460000c00c54485803092030301911420b010142c0618046c000d070360a1300c02c4c45410750859518560950050070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 106566070 1250 106564820 106564837
    0x303071401320f0c04050a0b040e100b0703030209010203090a170f070617060f06030405060a0f1401030f020f0a0f0e0c0307140a0e1003090218010302010f11010615200307030203040902 81
    0x13407040100182a031030765468140140a00054251107e161040c41040c88000030400d050014035120184141025001036800c955094500140c0b40c582c0000181e1452142940c0d56504c6403111800080e10704618541c0c1c01d403c403508003558040a1804042565034016006450101d521201410304140c0b1403074925500c013000401c094801c081da4000f10300558419107064416410100401c15a010b4070b004020200702000d0742001741c0707261418042d50400041c000103066032660f044020540d80d0342d1078242c0d40a440182903065003582c904240203410a0b5101d040164603c140c0010b400001d000180d81c8034080c281c032014404030700150b03081c1a0b50702c588081c206008203e1000320580e154044504001001a200020100c8680c0104110014228000b4403070a41d82c00040c40180d074000341400c40b900c541e0a090701026078500909014001c1c0350440103001c0a01114a2040e0354048181064864414401b034210341011640c3e58482c0315141c1c000e8050303031040000b04900000340c0c1c010b04c2c109 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 106567320 1250 106566070 106566091
    0x304080a0318030503130f060203090616020d050f0a050d1506140403050601060c0f06060b0d0f0504020d11040b0301050405060f09070f0302150409020c1b03030a0c060b0303071401320f 81
    0xa251550308c0400300d07041650706808a6200c0000c22102c0e400f046861550404580001d140d1300955007402040d03403061440030043d05002140c5909038a0051055845e0155002c4042c0807014404d281e80c0c090041e54840c0700001201c200c04811425900c404480503250000007034503490b0f017008002d5a142d41404401c07078142c06c0070040c00300464594890b45007d084541d403d1130b6240e400360710381810b645401d500701600c14505001d11006a8030310700b10460391170340407001d98104940d05001500034425085000d4165091804010800c0300115141c0d101c0c411540059030551030711010503640350034038000d8603440d40c41480b0034000b6280214000395a2008503100030b1030981c440a111050741c200c020031070881d602040e40340f8000440c081c40c1e60403a0400364011400e0600030035005010300c810172400f40c0102e0350742049501584041c021100410381050020560201980321103000b0803070985000640c0e90b0754416486d50b0f08440b80700c1c0000b642d4401017904180c481c10300c207880042d00502210800c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 106568570 1250 106567320 106567343
    0x3020c07230d0b09070609060e1212040f050a090605011205040204020910110607030c0903030309020301090204050708090f011b0815030601080102180a05150f09060304080a031803050313 82
    0x2696402c1d006166a4481c00b25901c060900741d0005160580742d40140e4240402070105101040c1d00070180b0080705401c0b0741802155031000e50300c1c2e051510b554203254003542e0000c1c0c0450812602940c0c2e00c102c1b042940c0c0709249640c0c03102c038801101e400d07002e2140010404000f1740302c20002e680180d50003d000070801498580040009803022846100f9032021446081907003603045002d106180d030069650502303003d1140700b0702c0014020005400000c00f4075541e80c0704082503480035400424003950244c02000f00f0300340100060290002120300c0140c41c4541400d94a00c0e1134180100801e1642c0d0700084d80207811030410944042000911040c43c0007401100c200d456a01001081d0081c541c0c02c00041e910745030410032003c1038000c03000c1140510061002000799407a06200401c08403d0310804580703030009a41c1c06912840303448011513200754044140000e00070080001e0000d512940c41c20001c107071450208024400c0c3da000c0c040c01080d001e100050014240010300d02d20302e485244a40d2a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 106569820 1250 106568570 106568639
    0x50a1503110a030b0102010b0306041e0c09020a090810090804050906030114151207033503190b0f0a0b0307030e010f2705061b0c100e0d03020c07 64
    0x100e80e0030400982c0300082c0c035060180303444c1d40c0a01ca84003000001ba4050709079071034140c0300c42c811704468040d0011810510610802801120803071800030707001e03d00e41555200d24010009088400c0342c0582d075200e0240400b485007402d5644278070006030f60300c03103802c5060901e00f504101052200900d665015525420040301c0c2035510345606102c0c507405d803808060a04594140040114044000c0d503080e4802d00061022490500a0f10303107420f0014004806102c3e14418141200301c034002d544a60309020090240c1120f1102081d460301104c1c0008005c6041280c0400c145030400388001074111900200070302000c0b5900c0000c60f400b8800b0b0601181c0071965529040c21100c9003c00d18440a075218440e010342001c29119100701e00840c640301c100003040e40ca070981c07960b4015180c0c450b503040d2040c9078440e07035407100d090b5110501c101040c0c0301c0958400ea1030a01030100312000d154240580700380f4900041c041c0c403c0e40c1d2149040c1004120407802d003825100902602003640f825443d140b812601d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 106571070 1250 106569820 106569851
    0x20405030115030c05040603030503060d050304050a060503061305010e040f0602130b071203060e0703021602101e020610060e13020f0418021908071e031a0307050a1503 74
    0x34010003400049680140c6107042c83c0e4200403d1741c020038415428400c040002c01d501400752500100100c44000309500549061880c2d40b141c2d80c01642c121640c80000981545c0140142d0300c252016900040b50851a501da4000c40300d0900800405041002c0440d01242c81090601281d600c03c9100600d4040e060031138401d422810741c007020288100180c224100000207031000718103821820180a21410903050a6014000411075810594082801c8aa04400c0c072400052140c01801142c00072a00050003050a945285901703140402488407601207440082c45912a40c3c0030250103010f00d050441c21240c7c1d00c01d070f0001c070f03a03c4240842407220901e80c0744001d01c2121612007a1941c0e541c540a20b107a1030400c40400011294814854076480c1249240010b8002071a03141c0390f0034a0707980d4942601c100d06c01e1070b0105043c1d410100700001254140d885587c2524080c1c8080d00d04e0892607041541e607a105029564201010150401c440c104100440b100312030141800300302c0444106058 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 106572320 1250 106571070 106571081
    0x1020a0b090a02040e0d050306240f0c0606010c0b01090c0512010906030b010608060a09090203031b030d0b0604051003020f1c02130603020316120b030f0f0601080304080715030204050301 82
    0x1088030b078100d140d0210451820b072098000030040300002d44030016078004040e0041c0170040c60140280301101c02041e0000300942002001c01101c07079040c0c0c4030041c10080050641181c8050040b52040d0008941298018000710071543e0780b0540598440e030074000c946016100100c042001d0290502a0740c4440b92415007080c0604481c08000440390314505000c0112041a805001480241014420103843e001006000d455a1b41c02c003103000356045c03010900d54861115030706100c00d078100e0701c80505007001c0300401208000300380038843c031040360b0100200c62140b8402c1a500005c1e100c1040340046c040d80103440c91210110045007007004090400c05076007002c4a0502e1210b5000030120b107103650307070400307440500100d1404500b145001400954410b100c1c031030507030034804009d00c1d01d500742000e904007101c1498050141d8442d842c3c0080c043d5590f8040b000740c100c0c14014a40041104d84000080c0c80894914000400c5914509000301c4400d00460315454200340d0204808180c1d40c4090145 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 106573570 1250 106572320 106572331
    0xd060e0d0201150e01060e0a050d060b040516020307111f121107031205090c0a0b0d0b0906030d0c0201020c060304080d11090d08090d1a010812071a040201020a0b 71
    0x142100394540c0e40002c0c211400076480d08606040181c05002602000403e18159102030400c0c840501c910350000c2c0108445500003a40140183c2182e81000300e141c2081d00c50745402e0310700303200544942c03000502d100d24502008006070300510607440450194128071b554a14041c094682c00044041a170905042c030766034070000b2031115150b08840700f00b580724045041c5200205d07242408500e03a0b000306410003a06c0c00c2c402d42d603181e802080080300d0901c01001140401001da0100a41c3c9407015041900100540100c4031b184c81c021501d60304204100d9485103400801910717070500e04079010340e400b040e07003c4140d046200e01003c40f0015195500110b02803405980c510ba01d03000010300b403d0030f5842d10002c0503c0a42c041c0455101910340321940b03040a507003c541c081d10350a100c8046112900c03242d0780039151008410503c0c2c14004010107880c140c80f01381c41920052110707a1210300480c410040000c141000003941e203074080c0da0031059030f5000b40c4144161462080940c880345090101a941d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 106574820 1250 106573570 106573573
    0x106030f0c0905010506030a090c0801060f031104050c0405090a0e03030709051e0321071b062a080a170108010501180501080309090907080d020309010801090506030c010302090d060e 80
    0x22540c00d00c00c0d000c1c4072078020304a00070140150f60501000c28280d00003d860380c5030307080e01c600c511001c2007454117585020380300c0c3c80000c20082d56100751048030700c2440d100a442e00500200551403d05190040d01e00c940d1382c0c0030f03505140901d04418464400001401a40c12690311300c614010300c01c040c0300842c05036080342d8500c0c081c0d41c20902001a2110442030a0704201c82c5640300b2030098070302241c40b5001007848140100c0c2ca2030310000c074008a01c10610000e00e42ca15440c1c180810401e0040d540741034804580d517002402c0c41160414100c41d84400d00c075424050f85512a00018007008010003a81d07a0790700d4449940c800842c20503240701402e0b0400b08503a51103000602c62181d10b9018070840551011042c09154501843d568a92040044560090840900081e002e1404020640c01881c80701c0440c1d01004540c000203483e40c01281070760f800940c0369000090390168500425001e500010060068101e80c00b0041d0001e610416801d6000a134000406000c0748440c400c5002c0320b08880b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 106576070 1250 106574820 106574843
    0x503070602040906050117040b1005130603031403040302070e0c040504020304050706030b0d0f110a0b1b070512060a09140a03030209030d030c090b03070311030c0a09080102040503030f1b010603 85
    0xd0b9218244c0b4116040181000b4030000080d0254183c01e50454020360081c0490f4003d85071400310000e00100f075000660851031210480510345420b0f8469001c40303000e65602d6040190040c848402c40c40181d402500613409445c0a021300b800c00804103820454420483e45415034440116060380c00890381524a07410402c010030000350580620400e0a0088030203c0e8079064a40c3c0c0e18215039900c8c0c4016194072030207d07c020161712041030040180c0722102c845915401028009519003174103902a14a5025100700010b240c14100707503142c03002d05540301400d03640d0350740c40d1301c140142001070003500e2001401c6011801c1c5081449543c421728080e541c00740c1e0301c880200038949404807031581b9108151420a409540644c44034080c002d8412941070035599440e130300000c50140880c10b039100f00c240000414030414012950003001414010703191000c00680e07850599081340502d100b0305070190820030280220421540003030804003d00c40ca082c1402040170461400c580481e002102e58040c802c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 106577320 1250 106576070 106576079
    0x12050403170f06150306040b03010513051203250c0c0909050618060601050a2a030e0a0803340c1a0405010f0806130905061b0f03041b03050307060204 66
    0x110a036507807014070804080c00c42d00f444030220360300051402d00c80100020204c0810000e5903541c004c0160040028000d000ca41000b404240a60204800854040c4a20f812850761070007260f00303a81c400c00c414031072480320034525950000900e0f0341000c02c404100f07a00d46508000b4001605100c042d14100310002290f9105151040c80e00101070161000700341e6040c104a0b000000180c20755014a0070b1030810340b60015506e00b502c5070800071705c45010090740b1400d01c9580c1440c400c0d100c94500d01036030740e892906101e542031180e000e8482c003d010803a0400c00142d4420500c182e0701c2294101d030003144400b4907003d8401030503007480f045000c8440103072550040110b902800b0010300180f034856a618a4240b8120010308500c0610a9000c140100100004d09940c0e40c1c01e000201c0b043d50348001c0c4814980c41c039015072100030880d4a545442112018509051045001e272200a03404201c41032441d2280e4881107189101200b0020f810102e5243c0480060410300c090040184160303009070319203080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 106578570 1250 106577320 106577357
    0xf060709081203010b090105070c030f06020d05150d020906010c1b140102070608070c030c0803130201110703020f090c0c070e0601030605310209060a08101203091512050403 76
    0x4450a00665403420700042c00300c100010201c0790207074400d0030b02c03907501c0d4003614007034074448ac0b180c0c800740c101e941008940c410b01a00c0c1c0c00906003001410010411a130310007a940103203041c824136040e04a0000d091a0006084c00100560001c0050401c0c40b216100703079480b4882901d00144480e54490021000c0201d0a00c0c840d0300341c0c81080900142c90010f00300500180b1100c0010121030411041c92200c00601d03000f803130944031003501f19010642d6841d0a421003d00d62000742812400141c0d008030005070721102060b00c42c20341b41d0042240340d1069100d030412145080140000761014000c21039482c80749020441200200030040e0720ba8030b103142c03c60001d812242d003540a1800341c05c0032400103c4100c200c4c15021808619041440302c5480c10340049402406941c901d81e401c40303000501580b58030340100f0340310310901c1510203151900362159001d40c10069080c000a0106002000030300c003500c240d008500010556150010b1031402071200b1009480d802c1d06c098000c900c0030690301c1c0e4680361 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 106579820 1250 106578570 106578583
    0xb0d080711030303010302060304060203060607170309062421070f06020c0102010c051c0b121005010902070f17070501150e15010807030908040503010507050c0715120e0f06070908 79
    0x1011400f5605542c035580108159200080005090a50000010f8155070b1458159400c5640050401e42501ca0680310000c00354000e8888260b503201d6080011070140301c504010030b01103900d01010a03001465170034000c482003451900d036a0b00ca98410f032202341c0d81042141c00010440161701c0000c4510b08203010f4100080d000046046904011600c01c003550000203c41142d140d031614440c2241c0610704600003050b01e07200c1c013075210600d01021012180005000800e20840710400c000d50f990b1108800d00300e101c0c00b0710040225400750b501d880403c10a00c03650b001d40c8401c4240503d841c1440d0b54060031605024030306007400c22510428081144107921207079009001c0b1841e0807604c40508006000c18000038416800c140d1101107081c00c2007a400141e500501002d40244824105400701030555001005010380700e1264400014030382401080c69006002c0341d072100c21000c14084802c10181a0848441c801407145241e401120300082108078403070303000340e03540034010f03820b200c0003904280 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 106581070 1250 106579820 106579853
    0xf0d180311010e07031403121006020d0905100e0d0b0c04090e01050717070c0506090705030d080c12040c0e0f0a05090d09120c050303040f05030c010c0320010b0d0807 73
    0x20f15000564820200000d503550699404c07969204203a61683c403900c3c99481080312640c00311044405000b51041292084001d4945a400755401c0140190040300e081d0340c60710403168403428080c0500e00290165203940301400000c0e2602c549040280c1300d02c040c01c03009940c82c0c1420a000030302000065124840c03c190b41079424000c0c00103040bc0013008001e164540b0782900840e41500200b45a42e001d840c1860201368013209540e040d00d0544141a2a1305040c80f9550290042030314843c200d51055401e40d10450081d0916400c00d030158401c0402e441c4020030898117807410700d502040f401100380350301e4414490402403920620740105c41c90182d46001d040200c080e80700c10f60303528a45400011a9050f0f074960807010030074903103d041c900075542d2113502481c0c05000010f00860303e04128103d00701a00c40c1603084441e0580e8010045414403504c410140018000b0001032194203804442d2620600c10080040740d403041c0403001131868140d88104441981000980390100488901c1d14100710 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 106582320 1250 106581070 106581073
    0x150e030114040f111207060806190308120702071d0402180118021303020a06020703050f15180106030204020a120b0306040f0b0a11040f09050901060501020709020f0d180311 76
    0x2814103580c1c0b92483d40c40040000c00b160381d4480040d0f05a155031030080541041d00c3d040f00caa890b9202405000c81405031b9038207020310900b00902120100b0b8400b041e0031254000308039868208207440c0c3c0034a07400702030110401c60207400c00001d0350030103154503080a0489072041d4195410316104010031740381d10300c0380c400340410603100402c00856110510841c0a105210150317546091018505108990340c01c000d6225403c80000f280075540002c20900f40d91140d0104c94090b801c00c10140c1e911100400702046100800d80052440b9990300101d210741c506072000400c045d0348a6001600341d81200c2203100008a8401c0704001080c0b071801101c001c2c00341580680034030300302074582d48e0001c0e660000180803540e0320000b04003041c0e019070081400d0740d0302c10303401034486841d03a100500c0091607103d03203402d190a14003c1340d00c0070700610801c0c00f111016002040620724200700b120180d0010b001100c010141840284601c903154042d204c07500300c00703034140d0864080b281703000780120040340c1c841e0005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 106583570 1250 106582320 106582361
    0x30b0f030a1e0201120507020304050102240c09041b080604060b0304080909043f020d0905090a140a0b01030c02120403110d05160302090603150a050a06150e0301 71
    0x200b42080744012201c0200c500c1502040341500058542d00131948000031071615210400c8011540880a00143c41d000d03070a6076107820000c03e031000c503641c0c0303258014100c45c03120010030a25400c00004251200001c3c001080e001c078210100b00c0910021101400864075110800a191030b1510074800900070707500180e419400d01f91100c5041d402035030300140c042c3d500100400c007031000c00010030781c84c4c4d001403c00142441041d0410ac0c0844c42c8000f840d21500c1c3c0329910800d015002181041d4050819503425668a01d40410800700d100081c00c11041c4698815034080780d21842e510301441010300940203e41c903240c0100041c1142c000a541008540013404140c50724041c100403501100e07003110707119501c0001d020006014020003a0028603500c80c5810083e10109039007480b000710b034000c9034070011039500e1905054940319014004840030780001c0c00505406d1040c0e11554101066441c0022955203c0d2080d0b0740f51141c0d031050383e000c508070541489003864240124081c01c010391041101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 106584820 1250 106583570 106583573
    0x3030f0405040209030102120c04090b04020f090d06060503010c080603070b0325170114030601080102040b121012050601181b0302070201020c09010b0403020102010b0f0604270c030b0f030a 83
    0x1600032800340c0380c852600042d0b410180e640c00d4050743c00d142c042001c9503a817401c20303030750101480d40288142c1c000c0030f0070640e070040310b4a0907200765030076a00710003202480c00723405804100c1404440c9808941c01a90b0780e40210380b40e00c09106034160a8a90b0316180001d0611504051515003254024103041d4410401c00c0685030b400030380545c04003200d070711800400072001c0003a9084140100400303150403402d400060002017908a10000400603019103801e81d0326824158217074442d5004400c021003040060030700c80d8120882c3c803a80590401c03a44403103552511ba195000c0c00d00110309540c564040d800520030442043d20701084008280010848460980d42202d000c13022410300364103040c0d001c1000b00030340e4020b02006440c1c4034001c1140c5025a151805810300b50014041a07006601c3d02040c91401d0400203264194103a0060025080070300d0034000d50081c5020242280100020304100304e013120540c0104002140240c40208400c012f0701e0030f128202ca5441c5c800c40c440d601c000040c20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 106586070 1250 106584820 106584847
    0x2202120619030308040f0510050423070b13080708010e0601080c01021c1803120210090c05060a05070b040302060105100f0f050a09050a030b1506030f06040c030e030304200303 77
    0x1103d41c9800c181d4070325501c904201125056008010b4600d014031780c0f101d25000c1e0170b0307402244154860104510b079071601c0c9805c41c40840c003044054181b030b4410390f41802a00c02a4014203025034a040c600110151125042421302095511800050f9100c40c090303846048244505405015800f00511000c2001d000007580c0d000c3c03c5070240550403440e9a1140d100c1e01c2a002c00819038040808a420507589240505008400702e101d44018024200711020042e901e00a0340209900490f8000c0024100380811103107601c03000c0e01c0c2007401010401c0360005100d040d250340c1f046019030050000c540c9000d052000f054102c40003601003115030840304517115000240b03c0356000b06450300750b8031190340480644d402e02d0a9040305034442007140d00003040140880501e1300c41e00c582c51480c2c4540c10542c00340469404192032450f048031901001840c1c174106540300c0e4011000303501e03010440301c0d44000001d00315801964140d54031080d060700284203104505e5181d410442c00d60045140035142503980 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 106587320 1250 106586070 106586119
    0x90c091a04060e1201051501091707050609030a0b010909020310060303050d051f0308031602160e040c030b012402030a1205060303090a0803040e0603010b0609010e22021206 76
    0x140a003c1d035030740d03643e6441d2108030311040a4195000208481c4c2040c00002034010200740c5000d0004400000c0403800c144801c4c0c00000140c43c0038000c0540500380000c03c610741d0800c00380250188a00f07162540410104502d850090441800c0000c80c0c45140c0181410001d801300c02d02095801c010b010000294400103c0307480680011000800e900c59080341c1102144a001d91811201e4002c404414048030800443c004e0b02440c210403203100100009070707150099898465014070301403204201150211280681c014816107071321020750f03180e60391410100360a0f004100304200410315111754510b400000000d600e40390000b10301380302031040003c1003548480c03c0f002c55180c84001080e0603031401c000380d03101100d005000c00500c68481140700c1d81c98005204a0b02c00b0002500840c42c00d050600c03138860a40300103410145400c65810054900d010103010345500400d40c04142140700705c1109102c084441100c101603607442040008051500000e031219200300c0046815660030240042030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 106588570 1250 106587320 106587329
    0x20709020909070507110303030901020a030b0406080604030c08041509080c01020c22020c030a02010507020d0801030b040602030c160c0f0609150e0105070f030807080a1a15090307090c091a04 84
    0x109a5070314991918807816080b22413107e40521000c018040a2001074015160051003980c08010700d00c0c0003000c202c1a00c6c014800d0442941080c3c01103400f282c07041070650320250003011801d14003642e801001200e122902524000103020907401c1c000050103000c800c061740c2091008107081e050500c0003da146040042080f41c601c0d080760b06100d800c0c1710750183c44207020b101e41982e85500c500f07400607020b80001c503507000060244104030103038907008502d010f058079084a0500ba041c0e5882d92108000d50010b840100c03584001c0c0200341c1180038402003100303c20302c580c9411290601c2c292484080f550241c1000d4180040060240440700ca2154180e40d02c1d1001c0c0b0b424910f8060000040c3c82c14405e019014003c00010f0280300b0906400c0350481d40105d07100d40d2688001d131f403800703001d104907220014124150782010b40e9100c5280b500b00d400403180c43c0600341c407074500108000000e103403800b5076101c001070b00e89405589079203e030000000c40007860004614480c0d10001304455201e40700342c0c001c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 106589820 1250 106588570 106588577
    0x20c061503010603080d060e060901061403070c08030403020f06070c1109100302180f0a0203091b01021e010b03060601050c0604150209040923240408070c06080702070902090907 78
    0xc220105a5007500710a0080d074000156503640d0b140660950040e00090080e000c0410007200071aa060501d61100c0f03040b148955140c81c9040c130489500c00c6a0350020b04050700b00004210480085240e550040d4003851003500144400e00b42c0346040b600300030004280a081c460000c001c18040b4800703911109890808544000031a500d0340c241c44600182a00040e402c016480c01c0b072100141c0010f14a8003e0041d640844a10fa840501a07030607484112515911504480c020490340c0b15800341d01c00c1404414010b030ba00c2e40c405203090002c10003100028030000d0b9142c446120050400f84100b603040300080c60103d14046030b03000703019540d100c0a04005c0414039000001c4140b48080e50640300c006000800c00c1c801030f8054100440c00d03001511189140f40c21802c0050500c80000410071a4413075290b40e81448590741040000403444020f20988459000f04290700c0002e0482c0c0c403410150810b9141e601c10350a0190000303103000050737000703024098410402100940d60707000c1e68551040351880c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 106591070 1250 106589820 106589851
    0x40201021b01140714070b070b0105030706050d0506030f0609030a08060603040209160203071e0519020a06032c070321122f040501181206090c170d090603020c06 71
    0x280480940c2d17444404102035008004012a0840500000700106070088800340d4981e6245c00030036468030304511560380424010050301e007003440d103500080d600c4100101606c00501c42d0740c0e2000d04010003111920065000010100419504400b0841c1c114806485882c1940f8180c1d001c40d00a10b006020301c4001451030429a51240c070070400c4480640c1d118190081e0102001d4a03810810b0720018211103500418196050b18100c4c60341204071250020034403201b1924100b0141e0080c114698000c402e24203c18012201035042c1850310035680e801c0d0002c18480c0c0c50750a02c0010401d610218680d4400742086103400c0c3d80c0d000f401d101da003181c0306100180f44102c102a16000480419800c81c085150800c441d501901075000791048070001e80f603480d0005c081248104d00c140c0c40740034026001686900b0030b40072170f4540d0710285080d0701c10940410041e40f100090602800300c04003c8449a0003500303107404e52540b00d89500001c1001e4203055090030802ca980f50389039a40140132024841480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 106592320 1250 106591070 106591073
    0x180103051008070602030a080106020c01140904151401030b060a080621060f0f0105010f081302010903170304060b0409021e0303040b0d06080f03130308030402041d06040201021b011407 81
    0x100e403007002041e1650803100001c0e6140400384d12900540d0007400842d40110001a03001d0006c07405403140300f0140e46a124003c4030100c1202c80da08070002d442c0d0030a50b204907030414952050440809000c03880f01c5100b1500003240010309031019020b200d4001c0750107001c10050684c210701d880d90403020844038941e282c812004450142040d10000340003a00c074417420310000c1d2001c020f00c00d000304001c0081501e2070382c0700c03801991030014036032071440001c58050004444c06401103070f89050920514040b5040d9a40f902c4490450a0010707061544900000c144001c1180c0351088080d1640c054038240035401c4c41d500081c41018010311801c885903880381d00600240d03018811503018182081c101a25802440c03680e200501030b50155003180c0c815401d0211688100105440d00b8080c40c0300038441e030508581e41d1030450341010f0000c0b81c005407110b1034001e0340c07140e0410780d40b01c0c00341c801c0042600b40b405000083c81c21028051002d6050500b05100c0141d9a100541e81c1c11100810412950340e0030f42d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 106593570 1250 106592320 106592341
    0x1f080109050127060f0f1802030106080f211605060f010603090c15030908040801140c0403170708070206190314060a0b09010903060c020c030f06010b16290108010c0518010305 77
    0xf2445c15038025140401d17043c0350052081041c03030028009d800800c6910340f602c84444e51590700440502d070540c041c103212182078480c0d8800d4402d101e580d00c441402c1034100c04420201e80c1c082c135021a810307000b260410100064001949005202c1803900340078840b61901c6115048086001d0004803070000c3ea0500d072094002d40007611483d9004141c81e40d01c69481038054002c004080e05115a1440c1ea400310b2680c804540594066a42140d40a112466071501c0741807558880401116044824098400540e4507100500100321201c960340072101d500040c002c007195501544141d2500200c010b02030540c0321450030340c0556501e8a102580d507070700b800041c1c40d1584035900c0200b80d141000c0704090382c9076003c5440740040070113030308586c45181d0303d0800c55102c3d5000d010340d20000d04184250351141c40854030b070004941c0a42c0301d414080d0021781c10112402058090a1015854032004101d540707024400c00408440380e15005081402c034443c43c2d224a580141d403030781055143c1d00818442c030300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 106594820 1250 106593570 106593581
    0x90506041e0b010905010c02100315030c090218062b02040f0906080118033002030708100f0501211503060902030106060305040f03081f080109050127060f 68
    0x203540d60103850070281da0603140054102e50700814000741301c50400042550099a015150701e90003480c40e51802a4550210014460580412200102d0350f000101140f82010800040c102c0c1110150b07850820000b40c1c0c11308070300e4400cc2405600104085d1070950b154502034010300c1d41d2081e540891004003500c003c003a0180e5000340044c55900400000c000403030742c0c8035404403070000000f8031509284521030300310f00c07a82d1100038010901c0034000c18041002010b445180804d2861280d41130f4600303220310740480e0011034580020404410a12002c05100031035600108010300d5854036031828000000c0c0000b68040345460352001000c1c10602114081c0c0094a65541c2c059051420a9490501401030062070074182e00a51030038401280c258400c0c02400d1103243c104d181c140c5104e01d6503604071051080140008403402d200005904400c114a40c80001400c4803000810151300d18100b046c212801c90300c00c81d1015641111380f119061020314210401a04000005800445003194501400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 106596070 1250 106594820 106594841
    0x5010f05010507061e06090e19020a21080403030e011202030106050a0309020307050909060a0e06040c0302060904140108070f21031805030d0504080d030614120c090c072a09050604 79
    0x41c2010700110700032403103a10402030021308ca011110039a101c2000194490401ca40280d041440d2103005c4c400300f004105c0900347d084030503421521034102500d601c041600260411130019081b00301d0a19150782c000014003d01a900b441180303503501d40030000d086c902c1261102400c1c151100124010355405101020081c00e0207801300b01c46150221645484800c210780502001386401051100c00b2000206103205550040300d030b05d00c140c110380030000c0030303003200d83d0751303030703115444000c1450050038204125000f441248000e004450030904101c110700e0458221141c003040c01500c5505044140c80c07001c03145601400d105000d82460000424228215000140c05102e00d0a12138500c540c490014001c440c0c1d03200944043c40014081182650b0407031007541ca810301044c441c4020303450050401d94003030302030f0811100b8044211000c6481450102d400100c020740200e541d90610482c0041c81c010701c80040da94030080b88459402e0311010310760307001d0f0600c10f80d034a00000794243c8640d8003ca131401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 106597320 1250 106596070 106596131
    0x1050405040509030421020102030703050f1308100e0102071106031305010c02160e0708070509031e010b0f01091d1504050a1506030b0d021003060b030906070305010f0501050706 78
    0x1880c00000c640d560307034040d206d80400090030b101d2090500300c1c80d540c0604400e50503030282d0b2070502c07d81c80c1228141c10400c2964020001040b0030703203682100b030b0a10310041c41044082c11401e02210340d000c007201c041c1600c07500e46074010880e450024160940b01e0086140440340b040e205d480b0100004071211040100510340c0d0710b02509068255000075481d47c00114050f0a00045612458111030326282900c2e141c010030900c9020415140c000c0c0007a103041780300038003148c510081c01c48600420304440c901e901010b0755a041000d115003031051404418110a09003d01c941c1c2c60410314072030782e950b00e2944020010589000c00c564400d0020820740c0d400c801001800f55042240000f00146014220510296038008001074070501034001c10002d144000c00d0300e01c503401c8540030b004800d034100c4000010155600340114060f0743c100055409902601c00824103850f0040000d0704403003040c1c04c01c543c9900305040410450307a100040b240c7c00355020102146080a805066010f6252010007040c1d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 106598570 1250 106597320 106597331
    0xf0e04110a03030306031203231b2b05060102031603030209150a03050703051302060705030c0304120b010803031909050a05060703020c0c0409021023040b0304140f0705010c020105040504 82
    0x18036605400100603217004a80fa44d209000c03d039000d408550040c02c0d4110344d5225144544203d5400100b125400940b0401c001e992100300078422b4005d500416001c0c042c0da134071a140c4540f140b80304524452010035494100600e003130680002c1d42d03a005a0070514282c07403581a40b2810540b0036016920034910151619400342c1810120800681003280b4010029180000007001c2a11034014240640085540343c2840c3c0700e25020b015066000c20b50569161004002e0080c03004802c1004000030b00070b205022121100c2407030800c060302030603404045107620600502000fa82411008008441142c4000426003c40d10340700d4288280080c02501c28042c0b0310401071019050740081c5a0b0a0000c000d850311031103c10b0401c01120010318019401a503084110b041682c0946200d4100440b2034031145102e0401c00800138440d4041e820443d4aa60044240020410303402c1134400881c07100000f034802c00211600d442c0e075a0f0017a03c01c060400c16039054080075640268220f40c0a4200a8028020b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 106599820 1250 106598570 106598573
    0x30e100807030c0207051c1b060801032108010b18120309030f1c0c1407090b27040206130b0d0614310216030c0506060a0f0e04110a03 59
    0x15007140c6880110703050000b0002c030203201180d4501640d800801055840c2d02d1740c03031440304c0400d528000329a80c44840e1194100440540d6441d002016660b40d680c0d0300358194030302010072162031458170b40103641004100504503044003415040d14180001e00e926441c00c8581c0c1818000b100e4582500000801c4c0000c02c91440800101201e0006a0440703e44c441d081008540c0d807441007800c00d0074804080c0a00a200f0310a480401d4080d02510248041d0210464003e05161141e40120350803580d50781da02c8010b0400b40b0842e458044004903103814040390b02010043e601d4001c000074440c4400054216502d40540e00d080080c15a15001544070038a040740400105403030f0199070605012107024480f82d280c100051300c50015951085038a0f010440f4000d0181030804520401181c4c09001968026548116020010b4040d5a8004d00c60790325040c201d06164002d40b420380108610001840075100c3d152200c0200e83d00c41f4404401d65640d8202100610340300d00c03040e54003060740b090010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 106601070 1250 106599820 106599827
    0x7051b070603150803030103020f0a0807080a1b120201031e060608040203070b0901020307060c031107030f0905120a020105030406020d09050709060509040f120210020c011401150e0d030e10 83
    0x9441d4551400c00102c0e40700000081d182c40540300d4951640e10400c014801800c0040c00b42a84c40b0340600120070843c0c4030820242804c0c0150080506544520030345010300c0041e44000912142e5074196050090508004080700051410040d060644502440701284030004074848040b41d400002c2022549a500050440b202502e007039209111700007000c11228540811035a42140c1600110300c0c1c00ca21b9170b01c005c090700b2004014018584d5404e510b0600c60038000041c0002c903c241d0750300c0c0ea05000c0c0c1d40c025205541e41d4120a00510b00d07814400c000d0a000205030a01d19024208161030b41e58038981000684606060b000120381400700c0e00042001c0004c0b102d0948595200900c1b080361103405000707001074122006440b004048400601195a40500051141c0d03944140c4100c0c8020701806000e980c84400c0310680d583d5180c2071890304249449125014040b040342c1201d0304405440014455916084020300c20044c0180c0d94007010f0003901d0b00025101e01810020b860f60f82050080e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 106602320 1250 106601070 106601083
    0x3030e0d060e0706020f07140111100c0309030f0201060b0a030e2812020105041a04020d120e0a050f061909090c020604060b06030405060f0711010f0614030a080a050307051b 76
    0x100151240d42c0103800c8510010404200307030351a031030700c111440c801100110b80b41d02c48150380200c2b600540d032501c002d407505802440c0001071146c4010032200a14a801040c081c82c60280d2800c5916144060000540300012179150706000e1038003043c80e01100341c12506014034203421188044c5c11032602c0140c0040c116840c16524094400340e54013802c402001e900b6540c08403002070014810070a14009400f1090001390800d001030b1100c1e458200036940c0034400d034103905400c80400c410000a41680c58140c3c08400a00000e0310510b841b84010340106005004512107204c440b80c1140f49018604e00c2540c0000003403010a5041c0040104c1d40b01c080d407a05020380c0c0586105017050b801c5040e50408804603401107070310030300500380c0f41c0c1c64031810307460004003400102c100860340b16015001502400345547c54842c01c080091500c1c9010541c00c940500d0802940c0030350403081148002c140441c080d141d88659078109590740c5c0c3d554540480d070724400d641032108100881501d1803841c2c800014203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 106603570 1250 106602320 106602329
    0x90b01170921180d0c05041d010605010c08090603070c0203100f0c030207021f0e0402041403010506010e06190e04060b03310312020409060e0f0604090c03030e0d060e07 74
    0x111107844031502695800c5100703560400000900502c042c442c0743c2051001032144c1400b812403a040951200005801d607490036031403e00700702814542e00703400b0000303100d003030b0040009080011448040d0b81e1214101c0c00790103840c920034400440043d04c014010790130b04803516401400e445195880000150003460b0058004110398a40306008400c14081d02c00c585003240c000785070312811858580240c8124804a0141d1300304426000621300c261150300190015240441d003c0d0403400d580000d050840d01c0042c0340c24100101c400340c0c4680c580358038007242c440340c2900007100300f040140401900c000090401e03440c0c2181c0f40610000b2102d40308400b85004a03d10710f12502681e40c40c40e440e18040701107615608241e201041642d0000703016541158117854034800260615a031055800100c8000e40c0c0984c00d0341c40f0740010411000080c800090348050215400c000c0900349459001e00509203000c003d05105050920903101d03500e81ca52003849507440300082c007100d100c081c8030703070342302c250354401c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 106604820 1250 106603570 106603603
    0x1908030f0105090f0612010615030606030e0303010b070813081609051e0c0c1c0207030b010906030503071104020c010e1609050f0c03040c0e07051e1201090b011709 72
    0x45820700d49000e0f894041c0d4414003181d40207407121000c004034030b01e21180744442d40d965034000041d41605a100c203000e210054600080c5140f0701800034043d5161000703040c05a8008000500c40a80440159114190090b09140d2610300404d62030720030619640100e102ca10507004e1032140c424840c0d0000c1c09885c0e00e25424071040e2507400141c5104028102d0300d404600422000880981d101800707414003a802504844d00c40900501a87c803c0c0e011800c50b80060f008200144140801007030034900500c3c142800708040ba203180c4a01c1c3d00c901900c00000d0105540003500780c0c3c2942c0d0b540544000c00107000080090752034034000541c1e504a80b1140c003445514100c40001c0e40d40903403051501c2400c108914040558603203408041d20340c0010070880705001510030105a0030404c4100510410f096141c140c0c0d26007442082ca0840b821084802d801a0003c000c1c3c0054515080245811503009000204403500d6010044c1c0c0c42c071540061101d01c1c641c80d1010407045c1038000030140807c40c40c0f0f45 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 106606070 1250 106604820 106604851
    0x302030c03160c0e0424110f070501050f040c0603090312020c0c0405060411070609050a080304050d0201110f070b06010509060d06031103010e0a1202150112030e01020d0c0206070203190803 83
    0x403801c084040003214080c00c1b82510f03a00340c07200c045000f001a20000c800c2c81000500034418849841e05d500820b103c9012a100840c0f00810003e0074030450b03800ca250710068555034509551144450344c1c4038020700c010540c40d06c0511080500480b040306503000d020000395110440d0600303180e520901e8600c128450f5040002248460802e407081c40700360500c1c2d00380a850b00d881a100c0d000900f06120044845100da4026100418aa1405540140c2c4110050702501503144c20080c20340c0c48880705841d0030001007107010300b41400682141e0100d680403079100341780d948940c0161010301600a00303d0b0011303400211200400e0240c1d0051055a10400b41001d00e40300e10020306007250340c2c5002c07201c02c95000035503020200310601040c001031189441101da0b0340e9040c07402503c10200a070b11070306801e50540b0744070040540244440710603103420300c000c112034100c0c20b41c001d1481c01c1d03910019004e03a100003811810754030140050a030ba00e00c900100088404d403440c00b00117580c03007107900500c44110031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 106607320 1250 106606070 106606079
    0x9060623030601090522020a0215011d012102120c09010b0c0343020f0306040c0b0a050f04080303010e090a0b041103010b03120405010306060e13090302030c03160c 72
    0x1403054034054003069441d4000d43e4203043c01d05c0002c0361400303c1e1070801824030303a500d40c0712080e40c001001c1600055020304030f0320f00c446101e0080b0300010707041030b500d4820140c1d10416000c1e1140180d07044812545494041c4400341c1c4c4110b415180f502d1004c0d40000c0c000e800c10080d8400010104c03a0f075581510020076581ea2240860640c1c0180003c01d0b12940042040540080402450040858440c0307410b00681400310303816844170710543c0211003442c0d01341a1342020762400b18441007905001351b02038290361800766244a81100070b03008040100c040070402c005030720710136003e9a26040504500540c1e903030f142c0c0d03406c5030390782c01c07d1080514550a16000032114800400c41303011055101e04503511680396607a0b5141c2074090707294000e07059075807440c3c020b10540e001c000701c0d807100f88419030b0f4030703620703800c100005040d01e03d07580004040c003a08441001494071810040c0300001d410003c001034101151404904601c52140c1140c4640302c042620080c030b421002042e0502841030810600041c2c0c1c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 106608570 1250 106607320 106607387
    0xe090c04060e0613030303021c0915050112030f0311040f0308090406050105070b06091909060609050a150e1f0f0504180201081f1a03041511040b0a0504090606 70
    0x22003103404204c03616580d003000081e01a8015149201c3d4000482400b401d03042d100104503002d481007950030114072312110480680610402c0e014110400100100c1c1003140c9001e400307142e007031151508065880d541104d40034405001d503800b42148021084c41d0b50b960303092810b9642c2212001c1c80c0b050740741c80c000145d190300880460b4012607010181500da6a101b400f0030020003c02851000c01d204440c0e125003582003140b180740850740c450440003c10b5410301d81c441c0c08030f4a000704038007411481e201d1100b510602d4000300408484044016000d41c1e42c824501d502c5c9a42e0003109c40000d10800c000115080340c8144036502500e200342c6040010403015010721102c0d0008040180c042800e100c0402c1b03480d114090381070032500166519541c5aa0341da0201408020740040c1d0340e044581c08024802000a46031921045201e042d4052240c4102e130a41501988190321903c042c02c6800078040c11071310300942c1510014044c01034100485585da42c4c014010390658480031001400b41c030740e846000d044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 106609820 1250 106608570 106608577
    0x111b0901060c0b040305160c0e0717091506060708031806340e06031f05090721060e010e04020102061602030f0705070305010c0302190906020a060c0e090c04060e06 72
    0x70403407001c850544031a21700313a6003a0700801e110f510b8100c10585d108003040203202c7c13a200409183c0d44190141c03038240d80082040303100b02c1d4200c51480015040c015520f0307000480f08400c920b00c821400d03068a907580040e15900c10000700901a403004410007640185c1c00c400c4d0842c10111a0584602c1e66034039964522403040c241c1a681200c100c410080000c11078102c034400090800c5c200403c00454001c0000d005420440d480141a48a2800100c1641400864200420080d94101d9aa003810030001d80413003105400c803002c0c081e201c00c04141d1040e550700110018550360903030065550710380082051014003202c040c1c0c003510a030404a0000a15040180e009000d20f80c0510b04003000b90340c81d4050f5a0003d502915140300e8624007101244082c800d650801c6030540340103030b5881042d60401c00e040f890401a105200e004503082001a4001c01c4044006500220004007421403904c00d80d92100300d07141150700111480104813001148100070410348295071a113240804100c02044414030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 106611070 1250 106609820 106609823
    0x1081b030304140102150a05010f061814190305012009210109060608030304050f060405030f0d02040312030b010e12070e09010e030a020a0201090608040803060d03111b0901060c 78
    0x1d204020800c10740a58980200200c00c052050ba54801d4214962040d442819685241525518401045010212402e000c002d048904120112181c00b4040040304001c2e41f140f00e41080802210040742d0f07072502e510704850303d040b00b51084c01da901c0381080d5000300308101c03000c48a00e0502c1500303500c100360002642c0010200501401c0d0341800e641041e4095a000300103058650340b1410301d1b00014100b80a00d0002e854900c0c0156240d203010b050031850f0814441031001c844e000f2f0b00a01001c154040103c3e01109c1c101c0d0916691200302840b484024810b550000c1c20130350f184e01c48101d400380c2c143c03c4a182003000340e81e170a507400c0c01030007008040e04d40c0c0c8691220907480510200b04482d840310500e90301c940a03c0002402c4295548920b00b5030380030100306401600300c000303008110340e04a181203001d01880c3c9004101d502e0a9591750100b440301030302903403040e003030844c5a208051195440d00d910102d40e009480500500d85440866841074800d1213226a50b4070001117001d40c03150f4800b04150703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 106612320 1250 106611070 106611073
    0xb0a0c0926100204170706050a080c0703050d06183c18030503040b0705040608070c0c090f0b040b0609031906060e010303050408010509010c120b010c0f060501081b03 73
    0x3007820041100912081c85000180108600032100701c8451000d40002c24440e9213910107042030a809504003501500058140b107010701410400703544c44000d0700c6e84286248181d40e9200100d00302a6000c0c010035100a024608019010641c031000030000000500c4010302440482401c0342400070001c6100c0400c0d842c035448100080140d98400780041140354103200025001d0345a90290410b080390385816808100004140b00070005494604e0f6408500e501c5e100d410a42400c1008080c001c3c054280d1040140d055003160601450400d004020420102c0070081504920700402c0548140960980301d203103444801d8541c1e003400c00484420b198000c01078910540c1300203d2000d10500110190f401c65694a0301041a00c6655a5240070b5402034481d9601c4500e0802a1400c1d01c030f0081483c40164108100d00746c000703170031244150000040d8400407038a031162900483d00440a21009070811400380030480c2808116800705040c5c0303841100350340041180364001d8040340a100e840c590035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 106613570 1250 106612320 106612349
    0x10f050d111209060105090a1b050901021006090e0c01020303060303090405090a050d0206180f06040210050d0603081810080109090201050403050a03092303061801180b0a0c09 77
    0x424085034070100c601c0700790030300850402c0320160b040030076458201d82c11050765100500511151802d81481580040d50010602111009852a80784d04628050100c2400320124606645a0091105000307030140190100308540d602c0d08428050100d40c030312210580640240f07900154400300440348285030240003036151404030000d11009250050038200700d401081d444c0d4001400c01d200c0107100129681c000c120074104003442d50050100c3c80358901d043c2d800048880303100b4070040350301383c2c0c000c3d0111404818a1000300c020f449901c296030b41e000b06d40707240442c04820044a14090004080542c00c80c1200c00d0305241400144000303420b90301c01003a0100010801003405400c10034180d0320614005080a50b05e03034070b181c580010071404a020405040c0c050000c00410004480c9603c13000c007810f5100d0750064042a103d00e03002e80952001580190075504482007500200d80000b892201c0e09622000c03820b0021a440041e102000c1060501109200d164410312451041c0c90404880800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 106614820 1250 106613570 106613587
    0x90e010e1315051032030f07030803091c020615150d390c050109082106040b0109051918060305070b0c06011e0801021305040b010f05 59
    0x1085006210140078100c1140c5400010711480b50207011507541d860110745420a1032420700c00941d07942284400702a413424214080c0e8400c96003504818007100580e00c402e041001003070030443c52101d856003030710a8130000010410024025031007006214181c5035002d1403020f400c1e04282d9680351640060b0b110001150607602e4541950094041c02410030f0003203103e125401e08523400140080ca580b0750390308440041003400707001c01e940c1c0c2000c806a038069000300c4031201050050011008041041c1001c510003003080961000c070a554100f401c080d2241685030028010f03692140c00401c6801882006c00d0f220f0a050103440e6a1050584440819a041c2403c2c0040124025607862907415100400a800c1000401080900075102d40c00728149042d821306500d0310071940c0c443c44001c0005c104d09241d2103000b0908906498000350080e0300e941c075030082c3d48120081900003201c10752000801c2020400c40d980982d048820644041c004078030300340010345040464541160200348100035864 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 106616070 1250 106614820 106614839
    0x405041a07030236010e1309020a0503010609020a0228080307120507020f0c06070b01050d03021c08010603050601110604030e010504180501030b1008030702010302180904050c010906090e01 83
    0x141c0c4621586001820600b40300d4010452030328000000c0005030000d0511005038140040d52507038a0b1080c240004040c030900c0110f0b4442114451031003139281c0e561034500c11959500c00c034030b0080a00038004d02150761a80702c44802580107800c80d4002d4491242c0c0e40388104002c0d080b000408094100110b044455604c03407501c9a07000404c047e040040403c0081041b00e19849028042d4a059004000200e00e41c801c031860407001e0019a4070458040c4840000260ae00c440541916419070342540603030540d2409901d04503040c0295503c40484d000400c1c00c0541c8441c409040728136946c3e0600180e110107005503401540d106c8000001d402100006002ca80500c455540026040c5030191800399104540c3d08100a402c0aa5442c0d0b030701d0350010818010342d10f0040703420408003418201c0c0315181803880750b0340c1d21407400c00905040e004265401000f104130f01100300c000c000b5101c444a841e0610701a07455502201426000c90060b05012607968401c00300d00b8261b648601d1040700c0e0303908140245 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 106617320 1250 106616070 106616123
    0x4030504051e04090b31020402132c060402030705030a1d070b071b060c0b04020301061802030a0e012313020d1208070f0801120c030c060c11040504 65
    0x103160038507802c03152940c0c0c0d0710345210f1000d019025000c2645142480084000e41d440c60040c24040c00304098040300002c19902518002039034101c90050303480c80d5845a2542c008040c0d840a1400700748850310404503085040200c5100040d4402002c4075900d01d402c20040740020b80b0300300d000640c01d10000e15141100d034840040c4209134400440d0903800441020b2410301e0581141000300c9000c5041400c0021040350740400589c0c41252010440c1402402081e0b2390380305402400c1d074603007140400c041d0f4400b9404070016218180020100b00000c64984001c2d42c401c4c0c650300b04403494074403080340c056410300c1411701004082c1c80340d40d801809200ba29818030000341100032450702c18514140169500c484141344148903130b4031914400c00c0c0800152204200404500a101b6610000900c040e40052a1810754507884028400c1d07034150b043c03003031140b40c050300010210302c0e03010408542d440e000400360000a10807030200c0302c0d020a0300c09200c150748003560002d00349000028502e45d101a0329000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 106618570 1250 106617320 106617349
    0xb0105041503021e1f0c0b0a15030f0201020d0e0f100203120702011b0c02090103080c03160809040606090503031204030c08210601020a050c040203060f040203190b090403050405 78
    0x703035044542c8980018440c0f040d501d04140020f91204410704250800100d5911042e2a0603c9800c401003000c101520254112000500014000c00050742c001c242e0791150303002180c4400c50f00c640544901c0d2202070104400010b902501c90408410105840740c00800540a809000500b40580c080306105101001ca426071096010900800344595001c07034a041c032031845603002080e0050051807032000050061005c2e800c0002610070280942c54082869044071341c041da4465584020314406401c1d40074170300d19101ca000324207401d00180203401c405040007820844040000c03555801054400080611a55030903400c140941481e208041c0c200680c018000e04014450710b00c255030ba40800c0d03001c4800c2c4031060146281c0d03d2641c2185400c0d241d40300c0740a0005181d00a0b082e100c80340d50301a00c0c259180320725000000100552207040c44840d1419010740155209c0c2810300c920000540c0a595040c2d241d8503051820303000d881c048140c1406142c00d602c0d4207103130504100c2444000403d9208 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 106619820 1250 106618570 106618601
    0x120309020d0605040b060105030405030304030f11100c0306080309030c1002030f0304050703030905010516120e0d06050f0a060e010905070e150a020c0a1a1c06180e0106030b010504 79
    0x10000903803901c1c0030341d151007441250005401c0c50180740143c0350b008003610b03050411000703004010000e00300004032500b2a4060400c06a58070000e2000c90f8411a00000c1035140e00035140301100c1c01c05c16070402c07884130722161028030445444841d82c65803800b400300000c1d856400440050003605000d080c0501e4800c0a00c180e84c601510109184000d03030050f40e08441a5002680070418140c2c020100b001410091800382e28000c160440500c1e0506440d40c0604410940040c0d10241c0d40070320401e10151601401c0e08051010741c1c00c203c070040604032a010ba03095910400079007026400d02c80c603404d44141801d103e260f0307400c14180000038040107003508284a4804102c520640c2c5003020b28104102601f4800d0f51640309000080c1000920100b450040003602014007150012a800b40c11820602d6080f40d15001910f0007040f05403504414520000d10788031000c41c10100e107803041d68402c07028060500220500b15802e07406c8450710f2102910840100300144050b01e17140e00b04130011480c0d0306c0f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 106621070 1250 106619820 106619831
    0x4150e0307021306050a0f1401051c0f0b0909070e090307030c080a052101061206080705040c030f141b040602030306010305131202030a03060e0105131503050703030f031a010207031203 81
    0x5c0070070b00810154008044000e07050008210f0f9400320185183c0c084020300e0302d0303802d0242070340b8040c88181e04050896450758031900c1100c60000d01707600400f0780400041c0083d2035824108100d0303448980701d004400721003c00d000000c40c1507c00200702d0300b045906640b030190301c10f45030301c80a509400252100c03007000000c004440104034041031585000d455420b40706015494400c02070a1100c540d140480b40e642410006c0080b0302012032014112401a03c01054403009440200d000f04180e8200500e0351303142005c40c00042c11108003640c8180d000e100c900805050810459026000754416070340141d00400000f1030552107030b0032041c0c0002c2490350032440b02101e82e6a1010000034003101303100580c030108101d180d06505011f10030003040b0912420f03d1950508000c1080c0f000985000790200d621418400700207030500003403800454104007502d00d41500c0f0b1500509005900c0d0492000904180220b000c6d1050202c0300007508805070014040b00b460f40e80d074141080c41e0725003000f0030300d40c3e1038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 106622320 1250 106621070 106621079
    0x3060501173c0d0203120612070e0901020d0f0504022e0f0c0b07030e06101202040216080307020a0b060907020c0d020102030f040e090f0703050d1101180b04150e0307021306 76
    0xb040001c01d0503d20f600a55103a0580d2203d0784004403005100c10b100d4413510700c1030303c0b00441c0820741c20103550a503259040596100d6414031b02900c01c00c509109403510f00982c6111009265001d40d001e54070131104445000b0103a41801c040e407428441d240940202c3d80202481e46004847c50b4a504070503082280c04180070340c564140c0ca0302c0444608020a0322201d09080004080c0a5540c4c40851348403204009070910900b400414003110f4024040c50b40081d03406081706045c0e20030120640d000c401c840e62803600340c4e802525580c080e20704403514100d0602251451400740b030030910440c100e500500c800d10a001c20481c00c1c00d07030b081c4207a05502040040951352400440100054905a00703029500e042072100da91429019443c00f40281c1c204110900000320042400840d000b00d921b01404400006020140180000c07840000341007110060f03001004520040d03544158002c601401e582002c482c650b1081c0c48007002d01d169141c00070840307a130061030400c0f01048901c2112800068290300d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 106623570 1250 106622320 106622323
    0x1c0203040f0b04050d030501051207090e1c0c06050a020304021e040e0712020102060c19050c0705030102120a15050319030e0411091921080702030703060501173c 71
    0x20388081e6401c2c0c00011985e240f054060191a0040000380c0f00506482c2807505051b44410080c0078001c2420f40b2a1941c41005204004900b1000300c03207001c1c04144c0c1030110010b0a22843c0070002c494290600001074040e8055100792407050f600030300080c5c0d101500d071175409410342c100f5000710380c82540c1d190080d60714081080341c003002c0d101d2070145003640b50b1140006403816100920440b03990008101089900750100c404114078070711410103a4481d25460b060350704018883d08500e4141d8070100c0ca403001e104481000b107000748103412040002d000b0480c0005c14041040c040c1e2501340c0d00031002c8281c4200c0300e44088105901034a490201c122060b0001401d0740c14200345007142074004912350300c3c2c0d440c200815035510818000d4010b4010f15180a141c14042e00880402c940075801c6401c0040c00380360000c841440f40c7c0141074410841d10392802c0d00080000b80545807052428900b145110039000400c41010822607421091900000300180d8030500e80030700364400c0c0d04408481c900200390 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 106624820 1250 106623570 106623593
    0x30708070f0c0b13080c130506150706020306010f1d13060801050f0603010b060a0206070c02040f140411030a020a030609300e010c030e10020718090b010b1c0203040f 73
    0x3e40760710681e5207211601016240865420400490f00003103000b141540d0798030707502d07883e2020b01c400c04155542e07400300050a001041079650000b07800040d030764041080c1d0381d005510500d82601c40c12031012203414121040b20804802600c0d242e5900a1011030f40340c1880300340c0c0c424006030404138040351202c50107401d40324141d070242c0d010030654081c000245005c1c00b851032500c1d000e4a507603052000c0b044000355201c40c050081c0061100021910080d515030340c020091042004105208400e20b10b10041700346c03107081b58140d03806c0c0f8a480e14a009407901140d600762041d00140040491410f5490300d40042c15410011281c2400ca107003032504042e1500c4c050030101d0443e91707040c032820301010300c09466a02d10a0038241001084c0d03104c04002904135607583d11043d4151801c101c168920642130f0702e4007100d500907242c00c083c00c0d0b007401aa0750301a00b12510091054003d180540d0f602c011103502c90040d400640a410040c84606002a05c564081d59002e4000d10200480c03001c107443c2c5004080703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 106626070 1250 106624820 106624829
    0xa0506030f010f060504050106080c0708070f020d0f020f060309120c01141003150b130c0201090c14130c02070501050f040510090504050f010303020d050d0b03030426070305030708070f0c 82
    0x2a02c0d0b00b0100700c1c501d402c0c440d16005049d1341c01c0c030170080d14103410040f5441c4100f01c0c6c0241400c0e000305440003800301d411801c1d8038056015001d040c0325400d505040061807001c0c0c604030310805d08515040b140d820003009a0b03005a28850060036015204550503001c0d07040740303549640300e6680b8104800d265004a03000c60003400c80e0bc686030300807402c5007042802c040c02ca05022407801c1c02c100060026890f00c0d403129144400c00340001504070560300d400c03405010001c20241030710004a101144a0038840c4a047d00d00804075404116413403054450001d0f12101602100903801140c81009294014030050060210a440e0285059200e0000800d40307038030701c0b10740302c001010100240b006040a00c41c840d001003e4041c441003540c50360b07600030341d2150901e00c10810000b01203100341c802c0c032403504900d48554000b401c1c2e1f5200c90b150300360446941f07104c81040c4c58020503942600040c4c3e01c00b0030880309994000000d07500e4005a5154400c3d036903c004003ca0326165000500004213000c0e8a540e030103030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 106627320 1250 106626070 106626101
    0x305041a0c100b0111010902030a0609060b1002070501020f01061d070c0506010905060a091b0e0a0e150301060e04080406031d010f0605010905062a0f1204030302150c030a0506030f01 80
    0x4010f0744001840325541e00c01e403580d1a8904083e00026940004000c60060351010700456a501917103481c101520310740f8030700d5810900f001404c81005802098200503540280d00711040e69180c1c0d14280e0036a01c003407044114140401c0100c4034040d03204c0000c0c96000803039040c00a175590196981516144090f0701400c00300340d9801c00c0c00068941140c16400800b1880700c244401c1031104101202075507220707401c4c0180003102da42e1503000c4d29007034000c40c000c107040d04219041f8a040c010041c510344590707040900c60351a10f480810f14092500c402c0d405140c11007402410142480c900f83d0007040962080344205000c01c80034240c0c01d40074040c2140101e0007440100e149442c00c0d0014002c100c0caa00710900c1100240400d074510000e1600d40c0c4d01e510b2010300c10f000782600c007502690034619105540c4040380031710440d0040c50000d0800800072a84a03900300d139138210001c001d038941c05105131600705010f44100042400d11409420294100e40300400341c03103480d6903d0300700d1800c64010034060142c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 106628570 1250 106627320 106627331
    0x406021c080708060f0301110a082205070b0d020403140d0207150203161104020a0503010f0501020a030804020607140303010f0306050124050c03040504021b0f0a0305041a0c10 77
    0x450003114850005005040664407400c0009002d00030700c40040100c2c4c0106900514589240d41c00d4004101d0712024404c450303500e022000c0e000b00483d20407510030034030390440c2c1d01101c21610808013840d1945d40020190410380c0c20320402c018a50701c03042c040c01e07001c0d400703020220100e501021102d0f8850401001080302d0b8051a1010b07091441c1a4001403484251034040c040c01d81d00030084456003840a400100304184a14041d01e1400309410465080351000c101d00380080c0e00400114103039201404802021955240126603030161100010300054810300400c006060490107005c0031807058200314107200e8141c10103840e6410980c049551039041d00700800510500d40b28450260540307820001208131444051b680c00f4280451031400c111001070401d03c0b100c4140b069401409000348195070b070301c00f00164040515210030017180d440c0034260404550080004206000c0b40c4d1645860f070401d85400c0d0440244505a062914420f004110050490790144100a500d4055410008a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 106629820 1250 106628570 106628593
    0xb04030b040f03032901260106181d06030f0a110103020c03120a020a030f11030105061e0f07020f0103200a031d060f0702060c04030809010c12080108240406020c030f040602 76
    0x41441c61f18001c54001c414101c0c009903103400c0207181c9054440303a050440084141082d50004052250f00641e50018185131040031424001410346c00395004404990b84005010a52901c80011110040141c00b042040710f01d40e5002e50060110f50300a0425a41000d0100e001304a0b8120116980500f0b17560026110704040d0b01032181e0782c00085140f10801c158005aa401c0009100c113000c0c241c410240490aa04800e065000400b1214850202591207035042c11300245960442c040482c420f00003180c00c0c042a52180c8203408a44000c0c0382700300c540039600311032070000d9800080118205500c80c9581d4a002d41c0603140031080030350820043c5598a003408030a842d80d24040d090300d086420020520459800e0b03c401e4400b581d810003651036503140c1c12401030360343c4811003000030203840720724500958075500200c240b4120707000c1d1002e072000c089201014240d420f6030804e000000108100100300422015070191203211149011246000c841811140d8540c125601100040c0d000d12020304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 106631070 1250 106629820 106629827
    0x40303060b040f120f14030405042307120209030a0f060f1e050721051503030a0f080901090b100f0803070f030807120f02130b04030b040f03032901 65
    0x30081511290407800c160520100001c002118483c00c060700c42051040b105005402d8016001d0360381c4051240300322038549a0040c0c03260091305c1128455440c1401c240c40c11071004404410144024074a41d901c5d55840c1810f640d4003d0b41070784c10490950900080c901038404100e818101401225a6002c2c09110315016003500c102605a142c454244500a640c50403c46100340324048496000b00d4590b440b800202c820315564004207100c0700d00041030f280900d0840c5d2005d4003509140c140e90100025550030306540c0d01c1111540380004107036075400008a032040d0319072a040000e060003c039846a441c0c40d00d81040b04151001108000100c03000c01c6164480c0d4000340090140c0c2d23010b5810700c4195102c100a005020b40090280440c0d40f000540c03079032180c0401020b01603240410002c0201d010701d144000d40000c00018504952040003050b502e00c03a2042e1011243e100c00d49014a81c2d941ea1400d0329040103010172007e0544075414841c0c0304880807580f649410240217400060b920f40d90004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 106632320 1250 106631070 106631081
    0x70c050a0501020303040f05100507081e040b0c070302010e030406031b081504020d02120a02090109050330070807080d06120b0a020a051204050a0b1f1e08060708040303 74
    0x29881103030840360800c601c1c0d8020040c2c9501641149400c11400081c0c14034500b4001b554a0b000030251802c4100300d071036600191000d00840c001441c100d070040c3d20041000b00301b001a48c0140108001e000010003104806005200c00c07403181c0b0000c0742407258402d94520710b811540040c0007081d02e07001c00a50601c4140c0201c14011840d1034031400d503003404814610a070890f0b170090f0340070310380004a82c5061140380c4c04a921540c4512410701c03071480c0440c0b00000942010054900003288043e0010b001d240005030f003c440a2210701c0c209901f00c007012072a000d4000c00c0d011200710b40050128a02283c1d03180c000d80002c602500d91141c0d5680c04c0c9106a04a07440c5070003585450a55640d40c9011038000c20140d584442d80c2d250050f507038507107454181c4103030145106480812640500b00010450301281903516540302d00002001c6d92264000b80c0020000d540724281a240100010004080e86100c0d102c2e10050f00444035007055124020340c0c5c1465030031120140170940f40381c1407200701a07062048 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 106633570 1250 106632320 106632329
    0x809010314190e07150f1e0e030c06040b0910090807080a050c010801060507020405100f081506060307050a0c0f021315140307050f130903200601060c0803090f030d02070c 75
    0x10700782c02820580c1006694191360128000c004002800c03c514502552048850b0607164400f40885644080300070010000d90416034002c2c052b035072024a403400c2110035201a150070007400c600300f50b140005d1010041007400d140042162100b0001010f04041c0400809803841101400112449080c1685449015030f0300604121100d001006000e42c04000c0c1c480c8564100c0300032a143d01d41c004d001c28000f005400410082021190001d004174002801740d16900c4003015060b1581c2d104010447e290204565520110b0300c20488410400c0c030400440078400e2140c40c5a1440c1096034000c9a00e070f000441006902940c2c0720030324000b1040ca18245d000602101e20075010140103000400c3e1200e030244900c501841d51410040380982c0c50001524204c4045c1001304015281804c5c01030182e10420f4103480c01c1d912841349181d071028041507080c107880481e141c1c4030418041c0d42d81c0980950004240ca0854050320540d01b424480510007032040b13522000f40903844500a042896056140340e20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 106634820 1250 106633570 106633573
    0x6080706090512070e1603060905010302091317070b06030f060c040b09030f0102072427110a080d0e0603100b030c070c120c05060702030a0809010314190e 68
    0x2004203580c0001840c056500950301010b4070400020f140c0e1400059810141c11120300504000e0491915050000c40541658082c08040d90700c42407101142e1080c00003a4003e028140003d9400d180507107450107081c440d22010000503002c0c0083c0d120398010000403500c88400c4002d100407032808018001c04100c503000601010b04004045264a02c01c51081e151122400700700000d10382d80600000341840c0b00280255941c0d00380c0c3c54401c030644103990b4400c02640c02c03405443e003010114803615584d40c2820f044a54802908075024051300103020040301c030708107a003584c0750003901c1c5c4501010062203184000e01c552115041e020702000c0c04541c20900400041c41041490105804840e0444028038000c594944801103450024851094080c0000078130700000541e0040e40c1084000d654010781550515a855008000981c8100300340a98980e1142124501007403002d07006008030a0141000a8585004407000030503281c1250071411601c4500c20659680045001d0301414160600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 106636070 1250 106634820 106634833
    0x3030c0b07081e070c0804080f190507090b040b041505130c080f070c0b1e1605031603022712011b080403090902030114010f02030a0f0e030a060912030608 68
    0x828003420703c2109825055036002c02e02c0464201c0340141c0300003c0d0290401c24050b038640d210014030780d507042404100c544a101d2003041c0a01da40401400b48081680840a003c94600c3e20045402401c420041694400da031201c0b00005e81e603607841101d50758049058108203640c5800704103c18a90074031a07400b41281004001c0d0f200c20342c0210707501d501c00760140c5803044070388520030202d843d1024010300901c035100910510080f4604000d41c5034180800100396181a603d841984c0c6015510144200108006001251240510303030716503c0003ca031031500500308017010919011322a00c4070894081c0503100c00c940c0c00142040c03040d041c0d1038281031009000350019860041c6401d0019082c550130440d143d40801e00701440b4070340e410024290720601f5522941c581c2c00758200360240c103c0281c04100c0040303e0030403107400402a1441c421850301c1e0b02c12501c1900c54192031000e09803c072550700d401507000c1e942c00036816119041100c0e01400350406c28000007640582100c206800c042c03500d0f4080e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 106637320 1250 106636070 106636081
    0x1101030b03281a040804090b0a180209030c061b060f010e010312030b030109200d08092701091d010501150507060902122508060403032403030c0b0708 66
    0x1c80c0c280154245182d552000c405503800c2001c01c07000d0840c280e250021220041c4014000300700090070503241d446030300f0080c003101c280800001e854140308003070309d0803c000d41031070000031030b640a05803000010301a107442e41c041d000000d8181d840114a41e0356035a42c5140268900000c001d060340c0300703e401251404c5075051180200c1d00314414032000b072641e047c052861040c10710940040110900180084c400c04c40c1a181912a03500784410351a20bc0110818080551620210300340d1181d800c0040d4902c0c00681d0801d000c7c9031100560460000c0c514107514420140034040414006d10760300e80001030085c0e008508110610074081e000c1ca603a070411005100740c40c0003050302d610f00d04003130515030350301d144a2030a08040e1541420183d8400703a0516100c20b100c00125810f4410041c03003221000c1c40c21802c17a0b200e00055507000b01034095020f13400140c0041d000380c0c0185283d0f49a0201074400e56045c2122035180300603074204a00003000d1140141c01c100d204a0120f070444201e08080303001d403510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 106638570 1250 106637320 106637353
    0xc02010902061b070b0c03040e0a0203040b0103060e070302090a0606030b0a06090501080a090515011403010204120803070908060c13090212040f1110030b030606010c0210080403030213031101030b03 87
    0x1040c08110803c5201c0e0301218851000f00040300045c41a0240c46403030751030000d04151603803c18410059000203220000310050141c0c070031244100d03448402c54106900390303110500100016954040d047c425004d000c405070380c4424a551180503140300114403181090300040c26074808200c0e540c002c3c0c058003024002580c20001510a4a1782860b110361141d449030490406041403d0015005001c0c500c40600911f003224541b9060743c40c0c101c4540c1c8101a480309050803442503100e072044581d01083c0c00b000043e1040000c640014042c0742c030300340003521201c40038102101075800406a00c0005100340390030003034540360b03001040030340c0085041c0000c1408010303a40744010301c0103001108410350b9500b0024030b260010728864000d8118444851640c0c4060700800103a0741c82c0f8464410b40000644542c0315040440006a0140c0780282140407400244c545420203041101456024800a803410110410307860043d0b0050301071b10080303a240720014085940551200e4000d420110141c0301d44983c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 106639820 1250 106638570 106638577
    0x6040303090b03061c1208060f0604060813050105100f050d03200f010f02040e09012a110111190f05040b1608040905061c11040507032a030c0201090206 67
    0x141484141ea8030b03600c11300040c964060400d68030480c0700d070002c2c41c1000c0c010034080c01c01c91b070215602e0310700c0315440b00420400750032201c0d00c140798002820041401000c5c46668025003200e007592040800d600c55a03900c50039185c0440e03400e072448003011010010100e01c2d10340c490080505546400e1501c0711a01c0c0200b520404824103d00101c00340050941a10700700041005961080b00070440d1344000152100654003520030394070040d035035001013060040b041c859082103c0c1c00384191b640e0401d107110f124906000240c030003400d003c2910001c4086080a000755901110340b2661141d13103034450310040d005074541e00c0c011002c101a6044400358507070800700b00c50558490450a41d00d03000d80c0d0034001416003101c000201900b1000c900040c1400440d000140a004c04456406104c2038152a04d40c48a01081e406055a9030010051895081036030003550445280e18003c615051041c0042440c6803280c0c4040710b81210808030400965850f00c03940c0c411113a548003d00282d0302c250005a0f140c007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 106641070 1250 106639820 106639829
    0x12090303040e0618010603050910110403030c08040b0708070327050105092407031412010605030a0f0e0f06160203030a0e0316030e030c0105040302220f15090b0604030309 75
    0x1128200411102d40d18000800d400103100346813040b2540e16450000c0151105940b1200036100307245044200c2a054060000105804000d0740e040c140355480c1290074802402c800c0c2c985000410010402801400007007000500944045568040d98078000385104100c000d00055142c0c1c010180c501c0305c2c01c25009501310752007407070500d49980c0d85600081c1c2c07816a00c1031980e42c07079007864181581d09d0320075005091228081d032030b60340c60214803104441d164407841000026400c020b03030051000d68020409160810788417800011150b5035182104203c40c500c105901c00c5500c40a202414820100b117460380c82003144056103400490000080d54070700000d8650750040e92a0811449000c204100392180c0c49001c2810540c000c102e82400b904080d4290080b500038040c60301104400d50042089608490b40136080c80d410440a0790017400f11000f10080150705a01d0389100303c12440e0b0b9005130122425004100a141803504c2540c4046075807140c02c0c4d900034075003404100301190f00b0541110807139 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 106642320 1250 106641070 106641089
    0x60e030316080f13030c09060b03160c020607060f0e03090d080f090a0e0901050c040f060c1a0a02040807090b03031b12070f050f070b1602010903140105091209030304 73
    0x5040510340078082c1d004030440503003890800310f8058003001003458003078100d900924045c0403281d26803010106031001c4d4001c0041c014001c00200e009038075009104ca036111418a40214200c901d0f1340064640d40c0841003c2c0c52098948120b803516a25900c50103e2910042009600e0031041034040f955075074024801511054000c5071031204641040d0481d411040f00401c182c515607180e0340c01c0100710100b5200401150310303080000c0c3c0c9001076141198152800c89040700249072070301c030080310440407200048410400011b040054a40e10844660042420520150711a130901c080c0902d402007641c801072403039092561599950302c3c044222040720700502440e042d5069440c00c9180b070400d00305074441c090039000820b42c00703000030b1030009a10f0b10f01c20000c0d2004180007241c010781c0c40c0c0250003120706590040004014503440900111141403040c140302116036a65181c1c1643c80c01503041c041c500b0f075100d23010016028001d00c440306410140e40c039014102105480401c0d0744e8004c6001c0e01800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 106643570 1250 106642320 106642357
    0x4060f060c0804050405010f0618080a080f1b06090f060f0a05180f0309090a090b010e0a0609051504060803070b2202041817071a10050d08070507060e0303 68
    0x18840440c2c12200070b0722010f007041c0541d580d01c240724200c4064510600000802000d9030f4440c0345d18142c0443d04070b0b1480b00003441d00031181c0e29110059400f060707401d040c4100030400d10603c0387c0706030b0020850720b0542c0e0140c0707198a0300d0182141400e1484614686d5500401c042003200c0490b061601d400100300d0500045070b40d80d09603078141c03180d29001c5441e120b115140d200014244000000d0480b0007081e2000000b0303071503450a03103040d0b949401008118018090041c04203180d141d40c0c080d8804d10096002ca50140d071420001c04884055403074a255403080030409466043c180179000080c09002e004515000c4251564105a03001504e03010080c4401243c001c400c4d03801003050300b1080d030001d000b0800012560000c0315920100c6100b21079807181d208101240c010450140c50b40250000011400340c525940140309034140100021200c5da4072440201d042c0e211181030031605481944400d654003094280036180c12032980c008010021841003209081d1400f10548100e000c00d072051070304 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 106644820 1250 106643570 106643573
    0x1020607020f2d07080706170702030a03050403050904060308040503010c0e010c1b050603070302030609060f1003270b01030b09010c0e0f28051305041101140702030a03050d0b04060f060c 82
    0x20101c03a0081807603540d1213450004580034001141c502c00315100d90322030107200c4600ca400c0b000d04a500f200c8800160b0401e0110b4444c0500a03000268854400e107443c91905c000c1600041c111401c5070804eaa004c44049001c0c001030401344140a101c103202d0401e070b811810940002000c0540f000c8009003200d8031a800c2104242e419804140a05801032582d504da190803c0001c000f0b40045a4680c0300d1484040495810b0038000204503007080d0140c01805101d0344028150003405202c000d00c2c00da02c07140c000520300001c9039506015854817480000c140c40d450b5090541c66220050114485070345071140707031b604031600f00d02184036030f0205482105d03076141007000003448004c506a401d113000310002d01030007420188510380416941c4c1203640780c01002d0005503280841e8003c403030080c030090342e10983c00100d601607409120118034446500c1c0c50714801e90b010a01781903100d0381c03c8021400c0481c00c401e0760301c1d00e4051144403c0055404100841c42c00b100a00d0102e132a1144005100b100d000000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 106646070 1250 106644820 106644883
    0x5060405010e13060e0d1d0a080c012a0f0b010f120b09010f0e0c01030f050f06060702060409020c070f0b070f11010201020c1b0a1a070204021602030f01060501020607020f 75
    0x100f01907054410703121010140300014043d03c0c002441e071420842d24900401c454580401000c095809e039000515403001c00c04010758036418000c06810060103241d28400210301c812501e541c81c68441d40348011020201c4c078010315034410607001001c2598039074400703000d040d8800ca015800b06811081801c090303113854411a00402030401200919400c260404045240004000c21919005ea034104020b140c1701d104402180d90030340d4a00071032552003010400702c1c600003000c0c240d02d60000b4203803843e01d81d0750401d0030100e0380045596503054021f00c40030804032502c500c20708020003210350203038901201c80d070f07030141051041503008207034908440c88075417103901c01d505442051080c1c10844100e00301c12072200320500040800c0e01d20a0003140d401003072903420103810380258400c00c11054206402c941c00c00c0301070f411101c42056000c0500e9041405170303400b00800d003031200d0f00100008180303042400090400000a00240075075002001d8400800000558803920f05005d40405074004014034010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 106647320 1250 106646070 106646081
    0x10806270a030801030b0c160f0614040c0e010f030203030702190f0914280504020409060f0f20040504110d0501080304150212090112060305010203010b070605060405010e1306 77
    0x600c11441200d29240c201500b096405040c0d1b405100401e00aa0b92140b00314020f1003402c403032580006001c80f15000040e0910010798055207d082c0c0429100841d03101c5100305503003103c060b2100c80b000ca10030488004071950b0b0031301400c2d040b52558541800c50b0042a600c0c800e40304001d008015442440b01070890150000015250b07030642d2803442541c0c1d0380100e024200b100b403d1000031400d940491482c0526420104000d003a42003803603501c8202102c00c40c0102802072059801039220104000058070714403d940d4510030080340002d8500c007000224086404409450780d01940c47c1401d031084070040c800351811a082224007007044580c0185012050003103602c0c03001141d051500100f82d40c5070100c0640166510422040403426882104036030b50011480f844a01150410a03005d8551154100b049214000040403540a6481d5681070032030f4400d0b4000c544066010441c4010465240911b94100d0000c072414046541050f10750f0068800183c03004070003411600c100010010140c101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 106648570 1250 106647320 106647391
    0xf1302060415020f070f0e0703110307030c02150705031303030908160b07020304050a03230a0305180a05030c01030903020f010c090608012903071803060b04060806010806 75
    0x4a440d5551001040b1006020601210150040d41100556900000340b04400c603001e48082030400c3d45403000e003124103030015010008050325044960b040e0340103000110301414555500040c10240c05200904240d00f0040300e4079a200c02c0b90a003e549684107054a81040400310003804511392403405400030020100c00a00d1098040340f555612102e01011502007801540240d1440c3c0d500c000403600c80c0305501455501c110194000d0010801c02e03051010304440490b00b68a84a501e00340c020301d400c9228108600207800060f458580c4840004011580e0200383c800100c028104030009448160801c2d85030304141c1e0301c24400b81858400c102c80b01050604d900200000442c0712001000180f03180960404642c00c0c0c0d000048081d00d0a10754400a41c0c0f07a0500c0f01c601100c615030154950001d03110b0405c0100014241c0d421040354882900110b01ca81800100001003000340130070741c0c2143e8481e00c1e850300240010400507130045001c55228446031111608a855042c90011301c000340282e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 106649820 1250 106648570 106648579
    0x80a0c0c030609020f01020f060a2c0d0201060f05010e04020d1409060109050f070f140409060806100501030c0f03020a050d0e0a11030d0c02010e040204030b0906010f0501080402090f1302 82
    0x40000501a50b0383c807551201e40243c0d82c031466120201c005991f91a804900300c0030300e17404000028107903035003036101488100200d0618151302501360f0209110820201240c0354a0b0081c030f0b0200b19841d02407041d40014801c2e2440d0a07441c905c3c20b40040c002007200c0340340c14020703500003c44560b80c00c60b60b400104c403003422401c0891a42001d1003102da0344c103130034010500030a02d0400030507000c0c1e00304008148a10000e9442c05200070260070101c43c807143c9185000c0401c1030034480400c108a117406414050001c1e81b0042090b0300d405c0948012040c10b40d0711280c18180b0300b0310701500707043d4018050380241200b0b08025964000c00f200446140c8540360304001260715207142004403000210b100c2803103c1c09008850a0034029904040d04c800030182c0b00ca020400031304c070600c015405034900d41400c071002400142407507500c0c0c0300c803001004100d0b070380704da990440e400500c095016003035050050002841d203803d4901e4503a0201d0b288032805084507950609590001d5008640d030001052180c5d030180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 106651070 1250 106649820 106649843
    0x15060906010504062115090c031404200909010c0224010e090304051c02132901030e0607080412020f030306040905010b10021617030307080403020312010609090615020a080a0c 77
    0x1b48002018211402400741180c1080d8214094074400d01860400b00708040918141d0746a5645412030206100c070341c0848085c0f0102c01501d607580c0c1d40d80e03407072081e5804000490801c161010090405c0c11040c0c2e100664580c0b480307101e9180034200f04690640b10100200341080c0c1b81c1d031403042d1841c001c9920080e44406443c0a0b981c0b1610041015002c0c60f2003038945900360088040c0d058240e0343e485c20700d0711540c0808005802102c414010a411030030043c1400a40350108040380c3e810018219100d40c0803d040e0414402044101005841841400d1000d0602a2003e800c940d46078400a4600d501c90780c0c5480c00c640074800b0a40c060b11031604010800d0303011804448000e510b0f48010f000e0400d0040c02e038800050000b800171018400740ba07141c0051480c5a80703000b415509404003610613011031000b44000f072001d0100c2d0040901910b030f0b45c0c4481140d9480c0000c480141c50058021004901c2e1100000d004944c00181c00001c503030744000c0b11034035044021411101a528400094903008050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 106652320 1250 106651070 106651091
    0xf0a031119050a110105091003051e040507050a1505070605070e060c0607140702090c030a1803031406040e1506031006060914090610110115030302150609060105040621 74
    0xf442100f01803080d284009420b01c3d00c401540c940c001d84401603004004080303103151261107580031035401041c8241c02d10315280c400c0014034140d44110303000c690981c090001808a40350803180302c8000d0184d9010246460003c0d03600600c2401040380041c4010385407404592042c1c0a2101d01c00b00781809005c0d1900c2e119030f10082e95440380141c9030240070030100908024080000d10895030050f4001c0c05833240c3e9107440d280040c20790300051448100aa480e040446509030300d64070318680078001c0d9004503c0c4040100240c26900703020b00201e101d1850300018189015010409038103900007a2802d148994412000ca4240b0304800345c0c0551180c50400b01007135150308192403100340e5914a1021100000e62410301c901e540003070b03484a84c4003600146c0000010704c180c080104103880080045802101c0a548581e680050381044001d0307000031a42c603100c1e550b4031040f00c0d4403078012500d0001d0ba041020028086101e140512420824003480007015019500385402590300a040308100c42c5801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 106653570 1250 106652320 106652323
    0x403060e100606020d020a03110c040c0518091b030402010314070c050c030d0509061e0301030308010302040b040504030e0409020f030a08070b010e01080606130902032b020f0a03111905 81
    0x1010405070402d107002004501e0710701c001020800049103070010310441001c0e45003502c3c030a0142050340c03520f216810700c2512070f071128001e8010000054840648030401404029602900948060300a4005008000c1c114001d054604ad943d42a0300c0310566035202d600040303014080444509420f020350308280082d580d48050030202c06030007002983c030043d01400825846104081c062000688140007a11107450080c1c01842c00d055907014400000301a5000c94195400903803059021035900e40c010015800d00307001c0d00c060280115000c00942c9407d40d00035108600425042d806650303200703000350440d21000030181d1b006000400311524000a440e000c041c3ea41301000481d03a05042000018a20b8030285040d03058408100241030203945407003d00032004040400500c80340d840d2601440035803024008940c5682c00f4500e15200d071804000c8214941ea400d1072450700315031065555880e00d0030302080d460314603649072138030340b0240800070003d500d00303568222810b031f0300300503c2e140d103080000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 106654676 1106 106653570 106653583
    0x1104050f1c050303100503191b0801060f05010e0108040b0c091f020a0203010b030a0803010314150a050403080a05070219140d05180f060403170403060e 67
    0x500818608150035004001d032035942001050090b85e40c441100e8030013802050b070081000c0100002100980c0304400c1c0050031a11143d28100312040c04901044000d045000c000d016854607050700a45146030b501c1114040342d0360307181c481c65a5000d0404a80f0980e0441c4002e020b5603583e00180b0703407a0b4400700f4515449030300c4a41034604082541d1900503140c1183d402411003007094414982100c1041c00d00e90322175884001d40d400000c3d0800304507810340e507000d12900b1548540040303151410f0f60300e0309080383c8407090508201000c010740d80a540720301d000380da0345007040d1a8440b0510480758240e480700b0050304100c2000b001841c80c464460701440c403417400004c4440340f9034540c5040152840c0783c0c3d400503c001981629120030202400c807040c008848003c6043c03a03c1d40040c00782d01c140c1c88000c284c1039041911808019840c2d0550f8010758200f00d05010202da0b6503102c070344506 = true := by decide +kernel

theorem cover : BRFrame.Cov 106474820 106654676 := by
  have h0 := BRFrame.cov_init 106474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 106474820 ≤ n) (h2 : n < 106654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
