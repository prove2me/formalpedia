-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5419
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:48:34.974601+00:00
-- url     : https://prove2.me/submissions/46e40f02-81fb-4db8-b143-931d2a7d2068

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 974460431 ≤ n < 974640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 974461681 1250 974460431 974460433
    0x1109030a0b0c04031208160203160201080703180501020d1404050706050d0e16091b1d0609030703051c03060e1f09150e0714030112021309081b030c 65
    0xe084941d03550001a401030080b00303442500b448000000f541c902030800d01714201d1340e504035103401c01020040f4124155204c502c19504180420366040c0c070707029410300580d40c0910342032250743c44480d010b03801030042c11384a401c2125030764024418000150018a07030030f8036143c0d080144421884042d00c020344181c0d07000345550000e120400c120f61180d806400f240404101c00038040d034068280d030380b408104181c01105c82c9507500d010802d103100c0c2d108122040c940c0301c01d02d01009864100042c00d444007010300700903440030501044642c1d10f407039040d5840040b0140072120139584074200150f81c0e28003909408250764183c0710120701c86d8407a001e108201d44c08205030b01e680d5200d02440304200c0c44036581a5444000105001500700524040c1d059048210800040749030300b07081c81c071410303400014980c605000c00780f00540c0c80702182c0b20071a030455504c0752074002182110f100042030000042c002003d01801d10f0301a406100042000b404014000c07001079408014082c505900c0e40030f44050400302d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 974462931 1250 974461681 974461693
    0x8191e02041d04050d031119020a0b010b03090c06030c070606180e0106030b0606071b06050a0201060801020309030316050702090403080618061e011e0201201c0f090222110903 77
    0x30140c041e41000760f640c1c500d071540e0b81c03c0c00194601550707501d5008d580600182d03c01000303a41400003081c4000d0150800d80d0300580386241640c1207a0341c0d50001c07200c81d80124000000100c2070151081540c50030350f0702c45001c0c13158540c0c600307420a03c040ca8440a0442c5860560701e15800380c81441010304507540301c818203a150381c405080151a8101550a444980910304d810080c2074110001101030009903c40710b80f25003580c50020b007164000d40100c801c1c0e82c810810b00c64201350020540c4d84c03202a400b001c6180f422240c0044585000d14a40290484210002e08c4101034000c0007403031243c1342c00d030303980194954040c10010b00072205503101c0f900090410348504580115007000821100103040c0b504580282c0711304103000300807603620b13000141d65446c070124402064281182000ad044500380e810001c0c0d440b5800c048005480d00882c0f43d507600d0b0740310460349005400c0401d42c42d800410800800400301403000f0100c20103040300400da0f01d0607500103144a459803d8840c6c4850103002024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 974464181 1250 974462931 974462953
    0x30c0a030b16032315044d09030a0b01090b120a02090c1312050a0c060f05030f0a0e1b0102060c252d0203060f01050108191e02041d0405 60
    0x82040c00140c454803007031000c4070007001552160300412040c254009081072141c4447c0e00420303003045140440c02a10102c070850720304600350441610f00c0b2140c41c0c05a980c0d03580c2c1c8000c0060302e4416032007002040040100d0000541c2119984594006803090b152042d5170a8480045500c48000170070003035124100d04d02056038503184034090911607105007903004180c5d46a050382a40c240990304203d40981c4418041400c02c40392140a0b00200b20606000010800700c034005051400001d00c681d45c0c84204600040860045412800c6c0c0b01c5000c00039907030342c0c1c580710100841c901d01c00d15486003d48104000b0501c42e0021204882200310031008046129000500d04217140054280c1615038010214880c03250560040c014100141081c0d61141c3d00502c510526007404001007072011070245120042125982040017139500542002d07403400e219180030100e00041c201c60300d407030020044015281c0702e500010344c020002e841700210600200c5041511080b050304046900403e81d0b0051140c0d00b03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 974465431 1250 974464181 974464241
    0x629030f060a180603061b05030114031006031118060a0306020708090339090408070215041d0105090c07120203040306020d05070e030a08031302030c0a030b1603 71
    0x941080c001000c0d0401a40e41d4000f42d14a01000603501c0001942d401c020000c11007207106229885050910034803210580b22000340c401d000504c02c202c0541c42e440707030240c0259814445103d10060300c2000700310040d1242440c10400b00c41401081c01810300f4541d100000c0c0402c9001c034480e03140105400f103101e0455540e07030041c1d00140c600315680c130340501501d1542d82d018070008400d0000034059001030030301d01066441d030309885440d0060a044110042c4c206840d890340c072a500c5500608515552003540c40800c2c8050910b040c0079512290220b804240300001302c03100310041c010507125038a1a41c0f100e041140e002401d5810103c065810828400080c5200c440074490440500550341065580d0f264007059038001c88000a10940d1801003010041e00705943e000c1030b60047d8010305c03074543c0b06da58004e010320024080707404400106160303104565040041316000c0034090b080740b07031059072442c01940d595420798004001000f8a040e10842920034820282d08991b240451020000e401c0209 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 974466681 1250 974465431 974465461
    0x501051507080706060905040c0e0114091e0906060406050a1d09100905010902040e2a060405040f06090c0c0c090b012d091205070b160b0a062903 64
    0x21140d0031810300042000c644135200c1c1d00c0052504c8103021589103401e19118244102c40d41088081106403070050100011001f120083c1110980c0c08503026180c40c04a0020240040a2003864031501c2003000341160001c00c500f4003841c0281c80c280708064a50040042c510224040c0c44041219904c0c0d02405580030040e4a403c40100801d40750071604001d60324065946880040e01c0c0d0707139152100c0d842181002d12130480c1e1402000d0180209007603885c0d003002d0070284903021001d960f00b000703550150f56403200d08641c02070070000d0041062081e040032542c098600d9114005009144c420081d81c40c500444a03c00d50a902100ea001085d00b03040343c00c8020b09159440d40e040000205175010b0032022135241d40140c81c1d0320031072120365580c03d510050800f5282d80000401c00c00f0820f8420018000042e4102516420310416440d089408420b00341104c900e44082c004444800510042c610554490401d071703001e0700c0000380743d450340b00c0e040c0c2e010002c040e0440070040c1041002036080c031410490 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 974467931 1250 974466681 974466683
    0xe210a020409030e18270606150409140f0903040608040b09150a140601030b060904360c09230603120a030c08090703050304030206071106180102010b040501051507 72
    0x1112411000c90740c0400e094480c85d52000305d14084103018001c005544260b5000520f040c01c0301d20083c8540e5000241d00c4080180580f40100d91901904006002c00c4068901030015080e08003e0440e0f18902850001402d0700c1030700c0304d040c10501168001c00003100f250103a80d8141c0302c41c00c083d00d071a034a00c0201e11004040070003a0141510890100d5500050b1700c0c02150300302c00c0070466a23801c0c10903141c084405041030f41030504d40043c2e40d40c69214507040d11400c04007110700084462210400003050300d40c41c1001d5207908507840942c4104156849520750307590183e241d1540c2e440e04c60301404129004060070f00080441c0030940170742d4107a03d0706e07001d80c0700304041d041d9183c2c6124140895659002441c4503008283c580c0c060b21000d0ba407003250298400300070402050614038544500d501d174841ca000103409510b0001e00c60060103070780e000546900c40c0103814155150380610600803450081e01c4650b0042d4204000c944242c5414060181a1500248501076080020640f00c0e015401240 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 974469181 1250 974467931 974467937
    0x91a0909100906061d04060e0a020c070f1707060305041523160e090402060a14190503010504140402090a0b131404170a0807031a100e210a02040903 65
    0xa0100d03802c003440c02048020b120039243c407568449114115214400090203290181385400420003040701d40c2d038101500614610401039841d408054264281411a080340700c0c80a0042c0c00050110075080c855040c03900d0450030f58503031644655044090340c0c401e4a000d41f071414680c0d847e08100321036605c41a00c004420fa1242c1c0038a0703a0340842c5450030401c0307d0404a00100b20311004034190071400134041800212080902840c1c01c5e800613006000700e110079820420305054412100c0c04032070490341445801014400ca01c29400d20046c02da5100b4003c00e8080e60400401c42003c01180e042240155401000492241d440e040384000a06c56144603e510203601c0d00303070b203800420510a80819139400c180944c550701d41400e05188125100e0709159100d03104021540320b0702e41c4140705070b070800b80391303d408115961014030003c0da42e082421800c1d0310208400c0c04001d025006111390428010036215504402c0b00100804e50708080301d422851181c0060200400528180c2d00071202c052080c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 974470431 1250 974469181 974469211
    0x12010f150617090d0e011b060f0b0604060503040b060a050a03051c030606200c18060312090913050705090c030708010b040b090f0411190e0301020a170901060e0703020a091a0909 78
    0x351f992001b40750285040e00d0340c60b640c003141070300c0c4c482030700500d9007009095032038134039040c5070985c02842c0d44001040a89400b1a42d004900d10ba600e03262101c0c0240001441c010000d03440c0d09040762150800d10040e0000b1000045986030140a409410102d0380c42e51121004828034284043c91044200c048a203180600211100300c0c0d9a600030350701c09100524030054061a050040c14900358010005500b580010702502040e6940d4071402640003a080400391540344841c40d08628100342d5410050303205005c40704111500e48848055840340d8a560341c0c2943d5030340d841c90304116500c5503014a0701c100c0c034104004281403c0c01a69010300340d001500c0002c900d5194041680e060f0002690810050030003524110800e6004180c480303100c00131802140341120325400908a8075401503906004580c10002544642d001c1d0700480090203c40c6c12944c02e4502440300400a601280d40c1030b02048014001107480900d800c81d07445c0380280107280d1403815002c3c1e010410701590080c9600c2c1b00e2013201e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 974471681 1250 974470431 974470457
    0x7050310050a060e03070b070b01120309090c030504120f020607030b0303300703060e1b0c010504031806180603050c0c15040606090504050c12010f150617090d0e01 72
    0x118100003c250690b81e401413120000100b41c100001c0ba441141c1802090007031402244070902564110303803401c06d00d0b0144014514040c0c0304940181c0c07050341141d10742940d003244103416800c0b05115920480e40711040180b111001c0c0c075a43d04880d8441d0041c1d000d031340000c507054080c0d4400c410001006045130300744464540c10a1404074440261010700060a6542c03020038480f00a103508409642000d0014a0a00008049062005241841050000300d0381980c0803009004c88110700c25060080c44285010b05001c0c1c4640300003200c00c80c0c009a80d107000070f4110710a1402500c0d070b0700d03041444c80c000382c9403039011005828080c00044181908000380d41d006201001309684034202051202c2082c5400c2c2014411610f1030b41c4001112418034080000007a004540702420300021111181984503500700d10303004181441d014024140303898081c50400d40007040340000c8400c00d075070784800c1007a000408400070a0036101140942e00c066504803405004000281c00c450040c5890681c41442e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 974472931 1250 974471681 974471689
    0x120a0c020f1c17042f040f0b011e021b01110a1b05040b1309170f030103060b01020a0203070b0d0219050901110c0f010e040b030f0610050f090705031005 67
    0x305462100d0760701c0c2d48503100341042c2c1e0005840d05502c01145010348991070300742ca03560b031942c2054101d8280c1c01c3c450034100070030190004129a011401800810500140d8040c040040681950080c01300300350103101403c544020100000000b215030161900d141600203103140c0e42e010142c002d06101c0803c84101c0410003c00001c040d260081494100c00040454242d42d20b13942038105501850400e0a24641c40c0c8640c1400200c28041090005403890a420580030410680700c0601125900250300222611a030000e903060b07a001d10380800c4031680c03000040e681c070520345170000d4241c0c0201204204000141018012460108802500c2c1c466807139116036a419010100102042020803002e0f21035921910704000c0c0710307400e002800b103802d000c070015100404042001e8100400f11203c542a510765400285050300058125519541c940b240540c5524048503200d0510300d01c00000201d5151204c915007001c480a042c2445617129401d084400e80e000529114841c0c80c2440c0c00120398031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 974474181 1250 974472931 974472943
    0x1d030c030f061803041a090d060c0e0f04020c0a02060319020729090c0d0501060504140414010b0d151d0c130b1f020a0503040e0f0705120a0c020f 64
    0x30354000504800c2c078141410a8820301c140141c50a154030505c03040c00304904401080c3d4241c4031000380191a460703d880010140c0480c034030010b019609040030782d00641c3d0444c0000302003103000c5600501900300300302800100c0c0980c103a4208503504c00c6014402504104d4000c41d008401c00024906031443c2c0320508050340d0107080700700e881a9a005c8140d4500c808441d83d0340010301c2031a07054280e81440079016540c1c1b1600c84103a8031070b40280720400104002548104000d2070b0140c814080c01c2621041d0341030342101241e056500308100358180e40c0046c010301c500b40d10740600038171b16400000991552a00000c1748000e8407929a920400510100010500d0401d901c241c4401800942c10420600040340244650b4905c600e003064208043d640c0d0b0095440c030809000441400368080e2040124540424228080c3c410f010020700401c076403051400540c413403100140050465102d550086503180300d21041b82c00e0f26a442404644201460b800c500983d030154411165844410a006e0741450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 974475431 1250 974474181 974474203
    0xe1005040506150408070e09031602010815040603080c060c0703050d0504032132012d080703060612020d060e03130e060a080d1e120606020a0b01090501061d030c03 72
    0x6d846088200800910041c1e6264002e507050003440c1062401512881019411800207042c45900c00c001807403a00d00d000110b203481c2000788284100c5550342403041380d6078005030740a9154002d110000702d5980c1590308964443c2d030700d40e60b15032400050b503403000010b160180c021410450b25040703c6007013941c40c5a01660003001c4010004103048198850440d803e400040d58610f0740301d01040302c0e00075200000700790440c0d40c50004c2442545101124244200500604401c2d103d401c1d0710118404c1400100d900550f8850403042000300e803900710001503003000f07000080d84030034804135040c0000c1c1580c201c01c54902c640e03022030b410411801c41868140200d600300b031026000000c2000860700d425900100100341900241c9841c000748a4001c021300481c444a40c1d5059000544003241031003140400c508220b070000c20004903846d044000e4443c20a14000d6445941040c00400c2c03c1c9903c0c42414100c49417601d0301d031400c080c0c803000303201c144038615091503140c0078450241d6602c0e141072010203080303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 974476681 1250 974475431 974475433
    0x718090f0e0625030905150907030c080319031a130209090f060603070f05041e03050607020105090d030f02040815060901060311090d060e0a12090e1005040506150408 73
    0x14000781140c51618100074210507550400903540306110b50301100d118401d40c1585004035903241c2d1410220700c0d04a10525840d000520042044803040703010640c842030702e01c540400350031959185c020b00e640e802401003201c8801200c0c0303032600d51740d8020b41c818902c0c04a280002030100400702c0001b9864601400590310f20754001940c5040380c603180340810b5010081062507000c0f0304152000c03400314000201a43c0c1803000c2c0040d44801c26000f00140e80c0185400d10900d06150a01d1004800d01090752104680c0344c0700b920086518280103000f5280706410010042001a400c0101103003d04140341c0c0001d100b0f5401c110105907200c0070b00c8010084c0000424070000e60515805225074818141d02c4081054984014000e1003d001d0f02107803043c1d4001c03524103007405907034205800100b42152060100d4803682c2c10000400510b84d9414007505502d40380d22018a41c1e80a004600800031181400c07404240d1405104502d0241d00c103942140c800f5060a1002c2400031032541940d015030084413003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 974477931 1250 974476681 974476691
    0x90c040e2a040c03020c10020f0d110d0e15061c140c01020c100e19050612040516030506061201061a09091b070f03030e0a15050f060102060718090f 65
    0x1900b050f005510020205140c01c40c94007104c480e603192202d2605c003071207801070703000500c031065030b007012090300c00c4480250304c10460b503050213602c0b01e030780e03400300c5240000c00d0b0602064840440c00401c0c2020b810300d07154440390007991a00104001c1d10f403120742d11155001c4e0160710a001c103600707811101009089400400300e5900c003e001a180030704c812a00b07482883c2900c082c141e42039100c0300314003019038242c03034044c807904180c061416150410b40207640c006a010850141c00d80401064600441c0207905881d2360444d00400303443c245070a80406031559101002040c05420025914070315040e64900000380d0540764501114100e61001c0c2c141031452003c10b04140c149006c40c0c0c0107800c8101d2603c10801c0c4a00c65000804030300072200e01803d1409854812803e040c0260030901c80e020b401d105032010007404e45412039800c5140c20050070032601c0d10700080e04032402c91001230301401c0160010100390f6603000013203c1900384030f005070b03070052000703031002558841c1800b6050040080c0c99012039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 974479181 1250 974477931 974478013
    0x50406110c1b0d03020709052a0307080a05060127120c09061e15020a05100207051c0503040b040606050a06050c0c010216050f01140408031b0105090c040e 68
    0x1d41c5840110b1903841040035141c2000007030340010b900400c907186504003040a039a001600481e030800c0104c030b4075114004460503003205807500002d6110f12100d40b160742164880c0880c88040310411120203010518200c400c180d5151005800403130507040840404035241ca0b0f01c00800241c5052600f1598110148018020b0f05054000c800c081d200c040409030501100d01d914085070361003885452805408040e008421601c2130200c104019000700c215a41d00c40e009a40b10002c0d88110f00a031068050000c103c00c00c000d41050200c64040c0940e109419902d40b6100c1b540d90140292003214419643c4400140a8076030810000003407099856042d241c0c01d01004060815203075948207030454102c1d600050311641040c2d075000c25290242d5860203440100401030311a95078880c82041791080c04180040d09103c000018034400c400d0400d000d00e404078546080703007a54001d48051401d03400042040d90241860380c08661800300000841e801e04900070412034007940044415070894416a6078a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 974480431 1250 974479181 974479213
    0x30a060603021503070c03200f07090b040506030703110a090c05091017040b07142706040b031b1204050f06010803070803160201090c1d0105010806030a020103050406110c 75
    0x41c803c03c10b1501c10502d0340c03074803420082c1942034607a0300909020b82425200c1103015003c00120040700404101c4041540710a185996180d5600c1801039203400c00c00c0507562030034140142401084058010070302207055903251040045540350080d0002080dc1d0000b94400450041e00d05261454a459a035119460140100c01800d8281e907002d01c0719000030542000d200d1450345601c40d800c070741c00e001141c880d01c0c07048030610b101c4040240a41c2c0003203070080162150400b540c0403008005e90b1082042d0b41d8405001c424080e51140d4881c0b54001d00000355504850a156003094104085852500b4030390240404481c00a840c2035805501c1002c085c0b1544808106141c09880164025070030000c0710381d40c500c1e15110007041c00c100c0341d401141062185000750803500ca01c0307030300a60150b00e41d51150072010710b0310640459803910900722000043d003540264580350040d88050085e0060306140d40040d00a040040e0003103c80300e0341c910100351000c030039001400881144002074120a50440850 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 974481681 1250 974480431 974480449
    0x61210151208090d0303540303020d230a050a2c07080d0206090610030201090e04020d170d1103071e110a0308060306070c0201050d09020a05030a06060302 68
    0x10001c000d1049800c404915440c2c259029000c0c116801c4500140340d107001ca001d07200050780b022114400c15044440340400000961524038445c00d00501142280c1c20803090a8404901c1c81c1d180c140b440b075000200740b00350010070b41c142c2605008909402c1e40140100b0059420009a001708201403c0c00007500847c01640e81290b0410070910140d2084c0c80240480794075842e030880c40d102030b11001e012190f42442101c005160070010f541d50030420345030294031101d00711010f82c200d00491300010342c807080e005861004d494041c4d488450046c01c0912400c0310b600003a00599202500c42050000034811104000c45826846c1c0c4060700c461020780d0341070682c0c0440c1141204603c1c10700411920311750125001500d544031180300c6c40031020503041560301c020050f00383c42280c022500d864041c1030300140c2181c01a6801e404071450f81d9164402103406642c2514000c1c00124100650480400141c2000d002d40c0e000610303a103240c03076882000030302e8089240030441e00c0540381c0d0010400c1d0b02c0e02e9890 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 974482931 1250 974481681 974481689
    0x1812060b090907090e011d060601021e0a120e0a1403190b041e06020c060609061804031103040f090e0105070516062d06030209060409080f0306121015 66
    0x18824500b8541642502d4045074000c51050780d99030810605011400d4002c0c600314030030340b4128070782c802d0540c004540b00d250440b02180507200d2a41c0d98102100d1001030710700b05400d90000b61040880070364410106011a491141c1000b80800e04c0c10116a030309680c51004160b4002003407111180c4205140c00d0110f04000704030a4000001c00c18085908026955880350303020071612072400403a10380542041c40140302805c018804982034111140c00914a8000e5204a030611582d507110020428001160454042038262450208000a014042c1808500304001c20b490405488180c0701810f03601c0c95105801c225200c0c0310380d1084010a1040a4001443d49000c9280401c60003a0118068400390010005551203910421204212440010000e51403038003816060350440303008003a090501080e0321501d032000214200e803500c1e2080f040d1b8203920400c030905000e8030481c01c07809030304010500fa4000c28144082c17860000300f4010345041c0b503051a400100380c01c0114103444040d00c1a00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 974484181 1250 974482931 974482939
    0x4261f0e0d0c020f010c050307150f0605010c0f02040b060c0105010911070812090705040f020c06091605120a0c060930060f0b0a0f050f040513121812060b 68
    0x380758005900034034520b40c142d015501c001e0a941e215004032964800c0c0e03007001d8454040810080304200e00d80f402d50041c19410b402c244100001680c010301160014071849020413031078030b016400103454060600410340010000200d076440100800d03120360100080310140d9540d040107004220103407103038024082002910b14244039081d07817241c20398407d410300501000e0315280000e00406040100300040c002c040d0050040f04021240e92000e500312078056445030049200254240c0000100e4009a02502c010801a64503207000d00c01c0d201960301e43d1000c5030040c0c82c18400824441e0420358000c18940d61107828007031a00c0320104807131079401b00d0f07203075a00c5115684400008104854124007a0001000110560011104402060b26145e11a0010581c00c00060001c3c0951035801c210b40c826964890740c40360360400c100444608076100108101c0c44040c030b4020646011902104055071706091000c1840018004004c64040d0b1200d00544c041c4810700e001c101160003655050701041d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 974485431 1250 974484181 974484193
    0x70f05010e060309011e0903081b031f0306050c04031b030203060406180c03060b0411160809131b0f180b090a0e01081b090c04261f0e 59
    0x20000910114001e960340384201400710104407424820f60141840d181480180b40c003502c00c12000901902441400b0341c08508810001581c1a4060f2080402c2d001e1080d5164550b6803030402c8114080d030740e0b0502640c015041c00d004400582e80344155800394441d240f0030350b00c42d4a107280610f9501a01d000740525001c0741e010400058400103095500305901142c08a0700301d1866182d090040c0e03071841c01031721414070100c000040c030000354030160320920142c030b0521a0011880d015400351007600c00010b02814082412408035040001a01024400800e580349101540d800307032003a6403590a040700c1040000543c0f0181940010503242540201d0070b04d8440d0200a41031103850490340d01c04c81100c003c002075088960f5440e800280080c003071001103140156112082d241c1e60301c40b110060360700d14190410010f014030304009581d1280080f00c204514103420425160726002c0540f406014000c0a11013184490001307001c0200a0f01104001c08130803280111351800340c44c1c80c80301588060f0808 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 974486681 1250 974485431 974485439
    0xc0f0f050903070f0e060114180d23010b0a060c140c06040905060306010509070c0210050c1f0b030c0d06020a1419080c03160507020307030b070801031b0e0601030911060309010b03070f 81
    0x20985441027910034403100e1410400c40440c140f03c80996000700003040c040b040c41030849a00e0400301c2000d600c00e0080045a070500c040c0940740d1064003400700441d0342c2810030400105e45a00c824030159142c0c003030b1802451820041080c5070000d8200c414110307218410050b0b141030030000d10340180b50803210750742c00741414100a000e001e101d60f0007070b00511f440c9c41e460301c601f030049044541c0401044201d446c0e07a0b001210b1500200d031555404070b1001d05200101e07515133400203201102400043c03010802034200da4030440203621010121042c444407524104030204110083c4c5101410403429a610a803030310382c0145402c0d00104800d085203414800e00401c444411150404400c090a18590701e10050001034a0701070707182e00051146201004000d401d60748928024100c9108524401c0c501d807612400b803414151a004041d4583c080c200004c0e02036120f0303003040c0d10722800f4405a240070709991011809690003241c01c0b241980d1079035060742d0203060801100c401410000180749800d0700b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 974487931 1250 974486681 974486717
    0x203040618080c10050c120a0b15040801060503030a051215032a0904120e15030106110607030207080d051302310204050d0204111b0d09090c0f0f050903070f0e0601 72
    0x6910f421447c5094480008070700105c654400b003142e20006015810092100342e50040c194014003488010f942000303000609810000251100c40440d41c0b1260304201690600a0403003000920310284802282c2c04400e06031014062561152140d14412650904604071441e20100c10511a4000c02c0000100404640081c0c403110b0030700101d04d80100ca820b080e00016042240000c4800c0c844140040002002d1343c12180582a03010800c064a8160355114001d404034041d41101500c4030004210310507944c802030b40300f03070f03440924040524154416900425000c49040d502151040e20b08104084040000040c1da40000c0009000754581070030880441d0b01900300400083c040c030746400003515051405801e49681038039928040707000368085054a6038500d00c070700c02c041c041018000046000c024500a640d41000f41da1a4407030380d1403102908541c802c07100188101005024170103140960f88c1404040001c180c40087d40e40442d04006030003070441d030080c022605105160300b0001c05149 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 974489181 1250 974487931 974487937
    0x41205090312090414100801050105010c0c0905060d06020703020c130605030a0f030e09131b051027081e03070c0308070c171501060e0307090203040618080c10050c 72
    0x101c2444107a40f03d80e0060041005407104040c9841d0303010701d107400c1011480d030340d100c05c80031102000024041d59a8990064442c810950009010290341c101d0178420400c540e000700e900004080d0044010f900c06482e050100c0e00031040480040e041303880d000d08035207428128000e0707038070700c6020400246240900103956019000e0008190010700c0b041c8000703140c0200000381c4021405410714446280020000080d11985841101c210390a805401c110b44062001d000507540041d01410906034029070980c0d1003041909401e600c0e0f1b0301444c84602030580840c0550080c1211001070a1100000c000800804440b02422210340e205000f420042540c2c0945901101d0b00b101040b0f56411240c2030100c0d2401e1070303400401d01c4d82d100304180111050001030000c403401c40540d00009a03600c555084880c2d4942200251781988890f07000c0c08949010742c001d40e00305200c1c11001540300a030041c19500e9000c60001644d60038070229600e44131541c103204201c540c0c001b40c4403c00a5240403441c11003180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 974490431 1250 974489181 974489203
    0x904020a111b060a140f19170f040b1b0a0e0a2c09030c03070b010302011707020715031b090e1e04060905010e0709050610020102030f060609180702060412050903 71
    0x4803110300800070117170b0850101d40081c000226295034507810484071000c0581640c0e90b080000c1d10580c804412054524005801742c1c40000d0154169180c0d600c40b04903855020300000e1501c400f0303c00c001c10087c00c8200030444665540c542124410918007000656180c40e4000c0200070745c4400c002005030a11144204840034651500c03126450b900c00451450080800e1000a803200080160078083c084000c281220f20076070b00d006c21b001b020107440800c100f042d20010b0150340201003c1c400d5441d2110815001c200602d00010100310f00042d4041c5100340c0d510706808150090b40611441051540060780805100e905190115024403620400c03c03000700702402c0b06e42ea411040741005020b40201446101680032541c40c0c036218004040206001e0721060b120307030f10200c044c40140b4010f000f52845810404150851561200248005540b0409640b50b00010180700040700340c0040c0e46da107001d150b40d5401881203250500c1d04a12000c084101201400020711000019541c0000d5201c626 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 974491681 1250 974490431 974490437
    0x5030309030325060f022502010e0103020a45081b0d08031512070602030403110d0228050108010b0304060c051b010b0907090b040311060904020a111b060a 68
    0x950f8210b02c03580c00b2121070b414028030342820906036000d89552900644040b000c0c407a850424010002e201003510107820500038080b966803015142c1c0c9600a90141c80c1f864002d00b403207542141100b00c090528018191a0380415010f4400240d04445000486030b007081504102c40035079080c00102d40e0b59594900c0741c1e040d400c1c2ca024003160300e41c42c0d513000442401e034440310889e01da04006100312082c420003040c00b8000e5a08010b412044a40090b5600490303110340c0245152908607200c00000c524482141c54100d02804501c60042c1c66941c0d1407c03034003041c3c3c1ca007801c2782101c0c4403044c6000180c55200c14100b100910040c000700340080220f0360815404240010203c85c81181960680600b00b030840040c091003110025502e010f4000d244801c2048030580010381c0c8805090720041114000c078506560103100c140000752a25155201500d801811181442c2e10800010207903480550351000044c845210f0f01c06c0c41c4c800300040c50259030b001034105480c00154022030b2407806641c2c1041c4c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 974492931 1250 974491681 974491717
    0x50606031e04150c110f0120030408160b0a0b030d14160512090a170d0c030e09040807150b091303030905070303030c02070e01140906130f0510050303090303 69
    0x81100f610714180c00c1504800050040600d8400080d03d90080c0d6031001c0310134003500b400000204d01c10311031981650740c11f0b1900c49203041d0065101d40d030760700000d1003124004402c01048a288800241e1600c0945c402c01c40030400c0d15104e144001030306d0088070728500070340c0042424080f040e00006a48001c811008855071641412503080d1141c0f546014068228003d20218414007404940281800c1038162406900140d840c420202c80d10443c0302700d804290402403244100910a003041c0350303558080e10b4858036000007400040c031464000e071030484800600280b00c000300041c0c0200c115010060802c200a840d1200b0b000c260001401090410446000070f42c24041500030341c800c0200a40010071a01d029480345006001004141c4040016201d0034000041e0350b9441e5103004d05039906842501c1c843d049036000e00500c05005011103500c20b06910040000628921425442444440b4046481c0c01c0200c1d48503060b2180d41c0049019070810801c42003180c90000444855070800042801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 974494181 1250 974492931 974492933
    0x70201081e012405090d080307111902131505010315030f060203100e09070b13050d150b01050414130905100b0414060d03081b07030909050606031e04 66
    0x90014004030401c042852000c00200d0224a020030080c005480d04400d0400006141010307035440c011000016441000c6825100024480030040d50f0045468205545140d2000c8074281c10310b48030518071040b41c606a103c20081d1720300030800e40c0c1c0407000098108411034061080861200301405458149a00e5941c44080380001d0301100004540004590303a124042d843d15030042e40c0155a2105161140c800c0800c0002c04954140d006140c404010902d1303138544543c607107440c2c020140d03018580c80001000201c036100e04003103050941c480c0c8512a01e404c50113003401c0807a01c009200e181000b400384420b0001d041c01052080303c01c0d504031545110b04800fa00444040c003c032a000418074007600c02c0c4202d9070a0550440201080202d6042c006440c1381901d5408050307017222220750210214090b03101003330184142540000041c032030308890fa0000320801c0c2140e804510128009110810200803801c414403d4982110085541e40d10b141084000f080802407880f144150034a04800490 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 974495431 1250 974494181 974494201
    0x120601081008010603031d06030702190c050d262a03090a1d0115080f0403031d0d110307020d140a151406030a0b0a0c0c08070507080d0c0807020108 65
    0x781c02400400001c1c0302c030688030701d00107105a14201180c04884010070340d840243c542142a28482c0c001d5a00400e01520040c500800107038207200e090703542035440140404c03540c4904150721009030040d1a00d556a0b041601104200f58000700e002c4c4801c0303818080e0109449200c03d10300b040c0c4200041000d4045c50f07404000742184940003400d98003440d854000148002c00315a0404c00130758100112140f40c0e0b035222024402c20341c4400e1100015480000200004070010b45590007070b0091400140484004440022a408200f40c0b080150300030360310185c2d0903610450624060100902131070400c0c40542c00300750b84002c0000c00501030014910303003041000080020b44041070300b121190019074a02015000103010760081c02107072024420028415080004820b5000390340458040c07510358902c0c1e2004020200d070b620680030803034201d8035035021907641b04c080c0441600650103407485610740f074031142c40c1c070401d0300ca00c10904c46014100030224110006603401ea58080c2080b4402d0342d5094214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 974496681 1250 974495431 974495461
    0x80c0d020c010c081b0a090b07150c03051f0302060406032004030c030308090118021306081002190915030c0903020303070f17120105130b030d0e01090b12060108 71
    0x8051540c83c010000180643c0010350900a803110040c4820089000c007a04070648102d8050314013140c031090f01040402562001010554000c211b018000e5404090000940749103d05882c0000d8484083c4001e030084180713500d5801818a610303c598030304e1540407400d035009520800040c5559074624080840d48441b12840c49115502c0301d070f980b16141d1810440351841130000b0b400262841d80003401407001481501c1011980100d8402d0035283c0d0360800881d00c81c4540100d0040d40c40350000210300004100e42045150781c4a80540c490641d007104e0a10021541d000310100101c1407802c0010b401e03800041420ba41061402142d5080410029101c1c0d8078141d200039010f11000071940c0601c180100309c41031043c802e210b440103060a2039003001c540e0041505107070000d8140b90041200c0d180001d150302103a460b00380b02156400c00100000d050118031f1012030040f600e800390a000540e4000c91840141243c019000d06014620310703d00c2180c9802020141072182c0300022420310110f900913 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 974497931 1250 974496681 974496697
    0xc090618040b0108010c050906160c0f031a090c0d110a0f0603091101030c021522081e0f070b07020f030a050a02070f121e060906021810080c0d02 64
    0x6180c064109440d00403241e031000d1280100729440c0c004400c442620441c00c031001c813240100001c0c100944003504810104004000f110401550100001d0b40c56035640340100841c0030b0a1248001c1d8841a51b040050718010703d028a250800c51200405554883c5010350454118206584482000012400f0700c8141e4100b60844181e900300000c03e00e034990420340e1002d02c01c510303800d940d003807900042d1300f503985041814015070028140c03200e29507002d1072102d5118691401c03a448208003041c412210144280040d680030400107800049140c225a4100270314101a07a81441c00c110310b005101d41e40903110008124a43c00130101d003c980c401c1041e00b2070440640c003038980c1e45030b540c0406065984009079007000b60146070000a80310020002d900e08a0b504469209401601030380c0c2c4110042400a21140440c040d0200401041c060b00c11901c40c00c1c03043d800103903140001200010452405490180b0034410480311500040d480692203401c4844c49801c507440321284902c40c0041d000d0884 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 974499181 1250 974497931 974497969
    0x33010e07050c0a020409060e0f0a02010801120303182a0501230c0d02060714040e01170307060204230d0203120a051b01050103140f210c030310170f0c0906 68
    0x10314542030281a072300c51600340c1d10010848081c0089000e5413a1900f03002203002e4003007002030004001c4400d042c618401104d00ca441c0000d5881c5125101038401c00c1c0680007a80c1500740e28106501604002100e00f49010302400121486480c04000a005a0844c8038003502586480071403041c2e91400000d646107994000143c40195550140003540c030803048a41000188480b000c0720f09200342581281c0541d4444500f88010340e00340207000c1080700701e1001100b41444100302c403e01103680b40c805800948141001d55460050901741c00e80130700900c0401520801c041000580182d60000340041c0d080c4100c0e043c140c8440010340c007625580100040005010315010b004140b0700c1042d400141030700e10440744030386040e10a03c003240e5503c5551208400c41d50000107080341c1c425060b9101c5481040d11580c0501d0082500758582c06c64005540d01d001e900c418800174404910351034524941c1c85070030402495050325100c6c00a688102103699180204401d6002c10350a8651351240b507040e010401d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 974500431 1250 974499181 974499191
    0x14030706211e1a0955020a030c110a0609022b06111903090219031a0114060f1b0a0305030915130318030533010e07050c0a0204 56
    0x201600c22200c28607003840348546009800185442003240340c0403903c440b003440007240720301104a2181880c0119800150288030130501300110300821300c2d170700603210750007030056160a404c44c8060140c409a0071180e05025100d124071001100c0014242003c0d904042d0104001c8414004030300202d0340c800306804824841d0307603010310150104c0b101c0545540311b000e0411000c50861501d490741d0048001c041d80d14400c0c0603501001d640b01e5000145174130300003000417a420f5103045c84265a950158411604806801801c0011a1725941402e00401d4a10200703580e00c84070f84005182ca01c900c1404040c0524081940e0380358030004c001060341d40c8024400c03124104140d05000c1c0c843d8101301c07076520f00c5101340e0744500380c91140340da0594080c110f034030b000c120f13400d8243d5000d4410600c039034034000f01c40d100c1074800400b1420810403c01d111614901104001703e602001c0070f900019002002030b8140441c004100c903540d4070511a41c00748091804a84501d0030040d02c5080c0300200b600070350301038100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 974501681 1250 974500431 974500451
    0xd0312150914010503070e01050d0c0801020a0c030201230c0a030e030c070807091e0209030f1b030f0604050c060307091505040e0109090510050a0e0714030706211e 72
    0x503070189281d4041c0c04100b501a07a41c5008040e91070070705005280b00e21007600700400c410300b801d20160803021701c20003040f070320075448201071b60890301f1080c01070f00007a41c605128010b068080c4110440804ca02c45a185011102c070840c10350702d10b000c0e2030201c1c2d401d00002c400c0d014900c65808610742242c1d90003566641d11006100030b5845149000f50041400b0b05000040c040600d80704204813849418520b05d40800305551041c000c2d0840c9146540500132160302000700710042c0441100802000020f062041d8100d0500d440c2c2194241c14008aa022005000100b04002040c002146080350800d43d21750364820b040394043d500f54040c1c1c032461710b14203030b0355101d58000c4007410507106442140c2d0020780c0d8450301c007030984200a9000d8640d410201e0703440983d403220f4000eaa031000c02c41c140031442000d402c2404c3d2130310346154066581e800080c54031412a1038140a4030004000c41e140100007900c08080d440b490500d401400004580d542d500307203c0d405040c01000022840b0039000700400818 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 974502931 1250 974501681 974501699
    0x11040e03041e05090907061202040323060705131707080d02010c02061b16021f03051509281103010602060402040606080c090108060d050303040f11010804020d031215 73
    0x1032100701c8802d0120314030080303907600b00522a039100e84020801000c13018604402512507405412840d42495000c00010000c901c10200103480c500d401c144d04012405e908c0181d5081102c060000b804205040064800300c9548442d200203940c1c1074030a00d142143c3d41170855107880034607880100a401000c0600d005203030190b000d00f04410f015001d480c095030b110540301d600c1c040380b100c1421a242c8240b20007031705059920010102184007414801603444c0d03d00860ac075000311441010b00080d251000c111480601c4403640f454a00f064641e8041d90604001040c950300345035014a500311042c1039103c079034a040d500100381006800c503184e0b5030380d40c41c0c5400035255001141c050b03001e103051150010f04c8511032407144d4401d0700e01032022418032148000444030310a014003144c0c0c4c0b0541d00010500418820f02c000c501841c418a01c0c903041c1c420364a0700c103c04410003c00d56051080a40030000943c99426080c0001a403515089000c0d00c1120780200041c40d45080c1d000c0e444440000c04101452 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 974504181 1250 974502931 974502959
    0x21915080403020c03030304030f05180a080a0614012603070c030b010501020c0102150109240602030a1b02061602030a06050108060603070b09060711031005040804030b0603010b03060411040e0304 86
    0x3010b907084d1111207440c6030915680303101c1560001d000414480104003118405c0011380a10b040d0013144200c0d403114000081e1140c03102c1c0e0410200c0e900300310409000c1003060702c551100c8514140895010f50b240ca0080c480c14010440c00d48410504003400c055107003400d200701e0b038205a210383d603540415100e041810b14028240942c0e400741c450078900c080c0640c00000c4038146015955070384455a8208040480039146030800d01482e01c094002c8414540c5003400040050b000035801161200316801000700a10042039400f682c43e407400030781d613025840b640d08a8800b40d002a80e144041c4a043c408280b600044103c0034024918081c008984d20f180490b0f40760185230102e049030505500d440b512140313840b40004e6941d11030401c00a0500151940819000303115000b025610140c03900303c54201070f907800f00c41c11590401c0c005420f004000c025403420341c20640c190000c1081242c200042070b5200e4010380040c244110b40302c0e80881c02d949a0700000c840c0c1c4e68190030381e506e40380e6038008155030302 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 974505431 1250 974504181 974504183
    0xd212003010b1b060f070e0d0629011b0201031515081815160c15020a03060b040e041b0b0d1d0c0a03080307022e0e010c0c0219150804 59
    0xf003100d4000ca03c00b40d100140c2d1030b000342c0702c0345a40d08894a407090181c03444510030043c1c681001d804102d180c0420558862103802c1c004507903002d12140c20b8204c0054042510000041c14414405840801c18640074202e0300301903420b0800117500c20650203a01c103484503d90041601020b4a24004009584200040d004034980503e800007048001b01c02a118420001d804400c86031000010b40d110b43d08420080c051011410520400a800c0d20ba00d1912814088204660742d00016401107060b4544541070040041ca8802c2e4141410a90400c803e05000b40c00600383c00c009580b06800e400510701040c0c0108150a03400342c0e00c000252200700540105410110240e04003c1d100c0000c2a01189030341c50b4003c001c0c0130640460956031501d4254101408031030452060441c1032450300c1088000c035088020380002c400d4800f501c6403445085c2c0e06200c00d01c20f00c50341031003800140c81e500131045c0b4891550483c0c004e59071801c40981d4980360f83c0250b0100305064200b4800204040c0c1188140d07000b030b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 974506681 1250 974505431 974505457
    0xa0c03031809060b07080f0706180b010905010b03060d061b21050903071209050409080c012405040216020604260c0310020d0e1e0d212003010b 63
    0x103582d10425800c07514240f14003400c0e16000c00c42d5030b001860b141c0c020002e07012941c4019041403419182e8000300c42d22403c2d0100c005004013030801c107000b000201c4500520010b00d0600103981801c11600042c0000340c1a03601030101032208404200c0d158100402c180721a0700c075030514034030b101c00c001d00820208048036542a0341203414030304a440d90240d10720400000c0001c52a1003901d549403103103002c1c0408040d04014100001155941e22b034003480b810f503801400003d864880741071b0035508541040300f41c100b0388440113040702d0034a03420030315610031104104d4006031258441943c40321200040c1d24025403000f030008022585102c008185d94050312020629028461800c50256032010b0790b488060f416401a0380e01d12500c0f07650b400608001c540c234100410503226034107040d45080040490381017101c10240014413003d008001c2d50903008174603e050365000c1c4803a140c40031442c450541485483d5101c1c0507030a9401ca1102405072500740da440015513a6070341e104414035541290f08070041c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 974507931 1250 974506681 974506727
    0x7061409130615230a140309010b01030c0203190f0201091a09070b0f040e060f0301020a200a0b0402040e2109040b0d08121504090503220305030301030308090a0c0303 73
    0x3c900c165008414003641200c95850340c1301c0c0c41040003094010315440e0b4108805800070700310644c01c0760061806200f030390b4004119104100005800d4988400283c2c0c11076109010540610f000c45001d00841c00789810500c0fa0f601c00030070700300c5c0507128281e800381c5040c6607101c03240580085405190701c00c14200c82078406407611410072100b86d2048401349001200b05100a001c4011070050407a003201005010f021044100d401281c00d9812402448011400c4c40003000e5041d40201d904002c3d0000e02c0e00904030305c8415984d000c4049001800190140780d4030350215075042c2007000320ba40341c2c0340d49020300c03036100502000b40040d0351303c0005064029410308003e01c0c0f5600781410b03100600c9501040701802e01021920210b618400205201d07261401d100440300d140d2036a12540345501e01400185540d541041100108024040204807005200d880d013080030580c08001d49065941c54a408540c4d03407144801a85000b2100e040901300046d008400410550003403000e01c01c40d5154402030303034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 974509181 1250 974507931 974507969
    0x3050c010507080f030a090606120303110a05041403011d03041503180201111005131115031f0b030a06032303220b040806010e010e0405070614091306 66
    0x26503010b40180140a041c062210103e8220344001071940f15032a51800942c00c6001d44034442500c20580c0004003d1003008900380505a06000d00d44121400742c10315480c041c1c52040042c140c5c41035110341ca40142c00c0b012549460359080d0401d280a02e00310601203403801800c06e4003601c81d84984121144029000391602006001c0e0050b030010918840b01c8113502041c1d500103407846a0307419036080483c007442e0b502d6071740080180f00700e07405150340a0540d040b40c0000c1c41e200501c03074a03500c85688200800c9126109410038102120f911460402101c070307034401c1c44068682d40311a150803441c40f529011040054441d80380d0b020310300300c82c000c40c0361038183e02c0e0030030b4106011590380c4003020701d0350410040340300712210320200c0c02a0503d0015400440315503400c0360b140290081d0f0085c00c9181c0240300100941069440d00c6409042008400e14503400d065403001e542d00c50520540b01404845250344241c51594415074968110150041060a600300c0c65000184001d0040041b03075500141c0c0c582c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 974510431 1250 974509181 974509187
    0x601080d0c051506130e07050f0a120f020604030b070c060c081005040c050f0c071d130f15020d141513150503070602011a09090607230703080103050c01 67
    0xd80301d0394100c009400d02d14901114404211401020150003185400d208520744400d44900124140d007100a4507525040c8401c0013000560140300b1ba103c2c090a40d018003c060b0303a2010140d8182d4021038050403041c0b0307840400d803507016960001c1c4c00c0f4407032282000041c980054000701010702c1044100301e100052242aa020700040d40c00b50040346c505e00040c441400d166000320b01d07004007814440d0030121712001c81c801e981e02121a4a50980041404102000c04400004e81c01c01a5200703501052600c8000540a041c1c800000f400f070003607100b0007906200b00c0104030310440012440c2903507284002003000014084000b580d40074600700318005620136051a041901a42c402400c00e69419404682c2401502100700858078024448000160664003040550020300d0140c001050407000009131050040c0450074050090f002e441c05c0001c1400040f030500c2e03201205040181360b0b60320044588000b4814a4135400071241d000a01c901803503046000b06d41200e115104550946890700011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 974511681 1250 974510431 974510447
    0x30304120b011211100201020915120106030b130b1504030609050d0801080c04091a0723090604030f06241412061b0903100c0216080c1e09090601080d 66
    0x203030801d0f000440e11580d9142409005c0c03031001840c40054281030340000024204103080c03520200095001500c0d6901288480b00301d40101b4a50034100071401c02203020907107088131140c00942c04c581e05c90301605145da4441d401c005658141c0320458446442c0c2c03411000504075108150b8461003a121240c406511668000c3d0580781100050300c0c0000640c0240805800700301c0d01110550260324500c1e10401c40740203410710903003440c0d4070030b001d00407000100c10b403c43c5994820480040200301c038140e640c03104030445040f00c1d409456101e0106a07414640010401a12560004605480c015402c086003a03054019108000b00c540f04590303401c0d0803c075103000c101519140c2500203400041c4001d0100c070420829803044221145080c1c007210000742400f40e01d1000d000c000340d407844404000359041103000154002ca15454a100e41070800e643d1365440707002c104070300c114018003041d065006848006458004040e00ca0b041600703049401d0f90300d40c1824010710b10b0f24030034030180300203281c4103803c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 974512931 1250 974511681 974511683
    0x110606010203091201020433090614030910060311040e0c1f1716031d0a12020712050601061407080301030602030402010e12150c21060d02030304120b0112 68
    0x21841c022800f424400919001e0300c021186550034000010007149600842c0400808080b101c480b41442e8000007000c46200311007030080281c0b8600078071440350070503210b442520004050766102e03a2010086403074010720105000d589030407c00d00000b0000540794004072740004403814001c034040505a15036810241c010203030f20103110303400d0080c850303025104960712105a240190b90b01450103a000f0700110291065042802241c1c2c40b4000c6503894402d8034540c09521035042c403a403849030074440d656107403210080c021400740d031074140300e41d4020000103005041032482503880c80d44508040c4c1d203500d024403508011441d10700320603400010100841d0382856111041e20701f90790075a00c401d002904004c00807070501880c1d50050400d69900c8201140001501004001014102e440340600240240000b452240140480c801948040d0b1501c5a11000c41c6002e5080d40d8980c400581c00d48403c9901a4040c00300041c003007981c94052003c6280c141c0141c088800c1a669880c0c1151074440d1760388 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 974514181 1250 974512931 974512933
    0x20d120f17060f04180b0a0b060702010c11300f0a1a1504020403050a0501060b091c02030c0402071b0803091005031801110c011104030f0b0a02070b161106060102 71
    0x10100d140c40f05100c1841d81d07000c0d100017116020140340c01c1c01e40320109030540e000800070041000000a50141000660054034080c0c20403040303500291041c51000c1c0b0003004401c40c0041040b054484000c08031800c480f03d00240300060101d442804144802c0038034074901e000759030070040f41c0040000c19080d011307403010070380072100c5405918112210380913000d01d41c0d01d0380021500c06c49545900141000c0d5000701e0150000d030303806107441402c50380d00e580f0035144240180700d400314583d61603480ca000505400c44000c411101c03440000c1c04c21400b96012035100d4400b250380303000d05c00f0031008504a06485c0c0440c87d00c507600d1303195482e0780e0302492458552040d8040c1d103030458180f103100a1a00080600707004103003080000c99082c00d60718808405000e080340454851b1440f40e0902490038080c0701c1e4848149000d0640e210b1100d4941801e1014194840741000702c1e03918211036048502d129001040006e0b18140344000d1801c611031080701c0740005013122841d05c01c0d0400400c0e01400f40c04160 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 974515431 1250 974514181 974514227
    0x1715010c03050a02120a0e180c040902090406150306031b270e0106030503030a1a0d0305030c0c030d1e140a1d0304080102040509090a03140304080403020d120f 70
    0x5942180d41d0361004030302c43d0460042282d80c0415840107000b400039500719842c0e22120403842c2040c0404c07444e210310156120712100c014011100c0c0c44004039810344c0c0500c10301507500c0007418003050203000c4e00e50007421502847d50170040e4695060f441401617a2003a07006030204003018503031101e4002c40e170084080c50800310b1001c015607100c4c09180e800c030780c11244002c0381e442c0c0f800d41900d08403442c40d4000da4494000004000c01240e00d44a01518842c62400360049100d549010400401c1d203e0300040500c07200102240010307070400160b542840da0081100c0e501c0d251803205070050020f1044440d20940c00d00c0026052903046d003d1703070060b81840302c050410340d510481c01d98054101d04441e942002851030a00c2d4000c50248024405022200e001507980c1c0c3c5003000303001d21403400900000854112440302070000754820f140351039400b2203040e0307507071613031a14200402e041c031560740025070140030301d0140c50070810040c0300c0d0704580c0b180740c071124134642c5003490a50f5400205d45122485694036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 974516681 1250 974515431 974515433
    0x120105031516210c02160305150c1b0706120509031801091206050f0703020c030406030908090a090519051315090812180109020a090902120105071715010c 68
    0x40b11690310841410302c0c0c0701c1d25803d5010b00214111640c0409100d12945440c0d204918940410032083c0441102e054405001e10b90384916885900d1901c40c24000c050b10320205614100104c00d4840001410704030b03030100d00d440317056940c0c1e40070144160008200f1010301c01048400e1032041c00d10400d02000950f141c0480c142d4001401c010055480b8107000c0c0200003c100c440c0c1c10600c10a140c0d114002c002500c4c14103001280515400a024004041c010004a4000e15001c400d480c110f071058180071071034021030b00d48400c29008070582c0641105c14401c0015035114140c112038042c5030400700e10500d07441c00355010740507101c0444800185e000e903595000c1c006a0501d060480d0131948034000034005100b07642d0044994000c8039980e10b054403d00a202c0d5420003001252002e031400e500822121000354089100002e0912031380c3c9c0c5150765074000d207080d905c987c641181c074a0f45146c0200036502e4204009400d00c03540e036144c8815144a00700003000c55004400c4c41c2d02c107035416100da002e04401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 974517931 1250 974516681 974516701
    0x3040617090a030e040513240e120f030a020f120406051324090c06030606090905090c12100c050d0b061e1303050f150c1201150903020310021201050315 67
    0x542042006904603c449000c20088100301c0c044052351004e141e41850040300640a0741c00503003010f21603800c03079820040d40729420300840340c800103649495902da50300c1019480082c003d0f880a0040c3c500c00142d01c03807049441c3c1234200d1080d40701d04410486510b81002e071202144401030024540341c800446000d800c1d144a0900a140d81c0126022034481550350741c0e2098a14654000d6022945500c0306001c415040aa1400904180c4100704001d18203c501580da40b80070070b07011405000f500c810200012401d120940b011110030300b0520103054108401011a4010804091040e00d400c46100b4180340042c00c8907040c4200c4540e1001131807400c40f50204c01c0e40440c0342902590741c13241e000000a00140300c020310a600702c3c070152980040058946d2020707200105042d48844e410000d45c2608100360b042d203419140c60000742000e851026038140c0301000c880d00060b601d849000c982d01c041034210340082010f0072500c608001540d9860081c03558848407030010191040e28000010640c000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 974519181 1250 974517931 974517941
    0x240a02072402090a08010912020303070f032307080714160206160209040b0402030d0903021c0c081506041d100902030c1201020706051b0f1b03040617090a030e04 71
    0x44500014600505240050b04400c5107a00590080c0d45440307646003031103804000650023600f03078000765165181100c030003040d4000d002c0448003810350716008400303c60001c040550400c00c1c07030801c1009070300b00103102401a0200b00d030000b0024580a0b42e410584031082c05403042e0031031080d400a646880741d404c01200340c100c001c0c03450000d000710780c0720005a13031081c00840c000e500030107040c054bc0c2401c0c014117050081c020300003c01c0c86109402080181c5800500c0e9040701d080304c500001d030402c1031404032069100740e481503584c0e2044108089e980b10340c02d410140610303011502044045010700005120281400540c180d981201c211505800300e142c0042c004244000c2c2500c0034200040002580b0552030320199849070340c0410860f00b0071005103c0d0981018149031500800c052021407441a8411400c80d140c45010110300c4d0481c001322070a0070301244100d00103881d15242c840c00c0080c0780c045a000f40d6a480390302140460b141c0200401d0814009415035550813002c6012010721000d01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 974520431 1250 974519181 974519243
    0x50d0614150313020414040501050109060e0105041a03030a0e0a0e0c250b04080d05181209010e030a08220b160302030d0501091b091d090f240a0207 65
    0x60303d9454003d005a0362880340e400d02c049450542c00e040d08090034120308440058010040041c0b0308007041c441c85410782c0c0b078103044410454011840c0008a441c0301e440420b40682d040d0144004900e8070480c0c0d070008041039080d01706031a42181c0c540d4425201103c01800c3e101525080d404020342280d000d51a1046540c2d402c5402032010130781e809a40d2000095030490381941c1c24040407610220030400e5010b60354003d900f12890b0f444404114a9242d214110700581400382d480002c0c203010303681d000d441030321114a002000d54100c0341d55070a10000607407281c900c464110189012488110700031002d01c900b81c238078240071103040c4070903486c1c010303c21482003130164150b02c4107204a245940c05070107001c0c0a84100030700030407080003000000c000e00d10780c18468005d02c10014802d0040c403490700d06400d00c10301c0c0d40a5614054483e4000d13a41441c20303000c0e41c4906070140980f84080e100543c0c907400c0c07460041182c5a2000c1d610604910300303d0240d120000c028480f0181604c090403510410400aa = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 974521681 1250 974520431 974520451
    0x1f0207080406030e030c0709020a1b1505130f0c030201030b061206090a06090f060306150518060a0806090d0f0e18040305041806050a140d062a050d06141503 69
    0x1b900e01e65028a400340950140f0302280d00050680015640003050f40d03a80600d561441e02926155525104544103154403001403903510030019000c98800101c881030550844220b580503105401d182d0200d0196000590202c0e0400e260000981401803c4581c4060307944448200740e142c81080100042028004c0310748103031140c0001c10800303190700c61911100d14a4400142540c61490702c101514020030003001c012003156001c10443d01c912100d18022003044090000d03540d00c507000100b58082503081000944902003c02580c40d60000b0200f010303080a844044110041c11b5088031450100654281c01c011006c201c4d044468040ca0007c3d042840ba04080e400c00f5240c0041c0c50318094460510a960f607140d240c1080103081c241098030203880ea44d8803101d110350407840407404e0400b00440003045c0310342d110318a064040040541d50001008040490034601485400610700e8020000f8404000d1030410001111181c01100303100c018005040100070000c0d40e202c4d0700d00c4d84c000406032404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 974522931 1250 974521681 974521687
    0xd0b04020f040c080612030f090d2d060b030303061f020109050d020d090e060105031602190b010e241905030f0708070e01030309170c0904051f0207080406030e03 71
    0x700da841c0d00a000c90b4034566500c00b101e501d040c9040009440840c100000183c104110710000310170f01c0ca08880d4507940940342c0a843c990b403898110080e5840d0032403a01060000034001c1d00e1201c1e00301c4200d28460044400780154801242010f840b80700583e9400d60200c2100c420720b445c90811418803107a24024000003500d0302082d2589401c09001c291840700581007900b00083d810b80101c0d0030b202030884801103000c04c1c0303401c000180041c40054030468003064141140900c40c0d100f00940303966580c00b0701150498076550f2501c07080c101d2080c084c03010b80c0c4c1e61003800520355241d070740412014006090044220140000c1c148110040c00003106660101007807404511a24100107030000310310100d0080c002c0d60300d007000c0f05003400159000681e10342c24070001040481da01186d00815140800e4004900c2e0385624056803420103030028158000c000d00040006120b00446c2d280c05110801c0400d541810400a5082c00ca1003081d500414206040c4028040d051195114240c8042ca61085900d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 974524181 1250 974522931 974522959
    0xd11030a0c1a03040218180f01020316050705060c03061201050f15030703080d0f0f0c020a0209070906080c0306042702010e010e01121505060f07060b0a050d0b0402 72
    0x8140400d8400580d03a01e041207404010400800e4025146001c0c0c81d40b246007181090ba000803140c8420440300c0b010110500c0c04074509214911000059040080403150262841100036010750800c407075248103070300c602d8110f1480601a070212400c1c650311a014080e699980c643d03500044d003024244da078010325070b0400006a00f03000d10402c2d0040c40403821020701c41c13500d094808a0210000103080c080d4000001c01c000051b5200b0076241c0702100d2010103e4401c081c8010340008140040d550719040381000d041e02c80064000c0341c282003c034002c1d620307080581c3d10000c081d40e41104611a1b000050040d000180a000e520f001031a0400c60003000410004005004840040c3d80d8542e4003051034240c05c500070856800010380101c00a00b800c11003200d9000c1c000180040303010b0060381c48029144c01e81048900000c00b442d0002c0c1400408068403280e072041114002c0d084200d085134001d2901c0c110802625041401000f21407009015204ca80116591050725545c0500205d0f00702c0401d6106030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 974525431 1250 974524181 974524183
    0x91805071103070305090406051c080a0224060411031003030e0612071e0e090a0906090c15030e0c0a0b0c1018020f040504050304090e1002040306140a0213050d1103 72
    0x900f035029a071051307102d80780801004102c46141d4482842080d40c003075012803249da482203202e0781540101003070752a0012000305a003054000105450b01e89003c4061000380080c0602e01e1f2f00548054034200900c0340c20016003803003841306039000300402039541c0e0208000381c03041d01c4440302306901901248c00c10b00d03088410740301180d0907102180441c1d0305115410b020710311820140f800c4002c41c940075441500d50740c04140c41420180011b00c449032124541d2060101b00d800c0091400d0f408060303a6000342e51011450958560703141c0b082d002030308001c0c05070500c00c000a80e41c090500b00801540d562464005c0f1000254006601d5004a02502c0c900c1c1c40071200c0351064090341050b45280c0c040041f0706104100d1039419143c203c40c030540c03604042c03201040b00001542c040c2c444850001520000205000c0d143c4407000088000c00c50001401104018885e040503446481c5c000d44c100d4a5124080c0000a034010b50044400540c0b0390101040185480c5ca02c5001c424000e03400520001c1c542e50210b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 974526681 1250 974525431 974525437
    0x50f0303010620010516030f0212090f070602010506030c061e0415260103110303070b090703060b09161b060219080604020903191e0309030b07091805071103 69
    0xe07000c1102d0320183c000302d03c990304203242080c440c030b0020002481c0c0490094104d5004035202d00405646912800c44400b50b0b40c100d03806002d845446180b43c0c9050300a081e0780d12500300e8203080c14007414000048040c01401150301a10004028040481c010428004c1540000c1501c01c0000c0c02d45c03001110251754100100064144445510030500b1441000381c54114004810518032144654410343c4020400510341942d07403040a0300c4a0401d22000240b840c050310b00003604403d1140d0030b10240103400a4400100c81c4544810f00c0801418030402a001c0b008850aa559a01001d10102e54502c60040ca50700080c0240d070b403d480c25030710f407601001c030703006a00f00f12a04060021594241904540915449101282c2c2035213004070410204e61940104a003507850441880080000c003d88105402c0d420310341c0109000c4140b256060044c1030118a10007070316000c03a07400c0818129481080305005440d041c040841141c48a0300c160382c01480700400d00f40c03c00c4540503200304414014001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 974527931 1250 974526681 974526689
    0x9090807021e031c020c0f060f18030d0f021902182409100306020f1209070f06030506300706120b0a15080a090203031c05060307080c0d050f030301 65
    0x2402c1d8451540c1050504c1d00384100558040d0045655070b12003040c1d0300007030300d1040300d4050b00c0d0200040001b4011640c41d00400d1142d512410307000c55049401d50745480a0002010200d0407160b12013100c080c1660013004480301c03000140c100401107005420004000c0f440c1c01d1018080248140010440840b9a0020b81d8986450a4070600180c4841c5004071040301c10042207a902d8124104111040b141480700d110050015070041102a10001414180ea000e06000b4a245281380360a08403d40c5540c8180034200c25200304400100f0514400c1c400c440c440c003800340c03640520900001c000704d1040024020404450007036a440701c0c0a80050002100038006503c440c11040d00041301c02c4141c51018404c0d42c000c010f009001c2007010888480034101d40024241501e46841c1c010b0a07001500e50840c0c069054800040d4410176882464000e00c50704c0000740c0c0801a54403401e041644606281c41001c0c401d85c064034040c901031a22400d911070552003007088403803001c03030080c40e2030458200740d00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 974529181 1250 974527931 974527969
    0x130b0706020306090f060a1214030408070e150105030c030a0b040e03030114011107030327032d261204060501062709020d1404240e06010909080702 65
    0x2c140001803c00764080c0b50171542a03070b02c1c52803e00e07000c800325061080a200e180750983d850744840b01804281c2d54401803910560301034940c0c0d680c6032225103503a03031150305c211040e2030040c000041d00c01612007410421040140d603510701c0c5840b81030a01669402c05000c40400e03941c4c4c0c950f681d03c41c2e5143e210740c0401b03240d600c0103941c60391714284450000d40700c2074040700d0512042d040c6546071100301183e2901602d171700d41400b841c503200910301905040e0841801e40b04200c0c140f9404001d1080031159040070140d01034440d4540101000c0f160703940d840c90070300200208035016210107080203084505ca041c012032070800b8142480c0114010f0072000540c1e05445560ba104014801268054591844902c05400ad240140b46e401d0305401385403800d1040d03942155010800c0354101c5080e420130101e41410203070003001030425041500c0c500c150b40f01101d11022802005a61507985030141c0709118600001801c6160310300701584d4058a00340c2c030300300c41100003044203900503070301d160750103420020b110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 974530431 1250 974529181 974529187
    0xc09010e040222210b1317030f040605070504150e13020d061503090f11130c1106090d09030308060f220c18031b0f06050901031406060f130b070602 65
    0x18100030901512440c603401e100c0140d00c0103000305d216001c0450700907000b80b0101c680c0380c0c0c02c0d0502110b24074a4115620310102d002060012410fa40694580142e01699007003065441355070064030580b0952085140405526120b100c47d140645e2480c0c003c01d0018007030402540240d60203c040368008150418035079907a040501a1143c40c0c0000901d224103820104111845178a40400028070160005c0800031101c0f200b002d1500c17103044440d82994290828030038203a010304007500d1140b4071070308a6560f01c548800250500720000e1003200030960703600c440d0b49a40c10b43d1002c0382c0c500c100819480c0c1055011040001940310012503541c00c2184030b07080c50b00c3c8040c1140080903900071030085002c00c000740070340401210422041008503070b80300c01080c170007401c00c002080f1814a9580b280b801481640c17800a00b42c0d8018004200302e01c000d036010041b4003182241c0d10704403401a2101a04078a0030300c03542041803402030090079045007100707542d202240c1e1651601e40a40c07121504403102c0d5004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 974531681 1250 974530431 974530439
    0xa090902190e0307030b06090a09051506030105061f03020901030207140c0307060c0c05220f0e0c01021204090506120a05100e0a05061603022503020708060c09010e040222 75
    0xc0309581003000b604a001d080d1140c41e5071504200d890740070744158800e18003080810385403910ba90180d00d40660000941c0c601074002c8030850302003141260b46134029400c040000300d191405150703e805080306044104c51644403071100f14000d420200d10315045c10b44c00c00c20b12000c941c80303030f801401d1402028018512118144149403c0101d03c2e032114060221034541000064018050081130b640280d45001001203100c890440040e4456109548245018998030940d2040e4005603490a018011200d5219041c1e00490b42e4600d0082242000e500900003448454016003245070410300003010780d00c400d1040b0400a04054505400711800c1e4403050783c1501c54512030080c44025005007001d00303500c03551602c40790b4032544c00600c001110340085042e0148940254151a0003c54607403882214201c03608110840d01c030201c00a070702604c42c0d01d00000c0c00500000c1c2980c800c40110f280c140c01d00c00b984c801540e409400210090303101d6002d02c100d20324803a242c1004441c4501e42d9440d100090700d8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 974532931 1250 974531681 974531687
    0xe04030917030f130b07050d090b070b01140f03030a03051009061d0606040b0a0905030f0105071b0507150c0218102306041701180201090501050a09090219 68
    0x980d00020408004001e48100000c012007614080b03040900c8069490900482c44070b13900038030790070842c01002c002c5000001d1110010707aa014407206038032400a45a01e450410100703001e01503000f4003410003040180a000c0301c182c0c144c15400c10152a044141140070006404e540000300400002660345040200003003945001000412000c02c04000c0075041c00301e103040c2100101a240c0e44d069000000c5806a11564215030080101204403a152051b0b1603008050003000e1244521a20481182c00d03040703e0184034003401030b00c8949131000d09060020402118046842054515004008000429035280e00c41e1890b140b10310781d07c40002080c54410010303d00e140f00f0515031041104001c10400114030080b06040da03000e2141050b10b40e80e03141944c0840c1d500080c11640241e00810300040c107a2641c1c032a0082140d1a200900081c00c00c5c80c0481c05510810401a000480132502003180b9402080207011000051604002032b5454503e418141d922012a2031302202c0308003035500c01d240e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 974534181 1250 974532931 974532947
    0x80c06040c0506160308060d020a140406140d0201111213080d02010c0806150418020318060c0d022115040608010510060e031f05011d0603151305070e0403 68
    0x16080342c106007081040f0400c1c0e44d80000001c001010b112004011a52990b04c4406485066174003c050380c00403921414031443c40b40004407110b02840c02c100d408500d447e4101854242950050503108400b405500110360003011014000064015200034000104c038200003001e6400d000f5880020b060700d000d26652a214003500d010003107914040d20300d81c5580c0c1c05249a038005a00715020000d04904c04001d80392481030742c0c040d0108408448100b08038007141d1300030394440d9080d90b0000c0580d400d004082510781000300d034240042d03070f010019030303404c0c82081d4064455100c26105d5004070035004041125400c05c165240d0401c083c0020403042d103443d2502a21000d400d40c04007d001c1801d0400521070032015600840d800d01c15640910030868030104406510400380440ca114901100145500180002e00a804030080b0b1590031300701c0c2058100d207650240401400038101d4840c20002d80c41081e102402c146070310303100540c0060204400700300200250505800310081030500d440d01800ba99 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 974535431 1250 974534181 974534189
    0x1006083d020a09051c02150f070606080c0a0f03060203041703070306080c06071e0302030c0d0807031d030a0c1e03030f0501120c271107021014160807080c06040c 71
    0x40e50145001317098650000040c8074055045e1094101c00c9140f00c1c071004180120344007180313070460105142041c030445801600480e11044292500c811106040c81043c0c0514083c21148105800c0308000003502a801190710a0090642910380641103010305250b43c0b00307488000009803910f01c2809400424001600c401e44121384031480e0001c1aa2030140c040390403800005800c09100f034841c03e01d0f0092040320b40804d4144c0603592145c050702d0001e00760b4034050b0740c1600003e1410301c4002146040d181c201d070340e150a8200840c1807021682c070440700210050012520130306451031620719a032054030b10000d418440c0d18081a0720b14004240c6040740c00590000400c15100441900811059000329050700d402821590500c08110f0086c0f40c411006010070060707500e021b02410030100400050f040161085813092148442071400300c89090d0405800ca5003040304102500c2c80041500c0181f10b03044c03003034080f1402d0040036203902e1810307040616190100d401a104210800420101c40380143c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 974536681 1250 974535431 974535439
    0x18090c180108090c030313080706080103081204050c04050c0406081530060f0103141614010c05010c0903140a0f020409030e03060a0e1006083d020a0905 67
    0x1490400d03410280e128045250520900303070041030a0b408140003c0d0000c8102404403603079800041d000d0800101c0f40c0c450510240602c100c049100b600c24000d0314120398002070064248030300a1140480b21001810840c3c25110740c1e4140551a10707940580c41c8120303801d10406846034600280030307014000042910b400194104a044615540c00ca4490010043c1c2d1844054929840f0072407101608001d44881d40c6101d000100071800f8604000036040c0e0f0300c81d4508841e84182604070541d6440301c6204841c02c0007111fa0f00b400b9950000d11a02049601490a0b801d000c0d074a171606400c40c0d9041c601440000c2c0b01101c02d10a1000c24000341da000291500200100300140c0c540c002019900c2e180240308035100d00143d0103162081018009014008090301c2c1a41400c50703442c00182088601640207004c0c1009600421101e441600100c42052010700042d19500c0900700d81c82c000000028030f04250b0b024034a46480040c03402c21034110342c400c80143d880070349000140012031b40e90300003489 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 974537931 1250 974536681 974536687
    0x82d0408090f060c34180b030a02100f02071716050306040503030c1e0a0c03120e03091002070b0d0b010e0607020f0907030f1505041103010602061f050618090c 70
    0x1030410010300402c0202481108021942000185c141000c40340a0600100e8040c0040810760485902102d66400308085041225001400c1403544400060070080e51203440d071215146040d0280d50382c10b0b00704000d44141c82c0090b8880070351100c8205801610310a55200d401c029102d682c0840c0e102020f0a800c8001340103624056591541d2840000c00003c26010041034030b10710b050010168010080094008580314060340030b00500c0203948800a80008035100407400c030325101d61046010845655010b1441e0034031100a0184144998000004521170070350002503611500700230304145803500b600400d41c816004001000320341c8548400e840f407007040216500603035034424510519481502d4000b4182d403060307025030003442003d07400404241402010540f03410001c0e0b1820503038500712000c100f00840c1c0003220919000900900d4050303400040881c81012005601401200034014010342107511000030507425007003903903140502c48803840c4031a145d02c5c0002116500c00740c2d000307880313007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 974539181 1250 974537931 974537947
    0x106061e1107090f0f02030106031a0f030a03030e190c0f0801060e0604180206040603020d05100b120a06031b150e030309010c060902090f060a090c082d0408090f06 72
    0x520b40e0480e00c41c010b412541c400d0300012200e402e4120030442168807104549960707403004050050403c401042148480c03d101243e4145045003c2500b400d00c090010b11800300c01da90f0075001080050a04c25052058448204030300c50750428045c2d00d0343c0706903444101603183c11010301640b211604421810390518406020f039074610794074580d00c16800c503804100040f0499500088900c031280c080c2d08080005004a0050b8140d0024400700c0000c160400940c0d50342009540c04402901400000c01c1007040301200600a4400d1140c00c601c0510001409035507940d220000d289604c01c0b488070341c0d244648101300c0c00da10000608404400350408204101c98400000d171281b10b10323021f06051000442c903240510403103a00c40350500780d000d44910340c60f003021101000c9500084402d1b900c2030b110f100001c24045118003c522002e4180e44900103035850394030110300101e41209420184809110300c050422218414540c042c9010b500c0b030f0f61b503601e11042800150383c0c08611480c004c3ca01009000c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 974540431 1250 974539181 974539183
    0xb041502121207081e0106110c030307020907050912011e0b0d121d030304030f210804020d0f150c031a061b01180b0f01091a01031d0106061e11 63
    0x1c0c3e072202103803402c40c01d07a90310303500420143d00c604049010700208071000403c0490300003002e1000344220380c0c22943d030b0380e402c1d6080590303911030610000c3d0031102c1400811200e90084000d4016407000802c0054260b02c0c0140980c215184a41018000c5200f007002340310042d5284100502000140e5104071702c0300c40b54071440c007641e4402d0a114100f0405201d000c0c1013109030120680303000001015a0392369607a9061549194250354030683d0000c6800c140540f0a541c000c0c88a11005031688503204280d807075400b00600c855000f081034400c1000c0d40c140c803000a05001a2140e00e28054a0000b80310740042c02c0141154145580f140805000c001d5018040c0e492000792420030b0301440904101404203450103024001d1105507410780d00e181e00c1c411040200080800f0320411001c86918017980e80c0c3c505c81c205a5204280003a0390214410306000e007548680c00c043c0c0c420b05031342c0450081c401015821421100d0700c0e4010304c002010104d0300c0e5000c1c01200c2c0c946102440307034603003d080e00824004103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 974541681 1250 974540431 974540467
    0x1e030e090415090b04140309090c160b070c05070e0c0f0306040b19090b090c0406052d04030303060515031303020c03011a040b030109050715090b04150212 68
    0x5034400c00480d00080c042105081d003403450322095440510100c0d002d4a40b01c620910f00b61000c4501d13007020320400003020343c0041a01c0f040e500c014030200c0142c607104c410303c040c2d6101074001c50350510505921004246c2600f07485000300819514146000d4803030400741d0030140c03a9005142000e90480a00801c03485200c280c0b0340d610080200e103680c03625a60009001002c100140c160400d9005d03203c0040c842d40b002c40300302141d503614014001248802c007044100d58049030880410360b0180303c184082c0344102c007c0d082580d0307003014191203d0603914884420090307420206d0104100001c091041551601682001342424ac8000407400755110130501c55000051514980c0e103104603c00061510030801000c07112806002040b505c50070b825128444a80d44140c03e00480c1400b0116015050501c14400d40d10b400002401d000c50420f203003122000491142103081100141020942d0303203840004000a020305010311a04074400031001c0d04280701107403141d220020601201c411205002ea070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 974542931 1250 974541681 974541707
    0x2d0d032906090405010b091c0c09020c03220510090509041209180218030a05100c02030702130207060b0a080a03080402040212070e03060901090812071b06091e03 71
    0x340994044251011032414041e820500368418181800045d548004400a090b032100580d184002d11004004008144070312036402010205401000c2046082c59400b51400841c0c038002e0f00e2629003003008455041c0070480d100c05120190b20001c0101e4075081d02d802d40080b200c1d00f0600300b103500d442d00007445010001d0019000200e6100c02082c241d00c0f400c6050054000320130141440c1d4217125408000350441250329010f00c4018000c942e070b80c81d00150000a1030b60010042c032039010040034040c00392540007038940641c8028441d00b0010703a55581c41100c00b0b9400840181c0f0340c045401d1460036640b16501081c05000007400c01e01488101082c0c41041c2d0340c141c104100b05444030302c0171400034458042102d8248014000307100c003141d40301c5904d0390b1144040b002c0301e007030751584d00b10542200c188850080a1140c1001243d00f0b5001c0c100040d0360109585c140001201c00310344101c04c4411004400b102c500d42d6850300340c0d081003500a004940416100415010941c460358082c1a515100301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 974544181 1250 974542931 974542991
    0x603071e1502071a04141f030c030b0d14010c0c020303040b090d0614090607020c01020c0405252007180b15210a0213050d052d0d03 58
    0x28001d884500030403901c40280124004804222011810010303980c1150003111404000051a07441c00d160004580304084445100d21408800508080d0018503440740324905143d210350030b001540d070320f0200d00780c00c0728090140304040e6a0740c08445800c45103844c0d84141400f1041c501c10015803000415182618400210940ea4501420000c1c43c4401d07a41c0006003a1401c203c003002d04040e124100902481c1890b080761032780d0302e03541ea0903038071240801100c2e030041c0d000c200720140e5850107400140e0040e80104d0030001c4003451800542110180c640c2c40c10100d8038100c1d000000c03200e8178011821111024000c4c14219040608a000031103903d0300c0c408c0343c1074072840c50b411695101115180c0d8aa6281c40c000e40d04c0c0310140e5030601c07664080c400d010b066003400001078141e083c0350007110300c6e440c28418600041400e0804000502290300000d03912841a036a0b98450114202120120b00803401c1c0200028a0103550b45460640c69400c03680070181040001c04051085000c2c00d04d004107082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 974545431 1250 974544181 974544209
    0x1e040206070309241211161112010e0d0c02091618060f1403090a020d290114030f0d031a130507080906070807030c0e0907080603071e 59
    0x10030229003c000300c1d0446840c01021070a0f1542c4050b4400c68448022000d489440c24814880b011303000b1180000100264040100300c22018034001038240f6060900c6010000301410a000c08030b80515600d01030000b550703658503101d1943c1d034000c1100c2e194101c1d00b071400c035940c04a241c0c042141448051314001c842c81941405403000e5000380b00c54192090114411a68170390b9031040103043c14260703203141001c81c00c0f0b4078070a032008401300c041701d10940500c2c0080043c4500c80e82403011400c10b0000540fa1154000981d03490400e03508076010804540c180300d1007040d41400224016840301e2500c15201e80c0c07010350805d141d42c6000c100369028450a082c0000c51981c260003100f080c0005610b82a070000004241c3d480c40c601c168041805640555940c24a5903503d2582c0366880409588030300c04202c8c81d000150080b48250000c02002d0382500c0c01c40c9142800c400031440c5050144c0342900491050702c01c001c000c0c00c0c1001007a004000041c002c1036510300b11042106660400c0c09000c145543d00c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 974546681 1250 974545431 974545433
    0x7091d0303070c0f170a030f060609031109100f0b070308070e10230c160501020a031d150c060906060f010e01140403050312041e030e040509100e01141e04020607 71
    0x2e29803103800114001040c51b900c0320f81000060050024030b4071105403501d44840480c0c8a44110321140c04ea030f80c0804207014182c0e0305000c1056901c80140303800401480e101c4049510b034000340501c0c0c0240701385100c0c42c1c0c440c0010310340540814001072240c020089044129102580c0300d55190181c4045405c00302c0004505400e480320007526030504262003400050300210280000540c105078100c480444d40c07040e501c0303030012078841c42403c0002e030000c1e1b15800c2d0f0f0b10104071082c40850101d640100141304040c00b00200c3c070086c0e045900e1307004403a0001002c00a400d4002e005a07230384600101c03160f00141020748000303014082c0da0954181042050b03203280b40e600d1018000c89001d180c1050450b170b00c030707590840001e10355081103600300c640c408194403040e1900408241104802c0d07054407014221103111060200424005025a60a1040080c4000351034000e04c6908032016aa0f03001040b140000315140298413000313001081ea04c603a626519181c003a031120142c0e006503045034203d50360700d25 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 974547931 1250 974546681 974546693
    0x40f15051305040c23090103050f040210050c010b0301090c03020102010506040e0d12270201022506050a0c0c141203070c060c021810030317070804022107091d0303070c0f 75
    0x30f45c401c8182c40202400400407100e10b01c030007514103850300742d038144025511546405c0c041442910000e401502803041a109a40154060aa1b1900c14000018000e1820f00041c0c01e5a070301c81416100f070a8600000c2c0b06559081c0140ca9020a055806000400d450365110303a0b140340e07481c00c52040050104c5090303101304850b0411040e10601406116480020915507070342081c08036012409481030300b00c100102128481007541c42e02041c2c040c030030b60701c2c42c10780182d07130700c1d03200042d14010801d4007140f040000e20f40303030340b24006401c004900f04208910902407103490301028910b0440c65100703020a400255000c000042545c06900d44482143e600b80f020500d00c490b0581242c0483d500001003120000f000c1b00100200d90083d501c0d00d03004170300588041d8180b5026a04500000c18040c00100941071110034540703007280d0302302039110700c0341c1c07002405041051a4100c0344a99443c0c00d128850071148800c903208403480ca40146295062400016140c410010002020f031125072a5800178010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 974549181 1250 974547931 974547947
    0x150a1d2a1c0b19050a0e070614041202011b0302061008072106110a0203031b04211b0b07050f030903030d2403081c050c07081b03040f15051305040c 65
    0xb5203c01880380c5d050101e0101c1c05480150300c0180c007440b40c4403000801501c1011001c000118040e2001c0c901410320800c0145d05401d50416030500c000c0d0360342080040c01c41e01c01951000e019a0180519080045d2060043c1846074001d81841e40501340c180964500400034480d00003140c0e80585c1d1850341d03031400e50054002d0064007400d1000104141101c25004801940b045c040c0303001402142c14a0071303c02106002e58024200c1860b9801d40c0928511001030591000c940100d01d82c034070000030400c0c820079100194124602000000c1283c00400808101c540302564219000c0c40c03d14240780e02090340d0340035500b44682c1d103a460380c6900c2420b403174151609141940d030010768140b140d12410300f81001d03071010000707a011a00200782c0b203411003000d108013800766543c0c2070076610300007441d26054450382007011442d1750400035841d94034040c081000104001c1030a03104019481e8a070900c0f650b41c40c000d00c8480307000d0090800120614410b40d80d180c0d02540c1d02200c0014101c48203840032039480ea = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 974550431 1250 974549181 974549221
    0xb152712120408012a030207111e0f0d08270a0e04150903050409020f04050a120b100b0306060a050c0618070503150a1d2a1c0b 56
    0x1004515111003034042010041043d18401002408405130710055800103074140309442031001e005078010300c80035100f50018034945000fa400700d40084400400035403401004603242200741982d01c10b05015003018000c0000b5911b044810083d80c01160311030072598070420f40140181c0c9003a0300f00b4014081d01e815500c40190700a001400750617160981e902e00349500f5038055807401044040c00e418144c0902414005690560303960741407038540400c54000e9008000e00403031041d01404045200e842c0c642500000b8138440c0e018140c403020600b400c0f903803c2c402a011040351540e400f4140003161b8140c081f00d41040c0140c031483da40b2102c01c1d201301d40a00522070f8074486400f4400510800d03014520390030b4580844001a030708695a220105036aa806096421000426060000d01e0fa4086a80860030484c60080008051510624418200a4007680c880c0d000300011980540103d000703035050030b0041d8140c44980c8041a071a0484a050a0992008101011903000500e1001603023000304519 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 974551681 1250 974550431 974550433
    0x203180f030f030d0c120209030705040b0105040306050c121f05060a030207050303160f090806010308030c04030c0626040519150207060b040f0c090e04050c060d0b152712 75
    0xc401c0900c0702005820b821a0b0030700006e9900d14400010a1140308564040700c000303004114039480d00d8103000c050208013065505210060000102195103405024400c15500f8a44c65440d100e10040015012000e04404d580c40b1110384041281c3c140e414401098410880f03034070307480f1400300c1801c42c007a04c16007000500f03a02000c018494151080c420001100b401522041030814159404449800a520400859074040801040820031610083d90172510381003c1a01e070984a88411551106030350080001030309030000e1041410543d200c041c1245d081800500d890b0415880f8159241540411214000029840703c0c00b04801174005003000e002503141913440f400c0700d0074180001c0560310315003070040381040340b10703641c00c504e51181500c0d2240d03079201d00c8240c078100001503010800c000c0046510344114400c42010ba0380d902c0180140016008020440d41e050009200d1202851040740b540d00000740500103034402001c000031004441c0f070b5850a506080540040e0241110300c102040e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 974552931 1250 974551681 974551687
    0xd031407081308210c0c0705150d09080409060b04051011010b100c0303060905060306160516230c01050904020c0111070c030314030603100504020d0615060f0203180f030f03 76
    0x4494820361483e21100c3c01d408000b01340c0d43d0781c2441080c0364403c0d120b8031314064100b001b050040e80b070000003003030502010303408141c2400e00d5a80301a0031644000810b80700d122000c1420000c040c101d010f100301801000c0e591605082c54800818a1240d0300304400b002d102c071040d8003000041095100d90041c0c8402058107500c03c0320300c040600300c00c4403001d00342c000034188800851910141d010700c500445014000b000e05645040302110440492980b240411408111050301c010003040100282c4c1c2c00f03001a1a801000764010b403d03040c0c1c40f003101c0000c9400c0058042c01c580c0c1c00806a5441400940700580d0301c1d2100e11005005011804034a04c040d4400f0800c20140640070320341c0e6090782e21030385400044004840300302c80c1d280003c039186075140d40300701e1030721403002e0081c0c0100d81c220788003502d000c0e02d003802507a5180c00e8403105c2d002c904d0860118075003009016406004425642c142d40040d40c47c006140b014085800c81c0c00403c40d00030040003541c150983c40c10000f000c4405d041c0000c1d652 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 974554181 1250 974552931 974552947
    0x1e06081504081326060112290a0f0b0f150f0d060314010b030a05030f07080405040507121a0d14071a131410080a0608030a09080d031407081308 63
    0x10820813400c251003002c441004441c01c002500160304d5040e1100c0c481c41404412181d522680e08141c1d162800f9000a1003e0710b618040b07590203030460050403140c10104003401400d940c2c5046601041e1050b10805541c00031440c991104041e5802c02c1d880500e286945085041d540170480c403c800340045000d150030310000c14850003480001e00c83ca403c000a00030300c0380d580e04043d07907050800d80161498008122000c280110f0000400c0c580d4419100c25051a585000090454408440c40303808034480800c000c50051041c4940c1c0f01c140382e501d80884440c4403150201e0407002035048001c10b0320380299803801d012042000300038003c21941c0300c154400403036075503580c089401012800c3e184000000020894100c07081c08410740c150003510003c20a80c0d0000c0880f0b090b18044d15840b07165541c0d020109010700c0c02c0c002401500419114400c2d0b107031500d81c00c14501044c0b02a80e4081610300851105a410741d0008290405840c1c9841c00040c0c464141190818240c2680106090f41c0025011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 974555431 1250 974554181 974554199
    0xc02010e1b1305070503070509131103040c06050a0507060b0307150c15020711010e150a05070309090501080d050304030201060509100501020118020f011d060307031e060815040813 79
    0x1c1ca800419549507503108200c280600507150140c582e00c000c11414000501e94520074009000c0326000246004407c0c80c4060064003143c4840c0308011030040004100303c140070000030745800a218900d0a6071400719007880041140c0100800141907035221600c0c80200c2c0d03410004140075102c0007450700c2c131170303c44164082c04100004104442c118107109010204481c54400c3d035480c81d42040c50355404601640c01141c0081c17800c401258032652403000c103008428120702500c81866191900d950751060b50601a0592216a00212210b41080c005108240000c140303520800130b0307414110703140d8869250030b9015290640000b03800c10005001c104405e0581602c0200f11007080e0020000134410040080040e55040c40103504218091502101035120781244012013007124038620302d08400c200090140d91041c1c42d400c0000303840d60480c082c5c446050001c0c900300c1c1c502d04800c00c1581d01d010001500c4800301a550130f042100b100014042c082171070119003240c1002c03e40c04d00f050361220908 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 974556681 1250 974555431 974555473
    0x6181c08090d0f1209061e0b0307121703040c0909030e04060e070e1e060f1908090616090510080a0f0603020f0607080c06041a06180a0c02010e 63
    0x4001144504041c0c804490f01840c49a108202070740c0c0c91002401d0841c00c1c503c06021001412914540e40b00c2212032210111040c2d2110603451000c0461580c00300c100701880c2071002c1e04a1504450000010800034001c88508421180e416010315182e5403a801c10448404481d88200000c44c00c3c078030000e040560100d14030310181c2c011241001301c1ca03101c82c0c103030740d6072002180c0c403801155003c0740d010410300d030284d600100c41001047c1081e50403440c5003c030780c150b004500007007021800030800440050003140d0815000c0050310f440180d51802085540c0d6985014002034030204403241c1a0300c1d114821210b00e00904800b9101c03807844a0980c00090802000722207102003503142ca100c406028040c1d00031034040382c0e00140001510b034080740c200003e9510441007100e68a41c02c000f5050717411402e1001610850052950f900c11060720070307110854070030041000c1e11801c00c1554041c112260005000e80061400000040300411280260300402d03580750300495511607041c0c450000a944251 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 974557931 1250 974556681 974556691
    0x506010f090f020f0904110c070909050606060316030b011404120b09030310030305090a050a0305100b0301180605070e03101e0c0503071b1704030308150306181c08 72
    0x810082c0961031050301040b4080c0d52200d040e14841002802c007146403d03001660b0010440c94000d2510308130340a03292900659502c00056147c940c0102c900340304060103d150b02c82c40c15190315245203049980c1400520010313500d10306166840c459102c260744501002c611817071b00081e1403581d8645400200184803040c0307804807000c03102a0300203440040c0110503640626181403050b2501c60540d40c0c07c1d00c40303400c404005a040040f401d0001005d41e0340c18240402140100040c0c10000396003401721058810038860f01e4041e82c1002c0308108448102d0303080e40304003034201c10300103640d440d0b00304104c428a1045514035814420f41c02d000f50f005466510020328900f08030004032901e11544040415a41c00c502034102280c400d00c00140c01900415208002404070f681420000006a54400003441840c0d030441c0c1006011809104060704012016040840303e89440d2220f190b03440026584c03c8010802d100d4000100424030814600700640804803100c0e069100340403ca21000070083e1300c044032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 974559181 1250 974557931 974557949
    0x6090a0902043305061b100203011e06030c050405150904050f070f020606030303010e070207080a030e0a062d120e010b0901240c03050403120926150907030506010f 72
    0x1c040003180c3c022070a580480b0409416a828080d800380c80d111095500e4117608442c1c007a0a0383c2a5803040c3c0b6200941c06019001184021001540141956088550010700c14145400b8000c03100c25041000e03201111022110b01c0d8440b110950400800d0007154600d5810909100500a5825800700e09501c03541c081d0f600c508100e000210200c0c1e6600003507802c035815810800042c46409540d426259022036240102c810207951134007018601208070f0010f4000514403014030600b45041c0c03640800501e40b030310307107403201480960010320384006c00d0451103405801500000c40c4540124001a0310000f80310003009410b0580000c207007e0151450558896203281002103118020030840c070480e204405a17400c0c80307511156082d10a11501d00c000e8003408000c2c00000001191003400748840c2602d59190031566203402e808211800065110400c0c199038010703035201c8c0304000181c0312280079a166400500d521403031515420440c01d504007414030701860002085c40b07105494840203c800d43c0b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 974560431 1250 974559181 974559251
    0x2e030e060606070f081b1207110a03050c01030e2d010c08070807140706110901030e0d020a020d0f050307050a1103071d040309090606020d0e030105010b0306090a090204 74
    0x44108602e40c46144002407441940b980050b02095200e40a0800c49010300a102c210103640c802851420f00800035441404100058800801548050400368070100b41d442418580c11a81e5083e2a044071194040c10595030703d82240050104020100c0c50484004036807444103101300703110720103880f144622a92b640c00e2100c0e40386903030720410300107126500d03031751b99200c40782c94440045894907891011084042e400380001000f140761845408060074500e00002e68509004d0005815510030480d80c03000b58004031070708210950045400135540e03030304030350113189901c0c0c0e89800700029020f0070002d0300501c4040f0b40d0001300907000404982c600e0145400000441c4c5e0801011b41c0c90303078503002d090000124005944000c1d04031018150300710384642000f6a595465514900449100d83c2c020b0340160f105c0c9a5192003143c000826400611090780280005d604095268007548406080c081c01083c81d5000540b00d110650311140e440e42d40204240600d20031804000c19900304000d03c084040411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 974561681 1250 974560431 974560441
    0x105012106240327021207030515180a0201320408010b03070e01150e030c09090105010f0506070b06100c080c03031504020c060109020306010207090624090f052e030e06 74
    0x41c12400c0d40b5560750707002c0280b201c0c00703545c2808002c05c82c045085015214440001c80041c4080c40001c0800c4800180c0001614102c040c2d6000c03e20300b016807000c03c0c0c00405200d0f025076448a480601070500d0801e82c1c40118420740c0c582c01e050301d482c2144400302c0c8041000f143e00c40064016140d1045e0131800c440c00d85490b080500c01e01407007841020b06180e020300c500c1041a014014450110700014141d0f64241112030105220b94803c07142e0ba030a036556400148001d881d1811214042d140c19102c280c00e01c0d01ca50b884141160703005c2c090301e200e0001c2042c902c00c0103200c0d0036440002c41d84600f0040e01c905528181640d2500140c407614650f00a6140b07058681c2858820385200c1c10442000b070003240d286c907244500030b61010b00428114024450041072120441c00303a203004005580041c418081201e0b1820704041c5264120b9013082070401c020015041c0340503100064450466901000380040042d0215961000c00c2100385220740500f1101c2080c2c255000141400d2100140c8030590f8030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 974562931 1250 974561681 974561711
    0x1151823122817190807020c09040825020913050303060418050f0c0a1d070c020402040b040b03010311040c0c030f02071706100501110a08030a06030803010305100e010501050121062403 81
    0x8103d4006006911403042902c23145881b2441981043c00b40c3c03001d0340341c034003441856004c044696501d425a6840340400e4000c604146c1c511039130000c400410140410f69543c0c440c1c1e00c5c0d20002d401c0c988226110214001c400d000c0c1c10401190590100c01c40d48880c03648160540c030380815a403c41c5c4202c80b00c060000e4220018508000000c541c0e46502d80e0300e9444031401d44004c40b01841c00da801660900c0045503040c05ca00041c4007904d5040d00c5180c0f03940c51440c00d001c455040014041c021070400007000342c3d003034108103007091081d814203040b030a0001c4d042c0300702e241c440c00b07510070034407142e00e0000c0102402e004034189004100100e011030a0b02e4842c030040d940076a603841701084d29480103c10705c000c43c2038000039507007201c0301c110041003055594031440030383d400130782080d2100e8201c598504c10006483c4aa80740401200c00280081d6240c40b001034190903009030f04400f45281007090196456044d40b06030301803c0e03e010b201007185810300c0700c100304400d01d00c0c0800c080380c80c00040001d0390903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 974564181 1250 974562931 974562947
    0x20c03030901080403180b0d0603060f0b150307110105130510060b0d0209040b030102070b250e0d02030a0501090b0a0606030b06030115182312281719 66
    0x10f0315034400c02c1c0c07101e99003180c200e0003641c0c03924581c45511402144250465004010101490b02c01241c0582141071041c12a1400310725401e00310301c1d10490810f2601d0b5404075180300d40c1c1c0c01031030588a50303c04d08166009070f055002910303239520f0801000a2809543c640300c07603040c0148200c5800c07100000603002128082d001d0460b03600e0b001d028000000c401e82d00206020300000c1c0020640743c1e10800401d09a030020360003240c00740410010401e415214444040324060000d513154048070700d00702d0140c0242c2d80007001d00d004903000b003500780c15900c0811626030882d900100801070308645040c84075001c1e8080d14000d2459041c0440002c205100340140103e40dc1c001b0191443d45c2d107010404400ca40340b8602140900c621a24080c0700640c3d255407030002040e01088000036039031032001c408102d90704180c3c802c3c410f0b9040d01c2040030180c0006541d0b03c0c44403c203040c001804040030780b601c2d5500d81031080140101c008188010415054902610424070f0f21008803090300010035096410704 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 974565431 1250 974564181 974564197
    0x911090306040b06010e06120108120a050d0b0a03051902010305070509031b03011407020a0c06080411090a02130602030904050f0708070305041b090c020706090f0909052b020c0303 79
    0x40c1c8164042408900702c1c101c00d5812203030504203013281c1c1c1c3c16200801c0301030300490304684164048400400c03102d40f060014107811400c14080700d103001c0c80b017800600580030f190411080640c0c1c59688980e9134a8040c100307000f86030000100d801c440441d8420340c041140102003280000d0802d07002c1861a40190107982c000403000300500314030b000404050145070481d05440340d042d034941d03141c601c4c081c1c8031055650041c14168050324280381c1d141000c1090008980c800410426444104000f00b0b00c4400d1007049040b0849560309980c0f0342842c0792000c2d0045048800020b032080800190013600080200840003003603909000c103581d0790001d08800c080031248600030441400004800b148603921050f405803045951a052107141003101c1d1904c090780c0c1150f040c180e070b070344245400590100284801004036203022000681041d1200c02050a90b1040000d60b9481e03091603401c200d0300348002101420401d035110400c01074511030030024180452050f003d405030003042100ca04003c41103031240c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 974566681 1250 974565431 974565433
    0x3060209190803120c12040c0f0602120307030515060a0207030201120c050724060f05092a070c090c05070c090908070308181e0f0109020a031113051009110903 70
    0x10092140c405440310500621090440c8030805c02202c6c1c0540541425010b18020200d0144440c1009040180da21864010354155030092464102d48000502100e5008005140108981e01e84494200d801e0580c800c1d102d0f808079004c00c400551640c00102c070400c50f4000da0360090080d20402100040356000824240095001c012110214500d6880ca10142401c40b0404000c10003401c02d100c12500b0304d40103c44c5000c0354000c10050fa00d403001040e0380000c9982e1040317116083d4460142c02d00c42c02054000e03001c0b0404100d010600045a1a2030020714280d102803284400c1454024282d6000c0101180c4403080b04c8004100040180304413400d45920102781881c013440c91310b0a0310321a00c0100b100b0701244e80e580c08420a131405000d007900b0380c0040d0344800c0681c2c04588070f0b2424041c4282c2a4496607250240400c090303078070005d03500e00322030300f0a410a0350a00f035900440c2800900e8182286854102000d1040f02c4c1c0b0714020100072520002e408218600c01500c0c000b02e2885080896941 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 974567931 1250 974566681 974566687
    0x8070204020306010c0b040f0b0c090f0121050c03070f090b040603020f0706090b22020607020d050705060a091410052a0d0e030607090302010206240a03060209190803 73
    0x18203240d4020360300071905040c000b00c2210103039100c030071300c0b24103ca08a961000e01055202041350f00d510142e04140f81204a038104903008000c40c24031129050000d0401001507044460211000310700c080c00c0502c5942481985800c110581d810348c0305032a80c0002441c00020b10031078500c50f034105002d940d420303211140342c10f00c0c0c100308030080e41080c4440c4403824030030000200090682d204120b041449a0240750349031501c0c1c80800381c00308101c80b800b45101c83d007290400040c1e644804030380e20345504481c94800c112540c2405480d1030142d4200c41e400c1980001d00b4600203402402d154111540d0440d0004500200000d2001114441d1098404218140802114031801ca8420050280b4583d812210364540c0c1d40c0c03403494411016010700104407500580c00c0242818002d40d50701803e5420328010b0070b072443d40000c0d52240c00401003885008850001105540c00e0340c101021020024241543c054480c201075009600a5100510540c5c2050030a10300c01d280d40560b00848141d0300103181 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 974569181 1250 974567931 974567933
    0x50306190258020c120a0c0303060b0408070b030a1b020f0d14090d02300c0a120b070e100f1806020d1d04140103141506101b0303020a0210090807 64
    0x2c0a0b401100d40714100b400381030700d822444501c0c20050003010907a607481c02c00900b103e060180c111880c0c1d07081541d11174007c000c00c0c132042d4000500c070812101d040398056920340e81d0000d0030006011900c1100b0414007401c900c000c2781070740040c400c103c2e03840b0f070003c0c0e03240d500000c60141c0d80c0044103104500c2e21103050001c40807a02c1c09960340e20407540050102c103000441c403c1c0d40d9641d0b00c0306d080880036010a00e4000d00d2500d204102420090205039983c0d41d5407800c29050b95070000318a20010b103415080300000b5584d81c45004140c0d1242c0004c0c03e00c42e08442c104002410b210070380d015105c00540f0000501c0c42020125072408110761494001e0b080da40c7c9046400c49901314041400c1c110b02c85088cd04413031540b2103200d2400c41114040e4403000359410351a08820328080810304454603030000200500e01c03110302101d10b800040481d0007415a50070450244c0f007a117490b40d254002e030301a40030840d05054141d002005c040025074207490f003c10030301074070701c2c1241d0880102400a60003441700da4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 974570431 1250 974569181 974569357
    0x1f080c0904020409150c030b0a0b0f0f0f03010308030610081005191e0f0f1805070311030f010e22080f041703130f0503061902 56
    0x107800600251012582c00016202d0684e0050035800c0c040e81d0307075510340342038400c01d52611561140060032240142c4607858105401000d000d10700c40e0300b041307903030006580300e03902c41403401c07181702d01c41400b0720725220769682c14008082d400407503006014181d46628210002d01c00c8980c03034800c4000503180c0d180c0e03d060109004d010184034480100c40084c2050119480d00803c41e106500c540007411114080d04140c235080003003a00d503101c0ca40d52000100c080c005041c140c01288030324002c3d00e00c0007659507100c1c03000300c2c05031400030380d111110580002813003020000d14800d0b0341a2080b014916000e0345034680300c41108003d25503001c180c40c0c031007250540040d4550001f8101140d036108141d0502d6100c12001d800391440b004880c1141e8000100a030810f0040c038001c400902400c1c010401080c03514021a40320600140791604c6040081d501d08800512a03056500032100e4810260a20f40003642c1001480540c442d1910b2400d0100080c03100200d5459002004121a046204a50014001c51 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 974571681 1250 974570431 974570449
    0x708010905060619110703110a0f15030b01020c180a0b031c110703081207020c0102010b1503100308030a140603060402030c010c08070807060f0f06050109121110081f080c 75
    0xc14204400f104541c01707421410030608016600070800089046440e0b01048900400d50b4040c2103c03e81240701000a5080c9000051010007613050200342503411b40d00403414007405490040d03000c07000111042c10b0300040003006106c2e042204040102e040101e007056034402e8015881540d032210301c0558805079120707001c0100fa941510044440c12a165910407600744c00c00303002200305921060801040503410000f40c40c00c44400c0c0020030041501d44041102e0301d003040c1c2010f21034200080441ca01c100c405000c03400441e001040c20762a03040c95400e000242c0140080c2d221140c070564003207a103d00e408580c440c00786074010010410f0080030001950345260340d0909445004091060f40702240007100200801072068500068030140c0129400c1101c1d07402800315022031801c40c0510069800042003030a40e5401901030b40b50149034540403080140c0400c030181c00c10602a0040801d03500280300030f02580b584009150406000304c1c0d1400c102c0141d1140a023280d00c0f035500903405082c5a849 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 974572931 1250 974571681 974571727
    0xc0f0a06120905030a080412210e190305180301051e040c2d08060609220c0909060b06190507020f040c0810060c170d0902090a020307080109050606 65
    0x800324040300c80d80c4a46003036170450b08100c03020424400070041000491203001c100c02c180740c00c200140c00548050102c40025003004030307a06030ba69111200c2042d170208a030101d031007000c040844141c941454010310703640006480e800103184510000303403a407a04ac000c0313030321407094000c1a6410700c0704003403035071340103800540203907600780014401040d0400c0d942a56484064001c0201900e0b08041c0b110100040083d0b01000c2c00303070044c01c2031068943e5811003258011810422900078003122648090f52183c150b20020014040070342c0001e503020460300f003a4805409000c0410564030b5041c14003415204200b42001e0b40d81106002c00c0300d050052000d407000500181417241c00700d84420125044401500389031021594410402075408010003912014250a00e8414604205c0e40c0d80c1c0c81e02000000c01d881451040460600f8001d944e030307440442e40e560002c058232b40d5030520707101100003580160350400016444c030340045042207890058500a82019080f50b01e04004041c138220040c074500b038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 974574181 1250 974572931 974572967
    0x170c0901091a0c1207110f031c02012007020102031c020f0d0e0c150a0804080903070b12010f0e130c0b1306120501080c060c0703060c0906020c0f0a06 66
    0xc0c001c184100c1c0640c0000ca030a400c040400d5481c031851000c0f41c50704400707201c2404d0f803000410a0381c00156943c498007140c40002d80e8400070b81aa814000790608800c100d807080030701141028440d0083d4150030800302014001c2e81d00b500401101001401441500f6000c0e0143e4002c11818014460064480740c510525032001820680d01d11160145a0700c8280e0f6091000e031100e0030046544c000740f00c1000b010104076a602c5035501c121241c00814090300d01002c007405001c038001018805500100c1d02130700720003002c0e0381c405610780c034049640760040c10340c815108603040b00111741d074410490b9020036611059908a61540c4189100c141401c0380c000443c2c02c010200c2c00003840e6100c0001410000020010001c11281000c05c005d29044045032110841c50412004201603000868650f003241c01c1501c82654170121041e085152420355400284502e2500c5c0c101c035005940507112009460b441d6081d00c00c0c00750751604000c004048840560380c0141d00c07030410445107015802040880541c45 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 974575431 1250 974574181 974574197
    0x20712030e030a030507021c2003070504090c030b01080703080d021b01090c0501021002030f0411180106021e010c0906180b040e01030201090e0f0402040213090c020a0b07170c0901 79
    0xb0a08041003800d00324003244000c42d01000310710707141c41d5880c03071400004020115400c850301d03222881809110511240c8024000790700d000c3d10184850720190101520521240000c0c4c60720740707a46072280c4400d45200c81c0c010000b007030541010030141c080301c0d000702d003150801403540c1e4402d000307600485000942c000e01c10140c0e56084000c0c000c0001c0140510000040c40741760500190800c6010821020040d10410070026489100d50f01c0d030741c00c55045454480c5500001000c04c00000e03808110071000103100000252030b5600140e0b4a0001c0c1d44074441c0884019041e03001d50a03200300140500100703044a4051000703501c202014415042c3c030b418500c034440d039039600c1311686900c160000000c04007400c00500c290358100c0309483c001c143c07120380c814541ca00300b15450b02220024000901c00c1d40c0010b4603144e0031400c440740300c000e8054880c2c108100c2442002c06907841050603400c94040c0401c400041030740e401460042000f4980c207030940290354a03058403000c103038050303803055040c46841 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 974576681 1250 974575431 974575457
    0xc0106031e12020a171303141605040209030709090305070209130512120420040606051b0708071e0f090c02010e010b030703020d0f06050106200105010b0a0c060e03030a15050a0602071203 82
    0x82c4000c030540d0207100640049c16588001c40c80d544800e4114600403401003003a0703161920005203107030444c0c0d0344040000344140d0300c0c42c0840d9280702e010000381d4000864014480d00784c10204100d02643d108000311185a03110315010b003958000c503105660b004180b540001c02190100034001015a8481542003060281c0304c0040e0499500e600100000740c3d000c1014010341c58100c00207020300405400810b800e91a20314220b0b41d07859940945148a491084d508600c5500c80760401e0280264542040c0320030b49980c2208010302511280744015800c6c0722030005c4501d01031060141c0400003a000e440e10700c0c155001e00c9180d07207646000f1100d001503150840c0105000c0d1040d0ba010308050340e508040d00d0000f20390041c01200b11050340c2c4990b454403004201c0c51625070201c03070b41101581011381c1c12000e182040801851003a0625829020000800c1601701790740d4414215641480030700314495803603209002c4040158002d840150348082000c1c0b0045180c12041009541700b498806100c81d11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 974577931 1250 974576681 974576693
    0x3061206070908070b0408071502013c0b0901261c02070812040510031d0717060606030c2a0304050907170a020c0106031e12020a171303 60
    0x10407500000000c82d0700b0740601200505009a0300102120003600f41054140514207484421611582045406070303050130f280c080c000c0d04050380307640050900e00c0001021209550325084e07100ca03224181c0032000d01c212501c40080c820801c3d50711000d000c3e804541c0c01c0c8074a9602078a559144880c94135101d040782c900c0303039500700028403180c091250b00c00e01a004201d0041c0c5005500c0d004002103400c0040f80c1101e00503040142c1c1e0440e0021500b1510030002034909600614846400c1000e07000c60805903100380ca400030ba00c10496000c8010089500e2448441a0f10b4800660703255500031010808600e544004001503d6040a00c0104040a02c1d800360b0ba6011440c1d005082d040c1904081400c000e0762074407410b0380d0b9100c0d2450400301000032403200c031101d9108004185805980e400314020102c0c0c2c009600910180d0b5120026820811040743c002c0300194152400b15050744030700c09942c01c00c500c041119a541c035440401c43d8101c17900e80340c812119821980c034090b2850101e240000105034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 974579181 1250 974577931 974577943
    0x3060312040305160602030c060402010c02150703020714030d05120a1e0b091003031e021f02090f060c060f06030309090106050a08070306080a0b0903042c09160308030612 75
    0x3c45040145044c103200840590140500c0d4001015508144001e408200300422040e0707006034246041d108807001807001070081410001d046134030300d1002c01c2000c209500014104143e4445007203880d484181c2c44105552000c2130113020f4001034090064000900903000900e030440e400ca40c000c16071a252001c280503015802454980081e21480d01524a0512039100340d04010000c50000c006d500710749002c2c01020b881e48442030700385a18604e00f8062482405070b003800c07050590f5000340003a0b211201f800039400a61b069071083e2103d88030f04d500c2e45802011150100711714405400607175112204a844d9050041540d80c15000810140c403090713699148050190007140c0b6403035111242c81070010107503100103008201345413822200b401088400101e104031182d1041e03048556545020001d030842c0210b502400303100c10806080c0010720b40b5107404402a40b903814440740f8907610442060380d560464000790519800101e800c4c00400c91500c011030348824050705e0754805030500034040d0314240d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 974580431 1250 974579181 974579183
    0x2c01120e073b040b07050a020f030309010c0210022b0f050a1a0411031f03050d0c0209070206010b03010306020c01090b10050a14091302120a0f0b09160b030603120403 73
    0x24040095003000d890651405031464480e129404443c901599000c000890181242c0280800071a02c0002d051007004211032401f2020107903612030030702c1a8018080e001102c6024050f000d50030301c5000ca1010752084c0c9040c207912164401e4039104100741e0040705140d003000b050440381c955901c250a50030500030f09000b03010302c09000550100c2c8003401ca440b020700c400803a106500303000c50321402c0e4a034030059075002207100600704070001c0001c4100071500c82703da01c0204103000708012054443c0e0403d800283c280d0003a203914010760380700901281c4500090044918541c0184010300200c0c030150b01900e0907142c550000541945191103045100100f03e50503180c030644a44d0500817801e10000250040c80d81c070b40c40300400d501e07206c006140080d008000390307040204a01d0007005d5603181909240444141c2045d145501d40c44d0401a0540075842010f50b00d01e10340c000407410365080000e071f16203002500c0170304a40890504809441c5507201915907607161081d000409060721041004200035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 974581681 1250 974580431 974580479
    0x60f040609050f010f090614070506190c090e130804080313061e0207351005060f0102100f2702030c0405190c120207032c01120e07 58
    0x60301d000c081280e0300e00411a4141000f45c810692960603400482c0c0d4001d03104c050910400b0202c0c20161506640140d1078054810302c00d403804e00c1000d13a1032170a01604441c2074401800300c1110b003081500d0000703c0d0f03c18031848807622400224181f00c12041d4820242c4114055403a0543e00da803500c1c80c6401c42070700510300e166100c504000e465004210a42e21881c0300e05110b024414407400a501c030f04541c410039509068295003600303035004c811a24202022040d42013198000100c070a1980e85000c48041c1110764030303241c0407a5441c503105d107200e408148140d00411421525440d12406401c0494000303400039251a200264560404140c000e5950320300d000741004421030042526003005d0440003030080381b4040a10070a807140101101ca13024070f40202180604c1c00e4a005c0341e50100100e0040d107250700c04602c540401d50300900f0041404020000000c1415000c6609030f03480d525400e81c1800308e800f4031440d610320901500154a400030f05005d41e14015592901c03002d01d003030f0000804a0b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 974582931 1250 974581681 974581697
    0x1306031a010801350105160905031609020c2b02100b0f0d0c030203010f05150102060c0306190e0f071709120f13031110021911060f0406 60
    0x510314a0000c0c00ca0051424a0001c14951401c6040b00d440200300f240541c0c981c0d00101d1507450f0118240094400c031110000030000740ca040c103040c0714002c40d1039000c10300040141100003064278002401110201040003451115450907403408025400807100c08400d00503072201000400301c409028031080c00700000b1045c9210306280082c02c000f542c030b660101151420442c200c1e5500c408456860320103051b2030750700d500862030070496070003030259000035030641c20151207400340001c0c0d030000c070300802c048185d400034448034100682e10780501712040c50a5410510000d034071480c086603040f0450848161041040e1349542d2802c4c00044205d4007846021105006d208074268000d20030720031602c812129181da0300703000b071032151038040443c1907540e0a240070072a100210b002e0000c44000d41d10746904260003540d2490b011100480b5054802d00c41d82d510b1103131200c41d60012800c05100080c1e28000300700402c1d1543d44030009035500c5000758201c3c03420700034940c01a40b080010800740c2a561a0004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 974584181 1250 974582931 974582951
    0x3040f0c0305071a04031e02011419120b09190e0f0114090607020304050103050727090c09180c03060e040510050c120708060f0630040c090f02130603 66
    0x841c00c200e0b40d0303001148001c101c01c001046074903000541046409401c403000e5085030004940803507440042e8002c01c0340c00035101c0c0700000120bc10309a599110723140e401e000a040081d00d421120040002600a400712001500e015000c41860308001c0e4103400c0064001988a002071a12240108692260795039440c41c0e080d030003144c541242d12480107402050241791094000792603000314403650341410340382c001150010303004400c032740c1c0713030114940901010b0340035a404030740001500d1090710a000e2515206040c618800c12131402900e60f103140080c001c0f18000503d80c010b0035010a84001c0654070320000c03c4003800c0b003030004e000740d01540081518131070a0070810100d8002400b07400c21400d00708150322540303000d0318445030300c540e40d414000442d594500105540c00d8030101c07107c0d48880c0020b01d00700c04007240f00398441c030103107400c007080031143c803016400700ea40d80300355809040000505010440c407842c5410a407144856004054100341701903200ca501c109a68200c04e0200f80c88400c040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 974585431 1250 974584181 974584199
    0x30f060e0307030c060c0201090f0b040c0608010b0f07020f0301090f110d02130f15171501060e060a0216090219080f15010e0603100503120a02100203040f0c030507 72
    0x80d440c0c51805145468419580075151030840b54000709002d840d6595004020300039844071090301d41103034207039000c482140b400221031401241c1c0cc58005540fa01d001c59030911400c0d50605840031414050f00d4120f901c4030344c0d0204c0d0004402203074002c1800e50300441c292400c0c001c0d20103151041e0502140340c0f400b480d24141c000882880035000f01c1e1080702002c0940d4880c108454183c40b981c00010f40c1c00c60a11040024010000d03240c003004201c140c00040c50855002e01410181401c0d0070b0350341200500007410000c010a100e1100014001102d501d20340c0b03807101c000c2c0080310950040311700300d00020120004515041e8400740480c0d5012421080b5003400d01038034000d85008d0301d00000b261400e01280444a00090a0340548410000540300c041e4001c032504028440c0c005c142a0700c034034066800012800980c000c0c41c3c024020115562906e00040068130a458680d03000380c2580452520704000a4000420580e24081107485030b002065014a0180c055070040e0054405642420000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 974586681 1250 974585431 974585441
    0xa0f0f020d2f0d12020a050d0504050307020a0b0307031d0c10020f010c050403030e0d03080a0c030917180d1a0c1b1b15090405130b1812121308040906030f06 69
    0x240c07132054010020507032007070361003400c8419445c6803403400076040c1c0301d81c00e045280d13000702c81000750401c03113000010500d1401e00010358403429982d9402e006040280100000503800c44880c0d540e154000c1c0401035807440c040c00b522403201d40030700c101c0302c00100c20784440e030954000c0f100783c0b40031510000e010b06c140765111034041d135401000d40740d40090b1809035400802c0c202d401000c94500d150760304594400f062294003c0b0880f250010f0504042c019a0048060182d1020003202d0b82603002081c62201800c3c082c03404002c083d080054248880010070b00000510070007441000c02850800501c600c45444200301003021610800802e07000015040c00d030400314032601306034451418030f03141204001c03400c0c040360000c020956011a0760f032120054040107082071400104040310b44001c0001000c003481d42c0903d41c1e801c00007100c610300f02404c2d0001c04c82c864182100b1140c01207100064410381c4480c0340300f40b090310500000d407070a0340c1c40081104803601500100c9143c0303142100361080c000c00e40a2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 974587931 1250 974586681 974586707
    0xe1605130c0e01140c0a08040f090b0114031005090405031b0c030d1b21091e050d0c24020f0f060105131e020a0f0f020d2f0d 55
    0x4108000c1c1c0d101c1c040030300724819182c11541008880d4243c8402200098266a034031072907081290403002c1c40f450424030300d0b00300340504c082d00040c0c480006a203090309e0059009603801030311401c0d448020f06010460b954001400740f0701051080b0b400040380d03100d9954152160f4041d40281d40c503000c15114100c05281e40200b810090f0b0300c0b54081d03045665000c2003c924640240c01d00d03002d2003c01c00d049400082e13000c00e0240200541006504580e41a096241c010350055510480441e1300c030300c411840d0200000c645003105000c4807050005060018551180a0041c1940700b141d940c0c0d0050700500c4046105800380e50720b05052541c1c483c2d50100040302c409030a40c6c0241c91400c8150f810584d84800c1441810302c00c45031070401c5a001e109940c040495030448a0070904c240030390344c081d40060350010400d000001d2525040d041800e100c0d00428059080c0d0b039002d45007007040103000301d40d0311300129080c1c400025004c01c1c12141304044509520b0000389a4003411880001c840c019080320710150bd = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 974589181 1250 974587931 974587969
    0x527010303050705011d190507120503090102060a0606090e1314030a0f020c030a0803061306081c0c0c14060c01090b06152113080c1006050301060b03060d0201030e1605 74
    0x1a00a2040300c2c04511f01507604040510300100380542d0500343e2401c807480c0d00110341032000750005401c5c07004c0031009002e615030a0702112140e0311160f42900c200c0f08184210b40000d05101030030f0060352540001c990308188422440da104605548a140a44090301c44a80e1668000070740f5500c5160030801403840340381c840c006001440710740c0002c20386411300380f4802082e031080040021b80c0f45e0ba41d11203041e032408800c0400c2103000d8071030100e5540c8202c0c4820302210060170000c400c0c0305602c50f213a1600002e0b803115011044516006500d204a5400c020035035201c402880300b186402c10900c2a05406801024085c0e40e50408400f0f0000c645050410607804030300c00c00c0024018081c1e004148031500b00f62890742e509540302d180c1b59200420000c4c00a00d40c010000321a11030550000e503900401c4031030501002016500c1c003c01d8202c54142c860240d80410620000300c0b549402e0b07900005050043c18045102814031811750306040c02000200c841c4c4270789000c14001818442401d240c0c0041000e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 974590431 1250 974589181 974589221
    0x19050406080f030712090e100306060e13060b010320030a0506030a211b030e03010509031c0b0607060509061b180609150a020a050111040f052701030305070501 70
    0xa82c009440b032250503c00303801526480f03010038801e441104840d0080500f07820b0341400e810081d42175010001d262100f83e5920f420620040789803001c000d80e107402000620311074490b0320051399821025003004840541415034034400d02030042c95101d1070480410003c0802540e0346029000035080f120082c01450203603200014800000d0041c118610503104031506a91104200c01c0d02255550700000b10400c142403c08401e004241c0c101d080a046040200d00901059458041d100d945e03005401c2081c2c102914000600070501c4280d12140d8440c002400052622000d62103000c02c0e0b50301138031030046691107181084a5100030b12407001c3c41e0b200c00c01c2680d1901c1240c240d0203415114421a003485980700082e819003560392440a003008101164029484400105d00070b5140c0c0e10091055915508003009c1c00a03000000003150181c4071140080c4d0402824030781406512044420000400008a82524011503158201c1070080d84a41d80d004d641d0104d900c1e002c0c2c29210b07030030840c810a06c660 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 974591681 1250 974590431 974590453
    0x804020d0309240206160c0807081e09030c10140c0f0d05070b0a02030c0d0b1c0c050f0603010e010902090a03150f060503030c06060f0d140616090803031b091905040608 74
    0xc3c030b194056408c00d040c1604c41d209401c10072113030301c1141e465001c200c2659030112070045005001c0d100346c1100310156418400c00200b800350200b241411100042c101c3e0b103000b2864401640686071030005c0b401142e05500c0e000080c2483c0500d01903103100400e00101b940010401512640c50307020318145015429810078070b808040500a049400e94000e0700c440f5140720300d407503154107520030012004034202290300b9818542e401341c05a004d4903000b125040e2040080341408001c990480304084d01c00320842c0c2c40c0000c0d40000b9086510055070001260300000040b80300503404400e500b50701800080d40351201c160b21001c907400d0350700c094001c0d0405d2111489101c400318040764400b8090b91510442301d0781500007541089040002449400708a502100400d800204684030780d00c03000c05058030f402560425074460344148030b1419160f104200141c422140451011a04400c0c407000c0c030309000c0c22500049006141c410046451842280304000c00e01d068080c1000030903001014104413282 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 974592931 1250 974591681 974591687
    0x1a031002071e121425030806041107170f070503040602061e07081008070b07050c0103090209180703170d0f1806091505040305130905070804020d030924020616 70
    0x1c00916906004414aa08180c00c04040413104654404640803101c80c402007455013404c0c0c00020705900099130140007610a04003407141040034aca02c201510f09001044c4c1d03500f4000c4a600b000003540c800f042c4005081910000c0240640a1055000d1621103051160003883c10308001c0180e825100b0354424030a9a0b218281070f036401800c1c0b4640020b450340c81c644454003000303140c0c0c000700e0b45105242001400548103809007007514802c4054130244800400110706580203080b02175400601c1d80003184070705110b801094289070043c4199110307941e80391100720561401c10000d42520307000003400c40300000c20384101d90420511400400410802c1d48403103004042c0c1c0d0700c00a0030341d65a44003140034483d1100218a00da00c0d51001030103540343c20700d00100703540c1180d40c00440c00f15290b1004a004565406240d03c40c3e032895843c40000da55907001c03c03219911031081a02030108260700401c1c0701541c154060307520002404c00e4100c03100610402864418014010850ba040c101c075202e951583c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 974594181 1250 974592931 974592953
    0x714070e07140f0c07031502040501020c2e2604110d03090b0c0f03040909022d01141b061f260f010501030c0317120403031a031002071e 60
    0x4070003210540c984401d02c0281c5d16019042d0005080641c0c00318050000c03031215002007050b40c0c001e030309881d1407032003083c14024071a180322104200600101c000c1d800d8625050f41002500360b00c1d2400b20103240515100710f02c0d9960240c0c4c40c0094489040070042441030f960314102603540280c8001351151001c5c2c030000e1858005014a0417510b42c00a544005044104105802100c128003074954969a5503201e1004080104040340120303006406080180fa200b0100c007032030340302001c03040342440d041c03001100c400104000310f83e00c1c0c0f031040c080701321000c8012041c01c0c0b010764020000c00440c2024100c5503d2180100005103003040f90740030604c43d642c0f8002c2181d0592800c0c2c2d83e81c1c0404d414000503941044034084284211b98640310000060000c159180300032280030f0044c400204541900900310340c4108091074407480d00c041e002c0b41c0000c0c0701360310825051101a00c01d0141d403014900080c00c1415003a80300b1202d46d008540e08091104484c14010180c09151250342484200d6403012101d103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 974595431 1250 974594181 974594197
    0xe030c0910090f0509010c021906151806061b021507080c1c090b040308032a160c17120a0e090106030f0c02030301180902060714070e0714 61
    0x321580003049141e48056040005403001000c1485500c1c07880300348900410080380c0c130f820f0a40c2440c2645c010b040c0040f0304003950104114a20071203d49544640e00501164200706a501c0c1c00390b600015100c4907409040a04c001008010170f44501d0036400070b004a84040d000e44289815241450060791846400c44225000d02411600d5600c541441c1030b80740140c0640c241a070103090070000c80e1410428168a0b43c1e1410b07162804440d840d0710300e042a0f4061408020801042000410703602c480c44200b0a111041150000400300c40258004c11541c200d03041a08030050b080300003404004104000c04060a50000110b807080f00b045449a5501c40030380b0611825400014400c4000e4400e202860300c006002d0040741039540c1da0040200100b8030552044079041c904040c2c1c0401c9807000c82100c3c100c03000e6007110810b080140180c1c100a1211a20403a403052040000c980016811540c0d4a1a05040c002030020940340c03001c4544056801030030102000810102d0070b01c0d17500c05106440000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 974596681 1250 974595431 974595439
    0xb0403020906040213062607090b030603070302030111071e0c0b0304081608270105040b0913091a13050d030f0915061d060d0201050a0c0f06060905070e030c 69
    0x140c5031000890002c1c0700c1c494003445100c1580c5408241c40b46c1000707c1c0501501c0c050103210304299481400c021070001507858000250405000b00146c40014010310381100c03008007900c454541c0c950000782159035070502880010b90214001c010f02162403902d18100071600180c03880b00c101503071035986070344060040d6112044040040740501c0021070558008548054240d00301c0340f241e080500460300a55401a00c3ea8007506464100d03850b035084050440b03a06031200c43c00c01c0c2c14420026140d401203448250008070600f00c840c25034071180100c8180070f020b02400f20841c540804d08502152008001d94101c0c55565011000204001840542c42034107142c00a0f801c0280c018860140c0781400f0003904800f14640d11128040403076000e4022909507100255440004c4400d079040b1140413a8410382c00800070302c042c0c01550058000700a0b01015180084076048190781c0c0e1a03503c00390260070b0314400d81d5403400b44288030182c400c80782c1109a9060802303421003000700003036903200341c1c0340c265001e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 974597931 1250 974596681 974596699
    0x501060f360305031303060c030b031c1101020d09111002060a1109060706050702010b010e13020714031b150121210203090315010e011a0f120703060e010b040302 71
    0x150701e004286018641c0030068956a001d00c00ca1140300c00200e00060310158900007030340101900905c655440c01c6000740c054101203140e1040205035900f41e484560030307c050600b5225001c1802c0c801000220000342001a000700fa5042201e400a0460344190048582c41d003844426900064101c0d4000b108400203d00000c00440c01c1c0d074103005590b2003c1e000400400c2610408c0b0964000078803d0365203038002c1102e096144011122091001c0a00781c01102c030084031740340d01107030741c00821115004001035511118100d9945142d171780082c050b61049112211b8130712080c1c10900401c035028580d4200c014007541030190801a1200100d46d0603807110442201004205420012910540ca080828204ca07840c461019459510a8400611901901c640c01c0d1000e06482c0d1410705032241242540b00d140c1c240350200c2c85403c00c944d445a03c1170b03070078084105010700700d5000380115603906808201d90300380288040e0940321181c00011240603102c0040c02031207203e1003902c0c101e98048070086e00d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 974599181 1250 974597931 974598017
    0x120a0b0a021c0209030307021e18100618030c150f090e060d03030906020a0504180501030308070f030b0603010b0a0f02071404111b03091219020409031206090501060f 73
    0x842e40c0b00d4050000c0d00a00b00e15603000f41854101d48004200c402610700c3ca411001c14043c1001071b800464680345c51600841003449801d200e100d0000e41b43746c02c80250034683c1e8032904e401e40703201700c82e40c4550401110340001c10303c0340b64015101812003183e402d11200582c100110301c0580003008091074062070040700c018013810b01c2504094801500030208568500c00000014920380c0640101e071041500f041d542c0344204150300c1840c2c103c1e41c0540e140840c548518504554121400074204200344e01c40090380c80d107580d0900114003c1c5501e003021a5102c0c540b00c0060104d105540f484015904407030710401481010990024081c0000c072400500381c96451600001c5000c0c10358034529042c0c04403104110140c0000080840c0c503411a00c085200110300d0b0100c0c1d40b4045844400240540601c5d404014103140c1c002c40e800a02c242010440110751078003403001ca40700e6a100c0f608076078846004000c1541c10900301902d010551030b240c02941d41002c6041e008112010a00310128a41c041e82c3c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 974600431 1250 974599181 974599183
    0x70e010b0a050717031005190303030510210218070c0219090504050102040503010b10120504060605180403090807230613080105040203160503061311120a0b0a021c020903 75
    0x180d203203030f400040306032041d40d0300d0004013040d0011107035503002039060080490146008400003070803071000b60704081c5aa0440c1e40071030140c04050030400d42c0841001d008511071009483c050280c0b6031280345101d07a503845004001400340c070041c003034485810142c1440b40260b845489001115011b840b20604400304038812004407401d5404283e08c0b510f41401e200401070107400800c01c0340c5044000380164180d071001c00080d07042c8492800041380481f80f003202101e07003581109a02500a00c00055066610740100700e8010300801d1001900d9042c00405c8205604030b862403025207907c1c070040100c0c0382410849125032200c815220100031030b0990400443d502c3d0743c2121882c910013402c6541040e65007090f00d010f0301064400728030034080d000704120f107001c0c041004011039800500034006a21000c8d5080d80904034010251070350090207042c004103031209110940040c111800810031030529041060040c0d0700600328600240c01002016001d9185040310760484210071001030f6200044400030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 974601681 1250 974600431 974600437
    0x30c011d03070621060b04060e0d080703050304050d050301150c0c08070816090b01140304230d09090b030a1b0e15030c240a0e0d23070e010b0a05 64
    0x359a1500c104040400d040d5801007081520090110703102c1d16451200802d00c09607101d40c042e03540340800521080204034440e410b5540c8407200a0300390303405c80c1203030707180e000460744011800d8011420000c140010400d08101032411014dd40c40c1403404c550418840c8010b50780c0b81100780c0e04000d49280400188000c0c20700d048004d11450703084035449a52411065100c100742c40d02c60148074074013000020300da107280c0540c034400901651108650f1003240685421500060415154000310b40a400503000c14003541c1d100255254000f050040340340c12004003010502d400c6104000c1c01d05046010701c0d2170025424a50301c1e80241c004026916005480041c0040750b0302022000040c1004c1c0089024078a01c41c190042041e0f003030302c81c0b800202e0180a980303040c1409040040b4074625442c042d41d0840d8000e000c68901d10b2915058805110700082c021b849007036030a46800302c0030781c065003041c1e41610007a28010000030260080c2442c09000d03c024550510030a548140c00240003a000c4e4403440c11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 974602931 1250 974601681 974601737
    0xe010e0a0806070c02030613020120010f060803042306040e070c170a0305070206060a36050604060e0405030a2d08180f0318030c03100506040b0a05030c01 68
    0xb211100d240c01c4000030035100c4c1d04070040e8041e025090201e181d03c1d083e10102070388035406031652010107a01a140c640a8201d182c3c0c80402950307503c1c0c484d00351400703d000e400010700010004588450810172400415004900010010144d00d04400340b41d84511040d0340031264040301358055036031418415120021049070050540a0102041b8588580d0341c01500d000030143c0d07820021a903440300160b03583c00042d6240d81d03020318a490100000c070881c803850744003aa0810500e5851400000c511500e140c2c809906040c90b80d26007007044801d082c130340300d1301c0c0c01440002004034039400d00d62a019220b201c1e40c07150030104000650340981c050b60001000b0003080b0008280f880070030700007170b005007640d10544404109040c4080e0740c013111880050f4400c2d150a0f41c402a51901907581000e803d0180100401034060041c100d080c4000c3c0d40510544611100e40d110105092034a882000b088400201d8254030815800c041404a928001240c004a040a08103c10104c0c40358240400a0006d010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 974604181 1250 974602931 974602933
    0x1b120b060c0d053004060b22050405120f16030e0d060f0e03030903040504050402030a0501090c14030d092d09140c040e0c0a09081006050f0d030e010e0a08 68
    0x10240e03410030b03030080042c140800e40c8503150895102c00ca40131440c0000550741500740700c0784d050100e80451503940c490300c04200c009121080380d82e485c13444500404521f0070f08000c076a650704204070520000380500349a241c460351002e03141079001c1540002c640500d582000c800e002d2803440c00304060259185809504000f0b02c400c0b40314210380b5060010b003410710340c01c2c14003034242000440e1448000055074010694580070b941440d007024248401080b000304140c0c1e241c400c41e86800e01180b0280f01d08690f2501443c80f8800850404a0030f0303002d0060b03481003502035070100309107418142d030101e50701050f0f030350078241c9080e01c0208056030348074140518528410780d50408400100c81056621060352040f1800c4e149401d6500e0400700900780c002e40c850348010001600000714401c15000041030440240d0a04000c8107450340d0b191480d12040030080c1640c9a03442009011601d41800d40c01c000d113104907200030100070f4030741d07000b0004a0f03580301ca903041c0f03c510250009196105c07070800d805004510 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 974605431 1250 974604181 974604193
    0xa080a020906150319061e031e0b01050d0203030d0e01090c060f08040312091b050406120809101704030f110f10020904230a05060907170c0c010507121b120b060c 71
    0xc2d01f06c40103501a100032240004040540e11440c0d4a10708003000c841e400c03104803112a840c1400340710503c92201d400b282e050008200c000ca00421602c00e040995101d21300024085100c3d1510302940d20f9a0303000502441800c42c0011070041e07115030781030740c4507a0504d40045100c2c498000003015103200c10000380595410115a0004c01d02c100e8100201c0d002107a040c03101d255511503944620310380c408090480d203400c0103000003d0502ca030401c40060b08500e49000420a0300c0700646024409480480000e04000c842c22052a8007171140c40011005d50040d0216104084070140e5603010540c41101040c0c000c07031a85401d40c1d40d07030700030341c038440f61422060b00548241840310300b103c0b422607544114030b2a28000c2000b9062040b03010b031166510352a5120008443c103440074010400134010311010b0f004101001444c0428043d06002700c59584801c2d20800580141e031056806112520400980703540c00700404c3e5034881a1700050343c9003210000782c0743c8074100228030140b180d8140005c00748111 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 974606681 1250 974605431 974605469
    0x13020919080a12211401090b0109090e071206051504110712050c0f060f220f0204180f0303290603040c0f0e040606060201020a0f03020c07050a080a02090615031906 72
    0x1076013048101c0d003007800c0c1721031a5030f0300c0d00211021249030b4080a800a84903c60034400000594020b8108203030110491b5045a510040904072800c030301d44c2111640d40390000d002d000c100c0b046c0c0d042d55502007120240464030300402c00791444c0c069000b011b0242c80d07000d90860040350145007210040303050b10041e07a00100030704007541da41e04002d40d8001e00043d11a4009050440d01c9a45450b2075008e0240a40f503222890b103034050407100c1c11b10240e038000c1e030350a410045846080d40c0191041d1185841c0032001c4103034117018045800500508e5600003001c2c40c1d40d0340703903040e21424440b81d5008841441c0c580d2581e0609005902036174010580500c1d030b0080104400410005061184d80300e503809024141e1101c008900340c0c001c2500700004990401100b04419000340c005d01038544403507003158201742d943c1d0005141240241d01115650304200903100c02d44c14070b10341040e400441529202c0801102891026640c80b0040070f40f00d01071640c801034014010242c01000040c16640c0c011003045c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 974607931 1250 974606681 974606747
    0x6050301020a180e040807230d030501050405130b011a09090109050603121c050411130c0311160201030e190317090c150d020913020919080a12 63
    0xd502480204402e40c0c8100107251522402500d1285c1c1d03011040c941015290341d1140140c0352200413810104850480c0800a034900f0010400708480c4e550300071400c0e514007000c0c842158005000450751706044100d00010608a262090450303040c2c1010790512402d0301d41d1141d060162814207a4041c504200000310540a41c100b540100021815107880165800c8040030034820031002959410282e940c000341024150320203913010b130245034400c07580309611000400b101103140315194100e55400c10315002c3c551512400c00307402803c80e03c4922b40350684041010125201c00700a040645072011000c14987c1803200c21080c0300030501e0000c0004451074064a101d105526202e11034110400098840d42c000174100e1402c20084c12031480c0030b8000d00324500c15400201c501c00b096800300b00d0855075484440c07203400f129805280050322402220200007a405040c6c0d070606003641d10704400d00200f007000c180b040d44180e2120240060345010300e0107603030301c100e40d804d81d0075641c156220282202c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 974609181 1250 974607931 974607947
    0x90f062508030103050f030c060703231905010b16060b2e080709050d1205191e080f0106030f0b041109030f06071b05030f040f08060912031906050301020a 68
    0x4414000e07a143c08016101b010764a0081000345c0281d94810008100c42ea0b004e94006192004500b51085407810300444c007504242090341c1c903146904100342101e0445006100c0c007030151091504003071520418905d076444c0540901e0020300656640c400d1400d055550b120498030040f003100540b0351500741388884007141103141c000030b0042050840080c0d900b40c800c8000f5403d0724070080491180d052292269442c800000c450070041c403108000c454240c4840c00c000303001d007840304ea481000010350030100002ca49240c2a4441c103005010051003845504c440d103407410764116240010300d18190020560150550042d0150800d18211000c03090704045001850240001c1c1c04a44101d2042420700d9580d40d811290840001d6040d5500036465075140d4074504043d016500322410300054070043d0446512683c400c1c070400c003440008202e0040e00340310315a80002c1070070181c071110b00740c00041c845510004142c1c0d06a2080c50007090f103014069840807010b804082c5c001c6440303192040000c0c019074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 974610431 1250 974609181 974609183
    0x3250c030c03050d1b12140d060602150c190201020f0310050418080a120605041d0f01020a050703051b15090c090114040b0a030b040804140303090f062508030103 71
    0x1004005a21000a020711880d036a80b1880212001c1240480e031686c4080401010b200c40800603e0030b10040c54a101078060a07411490391000a20700f0710707001000c2d1424000040d2005c0030b101141c1003099104070041070302c0c14850b0000683c0320381060780714200d0091152000b4858451004003d000d01c0440d403100407400e81d24141c408104d8155150050600b80300f60410042a0702402c0013402c1d0301030f10880700d07020300b01c114650120b1f520342c03a080042c0036248010051081807418981740071504104100400300014803900841c580380030008000c0c035a00c0f4014018003071190028007030680003000c0c0000c45041c1d0098040d24520021112184140c0d4400d4640100e14422004247d00500d451020349040799500040085104081300600024000d48544d403030b4820071148001011500310f51802d8400d0341320b408099038560400d10f9204002141032611406a131090000d480e0396280c0340039503640014100e80d0f244d107034417600240c1150001e000104503080d8114040b000108011440954140d07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 974611681 1250 974610431 974610433
    0xc0a09050408040314100c050c0d050d02040b0f0c0c0d050705010c03120f20090d020f0301090c0b0c1005061810120507030507120f200d080a0e090903250c030c0305 72
    0x200c620414115031723900581a441d06290020424071441600442c001d09520801c2400035051039514016061140c0000c40d840e007541100003145060300d0340c144020001c1e2030013101d01e8050f50340c440d2511360369101c00c1d000b00d030f0511404a81c19030615001b05040009040041c0c82030000500b030310b0620014000ea05409980120582c0c403001c4410740c6171082e50202c0401800000d48580150200640700d80c14000032030300341d540c402452000c2180340307565078081c09030504600c3d541d460800440340342101501c01e245900e880c113414885140c1c4c4403055003c80c814840350300c00c0c0342e80f1909100660f40c806030340000c10b40350a14001008220022481034100d81c010b03005d0f52141a501c041184010300c00301c0000301032a880903c14400100350000d191504251206440d108030302ca100071460b22484004141c41300200403502e1501e1503408090306000380c105403034401c8a802c10f0810150399000b01c2c00408450051081c9159041c0388e00c0360311044c2c0d5500412000c00769541c03818040c0504403540010b582c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 974612931 1250 974611681 974611691
    0x20109020a0509070e0405041b03081c2009030f011b03241701020706021204050f01062103020a0b070302131e180b1203040501030b01020c0a0905040804031410 70
    0x143c6400da900031311884098032000210400b03041000018080280100e45c5090b0b205451780000c0c403040c2c600d00107103200d080201ea88141070303880300500c03008804040510350f0400400310025040000444850000030044584072080707000002d05094080d1800d0100c1d40ca09004241c062150302444100214943c4007005a0442d00303628007401c1100d2488801302c2c14941704100982e040b00d100080c4000ba1490005003000d8096641d0f00990f444008030400c41002c3c04103103c2800810b2000002d0b0510b0a4004c1014a20740701e07200e1464520404081c0e0700154012416080c0741c024041040d40f10743c00340362543e0030310f004200a8000e4004040740e803a22034540304085038980320140312490820340180310424207454900c03940649074680700030b0141c3c151924280341450301d4039804201141804405142c0312400e00700010701321b0f820034441e1811540400d1008a00352140201c0c08141c072250000420503540d0380c104040381d881158002041b58600700040301d0070b00300206200201c1140001c003400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 974614181 1250 974612931 974612939
    0x1b02101e0309020d030509060d02160311030711060310090603060e071e0302130b10020a0b0a0b060301050907020c060c0303100e010303021e010609091b0f0b0f09150703020109020a 79
    0x46070142d2030001d4012941100c0000440c1c042e10107002100b0b0010540c61034031a00c0d802c00070980c0c000e4050301c28246114400340c1b04042e041003114030801c000d4401141030400b162510003040d80b0000449008a800101203402030b14044c81b07041c0070b0135214200380401130f80da10b4954000c059211040c1c803540600b0b00c0c003052030903a0b903446180000c081400301603014295000c00c0062001207140715543c035910040740c8855180c1500d20b11401d0b040c1e80140c289007041341002408154010030740c0108602d8050701d1101a55841c09880c107451096035074447c15034601b80c0a81c5010610b922440e0f0100010480d1038103400000005d42c07051384032186500e0a582d6620300341c00b00400a000042c0960002e15401404808504820480385415000440c10b56a1a4074082c22642d0440041c0c2d0215a0544154446c20300039800e20000c2ca03000c14824102c0b07241ca11000498003400560540007100000c4d0a66070703669040c00580c00040d81d241c030070b0740c6034040c1ca4003030300804002c1000c0b806012551030002e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 974615431 1250 974614181 974614187
    0x4151104140a1a0c01090209010e040512190c150612050c09040807060b220e01110702100f020c131a030109030801091808071103061f03031b02101e 65
    0x1158040484a0200c410f1040c1140040c1c120100041042d9030317400e00c00c0b000d42c0e02d91582e80c0c002e0181c00702e482100d04040c140103040c005045485640103100b000444208040b9003c900b0b100901480c0c00c4c2000c02c070914244c00540302c180e1101000038140341c07001c9041d407444107011204510031011540c0905502c0c080c0030001104130340142c03580030240070b0540455600c0e0003034084060020501100b103010b10410a1800d0310300d200104031990745142000c6140800d2050001d07480c00290414285000c0c1da00080c40c400030b00303c0220400400581d5100d80d903008025015808a0040c03403180614202020030780208000303561044d0551006581202c03c3c10103220717051415406640e10383c03643c0e00340701c842c03c0502105942c01800d0102c98a143c030104130148040c120592083e0100610000c04000301031a000015010604d001a01c000714800716000820b0081200e07458105105408642c0d205200002213480029402038015404c5400040d0320071000b103402a000d90046070f04840d564421 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 974616681 1250 974615431 974615449
    0x110901120b1c08091005090f0901080601050d080c07121a07200a0203060406050f16091503022206080a15092007030906230d050415110414 61
    0x154001030369051803440810b0464881d000c060064595030302c0c000b04200842c942440c0318104600182d40440d00e10324030301d4015414100d00c40708a40c2181c0e15414034241544421043c42620f00c2880400e1000d001c01c40c43c0710a940f024990740e07055a0000b942e8114207079200c03030040d1080300c4224030b110050850541444007503018403030a6441d600300c0c19182d5050600c51400407042d0394a81b0a130141c400059404003d62803080c5d10464011402c2e050204c9240040000500844481e581c074010803071015a0100c00f5000300e85010381c0c101008070700d000e020360080c0320f050310300c480d510020a9280b0100c2c0d50310300d4200866480759a0590030396a05480302c41107a01e1158070000080d140901041018440c1e005000d003004c10f0070400c0c1c0f98455105800a26500022007100403c2e0488020440315801264682070380c204651042071001ea928548040c6100f0268900c1145690300045814000401004c0d40f150031580300412440719074003d84800c0750031603c1402e103981184580e0070b55908000000e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 974617931 1250 974616681 974616701
    0x5030108032b0f0603051504080a080615070308091c020717070b03010e09070e191e020c0709060504020c070b070f0f1406130b010611010f11090112 65
    0x103141000d989010041c2400c004442c455250075500d01e01a14041c0140b00f481c010b000f403814005285480d52070820b040411480304044042c440d42d04010101d8004021034860009915003013107141d40303020010b8051810a03040c40308112021800e80205600103032a82d000b0314940089070b400300303442c3d503012050002e03407182d907001604180c004200107a240c980016800200e070091f0385000b03850380b04104039a08242e1104403030415810134000c0150062200c04043c02071002c506007240b820760b2216041c08511742d643c3c10015500e50304004a1b140e5106592080001c005080d5540c00c070f0003241950314031590064207106440c09000048a207410320890307042e005084060140d552074640c0ca03402640140c0804d60301d09241c544030340c00080d580c0021002480c881c445140402c4d02c00100310b46020801003c282d11a9400e000010202d8080c4454074112681c0303241c4581c0055541d614140036140d42c04401c40080d0074280c0d1210b011034203030060320400c1d4081e41c0b00140c410054000c0c0b802c0e50f0507a25 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 974619181 1250 974617931 974617933
    0xa18020d090f1401150504021e03092a010914030a0b0403030e070617010905070210020a1d010e030a120e06040f060e030a120804061407020a14010911090703090219060f05030108 78
    0x801b0401801d0a8000c2c20b1420122000405601a600109440c5900440710521686c10202001c0b450380703c0d00145030404111400e0020f140003900b0006070035010b00d40181d24910700700983c4400759a41c20082c40110560104140b4018140b41c1b90140203401456265040c034001c1020101d00144a0711844050000c40c5042c402c859203450704040c01894013920910440c00342d07010f40d9400515500003880328040c2903071180086150b45109158241400300d1240c104000e15a070000d55a80008031100390a03040302815001204070340064810840000c1c4054121130041030008a1408020400003200c0d815215030318004070b10000c05468445849008149581200314010324901ca20409a401441010002042c50700444403103688401124071354010380c0030006500c02c01200c03181540c0d038900090000d01034040d003990341c0140f42c400240524041d05040c40004c4105100341c00032001290084c061090744103035100306560555840c00b45e0408244640403e008683c0301c0c0302200c0c12038013498 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 974620431 1250 974619181 974619221
    0x1c020114031003020a17010c08060303070b060a09090c0906080303060307090c02030f04080c030c0301020c03220506040e160e0904080d0f05190b0607020a18020d090f1401 75
    0x21030841c1c10140101404024580b4080010303105c807400c9a001d80200035002c80076292000205003580d500c440000d0400050b0404d100382d585000003903600d0700b80d21805c601e06c507980f000086100d0804960023000d1050510708400e041c40410440502078030140d44051082c20741f10180181ea0b4031082e2005a0954001e41007000100d42c113034000038001880b0f1040d20b00e0003010402504403500950001b02c0740ea082902010140d150401428002880940003941401c000f40362260300ea020f15082c24030700014062003032034008401d03c030200151500405054a8980b100c07608046d003039080b90a960240e41001c0800040342c040e022031075144100801c0c020380c1d0740c2c1d01e130355070002d03500850b4050209030b440d140c04120704e42590080074811400c0501202c0007070703559180b000c16036a0030081b0501440c010440d120147c0c80e2100d415041d00c0c00c4a01078600306107920101d50080c410410f01125042c580103951040104041034a404c0500601c410f9420383c501c0c4441500700c49080410000038a143e07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 974621681 1250 974620431 974620457
    0x2120c041d131a0601030b030f0601151b050120040f091e050a0c02071a0d051315140105040513060e0f07080303330402070f05011a1c0201 61
    0x9081c800354001007007202582c00020594684908004004800064003081800c001c4103503418410b24056160803401054140f03560908d440c0c880006001c2c6140c884450702c484074010b40151030400e070420b541c02040c43c055059052480c002c100c0901c0b2207090580d0000280d5080e82410203071402e8640d0010b035920030a04e0072072410001d00c4030408400310741e0b036401114a041c000038804d040c0714812000c004a1030341c408081c024206281394000307200049400c44080b0071501e01605492505060080000302a00d5858200c054071902840050100100301141d202141c0c0ca50404c9054003075170f440e0f1a0881e41c07030340b0400061b90021200d108403c1141e40c2e19002040c669000310b02c1f2130946a060707900788103039840810f090140300c0d0810308895000009000185c5050130328102c45000b107403000c261004a00203841e2010940111640c401d5401107541030a0001d0002099411580075008007e6291006a20764000e60400f04080c0302c0c170500d40b84014000408103a4040041e416075854226900c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 974622931 1250 974621681 974621729
    0x30303090601061106151e061603111f0c0203070f030509040b0406150f0504051332010b0a0201020d050f0412030c0e01050f09120a111f080916060302120c04 69
    0x5804100c3c401071071101f5000c0c952105001400080c004090010040710796007805080900000f149560680c8074484803281108014000c9111440d03444010901c0da9407982d08078a14021280040d0610745210014001c164011008280c81141500c2c01d21642180307804000441f4a54400ca0090156907100070a02c40d22501c01c003181040542402030074180c4480c04244031500c074100b10300100380d803071081c1601d030080d082040c4182014070811100d00c1e50b600c408075058813018807500c40a95030208207031403c24003c0d01509c07000328280d00304200c9450801022800000c09407025652100241744045005c3d00c640075070006600070380c03622007955500000442c0c003a40f1601001c0c868501c244000c908070392703603580d41011041c12107004021001d070306c5c14070707042e0781041d0a02c081c802c5082c80d199820302c1c0000102104d039401d42c1d06142751070342e0ba440183c07801d080034010159200180702c140401ca03550140d0190462415080100000382e80d501c0e0801c3c43c82c401c43c000c200301448a21140106050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 974624181 1250 974622931 974622949
    0x3060633020a12020c15031512010e0d0f170c090d0c0302030102070501091703040b0703020d18050607031d0c28030b0a050705120414070503030309060106110615 71
    0x128500c1122240d0241d030b120f4040380302c1c19074150300060300003d020070210302c1c2040c45100c2c0a4a00c10b81185182400e410010420b8031503000c550182c03c1d0308405241d00e4100790321003001ca1519200b81c603815101e44c00300400140c04d001c01100440c1022503c41c001d46111a4254810750f0584680b41c6400701d20000c020802c0036020781100c1503035141c1408801a14280040c1c4585842180045034520300c51a0092000d42070520484904200348204808a421142ca9580008080c1801607544038006140c1c0301030034004880780c10348030389103540e2010032200264080c4221440d9408008642d104034420b28907168030030301ca0b0900d622140c8907004520b070411308850299880100c4521000100c1c1c0e07107404455461380141c40290355101006805041e600605900aa0615000d454942c1104e402114150080c002402c1000c5038405801085010862030000d82001003c40b5128605181c03d01daa038103090041c040001c045032243d100719000000c10a0249400d69a8001c24030700788403d01070211 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 974625431 1250 974624181 974624279
    0x7030815030a080d0f06120804060c06090204022b0c022d0d030501031e02011d0a0b12250503010b0d0f110901020610050d0b1801050f01030606 63
    0x1000d80e21407407000482600050000004c080404140c800741c0c3c84031242200c2d807981c840300e4102110851900080e403d417040390250b94607410182c01200e02424000c0041150b450025001071001031101507007440030b6038102a40d045444420f207441c1409030705500b61040c0d060410050f901210341030207502404100061040c891400e070302c00015209007050310307100116006d54042a50b860042c8203105690039424045202d12840384ca0360f0718142d000030805a4035200c11b500c903248081c10003c803030780c2d03094103000100740381d5044c691500c4280820390300400055074110722142c01e041101c45180000c8030041e0040b041030f200c0900350380c03800813000642d900c802c440c01c00556440448121301200c521481200f20160683c2c0c90311030007003400291501c2c401400740342c084100000c040181d0354079180d41d4104260702080f45642900e034008403d00481c6040c0c0f80440303d5080c80c007044928101210110b0403240600424002c2a03a00c5624402c24040061300d60454501140070000c200f1701b02c45030301082 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 974626681 1250 974625431 974625433
    0x3110409111918080303010e07080a0b0907090f08060405071215050705072312090607151506140f071a040b09120c030703111608070603050c0703081503 67
    0x80010001110000d0140c1030035140402c0b0b45038400b914500c144203401e8013801c1410004d624650400d007039440b4007140209000100400c820001b04000040e42010b10440005000031003c1e08206c0700180110032607010351070690502c40d0000807001c03000511a0300698100010f00350850070041d8104e0001800102520030314035070642b10380a0141481400c0c8500ba01d5038810303841c3c00c0c0a01e8080b041c0d14940022055240307100e0a9000d0441000c1000860300304401219651142c121010075940d0254001c044c06000242e404401d140b00d194100303613082507200100031885a240d000c207540c840c0c40d0b25106040380720b090001103981c9002030020900c142c003402d04c03092a4000b001c00e444207104200d808955100214040c00045041046021a12801a981181041c118010040d0380340681d02c0e010341000f00403051075481a1050002c20110244c10040c4610f003a216062280c5d43c40540c41040002460800000da15001400503180131039416590098030741c036002010075484404200d540c1e89 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 974627931 1250 974626681 974626687
    0x601080f01110415140f0702180403021f0e0303010b032205061302150304110307120b0c070c0e090a021f050d050a02091002210307120f090c080309040501060311040911 74
    0x41700300d02c40075180001c1141825a41e4880314810f20442d03841140340200410001414000020303004602c0c485082602c1740520040d4055400f2440500000090000360307010000010564014100c0118814000403561489a030307600c152102c260f0481d690302401c190459804242020149488031441d140020001c0c21150071441100300254001d850844455042c3e2203034151a04081c010b5500602c0380350700c0d500500d0a542c855188020009000f80e0248000203100300810070401c0e100406400c1251000c025840c00100e81d503511442c01d6020ba01c2400d000d0041c3c107190000c44103400c02405996680c0b4103007050f010110700601009841c114400d03800f030040c0e81361616074070008841502103a006000c419228807080280f02103030440e800307400c0ca0070001c2010141e0001b0020780246080c00001030303a22820722103400240030982d802004003141c00000101c290001010b0000c840c0c0c100c90810650760385600a0702101d68004940340c0b401c01c01d010404c02940140d20142c032603038054141900e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 974629181 1250 974627931 974627957
    0xb1f030f110108100b0d021c090c1707030206030603150f0f10140f0307030611041412281203060e060316090902030102090d0606170a081207110703050601080f01110415 74
    0xc0b007032400340300c0d103075072581d0301c10305402d0140ac81d600c0402440c1c80494052052000760842d9191030840c080640181000404a541c5490400090409281e00b07148040107040c00e00304101c4a003c250340103403440e0200c0c00401c54202d40d09190504658444880300301f4103400c0024065098040c41c406035240c016045c00101003005402020191980141900e5540e4240315050303100035600008a8010702c1520901c002c00e103030000e0ba1900701e03820800300c0d0071140c1495200140410515070000d21046a144454a06e1900744e00301006890400100c050181d456009169903600c80152003061842140010081c1c61803c0d0304c002c000b580080c1c000f500c0c0c0100b072000300e160713009100001c603081541c5101c10064060048611100a030334800604400245603c85403c5405070891402004081d4000b140722103000300100c4000310003d20030344480c070740d6a080054450100b44500c4040d401040f54211907580e040c0b069a800d8289038440701e05240c104205840c03c1c1c4a1203420200340300380c0c600c00c41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 974630431 1250 974629181 974629207
    0x209091f0c090f080c041107150507030624080a020906070c030203010b15030c09040e0f1c0f0504090b040603080403060c030c03090209040b1f030f110108100b0d02 72
    0x50880340ca0600104818150560003441e104840c2e000150300320700c5000620868a010800c0401c0100840700840c815000e0410100d07188242036005084004d071710401c101b40040340e0001807013040d00e42c404000042e03507130100e850010200d03a8196040b980c0f003030f40e000000d8040c1a0841d005013200c40010306240d18580844e007140c1c4105015515010164820811031400f4042c8200882040d01d00394038035444050b00c644c0e680005040c0201c564030100f960805c60722980c2c00502e5201100b01101d030861600c0c00030700d45800c00074444a480c1050240811410b601601702c051150b49255140c501e01441c103204d2030010841022482e03032041d00c500000000c41c070b20030003402c05513020314400100c8101409002d022107028242130001c0c5030401040700b0250391385840c4258000e411003000681a601c41e403803c018401d04914034502d502401401005019200d82d2082c0064440d04020305900c500c00010b54500600301d4011520324042142444030201d080c004c0d04c000c07050100f0140c10701c02c00d01064 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 974631681 1250 974630431 974630473
    0x30c03020d090317071701210b010905150a08030a05070f1403030f100303050702060901140301150801080c060304230105070e0f010908070501030911042c0705030a020909 75
    0x650010310701130411803000036901d5500707422415504042084101107411001d401c541441141980f110b1214000410700c110208000c01982c413042c2171030107685400000c00102402d0300c801000c01005111210941005a080c50070748903044021420402681011503460303004100448104480c040110b001590400c00804003c6c07207040038540381d2400000b45246c08000802a0072010081802040800c0d0404202c500e15a0103840390399544c5d40c80c80060342c0035000103c002000510000000446031104403c43c0404411903840d0b915076680c1d0361a041e51242c0300a0007035445841000070074002050f144141050858603044000d241c110084010f0844401711303040f2002c24020b0b500c00355140303052121904600d40900386011840e042501d4159142a130780203c0b07041c15643c9421800780002d5174400d600c1c40d80c000740244584082d1540030721107500e4031447c0207244c0c003414500081c282c40100b0b2440684030040c000305400340d80d98003003002401014102c2905400b40c1707900040c0d900c1e5040345d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 974632931 1250 974631681 974631683
    0x90d06060e13050d03050c09040903110a1412130b09031c050405090c1201030605090f1204031704120308061c0c03020f101d0a0512010506091312030c03020d09 70
    0x40d00d1042d86040290502c0c20810390403007010301d850100b000354501c2d03105407840e0600581d00015410401d00e001d07281141280038201070f501c5910201c030308020610001382c0103501e2031026a10085200000c18042c2e0040c0210044800c2c048001800001c0c1244090070b40400000d048981680d24402240200c0c2c000c80045000586c2c00a0184001d081540a99420070b00d440303419481d208481003003507010b51041c0801031029460310081584c041c0108100c480d082c029605540c00112594503a1405078404c3c4000c0360004006070038485002182001d40701100c080c151500c8078040c1c140c0c3c0c112840725006081c1c40d40b101003650008040c8865101e903401040c031821541000c54114010080015240351803d482107014680401c080c5a200c03000e2041e50190300ea404081005c03901c00107103d52610341201c0e8108203107490800760041c054200c0c60084d102a141c04600c0d40f214032107040220f40404000d440c6644010126409070322940c010130505840d03280041c103180740401030005842801c18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 974634181 1250 974632931 974632951
    0x70c0f0605120f0c0a08060103110f0d0605060a0f230c0313081605040e0c0d05062d04080d0e010501060302040305010b0a151407081329090d06060e 65
    0xc2d100c1c00041c81a5402c0760440c95400241c074503841c200009a80360300c2618101e6080126400100700541d0094210511070304904001540b40c038264400c5250a0b00b110040408a40c1401d50002c1d041c1007050841d424076105c1d540b00c0140c990302d03090685050f002d011005090100304400f0904900452015150088241010f940e54402800d00d0000c84103840c3c02100441d00115a624090844c1e82901000c032801503030041002d4102032010b906103040c07603d2003900175010b61140403c10402045140c480e2604071014200b008500c040103600300c2c81480e807801200200e00208000c40c00d00c6001d003200c001c0300a8082018500348500500b5610203074022130100e03401190a2081280070301410740541400d071060304c00a841c0c805650721284000243ca41070141c0b0342400c08034a14000100d807041a04403400365170301d2041c403c096002000d00d2250074400c1188911f04440d480301041040c01c0345000d50405420300941c5010816030304d6078101e0841755180e443c900058401801210240f01d00a420 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 974635431 1250 974634181 974634187
    0xf0501051c0503042c1006050d0c050408012a0806060327151905090604020111190309260c12010f1407080603461202010e01020c060606070c0f0605 65
    0x170b11400c00404001d842400c080c402c0410a01103039601205a0340c1c200141403000c250340d1080c032400d6800341718507000030794294200300f4003200d41c0140358541c4400d00841b00341d0750112203070840d0865040409880807a4010000c0022459210906040c07030b00300300740480b0180002105900e10362414001d040703454640d4042c01c0411043d01189510007041e03d05c1100140403600d440d030b01c01915110002c0c0f00030b041c0b0014694246620404101d0740e8403c4800c4500303003000d4940380c1000b400d840303c1485080c1044111310b01c0303040d03501944618a0f00701c0c0c0072507008042041ca4082008800c1d4031a030030000ea0b030740d030755034455945583c02e004d18048030304d00010103da030f8103011000070440a00102158000d910120413005058001005c0c2e090301e2061028030a800e50f041081080c0000600c00c641c1c401007087e400c020140401961b450444034016002005049803429125007030780a41e803001d6180360000350008820307003481c5008080d0b06100f0701040c070300c40d511174045010b24081c540050001030004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 974636681 1250 974635431 974635499
    0xc06030506030a02010207180b0d0c0f051e01080c0f13051e151602040903030b12072105011508060103110301090f1e020306130201030f0501051c050304 67
    0x510039141c0048059001d007801644540010b0b645030502c4c488d0480300509a144030344204c605901450744604000c00c2d4001010881c200301328006c641d4001c0320404082c01e880000c0c1c5103002c0d4001c0c070706000c40c8041041c0102c0d00200644120400a06414001b03500300300540030b66045030010000c050b1140c203041c1960341804207011401c2441e80101c0b84c44242c040891682d5503c803400e4000d107881c4160002d540d521f101d18108008030011800940090030700c94020300301078043c0c222040603030061325084000c40c0c4500700580d480394680300c1d0582c2c0c0304041e24504201c0290307001c000c9142c0d0240002003041c40c04a110b160481c5190340c4801040e400c0b4a0041c42003244c00e0700b5017220b48100314004e20200c011901d66220396566014000c0a00e8110754002c1d040050304008220360a4009040c0d40b000c1c500700c105190b4403140404205e0001e4901020b4042404191041d2416103030043c00e00410340310442090075001800d60810340b02e620080c4000901d00090840325000c01e203124401030226128 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 974637931 1250 974636681 974636687
    0xd0f0e0a03180803041503020f16051042080a150608060a0903030b0a060320030c0a03091a042f0d1b03170408060f0106051606060e040c06 61
    0x400d02201202c40c98814100800e0b200041550306503644a00c0714041d11a42c454154001d2003815038a140c2c04602007040c110100f9244682100e1a0140341907411203040c0e0f90b0294100c624245821104001004401c540805030000043d02843e414001e1243da4882c400b61500d44001503011416951002c240e10080150005480d220030bd220401072240c1d0381000029038071000c0c010080103801d42d840c08502c05051083c1c100d06540c060160078030008603201c9500802a040c0401c0c1c10034940c40500c80e54030442882c508403441081a081e14905102c603c09080f405030080d04000d9603900500086844505200e60300e450085125580700e02d101440ca80e800d0300ea00d8520100c0d035a00c448800841401901ca46508420150784220300c40094486c107d04191428499000540248610003e448148410400400030b6442350700864101e40c0c0d80b035224444250090056074000f490500040031650061000b100045104460100e0001d4960f10700c40c41c0b070300e0200d07000da5484000b10b00c01c104040d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 974639181 1250 974637931 974637947
    0x302090102190f120f05031b07060c1107050d03090506031b300108150604021308010b150301060f05130b0a0f1706030706050c10180506090c01080c0d0f0e0a03 70
    0x4640c14602d10f401207103440580303207000040c540302c0030004614072303070300d2407000b030703000c8858055005004003c490b52901c0001d05200450411070f0703640c030803480c0c042400d10303001c0241812a580b41e9030b1828080d01f070000f0301002d40c00281c8021500d03101ca040398082150500f0103410180c3d09401e4030389910300c68407076140560030680c0c881004410001e0040c0711250000c288444045100b2071030000544520300410000d2081040d05102d4803044480420303034039010f40140d560490110707041440540b6400c1c1d5513080748003e00c6481c010400300380113016514001c0015103d80c08950401103a10f6a42e0001400b996001062420005502c00d601a80c016041140a459900711000d200658540a40866965031541c01002c0a00c207010890545980382001800c00c444524081800108000000d41e402403440341030848440c003a00001803128500041d1004004e48141d580803d40c1c0c0b9401e55500301a4400c1189101030380c4c8a415103a003e07200341c099605d04086000060105401038100140894 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 974640287 1106 974639181 974639213
    0x30c0a12050601050907050a0f0903020618120705130b191e06050c070302010e040912050912030f0304141f140a0207120302090102190f 60
    0x205181000081c4100e0848809980b55000c21402c81d80c102c0780c0b080080c0301400040e5a41d84264120710380c0c00501e00b0195145900d030b40201c2c03d168042a21005040700d0240701e440181000d4100700000030099025004850503e00024078034441042e508110a80783c031a031240c56030b105004008030a184516501d002a43c90502d00b4040b50000300303c01020082c01c01c0050701ca4015001c039140141054082c00f4080e003182e0041d600c456629a00c590480e80d0740601c1000264a1000401103540f0f5031540e40d02c4082d000104030340e10f6100e404801858009000010440c5c904000f80da4209a01c40c801880e0154040b01851504400d58844907031300c444500c40c4648119944d008101e600d0b000703000d01c001079a0740e071052411f9214405005005000e14420070000521a5021b0100440e0500c191007000d03451111070010a6440601500c0c030112500760081040500c0c29680030301 = true := by decide +kernel

theorem cover : BRFrame.Cov 974460431 974640287 := by
  have h0 := BRFrame.cov_init 974460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 974460431 ≤ n) (h2 : n < 974640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
