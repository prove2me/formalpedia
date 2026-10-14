-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2066
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:34:50.374983+00:00
-- url     : https://prove2.me/submissions/67cc9322-5341-412d-8d2f-5ccf7285c97e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 371402877 ≤ n < 371582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 371404127 1250 371402877 371402879
    0x50a050607050703090e090d05090d050106141207050f040c11030a090f0806070903110103321008150c041214120405180403020c310c120f0e0115 64
    0x750f0842d14076001080803c1c0c1b01e1042e0f16118011941f2034103070140c01410080001344c0c0000c82d81d40d1140d4010313407070340000003003101036078904500d807070249680d0704280100c84c245403c07008860b01081c44402c54202a00384d0241a000000f0400200241c08000b011710000341004201d0050030000381c0761400040d15429074260528a240b640b075510340d40114000d078404010000c8803940000c0d071030200c0f5441240c1400354523850700141c0180104034081d02c4098907070414644058280309514420a040011401c0d60340c88625103035035504ad090054000586c89485c49010010064299961014068a0490802d51650241c5201c260039450548181c9108281c0d000517510038050342e145042038801403403401c0d15160104005200024550501000350030005043c10b001780b00b03910300081d006007640010703980c0342d01c03a107191480c0030030f11048220950b00c0d080030000140b0514001d109607803540c507801c0107400d00081c0900f0300302002d6031541b038031001402c548140900502c0514407100c00c0720301504d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 371405377 1250 371404127 371404133
    0x60a0902040e071a0f0424121a0f0102030d020a050324030312040303090f080309010f0b0d060e010605061903060603270f05060106050a02100b09040807030e0a0f05100c0201090b07050a0506070507 86
    0x1642c604402c2303c540c58038089800b9800048420183c1c91a41c00391f030030003044044080140e00b50301460325100060f500000c0d120300c8290344540254030418501e07802c191402c0750148840404080e00780d1064142d40108000340020610a08450f809440380c5400710b0301a4055550807050508550115805d80c008414885009028001c180390210740c080b00f0049100d503440014001004404e0103032100390782d14080101c82c01c1c00e40103100506405048030f03596a15031103061141c0005c01d001400002e03d418404110f1b24481e000b000300030f03c00b140e00c4645100d54521280b0341c50103002c10480c1e4408050038038000080d0305112890003090b65407941c40e150000c0840c06070030304802241c4100784510700304290a0540d0f500f40165086a00443c440c2c0e00c0700f8581c641510943c030011201548110001000a09250f851000400350390040e541540c4a899003038080e6690019110024045200c40c03c0910450b00c43d0310181004030700500484d030700800c2989520f0b04103c42941c1d0000040d000060020074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 371406627 1250 371405377 371405387
    0x140f0403150c0e01110c01031d03070c0f0801090c0b0a030b03061501020111030f07051e0c0601091a15030705090409050705100c030905010f090503060a0902040e071a0f0424 76
    0xf441c4000c1c20003c10390b0440c04626515281c19107400307818581e0300c40c038208200100b412a8072002d10681c007180d0b036850090500306a001120710645115140d400404205024103001d039000704c65010040383d41c030506103e445401307500100b10201c100765032009000c0b07a0351f404128150080f010045003441c8880004002400c0d0b405035045003d0b00f010400500c04011310352907001c3e40c8a0b0030b52400790307255040d8464001d0201c01034502c2280715900418441c050410200c1e005041b58443d901c10007186040b001d031008044050b9500c26407200d1a80400080e4403245030055910103081d1924501d8024243d0000b0112001c0c00c0040d140c42e07002c09014003040c200321803a003650140c9400c1c0764100c20b145950040400314180105410003a40d50458207100303008500003400303002c00030142c50f240d20b00004604003c1a0102e0107038426410148690024a4007143c800107031003550101c5d9208800c0d184000c1410703070010180c0000b4a40070000001d0b8108007030703160251403600450302e03960080754070b400501c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 371407877 1250 371406627 371406647
    0xd0b04050c041413060b06031009140c07030311130801020d0c0302030907150903230105010b0a0e04051302040507050307080f0610081e011403070b0a140f0403150c 72
    0x20003207140407220304500f071a40c00640d50080c00002501c01c11034041c5080e102600b01801c000e60043c2d0040144024400d039a491102039802c1e8002c1001100d16012000030002c40503500b07520110420002040440e110380c1210441c50102100b603882e0030440001205003030480d50001000e65808542003403815103c0c003403020302e014189025030840c01c00b0f90015881d10040c0c8070707038044888040d000a000a016140d11f100868001c0441c060b5030054030002c02a0408400c12840c3c10f510300000480d000d100d89007641c0070542c0c00d988221171000090240320041c20040c00002000710503110000042e40c0d980940d40c89074078507544030750f16400e0046001d8841440038010200b941c0c03240d010040303192250f540c110b13480c1d000d40c0f42c03034019600d54030307200441e4001d0210b5501c440b00b000000811101d4000c1c9a01c0e020040580c21941d8280e551810701c08680100202c1c0c40c000340325510064040d0f0040d03005001145030044c0140e2034607070380e65a0b0007406449551703504140340c0c8909c403103801140c104441071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 371409127 1250 371407877 371407879
    0x10b04090506240c011b05030402011e020d0e0409061a01180302060a08041a04050708070b0c060f06030715170f070e090a140c030603010c02070e13030507020d0b04050c 74
    0x904498880c0200f50300d01120030085007010100451140c007140001d42014001c0f20700c2041c18404000c808600800e60350084030242c0c0401d00300e8031052840710900f100c800301ea01e0350b40e0103005c2e880c106560483c3c100004e152642c0e40651994a1400030510621688030300404003212444100d141500142480400304410004192a02e200f0800340c0c4440c411648408120700c0d0441a41d40c0f2490112000e2100744c47c003501c4240d580003000100b080008401c0c098884034030480300001d94840b40728500b48500500344106422290200300fa406e0401501e9410260041c02e0703544054440b0760751721480b49403103102c9000480084010300c040041c00b001035080fa07400140c2495900e8046800343ca841d143d060b091340031704844000142d101c5510780c08003202c40c89522490000e414903580103021a00141d45d818440d510741803c410000e0300001d4104121034003003101c0401591104050303500401c0690f000e4062000c100080c80040c1c0d94400140b40c900c1c41240c04800794181400c1545c030b0140004c0c915 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 371410377 1250 371409127 371409139
    0xd050712121b08071e060504020a05060f04140d24051503190312020a02010218032409010914030304060b04020f0d020f0702030d020604030e0102060f0106051809010b04090506 77
    0x2500000c5241c003070980b4040d81094038199200c0b00d500d041c001030744907039440303500300340040a011080010b00d800c032501450085414102c5103031507400308003192180b009110642c00081000704000c07403e03070b44400726889000300380350710600d980e4a03545058111501c03001c1d20204075a48251031003031188240c03a04114402c01d80f0110b04410000710766a0b043c210000c2d466540400031010806206980405480d914644103640f80d01c62040080e010317400c0103000a4024403483c00c4030909060000745440c0e0306440792641038100c5182c0c4944814000e020300070410344d54845803504081010381884002c0a440000203503a80d10b081c0c1448030031603043d4107045214600411025142484100c142c500004a0b4480180c0d1162089400e8005d489080d400039014050030082e0b10b11681c020843c28403a60203174450b10700e00c0030741200490b20b6a10848c0c496404c0f0850b10b0061040ca0700c940060901d12040e10b6801003981085c40c0040c103500000da100d03c01d18540080d0034000301c1c00d1400b4050b00030400380c1d41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 371411627 1250 371410377 371410397
    0xc1b012a030c020a08030109050a09020a141e0901150210060e091603050c1009030b0f040201080912040902070206130b1308010b0603041b090c050d0c020c03060f060d05071212 77
    0x1170200c01d4031040c820310021640302c0001c59406e012070342c0050021355008181002d659511034403000140c00032419140304205d4007050b000782c400c1c426040e2002040003003008043c0c0e802c0c8a400100d2400720442101144500c071405071080805114090240250392000c12031490001c848515043d006030714414001041344041000070380000e464180641e040300c020144030079583d011116001c0321344c4098080d812030740c2440341010381d05042c01d00840c001e0f40c03042c2290740d40440240e602c0c00024140d0240c03080c02c02040000d0425507000d00300c250310003450344d0324015090ba00c995800780650000902504002040585050b011084030000c080b950000d02250750130b10005001070100a101400203154000383c251911100351541c009052881410800c2040400d0003e0141d00000c0c0c00386029842c2c14014282d4500009100803102c2005000300095942c50110002c00400a011190400780c0c90803405d0001e5024072a074809444602803414900580341880d21200f40d070260418240042c80316 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 371412877 1250 371411627 371411633
    0x804091e021204060c020a05010f0b040510061409060f19020d0c110603130c0b0913091101031a0301020a1d0a0312050703020c040617070902030c1b012a030c020a 71
    0x1800d40d900c075030001130020300c071401c941c005c1e0700f0100d48600080c00b5510340002400c6410099000c91001c078000e5408010b00c0d134502d009400c40110038010180860076080d00d00c001065048001c02d4041d07800b404040c10070f41e800322a500790381c0266529001c0b00703401e051400810355040088161030320071850500c0c0024065110039100c00400356299001e60000400a41c181c052514036100c00356004031101c600c1c940e104540340d120f4000200b0b0354424050422001c12440c1240203603582c41d90803910440b0041c000b6001540285010680900143d06403200d018003a030742032000e000300e010300da1101e64000702a9594101c0c0c20034904641481007520710000d05c040780c0c03803580054001c1c005082c0641d0f50b0015040503440c0c0040080c100c0da10a0511201283c0d1840d010390b400980e4081400300d0f081c05403207581c5801a400b00f19045644242c05011040003807444c00c450820b22000d281c00020204c2001e11450010b40c115071081c8444c0c4c01c070202c40840d20750300d4862100106828800ba1100801c19a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 371414127 1250 371412877 371412907
    0x604150506040e090f060907030b0601021c081506042c25050408060709051206010501140901030219030615020307030234030521070f0b070504030804091e02 69
    0x300070043d819030118001000c00c001040354076201070340c4a04a0311980792511442da078400e0540021100c030b001c00b902151541d400000e900e5000200c880c0c02c240303440c5a0010440388042c008004030004000000c3e07144a64880c032004001800c0c151560401d049024480751001c0242145083c085030502da0410001c810030034017503900320a500c041819040504038044441c1c0c022038005048600841050111039174100404404484040c1c4140030a80c900d0070081d91030358000d12034140824258440a80090113180081400c141c050600606201c0461080c520522800d544100483ea880d542031101e04001e102d00040b41c62240300071881c0c00c4090368020f49502000d65025001080190b240041052a000031a8200c1c40d8016018885650f4280191f551480040c08110600380c4c507101520580d03114211400550000b00c821000c08582d44ca11081241c0107040500b01f00b8180408000600144020002007407000e03800f2038201d020945100c124103200350f02801d000d1041112900b001d241e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 371415377 1250 371414127 371414129
    0x60e0f040f0213321503090a060b0103020903070b130306051f0b0315130f0203090c0109090603050303040b040c08030d02041401050909150103020936010612052805060415050604 78
    0x1800f09100580c810a01103185c821400003421400440841001380803240081d4080d0b5803402000d0078054a400517005504a00c01c640d4000d03010f4100e824140242081140180700c50394404901e10002c07960303074603a04111141541d00c402c02c0d60807900c1002c42c443c0359a2201000e070900d6100f0502d1030522141c841d080b18039160009014101b0385a03840400c0300907600c00481c0d4203040c0020b641d03a01d440c040c1ca0361144d03e0035140d6404166030034408140c0ea03036548501000d6070341c4035004518580b1252a44010000700400c01ca0751003507001c00205805400703001404011076030101c09a00d9504140b081d01c4421410280e80f8100030b4240220119942d508601540185210710b0414100b4403010040300039116120000741c00c10740c040c083c0b0704500440d200b9a100c2e080d2000060310060030350303184c0c5a45400c00384203950014480250801d00600c055200503004410034840c09409900c4400010000280d1400c071015a070381c070310402c031a03424580103c61145041701c01d1900c8a50510000464901407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 371416627 1250 371415377 371415449
    0x312030708070c2120030f040302090402190806010e09010203070c02060706060e1005040f02280915030518010b010504090b0118290703020304060e0f040f0213 70
    0x2d810482c50910400e1200003c1210807104050001d500001000d40074002d00c5c203d9403802c0d50520407681c0402e130084183c59010603486969131404e4515000c0020b218405403050381d00440d003400404801208081c0c0200038800840036100300c0d1301d04040c83c075410f01e00602404039a4010803c02c02d03075544c49119a002d541d0b040302c1c800d4482038a800c10800810b9142c22031b0300041080403e010345040720a8208040f518121018000d122410803054244e009002c59140141d11080b110008036400144903c064950351a000b201941e0341c41c991000050b40000c0c07000843e07a1241482244452910036200e4200040c0007401001c1d26a40020106e1003984940032084d90303600c06140c030a80c80350514183c134010001b40d44040a40300c014814102c40300100300400410384804010f034a8190400b039455990b0140c01650030300f17180110a880d08045211425840080100b800a455585119040401902050060301c480240a40b8101c40e00103410001c010f40401c40c01e20603440d0381c1c080303510207148 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 371417877 1250 371416627 371416637
    0x5010c1202011407051306031407050c0a060c0c0605060102060618090705120708010e060c0d090c05041509180510020903030c120702010f05090f0f131a031203070807 73
    0xe8009003240101207081451103031050341800d01a05980c880040c000406201454442c41951040241c0444600400406e09510340200041003039005002408440c4d0500095800b01c000990324141203504100943c40403405842e0f0290034019103100b0310b580690b007030000300103a06140001030182d024211808041c4c0d8000700002e0f090410500c82e040080c040075114148500000c0411902c880721401205410362a18840a0310248009007050081c4041520399251010808110000d8038030307028151003c4900303200025035911944181d9600e4201540080e00c03107400c249402056031322b0300c0303010071404014041c01c0c3c0c003107140440d0808020040384001a5151840341c04030b415030040315248030030b80c082e0340c44c038000104546000780300c840d20076a0383c2d00c0400d584800075241030081011142e04258005485400c43c1000e4050400240d40200300e400100603d081210a64840f940c81110b0800d22118080d114102002504608060700309110309500c1c101c0700c02006030718010495001c010b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 371419127 1250 371417877 371417903
    0x40e06040b011e0e03100c0f05070606030209180c01020d020318041512050708030a0f0c060906110a0306080604050307030807090e2e0e0a0906060f080d020d020705010c 74
    0x1030300481c2041c60000d20380d00003240348002010080c0008062007566030103805402040e00300d01c000d034410014002c0c87ca031500c0f8540d444042040792280c0100f201180c0079541c8010200150307661320b680e1171007090b159407210720b00b0a60030202410050a00600e0303065603c031400d4101070135004000d44056940c011191604010881c0018010704000904c00d49404264400070404113401d4840c20501d070300600c2107a84c800c0e91550459902e00c00d1100b00310006050900e204202c40c819005191010300605011078500e02a03142c1e0812034404142c10310a1000000d105203499815018440003406804054400751a150312581e48903c07881d03400400f00b18418000070815401401058058440550300060601c1c1040008a14001d04404107000302651000030710a101c40760048010b070781c441c019044071a20740b540004080d049800c01203c0e085c3c0c03201c1000c11140501c21b00d010003812010020204558590006803d00b00c00700d030381c00e0440d00302c03440c1130100c1c0c0d070012100d036000d6030b00503101d1100d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 371420377 1250 371419127 371419129
    0x2e1e030b061e060403030e01021504110d03020f07060f1103030c07080702011205040506010317070c17030405041104090b01050f03010b030a0e0102070308010501081602070e0a0902130203040611040e06040b 90
    0x41240300c14180c1d4080c50104005c4141a40300100d00c40c074541c20307021034009607003041d03a500710703210100c0e40100001640884014241405c680941c00c0c14401c5c0125540c1e40c0a00b0201c81c14450319421400c00141c4c8200191419a4002030003a00aa03069001c1d502e035003002950401e09105060b4080c1102c7c02c0080c001d41164422484003180c0d0f45124020845030519280450316948284010703190400009005007020800c04116204c80d688562403100b06482c208200d51280100046004035005c18003002400b52076a000b0804007251000083c0c1e50380d801d09901c0012102000c040e10304100c410310a5802041c0c0540489055450a2000703503100d540f0044500d002d0726104140308d40f5035001080d050101034116000c641a10001d803915074065540070700c000c100000d11a00800182e2143c0003c104917007540035229004484c100c008204115242c010819090b0b0358289a084198000100070601500744546a110780085092520700b514200304000f03800c0f405070090384255501c54850345c071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 371421627 1250 371420377 371420419
    0x902130b0c030403050d090801062301110c060d09060c0201110403060908041814090c0d030806150c0f0c010f09090f0603050d03020409110c070e2e1e030b06 69
    0x1585c1c06070850791000d40c0c1500041c100c0900d8841c60f01150308140002c40d1401d40001a00e1000c0c03050540301d407403201410011079000f0904c039415941130050781202401c0740c54140040546078080400420039411901e04034046807110701c650021a454054402455440f8208460840e604031134085100009400d0103c01840750754030080002841d440e8883d044440e41c1c00100d02418256515086a40c550380340300c0d265503075104440d6002007800d5400300040d01503000250452070143c807004c1d41c5203c12103940204d6005030800c590540c09164651b4060f001003210000c40f44080ca004144030300314a601504000e6240910003902d071710b401c0c1c01d024941c0c5a62148005542040c2200c042002c21100a0025845030180d03070704a5007410707040615000007138104c0c1e060140740c0c0000d103c002c0c60070410344072007000604414125410b041601c07510b002c10280c070001030319209034400241494070840500c00c1d00b03480241416104254000c10224000c220065070201090321621030001000340700c048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 371422877 1250 371421627 371421629
    0xf140d0203040c0302090f010311220f0b1903030503180f011a01230405060f0f180f090405100f060305120406030501051203030411012006060a0902130b0c0304 70
    0xa8014030200412040c4600c071085081128002c2d10f501c14039441d5100e400c200c50303500340405842030017031000280b02d0742040c854200901e00040e100200404c0200c940106950500724a20311907500d901c8440b150b480e005404081000e02c013030076031b8082c41c503582e409006408000d11035207880b28280f0084140c01c0341840441000c3e120100201304c8216244201980a070a0001403800601211080150000307032401030200040c402c00100e041c1031400080013455400b0001c07440d9401414000c14041a180a014000101e100380304252214038082c01d2100b40d14444142920403a83c00d4180800301e003000c0b801020b1150004008900b2081020005c405041d0359480206a4402d00c901120852600006401a54507550342800305903039800c00c120125661100e000d000c0d40081002c03070006101400c0d400d010031010704000014142c1c0952400c00340c942004803400e640c00180c104103180c58815214400f074680134008604101c43e0611583c1040e41c140180c3c0c4203500300042c202180e03082001910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 371424127 1250 371422877 371422897
    0xa030507060e0610300b07020c133801181502010e070602011401060c1a090a17030112080c0102040b0c0f10060506090105210112030810060f14 63
    0x1d005804c0c00c0c00066407214242c81102e58540c03040b00407425000008201c200040508184041e41610359140d144413200301400840a504c030b80443c0035459100c0d284060074000c00b94200142066100540a02000141d00700b44004d091b40200305110031403030000361040c1c050a01e00030300122460b0400020041043d0048000d600600340c3c280310301a4150030003220303005200240d80800790b076044d040c0e00366424940145103450b0340b040144401c1c0d08c5021811042c42c069503180400f84002201861050713070503900b0410719001441c91000344905041d08100c0d00d00c903114003518541c9011110164a46620802070000700e000410500a8200b501920003814451204960b10099142095501c0e244010b51400c42d000300d0060002144261140d1412a02c010301428a00110b40c3c00448182e446440308145561f89501144500300750b0a5a00b806000c3c00700c50300910550700c0c01d02030203008005022820544c4030800a003c8070307500084031002551a8181203d01007004035180806003c1c1e07110b10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 371425377 1250 371424127 371424133
    0x207030b090c0f03070b033904030b13050601050126360d0e01021f02040915050607120504080f07090606051e0901110102040902030f0105120a030507060e 68
    0xc010004404614000082c8048a091002003c540d00b03068403242d15105050581206200168180220501c000b00442410b114516a2460282c10404010f0010010301c5454404201481000080960940c004201440078421602035036942a40e41605000d040c0c10040640c1c019002c4010240e0141c8000300424100340c110702d0142442c050600f11041da1860b1a8620003004e41e030b00080c40d00e002441c100d600c001d8002c1001e070080a440070029018150304500c91013941646c0746242001c9030078103410389240960360b28a048a6081500d400044291804000c014104400d1307840300200d9840703540c03101c080d0701a009990015101e500407584144468043c2c1080800c4514000c5107800540c0d0b4124802c2080f55103c0da000c40386401565606c0e58620050510b00354400c220502801c0d080c68140340100500e602d81040c2420b98002d603100441030340e0044280f124050f0300d00c000d0390142c030054900900000990080030364644a40002806100c00000e00ca01401280c4d0015244c402c150011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 371426627 1250 371425377 371425381
    0x140a030b090a0c06110606011b06140109060617010909060608030406080105011805100e04060906080c030f0f060a050a060b030c030603010b100509090c040819050d08040201120203070207030b 84
    0x1c03250701c03400b031900300b203c004850f00d00100701980031300c01d07103040000c0329801040c041d5030348801582c2c00c1200400f0300401e406101359110004905000700380071500a0baa0481d150b503d407100b00d00a0b142c01e0f4001605200c8805030089000400c484480d0441d0a11800490701e4403030f9042c010000e102c0754220b071005000026000c00c1c1180c000880c00d040b15000e90b11809003407806550500d0741d1307009004040e440205008a0305403a4410341c100050088000c2001031170540e034503501e000f1100568840c89054200403201403c03403809002c0c524610104402604d0910041140d02c0d4889030000d110820055545010442e0701a8a510540c0074090040071507039682081d5201281d140c000b210458841e600f4150501d0050400f0748a801020b075054441c6401c0840c1b00d0100980d000c0020103020301d159051000240c0540c3c1004a540190451030500c0c044104074107009040c8201400300d031083c040d0070404e03c030040c3d80c00080042e400c0f0791601c0058a0b0740b41c1030b208a08040d0968409043d074103003001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 371427877 1250 371426627 371426641
    0xf021c2c0303070b0709050405010f270203011202090603030a0e130b1917010b01091401030e120a020708030418090305070204050c0c101a040b0d0b01030302060f0c13140a030b 77
    0xc045010340210741b191a0015500c82c108410344009004581d201445a542004800c421040c2d01c00c2e5101403110100b41c0104a26100c4100e0700264021134001440780c0c160802e50070070028294000e00150007443c640700710220068403035134400a03264098540903085003403030641580f207070241c07650040011102d50645107140c40c075481d150044a040200b0b052510b4400f000501c1001c52800068460000ea0340c5000d40d49a05078840c0e03040b071307070500d9291200117050f00014012081340780c9603242c0190f03c940380b5480003803901005421040d07a5038801c10052002000045d0410b00800c2510004500440e09140c2201d0b0340c014030320000c3d0454103200510800948050280c9080c3c01c941e4100c80d4008041130a8006030785070800c80401105002c1264032a90410381c100e6440d4160281c1004170b00c00c2039907900c04600e90240c0c0140c0050700850148465650301c0d812440d007006640c41308a04100f55100002c1002d1343d24071400300e65500238018140b20303884000710314000710341004c01d010f82c500d8092 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 371429127 1250 371427877 371427893
    0x8040c09021c0c0c020d0201050904090602070c03030e0108010812090114030a091104090f06050a020c03030705030601020d170f041707050705030c010315090209060702100f021c2c030307 82
    0x10740305658a41040754003900148104c481101c66a0020103500925819800640d01980301d410000d800030303211880007000c5000c600040480522030030340042680d1a609006114500c031190250400c43c20400420034003600150310b0000300c0203444c43c0c40c0d440c4e00030380051398542c00c029000f400e01c6002004100003203855a016140300c0380210818558540506c040104580c9041070052682c0c4030444030b00041500340c3d100580c850b00103000149081c619080341441d50b041120540300148000040100c42d581c184202ca0340a0081e003850540810350341c0a20408c540018421520401840c00090034011281a12441030361081400b940e034044504003240c1780c012600803e0f001c0e20031510310b80403a502c030744511202c1c2e1180b0710007a94030a0400d040800654000c540e0f5130750001c814000100565200c515a80c4031a80580f40c2e104020302e82a000703030808103482d124502405020301c24188064002000945020801c0751000b8004426041070f000c419040e0485501840003103103000c208805e00d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 371430377 1250 371429127 371429167
    0x501051e190915081c140c03070c0f0806010506090103020307030f0c260105060703050a03021c0501090e01060b0906090315091e1b27161403060603060108040c0902 72
    0xf050078040400e8659200c44d5482d03101c0e03520021900140d0404004e41c1d44140d041900403a841c0340110b240140c110802451030304005400c0d0f901e807240d07990400020600d152503000a103440c50261040e50300d130800180240c007070820206e040c50f0300000080c2c95144294009160300250781010009450846802407031f1002041e02d10442c981c40741c0038401c5000118450b281203400041c500ba140003074560302110b80d60010604070342415020300104072801a60a40300d071410380d1407240003420350724140818086d0745104500342040d034500442807001000c0748007114035000045d40c030155151082e5012038030300b054900000404680d5a800e00c0b080320000715001208030014402d900b80400346190042d11048007010302c103c03a92504003a41c1250038520180b8030030090300078100e20070054829000e1642481140c0d034144684081c2c00c6c01c0b0b490383e0004208a014046801547e00314a04403000c00e8251102618050522030818002002c02c4034246090001c0d003c2c4d0740b01551100c0700900d030100b010800c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 371431627 1250 371430377 371430401
    0x60601030c0c0c29030f0406060e09100203060307050303120f071706130b10030f0e07050a180209060c0102071e03020a0b090c042306040501051e1909 66
    0x246a000c0c00c01e00e01c034001c0c062160b0740106580c1c09aa1428070305020701030b1030480309002c180880070502e80340e0310680b02452250450304916052880c1502e424021140b075a080318605a20746000d210f0044c02c000780d0300344564410340005035652200700001303151a40d00d501c030365454800090280300ca8036144080d40d0080c0c50f842c0d00710420351184642034565004045581802030390306000202e10380b400b001c0c0480031000c01c060000700400603401103120805145513800c046034031080645440011031181550380c51156016241d4181000001001d008041c85490048800a800c0489c1c00030305034100c0c2c14a4500601c026540e0912035207a44c040c0d00655000c0d1a003a80b00110b82c002c03000106c40c0302e000b645d810340c05002484240e0341d0b6400c0170308014056080b90311030880c419641e030b21075203d5001211019580f41c1c203461400d200c56501b0100040c105401141858010411500e8022050344c501680f582c05d12151000f240100b9983c00703031407103e268145406007000a0305c4510354080c1c500311103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 371432877 1250 371431627 371431631
    0x21090402070c090e012018040c0507051209010f0e13020301030b1602010203010509040f1b0b1c0204050d02010c05010b0904142b0c02120109050706091d07050f16030206060103 77
    0x41c0703c401170032162941410580200c121905c01c900c4050040200103a00003030110750380c01a04080450101d4486074903080120f18005020300602408010410342d40321040c1225140400c10f4000910413402d80e0141001d10903060403402581d0740e400c003c2e9010a80c0c2c16401c5441e50703580d04100801640c25100c081c000101c851140071014030600886e4103a98001d820401d11b600ea950303c00d010307200f510106941d2181d500c0e0407014031000603e0070300000d1929003c2c10747c40d05054910600040000c44880300300520404c006c100750b07111903005000007602400c040b8040a070504043e0b001d814a0165680e10060340400c22003001102041809802140400c8401038400701c0308044c10b0324000300000c0c1441d020a000050303503d12070050204207600c003926002030698801d01035800e542c18120201d8441d088404203011956120f01a04024040581e411107020742400d0518071024001d00364004200c80002d204c400c01c514403048a91080c400d4841050501039420001c0d01d90b0015200180068 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 371434127 1250 371432877 371432891
    0x421051207030b130603020307030809040212091b01020c0f150d050702011407020a03090e0a1116020f19031106040b07060608191109060d120c2321090402070c09 71
    0x250445c81140d0035680e003c1c0007400464115114104180c114104082d4856000c00c94420b84406441d400d600803151b040080c0b400c08443c100e0b84c1005c2c00350030801130441d407000884103003a0b5901d0400c1d1060180942d040500240c284203980b00501c5a00444ca02160802040c04405e541c150301c5003148040040c1072940316111503031301705c0c0c1300c41d034207580a00003d10003070050045402500c005500701c1d00c0d1140015015103c2404003a04c0d40000700344940c0001214400c005500b048001d03da51060111008a4dd05501c2c1023008a14400760101601445109034110001c3d05e45504950107000b8030043c69480d9100d51a0050241c1803e00400d4524000c04600c825a000241c00c1d2400195100d000344115005c0c4200b40118100014010b83d0300508621102c0c02261002c64000924403d0750b8441203890300070b0500355a081110318001c502d08407800c081401d001e0300801e0245050b82d603004162144051225181468005d00034840d60080c07000926004121039068403200b00c0754445020300441d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 371435377 1250 371434127 371434159
    0x16050d030609020c1b010509030a1b0504020c03030a050a090b0a0e0c060306060a08100515070c0803070309090b030a08040807181512060e0307030806040f050421051207030b 76
    0x283c001c00480c3c2c1c4e040d50200020003c42c4400740341d450758120042c582a0304000701200041d02e00411501c2c1503032444a0003040312884100d580f4008050901030301e0075482d0594240d0025504d00c8000c0004d0b0145079a040031580000e0b680e0801d5082e260401c3c00c1c00101d040c03014440300109140c00781484907205807070449400342861025a442100e00074401802c040141030195241603004040200032042c00c000441c1720360f0b40b0043d610004142050154940303800d4500501280040d4002900303680c002d0240d600001c0e0300810540c00d98600f200042110100c503000700b031808902c01d4000703003039400105011034403041c0020305000303c1e0131159107048504880c030341000880780b0a04518032440240c201c240709043e036000304485100d02c41d003000250034001038015420b54010340070445c00141c882e402c2c00094a02401600d0501110010404c100c0c00c003a078900145100a4061744210b2410394140c2d01054024025a00e1940d4002e0702d084061802a9001340200f10741b0007014031030207249809001e8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 371436627 1250 371435377 371435381
    0x60a0b0907030b0102030d09060608030a0507020a0905011a0d09050f1c091203080c070f0c03020a05091006030c05070803090a0512030106020d0c1e0c2309040f030516050d030609 78
    0x34800341038001d5840d0480080c0304a01410040310140d862030b4030ad600c00240180c1c03c00003031400758032a41c2c03515110402c40c410070002a24550080702c2e002c2c10907006000102460742c0210680d84e9420300155500a4082403030098442c021000d0401d014801e0407000800c0081481c18441d00e0b03089111005641c50b12042d50517514038082d01610150300c2c0c0040307000901410080341c0198101220509160040d0340d81954150309100444285100d10002c104501305030140e030003e00030454040600340b420300329403010310f889481443c04164030394031100780e000d00502c121510f0b1500040e07074035502e10b03004842d107035100802c000481c1c8500c200301c20244410007200c1a01c1c165205980030b00002d1035489011120b40d844100c00741c0d10114032264008070701030500b24001138948a10300c201100707868000c0410000512804241180c3ca803c3d200e0403c6641d0203522585c050350108420700c680542e810100d4160140168541c4044107081d08441442000194281c0d482050740d4107204080d00d035568001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 371437877 1250 371436627 371436641
    0x10806010501090b070b100f03290c091905150711060a020703060b0a0f0914060a08030d11040b0c07031106040e04140a0516050111010c092105060a0b090703 69
    0x1d80340c00103111690000b6204001d10390042c08203d082040070341c032900d141c08100841c1c2d000700c4e03203810402b00380c139041c03410004a105010307485d07264040c0c1898042d5050f06940304104c0d08901c600d08510b09400040c055000320030284ca0050314518695501015004250748008026a200c0326080402182e61a00700304642505007641d000d0310701585990354500c0035002d840741c60303580810b40c03820104104d4801c0c00b0440041000781000728003d40c0303610b5243c070200b0700508068000c108a035804e210160001045900806c40f100340003d42900c1030008040d6801603400c4040840b030005614603084800080910540b4020000a414850303040100001c07407140348601003044000c9000500030a1220b5085441e8040540a8500d10b1034290b550500b42812843c01803507000c5444030034061542d10020840411205100800a00d1303050040944034000902c20031103004455207042545000e230980b0207821503441000c039078032810584180e501408601ca41c5a000301541e03400200b80d9071090160a03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 371439127 1250 371437877 371437889
    0x2f041e150608060a03023d0f0e0108010501141305060706060e0f04050a11040b09240901081c02030c0d020607081f05090901090507030503030603072907060e1501080601050109 77
    0x4048000b444945031515041051031140358507c010343e820700c0314440148854211645c5c0e0801e443c45000350203007404840d000400c2c1000f181e040144081e036080065801c0912480141a4483d0781401401040240c142c10039500706001081e09801c1044035081a0305442003c201c11041d6074503441410071142003120041c1ca00d0f80240180340201d500c02a0703800f68540c0c00ba2004c2901c004c0600425954881a9402d46076807190321410b4105070020204102010400c0701c0304100c0d549000d410960b5800f5840c0d88440708220410650000c90007081141c0da0620b08101b6200c1000e10741c0c4002c4e40742c80c0120342d1038000c1441300001840075001001801c540b5070310b00361712084035800c003405c1c0107868000a00c0c2c0c148640d43c0e0500d03400072544c2041a6030046200b580107565074607116092605007281c42e80511482c070104031156042050b00d04000b90a81c2c103140d0190785984e2036080c084084c0c0950800c2c060b4901031034001464900b0640c035a02c0c180c1d090101292020b981c0c510045803c82d09038440c070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 371440377 1250 371439127 371439139
    0x219050c0f040605061207112b1106010b0d0b040207050607231305130b01022e0204080d030c021603061805030307020a2f041e150608060a0302 63
    0xe5015107003040000d4030168000d08001491a21103000c00c2d019401070074a1403119a082c82007110007503001a031044201e03651401b804036142003400440b07402c10b40c4a094214030f00042003240c035961245c00110410130000003110f040d035039610400c114550103076500024240c2022041072071400e1500072160307101c1e400001051242c0d1600d104407880368044041005501c10381c1480a01e895021024000701005041011102c41c90881002681000244440700c19030a0122004c1980c0c1c000c50800c21000250082d604043d88040082c210404010024a2070610220700411000000900d0074001c19042d1020445520000700980e6034040850b180e000c4204208420f10014078580c121841c0b42c1e00a903c1c50348a200c16030b6426096400c12640c500c0103134807201d50041130083e1802031340c8980d4041500d54102c02030300e19032410100690707918a40260b441d03248810f01a8a10124100d286010311420040340d501c115030360320844a030b0300c036035400585003030085420b80c44d101e400742007225401094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 371441627 1250 371440377 371440393
    0x2071d042003070b180d0c0e1e0a05060306060d1104020d060b0304060921020a030503070216030c1502010b0619020a050a1b060305092805150106021905 67
    0x11004110030803070720480c45032444103a100e181c0c0c40400c10034004e442500800d60304d8007042818002e0303440c011680315203d44164000c407004519604244020313501d28090503e015964096881e5641032050b89a920451022042240786001548420701513902101540c0030344c2c4480c8104120001c0c07040c4040d00800300c0010200e102d03e0980d000301215040c2510101c0c3e1316a440f2101011a00308513015241c0544403e6454204100c49850007001d0009080d900682407070104002d40c0c0d80c0801100400788480040441d4142c0d008024070384290300403009640d1b00d2503c0f443c004454200d58420000c03c842103400c40310b8454010300540c01c10030720280c42c45007441c100003c2c0f034908020044000d415401140e80c804c01040052060308001c0c4c4c003511b03e0f1213101903e400042d415250759071204003054035240a0040b50f03c0302041c0b00f0904480028900791030b030003a0480032000ca6140f000188644105242494001e00d021809030403a1001c0d004d44914403450798241550203a144402003050b007200034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 371442877 1250 371441627 371441633
    0x28090509070f0e180c1306051c110403120e0306060301022508190e100c080702130b100806030708060c1903020d05090a0615060e090415140702071d04 66
    0x403010f88507000041c07081e084007042042d4400312074010354012105000000320000124070f01414203000f0800362800311302c0d10043d080d1075014299181000c000726500c07021503410126440341030750040d40d00207a5820810325144400780803160740003550360190181000040c0c0c2442c040c030a85058101c014640344200c0301124200c020f1031014501200c2224090040200c0800d200814900e00701c50798480100d510440e504000500c44a1242c1030104003030402400b00040d4800203440d256681540d064110058010243c4c016040c4405a02e811603180c09880040030b9202c0119801040158195a0600e8841c16515140c0740c1c11905109114020403920fa415004022800c40008040c580142020080e2900000f030702c009841800742c60b8442c0c0069018001e0f00c0c4a07190866925034040c40000d0f01e042c1d0040c00b0741c0410b00d81c5a114820351070008043c031004200b9500ca000c80554100f018004100d0f5545441c902607526000500c218800810341c1c1664051800b5078400030700381441155515a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 371444127 1250 371442877 371442887
    0xd1a090d05130905090f060103030917010c050a05030601090503120d0b09070c02060d0f050c0403020301140f0c0a0905060403140601060206010612020a021f0507030c021b1528090509070f 82
    0x1400d840c2d036922411b10b8011007042c09010700c1d07021314440c0d903d1142051628201c0f401503c008441800d059262248030500b95802400f12168203a041c203005441e0303a108070040e100c64016511294150140c00074101c41320248400604403440140c3c410822040c1d0380b0248483d000080340c0d40d00100301c1003001d500141c64120b01602e1000c10210000c1207a10f00c2c2c46008040d10015500600b04e03c10100701030046103400e00a50085444003e500101c1d85846428407904000c00341411000850004032100c0e107610603089000a440090840e0b5034440c0d40340f40081505121540e48049801800700201359684046003142c103d42c240d64a011052011180d542c000758031084582041d03201d425000c008d40c03122617a03480d4449a90050000d000e2806c2480501174404507101a81150454444025001c014000c00d000d03284082e616030840102d142001d030481d00c070f107200c0304005030044111000c100b17207100007004a2040c560750f15200b0035903610501094000035074000001c585880d10300c0d40254070030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 371445377 1250 371444127 371444131
    0xf070603021b0703050a020906061603110a230106060801060801050418150504050c03010b0303030414010617012f030a110f07050a11010e06030a02090d1a090d05130905 74
    0x1c42d2511100340388801c441c60b14401d5402203400350055140e4900b9490155041603124070142c41c00c0d0f01c0e2003d51b60180e402007034101c1e402014042180b0b205034401c14100b15140f170440d03000c54180d0442255480c040141101225170440a41c200a800b098084c4504022812203405880340e405076420a01084054504501129003480c1c1d5a82e900d00400c0d142c40ca0094000b102101c0011a402c082c100142440512181503000e40e04040340c8a0701a180007084030b5102e134200c0c0d0800101c442d2090414050506031303001f0340c01c114100c140c0b0194148103503c0b103454005c060841c090380d02c070200000030398040d805802c006140c2c1c080c000118040042c5d006002c4181c40c03c5d41e114981302c00400c00141c00d4111a20954403035201400c274804200c04807400e000180c0c0c090800c5100c2e160008009940d030721004165031051038000c2007444058449004203081e16030700440e0705504441d0100b44e0714100e20210340080d000c1c850350400b02060741c000c004403010020040d01c121031081c01e00c000d0001034100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 371446627 1250 371445377 371445397
    0x60c0d0516020603131a07020a140a02180f0702060105090402060d0615090504060801020301050d14070b03010e1e0402031b0102070f030c080f0105070c020d022808010e0f07060302 79
    0x180c103900700300594441008500c240c40c0b85425a8466800d4107044504050040d0b4505004600c041809074003500040d50000e6030f9070000c5141c14a1245802481c10403014000094000002022244109a01c650b015206043c83d03141004203540304a400c80e44e403003080c864960031403200008100136050400007045e440208042c041807072070380c5240c4c07810381c07c9030480c0140c006401c91a06000b42d00d040e0042c5070091071808025421075041000007140c42032158002031482d051110000d01c4031000780004001040c444207460303240c1d0707542c0d50040185601200c0444040484c06003280d80c101000c801c460088be0041c1c0244070a2010b5014030301400440310901d4154481c8200010b1031440d0442c411700958852402d0408032450002100d1170855100542642030b4140b230108488035501c40d041e4582c45e60129a68405540540041160340704103810040010191039104203202111101c990101c0302a10020050100c1c40c0c500252109140d41d40d50300301c0c0d00203103002c00881d84290050948150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 371447877 1250 371446627 371446657
    0xa0b0a14061209010515040e03030a0e161d090d080106200a060207060c020703080d0b2107210b16180e0a1107080304022404080a0b06060c0d05 63
    0x40070242060101400300e500303c495a448800300801060005203143d1015016141800321b450410182a1179002c010510300d42c565540d03075441e288000c1040000049a44142c1440945807120740300c5140250400d44a4245941040424104c03d00003c8801090640795280d035916420300000b01c480c42041c49030082c10300e00d0200c8400c03045209022042d50f192058100580d1440b083c40c21005451411403804155041140c080011844031400c4030300c0001910710010f800c81101000904903c00340e00c1141d010003681c3c4542030b0000c0c000840c04183c820780c00d48100c4050000f00401d02e140b101800c003c2000030643c01052000c01c040240348482541800c3c83c04004144d021030301002c0c2d100d43d1041c5400c80e030a4040c0a51091148240801400d5000e10a40340091507110034403e0f11000d44001d020b0401640618604014405900500b800e00543c1c17075550303641e076000d02ea41c4850b8000159401d07540007003c10300502d00607045884901daa900a400c5224182c0701c1a643c41d0092055104298 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 371449127 1250 371447877 371447887
    0x190807050d110408070f050904110d060f09020f0f10030b04240e0105040219050703090e090d03050901050403091a0f0a0f0e010c03121512060905060a0b0a1406 70
    0x240403405410260401481c0765510f481c5040303a114030b80300700c07a03016103d5000c401c3c2051000e40c80b51000182e00c15001302c1424100c280e4500401c0da208004000603100310300e4407180d90406001d60300a4500c00303000f101d112600d0042d404c00c001d40039040080349503000e0000c04130301d980580240c0021548a00c0100001801c0c003d4048214007110303004010408414a050240028100540c409014110a8600b1800c103096805980c05c5146080849411300c40e0100b50703002010311540c0300308082d0800d01d9400d41d06080814105503034068005010300880d044c0310004a0a000c14840c0c9072049030156203550b162813500690140700d1111202c140c89040c010000c0c071025011501c001c1c64961915520b4840c11040d8440003440118a00041030410140c540c040d000f10b540800720409240301d10b800043c03c1000194004a540110b9004a000e5900744100e10305112003648090412800703501600c01329030354810b0182c00c44550462080e400072492342c040c80b04044000d00401d202d04050f098070720b01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 371450377 1250 371449127 371449147
    0x90409050c060f0901110105040203030406050f130618050117150a090c050304200904080a0e12031926060103021b060105130207051011041d07080c19080705 69
    0x3da20072142c55071400c1e800602d150281d41c1c849141c1c10000c064030003c03c5203082c6540065200c0c40380e40b0a203420050040391b003405a04060045541104004007a6042c20380d444070040d024070350041900c0003481081d04006103550003451291000040459400c01c40c0d5903110340629a8201c001c001c40d04100290404a000d400b28855800c42404a0b16020746910302454110324040b0358040c0030a04401140058885071113000480380c11a50000c0e4180e1502e00c000000c64441100100d85d80c1c0c844450720a00c601000044020300d04e081d000100e8481c6a105d50701d01f80c07101100e41c800074000702120b00d600c142032100c01c140150850014513016180c108152a01c0000e0b12003d41c4000650700000700402c11840d107907030b400101185496055042610548446440c1c0803203a084101c0162500b9449030b82160540441f0017910240c0a0f078140144c007500d0044078480201e615a001c1020b41c000300e04003200000540d0341100744001050020601031303804582c00e0030007506031003c1c080d0174080300d108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 371451627 1250 371450377 371450389
    0x109020f0904021318090c050d030e1e06040b0408060c250213020d14070f05040620070303110c03010911041508030f07021f0f210c0f0f03050705090409050c 69
    0x4030781c5d45c0d08004583c07640301c0e08040f106991282d1100344902c581c1109040000d81110110815200440b0b840203914140882c2c0f40c0c1c00ca00d0184215441140003030080b440c2140c001c0548143c403901c40480f07040e07a8440848444500c030380c811001c110001e14440c0d500e20318440c050340c51410701c041c6c40184130840d807001202c00c1ea086238403020300854070b82c4c91442100001440043c0d011410b031078141101d00754140090441e12444c0079640c200039280c065844503001c01c806009007186814211040b0950301d040c014065500c000e80100c15004003191005186014056540c4090300110503c2c81e0744224000c200090103041c0c01d010450540640c002800700050001e0900300d00c0c40c0b01140e80e22419441080600f41107001d00e044001703149920002e96641c0500c84100b00c144038180002034900c03281e2050107000e0f000c00703080e0034030b401d0240740030284d035001040ca080c0320f010340ca0f166441e1034506010350598004603a42c80000f4010b000606091401d6000102994055000d44140030441400f24030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 371452877 1250 371451627 371451659
    0x7051303060903020d0f0516060b0315042a06030209041803020c0a0f030c0306090203030c0d020c09070503040312020310051305150303030702070905270a030201050109020f09040213 80
    0x7480c0c5a07034101d11001d164041c07000c030032515100e1a16440ca05003081000d0028024204050b1074030581540100800c40b103580300300d511640041c1200d0280800c1040c2d4003000307404590031241d40d06c0c1c0c81489080d51080030701031000c00340303100808081d06080200843c000e4011800442e80f00e51030301d60050f02201034501240409001c0d81c05404009081d40c04c0c003a051201d54400548200c586400304089000c240c03420041d40c0c1e2002c408503402001d0700001c0d1650044c00c1490704940101e180031034031a5000101d40c404c04d14240e40b560301c103544600c2c0a07601d60000300c0300a80480d00480045118002c00e038011a0301015480301450016251800b040507d070a02c3c503403e0b0031a55503401e100d05465403518842e01c0701e008400442c95850b24080082d10f983d036507c2244110394a41001c250203100c0400001c07a107004100b0072415079005413202682d9419071410690265280900100300585c0c14022135807100384000b8020f1808000070706120003503100c0c48080a01a412007404114942c00e041905 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 371454127 1250 371452877 371452883
    0x18040f14100e010605280306170a0201200d181a0309011805030a0827061906081b030a1b080c0102030901090308220914130201020c060307051303 64
    0x11512030410420b40600c0c041a0000350600138140244002c001c6601c4800031174205112101040404803803094000d000310344c0220039403050b114414001d40c2030014058100d039000b680c4003074402c0100040300d00d405150301c42e1901e05030806100b00381414050310b00281c0c0ea500400d080143d96a482c041202e288548401c8000c0303d4a002003486240c0f08240219002104403c1c4009040c1c61181d44d070710741e6403050744bc3c003409025002d400270301c07051110094150a0307105444100e2403024101c07c55038039418101c030100304611011958200310078980c400e110a6800c0003000788100a01c0c072401d11001038281040c41c0d49481074428180004c0c000f0750281d11181c927100322160515050030600f5007015450110304c2d0455006002c031680582e4000350355400c40b034000f20f2455840c1c4000d01c6000002c1c1100d08080d03413040ba0401c00042c3c489155000d290394030001086804203844040040310081c506100c00707401a4800d4403903601c02d140000040d500500981051407400012482c02850f008444d8001c2d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 371455377 1250 371454127 371454151
    0x60302030609120a1b05100902010f0c120c050f0a0605040c09021908040201050d05040c1a030c0403030521010311010306060e1e010e03010207060b0f030318040f14 72
    0x4004500301004402c0e040b03400903000e0120291520f0040000740200c0300118200080c101c40302e80784c000c540d85141c1c41242c01000741c5a401100c1680c00700900740082c000c070b0000d8405a4181459441110942c107a560b2050440664589500003120004940700040c0c03854051078617001c040540030000c130f0344507501c01c9001144503d03141c1000302844601d0b40c427400300340303004001d951480f17030300052a01c2c00b50581b07090146e100d840c1c9000480e501e00584503070950151400e0280812310142041800880b0708600052850682030b01a41106020955512160741814802400082d0090001d040040c0040c155103550791051050340094030402e80c02900d4400340d0001080300c81d6072501918020382440c1c1050808401001e021620540b002901950b680008001c2d0009583c0701b5241510710120082c000d5442d80c5990400b00c00400032100420b00c1040c52901c460329505021041d00c1541c5d044095009042800206100240449021032018282d65100b5914050540d20386a40680c07580480 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 371456627 1250 371455377 371455379
    0x7031203111305150a0c03140705012d180b07140403151a0904020d060e0706120b03010b0603240619030608120f0705160602030c2104140a09020d06 65
    0x620001c5069070289183d03104e07081054103211900410880302855052038030354082400a403402c43d01d8060154002d0103035080c004008102080b10190403900244800319508980401c02c0c501c0032501036148855032100c80142503004940b011078801c1e070000301800d01103009680303100c503000070750b0081e002100c1200b1204111600104207200740c00414811408403500c0d101e41100154010b00014002441515208188802c0150365040310928a82010440b04410744800e0082c02c08010084d0342c5260310b1a0211100d1240f5050090003201c00010f89078130f146407990011b0001d1a00b81050780a41140102d403641003c1c0c85d25402049444003c1041c0c0458615036071008055680d87d5000c440aa880701d0160030111084008407178000001000c070319581c01c11442d156003040c0f80d100c07994800b0301000e030740001e90381d8020004028210b110001d55650303691002c030890703103d070000c040ca04034100d0501040c00410840b03903000c036030303c14020240310b0300c607030356084010903607004046980000c1d41700c0070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 371457877 1250 371456627 371456629
    0xc0604181e0c0f0e010c0803130f0804060c02010210022503030204030c0f031a010f050112090c0f1d010605270d0606151103030402010e1203030106050a11060907031203111305 77
    0x280100400424a000c3d0805801c1ea1140481400050416108280050276160400510001000c84141d20004064885a8880c0c000d809a0003050043c0d000d0b002e4090031644ca54114800c0b508040700e02ca04010741d84800c405484110491010201c0a040e030812003c03011030740846800340100802422400308500794541285442c0c840600490074520800062002c08210314109050310000c4c80d11503c03c08001520070b01401c50702e6005040300b00150b00102d8000700000f072205c2034404001c2180d8040705000c911000b030440074405d01d40016420320079100340101940e08204d005041c894503030040703210200001e03003600920030119403140d0b6904041001d00c40c500001f00c403003081800d00c110716100b0660303155147c1c400204024100315001b4210340f4a9681c000905030041c400f02c08498072581c641102070043c0e071200440501060300d4281d1501c001c039000070418810440380d0040c00e2124030399a62100644641c2e4820418503442d00030400c2050100805408d89a5200c3c08844030070b0702d408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 371459127 1250 371457877 371457887
    0x5040c14060a02060604051e191b0807050a0c120804030e030708190804030506190b0909030a0305041112030904140106080415060b030708090c0604181e0c0f 69
    0x340030309010300484071565000b02e0085e0b4800c4058501041580d03034400051403030003007040014000c06220781442801201100030b680d43c00e508100400c590f4000c0d00003a207800d902d408000c00040d181900168801703209902910b0030070110705040c0a2942075035980c000c0c07101c40908a40001c0c0700e000801c4141030340580f418600050641c080d00c140d5060155882c0c4034002b10210480d280c010101a0081204141c2100d006503086401c0c0c0e0340600704150750060702000c10007418810303404c03d0702c05d201c1c034030380308540c2c900815410004519041c40c00909401600008209480c91000b008070547c0a480301318021200c03000c864050b607610510b4030204811241c5031140b40d0000302c0aa0014449030350810070158105800400e8200120003607034050300034013a550850650708601001b440030050300218590300500200c4140c0d00309400e501c081c02114080c038440d090900704c03c0410140100007952000c0d8400590500341014440c4180892003035485004031800050400ca00d04000e0030703404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 371460377 1250 371459127 371459159
    0x70609030c020a0e1e100b070c180b09070c02310f060b070f110a0e040212060411060c010b0303040803031b070305121f0312021e0303040b10080105040c 67
    0x182c864151182400104240000c6840b2985d07986500c001d80883c510b10780182c603500c010008029103560313500381071038030541d075401c180310b01e882c0310f919007101c100fa10f00140a8280700c984050510981991032140071036400c2c801044c2642c00c5013500d050b0520403c965440c400d00000e07641d00300c903801045c028004007103912001010000781c1c905401400302084600072602059000b030190600c3d400d07503007021404034079600b00e400e902c092841400038411a0307580001e40b045000704c41410880d5901c2c0d650035204d5004460060103040c11540001252034428040d1682040340d5000242450104000c00d1940d401500b1000540e48003004200c210800d02c041e1001c0940f150b11114248155542d000d001c03401203441c4000181000000906220480000c46240c0c000d6001880e400ea0b40e641880344901e24015240c2c0e0060003450b01d171101e441c0c4501c05070030401a03400003c600c0c0d65100d858603d80c54102402d080c1041545490024030300710240620b0b4015405940d810010607d01107402e02d406900f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 371461627 1250 371460377 371460389
    0x40e010b15070c0b09130e0129030c04020f092e020d050d050a0f0906060e0c07030c11040209060d021305100c1101031805010e011404080313020402070609030c020a 72
    0x41040400005420301d050030089a6113068220340358469840002d060001d99007004090601e040100c030b0508805400010110f61040000b058000700c0900c82911252659542c03500341d849010301503c10304090380203251350400160190308080c1a00005420907080341c0b410f03150641c1d0801400e0100c0c0070140004640c112a0000308280300c0f411780054107a002e00b01500c10707590794610014107903066540140b08184401c200c00c0000305258a4808001c0c1050b001d0406200d00c0000000c0208222000b11002e03503070540c0325000c40310900c0d070354682c4090008405a4006400340107a41b0543c69910103080480407020700580c4500010480090380d22550344420701c10100c0d0400c001225800541803186982c00242e0480902121001038024200000141540340c6020201e001444419801140340c000000001d00c07140c1c40001900c174601100303441c040c001c030303008001040d594040d12119010851018001600702031305501c4000c1200d4a01100f5000f1521600a15045281111040c0050300f2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 371462877 1250 371461627 371461669
    0x20f03031204030e0303040302150a080f01060c061109090124050a0f0f1e03020406080109060b04051e13061d0c030604090f060f0c0810030206030c18040e010b 70
    0xc06003410240000c0082e1000e81403140301645031019071030502c2228003854010b40580207581001600950660011100000207400900400c50100071266030314101c0da03442d0307501c00c1d18060315111400188085400e80c10240d904010f40c080c00d0701d84a05907402401200552a443c0c9640c1078400c5090706640644c0342040070401c41000c1c1d050708a112013114102c20700e44800542c0005105075866842000c5806100c600003142444c66640340d0003d2058072074654603e80241d9a6010b82000c2d00c0240c01a11100001131000340502d041c82401801030301c240b018031a205017070396408140c8030f40d4990308000d815512101b09000c0c05880044d0305400880d43d003200403840c502401480e000d800050112445a510b40d4900020300c20407400560301c1c1d94005000308540c0d0000c0c004200149042e0402d540441c0030704001541c0c40c02d800503100c00300c0f50090441803441d5600407440e20f00364030140d580320130b90040c0494030111b5219071107007580c0905c8003400041c2e081c03132032000c02009420180040340e21344 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 371464127 1250 371462877 371462887
    0x7060306030b070305090c0a170f0c060406030905340e0f1603022101030c050607172802060f010f050a0b0901210b0a15051e090a030807020f0303 64
    0x5602c03104070b5035100b405442e000030251070741841c650514101003101c1e42d00c1000d000d004141c24140b11914030f40308800600b1540c03034010075805240c0710504100411b40c8103200307020403c0050f0003500403d02c01840b49046e00c0201c1c031884000918041c0c94690b4085c064234010300d070742c2e0b22072007440b9503c0500700f000000c403458681031062500c010380c010415808806000c00c241c3c4c485010340c050710400d551207184410002859000807061000034482a6401e0595042c00141800c000045501c65904009507030401a94800c1640060b80900d52285800302c084501806030001694421040c4040c1d90203002d0604049401400d106011b80080103100081001006169070389810071086038281c081d1141c50f01c92000068030120641c0521020401102c40b1075000808a03038002420303010115000200302d80c403448500034980f410141000440d400b00800e00850001c008540315854540030102d2800caa404041010849164011a82c0c03074008981e0404500d040341603020001c80980081d4101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 371465377 1250 371464127 371464133
    0xe090610080c12100603030c050c0f0105070b040f0c03030f090e150108040507030b040f05010e0c061206030a05031c1d0a020d062d05070e091902190504080706030603 73
    0xc2d09011415030f01c21807080c48200740801c0144400207240d07407500e00400015940b402c1c0a0000079a2020407a003030700458110b218240f41042c2c504007840c2042e5103240c14100c40365101c6001c200041c0046e550449028030100004600700700c200d02842c070076590204840c60380d6201a01c2c0501c2d5420080d4404c20321010000e1107540c800621035060030918020f10142c40c0c506119003419659040076282540704410041849a0b903042182d000d84140300800403600001d4040b0b8851296140c0c19601c0b00c01040040b0070260b10701c2c0d0b140c0e08810024241d600c8260103541d114074651002c0c080c001e4a035981c0c08800041f2005100d06000342428003159400c0c148807444840d01c404000d078000b88a90441700740c00040c002c5c0c50788238440310034503503001c0002d040d006900700c500c00186120400d1001d041c5000151010300c2030310594035910f00941144250344852501c100040d00314140c0021003942884115155082d0600c01207200001c1d859003503489040151450410312550445010316050110800c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 371466627 1250 371465377 371465383
    0x908180d0308060d171801110105151210090606140105160803091908030f0c090a0e0901150e0105010f020d120c0509090712061e030b04060207020a0e09061008 70
    0x203c290112111220641329107031050400c0c410050105040f4000308a18400d480740490304c0c1034028017622007480c030f030150a29141c00d0796021546007000e80d1001140c03904604181c0c01251900d503ca00a0711080451103032068103c1e0300c0b041065640a880c1c040810903221b112551540c079060a2034464500760014003081101440b94030000d1400c04000005800c021b018807203a9200075081c4480409945541094009600255103010316201c1c05c038003041d06580c004046903009240035040d840311f9460a0151440d582008040014554989040401c10051041424054074604034000c00c99410000010216009017850b40c0c150340c03141600903102c40e046101780d28410a01d030f802190340070910004070f400c0c3c01794080d459009921a010f111880380c02009589520400f8a000c02c00c107503644035080a003516010220a1100c2e0303414041c00460940140745070b0280c041d8101502d852415408a0703c001d041c0d520280c0c0d183c1024060024621042c0185030708000801543c1e001d01d41007078401a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 371467877 1250 371466627 371466631
    0x121f08031207020c0910030605130f0f080d0f1e180b0402011407061407021212060609030601030c030506060f0a0506031008010c050901030605030a0b0103170c010908180d0308 77
    0x15021107a0000120800c2c820080c03200d0081000d092a2610704042c2004801b06680c1d010840c1c600341030100003040f00c8a051881e034501a00901034011050503512240e54041d0030400544401d8000c0240c02440122030140300c1021007d000c0c0003c43c46101c1801c02c2100b1503038071140c0301c2135040c1491360038140640c0d96481070068100d442d465864035944016030302c0c2c1c21300d001c0c1e00c5481040031940c1001d06c106540f0200007400d40c3c40e0b07040140ea032000c00498440141121b400410401400b004046250740b42800340e0107100600f56030314000061000a20f480000d034021102281006010f00410005105594001a040d140c8104145035038000403a800305034007420b8010a0b01000042c3d603c5645491203005210b2000200b009051440e0000d007103070301545496000c203040c00710000d4a420005081a20260400b04808180e42140e6a52007446200c00b5910380c1400d060016441c50f09003846100003c13442401015503c00d086040c0342284184080d5152050340b42c40f4450000c01c0d00011515 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 371469127 1250 371467877 371467897
    0xe180403082206110406110a0506070e0f0409060903021203010b090d060b180615040b0904050709090507020703110409020d0b090f1b040e030a0c060b0a0b121f0803 72
    0x254144044108000c0c50030b00503000580103500340880d070070035410214001c0c81550070310390310780d5808000703000f2055481d241000c0090817a840100000e015500c50290000b403d600184002401a401390004058921405007610a1503565020b5000c060301000704c0200d4606090000f4159854414228039a008500340c0600646c6e103000904104001030f804007028070b03030040000c0020104141c41c00c00003032084031424010110302d40c08014442c0075405071021a018a01c1d00307440c2116120038030000e400c01a21803410300400e41c0003c961028036001c4d141c070401c52a03005080b103034a50300b480700800200e4086039006a14006074000940c0310180ca10390780b0790308141b10311046d80340e4049091415501460241450242d800207202c0c0c2110b5100d112031001c02150f041c008a07a500400d9038480c4107048490002c01c0c010044640001c20b15003001d02d41c40c030000d104010701a03950140e00040d600c031412900d0b05590800030400703009030101d0300c2528186100080e882c0b030750504919550364450700d4112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 371470377 1250 371469127 371469151
    0x1404050114070c050c040b06091e1203120105041a0a06030c0305071b03030908090315160f0c151103090609120a0207030b09011d030310061805091801020a0e18040308 73
    0x47c1c5094030b0341c0c0c0840d40c0c1c5481c05000c070543e450f0034000140c59400711103a0346105080e00211545220710000c01d1316050030907688447c2c07030350f480c3c407041000402080307080a0503140205002c1e00150740d5115a44005c00140d100131482041600c0002e0890b0760007032003641401420b0010035204460448941c41d402e6050400045d40c40c0d0a050402c0c2078020700801c03039030501c2000d80202d690401c40e200303280210313030b07a05500c54400618402592040f0740301007180c0c0025600702115010604c440a001d61641c1e40c1c40340054a0054030004214a5008840170941540a60103105180c4010464240030107010f0303a11134100a040b00d00252610752610001c0d08014499000c5400140c080d400114281092600302c1c400300320310700031291683c03c11600e60b8141e4940c040001a001d0240300841700c0c40d4410001c1888403800c00c4104422031001034225110350401110000d4980400d20081070003110f2500c0f00710350604010104214803140039504404003101000340000070f0b40100906411181029031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 371471627 1250 371470377 371470391
    0xd1a09030708180a0513020c010609021216050d1d16140609010207080f07050916020d050a020102070f230102090609150c06010b04030b06041b030f1404050114070c050c04 75
    0x303058041030f0f405c81680140c0c1450500c041140c07550041c001d0707201074802404182d0303071a00c01000303e00501d49294204d40c00300d400500d0750320f589920340e100c505d0303a801d0041c2050f082804400c00c98132080401200b40d019800a060720010070011652002c40f203401010700e02c2c0c100700c480010880036009042c00f0301004600e299141c0e0090082c80054030003d000c56040c8a6a001c095682e2046031152078000d8403d107000c210146d2403414000340340001900101820000d08400322103a51250300c3d4041155401d009880001d051003e148080703d014481039607aa40901060444e00015100c41e08120382c410403042031503480b240251140175004548403101c01010040f040030a2103495100c0600c0c1c02004004203c0070307441809403041d41e010740c84000303c0c1c2c1d81e0b00c024001255808105030590402c03014905060300d109400240a00344101d50100e40d80e00c0c2c81e4140034141e50b042c2c0e030807101a5155030141342d40701c10701054168880c03424a800442900c03ea120b858440043c2e0101d14060703038503005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 371472877 1250 371471627 371471629
    0xa03120b03030d020c0601051005131401030f0f0e10060503060f1b03070224040305030402130605060a03052d1605190c03020607050405060d0513020d1a0903070818 72
    0x6035075078140f804405540e640074445050b40ca80000740540352150140e0b8024805c0701c5d00c240c081e40d2030f104a40c0c2c0300c100341600300840c040c40a01115002410035840d1691402a16038a000b200c810307020544021801254070400a400d148062013441e891030b02d0143c04220640c0c00149840c0c101254856940e050b466600b5000d001000c450240c03c0c0d0f00c14000103000034160f002942ea010071400c4242c2110505000d0001e00c82c0702405d540c003400007a01800844d01500c1c201241454101d641000018559507079800b1442903000a0258804203980380108403860702500d43c000143c090613646207150040c1403420500e1100042d00a8005048803d44007100c240079000b00c1c0c1516032001c01000049404050003850a038030754204078018054040820103450241007503c00340c5200030030160800d640c1d00c2c1c004008000080174a10051344200350300c005030711170640d500c2e0140d000d009a4403034403103109210040c285000c0d10040081c5d00030050b4001042500b070981c2c4d10b01415003905011000c4000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 371474127 1250 371472877 371472883
    0x703020402030a110403200108011d060d060f0b09090a0308131b24180605070510050705070b25080a09240b030712060506010c0c080601030c080a03120b03 68
    0x40504c0d11600150200a01941e035a00c1582c8041911244a480b10460b004581559080c4220b00042903003d000b2041101c64060721580010301400c082110185278480800361101c6100e8038240b559140d0ba5801281082444203a02a0502009000720902680d0041c4480c0f0024003400000c0100307444401004070600401a00b0800704a80c064150f0311783c1c215040c00038154013400854041c107103540e941213020b0803240701c1100b100081401010302c0c05006540d19070240c0d5046909005800078040482120300c10b89024010655070940c40710441e240c00743d0384000c050f050103c464081400700c07040504814584582e04180d00d0501042d0b12640158070140200c498010001d0382c07a454006c14030841c5640802607040d194a0500c0365448507400e00d600c9601a000b400d58a0203481040306c045005508082d40000061401904030300981c0c95070400c010041d084034082ea00144c004100740041c42c007a14014206040103002c0400195034041c01070a0038a00c00b000c559241d01c0701c40404c0d5024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 371475377 1250 371474127 371474141
    0x21c050303040605010617152808010507021608030a0e0d150903090f03020a0302090702070b0d0c1d090a0b06090d05070504050c090604030308060f060f03060a06110703020402030a 79
    0x9012281c40e03090a01d422000707007409001d00000200c0050116554180b84c60907a801000d114450641c0340e41480d05021220700c040035041031240030350070385d070700c2c14161b024001000b01a40c800005250070103050003803c144034140c203c0c0c03c03802400d50a00c10280048103c0d46400c0345400c1045500080c4000304905001d8000c025014108048804580508030780120010030b01c00c1d80c0d242a080d84881355007003000310b203000180d0018030076581440141030031400150081c40314011204515aa079103000110f9111040012040d07807540c00d83e0340c4043d04011b550f141c0c041c40d40c0d8445819141e6101244450100600d403164440c0c580c0410016610741808441d501c15000c2c2c0300c4440c0d1149824244e03035950803485498006c62401c4002820001d2203000c4e20400b0f04000d1456146c5031030344c0c40031107102c2d00103001c8952020504000c0c5100c1e07a0303424010000c01c0042d21540391646002001c0010404140d03010a040c483c2c0c10188400810303003c5a00001d0329070484005071203444555000006000d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 371476627 1250 371475377 371475383
    0x5030f0706080a23090a030806091504090f0f0812010f0509160903021302090901081c050a110303040b0f0609010f09020f04030204060e01030c1215110c06040308070906020102070f021c 81
    0x44c42050000b60030b40802c1c002c5c07a16000e46c66a03000c903110b40041c800255003c4960360b60030702c1c2d100ca0507801031405401c04842e1a02516404058000f1741c1c455181802d007180b0225490000007412044c0100f0107805603005040000d40d6509092520340400c0854400410b20b61505500000311100306014810450140d50040c000c41002c04814031100c000390310120943d44a042e40074000a0550800110012055181c0030131602403104000195142d0304440380e55403c1c00445007600d04160020030107103101c2c40c0140d0010429007000c03040c60541a1015200310701440c2c45000500c20715024807804012241d1841005a43d04c031890384a00c03441c0a6904000d5005083c2900094610007070204103058034019420600d000e50764100d032641559500c8001000c1c80042d55145581c8903035684865040a50100703214a0700341301c81891800c002c1e040303800301c3c0403403502c42c140f10640d40d00070840006080c00740000c5203002029150082c050344680c000038861044094145940c019807511b003003502e64 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 371477877 1250 371476627 371476691
    0x1a010f02150f070201060f03051209031e010207060b01020d02071a16060902040b03031e0d0207080c070314030a080a022b02040806060f0609010c02031609050105030f0706080a 77
    0x2c2c18a40185400070685000005608001d000b2a00024500000c0d00300c80d440401484803000e48030010b40c680c1c00c82c4a40b180d05010300140a1914400700c4000940d1441e5a000140d0f10901450994121103091801e40e0440d4044410456200c1d0000303001030680c0c0e50b4005000000c2811444415a0f100d250140b244451502504004000722608501c00491084809000301200780060550340e02400203904012441c0040d03503168085020300901c84111040d0000d45400e03103580340d940040d4000b00f07403602d07680c1c8600420000c0c010b1521035074034090342c0c000180d40340c45241480107100a20107040e8401981c1c1c00545009031003241c12607050201c00791002030309508424081e4100940007841031120368000d0000061103864140b0440180c90001031415040201082c01101c011700903035012a010300c01d000300134201c038a01910900c02021140c1001c200c0d0360419040c58141403003070000f0f401c16800f50609201e002c1e001019940e204003113200001d105008944c3d0007009404400309001c00030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 371479127 1250 371477877 371477881
    0x180b030c28030c090e0d050a14090d080d060f0b1c20041e0b0d0504020a0b0c070f0515040e040f0c060905040e070819060b10030c0807031a010f0215 65
    0x400c074210584204c80528500b042501224920503489500c0655544000740b42001424404d40c000c13400c103034080c800c000b00b1070f051204000109901104214094032055000704c1e01c062080c005005040241040005144160317161865100003401189048401c01d072240c0f9000104d10744075400102106c1c0d14100c0300160700075903828280258401d01500d40d1140740500811402e9602c180014221001400d40301d04d00507801104000403c00900100d070310109141d400610401030001401c1c4008010300034100451038060284001552030f8040340c000d01c0c68001c01002d00c1110803d40301101e0119014019646d501c1ca0b2120b44026000402020b801d15840c011450550006ea142d09641c410341c1c0410986080092013603031031007140b094201301e5001c1548006000040e180c070380860352095902059100003100007031210814100234000081e034510001150951010b440e680012590804124500d00801648d46140c10b008801d818440100000e55140e4420050069002c20408008044d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 371480377 1250 371479127 371479133
    0x1050d1b080402090703090f081c0e010b0307060e0d081b1005010e06090f04170c03041403160308030c090117071d010f08060d060204050904080301180b030c2803 71
    0x849402d80d0306034055980080091001402840386002e50398106010411403002503072901d171281d002800c0180d188051050f0008820458000d1605007012940049460303052002414500112903210101300310300740500030802d40391240d40403085900102c842c7d42d01c403040003508a0b141c0f01a21303e0340301d40c400c03001c4880c1d1058075544a68181c4115448000c0c403030300d6080810030840c406661050340d002104004c18000340c008414003a0800350105aa41404240300b8400c0c1160082c0c2d000c04201c4100341ca8124441c034040c4031004c40d849840c05840c1c652401c44d1130f603200328040202402e200c0c540008440301140e003e00300091011100342d02c0d40c803d51074240001843d151088000304201c0341c00708e03a298055070007601c006035101c101c0e59500820755a098100404140b5421050ba280c503820800400c00391165111981700da03000e89185681c9502d0000900100c0e44501f1082810524111404607690f8008c01c944d46201000c5904642c90410090403030307000c10710001c861070709400e505000410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 371481627 1250 371480377 371480387
    0xb011d150412050c06030403020606010e040605130204030510020a050f090a0905340c030309020d0501020f1209031804051023120708060c0325050d0f06060503010501050d1b 76
    0xc60f20800c2654101c440803414010140416180280503070090000a011b5503c41d50040c40952001080401c5082c4d8500c08103e03c0e0181112074162550002814001d11004010300700400b07051040c11031070854003075070042c0940151000491143d00014013174400f595846180303806041c810004005d1410002600c07145445000030b0b8070f500c41d40a0740ca10003003450585c00c00f800b4820540350b244401b9510f07a000c40040802c00d1049901061b4480c03500d021560910103841c02c2005480d41c50340d030f05999022240e0411004240080d164010842c011461030704001103107031040150b90100d15903c50300400121480a074028000c100c500c210205040c0803100c01d070054a072025600840942d060389501d544802c1107015510581d400303035021900c407441f10300040d68401c44007662030a410341404c040c4401e404440b280300700040c00200e89015080e1a601c034141c00030320100d00c204600c918141d405841404140b080c41e050040103d003c0a20003019000b19910402d2604608074100384e440010701 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 371482877 1250 371481627 371481659
    0x12032a0c010c08010f170708030a020606091302010c03080a0e0f030d0614061801120c02010516031a01030c02010e0604050102040303090803180411040306051302090a0b011d1504 78
    0xc8541c248050306507010700480045050314189640b6044150130030f0020161000c0e030340e85884892080080c0024400800d02c01390403146e139194040c0065092180800002080107401158a409000e48000060f038103d181904015451306000c1c10b03903a1842d04101c000d00c01801310707405038020441c5080c00104044002c5c240090107038010440e21340c5580010b43c50030240d421443d040b00042054800901000c4250803040b54140361041c55407009108100954941d4800701c0f003d07039140e0080c8850030036050b004104400a601c0c1c00c110f000d070002d00d10030035290903003c118149642c4020801015100790014031241c6401400c80d822410985800d9000758401d100c1540081e81c1c403900850407000c044121020a14484611000c43c6900001c020051103510a650103c400800c000800510f40b4040c00340309462540d4500d040c414a4018485026402411420150f1412007131003c0f5a800c207100101400000a004400c07007202400b01e8913403140481c00c02020f07880410700040c03040701412042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 371484127 1250 371482877 371482897
    0xf01121e0f050f0609030406020a08030a0216060b01030b0607030c060b0102030c0d021501050f0333040602030405010b19030b060a030c0e0a1401060f11012a030e07060212032a 77
    0x844c0341d6a0a04d80c00e449014031b000380c9005801410380c0e117010130101ca02454125125010041c42e111844412600401580300101d5810341c8615014205682600c50038104080a850319440c101c0c540d42c00038004074201d88010700030740d5a6040d500c0c090740b00300141c03001d00d49820212010103074182d10180d9107003980c2103100c44c486004400800d050600c408258a0340303a0150042105154038582c04004201c0744500306955900b0595410441c100c60000500450013040010380c0d904160070702600351208440b0603801007800d4007840c00c038481281115003c494016100031203682350840003404e2035004d5840509890350600c1c011030b224000352580b40c01101400020042d1030038041c0c09881c031180034400e01c40403a90161254482600400ba6800d10150640c00000c065a4550f04082d155410500b030320071000e61001e080940507014460001030002900041c910107140600c000d5540c2880b5201002e00c1717078040042000840e40060600c4004045801c42001010011004403103410102c114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 371485377 1250 371484127 371484133
    0x140106090f1409070501022d03070f031205061525030809060106090b04140f030d021b06030108102703020d080a14070f27050301050f01121e0f050f 65
    0x200d10451000203030402154411f801900300d41c9100a4058000c280300501040f10809042218108800034401014000d1003450404281f91681c10010204480000c0e080e0704181307000d0502c0a90b981c1c044400b40c0081281c40025501c00340c20b1032440c580b040c0b011070b582049864030307001f408040e00011001e2242c017103001101d80342c1c0e07650a0211110503c40c031500c55003610400003484100001104652017a00240038080b0280c81c100c042840d04402075041d10040e0000c09481d010300350350101001210204482c00c1c5d0565040180186d1658104481d450105a80714598008031955020107295400c400c900000c840405050103912210903010b000700184a410029051950718418801d0003600100246020b0785d442205641003880c400320342c000d0010f918440e000c03140c0c07801c0c00d401a8803110480d03a40f04c5454a42414256000501030100d14421180180841d02d007000c1070440c2c1d01d400a10344c03aa03502113041ca51040344220b100142c60403c0b03a440400030302200186035440750381c50500b1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 371486627 1250 371485377 371485381
    0x212010612050f210909060f100f020111070c050904060e0a200607050604020114040b042709050604031d060415020607020c03031c1b0c0c08070b0403140106090f14 72
    0x181e40c07004d591048000448000a001c2c90246003403600019500c10405081454505a09000078540c8600d00198a00040c0c00761180f11507143d0a000341d1207042c050354841d9040190a6980107940d41c41802101c0c0135520180000301072008039005a4241010301050382c506400740d040607401c2210344111583c00480c00440035800b41000710841d6941508000034082c0d58840c0e6004448000360a6014040184148004a04910a00700520050a40c00b0b103200c8c110038009040542664802414000d951814040303501098010502c0e0368032940c10300d891a905515151070003c81c0447c101d001c1c0d00031030046008958841001c0c0101d42c041c00c9a001c459881e03807801c0040340e03210084101590142c10500030036240c405501c50404803449544030114940460655445450000882c1c050004d881c074034190341441a254100009809860080c29240707042011607001ca04c03c0d888001c1c1815604185405d03c0c40007980902c001e0010190140704001c40a6900c0d8060400e030340075102c0c0581c803500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 371487877 1250 371486627 371486653
    0x10110705060304080d02070f0606060c2603340504030605060f03030f0d020d0e0303160206070203030402282403330807030501020d0c0806010c0212010612050f 70
    0x401d9a200d2940145010b1400d80c41d1701e8000040e41200390201c805103410040c09000031020300400c0c000d03080f0350f035904c0120403150030300f10100c2c2d50700b076414100903c4904201810340120001c0b40d521405841c5881c000c12415904030b82e908044100440c2c0720303008101c03042e0040c1c3c1e01000520803280154024046900c40320300f00224204081801640f542c0304204814408000401500c0540c40041d801410518422030a10a84184212140310754000004000c80e588102d0250303440300711030388010300b11850002000b80d41c07440041d1010388104807116065001c50540a981a08801140da2541101d80e5800a081000075420701c040d01c045004411003100a2003440380d8000c06c8213a021030f818140d292071182c02c8080200001081008602d480410640010000c107001184a2400103a403100003d280314200e4031000c1c0304000708518841840040ea0303000b400014500d030102e07580384000e01c0b00800240108120703807003460141600c54040b000c0c01000b1500d407002c00b124074203603030910034200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 371489127 1250 371487877 371487889
    0x1504090e061618180b0613031b06080c0f04170105041115040308030603150f040221151009060b09090106020c1f0302091e0415051e040b10110705 64
    0x301c04030032940c0302d041d00300701012255544013a65900d0840c00030318010300002040483e030114100702440c200c14007040040010103490003d000d02c1c829404299141403810041114002034005842e00c0808a03a0318000080202194020151810041c078070b2101c071080a400381ca41147c0035200c003607501003020311034100301c05c05462526115081a103840d00755a5141926003001d0102c5030548140701a00d03101c0026184a82d01441440341c201510781b400f84104640c45e003601c0c00c400501a40d0250581d0712031710014118980d8143c0c00f060301d240d1340d6204690a4208102d074030600e08103040110018007141c80c6170050200d46025281c18109a03200d05050383c0d90440980b00383d40000a441115104010341c0400e606207100500d4054030384480395001854041148014403c00c0c001915018072502d8039118202c0c1c00b20712800d918503018905800a165281076143c4142c1ba0010a004c400c0c0d20355a942c08402c4244005040701615900038000a041081901100c900c52090050208152a0034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 371490377 1250 371489127 371489147
    0xb0109060216210203060f041104060501050904051302030d0c05100b0918010e1605040b0108061507020f09010306090b07020307080f0a0507061e061a0403021504090e0616 75
    0x1814810202d500d00543e100c14950403c1c45403194402051020340141d40c14003006c3c1c02500368040c0f92682c0c1c10a4108500448100c0000d0762040d8500003040210ba6000000d032000d520b02160002055038825503842445ca0000800070340c10f0040504246083c0e42051500c560103000f00c003240c142d640305004030011244c8100f0031aa0002ca2800010121070003001c060b0754540d00440081002d044000a035880c14900035511902481a91005c1c4031a09140c4280d0300380039000d18003900d60782003034008141e5101048840983d0600000348040c15910350f000b002c480c000d000b4000002e990b03541c5c107008000b440e84400071142c8864140116550500c00001e0310041900001c1681c5082c40c49424451aa80322890f180f0921405010610209410b0f1180c240d800000002c40304200003003a041710201d41c0317607802010301120131242d00c02c5210140c0080c0d4050303d40c150f0729104000360702101003c060007a60b01c050107160400d90a4207001c1c201040d01402132030055221030501450910690310a552 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 371491627 1250 371490377 371490403
    0x20a0609061202120c09060c0d0f120507080c090d0f05030a230f031b0304050c010e03150a0213031709030c1005030a0507092607060305130305031f090b01090602 71
    0x80040429440c008117402850045402800f040c6001c0c084000c01b03091030314214260001c00d00480503002849c2d00312100c6104581240c508102e40d1034074803c003034005d41c4c014004114244c401b10704540c00e42c40315990f6640a941010500e0074200c0a850f0860b6039510a210f800c000800341c0f03a500580c0c48840c40c080803000744090f905814130b801c1e004a013510760070080c0802201346010700c1010468100b20000c5004600443c003038410007045000141140d030089046d540a58003401c1d064404481c0005055085010840d0159442c9411307a522000f00304650400f40c080480c0822400c4281041c1009145c5401705800740c5805001000c2000b0860811203c4040071520410010310740a025501180e841051800d1803002036844502121010b5a03074243c40c2003034003110000c3d0b0284001000000c0c000d0040b0f18042c0610301c0c05901036450b0321010300000302440004008110078072040503016440c3c105003020800d800383c2d10704030381b00501003400d0400d003c5003041001047c0c1c14030200300d009074255 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 371492877 1250 371491627 371491657
    0x403020703060c02031207020f0d091a071103011508060601090605030a0b01021c090303080906130206030426030a0f05091e0c060d0204080f03070506040f0807020a0609061202 77
    0x4074540301c800181221242541c2180030800405071801510f85607140140d0790765005246900d020868039103001003004110040c80310072035080240c10010241900d40002d9083d08a0f200c40d030710314003d0040c45242000325407650802000341026081813441c8012541e141040325001d880d810b0054070000c0b614040c038000070700c003000094912807440d041000304074070620450b0a00e04a00300b100300d0015131032400702c0000744005001c00c01e1592001c01103130401c0349480030340704506181e40d051050100341000280500300c00310014050180d10b06d189881082c6640031140104509060720b02194422581d448a0380d203446010400c006c107910400d8490400d00006060503107504056079a180c80c02510b0200d14803599949400544911001e40070441c03005c1e8000da100e500b0031004904100d140362107607401d42d00074000040851000a4160381083c0c0140c134502250645040140e01c603c1990006900800d000d200003d5081d4841d003400100c0c4c04980e0340800b8002e000c0c126509074801d6030f40c0100741c04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 371494127 1250 371492877 371492879
    0x2030627041e0f0503091003050c030708090709021c0627021e0c010c02190302060c0a03060302060c0c03161410020f0a06060e060d15090611040e040c0e04030207 71
    0x140b6100c00000840e02039442c800d4079a03055507100c1030712803000601101c00d0741002c15180d50a0911006646d1007040c2c0d4102400240f802c0340102c14580002410b4a08200e0701c60041420540144040320140026000c00e6642e40000c0f4900070030240030191403c0ca141c40c4c0040021904180ea80284181107140300b914400e845007000c61010b9004410f00e080c09030300050b018400f0030111801464012000c07000884e001401100c0a400c001400d928504e900c2480040100001d03400308100b0b520a4017000101d0719509044000c9000341907030307007009400c003600188105142c02c0c0000c05110343c9034100d048800354520443e81e10003100043c4207590605190822a401c00e14080549540403001c600c11140268103020240345064080081581c805680e520b003070100c5041c0d151042da1114081e60006254500c590340c901c060b003400d500c2c10490550f1005060104150350300b0000300c08a00c441c5044e191a10b60403900702110096808844940003003000260100100054611468251f000f9000300c1d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 371495377 1250 371494127 371494133
    0x170c0a08070c1b030f02180423010603151506090612180c12061a0a06030e0703080406030b0f0a14281706070305040b0106110a0c06030203062704 64
    0x322645500b101e80c894520640c6080d020f074495004001d501030018200d00410500510606541300c2c0841440d07028030301e00308404541c81502c103080740500080e208902d00d8540c0041e03030052440783c10040440c45100b043d0b01142d140ca82018100d80d07107030b0341401c01403a0744000640300b040c03041c881c0c400451b02d40054030240300320f50750154071203119001080120700c1e001d40d20701205500e5500b0038501801c101c000a0180320b010f200b03000202e2031490300d01e4000000c81c0e000074412442031107980105070f05e83d104003004c04800e0205000960b130080b0b0b80707070701c440c0c03140320250107082030300d8080307004104180865040d071400001c0641100c80348103141d900c20401c4001d11580381c0301c0304074405243c1e80040c40c0420f0b0920122649006218050b0b12000308080a0902414440003510120405042c901400081000610080d044a50320306180c02d40c080c08080301e03030610050b007402420800c001080005e40d01c0d0160000e40c8241411241042c0c000040b0461040c1e40040d02d0f41100e80401040000f800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 371496627 1250 371495377 371495387
    0x2103060e011e17010e060c0f07240c0908010b0a0e041419030e04051f06030b030c0a030b07020d0f0203030c0708070b0709030201030b060a05180a0f0303170c0a0807 72
    0x50b92580141d280c00c81d42d100c00201945a0310303241c100c0c1e40782c0e6480e44140300200083c80002d400c0780b41800018500308024803907190071701402401419000c0828104807407981c014042d003060703d141103802e00c4810545480070b000b46180d4814450203500b041140e2985140004406060780c3c84a4085d078100c0c0c44940f100b056440801801001c41d00c00c112140c01d0031b0b4000710140e04401e1007686d501440c0002d20301404140d5601401041011805003450940c3c0b9165101200c01e860940c540080e13011407081c0000c0c41e000c10040d03115001a000403011040c0400030000900c03560040c0c01301d40c001c1c040c460044452542c80004080180c00034404540c1c9416818001c0290794019090301d8205103e5440b100e048000c180d0b181c40200b401c002c0d0030003c65803d80a10802d8104c22030391281003081034140504a481040f6241d0508200840c0c1e449103944c070b420040c405407560b00d040350000d686038a40a0407201032030b50078603480c1e003201c0d002400c85410001111500b08581e6984115919118001e03aa = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 371497877 1250 371496627 371496659
    0x30a0206070b06031e0a1a1501111e0609071e120c0506040801020c0f0d09090f02040e0f01080c0307031208040302010908030903070c050a0b2203020303072103060e01 73
    0x19160260800f80030401090030004551700c0304210241c101640645890840d861a070740b0000d00c2005000104644032444c8400007005400030300386040e426941c41071981c1004880070f40c0300c441c80300d4100a0954240b00003200e500c94440784c400c40b880380340c0300d61400c040f40b1020341c00d80031103482014051140c21032040040c101c5501c1440c1042042d40c13070740d00145c402d03000358100d441142e60206035400969001c0008101d2010104098030b5920341c20900100303851098000c400d0282d480b0a000d01341c0b000f95074100c83c010143c140101900d0705040b0b80303810f00d2010030302c1030800f140f1071403030300c0040b51801040306021207901c0b05d103640641010190540f203291b00140f0503000d55582c6c5100601058044004500c9000c270903010390b5588029103840310554076103400042c00340c4c1607400f050211200c8002100c40c11007842e02201405c103552101400b04500c181c100a404d0f010108018081010034082e18840d0a0f40200d0300e449841003280850440d201845155500d0410600400615910801c0c0d04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 371499127 1250 371497877 371497879
    0x21003020c06160206070929090409030f080114100305090a020315010807060201020f090405180d09030204050c070c03060506040f050112020907090b0a050a2c0906030a0206070b06 79
    0x5820310406241c900d0814100319140c44070f1107000c60306a100d280d81401041e903c100c07103007402861a418101061111062421648041d511142401a040700c8a1050304c1036084020424807106040e454000d0841580500410200c0e0464002042e8a0700750340c0c40611001c0c000c0c100c2500c0342400e0307000f04d01406001d000c040300d9001d104070076805610240039601e10700701c0c46a00200e16514004a007450442107a000c4030842e441448801d804046a10840700c000b08211408111900c03604282041c116400411020724800c196250684a802190110449000725004c04c12550740807003110381e0f4451f06000410740902101c2c14400901254003143e0440ca020b8000207464240359030070400c4680a0b04500c007803181c40301514045203400c00780c03594815240d103045135105180242c400725501038014a032041c030001042850aa13481041005d40b46a400c04400401d924044080b200101d10581418040d4018074009411400d001941810849e4043d229a14090850300d5601c1008005400341d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 371500377 1250 371499127 371499131
    0x30210020d110705070e0106030c0e2e0801060f111c050d09081b010e070e060607080a050a0210020f0703030e030906040303110d0f05070303090c0e070e030709020f0403021003 77
    0xba2140e040c0400340c60403600c103400600360a030401382c4a08046405900000030107041c4021564065840a100c21001100740d4560b109000107108400308181410840580000c00300740c45000c00e680803051504071002c07030700e0b822301003109080c0c200e43c13038002c00000e04281d80c02262806012071010800c16203603600703881c02505100e00c103074607001502c44404007500e1043e8041481c04000000b01c5000003240103844c002c00c03079001e01c0074030b181d1075500c648a800c0d0621120700003e80746481c8c000407203d04581c000051a5504110a8041c0454214110032001886110101502100d10744201e64003140b0041030f060600c48555800c5000e0882e80744120310301e000034800e0b000b0035210f0320b0242002c0c1d0f200e52034080d102880d1810300c51a04551103405410400c03003010525541c0e81110440b4000307501454045811409030030142d803d2100c55000120850040040110745507002e8580745040d02d0072003e8171101c69031481d0310020307800b46020f8048444c00802c410001441c1415514030f50303095178100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 371501627 1250 371500377 371500391
    0xf060507120c1506030302070906081507030209102708070b09060c0706030b191202060901020a170a0f0e0f0f0a0806010902030412050c060c0c01060e09030c010612030210020d 77
    0x50304019050543d090003030b00751940b0301401016018481e000c040d0010300c504000c06032a1200c034582e100c0c041040011002002d401040b0554842e13011074911b1440905080000580400018107002500c000220080440c000394600107948441000c101d4004100402d401070070520100340950107030b00a02d0b0703c050200800700d00194180700780b5006100176100040c42103803200600c080c19500c02078203d105400c03181d083c00300013085d1501040e21a019130f40c543e00c4000c80300041c2d00d00f83d00c4510184c21101100380114040c410b520040001d40320558030418109a0810199201450100c4c1d01d0343c0039880c0d40f103002c031900742140303d042202001829080855030362060141071003000e8000d4140141c00100301300a2001101280400901600d045840c2c509100a1103844500180a40804880000d4441d81c0f0202c00d401c01e802410300e520740d00046050442d00a40e42e980a08440d280c1c1e9400c000c1c0004100e80d0807015094401d4050f0060420780006421081c0294406052240000d80c3c4440d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 371502877 1250 371501627 371501633
    0x30715050c16060c09050604031e02012604120512010e1b031f0506030708040f02030f0d05090a0522050405070e01030501140912070206090315130308010f060507120c 73
    0xb00455a41c0901c0d400a0324030103801e002400c4482d681c010314007600c4104401c000050742a802c01800494498041500803079a03c01210034a030701202c03200e810700ea250b03440c0c03511801000e032982c0254070a40007408078445003c070030343c0d180c0100020f1031484080343d0010800c00040620095000c2410601a074009a43c041c3c0c26a1a0f08160b8914000c40750030b169483c26620034651a001030700307003102c0f05425031400700d400500c00c210040000381081c1c03102e160801152010403a20003c102030f01c2c1a41d03184001044001c01907003151420034820480e12000060300c0c1020082035900c200940948c00680708101184000303060050001c0b9a14401c44000149260b91048100d000c2d520032800403403000414803200740c400c48094080c0d91150003510030f0780c100002000031581c02644c1a19070725268600c840010341810048003003026914406010454480c850044c151100d600c04e4940901591b00c8903120350013003000303028400c003003030302004071002044ca0321903103a418410915103410031440c140e17 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 371504127 1250 371502877 371502907
    0x4090602070204140f060a140103020a140d140604020304020d08071b06050a02100b011211040503011a120c090a1d100c121b11151f08030715050c 64
    0x13500211600c8214001d0014020702100b025070007070303001c4030024000d9081902c22404410000c0b00581490b0307000030044004c03401420310044520725806995107902030f4040b901d01034203001c1100c0c5458028134001401c540b07414402d5074001c5401500008142c030095a4803985d5034010070055450002103d0300c52a036200507c0410013500d00c591740d0030348818444c0c001070701d04a40707440d00201c0c00d400c0c9100d4070400e0764024208e40d0340c16000036003c142040c1c464912842d52140b50070481d05542040c0501c0c82020b44102d8480041c24140c82d100d0500b1410a24103807030303914810f02d0640c06801000800c546401e82c0d045a0020401c9a8203201040300301c0038078a10b814a190007003085583c54400402080e904400101800d8079000e40500540941004040301030540d14004400d1190141c18400d60342820441c00404084a00803015141042c89011040405804290f001c6030f0818101141040010003a035900c0c56000003500805c40c3c0c03030350064018100007000485e101c20b061016a984022030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 371505377 1250 371504127 371504141
    0x61306060f11013c09030215070c032f031810080415050c040806090a0b10060203031602031306020709110a050315030c04020a08040215040b1806071406150103061404090602070204 79
    0x19800078902300b02104490100028000e010005010440d4601000b00340c100a01640c0c42c004040261001c24268002d1b06c070302c10381210940460320002c103150307007201400168140c603900115200c9585032038043e01100d117444200d40080410308003982410a0b91501e4218541180c0c42c3c0007c07505150329800c00c5450003004403003d507000d6005044503c107124204484581040600c08500e0145003000d201030358074800501410403000740c014501c20f020784213105031441149174042c00f24041340c1e41c8070002e58804080c0582190213140c91069242c0010305021110303440259103546007141c0c0c1d58180c05507103006070710001c1d8042c001c440c01c008080d966840103190440080d205d0305060b0400c5e00500044d00c4080302e8007030681104000900a200b5a0425240d403410043d01c0d8038076008020020580034028101c008184003084000040c110001180182c80b801003881c004901207419401107068498502c103a14503001c40200c80c0005050a410100920703004000142c500711455000c6801c032030032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 371506627 1250 371505377 371505383
    0xc01060314060f060f01020a02060706062103030c0806010c120e091003170711090901110a051b011a0420180901090c050909061306060f11013c09 64
    0x701040038403060110821340200007551584030740140000041e691b40a50400a4841c0d4000f040d6842000025004000034125208041301e1604400c3d014882040480008074082800c0007401070150384101080d81c41000d050b03507525040368454440c0c00845546c2c44494040040c0300224070314580f100b0b0070f59800744c0c2070800c1c241c4800b465030070446911000000d454008090401003140850700d58903800d4480c42049500140310740b281c1030403500405410407140b005400105902c0140c9420030003414440f00b40d44000c480c291881a4402d00700c030805c100c03c0c00a0080201c0a014a0038180d00100b82c03c44c080104402e00b824030101e411140d00303c0c40c8041240d440400141009007000500c071801001c00b80d80901031010386001c00781050080d070030428040d42d14036002031110386c0e0301c580b980b02d81ca400c04410000252034401c000d068124070b03428080451300300d5244610103541440f4441003032030815103500f4103a407148000000014483c04205d05401051840782c18500c3c0c81c402c41c00d5441c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 371507877 1250 371506627 371506633
    0x91305070f05150c060c0c030403061b030509010c23091201020417120d0c091503090506090c031c02010b0613050f0f030606010e13060305150606130b0c01060314 71
    0x880e0200b0048205403d41c0a5190321505014a0703000c1d0a000644036009224808190744901b50402924558001c643c00504914200404c8078820a0310640c130b0b03940b00903035560070b01060752502400da0a0f6420003141e04000b070300b6142c1105550701d19160208010554041c842c2c0340c204114000f4658529817000d0354001e940c005070800c2000001070503810074048210103020004c0072151103030303441d0141840c00c00e00c85440d07012000c1c555125204000280c03030f65403030301d040b40c006a50b0010b00400340030800f251355100f154086090a140041c032602d08900007802001c0345020040002e03a40310034011f20805640d00c0d000da90241e652000d01804284590344d628404083c50301c410411205403055041d03004074000d43c6a80c0054801140c525800034003800d00c82a1b40c190800401e41c05c24505950850301c40c0303003000202c204800410100744c0c503200c1460700f98203038840d541041128415800803100d040c010305000c1119901d4407010b8200c42d092140005081a81c83d10390140300c41c0003050701c41042d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 371509127 1250 371507877 371507879
    0x90801140915070219050307080706050a050c04120828180f050d03030e07030206030a0e010b060306100f0c060c080601020f010b013002040305031b0f0a02091305070f 73
    0x40000c009180c1c000d4002d800488490a0010019407500000c002040c104260000f10701c042c4401001100c213520342c40301085035140d4031414004002d100a0340c0102800c0c1c04d00f030110b203101840005950a80b4072038008151007011a0b950200140d01c400d05201018268024085541601040c00000701c0ca050b290410440021008442e0440190b005440c9882c0e800006001e982c54001c14038040740ea140c1400203038a023044030041d140010540c0025400b6100000b041001c600c03c2c2c000d04150441c0f480203006280d43d0340304116060108481c92074000541d65a00762407140305600000d07060566013801610841551103000903200c189581c80c0c08184007005001d601e5038100980c5410000d00b1008000111030031700024170b100f500182c24140c100b25211030540c541c92014083c00390824003901150740d00d940b03181c81501ea40201144c0c0c0302c003440f2a031280e082c4100121310b54460840c0c080160044502c16800c0080d010700c0542400800d04503585071074002803080000c07102610301000d02225003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 371510377 1250 371509127 371509141
    0xf0d1b0602161a07050412050319020115050108130b0c070f030e090c1905031807090b0a05120606040f02250507080109080301231503011e141009080114 67
    0x8400f040c04442401d5008101300401e40d60f00c40165010b850700314440c0083c04841d400d281d03195000f50840001415004a40340400640540c402e844200c00300301c80032207241c3e4803001518003060403510f030201c441c07160113404000b0380880d5142e503100b020700d1503444c20301e0b0464803404602090040e00300d01041840302d401c8078a290070340082c0c1d4400c4205c06a14601500462420204100c0108140c2802000300104108818801000d001d07007410400319103c180d5178081e01030162004444090051a01240128041c100051803e1090800d41d004103116160502400000c0111400040c4603542c00e00031440d601e041e0307100e80d201d000241c5840700080c03086810070a0425099510586c00f985c500410000002c08400239241140c1c42500852034242c850150301c0d0f021100c0c80101070b445400480307050450034103040658141c5100b4990350000201c992480381013501d082c000c895400d20030901140c2e041c5090055401040d075140780c200c102a43c0c5032149802d40e520410100002c4a03010204800c1e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 371511627 1250 371510377 371510393
    0x705070902030403050702041a030a03081e06060f07030507170a0305180a02011115040b07030c0302130b07030905030f4c1b03020414030f0d1b060216 66
    0x64065a0001c41c618206a80e004d00a0321401000030700640d16828200315480780d02000712245036018090b0350b01a9110310b001089007900f2508050711812041b4400741c0365540c080e40900c2040041c05170391074003039a04640302c4140c103d5a422420003004104110025619503400c60882c200f1800c0b0948442002c2c00141c1644d00041c50404038030603701001c0c520280005110541980a08045820f40341d0440d28505006007504400d0051149400f413104100380c4151040c4607000c00c1d50100000c80c01e10703000b102079219007451100750500458051004103100002464030a120b030410900d80e0380e0740c001003420808007100780141900300c0751407400921070031901c0401c2076000c002013503039140315091310000e94040015030042c000811310721088124038647c0400c00014000d10301456402c0c2c42c480040c0654018059003c4124a8034401400c5080005660403034207141e20203440c49205031001194452070450b030803c2c1c01540b880c4d080020600520042901c4030700c1904020200c02681080c0c0c01b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 371512877 1250 371511627 371511629
    0x7090c0906020616080a020a0e04110c15090a060b1f03060504060506090916020a0c0f03110d050714010e04230c04030b01090506040b040c090f060203042414030a02070507 75
    0x1c503005034443c0138410ba4402c0c515503020b18410801a03c03820219012600e0703003c411270042e0880e1400a070001c03500b90350f00c00f400506020a00700c4030400c4075440e1140c001130003a40c2041055000664042c00204aa004542024005801607500c11b06050b024031540802030322190100c0c1d41d43c0d03804d00140c02c0c20301410300900070036101545012160b1000c40c120b00b40c01061a0050722a00a180c06668030911882c00503907080307513491041c5502e5842d80403400e4014481100c0708003180d500c86032541002c0503070744511504080503081d100e14100640c826151105c0b003190400500c04400c4145964074460040c00c1100d0030b10010789040702c101050082100500356848010341880200006010503d415055a618071001325550707c07240c0105000e0601050804d0f4042e040c981007031035142d4071090403c00c0701d00301e0a02070704013503441703005980340d02c140d02600c04003410f61800100344480010941242c2101881d18004401c5402c00705905030300280c1d40c400040781c00081c182c0601200b0400c9034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 371514127 1250 371512877 371512891
    0x810080304030c0306090c0506070c050102100b06031302150a0914030c101206050411071a01060c0b09070905010602030d0c08241503191a0a1707090c09060206 70
    0x1460103045466a070040c0300d413032000a00700340c1c03215480d508211159102100400000d00354a490b030101d450018552001402900c0c01442181c96076848030070a4003500c01c0b102e0018000350300d59100e449050500c000142c03400d84c0c1001414100c6506400c11000070480c044082d521600700324144840031a80502003030010f44607510403402c011103685d030406425403011aa04210480e052144000c0014041c0340d0301455016150000182ca0226080024100703184601c151804003041300f5030218070404207001d0f9400280c40c41c3c642b4000200841c81882d0014510000c13110a6550b5000c154181c41003608401c00581000c9241c4444002e81d004026020b042030410a40d58502031920154100300080890144c1541060784005a12041003008134a040d0000c5207a40746081d0841e101243e01c1102016045481c00b80c000810501c0000071240c1c0a100820144110349403400540024070119507a009902403075100040d600e00740d1090b0111203820341c842021091070a1800b07410803400800d04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 371515377 1250 371514127 371514133
    0x11808040b030a1e05071710180b040501120201020d03090809100c020405090618070b0a0f0513030b0118020313080c03040929010212070312090f03081008 68
    0x400140805050300c003560450701c0c00780d4680e6601c1801c40c0c0500001400f9003400714403089135060240003030300306611406a6807182032400d01e094462a1801c501114150071205183d0000d1042101c104400c0c3e0204401000215103000b0500c00207084a000ba40400c03c0d22504540400c110b58040c0000407404540e410704020f858619143c4415a00c10300707890038840d22040000b14000d9001d60036440c00307590042d001700401d19003202c0301c580c1c0d44010703108400c00c41601142103e0740f00d000680d0b40260741103595010700300b115444c0d0581c0c07044025407c03074040c04820f11101000059030200c10004600890545086500d41f040303c90302c01c5028189181350b030b40100100110150034040c00c103151680700c4070482d0f49010100e81c246c110300603508005078007070520300d0b1080e4619000c41c0d60802d00380030103401400c900020303006aa4a6030b150b112031890340c0f814001500800e0041e5840c0c0c83c1c0752440e10004c20300c00a25599a40b600f40e841c1811030118000809000340305c3c0d40060000090310f586401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 371516627 1250 371515377 371515421
    0x8030a0947071b0501090501060905010906060905270c0a080604051e0901020f040816050105040e07030b040f110c0f0c0117041b0609080c040902010815040b1002010b0301 75
    0x100050150005025006100d4100f003002d482c5428000341500c5a500100204100107140ca001c1d4041d24240c46441d9580381020004212012244190300454000c1d0300c03100d4815151000388a03840540d00984140c06c592140412100121401054490070424141564500480748040d0040d000a000a802a4541000c201454448150b035821040c1035104220307035a07460529031406482145911260300c80c0c0420300103040c26002070303c40c1034140c06048440d94180c8840044401d4080c5114820380c3c0ca01d2040420354045c06980031b080c41620181c004100201001ca0b00026160401921a2105400186080c03090000d200c4a41c50b901d58074040c04060341d9500000b4100110700b8902000c207040c0001040810145200c081005699046104296565804c9c0a0405a00c0c0d00c2281c50ba0701440207038042625243c4580c10040b94161038000380c0383c031114503d840c0100090500c0b90050b94455411203d80e5401c034464044022550010501c0440c806c241400c1d01d417800c554941e03201d1000d0f6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 371517877 1250 371516627 371516753
    0x80a03092c190c020a030e041103061302040306050106090302011e05040b090d050a0f0b07020607050f0901030b0307170c0301060515131d0406060b0304020d08030a09 73
    0x80c2514400e0502030401c22541c4514a44101e8101920402e46030320b40f61441580c0c409401180ea00603940c040d0315091f003042009010b20098880d00760b12007100010070000607026180c0456284c40302080710b58014149500e9a403100304803079080e00300c03001040c0030100030403c541c0e01091001d405410003481c20101540e800307000d0240d0085001e48100d03282d003c51001541d440762010400c0d6142c000d030844001500605010041c403490140aa41034402c030b04c00181c1c0507000094440c0190180d64425180c5062071101c2c0a0f95041415454109502d030a90450030765401c005c0d15020300030800550542a0403245814901100403203114002d9041c650200116030310000c00940380c06500d8040c2c3d558492404070700b501c140060300140240800c02c0c604580040c030520165214902c0b50400f0008281c4451708107031140000c940007036004102207c0c80740015040b4001d1500645100f0002c282c61225a540e41e21401c0f1140c62210441d80e12414220400d4002d04064501018003208403800040c0310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 371519127 1250 371517877 371517929
    0x3060103061a041d120a141b1f0605100504180207020901080a02010f080402130e030d0c0c12030605061617070b07080c04080d031a0307080a0309 64
    0x4803024140340e540c0c0380c82c1d80c401c81c031542c03440034607000003841003000d490421449002900fa4151015a510454200300e001643e00d00850700740c5100e5032525038185101080b0143c442c2c0c002c003560070000300302c1150b2044029041007800c0060050002c9904070303801c0618054100c0e0b40c1e580c01184034201126003001b45941040840d400c0d660300c01c28004025201c00f0100000e131207850700003900509020000a0021008034501204074401da0b655001c0600442040f2007002040e500a50300014070302c805406100141e005c8044190850290303070600380100300c51402c69942480c200041000c01001d4070400401a184a85844071803c00308655400c202c08034105010303a20b449800d00005400b1501030001403091643c40d541c101344583c0d50340001e490000d2002d5415940034020031050030110f0b880a1160040e18140c0c0e549138020031002840e02d00480107051036100502111403184601c2c40c0b0350320705215100281034120300501c80c42e04a031400500c40c46131640401c02074030300c140c001e01850110f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 371520377 1250 371519127 371519129
    0xb040b070512074b0212150403120207020109150903210801090510030210051c090b0703050903180f09010305031224130f060f061209110d0309030506040302010209040f0902030601 79
    0x1c84c4454150340b205102242c005003581048015504c9880ca5812140c0c1e0300100561040d40302e50703180406402e8440901c81a4042c1c041d00901241580b00148141c01120101d001c880318185800100580c0c0c0ba00c40403281c14080c101030b00c014a640c40c0640a450700201068018055200c08000f64500004541001036007400002d1150950002d14001107204009543c114402d01c1c0342c0341c2482001100318001820840c4040340c071044004d002402c000c1c020301c1682d1258031001c024500c0d0030f410340c03000c0c000d451607188280d034003110b441d605144603290b07145494042c612941c0215541c907021008000801401450060400185404803018094a04001036071507800c0e00e44034000085510340001500b45103004c581003e10341800041e10403075040c50441160060744501c2c025450450030802076503440740000d00b00c030385002801d0f0304038186207030034540340b50280c0381c03602d607442d2681c1c3e5803400c200c4180c60640050f90003003501d240a00d4640725080608000440400510689070b0200381c03a4001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 371521627 1250 371520377 371520503
    0xb0a090522170703020a082a0a0f020f15070b09010e0a05030d020307090905190c05091c0203010b101206270f0608030708130509010b040b07051207 65
    0xf145540c201030081140d001d507180c2c85800551150600c40e042c074010f08000a03004030b00079880c0e2416003401030110b59141d18a40004074900c0c651403580900c41c001540b0418aa04042410405241005501c0c0075140c090302c51084801103082c0100c900742506d6083c100c0000c990000030b41e41c000984000200d507002440c500740940c4070b541c0c9610560f0b0850040c0d104c40c0c1032074180403c11254503009007260340c40856106007000035040007401101c4c40e0044184064028407034070407881380480c1551098801a01c000c0010818040c20b5003c10b030303112640d2610002040c6510401c050180c5980180d43c064265425644442110301002210300d00e03074040d2050100d035840101002c015110380025002d8030b0901c1c00c4036512505031500d0202e503070003441808112040c0900c04034030791070550500d80c1210302000506042609125649645a10080045415208807848070403010083c10180c01300e103000d440c00e15541420b4103240744640f0703010b908500300b100e18441c000441c603030080390799014006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 371522877 1250 371521627 371521673
    0x302091e07180e01060804050d05090a060e040b0d0b09060a05280905120c06060a050303121306060b210c031f08120a092c04060b0a090522 61
    0x14842d14440c03840ca2581c120210100c4000000f0a030340790003001d854000c0b0f22580844032176801682e022034950090409046c0c0c00782201004000c5184900030070742c00e00e03900810004440c4a0310000a0540150101c12101701211008108110106004182e84020507940600c910b00d455a01c00d415904000048180c43c0386014540400d100d803644609122030f1f02c801210805000d140c40d43c030144e008040d880010744260340000f41942050000e690844002074011400c041d07040b8031140501d9001800290182104000b039004035406000e440700410460300300356038a0071503840c040003001031803007244d2511243c0d005002e8080107480c00c0700d0b40400c4074004040395035111010040b2290180d402910907210701c45a4105031200d5000416001240c0e032100a042556407a0301803081802c2c42d81014036a80020136041038100080e00b041d030051050354006001600400020b9203002d4a4001e55080c076030354000c2080c0306102c86c00c5d508003854221a1a8184c0c4a13503a40c44002e110030b84108580c01d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 371524127 1250 371522877 371522897
    0x1e020303070e062208061609030203150403050d0f0209041a0a0e061c0809030606030a0b01062109050d120e0723060408010b030d0507150506060c070f0302091e07 71
    0x21344c0301504200c502c10240341c0c0d41c2169031060701329580d40d0b09886155022610942d4440aa40105c4118003202da020b40544030192035a1100c45c000c0c500180240c041c0034003040914400c0020307104120b20060400320050326003c3d903106000c00c0b01c481e618410402c10307158045c000c1607503420204000300c4c0c484106940e020358900010681418103842e1149061000c51441c0040002d40d0f80a07014800040e011070300180d0b12042010303036410039014040c12300c000d40401444010300c11909031140d020704c5400f1080c10740aa41d001011522050300980d00750300000400c5552552050081c05080d101540902290380d1600300e143e1640500d22542c0c8580e1074900c03601254018880400e0030281005061584596840380707030b540030784040c1c0700f241d00c00e00540f03224034500383c041d000b0f840c030250308803a0b10319071009010300003c024a000307460b0b0b682c440000c1c405080000b10802120000e84a1100d81541080c51031040c8044880c0180c00340c91070752007085020740c51013540c1c114954085180c3c41c042d4240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 371525377 1250 371524127 371524147
    0x209010806090601171906200304060c020a03050a12060b03091c0503090c0d051212010314030712031a03010e01150801060509070f090305030a08040b18071509080d1e020303070e06 79
    0x7041045072a140e56048244241c0303042c0010000345105900bc0e80050140e83e034200700c02c903202c0c01904801000308000b07002881101c3e2244450000d5182c2c0e412001803030946a101104081d0001c030ba094001307511240070700329261440d2003044801c5a1500304241942080c50426444800c07120005004002c980744880a11900b00082c0d648040070408159031010340000d00701120500b40030588044500c44417101119100000322504540c0114001408418204040700580f1011107200481d130300c80140c030003560341c080c0b00310342e03501c42d030321000060401c40d51903c10034114166114040300e900d0000308000a486242c413981e404016403402c5041c010b15408181c551419580004d0300a2001065070004150880341c600e008500450b14030319940d581c40c4940000384100d108010700c0da044950108051034082c00300044012080c10100f51154440d00554a00110310480c4800640d90302d040703801700c042040c100d00310300141d840550f195142c03050025240702c844200c55406040000340384000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 371526627 1250 371525377 371525381
    0xc01060b070f0b090a030c110f040e0313050a030b04140a080f0a080117070510020a05060a14010e0c030c0306060d0510170a021807020a0209010806090601171906 71
    0x18040040500d600d0300322605152180ca8182e060449186912002103140d400c00080d802e20950350650f660003094049940d01142c00803245009604202481c071003015607503950069800c0c80e1008001140c0794441e02004055510300c60740030328002c6013882c03000d0001c41c000c88031f000e6006400484990154000b0600c451801a0b029806804104041a2401c0c90403800340109010001e6680e10b1390aa6200d030808080020058072034581d0ba44204400c02140c100301109e42c4c0d00c49440e00558070514801d460703050500b1400c80700c01c1c0c0802cad03031400003204c1c00420000850240c90181001c14142c50600d264903401d11003e0001e030403500d40400062425a110011240501d042c0c400500650900c02014003607200c0502800b040403880c0e804490045200054007028150010020081c3c450b050b40c080600401c0500b8240441c06000034200150315142403050007406100000d0803a4a040b1807864100801030300b00300710000326800300c1c0003c1d5400280704d0710380341c0017010340815100d25440c000e00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 371527877 1250 371526627 371526629
    0x20d0206070f0c1203030b092a090a03230606010f0c050c060a03021e161b0305030a08090f03070b1501021005010f0305100b060f18090c0702030f0718020c0106 70
    0x10841007486000f0404c8421000e42e4180640300e600e00303010801304042008442e00040710380e628140540545021643c2c03030032031030002c1c014140da103062811102e1004200069401d800c140e406403c455400c80303c0c0080b2601d000f00f1201c0d0840540032078201000020064150145003030204980e580d240b100340641405040c005010003054250766a050080c00f401031b4200d03a0080003200c05807070040d20b1240410f0704661070b01c4c0b500b403a100394100560f81c400250b1602490108070750609080040001601000140040c01413502c400c0c00c0341c03901c40781d96850187c0124001140d41c10a01c0203134002240e10030300c9604808841007805244440c040101e250109565241f1403240c1401d000286601c2c06041030302c2600e000e8402d03104400340c04d42207082602c2012030500d8009008000da441c4603402c0d60050b03e0a0242e00c50a4402c000b01000080c0400700140c40040130301d036001404004519041007404c3c0040c6000002d040b10a240032a40310811440f2280305812540019031034447c01c0c802c0d4011340c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 371529127 1250 371527877 371527883
    0x605030115091503210905180f0705070809011d030601060315080105100e091e0d2a14010f11040302010801080609100903030605130b09060d020d0206070f 68
    0x11010349010341c801000c1880c400c12420601d4016003031480c04515907180305890b0090076000e0720340408031100c00034a541c0c000f0101009110400481d00c6d07030390820400b4085a217400d11807064100070007002c0707203c130b800b0300b40b0014090708100c0d28000890b40c40988101c418242031040c0847d03039540c81040c143d044d02101c540c4c50300a039800420801c0d0164080001c400349900d02482c100d440700007440c22200143e414046008a00d2410050100c02000c4964006440c0c420b0710040d20840160408603001b01c03490120b2500320096604200747c0c03003410b0040124203a212400b100c20842c0711006401c040303950240078007026588120740400c0075002041717200c800280c10020400d0074180501c5a420502040b400038407180000074807546e00155041c010314007000540000c25810403680010103110104806068581900180700d0b5229180f00310010490b00011400f07401420802141260041c001e902c1490081d0014015880f180c0600c5d86450b81a02c401e5900d2555003016844035070218001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 371530377 1250 371529127 371529131
    0x1602070b0f2a0f030f0301051203120f2505070f110a0b030a0c0e0319020a0e0108030306101b0803101a0d151a03070e0a120203190314030a06050301 65
    0x540c0364050200d000e2050710074003410f03165002c001038000744d02c07071040300d00202c1405000e00c010700c040e00d0030f60314541c5040c14030710849160041d040600c2520704011a0164107104091707040150380003140481c800c0c111101000040f140042c00c1c13001e0454018030758080c0c03c8540c20400c5804218408504281c0300500404000d095503448410550b130354011541c43c142c00c0e051442190304a409810301c060031940c010003510841c0001c03944400d1180d50b02c1c900749c0e4041d134203010015106071100103180c068205038018654070b00d00941407010000780d9070650810032000701c2d158141a0030784951500d106034007102c43c030740d40e03150740d40e2480c034140060700440c51400140c490b0010000f0580014450312980040502c0003401000d031711001d0032a02d10400384a12000200d412081010400555000d5031034100a1445c044ad03501094904405c0e801041e40c055807511050b0561404101090150014145c1103190020710764004000f030038070580e00030a2035070110103d0300d83c0440ba0000340140c4405402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 371531627 1250 371530377 371530417
    0x303100e070e1e0102011a060301050d111008070f08040816020f0907090e010f05010f050913050103080309010e210c0304150507291501270e1602070b0f 67
    0x20782e072407070090f080c00d8602661908981d511842c4161400021980c001010941503a10b40f105101c0407500c1c0000440344100402c1d00f404490355100e211883d246050307610102e903072602d060060302c0d20b40c603c00303810300348903d02d010000069898022184088043c0c00c01042541a600c0491200c401c0100140d45c800d540400b00072200341d02c07031491022a4030007050b01d06c080c2d036a128102c0440f0410b005a500003a048107003404802e0145c0c00412001300301411001c00000d1804020007210000e0700200c4400d1000014030003c000c2c00d002d804000242d210203040c02480f02c0701e085054117002502a0b903001d601080300c420050007441500d006001442001440000c00c0b0002056544800803c9450500e9001020007a190081085100e4541b4240849198540c006105041342215400d1410402404108200416031010a020001c03c0d81504103090341131001004440d58001c1c103a4002d0001113000c00c156586c00526403007120440e40c41681d4400d002c11940340b1a1203803d4101c064081482c013 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 371532877 1250 371531627 371531659
    0xc25050402030a1b0f08010b1c05090d02122a150a0507090b03010302010203090d0516120b0105120703060510150f08060301020913020c030d09150b01020303100e070e 73
    0x88516001094800e140c10102c0f00b040030b0b40c03120170f0036120f41e0000311240014800c000c102d8005001c401910002e4040d1800700c44e082c0420364500b00c800809980118208250154040000c0952400c509100a00f0240d03030300c0c44030b250300011300b40e0015010260841040721031000d00c801131800b0000150000d051a10302400c8020f01001d684120029000743c00000340603820314240ca040e0f0b80d05134061441c1205c0035007000009440240d080d41c02c2d00800b156008005034401c01d40c0020000e950103070300e10360442e0500c1d0400e2383c4140d02403030081d01074010070a039130100030910300213036580301800154a441d502100b00d01144d244e003003034204984100085112580000080030369810540d90b8100c10340d10417051500341d01031074100c50381200c03000000c0004038405802500b40030f9181c00480381003000740c000280c29107410341000d0f102d020300e81c00d05100c842c0160040d459030703060a000840c03030b40c1803c2480b0041d03c00b4500ca1043ea0120200c0402d9405c0d2080c8929548000300501820101507214 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 371534127 1250 371532877 371532881
    0x91c39031b0606080d111209062206020a030e04020c030304080a090e1e09010608030901030908160803060a0e010e04020913050d020106180603021e0d080c010b040c03020c25050402030a 81
    0x2800d94004102100e801c00c0604800250140030342d0101f411090501c06d0400502c242c603040b410201001140c004004030301d00081c41c0c1000c0081140d070b80100080035203420040c2c44c0c850321144180c00b9600400040a43c02c400000700c0703401c990b0010301a40c0d04c0a505d00c0844407861250400d44c0460302c4507060086c00410016840510b2902c1c900162080e2104c08020b800c03180240302c2d02d01641c1003440807000d1036000742d0180b544503005200d01e600c3c0244070545074605800c0307480100c0e103000c404820300c01c40c0c1c2405000400900010110b90015506042824411650041000b4440c46208000402041140f104914203a40c008103c5820415600c0c0c003074064445806810f400030880c0380084049142401100c080741c0e0040c180500d200d8101f80014050340020038030a400c440030311502e000051101004285445104000144201ca20f40c100700564800e2207015081500501c100030102d20042080d0583c42100c100c81d10076401044404180915564800e40e0b0251010040280c03001c465 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 371535377 1250 371534127 371534143
    0x90204110c0d05031815100b030705070f021201050411041503030e090a0e0f01410411060a05040e091c0305091c39031b060608 56
    0x86805000c00249100c035461035025805110026911080390b002c01075004000a681024580c41422444010b00041600d0482c0808102c100d0000e4482000200c04480c682c070009048003090480ca1401c1c114401040c501440c00c01038025481140ba0780d04650760880d8010042c3d0041e4024052494181032021701020b09405607400784d81445044000040524500002e40341d158580f040241301b5803040c0030451000601c2c05601c1036803090042585070003040000085003000b8004140110140f5208004092510307807080c00da5035107181419501c006503014040e5200d0b56190880716a25802c0c03804101e8442802150000b0000076086040340c2c2c4a001130060713030341148144030a520b4480c40380d541c0e88050b5484a004e00307680c1c4189641d00b0b100382c0000381c0ac081c010382160203a034400c55100403c80d408c0c0e0318490205408a00041c103a509483c01141000c40c0070724842c01040b500310948030f03441501b501c01010003603040e1240700c85900c400d80b0f84007180d41003101048105c5e12070030010355441d04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 371536627 1250 371535377 371535379
    0x190302060a0b04020301050a09051e10031505060a062706090807080f150406090c0b030708060f130b01050f032a0a090e0603100e060a180f080a050c0706030902 70
    0x1400c0001c00700b8107013402180d040b0b410190110300c00ca860030b01050300a180240c110303007000c2c0c0c070800007036407034002c0e107900074000d1903051b07144443c00b8074614003511407210780c4020091060808042000307030303030340c2a00070411600315081105030002d800c001032100c1c1c914400d0704e035051613501d84085005a846020380782a80c0581c0b0445d13842a4582e0360461752814007070f2207501c003507000c0310700c0c1110b40384500d2800307420501c1800c003c00e81c0204c642d20282009c1194121802c003103004070030040020383c4043c41c15000042650440806401d840c042940344440c0e90a481107262982c0032003120f64032580c100e440c00c8040340300303180d240c2c18008145111031300001c0d0010001302c0d07411940103125982200305c420003901341d29845145881c140080c0c64840004203025070600511f1518056850039016078201d101e13400d005481107113401d4005a08a614500805000c030680c042c111000030b090324502420241c00ca40740a448a0707d02408942a01c20071458907040e01402c800002c3d00c1340c05422090103184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 371537877 1250 371536627 371536631
    0x8010506130203040507121407180506120d11030405060f0d0e030f0702090a020409021201051c0804140604150905040507080606030a1d01020c0f062d09190302060a 72
    0x604107011002c1c1c0c0415034000d00690462030f13080000160036101188040e2050340070388a0940140521414959103034041c1c80312205c0c200d110700918503184035541d44844103da000b100010041c010f80d0343e4010300307a0074800f4400c1544074440d80c490100700b920300404c0014560b50f1743c1c0c00ea4480401064214942d0620b00030b041c5045812401e10220070b9079000120500e40030304004050b000c00c8140c00010308103040303031a0b00700004194691180020f00300120444a00c0541d94500010b00c0403049a204038408004000709101c000102140b003101c04495502228085001a0800240d20b070f03c0755901c2082c4054000f5000d10140750000444000c64008803002c11099464800958040c9011101c841e80704d4400c100048800399568481d02c04d8000c2800061031078521503e1103400c81e80450452106c55100c0204030b481e000c81041050703802f00035040100602c8403140d20080b201d82517420b8080102103520000355080e0401c005111640c9041084040c2004e0b8500f00651190825651540203074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 371539127 1250 371537877 371537899
    0x90807020f04061a0c120c0604030f030908030a021306030c020d121b020a0303050615070201050d0b040f0204080601090b0109060c05100204030c05031e0c04090303090b07081e01050108161808010506 87
    0xc2c1086c043e200b407403800300d001c3d0085564950f011105000c0c0c0e421518149075540d100c01d4089805c600203140320304000540142e680455a11075440b200030b03940660b0406003800180f40c80140c1c085800048034045040000c1494128505a4040d02c1808880c142140042c4004440d10391b0020f51902100c0c00707a102000951a10760600541852802010f6645401040444010352086c00200110190200c1c0041c00c1040380c00042c003a60300148a01011329004202444a010140000d13401007020300e2040003440c0c00b08002074001c0804c0e214880078400c81d890101d050090510002d0944c104a000031995030303481e803500021301e546a0103002c0c040e01c1a103000b05004404015500c1c0703860801c42c001c00040042404100140c1503210044007003640340c240754400201e501008600076011516150354901d00107051058109551281601c9035071400c004000300d0340c1141c42c3e03541000c50011040b1121145000c1a0b51101e00340d400c0c51040e200c000000201500c06500142c01048201c0300700b1050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 371540377 1250 371539127 371539153
    0x30105090d12050603062706091b04090c05060307090b0d050117031227150702210f071703040b1503010e060a091b121104090807020f04061a0c 63
    0x3c1da4110340540d00340c1d2054001c900300c000d070307a041c030710303550404989142e502c090700d00384503082000c01e4523250000d900000b400c0400c80b42040c40c2811301d520645d000c1024036065110740d010b607400c82c0704072401048008041200588074806020207041039945c8259980440d4203101e0043c00300740320b1032003030369650045109003d001000b21a1404d440c045441c0f0b40c0d40700e110503010303a000140651480c909190080c065500c00900104147c0c034211031803400249001440a4203013440308690107141045810654418003245007510b068a81203007005480e541240741040e8000c1400e200d801e1000300200811042220300207d203032240303800c50304290318014108245401d80d00520114641a000f141c00a40700869642c024140c1c00d004600800d0705100b1440f00d201c55a150380c101048000510307001c842400b00306610002c04400c00d0300c0402c007008458842e500d0038000c0301c000034420941d40340b8005c066912908810301905800f44440e4080032f0410102c006540000101c040e40d0045240440350 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 371541627 1250 371540377 371540381
    0x5060c01240824060927010f050a0c0f0c0f02130209030f0f15090c121c05090607121e0507050c030706020a08030c0409050a06260c01110c030105090d12 67
    0x395148050003c1e207a9201d0100708010b104000748040f03505181000280581c0a01258000941c036286000180b2441060800416100010f2202c80201d04007603610040c41e6002d80ca101c80b40130b00780b60080786600c05203022004e51052501c040d40c09010411150081c110766401881ca54204804480c608101e20207425150700320501c00c0305454004035544482600311103443c079405038070007040c3c814001081d0000340c0700e042c541c8081c8010707501c4644400e20082c641f0580644803411800c0290502c4040c200040d42c5100d03080008020440440c4410141030080301031008940008000001c040c294180080664210501c1910503100d1030b0301c102050306010900c80240c0c1c0103a4064004100c2075110343c10f035540007503c04030382d0408c00c2000042041c154401c550103184081408200c0c503103858011144544142e1145038282900d41240c800100e002440c40080002070801e03140703620800351018100402c9203100e5805500f80340170440102c0780420305e1040c00d841510780302d02092000280100f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 371542877 1250 371541627 371541673
    0xc03030b040204170c030721060204030f120216030b0a0c030b040c020d020d03140403030e0307081303020a0e1603050a1103040602040e130c0302010c0602161103060c1305060c012408 80
    0x1c109813950880551101c0603503140c0c2c05d002d00270300e0094a0681c0c3d03903076050a1041400801e81c1d50310500d0500d90000740d4148040c0b4040703001429003900103411a260398441440c080c0031600d80d25a10350103405500d000f40c2254406180040013000705d1724807440017030f46030f94040c084607006000c0c903021000c2c6075010b88292440310310f040c010604550388580d41a0014054005007130030130300c0140400700005100d03500500310000c0c10b0200d03180441c5144140900401c190300000620035240040004081221181c0c0300130410724034001c501d80d2074684c0307440300810300002804a074003400005c003c01c2c0000c0d9001042115410100e04d2016600c00501c4405242040e000402020000740104090361144031203640e000d0007040c006103030a81040031500101d00000301151030319601d041c035040c02d01c0c00740102a4000110f00d1054a400c0800840b19104002030040912480010601b041040c00951100f078100311104c55850043c000614103116244079849601d41c5071040c44144d41030407041d0a40b0031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 371544127 1250 371542877 371542889
    0x51605040e1b06040f0305030c0d05091e0a1206150501090302031504170307020d110115050105280203040311010509010807030207061e0213240c03030b040204170c0307 74
    0x218181100c2e6058085030700e810790050740c0c07012080c8408103140001d43c40f03010043d40f01e00002d40d5161030305080181442d48001d20310040c03040903c813103000c82d114400412404490581800d12040038280010300010441e000380300300000541d035500c10400c0c50b070f0007100e45180641c1e4814903070381c0d40c000440322084540002034140e00300304004004030414014040e0072612828a254281101c0d04001d0201d40007100d085006901071080710a4858101508800c0000c22000134041150300800c40300002d802842040d040040020740305000750682c00c00f000e140560491b91200000442e90004e540b50418001a60305046c0760108804a40c018000c5601384030b410303154144c5036035840b5820f40007500550030a8a04a8441034240420f070100c11101b440c14002010058403610b04a101c0003503502c0c81c1e00003481d40c06d5400c00c1e10b90304209030042200640018a0841030704035071032034224058912032084d00d03005400800d0208202841b0115190744d6002c40c0201d528072501e40c010503642c3c2146100709 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 371545377 1250 371544127 371544133
    0x1090b0c0a2004090606141e060a020a020301020703020706110105011a030603030c010606081f08120f130e07120c0c030f14030a14010e2809050a051605040e 69
    0x200066115242c000c542089469a5030380c0403056003c2070a0b5051100d0440b01d840c3c0d219028481519200804403416100381c13401b42c00080034005200c1c110000d042c07068483ca40100b201c440192081111150f490360140095489400d9480d010390340e00018060100450940c0e0200004041c0500c01c1c58100c03280141f00d5180355426110f01a4164006080075406d40010003450705024000d004180c000d0055a4541400f403070100002d101d15410f15800004454a01c981000b5070f94002510f411141850340d2025559114089200c000e8401d60007080c4601620410006e10060740c0a0f0191042003282c4030500100200e012807422100105111004144501c05100201c1c1c446c0e08a500c0c0c0180c0303401e20481021040200c5074164000b1104140507689456510210940c00006640189035142c0301a000d818490700030b480901400c0300c0c2d09200c00d00540300d1042141a81c200341241074106003580ca5440e0340c5c0c14510f4440030a00c0590001c103050751000211414644580e64007440d0340000703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 371546627 1250 371545377 371545393
    0x140603030a0e0114071202150705040b0d0b040603140c0f0f221e020403061104080307060e031603020d080f15060d02090301020a120b01031a0d030215070e01090b0c 72
    0x5688040254800c1e01c0b1481c000d101040000b075070300074846d00d211403d4005280ca480030412400b10508014002c804019045c04100000301840c03080d00c1805100c81000701d141c0d80040c02140040895500c080c00d1101041e41c182601c04010070003203d9990700365000c41010500005004660742c2d503901403900100300703965a040d401c03504000d080140c00c840c100800d003047c81c0410320455a1065400c4822aa4000380400c00c020061041c03e5561a099494070306007454030304030b55100d0054410181c00c581e26004000584981802103603c405010000a141c80d0400e0800a60f42d91180c0e8032840455003010214010741c00003000d86d0f115200004100031000845000d100140d0001d145c40d19035542c003400702e1515542c0a0020b0524803240ba9124060898800c42800035141c284e01c0c0641454a003c080424120003014900400d407401e583d841507006591900300c3c0740001040c03101c0c103064800c80034022000e610100b5944981000d98506105584070103000d02a441810f03102000e941c41221 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 371547877 1250 371546627 371546629
    0x1060915050306030c06211602071211030102030c090103050a05100618081c02100c02060c18030706091e0b030f1b0f041502030c0c0405090c1201140603030a0e 70
    0x155440100074060311450800040030440360b40040c0d007a4030721f080508034254100311000e0803080d0b020390366901450b00405200340c040d44502e5113016040399000340f540004103101c800300740303520032a4001c0d00840d0b413860702c070304490090780001106500107428070000c620000500d0140078007d01070955602e80c52441c0804c01d5030403454401d907810742c104a40348005002e500512441c1c0d1008a00140c500c124090442d0003400d002c02c1019030282e052a211780b403000a540001c07030070303031090003c01d003140d4550810403440d00b8280521461903062040c542d0204070f0316406030f0400d04403080345c2d8500d8111414012020f620703030072078068158142030920000d25035660031840740c0d030011040341146c02d0907544609020481e42c442214072403079880004082107041c01500001d1800400c51000e1800c0c9003540f05501c1c1c50704030b4450228407441d1075202080451009001ca080c20301350080003400110355490b005d0340a0602c001005910b280e02e580014a9410007008035030011155070f07180300034004488 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 371549127 1250 371547877 371547887
    0x52506031a041a04021303061d0d0e01120213030618020906130608071e05010306080607110f190209060a030b19021b06060f01050903152505030f01060915 68
    0x9510b440414040c0e5003c98854a840c401007858004400005080504508200080e1203400c2c810301710360350200d100640640c402003554203088500e031034840710b840c22810049800d000e20700f0640040360300c001039160305040d8180b50041180d12403071052081209201304c1c1640c0b400b03c07600181d040301413080026030b07038a0810440d00e140301c0714090001d403190b15480390510f0180183c1095200e00000c40e0f180500c01e00030070300903000b01402d10301404624288040340d40c07a4140034000d8818004c00c030440b000d001c07909200b81c030715040e4204220f445007443d100e4100340314005107100780c0c0240b50f00404034030103042603e061000d4942000701c040881d02c40400082070b5205101c0464502a0700b4050000345090b4100d8019800ca0302d600280f50074144070003080340307040540c021581031103c02c1100e42415140425941c0a8251100c001101d5030760709075072085802100360200c1c901d0110003101c1d040385504040a10300a40700308071880c111b0380c0c907620706071900b040c82e00440d9441183c001c006c450492180e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 371550377 1250 371549127 371549141
    0x20a050f0903070306111803161211030d200606010f0f05070816050c09160f02070308030a0c1205060d0b090c0d060c1211090f060403052506031a04 65
    0x5401c0300c3e00300703542c1e868201c2107030850030b0f0f5900004000690450321030024000b01c503c010007180640540200c16a0160002c0b02c2ea1203140071152104c41000c05010141ea000700403080c01409440005018480003082d00c10301000514003081580700840c604034000802500c210410b840704d8113411250130068580f04645c001040800404122240018654401424030ba07906000c0c100405007191034070a04150310342c48418016520f807400c01c60500e075800b41c0c00351000c0003170800ca9214400083c00320304102d0313140c01c007a2219400005001c107400b402d502042d403129060ba5a10b81c00c82c1200f00c000203071801070b10001d91011030301070960085038000100d0307900031408030100c03031f09284c5181c0842d114200c00d240559800e17654501d024990382d004620071811610340c2204100c43c0e6240b500d181020300403001000d0203001003a0300740d103a0382c40350b4084901858010f002c6581240202d01d80c812003011541e101c50140058070340c001502802801071400d184004400c1c400c1110180301880010114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 371551627 1250 371550377 371550379
    0x130b030607110304080d0207060915020703020f03031b0606091315050703020d0c1e050f030f0402150c010203040203070f03051b010e040903050904060e0408030a020a021002041710020a050f09 84
    0x200b0480085c2d0214104038808000204d50054480649000d1001e0019491030344506102c50700303000c400c1501c0d41e0114046050780e604449040c081c5e82c0c01d00210345140502e420300c0c0820000f4034002c81c1c10301b400041d01d9100b0314084a0840d5103035a1404843c144800c4440014501ca094120030941080a0740186501140d1031400505140d06909003600346c885c0f1030501c00110b400b20b03000062a0705000b45034000c0d9201402d00d1032810000c40b0314202a41300052070000c80c1c2c0c0482002c54215902c012006400e200a491070030344a6140a55460003036109882c102d00c0b0b40708a0304001b880b030700b1500c83c00040b26000405007041d4116020401c001a4041064034108031a500205015548902ca5003507064001c1c1d540f1a211800e5000303000460351140c03c5419205491810000041d1945086a034051603209001d81c50305081d1609a2030102d0078402002000e00115000c9400703c22901e80300303844040c02049804004119030018102c0c8034900c0000e00280040040c510480b168800411203130390 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 371552877 1250 371551627 371551633
    0x15010306020a1e080f1005010f030207020f090c300a0e1513050c09010b2508040e07030506040c050415180b0415090510030506042405130b03060711 65
    0xd4081d210100b403043e00c1c501040b02c00e01440300704800080015403001d01c1c100403240b01d50801c80040d000c140c03900000001c068000030f400303045448407802941042c1c0b01428072130307881c10a00c2c130b840c480e50000b02d1192070305030301e018049209000006060468030400008801d0645810000340060036655070100000c3c40b90b90700011060710100103152150745049d410044580c43c51428608200c400b8102034412000d40b00140000d1000c1c4040f82c128961154821421010b2a05601000d8842d9100509282c0001c02d0010b14020013011941c46280f8684d0704022650b916000c0000301e07003890807810000765080c0002d10240c41d51190542036411603040c0b24525401030111021008a150000416007a01007030800c07418400031503150200086003000801d443c00d00b0b01242c483c8028a145a00305030710f60000ca0015100d83d400100c5a0000000301c04e10505003186011500f04180301d12801094892884e42c00912280700e46d080c00350008001c1c0c46503072a4480206c40e100007102d04032a10740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 371554127 1250 371552877 371552897
    0x302040509010909050f0706051c11030c070302071206060f081f0f0608100c090e01150f09050d06050103050601050105250512040306090b010e09031b010b0d030c1415010306020a 78
    0x4404001f14801451039030b0712980c1d90511429502105041030260031021410301d140504110703244005e03264040c400348045526540203040032846d000c200ea1010304d5800010b2074140901840b034108030191025003007c1d0041799070340d680c010303940c040c500c100081800e03280120b4180ba4506d034001400c2c114039a034000c2410340c1c072900003034201202d00b1901d41007942d98440c0300c00c10a41104141c40105103003040725940d5850a46442e4040131000b02003010041214401e001c114040c4074000040c2501130000a104000c81c50300d03c0003442c003030000b51442d02c281307400010f0369032140c2d08480722045852104103180030001103d003801a040c080480c3c0c54055420405c00d5130560601500066002d200c002c580e150150601502142c41130b000240401c0b143c508024203030000104460f800700010492440122017206564010720b020f40b003250b401140c000d000424545c0c4900c000034070b1070080c3c1d182034043c003041d00b420755107420320010a141c14900500420100300d5075405005060a01d04111202e4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 371555377 1250 371554127 371554153
    0x19030b150a120609020c06071b140d09080f1002070503070b041a0601050702010801140a03020907020d090801060e04020108070c080d020307080907050f0607020d0b0106020d0f030204050901090905 86
    0x2a08001c54100020300100d80c00300542a490103450001c0c10581000c40c904070b01105800d0702c94200610140c14800c502c040805003a0038810525680e43e00401003528000d50006220b4030361425083c500002100c041c03011030106400b056103c2003400c8032000f88011074411b4119006500a11016569808140000c20103d5641c00801c0c0c4510302c6203103550220804a840e03080e04800140102d030420100344100702c0181d030418244d5040d1356091002c60164042a07001440c241403a4200a402884036000e01415036000155400100282d40714085c5107601c0e540020300700c450910850002e0010386021030055401007119075081545c91130300e4151403809840f0604280e100141102d1142d50002c20005c9282c0d1050045802c00c00c0c00024008485c58440006e40ba80000101c10b40304160008081c4115541c5002c032180d41e030f0707015004104a603580c160194446900703180300c20105000c0150914134520038070843c1d040d1000285044016400e280035500106800b1a01b144c151050100140c14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 371556627 1250 371555377 371555419
    0x5061611090103030e01090605030601050409020306040e100b0102012703030e070f0e01060e010c0c03080a050d140108070807150309030509060706050105041d0a060e07120f061119030b 81
    0x20f50f009499219001e9407180c001091a81c9507403240d410032105000b400310036a400002c4800300d038010940980c50340c6402002030003c00071801c828031075204003154800380c0c440982142c000e41900340c00810110106d4008182800401d4020001040000000340e00180c02a40004c010040075403c8401d03003620340300c8004502d201c9802480081421100402c101940449418400d600078600200144420b40c0c500d6618a5180001030000c0300105489400a1082040d582c1d002c00058003844182c84010503071341844000c2c09901003a0064003c045036006001510300c0132101180302c56010603018580c100c004020342a000c6040050800c042015903030358001802d0018040d480005103549444100012214031b00221407443c541800401c440c43c5012440004290b0044004607500c5012000c01c7e041c02440c3d0041e43d60040c03007005ca001400b02c0d2460388400306200e024200520000504031483c1c500550800c81c003a1200d00d0701d64400d4a209402141c0580d134007902c50300007001804140c00b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 371557877 1250 371556627 371556629
    0x810051b0d09060b061801081b1204150504020603070c021306140f040608030f07140303070903140109020a060f1101050a091b0305060f180303010303031b0207050616110901 76
    0x30035101c1d4400424444940314480130b41c402102c0c02c52a1030140484951184520400f840c113115188001914000c03d200d0b036200c41e8110308500503600d681080c0b50f001c4c14102074500b69611401c200ca050283e00302e500c209130217180c004046038110345e5001c0084803c250145412608082510144200842c103401900082d000c815000c180c01c03142401448000035a48a03d144201d003000c3c4100032009021040380c0f8030b030440ea0106036607105103017400c960240c00b08a440301c843c40000204031003164401c0810701a2403180c10800391103d032010400e400d07625040e90280d400b02203d4001c00c4024060203554070f0702819420100c5084e5000c002c054211760f02224100c041d141c86030107503010800b0104a19098a103103010001805007151161607952000405c0940c3d62020440410300803150b0500c0e002c801841e640c1241e60300c1d0385078507004002d0030042c5d8040d0030703486400c41581e0b9000e001040b007400341c82010b06414240710f500e43c2d54284850b078560040d07035070444485d40d00c82c894a83c024458 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 371559127 1250 371557877 371557897
    0xf1211060703020301150906051b160e01032a06050d09150b0a0906030b0f060607053a0f05030c0c0105010f06021c021b0f100e1003060810051b 63
    0x1610ba61600c095190b8060fa0008006d040080900c402d100b0160090f040c2c0d85071019030a140000003040c41c0c2c055103807410904000640080440c40010400d10070514a030581e403241d407a05100e0300f60000503801c112100d00c2201441e009040051013100d2044c4090103c600c040040412407001c583c80d516001c11490000015050302c543c1c004c69141040a084001811f0010301004003e00d1a1500c9603126000b9285170540b4010700045082a916002910040c0d0707001010f0383e5001800c004400640c4503441c0c1c5010b4451407200320350400300b80d6001c6094024816441c2d9007480c801c4442c00312010f5000a105100914081c00001c152038024401d80c0e0103040300295141c01103007800030180c540a03101700560100301c44255480041a80440c140100c075001d09125002034050000080701c0f0000b4502654010300a41003208846510882401c5400c2d020b55000030320301c00d0040120300b5680c5501600d14154010216418003210641c4840da001c040c0c03215140c69515800b20020707296210075081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 371560377 1250 371559127 371559131
    0xc02040207050f0d0e0604090507050c0d08090c0607080706110c010914250e191a0a0b130303050c120c1509011b0c110a0609030308060603040f1211060703 68
    0x110040d0f8030811183c8400e6080382400c2c464820850f0019000d4403550050005003621440401c0030b460081050701e854100c50000c2d50f4181c00126402032117501c084940c100a4400c03c0c1c00701040d410075004070740c10356402803001d9180c044103481c0e01001d0700c0d030504a00c00355001082903480503e0280b203140255031181d100611100081c12566150100c40b0501c00e0345003030049242c1058000d0a150781c021203010071000203a65540c5406000b01040720100503508504082014003242800d000b4500440000c903462030a540d02c4001c0003002e030141e44043d0a80e42403001c3d043c80805d0003007001d820952282c00490351a00702c18810900d55030480c026140d0030349d01c030074440b034103640210305000d40c09480c040082106c802c1480c0c40400000d030314030b00181441100c810140034401c0c4010868001040a00000516580c0d0f01e002030404407644401d40008001d6000b0811924206044038002c2d9040350340c100040d4034030385810748059425420041840500100380c039294905012052050382c06442c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 371561627 1250 371560377 371560393
    0xe010302090f13051002120105040e06060d06090609030c051c0219050313030f020a0e06030d1412160f0503011401110708010f060906050d03020a0b220803011502060c0d0b010c0204020705 82
    0x505210f0060304840e10650415400c01001c010013300c03254058000ca5981d0914003607400c104004107072200014002c94280f200701d10925402c8000000c046105008641403c0c03440d04185801c000c66501c4c2ca00107801403018038070120241d8908172105406801940d207403c500105030180c080d0307154405c07a80c0d414003141200035841c00141d030344000c00280b8080c50240c608200040d450b0701c507840c03140d4140b04a8465050030080c100d0156894195031103041032250625440a080304101c0e1070040000507001d01c40c000e04e852282e01607d04968010043c400320301c070014010740c1c182d0041800c00d5520310401800154236042401245070409000c58002502410102c0c488e01392419a08a030b4004c2400e40b0031000000d90010703002c1105600803603c42c105869a00f0a0001507041d0742a05c14035540745040e00080c081c0e22001103040740e107842c042a1303001049032020b07600d4074400c442450350280c0c14450707070800401c50340040070000b0051500ca102d0044a60010b001ca13006014261941c1d842a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 371562877 1250 371561627 371561647
    0x50613060e010203040b0909100801050f0f150a0e0406140a0b01090504110915040f06031a0a031214091215070e06041206060329010e010302090f13051002 68
    0x40701040040007071025618007030038801d8280d03051207074001c03044c0641e01c2d807000640c48130714801800014056240003407180d03083c0001c60954500d8151012814940e110b00410070200c0d00081c0007801202c0500580c1950740340c01c00d0102415002042900c01c00e840d41041d0b0100d004411443d481211600c100041c1510350354001001040b036a00041d01a03031505180240c0d07500a41e040e01c40030034044420340c0c0007114000710750805020b6a40000d04800c403001000c6401d1380c00d038011080140c00d42100c103014510b00c004005101180c0e10025004080741d15000403100e10403000b244c503054100354140c3c540034131140811040400307d81c24204581240100c13003109403d0503246900a4041c1c1b5051001c04404030014140e0b210714450700c603003c20382000d10b40800010f504841d0045410190b0903941c1d0f020002c0c02d40607412420728008002c3d1041002140c5940051402c50589401400e44042907807100001a0b408802410401541c0c028001210004400300500d007503420b52043c0c0580c5995120f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 371564127 1250 371562877 371562887
    0x5030a02070609051806090a0f020c01020d0b04050714071e0f0201080f0702330c0310080105090a060f0e070b0423030a03080c0d05090a210c030e03030405061306 71
    0x1c2c2015108140d015100c541c05d02e45e020615401c400708562001c01c54454402c40d00003000840c05c6030784501d0000c62110401310b010342c094a42d00c02d00f20014024001680708001c100c0b1401c64068002c5440e41121401102001018203901c92250146680020070f50805400140b540c034412100c004541181c0d00455900040240e0840500315901d20942011100a504e907690074070341400802c1c08074004c1c00c000e00c0c54060030401c20b841044100300c0c1d080040810f1000d40c02104d99800303807802c1001c0010720440510403e8440c10400c005440780c120380e0341c1c2e0780c0080c0c00d960740202c450b00d40701d0049201c02d183c144030720401442603004c0655928a0b0542100b400304421a074170300301ca8503419804505803408691182c5031513262070104525a1804c944401034022410783c1500710f4038000402012a030001004460030303004482500a0a401700e43d1703960a030b0220090f08000404018840000a00402d00003c035200f0013070680782017588440c08203d0680108130b050400c0065807000f00009a046 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 371565377 1250 371564127 371564129
    0xa11030c0618070306061e05092806091b0e01020a0b0112060e0d0f020c060a0516150e2b050f09010c080a0518040510140d05030a02070609 61
    0x10195050040690300562181030040c11040c82c200140604622564140074060107142d200a0030411709403a40082d80300d4424200302d1041c3e04010b00780103d06850500b94040c410095425140101d080c045100480009881c0e2080000307603c0d0301c0c0104d084403550051001592448100140801d20b1400081ca052003401005065411032900c04020440088155054030381448141c14103490a252200081140500109041c0182ea0501c45e203e5400300c0d41c000c4400c01a0301312115212403c081020502c51498189d0214804000c401c4134800400b4400344072038046d1a01803035100082c07100c602650701140c0e1440c0c00c1e07080210382c07084041c83c41003005005000114200c8512003080c1c0042e22521175031018001514022075000342d140c2c810800510501d42c080c1181d611032041070f03070180a503007001442800700c011031008a4140e0400d4828907100380341c0042a000c400d480d0400f250480174503202c13020303007104900c20b04401060040001705800780c46036000702403007890183c00401072101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 371566627 1250 371565377 371565407
    0x2130b0a09050631080a0b070206010b0f0706231302130203040803060d170d05010e090c0a0b0c150411090702120d0e030910031a010e0d062409020a 65
    0xc4c0036041120120074036104070380800c071404502403480b410718041009825800003910b403142d07030304840800c442c8000d8680601a075408446282e6204c280100031805140f1110340c081c0000c0c01700c080851800c5e08104449c40842031500320b541e00240d1151a000e904658402580415100302c00441c1081d5480c0c10b00d50700e20410450035418540c2d50f02100c0e100c041e0286106603c2d001803181442041c10001d0032401c0b144084075503a010100906010b810309104442000a55a0014800c820045200c120070003005007082c1d849420018404d10541100300000305500c15003101b20000f803080d004c0030780294003810007140e050580c4020880e211100a212400b10f403c0307021122181d0100c4001e65118219080010503d10007090189185000d0075030300c070354008041900102c0c0203415038041e259803410f031511010b16000c0f900040d9103600100782082c0e000503807078844c080403944682c081c04501180e5102400c3c08104c00600421050b100d4004955080d030004500c042c0c00e42040b44084a090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 371567877 1250 371566627 371566639
    0x6340807110307150504021f0c021305100608150303040b0d061a070821130605180a06110f040b0c0d090b07030c0302030d0e0a050708070e070e0402130b0a0905 70
    0x400d5803403030303e1400700c13150740c1e9a080e03100c5011508560b68011840c04101c282c001030b5008107603452008200144400d401da000d00403c0034000900e4040c2d00559120700c00e1807585240710391030020201d803144002002a011384004542504150ba07091004100400c5100d940300d84500203200100101c60040e1b12400141a2905c10700c0000c0b0201b000750b6104903004102c0c0e607100c08810446524100494644c40e078030032080b00070842044a58600c0d40c000c0c2c4c2c09840100311941d280040d101601c0311181b8039210310350040f0140d00c0026103c0d003090b00c01b103007004071040c10480c1e00d00880142d0340042d0003600c0f02e54004581c00e09044400c0008400c041c6082c90a80b60f0b451030203000200500c110f60019040080c10500a030625008004507111111025420010715181c210556100c00190008a660780a909400981104009481005c0d288000b41e902c1e100d460742c0d80c05aa01c0755017004540e030082c0d02403100e098a41c84042d41c00c4010710f07880a9866454000c20b070000c112401941082e40300d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 371569127 1250 371567877 371567887
    0xc030b0a0303030218060304150e060606250807080d1103071704020d1e02010201061e0510020f03030f0610030603110409030302041205030a0818063408071103 70
    0x168584000c00c08403a01401c1c0140d0f0b03196030390740702c00c4114045820a5004030b0000103010800c01c803550307d180c0b00c441c001010401e03401568203098480c10300341d035406d50188090001c1071044441c20448204400b004010710308040480c0d403080c8082d04100b0054a06580110b02d54154041a00546a250000c0300700c43c0e10354a0001d0000d01a495607070b41800050119100080442d203a249034045002e8108000f00c1028600151002740400d442908078010350901c00f00060307114030790805804540c0c80c810900400e904150074411001c0090070140218030554400e030042c1303642400258091020341e0070140b810714000c000e208014910900301c0b03082519150041021500d9034002ca41004070450700400e401841d03043c200d02a000b1a000030b9811181114131a007080f0b8000000c0180084548800135240d480c81440d01c0c500b804003040c98860340000f8001051024000400d0702181a40c403590075002030002008503281c9400018000070032041c0f4103201d6025008411103414081d0980198980 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 371570377 1250 371569127 371569129
    0x60f08030702280306050a0b130209040f020304260d11030403140304050717070512060f0609090c0f040912020f19050309150f12010302010e0a0803070f030306080109050606040c030b 80
    0xc900b070341c800034200c06da441012131180405a044020828001400c4941c44030000c440e04c0c0007541700702d0039248a107203003100f0032809074200c1c0280d91007541c000c0b04907071042024116400030980c10720904411888100a440055442881004c1103018649506a104e00c0c0034034000d031060700d0940f1044503040060042100062000a0800907501c0600c07041460b1100e0104903441d00c40150809640922000304038070002100050b1a481128500c0c603010031621500300340108004151007c0040e60800c1e4480400c41c2018249a40a03500107000054684e503180c5818200c1d0300158111001030300000504d001c4e4400800840381c848015040044174040c00c2d40e5595900e00c201c40d002da02401480c0b07203e10307010b41024141c5140c0ca12011982c0e5480b02c1d2581d20071040e49003400100d02086400c2107071031071810034909501c20b4600d0034000b98a000c0c001c0e147d01a107102500b40c00c50030541c40300c0300402c41007021701829803020301c100c0042c0f101c1c1c1044001c0009858cd4240003208140c540b04c00a286 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 371571627 1250 371570377 371570449
    0x204050703060b2a03040e0406110304050712021507060f0501050301022d130b1b0705010c060504140f0a11030a02010806010c03090e0112051c0e01030f060f08030702 73
    0x2040c0e82461580d101381c651556a8076540404000c2e002180c0030114000400004e48016a031280d0700c140e0003009180c20008d80194640001d440c0070b01581d2043d0003e0084058801c103000c5a1400103249036400a0340030900100ca41c401e000c110b6192f921469140980c500c00e00555004d40b100314025824140f400d812142a83d09555003620101c0d04664400758075040e903c00c484820f90b0054080691540b15620900c07954003000603054200d1a1041d60107008402049440c280d9005175a0500607100e507882d13035005000c025009907581c5115004218210b4400c202007910003c001028040d00c0f940c07400d2002e140400c4210310360182d000b4040d4000140e0740000400c7d40300c4003d0074500c88096450804641050745500031000f031792201c00c004500c4000c01402200c040340310304222101007100c91081100c807914004260041601d61042041e11341c0207070814401002c2208000072002c1c2e0b1030a0326410402c203a070005020f030f0000200750095080c0f42034030741d00f81c241101c0c0c81c3c00001104144400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 371572877 1250 371571627 371571637
    0xe010906080606093601090501060f1202220b100206090d090f120f080a03090b010504020a080c0904182603010e0c072108010602162102040908160204050703060b 71
    0x1080c0c43c1e05500407071700c0481c0714401001714150760001c200e210603a203003841c000d10310f5026503011540c040100003004000910b2260055a000d450031045952100b000c400c41600485080d01264035004d081d4030326111f4088100b08a19240c5c010300c0360341018004582054081902c0d9010023025010502451030900310030360486030000f141d4443c513a21030608884509409500808031103001070803803001d50b41270b085081294060107000140d80d030307103a040102b2445441d80d08004540081c0004080c4481103000d00244030020b0004074224802692608407114006022100c0440d8600301c040f9100700803280705850081c0e00c84071883c5505050b84454484001401140c8115000400b00c0802400e64159230030201441c109024030b102c02c50003e00506000d006080043c411400d69099405400c10700074100e0f0940c02040036491508500001da1182c070507010f0ba00702c3c0e1240e00007400294004010f21514054190300324907403a40380b04200603250b01401480401d0306001d030030f1002150410031a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 371574127 1250 371572877 371572921
    0x30c0c08090904060209090c03060405070e01020c0904230618030f030a0506062a010b010f1b0807140f010b03150705030402130216020f0409081c060e01090608060609 73
    0x700b5980c2e00e02d8210041c1c0300e50500c003034001c0046014812072070001030141d4011601140c0074412962404012140c2425122010340180d02c108591705035400c3c812901c54116002c1d05100e00031000da40501d20864006454141b500d912280421969002000d03180ea001450716001e14038144a0600c58440c6000142035103880d2a600d030089000342d5030380700458102d2501d1283d1406202c4e00c02d07004d5440b0080154200d100c5500f0b01040d1600d0350f01c1549081c0d403030b40300c50b01d07842d101c8650001c002541c0b0389a80e201302e51402080103924081040a5003404005001e1002401602d4034416500d003550326050140707000b81d00138020300c000054082d020380d501c04424582251a9511030001038131050f01c0110480805100143c013207a24030400d4400000c21b80203807810543e03d80d40505100071a500e85002425819003031201c5000011031740104200503540325004560203488808010320540c2c01c0c2c0c80800c03010b556081c10085901d043c45400d074014800c450136600d0f072600800c95041401002c84071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 371575377 1250 371574127 371574139
    0x12020d03111615030b040b0a140414090a03020709020a02060703090302031c020a0e0d020906040518010e100c030b090c09040213030b06090609130602031302031903030c0c0809 77
    0xd0600320604000741032004440d400b9481ca15a51101084080e0b095254000c00090038080800030f2401d060003410180e20000e000e6410b00c91900b4468131054140041440d40607880e50b02c2040506890450180124404805861240510300d0003a16200c6640d118011a80c01030140c042c2098012468960107909800c002c61845182e160480c114072600902031050041a114503070900c9065011303000420f0356460769000d5840c1d035020808041c1e4044070003544044010001005420150025504044110304004484000c202000d003501d060fa400c1748200d0340860440c01e150b241c1d03401807039100b0301c1c40e0808000c4030145201144111100510300c040541e00014894a1030300d4550448540ea84000c05081440e512442e0944509409a5010b449004c40f54081107049c58440da45038011280c1000462401c2ca1603a00c000203908002d20402d519000010b81c100543c6040c4020500da1442d124502c0048156142c0076040368550344540701008100b80501c40002c90010454000c2d4038100c0e29 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 371576627 1250 371575377 371575397
    0x601050415090c030b24160204110a021f06140907112508070f0311130e010b041a010905131b0f030608120d020307090504020f040e0112020d03 63
    0x15501402000740e000c2c0c80114641507529807007035813550046003c070342e04a0340704010130b01d80741742ca8240704100003030086540401c020501d42d001d074144590360404c6c07000c2d0000c00c0f603002005414042c2d410845c01040581c0000c3d007502e44485080030b6880c0364800100040203600d007405181c8a0300380462400900501c0000701003052540200e05006648800b903007250014002c1d1640e0455054010405000b000c0c00c6400101d03009501081940c02e992041c10782e00e025030328503210030608003d040f00d580d811600b20080307086460b080d80200780003d01e003000081501401d00c0c013030204944802030004179642000390800000e0381e20201020442c4c0084604880c0d03904c103802c0f50300c01005002c56100044088007491f4a889800c40540b40c4d03000700c0da440c108003455440c14060b49852640303080c1c441040d002c001003040052980c0c00b96811800d18641460aa42c4840108003242d0104030f101e4802207010800700040392810490a0141c80d81484040c01c0c01c501703a002c07a0a09548441c018144030300050703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 371577877 1250 371576627 371576651
    0x1090207171b03192d180e0703020702120a02030c060705100606080f011a040605180a06051b0102161e05060103030f030c020c0d060f090605090601060801080d0206010504 75
    0x11049100e59503000a0b2030b81c03161032041c41940b007010288482c0100383d1582d8480c1e42c130700480900d050000c1e0611031001c5c2c03110244100310394007414403114840305078000c08045401102c1d4031105200702d43d16180103030744545600420040000201d522141070b4800c40060b00162130202d81e0b1004841c041d0340c0e840d1540b4151a010b8107240c2c84800401c8680d16207400050103e42c4490302e54001c4410181c14041c2c0c0c1d03243c43c82e016a503203e00071080700542040000300400d911600040654012104c000e20068980e000083c11180c050352004001a002240c009100c0d01c584004c5900850500002c616142e5410f40354501440c4035000540391034084541a03001181d04100c2881a50740101a030b01c247da100d1a024116104145c02000020b14007003600d0102c2d4000100c141e900440240f500140d0185507840b04050603060311a0f0000755225195280011454001e0724003030898000545890340c1007020003000450305a02c001d02d65030052000d010940e402040e03441c1901e4041d40c0128807140845 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 371579127 1250 371577877 371577907
    0x50705042705031207050403210c051015090b090a0e0106030b1e071718070810060e0604090c0905040804050904050c0901060801060203042303240109020717 69
    0x1c007203002060300304aa00100711010004104201c00d4903200002c07a00c0d0041c04a480d070140d400010310b0000307840c02640c800c0d041407500070a009407520b418200e0202035a1910705010890803940e40d51500c501000010f000a0328010f0060300004204104450401000421741d5002802d40c1c80202d0f034910b011404c510003174100d4405150801c0f025412800c0c20034a12280100180c1c034072400c1c01d03600c00484c550502c035201004007152085034003219500d030300400340d44410703440c01080018801c20000040840e401d100c0f401c4954001c071070010300c913803a00b00750034003600d0018009442a80b6144603400041c1640201005644040e4000a566038482c41c0c9451b640c0300740d401845d80070b06000300300b0003000000a100301ea820f2094030852040c1e641c511041d2402c2000380150300c0503030000d01050003542400214001004c85008100c00b0035290b0002080c102210a007007220b05c00c03011104c2410000c00e03860070328010b0214400c11441c013445a00c07580c9100b103c0f02a80325900174006640e0490703c03910 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 371580377 1250 371579127 371579171
    0x4050d020d14090a0302060309100f0b06030106260709030b0f0c070f080405060d020c010b040b010e0d05070f15020d0c17220b03090708061003060b011403011e1205070504 75
    0xc1e2007e030740d07410034030a080c0c0c0c0c03152480c0c003607022075040000d40c0b02c1d0381d88a0302818450200141c021411030742013402c140c0333907400c400da02e903000a104044050002d01355444154020030460300d031020b2907030841c01d040d0b402500040c110706442080078207024502400a044a540b103400c00d40045180c074039407800400700d100740d0784815030004011a00099030304e5135500a0a41c00340e00d6000b0410080c45070140000d4550110409000c250424124134103030501030001a1440d12540540f0a52b980741e01c04000c01210301c0e0440405103070070002d00b8841c40d4040103004003044590804e00d1203a10301d552a5174510324001225580c0c110041201c0b1050351090140310b54615007026403840c13040d1074911030f41c11070b0412a44108184250389000401c802e011400d54007810002e00c1404da45e42c25519154054144801c1c524100311410351088000304008005d1406045100e6007490325040c2e004001c2040389051b003014450340544886032000800c00502841203034401d40d00413400510364001d8900d40740d26 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 371581627 1250 371580377 371580379
    0x608090708030c060612011415040b18101205030a1805060d0f2904020307020316030804031e0c0b090102160521030f0a1a0a0e04050d020d14090a0302 66
    0x10115143c0301c03005010411038405ca8043c1c0360076040800a0301e80c41e0a0700c40d2820701c207a94030036400228002c10442442d095011038041d101140d82038180d030100d038650443ca0030002d08254007a05210030f1100c0c51014000030500000080340d8002d07140c8031035449128202d400c8061010a04014002e01c12042c000401001c0080440380c864680d01c2b4090042e004844918000d0b07031900c00744802d500e4007980d42c69032a0081007240b150309203a103c103000007548003420323203402d601c4184030103001103032414916001c062099132902e2943c1490702c0c01034940b920752000c00d4880d100d03c0415460040e8402c030301810541d040040540c1030f86031040c540f402031180d0741d204c2e120000c1250060081c00000950382c88822010401c00d804400d601030110b1040c0010b03030b281201403a1040105080d0100782c0c07c03240c0d02c120241080c54001121000080c90410203501c50580c028030401040244082440000d08000090000d40b02034480203800500e041c02800700e00c0307a40d002c041900c800301c0d1070313401740c04000e194 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 371582733 1106 371581627 371581633
    0x8010204151b0f0f050f06010303051801031e140f010305030a180902270306060109060f111b100507020d0305070614181005010806010608090708 64
    0x71024020180c01d0390300302d480c20200f0502d0003607803083e500c41e840f42c8040d070005291517410f040109400e0f0146800110041002c60f0304042111031003d4014541c1003688281001a0010250f41c080700bc500c4060106003001400158051030321505442c140e81103d80e9014103184d0544400d01004040f44c00601465844074011501000007425455a485102d070300ca0300314504a07004095070440b100700500d40381c0423420b5010000d1352400c40036000b510503460484d0010b0074080051090100b04200140d16a100c0781c400e240090078260000309440d6512020300c1d05880102c43d004186104142111100c0303941303800740044032095640a80301d01d500702c441d42c50030b4820750022002680c9147d06c8050f0f80c000340c80c002d13000500c0384480e504032500242c1009080c910f000c05055034514402d26080040c001d14100150710342c111121440d000506544c0d12083e28100030786540901100d00c = true := by decide +kernel

theorem cover : BRFrame.Cov 371402877 371582733 := by
  have h0 := BRFrame.cov_init 371402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 371402877 ≤ n) (h2 : n < 371582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
