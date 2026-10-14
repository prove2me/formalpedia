-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0504
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:09:11.838432+00:00
-- url     : https://prove2.me/submissions/a345c547-6de3-42d5-8c2d-02b8520d52ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 90467626 ≤ n < 90647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 90468876 1250 90467626 90467647
    0x20d12080916060903060e030d0510050f01020622030c0f0b010e010b07030e01030b0112020f030105041d060c030601090305060f010512010209010c06020c0c09040302010f0605010c08032703 83
    0x801070720400307045080311414002e0207070121030941c85100d5540001ea070b42c80d09000160107504460020492502124100700744c207843c641c2036404c1251004001952400300b001681b0308014548104102030000d400c1e2420000610450185501c074180e401890102d4140209031080c01480240d513009080741511003c10b140425440c0b40a02c5400c145c8800b10001040b9481c8240c00c0301d01c42503254581e401c16014400064000d0701c0e0942e025814444030102c0b000841069000904920203a0001e550707907581048108411218860701078000c41e9250078001c2002c500000f646078104c1c4c000c02c1d070544c482d03032210012611004c00d13410050190082d5018450284c0751940c400781a58021a02910350004d904d17082800c038003e240f500c5000603495402c60011400c02e030b0041038059916030540741c3e5868030030045080e0b20810307601200180e544140c410071800716881035402512007440c0a42c0307181d6042d10703101c00d1400060701010742c2001170310100c1401e0f0401c2c03116004070b900700800e5940341c0c4c172543c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 90470126 1250 90468876 90468887
    0x50c10080405210a0e1903081309090507030f08210906070f050901080a09051c1101020702060405040c09030606060203040603061d310b04060c1403070309020d12 71
    0xc07421103552003590f8000c1d031000c2e14655250b4058200c111160705201920004403204d08811007041d4201212001e00503031440044000c0010f5402008081c3d80c500140600c105021160740c0040c081c1445d1104003000200d0106103082160b0301b0456021102c84681004140ca00c540d02c040403001e841c0342e0448804124440e0024414041c02094446507500c181d000d68141080301d8140000410070401d655240d8011409280c0000000740b0001e00604156134003407418911030b11400002e0350402e50007040c00c2d800345084ea01c04e50654000e40c202141d581c00301c2c0040c0568003a940c4036603246e000800c4580d1140401800940d00a072040c000d045c2c4c1c2c3c88010f03449078080c1c01888006410941b0100c3c192454400c0500020000c0314400381c5c0d56101c45074114180d509045050403094800d06221444103080100168280030380d00c9030300785007840e2034650b045441981c00c0c0028403030116a40040c2030054030580703510040b5810045a400805d200003030441a030b03084001c3c42aa40304080f01c10703555021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 90471376 1250 90470126 90470131
    0x504090b071e02032505150f070e010c060209010c020901060e0f060c190c0b0f13080606091909020409060507081305030304170903060405010f06141c050c1008 70
    0x25100e02d1441c040652400c600b12a8000082c8050b0744208802d864036018040b1340f040d010010528140504840c0e0f0302c60342028000e0301492030000b400010312038001000c0100c00d07000741d020705060f03c903448940c002900c0319110f03110240c4055404540d502c0c890340240d038003800c070079402880340000307685440000e0514a52402028000e084414044105d4100f25088615007034000c0003c0072407140b941682032103090100b004461030320b44004005014050740c40500362100000041c9502e4003648112010041816444201658800000e001c07558403410711aa0700054180154000f4000011010f400341c0b00c0030314003d41051400c0e40f2841804820780c0401d001d002184d0341e15080d61a43e081004580c8406007000e416600300308003090004030100e1413042c0881e510726200d414454280002400c200080300d080e40c1d0b5035150b00249214100174462940640002c2d82409039284840c1c0c0400c842e40d0080341c4440d041141c40c46250b0501004105800c40c04000400025464019000c0208455400d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 90472626 1250 90471376 90471391
    0x813060f050f0d0c110a0b0702100501061d0303090307121407030309090b030a020405010602100e06010b0406030f0b190f0602060c0706180506010605071e120503100504090b 76
    0x1440c0305054190312a4084030312414419408506210a104042d0000d081c1d841d202010b0100a407199060300e10140408156030340142d150395180e21300f407000a42407aa0120900c41c00341e1034000140040c540000d03a2540040c81000c1d849002d0005d54042440c61290704542c40e850701c54404002140c0041c1d4100c42200c030303c55144041e09010700200c09580d0000d5000040201e001110240700340d16050380303d00181c00009081710b0310a0110b80200b821100281c01c8400181c01001c0c001180100ea03004803621100000010101907242030700da10341c00d0087d80140c0c001c054540c800c1038880c4000342c120550032440189543d950300508a811001e10400e88940d1161032092080004c5040c00400d070030b4820a0348800c098a421069a03c080c018a030610510303803941d001c0c0114101158003040382c1e501030308442d00c9095454405040c03494200c983c000e030a42c240d020340680040002d50098091039005194203007561251240c8030019500b424036000642c2051500c110343c014045860103490280301d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 90473876 1250 90472626 90472637
    0x2151902010b1002030a0c03030204050402040e0103060e0604050c061e040801090215070b0601051b0d0807021b0310091e060209010f0521060a030b040c03050705090123060403081306 80
    0x100014011540e4007042281c0143e0001e01003409541e0042e912082458420701d0b004bc81c05031600d001504903000f07901303e1664007400000500070410244a4660151403081c0144400c0c540766035001d69844054080d603000740008a603070882c0d0140c19452440b14401c00c0000b9440f1612210f045001b0328550038164850f00004160180c40d0041c001192582c1e5001150745503143d03100f10040d00d25134083c2494024007508074040d026174002c24001d80175001c103079903607202150821040080c900042d0340300c0d40ca4040b00c03000000e0b1742703542e00040030723610340c841e01c04045070300c0e50103040907501c070403241b200340d82c0002020b0242002c001d500d6008241a2100362036000314404074013421201406518154045c190700c80e55107440720303d01070300c0d4150710110082800c15001d031070b981e0b20150450b0945c0c040b1200f181c1c100050080280600c40100505015030380715400d50703d008401c2c0d60307003101c150202441c40c12541c6d08040b6074607410126030145412241003552079008542204030341ca1300b44900f00c0005c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 90475126 1250 90473876 90473891
    0x3050c030d050712050702130c030b0909010b0303030406240f03020901090b010e0f04020d140f070309080d02160c03050f06090123100906180507020607050d090215190201 75
    0x602410a030390f4199007000e0300e50701c4400000d43c10345541d0300540013680d101c02c03201c410098124181c001d40d1480d41b2141d8003c02c1707004511040c06070b218405461030081c0d9050458511040e24000107590b0300070f8111303401140e4051031143e004801d4081914990101030500408a41c00e1401550082181d1098030040c0c0d0740e80c6c0c0e0750256021103a8120120f80020750000900045151001010903500c900500c018601003c1d11000d40440388001c180c241d02c00c26900400040000306072045a1207511030038144000e01059403103820038490314008020043d400700d510103035620f5558181010580c01a0700807042c1d5101e0500c81c0d9500030b03070724900034944582400a020041b06019102e584442e1441d85112130003c0440b00c020f29200600041000d41204030004042119002d0040240074203a1030340003c83d06045801c090751001400101552f01c407009004040c0d51000032550400d541d00c000003143c095601c0090811041520700200c1082c0201d2682c0c1c2c0240f02d00a12510111141c00821645 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 90476376 1250 90475126 90475153
    0x2060a020f060c0406081801060f2303060709031403040b03011214010e070501050c0c090a0903090b160602030403110d02060105030115030803010303030b01091208070b130b010501140c0703050c03 86
    0x62040d07001724000101c607100841c6000345081c100c4050f040c4410004a1616120070050845900752b0740800901c018000c403621403080800c3c4210781c01c14003503010b03180c185040c01e00079101c002e55101c01801056002000104044280280d070081c0031030101003071307807560b5804d401905038144640603208014014451000500305115800c51011210094800c9501e0100152490381252611042601a44074207104503581c45180c43c1c881c0d0280400041c5480e41030070028640a02d035000740340040010881070a00381c1765103014481959104c500543d41b591980350850300101810212885032103020441c6c6496500420f040c4c1c141e5006800030001c0940100401022660358400a06011001c00052001c203220360485420f041c010f05100f200a551000300340300d840030607030064030035003004141a41000401048250400180881000e41030500e81361050046010b00c40c2c54140a60120102c0c0310303000c030b00149d1360240c0540040d00c1c8415a64200162142c81e4005a180310380150314100024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 90477626 1250 90476376 90476401
    0x80703180902090310020306190f0321080112030504030209070c05061e0f0601030e0a05031306050408031b070b0c0601030b0106140307080702031e0d15080a0602070c0302060a020f06 80
    0x38440024002c2520b18a17005a1400a507c00741032560040d03282c2140344042c80140ca03074500100305070764000c0400e03440c40c00d003502d080e64920320030096440c60b0001c010055902c00c4185055407445070080050005a1509852501c0b0f1a07100a42114280007007244094204101c15601c0d0300600548019640780020501c11403403a101e0072110482d0f10000c030741007110414480d0b034055418100096201c150808207841d03d24880e03001c5a076035000081c000110045202284c00900b91400c2403030400c0d00f0810303810f8913801141da803c030315901d000d50a02400c903802c200c118020901a004503540c1d0702896000c0d03841e40b8090005503400011140002203480c49010420040301c103100d03440c1c0c11501c5580c81114541c1c0c001d802e01003144400d019402400340d4448240c08807118403a502a6240070062446080e02c1240200b0101c52425034001c20800b0300108140c0e05e03c550156005980d40d6407454200640b0300f850300b01942084000c205140e403c1c0c0c000030f400300e007201e900d021602c16590b8010f1900e403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 90478876 1250 90477626 90477637
    0xb030d02160608061306180c03050105010503040f0611030108010c082a0f0c1006080f0703022103040f06090e18030a0c020303160318080102070b0609060a03080703180902 75
    0x810381c000920030048544110155900440020030101d84008115518001e5482540080e070607503848070207540070b100301c6d4072501c5082c65607803c0c20300081d071512002030084d000080c0b000d080e000c18264420100100c541c8000c4013280701c40b51003510795840d1410175000b4681017246402142400021641160684628038082c0d03080d41c0101d81d08005106406041c2d4200044e50280d040050003a00040003041c40800a040c02c60300000504901e05402a454250400c14680440e00420010700250700d45c45d01d000c040141280300140b81062000c446031031845541d0040704100700c01c0e01c1c082555a48580041c0842e50054002105078413000c45000c00503044900c40320310780d44100201c802e46070044181e16040c0b80010292030400d0312210941310781950102041740050700c44010007074191000110403010304800e0000310300b071100d07650b1001708200000e004144101103001c0051203c1c0d031140303403190141d51f01210b10b644403802460003602c4000004004800c02c1640b040c041400381c002e01c00e55a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 90480126 1250 90478876 90478903
    0x906031b050901020a08071b14150a0e09010e1510020318130f0f11071109040c05120102120c0705100b04020c011a030c06040f181b02010b030d02 64
    0x100d6009041641c80364004540c0c14150b01a4424910100355000094041c90380241000b04400710300070541001c030401c5d41c1045414580b52441e410a9441d014082003603511414882640d034640380109444030b509002a160b80102d080d000400d110755420195401042040500110398003084200300715100e20110420041e44140f00700e14411000b0507403407500b1600544410616481248841d003515440304000940648403014041e00240510400c11042d03c0e9482c0344d802e0456542d524107500003030501c150302c9058071074045001e10840000610007000014034000c90843c002031103901135044550103244540490b0001100203000c03000700c2d0101a84503005c0c015001c0d002c03407800c004040e0001c0403074000b542401b140084c140c0c240324122102ca00350340521b51000c208010503240c03252043c602c0740901c406100070031803d5508010031080e2144071202358083c4000e8030360359005001c04030703803070742d40d0500f1514281d00141c06620103011000140d0507601c0d01c2c480440160707562103600d820340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 90481376 1250 90480126 90480161
    0x2030303040b1b0d02071202030a050f09180720030a080c0a0c050115050301150803070f060906180b0601021605100903050106090c08130308040b07020f010516090603 73
    0x5000440740e070710303056016154000305040d0502600d44007400b81c02042844604c90b80c0081c150051040700700404001c40500c0c4000c502c3d040c0003d0009046004841011180c220046503440e650f079981d4145204040d030460071481c2610304180020202c6202c141e1600c00c561142d0a03010064030048100d4070144602c2d10380002035124150b00e020320746d100d1103103c0d04126030213900000103a020b006040032283ca00c0400c100c42e40c200f504050846510001604014084000c10810b0b8032010090b03079403140d00a2f031a12074503041401c01402400700444000c01c414a025071054525602098a004050191a284020399074140043e130f591612400c00070402a1751040030030261400d1014401084424070380b0301d1b11f90380d40755141401e50b00b00b07800540d0415240c44200981d594440002e076848090440c3c9210040a60b80380903000b520042c1010b004104001c001501d10b900030840001d00b408440020071040c030344081030250300c001c0c0c03c03c0800010000070000542511178080d00540d220320032401c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 90482626 1250 90481376 90481381
    0x503070f020c0a03030f09050910090c090f0801051501020a0c140d080d1413080307180e04030c020102061303090e2e050a090507050901030e0118030e03010c090302030303 75
    0xd58000e91041010400c501c605842c03140e003500d5981624008501c25141c00340030b0410076401819119840d04224010f024010820205c410860a44000c40724040000a890350104008840003651038000c9800116008000a404101540010700c900039014288400048103401240c036528002c00141003062000400c0c45510380d00d01e070050018000420b8901e031b8207000d50320100d080c3c20544041d00300390365031a5480c4c401c00c090150035511021090840c10000c005664001480c0006002d54041000e11030300d02c26845d5004400394054145000c0ea240103140500e4010016600141d04234010300600d404a001c080844e07504040e650b03416224000f4060500d8400214040002c1c06100e02c081d00b84051003104a0400c03005000c940d00c04540c144c00e40c2088103000d0007203c0c07907001d1000185007400304000c5561000035100d20750024070780030441c00b203403031078a501400113a54880485001c1c44585000c01d40c2200f0700369098102980240407260305008103a992203458800650950402c100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 90483876 1250 90482626 90482641
    0x90a060b0a060c110303091302031e091b040b0a140301060b09030a06021e03100303020601060c030e010309060b0a1d01090c050403031101060807030c03051b100e0f030d052106010503 80
    0x41c0195484c8014086134140302e0350600103103403111044030f92403c03681e0000038442070445940d061035a043c1140c403d1611400c0c20550255107001c1e0703880c004407180c0803d8580100784d5031604400d669000042c0555071041c0c4924100c0211044d04c10203912a40c601782c400a50050328009448501314010060305a004031a00c1da5806075024a10401e95181d1100e41518090f1003e005540100701491000c0034982c154540a460150107070000c40a2100e204042e074000303035100291040ea600c3c00c1ca0041403a003440e14180015140911025074401e5031420301007050f007881c254800340c8025460b1401c03500c4c0d03a509842d4040b030300300e43c03c6e00e40011400c00c0140003082c0208510704900c5201c000001d4440e9031003140034103102e000d40084800c01c4400c4010000d0050800202c003240c1c0d00c840503030b00c96a050a00050b940e1402031815801d11440c21000e113580d81d114500070342104c4004d0142e07034504622080084c850760165003011040196016400a01c502c8a84c105100b85d0068560350714540303e840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 90485126 1250 90483876 90483893
    0xf0b1009060c020402070602030901060f06050c030423090406050a060909020a030803130b010803071a071e030603051b031603050a150b041e0e0d05041703040509090a060b0a060c 78
    0x80b01070780c01c180c003006640700182e510300c000d5200d03078040400001c5260a2000550a0740c065901080070820180403256007032401004460849000b00415404100e825400e0b1304140c8040280c40c0c1d00820700b400b00710a1009a40100348521000c1d03008100c802d844a032003074221143c1c1c0304082d41109800105000043d0f50200443c0c2103010004550308148036a540c40c140142c2c04d800440c1c41d23400225107031040008405002e080002050015803e1f442c241034010328080220b413591030342100c0c0518200303a15009901c00f002841d0000c3c19601c4442c0108000c5151404208903640284210504080d41442080545060302c0d4450043e141504851300c90041c2c000140300450503296680700c111700c181d076561151202000c09a006640990010465002101c0d4412000a1a40c00070031000c0d000c640e010003100c090703446890052950482c0044014954011500b02d03d03046803160302444545c2d40b0010341030381780920581c01401240441c0c0180310101c8224400d0101040030342c1710990000d0680f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 90486376 1250 90485126 90485147
    0x1f0210050a020c0304030c0503010501050a0b090d0201050d0c08010302030c03070602030a030c0509090412030b030303010b1b010b27070e10030e0f0105012d05090601050a17010303030f0b100906 85
    0x214005800c0c49842c0700b9030f9045600a9000b11440c000c01036007002075040a0003410b00412040380c16040306850301001030360b180b1030f04411900c01c00082602d8011a030040b0291014565410020001d01c16205406440c40c0000c1c0020381c4240308807114003070b081c640000c4140c1a02c1c03040c1d002e9814980303100340580142020103494018010140011421503d402040510444c0611281c00d500c41d0707440c034040c0489407204c055a000e40c10400041c4400004802200c000003079000401c10362030007001200d401072400444965001c2c030580f000450184071000c0c0302c040034004d4414443e65031507e403401d50361603024050140d0002104078909c1e00041c0260703c1404d9900a0303c081d5069003924032141400c5038001d82100c0007020ba04410915000e0f0080000074183e0040762480c0005ea0500000550a60000b42414100300c0002a0309048034400d82521000c800302d0503c803070f9a542c4a14015002d8203052540c900803074a8100d1034912840c082d1000304000540da01c41d4090607080840868102004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 90487626 1250 90486376 90486391
    0x6080307050c10170705041e061b0804050301052701090506010501080a021c0c030b010e0d060504020637020d0804081b120904050c030103030e0d060b0306070e1f021005 74
    0x10f84d005401d400000c0040602c1590150b440d20303138650070b20104010302d40c00c0341c14803006440310180500001c0d41144d10010164900009641c0000c6103242c00081d070301c26904401d816500708402c2c0f0140c208800c1c03091243e105110007064003812015080c0b8200e030307480b03540a00580d2119004000c00e5014003002c58001182800240c54444c03c6081c000b050010241a40015645d6151a400d8164184a20041610300340390043d03081c0b00304400501d207281d01c141d02034504d42d034440108003150341c0e00048800c42d105110040034000c002d98650a074070320030302402c000e0340b62260f0f0704503426510114600010380b078107480e41c11403500c403074949032119045461400d580d6080b14009407581d40303041240c103100080c0458110740d030324110020701040d24006010f80c03008040901c014030010385c000109405010065a01040310b0019040440180034080c01c099050b00403078080c8180355a1050307d00d0444c51042d5801808070303074810280e803c00f40314000c0c2880180c00096411000031341680015070003007117 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 90488876 1250 90487626 90487637
    0x1211060406180506070816090b0d0b012006010e0a0b030303040f060e01090503210106120b011b080706060b03160507050f030c060406050a02090607060c020127030306080307050c10 79
    0xc06946440c9020419580c0f040890741d106d0400c02e0078921160705200415080c5480001107142009040b0769001d040c00610030541c0741c2c3c1c407260a6034030854006950400e598400300040001025060311041c00b0b000e054441444c1078000b5400d11494003c20b03590181c050005c40c030f19070f5180c84900103070103400b800300c13015070b141c1200286c04d1009008031043e045c00390010796952442c4424603a81e42001040b998025030807c0010048150030200c045e01031540604003140400080c03004032030440d80c9000b403d40b0342100400c0d4506011501014200c018410b0100b00071680c1c60384082c19182c00107c0b4109100c80c18042d0702005188a000500b4120b0310640440321141416840039040d03401c02d00e480c00c80c544c010b03010001803044a001c1d154001c041d03982c0c1140347c000114049965441400c9000d48480d44074440240045d100754400319915118103000d0540345015481c0001c0001030000590009040010200b0420301c04405c40d05000d130700a00400851503610144000203042d21344c004103000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 90490126 1250 90488876 90488921
    0xa030323030a060509100509061203210601020f070311060f0408030f070209010918030518040504030e010201110909040f05030409020c0312010b1303080c01021b0a1211060406 77
    0x4a003100514010070020801146250421041c0302002c0b00003400c4203041e400c00c0304200903a4840b181301941120050f2031480c0d42d401c90b40ba40700d20310301c10440042c0d0010382000143d180c0d05034000a450050009a003500c0725001c0e0b12107415643ea01d41e020250240b0020700e81105245800b4008110122a1000043c10559654032482c00c43d08002e03503030800401c00051341011490241b40b8607014001e240d404010760641c0203801b0620907001580101070110003d0481c1a10710540e00315202c07528020018016454540740043c1011941e002180c055803c0090b400041d208a4056a071b000c1780280c0764510300e540355280d10000a840080545440c04104004250000140018801d81d42420011992443c0086c180760403e40f0503480744082d8082400a0003902c9001c3c4c10300000c490b0450601e40c0c440307102d50032a038028031840020316a0011407004580600030301051440f2064015450404404424007042c0c400f4007840c4c0019400b50041c000190003d6043c2c0c0c0224030904a5008000341c64 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 90491376 1250 90490126 90490187
    0x1b03081f0810020a030e070608060607110907020f0106081203040611040509041b05040203010e18120706060305070b0f07030f020a023c10080405030702060406050310090b0a0303 78
    0x7103000307a00300c2d0030b40008020100d20341500900e09010002001408004d02e0420014450b4402174182881204001500000d003c0b28800044500c000241203d8a0707040c0980042d6451400440120807035007801030001e1050408103075018504114420945942d540f035030340c18001c10b201c21350032120441c10b0001041d00d0b100c45a10320b102d54418450b01e626000305030402d40602301030790700241c4150700403c0182720902000c003d0301d4010303004d100846d40c0000c0414800d400c02c0100000234140b02400301d901018030126402c901c045900076002d0781e007201e4a4100c56412445628490180c4950810090340000d201f0301084d0310650803031043e9940200703513500043c2c0305604840b00c0c00100e2612100e8402401c8000801806c4081e081130504a0b01c03841e002003008001c40100720710034052950700080c148402441280d0345558000d01c40380c0e07115191000581240c01c01c1e10111000c40e0100c030003007004c0c1c1492140c01045000140081401861035030100c1700b40707a1841c98800181603101e080c001d00d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 90492626 1250 90491376 90491383
    0x130b030c240c0607020709060f0b0310030204020c1b1c0308072705030f070501090b13090504030206040c08120f0a030b040e03031902090a0b1b03030106020705011b03081f08 76
    0xb040c4542c000d4911410180d40c000e280c0344079a00080030b95807500301c1c10045402d03480316403011105079225a070785076510b0260003030401403240d02c00380d0800d00018054a05a50110b20081d0f040f4802403070542c0401448140729000c402044601242d681411207030001c2070051032807070351080c1c20744ee00c0d00090001c007981e03114094140810200680d40d0282c117000c14a001c1c44000d104110490042c030f0840c2c60500004c041032082e102c0d0340c65018000410011103000b901c4120050150624140708504091400035903810701282c0c1591092a0540007045541c004030325004184036401503a82004a815683c22150f0310003143c020900d60b40f500c404109071100c1c05882c4c141e4880c00080c46e201d1078a40840f008111142c0306841da540c1c410001c2c5c2c01c3d030f5641d2200800c1a0381e10032040c9610b510141c6550144401d489038400400e1201000000d195903000a045055030002e80c0c8040d00722000b0112004202650f03400180402c0384000010006a400c1e04a40040840e02024031038041d620742c541c906 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 90493876 1250 90492626 90492637
    0xd0804210806040c030216030e01030e070e0402030d050c0a02040c0c0f0b0906060d030519140d020403060c0c110108091606021c051c0504060f0e0a02130b030c24 71
    0x22a24010820680f49028032424040b6030380384c00d0544c50441003603510f04008500c5e1600030103202000c900d03a10264809c0d80001084000301d4203e800750758885c001e0329050842202c00324481d1080808030564248100d09844248034800020302002c0501c1d4204405000e940c2581010003514103240000300da4041c0d9900c181e035006583c0c59401e410132503401414050020321301070080c944801e0110000c1d03441030441d22807040c2c0703403155030540e03020402c04c6a14002103201c0c00c0c84541e0101d12540e0b40001a4010f0048a200304010080360f580004260781c540c1c0800700203081602c4807210842c00354042c150070381d402451041030718020231003c0038200e0700001c0e6800c0500164041c1400f16410350141800080c44949418030a0401c1c1300c2c3e403c08142240350035090f5140a0311880840d0030840340343c1061103008491171007444803051881d2000d07529460400268072541c181650304298181504c1355240c01000500070300441d04903801800103c06000466002884152200300e102c100c0c100041c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 90495126 1250 90493876 90493943
    0x150b0f07061103190605010509040f060801111306030506010c020d150c02030d1a0307060f030207050a080304120305010312030c02030c060109060f0f0b03011a4302030d0804 76
    0x2d03201e051071340a55100d24224100700c044985000424082680c0242c00c2e00d40c12103044502180c14a107013100c7c00044d020942c444120740d82030482889603585940080e01502e000100c04055850395141c0c21000e65005503540b0b40400c480c01403020250500d00418801580a600d80c200c00c401120381100488528054060060b0800318001171b001000f8041e1900058500741d405001e10903500000b030305c40080344184400e200d9904141c2c0d92003402074042d1001c0d1608030b0103a8503014054100020b080c4e00c111021100c0002c6408400101c41c02846418141d035048218950712170101d20064000300000d0050f942544000c1c031600b82080c10800149019050035100403c0091074028200710a4019402503d980107001310180000d6010109030ba046a404150541e0580950562080b0754130a48000c0401040e9030080140c4810340300c0080a80c0705005841614229034071200124000c1400c0c03802540741d000b003802e5610346d0340b2611425400c24011510710381108805400b0081c0c0003940c243c0d40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 90496376 1250 90495126 90495161
    0x170115170118060e0f07031101080603120a080106120507020a0314040b0c0106030204050c030403050315010e0607030f0f0e0607020618030a050c031b18100911040810150b0f0706 78
    0x6031310440003440015055003003040105515411965207500ba80c400d043d40d90b0400400e07000241c010f5404100d80c10440e40605280781e5105029400100901c1c400d01416021460045000700b14403a24440d05229034030a5020300030300702c01540c044500b071800f628840741070310b014000418908000c0001b041d10307125110001030440c1c075510500c415924010030034581c0c0d92060003000086030f00711b4202d82c0c2c0450a409400a401000001070700c84480d10341c0b6842c0c000c480890305808154100c80040400325030b40e2107a100a19405001b25008034501c44600d40002c0140900f000500f0000040c003495000241003000c5059100042450075400c038406071010b6005090708071460078107215001d5000e6204488107480745050020460380c018014031507411880650000e9080c0707101c0c03001403000e004051400c1c0302d646420003c4401503040380c02030610718001d064028100028a200314001d080500ca51038500a141852002082c0c01c6000e0403189a40308001351400507a040c414545184140205c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 90497626 1250 90496376 90496391
    0x10b0306060301090804090510030f0605180d02030f09060c0f0a0c0e060d0f02030a020303041202032413050109080f07031709100902030709090302030417011517011806 74
    0x80624040c0d000d081c090003039250100d0103022540107402c40b800d89004040c0070860f6207a000c582c4004a1071588050311400108500074100900354200c6c6000f844910714504d81c0e20007508041c0e482e203190500d0784000d64000c101460b1540e10590240101d40d8004180500b01b40b42d194105081207200340f0104482d401981241c8100b282e095503010141120b84441d00781d03458201c0110b6a440c01680b0060407821170702240000319030301041900c049a60107001c0c1c9858541e12800500d5207002140102d20a004000d490f108181910401d40303455200d85108980c2ca0321010426168040f0030130040d20b480d5250405680410854ad00504c078031240071301c10603910459410020101100e008a40345011601c13002c1c48140d200016900d84944005d00c0f002a40440314400603140c0b011561041d41000c5c1020700002c00d040d0040091b000302d4507000b003440e02408c41e481c0418200d412001c4c0100e541d0b0340828090049a0b007001050640031580ea00020f580d80d500d0140031390798000b00b1004c68a29444020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 90498876 1250 90497626 90497629
    0x513050115030207110d060f091214070812071b080307030c0302070314133206042706030510050103050c0f1c0512040306140f010e0f04080417010b 65
    0x108540740c0600e01107007056242d03544e4200d0b41c0303406100d03984520f8500c0c004009002541c0d01800700164004000c00c90180103191980d011000420010085030f0003014141a80320498104e4451513031080b505440d10800003145c49030408064440340c01c00c01550101c6c510348088500d60000d04e4051604180c40745420000101a206074121000405005102c40030000b0703001343c02c600021480b1064a901c41041344003803242180c26610502c010752141c0307680040e8020b1041c0c206000181851382c00100d450035010b0045911683c480e01e200051500c000c1c0260748100c0440801040d0a241c022030165a241c80d811b00d04a0341c8017041a805680e9801001084401c2100c0c1413007000642c1c00c000030741445000100120106030a049581c5003d480500c1000401d000b0120050080b01a05403190b0300c906041004011180d00c0078141901280031071048858030140e14120303640340419005070351382d043c0c45009040c40030784201c8181d0003c2c040405e51040d041402c400400d035540002800042000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 90500126 1250 90498876 90498899
    0x330060a05030a26071a100302090106051e0c060609060915060304060e0706020601032901031113061403010501090e030301060507030c0203100b090603011a041505130501 75
    0x40006128284528080080b6100410050402c0750132044440004030110030800156201c00c0442d8030f50030700001c85004005c0c1511000e00c480038410241c401991328007011603500c05841c0806903100d0043c0004001e4144500b008140380040d10060303a42405000c601039070141c024944a42c0141c22500c02c00800e0700740060f0b0503602c25000ca074400d031181040000140d41303000c804c411318018480013001405000b010780041c840c3d030b20303040211030030300b55541c4000791599828003088034810564259106a610440c0c0d0348581d06003401c0c12091035910b50396400040404400415800ca8103849811484c0b1210717100381e4006140c99004011001c88a808242c00c40e0780580003c94028a0b0410a54680c1000400e0300e0642e4040d0416607511302260500b40c4000301d070140000d515105000290410720700302e81140249100a45106005468030000c25090310001022107950524024615290f071800350001625000000848000320b911480403580507020120316482040d10742e80100400d03071082 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 90501376 1250 90500126 90500131
    0x21e0a1401230415050c0a2d0c05100e10030204051201051b0c0709050c070614090615040f05090a02010801050321070c180c0201051303080c0c0330 65
    0x1003805030090b82c40310000410ba01550140d4404a440c1c2d00384d0110044c0101c0880343c000007a03a00702c0f19508044d180c10208000445401c2995240c95445000c4010311503941301482d030b0348400e01ea1911030a04042c0462102c0380c0c560b4504002e004605c0e1044c40e2224a14652081c2d42980d0150b0b855040c24140600301404800343c49503a8036040411604a140d41600020300c4405441d840d520320104008510703211a1341c0200e00b86500d440c09000b85001000002d0401b144501d4050101401c401d29416030000e08079003c80c40794014100044040700c80b00c04040010000038030008049030100000b104039403048800c01104da006400180c1590b8100380c6050040004800816071740b56042c090f0060071581d401d01700003260010511000300081203003c6000f91406031a0001403900c0e0031004d9010700301d100c4081c00554070b0180401c0070b0360086441c0308200c8ad01911804015202c0c00040f1811f50302c111109040c40c001840520a02d03481c0c01614400031015400d00180c808401c1000318086401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 90502626 1250 90501376 90501407
    0x150f0c020f060c0c10050a0212130c06080702030a180b0a020c040b0604151d09191b020318030102070b0f01150c11011209050f150105030601050a03021e0a1401 70
    0x1800007240074280010000030010172510040b49135120200c000c0f010703000d0707202c1340480400b61104025400c1d01d0311400300007960045030401101640d8000540300c900064440c0710044e0410021500014003c2c220a01d04115296085040c90754030303640c1c48823542140500000503005500e0340700c0c082ca4070b0301480b400d40383d0403507005241600e401c41071640e442061600505002480c00000320700314951104003015080540b042800e89410302c01030501d00405000744c1107903880c0803040f80c036440b5030016807407840485400451814000120422072441b052040c0c9504d0341d000c02600c80091a03030030046005005040e0b0031034003541094044941120700f030f42c00d40c1c00c002c4151012404038030030300340c4040005000e007003076000d0085d401e6204002c5e01c51b0300c0c4068514882c08540510b56480002d881e8140107600a861503240d8071401015158442886031aa00488960041c0098640014000d5107904208401510000c281c802300b10940c0050b072050350703110b0043e500103103a960005207a040d520700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 90503876 1250 90502626 90502651
    0xf0c080408010c03061a0a14090307060302040305240c090a0b040603020307111b01050306060d0603051606020a020307060503091603080d05010603090c0b0c030c0105040503030601090b040e0103150f0c020f06 91
    0x341b43e4a0084400540c1042085c0e80407201550040040700c0440e00f0103001d80300d5031a103035940a0084d5001b884115068807903030804804140c1c030b0b0a21420301d290b501419038980e88418171400180d03000130b000c250384050300030000590f00700c000c00204010021501d0258036441c001c10050840d00b145150000360b90840e2207000d11b11030580e03800d001194001d00b030290310703070b112800480ca2a003d1484200165403400d0b101006000c000244840d50040311188118070311f8492004a86401038000c009425900010051080d13030301540c06580d000700b40000721900d01c102d43c004550810748079030003034841d407800190340e8104220034020300b0301518403400c0038011a40c0682c2e80708601ca42387c0c030400d1070030100403404007543d49060044800c071800c4040203006600307103401c102761681e006980c1ca5011401c21440003402c1c1c40385501341c800322207482c01c10011507861a2620b0501b190421085d2071201da89600380440c070394551040007003c222650007000b88000f04520b840ca010405491213010b00b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 90505126 1250 90503876 90503909
    0x50a0c0207061707030207150e100f020c0a060203070c0506070f090905090307030c03090803040f0f0e01180c020c1201150501180909390e0402060a0f0c080408010c0306 74
    0x3090f038010341251882c0740040e603815441c1400f401e0740350390000003000d050130a59401c41041c4001425022500c1c40e01c403c202000d44600d036402240300300c0c0700c0140c49420a00345080410306a40c06594001000c1c201402403c0003562480d00300f1034211807520100704017459a00d030469100d0403c0d0060b0074069410401820306110017596400340c141c0050411140b0030984003094440c141d5040188042c1c1c0c100c0b40c0b0740752600e4406030505001e0181940f8901c0b501d00c0083c05e03c0d0700ba110300d4100c0e452440551003081c030129005016142840c0ca407003c2d40f02e400307020005a01c6036182661685c0f6214000a00041d1040710000100e4403540640d040244102d2000401e440800c43d2108543d101e80000901400c24500620f080d0781d60803480c945a100400500c0345c40010206d1112040c8401e1a00c0500303a450381e4895120741001d8501075000042804801c0c0f0050051180040c5040e090038519000041b070750f01c0481641c0319801103103c59450f41e490000c03941d0075018550182420340086908403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 90506376 1250 90505126 90505157
    0x4050109050910080601080a060b0d080708071103030f030a0e01050108060a0e07090207140f0304030305030c03040201051c020d0c080c0d0b01050705010c020a1502090d0201030b0103020c01050a0c020706 89
    0xe003a40a070078451042000440c2c42006640b500400030b1003100c06541c01580d5980a40ba150400c0e943c060b240141042c00c40140c03860701c180043c0c44190720898440c00e20b51a5220100c00e030304102000c60f010050300080d84956a410030203080d10104c0c901c0e07950f581c2e24011021409440b4804200070305681014018014144040b0341c1d42da201112000012711001c0e810031681c50110070740e00c00720020f44001031000c18050161032030743c2c01d130003294122080071004003d860394034030075032102074000b440034000700300942e6036a0001e5801500501d806802d040412420f240d00c1c003000e240c4403101541c00900c8006202075030040c1d0b1034a000d64104541c0900e001c48803541148503004002c40020f40d81c4031211380c241e010310f054400c00c9402000820110514580182d51040308901c1511901c000c402d6220480d800ba000302c1d0203149001e482c2941d082c02c44e90043d005070031440d000f0f0b814143c09021103558420244a003602c0340c61406408140f50fa9904006070034842c0710742144e02044a142c150b88800c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 90507626 1250 90506376 90506387
    0x2030a0e01090c05010509040b040e060109050c0f09040b0604051809010509010b010210020c011b08040615050d0212031b1506011403181002180f01090f0302010c020609040e03030a11040501 83
    0x300c52081c21b00c655114501d400103001410f50120b850b0340507180c00c90060050307800140242c181c41c03a001e801c0103151030701d4081036514040d040b00d44114013420054010142003a0b0801c1141c0d000182505044c603856000280f20800011a20103a4230884001c1003586c0c80240540e58002c0415002000100741c05070000307494140c01800c0e0550719030005090780c40c5207400d42c0b004e80020350384180c8401d02c030288040100124000d4800752015800c18103108044180c136500e0104550b4000c01d40d204010680d800e0080803034049400050031f001c28044c201e80011524607120700980c003280544010803142c1450710b8641e0005d84914100105200700160340b80003c2e040b01e41028408040440303030703500070440718644545200103424040c008146005400d823000403100c40302c0400c4170400c681c3d0380c2103401102e40c04054803c0340d030b0001c103900e010809940100b0035681d8190000c1c12051a00c46004046815114410203000039036000104001d100a218401c1c001d1403168119402d2500d442c14000900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 90508876 1250 90507626 90507629
    0xa0213050f0102030909060a210302010b0103050c070308040303060807120b0108061b03100506070b01050117072304030602040605040515090a0e070513080c011407120c03020f030d02030a0e01090c 86
    0x81c0da001c40110b81f641e41ca41007940d0042c42001c4a0200b4100120038660f880c0c9540c650807409036081189510696020b80103480c840c004a0884a050845544080f16614030251054062540e240400b0400c41e80900240e406440802c8140040da482031a00c00c200e241e0503031020f022a004441841a0741040c0840744480302103c04c222074680d190300340107003141c944a500850b4030260000f02c0d00d080001c00380d03480c0c0c1210000d07202d01d098508000c0d454400404e046075008005000c2d2455688142c0d01c2c182010001d9034810426420551607075115012a0700030b130004400304130080703000c10151400300148443c0b079000311314007400c1c001c00201080c0c90355024000c50a440019500040050b881038041e14421800509030a031200d81c1d400c0e0b03c5880b816a0142e81d40080c032015a20340c440c2c00c001085400103940890038000004199104130341c8200003800460440c090082c0700c0c0c2e0360901c100041c14000303581c0c610040c1e503800d00744002400c81d1410f0098884a034142500000416540c030f046d00c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 90510126 1250 90508876 90508879
    0xd0305060d030c1704090f0e010506090c0c07030b0405060405070506040f1401030908031f15121505030a03020c01020625031a060409020403110604081b06070b0a0213050f01020309 79
    0x1c00d04082d42ca05411130505510030001c0707407040414002030707601e019000740101180005c0c00708503662000c4540d03800d07030f5012500070307030815200300120300e04071001001024100e846038180c40049480f0780d640a0000c00c01d60707080d40c0704d0b40007005001c2448020300000e03006000480d4000d241c00d02d07280320b00b1900f01d010310a100481803c18405181d5034041d8010444107503002140355541e280400c5401001d0002245041108035103440c00301d4440541c0305848010341d410b488021009892020007005480d40910b0840f010003920301c0040d5648003000124000c5200790081c6c94900392280009260000003800803840c0f043c03115859174000c0702c3c0a00403085080380d20380031808202c1803000c00711280240c07440302d4000b58001000105d00c24039034080c0060f03078441c00c808070804904408000c0c15010300d00030001c0f50381094455101140b41d007108010b004e200500450b04082070b82d240c4000142045510030a075540018180c16041280c0007a44050002110b003034208071140c0d40002e5980c083c0700c5615 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 90511376 1250 90510126 90510137
    0x1060c030801061d0901081f110409020702042304050c03030f040b03060a0f060201060501080f010b030c03090a060507110c0307031110031b020127050a032a0c05030d0305060d03 78
    0x103149070480301030303403061a0b403000e08045c0c013550b03481c400e072551400342d007201400124084961641e01c000c03900903e4201080c0c982038604250900d003038071000b0340c00f4500c12a0306c140d440051000c0440e521407942c421000d641e0103c8000d01c0c080c10b2a80c104814072010501c01c0c0c0040142c12200344600d4141c5081d10f4a0303100071364072903460b400802e0f8114059040840d810b48070350000034445032305402002c10f94000380d032800100c0d164060000c02d408002e0041d851120400c1c40060500f04042c1d0140d075000034070904899099909849800c100c1d030090741d10703a00043d030f0480d1760707820307050200402c90341e82c941580181000c40c51600d070342c00c21030b00141089120391102109004030034441c1e000310103840402011182c807032034103d40181c02041880c9890000155818442982c036540c4041003072681d4200c4044c02c1084000e0380e080300c0642030b124904040340351091005040b48001d03507807800e07440d105581c4040e8250420003014500002c0c600c03003404041c02e0000300400c0d42c0b11070141000580d07060410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 90512626 1250 90511376 90511397
    0xe06010c03030e21030a0f181b090905010203010501030605031c081504110d0b0117011202010908030309010501080105090307020f0d03020708060a1505011d0f04020912010209040501060c03080106 86
    0x881d402c02c9608440002a5502c071081864548504e10082d40240c000000c02c2014000201c07400c800d86801104064001d03c00d181001e0124840803d4840c05215a50421800d41d4582c0303040d00484041c010103807102ea6000c001400296050300c02c160240000704c4c01011210b40340c0046240003a101403030b00c0f00b000910b40115848241c42040c00001f02c200401c00d0000c0380030610f954000350041a0000f0403a82800c3c2040b00b2035005460405624880f0403020105a0800300c00d483c140c42e2250040b410031007140800101000c0030310245000c0c03408000045030551400c0007490070b680020300140400e40040203610f0041e0b4601402210055003915800b044100905060b820b02d0660307403091606000e8401001211441d07640b220425001403881520b0f090b4844004403015044050b90401580b001441c00b4100e00d0b04902034800008014805480d1031030000115088108444070112a0381d008075010205141c07038040c6c0c81c050032441c80e2013600464591001804150b06104283c01d10459006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 90513876 1250 90512626 90512651
    0xb09060f0f10020c03160e041103070f06020c180c0a110a02090106081f0b09130603080a020a031403060102030306090a02090301090305030a1b120e0f10150e06010c0303 74
    0x1060092410010b200280da8008180080d440d452082203551280c02608038105094420000d48015601120b0b080b118a41da180e8034022020350006c8103641c5449800000141e10848400c00c40c00b40102d54041c7c031407000ca0700305110320946041002c500045400080041e0540401c00783c90b105c9202e0f14100304288441540c842c2080c04001000e500220b01c0381c0003081c95078000304101d000c0c018071442d4101e600120181c429071260280500210030700d0030841c403601407400c2031000403602220480004c081e952036880412a50003200000056044500d00b0303002d058010106500c03103407030340c800b0600e58900710300000e49034840100300d24420040000400c5c0d10461b1907041d5100081c0107030081049681e2030401600a8000300d549006560900004094003031401e8446108025203803101c110b02a08480030034083e281480c80c0724894420100c034041368080801c620700a80b03500100004106030003111080e00380d200e640155080c00c900605003c2030740d07480400710000580510307000820008000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 90515126 1250 90513876 90513889
    0x2301091404091b03050102210f130203160807050f0d0f0206070f0503040b07150c02060601080c1e0a0f080f0a091a0a050601020d0309050c120115080c090106030b09060f 74
    0x807920703d43d8a0412010080280550041201880c0541c00c101c3d005481411030125110403034503150340100c210041801c16410461005005100400b907801d150510701c085002982c040d80074a0ba554895101000325003051b85500c0010030041d42e500c50108910b0710385200201d000c00000340600000160300703003403004031120400c00b20340c4101566135650f9203031110840b58200240540d20000b801c0d0340030460051901c200c0a244a071a00500440d507580f074015100c1c1140240b030000010410010038804200381012260030580380b081240d141c0303981c04d000501e400072940c080c50500000318140604c1704171525809a024100c00c8010030303040d003e03140941c06074a01501a406001d003075420f100640c000b5070400392003150280d0031607200c410851000c406451444070050210740150850400904101d285c180ea43c00c90140086145980103032880328407039456100f0141c50300030f904041010b10304506203d0050405107030900226800a000a94006000e410f541c4202c411224800352600c03100b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 90516376 1250 90515126 90515153
    0x6050607050d0f03050105100c11101e08010f121e03050315190302010507050f070303050c1015060516080406170a0c0e0603040c0302030601230109140409 68
    0x500000e485024501d0810740d100c08900a190101c2c2486810300c00c0207100f8032949040755401060700c055036241e580e054600040c50003040d280e40035002020079082d15030b080c2260441d4083d0382d44006101d614202134070303003102c2e050108040242c00001044010041114030081c0c1e9070522303031400a9165450030090300d0240c080c10030070400c08107449405250304a00510700c070310703010388031000b40c5403c1c0e10810214505001c8082a0458110002d101652040c0050104284124103c0300b24080e041003030b40c0341452651003100056000034007003040240910140c517009540c03160601c401400d020810f810b80310503005180030480007044000d44500d00c02c000c003509e01d8100c05001c0d9035a44412000f04000390007030020b044010801c0c0400c20001c0b0a12a180355841640d44006d8040320071f1080042503403001d081503035510640301011000da502481594000c020780b0156045d0780c00b15480c1140e8400710110f0341410300c07a5907002000a100c0f40588289405001c0b40c3c0000c90324220b14000c072400540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 90517626 1250 90516376 90516379
    0x3110a0c0603021801091505090d05061320090103030e0607170a090602060c0304020d0c0e130c05121002031e041202150c040b030a020706020307020a020a0803070203060c0c010605 79
    0x145100289842d0903500078000b02c4556604403401c0c481c40d0b00103541c5402c0603c24480e50000742104600c0141c452400307802140c1d4006c12003019850141c4500c1e1401c14280d501000701c013024041602084405c095a86660340140f202401116002001030000481444040c2c18086400052030169907003000700e44009511004a1003101e92050010086420042102020903031301c0c0004160940005480303449041084038052955940c0d90903c1410300e600e40302110319001482c40461702024054039240b0889241e00f0424089a8070304100020720320641c800c070302541080c1200000940c0224845800001890000d81e42c0d407240c0b55501c0d0751000c0e410300081c0c034440080900c800c10030100c083c21400600f40c1d08070344060325412600a8403030029140742d01103050400040060b06002e101440d400903070b90707800500385880c075101d0206903441152400016045000e00e0b004525090325948080c042e848003c42c2014415804640d864501808148031004081000d00007003100350000301c0078000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 90518876 1250 90517626 90517643
    0x12060403030c0909092301060e01140a0e04150911030114040b0c0405091303030b060a0e09090303010b070618020a08030403030201180206090105211f05030d080403110a 74
    0x101418014010208141d00d18001420902c0019080e040c80c003036070705c02c1c03a000780c078244000c007425642c240c101040075500c5002d5501c4041c0050003101d072211982c0204881100307206a9007250f02007008002c0a504401403081d4504103010100c1c0040800180032600f03050001003220307003402c205a400c072110945907855800c241640e43c50401d002d20940c01b840c850a101c43c101d031100c00d85c01e40725001d1400f40c00e4000300000000380d625012009884032290190a0001d0782d1988440424015840b094088010502104064103d400c00c1c03d6125400190300025608550405403c010300d8410810b002e01902c0c0c8a4505040180303000190340406640104160407050b0b445165503200c1d085440142d0255280c000d114104030800c00c4070210b0700360f000740300c0d07881c02c601d002c0150b03070b550041c018089a594222a4000350180d943c21914011481c1c074103690300700001c0d050541d40c000d00503040303580aa0080b03441d00e4039a640000c1e486401c82d80c1810011080d805940e0700c1440d00544400281c030100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 90520126 1250 90518876 90518881
    0x7030c05061509090a0308070f120614130c02060c0d020408011d0d030b010509010815030f250506070210111006030b0105060910081003020a140a050108100501030b1206 74
    0x8440800b40c0c603420a4031a81c03150307900e183c6001c2e10342151803000742c0403404150001c0c0c40c0d64032070314003001e80c98250306142c500da0440b070085004880c200d4000c50504d82010240c0455480c0500d40408202c119010034050010800703402522804050852080b0030008107408a6007090340c5c0580d4040c0c41d03840000c0281c0ca110022044014000125021250282541c0000070713901c24010802d40c01011b85a061410f0001c400455032400014400140740e03d0000c20310340360307550030700680450b102050001d08201c07040b82c41282d4a0f1a1400d80f0b43c100304080344040225032690000c0e980380c150111071866030780b003c0200c161050441240c142610380501e2645001c00b116a900101c140e9000d00c01c03214003682c0711000c0c4140c03480386540e6207a200407058003030600248900c00240c2d00110590516940c15565404501041c2064000c0c0c03003400386150048400b41040d14072900108400d10f040481802d0800311220315222601902e410140c03980c1024105848003980030303201ba009142203400a2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 90521376 1250 90520126 90520141
    0x161d0a0306050f010509091b06090604171c020c031009020a0302060703052d07140705030a0510052a0d112101090b18060d05070b04060f030c090b07030c0506 69
    0x1003e09008803841800c3c0e5001051500c00d000a425250003401c2521000e440c00840400502d80c100307a6501d640100300304004581c0c8200a6070b04400440250700506042d46420006440c80c14041c0b01402154004840350040e80d81c0011507889030b550311100000c4040140c0003150042e003003900065084040042c5403010154810b000305058941820032036000551280c8500790069500d039080c205484c1401031201003220200011442003400007202c651954440200b818240100300946aa40160202030300315000d5002d22540250b40c00650001c031542e40e06044035519030f140300f081c28800081180c10141c6480e500076071a040c0040102501e0300109510130030340540500798151000801400098590000d004090004c5401807030004550030b480103c0c484000001c2040e0352126810149402250307081c801200a40003115104d560740e030078040c0141c2203a650442c8402018a0301d8001d00c042a4040c05d100180c42500003569601c585500f0100d5000e00e0110780134207113004079024060714 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 90522626 1250 90521376 90521401
    0x212031603090803030f0601030e150a0c08100b0a0f02010b060318010b030601030b18030708030c0301081b0d0b0702010b0a08030a020c0406030c0302010e0118031a161d0a030605 78
    0x2218402e64444076815101c040f655128081551142440d6103481c001ca261580681c0020000000400442d8110010156102808101a2051000c19540f0850003010603400305c4002d038030045114003011220710f010422102031180007101010001c0f40c0540e00c0b1614800e410450030004018480c0e500d84c10841c038440b540035280900b01c5090341c40c000c0e0350045802c0102c0d08504a0740c01410601603980c0d2524403016100c0200300e0700013207002c104200710006440401a50042c0e0b003080025840358105038a607450000306260300805007400c01003150f402c3e83e40717880c2c060036a90b110171100c40e1520b444609a0252040d0b141072030713101c55900c0c004901084000301400c1604c003507900300c0307c0c0c001c00381050008640c658003028081001c5940c0034800355008841c1b9080300340c8189403800001c01a040d007400c0d0451260003c5903a19540d169a60100030112030441d0030411403401551600e01c40c41c0040d100203802c9080303c0c400c40c200400100c05a071408080d00c025900300c00e0500481c90f1403008241d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 90523876 1250 90522626 90522667
    0x4080c060415141501030e10021c0605011103070f03030e0f01150603060303020307080f0717070302010b1e010309020a080d031d070e0106050f0f19080c0a02120304021203 75
    0x1042c52404011600b161070055100e070051428081482007103001800460150030750410f07190706d030312808101900c41601c51000784414141c40c400509528119040d03041919890341c07046042141b20440c0440c901d501208485401c0c3d441702003814102d140e0b280590103440d016140d40c0d4076018030034241c510200103400c400300d06840d02e400e10f00e415441b0401130b000c4400d039010140050384180010304c002980c410040c00c80c040d0034100320f0300f061410f954902040d51015030a5466601c04a012410181c0901844460a0084490b008011a50727000d00e40301d80740205890741010348030407101d015901d4244880700980340c041c09031020300300b2070316010307015103003d4a001912900c2ca900c1141030000c0411108140c501074040b580c16a440c2071b9049079181c010445002c11907008000003000024001c00404415690f800103446166a0070b00140c030800c0000d03c10b0301d20407020082c40a100380d0108184600c0c0031440161910798850380080345076488502c61910651000103103003400e02075038048592 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 90525126 1250 90523876 90523913
    0x90507180203071e05040501030f140103260906031501120f06060206010f03030c080d0f090f11040e07170c03030403060e0f010905060f07030e060f071706090103060504080c0604 78
    0x882d40304d101d01c6100c0d0181e1040c0200b130020324180710a01032903109410108000003004004294a18501001c141c90700782a030048944165402103880d0780305040c04050941c1d880031104900340107c8401040c92880014600014101550f141c107101d41c4c010f2110546403c3e4520b020080c1c074104843c16801405c86004e030001603c914400055200880d0080c0c00c10741e0381c941c0d1030100721840c0703569283d00398010b01e1062044544507040101c00f13902a1040f21800d90090a906011504d5420500e00d418140045a8000e504040341c8401002001984408403031005100c9403024482c04038250600503540d2a4903450300002a001052100d1504041c4c820040c0e002034a2200c2d504625046c200d854a00e40100540c00c2040024182e9000280351030380071009080c0420140d007940a1760782412811500320b41450034000600221030b600c01e9018240242d00d4141c0e50351810044006144540d0510000745969100c40003cce04001944003503a80708061041241e010382010718140c44910015440e10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 90526376 1250 90525126 90525137
    0x1a1603031a03120a050c0f0d020d0f0503040f020f0406050a0f06020c03190308100905040c1e0e01030b0a0e030a05030a1103150108060102030415120b06120a09050718020307 76
    0x8078110724001c0341003a000504400507502e00304100200740c0385600301c1c1071104e88a00805041a43e0f0034000c1c8803000c000030340c41e4050101c0000d15840a00004e440e804c0110800c07005204000024119141c10181c89404642240103a0780301c0d40054003078440c40d0481034100b0302e4103a000400500e020098800e03134003160296242c800204090644c0e82c3c035034440ca0ba031403001c4006408003103400b680c4e00a81000300d04a05004440d00ca1a101d0107941054804603500d0740c41003010003520700ca400c14549141000400c41590328902074442481e010b06000182810304503002207052429564006504c9491140c1501d80303070000c07044d000c0c1964208030b6107840c13413038203142d03400503040c020300c007201d01c00d404218044900c0861400116070031603005220906501c010400418400710810300111051003070f581312400380c200303420740c001501e240c00c40d2a0300460042c829407076840340d082d00b250380c0020002000035a0032f120303082081c43c02c40c040e4080f440c0340581000040d061407607a0000c51094030359031517a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 90527626 1250 90526376 90526421
    0x1614010207030c0807031202030f0a110307021e010204080109050d0f1e0509030c0a08010903110304140111030909070801030308090c2101020c060709051014041a160303 74
    0x4160a07072041a5004000458501c01d10001911590140c90058001c1c944080182502d0911408990082c0c0c0c0c0b6a05507207180c0200021000240185401d01880a00090079820420743c040d60344d101e501000c51103a0800312140d070300c9400950640e8005c00803d0003d10080080d0300b003da407136214101680c00001d052102c0f00c586640941d058105403003090048150610100b54101d9650f00611503580d0701d4055015002141c1c3d5440f40c000c00504603110000038200c00500e0301505c101c1c4100c0406c4055081807008016104189146400744e0200707080c0129108003071600181075103d180c803461385c040001000e100340c51351b205a003036040e0b03803082d11070304615110018030303aa440c00a5450540d105502c41d45240e482964545031000e90f40308040054207100000080c40c0c2449000c560150015043c40f10811440c03034081011050351015003000800300190b14000491449607006090b02100e030700e03604c5003504c0d65600488a58081c41c0e42404082c4480d80307801030250580114081c1c003070100700340c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 90528876 1250 90527626 90527663
    0xf0303090c01030b0112090c0503012405010c0203070306020c0606011b050a150618050603061e06010c030908100f0b220504111008070909090803040f0606090216 71
    0x2264018555100242219484100110b025101c02c000043c1000300c03080e05c09644020314014944283d02c152038040c84541000181030840d8154028444044400010102000082e002c940705558081c640303140031010600200c0d141c020b0310ba000410340b07880011319842d613850100f4414042c440c00da03030b02080c00c1c054411600380e010070f001c00501240c0011003610001120342103e84c140c6c2c03405550100d1101e94440d880440101000e014101840d01d4001700140c4d0725041c00907030f138441140d24100041e61825860404050f034001c2c00d19040c4085050f000003414041c1141c04d004080860440b031a00417440c9540c0050701a84142e40307266801d0079448003580c50a280c071460700010020402d00d00b0601804444089c10000c1c0c02a0b80d00c195007203103c1c9958031503d8040c482c02d40540c403681580d080c05c010051100c00594040c0804c0303840d0110742000901d00300112a0419003166500070740002078108440209559488506154400180c0c0c016203182861400d0720740d40144510040c2184181 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 90530126 1250 90528876 90528883
    0x308010f050f031518010e0106050a050111030a0f0c02060c1506040c020c0105180a2303060c040e1509090d14030106090506070303090f0f050f0d0807030b1f050c0f 72
    0x42c1c0c12580f54000c020328846403502a0fa109601000011075000c0f400443d101c01c50840e246c82032009140d9454580a20450801c13501290080200b0301e8803011003104072290580b6400785040c900c0030003074003803c02e0380a03a20603c1801121030300104480e43ea44810b00b0601e86d100100348205258104000001c2c580d85024414800c1e04c2d1059006010b440030010011600c96008101c400d113000c0039007100c40040d849201c80d14014115241d454000e402d4481808140301b15203043d103e220707600c070a00304104100d06500761012100741c00e1401100d0b0720b03060792814040c1040c80e1034607040480c074030405c181e4060001703029034403854a898038522203a0910007400c0ca40300074020341004c5200e08204110900f4410020050503001e45000102c8048907911101107801d04c0d0340a54507002580c1006050003418064502c80d103143c10001c00442070076500140c07504900400030014555900c501c502d117511003695860300c0318000c1d140c0d60071a9013030b1a0701401c0c0340c00011140c0000d100d0701c0000245490f001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 90531376 1250 90530126 90530149
    0x1e0c03050603250305030706050702070f03050c0d0204090f230106050a0506070804031709150c150a02090301020d1505010c0f0f030e13091704060c0b0403020a0506040308010f05 78
    0x2070064254030044480011400c10f0307a21005003c840f0259001020030020701c007400140b8482c900210701410003503c001c0c5060401c1e0486a10150250300400014800141c0703040c1034203068504c2c0d80c60011a00000700113000d0318202412820b9500340310001c02000000700e200c141d10228100c401e807200c90b0394050880d030103806425040100744109022a241980c003030061b20348070305425403406480790345842e400403040d10740c0904841d020030198401d15043c0034051800241024241c203090003890101d0741e452103060f6a482440c1b074000424660760310b580444001c0040a0020356444c10000e005400411020b250285018508500407901f0f62140000910803078001c1d6a403400550580c031011a03c5078401d804030280a1501918091038860365110b00102c01c825000188901c80c5080000d000901c14841c44041c1004201c14031280c2d40000104a5950304008041059074540c0f50030b900d002d80300b241c0a1b000c1d01c1071000f00000c155020004c64146d5100d4040034071020794030030070300c610349000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 90532626 1250 90531376 90531379
    0x6030b10030f1119080d0e1512101a18040203070210020f0403021e040e1609020f0d0216050c04060501050702010c0c0b030718050d03020c011206091e0c030506 70
    0x88404030300428034880705483d01c030074001c040300e0029009101907241e00c012684610003e0304110002100250840c0030101801c200380c5030400b000440340c660030075a1155542d003000c0f0b0b00640000c02c410307c4a07101c905000d030144000700008400e40c80713000301981d04003003c0c51008008081c24400d55044ca8000c0da4000e0807550014045200c00d0004130f0080c0d003014600c0c4d4040d0100b0700c8000f001d61b80701a00000c01c200c14074203101110003480248000d803500b00180410300d9000328600701e006440c600540b400c49030360303110041c1c0764042074004010710f1007042d5843c402c1e1400410108040f40004186004582c40340044a001804400900c0140c0c0d2440c072405000c2031302030040c000035501590350201040d07c602080d080c074586441c18800d50360015180302002441a0300006031002c0d204850001522040381c15003108a01d40e0703402980c50205214070f60401c980b40d44a4070a404035604140c0c003501d444034043c429100321698820b2020001c540b86080d6509040984804500070300c5850b015420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 90533876 1250 90532626 90532643
    0x308030c0c070f050906010804060917030103030806030a0c050d021f180603050106210207050a14010e010e03030402150c03210c1305090919050c0102010608070f090b0103180606030b1003 82
    0x86d036200555a040009006884560311000b980c00019043c0000301d941442640c1c00369240c1d411401c0080444000034516030107036202c3c105080224142070b603013404540c021526200f1100c0144046085401c90028105290341e014121806a980020303481488800498000c003d0698510003142038603800e00ca080081600301e0420f0360030101500c031f40b01342c8000803000540342c000940e07502c80c40e060401030709440c04460440301400d5034100b070003480360900400c1c00030f02210080025454580c80050402442030748880550421018000192480c10000c401a00e80310b800e40244c0c1d248c80308002d5001e9805000c1e110018082502c800c06460b04511518064100c0d6410300d400d1018200d00034094401c244242c42c10784502c1c68102c144045000d00c600083c00048031080c0001e42941c40c660400c0007190400401840032109190301a01100d14825001c0b8490b110100160002c2000500200994000600143c00c3c011285c00c68821a80b068504003410b9981902601c01c0030340a0000400012 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 90535126 1250 90533876 90533881
    0x11030c071a04180b0a17010f0510030b0c0a030b0d0308040c060503011404110d06090603020a050f09130614040b1005010207050d031206170714010c15090c0308030c0c070f0509 77
    0x14a501803520110058041805c1c25111260441c0f030841040031104107030f44a99071304103548c086003d090303001192991000c00590a580d2140c24903a00141044442c1a000c1415401148207400c01100b4000c09894036035014403a05006010140c100c9003682e0103c1080c1e0005450341c45441120b040311520590604011202d008020243c12011000d0030307001d4081c05a4202020203204070f0004104022000450b01c0c6944140507400c58160f00143c824000c4da1031480450301d4081005500c401400100780b101c140031301e01640205990b402540301c01a041e01040200041e10850318050601012a588807075910401207030f6134a141c0c081d180d0801c034880b00781c4002038011161034407245544000461103a03161041e502400e031003201807552903889000d0410a00040340d0100690000c207103800c0e840c5020549079025154565203c1050140d81c0e6110302c400c0c801000ca02030007031640000203a95906081056103800e4020400c4000640981880042e00d120302c00710910480d00080c00e100000e6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 90536376 1250 90535126 90535169
    0x2e23010c0206090409121d0604050d020108040c0312030504020f040c090b0703050d15030201120504030c020f03100509100605030f0604110a150926100b0111030c071a04 74
    0x642005a0f4681c22644450b2994000380140c2c00c200941e1050b0303a610060b8180d2500122060005080407030b028031401c020a00c240d0b161010042c010b5902803c001459403564a04510840801d80c0003a00e2480c00003a26200c85501d0342001e401a4002c403040d000d502e9000c0100012554000c540f1000700b007a40300100304c000d0558014061aa0181c1403c03400e02c3c00c07810440c1d0a6803039000d405604056252020300440d030300100c03144c0b074002601c44100524981550094488140410060301c0303024070741d95810700d507602084144026862a01c040c445420442c003c9030351000c0c892107101c5100e05100002c00c0030706002400e61140c5148400400300307600c864541d0200005c42005c074a0f00700459607004142c2500d1022a400c5105a580e20642c0a5280000b05004021000c07284030303590b24156040403908000103440c4607640d801c100700040040c0c3c0e440c0143c0b05031380d200000a90b14040890201040c5801049241c101d511191682d20300c4049089a030300148141e00856000ca4940b02515140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 90537626 1250 90536376 90536389
    0x2a1d01030303110c1b12061003050d1b02210307150b221d06070221090105070308060307050d06062301090312091d0603011d0d03052e23010c02 63
    0x803a10080c06c4905800040001075040c1002101c0344070f40d21003140d03400c2003001400c00c120380c800c04040c501b1040403404025400180025424040c0c8280e01d00e071140b0341166115600020440b85110449540e00210710380307051001000714a500b140303071403d0b444444a092200b9603110f65941d400079481502d440c2c400040042048440c0149241c40110822080580401034180505100e400030620080b9030340c4500d10a030301c0c40f12541d20f001018802c00d02d051b60403070140e8044951606080b044cd50f5060042131170120150710003a489801043c0d44018000c05600c004180c840955140506c0310300c0249180c1c1100880721803900142041c17004002003a90000e410040840302d250944000d5a01c0c0c2003030a002411100740703901c402c1140140999440d0901c01d01c1d20406469a003504903110b607005450300c50240055284c1819100c5000500100c2e0a0b0b9090580544459001701031800e00c510354500c64040f4051800b030150314a51120940d99004100414050160756000d81001d00b94280101c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 90538876 1250 90537626 90537673
    0x308030c07050304120c050a05010e0d1a0a020406020106090603030806090a0f020307080601031d10020a0917070503070e01030c0b1b061617042a1d01030303110c 71
    0x600d004140002800140103100420050034201c02d03928201c611400c01d007400c0a01540014400c0403140001c01c0a41d8101e006100c84070710031100030405000504100248012000d003029940150500f00a002c007000e07805482601d0059008001d1140c6880090048900c2c07400058046071a140028085103060340d5115440030100ca400f1a600c03044c0c0485000b660001c2d6800350110fa42d2004015081d41e0502ca000d515a9068058842c14104102480c0d100c150403581c02c0301054000071500407080c02104404010304402c00704001010b000e803841511159140206403090141403400039034016091003681c10781e508600124540d6187c03261070b0340f0b55444040c0d951540c101058442c02d07808024000144a0603040c0d51400c060450319070024004509202b880130602800700034480481d0b4600c023824484031180000719090031080360071340400012948503642402c8894a410b041104142c0f07900d0480b403003518148840041e071030009007240144070504045038403034400000788078488003c800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 90540126 1250 90538876 90538891
    0x80d0801050a0b1b030a03050f070c020d03110a02030303090102070303060e1005060a12090b0a0c0c05030403121e090509070e061806040504020c06010e0907051005030a1b0201150f0f030803 83
    0x500d0402c03244c2003507041d500718200700000b096580f020040c180c407154008550041240c5410304d8440d0081e400640c02485142d13001e010800c1101d0412806641086681c14084c2c00408980c0c9900d130140809000c0d6000a0084000a043c190009155240c00c05498010084541d00224050420090201541000364820200501407603082c07051078540c40f61844c0140100d05014aa00d010b280144c1614a05240340d810000c1d1410044003050000c000d903000e483d44054012702e040c00c400b40031510f00b1407010b026200e00b442544441101500b100004080b00c0d425120303c0300c55555140256900c600200307074550003403410005d006080243c0080d2100900d0000c02e0720b407e00d81c484010404a0300091070350b40310350740020014400e410a02480c15400528540140000760800c40031801ca2005048000140079000c0080380b15a0308a4105151000c000c807401e190031407808000a0181c00440382c8201d0701064800046a480300c4041120156905861088004d91a541d64910183c1c0000c2c140d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 90541376 1250 90540126 90540157
    0x30711030c121c0c0c1704050913020f0609012c041e0b060f18031e0f16080d0c031215030b1008031e210f010803030907050405070203090307030804080d0801050a0b 72
    0x2084560f20960f00e00e01525440ae10728002800520504c20050054451144985000d10000d4aa41ea100542d500f060f00f265982c8200b1751000420184111400d850840d8030a050000d07000000c9400c03001c003200389600c20741c14460703501d91100b030101510400407092010709040207201c26150384000b00c0f00a84902404551011040f07128404c0d80d090300c0074a01d000790300700c1d074444030300d03000e0402020905503990205820000d14080b03401ea031342e00e124040781040c003a40440c0482131600445d008030084594503024030241c0071510b1002c814018500084902c45010070215151070031200e40300341962120002940f404200d0b01000308158040360300d1892001d410402c400c00a4841c8504840200140d06100540e05248400784010700058124401c50352050040051b00701000902d003003105c00030758000540c1e489441c4200d04600c6007450140c0c061140c80340000420017264000d104171032004003075440c9020a52400c4501c15801c0c820035502028105040c01130103401002030094940e910001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 90542626 1250 90541376 90541379
    0x60603090f0706030213080106050a0e091203010902040f06080403090905090c0d0b06030105090a0503160311150f06010c02011d0612100306060911030711030c121c0c0c1704 76
    0x1490b200c859041140060780100719210b10b48008418a400b91190a0080c400c99082c08003240790041c0318854000c0140070400410300110080c81003103810003500c200380da50ba40e11101e084000c0c0d4000d1180000307030740544a000903000d20a481c010b001d00e0b4150340b0203070031a10342030ba200c020340805417411585004130303041c516050350381000c5a241a84116640112454064101803c441e0001c0075140780e03400524160340000c41c04003c545485140c1e12100c01c80c40118101252400070b04042a0124820b1024800d000c0c0d91000b600e5210300c403110000000350741c40d90300440351041102e6000f80404c007003400c40f11800002c011054200304016200500341403840248000a07601541c8072111000ca001044c014442c05000e4840030b410884003d110104034849017203160710005025000300942c018608104400501c00c0300c00e10038a0b82d048449200c03400b1100e4601d03500590b0019403800318140c4090100c8110b006480b400d5030607440d002203004868940002c103000c07011420030b840204000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 90543876 1250 90542626 90542653
    0x1204020609061204050610080d030c09050a080102030603010b011b110402070203070e01332f03090a0504060614070804030204091401150b030c0705160b070203101406060309 76
    0x243c9980e0785001d0408003d070409003005070401c000030b80750003100d41c0d012800f44256003002030000045011446e0005480d5001c040407590741000d900065070004012100046019054001c0c60281030105c0082016220420054400d060505a071a00460403001d0020124501c400c10881d000d601804c0035141641507400a802e05a0b00d030880020b0305007a4005000ba0400f84801111440120903021003040c114255107010f1035400d8480070800003212403101081c800170458a40c0050038a50383c220007505152699201d812050700d89008400044001840f131409001c2c907821211541c882482c6894000c00460031507200900540b403445c0b00700700000060300e03148a4503040d140a00d504514240c02c0040c0d0310b0031340c0d40d50301c40803500d10303003600701846100d00c00000c40341c206403441201507480c0d456162140c180092004640310000082500044480240004018852088041e1624140900880c50484450135008200b12421000041e050b080c81c03402542c201d11000101d1354007002d00d60 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 90545126 1250 90543876 90543889
    0x302010e100c0f0c0806090f0604060b03150c180616110d080d050f06010e0a0510022103090c0114070807020411270a1d1f15090501050a051204020609 66
    0x20080381c002104113000c01c1204030900103ea08210320f000070302443c00100a2030349e0380c0e5002400c0501010365070032811000d6542004a000c880350300f581d003045241b4042c12160300c5904010345845407456031640e203680b103207000411100807140140603250640f00e0b503158084ea524900c0811031700441c03000c8030000482e002170b000c0d0820b0b1480803c00306030ba1404041c2400c1076400030341014140404040f51125907038854020009036141075460f0400d0004d0110200d0ad000e48002442e124402c5403030070354080c070800500a40c460350403c4e044940f50b104190044602203c160600c0d132240c00b040c0050000902c0420003070103201c1c00180080303801148008c44a0043c2c2c009034026404d215107085d950048600140f69030002e810403185840c2d580c5c50140c121007503042c092071815140e0320040000380e03440c4c0000b011030041400305a41e100c83c503459080100032243d4000854005c1050307042d001910398800e104a40380489290f65880c10400302108100c0107a00c09003007280d020001740241d445540315074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 90546376 1250 90545126 90545153
    0xf020f04030b100b070b040209070201020f07060516111005040809040c020a0606090501080c0108061f090806092a130203150f06030105151e070605090d08010302010e100c 75
    0x30b009184083c00c0005144000520680c00b03006200340500c11400071a13561840164080d405480280301561000f0040b802403080d0011b0414a5801169007170900c665948014400c40341070b100b05230b2107405105e0a0303070a80340620000055500c44030320150207141603049603130030512070404142400005c4001400740c80b8801c2203003005078005d03201c410900c01d0600510000f000102c40401195040850803902d482011604505008140c07020486503100c01a901c2d1403400d806064600541503200000c1204405109150881c0300340000700b20103d1000c100d00800300b86807460024100001c102003142800018540c40d40080300303081c0c48140d141c003400254410b03201c8100c0c25421204801c104401c0049003082c1c60b020b40c07814001405a03884003101016008804200710b911036203103041444e03001208034280d484500380411740100f0001c154001500074006a07040d100707050410101224803480920001c2c0c000ba1468110f61994104400c1000c0405003c0c94949802046522840300c2030300d0340b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 90547626 1250 90546376 90546383
    0x1030f0c080a150c0c051009030e04021219020a0c1101030e06090106080f0705090a09080c0d0f110a030c0b07050f0c1501120c0b03060d02040e0a0201081e0103060f020f0403 76
    0x2821045140081c6480307010f142c4e44080c1001261481541c484690320086846892042588c1d5040e11040c0740c098030602d0000c81e0014415503541d0361403d110102c00c181650407100390740021412106016090080d179241401540d04c2d01d180c18080d803141c3c80c48280d41810181410340e18048228100c0040c07008074030030154200007107942443c180d0280d15041d015807a80026070406082440b66564805802c2e0300120307030700000300d0356003903038103084000344078045050b210391142d41d00000d2555013092044418000c962958039600106c40c00c00c41e281c041d01c890003400580b040406400103908100b8881c0c01854503d080c90801a41c0b490a089903440310740c000c0026880b80c0794840703801003420b135114094000ea00d500410b86450340e80300707186520540104042c504021000644036203035591121159134000380301b0300842401c01c81d001d0300c1c0d040d041e0303050340040c1d20701000424004500c1d004149030542e800941c0e03076980c61900c5500061085400f2045e07140d800700b00d500302c03c20284015001030b500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 90548876 1250 90547626 90547643
    0xf0d0f050405071703030105042c0c0f06030603061f08120702041b0c06020c100c030e0106050405090c010c02030106030206281416020f0613030209090102090901030f0c080a 76
    0x4041c01e22a10b40300f801d500544e903101a88642203144007001c400d903030440b003041c0d5000c0b84821580d05030480344060f4050328041461068100d5100703400c001625103c40c50180c881c000c50f508004c0c10b00680b440101c174240e4256001e0804190084020b40a8103210801c403882c0d09003190b22540301c903082640481840900e550701060240030b40c6421b100c3c100c150840756003e03c00f00c04c0c41d0400a0714024800101a003602e9002c5019010b40d08184042c2240d0143d80f0020401c1d08400103016000780b28007020803495619002c00460641400d100e0330303001d003517444d000b08200c09680d4011503c0e18107259080360195250390f000401a143d00010300364401011588038100e1514a207004004051001d60404000781200300c821551301e242d00b1613640c00d1601845414815543c0041904940d2a541c02a0441c4c40003c0b0444a400c40c2d48013282a02e20031110700e10700e603c61150136801e034000c500e00306a11180d95001080000c1c0c000e50800b40f89407003070f00d0840b102a641c9440351f04104d0303a200250780d0602e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 90550126 1250 90548876 90548881
    0x3060705070326010b0d09080a03020309010c0207140609031006080f0d020604030c121e030609060501081e071e08071106131202010605120a0b0c0403170f0d0f05 71
    0x142c003d00341c44044092001070015090030740c142015070200600c40c150403c48009606001c4100c1900026901904020b1030741e41c40d0f900100c014001d600807603507010316510b044030581240d44007291100031a100c018019105034080d20400407145d1243c5803440d4148a0040000036000150240c5001003042c070b40605988000d070000395051403a42c201d24400c40d0458000c01001a400c0b05041c080c89802134004090132003c1201034800203c1c00400b0a008007501001d50345044e8550042401c1e40c0303545400b4400d00d5554001590465400d441841d00151112480000c0a00440b1150ba120b161483e040034408400b0848007110b00841140070009059007040180d05a002903180149220120051a0b9481c211100300d0f2443c00c03c5d1001803410b2401c90420800034800d400513000f4003401400381a200000500241e5a103440101c212402542c0a00007160064488103450880c0d4110514056160001c059514240c0c000c00408801c00ca051000704801c048920445c2c1c00c000700443c1c00903090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 90551376 1250 90550126 90550133
    0x6051003031e14070f020306090a0c060e01020309120304032f090c071b0b040b070b010f0303020717030d1b02010e0d050a030e030904020a02030a030c0531050306070507 74
    0x4128000078480250800380e4510200764085042d00e29110307511500d0b91960000d01d042117842020780300c040d6040c4103460502c10032031400b18a9150192152648280c1c3c80d0340d0f254240c0342c1c200080342980c0543c001740403039605070801603840d20030206480281d070b01d0b058596a0b00050507510303810101130784c2c110103446030010240403241103142d51b0480d1002042d140c000504501e91098032001085d5654092401d14910080c4080b28082c260b620502500c1d50b49501003101c82d0f803c80c003801c1d41c0b20000200005840d000d1505d00f2403e0700e8140c4c0c0581501c50a04407810400c1c006481044a688800c00c01d0016481300351003480e90640003010130031144d80826200a00b540e08001c62084c441d0000c100c5042003e401204440311203259041c04240446072881150071405484000c9420500004500c031a9950110040840c003005031000c10100c00f00031002c65050085114101c4020360055a070b50260030901c00b240171400f11603030b04480464072500443e0600c90117480f00b00204a0129240c01007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 90552626 1250 90551376 90551387
    0x150f0501050f3d0909020304020d150608010507020c13060501080c07031803080a1d010e0d030201090516051503070807051606060f0807050d02030a12051b060f0f0f0105040b0402070605100303 84
    0x1403a15800540c154102500000d07590ac000d4030004080c9403140d45a4a803200e07458000000500503a8000c00c858940a140603440300d181c2c02080b480340061401160f113140c517504c42c1d2130a680041c0d5540c801540d40c445031402e150f00003001030382484194161403c10624900345034000d14410240d060701d86034008030141c4900c1000003074503065850502e102c129039a111030341d1811200111100d400101d080d06083e401800c042c038020303082c0d020b0304d0052260a00c071034003880300f15001565105d0000c8050030030500a4003085d1030b80c10004401c0c50220703008a11820181a09411059514060416540d1030b10111030595110b014600c2c1010700800020405100e4080145001e480007215242540d00081c2c403074111000003404030038807241c18115140f00c0c10540314500c61404001260b6074401c804d0554070581120b140c45403600d413800149402504441260186003007a007010826400d01c420040a00401460769401c140d081c010680072a40c54081c060280d01da103042031001c1419414000c04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 90553876 1250 90552626 90552629
    0x6020901120c090905011706040303020a12050a05010e090607020606011d0d030903060b0301060303020307060c0215090f061308070609030509030312090118050703120e06030103150f0501050f3d09 86
    0x87c076910211388058044400f10315154840d0303145c81c005a444400802c00d441c02240350005403441c13440c0108101032184540d0049041c0c07035006000301d2055540c501031507607414084401c2401600311401241c017070350186100f18400c1031401040f182900201c0041100405180301c15800180e40c048100188045441340902c00d050983c02030000760704548019583c4c0c41011070003000c0d260389070042c00a80d84240501c00440310451500580341c1010052199204025403003140301c2e005410110302a201060043c080260f440f08440c0e0800051340ca9400c001c0007241805d4060003010400c0f440d499505000401c44020010402d052900741500f8203402c48074418028020b50100455a50100d980001d00d081100d912003514180180c00c003104481c02c2e4500642c5c6a08281d001c80048108000b43c03e091111920304502040070f1030417001e01d80291003003882000e400508183c6085840d0403e071122070100c802504038190005121a140701101c0c1d881460a000059050050103106030b0000d800c90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 90555126 1250 90553876 90553889
    0xb0a0507030e210d090305070506010b120c090114160b0603060c1c0b0307060c060507140414030c060a081006020a030e06070f1203020d06081906020901120c09090501 73
    0xb2000740c0000070f40c0e481084201c10880b90030701d0540c64070700c8440000c039802c50070740c0d10040c0300d201d005240c0904950082401101c5600490002007406c00d89801907501001604955002a4440c04000c0b802503102074502410000c0450410341c501c40240001d10b440c008000c540c60301c2d000142024000d05001600140c86504a6000d001c2c044402c1ca0646000d03456184011000c04245081c41e401030002d5045642c05001e01c040000b11107030414200c40f92140256001d1101d0742c0c0342c04049454404002060f07107040c07000c0c07005001c2c840c015401c6a020f440060300320b40e051074032900041c0043c0c102105c0e0030005070102c01007002840c0c2111112340203000900091800e201240c2d809840040003026880c05180c02107601028810a41c2400d040c1e640c100103150740308190f2920050281d40104144000b40c0c1c20020001075003140014909075404410f00002c2400b581c070795070b0300065400000882c0c10007422111100509000d88649030f0844a0394956140d140d1400010710283c50050f400030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 90556376 1250 90555126 90555131
    0x7120e0601030b150a032103050a0902010207090b0604030c030c0303140a02060a11070605040b06010e030f0307060f11040f0501080f090c150d060803130b03010b040e040f06090b0a050703 82
    0x1000015100440e8681003090204c0e08882d80d407412000c81c000007490f13800a82240851803565003098068100001c0f117000c1544c0521141d0749841005042d0756405100a006a0020700108401080755004a6840c0030042420745010b03500e8031503046264280e003040e0f81c1c1e107007401801c00805801440e1000c11001d0181c0c0d00e8142014404041e4588030000d10002100740c8070843c0f85841d40c260b5040307422641c4c0c041c034104a6401c20741031001a481c02100c070a40484c3c0c041d81c10311210704d0001020000489941c005503d05000759a61070090040304002519681e1521440c4c1c031100300070030251015005614a440a0f60301c0d000006080e021b02410b484481c0c8400320903c07030380707800204441946031010345482e1080c0c104400034103010300c105680325503071500e0814042040c031404002440000c1c0101f42064034640c440307543d500c1902c000e01c074042c41074804010802046201b0f80c000d0303a11900988120380807910315210350058038099081107503000301e0b21041101030300c640d10a03a0f400030300d81d1508 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 90557626 1250 90556376 90556379
    0x1d100b03010c0912030507020d05010f050f1306110904140405010506010801050a060305061807020a0308060a0602061812040b07150506030c130609110c06070e0a030602070206070b07120e0601 84
    0x1d400403000740155650101040d1013102410301a0044480c0554050004644140c441c01c00c43c4c000c09080346403641c140e0408000c9040d014204101600a4014107410301403417409603107070070041c10b074035903044000942072000320410354032441500808420a402c3c0c0c0c0382442c02d031030b01d0381c21160024001414001c0e074000612060312541441400c0cae4a07141000a01a2a6040011901002c5405003c424980301c001c120460340e003c11702580c064484d4580c03031019200d2400300440006d19002d100d00603440040002c4584080464654414203554142c6190240340682450b440c1d105811010920100040f5078080203444140800400e001c024108110705198001036100ea40b841c80c03151051011407100c981c414019801072004140480d410458882c80d4100751800350050f0114007098001c0340000b0715003a00908120701960340040441000e00e0850760344c032000717402c1903070140e8120205004c107000040c1654081307402400340da00d50405803045400810103407200b41020000c40d4020500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 90558876 1250 90557626 90557651
    0x108010203011508090a0215041a030402030303040605040c0b0708090901090c0f03051b040320030a0b0f28060305071e03060207050f030307080405010b0a1202040903031d100b0301 79
    0x20190f120243c501c0d26600c1034960078110707864070b012540040d50020307510441901c0d00702c44070000d0048501c40c4100c100401c0440114851502040313038041e4268100300b00003000076003030758000c0d42c0c054031500a24202c5074892101c2c80c9203401c1000d00301c980b02800120359655203040c450b030a004003051601400115401c10008004060300c80991080c0b68030740010031920b40014100f42104011020002d40759075480c02e1884603d03c9134000c0301034024003000924140d0801050346520782d1b40141140c5650307103a071000480d581c00001c0c00c1d0705000e2081700c40d0b00c1c104918203491160540314400003060842c00d42c20007504103101c582c421201c24011030000d01a2418061030700048a8020711700607203030070040c1082400d05001d000c40075a903000000800c0401508800003030b0046008030001c00003d48058280090351110340610b11200342441c0d4030340f00518040d0000442640701e4030380840d40d408130404402d035140140704031a54035000f20a480d200b01086124a003101ca8080b0f00a001200c42441e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 90560126 1250 90558876 90558899
    0x3020c06010509041a150d03091a040e01030b09100606030504110a0f090f0e0316140109020a1806080106080d02011b08060d0501020903100501031407080d0e041e14010801020301 78
    0x1554024801c1189002800c600040295a1001c40c001f42c0842d5018a40b45402003150000d405405124020140900002891101581c06075030540201281e96402e40d10f40052511b002080445644580641160078610300e0003001e00421707154602040d03038100391030828081a00e840646001c1c912425042012258083e00d450407200e1300d00000031150010208500509040c1c8400c240c1031000080310424007101254408001e070003818210492081030040500740c13125500041e501507034003030003403081241d0000c020150b0345407100000380b00c5540e50206d07425600d456100340600d80216400d00b600c0781e028007410442030100da602e01512840440c0141041001801007805000640c40c0e030410001e00354122580a032004080301c01c1c0d0120074514030050b20090104450345520100402401c0b200003860f0015120313040003408d240c0340300e100200d0f21903041c2008160f0058992043c40d909500841159001150b00e05012070041c494050b07000d04582c069200840707507841000100216981d0300b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 90561376 1250 90560126 90560153
    0x2100f0e010e0312041502060907030c0614091002010f1805120f040305070e04060f050f0402060d0b090903090901061103030408030711030c0c0f030a15020306041b03020c0601050904 80
    0x2400c1030b08095818601003890440c10001c0003404110005010a0100a14010812103506030b422030f03002c0e60360740c58640d8441602d03101c001d08082d510003042c0100390107551003103110710454035640d0400802e200081d490300b4065400f4030150355201e00d07156140841d03009800040b02d802c410000d18422960350160380768400811441d001c48080360211041e03240d0401c0750000e541010884001d00d03100e00e20900780c1101030360111101b603d014103014034801c1c05c2c000c00713125440284207d485a0f5540d000d00a00d41e2003c11581425a82c8802e400000e0741e5085001d402000e00c20001e51300c420106061109104060b00603105010800224010342600001126032040d44045400d450b46c0320220156215500401c001d440c902011413414038101d00090300600090049681c2c4012921130802e160b100e103080760380540302c0d50101518420311340d4150015500444003510000350b0150041c3d00c03400040109104600084d0005110340e0f4400040106a000d050100d0743d840c01428103941c0c003210030080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 90562626 1250 90561376 90561379
    0x1e0901050418081306020d0816080702030c0f03030613050105030601030f030203040e09030c06011a0414030c1801030b06010201050c07020405093c190f0804050d08030402100f0e 78
    0x15411150618201e4882c1e540c040350f80080380e2900e0b00c03003403110880c050300b150042c14010300c1a1045001040d204142c1c041c024042c0c9045002c83c20f124800440d9250340041c0303000c09603c010000031a0b0391004009042d410850f038006542c803030914030208172443c880d11040b22807203414000144416a0301060450440360300c400c0030380040c0030318030301a400c5010355408062001c88a9041100c0302c03601000810304600420181c884907031301c4194805102d40b40c03404203140c480b01488140500e4694002c1544023020080841e032026854600044000840450303190300114804010800c01500851458000d0000d00090100e4503040c0e494501e140580030001e44a245c0340c8010501416041c818814900b840182102d2500c41a450481d100c418a034184001403090403161382c8602000b0540010f500c203401000664114184c5036200c0303c16800d10281e44040301008002038a540f807205030f8a101d486601e1103a240c4c83d140c01044000901c0c10240f00610550b04034074081c4541c480c41c0350542410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 90563876 1250 90562626 90562631
    0x1209140a05181306050a050105031501060f0e01020106090510060f020c0303070f020f09010306020901020f010e03040b0a050f040f030201030f0b09010e0903070204140f01050102120307200307111e09010504 90
    0x303c1c0090034100c8002072034003814680c034003824002c6240c0c4903000181601c5064049980c43c202e503020360800c00741d09114103030004100405140c949480780145c007070341c400144008078669403502c031804221042580d04046802c040034040000a42114913000442d00703d0010b005000314030b1000c00d0b1603102d03040000b40f60007900440b0300215641c0800141c44410044c010389400d60710703442c0800080d400480c44502504c1010800d051a150500071007020050710380103142020f1410103103110701d0b001952441d040c0311007444070b0398862100d10301500040000c007040c1401c079840d5000140c02c980c600d020080400c4e04004000d0040d841d407504460444003a5803041c0c5556031500d00e031a007140200352000350303c80c0c01c041a40c02070850b203d800e240201036545103001640d90f00c000583e910064040d1103141140b0a000040000303004241c003810034554480c0132083c3c1100051b0301070442d40080c2c000c03248100f625400d000c85082500c1c0003804c484410100c10000307441c40001540300307941482480e21a64 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 90565126 1250 90563876 90563881
    0x10091d0601090905040506010e010b040f0302100c14060601031a1c140a1113020406020607081312020303040501051b071403040504060b030901050603010b0a0618031209140a0518 78
    0xd10072010740e0b005003c0898108207905052500e1500c40c0800e01c16540c030540d2600003c11980380741e13411a021901d00c4218600b41515503805e00c521440c0120203c010300c0b81582124000c114404504410000e121010b0100c078130b4004005000c0740e2403141c1100d040200e074603514100b52a880c5078080303001244128203509120134030b004040d12a0b8428014014040e000307501d0300f0032894a16580840700d08842c004200712200b4480000c030700a5100d000c00590140c2c01240390136010b50a035030b403c013140400c0000d6074403990f261032601c4c0300c044801c8801a03000100700020700c0f0080c400c4c181c10420165000440420714482c1074442c2c000c2a00c0546511512191111000c41c100f0854000b004082c00501c51140d032044110099002180c0ca00030650801002800c1d030701e410302c210100d00034010306a2458608202080f0707400c1600c090700c2c00b1070f007400110200215504500000042846030382c0c2e0f0030b00c0c90900c9010300f101116040800d018180100d010701090362502d050a1101d032949001d1503840c4e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 90566376 1250 90565126 90565129
    0x1260c1b031e0a1d040e0106080d030f02190c05030c0303010b0705010b041104090f020904150302011b0b04061a1e01030b0916050307020a0f030201050a1103040c03110f03160510091d06 81
    0x4c3c9000c0d411002c40c7d602c0c10303100181103080031603000c41c2d070001c80e10200080c018490410046e072040034400702171841144025a01c85000d029441101d6002d03804813420302586110341451548282c0000d01212030200c1c8550421000740505003214000351070622002c6903000c4038149a0040c0e000c0c1d004195103c0700d5040c04c40c119030b419581001c400502c288200c141040c0d00200c001d0850005030b0005550103116011100d0f2311440d0070381e6a91003074104e00c0541c1d807500e035100148852042d0100e9003c4a2207480c0807641d03000c0311881c5880b0f403400c02000c550010700016044521580045000d99044010065105020305c420303c1220541e00b401c80c1e80355981c0d202241004006c040091115964800c07060505905600c8036124403612102004020a40400d001d00e41c0011031b00240701d1010a4024400038000c1003030103035000030140c810170411056a00090074011074411015500f00100020400c80c9403655103100003644c5406c0480c00e640c03c0560369141d102d214600c001d0030b8201c403000319000c0e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 90567626 1250 90566376 90566381
    0x1050609180a020f121608060f070c080d0212150307090603030203030408090a0e090d020105073b0d0506040204051506070b040201180605031501260c1b031e0a1d04 72
    0x82007040c00e842940c500014000e0144200b40146c2c0c00718428600050091203031b00e409d07280039920782e488a050107081c641e038a40c0d03164004c0c0f01c40d030303d0181c003407050f24113882e4040c2886001d001c603081c00b04603503400300d800d040c82c0106580c41056250b04221041000c65008411a90031503041400d2507925070028000c00c2520000d5171244262035050000c0000309440400c003420b00384401d40c001d000c1ca4582c01e80c00c84031103480f0303400002021044004075034a0294503100056038200540061900ca12074000515103804030030060f289074205408202c03c6241902c90103600c0302c0f0381c9a00314058000c103004039215010381d400081481e055000414107582c01120400a0171401740605000c094440c403000f00503130001e90f05084440035480d441c04241d07015081c80f52400001d140e11072410340900056180c4a03402800368280a04100801240c0024000e00401c0c01d02401006607034444540d000501411a030000040c0107200a004000d1000d500c074021400c800707400d1002800b03665074a00008d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 90568876 1250 90567626 90567649
    0x309070e070c0c050301051006031e05090a06060b0a14032e030318030b0a0f0612031106010e040506010b0901022506020c090c03131502040801050609180a020f 70
    0x20100c0648042102071684103810040035442000008403403603960003894241c42080da0f403108031025008061008901c00c0d84039035280c112026900b80c4c9004c5490f0082d0448009031192415038001144840c01e1110070300500300144404102c0302d180c1014548010844c072180c1d07401903e0f1501c004041a000e0300749200c88501081d150004074501480c4e401080d106400300c0c84101c004c100083c61f404009109407454500300c82c0c10860700c5589070346800c03000303005241e0500b200101a9441402182c501c02170050b00c9001d81c841e0b26810b800300c4d54003900078a0100c0584c040e15a5031500710070400041c0e000b2a499044580c0c043c1c3c00ca40700c01e01c1e14010b0741490408940c00c8110450101410018414a070424049030819001c0d02c0e941c1c2810000e0042c5480f04070340b800c50440d41000455490060302801d401d0403402000c0103049003005a094009981c002d6100701c03401e039192024841245400b44000350098880510b000e1a110042c000a48440c06460043d02c640c211606c180400d4948514220 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 90570126 1250 90568876 90568889
    0x311090603070c0305040e10050a0909050606191a03040318081b0d0206031e0a0e0312180609150a0b0d0320070602100c0e030a0b10030c06020d030e0c011202030907 72
    0x7e12858030b00c4030792031880f2061152318400d8610750800501040288105800c094001c400b600082c0c0ea00c80501c071105240195003200e00c105014005002c80c0348020500341040000743c860340e070782080e0500400c004881c1c121410010071805003040310400002e4018203440c6089003044442c40104009610b080f0881c00107034100380000204a02186500c00000c010b00d0503614800d030340d0300c2e59904641120b202c1002d43c0795a50040110403200c9008034212548480d1042054070300344040300e0f20606201d000e94111400b54400e0f00c05c55000440d44100341c0e03004504040030000a0300000014845801c2114003400b03001c0b80d0486500000050307201604401003400480e211259202c1000390740e2040005202202494110b48080c03051141540041d4544014000c142c4907000780c0f5595000800500b00803407410410034004009829904407000038101c5801500d49240e0f8154064140ea10008d10400c283d00302510030441a03030002c610091030144113200584070b940390010726103008480e41065 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 90571376 1250 90570126 90570149
    0x303041a0405061c0c0509060702040b04230106020c01181509051e03060c13060f02010902090a0507020f0706020706180b0301080d090f05180601030b0a03120311090603070c030504 79
    0x48845004030404a540804c090f1003000b00e02420a01240d907801101102d95200e441001441d0151034030f604031441080c0010400512811b080f03801c2c0750300502a148083c25410000300400125405018504507a41d00f800c0003507003883c102c110004440c071b4a00079422400c0b00c080350085500d1180304c02c80003402d0080e10f00c40d4084910790400410302e0114200b68070038407c200004041840301410713101c03e00040c0c0d2000000030308000003075428444040d43c40086650300c442c02000350342c1c0c1040c61801740412100001e0342d42400140203082101c5041086166800342d041045000d90010705101102c81d58a404006840a0ba100314100030290b0b121500c4104080300100d88480045000b00707886040d80c8a809145540b4805081800614400c495000040e414800030100c0100405a8098414900000c0c4000c0e04000200301900d1a0420f5800000c61901c5d03104290300740c40380b0209107400d9040a8105603803c8000368061200500d010100042000318004240c0642c0943d0040c000307180ca503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 90572626 1250 90571376 90571387
    0x3010b070b04060e0d031e1a040b270a050115020a0209061518040501080d0c0201050702010507020904030809060c042102060c030d0515043c1d06090c0303041a040506 73
    0x200a03114069802000e950f81c60784580c0203030428422400421250f44a14280501d0307031040000814101c070400c0c2d000004a02012f042d6040101b403507211101c2d10742024003c1c01c00c0314001e8202c13034050b0049602100004401c02409400080c03c514644d41110301078030a94820001c03505100220034805850740010401101c0202041c00001c00d004050b20204000daa0701c440700d5075034503090b66040b40400d5182d01a0301c00b5501c10740041135064018103200d894800244d01080f00000200c030207800140340c410911058210074890700d40c008036840c0b03040741800d0429010003900701105598180080c000d0100c01c0464803400b0544040340c040c801a070fa03c1d00c4d10059104081c0c101111011a508480045641ea0b03250a12902e01c2c0154080600714020490040100b202c4c0da4044c0c0c000c603120101c0f04040003514a901403e082000d00c0b00c101580e03440d01c004400e140540142c10000180c010b500141d1054130008195000c44041c0c800c44c1b032981c4c5c1b205c00801160b118075005242c101000050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 90573876 1250 90572626 90572653
    0x20904240f060302030d0206190f02090604031202100225020d0204090f12090303051911060703140603011b080a1808070b1005030d0c0606050604030606051503010b070b04060e 77
    0x1100b41140d0095080c5e400d4984800c004030f80322a41110300e40c4003000142c011002141c0254040440c03a54551030043c42d200c0c15100103045038005610480b1050345c0001044911603042c041914070f4185a075041d0f081900d020041d0240109402e080d1240a00b190400c8041d551403550b259410f03600500200301c0080d00b82052101850014026681c50b004a405c90703030795520500d41282182d400d5990117081004801404210481300f0401c0c0301009a008401200140e00f401068001c0803151000543e100760804000142500106554801e92420300e401d640821005e45201c0e1b40107851910394090b13921060110300400162040031500640501040f0070400326200a040da81d0003150300030315590b1001140c1d10300341441c2c0181034041e080014407031302490040950003096031184101003040c43d140e1002c00c3c8543c01030740c02680c03400d8440d40704001c1410304000409041c000071110601d15810b00b0717842e1413144176940b001412442500002010300681e5400348103052480d40c2551128000e00e02c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 90575126 1250 90573876 90573881
    0xa180605031b030309040e0a0c0905100504020f091009120503030403080a09020a05010513080f0c100809030a1d2806090305070314070b030711150103020904240f 71
    0x102806032040c20108900b820381c04070815070200c07000b001076280100140500010f4020300b01417091520038081d02c2800035500c031850390060701d102000041c003854018405080142d55500c654043c5d48104001d0000004050440f00c1c03d8405482460200000d04821030300309140e41d00c121040003004282da0104100170004600483c041c0c0d6500580380c85640c149001c0780d1000703900a6015060840400548d4060b01c05042c0748440c285142e00a0b5960341203c41c1800660a0b16241c5904051320645072450080d0360700030101c905243c04402894440380f0300c1e59038420b042d0424240100704040280f80d2213003048848811001501c0e6103025603144401c080c26034600807104922200110340810070314840d950000c2140e070054018a07900e480c544800802541c500c03a084000e01407075101140040c070b135000071401030482e83d81d034840500384a101c50382031500140031941440785000040000d640c4520502c0d0304590000b07590300703406000d00c042042841802c0c0184101300d06080300c810302c5c036142c0d0b07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 90576376 1250 90575126 90575129
    0xc0307050c01050309060f04081306180b03040b22080a0513140a031b05030109030f02060f1303030b0f04050c0403021c0f0b07032007140706090902090a1806 69
    0x100100c03641c5154440040d00c0d280022a101c450b030340e0200e000100075803101076101da0403d0054910619004030b803581502200c2150b0003010200d40f008a813136902d001c031500000e00608100b50308a085061642c0e076098107000c094102e490101000c01c090300701c502401101c281c03d0345d000c1c80ca60394604007024050b08a41000003004049608031200048003010381440c00d0024100504a8141c3da0843d9100804421600b00c14030240101640224441d1000d104049455000b80c940818020946000a1a0200051103d410ba180720f2003800340d1044961200c040b61541410085500b1408902207602005c0d52108640d0082c02d2005004000003003100602c2603a000341e492883e5450444150034a1240f104401071100140e4050800030400d40c07400103801100328500405e115590b03610843c080012003a0641c540540002c16001700041d000d03568172010342175130182c002607150120107065540548541c0b28521b4002490740c0166551040c9078001d00310031005484c3c003060301d00803000184100d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 90577626 1250 90576376 90576383
    0x7200a1d0610081f15020a0210030e07170a060c080106030b0603041208090304170303100e040209040201180f12030e010206130f060b09180c01050906031512030c0307 73
    0x4034008101c403820868001c80c00030819840d1828203850b000f949034214604502262442c0a080c030001c203040c510071100c4070240006030300038038000c0c2550041115031104070503500c041c145440d80351041500c0c00b080070b01c100d0343d0703401a00201c07042240c00c140c01c1146030381000301024540605150b220390001043ca060326a9503400300b01c0342c1c2828081c01014030098070702030404a001580360050900c1103600d41c1d400400070080e0b07400d040c2d695081c141070500300300070100c0c0b54001104201986150701c054000074480b011407060503080c87e402080d00342c00041c00c0641040303d08201d004129a9901c0c00500900c0c644607022056683d41c1c1003400500c5540700101e00254400800f03a0b82da40c80025030328000c00706c1e602440d010310500e070358a102a1030f0a080403202e0680b1200c8c0394100f9a522980306202e416112160100c010707902c005607042c000103015582c1031120a100c404440d171602c2c0140d0354000c0c800b00c0c03905824201c450010303040808131411b01d103a9210006400003100340200c0a08840d174030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 90578876 1250 90577626 90577679
    0x10e0f1f0f0513090506030703051902130515090603010605100c0b01080309010801090b150a050702090a110a0c06090b07020708060601050405060f07030c15020c2107200a 75
    0x1d8810085800b803044045041c901480901e090100c000075900164000d64001c1c1203515036552642d54a00381844150462241c1090518050a6041c01030020301e0102e5044401c11803803401c1201d8031810251602070314040e148007000207076161025403011019040091056041800c4003070014000300c60340908880040300c03a0000203020800100f81c0e40303040304c1615410000d030b0814070184010005400159401000e01d80d4000e4100f00030300080000036603555840342d0303400742d40c010b03c40d007404c003d4042c07007041e850a810040c071101c0980c240c855601503841c1c1212036107100d0900101074501c034900900f03004054014040c80c250005504170445440b042501c007980e94441c0103490324002c03440b440380c1140040009229043d070040c02450540e1103414441417584c0b0544a03000304d503480c442c1c218007190f4001040c000c0c00008011824084143d112901c0560790700071107481c121301030f1800081c2000f1100d05401101c210f10040340c803074204040c0074400070316600c1c4121645011007062480c011304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 90580126 1250 90578876 90578897
    0x21305040b0303070210140403060203010b07051b0604090e0a0b0f09061f060c080d0614040e0309130b01090e090106030309080606030703031103090301060801060602061311010e0f1f 80
    0xc003c0282e4403015001401c4510401d4005403d542900140340d401d080103008000110014400744051800b820705400c055840b80418908945401114036103a25507907511080d0422315074807482101e0070b80e03c0780003000c64000e00780d241035858400f2108006083d02d170003404002d00210300d66031992188100400b110b80340c3d21170000404800752010304000080c620100180206800346035082c0300301d40728028491400716020723951340441b8170a810040408648800707105451810340138080c485c02114010314039003c5940d000443c054800818004c00903150b00001d00c2580c003455404005200c280c004540c0703032130040c00d02c90082420740411404108803c502140c0210005000c5108840240c020300040341180c40075640e500e24000c40200500c070800060ba23041d02c0030702500005000c0f8400101d030403410701c20041e0800c04002d1402c1c0c5080145215503011030111123116a0b102800c0c2000f24910704204042865580d0005610b500084ad040318005900c00005005540c0301d0a595041c0c040c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 90581376 1250 90580126 90580129
    0x61909080c031e030705070206031e07020a03020115050112090f0b0403030204030606170c0420040803030411010816230f0a030501090b030a030e180106120e01060b030a0519021305040b 81
    0x1801305981c164005001880880b0042c2001d070700464002480c50061000360000800001c403400c1e04035281d00041c1c000c401200308064090061000f20329405441d2000a8141400200440000030014041039141d05142090000c0c2044500700c0c00e41200c2c085000785401d05020b00a5402880100d41c0146011070000b50b602a0440317024010385844054190240c00000300030140c49510041464440280315090303210f886040200300501500c1c0240d0b80368901410039001c4c41c0170034100390741404002010081d083c50b5408041d400c00001c0d041c011001002000710422032002c401810010500c00a1032142d500a013501a10000829540c00d0000307031f890300c03100e90039110f50044650701035000200c882c0c00640501c42c9045103190103041c440244a06040003520007600380d2200c00804d103030200ca0424014a40261411442171200030f100e15494003480c000280b1009090030951562113020a0f050220a45510040e006002c0c017076468103d0000342002e4028035200e81071240c3c2c50400d007442e09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 90582626 1250 90581376 90581437
    0x806040c051914041b0c02090109060f1a090d080702040c020a080f0d110304030504050a0b0405030616050d060b0307200a0303090816060b0a1205061909080c03 70
    0x2010a002c070708400c1c9031070580d000c468030511001c4654040e4503000c0803421a20000d83da1310003500140c0c0c441e24100707081d0060040620060f00720060041c14404140540034080344041c0480300311868070112010381e8207000c6158010a82c2c01da9214102140782e0081c80441d9014000c6140201c8041101508600c0c05a94444c038883c001006540140021189681700c0340240c0405c010a89010500440003c14110281c1c000c5408401040700403a06200c00c1c10086070010203031400c18451440c00f81040002507640d40000d100b07071200c0014000040540340f10f0070a40f41c82d15420320051019903241c03091500160022143c602c00100b4034041c1403000203640d04c0d0403907011440400782c107031150aa18102c02400c900002602ca002d03003004801c0b441400c100003494601d0280034009000c0b44444100041c448440d4011100301c40141d20000100300f0106105030881c0b0176140a4034103c1d0078002c0440546407104008d02200408200140380303034404001000740a00d0641c041e62500c0048001114 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 90583876 1250 90582626 90582649
    0x30210050d2409020901022a0d060e010e0708060a0b010306080609070810020f040e100506070609050111030405031603021906050a050a060b041a09040516080705090d020607080d060806040c05 84
    0x5030b210f90f240c00002c6900441d1030074843c0301c40100003231288150000c00c05a20703129404a0f030281c1e030313a2520b0014000a120385801c2113241070140c072100b071401c0c46040d80d4110140c504070007a43e445c024004240e000e170b40280014400c0f04140d440b039140040c505500c070840b520a85449009040d806010603455100310b5004c04179803c03c40e400d190030402d52100034000101108110202020f000c43c00c1c0e034070309000d80061031142002081114103803822a003524094016110b02520500c140000a80c2c08400c0e50040342d004050310b20240f010f41000c911702003025018240c00c400101d4401d0501110b43c100341e00c5214014030510040e169400c1c200c04035038042c410400150414070051107040c2645094000002c10a2a0306040070400300000c1d0844100707403242500e043c0140c0300110040d410a5805502402c182001420302d03d00c2c00c0481c031003c5001400034071a4000040c2e18007000400020380b0301c1100d60820070450b00340c6411240b541c424050318103a85941d50141c0c00241071030036506192 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 90585126 1250 90583876 90583879
    0x10b0907030516050c01110c0d0f0206060d0b0a0f0c030e1c0206041e12030c17040503030106031107050a0f1703010b0f070206071506050f0f0a030210050d24090209 72
    0x3841c407404203d040f9155000901171103c80d548415002c80c001500724041c12844801c03c024003001c01c1300b0b91016002000610040040d900810200f046941e12076200003800c5400c1a0210210ba4030700b11448020300c000740d43c0b0440784e40380c00244104154103034400e80e5211006001c4500c5030041c068a00000103d0700c560301c00503802140060001a03141500401296038110030100c080700d0380c0c0e039860901080300b0280c40040c0d0341e14041101d00e135216851041a001c00c51140350b150526450359500c03884140a40c8040c1515190060703411034030304c2d08940c00c00340c1100c240d90600050f440e01444401e00c182d010b0324800f46645102445640402c1141c1c101e070b19408103d89000085a500c10080c3c000a40c1681d0084042c03207131001040b141080515842034000e4000750301ca007044200890144109000b034000e9000020341001a00e030380806105070303a0121507404500710f00c81801c0b5850301c21962000102400e0005403562084508002560b030748aa8070700c0402c040e16031191800701c2c0600205039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 90586376 1250 90585126 90585151
    0x608011419200a03090b01151403070e15030108010b01180504090c0e090601050907030c170c090607060203010303080c0c0d120f0c0c140d09090e07050a0305010b09070305 75
    0xa001815071580b0580340300040c298040c520034140548a00d440d00811401c3c004241c84482000030000103120380c1c1d014005c4031031003445910241e0002482c1c07020440140d0a0a02e001000c6090640560740541c1000320003029847d010720000d003101d409800078070614140b982031000500704c66005050100000c0031034071610300c0d11841c00c4108006000c16002c140c03900103032120003140e00a9440030040c81000e0300401050194580018440407290040c00030042519020b0402c00c11540a041000754101c0221503142688464001e0700c210320030f1a580c1035100d04009500c00401000740c0155040740e000303132114a003070742c0c40300740c051028032452050702c9840e006046003901c150b028490310845141006400a1806480b00000040300c284c03c00f08800b00f841c3c40d40f2481003040040d16004030302503840c003130213200a4642018040b90400e02403020025140d00100c4241d1394100312003001024024440d14030141e8030b00b040de0081001e0081b080c02021001c00080d6814040d0054900071400310412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 90587626 1250 90586376 90586411
    0x1020c1e01091e020a05100201090c0608072f03071203050f010e0106030905010e071d0a020c120a0c0f0609030e030a031b0f050105070f0f0806010c02010518030105010906080114 78
    0x34a104104140780417a40002c54800104682c2c540011041c4031490940000503108214240384048202650100302080404802c00c01d03880d900c0b6000720074000041f104081400728010040c0d06030010903000b40d40c0362001080c00000d1184200d500725480b01d442e2800c001a4407043d02da040412402d0064008264100c8010412030f44139521012815000c0e100000740201e03118070301c6d41825400d078015944000c1d0410350078003a1b071451204640044074103104510305041c845840e41c85090440c41340c2900c0c03001150a40c0f0903401044054801d0782d014105106500152400c40c00910304d824080d0000b610f00c0c56009660709000a617020090741684030441e440c150682641d10310303890300c00100d807102c04200900700003c10074081c4500a1405442d81d0810000404001380b9a0044100303d404010040042c000d0698000c0312502501c0d0302860003035503c00c44640203001440b642001180c0541c6040000607a820042c0e118009039030740360700240183c0800201d4405c0040d01510038020884183c4c18 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 90588876 1250 90587626 90587663
    0x6100b070203030d0525110709090c09050f010906090c0804080307230c160e010302090721050106020f0309090c07050a17070203100501081504031101020c1e0109 71
    0x10386242440141200d141164800440d415a40c090742c41e03102c3d8030300c10503586500c0421002581076211152803d083c0904200c44403940c0e490a51240403019030f640e0764484c040c00f801c40840740241010b2078003030010341040d005252600009114407613005103883c002203150000341c040d0003440c448540e00c0703501b5601c5036129141d803640090515400d00501d80000d81461a02d00780b9000c0b030030010341c0101c0c1c44a0341100c07158100040310300e031005078614015043c0f120541181d00641035070340541d07841d04551b8a4150a403540d6801d40c1c030b485076030764040c89010000c9003150055816500c8175405d49808071000c4000c075549019040d8842d82c0301c400013000442e0101c807400507086442c02034007120f01d40085070301c5440121416000040c1400c100103403e40542c242002145610103028808000c0c41d07140020241d11740b9100c556410b05082c000380410103240c8209441c0c02d1104044c6c0c001c56840402c2082d05a079507080d801682e071404107034103aa8010350018400c1c00a1030740c00004141c4c154140c0070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 90590126 1250 90588876 90588899
    0x60d0312050a0b03100623150c01020d1d0c09070509090402030304050409030c0303061d0c0901020a0b011d09010b010203040302190b030a090203060a06080d03200a1707020610 77
    0x520710010030b696100b00c003c45903410803141a100388070b004006400d074140080b000b00000c00700c1c882510b0740e1401640280c1034544901c40896a40c080a01949501070036182c103002e4420b10f950b03805c1450130000e04c0310014240d800380710b0b030701400542142c003d8099142031008030102140c07003501140041c4907001e95810009005a40540700405480c85d11780c82d100041c5c12100603e038194000f642c5d0b001d13400c080603090b100e0700000d071118019901625280e0074003250300340c40c024511740314010040b4110b1220b034002c0003460000c59200781151030035070311101400409508907484040c920400c3c40400da171440c0610824020400c1a4003842c035041c1543c0034040d1800403207014016502c1c200d0f10010300b680511018501038600e010010412404c580109498440c4c00b43c1203100e05461b021082110351000500e900740c1a2075410007068041160f011130b040c4003842c50b0466506d40d400501640400c1e4891600000040040c0100741070f5101e030780c0d049030340380c200700d59600d41c030f80300850b05004411600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 90591376 1250 90590126 90590131
    0x9060609070e010c020402070506010e0a020c030301050418061b0e0d050c09190e0a0c231e030708030a0f020609060106050f09030a03020109030305070e060706090206161208060d031205 81
    0x6042001340403940e94089402c0707a12081c2c041d00c2d00d800100060181400300ca01854025041140039802c100d00460400e07124401031041c5e5200310340e80c09400b0304801c0e0003c10b0740942600154200070f001c0d0302c1c44000d0b400b11400c80d44d11000a2001d41e9600f0140f409899401200e50414018182c09004806016840c00c0c09041010416680400c14030040081e000719801c6001c03100107060900d07107501d0034500c4455640c2101001c11074031300614919441749120410354503002c85a0b8545131840c6000c1c2a084010002415054040d0750740106110308000024050000c07181c0d1010391050f0f88100480e202ca109451880c0030740c20820040010301d120304003612802115120113840d03d5006000645071030702d00b002c12400b50b5190050441816094454039500110351304055070b10f00104400200e161140d82c40c010002036a0311900029900d80320240c13000c1c910104140b07124103513142000800c82042d40d101d0313000a800000055140c0c109421881201581030711510340110300220008080d0600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 90592626 1250 90591376 90591379
    0xb04180209181608060a0c0e040b0103021908061309081e300114030d261312030605060d0207030c02090a0c09240c060609020301030b06030609060609070e 68
    0x1c80b880d01c029407018003024400300f5001005150f0585420f09503410300c20020301c000704880c500340030440394680112421300d11050440e000604e06801100680080c080c4c040360040d18590002d07100d01240d004926140030b01000c8843e030000060b08000c0d24152260801c00404042c004c0c01082d6401c0c03020458035120388219000513042c604001d40c031030800700b20002004003846e84140d88100c403e001c510502d003d01091700e5aa1030201404021961310800c8507401c00410402080d01400d00e04501e00c2c0a01ca00f026010820072800e0542c0460b00b45d99000400781e0300201440001c1c0c01c0c40740203109600840c4d1020b000d030350034031400a40d620020341002c842034003070001a03041c080040ea10028014411580854000352030312521800912000c401d401c102403400300d9000f01000494401141110b03070076540303844540c0c40f245e80f42c0500988455400b03035071850f0002c00040100f0581800592107a074058089850075615502c6481d0307514016500070f078028111102040401e8803400000f07070103a90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 90593876 1250 90592626 90592651
    0x9060d0609020d0207030809010501081902031c020606011b0b06090903091201020d150308041a0f071214070c03081602030f06010306141009021608070b01030203010b04180209 77
    0x3903411000c420ba0780075003200260951300180700c90400d904503540319044039104008002d198107058485603100e50b01406050621840380441c81159000c00409200321100e5074000c0141d41c1c000006591a48140e0701207001c0740010341d25101c455000e15034400b0032500801c080b03040d0740f03a403400d0200401e00a06180010700041100d40490b450300540c1d982c6850080c0d000503a580743c00c1242400300da030b0320600172181032015201000070038011030940f0240d0b0072500c015030f1140c1580392030003824481ca140c041e01503540401e405082c01001c141e164500347e20354a80f0501195100071024191142c4800144001c504e00003d10209030040007400300e00c4510f40a8080e545000d800081c0303031442110000916a00c180014810082d00c2e0082400017800000c500c01da50130459041103001c81c80c1d00034096001d60110324915002500001a00f005800c844090395908460030b10130030080d02400103074060344c01c0540780881c500781407080c80e80200d4082c41e00801c801da01d50811045942c0079108940f00b50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 90595126 1250 90593876 90593879
    0x180f0a02070c1e09180206310b0909010b0a080406090213060902130b091806030a02091311060c0c040b04090b012403020f04090e0f03030702010606080c070809060d06 73
    0x10041002e4048002c020150a08280c0c505100c21003525004d448174008102e20460b034400580343d0009648078616101c0410501701c00c0780840841031521003007640c002c0c1d8185140001c040c12901c00a010042e03094680a020f42e0300c6075408141481103d42020005200c00006008240c00e40e10000c1d20307034802002481c2e58000040782e042900d241d0340144c01d05a600040e2028881001205030000300a200c2c556401c1001c1040000c1180d03103402c60300e0307143c00b145200140030340e5400c0c04104074407035000b000b2901e00d041c648000c0400500c008000c50b14080e00c911072007a503203002000d4619180315a00100840e403290030170b0101800006005641140c0c031016031b04001808074203118080c1640703442080c00801c2203038845a800070310036950b5041c9441040003030b0b54a060041180d00b40d4aa5a00219260034903480c02031526a0b01303940c0c84c040d40070200134403003c03a9040d004a0101c2c0c81aa580e000c0c2d50326411001c429520a001d8010401e000400c94402c3d641071640150000c0c4c041400c000a409 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 90596376 1250 90595126 90595139
    0x3110315070f180302010503011802040f0608070e0301150911040e15030d0503040f06020702030f0607050a090e060303041e0f0602010c0305010b070f021e0d0c05180f0a02070c 77
    0x326400d845071030108880400545029a000c90b00140c00c503005501400443e1850300003070420310042c003c1d0689540481c0130807285100743c0d012200203100318407056000980d10780000f0464642542d000d40003590030040180149414040c401840d0300391080c04000c245894640c40050400c1d40180c1c0c60303580b00b031200040c0b46040e115014865901160544410410f8800301414000c0b0641c5c140b0600c0000c5c01408042403030500c0300d1441070740c0000c00598030076231800040c1c900801800c502e5051700c20340f000c0007030417581311018119030300094031030144c2a0388803020b4101d0a482140c825030558000d00c070401a4030300c42d0190b000c0e0304003000040341c0c0340ca03201c1042140c5680f0b03e411840140c0e4644d014501d000342c0c94401c07a8018802d46d265541848d143c1c5e59842050000c1c018080d100c1c0070074000054105106185070002e0301d00080540090164501d40351003010740c3ca100b0644104161540981c1903607450080510445600e00c0d9000c0c183e83e07200e060701c000d411802007599071040c4800301040c403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 90597626 1250 90596376 90596413
    0x30e0105093417070602030a020a020d240b0a0f0305120307140d06081603030f03050702010f0e060121030c140c0a240201020406050412020d0b1806060d0c031103 71
    0x1e040f0b6821600241c80c2c1080a00740741001d00d900910855204000c06070826a002c00d14003420782e4110380340d00c0305c3c1c0400d0034409515400340380410f14442180403441840c04195100d0722500009541e44403107142e5422407200d10a099110180c45a0082406440400462401198071040c0e0b818000c0b20800740d1003c550594101c54004070546945110910400c0c40400019001800b04454100c940e0708560307000300000e802181c0002859101c0d000303d00c0e0a4000c1d00070110085181c0010094500041c22069980d4820300c0340303070f10095900f031009080e00c40d805141785c02d01d40c25444002180880f9590380a142a41d00d038219500c6c0240755545071155640d1000c0c1004004060501c00d08040c41d50119004410603200803041d61700c100400c01ca865000340c103131400c45d00000d6059041c082c260021034605580d040300200851a498100401001086507081034072031104100d8140303603541028001c1a182c4c600e009402d103e048441000001c101d449280f07501900981038800161215054658 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 90598876 1250 90597626 90597629
    0x50c190c0501140106050909070e03010213060905040501050d0813030506101d01081c02010209100207031502040f090908070506040605010512010203010e0112080c100b01030e01050934 81
    0xd1040e80306141407090074000d01054690a0080103076551500d0701c0603283d0321810303076154080d40c10740c000a2200f5010358448180c400c800b81c003d5680e00043c02a08014403040e0054001040441d0b6020a40d070500303105050507240b0183c80c608488150381c40d1005250881c0480c02220b801060b400700020b6428170800340031340d00040c82000030741d0802c1d487c071800c2c48411482d030944030804401000050000903103485110004190300100301c0c08158101d002e4400e0440351170f0440b9011034400c030b001c0e500203a8402207a000b03c45500082020384800c0c01031788035130303c03d030080c1c182c6c040800d1203803039001d522503004c8030b1091404500e0900d80355a41c0b41418021a0117540e0b1960340c10041040d420600103071450210b2020086142d036042850144007500c06015008185880071030240c00c004a000480d480512142c007164000804101c0f01b102a200e44a04c0a0000c2d0030940d0503a40ca0505001e030500030135495000d40b50080360000c041402180b0081020501130b0072810080c1c0340c4900401410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 90600126 1250 90598876 90598927
    0x21110a02040b0a030f210c02030a0b0603010b060f0309010c1418210703030e030c030304030f0c05060d0e01060501050c0c0d0201090f0602010b030f160b0d09210f02070612050c 77
    0x111402c1034082c446446c0071890410500380044d00b0030100042c0e8000c00c40100c0c540e07004d401a2010703160440800e00401804141a8100e40c0c009406152200024040d500c40e0f40524000c0c808181c8100003200c110340e00707106442c030341d580601c0004040b000702d05c80c203110010042c02c030040301030391441d0078402c0301007008490b061a0030001c1d00340245039009251343c126480039801051625000d00120795a40700e1840702030001d452502050040090980d285001048010032407912400001e000700d00600c1101c05248641d803a107d4000b816500800c2507500210a00c1c02a00514003110140403170003146110403410085440c002280314149020900e01805499000291030200131007490f00d080580808540359901000d5030451841e10308004100340d4580054250711001e080d121100170b4500700a0062030458400105840114003925400e069103031a40c5100d2120102402661140c91034029200081d10480030f403500d4000c26008030750041070074034045240c0160100b05c00f8510441e140c454 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 90601376 1250 90600126 90600143
    0xe040507110d0801120b09030c03070b0702011406100305060102070306020d020717070206040b0706140a0504020316140105070f0f0309030b0f0f130303021621110a02040b0a030f 78
    0x2204107400c200072845801c0c00508020040354140141d80c40c0403905c02c54010701c41819080022000303c4180155a407454200c022640c0b02c0440e840c149602030800c4075508015882d003040341580d09001e03800c0a00414000d1300d0841e4814503050224094007004004c141940300304400000060110720040034090311030580161500342d10700d090713500200300c1100d0324412042401700c000542d036518111000c803041441440c1e500c0703a80c0d00d000c2025100329a1000a02c405420130401d4410458120b10b200384c0c822420b942c079000030f15982d0301d005100f0380250020440c170089840760550045004101040c011001da0400b418181d031003585401d9406811000030300440002c108000e0304840464006544440c440614623010580e038000c07001c0141404a40b80c0c007401401c080c58000d80c11909414900520b40051112500b03094042980c44244407082a075200060560244541030003046004900040c10742c10619400300409000300d1881c1c030342d01080d20280000080c01c030700c6820020921440e503d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 90602626 1250 90601376 90601397
    0x2030f06010620031c02071506030503070c27050705090604140a051c030804060209130c0e04090b040f0305040b031f0e010806070305090715020c030c0102070b12070e040507 76
    0x34a41e0300e0560001d45201d80e03100f07204074170324603098030460010070070a081c0050300d5040c5401c00523601038a505125010f145051008810b100d00400180707c6140542402d00c1010340d2000c5c4102c44800c40e180b1000c0a884060817002c4c2403104d030708a650401294035040741440c4551b00042c0a079030190b4000918420f2180441e121814280e0f180001030900b01c465002d12074485840198100d41c5a4000f0308000f41180007800704200e0398103807455941e0140001406445401022000b4845100c04402256103141030b003604d443d0134041d40e9802640044501456103656460044001e907141c81102440002e0101180e180700140282d40b290b80700c0c01c40300c1054061860030710914601034001c1c101c00700151005010803800020495005007031791400040b0383d5501d0b900d45040c5400c603001002d948101030103050401e5400600c10b00b01d040100c003540c100307800e80001640d8a070598841c0d910010014400340e11204076540003c3e60010941c2800064200e1920004007219011503c40011400c24030b503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 90603876 1250 90602626 90602657
    0x30f0306030d08010b030a0b0a0f06020307031d030a020f130207050706120903090b090d15020901080f040210080903070f080c0607110615030a0606060509030d050306100c02030f060106 81
    0xb95a01c00041400c0c52403207941031440c0c200240c0300c000c020303c00e0141c8603880c0f0312030b41d2a00102d04004165000f0424011621640000e4880c0d00015081c0d001a01c21440f00000a840d0310b0327a0340d00888000c2c01448840304075800d100150301d14a1480c1d600c45e4800e440a00c03400e0140c0020f140c00c03403141006d443c0310f0781403d030080e00600d005010010032a00e0009490300203034210380362005030354045800f55281d0a60b03000145034003c160381c0003010000c1910003008030110b01e4001c0c2c0880a4243c81e8030310584d0303070f0340d100322900b800445020b54488215241084511700400c2d10941044040c01585d183c04415290340340401d00803c0b0898014100080d00f42600d0700c144140d5402011602c0c05150341c03113142c0e070700307583d20080902101d804000d006002282a40c04104a81034117600690500105550f41005000c07038104040060080c051a513070520781d1803013401200c0c8201001022090741c03d0314000100c809503e82c4400302d8042c840d24460283c1a10200140d40c02006580e0324060082c5010b007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 90605126 1250 90603876 90603883
    0x6070f0212010203150f030f2506140403060b1207060f0f050903060105060313060f0902010e0604030312110f0c060411030a02182205332403030f030603 67
    0xd01e194070030b0b403050007400503401e4509041098100304480c400d00c00203404002908100368041280814828500403010410080c3c80c03014022040b03d0100c00c00c5546d80d0b9003030b6487c0e10074050b69260b4045c100410b0001800f6a031107682c0440d00a44121b07056041c01000514095843d000324011540305008240342c030394009080c00e0440c5003883c045040000080100390745000c107000d510302c140700200c0041c01b9402c025103044c1031550030200a01c038101117001d8200042030400c80032381c00114036403082e14560420320304440c116031f071640d280c0050505801c03c2c000100303040070f801645000200710f0010410100c901a100a11040c405400103080502e03080240301a4201520b011b50802e00c0c03a1005680e0311054281c0c5104441d180c42c0c19544d44d500c81c1100704500003840020915441240000c4c40742c00141200c205981e44500f02548542d010f6807540c2d02004e68a140300d031400940010007003250707400030350340c0142030010fa29000000540003d0a40c1c01804020b12400d001200b088440d28040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 90606376 1250 90605126 90605149
    0x310031b08010f02090306131b0603140a0e100507032a110c06120406061a0301090c02010b0d020402160b01181103090d0f14040b03010314122706070f02 67
    0x3d4104510b4150088003103a1070399030041121010b0082c0c400320109000043c020780210301c5219100307040390394403480c0c050b000f0a1184a00c1c9100302440c00000c0f81328486100744203040c4c020303a00a01100c00e010041c0c1001d0000100f04030f00b015103c01c0c0c00c040310204900724440807812a00d184c40e840502c0711000701080d002d0b8000d5074165100401c2c100454491000302c481150b5810041900360b80e50342030442c00381a882e8001401d0f103002d840e459459000300c10245041c3c40ca41c4a051080c0f40c001c4100728262021110725035440b04072100181d0051900d5401404aa08402d0122200040c151a17000403020700340d21009601c110b9680550148100380b081050520007615024210b08007401140d64984001041700e0038072586000c4120306901a4544c0741c03482c18100851030303584c4d07284c103c160810b030000c2c40100d440640d05880548452030200b41d100134215442030260411100d04008000345070110b0090712a400c5015000b82d007622400b0041a0755030054020000904040c414450b488bd03e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 90607626 1250 90606376 90606401
    0x606050f03070b0a0f03020f0f0307080702060907060c0f06110a02010c14071b030602030c0901110c090a0f0e060112020a0806070905060906040b03040605010503190201080c0310031b0801 82
    0xc0740b01444201c40341c0c0155002e15100e445c0c00780d0360400221059009100d0090085070040d0045010800c401c002c1c0e00440c41412156200300c540d0300d803150140d80e546010b648400d001c2e00505018000ca0348220200309a0038060424504500082c2d140e280403125070004401007031000140c0441003c0d0240140600c0c500300d864600d0000d01140c410800c80c1c01340c044c004000103207002582860440c0740030b5400180da0016811550780c00c1501000c4100e604c13590006000c03032050140080321001c0440d408900c4440a081b454280c0c0d100e9100710010160b0036a444a050380d51707110024404410002d0901a001d0317048006480c10746801001110310255100b03da266200070204003619900040050072a041940d0580d19440c00300d0001c3c0090117940c01103401c000b000301c100010b1064642006040342c07000d605440140c501401140100100c01c0c1e40030340424a10000306410b007000c0d60085070b0204980310f546498540302c0d5240d242c1c55480410205150207814828080303102e007881500700030003a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 90608876 1250 90607626 90607633
    0x14090121020c011b0c11040f0209030f032226010f09030207030203060115050706020a141c0b040e0a150605060a09091b1407020f060d06030507080f15040f0501090606050f03 76
    0x40c1b9030f604a4182005e5a0b05030142d41c40f407040310100c40701c5406640340303440e00900795049182112001c5680c0d81200746c2140004069507401c64004551102020907918100c024a128440b80c46074080c0e00d081500080d402590b032205060034840c81c9124807040e2521940c0903282c03162039070040600e00300043c0c01101c07a008410300e119001a03005401c50b0a04caa000c400545c0b950f4003003100380e403440b03044909070810b8a000030b8010303070098001305d01d103480c550901e2080003e08544005d010850390b2000030444141c1c40084c60303e021800e481204a142444110080350594440005c0307021504802ca5403804504541c10500c41404203025041c2400e006841e000c1402c071072504014403422803014800881c6500142c0c42e0255200d0317040410b00010043d0086a031401d06100942c0240824030003a6114054144007160b2000c1c04a90307140d09929034001820140000e500040d01c00c607001e88101c0360742081d4019440010f60030b020704100980274000000340c180c83c2005100740b041803030254a10981 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 90610126 1250 90608876 90608897
    0x30f0705090c0307090e360d022a03010b0a06020309010815061603030b04060b0408010f050c03012105010c08040605010503030903100b03160e1614090121020c011b 72
    0x2684090011308440044a550086895905010942032240c2c87d090b440d401c18400399490040c10a04059031210b1200b00f1212801920700f8104d8a81041c100140c41a214030035004160b00019146541c00e100e0090001425000081c0003d0340040c09078011400768102051038a999a0800800c41c1e004a080070b490340030360003c00018401d40b00c0e172030a12107507011b40440103050511a40c00307452000000b0704100211905c0344c10b0803425800c54415072000350308113510440d643d850782c0913490003a0b68841400b41141d013803d01a80e0405031040d0074041c850701c5c0f00010000301d42c09024000011b4090b0721f44080c0390425060801c16a01c058000c0d40c083d9000b081140482d88000908415042212030b0000d04081d0000010382401c003a28009241c980c40b814002c190b002c0e0303421344203000368402d8119041c921005d507000d0b510390581000e500903241041c0400c0e2007a500400d210b032452200d07901c580074030102c5070040c4000c0760440101c0100c1a03541d01005102c0c110b0405541c011b51200e41007400b0f810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 90611376 1250 90610126 90610141
    0x10e031e01090b010e04110d030302070209040f02040f0b0d020418050a0b04020405011a0316090807030b090c01030b1005090409060f0203090c041b14070b1f060c022d030f0705090c03 80
    0x740e01c1c071f030707441801098a0b42caa172061510990588401d9640180b80f0306260901e800d04a24100d24894243d00c200d152080b8a0040a524441c80010301c038083c003481461036240d020040107001d8041000d0061020811600002e18284012000301d8807944501c6050705083c014002242d0051300302001180e85401540c04034000d4070240c0398030442460201c440003e20440442d43d20035594088a19407045210120400c250050810702c207070409001c50304030b080407800450079a02c0c0550081d800140840c5c010030001d02c00c80c000c203010780001d0008514580566034001c220744500014113081a0f01200303105407220180440000d60404440500c021540322071258003900d90442d41f0818842e2040d00035824052407400c3e40c0a05400200004041c5000d104012a40721654412035030041d4801c0c001c02e00764003400c5da0b070300f00680142500052055840c50f500e41005031081d0809840da02c0c1c4544481a6001c0101e50780142070140a403000c81d141c2014086481005440b5000c40340d001d000300728a2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 90612626 1250 90611376 90611393
    0x510031a1302061c0203090d17010501050a14041e08010c0c080415031803050a0801081f0e03190e040b1212280e0901081b010e031e01090b010e04 64
    0x7050b01140da0302d03916200304040d01038159005000340a001c0c0080200300ca1401d0100d05900d01c1c81c00764858640c11411075401111805090040c01c1c0443d80c02e02c01110094441c004100d0032091440740986420303211120200c0780810240722210840040c0014040f41200307009822884216040c90101500700303980d0f52a1a000ba80503504218036101100c1400601c0780d00b01c20320340441c0350000d955929480c140104a603028004400200d215080001807040000400e821003129604180c0843c0104081040c0940640044000984028041a00c1403009544103240c01e442a40b43c8069012410041c40305680002601c14814910009100101840460090500b003819955280d8800c0858900c10380000d01103d092241c02c481c500080c10650000d59602c480d100480320b5911a84c0d070303850500d42d900b14100182c00f0304080c11511b00f1080d4080d00c030401c14620001c00341c0703820710f040400441e50b61034a01c2c0c006245a45414204003848270b0380180358050a0703003c0ea016810b15040e11520700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 90613876 1250 90612626 90612661
    0x80f010618030b0109060801200a0c02010306030b09060f0a0e070506071a0406050613050403020c0f060c0307050615010e0a1203090e040503070302060f01081203090a060510031a 78
    0x140281c114020310820441c1910501030350b03020031001078550310380c1c208500800c6140181040382d072070030b21102e80d02c0340b6480c00c200c03041010b5980c4034944406000100c4101d4a1031004034141500e0312000f0000402c01c000d0580302d002d40800804503450700c01c00100384403001415100040d85060340800c2c0813000483c440382680d000382e400030b54802c40c0380782080e01d2841c008485c5100c0d66400d8140410810340ea0001406540304a0740c039402440c03ca402c5100700c810a69000300540c1c480b6642385017500303280440b524051340042816082004803880c250566104440071146ca81204041000c1000121200c035248142031030101e070242094408517026100d6801018a810940301c042010544100e0510010b030000c00c0b00c1c03800c603040600d0050f580c0d0b001207801701c01601030318000a445681c0706448a04980c81c0f50700908080c031090488881640c030180440006015030103840c40482e0450003a140030300090032001c05210b2450915070340072000802070049000c01081441014401e081c00b610 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 90615126 1250 90613876 90613889
    0x10b040905040503040f0b04090b0105090906040504030c050d0f030e06060a031e050111030105010f170606070206070f05210a0503010e1909050601060e0d0b04080a091211010f080f01 80
    0x30240c81c0c0e414000d2035801755600010ba040d00a807008112440340c1405081100c0b80c03000e040c05146102401524140202900950011128000500d00d442e00b0341041d50000c0c06814941f00c401100d803586410b100d10a440e210100d140d03460740d860001e615104070403207401c0311000f81c002810454000782038180c0303d20024029040308a02038400c030501580da80105075110313000300b00c03151100c0f036021340320341092040c240801c03640c0c1c00700d40704240a0807840d9840b000c12107944030550b0795201040516040300e401a81c22540a0100d2000181c400c0860f014040c0208010007000c003070300d03910102910485a074a030118100b4045e4413192034201c41500c0c1950b1040c000c40c1e607213598015240d4020356200b81d1182c3d0741418051a0030500101050050503141665220741d000c49103001401002614040000c2080000f640014046151003014080d000c90314a030600209039540f030100440d510011040c0d0311100094200520345d038201428590040c2181406a000d00d040200740b420b0b0b031014811032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 90616376 1250 90615126 90615131
    0xb0904090203070b0403050a030806030604031418060f0c06090a050a0b0601050909040606060219080f0f04050a0810050a060602061f0b0a0c0c050306060603010303050d0920040f05010b0409 83
    0x5411542d0610420001d40310700d0030965211662801c200785d55001c1c488094000c1341d9001c010902034100840d45511440d09901d07800448a400e03040000036074801c00c6101c03c020100d5115591070f0340ca600081a012078618503103a113a03c0c240c120282041e00241403504294441a4503800040011442544954200400b8021642d5690069405104268807103034410030400c1040100040c41d440341003070f01c0c51642118483d1003032242d000381032440030340083c01240e41840b43e50000e103465402040c40041c111880780c206952207000c00c0b171180058010907880d070081c0a00c00c090f107045209050340995004010701c06c0740e00c0c00f80040d445d0302010300000742207040180c5401c55040f054a4440041000a104641d2450f513100001c08045081508039080e65003448009000d01d800102103004020041c100761071a441d507582582d8a6009070f81c211f030026207592440011401c40f10381000120092038010140c0c031010010801180c007e0403443d02d8181c9410014070440200000782c0d02035800c0d0a000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 90617626 1250 90616376 90616391
    0x2010b150a030609020c0a05060105011107031103010209040c0809101a0907020109021e09100b1c090204020d0c030510030506240a0308091005040510050d090501050f060a0902040b0904 81
    0x11000390000d038001c41e01c42d9000003418460100b0007e00040303e280a601610041d90b291001142c0a4603034120105082c3e000c0d09041c0007186800b0403403801d06900400051070524401c01040a5594401401002c59103190812408241c18030418038840c5880001300016032040000c105030b07443c024841c50182d0318550004582c2d9001358014114a030b00103101130605c18408898800f41c181d0f100f80180100900f40101c1e5400380c001c42e115060b40e01c5121b0080c2441e04052032074440d07500c66198408000e8817030500d0740140c4c441f48000c01d02c042e0040004125184c1e10840641501c0010f4900c400d01c860882042000c41c4001c90400d820020121003890301908201e407040124440e100c1d0140e2001041800001b0021040020100c2000035074071a0781c0341071707a0003050341c407409580321301500040308903401c5d090188106c009017000103200070009802d107800d880d500e007180e20403202c082c000c203401c00030300059103400c40c0e410f0001d10107403000b5417400342055901c03001e50040c80c1c80140695240c400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 90618876 1250 90617626 90617647
    0x1005040213050103110310020906070f03051306050301050f06090907120e07090605010809030a1b030309060c180f06090317090d0302010504261204081309021902010b15 74
    0x1915070500c00e040310180030300d585030f041c07440080c01d444265074442d120b01150442510424000d0318031021004111900340342c03c949072413000018030002102041030030080109102003420250001d4540b6985d4a030b125814a4140922035020480325031060070180540d10287d5500c82e04c95034002461b103804105c1801c050918005418a0350621001c1d0280e010003280c81041c0c2c1d80001c0803994240d032254002d8607600394098407031080110000000307440f42c0c01004206035421907040540c1c420715001480c108261240b00489444020305000900701c0c85400b0182c0d10303d4000c113405404207800c2c40402c14138240c809085c606483c40300801864011100341034101144054480c00b15010340120440340c41d5150081c020182114110b610307000103607110031800451841002904880d0145c1c1d0b151041c810004100407000800455a022082041c0107041080c00182401842c4400c800343c0c0340c400c0c0c1c604c1d4820490f80c01c1c94010031a0700d40b000082c150b84d0341d524884a10006114441d40d100c4401c003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 90620126 1250 90618876 90618889
    0x60a0e100c080603010605010306150806030c090a09030e09090316050a020a0602150a020403080307110c041a030105090c0603130c090606050702030607030b01120213030203190308010803070510050402 88
    0x190460328940c50141841c8116801c00c0710030348240c01c01c4008010072501c440c010740450754a8017031030001c1c03002e10b81401c030407a02030800a5007055005044a5107202201c0024441c004100c0b504032550380ca0700000d000300764001461085075501140c4501907032400307950203a0f685c00b840300d0391000308940c500d83c80e0610000b0302c8001c1d03000e9000ba0010080340d4450388080d40d521502c0000d02d640c50482c9000030b581c0c041c40c1c42500c0540780e10181803451500c0346a41151540c100400701c05c000c0c0240c0402860701d03a41c6104825251404803880c240d80402e41c4201821680014100e42c12a0410000c01480399241c1c0112540080c481215043c2129141045c40400e2080d030462556039103454070200d174080c3c0281c05000064821002c44203290b540510031001e603040c02040c1400314038107001d40d0310b1008041d0043d0024620812440800c6a13032900000d05c3e1444106c032000c0d10b0196054040141540b02e5011409400108015491b0115550701d1035a108194415058100e82d02d10100c4c04541c0e40b407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 90621376 1250 90620126 90620143
    0x70f14123d1103010e0108010903090311060d0e0106140307030b040201050313060501061805010509010e04020c010b0310020c011506020303010b0d0605040221060f01090b090103110a08060102010b060408060a0e 92
    0x4000700403003082a40000c500d43d000f030150555042c409800001c44070b10501074070405036416968428000d1a554800c90078060012040f07074096418001345c00082072922030291064203410001c0b6415107800210a884400030a003c1d000c0c0d0800d55061004c20054520150000e9080c40c0ca25070301da403000103801800c0e400c4800241400c2c109000010002c1d4400026040c1158202c6032415150b44e0b500151000d01c40d00f0480c80c04100c404445030700e01d1602d54040d02c0c2d81ca05c2d160020a401825000082c00d10640301c102607561580441d600c14400d001340301e066000e00003050a0000d4074100300006c0e6980c001440340303030325001000603010000c04842d00448001c10001d8415034550300803e0114200c00032103880600881054030019140d40303801d50fa50107000d40c041c0c5508100c607040082c02d040c1e50741311070b180c00d042c15251034003940d0143c0201c00805000070700340d44505041c00c1c203100090a40d20103400c9103214140502c0300b4455114003042c0c19412003840003002034681240c840700e6050a991 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 90622626 1250 90621376 90621493
    0x21040302010b1801080c0d120c08090d0c03210512190504050c0916090512010b031504050705030102030c030711010603140109030306050301051b0705070f1412 70
    0x64100c0240f1080f940d0190694280c0010394030184071607000e0000891211601a0548e041d0185094403a40101032011b030b9180a144400d2501592030701080b070340b620300c0808594041c8100801c009000c9140840385242c058000c1004180c500010300802e940111086c1c03e42410242d0041400c200d003a44410b04d81c0120300a051010346442d0600e1500c034201303004171500980c031900020300448410100513550344940d488080405083c00140319152a000d45141019907944d81803161941c0c00700300e40c0342c07036619044000d40d092425242840c2000d016602540c082e030b0061081c04200000da0003034981c001414074121141d45641600c1c1400340c40568000340c0300e0a02100c2001d003504040d00047c1003240241c0f01031000c240c1d188141403c0780e004645000c0e0000030303290040b0741d40078580d00400040c0d0048003290700680d01c88550b88060b02403940245501c004504100c8428200241d418203402500406480d10310200030f80c40144072030380303000c1f11308550038501500a884098149548076111 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 90623876 1250 90622626 90622639
    0x60a141c0f0504060b01020622030908160f08010b0f01030207051509060604060501170103060c050f03070513151d010309081209011d1c0306090905010b09010b21040302010b 76
    0x9040c0150000b440c0580b4141e51490a08456043c19400060702c2ca0007010b608900300010036900710740842c150b040d05401c40c10490b128400141c010010004000052044400c940342c1134a0144515524010780d48048880d9042106c01c5500d83d95182c149032000a0038200960380d01c00380e10384541441d203404420402e886074001800140303036000031014032a92041d94200500c6440c1ea00540c0c0c8220700c0c0c00f0f80c0075107038960401803000443d213401c03154a000301410b000f8102402021182901c0d007044801e24000b5401050701c1d41440600e00f440c400070090181220846c48550034001c09411901c1000d0343c0c0c801441090f605240d100394801c210264020040300d48585000e5000c00208000361b9448410f9801d0141c4690f0140020030050b0762403611070000e25120300c103014179242200821130341800303040e030300c0d9000580350030706000c0c01055038890800050070412640412650417410b800c1800c1064060000345000306002c1c442101d880010b504859980e0354902e812400340c0013140307910b1f401c9103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 90625126 1250 90623876 90623891
    0xc020301140103030e04020c030702040b0303161a070509031b12010207030804020307091b0e0103060e040303020d050705040503030715110c0607091e031b030203071401030506060a141c 81
    0x190200400e0b41a603100c0d0ba200411604003000300402e170b0007061216440da80080154100518140e0300c2174907502c0001d02034070300b40f100200080503000040741081e0350701440892001050345c040808164003d80b82c1c00e0007805c00403240d0210381e0780c101c0d81d1456450305400800b1406181d45401001940c400650004d660750130301303450010000760f002e0b42c0490085c480c03003d01055281003130203400b610615580381c00603061500710f0101d41c0a40090700c4c00f814583c0e601c0021460a03501c0c0c0d14036101d5030298601595581c1c81540394411510300402503400c20400380024405e40c0d5010040b6410940c200042c3d81031070360341030541e400410301982030500007000012441607203d00410342070302ca840c0c2ca440342444541c2d64290321a00000d101c1a046528072410401d00011b002c00c801c0005109004c0058103020f9201d601180c684105504003501c0441c3c2c150f0092039035039040c003516910800c00e840303071400c10010300405003014078201207400c442e040100c0c218800a042c4800c042c041500b94800f0300002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 90626376 1250 90625126 90625151
    0x11070b0c0f0c03070e0f040f050d08070f0f02030306100201021603030912020a0c03080f1902070f05010c051e12040b040603060909170a1808010b0901060c05031206010c020301 77
    0x12440c03124241e071680681d03520880c1610700400e50300100c0c1c600d81c0c60510550b4464030380da603014900034030031150001002d0004000c20320805c076210a01840380c84030482814100e0001c2c0810f421400752804002081105401d000d60110a072034020f0010ba69051201c41d40510a03070190180340002c0440c0c80b401108141855896041200c44900445500400d202549022601c4003d10752000d00b200940d42400c200003281007006201c844841001c560030001504240710544201544400c0141d002003020b000c2d040c03212003a04020003090802141c4002c2c2e81c0d40342c68a03448180030754408041c102040e8a9031680a00c0103007801444128003c0d51740b901c451029a4540180c0122400286130150200c1c603010a48113101046400c11865580076010140070000c0b58016005030040281500c000400d0110003103c1d080a07000d040004506601a0002c1c8401d003030050344000e080020002e0f260b400304001100302c881c0304008407017440042c3d0720400160f600d50031051000350150318010030b8600c03e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 90627626 1250 90626376 90626383
    0x26060906061801080a1506080109060b1002241003020604060503091009030c0f11040f06030b070f051b210a03050a150519080303040b09121201030311070b0c 69
    0x1d0001103070b001c8110350064075a800c10503424010030700154403981e440000315101c00440013210410340e40c0490300640300c080c401c0c2900c210803800c4541940741d0035603030a24a02150f50007400740542c402449030440507000030203078030310400d5034680950b03844012401140002407410069a005092107540316550f100041070b070b5108491800c440d0203082d28241c2c421100340501e401d040c0c0c042da143c1507515029100d010f03000e2100402250b80001c00704d0583d10070344582c0607884901440c00c1e000aa000e10b9070520000a910041c90a07041000031280402d102da00203081e1844203c080f0034141c003000c4882030040c0340200780340b05403a44641092010b614142004003e0134a030340c455401703005c01d455420300760301602c030700c000d8400710f084040701c0606c15418041d078000410280d020080c1c1216507500501070855209480aaa402c4011130410220f030008120582c03110210b251078a01c0c0161401c00640e0015060000904022070a11081d801e480200418400344c1420059540c0e0348441c0da100a0b603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 90628876 1250 90627626 90627631
    0x1803070e07030b0a0e070809070806130314030f190605090a0b01021903050a0f03091a040506010e040804090b060910020601180203161407080a03050f0a0b0a26060906 73
    0x2e410700300425140d0409049050498424074448811519808026103c090740200040e000d84201080000c03501402c10034076025845031000b00490b01c11505000b401c03200e54002816514504000307000585c29407104a961100080c04c0c0407107005410006500517014690100354014444000e1126410142c6d00043c00c00c21f00340c0840d294a00320050140c002c030b441d003002602084040c00034100d014000e203100d1400d442945030028054800341d480300b81c40440c5049401600c03544408100420800f00310050240410304040315243c501992031410034401c07401141e07441d5481d0802c04049481c0c4030b09031079420000501c0f1201001010f40002c0d0358200900c50036103100e13400c41221030448030341c0c802c6a018660b80c400300d02207500502c406441c150109038911040c89030030007802000c242e601018150460147d47c02003200d0a00321084d14a9810240064403403a181c03186001c856a10389061104580c41030032034131380c08404842e60070b00142e0000c070a000f0314080c2d0f00c00c101003428042040762 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 90630126 1250 90628876 90628891
    0x1407050d09140405041505090a140d030507022806090212100605100804170909040b070e01032d150321050a200102070c060f0311090d081803070e 64
    0x5104041410007040c2d450503a000780440c6ea503039407070081d01411341d084a07030700410803003c4030000074403035070381b9004025003803081c40064014400301a401d551500560760232417620301c000c00325082020032545a4480740c46886404904a003800000c101e03464009009181d0000c061184038851401c010f41c50301051000100d20b1443c200c3c010030b01d8a001a12102c1400003641d0714002035440d40e6404091004148081c3d503021010b020010181e6074281200d44100c2c45620720207203d0902c0783c405050550810030701070503d030400762000c5100c0ba01c002c800ba4600c202c4d4000c00c41060300d42c00c800300141105215515a400364070b07404014441100595005503032481040b44400c41d8a41c0c045800d4014884c0a000090b40c85203510b1420140145011640c0440e100041c50056160703074150442c4d1103544181e0104120450f400c02054062003401810010926600c0c98100620300103666804440001481c0d1203002c18000103401c5042070110103001c014080703525075610740c80788001c0f00c0003c8500341e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 90631376 1250 90630126 90630149
    0xb0414090106050a0504030f140604230a02181009020d020403020a09060b0f0a020f0106030b070806040c05031b0c01050109051902040515160204060b04060201200304031407050d09 79
    0x54028410f400b26604101143d480da03081904550341e01c4803041c1a0350050b11484102076065138003030310500655000b140700c1e440c6c1c00301c84540a0304030706800b541c0100c1c2e0145034004200b03e4015845041c00a20b2001c0400103949076a0b542d00c204e0400b40c1c18a8000c804501d101086a100c1203031590b0003441941d00880b00500c0301d0341d45010300000d4840501400c0031a000c1400000352035103000300500011000c50059440c28083c003519142100c41c41d900c1030700c02000000071712002581041901c1d420903c10344080c014240c540c08041c000c1e10029000e2044154a4450300d41d20049031002c1d0380e0307540c0c40c3e10028031681d69540303101c2019103400c1e603040180301c00e99030600300c4c000103d02c212422210f0140020114103420000c20070703150002c0d0405e20441c05100c0000700180d0319803140380090030214424507200ca0601d00020f00b1074005140c1c61208000c010180b420211090302943d07805075041ca41400419500350158070b03140036110000344144100c03c1c1000d2030310b820010900a07202c005502 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 90632626 1250 90631376 90631379
    0xf02041d010f0f0204150c150905031305010f020703021002100908181017060409080c0f0c04020405090c0309030f04090902030c1804030c0809150702030c09040209071101060b04140901 81
    0x40e0f0120722591061081e540c030005800c0b003030a8010b000c00d03070381c80f8002c8100c2060141039000440584003180011203c6400018491405001c440d2020001c0c240c28601f00410715035104001e0768a5819000203072091408002c040e0304184208850a61050b0980d130610821f086031410a0080d008140030b9814000441c3c10032203917003000c02080321414034035920400751007030701d0b00d49968000000d0043d0750043d8490685801182c5694000d0003d44443c4000f85510103060f0070040c04c10300d0083da0184618010082007000350b50740401035400c2001909178554a0312156144c80c40d40c840d0a803010000d0780701080c0062008182c0e0700c070017502c0c3d0081d815611003224007030400ca100403c90054a44000c0440003040101e845106d460080700e01c90300c14035213091a90000a4a104504000014442070004031a000c504043c00501c45180c420707100c0c0300e414101341e40010a2108011b0091041109140030480e041c0000d4112a0060403040d504940d1380c1e859000391140c00f0101030005000c0ca041400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 90633876 1250 90632626 90632651
    0x40b0912031b030c0f0c06040e190c020309090105121b0402070b040c0f050316060c030e06030a06050a080606010c03050c010b04090327050a120302030409050c030f09030304030c0f02041d010f 84
    0x48050107203c00031f150500c1e050408804000081d0081e0640011001200100c54024528072860000c8111a0010b54a41c15007004000c40c40310141c20040c09441e069900003028000080c081016041190950003c900080c010500a0084000291501c141c41c424001840b001d081020305840c1e0185080038000d8441c020315a0703500300312a8280c525501040c0c204400d40c03143c8211141c09109190000a80c2480400204a50800da03089c8180c0c6a981ea42000103140072158540145800b078050421440d1980020303200c8628500c0213401c2c41400a110305022034294040c3c004240c006000700a0046503007801449400c0105a440704800461010006e4411801104085550045c1890380e5a410725040c210f40010741b400450941c481440003040000c060f00425210310b0040c07480319141e01c3c0a450711049548050821006a0020400e000101e0b500c00304040d07107a504981c1c5c008249240d0310200d002440080150b841040c440d540c0598400019000703001601c08400d011322884a0044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 90635126 1250 90633876 90633883
    0xd1e140613081902030909040506090d02010b0f010818070603020306010f0824060409052406040303090506162901090608030d09051203040c1505040b0912031b030c0f 73
    0x80340075140580a1081200103c294903402141d44442d00c1502e0901c4070760f0010850400040c2c07000c55843d00402e080001e00c0f40100003204030164144003e00c04103480e040401d0301d03402d841c900241004154000200e000d01e410007034440110400c2c088032590399407680020000e420980300303140040d401c1001d20b100540b00f1a4040e0083da000181040c0c4060114080944869006002074010100744400a0840268401e40d4490131108170080f2404420030441e8410400100c07d60784918001d01c814808a0303400903814092b10415101d5035a80c0a85071031200103841ca0281c005c20300414101c041c217502c4114401001c0d0f019806804140a0740c90b24042d0b4255091806044001d80c0148030030305801c64990803d500e0b0502880a46580049000c1c21042c1988210703400d40d44205120300c1040140c00d0400d02e80c404141e203241c03060400303040c200902d0480c400c0e80380b2140302d64072821410704e000000f4000c843c40106280d407103024020602a015489800074500c0c15030350b019101003500b1508022 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 90636376 1250 90635126 90635161
    0x80d0b0d0b0604061d1501141305090a0203040b190f020a02010b010305010f14041d0a0c170303100603150905010906080105220201110111030403050705061302010e0d1e1406 76
    0x401003807400e941c801c0c5071112030321088030302c040c104640c03a03501d180c00c020260000e14000c20360301d0701906050f05020501804090140c40733000079038810004c002c0443c3c60342030841d800c061610700084208142d030001c0c1001d01032210001000c0340c40012500e80b030316015403061441c05020380b0240402d0382d07034542100c0038070307058419014481d00317240303c0914501c1d00c1d5000158004010728208902542c030f4200d02e18010f6844000c8421404000042c011552a840303080c3e1410101c4005516616200b5603010750514244070b050103040d210054003a8180030241040f01500c00b20f42d00300500d43e541c0c0140c00140040c0e20507100c255103800081000080007441c54007a056818a400c03030181000da004483c014244801420b10b55601c07034118508040380001140158025070300c490704c600c454140613013070034030291000a103001211881d6005036000320001044170001c41c0c04038a00c54450800c03024200340b40d08040b42c048400900101013080d081c103070810203018042241e49070b5841da071001100c003001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 90637626 1250 90636376 90636419
    0x106030e121c091e05190507030b04021f1e02070305031b0a2004050f0907031506180c03050c0a0806091504020d0b040c020705010507080d0b0d0b060406 67
    0x1000310340b0040b203005100501d50301542a0010f0807071015116120300f00c441c214010840785030007802c0b0702032000030841104589111454201c2d01d11142c0e0302c00359503081a100083c003401035140080e0540d91030341c540c131240c02103246c10203079001c449a03002881e04481281c00b18070029900707003ca020724400601082920761210045d0728000120307800c10310401c13485001c61400d10900309006c00149030240b2050380008011090440390510780300b04020b03500c004064040c40c0d41c5030f01c20403611020005190040300c0d080041030300340101e444140e13006892650022645240c681e00285002c0640d507002980d48485581e04204c0303525450444001403140d1070a940015203100046000791500e842c40e540c1000703a00050040307441101012900f6078100500380c04046546411604842c1040d000303c90031440700f40301800029007843e0000e80b450040c00b5000d0001500483c000898a880d03600c15214000000c15001d1561100d00e00307181c440c6000c4550600032820200d00103451010340c801035103c03942 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 90638876 1250 90637626 90637663
    0xb0f06030f0a03090b070204060812070b0606070201050703032c0303010e0a050906010b0d0603060504060209030d03020c15060d050a0507060e0105030402100f020a0b10030308090f1e0a1a0106030e 86
    0x58580c80d03070040c1e00540e1b4180d038001c3d41c950000902410402c60b0b9031010780980b54031502c3d440f0074100380c229480c0041c80c4c60701030f50007009014010f0b80e0100413514030780d8bc141070024446c9404d06000c0c42081e0a02e0f0391203030303002e000100c0c0407103d00f000002d58102c80807140318280941d500380001e4243e80040e07405144540c800d40050111800c03040c06010b9032112a80000ba116580351600310682c0c006860603600d003030b40084d41d40502e04052002002404007814194a4070340300e900070960f02c41e00c0c800c8558020382c008000c41e000b5640e003811102e88a41000440e2400040c0d410074a440340c102e4440e91012030101001401c5030350040c2d0599104d943c00801b074a0b02e84901e560281d4102d601c0181142c110701800312808000b4400e950013078043e0b00c52020300d0800c5821490081c0c40017101410303441075035001e00d42c180d0943d00001104c083d010034941801000340c003603040403490f203864590010503003610010f0040000c140007041034101c5260340c1d410700c00c00c03807001c1c4095226501040800051030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 90640126 1250 90638876 90638879
    0xf060c070b1c06092a0e0d05010f020a030b0a0807050105030106030207111e030c0307030c05040e070801050703050f070f080106230c071509240c0b0f06030f0a0309 72
    0x1c550002d031480000310360010400c0a062500d802c01c81e40d0940203124480d0f03440d100401611310301d000e046014040284001d42500344480c0140c0000c549180d07441c802e0240120318000c0080a4021601d8540300e03444c1035480307261074840500074107580c5004034040c1d074150100041900c00000c0a9045820603140d20345103908094044000e503018800c01d4480b00e1982e00c07280f55a032100441d240c0700c0080e821441210401c01d104050809911450881c0300e07502148044c004140421903000403140200d034000341c0e005e11510a02d082c102e2650210500e540f0340300410001d41e4054120f107101d130a0b0038040b002680d41d1200d041d6206c00c030f000b01c072000003100903006004090040500008403188001c00c0415681e00825240403680304000ca5111504079075000c101aa0302d900e13a560700d08d0100d042c00000715003029040307005e85a450704c60680d000300006c03604642c030f401001d01d02003d5070008c261951618001d840d140c4072035001da403010f0181c81a24051040d041c0d0104050203840da25a54256095 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 90641376 1250 90640126 90640139
    0x606010e0a030b070c060209032410050619020109051e0607081e0622020403060b01021c030c05070f20060313060b03070503030309070e0a1506030f0608010216020f060c07 75
    0x1040505000c41b41c4039402c0020a07902c3c1e40822983c2440400d60307005039032010001482c540000300141c07244a0741c0c2c000c48000c1c005581c45000399400454003511502d085441c0030310483c0540605c40340a0890f001f404030387c502c00b038041001540ea0381400802c6952a84840c601100c0c040d400719106d6410031240341d15215800d1030300048a070081001810404030150303541c0900c2d42c2d03064111005200503800107080040181c0c40c01101d011031424005026446e99883d0304440c20440000602c0403d90784040901c6400e0045003559401c1d0780001800301c0544283c0380c000c58001c03c0601890304600311002401c050728000c41100e2140795a405415000e900030b0740e030070b005411110300096141c06142c1c8049120340341000514811080c40004040440ca4010f0941131144094009070700c03c3c0c100400140c542200207000d038125012403030001869020702da142e600805480d0481c465075400010814900d0f40070300054841d41e4001c88102d614100450700b000420300c42d011105d01d05070091030081006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 90642626 1250 90641376 90641387
    0x111303060506030a0503031303110703020303041703040812120f040206090d060b15031803030402220b10030b040b0f0d060b130507030516110c100507020d050606010e0a030b07 77
    0xb040025085072031806690f034907103085410481d843c21090380079170f451400341a844990030503010a60000b0701011030543c0c000c40e459128a00804500d00d0100c10407502c03c0b441002214000d004810949081024858804103d0b40c80401440300000d0204d02180c6ca00560070031060007940d0040c4081d29012043c0700741700103c4a0380360b060b40c509940312914143c5444016580c40c070b154011107200e950f40b41181408403540d102c181248140c1d8070074800c01006072120310340c440162403188030030303120300c4100034126020b090a09452a082031091a0a041042c1c254000701c4004200b1030702409600f20503000e1190003560f00700d000794416482200c21380881d01c542d000349200f00000e0020381003943c96944420072b440301615081d000a54031010041c0000ca110144240764003240340995900000005140d91b4900001025104000b2088126081b5010b4011146444d130f001d03044240403c1d1508186031542c008440281c045041d41213410b24524002c81508203880e4040c030a20b1494a401c4801c03503c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 90643876 1250 90642626 90642631
    0x606100504090911120a05100506150c010c030b030318060703200604030201050a050402100305060105090406090e06090102040f0e1e09010209030d020d02120f1b101113030605 77
    0x3403000810010441501500031000e4181c0128034482d2103080b201e0900110402018080905400c0200b03a440001c2000c91110b01414014102040f80d0700d490001034410804000c03032103002078001883c0400c0d100103401507444403c1c43d80b001c05c40c4180800038192644a030125a6050320101c2c40c941240b40303006009001014001d1070180550704c141c0e0b040078413412000c410000f00303501a004100030181d090084551051540300180710314105a80130a100c3d041038041c8005154413040010113a9105105541204400034018404203543e1461040245100300050b20345006000c00a210210140211021540d465034400f035120b1400e240381884100181c00c40b1003012840206142d12004521423902a000d0030b8001a5500c406c14101031400b5000002a402d540044d05003a5413141c0100321807665286841e031003586c41c1d1414002d14100e100e2120702c603015031804103180402c0500003510004c00b8000b03c1040020303444030b82a00c8114040d81da42c0022501444c48240001a490f81110f40c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 90645126 1250 90643876 90643909
    0x619020c1201150e0907080f0a06050702031e070303110d0603060e030906040303050d0207080f031e0f061e04050a0903141903090f063305210304031a070305090f0606 73
    0x10155521404028123160380003143c911543d0100c0a00c1050155a2080a41080c103600041d0704c1c020300000d44040245041c41da41c1c00309200072841d541454000d800060b40051100c1c00151b46a000f541204001e01c85800107817034181c5040714061100390004100d95207002d0060030740c3d0a0520b5651304445651180002400c6240c003407106500003103041001e80403207180d144800c0e46034580181145030b9658280b9a41103070040c085e0034012402c08030001c0d941c100d41c06440c0f24810880800c19030f40300c0b551261040e5000752070b05c0d08002054103a54442070700c4030b12030307038640640040d500500c2c1c00030302034002c0d800340844c00f0001c0d82d22028003e5004660a910030b0382c0bc204154041e403160422551200000301c0024094250888011320b1001ea280100c6001d440e00100c042c00c00c2e010039035100c480602d0080c1d40c3c40501d000000744e4410410742d4000c40e4404d020903491035601e448a451300e00d09452110101e8280804074a0000c0c01044041e00c0c28041c00c000d1909a5481041101d00001120007a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 90646376 1250 90645126 90645133
    0x12040b0d0e150408040314160302150f120402090108060c04051e180108010b0a1206090f0b010f0e07030c0c0b06011404060c05120f03150619020c1201150e09 69
    0x40c15400042c0c07800380d00c01e41c01030321055105d6166040c081c0c65128500c042c0b08031500720300082c04280c2440d1009405903501a00c1400c0b00d43c0301000c0d01c0055101d0700d1a0741005003400b1510140c0888100c0c1c030709100b13a01c25181c1c43d0305643d0b00c2c0c940075070f07a11003500c1240d5100424442807049052896040040e60f0b0b843c41f4100050600710b001c40d0300c041e900000b46007000f807a84014800d0501c240513004070300b1000e40f1071130019842d080d01e4600d0304400c40340043c0499164014032040c000903096403410240c00184500640d41c0d5010f0000181c01580301c0c13074582c2c06100e00003c13541c3d0b0007486942c040d4600382d29681d02c0244030f9651200716407170080503941813090780c1c103156024049010241010b00920707211060780c41d04034140146010b40035194804507100801c00c15080c1641d00040d00d4200202a035544220070f1540c00182450090202d054000012524000c41959001600e200d60010544540c0405040c074010305080c0c805241003d0303100c00d1b040d03100700011030b0761904007944405003d003038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 90647482 1106 90646376 90646393
    0x507051f18090c0504030c060c0f03050d0f060602010b0307082404060b06180906030d0e010c02040204050a03050c03060c030f01050f0d0209100812040b0d0e 69
    0x440e04208402500c480c00841024850001d000c14035003d00c101d801d03891000f0300c40d41040c48280c0f11100245400507a41c0d0144400744020358014107020301e003080c241c9007a607a0381e00c02101030382001c1d5110500c041c00400c51080d0700103803002d6800440e000b55003508140c505080c0b41c1141249811001418040305840340401a02c1d81070b00e0004207481c1d903182000e5004140709030180380c0042e000540c00c4c0c0d82c1d8000300800c4010080844a070a0306880d200207241d80e07003145550340c10100383d043c2414081580511160850144002c2000d481d107a04c807030216038540610f030700448041c4e204040492540c90b003486070990041c2c65141841c1980b800c080b80c035112050602c41c00380600c2c4100d841003007645801c0c2d0003403200c1c0e13006804200ca9045c0729500807985d82003071194011034021030242c0c6061200c80001c0350102c485950120381040c01042c3c6400c0181402146610980708140700b = true := by decide +kernel

theorem cover : BRFrame.Cov 90467626 90647482 := by
  have h0 := BRFrame.cov_init 90467626
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90467626 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 90467626 ≤ n) (h2 : n < 90647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
