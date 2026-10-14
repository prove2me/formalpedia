-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0474
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:59:52.708652+00:00
-- url     : https://prove2.me/submissions/a8e7c1a7-9464-4125-b7e4-72751d9469d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 85071943 ≤ n < 85251799 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 85073193 1250 85071943 85071947
    0x130e04031b0611030a060f0909020604051e0607060204080115030309060509010c1e05061e1909020306040b0601020c04061a0c030408030301031b08030931140105040e1912 75
    0x1903a14243c1400c80359480c94001c500708000c003094001c02550348401240814101201d1040307105081d40500064035080c10a81004000302030380f650f001c1c0e142d40c20009076610341c40302d8001c0c2c0301d000e220380405a192030411a1031801e403810090481400d00710908100003080c1d10881c1007013203a180e4101a980e5850250048409604840c1b0140035805d0b10401c0c00c150b414079800701c1d1192030090742038071160348925420b004400483d8011070740142400d0003150280f281100074411928080f400012904140d9010a0400c0c1044906030b03084988203080046c81d5805120144010008407802c00c4000c1c1844d0f114a1082801d07402c8140c001c001041c800f042110400c2124090000c650889403250380d6883d01c00441650794000c074021030804d00d03001459103000070941d502c03c0001400003281c0120904003009002c100d04042180c03026482c2c00c00b41201413441059486807050001e11202d40c103010600c0250b5110b0007424041d1781c0081c2884c60262941c04283d1551b99100b010390380f180c0464402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 85074443 1250 85073193 85073201
    0x915021b040b0a05120a110108011202010807030239010b011b050705190515180d020f0a03060f05070f0f0c020307090c0201020d112a160b130e04031b06 67
    0x61078209220425400c00303185d001401101c414404d0040098503002103004466141c028030800100901d100728081c01503010303100301c40d4405a80c1ca00142804006400d14190b40c120010748001e03010420013001079080780c0c2540483c181c51082c0203003c004172480008040c0c1c0110740c50340740140d6510000b00e040003c14441400105001000c9584801d0030108610a9541c0c41c8035440c8244140f106d0841103100403003e5a420020342c002d01c051500b141002e20050506d820400c030b82c020038000240030941d413800d087c00c020314020309000a090803050100c408807800642007505101d82035001d4820264410702c203070307480d00240c41d004d011406144040b81c035000035504042007282c20b00203110400c81d4150301804609109240c240201c06500403450030500c03802c0c180c21203200010840307500328207002140d5880000041c04503016035804400018500000d50080c0c1c4265200240d0303490320080d44180c40000e0812844c002c4200c0c10720341e03801351046950084845068205512000501c8041d0740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 85075693 1250 85074443 85074449
    0x1206030c2430090a020618010e061902010f02070f12020f011805060a05090319020a02031617010507090e060f0307080d1d06030601030e16060915021b040b0a 69
    0x9601065820b569596030b1860030891001c000c0503910000a9941500040f6800615000750080d0728040d5071006400320f00b5000c51015060091103030101c6419120000200318042560080c21080d100251009003581c0454100003c1103006010420100e50301e40240494540d01a20543d4100c03e902416070402009044a505d25442c02850303c0c4030b01c00740b145011503184100152681c541d5030100c200100c0c1d81c15903e0409507842031180c0c920318084156004070418180c0100c03443d8140c150700185c68221848004045561112010089502000c6200340080c40080081c002d0b031a2092008058005510600e02c02c41a5200440d00c1a146d4105508403900f020f000e607004540c503001015542c0d81810031080008000748908541c0c0412071001c41d00c00600240300c0791542c3c40d0800110064030141e04e0030101c070b0154a07210400c003090340300d4000040c2059180c81452070302e0111158804056038281c07900395013087c01e229502c040e10307440c2200503607401c54002803040d0b01c44d00458200306041d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 85076943 1250 85075693 85075717
    0x2060405010f021002030f0411040c0e120a1502090901210305030709030209090f0613030212030a06080d030c020114040302060f0a0b0a0305100606090503060a0203091507051206030c24 81
    0x1803002282e2003d47d018401c80c020340c440091250001c050004403066108840b00040f600701300904980303070507005921458400c2d8121403160b030303403529040c08111003814500c0342c456000841c1d103040c1c1030074000c441c01008079442c940380740c00b007401c00d85a680c1106480242000800000640c10307e000b003160b00065900a0841d01003407408403031581d0b4500c5d4100026055115107000245190750080e219001030358542d019001c0d44403462003a50f00c075000034229400254483c58007003800c080410601c00200c1c2d603540c0107e080880d008000e8210b901700c80f000c0a56500d1141040046a000110550440041c01907886542e44c0c0000c240010031004081d543d001c042c2c480000b0901a00051603403c81521040c204000c0c1c3d40c50310140c0318a14a407141039016040400016030341110b03a409554461130200070394031b0b104d91070f411010f02e100080b20201c0100e0008901c0c809505001a050366000300e041e0020300d03003a801440000d01c4551002c007444c10508000301448046003118040d110104c0401c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 85078193 1250 85076943 85076947
    0x4091208060301060504060b0417010f0c170705031b030a090602030c0409050105040209100c0318030c18050108100902030304080a03170a020f090906180405060703110702060405010f021002 83
    0x120400421001054954621039800c1c94004941850548503c00440c0c4100c201c85107018544004030351204510a0494203079580e5142c201c8280985020b5465040d9055450300c458146910150005850152085081000620400a29640719020a60100d02d2104516182d90b41c0f0200074025181079440106043d00100602c101712008c0405403040c3c071035104044c0140c0c1c1e01d0720300384070483c05804003480d4040c5000b9104280a40142e21a4a146009282510026800c84008185000554002c6500e008003000801c16410108621902c0d60201c00050106514281185580d0126003a4280c00142d80e850114115a420402c503401085030790705460310f400c0d550401034407030710307140d400200200c82c1c40000036100303445407007280e00e0a903240720205d040165a0041c4049000f0041885400c45d0040034038035980c04240c4a024842c511400042a55141ca1030b002001c0e152000b80040300000207104800060f0313110001d880c00d881d02840d040310550340f083c100300d240010300c0008000040c40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 85079443 1250 85078193 85078223
    0x1b0a1703060f0414040b0402010c05070f0e0603010e0a02010509030109050f0706021c0807081012140c01020c03060a05043e0a060c150e030a11060705070804030308060409 75
    0x62000a148500d108445050030700a40c1c90070700003580c2d04004a40d520244010000f17000528004070f9503003080c01850000c49842c45940c030b0a00d00b0909070001c0c80e00340305c41101000017030b000510031540200300354024002c06404c1141c1680e41c4d2440c16009041c050041509511a2025400350b40200e030410700301c3e200d910703041c2c030710170340307844e514000c180040c05005100410140305c1680800c00703403419645c10129a80d00a0200c99500019045404200b0050070000d075420341202c0c003a58490040c180210103c00090183d4684844075807100e05541103564110010364000c219903600860403130b03010580741d5075031802d0341c240c0043d0799038054480340c03d0081c4020f2111031500c0610705d061070309070b030045a003980d0704018881071b5911a0b503000819890684001a402110300906080024800329200036643c12b900d0445c0c015071103100009135401140039140c0740411403d40c02c0030719400d007a0310b06005511031021620407808081d05111307070000803e00c10344031036000c02402d1380c1040c0700c4074048030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 85080693 1250 85079443 85079483
    0xf04060509190b0a2603070b070e0a03080304050c01080108010b0609120705030f07030501052401030c02120f0915030408070b070e10030203070e010206010807290d05070906080c1b0a 80
    0x10012100181c0348068072111042085c000044501060304017142a91543d107284c0121240102c501d5016003048000c58000b0002d40d641e00030390b00440c45a00a00b000303601d804001000c041d01607004007142d85c1230465541c000c0d20391030111744100710151116004103200015181c68200f06900803a094410f00e411880c0302140450b00707106a80c4541c000f840107031980c0b0309a00004481504600c484241e5107460300c465030003680040c00358102c50050720440d03000008404501d800201014600712400030759200d040ca820000c03d6003d0b010150f030356081d8207150301c170b04606002c0d100008002039048004280f510340203401c100c21120340103145154502e2405002000b0750010703140c80c030200ba0726615a034880d41c004206181601d8484000b8094545060b030180d05514851074070645001d40c480404d0240c0c51154018030030181d5090011503a030030171180c020030500c01944540200b124007070511100060b00411983d9260000c510707803100c1030100700c003d41000140f076030003004110849100d4842030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 85081943 1250 85080693 85080719
    0x510020d050d1503080a022109010212070201020a06050a0209010f0819021c020301030302100b18041727010206060904150507051c090606060903030804060510050d0b060f04060509190b0a 82
    0xb0101d41b40c4803007643e510758003231595016602c1b240c1d01581100d2100800d210b10701004e03040b5a03005104960b032006058403080c0c1160020356039060780c00e4001900c1d001d20750b0441007940420002e4a0080141c0c9018007000b1280c16240c1d044c072524503000075164042500454a101111142d040304540e6565a450003179964002580c820070044c1c1011416015480d041c2401c202036401c090011609542d04e035100d0190380b0340c0f0303110941c041c0c40c28005180c2001c041043c9900100307490311200b0050070310000191800000800303007803184503003000b000700260180030258054000d561001c58542c4030402c050b1100e021384040014100c042e000408800207440e017183c0e980c0c0e80201c10800c98951030760001c1316060581c1c000500440c2e205808200010003661001c0e038003083c010b01e030360a4a600d40c8000752a40e89940c030107480300342600d800c0c002035240c100582410b034034044600308102807501d4046840088003c0030004000001c0544181100e00f54001c0345c10002d00030070380385055442d000c0042408c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 85083193 1250 85081943 85081963
    0x4020714011a0402040303301406090a0c02250b0706050a0608060106050a0c050708070e010618180917030a0204031112061303020a0f0c0510020d050d1503080a02 71
    0x1c0740c00c2075400c2c0080c10607108940030b4076010303035540d0a8001e410f6403e8040c60b03c461a40c48590b0802c07020000c0c8003949100f8000c4104a0f80303403000c024100b0100b040942e550250003003a080d860f06400503017294002440803802840da01c0c00c2c8260174140e007100707012034016600510201c500040d03d241040b070030b5400030344955080d480400402c0d4442d0340d0190b89001c00d002d00c0c80440c4081040101d098055008810103c1c03244c802c07141301940303407500303207080000544c000740c0d0001e902d81c0180644e680003407507202028107a211040f030040c81c08441950402140124514072a610a02d440074031200341187d0b000c0c21055031065940c1e04105085900035842880240d441c80000066640d017454404500c6a2801101000b040c07140c80d010305640040801c0300f021001c3d4822030740b07a440050b055a1507030364094087c01c03200040528000620007400c1d20140000210340015142e2000e00b40c019094030545129403c000800321141c984058004003a6000a89044004a065500158001420760036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 85084443 1250 85083193 85083221
    0x712060f0501021603020105030a020903011116031b0203030406110f0106030507050a0501031404022b050709051f030303020309030d060902040f06080412120902061b07050d0506060d020402071401 86
    0x1940300500e180440c8842400007c0c0007030000c202203107030818940c000d00702400c001000024120320946081000d948a200004c0401c01e0394150a0700785134024620040e003440c0850724500812540c1c3c0042c0d12449103026001c01c3c04601c0c80f0600c00004200802d0240d0840f90380200901a10307800c040396140c035240b2880d0310071182a4000b0503654401d0007000c0b4400900c4410b190b281d26640d00300010b032048070f00302ca055040b45c2a103441943c650b403c907a00c85a409500545410303410300001c00d041d02c400401c1803006000703111945906003404c07000c100803282c0501d40161241c82d0381240c0b90440c4200a2029180343c1000d40105203020f055000b88103e425403c1900c00306540c42d00c080d61060800c64010b05080000c11651088a000c1c0344020007032400c0d00b8002034801c40c180d00143c07498000302c2c4c02d0280a290391261924055040103000003030941110158a4450143c0d00d1941d2440010b0002e8020b0440c030b1055002c5444640548024981c00101d00b1000c40504440500820106104400d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 85085693 1250 85084443 85084453
    0xf09111002030a080103060903020a02031509060a09150b040e070b180102120403030302030703020f030103050a060501230409112101110403080d0209010e0a060c0b09060f040b0712060f050102 84
    0x5000004580da43d2003552900c41d0180c1c61915401c0080004410950540c044c40b0201001a941403100c0b07030b10203110710495011360600b002c6091500e07400508042c259454892040c0220b4006040780c0c400f0f02c074401d4082508416140490013406030801c0072440d600c2501ca001c03c1c983c200c80050001c80d041d0318019015882000012a540c0380c2c1d9503100040c095007004188003003846500110b90010f03003802c01516001000505040795842688251000d0300100d4404041101c6400340e1801000401c00c0b9000840c000c049891051001000452090b0343e42d21000c0c08114004000f031524400050001d180d20003002d03407904000c03115102d101c019504c1d180310810581040820764080da03410114943c1802092001000250310200c070040c18024212003000640d5200794021000e80207c1c1c0c0d440c0e200380f1f00c0d813401440c030140103020003203142c11020401402e8400c1a0380f45030f000c0c1d081001a042030f1100401540c0781010075040d13500503400c104010500ea1000703004801141c400384d00f126 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 85086943 1250 85085693 85085719
    0x90612021201060501080c1b0a030507060b03070506030a0903030902060703180b030f0a02030a1d1f06080a0201051c0c18090c09050f0301020904090606050a0803160602030a0f0911 79
    0x1d4202e5030306000b80e5001c2a400f20119506192050140c5400300c40e0500542070200d40c0070101d4036001540504600280d40015100c081140b0fa00400c14070315000c2d0001c000c40d5041400140c09400300504401c20b207076860100005245c441e422030b007079858002c1d00859640425080c0100000300340340d000c8030000015500059606894411a44503403641c8418106985401080d18040e602c0981421000d585505194080080f0580200c0780d205541c1c006025644002103248a0b9148000000800b103103402020042d196010811850301582440d043d0b640d041041c102c010064041005120200c0c42c141d41045625000300e58440c4024209d51500342d0f00b0b50301c42c1c07440705603240300c18401c0c001034402d07000b0400d504080c04803811115005002500b02048030011400f00c0d40b07110404c0d03554070740f22081044281040e0004902511a2102070340c9000000004803142c0c5840400040006500000103180031542c0e510000081c904c081090107444110704024140710204043c65204040c0b0240c81 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 85088193 1250 85086943 85086979
    0xb040e0f0312130510051803070201050d0509031e030a27320c131b0e010309060203042019060804020301110406021f0b010507110a09061202 62
    0x84040d41203400c0194a020600030060b8810750001d8001c2c8042c404100455000810512580c200110440f00c00034580c9004841041072884003480500c103901304028010150742d0080c03c4a8a5400b0003501181548941c20081d1952150034030b62480040c1c02d041d5442801032400083d4018586400281b005201020007400b00015004d414980d9403481032500e00000c4415070380c070104c1c100c10718034044e04013083d404092450361102c8241d12150040ba40000203403402d029070000825844a0170085c800304009083e400300c2e5001c1100701400b0403210508144d078801e0700310305445507010106648034106031501c01104165010801241c22180b64550382c6401c040a5440100d040e0301c0d069034441e45098010780c2d00c40c83c085c00903a01035499080154824007114003c1001b0b0116900038550303a9100c0c0d03504907414482c0100005d001d82030102240440c2e9010f81039a8600340c00c81c0034410b2505a01c0000b81d045180c682c08601e0304d605103034002650110030051000b074280203076038003010103101c040782e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 85089443 1250 85088193 85088203
    0x2030c01061a04030f060b09100305060c130605031003021008010e07080c041809050102040e01050a06300b100203180f0d08070302030c01090b060111010b1e0301110d0b040e 76
    0x30021200b2410302c420004a104c000c150781c3e000c0c0c018000020710342c2d00500407400d2417400b10760a06203003c0b003040410400104103c1580c2c4900701604040c1843d08011202009039074038450002000300200208420345200c1c58141c0045900400098141400f03032400380c58014248513010311004a400013500c1c0c54010b44405100e00001988945440c6c201b29038200030200714490080081e80c2c81640200154003440104060104451031980703661608003044044101504000208503030320551032204409050000304080325202d08001844580351002d00078078801240d1a84011000c0508901a40100040118403080003803c15884114401d2280301032902c03ca0b190071800d1650f1000c04100b41c0c00290a011b4800c0c070550349009046114242902c504850982e40c1550003020301503190307040f00c149014800c079600240b00710b10180700003171030145200310000c001051008050249503000c0d404100c1c000c030301080d190f4a403900280b4820040c000c50b80c1c010702840c500140000b101c01f00151f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 85090693 1250 85089443 85089479
    0x306010f08070c080d0e07080d02100504020d0203010c0f0f0c030203040b13030506010807080d0801080a14011e06050f0d0b070507051f0203070210061503090503040506070302030c0106 81
    0x11051400d8040a50480300700c80010078240400c000d401420000800318001401c01090f070910200d481720b18040c5460920100c4c1d0b0240100760b1040001074015600440c4900380310074181000030f01070b85c40d8004580181c603a080700a41c0f551800c081505819040010781b00f00744031642d031f80c00302c42c103901000355188400424080c015a10034001046800d040000400700340c80c18482d50f01c103581d500d5503407a140c14002c0e0001c0b18142c011078010300519108014190f0700081600d0080003030f500d006021501c2d69404c400203000042040700b100428642500406c20907005511001c5000072490381240003030001d030046520695810707419010340d01d04400c0d0399249507005548070405072104e00003503440d40e0040408071036900404001060307031400c0b9002c42c25100041c0b031001d0380e6443c11110007414003048031082c03084149444014000107641e189074000551003400c0000c1d031200242001880c40c0107547c0219888400080c9810402da0b003c4040c110b00702400d0000c5c0a072645804420401d800c81036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 85091943 1250 85090693 85090697
    0x70201171b0f0703080115050f03090106080a0c09150308030103020105030402120601080f0606030604030819060b0307030609150303050a0e01020a050d020703051b010e06090d0209150312090603060f010908031c11030601 96
    0x102c0b00b00307130009c1342d08020b60b004100c040c000940c10780e80e00103241c144000c40e039081d62507480c0594100503240d200d0003001e4100701008107011455095640b21545030006020103410000c0110000c3e045480c0c641f07100a010440800700c0f9480c3d80c0d42c20125542d89110007600d004c40c0200008288039080014a0500981e45030300c4e0740d6401d66909000701600c18020146209290712003000003000f00e020002540500910380d00410790900f04245103054500071120344000c814910b00400110b68040103031a0081cbc1c152034003407000200700c00102d103031484035200074059016941d01d8001054000a42204691054069500090401c51080c0741003074104d1070f20780070528050004000d460f0102c02807031405801402c3d4845ca40d01c64000c03c0b0300d001c045410900c0707200888082c40507880e08202e594500c00ea80c400381841c081e05a004598a404050042d40c01803203500c12581d40c0340c1c020f5401001070848201201d4890007108102100c481e2500ca07801e02c00d038070300304d040040701c080a0f040b20311400d41a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 85093193 1250 85091943 85091947
    0x9100902030616140703030b01080c18040c090504020408030408010c02030a08010e0a1d06060307050420070804120b070807090506070b040602090301060906030501060506070201171b0f070308011505 87
    0xc0d42103d410891910f001c2e003001860784140040280201c040c1081500a0b900000c198004c4400500704003400340540d810710310148485803814400c10551070101c5c6040e04c010651650041060744c4000d011b0b00803035486030010070b02281040000001d0301c11200300400070702c102e044204e0166100c1c07044243d80c90005001400501480004003210398100e0b191307000001d001c0386041159983d104480c040540303140c003c2c40500000e441c0c1000b9090241004650070414020601188980d00140d104003800c691408220003007800001c0044d1401000c408428254400551410300c410340d0003240c40744c001c2060300c80898080d51258560070150f8202810203464031805031511040403000520440d1407980800440100780c0f006c1c012800200b2100b00301081c00c604500c3c18034255051500028003662050002e480580e0303009620910021000d56990019100c0c044000c00500200c00c0b000444400029810259401ca50040c25081e0080d50f5583c0307141d0301c40080703000d403130102c0f00710500007001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 85094443 1250 85093193 85093201
    0x9120a150b13022b0c20030405010e040914061009020405090a09020d06060803040501020f030a14160b010b0405031501060f030b0f090906010303170103030f0e0316090203091009020306 81
    0x207254002d010008824004603071300b14080603183d45041d1070140c00800b41c4d45440c20b00b1002d81d00040520360a007107a02d15401c950564400141d82e0f40940d1041a04000c503940040d0050703200c07075020311021034000c280c840501c0d0700b9000441e91180c0a4662407481c440342c6500141061140c801c0d10b0a0b214001e1910821391a414190301c046c213400701082c1d07071004030001514002461480b07540c000704040800303151a949480000f80c244809010f0500d120307042042041c809a501099920000400411440c3c0724174030803544806109104800520306400351002103001d02e46c000141c411034100720120b99085014a8101c06030302c1c42842014045400030546144281c007036000b085050001804800d030351100c1c0c0d00041c95000040d20024160341003d00144103040c2e0050f800103840480711080c141d10351565a0081c201e000304d144401c00c2022800036040035540610912449140d0840403107002c035150300d8943c0080d4015110340c101445070002c02c0308450040e0107031802c1c09400030080c0c0880c0d59 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 85095693 1250 85094443 85094479
    0x5070b0f041103150910180f051609020306040e0d140309030c06040819090303020304030611040905090c0907020114010e0901060e0f0103050d08060d03031109120a150b 74
    0x80d10440b2000ca8460002c11943c60800c90410303c20703920700701a540340c03c0140c00c15041444005808400c01e040c80312600a01e0302c00e04259441a81c404d10504080704075040c4103061000100341c4818400107d080010550a0741c1c01441c083e0704101e07008c001404c1c059404690720f01e841042c0c2c03404640e088040c1c00101c0884030145901424440a5918000c401c400b424180202141c044811180c04200300741c441809800c0383c0c8110b80e031400c1036101207003140c402035607a005030300c8010505038032048440340050505003920000c080e100ca00b80024100304812a80b1051078492041c0144140c1300022000c0b4814001c0790b010b68480a1004400e9013408030b056034005008001c1c108035902d9880006010f682071310390a104261001441d01070754110300d0070724280407454540d281000f400c6801d01c50541d5501c480c4140c0c40b94541000075400c007450054045c03a0041004141c1d1000d4100c001a021240205080354020722442d03039070004d21980101b600488081429454129415000c50042c0d40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 85096943 1250 85095693 85095721
    0x918090305130803030a1805030d050402030102040905041203050903190309050f0604200102010506150d060e07030f1107050c0d060b0604270911010f111005060a0605070b 75
    0x40c000e2800c645030000302d805507400101107510140141e48000100031074440da512406e031001c011035045509030201c603143d00b035030b0303005e8002c4801f40180d407440030230300710f6a00b541100c5c020b2501220503c0343e4541410507010080780c00c140100070a0400c40010348424000c0101c1d200b01c0300c40300d040c2c107680c3e0300f140c4114000e02c039014080712544030703011610742100c004118841c4154401d2041400c9600b100c40e4a0786070f55034880003a4156170500d4240515940c0e0404070040c00c4c16000700c1951a0401d00103800701411950344103032151002c400910000ca03506401c40f04003924148420300c212a44180340300c0d030318800d070702000e019501710011031141840c140c1c0e002c50809000c5d003400310740301d800000011300583c0a940305480c10315810035558181900380c544140c000c0301d0303003030f007040a090183ca420f05616484100c0d581081000c1100380811401b850111143d041e14004550026618a006500070b0005403001c0d80700c1d074001900050850b10070403c135041d056004601580603150f980c0c84003209 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 85098193 1250 85096943 85096961
    0x1080d0c06060330080403051c0b04060b030711160b031b040b0d050702160b0f07080c0307020a08060103080d0f0e01022b0b030604020f010c051015060918 68
    0x302d0b22080c001002c204003c03642c1c03210345600c02401008074002000088045103a01021060240480400022039040003d42d120030b02040c0054200c00c0200300740b100104480703102d03980d01c40c3ca4150089001d0803610061881800c0301c0c0c0711000d44585030b1f003030141e9030f20715a005040d074080b0008092002203140701c060b6400811a5101541e080501003029806800c036801c0708121000c04101000400303a10b00542d03030450210300103031102e25040c00052119000e02d0103080d500a10008003804817041d90411114441d4200001d02d80702e5180050040d01c036800b0a00992040004c041c02080c07182004c1690b80c104c903130040d252480c1c0701c24520600f024080c10801c0d443c249694100901c5900c5e401e000414280d015031aa9509600303803051030208400b0003e501030111480e05201c07070002d417000103c1d1604150102c414203290015840121142007010400402900811407509150403042d04208005016083c0c44a00c043c2c580e0f00803940f148291081540f10701007240c0b03c00310740d1540c1c2d114990f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 85099443 1250 85098193 85098203
    0x120a02040c090f0e0702060c0a230d02040b030103020f0603061e0a03020d0f05010c02030a0906030513020411040303021209060405041806050c041e06020303010e10150e03060a0501080d0c 82
    0x11642c1e45004502c3c1d048036991107542407132007100402108035130501425502240d801c011600300110108020700100d81d84030458205080d9070443c651410f84941a1000528030600c2513507140d881e4001541e66070402c0c441207014040e03100b8980c0c46c528080b030580340b0466000d026443c0324030105540c0b980d05514055000d820000301d02010016840d000300e4002d0b828050300c441840904246082800c440742c0f4080c2e441150414440c0440c00c03a030000083d000c42c4c203245004202500c4000e80b140c0c1c1101440002940140f8040c080b28260446a0203041200c2c041d0302a103d82984002606010380704a484655200740c0400082c409441c0c694004009001c562001c000b9030b44482e9074a0701280c0003984d0300c8042401c040b1b410032184003680f50944020206003000d240c41c62804d00045d540e4041030081201d6200802c0c0081c0c083c00c80b840080008000ba841280c5500c0d45891001d0041c400c1042218064007540b000240701602c580a200c1c12034000d00001c081600f501c07101107820b840e014104440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 85100693 1250 85099443 85099457
    0x9080901050711031c0e030703110105130b0c15010b03070801050409060912030f060503070f0e07140d020a080117101820010237060608061003060b120a02040c 70
    0x3626840401c405c00c46050460050b080514034603a020340b44112007604148664003a01040c03000960074208461080400c0c2010340d25120f4100c652894400c0715009411000c0b40810203404a1000090300a1000441d8460000036601c0d2100907100c2d10007100c0c03102c0810912401080300b0309082e44100310941c06120005800010f0341c1d40e0594803400354169200080e192508140c603c07403d07202d200e008100440040409034540b0030b0080b081852031143e4000e806880d00004c408034044c0d40c6212000444c45420b658a40321501d142c0d0094200711000d00000d40b50b100041030a9407081b402c0b40440ca8240001c02d04418480b1410020b0b000700710f58024041c040d1280140000c02c403101440071501a51001040350003820002440c103101c6000c0504150103581c60010311082c3e1070904400c0c140024994039005a00c0c1c10300781701605881d404003c00d48528010008582c4d40004802c059912030741c2c0c1030145890346010450240d030403050440c2c01d034001c821150014985a40614103030445414100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 85101943 1250 85100693 85100723
    0xb010f141504031203050f090d020c06030a15060c051c12090c050a0e06031005040c030318050612090c2407020a03051c030c02032809080f030702040b0301090809010507 74
    0xd044e00102110820119882c1d40a004c21103098808150b80042a600109085904100003d54584084a0150042c00000049486514280c0040f0390f95080f0046e6114500e5441a0041c2a803410301416612806a4852024440800c0c0819511000c0d541d403448001080700d4440d0000302400e040860b1894a15940043c99445a00f4018020401e034100580320f1310708181030608202801102c0440246454100300009018200301000d0b6909403038901c1400a10303030710f1070000000641000d6440600800c8001c0c08002400c01140301c2e081580c10b46500e040782000307200415074540540c0456880100c0708149048011024019060000b07020b02c3c0b6149c0d0300e8443c42d0038102d610b01207030341019420541a120b2074041c011900388082d144000d515005484500e00003003000004041000b03000000503070b40d03d0780b03d4644d0070090010b01080c0c1d000c0000d82802d041e1b4075484000704030f0240e07060807544501490184141658a5041101e0070715042c0d00c003004469030b51010a00712070400c0c0241e622 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 85103193 1250 85101943 85101953
    0x30a0f0501060909050f0c04180b0315060f0f0102070b1614060f0c090901060309030e1305060f010306080601061808010c0e090610090b090418050a0b010f14150403 72
    0x458001c1c202c980b10116040d0401850406a0f4001441030818249041c14800307080444000c450403500303940035811b40e0300841a500c20151458820403030717062158440040c01d4603c0309d80d906008000440e501c0440d41505000d00c04402003070700b274541c00341e0803000080280075842d00003840c01104020032001039280b42e540300b1410482a0398800e00c15845103040110700500c1851480d000b283e000b90560030000c0e24000a480804140284001c160300d131a0320004241c002c2070740c0803074400000d207281800784582522000511048801620610480458001c2e65010348039100c181d0700307608050016a800c0c00001d665240c1d206031541d500303501120f0005101102840b508401550644c2c42009810780c8104100122101400d1548218014880d10403225008030242040320040c591035901d50f0450f03000980203101c000c45a05034038240755107120803c9804201c0075895842040c803580d199072240b44140140d4542c2c00307104600c403010301942d1406c0c50300305440000c801004015901e015120390350 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 85104443 1250 85103193 85103201
    0x1b15070f0e03120a090605041a0702060f0c21070c030210140c0312011a070f03030209030a0305030610091203050d09080a030e01060602060c0d0e0307020a1706061e06030a0f 76
    0x203035840c540d01c0404c85100f16540614080b005102074507040f4207044c00c04003054614030059500204070500010a00308540307600781510000b0a000118645440104030380c02d49407041c0c4007916032103001c001c041814101d03407031094500e400c0d00b022402c0303046400c580c00c0c0800c0f4110002071105004609016460103140350300104043e14281015580305c1015004500c0030000681001d01c2801101c0c050410440360a000c0d0b91005030401030103402c01040f418103500a1142c0801240c240c024088401c0516800c0801140254001e403a2a01c1030b141540381203490503510702030540503648000400020034400d001034891070264030720015296009556102d8503030300020044020a03141d07010b00c02c684d5001e208036001040d03540040c0c00c440c03400306103071000c0744164040300d444250740c1c41120382c8001040003a5a116030b40034100309450303905da0340210140c54890303001c46d115124200000b01241440141000c00b4800401c0c090403110b42e14040020300c5d00010b100c83c481d1030703413050301002019250003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 85105693 1250 85104443 85104463
    0x1c05040804061d0607030e0d060c020708060604050103020f280609030506060409050d031802040e01060f0801020c0303150d0b0f09071a03060d0f0f081b15070f0e03 72
    0x10035640381e107020400703007110705181000102c500c120b036290581615810300b200c0843d9410b20b8150b0100c810b22000444c1c99444100241009183c00070007509660001441b106644813802250b40c2580c41c10100829100240002900000200c000303441c1400c1807030880c0011000c0c541500c80341d07600d0100200c00d13041c0d030f6484a00058444803003002440070601015810840c10f803402d2281c0303040754441c945d5401e5120901c0003016559079624000c15001f5070208251580208180b041041d180c0c1103d0103001940201090322214000011303000005108407401c5465481c00303582140d071360904100011014500c982e030000e036861440b20020340798641e66032140c3c0d0701091101003424010401460074a441c0c01c85510700700108510521128005d060343d41c480c40494111f007070395a0502e41280b110038110402408607090351034040402c110600540300e125540354600000d40c003c41d01c0c0d80c1d55001c0b00b0341c13891414511540070900381c51044016100d15401d44c100840e003850307030300c0109240c000c1d200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 85106943 1250 85105693 85105703
    0x312040b0a0c020606010903020f01052110050a1208090103060b0304050a110102030c07210b09070302030c060702101101110a02031902161509170d0e0102011509021c0504 75
    0x10040104051072441076008000070b81c8001e041c10301d802e4002829910344c034040640702d03101c080540381c8568030410851f013411016010030300d225040302d00c2040c0551400e0354989449103030143c01040034100704941e08121a01c98800f00030b02c15894076084560360113598803d0405899090101d40200004001d5004502c01d00040c9240c240c64201a030542c2410000241150002c0007070030b0740031074001006400c0e204c905c0340e0b20540b080c54060002d0081d1100c0d00c0180380952000401c2034441001c0f9074081120b000b541034403207400000080241510900f400294000703003909081030054840c20442e04080d0082e800000c2c0030828048000d4180c111500b10b400580c000034042040c040c2c0d09158026107500c0c7c0c0000c060b80c5d8025000160122910300071100c1070203150603842551413045d10504000c1080c000707a04005130304010490340717410141402e02b01040b00e6034403100c4654414426420555941c841001ca044c1c2032000c0003002e94410030404519001c5d8140c9208800c41612820f4003841c861 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 85108193 1250 85106943 85106963
    0x1806050a12050c0f180a0b0306041208010b0a081603090503030109020702040b0414041e0605010b070b2412100c030203010806010e01030f020d0302011b11010f1b11031204 75
    0x90b240051422940d81c6905001c0d48294180b00c0c0d0030f03101d20f0b401d5081c43d44036510340b240031350320048880d009107420310301d0a605104102c01d0109003d40c0140b000e0082c2c0c465900c8150581c1c8800d4840725a125081c4514006241c45002440054841113000340b0020149004107410001d500c070382c0d2941d0003c4e003124010b030344d0009101301103282038403030f110f5003500548081c0440d900900c020360202d40000d002601180d80d00540c00c8030882441d0442d0b0300e00ea40720310200403d503107c0110803c15084404200e0308034400c900810a08000707072140c0e04400c1440403581e141e480301c502c14086220303216645001c1503c182c04c0700302044002406000742c01d28a6a42c0144c40e0762408218615044041c0d2084614000f6100148003268910030203441c0c00f601550020380440c0745107401c0f401020042c07031000f20403c001d24070b851840d6000202c8012103400c0002484200c0da502d1586048034120400c814000b000c17082507100b00390248d04c0d200c04000c0400207603401d2008400800903001000c4808407503c41003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 85109443 1250 85108193 85108229
    0x1704060f0b0d02030d033201061103070507140a0b0f09031903050d020f0405030109110f010e0105030a0906020c0a05370b10050303070f0b060108101806050a 69
    0x41841801d05a550499081812422607004031703840d915240000f4003003545500840b01078007030072000d1a16085d02c02191418460f0311403aa00c000321001c0c00307404001003e00c0040700038400004252003401da080000707850394a1901c11240080c42407001070b1a00040780003800107000390150042d00184031140115565081e50800305428603480701c44c4403001e100e0741260388000c01da005c025110305d420041d40050f41c80100c486014058022039101c0c50b410340c00c01155108000c003402400c00000300546210f00c2180c403000040d1004d0704603041c01d0703000901c00d00005044100300c2d00031181c0107006d01130061030660006c000b41c1c1401d500c9a825980c40c3e1000842d1a080c02105140352025010b074095030b004400807140b030106840030450003804a02180c0041000c00f40690000c00c000c00b4010708995440b100c51070101013155034601c3c10350b00404244009580c9500841d4202d1042e010b10400001881c1061018031010741c01340c1010158690b29a8040344c43d40b104403101000e0101c1649410400f10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 85110693 1250 85109443 85109471
    0xc0d0518030c07031b1d070302090901080a020a090231030203010c0c0b0f070507020111010608030310030501061202030a0803040609021809100c09120303020715020408210a0807170406 81
    0x2940c00402c881c580000800b00007400c00d000d0000e078040c3d41c3c0b40c80c1b001e4079201c0e80e60841c0a4002d07501800d9000c090325000117003c003400945103403182d1007038440c01441565034045100b2070044600e82003400c490ba07622108480140741d01c00c091443d01000e1110714946940219084540c4a00f060700426030b104000b0b070034445009202507005031401159107882c542490024404e0040c074170020305014400c001c4035030100003074025801a106510032a5124580400318814907040e80c8016101035180c80d9011454100b032558042903103030040d0050598540680d20b03807025501c0180261000307680d0381c110301c1c01660703111050040c61292002400481c248491070174204514100001081d81c030700142420304c650841034500c1140d8440c4000c0400090034181a03010780700c1d07042c00804803c03480501d0b0750340a0f065405081514a28400c844e108002e40b41c0342a2009140403500c1c001a10238000400c046104204059010a052a25000786100c030007080d04d4000741075804984aa440706a5125401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 85111943 1250 85110693 85110713
    0x180b1b030406020a0803070507240606140f0c07090212160e030606060d0f061211030613080f04030203010518060709061d0303210403170c0d0518030c0703 68
    0x111496029520342490414081d40e281040903008081210200c005030200e03020b0001d5031204c940000050021400000150702d0074083c0201e00c04256242200100d4241c1c0b06000040d24183c03010041c6150400c604d401641c00d401a1190002501c2024400b14000d2820b00180c031614100050300c02440c1001c00b01408401180c0c0081d204104d403007000540305650000d5010340002080d503015540d150b8010024015016100c0752906031030a010000888012004044002d14040d50486801041100c100b58684100743d6500d007000145c80703000c10101c0c071160010101c5031071070b0342d991f0320b0169203030301281c203413001160f000341c911405032131402c0702160600c0807030f5200b4110f00c0c1200802d41031007170182410505001c040d00c0301c1032002c410050b9403410011146804210081d840040c500101600300c048400c840c21000554504c144003000200f50140902076034407181d62504107032620480e4401414010420204002000344190420005100600030250702002424805007581080c4040c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 85113193 1250 85111943 85111987
    0x206091605060c281a1302010f23040806090624040f050a090c0501030b03030a05161406041202060601050403060e1501080703021f230d0501181a0303090f01180b 71
    0x17405d505020840441540304100b1304050742420100c500800403141200e10004e5504100101c030300040000101d080100040d1003142c13900c20803134100355142d41c1c2440e1240010f4400c41c089448030048000c0b066038003000622803803006000020080f4007000f440c016604252501904140c1e0f684c2c140301440303402e52810000e00f00c282020300580300c459000c40d640388519014001001400f2a100241d103059070724042526401003002100e00302989869919080d0640d412900c2545a12a0601c4e00d400030824a12550301610790605040c51503c4000240510382003c3c03441c0e0140c0e20702e002c2c2802162413658060141840103100c0c0314294814441e203081694080e1004201000b4440d0380250301c200b840f0200e5210540d801c0348040000c0003103940313002d0121240b01550038140080b649124a4040300604059058140403103040440c8200410042582c0ba642540003040074540d603081c01c8602c030740880410714110700c1d070780600034490540240715040f20744040c80001d003d1f0340d49030b10b0601e15440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 85114443 1250 85113193 85113233
    0x70f0f02070e010501050d1b051207030b220e0601030c0503010c050f16080403050a060c1b0201020a030f020705031209010905010908060703050402011101020a030902010206091605060c28 82
    0x2060b818100c1d10a1101014881e0b641080310001d10b039102c0f0340c1c65802070150840082c03800d86203000c01540203031254001146050705241040001015140b1900481a420704080c042000c055650701c0c090034151a400d03043e42200b42c550040b00c0c034002040200c98004c41c05417124040c4c640c184020142960341e403901007010484103222003440c01d00c0c0401150030b02070b0600100c108030112442c0c0702407280225440130b00a80541c00701c18007800700b607402058030700d0f02c69038a411148240140d100010304001001a0050340f002d43c6840c0080c1c0200c0c040d5450180900481d1041542ea20029203480d8a4501d80000c802c0045800155560010301c034402078182400c26511060900801703030b0340d4000003410b442c20580c840010605690254002806405110000303550315003e0780c0c001b4001d0006104224014415a4001091185d020070903075108590f40300051303004e614003020001c882d0041404a0307050f00460454412424a40348940b001440d6401341c00301c0c1e04658240543c0c07040d0507401c8001c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 85115693 1250 85114443 85114453
    0x90327060f1d063a06150815190f0306200a0c080d05010b0c070801020c0312180312071e0c0206070311010c050421050c010c060e0303070f0f02 63
    0x1450055070440c02c050140603903000352079a182c003085030200c0c444611002c2080c010590b0051915040c15403080c02e4420303040003400080e940d00c000c446424144480300740000d2214002c0307510070396646030204071200000c2c00748207000618140003c6603550383d4821120440c041000f04100001402802509034070b249803800c080c01c810f14184040c1c4200c0005508100b41d071500c0800f08080741d0241c60740c4501034041040b0a607152002c04035141d1000c05456264442e00720009901c2c0c105000700c502d107004000155040c013600f40d044480481c000b40c00843d031038010042503070700319404001911104100428000b0a401c0c15040a4440c119811000e0700c0c2c2045c3c0318030f261080360041e030780303104503a41035900741c2ea16401401d04460314040b4940c0c05040b035003003842266015a21001400aa500710001c0300200c20160b07134844a03042c04003500400c00e41180e500c0b8805036004030740c1c0d112058001c01020401445080c175041c103680c0111031600204183d0440490314079800916814903a441d40000c0c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 85116943 1250 85115693 85115717
    0x201090f05060304020d0c0902040b04030204290f0109050301050a0c0809190816060903030c0e0103020c0601030b1803070501270b010e07050702040e0105011d07090603090327060f 79
    0xe01c907100040019006880300c0d90000204007c1c07252020007031140c2c560444d02d6503110020740c2c49030b61003407100b603101c0c500f42140701101c418000b1a07160b0508484040030004508030060004895515034018144281c00c0c0780020203840a001e85485208030042c0001c038803800034400380c0609000f5014802c2c551180c920004d2061486103140c04c025000300c4495103500466501c800010245c420060264ac2071000346810036801d43c00596203a40ca030345861408080c3d22004400b240900b100300c60700756004100400206155800c401d030001d1642c1c0160380c0f90f17400140340510b182d01ca0202201e8030b0b0341d102036610201c04001c681492543e5038103c07000d805101c0d5114044212010b002e07460640c503681c8007280403540904100c440166020300280400c0d4034007140710b4024002445826001054800d50404c3ca00410b481c0794841e1030315864028072141845003c800814050a003201405805910346aa520440e41c5d60100712108e549488580703414440300410749105521300a0522407900128 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 85118193 1250 85116943 85116949
    0xe060f09060406090606171605030a15020c0109170405030c040203090607081f061805121506060f1641160b07120503060a0918021203070201090f05 65
    0x103103030410742286010400c8096400c0c85c2005190550100019099240c0e49059280d0702048034500c50b240c510418510070f903104285600e91540d00d000410b00392003889962543e1129501400c5065400d8000082c654007a175030b0002ea601c0916008550742030f01280c2000207280c1000640d4010324295804d50441c204041c0460341c0e2080036100d4800c1c4240c420000c0c00660135602c883c0d03030100c1d141c4041e0019a0b43c6820180c00c09200c0145080c7c00403248501040c2410700030052001c0800c0200201050129492840b184110250100c0d40c400f9081101a1664070b00d4000381490900034a0702c4045503120b8030300350001415020703070349501e0200d244100c0341515540c070324000d02c60244a55110340c100000a21030030801d48411200385945c40f07100102d01035190801900f4214442c0440c00000d4008000996050104551050380680c0300002400310341a1500191410948032400d0304000030390f6400035080b21709460041c4143d50000c00d1203000d640c1e01075001001496003000c6076030707018240b8000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 85119443 1250 85118193 85118203
    0x803040803060d080307090e09060702030a110106032f0915101215030219030809060d0b0d03180b030103050c06030606120c0301030c06030e1b0a0305100e060f09 71
    0xd081410007000058554858640d800540d0b50b00039862a6203252090000c0c00141c5c0070b0140c034250040103000a11541c00014089014003010340043d81405180002213498114483d8000c003030355281c2d85d0000001e101c05440c1030060503c900b99200c0000d40401001041c0c00d600c14080c03103003440c4800d000c1110742440f913900345003a0680c2c2d4540b1400790000151036480a000c0c04101c9140b0740b400c00c10742c0c01614a4a542500c2c4202c4034502c2c0d020b54008411101003075400003524201c400c00c05100d041c030b02030005050303807550100b0109a8041090000d290184a420154040340307011a0b2500c24182000302c2d44081d210382000c0d282103504646513599151424400359020310b20010209006690f4501a110b005c0700c0e0310382200491030100414103180e0020f02c0121148413040134007090300b6001e0300072a0241101c5034000c00b4840d00c1400301a541c0c0703102c2088160011405000800861010311050400c0410208042005140004245e141c10401003485140400f4202481a62000461 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 85120693 1250 85119443 85119451
    0x708030d0603060b19090c0c0209130302060906070e0d29060f150409051e0a060503010b04060303081302152a010608030a030f02040b0c1f0e03040306020310091508190803 75
    0x500143c1c40c7c07804030054640721841000603601c503401408020b68207294000d041e0b0710034070a030700303481c2241c4030268003d6542a045c2d600201140f00a840b080807820700c107881400e843d0190780c03201803418280c5400f410701c0761101c900d10800e4444404100305410300b00c50810046606a8103210401580050703101d4501660203803c030415100c20114103c035517205a03070303003c030080c030201a001806c080200900400c41407050f10300035420040b001100c0d2070240318040c1200d406071580d40d041d03036444100168030201244126845045103100d6010360201e20064090001c404003011420456078003c541c50030b1080e40c104496071704012081c42218804000c4d280d4082d018200030400d1440c82c01c11002900581c0c0040c02c84020101c0c00045000300000c48180003400c40000e044c101d00c00c0b1517010140d54032044465419032040101300000740ca04da000710f6100d00074019045100361222204010384400b8011600e40001245050081d60340501c00300c1c0384070f561040038241c141615079915445000044c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 85121943 1250 85120693 85120709
    0x2010921110102160311040908040f0810021227030d150b03010f06050307021005070905010305090d020303130c0f0f03050708010c0206070f0e0405010303120c020703021c050708030d0603060b19 85
    0x11191251b07580301e90700421802a80580400c0e243c03910380b10000041c00c40d40c81440b0f014461003d003440c8101c014400c642d41c000003d4164106655450440c2030414086002c1403082d41c0c2000304081540c40600292890400d108008901940b480b4580f0b041012180c105803802801000100700c00155004414120754450420f16141c1c1c0d0303034460036030500180743d114090241c102020490305642c0280e4400642c0e02c240c07070410480d01c641060607940ca08000300c076400343e84100f000c203016a440c0610320b00d03282c0c4030383d4101914540f9a403c1c1291004694420a003c035107004040c810020240000405450384900820010981590084d07171120003034107100502041844103120b5a1007110359010a810241052060356507a2070010816000401a043d1080c036104041c10090300c00b054507011680c004001486441c1c04a0781d1501c17816080c03600f01e41e24803c21000140f003070b00070b20241c840b0803c1c5150004103145181040c5003515a0411740c2403048641d0860084000b8001f059181610151 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 85123193 1250 85121943 85121963
    0x170c032205070602060610030912080a09020301090614090a030f180815070f020a02011202030c090315040302010b040e061305010605031b040605090105150304020109211101021603 79
    0x180502940d20a1458010300140140d8030042110380d00001c0441c041d00080d90b6059503569001c030110116001030f48001e002c010f40c0500700031801d1065108a03004140d4280004000341c20b035000a003103520702c3c1d4080310b00342c0c2c491190348900c4000103061580032040d00e01402580e03089aa0082070a001e68004000b8840742107805440b04500b102d12030042d00700b5a044400b03d40341e24010030b400c00b5088a80d04006890500c00c1c844440c40403c10300b15060b03041c0c651059204207008094041d4000524042c0308481c248070400596800b00310081c1e0b2107880c2092046030342000d04000b401d450501042d98011400c207903450b160500002001c55010202451820110680e0700d095400350040383d0246505d4801c01c0e025240401001c00b50010b0400101e40030001c8075601c0c014081c10707a9091140319884034052414080100031080190380c42071051504141080e215230143c54134881406071a0301c2c0c00300005000040012040d01001d0b442c100340001d155010340785400091040317043c00002c16022170 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 85124443 1250 85123193 85123231
    0x41703070201020f0403060b031c090506090f0a0605071b050901090902040e0d02150a0509031605150406020c060609010b0a1805090106050703080a060303020318010c06050f010501170c03 82
    0x400c3d41030b615501207003e126a510380c1e90b414894050010102041d2290103058003c1c0407007840003541300d400f91642d417944800344d8a40410040b160f00300b403082a0b000700b02c1ea51052071031b50b94042d11034090062a15250380300c45050400c104101601c0400302c245125078401489940d9503d03d44a04403500080c0100b0000340703d2001c640034241110344078034240706040c010105941c0104014091400c2900002440e03034034071158506032982981c05034940d4004019001010410100805641d4020750481d1101e031708001000856a2003200c099591079400b2681c0d100d408000c1c06403682000c81180d070660254103002d421003c81c480c070b86000303052010b00491200b0a103260040340c002014010042191344d0f0b951800544603a10102044001800040014030468442e1040d00180ca4269000f1400c00c40359213503007043c0180301c0c03010905204980c50580001952409190700c110030840e00380942c3c0d4907000024024941e4001883c030240801810000c07200d0b240c405480e4880d01c24800240f0800c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 85125693 1250 85124443 85124447
    0x5120918040b0601030b0f280806010905191401090b0406080307050102070b07080903040506070c080d02010b01021c050304150b030f010c090b072609040603032604170307 75
    0x860320118034900c901010811003030245060344203203d0034080e00c0074091007a00070304000c0d0301982d554070640d000c2d040c40791010000c501d00601c0e00e01000200000d54055843d45a0245485001da100f14041611142041f840030009400b96400000c1414284203401228040e401e00c80014001c0f9180c0e2507880d28601c40c1d55945030040401400080143c954a84160406038040d40c00200280c136040407580209a515110b030189070b214101c6000518142801c3c4002c000f00c0f548000d0098648010391040440caa140070700030400200c00035000003d01206140000e0300307001c0000460703003104122030650520f568108003200e41c80b0b40c0c030101000743c000c001941c81c8020704083c481c1d1905446050101816148150b00c000844501c903210300d0f001070b0307480a8080c1288900580285040d40c0000006842c25200801c11880310006040c6801e02e900322002c0340460b052544240d000503a100b0492402c0050142c0902d140015244140014a41500d0300300204842c01b61104c00b0050000029541034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 85126943 1250 85125693 85125709
    0x30c020709020a09030212060c03070e010c06140405010c1b02061606020a0801091103011a03040501060314011a090403140319020313020f010c050705100207050604151407051209 78
    0x1c84604011910f8801400c1c000b810b0428900003240242d401e903d5902209500081d140d2049032241d262615554881c03800719040400b04e45594140310030602e900e800106c1500420491555240d0200c005d40f5040c00c10600f52290720200c00244503484070740300d00411816410001c1c054041c0d40c0c06581c4c0d10341c0b0800080400001c900135100501c04100f104810f54440ca0190403074075100000d01c00c40c250390005990a03c028400c401240d040001e0a140c0850668050340d03101d4040c1c000002c00310b60f44c5c0c9540f05049005001540300da5035800b500407845030401c482c001345180503126402c0380e161550b400750140080d110400b0603003201000040882140f11801c3c4804c3c1e59480e001d64490800d4403242c0900120610101d11820800f82c0398407403540f190180e030940316084001030414500c5c1009010015544010710801c50060700710105180c1c0b20040140010702c402c046134030750f64810701002440c03510032a5030440400c00030070001c030110354001940d2038601c586000003a951954480021240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 85128193 1250 85126943 85126949
    0x2031b010801270606090305070b0f0901141e0306040c08040b0f04051c0f03050604090f080a12110a0905030d05030a0213180504020405130503040b0c0a020a030b010f1a0a030c0207 79
    0x45013024008039420380c1c4030f2168821207110300c08503840691103402c01400e40c091008213042c9224244412140c035849100c08050440003107080901d005655080445208805541071141080000c1403250605080c400c20f11100010b281500e050704080d90303901820040a4840c0b45002c890501140a00500344a0607114070b10034031682288111101000c2c2a50088100c1c8202003450702d000103900c0c0c00c1a00410300c4e2543c2c0100080460f440d95541c00c0c0c65500180304510400c0039401e0b00079010003092140261000c4145c540985511a13441d00a0400c034064020340e00940001107400c1060360030034180e80d0800b17407107040907844460342e04800703416130001e5010380301507203103403550419140c0590f0000d40140d00903a4140202c0d62030600c880e003a449c0d50f481c000c00350340c410002007102001400c05041414840740581d4043c070300d190001141d10740d081e082610328a80000040010300d410201c404010100c08104074114542034040c90024010b400c140341c1819140c1c031010407164405d00111010b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 85129443 1250 85128193 85128269
    0x503070807080114010501020c0d0c090906270213020a0e210f0c030a031d090414010c0c110913020310020c010605040b06040612090503041202031b010801 68
    0x11240da200451592810301d841582100d5181c8075220365040b0403480706034107a64041e001007034400301d103505100440f030b400d400c26104540c40b042d02080c0030406000d1861b0b01801490003151081c0c2200d03100e0385001c4e82040c440f0010050413410401600d8034205c0740e81c09482440016154001c07e101640c0000700c4901e03081d8440c00e2560250300007903880c441102000c0180c3c085401e00d0f510205050782e6181000e0940354552700060a110009225580c40303041440040d42d0042d99042c08004104000001d1364102c6100c50710240c903940d005001d10418031480f20516050b00c3da00c85503182c010441c2c1c0103200140c0180b0101d0000b5075001c548c4040c2100055018080321020f0810480381c030000d400940d070001155003003100004041c5818014110310040051400307140c2450440181da0a041c0ca12454024586400b01c203008503a061000c0c0c0b009002c4002c10b40d2845c140c500c1094244044850702080203a81c141070300c40075036440b0400d9810b5410500200043e2807199001800c82c8043d540c003d84 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 85130693 1250 85129443 85129453
    0x12060308120405010c02070305031b010e0d0f021b0d0602090f090c040816032a0305070e010906060318020f030a02040207061506020303070e040b040603050114060a1502031b070503 79
    0x680c1414041d080c0e44940d000f81c00070044014a401c0498403049030303220242181c0c0c02070104250100c441015040c00c855131100020300c1c44c0c00c04030340c0c5080030080001c02d8045039a50801c4110640c061060101c05907001c0e0b0807604541c1c00d040062400040307007002404166001c503141038180c0b0b07449a14101c2da40d000388002103902d0f1500c4100b1242c3e12500504070140280d000c9410302405072501202501c1d03110702c4000d494107000740c0a05000c4002c540c20301c070f4040107000000200d081804003001400240000ca8080d40c1842e8101003a1001a40620101860680c001d0031042000380d1681ca4a81d0448a0505207000c410000c0e1030900002c0340070307500900c00200582004195031107012106044007002110b41e580e00001d070b80741e0004541d48804540c0151001815107060b520076070a14a0050000518507141d4950a00310703540591944072524480c4140318403854040341503401410f140e01080c5103558080c800039184d004d0303040c0808050500b0005032000c0c503000d01642c0083d0401404070381e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 85131943 1250 85130693 85130707
    0x70312170a09120201140606280306030b1003050307020d0204061805010302030d080603060a0507050d020a0201020c01111e030a0b030f15100303090e130b0a0902040e03091012060308 80
    0x40007040d032100c045443e65030007260392049038010302480006242100100d4103595954080c401c4560000107800d90f000074111041e8402651107050300075550859600203000350861400204905000e09404810f00300082e0400c000f400c0081140e00480d41503c4c0c00c80c5405003840810094543ca1b007000e8807a500d480d54202d1030311120f6005604890088044801c0e0600200d030a0320740d044143c032004d0f0190401c3c2c1c0025946002600303c180c01c6034480c50924a00346c4030900010490304800d108a0050b500010a0307079003110240a84a809100d541c0c80360702d8100184002041d401004e00ea411140c84040f00085803210540e004901d95100075060b038020038200704000b9140c1d00344d165540701b8088140e0106400d8800c4502d880207403a0f041d192404420300f8014210a108001011f004480c80399034a0a400036201c00e0000b070003054012004a951000da104001c00d842c20700c2404c02c8240d0060003204802c0d95980c507080c5801e0f8190500183c488408022600076100f42e400103000c000c0e000504c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 85133193 1250 85131943 85131961
    0x1a1804020301060f030f0203041a041109070503010302180f070f0c0f0b07080109020414010c150608010c09080102030c0d18080703180b130302040b030c0d0f06050106020f07031217 79
    0x30000c02d50069030300300300a5030091409407c9000c20394018040491500b0b08040c540c10712a4129080b0b4003a0501000c4402001f0005030850008c032074040004001000410071030400c4090a80b00e04107107000c0003264a0418441250400000c0017031040080c2844000c40380c034001c821201041e0740058019508054500b000888040180c54180c0001d41950000030265818801d0301c0c25220701a0803045400650001151010f00e12041a5400d01202110a10320080d0780314440082c210600080b83c420f00c1d001d805003030500c2d1a4020145039004100b003140c090001412101004c01d078030000940950920948110000d800c10014429100060100c06241d003000c00c0c11000c031a00341140c03410944030080c4540f81d000300398080c900101c20b000244014a02034202260414000c0e0880e503200c05401c0c006105003281980582d4045481681c1400388609805014050800d60004240111220740b0701c55440c02c5031302c00504400c840d5680c00525900c138203108d00c0d858009110340400750802180e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 85134443 1250 85133193 85133207
    0x902030115051314042d05070507030c06050c07080a080f060a06050304060504030e0a1706070509030601060810030b0a0506010f1407110a050603090d080604061a180402030106 77
    0x1900500c030310102041d40095105108940581c0c224074a4207001d01d2615201e480107059141005174020b44581440851051710008024111060b400341003112100201c0041201c0015010004001c001c21250300425042294950001d6020703200064a070f0f00d0004041b1380303004401c002821028001040c19140e0750000c10b40f401200d24910038101e40c1c03903440400c40c2c41661403043e80089002400050b022403070503840154801c0c081e00300a0007000c081800104010965001040b258903200f0300800580c03020010941d0262481c00e1542c902007100c1c0029075541014810501000103c81c0041d640c1980c1d0040240110340c0302c0d031003821504050364204003410b0203c8644d800136054400d04021540300d42c078403d100100004551b0300d40f50103515044211440c04c20304a41018482100140988481c0f00451080881c40090303c1d081d031844000510b4000301034600d5100d681021400d0000302c4c0440e802480d070450760501c3d141d0320400211001c2d5080180484203070f01c244040b00005501d074100308 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 85135693 1250 85134443 85134449
    0x304051005010e0f07030203091230040203031207020109120f020c0328031103030103080301030c08030406120b0f04060609082505010e030a050307060204030c211101090503060109020301 82
    0x6014001030781c03a1540752294207000c980504d10101c14a02060782940203500841d040611b4505079640010b030300000780c01d968010075500c0e0b1011900c0c130041804607410160f403a060906008000c0340c608250b00025a02e008840000d140d8451000118036058001d510406003a0390119007010b55040013040074019880740038040c000b60040e4443c02503240340100d85880046a44080001c00500006680039580a0300c0422028410320b010284d2800328208081c40c0214400c003c070580c4c3e581585401030340d410040e880101e256000340014448213810114252140200070400141c1e03a400c0d900013402d402d4541280f68120345442c00101e06954003035082c0f400d13904200201e4100d451400944c6660305d4012641005440304280284490f41c400c0c244118a444010700302c801c0203003551101425035010000032a130f800d81c002001c000300811511454010424450412007050f00d4100403c0e002880c240c0040020341c0c0c0b032803411966130103100031030701824018045480d0f540e1120700c00c00003940280 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 85136943 1250 85135693 85135723
    0xe09151f0305032107170c0904050405010c02120c100c030f0c0c02031b010c0f08042102010e06040302010806040b03010204171f06030f0f080d021612020118080d020906030405 77
    0x10340c00251303520b20020030034015a61a61034400030108640a0402140041c01c2c00800c901d00304402c02c055900c41c0100c60045004200004a440d1000760180c41c1c0200741c0351070001031905004501d4044804100107100000c200c0010804210109003100200500c0a215078083c2c40c126031503031902c0c0c0c4203010300440c42c8290200d81040c60558414540d112540390070700c0c00100403600303900c0003c01c20b8442411052054802c50305094070381c002c44070441c02e0010319a241c0c1240e110302406660f41324129681d641019908907203411b0031034000a0001d8801000c581c000e40d11191401d00988003541110000e005080b02c12901500d24450350303454007000b8150144c131098605d0301104c499002e200d9042200d5011404c541001c019a1310302c169104440c1080c0d0740e03c103050208408480d051300080030358807504094070b03007824071500d0051000b401e4020701c407045a141c248401040102c16000d00400350b000000c05880e0030754104500302034407404000c550800408010310041090009a05100540c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 85138193 1250 85136943 85136977
    0x5060f04020d0c090b13051210090308040b0f0103171303020a0f05010801140109031b080d0f020f06071b02060c030d020403051002030402010e010c11120303010f0e09151f030503 78
    0xa01840303030f86401800d144006c08540b4040401940c5456911803d000c00d14030259031801087c45541d00440314103150a4001c540c0240401c400c01040044156008a5010811000d5411921031038085000b03070014110403d0300050201c11401d41ea41054025540106000180703510758038010b0b404c0b050340c0310701404107101c9000402c51540a0015035040e1406a40c1c20074060b1850700d4161384124a0401c5644503c0c04080200303060800340202880c002e0162100c45404140d1030b0b000f0300d4141d00f00c40f0340020341c12100922000d590301c10a00e4684c18040c00500041d01554000140c045c4901d440c4011184000500c6081a9070b4a80190048034003c80c26140c1540750403240c2d40592000b11402400641440446509980224076015009010340001c01800180c0f0004c10b00310607001100c0a8250b001100401605511108070406040141c1800805041c03d001c01552081030700b8a402402c105140010171220060181c04807054480011031801ca03524108540c0f01e41c0081d070403000700000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 85139443 1250 85138193 85138199
    0x91806090d020705180f07090308030403021b03030a080106050c01110d0603050d05070f2904060b090a0614060f0f1b0601050f1309080f0a02070503010b19060305060f04020d0c09 78
    0xe45c00002d8008401d250900d070b10360713030b00c003101e1112400184010144001c244006c004540f01501841c4164400e4000b03150541c58192209210900320304400c2c4658400c20000c1c1081d076210085504503129414603c4d128124020035502410360418888504040490040010031032500190116030260095640360640c081c0210392310310031100c026124546c0748112400089940090b0407401003540c50030351000f0078188442444d007c05039419200381d0340720421001c45103040d092468101c21800c008021b40c1d868150b0551581c41c5003580c56108250104212f03158002c003404440c40389140e00d405c2c541d145043c0088680e01464050b00b103030f041c803c020010420f400c01000310441d200d0020441003a19050340502c2014140d420000c0764aa00284000c00c4806d0903480a0469084039801030502c1034109414142102c0300c0840300c81c45804070101055428150130074200603034034030b454003003100d40c0e9003000716072140c40d551002e41e08244009250100d03194150b201a407862802da850800541c0d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 85140693 1250 85139443 85139449
    0x507110a061e14070507020d06050109050402090108070f0308030a020d0507021e060c1606060918140601030f020d1b0b120f070e060a0903020a090e1905030702091806090d020705 78
    0x10f1840d04490042ca8070300c00f0a00c00c1d4003e001401e0000c1c4001c182c882000074550b10842030f41c40a0340080790103030312903040c4402c500e411122980542040e00080840b14903101c0100e108614903c40a800d0b158001b0101e800114a134048580d2401100c405110504200d003000b0341c2c840d032410391645820302442d00d20329450000710b011402100c441c40c5e45400c4c908110002d1044440502003100c07100c0d81c600c000609208240140d601c0e6400c0d40e04c041802180c18200b2040e0003440f0800d161158200e100144000b8039040041d010a54042c7d4403214150300c140b81c40c104c001014440c4601400d40081d000509105200092062605d014400c94113a2140c8440b0002030308251081e03030216480c07001d141174070308203200540355480c024504550362683d242c0202c2c20000030798100b0b80c0c07030584600b640c02030604100442050807500031064a92603010341c8560380c0340e028502c0e000f4820000d5501150144592074074003a00f00010105492031403c1021900e0340c0c500e44815400050f000b5100d00007800e10b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 85141943 1250 85140693 85140701
    0x9050f06041b0f03140a050d020f012304140f07090c0e01030b0d060e03040506030a0209030606061305130f05090706020f12040306020904020c0a060f1505130507110a061e 75
    0x290389103034000f144504540d10801c02c20841e20000409104450004000c1181003084001c0a1f0094010780791455441000900751011401040c5c017130306968041d00350105511841551060700518039600e192101c41c40d01c0d080403804426440a0f206801001c1403c6202d40e0245084ca5070a84030180100000401507040d0340c1601c28042e400028640031030003048458201240340c80002c0140da19085e00d07000007500542040c1da0321188a640880c40300542d00f010420f007038200314202d030044d040044058015044007035901072a40200d0b4285501406071416410400200c1801c100500103440c004c00515612200c1d446160300600c15a90341a07079540000c140103a9126074103100794946425525800040c1d070004e0b400c0381c0c10507401c201041c0b00540030303c20613985510801c00410b22221b0307111804103851400303540ba44480d0392600300300000d070b995014a00680c144410049402e82d10204252605220180d5400302800b490008c58108146980070303c11000f4070b01c29201d0011110f00d071a000312 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 85143193 1250 85141943 85141949
    0x4060f1e02030304030807020f0a08040504060602060105031b0d0606140907030507050f13050303040602070320010504031202010609020f0703030e03030702070e0411030d050c010c0e2209050f06041b 87
    0x240e0000c0000c01e01080c490411b89078001c0ca140129800c0300401d810062074503441143c00d40d1250310219081c0030a1605000c0c0e040100b025200905140d410640060385804615050b50b0100d4442a04814251182c0c120070b600190810800c22500c0d5940064100c0342052840e4284a40d80250019941500034840d0a004908a0340d64a05002e1151441c0d10300307a02019608002e074400001c0041d0940d41000100050521940500052031640c03402e8921840100007414600b0313000049000c1c00d0340c1c80003d450413a904010383c10448680180140d00600103034128075a00c5d800000c0300c02c8009005c0005002e818460b0f136040100e02c4414504030b49a000940f0010f0060b04010002c2181c01c00d20030700d10740c0282c050960521649000c00000f0b14115004d0411004508081005510410284a85564843d4504180321488113020001c3c00030301040078030800280b00c003081c0b45000b01c8940c0c004407000d50320030110f403280381c00034601a0340ea910071035040760240200403070200d075000c0344140c030421 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 85144443 1250 85143193 85143197
    0xe04050d0903120c020d06051e07020f0a150e10020a02070803030103080403020f01050c0a060609060605070c0933080d05040e0610030209130b090601020714040b0402070804060f1e 79
    0x40e1456032282156a03400c00c01307040c1d07071143c15038858030007184071031040901034183c4d00165001401110300782506a40c0082050707042d0b4001c1406da2044403804984803944683c403e1800400c1031107030340740d20001c150311801c0c5249485140140d4030307800340350b6000300340200950302219941c075551890140ea0348824000240300c1c841c00d0000700018149000d601d004010141401810180d09075200b6180420f0344000740d41c05074407841d0400c001c5c4030300e11400024040034500349103400140d0329400341c207003041d00c82c1100d10f176070752000b100040d0014400301c045a1981c0e800300e44910081586c000006040d406100118001c8000100180d0700500856003102c0003a071412842d03075102410000780d10103440e003250030b0580030081b0441380e03a1405100c10b6075051220b0000350340b901080502c01001c900601c01810365100e0341061004401c00014600c40e0002120702250704038110010402a000d8140018010700340418040f881541040c0c005880c0c003103a40c1e4001001c00070740d6880a00c80214800100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 85145693 1250 85144443 85144463
    0x10e030c100902180c070c050406050607110321040914010303020a0305070206090d080a0e1c06090804051908010c02010903080f0604060f0b0c16030b0c03040302160e04050d0903 78
    0x201c07440c00e402c1501e0460004002107508205140b44568180e801c9500100307032000003400104011900d100100030300000c1d00c007006518180004a6907901c5104401343c05000b1100040449540c104640154141d50798104270006519810f815856001401014206810115900b40c0c202c080b82a0070304980d0075600034140b00c130042d18191644d0b4001241642c02034020000300d60191203c0c003d51a04601c80c040c495070f6100c18200007800b40c0e45101c2c0756031081c400000d6010103110b600c9011103d407038203d0000501c0080074a0400c217207200d81e91040c0c1d001548034280c0d0003141103d2144800325060003009000094507400100e0888640b0100100890394140115080910540c10380c3d5114030007402c0021020303201c20707400c0851803030740c1d1084000b0040054160b501c031009104100710001c4040e03a030b100c3c0e41c2c00e659506007801c000520328541020040001028141b0801500321240e010035044c1c61480d80b600808420010100c0d41990ae5202e866006055180324031049021644c0019070b41c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 85146943 1250 85145693 85145713
    0x9010b010f0f020c0616050607020604211707050304050d08060a0306050c1303050c03010c03060b070f051507020d1403090d030c050c01180204110c0a0807060f0e07050102010e030c 79
    0xe900010042c1418007148510307100000c070f0341c48a8000304001c1646d100403590a00c400c2c9005458a00001e10000440d04001e09000000e03040a20f00e030f82e240c090203000780304987d414108032280c020317200d400380241f8980010f000c2c020b50000021400b49000da030036a81c001400b0785043d80c445101340c80c0c2c1d43e00541c8440042002c0303140c40e03110310b801400804e00f6900d0300041540c100c421014541058940303400804480c00103140074403c02800c0d44160805006a038a007401c955070364016410003902c104e4010516408000007030018204c01449902503031958249050300a54031401c00400308041020310800034050017044007034a208600200040c441803109800071006004100007100c01c0c85400d00a58410403004e0041d28040755001444a04490b4103004020a45581c0074070608850010424031480203c00b041d06908190003c010598905851808130001d125600180f11340901d0002200c0e612040800c1000c102c50090f4000c0c800300180441b803585a12492401203800c2e0b010403090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 85148193 1250 85146943 85146947
    0x10e0702061302041e1b0f0e09090a1b090c0c0b130c050303040e0f070309050703111906030207050f240901020d061701060602010603030507020105130512100509010b010f 75
    0x10300303a80d2014001041d060300d1502c0500c1218550500c41c1d00700d640b904181c6031080262090103580d24150b1030909a881c107c90809803050300c4040100340502c560000144104808015581c1444da011000c02c6c4d102480050700c08840307a440c01001d5200303003003400c043c800d1881220100011a0407210f0400947c5a021010006802e11003003114058000e11001034650303014809400204100600c4403034604c0c1402d811050b40c02c0c01462070b8241403420355031501180001031018103a0394825220454543e20a0004804c648620758074038103402c556102040c09649500035107440c0340300b0340c00c80c0d48190801c0c851903103482d071100d020b07506d000700d00c120010b942907600c0000e0f82017040000010f24090210320400252103c6810001400b0000002c240c040e0b07400b44242e0005003403600c0200304250031030354001e0003071040c0710010b41040400f02720741c00c02a0448000070000c1c440104000800b859582d03e00c5c0d1100c0c100b00c0f42e035901e5460140002d6445406002d02c41c4800c0c0169200702c12420b000e441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 85149443 1250 85148193 85148221
    0x7030b061611040e011a0d0507060f0201112715030604270c031205070c06050f1605100f0905030301050d0c090608061008190602160b0f01030b010e070206 68
    0x8240c42d080400d0300c8940719622a842035881304410000049071281d60320501c00e522005c0c0708070007400b601049111101041000c035040003540c5079031802000c4515000803c0380075140f04129070440440010f8240e4001ea03842030208480020403004444000c202010416030014a112a5021800410002d4000d00d80350744141c101365020301010142c900110794002c00300c058000112540503072240140b00388500a1503112491100d440e1041c0342000c1381d503421008440600c998018018042044164a046101941c0e006181c0c085401201d8089081c220760320822116214005450300103c4140d07036040c2d0094440f055000002945140d10389024042c0ba5002c481040e500031498030b0011440800d07030b000b0000206420801441035080c00e100c071442d10701007548000e01591011020585610f03455042260040d001440161621510041c41c0d1020602d85001041014540c04018400e550701c2002c41c180da01843c4805501d80c0c030fa100c2c0010301c0c01e080d10014056484271002640d84021414 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 85150693 1250 85149443 85149487
    0x30c060f1e121b04031b17012406020a0b130f03020304090f050108060414030c010c11010e01020301050a030602161a150103051009020c070510090e07030b06 69
    0x194625114401c004a00c0940310740303404806040000070551030244031000a190020250185030b03110b1039200340c44448522135484020b00c80c1d4068110b0540c403405040c001b000a02c000f220500444202d94a900e000f02500c008a861042003408491085250741c11182d007075a040740c00500b480c64140e00c80e51f51444009124800450351401c101000032000c1c100325003030078469001103448505048200040e200503290155003545030000401c943c010025441d1f401036000010f8400f030a801144c0b00d030070b510404410700600e40c00d1048000c15141e0010f041e001403c2110300802c10320142c008a136082c2e01c420300c1840d6024203002000c0c004543e041d4020940c0c503021082d44080d0100c00c1d540d48400b510041540071405c4a000104aa011038000d032015121909103000c215516268801d8062920305001d10b1200950200312007141c4c1d50204028406002e000b403042c0b82c0c02c8078141d03000300310307072002e000b031002200003140030407400e5010b40220f000b00c1800811240c01c01ea441e41400201c584045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 85151943 1250 85150693 85150717
    0x10f080a15060203071109040c050d1a09150a0504050601150201060504050a0b120127110409080304030f0302030108061b0702090403230c25030c060903110d02030c06 73
    0x101e0440144120460000001d0940b82c010315214510740c20b00700c900080c82200240980c1241d070030800010706020610090b10341c00c49192600941e2420410001d944082e10020500340e00414400100d00005810354407000e000b440e00b00d40d584030000b11050b07550544005096038401001071011460040e140c4119402d180f00005840e80e0f50b20000d800e550058030440c0300d80da540c0324082c0c5141070555203444100791080c02400810141c407901c2c242c0c116405003018946034038201070302c10000e25120126044030300900500140c1550708100c046a4026141200803401716050b04504602034002d49048406000203010765a4814100041c0c10b1244c0031212480c41d010001200140c0e2603482442c003c038001d5507124812a14200394240400444404a10404090010b840c4180001072049686c100210308045091a0380c440c4901200c0b01d6000248170084204021841960008414007160b0182803801c2441f0381d1f24085c49942e52080801a415800204500351282043c1d0024003202c8512 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 85153193 1250 85151943 85151951
    0x12c0613051c05090108010602010c0f030b060904091101030509070f0303050304060e15040204230c13080a03030e10051501200709021206030c090121080f0c1605010f080a 75
    0x100c00c4002042e101507200c0c1002c00d00c00b0642c0101540c0c000741440c090300041c0000c2080502002024028a0044030068100342c0c542180310066240c907401d844903041c01900a00007010140780c12203201d80c000101d940000d20f4400091904039000407140c2c110b0f40d040c542c1d050040e06684040310685d0004005a40340f5880700d4001146580c10071482081c0007006404400606140c0704000035911002c4000b0380310240b07104a90054140c41140c160400102505259151202816880c5045241c3d010403101d0041107141c000303258050b0000001f40e01510305441c8081110580207040f1403081d00e004c41212a449910401940a00341c2c100c00c00c80701210031000c400d013210025250107c1500500756440d008600d00181129024031160046001c4018200b00340d000d001049900c80140b20754034460071f0454040a03503001d5003908202c1903400645266841808107070200c5141c0c000031304550580f140d0b590114014441c106003009648050751945240514910101e840c074a019201c0170003903a403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 85154443 1250 85153193 85153213
    0xc0302011104030f0507050406060e0d0204090206160b010504060b03071b0506070906081b190c02180114011e030e070e1e0702060c04090c02150108012c061305 70
    0x1c10307018000442c482c1c060802c4030368052610b1420000c035980701602540c00c2520078042c0b0f58110082009441003a203043d000f004244c0001005010428806504810006440700a00580c0103061315428040c0c010004644d90700e505202c121130141c803440c5550030052003c06c0e186e81c0705028500d02e900c2040c224464010803031700d84034203000055680c1c80115003507003010000280c226043d00c0c0c0c00102c05070700111039042d03d2000c84147c8507058040f00d0714100910ada0190754003541c1031141c15a0040c2c07000c1e245140751280c003100047c0a005080900300e02d04c0c60080c0c00e61160303511420000f04410340401c00d4240d41d50a4003d40006900142c140c01740c42400701d400c0030f480107032921446110440d0b440002200c00d9540001d10050308400031074001c0020030006d8001c1804880c00c0301d0030383c2c4c0d0004034072a05920032800c0c904890300000640c8074070800008c1c450015000b0050022500c2a0b0300030b41400c401c400150a043e51050f5489500b02074000342400743c02c1d4002108150040c0141c841d0000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 85155693 1250 85154443 85154471
    0x50d0f0c0602010f0b06040f03080306190b27030d1103040308071110180e0c0f070501060e0109020a091403010902030613030305060108040b0a0b040204050a0308040305010b0109150c030201 83
    0x6059000741d40181c1d522401a40d1190090082407006017054038250702d014103080000da084401800081c0403c1c0b00080030840a07150040d41c0081c2040440e0071046080d04c0d10810f0603607034404110405e21f0000d000e2610941040085903c004400040c010b00d01d92201100c2502c08011043c41d414143c0014040040450103140c0100303082c6120b5005000824940740401c00103003044031250040049081c010b0960b0002103441c941a510714040c40d0151f6521000364465910a454100802080102c1c0c1441000415000700c4151a80030813085416a219a01c684c102c0c09600002c0c2c2c0000c02c903140c1001014030900841c0c0d403110001d0f001046c25000e5030086858035a0a45d18003041c1509428a0b0040c164076201c0e080c0c0060302440c11303008030304060f19400c00f00080a002c0151503996491094134555544e81110b00400d4080c1141c071810790341c5d04004100303411174402034a181d400c0c40d005140561160282c1d109480d020842d0104c1940107100807030318403118a2086040d0765076009074141c3c000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 85156943 1250 85155693 85155713
    0x206130603060906080a050a031d040908030403142b0f0c080405010b01020304140f01020a0b0a06030b01050303090120030708040b0901120507020601050f01051209060601081005030304050d0f 84
    0x40060784010544601c0d0071440011110a0380c0314030442e400c40302401e0700040011511600d01a098540081018400e402031b1014888140700164481d1409540c502003101c941c01452240e030180c1c941c040c03103540c1c550f00b1411600c1400800b15040c030201c9047c0301401480003040c82140021040041e0342e8030b10383c00302811900c1d60b5800c072000c074038880c0410040100c01d0003000c811140a1000d14141890a64a14809034251304510b10880c0d000e9170910260340300f041032404040c1c125204242c18140349100c0c400500e0240001d6601e800781d04000704403800c002085515454040e524404524805182c1000320307101c1c04032070500d502040101c42e02140c0440f0180000c3c0c020440082ea44018503400903111141d00303844104018108020000360380c1d00401c0041c1101c030140d4100f51445841d1004031a81d1060100b0403050340310300402d0048400c00021101c0c843c0030207880707000054840d01c0d041d51440e052445104e0741940100001d000714104103441382a018442c83c7d61030b030080c005030360b014030310 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 85158193 1250 85156943 85156949
    0xa0c020c010813150e010603020319020603010506030a021306050c010609050f0402061c0207061406040b0a1511150a0509070321050705010c02010f0b0f09011202031914060610020d0804020613 84
    0x1a1f4603294284107618052250f240c9441100075103000b40c2040c0d50229901340414495988907040100028211400c0b940490b090501d6a03420301a980d91680c102414903000400101060343c60040041103810940c45038a004041d14000e241040c1c2d640e80c03c01120364011032084101c4100070071190b00114040c0041c05000d031003030304003003a580140c2483d0318900c200205100c0c4110f08201c0000c01720f07242c0d40b440c0c81c182d942915030403000c07c6441c48142c030101611804100c8501c9800da1004018104420482c00313422052001e0010784c4a001140d07659603a24040981103d8014002040102e201100182c28510a0500b00e04096140c2c95042c2100d280c1107505c0c0250f5143e20030165409814400c080218070304490744500f0030b06080c0410f200f510140200980d004845003641d0940d5010403822080a0705030305d03130300b450000c1481e20740d00d070003400701d03c04039a40b087c100400c485207848003120800114a0f030082c11160a06178040785d00c0200940240e81200041100d90480c962a00482d005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 85159443 1250 85158193 85158221
    0x20d030e031603060c0801060c0f0203031c06031103030a200a08210603070f03080c0111071a130201050904050601090b0301170f0f0c06031e0109050a0c020c01081315 73
    0x2c03051840c2040e000f5102090040310402c80c070a00180025a08143c2c80921641c0003a16041c003203c161010030710b544a46941008918808445003074650030761341112080e40d01c501f00507054503001a00f815540d005020120002c251180d2f10144840307040d607103c0e900e5501950888564500381d0726090019800668050081d000202e1100c018a080b1945603030010b4044d070040440328584000d802050451307000041035034000248113030031040d094202000c541d403a881115500c4480c0d240141c1508940d03030101010040394000200a803240740c1e014080320f0f8040c0c4440785841180c000b0000106001080075044c04070100021a08048032005107000c2c1060701d0541c030a100c5c54010440c500b0a004003070700040c2c0e2040c1501b640c0c6280210301c1c41c41700401a518203840340c40d1301c40942c10815642c52040802c1070a1000000c00040c144c01150007542d240b4030801c100c1514040898941c00a00c0c004c501042051010402042c02c559002903c5405441238410ba201d6051108047d41e0f008022246 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 85160693 1250 85159443 85159483
    0x1107020906061c090f0320120d060806160f05090a050f010c23070b03011508190216031427030102070b150f180f0408070f060603030921020d030e03 65
    0x400c15070003600050181d51580c500c2c1c0c441b1424842e0103662400403800441c8c514002145010214005800142c0507100c581c040c1c80241c030f80003000d4200900c60404180c0060070010042d8100f80c018812a155141d0251217441c0c91030a0105001c0e00703003502d858050422980480785404142030b80c10b07211200d00b101d0842041081c04501312841d160154208034882c100400041003c03070644803001000c8002e80c1000ca009a59101e0b4800b8041d041c4007071182c1641c0000351100c1230142c400c201d203010700e100b6104c503210409502509103040c0a41018003681c000000900c041d16008280c4200c2c070b511000380050f14000c41c943da0540f4078002901c2c8032840415020110060f40b80200200b454224262446058208414900c9500e05005480344404281c0d00d400300c1c052180d58001c070b42c4519007180c0e03101b80708030640c540070004140501c000e8000800140020031000c2c80c95001083ca020100300c0c2030004441e540070000700d038441d20800c0f03003032004108101c0941d84050040000070b52058125203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 85161943 1250 85160693 85160723
    0x1c0519020f06120402130e0703060516030603030e01110102160b090607080906070309020f0a080d030e031602060f090907050a11030909010e060a0314030408011107020906061c09 78
    0x70300c485160340d0030312034582401004080101070729041d51080c0c0469480081c00040da040200074917541c144448280a88000030003803060350b401c20f40c000c1810307400b12a43c540720010120110b6003039001c014001800710051424a6210b40461241624000001441c203211001d0201d000102900111002003ca0007003004401c01405210b52100d4107040680461610031611520340100910b06000e141c1c1d10803004055403246c1c9054450b02c507000d881c480919440e402c80640d80d490a0224000080c01c0280c00022050013005175907403520032800541102d8059403c008040e0040070070526080000e01980507240d6400d40c04600134500e9440f00b80d0313a918600c03c01400788401102500c101c2e403040001651984400e02a981140d40039030a08078141c5801d0000f401c010f5841d84090941c0950018042c001207001c0700070011640210020000207508070740e0f002c894060b0381e8020794458641c0340004c400b170809900400d101c0217a0342c0c0c078410440d521010103040365851001980c0e84090f5410b44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 85163193 1250 85161943 85161949
    0x1060503070c060b1c11040c09030f080412060207060510270f02070b041203060f06110307050a030807180305100b0a03050d02010603150203090d050a09030204050f0f0c0a0503061c051902 82
    0xc000321b18000d0340d040c85114007103c2c7c080e08002144c0302c000c00c241d00c05108802445840c4007900d010300f40e401c0310400c0d03c16040c180b01d0080d40006905844591400707010501d808100240101116940f5052001c00691721380c0014250140d44034040c0760300e40340d010101d84c6803000c0c401005a1485064455600e0030103082c00b26a00c180c1401141c181858650140005190700e10424215034951a01c40c00c2c00300f881d5141070641c000c291004145205000d01c0342c003003641201d90107102d090181d4a103c045c02554409030b400414901c0041c01daa00010b0841c0e0709158142c20a8103581c9018141c44c506d96074030341e6620301d460745d805410401030759076120a10802504d010444201c05009e4810b60039418001c1c45a9284c80d101da01c3c40041c4440080c0141496000712481030040d60028010003840c41c0504941020400403245403100300302c80d10000e1296128013007920720351842a0340c0c29007103582c2d040030b0000e41c44a01152a4407140003171074013000100104511031000042c4180300d000c5495600c14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 85164443 1250 85163193 85163213
    0xa0819050609190b060409020d051f141308040e011e0506070305030708041b061d03010c0212030403051911010b0f0f010e1305130507080601060503070c060b1c 70
    0x10007500350007825183d4195200300d1080710701942c0200e42c1c03030401c1c3c80d0180003c00400e85140c000f0b410010700c81d610320a011000c10b015241180c803001c0c0c03203111450007141d00102c541e961030b00c04c00403e031840402d00345004c00f20100c22840c0700e610803d25050b1207841c1855041800da00c081e11407020000301d00ca4100042c030707012000b018141e56190400100d51780180060100400030307010821058000350a000030000507038801c1640b204000700058072071000801009998920004404000209800d1818144200d104052203035010740b8101c619900d50b0314580e84050003e40030003d0601003d428840d00c060f802e0004d10031925107402c4001c21059007801d407082103030341c14400c003544107001c00709845400c00100e45402c06d20b00721350380c40d07406400589518101f00c9c00302c0c0818500300c20064004030010203100c98a02420484038215921540350b40e88200034026640054800c3c4082030320366021b03010480350703503104180208a0f070808201048042d203040000001d54111110700c0803c0c0705060030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 85165693 1250 85164443 85164451
    0x1090803090f0703030f050307020c061b0111091503150406060309020f0d030203040501050a12021603120504020102030703030506010e091006090e2401050c030d021201091e0b0a08190506 82
    0x1e411200c4c0356480c040d000070024814201401000000258807600c00c4c00b103d24141c800030200354461903610411b42d0070f004021014035427580ba0140c00d084683d414004c2d207110351802448051502c030a518000c0341ca4002411018a04802c4001d80a560303450380207035006400d5030b03900002e40c0000e0b0f004020038584c002d0f02c080d0084110390b0009020075404030445003900c400b0b00b445982c031a00080111400310000003c4204a031010444000c4d26845110310100c10307000307907130304070300d1410395604502101e4040d81e0090150744108000700000f0700a80060b0b40c010f005043c60300c4d020049802240251408807004131402c002c555051003019040a80200504132031005004180b0f80030401c4085607807140075500d8441c0c81c0c0804c001301a0310440c100da01e588540015070b17846502c1a01518065008008a18042c804541c000300343e60019100d007925079661030034031124203920041044020080e1030f0201c0e402451000c0007042112081000499120300d03169161003042280c1003090500310f000e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 85166943 1250 85165693 85165723
    0x12020406050f01090303030e0f010e010507030c020304080a0b061f0c1704060c0f05030403080d05010906090b0303030a05061507051c0903081209071203050c060105090601120f0e0109080309 83
    0x40244407283d034004c0a000585e03a240c02c0c002807951188441d545040004c0030b488055608055000042d00d5064000500a44490318244001000300c0d4003170342c4900841c02145090703030103690004045404401e0041d00f210b405014010030b182ca070490114490145c7e1036210201d04503000c54000c122898a10b10140d00c40040c42d14101400c1400080800d43c2d00f140240c100007203407041d041031041c1442104c00030755000840d15503c81c4441070b4500503120901c5181d0700b01e407500f140020740810b940a402e0342860020051455a50b134041440c00401c4094010364118190300310044102c0620802881c1d414082d1000344074040c2124564408440e0982135174080190424040000a64038000c4c0d40442020308a884543e603901c82d403003450304e4800e0b4001054010310044440034550044000c0c20802c100d8816a8000e03038943c0103000c01079409a03220ba0000da1040d2072201c5103192075000500001c0a0040400d05401040182e4251042c9040a07102000000284810359030100620100d10b2800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 85168193 1250 85166943 85166959
    0x9020c071a0405090405100203090f070e0c030105090703090b0c04030b090c030d080c090a120605090111030106030c0207051005130905010612020d1b03020d06050105070c0b0c0a0c1202040605 84
    0x1960368a405203100f41e07402200ca003800710301080307410300c19a503d0022990085480f0725194241c1c581d14400d1038503880403401602d2000c111950a181c3c42481780b44c0204c806860742e46080f042c03214000c4001c001d242010b41d076501420000350015a440c0c0500344042865460b142581003c40554038040c02510184c1d10000000700a914045180b0403840380504113405507954500e501c603610312030100119032105d61410089000702105500d10301b014000d80c0304102c180d54444103a400c0314404100040a203a0034001046260310030740144c4034110080c41560303903c42d51440491098040920300e2000f18001060704090f4070400003480d0300504402c4014813840d494900f000e0a0347c805013603010b00e007a40009051011800d1a080740d001c40e131000c004402c0f045c0d84a00010025042054103c0e40b03a0304141c0002282c1d8030603c2519201508207504a104520740209014160b20580e075820300c5020b0040300c0f40100b40b050445400401d80401b01c0c3c1c1c030384100c03481040100c40d05074101b1b512a100b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 85169443 1250 85168193 85168229
    0xd1505090106060323130c03032a0507031113020408030c120304080f160b07030b011116050904050705060304110406061d1207050301090501020d0506010929040302040609020c07 78
    0x305c0c0c400044080c04101c4a026882c0c1c1c4160800f541d0092201408282d5150300010426501c500c000d0790f601c00403800011010050328020402d08040390000c1d240b80c2c410003082c00492084072030104034100c02807486880510002018041e40c100350b0224450340c01c04500070640000902440d80030380c031461001491440c05a035880003902800722a081e0050b00841c00d03813400e607501d18100c500b15400c00d42003030252406281c018041c090803480c80e8001140ca03061071810000c0000c490120b11030080500305407a040005201542c03d0040c4191118440c4c010000303076688a400c0113502441c00340310030a0111640c1010b00c0152055540540100190304e00ca009941002e07003d000380b5880d040396455509142c13081014a8030149820180e4103510f8500503100b04a0154014403005100f110b06000c943d80c0c6400650b5040458842c0458264a0140c2d10548a402c0d1441d0b851802c0714251082c1499145c3d0003080c2225a65000100c08990028101000b05420000100280013044440540d450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 85170693 1250 85169443 85169471
    0x80f12120f06010201021309020d060b0405010e090a0219020a12050f0412030c051b15070b07050d0612030c060506040903090b0901120e0d1d0a03110d15050901060603 73
    0x4001040d0914520010700403661030ba1003901102c0c020304890f1141c02006480b60042002584480f002a0b003252a11768001003283c9008107840807101e0513101c030710040c07410000784030a6240003042280600e500f00002000c0c1d00c43d690345010701010541c0180300340382d1071b440c01d168604109010107050040c140b02d004400503031442220241e40040b000103c4283c01d130701e030076a0ba09050700e1005059015605140728050100d2408a2500d04100e0b0b000d09404100c10108000703214225020b02030000c9a000203410347e02600041c00c1001c11502c000910720350300c0b048200041ea00510880000303e20030380c00304c113103c40c60080581200c811201009002c1003a82c019240c010140b017a40315002c000304924031103a0207035020712241c40d0070100c01e01c90301000d204030a440f08150345844001ca0100015480d00080e99043d03400401e0700901030340ca140741552141c8408448903001e05038049100300c080b03c0000e41c0003442c0761f403000c21443e0114550070800303031050940300c00d9001071080600e002c0c1c103a50104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 85171943 1250 85170693 85170727
    0x71a090105160c03050d0c031a0405010f03060e030f0706050403080106020c030a2405010803041508010605030a111b10110a08240307030803010302040605060c030702010e03030d06080f12 82
    0x7155050020003140245810b41d020302459101906d605e2a1600d0084c207160150000035145000d10107941d50f544c560001c0004841003030040a000c1c8480000600015a00c2d5000c000e41280c2034003100e04100c6121890b02c19a03102c2c60007110520703291014001010b8200004601400450010303005c448095004240d40c1c0d003003c14050500c8290084220b01d021188000906000080c28140003668452590f1560f82e0701c01c1c0b00d40b800080800c41700d00070480c071640440e4141c4001d591850725544a600046c000b8003106034000700e9019040000c00d4940c0c11502200d514601241d0141880b80c401000550413218052288940000f040102c12a101e6000c60882c1d4841840c2111104041c898006042c0d1903081c160300c56054410b1000210601c01120023550484e442160144411500e403402c2c4126401102d62444041c0e00c188000750056006408181044901074102ca00300000705080c1819107645520445a940100e0b003c2d5104e80420b1084515031a06003099600e030255843c2c12000d03407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 85173193 1250 85171943 85171981
    0x17150108030a170601051804020c0f0307020306071e0f03061d0f07030612080315060c060a061406040936060f1b0f020a020a0b250203030a03150b071a090105 69
    0x2c18610641f11552282c1c10380d821104070108a81800c032112084030b59a5203d00c0042e0b20034403c4100140b4818414442142c0100150f0318011204030506c800740c945030f141d500c162040c10b840380300200c1e00e29441072061030260303105020f5464608104800d04a420005011300b000c1500302503040c428440700120040080750300030007241d40d0340d50304151a0303c518141010035601ca00e0010755040c21010006c0d4841c000c88072040c080080380d9403240c401c804c090f8022181900041c05201c00c01091810784d1250b45148111740c4e6194841804038654451556842100300c586078040418505004292168a9910950302e40070040003d500c64100401f101e10a01001001138101806e20003900c2842100742d041c0d400b5025294060325040b1200030382d00104c2d80c441c0c042d200701c0b40400121640d03964030f201294015002d07620f041c541142c100d0103402240c10606200002600c001110200382d0010986940503102000000e81185006003c5d144058020031a682c182010301007120105403000d01c903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 85174443 1250 85173193 85173217
    0x40c0501050c0309030d18060206060d0204050915090102041e050d0206090604031a040210210c0203160506070806011706010e0d080a080103020a0614030117150108030a17060105 78
    0x842e00c80d01c9107035107544a0483c80c2a0076000c0c3c1c5901200441d04190301280000c404009500b07043d0b00e846080b65906000c0311216407107690300c04130710094101a0320260700300d1031032025240b0100151540811802c0190785c1010240c0d80002d0800c40410715070007609440000f016409402c1e07242100140402a01e104c2c0640b046038002243c84140d40c40c1801c40c2c000719400240c1504201c0320300d07080a400f8504407400da000d0405c00a14400342c0d449405030010a15040c07100701c43ca1204048080000d1039032040d0700b8294401000b021031214007411103007001d14401d0008198614240304001e16600e8050000341c184007080c50181d03180400c1500c5244d103c0f400386440041004080c0c0003030607100d41c0100103480d207400002c030700d40032680c0800da075070582e402604c0b50000f665845030129084043c0100d4000c82ca0f07420700042c400d00300000305072000030412000f21408092001c8005034cc2d41003c1c0e0101c0219030001405841c180d81040003103010040c484078051607440e0000001c0c01605c40d10300340c402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 85175693 1250 85174443 85174447
    0x4150e011416020c0925050408060a0b03120408010f0c08061008040c0504020d05060411130501080907031b1403031c0510080f0d1d0d1b08030d0603030e09040c050105 73
    0x80b103502c2004020b403a01c070000d00c0301e8103500b031010055082d500f42e401c1e4158032414940740316403118001c004650440c0c0c20100289030641d654240900149140380050303031700d07008030303010f0a03940c0b19041c01401c0500351b61030000404c1d1a14041ca142160301464040c0c3c140304040d001c1244c0366907500801c00d40c0822504222900384d40c0c1e80390140a0510580005500c070388041191010401190300451003400700b541d080080c40d031609000403482c01010654004081805024420741d403092005540140414007200c140c1510b0f6a6a101340a0307218101030301000e820714042180e00c8600c22402600780068014500c2d01200290051080c04900000380d5400c1d10303000400c803190a1328480c01c001381070040945d680380920030009a182e8040100ca900090400310001c0c540714104a40341c6010b42d07004046891600d0035594095402010f109059501d103050302c0001540f84043c00280161030402000140741c0e400d51802404400e810300c00c06001c1c403442410800000c85180f544400e44100f420455 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 85176943 1250 85175693 85175731
    0x60f0f010f090803030c040305240a02070c030203030c06040c060f12021612030e070e0c04060c020111060405060f011d190609020c011a06030403090603090f020904150e0114 76
    0x5250400e580d40818070031303c000001c01c0f41601229003e8416240709400781c415502031a2141d01c003074012621402c0b00b00800e2000b00784002899801000400e10802ca03001d001d65484d00041d0840c2c0052102c8c0407260010410071042000f04a4a140070741060305051812000840d001403842c5103101c04006020f40c00100c8008640100400c809080d522a02c04004803012388401000782c000c0042d2691148200b070701c0420394401c062940f5100361150000d5a041c00d18120045a0300400c280701a41071140c41c48001099050900400b407145000390000c04c01800d06100440c08180142c2c0180c5954030307400792102001100400040d0000e03800b1400046244c3d0340f03003a150042100d40e210781079691002a40310036281064002c0902c0701c2c00e02920403100c520090610500d4030040341d0040004e40091030500a06020360f1140303011a006001c12035480c6007650104d54100380076907041d03400c203862100c2d45805003004e0251160041603a8000c0c008503244907001c042d41030000c0d080d0341000b0307190a984 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 85178193 1250 85176943 85176947
    0xb060f0d051b0310140604031110091d0610050a08060f0f0303070c0807090204050901060810050604090e120c070b030c07060612060f050112030c0c051215060f0f010f 73
    0x342e8041d4000c0d03202d40d80b4206114190f56040040c401c1009031608003050192903c1c00c4415070342140d82040b200e4400c0440201041540d100108654003070280000d804120045401000448401010030807845400d0840802960b016030038006070401004002607012203030302c10750a03500284241d4242491030b842c1000600a000040c00b070710741600c40030a00105203d04032424004480c07094013035a14158460154105921450048540000c582c2c001001ba007842181566440314400111403141ca0b143d40005869521613030010602c04e8456010100c421401d02103025034410741c030821880c20b081c0ca10302c5512050648140324144c0030110008a0040305802140c0300d2035031000d820001143c0b03818040301a0501800e0944140c0c1c0303040300d0041c940302c0c00d101d440d0503642e8640c076011541d607007a542103c02006428007100c104409140026060325042c8012001000e684017070000e03410144080620090014a494803400740c1d44485c24880e00c0705e5042000f06030084ca051541035583c0142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 85179443 1250 85178193 85178221
    0x605091b16050f0309010905030a0515070903060906020406080f1005010c0206070213051602060411040b1f1d150d090f140304030303050906190c030b0d0c03060b060f0d05 75
    0x2d48140204891402d40f440048010001002c0988500b42c0b044e031114241070707031500507200043c060352200807145084a80c80600f00c0c0e01070001d10741100119200d41ea00d1095440d406021240c594000c01c0600c0500e4202c0b8040340d101c0c800042c0041d0303503d02440f02041003902441181d05004840c200ba000b551104802ca400d016006801020120020010702c001031000b00d8400300304c61400708104000754800f00700203000d181c100c02d80b403920a50040400c4000c200206010303a200101d402d44144031241e400c031039a26a0348545074402ea04002d1455403403031041003240070784142c03a1980d01004c130320083d1b000d0710006507800100141e030340658a032480c2c0c2c07110401c40140c4014031100c1d40d4084034030300000400a8a200790340038010303620f80e481c18654602c015682e000059106d02e0401c100d01c0025440f50780c0c11016880d021640c2e005041c04114a09040340d405e036201d401c80b040c1030090050398090380078600c1e000e4030541d1030f1000b000c86d511000c0c0148603c0c000d070700d0740340c0d8046a155251414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 85180693 1250 85179443 85179487
    0xc020d030203270c0103060501021609053301020c03010b0913060905030c010203092b0c080f0a0e031203060303040e0604090b07050703080105090915040c080303190605091b 76
    0x903c0203400326540c2c8641c1d9540707102c007000b400a4140385011940754400b00d40300d906801c481060303c0129040c009414050a40288002c10900d00f01990111003200c051084940c40d01190400e100c0324860000241002c201e0040755010ba810002828401d8441151040d485954800d15a0001003149800c901070041c50101070050301c00400c040c2607848065000b9070144120304211640c420030288109440c24110841c4150070034207045001985006034112074070148100c496030703d00b5201c81c400c172710141c110003c0200000c00c100603401c460b0404010020154104401c094150701e071450000707a1b60b104900a080e030481c00d02d0b000c103000c1d46541c0c00a5122603031124000905241c0008010a41c1e0882031041d030000302c0002c000078150602401e0203001703482030f00281030490440507805800840141080766126085900000c140e80305102950090241000b025000c85501001c01d0503a5040d0b00443e10801c0c03104140542c1c0c07014288041c4064a09100441e00c454101c2420b500e1149402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 85181943 1250 85180693 85180741
    0x60d15090c081b0405041707020f03010c0e0a0f1a0f0405060409230601021c0509100503060306101202040c020c030a060f0f050f0c03041b0303050a11010c020d030203 73
    0x41c0003107103411003c0f4504070240c4091800c1903049801c039081000751881580c01070601e92071213141d1040a1205401418268000b810380e003c91700c00c0002080c01c6581041c038040c00520344843c080814580116610002c003485003403960032074141710344030082148090260102d1038000404c401101c0c0004151401880010300c42612a55107651180282004200415000000300481c2c000c0400c03900b04140207410680c010600d507003d60300d9a01d800000c3c0c0034101c05000090043d0052592a00c0344042e0349209962416224101601032521b046406415000d51204a0784188001011400d0015000b901280d010881064040c001c0c1e0400350307403038080ca030540241c26201050003515041411020b0a0040c204504040c401010041758800c2d00c1c0740d0744003842400891140303042840a075400a0181082070281f80d0071086140c128601a4403c0f0302145e000f040843c91140c0100007690705020307030402170112101204000751100d984030b500c1803d05038088007061000c0300050545104410707070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 85183193 1250 85181943 85181963
    0xb0f06011403070f0f020a120f050c011104051c030c0308060a1e03020f06040b090423090109060501060807050a0807110f030d2003010306021c0c0c06050c03060d1509 73
    0x9014002c102c1c1010301c980501040c41c5d4480d00c0c1e25070f4400905519aa900860881141e00d0701480440e07040d00e020b08100100301040c00000c0c0341c0b580030f114444288150008040d52070b8646401d005c99903d540e6240c0f50b14074018000280425044030015048540c18680460280d944100003445090150450501c0344814811f45000c2011741c1d40602c290790003101d1107910190044104047c5c2c4c4214026000015030611215910341415040300503551401c00401d442004101144812a001200c200d01d05a4494030f080003445844d215050242c0814642100e051800d400007030803520407030b2040c2080003003150024550901c98030081145080704001d6544076881c0360f800c00e0b980c1d00a407106054052402ca030644820b1000423040f1585003482d1046415a03180d519540001d40103110728002201c801d11048480540511810004a14940b14454066400e04120040b03800040014851181c10014042541d55512039030110342c1d400700901100c8103007803c5801c09800702c400000c00c08044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 85184443 1250 85183193 85183201
    0x106080618060a051e0703050403110615010e030109060e0304031506050105072a0b121e06011110020d05010e070905010e1e130e1009020a0e040203011d0d1b0b0f06011403 75
    0x2c1f5400050040d0300036660303d000d840034000c0c0c2c161200000e90758441c1800c1c00e50011070455000e40414000742d403000740000350055032501c4820035100e112240000a400014003031081020801c0d010345c150002e15009c0107103a0414002030301502c81d80d01c01030040f501050020507400302c1c06116511509041d0700d401036160303442201402941156400d10746210b15400015085000e0340f100c000881c14403040500f07035440b011700640c0c07403c0201e515160640189a003000a004580c0001c00028008041c00a100d6141600540806078054905401c00244050401070b1303030f900071042038005504840303d0080a00d5400c0c42c010203a800b00c0411b070842c03007440100d4141c0c10b00c4c1d07021621001703648054545002c4800444d20807a41c0d070302c000941c400494041132148101d4882a154854800f800016a4900c0715110001110b000d4004516940c021100a030380c003a031002c0510321400c2c91030034051000001d9600c400217810000e01c070041c41c8048100180c2e06a200d03040721054032001021150360790030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 85185693 1250 85184443 85184447
    0x110912010204051215011e0803032d060915060408060c0309010b15070807081204060f1b080105040917070b04170304020108041205090a080106080618060a051e07 71
    0x207119480c032600c00d224502d04100c202081004800701c0002c444401743c0c0c05e200e46136011100d124280201701283e0303440414080010401140111502003c10f09004940c09107070166998100942c0c0301280a031042c0403a948901040c1030f001a80d08002014142811010812a00030351344030700741c184200e505102072000c14000950250320600000d0207031030800418008401100b0305c14191118081200f5000700b20b10601500c83d0b584511540d80c5080300480c520784a91070140c8081d982680d458480700883c2c2218441e1201c5076400400c0040301c0c00236000040c1c2000e005102e800d02640d19442440704103c0000f0711951102c8480240603158205800d140c0c070814401c981c11101804541412410b190b00070055a20450781656440090755490b9500800d440300c1c8100241400fa090005a0081d61000d00e80c1d40600000307000051050300e404015031a0030006042428481541070b440f842c01680801c0710f5900c111007030030124554642c0e850903100c02030000d401c2002080f40c1d40c14885216 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 85186943 1250 85185693 85185697
    0x60902030a0506030a03120203070c0606082d1207050304050d082d03040602090a17010c030f02040503030a050c07030b0a020a02150601090504092a06020f011e1109120102 75
    0x9903580e4041090b40c0e40c2c0c2c428185d0700c1200000242c046481c04021002d10100b503001507a2194003071802c80040c040c030341c1e12401610300300d40100d00981c21800024a56400741d03140b072440da40b540c407501001e4074443c0d145130b922164a2408003541000001e803a03c207100c02001220000c00c800381c8450303c125500e0510003103170b4200c03d00c549040000c00f01d095007040d403d1004603e0056180040d80e2440d25141d841200a60005000300e42050320350b000011002031811a054000104000103e13114401001c01030440b2000103440340d110b44144424003032a240007050b02c0b8140d4a6041032a030b0703640c29103074951500d802c540c001403100080d041009608611074018001c06880d42c4c00300c07800e0b14012640c4075800750080ba825400684954020410792800b078000b6503c240c002d00380749458079078a00403e00411104c81c00d0800c00441034504010150707040040b4034612121701d00800895840703c040c402c1d00840e0340307a43c41401d07460b92004000c440e102c20440f14900402400401c103d0440c0001502075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 85188193 1250 85186943 85186951
    0x30a0e01110609031206030a020a090b040e0105010e0601140f2b02070b0f0c04030b0a090317010803030c0a030b10080f0a1806050c070b040302060108071d070806040f06090203 77
    0x40c5220841c4103144800290080c0209100c2e80034509000080196003400b0000800381c42d4184144d29403000541c64100145002c0c080c13881000c030741f58400c0424030058542d141c400095903032403d0010000400d040805640010091802d401e041016009030701080c01000e15031f0b480b40c0e40000743c1a105c0300c008001005074060902e100c5407111090b00114089006400c0c014151010b2a400075140318042e40b1030380d80c45564074402c02d0405490b80c60307903892110101ca03840045582e400c1c0100c1070541040840210100b10075004410390305203030b5066224000030707240b511503610108600110038000d4100c050002000303440100590100d0308020910101640e00110522000010070b240038014001c00c1a9080e5241050701806a655079a00c001c1130024280c0aa00009220540c001200541c0d40c6000c0c9011b070b40103000c2d035410182d01c41e0070004140c0c46a018031940360b17440c1c526144a9008903030700c80301c1d0b82800c1116075545800306010f03004c7c02d00d0f502c940700d1400401048440141d4059805 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 85189443 1250 85188193 85188197
    0x801030203071706150114040f051801050d060b010e1003091101020318010507110402190201051609090b01020f03030108010c090b07020a0e04030309020a230a03120f030e030a0e01 79
    0x215954903250400840380440c0d40d1110f640020300080c0e580300c84d1000c60585500d0614100100a403a08419009078006811551a041c4240b0b010825450001200911312100303001c0741925500d8140040c00303038400420000c0c005501c1c3c40b51449030f07030700524404808240c050010107811019104c0200201858541201d50114a404403c000d501c00010f56003038103440b51003108024901c3e4010343d0719801081c0304442c14141018042001e4a0320b00141ca0907006070b080c4841c494664001c080d003540c800401d00e075008450301c3c030b003081d007a0792250b19202160803810002414103500c00040781844140300c3c00704180c5c4400000080d460505511008039010541c1d100c4a00940750340d00e00015215640303010794020001c2d501400940c56003680203070000e110f42400220901d0700e901250490429903c045620056012005000030080481c1c5400e42e400302c81000e41113003140c4c1c621600c829645200000c120544108900340380c003a5000c442d4150030201169124035900c5001007100d91250305c1180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 85190693 1250 85189443 85189453
    0x90912021005010602030406120b040c11060c0a05030c030c1b0601090b0a080304260f0303040b010506071703070c0507030c2412020a0909020a0305070905030304050d120504150801030203 82
    0x400e6842074407030103050b130b01c4690103036103868a0280d049600c0d103002c4200408499682c1c00001f400e0342d03180315051000751030341c440c56010003804140c181402c40060140711500020040031459540c824112a400a104812a910307510340b0500e540315405100000e03000340c14010145450410300082c0c65048603544141030120400c0ca03003d100510f1402c0c40b8501030307988140001e00c04890380f1481105540400d00c41700800c00b8042c0e1195181c60a0851409400d800020901c424410404582d90140030b0039150189001b020b951910b00903404d1051310500c4800c0800030078096841000000d1004e504401180c50f0191203081c450030f0202d041c42a0300030803601440c600380360000c0c0c111400f421601c580f2080c0704090b40c121114042e500504000e030800011400100c0e180b1610b1002c1d015000c10399800140340d14003401e01900e40316039908480d10940c801d00c41045141d541301414440184d000d007108a0204011100350f400c1d000765040354420b261000001e904090780b1000c40e50403a4021000c0350 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 85191943 1250 85190693 85190713
    0xd0f020a150e0d0203010e100c0e01030501060e09041b080c3c030a1208060a1a0702011b121d010309030c0201050a090e180114090309150409091202 65
    0x1c8501c060020050011030380048401c01035103403485200c42e40b42c2c0042c1c000300d515007440ba0360780e0910016240f03c44600f03665108551480d944440507064600c02070904100c99410f0141c040e0102c150112001d00c180f0f0300c40c1c0050100300d2522501ea80848450341100101341d1500381986c0c45e18034210010b4001c80e05541e4040b2044445c00d0a0b0b810241d010080c116005989201e00210000311111290180300e1604464006811141c40030722600c1180e80b0a0b42906004003040b004860681c0008420124201d028400307003684c600f00c58200d81e090a000c41e0f1282d140308511107607149a00080d1a42c001581407800c43368200800003403c0034100010b54174026030800540c200ca4040c28050002040b90040c0d00055010b42c00904401040f800c228060355a0b401501c611500112610aa14151030b228000844e609014080481c44031300d44039915440e1910510f0703942d010780004e81d44100c03031810507048411301400440d001ba0009080030b0080c4880380c140000f62180001d2003000500c6003525513 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 85193193 1250 85191943 85191959
    0x150303020c152a1902030f0c030607030b130603050a050d03060b07060c1b060b030c06071509080d05070e01080105041b0f0905090f01080d080112031b020d0f020a 71
    0x441d011030481d6400b50901d15200008241841080021091445001550381010004111894545806070310b80f889130a014418107050503000041c0c00e14a40c09281c101c10196008945280d01c83c0300c614000903180b03030400010354246586201d002c000385c80c0c002c000c42404808100d00441e81d00403c129200b50110400443c101c0355148100725100800b40107400005405401245001015244c8464684042c240f420360300f103070304c003402c81d0750566421144c40c00741018451418051003c9840504001040e00c07078039840d080403c424505a5903566044081040e804c094034044102030004004900e40150701900c42409a402d450204890000009040ca800e006d2848500700c1c1d40d100c080421004801501c400c2d0118000c2d009010300e103640454281c0b5401c0c8050301c14103009100c1c80c070340d5251080042c01e00d000f524180c003c0000302d030014811a14410303c00c07601e050b030501e402030b4180d500c03001000403210714100c001e5000302100801c20900c1001c10961001c2030003150300100c6140d0301d600e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 85194443 1250 85193193 85193209
    0x1605070c0306090303060b030f0108011a060301120302150406020a030515061603030e0d020a14070303080c0310090c081005060c0c060f0d0203010b030708010801050c04120c09150303020c 82
    0xc100c9211031005100051540c1c1105140303900c00d06010540c02d0721549000b180703400840b072100031032084100400000100f40210041e02d580720300e17401c1d1003450800100b6a9440305011740a904103c0031460000c140c400c00100041e98201d00c0400451b08051414102035030001403400c000900700301c0420000160101d618940d010001c12940c580246101750314070070050804140d0505585004035001c291051010301074150980e80509080041c81c944291a428022864540350b0f00401c003e10000b50030058260300281200c0c6095101e680321004c1c240e02c50000e400103003216007003c16110107940c100b1030300341c01814030304040041207480300280281402103995003c041e41c00300252400600340340000701440f0201c00045c81c50540f10b080301c41c050342d0080c0c0c80070641031800007c00082c25070000240d03024110707a40091025091001c024000b5001c0c03401118116443d4145c4c840030050054100c00060030300c4807040c8a2016082401002c80c00b25220640240c019401d1240c00c82c40c200710 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 85195693 1250 85194443 85194457
    0xc030f0403140d120c020c030d020c03060a0b0f06030a0b0a1d06120607051303020411070213020403050a02060d0f0c0503010f060509030304031103030c060124080f15030109020a08061605 82
    0x10304c106040705411001005001c132210b1410070b41c0150000030070940c40c00c0c0200e800c4588540c0040c15881d291200f490304c1d2220080c03000d10094a004a03072034041c2d40701403603149401c1d411500282c9945804407590000d00d03003124515804490340e000029000c6081402088141108001428a0ba00c050510104980c0f42c4065003044d00144005086039000b00060201000c0b80420320700d10503286d50110702210a96004034101c50404a2120f04501c0c0c21540c01c9140c1c0050754055048c245180d1740c03d5034581c0b400b00e0083c070034140400d080003000350303960100c00e0158130b49c81c0500c0320107111400580264028015110f080c00114000701d8a2409201200e40c07200000e0011031416145031a06003602c002c0865865040c042002101c0160b103041040501800307109100b68500a104403100754104081204041400340d56000c10070000715411445070b02010f819401c51106a9000c00a0700410507854000e502030007103603011951070400200a84500d0b005910032441205000c1c0c01d850ba401601 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 85196943 1250 85195693 85195697
    0x50a0509250503060a0f06060c03020c0918150121021516120e040b01080c180a050d05060906090606060d110d020403080d0c08010b04050409080c030f0403140d 70
    0x10319846090401200194040030301141066007150300c070340009080040a4a600c2d030510f4403040b400d040301d40584909402001c8a0401c41c0b00314040b943e01a448a0005d8140c91041c11800f0000c0c1100e903680d008141e11290344000d0315280c4210308010340c1558405c0c0100048605450345003103241c00c0c07404082c010980c001b01403136800600c4204aa10580c0184080d41000403032440c11400540030340c074001245038581c0c50b5400c0700215407041c0030454036015901410010303c8810b00413030005030000c580020900710108404900c440b0086501138201e0751001d41c000026170003080602602181440c01180071100359601501e4071440540d403a0300666009a2100003001b040c80300741002da105000b25070240d20340900701301510000508a0700f240c0e20a8030a0032000507019551402c62003082800f145034101200301d03506000201708540181d00899018503035600b076000901185809075181c4805182c1101e03665045c030713403960a0760740052104580c080c03022250041c074043c010a000e50701895035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 85198193 1250 85196943 85196953
    0x221707112202160605071d04140f04051501080c040501090203070e09040615060509010f0914040902010903020307030602190203070b0c1602030604030f1101020403051207020102030d020c060703050a0509 89
    0x103400c4800258440c61a000c0743c40b180d06500f800103140390291610a0601c2e0b00c9019004841c440e07031040c0660140b42d894881c51404034140ea8240c0c0407007400e9040441501c1d0004540d940d031402d07074904190069800b0680035000c00000e0800c10028141401190984080c802a40d0f01c4041da01640026103103540492a0180b40b203030309091000d0400d5019005400201e104c8280b02a0b01c100d0895035000100021070001d0742c0c1c2042d582181e02c000d200c01c12403502d40d4401c1d2401c1140d00258030078501151046071610f85110540e881041b13900081d640050a9031040303542c919080001758814540142e52222301200c6031076043c004804c1c0c88040340c000078010426554401e04808650010a2008144d9030810b12000940c90401100d03100d148241c503115218080140003420b0300054445054190b80104020f20001c1c8022406524220740f800135103849044520060707085004008880344090301c003107003201400100117040c50155031140c60810550f2140d10806065075412100b0f0600c1f030b401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 85199443 1250 85198193 85198249
    0x3050309010309080d0615030e0a0210050a031e0209010306080a080a0c0204020705010c020c030705040c020307080c0c1009050f06040b03130804170105090601050a06020622170711 79
    0x40d82205600c1446001d1080c94840c202c5e4124084640c0c80d0840c0d40c0c070074280360901603a1501407260a5042d4043e40085c203251895a0009094004541e819800c0140200b440303064075010340c100310680c403081208021551405282d0200130b402c070a103194006400d14070000750b4043d01042c102c003100d4000c0f02203460441c40d414103540665100304120b8000e50300308041c0003c071340b080c03007007202440c01135014001540003102014030340364241d00414450391600c41c0780b41030147c00008580360940d0000d911070300d640c07014840138204510803406980144650700080c2003294408203803000e4070001c07148400002060700912a0a01590151003160241040806c41881829141c071010f40c2c4a040c403185481d45442800380c241c4000d6082d44040ea46a00070312990a03400c1c44403501400094035a400c1c1e1900d403c900a59640700030f02568048041f100325115850b140c5441018481c0e0040e00b041000da2154802500c6a40807242c182e495241c48903042e6818a0103500b00c1584454045041001d502c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 85200693 1250 85199443 85199447
    0x360d110d03090312150302040f02030a0b04020406020327120f010e0c010801090b030c03010c030b0a1217031003050a030504170106060f14090d060507120203040803041415040803010602010c090305030901 89
    0x8005d1521062040340b05000401a6601e006080062000b50300150712401c000401c0003d0b209030b074041030b1140c0d0050106202155001040c2c820540e040c0c0c1014180488a40071000e460864800c0030381c00030310b10084c58002c028002450034548418100800401107118100c946a5220203016400a1956001040500f07480c0e0040c1c458000001d049c0c90845801d01e00181c00c480f1680c01342800300b43ca41844803150b00e400000d140040c07528275100001d0810135a9645446442d00480806501001c0302059109803011010000340d50b00004507494101d4a04003d003150b0003a10903d00036160044117400c00813418050441140c402d9112002517284404051700d200f001c8800303108060310305100000542d41c520000030809802224001110b060000004141d85240010022002c0c010802e000008504200712940b043c1c10500c95031485a03403c2c03c85042c0100c1a9904200d6112041400184150307813004504940c450740082280c081000c2c6e0030b4402941500c0080e200e50000d21000100354 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 85201943 1250 85200693 85200701
    0xc0215060103020c0f0c010f09050303030126070b0d050703090302060a020307140403210f14070201111b0a080724030209030d050a020c0603360d110d03090312 70
    0xc9014100503050030071141c10549440e800c81e4580800341d0100056403010350f0000904551864145003d9041500344000310b44da070700c018801c4d0030694514440340a0381c040d545208070000c00058066624450340e5001001541d00302c0d40071500046d1030b01d00460216806442402101649900907000703c2e5a00e444240094000420b003074240700344c01d0691400c20900800420203140300390821a400707505020038281d81924801110140300d2610440c490301a04002680070807130904151640d554000e1004980e80d0700300f4241071041c0e11a40030283d01212210642504047d400d40c1d00030b00c0b81e5a20f02c035107941ca81c03680c4160008140d40c8411302420881c903288031080c00e03590b030502500e000d100d88046417410161400003c0010b001089180c0d8590707041c40907401d003080072504181581454809903032040d00050011881000303100c691418460410341c20708120268800782c980b050040c107409008807460804440d124016499001e110300c3c000d100324400243c1580d100000d410700300400800030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 85203193 1250 85201943 85201951
    0xa0f09021819060e090106060503070c11060d05040614090303070c140115030b04030e06250615080102071103240421110f0c0105030a0b0d02060313030807030c0215 72
    0x38460b851a000c1c04071105004143c028980c0d2408103c841c940011424210340d0690030040030440300300140000d099014401a04030354021011805c4010740d580001e01f584210054940c0c02420182040280f2105612884802c84840d41d41c8203070742c0d03804103400e84a21040b50000c0108100180c0003021030504096840341070000b1000282182120001120703003049540103c1d500c04140c1d082004141e17208c000ca60880b8000c0e40c904c0d09204480c800401c0d07018008401d000c0c84180c0c0c005c0d5405000e8244c02424020f020344442101e00c070348500110f03011354030440064422600500741c00030b560400141d060f041c03a0010540300c2100715080d80b6070f004100f02500c160340340c050b8001140d0a00303c48003101540303d029030301c8007940d60200400c0d50741011000d421801340c0f90003202e0b030841c0598000080b2076104000303580010b0b03101402c0f00028030b103050a44000e508030381d010040007500c031141d50040c0f10150003901d03030389003566a0f00022002d985079510600010b800c0f55041c2c0038140c00020082d600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 85204443 1250 85203193 85203211
    0x90207050705090903210412030903020c12010204051206270a0b0a0903080705070c090b12030d0609060506030115080c09030609010b10050f040b07020a0506040e0a0f090218 76
    0x260b5100b000866540041c1c58030b0b841c075007000131000d80742c0c84c0040c41030013003009030001c2456a02d410745842e00c0740c81d901070100041c1925200c40c441010310a200c0b02c1006e2200400642144400300c110398001d4000340981805203501d0220280820b02c00201c061042d080c2480b150f06401804142100e600c42444082d043d511400800c1c80000d05040c42c21841410035000006d20801ea80c20001d11880c1c0c081c00d49018041d0402c981d4020a52103007001c401d84a66032404600c40b1030f07120204820040b0100b94591a01002c9410140800c1c640c2201007110b0100a0a010103030711142084814402807241091440003080d003e0101d900404a2540c44240c950342d8604210000d4046801c045048070003552696480c40c8194091805070300307006250425150943c1410002d5405558078403943c0100540d011001c0384d803070110b54900c400340d805442e01400f90f5031299950483c0442c500c006603006131102d13041080c00440c1d50341da803241040c00c94000701140c115522201c0784180508018020084e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 85205693 1250 85204443 85204453
    0x30c0c01060b12090c1c02090727140f060d0506010203090a030b0a0f1802040e0f0f030a020106060224070915050a02010e010e0c060d060801050f0403030f0606050409020705 76
    0x141036060b10040c2c4001d101032503101c5064a8030549160804049807140e5100704480300c40784445501116032410300f2507040d10500c0381a1220103041d600d000072007884110080c1060400e20940c400c4509080841c4d610006d543d181e0078910007040702c1c0d0f82c03901e10044c0d0481001d200141d40d416030754101c1500083c040c01660320303141201001c9400100c190b00140e499440d0481032050718000303403080300d001c012101c00821840b01e51140000d000e98500740045c1c0f003240c882036a0200448203020b004410000c43d01241c9042401c00300351905c94201042a030b0142d440d015001038a0350000c0340788405080194420b14440b018001499040e13140601000100501c032100071542050140d4035144402c0c642e04c407192140b100b070000a0964003203510002540c1d0401032103020400c00002c501146078000c4465076250384a14014000402865106441c1503003803005221424014040d054040c600035a0b00b07001400b10515410143c0b04144111400540100020407586020790f01a0605511540a0350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 85206943 1250 85205693 85205699
    0xa081b19030e030307090509150f040b0301061503090b18070308030c13030b091603021302030c0c0d080114091e1801090606050103140403020a1b0e090606100201060b030c0c0106 78
    0x1461904100e0311180412403c406c24045441c200316125030105803080e0310307819540c1100c0403451421410703400501540d1035080044496a080d00024003502d40303065081c1890341240d8006002e4207d0920542d0110b1502000c40c01c0c924500c20b81511150040f802007807980e1940d070700c40c44144d00c0207221202c00703c014401c6281c1054124902d80045004401c5095a41000784d140d0303082255030710b04800c1000042204000603211144d00b55403801400e140180c4a55410100b04507500c03541d141ca8040780264540c0314507003600702000300e0582c0c25400b840c45421b2444400e110300814161240300110303014480e00c0000140500f103030b41e0710504400000e401c0c4641d8040c0341d42912800c000449a05446810500a40d44d06228040f900075080032a84100e0500e80c9001c1d450b810f00b210040e210035204075514003c160b1002d2602e0041031011072034122485c00c4d8861907141c020035201c0c24824480b080c412018a84140141c40544130004081455a01c1d0951903691603030129a01c25907954a4003000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 85208193 1250 85206943 85206971
    0x120607050f0d0e0f0f0717100f020909010b0a0305162f0304180b04020403120f1e0305040506090c100c02040905012a020601030b2a030c0a081b1903 65
    0x101c2298141c3c030021710b5881c2d0440d200a0401040c0d4001800c0f50001040c020401d0000203030504150004074000262a10442c0400340a0700c0ba01504980014a0301c00000390342d0220b40080c52001081d40d0204076039201c23002c0c951000c40d20713004076000082041400071410000700080301075840010000f49a00d50045080314195009a4070408407840340c000000403116550007151140c1c0c5040300c086142c6030860b9905000001d07500e540104109005d00b454509600802c10030310305024007e40700c424807603804030003805404111002c8030103001380404034102100006414445030030060030340b202c10310000000ca800310544001030381d0041c4c641c010070300814820320a551105840c14000c52000d10021203030030700700b81500e10071400c560104004001007458012a240c00c00c0300045443c12904240000b0341d09407500588503d5080c0c4000140224101000c0080c4151451501c0d6500c156581076a44d419059402004101c5c1345020020030314101241d598102d0849640e00700052801405001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 85209443 1250 85208193 85208203
    0x6091f0302040303020c03030702010822020d0c05010e0409051b0616050a05190507050f18310f06090804080105010b0409050916051e040504080306120607050f0d0e 72
    0x206000c00c0e40050140181a41070004500890060b030080d841c1108070790000f0407640000b4001d010401d403e0742c41908a2400300041803401d034009000c0740c68211942080b88050308144141c41c0070841805152030345041a004a0002c160802d014202600036040d051100d18004481d40b980010108000b440705a00321502600b803c0c0548010201900c1600e885440d04c41c00040d6801804c07102c11001c1c0000f0740005440054507000e4509000606460002c00c1040864034030720000d440303501c02000000701c61340d460303450484003d038100040d9044042c0f9407001244000d9024290f80b213502489000b0541c0e40e000f14052034030403d45140340c903a403038540f542180e03030a0f0040c56070b40d0340c001000c10584142c2d02407141c0100d50600074188111460b000755484c0700261184601a4007035401080040d034004403101e4201e100a0404e02c40c0349060314100c40903178001c0314174030b102d05540d603d281040100000c05602c0382c0d1194071014500b443d00b0100106681007201c1500075148c0705d000700105c501041c0f02c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 85210693 1250 85209443 85209499
    0x5040c0c0b0103050703140609030d150803030708090c1203160f02030a030302030405010f0b0117071e080105100809070b0d0906110901030f05220602041205160602150103020609 78
    0x201420145e415480e0480005500b8404407006038844c2050010182c004011a4060182e9242c002103500c00702510710107101c41d5030710410003400701200308048030790004901841103100605032000f601c0c030f902c100052003050201c9200c03036501c24840455000f141d81460750400307004a0700125404d0035a0700192074101d0b5180c4c110b000903004010b020401000340074108007801141070501a03e10f08000007450f0410426400401e20000400b142d000d078010080c103501d040d840b9108400316043c4500140100800384034007070041c1c1c501c81d90b9010451050030900d01452180d001381c180c1c5840c0c400c031034030f454200100d080c03107032035640e0910300004800c5c2c03180b4aa20142601115110a526000942140d0421000c088058200b204108051004a0400105280d03c10650303401c90040d00b03200009005a4100c1c6545610300005007050140028090f980c524100c4180e01030b00d625002c04917180c03e249240b074a401c0292100500051a0090181241d600c02030150b80e90b010744142005401c0c0c4101c9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 85211943 1250 85210693 85210703
    0x90a080c0a060f2304060f050a150b12071d030601030c14030708030901030905010906050f240d02010c05030909070801090c08010e1501110a0803180604050705040c0c0b0103 76
    0x9449181009443c2c002c040c038905090000300103865544c00701c09030300703071001c2e8440e80c1200b01c12000404100c201d80c02424028401c2d02c0410003440d12400400003070140f58010360b40d20000d84400034090726034030f04031005011260304500b2076031500c9805035407101015804a2175080c0c021807041d0151420084c0f980290701410010400518000d103101e001a04149910701a400c004c105200c601070000c00c80301801401e00c0c1c006200005410458010082030380c00410380c60409050154600f40e407804180200c1100f1541c0012104401150310b000c81420ba03115000516000c0c03050256000e00561099039020b4425207190004200000d1103260381161050042080080140082000c0344541960170645040420ba2541010380700d02c040000180386800303c0424502c0b03591264843c202d10000112190b0403a119403c0c14544038007260001c6410030301807005408103884109000801a000c2d54001014004031804d0a060102a00c08411410148200d4100c4100028030700c00701940294020703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 85213193 1250 85211943 85211953
    0xf04050f0301020703080721060801020415021605300f010c030e06010e06040e060c030403350907080f0c0405010506040308030c1606020c03131505070b090a080c 71
    0x80421068000c00c98006000307038414080200003940045885400040508103405c000000c180d1881c00031310306240030041707a800c00d000000d0042054000d84203450649050900201c0c1c0d40000301ea0701e0300003e00d04415880c101c0402c100c2d90620b0b5008000c0b100860302c9140c400c9882004012004030b440c000e0003001e078821850044d00301020b105000c40e107046842c0600c0503d00e40001d0329641c84044c01000140341042d0007003001550340b40d000250002090040c2d942920b0000c0381404650401c58080d00440c1e03c40c160203104c1020954580a4030100c2c3c054040700300841280c40d0b80c6144001c00c01d504520a1603404a0110340802c0031420702c0c89440014942c100142041c801540c606a01441c0500828001400010361071010350340d200b1455078071240c5a84080548168442e00c10b580548190720004400c8202e100200040c08c03090b4040c04440c0903941d07502d08035070b1410980e041d0300e000518188000300c0051140101240c0103c19402122050390894032200c440b5030007038421000075441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 85214443 1250 85213193 85213199
    0x20909040f030f090f090b0a05040603121d010503010608060a1e030302011a030a17160c050f0d240b0a090c021213050108060d0c090f060506130e04080408030f04 71
    0x88240d00c42050510f03894202c0e0000e1400003035a002101c680600303444240c641454080130b03120380c3c54100061100400610110b40e030390500c003440500000346071b4001811300c1e8100002c0c07076400d0311602d80114184c0d01c1c3c0780365030710307107002200d4002c2d02034000d030707440450060000b420030498210803220f05d0700e40d2020b1100e68a54900a4215040d4040b200001303c1c07121035580046e9004078024003030540051580e40e4020020580c81624410440b9101400103481c11440034003c02d0b46052068450a0f2030130b11840304158200890003100300b0009041480705c95035406071211903161000b8940250101141c3d6468034400182d10000da500010303242035840e200c0e4032915a04000a0b4215281d0701c0c0e01d075240141a900845040046000e5541440b202401096064441140d0724442940040d01b5812035511091104050410b85d0401c0c10b0346810318802007450b1820404030741000a482002442961030090700d03040c118002403060ba52503a06100004d103020090009005e0341d03611500c0b05940e241 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 85215693 1250 85214443 85214447
    0x30302010c030c080603070618030803010b0304021201020304020310110d020c06093f0d0e0d02060109060b0714010b0d0b10060e031b0f060408070801050c030405150703020909040f03 80
    0x24100c40c111041003941340901c005618046016010760b0618980651012100c3c1a640c0310400c05500003000304000000000310444410080e50042e4070031221580d44443c04a82c540c01c0c0c2c0000d840c083d40c540c10041c1280c5840451303521a2480c02c60001d080b84c24203a00e10034071400c0303800c121152621368100c0410461208400e00c80c04840a0100341414106d008454409003544a01ca2040c010b496130325003034180c01510709095400607001e808080c4202041c50041c00d0b112200902102c000d03104180010035440035034011201940c6410140d242805066103805581e1012018110030300e540c1d6035141c1d100d80e11801e040c50656400f5044602840c1041e24860f203804950768000000c20045803182c010310b0b940071030000e0b0030151030a01e6104440c2c0aa00050308010002541075003e4000240000c010350089011400c5480a6008020a50f1020200c280e40e10084170001c00a80000c1c0030a00c6007242e4161854201c04c05160041c00c00d1658808215034070815103080d2401c05071100c41c042095 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 85216943 1250 85215693 85215701
    0x803010f08060c0f090a03060e030a110303090a03050f0d11120601030207110d050c0a060201140a09020105070212150a0902100c050709090f05030a03060e0705070203070509070e0901030302010c03 86
    0x40300000040540380f41100c8036854074010104030300c4504100040740e2920340da403c90b042014541000c0d00304600d031f0442c00c419503240e226112042c04913031005c01d40000501d000c8241c91060760340c50090718280791b803550200c49503801507081c0c0b564540c0a114100003010503210b030407903a6140040c51a62a090854005d071100802040141014010450b41c0c0c00100b41e40000e0000507815550400000580e00e440342c181403182c111305800c6400c1140008009070b054100290b8449110301d50003454035a03c6031a003d407840302001a020400030043c003c01420624422220341050400b6151f50300b03c40205850105800d0f510490f4054a5400190551a120b070a4100130501802c0244500000d80d50703294039080c441c8501003049a44a0340740c0240f24142e0044c07604c0d00d03441025282da030702c1c551001030001c0c90607010b550302c104103a0002562445c0981c085170740c0603800600515034180b0700342c00c01c0780c03944004081c4001c101c901c40b2000c40a0321441090f90103544250000325800846240c021300720303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 85218193 1250 85216943 85216949
    0xe0619170a140d17010b04050108041401050f1608100614040e0106020703030306060e090a0c02010902060d0501060e01021603081305041b0210090213050903090a0905010608010b030123120106030803010f 89
    0x3213001c0d00010419000b044003210101e800a0130030310103650b61400d1000c00a1050000300b8081c0d42860f042251002c042001c407446507504000e580010302c1462411101d03400d088a40f08502900f24034180b02d5030b80a50704d15031700ca40c0221152481c00740c4074100440c8051080e07120a026901105003801050381500071000500b0703c5150070603120681c0f5000460303195003d00440742103a40e41c1000901d9500c03c0d04410030894020f07203190381c0c5000c0307640b1400c0100001d10035140002c40c01400e060b01507101103104000001c1ca003400856144c10758440490f254402940c40740b620410303620000e10394441d80100c04402d0a1000206402030810801034241b21030044181380300c03031520b8090001641c601c881d103044421240d1001a481d620b0410581c81e5114410903268041102d400c0028070f900650007850581c0d04594644010fa41e8170703075000b00300e40030a0048009240940025046144883c020300b0201c01c4010714410303101000c010b2441c01c5609a0300192002040000103120f1001425a80001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 85219443 1250 85218193 85218227
    0x50301050a050f0a150510050c060106080112120c1205070c0509090304030b040f0209040b04120201020304150c0e0402030712050c040803160309030b0a060e0619170a140d 75
    0x128580900f81d030411050042c240e40780a503660003070a039645924000740d4003409010b00009440012440050025000445c45220034810366001240c6244500000d904079000280400b034105000c1d610320144015000380b0b03904000003044250041003c000d45422184901d0303d4440d69004981000f103103a6440740c101500a407203140500500c0038000080310201c82c5c01c00744000060701c981c0b5221100c14007943c4080e60000c20a0705100c00d000c10058554003642c45030821040140ca0f501043e4244e00049801402085010016a81d4060940c21080940d0b4062130002c5580034080d002034100c1e00300f42e0300c0c21f00040c00140c8245111210b88540c5422002c11292503040500d0912070555034805d540c1007010414400921108060281c82e0000165078094850501884e01180080080610340302d084000d1000300003103105418100701c07600a11580d2030009030102d082c450380010721170010f1a121958403400c071901010940d48030079610710030f094002402c1000620074004000003109048400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 85220693 1250 85219443 85219451
    0x2180402010e2103070606060206090705090112050a020d0605160207242a0b0718061103131e050109060f0807110a0501060303110f07031704030c030c050301050a 71
    0x1507030700603510342d52078501114206031150303929000411484084480c800548408142102004502d0b003000341514081d070b08880881c0c0e19a80003940d40c044522030076030030500b602c0c0144134102042241000c618010411a200c4942d158040b52a03121716140039500690f42d0b605100311500d0400295210211510051086600380074401c2066104641f180e0300448440075103064690140c07210841c4151900e103c441821511040088169071101046402c8000540010380c2c0c98015480c52140c0003003282407000144c2071000c02c1d1401c130300c900400c80f030900c000d104007086441c06528401c00740004ac001e40701c1c0d06643c0350600000c280540c02142c10711041c2c8a040c00405e912040070907000c1910b140c00d0314283c80c2c00205640d02020140f00c2580c5000d41c080074014424150041c0c81160300c2039488451036403058410b99118031a000c030b848041e4100c0340302000450040c0035099410001d0b40102c5140683d2942c54500e01c103400c1e40f00f181c9100d000e00e803c0010b85402c2c0b241ca07034481200345081c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 85221943 1250 85220693 85220701
    0x60902150a080c07020d14061e0c0913110708040f05030c0d0609020d0b01060e03070605090604060e120307032d0e100201060b0d0207060605030f0d2604030c0218 71
    0xb40c4107210080c1885030b1a00e001c101c44082d580c3d0703c50f45402c0d46402181140800d0040035010f6280d600c101d60344034803044200c102e041c00322041e405503446800b00c075800c142094805410007401d0000810040082c584803407101e407007209100f0040100600c07c61310350345d80300d00e05602106810f01d07a0b80024420340084503844100d03100d00211004c003591103240001e041d6298400103181444546002d0903184500d00042805900060086046c0340708074100c3c2c960586c2c0c6c0408035181d01c41c50b507515801450500041144a014400e0801722450050000d9a03502181c0540d40c0766800c400b10980c00074a21410700400c80740a030001484010960008035a000b4440a01420020070201200d00481c401071000621502c01e61000b0041c3c000411910750310028000490040d4014071010b40e05170b45842c0000849150003d02100d02010748805030200000c03000b82a61061300c54070b40e0409910042d00300703c07043c42d2400800c511907072007a2210442402d0a00522003580141e0004c00ba01c030512038284 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 85223193 1250 85221943 85221947
    0x60103020105031b120f06030c0a0308040b0d201e030606040302130b031c0f031a0603060a0305070603020414030c0f0415030b25050f070201050d18060902150a 70
    0x140d42c06100ca490b2808105501071191013280b24601c9800281e59400c82031003528884084802c0c003d075011012280308407040d40812068130b8081c80000d0001c9000c010803c2040000005801340d11030790b070300004031500844100300d55a03001c8014a40d0030040000c1c2040f030110b00400a246400c1c41401041c1185441d0000c100346202e2808041e21800c000d80b100b500940c03480d044200103000180580d505080083d40900181403030306407042c007194100101d1700307806120380f240c0840c0550b0b0090148400c02460180891a40060a40d94001030300e9800070021030401c01110005040c10380d0300584c0d0710301d0724a01010068800342c01d07900c00d4001d802e072218241d17541075041140031000c0358005400e024000d0781181e01e52455000610104086003000f0329101301102c125002030003e00d184141d40310404080381d00c1e2107030380c4180c0d24000080c4085e1001d54418801340c0904403403504000b49009030300b441d842300051141d03c1190f40c5d0780c0f502c5a160860904040c0e072026041041003040c00c04030b0300c07180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 85224443 1250 85223193 85223197
    0x14070f0305031606020423100f0c060903050c071d01050a05010f182c0a09050a17130e060f01030e0c0402031f1806050109050a0302012f070f0503060103020105 70
    0x10107004080e00f0f40c000043c044c095046070014000b88000c07991034034160342072041d092001c80c80c2601c540b40a01d240d40113a40600003036490b660b00c0d5a10310340d04120f43d948410050004140580412009002440302080c00304000809441e9034420b0030340c0740700340700450865114140c11180c01205a8601004141d8028480442c3c510403424000e22502c26025039050008096200c2c94008510310403c024911391401c8900c0e904844000c080c10503a1901500c00607070340c9640005000b5485800301c8008100505148500d80b07441170384c094a44982144901c3c112441d81d000344030445044810310849240500433101c0a01081c20203010008070039a8598851001130382d410b00650700080010301e82181e042d0a1249000b001300441d202c01e80760321420340f00181800448201610308400401c00d5070207081800c040f00c800a00d096500340c295030045402c4a01440c800500e15044540301d4440c0c151001c10141200c500310082c900b580c0b0304120700c0c0c14009141e025900980040d00103001603644078003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 85225693 1250 85224443 85224457
    0x7150203030406051024020c03031c1d0a0f0503120f01081c08010918050105041101110c03060105010302070602190f090b090d030509010c050d0c02130b13150b030414070f030503 78
    0x404001c030406c140d035080e420a2084c110140c1e044c00006090601102d5844842907040d0060304200f083d181360f0084041c3c1c003e0000000101d82d4030008940d03001a0351b050b1700c440307828461001c3d03d0815540c0c5151144006c0700340c1d6940440d004403001440310b80e404004c02c82d42d10043d000c883c600c000c11b07204d000e40020b1040c090200c13003503143d4003654410002e8031061440c0f035901200803c490b1405013005412441c00b0849030340003400d001801140300300c1c0000c0d9821768000044c003415499203400d0043d0025170040004951441c0c00b800201030104007250132549481c80c1d07860301383c8016507041c00108070b2703040c9401151041c0f80c01c1c0007890240e1180c460110101d0f0781401d1891365524040c006840300001103700034203074032645a0002c0415448000c08500074400d542003041e03e0108950f0506071051000900c0d04001c1202d64807070010f402d50003800b8600e6048030f4a140c1c050300c54444c100143d104880645251004500000c00082c04200070300c024107100b200a40c00c1030a643d034041d200d00c1084 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 85226943 1250 85225693 85225739
    0x207031427060f0c0105090f0d09051003090605040c03051204030309050d0204021b01020a031b1b110301020c0604020f15030c1c0f0c03060e0106050f030405071502030304060510 78
    0x781044219840700821180030b0002904180d0715605032686040c040d24040b00d00458034014813450001c013034800241d146000c3d4030340d2241c40c0c0460500c820721503040710009a1500301901d85508102003102480303502e000714000d2140079803907429800e100c3d00d011401c0030101c5c1d02c10307030400040020035401026482501e108682c82d5403600ca207800000d000e805a01030042283e80703040034001d1020015401052110802e0b181404204d000341c0d94a040e07100c4090501002c2450081c8402220416500d0f20141c9841140c00303030a60b0901501203404ca80103200f8020103030744402d06000a41c0b5018035409580c4400b2907286000401c4004898594000600003510404003c1421400303802c0d600b0082c00341b0700240000b0081ca508d070110b0300c0c001c0e12003d05031401113490044049040b019100e2000d050f1746641d190545801000f0100304890b0384020419142c5004800c0003149060004a40300e035500c0c210f034021a16810982000c800320b80f009401001e178442e0b070017420000b58200c15006500d0015003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 85228193 1250 85226943 85227007
    0xc04030209090c03250e0c0a0e12030406030f050603030a1e1209080301090f050114280b07120c1a06010c0c1502010f20160602040902070314 62
    0x450b01d0703285030020211a075503050040a21040343c00c03041c440c0c0e01032189003070360641e4803542e540d0700d4100038580151b44811162a042105d044802e00424201a00d0134001d407640c020300500001490443e04940c019000180d1906440c02d070880881c010560801ca08a01551401c00d14090242c84000021035022803400048a4001424010071110603030804a4006100c0c603005458941120751090103450b0303006184c004601c081c1000d074495941a50010014054501128410001c0795401c003200c907010301c0e6620012100b4015000c022030000e08804000c85d480c2c8115190074100902e8494a0000708242d810450f0041940c9941914000d81104090f180356207603280121a0030f410f284002e00310f0041c2c0d03200024040560710520a090400d0b82c020081c106940a4a0040e25110b038841440b403002888106d1000203408020304000d540c074071040b601c1400030b81e1444c041e41c000d80c0c012a41954041980020326810040040c1d20361045100507103010415180140b4102c0030390203030b031036002c51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 85229443 1250 85228193 85228201
    0x801020414150403050102030f04060c03140c031803182b02060d060b0c0a0b06030d050d1d060415050a0506062a010207050f0106140102060a020f04030210020a020a0e0c04030209 78
    0x207404215030113103400070001c1d0b569140225072011081700c1038404540180c074011150713807014801d202d0001580c0d602030384440580c440303450310403242c0c0010740341028041c1c4221341003000c01d0080004040389031b07a040e009450fa104000070000d520241448181884020310703440c402042e0380580e4500e08a604660a03034a0b0001d10400f14010805c1d5041445041d000045488071a000000d542440d148070f0380d0501119a10201456203542c000144100031804c2441100407034011600070038295494500381e184504003240d48245041c4e41a141503c0a03021510b00c2150305046010796030380b28003800420b002c0c07410320301c000c03500f184203010481c0840b1110051016106013944050004443d03007000a5494080608095440354048003501303040307600c0e0000014000c1280241280e60710030507005000c890781c0d01515800a54411140003c112008005c0440142d490000004103070708654010b0100d0304051051100c2c1c1101c603080b20110103280c404002c1c0d20307101030040b41d056981c1034a6900941e25 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 85230693 1250 85229443 85229479
    0x31c051303020603010305060619060210021c0903091d0f1f030206030a1a120a02090403020109080304141009120f09030b04080705190503032710050702070801020414 73
    0x3040c0c0c0000754800400000041071060000b805806014103c3c0c0034440198a100d111321054024407918004d07800038018a411300109a01800d141e00800031020b4189041c40c2103801100c8240c1402c078082044014240f0411240c64200b0180e220000c4081d409801c21020f2600c0990703000b410444205003400c0003000c00590b103a0140003d660192a40b9100d00303080c0d009a020704540351001546c042280b00d43c8041d481c12582c0c0340c40b1051341c503001c2c050b4610150203016002100900035000c1d0344d00c1d81f003140c0004084000861080d40503040b24202041344500083c102801c08145980c1e16040c8003021010881c1003000b40c3d0290894282007210404460050303407100c00990002c0d1008190100300300910840b2001040c000e80715006032050080841069071891511030006803042d44184009140c8410300c495100700f80c0380c01096002c884114803000341c80c01602d601c400d1440c40c1c40b141407161b5070b90100040c5c070141c00e0001c000e6040a0402d0405482000846e00e403038441c0c0241002d01d11000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 85231943 1250 85230693 85230727
    0x703060c140405090c090301090506090708121206041112010b18010f14032707090605030304030c03060209060d05130302010501120201120203070e0d08030403080109050103110f01110d020a020f031c05 88
    0x551040030b60300c041c07405643303c1c0c0d21181907100e801030a00421080c0b40001c80b54504a6941c9400d81000001907143d000901c0010f201500245650040070849a40031300c1c07044450303a00820349024201d5036244020700c1e8140c40d003d06201035042c8840c1070322042150350040c081000c1115003421060300e9a441000249609078154044d018104642d01040800103002c500324095549000d024050140c0c2e501c00c0c59a64850380c2300142a10803201001d000141d8290000c0000000042031142414520700b05101114000c1e20885130158401180408041e02802081d005055510092101281e0342d000a402418400713003070f04a0643c0040040d030014042c1d40c00c43c0086001130844600c0c0521494031428942c02910282d0200b86000d000045090090007034070f050783c3d4800340d030090340300c1e29405000c664442c96100c103061220307074075810418002c1008184200d164a034014140c400040c01400300950700d04c804140070b9003061401301c003401e109111030007101a05182c915900c0c010206025165 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 85233193 1250 85231943 85231961
    0x40b130b0f0d0c05090d0b0103061a0105030c0a020c0a12020f030c0f0d060e03040f030c0909080702100201140c040306050901090203150411040504210201090c05010e01110703060c140405090c090301 87
    0x1404440c10b0007d02051100d81c2e4143e80c840c0700108034580000c06140e809148011941c5d00164081000a03004400307880a0049902c00307004841581c2036a070002264102aa00494030f016a00c402420561030720b0700100c80d03000815000350803180340c404d021901142230441400d004030070b10100d55041000651146031042c2c058003d99072515140c21102c0068401448245c030112084800032404e000c0c3c40c8100c561440d0300a549902c0c111041c0c0c2070090030803816560303405556850082c030404d500200581880355558207a0079603194290710b0036608a403405050306225078500140c074001601d0024803041901100d4011700030580e04c0c1d241c10549035684c001103079040b42c03c040030710041080115061900340c0051034085c407140c400e514105d00700c030719122000e0001d0165001c200203550041c0400301104006144c40c0030078094a442d00e030300d0000700d039004440d00d9607103c0b8051030407940325240032541c0f42c3c03107413006103004d2500c0c001071643d800c044d21344c0c0e100383c40001d02070740c0351382d0254030002c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 85234443 1250 85233193 85233199
    0x9100b030a020a260606010c02040f020d1a04060605180405060307090c02060114010804030801090b060d060e04060c050301030f060c03320a02070b0f07020f03040b130b0f0d0c0509 79
    0xf0780c54644242a0701c0b40c0410701c1d8030032290f0100c003104d0000c001c003080003131041d2810b9484a100502540811000c0c15000c2401c2110580c07c1001290209180c01060b0341703822100b240c1d2030100150030a120841d4101e500031001c00009025840441d03840c107d8485100c0801c8402040c035460b440c0000c5d083c225294007000002e40ba021810318069000b00d1040e0488180764558140e0700002d900540f1060310454004000440010051001c0300340e0f644625103007400904804e0800034508140c81c02c680f1a5041101a46034100801007005081e01841d14103850710301e030a0381154915a100319507400c00050050034a40c448a04c00c286c54400e5000c200402458240203440f0107075400030380410700c129612445159a054005003c81615000315981c0c0c0c0d07440000c44a031645c41c518101d5100324090000821070240c0c1c100c3c015151000c0000e000580081800c0c02d50714880d0354043c0d00170030074950105c4880c40f400e0010070401c0d800d1200341d5881c6c401150011a03c02e00e991001c640c135108420003998 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 85235693 1250 85234443 85234459
    0x213120210030e03120702070b0406020a060e160e070c15091103010b010e04050405160305061008070e04030c21020a05010f05010f17010603330509100b030a02 70
    0x208166082910040a402620201a41203a0141c100d0948a20380c00c4100d840d4002c110b001c0c110600240043c1d0712081d1803058451642d00c8804002c03007680300c0ea00c13000041c1c1c00804d031041800460b22030f08088140401c02000106e100d5500b90300c280c401c1e4800c1d040c500c244040017500140c001c400b01a0b00c10303071021075a0011445c6291020003003805000139150300100600d00d03411070405118950002d04141c40e1070900001c2c00e801c000c040d0000520440d2980920105d98240c9803e02d4600c01c05148a078000d8138242c5019040c00243d8106548030340c03c1c992050700c080041c03128000b4480d40051301803804070411076141c20484e411600c0c54582411802c0500c4180301555030100310003130064842e000070320624049490306c5041d14000c0c013600405501c5504204851581200d48900c130500d1003002080b80c0d03a407502d41300d91802c841904822039084689000001c0001d014012990a603180d00403c01800c190709400d58a00d201e600c7c00c0804d5541e0580341155641c1000f60003002c2c0c1c1e00814601d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 85236943 1250 85235693 85235699
    0x907140d0303060503101a03010c050d1104150519020601030305190e032b0314070c02010c05011a0f04050f0114010201061a0a090803040e061306240f17010510030213 73
    0x400141000c40f1f03042644088180180e08520f0103010704921500b0740c2d5116818008030060381d03c01031425641503000c1072010440026807540c0540c40c04542c0c0a551107554855201e904c0c0040c203000310304160011034100c94014400a600501510704030802c02044124241d503800e801d0f104c8024059805a05100b07071040d8180020003880b100441181407011101c0b00005220140d003600c40d802030580340d00240c180024020b0b88154088610700d8014540850300d0310032038503020308480f0491500740d24080820482c00c0207040c081c0342018058000e503000c100d18501501c40e49406c24040c02000b02c510040204110705d68402d41100b0068203101090700c8140c0700c1d440c0003140c9503108603514804140b82c110b0000e4000008420f443c00c403245004203070025030f41c000800c40750948070405000499030303414010482c4c00c024882c0701d4078100400c404070403d004401010706100b40e0020703240c0401c03d100c0d248140028020000a04584098500b1802114181800c0d400385c02107030303494014010901000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 85238193 1250 85236943 85236973
    0x40b0a230c0a03020106060906090302040e0a02120102030702011404020303070b04020a0b0c030301051212030a05131a060f100f0e030f120d110a050304030e12010507170907140d0303060503 83
    0xb07076070014480d4008011080e65080e066512132501d10443c4080b604004003040541096017041c1043d1200605a448101c03c586c0002da00d800040900902e070384d404010447d0150b024401c0e41d0007a20100000c02007440c05070300080d668414880020f101e00303403010116045446010b0f046029081c10940151150780200f14940d50303410074411903100740f04006100c03004800c0482c181e07031581184500c0628603500d40d00400007920380640400300c50b20b0f0725001523000c2182080403c120040d400d050603560305000d0308001d0f20a4060034298855080114200550781d0441014128001c89081003c8164250b0f00002d04111007100c540e90180144005c90314048940802808004d090302410051350346181d106180600a011040c00400c10400204010070300490408004070002005400c40c20301e410041400e65105a90250114542c1c032a001351841d0007201060b440295140100311691425001c5030120001800f81400307034050b42c0801b814584260030800140030041c08840c02202c40d0700c81 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 85239443 1250 85238193 85238203
    0x40f0905060c0705060c030115050f040b040f030302011a030d030905010212090a030206090a120c060216080414060304020a0e1905190524061c09080c01060b040b0a230c 74
    0x20458480c0915800110001b1100056078185d600d0303004108801d501c03015003900c5591008001e01043d540c10302000540c078402030f00410140040744203600140e491460b010303013562a020420f941c40303107440e107100310180c60000300007812510754500800c200b0b2803400c082d0f009206003a0783ea1103500605080100380c40f0006000c45100f8442c0e4204c4075290341e0603041c1c540310300d2211001400b00081d1040521118883c2a500041d40e0141100500c0c00d00b5250b142c11440354000000c4604d1744010034100071800500700c14001080301910558070f14541030b40007070080481c07805100d80e00310586000c2100300c100151030700309241404100700518145808007150468087c0414040a400c00d0009020400c02a11000c241c1c0c4c0c1c0111403112103520030003000250303003205040c4403403161644151080c0d5412030040503280743c0100c450690f2071030107461290a490454214980c8910300300001c00c41d01e145001112a4900e00d4600380741c14030015034103403506c0c40c1000940b101540d800319801c5440d40001c24 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 85240693 1250 85239443 85239457
    0x204150b0301090204061b0804030209040c0b0304051b010e09010e0c07050f0c0f0105071a09010e010213080f0309030d120204030803010b0a0e0a05010f0311220303030c140306040f0905060c 83
    0x150041040c21006901c60f647c4103180c00140000000e000030001030034409900c03500300384620106150252900311003085500119003c1e1000c0d030140c01c043d84090007070792900300b40718400c2ca80800718001500110300c1c043c8043c03180061802110300001c1d114040c041c16203074000c2d8010140c81040d29450100d903030707603038001c40c035103104255445001d1910341c007940c11122540e900844800700c02c0d560728042c0b044414002c1c01e4041079507d40e44032030584503013071006118120040c1c04801404d401c02001600c0c20b6444030828106620070486018031b41d800040400c012403140c034100341d4904d0101c24120183c090340d4001080144044000300c6d8141401001d003080700702d96601c01c2c0d02a000501045030000c5c07030f881078901150464114500191107900004880c1104080551a110302d0111038569003928610280d000c450514007030081681c54016802580030b54a080e41401031541060803080c03201524880c86141d98044882c00c1d4101d5801c81c050254000c03080e10301c5171809820031011079200c54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 85241943 1250 85240693 85240697
    0x240c0216050423090a050712050f030403050c06030916030305030604050f04020f0118050d080a0809010c1d0102101104080c150d0b190906090b0103020304030c0204150b030109020406 80
    0x10404103140c1003900c1070910343e8507200320b00c103a0300892681260301084044c007081360034041d212003000070a00800c0050001d010465000e1204410b031f08106007044206040d407000c0d500108030410100300001102c4401100480c1c0b025529154080c40519040d06600d4056509540040001c00d264208014520400d0180d80074001942c407808500b011120850b002503006c00820501400d81d4400c104590314090441000010700740c07107030002100d415414070200c9020310f00103240c0035800d0f400444036400c07031200c000034403e50700010405031031418040103c140200e440540c160380c1e40c0c42000760b201c04411501d03040042204a203c0d40e200ea5200d400b51400f84c0c490164281d07081d041003280c0d011406948100c160a100700401d0b542d01800351a04c8031a4015400099004100e2403421424000c12181c90001021850b008030340054498600342c41c1e061520520411011a41090411000d154116800560000c3d0403410b5120185130781c110108031813000c000810340c460707540e000f0400d07184a0703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 85243193 1250 85241943 85241983
    0x3030e101103160c0210030513060515031e07121a1510021609050c0f1204020102240f04060f0f061a0403081602010e04020f130503070f03240c02 64
    0x2120051310100031140000350080a0005041007062080c2d000607088091800f00c03a00201e6103880b490305030b8405070781d4440c251029000f80078040c581082501075004584941d628030380da1000d10a500c501081c404c250076810100d039020700308500603040c02440030007601d56840301c2c100441c1d002000b0281d804064080c0c184c0401c0301d1100e03400040c05100380544c03400c0d4800745070b0030640030801400d0080c080315085d00d800e0245090f0100354902624105402910862181c5458000289480e42d030074240d080000c0b03041c89000840f05000e113807c1c0d001c00116402c50050702c50749400001400c0100b0060616807030b1009107808910140c200c40c0440e2840020042140100341c1090f000b4411440300810001d010400c03500103c0010b0202d0b0b910600505113403180d01402004a800c3c1e070f0020761244500c0382c0008041c4e8101e248600b681c009048180c000f0b1003038906000500d4214140c5003c0a0070107000b400106d009034001a0761010316140ca200b042c40407440660001c0d64034440c610130155070b0806 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 85244443 1250 85243193 85243231
    0x31403010806100b0408030a030b03070302180a14010506070308090703020a080d02070f050604030219050607030908010f0501030302060a09111903030908060c0a05030a0207020d050d0909090f03030e101103 90
    0x501020f0360300b514046d001070f42c54503c0b180c101b50000c04200244d203130980150240000942d86507a84601c40c20010030425820746071a240000c112500c035072040d9101c080703c00042c00151078800c140d410113a41030401c454151543c444d8980340c04500c1d4802544084411400300d0b0725040403079000c610080d29000c5410964403030000090305c2c1c4140c001c3c0b40d00018240820005403504e128403c0c0f444140b081c00000d8551541d003c118035600c44481035010030240c02e41003116a2003442850026445944200001d506565000303458580c054041c803061500c4003440424040304811055680b40014041d18281d11031405010903030206102c15070205690501c00524607601140c514070404501c10303042e00d05442403505448541000e440b040420354244070031300c0182c882046810300315021300000e00c908400c0400060000c459a006404214100740003003001940c070804400302285c0c1420045031506c80d070003034a0b140100381025007084030b0a2012144180481000860058400c0c43e009025804 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 85245693 1250 85244443 85244459
    0x3041406090f0d080712030204061106060f150d0f050a0b0306010b0f0304210903050606031207060b0f09070e15070222020d020d051603051003030c03140301080610 72
    0x340103069402007544810700009140c0f01c50040c03100c1d0b20a030800c82c184103240d00c500945a1086140a02180c0d0004040c000940c1100703c00960383c4403203000781a82e00d4120042036040d21458480c60003903034403200307440c1e940c95540259400d03031003080c03000c000c0c0d4144010903d0107040141e445505a602d40315a5144500300883e000313058801060259181000a401d0f201c120340c002401501c0d10b6259141c1904060043e441114075182580d43d420b40d000e040d420031741d0130080060040d51190b8003040f8401445c44402007070300e0781981c0088002500240003004148000c400d030a5940d032107124103003005615500000541c00100c415140c40d510003a003010007a83d40e1040c0b010280d40b0204000f0305204480802c249481c0c03803c02c03804050300b08200143e100090340c11910b00348404545440411150503440312160144440d030345414441d82c01e119a06510007050347c0005020056900441014140038014041c152092140055629070307544482d9034071224150b43c1e056846a2126002418003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 85246943 1250 85245693 85245697
    0xf03030a090b07030201020405040e1509010513030e03010605031911060304020d060203101a04091a150c0102070b150111061603150803070803010806070507030207050409150c0203041406 82
    0x461a900ca80703084600705101d00001d034010103021021507400304000b08440d1a2070091011018460004102225402121486103a0000d00d500c556a140904000a94815940014240f034140c1443c01442440e000420f000d8411a0000ca40510540b03401e00541000b5414950141340100350000644803108200030080c8410b0700c020b54000c0d240b40307486010450a40c015600f0038a041d2400704c100b9a2818407280455421112401400c0c001c541041810303818041c46a4404170040300048100300500010031400e0200844030003080d0100d1169240da10950498502c50f410945140062805020102c020384c04006101e0001e21074145600750b00b540090703060f01800c020000a8154241000114000e0101c00e0f00300031100d600000020703c5002c00c1c001030080901851950b607407503040541c1c103450120b000d402d4208028081101001203a07020038440c081d11811100485c12006a0501c54215030f07031a94400b03800c5280104d001d00070b0350000024000c940b001902c00c1550030a07001086518 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 85248193 1250 85246943 85246957
    0xa090e13020402030a020c01061e09050f01090504140601181b09030b060112020f070c0609030309091d0d030b150403080301210503181f0e090a060909110f0303 70
    0xa400d00d0150001032510b42c001d0341e4840c1210b0f0b00107081030a0743d0341403829509540c5c0300e030030703404c85c12807119103140044814000509a116410f11907800c0a0040c031074035890512900c0140c0b69142c01040820150050b0b807076480541c8011107003035503120310000003d00c105e406600c100e28501060031603144007a012004081c45162108880c82c1e28540b920241080c00522340d40c10890201c040c891504a0f5101604103020000000c9440710818600700100300781030381089007400010b10040001980c000201800d4822810380818000305050034100c06001d008074581007030007121001880340e03034036500200c156403080700c01d51401040c0c40c030148460310035400003501410f000c0005101e150465401c4d01d40980d13000f001043c0c41c1c100e07a255141103411021006681004a4106200500e4802004426501031588940c1154481d000251500903030340741017805060b40c000000c074024001c0c5d000741c00401300300324103101e00e0b442031410980d03c03103490300060302c40c0d116899807003401d00f0004140c440b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 85249443 1250 85248193 85248211
    0x1305011203030c110a0c0302040b06070209040f1a01030b0405070b0f1605100e030c0705090c0304030c02011707030c02120901020a081602130605030c011706010e0604090606050a090e 80
    0x640c954078110702410031070010805010700c08800b103c40c3c1c80100080072800d4043c180c1c040780c890540c0704000070345074a071208910802d000c3c0070240c00341e568800520b40041d40004404610340c00b5103841c00d0720840a5680d12042c1d00001d00000501c0140788d0340900c540d1103401503401c81030300c40c224007071103000341d03050490700306030030b00110f941101c0c9000d0380902d141c05801240c030340301c2000380400103440b1908541490390f0008134886e030750b4000402c08040035001c200c604071014030302407514004902008101400300a83c40300070130150390040c07152007540109031180d00c5081c6480302016004d010001e841c1ca006118802451003207000e54011340e152101c05034003401c0504419103030611203800c540107010111224882e0440140d135160074091120301c1031640424601c5c5043d0800d400c00701d410105c581032103025403218881e20920801c2650102007420311040c0d00701c0c04000f0a9581c00b464000020007854428042441604035014184810180d80d0303680c0c8144d114074400700c401c90300b91384290b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 85250693 1250 85249443 85249469
    0x40204050703060b090114250308090c090a0906090501110c0f06010b0307030e0717011b050309100507030b0402070f0b0c04060206070309020114220b0906070b04110a14130501 77
    0x2030747c441c1d8880320401c485004802c2c1045142d080c5070702d603510341d500d0400a0079890a4440101500312014035480744c000c001a0000f0410708000c40d40c06007006003c800301f16981d15105003000020751140200c9904803000b0800c0d0951000c50282c0c6512111301c4202c80c1c40b0303941e01c4503d221300001d06076040e2001d6108040c215100d4120036000b60690380d400c4900303801071100109015071652401441d01484030004101c429145190f0048100d1071000f41003000741c00c02c10410000700004480e0500c4058000000303241d524190124028005400d46503030260000484101b8000c0011004031168003481900e4001d490f03000754282e45105521074032002d0780003400001c56280c060b51012000c5401070400d006ca80c01c055000c9032007540009864a070180307002c1c0f0160300e0910300e101040007030703e11944001e207071110640c0000d08501031601c0080450130041d000404121f40d84c2e4000d03051500c0030704a41300c0d054413140850000500e03030f06003e0040440c80d402e00c1c00e0742e00303a008050494444e400e06038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 85251799 1106 85250693 85250707
    0x7050a0f0309050a02090a0213030614010b03070c0605090304030c030602031f0b07020906130204080f0c010e091f0b0301060914030102040b030f04060b030102070b040204050703060b 80
    0x9030405103814200400184000341034010550101e4a225190381c0e040d90300f801a01c1403620b03850340c6001c0b0503400020402190043c2205241164074a41e0036a00c404548002e40801c035040d9002416a50700c0b03401003107046d800960009030b002c0030b0f20b00e020b0316902c9043c0d270003985074802c43d9800c3d4000201329030040982d805110800c104010203940130b18010070001103004400c0081d100301c800002041c02da54606801c01d00c2c1089280041d52201d58510029482d0141000171001901620229922a41c03140e011a00500c400400006041d00e50f4050100c081d142018120340c03020740c804000c604509010055402070041c0d6890020b89801d10402a01c01e96001c0400d0380281e0061000340103c030400402d0f00d511852000030303031000356503a04117100504a01d035007094055100103400c00c10302c4020502036200d280296020302980e210a20f0403022140c2718800d24009110902c815 = true := by decide +kernel

theorem cover : BRFrame.Cov 85071943 85251799 := by
  have h0 := BRFrame.cov_init 85071943
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85071943 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 85071943 ≤ n) (h2 : n < 85251799) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
