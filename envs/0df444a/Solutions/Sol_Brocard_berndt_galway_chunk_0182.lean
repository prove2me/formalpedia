-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0182
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:18:24.976468+00:00
-- url     : https://prove2.me/submissions/f1ec9cce-471d-440f-8720-69603776adc0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 32553962 ≤ n < 32733818 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 32555212 1250 32553962 32553977
    0x702070509010f030228030f0305071a1b0903031303030c0c0902030402060703050a030b0d0b09010e010605060702090601021204030b07110604051c09050301060b0c0705030706080a0c030605090f0f07 87
    0x5601c070030502a410907003501c6c0d0f0180051569a020101e41c001d600040e15402611000c0802c05400400814216003d0a05d4108014000040c01501d402c00c540c1c0d079920300703034546000506001d01c602800301c0800041c2982d003402d00c154030210840300d2a41c400c0d1f0000d2841f030407040500c2800d466801c0503004219040d45145005d801040c1d0901c5101e4000f403c102000a10310002807095100ca88200002410b124510010742481140c1c03103c1a00d028405500e014503501c0071460510500c0c0840b44041c20103401c0459039000c0012040e401030a29041d4001c00b988071500c00064001480914443c40994480b401c1846d0020105101c0700a104141c0d848541800b010410000d40c000c501c440c0c074070104c40011171003801151035101c25480250150300309500814803019450240034564580c2044500243d905c0c0105640c2e01e50300c4c881d481c04038005d44045440c01002d0713005001c0301ca034142000710713446590300e002c50388581c02203624152107034503407080c494190502d5220540000380d6161012 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 32556462 1250 32555212 32555219
    0x9281e030e01111203060a0806040b0901050924070302160507080706080105010e091503030c030405040b0609100e04090c09090210030e070b07050a0b09060403080c07080901120f02030702070509010f 87
    0x81d0313181c200d0769889038000360200c0003c500d41e0f100c041c00320203003095605030b41880c102442e10040c0104259240d180550034000040d941c0c1c400021a0865082d00070004080465912030313440f8803000140460007015020820034042c4405030800c88000d82c41034000b0324a0741c0c5001010b60415a103904000108040d50004111076a07012445100c3c02d0811248040c1030f403501c0044484041e0a0440c19825000c08101c00310603003400700190048400a86003030006070000381c10014248142050b045c1e220030003180c04901c06215041c000e02890300644005240c0f4440e441d0701141d80030a81c40445510b0b00e44107400c0442c10031304204d029284031810180901100010b51507202c1000d07020b981048100414040148002007040e0f1307144c20340014552040382020f40328140c84000480f0309401145242020544201a032002c41361500d401c0398015051964510044448420309880d1511082c0c95100613007000c10030740b0045000e03801d03e4004005091414050081c0b122050f8401c0c3c42035408500e042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 32557712 1250 32556462 32556497
    0x27070f020304241206180b0d0506070c050c1302030106030e0d0207060c11090a140108030a08010317091e030c010e0d0816050a030302040509090609281e030e01 70
    0xf0381551022000c040d0078203410740101c4005a186490324842410007100081a204c00d031100200601c01a4051148100000c03d00103081d482403001400d135441080010140c5101c1e4840002d0903205600340c3c0c00d049840e50014820441260070b00c10041da0000c0104080f0f0740610411403070700c110b01d002d0081d4203403034a4044d4841e0994072402041c4405d038102d81c01000001c5500c119041d00c0201034000c1400d102a800004020300500c0c184e00c0c40d05003001042c01d170000400c3c0c5030307107620594500140f41e003195030385030031841c04840103141c901050002110741e03510880c44248454082c0905148060b180040506e0200000400c03411b1040b1041c15100ea521201454050582c200c8840c59880c203240c00e00148954007404090182c0c0156500701e420164550000c108072541180c480c0041c1d1541d40340307151110303400d94090a213a4407100c8070150750020194100f8140c28100303800005005251150302e031814030746890440b41c07088000c5100070542c00900c200302540d0f080ca040c10840d4640e0020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 32558962 1250 32557712 32557739
    0x90b0403080c090402031906050a0b041a0403060509010506210703060b06090604080a1109131101031803020606030f16060507020d120302070201090905190b27070f020304 75
    0xd4100000000080c1c1e144010808a981004020b0421992480c004a0031442170000703501041c2014200100003038180740c4296440d041d99803200741c1c45d1a252034078121090400340c01e01001c0008000740000000b013036484c410140302d01540000802d09282410400000c2445c0f2003040c1e200e1401c801154101d02030005680051303a0f0b0102000500743c00090001c0d5023801515809a802603000602188903880403600303090080c402c01107440c0c40c8240408200942100b00c03461a0340109040c04540403032840001380d103605506050020f85040800c486c0204002d0b014019005a4450424041c10341820064088241c02c01d20241101c0040c2c04492440340e01c2c0f52061004104020512000359030f9041d2a030300c038096202d04080400302c05201c0240182d00009000e80c040f03038000c04009030741812070182501c034240481c201c2d40c102807100c0019004050041540d81c0052030b9540d610445075014403400c54003c00050000340ca481c2040c001800c8220600f40d010440d081031104000f500e405040707 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 32560212 1250 32558962 32558971
    0xc0509090c0a1704050703080318070602011a09040c05040213081207020a03030c05030c03070b161d04020d0b0a060507050610050a05060306030321060a0e0f040201081306060e0609060103090b 84
    0x900d0703043c40d00c40d824064500002500050b01d002400410b1041c106480d4280b0400c40e800c4900341c0c1c1507160303030701c001b64222422407014020325030004090440c07914090b150664800e02c10794017039540d5910b03400420f0403a042110b0b0b58443e10b02c01c24051000c0e6004010001c0080c0d000d4454a1a011407980851001d9100b448002c042c40705403a0310300c0c100a014405d40703081149c0c0d0811030b1b81742c041904259524000995a001902c0580716500c1241c2e4480c0114144840d00c48000c0c40c0c01058960a0000944c401c0c8124901280da5002d1112a90340d20080ca070001c0046d559103a403101040d0416074200b50380648040f41291071100100f10507100e810007402118001c8401b030b9203d60304c820100342584681d41c070642c52006060343c52400c2c0c0b1145046030340203803c02d4411089454603005200500030003614400403440c00c4000041c01503104510303260348100b2041181c143c141c0b60742d54030740c280d030703a40d8000750482561482000140d040150661780c1c00a400d01c0c0500c03540d0a0790702d40310710307801000c0d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 32561462 1250 32560212 32560247
    0xf0d0216081b06070311010c081602030702010207060f0c02030304030f05160e06060706020d0203040605100801020c032703070e1905010b0d05061c080c0f03040e01060e0f040c0509090c0a 82
    0x1a413100b810300401c02c0004460301e14000340111481d1204c01007540074201c408401402a103100d00449600c0002070713400495044e001816024188201550030b44800040caa0410800103810310040c0c80038000741c0700540c0701d0340000305400c6031450301c281051301200b80403221150b1041c00b005a080038038000c9401010079655a1781e504040e0921a000c0d22409003030071070355070000090204000e1a540034a104140c1f40940590003916110842e00743d1094040c0d040c00e50b803090201051030103000c01c204bc510002c511805a504190402107420f02810b2340c42001c2c1139124030100314a1821100d0f03204410750042004110541c104410300c00d02b800b81d0120469200c1d42d13100020744a8840c00508600f01c85460300703070584440186808065540042c032112014040e008200421078000003c0e1000d541c5038800d0120680e086c0b00c003c03a86841c0c1c0c1c08803181e004180501e10861030b1518414080c410741c1a0780c0706580e401070072050041c0950054000a030750601009204111544005c03000142c0c0c2030030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 32562712 1250 32561462 32561467
    0x50711030712090e15030105090102090f040b1f0807030e0304031a0601140f0403020f0a050a061209080307050919060905120a0c0803120915060603090f0d0216081b06 73
    0x20310111001c460603049010074880c9a024051707140300c3c102e1003004180701100244002d0b40c4d100340302402d0f40920701c600ca820144040c0f4400c030900d81500100e500140140992070300d00c40b232041c04418490945c6000d000315a500d414040703440d03814000d108404110800542c5441d2a550302c1c0c180b840d4111016095007032003803001c110203078810440c6003210341c0708400d0f01d910b901ca2038640246560003403208911984241e9141801820017200070000c8590007030400750100d150150641d0300c00030644040d40c0309980d41c4c1e82c05000820200c055170003148603680b810b031141594000e000c50b00302607903881d8401c1c1550340310401641340c0c0010704105440b01a01c1030003440400c42c210303134a001d4040c00b0044c42440030340000b20310420004050602050000d5011400d601c803030701c040d42c45e80c8041001d0720f56a042d03580040c4aa0078007000468101642404880900403120f0705035044c151850b8030100144c0100d0700403903100e2084c980030700c068800c40d40074204030015030900c46103280407205000e004032800b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 32563962 1250 32562712 32562743
    0x9080601080604170903011d16050607032601060816020a121b0206040306090204060e040804030b07050408060708060406060905010806100302090a030309090609050f04020f030c03030a03020309010507110307 91
    0x404d01511420300003c1e00030301ca0002500e110084442043c03076020010f2007041c003000014250244440c04842c40a00b40e1880c042050700c003160b603441c070b40c0000503640310b020f01a8207203c014105028000c00180d514002d9904140c000e039807995038202003800031035120704081c1c400f0071040101800600858180b81180110018200d10072804200b40a980800301060000600459030044640303140300300c400f046100c0d00c400c0c44941185068402824500c414401800082c0005250f1038000c5140e04240f800c0580d83c0403440e141c9001100c820000990707003000c0c00003604050181e0806007503107007440c080362420b110008162a800a040c02c0c480d10504413080b991901075070445590038400750541180303948030306010301066414800c44040514000740013400218611410380102c0d000c0323410ba8610388840e000c000d48006841000c550500405050b440c459504000a1510a049482c00750b00e03031510400240c01c580c8010000000d014001150a0850002004407491580d00541c8188205407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 32565212 1250 32563962 32564003
    0x1005072003070504060e06130c0c0609020118080c1201020a020c01141201170d0201050601080406020306040e031908090d02030a050705010b0907030212070c020a150c0b13020109080601080604 84
    0x1850f07448142c00c1843c1020110300c0c0c10305a1100d901c00d00c41500c244090109042c4040c007111020508078001a102800210000b41103421103540c003401407615410803c003e64803521401c000340e100c00035a90015524100c5403c0c008440880118004004c50800302c1c3e901e0065181d4001a0351113041014405020f05070404400503541000d9000b4446806503841d024422400492541c0340c425078402d6600c60340b415031050107494490308060791100016240c03599004003a41010b0090b40d8050b44840462142040410103481440c4d190340079120703407454203c400b405289001c0e0041c58250028410b0454840d00042200c007085010315042d9501c01050074094010280e54080707980c0a011041449400303945500035106a004a4038a2449900d40810580385034a903190001c6d00500f1515003003140c000300c0902801c00b01c01c542880e200f07080890381c4120303a10204507401c1203010780c00c4070101c080d56480003004001d0014940200a103504001d0343e0740e610040208010841c03481c1880000e81340c41c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 32566462 1250 32565212 32565223
    0x2070501020a0305010305191509050f0a060506040e15010519170303040309150905040c050c1218010906050904090f021809060709031502070303020403080301141005072003 76
    0x160048001c5441d0b010b8028001c02a09082c40251441c6c410307540382c00784400c1054280c1081e598821a5021101902e4003c80d015040c001419145400346198560b00e0b01030901c007800849204080000d6030780381001c108000c5030000b109410080d80600c12001c0d014101c2c0c41c03003d05480d030485103115100510b4aa03424149a2500301130300c0a0900c40300c0700b414100c004040e42c0224425121845010b8a8844807000090420800d00009010a00c00c0246041c5a40b10310610313000342c80c0c80c2e332500d040b0842040c6844025204081c140200213410303c1549520101c0112040003441c100010a1803d0001400c41c0112103100e032007107035211054020440011111010b281c2e016041642044d800b400f000c0b9a00070413600701407540219030000303000610440c60f43c41030341e2384120740a4901501030f55800007504840401c0302419805c00001c03000c2080b080c040c1d0b0082c070710761075100329180014007480403100d204441101481700a01124001a91907407403264600030b25612891250700c2e803070001e840c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 32567712 1250 32566462 32566477
    0x161d13050d02030a030c1704030f0203040b0a2001050618090a0c0e06090601030e120c0c0d0807062f030601020106090509070503010501050a080a081605070603050a050609010b03071202 81
    0x140710310111104020340120207401441420b031810002c0102050003640c0205484100d002c8071a00d0700c00003130000340154004200c00003148112420715460780c0001c00c2d00c0d40506180c1010400d100c1d212403240180121920019144100a1200e81800c1010900c210b40e623140306101f1004000020700c03078074010090180b1141c0c0010b0800c40f0305688030840d081607081a41c085010b00c072041c3c009901940240586c1c03555994040041ca084600303048144000d400842d0b00200074012512850040d03610808548403c0d402109a03580d20103551605004840d00000c2006916070518005240e42480804604010703500941d2288c0c0d82d590240100c0c01880550025040c00e031a003020700503040ca0001d1940c041c1e80c2c040c1c00802c996600c42c010803035219101c1c1301321303442540050b0841c00040c0405001c3c00b080d020090048880c030f8080e998180c00d10440f41c00c014000703a5104c040002d100000e00a4a400c080700741e1310220309505140170241c0d00e00c001040d05086c8400100c0b41808034a40340d0407201c19 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 32568962 1250 32567712 32567723
    0xc030a0507082205040f0b0105160312050903190809070918020d0b090d020307080a0f020a050a03020303161b020402090109030c0e0114120703020f0a090c020d02161d13 74
    0x115940070f0140115600c0a0003928040d40c94001c1035940d204d0644034043c004013058551074100030ba12501d00d02c4504070444222308121a2120503940001240200c0e07004504045c0659100c0c01d08a24203101096190741d800c0030404104203110f202c1e0130216400d4240c8401003000701d68051442c005204010a0000082d00088407200d20030070300c1200f807400d0f80038040050a03a00848561034040382d480c003c1c09000340424900300021201c00c0c1c064910a0104c1c1c41074010384031150250f4481e40d08005140070143d001da00000100204a0b004004405000f0000e041000d001d22000d07804a0100c080544000e004640c00580c109050380581c410900030744d0300003181e00c14241c0701c0422080050f030a03c2030104171b20031079814850500c1c1c001030006c2041e10050081601a2441d02000340c05030701b0780d02658000f40700a8000c0f803c01c0c9a4002c903a40c4405640040c00340c41c0210500902c0d001c540382c40704426443e080020300c040401410000310100f06001d8072070f00ca4460200000314040000c000030300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 32570212 1250 32568962 32568997
    0x20c03130f090c0e040203090c030a03030c03050f07021527030403060e0102040b07150209040e0c0a14010909050612010204060c030f0311040312140a030e06010b0c030a050708 77
    0x2400c15016498415606201400604281e90b103280340281e400700720800b4089001c4520010361400e00d54040c43c0c0c014040300c200c5a80d0160b03074022034240000000147c0000340c464a8090303040d0f4050003542d41225000b0010407091400880003500c4203507403104041206001004211304584080301e101d00c40c2c0a141da11a24082c1e500d0007180d90358002e00c4200d0b5a5401c12084403030000040c0700381c404075074010103030518009295458802200305d502d1801a66079017070010350340c00d803103511a10384003444010003008a001c482040001b0410356a001171006151024060410b0340e00c6005601112100d82d00419a07032160300c00540c5e0103c00500d6050590320100e000210300fa84400c4140320030b03000e0703122884c1703000b900c0c01c0c11030030307603010035003000e500da104100810020300d184003000001c410703078a03105030801e500802d60314095000e1f81c03032000065203802e14103282c281c0901c511070060114040705441c10b10303004020764aa0003203607241001c1c840b012a1090520800c42c2c100ca0140303400314145d41 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 32571462 1250 32570212 32570227
    0x4080a03181e060f020c0309010c0303060305010c0518040b030c0d03020a02090901090312020f040b0c03160b09100510030308100305030d06090b04090203100c0905030303090d0212040e0105060304020103020c03 92
    0x14441510000381d0b0a203040000f0721074840018400c4070030b0108a200074524201000005451600c0c52b07540840030140d54440010100c0c10030b01c504025031035039a94641d030780c03038211a20250200c0000e55a6108070328019480400395000240203503c00390640e54440402100e007002e9060444641e00650058060402c01c13000c4031b8190701421000e07103c0d40324442c4290714403082c4001ca000b556003459200708200030a10038641c0d0080900700039024441184d1070307c00c00455400e29105031501c111005520141403002c49603003880001070515a1420410803464139811981e0400c07803a101c090103106007440490901c2001c1540714010b10340000803260750790740503410600240300502c18410164501404841b5a1074140039091490350020003c1c1900d01000c09614010b002c40d2080700140089440009480d840c140059481040c821014004505c0d41c00c002a08151071498401c500520800c4148012117000b0784082c19100160341b541e03101d995a10068000380301d510350083c4035100204800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 32572712 1250 32571462 32571503
    0x6070204020706050609010609030b060108040c0909060b0913031407030c02030a08030601080c040506030f0c0c1006050f010c08040b031506042301080c0a08060d06020c060403030501050904080a0318 87
    0x617005640548460309143c0e81c880c0d00329100c0c000d03400000c2014048501040d241c1d8403c3c1001d540003030062425510f066941c2c1c402d51b0441da90054111601901c0311400b0105240c0000250380c0809603031b005554401031903400511400700700c45840d490100c04a2188285407085400c15101980541105e003030402a08124019800c216039080c0041d4111000804040c0048103640c104d034006082c05086403500a10f105080c00f00a090740e040e1a010300c818440190100003048048814000c002401c900b0305047c4003840070840b039a0707030502196128440c0091004002c0320f00b101c8194418030745036114a003823000100b22002100354001c03400301d03020a0071000300c0502040c00c2200c500b9546450481401521043c408440012000c482030040e83c86060144a0007540014020400800c2440d1a03032000b04076048800a0459507120a081004054040c4a200e001d40f104840068017807516070340300d4580b40728500d5408200360715074111440386e008480f54540c0b400d03807244014a180001e940b16 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 32573962 1250 32572712 32572721
    0x70902030c0309010507170c07061103010f08060138210601020d02010c0801050d050309030604120f0c02030a170d06030605070e06190e0109090e07060905040516030b06070204020706 80
    0x741c442075460000400c0556014000351003000c0401f40201d40982c1d909600484250015075040e10702c141c540c1e080c1307a00c03000f0300001940030b0401401c42d100568108031555146c80c105070022000d203140d800c0765414142035207440c000c00c00342204141c1020000743c01035004a010b600c5400d040400860ba200c02d090030b200845611450007a0300f121510400307240100c0c00c0c1c42c007041c1d100020407070b080c00620450510b03e4600e04074601800450b480c255080300424544041102e06039000510040640c0070341e0f90141c66202c0e00003851908040303011251f000a0f480d98071114004008a040c3c0710070b4102042410b090707641c0e10f402c4d01343c104107085d52400c00c0b4014201c100c660000041f0400380b06480380c03608a003696818001d13404d100c030003011401020344650306100c00c514180141605e00040030141b07405010301d14a0b000015226a514000c4050f2003001a40c200511840c100400c20044296004000000c00d0389032a010502111040110b0204c0c45030000103034229000113002400d10203107810 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 32575212 1250 32573962 32573971
    0x70801050907320f0f06031801060b0403030504140103180605010302040c09140603090a02090112021003020a0f030510051003151d0103030305060102010b0a06080619051c05070902030c03 82
    0x3070048004100e00181d40300e0b04900383c28a1420181144000081c1000b28050103070903006442d41c0480b408030000129207410413110b621700c1540084049001c204280269030082250644544c10302e030031a6809486801a4042c0105449910445443e6a0b120344c1048860500c1d0700d0b050103411070181400e4001d0f00302408264000d03820242e05115040c85082658100d6452103140050200003804010103907101a01e002c4d51881200d10107009a030ba607202480c020311100c0700102d00803429205200d640c081c0005e03c07109151061150640303054204440034610351851900041c0d0b99500481d00e038120710307990086a0010f0100e41e003500499090390250408021106c1d0340b030480e541c0c80b420216541403400d03403840ea024001d801000040c1c0240c0015820040500000c1207001c2030102190207075a2952064001a55160034400c0034101982c0c1d0b4140002210408030340c03613080030041aa0041d04868203020700701e090303580340244401800918042e22010005541e00d007004a919450f9400070364 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 32576462 1250 32575212 32575229
    0x1503040803090607141206030a060e0615040203060108040b040c0b0d0b010206091c05030406061517071d210303070216080304030203060a02030a020909010602060a0c020111030a090302070801050907 87
    0x100032480d00c4d8014a0314601004040903200d03d0420084100d850100e0040c3c107045c0c26104522104d80011218095080d070740c4d0a440007058180b6043c4880700c0e0401c0418075290080344100144401030340d0209c60705901c541c1000d40c10480341c9403450040ca0820543d070241107900c4000ca216005404242c00c00c660095099007102c8203030b11520310707aa40740e86071041c0d60340408590303090704481123000c0c001440d4483c0c094100080c82c603a407040070f40801108445000002801f80781c0381d00440140b8840305401209524184401c10b55940f4822140901440700c14400d40104c06030350f2280806040242d040c0d030321202a80c1d1030b4100300c17802070754644c0d032807911060901d2400d0020858400000071340b0100c94000700244255180c00403954000d61010301002d0380c4540030010030080b074407801e229078001e1005e94000d10040c40d214500008844c40c1400d00011a41045a810f0200250105403904140b01075000152400246070903898816103600403d059400c1208001c045200400c2c1d11084a4001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 32577712 1250 32576462 32576473
    0x150c0a0207050603090a1103100f06051813140a150504020102060c1207050a0e03010c0207140301110304060218030a080705060a050c070609080d0906060801060b0a050711150304080309 81
    0x8104004050000300c9070142190b1200009501040117691811070601f0040c06039101249004900340607100d605109500190702d54138104882d08040e80d41e84141d64010f0190701042c14181c20a048101e442c4d00301030010708107001c0c0d000c02c104041c03011400b0194000d2126643d12844002540600700884082c0d0147c050100003845034140d42c8200e4400b0081d01c00708480543e905041943c150300708200e40000c00200c0da441c0c00c001e031002d10911210b411182c00400440785802c403040c1e2000c0c1c048003110f000741d040c241d20f032100407404002c0c5ca4115500040c00360b160400d0700114100785111056080d814414019004140070490008220a60103401503d000d5078500301d4050030307114195007030b82c40b41d4001c01c45040401d0075540403250300da11601604d40f6200c0100c11080590b0f10a0500b40c4002d5a100d0342040840342c24400c1c00f0081c1541251507050401c03501002d80315024200e4054501840159001c405a03901900d2003500310010f0325407500e03801c20b400c040c54690000c071500809482003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 32578962 1250 32577712 32577719
    0xe0a0521010605121c030c020303160203070b01090f050a020a09050f0d0203010204061e020105010302090f0a0932150408030415050c0a030f200a02011b0c02010219020105070f0203150c0a0207 84
    0x1d00547c00701c00c40c02c1c1c008500c0c607251500d134150041090a03010381180420701080c40000c128a0845000300450040032402c48003203400b24084860280090038038902c10003035803404581004a5404175071080300c1c04610ba0411401140c003c0900d8007000358154400030340070980301c1e0000c1311000014400000300c22641000c2000741d00300d030002c0c000a94840c90f00000141c00c20307204200744d2341c040032110317000c01c5802c019510b1144500f40070060040d5420070401c86455503e60b062075100310351040340201881803a0403107040400b500600702410f45a80080020300340024100702c0901d140c43d020701005070785480c241c5049140c11240300c56001034100040016541400c3c02800510001c9030000c403c813001614600c01682d01903043c1909554030340e055a18000015407540406641a84980030100894400242001c000d0344440c01c0c080740390b00e880c0c00542d902070156016660b000c01c40c0c040c100c0480c000207189c861944004049056a0300c1085207100e4000044c10502c1951b8007111000c0d40c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 32580212 1250 32578962 32578967
    0x61d070f03020f04030b060301090507030b09101b05030402180a0b1302090109060e01270611030301150c0606080a0312050a0b090606130f0e04030e0a0521010605121c 73
    0xa0503501c0c5200300d40074030085c804181070400040c0c0003e002800000d03102d48030703a60142400c18991056905510203802c20180a800707004005150710580d10410013003d151710580458440c8191060800c48080009021500c8071f950900d201c3e01154081c1c0701c00e00d002924103028040101ea01c038043c05014065409404003030090395070307825058540c40740c0c9506043d81100c5a00c0341c8100702c0d040011040c0c18442c00b4a0800624050140e105030b80707108079007005400b400380742481d05c895041d0341c030030401003040c8489400c40c5104ae03c41303450440202030103800c080b40a08070341d400813030310380c0100c0707800c402010303008454201245000c2e003050020780d8032544070b04101c030061a621600244140c0000d002c6250600081061440448402a00702e461340d00340794000c0301a8100f101c0644040d0280014190003921141c132100046807064400341c20310000c40c040c490341d059072140c281d0245d180944442029081040900301c05000c1d000d2000d40b840c0156601c2c0c2c061411158040009000b8001c0b251 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 32581462 1250 32580212 32580217
    0x3110a1203080f06040b040c050702030105070c0201020a0f0309090204140103060e01061202070515091006090b130c0306050411092407081309090605071803030206010b0c01061d070f0302 82
    0x64258030b50092030f550351845522484402808658042d81d01c80400956540b24411001c280180e83c0d07640e41c81e00c2c130502c14035085400c060440d0084c4030034801c8810040c0e0340007c900a103203500c10f411410180080c6000e40b508a92901714242c2c0078000309010030600803418421940380704c26601406043d85d9449040110602800760758005010b910607480a146549c00501d6894854821a6650840c1c09000405818265000b0314650040300c015a60715249000314405400081c40410450704d042c00007a8401b80d45010880c5055111580245141d000e640013000610300980300f8440c011040041800c540d004103541c0388502280300c41c2d2980c2010317121011208841864820b440d1407100d4403130501c02d0308010b24a1001000810000c5680d0145008400005205060105803420310540150040c01804000f0110070050241000070a9000450303504480341c1c02e80c0d0940c0c2c0c0b04495003a60240c40d05030001120501e2202c21a0641960036420903c14035860341c400b4101c03482440c0490603271 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 32582712 1250 32581462 32581499
    0xf050c090c0a0f02100507020706080c03070203070b06010201020d050907090608030c03040b070f080a1809022718191503050c041104090e0c010305010512071208070c03110a 76
    0x40c5001d01480035000d004400348003039403d450049480c000400c801c0c80094400440d4048010380203003104022070f50b04000c416410001500c001815403a180c03130004d5030bc3c01010304c0075001115900125060f0390007941181d4198001030018812480c100c0c0300b00f40d4a00380d40c41040c22892420100065042c0c020080c0c442d10840c11001c0d500d0b003031070040018601d4108140595204034130b810f1040c00100000c00900354081951078444104c040d868a440c0c1100b00f56003d024200e0042166203110fa0801900700c400284d11a59030034034013841e501069006c1000e2100c1d0343c40199540078032131a250080b03002040b101d4004d800f03100e10113075191803042400040c80010032551100040f400b1174030b4950010070301441414001c0d03003000d9540c46050203903a080d1201c80a9a0030000e0030f42402d580c54040d80c2c0c05403200b40c402c4040c00d0748141106945a501e4415824104c001003500c0e001c01554004890100385c1042c21310103115200d090150b058038100044501c901008900010b225000c00d0f0742c030480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 32583962 1250 32582712 32582731
    0x90d0506060108090a1a1b0406020a0201020c0109030807060e0f01021206090105040905070603090303020f030a02090307060306050d110f090c0c0715050708030901060302040e032101030b010b0d020f03040f050c09 93
    0x480100030090712a2070000d060082d00f100b1011f200c10350408188064802413070300d6030040210003551700000e03080c40c1c42c0480171410054070f5503080c000f290a000485d102c80d41c0c00000041d425042d00380781414128440029107103940009070b00c0c3c0c05002d14071403c60080c041120b60440301d0b683c68081204480040380018141c0c0c0010b60108640717400ba0b80081e40107406400e0261800200d10800101548102d4a04a68540c00b2030304020b035050420a180c00b4000d9403c040016030306103c0000c02141840c030303005003082040c6400c00710f10b460f410a80a02004090110101810804405106a00070100e010710520503041d00040c0e107081001c001b070040c2c00548499141400c1d90303e60304480d41c0020406003031503407182000401600e4034032a10010880c1107014540754424000720f000d00201110040580d84417100040c004188500100350445040040e84d554a80c0795030100c2e0003074000c1c031104101ca49000300820060101007000940e200e4030039015030301600d1180e400c00003d20000d036141d100707 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 32585212 1250 32583962 32583983
    0x60405060306040b0709080601060804061d030d090201020106050d0b01031a0c090409110904060c090f030c090513060203040501050a0608010c1d0604080703060c08012405030705090d0506060108090a 87
    0x89411624515005074071846e03c0c0c10300355217801d00380340790403400c0c0e02c00c00008800c0403c20003800041d11410550140c02407081d11649140d00381582d41e4043c4c4130b8080201551002880c046a00035440440180801380640003014500d084c00014075200340f0040d62201d030220521040348004c44041403142c0403c0382014105540d610520001b0300130018121084d070881203807403003d96141e9041c0b51007203205401c007103560348440c5402000c0460b6644982c0b0b002680c50814400201d080e90303075000751658090001280d96816801400040203080301900e818400001e01c1309201040d0840b40c480d042d9060140560b9035200121404c07a2640200100022880300c0305450341003000040c1b114019004003110b05140d240c00e0581e00700802540101c0304959545601044103411402480c01403841c0c1a03c0396250036015541c0e81c000070344010032001c0020000000d05524015000e680c107608002d050b4542e005c0c0e0342e29000e41c0e180e40c1942c07164046140c035000030341c0c1d8200024501c0c03121913000590702c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 32586462 1250 32585212 32585221
    0xc02060403080a020306062506060f06020606060c011503050a03020c0f0612060f0301140f070e150903030f0f07050c0a0f030212100903090f05090f0f04030e04050a0c0305060405060306 81
    0x4000c3d04080c20302a4000d00030082090390390451702c0c0000a80490f4059248c0c43c90003450617031704452040c0d002e0340a80213404020044a41c0200c3d90b140d02201c1598029542d2003400300d654014421034007503491281c800003011041c01000900014064802e40071109049602c008225040340c42c1010036901000800180a5200c500d2441c0c0d90000009132282106c804004c000074259550384505204112100c41004074500a02040715000583d43c1000d01c41c00c4070f40404a5540a40410705a5198100265038041914204225032090003e140320640b1203002d02c81c011990351001201359258811400340c0c0010745481c01d0030108841c3ca40a80411f142d05e550b0130700c40340040b41c8241041ea07010354036583e90547c90b00e010f44244188290307186c540a07414908490500b104a40007a40940d940101b00a0074490501120380c000c1c440802e2038515558500d4101c032118100c00245030028180300604c010300c403c1d07410644444045440034041c7d82c1c1c5920070303c030880d14210341c0c107a89a0310100206 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 32587712 1250 32586462 32586481
    0xd081b030a09020f030706050d0f020406050306010809070b0a200705060406030c26040201110105041505060d0c03060b040b1206130f0506010b040510030b15031314060402040c0206040308 82
    0x195480340f010b030945940040307060019003001e41c0f03644003101045002518955001480c46a01080c000c0c0120031420a07003401e50007811800000c002d6810b0010420205121440400005005110186082c0d540c0c10350b08400405170349581c0102e801d1508000c20060a03290007240000555001a18a41c145440d0a1007103001d484000b0480080c00420080203a440d00e000ba45016503245d5104075504500300751000400c0c2d110385200a1441d079240406003c00500300c100e620031072482c0180c0204a944450000075941022908001d0001e1013031500001088025001020104411101001101d00d43c1c414006c01240310325410b52140c210b44001001e08240e8071040074a10b004034006c44907010700e503460a1074864207800003410032030082410001c0c1d141880d05000380165610f814420b1039010004a4201803c003003001d0354a000110004034041400000c074030000ba0451194482c403284454607503103684042d6010780c043c81c14410741c1c1f18100d00000d891401b07a58103a551208540d141e2111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 32588962 1250 32587712 32587721
    0x3090509090c01050a030e0304030503070c050907080406020d02040b0a03050a0c02030a1e0c020607080301050a0501050711040e0f0106060e03060f010609060503070201020d11120f1009020309100e0d081b030a 91
    0x621041c947d03900043c4444003800c02c05000950b00c240c0046d076072080a814865120070302907218a100d41c07040c108000d003180d800003045402a40c403c0000d62200302c0c0102c204064000c41e080003210210200d8085007256260b0812030140d06100c1c801c10800c4034190040340c0300d2142540350800301e10b0300c44141d010b0100c0100e9010000003686004a10340d900c0780e0000704c40e6404400e042e140008040014441d500c1c0500041c402400c0c240ac04510f0318000c0d0342c031880b8800b41041050300c1035030f40e902c21009130710b82032102c7c05c0092010130003040610344840707020781a603c085400034001d20171600001c9041d5502000c840c1038070415162a806545040e8040f5010b41c0020442800c65409200340035490329240034484a0414029480e6140c81000ca068454003200605440210341d0400510201c084048030303520644410401c050394a648168400e49070030742285018524a00e0642542c01c41640824605282d1040c2d54035440300743c481000c20305950740704850304144031500300080352a41180790321 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 32590212 1250 32588962 32588977
    0x807020a03080a15080303090f0c0114070c03170a03140403080112150501060815180a0f020913020909070302040501080105011101090b0c1809010f060c05030c06040302010903090509090c0105 84
    0x2404103000e134554100c0f401c00307000d0794882032059002005218060005100c5112030b00c0c0310301d0080c48001502c10000380f45149000d000c5901d02c10000e407140c01d00c20301000e140e0186800614807400b03040c9910046400f035028041c42c40000c0c2c42c1038961945900780290140c041d51301542d840d122a42400c1500110f80110402110307a518100085080010b583c041c0030b001300032540312000e85281003513022595484070100340748640341e40c0342031030408800004429081942507200080000b040703084c000007882003661584d4403404100890850000301d03001414501c600352500c0318280c0340e000c07080d010b0b401a80211b50101d421500103000c9548610f1403224808080d00002c2000904c98460213549a4240d86550160000080c42c0305c205c0c29011368074200703d40c195140f56080d0702d07084651407680c1e003d000300020011004011400e001e4100b040e200a89040010341d8082d00b042c0c980a802000c040508401103400d5500000f03030703494040d4849115205070f0b0050944480c905004644903400f880 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 32591462 1250 32590212 32590231
    0x308030c07150203010f06020a0c0b0a230403021c0506040f1509030206010311012d0302040f0e040b06040b1f260402180714070602090d1a01060807020a0308 69
    0x10300408600b500d541c25600d00c1e0345000041e83c9504018204c03111001e240c0150065500200c2e180000541e1851a40121980114500d0700e0b180b031110100c0c3c0d56034090a0300326803211010040800c00c0203000003841103e1086502d03140818200180b10044000300c100034000d60000c0000401054061160212083c41810039401d100050b910220440d98001300c19001030b0720020041c01040148082515064002d0804600404441c40c1094400345010028090b0703401c0314001841d01070194060310090038000d006072502c1d030744510202030613600466040e83c6c0504060007040c1903080920a008041001410b03512085114044002c44010043d0f80030007048504642028000c8540c00001207075280c3e183ca041e624207082c010000442110b455496171b0000b001c06005001c0d03044800420740013a0682655181c0c80141081c0b00240641e0340b1194200000c240c200f41008a0346103030401c1503554040c00b00540c1d80300d20b0308440210046070800003682c0a079000c0300109000350000e590048115 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 32592712 1250 32591462 32591467
    0x403030b09040b07030501090b0307092003040515150a0915050307060c05060906100e041505010609030201170408090f12070602010b03190b0402090903220504240308030c 75
    0x200003080000c00c1c202d8095507071149107018070240d954940210f50040100d040144144402500000e48445880c0b0a4041842d600c40c1c401c1d424500420342031251500c24143c0f50f480e49441e04003681c446440c41230320b50a8510b0500090078013a4100d900b500e0305000039001d1040c10741072041480c01008000080c0303a05500c400800192507400304103c0f80500300680d40c6030b0b008007281c580306141c034002600300c42041d0000801c1040501c0148402d10445480b001c0c000455222400c00c8000f00b0500ca0704114207130b04200011400c56040000f801c11240f003a43d1f46080070103890540714480300103480042ca502800c00042d4014907001c032075001c20450080262501c6904000401c2c5496605d07444030000d85d44038148400d0901d0180b10f01c01072594503d82e445a1410039556151444400801c001d01c11140b9101141c2c1100b0200107403850f00341001d40d04038009180e8140ca4a601190748039035072060f4200b4542140104d0103c111920924171810781d520400e0130360740c40e41e5403504000d108540d080c1c007d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 32593962 1250 32592712 32592731
    0xc05010e0c1509060306010e01110102040e1602031e0904020c01090c05010912030906030c0c0203060f0405010c0201060506030c0a0c080d060504050109061202010c1103030d0212130f0b040303 84
    0x203128540340140ca4000411031100e10340309019201c01e50b51141542148107001c0c0c8440ca44910381140c3d441002443d02d0031241c0300c2c103801030300c000c00030b045100070f15840881c000c1502145e03c1080ca0040d0070386500c0c01181280d440c422a902e01c01e01c50310031034811030201c0900302a0245006401000401000036050400059499084039880c039001e8034514040c940401c2075581082d0342c0d002500b40c94804842c81501c82c2c130003070145400752290070700f0556908101511340e0312030300307903900b42c103600406642c014140075040142850040d18240c3da1940791015603184a401445210300310b9001a1440341159150007400d10190451180d04050001a880d6500000d5518000b0414001c01250000c0c44e1030802c01480100d85058101c1e08140e0314041d01806203900d0504040c491583c24030307080c030745500145490138800d0700005600d5090710021038901e461103e50b801500d0890b400d00f04051032541c80f00210041c03900c1600000e0013820003411003101207880d6081d8141d00502a05001c03c01c2075a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 32595212 1250 32593962 32593973
    0x201020f0d02060f060301060501050a08070e0d05060703111611060c06070203030a0f0504150e0c04020a030903020c04060501090e0907080304090603030f0c2103060b0c01050412080c04090c0c 84
    0x44541c40080103070829020442c008128a410907004042603000708082414200042c1a5201e49030102c01400000c41c0043c0c56a031186880000b150009004040d240090b49090b641c1c40100303a60780b42c046800e001500039441c0e81103040d109a03610480c2040240b24031910303141c498183c8a03031020380020b0300304613040d041c840801600d1f000307518a9005558a01d8807040700d104490800e400303100d41c542070800344800302d40309000f403a08813208030700002007480c1d101c1c4001e0b150002c075a170b442d40c100c1d00114044441c1c5800d9801580028084d40954800421160800046500768003415010982d490414002ea04440f841241d02030080f42c1240d0b4007503154003045240d5085540404a019200c2805004041d4042c08034a03040c061410701222004044d52500b03840c03c2d025400e016201c000c11003036002d2034440d40201006180f000141951004a15112800303444100d50681c2e598041c0d090a260051180042d0744c42860380c1030302c0d41d06060400302240082c201c01c1400c101000398010300354bc007280c0e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 32596462 1250 32595212 32595223
    0xf0b040e0609060106031e05060418030201050709090615200106030804031703060901031401020906030406060305060f09030702090402120d0c030801140109030f050316050a02010e060319090201020f 87
    0x1110020041490300b0444249840d105802281c209410808180c40556103610b00e0980003c40070000703e42551103002241c000c01c0c0809a01d20392451001c0c1803400c1c540c0643c0018011042a075a298002e6220003242c0151134a0b0f1007035001c101d4400c941314905602c00c041c02c2000c0c4a9900e113003980d51a000c1c51282c250344590300103032040807002404100b005501411007031008a0450704a046150401c00603800d81014880070703181c201a0101c4035108003003076048802c0c0f10002070040d600c80c2042c0c00e08000504541c00112a24451140030680ca8081485064030450381c0c040110b00c1d00d02e10b070382406070400c40a40101d800c460a41c0748644006401d01510b800c42d03085564407101c58003903080060446c0811380c0102071140c0c41465008841e42d0105d400c40950790002114036451200f4540700789544105040c200c0140100400c1c0c40400c6408506c0c084024000d030303640e0300a4a005410405548016200003900454000d00c80602e00703165040160303100d005005450a040713183c1000350418 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 32597712 1250 32596462 32596481
    0xf0f0307020303010e0609040308040f060609110408070f030506150a05060a0503070906080601020307080318060c040f0e0c04330f0809030a2109020411040e0a0504150f0b04 76
    0x182c101000510100400c07100b816407142c0201e407090381900b840d8034068542440984003134003000408980105001890f00035800800100340d0402c0403440e5400380b601c858105018026442c0a10744000403d100c4d01800807007a81c0d041006480e080d00e40007440c4800e0710b0110500d91700100c0c01d0301c000456960341c0c005001e05403d141c07600c2e5030320719090800810405080d00203000f070100d03030010301c1300c0c50341e000054900c1c040d400f829040d42d98aa595055841011090b032442241c400c08041150510001000c0e01c1128451501c2800d0b543e111035415001200440f5175040400091101b0800d5847c05560a510503122041c80440099021a00c0c0300f50001c070f08d2031a01042c001c400c0036000c50351000c0b030300e58031040d11000340d810104c1c0184003d02214080c60316045c40140e07241440942c0c04030750300c0182e03003941c02171080000030b900d259100b070641c1007803144105030565a4000740c10041e241c0141881a580610041c01d0f01c44c03c3c00d03842c0d00600c3d4001075410441d0792203941d40740546441c800c40900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 32598962 1250 32597712 32597717
    0x513090906060608060a03170706020903060c04170715030c03021306080115110c0609120601090f0b01020c0f090c1209010509071505190c0602071209140904080f0f0307 74
    0x494280301c0064000718000e80030786d002c2c4850403002c20204c2c41c0c1110b400c0c60080300a000c030381d4540780350910001a010311a000d5070706000380420322900e010504d00400440d004100b0408401001e8009540c40d01031a1084000171005182c50010180c4a0b6010b0b07588000a07060060a203664000c05e548802c0407500b0003008191300c0300050040343c1e40121340e03503940701c2c2c0c0d464010b8100c864903034120340707800304034840501802d4045110b110b213984028071480442d100307500b125519a9a1800d1802410360003083c032000364a00241c601d40c03544049805c903208100641f00103d50034040060050501d4000c00102c007150381070146513201746441d0510b501070401080040b580341000039030305042c40780960024502c0c28078240c040840581042c2511004c5449601a014a084441d800e4450102d4a40000c1000b4800161507003000300885001d4100e101940d45c950809444618400081c400424101d41c170099440000d4008bc92140044c03c8401030789644078180507494032000e04540080d20144003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 32600212 1250 32598962 32598971
    0xe010e01050438070c09020c0114071814010804030c05031b03070b01050406031e081216031a0109030b101d01030b0c0909040206030a0e0303010f1403010c0509010513090906 76
    0x340300580540f140c103048041c2034101e1400c0483e42c1d5003100d000d400d00c101c0002c0c030340100300c0869074a82940800744501d0081d1044141d0715102c08001c2c81d0420b924440d0388401d034154000710300460141561403058006031900b428a4541b51010780e46c4000602c002c46503171008002c222013403800c4030b000306421141c40d4015900c40304a443c00e08194041604118092880d01780200003042950310500039044507011650b0810b031080c14003d54a12410391414120700c2c1c3d020900461f49150300c40090350202541d010040f200c080d01c00c9081e0762402c0409540058100241400407518115040c1d8200c3c1640d140691101c0d99440b1a82c040407082c4c0525590580a40041062120440d00180d0211043d10040e1610404000052280707101070320103400ba07900807001503941c040c143d1000b04c035809a002100d03100d4ac1d540c0c4070765013120954007458903031650390f58500e08141014002c118a024840c3c958608040500d40110350582068800d4a02e0416001d400613900041c0e02c6205d01da103018000102d17 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 32601462 1250 32600212 32600279
    0x50d020c090a050f0415020c01050106090302180405030d021605100c080901050403020a111306170106090212010905040201140d02031b0909010504020a1103031302010318030e010e010504 82
    0x14100320002d01c4015400d0a03d010000005992103c0301d51103640034042c00390076172400e10810020301031600405001d61804002040b002d03085080001100c7c42101d1040b15807014002990341d50805540050150780188900511105240c01400c1018601c00701800518640e403519843c041c1c2c902014420b4070f554502d20500160b114440c1548008441c0081c052810329a5000f541c51003095000350115104555041d144c0e96080003040343d44408000500c902e984448229201d07040400d04003042e9803801e0400140301300ca500a850111085031a82c1241da0310b02610b0001510000b43b040341040100d600084030240030340050006184206001605da240090f0010000d000c0c001450110110a00081c4603d583c1c130104281552026200580c035100a5a000e0f01d003003c10012181da207000101c05c00902750415420358007a24001d036818000410030000240e0100c0e410000500040c29100454286502401d20043c104c103061421074030382651154440058100030300c00701c291500701c110300c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 32602712 1250 32601462 32601469
    0x3070e0405070608010308090105030a020d0e0d030b0a050d0209060d0f0308010602190807060c0e03030c03070204141303050702010e040c020109110907090e060301060e0702160807050625050d020c 86
    0xa8006800c00101315411038645101e18001c581d40035041100000008016079601d806440d08290080d00520070060400580750700c54601d51003141c002450084010803a240242c0b81000b01c44015005080260035902448a10721008200c2e40e0005c2030000c0b0000000c4400e0001001c0a010340e451589950420100900307001c0c401001c140202181905403002c174903084111107515030b00100c00904010302a100f505d10320048850300d40e00d40030100b04051034420200c01024824800c46042040c40c464440c440c0b102001911404c0134144454014000a40643e000340740c01030050400100c1c0c0f48207c4000f400707070340e030604813940141d4452020800304143c50080700d6060104445108030f52a11740002403900c01c09100d103211054111010510b50344007944098080c024a40c2804d03064981224040e503181d422003200c180a03481e55000040000e000300c1c48070b0a54200404940c40c002d034004c6814245101500e06a2401c40c6410100d00040c41c10814110340612039009403242c9021300040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 32603962 1250 32602712 32602723
    0x1b0307080c16060e060904060803040b041e06090501110a0206031003110d2a050d0309050102211215090a0f0c02010b10142203021f20030903070e0405 66
    0x5540b501c88076818800c26800000c203c0d0304007020340f90b49482e200c00070001170150005500c92003507800002000709a448000005005943d5003646809002c902c0c920044440c884610803900010441305003840958801c40a80e80b25002410840d81400c68940008131079034010b50700b00c00d540b402ca40e01081004180020144482000c4460b00d0307214442d600e030a01921602c038000c010041d000c1c114581c280c080b00c0b0740f0001034074000e00400380940c414600644800c800340115800f51040180381c07104a48100c403a035281e2161440c00d50f06210415544544010002c2c11a50302c2100904d14090079840703002c0441d110300b02010740824800161003001c802c17100304210075421641004440103268441c010240c0007103a46140100c4010050700399081d0034001c4c0d45562050405180c041c40342091081041010b41c1d008030303510b140807911005018083c121400241002c00c80f4600065200b6201c030f154403404c02e00810607a0714120074000087c0c2807003215080020b400c80440144002d001c2e08028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 32605212 1250 32603962 32603983
    0x207060b0105090d0b06120a0807020906150706020a0e06071109150321310b03040308130204060503030705062a0d050712050108030702031c050409021b0307080c 71
    0x1c005280802500c045200f40544a04c040c204e03411220100d002521001d6407a0980c0e029130003a21010a00351810421503071120348141d00c20301c020000f050b01c07840c0090074040100381040c00d4500d08042642c0d403a0107074000c00301440910600e1558a2443d4807444010041c2c03a110b07105410012049004100003010003038034880038502e0b0000043c0f0913480026a0803449450803007208409103a00d00c020f50300d4440c02918924100300c00424807400703040f800c4051000507008483e0100d8980b54041c0740810300007200c0284c001040140452180c6402c8080001d16600180022030069182c401003807850703102c03d1382212194820410080322605004040e2140e614004140c802c083c09241a1039280c003640740034503030071a50703880400c600c180152104440c254050b8418400b03580d4603d402500ca4000304800d0340680500f1240914102c030b1004048000c608980312181058144101d910094011000800408022404007131080d08200050444580301d0b07002c1f10b07510705e507101126040c003540f45c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 32606462 1250 32605212 32605217
    0x20904050f0f010c0903020d050307020d08040e07080606090108100816060e060a1403070c15020306010206130c0b0703020f15010314010c050d0515041d0c010206041a0c0409020d0207060b01 83
    0x1499044c4140d4000b5060f0121794044480c0340d648525070a206055110342d0200a6011451380301620812007410301600480c0c031103002902c0c455031b40c50401d40d94044100c07840ba0744400108a901d08a60003950802e402943e480e03450180691506040da140408480102c01f6800070624200640c035031204a524503004240c4502d420315215150251102c0e080300a92505140702100152850344901ca82e0800f00c1c0d04204072004d4547c0c050003900c02540255040c0f4018042c1b0400212000f0200d94031a201c0c9a0100e2000703080d500e00980c64000e40c004841c100c0441c000c000c02100400c1040104c3c070f01c156840785101c9495455490007004c10400c0703013103074035059051100c0740340a07c0d000b00c00d684094540140101d0a0764580c05101079a05540303420342c0d8400e1500115900c48803840d041d91f41c45681c000c0440f90f07149481e0006981c1d505007141c00505290303800760940a80402011642c1c0c210f80c00a00c482cac10551120b0081d410303604505040c2c1e0b4403070343c00305010301440014003034450004001e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 32607712 1250 32606462 32606471
    0x10c09050f0a050604090c230403060c050702100813020d0605071106040804150306030203030c01060e010f03080304060c0c021e0102010501090e06041101020316060207060c0305010510030e0a020904050f0f01 91
    0x7030100300580900e01c1b070904000e60700c5020380728143c01020020448407607441e458008004440510310190040c0c0405d0301c07035910302030a04400900540803200e180d50000c00f00e80d21041820702c1150714070740080c1400341c45d480e1041c40c1d40061f103800c101d13481e100b48610000700391072400789030040c5440c0c0013010f0b00d44181c0c031000a12010459041c00c4a003510484141086001400441070707010704460380c002501880002078264811a040d4059030554201c1100541c0b546d9940c13031500d44010103800007502c0e0100c1000850300084280d40300ca1514805410501c042450035000a02c00722540d8071040c1c079001500d0083c48456038203200341d60162004000800910481c1d2800c1c40d510200280300800000d950700403900c407a8002c005889103851440480d000c8450f043c60541c0280d000f4a104491240c1000300d0344d000300d030281c003919058560141a2411007400d14404030302030140031070320914900980a100c000350b110261843c0c4143c0c01a40203003038654480800c03d01d0000040040b01842e40b40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 32608962 1250 32607712 32607719
    0x1206010e13020a1a0f040305010e011b0504090f060f06020d1707080105011b08041202040605040c02030909040c0e010e0603060708040209131a010303020f190309090906020903010c09050f0a 83
    0x1c900300e4006403604c0101c04d4a445801000d5408a80304040d0f88090480c008900001040b0054000001880400009024000e0b8415040603074800f407030380701c401180342408180407444042d0311603840c5940340c200224603683e5600d1690324450b1281c2040005801c11840301210a030000011407200c5d80607550307800383d032500d01801010b090043c05543d04120203014011480090f007041e820089820010b03495417180d884c0f030040030f0811110006ca0082e400d0400010300c9150901ca00d10142042c0d8001d1480c0022030000c00000351b4004000b1a400c6050a00110b11055030040c00da020304945415036007142845010180b810350003c0000341003110800801005844913450950480c407401c180d0102c800d4a45443c1a0060160b03800064485054000000307240c0e0003d0b04002841c130480c192a0211445030200162510440001d404108044070421640c040350341b140341454020030005040001180c0000e080da0700600308c0000060100c44203128070302d800603c41d0301440b400c40300300100518 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 32610212 1250 32608962 32608969
    0x3020d2913030302090301020c060f0105010908030c0c1009090c05130b0711010e01030f2a020d080105130f0f06080c06070201140307020f0a0b01030308010e01060c110f1206010e1302 80
    0x881e01d4001c0415401003001403a60314250103031889084000d047c3c0e403c62030011018a21031009101302400a0742d01c9000181c1500d0200c1166041c005210261034514615420b0143c0316034500c0c951810030902c8800000c22104610030382e03003400f04031340e83d20b5603a0146041808181c0c4898201d00342032041005100c00151280303515040080003800c0c035401440c800b2005070001c11014144004150404151000825060703824458070012000c1c0001c01281c08042240d44002541c00f0304003141c01c07070005201900d05a841054542c0b070500000c203030044402c81120544100190b000100303a1141c0050000600901a103640c0d21019580360f82406156000244a2b1000c1c020f490000e0600102041c0c1c0c0c00c1c82400b03030301c441d014142d003100d14a0800345032241088000b440281c0024241400105000c075004a819041303803465034501051000a499561042c0c0c3c0380c103002d6a01440382c03558105103032210101d14138009140009442c25601d0586101a140c0006002810071016400220f00595 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 32611462 1250 32610212 32610241
    0xb0f04060b16030915030b030d090e181219020c2709010605040203010b03040308090106030308010501050c0f0607021005010f0b0417010603050303040f060c02070302060a0f050403020d29 82
    0x8a00303054141850002e03040c292081065500800c0940c0c20b080354103c1c405800d6007114005900607001c50b2000c1800b400100d600e00c0a41c05903038a41000385000c140800078840c042035515841200b605c035007000301d18100003141d1161203d0904c182410020165442d0103000c0041c41c00d00039141410380040040840e503040e41e42680300034100c80c125010600240b42581b20b5409464041c0003150b582d6103480107980f003a0412241103000a204000080c0a402c06004800c11a43e00d5143c0d41110b034241001518075812407000c45d10031b03104090700040540303003c100c0c160003160681c02400e01d00e8080d011000c16200140c2014a5103130f2410003c12420130020300b02c404607a40d200301d06003000d000e010f40038098422540301420511000c4248000e0005010119841c1c601c22207041143c0000031001760f807140c00c0c510000e50711007810310540b0f10306409401d140103503494501c1d0840c686501ea41c00a4912103020b0021341e002413403010ac0c511080c1744001907040002c81c103410000f039850600050344800c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 32612712 1250 32611462 32611477
    0x50301120c0e040303092d08070f0b18010c020106080c0103020f04030501050a15050102060412030f060302031515150d09020a0306021c0501060c02010207050f030c030604060b0f04060b 81
    0x82003500c100c828421805207a0700034010715420300700c203401c184c1030050241a400d82c080c3c80c43c1c45060b50b00c1c80c40c4940d186914050402d403a14219009416840780412a0072034241562413040c2c1d90701c1c000c00982459085403060040000c1c2c4615003208920550849000c0c400b5001903a240160a2103024400900200061400d280c0980d030351041240000c000d006d103510040c225800c0a00f0b021101c0583d400c8000c8484140e0640c005441e40d58004a0351a0300c1510b014120b8101000c0541881e442a005145000c403880300200d021550b990100b8501000c202c3c1c5006040810f400b4808004961040d6005120048403100c896840c18200102c1510846c800710040e00d55818448046441d0024042c0007141c01c400d045495111241444115140c010107030381a00d49401c0001c104507005280744042642c040e4010450745091006005d9403060000d0460350501c500c0701f142000d90b401b001084e01c150310880c00460307400e108105214a20b6000c411007842242000014003154083c101641d400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 32613962 1250 32612712 32612729
    0x702011a0415140d050d02010204030201030c0806010c0b1b07150c08040302030409091113140108030a090504050402040605031603031704030f0e0d120905031b0d0f03051c0c020f010c050301 83
    0x200c43d0321900041c030b4180c60080003881401782d0782c0c02004058065003c2c2003103a0007030f28180302c0b001004a0440f02d01a049481c9804202800e40c00800b00b229801700590011301100c60803507100c00c030541b801d03041c0c000c1c18007241c0700d8a202c449144040c1e5140030b0140c040c00d01e4204091581404d035006500ca0140e40540700c1419507681300c8005004031145401a104070140040c9582c4542a28800c09005184500550b101d001e200004409400000f20382900e4a00d40c1c84100d070034142420040504005081039901c43c0c0c6071400855241d5091010300745144026640c5140c00c1c6c6103207009045040d02e075800401c0c0000c41000c110100350014040b1a400c1c030941b405040e00c07143c40000403003010006501520007036192042a00c80c980040c07205090303410440855098090340c60f105640301d8141f080403a040640761030b040c3c00041d05c0501c0010f149110b81841e03030409105c205138003500c0c650300010000c4151511030308520940c0505c461078001044100038811281c1c83c8402402900c0b062040012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 32615212 1250 32613962 32613989
    0x103020607021215150108090c06030c07020604030614180a0503030c0c01180311010f05090a020907051b070303080702060f070e030f0708010203070201050601020321070e06030702011a0415 83
    0x4541d50034066013901959200200104d410422991608428030141480c0415400c0c004210f01100c00181116403450081489265598804e0505800e420009040381c02c0079040c8800700010384280149400c0d103031681505843c51071b00c0c81d11145080602003030100d00c1d4100b980303444041040801280d9105a02d03500302c82d9508a858803d6006003411070214440041c801007203802c06501c18102210a82c80e03000a110000c585000b01701201d401f5070f500000355000540c100300502b031540f00c4a90000c918102242070070308401c09581d55007010130f03010031a60000e180610405800041c001c0d0015403502c010001403030603100c070715980c041c054040d009101300c0003041d003038665040003c04880100342c000c1c0d9008641ea940058040c0d0010b4030000e01550910380001c00551001050701d14900c00340d142c252080b5450001c20b007030000042c0401040050796000e0701083d40350900214060a056800040e52100d05c01d8440d0090000710031252160f82004135080840e00310042043c159100900c41d80c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 32616462 1250 32615212 32615239
    0x150b01031b090905280b01020f013b2e06030201120e0316050303040507060c05070315060f06020a110108280f060e010f0b04060807050a02160f061403010302060702 72
    0x110011110307038581004a07805c80c11168200c000740c00202c01c0d50350030f80032541c400e2044107946003610b0080440c6817400300d08c0c00d1004481c203141003403030701d100345c03501404090040c0254030f20f42850f500c948160414a6080c1c5441225043e0511411a0514440c400c04c6034500f103030300003003250085481d424501611822105a86a401d004403a020300a1000c6d040003c0314070301c0c0c010780b280c1080780c0568250007070040001e5024000d060541c000c43e0b00c40c000c1d010b4a415035940303100c1d11030101e4003d58410b6a52402080c8516190b114402420381ca1300240100080ae1510450101190403c1d90401c103079401030041082d031032000030301c189138030744007192801000d00d01140082c0009540c03540ba0703505201002840814030600d41c0e0503106404600710900b521000c40c010720707210700e00c0360300e001135220340001e43c0042c0719101070b000302412032040e04d035495400100c100952400d40c11100324992503000400015401c000c2494040e42c006149605540c9181c0004079140a02040a4040c010104480 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 32617712 1250 32616462 32616481
    0xb0112020307200307081b070f0f09050601020106180c021609092a09090807020a060905030c030a1e0305120a0903080603030c0703020f040207150b01031b090905 71
    0x5508111050004545a14020303900611080c107582116111a0400c0c40100c211480482210341ca143c220106178a0140000510464401140200e060300d0040d07079008110282083d41d200c000700044410440940d0800107004111000582102e040d680f4111042200c900b040ea0f01c00c000da14244000610026070040c241d0a04440120340c1c0040342041d035010030042c01390b91043c83c90383c0c09061030030f600212961117001c820320f400d14054007010f8a0002040255010b400c0401d1440c4190303d014100011540404c4484489404c80008104040000e00c1b481c242000b4446401c00c088004165800054075a030028107030f50b403008038100000d0100601414024001c40d11038510441001042c1d10b48070b00c07424028102d880f811400120f980e0b01140c860314000003560b4a255505002d44202440c541c2001113825514502a400c01e400380007003804901ca03105501c2746404082c00200d041090000014212009000c100c214040c94940310130440b031303005101109035200040c0c0082c40351a0360000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 32618962 1250 32617712 32617727
    0x3100510090207050106291801031803110f0321060402090a060305010305010b010503010806130510021b0601050603010b0a030207020105041802070201110102041401120902040e06041a0c03010302040b01 89
    0x210600702e00010b0b4480400205602c03407400c68000b500d0130f003404010260402d08240321150b400c1b24501c414812106168182c1e003001e102c0d405e0506000500c50780082c2ca084019105020039001728040da551000420414455120302ca11050701842c9089036041d420031616003204048822480c2c440009802529194100c40301c0580c000c5c444007a45a5410000700a0a03090000b101c00d5401c200ba0281d15501800a03203050701c548901800b5a0750300c8004190107200d9104c030550b441c4c4035000d8107580100d52803000700b00c1c01d9400d2440029111100e030031135241600684c021070184904000400005000105075060340341c5910740980c0c0c4c0c00300c03400121018002c903001081d18000c100711180142126900418a03a0300c01c1e02c404030b071020340010780d5080307014038070a801c4180707504483d81c3c105610490721071207142c2d1404800102e04c006900414100c0b01d81ca00502e44030340c40031040c0000c0c04060301c03c200e03200d416864103c0881c80d203c002158140411712009001b140c42e40005036090780103010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 32620212 1250 32618962 32618969
    0x30603010b0d05061009060b0f0702040b130603110603040506061c0c0906090e010b0108070c020409120e090901020901020c060a20010b0a08010e07060e03030f0a0203030f070c0203100510 82
    0x80c036070b1008107050044d12407000380c2d44104445011040000c4800d1070380681001c607100002074504100300082c1101c501da000d03a10403039029036922665610369031540021f401e500c0c2c03640c0000418a04500c0c042d00b15810b03055036103100d40030510820002880000b05654060030030b03078080c00c0b0802c40c240c04001890030b0200090000000850104650364180d00c20780c1201d41c40c01c000d00c80c03990000e490900300c640b00c04900340095486400194098000d5030010032942c030180001840d10f00c182c44079404080485211400602d0921a80341310740340a00364160880301c158001c510700003e940002c1d40e07804c50700c0c807035500540303001c0361092959000f03000040c120104011410710410074944500e0081c140b049900cbd100d0f25100700003113003c2c04144240e04a00c0341d440001d0547e5400c2280941c0d583d14255036040e070610040110302268880c1ca0081d00d914012900115100e05015015080251000346071108101041480002590300001c0c2c48441c6a0016000035887d103403040300c035205003d59003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 32621462 1250 32620212 32620219
    0xc090f010210020c010c0e010503070c030305060102030d0212040507270b0d061b020609160909051204060206010e0a050402100c060e010606050304050115050102030a030b0136151202030603010b 85
    0xb5600c8131464045d00300203180e604983d0303620030030426500152198013080c1d400e14000781200700b002001a00a0b404940c020030140122414448107200c0f6000740d0f03003c5203941306003200308002e101c05c0001c20001c91020b0240c50314921030401d02182c1e200d9488000100e40d2901e983c8611107000c050b150100c980b0f650b150003000c1030105141401815018000003012100144940c100003181c1000216031044840e210403925600700d4680b102d010050314440c041621640218910f500814030381d00000c10082c1402e80150000b50301d081400848900000d04101a1a003031808000c016039541250385005402d80c14800c11008950411100500e031001e8460714a42c80c154004c5140d0350444003075131045204000a0002005034404440700c0a4a80b05260150f842031015684080c0207800002000d1010b144c070b441c10a122098410301d008404600d140c1704059180721401942d0f1030050000a000d145840303000c00410307030200400d1081d1400724040003943c0031001c00c0743e681d001c0d00034002104004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 32622712 1250 32621462 32621467
    0x308040f0f0605060a050609131104080a0c0602010e03090906010c060f020307170606070507051309170309100e07121406161b080a121401080d0f080c090f01021002 72
    0x1850824010030099401342e200302c1000100080134a44102105d8510390060001e540040440d80d43d68064100c92800c0c281d040002d000c00702c1c0c0010200554015103000d0545c1102d0a07180c280040d003101c40d02c100382019504100b00004964031540708094001e00300b03192000c0400590304143c0f0050042041d000c01c0b007400041400748142d40608078070101085003551a1864842004101207481015401410343e0000c080401c60791a01c0291141c12241207180800d16008030768592022101501100c0c55440002c014810486001c2241c903c03420b62129041200c060305075000e6966060a20410400300343c6e0b80040b80c10841c00d11081426200c0c07000c22155141040b4030b040d81c03509001c0d81050300162203400c45607001d55000c00f40982558028100d98580075006004031810207030a9203030009143c482e040e1003520103c0300c05a03070003080e584010b0300001c0510900105240c02e1141d41004020b0b090090004a1014800325900680200e503500a1203041c000140d0520300d00f600c0820a09101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 32623962 1250 32622712 32622743
    0x170603011d0705011805180c0f0304030c031e08060f010c06060b030711030412020108042306010e0702210706060b0301060905030105010512030304060b0a1203030218011103070308040f 81
    0x150740d000d80fa0242c072402e04d0380100c52540c0301c40322a40d100e02903110203610030318041d241490100c5904440c4180d00d0900d4900b12489050041d0300542d001c600103080d000744401410b600c07005a25a5402c03244400e804600c9440c001400007001402e21441100300c1c1c01030740300e241e0189016964440d40502d00b80412a910184803813550000c03601400482c4a4143c2c5000040021007203c040d141820000360008003da0011540008020021a0954202c0c1785040d40d081c2c414601c0c10040031400c00512039581440c1c2074402540c4083c02200039507101168140511800e03000300c00d13400c1c0e0820307011034a900c0340c0d040040207003502e940903d41d0098000000305e962503007c441c40c41510703c15002407000f03036070350400d00601400010b000b602e1038000b400414000341e020303008114400d5006200e003207040c0d2248032400c10810152800c50110364002407417901410404528444e892007401c10317003690202d00c0c1c43c040d00c07845a10401001c21000400040400401124548600741c0101c0108110740c0c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 32625212 1250 32623962 32624021
    0xa1403061f0810061509061d060f0c010203040302010f021911071d0703060806040b070c1a0a02131a04030b0a0225020906040b0a0b09012c120703020117060301 70
    0x4c16008441580c1001c403440b080b040d009510b184100c505503600c07994003000403c4a10b10346d2140142c041c0d8090810000040b80c00f0022000c0c1010411840006035a401c15180c0a0700311458030700f000907124018040300030545250001c0900c42102420700c0380040c20400100c9081000d19046640c0f10340070405140c80c2018084610707403082000307441c1042002d0300c0e050895030b035100072903006080308a8440000c540c00d12a49440b03111a10604d078441d81d08982108183c1001001ca409400095000c0b038040707100901c11036850002e00c1c012500d46481d520394001600c8a2249000c081d0000d00e1440220b1580342455044440807174498020740d20100404a1f507503011070b514202030f13105614180c0850070074909443359410329140242034001c0c4510306407909035590040c007405414003000030442d41c5860303022950701480007401900440028240000c11182042d40302050020354801c410920050b6086603000384022400c00c0c002845554902c00280034004c18480f41c101603c60502d403034460413 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 32626462 1250 32625212 32625221
    0x105010306051e010305120a030905010f051f08060402060318011103010f0602010b0a0303110f060c070204060608010303020303040204050406060305150103030306050105070c050603070e0d0803060a1403061f0810 93
    0x442a2505609415040751500600f000e0001401d140c210b600c200e00c840c0001ca004090800301c504003c40c241580b92206821204c86600e580003050f11041000180b503000c443c000d81040d011000c0e8403250307041c211440c1e40d409008000a004020020215084c100e000501c4142080310b50001d0181d800342e290080701581080c0304600c072228640d440410218010700a116600b2405401c10205501e0754404485601e07180c41d0b8524280039800d203c841051050150710f11500c07203000c0c000d588140c24814002201d906511800c10084440018000a03a01000700c0380c2103a011580459180c945082c004010140ba40c0000d01e244581d00b8401a254101c0001030304072070183d10108580e039030ba10019906440303151002014031102c4841030000f0320f4030601554002500d0304d4080e680b01123020203d0b03c94842d812003038070450400f204000d101c1c03078648100c90141c9400c00d070540c454040d00700071075620000640414103070030f07410800c902d4206545806d400105292801c0358031300184201e100d401407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 32627712 1250 32626462 32626471
    0x306060904060e25030506010c020907120c02061501020303061012110403050c1201060b040902070503090604080703210c08090121020c120c0601030b0a060308040303030b0f040603020f01050c010905010501030605 93
    0x514584c8007800210303029200d541d00c0b451040c3c4815604000d26403c10004050061484050040c58060000070700303c030303214894080110b5002040c041c181071114180e912511500d16046610804c01c02050391246a18901c2ca80b0443c00d02c00c4c030410101002c41d0180404031158400e03024003180c004144140065003404c055019100320307006c003400c500117a00381c4209009038116403a007008100222640396008103103180c045c0d425241050075500010740203030f20960000b400c95002a03800e0041c003500c03038030801806050140031303a00c031040700401600584900d20090075114010502c903405034007550180e0f504d03480c1000c03802040e50b50240554000d42101c030340d900f803910410a070411056098030032900081d146c80010000e581c6983e07907038181d0b007a000300010403d940baa040000003645020107440603501c641c4021408010310f4050102c490502900380d4410b80c10300008101607143d61001e90380c106000e01c0c11940c2c1d600c1c4004440e001d00b5404100405561030034000200303104181d44040d018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 32628962 1250 32627712 32627761
    0x603040b060f0406061d13060e010501080a020a020c130e0601060302030901060902090f10090e0901020a030c020c0a06050d02070c03080901020106150503160e0306090714030d050306060904060e 85
    0x140140e82c0d09210031a0348500490000c01c540c031352800c9000c402ca0002a81501c40180304c1071902000e9038000c01601c001c0d80c0107042103004500103124035a08001c0c80d0342e020180c1d29046042c90f55011000355101d131031303d14440c080c14410030342c41c05042868010038000900c00d02182c10650352201c00a00a5100301c43c032120551030214080fa0b9501d250080b900040c000810302c0504000110410240d10302a43c625424041c0c4080005980070b28440914440c000100005881d20071841014040d94a401022021034001520518641d41c234003619030103030785d16450a0790300c0d410b0910700f01c002803180350800360002110900000402102d00014541580e082c1c0c001c1c05030b69610606d130340c0c0121701e2601403404100184006113242c15480c096083d250703403916040b07030070f0000390011030b0a02100382d401403102d03009401e05212200748007441c001d030800180d004100482900100518130301018101520a5100140008056481e40c22003c043d240302031842c03040f82130401400142c0c0c94070f240074803030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 32630212 1250 32628962 32628979
    0xc2105010b0f06030604150e040302030a020c01090e040b101a0706060501050f0d0f020f030403020312010b0a140306030a021203030906070e0a03020607060905030d06030c0e0903160c050603040b06 86
    0x2182c1000908454104406000d10f81183c455408110103000d100140c0050424103610008030211503195003401140a07801950b55111012002400c005003444101e042c0491900c0c200801601500410750050300141d0440307894507449402c0c038698035503500005014103100081c40c580e1151200a0000e188240b40c108043d50744d85005440d0390140800c4061440000d020a41e507281044d045201d01c46c0c0c00c180010b107454a241c1440303405420540d8150010f92010031030f141d4804002e2141805800c54a00b01c44c100301c1c0000f801000903c4020940003a00d0010021500980b01000246a1a0781c01003070b00600500404005035690401c07203807000c4510401c00414401030140d030380f1960741d141c05002d52800509540921030954480241100d01c166101c01250200d20140080c04038800c100304e022800d14510305186c8110704564012644280d407040c14044120000001c0342c40d005110b48003240380f1040c034142518000d01d0369001d00d4000000008020400910f0382c0313036a2050008031800311 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 32631462 1250 32630212 32630231
    0x6180709090e060c040303050a030905070303030e0606010903021003090201031e09120f0c0b060628171003120915030f05012702030c0706090507090c0810050105070c210501 76
    0x2903940c58256020304d14450208030500100788628001d0425211a04021460008a07038a5a1030455540c2c0194000303559820074018001e01841017075001402442e000400b1415038000540d80401c4414440c1031503581c1500b0340842e4025040002d41007400c84090300d0f02c40031200c6001c0540a980022242450020ba03c229205d0040e00c100c1801c031203540c6c8060710329200d60703500603a0ae0000390440d1380c4818180088210010402e4807451a0800890510145400030b040039124071910880110608030355010401504c03038490151040381c0d00b1405000300031400450a50310000950040115040301440c07501d24a9090740203220540404581004141e07690fa240c0590390004e07103c060600d2581c160607400382559600515002190b041d461403030303c00c0c81d82c1d82900b107665015048401d40c00001c0d0030800d1040c0f47c840c0200501050404044903e48424200c140d50518010b02e41840004144030342400300b9113910354007520b40180c182e00742200c00c8600300c04000307a4060494488d0b080000c2030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 32632712 1250 32631462 32631491
    0x60b01030c140a030c120504050c0306070509061c090f111f020319090f1e05090f01060c080d0504050c03060106050c0304060806040905070605040f0506040605030106080618070909 79
    0x560810302e2020568204851140110080c003032160349001008002c014a6007001960720601d80910301c44d000402c24400b02805141c18600c000b4140c00502105000c039141544920b0f0403101c0481034000c44100038400392900100400c0351000282c40101341103174500401880d407160104411045a41003800603d1254808a0302021081480180c00c01e00c0142800c5182941d4441c6207643c0c1d041c16403800d80c460303e41a2440019502c1134944502107640b654003140108040c0c805414241d4602c0114600b42d500035074442d406120f03843c100100c03100c4007000d21181001b40c075030304c528500e0301740840d040505000c0d56400503900024401d00814000080090155007200c20380424113015506142c6010300030394441400604494100e80c0f5000d81500190040c00320300c0c0a0b02c125150b2945440c10b100414080442c0764001d180104001c00003031005035000426241110501d00d00f100c031070303074440c0c3c0410205e2281441c0100301891500038010119004018070043ea861800704101810820090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 32633962 1250 32632712 32632727
    0xf1404020910030b0f09130c0504060302060703050c010213030b160201052505090301020403061b03021c020a0c020a0e160302040e010e06030f06010603050a0e0f070b1b0703060b01030c 81
    0x2582c07044101922104942c0207410124039020020003000c0003182c1180400c0124030220b500c04440f19414800c002000010a1000040c000c280c41c100019421580031944d40c0c0b04194001d01800004174210b2000070f001d404644982d80b49498011304907076a80f612034480b450960b07284240e120403110704804c81e0320500c1502c1c41190314480b0a8410320000200441110001151404000d801c101c15500c42d00e00340024801180300380c00c009030b4007540450003071b44a031b07214607240304050040140d5004500c119103441440c1e4580c1300d0060352112240030941d10b075900345034000d41143d0b114100054401d8180901880340300d01d0750441c1500d80c1c903564202d04074491030003514200109000180643ca03c0060030340d5100d000a003caa11f4040c91030034280c60703c0b00980c040d6002a4458041288030b88041c007816214568880c002d00b05080d0b01003107551142c481e8000c44200e82e60200c3c00c200300032810000302c00780e011448281c6244646904101000c0c00300102c080d8040303801c20070843c940500c20400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 32635212 1250 32633962 32633977
    0x911100e1c081c060509010618170a02060c0c01080105010c08070b0a0603120f20120322050106051c030f030c02030906040f05090c160605040302010221040620040909020d0c0f140402 80
    0x6151322541c0c140a502b05040039101c2ea06011846003011020042e12640b0041c4130501c160310050054564901c0010103001050700039034104094103845030006810799044d41c107a01e80c00521644299074100841c402440154005072803141c5502d204400d041c0c2044124403d49802d94a0f9102020440000030b01050b04418012065104850790715460b03407454040c2d40c00500d1003a0010407168091948071100c8050b40d02610b13141d6650000b0030091824640224490005140a44d115032094901409102103030b40007005060b1075003d0956058828011a41c4445000340034680750342d101c000da00040e07003203070042d5400b07002c10502082c015402003096900048058400f418103000c5996640003030400648114191341d000d0114101001518004141c0c44d9047c440c0e46101c1e00d00f0381011030580e00da180703583c11030000400c0241074003205801120207035041d0380d00201c0ca02d80303d440440c0d40302c1d6081002034807040403118003090003009941504212081c803000c1000c0080321004000c1203104184 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 32636462 1250 32635212 32635247
    0x20301080c09063c030d080601080405100c02030901020709090206190c0816110405070e060c0a1b03050708070b1602130911100e1c081c0605090106 65
    0x403150015403500b009425030010000d00070708815144000006149944c18140c041a00104000760210030002568904403140482c000e1090100c41d00c000781076400007400700b5040080550004084c0681040004041c4090580070000310142600081d107036000500d4090060107003580001e01a03105008201c1d0703280c2c00500c0d035841c0c0003050700501d12418202c203204c014090150b10b0517012603203a901414000b25001c21480700468203241c1210300100d5078034014455407401c010703c04060342c400700b10800d0b02400c0c0e4150f0360b6124440c020030701d4900800d100401c1c4843d20210034045032007880031441200e220f13900b01c50999450b070352141d450711000c0c010352020460a100406074200c000e80c13011100360010b003000964402c0b0641600c2600d03600c141c2940c0100040e1401c24171420012403010f160265403a01e10680c0408000041c18100d8006018080c501503407012400c4c803944070704480000b004910040840c1400e100a00d02518075881840d2048842d500000f07240c60003902401c040c00b4a29 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 32637712 1250 32636462 32636473
    0x1406030f010902130906080d0813051005091002070501200403050d030209040603060c08010f0807030506040f0305090d050c0a090b01050304030c11130605040501080a0807031d0d06020a030c020102030108 89
    0x3000007500010650b50880ca0a090000b80c24a178521605010b031248070003908420100c03600c05440800040c100841c0e078845101640082100451000c1741504540f10205464542d10282883c01e026043da80c5041840019107908016056016030b882500c0c4c403800352101188144040c02d00e004904c40500f00d60050614580c010348264024120b004000704001017160722600e0b400201c0d00b094100c02d0101d481c1c01c1c01800300311045080d4200400c191310081c00b409003541c2e555501c0b0000500010240c1b905070102d82e0402d4000c2c015241c0c4148090300c48101a00182000e80d580d000c2880028020f038a507410204100c2d82d14010641a0394068440c02d1940d03c540d5000c844020480d08192010350003e20003122075511840c0e10070728124040e40c08180c01741044104000c44206070300c0706000d9484030140b80006070551040c1c46003650142810802561000d801c4081d031100112600c6d840b0a6008500c800c008040c1d01405a05240703550421550b00030100507802c0380f100703018880203079102 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 32638962 1250 32637712 32637719
    0x606060703080c04090603150b030f030a1808030c0601030b0903091012091b03060b040e070b032d09010e0f1c050c06040606170303060603040b090a050d03061406030f01 74
    0x62498243c11581040b2000e140a03600c0e640b40040326030743c0c0c000301c500801e2151000e420b0031580c0910440190106c0c0a0305040380d042c1e14803952441000d01c18410303c121050595150000d80c59600010129203003681d40c0d0321058040725486e143d09020803112488104041800000c0c0007094440803000a04850507102e00e40c1d6050341e12840c0c2e61090b1100640f02c0701748100103140281d5956005200002400030241075103010803c0d80d10359540740d802180f8010390548600c800081210483e088108219a2501c3e401d1400c5003a00b2107103203280e030b2500c070074000055070040218294802c0464078001c2052003080d03d8038a448a03a60080c03c940340c0e008042a104c00c4d0080c0e800c00f46205140d0511601d80400e0041640c24100104c50a8030181d0fa104030401900c20421040e64510b225030002e10f140d4034016001410600001e080600303032400301c2d000561004000c0041d140400e41000403500b1803c0101c01c0180900300a02845102e1015408039140780d080880903031f0b01801c58400a00c2c1e16a09 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 32640212 1250 32638962 32638967
    0x603080405010c02130e0105070f031e0203070903080a020c01110607230702120c09010608011503110c01050f041709060708070f02060c060403021501140103050705041701020d0b01020606060703 85
    0xc43c4002642e1154014102c1182c41c4000e00c640342441d00c0550021959142c2424080c00c0d110b03480030101d00745801d0600682d802c4a14910500000307000300310041e240e80351100c00b02d038030040342c0d00b004207010341c002501c043e116000152152582c0090f44e400f42ca070005500340b591101d0041c0c0d0303924041031100600141c111105084403003001050b04610b42099003e03000078100c0c00418401240640110381c4888983c102a40040d016003d541005002c0d545007a640700d1303d0184008072001019902e1460140c169070207812500d180c2101c06c000c0c0014200800709842181080d1000c4461001d803513134036290180050191103a00343c00519290401606498044142e404030204442102040d80e0420040c1d540300040c02196240c8002000c0c070b071409180c0a4a000180d110782c544012080300100080d182001c041411081d003031034081603507103032001d0980b001d02603508000b9154040b40c5180c030320400158040c2441e103003161030030322500340c5040040e40c58000c01c1c1c8159400c1141005820007103030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 32641462 1250 32640212 32640227
    0xc0a051c0e0304140f0301050906160918021b0d020a140304030b0106120510030b010b0c0111040815160e061308011a180f07030c0e030304080c090a060308040501 71
    0x614540070460101144216042d507205800030480b00800e4080616039080a011038030358004190000c000500b041c0705030300d84d200b80c01070031506403058510201d40304a200309001c0b4001c00b00c0d8132001030840d01c410a1800079402a10344176034407001501c061644400001084d0001d4030140d00608104072640e200d20844800d04207481c0194401008000006800740c2c00690081c5425541d100061a400742c941c415508003821180c2d802c4071041d001e2010030001d081240c11203007072080300c44d03403131181960031070140c180c44810308038221020070001010f04000c81e0002c80c00700e101c1c088003201d6880100074100403001c004950001444038000b1940f40c1440130080c2002007030741448101ca50b981b5801c15081d143c80c0b0785407072910100c101080c0d00d24201110310b20b100b00f006c24501e00091030400c107100c1c00e4410041210041513190340c0800003031030051010700c04015025003560f65842d25403414070303074400e882d4040c103003e50901030000e05041c1203441110203807a40203190a1405181800444500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 32642712 1250 32641462 32641507
    0x15230f0115021203040501050609010902071703060f040903020c010f110d11070b0703030f06080303040308160c050307060903020c010906020a02040902150d09020a05060c06040b0c13030305030109050c0a05 90
    0x144194603144951980c83c40255200c0c92203a000842e080c60800d052050320401a0701c9038801c5401030010074000f440000da00144106030303035501620f0b60742d02d4000034441c40e50360401a404c94500030340102896804540c2244120080c1c80c0d0303561680c1d42c05c008aa40407000303c000c1801d900645110041e86204034400c218000100040b1030140e03890782103d03103090f40b1650f022030210369180109000d088140c090703c8000c0003d04090760842c1341c40c0d04d003d0a80341004210b5001c0c40c21008040c01118007079640361030015085802c9986800300c0303260180007840d5002e01030f0701500c00c1c469141c80941c414601f6000341c800031707405003011107003030360a20002d4000c2040882e0300c00c03e0310b4401e019000320000500f104a2003c00d01180c43c0c00300e07006100700e9502c0d64000034044c02e402c110b8a04c1c91800081d42d550015403214a45109503201c05c07480c0d1140c041c40406100b2020007800000605030b0010246069420303248c001c10054482c458542410700c00ca000682c00300e01c0c18040719100350b1b008403040000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 32643962 1250 32642712 32642717
    0x50403110c0f0a030809011107150f030621021504120204050109050405030706050403050915130503011a190b1c0b01020a021003020c010e070807061701080606060705010915230f0115 80
    0x123840341041d02800d010083d046481c0041c440300a200242e5404901c0d5000d8102c1c1c5d090820020341012244199980d1000711202002e509640407002c546440406115145500c00020348035512007504c07902d6040000c1c01684203900744800443c400c40141308050080750301030000c500d40080741c6e231980003401e0001c10a5091000038050b0041036207510401c019088070071078460381c3c2d0381030f80c110f00e2608a909030170803070003170780341811036000d40000320070810070140100c44150144600c090700c4891045540c10450f100b0070042540840c0708007600e0380e81d00b1801070040500800c032020300120307030702d883c00c51019510107840f070005020580039500510f9111901400800e203030111688051030000383d903100102c0c1d980024402c00c082079205a0a01807240400c40d60400c5501d406e0f610b0343c0c0c0300006031202d8860103000030001c0401800750710032042c841d40540e910148030740b03003000c0030b00038030700c1c1c08000386030980c0c810a248007480d1078486184103064800c40420303240d080c40440f2420f110106080700a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 32645212 1250 32643962 32643977
    0x270a290c2119090504050f011503020c0a020402070305040f081209010c0318030c080111030903090603060a030b0c04170a050d0305090304030602030a02031f03050c010f0c06050403110c0f0a03080901 87
    0x45451020380c02c0c48850b54141c486541d0b0a2070b180502c0102d1b000100305c02070446070b0030014807290200d25002c006444003480c0250f203824400540c14200000c461009501902c001040010150894040c10442e07007000c1c01c8141c00c6685001041d11800a0000800715280c01c01000c0030703560144178000307200c500924141c2080da01015001003001602d4105076040d0002c1c2c1d80400c803078182401221580980c00c0c028508505203890240d5690180c420f0f41e5214010100009c0c1c50303074403000c42950046801407000340050400c000000501e600502450300c0141038099200d4110301e00040003008a079011004146424050404600410018010b68101e010401001000c56510300195000c4c1700c450400595a0601003200c0c0400303041c0d03556610310040610f00410201e6804100d101a084081c01d00701815540d940b0110741a5002d40f800508841c5000148000d150380080c501c40042900c0d02103400c1002880e041240da103911200c175940c04048220280005000c19004e0100c101d01070525a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 32646462 1250 32645212 32645227
    0x70c0b1c020c060a0507030605030a02090702030909040602120705031e0a020c03071407240e040902130b03060612070302010e0303190f1205010b270a290c21 69
    0x18282d9100401c040c82d00d0344904148548a44a4071449800012078101040020715250100392a11041c0402071b104800510008451600078000c036940c0842c01001c801c124074092500d10020f402c596540c0d1100c08118000a00540c02101100d0064040301d00da64414400404610036440c0b0041c40d00c1280e070b4090006003944581040a001118895050f0481035000c2000f505d151000e1039018541d00350b0b046182d1000342498000d2580301100c24540001c10682c00d60208020300051b0100039001801d90260b620001d00b90340c480c4030036040485c1903940b41c2d1205020845a0f00340340090a8540d0030000341080150701411287c469104042c0540341040003841ca40d00c550041e100c4e41e00c001c114030407038420304160b00c840580040b03280202c1c100b1065041c4040c0d40c80ca8015805080308070783e5041c240c400ca41c0000c103c020429000200b0407505030391160348038000c07a2104403c01e002e42005d0810087d0041d0301c04180c0f424200c03804000e1207030503030504041c8000000c1031a0390700160780402410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 32647712 1250 32646462 32646517
    0xa0215010f1e09050a0b030622031214010303052101050307150c0c0909021302030903030f0c07140709150e0f040804030609030c030e01020d020a02150c03040e100605070c0b 76
    0x110305c11110300600041c48180102890300303001c0020900100c1d42551003108569040074400500031070707018948054041400f4025000901c00d00c240364100c0c00030003000004243e403000040c460040d044010034402d1511075140c00f42c0b8102030090342d0f1715810400081c00800e0343c800f0101448400d41c50300719550071140d00d0f8684100b80c3c2da0230000c0c20a850b00708401c103500f0401c605801d82c55200c1d600318a0361400500103034490001404441c200308c601030200c0c5405810307000b03803410940c02c0740d00800c3d11a100810310b5a65000c1744610160142052080706c9101d40f81d007404011610680c40501c074654405407454120ac900500c210340c41e190500012011500c14840d1040d21b9101c0d0300c600e40c0000301414040c00c01c111803c5d1803070440d131106280d02030b51580410103826035541a40c800c01140c41d001a0084240031700100d0610034071001c500001d10800360b201042c0680340c8890560403803a160b000859180c820100b0141078503e814a0800c0700b000000300512440c00b1804180960710902500b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 32648962 1250 32647712 32647721
    0x3050c0c15090102070803070b06101e020a05060108121c06080a050102030f0a2309031c09110604030503120c120f0703050c211e0403050a0215010f1e09 67
    0xc1e26440002042c40034195030100505406044410b00440c03e000c116900c0f1400c014008124602031500e121403280410b000e8281041070300c103400030007e40d1f125260310003503580b1075250090315035109050001807101c10110b41034403d81d6202403800e25003005c0003c1840841d00311000603c00a2740c4c1d020005105405200800ca800d00c903500160350790600356540003000d00c01601303400ca4603207802a40c4009041c0b000c842480140a90300ba821030766079181d1080c0c1036005101880b01c03a11f4000700e000c0c7d48a01d5942c00102005e10641c0700ca0f02221000d0107002c4240128000280640c0c000c01408540c406042c0341583d000c074250010324070300341c10029004289070054403040115484030b803c1c443c596400d07016030f6600c84154143e0070f04196031007400d00c9006203160720040081703075481d011610007050241071407100303204401303202e0560610b850000e11039841074221000500031001546d400035103a0540c641292030b8031801400c007a003040051803240c410307a6140f0300840c882006c00a031b04403d074007c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 32650212 1250 32648962 32648989
    0x60f100c0f0804080a060c09151b0213091a0609040308040c18050601021b0603190603050307030e01021203070804120c12020714010302090a03060b031203040b06040e1903050c0c 78
    0x141c1020700043c034140043d50310035964641800802c1500b8422270015521554108107585801d504040180454040740355a114010390062450014008900400d82003401075038410b14000410481d50070510802210941d02203034883d0400011401080c03007241e140c2d80040c010701011a101d55280810346035030311400304c4500d60540311810019150380600040100c000c2c1b1400c030102400780c40b00000e549210007000c20000400c00e28034004200000d502a401035a03008045954410090070060092440b940780b4500502c180e580b00c5001503160703010307a80584002c1e01e078070855444581e07410710035560345240e100400000254000128034402011004070728140c01400c0f800d0f040820300d600c828031201c0150b0504d40108082d54054487c7c050850449410003c001005045c1c10002400c00c98000c3c583c7c82900d002105000c1480820324019008440c2141d040003090342040806480c0d050050039104075950ba040e01c27401103030080000f00346011001003075692004c20381c0c1c0041c03a90342e01c168 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 32651462 1250 32650212 32650229
    0x90c041418181906140114011e1b0b040c050114040504090201030b03030d1b09080c0d03031103012d031a0709050a0305070503010606050309030406030c0201060b0a080609060f100c0f0804 82
    0x41710114005690400c4601422108011010080c04c0fa400600a0104622074400420043d000d18a11600c01c1c04a41c030300400e003010000d0f04208500300000d485c80250780c00e03070300c804120b54006155030040030401e1403003885400150409207000d082000802c8480d0040e414592a0b40c4030035150b030750600040c030b500700e00d0500002d142140f50349400100104260004203001080c0c606110354800040c0700b00800d54200d40c3d1000d865100e00c0c2c00c8010b4800006122000303c80400041030818038502d514040010818041c0782c1103103100fa0b046000c0080b44030141604079041d41c0701070071400241c00640c1c410f4080c24501019a5904003254201070903610580b142d80009605200c103150a0003904001d18091504606605010922070744a100b039215000a0580d103030a00e00e0924000e40009004000e02c040d050780316180144050b00807041162110701c1480394000040c120718229070168042d003005000c0754404005810207503001d121035401034410310f100b59022000a008200108060220f02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 32652712 1250 32651462 32651471
    0x30602030403030506010206070c021504051807020d0e09040303020912030c0714030a02090711100f0c120c0806120f060405010e060a0501030b040201031109090c041418181906 77
    0x42c20300404907900074000c02e0442d0000414040340540c4011900700480c0c044515042400756140140c4061007079a200581100d0125401c941010340742ea40a4440c400b55020780b0350100007098207d4801c00b4800441d688aa03188000c10046442680505031409010305100e41c084294041c482c51600010190589580504018440007984a00c0b0405104060b00245140046c650008030020703001405a403c00503050150104860104001c100400ca450000c1000b40e0000c50500301400424140ca80420380d1403951811008042c426009903048a42c6c4043c59600d8180c20409560a5031603045590f1044050300c0803003150500456004c1c03440b84000188030800011001d0030000000d241c160748916100042000c1404444801c1d8880c0e824a000280c41c182c40e01001001c3c0505048a41c001d0b610004114801040c600144240c0c5c3d40c0708000040706071248104040c1d40801d9907000200302d120350104001c440d440c4102c041c00c4d02c0d8031058a0442d0340c4000b010941e059090340075282d00d40c46 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 32653962 1250 32652712 32652721
    0xc030506010501031d060a020a021203090703111905040209010c06020f071a0415090201091e061107120206070f020907030204030b10060503180c0a120501060e0712020a090b0403060203 81
    0x600c540e4403030008640f00e14100c07121700c404039515403d00400d4001d00c40e40024070b240c0664400c1c018002c4a043d200f82c62510383c03d20035041035032a1141d010483c0d5581c0e00c200c40500500d02220201b00d00c00c0341c51400e401b09410401801302941010310b40c035040c011240907100004d14103001a00d40400d0248001d616071110f400c0055245e074500c41003091030000d000620020620340d894215940040c0080443c07001039601c0120303600e10841d4401403a280c0024405100112003000c000d084940540d9000341c50094110080d407a00014030522481d0344282d0030050050a010b00640069402581c110714040e1a60b00415040002190502c000036030010b8140104001100d90390382240520003e0221141000c00142c254030015005412943c0d12241011300c41408000041e01803402521002c141c5944898401840405450850b900e5080042c00b15008002400c2c4500c5100c2c943d4440c44242d0703044c03843d94020b501080e80c20b81040700e010341c0800d0f0401a800204010f500c2000016589d181 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 32655212 1250 32653962 32653967
    0x409140105060909070f0504090203070201021903180b0405010609050f04051203071704060e010204140301180201140a0311041403010b010c0b0105210a030c05070608040201140a020a0c030506010501 87
    0x2050300518882c200901c859000e5407203200d001a4801114107142e10701b540d21880a48090003213038026201d2238000400c0000040e07041d00070702074440d0005082e15020740d1a00b4150184c03036018425103000318050300d00314046250088101c0d0070078003440002680c1921502d03c001a20f174100c50121100d5010402d01003040801c0001c0100b43e2468081d0f0360460402c1c40d8020720701c1c061070703414101009100e0702090601c81d156105110801e0440000c55540d81e407000c041c0507030001e50303044a1207035181c0f450018995481c40b1140040e40e0741652920702c1542c90802856860b04061040810107a40740c840a0301d0810040041019090b00c845100441d0504000c050a5400324000d541c100400c2161b410006481d1601903810b40ba02114a030810700a20400387d10901061100d98405200c0d01180381e041c9070b081928ac40c81580264280c0e003116450b03c50503101c0b0354041c0ca000740026045000f40648010a101621150401e841910746000281d00c6038020000590426640c03508404010441e030f68 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 32656462 1250 32655212 32655251
    0x1050c06010e010501020d0212040b0a0203090307090f0b150906030907090903020c10020c100e0112020301090504020f0a0608040b04020f031e060a150504051302120a021809300409 79
    0x402c0744000c042881c0c0c642740d60141802644920000701c400803901d031808500a0040d180070b000040c048440465403400360710098042c92140e010140c0c90244040401e0800001403003d030300865000c10f2401d0031041c2030103040d0344024851100d50180100108c2c6d83c2c50140101c0a07603034041e078024030802c2e499008010080c00040d640c0b406660245110034096201c9ca5401c500652060400c8003002c0100e000590754000000a07011640d0301c00000460341c5074541e440140520300070386034202d130f244034142401403000103402100c021840040000300081c0d405007000e41c0c00391008d400c01e03a81e05403a0000c81c0c07801c80e801c01c072244810308025401c00810b100300503995100d0122042807000060a02d42803902c144140a1580560388500000300d203000381d64848a901c07036001d011110706103031f5204107545514a1180032840f800c003c0407101d01c00c14208590364081d02ca1140541300007041c80780d01600c00ca07801d6209008190400007510300031010240508001c01a0b40f50104610a0b410100100070f0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 32657712 1250 32656462 32656483
    0x3060b07051f02070317071206080303010f0603020702031203060406050604140405251d030706120e0705090f06030c040e03120105031203190e0102040b0403050c0114031501050c06010e01050102 85
    0x301c0c0b0500c12000884d502036001c100c0364890140300101607c40d4401100d80103402081000985d041c0303000040d940100200071030480355406002442d1795291101101a07109111004c0d505070310000c04c01e02000102d500442e00540c00a100182c2d8a617520b008c14132a80165110b41c48100f81884110071a0420b07000781740e030004a26400050322513510510f0100041c0038500032040002c61610020411030800000241000003400c42e03140a80e0b80c80000c0c125403d0082c012800da0074080300703410904001803524140c440c002e00590003a0380e0745401103122007004048642c9403041010039600d0391134621842c076404c1d0b80c50700030f19940d841d0790f20720346821001039000a0083e80700c88511701100780340c0420b481c2c00c66001e6042c4240d0381e09000100d005440401054941940f0001d0005000205440240210380c8180c003910080a400c01c015900c60f03800004000400c8003c00c00038907e2689012804201700c1e05051903402c08800030b00d01480c02c1026000040302d5001c03600107129070343e010031140301030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 32658962 1250 32657712 32657773
    0x209060907020d140405120a141605060a261006080402030c0118030c0f0e07050304020a0308030705041a0a090806090d08060a0b03070201050601030b040b01050405090703060b0705 79
    0x11400d09600080d07075003094142541c1000351064513024600390b158100d40044c640102202c104005c0844d03c107842d202401c0040300c10036002c10702e665501401080b44409403070f0048855010601d0320781400125800f1480f46c1080101d40b440790090410704010040d185400b02c10080f0072494000004284400d06803c103600784200340c4c3c20000103960018509001c01c60030b1174a1240b0202141d0f0340c0d00d40055541000745103010310034020901100015400044500c0070700412000c0e15019400c0d80ca6102c26540690000c00102007800072905030802150480c60b50714040e40b1b0b00355210310717150401030b44403101d400a0340005150355000d64407a00b80710141c100500500014140041d005585800300e54008050010701400039841740c1c0d0b01e081410040070ba003a411541c070302d0700d808000e000b00300c200e84043c04685001d000ca602ca0410307110710410071106841c2d9a1400d402c090800035400c600034102d0003096150640820641d41c1d0001406c0d001d8460310081106000c0e072043d01600400b6080e00010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 32660212 1250 32658962 32658979
    0x1b0f0f0b0409090609140f062203081504020d02040302120303010b070f05010b0402070f0302010518150901110c060403090b0913052707030b0a02070b0105010513030519020906 77
    0x212040310894085840d0650b00043e10021841d011011705040c01c0e000c0c140c0f150a4240c107030f444202240d040c0519404000380e40156590713110280007494544c651600c003030f92249028000902440b91541c10510a045041d0200607140009040c4c0c0d100303400c01c3c940107801042c10021820401a201d40051034100918110341c1000b0b00d80b40c20740210240a04001c0e154040002401400e6011002c002c0020b00255074032061414604112840080c04500561900001421016808003a5099031b004076015100d005000c000c0001110f030040d1103440705540e2108a1182107508500901040325008003500b010300d040d08000d800d503040b640c0000a400300411442030703541c7c2c2d05100348001134804c1c0c00000d0b0130784404002400e8140401d1840c800c0a8090080c81c0b074000340015007801b00c070300c165483c103c141e9400e042c9030243d008205009003654805001804950700980280c02e810307004500d00c15020b030740d91b02d0b01480c080d00c80c8001c2817174500ba250fa61096040441040d41c0c0a007050319080d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 32661462 1250 32660212 32660219
    0x70606081902060d0e010207060614030a030e06130e07090305100207170f070b010b1b010b03060a090305120c0a0e01020a0c09180204090b010e0702070e01030f0c031b0f0f 75
    0x1c5024140030000e104810005019292142e240e10100c103c07045e41000710b440749818900400100001d000d1102e843c0c01c5070400b181503240018860030311660560742c007031240ca401811b020040c2c0180c2c100760340e0822400800f099181034200810b00c00d03103850341c940c0421490350a019041500141012202a00401071000482e0512070f001740000b101d08120f0395030708500d502d40686405409402004401e07c03400000b0002020400392540f01d2002541880e00c15003490002d080300d03246051550560480400150131a100740c2c4200b00c1c003800b0703060643c41d00201500010030628201c03540c3c80ca11901041001403281c0c81800e80754030500a00040281d50310741d444003c0810014400d0020940c1c46000c82a40221030701302d644da42d154054030501a1240d50315152031060802d0281c0300c2101c9804001403450f5100250300b1046400390640382c01140d00310349404140c0001202c0070358990004440001c0040ca04075814036211401c80365101c101d07800d240c000201a813a40d804001112481c09060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 32662712 1250 32661462 32661493
    0x4050907060212070c090515040b03010603030c06021e1603180806040b180109030201092a03030305041a01080c030c060a021f0b0405100e010b042402070905070507060608 75
    0x2040c03400f018000d0f292288480d140c803e440ca500e80d00440c04281c102414002290000c00c8808440c0c041102c00340003411054003030500300c9105100180001300031000038004104198010141e040241ea1105038045000100071780d04e9200c2d0110720034514003c0c00320818194851030080c558406080001c0c1258503001c070017543e070704003c1e01c09403541901c1004600d0880c02c1c8943d00d60030030800d6000b480140542d0401a0091200c40400d030b8010f03401d151110308080c00b0210940c4020703421182c42c14028150b8170101d0092034001c0c000c5400100d00300580210a004d010124001c1030641c0050a125200000b41410006601e844900846081c498488066008180010a142403d004840324010000b16201405e0200700d059007203442d08003400400385519100380c081e91030503002c1412590380e414010b0210700c25441611418a10340c4004540c0d10b40300c07000303440e50f520980f0442d8002c5448480369412150103481d00008260000380070340c100304450140000800c4003e010340001000f10401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 32663962 1250 32662712 32662723
    0x405150f0610091a0403030206010506090a060c08041206090218040305030105010e01050f040608070f091401030c0e0a090507030b01020a050a030c03021c050d0e06040218090a02060f09040509070602 87
    0x44030b2140000000d280290303803040000c00010180c0c40b004400e0b007401408450b04560113030005500600a4030008a26407c00b60f00300e50700c8440c05465000000d01c1e20000702e42540200340c2c122800403041000040f143c0322944902e2034035005080000b01c0c00040d00c100011341400d412980c4d10b0801071070411010035046400d03030741190f00c2820320380c01d52807180c00100d07010b2180c4074130b14159150101d00821101da008800c40d114110b2070b00c640040f080106401d031120b10f51417141190000c0d21204450885d4405e0700080804401820002d81d41103581d03000036030040d0031b42c10a010040c0c1e160204a1525410b004010311140280003828040081e52511516015043e01c098244041c10b0f401008045c800c110341003150354159042050164020001030941c0d22500301010392608040d008180d00c4e002080c2c442c040c55000344000c280080070118580941001803005c1c4450260709a0761015844d150010001ca542c0c04414030380e5492190100401c543e0050940c1e4000c0e405564103001c550f800096 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 32665212 1250 32663962 32663971
    0x10515090601090503031803060912030a020f0408010905010507030f09151a090907061e02060a0b010e04020f03010906080304050105180307050406120501050108032b090203060408030405150f 84
    0x8003010240e80d14801030707034807003010b51025805120004469400704a60054503512410132010b991954076000000395aa031410703070380c100c51004100042240001584d0003000c805444507039580c14030355240c003050700315a82c1c0e500c1510103035148c004100303000d981842810301c4106412402c0120805a0710b0b01c0180084440590700940c7e680c48000c0c0440188105044d8420030040c40640945080c3c582e803922141c8a20441c0041100340c1404100081081549000c1410540c000c09003941c4500b00d000141c01c0e6141c1881c148210703001c1106241d21580002e04c107000c400712804d82d5a52415101c001100c80030313845015a0b0300248010b000581e4080b0444100e80c00d40400800b0030300c02000020704240181d800035038040c0c03621500240c0c0032941c6c2808244e0501502c02005183c1c0d90b0b006c000d449120707540000c12054507448c43c642c29210000c42004484c1d41e100c80000d441e21440c0c2c0401c1c9030010549060710b00c95070200811081010821030a00c440c030300360840d9131090804c0c602c40c1210040181 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 32666462 1250 32665212 32665219
    0xe0406060b03100314030702042c0102030705070609030c0506010b04060e060901050304080d0f0f0504050d0e0102120c0a0803090604120e01050f030a0207051b0a09060305060a11040f03050309040c02010515 90
    0x8560185c131242042070743e5455400074410024003ca00100c5501c28076101e030b4402014903e65903042600d0300610a1341d1103000d5580b9068504045969088014021180304805110141d1700c07001c003040d42000716501a10f00401c1d1250745a040c408090686840c0c08000e0740303d05000c111a0980381da014003079030303045984000c0710794442d0344010340d5501034110700026032651361a00d484034814071065000203000303900407001e8800b040781320601224010204000180981d00c541640c1c02802d0314480103000e0240341c0c00503958170343c08690f1441d28a03802511094001d03400700341408140103040b0080643c1040c9414101405d503080c0340003034814014100ca003a00c50300d001c00060401e60154040300c00c0320b640074081c0d07030000140c1c09400c40078149080740e0300d000300c10694001c10120154071505007641c0e00500180703200e03610441504050400c0c80344030484402e0910000951030070542d0710700f01443c0b28001840e2140b6076501844100d83c0c403582d042c801c40e0704050920041100000c451000d8a030140d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 32667712 1250 32666462 32666483
    0x2070f150e060706020a0c020a050103022106120307050a030e0604060801060f05090603070f0806030102120402040207050705030d050301081005060618010918020c0105090703030807050a0309020a0e0406060b031003 94
    0x107000201a401461400790005000040d42500c46a00500940506100b11400ca100d2074079603004508030b004640111008200040e00691440040c0740d00a0b80002c0c0200340800a401d000d40050441e0008101241c035640b00c04c1c120010190410098010b180045e10384078107040c41e010300204100c90601c914002d00c82c2000d200e07000c9900c9601103800e860700c054040c0340d880c24100b0000380781c4403046103040c00080340140452401d02d0103008442480c08103040680b0251074030340820001354401c180c229068418008001100d80703050003000908540741c2c64264896141044450403e80b0395003c1e20307003031880c040801200b5500c0b6416100000204464ad00280d0311460050360310b607002e41c02c007a0186208080c0a00303c018507030024070b110b8110304028000d41d281e44107841d50381c0026000040108041a0000c2d03c580c3c461005025444101c1c41c0c0420402d00b141c000c40c08100c081d4001030305041c002010002440880d0168000501081824a142d403809115002a511080c04024050000c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 32668962 1250 32667712 32667737
    0x14010b010f020a03140904020a02030c12130302011805040608060403080a02130b0304061416090902040e0c07110901030f021e03061605090405131a010501050d020c010e06090303010602070f15 84
    0x3000151503886e20b02070011540d030920b2400103552900a0071030888544203800301503040c04800400d03a80241c030500391142043e4110360043d00d8421a6030000e03440080000c5d80003400382d2344e03401403000606a0070043c0403141014200107002510007001404400e004011081210030b42e501008201e640401340c07103859407103919020010b000f42d035908401d01c051460078090210349281410300a040b10b902d0756106195903081c03c03c00d0340102c0c81044406580200002d1401000000815280c3d11035696601c800e078694000803060002a0003e591402c0064000400c5046c1002c107014041c50b901d0881e03d81c03032a5440001d07035892004100032001072150302c01d0184180a002564501c4200410078040d43c034004000d0425241c1c0e0820a803090004020004440d4680780302590503a0340607580c4500d00240c1c2c0c15940065440303038a051801d907594000754200320105100c16800f91181102543d80c07545008402171034203223aa00100c81c0120a031004001810703000401d450101518180b15040d00c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 32670212 1250 32668962 32668997
    0x30902010e0301050a05070e03070311010c030203070f08090f0603132301050f0703140c030a0b1f080a060602030405010e120a0c0602060f0123090a11040314010b010f020a03 76
    0x218403030907540640c03d00040c44125586600814460314050340c0c0e000c2a01c0d95003082507942e0b40c040c80701802144860b44901c1e500e5100d12814824640240104c9242425913a0b911040e0556903030140c82981000c99017001318a03080380031508845048400a0440c145840400713942c801c5524004c2c0401031a010340e203c0c50500c840101c031880325a9008102c80d15010005084ea190210f9240300001d03d425842c20100030a484c0c018003c00c20320f03800c0c81c1960b8404005d0f0005046404009510550720f00a0700741c1e034a420745d94100349449641c0c034807815080070807002c420b44e50790741c01000c00d54006000c28001c90364401440e2030b040000704c81200c240400c81c2c070810300740601800c002d0301d5620303003074000315290750006107441c0299582a40c411a80e0703a1340100d441c1e1882030250701c81c0592241d50203080c1030b00d4003034821074100e4000c400c0040e860440c0d14501119074069030044030140110025141184000e1041003500350080c01c04881007108800020340301d6180e80310040520090f8500b5211414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 32671462 1250 32670212 32670227
    0xa091101031a060c0703060c0314070c21020c0103060509130314090301060b070c14010c0312060b0307020705040501120c170304050310020417070b040b0c010b03011a03060c0301030209060103090201 87
    0x102c098029076a550314419820340b0b4078441c0c04251011400c0429150b08036110340700d0b6814030700340809000c51030f0b1186501240c80c42c42c030b0081030350541c4004041c1c000301420311100d8219100c582e0014140d8202120025040d500c05600a078411a001400c1003c56841a481c01d8903440d0b0600d89140ca40321524003240380c1b0300031821030315050342c60118042070110b088001404400c8c002c010a0742026076984d0301000314400b200c0d1075030000c0d1142c54400300080c000d038002200c030503c034800800c0300c1c0d40740c0c2d025401079041241c0c2c50300140c0c800c030401c1009081c0340c4902400341c80b43c2c800b01302e00c1a429848090100059110744031100007000107080d000b12051043d0381c0600f0008042da405200000c1d1144080d4100740104400807038001c085150900f00001c00d10125070504124900303091034082607021a40140040706104d54076100d41c101d440d81c081c0708080340003108410482d90100e40e142450314181c0002e2403001017031420001030007d07a94022103954841c0342480d0101d103038141c0d032004079200c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 32672712 1250 32671462 32671511
    0x102030d060906030c12020117130204110d11271311072306150d0507030b04050d02070612090303060b07050703020108060f06070215070206071104050a09110103 71
    0xe80340c1440820030300000d80101c4116401000880300c010340b202040040130a410030024042028120300b0a6035060000d07401c3d40c080052036003101a06800e8001c2015a0145d6208031440e8400042c01c404240d070a110b0064682400400d032820543d600300b1080d166082c0900c10f132100388080300c6201c4603654007510500300140c01c0038180308094400000c410700f81c00c01402210440c140d1001e0a85005c030122120303902010a20081c002c0d5200d16500440480b0145000c80d0003c0d1022040d0006c10000c00c403801c02140f04040d02000341c83c0c00e041150802c40e424a4100c1150000841081025801141c002c0c6c80d4418040014600b0101d00d8250b0080c00582d2085c10945004655003081c44804103241c0112030003130300c03501c805507074200401035005003a8807202e40c03100c8180143d1000d400c003c504118100c1e07070b0018031413400c10142c0019809421104045404035401700494015040c14003406401c1104c125090204008a42d940000f0001c518a403504150382ca10100300602070f800c4604001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 32673962 1250 32672712 32672737
    0x403022206080304090e010c0503090d030b030118050a02180c0307050a0201061205150702071d1003170c0c030601030c2d06050c06010f08070e0c122403010e0304050609010203 77
    0x141c40c0e40c1c800700d0000d004150030421b0305520703080d032080980740500e0880380b055206170050a04140c000100342d00406440500d117806d99130f240702080c14103540c14003041005014000403c2c0b402264810070122107000c0e035000e040900c140781407100ba4110781040d00d401c8441400c0954030b5001300d0000328010700c484c0d44412110b800180022050100124002c2d91032101c400d50a012540c404000303990701c8620380720f014550444040210300223000c200b03813aa04030180c00b0303001d10103564a484440c4001c0798481161034202000510019110080190903800c1303d0540140000750b01d140c8035444101c582e0b216007441305510003168405030003550041d0780752048640b83e51220540300d0344000c3c099042059040d8180c440c00c0008143d16541c01e8412040700c940400500e0b0183c10b11822030325000c0090f25000004200b03200140019200c159114030138083c1e0188030520b1036065203c1040080e031260b41c44e010b0303454584460303070800d00031045034161407050315400d54078041c01c0e004070b01e54480d00382c0c044a0f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 32675212 1250 32673962 32673967
    0x4030309021f031a030d12020f0f0c060f0403021c02010b090702010501060212040f03020f03120705150105010e010f0e0325050f010f020c1309021012050c04030222060803 75
    0x902c203440642504410708240e804001950710b4595215000c0704a007280c3d58541d1180320407080796481450030b4000541010f002500304400285c0021007038004d810140fa100d0700c04070745075002100801c2102d91110300107174480428142a207029440f09480040d5443d1444d0180414a9a078000d4100c60176501d03020b0040c0c01203280c0510000d00810b020300039100140243ca120803001d00c8814162425907001078910300040d461507003041440d00030110115018002c1c1340a841c2c0c919120302c080c00489009134090310010070482c040741c040d0300c0142c102d103050004c4030603880c0c0e05980c045282848201c10f41890400c2c000700e0380c0000e1600d203840c00c002d81c0b0050214641c1545c00e201103010012540c0546003c070590140c0ca0054030310859004901c2c0c010303400004018420b15005c5900e42c0302da21003200000d00c40030590040740c0202144070b2104041489005181540301041c460716038402001444103041504607800100d446400144610651b42400141540c808040d03210f000148418400c507907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 32676462 1250 32675212 32675239
    0x210714120301030201051b0f0d020f0c0102060c030702070f14030705041e090201020f0d0e100203030609070509130906020a0206010603050c120a0209040603030207080d02010c0512091204080a02040b030120030403030902 96
    0x9d0b641d04d507405801c401030080b0805c00c5103503900043e40c179154000503000f030f1095a03255214035000c0e0704000d002c4400c52148000000f4402004c00e03140c0050200d1140105030f5018000c01d151074502598032040c0103e1411801c010b11414141c45c0840c0103054642c041030401550004030b103080e50b10740c1e141009000c0c079005004010b400c221014a990005e54030581c80c0340451900340d859010855030540c21810020009580034480c400420382e522000304a0b045040700502e5030011a00c0000d0308552103a80001c1110303540e90100804e03401003105180034411032608002113107060041b03110641081c101e4401182c02803242c3e405883c0d404d400944100050360b564200296030b14400e105003100c1d80911403400c26010710600030780102c9030680e103400703180088102ca440200c1100500c0c40c03020780128a1071044803800c01c0c000304002c088540c018841140c942c0104011140f410b83c805102c2da26210700e040001d480480c2001401020701042070b141e80d55410700b42d004d0060088001c0d441000f00c120311 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 32677712 1250 32676462 32676493
    0x140f09040b04020c0d121401230d020319030507140102040501080108060f0105010c020105070204060b0a030606090807030305130807030f0b0c070221210714120301030201051b 77
    0x100008a8111001d200148690741800202c0c89610350394100394005440c17100002d03000700001c1ca4590403180c070014003d500700e100c04030016800e800184000c907800c0b0f00301c60b484414003040c09150350119503082090703c0c5580080da0303584102d0200c10300b01080503022400c0c10300030004d4440c03480d0000c103c0c0c01c4000c102c1d0361540c001c0d0300501a690100e2031410000c1141c1100040d19845400c0013140f007400b907401c000c01503035030030408036080341006000c11409005844501405c8010090b02030307030980300c4400305c2d40901940c0003030300682c1c10403c2a40c02044240c1d03001aa1004aa030076090203035464010302c0e100340064005030080c010900c1090350000400120030000d40510340144054480c03525503010f2034455100d542006580155040c00112120b5041c640745145040623204581e10940144005550005e180310400541140031404109008181da0050201494038010f031044521040c60502e090106000290400c41e0104001606200044091600b11641421200541d10802c180d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 32678962 1250 32677712 32677717
    0x62701020903070815010807060507080d02040902070c050906011704110102030c15041a0c070b0a0221060f010302040b160f08031618080a0312020702090108100c0e060a0f140f 77
    0x101401c00c0c06178000084100c004501401034402c16640c807032801c4915214095142c108000c0f0b800c5056081000180f8406248001e001d0700784281e040440481c504410000d00c1140201214140500c14403c50300e0707070910041240d03010341e1200700306403a1280c490040345180a5410741c3e50b400e11076100294a220700520125204034822030f020850f844604000c055443d100f40d600c00d554580c01d0000100082c070b4003040940c0203030400f00050520843d401000c00d4000301010070340e00b82c034000e41400b001e0b00748841c54040020b02800c1c19842c091801900d21035511a00d03440c0044026110300c1030003008203000011045a40007e55103440e42040c801c90510429105c202c48003196130b64002d5550240080b2102c0d0032190340802801c00c01c9401d0b181591091100d03c204030a042d402c116107801a0303108030045019000a200a1a2580601072405c0032540807462080502c512400109495030394070307040b11041101d61902c0074035803480c4c1000356688400c015440011403000f0580c5800314030308170b01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 32680212 1250 32678962 32678983
    0x12050304030606122001120609020a11010903081305030415050c10090b0604020702040623010f020105040b04021309150b310504080c0601080d0905030627010209030708 74
    0x100b049100e0b901c1044c0000340c00c0ba07040003404c1c00c03101480300c100d00b0041d0141030681001814000a0400d0801c1e80314101c40c0c4c0ca0704113110481d070120300d40c450030b41d0103195207182c440134100800000c400790301d019100c140004c00d0a2400e03c24101114100102402a035009050300800e6840e140b002881c00780c03d94008409240d0f90b845010fa220340c0c200240c0c014904555008910155a41c50311411b000c0698003000099070031035295100018000c00d00039001203c1001b46042c81003040ca4131000400d01d040700002101160306010500012030141c0c841940c01a034110b42d051500c142d0798040001900c5d1038040581130110040c2e51450b2503aa0341c000040e0040102c6d41000001d0800c50420165110480c00842c040241c00355103a866000340d10194005006212003400d0001c1c500009150900c00d800541d1a600240024044c00313811502200181604a01820321460500c103900031020803440e82d0703055104400310b0841410420350490707030003650260555026507140d600d00daa42c1c00d00a81c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 32681462 1250 32680212 32680223
    0xf0a08010303260406020901030b0d0b0a0b01091809020f0402160506010503070f0905070e060a0c0c0e0f0402130b03071707090203090d050a090e131a010803221205030403 75
    0x481141051002c0e00302c800c0c1a4418070303c018681c4664440c24000d41244480a050540c0e41642041e281c0e40e96680c419000e2289010308254500206460180d81400c1d111506116a0a6090106408420b9035051a100b00500020100304500006420726100d0140c41c1c0c0191001070340c200a44286840c654519004400b240d0450360b861050564030701061281caa039a4040c03080500c1480302c90b40009030014298a481c1401c420150001039181c0d01c1120700c04080358101c90035000704511075542c42c0041c4101c03948104945081910f2036203080c00100000e1041030a105001001000382e441170008090240c00c607000c8a49514140c81c030840518258005480740d1080010240e104d4021203128603203200140aa01c0031082040d10641c01200300310382400844000031070000005920035101d80c6090358501d41d504d4043c00c3c2004c04240642c0e40081031400303c001401180c2c3c0020498a10055660f80313002212000c1c4c031215a0403445400813515404103007010000d01c44000050410303a40103d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 32682712 1250 32681462 32681477
    0x405060d05040303450209070203030f0603030702010e0f181306050a090203190c0902030c031807050609010c1103010504060b0310050603060f0403110109060c020c0604051c0203030f0a08010303 85
    0xc0019000c1e40b50309504503810308a00e9034181349859180c80c417a5801000203800c1001ca81c500d6400076054000855a0400503403001c001c0017404500003020741c1d0080e0003600030714600322494000800c581c1c60700c07070340f24001c0c003420000000030b1701c0703000341d00006101c10b80c83c65080d410b01901c44400d6209620382512024202404540c02105601c01c07140800d40c014010429000c2410803600710003003509060b41e40d803101690020354009540011481061a880c03095500e1419504112040034000f0040203580c0c4121411f001d00d4490344100c1d0b00402c424203101c01d400d205890210244041d881102da05542090103110401889401408041900301c065804512054210000303e48007250955415840400400d00c803c2161140da50418028900380c1d950710b242030185420f6510348401111003995803050100c41c19130620100f02c0b09071040380c41614040c58000040c0011107681440c50b49810b1050722a01151b40810850350060120f108054032912411006401c01c1003d110a40124919 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 32683962 1250 32682712 32682731
    0x6020a0e040b090a09020d14150a02070506010e0a060902070c212004020c061504061401081807030210050309010507030e0d08060103060512100c032304080405060d05040303 76
    0x1030189002c06000586411803995610300280e0181010754016a0000c0180c0600c0002c103007100011000c41b481700c5c0003481c03148541e600f0300381160801030240588900c1405101d0008101141850450740f03200050805510740d03007920b1005041581c0400d121903c00250441004031005808085656007074983c005403c0c10803d2001d690356000c001000c581140340315452042c0754845050714142c2c040d0005051002e602c0d8441e207080030989005060240c1034080300404e18242c000c2201801074025008040ca000d840040d211601c040c1050405135030070500c0c6940703140d04220030001140c005240080d10052540068901d52007075882d030501c2d5086c4000904050701901464070040341d038800600c12007200c0303041107602c0000034000d5410035880b00c00004181d43d0b2000011255103e08002e42004c00d039030079001c807c03190b00040782002c1c0b50a000d0604200ca0074031110482031079002d0301d5002a40c1d80e5182c6081540305a420a07a84214089030b41041c1495641c04035100d6132090300c040050030b55 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 32685212 1250 32683962 32683969
    0x20d1a010906140d0204030c090504050d02010c0c030e0d170c0c06030705070602070203070503060705091e030601050603042f120c06090d020102030403050a060504031407051e030904060306020a0e 86
    0x850044102188020340c11040d1180050004c1c00e4070012030a0041c1056101d0f903800041c11015406003104c151220188018020280030500c840344c00ca0008200120700c0c11006481316420503c050148881e03842c030582d03d501c0d00481c40c80300d181d0054200b80c000510400c024500d4000740190344051041034030040003400c0c00c0f0110385c0280001d460301400c0c00d00f56610070001c0d501650040f6054000d01c0400142603c040041e03d010300da4940f60681c0301d010003414040d0358060201c20780010704284844130300984000c0340050544100703540f80303075aa070746030708110341c90040e050305100706a280c464012200c2e003003094a44880801c1110030291746a9440911655552010314065104030f0400c084003a41c0380c40a1044460703841030040d6804c00b50f4076140d16080807002c20041e20407603221381c100030070107a10026174549600101801030400b42142c64150380d541054000d0300c031660644280c6142110108156610500d0040c07040c00001c2d20303490290003035001259000d0120350340c04600e052928 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 32686462 1250 32685212 32685227
    0x1090b0c13090209040212090c120114130c030b0f010e0106110d180812040302040b09010b07080d09021002010f05010605040305031213140f06070302030906130510020d1a01 76
    0x300c03001d540349001c60500c0703000d070003e5200c010f003240e00c182d080000480008014041911402c500e41c0940500005401800300c0780512186540141c0d242110703100c9103080440c88071f034015810001a24602c0220b14007014144420740002d001c072105482048498a03610312070314103841c01002a40308030790b42c501040e214255120028800c6400a88080070254824003099174115000541903840c40c1d9030703d074070906143c040d5550403030b65440042c0603c25030134540150b10000c202903422154640c540142000c1c90b01603c84010b04c14100028010301c540810f81102c03204036001869034290100d82c1c88080e00801c1403151005d202402c140001814a00440590301101d130098051454171051000700507528070b0050120541c0c4c06021010000300328a040103080041000004140c0c4011495100740b809200914040030140104100305800c04045185078000e1050003001440780500d10301681048a4035041d030310200d2020616200c1c0d0110307508000750001c0d00b600940c600030490b00045a030b04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 32687712 1250 32686462 32686477
    0xb1503010303230d0c0509041a0102150402030111030a0203040b0612030904110c030301031a010f030c030803090f0613020405010e04030507030f050d020f0903010c110c06070516060201090b0c 84
    0x260b010704503400300c8000301020103c41100d845000340341005045455045400401d0f100c4000b03803000c2030382034403400c0c2882000101126500302c912600c0460700000d41e5a1082d0760308002c4180e002c0040b404648094114410680442072066200e24007107a014000790411a02a90400b460001103030f5103080c90b02c2800c620702c4044000c1d40c45c01031602c0620025241c0e418030400164020032510810800920141d8047c51180360b42d44003000300b00c10b04428031141a0041825801001c50400006410843c1c2d0b10403603903c103402c0e40c1c0f41d9032000318160401203412481551805048108000761190f0150042d100c1c3c0b00300c4040140341d0f2500310603440c1c90030407100200400c004004c5c076408a801a000300c02031001030b141c02c0e85441400d1002c101a40c100744001c800740038002c610306419140c28000c40c101c0040e1031610300c03400e18a03020b000d591040d689519500403a070024101c0e09100092000c2e0302001541a15000001e546602c024000c0200c0d44050781c25044250201e00000c00140440380318 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 32688962 1250 32687712 32687717
    0xa08040b0a090804090b0102030c0115060801090608100c030b030604030918020306030c09040c0305030a030f050c18040c030b040204030b0105010806060711011b02090a050f09010b13050a0e07090b1503010303 91
    0x10315003041303080785c006d10290001e90b040d0300c4240a01640d00000740261301c496410070b49100919441e05801504035a810303000040c0c100d04246060020540002d022060f00210900114118803e800c0c158010885009110380502a54041005050b007102000045a03e00700c3e8020182000080708800c9000c240d9140f0f6050f0409181c0e80c51038078003a000d03190413034000e8841c92805a03582d034800340b540d03000c1c2d00170f480404d0f00d0f41c20b04c0314400c900d0311850b90b100c1000c0c0e80140ca0450034121000000d610007400500c01c56907080c031681800e210307601c20010301c9400b81045540d5034a90070445c40f582d03c00d00c40c082c00180710000042c40b50401c07405468141d9030000c00c014400d503139680150f4140d5480c54400c10b4081b0101c600c0405691444034642c0904c40603000040d450900007840c1c44941401040000241e040445121680c2c9508241c48998908210005255100c4203034000240240d100a00c0300c80c4503020001ca003450b0720740d000d140f11600850760a0002110f40381901c0d028042407002401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 32690212 1250 32688962 32688967
    0x30406090b071e0b070e0901080307020d0c051306050f030c090a020c0c040c080a06050105032404090501140709120b010302040902030a020604080d02060a02040305070612020409020a08040b0a0908 86
    0x45040094060302c641d07071098181e400c20701012208800b20040185064500d501e101d02030119494000861171980d04068070503408a40c10b00305150b6032846480802801101c12640c900140b2510038110006003c0c02040c00c04c001031500c0c04100a8042800f401c0c2c0b10305003445070041c6034680001c0c6070070240000703000f02c0c80c0356448034100707402504080000f140d00e00417108900500c3e45c03644203010584e000d80d00c0f00002810102e04220880c0ca86800031f5060020070000e000100c42d19140844504840f031940306101039900002c9800f03840c001b00700401740d6082c00d152480180029036114496411942c4001005a072000c0014802030749510180140c10440014809070406070820111940040c04555124809501050844e03006503c610342030f0304458402452a5414030a01c0e4205030a5107007503041908548445852f10054400e12080c0401041032468400b4580c0545008020705c1380110344403200c03e20003038224401228200d4020b0003e40c0040d5180026100f40c0f080c6542103040d00b030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 32691462 1250 32690212 32690219
    0x80c100f0302160b0a050601110322031a0f070203070f02090411090c03090709090b0708060a0315020301050108010603090c0e0711030f07050d0f0e090601030e0610080d0203040609 79
    0x214600c808120900405030200404030708504807070004480c2912803803111980c2d183c4031520307a00b01c86000d05214100300c000741c14481041000001d4640c03411048039030030f04a80c0560603500035000c4903800100050070420014990721101904035104044440200c04950b43d030460480c1c880c428860700a000460904100f805410540002988180320b14000c900b002c203488005510103d0450342c04540300c10010805c1207402c400e00c084001080c042c0005e0002c0780655440b0140c03011b0007010101002200340001e0569541c444081d0020340c1c12421b90b102c10b10702c009044010358400d0203410302107600c0e5000091403611034455604000c1d013203021010300c541080800020101c019091070700300100500c044c05904000e000504000154440c16a13645086190907410001005125001d2003103030f1000b40100341d000f80303e4403000241103604101c9607455070016402040f500078031102a01c501404c0000b03959001100800342c42c1c0703070411035400780004003089940e403049002d000c000888201c01003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 32692712 1250 32691462 32691467
    0x50c100c1502091207030302010b061201120317040f0303060b030601120c020c06180310020f0409050601020328022a04050406020910020a03090b0711091e01080d020106080c10 77
    0xc41d00c103104400545012010b100007184058003140450f0603030025a020400c164092241d0f10b0080307030581e106810501e40006030b20052005100340d80300300100c1c240303400030075106016407241d030300da40d03031154140d4101410400c108908042c8101c0c0806c2c909440410842c03a8203003a070744110704c140d4038078924a4a42030381c940a4042154590190310a00d0b201c040180c1c1c4403006080501c1016404000701160181007600e0501891508845180b04000304c40d928a001c1c1c04232000c0d5224824017107002e444140040345180304689800b603000d488446494640d114a1504800031701450b4200c54250110749045007400c5101c02d1440d0b03455203220810f6030f480c24950840e56000c1c1c000c107401030400b9085404240109910010400140c202c4c0c40e09a0805402031508800340c00446091400c10a907507a8041d010004042418400c049150010f180c030b0410007601404583c0d032540c96030310b6594a140d4a507544200144c41c40155081000202d245040043e43c5c3d034540340020222106041e81e400103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 32693962 1250 32692712 32692733
    0x5040c15080f150f12031c02030c090105300702060612030316090306020406050901020f0307020306011a0c011505100203030405120a05040801060f14040506010206150d0b09010207050c100c 83
    0x150084d40080d2015800d940d20103188082c0d82c660405140d4131300fa1010400c0c10b2014012040102903c107001b400704c8002e40301d09403010a2002e08009581d0501451100002c0761f840140406000e241110701e0400340101e030555014401b66000c441c200d4071060200451070030241c2c0f0381c01d125441400080d6041075074000d22440741689050000c1850b85a0700c804007664020b80156020800000b481301d4256410056103140d0102c500c05582045050b500003615004103108485080f101009104544816074045524010405008001c961009081451402401e2040c184111410500b06044a00110480c0e1089900c074014080d010002c05000940740c2015401008002c070920002c03c801100b4480c00024040700301440e06c81c0d901d410ba0981004554061721409030f400c20b03050040c0d51340c000a03501c0d00000740d680b0b221141c0c0210000b0540403d44614007a210194800074803000b2001035006003002030040041c1d411495a81092000e0b1b4014000d118000403200030701e40c4041251030b03c0f07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 32695212 1250 32693962 32694001
    0x6050a0e060d0b180610031b4202010906050a0608030904020a05210411060a0e01081b0d0203010f08010207050703110a0e04110108070f09060c0204090605040c15080f 73
    0x10800c10340e4480400203160060072186501c07004050103040c01484000b80c002200b0781800c0f12390301a00c50070300072440207050303681420758000001b1031064007000301440b00c800e07040c03510300000d8003000e0241d03038000b4040d080510042d54054030b0040420070040c0c580c0180b100340e90740304000b5440c05a02405100007944181c2a200c10442c081c00040b146036034440030803100c1340c2d00000a00ca01e08040c14403040c40e910400a1a20500c010013001041c540c105102c60b040042c00d00302b8120b42d54500140d8056031003188400c0e000103100042d01071400049601840c10380b50b00c40d00c10008540c0b1a08281d080784940c07040030740303998005078081000695900c8049600100a40300140c215a56045030340840300c280c3e01100e0f041900310300014a1350f80628415070040c414035020b40d8844082074040e0400c03485000d260300f00180c0202131420340d2502d03044071060544c0940100007074a814106440e41349024001d404181513440c203140001e82c81900218000ca007520904600d5848585090400084140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 32696462 1250 32695212 32695231
    0x50d0204030b0f07030c0503060d020f010e040518010f0b22090f060209180f07110307050d02060403090602030702060d020702030109060603080a020708121b1002040906050a0e060d0b 80
    0x201000281e922050b0500884408828148500b0400d0015040e1401a40141c0030820140f0402c0841c0e81ca50742070041580d01941c071145a1500380d001242c7c600000d010301c0346c0081c02d02c010b210300c02051150b40729810b44004020899609491241d806440009000540c41031031244106240089886050003181c1c607684001161400b60346c9040c0d40c9020703584107407030342c07940441c480300d047c10f0800b00d291a4501c50401721490741b4001c0c081c9240505c0107800081040b04180000050903010800c0301c028580101c1214200e505e00b1134000e40e0791808940c2140040c1e90f0120000380310b4000025251050350062046041c050014011402508000b00990b490340d20340722101d001c03d6640c49080051030140d01080d65401450502924010f025402801680d01c184044e41c1708031a117100752607000000490104940d4038a90701507150004c0c1c0034910036603901c0003030000b0702281030b540301030704455054400ea052150b4910320000c20354421551103800010110461000500402000e54010100c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 32697712 1250 32696462 32696467
    0x11010207180f0506010c05070303121104030b09070b030903040506090a1203020105070306050604050a120c0302090106080907060e01051603050d1e0b0a03470f01080c0a0303050d02 79
    0x120001044000d0814021200c50342d15005140710b03529078080c0f00e03440381c000c2c00c050840c1610740d65a01c0e030740c43e00c621001c1c0420459200c800040140d039041140000b00400c074035500e8603145e00741544207080942d40c04003e441031a000040624403c4250f07072081e002c45c8082e41c02c09150900740b207069070140703c141c1d601020703034000450031101c40201007040074001c0d40002142d181055000e41140c02a40100f8480c05c410300c000c10065480c0c90040080d0780002c0080c0c02c2c0240e0508d0260700401540e000294080118400407500f164070800b8140304900c2c0400b1112084d0750341a05403204810b0882c3c0f140000c0e800c20442030011248820112070b00c1c0300e850000e1501034050510780440d22011026240604000d0500c030501041e4020b00b824400c0c00c54044480b1403031a40d40c0303001c20308a00c60400429004000c150303c407052003c903d8204941480c0f20303400c9c4600c501110701d25070ba0110782d508030b022030000020030002e00004005181c4c050240a070041d46003951829201c1e504030302c0300158840c0d000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 32698962 1250 32697712 32697719
    0x30504030210020409020a0306170a02130f050106080405120703080f061201020c0a0c0806072003040e010306050a050a0506010f030905010605060c0a031409010503040605060d051518060f010311010207 88
    0x182d1006000070907100078016145d45070600003d040d09c010742d00011082031940164180c0b1000420b10318580b41d03044417581d1040c0b80c1401c810000e080c03c1151038070f07036500c0d1200002d41a5080f06059204a21a209075441c1140704120030110f4003603040003800180c1e8910000b01d00502280d0315507040792000303042006406401071200d0070780e8458034204a09400ca00039940030800c0c247d12400203030100c00080c040d203282403140140308500141c3e202c2e9144420082940c2d01c0007080c401ca801401940c1182a06503840e4100000035180580d0100e03903491504002500c04080c82c8103640c05542e0507581c042151245100c110702402ca00c080969080d5aa00d500250980d42c15005001c1c41c0b00f00ca001d0540e00801c1d05000d400001400f401d6104210304125501203030f030b40501183c1e03029902c00c5000405c0c1e08c42002044007290300c504010142d1141c01d1080750a03104001e10244140c480d21440c0070740300300c0300380c00c2912484203071401055a28801d0050000840350300b04c099241070f040c0704880844d5030303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 32700212 1250 32698962 32698993
    0x70b041103060a06050a0614091011071203090806040b06010831050607020609030301060c06110310030501060605120a05061203040e0109060b07080712051e0910030b0607030305040302 81
    0x40d10b00f400c0b034136640c1004004605003072148100510303050034601802915220741003110b104030801c040c41a00044038080d405400390410a0804e4018412540c000e074176240031011313100340060180c3c00b06d0b102900000c0c0d05440066150300c80c0f50f000f03c94036a1a180e240040d00e28900c050000c0941f114542110082075004040e810385520040020300130b10145410b0141c00c04001500300c50440d0014002c109000400004a1741110428a0005e0744140c4030b081034030040550100d80301d540c1a002046c41003925100541009030b90091000b0040f2540e2100c09413094401c4141c85050b00c481f650024003101142d911043d8040d801400391120b600c010b2a525003194455009003a070a02450014800b69110f4820a000b5100394a10300340ba14451362649000c1d4003030400c006020b9861007030050039040c823942c252036004280168561500f28011108240f81d00a0703a41c043c02250405c03401c446140c4039004003110400050001031030542c0e603803022005424000d1051b400d500c10700c070880319080ea = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 32701462 1250 32700212 32700223
    0xf020c0f06040b070905030601140a0f06020c03010b0603010f05060309070b0703081609031703070908030a020a0303050a090f12090810020307030b01020c0105040915050a03050c0306011a070b041103 87
    0x2030020301600c024074191900752511040603014004010144105000b01e4800007441e505490401d41003903500740c2c003030000586d0301010b03070422100d000d506400020056000246c1c81c00300d0f0021030007404060041428401e49000074415503441d5841002c08005509001d0300560b046100c20080c0e80d0000d03103c22103114135501c00c3c0012000500d140d410861115a50f9404034440c81c22440e0655066107180c5680034202e03a0205180207401d400004903080e54041c402c080000d1840768262620307401c00c91006501c038484404150080790608000854000c00b620462100940c0455800182d9034142c40e2402802842c074405814031404440103c4c840d0010007280d84000c61001d03001d607407880e211100030141d0b9404907405041d540084c0450106a8021091701c05980504800249006001210141c80503181d0700698106c40750302408814007001291625100c24282c040f15180d03680d41c641580e1284584010001e14003080c4500310010340150241d07900203000b0000d0310401e900f254002030501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 32702712 1250 32701462 32701483
    0xa0b01180608071101110f0c030c0703050303090f03090a03060209030a051006090e191104091b06170c04140d0b09070503100c081f1502030901030f0209010f030f020c 73
    0x782c082010007038035a9018400304594440100203000741020301c2c240d88828040e89000004001c2c02160805007030a00b0005d0300d04011510080321000c60303481c03c002e5180c2e072060701e03503001600a0481e043c984905c004100c5078035142c05442201303982c1ca180c0b2000000c0d00420041c0760316029500e03820000c00d85c20000d010145210440c0020164a0254004105c070a500c002804980204000000701c01001c00315202c2c5507084003c1c1d1901d1600d43c8001001403451500007820245070561000044071406803040c280c811644440015014482204400b054111900000744004000901c641d200008600c2c02500003e401d24540386802d13681d0000ca80340845651000c1e0340040410801e034502004007a0307c05401c1402000714a801d005d00820303040d0024807885e81080b402a0711103045c0d00307030021b00000b8806c500740241041c51645000f51642d02c814000c03030010781407403041d5104118510840311110016140c0d00f0740085041c4095000d4100340100b50708440c1c4c02c1c408030960113401d004d9602030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 32703962 1250 32702712 32702717
    0xe13020721020705040b0904030c02060918060907090509010b0d06090c0203070c051509040902030307080f03040c050303040b03180f071203021605090708090c0a0603051501020a08030a0b011806 85
    0x311007030528000c0c40c115007076200b14031460400c000c0310482d481e0f149030290095050304c0e0a040111803070000c20928440c04200070b800010105040110301e5502030500d00500c012124a4084d0319a42c0d400c48a6038a94001c081d8881e01d2600104403019040c4000c0c1803803440c140740440c007103540d804500d0460300003a5541025810000303d1000f0840c00101c00006040c2c2113504480c940b141c01502241d07802a4549603005a645604040540d1344c01c0054881041d4010301c03544d510442c2c00d84180f41c54100386e90440304d0004003403000c5100d103404000c0d10155412004074070b086659260300701c0030111503140e15100c50b000d4a907020580340c80c10310260010309201d00b05103100380c0c8035280007850b052030b103031400d40300d55001103040c0103075510800e00c66000020740c030708076000d40c60389100c96040000124803a40c3c801e072001c03800240107800d500410702c00c0320310340d2010103840d40b07000040e80c035900c1082c00141042006c000007210010b1903401003e00f0f507010f240628070b4403858207491580006542040c000f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 32705212 1250 32703962 32704013
    0x151401050907020d0e060c0a0b01060306080709050c0d05041406040305132301030c180f1a03040b07210608030903010e07060c020409020105070b0a0501140a060e130207 74
    0x20500380701501541100c0d003407008180400001c0401016070540c094002d104240010701046141e00c08c001101605030010b61044540d6520000900140b010780309200c414080c41d4000a07506960340f0941d80308054942c9020f06d000b0211100c83c004140003007003120b900c01001c4021006020400031030b40300b00c1c466180c0540e40c0614546811103403103c0d500030030714802c82c0340d681400402005980e20482800b0708002c03c11303c08103402520a00c101365280840a540f18030001102e03400e141c402c41c110b8141001e1110850013030740d41e0150601c01164090024008000130407481ca00c140e00c4001c0101e04d011080c00d2101d85e0b490a1030a4981c9a404002c081c0c0c000302d800c0003540b40a01c9406102c807800e030010001d1514101d4080d04c000d82000e00644903503660304441d0192790080d000c8a44d840d5010814181525140070b0020040030203003d00007500c12141d41160503400c107100e0b028143c84190301c805000c924194204803900000c07c2d15440c9254003882503100045140030f9407052849010340c2c0c40e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 32706462 1250 32705212 32705219
    0x5060901050603061f030206030703060509040c0501080c0304020d1103010209060d060801060501020a020a0317071202010f0f180b150409031e090b0a030c09030516030b09010507021504151401 84
    0x10b2400030064000070380f005c1aa88060003981c030091342c800031a40d045c0c0b441600c03a96200f209070020281688a1500100d001003000100f101b001000e00654009890310300e466111840b4040050104480007034200842c48a110f01141e03840340e207096844001400545000701c41004229160040e2a14401c1c41e501d40c0c40500a0350028003030000602420710051541c0003039600080d0211400d440043d00922560200000541070030381220411a080388802e82c03520b14400009009003006903006a07414509030307031118400154051429480341a4006030300c0c841c85505c1350f8100c1000500060032400a0401c0c50032503840303c2c0104401c09000752183c0e501941c00d601c40d101d44100d5002d0304000c0110400c418808040c114080c0c1c0e0904e0104e1400040c50503e08006503517100c4079400c083c106104103034203140e1503402107000e0340503244581410070607510f9100c0541d003614025a50f0f03d0160300100400e07091079400503031060b8424090810030381c5055200e2100070850b03503040c01c2100849202b00051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 32707712 1250 32706462 32706469
    0x40603021c05060319060b061b0d020615010e010c020405011202090c0a080a0e150a0507022802010e061b03070b071b0209060402040b0f07020a0f0806150409050609010506 75
    0x740700052656105108610706100001d848804071001812200f042d4101c507018800c980d4001c604148000e8403555075484140010b01c2403d10842010559104a001d000d40302d81c404101180681d0040300301c09800c000300801540d01d02d54110003281004014001710015966500440d40286003005446198003540d00501420b05001010300da1011010031080381ea040d80554680da0182e42b51400080d1450725452150520400c002402c0a102000c024056040d1960b802140154160713001c0350703440364800f0308520050702118058400c03140140203410155020b101404c007d00c000a182918201400c405140d10000305d5454a42d1688003080c80d0b030801060080c0141c01108900341440030408480c0350814030600e0510090007880309034041125070321640c0546014220800780181c49140c80c48011040ba044400b05900c6031451440c0003407045030a010490070f440c0844080d1080d503030740035a40305039140031601d41d03a0881d55410419021130700600c5101e01500203803002103880d080c14400c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 32708962 1250 32707712 32707747
    0x50103080a03180b040f0f06020a030b04150807170106080a20011e20190b07091a0903120304054209070323070e150d060b040204060302 60
    0x119061803851508050208508010250380140e1040500c90040c0b043e00e0207947d00401c0840041240340013041450500380c240e00207220110040e00d0400c900d815040c0d009001c0300ca84e214000795a04524003d1040c2c0403001110380302d03401c0100010600f19918000c040c42c00034040815120b000c40003c034055050580a41c0040310503092901c40040003403846003410030650780c008902800540710500c038001c0a1403041e1589083c03140709889010700c05903403000b10020f07411402c81c0c9160588001800c0c0c3c44c0900000d2043c3d031410709a030543d1024441603070b41150301c054003041e4140720700e07544540002a100e0003148200d200340c0c0904503138003d80100300d11100c18941c2c0a80e10140944200340413080c50030b107182418540304518070030fa4541d0826141001500d0300003030010005a00d0300c00d10410044110308518a026045401ca60350720300b031000b4203070300036148202044039109820301c2c01d14282034280901c2d0b0041c100016004100000202240d20550120b00401c0d00452100581e200400c403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 32710212 1250 32708962 32708981
    0x30506070c1a011802030402010327050c1002070e15060a09060f0e060d020a140703020604030212070210080403020115060f02070b070b0a02070804030609080310080d0c030302030712050103080a03 86
    0x5402c241c0b5410032290214156200351055000d643c04000101568800c0d000080c102c00402103118030354821442104240034951401d80e4a8419105541424200020444800c1d4603990240070818244100380c1003607070010f0800e43c4642d03000f4040081e203076034140040c1104c600984524001c0c914061019044001e40405802440604541441c3e5610340e1000c49405032980c500040c0c0d607100400083e40c031141007042c18a8106804588401016000100c050241d4041d800f05d0701c0007010f00203031a1040c460118020742003020007003001c1845003d2180e41d50424480d000106004402680c02041c1084039400840058242c61b040408907030140450710142406402c2c3c189080015210403590080c060144a91590700040020030705c40d007107050303e02035580f08400b440030180c2414105001d4100b0764052610031352580002032607150020340201c03090343c251110b40480d00341e0b03103042e0025003008002c2020300c448104d04041159052190a010358802d14585442d00400503004048500204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 32711462 1250 32710212 32710253
    0x1090204110a08040b0720070501171b07080c0303070f09080106030b060607020307080f030702090a06060807030c0302041a03010e09070b03160309020411090405060102010513020415030506070c 85
    0x410031120300c0d400a0384660164110481502c2a01c0d4a9011695006800600c100180c11f0503090741140d180441d1003000c4800076078407000054147e100d050b100381003c0ea40d541c8031552200c030310b00740c2902c404040d003441401400c0700e904000d04014030314110b50044810b4000980d9a004c0800c0701a0407502e514040c0130040020807045055913200c070360040c0c0150406101d10400b0900da01199410400c940240120100391a40d080c07008181a5403a04410001c030f200d00513010019032078000910550089882a41e00d401d1180c440300c0080c0c00401001e01100100343d020440480c000243c001445c00800c00c0600c0300c0e03070340e61500300380550344000038044171040c0d000458100816449882030f00d0700a082160144018080c282082e8002c0440d00d0b17009400508140901c41903100d0300010f07040c040815181403003640e460300012070072103204807007a07103100c41c9484212001d4103083d8410088413036901d210b03043d1180c8ac1d17103801d85818400c403042000200300901e203900f08101804140d2051350b61740c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 32712712 1250 32711462 32711467
    0x7051f0207170705041a0d050f0c01030b06030106050706060905010b0403020405091501030210110106170c0a081009080403150203060a06140409020a020118060606180e0402120a06020307020109020411 88
    0x214000c1d183c011610446204070740b41e0410121103034814074124003d04005004615070010303450402e8690800000074a401e0080c003014206950090051003000c0f18020130382c0f460341e0f0908a0a6845400c050001e0f500143d40d044085220f661030b2240300e01030000380284035250341c40c501c10131013510001403402400342c210741d461600100d4003c10390b50640340c0c12606004a071314158000c1700d16911004000941e50700b00140011505261b10000c508a801c02003698400101101400324008031485150313455840b50021416103011940403074103547c03003100010320700340c0d0f00d03180d00c0c0b00480d0f0040742c8818280d001041c03022900d40312040384001c018508000700e2100700100d03200030f00d02072440380c16071140e0005200d0740801d100303500c0840c000400f01e60a0a46680c2da0a1000040c03103a409200081900540c540385501e00480740e403001c035101441d0300402942c6550901c03612108424040c41075202d00c4014000080b603a001851051400f540000b402c11094010442550325030714401c041082c08 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 32713962 1250 32712712 32712749
    0x1b0102031b070c0e0402031002070309031a071202130b0c0c0109170703020904020604080610050301050a0213050d080405060d020309060606070b0403110f030a030608060f06010f0305060307051f0207 87
    0x18284402199915404c0d814280e5136800442c0c2812301e040c0d080640703030b1720004001040513000318100e02aa4041e0324030800400692440d03855486c8140c0e2030401142021010454441042d0028404441e01c1c00d83e40184558460408400d40c20419048a103034112691203505568041c1f20700c0005c0642c003e007164082041078445460300c00b1400007038003c200e2000010299255031007114010a102000c0315036a181c030b03424050740c0c201d043c002d035407107942070074003007035005e802c6009440402d10004c144915030b5103080d04001c00980e038010b0888840009000000d4141c0d90000a04400144070002507a41c0c42c00e51a094140003009000c1071280390140007040103d00550340a43d40254141001440d0b0b01c88101d000e40350404080940c88207101c001410340e00d0607455000341e41154000d5040f24900e40340c00c0b18030210322104498090028907280c1034140b4484c030940246812100150035601815200c0001c580c840b106030080a680c035507a42111040f0642c10854a0018000c00041d14040541c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 32715212 1250 32713962 32713973
    0x4030308010b030411090408030f06030106050f061b0d0207090c080c0a0516080a0507020102280201050703051e18010905060405060d0b19031b030c0306111b0102031b07 74
    0x5040c020402c0c003039070200020f020045000e400908803080240001440d00d0140f400c2405940300310340750300c12581500d000c82c5441c2414090b00341541e0700148101d1320348803038400f8401c6981190a840388810040c07d420324401606000048a02c103142e805483c560303003010301034000e6924001c50102003101000c108800c516108081d03030041002f5180196450312030103240b00000c405d07520003402c90000002c01e1905150820b0007045010300c04e0b000e035084540341e0b549801c941c0c8130340c42a035035041000400c85401903100782c0007071803280e1080c00c01509040c0002c0f02c000b501075014005240b071070340000c1d542c00c04008050850000301800d01c0d0600c044c60415010400703078000c5220381c0b030003200086800f00c055100ca811500d240d0502410070290b602c488007051620600c40c0c40f040d02c1c540304078078042c0703440394401c011a002c2e260007001005010785160307140e1005002404c40e041c100c4505104800c0140e00c0b052888240300c4020002507200c0c10310700e0343c0d0b502c07400c083d501c21110400c041003048001803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 32716462 1250 32715212 32715227
    0x50f090d0f0c150e01050619030506010e0718080607030524011202070204050a09020f010c08030415060e0a050106120905070905060616060e011d03070210020f010e030d11040303 78
    0x501d1030311181c1c0000320700e40540c03421100c1c03543c0725465042035a9000c01843c1540958410712040302d21708100d0b00d00c51034200d444210750102400a800c4100103000c00c4082814070307038008900d403401d0350301c281072040c02a003a0500c41e0014592904140103200b20b5a5160240032b410032100100c003981040303100d40c2241c08a0001c41300606204e4007064907103020a4590503149180c2c2c000e4818403042c9060300908005040540080f4801e42200c40d00401c0c1d94469203d64180076400076200d413464a0b15140c114800b022081c43c0c0c0c1c1c40d9034036500003007400c810042d0650301a4580f0400400c4550410902074076114206802e00300c014a01404140810700c00240342c0700308c80010000080c00c0d1524030210b0120321802c83c000c3d00e1030007000110307010032115911525840c10400b000300b11190150030111390038618490055003e5001b440a1409850850004ca00c0e0104c2d81c0100d5800421f8420300c03e003981e0080740c464110303400c04140c0c2100001280500309030041055100d925003400c5507000352204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 32717712 1250 32716462 32716487
    0x20301140909190c081005010306060603090c03060506031c0e030607030c0504120516080d03060503010519020c0709050c04060311040501050703051b03070f03031a090a0b0310050103030201050f090d 87
    0x3445414a180f0501201300142d40180c8226070948103410710b4032402101500080c802150340d00e00e82103000840c1c52180c4a00e1007019444070780d0003001459078446002910020780480d074103014019110003141d8007045001a0000d8940761045959000300400d41844c500500c0d1005042c20b02000241c0581e00008940503503258850000250b003240c02c0c014034200c1040c00305000300410a002046010001801100720030b000d40e02404519290424103080c1d0b10203039580221280810040d50320807400390003400d4041d002108a81c0030030754030301000e8242da070280c0310b40041d030a000606202a0b54940190100c84d00c0400580e49400d281c0b1000a00318170480f0070150420602164103c8944ad0040c512500072500104880d00e61045040c24000b02d5001d040c11000300740380c101803403c031640d50f410442c0f00f960300401143e1581d0341c0303410107405440d2081c100d541c58003542100d0841d150803413060901a50080e400000c2034902200643c080344005881800d20307900c141c0f0f5808505621940d09000c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 32718962 1250 32717712 32717743
    0x40f090b0610050705070f170705061c0b100519030207082a12040f060e01020c0103110d05040f02040b030f06160507050102121b07080d0c0e06030901020301140909 72
    0x982d103840c00101c03981d010700c00300200319002c1d0030000500c034240f60f0141800e807002003030711013101c0400c072442c2a0f6401e41c500c2441c0c0c01c03290034000031035400c82c1c034405402000d5451801103405120380c00000c582e030b00002c8411011a0000c125582495080c030056a080c0c480340c2011031a0206a40301d040d120300810100400c20b02401034a03016602ca0b00c2912076528540740102c0d9001c0b514203140100d584c0150151409602c10020300003440d51140b494505c090788182c004e4034042c000800110f001d0121210489000c000400030500b44c041e8501ca150300c50340c00b95100c0140c0580510400050781e600ea8217161007075000d041c0c08800c01c20082241d94000059510040210b040140240d915000300c0f40c0180070ba51000c1003040f051421484401c1c4546803100902950b2000f0b0700005056001d55200607009440a005a0b56182c0166002e08030340c500f94100b44c0320307a600b001c000400c0d03a40116a96103041c0d401200402002c1307a034204014040008450403e01450442c101560391091031503402c1c1c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 32720212 1250 32718962 32718979
    0x309090b040225031b0b06040903031506030b0a08030f031807090509030a0e0a121119030c030303050a02040b0306011b0804080a0b1806010e0c0c030d0b040f090b06 72
    0x500d41da41c1d9044030708999144500910042c01101c036420044a100340c164080b907017007540041e00d202c0905201e0303105540140100450744551091000900d08400c044081c155680c9000c1220100c49440d08000c0c0950759000ca101b41e01481801443e00b0582d0200006500c140300ca050990060415660300150480d10b402d42000101052481c0c0707182e130752203c0d1206160070103104200e03401000502140801e07840d035004031816582070000c101000d21030103102c81c0a962100d00001d0701c21a203034040c1240103040d0f000d042c3d950b4928000c070300e41980c011103694810480400801d9054000e095102d46207000450500340380004800040c0700c003d103807904008120702100c1491010155000105401c280440c0d103e03519064040e5035402c058205071040303240f00001403051b003200100318220b501d1800c06840240d107401564000c8505c00740c02118403404c00e100c000d0726800204081d2920070001d010105200009005000845000070800b25606080020100114008554681d0003442c182d07421034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 32721462 1250 32720212 32720231
    0x506040512120406050417070602030d090f02100302030702070807080a020d0f0b18011109060403030f020a05030307030605120a0201020c060a0909050103060506090f09070303050a17070c030f020307030909 90
    0x70b0401200c1c108802d01480041008204144e0001c040d00540d12542e030304000100407095020395402c00c40c8200001070340300b0800e410300048590403c0318903a1040306c000c60411102d500052800c5151040703000000e034040f082100140c0e0405c01080104040c0003d04446130030082c4860311600e81c0d4230701a00440b4250100002c10420400031880309422401d07908203414020054030081c3d1160000008560034000d0010501c03500e00d00310b5a54280c02400d81d80340a1866500740c0b801c1e01c04404503010b5008111800f008144180000e51180d513256030005241c604150400500400d2070345645001d03800541142c0050740c0009001001581c115602502c13804880b404680195098008a01c498104400042008415040103001e5081140c50f101c40d940c4582060b007040204a922070441d6201240c1040468013a10081601204910742000140801d038000b0f040030310242d54010000b41d062100509065116140b808504035602c0554a030204a44009141c44058000ca820740c5030340c0d040f40c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 32722712 1250 32721462 32721499
    0x3070509010315050c0d050907090b01031103010509070504050907030e0d0c030507110307050307140f010c0218060f04020c16080f030d02030c040510050406110616030209030f010e0d09090605060405 87
    0x146c10b214820102031040d8505071424a84505062107002c4455041628ad43c4803903002f40a001001003030020200d007160f18084c104114410040c09030320a0041c104408145c6417a80e5041c5c80c802c0415440200360030190386405440d0036030601341d407401c110540d603031800083e030b001c81180c0020f9081007103810b010b00382c03800080c24401c3c2c40c0e01150f458170840000281c00f4040140103080079a048070119803180d51100192100c545a600007903200c000001c140d195002d4034544c558101c10b000d80384004118000b4040b8041740c0c009021540d2507408210040c600700c10050b680030142031440c003e001c0c910b0144040e00d540e405214400540c050700440050400c00d40b44080e20020840101111a60485604098607a0b4420b004030b40000345031581030005418002000c0d8012105a4040f0051020189048000750042c1d04480e50500030b564008954081c03d00407203030800f40000140003c016910806055502554096082c3c941007100070071956a411050318100c42c01030b5011b07150600f100046 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 32723962 1250 32722712 32722717
    0x20304030e030f0d020c06160201080702010209040908280806010318061a0108090a030c0f0f0209070332060105071b080a060c0302070b040215040806090c03070509010315050c 77
    0xc0b60184501a00c0104205000405a40c070130190303001c2d6a4800e0b41074040c002a88154108410903000d00342822005520400260f42d01c26686c2c40014100b00106000400b6035001e0340060b20070b503d010400c16811a10f0146003100a5030074554400340810040d0085c4c010800184803906142d940c46072a0000c0c1c0b00008404041c5030310107010040c4294102a00d020342801b19070403030000d12207100103180203c002a0400d00c0c16055101d40c020018541e80d0004251905002100c0c0c0610b0b100c1040010b0701c9030400980204000d4170003080440503460848200001c0c2c01c080404090507005001145401041c01a000b1100780780540c0d03591554200520511240140e06203c00c6000c900051030800c08103514101c0c07407055905000a00c4034660840c185d0141c550007415031042200030400615007070300b04952100b100441207003815541e6402604000e0300f22007203901c540024040b05200c7c5010f00c4907030051b103002c07644500154116210103d030b000141098810f855a610003181450a0382c005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 32725212 1250 32723962 32723987
    0x7080f0709081212070207030b0a0c031119021603020a120206070b07110705060414011d0d050a0b0109110403060203040606050a06020a120201020306030c0d080c1e0d09050105090402030403 83
    0x2103499070140c0c0c6110f004290300c209246403c00d401c9002040d60184082505070880c0c3d0052100189501c0e5540c0300b200408402504001740b650700e00009007c50042c001134805100b0b00469610310345039460002c1d0034000c1140385501001c3c010002030006903a40a152001c1d1072030010402c124610920228030240f2a11901030640040c081c100050603a02100b1002c3c07140350b410648002079642c20a00901b80503500601120322102c0c0e102100c030354840c1440019141502c09800d80d0f201032013010801d1b40c010304900780c9154201c00c0150003802011440c0500511244d2400c00c55076a80f0046509030740194000189a590000f0200703042c0081c030742102010700002410b024200da034504020395900320ba110111480e00010322282242801842a80c0c450352028010f00b0030901c0b00c000b08002010010001c4604000500034200c84d8003080046410426a50880900b9181808200b92901da00140e2190402c188000188110b9900c2019a20004400e503009030b00c5e40c03180d1506942440e40c450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 32726462 1250 32725212 32725229
    0x70e0c0f04030503130e10050418140c0918030a1b0206040b040801051503060c0a0207090e01020903070b0a0e06090d0506090c18040c0b0c0304080303010803040f080607080f0709 78
    0xa010042c48404001000617650290001c0413081e90f5a020b80744140c4104c60159008400080400c0301e8140b6410a8610151420101580c1e04c1599501c07102801d06015a030340c5c41d0305c942e801101c5410800002c51300035060082500741d03d02c02c48403c0d640c1b0712901c440c40c001c0152a0043c0c100490603014a13030f40303907a4002c0c4802e84032074480071880e601d40c01501c61026a0340c2800040b8074840f4442c2c1c800040424058060149591405604a030725407040000d102148221503001905803200c2c400d805501102d1070025942c0c038020410980b921101d41c02c079444e0303000100031020585030002000503402c3c0c8140c0c4c10507103c092071000a00200700d0200d000c0c046009010800c030484201040300d4031039107000c48452100422108001c03c4921007246c000b0401017a40e4014080c0111400c0500300c0d5880700001c40b85807a455022103030442c2c2003a4030456a5a0020605120707503401400c0d900081d21103800101500d141c08440204401b602406205040705182c001c1903c061240d240d94001e08513a2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 32727712 1250 32726462 32726467
    0x50706020412020112021c0522050703020a06051207030504020f0910030c0b04050105221208040e0c031603090c0906060e0909120a1b0f030206040606060201060602070e0c0f 76
    0x207494640c10089002d01c100e001903151507035011100207500c05c2d20018000c004480c8110484080804010040a401100c49010005054200da01303c3c1c000c1014440c40345c40545051851481888004a400d810040c244101404809014500003074099030221513071a0100701c0e501c69001080940d1180c0b030201b0380105c0c00508115844902d01e0490703040f03078031403030303c40385180c1e56051424200e01850203000c0c005181040041d03155002026007800d4501036010780314640d60354003e6000102b991000895070389401080400101394500c40f0300d5445048a0480e628514010003100c00c1864400030000c141075588881006011610204201500d203220080062903101c1001038a00210000058402c10315800003841590300441e8a0602ca030700740c1082e42c02c10101d01c01c2661045140f4080c200010744000300078012030040c04501104034000d4002c5d02c0b00c0c4c180360a00e8019900b180c0c1280707066a042031030804c001540012600102c80104810183d0350301c2d80c03c220006403103881eaa05100c420013 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 32728962 1250 32727712 32727719
    0x306090b07090819060207081308070603050c1305061e0309100b0409020105030123100f030c02060103050706050c10090c0f0f0509010902031e04060518060f0103060c0507060204 78
    0xc04142030181c000c0352500d120541d6111855940c600805203118a1082c100760f030f4000180701c91300078002c0c04d03101e0543c0600b4140107119003118401c0a50242d64280d00494040000f640c140c40f406800c4540104a40d140c0401a850342240300268490305020b200c0008541800054010182c0c01c20002c1e44066030340d07410300d9000b141d81e81400d03c2142e44050f107001105d081900d094460200d900f0350684905086a00c0d014140d1040b2010741c0c0001140111503008040650740d4408005a0300705985a402401d044104000c040350340d5076044406550100c0018008608001106c0c03003100c00520300241d41308908904c00303040601c42c09140e24050305110001c41048a22552102910001c001d54801d0070780d140d10040d251462481090782250342c010050025914540003180c1c048560484c120440c20b2082c20300049143c2110b095039003d80d47d0060100801030300c03450110644000d0010030650804203031700c12480c1e10602c4006d000036070358280180b0841c064400d484440d0b402072002c54072680d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 32730212 1250 32728962 32728973
    0x30e060d0614150c060106081306090602072f0405060402070506010e1b0307090b0711180907060c0308060d030216031a0705030c09090703150803180d02090a090309030609 75
    0x100703210300352044064016005078001e4240546000061303050041c441d076481c00034140c030011005030006203034003442803040010441c03500840840724800c4000503034401ca41c1c02d10900d25661100c26010028002207000c5002042401452183c80c08480c0050f4607200c410019000b407280300e0005101d8008c103000041da1480c2480424414195000f090111600400110717480f03210894440001c100105000d004480ca01409090071a1144e60405900400e5200140320204030040c0c100829640d5400c00440074014000c04004200c01d007424085120159009488403000034011409521364100c40d070305052007000b4002c20045d9601201580c00d8076418614402400f00d0144901c00318100040b42e1020322440072207210380d04120007281000c6400d13081000c12000682040c04150305c43c10429255101c1000d032000074004c100c01140c1c0c8120035614000706001459400340701e0305411880750050f80b901c600d01035001c0d0002c07a001131181001d1509a0b882240c036000600850314008060b000c009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 32731462 1250 32730212 32730239
    0x609030a060e0c030309030d0f02030d0203160f03020c0307080d110703051201060207030b0610020f010507030c09050a0b091003090602070609031e050a1103040909030201290d030e060d06 82
    0x42c5041d00b5107400035409014135580f81300d441035141c0c05520044200c81045c2c81110080c00e03402051040d00d240c16aa81031520a980040c1e44101409450001072880c0603048444003040340d0703050405500b0500c02048440d128000c03154094015000001c07002c000c102a54420340c50101d0745080b05807903032814100240560000401c00c014858401c001184580c0000343d5801100c5d4080c01c00703c01039035000103100c00b5402c851120400e600c9021030640c0d00700700030300585200d02a140c4c2d001499420341d210042038000740b0f0384694002c100d100c41c00d0100c0780c141c00440e0b0006034190383d40c8040c4c40b80c191085004002d040e101405281c03010800d01d0410120790482d1a02034040e59600c25540b0007181c80030044030780380c02503901148080080700440c80c0601f0224445616100c280c82c14982d664004a0070344496410480c011707591028000e40e11055050f65540b2607040c414540403045441c0040b40800151540150a128204109c403c403691000308441c10300013064420b000041e07461880403140c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 32732712 1250 32731462 32731481
    0x32613080304180e070b07050c030d0206101703070206070c08030403060207020916020c040b180c07050d050a0905010c020a0306090b04020f0103090209060904020d0f030e100e03060f060609030a06 86
    0x2aa040e1410100c1c0003203d001d0790b41c130740d44030b030000c1d00c4010701d400c0d60700c480c651000b1000c98041c0116400c1400a513010300507010900081d4010b005e40d071824002c425284043c0d80c01c84010b509550f10307400003002c000002c5d11a82503040d6011650380d42c590030801c0b4020f410f40d00c00784480c840010080100010394002d000301078426286200311341c0b0791111101488952056402c0164400706402c891858150000c02900c540940a01400c600c0384a08880e18082110300d404080b03030000d0b00608220f42004510001c0807989881400c00e00c8001e4020134140c190312645040040c101b81080a554500c50000011035202000700140c5d401841d03c4640410101c4081e445110038035103e108950190040b840c1c0350340d00401c1303440661703a41d90400100d100007400070b80e0001950403000b0002200d034144400c83d64060780740c1c030550011540030000c201032400900e0313040180ca000400b905403000550203030004441c221040c0540d4031900465254020302d080035905116510400d0244016684000e00d01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 32733818 1106 32732712 32732729
    0x60f0604090504050c03070b1902100203040f020108060a050f04050414030310031209060c06020c120a0e01020105100503120a0201110a0f020c0406032613080304 71
    0x50342158020158541d03039441440140320013000080c2042c00700b02d00078440b40c0e08140780c02e16103010300700c800401d00213611617034904039009002400c01c0b800041c50840d10b80c80c1a00f402003181902c208140d001c2100e060105a82d41000c660300170558202401800000180d9000d000041600400540c0c001416120001c44240c0c180b004501441c0095101c4d07a959055080c0340060040407098101480800c090800405804c01c091040c03071600000d0068890382c0720240759043c009643e011101081000829a204030307009194401e0004083c1d008101c00e44e5420500d42003012107004055040d48080500d42841200074001c01c000382441c80003140891900d03080314100c4c0c00c60b0110301c001c255425a4400b11a03410405085006d008540034001180780d52918500a50f080e15540c0c60803c4140c601e0082050f02021070304840c000c2c404420490350790700061030b200e0300b00b030040c040d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 32553962 32733818 := by
  have h0 := BRFrame.cov_init 32553962
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32553962 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 32553962 ≤ n) (h2 : n < 32733818) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
