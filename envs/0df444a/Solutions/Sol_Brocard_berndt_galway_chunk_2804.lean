-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2804
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:47:09.861984+00:00
-- url     : https://prove2.me/submissions/23e3ba4c-58d4-4140-b5d9-79e5cac59e09

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 504136690 ≤ n < 504316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 504137940 1250 504136690 504136777
    0x4150306081e0313030803040b070801210309051302070b0606030c0d0207050c040e030a03051e0f040f0605070f020106050d0b06060d1401060e10090305120d0f02 71
    0x1010441c10200240c0e50b501070300358004803140594485001451803003a0704000324080e0403c1030010a11049038051403045020b29802d03907450f940c098040f03901110074000e81a851900d411002d01c5100001010b42c1c1c11440b80c1800c8100d0b5489000040e4030041b4040c2d0a080144c00082c000104443c441015400c980103640071070444c141076031003206500581ca480390005902082820600c0803c008444054101074400c10500f4010980140c40394004080640800d0412010078010403602040d1008420943e600e840240c840d241d820010b404003a10549071080b81910000120740e20f4400c5a0144025444003009000e9020029080d50403550090780b09014500ca4100400c240104c8258000800c9592541d18003c4618800040c03840001c440158a0004000300b00c103a000900103009460407965000039001d144800c492130b000c0d5000080c1560001c00f4440c2000e403200000c0c0218444100c0003140c213644803540038049070003000108229020b102c40c080c41e0744034a0025002c03030380d0320480c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 504139190 1250 504137940 504137951
    0x609140a0221101107034a030f030307020d02191211030f0d0b0f0f0609120f0a020f01050406080106050304080c0d02061801090c05040f090b010308041503 68
    0x10009180d10100700710b5a20b5805054500d510001014424000c1d1000b00c910200442d001006481300c0b1900700d03490440110b001510402448040c07180904015045041020095400314610010004125080174900c04107100c4848166505115029600a403900119102d01c1c00800080c5003200512518040d500b0482c15105854141d07512262103e0708030740e0300100da0740703030743c0d01100c0c03a0002d40e4400002d408042460306031204100010201e83c402c816040c04403654010070014040d45c5590300d10383c8a028183c2c541000d00740100500a0498002c1a900151480401950407c403000c450000c0d103800c00d414400c11450072102c410362201003842d0a606060810401810101060068505100012002a04204580b02110003c40c2d102090700c10628840b24060742e600000c1d20011003a81d1a1003c01c0e10b1103605110761046980c000d014451418900300600004121800503402150b4903100d082020654040c400da00842c412132490390707036624011130881c83c0c03a94071803064200f50a08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 504140440 1250 504139190 504139193
    0xc120507030e06160c0303020607030c0306051c0201030b0d0c0e0106140a230c100b041e050c09120f0d030203130209060a03061104060e0609101d0306040609140a 71
    0x1000c104000007903c0181c0d4809074003a5911480090601c0100b81c0d0803442d20100805602160180c00b0f07440e55281400019941002034013500c2c498007840b030f0006d070088100d951039200034402031071950042c140010700c03107c00d5002c11000c03440300303c0503a040c400900003045103100303004c400c84c014080c501d80560054640700518800740f0602c0c0c141c0c0304201d40d21a40300000341b5900016507020080005144d50f40c03e01d0140c4a49629a4604080c0e5240c94240b000200d030816020f00c03414a0302c568404c40902c24a0300d0741900601000e40030a02d081410b010003040c94444034030044440c00350714020030600c1c241d030365210300e072005083c007900400d40141b062040b805000d107800c044003a8106c5803c0340320b580d0341d0081103035074040d540058080ca041c09201010042844010700a456140c0d4405489289010a0110900c0341c03000143e0002e0440d540c41000a01ca400100c680a50380c41079544035403441030001e031404005642c10f5074243c0c1e0b5800500100407501c0a40043d41c1752a00c00307040c8050fa035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 504141690 1250 504140440 504140447
    0x4050105070212010b0d030c030f091802160c0e09071224020909280203010b0405011404080703051e01050601021509010608010501241404120c0909030c12050703 71
    0x1441d600a024000b00703051158025401c1d00308028001c0b018005504050841c01c0080441100a070706038045881e60305602c54007071089031040c00350365419880c0b000c3c400348007401400950101c01082c090301c40c1c840c8004002104440c150000f003002d05003a1645041001189051101e15401000d00c1e0780603616910004803000b080700b10b02190014401002c00a480131207029114140945900c603084004014000d013608603080b20b01e0a90082c401c080b2920000b41600700e10013030240d00000c0100340410000c1e98414a200a003010a8040503414156200c40b600e15140058004a5198100314000052034040c0400d1429074908071740248601d0034201c00103511510852420a4601003a00c005446827400750402c40c01013190304002c0007a5a9141140f20f401d02c412041c4001c91076090224500a910541c819400e020400340842d207081d18200047e05156401da00403150750b0100d190000d001c2042740714803603800d4042c0c0c841000c4900c00d0300c1c004400c5070000c03000e07100307001062101070040380d0b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 504142940 1250 504141690 504141697
    0x100c020d020d050306180f0403140c0a0204090f0b0a1a012d03230a1503030801120f121805060307050904020c0f01110a02010f0504080910200109020111010204050105 73
    0x5241841a603945440703000ca4100081721b80322804449181d824005e8031a002c481c040d205501a6803580e0401d48030854884240c071980032401b010ba840000b4000151a296000c150518031803000b100d010a140e941300da000702c400300c03020741281d641d65109100c102401d501c010517001c802d1030b09103603403680c2d5501c0e0405c1c964009801c1d24010101c0a010300014004c0d8007102c00c000c5400e8a404049440c040083e0354510201d55a080840c02c0c0b412440460172241894010341c0d80c1502d075005240c1c01c01c81c040701400441e43e010b070b1390400700107692004503542d80c8103003d8554085e0759000b444c3c41000025440c030f0040c0d50001d40240d80030000c00c00459402004d4468485088901681c2c4188940d2007d24244005451045035460b10792190301040d03034240101042003043e0024842c00349c940441d80204c440840c3c0240100508010390722240c500f078003440040c603515003050400c01c0e041040120058461900d13101507070703646441d4a4155078014205587c034468900003035140508000008180c0e02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 504144190 1250 504142940 504142963
    0x90506040e0a0b060f1e0301030b0105010f02032101031a0103150c0c02060c010209090c04030302060a0209030a0606290408070911120709140405061e030c030708100c020d02 76
    0xda859000c9551514242c00550441c1802444191604c080c13511070086a4440c414881e11810383e0345e000b04001b80640c1c1921f04903900052689950307860700c0e0056804203000c0c40008d0844c0020804002c500070050305404019100d50341a40c0190705514080808010b01906480905002e100400000d11209443c21541d01030450208900c800d43c40c00340e505006c0c22030020f43c08a004603514661032030543c00f801d1000d00840d804981501c40e00d071400f00034403a42c080540143c01510000702d905078650001c0c1400d003030140c00c5441c0100d5648911040b03d0b000d030055080e804110380c6240160b0300d24072000032074880c900f060515062820104550f1071840e841401c865646442d0301c0c2c0a2002031805035500c00002c00e0345001c0c18603110b80d0040114501d40620440b980121100c0625402d061007034911030314001e40b91882000344010008124800c1522203036041c80b07503c65055a507101480719000502c94a401448400444410b00003038512001d0341307808650100c14002003460340080d200500f607 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 504145440 1250 504144190 504144209
    0xf060615021911060d0e0303070206100303320c010903032417011104090209030d0305090c0118050a06110c011b0605070e0604180509061506090a0302031e070609050604 74
    0xc40d83c01c008607140d4002c40300113115491801124100001020000b984114007a90a41d016980c0e0f060035601407081078040500020040804900e8138040040781d00000c1c1700d416000c0504d4000c00340040c01540c4450700c024070b1651142d624030105500750195070040480c201c41c141001d070259101043c02e0000c1c3c8640c4c0f01e00c11030814038606680c02940200c10fa03000d140c4c4001c0e40c8580740d1101d04040e50100000300e000c2d100d15400c05071403900c6449514061000c0101400d0a062504011900503603800000301d181080c1841c001242e03503c403021580144102e80721001d04400182c1964100340c013400f1468144095290344100200c10601c2040c0b001d1340c401c10020341e40d01c80d250308030341c01c1c0041502d094000c28009004205c280341c1d410b0304903600e0304203c410304c121713560128113540300c60301503800854400000104240d64034242c40903140c00d1001400c0d07031501d5580c03500040e18213030100d81c5502c400d01e80309850707031000301c0d0501c20f42002c0e00c058101066194503000100f14240304501c03440c1d489 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 504146690 1250 504145440 504145463
    0x90206070f03140c0d0e061b0a0318150309230c011b121209120503190606090b1c06092003010302030c010813050a03260c04030b0408070f0606150219 66
    0x580e80c4050540d503096a581840401c3c80044034088c5550700e132802000e401049061200a085800e501000c80c15241e4204108125564050050380904007228044a924107004040441c00038040300311400c480c0c046000301003024074840094151a4000345d0448007454020844010480d0703802000d24103030843c40c0c075014a0000000c204010170081c00010880310001c1e00700d2800d40c0e40040170314052a500001d40b5180c0d14074100e02c01c102c40d024862040810b031450020000000150050b110341d0030121070810410104050755401c848098208000b2540d0312446001d0700c410b001c052468450840c0011847c40d41160002503841000391880e41c10002c40c0b07000941010365403411440c400b580300046650340c134041d14015007585132441c441840b103400e200d000900349a41380354142c01598844d021500d018115141d40006010041040d260031008210380030000d00b40118a01625000d4040010890300709000003500112406200d01190b00c0020000c2d4038544002c4018007440d4000426543c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 504147940 1250 504146690 504146717
    0x5190617151801061d0f06010207050f150d0e0f160902030c12070c0b06040903050d090512070f150b010e040e100e0102031605072004090206070f03140c0d 68
    0x90040c1c014141055013001000a141c0c0f201c102ca40c3c2400e000c0340601413203955050b540740380802041741c28a00591040600b00202c1c20480a40424000041e10240c8050014000d00049a21055162814503a036289848500a09018486000c00c10700d018000c1c1c4181c3c176400c00601a01c50180c43c0c5419030010105000850b0a400c880d00e010600f8400840d51920900103084419080c205544c10206500002ca440c80d0a2041e20103203685920b441d4200301b850701c401070040912a10484851048203070095010014601400c8010311030000c400d0b04618500e452050100d45000d000e0701d050801002700b84d180e0300b1030762801c0c00440540e00000c0208081c00001d160014080c0b08580031854081da07004000019002540704560b1a88540c0ea00790395072204039060b2140f0600503241c0b0780d144410700c11401d403203210030307200d07860051004c40e105945400040c13041c0d104076011030b0710403032b0140c0e5003041580208940c1d5050300304010399401d003c8504e1580d5103a50408003a4400c00110818204 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 504149190 1250 504147940 504147961
    0x6060f0f0c021c1401060f0611031608031e0114011206050603011409090309010807050c0106080304060f0e0d030f050c01020f030406050417090607020103050403120519061715 77
    0xc440390b00102110603512403107001d0240c00c81c04030340c01c0c0c81203050f0149561032144140200001c0f2040c190821206601d8500211424001ca03240e200c0280010800321801c003100c484540d549500651680d5035031b090900510304a44828070a403a800015000104907800c161a41540712420a007001c1c2032403030b100c1c1880c60003844990090741c1d020001000214411010410000640e03405890318030003a1584a600c0360350780950301e61540000c190314001245144a41c014015400200d000810400c1c0c94071302c41807c40d0080d80201001607031050007402e040d0b40c00079582c1c101c84400c4d00c4003403500d691900c00508814030072181e001401800500e000542c1025030480d5000c0d41c180c0c00c0d0035100d00f070a20f8804050711058805841c2801d41071103c5d0b99040c90482147c0604030010040c030720b0300f1a151b0042d40a880028400d40510a5032184038071080340d07a001da184030b060100e18010442c0c40342907602003195000e410040d5240d051984540e8203400018929481d44c44288001460740d59002506 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 504150440 1250 504149190 504149207
    0x60610020109061d0d02060c030a0b03150c18010e131d0616020d020607090909060f091208010807030f060e07080a0602030105011704150902130e0615030106060f0f 72
    0xa0003d450042044106040250900010314511050311030b034208412040ba628903068420b01b04e451700800202c2d511581d1580000001c4c0e0020302030760180c02030070602c150746c0302d021955043c1804000900c001501c1b109030240b0b601e400242001080503081201081d400c01d4101400e9001c60741e602c00b403001c40c0c41c0000f5038500d0000c1c0310088074080e1401f00d01d03101d424240000d4a90140c0b241c0000c2c00e00d00317400491104d100e0001d0356142070001d89080154000341c1002d0a007900c14075540c01052080c0012409400c50705401095140c0c802500031b480100522070507480700b40640c110710f40a0000603d444c03000d6821680080c03020514110a441403424804640d01503148c42c810450103a0400840b500514100c440981350904800d40c151010310540108507802000c520544062504406c0c103944442c6215001410703203031a0b20504d000d01e0b001ca811550741e00105038001820003440d01e04408072800f400c60160000e124140c034004d0f0150408805041c0c42040c0034900e002e0b1640701d807081e02d14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 504151690 1250 504150440 504150443
    0xb0a050610081305100921030203070807050a0309080706051b0c1009110603010303020601060e0307030c0909030e150c060a090b0601081b0f040e090c0f0d060608061806090f060610020109 82
    0x806c1200741c6890200d9400561600b424140c0c40758846200000d800b900c2903920501082e22010083d0741c03001403c450503809444003109156030742c200c002c003162106014280c0300744a4000001c16091006448030b0f0014503010011030523000b04070308101c0303c50105403090707211000d04010074140201d00d849003003e100c0303c0d050780d00943d001c000017060540c00a043c0d07049400a03102c0900c8244008103041d11542c1a01010b414400e090008004085080d8000032015010f031420310982d034000400140610341e011070540c031481012881900c485000c4c000c058102c0c55440c4208120300f401d55481c08034000081406061000500010b9041480c5010207201a03410b00c01303460350303088440f11240f42030700607010b805442c00b045400154031071400510780310703212001000c5101a9451004005000d00c8002c03044580030f4030307081c2c0003410031001c0040900a0540c01e42c005020200f81103140e19100d4018803044850707202508040164501044890700128141d9125402040b5128140e000d013015450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 504152940 1250 504151690 504151723
    0x14041b0f050d0219020307021f0c021201020c07061e02030711060703111f0c0509030a150207020a030c08010b1903060506010c080703020708101109090a060b03040b0a050610081305 79
    0x202280c1c2141c0c04801047c40364800ca680d00240c6a804014000d1204080c00110104180c40300c0300c4050720b0710002c503036404040710f0005441c2880398100e950501020740e0284000c18054004080c481c02801401d080310b502610081d41042c8c1f6503100c440c00c282400d040721380545000210700050502c1001d03401c110300327110740889007151000d8000003909425001d01c039030a5440e03c403404080740d02c5017007100c09106000340141800001030311055080441c3d03c00c2e031145039600b0801c00d00103840700f1001100550203800d0306041c0d40c1ca410305003400c2d140380101462040c942c2440c42c5d041004d11103000d000780e0b80c2241000680d540c41d0001610002a61b0740064054003000c00c1c031408060740002e50308181e80000c010f07600390301202d41d44c01040da14405914101040d060248006e1410b0241c4540e03803060b410303400490017955500005615503c103503070a07901c4000042c204041e1004600500350021019502103254541000c0010700020f40a404038007800c07040d401e041c00307019003042188640e20381c0c1c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 504154190 1250 504152940 504152977
    0x40803040605270f0910080d0c0501052503090f0c030503070201030b09221707150b010c0b06090a0905030f0904050a06030f0b0a02120114041b0f050d02 67
    0x21010340250040c003802c002214103818042a0703d02c0a405400440c44080c1190034407080707440801a00e444020b0010100382c158000004202d4810000c7c02c0d0742300502e8a50351041d1103103040440c00e640f0020316080b02480100d40081c20040301d000101c001104c0d602c1e0029110782c107454400c440601d50a006030915080d040040280040403000381801403003600d082210030041d00c140315000104545031101201c0078041c580d2085a11036809101d5407090045540c1c95000d00c00d8641c1a800030b80c0c00352180403001401600d03481c503510848080c40402d0074030002420456803404c1103048001e0207240a4003c0c079010440303a0b2882c0d001045d8965003c01aa5291888106003003e550404400d180c070450806000ca280c00c41580f1031784040d60782160310301d00841040c1e126841143e40180c81040c1c0700350b0070030205600d140303003000181c0a441c540c10400c9240700610f08200c20382d08040c0c0b05041c0d0420642c10007049580064194132aa13805082072500d81c180b14000d64000d00403420300072220103406 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 504155440 1250 504154190 504154199
    0x1401090602270603010b0a02030f0703030507091202030307030f12061502011404170a050c1507122c0705090103080304030912051b04060302030f0c2b0f02030304080304 74
    0x1900030705466200d8200c0e0110b80440040c012520324081c00380160050410001801b0700d0f541c0000602100c05180103e030704c0c002d803c034034080d0a6030210b4016000603030340c2d0b0140a440d80c0d02000070f10003070410740c0c0e092041c8036040c0c0009403a845542001403e015070304441c000014007a40194030741700380b5030204001041c1d4440c0341d404082500c44a120042d40303001d00a160f85100301c04228011030f0401345c4411103110702905070855600402e10001840003c1c0000100c20004004091040010b07030680c48107400c08040180078a462203451620396030501c6681c60700c0d4900d102e1400822a03599640d810900b00208105080c40450b4010700e81102210b0004028081c00c04029405103102c0c2d070b10361204d21f95455501d070034205154002886038110307074201c0c1c1040785e12844200745034400034000165580d0341e40c0043e280440110751600700360440d0090b8211341c40c100c03200310400c902c164100c20707103000311644d00000109a400b000b07001d109400c5050055440030010389028003a040d049079540c0e5200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 504156690 1250 504155440 504155453
    0x15070e09070210050606180402030402040b0a08010e01060e06090a1a131b030213120213090303090615080d0c1b06050d110a080c0c010e01110a1701150507140109 71
    0x91510303510303424140000720f241818045c0440d4001f020074040340641c001c01d10700308000ba50000c1c10030b0f13074446e4481c1440182e540c0e80300612401480c10200000313222450403410350035180d950307121044280145080105580b40d0b00301070340d4000601c940000b00640785e04840d8511100e4100426049103410480c45440500c41d8089030000c00004142c04007000004004ca05900c5014081050b0b110207000c104144271680c03500c2c840c04c91000304100c08032104198a07404680203010f041e40042e449041d4002400941e00c00c0e0075000d507103900700b042c46504103c162a551051182c2038810802084c1c0e546041c000b0441c803129500e0b00740c4070042da003240c1d40d031030050035604001c02d1541454680f40d124140001c0700803c0700c07010300f042d03120b50400350f56414400302c998100c2c0c04040c515540b640c22009603900b003842143c541030f051100716a1640a441d0004141d070421000544603a0400f0300140700304041220f801c80c42220b00d180840c0d03215510310700355810041281d0742d034280b0360800c035400781000103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 504157940 1250 504156690 504156703
    0x3030a02090103060510021c0c170a0e040b0a12050a050a05070501080a020304050c0105030603030c07060f110606060d0504031e120c0203030f0106050903010e0a060902031e15070e090702 82
    0x1070982c1e003881050349900400044003c042013110143e880016020103d00303040805c1b44000b80503042148424410351100105403e60340e22202c03a0b0000014a820b01c20b0f00004031140e400300035241001f03ea10b464010034400c21460081c1d08240c00b0b1652290b080006c204510042c0c00d43c803605454100c8071900c1e11b0380d912080c2e40035043c0850074036000580078810b18401e0741e21464202000301b02c006405c1e00150741d654401b41055805002c104807030489181d04111400c000c00143e504c030700c150001460000e081c0d00f5044082122a0006014010b05d980c0f600b080e1410001c880390002400c0e104d514043d01c001210603005451584084884440c00f0b40018540112005018003440003040542e005c036103a00c003c84100c3c50313045100005200b0785110300b0180181c83c40140000070700321040c800441c90800d511404840036601e84007013000318181072003030041c104406030050740c019040440040c0c40345218080415000b148200250b0b43c90320407a040c0d881d060016110f603180d4181070130020b482e00c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 504159190 1250 504157940 504157957
    0x3040203071a22080307030215061005030c091206010608090d03050906070c060f1e0c180e061906020d09060e010e0909010e060907030b01140105090f030f03030a02 72
    0x6002400500b0b1902e69012080e410107403503840d4a004007810a00b000340d404104500c22402d155a000304100078200001e200850081c1c006040b200786803000f0303020700c0070010b028074025080b110301c4d400c0c20340d02b0034180c1c2d0700b141e980400c1715143c80703007031000c00d400040c81c0400d0403161258400000700c0d40d030031440f107030300542c159001d40d110003034080342c10307419102c00f03407000c0650b540401e0005a106100703502c1c0b86003180c03203490085824034020882400340c0c0ea005a46801d45003031001046030380d01141c481c1e403001c05010306001640703480003a0710008860580c49460400c84c210300000700c542c0d480300b01d42c07500d52050003c910701e4030b07482d1703240207613103006510141c2c002c2012072030b0114109004e03581d1640c0b0700d00140c1d035180020003c1028004c0d02d03600502400f00d10b41d2100c00b5060355074402c0c004240f20b50103850040005510b141404141071b0010303486440840c1c2d211240c0c103000d90f44201110741d103000580c0c081450800540c0421316015440414140740d00000c000d21902e465950005c0c18801c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 504160440 1250 504159190 504159193
    0x50712060b011b0605060f0402030a0b010905182205010207060603150b0a06030c03060305011a21030412140709020306040f1b081e040f20103203040203 67
    0x4518801c01502d00c24442c514042002050580c03090002d00140c101d19030100d00500070030340403684a030205040e0b8005851b103d5200381c582c0d0000d0b009584c4003100c0801490101c45041800d044151442000b4501a02e4080d40d00b9040340c4c5003001c0f0000341d002181c0590b0100c021583c0c2e0803e401c00600506050204891645001c00140c1050f0b040c2e00421500c440002c2c485104149011000e4004008c0781c3c2d50f1400385070310b8a80000c0441c10038031800d01400c042c1440342e40c074065120204100030f03050144400807016191007505000c2800030a40d41030b11707012a61354800c41c4403420700d0395860b800b5219007030403071044040c04101c1001d950091800f448052707605000a00d003544400c002d8501c1070903c01c4222110040b1040c215108100e01604000d0284001021480c0050403101389441150140c03031864001d40c14004020840e000503e1607aa040c207810380601420002500303100a030b03070818040169410381a40002212040202c03020910012a40030150307404a450300d41d0005c4138103921a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 504161690 1250 504160440 504160451
    0x2160602030306090606120609070e1e150c0714060d0507030e0d090e040b040c0b07050d17010e060918010c0207031a0105060f03070c080a031a010e1003050603030705071206 76
    0x181081401c0e203451400c141d0f030351f502c50780d55103050141c210380003010a4208000d03410300c0d0100e0b4440720641c02a07210381284071400e0b04011401d00c0b03400078032a445102c200c1e20800c0281018030021440c40c2c2510024501c0020302050000003413050300034a076080241c01d00e01402c3c010303290b40691101040314044016240708007006a000da44505252040f030494921603400600065a40050268094441e4511698841c2c030342c03d101034543c201500072030301c951040d0314562000b07401c001c0310910b206048041c900c80d0340c1441940e4188840c0586041d01076541c502c086030300c0e00940c1a061a07074151400080200c0d01c50103000940d5200179100981c0d079011461040070b03440300d19000e42410f035200580f009240115400c00700c0b48940c8002c1404c42040746640c803240004007504010054804541d40100b007480d803c200170b41c6400940f45c0030b2410710412100d410210f890b105d802e815484120304001a1680d0760340007107130461081040c004c00501680c0404642c1508504035181c1e042d0080004121 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 504162940 1250 504161690 504161701
    0x51234020909123103081b12070201110c19030b0a0c230705060103140d03051b0a02070807030602190e0303250204060b0405010e03030906040905070216060203030609 73
    0x840710030001039081082c40c20400c020113108800c0644c514040c010204000078103003910704803210b24803504106d440c3e20300000c030f140020741c503401d4101e40f1a0402c009041c419910b150315002c240707d4968024107021824101d520031700300a100041030241d000d400780c1c1c842c28142440302001003140c0030840d5a400c80358082070b16000d0704c0c42440c007010b80c9900c07586103036402d60004442c0700d0040300b01000d03045401c0000c2000110140002402140301e041c80c552642c0801c3d80f46400c008450440714101403a1204019441080303024140c04080ba008149a0b50455a10124202501d0750456907880c8281e00740001080006e500078a0741c004c541440000062207403030229034007903070101625455442030089071241640d04800c0c50044081005842700d00100d0b40c0890140c440d03c0d4050807100710049020025542c00c0400340381c1c0303170750101e0185241c8500c07400040c00b41d0107940203210480360740c0c0c0001070401d8020072940d460012408520b07402c103561100c0095407680110b0349940510145400b01e40c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 504164190 1250 504162940 504162943
    0x1f03030305091b1516060f0b04060b09010e011103040b21010501210c121b02011107030813020a051f030c050304051c020c040606020102070618051234020909 69
    0x2a200d043c002e01580d03030800341e9009401c40750020340e0074608914141032400005a00f40c403aa21240d08014008508030540c0002c0004444055100c8c0d4050f41c0104400350031681c1c85482c5100d0144242040d0540240512440c5c0c594022a0400c6070002000900c105550628001c400c850501d0200d009039240e8894004407407a03540da01e441e10701407054841d140005c6200780c01401d1200c1507441c1c0350f095655541d5440058030f0600c0c04044480366050070f4030190603820f008901d1440e04480d030780b525141591b0307802032400d00300800c0c190b0a01441c104010843d07440020090042078010700e114052201500800a281e100d01c0c1c0c0400841d180c440d500c40868054000d5a02c6250820054a4580000710030544450340300c100300411801401c1c0808802d031703102d214510140080e81c4c00143c440101d0f140c01c00880700320a20803a10541b09000c032100041001660350590410041c03500e131200d0305400c50020000c41c101191801220768582c8800c5200c2e20690540344134004c0b035401e8403640b110580507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 504165440 1250 504164190 504164233
    0x40b0306040f02191b06140f0702010c0e22090b161718210c1e071703040504090b040b0a050402030705040e03040302100302120c04050a030303051f0303030509 70
    0x525180e0b40780841e00c020039004e6601144400030032650211206410b0741d412040b5201f4020b1074440503844d03000d0008188228002a030712110313500080000180e00c00015105a901161240c400c8000c00c1c181c0a0050f0600c0070040180181c0300f00740103403081031030070f1981307002c00b240c164600c5007008030751004e09445040580b03520407808944162584600c81c2c100200c40c80c00c51100d01911514003800e0098840ea034906030881094100192221204401d03581070103460710300066a10010141c00c0d562002c0480e405e8111140008800e03d88031140c2e54480c03c60055500c52540a0300d081205414060304071103d1b442988108503009a9640e91401c1c101116000c0e1000703501984442c1c0144032030b082c541e11809040c211032003100e040c56600c0d130004200805540c403060002c0e80105400751980c242042d45508188600422800c2c07c0c1410040f5406000b0380c80042d04158480011a500b6140e81440d04074180c10400842ea41c19140d08029014180c00e03142085d0034840c48402c3c0c40160322140c0c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 504166690 1250 504165440 504165457
    0xd02031303031b0b090105060f010309020f09071206060c1e0309090e2d0706090602100f0908070302010605090c0906090f12100b0108070c0308060409080906040b0306040f02 76
    0x840a070070764a0807104414070114115154209003694004951034000c0944103224540000c529454400d050040088031504c0090506080005403c016038900c0ba44441d652070a444260890b620610f0882d102030607501c403800d4032454034202190443d4001d1030300c05000c1c000d041990b0021203040100c1c501c0460081c000d00040d40900301400502c0041d00f0210100c0c0b002d5040b80c0d0a80c040c241c2481c0d000c8216039000d050106000c542165010040c85180c0080c48a42030800b00203107003441c00303074490800d40c00702d6000390340e56003201d002101c45900c0000555005203080d6200c175118a0041d00810880c0901442608421300117602041000308a0349800d01c090a03442c20103c42a040c0100c3c0218100107541c841c0c1c00c4000643c00301802c21640700d68159002c004900d20085000150401c80050008000c01000d483d007480425002002d0700e4201405460003e100421400d00050b50300491103550786c8680005000a20604104061801102c3c00c9404110030030141002c90102c0c405ca101c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 504167940 1250 504166690 504166717
    0x20a0317091b01030e15160302030912030601020715050a030b0604080705190e250807090e0915090f0106091a131503120f180b07020604030b09030703020d0203 70
    0x4460000d142d0340b0580d803010074018100800c4a030038402056003804400c456101c5040300342001c0088000c0741000d544a041c909040c210b2941c1003814040b41c842b903d103443c8050241c400000310340e0691080000d10000d0041c0c040d0300340610b50b4010000c140d64403a50310900080d00740a4442480d242ca2404c4904a030201c0005001c0d20f85040240002145007050442d06007094000001e1015071007803070f061080d002d141c48005400e01c030418160000031001040020060f0f140b00308804250080000000d40d641c24204036103075560881c170704e40391030010b140d040020301000c0248506610700080c81000585464000d01c80b8584810781c0004607802d102c182021841c40342411081c41c00c107980c0343c7c41703036008400e408500344503900982c00300304c41c00d540112094565440c9030208540e00102c040390908003032600c074807104107400703031615240c00d0b50081c90001c1c000003541c4000c42d0f41d220100d40c020765100640c81d140303140c43c0800c0e54482e00010750a030094050a4a0a0701061010040b52005107070540c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 504169190 1250 504167940 504167953
    0x403020c030d121a062a060714032a04081e030711120f0601030201140c07030201030c0203090306131109070801150507020d06050105010e060913050a1b020a031709 72
    0x1103520b009090040404881301c4446080c103092900d40d10f00130402032403100d0034500741d0211110400881078a0711070075401d540260007170081840d449610200d84080d440c07149a1a41c40b00420360240940742d81c0c15030000d540300d000044000599001410440d140e10040e910100c02c01405422282c00c503400703004460b0000c008a400103000844a02e11144000d025620850741c2c1c00d844920f84182d80d00040c180d6804500100119a400038052401c24111000c0c107040694003010ba0765552901d000007414103481d1800b620104e0b2080055820715803000701141c130b0301d0600c0031392400c0340d699003c025070f030180484072403c441d424200d4480d03000f4482035a803854141e107000c400082810301c1450745c42c1004000c010240140e13840c1081c10103072a0088200041039450407001402c0c8030300c111150b50040d64244a480200d95400390414845140140c020580769070302440d80004184800d00800300c0c04110107020445a400a0b030407507640e100b130316040310754490f01001b5419201c0441d6803440550005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 504170440 1250 504169190 504169217
    0x60515030610020a0203070902070b10031104090203280b06010e0901060e0a0909050c09091c1b02060301121704031707060e030c03090301060909020a0b070f020a0e0403020c030d 78
    0x21901e4128042c07251055620b9050203900003410904207a00c441411600420f6010500410b0300031160002002164500000d03e16900c0385404030184800910a5035100958400d644050084070300502000301194403404c10003100c000702000c03800050b1249034511002401e0b5500400b5281032000303006101c40300130380c600b06040744c601c1680310b00b00f5002601c0034800142d004442c020340c2d40291181014049124401041c0442c000d40104600c54641c40460303000d1254800101c01030301a034480c40c04048004082c1c100c442e40e501c0308030000b50005030000000030441d0103d00b5088160313216003003100c2031034803903400004140a14003015094070116000d02c549015160020823506120f10404110380311100c8a035400c681100008526503000052151403d00d000e11511000d000c89400801031014180c01080821100d40165000a800094910188030301c0100d1415416801441006020740711403c0004281082d06d040f03000d4820f42c007071100e140c40c1c00f05030780408041e55960040c0f01d0042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 504171690 1250 504170440 504170449
    0x200a02070f0e010b19020f0a030302045003030403031e0e18130506150a090e0705061308070b070605011203080a0f14040503031f060504030204020703050903010f0e010605150306 78
    0x305c4000205510138a014480001c4041c02000481406510016200c40c541250101030242c00540b0060040b180d8810144400074241100010709007480040c41100e42c80651a41c2c1c10280400a0362510000c2400410564045605202d44150307041c41004a00d24210907280d50042e02501a4040500c40d10b403200b444014142c207501007007040c0704ca10040c140e80c9609041c04e1041d603042582e920380b40752050040c100702c1703c4070004140c2d10004024028140100301d032100da40e4000c0381d1040300300081ca0302c0c0c154104030864010303020300000c1c0e80101d0b94072110f4403416032000e0b03411100a820000000741e2444010709080e0200d405454480c656600c5e034000e01c0040150440c0945001da44a030f81007581c03d417801c0e00c0c9210333500c600c0003103030390781030506051302d00303c000c1012030f400311807000001d118640d032080564040300d0b81554003684551080c0313020342d070034010700c1e084a405601e0b010581500407903a070083c003032140308180200440c3c1e03126030a0001e0000a0340b880c4400030340400204585040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 504172940 1250 504171690 504171727
    0x9040303060b070b04020a0501020d020703120507021003060504110903030a200304060804060b0f150a0302071a041202031608090f22050721200a02070f0e010b 70
    0x42450300058094540c42d88080b540c0012206407201c4004000f0041103082c44420140038040034001006130a8000800030f5494181c0c3c04010070442c1507201820405005e03005907800280e00510102ca5888100340c000c0c018045403013410300c1340741001001d82f00090040704480c0e86100140242d0301d800c0104906039803480e05c0c6040da980003003210b080c00c0c0c2e42d208184094000303019a0760700c1e1483c070b081c07906001c826501c000007411f105005003c3da024042d91740001919000910005450301c0d195542c030264002d00800030007800159a00c1031062864900307148442c4140d20400b10880c1d9200750340812a03030790081103810328100901010150114100702c000c0e10140900600c903010407400000810500c00a000e40d000c09070b0203a40064400c0070450140c180c1c840d00d20b01e054140d0044c642800c60710121660141d802090b5542e4114031050461154480c080390412130700c5544002c0c40b2002551400039104003a80300700648804186491214131240c125020821079038100004400284110381 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 504174190 1250 504172940 504172943
    0x30c090807080a020f09010806070c050c0d0c150815010c02041b0e0a0914060402310602100b030601030305310f0e090d03050a140103050303091903020a020904 70
    0x8110000e6000410440c003000b410101c00a01610659031050007502c42404441d03612a0354400c0c01446114000285140e100d0942e14020401d0030107418110b0070000480c0136a5008512001904180000e1005050860b2210605400701441d500300032216140c0c01d580c015000040c0c022180d540d58840c030f102042c02d900040c0001450075001c46c0b000404184071740e4030030225003103000c09038070f074a1b240300e2900082c0f00080c814844882c081400c00c220b440d004100d10302c1a5408580c40e03510040740201c00c414603403007140090a100d0058588090b1800c6841000d0041c1b03e840d0441c150419a80260001c1000107801002540d00b5a82c0c1684c45810504850b440b01495082030301031810320805448001030f0900e5003002c40c9080803000705428003d50090b108924509090107890b90000655400c40c404618000496495440c601c00240039600301e100a81d81c003800011060100120045014409031000c4603e100c0c0705070803007038882c00509006405a080202001c000d424261010750b4400d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 504175440 1250 504174190 504174197
    0x7021311250b06010e0319120f0c08030a02250f051c02061501181413020304120e13020f03090f010908070b04060b0a0801090b012718050607020604030905090f0106030c 74
    0x30f0740d200110034110101b5000c0d1900039031045440c01d80c1e50005610303009d01556250010280035141c85800e001c1c0b0019001c1461564000361003604078406034565151303140400715040340802e00381400c0c03507605065001070b40c05004000f0a0310a441170080004d5954101c0d801408807a070360101d007411902100d80c0c0300c605000c100522141484032001041000e490660050b9002030030010900040b024000000c400c0b05204005010219505802000c012038003482d00e0685000b83c940840d010501d54080802d240d4000300b0032880d40b40300350020f1031003070328410120340310036131100c285a0980d02d030248007520210301080202c001c9018034480f00e61060080c44d0110350110302c5800300700707000c07069400103513165590b000b824104800300130458010405004020704c4010b04040c440086046940d620b02031990340c110b181407003200540446007041d001015600700c0d207085100651a174400b118201c0004550020203d600c1c50034070822801840a102d154500b40e0900714183d004001c54a00601031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 504176690 1250 504175440 504175453
    0xc050706051326060f01170303041a060409020a0803071e080910180303110d171303020705030102130e07030203070c0b04050f0609031c0218040207021311250b06010e03 74
    0x10540204100c41c01070380d01c111215521741c13509600047c0d0641c5180c0c40c03e0f02d50410030520000c10703030074814010072640d01c41b02000c003a00c0d15000070300140045000250002c5825000140c1c030603010002c0e10f44c00b40a2180c0c1040300d4021610707170104022442004154500911151400d400d002c000d15640140324100b658282031001d5103503481c90441e910443c0042e015590102e070300042480840c17126165810001c00700c020310422010b06803001007642c6105280d1400c3e08060500c05c0214100804014000315642c618002c20f1303d40f20101801450529581100405c26081c840d10071a4414121a61900d111400079696514141006001600c00340700c0d50700741031030000090100341d001c0c00c0341c4002945e0344e040f440b0300840540750342c61182060601c107201c440400031000b140001d00a1040b100141d940c0c4a910014103e40213044a580103030b840c1c0004110781081100c014002c0f03240349641640d80403400c12139030104400c0514014114554540801c2c015400740c0441c96002400909507850b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 504177940 1250 504176690 504176759
    0x11509080d0c230102090f040507090303080703020708040f050f0a060e0103050c0405100e0f2b08040e190605041a2211070b0f01081506010c060204060c0507060513 72
    0x1441c9080b0f0303d0002d10369500140c188a580703003004503540410815502403003a803402d0000070306003034001c3c80040c083c044420b000401c403d02c668122508942e0100c900754a0750341703039641c281e038440382c500400d4012408141c80d4206071030120310140444545a450f504010924001100a0b1030043c11070304c408030080c80003254079621483c0c0c0481c110b1040c1c1d00e0418680014041109074034540240324000c22140605414074051401300c0c0c150002501d100d5112055203103491a054496644001420900d5100780305070814400c0380d013a00c1c00000380c000e106c029114030810084803164501c502c6a4122030b00c100c5580d06200c00180703441145040840c00400e4000c001009940174448401280440001d41e00c01b00035540c0056078201c2542c09142d2059030600303d0540e40d0b110584084400c200720040043d405a00c20b9004402c169070182d0b00307644031030f84c40601074542018584115142d004100e0f002c074107540f0901c151801d0409d0405e03524580e030b180903c0420005c984484031075040e441c0e0b048200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 504179190 1250 504177940 504177983
    0x160302160e0a0b060c03040306091505130b07020102090f040c0c02041113090b0306242713031209020a031a060a0806060f0103051801090605011509080d0c 68
    0x4004010244080c10903140c0188581d08840c03d100c1d849105100500c0103001c0c4103000800e0b80c0940e40e0003040014104002c1c2010081c80d0040f4904000315070404042210314040c410302403460740c2c45030216000603210303018160300f41e0099850b8690041d0190300000c0151805400071900a0301c50b00780b0070944005038020501399202105022405080000c07142d01030202c8460020090440081c100b11100415000a464120103401c92445809044003801c41c02d4444c80708604042c070090940035880c650007611200302c0d450040c0c4140303420251b000204581205030a0540813030b4141c0e184c16180604c4000540144100001a82c001c5506440400040e5a80242c62440d410282203c5070a20303020303040000864103070304140c1880e008142407200c00e46807008441010f520900707003c24070355560103216440451f0343e00306070388540c2050200c20500003687d1100b41039078602d414101505907880400d50301c0041a100e013081c940d101180203081c09114110320107507544503100c403085006a90340c154 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 504180440 1250 504179190 504179233
    0x1a071a0a061a0f0301030201051c0c0806041b0c1202010617030903121e03060409120804031103040b0d021303121115060904030f270f05010201050c160302 68
    0x2400d0665140018007107902c40380c14200d0007030440070071549411200321488101d4001032200074140000400d020f00d00c40c00311501407480c0b01c1000e60400104500e4034004224480c252030042c01385282070078603401011810072076201c5c02c1294071503100c010751540c0e4042007200464080421550b8a41000c00c440703a8030005605e80f0304041c1c00840e1150182d50030541442d0140302c240c540ca03081040760400b885040d2403610049030519030006d8480c2d07200b001041c0a051a00310040c9095038008071580201c0d0010036190081d8004c3d0b680420603440c1c00c500302d030340c0d1040b4003501c419100207210f0082c820320030307400911030388110349526502030740d8907a2100b481d20501103007200800d81c0d01c062041c0c0d04204200f9070000d242160b559400c0c90030010041002098094405020005030540f1811a1402517218485845015400799007001c00240e910000103c5c1d4090303801400d40c0050001425841402040d018a9070826000e02c1c01001802002c1e8070824107104500f580603c0c0c0b1804468010060314 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 504181690 1250 504180440 504180451
    0x13030305030406060f060f050c030702180411061e0c0a210e0a060540050306090f07061803120908010e0703050d0e0103020c0102040305010e161a071a 66
    0x5241d102e05041c5800030998101da0400300946041e850b040100b240d1204007180c210b0120f0422681c0c616004803117a0640c0f01c0c0e0303240070b074000004030280803c010482040e20301c1140100f41e0300b04101d4070241008040c0c8105401040403001003c1800c0150314004001d200505d0000100c036009016599014412906d400070465011598045024815040b042c040751401d0304455034032070f160a0613800b81c624040c1c03413040c0c2d44003201e070204200c001e0754543c186034a85c0c01200c1b1000c4015401108800b420409029032800380c0544c001003001e11500040102c3c0d400071400c00f5003a01418110111000306021702c01841c1d140c00c3e43c0c00000412132646880c407958461760350b6503402604000c521800c0d00c0f600c0c1c80708000380d40102c2040011400c08244a695030740d241c0740142403150301c1d0004070701034090300c0f0410031954400100041082415031010754a100d00b4000d5400c81c21003090380700003038010f034400c8021081101c1c00c0c1d41c44051b00d407801040400d216500a52076841c51038202d044800d0115403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 504182940 1250 504181690 504181697
    0x200c0a0e0403080f07080112030509130c180b0403060e1002120f06030c10050310050a08010b0411040b160f0503030a05040c050d0312020304020609030610030c38130303 74
    0xa22060681c000d0700550b105001074009001030605845c01050a44140b047c00b54218100109104061080045540115008041204c80c0c094200c00d18020071104040d040420400060110080318584404044450121510f401e0601d90740318180030b008181129035682c09a4050205020347e948040d242a00784c10100d8012490160002d020460300603100c40d1290340100c40b00d00543e5135400000003024803a103130480c2c0f00c1c0c440584c10744038600070b500320640c8013400a1b03001c1460350055100880d0200101c2d810b010b084160811581c00748943c0c013562440c104200302004116201c14900080d9520965850000c0c0c8004d45a0380d046070003d441410001c0d40328800e00081c4108030304000d0240408481d0344104451660b405080c6080f0300c841848802c0c1c020000400b9035441c00d0503610f03401c00140c190703441890704401c100b6140c900f80c002150038007003030031001c621050404d00250710102540e00c015041d088680541030a031800d01d101015851041100c8012103049107041c0004512944 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 504184190 1250 504182940 504182969
    0x1050711100f0e120304150614011206050d0515010501080915071b112107120f06020a050d0606051206060d060f12050c061e0a17010e010611060106200c0a 68
    0x94008011041c811f40481198200300d402e0003c1030500c9485090b2001c2402d000541a07090b442e110007030070840e401300e035100403030410350f1040c0240810f00c15098090304c1c2d40c410b00d40c0c0c2c0740c40041d40c039190180c0f45988540c1c80714280b03004181a10768405c0e0420468100340030340032080348148500050060084800070035000d984021800e040300b030f008a00c82c4c1c2001e410718000c280e121ba03a0341e910803407084082840c50290740105018018081e4008290080341c15959481a0314018040358814030101c42c00740c2c64071b00c0002d1201d2003541501c0d111122160034842c59141d500400400740c0004120000300b95444000103401750f040c1070468014158091a0300c591440c50501a05010304904403d01540c0c0820404628411080d80320001085450b030380c545400c18002c007258031441d820020024500920000f15483c686040741c20704a0700b142d590b0107585604225825100c55081c0f003000041032820b0b0718005007a040c2c0d03c0140c0500310400032103c08102d207000042c001e4400e030384600c0c140d04410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 504185440 1250 504184190 504184193
    0x1003060801050a0504020f1e040e01021209150a0e0102160308061311070816061a100201020c0c01030209010203070c26030c0709020f161401050711100f0e120304 71
    0xa0007220303032042030010208005d1030b081d0003260401500950162040f20b0400800320300301408141113120303207805002003210b840d09900300fa000b54004904a064410f1440c0002d11000c4001411801344000d0840500103442e11504400942412245101255005d2041e0140b407040c0f420196500ca000395a4102542054001e00034008500f412200c2100d05214014603929413050440340100c0d80304134455510305400da82d804103c510020300070102410503030054001c21040e0310103c5203c0c021a880c140c00d06821000764202e00ca080d070703501042c4e007181122000542c025400380c180f500040c01924540394980d030380d80030040d00d241c100c0c90900020b11021030301c7d480ca800710070b0f02041200004500d0102c038648116074904003032003541490f0350005880401540d840e4180c820500e00d14640b542c040f43d141c5041136607030700e04030550400780d0f00e0203000604661041401740b41011000c07019180d11031141121901174801c0309500c0c60503a4480d554101c4d00c5038100310901d00e0445240f0165103d0409 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 504186690 1250 504185440 504185443
    0x1207080910031d210f090d02032e0605010c110f01120f050907090b010912021c060b0f0a140d0f08030c0a02012d1a0a06030b0109050907020307030804030e10030608 72
    0x104e0b288401c01841c01d00c64540d4000c00c0078100d60350208200d485c44021051440060715010b0300c2c02079844581c00400a800107081d00707a10007241e00b02c10100500c0425290801100c00689584010704200050014503203207040000e1005070442040c0360003100f50120f0100300e4152100d103014502002da5590400550120030700251000d0b0552000502403c0c444200081006196001d9590090001c0e10040110350f9003da41c440d0a44404c032520914000d40c1c10610002e0a40a0340c2d41c2c09202c42400c0e02e1118a800800402501e64141400300380301c0c2a05e06200aa918a0794101e4400081d00b0b10080800d0b903d0000c0d51003080c03508940d81d61100d0500c0020300751118880211307441a110b560441c1e4180020800842c3e00c01103040c0081c5000702c2c0d24a070040c04142c56803c40d0008100003010810381c1d4160881c45092200ba2542e0034059569001e100c0a03201c1100e00400680007488407000082c03054000755041130180c9002c00d80a859580060340150102403d280407030341c1c40f041004030450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 504187940 1250 504186690 504186733
    0x30501060b0406080c0c070f06050a0e0103060506160201020c06040905160305010612230f01060908030f0a050c10140a11030702121e03010b04081207080910031d 71
    0x507a00303036541824601140038015481c0544104500e290106151070600810041d007402070041c103071019107003966407501602030382c046412603002400183c1c808406501034002c450071204060085490b10600c03070308a141c1100409001c0b811400b0390540c050682d69044080c03c0a802d0f6540300050a040c0350300d00c0b80407203061407020b000745403e10004001f030300e03041501d84000c1c8072107030408035880301c16041c00c00444183c8091040e03e80828028860451361881031541643d503a500c8481e00b20742c0b9030100355a00e01945010000d50701e010130541c58030750303c9000a0709420401c0001c4075000c00700201d800c1c040c0c8640c0d016a8129440c484c0400901c1d1040740101c0322510b8400c0391403451b50500d00c1c0000c0d1202c05000c140c1c0408000056144400710341011501007084901d1026612540c4030301400b0042e07440340c8200d19091140383e60303104048032000c0444183d03903403100207146070080002c10701c1010041601c0c90000c2c15983e2403c80300046481c0d6004070907a0000000d081c61440b5010018080341 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 504189190 1250 504187940 504187949
    0x60c010b0a150c0609020a03022d12120d02250b06010e010e10120617010b0f0d0605060312040e04050715020c04092a180c050304060203040c091503050106 68
    0x2403520788000682c028583c15078003a008400414004c0990010072034100240d44025081281c00f40741525080b9201c2c00c00e201210802503c2c4940400d480812071252039500b6241402e402c9400c2c403030b0110034403130000d002c8014401400345c240300b40e10b054144190003411010004003008180c8204105030310f2009940440c00b42001081e1030400400284008141504540103070b80451402d2401405141d4280c0381c032450300b0301805103c0e26100c10a403070303820b41c10020001e9800d000c07010520340383c40a0001245000541501001007003911240040c01d0b001d012950180075026090b02d001c241340e070080000c0d04551461100c10708007031408601c2d0600690140007080d0842401d81c0e400e690104045038136103c101c60108208215003800f824052107103030510b018240304040001c0c5007100c0c403a448200d8820a0304161031400d0340220340c0944450458440001e001000014001110b6502441d007040c0690b00c0e105805444090810403680071034404007600681c8101001002424002c100142 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 504190440 1250 504189190 504189209
    0xf030501150e011503142e0b0a080c090402041413091101030e030c0d020a0c0b03090c0409110405040b0a0c210c2a0605060f0a0b0a02010605060c010b0a 67
    0x146080203403202d4003418004e100401c0034000b0494204e51103a00208082e81001c0f0494203141002805129075000c0005007003441519809424205800110304c1c204507080c00c01c00c1450002e20310012030b00c43c80000c1400c0516002807084820341d40f0b440c0301501c0600b860710340d541c9819448108100c0003000081507a01c0b07903414110100d00060804a00002d15842802c2c04903034500340042e01419405808002c2540303210b0440341850041e4006000b1901a004440010f8101d40350380205003070b40f04c226600c8079241c0c080d0303150721264241540001c0c40c483c020440c0c0424850743d48001826038005072003e90b6950500010b000c4848024070444004104600300040c2c1c400b45003481c02401d4145000f4012480d0341c40d0007910300709014401e0021088800b001d040303c440e407019000890003869000c03d540c0186042c001984600340048580300804008bc01d1410051401800002960011034101c0c2155210840090540c5070b075001f6043d500440b40001c12050541c00c103000c0c0c0c1d0412135215850b00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 504191690 1250 504190440 504190481
    0x105070b1503191a1f03170d0f020d180b0103021504030b15010e1c110d020d0b04051b010c020409050309060c03040e0f040201080f040c0b0f07030908060105062a070f030501 76
    0xa003450040c03100101c9031301c040403914080a00a01c010359024103600750304241c2c2001d4190001107041d50003031032f10140003c0c0401c1580450038040e210070100340070040c560080c000060003d8074001e00e01c003016401e000085403030b181d1241e03a850304000f4141ea804800c44181d404da42190b41c1c100454402001d4299010468105150f41d24042d4541c0d000700a0201959084586000e407200b040f0024283d8002c0c0007513034000b44514002414000403201a24103016003401106440700001492202c0c0c001691103400144080e001c00006005284c000c03030f02e504c41000796403850346440e0041c0080c1e03180f0602942c1c8491030112000078401e0000c1200014849003010400148e8200d00080c2d080421031480010079600d9260000344514190095440244080340450700c00c00400028294640310b6956461225a40c2c03030442c0e90b810080c02420303400341d4140001c40c010640420103a200c0c0d450605000761502944150608141860300080f0841e01d440c401401807003c240125492003d0361445050f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 504192940 1250 504191690 504191731
    0x306090d02070e1b03070903060b04050601090506030a06032009160918060504050f04051507080a0917070b100807140d2a0501020c0105070b1503191a 66
    0x11a03050070301a0940007260f030720210350805102030710b0151040002a426580741405070003d4800a04d6100484002e401c0102000141c1801d020b150700560040c0c59200c0000c3c10309007004000e8000030490085607a45a800102042c3c02d2007942070b00c410001c44050710700c0c51500c24400800d50007840404a186604007600f5460340c803480351801c441008420072062000c480e4520050f10040d030120340d01a0034081400301591070303440b00c42d00903803169046851140303026100c90200581100c000000c61002c1e07000440d85046600710101d5544190708640d511084020400070f41c2d04449810360707000d0329100c20050203403000031503c4007408005000300541031625101c1003085030b4a200c1a40546000d030181c504100015505454060700309804148040c05400c03001d044c82d45078400e9500500c6540117001d050350195007181c291681046481c1e116564a454000140408908064042c824600080c010801c45200c3c5114903104007000014010302940c040c0240d00c001e8088401e000e490a9001b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 504194190 1250 504192940 504192943
    0x910020a0c03111305090303160c050607140c0303090c0108010806040b060d1518060507090b0f1303050f0f0d0809030a08090106051314012120120a020306090d02 71
    0x1012654014480d0180f14001c01c0450000300464220b07502250500d010312a411700044040c500c2903102080b2110000d546400c00c41d0802c00a07800509035811400c081541d02d031141400003c40441140224942440c40d50310920350340c02101d80d2031403070300a100324154541e480251240180310f080010480e605180d107918040720710107050030340300328400048482000340504201c21001994441082a20032640303141c0c00001419404460152800c8002440c882c0900460010f89111041e01c0d400c04541c0c41c4814015403210b1518403003010032042c000005081001510071b920400c0c4003400010010702c075468a04103441400f42c3c244481071003004055940001681c2682c0b4251400100b25150701a00c0342c01003206030040c0f500404070a24544010340f132500302e04240311013104505d0b040e80e81e98115403201010104030628003444540d40c1c401007130ac82e858808903800340b65400240195407400042d00c07064405803d45254002c0d90550095203024030040343c0c4404090040c6c42d01c0109540000e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 504195440 1250 504194190 504194213
    0x50a0e0925030b15100201050106121107230105060f10032301080a14010c0e06030a140414011406130e030f041d0a02070b160e090106050910020a 64
    0x11071104028810040c104028070305030300103540001c045410780c00c0c525903004400b21681d00840c060062003024800c1240f0501c9058100c80003135940142826080f07c88001814a03507101c03010400e424481c02d4041042000002d0322411a0405500f0040c10351060b182501c02c02803030544100c1000b40c00c1202c0d5140c0001c4a900140c0601c0c0002e100c021b070800c0e007110095916007140f50355207010004a90040c00003041003c3c0d038010040d4501200002d000d6074213880850104c0000207405490b18111800d08034081c5400c9881c1a401203080b640b064401c110894044805843c002940c0d21700390f03000d100a118100070740703161142c0103c043c5040001305040403905060800300c40c2c1c3e1100000408081402500c0000940107081c03981d032a61200c1122445c03000107101e0144074075203000316046526078400c40f1401c2e41d021502d4405580c0b62081e0808180c24004210180039462240c3d035840c3e500d50148502a0809480303141c0c0300c88a90041c0803140c0305441da18020355201031240c102044801008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 504196690 1250 504195440 504195463
    0x604050402030a1e0c020115080d180e04151a0a05101b0f02010215010812030601200615010c050a06050405030c031803060c030c03130525050a0e09 65
    0x25a032070f101d8100100003000300000310501e840000c42c03840d80308a596003103444030300c80d542e0080c0005500308000405545c22071048803401d0303101e01100c2c20401d002d410840040e40c0d0545808a00030b90700e4444c1c4044d40c004580c01c036622601c2684506495070b2501c103000074a036090b0140e00706a080382c3c011030b02082c0320f4003906100b5100117400b8403030a88a980c4000080c40fa50b00c0d280c076088000e19020041140f0484204c1c00750003070602503070540c110345603582e04031916034009020003049114908602d07800a000341d070400004a10b603500c1011004003600e40d04010f480107003020726094614008900401c103169041150800c440030114400107045a596504490002107030b45035803030a20b1a610813490018404d000c0030942d6074040d8108540b602464030154151450b55035030800c40f110f1444101c2d2180007504080c4003140b030707407034041440d4502c0500c550115a43c1d1000000f418a540614601c8160601801e00e418005424562003040050213250380d0328445050228a4640301da086014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 504197940 1250 504196690 504196699
    0x6010914032a04020a030902040b04090b0f06040b060c1c0302031612180813050102010902060a0f090806090309041d030906070303110a080a0b0d05190c091104050a0f05060405 77
    0x18140c0310b2450001142c550107500410465407048400d40c0540580b1800c0000d03803255190007400001410540034641429a000e40760f8481581c541c1041002c0d260080d000030f404c16980d95800c461915020004c4c0720b4542084024150511031507000c4644032480ca0041742098014000d0220000c20b241d9418200320346c904040da0250340183c01e440050410f2080d80c05006014004142481144030042402c204c00d0b019400d103840d1101c00582c00d803405500003d421000420007001001d1140002c110780f0111880d103618010f0b82c07001020301d054010340da0f1070384a400000d42200107140910940c40c44c4078243e0321000083c9044016540c0728050f03d01d8440c01100f0014201c008c052003613100c3c0364024980c2c0c0d452500c0c3c43c6c2143c002468000c0803105c60016131300e48100c004152800184500385e00b684100244092a0012000300d03041101c00340c1207a02c0b499a00300403a040305d05024001d004850030303501d80e458600d024200b0002c81000c0c4d000500e10b140d810414482500ca440c101c07419502d0956 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 504199190 1250 504197940 504197983
    0x10617091c0c1b120c09060b04030809061e0c0c0108040f0b0606190c0308180c010e0117130318030804150905091f140916031b080601091403 62
    0x40511011441c01c410a001030110f150104000100380700311100d6a009146203813050b0346594a4804a88480c0140d04080400f1310003040010309140c010304180343c0180c461410300001810002840c10074011b402c90212001c20713038003412002000f182c0c207060350906c0c0400e15400e2030b8850f0740b00d03640305030381c040c00c29003e19001943c0c41c2c84030800c84580d65074070511f00340599100e0b080142206481401140001c03a2034002c40c110038200a1000482d440d1500640300c0a1000401918606041c2c0304240c10301180d20081c01c2c540e61b50142c441d10841e0581450204a41140342c010032034100c03103031007003015031810405101040110081c0c5064403027004c80c003044429001c005456244440e440302d940400440c0800c410407024800c6052110745510200d45020380700d0034050780b05240710003141c1e00901d400d000904001e454000c54040070b542411b000035008443e00c00c2c6101c1c100d034602d2460124651109100c01542e1040c003810003001a03054040c20080d600c2d000a40319070080008030290841d40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 504200440 1250 504199190 504199193
    0x803150114030c070c0b0403151a041a12010c270b1801120e0a1b030507030309170304050d11031e07170a020102070509040809030303010617091c0c 65
    0x81c000030707200030303001d0300c9154491402c40180a46039000000480d480101650001200103802e4181da040c1c2e41c1c0000c0201c2182d070086200340003008018072a031000f00318000ca045003902c1d1845002c0420300403c2944921071422028050190444004801240c0c900000c885450f07501c452513440603c0001c1d80004025041030429400302102e41001c184044006030084651403210f0b1f0383c00003107100781c8034941d20030040c1003102d080781e240c0035100140f03812612011000440002500940c424040c06c28062151a91105450107850b07810803400300700d50400602060000b031006d1040c81740c05900451070181064080340405087c400001e000b0226148a0880d40e90b050004012041b04e410406401030068104581c0d40c1043d4807510b0700702442c55040c00305140340851200480c41d0103030001e080720f610703003028040761140003801540d0510040c030450a5994040c4001e41c02000ca40da01d80f1070b1403801c038240c8003129001403c1c03400d05500c8450440e10002066002c20400d844505000b4098102c2c0e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 504201690 1250 504200440 504200447
    0x108060d030509041109040c0c0b071b08040b0309190f020603151e10080c03070c05070b040303080708010e04050c010e061e04031b12150f02030f010e100308031501 72
    0x103003a2a035500c10704082c145c3d10028600c00107480e01200c1250103121036a8200b6054485860406014141c81030740c4002501560244a01641d107a901401104115966480f0302200f5085074000420b2000c0010601c60307004010441220507400d03d510803020920503580e0746071030061420001707000f400044001000f41001004004402c0c3d0003610b00c610003041c0f5901c058950315a004490310ad800144c40b260840b6116260607442080c0d0046200d2441d1640c0c10250352140c40c0807021141d074070030006c0204d08403010b21f01800c010361198541250130704001c07401901e00c0d14160403420005a0480401010903130001e0790031103c040a00741030300d24002402c04074540b44520000da4182e030307141041070009064104020000c4a00480300842d42008295100070302000c6403162410883d0750030f078000b0100e0305110384404c801040074000520001840c8003201aa0800c40d5082d5035001141d004004c0301c030710081c02c96408500e038101c0340300d1035045035110a02030001a20004885150000085a5901 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 504202940 1250 504201690 504201697
    0x80c01030b130212041403120a0504240b01140c0c0108040201091d0412020c01170c1207020606030115060c08220b0a110706051b070b030a0207050c0f0108060d0305 72
    0x10040c20f550b04c20701210600700c0c4900c03d4030121400d0121100c0c0c10500030021003036a02c0f10103404a4582c441d112481a14040c180240c4281e490209000200c00080070180304014107242c1c11401290396443c41d000905a941c900ea80342000142c20000c1c07a031a01804180301c00d55000c02d00300301104d0380341d41c00107c90103040b0350029040450060410003181c000340c08034510440c4580c034180c00000c0c80c0c00c41242c540c3c011740091404202d03c4440101d1220082d030401c2c2d404050034002074100102d0500d20000d1400580e400350158200d40140600c0c0d00b028026002c042d1440388d03030301c7e01c110f14024000b07003a00721414010f0000e690210f02500c0e0704c902c81181404120540780600c015a848040301130866211100351300100f001c00303135080038481001c94441f00b2642252111803c00104040c101c5090b141441d4405203801f40c0c1e4004202010440042e41c010040a0001601c580f50780c9407461416a08414051281c084500c80c114140e90020840703038044070948104030700440300d1809940074007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 504204190 1250 504202940 504202969
    0x31211010e010e160e06010c030c0614060f04050126010609050408271503090f1c11060603060606070302100218040f231008060a06060e0a080c01030b 66
    0x142401550701c030703410741508a29401003904080d00c1c40a50000f00030004c00d1440d2007102c210a102c90700042c082e60003004030031011070107070822011300411591454101ca0f9510641c070003d2172807100f40102810110050135040400352010082c0794100809070a0302c44120181c1071124841c0c1c2007100b4011820742200000b070284400074031040c20311380362580651700030812900c4030340140403030303801c03031004280040c3e010010150182034990700d0700d41403405552004081c60070301d00c212401c0c8454845d0812040b0010380000f00d00c9003200c080d180000341400059040d0000b41d51220062058a40d00817440d15004041158816a6040d1030301d403e07800c00007480f46080840748045006170071541a81180e401d900000c6404000315440c00c4020800c80341c0d541c00d40d8142d8290081030242e841003140a0b82e420007100050050a607598a00192406c01c04a82c5071203201c1c0c0742c04080045580118142c1700c8418120f400c1c4407114203004030151354080f152030282c101602c4480040d2151508441200c989 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 504205440 1250 504204190 504204193
    0x309030b131b05040b1e0d0201210f0e1b1309210f0c050a0b180d05090a0f08030d0c05040b2d0a14030903040506130e1302060301031211 60
    0x1081054001102c0ca0394800c01e8041c60528018403198035105098000582901d128001e003034500340300707016801284450032814000340c0b907404030003981110907034840340c205401d0204e103007041e02e00c0845c25100e0080064155502a40c2c5050640c040014081140841a5a10801412403940c1d180c060100000702504200490145048030300d40d0314261200d0640039140e82e8005064150221003210f0305080c00303000c80d004a03400d24002003d20120070381000201c480b080303403c440115001d00b8141d08030b1140b00403c40004480c015800c140b403010700100519400c4002c030514040c4041d44070300c1040c032a48406a902c86000d4a4540520180c4000e04500552a030f1a0015a07503000085102803094695802200301035070640d401c0d040c102c581c00c0d03050b95a40d03101d0318510340520109070409000300c407040c0028003000c50282c48030009400386040440088990030300c2c0007905c0402c1000a08428090100c3d54900b00160716200100d9045035445040344000545d254401c940488540d548017065 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 504206690 1250 504205440 504205463
    0x405040213020c061803072d020a09021c020a05040509040305160f02090a1b0507030909050c07120e01050906070609020a0602010e0c030a020d1118040623040309030b13 74
    0x268070b80050b04a1050300304240b1700310b46110040005a8901800300c000305880c11100a003035228110488128007002803100c03100c84074a803980000c5060b940341d08120001540403d0315105030030070142501c10101c582100318908130407500028000d200300c0c000d0301d0180305420040381c20540f040d0100c41c1910305640c1d6441c0083c0c100c0c6044144940001c6050b48a1550540842e01d0b070342080c4a00311001c1000d1403808894510110142c6a0f600300d841c00b81d040c0201080000f515003081d0007a10b214040700901590f5400d00e51400004070b089250034003041100740a0600c420741d8100b022541810f42c11500c858403280d043c540400a019041c900039081820311800250150701504107944070b006080644500c14a19421b0556a4250103800795106100107211008180d20000015049001078804060802d00e200b4030005450140c0d000c549141d83e0700162011080300c0001401d004203080080d458a007026200145050a280005800240140c01180302d103404029156401903120001054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 504207940 1250 504206690 504206707
    0x51813080c0304150305090c010f020304030b131205031302040902120d170a09020a12030201021201031209060504180510120b0f010b0906030a020c010227010f0503060f040504021302 80
    0x4070b9402c640b0075040102c26111010340c03418002d00441d845004507000a0a811034500011111341c150440041c096000401000c0040350218210070320413450b20000c0140d41c50180707880ca6048607286407a10812a0030720503c2158031107540c0700f0364181e404072004a5006400d0002a4443c0201083c200051090000208405e82c00c03040e641040301c3c620402c60102d903648000c0c1c005036080701c48001e5000020310001d00c484401003041040a901a2000609141d441068031705071580a80060f6205e01c80e00c40503030541c0c0d502415000262603107240c05814645003261a096802d44071001c0c811340c0d82c0b61320001e5540e004003034280b4010300d090000200b030300e4141d040500f1880000e8a807a2203e800c218004144c28989400700c0f1903104020b000c2c2c901d5a2386400c4424000d400c400d0500031555003c20124442c1700d4003541c180c2170b4100080c0c1c680f542c1800703680090700b40102c00b003115080c0315091081114541da103003000c03030340c441040d180825503589900c00a0f02100102040d1582c0030b00c08034078841c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 504209190 1250 504207940 504207943
    0x1180f021809060901061209050a0c0b0d051006081317030c0d05090105160f2607020c01090605041503060f08061008060c0d090330060f051813080c 65
    0x1d565690645600c0d11035103c900520092003424010440492039044001484d01c0750f660000c10f240f03005505a510b035444036500c0280e6000c40340d016122155002c2071001d00c0703010034482c0f01d4005001c2c814a43d1550300d00080a400c5200040900941540c00180c0005010110816070320001c0807140d102e54a28002043d03107280d800c11000c44078114a4000010201b4805101d8140501e2041c4c0c004c43d182181d80808888040c813505084040003800680781d00014411640c02c0d0070070803070101d07a81003494008802803030012502000c60401120a401b0807080c0e412074119015524510002401c52041e0081500940110352000c100ca03040c01000148020002c250340d4098144204400000d580e00c82c0119980c003c199104503001c2c00c2004207a02c0a0302e180c0c441754031a846820010640074003018a0801d55446640e035108020001a4080c4242003e202d210050304031030418600f00f03070501c000309241c0c0031200d1240722076010004c0450440800410452151544001b01c00d0380c85a0501c00303503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 504210440 1250 504209190 504209227
    0x20307030605061c050c282718020f3103171804020c0c030c12032502120109020f0121051f03031107080109080301180f02 54
    0x21400289001c101181c2d0b850314500304d03034210414602c80e0341426112000b450003410b01600c200d07810901000025029020704229640e4280c0507400080300d080c28110103015080c04c09850907841d8140c9114041040c082c00c80a002d0701c0034481844805107404001c20000c1c816090031b44014040810050440c07561a100100014084c9241070494030074540300c881070b035080b408000d090605041110481020110180203400c414041e2031700c0303524200c0049012039100016425080d00401c0c079000181c141000400711581007a01c12900c40c1901c40384a0b6142d02502081c3c0030305400b00d0302c981c031171303024103181035442c10381c0013050119401c242c0f0329100c0c002c11074520202d004150355485414950302070100150711011000019050789015200b020003130200805e04100417480404000c036504409080c0c5029500c240c40c5c114445240340e840d10b10b841d070700740e0004050341e04180424000401c08029241102c2c4203440e00124a001c111144028010200e85502e0031480464032001c0e011b00c00107107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 504211690 1250 504210440 504210451
    0x1060e04051b060f070519260a021e0a05070f0e0c0301121e0803090106140306042a18060e0603010b0102031c060b0c07030b0a02091807020102070501050a0203 70
    0x1200c40704015840c240c0c00412501c02140d9008405000c4045200c60389001004114440d10540300041f00214580021002400d02914407403522144405000718201c044552003a00100440c1007108080b4029170303491445003141020442d40c0941d07036180908112042030554424240c0b421a40c80d22490100c1c00314074420001c50705564008648403900da1000c45e41aa0107a030b61a1403000d50945070000c105541001500d000c4141900c504003080c2c1031700103140a2440c44001003002464500640250000f070014a84071790042030a100006401443c0c1c00d00c0c020080a03850641d81d201c05d40e8030b04039005544151006182003520070784038241c13a440282503c4444407160144d0702d9130400d060891380980489409684100040307100c54400088800c031045e803c44000c54216200c55020f500d40d0020540481f10340d01c812001e0041003d11504c00b54010030303140c0f0447c00c21001c3c0000a0010761129130800401d036880c408211814801c2d01121234040e0400700030303c5a1305011603c0d100940c0104d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 504212940 1250 504211690 504211693
    0x30503090907030c0e1002031207110d021b12030408010c090e0c0a09060509030c0604030605010e180705013516050f040b03060a12051b04020301030213150801060e0405 74
    0x1ca04600030f104000920701d00341e4440c04145d400009006010990100b21020f620042c07040b01201c416400d500c5128213900c0d501c5200011180f449189403a15002c0c440b020364000540e042c00340b03010784800340c2d00712101312040040c0d80d10709003407142144100c0c0c0001120394200881c0c142000d400c01c0810003100d07040d004158441d03032140000312050140e0150600007411002040005503c584043c00f98400001c003500d1866007180c001a50b981d000754001c40382c0c44d49810042068140c0440c44a61004091034071407042e4112130080303911250b144c002c43d4140300709103030021480000001038001549022070000785043c0c0281d04150034a000b2900740580020340d000c0c802ca018410825035030400801e800e0241040d0620303290344485d400040c841070b00b00328140c40015907401c0180c0c4a405540c0140e018010144079400e00281003005111109c0c021401080100010784445d51050280c0620450024107404031030462004640940c0c00380c0d54960804a000c42c45565510314540658130440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 504214190 1250 504212940 504212959
    0x305060f10050306040b030115030c030b0a0209061606151d180a02010c0f170414030a030804021c02150a030b04090c05060309070f060306030302012a030e0102120103050309 76
    0x1040001c10054800030100194083c40410601d0030720b90003c0c803021800800108040409180c0c075030315401203602c1500c141c004403d081051114800819800c6100c800c02540b0b81400307030b00441c64501c0360294440c03404003030003c14410722403a90301c50811034000b4110300800541c1e61040440c1e0f0617032090924a42c001d0500456040c48640c5843c64014004501600540403143c00569000483c2c0100ba1242400d030078000001515450b80504081110040c9940b228246a401030064000c02800c0307010750711a6001c030b0042034104403090b62081e0f040384c0046580c0c1d04507845400301c88203070344000d400905021903805820700d500042d00e00d20a05640c100280304891003004103a0359404005003907425018800e000a0400e00001c503031202c150000c98178442d90303500c101c0c00e14225943c00b040010740c0d00c5006004155080c0500703600d1703071004110295800a8481b425440c40144910981810b55401c0e05620400b0290150b034418a07065100804035a074a003800307074480e408844064810361140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 504215440 1250 504214190 504214219
    0x5090102010e07050a091a03060426030408071211012f0f0318160f0608091606030b010e0405130219120201030213081c0f0201060501050d0b040204080a03030506 71
    0x203801021101d005085d488450301e0000200c00806003003104900d58180c0758005046504d0811285004a110340c3c004d6a04000112940b00c02c101440e9041050b0350040013403001240c0710300b042d41d6203640c00250403600b00c0944903080c1c80d02100003e201e5282d5003021070204108450a001c44010403540600040d14450202e2007040e40c0720b03440f500401c03d02e040c008074000e400c1d401300e400c06020403c0d0403500402c00341c085103100800360b03030310000d0032840059044c03200c1940301c01c0c4207800195000003050113241904407460200e900b80112810146d841c845100168400c00051642410160082041d81072501e07050b110100d420109a002c2c82510520100c403230744044021040b504440064429944140d0044029500c00f82001c00140819940402c1d0110240325402155001d0540e00303221760190030b03020b03080302c201105040035640b5250013042076036041001c50741e03801c001c014001070103040000024000e000f03640180b14030b40703d50003100007050740541c0304030700607041100c480004c80040b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 504216690 1250 504215440 504215443
    0x10051506040f0902210115120c0e0415171c090612020706020702041404061505100509130c08241809010f020f21040503030c0a1206030305090102010e 66
    0x840c030074002c02ca40a41c00401803010554041c10b498084880005001002111075020340032080c0c001c044410003101090a0031a0030010410070540202e400740f240400c090400342c011300d00f99001038000d54580e801206100000412b000140007004c03501e000310304140c82c656944030f0300a00c484504503694080da2000701c1c06091020219102da0750744894088042e41184065000b21070704441e11038003803100ca40160fa070790154418601001d400d901c541c1c900340c100b002c11380764000e440d2015020111000e11968450402d0284d50040b14281181c0d51501400440d0329200000001c604803450103182d8088264800000e600414904180e00c2e40710021401da20316500d14414281e500c20020640f9a051644004503d640444502c0000640302400301c000810303070f03020400c0544022000565280d89447c030b40c14401c0003060510807581285450f55132150303a03104c0a00980511640480d08454140c85001c0c0c0004900c58558240029070f52460081c1098010003400c50141d42480d0402d10a801e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 504217940 1250 504216690 504216697
    0x20f040c05090a290c07120f061a0307090c180e0f0f09030423030d030501091503020a12150614130506130b0d0c03080c010606090803071e0510051506 66
    0x124101c040c00807141160042c2c40a80c00761050500e90301070b1280c0021204506521f03640c055000e034001082c0c242c014541031040b25500503080b90700800c00c1d6031002d00c80d200082c441064035940d82c4e0006c1c40c140e4840c0c05407044030ba44d495203040300c00c82000104540a075620a00c0c010010340d5145682034070780f4000e400c5611001c4031040710b40e51003403100304290b43c0741182d00c4009245075a030b1504107104071008242004d08121300d600c01300703885500420042d9224401c211422241c1c0d00c1c002c24007420341e4001011000684110301ba1050028102428810354000560620503400c01c10080300d590340070041d8851040c2c1220034411000400c1c1c0c448030403500c0c000d080c4a000300400002d11120b03128034074002070003412012900702e5402d20f803000009074159102c0c0e01450007484119190f690381e440050075900b150b001541000f01e24041000714000000554514940c001c03010040761229a410350340f1048001c00244c51485002d02e280300d4075520364840f82c001d80340507582e964040303020003c0c01020311 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 504219190 1250 504217940 504217979
    0x4050c0a0206071b170d020c070807120305091044070804020d03090b04080a0210050901050a0e041103010e0f1f0501110f0a120f08041707020f040c05090a 68
    0x900400356030300161100c0031111110701005178590134400e0351032030398049803c006255100c65010b010f06000c04402001200300901e20002490090319032650000d00c01e014841c1960301803031800d042c1100710307400b942b800d855001110350b010030300552010480070f0030b000b6400540c0700a00c600c5020031780041201841445020281c54040b415200c3e0303401c0c41a00d003800d000c16800c004000801103101c00042000b08000c1c4004001040d08040c540100201c80c0551950304044c00b20400a1000703d903001025503e4030100380c00c0240c01c030119000070030090300c007102d200d202c061400000812a4002904200c2c003030b00158002c00ca035562000c1e5008030401151003120340b000440d4804201c603600c11811000c05003010020784030074503c4007141910b07141e030510b011902d83c0c0f0341b01482804035901401f03c42000c20030b882c10015604083d2901003080004a48081c812080010070000350b4891691766485014060700410410180c0500180150010510944200105a40000c034810002d14084010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 504220440 1250 504219190 504219227
    0x110405010b071101022b0816020c19030803010f060e030706210f050c0a0f0311031306202511060903070816060813050a0b06010201090204050c0a020607 67
    0x2100700d0f100d03d54668540b85000741180320b90088408882580720320000c0820284207988044000740002404000005002e40e0b01c1c01c0407440d003034801760341c0047c00041151068850045103e22382d0070032007001000d82c0015041100002c000030381816001903480c100c400b5607480d9000d00d840304041584400c49445188d0020f9420b01125840790500a440d04144500e048001406019a40343c80c050700e00842ea40783c40c00c100400e42d11002500007803a040342004a28040054841c401400d20060001409207800ca8600c40c40d000b0410a0300d81c41016180500c070303282c00c00505903a03071758016070b07001c0c15422a80504414002000e561b205042c51561a4000c90a64a046180307040c090941c00c0100c005515126054001865142c00d001c00581a4400c2c8803048a5505184c000342c4819809882d410b0800320002c1c40c0f00100728040348912078140c1c07003104031480d0348481004030702411024a010f0b45c0a494038050280a100f03400050000c82c4c01c64003079400594958400303072102c8580e0307120b0034503d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 504221690 1250 504220440 504220447
    0x27120a050c0f13060b1801091505030406020c1f0e0c0d0204090c05150903010b090c0d05091011040f0f061407210201090501050609010b07060e0c030a03080103110405010b 75
    0x615041e40305114090340901090b00303143c80d044032a000d4407060340c0200710046001a002600c1c0d0300d4104900e64000342820400d003454a007038a400b031400609441c1200308078001c404602003241907011a410700d00a041201c0880850360b0202c03811454000c20004003520305a00d064a90801040d0071080d2200208205690301c410303000d00000e0310b9000c10444402c0c00c440004101c607600d11504124117030f00e48014540754008042810b00b1280c075540700520912000d0200300a0700308070011a00724000318607003c1126180c400d071141c50802607400350040d55042c0b0800c10b4100c0b0545018100721412805c0700c4003650f03940c05140303001e0365480c001c00740050f602d40344001c0c045a1041c020840c443c42940c80c00300142000c0b0030a07074010b200c04503180050751505c007032a00b401004d000d525004401120300c81895490b20301350041501c0b603401c006200700e440301840c0140c18400c0c828460400c074040c007034501281031480d0003846900b007404100c0d50f00c4e20807080c40c05542810b20a4905a6040c610420b24 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 504222940 1250 504221690 504221713
    0xc0d12180614070213020a02160b1201270528050c030601050c03040e180d020c100e03010902030604060c1b03050f090301020d110a020c060c060708040827120a05 71
    0x4580d202c00000d0b40c1000e090a417220610000340b00815082000741c0c003074103145540d1000b80400c130081d0f03842103222000c1840745c1c1c080202c100002c00c2c11110300c1c0c3d4880c00c403500600a18502161008400c4241c0c41c649010003142e0120302d031041002024482c5000c030b88c1001068001d08690050b81c40f0414601d0601c0060b81da135015000030600041c1f5031040f24180760f44c42100780300310842207a030343c00880d4924410300c640000400480403460840d001a040010040000c15050b000d8500034000304440f01200603d03645003036005e1007000e03401409640e600c1c601410b00b0750280144107585d60000d04410f03108250b0700c2130210b620802590568549241120581013440c01d0f40008000e030303506550810941164100304d21030044031036000b850a03903e9040002001c0d041c134440203845400340c003081201152469003c1aa907511503000d091080700381d21541805990b601a500300b40702c000404a13124208a8600e52003821881d008851581e400c0c1c0510041a488a070715141c010401d0b80310008050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 504224190 1250 504222940 504222977
    0x2c0f01171b1005040305030a0203070c050405090a0303150837050607080c0d02070f0209060105040e18011b030203060a0f03020d0b1b16020a05010801030503030a0b030c0d121806 78
    0xb4140815032600c0707400d05489440d03a6003154002c40c0c00c02c1c0582d1001541904102c680d5200000420048a0800c003502c1e0000360162603042110008007050b40e54079103030000c22224406000070700b4070340084510107181204100004401068448855940803c84003904062802100c44c60703648040600516140c0c16030075204003002500d50100c1e01001d000c0240c00400b54406005200e0140e441043d003440140184000c01d00302800a90400404000500c40c00162111a41e04000001000c01c0c0c0c0c0d010101c000d500400d20540c02c107810b0100002007086c400c0d810b4000d10702584048641d85d40265481c160700880c00c0082c800250040c810b00e4415003c2965030352081d50083e401d000c008110041000c2401c201d5114000b01004001d080707504400350b04010042001418080c00c00240c954110f0f141c2d9962400001c2c280b0a0b281d8503a08003503041c0c2c5092040c00c0c81d0310f0700034103c422421514038200e506d000c2c0001170b1a00043c0041c0803100701e0140504060115800382d110119036910190551 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 504225440 1250 504224190 504224209
    0x607030c031b08030f0a06050d150207060216060606080f0a09030c0b070f0e0301020f090909101404051c0f11030f040e06030d0203040303092c0f01171b 67
    0x41d4280010380d100d0742c0900400c500780c940b03502d110305406656443d1203082c2c400102000707090f040c0e40503c3d061080c4070035210361408019041c0c01030807111101c0d808a1003840a841218802000d02d400030a201d10080404005c0c0740903503204400500c082a00c0d0f00d021036210400700c070041b450800c000301203000402d0700c0d8049201070380070f46481c082d01e05040c0c80d04400c820707013551080d0000707032a02003039070545070300c124050307601d900442c000d5291001e030b01d01b509014040e05414034171070403500022803441d510420116100c0d070a01c44c8180600000880e580000c500d04580c15146405815401c1c1c40f072400d045684000740131162510205a803e50b42d0403140044243ca40ca40284010400b18500540b0030001d080148041031040116140003018107003400c0351008142d06540c010300040c40040e40100c901810340d10344152515040214410001d0502480741240e0445500c05041c007003101c6404100078183ca062600303201200222484255a403031000c0300c009011050030701100041e20340610721 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 504226690 1250 504225440 504225443
    0x51b0a09020d090c081e0106031725420b0402120a0504021c0c0905220309050a05010e060304171c091203020304030e1002011d0a1505060607030c 64
    0x144204460b42d40e01007100e4607800c07a40040d03000030560280030448404183c0030611b000024040649540d44803000310b00544507000d0f00c840c0128401e0701b80007071144100301c4403050f441080b801035074900b0030f221001a031520210460b000b140800030381c024000c0d410752915004456020030305080064403801040340019245d41b0135000c1003510001d2042150590203034005250001d12401c00381304101861880c04030072038070000c414010310f0104003110040800c130341038240c02260b0380e0ba901c0e90111143c0c8555000c10f03045802d0200134803d00d83d000180a041d101c0c1030752090f20310b54a800064403c01084901d0035030200c07081001900007041c2c4041103005510500301c4908094150030b0394040309502203d034141c582d60f61401013050009a000c8141074042504003146035042035200141070503d503003492401102e0001601c24101e200350300c0030350710160041e5000c42803590000899212604003800b60b500703030b40d1394144211100441c482c1c54080c032001803001d4902a015901501e41c00c40c010300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 504227940 1250 504226690 504226717
    0x51612020c030a2901121e0c150305011e090216060603080c0c0405070e091515090108060f06190c0803070c0317060a12050709020c0604051b0a0902 65
    0x15110441d10104030301d0f20703880d03c1941a001c011002040c48082c04000c03011240d05014040010014100340028403512a40c225849401008001201d0140404510307001019440305420004278840e0142010b82ea6010360b54043c8130f9a41da955000c0d442c114039007507410808502c20420803443c0c0705036005040329407050000307104800c141c1d210941120516070082d1085400050400d90020382440382580244049a04002038145282c0061103948040b440901480c1c102e00810004072031041100b540c414002e21104401d4411407901c090f81d04546c22160102e044807020801516101c001a940e620015010703034100f138208422210400c42000354401030190b5540e003c0b001c20000801984101030a4586180304005850000d143c0000c21140380b05000078541804441d9846d0b4100d0821103c9002144621103158201541440243c1e403150310380d14070008030302507460004944544258003a4045d0ba0590b80c044030024003601d048601c60354480d1000c0c80c1441051415406807001d15156070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 504229190 1250 504227940 504227953
    0x50d11070e0106090314072702070f1407050306010b030705130803070c0f061e0e0f030613030e01020d020303010902031315090c08030f070b06030c0907050705070605161202 76
    0x1c2100c1003030030280c0288000a85454050040c00043d0300040c204001850042200501d415015100c2459403411000003005001c080802c040d03694054031006504640003411504080c6080700e0a03016131001c40c05140541c5a001034585004160f15040303488080b142440c0d5330302e00c04200c8040e030040000d1848c5002000d030103d80b620040025042541c49a0800c13034140e4104140089120300c640d0100b002c010900c03800d059250400400c103080200103060203003a1381c0c108800070304403030f030311001003a0903104000c10410401080502d004070580a900d40c0d0240e40031050049856411030240c1901580c420001040206180d9008580c0100340b060161860151355031220407402041c5c007803250941e00d984484e024000c00415400c0107000c1040114603001d128861201c84d0302039900c014102c22035107030008030542c0b02442019801c60000341445110f03d015500904a60040f85003560310303100d803d5000c10f0311270041040b80c07544c0e1051581400d80041556842c0844044801032200314010172 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 504230440 1250 504229190 504229199
    0x607031106100e33010306050d05010b0423010311010c06090501020c07050105090d0b100302030109080714060106081317031302010e0409030c031b152403050d1107 72
    0xd00285000310260000d841d4910b140058400c3c82c1d090242c511036400c2a110000540c01010041c0f90f02c4201c0301c3c1d062180034050820050b80108030030707409160400313a1078890208000065002c401406011101006206103c450207160015210718000c4010441d80047c008a08020304c02055544145040400b2000f0341d51814180d4020720f00490f030581d0040307182d15100d102848900040c010a00e016810f002038400007030300c00f880e040c40107400c1300400004180e003412000c10440155401034000c0c0840040c0c1d01d01100306610200c03050340c5800340c048802c807140d0710102e18039040fa45c2a0b0340781c0d4143d0b191b81400c914500d2407040206c03030b03103088505a0043d1901b0300c4055441800282d40c074140c54245400050401035862000d244074034544442500066000714030708080b81e4244c94082504075a100c000c0800c91114080540039144004000c905522a0b4104504940095085c2d1420102d1440d43d425642d0440c00001c0154000d410083e4050f8403c1000315024034000b02282d42c0590b1344d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 504231690 1250 504230440 504230443
    0x6090302060706020f0f0309150601091a0702060a050a1b022101090609351206120109050309040e010506010f27030b090601081207080d1113030b070e0102030906070311 74
    0x841b22804c5155008810000e000c07609000100017440000d09a01e21480d041000910f007110302d01800c0344030b10400410b42103051b0141c058462540c3e0261101d035507031500110140c00c9410070484040010220f2010080c24001104c065a070340c1d50141008480c551038005641e001c1a499050201e25962501c032035021501034015942e0701f6008048000b10307007042040c0c44e05071200141d83d0340103413000c120a907030700407146900b100e0944d45111490b41c026180d000000d1140f0101d01281c0e81c8640c200307424002484404001084880030444040009040c5019524240c600c1103e4041c0451041c0c800c240c06c1501508003c040007001075100102e5480600c070b0000e6a4090742c0013075aa99014200300710621800300085405400d0100c0242520940400c40d42040e00c10700c03000400000b00442c00c80402c0400390408500c0004c261100c1c0d03265035034240341c10740e00b40142c801a41d01860010224526030701402000007030030010381c041c5207020f00a9050200c554002102102000207500114615400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 504232940 1250 504231690 504231697
    0x2004020304060605011202131e080601060302040906060c11040f02091009050f04020304051f09060c1d0a05060f0304020f06030112151406010c1505070c0303050f0106090302060706020f 81
    0x1c61440090914103200c0014000b02070315030700c0c00f41b0038810400300702c18800e100418000c4235960284030700030f02c9644403260101050703548002182d1080000108a00350103401402c1680c009910400045580c2c200890790b00208020150000c40c010f500c02c00f090805810541c020101010094540a542ca001c500d04201000901c1d0015080510a014514042e958082801d00456081d402c60905445a50311015903000c0d60000c14555080c2042e07415160300004107958010f80100005240c4070b5001e00350151000c181080180c41d125203031401d140030000c0405070707940980014201051003900ca016036102500036a0310440c400708013070160f59480021800380440710030300941d200345072409507503e0720b02e0140c0500c03c5007480d82000e030842007a9182540800c091074140408400781c141f9980c40c40b00701000c46e0b001800c000c100051150808138000e4070030300c070780c2e403c001d02c0d6100c21441c11841001e000340d40c009610a0380030405460302001400441e40200001844e01e501c2604401e510707030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 504234190 1250 504232940 504232943
    0x10212030f250309111503010e04050109020315060f010f051b070906030503130b09010509011d03070618090b03060604090305160b1e0f0a020d0e0303010e0a0c1b2004020304 76
    0x4d0311944203404000d030b417002c0840307421801c0e940d02e8085010090030105a0005020740b0785d280d6040300001d02805000d41100710a19005410788840c03413802085000c407800300b2a1064000c1416109081195100355803c1400720901ea0750b045c140303590019101907030486804100e0702e40c8542e40d03021403010140d03c2100003c6210b500290798a04801044e400348590a81c000ca02e59402400f112415980180480700912800d1038041049010001d040001007006100203415104450000c10400d41285030050f240c1101c4910307443e0142c0e01e20240c0141c1f50640c0c1125016009840400d0fa281031540250400d40c2c0300381085814207401800340c9108a4a001701906c1ca481e82c0003c5c0441155210f030b01c1400c00c41c0d043d21004040c40c0004046600000280903c4405540010802c40004280d401034041c1000101504d5176969544101086910b0544074030764100d00c0c2c10b034181e01150040d07194030b460300c0011141e02c1084d4490307110100d480751f4041171440d200c0003150400785d06a841c0c2c0700552290f0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 504235440 1250 504234190 504234197
    0x1082d0f1006090b0a0305100903030e010c0f1404080a0f0f0b0702030310140603070c06060f141f020d0807050910020f010e010b060d0213051908010506010212030f25 73
    0xd034a04403c4500313a07103004a5103405820541410302c0030a802040f440700502007440081108131103460110003c02d2030f101141206c3d440d0054548841c0d84c032610125152101e0b43d110005001c020905440300d00c42c42c410b441e2507501074403101c00000c0c0340462146101d8050a020b82d80c034000e58880c40f82140c011100c038001a00000100b01c9d100240d90f0154016000d90304403015204030142c00300d04103100c09800a4203011030710308007004110240d0807000c081c0c40880f0000c2801550764080f0030030001c0a00015100c1d40309000d20060501c01868000024a803030380c01811741c004902e000b5950254058502c2040003002c10000c40e181c1c1b52a90700c000103007400c4c1c2c01804c2074440380d4030103030840d19841401c0a650b41403401c0c0c40c00341e956441c240c0c0c40340f509036000180da589002c1c118618200341c0398401c941180103203544103404c0e0100f4450004481d80b900c0240039650f1090012030310345031100c1400090240600c04500721410102201e94010f0000700d0540b403008054182d00c040100d240741c03c1000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 504236690 1250 504235440 504235451
    0x10f0905060f09060114040f110408101a0108040222230906010b250f080705160e0c0901020c090c0d0f110a030c020307080c070302040501082d0f10 65
    0x614031442c000c0ea51090058000c3c00e429410424401254030408100360310407030700c504203583c0c44001c81d4001c480d00c0c064031544a658503a41c08895440300b9054185241003486c1551941d050b8104024402c010f42050b500c0920956544d402c000300d24103010f0f54500c0d111000116400c10b2040c41c490100302c0ba0007500702d079070005000c1d00b0380c840a5000402d402802d400c440d0040000518107401d440490b103014240344454402c07808103c01200b540b82c4040c0442441417101003c0c408000c0007804182e0081041d1466000072154031521501240325940f902c1200c1000a00420001c0d000742c0420881441510303403190100c400910010000e45145884803400680042c0c04803543c8900040701c65180d2007405600d00e00ae074840242d01610114805050711211020801d40c8240100c4022941c00ba15180d11860324042c540d950b40c6072400100e010707505d49000420a4a0001940c45145284a00540d54100102e901c62a104411401c000d41c6215110124007003d00134424500c124480c8000002d0707 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 504237940 1250 504236690 504236701
    0x24040609180902090105010806061e0711090114040f0f091518020109090f1b050903070b0301030803130204110f03040b011a031605130303030b010207240c05010f090506 74
    0xa08a885a07a10300e409242c4030b11000141c4602460b24115602400c06100503a01da00103c0c01c107204182c1402c114031030410034113988442c0318018018aa002d200311010801c400300c14099004003e0181600d00786181c0742801c120b00c3c10b90440310300711005041c04207000850419030802c2d9120490203c505015410009070a59264494604400f03100700c4000d805100c00c1d000646211114050045010346400c6840401c200d550040d102180d1040c2404401c05164603006000da001501382500c0f9001c0da1000107488000801602c2c1a40e81002e2028555142c00025041c541c1c540f40e02244c110352241002101162050041c15142c504c482801350707680303014038000600e03040581103a8000c03030108000401d50b62140054035400440811140c861004141080c0d60038000c203454141000368503034011082541c580c101caa101103080c0c003111034a80e140c4c1241441d402c1d01c0f0030b01032140e0f415041002c140e03d100304245031103d40190000101c2010300d48082c010384180f004143c0c0d0962100c400c2c000b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 504239190 1250 504237940 504237959
    0x121e0b071e050f031008120423010504060f1101020a0302070209090a050a02210601180e0d050f1e04120b07020318101209030e0310090206070224040609 67
    0x1014450251804404810741100c080c0060182c1c18074141d0011012001410080c2c00710340660141580c1c200300c54013000f8403200144290b0150045603651aa00e00c907a1314041440308400c42e15501c140c4071142001d0070a00708440f45ca002c9601102046100182054021000e01c003d0115950580d009030b541e400c10b006000d190880a400ba00e0b0075485800d84001203140071400070117140d030441c0d480840c181d68140c3c01c141c2e401034558000041c000c1d500001800b0048121810820401c5030313051040c0003041c0c0e050342e24ac2c2141003240c1b0200301d00700206e1070400701003002040a4519201d298401c2c1540c100503140c1900207800422941e0340900004060066202c08240e00903414801545070110312a00801c0800f401880240039011000c0d110340890b004640560300c042410324208422001c6d41001086020805c00550090040da1402c081e480d0700c0e401511450b58000e8220741c601440d40c0d003405401c0802c0903107034209114080c1d544c10070801d40c9001788010b160a0b520041c0c900e0074103a030070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 504240440 1250 504239190 504239207
    0x6092106060111060606121b0c031b2d0106090618060b0331140604030f0e06030f0a2a0206010b03010305060a0c020309030d1d040213121e0b07 63
    0x90f0103a6001c03108000040c1d0361b52048404101100c07040340c2c0c01d6100d5840c484015a402c01000000800c00306070800304800c0000540890b030380080d041c20301030710301c030386400d8681024603040d880021a1030554014000e00d1190120400300c5076000203005a5a80c5070740302114400d8003c80030340040b46a40700c3c1c0381030380c0f030007808090300055060900d5820000403000c0102d542c07507070b405444c00c11044442a4495500101ca14268010810044d51031040300c09585400007100e007100801d84a0800f401910721030181420728035009885540745803906051007a075240c00501d0080801c0e01c590703e21030300020352650710301c1c00d81c1c803115802542c0390180c02c06820301f00140c001501c4844184010000300c1c100140c2d1a401c91040000001c09250714a0124251f21814141c21b03010b115000e01741e242c0700e07880500780c1900d0409140c80710360880d4200030401a031003a10210404207c9140090210414452800e201280b281101c0d400301e500800f4256000717400f0000a071003c0440c2da0400121a4020084 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 504241690 1250 504240440 504240467
    0x6120510050913020301140c090405010603060b0d0e0a0f0b0412021908031902030c0c100902030303040308070e09040c092f0a090302030a050a14011a060921060601 72
    0x400a00c40c24403001c681950001006840760000072500c0d082591000c0d801084007210803d03440e416842d00c40c210407102d501060065000f0b920f804000942144280f2408003a5050f407001285002000780c1c10001620724000c0403100e900131044c480f4000740750f0304100c0c9a510710a100301401031509051491207550005490410741d0888404662914214080b00d1400c81c0d128900903169251108102040307000c44824400c030b07910000034001040104409805111020310466010051f01c000100a5a8218030001d405034020b00205000034051b0407030310340c03001c00c0303107002003400c40b02c1e20005806803070640d4141c80000c0101402d0100144038000c00d000c80c5243c201d02e8150726149015940740100100c0c030b42c4c00501c00820781040030380c13140d40003030011900103044a11407010303030405944074101c840048503206001c035a15880b854040c00390403000c2500c01e811064002c030500a105459005400983c0d010130b40d0741002d01d03a01401e007440c4845808003030052500749404030015282d0003c1350f06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 504242940 1250 504241690 504241711
    0xa05030102043f120e0d11031b0a03063606110306010915020708011a040501050a0f0e0403260709050d110409110d1b052b0203030c0106061205 63
    0x202c10340701d400d50303011041426480740d24461300600d0403104031440041c0320760040d440f0180750326000070312911465244080500310705958003031702084440640621725034200340d0030298401d020004290304da0b101c04c0442807880751001801201c152210000a100f41017107054901100f1407a040c40814800c42d46c0600300b030a4070324594144000064001c030007910039200e410030200140c40503c0c0c424008030008200380743c0207000f00e41c0ea452148a4808030500101d018510705000041c4900e0286540d40841b10a9400b01c1c1c901820442c0083ea0008001c20a0b018402e91602e1003c000444031902c0100340410401541076080481005005031002d0f80040d00c034440c0c82a0207000304140760b058100c0210202c500103010f0034103281c98180e03400f0030300c94560301c20405045c40b42070180b0300e0205004d20394109006500303280c0f150b040000540004140c281000303405e022844e003850200407220800341c001002c0301d0401500c408201d096070107580201c000244454400005041e240c016641c001c1c8007103c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 504244190 1250 504242940 504243029
    0x301090522020d02040b011803050604050f07061202181203070302060705030919050f06041a0702010c050f1305190e0a05070f080a0e1002090f031203070e0a0503010204 74
    0x200018510081040d002c1c1c429079481c041c1001d6a030160b000d00c2942c1d0f500b400f100c8851562420156140d070bc084400781c0700c901402d402082a0480072800c402a01c84945034424454503124480c002034012b5400000d03101d085a01080c02a0b99040210316001039400085a480e0f4140c80d00070300301000a8965818844d05000b0b100d000c06001ca981440461404400125940075090043c541030040c94a40f600c1d0144c04188800d01980280c5519100b07102c124000554660210403822903c2d06100700b400500b042c050021009030400080020100b407000c1c11050584400006100301c440c28400d00350a1401c441c00c01414944081069000c13580c29030410003850a80000380068245002c680c0130000c1c2c035030004402c000035600c102501d0105c4800c0342c00340300c810b03480c0304025448403455a2045885642000407441c0c00540d1144420001d04001c1c25a1904882503802ca6992250141c0c0325108482c0800c4a4400b40b002e0001803050b4591941c0e44082c84d207400c100d40400d405201d0b035800c00301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 504245440 1250 504244190 504244193
    0x20403031209111504030f080405030d0206061005090d060608010608012f03071214250f050c0a1b03060b1002280b0412020105241011030301090522 65
    0x155610880c60f202601c02e10300c011084d140304040b5124540000302072035294a4031009010501c0f01901c1503505c1030b421610000c3c10800182e030388201c22a100380d400b210424018000912940c0640000032014210f40200d070456680c400079a1210303007114030700d603668420800100c8002d01412848010018044807121100100550011400e2401c610084800004244a6441042c00c0728185003113103420454000003155840d104001034812a14078401802e01c900c0c410280024100c0c4070b003941c0c56403c9190302002007030b49e95410000c81043c1c036014030a248800309040c1700d03036402504040505507014030301b90701d031404c212007429010034000c846071090011b0442c3c0005914100b681c00d101c600d03e00c1c28081c1805c00c2c0300c40c6880402010100d9403000c0c80100311064070407000603602d6800920043d51103031f4a146800616505101c0ba941d500c1c0142412403c00d07284003405401c1034901801d1076034081201c58503580c02a4440403903d42e8640411114910105102c401c8100c2c07030f100f06c0c4201945 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 504246690 1250 504245440 504245453
    0xb070b0405010609020903100b06040e01080c03071a0a080c13030c0807090b0612040c2301020606010f200f011416051204030509030f01050703020a08010509010b0301030f0809060409020403031209 86
    0x2c02d4091072110356038427910105940307040688000300a0000d01c510307250b03190841d90ba161b034602e0580601170712030004040b428035814007007190500080c0c1c100501b03050034541c0c115029140035100b607640f00340400091000240c41c46605d009076008a0302c0d00451443c0010300f600d0034225a03c02c000592806000e44519030b284012a980184024802403450b00d550410400c2c243e0103a10042030310101424132580100310100070040042c09130251101580c96900658251120050312000158950030f1407413546c1c80ba130380041c01d184103201181c20094440102ca402c6900c04100009518401c0e010001c1c2b124494042c4005500f02d4a02035013004a04004000d0b1100e020b00000c0a00c900400c1191840d141001140504903441000740316a04084401030002c3d40005041d5000442540001c1042d0820131402030485070058152403646c0c4c030b0740d01c800da20150204003c5410b40d400700010801030382d825004c0c0000d4501c0c03c0e0010381c2d46c2d15500d00605021650b590700203a0f06c4c184116000450b03003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 504247940 1250 504246690 504246703
    0x303010605040e0a0e01020d0f0c030b060313080c030c071526090102071b090e01140604020306060c0a08032502250e0f151c0204150b070b0405010609020903 69
    0x101604003001685588a1107009885d040c91501c0e6076603c04a88003503003450304e40000b11090b0100e0b01c00c000c0410441400c40c10b480c0c6005c201d940081d01040403d6000704650451a11603016141c02c81c24a1820315159055900460b0240f100394072080050080009280c000d0b200c80307107907050601950364103001c108804059101d6040d0984214800500e80500c203404440e9619403040c1000c094503280c44a50351041d036a805908080c6103001e070b2126064205105000385950070032100342180d41c80314100000707035000a1000e504080c0074040c8101095027007000c914054441c6403240d03100d240100ba040c400044440104418044880910245075008506040864024502c26850110b54040c04d800d92030654403103840d061001e402c01c0482e07403c200c0814095849440300c01000b60400081081892402c03101414a0042d003650000629240d4000c0b03014070f01c4225140040350350742c20241d40300d800000050720b805001600b04000c2000030310411014102c003090860408140b04003003503550b030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 504249190 1250 504247940 504247949
    0x105061809100312030507110d0c29010825120212120408030301180606020d03020c01091401090b220803100905040c0305061003080f071103100e0f030301060504 71
    0x90070800305100903801d145080245820500c420102c4514000060040c00215042d00000e000588102441c180104511031403007501d599150079200035441c0c40801d040845d40b10402249881400c080000ca0178008600901900019001020301e01061124130f20b694807009280c0c00b0903d0041c8001c618502030724015580588819180b1600c140420386409001074000f10601c4000c2400110040c000000f03505031404594250601e969114a013402d94456016060150700041c0c02d4540d500d1181e4080c0103001055000858640c1c501c0d251140030802c3e46103c0255651541c810400f48070036140016005118143d8684e00005c0000704038010103840000182000d4000020800791850022444090007241c2d87c10802e604003450802d80504032440103c079580500360005a0003869905080304030b0343c2201e015494000c201c41e450403c0e0780f0101e000c035451030106100c8041624100b100c2c00c0300050700c01c0300240001441000310324005035258400013540c000c00062044580c4902924200c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 504250440 1250 504249190 504249199
    0x50609010e09010f0f0e0f010e061305010b040c0309020f03060121030302040f0807030203280201031e0c091703210615030a14010605031b18130203010302010801050618 74
    0x3902e80b2802c040c09440a00e1420380f09508003100c40300b140740144e10a00c403000b076030710071030b038650600c4c505560030b88041100314440c4e03800c0940000e010408810302d807280f69108270000214099143d0004d0210b8070b0a0a0319030002c1d941d0b440c00021403c240141c000c908004800409066141451040d03038865001c02d0444c0020f500c0c0c0e11001010302035010364003c0c00c0c450400e04240c5444440c01c0d95601003503c81030b0b10a11590140201e4841c5070f0000c0031544c000c4c0740c3d100003044803d80040d806002e0401d80d512285041d215480c0340081203204c0e5440b014013039580c0700340c51403a02e02e07100d0107000001060007181c0c20030800c440100c0e1a96007203440b1403c9424849590303079070b0200015800d4844100740c4d283c0010000811112101a900c52a2a40e40d208405007060f40c90348400c4401d800120307181807441c0c02044140c000c40c0d240002400e1409100094514005280800308008901035000c0c2e111554000c40140704668001c18124054041076a119080c00c0c00b06424650f03014210380018040c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 504251690 1250 504250440 504250469
    0xe0a0306110f0403150c0513050f130c08061315180204030f0605090d03060302060d1113031406130b0a1a0d150605010e030703031202090a060f1205060901 68
    0x220316200c001c2da040000e03a581001d448503076a0134070842c002c404c0813280d0300e00d0f40b40038050f440c603074000c070309441c044c0080c1d000c106080341c144818080c007502a52001d5500211648082107050344500070200840110f031307142501801c1001c1404141092a512103034454144081034616540c070000c01c00071540f003480210000404088400020701c1107400c06444180c2180006091010907004680102100c81c2242e094100c80c140c110101c4101c1e0000070b510200400403840160750ba600145041110300d43c5891600da400f10f4544010710041e4800c44998440c12480d94103810107001d0158001030202e0100c41200303840e690800010790040a92450a90b620f40f0408003a000124540307a10801a1080d44180200e01b0303c10242d814080300b03031074201c1c186200440e4a52168a801101141c00380041110070305541d0299600e2a9254035624100e07800d00a601b400d40c3c0d41e0070300d05c0003058141c442046601e450300c2c0040c0820310781d950105416061809109940c1c03140f8201c1d504441c6140c485a25 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 504252940 1250 504251690 504251711
    0xb03150108120f0d09030206011d130210030b0a060e0301050c040803091504090c030b10090506090103020d11070308010303080106020304060210230108010203190b0a1401140c01020315010e0a0306 86
    0x5a8082d1804d007146076440c1000c4030041503000a100c42c1602c1d010134061810035610a9030300341544080754510440002d800e40300005003020350b10301400040c6401c0100b50b07441c0e43d40104014049552103900000c1781052030710b2580c102845201d800855640d6010703c2c3c582040381283e903030712a604d21140078071860351540406035560170030384020308001c1906009621806000402030119104041d115910305500300c89040d001e15181400c542000c0c0c803943c181007080005600942000c03c80e00032203900d80307450101c00d00380040200a860300c2619442219411801c008114910503040082558802c000500c103071500011070001001d80c2c1c400109001e8441c5920524401e1181c1000d03041007056000030550040c1900514401d4030301480f5000e031918295860301c140d40d48240a283c0012a5204c24000440c104940c8042c040d0b040c10301003011141c00c4810039603a030091130075488507540482401400203080d07140c003d44030001d20304080c62000000000d454114140300003414540e50755001007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 504254190 1250 504252940 504252967
    0x2d11091005070c0306060e040c080d08040303051302090a05090712080403170c0d0306090c020c010c0f0201110607020703061109090a0f06050d1a010509090304030f020120010b0315010812 82
    0x4000d1540300e034090001c107950b0150103540c044c081d123007254451480076011488030130004424a62406555411915441342d403410703070081c203001c1c01404ca0607041c64014030240c0c0f20f8200c5107000e00c83e01040007031030f49001c082c0c0a08025542d000318400d9441c4005c01c001140f0210f003600c0030342c0c1d0000b03161607050f2142c0d051103035903100e803100781c41c940c0c0030344440290002d825a000400301d40041c18141302c6a088188200e8441482040182c04110170880d0b40001c50f41100b52203c0c00c62040c10810740003810070030918640300007104d4110043e07100810a00401c2910302a101c01e1071082100c242c1086552000659207a4000b0b10500440340e43d994400c24050305034201000800b0040c2124505040354140012020000001c045203614030720000902401c080001602c90090030026600305400e69031440b00c540c0200c8001d80c1002009085418035080d506e4a408807118503000000303200c00c1c40800c1c1030030040c1560010107664041c00041190640108030038a49052504403d90344064005000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 504255440 1250 504254190 504254213
    0x1303050a1a0417180d05030904050709050a12020301020c07170f0105070f050702012f0111031b0703030213090507030e1204120f0c080312090304050d08030402042d1109100507 77
    0x41d17601c00e4405141c00c041c00800300040598000c00d031402d100f80e640c0d2140a54006040d481070b990400b02c01d003010409242200244240e00388001c0000d0f150187d81c0b04a1443d2000a0704560414004040c0d41483c0040410000c48086400c4000703109500e030034070014040000d18505e1105001000070b1002c11a88200d03007003940050a10804800300001190240d81c3c03c0c0c0c0701c00044145d6103460078503054a40c078201940c2c80303810f2002c00401c4180051940701c03c00c0d0044070701101410b03024081c0b4915855200781c170401030718841d500090149454035005081d1002659001040d4001e16515601039544800701d80c140c0701d400d004603205004501d025204030b06d00300b002901040d44a040440e044ca00840104034101d80c0d817005c0369490721151209030f140d20a0744107251340100690a4500050429006140d100d03000600005400c082c0d094042e0081c42003101b480da02d86c54140ca1100c032600184a41e400442c024a4800c0c249007990000c6180000c4036090340d02401000b080c05170130000b8030440c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 504256690 1250 504255440 504255487
    0x60c0102090307091b020c030c150f07050d08160806040b0111030d050906060303040602100c0e041a040c0311030606030a090821060d051c03021303050a1a0417 70
    0x4581200741d035513160400074800c40125442c054a08511842242d2002a00b80501000100503000070314030f000400c59600400441035507020703400d00948421011843c01740c0241d5005502800c401021186d0003042c00780010312001d9209440c036003025001d54041c0005074040c000340c0d00015011503a800690ba84da85000380d07000b15100001311020004019000341c0d025000c83c904440d003680b034640c101500c03400759000d0303003006912401c01c030102034189400284c03241a00b810500a0203121030046001d444801e0052000007487c0041e45034282007501c41c04010005a05e42002452241450329140e44030260245201c0c000200116201c0b510590007541600d0344850060341d58400e87e00c4040b4815140070300c0c09404c1c122100010124102440c0801d00070350300c000600032002402009402c400740900750101015400e03c02c8a2601d030110700c0c0040a0750191004150b014035900d0540e8600350170346c1c00310100300703000420301002a1740014924548049031908644842072959031a0f4050504c01c034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 504257940 1250 504256690 504256693
    0x161209050d061d0601031502131a1c06050604050f060d15140f0a0e09150703061404110a080c21010501030e010e1b030115240815060c01020903 63
    0x11101c00c028207a400780c3c1002c05003401c000c0d02042c2c0061141d8603036500340b0000e4910b0010042c48034401c40e1550040c81030340d410031500148681c907000109181d04000410280314500010101c00d0194032825a011709404a0301c14042182000086007050203180310b10790040c004e1010131001d50b946d20b01a0307010304e0140b403420030108042c600b1120030f078501885141203034170070486480703107504007484010200c0a007d8100c4c2c42c080c4c03074555800410300c0020000c070598000c028084c070220055546090142610381d40c0416130380d041500041340c0030641c2c06103a100390b10b003181840311082e8600a8403100b0f87c0501745034143e6500c1c005801518402c01c21003044920504805c1e83d404448041813606964017a40d040103400036601d4003500b04d03900f0080d440320590040c5c0c0b0203c1180078000130313101d00030340c05800072030565404040c1d19045406900003a0000c19003c019140d03001e081c18070041c103c0000c0c608450103040c84c0f40ca08491640340b1070301500868000070700b41e20310607094040701d40ae00c40290 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 504259190 1250 504257940 504257959
    0x303070302091f0813080c120c150906010b1309020a0f09321302120615040e270604060603110607031707020715020309010f030216120905 61
    0x100400a500484030b051007a01c101d00000c1c00c80c510000921148859500d032051141c40799070b1303481805d401d503010403142250200301188400d0700030700c0307281e5511210080c1c50762600f05400003e81005003000300240c11641d640100120142c0000b8003d044a000c8900260390360401c0584407a100d56942111008900002e400608141d011120055186c0c084c1d444800481e182d080806511100c59007940100444e0f81242c2e0480d40d01c00c00f02d00b80c508004041400c00004048030405980111440c1c14018010b20100210b41c03c0245487e0303504650b0040741031a15040000020601d200500701e149600f0302e07401c1040989404415251a05201c9012a81640352a1501c0c0002e03041c00d0000300c9100c1d91260340c17900c050a12005951005507d911104c424070a21301c01d0140c04007005124000b1403103108000903c0406071241c2e01e0116032030f94055541c0300500d0b4000740490401d50521010036104028980e240c950314011080300c0c82c1c4c82000f80d4030300048020110364421a41d04004d900c0088074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 504260440 1250 504259190 504259201
    0xb03040c08011505010539070e18060403030506030c060d020901020c0a0b160f060e070812120609460b0901121707060e190201120213080303 62
    0x218090300446040c0c1000740105142070f80300c5260031850348502c1d0b02203402403001c600c04002c04449400498561a001103076251081c2087c00d42c1140701c0304001c180c2d04081014083c500007007040c00d034080b0044500341c020081e0310141ca5034800d130003840034080540c1d030400301d0b605640c14007514030344402c014000c0e601c2e101c001040900079480405640c0c00f620800c6180030281c2410f482c0081182c04854216007451100f0b501c029082c04805404c0341d242c158950160000b548510036080c0b01e5500300014600c3c2d90402c040b9902c0d01c005101d0b8420044005e0080c10701d4004070400540e4000310564410481d625032140c0c82d00c80a6034110342c160f9100d4500310070891013940c00d1503184036040d41100c003115034060121a401321040480f480b9000803a2000500c112500c04c800c03101500e202d14030f41c0d031015110300070341c0c211504680c104580181d101c8000500083d0108518600d07004442e01290140c4440d50020308914103043da829500ca4003c80ea400420b290307040c20200902c000000d9a07540d1070070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 504261690 1250 504260440 504260453
    0x6031e070908011b050a2001060b1e0f030105280611121201051009180606030f0b090a051906030f0201020607020d0504180219030501050307090e1c0201060b0304 71
    0x214010403080d9864604803c240b14121015058903040baa1034086c90500101400c0b14802c401000c2d0f071122581d03588607899425402d100301d0009026200010f61141132003121b103402c13032208684140c20600c0c00c0c8905548071581c101217070304413202256004907500f80c9803400500c050f036048a015050200084c00960300c0d40140d10890106c40d001d084d50403000b1400d8540b8070300c3c0200668071412404a40051085003404030000e81c2060090038140741045d91014100081420f40212040503a04d4500c104622501405a0802011400c0d0140901440040441c1050304000c3c0030b011040d448601066800450030114041c04141c0001440340607200c0c00c1140132204c0c0c00c1c400301e0051040a00048200c0d1000c00d0800044183c1d07603461785802c1c41c062940d5946c40300c041225040ca6030070014440108181a11500e4900b116280880d296152400b05420300044c0d074031070300c1d0321342c00c050044e60480d1010501500b15469460002d40b0080030a07000c0313004040701d4102c80c00f0008000244000d0048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 504262940 1250 504261690 504261707
    0x4230909011a10080406111e0a120e03120703060503010c11060c0705061906180b100201151701140403020303040c0603090b13060b150c070504020a0e06031e07 70
    0x1020780840c2040a800244000801c0c200700f1035001400d041c01180c0000d1440c1c05c6042c0100107464610700b0a905c1c010300024000380801402c0c80d480740007800600d81038000c24091480c60b51948104000464519202c1e102c1c480d080341c114850090b4000100e140b800f03540240003500d800b07070003008801000d50001c1d00449100720203005d41c1c410140028a6001c000080320100c50340722025111944480c00480312440341c100d0a0b0105941342d40f0003190305181991403d440203c80310010600c401e80310140004481074944210440e4100320034a440c005a9a5482044919011280590154040d0303468010411142652041c031158814082030640c00000356010320701451f0a00d00080d540c1d6025421601c80076801400e8800610000340e84807008007414041c5030040710b010462000c121b00103001d10042d80d0103074914440c04541c00031107450401c54540503180c00c0c0d8045180118589010301103139512080310f48102000800151051070007400200e000b0a0002c0650300c1d0306000340007404020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 504264190 1250 504262940 504262961
    0xb030408280c0b220201050f0906070c051206091b0307090c0323010302010e0f03100e06090115050604050f221d03030712020a0e09010306091a0c0423090901 69
    0x4003c4000c0f4200421884d00405400560702080108940c3e83d401503c0a400212203c07a0700281801140f02c1602c13004000c000552040d01c1a09003203040c40300700302d500d1484132180c800c29032101c001c1000100e40000c0d400b0061128014505810303200c2c0780028a4010540c1042c81d002e401d00d5580a002070b0150080c1c20803041500441103400941c40d0002c03079000c1e0904c00603000649001d0f9086a5081200c0c00c203100b88409800d9808200300000400251010008401c0c03480d4800c10421013010400c2c0f0822144034005d000c1c03244600d1810002030301500a0303019091103a805003500c6000ca950391482c00d15004600903040510000c0c581d035031070080c404a0100d074246c1c1340b41c3e0010f41b0b100303201004491140500e5140d08102ca01c001e40c8480080d0415040c08042c001800c0d807004556640e41c200b64000e6100300300219108105213084940801c0304018050b04080c0d980c14446880c85610036202912226203000d10000000c0c1c0c00a0701d590082101c10744c1100108091092400e01034000c0c4150b80c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 504265440 1250 504264190 504264203
    0x120f031b0f0601091109060a080f0a021812011409010615030501030b1b0904060e16021504170f031f0501051e0f04030b07020f010c08010b030408280c 66
    0xc01014800c1500c0e2040007034100c0d2103410000c0140090a0698004400144502401801c00b003481003c94034a9208100440c0030400400411245c960304061907540865081800d6051440e060004950111000300a17813083d80d11503065040744400b507011096040384c80b01d11070740505222940a009000d00e01400030712510709081600350b1030003809224120307540411058a00d1b45d42c4803480540e0200494071488084041104c0c680e681d845014000181668064040342800d092382190b200c0b4580e03c0110080d504900340801c3c0c08401603021070b03886500200c1201c140701491001c0c0120744210704d5484078502c004070130b205140020500c0c0d03d200d2502c04290907015911a401501c050103010007903107060820181d100b00ac141044017820b254a90001c0b05802c2070340300e41c0c84080d03036101140c4160069200292480c00500240542c0d082c9100701e00380310080e54106000ca0792548070041c4040c0c495540003449000e0300d80721488102e0200364408040b804840c0300c110040c143e240140095415 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 504266690 1250 504265440 504265477
    0xf120516030b01171c081902030703020432120703060518061014010e010207030506011403121804020a02210a140f0702220e0a03030e0607020a11120f03 67
    0x140d800041d0b201d10304480b2481c0c880d18030000c10017210070410050039140003c3c200701947c090000280044e40c0688a00c0d00d003d601c0c4d40c00c20031000010200e0740c07a00031403210038030542c501c1031b50221912a0b410f40c003502c0541101c0706205111307103000080e0303000900c0a4908403c1110705244541a142c5400700d031800d0b2400c54a030030080902c404c4290051085042400e010303c480b960140c0c0643c40030b60780c18015503652940e40c0e1034407030500d2030992107900b9148038102d622000c0d181c180407090320501c0c041c003500d0400c0d00300c030399882400703100005c1c9600540d40041c048005c41c3c020004c40300d00b95010000080c1c03001c5d5900384504680c0005c514980424001c1c20801203983c1321500790b5903081d007074100b840d0030007160707400b0041c00c0d04144007010790400b0740301d031410310015082c091040200d1420000b40083c0c0807614009084031441c043d1800c66801040030300c05500c0e4042456140d082d049610300507202c28083c00961508240c985000d0a849045180060110088084d03e091010181680c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 504267940 1250 504266690 504266729
    0x9071503140705030912180102010b180402130e0d0c03021c0e090403030e0a051b0109030201120c1110051b09100f0905040e0102031f0f120516030b01 66
    0x1075545040300610209141c0c40010300c07007849000074542c444452012940c1c0800e02031005810f0f03611000c881c094141d00c00c42800c01e0303942c0900078041491420b80e40074580100d8180711100340580544002d200300d811107a40d480e804034031741210310b40668410644050358008103000d040240200d00480140c0151100700d0b203002803070719442070821440c0d140c0e00700b421126020000001001070048090550342e2600820700e200810040540c50310501c0145513034000b510080c000142003a0301c0c20304120a4070010300060360321030302d1544c24443d000c901040c0305420300b0701a01c410b554081074440911a08030007502150070707500014010101448001c03101c00c15a103028040384210407500d50000760080380e082240784108a9030616000d02e1801d188090b450b2000a170503141c1088140040c3ea4001c001c0c80340b501d000000000440c02032114036001c1618241e85508104440c0c03060916142c0c140e0321910a1010a002c29668010700019482c4043d40380e150281c01c1c80000e008400c40718a10722040d08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 504269190 1250 504267940 504267947
    0x8160317060a05090c071220120a0c2a0323030a08040f02090a02030a050f060f04020f120a0c1115010e1909050f0d05071106070c0806090715 62
    0x2409101d0142820030414202010b0040d00d10303010b0300c0e10b01000010041400810303600f440340d5810304010f9503000c40c0000c61041c0580f0448144441c00d0f84c40d00580d0f003426040012008458514070b9504000d038815600d420425818a20b0346106404020300506c8940240481900c200c15070384200f050301111280b000241d02d0051107991003100540c0100100b00c1c02a002e240865403052180301600810300950f40070401c80d880640d0403003030407034010051110760f1005002d11540100c2625000c409481c2120029004042040fa168001e81d030011300a03444000d000116400c1840b001b0540b0080d0400e20745110003000c0010343c8400240a80180d03032209100070940400c01214000c210020343d0a00708603100c03400014024400a03400810802c598031500e0082e40d100d9401040544111000030803020f0810440001d08030030440204039400019448810800301c0d0003064070300e01c2e1144011b2600f80003180c0c40750080d290a206240401004031400111308054406654606d9107183d0b082c41d054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 504270440 1250 504269190 504269237
    0xc0e01021203040b040201200a080702040b030a11011d0a030f0b1f05101e03050f011202090a020c0115080c150306032a06040f0e0702030a0917010603081603 69
    0x9010400c0c00f40840c01542c420005640c40c116000c07400f140055a842d1a5271a00f4203080c0220385040010130b180c0309501e00361144031040441a406400715900690314601e00403031181d015418071030481d480580384901c602155000c1074014062000341c43d1a401c1905c14060b44400c1114000c8200f0005000c1082d000300d8056210310341400c200b62141410304115070315070510910010082c0c81c09031005070060650300300302a00780944001540b400c082c2d41128148105070809400701041c96040f900684401c0d5007141e02c800640f00040e01e035900c440096000d85000081d550b044054040c0c00715500201080748900e03024202c8031510b8011088070f10300388500007107601d694540c220841d1108603880d03a0900c0030484008003203000701702410074001406070f017050b040094031022400c01031000c0b400070079602d900310032a4002942032008a140c0186520306500a240d1408900001c20b0700401e000d4000401441c0d1016001d0f032a28260f4548080703121540700140d000484a0045504054221408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 504271690 1250 504270440 504270443
    0x10611030403030e0d0b040f060605090105060f0304020d021f030f0513030f020724030f09020a0314030c01020d0b030105100e0601230d020309101401030210120c0e0102120304 77
    0xe1810503185881c00d5400000350b002103034000030b00006480c002107001e07420038401c0f40701e211140306000050600c0d00803105144c110a000b0b801c480e005020581e58642034581f11013a110034555681c1c2c0e2803000c64581e011103540250014002c80c0020155280920005070f1032843d541d040120904008858050f904155201b04c5100c0c280c0b40008086882074411115018240c01180c0b0260381c0c45485884c0c0700507100b82498003200064002403910350500425140c4041070005001410240c0c0009216075403d100041100c110350a4005d150309050065840400d4480021505c0e8031038010340d03030003030000d5a0300fa030300c41e51828000460300140718444c14141c4816070b402e20f20310350b5036000550f00b42e05641240b199801c202041e0b5241e0303541040003099502103000015849040001c00c403031414043e180a05200c90400d4030300900d49003041d14032811260100e915003c01d296841040d1001844500c03440c0b4110300b000c515464141e04024a030032552000e80c2110b00401106042d0740302030005480 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 504272940 1250 504271690 504271693
    0x91d0d0801051c031e1808011a060304020a03080304080702181608090307081305030c01170a021818040c06020d140702060f0309070617011d09010e0f03040509010611 73
    0x2c100d040c0e0321085031800203110341022594200081c17030803400071000e03681c118001042003032509041e90100300c5d40001000c4a41c000d11400c400c40612038002c01e40d1100d0302d4010f8101000140c155074589690350f000b0741d0043c042580d00c3c2041e040c2502d4a501469042e8040c200115801080c200c9071515148a582c4d480c82035044105440e004882001d000303007016480c2e110511001021030f00080c0103200e00d007040914980403c0c6008141410704060500e02411f00c136500c42080c409800c103030700580c0d00c0b0303a040b0310050307458055440c00c2e6106034416401d41c2e00445a1115440728002440c0c80174011402040700d0102255a050101e07622500d8146401c002481c101418095103001c101030070020348010b0040c0d041c003c0ea00e0215070b9a030000c848200b440e42c002c41d001c000c007640100c500c81c10b9140a03507010000d503042c2603041d0800c141c0364100450050505000528114007944081074a8149105450400b960100081c0c0e80760424080c00c1d00c1100440000141385006400090b8075040460 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 504274190 1250 504272940 504272959
    0x60607080d0c021f020309160f060315030b0103060203040b06060a0e09040807080a02031902030f03041101030e01060621090c06050a2a1203050103080412060204091d0d080105 77
    0x20429006014050248015482940e00b034078201078540390b2107504404c45041c016143c0c945140198508051420803000101c40444c0510038003424031105000d07190300e0708001c43e5003060106403860707403552584064140355010002008001042c0c0046010703e006120701480c80d10744404001d11489492002008a4400318910500d0b050442000ba4050302602c08582008491b4403200030303641c803003154803005800005100740d105c800c504502401d001c40348011030030300c0c4d0500301c0e51400340310107040540800042e088014143c1e210781c001141c00c0e80010001d116007643c4020280a503d51400c4200c1c8000d114600340c0c0c40c03104244201100d4541100e888006945403400955a0751720540b600e1082103031044c0f00e60100e1407100c0c0301c001500c1d43c1c040901d41c210904e05044520b41c0c94244c0c00750406003060010000304a41002382c0b4140c6901100000c90b2130610f183c144000c0c030582e40030a802c0d50a0510407a68a8420300c241154041240181c0300307104c031204002c6500c0e200034040c1640c0724201d00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 504275440 1250 504274190 504274207
    0xb0406060516031116050a080a0b070e030309130c090e16050306060f270d110f0301020c01091101080f0405071e050409050d02010614090103060e0c0a030c0302040506060708 76
    0x102114141c0340c000d0070041c11071888418010b08103c3d00707042c2c00c42c00c8170702803404008071308000c8003050040a1540180c062201139a40380042101c004c0c0c03100d000c0101c00b6040700b100d503500303004590440200038200a080382d544800d120241c41c0d034412080115114081c00114146400300d0203100380c002e00c5003020002c0034180165a02d802c0580b15640110003400400c1c1e54240103c0140f21000000300044010f09148074006082e0701d05540e00c600404040700d020740090060420541241c07411540e070300505c4070302c40109009010300a201c0d8407540c00c007440001404040c0c4088030200d03c0a0740c410383c20355108508841c180703005480c002c006610007001004504c001c840d5103110100518078081a1079681c400040664010f2242600e4070b4204504049029809100e51401403100c3d0b46d07001a02003030080011504641440043c1506481c0c40c0038400f148400d00c11640754401c0182001a001d441b03060224800750300e800100d010307514203c0860143e2a1100650f80e50030781c82803c8070300d0700d400d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 504276690 1250 504275440 504275467
    0x7020f070603020421050a14061603090809010e0f04020739090507140d05070e090105012307050106120302070506030112060207020a0315020d2003010501051c1e0b04060605 76
    0x141c0c0646d09405048101c40000d1104040b9100740848840205440d08240300950010126940d06106049c0742514a20000d60400c0955115035001d00f0302d0704a24500e0408111450200c061850307020380700181d8203003082088900d40ba0902004076400c440121840010303040b41603180f00000324040b08102c03c2000807880c0d00290f0340008103181c850100607172000720150301d402c99207036030b207655071501c04100c41c00b64418415050074000320b80c00d6105515110010700540c44440c03a1b9004040807940c2d1102112442e0212800a50300000030412640d548c26110040c0e08000c40450050040181c001114501001600d042e600c84060301b0780c081c0e00650340c4400940c0a0403040303070040c0081c440080414508030148641516400700903a603580c54070b6110049451818000307005850710b20305128122300c5041680d042d260207080c2595100908034040c02521180e4180d10745407820030155540710f0040448115040301812400c1c00526040d40402041e02d500f8003030000042e070140a540d112400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 504277940 1250 504276690 504276749
    0x3030b0f1f0201090507030b010302091e0105040209060705030412021201050408040e070c051204090b0604080705042703020a0c06050c06150a0305190209090d081303140307020f0706030204 83
    0x5042c00001800803880da900c5041c10001e504c00d0301c040750003000410030b500303041140b40c1c0e10113130100700d200d05100c03c90442c9032401c1d0103004c3e5074090755000c154140d09484603002c03218495000400c070380d03e4a0762030f12500c0d40f01442410481c01549641c1e008280076005010b0765010399404403500e81020706007041201c6c1e4a60081c4601c0400c1201850140800c00c203129480c1c620b40c0c806402c1347d80c0e5003403e81c035400b560858001c041c00380c00300300002c11221a000c918041074030b200b180d000c11060800d414011086661103104079002c0c0204c4101000c00d03070006440c1005070310076923006006d255111415202d500440b00200455004107001812506480c204c840070014001c151880080d26a20b505242046100b14080a40303d1001404258601100d445900c44c0004009161030998038400402d103420103000b10803000c0340c0c4c0140034101030080005154509100d082d042d1207240000009603241302e080c040300c005004080020907054800e0013290282c8544002c2403240c03101c0030f240c9010524 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 504279190 1250 504277940 504277999
    0xf04020d03140307090905060604180903051902150606120403120f18050106140a0306090204480e0909070b0418062702090f091303030b0f 61
    0x115080d401c2094404802c040c1d802681603030707112401c4608003c040e404840026041c98030610b42400200034405201a000d041e00ca56141d0100b82060180f4040e078590050302400c101d200c4a6502840d03100b81e0000c0d42c1c804464040c00202c4041e2160800d1140c58424591500b4580c0301c20000100464043c0050b42403403102c6580000e00c19107401d0400040742c0d0380501107107601140e401e007401885030074040d020117040e1640201048404c2c40300040c0c0c0c0c22501348402081c841c3c07207a04d520103540d80d541c400340070301980d06100380c50341000350060044452440202c1071700c05801801c0780603040d000003000c00c100324aa03c42c1c4669000304030030481445001042c0740d035903200d101804103415100704082d00c02007945c650103241d048548a80c51068594680041008402c198101b010785038102030040310071600c0d03050059482c0400804501240040e01c0002d401240325000c0c40b18400d10706d2020800705000303a07000c0210136180d0b42080348941c0d4244030b0300d6200e6020202d47d03001103560507c126581 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 504280440 1250 504279190 504279197
    0x7050d11010509010c061a0f04050921071b091803020303010b090a170f07090c0e100e0d0309080d0e130c02070e010602240402150306010c060204030c0603140f04020d03 74
    0x11400b60b5520001d4a00c0c11147c8240303400400d580110505010945d1000410b04039414040c515000d6120f075614036000b0a10b81c80b9501a107072145520000500312a0301e2508000410303030345440000a00b2183c0313124401c5428451909096140c10a100b89079400c2103070341940070f10b280d030340703840105011600120181980980c0d031070400500100e003031034400215038000d0302074419070341c0c10b01c440d9042600d03d03880369200741c3c2000c1e40c04038495031084000b50b501c0d00445410600580800046800003280f05485402018008543c42499088003120307003112503c1c0c0844000345040c25044803c00304420200e0303000728075250079a88041c440d41200d511100a48105d80b4180d5032103049038620003003a4000e0002d45c100300c9030304541c941c107000242a41031406841201078245907000c502445200e12501c0d8031141d0210108946030b1080c22602122501b1100070f548445c4c8030300b0075030003107071b020710484000c24076103860740b6503004100d04068032940c46e10107000ca041c1d445400b40404800c0200b4200c081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 504281690 1250 504280440 504280457
    0xa05010e01120f1d010c080906010f05012f01050103110d080d050405030906040b03070e04050f0a090c0801060906090b0109030b0c03040206120a0e010b01111b03070906120507050d1101050901 84
    0x106034601130201898100c010001c201041d0503800540f92034400388c100d41c02604036030014000a583c070000c030000c4400c01e191000040c821248503400002c503080b080b0741000f00c0303030394600080a015080107060303e00a80240040040f0706d020400c0c208108200102030240600c40c086071501140c0c4111351060250003900d1400d1502c40000382e103540103400880c1c1d41800801070000a030b6202000c011045810342d010056810001514040f000004140c180010b40350404403040186440040000308281030081c405c481c2c85079101c101610b51800340f006885c0c64001c1103005580306400c1c100889806c83c582070030640300c10300c88409542c0002c00c141e8011030108071076030760a001ca060703107849602c42500020301c03040b581100c0c03403d69090381d01c0c0c47d042210040c0501e0480e100464a107040c03100303d8141007504100c0c14086810300380a81d11206040b8604000001d40340c001d40f0954070318600c644180c40c0300b0b6446108001c690303c000c880c081e0440060700340b00300140d40640002c01882805043c11540c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 504282940 1250 504281690 504281711
    0x80c2502090a290a0e0c041a2526040603050928030e030d0804060f09050c01050a0c050708010618150b031e0a1a0f1c0f080708090a05010e01120f 64
    0x440c040c25100402c0003040000d040040700d603c0090f0290b18000c41c1d032014034001d0b10031041c01340510f40c0c2c9c1c0c41145403010141224104011466074101c1504001c41170042121803110701c54241e0020301c5448080307820100090042040841c504000d5018621a2232241c14084034100c140d20102004030107002d0b06141e058007523a0308000801e18039204e69205022460149850816200c00300910600380d820100301c503000800110b5415642c1c0d6080c68916202d0030783c1581105e518803480409811405005000301f5150810b40020054a50100200d48040010240c000440750b00040e290782081c1701c050140550781c4004003c60304046400c010f110101400030403a84602010741d14500e402cad607500c92820500e82541500c0c02881c41c220344241e0440a00e00c00310320030790101c1c8c3d512419803071819001e00030000c811702c1a03043c0d2500318090700d4540076180745c00c014990000c1d000511900001c000020150304c51402d000340c544d01a07642d1080442c04482d0b20700600051044c007881151a40c22400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 504284190 1250 504282940 504282959
    0x7020f01051303110d08060915150309011d06190e06092803050f0304020a12051005180a0b10150203130b19080c2502090a290a 56
    0x42c050741c1005810240300076a0f00d0094259000b5242080058002490480c0c0043d00040c429910040070b0b640c0030310607a2656540001c1c50340d01a412070b849031403e0800a640900c501c00381d4480e0240350002c0120465208205280b00d40c0b619800c596a03002100080e040c080445148801901041001c940146d89400c4142851400c030b400c00c80541c403c580c04114031003102c02020800c0c0d030005103002d1000c10380d10014220301c1501070340201c0041c0040890304548620f074a100042000b400442d02010003072503d5500c94a00b034041009450074500800d55560114030302c200310126010041819912964801c6008a001130840c4040550310a00040d09001160740409286481c2d0103950358114002401c00880000d4110080c641400d004007902c43c41003405e034a0f400040c40c18036100940d210382c410b41d001e200e10100c01044582845490368040c40d26004041283c2c4212090b0750340342d0f51b0981d1541100d420f600c0c615141d40e10041d4440760034401c0c130402c180807600a805004100e0700d500341d80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 504285440 1250 504284190 504284201
    0x20d061109130606050702042703050c0105010e131202010b271b09010804050c04020d020711090f131a04032102040b071e0b0a052403120307020f01 65
    0x180054005641e5a5510b0704406107000c20b0780b000c904200a41c02d09400600a01031804000c0c010f580d1030b4810009840094511410442e10f00d8070602ca698a81c6002002c0360000d42040c0c0c2d041d8280340c000704642c20030f105014421882d412050b03412400b240c8400d0b482500c00c40300f910540d582e960f2074107025100c2203100340c070b082202e1240d0722500482c031b00c201440780300050252062103020a95080c3c8103524000303e903402c4009180200301512039003041401c0400c401c0c250350384548002064080259030b81c01800071f45020321015031184070a80140888d44408031907010b15543c04500160350742040b1988030b0712450060101c4648005100003541e2805000d40b4281c000c40c01070708031045000081142d50000e00d40203c415030078289082c048c11394500800320020540c0ba010700d4510880300800350300715284c6810050580745804c1c030300e40840c02407200b9244000c80f200c00040192010381c1b04449000c8407640035005040b10380c1d0f0008800001c1e04064102404c60141c9002d0707001da171009020b00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 504286690 1250 504285440 504285461
    0x140108030a020c03010b03060408130e04050705100c0b0117070b030901050907060906090e0601031b08070f050f071e0b04050d09060906020d0c0503040b070501090b0114060412020d06 80
    0x21603031046850300203460f01c0f07507400340c0c0c621a0703040041070b10a43d10040352042e08681d010451948501c1100a0540b0507800780d04404661510f400c100000d020002070300200f01d80050340c1c140d01c1e03030701c04800494059210650180450491600400407078800b9804450196030070003d40e0356460326034100d9a1268019510440c1c2a9120300622014120500403240140410b041415110b89060300c042c00c0c004481c881d020607941d41c0000900141d006e504400f402003045460300080c4000860090003090040d21100c0c0002c0800c00a10403680c01502100c19400c44404600d0400f4100e583d00c406181d40b51506d03200c41100071041c240000c10b0030b42e1403030046e48120040c21403541c204000502c4108581d200c1001c01602300f0313003000600d8001c80d210000404a12340241182c0a600b440f900d91301c40c0c0d07406076144000024080041c8001980080c809074070401c800d8409990b501d1039102c42d400c2400d21140d0101c0700304400c100d02d06401ca901c01c811031015181d1480b140082e00c4200882f07011085 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 504287940 1250 504286690 504286693
    0x20f0c0f0102120c0c1c0215070f270b03040b0a050609040c030204051b040b3718030506010b090f03010c14070213020f070302070b0309030a030f140108 67
    0x208951840400e001a1625452a400031070503c45101c00300e4040c02c1001d050302150b000d0001c0d404c000350300c2c180103800e000703880f1070f8144401c8036581000a44d19034510b1402900152080046074030a44a50780d08c0c101400d40d9a40d51060040d03810b0844c1d9411845800c0d01c1118065907000144060000b028500c224000c0799464028139201003641d080c0c50780207002c0791241081d2000c201c00a04002400b0b400d90f501518002804e40d034070300044400220390700304c1d034143c0a00454009080d14042c0020407000d850700090040e070318040144919a0701d170000c440003088458000d00282603218421490841c65000591000745607a40c803050b0604da002c1e00031310880900000c0001d503608190403402c190392003e034000c020a04a140004040070700903c3c1c0480014000100242595541420880b494a088030110f43d140d02200145005504c00302c811405130089140004003040000c0550388111954400343d40791401899040300206983d06003491010b0f6140345410baa62000c07182700d8041c0c6800b80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 504289190 1250 504287940 504287947
    0x3011802120a060315150311010507150c020c0307050d06020a050f04060203040e060607050601210203011a09061e0108070c060912030e0111120603071a0706050c12040f02040f020f 79
    0x2e201034040c2c1d50403643c0640030f0408075191175501003940207004994012010131508c0800c440121000d10541c4005425081d90800362807062400364000c0e00400500d07000c0b161002d6054040c5130300c80d40c0602c00c25a00074443d80071200031803100e8004000380c4085242941c68407004140146840c1c025030060401a800480e003448421013000c500364016404907441d508009040d60703095560342c41400f80e000980f2040201c0d0741e94200a4101000c60750b40140280f24180100700465085000c60500e28410a04070010034824104600160a0420740d41400103451071400c0056500c10341c05844401000105401440802d150388140e8117064400d9211800268a00340700905a4a0008041c0b1a1b0392410f281e500096110b04200d448103120011050766594400c00081d05202c2a07500240c01da40c014189104400d81c1c420003454490b104500030052612940361404840c01850190013070410b03840049004121040300c500c0817584010400306529210301c2d43d402c00d81c1c00c001001d00c2d4541c03010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 504290440 1250 504289190 504289193
    0x110601080703170f090d082b05130b0a1a0406180c032d090209070906080a023405010e01061703090306011a0c030a3203011802120a0603 60
    0x2410f031500c000088a1140d8209654903005800a00c036100f200c1d4420f02c001080d075810000c201d8195200c1e48800d11b880c0d04801889030612865140144102c0302c524500310008020030860400c135031035240c106050760b840d9654900f068006103e090001d0181f00091031048e03034039170303038901817080582a41c1d8400d040ba03810b040c1e04982502c0030342d4010003e060071704110340040b00300c1042c094800800b81e103203140c1c18120311103c80300400030202c1c040d400021400030400320640112100c070032101c2c00d5443e6419070344d43c48800c04c01c80c0191203409020a0360056220255009110184807c1c01d00918820b0400401c0d0f40d002d003180d0f0002c3c0c809503665180c0d41d00b00b0004e0741c140c07075490004030f5844c0607501d083c420b24002a00c0300c2c414081c0d103100c400d40c4088080c1080708041030fa131680d081d040841eaa80c4203007480281c003611040201407540040081d030034081c540c110801354aa81210846c444c00d41e42864180360180041035090110207070700344000c0d00541c0c0c0300c61800d405403000000004400341503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 504291690 1250 504290440 504290453
    0xc09040c062d05090406030611070b150a031203180b10050d050c060708041802030a1107030c14160b0d1b0e0d1109070e1c0503030408030601110601080703 68
    0xa481c59125071145842c03489204000300724040021220340c0b420030707500e50f0100d000900603c51600040d2072249046da2504040c806500208071581c0641480d90595840f0841d038a4401c1002d41040d8104024072000c0000038102569101c4100d1350f800d000c03602800711100440501c025850995072503d0710414080c20302d01c9081c0700002b80000b03039486501c0a11517218603540c2d8012110003800303840000750640074084580e05480290180550b00354000c51b10080000c043d40003522000d400394504030130f040c203040c4203000311b94003141c0c503490302d00864099884070a209020400351504078041d6050604081c40361425203c003401c40c0c0741c0d84540b1780b07142c420b4540488914954001c807a01c0400c0d00259002d030840c00c000b50344041281c9000c200c190600d440480348126100780f5401c08941d809000b600ca030407800d00d011203002030715107100c5142030510078881c0b43c071315041c080d015801c100040742c04505048000c1da03020406040c001c140710700328041c1c24034004d400d03408a00a90800c0500b8801c0141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 504292940 1250 504291690 504291707
    0x30b120d0807032a210506010f11151021120f0212030a15080a060b03060112080309011d0d0801051f0503040606090e071a0f1603020c09040c06 63
    0xc1e038981007043c02055000c08290313521103491011301c292200154003403148904003070f10a1451040400c119060728148510280c4401d980103800702c0c0c800901109010700c030b00298410080c800d0010485081d880946101c23400c1c000c0d0680f42c4d290b0500c0c1300481c00e001345a0502d4080c100e18115000624114108007401714410100b90081104507010480c9440c0d0000d224190813200c4607000f0b5507502c40340d02c0140100034101d800d800c030040394040080c0c0d40350042045041e482c000c06090001540c0740c0c08044c1c40d400d007401020030700400c5400b81400300d031410000d594400903100001900782d01c5804983c2c2d40424051019080d58008480c0ca80f003d0750000e14a401000d055070801c0d6000858080c1742610b2070142410010400301200160030300009401c0300005280950341084000b480302c00340381d100d0b103c5018062071861900d080300c030410081001c58030040520340c411402c003c94080c862a07031a80100c0240d0031440340e1820100c26a4443c070300c1e07038002d51103485501802c51500101504021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 504294190 1250 504292940 504292951
    0x6091603112e0305060f0901150c120f11060f01090207030e030a23030c030a0806040207020a033206010504110708210603030a020607032d020d141009090201030b120d08 74
    0x1b501c98804540d200c24605c0b5041d07070b425500f41c1201d9a03200004860040c19001c01070148080540f5500301d250304515030306070342c5615690303a407241008003104950b91407040d0b0300d2109a0056030010001d48607140d0180620b079100c0d1900215014450380060301d0413006002c1581d42c000707500d40304030440c1c8059a6503883c6101e1000950700308020b02254030344902a016414007401000c400051169685034100d86002e54010504603080d902c9040c000c2407c09009130000e0b100203254628802d0104003503428021880c11001400a6801c04042c080981041016071070030800034042036000a00b06000341040c10100b04400001030200e404041920a010b00114025041000200041b07603002c50303642e60010070b506012a8044921050301e007444400450a48450722410f901b01d409451034009101032000240e09000c1000682c43e40d22610b0340c02d441c05050214071420801620540c0d40040340f44c42d005040000f11511002c0110749403180c240709005141c3c00240003818065048040c45801a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 504295440 1250 504294190 504294199
    0x7020706090f21061406010206060103090b041b030804060315090b030a03030e031b0c0f030607122406020f0d05160f02060f0a0206010806091603112e030506 69
    0x600e0401c2d0444001c580c0e004101000c81030000e0314000440404031071005503400341e410840400b065140c002c129074142ca5840c0140104400305501d98440e01525170081d40001e4039905503103071a030340c0340d0200080105154000c18112400804146401c002d08004e00c01c1c1d44012902e400010b5081c651084203406c039a4130710f490300e295200d20380c80009407541c0b05541030030009042400300c0d0002d0303c2d5000303a203407507100c00c02700d1004c41d00d4040c00486c00d1581901c0544000441016001c01c140d114a01110044002410f007031100b00807915035003018503209030000080c200c0c040e00114000c141c1c80c2d40c6d007200c1c025030f0020522640b0a40700700032402a0b04507502c0c22070b04015200041c40c40c0d10031b0022010f8118183c0d000c2c24800e554800007100c03141030000b107040350f40306c011a00c041e48641007440780b06124000d040008101d54800b14509502d201d04c90140c116003415650741c81d103464201d55429420020300e40704006030500750b050580b185804080702440c60300c00d05900400380c49000340058001d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 504296690 1250 504295440 504295457
    0xc0a05070803070804150c0519020a050603060102031c02070b04030e1206070f121b2307030203070308072624130e1005190612020108010e06060706090b07020706 71
    0x4034004500b50340030340d45140d4a506c554a440c01d0202d4503038020100142443c02004440c2200700f0000c6070f13903200c01344251440300040303950384100074480c04211030080c0540c2007007014141540c142c10526540f03401000300141407050640310205841005ca070200d000c41c0d005d08281c60207260290400034100c0c10342c4001e080c0c500e0860001403070002c140e401b01040c00b40c904414440c034086900044200c084c4058074013a49001000010b05070700c00080c415000c4400000c4141d29003962030110f4030301d90381640080d80707488201da03421110140001c00400030081400b9074410311003c0342590300020b2052a280c240d460810b84d031080b00b80200102d10800c1d8050829031889291100d400d42e02d00c144103210000380381505c400c0d00600b04000d801078403005520b4007040040007803010002080002082000700f00040c2c440e400780401e108000740103804142110010030081c0144051907920007005402d1904001c40381c0d07111400e031000f1840456041700204200308680780e04000d03150084c0801d1802051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 504297940 1250 504296690 504296693
    0x9130203101811030a09020f01050307171b030a0e0d0306031a090c030715030f0203060105091009080a050714181501030603020a0608071701050f09060d080c0a0507080307 75
    0x20a00d5445500b180004082018442c92101e5020308115000242100c0d500d1910101c1d1030020a4100c508034400c801c07119101d012544074006484c8240340c02e1312070301441c8200500c00c4d50309078002840c1900344030645182c0c2d01a50b03030300e10103140194401d43c070102d02040312400e001d00701040b10140360109850008200b000c14202254502c1c480540b1000090075110414043d0900f0040700b803442d01442403860000b944200d4041144040340b4550301002803003c001e1749181a40b0082e212a0300060040c4042043c500e801d001b42c03a54503603181050075895a640101d241040f4075010161455048001c0c10881645080481c0364104011190701a90b190306a00040138010040d100b40300c0c000d1070660b045800c3c1d00039071140000d1900140341a444507a110703002070014108072003040000e0328030f944000340816524601030590f14020702510b01f8002440c00d000341864000c01065000418004000104171204000c2052207150710183c80408620b06041d482d1901a03441003102e607208000400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 504299190 1250 504297940 504297961
    0x8040b0a1e09060513150504080106150807030b030a0506010f031a01261213030624090b04140103060204080601170303070e0f09010e060a2907140609010209130203 72
    0x560f2003904146840704612603204003103d116401810310343c031581101c6024550044040d00440d5175500090000c191190600c00300c1c8200310800f03c011800c0d04c3c000c80c2d01c1500030742040d80aa4005021110410301c191211407400d1000c0c0d01a0300085100c44050040c00040b0228543c2e6070184810328020707514203d52151000a0002c0d894100b00910b040c642c491281440212074035054006010344442540240d00826100c034402210514980041e8030030f8100d04548109c8481c0b0b0018030b0700000d61410b100c40b800380040d004d1071940666601548060700d142881407070f0103140544001a1101d05003502245440c0040e00301d403d010100343c129081d00c4c10008126540049180b03030480040035140702040e801c141c03411455500c0306c0030400210b403803041c03001e41034800c0608030f5050204550701d0b542403604020300110307003003258444c024100160321800002c022092007138800c2c034003081c0c400640c182030000a5a0000440e500014804414a030600300040a900c0d2540c046185050012000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 504300440 1250 504299190 504299207
    0x10906080a0c061427040e0a050c0405090712060207030e06040b030a0f0e030318010c0e0102070308030912270405061e0102010e030a020a02090c031e1308040b0a1e 72
    0x100f041002e021454812060034909981d5049081c12994000200380c928403160190b0b803103440b40c0580e00e01444070100c01000102801002d0300035000d01511001ca100780700107004002d140800038401c5690000701100b109904d00b20307440c06030100503100c1741c44d840d0062002c2da182e81d1062103500700380001e11900020308100c0b40c1142600300b001404082c0c008841018120298103d922400080104150142c501e0121031078850264000c000f1441d01c036100340d03142c1d03070480440c600583c40600c0074070000b01c1000055810142d01d800b1100400381c1005901c03815840b00c08001a60b0304c440a04102040c0c080340744c040c05e40800c88080c00745103000d030f000c1210280388200b0404807110069900d640f40e4001e502c46060301410344180d0f80d0b594685c480103550b0381540d80741240a00000e80008294100a0b82030724010b014080d4002012291031000101943c1d002c0d054a550811040c060030008903000006e200a0102111003526000c10000140c519120607001e642c08a07044282101c0d055070003c1d61 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 504301690 1250 504300440 504300449
    0x10e03073825020607080c07090204080309131416030608060c1c060f0f05030c041b0c031e08010512010618090303061d04020918060606090613060305010906080a0c 72
    0x204003040b41800400452030014001e500100005003203010720040600800c003075007000d0201c58a44c2c0c0d552041c04101d1103188500d51458200b802003010900e001c2c00b2505100c0c000c000c1c0483d00b034684040d03800d660074090f40d05072003d06a10350039030015901402120b0042c0b44d204c006c2c0c80e09150007421042184600c002c10545e00807007212110741c10115a0002002c0c12110118400003611104108003002140c06224400d01c2182542035040c80d140c0980d04070101c006a82c0041d07185401001d03110050842030881c02d0014100f44080d9244005140b91060841a607810040d54902024005252446030300305503140d0410005210700d100100644891031800c0300d000401e4021b60504800400c00c1e600105941c08190300346c1d800d859214628107004070b0084039000140d49602000c4015440303203003071140702c6810040006070240307406405072400a40240969240046c2d84c05500c0303d1903129000840400c1e40c400c01031089020f148581c030040c019400003002c1d035035041d481d044c0c26040f10b0b116 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 504302940 1250 504301690 504301717
    0x140117100608090f070b0c10060b160503190201020306010f0c12080606091203041a03040f11180a0501061404030b011a070506041a10120f02010e030738 67
    0x10070308402c3c04120b16440e004201d01a035485503291226950316605c00c000a01c50703842001720716900c0304803034491617088440300d4403118031348081c403d04c3c400ca403605440140d61600060040301c0b80398102d508090f1200103070354001030382c0c0e203041000901030410111004c401c0020748020500003554000c607251348100e0506000d0341c10760714440014041c1c41066070041e01700032003611101d02a00e000001d04140c0b031210f205214060440d84250302d1900040760080c202e10f60761440080854a120440c141548000e00019003100380e80c090818040c3c02541da854425580300b00400040d60702c00c5603409a440508039261034185141c4481020600602807030020118150700a140c1003200e00c202d44039640d1180640b00c1d11324182c1804e05201650500840b40340203030b100019104418514850195813a52410050803a41c40e15002c3d441412514200d050281c03042c0002400e40d001c011041c001c00c25031840f600013031707401303150a500300407403803000405c070006420922061410342058580e100101074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 504304190 1250 504302940 504302957
    0xc0203010b030304060201150e090a0b060303160f03020c1903020f03210d05011401050a05071b0f0302180f010308070602040f1716060f03090c0f1401171006 69
    0x40e0041c14040081e40d410701c07000600080706030701904034240c2c030162856991425a40d4480244074048225102d1001da0000d059203000203840860b030941050029003120301707015521240328034a401d4142e0030b807041e201020f500d20405504020426645c001503c10714030514058041c00810307001800007d1040c2c40d00c0d0380304041514208400c1d035407402d2502c0242a411041c1d00d5180b42c0e58400000c400165041000101d1200403030441c4110441040e981c030f40c41c01028030302c11155034200c6d84089a03002c0a41c1c034003526011003140108041c0c4218007000d5015443c0d4410070910406200c240c0c0011800d0340108201804c140310300904590b0030280307107665000185000c1c0300a10640d081240ea065100344041401d82c1020540d144c0360400c0d2048070040580c498072083d11040303034400c12000030196403803d1612031190304218034040c8140100261162660400c1c4c14107445a08107545651108006002c00e42c0d11102d407250092401e601c80d040c034100201e600c062411309000b40d006211554 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 504305440 1250 504304190 504304193
    0xf03070b09150d05070302070b010b040501020706051614030c07140a050d0201021002041d07031e0b040f02190318031b03110d090f151d040605131e060608070c 70
    0xb408036284004041c2d403c000c07900e01000090f009400c90340703058030011041c42c004203004c03049400311402d40e9016001420258034000302103170303e944220303040c14410281c0c81ca80000507840d0004030a00385000c0005d503840d4180450320900d8096940d1003150402103d000068050326070400c2c000680340e00303640c0b80328100c2c6240010b0746440360040700b85200310720004001605150f03c201d429081620004016100c1e11003010440c107442088031a008544030710203912690024503805001f074020080e0011035200950b000340820dc0c1c0100009001170310702e40501d5221143c1c1481149440c2c40b011070003402d1103180741c038001c0c007c62400742101d115005500c058070030315005204800203000c404044034000882004002e11041e283d204810304490700300004103018192412405084204d507850f1000c82d00003010503241020703101c0c0c011340c01035560440460181c40301c0850118442941c0382c0441c00e840c18002454000916403640000149018018094568004500d940240162500d903000100c00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 504306690 1250 504305440 504305479
    0x4030c051314041202071706060d031110020904050a06121b090608010912030e12070812070c14030304080403060b0f0907030c0e040e030702130216110f03070b09 71
    0xb00d00c0380e000341c40504100310410207030350140c1c80d4a8201d58261003115969052140e0703452500004095680c0020000a40500744407604080c094041e1030b20020a60300a04050704000310b04021183c050380000d040140c500700341c0601034101450040c2001403e1a059907903240c104500002000c0314402c0903001c403a019250203500182014240401025983d11718590003017a00b0042110f52440003002c02c2440c40c0280720700092481e0748800f40000200510b10200c05a000c0e0b90b0481304500188003420f013880d0180d80d401d00c180719540b40d450030135100e410000b4080d080d10000300c178650b00400410000400400c1520110790380100301003549612200014520328070b048030542c01c516803200f0044050f81c141c0200c441c40c4920749038a01004031510070f01c006d4030740d4010f60114fd81e20400860005080090522000d07102c046001410608454201041100d040000707544580e20741081c0007140c906103119002c100800c40007442043d02c1d0820000950103101c607940d00c103080c1c1e42299403000d400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 504307940 1250 504306690 504306701
    0x1d0603070f11160b04060e04060b0901051e030a0e10020304032319121a060301051513060203040e0711070b0d0207020d06060e130f120903020913140304030c0513 71
    0x1070b680089041c0580f1850340c0700b42a0020710501c0c00003440e24403c3e11307c2d0b041600c55001034500c040481407520084100565203507101101d0050200c04e51000051803a80c014080c1d0300980e6080c00c0070503141c1081411301e141480380c454500320148100180700c0025089540303103607041d2100c442c1c4000122445500219805401c880314850000582991340c0164440580060520099020440000a24410000100c506071000d400010800060001d0302d80803034001100141c4040f440d103450445400b0405198195009a01680c000309007032090884880c5119030009091400c8001e9503030503807086950b4051841001d003512400541c858480d1270300c0d01103d03070711038028241040308041c51401100500d414401c8000103d81000400d000d108508202d942c010b4000020a840001640b92810010149514401401152140080141c4ad8900b401f486400041c1c00c40d204030b041e60a16000fa665200b501080c0764104110a00c00601600703010300580c0c0c020f41d141903a5690743d1010000409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 504309190 1250 504307940 504307963
    0x120d0c12140304050c01020622060b04020c120904050a1418011118040f0504050622060c0e04060608280f0603121d09060913121d0603070f11 62
    0x100004000c03d00100140e0461004807c2e402c60b509030380c1e50428031840a0301600c00e0700c40c14802800e80c10100f441d6401211741c5200080c401072034110f00007a1540f91030601c103541000d4078400708002145280074418036900c0303210070310f05129003054ac1207501d0701514003e01c00e0f100c07a10001c5040415034401d50003035541414841d00903585c0d9041c40200a8070700b14010300184100c2c104441200070580e1800b941d40202e5101001742580e0f12100e041112042c0c0300c3d48108000481c00c09900f01040f054010140b0901d000d80301c403107104910700700740016221030b034111105104508042c002c1150076143c407201c40b081e000315901c1403052450a41c0d405448100c401403900d0b41030017008824042c24026130503a0030103035102c0c014014840d8110140102c4c58441103544226900e0026419003001301980f0340c44a4100600403280b03915a503207540c0c0003519070180c4005594080060092080002c4264500d8800c440250a6140c4090000c1c42103140c4d14900c0c00300a9140b000c2c4410f034400300502d0303890300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 504310440 1250 504309190 504309227
    0x50a0203042f03011805060109021e0703050c16030201031d0705040c0c0f051e070e011205160306050108100e06041b0f060c031b230307080708030402120d0c12 70
    0x174800c085542689054541c2540c4034003a41000145400c00c501c02c460210072418200d5103041c66000e40c200b10342c1c00c00c8000360148401040029420b076400d00c0300c0071341c09600019080480307003180001011110022800181d10341c3d0b1010744100b6400c001440c002301c1d48201c5e13000c900302d280f02000b200d103040100001403180c41700640c2d4400300314010442444904844c0000c000244e081c42489a0700c08951245500e80342d205c000510441100500c039006690080c011200503084104508481c264241c0c4240c59460b0340f88010b204003542030240c210783e001e52040c144098001614459243c09010f88000c10941c07036816003031b507640e04503080e0400800308510b00c84040381e42e0305000341c2401d860030012800120110005c0460a8440404c44903054103c4c883c910140081100c00c1c041103d481d031004002c1c4020302030000050f11120003003160920403541c0301d8590a0910502c0b4a12a4228010748684c1141a00304040c0340c2c090442c8940a0b0030403014103900f4150321082d10302080301480340310708 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 504311690 1250 504310440 504310451
    0x1719060b030c03070e10320c0a0201140a120e0a020604080102030a0b01030c0e040c2a05010c02210f0904020712080f0c0f09030c120a0501050a0203042f0301 69
    0x580840b00594440c2c0d40d10344403000e4150817a001c0103d4003000b0344a0401250001c4032490758020b515200c60744440d4002c90708140704400c2d12150010750001161883c850f0b100070102c0e01103580c0000110f280e5110100fa150801600140c061701203000880044141562048406181030f0100440c11940340c0140c002540d0725240c0c48094043d40c0101c1d4a0b6212034200401c401c1c0a52203031050400308010340d5142d10650000030b0402011b17154461082c0308005c2c2020060315480030440e03010740b4400f9540c40007a41c1109030b2500c10300f5900100e983c00295080915921413200d5803ca803100d44501c01401607a540b802c0c014103d801c1e0043c07011450308144049040010491135051180030f031301140d11010500c3d501c1030754090440b001100e0300c1c020072100b07004d80309206c902d0001401091354001c0940b0202d0340104041481090300f008141041c0d440300c01d4110501500384130b0140c20410110096182d440c0c5515100340c64a000b040c04084000302c0d07203964003109000006110094070085c000c0c0070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 504312940 1250 504311690 504311701
    0x5010804050c100f110a02060306010302032502030705060f07050f0c151513050402060d0c020f1c17010510050901020c04090b15090402180c120106030c0f1719060b03 73
    0x2c4d11030000b11300e07000c107000402c000054a030020b60100b241d0390081059103165540320044000e5000075280b802c2803401d405001014680d5001e4500c80c80e441940107640303034009410581e03d402e8002c0c100c500c1001c115018424000c1d40f01c02140d1b4054031258413544e840000c400a540740540d0b00d040891242040c0082c46880003003035001070051079003102c11405001e200070040040720760980d000bc3d8080d030104600c0c24805c009401c140003000d0340d40182c9410000000da114100303959012224100145407900c1e03000c0c2030300082403400d00345201328259602e605140125078102c54000d81d82051280118294560741c2c403c000344415800090014042e00c042ca280100c1c41040982d445080e0342030548540a160500e0303030710030344907036001404c042c01d620310200030032100b10010304a031001d0701d010001481c1c00521841242d00810455078000ba19500540005010700400503481082000300c4154403003003c00500c096400c03a400c2c0c020010303a8400740c0031754001070035076503c60480308030b02204000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 504314190 1250 504312940 504312947
    0x120203130b060d0b0a0f0e0319030e0705040501090c022505040f0209030a030e0a1d06120307020603040c0602010b0904122a0c030b06010912030f170a05061201110405010804050c10 79
    0xb1020741d0151130502c4460807e6010584a024003039034021036a03030440c14000040e01c2030b004951001c0c2000d064030607041d100c501007001e48200340c004110a986950102000543c100a41503500c0012208082a03181d003000034083d1803128820305200e152150050300301c0c1d800747c2d41213602002e0003c00320383d519003103407801401d600501c8070002d201c3d401c0b1000009410045001e0341080b1800c0554102d0b50b42d40d8401000862980d2914103d00b503c0140001401a01c40100031401039014481c15010f69280040007400c1d2041040c1050023281820107000000b40d2003151035885075582e0502810100b0304a5022007494641c1c050780b0400d004c1c45801005001d0340e81c002c1c00649000300c3d0444140e03aa11801540c10030828410395184680400359140400c0c420540b10828104a19000300403141525041d681c501040c5c5103031107210f548006100c030515114040c01c1914a0000003800550420f100c00704040c040d03481b80c0d6040c000313400d000408201e01848003007040c3c0360003000c010725048000d8008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 504315440 1250 504314190 504314201
    0x12030c03020106080309030304170f0102040f14100e0d060b03061e060603070903030c03050702150c1e0706031e05073203010902070f050715120203130b060d0b0a 71
    0x340c015501e04100418440000700c212540d00d0400b4008501c0c00b46401114103483d07010039030038240f9014414403041e44034030070b00041004120110b002007c20b414407019924080e05400030a101c1e03042c03a18038022041c0c01400000032030208407000c01103c0128102803003c2e107281505a94580560810000c00344011a5000048001c0e0054905c0d2940c03460244061840143c2d54100410306480c010070000e40304d4400c0e091114400c0c64020701f405820350100c1c8115070000480480014042101c5604031001c1242c05004032901c40d005450b09401e11070039459100074001c100405880e014401d985004140e820804103024510820984c41c01817001840e101200520581030354880144c8055450003211025038180c0303606819203513901e0000c02000940c460002100d901c01501d1096000c9503051108000804a6840c4c1c05100c82111030010043d000b00c02c1003558852041c000d00402000018000d034019a02003000141c0e80c9625000a104621220000f0b0481034075034100040e0001d540c201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 504316546 1106 504315440 504315443
    0x117100e0a0813090f0911010c021806030304030f06140603060907140d050f0601150504260a2a09020a021504110d030e1305010b03011503020412030c 66
    0xc03806171401c1d04000100b4aa80d4501c0b8818019074a0307000081da442444d1840b5a2a05a400600d9414042801030b00c00e030071800c00a403460b141041182c0c0519000146603011622901d0100003a0082e01c03150704541a143c030200b8880d0600149050240c80c440c0c019010690400f1145041d01407030002096102c0709600310100802c00500040b18118600c5010385400d6051072a1185601580100c0b02c0c2000402c1004009600804070000603201e10f0403862480b0810204680e403070268098000303003d44040c0c0c030b440004515082d0110f0b0450080f40c2e01d50f170b0072607580d440c003030103d01640443c0f6003da0010581210004000b000641d481072203450030b244840d031003c01152001703501e42400c0307003c900713540c000c0105031400203030300b40405020000c103204039818901c1c04e4955000c184140010300e1880d01d405039840313000350140c6000d0b00d548812100c1032040c131304004000c0c0701070000 = true := by decide +kernel

theorem cover : BRFrame.Cov 504136690 504316546 := by
  have h0 := BRFrame.cov_init 504136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 504136690 ≤ n) (h2 : n < 504316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
