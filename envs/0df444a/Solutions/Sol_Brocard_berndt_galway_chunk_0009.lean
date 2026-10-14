-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0009
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:20:25.311926+00:00
-- url     : https://prove2.me/submissions/6ee07466-7ee6-40f2-ac4f-e952dec8f09a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 1438856 ≤ n < 1618712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 1440106 1250 1438856 1438867
    0x304030b01032a060e150a030b0a0b0a0903060518030c06090705030705010801030609062409060b03042102030408060406020301050f030708030406030b030c100305070909020906030c0a02030c01060305010b0102070603050408 98
    0xd0302d10161420b11143d1028510308005042251203000e0300079124140d23808109402100705002c003607507581d08a107034140020040f40e146980c1010346503040302e51040d800203050741e42000314a07400d045003454003401c4c040040c03104007074080002d200703001e0300d005025583c1e8260785000f0550360741010b10034107010a031100010008980c0c190700c103207650344c003480707000c85c5c4907840803a07901d00d00c00150720f0000042c601c0c040c00d2011800340e10840c1c01234111340150b1031031410b064440c0e051461840c0c9a9405141050b03c0b0307804011720034410780d0020000304085400074109413a00101a4100b40500780c01820f1300003209050f498000345000482d98031501640c40c00741003000490142150032840d80e01841011071070740243e01d407420b402c8101c007000e03940010f241c202114010b1202c1201c0d80141205ca0041c042c5c0c01d103d41d510340c1140d42001340c01411550b12090b2040030b904600415211520951a00c0400001d1001c103400c0f0304200c107000da0a8540281c2c4800d426000c035102550041c01c548001e01c032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 1441356 1250 1440106 1440119
    0x403030504020402070204060f090c08010513090305120a020301090b0103090b0402120c03030c01020c06060a03050d03020a0905130902040b010201020a020a0b06030703020a0303090806060f1008040c05030304030b01032a 96
    0x515007081c0003600c05464407440e43c01213004d132241da0740710a0148550020410120290340308080703c000381460f003100b481d40341a0005041d4071020428200c0203030303540c40e94010107004034200c902e0a480e91321030054074600100f200c4000e4009108076000e56082144100d000d610a110700b541003580305070307c840662159001d00200710340c680300d0f4070500e00c1903030701003c81a80e00304050503079503682c4000580c0d00d5080c1071003d4148080688400d00030107041100b03000160000c05d0212042c1141d180043c1c890350062002c03100b80340c03185d020365000765541c111611a41080c0c2c200c064524002e0f50b00740810005078004900301d02c209400100141c12503144800050416654144c01aa00500b01c034505600e9800203900b0484a600440200700119020400403d060140aa00080449151741001340860201d0f950909035920072013004074200014041194015600000c0d03c0c02900312510b9a46929041c80c01c02803c0c04140c2f0a9030b904d00d100d660003c04641d002c628444070341c0302a0940c500d06203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 1442606 1250 1441356 1441361
    0x3050604060f09020702190308040909080d0504030302090a06080c09090907081c080106021204030b09070801180201030b060f1207030b030109030801030210020f06010506070507031a04020a08060f040303 89
    0x1849264815110440051040b0303030a80d44070042c010030800140d48070350f01c5c4104070a0a119181000c03c00e140c1c01000c00115041500303542c1120a540b030049081c60140c64100110b01c140c0816200191810701071100785940755001c0c1074042c80c1036070444242521794400b0364542104641180c1e00c1041000115624201806142d4000b01d0328411100d030baa4136064482d06084e200c0f0031007000e2049401d00d410046a014400600418550025128500c00604140464400c034000034000c1040381010599000d010050300d00140507120003000000d0814887c2d010031600c640c1c0980c0040d0601c401c010540c03810100300c07041d204009000341d1814500c03d80c41000110000d2800381410341d1441c046d03210303840a020740001688640d507604925070461042003020005801c2c0c9000b1548581540d002401c0000f8909040d20421604292281042d2514610300302c5d590f08010501080da070000e42c0782d0b640002070180901d100b2141081140d40765007240f680d0704011182818100c000c180800c000c42c0c040d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 1443856 1250 1442606 1442611
    0x50a0e071401090b070305031b0403020607020d03110d030507030b0303041202040b01050d0204030f06050a02070b07110a05100203060406080a05030403170903060f010801050606070203070b0f07140604031806020604030305 97
    0x43c1080e454183d51902504440c0e00650b04c181c020440c001b0820100e1014000550000044c4c41030141c105402c540114007180148040203004185402d07422050600865805c50110480fa080b11082e00800d03d0023030141c4020703a00b00c070110381008000040c43c540403050303c058403685403c10651000319001c00000d401071070621030501c40e040152401404060004002440c09280d0655600704e9a02c0c107001220002021004024030602c42e080004001140d96508415645000c96240001c10403c6081803a0300200400c20310400d110360002690035009148214000c5500700407041d5a0b500d01034503401031b21001440d54004000900000b025100890700c00d10580c10250700300009907011918101c010341d4aa60340e445104c0c01000002d4090003070035849282610398034180b08103503004c6a5904098007505080030400308010010300c40450a07900d0264020045104c524401e1070440e4840c41e00f95025000203940172800c4096810189610307044600c2a030041040f075031151811001004c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 1445106 1250 1443856 1443859
    0x6060a050f030702030403110901030305070f020301020c190204050601050304020303190504090204080a15020c07030b0402030102070206030f33090603010b060a020d03230103080307020a12090603050a0e0714 91
    0x34040c0e41c090001c1d04001d0340c41000d494000395a581d09500b009001d10004206d41480f03910a940144006580b01c01602d40160740f206242d03042e90390034400280079001e120020300141c80b9082811040602c2107840702d804a0003900d0401c215114100112094842118040d4041c2d10400002d0030701000c0c040801c510040c2c0340f822600341a102d4201a083c2d071300603401183c680d0f0003210010184a1001d400044e1111408021403901426688403620307178000e4480039000e000c03280000b80640d2800c1d01124a5141d00074451540c904e00b4414802c5604015070308c2c0c108401e0664118040c05179800d4210070030740b50080d1001d161804a078200040041c2c0189616055500d80c1100390164403a03030042d1200300080c1c0c01400084d00c02007030040c00c03100b0001040303103040c1900c022000706465010036981900d8200d82802d98940c1c0710707041a0319014003004000c044081c20704802c40702c2c0340d000b22070700103888981d5001d221545a00c8100020350756140511000743d00b1401c8100410b08481d003035045060f50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 1446356 1250 1445106 1445117
    0x906070c030f06050a0c030603030f030209011209080301030302070801090206030604050402030c0411040810020f0d09020d050304060801061d03060601050c070305030f07050705010203030f0a0504020607080d0b010f0e01020606060a 101
    0x84070358400b51a00502d00048401c40d0b258070070b01c004110903000d194007081691030101b007510f140d1780b002080c820103500e5110505900052007511130348207003186e00e842c980d48a801d0000c0340c031916000d040340d8030911055005014070040030503a5407040c011020190340043c0524103580b1600200300013802d0280080707a05102d41200c0d00b807580c0f6079020f64110074145000351501e40d0315054910342460003903115002c9403481042207401c4511031206a500180401d540020300e0b42042c030104420400c0d01001801e00d1101140010740b03140e0105940d230503181c082d070750201c1c14100c041c0c2140c5844015144140e2580007070002480e1548900d005d05698a0004100c42986650b500c8040c1154400301850158520024410b824042d0411544008000030701c000d501c0e510b81100d4000600c80060020340c10182c96201103010741d5105010b07900c403141c11018299417040140b0002d4001c1440d071301120301298030406608030f000d00a9001c01036007030060700600b54a40d100070401c00c090f8024140b0b0000e010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 1447606 1250 1446356 1446359
    0xb0402090d0605010503070b0a080f060109050604030b010305010b090402030d0305040201020c0a080106080c0d03020d030b010201020d0f090201080105040513020d060609150305010608070b040501030c0e041514060406050906070c 100
    0x5495040c00400d45024400c0010f4a505090a044c1403034069041f03111041c108110042010b42e1018506038040c3d082c503800350b1140c44200c01252401d0b03a075032083c3d602501c04540801801258104a8100c0c2d00c150000c101d4401c416040c44400c250490700039505030404020900214001e412050784944148161002c20191600180c0040302d6070b0813200241c0c0d550f000520044000f00a2640c0c403420498640b00808069a4001d50341e003110f003c5403041644403046052164001d4040e50b40686882d078050001102003058600102920300050780000d030030708000aa103052034490140243c03802035201803a103005401380030f84041e001c81e04a482c565104030004007004148103103e004503803002caa000e141e2860070f040d0b080d2403e42d04001325903002040c08003d45038214003110100da0081c02c010501c180249000d6881560f0a03501e95009401c08510547d12205c040e400b00a0340c850000302b50211606c1d005100060049024982c0480c10802c01401d1741d00c1d10101800d54648120404050076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 1448856 1250 1447606 1447609
    0x312090d0c0308040803040801060504020309030a0f020a0218090c12120a0c020306040605070807180329010602060106032a0309020307090908030402040501120b01060503090f0102040b09100503190b040209 90
    0x10f84c007651102041c1d400100d0f0920400c40d080c0130781001444220b8040d130860411003c41c0b91240318110880d03003404040703811381040c01d000b44054164181c0041c524110040c2400003810500c004503501400790240c404000003070301d003210108040402c0c4800502e440001040040c1c0c850340300720003071401d000d441207241006a4007080118890303071007a903011070242003400f80684270783c40280614041c40426000c4075010300100558400b240d400414240070b141440d900c608030608400200c4d000c01814000201d1103903000a41941200d4455404000d02c0c09008d0802c0e400a000b0100240855001c1c2503000d6014484c1d081441c003540024140c0c0d0705203591781c03c08004c80301100412110404048104429071a080c4215401001481d490200d4604607984680300790005000f000203114012012415103035042144064404603d40215611338032040d645d04d0542000816510804804050a5005100720144c078020510f10b80b500068005d441500000341802903941d40d00700c0c0d0b0910a80085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 1450106 1250 1448856 1448873
    0x5040f030f0203060f0112020105070204020d02070c030b060102031317150405010506010e040501050102030703030e0102040f120204150506030c0904020702090f0f0108010b01021203040c0b03160206060312090d0c03 94
    0x10362045400c000c81d4015441854100a0020407000d40071800800401850040110b00c01340d01d582480c1007a91940584001002030089802d0100c4191000c6114010001c8012113101500c2c011051a8035a0f034810300120391300e114a8000074603942586800708408403511041c071206000380c60039941034030f0011052301c010f800112001e0720310b40e44550600156503000800300b10502d078266814083d80d03051400107035481c8170f02c1000078105561380700d080728460029410f8602030b000081400c90982d9035155030440b01d40007100280d00ca02e1030125040100151158000116035020380b06608599502c0c241e100c0c0c0d600700076200341e00b05400f04081d030010b81e0342401441c400ca08011809a00d4100000c4442941c04160000d00282e0324107000207a150b80c0010782c00c81e242d00c50290b000e68a55851a2001c003851607540820060b92000c0140180441c9502e81d01601b0a81e0303508544044e0b80d1a0704050f41c8415181e80c01d1103c1d10208040000e07420b1040181c0520f5000c0e040e40c103452566071740d95440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 1451356 1250 1450106 1450109
    0x62b0f05060c04090f0c050403030c020f0907020a0212010b01020601120606081002040303020d0201050402010e1e030303010608060117060109031202010e0609030405010306080304050f040c11010c050703030b0303030f010b0a05040f 101
    0xa030b03000025043c040014944581c1d50840b4a49008110301d64091030081d0044c800c500014040c000c03407240200c1199290744c10101c1c804c20281c00200300d81085440a50b031526100b02c128415400c0c0c1700c910f105200144120940d15105900820159190001907101c41442001c00c2e58070a4440b0b0010401440403c481d0030100990080140d48030301e1420f009081810780425401103904003000d0001503a48401c807600c0342501201e84820106141045181201c00c060340c2e5a09400702000010740c0c26044039080384181000c0c1c0741e918028403420341f41d49440b10201c0748640468048507051001c1254034803c24800c8890703000000300134040150840c58004100c3d400d5200e6800010140704650741801010010287c0701c000303600382420100068450f40c4005010b6000d00d5444102c246268883d0180c0000d910700c1030001c0106184040c001845580071610580c0800d040268180781401d00108882c415810180e0b07625042e401e00042c422150b0200c222801001801d1001161f806072140c800c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 1452606 1250 1451356 1451371
    0x40807021c0803091b0102060403080a020d020405030601030f031803030801090203040809030105040506060a0902090d021027050f090105030d0e010201110f0408010605010212070b040507030f0602090405062b0f0506 94
    0x45e541060303000051401c0303500440604541100041c000060b0308240095041006c8540150315203114407410b130001c3c091540225414441c1200000501c6060501c8401f818040e50340c00d0f8503208110800f40c2c0005982c0f100600156801004200c10362143e80950340007403003420024035048202000070300f0340d4010341d000c1d01d150b0484414815180b403c15011002800d06000a6040041c61400500041401c1a02070300915020701e0702144144280b000418000d85298002814198844007206091450090a000394944804806145000080309040f80d900900805002402903000c035805150044801d0642d900d5498058620740244090300d206240d101c640364440386004e000c03500359116903001905540000c4011000d511100c4111041550844030000c02c6480340e141c407615060455001400ca507400c1aa80c000700641034000b40b022003c00c40c2c051099803103075001c2144004107070545040500d6404401c180c04a01c40d11103908031030103010300a005000350b8032030301e06080e4100d8003003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 1453856 1250 1452606 1452613
    0x6040303030c0807110c0f030a0b0c030411010203160201050c070302060406020c010806040b0d02010807140d090b0a05010e0612010f02070302070503060708070c08160203010603030909060608040807021c080309 92
    0x1d9044562100f4010390280744c500c1d08107201d403c1980040c0e100d04000110f50302500d080502e04166450810802555030381c13104000c3c40c1c81c40c240d1304c078845c1900280c0c0e04860206010032002d54641c400402d407052840003c68000855a6030750041d6429803018000003d2030141d8400000984d944102400c02400160041c04554940c0030004022081c0200158800c901d440c0032000162501e00007002c03050390a090910690b26602e5050350300f0020701c001e0710b00d440c00c00902c070f2501401c982c0060514901c500003040098480b445a1010b0324400d000e0310f1b1180b5690400074600d0b144c00507541942c4440b07070000207054a11000c0340c9081e0391100318203801690056000700f100d0b080802a03d0b5120900c1d251103a006d0038000710080c1000c005140181c401c1c0c40206001c80c10011442c80750a00d90360081c020403116940c0c1c0340151042c02c0910400c5407880ca040d00000e9180d0058181d0340c031480e40314405524003841542000302c41c2c114070913454486606041e400700000e515200442c0541c0004005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 1455106 1250 1453856 1453871
    0x10215040803010f0506070503030103020402070201020304080601060e01030e06060907030b060408060a050105030d0c11010302070201090503060412080108010b01090902030a0204210606050f0108070e030c0a09050603060604090312020702060403020604030303 113
    0x40000c1340e95543c00b05024100030007251300445d00101c00e0b03c0c192981100e016075100c005000407861405503800c80400d90003581d00010b201601304090175140c1c0020b0300c003400981c14005407551614400c60300700f6000b100c05000100e4540c460b038000c0d64928802000b030340c100f580f244601464284220f0380c0000e81c9644030014092072804018401e5001a2842c040c0400c55255481c1d001c0d44240e02d10883c14140c000c074860741160701840440300946070280031521580b0b020b003400c0c08603402403d070304400301c0c06810022410100c1030042e400562810307158107117464a06607428009601c018614030045038280300c0414600980714554400e000396001010060745542022800ca41d2154005480346c10013600204e5076903040300f1400c0d801300340c90512030040c2c40c820300440e01384031140310910780c84007030500c1c01b0075403104a40c445402080700f0340443d11070780c3d224410b01c001c0f5801c004020780407620308804100100220b80003400103074405004142002c0e0390340c0c0403400b284c20039002140400c2e01d4448 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 1456356 1250 1455106 1455119
    0xc01051806040c0b0c010605100806010f02010b060f13090504050703030306090203040b060603040303060e070512090307030206041403040f03120e041a01030b030a02030303010906030308130302060708040201021504080301 97
    0x10005480c0d00c00548032a04240d0f44038031601060348242c0c40c20b0000401d0b80041d0380429401800102400f03018080c101014000c01010350004171202d502044e10326402e08190b40c030500c164660300c08040c00c59494400d202e030034000a0341042000c52403450021801145917500ca010f0607005603c500d0042c80500c0c00e42c5005000d41c0c605811401c00a071041c401c00010451050141d60820b030305a906503070302e494a0400320003626841c1c0018031900420000d10003019400002040200700c3c2c110b80145546a01e17094a45a208030b480260040c4d01c444046030209011a440f085030b06011021a4541707a0f44030101d19102e861a0300586900d03200122904003a900420240e800280c11102040074910032070481030091400c2ea2043d04050303454010004544042040d02d580f03e0300203040b00e0320303580c0d10300d4903401804241c0000c4000908600220300711504603502200e1066150300646581d90710001c044501c800000e106a0440c8a0882c818140519200c201c43c0075500403a044e6a61358182038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 1457606 1250 1456356 1456381
    0x411041d0a05030403291305010207020a0b0405040b040504050a060e0a0b100303030c08060102100e0304050406030605180a030503010e07050f070c050f0a0b040306020a050705030c150703020405010819060b0c0105 93
    0x101e48082e4180c480500c0721103084400300d015840716040c407111f10060a9420140d00900039030200a412000b07458000c40c1c0724141d80003410031524222400d22466200c2c00078001500c50941d07004100d0b034441a010000036055410107036405080d901161103d0f500d540340c00c180d12600340d83c09a1008075030034050003456070501408800b0101418016218105440003e41d1041d2041d04841a250b43e2211300110403814800c5074000c0c540244140701c002d45038209a001040d0586007000490007030340c18681d0351040411b50b00640350b003640b100c070f0460b032030240e00034404100148031f40100401000b920380305080404c042d0030054000e4856100a078200014041e80c407580c031080a1080035030600c20003165094404650070f0380d0b8841800740c0c4854030503100b6243c0f03016050006209000c0032421100040c4001030380c0e900b80c180340500310415141c10318142c0480c07080d40540307800a010702c00081c0310711a40c0601910380b0101010006000c07135443c1a500c2c86500b0001c1d41c00c10b165112018071a81c144c0e242c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 1458856 1250 1457606 1457633
    0x1e020c010507080c1e040b070302030c0709050103020603010317070611070203010e030903030d0b0303090d050d0207050d0c050105031306020d090209060406080705010804060f020403030302040e09060411041d0a05030403 96
    0xf410248030034205034944050500401c24280c01120f4500183c42030000c2e1001138500600d00940c5607502c40b15585000794032600080c5020b8800e10400348006030300002030040398100c0350058402071452b401d41e00c03054412031004800f109500001c01c01740f0002001845105032508405941d9a01c0381130174410182921800342041655605c04c0c8000d50b02c596010003103071007143e02031100190822010021a0a50140701d22090303000ba100340c0e09405105000c50944c0c4a5003141d401d8908a176120401c001034240c5418020305a1164008144020350258008542001d5a0340484103414290380d18041070764071110a00f41c9079501c1d0400a001c50801c0b000c12034000340704581c1071021a0070100041c2d510486842801e04104103180418107019603075004041c2c0e909140030940d13443d6242d00740940a9030040c800c6641450300080002c10401002c079a41d801250301c00d6844265940600030480034261040c03c462a040c2c4101d800241c400d0308200c180002031140c000707103480e1441c40c1030411071042c20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 1460106 1250 1458856 1458871
    0x3020304050d03050105010503060d02010309050f030301060206070305090a020d06090b1609090509060a0b06040314030307120c020705010305150910090c08010312050f07050609060105040b04110f0c011e020c0105 93
    0x10000180100da0b0448e080e00d43c0024143c80c40100c2c50224001280684a0110064020302440c1c4190303111050100041d8180d889507021103841d074507003990840465078221aa000c2035003282001400501d401e200c001389860140001040c044541c1d180c0c03420070324066440354450100c1105622046401030440c00c01084100d000b0001c9240c100000b5441c1c14004040140040e034a5101c0070443c1c0c0c5c0c040644002d1500f094520700310611442c81d540d078079801070740c80402040720007021402c40801c0d030194a01495041d405809214508070040d07020700400b8051080302d038421501491a6260b10b00d03014404e0120004e03182119103010001000c0381c110b40324030030820550700014408510004200501c2d40c02514041e6910b82d6100240310300360080d1070000b4204d0040201784004002c0c0029054140c66084401b00a801c440008010450b0b2400d101d8200021040c0003480b04c22514001030301c80211420004182c9418041c0710f0041d4000118041402507404170314011019400d204d1250700008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 1461356 1250 1460106 1460111
    0x1050c0403020a0905040201022401080601050906060d050601022404020405070305090604080a020312180d020102030115030509010902060403050d1e050702060a0903050f03040e0f0f0601110a0c0603020304050d03 93
    0x11a004141211001c0c01303041d20154640c8003240841e4820000c501d6070271903910000ba400348a0100ca0382c8009403e10504912307104030400441c1d1840c0204286000e0350005000c64a05000124290050710f002003480d4198003c8004150b01140340040042d9441c089501c988201d1030144104030403150041d120341c003010f14190030407034031010014a4680183e00130941944550b00000121b103140310341405032421580c003206002c1442c218601d0158038007294010348030021a0010100d08070f0001b48195800b4003401c40c1e2880c90140258449a000414100041010354194020403556445540304403920351105160401c0e01d540002d00845540070322000002c031901518000f0281d0040c0c41700648600d900050007440310f0f00840d01c40000350381c000c068034404003842842548036040f82c45482800d4542a001500d45542048128071500c9043c2000d034058807140011905151a2481d0f81804e200e1f650402010410700c1041400828483d68050398034901031401d5800e0242d000c92a00c203060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 1462606 1250 1461356 1461359
    0x301030302070b1602060f07030f020109020108070e0105040320010908070302090103030f0e120102040501020c040605030a0b04050f030c010f06060305060307090b0301020706020301090203040b0106020a05120307090e07090302010201050c04 105
    0x764007041840c1101d10403540c403919902424070403100c6214840c4025480300d0300240f5800046000c0000d0000b00c0c2c0245c54900358800856070503070a0b20b804050003070015400e030000600f00d502074644502d9100040c9040b40c03d2944036619608603007905070b0800340c2c055074072074003416560f03201c01d03403c02400345c12024040051842e404254210018000101848204292068514460089940d41c0c080c000c20200c0c0c664a2442c8650007036101c1d000790750050103034070100600346c101406890201c0b00c0140092a0000c6070362240075820801030301c1160750340185800c40300303140c00801c044c2942e5080d00d0000143c0c504040b01b4101110480e50200d414141040204155941d011446030300300c400000000c00c03000031000c00203009118007440145018800300000c1040b1440368003a600c0355104003422602c1c1d0741c03600700c03d90b41c82d074040b540245168451084550f244a44002654100030b107070030a101c0c0710b9241d684003101c00008464820000c1d0790b1074410000d5607824028641c00c0300088440ca40b41031b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 1463856 1250 1462606 1462613
    0x601090305030a080c0c031824030a02030601050903030a08060102060a0603032c0307060c1401020705060109020702010c020d03020c150a09050d080903030f0304050105150603130204060803030901060e0a02030103 93
    0xc0c082c060b6024180602c0d4400100084030701380031540c1020102c4c6c02c0d40e9440548212002c040c0c0d100e11603590003403100b09141032052410000e18403044d210010b2850555449c0790485019500090020381009014400400640c030100040c0905e501203031203020070781c6050000245070640040103030712246d0501c001000401e4001000c0303061008026107030000906d04008880503e044003080c240c00d440303042c000046c8070758802030495086104080040402d105c0940c00ca080c0e0103003500150094100e100100041c0217150300400a0a10604042c4a42c1c0016000102d54003640700064016030403141980446181c0340110b07421206c0104075090030900a901c000344048068000c0c2406210b0b513160354400c0c0f013586e00c10742d0004940142180d9036460840c09152168006035004c0341c556003130001190840c2c00c1403803070800810001c1c00813401d654a40c407802d00c0764103450300240e0f003040c3e4810300803c04290510042d84a1050303500082162458901103c6201c8401848490424410b10043c07000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 1465106 1250 1463856 1463863
    0x402010f080403090b030106050a0801050a0608011211030303010b070209090105040c14040f0e0703021c050607031d01050405010e1603020303030103020103051f0305070303030e010b0f090a06080105090303040b0601090305 97
    0x8125880c0c41c0d00541c0e114541070798042003540000c4544607010000041c95540407006001c44480c82d034661044e42d076070b9401d0065801c00d6000d440080b0b490100103003e0040d8040c540c00d901405246845008030800021a04660082e04a4801d0440c001119400d41c14405141a0020a0303500200a1403600391621407400398079000351000c1c1c045400c02e02880b5900d03038000350b9410031005402c02002c2050005513070707181c13040c2c441240211340d003001ca220524044e0203d1075800e9000b0300500095500d48408034000d14003060a2112202d444045050b8032409118052049102d0400085c2c00c801c0e028007985003100660149903082c5410806000685010042d41c1c1103e5082c2000708182d12010001e42c4040700c078500002e5070296491000040c00360001d44a400c0f2400303a20100310400c1e0401203642680c4800000e10340003103148283d0303c0a400c110b001e491340102c40c90320014090340c94140403800d40b0320544014070107030b10110074007040c000754582c3c007a000303e02401c006201c2490740c1c0d19142c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 1466356 1250 1465106 1465127
    0x601051005090306150303070203010609050414060403050a0507030302041502071701020c0307060f060e040302030702090c0315010c05010b0301090317070302030105010c0f0303060e01030302010e010c030513060b030703020901120303050f040201 107
    0x30381102c1d440d0603024986040040d0b40b645076000b4001d00330305480d0248080104411101a114014a0036844441302c402142140c0110b8040d0f40d07803131a000810b4800c1c4c0b0701c3e5010310385c101c00700740c1e0800000030f500b0030b01f0f2007a645502d0203501400d5054030748200706507126021010704941da481001304103c84a0000125640c490740560082599010b101141008103506c0d44000341380300c2e0040800040503400301c010050305201f280c00480f1502c62904244080c0021038001e46c00c1d100d03041008034958003800c1015611441500085030100840c00420b0950b041c80c1c10480c041800c90040b030f091007142508540d403100d100c1c50304505641c54100024001040020041c21143e44410080140751007500024040d00030340751001c4082d6500d140084c02008002014000d0f94030b440c0382c5031440c81c840e004c0d060003000c10b1912103421b00103035140d0000400c551005107034144501e440002c016181c04040900070618403604040800343e0b0f08024003540c60061107000c3e50410681000010b0380c008004c000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 1467606 1250 1466356 1466371
    0x60916090b040e07030308070219020a030803100306020406050408011406030303010b0708040306050705030f090d05030115020c09070203070212060c0706020703030b0301050c0901020712021005030907170601051005090306 97
    0x40c00c41c80c048003042c0108802c01c42c0038118011140d000c01030642002406008a1041c2d084400030700d000f100010b600c0d8000c0b003000b50b1001341e01808201040084014507000209500b800140e542d5a542d428100e900a42c044070129501143c200320140c000e101d50035143c9151000d10038203151130740001740c4a1005004109200c20045414800d01280038251000340d64080f004110900b4480000741180e081211000e402c1c4840c600010030b60007000c91039081d0307424280c0b01e540c11039090811100c0103003040d900610443c460140304030300d941c0e680b6616a000b0440ca8020b90343d114541d0042c0100328801079180060342d4402401c0c4841c00c02018121149990040c900603140c010503c2e0840261600010b840e070305600385000d005034500108018032172800240c00715080a036030386040e264458020200a903001001149c07a100d010b029600644c0d205000300103552a09803640e074404030300c07040d200000c0c0041d404000180003a08010441340b401c03207a0703414124103100c401000641d1302c690003030010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 1468856 1250 1467606 1467611
    0x304080406230301090b090105030316030503060102010e060f010303020d0203040f0501050a0c02040237050315030109020d1b0f2d0909080903010b010c020a091104030b011706091609 80
    0x2446050100c54400c086103642c0a2aa5580d40d6641e00e800260a503c141c642c0705100f40c0000049502d0300204617181c000405002c194240d959460a44080e04000c00542c1503540300e506198540340e0a02c0340511450345031001d00d1480d411424000d02e00800445580190f5004100038440c520500e030050003100c000346003456590403800012200c0844400d0000d41260021441418034000703200d10701d020340d0380c454081118542c0b0304c3e800390b51f403140100000007280e002c0022418580080042c4421200050004144886a030b4081441c01caa08003054a2141c940035214860b02440b21140f0000d0041c0c0804004460804032000c00c0002640c243d1849402c50415058100030040050002010f4004c802c01c1640210301340030300d20340d20111482c0d1281d460910090080d40c003d4030290000c64000e40740c40462820601140000c003010084800160003d00000000508004030039020b0316038101c600e40c1d5607d0030804240b038108041c1c400d00850f040b4150246110503007211100803600c5c0407001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 1470106 1250 1468856 1468877
    0x4110303070b01270204080a12020304060507060e03040b030405100c020604030801060c030e090702010c030506040207080301051003020f0f07020f010809060a020f0405040f020405090703050115030c05270102070503030304080406 100
    0x441031580f001300b4100c01503a0000c1030001d032405002c151086003c0c01600d08444c4001c641100302c0c1c481c032a40c00340501050301407050700c3c0858091740c042103868028200300c0786000c3e200e0160490541046400311400d5106a000b00048412030081c2c8000d08414001001d070780c24a43d4020744800303014040c0c03030100928600210240740c402c074001c00040c00c02910124050510040c001d018103600ca801c500440d0502e0040b44039801e03e4030880741e82a802a000c0c5095074240070400c0035a02082d00f003d003c0540900101000c0c181a000401c400d20030310744215990f40b8540705204d11a071074030f00490706105039074040110038907000c5100760b407110703d40700c005035602030609140141c1e002c1c81c0c02c0300e40c1007803a00500006d1504203900410a40360b0854400c01a50b5a580044003030307075424001d00041d824012042e20015000750090012170a45042845c180030300d851266003031a81503e0391850510000000c2c1030256010b001d11006032034154007451543c545625401040d00c40c510641e0b0420101501c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 1471356 1250 1470106 1470149
    0x3020601030312090209040305040501031a0310021605030d060512010507080403030b01030e15010e0105060a140f090d0c090e011103060f030f030d0507030606030c0219020609040f0504110303070b01 87
    0x4060304644c000e00c080700d64201f80c00e008002d9081130041c280800c0c9481c00c14540d01f0162022401c000300d0040040c014444403034019000713134000006040c1c64801032480600018014400791040f03422080340040c40d05d20f06400c00052072901d181c000c02c1030b45003c2c140328942d81d00c0740c5060361090b018100895010f8500b0012070090400e1040c003a102c0c021060880050031421520504035807010039003499036600c440400041e4880c0c012030b400413503001607025203898000c1026243e01c16482005500f85206040468250807030584202c6030784480c200d0034401210a48241c81c0400350160080080c1d02502c914646c151002810305840750000c084000040d40d8100305408000020f5802e88c2c0e100c1d1208080310001d04400c1d00d0000200c0e050841c0814061f02c41d20854181c903101e40c1c0201202000c8841d40000701300581d0003660441700070004009a0349481c02808100b0050503000503032407031700e81803070841d86039242c400d544a500304010305001b28a00122171030544852030841700640034501c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 1472606 1250 1471356 1471361
    0x703110c060403060504021003050c03040303090501060509131202070b04050f03030c030705030a030e0312040602280903020102060606070c050105160615030302060601030608060112020303070507080105010614030403020601030312 101
    0x620300340d004000280110400003280c2096004a2090710000c00700c110040094040c2e810450ba91105008140000341c0842c0c4290480300c6542e01503000020090b0300e44011402e583c03402c40345200f0300c0a100d120a410014240d158200f610918030142000d1805c0100e0602140304a1090700d215105151414180395802c0c000c507140d89610b41c046a40d603080614005403650420740088020900c3d00c200184804d1021040362a0400b1003940e041070b556854ae1200d00035000f24140841014011003852101800d8491010000082d074403030040b094074502c002450482d000b042203010301d00500c605000109855006c00a40e502402c00c940c0f5600e09114840c0c0440002c4405000c03103042c90b040b03810f00c090860701e801c182c84c02271b401d9640703554501700150180e48003403041418540c80301004201c4480315100100da814802800d03203141000742e0f240c161804075140c11003940ea940d00c1004220541d041910b034541151002c100c00e0561074581c41c041d4440c0014030000d000d014410700c08550b03009807036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 1473856 1250 1472606 1472623
    0x1908030313050d020703031e030b090903031006020109020d0807030c0b010e0103021201050609160504090e01021317030304030806010309020409030305040203010b0109080c060a03090b0106050c0c09060105070311 93
    0x4004403500c038079000d100c072201c5400260081d10540207003401803000c1480402d41105680d05600c80101d1040e40f40c5d400c1c50322024840d5034400705680d681d069000307965008005401a402200115103d0905413080042103616900c40c00c20b580c034002038400162642c98486a00d0740c2c0150242d0307252429800c0986d42444039240c002c0022102000102d20003505001a6050b2030094400b403180340c4409074041d080b1201918515440720302d0000245009031200e038450120101e43c81c0403400c0c2692480c050081e18020050000300d0b03500459503900404201c003024000740340440c3d080a4901c9a0b50ba110740b00c0c8005800034040010010014007143d0107a0865600039501030402c0214010704c3c00c008000300410f5070101e10950078410500841e42c4070720100380c00c0c0d40e1048085d040d090805000c00655a124000712410b060b1aa4200000305c0d144c815014000e240e0b60f01d40ca541c0384c20b1003850354106000401114813821801040c40b0159a114040ea04519450f01301501c40315040000b0900e40f0501c2c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 1475106 1250 1473856 1473869
    0x20703051c0504080d120f020702090a1e0c020601050319030906030c030207140a03021501050a050d020f1801030b0714040e04030c0605010602010c0306090203060906010c0309050a060503090d0201050105060919 92
    0x5100c00d4400969100c6c00c2c64400101420b82001100600d0b4154030691084000180d80302c11140d01140400f03a01354000805440410740070120303200c2d02c68924017565030082c11500940c12403001013026050a20003000528079058000345154a50f940260030304040e4084c000402d550f0307070540403095000e0740c112580313030b0b8000c00300d51008100810550f5444010880880040c05400005e2211080a000d2a07040c2c64005040080d0603040600b405003407035089806a034031100b10460f81c0c405d9100c1503a9400e03c180c0c89608030200758118103114000c0780c03001d000381003000350310080000003103442d2040d07400b41c8180310f5100460340c0711401c00f100ca00a04d2080580f4052401000064298056012150001e0152410702000750b4452040c400c0740001c607401c0fa0001e50600010703c156110350410012540b090400b00724003525407010074141410f41d00450003003a400000d012502e041000700400801c20340c0f0084c040c2e503040030041503641c082d03552030f40c0c05144a00160381c1c1402c021064480070300745 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 1476356 1250 1475106 1475113
    0x160302010b0a0f03060e0c030d05070203010603020901140a08030a0206040605180d0503060f0409050307080a09080303010e0714130b0a0201110c0717060f010608040606080d03050a050601020703051c050408 90
    0x1210780c800444000e89101c2245c00781d161030310018618130081041c10404000a0152106040103074003550542c1c0f000d00203c0c2e01d9507072144080010703075800c09614007034540c3d41c00d01c410304440c240a104103110b554002c655980c3c01400329001c0c00350b000036402c2c0e000380d000f5004a00c83e151194401c1116480d00e291503070328001c07071008100055000f0051445101c00b140c040c607086014009220442c3c4400001608941080084a01180b00e031401400178a649207043c06000e983c1d02035035411a0404e80000c0c107418019402d000c4140d07408060710b80007451f600115440c0c2900d001040c40040302d035106140d03440320041010f81da21030007903003c03540780c40b00204c00c540c0d204d00328401162104800c1c000c0d0b2980341f4003440703030164040300014410700c074003914000006181d092010a80340840001c0044600a03141c40011071114804d00280301c6052103902e01041904090f42713030384142d075001442c0a0440d0312038a010400715400059000c4a8030350001c0410f45c80c000c2d588111550b00c19900204028030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 1477606 1250 1476356 1476359
    0x130902040504030c0309060e030303010b0a18030302060603010b01030501050924060a09050a06080103030503070305040204020d060305030304020f03010c0504050111030702030114040c0801050106090501031e0f0605030613020303160302010b0a 106
    0x40d0800c044ca03c10301d20079501c074050780c0d489400542d5034010054025030558400d20060015801100040600310040e040031004881100300b81e2501d071000d9042280103802039800d00c07c1a06090241c1c140c070070000d09043c462581844c2c007041500030010180006514010504e400600411b8082c40a800016200030394500030000c01600e10a100c1c46400e0007540f80c424009546881105d203281030341d40c9542d03407525640b107100045000d04005007003682d101d0382c00c0000c00d10040903845800002d520540185480b4540307801000003581000400034000e905202a0444541d0321500715000d072503007402c0007444d11698081040c518040c91000a400d986848441c3c0e03241c54100301514880c40c0300717104c072500c1c1070789946a2500f81c400c28030a100101d0482c1900344107560181d0092210f481100410102d03040c9203940020544411104840c2007a58031081401181130500c046540310000e807203440c011105503070110707030380707109030000103010100c415261010580b00b90452442c6800c014034042915 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 1478856 1250 1477606 1477613
    0x60b0c01020702010e10050412080405030a0c060809010e071215020408030403050d030606021e0307050607030b01020705091003020f030703060207030302090a0905070c0303020d0e060408090108010605120402130902040504 97
    0x7544102da00341d000c12a400c104560343d1400c00803c04001e140c66a8850420703251204242c142200341800b201d650348184808151620100a014020340c001c0c82e0302c081d40c5140a41c06400a100075082c41c8070351b41400e43c941780f00c04000549904403440f1480500390380c9114108644540302c0c0041c4003249074000600010381c22000000380c401c2d28011000d40351481d14116094040365454403130800960806840500701110010049201c282e20030142c03850041d030b0380d4034541000e05c11a0204046039031015420400d50381001401c01800064400507070030f003095017803201c1c40000e901c00203104d5544048507001984084c042035008651000302951100c41a140103400f940004261034020400503e0004020000b030290b940210203e44400800d000380d0f460440c040d40c4442c3c2d84104803501c036241c24007824410822544035a004521503601c400240700014601441039205004100060141c8110350f16121a620f0700164110b4030075072211059207401000e80211103000e9440382c61f100400091 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 1480106 1250 1478856 1478861
    0x70e0a09051b03070617010306020319020c010c0206060103060803040905040501020c03030411041b0e0405060102030415050301050901060e210114070302030405010b06030106020a060506030a020a030507060809010204060c0305070204060b0c01 106
    0x400c40304030140c0b500d80d45c4501d8101c55090512080b150315003441001000800c402d54000c680040c01480040d10305810303070301d0901c142d80c032078412403205a540701c0c00201d681e5810320103550042424070702401103e00d040740a5a81c0e001e035015641201d84e96078041420444d00f581103850041d111003c1c0c03510ba00d081d0500c3d0001d100d9a10b9040c8c0281d09045809540d018100d0030640c04020036200c424036580b40005000007000004c10301415880f04001c00f18182501e0004803089003000d5480b540d036981060700b448480310701a4044030a00a2603101043c140c1e4914075001090218210000c03500f003034025115024190500d800c18220b0040b000340402c80394190011403085019800034032419050130140140c0344024072802005800000c01c0000107889500800d80225004003120790102c4a50000740305d01440398011030b40c6a00020f000c10465030842039a944c00134408000b14145850070f80d010b481080d080000808102d40014098119501c0ba40020043c20342c03006066120301c840b2654600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 1481356 1250 1480106 1480153
    0x303200d050a020709060e0c0904060b04080307050f070e0c0304030309061b02010b010206040b0c0d090501050708040c09060302030a0602030a020c01050405010b01110c0d02060a020718050103060507020609070e0a0905 95
    0x1406001400f20f6489004d0181d40c046500200700e03144141c8d140c2c56120b17016001295041d510030703100c26001481d207030444068009031107650059aa40d04051414515140426016400c90b801c1007404004050341c1344041c03503012600a0107941e803070755645412002420240001045246420700601d080801e100145202c0140e6400030404244044010380e5a01021900102a02069000201c0c0400480050800901604408104980503544007429913000300c90000005041908100c14000c4c5161944000c0c10750b00e170100415400d43d0003103502d81110001c0507045940000c08560324415503411507101c2c0350424000c0006050502e86580030740441d03101e0f01d00092a04409070511180031800007002500141042a046115070903c085504648078a60542c0513a220025141c40e500071504c03045100c0c42e074005065811882d00d0400c85801074190421980b100040140d00c0342d0014140003500c20b2a410f4020565404c0d05c030001400808030010301c54000d00303404190000300700c8040803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 1482606 1250 1481356 1481377
    0xf120501060807090801021215040209040204030605040318080309060304020d0f0b060306090d05030a1503020a030602040302090a020a050306010305100f09020705070501020606010c0b041a040f0b0601050c03040303200d05 97
    0x4803581d0340c035005c590a030302030000640c00c0f0b00c816401040510096500043c00710501070800340c10140c42c600058101d0308240d00c182c40d100e031504204400c05a20018201050f40c000005554450801d90480e0b641d02504025901501c0300101003020b5584015040d00c1c05603001d00d6240803014240340040c000030301070b40c58901038030405c00403c01c1d186010442c12400c0c103956075140e04642d00c5d109150041c2c400303076107c00704803034180300080050780f12000010301850042402603980c501d18030520400d0303003008203040c3d406071060082c1d420103507004007100c2e0041000d103404107164485002c42c003c0702c5020342c0641d0080840d41000075a54800d6000760140034050829140f0540d590001a61215030858001e03000540c4030416030700107a4003410407500140207009186540c0c1c10070646007201c480565041e18102c1c0780d010b54034200022010840d0f4000001c0c0b801034100040b103030b00247d59018500006080c071401e01d0b01044655a0040103004c40181c1008803004c0c2c6543c241e01401580c842e13040c14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 1483856 1250 1482606 1482617
    0xa020a0b15030a030c020a0306020307020616020102030c12060a05061b010605030607021207050102090a030309030204051303050301090e0a0602070606030209010812040b09060903070305010c0306060c050a02010f120501060807 99
    0x84101607501e00c154050003002c2c015142103a0141d40403070f9000e0810f4000c90744080c50400101c040b03040340c40038500c5600c55400516007801c1c418075031501e80020000305001c6a004008200c0006000004e480d030200d91000340720301075110790700041d80c03444aa4105580041d0040741802004c400000500a019a614001c11549440d041410b071035220441d50200541d001c2c5115021505100307000305030050043c00012300303044a200000d483e03522154020b800140c0301c50428001c1d4a000d20a01d60000c02030300030403002001a0b54007038000d010507c14a0303d040d80d1181e01020380c903000d002a0501070341c4000110368490303541c83c1c550010070081c002607005128103030000c16a8000020b015502401c02d500030703130070b080c5490001c0905034400300d03e01e034116405004801d8030751401c200a00c05184104000b0900d100b0f214002030880e81594000800c00c0b04401001020503400b280b5140c1140d0203203440018004001416205c100c0001c0861a03200d2420000090503580440d056020b1030055498 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 1485106 1250 1483856 1483861
    0x3011a0f04110901050304020102070f0b0901081f06050c1f02070b0c0304030c02130603050d030c030b03030403020609060703050405061606050c070302030306010309031101020d0f0c03020408070603020901140a020a0b 95
    0x240300840d400904810800b2408200c09002036001e2400b0f15801441481264603ca880c0c1c602040040c1240d440403070011400306043c0c80a60700f02c1e4000e0740c400000d601e000304031b40d807520140300c1040d602c0c4202070034800001500c0108440601004184144030407580480400011444000b94024001034030711020311703008034002500400841e406290107540d64661800e080e0204403101030b811401001d404d0381d0381070000c00a0700c14032007052400304c5600c000403448440b250190640390751700c60b060322a80081009000580c0da840541c0c807000700903242580c0380d0101c2e2030180c62601c00c40d000070364061400300d80b6401c3c0e81c0d0f661822003035440c42072005124a80301d00103116024001e0329001800340c0c0061000a00c903511a40c4801e444d98040d15080048005082c00642281d00144034564481c0e01c0d91503a042503041809060b25120f01031a04501c0d05203030070703100e5032582c00e01d004002c1019000100c1c200030340e205000d0b400c80303100c96620051b561603055001a43d00d10b15808201da90321001d400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 1486356 1250 1485106 1485109
    0x103020a060207030203060a020d020904091103010e06010b07030302030c13081c050a0e060309100e030c01050603060103050a200a09050402010813080405040e0a0807050a03230405040903030b03011a0f 88
    0xd0783d0040701e502400421580d20754100d034130060340010b03050588159081c040b40c1982d54950060511440c080c0305086005541c800a00d800e58021116411080c0e1200004000120411040340c1c10180c042c500141c44c0e41b80c40101000d54460751401881c000e2f00220301040402d00850040c0000f03800c07286000500044200986090142100103404038104041e13110140c18600020b581c4050781005a85150b00f0110400086400c0c2d101011101d600102c0c405240703140c00d01c200c50b00f10780101d00030051507155a40300c80da90400315000400b00b5108d003040d442103a50500c5035520010303005102010a544414104004000449013070340002c9496012450440d42128001129030304041d003607141600300000d11010f86501080704aa1340b191402c0180824500d00140220511840c083d01e5500e4003030400808031182201019030824082030030103001004042180c04480c0b00f5540890310a06604054005003044225640c05500303245480101282c6198108804142144ea50004007901c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 1487606 1250 1486356 1486363
    0xf0123090c0306010506070206090a090501090606080105030c04180f0b0a060902030603070e07020703060509010c0905060c030304110111030a02010608070603020a05070b06040213060e010206070305070c03080415140103020a0602 100
    0x2800702d400d82c200c00e00500c020f007090310051901c0ba0003d1304017445c220011011401c4a6096400b034a411903998005001c41c0300e46003c2c0d1801000c40b0b2070081082e50400000a440d4400d0502140c480c542d902c200b5a400c48401081c07110071500700743c2035490000d0031706002c5d404407005c80e001b140d010318182c0c2c040755a4566109881c0584000f43c0201551818111044034480c0090700d074809501c41c04200200240d028003034180700c1d0700c8030170000c90b0b44000b4031005030651860b03401c005d1090909000c08065580000280c03a40240c000145030400c11000d801640d007460b508249408900000503240401501508201c2c200c440c5102226200c655820084049000b4052208005030b030801144c0082a01180b009030488001000145030200c2d01c50ba6001c2c0300700c164040c0000c00c0d001c07a8020382940c0c0500000d40d016039541428030072440c050b4001461041e08640040c28440c4130400b00702405414801d8079002003000744104051080004030102100c803d03c4124400c0c00d0100d8041110b03031010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 1488856 1250 1487606 1487623
    0xf0f0106051204030201020c010606050d0f0203040f080d0207020d11030607080903040311040e03121e01030b01050904030c020301020301170f0d0509010507050109080f07031701050609010c02030f012309 89
    0x196625402e09020750702c11000001c018106070300f190f4080c4182d01ca000c3c5c0a00c05c00b0010030461f01c1c3c2580c0d070441c115405083d07c1041130b01d125564414001c200c04140c142d12081c1c0e0302c0e58403020b410340d60680041044001d014089010b5080355001602004010088588240c030000440448010703943c1c4a030220b5010004445a81054005010420000751b00307a49204010134002c00100d00c2c40c0b11800c0c003915580054045102455648050015180100d86c03c072025030038040a1a000c0e6066403103039102180c042c4122070040d42070100080605205902010f000743d4001d00075544c03965a25000040e40c0c060341800c40c024040c0c03d0704001c004600140500c00340d003031911441e00308103ea80064540d0340008a00342c80300d540b900420070010354100c0c000d04030140c000e10f005848900c0740c1801840703c1e8412401a40b0310b1f003c040103000664a2070107031107420800b4600708524032040e102080c00c00451050800666003010012069010001824241e000c0e03e0850341f4456540d02c5c9032503a030340d1844e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 1490106 1250 1488856 1488869
    0x51005010e040b040605090709030b070e03070b0d0b0a0801060602010b030102160201030c020307080406080a050108010216060510030203150f06030303040b010302090408040b0307020c0a0501020c0105030604050603070b040305060f0f01 103
    0x14481c180e04141030540145504900090000405950380c0c00451070b40030044803064009500d1101c180100701d079000c0001e4000b0150714054030140f2141000c01e030364000b42d0241c11014200400c8100341c002c6260020391040c00d0250607440c0240da2000b505000c2c2c0003901420025500308403818642d8101442901c00c4d40341c1c0c04e0f1254140052540040d03008140082941045010802c00780002ca52604000c0006008075603034211240b501d15103940c11110180c210380100e034010058903041449003202c0c01c20031500860000307285d840d075180c035160302200c0354402034050280010607070303800001600851055031301d08030100b41651884200358481c0b0040320001e1684146000500240c242003010a5016115107030040c0303026101c000380d04068008417000401680007003d4500f06080c2480c0b0880144001e0005100242c020f03000a42640002048c460245030761704002401076408110740c2c001000000a0305039030703c0d2603003811030701d0b6202140d1840d0108100400304800c40380560940b41211030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 1491356 1250 1490106 1490117
    0x10602010c270e0c030103030e0a0b1803030913050906010f0302030604060b030c0d050a0309080f03040603050c04030803010303090306110f0a0e0109080718050108010209010509010507030507050a030c020405100501 94
    0x40550145240081c6a10080b4002294440c00f089a00d1400304860041036610f00c42174072507240d450000c0c465040025242c0c0612007040041081800d042e00b65415410b00c0300500c40204084808646140283c0180c1c9a009208202032402e00440760303c041e0160a401e401c1d150300e603803140b04641c9880954417000750152310410001c0c0115210ba4498840d8401c000c0944140b041501c0c0003440b40d10801340103440981201481500701a00702c0c014000900b079030000b91092070811540542c990007548506800d1548400018080c43c14403407c507000ba541c049101070f02d130f5850317040c000d1466405020840d00306180214180c1070300c00203c2600d13401c00d140522903140c802e520800f25010544480c41506201195901181030402403041001030182003001490440120308040d081e990181c0c0501500d91040040b442c040e40c1c004100c0307440300300078204140d460496150881c0c140c410490041c016004a880110070594007040c5520024002c480500141c1c4a5038005c41d001a83c61142c28045030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 1492606 1250 1491356 1491377
    0x1502040303050a050a03020d0609050114010212031b07060903020708061302030606010302070206070b0403050903160509010501050304030207080118020406090c0c02040b06040909080304020301060e070203030c0d0204080115050108010602010c 106
    0x184100000c08242c5e00d20314000d400d0041004a682c00d440043d08140102a11900184210310074065040180c050902c01030550440003410b1012511001d00b51100e140382103100700000307950010444507595403102c400c0140c000d55050081d250050390242c1407032801444089001d01c48208801c0c807000f0303001009007069403101001500290700080e0308907004070003440800c01083c000c049a603c154001d0b01d580e982c2d00403040c10035080052842c654105550321500920040d02d850a01d01d043d80e20a0805a980e520b40c1d08050741307403901035407000240798240700c01004c500f1804c086007003007079100f61421f20165844000542c00d03108000c0d07a000029180708441c001503d01030b049119408400341c4640d103403a403641ca07114240c446140b000d0320404030010510003142070922401c0c0040800010045160415a0009441e4880a486000080c40c00704042c584240d0560480f401020444000c100111115807550114a101e1242c1d5002c41c5509000141150060141b11403904040e1b64505545 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 1493856 1250 1492606 1492627
    0x11010c0c060e0d0f0606050301050105010c0503070204050405010209090403020c01170103050606010309110303040f03020906030105010308040e0403050409061d010e070f110c09040c090b0301061202060304020312040f03150204030305 102
    0x4507180300c0c1c015882400c080c81d80c004100107040d02404c481c0a800c001c640c1e075003401301b07050945d20f043e0712080c100245003c801002c41c0012055a0040d94101c41c0821a03445508186000e40900075120341d000302010140020150000340030400301e5020b886082c51005810b600290080007441b0181c09900301c60000382c034561180d032281110904c44c40c00c2d030010000810119240d078020340c10034007060407629070504c00d42c40e2540036154400c40c118000e1100b076056981d901010700071803199030f203140e641c0130115041600600981e40500800e00042100030b54802288895903c0340544100d0541001c0000c20381e0811008100c1c8101800e0702c80c40451404240201c819206c4208515500e024a031943c4c80c1659964000e507000d180140a11488103003808045011a40680c216511a03807402c0d4041200700c00c071258401105404071041358513541c40d070021a0810511018140c2451800a0045140200a1285810b582c0500e0b000a000105070314500300324412408040c0215106122203c82c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 1495106 1250 1493856 1493867
    0x6030f19020702011e020a0516050307080d02030f0a030605031504020913020a0501050901030608010c020304080d090e010e04050114090105070201060501020f07050d0302031903020d05070216090203060105040513050411010c0c06 100
    0x1c03060a1310440d0801f440c00d458550400031440c000c03510303002d1503003c201301610b81001448040c004070406071051650a440c0070f50749200d003100e22030440c1d42c08142c12800318025803142c0300070807014003501d041040b84803d00820b1501102c3c02ca01c64a4000b020030380c0090410b1010045c2a80a810086894104801982d40341c1220f0300341410980c640201048101e006e008020703180b01d03d6001192a1400c001843d0b090100ca0b49444d801c200310b80c5420041052a000c00c2c50440d13000140d40005a115802c005015211464440c40103803694420300ca0b01c10415800140f040007668001c0200688810049850b514181c442c0b031100e40c0b000c82e00f40480d00d0481a55103400303101c1d0045900c0c00545507020800450740b0700700900441c0d4080384080b041e8a0600400c0c2c1e120b0101d00c041e001c440382c1a0400380b1422203d018190005901000051483c0d001308100c0d0060300009000400c003001c40d1061402910045408a039000003404d5802d45550060600b003513510381c88000642d040b418800d086a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 1496356 1250 1495106 1495157
    0x10501031103040c03030e031006090603030807050c070902090406090e0601050a0f0503030403060b0a15050301030b01061103030a0c02030d021b010f020f030412030b06040306020d110301050307030b0a02070206030f1902070201 99
    0x38140501244d480c002004ae1050740018584498081801841c500340070744101402040441407110400071034800344c0000c12110284c961990300161102d0080d000b080c0105003e800c0314924038070b40011050100c000042a038100c3d04120f1f141c0007495143d440a460710001413140c650550300030300081c400150a40c2124031702d40005803001e5111565080d43d00c0308045604020f10100c1c4000005006000c0a003103007074050719503401c0c41090410021003480d50303803000500e50042d25a941400a065a1084c81180c03500c0c1c2d40e42c4001d40d00e8410703020130000250309001e40f01c1340039031808600700f40101d206e0003941d00b1855163701050440c0e4898640d81000c0301d808854004140d5036551044290361044003404c080d5019007001603d817040075551008507203000003850075022083c801005590b40004e50700e403da0b030b03000754010541d4039000740c000c1c0603004200d0002e500c08404010043c003005e10310200340c070ce951800072101b00138507005a8501240715082c030281c0040c1e1003203817051000c18542c50140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 1497606 1250 1496356 1496359
    0x106030e030403110d08030708040605091b0907180603020a020c03010504050a02010809030d05010b030702150402030606101701060528050f0304020607020409030513060503011508060102070305070608010501031103040c03030e 99
    0x45c18654030b41c1d80c0d80415841200c50740c0100c1e4440041c4818800c5610400364811000e10007044415503940c00f841d945045251070303500c150040c01c002110700d4401c0e100e200f1400c080480c58120503031103c40141c042d4002e00003040c0103110304001240d00c0c0c581405174501954100000d000b001d212071b001101d110703000030007240705803104015405200042c0c0c480c80d0300a0543c00c86c11030310f038240075038000c5c00d094155250000c1e101e01c000510001d0f984c08200c140c1c2107082102c985200f900c1c80402603540f00079201100c02206464000001c220750008002c041c038900403441c080ca00f6480caa0002034605100c0800030002c1c5c420300c0a421003e00b500004c5800c680000c03e10360800807940d0006040d120381240850000d8400b2a001500c0002d0040c0d440140402d4208a42103604103000c4031400628030f40c030001040101404241280d00a00c40030f0043c0d03401805480c0800e8881c08007404150003031203103171300281c600341000489144642c00d41e0700070b0f94015418401a85180c60850f09000103481c0c06 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 1498856 1250 1497606 1497619
    0xf07020c04050c03270703050105010513050610050a03060e01120308090601080c040c090302060304060609050108030405030c1903051e060105040c0c17090402070b0613110403030305100302060f0d050106030e03040311 95
    0x11440303018104886c100a41c490b40001c00c0e59810403043c04040c14040301142d40044c146000d001c99030384c3d188200d030f030000010b00c0c5c0141c86100c089021005010541d00c84000e141322040013281c4510060080100d1902940302c805880c0c4554a03c250341e14400d100b404199000940036140c00c0c0761580110b11422076070302d0601c2e1a0358030398000803010350003510100d400310755a600c00c02020320303a07008850061000a020b03609051804c400b0903100e600d080d00ca5072107070a071005994071680000c1078071005140c10000320788040d64039000c607070808400c0c40034154036445281c0c0000b415161a0180320144501036807003007200c5000765075000c40d041c40305045401070001481405000d403518400303060000e0041d6240700140c01c000050101100155050100150404607419040d5980d00200c4085961624000510340e4620995540c09030131500029400000016261a5103001502070000e881c410301c400c00041c0d9858100b41e08994002024a120350400d0004202281e034070140c0d51040d11010389407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 1500106 1250 1498856 1498921
    0x402030307060e01050702010b060f070f060f050c07061a0604170708011b08010807050108010e0c0d020a0905030c0a050102100f02070807030302030106090b0304020d2003060f07020c04050c03 84
    0x5a40030f0f21440782120f40640e66420402c82019424000c00101a400b521040e142521030341c1c440b1894880c00f84007070407400c007808104042040341d0344501d070031038410030042001c0d0401009501169118047c1070f13637460f05080c243c001d100400b408903030031880700812807407605191004442916003a840d100046000d85200081d03104400c1c091281207a500f80c0000c0c41d8803035840340245c0b403058103801452080d0300c807040600050b600710103124190381d0380d0340f95140345590701084010340740b08105039412054000f05000c841d070f40d00705882406480c1d080b81a02d000202e000f091242c0501c640c07007118016485a0140d105081e155442441070940b44440586010361549420180754847c10381180020745c0003004002c9981d00040f110098410040d00501e0360402e9000288014484440589210840741040480d0392202c10342c2c030b450360005402d41d00c8900c0c120200c01e000d00c0082750b80340d001d07003d1f25054001c42d291a11030035104104880382c10b0b042d03440d2012807600e04040d0f181d42d9055418948031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 1501356 1250 1500106 1500113
    0x15030604050d0215100303050708040f1d130308060603091203010f030b060102030403030203090105030601030b04090501051501020c030a1e02030303040606050102160302010509040902010302160503040e06180c030402030307 98
    0x40e2185006800400504841100c020b00c0d041e07681c03010216412050b02885030354400f000788181141c0c4c06140040c1c80f8041d500b001c8410b842140d01048140c49a650001400ca407050340008181c2024050540c06070b03141844107280d24002c1c00c006000951354800030351245020320146070420280300440f5907140001202d0040d40e8001c0c0c000386c40d41e1210040401c1046805001c05074031200c02c0c07000d1800d103460740c1e402039540c2c06110225818014017100040460b4803030340c807034034035240000c0084c442c0c0002c2c1d08100b8000d20090380c44050140c0043c051a4255000140d290b020040250040901001c5c40e108d160311030600c0b41400c80405403014900b00503036000c001550160703008850016215203450700180c6044410300320040b80b0100a00e00f000581e03086002c0c6d589010341940e0200d0403101c2880100c000b0300c91950544c0c9448030a8602c00140b19000004d00300365045404c2e042c03216101c4404000319840c0d011680d00e86138040700001072900c86440080c580181c0302404580c28015035030b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 1502606 1250 1501356 1501363
    0x605040f050603061810020f09060d1a010207060e12030405030105040b09011401030f03050309010b1302040303080604020408070501050d020c01021b0c09010303020c0d03050705060a06030b010801050c030601081503 94
    0xd616220301c18402c040c60b00380903e580000d04046035800c81000c02d001e542e25426181c052030040d99001c126801035004503004c0780c0405a0003001e03e50f65451003100e0324024030300c008450003243d10f400402c03941c5500001d80c403c142c82540c0c592100000350710040080250704425404500c0c0014440003030aa10240030321070003075102c0c4802c44c00601e0030800c21401c5440e03240c08a0100e104141c0100003241b4070f6501c90640307a8251a02e259070742e40d4208071034090300d001a1400e80082a00c103600d00784246641c041c0080d07c0c0f01743d42e0a04a5110501044240d000318007030740c002500301580400a542c014802040b0b0880ba0000140c24003aa0303a03070080c00c9030403004c01d4000240c1d028200462100c020700c44269441d004480810302c550540c0c40096540c400740480900820140c0281301c1454029802d0b02c00482d482411501d161038540041d03005091a44800c8520b88881c20010502d0101800707580d114410a0b103010b0f00f0b41d03648200450303c0d5440542202a40750908406c8451a101071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 1503856 1250 1502606 1502621
    0x307080109080903060c030708060405040f0b010303050c010e1b040207020a03060f06090c020102070c0501030c0903050303041a0603070605070b100302030303070c0209060604030203070b0903011104090f0606030902010e0112060504 101
    0xb00c07141c5494442d0f4009160815400401c10611800300f0010004425082841d2682000003500c000500b0b40e12403512100d000d28825001d04042060000081010f6025004003009642c1c10000e0041003043c01d0102ea031081c0031483d100c20703000048005d08450a003903020303041060000304003400303255482e26a076045417420680302c8050390300c480051081c4880e0340201d01040380648021860011f03540c0700ca010400700c50040300c1c105501d41c4007103032440384560603034000f8540050a4990300d040c5450b100c0480041d444001003044400c1d03000880c1c51801103900c60840304d483d12541e181a5080c0d40304035400000a00040c0c02016400c0044056141040903510914031501d98003561900390041010f007140c000c21705031045030f08000c2880181c801088450480f601018210b8684505e180000d0141c00c1600028028200101d800501440303d0f411000000480b071500b00546500c82400301c0c141d0302d4411010380400c480b2140c030312a65115012040d0800c070485c0c4005442611000001d0568205 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 1505106 1250 1503856 1503863
    0x30703020403020102190b040204050601030615020c090106020607020604080a050403080a02010504020301050a02090a0302040e03090306040308010311040203010f140a0b0409020a08160807050d0207050a03050a02160b03010902090307080109 105
    0x1c6424000c5503010071102d841065244882158000d5030fa894000d511001000240600c0d121004250781781d020b500a48044c1078101c0403185045860b0000039a0750140c500401e1003501007900001e047c0703002007203035406800c00381c0c00360100d641e95490b0789909611840c005030402800b00400804103240a015008043c0b0315400030500381042d00416080d2107000e490f1313443c0c01c0d104004035840d076690507846404603541079038049120751254095900714004c5180544d0940504000c0004240c0e20180c42416a48030300401c01100c0750000501c0300f280424041d018402c84003000911040001501e5814500c000411240c2c11549903e02d07042660004c0c0d0184175125008210400181d402400d1198000c02540c1003240495907490028110000a8001c400f130100c0001d1860265090350115984c4e1500401220001009454000c003907500c0080c0510060041802e800b8110301c61069040c00c47c0c00482c4414116400e1407030440c0203610a140030b99061050080000e07080c1c10a000d980c081c64003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 1506356 1250 1505106 1505111
    0xb010906090c0f09060e030a02040608030a0809060601090e040807050f0c0f030a0b01060309080c06040302030403060c02010b01170604020c150106090f060203030703020d0608060906090106090908090405040302030f030703 97
    0x14140d00103041c0c0d002d084084050080190742100300941c00521a41110a5031600c45881c140d0b013404070741400440f100181d0003508200022509500020090100d0045e913590081e955941c04041c54548600741d4a050004045140402035451388100c4503410070701480c101d5140071455a6024503000c4d207403403080c00a400200c1c0c1001c403498128980054804168003600300b00c0c0c15980c1c0c4c10440d8205019034000c0c03558079500c9030f0600070f1503016102044c240500f120260300386400c002e503807a00148000c03640035041110a01c8800d2040c02621242481a152000210100c0100e030345004001005150002d83c00d1008450100c000c00c0240c14200c60b658114803c0c2d410014001d080d603a0304d42080f100480d2440c0c0400006a001040740d42c40760b0103260068550400e02001400f40c0015801181d05100300070074000c1030a00030034032030b00450210b4000c00c0900c1d5140c0f18a4180c60007514090140d0006120b80c11482c00c1a030407141e4080d10a105907882c1c1941d661200b0303034030b03001682c12000095 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 1507606 1250 1506356 1506359
    0x70c02010206100e0f0702010608070602011505180a051f090e0609060108060703090206090a0605090109080706050901050d060807030308010f0801050c0412020409020301020a0c020301140105010203070807050a0b010906 96
    0x5070180001a00001c0301804a1007042c101004070408800182915917841e8003040001e43c440e00c02e5100c1d07006010b0300401d9410269407514000e01a20900c0d065104410b140000042d9524001c0d410b01c081c00c82588041034181d413400302020092000130b010810456070a01e011920f00303818006a405010403043c0001c0300f0b00700e402c66614000000b0401d0b980351b8407100061021400c0014142d60100c60340c030740031440102c1440841c10358080d588507a03800031060b200220340036070440042e00040a0030f80e24003592a943d10039099440d52144928004580100809038103944110010b001108606101007a143e0756100460f02c1c2c54103035842540096010001448420750494041c2d009040d810000d11141c1032541d03031258107204601c503d50350004800400342c21501c480d041300494a03001130003191540b181d170b0303c0500b180d4900c2500300d01c07951901d11040890385026040318140c0b034041c2c0c000d5007458503ea841a10300d43c80050203071042d10505945100040a4401940c0030b42610358001c80d036103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 1508856 1250 1507606 1507609
    0x405010807030308090a050304050d05070302040207030806040b0102011104090f06050a080106051002030306031e01090506010806010f06050c0d0305090a060207060207120224070905060706020c0c090103110f01050f03070c02 98
    0x20074014007085d565070030a030304e9000070070000003d64058071800c842c9205241150b1600b07610749411a40000c0d0041e00100da102d0a00d6003141040d8402d813002d0b0703402d010150300382d03004908031106044440c0d0309400511040c045c030515517014030007100c222400080c5907a15800010162405036200d2034950707440724801d00c074a0400100031800001e041c0015800d50030124006902c7d401a050101d010084440d005440f07000250031818006070400240d41d4556155100b0981341c40c024080c9502d00740c0340d04400901c0504c075100f00c42071018100007900c804410240b044020b0038020b4603052041c412607a2190204480d840200203040c8650030040c0c0d21092407130007030034000c1c0350300c00070003990040030803205100180400641442c2200042d6001a030320040107461580107500220741001d00858103e003040030580c001d181311708000f400c0702d8140b0614010040b000c002408024494034504287d0300d000d081029403446403c01c1410070b5400c04102c20302281c001d030000c49170000000e20440038101907 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 1510106 1250 1508856 1508867
    0x30a060b0f0403020904080d020304030306050307060c03081f0b040602030d150806041101030e0109050304090e030901050a0f0302070b0c090a140d03050c0a05030f0a0305010e060d060209030106030204050108070303 94
    0x900c04a00c03000d007854400c00200ca514007a82c44045d0203141c5c248000b40c01c0207002400c40d00c03c644007500441d120706003414020010060b90180d14088d104046000c600f8500031601841070503419a2820400d50b1080070911104450320300265001315031010101c2c0b4010104003400140445900540d01d4031110304a400c00c0d58213242d2401e0031654600b078140714005003c1040340d4040d4000705c0b203c0354601a0070040380180310003580101e040d460144904100f06010008008881c0346210038066104140150b5440f0f2281240c0a40828400c000301e40803203000c0d004058020310941001030504540340c60f203980c9040308403416070742c060b80003070064102c1c9410003c0700003401da5505844002d030320140114400094405014086c01300120311100c14400801160840962100a0303070303225007c00d8401e1590f50401c00000b404139040000110f4500070080025107e481c005140100c02d03015a11014025404112465055500c81318044003688850058034001c2c1038030740050410600e5810020306 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 1511356 1250 1510106 1510109
    0x10603120815010c060207020d020301020a030b120705090117030d020d0c02010e06040804060507050c0a09020702010206130503030105090415050405100f0207020604140102030c0109050102070201080105010e03071401020304050d08030a06 104
    0x803041c042d82d000b04030b140d03445110070031350300c1d40100016903949441c00060450a00384500039411b42c000140b8212050345600056407102050b01c0c102c50040c0799094268407070300075004443d00040010010000f50386424815860880da400540f031600031090313130b400b042c2d91280a4401203240c80340940840a5824411f0000480c400d001a01841c107040c0e4401c1001d04c501d119401c2003010210301e00f814000107200d41c03041d0117402013100007200c4d45c0700b10000c0a90840c07101a070160103a02d0000e190310010355034070700c0d009500c034014602e140e080400b08012010050000d550601811003a0005240c0601c2200c2c09140200c0041588801200318441500d04105805124a00501031000103071112429101070302c1000c05800446a07107840100d00e14028482004450741c204480c1c002404810f5004240160007030b03898000c181e0725140152842d80f020080d50b80c042c0e000d0b15041155400c911224071110a0520540e40b4050f503460028550013014039040e0b403810000018414a5800c610601c0c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 1512606 1250 1511356 1511371
    0x13050601030b10050613050103020a050c06011805130b0f04060204030203010e0604050106060e1507020607150603020a0b030903030403030507030e150109050610020307110109030602070809010e030c03032205030106031208 97
    0x14030b0550040322946c1072003000d11983c0c0c18103401288078442d4900901c1660345410b0100c080307401c10b60351200c3d00032051090901d5500364914000c0482d500f1100251040c20203904941c06080c9611110005468140001c1041d104140e003072001000580d400e0148045060804004042c1c40c200f6060503821241c2541c00307482070115226000e559174a4060b0a420000e181e03442c01610b412850011403168410800010f00424131611030b194581a558008003d8a0003520b618500c2d40c1c541a050002c0e1200b903c110580342e106100090010b41b00f90402c0303501140500e0f000c90080460318a051a101100c0d0740e0303586e298128001409503003254400c140d800081101c982903000090035000c3d40f40c0c0b1a045000e0426140300315102d00ca40d00800c0007600559201034110769440f400e00700f24546800090034a40012401c841081841c5000a8480c1c89040014051413611042944003942d00d1038074203e50261121402000031141e6080c0b1600005600540002510500c910002860144020b2402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 1513856 1250 1512606 1512619
    0x30402090a0614060f0d050106050c0c010302030f0105040504050a0503030106030b011106060105090105030703140115020115050604120204060801020309010902010906020601031a07020a170a0e0105040b07030813050601030b1005 100
    0xc000341c10f040c1009000012040d03e81c0d40d56115901002001c9201c0d050140a00d6410540001103090348680100b00c2914144159294001c0c010011000c0c0c0c40140c94240ca0a82d00750010700440c034042d1b000366002031085084a1b0020781c6139851505580090b40540080389d501c074580d1105507000343c000c19240300035901501c514502100003900300d0148112550407c84040000341d01329009500c801400790030030b032004c2c600d913944000c502d4125140030000401542450b00e0314031002800719842c010f83c2c01c001c11103401c260501600601c00440c503035069030300c103449010004003010300b1310040d4090314a400010421403511b00000d0000c03102c692252085502030401000451292a604564402c81021001c0e05071a120412458001e00710000351a20130f0320300f91003000c00c0f0810300078440c2c4400c0b5125a1801408070005440d1405244107025880404025110001c0c0c4249000d40e031108900300703000c0c0302c248141c90704c40c5448000d0300100c50303080c0d5020511850300c050b52a190010081100c91 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 1515106 1250 1513856 1513859
    0xe0a0f050a12020a0914040215030709060f030f0203041104050603060f06010302070f0203030c010501060f05040f0306020705030412110102010f0915090206090d03080f0112020a0303120908040605030402090a06 92
    0x800c0c1c00701441d12500100c40c2a4080340030455a0303422a80300280f140d403030140441c12070b01a42c0380c22904103540c01c82c070504100b01a5000c00c40d2250550748102e40a4903040005841d100e002d0b0b5008070740182802c209a5203803034018100c60240701031801a070040b801c03500c0303c900d6203052204459010f00a18480e0f4002c1d410042880b0601d208254010710a00e00541c03a106a450314040581d80050020740c94000232a13040504841540042e0480320150f40754811500e031410300b42d03043c2c4101c0c010302c440f2036004041070000c07600c1d98009154003480307542180d10305952441080d4800f00400022641d5001c8407940781703010f41c1d0902071042802e098980802c601c0b04207a440b22a0301c0c0c104017510703003529150400385096544034416295036031702c00b9100c900101c01c94607005220032001c642c0000308038411400418000050303034145510941c050300041d04141592130a1f107507044450b2840044c20303100c584a0740061015400f40c0010700302920307a1626810a441002107012006145440242c50310744c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 1516356 1250 1515106 1515109
    0x1504060c02010b0303070303150509010806070905010f020c010c05030d06060504060905030105070903021311030901020409110405030303010308030a0e0a030908060f100b090415030b0709060f02100506040b100e0a0f05 95
    0xb181c081650508001500c07040a5a1182c08034175240d10081d4042f29590001501e0304010444512400d1590703110050b081d21240156259608850070070010307800044240000d500030118015007030302070001c4030309103010001010140c81141c0c1117000081c41c007180800130960040c641c08082c0908600903c224540030340010700c244d80900c0b0203445121303c04000284104e0950255100314a4445595640d01d842c0c81d0a6010394404c1c8240240720385800000c48071007a0f108103032810340314020007851a6910b9911010510303000a04582c0140d03507a100c419030b0000d400c0104e886c0030342c402e07250751542514042c101810710000a00d41c1502020b4030040001162f40d00c403100c029a018400141d4a4aa0b8940418000c28200c0454449075507001c90100900440c3c036100ca100d103681d641c170684030b2a00d48004403003144404429202591258100580f03c03190780e04456406070024000198000d00b10002550010451440e20049070400380c40550f0b50601c1820784d03001d494009401c210030703841c110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 1517606 1250 1516356 1516363
    0x10809010204060804060b0103020d0501061d04090506040305070c0b03070903060b0607020a05090901110301140301060602120a08150607060c020705011704020d0c0803030901020306030c0108010312080907081504060c02010b03 99
    0x10001000705d47e0314850020180e00a9069510403c42c000c402c00066851300c2000d0481c1c0d00300810724078580014006203501d80703040d025003001c45601c14050a051785840d0707401d40301078100700c40c215944020100082104503011024521070030075a81d6400584c1e1071410103508481000c12482d0081c10104040405a210070602c041224415668032201e40e80386444140100a0301c3c40100c440c40c4000000158920820700346455018200d0007040401e40c0c8400990355480400c4030728418030803c1c08013841c2070b405502c10950201d03e07081e1501409401400040146d404220103c1d98107944400f111822a070400c102405050b080c203211000154503031545401d100000c000a00c590b0010041c031040155500d02c150090410004903612810b003105428043c0d0411141a4040e00c682102e5036100c0d8460400b150480303030015980c034802501e01008488403000200b007221184500320340024142800c2240118410307009245804c6420700e45080340903a09883c03141d004581c1000c0720b405142e078010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 1518856 1250 1517606 1517611
    0xf040506041209050a030c0305010b010806011b1104020304050109060c080702070b16020a08030408010f02070c1202041506020c0306010902031b03040515010303030212060a030309060c0f02120304050108090102040608 95
    0x2007402c1c07070700c2d0095044881c003950b50441e41e08681d90f21400820009040081025240305400a00080c0c0001c801120710040848001d40024440c2e05444603840c604444120003130300034080704905242c1080490b05036401a0342c21901695a1960744080c0005032088507003030074080c42d0802650074083d6009645540302e024507090b4100018601c0d041801c0d0030101240176034003a040f0b0300c42a0746d0740c501e07540b241c1191140c02c2c130350350910345000e80c900321a10880f145181c0c40300b400102c640c18441402005c92130040c1c100d80042c2c0d1110302d0315529526a588400130201a401081c0b00c2403a0300915081c03000c1a84480038550040c001e01c90f02d203040c826920741d80c02c0c0b420180c076100c0e80c2d2814007515104100d6102c8041041d840004014164560000c010107000341400c0d0340b090b10b4107414072030024094071010300000d910710010301090340b08200c8404c82a001b000e0740c051407041600014114810760a454007546c1c40003400300240e580149e259580100d0490007141018601000906443d400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 1520106 1250 1518856 1518863
    0x304050f070305060c0c071d01031208060d0303050406140c090a05040902090103060903050d060605030f06010c020109180204030501020d0e0f0a0b0403050304080c06100302030c03010b0117061f02010b01080f04050604 95
    0x1c12101d085107400c01c0140c7c01170401d1030907028080640020040171001c01c0c00255a640349403180070201ea4040c1103481c0c0991005450f280c485000c0c3d440840003000094021107c181e2255020385608000180d5940034030b440c50741595680a1420800003c040d06030b100c3e070b004508282800c40075030303a03040704070b4112900244007040741c0c011884d00b241c0d00d00c6020440082c2a01e061004243c0641c0300018612412200c032080516449079001940d4050407038400900081700450140060140700b6021000d180380708901600b1705480b540c442d42683c01c07455110b600280e0329228500000001c2001d540c41c00000005410303041c8d680e0b00c0c0c10881100007030000d4140180040803a040001010480c0d0301c4034a03070825250303079003811454804108424801079100740304866003480c003481c061003070221080050f140c007540003040702403101441c0c6000b80081c2e1b10017610040e51b03804181010700e4041620a503400001e02c00f5405001400c0010080c11594810b05090208030002c5c2000a101d50040e40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 1521356 1250 1520106 1520131
    0x629030a050c070b040303060e0601050405031e0708070b0903060106030b03060c0c0a08040e0f0a0c09060c020402070203010e0709050c040f0302010509030109050d020a03080a0b01050301051302120c0304050f07030506 95
    0x50782c2c0340307200061088030700003010740710b1100402062582c154840c00c00d40301c426080d440c09488130740044519020b6401941d6058100c007048010a00000c5020321030b00600c9410b031200150346004d400d05155465000051116002940c2605480d09000e00340c0034041c1d5003020000000d541000c2603035980c0060180c90070842c00196070070202c034200408002254080c1c807555445403501055600c062040c0c070b58a1404240002041c01d00c1c2c40b5003d42c000d488110fa5400410314904030085514141007c002c2c2d820903800c000080150b1403e000b102192002c40300140310851411109100f1140010300c2c50001c3c400c240002c0c0140d1101c184803400b140d40910340103480c1c1c070f11600060300600c000c04009040d8810003541c41d48158004c03c1c05025280603484040480d59074a50a9003a513a94440740381c0000c070100018005c07890300f5048072103031b507180b03202c01424140d04881c410040308090343c116070003090100c00c0100300b01c01001401c02440d250405816032902c0c1d03949460b40e413440540707015543c02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 1522606 1250 1521356 1521361
    0x105090a120306050d060c030c020a0201050a0e0609030102070605220218070e030d08070f020303010e0105090405120c06040c05031603060506030309041b02010b030703030207030209040819030629030a05 89
    0x703101e40c01190182000912a41002c6420301c0d004005051f042603010111f41403184c1c2141c02c03800890340601c03190301078441c50319001c2a10011204142d2400d01968404418094420b15031003d00c05003602278402d0800040a0030400e1340040341c000740d02520070346100d20301d02e85401619001050760313500d016900c002c075503034030346100540c2d032104040c0c045d58051082c2115a58841d512071445409494280c80c2c1d00102c1c16070000c22601c0b03100074024020310440070300041081d07060031790520b6801801481558951180d840e15424168440000c46d10103600c000d090000340030f01590903400600c011001071070448207900030f203150351009220107011140d5036070002e81541c03024012900d28180040c410800300c4a24448000310303c51110800340150b29116800410f400d00007010b0040e1303601038000700f4036a4910f0303082040425008000311144c110a004c100c05074000c003001007000b426681c80100314181010000c00c090006150101d44c0001c10b09a0070301900c00c00c0b03085070b1308002480c10101301c65 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 1523856 1250 1522606 1522643
    0x10b0d0f06120303060311060f030f040501090804030b06010206060402030702061305010605060706020409060503060702060a0e0715080406050705030105010504031b030b040b09121c020d06050901120308090105090a 94
    0x40c030003644600c104850700a09001015815807098041c6c903c0f03482c407200030059400500581e8094003025061500040001c80c4203a50340078403003684248103000205070300d411a502c0c0c016640182d0700c100e8020301c081040c840c496806200c09503100300191000c6081d0b00d0190f400941d22040581501c2e22085115104002d120f02074010310054940a02059551040351502c00025406442050714007442d0560215451402141030f5010b01c015900400c0702c1d17200c40c43e0135401010800781a40309031003000d0000503614130701d040d800061000f5440d0038440f850181000e0064407002003500c01044802c00041c0036030780e042829075095917008511504003840c000030340003695110390806068181c1c04010041040a071051684c4035484400c00e840d282d101c0ca070b0503030043d4041c00310380c4641c1a114041d00b10b0585019406402070000031480441d055903100c002c6840d003c420713080001d1850104481006050700701c3e08241d000039420000300700034075001210350b840d0204440001d000d0a01150007101d00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 1525106 1250 1523856 1523861
    0x30c050705030d0203040503010510120b100e0a020301050108060d03021c020102040315020301080d08010b0702060c0a020a08010b03010b0108010506090d03050c0303090312011202010903020609010201061205030a0201060806010b0d0f 102
    0x505000b808a420b02868010041d40c1d075000780c844c0358425802c01000642058034150703004103c50514040320f005860541c1c507418401001006445071103520000090886212a48540030380b90f9144011b940c1e5050000042c01c0c00001000d039800341018942000c0083d50004281d59090440e080514440c0d8080800303e0191160740c1c0098602032414000116045442d4015412142c3c1c800071298983e070700300c0d41a2194502480b8150000905000d0380c005410300a0090460110351815550340508540c000f07401e488090b04080f413181e42d15400c04180741000d103e0510311401c02d00340300709607601d8600010713450f124040700c060042c045240310404040c0a00d096520080c00c2c541a40d40fa8074107440d4555076a084400850340145243c0e00000b08103030010a4503003a5601a5200401c5031708580902c002e0364070081e240d504641d40e0b2800000c0c2c2c80d0300c51104811040c4100040c581d150150500242941c1d5550000381c81034010b0310040010400e0342c000c544141c03019140210300e40d403407080170100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 1526356 1250 1525106 1525109
    0x207060501090c0905010212120606090d030c02010801081b0609010201020c061602070b03061003090809030304030309050f01020c0112051b03040803180106150503040501110c030309070501051204030c0507 90
    0x1964104400440c405410350040c1001d11502d41c0d0380030401d940c0340c0c012030751143c1414850f0342c030300410020825007060700810558014405040246003100d407001041075203460000a90010750f24114000c215a40070018600510800006050f010041030281091800e0340c4c1c0780754801c50b0700040c1e0801c282d00070740560321110400c0041ea41c540c0741c07084481c032501e1503100c8920018002d0a4000c070b00010300d4802d6070f00855015185411029007448250020300001070181c2e43c1d000148080005a6000c10041c805180300b6503070226918235280900010002407041107056400180e80c3c41484c4e6804031403132282a0029601181c10349440c0d404060020260440c404208000020001031000100007940150039200f2118019080c1d0740b401400c0350603500036841111954144000c05910600c05990464010f00000a852070158450300042d401205440d086400100400841d50828820b4100420082c2400c1d171500713200703822140d5407850041c0020144030254804405200b0704114600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 1527606 1250 1526356 1526363
    0x70501180803040803070501050603010c14071b090b011101060501080c16080403080703020606010c020907030903090b16020a12031209031e031b0e03060103060507050d020a081b090904060507030207 87
    0x1d03a65031311542c6507a10b980c48101d01f61099801c0c00c0200b0000c1c281417040c8186054607076902d04100f0590b8040c3c240652001c801600c9400c0290146030000c51001907010042100344030001e40c00114200150001090040d10b501a900d042010840d0b81d8002c0181a80b2821314070700076542d1050300191180000c90f0300005042d004d0086004030410041c0c0d001040410b000350201c500550710403004485614941e10001e400640900c00f2a0703019020781c22240102d4803074208003000c1522015a001c082c4c020716110605251040013010650403c0100c203400f6004460343c591401199860180003a40c03618504d54007240d075500000d0500d840340004036801e69508010a07002105054024050641c070180c03004c19124600c0000042e030b02850541d041c12401030082c04240c1e1035034131640002c0000030451410700600b04603822401410b0302c010030302c0a04640f00c500103400e2601500c03034800c00c0009040c00c250810408802a6039406407144c0d403260380940c011030650384116044010740178412004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 1528856 1250 1527606 1527613
    0x1401140d06030b04060605040513080a050904090503030402040c1103041e03020603070306052106040b1003050304030c0608070801060c0f0615030602070203010b04050f0103030e01090e0405010b040c030209030705011808 96
    0x3208003c4110041030255006040500a542d01c0d2400c00c4110348041e100100d04c054269064000910000050705070940141000741c1070070412408a810380340c0340399049445030000000c100461629101d40c1c1042c107024a010003850b600c80300324543d64400c030f0007505851111600c9403a4020800c5d06802d002d10390140c040c9840307040c2850040c02510f000e00420740318859030589158003814460004014a00e218010309036522162690914054085c0240340700d060390005c040041081000100002e40c80b4018906016142940080c040040504800d0400c08000c00412189030b2105070b860b5100c2c0c011411500480c1d080c036008001f815841d040b09142c40c5000c00000078412268042c00c14540250000d000302000d20003040201c0740221041ea20003030f100f00c010b0010a01c0340e5021f0b41540c074103042c4a0500341e10b403d0468031b00c100440d000c413aa40e4503124a8003c3d81801e01811030802000c0c1004e40c00c0240c4140000d842d500e007801643e04001c2c00300c00303402c44402d10803002d800a19010f0242c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 1530106 1250 1528856 1528859
    0x3060c02030307020111090f0603040807080403050d020601090c050307080a14090c0f0405040209041202010905010f06050f0306040201020304060f090f030302070305150112020f0d0204050108060601090503071401140d06 96
    0x60340701d400440b10040035503e0100c05007103444022007111100100245400da0f116405010820b031a00090f20540d081301c0b0903c60170000138000c1e07004002941c00ba000400008034103410003840c08030140c000301c002904007030104100b50380000603250070400a081212441d80e610044070010b2940784000000d5072a080d040c00304078900480e02110b1203174141c0d07a402c0c115a8035030900058482c00e0b180290801c0d00400000d003c100d0b001004071a04900b48008034000c00701d603c0b500d0035218141d4521429a80d5081c0402c00740c501543c24206002056020700458501600041c0d00c0c4e00503446548244011080342d000384500c51443c0c2005000640d0809442a4803802d0080d900c091038002101c5038490310300f0811402c1d260901d80750403260a501d061110891507400d121500348203a4050782c00511045922005079114019540a0025440103010a19007400010310000c040c0c0e1007180250400c8500303208090500e549c41c0b054000a00300181c10a0f000c2c010f000240c4a10300f55419010301d040e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 1531356 1250 1530106 1530131
    0xb220303050a02010e03090d1209090c0509090901050f0a02031b0705030c0114010305030405010c06061d0402030606060a08040605060a05030601080102031b181e0307080109061802010f0c08040306 86
    0x81c2c40c005442d41c1c0200424a08011019500d109a207840b0303500c040b05008440000d1000201080c0145032031900c00c0704e1607501ca04d564140c600005021001c1540405e034a032b0182400e80c0101e50010703154000b07109a04000300c0a88002c24083c04003064190000006808d0003c0048140703c0800c607490380559442d0035040c016141d1700450034030071195007002c1c43c0c85590380400070b005050740c2c2c01c2030140d4030740313440d02c2c00644442800460803503c503521002c000504416080905103100300c06040c5007030600e008e00c101402c00e00014015440744806011a01500382c1c00321509a1055016000203083e844101c0000c4c2e040029502132139152040000104074004103401a41c06403c0d2400c40c1c001840c840c41007034201d806102000c1c07d0a00c00c0c002680c1e15464900070701e084000c0b80000c81c00000804201107424a0750b030f40c014284983d1100840c07002c00036144030301d5a00c0c00200c8013072984400c49900003441d6040a0f071241003048044c2c0c100505200c001d9003110003d641c0700c42c0820005503000c0303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 1532606 1250 1531356 1531367
    0x30308040506010e0412120b12150603010c0c06020f040306180506090604030507060213030204020406030227061207020f0102070c14040606080604020c0102040e0c0306190605040b220303 82
    0x100c04403040d01070302c0300008040c0366903203c0c07500403903110892110a00ba418800c4400d0a055a1118910340c5c070b90b100201071751030705980080e081e07180002818a1046d000701450302c42102420b0903019a2421003070540c0305030302a4198031520b601010140e0750341c1f01c0076614141030243c0c2e08040e0031070745001c005550070072050300c41c0da10961082d010740c1e500d591160394503600c0d147d00310fa002d03022520402c44a4005522940140026003420346000500350716500400c007241c02680241d4007280d0300180b83d41c019103440c507156444001706069440c083e02c482c00400d0308c90080071041c250150002d4040340d1001c3c001d20040c001c184141c002191295801e00b051a50f130300345441075141110b2071130040da1650600303005020548480d600c95a80a403a29020b02000f9400003030b61030700035542030002050240888212600805c032002d4001c0e101e0030311504001c44090415042d0690b1501c600007004513070f030054181c40c100c0b4002c03d4499182d40d1500c01c4625a1030a11412008260454a02108060300030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 1533856 1250 1532606 1532611
    0x3010902030f0c040501021906090b0405070807050a03050d0c0305070803090102070201030c0302091008090307051609050601110c010509010309150615020a030c02060702061308030c0c061204020904060b0604030308 94
    0x4120b6030103143c5403000c05034030030b116034040d2600603000701084420419980440b41d080c00d12515000408401c02d4581d4118128280c50071501908440e400300503040742080008094442141d0492009180d9900c055580741003151002c184070100c00c001080c10300400c2914055500155815a203242c03030304209000350b000503000ca0100340791a00500d034180c4a44283c9903000e070080e0400034200c00c1e0000549900300b005080b000988000c004890028100388206d046080c2e080d240c16400c42d04200301d04084c1c8400600b12030401201c82e0042c0c130010340008112584000071f0a00b030340c0d118071200048024044010010b80404061003190303001d990694003da04550f03008140c0c0703820200d0500c08076151289000d0240000f40c0c2c2a031040007502d8804c0040003007034801400185005c480c525242254480c40e4040320051304082900300ca810020f00000703a10303140072148540b51600c5004809000240540064080d034025030024003008419400f6540c8208018087ea032120340c0c038500102000000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 1535106 1250 1533856 1533871
    0xa03200d08070204050c03010e0f0907050301020d050a060806040503071101021006061e03020c0c0405060f100207080d020114070c0c0902031021020102030909090102040306090b04020103050f0115030903050f0301090203 96
    0x41c00c0c0007900e414003a1b01928140e808403104d20740180c48549100d42810f0f8054441b00309406101d4000600e69000d20041c07032404000d040c0400d0900c0c01e1100305045550035444081c25801c0300041100041000c001c88030019800304100301c030301a2210040f131034101050180700c41c0c01d103001e8000c0b0307000e0f4000e40c420068051215840200d0008504124180e00034404c512a05034890f401036507681c54035800481d4003001c06840810b414410381d0000d0301c080c5074040401c02680100c001440f102c030702840b138001459464002401040d5040205401401001704820204090a003100c010010382d520200020b2035101c600791746904002c00d0f0301054100c103200d0382342003900c20b015540500c210b00340c47c049101d07016000345050110343c100744446040000d140903510f550030070020000817054404c0b03080039401242c45556501c7d0a2001400326000a80308a8003070508030b004000c0100c01ca8025102d440c2c0d2807402180c214068030302981d05009491400c196058084008580e03240c40d075000c0c520400e01c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 1536356 1250 1535106 1535111
    0xe1306080c031c030903030f050a020703090806070507030e01050705010c0801050a0503070f06030207030c05060702030307030b010e090103110406030803090a02040c050406020304030618060207050105090606030106050a03200d08070204 103
    0x494020075a840440c001c054544100f802c2c403844546000b0340c0500e00d040d0007403c000c0742d003c95080c4144216003040b10300c103c4046e800f04e10801816030044103c0e0203000da40d4014056407c1081002e0718601804a0003010064802460320169124105072151254000e00a02a5001e074a101500082c42405058011035840030002035615000a91a0880d056801c2c00010182421412070295100c0c0400703605203e03005041c44001442000381e640b0a4981d50301464690074100401010b076500307051003504003d844105856030380d5030707020491304680e40050f042280101d20350105004d000c00c1d0b4000340420401104002c8040b501280340251148201c0c0c082044102091b002d41b41402a8022130b00140d1042c081440042c916a0121b40000015440c50421040c90b503580c0c0b050f40c0c069141240c1d16519001400340071401001f009403c004210000e001e13880c20080821f129603018400900000e0518807461804030780500d0020369400c0c051f0001620f4005803d008015a0054104a0040380f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 1537606 1250 1536356 1536373
    0x50a09020907170115020c0a0608010603050601030902060a120b1003090c0803040305030315130507030207030305010e011a0702041508060108061609120201020705030105070306030203010e030403030f050a0e130608 94
    0x3e2082103020f07440e0507074010100c026402e05a401c610794040000c50819407155200c5880281e4134580c079080200a070703954010705981081c0c0010291540034010505040c201056800141c4d944800d0300d503021528940b644207504140001e6003d0201c140074241c100701d5403040000b040364580c0004080f0341c094042e002440344d441d0b60701c980e02d100e507210240058009002049540c5884000d50140180003002c04c240c0c0d42a80404404541058620601103903000418400300f40d00360103010f00600030b0307451400b01585401200300e580320b41174405031000b45000409030115510741c2c1c8012032100c4030610fa5074032261280c132010740d5030000380200b031002d1052100040440030381460741a007070007075070fa216447c0d503141001010a0031107025003203040d400796a001046e01d4030240f00b118403e0720035a5020a03100d2441c011305003103a06907400d00000c1c1e0001c0209002003508019074652244042c40c2c00c2d6130311a054401111214188480103070b1081010a5003441000305411003000e50303441105076000c0c0c0c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 1538856 1250 1537606 1537621
    0x60b0408070e06010f0f020f060f160c0201050301050105070213060602010509060a060503070302121005090607030e0307050606061c0504030201020901090501020606010e01030c021204030807030e030303010e0a0b040609050a090209 101
    0x8221252800240000c484c4c20301c1030303c46e8404038040c1a06c3e0048460034502600050300740305007254450085403080003001000035482010241c1c41030345050882c4048180c0d00024078510050241506129002850200310748441c200c544a495408100b0026680c880d0030080c003a00e8280e89002180c0b25482c081740b183c181502c5840104e800040c020000145590f0a202c080d2011000d405480c5c0101d00110111641e140200d40c42012808058150382c50101e60240c02c03034095030070304032540d84103022a07400a0400154660088400c5030003549440e88a100c44408100c0036840d403018609003401c0c88200341c3c05402074040341c0e001741c80341c002042d01c500049907108011150709000030003c10070741400c0c0d400b03a441040440034a01c1542c070104102a81d1a550364040e038000c80341880002070790b1060543c49000d04c046280210302a500c2e40d450099143d4402002401d41764086980381c14184036503699901c04d06c01005102001d1049103009910b000040440b8079040e4052544d030400180311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 1540106 1250 1538856 1538879
    0x6020105100b04031104020903030304050105090d020d020705060d0b030a050d0305010e06090402040b030f070303050d15060206011703040f060809060a0b01020d05030603160b0c0f0a020a090b030a06060b040807 92
    0x181c0740000a20b50a0910716281c08000c83d401d1303c0100c0c4c00c281e081001680c90389052000b1886580940c2c00030030036007054051140340003000340f0700710119040311010050340c0d903000c40d40c0811914100c5940e915644034401c0c4000410403d116948d041c4509180707107081000110b416480703100c443c0c0b41040303180e0740c0e03040c400d02c910300c12140c142d40101c02c1000180149441c0d40a02c4141d00c01400b2140007000250f540341c40c0802640050300407400103c3c101c0d000311070900881c254a80c405101c5103220f442c0960103581e509040c00b500c10000300115100b5001c00c41041910014800042d0391202e69a5522010f010080181d503407a0071802107030001400140301e0b005910f107900c01a802410300c01d2800b0004c41c1d4a401c00340c11194980035072000500d0301c49141c0b44400190644113222561600c5500b2054642075140041141c2031300911007010141c0d42e08201107048501400c4042803082106000030300340b800c524801040c031440e0443c04241e05403500050020b60b06074904940c2c0710b0b9258520517a9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 1541356 1250 1540106 1540109
    0x20702010503040807030306030b15090a0e0c011b061503030e010201060b0d0b030102040504050405030901020f0114010501050304060b040501080f0708011509020c030c0a120f08060a140307030602070803010602010510 95
    0x2081c010004100050007890003080038901a180001d1174603140d55415032001020784200e003000d061800300b500baa01e400d00c4240d07000840004100070303e200c0c40c0c01481d140e09011000e141405020304114980d6020f200510001941c0003400300844052540c041c1c1c441d402c0c5e404182e000840d150a692084e5005100d41380a40703005102450401ea0f014415001500700480c0f440c0d0155024400010b203510b4034090280124031542c0590b484040d1907000905e07000d20355611410603810815076182011202c14042e05483c420701c0d0159403603940d03080c040007804000a40640103494200001561800070846c2c80121074503100350f401c110340d03c0c1c24060036900000380251088010650030002c6440f1030f4000c0000104610580c1e0425154100313071814000440c1c82540c0c0d010001c0e00f0b044c0011307800000400480c40c0e5082c121028201100494001c2c54180944c210054178003188800036982080094001c60344103c00355614405858200e40641007882000301540c240800300340c58030f0000783d0313190 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 1542606 1250 1541356 1541359
    0xc06010e1f0504050a090501020301030804030b09061303080601200c040609020c03041503060e0106030e0105010b04060c03080405010b0d03021501050603040203150c040302040504060b100305150d05030d090b011404020702 97
    0x1c22071824541088018500036011403049a62100060005503081c0041c0d402103024102e0709841d5441c5003031602c0001c034000c25030101d40d0030a10411040c1c240c40d80d034440500350585000c000c50350301c0303000503100b03042e01c031034051511100d903c2e11026070280051041081c4030b0a8501b4440d82c0da035a0380ea40168001c920001c0703d0b82c0c10510060003a11510402d0b007603142c4061501140303040d41c45405032840344c0203800510000f9101d180b84480103409005050041400c00c00c11440c15140c8980240750000c084001400c110040000c5000d0000940000350000c0c0c4c01080318403514164640690344252010300e070984d10ba9244000241031a080302600d01c656005005070401900004031000c0c00c02c401008508154001d00010016031214031560748218410040003480e0094807082000210b0254425010117091008104226540030313070304180c1c00000d4641c5002ca11a62400034158082d000709510306619000311030083c400e1031000709040703c03100e200541030003203480280400d920403a074000c1e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 1543856 1250 1542606 1542661
    0x9060a12020301090812040c0b13050103150f08030c0105060d0b06060c01110a0905090604060f0b0a03061203080402090702060702070303050309100c030605040f0509062a0c06010e 79
    0x3000104010500905818030080000a1011280d510603100d5001a141d40d8194803400c42040100642e90007288003500c040140c1d0750400c22a0070320455007684134050541059140c0d10000454440000030b00c01400808190112290311405050780d25040307082ca028007903003440041006030500b451000b07121900321500c040550784000c2446281e0340008a01d6031690343e60605d403840c9002e0000036010417903165032110442031900301001445c11010f00310520891501400308008000000c9100440b2000f50704641c8402c898081074001301a035900c40a2003a807581001b034205540146541d03c198400c4504c0403040e15020700480c1c1c2c48008941c01400350303024007401c2c00424020300c061341e0301c00c01031030403a43c0c08918580c4007419a02d50201010100340c564900b84298542401021620b8001003030030091464440500ea0b52000098802c100c5903034605458002014000e40c18038607190100c004035aa0100c0041041c0e551030240b01d00c410140744030303011030951601c6a0040765030840da00105d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 1545106 1250 1543856 1543859
    0x30703020c0304080106060503070f0806030a060b030709151e120f0204090519050d02030901020703020f040207080c0a03080c032a0405040c0302040e0105030f030304060903030902090109051509060a 87
    0x640096000040c4003515210600001038001c909001b0b400251030141c0c0c500e078490401c26000b0300000080401042484406020440680c80c0010042c0c50b0981000c1e021510008490111b400e1019581010014900f4504a81524940c02503400d0803940f40c07004c2600c981007046500d132180c108034041c41c201070300c400e0010004119000360b0051003030300007440064800d801e40c2d640c9161030045418010080003500006051010500c01c5511540c2a40042c52030141000b000035291070041c0002449686502401d00c1d103034982d581030b103040903800380c200d44d9242d40d81240135640b400070030400c0300000e12030b03c0003a112800350802c0e00c3c001c0c050140e0400f01c88095501c03070b8103400c0e0f4800c02050156400d020000b055611402816841051910010382c0c96060011000107014143c008074069801042d0301e03c140100081101c8e0f020307820020014035001c40b07107411401340404c0c0c0c6007c0c1d440496000007144030045079004c41d0144010709441244021400180301402c401242c01c6907010b07105410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 1546356 1250 1545106 1545121
    0x902030c0d02030901050703050105010306051005030a020c0604080c0f07030c05100201140705040e01050a030209041401110703030b010f030603050304050d02030a06060801050f01090203040507090c0509030601030813050d020603 100
    0x145401240c4031103114205036503898110100e0b00111041d040a1b07465100348241c030750300340c455117000d0300d000e28060003900e0611011841018920b82e00c4030030420000001541500316506640c1300900080503117455041500341403007960405461030741140181c004c600d64084000071150100c0350301205101d651880c1c001002003003003210b4044000d6548910b140001d64010700d1050b071007040c0a449144e100d504002c5e09140c03101050f044203004030440241400942d444081c05940030b80e00811201c00110000070150142005205c070000a890200703101d0101501a0081d41081c4401e0361120380002c141c4108406079141d034800a40250010401071005041003590610b0b224006422101981c1e0380da56500121003071640441b64695440c020300c15801c00600715503004044050b400c0d41541050344480b40c40703103180c1c1300703204147d41d0314000052058081c900703580800c0002020703150319607500c0c14000c90316481a5070345285410719800c0420245094090019101c1e00505942e0031035843e0030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 1547606 1250 1546356 1546361
    0x81303020109050a030801090b0103090206030402060903120424030203060d03030203070215010e040c15020706030506010e060a02010b03060c070c090b010e0a06050405030c06270105130b0403050f0a0203030409 92
    0x44164115500d0b0306512011510030041da5940510075038030701030158580b06141d01200e08107001141014200f040e888090b0303840c0c030252600710342c0480e2283d54404004000a01d02401c0405260342c0c42c002240c00508402d221200c86a400c040800001811141c04c000710124841164655440041c24200a01282c0300f070303010b5039006595004844481c1e0401220002d0410240d00c03200e07242002104000410910303079041d10043c0b03845007504503120700d1180b01035142d8100b401401d080550320400a20a60301c1100c1c084140e24001c0c00503035444a000310001c0c080e14008504a0091203580042500c094090080b40d901c1030f00003000c052128103200b100000741000b0b2490904115039402c09200c0c40d80c0e500c030981c00a015a031156683d80385440309140c1014a4516180d01c11403040c4410b91000d014080c0c49096500101c4403c4103d100040059905016218903583c02480c2c4074070114003541200e0040084d02d000d20115901403182960555a07058008802501900280000c004080240c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 1548856 1250 1547606 1547641
    0x2060406050c1b03040503010b03060121030309020d03050c060106050a02100509030904060f06080703020f0d020d11030109060303080903070503040e1302130203010501030e06010b040501050a020c0301180201021203060108 97
    0x42e40c030545402d90210310910303c0f0f4103109952a0642001804200600d0248510f46844100f50003428456151500314001b0307070b034450725070749100d00c001000e2800c045c4070384c0c40803800c02e034018a01e4205240c1410024015082020a22400c1c03061000101d100c50103072003a540040c0080e8000c16044410700a414068200a000308669103c01e100c01015030385c46004501c0a419076515400354140360900040610308007810480c00d0600c10414150f400044408441c1d80b11282407008d41e0381c48900111000500078002000a032100202c00840c1c2d10401d03401410449000365190f00040c0c492142d03864503071092800040865204102c1001146070030b03050a540800b000c5841410700a854020407080e800c1c40c400100103681c0000180915030301403284107031404e08800100f040d5030502694002601c070b02c0c090300d41800804201540c0040c8204100d80c04031030050020f10562400d40910080c0c8440500f0881c0903020380c0e0800c1c9107020f10141138911884050b0368030780c000e440784104241703600080c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 1550106 1250 1548856 1548871
    0x307030b0a0807080109030f05030c070303050c070f050303070f17010311150d060510020a02010801050405060402070206040b0403060b01080f011203031d0708070609050f06030a06080f0303040b0601030603030206040605 96
    0xc041c80040c824005002c0000145400000851140c80c80d140040146061924080a12009009001c00c850314101912001c0d9890b050009154480d07011020260080c110001c0440940c514850304120000c00514082d06907901c4101c844c1e00c401a090700c142c0840048511070021000040000c10100d0200b00b082d00320291000015008058030303d0140d61180480301130242d1241c60801660404216000c08050782d840908461543c640c0002c150300341c10322400d44255140c4000c5046941c856041300e215641c002c041c01d0755681d9614071800380d034200744001e407806442e01402602c1c039402442594820402e00d035031100140e09000320303a0041090006e040c0c04143d076800c2d090080441e02c44441900008010051441901d00300d4040c1ca0310388260800c008100d001242004251a070143d2450703400c5084aa040d240e988001e0513000415003039100841c1885050141000100040300540c080c0d070180d03064084694401c001501615043e00c0b0040050b401000064007041c0b080d488142c00248 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 1551356 1250 1550106 1550119
    0x6020721060e1b0a0e060d03030c02030c0a03090311040209030601030b0408190c0b0a02040f05010309060212040c0311060304030f08060d02030d05090301050906070503040210030605060f070501050601020f030307030b 95
    0x300b1040d01d1070149690104600322400c0c810001440c81d00341388110040450320400c2800380780000c00f0a0b280d11326094018145501c0d01c0020040600a2042c0c0300784c4c40b800b50444407030030141d00b40148007140701d12099641404c0c8090f02070344c0c2d0030709000325564104041d0041942d81d286030794003040e00c80010300079900c404041c07003d454480c82207a818806180b031942c42c000303032041754207103200003550181c074414045204000400c1100c0c10505c0d41021518242000038420781141448406032040100484411a850080104000d4908240d4060703c2c0541d00060005146c3d04c01d01c8490701c0240ca000d004200c0c091407058900b48600c44072548145c004e00243d51140d243d0707000c00d00e49400b0b000b100001c9100800c600341182007d02c41d00e40c0c0300c860100200114100075802030650300c0301a202074020518400360000060298002c0d10041c2000342801c3d64400ba103540c0f45003a5001907100f100d540d401e202c007007050b644c030000d901012170b00d00c40b0146140d41c0300d48a05030700030f141380c3d01c00c56003001c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 1552606 1250 1551356 1551371
    0xc03080403060203040501050702061009110705060103030807020d0504061202070305130b0c011104150f050f03010807050103060501020606031e010905030c010c0305070801060c02010804080d1a01090602072106 92
    0x48006000c0d000840c4201e00258890034581740030b07030a4800013000d150856004501308820b4601c686601001c6401244000940c0745401082e07028920480f40090154402c400c000010150700800d418401e017006d03400e483c0c42600380c03401221140310314420f401c0001e10700e10710010345548a40c010b000d09482401d15901c1d00c46060a0101c0c4141c0300c3d13100c400c0c00c45000c1891682200c080c0140106644010035030361030207090003201582400062a04020003000d8030354405071601030021a40030a8031050311984035a580da030710f143d490007940201d6000a04000c0006541e5000140d25809200c008010780b0941c1c5110170240c11007050010550700300d64885540c2c1c40482d106000800c21101141d0002c5040c0300003090183c10303180060f00207002c002003100100f0030035510060039640641e0901e0800f040c3c0d11241820300150262039038178001d60740340444002044400c2e84d86444880d8003a00d80f80e402a03900c5030141d842d40303550722801247c03a1840c070611702040c134014a03a80c0442d100d81170004625 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 1553856 1250 1552606 1552613
    0xa0f0507021008060102100905030403060203181c0f030207030509010e04020f0403030203030604060b0403020901090203101d070207060905060403020409050f03030106050309070f03020f040203090c060d0c1107080c0603040c03 99
    0x30b0710501010400304016006110065030706010607101c481c1c0404050100000301d503a21640c0340306500c00502881c4e40800401c5a00002e019528204000c202c02c0701d003420b081c00c00700501103840f044e0940210300310714079403c1c06600030700079204960340607250182010440c0005440038400006456072290f8200306219001030300d00090805035000380d00451702d81c60b0440501044031100c0d0009100c900e4103000820050f660701c40f03200d042d00d2a6250141c1c4940740c1503c2e91051141c00c0e080041031b5a00064072250700480290748a01c1200d40da821941900e9a40c4810365180916000383c6403c40000c000900140c00d041e00984c0078544200300721102481042d0401d03056800a80028000540000c14007004420070405d0002270a08806108441859580003030481e03255450071500880c0c001c40013400c04141807106c0158110081c00b0301c1d075551140800e10b0f0041814504400100e00340d124800507030070000402c44203403500c1c3c400802d588466841041142c1e0001401100e1000c44001c010001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 1555106 1250 1553856 1553869
    0x303030a060905060303070c06200709020705060a050708010b09010212130314010b0307050f041e05060a09050402060405011404080102130303030e0a020916020109050f0c12060c0a0f050702 83
    0xc0014030300000381d0074103080d040025601d014101c20300c250300912440001c114800a071004480750f5040590250081e403182c1504000e1900c00a4424004c84034005003120054009100c1d440c424820789906035640321503001180c205482140001e85500b005100061914008041040050040f5900d109003081e1002c1140c0c401200303c0c41b03040107200c040007000b00509035401482030040c002d100000d13000c0c0110fa0340e06d0451103200c1c42101d81030440309560703c407940641c91842c07600c1c0d2104451141940c4501c0980380654002c1e000c3c0403091000500306a07503101c0d107805a80d000305610324192816004545100c00a440c0c1c20042104110000329408244020511450381910605015103103041c05412144100152611900950302e04c10041ea1090040303a8010701c02031103c08040c208640481c010810954002c1c0140b141440380d00d074400000620815514044480c015000500e003012030319500255552021900c041c0114881e0b40e014110103451070300645445400e006494000580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 1556356 1250 1555106 1555111
    0x90a0b010306060501020d0f0206190605030d0f1107050a0b030402010e0306040c0303031407050306010c03030b0409030503060301060902070201020a030e0301090c03080d05011403071e0308040e010e0105010206040c0302010c0201020a02030303 106
    0x100e143c0d80710410070040d6014010402084e03d1030614200c1b15510035006922980000d041e00c80c0c0101d1590b4000030807600390301550103458081c04480040048400c084c010f00082c40e140300110703848000c04842e600703002440704240c40b80541542034051908441400b2508003510403814008002c00694141d101005036601c114094801c4001452441c28046c04482503000815800544c100803c41d05942003170480740c000000f840c000d100d1042c1030800b24000c2455140e820b0307015081401d01002d241d8020051402800b0031402040303801d0307072410542c0881c40380d080c0007400768101c03590100c08213004000307004103e0401340000c21555120341c2e0b20038450b0703d5900300b01e40388000846c2440085940384140790140030301c3d80800c0740d07030548900065a605003d00c202130700d6080c1c7d00b000102810302509a000215030055215441e141c442181c1d0b0503214090088030700c181200f5000045962000513414041c40e0808850694242103800440b48503030381d00c0381a070541c03081c00012001078904000561 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 1557606 1250 1556356 1556363
    0x702040207050307110402130509060d050304060203040603060801020c06060114040e1e07030603020306010506070501060506030c071209060804020f01170901020301060e011701060809070902070302010510050405090a020405090a0b0103 103
    0x10765640045c64802845109864401e01031072041c0010315000f020307a48540b082d03070300c102c581030342170303500c80c00016511004500020030a0101040c00110590004041e100303a81181e2414403100d512109440d08074002e905181c91140d0111000c030306c583d409100040b000c954804151440c164843c0010080c004050305c3d54160020304540480750100c40382d0600390400d0385854240061071031900000d41e07804060103424806c1c1c600142da0f070304018095204000030440034081d542c81e40703440ca001412541003860b05441d12007c1c80c1d02045024400c0b59070106913444d64a0b2400f0544403070b020f00c0701489500034114103216588010040d03080e050300741c15205202100000d03a8941c1000002460030190146440c1440b184d8480c1640caa46c061400751305462042c0760090290380e4503d0058030700342c3ca07540048000c91000030580d05241d41034000314460b21880342040d040d2691303042800101d4200f00d50401850304074120001c0189000d8100c1034000c4039440131541c29500703d490300424960280d00c00ca = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 1558856 1250 1557606 1557613
    0x306050702030d05010503010209010806010e0105040905040b040303060b0c0601090903030e16080706050f0304080304020102070302060c0a0302060606180d020604091a09090c011d03070f03050d0e030f0c0114070204020705 97
    0x59035520924044d850152a0a0f00258141106036001030040310000d41614144103062054482d42d0b4418005d03a8002c044d030b49400e000034106820200b4142d04152030a400190401c1d03404107a0107008070440c1d503011200002000c2603803800000e080145040741c000c03410140c035107085010344603003001150640d03103621555841d19450090b41d1440c1c4021548a4818010180101c6421400c8041076075845508085400d0f501e607590303c0100e08002c8203820080d4005008101d5a80003400000d06a00380c42c4a40c00304c41080d00d80b04100320141c002d9048581c1180c2c5203001402d42820300ca64100343c010701c0506000c1c185611028102c042d1850f601d11409105407001292101e85000b4135050b800880c1d00b40036104040c19900000c04110742000d5210000b4103c1c0d00079581034a04101c8000241406a40050350030749900d03281c0d44a00c00050350000050b1340800741c0d0780c01c0c940420000c8860406500418019000e003005440f0f6001001182d8074078002801241c0142c1c507140010400302c1e01c00c8014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 1560106 1250 1558856 1558867
    0x313080102031609050105070602090307030f1401060e01050907050a02070509090c030709020f0301030b040c0902030f040201020c0102060c0415030207020d030807140702030a030305040f02030a1101141201060e010207030605070203 101
    0x9100f2410080d01c1c0c503604001e4002401c0041b81d0700074040325a2181c03c54805680c1d0f00c0ca69020034603154481d1300080c1034807010070321402800044059080121142002488104e030782e10403618078200280542648107039800080341500b8051030083ca031041ea180183e8842d80da462000660103003085605203010b0308030000038a110f18080c040040a0003849070304504207101c00e080590140030501000f01002011008030f024081546c8012000300309610065503030340342c61041e4110128080e0f400b24094814500c07100c01540c008500c10384501c10032680385007003a240c041101c1907044645500002d05900b04004805600c40403880b42003d0f001351070700a442d051001008101c10800b8104165982d0144009401a0780101d8208a20768151a0100f080e40b1035041003000051a0031000303500d40b041d285103100304254036000c04010740003620345035031502c21441c0c03044051040c41103c0241c03940070780040c0030300c5000d003a0300b08010106104660360300740c603a500c0d5801c4500a65080e00981d001188 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 1561356 1250 1560106 1560121
    0x20c03010e0d0906110c060a020f0a03090302040608010203150f01090305030c0307140604050309060f0909100302030c010c030207031e020a0b040503061308070b0601121d0c09040308010605030405031308010203 92
    0x3d01401841140783c0038194400c0d2902103601d5482c001c4075a84901b20000380c501c1e0340c5108114000c42c504038142907450003000303860041c00d40016031004a0081d8184100080c0080b01172090301e01c14140c50306c000b03940200b45030410580ba045255442c0c14440301e0360000c00419001c00c0900842d0741d6202c021a55144c1a08080f2640682e255180b000c6511070002c000001e01d011040d40c5104005681c0c2c107484d0940844480401d00440d10311542106d10503007000241d442020901003228025815540e015401d0001110601c0e010305020303005d41d0000c00700301300103441003034541589803e200c50241c55006c0f60b07000602001d40d40d44020783c0c0072000719050000345018820b564020000107407000030700e0201d81d200d44c964010702c50040c000b4101c00c000584542d015110000c90500010740c104181c001c0d40111803000c000f5901404190310030000402c03142e00740100454055a01511400b110ba071030810b080b100c951000300100c030280414031503d0318403c441c000c0740024045500015071240350400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 1562606 1250 1561356 1561367
    0x3031b031209010c0c060207150c0c03030f02030601051b01020405030a0c060809070e01090203060103090501420e041b030308150102060708070c0809030d030204050109090204050a1203020c03010e0d 87
    0x30244842d0340d1610642c80030954200c3c9030944001d030b1010015840e00510704000d41494041d0604801c01f034204811501c1d415880b048404016121751010080f140c1d100d00b11070200d010440e03d16005c500100110441a41041d4044a410030280005840c180c3c507071000c00e041040741e40381200d07134000c024400e11801d500070301c1c840c2d07106003c0c0d001400b0302ca24114091028400600c6000d51465000005c44c5032039100f0741109000703e40141c000c0c420511044559940076168500071072001d4000300f03070b081c0c1c0c3d4000502050780c0031030610710000c100d9013454504c001e0010301034411254841024170740903160310442c603080e0045020362103217241407408243c0b0558564600000d6811908200100035100d030b04400c5072a04114545002c1c4a110204e01c0c0101d494802c004400e40c2c9071180b4000d000c00c403603040e002001543d100713980d003400300c5035107003219030a0f80210301031503921540410052000d02e8088508003d501d002e4411181003501c0c42012900710388880384480c895800140038940306a8205 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 1563856 1250 1562606 1562611
    0x30d0504150b06030a090f0210020714090103020a0b0310030b0408030601030608010203040201091e050d0501020306010207050105041802070303060504020304030807030b01090305060c07170a020f281103031b0312 93
    0xc0402e0100030202070024285120040c8407401031503403600b0900520541000440141da03024040416088050710080d6440b8524840d1600302c403862070307030803600c2d0510b1a0324078102c80d4042e1102111a050043e00491500700409800b4140d000070800008180c4e00c4602a004502445081d1303a01e0a1800006040c1c84440c2c125280f503a0042081c4030060743d000c60b01008a400005c504c1081c00107400c030001080d00264000ca510449042141c0d042c00011341c015400b0b10001d030200c4150682e40c100554042c0100c3c89200e1403260740d6203a1035001030881c1c0061051900c03074500000c0c0580c844001a04981041ea0103a0025460200b001041034051040590141007402c01e01040c40c40d65940c3d075581d98009111a203240000324180040200725401802c00f200d201030080e45032202c3d103000039501d22207610003528034841c050341c3c072a900b54081d142050000f240c02d811a14001140c44510031020b80382c0380141c051001f04080c2d0075080d0902c065219410117080030750383c0d43c41c0300c80c0100c1121001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 1565106 1250 1563856 1563893
    0x2070204060609140405040302030405030115080606010f080408030c0d020d020306040b0a0b0714030c010603051501060f0f0302030603070302030106060c020120031b0c04060b0304030305070207060f030e01020408030d0504 97
    0x440b842400740d4240142c00104448040724003080a988608d012400c40c02181c3c0714036015800c291101c0515121610f2443c29513400303c0445006070f03038400c011a141050034a0b03044c0804d04840219001c00c1002004540c446482c1c4241480d000308801800c089a200d83c14420304140d0100c103020310307403926001d1203642080803118001e200b4102450000c0900c01c0c18070040800c0e4480003031030b1031200e0510954850740390000c000c00445940b420103580b1880302d00d41c0c2c01100241c00c000850307418081d4a540848011542d512540084040020f0f0020343c0007809040d4548030b401c00000050f0703001d00400000d020301d40d480869080103880094001101e1021501d1504c45101070525030a100106031661044c0400422000c85000c003105c1c0c1c01c003e180c09800d500141085000310752103600500642c040c40c07090394204101d90350154200c0e200c01c0709003c0c1c4c0002030f00c4000c00480d403d12035000700c011505041d00040c5010303503410b2181d103550300031202c1d10324464a50b000c001c11311179100d02c40c0820740d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 1566356 1250 1565106 1565117
    0xc010f06030203120903010906060b0301050109080a0308070309020f030616090b0702060307030902011103030403080115020102160b060414010906050301060509010e01090f020c0f010f05090f0303060405090c030601030303020702040606 103
    0x460b07001980303501c020000109440e80c00701c0c070326a0a03602500010203050f082101040b00d6a100c2c07080c41301030f6100b4050b180c0492418400081d856000244450116405540b0300000ba1100e403001c43c09000440c2040e41c0c400e03403445400b11240c1d001d01c10140242d5048441041909100320040c0c0f012b5602c2e801005149003d01130903016841d95400c44c1d600001c285000a40d01520b0710050390b1911400d4641c58035803101004210030547c00282803410b95510601c00f80042d80c20510880c00e0b40b2808032248010440c000c4604006501c1c020081c2d007000700240086005e060107141c890540c14240d0000c0d451341e0326103d081146003020700c41c0901808050366205103030360404140f0320f0304407418840e840190350b88551403d80c0e050340f035041c1c5a00c108200d090301d10507100c01c0e4041e40a88032100004008900d813001151400c040040e1540704403034290091415582c2d10000c01c0020400248980243e014002c55011140d03014000c2c24007031482a200140c84445900610080302c2c0c854200105000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 1567606 1250 1566356 1566359
    0x50a02070b09040e0703030203041409011206090203030c01020d0501050f18010b030403050403080406050901030e01021608070f0203010c050a0201050907050108010302041d070b0c0f0303060f06130e010b0c010f06 93
    0x550115408040c0d81c021551296600c0c0c80e000420014004440329000a0007468008402c143e800320007481190480b102481e500c43d186800c20055003820b02c98117602e452005000400180e07150000000c0d117000506503400c1190420f00d5509aa0000c2c0840c46901d03907400043c042c0e4544800c0c4a0346081c0103490500d8038000c220034004801c40180a1640900d10200000b010144100c040720091940a0b4059444075500c1e80068000d402c04402e2501081c2400910b02c240c020500c01e460039118490302030400405030b511003004070707400b404040c5d5002010112030401350310240540d031640d1050750345440c1c3d10125603000a0131560090f090010503003000e8407c0250741e9002c400781e8156a0100e50004010002d099449140100a80c85e5400303805400000950340300404003074aa00140b00c801d84820b2001c1e03030301c480d8480c0720858080754040030696482103181032403000703010002600b52040c50202d444d50981c42d800d0030240e00129540c2c200003031a0042d0002030096610000351001c05001c1e0030b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 1568856 1250 1567606 1567627
    0x2010609090330020d06150f0e0f0a08010905060105031603020d020f060c010510080f0303040b04030e03070305010603080a110604110603190e011b05041409060f040e0706030c05 78
    0x18441100703801d5804110a2160074903050740f98000c2c081100c0b80d000c43d900d40511403040040c005da13100d248170441c0c8112114800c01d010703000d40c0c4d134100c1613035440d0340c41203003150100312643c030a40300c220781c200c243d01070007203201031003440b800c1492801040141081d41c03600c3c08161911a00c842058500341203114100010b0300d414078809089036044404020b60503010000c945603015071141c0840660901c1c050050300b540100070306050f2451b0314160342c0c05a0700b4510050740d030b00c02620000d201480c1e543c00207010074401c0c000f0300000b110007000c0d0707080280e8035100c040c299a515002034440d83c0340001c01150f019004803400c00c00300000c0b00034003c94a026100e40741b10160000c1031902440c030010000d10008040b01542840004401d420400030380801035a900a010011400900f00d00c0f07a000341c0781d800e0144090740e048030741d0000c502d110f0f000c03600203005075001c010700007a40000c0b0700c1e003103801290703514010740350754614003001000b8a51810000805650100c4048024010304000800e0034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 1570106 1250 1568856 1568867
    0x2103090103020304030309120c03080c070b060f0a0308030405030310090e0d0e03030904061701050c0f04030f06090602030c0909010501030203060d020108100308030405030409050a0216030c050109080301090903020106090903 98
    0x200000d0800503229aa07508080d07010744004180104040c25200020034043e80081407414024081e0b42c55441c2c560340d50076140c850780308104000d080684a0000501e051504116090384110060b001c22861a41d95032540500d800580b01243c0640004c410088402c682940c0400204803c1605200800d1807081064541c801001c101080280c9103118250b140c0382001201da1800d00a00708215003070355660101c0c0c110100a90520315075090401003071005040c6801e64500440300c04845240078075590f5175103562030007410f0450381d2035110b05080300401c90501c0075601c514a41c984055071140e0100c108010410142c002e281450710500610600351107458084024950a090044964807251488280e0b87c034680d100030040715000042200700a404406442100e082e01c1d428002910340c00c5160050f8040c01241c800000072000b1403a020a101e007910514260088000140200154481c281694800d8200144540c2c484880c030080590904c603140042200301d1003044040391a0340c00510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 1571356 1250 1570106 1570117
    0x309030507110a0b0a0e0102060604060311060c0a2001020c0405070203030703020705030403020301060603021c05010302030c1011070602010606020d17060904031101020703030b090c0304020a0e0a020d02040f03022103 95
    0xc9008401c8480001d07103d81e400d007000350901c4001d15885400d64040203241e0501e009031140140a644007140544c10140a8041079030340c441d20001d5030031401028001960002d9051028a01c10344810318041566880010141c40c0c402614244042c2d12000282c940300e800074945001d145400700308051640d001c010b503604608140350240e0354034200d0405070f00d103024540001c0e5040d442d0100001d10141c042d80101301d225001a0360300e84405e03485240038102c030004d01c030294150300815405d0b0401d140c002c030000742031400b508003404d810b03020040d42458070740b007600401d0260390b40c0da10078003059404010089480d80c040c500208040c1c0310070916500341c1c001500035030103070050305d01081c06c15015030156160003580000854607280c0c0c504004004d400070440b428018001d00c0d000c1141000f10104484c40344c0d13000380c21035000754540104a503062800078420214260b003400120301c01c147d203000602c018100862541c1280c1d04500401102080708101e085952464403c04004803001106840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 1572606 1250 1571356 1571363
    0x5010f02070605090105040506040905012105030406030b0105040306050412020105090102040b0706020c071206020304120903030e0f01020c030d0206040c0503030a0903030806010201060504020c0109030e04050c0405091312050315010309030507 106
    0xc0d118401d01340141c0b0b03103000300d801c0580d01c0203001c01c001c680311010f03500541c105da1b401484500d2000d03040c03810306d101100004c8013070090b8108000c00e0044d0350198010071305904062414601d400d5482d15039200321402640e0840f802400d4030002e104290742409041d0f041b0209200071441c091504400c1100c0c1c1c45002401010a5000700d8440d0303151000b0700000009000a0030150003a00d420703d0a24020360085030211082c07005001c40b200414421040e49090340d900d51150f124952829007001112000c41c00080c1c1184651080c580c440c0c0c90905c0703000c5a2203410b400600c0c203400c0c6031034802034803441900841c1c002c0c1d10038800c6c20561980000c0e01000c40340c15003401540f0b5280d190041b0f0242c1200e402058105000040380f0f81c0c031000561052440e035004c4e50321000d41e0719511040000341c80e41507d2605060505000600c11403900707219198101443d0460305507034201c555110085010250784034000701d80c0110400498822095504250420900c0d08100030f0b000c90784c0180c40740c0140c40026 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 1573856 1250 1572606 1572617
    0x40b010201020306010e1504030501060e090d020304050a050108040f050d0c0201020114070203270402040b09120109170a0507050f010501030b010b03010b03070806062205040c080108060a09020d0b0109090c05010f020706 96
    0x2190750101f0f008990185800c14000c0c4922901c440000c45041001d03924040c4030310506540d106058408020395080e00c400510003111070345084011240b010000e801514070105003014500004ca08014030960342000f5110703400040701030300000e0b00711508948030030150b40e5000d0030008116030220480f01c4007503040044c542110b407043c01041c1003610003000507402600c00200494580c11a4000d04090b10044852a468a01c0040303014241c8102560083c02d0200d654054100c1100140c040c0109005610302141803a000c1c0c5c40b030354500901810005102d03556280140144038401c20b480707000d015120b2a40d840c2d0351500040e82e8044c4001443d40b000c104018020451680c1c51a049689405001c490516240c18010440c1006503541c8206486203140c8903103242020b001e0300071241241d070108040c004642d2075031800c40140001500032a0300c07035040d0040e1400103186c00e43ca10301a08079820b0003d034003006803411900c921501d03003102d414000c10790482d60701980d00013408000e480351450320 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 1575106 1250 1573856 1573879
    0x61204020103090f061401090c030c02070b16020604030812090d050a120608030a0206070905030a080d0506060f030a05040b010608040803150a090609020c06010b0403081206010905090103030c02040b010201020306010e 95
    0x1e403c0384d07400804000d01d094104840012000d91a0b0b960038182c03040c065040040030220032040d03044a04400003000507800084041042e000c900c000b611000451807100a1040626800a0607940c0315400032143e2401c007240f8009440c00f16010301c0d81c00f14100c0d008100ca08120300000c3d01a0250001d00301c10043c9800304140740d0403407a00100014003a060859480c0c1070b080a019450f000e003112031b40006407000e400040c03185800990080d60b107420807022807070208808511000750400800f05500641e081019480450301c0d0402103209079550140010141002d00d0b01c540080c0c410307400103081103626001d20022902210031640c002c0020302e0070401914001c004580384000560011040d11b1a20900249002c01d9030000d208145000d820303a00c41e681c0790440b0300602e01440c00044e0291400b03121454941e1050903d0359000841410100a02da81d107000051040c6026003080b030000d004071500d01c00b10b0526010701c00a4003001d0009505600c2d01000090000050704840c611400081c0d10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 1576356 1250 1575106 1575113
    0x302030103052107060e0307020913030f0201061a130b030403020a0c05010206040308010e15030d0914060316050c010b060703090303020105070c050d03020d0212010303020a0302060a021c02030c0903010603050706090506120402010309 102
    0x102c51a10b92701604c500b205181c11244103010408192007900460301051201242c03501c10f20820050740c0501400c2000e49200c842d1000040e0484544c030088031346c0110020508011080107036100302e00c242d0007040c1c00030302c502c0c00300d036407007a190703c6941954880005e020007ea042a00035054600801c03103036050307031307100004a2002c15100b041550180504400700d4003290341301d41484180d6210a07a685c1d100300942d01840351a1000321a8014600c140d24010b0712240c0c0708500400b2104510400842d2081324400004e180354403005040740800d140440401c10160203000e8a9801161810945980c80755a00d4460301c525600347c010041540c001034a000f0707108940d040e903880700c0c800b81001c810341da101c3c83c029603202c94861050300548264000265092501e000325241e400d9140c410311000c0c641008510043e40010300100c03400d180a100f130f0500e9840900c20b540046024038000c0140500d450000362800c179040d001103000d600c00b045900c0d0100380340030309544c0041d82031900040000d110706 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 1577606 1250 1576356 1576363
    0x1110c04060303030b03010b010207050d020918030a02060a06050102010c1205090106030f0503090108010e16030c0c08030a0507080105040b03031606020403080c010207050c040501120f02040608030a0302030103052107060e 97
    0x41026601514052000c024140e2641c030007402c085080c0d008028883c5c000b00160303903c0c0c002e445120792060501c1d842000500b0281005a00849090450701d9848840701d22142140c01241154005034003000401a10132031601440008140c00c1c0000c06c0a10421013000f41040f900800381c14a030740d12000032401a9409501c035400564110f1855001c5030164940561203600150503140000d003123100200342910080750032405101540b400001007a200007055014111729148a414030509045100204020384000d52150ba444900080ca034501190b01512291068124a008502d007615480b0140c400004841542a5180011442c1045860440080c1c41141c1004180d040007044104204205402038146544208250b54880c1c00100500040382c10034030500e0090841e5000100c003094806c004030210a0010700080785071034031307240c080c3e1842d8002c0e10890f0019a00000400900c8002c1c41010201c81c0304865500051000311000009070191010180900d6910400000100340c00c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 1578856 1250 1577606 1577623
    0xa0e030903010603050106030507050a0b0403061e050a020d0e1204140f1005040e070c0c030204020a12020c0c121507080702070302040501060c02091003030912020d0611040f090501050904020111 85
    0x10700074001d8544038903155020301960b2100f200d0501c10040040b0312407409000d0401a1280040c01e641400e28646501020f4643c0e2111490030301c1d050083c1004011040c02200c0c0b103101031150159449029281c03200445140c141c1c840415001b459690225550180031242210940381c14010181c2035800001c4038900c5407a200d640c0592a0801003689036001405002100c0445041c072402c0c0d5a6a1425140b004080c440103210008d083d030280300610349a40501142d4460303142280400100d4080c200072a40020307600c500580c4240d040d50348624010361410080c92030b4602600d41300007a4040b08618038000380030780082c4050701e000100d03813a108001c180019a0001c0c02800741d540c0d0f41c0d002914004c10b80700c00f45d005050403400603440507000d0402d002221343c11354a0b052a149030222801c0034000d01507040340e104101c3c00410b804075400d8040e000700c803000005802d43c0d85d450a01082044080750b80310000007400c101c010803256585c0000194041d40a00b4580f031801070a0340010b041c0380c0f96 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 1580106 1250 1578856 1578859
    0x30f0b060a030c020607020a0507050909010b04060305031803030c07090903020a0f0b0601030501050607020904060c03150f05040b010807020a020904082106010f0207030b011202041103040303020702040b090f0a0e0309 95
    0x880c5008409030302d50003050300d90310b46409603942500c81000403a1201c203031000c058183da0100c28100000e080c260740c095840702026000080410ba0940010243c507221340c020f0760345a10110f03412064410383c0c49800c0743e500782180194601216a480c41c2e0702c1c1c080e03d1151b941071a5859a500702818005d10504c42507543c4600c0c0f403000b0040b60301e001a0709501c240c13019030010345444008075031814000221003a60750001c0c0b80d040d0a507a0307950f0f00b001034075122624030b0425480701040b01c1079607030a00c40d40c3c001d00b0090b19211072030350400050008032179132020880e04016880040c40105900415500746062b01500c103810a550b950800f60818030850100c8075a16200e00c60702c124031441d40711514003441d401d03600d000c0c00040e0000c0482e903501c128080034202c0c0000e440104111252040b065030030398030103000400c42c82000518801c9541045400b600030070b40020b0300c00110700d06881424500f900440d01c0380303e0703410701c04d4001458400080034403401a560b06841142000200306403400d5060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 1581356 1250 1580106 1580119
    0x204050411061903060608071709010b03030d0906050601030504080d020a05091201050712050118020c010603080a0203040608090102070305120403030e060907030209010902030105010c030f03060f0f030b13050d030f0b 95
    0x540c0f840720815040034861140024540580840c003984070b51121405841d040e40d03007840c8140d01d440c89061010f0050020f000c55966014038400c240c23002d0000c0e0201203030001000485992500f003042c1980c00080030700381090300c0c2c6001c000015500005890342140c03101030040e1203043d07514080d0390394407491200300d900c103402030340c03480310340005401003407003001107944400c1031101402c0341c582076403801c0c0200800d92a40a0510708030710016406042c2592500c000480c00707581e203031110310f4680c1c003d000280060300002418800c0d00d41207200030381c000c002c1030000c5281040300d4a004110b80a840340ca400e04240c0c540109007410310a8000100d02a00306095800f01d04010007100e5803807400b403000302e005406480002490300818401c6e28121401a191865038100950301146c061803010301a1007032568810003c1440044c10540d00040d240c4078208030002425801c00c40d4181303200520b00d500ca0840b0207080b2002030400701d40b400b02d5107107034140856011000c440c1d50700980082009103400c0b14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 1582606 1250 1581356 1581367
    0xa03030c1a0c04030201020c0405070e0d0206090a08010203090607090b07080a23030105040c05040e01050d0507091a0a05040b0a05010e2403040308010501110a02060706020d020c070311060403020a03020405041106 93
    0x100b6190040013107a02c01d0f000c80721003242c0d10080c0f10648008482d15030115000d41214a45030400350b244160320380c801454240b82010500c0000d5916816400c205e040e07070341c00300c1044141c6504000726504201c840c01e04c1d09100e4544078959045202c1c1031802080c0d64008200409418007a0240181003030000411000b1004405814503558000f4812144600c1c104105610081d006000301c03426a0096060103016070300701024018403a10a06003194140b2620030006420815441482020380c101a0003d503203100c0b010810070040d1003174022511442c03070500d000c8120303074450720550103c810a0034080d010021480024000b003081b480c0d0001c204041c4007014042c84071100046101e41d2180d1a02c000305c4e6280c0004441d803000410310090300768028048400585000d4019003045031003101c1c05858070400f100744400341e070000e40301002c1660245d44203100300040083d00c0615002c00b41c906509140c5550001030700c1269a1002a010b107039180c000c00d0600402c1305010030b4012000e0902d41c0e840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 1583856 1250 1582606 1582621
    0x201050403020c01030e03030402040515090702010b0f041a040506060d0606270501020304090506030102070c080f0607030203061005070212030403030c0605070201020406050d0c20010614030c0a03030c1a 89
    0x81204480072801805528a0320040b90f00074404e801410403044001c5040d5916030f070030300004100c082c4c030032010003070820b99580c01640c2d188411807050b22568004185075451000b840022060301440724403d071305000b00038018400c2100d9117241500125000b08280c0c50348004240380f8820208407400a80c140740c404078040360031a0b900c0e00c694000009500850107034103c80030482125004482c010381040104200300031080c2c12190704002c00400061501c0b04540e00e03600c0890311540107501d10b4201c2c101c00d5001d8001800741550141351818107515510340440094081c81c04050755030144000481c1c801c043d901c46074211140f04404504599880343c881c20041c02a00001d40304580380c81c100f1000072030b41407043c000e940c102c030059216507080000e0f0300501000b611710f000c0709800b0401c6021907010214504115903810380683c000010303907a403c0040205148101c01c20075030080d070005d2080720035504c0d00c0240204494040c40c1c000ca03251000c0c40c4c24181d0100c06900ca04001600c41c0500841 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 1585106 1250 1583856 1583861
    0x20f091b0a111e03030402010c06020405030105010e0105041a0108070f0c06050901021b01060305030f030a0213090203060f0102010902030709020c10020c0705010f0c110603060105070501090c06080708012301050405060a0201 98
    0x1000ba036004591980007140100c0039094400d24043c1c1c91a0414404140194007807160295000c0c8101c402508150321440841d0031100300340c1c031060b01b17050381100400c4a41024070408000360000f6108201c240c900d24006400b02601424000030040c5028090341d010303102d0003010403071942c00f120a00c0603040c6100103038080e4001401c8100d9100d291050750520409c140708940460303911101039414103041401103c03103600014000020f440d000c212012140f101e0b4540b22018003148600181c881c100201407000300c4540c0604181560703d840f01002c09030354001400002c50b1f1030b60801694400c00080140d003000003034012440307090700210381d4010070200483d003030b000c4d90400e90b14403002070700c1c0d11803c07510701101003406090a203c1030b1400c0800c0c100900210352100c818100f040c078101265480500316022a841a0340303682c180c1a05100790b5510542c096004081440c1014455041114411701c81c13902c2c4900743c80b01042031071598000e034001c00541c3c00801340144125100d0840c0d030f1001c2d02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 1586356 1250 1585106 1585127
    0x170f0909040605100608011a03150402030f071101060302061207020f0a03020d120204230a0f03080c0c010504030203030a030e07030c060302070507050301020406050a08060303071b030b01050904020f091b0a 90
    0x101300600b01010070958412002e042c100e44944180526000f591421000141d01c043c1110503806a0b5884034062504c480c00114094008042555154038041900410012002100300200c2e418094108050381e01c0c1c031700356110409980070b8151030303454065040c1d2402010f02071285250250780000814190081a00c0d9140003082e241d4845030310301100c20000700e2141d401a1100c40e205111411000f4119090b8002040400751034481c40c03d8550342003030000405030744111134041c40003d21840f107010500554015843c00e0030101d003054203550019481703014000c000401c06680b120180f026000410481000f150042a1681b0303451316a9030013006544091026034079407080280000311410144210750842c1d911b5070b1034034103115011408549060018010586c144030038061000401c6038004621070b0880d0081c0c0c4003408501d149090807a0040580c440c0b8440d0320382000300700c0541c40d00c2181e290241404c40741c03510b49030b54500e401044400d2001400c4014400801d5a01302603810450b46170 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 1587606 1250 1586356 1586371
    0x406030c03020403030c030c0204090c1203090e06030a0b09100f0c0f1706040c051c0209090901060e0a020306010512040b01060201110702060403170c01020f0307080601030207170f0909040605 84
    0x8031001004140d050380b08030310004000514019100010a10030213420003043e1004002290030760464445458810280d000030300c080070403d424002301900107080e20020a005802000c1518105000a840703500c4078002a00c0c90340304400140145800f88180741540c03c407060308005001c0b444000100800c152007400c0082013012640141d06030283e0b0b40c044024041204281d11603a0380418000604200001d24080c080140720401030b82140c0c903034400d040080c3d08001038580540e401040410007000c1d08100fa80e9140034414480d200b450142d9039400000d140025a690f255000100c1f43c91082c4000c102040c0b210b50b09010810030108401812503801d58020320807076100c8040f1111038807510400a5008034100010000a440c9402440c848580c01d61014200000c06c03c0244c260381c4040c500c2c001c170b99000800c011107581c101c0c4289402000030300c2c1c11800d101c1c1c140e54020109001d403141c48500540400c4204050081c002100c0c02c10790301800f525101e041502d0402d01400040d100f40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 1588856 1250 1587606 1587611
    0x1060302010801090b0306040809010201020702090c030405011d030a05160501021c06080c03031b0c030304080a0b0a090201020a02090406020d02070506010306060b03070206011203090b03010b03060a05061602010e040902030a08040603 102
    0x5540b10380d40117560344503030b004006d0b048a0f101c0b562078900d142e009151281c1555028041c140c0581c2d04c4244040c03181148503075140d544d14091a000b4215070324200700703c4140342a80074085c0c036210000706840804200d824042d5950640e5010340c100c858950270700508640c00040d6405900c88448514007075034460071014090251154919621100c440642a40643c014480000342da503c014240100c480702c0700585188012841c0804e0540c0d001d5040141c0e5035012014110810000c103c496034801e40d546010402440c00d5130000b500d075401210041d00c69419000401c09000042d0b044801d1030341641030441d540d1519140580d00c92600f4402a9012460b00b4000031301d114403642242c4c443c1d101c03540a44020382c2031009007084240c03184020303010400040c1c004640c180b000801140a411080c095a072039292420030428813400c00e401c680c1c05100c2c00e004d60011a0f400204103602c203036090800640e02114400410020304a41202961620802030030350107100c03242c80140241c0b80f450340c06 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 1590106 1250 1588856 1588859
    0x150c02010606030b01020c01050913060e0405060603060f010603020705100c0e03060603030301030305030415090203010c0c05010e070305060a0b010507020d0305070201080c0301050a05010c1b031103070503120f0c07080105070201060302010801 106
    0x1d070104d0380c00410703030750160b0080c42c0900280d41c4940c00034815050000c0015104d81500001802111030541026004081720410701c403d001c001c10045070310810031030080c0098504a01b00540685042c0310700c1003130540101d003840c1004014008034034108a5414200075911000100400707641c4600a854024018903000c1200c900300801243d058a0b0943c5400d03246456540c0c0724100d0b1501c004031020315540e42c21404005030b80a0040030070816007552205040c0c2d0460924908444a440c0380410308e1348005800c05c00039501203050380d40240c0c5604009148141040142d82c0c9100d5400002c1d886429404034070101600a405806240d00070b03603078030519985889940115202c20702070b003076001c103400d101003203c1c0d03100d0f08850f400c1c180b045803008810745104c25050340c1c00b00309400407100c24091003ca40301e01c0c01c007081700100800049000306580064000310540920903041d81d0f820300500020380001049080212100925501008100e82d20345002d009000b442c0d079010490018615400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 1591356 1250 1590106 1590119
    0xc0a030c0206060d120203070602040902090f09070c020120060a050f06060307020307120e0d05011a0402070f0609052a03010501090e030307030c11030703020f0d03090b04080304020409150c020106 86
    0x15658803030078020308802580d600300d4440c0d198017442c0460301411440108002c40014580d40003030001041901400750710f03030025008101400c3c400b00441d600541418040100c1c0541c02100041800e40a013400c000c1d0322804c01898060007040c4809540304e104038000c1c00b19000d0240e200509c58156900b544804c1d8443d8003c1010500c070036680d28005034410700004001c104500c103000b5070380195082c28242c01e10420046004c5400d0340005030b8550350348025821700c8404141d1700c00400d1800303c41c11071404041e0740c0d42e070381000800580904140d94440d451000c01408000c82084142d00c0d04410188130343c01019108101e25040c0901d010f1b5007803c3c000112040940941d4440c520310002450546c2d0300c07a00b040380204030521021003004499041c01071303010710030b00082c820140240c0c081c206100c04034202d40d10b030051f0a04480205494800118085100f00808a40080d80300000d1076803a12071f400081e019051044000d012071210704003040240190303600c06488561640c00030b0181580d5000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 1592606 1250 1591356 1591363
    0x70801060e0103080c16091401090507170603011404050604120507080415020106090609020a1704020a0b03040609050106090e0d020f0c040c110d0305100b070312020a020a0b0c0a030c02 81
    0x4a10748000016000510014540c0c00142c22110580403c9650710404c850b80220503849071341c000000e15a458400581c4410111000d601402801006100c075040c1582c0041c00740e43d0140c5070030022501800402c0c034a540a402c105604880a100326183e800e180c1401525440140d90403038003040c100f801d8011450084080d210b40c647c220158604007032402e040d403490340102000715006c40d50b80701400714600c03603184141c0c0058801c04800503103540030700c080501030380745801600c600c41c1d10020070040142e5440c10940f080c3d800f40f022694598480e858010054140e88000401d5542090008031b043c00e11135006080c50100703801100c0c00c5454030303201030ba200c40a89003da04c05802c80789031840d15080035000180640034901c4c0c03440799400304a901a00b0200c60440200c0001c0d101c0c810300444020790a640405000300505003032600310180d4025141100c2c01311460001034012400341200c41c001e01c1002045500449080c02510346811006441d40c0071036076510209103045901c112061001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 1593856 1250 1592606 1592609
    0x10060e0105030403030b010c0c03141603050c060702031501080c01030507110606040b010e0406030c0905010b040605090103050709081f0507020304120f050304081501050102010f0507050901080408040f03050604020307080106 98
    0x103071074061668031143c070210081e00014003840d042c4042c240421001413941490000114002d1a0a88030061069001ca04106880c3c0050701c00041d03004c0f051000c9000882c070000300e1a000c03103050356220100e1003c24242050500d1412403a03110000020346e2000c042500021132000743d03802c000640d0340c00b100b941c0061500c82c2c003252079071000c40080d1590a141c3d02a110401c4d050500702c00c0001c8110001d02640c00720342040303d540d095958104240105406400d014001040d801424281400c000601602801014504250319580032030061401000c80e8406080c1c40d00588044061001d15008003141c103030749401c0c80b0381c500760005524078030200584003030796000051306409031150b49600780c41489540702980e150200b0407000030b04040401c0058142154078082180c1076240070006401c4803018221070700428144002c01c80ba86610034101d0b1300c10042420450f83c151101c0c2003424503030240f50800840b0b00c8d004003021080c040c0000d01948600c0c4202c040751001c6840750b141034240d401a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 1595106 1250 1593856 1593859
    0x10b07030e0a03060204080c10080a05040302010216080d0507020303060303070602030606090607050604110406080c040207020301110c07030c06140306040906090818040f020403020303030103020d06020c070b070201020607020f0304060302280810060e 109
    0x581d000c10550f42250f00b0037030304180a07100150605900c2002894002400c260456400340c001510000a0640d070003201d500074014000345080d46000800700e86c8a1040403402000540d0010000309603550301c0059400407203002d8542a240c1c000c610340541c0e103d505031025a448402600441880d2425008440566072001c0c0a07011036a4084c0030b2002940241408a915540351100d60951403085c402600f2a10351002c001d01c2c14a155003860074207140290854070420620001c0c100700c1c1c00a00040320b0b004070041d0780008820501e400d00300000c00e0001c400821b0180d0014243c40781030310540d420036001c0e00490703041000b50980000c5108074811440000c1d0141c0007440100050701c0c0c01d02005003c03e014140161404204104131401e03c0225000455070000224442c4150759041040c554451003500003000711034002c2035a42c0d80c0e0701a600c0fa04040540000d6074008a01c045882d0101d90569142060300d180510300b009840460200c868040b01c03240da03640090a41c0c4a010381c440300c400c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 1596356 1250 1595106 1595117
    0x102030901030b0301060b0d09020915030c0907120501060207080f0f0c010c080c01020c01020403060f02090306010302091008030c06090d050f07030c0f0803070804020406060906020303010b07030e0a03060204080c10 94
    0x3036640040d40a0070760307000d681c2d40c50356903104005103054002c0024240c0d085c00c603800203041d2005104206401e000600f4100210101015055181d140042c4410030040201c030310a40300e985000c8100d4141c070301b151701003103941d003040e00015180c1d0b0001280c00c10384a805007540e52071820100000d640c1c0c89180510107459102e0000b071815540100d084008550040c1031042c03030608a50801426070b4410791840c02540e500190800c2849403d01c14120408245541545069450400a41d44020600020b44a0301c14100031801c00b02c42c00b451074005014280c1500e482d084031021460f02e85004481480d402e0207105404401584220111240174040da000507040010607101100c04040e1000111402100b0b40904000b01d464100550f1141c2e00c155114242c1c0c1c0f40a205000503188503510000510462046c1842130a40101c00d0f43c1c1994088040350345c490113141000ca0f49449000045508200100c00120a2210f60b40081003a03423400c2d0202d031100040d003402c1c0055240c0c103a9007200000c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 1597606 1250 1596356 1596367
    0x203070803120109020f071407050a06030203040503030703050604020d150f08071503050702030405090103060506010e03160e0a23010306061a03070c02010c06020f0405040501210b070903050d0809160302010203 92
    0x41090303001e88041c41c103401b0300c2c60a04805582d0b6003e9501102c903040d10981c031042c002c0000b4640340301850060030040c6001d40c01d508041c1d0b030710350b81c03800090890301c14151510005101500c440c0d05540e06c29001c0303032090005081440d218000310700c0c1c502629410040e100c03004110303001d00040ea6800c49021104010031581803280841c01020090300e1081103004c10400010340380d0701e111950380a0350050074002060f080c4400054403445003c00035500941101091040184024190004581c04036841b01100e42e80e0303000b038074001e144c402c0d05801a44240e00d5400c145015400b10241038034401c2004100c0c00d51070700b80e082d0a05600c84500c44a02e00d040000442c802c0c403510700e40100c2c900c1810304400d019215554070341607800800000d2188440414108a240f03090b01034240104950f44149400380d840e0341c4601d45416441c0c0014040a076007101240105d803050200d03800440d003002c04c0e80c00041c0040d50080026006555081c0c00c0e1040c00002980340490000c01c80450f94160019440e02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 1598856 1250 1597606 1597619
    0x5090606010c0f0804030605010b0c10060506040909080f03040503030402090702011a0121050f07090f0305030901050702060706020f030a060512070905100504050406020712020610030209040602070203030c010902030708031201 99
    0x40c540d03d0400c07500740e5414880000090590701a15019100d0781403807980b20241c40e01217510341800319954070303000f41c2050410011a12000100c1e0b003550f25078400407840900e20b08080c14244100380200c02600000810441801030120255009600c01c607015081622150310407401c0c0c6020070f542c0c56801c4030b8114401b40960007041145100c90702c09903603040b00c03590303000f04100711101150000070020112041194982e4040901c00180488400120380c003804e40d02c2c0d650340c82c0030703200c01181071190024001081d96200000e6504560384110199507030700002e480001540c205590b540300a81c02d100e008115407030140344203c140001e10000b0104c452a0082c000042c2c880584600c0e80ca403135800020a0540b03490185500c101d01a64026941d452646040c400c40110465400d045411103800e201040c0392205c403905c100c0c1c2e0115420042c64030f950410200a200e100030080d172501c000281c0416904040d04107180c414021015102c03959a284401500d901c00ca918104c02030b580c090041c00103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 1600106 1250 1598856 1598873
    0x507050c060a0b010e040507021c1403060f030304030b01060207032f0108071e02030309061005030601140301060b030403110607080606070b090c0d0b0f070306050d0807030c0c12050105090606010c 86
    0x41d0b10f81454504070803104d42e8040740c2210740a64101c401a04480110800140c1103102000e0a455900e8411444a402c1d03903071103c10b00000e00070603c103460403407c0c0c003200e9070108140d078051a000210364150396501c00c0e02a684d44150f04c000c50ba011100f200e00046010400020340e003400c0c042148c808490301540c01107903a424014030403414421200c8103101d01d45061009107001180c0c6030000d6a40f410051129890160002c000402d903240d0084148019207010815504640300300c00440c05040f05600068054505600106000d04001c0100000e1580c0b04880103103001e5400140c40103916000c200300c9800104a035442c0d0015000c000c042d001544004291758130000307540aa5500a0a0600040301e280c0301900556188045000348041d00c03c0070086d442c0c210050381010084149080042804501400e00140c60f28002068203014503006801d49030109078454004031040d5200d1450b000c51042c148010b440962a000001e4441c2400140c0786018140584070b041c580c80207960780040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 1601356 1250 1600106 1600121
    0x207060201090c0504050615040b070201030b0402040501021507050705031206040e0f060601051303020402030106081801090201170403030b040e070602010c02210306121009060e030703090303081302030304030501090201030507050c060a 103
    0x10440da2408d454094521504060030143c0490408242d540e1310764000107040c2d40f002451144140e20407c010005070f030300004c90020440000781c1220044d600c2500c1030380c2a00454038043c0440c0400a403241800305146035045c41030300c04480400c100d100c8a0703080d07a56070180000407071480e40035401083c810360246015248900390940020f0142d9180d50115059030000e034007600200c0d0300c2c002131214070ba800f555800c814941c0c0c0e8008010820440c1c0000340300b0300300d007020341c04066441d00104007450f1003508081c1180c00c6c003610505c1000d0080c0a56940c7e00380d03912a1600652070000c41c0410345201040505191502486800c0382400740601c1030055031010300010340c0105540012101001d0a220040c00e100e041080020100014103190041e60800c0c0c2c45c4820940040040d200081c0d04074200d4000c1c0c0344c043c50a580d00c1d0b542c10010352a940340103d000795040c030010500000704903054003d000b01074400e07681880f4548800e80c0c01d6482d4041d02002c40c10503000000003440c1c8440340d50003c5c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 1602606 1250 1601356 1601359
    0x30307080c0d060512010b010908030705060c0a03020403020904030c03030e01060e18030909040b010305010506010302041815082a01030204030f08070201020c040501090c08060303090102030405040902030a050303070207060207060201090c05040506 108
    0x5141507a4400091000c245d0380c0c1000c2050f5150440c603019036800000030002071035408051803501a866840c1c0c5c0c1c030f410005004129042e80412001d1405200b5810380303003d50342c06007518510381028180540069a6100118006030400092400309541030040340e0889a200d2082a401e4944010f000c0d05a24001e25103055440103000582d5140d80303081c8034a0140d8080c161803052941107041060075a08014031050505004110412401c10051a02d0081c4621140000303918204e0210a00c3d104030150312403082031050018000c03049003c40f83c16240031b1404181c9040e101d5100300150180c0c041c500c00580308029a20510010030340b0f0100900e030705c0f031051040e103100e05008000201201c00c07e80003160780d19038841081e42c405e038010f40d20340e800c5141140254180a00007000035500e11503401994050741c2c41311862011510208148144c080d8050140ca4481c500302100079580c402c0b9206480041c410340d40c0004c0c800c0c1c010b10030740c0081500304d001130908508040c18000540405403105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 1603856 1250 1602606 1602611
    0x5030a020705030a050301030c0b120105010804020307090f020c10050105010804020909100203040311010b010201060b03060609040216050c0a0e090601030305030606070218010503010605060301080703030309020102031c050106080108030307080c0d 108
    0x1c4001510610003804035428640310191694158140603080c1011900030f0b044061003048a000c1114820180310f0444c0c10034a4521400e9a4a00c082404c0c00703644d80c031810031907041010000700b854098028003201500901100c000f080d280e00c50320700b5260300307206150108032000701080160400303020041d03104000c1011240203164003480c000c2240d00c1240d054000030b408082c8000e0820007801903085284c000d2000f0710015041a0b2406424800038102e9440380000042c0c03524161200c0d019200e1142c44001d041c01d03118501d003816921106004100c83c49000c0c2604041403190038000d0741800740561400501d166800c542e02030343d45a0000c0c00782a4850010b020b1040140e841c1030b06020346204c03141400e109c6501d0b01040c507095031f105030007031072243d0b80600c01802007881c0051a40d084a0701450007049420aa00050341103208850780e030546c600040541d2541e01038070b5000181250745a80d540f10484e070786d039a446502d0f0b02040e15030b0303030008001c1000b00e000c03507411101609200320b000400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 1605106 1250 1603856 1603867
    0x2090c0c0a0f03030501060206090d030b03210c06061c03050306041e0f050106020a03050702090402040209090a02090307090b0607020906010207080a03031406010509010206010306050403030b040f02071403040f0605030a02 97
    0x203500e441c03628103044450103240e8a501c810141d040c000c02c0d0040007503000602460800c0d038803150b142c0500c0c801d81400c05560307402e41c001e943e9003000480322032036031032032205424810444400c44940c014032000c0d0f81842100d011036198240080d0300c2140c000c44100098100d010399404449550024007110741c0240c4448440320351024041080580059818000403400c50901880c0251072050740f090b415900074500c80c1c00400d40050440b801c0c907904851407000ca03540c500c0050020302a40c1d111a400007540010800300048079401004c1d0b20000310308880080d81c0e281601e40940301b122124035001101400340310b00506051044940114050040c0c1e403080da1920001890301184074030640000303480d4086d00d41007260070359246810001c2071a155207400145030001c1e507580c0061200410310f9a9503400502418825030011801800013401408902500101c001c0030390807002082e540c0900214200390000000000c8408880a017400c0510803860007400f502d40d608010402c5030129000c004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 1606356 1250 1605106 1605127
    0xc0206040f0905060901060206010501051218010608030a08240f040f05090309010306050307050916030207020a0b0307170105100c02030102070b012601020301030c140409050706050406140405060702090c 89
    0xc00300040e00c410840083c240c5809000c01c42020410b034003407015500004010701003a41e00c04102c2c1c3d810400d000c0303c0c8629846400c040009200181c21404041d480c08001241581c400707c020500c03407049076561071254940c10003a003d200311a107030f401b82c0c0e0040c52003440f0b4541850070b00100c141c00700800c0000e02103006032038102511001c541ca08083c0e0800140c1c002c4542e054440d900141509030010030b510b41c100381c003207814008040d0030164110340075466059030038460380480e0016a4080d01e410310303080e034a04142803c0c0c0c10584e00c803400b04103c04030346070000312841d01940c122140188030300369100502c001596124840e030310a87e0195000c1120390041011200403034000c042151103600303030040154840d00c0407180e6580c035011704d900400041020440191908003503411a0000c400c100c00c42000244c0106044c440040c4180580000002d8003500a40544106d03116034076800f40c44400b101d010181d500c500e020f41503000e44180b00c0300c809810304d08044c80c7e01110f0a804146004031251 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 1607606 1250 1606356 1606379
    0x909021305040303060812040302090601030b15040b03070f030e0a060c021009050c03010509030a02070303030b0d060507080f06040204050a0306020a0c050303040501050103051506030a0212031306020102040f060c030903030c020604 101
    0xc030141c011940345e8000b040080030070062000030342044410341d0305160442d40012035008020f001c050405840780d1405c101c903640c00c54800c1d03200d0340c419003003580c4680e26008000e290300121413400204843d0003070380c80028041d00881000211b01e04c0a480d0f5040150394801c002c2c44d09041c02011031240030014002c80c00c2a200e11103503a07000b02d0007094034010b0b440806003502d00c010021130003078006004101841341c0001e8400d003940d500d41808a5140c9003203012800c0518800c0004e002c05080a09100000750812986c070302566020003110103c1e42d89405000c20b91049100c0c0313a402540303002040001c9003680d406420710b610f561510980110302901c400d461a001924281c1d0b159540d000100f041080401404501291004a140d514a8403000081d110410390101030301501d5003010001e5658818011140f2802c1c1a11800d25165107a0000074000c2d0800e015240c0c0c40007825102040a50280401d0003405e9855500c1203c3d09080d55002c42c0c04a9028000f01d81041c401d0102140c2008882d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 1608856 1250 1607606 1607611
    0xf130e010e160801180209040f0302030d020304080a030608030301150809030403050106030302100b0406050607140c0901060906200309010c15020703050a031406031903020304050301050708090d1106010909021305 93
    0x200d18007003e05000c440d5003140c041d140c02000581c141a80e4000586804961940c05900040341c0840a003107820140d0030b51041c0030f2083c280b18400001c000400556a02400407900741c0e40c0c0801a0302e071116640341d942d100a024101e1042050095500900d1240c032032180d000f80010b090b241820b590342d071103e007990f9064008501603000034200240380d034407d2003141d003d50720450b401d111051410002c18424400c0d0b8101404440c0a1481058824400c0181c03150280025046250660b52a00b006180340b506020b0040054480013001c504911402c01030030040300844d02941c54000800015190030f0f00c52101101d41d64041c2c1c4901e1408a80e42c030292044502980300ca507a90b041ca520002c04480000745040da140c9480000d00c40389445c001842000e01130003442108107c0d55a04040c1e2450103503901641c0d0640c01c001c00c100076198010009401100c03884101d4182c01342104007903079448070b840f841c003c1c1940020010042621590081c0140500181c061600c81c108000080c0030389804 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 1610106 1250 1608856 1608883
    0xc020904080304050d0f05040501030b1c0501020903010e120306090403090b0c010b0112021303060203060d0204020304080a1103070b07211406010e04060308070803100506040801090308060f130e010e 87
    0x100403c001d01005200b0284402098a0640c002ca15158809441806079000d403a04042c0d4403600c0c565030b500d03003d50b000301080c2c80d40c04d20031003c8070780c0c0f0f010b902030742c002760106011394200315066071144030000d00d80903081041084c49003955220003e000c9074440050050702042854940001c130040704a00510080c159003002140030303200b103030024080a8004c40c0441d9003500c10004040c8141e01d0456174001d4076884032b80903a403071304ca0030005089100e0b0345101a6000b8400010300c410800c01034010300034a190b07600d03210042e4460011207a200e00a44101a0031224020009501503120f03c00302d40c1032090b500b04105201412411110885054807054036030a20400c040c081c3c29070708002900795a0804540c2488041e06542d0780040354043d041d00200f05079400b10101b18850018aaa1070140101070442c41c0c4440c1e03100c1015010306400801540401c04100110706c5c1420004060048188090a8001c14654200c2c900004209907006881079540e0b8100c07820384841d0a00c010344d4543d19 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 1611356 1250 1610106 1610123
    0x90603070b030c030405060606040302130507020309060d020306041104050a030b1306060303080403020c03030a0f0c0206040302030105041a0a0b01090612060504050702030403060e01020c060103030f05040803070b0108150601051602010c020904 106
    0x109407421501c7d0407409040c2500c00c2c1e900b80f09c00c00050340d0380010381d0811449100c0c0803030f0585640409034510f01409000e42c0d445007001c90705a140c641c0340c0c1e0107544a00d80441d402d200c0e02030303044400440d40c80b49000d171941090040c13005001151401c00b000e50810f026080840305281c41d44c4441c4112000d41c0c000300e0000f46000240002d0560401c8101c130a0501100514a0041c04440207000810320480000900034100e80d800c0a5550b03260a560085401600a0203285001d240c080038034a00000c4640004030070034003050382e480b6284989242908103031a2401483d0601606441018048002013440e40e2282c20219854a4501819000d401c05030000e585450031813808009894540c51680300c41c0e032041c00100050140000e0b5a4116a0107040442c01c840c0c43e03803030880d00c901c540d400985040c0300000d200400c100c9602c02030382c104d80518007078400c003030000b01da0803d2005e4203590031400070b40301303005d10200202c110079580100f42c07050400c400d006070140c1c0030485998044506482030360 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 1612606 1250 1611356 1611361
    0xa0e010504140c0a0c0807060606110f010e030405011202090d05010b03010c080405061302030f0706120b010f080109020c01150e04050106060f0503010b1b0303040f05070506090a05090603070b030c03 87
    0x1010300926840840020b4080c50783e10700503081c01c005000d800c8642082052141e145000c2c07024410446e4041d541100c07003400166212413000d0803035100114194903511440300848404041841b6030142c40b81008040d40ca0145001c00460ba0b50400c2841410465420001e145e0241c1d115004100600c0c80b941c0080b81c11103100b02094216402c03074642d00240709240341000002403012039000d078000013400307a4160150203070000c2442c2c0303401c440b000e032858829a480400c656402c091081c101ca4981c11080c88994604401103039001450450780317001c42c0c500b130010b02000002d600940308a0440130000600e01485400807600b1030210360140008100301c0041c0814400c0c01e0148002405460602e084200a0084014002d2005100b6429900c1e00402d409000c0020380c4c0e4400620003804044940700e04260520862800381d001080716180f040d14400185800d1142c16a121510b0050081c070f07109203080306021001a0041c1341a5040c06215404141410128003450042c2500344c0c82c55204d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 1613856 1250 1612606 1612609
    0x20d180312090213050a0e030c0601080601090606020316020f030307060f0e010204030b0411030115270b030a0204090c030c060804110103110a030207051612150504020607030c030207050a0e0105 85
    0x50103103034800c605440c20b000301040540c40d10041c26415180940c0e0000da1303550307440d642c440180055110500c0300c0c0000158003052000008600b8103840086040e191566610150507040380c0441c428000980c01c1880f601ca005a60100345188042c0050030f2145014000e40000303046902162084550b10b988444060340701c54144580110320200200840c03420f400c0d038032600d0ba858030013031006080d40c1045001c1d01e103584081d01300703020049503540c1c0760511980b201400c842e100800d019130003160302d464410b900480c002c4c0c060b0022100020340070740070701ca8050b0248405001d942505940c5020510f00000000c1c124034560f070020041940e802c11641801d15205000000c100e10007810103007000e002050801e480022150314524a081c0141d55222604d0554144003840003030019414101d072001891802564102d10385a1044030180b401d8054a100d0108541083c0c8002e50006000c0c4101c10001b80a1051459460b000f401165150f594a00008462680070303049820300c0b680302001003155 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 1615106 1250 1613856 1613867
    0x1020a030609150303090308030a0608060709060201140402150705030f0c0601061205010501050301050d02030c030a140106060201090f020603040305040e0106030209040c030203040213020f042105120703050307030b04020d1803 99
    0xd02003d0400041d03602c0c5503071402049441580405441a44000085060000c00703030302100c001c14501c021355640386803005018080402c01e2080e90059400c240d0008491004541803902c82c541c0140581d01c009880040c041c0b090300561022a980c0c0b1040003848011103072280540404003400c0000c000b9513062a03c02000c0d01040b140d51a2120305080c0180141ea80002c107803410344800b5225841c2600b164000640b43c44000c00d07205401d0b0156100c07410070f00200028005040940000074000b1030380c0c0b420b04a003212210f402c09810011a508500018a04a0004c6030010300914280f81019140c0c03112110101080c1c1c400400300f54001402c038001d0030240659100640c55050850842c40c054000c9034503d210814200682c0380c0c0080c4403260b0401800903100a08008003c50005001002064002c1500c1e100148c5003481103038034213100032405000b165401a40b40e91400e0460316008808e4001c0c011491940c0c0d4490b07001c2c00501c550400510960002940002e042c0030810244c1c03c01408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 1616356 1250 1615106 1615121
    0x503040e1506190305061302030a0906051503070b0703050403020a0b0309070e010e0a0902010201021c02070c080309030a06020304030201090b19060905010602030f07060914060702010c0e0d0b040c0801020a030609 93
    0x41c0b0400d02c8419103410031007200754086401810b0200c0c0d180d81720400504c1241000d0a140c040d6480482808803480030743d03000d442c001e80b25000030000390721201e11203007a00c14403202065041d4000503003404a00d10420107081814401d040450609860f80d000950031404c0ea00f05800860b4080100001076800f040140000c00150404182c10b50400a04542440c0010030201b00a919101c41e030003164802d60446070301e80304084101d0b921102e425040d8001c2d62181710180c035440d03041840032492078000310444140c00790060081050070303c15910728010b500001c1040e825035590340c004a010810001d403c030721404040540700b4041e1f40790184042120b0b5150040a0280d1070000180180358001003180d8500308503008841e117614043c50310f20007600f60078800901c101c540050010100900140d0107002e128250001e01010070800d104a07500d50b8440702903a40203ca12402c80d01041040100c1c3d030b042030040c01800320a5485140b0542a60300c022008000290b840c0c00410a00780d1070301c00c00c01d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 1617606 1250 1616356 1616359
    0xf03010e070e0f0a03030503090703050f0a02010215090c01120b0303040902121f0501110c1002030405120a08041401030f05090303060102011a0d060b01050409060303020102030103030e090405070b03090a0503040e15 94
    0x10000e0001c00115a001315140001018002d000010544600303003009000011075212045580c03054140799415240c106a020413809480740450101d0750341c0c49007a82c0f5200350031000040c820018180011150040c1408a20158070350300c40d859003540c0c03010f01c02030014045c40d00000d81c5c0d0305543c1803540d80e81c0c1401014452008800e442c07140b0b100c0c1142c01a641140c009191240c9500d0410040e10f0500c690000d0942d8001c61900580c044150084040c004407101147c11500002c1c883e0000c0d52203800eaa4001441e05200b0041400b2290300b4050100c802103040c500040c004101d00d0705102158000d42c3c071402c150b800841005207540e424041c807210000b0380d0035005c4200701460045554400341d00341c000d01c1240c641000c94140c3c0d02c60010341e40100103200c401d0040c10750740e08002e8001e600070700060700051a1075607180514180703944080e0185a0080050540f545440c600010313540016204400c0c9025107003a503030224000b00050005400b03160303c1606a41010f50010405464095819 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 1618712 1106 1617606 1617619
    0x3050f040e01120b01080d050403061505060307080604050601020a0b060607020111030406080703050a0903050901030e070512010203010e0105030d020706030b0307030f05061605040f030201050702060f03010e070e 93
    0x103d05024103c4414079988520f000e41d100c2c2c07804042c002c0800c0f8100002c0000035059402507104290a90040300c80507100e80010f8455441a21004001079151003840b541d40f40c5845940d8015109000500c520000383d03940c0448041c00500f2188580008a032200542e409094080b083d010f400381600d55039620340b10040c00480c800e07101c5c0d600203481c01e4001108a201d40c407031710540c96050b4981c507080c00031040045001e0500c1c2c0d00900d0031030040d02000192a264003403103036005958000050780305c2d03060000391100140305030b0001d8420760284070441c0e102500890910705072407040c0340101d58121442c4c042881c2640a0340001c240b042e10403038920901c2030204582e80110201c1c040300114080010f0121084d000e14080d0300030031100d1110030001907000703000400f40c0b144041c1400e4182501400c02d100c140c1c000340c0c0003060034055070381048003142d80443d440d204070030102c900 = true := by decide +kernel

theorem cover : BRFrame.Cov 1438856 1618712 := by
  have h0 := BRFrame.cov_init 1438856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1438856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 1438856 ≤ n) (h2 : n < 1618712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
