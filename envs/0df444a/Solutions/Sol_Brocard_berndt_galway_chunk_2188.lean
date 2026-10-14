-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2188
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:55:39.462039+00:00
-- url     : https://prove2.me/submissions/d07cce99-21ad-414b-8d28-64c63d3680c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 393345323 ≤ n < 393525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 393346573 1250 393345323 393345331
    0x312060909080711060c0a050a0201080906060d0201030b01020102220801050c0301060c0210030b060a020610090b011b061e051005010503040506040f02060c0304081006080708100203071e050a08 85
    0x1108200351807450316490150300c100c01e4018651802110001c070309940e01301c1942c1e4554003a00882e6140001c81c07030190396a0640c1e4030140d02080e0003100290030000002007552042a0207810015800b09950064001e0011300d00002e066540900c6008080565000f500081c404100c80c0204400c0c40c1c1b21003242104c03409420329500c00380c10001400b82e203030400484003005030b0541d1500b5200445d408210300801a0b1368549501c010700145d034660f2305500040c0c043c010350701c1906940655540f100408200e400b40e04101d40458030113400020303240180341c141e020322030068001007105480392554100c4413100082074080540d0754014460840016513224004c2c290a00300149075003425103c3c40e41c0e03008024001803e00b483c0301e03507100454561205882c0204c01e0142125140c0b511202000e480d0710b030030803002422070700d06a40000e80c19000034100080f106007070042c140b480000d04d080c402942c4010300075414030000089215001e945020440854542a51003c2c1c45501c000c0d001054040054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 393347823 1250 393346573 393346589
    0x2070f0501050703140304050a0204060909030314060d020114190f17040f06020307020a050f0102040503120306060a1103040f0603020a02010b0406150e03241905010308180d020a03031206 82
    0xc40f518000035044500b0314200b40c1c4a01d4203070788a41e40c3d80703403081c900501a54002d40180c00e00c0030011f0b006480b608074030789042c0300741c400740001c05e01c0400110316100704032005544200c4071040800954090710300c00003003484d041d05a03490240240e5022048482d5201400000784060030b5001d0310039845030750801000d560312001002403c0588135060315010014014185680c00030201d0319103402000030720399480d071000c140e44040a01219880c000c3d0040e1181c40c0c040d014412604040b180000101e91140c44000c1c1403c4c149142540c080390641c102c80d0405115110800c000304419041610010040c18541e81c0540e64407a1303020024290349031109054004d60500318280407c2d1180200020b0150451402c0300b24142e0250000b40f42c610310b0a0041c541450f00c41a402c2520800c011240c8240c42d04206503000b022203183d00000c480017440040c0042a091007030000025442c8060100398400900008c90102c0c26000103100346116882180440d02070072080d402d0200314001e605c000c103941 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 393349073 1250 393347823 393347827
    0xa032105030f16050d0c0e2b0305210103060207030306080f0a02010302131d2505180d0204051602010b24090d0b07030c032a0809071502070f050105 65
    0x1c081420b00705030000d40081604200000c0d100d00c024810020744a400d803a0703881c00d22082d118a0405000e000c08005224040d030b13043c00c800c1243c40c06000d42e91541140030a03000088408c1600c0c200d40f150051003115400104400501800304880100d00740030710300601006940c5c0c10b840ca0050201d4006503c0016180c0098415544585c4003141da03510994080c2800750b0354001c41e100b8440191440d411460601c0202070952100200c20350a003881100c40760302642160402d8140651040f865003000b0000880c20031100306040e64075002c0b000e1105014083d410703818182d034001001d5400480d8694540f4120f05842c1c01240d41c24003817400d0f41d15050380d85082913104031500d40d0013048907070b001e12441200080c4120207a2503201d4400d242c01e4100000c180e6a0810400c0100940f00f03401c1da5900090411034030005801c0d402420311480d0b51741035402c22101300d01d09403d0750704100091071258540291507000480341003c0020ba0511002e99001e080b04070700f840300000c1070200c1900172034108801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 393350323 1250 393349073 393349081
    0x81b0601141008010303211d0106031704050d060b04091403071208090a03050c10181a10090f0e030a090611010c080c160203010207060203180f06061e0a03210503 71
    0x2007035180c12801300d03445c0c44c49a5500b440e5004001741400402311881e806810000c02803000c019407101c02a01c3c4540f000300e407842040c207031480c60b034001c03401440c1d40328032031072002400559194400c6c85102005840402c001400d42c446010200081e005d4400355000060303248200300b2022109442140d05d414491000d0a080c540300380e85019a040040600c0000241e58942d1241081605020001e9010a001080c80c814404a0880c910079045403c1c90100c0d29065150788804402445500c00e80340400c03900303250010140280030000d26003081c1c9581c51040325102d180a2000302850031740c9494100b03080d13181c00001449804030400d80d00103649414810200e0b0b036845034a03643c02591005400b612064440c58106888041d070b4002941584009500320810280340c025612a14151305072a0220f26aa004961103203440c640420701c540080c80014642d1900c125240450406804551034071421180490080742c00b682090f44c084030b8082a10101403c10844078546243c075182041c25810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 393351573 1250 393350323 393350327
    0x3150b0102071520190b0c03040314160f210513050d02130507020601060905010c0b0402040f14100311030706141c1401090b03010612081b0601141008010303 69
    0xd180060740007041858500c5441c06402010800701001c030311001d07a400010314003c1e8210054001d4002c1b140c0c0308071140090b40903180c00c0c0c00c0da032140d13070907896600c23040391b40c4080e842030769004940c5d151407401c6d50303504400070072025100e07404041d2291110564018080d006540813002141000f0200f2000f0080074001105800401d02226020f540310800c82c2c5240c800160000c1c41d4805031400d003458031041005ea143e000405a048914945604404645880044458000e00e0001518007503400c03010400504190340304035400e009507440081e0442e82c0f03083c0e107240c44601362404400500f003013209106004100992400d020000c400800040313140c0200684502c210524443c0e04203004030303000900c3c4041c40900001d0504003c01007092044404c90700c002108207005200c0c540d80703881068031003800d0510030502955152002c00104042030781d81c952903540564078000340022039800a54505100704081070182002c6401d0301480303030f590341c18030450030360759800380c800c05c081000104007280d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 393352823 1250 393351573 393351599
    0x90a0519150f1a0a0609051e10081506070822121a07030b091506070f200a08071206090506072703030e040e01060338090d110a020a03150b010207 64
    0x6d0080d600117900400c201d1500308500303000c11846400c1105e009d000307113030260301c1440355110b81a80c0c00c3c809034030000306041c0502d601402200a007548030400114100b9496912000c0310488100d40040c07910b510f881440d6010400c1aa0031500c1c03c8103202e41e1800c2d0241440c802da8801c0359450104009000d08000030f620500c0600074684000400a41c844c1640703030384007150a015008250300240502502d451080b20f4081d8003901361032014080390801c20728161a019084500e404014401c07a030410142c0c00641d10103220840700782c0e41e500010000204140803843c451040b40c2c94400b20028042c038803500d142c0540c04812100075151206000194209824244603402030310001041440740c8000360051840740c001424003038001403484a0181c48810708a2090407000810030200354032620403030795400a9038019100c0e00058000c0b841141704000328040c0c50784100450701640040d03008107d45903410342003640d1004012000010080c1e490017161901c0d03100f032004150300383c901107a400c454 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 393354073 1250 393352823 393352829
    0x40b03120c1905280204052404111b0a060e0706090b090619050d050108031803010905060f0c0f040b0306100806030604020f040207050105011409090a0519150f1a0a0609 74
    0x140941002d541e0000005441c130f0114254064810842c038180984091000640458074401d0311a042811a206007050302a0b01c0b00501030011640c00c1c6801a800742c600140d519181014174810501c40c0700100d60f050180c80c2c1c3c15040400500805810000e005012034640d030402141d480c0d0820040e9402c0d241c00e0111440c804a602c00804c0048945108440c0c1d40300e80f03904600a141018001305007490003100a0100b5031048098480381d034160024542039505030700001d40960424000901c032070601700704c51035001c4581c02c103c0303240030054080b00304070741c00680040f024140080201310443c188213208a004d410141003c4e0382d00d15041c0006540c0e204014802801065420030000813621540c05840070b5a0f480300003442950b03104c0c210758013410b000402c1944548a034101080c1400000f142e9000c3d031503002005400080080700c2613203a00f80300300700119008604c61304414aa24103d1082a0300e2120288004c50f00b10307240c03409801c41e0f04110110700e1146103d50000c02045400080001c11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 393355323 1250 393354073 393354103
    0x50a0501060f050c0607141902100501090e0a120302070b01080601050a0e0c03060d030212071109060405012103120e0610060813061a0a0f0e0a140a0209040b03120c1905 74
    0x18034000540c86007c0c1d070203022070142c3e1820328140040c0c025500030a00c6208441710711030401541c0e030707070300c012509443e40e1103030f183c605800c408040004034445441260711400c540c03c0252034402076541c0c440020009074000c00035504101c0041c021031070302145510040c030403c80345050500b0a401440228800644054480d008045903d004c0500905c40b90105c00c1c1078247c007035107602140c18a0800c01606c0c2d42680c0c450202e041c00034103945001e11805042e40d00c0c4040c1115240c00b070f5407105040451810041e000d0028101c05030014040f24042ca0b0341d10490b5030040c04507400c5c07158a1100d07500b00d03504545d0502c00e044040005403a030700c01c1440440d81e002030011481c02e04260040c081d00351a05035141e0018010900403881c103180000000494150a180030302c21390f116000d03582260b40004404542851074030216001c1039054014101c4448001c0001603c040640d0000b80780c69031001c54810400c0011600c030098000038071900c0c6508103200c0c814108070500d82d5400351100749200344008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 393356573 1250 393355323 393355337
    0x31e0a120506300607050d060807081507030207020310091b051f1205090604050f010c050304020f030c1e0a080106031101031d0d020304090c03020702011205061201050a0501060f050c0607 82
    0x10000c0400b8890300902e4043c019194181403190000300254022602910942d0908000080d03102000030154222043d24010f4500d200c2181e1212248120144c0900c04140d020300c06072000d69018081c40c81c0c0310010580011b410705c094a00218001c010003c040c03911981c80808000e00d0f00c81200d45031070303403400c1604180010b0707036140d050318540285140d1002c0300e0724000030440303030202c0002d0703090044d401a021140007807d8280240c1c00d80e5482840e03600000d800f40f0204e001414880c2520003030701c1e0028150348062403c0b802083d240d90a000c90b031800c02040d640d100e181824070480c800090908480248010750075612804c2d50f915038083c4079410551707586641145a0240001041801d00d910140c8400100d0700740000d42e2900180500c4e1200707490906c8030b81500d800b078400c80e1041da80c185c44032a40c80c140074a0b10700041600412403500a4074800080b4495082841910702c208003017600011a541000c0d4010038007450040c4d00740a200c0100401d021074400003442c02d50100003440e040d5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 393357823 1250 393356573 393356629
    0x2010306051f1b050a0b0108070f030c0605250b040312020708041206060512060105010f03060630090b040b060f0d0620040603020705120415030b03031e0a120506 71
    0x40b50710b0b1144400b42c07441c02005d81071020041e410f039015040307402100440d1021501c5000402d0b50984a00c00105504101c80d0308001039801403014000e039000544860007054400d0112000f03007440c20000711003c4c503500e0100000c241e00060300c8a03999100000071400d0851a03a20400544540e0003180b860441e0f080d101010007110350001000b4100140c911902c1c0c040044500f6a1464203001d400e0208803800308403044288680b28000440b0015651035580d8800ca5401c803862440b5480904006104115104008003003401084911403060807100386925180c20003022946000d040e203032180c4014400b850741c40d6981c07841114140c0d0494000100714001180040103605401000c3c0070016012070300185103601540584403060140080d900501d02c00400e405280c17085001d11071703004480c041304d9103600b4840d078415050001d003d01100c0c03400e032011000d400300c0d42d511403c2c0e03030742c6010001d405181c0c154031102007400d22040c27a006001608042000600700140d0401c58032101c2485200a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 393359073 1250 393357823 393357857
    0x3040509100306020f0301032d02091015091a0a051c02210411100909020d020c16080f03030606090405040614070f030b03150109020a02030c0f01050402010306051f 72
    0x1a4001e5601c443d085540d4180a0b40d5005a600240b105031820b0782882d00c0c9105000100d0130b04104900707007072119142c00c41d0f2542013003405800075000317814400c1c400720301180c21403505964421840c8613407035080d01d9514101d52280e00901405103844091414000201450b410034152401742c0071000a8101e442c20b030411000080c06018810000b400c101c4407000a004d02e1004028000d038014a41d1080c0c100d012002d10012605c0c0356045800625000810010500c89031f02070400c5807001c0c40f0140c0781c614500c404500d0005040e21480c01c81002c9281084050400c22840742c0c4607030741c400503605610b04080020500c2c020f081c0414042d94842000a0402a566108801d565407031161441039050a10004201c0140c610380840070078074003266031016180001d0903029002410012415a030b09200070303d000380d00300c40307042001e6100a101041d5100414130074450007008d9003000084500e054000101920060382c00203004200703040e0f81031044c50030b019660000007043d0806006c24650803c40e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 393360323 1250 393359073 393359101
    0x3080409050414010947070c05010504050c0102010608120328021b0706090311131107080c0105010f0302030312270a060b01030b0102071208120a0e061803040509 71
    0x2d500d4480d4a020031800c20400c401ca01d45550412010411415850191078030390040d86c0307205076039070840703d000500c0c0e254501d17840d41c0340d841103c510b0425000d40080e5600350170342d403083d14210b4490300510191440341d60f091140e5030082c01e10000508400c0d030301c03036030a007064440034000300034840111220340404c5040106000c00145c1d0213004540e44c1c9807800c80035200314941848244a8000c0590000c0c05034400e007000e400b501e4010b41c0d1070b00c0c0041118100802000c2c0d4086509850340ca0342c00341014810940013404c1c14030b001e08012603581d01d040d0222400c503401608400f10071070504e0003e20161700c0010507510065240f20321381020380c64540c25501300e0344402d1030300114041d100c0c00e54000940d003c40d110410710701c1000f00380480320784c000064080c1ca500314841401640300d100100288801c010030407100340d0140c51a2440c040b0102900c0c00c4600044501c2c0880d9902c0b40000d05031204100000c80d03200319000c12071034464201c402c11a8482c81103110301485094008040790b159101209 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 393361573 1250 393360323 393360353
    0x50702011707050a0908070f0e04110a030506150306010e060618040c0903020909060105090f1e070c140a20031c020609071707030f1e03030501050316030804090504 72
    0x41e021589152900b070051030f50340003c0c2400005981d4410002d414a00014100161403a070264144128240111075810318070003803080d901c000c1c076242814515180d404046000d18001e03005000549810700b001b00c803036211900c2e20382c0a54480c000400040d00801c100a41200c8111002030ba140c001d0903d0704080300740d2104c415409440c110003045d4081c0c21041d0744048920130b0307500c003900313640340740200d038440409109040d00412080b001580d0303461030901b2150700040b4464080f0b10380101e00c1c0340a840c20400c540c000e000c2202c202c020000d00c51103828071440010880014030035006150b584000411919503051005003420250341d40d580d605110082481c0406270100d0300b41a65640029503a20003a10340308100e0040480203d0480d4040040da038101c1c11036130040540f68910b986a440c0841c290f44c1c01c0d54034062094a81c07a2040c007120140d443e0600954010540c0e505203001c060904c90701c110401940c0501200c2040021003200680e012a00c00040000307142d520740c200041110540b00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 393362823 1250 393361573 393361607
    0xa03090b07020706030609050c0a1809090f0b011211091308070f0b100b0403170412050607031a090f06030708060c03010911040503031611041a090f01120305070201 72
    0x401c0001e41c0d00240c008111407055506000d5070b41c0d110007203002c4030170030b80e040c030030221080000c200024024481c000d4181034070042000001c5d03544070688100c540404044a40c0d024120b0306406015200702e1550260404103510515811180d4401da51b20a80c01c40c02c5004911240015a42e2080401c0c11008075801410580d44c0b10768a1610359088005890102c1d2070306114004908410503000d101c501741c07000c890b4024a4a8199112034284280080c49a40c4480041202050703000c15800810f002c5482600200420309045001800b0794000070354120b20911044004c0d405c0d0355070294081c0d04036003900c00d802034513104c1c4c3c001b1030300f01720813030300422944d100d040203200e00034070520011030488040c10420030100202494601462007684181d640c0340d48180f20b40303852400b0a00000124500c584072915074990400003103401d40712159811034800102a000c4400c80c100301024a500040b291180d03880d540c10003016040d0b00042d900b007e41000b43c0420f0903011a409400a00d148103400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 393364073 1250 393362823 393362843
    0x110607110304080703030315060e0a0303031a0d080c15060f2704080d060e0609240a06032003040b0112030e0910031a15190b0f070c0e0106050d020a0309 67
    0xc1c140a8060032113601d58030030b0010031488c00a0711510034041d042c0b01e124000c0603188280c2c90344d1000c07006012981c400340140d09120958401e1a80d40c0246a042144500085511826030202942c140200002c0308145a03010352304011060382c4814441007c980d040301c1c880000c1011465114039090700300d0051608030707422000d010034018070740c0241841100030035003400000d0311150300c0032044109035041d903003042010003c103140600380c55011340136400c2d40200c455201210300002c1c980840941c00b0381e000c0395a806420f02404105d010b49648042511001c6c1e00d94103260f6104424130105100e158901900c9006a104141c8101b4036550182c1006003841c94605103000313010240725503807000300c40c00a01c07241e140c0d40f2017050b50a00c511861000c0070700c5c2005003141007031107840c00c00304c0d501d800c003158800ba022490b046d01e640a0407580d03004031065501c032085490200c03c2c041480e0403010311a424000100a019070182c100c90512034032103400758a8940f40d601c158094400050028030084007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 393365323 1250 393364073 393364079
    0x51015020106091a190302090a05060102010e06180c03120d020f0708040b0406080906040c030212034e040f150f0509160f0e0c13090b101106071103040807 68
    0x403400042804c400215450311000750041000c2011420920000390080c1390040040c1e89420f660740010751000c0180004a140300080c960706052210883d4081e650b00328440300c5c000203080803c003110400506078014030400c0554004030800d030046e0503200981540000d12600100f40e4007065a41d20740d80501c141e41c540d0303241c100c9620550402c0c040c070000211500d00003282200005038860091b40c00c00303401c0d081d0034110303002c0c0a03443c2c0c02400202c1031444100701c00403981c1c2d13001c5401401203c241c106510b1110000d05240181000c100c81420400d1813408400740012800c1c5055400c9a27000d50030444500103450120840f0081e843d00710000e502d4141d96010303002c101e811040c81180343d0000d41d600c2002150f00c4072001046801003402100e0300d0038091200d00d4100ca2002d42101580c00e459040080390988034111150a420984909448200785213082c1001e00401002a005040031104880603c0005982d40d8006000404101c160703140383c05902418000c58001d02403002c00d860081e03803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 393366573 1250 393365323 393365351
    0x40b0403150606120c03020c030a080912070c1e0b120406110316030b062514010c140304020d200a120203071509091b030f05101502010609 61
    0x1062000303079080c544580c1c0811400307126119080c00c1e2000c0351580390388030428190400040951700206020300d942002200340c90102080078042d40d841c84c1d52a031f4901d103000503e140c20f0000d102da5441e080702050000000160113650f00000f43d4682407240090504150003c000031f05203584113503815007000030b10384000c04407101c040b803159000b510f060000610003000105071f80b00c203c820002c0003000070b94862485101c1c0c2c1040c2d0321100000c0415042170341c0d500001c045506041908200b80e55a4a00321081101c441d100102d001040402044408c4904038090b00321407403480c0d151140b1700c00100003421980c8100c1131070300031a00008846030451680b4550104c15107000c821910070000c1c5200015002500040c40200c0d40d4090058504289001e1000c0700a4007070182c0f00301030003001c0c44007140707584140c0700701c07401d202000891320400340387d101001d003c4800c02d0040a0010f800d00c0204600190503003500710441d0101040703070b001545064002c034011718290300100500c504020500040c0c00c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 393367823 1250 393366573 393366577
    0x60f0b070b150f0f03070302040e0a2001080106081e011e08010e03040b1612020105070e1c02130e01050117012915043303091e080f040b 60
    0x500c11041e00c40c0035281c0340d058084204003000309940c0a0801c1201c2c40403402e01c01c02c41500000d014080382d003c2d07500ca42c00201503414002081d6843d6011048210a201c11460400c8041141103d940b9070008690002814190705002d40381c02e21034024040b030515485945c01c1d640414526504a00c0b070350f11600e001440c440317400059a101260740f40040f801440610501b8050090740c00298039080c40e2001c81a11174000c05903100f4844046c0d034540c1d0105031036118075403180c0324030307400040d03145400c08000c2c1ca03031168150201d000d0070500300518460030410645115282c0c0448205a4020018400c0c60260072400b40c500150350030300b03000040b80500c4084030b85010344c0090081c000300d9151821441602c48025100320b05280c20700c41c003901c504041c4907030109078a4a49596140940b01c003420384480c80d400086000f05608070b4207d0503030400a02140c007000358103160500c0324040d192200301021510001411a403543d510042c070070004410101d070b03c1002030600c550b0321150785103070120060f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 393369073 1250 393367823 393367837
    0x19140f0d0b070206060f180903040803040e06030105010e1302120313030b0114150d0b0f04061202011403070903020618030f0a05010e030901091404061a130801020a08070f03060f0b 79
    0x5031048001256480c5411324183c0d28010020384104c0c0b00e0032801461f0400404058280c102e180410800824134420610042001e040900caa5251908040c0c00380350841e90140e2001d45466180d80a01c828100d060003001111034040391030000c5945501c042906510a454012003545100c42e4004108280104528100c0d8486000c0d88003000031030303040c00380f01f8070504040c00701440304000340740d41071580d0303400b10040c20009490421034201c400040b0742150326980042441924021004086681c0801861542e0004c7d43e109030640c01d02e846c0242180b061741c00003c0c822000401d0218070050f1110070208c1024000781210101c00491041d55110300d641c0c070044e00ca44d42011120001c588001040762618101a5142100e6034a0300500e11010104d907104107074019281c0c0d4000603001284000401e4280203a0045551200c20f01400708103449103134041c01d102c0e4010710468038000d0f040003d1950000c1c25081c108071284040c03508400601c3c664114501c02c5800e010041a0410b4041c090940 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 393370323 1250 393369073 393369077
    0x40f090e1002040f090e0606091b120f18120f07060b0301020406030e120307020601060806040f0c020303060103060905090d0c0206041502030a03050708060d080a0216180b19140f0d0b07 81
    0x266421207100c10b0307d4001c12a68180c2000e0f141c40403c80d100041501c40301d2408103a0101801e0119400380100c03290707003e5841d039081c45003010a20107050500c0128802401d4580c008055568124041958600030104002e14500d008140c900c180600740d00840c0d00c0400040c000c660b00c50b101d44010b03005208086001d561845460440d5242d01a05000ca0340915095002481c090b803800c00219a801c0c1c00a24030354000b91144907401a03c4440d01881019120745e801a40e04c03840d000000400700c4015a0000264904000c20300c01000808206400b452076140f030100b00c560a0340c004a4643c1c41207070700405907220350f056030070080ca074003101520328445140e4050100b40c4171083e045500443c10354103558001d0070340c0b04000018103c40010030400c4400e005542c94003940c2c908980f52007066500101c3d002114541e1258440da00d4410a8055201110101c060840792081c0c0118010240180c400e0b035000c03010000c0c1c0554803450f0740c3c005624014101030964440d450164800107040d1a2640 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 393371573 1250 393370323 393370331
    0x6030c030303060f0e0402040b1309030201050610030c140304050f0703032601050612101d060301050a0501060203030c070317012303071202061308030703020303011802040f090e1002040f09 83
    0x1810b44c050412a400c4508001c81540a500e42c0d408000080c00f500c445160302800d2003d4140c00c02183d806a0152240070360000103c5183ca42c05104915004242d04803c140c98102100c014681002210310441d000c071030100e449949034a86140740020300e40c0703a00413034030a40c1800000c069119103503e50004e03800766800100500003520408135402801901c2e440f00c2c0520148140c0030062036826844810311110f00d13507031607a51881002282e020700e00c44410f02d50803010006c2500b402d0190315088000303640100040d6141c044025120f00000d41a2840d1040008400080c5031240c11140956012400c1c2014103503914079600c01031110716a82403407000d400c4c01004501e850081403d50840350100387e4529550300a5080044941c00070401c8114411100c0010070a44401c00240603068071a4004581da9411f0034a071000c0004035410815505004000c01d0140229106502040b00c22646002c1511400e000c2c150341030003905041d8074000ea00c0450b0000c0d541c01d240203c00101d41d01458204 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 393372823 1250 393371573 393371579
    0x50a0b01090605030a0305030c090a0f062d02070e07090b03010b030601030e0604030207141212030403120b06092b11011103070f0f050a06050403020c1e03120d0207020406030c03030306 81
    0xd82c5030545d8850203008514144002440d8940010080c40c00100050600c80003070f4a85400c0008046250013402c0010804d041042c1d4580100c0c80d041c0030004400034114152841440003542c0b2005ca00640403207440c14008a11403501a02910028081922407140c41e03684503811154541c0003121424000f9052036402c2d4000c40c00801c0700e43c0519055405000344078140b8a155445810307a40f4030304e401c10103d04c00540c0101301801313842d200042001240b1354905084c04e0051400302c40b94240f03500585807098200740c603605c2c81c00b16648240203440018281c00d040034800400c405108a06890b006030310721503820030034640030100380180b0980300c001c1c1003440c40750b909a403800b503050010300140003030107250701045200c014494118403e00072140580c0e05590b4000a652040d01c003140580d1000c0c40060035840c101014900c0e81c9404420b4056000d801c1c0c0001e070703551011012001c00d40c01c001038007120051003601181c82d5903402410900000c1c1e41c0c2c0c50306452b40312907403000f5800286401004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 393374073 1250 393372823 393372829
    0x30e01050a0905040e12040f0501030e2e0b0d05061b040e0103380f06040216020d02030f030f1b0115090f090b04060209040b09090d1b050a0b01090605 66
    0x501d000740800d07614419080c0c245000d100c010030401c455018188110300740e072810300307826000510180042034500706450f03240000150a0355080704095000390800c6007100d0508400c65840b070074411041d07088881e0032183c10b1a4074000e10761100a15007080d0405111800e2040014041c0d000700840e100c0d12005a40c5201003241301d014a028100441e0380c40001000880c1400c0d0024070080d139142d18144020700500c46413000c4040c00d200800d403c1049030100a140804100d2140e03000034182c07020b501e0040191410700450714102002442011140848070035134a00304805c18080411030308580c0c0d40e0b0000441c00c05d0580042c15040d1003420505c020403e442018080e001540488045640c1210300301700090010b480141c0000003900c4d903585d600307404141002e41c4903001718007504006903190300e60f200384800c1c3d80c00310004a0142e001034044c0100d0a0000801c100c07400280c3c5000c1613200e928440d440605171912101405500c1086603100500517a020540d049800c42041000801e94a2040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 393375323 1250 393374073 393374077
    0x3081509070c0b09070e010e0702010b03011a01051c0c02030702090a0c1e050f13181104270509070f061e1d04060e060325030204020a0525030e0105 65
    0x980c001401c2500c54000501030b00003213900101e1140c2030b542c8094861454448050099112680c1c0015000078001425020b1254103403566055000b4880a030078070340044640600183c5480c100070380001c1e980e20000b00c501003040c12010080040c0103444815000a640f9048035005034483c50b44100426a81c800910441c00d0180980c0c4070030200075130704003003070f03040e041d40200fa030060110801c0b80008201c0340c0c40090903484014010540043c0c10201c4800c0124210f2025140c118902250001111000c000b907408035036404002e403c00d00401c504079607100c209000e0801065003400c092101c3c81c0404110807050707800c4405100c2849542e4002140e0380c01c0d0000b14000036441c006854600d0318442c11f00da4070294a038805186083c9445c00105040320400d0307100e10b2000110f5818014145024007206085016000c10130705907050000100c03a07070b0021884001d120760b5000a259500a00400a5800c2508101048100742e079001382120410180900110000b1b451b4114030311180d070090007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 393376573 1250 393375323 393375331
    0xe06070926070b0702062b050f06010c0204021b0a0b060f0d1502070c08060403020604060506030304031a04050a0206030a0c02060f0408031302030c1909060603090b070c02061603081509 81
    0xc0000c10710300098034805601c2400182d82020041061f500100703610000741c000544031f5118001641410806142111006055140d00a0b400c206201d03103030380d02003144d1820b15011030f00147c2d030f4030f050984030303070400d4144010003100d00036800c0440c1880080c02000e8400c00d0241d4490070381a41c840104403041c7d03950080200000701004442c0c1806481d540038227082407241030112041031325007001d64607100007103d0803001030340640c00b080104401c40c010533400c100250001c5003000c0c1181d6900841c901185d410324900d5003c400081d080c01410010110703101c1d00602110390741d050100b50032000d04064070f039040251090391701140960180140840c8695040f01320a401e6442e040c3c0100c40414aa45d4241d9140c031400e142000c01c0d540740404441682295413100210301c1c6000110350581f66194001c10901d40f40030032400205403c24902a4030070302d0f07490450040d00c6503100083d800c2c015048103404140e205524a400c0542000e845805500103401e22040c556810080101c2e50500315 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 393377823 1250 393376573 393376649
    0xf0c080a140912030a060b07060213090b0109120602040909051c05070803040b09070320011106010f17030d061502060a1104090c0c050a03020109030809072102040e060709 75
    0x242003c1c1d4000c00c0409590044c0402001080403956020365000030381180f001592242e40c0001d1058a10b8940384000f0028100000c5c24808000c207180080e01d5030886e48502032504070141608402c00417940c0c11100034000c54202040383d82000d04109030303110020058182810f880c501e10381c81050168007680c5209038820b01b064a15500d503516025282000b41580d0002e1141c140d000c0001420b140045031032040c4280099516031682e00011300e10004054400d043e604140c0041c0100034070781c0400e0003601c04550104100b1b10380705809926520611442e51485498448080307104079160200c400e00c100154225801519000d031900204d9203007494a880325002044208669070298002c92090030720b0341131598901000d03403911070900e6207610b400c80050b50358082e41010550480f80c5260042c1d101c7d8000c1c0301d803e0500550100500c00c00ba4001050001040d020086594503046102c041c00480c064401501b0301d4840540341c48041e000e401d02c100540805143c000f140c5000c428500070b000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 393379073 1250 393377823 393377833
    0x3010b0702010f020307060c03240830030901050403031113060e06070b0a06050306010608040809040b060702040c1d04020c030904020f070503070b01060f09060f080a0f0c080a1409 79
    0x550055039003003c540842400e600090250074007080b0103109031130407843c0307a4402107135400d642652043c4628480401c0007640c1c0203080140405040010740300410608241c000d03078251a43d00c6020701c032001100459241d104000b08001c8804410341100c1d010358869141440000143d156034883d90142d00020500215601420044e16109142c01a0a060003400942c900000c0d0744407014415011100daa0711140c69000800160808100441c010181c80c41d00c039a041c20a5620307038405115108850b880f59455818030003007556400c0031184107a500500c10041c1440c400b102030071161b54001e000b10000408400071300c2c2401c2c28022101e003410800c011b14513182c0f11404010080d00075101d006002142400303c03100003102080200030f01c90040d02c101c10a9803410400403c1c0c400030803c54030401c0401c940801640d50003000e01e543d20082c50426512a64407000d01000802200d1681402281030800d030380c0303070190011140c0740030342c04001040c0020240e41d0100389101030242c031120310a5100e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 393380323 1250 393379073 393379087
    0xc18181e0f020403110a05090c0325030504050715050f132c0c090a030620041d160206060d081207081806060a052b0c0f0b03010b 57
    0x80d03011011010014509009800d0322100e260100c90101c50140744450340010140f050180c1102040d00101302101d83c050701c0c40c100f40c04506454000362050042510100c0400c103503040d500514090750354088000035001d0030151001380a08001d071030503540d038051980c0124040d29200300b0300040b08119141c0c18902450204102c0b026030012070103040040301401e001c9000c402c145400040385c0c644803070218007841e190204c40040324014112404940d020018103072186c4854000104881e001800028403401418400c5255401e4140b820030f03210b40000d000c21070942022129002000f41110b85005270351364215402008190940c1a01603417201c00000d60610b0300e4090740403600e00c500941400c1c420050301e4110710380015a846c40104040e042004004040881d0035520b0524010050415007059004503602d1040c1d806094040c06c0c0c82c0074450382c0080004110105241d46161004007543c5c107092001d113030720250082500804003482c00003859842c900036a410396502111440c03030300a03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 393381573 1250 393380323 393380369
    0x50705220e0c07020a030c030f0c090216060203040206070611180f03071707410d0303180f050d030b06071101230c07060f1803020f060f0304060c18 65
    0xba50100e17800100c080700803000610507001040194030888058841c8030f01482c1200001c010360f0441d8960b54418020b1300484452000469811600140b0059407501c1d41e00102d21a44070320203004e4125424480010141304071940280001c1c9860300c40900c1480d050710400840c0703d829101240c0c164400c2d041030112500100014400990060885000594500c07200e0000201c0e02910240c680302d070385203030103802c0078800b522402e00b01084406040c0300d042d00000b10040d04000f400350400d982e540c086441c02a485048120b00d9800c0000424030780040d00e04103654040d05242807001a0030002c207801e40b0300b440815550f0300c03944964045030300518000116071461401040c80002100784040c0014100a880206000c2400001a0002a040a402412460b0480580350800c01340c0600c0060740c03400d100350803040d29070480f880095000d40500044190042e00c2d03c1712070b1150700100340010003442e079005410011007521081421944d0317522904a40c04188564a20f000003080402801c039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 393382823 1250 393381573 393381577
    0x15030c070210020d0e01050703020d0e06090d05030304020f120706030f110a020a0b18030f16170406170103170a090911370f030609050705220e0c 64
    0x1815901028246221500040c414501d403404010168109011081c41944d01210303100c0b0400c000e003001c62130f1109980c0c009595003d50044d0f0410003921140d1f404440d03907031038121038074007000a2070151301c20001e0408a8407a4402d86040b032080004004880107824040514060034200c1d00160511918251042c0c0141039002d040100721075aa221154030700102030b0260404105543c0101111601c0f803030721400f4860042c054010f6201c0a030703e0301e10840c1c4004101c8110100182071030780c49102c5400708882c21202480000d1102141c5c041060a1251200c098001ca964a0743e402040d0340d00500c11504080c030038000034144201408400c070400b8070a00082544248074504000d90a640b41c03031072400c941e4120f1240186110005131000c0342c00c01060342858241c0070000030840581e0a00c881c0000a0120004d2001e00110003000f1200a00940c441c400500038044103003c2441c003014000d0441c0c1c050440c031403082c278103094407400c0100082105400e03541d0034040c2158588481010b04125 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 393384073 1250 393382823 393382831
    0xb0a0c060b0409060912080c0306040e0c030a05010c020714090f130b04060c111c0f1403070e0103060902071a0c040f0b0a0305131a330a050f1503 64
    0x32646900040159403039074072401e40810700903440080c0c0a4001e02d031484105002c600f81c001002200d03014081d03841304500480b43c0001c02101c001408405131041241003140707140155a06003d1400240c05108041d00280000c11856084e620034a854030b240c040d811111044183e00141440005040d001c54800815040070082c42a00c200051640d203604030140c00700da089070083d45a43c84100740700d400038848000c082c864030203405000c801c55040302d62076806144501c20032580c0c4684400c0c8034001d0341d807024519040c5c0c9606d5074078507094401910000d4001304041c0000e01e4a140002c0d091594400e5600041e8031400800a00b025004800c0c2e81090103480c0039a030034020000040ca81c40d80d1881c44c0e00030140c80c00050b485610001001c1c00700c41e001012076051402d46c407a00c00c00541101001c488014010071402c001d5183e644000c0302190090b80402c0b0483c010000d1501360300042181d122851a04407814038200b41c07510300b1301000244425a0079000840c103804100d021442c94051640 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 393385323 1250 393384073 393384083
    0x614090d02030d0e030106091416030902090a0b0a06052503050d060806010519060207062a05060a060b0a0c110607020402120a0c05040308160203010908040f0611070b0a0c 75
    0x180d604103800190801c143c286290700414000c070400705841c1400e0240d000102020481040340030b4048000310301500300141900540d1a82e128604102d50080d401081d1aa4010b80615030310b107800d081c0480148445500c00e881004001e6001039120310a600b00d6601c0c5044880c4c80081c8110500b4000f0750b04642c4a04500303010090101c422408007620840004010400c02041203514141c02e00844040407000344101140f2030a083c400c0c0e44e000078446084078100d140c100140004040d03002c4805040c00b015811504c00c00400d4000c0c800b00041340c5000c0d0884034000c0104641d81d800005451141c20090720100300d14400702800300e164841483c800c18000381059180c440681d002508a900200c80411a4a41c2009100c0040da0f207200b415042e050a0070954907050a58131039000303034002d000c009134403624040c41040071900c0a400501882d41d02441050301d03a515840c101c2007801c594015880081c0a090b03e0381040030000030780c074045503140c034850761400103200412144c0c00c000d1482070790 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 393386573 1250 393385323 393385339
    0x3031e34020f0d05030d0b0909070501090509190603030f02060f160e0604080d26040203030403240509030306040b0f0604052403070c1509150f14090f07060504061409 73
    0x10104909100400720b00d06c540704001800301100e0100b107261040a00a841d441d4050300c1c040c007480e41c07c40442d0080e0392084801d03241c2070341d0b44504c1034a611440d051001240e4200000002096084003103a4403440d403d8007a64038a0361010b007400c10f0700108071400100041d2003507603502c0c040c4c02807001880c10040038011601d40385d01c0d40400c9145c086100300c2c00c000103001c04460751040500c2a0080090803083c11a142d1030305007a00029603c0c083c030f000103480e019180c20300ca254240b01e00d25a030402c842e0710a007402586001206181c4072b810403280c8078019803c1058210841c64403030007410b0700a03001801e00c0d0074a410901400410000b84441c41310140355613483c401280303000f201071449616607a42e4101035071154030346510004204100900d440782401d05820009103c6150540c0f9491504000900880c0c50101403002d09070380000020407a48400174080420b801146200ca030802c03a40498496070340d6404200c03260300c40c0c1c0c456000081c800507508000710701d022008181c01200240008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 393387823 1250 393386573 393386599
    0x4171303081c1415090933040c030c12050a0b06120703150c030501050603191b080f01060e1c020130060608090c01080603031e34020f 59
    0x94202c070300c10008416401004801c1281c004c11100803040340c40c0043d035100041c0e08082c200b030382e035940c0c621119170507103044604501c0e4a22050640e00c3c0619030700b180c02c0d406500b42402d05502d00801c500083d078104143c160b02003415010102c61605081d4044c000381104030051f00d60503388000603009135400b0b101103204048a00d0204105406540115041c074070360401d400c0e0500440300d80c032601c10207050030400104416640e81040e80e0b80b256080c080101c06008814050303009001010110411618034183c0c0c1ca1016880503080d44100c0f01c2146c40007099890701e206540030021031304043d5000202054030302900c0c00c00b40300c00c000c1074130604241100b000c418042840541c3c4107511002800d0038103409548581d1107000d40c2d0001c02580c01c010003181401904152240c2000090506001025001c60300c243c0b03003041240d1603a171040c0014801511100340c003000a83c821405034140d000449040050361900000c01003001e04032684c1030b03024010542c207005100e0410f49509900c4040d12100c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 393389073 1250 393387823 393387877
    0x1f1406100909091509140105060a060f0c0201020a08040f0512060103020d080711060301030f021f08010b1b12131a120901021209070807060c02060a0302250b0417130308 74
    0xd0441600c1043c0e80910040c0d08500706e82102e00040045200b02c0480000704401070b0000d103156201001460180092041800141c0ca020032000005101820020300020303103d03280d680c80d00035150121001810628455100c2e0b0f80d5003c203000195218220114080019220304010a5203a02c24288850b2503c924400a94207030000d134003e6450104c0401104111f181015510091400f4500007080c1d1741c031000c100030400301050082941504000844a61401e41c0c0c07400d01c0000030500e4215076142d00e4900401c000c54202c02503500007002c5541e40403030b00078112084006121080c0c02002d01f08291040d8240c0c6801c0c0103030004011b03540c00c000c00780c41c00043c1c0c5103079882003800c800109000c600d403007585440c084041e0b110f401000748000380d0000581d1548100c441d8803986107000350312416200400311001000408001d0401a50f9554804024041b94550310403406030201803100c5a1442c25031582e8800e5650b10000500b10307810620018580b1005030840c0309900b000c00501e0b0b8009607607 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 393390323 1250 393389073 393389081
    0x20102030c0f03061503090a0b1f050915040608030a03150b03060d0807061d1002180d0c12050a03121802040519060e0405060105060a17091f14061009090915 69
    0x7c42c2c05640c000382c010000b413040610138590001055800e0011140c0f60790410817800420380500c80c42303400c035072021a11041c500f6094504015004108100d41030341c812015941740d0003a850000030904042e250460004071a482d0000c482080040600c0c507901e1604201100d110080220344458041c04074102048403441981c000c0d0301541c3e0040c00c0c10054103100b070700d03101c490907920170307014010400940140b68880d094210b6040640f0600480301c01450f00b03100c19221341d001109002d446481d0041480300004003028194041e40b2000f607070b204846d20200544603912948540c2d02c018419103001410141d01155100020854070f6900000c0c0000860540d40103a000c90100c20481050005000781802128010b1200315010303803030b10541c40406044401e038011006034a6454070b0008020000c280700c1c005241d032003600c12001c0408004203080043c003010020604d030402f8000000c9a60400e94114400c4040b00e443d8098050315001c401009444030b0001251110411045481410b1040c09 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 393391573 1250 393390323 393390331
    0x8030901060306060b1e040501020a060b0303090306190b0409030807080403030b1012060914043c1a0f0a020a02070b04061e0c0816080c1e0c01020102030c0f03061503 73
    0x1d503d81e585d04540c590140040b02000c1b03241600101007004101d0381c0e800003254402e4903030144000c41c50700301c400e000078218000d101015400d0f005140070040c500000c7d050703252115400e42010081c2801c40c00c20b1004030740350054018040354120380810003407070003214610b42c014428030b00403c0c0900c020300855403800344c0051540c04251f201c0ac900a11400320f00402c0003078000d1400c104500206a02400004500948054803a100081140041d4dc240313408400d0110100001e495141d003e9514820074032071202e401b502e49008404190f40354854028081c6c1c01880740701c600b5299038440d0360741c0c0341c002e51000200f0070951040784400034048a40348040d00007000b403030b1200c045080c440441714007000d151160000410440d80b904500040116051340c01200741070b41c0075181504980b600c0c4405205205070140c4910444c0b107031812145607400602c103042800c1041d03c40781294071005900342d0000355604250090140b10342070f1550380200c0030310342c006001842e4618036440100319000d55882030ba = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 393392823 1250 393391573 393391589
    0x303050c071b05011d0d02010e03120f07060606050a122d0e070b0f0f0a09051c02030708010b060d0c1704030e041505060a03091112070e0903070f0803090106030606 72
    0x59400c1015617017100715242103048021400700341080b10000140c62a0038070300001e044c0700740c07003c00a265480810602c810300011450260351000081f44010980e003016104840c4d1600f444000b251040c0b048055420003552600c60007240010f0001040107841c0b5004010000d6942603840301441d0500000401a40c40c500c00008580c2020004207040400076003002d25040c1007003001c9440003100e00120380b19580708200050300e50040080c12130300510349910459120400c2040026100603684200e0302a038400c070200e0f12910340d1354403200d003038404111140d03070701c0352007440b10081c5201c80d034202c11442c00041c0b8202c40200f00720010000884019a4194000b501c0700400c0111070810303104104030b9054050424001901e006c00141e150b1240003410000c05450300f0b10721007000240407000d040b0681c0140649407145c41c44440c0382d03607400755105441c00c0c044043c010400442005c01100d0100d50031207403000244200d5151042c443c0d00c09010000e203507503145800008941c1600c60040a08104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 393394073 1250 393392823 393392873
    0x62309150f06270d050304031209091a0109050109060903140c09040804081902090a020a030e070605070c0b0301080307140307020d1a0612061f05040c0807090801090f0303050c07 78
    0x4480041c0f4404403000880b40104070211416011500003c00c0d58112584035441c0310420490700002c40b1000fa86500102c0d195060030178003040c907845003003c01c03451403080c5e81d542c262035a6080116030700d400310300c6a45c01040b80c200061002c100003420202d0401c001c02c1c00c0f074400036000b0003c03030180f050444041d28100408981803016003401e20001d111281050540313000e450050300040c0131403201421140c4c15960000715250b03254040d81003070300d650111005640b81c10750b42d400041e09980c8021030171103003608040e8002c501000b801c400c2d60705923072840f40118105106541c90414403055a4980c403502c5c4001e120100060b5607040c03039049940d2007803880c200140c2094143c21b2004038040c26540c49105031400020a0000018203540e00041c5041061ba15440211800300a00d03006e4101035003007420900d510030380342d07005458280203030201da07695040e0342e0f81c881c150341c00c03540d8607400101455920041000464426001240c20940b0184a1407070410b143d91020215090300e44410125242 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 393395323 1250 393394073 393394117
    0x3030a0804141f1d0f0105010f06030203012301051b070314012a09050409050c0a060908030a0e01031409011a100c17040305030d062309150f06 63
    0xb04888000b1800720700002080c2c400c000d068a451001e07400410382c01101c0c0da4244102090108072a0b111010f07181c40140c134000d080490310140a0842405801c000c0151110001002d41c032a01c21641200d004010b0010098078051980e401400d500c050700d81008801c0c000c801116481a03440002c88000074000c104151840c9800004514500342e60441c0b41d25081c540b0840601c402c0f050031003c100802102d10030b50001c40c0c1905d2042c8981c2103990071514100d82d0008001c0c0009101d0101c88044079130094540d074a001c101d03280055400b50041c250400d00c0400341c85401072455403048041410b01080c0080ea031240025852000c0768481581da458507000301640d1003c411100e00303920f00391441c0d1440d1f00c1035480a801c2582c40e91000781018103415002c0c0e0210409819103000d150300a068940c2c8468036403e05020b054680141d850303200704000020f400d00895004c014180c80080e125421650307501e80030908a04507410318039000740810b002001c1ca40d40748070080559041550303020401c013003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 393396573 1250 393395323 393395333
    0x10e12150a090c0605090f090a110703020f1c09150903080706021e19050d090b07081b0703080708090a02091e0901090506010b030a09061b1101050f0115020a0203030a0804 75
    0xd45540081e040c00300801000741c540c1c452004805070307c6002d603550121515000001c400400c0f900742040b40b81000442c00d00e04055012902a21400c01c110868541e00c120403100888840c5107101e50001c03c8400b0400c021410882e285405200a07606144186030390325100e4040d80ea00a00c01203c055500241c2d00a50054281340503080704130000e038903070900c4400c0d82126141c40310080010140400840c1c2e01001e006550440c40003a9442180b0322681d0825040c00b402440080d80c100384214913801015001c1ca062030f0a45a49980540d10302c0b04a40303400d80c0599018801070b05088490043d24886005a115000030601504c0e181040d94808480c4000c81d00d0603100140400c0c1c41a41000c206c9004564009441c3c1d0540344d81c2c10301c03590b0b0b946807a030b5020b008100842c0000c00d070350705200c0480052413440900002c0b001280c2c546003800008040d80c1d608a03401190300300708603c0194010b0244a036001c1902800342200e0040300c48a01c0f071a00000d146802800521000403491030400c41080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 393397823 1250 393396573 393396593
    0x6071407052e02010e0d120609140702060106051602040902030f010e0f0d0e0d0b190c0203030114040b01140f040f0905010f0503070807090203060d020909061f05010e12150a09 77
    0xc0c0620081005601500342140c460303072030004042c1040b880d005419100305055000b2001401c01180801c500c3d018050004071361040bc6900b100540201c400008502d0b00560461745035505803070320070a003008183e00f084000c1403400e90590b098450000d1640b00c001d0f09110301000000d0707020042c480c1041e6910100c0c944044050b0391800c01c10102d07108545a101c10900c0d5003032a9001e8076800035940c804840c07201c0c0619001141455504001401d00319030f40100065040c1c4000c20360b240c00c1003141d4400d100036208002d07421400540040c0c000c002c0c0c0c600d0000900124048004814a05992003e8100054071036401120045658400403c10320720581203800062100790083c041036454001585d44070382c078510503928550740000004640d90345010310070000e039900401e1400725003843c2e0001541c52800300d0380e41000c58103260400c0b4444101150360000c4800507584c078001c0c24203000501648810b0000c902041d4815102c218280c4155410101e00c61448181e0005007000300d814440420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 393399073 1250 393397823 393397909
    0x30b130519050304090c031b090302030607091404090618230d0207060c0203010f020f13050402030c041802090319050d080105090402061303081309060f050607140705 73
    0xe901c45024100008102100341c4d01240c03206040050440540c000980c042d2090304c05a81d0748002d41040078840f00d42240420342541e00a4040310070568418000781e414008502642d030515a50300c003003106610f031541250f19014460000400c414800c4017072400c40040101c81103850030003284000d500d496484c01c000c50300c40029001424510300c8800081e44980c11350058404100d02103800c60150b4409420903c1880b8601004654030200b107113001d20701e43c00c6103003400d0f0200d074070140004c0c4914160090380e004140721003d451901d8079044114845190700c500350070b480d64082c4001b403526601401403030192140070100074114646440d046042c034103885080f8050000e182c0050040382c888582d141c1d4010740c16981a40d4845943c03c2e5030720a00808d610090480000084100d02480c1820034a0100c80e0114030610801d61201503501c2c041d041c41c06000d030012000c4c40200301107480c103000c40ca1003042240c01d403606c0640f24000300302800034081f088030a03244003010103030080071000611286 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 393400323 1250 393399073 393399103
    0x50901080c041808160f0b0408251101270603020715050717040212120414010801030807020d260a090e070806010f020f10090c0812030f10030b1305 65
    0x20b1a81d0b50b545044c40c41c01103c2c07004514414041e204010007a00c1920341c1801500031244c0801c61515240902060b40302c0000103541c24800355040b000002840e80c04880710b580000c1c2c0c0d9080c12000030044524004030000051010481d42c008241d1824041044010b421155005a6944c4090401e688080c0c0e8002040c0300e0b02d4038100410018980c002d4007020540e03c111502c01c2c01b43c0701c1f4000107a0359520101c00725500c1c05000340118500169900034004c4400244101400c03c910400541d8512001d100c05000b41108012010051802d0209809014031a26650b000303074403201410700003440d403000d4004e03250400240043c1920307000300140d0300401ca0309080300c42d85d1428050040165901811003414007181c03418000711076000b4018260070200610440d00042c80b10002c20019040c602419620884074200102c1d4240011800709645048108203d103541c940d50403071550f03504010003401d90031a94180100005007440e640c140038001d407000305090800e030b43c100142000410304407840703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 393401573 1250 393400323 393400361
    0x60708010e0103060203040807050607090608060411030f04030201110a080105010927050601050903190215090a060c080d02030705070b010e01060f2304060203030114010201020304170310050901080c04 88
    0x51101c41503086040d25030080000d40c4984803464050b07894081c004000381107014030010003542075030008000c006c481043c0e48000e1140c403200180000c40d201d03010007924001003000065140701491503c01d801507c40d2000083d50304c844136040031a074110703010303000000c0d024900411032586d000ba07a04025000c6241d0880f561300040c2c49652001d060008080901c58803080011840e0380120162501401e028042d02c2c2041d041c2c910344840081e280701d0403481020000304000307245809006842800801510002c0c510741410b42c2900c030b400d070a074000c4a121000f0044110601d81f10f001a5004420309e0312400e4540e0f00514011000c042c05801072041002400300403c00c040c2c2c841c0401d0240c241c2800c01a5540084110a0901d40c105401089641c00000f0b000245164000300075030407121444c0042c290f00d062807004a0a074070064070060b0045031038071001548154400015a040203c031103030758000a940d2004581c004000f64042100750308208141e40c401d00b000d00440007044c0a02c10004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 393402823 1250 393401573 393401579
    0x1302061c06152c040c02030a0210020c06180703060c09090e0d020d0e030309040e0c18101511010f0c0201110f03040b07020a140102090111150403030e100e03070506070801 75
    0x1060007101e000307080c4201c2d45000f00d420340985502c801d501c45910107001130100c002d4644019550760710030b0810a0052240c0440080a41814400c2e0352011601c10041c00d560744464900d420f1007091500e900c0240c0c05484400800100d1510959803003c0d026200c442586140490314000c88644010114264020341c42c2600c840e42d0100300310304106400d080ca6007502099001191450082130000c0c1c0c0c002c0d190410000100d480020300c0d00c841001107401d510121070a4075190810f02e41a21000082c842400c018020288007081d800c3d5600940c0c540b0050f1285600740f8036094801355400c1f01503150760b9480e14204a0360a01400c41104d410240d0300340b80094030b07941240d85210062014007286642004900c50501c02e11442c0d40150700301c50341268005010203181d000b503001c41030389404a03030307580503280c144000890025011524000707158030690382d40d00d042e0041c240486070300190780221002d80065038880e110307210490180b8002152a220203181040c030741240500751806005070300c0010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 393404073 1250 393402823 393402827
    0x100c051015080a3005040605030604021908010501020f07050f060d140c040806100506030a0507020f0a030c0c0b09030d0c03051201030501290d0b1302061c0615 70
    0x10322a411580000140c04854400094100c090342e049215180651141c100600c51070f500d03044a01d500c0340f0041c9031858001c4101041003481c0c2131000c00411018002040200c0c060005150300400c040c00140c580300c0441030400b241c4070f0200c19000070500c400e00600265a04000070704040400c540104482410000080e00039001c40100e140700d1178001480d05401c0005d9001404400b2010700790071480e09211080c8004c9070814040ea40d50740c030079180000d103200c420190030001c40300050013081c0745860741c82621000d040d005100e9010b5210341080601103500c200a240d000303074040d1340e6840c04004640303408400c07007150398042c180e00c8405100400351076501203000305c04040e040c101004205101d24095819000c0c41301d0704240344c03041000001c113025064010f4290007031842064441a0b18200e2035681240484100e40d0300100c031000d42400080c41c3c1c5c080d844d04801c664210446094050340014440e0f0720000f611028000786015040b41c250060040704060300d010701918454842203400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 393405323 1250 393404073 393404083
    0xc12030b0a1203020307172514032b020a08010e040c0510030b010801050f01050406051b03040f0315050103081c06080a03050406020d0203121501030e011a010909060506070320030705010605100c05 86
    0x801017407154500058003081503180c0318040740d108900541c0c0c2c07541d0f0180bc0d52402c0e00000540070b4440e159a07154a140210140b00303d4110501350303141c00300241d0071300800d0540004020400c850081202502185942c1d50018009208405035404141c0419000c001001010103074040c9000701c1c05c0b046500240c0e82c101e002c1d1002da402c83d1408030303201c800b0400d41811400e800083c00e441804009408184404008000c0b01070324040c0909842a0b15020030501c02c80c0c1092001070506141809007955209180c1c01c0d81304420318015000c16903030707207416000d030410003a10412000b190000804101454061140502403007050010390704101030540d1000b0310b424001d1803034100328102410040130b40e01070b500446200a01c04020000c04048061003c000d0501c100e0640c04241d503400c00050b155124002c030340c1540c0b40134091600b4114180d0701583e03ca154400c0e00c03100008610341c40542120200040d003c13a6016034004684945000705002d2140c004030042e0b010060390700142e40c0801c1000a03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 393406573 1250 393405323 393405367
    0x303010f03110a09050c0d0c020f0c220203011212140a0c03090312020622110906010c080304080a090605030601020303060111100e0304080105070c12030b0a120302030717 75
    0xb005803108988000a4074003050b9070400c10441c1d00d030006100f0400400400742c4120f0140000401c00c6074800c0720240d90380c2c29202108074031544195030700101414104501810081c441c0d0420f0f04e03014410468000740e801c242c20100204561402d10b2003800102c001010f0040b01c0c50030844174000070008002001d1080300005c805000701891448101446041100001d54020b0005054018004002501d4640544440d10384088102c0d00e15000400d05051404590b440b040480b000c500010a000d00c540d8010001c1d41480b51401851010501e160003d41c4510b1090005030754510344c00c40040c24860058000ea020083d0500421402e0303600001241e07008442420010084070524864518000c0c4001100b00700c2d904141e407000080e10000003810641c0c0444000303000c1f2340d50305401210130f4052404050440c04800400d6007a0502079400780302403807809800b0700600c1f0b80b100320082c41c19056042c100e005905c00501c44050010040304004150803243c0c0300d903d42182400b6500300c00640b03907 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 393407823 1250 393406573 393406583
    0x41b030b0a0506060f0a02010207050c010305070e0d0510060303110607030b090f09251703160305030a06031b05030d08060312210708010f0e040b13021c0606170303010f03 75
    0x3151441c4c0d50301082ea91165440a0103d81c0c4210360b00c0024082c1d000a0000c485601c00c02e200b01c2c00c0d03503029001d03203803041d51a81c0e16444491a90b0040240e13480417074030203454034003a0000c04444003400d4082c140145001c0d88817142c0788500809114544280240014101441c100c09500b0310790ba240c0d00140c11064941c0704045a4517020406400e0603140717901c403801c10882c03a400348503d07003080a06070308450000005400300d442c141d604070b849110f11844400b03900222425403001901500c00b0355080103508900181240e242e960725400d000c4030004007014070101d04000c10051404104104400d442d40c904240301c2d0401070041b82d40c60b0004c64030f800070300c103000c1074102c8034018880c058000c1d810540300344810360402450140c000300080c0250500c10400000c00306044c0c19111146019543c041c14030061583c5081d05003418240da04e100b02d9100545c100342e03000000c1d2200340d034507407903008400001e841481e255410f0305041204a5410380c5030028401082014402108441100c0c0c100c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 393409073 1250 393407823 393407831
    0x50712020f07092a11010c03060504060803031303030c09150203040314030a090902090328030305011d070828051006020115090f020408030705030703021207110f01050c15041b030b0a 80
    0xc01d03801d48072200d0000e001681903190905103400640c0c549c201d02c04460050790200b000544034504c1640324482141d05801da41400c10030240068441c0c4c1c0b00a104032024030305a0707440c6407204c0c0052504884003c101d4010f80c0701290a00501040c0d52220b4141c103204002545040b04000c0c0c081c0486a1030310565014540c080390801051b1403e00207140c6840300c0c85610405941040000040700c010541d050700002c0c40e1a00200700c0844d41c07010349401001031011110550354102d003c559440c0c0040800c281140300f070103001042080700a003110445000c040100f12894000c0b1124030814a90384104116814402c1031513840c3d40103c11081910000303040815901e0900c0d008401a10442e80311141621001904106100c000300140945d58465400d0f07c01545075104200780f40c0c0940e03000030b09050442940c148461070705040c00c01400106040403824807900c940240d0230f001140d000b41d44103440c0c440c20441040940701080c60004010380798000a0350031615108080c1400515040101c0c1d41c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 393410323 1250 393409073 393409151
    0x1e0601020d081005060c011b08010303270e0f042a0b1b03040f030623190f1a01020c10020606011202160f03081003050616050712020f0709 61
    0x40c3c00942c0001d818064115980c0d0854000741c07074000c0c4141a104414502d403007034030b601500e00c5200310904807130701640c1d00c42a61035007400401810303500300881e18621058913400a8140648100c0c1d034861000812800b00c00d04c2c140c100b640040145880c01c500c81012050f45121001c1104260310613101c5010b001d0751104d460321007000d0b41e1100c2d102140c5242c44007103000542c100c01015298207681c41002c05001040030404503502c0d8000711010703680151400400520100444652031208009116000c54424950702d01e1004527a00d94800c1e00b6655245511820f1952f01048203505000c000d640b601103480100703500035190280513010604010b43e46030f86584e58030503501035400c45204040015490b840c240350070790306003046040440116541e0000a03107125203403600842140c1d000b06c0680b800d82c4ea408011613a54482c40d13009401d0050901065021035280030058080c9503190b00105008110010030914004280d0b02890b5254104007000d50004c0c0802c88a961000e1503940703c50500c18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 393411573 1250 393410323 393410341
    0x100b040b031e100b010e0d030507060f0203011703030903030612030408120306130b09062701120b1305251d011509060203030f040c03080409051e0601020d08 69
    0x400c40030381a5051066a04940c42d04014481c550000c44901084402100d8440705007015240c0c0341c0d034124081030a0902000d1030341000344e1a0002d0910900e0003625088080c0d44040440b54000b5810200302d40c04401403003400c0705010301140841c5804015802c2d4646110216a00c1c031004001c0b0380200e00040314103800920400540b0041c28613903058650800300c50101d81c105400071181b5620511a10b1848000d5081070f00c03443d007840801402c0080c5603620a000c0c008500e600c000d540b91241103d03c0e030200019014223190703028018a401c81406208a420240c28680c4090700295142c41039901900015900007400860f00640b185000714409050403c4044218180c2c003215a404003000c04041c0c4841d080503141c1a81ca0040c02003c000e040c62804403032106080c064840564400c1003c560001e0b081000e0b1507006100300035a06055840c0e9561005940141d801251615101e03030a010345042c9404524806080060300100c5620304600003d603500000d071240c909001611f4045034001e1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 393412823 1250 393411573 393411581
    0x12080c07080303130303060e010509070e060405030f030310090e0d0c02060d020d0e060a0e0d0c050c031906230105120a05010c050904050a0c0c02131b170f0108100b04 73
    0x10304410790f40c40e4a8000044100889220001c0b00005d180140100e0310b00300900c3c0c4281a260050b04103030713090740c0b01142034030310114040569510860601c0000b8096804100c00d00b699100c550245d03440b4101100a2000e00c3c010780c01c41c41c0d40c6400c0c1102030410520000343e00b1012120351030142a144058008030701c4510503d0f02c7c0f07041050000415480c2555290070019034042544210342c5243c0e544c1a030f03442180c60380800e607580c50300303e0360f5440455881881c04a464502030002e0b103014090b84800a468052520301070b580503001c03401801d040c008244507020300c800c2c4101c003000100e070055900d040c15640500400f84a14810b00300e1640e1f99008015100616601c040200101c2c500d8500192841d00403002f070901c0745050400081c4c11b1601c9000760302c0c1d00c000f15200c1c1c40c0b840403103a08002802410081406909a03150301044038407140c040b81011140031a140d8040804800002202d09000201629600510b10b001004a240c00162218030b2a00a240005c1c0310320740c49001034090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 393414073 1250 393412823 393412829
    0x203120a0209091806180c040905071805091c090308160213050615040305060429010e0103020a4401020c1510240504081c030f0612080c07 61
    0x4100c425013002100c0800000051060b01003000320750382e81d42d80481800340340001c440220b031190441c2502850b48d080c19000b4010640c80341c0181d51030a9219558042048040d099500c3c01a0311501880321061007400f1022403010700c4480c00c000d5011501c00074048101c1803000510b040340020b40300d50603042c3c3c044000d410b5540100070302000c404402d440b1002e8481a584c0c0c0c2d206400041800c2c80a40826084400300c90303000000d0301c0300b641d40d5103079074034010355503440d8059100414584210070610b98001a005c0c00313401110b1900c40d411401030003a103280d90b0304080000c00c4e50003220025021441c0801d00302000396400341d150b04000c4140745100c040d6400d0340b8007035580081140001d100d000b00e65190048030480d030b00b583c0c568a5030704042603070555114100050f81c040900c2c84010100c022241a0917126040c801d01d0256110b4246140148240214a040042102d200c0c85039916008607004004140024005076041031120203041c2d821020003880368600040883c0071a1003844080c1c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 393415323 1250 393414073 393414079
    0x504080307032f1510120f0317010627140d050106080d0e1207060f0503070e0907080403140a090b0c0a0f0305120714190c08030702011e0c0203120a0209 67
    0x24012402000e59440c94810306541300c4410100000d16a40f9030789283d881120030070844030010340001c0e151a070842200e003009034200141c0300c0d4039242070102042c4140c0204402c0d5144500041d4003240301252055000c0383d44021148c0401c01c20030303076005d0740c01d5544005044031480043c03090b03440e01c03900411250b8400c0e8024090400e100c0740317203a002311808002d2203081d02c2801c000304060590305e403038100c14007070341c0085100604205840c922803070140d98000780e00d0421a089141250004a0381035048810800061103801003004240e40100803045060102c10007501341008010083c1810032076000c0c65190140c0886c00c80108601040702c8022160003000502c0620082d0030000c0c010361050481c600000180c40c042450079200701c96160f189074800307120f14200940d18012800e17401c02c50924004016aa00010020610000055010b4815600005050b866011890940b118003140051680303140c4130170a41c601c3d4002c02251401207074201c00c88441e903150302d4140b00a0082510b20f5030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 393416573 1250 393415323 393415397
    0xc03120d060b070507060513210302011a03060105010c061e05160203070c0e04020310110903070e0c0f071704060f080121080306040b0306040c0312050408030703 71
    0x511221180240211032a80c10148540760b01c0e8504503540d803060200040141e44652800c1002e58450b0001c4c050700c0700030049201c1c040317684030b1110400744010344140c01e900c4501c806420405409202d00c03903a8903c00b510013280c3c440440006034880b00c05101e950305009130025003408114840d84816212501000151851903500564100a00c0112814111148500c4c0941a114000001c0d109640d0b4010704d04c00c07078941007040d000e424201c0504100c0e014440c10014040070307012b5018000e548001c101c2101d865038945410145440a6070b4041c8508588103014499201040b4080b604880c46010075541d503480795280c0410482030345040340601504c003140103e0700700c0d4084c56a80ea00d1205a0b92402181d0703c2d03a22001c101400040850083c221000300c450000d29041d000d1940510010300c00600071449901081c2042d204650841d03a20300d13141c0701071003005254410441e03540070500d0980c2c00d01d4101800b5958038410040d0140074022a840d580d03000c1c0c881c82001100c0305006012407c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 393417823 1250 393416573 393416593
    0x20d020d090506041202060c03190e060403080a0513020603040215070506040506010905010905010e041101090f031a0a0212130c0308071202010f110a0518120d031107030e10020c03 79
    0x2c1e072204400e9038220b0f4034202a080140c00b1610006085000b82c1c500100980f07140c54400d210754001242c240344a403035913203032500b6a50380741d42403141c540300324040d03280c00000d85030410400044401c01804248140305100300c000160b214079068a0b4040d50540340304000c69800d981c4e0307001c640100c01c4014524450380c0200420013101192141c100c0c1d503207039004e02c007907600c0c1e81e800b00c00da517400d006a09012005100180c04245003142c003005481c810f050011486441c1c02c59a4200c52040d08151b8000a40900300c20380159051552a0300c0005e2040440c10110540c00301d01c0180e4025203c0410f03075003031081c03840c148008000c1240055070b008210a0384d4400b2031401c0c4080c00d2203e0780c0c002c0035508e09500c0d1035030010300c3c2c0918000c1c04d102441451805050b9041501c65400548035228040800e219130703c01ca444810520040020810040000107c0c002004060301c000307130015488458184524400280c0200c01c41c0b0300701404039800d90483c0010311040f0b1400031724803007d80c0d040c03140c41503130 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 393419073 1250 393417823 393417833
    0x5160305030a11190e0a140105071704150e0306150607050115031202010b0409230f0d02162112110616020118020d061e0e150114030a0303020d020d09 66
    0x401381c1c269a40b10010103081403410004190690300c2400810b01041240c030745c280d80304100501d11030b80310301c0b0102c0c05498002c02d251200e4006400c8420b040c025428500e5059400010b40110120104c0c028030351850942c5520410a0518103503900900c008190801008400c2d0000c48803282e00e44c2201c200283e480c02c007418102264064031025500c0c000820002e03003090300484480c150041c401c0050001e80740002c0408640d0943c440c6564041d54419008a503003d2154031040949507006082e104080505100b40c1e03501c035400314800125020400b00710b4601f175160791104640042e06200e141c01080001d480702c495200215505009a104104c0304a2800740e05840080c81a40200005170604000000f201a07074440a58800482e40600000500941000c1c0360300500090041c0000c0c0000c0c00700c1c040d2040b41c045c0c103240341c00401c101c42440241261142c010030940040303c441441600201e500c0303104001018003090740021740b8208000c407130b8040b00c103174403a41c1d90b00f0003041c080c600740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 393420323 1250 393419073 393419107
    0x91502030301030c0b09011403070c1a060a0602030c0c0d110315101a0910090305030a08041506053f010f060e0c03010909110901031109060105160305030a11 69
    0x110313a54940c03039001060740e5000000b51244100f0686030f40b028480b081074401211303000140ba0070f04001e40900044005410f184004048940303c0f0600c881906003c01040301440080e004070b011036005001c880d844d61400641d6588042c0c042d5103601e041a1707942450064940e03a0302015030184540001050a50540c1006030f1003081f00320403c0f4902c40e00d50385000346409042c1c1d02045c0030f02052140c0489407400030062408020f0354280b602110b5943e83c1c0ba80d086405c000140000300d4619420001030088800b100ea610009920b81001103d0600000465010300c800c1c0c0308401c400309030305880201400c0c18403260180e04110b19044c040f46c8403010075001e40120782c1d40801c0c03d410050b00054910111020303d0194100010b42811a03007819110001003155034415180c598400441450507252001c0e114040d50043e1006081150884c0502c084908094041d60400038100401c107144500c548560f0045581032030b007030b50340b9255a2020f1000d0030100b003040039801301c001010700d00c199104007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 393421573 1250 393420323 393420329
    0x80402040617100c0e01050703080604020c0d0c03080a050c0d0c02010605030f011a04061d15091005031e12090f060a02010506130612080d180308010602070506031510091502030301 79
    0x10144104d100c158411a0741d942d480020902040040c84070304006170040844503070010300a44010b003031400100c192483c1c0292000803202040c0d6004c03040c8281540080465403012081d403040c4080d0a14000c8105148101c0e10342c810042d80c1c502c0c0c504a842d01c00c2d0480740013003800504503640407000081d0107008162000041800c5580c4903c4541030f418a03009500440b17600540d4080107818559500310b014030002d000d811441010784c2070070181d41da4201d2081c020f6070101c141c4c1d4405410403082c5480c1080e440302c044000c00d540301003100074040c00a0381c032058030b40d141c000c0c50312050781e80049600d10b0710008a15910940c0410000c99080e4158880c138424002243c0b14240328004000340f0084880d0f500400500344125000350010880c9100100f01e008542c80e0300082c0b01d20040440580c0b2882d4000403030000701d041c0c0042280660420801e03000e0801218110320390300b05045540c0030b65200c1d614003809022440040400c1c0e60154184c0b0000b412040d880d40310031000d0385802904c0ea17000740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 393422823 1250 393421573 393421603
    0x7080706020706020c030a12090f03060234110102280c0b1e090d0f3909110903030f130b0f12041b030c1403010e0607080402040617 58
    0x900000f90291000651110780c40c03015003d440110141d0302c5412164200700211000e00c06078600000ba0013010284180041d4080c1c3c00060b141d401d20340440d80e460304062260601e02c1d45125842c2e484007100c0f0100750107181d00401000400c3c0e40080143c0c24040f280c01c03400740010000d01100000a2010301d190078151103080c0304600943c64000310301107402a40344c03203040300320b58540d1042c8c2554860000e06c0c441c10024881c0c00005d01c0740d81e0710400ca101000f42102c0b21401041c00780400d446001603054410580d032040c08180007075540b100f01c2c130000d40c0300e001074154035005180d260404510480d0300c0980050f0541c0d54501c2d418990346d09503484550302045000e241400041d4034485e94041d19544074401d8005407606100074001414503c1c0503005170b6541842c800801c0ca50964456941c00640c899410000c695140140628001820061003402641018200d030311404010407680d40c0903819050041e4280c40b41d0001c00c0080985400103a400909026000141e40340012000d00c1c22540d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 393424073 1250 393422823 393422833
    0xf0b120a02030115082e0c0c060e060601050f0906070209090607111207060b041104060309030215060a05090a020c030307030b100c0b0604090501020f13050a140d03080601050c0708070602 82
    0x13012244241c2c03084c4600c0c1d20940100a4038a40c1c07600703055440c0c0000011100c081c07030388605400c0380b400f02c4d0b084030051404107001030b0080080000500070104206c000001a1815280c000006000d40c411a002041c15040028211302d00795511402d494044c1d03000b402c0407000e450800d10b007039500d1100b80d41480219405030900014201c0001e0240e64001d8420032035410b040040e1b440c074020f0072400c0c098540c0503444001d13503510020f004020b0001030059aa0220341040d55080207414402c1940d0b80c002c4000b400e0303080084a46629103000100d54082e280c0801903698501c441009003e07070111081303d400004140f128495146d009603c4c4901c04480342081124a07140a4808807820340d070050001c21040000b42003450305602070050280910b0006d8500400c0c01b2115243d540311021540201c60009428031543c00c01038003000203400d4040d103c16510880314001074400e1190403009041203c03010010308543d115005a82e9801a1881100d452036144c038416a223601c0701c2d0040e0001072040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 393425323 1250 393424073 393424091
    0xe0901050c090409060b13020307030f09020f01080702190605040210080603070306180b04050f0105061504090b010516140d02030a090302061605060c030a0609050402090a0f0b120a020301 82
    0x40c8501401002180c006528204490080c040505103404003942c40c11395030300400da40b41d11400e002c5030130807204c00300040c3c0c0d902e041103024040711980d90381c44007001e203803c01100068540e00d02c6849001001d081503d0380c1c0d82d84110482c07810b10544501d07000104050081340800c4402c2c0c12090003a07100321484080c02200c1001201c0c0b101c1c04540650303059008100c01c20110705a9400442040d00d01da030b0401d118a51a2101c0103108000c2e030b0b040b82c580d4401e40c04900c0f0007100f84600b64210604071150556500c00c070034402c03142d0080303019042c0e00558510040d84141c0c06907044410803a00d0001950103082503040c40803650070201c030b06035081c6c040e201c068001a44084119031036030b10940c45c0e1701d05140c1141c0a005a54200b145050020440c1c01040000700b074040107803611030f0b030107013503800d5481c50040c0800060360401d40c010312071302e0b08080c1840b0040c0c0e9841501680040d0099001880305404048100540741895485400c245480f142010502001c20728081740b80c000d0f0003c2c801030700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 393426573 1250 393425323 393425341
    0x3150a060f1202030f13060b100804050f0606030a120309021c0b07030227031501150e030303040b01050103020915030a02040504060b0a0507080d0621020310050f01090b03031306090e 80
    0x4000c07560405801e185e8000591402c1302c0d80b401103082400f420002540c2c0d0064400715048040c105600c9020410000412041000401004200020b800040d05071406c011340031a03070710010f41c01d000700090682c0760000c15252095001c0340c0301075001000d840d01c00a0481103404201c040190a0700d10f040550005030f00c5c0d50082c005c80d0340000d0301e01a120800219110047c81002d5030200300d95040c02440a03440c1c030f421000c420107019100b9190500d02c41002014013400d003001185420b8042e42042c4200000f0030b00341104981103070001e09004d81c0d140c0e444000503644900310b4030391850410001c414803100b5803165000d0400d0300c100b541c00b04992601d510381341c211801080b01400c0043d800b0810300000880038000341c0301011004c2c0c000301c5c09035102c0c1c4609005820100040f41c541c00c1c000000004e504e410080c140260800c0f41c0c0821041c182103c1c8540012014001d540c03125032224603030308164800b0030442e500c600c5066104068075449042c0140b80444501c20f9080026402e07011405000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 393427823 1250 393426573 393426577
    0xa020d020a0c1208090a031101170601121107020a0303020304060e0307120303090f060212061503160f140c0102040303020705060f0304020d0206070803151207051503150a060f1202 79
    0xd401c945004642d51900034002d08001c1c4030407086991110612001e001a11500c007880055849060000030b0810300e00300060140034580118100084c030721003484416600039001c60044126030001040803044101c00701818815400001e420041d81d001c004181940840600241c2e411640c03669003075085c072001c041d030316400c40c0520180d0003451850400080d006e42e201d109414407665a50724204202d8030b44e00200e801c038203090100e070344804080201920f8040c89a0340748800040c1010f0541c01c00e4558584140300c030b004503009210f108004401450300600c000404605007586d5550788a813130070700c124043d402502c4100d0140c80b40b804040741030320705402602e00356400410510b04541c3c1d10f03020083d034035030251001d07030700420100100004549040000e500c25042010100c440078104414040d4007071141d03041c4407031600100b400b8000c50b951258620010446140350f5912038840856041600a450030303000d03400340b00094009030440d0000312611a620058540e1290004045900c1c0c06038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 393429073 1250 393427823 393427843
    0x14040305100b030708150a150305430317040305030a21050a02030402010e0316060804020a05040e0604150606050405011b0b1e01080c180a0b10050a020d02 68
    0x81e00198000031051030399510400103504000c08481c1507a035145c003034a081401406029040064240404c005d4040c0e5010f013807600050f1646100d03029180d81c981d03540b2228000b1819a46050100000c2d0740141607030000c1d95460010300c52800884540c0303001d01801c010510003102c1210038a0820000e0703400c80c00580e02100e402c84082c5140050fa0442103a100043c01c0052480304141390480c24607101511981d407050040000040e80c908007030001404c1c4051018200340300c5c0e48101805030300c03562401881e504942c0b050419a003540c441d0b00c0060802c840d150001c82d0001d02d400b0380006d03000c1c0c002500c103006c0d5009030b803114507a11000e5008001c0e21024000c2102040c0100000c102d80e5210341880401d0005180301c400c2c502d6619500d100e011003058404d48c0801200100002c0800f03c40544240104556401010454007400200d801041d42c05800300b400d6403445d000801d10002c0e034004201040c002000515030411048002e4182d4000031030700e400610400d6015030a8a00026500d865 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 393430323 1250 393429073 393429083
    0x2041107020a05090705040b0403030e1e06040b0d06051903030f02030c0601030210030e0d03020a030e0601080a020420030f1005100e040c1413050102060609150d03200d140403 77
    0x1030b41c20f0900380000e1000140118003007020070040051000c0c942c102070400745201e1307969a2000c0c00b0000401800b01c20b001d5a20403030341d08640a0341220f81c2c41c1c0b02218102e85081d50615118103560250600078a480d40c00160444900c1d0003252003603260103c4001940e120340c4822803146041c000c00c136680d0141c501500c45c298070010050000d440d00c56103114000d0344030b1074003050300803015000a00304400e005000700401e4001c41c4241040307405003da124003081850060000390303d4050a01d41d41d4420030000390140b0340e02c48020300c4c021900718100c5c4803903480070070312a900e00700140c14150b844000c42d0700004a24110602040c585041050309110002c40c2e5030790710b01c1da8006010403008104080d90081404240350740c0c0460380344280f010700656045a407030a0400d0345040b0019050100040c1020f00c10b0042c00100060580c3c20314598458030401c0e60f900c040d00340d10346405da4004103222034841c1c200920080e40385841400040f0f41440d558545e641024441c200340e0303140c0b420f0045000042c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 393431573 1250 393430323 393430339
    0x315010806010521030a020a050c030a03120b011404060e040f0c020c010f0201150825050d080906073003050702030901030f0605150309010c2a0201170a090204110702 73
    0x340c0ca829210341c00c0b801d030341c0500f022a070707a0503650070ba15580c485e01b0940d0268221b1442802408020300401408440640c0035000521403075034000c0c03001c2101c0201d1190a5684c41d0400703201c0e40314002030394000c0081d0584030b5480d501c1c0c4402400348655050020320170b50403e101070550003a83e00a0601ca03404c250002c01040302c400b001502d5450800c1c11000440d940c4024002c062099004410001d240003005008400944101c0d0145c1a0a000090b2040600000100404d403607000303442e41090740210000391280c000d80e0000d1000d120b4510098024032405620b12000c006044540700e110a52004001c69100682c8090302560700498003072025800c1031000590550098206852100c2d80381c41c0000c44903100c0000580b214484600030b00800004800c0151950f000d00c10700c080e4840c141080d500b62560000a10391441c03490800000c40840d94070040c0c110390058140e01e001401c16240000507146c21408036004124120090f032043e0304000901540300351801c12100403079005000c1786 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 393432823 1250 393431573 393431579
    0xf010606050301140d1509030201052a0a02030408070603050a0b0910270509010e100e030912100f0e0d0e06041e090f0906061e18020c0f01020306031501080601 70
    0x31180c4130401407482e080022404910000f03403446580000f110581500000c08440c0ca0030000d00b101d00040c8a0350041c05d180040800b01014428000e51420000c0041c0390b5484014004900314001c940c8084c04911519101142094040d04524424070581c00100040c0490000304001d9801c141d40d44003402d003e00909000c8680981480061221183c54404c4046000103521088036000c90724481d41d40d550f400003812142c403c2c00700340034450000d035050042c0261444503e0b22841a40d68007481420399040c20550b0510138007076210703c8114001c2c1004201151161a005400d008000107003174043c0380001c518081c041c4600c06017030f20018207818246800c22544680c4890445803007192908071940014604155005104400101c8080030400000c0c51911100f0f07290f2a4000300c1442c020b01c0d0b00076030880120007040088925100301107110f001040b503448024442c242d0b400031680500c4205003124141500294080c01c400da003214040c08400c03400303082d007400c00c0c00750388801c3e08920010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 393434073 1250 393432823 393432839
    0xf060d150c0c02280e010b09040f09020d050a050709020c030708090103060305030a03091505070512100f0303051809010308040902090604050d0b07020d180e130209010608090f010606050301 83
    0x740e8840042c140503000981039000640e0401e4440320700c01c151807084589200c07481500058400500394508005819410b24648469074003540048601995403500c2042d803000f0345030061168150080d00130350700180710303042003916135880e20010365041c41800c0b0000380b900d145100b1140901140d001850500b10340f03540b000f003980c0c0910003c03030405450b80004804982c0034002006550000d48000402403110300d01540181c01010059211a00d42000c10802a4000046070003502403030088001c2d5603540d40f80c00140030583c0e0000010b0381c8410300c0c0801010382200043c03400108500c101440092200d0402c80d102c030003404000d10300441844100a01a5640c01410025000404c0c4030306103600c1d480400c42d1a4541442524282c0c100400c0c0942c60781c0500c9125000c1d5110b1600c0f05510000c80030036030100740c503481840d100100326000514800b003a14001e00340582d000b0311201c42940d4804005001000603950103806005441e1051154181481448201c0300903440d01c82c2980c3c640301c56 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 393435323 1250 393434073 393434081
    0x30c19050913050114010609240809210a0801080a1a190f1a240c010b09040305030618010602060403051c2f0310090c02030c0607080f060d15 62
    0x701042d1421a000000010380c207000b420a5008480e0080c0c500c1c0d85000d0000301010100d40c480340d149100007078003014010040342e0390032680506040c5200c481d2150b1903d146040c102405400d000d071910140700743c03541c00c2c0c1e00060940001c02c1d80c6203080c41e40c030b5a500a440f50a1600c2c001e14240704946034002050381c040c09158814401428008180c14242d21102a22816100c050f001540c0e08074a40140c026106185001502969a20030110b400380001c0c80c81458851807250307107800450098050030f0700b50043c0080007001380195072107080515018026810695005e40304115080485500d0840c406a090490f6003642c001c101076201c0b03460513641a800401070b018102041034800e4100d02d02c50144c000b03450300c2e4240896000c00425942840d00d0100c1c882d44000b04010014000104007402040e03017034482c82c5c440000c142d10003075016899882655098845401241c080000c039176045513000b8071403404070402d11110364851082001c1e40b4404000100301583c5000004038082860340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 393436573 1250 393435323 393435331
    0x160b0c060402010e210717160b1305180115050313030302250c03060b030318120a0b04060c031116060e120c0102091c0308070c0809090108010b030c190509 68
    0x2510050000039469100c0e03084205d440c800d1a90141c0700030003107a450080c1102990050700040c00ca1038404c000c0b0314140490344e208000401c00041880020307008591100b030000c040051000b19401000a85400e0104003449207501182030301c441d40c00c0450185084900c1a445040200c0400b49942d405400a40008541c1c01c031100d020442811440908403168100c0c6005003681d0151038598030b41174041c5c41e0b100c4e0070203019030424005c2410070440d0600300400488100c07059440d40041c070694a02d8081c0b80c0d000a41070314500070038041070018039801020b480d040c5590034001c0301e0b0740703a555503103d20500402e0550404039505403804141c0a50040300409054000d640850154103002d09540c1c2002d244010307942d5001490ba0038601d0800012420014441c00c070419040e101d45001c3c2c134034403004114000b4010668003510411103a002101c030801b100401e04142540c480c1c5100d4000c00c01340080328040d2180c04100307600792030820603412407040132030703250740e82d40d0306050a003d051107000c1c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 393437823 1250 393436573 393436579
    0x18082a030d092108160c06030e0703060f0f0203070908011a130507020f0607120b030706020319020f0a0b0a05070c0b0114130c0804120f091403100509160b0c060402010e 74
    0x1210004041c03200030b10f003031800c5c00304076050180c450400c8a50005c29030700c40c02c145481c100c4802c11340a008285078040344e400c40000982c08802c2c0051034050101c010540454500c00010402015040940c18065856080007001407400480c41d0064204240348082d40c40070400183c1c4900da00d25800007507004d0f11600c1074075000d004001040b45070590507a00c000c0452601d1203810440c04203031145908080c8210006d00c1c00c246441c0307003c0d40301d20466240044211040c4000d9101600800c5144000d0b01f080003110703c030000a0900d038200b0803041e112440d070681054041009584150040c20301d164200c40d846140d43d01c0c0c440d0840c4070003183d408942d04600c0030049601360724020710840194803942c0c0c80f150900e20b49450080000c4403c25038480610070034401e80500585e005200a09030b03400305182c010320803a01710001e4030b8544028030302c03615035040c0b908009001d200454850801204186030411880c0c175603900c80242e00074114803040a0b071156002901640c454526084900406 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 393439073 1250 393437823 393437879
    0x60403081b0604030e03010c0503040b040201081f0803031e1501120f05150405010803270f0405091006090b0609041112010e06030610080c0118082a030d09 68
    0x1e4450782082412901a004212071700c50300702980c1428003c2032591081c518000c2d195180c20b41d079100044102500107810400d0302d0700000c189090f0301847c03200c0310703200303040710303820b4990b6000c1ca60b0f60380e4412200000c0c800c107611640039406802c6809140130707003524400c20041020040044400041c1e580d0011100c0e0f8403400b00e148551413600c959405142c1c05070b44026034011407002e20041e901c0c1a440003580758001c1001c16400c0d07c4405850529000001d9644189029030000400c03400d0804485548245800d05220304100d000071b4110701c0001c031240500c05140c3d10701034041254001c16000380c0122040006484510302035000203a0301d080504050b05100e2109032141200c2001d80158000692101c284502403a04002403644100056241c00141d0704101c00643c03100c55401c01c00c4d05024000640d17400000e1808501e002410300001140c0400e911954042681e0444590f0000b042030544070240f154100402e0300f4004e0740c280d845110100d440c010000f5080c00c2c83e0003001fa60f4410f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 393440323 1250 393439073 393439117
    0x606063209040c02030c1207022d04181b051e03010603050717060a02031003080702010c0210031d06012d090f0b010e0f0a060e041413140c06040308 65
    0x24070f1045040300c00c0107900458440319803044052501f807086406000b4030106010485c0181d0700d002c40c00078a800742000301d1240b262450090380700300f59031440c0103030b00504200341998030310001050044441c0c010043c02c980150a01018074516901d8040c1e1030f001072003014001e60b528078058a01c200301c2409000003552554079240e4a041c608990014020781d00ea90000c6c48418034104081c83c0c00000c0303c00114914107007251003082c41d1416100c0203140c000c02003803503030640e0b0003101086000d43e0042d262220071760105030002c00400082d40c002c8038240045080704082c020015005050320507190001101e13444c42510303106900c42c1d99980031032801d680c18000ca034003d098010050814190100071070300000080001d0400340c2003081840c061109000a0400c80d95410106811942d02d401d01494051204020030060420003102c80e100000d0071301802818021440002501d81c010300c2c0c1810189001c080c800d07143ea01c1c91360440c0d4403000c140001d00200e0707601801080700000a0800c0d0742402c1c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 393441573 1250 393440323 393440329
    0x1a03060c0307090e060a06030e01021e1312020d020f03030d0c0201020a0e030a260c240702152d0f0a0b030c0d14030f0301030b040606063209 62
    0x10032140c03550001004401c0c851041d402c002200d001e0030382d801c0c1601c00f52034404041810752009100b910101621040501e40d590000e6044910b0031003000307500c86800c101d0809000c81981300300204400c100c0c5038403000500c2c60744a00030707442942e802090743e41040c400c0e0b020041000005807007554940410080d418210300184191941a5440e80000d80ca40140101c041c001010701d602e602e003c0c0d00243c90b0500040c0e4a500f4120314904141c000b8409034203801100101c4e80038a129031200c504c1008500d140c068910038a0101310310301400c000b00641c0c1d441c04101c0c1c5907001545540c1c2100c03c5800070500e40e8580981e02e004001807840003a44224050030021000b60041d11400c0707140e0024414040040260b009614140d0801d41c0146888209003001c0f1703412a0203c040079188007841c4108825a000902c211070040f0b661f10140d50301c0396100c0c1058070400c0010b4604859103443d0200001300b05e400b8002c100080d5214a60500001d40e110701c4107116a070344144612403030300f000c001d40181a9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 393442823 1250 393441573 393441583
    0xc0906031f080d020c031e0a12020102090d0803011503090506071b08041d07080114011209020d050625080105040c0c06060605070314030c031b0705011d0120030a1a03 73
    0x20f556004203117401040c0141030030064500c1982132138888015156410300c1000034008047c540c40110010400102c0c041240240143e080180d070045002407400c00380103000c0c020b1816a42c008124500150a0040940841e032001500811907017040c0005020980124040b00300590300c0c0000c08401e13803040c0d4a4094035031064100d03a03100351031f42404002030f030180c6001c16808040340c1010141941040c40e408001034409618604010010008402880d895004404040d45c041e01859042200e0301d0000d032038050031200d41580b01700c003482100010b414550440c65080044c1c540803480d03400d24041c81302808000b11001c061008019070a40001c550780b140a00074080366481d070741c4515162070010000140585c45031481c0304140705018034a4801c008030707600f017854200d10100204203c00d68880f140035808024115502c0c2c0b950030100c2c08411311158400810502c0200130106d501070784c5020407042500521007140c014000500d40c1c0d01c4603401032141034070000380819000e0500d03000034605 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 393444073 1250 393442823 393442843
    0x6070207170a0606120308060301090203211315020d09060801060e06160303240f0b09150c0a0c05040c021b030c030f0109060b090906071d1e01080c0906031f08 70
    0x3085e004500307141415800a5015003100341100280500d0050f500002e6843d012000341e066000786210401d007583c0c0c0e8a6040b2103004803502140705032940d552036a00c0301c402d05500d1f00b1001d4001c00d030080031090310510524050307491644911416900300f41c001c499a0307035001c40e0150050400c001c01b120214820011010540c8a6640883c420007010781c031441c040c6000e012100c0950f450385051040d11074501c035040685041d40741554540740245c00040c0e605001c81f84ea203250a500166030f8616501c0421812240d600446080e10381315620000e1208807800c8565001c010f0f04031b00c40381080e841d01c455911015900007012501182c0c41c4400090804441da401e1981c169541c04565042000c50300404064290446480806241c0055556103c020086c03928080240c0840700d4082d09501400c040224240609154004010000749540220300f04424901140800e80004e44200412040310070f2820050f0a0509644554484007030084c51b1490004000c0c410040108c0d800000700040802c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 393445323 1250 393444073 393444089
    0xb0705030a021b100c09230105071401060e0705310f120b0a0b0d0f05070e04080a140306030a0809040f1e0b010201020a051204231e06070207170a0606 66
    0x9131014140c0c00000319483c4903144802c1c490343c1002007000030f1b00340089880411003c0d0050700010702e6200121100e10071408004d0440825101103c4c00503c1540301e82e00b9a100d03c030200701e076500d8159007620f090040410702c2c6030030750380c0c440e9504030640241d031181040d1900340d00800c651a200c00391491038600c141c0007101c655441001d41d4040c8042020b0080d0000440c0c5004c1010101901c08a03913840c0304080082c11654080402c0f504006081060b40000e0044042506160501d1724003060a648022009800030b0340891002c00c1c509005421640500340c001e00910a00900d960b0740d80c041d40050420b0790307100d0f54a1202c02e4070400c1c0c03030280851014468803c96010524000d0000032103601e54556811684144400d032450f980090403500c4e0400038800c840c00a5440b03140010409010310102c116401c1c55070305520307074208000b07503c00e200746c0c07240111003c8004c0c5400f85e651f2020202c0c1d03540c006a001e20b0040180440380341c45d15074140541419515074480c01e071504402d40d241e80d404045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 393446573 1250 393445323 393445333
    0x1211070b0c010e060109110f0f07080f03060f030705030c0112022a1b0f040209030f100c09060813030c1518020406051009030605100503100e010b0a030b0705030a021b 73
    0xf2082c014030000307001d0030301078000700820280034004200758000c0c400c034a400480b0026414100440c0e941c2030301c109039400203901e03590f400060b103514407070b820a890440c0603034191381007120345140c00f0481d1419600054001e091941209004640701d40d5000c4800c14081d07401c01c040f94103408041151070658903c289807040500040001303910b0200c0c010324452114840c02095203042c0e48801e110804a0403c8034050380b2502c1c4040000d0401a0003c0c500c1c2d100d01c00e03000c2451084403190081d00500c005600e40c0c6070916a20b42054450703003401c07611280d84d111203101d80000030f8018041b0078692401600c1001140600581c24011100e03003030798060107504004050411490203000d0740c0d001d450181e6001c480034100c02d0303018001c01c00303c0c00010100c40c3c0306e1000488440315640ba0304010031008044900400c02003136040c00601d0210744140c000d500f060406007075030900b90041b1040300c1e84101e50008135a510391080320f01ea000600306a40f01c42d001c111640c3c1d540c0c0f88640d5051040d540c640502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 393447823 1250 393446573 393446591
    0x60504120206041e0213090609020909070b04170c09010b1e04080a0311030c2505100c0f050c121e16060318060e030d181211070b0c01 59
    0x200d514915a010500310340c086001c01c0006800c1c0300c410503850301c2c00004607200f4030f02403002950b1030051000340000b02c0d00e443d03e008103226150700f040580c14026660f1110903103540d0015034854115004114164504201c20080541c0010311140080e807a0815200b112403068001005c840081c0d125050340080480c10107020102414614450107445103014035203868035002a0b214025442c015081c0030300c00c040300304103c000f13008807102d04c02c112003561541c0c2c41c0c3d1003585040e444081034500034190000004920b03070070007a0b008541d4811540f1b030403100b60481da034ae0312003800502d20102e409000c2c1d6031400c040342c0c5580a2000070102c0c0c44020b00802407041c400003160710742c11024a0410340c08043c030141d02c206085051400d0300c0962030003064500840420000704901c100000348a030386845d1041c201c0502c040050000381040798814003414101c003525048c1c0100050015000025481c01c41061a0250f4003042004c01c0740d80a4600480e96460685151381140c04d0080a0340d446060403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 393449073 1250 393447823 393447833
    0xf0f0406030b03030301050f06070c0305070f06020106050607031b080d0212181c0c03020106080708030705150601080f060103090f06020a030e0f07030308061309081201051f030c1704060504 83
    0x140c0b0700d2010780045040d90302d0100040c21921840c0704042c060f0724002951828400682c540f00003840d0040b007103501d03540c0d503000d40820301d590512860005502e0203401065a01d0a941250754094042c0d40d070800405c10085445280c0011440c212480703241044030107000440390001c0c104070b0359000d81480081c58001c81d28900901c414510110300e81241c8184081030800b00c40380d00d60b0300d095141401400e4440e140581c010205500701204a2080c00d1000034002030000043c4406481a025204038804030781c90b4250303004090f2540c5000c128040002120030859034003443d0b21101c145800300b102d540948810f060880f0028054030242c0d0001240032402d5050700038466003406070401032005086181d0110b440750101e00005041020729000706003d07039140f40220181a820201c10040302607a440c0030360803a40102d2198094414500000489181441d0b50501c90303070014002d46119104480c08034000c0203400d240303805001a410140542c240d206020324032a5100740d00014041c2032134101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 393450323 1250 393449073 393449081
    0x305010314010b031510050a0f0611031602040f11220f060206060906120f060a0b0901051003090c17010e010f0b06070311190305030703110408030403170f0f040603 72
    0x9000d1503030508a09880d42d850000c0d00a102c1c21070b0009110090701c1d00782e40484c1003861b42d030110764000400c85001c10b020180606450032290030762070b03006c0c20300070b80b894564903405640d030064202c0001e8040740002d410181c0180a54041e41e001c0003400b9000b0040c1d1402a800c190310320886100d488a4800004803000303411400307862046146c040d00d600c0c2120003999090000e0426003e6182000400c42a4468030f403040e8000310351900343c91403401c14642d01036541c0c0f01116656005401d04101000c682841c1c00d009050782e00150401d1440703075628106070b014040101046031264a045000559600030343d481030b038035130741090002c615150311481e01400e40705a41b001000003840c11104c2805a901c10049621032645404d101d902c082003010407606200c0c590090f048003540312280d420806600400844c0300301c1d0700d80c03001c1084900110b007010082c001ea01607807006600800050012031001159050380500c0c03610388929251a040380103815420120704919060320100d01440040d030940a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 393451573 1250 393450323 393450353
    0x30c0c04061503090c03050d120b010804020901090e0f16052d0d062702120a0222020c010c080f011a0324040903081005040207080406080612010c03050103 68
    0x2405001850404003900c0180c034042c10194140b690b1002070400300714030000f8000080d0b402c0410b4401551b909100600314910613024143d0b01890503818a00c0c030740c05100c045c1d02441c1c01501c6008180c0c203054020000b801600d0395a01c0510400a0480c1c0f02c1c141040307650301e051050a5070b078030a54541420303c1385029010091043c4d00d1010140a511000c1e14403000c0100e100456101c0c1c400042c41c00d140005091146011a00c00342501c102c2c80050209409140344a10030307110492020310300c003083d517103804490b50025485600305803001020302803080710300444611003034014500a80c1101803421a22074131907100c0030890080420234168139a5400c580148134541e03a1090705000d41c0340390103c500c0010308041200030015002a1340c6c940c02858660782c600050300030001d004c500c3c14080c0c41c8400842e074002e98640e5441d000300301c50409000351038082e036208030803509003820440c043c2c1c0c031004000c0c40c4a80011003080d261102007024011000d41129a4500180c84d5046080c914170300751000c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 393452823 1250 393451573 393451579
    0xe06060d11040306150317030411011214090706090608090a080d09060e0718090507090b0f090c04060210060315050a020c0a150525050a021e030c0c 65
    0x104015519404115682091040c0e0000740d8002407a107210701d540036a0f0400b074011840c1031521041e072040200d9003000e407400b81035441425000d92442d18054407040b90000c1012240081070907155004c0d03002e103a5031100f840b2021861400600207183c00d68022110780500398440c060402145804c0500b44000c3c050501d090011031800d1615a60398040c0c7c240b006007031800c00502d81d40d5047c20b507482002c0d0903038004024000d021842840c595176031301902601440001c0320143c4403900c00184620b120349507000024040082c5040c0782040203281c2135a81e035403c24079045407140560785003002c4504c9803000402d200d455908029000389420440580d01c1e5119150038400d0010904501682e0107181c0b141d00b0104040c0c0d01e180c46031000e130240004103051031107a250207108000030701e00d080c8913a21034904100038950714000038110440c12007443c078480b20301118410386141d01c95001410084098011070b06980483c00360740659200d107041d1512141c0012603101c0d030310301080c000040d070b1100407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 393454073 1250 393452823 393452849
    0xb12011418010e0a12021e010f0b010801061704020f2808030a1707020a0512091c020f010f03140421031e02070302010e0114071101020301080d05070203100501140a 72
    0x9440c6055030340016041c0505480182217090030b28900c01c1107a10b0900800e0300301190140c0a9468060191445040c041c0f462400d01e00311409a510a0541504884182e51040d48954982035900d01000c009441030744c1103000d0082d0300d00c3d030352940c03000c01c0d800d0501840041c40d409802d42d83c2104c0b11500b600201c040c4c0e0010000345081c16441003550700301d034140e1154101141c031600700507031070104880713401841c50003036820100d101030407400034041c4c1d804240c40c05807002c0001d6018800c99107585000961000004552481d00c0d48582407009995085d0b0400284800e5800440002e105007103508171451010784040fa208080b25a8a00d4030b421180c2c00d0a0000e080ba600035002c810322003004003c031055020810905040c400d412041c4e00f11200d400030400106482038405600718112039442c003280c102c014100c44840d05108680c102e85514021741203a04405204448a62251074107907031522075007104551411340c910440c0d000f00051015800d29000340380500406200e03d5000d80c0c2e05183e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 393455323 1250 393454073 393454091
    0x10050405130603020d0b060315240316090c0216080606040b010e090a0c0c1a10120f0f02041413020f01090e0408030403052214150703030b1201141801 66
    0xe545c03600c0361055800012952583d590742c000c00e00e4490201c03500c61520103110180014401483c50861030011840001c1c1c1c00d42c0d00c1c0500340740c0d481c441c070400314a19080c405e01c04c0118552075400200512100e1055401e003100d2400354102c5080c280c2c01c0351005411000c184541e03417030079100d2034020041c00c2c02c04891a00103040000e09104000f088600255100d1055100d81803140a418006643c0705101c0301543d01c0703511418900d42d000301d45091001d0000900440c0c2c00121500301d09040d603000c012221050300300e90300c5000e0307412018800c80c1c010303881c1e0030f10100800000b4015031090101400c0340903180206d004001110143d004194113002c504d580500104a0000d200da6020340c0100364030756a0344580c501104c1c10300c10340341403402801c00910382c40c3d6644280c03c2d000046803e04101414141c40b08020800011511510115407800800c5004006406a0400405014010a000148000b181c41c19003540c1c50b8007011a5031107600300802407074007900e5407101a2a6142c000800034844 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 393456573 1250 393455323 393455329
    0x10c02100b01081515070f06050c030433060303080a29151b06010303230a030b0120150c03011a0f0c011103010303020d0f0207140607021005040513060302 68
    0x5410b001d075184a00c2c40300701141d2124001c0c0c1600c15540800c3d0382e598015400c00a00a00d041070040308c003142032501140304070340300000750380c0580d0300440f01307150030b8406c6003d014140c0082001d6074008038400403c04c5180c0070600c1244010b60180e00d404040d892720100c2030040358a640b40088480c42440c1c0e0f04c41c45442c003003504440c10345090382c04e101c1d407410708802402c40b07000c0e50407203840f0a401404900c480c80b4022600c0343c1241c1c480e40384e00080c0812024524502c0200003035100b9800340c14070012400d00d110740c200d0100b2400604000e203905100c01c18000f5100d1000216240c1030740222030381a415881c0d65085071342302d80d10f071180d24255414110000300d640b042c045100919540030400c40e00101070181218042c9240e00001c01c028042040102d1a64200344010740250140141d000315080c002c0b18280c004a43d03d50103000c107141040781c086246001010302036048081400038000503101c030305841d51402c8045c0c0319240c40b00e180804011106030000100b42e48070b41020b0701040140c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 393457823 1250 393456573 393456587
    0x17010f170d0906050a0306030c0305030c1002120402040b0d0f140d0311030402040902060d090c06080601170103021302040308040801020c0c0a080703020402030411100e040609060315020a050903060702010c02100b01 94
    0x1c15610b0050351350017188100710054042504054403052a4640002c20848001f00900c403103200c0343c1c2500c0000350b080340344030b040380150790743d04a003d25250300040051801d54044030140200a10385082800640c0340c1c0794809a621404440310000c81606100101040100000b03c8403d45000c0c82a00102c081d0000309000c0540001d02031030319028035004550303540065801c0c2180c20350082001c0b4455007458044100c1c0e52040d140441d40d40f9010540b0f030b502c500d84591002c4c040c845840740c182d1a6a0070b1010140805542c65440c1da828000440065040401000145850030002da1a80010710905041084001441d8800e103c08042000031407000b00303458084940458005132660b5490412040415400101642c450388010303850150342e4020a03860a090425101044410b0f294440002202c025000c01307800e00c0c8046120120b03021043d0024030317043c0b0306840e20310b06028001021a10f410815a10400940d460781c1e05900055410040c1610060030810f00f44458100c401c0060300b01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 393459073 1250 393457823 393457829
    0x9030e03030903150709080a06090605010515180f040f0603020f040507020616020c120d03110307050403020d151104090c0e0d020f0a080601060c020f030606100f17010f170d09 77
    0x1318403420004166500880035107008000e904191008040f0f10301e814001010f00b80011180c0074500000450241000080394600302689040385103031401c029109034014100075151070707100b00da2001c1c2034603a0701c46000321550b02008007001b0400750308620402c420031480d0f00320240624607090030803001c1540022506d8100f031204101c6407000da0028003c070706200c0443e480030303080140384026030900d02c40012500181c94440d074081080b480c00940c2c640340f9110540b00d50000981c1408248094502400c060782064411080c40d0010901d0b221700809482036921090568280450300704000c81c0d0078002c04800c90344d28a0070445802c4180005070407501d80d020060b000711040c41a882c0503031507800140020300400405c4510541e50354500500c2e14204500880c000c17510703610003003828100041c2c56030081c140180010040400b8100840f4424040180b1034200f0585203140c0361800b8203600418040e0500070340c0900400d003420112050300c1c0850168400540c0102c0319510a41d0344000300e1815 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 393460323 1250 393459073 393459103
    0x50402070819050d0203040c050913080f1602030a0f020909010c080f2a0306010e010212090d0804090203040b0f090c01020d032c1b1806042d09030e03030903 69
    0x200301d41d01e400320fa1600401c000340009a200000b48424884052540e1003201c5084a0b80b065941d1014010b20f501403213400020002503092001c501c0d03031080302014124403211030a0800307040e00700750006481c142c0384200944400700d0324003080d001d60821010142d401303210900280654071810344002c01c070720740051108514507488400b00c0c0b45841c0d54400580180c8103400c01280c0c40303030354001c542210350064039114013041c09019031005c15400420b140031920f56859005003004171010510501c10070400d0b040b2591501080301140b000c01c1840511302803170060f1450300e0680b516580da4481c0c3c0e60b018000c203500c2c0d4001142032656030790000c0d4070700004920f45804a1000c10702d102d65002020421079020900c101c1002e445a08080018241d00d50440e40c0c101c0c03906601020144070300c01d80208080720034002c016000072103500307260b04410201c0c1036881070f0704001411070f4100200c01302658001c030003450700e13000d06005043c1c2c4110102103500088000c1d5203001326950000e41e90700ea0803615209 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 393461573 1250 393460323 393460357
    0xc0a0e0a0b12060708060f180105040b1c0c090f052e050a0b09030d17010b0702030c0a03080304060b030309280b0a050a021c050f070510060902070b010504020708 71
    0x2142c1e01d070010304554507400341c0700302d503020708201c2000742c000a021200140501079803000c1001c01d1501303906580d00c200c50071950301410313424031040c000580800c6060079008141100003d81e10b101ca0340301c10000900920b08407d410741805802001d503094104d05000c86414042404030a145502001074402c20610f41601208070100d00a010850349a0040ba4000c289460014050f10021b00074001c0780b0301181030b00c540000b14801581c10b0100c8280910307203200c0e91001030241d10115401498207074001000c80718440c400000195843c20039810417201440040240f00800030603000f0703c2c10300b503400ca0242d13061001c9400810f1020340c00a40e85003040710b145885822507049c044020740036217580c4813003a0740d03607030b0307905019001d94000524440180703d8604100103880c40200c001c0441130031540c803149404440030b074051480d0002d0100384c5650103814040001c0721414071401000b090403400250303c60100741003508061405070b000d540554010001c01e0b0005021800b110100745080181003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 393462823 1250 393461573 393461591
    0xb010306090e0a030206090703030e0d2a08160e06011d0d2102071802031f0f05030f0105100902031b0d020403060c0509010c2d06050402030c0a0e0a 65
    0x20064496a484070070040e180100c503840b421408140c01820354080d408482032038550b03e41050b070300c0341948030103000030712102c1e26241186040155070016a00521080e1a512040e5080c03130b0459004070201485075111850422202c0307000e1089103141c1400d2042e50130342c50300d06445507404680c001c05031410000001c40f95003e109006055002c450030103400c5003d12a03603458148000709245480340031070403d441803190240c0c03000801c9411f864020205903286002022100060340001e8480c076817100006007528001001c10741000020601400401107951034041490b04111125020350002c0c1d05000030806800c1142541004a4008400040c1c0d03950384e00a8075844002c1d00c2c145089585400143e9040055150b00a44240c80c002d0400f04000c0803040020b803054468100354a002c644400c260b540411034115414041c0da00d89035030015484140d11020782d0805008508458030313640c40f014070040d42810070040161030400d440e8004180c1c141000602e05100043c0f50101c4140c654042c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 393464073 1250 393462823 393462827
    0x30e0706120908070606091b020709020a090905070e130b090402120a0b0403030504170306180a0e10230105180a230711060c070b13020a15030e0304030804090b01 71
    0x240c40c0b40c0743c002600e25114411440c1481c0985407034828548000e0401150108107245400c8018403040d1640062510701c1c0b900d02c28001039084043c0000510014084c0098031036001c2c010503105204d02d90340c160381410a14100008412a43c01d1426901e181106e001070355281c240241e50420380440746002c101242a8500b0b141c241c107a94014507601c185000d0104041d015002103024030300c900d40b1041812441d0202030014041110340301c0e4002c150100f004820410880390941028003a02c01040d8406550182c1e441d040d4001c45810400d660b80341c0c4a0b01008640c5052a00114640a081c106501d0b040015002407494038691054402c21004610442c9440d400b00030100c8030020300d611103070700080404900c03c071f040390f601d000704901000c00c40ca18000402c40d1813042c1001d18040d42415190307100c00003000741c01040b00b410001031008000260307030b4810814009040c9056038a500d5080c00000600790b802d034040f8001541d0cc01d01061000800724810b035030650758001c000003580e0300c500d001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 393465323 1250 393464073 393464081
    0x207060c0212030a0c12020c01120902121b0a0f0e0f0c130902040305010c032a020a060e030a14161104150605130b07050c06160501050703050115030e070612 69
    0x100c1c0c2c010301c00010f040803c15005414440c555010b000540e10346600722030f069844c0e001001a281c0055032500e480d000003401c07070341300b120384c0ca00103003a104102c0087c0161342d14103420344000c41c0c0c0c4001c01d100364150300d241c40f6000740080c005c24000c0c081042e2500450a113624000b408846180a00300c0010308500c2d03000c01a50b8102c0202021580c406944c0c034810b0000b0340c0a40401c0e6070550920a0318401c2034080d0003402e00c5d0481c2034075103203901c14500380210301101c0060382c41c07021030156902d0313103012034100d004240d2900c04c000043c50b0350303107402440a05070440d07400041c82c0d0343d401440015154030303080f0554075100d5000f500e01c0340ca0f205101d00040003403007030500405200c4017556001c03941c254800301404001401040c0080c2040d01c584006050b4050f01c003000381181c0c0304225103d82030030a80050410006071b10003545092215503202c50035180111b603508000795503000104503001240d5208010800b4900b810040303214902c078074589030341d02c1d0b0140b44207200e003510000140341120b82c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 393466573 1250 393465323 393465349
    0x2011b0609080a0305091504031202040b03010905012103170a06030506040b07032016020a050a03050307110906010f0e01021608060603120901020a11130c050c16060207060c02 77
    0x1400c100030000342c500142c154101c145031200180c41c00d00042c4000000043e8014201c1d0141110140c0d65940e40c0c2c01c5403202d050410a81c4203d40900c0001031000011018601070304032030401041079810813502121f00070001c80342900c0148114920b0000c640c00084249004140c1402d10303d040d1307110000140070300302652004100f44030b860204401d010008050700c1c098140d1b1ba50500004c0d0345041e840d150410a44401d20b240c0208009002b845070042040b0403000e48068420501c65aa0354000381d03602c1090303402540c0582000515904009030340344640040102141c003940c850500000081184010b8468542403000541c02c460303040c1c5c020400000300005007141c00c810982c07500c03039803501c44900f550a54007030720500603d103844009240640c0c170400010390081c04000284d8507141c4007030700f01020444e040101041c01c24181d14103070043d80710302601b6844da2541d517101040c455152100d00040c1001070585071000740100755001c680d60040303420328a48844040fa26000041d0070400c0f5031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 393467823 1250 393466573 393466583
    0x604062d0807082d04050106080a1b120b0c030411030d03060602060f0f0f180a1118090c270709030c0602071a03070e150301141c02011b 60
    0x382000c03000d5214203242d10030201c640d20300c001030700c8030300d07084009011048002d444203a0900c480070707a1100070903455034041e004100205445590f240a1800d040d41418242d5481481600010000314641300ca000108111609179109114648480300e41d4032016010002c1710300000042401e00150907000c02244600034151124808015006402001e5520451016015903000681950300c00e440c060300c512070060341c540320340d030b504100b00c421910010030200c03d002d180001200003907010003076280000d22601400c80e5944081c0c08225510480c0080411a00b207014204203403208003007006c41c5c4201c1c05031100d45010540346910b49503045000400d103803000020042105071540881031788100ca010381341410300c16445103c100d8a0b0001400341c01c420020355100204c1d49140000219489400b5150502144100000007420042c8000901803c441c0110052000c2c60740718481221540b0f00b2107401801045089411098011100010b030501c134803128a1004440b11040c07004401e9404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 393469073 1250 393467823 393467897
    0x6071b0b09040b030102031603020a0908060103061413020a1a07020d060903030506100813020f062d1206040908070f06020408011109030618011e020301030203010b01030902060406 79
    0x36901030340550418000305200d1030074804000d8641c1810b00c02c0703d00805103042c2c11842c050b507080068001c1d5000d410720b5410084006800070b1181802d211580c041d62140e08007003680b00b8a02654250078038082c0003e034220b0703503403000c0d1001039a540d4100402c8446000b4080d0407000a00300f810070740d008250010350058031030400d000400206070b020184c0a03103e61010001500c8200500500c181c920300c5410100b06024040395030259076850030307015184001c1400d210000e2030b8001c2410b0f074002d440301c0072000c100700900070f40680c0c21140c201d01c842c08285030039044c0707880c0100d501c000d00070242c511809950b030780b1400070602148400311900d15802c9822204555402d20740a030080d4013502c1030300400d5287c415001d42c500d2051045485100004004050648403944047d0513011040c14001d8159a00d011340c0000030002107408422050782d0030016103940c5035006060075141a030382d0883c10189044e09010050f034405094800fa40c0052801d1130048030803a1062018252003108840e0310481 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 393470323 1250 393469073 393469079
    0xe19030e0d0f020406080109032127020f1504210204060807090c05030c04030b07031d0c130608030f03040507050301150303170106091a0417060402010207140d0206071b 74
    0x1c03000010b14500c01d5404210543c1e450030750600321520500c0040004240064100d90707035019000502c4d5421102000154502c2902c482c0001c000d58801c0143c41860704400c42003e620b0a01e007034402e04c1c4416291510714010b0a00240ba0314480c03030140386142c5145d50302284203494400d1054010f1a8050070400c186612149000e541c0c890300e00c43c00c00d103103061540e0a148184150140c1e40151074000402e400e0078103580e40e80701c0700400144078008255841c2c40088081c00d000a103594201a004007500e6000420824800002c06807098103407050706202040203800d200104a482d003110300781100d80c603078603140f50090030013600c0e0744026070640c04c0c2403002000c070302500c00c0d8400300c03071003900c0b105491401c084043da0286030910400010810b951410021804a031a0707284c0d018043c1e0700850b00e056141d04481a00b80311025102c101d80c0c0c00902000115601006a0405807050020224240220200003101c5a8031054020300500c00800d00404000e200d01803d07401100c0381c082070040c1a2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 393471573 1250 393470323 393470333
    0xc030309060c0412060b2409010e150a0c020d05010203010906050913050c04020a05040503030408010b09091615120c0309120c0803060405040f0b01080f0d030e19030e0d 74
    0x209455003a89801100041034031040d06030100d030211a81200d88581d5600c054503424024030101c03000039080620070803403910298822006114910380000c0d80c03921454017130001404a007000100718011b04543c0c0004c1914030490b02075500549082c502045119505d101044030781111220040c2071350f00100004c106240203401403401e484054641003107030741e20051001c0004c4412180645250044403401c0d519081507002010060714500f8030328070f00795450020074650390207580000c900340d5503001c175145c41745030113410389402c08141d0000300b41c444001c029071040c12210380f1804150a11101000e09510302031555101002e504060030403406002c500090040e1091580883d100e07810900040781903030040ca2240440c94100401031300350342e82d14083c4001420003030400d5070002c00114690300082c00303151506000c3c1c8003c0340035010745910075010303d00c0c080340d0100c900c06160a01c00310003003903e000101025030241010310040c0c0502941815184002d00000140e0440015605081848 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 393472823 1250 393471573 393471577
    0x308120601170f040314210901050c03010f09020d110403033b0f0f04060f030c0b03010e150109031e0b09070b030c0a0215131e08030a020c01110c03 65
    0x140080c1c80d0344400b050200c0000c00d50802c101c4400814090500204010a110319012100441c00340c206624241c5030140c1c0503190600740305030358401024981080881c98080c000e031034018020050450455060850703810348500c2034041c040e2855804151074030303990080e1b080304d40f440102c1c417040c6550341e843e81402012207038a5600008041103822038050010800708182107041c209000c4810351100010030000181e43c00e100c0203500103900d042c8820a9515840350000410850140d581d0181c43c528110f00480075690054041020501c0100444044090f5855001a400d00152000034602e00141e4040c3c0c4070740c00c040e0143d129419403210382e140700800c1880440c0152800e03145a51010034281d03039030090380a40201000180042040074100c0307000f815140c030450040e00d0003c1e00c030703040c12014005c08480c204001c4071410140c0050080f8141e8000f915150410380d403c81041035225031030244030141480d001039600060007182c0300d00c2076028008200d00c464071a41d41c0c42c1005c40b0990b0325 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 393474073 1250 393472823 393472831
    0x717040b06100e10030e0f0d0522050d08070303020c1209130209030703141f020406030f020a0f140c0a080d050f1005040207030905030a12120b090c0a0207030812 71
    0x12604250b400303004501030407208001c9080140f540e00c0440b070700c0c0011030141c0380b0808020054801c80c2802002c5840900c030307060005410b9501e190710b441002e0690060b0304488101110380e07110039882404582c1329401403c071301c05d400044141e990401e07481d044009100e111300400c0070740244016007490100000080401580032600c412107800f01c0d4004004910881d040b00d40d042e409918100f000440070b6603000700e403a80e0001a140c0100c1d20840700c070354001040400e00c2003154002030510030150944217002c0030200f5180210308140c600c52019208412651000c02840a144100340d1030a103100c0c1102c80246180d001c4d1000480146880d00a039004001c0c20b5018604040004104101903c040b9104041440d101c200b1140750030203000c003c3d88202400d60030015140404035a94500304040b8941d2071058605c100861803041c2c005100c101085002204682081c00d041480c2d52860000381d0454000341ca581d0390354090840c01c0c0d02c0c01d086a4001024500c002c507040e046490010322142c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 393475323 1250 393474073 393474079
    0x91505060604121712100e0c040e06040f02040f0602010b0f030c090a020c03130602030702090703060506070201140405040c05030907080d080c09030106030803011811030105180717040b06 82
    0x140c44600c00c0003400c0c000c80c003400000038401c03070101012505503100c00020401002c039051034040700305000d000c1804200d544600515418004000000b86c007080158401c4000702c025080c142400718000000c00c01405091282d602ca84400d1a40716490781120010000c1145680000d80e840201a028000d02c0c0b43d01481640c2c2040451480d08010401c42c20741200144120b100d5603504c19080000e402c4020991854402409078904c200350502c2040042e0410f07030020741c9c480c1d40c07a1041001980006041c1c00406040c0001003140b81c80c0c40065481407a42400d05100950541c1e15050707090040340e00042d880307420548a0000c0c20b410038001d50007900d5001c162104180ca0700c60070395403107480740208000101c031000002e101c1c42729100900642e08d001000428070350f50f651510307489500280c0252644031900000000c40c24000e100d49040214002d82150039503150200044070703501c80c0c0c400f400c08140f0503c001030055104140c2e1100b5011480000082410305092000310740d1800c03141140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 393476573 1250 393475323 393475331
    0x10807090b0f0a12031701030303050f1807050112020d020d020702030735010e01060806070306060e0306010501051b0a0312180c0302100c06020c010b0906011b08090a03060915 77
    0x415400d1699140c9440e82003d860b42c008245015001080c41015510030b40400c1041014501031103101c59a80f4000e5010b5038022a207814060200c0740a1000609070401e5a01402041c681c81c0700040b80b0841102e8090030300d040d400303548040d05c001034030030310440c400000c1c4001482546620a58003500140707000394203c030b03030154a5000610900c4800400d2100c0c0c000a0352200b00d090180c1b20152842107031100011038602c1d0003405140c203484054001890680104040240c25070f81071064200920751071400c1a000c40e03141d00440c0e140c5206010f551704220303001810074000c51840101081c880d00080480b8102e8441e400c008202c508004403801006042a22441040329042d41003122070303800501c200c540718950307403c000240c40c100c2034550038410400030740710210304244054400301310f88600100740488450200702c80f005004040c6818041c007030180030480e07446100f010b1203d903030200c2800d40d600c130032800240103800340740c1c0001e108500304456041041203280e100d044499800320148 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 393477823 1250 393476573 393476591
    0x30813020301240b0403110907050c0607020601140f01140c0717070612020901050307030f0f1505090f0103080304080a02120f18010f021b0a0321020f03030613050411060301080709 79
    0x900d51217680310290040c0401e401507036861070911100c40e00b11481d4100940703003034442c030005401c200c801c842030005600204010070080e5103041401070620300440720340925542e00300002c1c00c9034403840390307140640b080801c00480c1d2503400c01884014126103080e182c201542d1000c01c580d2014a07005200000f210103202c0d028000316030094602481058540500315a10030704100d0003441c4c086000c64119441d0280f2014003c2d29201d01103000001c035021222890400c4203000340050f02420003d10280401d00400c007248280e01601d0300941d0106855075a4404403400b01d01c0d00100c0d10142504600c00603d03041c1180c0320600504203103400300c1c0c0c10301c5003071103100055402c850740c0d45841026802c001600015669011a001c0c106007004041c000d204d607d80d10350000d00b882c01c007010b1286290360170300c5588003030b010000c90814081c030700300840c690f2612101058288c82400090340441d071b02c54002c101001030032001c1c020071240c06441c40c0d03243d40e03444d04940c1d5121140d1045980c40c034039050f449 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 393479073 1250 393477823 393477839
    0x4120302030f0103031b1e0624030b0a110a08041203060e191d0102040512060c1c0209040f0b19121115040806072a03081302030124 58
    0x140c0e22510780002d504003140e1030741d1000c0d41d0000c0700040509044045200d01c0d0005028142c3e00da103828018080301142d40c420f46002412102c1401002000464040a2100400071464120f0036280c0c07003102011644c403848455000783c8150607a401b442c034004503005052951107048140b081e40120b01a02c0c0c1020035000940444446010710051071b1090800103613003c2d58800890a00c0c40714040000d0506042ca100d80b00705201e5803948519a500050100304624001d27a860954040d400064022030401c150b2a41c40e038401c0400554a0815030000110142c580f6419074a074014003030300c2401a54a041c0d028401880441030300c40c802c80c10301203161150810f14455205454208806070407500c0c0a03140d607400d0780071409200742e1003041720f00006035109211f40500700520000d001000107040c940c82c040c140032120065400342010a4403204041309101c0c400d1404107070541418a200e803140a900f886092020b480a07400d50f00f00340e40ac0b41c50300850143e20300c140030803880400c600b988030088 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 393480323 1250 393479073 393479077
    0x31b0306030c040507050717071a160c02060c031b07080a080d020c0c0d0b0f0a0b0d0209090309060f0306030d0804031722050d0306080c0607032307050604120302 71
    0x394040d404401e806450342010f0b400950064040d04160b030802101d03584080188402e074102e902a00b4000c21580100b1004810b901c040f1100801114458a42090300952480e05441c1420802902119070000c1d5126842140c00d21070082d81070f40d645600300742c00500c01c580114040d022501c2142000a038081001c60074858141d400255146803440c280280e1010307410100600d161401b803001c1207403460740c0c2d8025804441b403240303902c000300f490b1003200621886030091440c0e80180c2003940003581650f403415030603032441e412038001d030f85034070741400c002d1450141e100d0f880d4000e100058a0f441000042d8042c51154800314200c844208908208803a2080c09440007008104442c0162548800480740d403540010384903001100c13190750380d45400b102c0d0007440302503d1035040303403444c0152070750305000d108060442c2000420070b00d200320000c940180709094014040100400e140c00b8103c86400e042500710100c070031250348034459410481c2d110142958221880c0c484040089200760107802 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 393481573 1250 393480323 393480331
    0xd120209180411090403170a0b09010306020d111314040b060f180d080a030e0f0616030612060c080a150b0a050c0105180c0a210201020f01050705031b03 67
    0x8001c032000e07000c0c0074049401e448003a0007261040451506644180c59400c051403003980266550140c00e2069150ba03414028051704c00c0540c1410100000095110180c03070724112079020342c005917500111640040207001c0d22100705594040010800f941d00a035944100648a000307e030803401038001c801b00421500075440c01e41d000081031100c00f18404001c0058000e44504152000d42c074200c000c00140c4071160500704960030440811000801c41d850b208038a162a44070b0000d200c81c007044041c05580703540c0289a00400e080b550802c80c00c0301c0c4250410380051140031036480c4a1049450080c004d0701070013016000180c02000050900030003401101008031401c80d8140c4500d040031058103c1c0e41c40601c800c01400300402c0340c01808a400d10540303200e04e1500708003425541d08160306900703094400305c003984912080b42003031118030214110107001410b4415034501c1c03400544010307402c181c0f0842e4062442c0d481c0104229a90f03401070021031095650130b031f07900c2c0005504d200384031303481c0000d803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 393482823 1250 393481573 393481579
    0xf02160f1a16110102210d052208031e0115030509030304200a0b030a050f01090b21070b070c1e080d0c0303060b0d0608010b010507050a0b10170d120209 67
    0xd5064004905151843d60b070f92079062064408031059016044e0458001c9104001c0c42140040c5250540c0e0440c41400d400c0102a080b904100034800a024004032002501074081c0070004040342e42504514401d640c803280103441c1c2c001d03541c4d450072820340300d150b1541d0070008a8100320020b44c0c4082c0c0401142d2040d07510121a104070284881401007070001a410b150304415450070208515228801551003064000404625450203c400d106d6508060303000c455041d05110029510740c7d6925a0341c3c000501c40c0088980d05008010040d00d0582d1961100c1502d0400241180074400300c81c01885c191022024002511161401c2c44083c2a255100d02e8405421416110061a03c1510101c0d101c0d8045d00d4080f072800e8842002541d207610100704014460b0343c0c2c201c10041824280103c200038603003402d246003042000d40b2010f4564481c0700004103002042c0d800564550702100e4480041d00b00031494000680b4000502d0759284d2035502d415010131000106491114554022600752442c05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 393484073 1250 393482823 393482857
    0x114010e0712050a0c030e120d152103080603070501050a052803060f050906030604080d0e0a03200a030f030e031c02130807030c060f02160f1a 63
    0x481240e03448100c001e8070304010414aa051401101880c0c010207019070f01a80001030103a10b25200613080ba01f650f5010b540039000f500f9112200e00130101640c1030002c1524011030300786000c0c030a40710302d10220341101100c1c1880418000d88040c1104104016502c651540c44407520b461301050b540c0c600300d01c1040e00152040180c240014481d9015001800c03103102c80030803642d1070201840b14210040740d0000080e81d01e00c81004448282001100100800d40d15a1210304019012035110b0500a0015010750f0000661100104045d840403450340d4403003080e50041c402c0b85c540103120b8104145800c0d8480040302c40d003030b52540b01090042c0802d0b855120307460001c0200c107007036029148480303101c445800140001d003008522440d03802100b178844640140e40e00b100801c0401803546079041583c065010074000e000240149415505450041c14800f40851103410700300d26103801c0c00c1007004210003100d00007540c80d48440c0001c050f58211001040c0011240c1e00c414070b00e02648403c030ad05e040607 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 393485323 1250 393484073 393484079
    0x80301050312030f0c090301140c0a090623090d06061d01060503060f1e03010f052706070810080a0308010302011209051b190b091806030c13020408120304050d02011401 74
    0x2100340184446c60010b0004030f800c004440d44d0046210089907050392002e0002107007408031f41c1c400320010160106050000e07040c900003880d44440e44404560140c0c103100020182c660342d6034071076002c1216611640501920380c9034449075100e04d070080da4a5030901a0800003090180c020402da0340704060180951806144800c10060210384115022400711040d203a43c01c42030b102800b5074000b000040c2c1c000700c0c05003411181050601000d1086203c400204d9180003080070010a00726008015440c01c0d48150320f40c1c0750140241e1456a004050504c1059174000401d6009204241228001d1b05c540c00100100d00c120000d4400800300102a42c00851039011043c400e03010030b944c07a03075000d8203800e0688101045a0322807620380e0400c80071400081110780346442c00d245260307868480c40140008504001000c20340d61442204510310500b00c1d54000c0300c1081403641a00d000f0204041100c0c03884082d500b41e0880d0b54000d03a41900c07280200b4140c901d90078014090411a11004402e065881e8030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 393486573 1250 393485323 393485341
    0x5070608150d021f05041707060c0803150d0b040b0609100504110c011d06070c0803010501050304170f07033f0f0c2001060b0f0c120304080301050312030f 68
    0x300d418040760700258281c8080c842000312401004d09840d5070f155541d495050541c0ea66842a0400c000f01841d032102c1024010294000d008204080c0e000c2595601e03601c030550241c494100c200c142c43e40011512009201f8481074a10f1140030703c2c0115042c61440c1c96203030038048411411580e000e803040b2200410072480c2040e0740a122540c0c11181860b0070b20301d40300c0740f00d42921420010b50705400700c80e41101c09818024031141e41c00508500301038940c000266502c01040c0414442c09041c13201c0400043c09000e0f000092075034145990b004140d55080e200e400317904941218001f940001e060340750706080041220346280c001c3c0c40000d01e000080001307040d421802c4050502e030703a48243d192410003002d038031140030340720300c0341c4254907008802c5900d201d0038841101c0e9144c503148142c0c106101046283c2a103401c0341d440c0c000301c90702c080e580d040b62042180f800300750144248007a0f10000802c001c0c04880005181a140104c3c00c5d074080140010304000c0d1800301303030351401840c40040e02080d0082 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 393487823 1250 393486573 393486589
    0xb0114121e0c1216090b0a03020d1a07030507090603020405090f18010e010c110c0d031b150506040e0f0d030203101508070e01020a08070b1503190507060815 69
    0x45624202e504020029000c1812040c6403c02034640368400c15010070382001c81c3c1a40800b42412140070055581500c000a12255441c40040d02461080400a05208061010000c0400e802000b82410b003014000200140000c40f0301e440040c0a5403000b2800c0c0c1e02c2070089408550009120a803152039003103103582850009000d42c540310a0121601a41650170700909940058500c0005039401940002500040190307086180c41c5e08131848094290307803203191002080b609484c10000c001c0e101c400444070a1040c0c07001404031203100382010600720558004030320400040d542441041c41c000e60031513940501d240f4a032955001480300c6100d50703120760702865006082030003040f016aa10a40f0054004110850500040d4602c1c10881010b40004010690300800e100a1050007015222240a0300460500500c03415419000c68198010416041d82c001c500606994462801e107500ca0030390028018100c41c2805803490004480e8080c001c441cac4500c03070303882010003140e4001040018032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 393489073 1250 393487823 393487873
    0x51206031c05120705070b0a0c030f020414031501031205070219060305060f030304050102210928090b010f0c06060306020414090c030103050d1d030a0b011412 70
    0x240c072409240e07401403a41801d10a00020305519019912940c01e03802948102e8010181d409005082044800140c0d460743c00c950b0004c038042c00001e504050800440103070007040810ba20281c00483c01185000300c01d5160800d07484220110350b1900102c05002018420910000d803020141d0460100d01d18000c40083c0021440100403c2c0551205807000107c1c264036000100000e640c1c0003081f00d50709060240d450558000c80c01941482d2030320700000d5803100d01c04003501520010403011401a05064152400544000d00c07692554508208a421700760003040700713005000001c07000044290080c4600200d000c0306948885681e200d0039030556003804032007411100550b0b202c10000100f492440504003800c040c1c04120342c0105680200b015030b80f0007900e0816200301c10001000021070010ba002503002c02400c044c11180ba610700601901740c5807001454040c011808608100405031801c0c9040c3d5141c808641e07010954001807000c81e00b0210314004c000d0b401108a4040c90007210141c181d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 393490323 1250 393489073 393489079
    0xf0f0a20030a03081503160b0d020d050f0415060302010804080702120f0607020c0111070306050c070c0305010504150c090501081915060207050105070807020f0406080d0801150f051206 81
    0x103496189010038a0070141c0ca02c16030002c0c1c0c01344140083d1080c0e03440d8209224000b02c3c01840401100d03d14000d45008502c507007102104001141c84500702c0c5034064407284000184108031328680f404910320880004c850854402c40c64002d4074400309424800d08060f0783d01a95400010707515680c03642403036405507000780da07c907116079050000716804204401c0264889070181034a4140144040c5c60010102003060510004545100d90400e000030001c1c01c480d0003c3c00400d02d526107201030f18a602c55802c0103020380703450620100a0200541215018038481e8080800010131703c0303604003c03514001d01510008500110400a640c840c1111540124a88924620b01003c1a0b0100d0496103000392030501c0000741c41c010401245c051012000400307007820400e161440665a104440c070030705800170720034040407046240c01e031a07981c0243d0180400d8000c89400302c0c21860041c2011710244240c075400e000c01d04803412a10720402001d0002a034949074242042861180480005002408250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 393491573 1250 393490323 393490373
    0x1d06010c020909010b010905060703051e0415031e05010806040311010e0a03020a06111201061d10111e1203060f03031b010606030504031b05100f060501020f0f0a 71
    0xd80d580e82d40d0360f0700668000000050700031005c40090b09103a0300c1d070304c00c0d031040c4424017035071020035084400c0740d200c1c258a0511003040007039152114020b00131a00102212070310f820010041c15019445420150668203081000703080318800b201c1a01d9090095241d550406804600001d026840d895040c0109100102d8029000030106140c501d144c1d00507001640301c03c0503801480502d07c00c01c210030080150191030940050074000d4060703010b02c100400c00c0003405181700045000c19803c0740300c000c000c041d4400040044c000030325a44c1d00d011001920f0044c80b8903804115000080d40c4011300085001d4000d43c404e41d10012500d4000600c030a0704050111141d00c0d41355402c0c0001e1600241c1e000c0d040146c48101440c0c04c0c00c40b041a0401008d0500d00b00234040031907005500012400941c48a42d4420030861411908000c2004660781005c0d003032501c400c0b103108883d0095402d80301d00303900702c80509811403a80f9584480c080c241c94040d41041480901082e01c03001104a0000000140c0c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 393492823 1250 393491573 393491597
    0x14151b0d05040303080a06050a031e06060b030a1a0306071805040504030f020f240411040f021908011404110708071b05030d02060703050907050a080604030212041d0601 74
    0x90410030350860010000310005002c1c0308054101c042076401980e4a001049124241b00100c2c03444c0580d408090301c0304c0050b04032004c0241d401407008942c19330003c0140461942d550034420550802e9510010a40c28909140c5628080c400d5035001013100030010b00507511038200035210010079400d6600001405c80010429885500a0710301840c402d54407001148001d444c0241820703808005401a90013a2030340c94401d480004000c031110940d404d41100b6502c0d07a1410501c282c040324001030700a410885900c004403020340c081d146002003901c89230070310f0403560011100c00c9001d000307050f11090f029007401d1660a0a03404045c64851121400c0e180110f95210304c402608280c008031042400145001a04624420a2030051900360003d02440b111302d10040d40300d42d001400c0404240d980d0001440d051030400811008280162005201a44448080c0d44644049400390302500c40c202140314008030240840d001c41d0411400c1e00a0756403e2031080540480c05021641040303080102e41e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 393494073 1250 393492823 393492877
    0x313170f03070c050114040305030a03051e09070801060b2803090b04080405031218040c031b0203070506070c050304060819140402030d031e091b08030409061415 71
    0x1d00002c3d00441c02ea050041c5884c000401d10b030000610303e4560402800200001180042030760b130050070604003c511030b41c1d00f840f90b440b000c00c41c0701d0040d403c081084c1840b008110101e8a00c00740c070112002030040b01d40388c61f203414070341c031420305078860040c000d0804c0d206c080c0c01034000b0302ea1540c243c43c000c11204030f2500c5800842c00c054600b6581c2c0e150011301000280350401c19040b5210f1100e202900f800e42034001c483e04c060030588403500503502d0320900c00100340b00c0e40c041d2071f10200040d000510103000c0d0358006d580e0b40103c8000c950b944030350404529024011020078010503486070044ac6001d080132030484401802900403001d1204540d02c269282c0d0307103801008080207650805014514040c0101850031002c111500d040c94030b030007492105540ba00400c0c04111000c048042055491860002c0103d07541c20303480503200b0403160000c1040300011005000b1070351880c4040c4846034645210441905100e41c000303500800003800060400000c50161a10032404281e40c0000f608580007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 393495323 1250 393494073 393494077
    0x4021207051c0f05030c1c030c0503060108180304081005090a02090601140c0d030c0314060603061c02090a0c091a0d0c030b0a0602010b03070902040f06110a08041d01080313170f03 79
    0x2c41254001c140d04500700b404052101e24021f01c80c2c0303401c0c48011800348000d0981e11000d40041d0410184900003245000070a60080c030040e08907085903030f01c6070b0701d600d440e8030340424036402d0304080c1c00c20000c20405030002038048011a002420020203403a01303401500c8400800c082c0c1d012240052142080c082ca06004407507503003495407004508143c00450040c12a866500364030b640c071401c101440940c3d1680030540c2d52110090350362640c10003003407048040021107010002e51080104007004441d8260f50803004100629403510004140c5030707094002c1c182d032a0500c140394401c0501503d01e400105402c203d250300d415007000102d6904200101c2d84000c904e810103000343c1c0d11a041100942020040503008090b291001c50a00d400d20240d0000c82903507101d01010020016100303181d021042c4441404964805c00007544d4564507000d10700500c03005031907090240310f81400000e542002008480c2c5040c100c0c44007044060408c4a80c03600c5c00150b82c0000c0c0c403803090460b4901b17a07140401c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 393496573 1250 393495323 393495337
    0x170c030721111309141f0905010b07020901060804120c03110a0605091e0a021302090a03051c0f02030a27091b0302070b150d06021204021207051c0f0503 67
    0x80201d40e0740b0400320b401041030f402944042d07865850301000c441200c0020070200d41006841a417400304d5150f40d45c44220f02c18040e040103024608d00000091103042e0354000303200d058800d40b40f03541c003680d0701c14081e0f8506100301e80107811032680c1454941d240b07114090582a56101c2d0514010640b00711002c0c07860508150004c5580e16075400a0103d008020002013000e482120218039400c04103551142e1079010042d0001d00400f407641c6c50707110400c1160150780c4494000750034071102d00e60303a081540d590488030106d0010f03031080f80054031005100b101421030080700741e00158a002c2180604840707482994040c0d5441841760140040300048856011000701103144000c45e481c0c411140c1d4941c05400807810600b8940304000b15400640c4030105144e001031601c21081e4514807541c04140c1c50100304100402161000610880400105c00018022402a508113428080c01030300c0c43e41d102018020b059001010024000c10b030700351510b28641c00c81c81140340c10642901a544c00f440c58005c0c40d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 393497823 1250 393496573 393496601
    0x1020f1b0703230c0f0a050d11150a09150c020d150c030f0501050604060906110a170a02101a040c1101090303060e091f0e0307020901090c170c030721 66
    0x80003006034007010010070b00f142c03c0c101c52819034860004001492841b4910400740600342e45100c0c4d50900c1054100803020300c1d0003030310007060700400344406d40c4154032010544d40800c10080c00491000d45403c9401c008100e1510b030464003117802d408000403000894021181001702c045440c080c02c03118045c0068100f807945000c43c2600e111510ba00607130701d0580000d40251000d1000308071507075011000070100d03201d50a02144c10403114041900f0040c0f40d0078080c0001d1540703161a0140030402c07004006540142c1c2c02d40715031521000070202a40c5211900c0680c030a4500146025460503500c00d008400c05800c020001070000c030405401e44a8145041d40401c1e910a8101f00c94100b60500307681c4024800c01619140110f0740b0303580044070078a46214801c07507594040299009c420800c40f0115a001030441ca815030b0750340c4080c00908008101003000030402106a500c2c0080c614401d4000c003402c1c809c96065030f4541d001101c84030844207034000e044a0118010211070f10922a49a40308405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 393499073 1250 393497823 393497873
    0x23041208090d060b0a050d021c330f1a0405130605090307030e0312070f03050708031021030c020f062a060f012301030e030a031a010201020f1b0703 65
    0x210204125010654410387c003c800050910005030f0f0303180c2d03070341020350840190200402d103141800801200703030355607180000319003407101c042600040da03a180800020040a00202c1c8041089c0e20554007070110407289019280c42d038651300d260640003ea4003001018000100e00041d0315002d0036103c0694000d1507503000000c1000c01d03d60b1010142c1c240ba00700b41d0040c40c0103034007008401c01c070780305020000e4240d1800c0b403000c1c0c04041c4141c085a64994202e41010344a06019100100c848040d10074041c1001e00c0108010082d4a16205003030402e405d501d4090710300701181c0170b00c8071000c103a00f08103034890010800c40171500302c40617403800c050740c00030740780d4901101801d992403400d100a0a441e04105600e0010801c603150504132780402006201c002001110f5400140d000c0d19503985000d0290202080b1201c10380c7d8160310804e0940c10005030f55400120000042e0b080b4802c503020712200400800c0162100804105c80164640c407200448404565a4594400160702c4140160301807100e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 393500323 1250 393499073 393499091
    0xf040320420d0903120c0e06030a020f040312080601020714010207030602030603030d240909020f06070203011b020a05060a110313050c0307060801051905100c050115030302030a23041208090d06 85
    0x1603c500c0144400f103040628610a24000080250000500100483c4c2c2c0013305030103440d40c0c081c151402598400591030707030400d04000251154000b04c502d280144560070000075202d6080c85032140d0014180c01801d1100c0c1180c503a00080e5000a000c113030140b0003080b184118180078402d000e50922184a41c009441e6103104440c2c5088881e80144000c034102031407100941e82d15084841c00c4070049503401c0e42c2e440b140c4042805030801c14104020002d07480101901c95070046842030046201d001550704664424070604122280c0c5840e2071015502440000c1c00340c401c91100000c4903005104a56442d012413001a1400341e00c2d0300404009400000100300c02d0802d1041c070340c0c0348a070a40084212a040c00041040c0048020101042020b003020762414010290b00c0201001a0111007284103a00c0303003400b0703507291721101e808030008074480018020440d141080c2d5202080c209040c038545031800040440000c1e0203141661151b0040160003c560b80310f05040107a540b0421020412400d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 393501573 1250 393500323 393500357
    0xb10030c1103090102030a08071b05100b0103091505041b23040c0e100509030307061a090108060c030403050c190501150f09020f040320420d0903 64
    0x540c840e4108041e600c2403003c028183c1e00031082d2a54504c0c58944003000d941c840b0030490701c1011205d0102c0380c161501201030103001c004181d00c3d00d0703880100401d000385058800110100c4410351009007a43e10311050b0914208950b42140350018050000307546500510705c000303070031840158400480d140480c500d901c00461416400c1c402050101c07002c11144404001c041c03c500d0701e40311202e00c01e64811620403a100d024505513800c01174064112038070355401c0e02d03103013004004440309040307030a0408075124402c3c40c20f003190a0580d083c07000a40361a894078402d2100c82c1c0c1005e08102d080c4441807100d4142c0d048100f04894901074810542e058941325800c00d00d003119550080c07407044104101042c04000e00e80450581111001a801a5200301101411426000e0f5170001800311500e0f03e0085070b0411000e40c640300d05c00080b0760004068410340102d42680a0010a09a0110f0001c0c2040c010550210542c9a24211074007114501104996a030085402d84541200841e902c3d008480c00e0760 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 393502823 1250 393501573 393501587
    0x110c06041101110a17130e150d0203030a030504030c0609050c0a08030a050a0806030c04230108030418020a0e04230901020a02280204090308090114012105010b10030c 73
    0x1010a080460080c88030705261502d0b003031440c42c040c00f0141c403a50000005d2083e1400c813841011100789200b03e46444500c0c1596408003910b40307110f0b098a03003481c2c4a0a1070541c1c1e20074483e0b0b600170002e5190000d400780070340150500070420b6083c00004420400403a081d8007503003840ca0f00c036102800701142d11600b0840b18094681004003070303034814000121190340103000c4852102c160b0404181560700e40002a1a0003280000c0f550021304190313002000d680c90707044603401a20924240a942c1c1e0301d80c1c152550746d0142d481036a0403620740145080341000f403580182a00751070352400e00800c604070b8004c1800c2c0c502a0a220034aa1303450f041050611401c403186580011120b0020b5140c10b6480400a55542d0310707600185110500950b071018940c0360002100030240d000d4418880e0500d5810007900c10307041103600f1140e035402c02003003016008a070030159058601e1001054810f882410b5581e030040c280d04e0081b10690750350098150f40e641c40607800c400708000c994001c80c1900051b0b800810340c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 393504073 1250 393502823 393502853
    0x170708040527011707080a05011e0b010203030601080a02090924010c0b070f090f090902010f0c0201020a061e05240904050a0b0703320c07020108010b0d110c0604 71
    0x2045034191180a2401600340280c115541501d0213813440c80f074001c415040106651003c4290b00c5950800000c214064028492400000c0d000c2182c030002610040c094641841c28a030040c0c004100040c81580070301c03030716500640d0760300005003441001c8020520310706090303d01441d05032000004004065488000309075602013880e08601a00031076842c40d45140c1c02034101c5e0144842c902c036200000d841807003880020060855a80310141d5031344142c2004000c0244280e00060301c1c0340358841d921b40584650501158107030300818501d00781d5192800142aa64540e0800c0385080e00e41c0180c4000c5405028012a10700d000e021095140c13502a01108013020300740d07405030b0140820031000c6a00800d038201555004a0020b80c0e607500e07868100c0080804c0c1c0091241708250f0001241c1072203113115070300404131100e0f0154515443d400b40340d0210303010b40f240003400241030100500200a1100c05000156035040700401c3c61100046441c81c240c01001000700550300c008100801c4c005401c516440d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 393505323 1250 393504073 393504109
    0x150504111203072d0f03080604050c120622060e060f0315040507030b041406090f030406051c1d0111090d0201030209010e060c01090506062b1707080405 67
    0x69400720710845601c90060701c9010b018031105070000601d401040003c81500d504200f80445040000d01d85450980c40c0e20318181d0004114030009074003424140700d0b0310f00030304503040c40300d08004020b0102203a00e0001400160025482601c0420f66400003858901c401020b48010407210f08122407074242c1301c40240091b11441c180c042106035074401084c04c0c01d080e00d4040c0641e500e0340c0d903803c11510b822601e500042003405401c007000706114800384800c03c41c04c9400180d51460301c90740101d0351796421464250540d030700700304002c01030030307002e48000d10308805824511910700c1c0d0122910011946000c1c03510051442e010300a00410500303200c2e00e00b44030081888a0304054400000c5030b02260781c4407000b41031580c0001c1807041c2d44e015aa1201801000918241d9030341510f25206002e000314907412200c40c42142d0100e03880717103070140c04114600c86081c81c59007454005900c0e1000900c0c8100191184011540414001c44044004180e001d0065044581e114504424007010226000c0c00c520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 393506573 1250 393505323 393505339
    0x3061d011d012003070813150203150136080312090d030203010f0603050c0d062309090a08030403180906030c0b070215181201060f0812040303030c090315050411 71
    0x3c0c1070b00101c820740350000800c0c9848150365a8084207401010044030707010b08141907040f0310302c01c2c404d00380c0c0046100c1c10340c6190780c0c808442128019117403424184541c11101c084004040300603554118402030104400745101085075842c5501800c41d4002c44144444086101c101304860070b003040444101a414642180342d9850710041500801c0d0a01030f1504040e20388000c59a0000039500741c0304548201030302001040d079501c20515040c00c0714003881c124544000608845458100c2c085846110880041e1008c40b100360780c0d01e882c45e440140100c3c14854800e8100401c0c40020341010301520707056100140303031030550a088440d01e030a0313441003800c960104a40780c01a25070400300001c94640c0c0340c030140c88060341c400c09078005000c04c00060304031030440c0c070054045405420100483c0e2101030004c08030754032170001d561161801c28403d84202810041080041d110350701000d0944140e1a08200460b102d569129400e00c00c02c2040b4400c503150801e01040c8040c03e51070072903486d02100da2030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 393507823 1250 393506573 393506621
    0x10e0105030d0e130b1f0311040b040302040c0207120503030118020319110421060501050102010b06121b0c2431020d080d061e03061d011d01 62
    0x14003204030700f0748950140d0580ba0002c4409166038108a01e070010040c030a01c50000c1010007815480b4454642c480004d0502507402a003006401c00c0b1020341d07906a00c4103140505507000e006c042c10301c840c0f0801c21403180b0800001c201c20185c170652585c502c03482c050342d41d070b51403d440c14608420802c503000c8900d03c10003d024250300c44044d0a419002580808910004141e040001500071940031000803000454903141050040b0071402e402489440c0401050340c031030004901300c1d01c28004591700705004000c1640351030224200395038408610040710007003445032049106e01e07400054241025600c08406100c003d21b104605c10181926451544124900600c1c3d00850113501d0848041e45000c1080c4a1203400440ba00f5480c00c7d50094009030081410745840280c65120b81061290103280010110b00f03030551805031140c281011003105a00e41c1151104401049541d1550700c603040900403c00000f41c003070007004840741101c142d002c0c141882c50400c03420b51b10408209131a243c1010703418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 393509073 1250 393507823 393507827
    0x204050d1e051e0f0a050a08032809050d0f02101104080d231305130b03011a0a08060c19050408030c072c0402040203060f1305010e0105030d 62
    0x80600c0641255146494109401c10701100810040014025000741d103118443e070050000d0104240341d24504940811582e21344898030ba50070000003c0c140d401c4004044049440007018541110500c1c01e0800c07d482d02c0010100d1941c5844040540c45465200020910034203001034040017405040c84401d6a018400083d02c4140b0b030a04110203075514055000802e0a8805a40142100c1c604480241580223005030103045011000130202408914030482401000f041d11585500c0000b07200000303007410100301900090401c2060101ea542c4008521a41c003401118508031011a1030000c1148001c140203040d480d0fa00008003a502c0b40e0288071190b076812003125096001c10820503012851000b0841e054815076000c034000b84400f00d2040403610000c1088011950307183e01c1c40e41e00d00c0314104d24011501d91000c02c024400d01400000e805403c1c242c00850340003034014140e01741c4641601c0011050000c410742a2009a9a00d005001140d48020001c4c0501403c6000f0304c4210f00c00500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 393510323 1250 393509073 393509089
    0x3100b0406080f0a181707020a0b030a0c090b040b090d0209130b090129010c0c0608091c020d0f0302160803010302040c020127020a0e1603050106140d0908040f0e01080d0201020405 79
    0xc014210006d458141c14080d18041c02d03602c0341c80d8002c103d8a1a90355800840300740b0b803c16074030184824581528100400c0c0640c0507034040b1404c0c51a19400d017460114145800d80007070003103d811803d10741825005955003804c039889403990002032000d1803124148a040c0d020014907070015a807501a9031106041120701d1540f081c4001032600b102c1140d60700040303070b010130761820007052550101c0c00410300f10740000b50240300385501c0d01202c4590b004051020b18101110301c41c1005600103105e842005481101c50817900411410301518080080380c21070100301142000743c801440120041c01107145c680107000401c5000e100030f00240382121624003100c5c01e0039000c080300c40340c084010300441d03d85080000051140c1f05802206141126111600341400200c030f000103880c0000101c6d24074050110600550792545102e424000700386014401403800c00740903900c00c00b0034000003414041d100c0c82000a070860400c01507240d40751404030303458078600e50f100300f0139a40180814409910b80e003c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 393511573 1250 393510323 393510371
    0x30306150c010b04020705060712060b120405010b130c08010504020301061e020f01110712020d120e0a0f050d020709020c0c0103111c0b180c0a0503100b0406080f0a 72
    0x10419924407001e0402401006140380040c0c02900225442061000104905124a50f951194010105244007440072200240101c80091a0601102050844199000c0c1c5d03c2846200000760041d1000005420080f103140714110040e1640c03494180554440c2c0703800c0c0149400c0e2810350640d4185007024101c03041444282c2200b2079087c00022210384200146008041c240c0002c0140004040c40e010340396002010a41d60409200c004810146c800181003e0000c00d0b030fa00e03181021540200b4001900c1c2205c107101240c030030021a640801e040f8000c1c0020a40301d8401070501100440f4064140540765010786140d034418040491813081c08a030f44600751a00340303400500c85118030070a207894040c2d4001000c2c94210f241c1d541d400d014260b4022520400101c40545415184e1408440d0034441100c00b00ca200c001030020740042801340d000345800022001030b80112940b80d080d403040b583c1081c2e10075800960403409204280441890382a00200791038000d11485d01c0c00290015040e11644c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 393512823 1250 393511573 393511609
    0x20d0803240a03111503010620060403020d0807090308031008060c031009020a03061e03031128032006061e03150a0204180b030d031b08040303060e01080f010608030306 74
    0x40505010350350760380d0b0071200001784461641d140d503115000140034a001241002c421548032401e03008040b40010350703e218586c143c0c01861143c42d880740c03c961203440036007401d050059082c0040b00280c00c0002540c0f0841c51901e210b80d00d5490800d150345450b00107010070198030420010f11a400085481100c186ca1400c180540d03544500e203011001061268815100841c070b604c06100721420b107861020403640aa91400381a0100142c001d849403550700c84c90b002d070f414034054000200300c03107800001c61500a044c42d107450501c0c0440c6e10b442e2a041c940700300c26030304680704104151802c00382c00c07544031903100722001ca880203ca021030b540e456042c44840c504100900050000e442903011035000d404d0100802004440c9420450040d2454103d928840d02903030094401d040e10920a0748280e044082040c220900d4440060b40c0c0715a0107002982015212000411203003820103043d03008011036402094a140c8024815013101c000c1e130002d400b40d42040052001580d11502c0b006440080d503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 393514073 1250 393512823 393512843
    0x30f0803070921020405060613170f0d08090115050a06050d060f180b12070e041403030f01080c010c08040b0a1803080901091502060a020a0309020d0803240a03 70
    0x81d20342a5451903840c1d000110402c20741e0b40c03802040780d900d030205420b24400d40e0184655118201040541e029801c0b207e942440c0c0d900e8100034119140b803001c0749860006040e00d012114184500b81460f821800c0c05010960390300503c44849003d21842000c84891081c0c4580142030100090030b540c80e501c600c0e402c1100110784d00d80508042c1d4408001040504038400e13a040e500d0b1351002842c1040490040d489c2d20340f43c92120182401b011100e0000b5409000d0709100c0e007022101d22030f9000181040d14801c4081807030250844042000354018800c00c80601182e61608511030714040260103854108203007008810300003540741d0140c40a0700c00c8681480d8031440714181c01c8400070740c920841d405c504c07045a070010a1020610007411045020b903500810b190302c440b54910000c004000080c0140e0105000905031074081d4058009012280703000320b10b044994000402401d4036550030b5a0382c100010a10024007100e01003070440707210b40c25035103035088400c00005401484911005d410b217446 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 393515323 1250 393514073 393514081
    0xf0905011406250302071e12120c0c030f0605010504141b0708040f05030708030c030702150702031005190b0f091e090609010609090b041401021b0a05070f030f0803 72
    0xd0301c3c084101941e100d07032041860103160600a5484107140300d804110388034000b55003102000c40da1000180d41454409010441003981d900310740317031400d511003c2080a10301484001545000001c1c00071744c0101d11400c480c01650400d032040300c03030680c0158400c0d46804542036008140c0080d240d4043e4a044840e403400001c04c41d860018440c82000410f03903000042c0228030b800c10311000e4030550b0802c6d021240b50b01c0e15488996035a208064a00110794400d01c0450b00500e8010b81e03088239050604901030030902c0c20380c0440d250001a0031010f83c45610f40c01041a003107660001e58032043d40c252802c0c849a20034001081c048002e8042c0f40380904022400900000b03003412031450810204080c02085290100760103072240016180e0031020750900c000020300640c00d00801c0e41060300702d26091034a442c0c6503180340c80855030b40c03004500b954090207580e8604444000c0c240707070580c400000c1c1060908516002d401d151050300007a0707400310020410b00209195040050070310394813403501a41d0f529 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 393516573 1250 393515323 393515347
    0x20405130c0927050105030a020d0809011806021c0503130609060216030c0b070309122118020405180601060c050304081b01080a05061005180402070305040f0905011406 74
    0x211a00a011000800c40e0154403002d0300c0400e8000f03c40b041c0340c041080ba600d4004064690250358800795028880c1c9207914045a03260004244d030b50b00506292a685598418540c040e03442c65024bc40075070440403840c0026600404200c07150901860154074510b441d624081c206030701004040c20b8280e07940d551908011542d41103603071035405410100d0014401d0710b401880a00c07420400c80f062080c003000300713003484e00a000c1c1d840c8442d4040c41c0149015084c4e10101c58076071400b801c4c1580325440c002181c05804080c4900c0c26548605070a0102c41c90b80d0740180000d451010703001000c4014603441e0f40e5014800400e0050554801d40351500480405003030252841c02140c100d582c10f400303288040b80c1c1400c40d144000290f80b0003038803801002c1e40c4445100701190740032680b0a4018a0380c0340c180035100c4c800d20083c800e07018102c0703c0c0300c402c407400000b00e0101d030081642103011450001d418040d003209a22581d00800d0340100500156042c8001c02d032607620a1108540940c901060a01c174002f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 393517823 1250 393516573 393516587
    0xf090c0c0813031e080a0c030c0605041b17070b13031202030a120b030615030f0613020f030303070c0f0c03080705100f0605011b060209030303011202010201050703020405130c 77
    0x41d80240d88503480706103500d080d08034550302d0702c8101c0d42400640c50f01c0840c0010807513620f0701c10341c11604a6041918000d0207582215101008504014a041c00d0b2400a00d2912070140243d006001c0d4591a541418192401548a400041c3c3d41450490780fa010b1003030000c0e2a80a480c102c03040607444940010608144180c19080180302e00e6940702a603e0780340d40080a00a01c8010ba0b403400d0904101c81101d20444102d031440d030f905034001c400013484105440c111018400303000340841340030540340b100300340c01c100058440301500e040d10504d4209601c0e00204081d15542e044001d146107040c050400f400000e00d1000040c00440d40041130810b100b64450303018000c6800c203040315a29465894107586a650540c904111245003c070785000f0340b44030f4820141650300c1a103c10501078202c480310140080e001000712a116002c0041c5c0b592501d007400610700a200c44c20a14141205a1002a09441c4000d01e4601090700c148010005c90740e90140f00c281c00e054009000803c0300f0203071400c43d024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 393519073 1250 393517823 393517847
    0x2090303280e400504030e040203010302030a0f03050f0c0105010519180b060906030903030601080a050105060906030402040207170715050c074101050f090d08150910060e04060f090c 80
    0x8010038540c18103103070f0321540007988601e00c6075949840319100c15040000701d000a01010750550b001c51480710000700c40c0d461100c40c1d54064103016041c11521608501d00368080188825240d44405c010400e41c00c0842c4801c02280203081210425401d0011a2442c6040b00e04910303801902c800d842c00c55a1907801c1102c50040c1d0148c00180e80c0c0c070700203540035a658030540d181400a880840026000202446031743d058400040c80c16280c00450400c006082c0c0014005036801a401c20542c40001e01d480b000811504941104646503001c82c2410503441e070319a15041034641c186410480d02c0b081d4942102c21032a0702c00c141d100c0d42001c0912100d260b0603105424402c08c0160380209586c40c01c004c5c01400d85940200c000d0040da83c8075280050012801d0703c00422039071110402d81092400340902c243e0003e240302d120122542080001005220140c0d48210040700032031060181e2079006082d04c03a41d11041d542840040d15004800782030140500c648d0241c640d8815914440070b20500744400d603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 393520323 1250 393519073 393519169
    0xc010c1a010f143c0604030b010302090703020403050d121509050a0e03130504050c1e12130c42090515030c07020402090303280e 57
    0x668640d00280c18030b0006008004a2a0408840001e9443d00d03101c0300301c0c448484a802da001030074014054a0040e99062601082c8001494141440e22240043d00080d800381d60700000381d500d540113000c1c03038503800703080c51003098010002407012420000c1c034045a82c0b224a459115040003800c144001c00c03503640700344200c5141c04d03800900c2e00003d0b000b080c090400d03410200400400c0c0c0304600c4e903a1091740c00c001c0c1d075000f0503001000507142603070006520005c03c006041c507100842c0340704480d10001c2c1b08041d155180210301d4269100d40b183d07100d0f920001942c0401890000c0d42c80f031803580103a911038152141280c007950702900109001c0b0710300c00340c0e602e5410041c80710107c0c11212a4182c0e80e909000151088000040ca89807201803c4d0420000d9542645161148012002d89610504099030801e40070403c00d15143c0b02040246501780c1c140941020b826a40c0c0903c0716800b4071954030384104000051a21144ea40d0564807400415100118401300003682c2042c0110110540c50408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 393521573 1250 393520323 393520373
    0x3020f13090b1f0e0c09010306080f070311090403120c091214120906070609022202030906070306081e010e0703080304050c0301050417360102010f0e0c010c 69
    0x3004035801450740a4003540d202c2030080072502c0007100180c1c041c4e1113000020a048030208078501c00e0400204031540041c540810030ba074a4a034440e00c1c18501007200b840c20b07841940c080080c84203440030085860000c03500e02d4941e01701074030000c207000c50301348103c41f1140e9030b0f94000c000b15004103203840c010601e1110b012071100310390500d0044203c4034005424580a01483c0c601c0c590350101c229100c0a0340140964203008803902e4403001848040e1080b0713007150074402030001d1041c0d00c03002101840c44550300942d5914000c1841c9040440151591003418240601848404804148240f441c00807030b22195541003113440700743c054203502c82c17400346600440b00040140110f48005500c2280a031040b10b0684a442d420303d4201d6400302c9003d0045420010041c01241c43c4000a0081c074a40c1c0c000c10309c0031100400c0454101d0085480520b11840c43c0e15821070658080c055a044d038030301400c08120344000380b10084d403281c3c2004012810403098a086200b00031032a540c4012294070404984 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 393522823 1250 393521573 393521591
    0x904060f0e0613050f030910051605060c030105031603051f06050a03110118060c030c05010b04060b091302040b04300c0e181002090f0d06240f03020f13 67
    0x4a41d80d002d90340251071034010500300c1305006174000200c0c0d610100140550751501c5606400321855000388c0346c010070711741d408140480171601c2002598015007000125a0b0740313500d0701e801c0626042c444401d25810600c0c840302080441c002184807a0002e09400d090601564580d07801c80c010709441e001141d008010480100031700107000c20080403010b0a032110030350340d007189040a85103100f6205420004102c278618000081c418102d04100e10310940c0007041003402580050181c070290b4205110458010416101030318015000700b02d0f41c031040c3c000f14501030601460018a1043c3d000c0d000045000aa18444d000c4070b1030f20030802090710b1004c1c100c521043c4e1400d081d004a0b1842404003807030440d004140c03501c3c1c00b07103070600c40000d21b4001070800c06560080c14001c0d41101d01d03007562107a40d03001c40e002c280d1510725405043e144140400600901100b00c010070381c4010710351080d03103002c00280622200c40d181404800b0390b9011680c0d210001001800104c4074165180ca0075403540c1000c945c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 393524073 1250 393522823 393522841
    0x70b130308030c091503010b1c02040504090b07030f0b01080c0702030304180b1f08040303090507050604240507030f0c050c040f02070507050306090a0222060602070905090c0904060f0e06 82
    0x3034480c0c410f00712a90950168080d145d100c8a001c28060300740c0444040042011015168074205125640751070050300f444c1d034440c001011141a00820740d90060f940042081d0b540d40b6100d0b071480707103244a80801070140d1034000201301007001405102c40e0310f00000d00e03400b03541e000c02c103480007011004c03518000410880c0203c070180c40c1d1062241d015981c6000c55454800c0c5507110410580e5159a9241d40ca03940c6803012006030921100c25034090040740c03000320790341d210080104003900740e0444052015881004000c01d43c4402506441001421700a00300020390200e5540c40b00c1783e5914001c46611060b0034080d0070041c1c16070b521a441b500d094001d081007915034015201142c01941607880141c6da40040c140c80d04000c86012071142c02c010f10140c011701c0e00e81c0b00108050039280241c54140304000c4c04004561081c1c0092000d6804a1410410100d56000d4680c1c01210300300642101c0c50010086207181c040648024851a03d40c0680c00215030181d21101010b40c1803412034689003444000c2d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 393525179 1106 393524073 393524077
    0x190b01031b1b1202030720181f060e0102100506150c0f030307181e06050906190e0103180809060a1407050627070b130308030c 56
    0x41c1c00c0458840520720f807501c0c00c02c0c0c00540d030350100390078107030035042003250403580d1050800c40b100000e8a51481d0f00d02c02e0505081104080d849190174044442d409843d00c044804407003000141003a4001c0602050034002e13003d84040c8010a1000406d68400700c9445d40c0000b2039402c018044481000104038200b84c21040d9401c42c0030a101c1a81558401c0d80e03800c0c005228500d0b20340315008656410390042c60700c407240c9104d403408542d81d24011801d9110b04800d00c64003041c1c44086845400444420090364481c80c0031310000e2880c040d0012130031201c001c1c00203140480d401c5034415102c2400707003002d0304448034504180c681c10401c0707410707404031000d202004104902c4102010511014000541c45038026001600d401c4141c0340303203800c0b40600700d621110711541c4800c5102c07010904400b5603070b00c0300005075102402140460b02c014160300041c14541c000041003880201200 = true := by decide +kernel

theorem cover : BRFrame.Cov 393345323 393525179 := by
  have h0 := BRFrame.cov_init 393345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 393345323 ≤ n) (h2 : n < 393525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
