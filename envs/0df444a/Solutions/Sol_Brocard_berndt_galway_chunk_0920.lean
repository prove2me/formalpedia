-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0920
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:57:13.905893+00:00
-- url     : https://prove2.me/submissions/fd5dd567-a964-4796-aed4-3bc9858dac98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 165287769 ≤ n < 165467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 165289019 1250 165287769 165287779
    0x402090408070503180a1403070b030702010b03030a0e03060c160b0403050d0903030b0a05030316061a100804021302130504050606120103030f08090304060e043813020c0309 76
    0x20200000d841c200c03410341d900441169190804035084c01a03014407070040314002ca004110014003650449101c2820000050141404505042e4075011076000105100b0441d034130f071070700480d190f00e041c8000c1110b9002540c3e0744a0205421080c0340c50060041e0200529420070400070700c10302e0049410700703840c50303005108030076680b40c0b0b00707044a80c4e0080c003080500d0507240209a108041c2c056010454524054a10310b501c00e984c0c0341003580324064500d401039403079294070590380000c0c0107502c4000f0242480f0030301030301404170002103140788110003443c0000c20400d901703003c29403402408106244480c0d070002e51400c13043d9070085030300c90710700d01c40c16003d40d40352000301e0721903503813601585c2c0f07030000c001c0a1040c41c0d07032361781801000108042600b002242c02c0c2c01c046020000b0200c101c505840303503600c03034504003d8130206000c000c0c0002c840c0070650b00e40e240c0c100184c0030450301d2030218040070240400c58400c00f10301080303d119244444a0091441007080316000d020210644081e8101110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 165290269 1250 165289019 165289021
    0x30f091201150609050a0503071a0d0603080d14060a06050f2a0102190503100e0c12070305070906030e15040f060219030b010e1e190e0a110f03040209 66
    0x4106400b40c80d0403520450350b890380503004101c0316449040142100c00456070700c1c0c3d92540ea034090603101c4003d4000c0181000c40440c0b0541000c2e05100202400c2090910024009549848101c110382081c00454042d940b6829044c80c002c01c80c0080603080324049640e412030918004d005030141c40749021445da46100070400c801110381d000d10b4540095288085c0314488120442118000c1d0701034082c0389410b046042c00c1c407038590307c00d03c281c030312503524602005c0c04079040c000a0410600d005040c0c8803402e604115007a458105c08140c1805880c403a10003258500300403901a04102031500000101490004000f65014000403c4400000b181c00010b030b181d101c40c1825a0111600318000d0702c02c1d40006a11145501041c0700d0908074006681d04000380394040004603010010500718982c0040c20308030204684840d00c22a424504000340000c00742c1000e078598001480e081e5105011082c082410012211218001c6651910aa144c07207440c2c0018020884000e0101030406805946164 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 165291519 1250 165290269 165290299
    0xa0c080601031a06030a0c0f0203070b0f0604020c030a03060302030f16030b070c020307080a020a2106111324030e030f0304030905042408070b070605060d061e0e030f09 74
    0x121100001ea0000c0d0000340c4d031b445c081404002808407070340d80d80e001484420325041110f04c08019a481d16074800b82144043d140d00401d0f0440000103840c803944245d003040404110a000c100030038403da8103440c045800c0d4590b004040c10140120842042a004030010001400030015001c090300d0b4040308079180c2e900d50f6141218181e0054034001d40510403980c002c2000f9100080400c40d0600c00c075002e500c2c1a8507a40d290b1020780d60489500c03a5450100004000913241da001030703004102001649060100c0341440403105441e644c010641c840d15410905620b08190050340a051a281024004d00d10080b46013070b070300d10400e003000100410200100f0105489481403070000c0034000c00601c0340440d03a84001641801060b1210640241c2d46400a140c41003c40c0b10000c460300d41c550181880700a403600c030041c1c08010041139001c03102d8100c0d540090b4040c1300d00900d25090309002494508a112403104441d601c6038202544d500034801d407a140020700c1c08848290005848554040040b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 165292769 1250 165291519 165291551
    0x2031915120b010905010605130b0a020a020402040902040e0109051501111507080906071e0c0314070807030219020d0f0201030f060b090f0607110904080d0e01050402090a0c08060103 80
    0x103600181d803a94032440c207400520030b466550a05070b506207441004140da8400341500c2c00d2042565484445900c100c1c104002c1461001400e06452580107407a00190954001000c9a003e0703088175002d03650104003401404680718a0034090301c2550810085418407602c110843c44941c0881030400071002e028140b00402841a9058403017040c0003466a4104008007510160342210020003030300c541c0000648051146040c0b00070060031801c40d120100c1c06c200107e48241c0100b00c00d40500c88804804841c413000b070300041076454000c2c81c031640c80350920714009040c5202100900d180c0170b5601485005680c54041466003903520180c0140b03c0f0540d4030068001c0d207500b550f00e88406140c201d00040d40101d010007040040000ca40c507041c030707442440411002d80038024000d440c0203110040c3c0310280c02e010794540c1c2c015006401c41c50030b00500e012000c0954001e5216038006944950a102c2141070100400d50004400101803007081240700d8010184040280310504160700c0c0d2148074680842 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 165294019 1250 165292769 165292811
    0x610270501061112091f050f0705010603060c0f0906030218120708010b010c1a15030f07032108010b07140d0f030f050c090d080c0f0717010209030a060902010311070615050103020319 80
    0x23600540c07d88031000381c00c1c030a00a045512040d0365881c189a44000f249109100c0103120140603200c4082050802c1e01c11402034210b2103544020711100c00c140ca070b442e610182080b040d246004010310f400c50600300100d0039240d114418905020300c0540b610006071030a441e10701a4000541c0040d1180d84040c4107010808110306001d425005444403e8420040480c2c0b140c1541d000744800d600321100f520f4400440701242103510009040c07040140500c0480d48020a0045e0090081100c0b0a81545241e802c000000c8164800704100700140174103a034140c024040710b003d07284420007691602140980310740c4034041d119446840311507004000c200c0074000352a080815402254048c081d00c1c81e046079149050b0141d90704000480d25084180b41050084030103240380a80680810302403039480c600a802c0900c412414961121f00000c040e01c42c4030040c190542c0144008142d09245846503102102d058100c0342c10180100200603444080800659100074001c8001521007400d400805403440c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 165295269 1250 165294019 165294037
    0x31b03020a03060b03010b01110a02010c170a120b030a08040b0310080607020a0312090f0f0305070501050a02030604140402100e030a06060e06030f0610270501061112091f05 76
    0x7440404014081c1c550300210a4003400d9000300320700580ca20054031186070f81d4496031115030128180000652103109030480300b80c03040002000301c4898080d4440c10340c10010092002400b8443c81d00c003090340c60301442078503480550140a91291311307100d80c402441a070044403403c1d0800008260b400b100001d4003001882018242c170914103050100948518240e0310a0740060810100c1c400c100900f071282801041d40000c880c0c3c0110401c1e515610b5024a50724140c0520006100c11000b00b1800c2c02140d101f2040c90f000180e8a00d4080c0411048454081140220034500420440161500003000000380b56500745003182040500000707181000e05400200500d00f80b031000203500e038084ca00903004103011426220041016820b0070380e100d10898000c140e5082a540822480c90b001505000c91901c600d10840000e0683c407100095840171303030042000645591900050000a1012404040140708040d1800200c000080e429406020400040d00301442801664601407012500030b80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 165296519 1250 165295269 165295279
    0x61404060e0f03010e03090112150303030b12100c1106361506180403050403083109050c0903061b070506040303050a0609050403080403030e01180606080c06070507031b0302 76
    0xc5d11004441d40741d4001c2541c05001c9000111800740d0045180501c1079284810510090780700d02c4d50720202c5c09003121505c2c1540124110a00325407000d01402200090a18044007089588400740010b00c1145003003440701e811b0300050140039000d800480b44142c03c00070f20746196a00e62400c0c9201c000c032400c03261445528440e40d01c4100042d201000541d100b0748007115001d06140d1015080c40d04880101c2d40140000c10800090000400d41000380450344044032400b5003915040003c00d000c80040201400c03003180401c810841040a40a4140d120b81e0b001d604601303142080c40440d64514001e0907403605a0702062489200740088410b0395500c580040854a49050509003d40141001d403042c5050f84e00384a4040f88089880c0910b070700599040d9a07007001a070f00d41d24114014100641000305135502d46c05c1e03400280d000d0b081e03604600383c02000001541c03498a01c0321881c200e0307084809030080c91309100c50130100308041885002c0303a030014811a0710b0422541d041c204440b60b13802c000e40c40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 165297769 1250 165296519 165296531
    0x10605010206130f0b06150417060c12011e050604060e1e1011120f0408011505060f0c07080331050102030403151b09090b040501180902010c02090a090b01061404060e0f0301 76
    0x704d00e03d1903209c418182c0c50070543d0016100d20270514079900c940303c10b041c0c007000040c004110034000380c0611600f43d03180b02d4540c0b05294988001500982c0264044000a200207400004502d07000380b040494801a00c2104844080e44010a50158456400c1424008030980401c0d074040140000c00401c0d6804154640d2880080d60b0b04000c0c1c0c006000b0b400582d8641512204c0380000c0e810b082094074002400582845584500c02c50154056010062140141000019070350003c00c090700030005014074101e141700c0e40c440e000001d900b0030440300c00080110b200401040e600070040700c050343e4121003528100c00c9a40341c1600904045003d00c905100ac902c1c06004442d4040352410940349100030034030141206404000c00d8039000c0c003800e00c00008002c036000b140d090b2940000b0a4a1042c14511030200d2250009240414110707a10203059480b06c24117010003901c90348803805403410f0705011080d0741040350041c0140c0a80e000d00014480343d545500116a11042c4141c40003400030024010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 165299019 1250 165297769 165297779
    0x41803080a090c140d0606080115080601142b0308071403100603050606040e0f0f180d030b0102011401030b04020f011106040b061c060f050a0612260c010605010206130f0b061504 78
    0x8000c0f52212b81400c0e8403012001c2045240450b1840c100d070084494203142000500810082801c000106050302c2c102d800000e141a0a407019000200d01a80755a02946058070011f01401300e0303000c4120ba484070800030002d00c0311548404c20281e031154540059540e40d003202007101c1d40310780e404c040c001d0f1107100c0070443d41d1401521428801c01050342d0340f00e140d07190703c14040011008a45400358070f0700004041d0510900c00e6001c1d41807240c0500c0081940740003410044c40700c44080e081034580c0161300c0f0420065040076009404482002c0c82d04104503503588a4083d00e030200a080180307603180d01340100b0882d90303655618124a155030502c00000004901d0290001d042c4100b0b0080401d091900003480865188502030841d8049034140070b00382e40c0d40e5640b850291066640807002990b0b5101400e81180e90406484000d1006c40002485800c21001a143ca07200600303241e02d012201c019500000c00c6118021645940300880905548070000045c400c0c5008841c500c0707125a0115001903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 165300269 1250 165299019 165299021
    0x5060115111905100b030c13110f041703030603030403030e0f120c03060702010b101412270304061b02030705060c0d080606120c0309010b041803080a090c140d06060801 74
    0x40070074496000c030f81a444c0c1d544990f0054902d04030a035a4541c00c03001e11500141440c003a0b01e415503002e04000910785100c014480855048005180c0c070000c00492b0a000c002d100c0c2481400f000403080056007140f41030310000c1e07500d22403400010104040b10200d5451900d0b400c8104040382801002082460440140d880c1e035000403151280c4a40304501c085000c2c2401171280e25580b0601411619466400000960350410703400d940b05d9107070344100300c20780494038000f200c10b0140b0b1b1010b10543d0750300d0480d003003d4a4110810382d0a00e46820411042001682245144440040308040d0401013840f500000741040b041d9801980c21142c0050707130308000400403609000200c02510f50000580701c3c0802d01042d4020444030598065041011614486102014580c49803c2400208a860054021070282c0784000300c0c20440380c0c4030350145410076402246541c2e000260a070108580001600c64240d158164490001c2c05030500302c409001d91541114140749a403c0381007805459943c2c180d4038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 165301519 1250 165300269 165300313
    0x1a180d0611040e0a0f0501140118050d0546030315031103010e0c0f09130804060203120108030a020a030f02012a08010b131a0c010f0c03060902070506011511 69
    0x2840a1703240006142443c0c403984203140c180c944501d03210030a039107804010355a0001c0031400c810b20f0800420001090784d1860300c002042d602c51006030041d40c020740c0030984180540213191800629042d11081c9500d40c80c942090040d00c0c0c0e24a0101491803400c056004160f91090703d460081c03403407008018408130300324101000c0c00a5008200004c0801140750300e0724801d02c0310b507900160250a6401e10324010729541e0300000e4040f4164805005540c41002c560710903444880903030408070300710040c0d24a1400441c01000808051454600000310003502d54060810003030601001040d10017080d8800d43c800002d1803012020500c00c921000401d8496128150900e000140038000120702d0000c0502992054010001225181130034030ba4002004d07003030442c0c5455a01d005204001c4502c070309004002c0f141019a40006808030501c000909483c1c15400c1000403500400034080000d00c0001e20a044030300002011300440e0746032004607100303074a10501cbc1d4504e10800d444230b0100200341e40381e2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 165302769 1250 165301519 165301531
    0xc0221061006090b130e090111040801090312060608060108090304090c090915030c0b0f070213021b0309010c1103010e0a03090e0a1e0b030a12091a180d0611040e 71
    0x4911096070b03855610103184103014800409400020003080b50301032100500c0d401602e580000700c4c03108400c0501c1c46090300072f0340c444090390791200e514501749900081598405c10400c1d8050114a0401d400175101000c0944018100080100015142c81080c070680c0d015100c0c0c02d42c02e20402107240e000401905043c005d000115152200880b0860003000124040704e500103500c8180d17074039210340442250003480941f0112a002c010880c0140c3c0d80c407030702041610020100680b92640d010300100d1001e002070b002c1a06034000c106c401040d030f0704500004a4954001a180300b100320503804a80548035680340020a4402c1c0d040032401c140d0020750104c1a02c0cc13a03000707200d5541d62900c620056440715000b081c4854840b280f0041d40c101160018002c40101400700c40e03040841e5078443d00c491840c0c00c00740c8001184000e080c81464801610326842501007000750382024501090901e9594143d481580b269088210303030000c0005030b8100984080c8107450103500c60b9a2903d003440b41c104111a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 165304019 1250 165302769 165302777
    0x50703020708070f0314030913020c010c020f03180a150201020c0f0303070c080c0102272d040b03070312030212010506070c090c030e07030602120601020303070c0221061006 76
    0x1c00c800000140a9007252030780004801c0340c52440c1ca584408100c00000000d240c00100150704189c1c507861503c540740209940010303914000c0350b19031821140750140075421504400d2501501c58400820788810200d03400c40790041040444c005038441c1e03c01c3c0d0044e185002c0b100d1100310020f0f010350140198034031541c15160300c1e8805441440c1c9034030041369800089035104c1c480202065460024061181d020400186440340e81d8464100700102d14040b090a4080514918403a0402c11005805022080000117440704902040c108556400b030109000b244c0e9403082101c00c0c0d0303042002e0001186c01c04085070030700c0d00d0080e00801950010006840b014401302c00065075040c485c1c201c90b00755401c211800c06a0341840d4903400034240c1a0784e2501056150921803200c40d50a000560046115050040c0d0300c500000c000541c000005150138195007040c02000354486d0010040720304c0550464407000c11164030700341807443d10f180b4170ba174040742d102c0d2a0400143d601640c00c04001e1b40e441e512 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 165305269 1250 165304019 165304033
    0x10e0705010c0b040f03050d05040c05030f0d0e0603070905180a0605010507020306191e0516091d0c07120804050c04061a1c050405030a0305150d030e01090503060705070302 76
    0x55030102c540b07242c018142e081c1c0c100050003003050b01c10f05420180c42454841d140c160303a150301400384c8400751400e45214003403080401c10340ca0f04114a1004031484005050809000840900507402c440c0e4058000c1b503001000446503803003030280401628009110207042908080d50004d0b18508807160800c0924041d0302041d83d60091040c0c1e9000ca41c010010203030340c0d07110f840c4181c0015040140d003000a0300c03801d40c4c0038045110038400ba4020640c0743d00084528101e08000e001c480000d0054052140048044c0000c030366a440500820038070103860301c281c1d06c80c000008501d20810302c0c003400e401c40d460080200c070740d030201c4990301850058045500100c4203000f088221407061094031401560301440545000c40700c005442610b288d0020495a0821144054203460045030708441c5508006040b00a5540604c502a00451140290003e00001d8000704170100705407003000d0f00b40103503091124110707881086070b03a001c0e06000c0c0c141c40c0a402c002a01030001c1d0404e4004a0150080784 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 165306519 1250 165305269 165305279
    0x30c040c0801030615140f0117400b07140d05090f010e07090e0309030601140102061f0308070602070c08060141030a1a061e030c0402030907090509010e07 68
    0x1501c00c030300381c0e5801610300c0c0c0390001c5003007000352203000182c00c1ca041c010271890880141000006903881040440759a00216101c005031180c2c021003082900b0248a80002080300395403000340c0110320703e50010444510707454100098400008c100e0500c015120f000801290900c06a00818090300d02407040310300110f61513024034240c903070303248484a195010707003020042103003290820f00d403d400c0c90051301d00e080941c4020074100402600034a20061100c00d56413455641007203850380c40100060f60f24902400d05680342c80d40c00451002130120040429005c00707104456048070395184c0d00810b006412560b800001c0d460745024410400403c10b900440d0700742c507000c41c01c074a080c07032503c419034960078120030901100440ca240304541c0511a0301c40e000001002e510b02d161407519440c014200c2450030004000e41c0741040b6810802c0740521030015022910002036000011004982c0545c43c0c0e0303503102c2a1803514040d41d0003140c03881c2c00c1400780103040c501944039014049001c030544244588031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 165307769 1250 165306519 165306551
    0x80111190f08061c0203010f1b02030712211a010e0a14040e0102090303160506010b0c190501380607020105030106050d0902090f0f07140409020702030c040c08010306 73
    0x401c04000c0814000e10000d0003502e0000c1c40c0e01c5101d144100310300c48a0034036401207400c50341000d05416900d595041c0040410190b848140303e01c000910086113400d0345650340c007c101d203054406100703004040207008048841070250403d92800c004c0c0800802c220810700c05e41c1c0020f803080103400b10302c088241410303c0c01c0062100c0151007003481c0041540b142c200a110003400320f8004070440e03560034050303010190342c14802814800960007035541100300740d007085414041d041c0d01c2101e031030703c2c10040b0012444001c11046955052805c01c0e0003041000d090003805841c0003086440181c03034880041c600f00c1d00c0710040c0f08091900c0405400090360700002c1c00a54810b140c030281c041007090004210b003d2041c001016001d109003c045849001903000c1080c4200a0b100400343c400210b00300131054051500040d48200e503403402e0001041c4450800006115600070480c00580009072a815901d0070860110300b140c0c003070020480c22144140c01410f81c0000c2c04119400da0a03c1e0800e039180c480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 165309019 1250 165307769 165307787
    0xf14010c090506030603100e0708012412050a05060115020120040b0711030d0c0218061e0103060b0c0105010518040c260d0503160201050103110105070c08011119 71
    0x10980740d0034015030620042140e580c10040c407540c1d05100e040074549441c40309020348003d8122280040400c0390604009900b912174820940b114000c100c2d0b900141180c1c03407403e61048a580020240404081e41025070910a80c1074000c0c00501c01c1400024640000d0b02d180070740b55a50364001c1011240010344d80c0f02c41080319481041405040c0000d00181044038001c141c0300e88640d510f07100e40c080c0300001c641080280d060030004210b01049032401e6003841c040100c42c0d404080404e411702e00d0960b00040c9030706441d4042c1c0010304101e0728202c1107a4004c0c3e10503c0500800c07040c075a02d84035583d0aa601801c1309010303c0380504a04003402c0184641008002d0080398003030741d048140e6043c41003805d002480d01e0018501030000c105092010710301070180c15184501039031441d5507442c002c221240925061480c100842e07160000400c00f084070350480308000d00f02403030081e40c0d400b5142499000359515800004c819482d0110700715800380071030002c04020000c2e1180b0122000c0281c4180c0300700722 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 165310269 1250 165309019 165309041
    0x60d140a0e07080312061906050304020a0b090a090f020903030d0e0f0303010e0f0408040510020703110a0602100203060f10050316031406010e03100218030c0d03050703081e040f1401 80
    0x100c00d004130070802d00705c83e101607800700015054801c4c03803070005101c0200c498113903c0100842d400200f80000c2d41810001391000c1c180f0b04400380c1c5040300312004030701601c210b4402c505d0315517a01c28412204c0138154045a00d100801000c42c2e85070a805c899860080290780d2044519100340e0508901c0d070900441624100c5000d0310821004ea51445000c6140e004018400c0701c02403410031001c2000d41d144e521444520900358003d000241c01c1d0300d402840d040d154072006100b41c008110070442e5642c009240c0fa190394480348056240d48600002c00c1d0419401e01c44264807207020074980c5899944032020b03502c920841600d1610410700c1d40400d400b1560240044c8805101400004089502804004040410150880b001040802003100403600005104000040302c030900e02d589107020002541541401c44120030086016038002d0100d10900b103004050222040000c1c0d0700c200352194491010320541780e50380203480e10785400201007004010803151002140e4140307440301c0f814440c59800b08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 165311519 1250 165310269 165310273
    0x405090c100c0c1802030709060e03120f0405042d02090a06080402030f0105070c03030b0a080a0f0807020603070f02060a0b090a112208070602062202060d140a0e0708 73
    0x1600d03000460306014407901c10754050600c0003001813100300504400812541e000d00c01078880c10084401080600c0a500800400406038084645560040b03290500012a480e9455503907074030110f05003250186900040c0d20601d040c1440c82e10002d03540ba0840f000042841d8001c42540c00307602602240075082d0025080b200940052241034041c00000e81c005000a01700e41c0c548140320a01c60a445085070310900144550301204201a0103005010000204550b81103c60b07041004040d0f5407030030b01744060711603040320283e0000d200c140c0044551498000d05803039523900d044040645100030019501e00144a800e0001e084428140301b6108941001840f409882d220980c071603000d80484408a070440340200004041c465904800a510f145504e0bc2200f440345003480e40c0b03007000c0a5a22960940d0450030401104105801c406141c000250300c800c0b81e07402e56800420094043c00007845441d80c641802c805420401000c642d205404100c0140540641d440e0215200c0b90107200d215210b03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 165312769 1250 165311519 165311539
    0x3050613061d07020307051e0706020a08030a0209011103040303020106030b0105041505040f02090405010e0601230403031206050919060602070605030c0313080f03040c09020c15040c051e0405090c 86
    0x12400b945029040091841201d0400b442031720346604000242600e1840c0c80f0560001c0300c07024070180300040c0145240d00260a84220540300c611403403200800085080fa0b00041e445c206070300640174850002d800c80108ca89864607841c0c081d0007498207000541b0345402c100b00010b00d619150141100e40c210205004c2a0b03185404188400b81c11f481d40401522902407190f80c80b2511170f846007078000c001502c0d01e5509401e1800024103002e068400d800741c61040540b15641d0103901c80d04a608803503243c94042d8a410180c2c42210080409030052648004128180b083d48820400d610303416038920142002600d0380d0314070680c0d40d10618071400010071014400550980d01c4078014640c0001820700e1030103501e00c0c2d039484160796801003140240da408040144428001070151040160407003003821441c1c8241c040146e41e841d8581201600d60f6401c80d00010100441010150014030014054913020031000c041c0e0710503080440d0609010343e02d0000001e403284000a1882100031000d404a5a8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 165314019 1250 165312769 165312809
    0x20c0d080c0903010c03050402040b030a020114090103020d06060c2001090308031509130c0f0b0301030206030a0e01020c07030b2d07021c050706050709032d080403030305061306 78
    0x40640000c0000207041c0307060002d5015503c0a0090b041d61130746696000031240b0b81751040004075101c480b501806603112008000060741c10a0030414840412a9800d4403a4201070040340039105212400d030026090420005030643c01503524034013244a4100c09892500c00c001e00814800d003107070018006a0902030800215007914001c0d9000450032600e14031b1040c4900102e4400002a140b0380d042c01c00c500350510074000400861400ba00c100c80007460424500281440640030601000e4410708000022800b0b03051554851010520071500030740d2505124084691030366440e110594904040e030001810020343e03546140314012454039440300e01c2c2000102c40411400060050b020341c810300454241c00c400480748401103001ca43d4540d50344101c40c0c9401802c1d85c8001d480740c0f09100e00080c080c8005480d8142c20207042c281c1101880c0c01840744440082995000b850162001c4030024001c41815070541103580b00f080107841807850b100340340c0d000d21308840c0303c3d00c24003401d0b00d0100e002c031903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 165315269 1250 165314019 165314027
    0x9120f020d050d0908160b0903041401110115080304061202090a060309030c08040920030f041e0b0a05042f010309080909090d030509010e03160507030b0403081009020c0d 75
    0x141c1d04203c0040080e42a950390b8410000703038040300c84602841c1c40d501c200c0c810400c4403850a0b0f40038101001841c141490803a040c0542c1d003150041d1410b2054008022040c40c100358001c01c0103a0035003003d20382d22583c54024584a0f403003405a1000101c802d25407403048102c0b4000c0f280b4000c0040e0442220f1450140110001e001c00319040707080001c1884000046007090000e00042c02d6602000902c0b8904c0340c040302d51240340140c400100e00e00520804c07003c40482100181c0c82504803102088000901d407a50240075003c290003841c8029103024044915003a920447c400ca1203031401c5884101240c800e1020590101e40c0d0b50f01c1e03091321100800a07940b20390003206400d841100c0e11801d01d00340354001071407e0400c460202041d8000003e070f00c0c3d110340c1400b03019041007941c0c0080000c2c2800b0b4000d00c1d22441603807909180500c4030507030f840802008001090086801501d5009103007070070316008000034015600400e9035001c065002c01c4040c01442140c00d031040c8400109140818040c0c192 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 165316519 1250 165315269 165315277
    0x110a1d030304230a12050d030b04021605010506091b0d02070c0b03040f0209010911090409080408061602010507020d27180c170f13060905010f09120f020d05 69
    0x164050209100000e000030b000e10510f05628040001c4845492002080c440080b640e03921038080d40311250708240c0411070100d0300c080e00b4180c0340360100f045000304000c600030388101901f01201268026007182445010340c44680160b4040321603402d5a103403103900c00048281e034050017000001c100300901d000081d550081100521400000240c1562000c018806420854054030072003000c245d290b00318a811011540035140301c4808201071441850700010500170880c1e464081d5503104441e0080c85419810b44004040da04203d540c546000405010a01d0200c0907075000756003008041014240081100804800d40d0703942c1000100909804000f2168000035110600700c1f503600100e4000302902125801d174400e40000b00e020100c035100208046218610b10303040404031428480500000240300340c0040d1030041a009003d01e5040003c028120400e009015600e01106010406c5d0641c2102424602944c81090004600384041d2210709400700b214006270040004003070f240f40a50090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 165317769 1250 165316519 165316577
    0x7060c0516030308040303140708130206070c0b07211d1809010507020c010507020d02040b1305010320090f040210050408100204210314030601052b110a 67
    0x446a07005820030701403031024603401c140c1c00511a68100030034181c2501400387d409140e186604280d1902800042042001408980c1407140141001d4295682c000560f00100d8219150100c16603071000402c0d80c0f030f03120f40e608868000641648194105500c03d003035184a061b42c50380c194104a040c000080da251001403a82e0001c0e01200703000205039603810a502c212124000040c0c14202011b001e850801810481c80c1009000c128110041c0c5400a040d4001da50550300400c070650084c000414034213040ca000840d0701d107080700000a100d221007074041c0c4c113074078054001b240c4031a80080c008000b030100c54043c0c2ca09940004074006052089013600d0100c41480c1c8141040d07100e034805d134100390743c580c00c0c40c040c190041002d000d09584c0012103d618600140036800114807a5405011403204041c44006001c012001402d142d010382d04490400c0100c8038072403001c030080f00b40c101260110000c0c2c0c01815103400200c0081c2c103054400c84080000c25140e0f00010300f200d40401400c081407000c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 165319019 1250 165317769 165317773
    0xc0607080315180403030f0b0307031e0305090d1109060f1804050f150a0b0f15091f1e090803070b0636060306101e1701090201080f060307060c05 64
    0x194406003001c1c443d070f07507001340d102c5e40d00401d0b002d40b54050385054545103200244682c0010380704200164050303a03d506501e8130003541443c965200e00741620a0300030f85080a0300900b90b0750484d010088000c4100d400c582d0112580c12340d40c1c542006015140707400e24000354004000c40e06490950341c4081c030440e44030f4451011070b0040840c0c00780c41801d200b01c0c0c0c50021030285001c410300c1412155809410030080c42940c5080040101000081002403080c1a18110351800982d840c0191500c00b0030700011144022141000540e80900410040c11002c0a2188000c0a026002a58070441c503882c21603410034001c509080702500c615840c500c020342070542c08001c0c04840e003099003441400341d03103140c2c0c032141c5041203105031503004098546c01000c1074400e4000e401082065400071194005031a20700300540c00d465450f0405013a5100c868020040307900400b50b03035524650054000c00440c2d8800e82e00d5080d503071201944803001980c152030307256060f00508014401284504110303800e003405107003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 165320269 1250 165319019 165319039
    0x70509030f010609020c011103040203060f13021c03030c0e0604150203160f0b1b1611120f010f0b060a080408040e01030308220b010303051308030d0e0c0607080315 72
    0x14900b421110242d001a01c410b4000c00e568281440a120307503803a603409036102d24518a803590009131034030401050030020403c0240416250300d40282d6991010b513018000da0707090b101103400d091800d030b0242d40850010782000c0100700d429205100d10340d2a0b280142c50340d8181410000e003480c0081c01c1444140440c4000d0141600c804400c0240a07410f60080f1101c480c040d0440c02d2407480014000d01004407030b50ba5455aa6035242100e0480c0c1c1a84180d000c0e851545584d403810b101c80901541c0040e61080c1410f039600c06000b030220702c030007541224200801890300500020029600e898581d10f600c1241400724164050040417070981c010301c9107001629058407142454045002a0020785c005090101008000400301035618074580d94072a0320786000b0b456503103001c00c4000c140802400c006010a4050b1b521400c5103650700a000090b0681e41c03500300104860004204a46c94110640b1814025041c141005c2084523000c64001038200d20b140d680b00300f208070921142c002c1581142c038800e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 165321519 1250 165320269 165320293
    0xf1311030406060f06050f18010903120e040612080315030708070b0711060304020d0f140d0e0a06090f090b011806170a0501121e060e0f01200307050903 67
    0x1000552045100301d80c006505030074580d507404c0714061900100107210040100002c20b01400050b200003d506083c079000004038040100c030691a1039000810100180031310315181c03500080c1c10754400c0c83c191004c01c0180daa4481c014803420081d030003c0c21030041000401c0a02080c540f80c23a80d442c1002d000c03101c0c4665a000040d14098032684800b42d810000325600c010000316222598800008450355401c0d4101030f00050b9000446e844000c118201142000c030401c0300041072010b80b54801e0701620b60a120301c14000d000d03018a0031285200740111780011a05c3c90140301c80005540101c00382d8003031a070030134a03614003c02c419440c0303074107200c40e801d801540380881c1c980181c0a460650b5480c80e5000c105420f000c1000409014110340314145030040c411b12020034158002950001d420303100b00103544000c4070102d50613110282045041c500000c2240400103403d823141d1410900030400085000016480b100c14801d000d0001c40f02000030400f902d10400160451490040c02e65044d1309040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 165322769 1250 165321519 165321551
    0x20613030c060c0b09030403020f0906010309021f0207080109081603050405060711031606051e092e03090302070b09060d0c09150306030f0b0c0706020a120c0e0f13 72
    0xc1c0d00120005496080500802844580003170b0400300040c0110304150540d4002910740c208900140c4c01a81e01c0300010300140c1c031903006442c615401500d548280d810031084042558100941d000c058800c0140c001030180e0705100718200aa00420440d0900c07072008642d45070040c000c1d10503401c111051101140360313520351006040d15032040040410a004000c185420402e002d20541c0100d40d5141040101c250803030304030741c074401039110710780c00e1000171000c461302d54010746261640152140885081f1020140329141030484000a00600c030789203d0300071400c0e5003040d80014016005000c04004011130400a03084100d0002d00d100d0915a0421000b002c49600c0f804600004408640030041d00d04044c15412031000d0751724040c00203504548507001202c0358840d00424501c05640091303070000c10141580c5503980d02510942d514141c030300c40100308107240146403103070519149004078440c1c02000c08031141040507000f000306107840c0301044421824500e50502c0c603511141c0c0b00e200308100d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 165324019 1250 165322769 165322793
    0xd0807050d05030a14040302070b09061b3009010c11040c020c0f0d031e020f07061d0405040b061504050a0303050424020601090905010b060406051209061302061303 72
    0x30b6a0b40c0364413481c05220301003d88103081440c1aa644503e801d10001c2580800c1007000e0720201e1300c81c90b135038030302420103d55a841100101418034251707400d8450b905c00b000c10307a084903541241c0e103072420f02c40d0900c04400302440001c944e1030b55207080248000c2035000d0310000c0340c00340c0140840f002c0c40440744007107030a40f0300708404080141c20003203034410385180550303900b520f265041d2401501c46540e550040c0c400000703588540c40216051a40c020014820081400344541400603107100f155910030161101d000803400d44100549500c1d004e66a05103449a148070f280c020800900a864100c148154500b8003000903451440820003c01c80342c407a84440030041d4031035503d07141d03141c2c900000e5000f29100c801800e01c45903220388000c0d100d0740d030000303203d4152207070300384005480c02161a2450040500c0302c0c015030040c81c04a000180f907034008000d0401c2c0c84070381e880c25100365034003c0c5050f1105401c60700d028208407400510340240c200040035000341c2c0b41c030001c101c0d903240d101d850306010101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 165325269 1250 165324019 165324043
    0x90204050c030406062c060d0503130602010f27020a031b090f02070c05090c04080616110607020706050c07090e0607180501020a02010f0516050c030114040807020d080705 75
    0x20000061008200c02d510521005202c0d80c51048011001d40e4415642c1d000e8690903400704d0041c02020580540e1400c11000c070080d880012203132fa40c4070485a0340440f814610a0f580954a0700d0361162194807035018200243e00c0c80303034000107441c17802d030141c2f1100c80003681c050740c01886082d400300010350000c0c080d003030271302000c007550b907074240340c40440310070360740e140403039460450042c48500c00062003284500c0c162071044441d201169940c103540c080901035a800020b55201e5501070000105d850042c155002c0b603981d8640c51444507501106a03180e0302522039500503480020100a61445640139040d91101c000559045941d54009001500ca0000b02c801007a0401001d1110058005108105e042d01688049001031702c2c01c80040c0d112001420040c1c103000440d401c02581d14030031411202a261440912070002c41d441c01c1042e03413081035081c124040c0d07103400b50b07400c1c0410480140601c255400703c401031800e110380d400d2064503280344d0021103500c1018851240050700921044003004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 165326519 1250 165325269 165325291
    0x5060708160203070806011e12080a170103030e090702060702060c0307030b060d02090f0901030503090625050709051024020102040e0408030f10030822050a090203010906050109081506010309020405 87
    0x1d4104910a012302c411401d50841034984d200082001080310320350161091740042000f82c44038203050003510788610052140c0402c0080300008410150071105244410340c0641c0c0e1703212142d40da0b40090303036901030660348400540e204400280760354140c00021a40000795180200b1040102c00216206400c003a40517210b194000c030350640f082c1000ba42c0e09035510380440b10082c0315451900c1e180e803240f1a40d892039000308400588115200c070b801d14100030425003e402d200200d80361b0b08041d1745131202030040ca005541480c02061030045518104401e0301d8851340e84441d0700483d0341c4501c901c038a50410007001d6540902c0b0008501507e039001c03a02c00c1d80a00c41081e030724a403000240300d103020000e2608800500481d806e01c08200800161042407450309140c00c44440d9860311030003503609039071107954030a1480750040381205494010f075048400f21901400754603284c02c0103641e119620b0048105552100d4040346440810715950354003c80706040028103000d4940106007501c0c022100d1070500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 165327769 1250 165326519 165326521
    0x1050f0d0b040f0b0105030c0702190e040204050709062a051e0c0301021309050901060906080c190b1e0c030307050a0e04060f05210a05011b080105060708160203070806 74
    0x941000c0c0580304061840f440c0402c40c41d101c14002070720324000a0140500c9000208060045496011011846040308043d040040d9500c1004002c0e15804940407409503041c0008941c10500941003c0d00f51401c503120003240708082041e002400b801d4005085c05418081c001c030022480030304c180341c0251140702070420040031140030185015450303130031140607a10411041e000e03044aa10440251800c0d8135002c1520b440715201c00d400b514180d005102001c6ca0240b0018622030001205844105d041d2108101d40c41900311201c00300c4440d00c10192039010400100d44190000d40f2099100000440f1060904001c0e40400d85103030000c441d82c00c04a1b00c000f4051030071036004070710404da50300222400d0010f2428034200f118144294864270b409200030000d907500c1c00c002c100c6503c1004e641079086a24a416a00b800c0e80603003000c01d1038610030b03150070b210445440c0c032468625060301c0028081c40e2074200c085d03546146c150b02c840c0c4908511002c10300c200005035401e21507640100164002021a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 165329019 1250 165327769 165327791
    0x903021212010f1e171c0306091107021f1806051b0d0926240609070507020105090a0e040c0e0a0905120f12010b281d01050f0d 56
    0x5007403c5030000400c140190008141c18002c159041e81558403140008a0f465800b00c0d6041c039200c03900b100890754503841c0c85800d60150f89944113400700e5100003000c9c0715802040809030124440e03200081c0d00940e14001141411004446c8060704c840ca40c42d10101d550f507a511030082850994100c6030000f640011340c0030300307506d000d00004049120040a402c140940e000301520490091042c2d080780c1603084004401000e0078901412440c8162054550300c034074060b00c28000c0002e00f134404104a60360000700d0b40c941020220390784602c1c2c0a48039a8503088580d0015902908640c03245903000c11800e00c0031402000300e45103d4022031050211aaa80c2e003010544801181d00800d044009442e0a180d100400c20000b01d40720007031102c01c038169031503514108d801c90500c40c4007500056850b0f508000a0500b07082c400804211030080e0034258410703181c04580101c02c0c1d04a81e10000102803801242030600c140b00c201980e010141442460460781000e5942583c11150315007207201e0b036510803440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 165330269 1250 165329019 165329039
    0x60903050d081521070e0613060b0a080a0605040c02010507030f0b130515060a0c060b0f06091003090b07021e031614070306090c0303181404090302121201 68
    0x601d10800c0e00b012007031032400c10880c0e0700142c000c00e049886540c1e0100f112030700c21038019500442004c20026111142d85502441c06020b2099419900813aa1540a8882c2104038481c00e0145d541e841506850003043c000308481e07081c80a4401e0403819695000001d8030b40d100d21840c000030783e1540001c1001d26090308090200e450f20000c00ca012403d04284d0f4019a0b122440c1d00d82c2403d5442c03000400e0f441d00c5480041e40409420360725002940000c0c82072086800549040b2203603c90b2005000b0b40314505d003070102030b03418400c100e03412082c103001d982075918010900c0000c0084901d00000c40b07807906c2d11070509c090020340e1010b01603040705558022502d411944088203615480041d0f15080c0100c000710401c9403015400307080c17031205008554071100203000401c01150020024096150b0301d042803c00401d01c1e00c400c50118007001e901c12000c80c550001d00084480107188408a115210180000b071b010710704c002c8085000303031103071100ca0440d00b2010b01003d14211203107008940c14480110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 165331519 1250 165330269 165330283
    0x1503140403080109020a05091011061e040303020903010905010f0605030705030601030f03030e15010324090f0b0c04030803010e04030f020f0a060c12020c0c090a0e031602011806090305 81
    0x62002408004000220790000d07503090442d0780350b24005a0b03501c803001d0219014000c9441640d800904040001240c42e80a540b2349c100081003802c0e5541e6480d41c031114a6000b60125282601102500003e4003190007a0301070164070102800100790b44441d503903a11f0031a6241d4103d43c20b080d40d100c00034030072410108007110242500f54020311141d41103480340d004078181440002c2c205500c401d034050041d0020720030514203006010342c00e0000c4d41c403032422054444541340360307611b14010240c0f507004058003070080c100c405802140800b000c030410344500d40c544c080240400c01181042000000289154000318001e110355000c104050816141c010701c166861601c10301154401807800f0300c1d035070300400c0c80e44009920000006070070700c41310303810340b455100d0501000b1613074808200c00f002e100c004115a940d8940440c0c101e0300660742c6282c5082160b4147d80141010f9000340203d100c1d260344452804c9072640141440c0c1204500c143d440f110240458025100007012810100700308102080301d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 165332769 1250 165331519 165331541
    0x6082505010f0804111f030e0105060411030f1503100b0a0504062d05040e030a23070809060c030a02100f0b0906060a0c06050a0c0e03030403050309100207050a1503 72
    0xb440058510800c0240040009840646414540c141041c010703510400003445201c4c0c68240c1c0b0b643c859071440d000d801401c900c07860b1881542840001680b51600d4484d10789490a500030030f13820368403994614005003030000e041038250580225400341c10703a000c001103002210310707060108101e040041440507425103a4041803390341440e0040c401000002049010318001403590f41844a8000d000c2000e0481d907800741d5045450144600e071481000301c014050121551508484030658018581c1518034400340d141041030b05110040000b20350034014010000c00825103400c0004144a003030940d40002c500d803002d41d000d1040d11020391510300a8014840305200c0410600c004180850510500241224840c000c002108682c15000e04426444142c0000c004c004c130b4544030090600400b9030040080105000b20002822884e00204032000da81c0c0c4040a90b040400c610140a4141c0701e103840b22066001c0d80341c003c42e043d19180e2980c4018000001404580041078802904503900c000312 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 165334019 1250 165332769 165332777
    0x50c07140607020a200d110f0a0e070c0f08030702060f070905030a0201050304030201150308131a090f0111030d0609110a090e0c0c030f04090c05040e190608250501 72
    0xb00504160080f4400050341c0c2c100d5080402031210a80c40c43d2441410494030343e0000d4800180c40c01c1c002c0d65083c45207082e80560341d98100c654080204904000c0600c200d400c8030a4002c0064101c0c0d20580341c14540c180318840100c4150150b40d1a1ba9554000303c46074001a8420001c0003031840d626582c040d00021a0706051000c02c1c1440082900e501e1201401781c1806000808941058401d60002c1c2800c1c1c0c8035290740220740c4e22442e1683ea9680000780ba140703c282807100110300c10341401d803040c83c114042c1c5113091a0103035034000c1c1708002010700c104038180710506d441c030004c4242c140001c1c40411080703a8005070160801e60204119030307160500c010b490318140203a01a184e0444041015180d8044030000306a0700c0c8640e50030103201e9000c90482030b00000c904060319034155405030080e00c101d90001e03c900420440100d516015600c1402c050f00650f20100b43c480031495500c0044805030303e0041003d546500d1850300d015152520078207022400b0202ca60780800020b0780303201070b08091034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 165335269 1250 165334019 165334021
    0x3040302070e04050307170d0903030905011b080a0f1404080d051005010f11010216080309010605120607140706050106020c030d031a0603060604120507030311070e0705030613050c071406 82
    0x101c0c181c5e02e0050f154010101c0b6508095448400290003d072144000010014400350030b240c900180a4051428119060342c00c1c003241c4da9142102080c4140d04010f06e81d200e41c0a81d4551010001074078003440010281b076502e900c103948030b100c0702006610590142065550310169204018100c400c01000074103881c2442c8820b00071680e00c6000c40c2030000151405600c80c00207200030070f00a01c110042c2600011081280380c00708581c1078043d500c6030600c00000c00c111a5980c06000d082865001c0b0342d0040e4010300b0001b010140100c0b1003607210260581e009003071411a40c0d400c0100c0d802a0060b80141c0d03c007802100c224074041041c0d00c810601881d084c000088440901460089800c00a81c80349802000141e516104c4005903401082e01c03209401303018540b8200b2135107921960000b600015130b103d07202150300400040d00b004451400d256842c2507503554a08507059003014140681c4400c1c20241c0341290303085802041c0c01104170b0244599500d40c146450380400032072240e02d03501c40c1c000c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 165336519 1250 165335269 165335273
    0x30804030b07140a0c050c030303160908060105011e23070b090f070603090f080f040608150307060c0812090f0f010b0913021207090903030b1903020103110705060c03040302070e04 79
    0x100ba10061401170400504042c46481e0290900c4c0d8000320303c40d01403001004100001e5140351151402c0901501d41510458036140c0d030360b071150024051140485c0140e504ca008088441ca003000e2400101d2810024010650051145205020000c200202400304900082c09071040d0055040b00840b4000e14421206604a43e00c03581913104071014569181402801d004c20409203420490344010328030782d00e4400301020040e1f03401074060640040e169400113650310700700b1b0504901107100100101440c51402e0360850301c4500002d003c0b2100b01091211000340d1a08c2d1040a024048902c094600e4680009041e4038058041d80c03088011780c182400c2810f40e4441110a0741c00008403001c1c1a9201003600105050010b117030319071040c510072988001160b80a981c0250586482603400740300ea024100d00304401d1000410f6140b80d4050f49043c1017006601a6102c059428031901496040054070740302e844c01c08030f003280e00c46140072002040200300765040c803582c00170340307100c00310031b40981825 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 165337769 1250 165336519 165336557
    0x70315090c020f1006060f022b050910020a021318290702060603070b18210d0509040e01060315020d0204030609030f021006060e01031d0601030804030b07 68
    0x522440038001d40d5038844240380742c801d00c030060031961000102c45800102161020007450284a41e10000c0d130340d000c180c1519480820090340342a0f12903c0785440580140d90481802034804088091040402c80c52040340c40f0110701e038001480c0c54001d45881b02c80e50048c00280d2040d200380507007207840c0082c560018100100050303a4640c01482d00b01285880d0116881e01041303000c5031240111426007000001a40041c04030b109040c15000d60703503125a104540c8089003d41041c207960145481c1c42c2440f40d06002c9144680145d844130031411082c42003180a00f4111482c41d038000054000489a415041c41d024013555514418001c005140c69911801180e0003c4094080d5494001071200a445800d8041d13602654001508100c114054a40544202e070540c02c588094018100caa00c0c01c2c411522a9100300c0301d0035240c6540d12962000114000c100d02001c801002101c165030741e451030741c00c00845000c0c0d4031500341107640d075046003810750782342e00000c0800080107404084154a0180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 165339019 1250 165337769 165337811
    0x2030c0d0309020301090f08030a11070218040c0506040b04080f0c091605090901090204050405060301092310020f0403020307080f1e1903080a0b010201050108030417100e0a03080703 80
    0xc81d180018503040c4520000e4050b02003100060251040035a0764010702c25031400070741c01000e600c202007180d0035020b00e0042180c0505140650b10003030380410901c03503110348040f1031f41c010b00c1803076401c00080d00e0302d000a042d41c025400000484501203014802500f08000303110406036800020126050440b00040103058014a40500401031902c1541c00502981c00e503034a01000400c980c0b9250f03101d02d00740c0029040741c0725641c403a90810b00401c086007010710851500e01e8115440c0369940315068011648030a10301032080d07982c0b0492a202a0702d849078806003807041c130301d42c02099503585140100362509450341c10210741a0000401402088c40c0051420490301e01940310310482c41d03420f00c0260902d1543e0941140049450214604059000007800e200e05003909040000001d088012800c032002400b450856a004020030301920040c504511b6500020004407101406a07482600c159101c0074140308447d4444400b0604054019a0b400e601040b2494100100601d00702843c4044603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 165340269 1250 165339019 165339043
    0x1017030307140d020c03070209010e0402031b010e0a030609120915030c0306051c06050c0a0207090504020406050d050a02040c031a0114130f05090901050606030c03090a0c0602011a0102030c 83
    0x1d10b0329440181c1d0314501064a842c80310401086403034a60204540e40c8aa020035400ca1180c0e81890000c1740880c1c0300d0a01c1801035070050300500d0300f25802110014000c075000559810700c4a03802100649680788003844000c0d5120743c41c04141c03440b00386090003421401c21807940510ae1014400d1050103015015144510712601d400b040b14080035000340c1c01040729412641e04100c01d450107160800c402c002540d0102c1c07013440d0402043e41c42040035040350180450000040c1c001c00c41c2000001030503040035401078001071002a6941e590000a5004801034004036210b401c9044034006510f0140300b0b00c40001040d05003480b030039452800500c8171124030100315041c00321404084400c1c1406c24265441450205548501141c0b0303030501078520306261007503d100382c0700500007c035044418014140503003400341c40729007103403110140e045050f04010004811485407408101c041508011114001c15003a0000200f4040c00d01084414440d1f0321032080c10b652080100c0b0103030701c0300010f00c025a68 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 165341519 1250 165340269 165340277
    0xd0b0105031905100f030b070f030b28150809061f0e091005071d060705300a120c030c0801120303060f03110a0f0b0403110d02040e03031017030307 65
    0x10703945040540480c2c4c40ba8109030009000608003204105841984d90f004003181d8031440311400706210b0072404d48200385980c0b2b41012a0401564421b0108440038115180010313a440b0b03501c2e02c42040014240000246c80300241014051118a0780c2c00d0240c203400c01982c2d1a130ba0038202c0c610365107a0711862180706203031032122088005110403000348050305480440304014850340c10710040c024050200b070840080040c402107003008040c40e200049a8209134400090000c80101c622a0b9403040b08044521070500500001d0701c0148600720001d1110b0881c42e101e0401d210b0640c02c01d039080b91702d60300c62a0305043c1703400b001c1c0c040c0380e8100084c3d0703044554006410b5180101780c80d0440107480c0c1c50344024140c0311044004010411803078080744180d00d06460361501182d5079034401400e03d2a62140c500311543c100030034000300d901882003a81003040a4841600300441d5400f140484858501400702e681000c814005098110b41040c0000d10303074000ca0007269240c00001c0360b00d921002c1c000c44248 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 165342769 1250 165341519 165341521
    0xc032604030507050a020a090b0f090915060312121e070c06050a06120506040201081f061d0303120604150302060f090f180405010f09080d0c0e1201020d0b0105031905 73
    0x1020130040d60b1740e055805011740307141c20380d80ca1060f005040301d18101c2d84142c8140b442c28241e42000c50601e1310a90a54005085841d00700c038090303401810160003241c050190100354041c0c2c001800081103105c0080003040c4d59891302d820711407031141000b64030b0064600e00406000701c25500c060500c1d100e41e0080381c001996200c0300200303001031440740e01c41100110285c1004041c02404035441d07106034000e80b20a1110340e19140020400860000c10324241e5195500a1001030b110b20825a500c800c070a4060048001c1c80d000070b45035070842c00c240e400e05011041001403900313050081825141e0000b8803141c8480c210790016110b4000c0241982209001003116011562078000c40c1030100c00240c8500752041403200034880802003250300703840c0c075030905881c03004000c490b100e01d0b8105500310b0ba959003004caa0641e29009400402654000c110250030b07403890741d54400320b03c808000250320005039280483c1d84031406807444158400d042c49400e008010b140b86e82c1e80000481901c07401070010311 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 165344019 1250 165342769 165342773
    0xe010804171b07090e0601030c0608040c0e010e1902090102030a03020d020409050c120106020703030f0309050c0402040b1305030a030e150705030f091216150c050a030c032604030507 80
    0x9240100d00042076040e0400c4102400b940022601c84140c8004840a124120010b00030550780d020030b00c00241100307c400020400c0a1207190700d260028030031b1a1804440e42d960480345610982a080380382c0380d0aa0300d05004006038403141e229241d801c000d5055040c0004080040e48900400c1d1111041c141c00040803c14281039038122406821420002c00160421907885085500403048000590004600202d3341c0303400000c00c0f42c116681503481c9008080c0081045001c1e10448508680034403031420340b0015903031103002500c040c0050581d030940702c800d482c151031700040311540000e001e03030400e91a29011a038068241c564244080e01c14850f040c210121038180d40c070074420017400c240401b00300890070b885504024082d5000c11904062581d02c20904e1540319030514200100000b4408002c00c04698111101410326100d42130012138010305031030304e03800c001c030082c400c50001d202d140035403003050f0f08410843c18104003a036120905c0c01e20402101c6900401520182c2840004100a81 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 165345269 1250 165344019 165344063
    0xe0a02071e0602041802070803040602070f0c0303050a09060e0a090209060c0706030203180c010c03110c061201150f050a080c07150f0609020c030301030f020f0901061701060e010804 80
    0xd48001d2200c08100c1c102440c02d000000b50018003400e60a00c0c811800c8101d42003030b500950b000140c01280072891501c4956491009600c003140c1240ca01700701181d04030101c2c0e14001c11200860094880c56910058603200825600706034000f60140680d28031580503030707210000d40303006a407254a0016a030704200301c0001d06034003415140745c03070f50701c43c4020202c0d01c25030503006180104105206801c2c106015a00540c580400c0c210b014005503020451902081c405c40c80c1880f249020420b1b80c02814220000c04ca0716800084040060350b200c8004100003800c8801b0304044480f1481e00c0ca01400002c2030041c618881e406040c0c0801020201041751410020700311075030a0b41c040c81d034401da2820203161802400c07144404054092501c5030010300410580200d40380c00d030088001e14074681c02c641c5d5118080c0701d221001d07600301c800b54050320300c070b910f9011005018025588030a11061000c0200c8441144160802d00800500c448a0b84981e60000c078642d4100b42d2181d02d01e940040402d8420b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 165346519 1250 165345269 165345293
    0x702030424020a142b121116140609060705040b0a03020409020a0e0406090506010504091505040507080a0516080a0e0a05070906030506100e0606071103030d0b030f01060e0a0207 78
    0x58180010a04428000c2c04000790445081100f080310088a00750086411205c80140360450082907a81c5040c0d1609680356001d070040c01200d00d0290709100c0d450700c1c0009070b91101c034801c0b50080b122420054500108001c001d41c421078602c020300061424000050071340c040c41c420805015404100c50704e441d4041c1d015900a81040c180464841002c5a4010002c1d480107a60078003031071600d040418070b01041d01030b0910400041e10b80070300d0302e89002414002003001d8040b60b00c09840400012800c0ea4960050038024182c1e070b0707a0300e283c1d420868030a908031480500341096040c80c85406162154005074525485a070400300000d0b592004040c2c00e080c8800d130040204280541d900100701c00c26a5440759060703a000340c7c1211071f0380c1c0e01c00807a03280c020a6800b58051180b85000010b41500d000c10080c05a50f01ca0707036003081950403030710119103150000345840030442d0b100c02d250441400c040051000800445000784440351a0945034080c440d005080100c0320750700066840c040c824100411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 165347769 1250 165346519 165346523
    0x70503060408090111010e060c0a030603051213060323180d1107090203090c060921010204030b09010209131107050f030a030b0102030a02060f0a0b0d0b0601080702030424020a 77
    0x14800c03915142c6000b0005a01000c2ca0601041d40c440703502c1c811040c144140b6120950400050156444184d0030f140250040202e540c1010f49941020000903014054110f01508900d0081e46a580c0d02150400a20381c0e41c001d0000c141c9070000003607407046d0b1071845101c50b415185015080703489076510f15044000d80b00d000c81070303441000c900444c2640e004c0d200b1410041c40800b40e40c0c00750307241d450541c16403209172000319042d0700440e2000000e280c85001030103145e00080019980b00403002400000103158001e220043e540801d0400911013942c03140342e0710081e42c01c002c502e020420800600307101840c141000481e903507100c004508420782e10883d10300c0c03a0094110781041000c0c1002e180e580e03006441320700000f030501203d10040d500000940d0280140c540182a0302e035187c4907a4a03a40c2801007442c4041a144d07001d540305500c9a80500c98451300a41d108043c40ca01540050404100606014215402080200300c1d0300d110040034410b03030402410035031903001e41440880c6400045000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 165349019 1250 165347769 165347773
    0x402150a02060703060503070b040b0c0705100509010f030b011706030705040f05012c0a0b0a180504030e120a020d0203010b0301020c1b06030c0301050d1401020c16091802060c070503 80
    0x555100e9940010342c0c1c510070031407580c00340203c9440700203060b100c1150f8483e0414200050009110700c01000c00030b058401c0c0407104075000e450790b40c00011341c0c40082c80030300800308000061514081d680181d5003a1000f0f40d909046c8140e1172104002446a0009603a00b040d101410010406660301405220010400100140009201c0c403541c00c00510b03080c07052055514814000b59880d91000e10038011122009031826001e9441074040c5015242212001da0300540408010580300b00640031149030084c861400500d41c603092402404145603c240c4c180f01d00e0903940c1c80147c03400001407610b4402e5054541078040b100703e2011902411040b450640e055001080003000000c2c0050114040465a10210303071640c40c0c1014003030b85110a54000000c800c0400060102b07003401a02a2110f500c580440c840300f2406408190881c1c12011a002c010340055200440d0041d007004004050a0901c0f410090700c0240500b861803003140304002401280040b49151811400303004041c010301029017 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 165350269 1250 165349019 165349027
    0x10080613030c051f0e070509010b0304030f090f0b04081005010503030409020a090302061204120c0206090409110d03200c0607110612010609050411341b030501060e0709090203040215 80
    0xb0590004c0c00c45c20101c1c241c44d1182c1303980020380e4a058900e00d41294540224a89191603649049a4040e622581071040c0190900000342c0c0d195200d170200b00426414521a840764240850740d424090005038034107005081c900103024a1340c000c000c99089800c040001641d540a52000340e62842055202a62000010401c501d048024580c518841c42c03080c89202100340c03040c0000d8500d4205008042d4009805001d030054900b40b07030b0f00079101c10f0702a1208800a0000c1000a00301000c0e9100c00c400048c0d9243c0c00c03040801d40018401000710595010348895051003011905901a0980c041e18003a408503504507a5100c404c11503210760110369007034480d581c40742405007030440c0c0ca102d002e00a51400ca040c40080c0080010744030451855240c1c011880080002c005d0050319003a50702203400c2c1402041b40c00242d1030240c04415840e81c0b003168002514600380a400c695859122400f00302c1c0100402040741d62100f6030340192129141d0040c1c8030f0b01e490002c1880e91a2140c140c52102000013 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 165351519 1250 165350269 165350323
    0x402101805011d03121e0a080f0604090203030307020a030801080304270b1003020403030f0302030c030f042a0e090616082d0a05150a0501050705010e01050f10080613030c05 76
    0x100400401c04442e06a15661064642c00c0786c091080140b000005691040403d000c410700828550300b14070b000340041060844c07900000d09541c001d480c3d4030050390003001f0748400c15800c500c9660040100d1405182002d1030099040c03d122040c10803100210588a030790785080740994040302030702c5d401900170b10002c032030650302034000e6102d40020741c0410002410200c200f0b01c24001c407171065001054a07429511400e543d025400c00240084a6010748245503418040c0019040082c0c0116181d4440080303142c00071300a50b180019002d07060f9a00301004200340f551509030300075212612440e010409540d000346071803805003095090741c02644e020302e10744008200b03824803a004050741c0404014603241d0402d05c0c2595040700024540040c54241c0800c402d60041300507065a80c065030001c13542030382e40104513086540840d80034100110a2003800b09030031050b21500c001d80f04c2c0c00018985400c01555046403250b18078001000c00810700070100c00c0010610007034140819266130881400f0180d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 165352769 1250 165351519 165351553
    0x60721110c07080f07030c05090438090d090608040c08070611010b04090309090b15070b0919030806062d09011701050a060323010306050402101805011d03 68
    0x58840c0341020304c00c1d1807414a40d80d00104580044a5222920010452070b0206004d21010014000c0d907000c00d07002c41805211603181c240c0b41400c0b0405150001c000e4042d40e0300c43e03c40d20f02800c80c4855a01000051905540004607041680d070302d810181d00590f503601d0704000044950304100000c0c06519400102150003804030410381d0400c0000b80300100b070000a000885034a404090002103a0007001c00203500c4551040b80303412000b078104016540c24036404c24540c1e210100031105400b0303070782c01c1042210b0240f02e609e080d120350051101c0710030300c1910014569040a00054801e42d000074400e0f80861081c005440c031248401115000c3d000105040c0382690040e40246011481c051481c02c1c0c024060b00009050b204024415404075091910443c000c5c20ba0b1381813600f0410350380720761101481b400381c8614005e5210b80380c00301e41444c1c24418414440e11940405003444210503081109960044002081c0d070028038202c0d2041882c0501d2070046403a000701c01f90140998129004503e0b20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 165354019 1250 165352769 165352783
    0x80d020c01140c03070903060c03180b0702120301080705130f0510081c170402040b030304030b042603040201032a0e0301050c04081e101a040c02060721110c 69
    0x6180145042e550301c41c1d416508601c001c56615001401c40c10081c800500d2a60141d42107409500d0001200c2848000c1d5010950000b801601c9080e4400c08000707005a04010885120301443c0e001800c5500d091441a5659003c0c010a842170500d1452012000c00c1d9500010340006480da05200608011108090400450003210018000c040ca1085c1c000d141041e4603d40105554515010b0010401502c03200700c8003400880c0e0141e11071078070001720f64040025001130760050800c180d007800c041c903084c000500d41c036502d40c0012400c10303414620310b013130031003520350090b028240820304040c1a0b00100851045c020b16003071044c50034040240d140d40c0661080c03141c1c0c0e0140c0003001240c444640c2058140a50720a81d4481e611000a9a040c80340c00b0340b101410340f42a000700c03012449074520786c00a44d248905a19001c0300500807461480c54940039a0b12340f0a440c0c00504814103100d00300600f2090740b0141411241c0c032941200e0004481e80e400030080c8146800c0440d00e41c0032030a0810b071513200c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 165355269 1250 165354019 165354041
    0x1e02030603240f0601032304020a03050a050f0d03110301142b03030b0d050c0d1410020304230d051b0607020606090a050601020c0909010f0e031b030f0313080d020c01 73
    0x210750000686254024404d0302d00481801418052a6104280d1f0f1008004003c2040340c200302d140c0030010006004102000741d442c414000341070310700c0349079100130b160130b031441e203803a0800d030401c0160b140d15040c40b03003102e0548441c449800101031144011500312880704990448454623030038100d91205100c4881208581710342d401344a001d0031102000060b400d59100501560803032540c80c1940d2618000768942c0c44d120741250b9100d611705210090a0903540d005816650f1f0b00001000208080c41038854422003103c2c0c8043c03000508044416561510090910180140010746038008003503010f524421110201c1112130b58608258000d456600503a00d9600905580010800c8001640100742c41207206a00404442114404111503211701400c00130b0f40755a58103241078070809a00031b00744211080c0005540e5013080303c441d5840b011446240b45000e410512032802c80140301d00440e42c120012060414540030207040403d490b1080200c1550340c0c501c0091080c0d2000019040001038803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 165356519 1250 165355269 165355291
    0x2f090a0b0415080612010207050a0201080f07080c310501030513080904110c150402011202120c071a040b0402040605061908070201060f03031805041e0203060324 71
    0x25928850403025028a000e0041c6008204041c0d40040d8441d80002d40d104c100100100b50f16400422460b00b2a44100c80591321500808030714800d6580210701c0d503412182d50350b041403181c80c204000402c103980c00f0700441190500004e4144410b400388960400394548081e01005007614032480040f03100c20751003400d0119080200140c41120319050b130b059a65003084a151a1204540030000107000035a609140080180300895041c0002c20081c00c05400400c400c40050402e800007400704003003181315075801401000952401e0454918494001240310203075a2a44144c0c0303030840020442c1d80c40826550385100420040c001c05d40e41c2e05004500a5604100c030369100d40034808544180c0c0c8050407030006804070a4000c510909025910592505c00094401c2d1a102c0861801c0003d42c0243e0002d00c040c100303200c01072400c0c8080340041000300c908101034640450b240c4007414004621003041640480041c510382c40c107001c0510b00070700c10f004859440d8040807500b05007420035140ca1943c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 165357769 1250 165356519 165356539
    0x310050f0c0c03180d0b09010203091209030c09090a08130f061d0607050c0916020601170d080403050c0d09031406041e0204020415030c02150103152f09 67
    0x51a0110b07859204410041c600d0042441c81d914282c1508403603060b080400c02c05888003242c8007011250091056200145c0c3e64280300002c0c5140c0341400d040280007290810079215a540c0016040b840c81c64151030051032230f900c403410f0a091111030440a005440c000554010402da20854041554010351400c3e1400703842d0328086070004581d2412640d50b927050f419010003803403c44041c0c40c05510031422140c5000d28080130400d42c0307a05a82c80c80502d403550800403900c9406124850150818007102c0f006624100e5606c0d0381d6818056090b000e2000f080302203004d1503c40c008684070040114215207100180c0b0000610301a0381d4441a501b20310300d066048103425020070050301541d0040c18400c0c1041240510000915010380200e900075401c22000a54600051029004070000d860008044841c2c140c00390801e0100c034118200003400d0b80041c000101d50109090401c0c0f989500000d00d8441c0325034034540131104640c0741c800305a040301009100c0040000606840d20280c1710502d02e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 165359019 1250 165357769 165357781
    0x2e0e070f0801090c05040e030903010f200711010f020a0c0308040501080a05060d030f090e1503060105032b03090f060615020109080f21010b03010302100c022107050310050f 76
    0x8940c1c3d400e0000781100c141150401c0303a0303e401e030855102140c040f81a03c0c030700200013001a00310703588501d044401503101e1301c000400c1d001c20108224202038980e00c451510b807290360303034180b0410310b8540f5505005652102d40700c064400c110300c82d0360f141e0042010b01e4194032400c015019030414400c1a0010383d21000240220025010313190168a020f00440034100d42c03a5415201140b4015071001004040c1d0800103420240400c1e160145598a1400c0302c0303081e10030103240c103205050b00058029841b01e858001102030141045014560248010388800681001100501b01c208400382c0700d00d101c00069401d00c0306540c40030041f80c241451041003d0f070300d00020790030b8501c0d0580141800000303100c4071307a0541c0c0103801880201e005080340703080c0040103880b84c0c105100030303005070003800c00110043c02141490400102e000c1701c5400c1003607600681d5400244084080040b00794000700b00355230229117550401180018103001416601403658982d1010020841295a100f94000c24400f2900c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 165360269 1250 165359019 165359021
    0x307030207061505031f020c0102040609080c090f070e06070b0408090901090b0d021207080304030807060507031116020f0907020a05251703090a0b09010f09082e0e070f0801 76
    0x8407100900a881c900103090741b00030911034503185050260b074007040100183c1c00300384020300103001641c4404046504040102c0c1c46d0010540d510381c01a901e0000340409507040f800440d030701c454146010301c0d0315a442404100640511b4400078005140300043c4020814004080c002610080d50b144241c1da80c0c030929042a640c00440481c4c0010326131204001604000c0207010b080038191007110450355580740303040d00d19030145c1c1c42502d841401042a000300f005500444c5e0b0800511b290600c265030328601070040e00c1c46102c40c000e044050000c090811034179880c001010004004000061500c4c004da406510b0f008400701c2102c09020f500c0c1e80009900c140d0200011200c203a40d03241c200300342400035107400300362407004100c40f42c4418020303c96181e4811040001400b6036180a686030302c290800076180e450082403c10034820351000a0150050004241e00c1d440c59501c208840c01c3c08548010900358440d002d00b82f8280d0a111320038070202800a4034004580d4007504482d030441d0388024880c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 165361519 1250 165360269 165360311
    0x30e0a0308030c0f040e0408040614030705030a0b310f0e0c01030504050703080a0906030515031b040f240512060a0b0f1e011b02090a20030703020706 66
    0x107006110034030204140038070280142020124a000361498540c44d50b44641e1900400c4400b2078005400241c20b0018540c00580124884481c00409046051248004d0a5404000c1c8500c0d0103a0380c5441da1149903a4000b4070054071040032060310015041c2200804003540b0304035008054900b080c2408000da1410301c80c01e00e910001c280a480720500e0440110042c00001c0d20a80d540c0c41b070400040041076050005111041c030507224043c28a190403409416901c005080300560100088410625140802c0c20040310030310a144100012445000038003e181024100c00354501e40554201911503003030042e1880e020002c0c06c00181c990350410450020f8082440c40015006500850f510104640248001c40c100800c10041058070070003003604042e141030207040040422100c1295941c0004000f0112640c1340710b4401c00c0015034001c0b489280c0c002c5c04030460255505210251149500240703110144c40c20103042e503905020342c005002e5004181c05507041d624045c10010f904080c22591 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 165362769 1250 165361519 165361523
    0x61505011103040303080402060c030c030c010203100e040803060d060608070f0302031501030f140a02060c03090a0b03010f031b1a0705060c130306050a0b1f120608120304060f060b0304030e0a03 85
    0x8006542e403603030f0a0212a2b000202a103803140b00501041c0000a02072003c0c0a0640080d40016120b180138480fa080c1c083c04c03607110b404600000000c0c400030a5518045030b610050030345031403240381540c0c6002002095140d000c00b4907402000c80c08507070f8440d10b0007040d046074021801c030341c030303040300740401c1c410f010401c0c400101841d0035060a100001c029880201d04039440c20309941c1c0414154010031102d0f405940703006055040029802514641154440c0142c81484c0d5042d04541c1404440034003615540000ba100c2c4595a00c01c0035606045020840039142e2641744908407504007841c41d12a402c100001c540c00d000d410000b5103149211019120701540c541c4101c00303082e24544448000313000103882034040b280c0300e64468030b803901c40c000d481c018034030b50400418614404140007845010720111410f03040d81040d00c200140e110026940c4561014110a96581c0c0c6a9203070504c018aa00004102018200700c0300280c02c510100185210b54040c2e1600407102c4100d40420100007128000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 165364019 1250 165362769 165362777
    0x60f020111090109060c030e060a03090506070309080906070c0506130609060c0c09020903210a02010f090b06012d02010b090108030c06042a0f1706010608130f061505011103040303 79
    0x800410781b0521400d000300c1c0c080e08015411400d0b00000c6856070744a814058046074451100b4401c0000802ca071652005482c81e042026252540d80d01c5171620076094502e00c00d090100700c94081c02030308030300140104401018580d4a1f00c2c8980a0300000310180f1500c1c0200304416000240d41e0301a02500007031660000d60006402e04000c0d50030000c2d0000300060341c0600c00e2200c4440a0101541c240c60200040205562120301c8181c000742945c0c01c26402005072414511240000f9070110300080c1c0200c82400c1800f80700443d00c444203a48031b6008440c4050819503000c0f00305994040d03002c00c608002c10307559070b09182e0b01e4500fa80c2d1707a80710340c0140104e00d07881100020003044504a0743c151001c00325480007441c080b07140a40400c82c0042d0800380d505142c0040030082c0d00801c81c51854402d42d0034014060341e40c03410384003034552030009060300140e05030010148108012000102d0015621082c10082007040b0030310441d940c80c450247c2404114204a4203c460703034000280c5d030480f9410b5032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 165365269 1250 165364019 165364037
    0x908060c030720012d0b0d02040b0103020708070819050f031803130b030901050f040c0909112106090f0d1407050f0d12020a0807051b0601060f0201110901 68
    0x210403503850107154078a0b0740c4030601203012800300340c003800b03550500250300d03c1c3c0074406141c04544c103d500072503659002c10303941b8000021303034292a54a6000455601140c4c0011750488210069000c0e00c00c0e4000103101540014840080101d0003000d03000840003e100201d808800c03800980300c40c8955203030048c000c802400091b1002c074201a521005071042c00949081130040d030400000501d00741c02c0740c201054040304000400109114050307100d0161f80c0c9121160a0945440c0958a4980551040300d900d4000c4201480741c240c0011030201c4c000342100360b4100030300703480c0704800140e000c0701e03c0b55005e164040781880e64002507411860f0341c194054020000704420540b841e0b00d120040c4800c6203c18000000400e100340104440f003441c01000e4401800801801802503182807141500c051050000b40c403ca5400360404e0303401030190600c0c0d5a80c08101500c80c4001280282110140c030030a400410000c0c2e0184455902021940080c08001403413540c001040c081c0028050000e41c13199 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 165366519 1250 165365269 165365281
    0x40513020904110406050408010b040902180a02040e04060515090702032508070803100b0703020706121508071a04051c0c090615090608060108040213021b06070908060c03 75
    0x29008140005009100140c0480f52608907082c9800030340c010004158081820090030034213004505603c030017207a0800652110b0b0380010410f02c242d0301120090303550340c00015100e0140354119000741c542c0e807410354494542881c110000d40012201a0381b03100303402c3d41185103410030200c05401000380d90061402e2003000511340003107958840d0480004654510610301046102000308a0300780120141540e80c80c1c491402e0028103265440502a04020810b41011070740c00300300c5a06881c5240340100b40c0c80b01c841e0f00c41015040d41d030340d1900c5e800e100307040014101e0000070b4503404a84032041040849840c61003030141718040c9100b5980c202c20b8403103051409082c0110410140c912805803441c0040e00c600003d000c8650682003041c1e4004103410382d080103070308411000d004059034a44159a4981200000d10070040640024001c81290440004824040d019070b0103110045050400d0300a0f04410540da8a005aa043c008121183c00c082144030b000b00701540f01d026011081d5195803255 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 165367769 1250 165366519 165366521
    0x30f0b010c0b1e0a090b010b070812060a05040c170c0708120402030111070c030506010e090c040e0f0318090f04080a08150a0e0412090f060c080408060c04090e03040513 74
    0x2490442a0202003d03203000035180b00c00900d0040d80580c00005055440c0e142035245500706800c1106961024000240001c0880084911507440f2410b141d200c2e4540c680400d90400301c6401c010b6115003850003071006258858176200c58040320030341c409100e0300d4044841d0118420003c0183c0005010800c60703220359049440c2d680c010384003074000618100342c00b006514a030414170701120030b4000710400300203110301000168058882200d800182e81040100a60364402c81444140225100d0302191100c00d030500050f80c040d1100b00c2680d84c0c5400c00c00b80840d080ca840e003807003132045030300708082880144c0001d0528402e0340c0c402c1e201440d002c0e0003a400d0710301590003003030051540c5044040e0000d58594100c848010b0103d014a9800740c206440c08419071400150500100680311004000841040310300030200c81250801c21108501c9062a4075580300d02e13005102a44506001d209261070408010001ca40351404100038000b00719688644922451041c00c5c0d00c04140401c40d8000245 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 165369019 1250 165367769 165367771
    0x60a0b061e0403060e0615031209120a0203011505150c0a02010804110409061406030105070f051e0408061807080604060f0b030a0302010b0301060801050603071a28030f0b010c0b 78
    0xc0720441d1400c20790340380e542e01d05813040170001d01c0442d0000b60921035031216500c80c02c001100118013400c0301c05941d0788088c1c124000c5041461040d0078003c289480c203401031081c410b80540140007402003410310603400459454611a640c040c01c00076220b40c0c244c0c0041d000387da0b02d44020801400180b500c039001140e0018018200782c418000042612000d5036480c030070f2580c60b078403810b004a00b8681c034060790041600c0c01001180664140390810541946c4103404000101c59402e1803030300c51040790412002c0d900300c01c0404110400024001c00c4009001441718400d0350240d40002004101c0da40305a10b841030b902c9040c10590201c804680000c00b1900032103c090301c100000540e0110340d0000910380003c40000760702507556100102d20a04003801900003508120f40240000e0401c080441d036a81141d2140514442250350707645452029041240d024078105081d80d080d00340c0808a042e00d24900d09080d0780840e24004070300815050030700818420040503141d0081980044c0c84d01c41c03074124 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 165370269 1250 165369019 165369067
    0x10206160513092a0c0c0b1c050103060e0f0318041e0227030c060405040b01021e071e05010c060e0106051003230112030c02180403050309060a0b06 65
    0x80900010401c5030162141040051914885091300c91044900700300344031154040f60104100c000000011400420035182201c100900f450340c1d60300c49a817203440c600302c00c1e603070185a1410000000f090002a41040c5881e031605425641c982004545280d542c0c850507145843c02c00106550208a103002e610848001520300c042d0b408051210b0050422a48680b01c442514020381c04503415070601d9040841035802c065004102d501c2c0d4040000d4480c0c0154810a80704c1c580311300340240c07aa4400e00c02c4d000080d421160150700044a03000f140e0310743c86140034904a150500a02d103100810b81d184010480f1810b8481c9041c416564807844090310f402d10145111f90340300c01c0009020f8075800d203811401c01607585c00080462200026001d640b00c2400e1040041d550480103008104030400290020b40d41414100c481ca00703148003080407040c44110001c441c00284040000f499044070066102d6030583e02541e03090380d201480f00088070004135045400100c00d0201200c452540f40799802044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 165371519 1250 165370269 165370297
    0x90a05060a0f150206061c061109060301080f060f13021201140112050708030a1709010b0a0306090b0702160501030903020111030a060305240a0b24040f050102061605 73
    0x99100d00301c0480d0700003154060104004001c030b1103103ea030390510041c0c1c0c2000007100e0300c07039004101d451210140300e44158060a80707565140c0c2c205491030404115089010007030100e688941e9101445234888464501c2c0030b00600803000001c0340c4e001011030390ba2044107102c11004901440c0e401b4020405042442c0c4e1400d50341c0c0f0b4220203200b0310040b246600038180703c0c0880d40b80034100e2070325600304440c40e84a800194014000c0201c2030350032001840c200c40c1624802c0042e5518075110501620200b9100c54004d010550702000344507043c1c02c4405018052040d04d42652247c00007242c0e50502090040c0142e96520750034040b0390300c0f0350445213402e8020b00c00841d01e14102280511645d01c180c9411141c50750710201081002001d00550342c120f100b006154040d08002e5103e100c08607402026000c2c541e50740c5114a000f0380d5417450070843d40305405980030f80d86070011420b1860398803900503280d40300c0e24040001600e6100141e0340c0d104034040d42c00380098058400068030203400c081015007443d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 165372769 1250 165371519 165371539
    0x901171608010c0e0108090c060717160309080a0b0703020a0c060e06090f030f03060402090112020d050105090a0b010e060a0c14060415020901050a1107050d060204090507030209090a0506 82
    0x460000e16000c4003620310400009074030003c80d4000340114003510f025a05006080e070800c8034203400440ea0326000e240640e1595981e04080c5400c42d1611201a1451a00900450030f03007841c500b030000169241d84244c6602c000a030f00d86650a50711031462100400c0300c01c0c0030380014101d601ca5000b8004510560a00641c0440707607580300c000340c4221076030741001940440108400c0c814100300a102c0c170b40000010310310b032110281000d00c1d20310008001d03a004a40001d15900982d05c0b5100d114030218001600319226801c060a80002e0002031142d6840b0b81401800300b1241c07074842c81403140c4503005071038407620f0001c03180900281d030704481415001d10041035a110080340c501c04130000341b48140005004c50380340c0b5140920060030070000000c0b0041c030521801941ea44c01038100d581ca011035003010041000150200d9180c00c0144d008540c0140c0000c130088208032058001d0b10a8400c3c000701407010b40d0b60354100700e00328003034845425441200c03c00820f0043c06a940038640224001d8102404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 165374019 1250 165372769 165372793
    0x7142b060209041a04110c1506030a060e0a050f0c06040303030902030304240807170109020328020403110f09061306030605071d09010602120a030207050a080a09090b090117 76
    0x840340000410800130340540f807002000e142c64403413804840010074005040c008039104031991840f14a44241510350b044010940a40c1c0804c0070410301a4007407000e010040a502d00d00d41c88440d0742c50200d516201e01502d10030b0407034022802d0503040401810850030145161000c40c0500741403101030783c15020401c80170448032a03200409a103521030610042d00312000060040218100a040b80b00308880c02e81021102441004a641120003501e400340c0c4940380c1d0360459002000d2540481d282d04131400c0e04056250154018004aa0050a407107480742c4051081c4090544040f0a6580c06070810300000d5841c036010030101002c5035900700001e1030750784036030704c082c100d1b0700c1a140140800c109020100030f120307940b0280c0d034407501305582883e025450100c0182d65880322004030700b00c25002180c0c050300a4800e505880b049604002190100000c0d17090034207841d070044002d0310000d21500e20100c1c8030300c11400703180b540d004060402e042a0703103464030b003841d103001c04126500280900391000311 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 165375269 1250 165374019 165374021
    0x31b01030b0607211211030403080405010f0501141201150306090f1a01150c02090c0a02120301030b0702070501020307050705192301090501020f0a02091509040507142b06020904 78
    0x1342c0ea6080d000d0301e020704200c10b24040c003d01e00903000e00d0002410300041407030401c60794068a8029906040a90380e9444074500760380034102c04d003e135401041c50f00300001400b60300000407000c0c1035419560041d89540d4074500fa03098861903030b0800c030003a40000b02000060829401110304e01e00541484215440503540c90710208118005004c144200d68010700c030808602c440004040914240715410310b41e0340e03011841c1d44800138180102440c0c00704802805900074007503035604550020345a9584c6d80c403071500041015042e40da2100500c1100c8c404603030380d40008111500c0940210003480c08620b8070f810404d108100c030750f4000c0c0740340c256980003d8201d91034620701c640784201c0813400302d100f501c54001000518168012811903001410810040d04089100403030f1a8060791054155940c5884d2100071400000c603040d003007010182000180a00400d003c0103480d60f21005800ea50200c80804c0800350030940c10380100034000500386100f003c009a61840035100d880058280a403080005d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 165376519 1250 165375269 165375293
    0x30b1e1c050a0c090c03110c0d210e03210105030303040f15020d09060b0105131a0f0f0301061409012c130b01030f06080715020a02100c03020c031b01030b0607 70
    0xb044d01a1100b05542065815019106081d00d1218440d8100300904003080d03520f1544400d18014440700342d141442212a00c1d480d4060011403030300c144002304000010998951200483d8034180c1654a40350080b0849054240c0c101c501c024001c60030340d104c41d207c042115881d540201d42c041003402d0400b4504882c2c0c00075003107600d5a02000100c82800d8105901684c200d0350b182410400e0030085209400c00640765002629203002c88040e500c0080842486117100702d10781d14194480110340d43e04088001d00c0110f044c0d4201d5916015440005400c010140c0201c1001b03a001c203804800790f0780021900080148003050000811038144800c40120300003c102c655589491502e4200e510130650301030007281640251024200402c600c0c10031555118009401141000205d4801805906200b0451051155001404814162030706800075040c2543d01004801600900075031128524021800c481030205170519107041984040044000f000c1118405610030703810701c00301c00410801c5d50700b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 165377769 1250 165376519 165376529
    0x605160f0b0106110d0906030b01020106030c0f08070b03040506060904020d0b07030507030c05040f030f0203100f020421330203040515090a0c050d030e04020a030b1e1c050a0c 77
    0x240d075055041c898000c1180714042005803460384445003545500c0c0d40070481d00e04489243c5070000300306119400403130240001d64006803a0b8150303600013042c00b038000320141c000c03200c1c01f07400c0301c50069503025403072414082154042c2c0560001c00c001162410305103150f941c010720042c140c0d0807452056444801e804816192200000da0381c00811100a41501c1a0b0501e114107081030707820940741c40d052004500b100e0100401d9526500d00c41021034400704515040c048013002d0074064201c28080180c0250000c2c82040c030101010161000d43c0040c80c0306581c40c3c2608803688000c00e0303407119581c0c000380a669865042c1030f140f16242e01900d441c0c51024500540c450b90103441d030300d01040c040c1d101000c4003030001710f13045d00b21144105c00101840d600381c044880a403602e0210950506080d1070921290307441540040c00000c4103078840b90702d503208102c0c5401c116892088800c40610950718030003001c0102340c010348881400d500c00210b095a02091034886c400300d071000e00d500d55551012442c25480 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 165379019 1250 165377769 165377783
    0x50d020109060b010905030703120e1c03030f0603152705010b04060b0306130506010c021002010e070603050613021e04030b040530180301060602150c030403090605160f 74
    0xc001c0030803030b803409808040f0784246443c44a06040a0000c3d03290130407403000601d003032005c60300c8850080c017400709031484580003401e0340260002000e15078000c0320721400440c0001e280002d40001c0070890710a81007543d400080030726422840040240082400c2c28042244040202d031030901c04031384008200c00d0700c3c410800801c20f036102c2d0090209941060300000480f400600400405032550700207502c005244160100d0162105401070340d400c000300704040d4200c40016030a920303a0303030150042c8540c840c100c400c0718403280d41c460084085038416240340380e202e4501c190445c80401d85401074181141e06180840c440703135411200b1011540726a1040b500350440300200800d200c02801414000030054075076246815046040c0300d04a41e00c076076200c0c002400402c0702443c041882070070044002016008201c00d68450f4000707035540c2401a0701132001e42914002030360108500b41a2030040c0d0341a1a59002c00313051210a840d503030404502122444400912140841c3e891212400c0681c02455 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 165380269 1250 165379019 165379031
    0x618180906050a02030103020f311b020c0f0f0f06070501150806061c1e150c05040b1222030e151207080c04090623090c09010318050d0201 61
    0xd401e100360744000302010307002071040c001040944c403000034100c144901200c000718005944c05115500e035007000c0d0307803d43c5101040220304414507294030102c0003105500b550301000e010301d64100d03035600369074064a402208250488006040c602c0300144a43d034020000720030900c130100458903a42003200140c031180e45440c5012951201d203140d010282c04601d025140601d403800100368910b10744805803544065681c800000c0c4040806200a210500741010074507400d14100102110800ea660240035440c1c040c64040c964060002c44086410303441d03e241c200000e20002d1017501000905071004241c0c03c5030a601100c203034101402405204c1e4948040b445240410b000d81078031000080000010104110514031015010303159021559142c8414555201460600180580d40c0810f03000d50400002040d424166820462000035015462000540c00d008120000200f40c800142600d803c000c2115554880c2d0069041903d010001c1112040c03165680c41c0b134007003019002401030355210 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 165381519 1250 165380269 165380273
    0x1101180b0906010608060906010c060903030c11030a12050702070302150a080c040819150903020c030c030601180509011509050a0e0102130b09031507050c071a030106181809 76
    0x1031035081d00548440010841d07907043c918041c11075400604440e01c42c81d003010008005078850108034150f01d902800074010040c1c40d00c1e0280c0900301c12280e0601144016110b071100034800401d69001c5480c40d0f0301d40350348240d2607800b00c00801c1c01074801800c5000c0e501011001d0b859401940301c54071410380b5501c1ea1800c1d001c1c4010109000507051100965080000300806003000592140d54952540103d25415035071405201188421580681c0d650400801d402415008268161968002d81c180c6843e034090b901050b03142c00c0f0074007403026004407420503010846185d07031126a000f44040e00000d000e00f030894170210700c003e4a43c04400450740352805c0210001483c011005016031000003542484518041d0300b1003503086000d50140c1e6400071a09030b1440c1d1301000110a541c0003d0031040d61800c6c880002810396100e840003000d1032103101c00c0041d1102d5200702201c0c401c400ba040d403904507400c0190071039040903c0d000c842681c41c3d00050204519100111030b00d40212200d9000400340c1180c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 165382769 1250 165381519 165381533
    0x180f06050604060f03060e010605151b0a050a0f1401021c0c1e0c0201091802091002060709120203010e0601060207050312270607050321061c080307110118 68
    0x70505409981462010820034540c00c4070380c002d5039031002010500440c94540744d1b0040107283c2c08580c0c02810308142007100e040a00040410303011000a440c0e80380031714a0340c01d907035600c05a802400ca90200f44420041031010140381c8080340b01c0e00001c090000301d64400ca0a907080b1003030f800681c0d24220710307041110f03030940704459084005007450b80c00c071031045500318101c01c8182000d2060007414400c40f0216885121740d0b402504000030b0320b0016880e1a03500100940101941c10b000d03644503118103485030300006809210301d00c69555040350a051000d0b1495020341284d00326015902e0b41a44000a042031182c076000c0c10b484d07801458194505070406123000c0904c0b803916249102085143e4070301480e0065040e0b8004400c4212600c88560b5000c07138150302c510400a00a800045100c603400503512055900c90704254215041a807515810088880c0500f40c4206407004180405400101600081d41d84410302d4100036040c1c402141c50942501c3c51494510814030300305460804010403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 165384019 1250 165382769 165382771
    0x30509010e0906011e0e061326070315020c10050906010609060206060f0109080a050a0c1d31030e1e090a02162a0b031608040501180f0605 61
    0x421656102e0340d0401c600064440c150204800c0d00568000700a106240e00440218118010281c41656030303c246404020f44001a40119090720940400315011030000c401392480c0490500b01403d007840c40c6980e42201d2070002c1c8010000b05409000c440c149040c1404003580503541b0750008600751400c1d1603020305181c0160080c07420301c8550902401920f0380000d4003035004c0350a40c1c42c40203100c032100041e50b101c0250340c072811240c41152420400c1002c04078084a81038072038040d9002c481c3d120790841038206540c55005c1d10702103024000a49031010000040710203244040650f0b0003051440e0704003c881030340c005c16000b0a5250044114030300304100d038880c0c4c24183c100002c041d008100001005440042c003810202c507000305080740005140001e1f2111298401406030342c10442e48464910004920359005881c0811140001c140c0c2c40002124400c043c7c140e00c11442e074200f007500703480810002c1c00a841d03542d43c500700f0301c0c032111061001076001809040402140c0ba00351501c2c0041d604 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 165385269 1250 165384019 165384047
    0x2031005190911060a0225060c060506010c200f0a03020904080c01020c0d030501140103140117030705060106030e0d0e03101e0501140301060b130302061b0a03050901 73
    0x4541410400440081c40c500210040c0004000c1551201400d00081c0640c0c0302501d03030740c00240040d055162580000d503c00c0e10401c0c4024520035840202040301007070050384201d8001c40e03500c40d80f40b00018aa5400a035200c901414954225032280d2100c0d82d40c80c115400071550485550840d110300d103090441d40110388412582c6400c81c42c15030340411441c050240c0002c00005001c180105003040030340649210b030b05a0030440d01000141e04000300941800e1207400c1a101043d40d107075295510070701130040740240c400b039404000d1b46403201da00c0b01ca03610529038031614041880362a0000d4414000d8500030030710b40c0c3d0081a8514202c208505100001810300709100e044c030200c1209850106a0021302e18201da0005010800c10070362403856401941011206484c102c00843c40d51032290740081c2d02441517008020140d100d814442840c442d031144402140c500d080e0400052408031b000306580c20070035554103803000b0040c150900e0030400ca030045020540c00b20b804945542d00400d0004094 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 165386519 1250 165385269 165385271
    0x20c010e0402030919080f16021221090105041802030a0e28020409050a0b0a060609050604150207030c0f030b06040c1b050f0307060501090507050306060a0302090310020f0304020310 80
    0x420039640666903040c5d42d0320411000705410000205110351141641c0e444201c2c80b040d0396880c150145050420405050100d104004149221012a8000400c0703002500140c005012201b10290080c00c0d903084520301d1410800b04010208a04000b00e0428900f0300d2280700c050388038140500c40c641551585110b41c007050380032010b05440601241e9507048074100959401c554115240045009442d0b104005440c1703200b5a602402000300c40f99125115040449040001c5a1546001c0b104c0300103d10a8541c019408d120500c1005492020500201da45004a0305070300d0f92a59580c80e203c0d05079008116042c2c00c00d0040090000680035194490412102001940302c1200050000081c150706d5600c0201c050b07110504000c010407050100c507205030201d9072038000710718000000d0023090048400090030000030540300c900901c01c3d02e0003a40010411802e10b407090381c044000750840c40b00b080d814400d9441040202c1898401030204c400442c0710b140c0d40b4a418010325180070402e81540e8452 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 165387769 1250 165386519 165386521
    0x50306090f0304270e03361908060718210807150608012403030203271005180109030c120201030b10260f010e0c130303020c010e040203 60
    0x81d520201c1102c0540b03918a01c600601030b140d18a104440d0340341d140540f4880e18082c000c4400000000241c0155060400707030707a00410309004548032284040c00c074661003a0405225902e20300c0d10b041c9186012880000102c1c00031f43d07400d0a1446c0000580b4000082800e902d10801600004000d01000e0106c540400943e0000f0b40b001c0004005003401c060626000802c5a0003000b034804a400c0c0100e6034078906200c596200e03001d8030f00030082c0e42032101e440d5070441c081600c5032101240c1301c82100e80640245007801003201106144120030500303c1c60024402900e085580d0703a0b0503111250201c15a100b6031101d0121280052081c8403c5000c4c0c140180d0b0302d02080084c94040001003035034a812141da8032842c0700e2006802600e0050440f683c080f1400003850250380d4030581c01c500441e400d402c004402401a845032180740c07402da402c40306000c01782005011070710701689201d81040d0301c5804580b8040e030032a00080701c94416081100160059000328682d5a071081d030700074008504071030441c61 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 165389019 1250 165387769 165387793
    0xa05040b16050f07061401030309060e03070302060409050c040f0e2d0402011b06050103060203060f0d030f05071713080709062103090f0e0f1302010c032706020705030609 75
    0x481e0054000003900d03010700144a008000c4107400442260b2500c611b5102d180d40c4a1138050000c070742a014890000b056040c0d40e050394640040c503075040b40d40180940303140c2800c140000300644401480b00000e40c4040000040c50410092401e000780843c03400d9800904040c100110310345000805c0060300960b882c0c8201e844280c08082581003542401e161550301040e21402d21448030000002c1c1c5209d16000001080c010306800a40c0305002c1102c0400503140301030200700d412240c9030740c0640000c2c5050f040e042030f1805080102000c0780200455010848500500012a444842c1217442d9140114081000c004100015000742402c80414014141005a40d210002d034488040320b44500002c00641854000c01d00711018090790583c0b21400d0740c88010300c41a038041a0f8008969004140004100d000d081044040d1503031305075100c00c0f9010700c98404031805000b040945038002d02c0402c02298401c4d5510386000240300380e8019210541c1342504140c14003a0007001079099030401702d00703420 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 165390269 1250 165389019 165389027
    0x2030d2a0c2106060902030108030a110a1e0c05030c030a03030f020c0303010f060e030309011707120c0f1403090312070e0301020a03091101031b20060a05040b16 71
    0x6004111400038140d5400905001150598aa020b00c441e58003000581ca01e010b07410120252203030040d40144510f40da600702000891100344030f0410907030030500102640d00d21035141d451440300207400701c640480068480c0d59240b5000d10904008118400c9010f04000f5011a9000240800c0b0050000458640042901d5154401c4000c04160b80c6840240075401198142c84908920800701c989942e10743c81d844450006900880021500705541d0807410700c4c001040790311401060307423108075105070b001906031240f90190150041c800c131310740507116200192140c514114295600c0d8600d6003082c1402800200a40d001ca100f0f0100810800c1441140041221788805064061880c5a81c1b03004084030740c1c0010030442070385540005110070b10715502d070f08150700c800d000d50381015070000714100550443e01c0200c10420140e0580c091440c00900a441074000c3d0100815a100c0083d0782d81c640390300b0400102c800401c4599680e007400144030109814a5000b5060080905148660900a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 165391519 1250 165390269 165390317
    0x30103062f0c01090b0702060f2a0f0c01090c050f0d02030c01051b030403080409050f0402030a020909030f07120912030923060304050606030607021902040f060506040608010302030d 80
    0x40c000d00740009150215600035445428855000480c4d4130b818141190004e403100e03010b40301001e00d64450408100c034100d40e00d102303044845001c0c207100c0c621449034842480d40c0c0c111804c200d841000a122000c807182081c0549983c2c07602c07403200c0702d004030308001c01c1040e20500403242501030b182d83e119440060303c0000700303090144c0090031f001d03407a072080c2c50400ca040b401041d184074041c0004140001000140e40141c410740760804814080c0b942c41c4130541c40741c240700700c4000c0e62503804807542002500b05007070300540201d5554140c0f442c000c10030800d03421607404024112001e509581c201d540450f4040220000750005264002020250f5100200200898018a03030310302d02c14010315502c54401309030103100d40006803040b80c8920701420426103900c0f00b02c1e81c07540240a032000040c40c3c1d520120305c10501c4114030070042034124090f020302000700b200344d1541100f0342c1e03030f40c0300454035968040203400203002e1991407030340310f40c1180705150a1607000b6800c00c041c0140414191403400b0103100701 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 165392769 1250 165391519 165391601
    0x122d0c02030405090f130807030e090105090f0402100908030a0c0b0105010c0c030b0c041809020901050f010903060b0f03120a020c06090a03060c120c2d020c0d0f06060b03010306 78
    0x380219150040440d281c11b040200003803545030005040030416070065428400844203c0b010a41a0b0340c920500201040803509806180c400c1d900040040c9403503010302541c0ba00924245650a89445030300786507038081e0754094040703480400702a007007203c0304a100d4003512080c600303000324015560701e420400b012804000c0c40509400000303040a240e10090314024a0308122904030641c160f44c1e0540201042107050780030303094080022440e804c0101b0100d040b02c10695504031841e25540328100104001b40b1855808010350040b00c03030507602000382204050800094568031201e140c8081c1c5030490201009024500034081c02d0941c3d40c54000325000c90340c1280001c1141c2c100c01c141100c546907440708080003640740c203448030443c07540720700c02c0740000543c0c0c13821007400154001c0703c100d402d140030b075080300590204035051000d08103130a51718810781c410980b000c10440c0c940d0719a01641c1c55078000509010000c0010018880b0502964401a642c150441c8a960900c95061141c035100d4000b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 165394019 1250 165392769 165392791
    0xb0a0c02030f07031e09031b06120213050d140d030612020913060504060f0b090906041b090c05030a11181021060303260403122d0c0203040509 63
    0x44024903010700a44440e042c0008085440511410406005040140016074440c88c3d8445100400c04207043c20a0544565440b0901e000c07a061140300301941c00300001c4080e80d406140001100e465008850070940d2180d44010b12002072840300614240b01808a501051705042c0c080020b000d503000d4036110740390103607640790603035840c0780d01d071290044000d000504032481c0604002c1804101c3c2e0050900381d544020601c02d4010340c1082160000e8251100d803641e4114001250000361666000b01c8112400111058916525000c1208581e1517643d0038020030300000410030085100d01c070b07510402c00f407002a00d0405080e4030382e10580b2000d000e0740d1402404207080c40001e0500803d0f81c0c5a034050b055405650910b00700384420060b00c000d01c07041f40494500c020007042d0030300100c44000c4410f0700c4443c00d0300c241d0301e40e24101c6000e269400c1c001801d907518404c2900d009000109000f040f0308804035001240d840c0100e0508444040c4280411504280410311240d030fa0000407941008010103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 165395269 1250 165394019 165394027
    0xb011704030e0d11030f1f09020a0b09030c0d150c0f050304260f04030b0a11070602160b01030b090c1e0603090c0a0620010c0804031b0210020a0b0a0c02030f 69
    0x80c11094001840744295814807504c20f01a2604c0c20004190a1010b44c910301080325000c031101f00310a854116400035400300c0212014002200030001411450300001c04030340e407404401e004900b0548550205845074500c400d0914100c0c84540a000c401ca003061400b0810808440c000606c01d000181c0000d00520002c0f140d0305110304600c490300000c3c45400b016641d40d440401200300c0c4c0b503015110441d00350300d0840000d803140d04603105068407140c4e4141141e2515403d5921003000354000003018200e4081d004000d004104130100080c045c40c071840504c54181041c1c00c8640c078200140c031110b40700d0100a5a11000e043c40c60801c3e01f450001910b031135890740c880484a42c2072401c4503000c00d4000284000005110380d21031003040f48003104c0c6800c1604036030681c402a082c0c81e01c88035035201260f01c0a001c00d0000303102d5031000c1b0851650303503a4000c060341158002040c1d026024541d00044e403103184e0040600155600446c1c0200304201c1c1005900c80401020f505e074040c4bd2801103110f0004a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 165396519 1250 165395269 165395273
    0x3040b1602010e0303070314060a050d030f0203130e040302010515012309030d1709030f0708030601030f0e0f0d0813020d14011107060b040209010818070302040608010b011704030e0d 80
    0x50440500f20b1100c1080d01d84078030301004001c2c028900302600505103007ca0b808181079003480c4048500b43c850181c0180f1441d0742507181a02e8403041003502d801144410004490359071709810070b2101400e9030a581800504050074020b081d100c0c054541c0c000c01e20b602c2907400003680c100c1000f5100d544a0000ca080050307522400b1380403409480c070344a4050007440a4004500d51210001082c2c0e141e10582e8681c545400c1621540ca000741c1410101040e02048041d000c244203002665010205140200708680d00c0804001039643c42070540c00031b640400910300a695082c001020401c2a61170300300c0c4580303810481614840c41ea4a0060300a151202601d0700b4400005270301c49080351408024000304078404402d800c0d41e4041001610310030f01d070a2000c0d4651405008481c0c0420059454141640b00c1915a0242c80e0309581c645c8043d102d15a00000141c4440c01500001c0106100019401c4000b00001d40304d4110500030f0650070b10040e0030040020382011420300103042c2907620081c201824 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 165397769 1250 165396519 165396521
    0x6010603060e01060f301e0c2309150a0809120705030409020703030207080711030c01080702030a1d030a0803010e060406050a093204060f06061b0203011803050c070b03040b160201 79
    0x1701d0980140c03402d00900700840054a47c12004991202504101040140b0021200264250040f0305010b48040c1280112202d0700054040707864010500010300b4816000e18915911030041100412094420090902018002000d500c1d41c400310041c60301c1801e03030300c05440740326502520900035408540601450311039810f0700e0080d07030300c5080d00703541c3c510302d09142c41c447c0124082d903032007445080c1c02c081130340d40b04030000c902070b1800360000c50604240c0541078038410751844840d084503a29424001455500304a08515507000d0241c0700d036a54142100b01d906100001c2a1034040c1d410480100890703203400240d6030880700300940014401c0350750040059030030074403590810359075840d510240f10750740c10010541c00b581c0b2440b401c0000d61000e205a0054541038840d04001c40e1801c00d05482c40d08885d005054010301c01800002d042c034081044902804607802c3c00d038001100442c10304a440b00400c41c0318054100100307024294500b40d42e50b5000518000c1c0010006145000007204e20360003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 165399019 1250 165397769 165397847
    0x190b06090d230f0c011706090702160605040608060d0c03081813061e140f03030706020a0513060309020607020f030109020d0803060a051f0f1106010603060e01060f 72
    0x41c1580d00303034420005840c0c01e07a489203e40d9240e8410301808074154910740c080e82c2a14103160050880c4440e83c1d0340c4200300503c500000b0420029801f074401c0c0c540a01d1601883e01d800b034206900e0301d81e143d909100000b0607030038005203a00c3c0108504004000030841000051003225444000d80f41e45001840480d8141c10000b50321b276400642001450082c64207a41181c0c06031107a0000244c41d0b254003074080150706c2030030b200e5804a10541d60544000f070401c0d0002040590000d01124035001d25513aa201c2243e0000100a002440c003046007200c050f40480090010041c0b171405000c0280d20b5000100d0500c24400024454107142d441010326450a402c800780312500107000360041103240c10110065401103c80c5841090b2280c400305241c1b620b10f0305000c0440d80c81402c42201450a00252001d07040c9a1620041c00441140503144802c10080180079151599000c1201d1b454400c5403a403402046e0071610030300150740c140c080125441001262045d00842c500c543e12005160200b680e140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 165400269 1250 165399019 165399053
    0x3071103100219032714120706090309060f080705090a05180601090b0a0e0f0402040305060c0904050a020f0a030f0e0703140d05090d06021e070b190b06090d 69
    0x200109030382412010702d904895626a03113441c14002e00c00003c8004a5440c50064080d143d5420b001c00b09004c42c030507044000c80c04042104a401c0003288a080348643e4001c10401c4603540c2e2544516010541c4c003ca01c007008101508241f40c4c1281d03a0440075064400040a02c41044004a000b81490761030000d410028907026110b04100010003444032011401100c1c1d041c0468030380400014058012000c035031400000f59a0b440c0c486c040101008038104000b8415035025400f80004004100107020a50180340c00b540e03120360b0342092609000c1910780052404100b07501c18040c1003821203500049030002016880c00040e00030100716190010802800b03002028803c480c4003204000c0bc21501c0e03640780601200300c0700e03900d100000880c0d1a10400c0c07c0c00f03822554260300d0400145040d00501320010301c0f00124099085c08042e8030400c6d401009050356200c50090902458250240c510306940d040503800388020440f28020500c5445a00b2400e40500d408150030b2007030160001d00c0401c01c071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 165401519 1250 165400269 165400271
    0x105130306020316020c0f0d1a090d110c01090308030601030e0f010c0315060f120f090819020a020108130302010609060807060f020601030308010512100f0221090307110310 76
    0xa5240c1c10010000d4008a461040340c0c4c00814200700c07100d000282d01c80200b1320061442e00700d11082c00502c42c001c0d0004800b1208240903582680e00048130355843d611a51603000188000801c0b220000d04082c0080c006540c240c11070317001d14804d80d910400c840241c0303402188282da80d8a4420040300180100d0b0341c00c0c41e0a00807140640d0990390103400003a480e05480d07030144291401ca802610940503503100710300200b007045160a017560301614008003072160000340021003051154000c03040d160036040455100000003a200e114a02110399201044018030043c5030040c5240d00103011080041c280e640640d070400f2090341014400d4000310080c20a100f01031115035618040e0540d60207031805100d01250350101d408a80503c0040d00d9812660166205c20744ea900e04018400d40e48500c0700e0403203850090600d142c070801c09a026000c1c0c1c11240e030030300503550322090b10880076035942c07201c2c0c60b00b1a114140501c220349100000b50380036150814011900c6070304140c0068a804180c140c009581 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 165402769 1250 165401519 165401557
    0xe0d020406060306141503071404120f0627020108060307031a060306070807021207020a0914010e06100804080a0201061206020319060620071d010924060c020105 71
    0x5140d140d0402011144842a107014034400f400800c524581203880040941e1b0040c40001c004c20708c101700c143c2005070361424a6140c151140426128200c01c3c4009559003407448001c1000c01c0a107100d02114080301840d01d41c05130080307007032a155000c800d00c2d01904119071100801d002c7d45d03046c440007004507442010396114104224000d00088411524540300c0d002d1980002c174403070301070540d49206d401164080c000070079810711205401e030003036030051381c101041c1c03440410030113000d11845160403c0003c4610013585420a0300c1c2001d0b5000300303424000d010314002828820f41001c1c195400c5075004203000c1d100c1c5140d003001ca0041010b54404075415081c02001414410700358003c60181e4401e41c000004e00c4e001400640c00d03940c05201b154000f50340c81201040a2504400040495040105441095643d682070800704040c00d084400c5401c1180d004003c0026544174001170515822400140b41c005e0058880305c280c0148200740510040c404a50110fa02c6103044401c6c550071100d0340c1080b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 165404019 1250 165402769 165402779
    0x80405180108100b03060f0c040b0c0309040e031305090405120327010b10110115080f071d010506070c030506040305031611032704020d0c09120506070e0d020406 71
    0x2503104288600c460900030801d02c09a030000d81e0288042001019004101c141c0794000c1c0c620248100408001c2500b80600c008682c002e0f0341c00081c404a03840700011501d800303c80382000100c07240401b00a600d9441017001000222070b52000360708450003110286226915400d0007820501d903a201d91400396800000c1002c1b03080c020440e03001300440802e034a1041c1c07408841030b9080300c075107803000b0380d1168030403504450f480d02c9000e0b103942c141d500c000041442402d030345180c104c16109801032440c2d908130112841c0f100704204916002010f090001010801143c40305d44080c1c4018010360340503070b9000811200340708170141201c0c000d40d803080403500c6514050034001d00c90340041c0d5001d0b920803164103003100c100d4818803009441d808810b0203503150924030070303034401c001030820328101c0c103c0881e40c4808419074031b40c40500300d005141900441c600042401c02450f0f007001d900841c000580300d805d10740200d54002607980e032100e580d050041800746040002480c020340c400c4000c0d4000c1c05d010740454 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 165405269 1250 165404019 165404059
    0x1103030c030403170906040b0a0e0907020f0d0503060d0201180b0403030e0a08010b1810030c150f02031e0304060f18060506040c02100b06040506041d0c0a1b080405 72
    0x100f102c0c094062411840815080d4401c00c0c854502c41030f510030020322040c80203c1c8604c0060100061030b040840c078020085002c11413400d03049402d58056001405a5028054188505c1a403a421447d04034a1032910390b000500d0b00c125820701030f0420000310760f01018201700110060241c0700703040c1c1d400c1d15207540b03107001002c195408240702d01450001c00c002a0b007140c140035015580e10001d080009108100d05404440f1030018881d41c1c1c8415200c1c03000020a000e4424140038098800c0c0080700d81e0001000a088100006070b0002107500402c1101802c0c9000c4051b240168441c80100342d5907140c0342006800360540c04103134620a80f0b04640140348005002100300841c0c80b922040c0104e1342c40104200499070b01c08001405030f000724049910500b0a0f50141040d02070040406081035110404100c0b690040e4004a40722130419000b03285c01c400d400c91990f4801240401d0030701d80120200d0040c090610382c80c01240038400341c44103400b0048400d00307640181002a1200e0007600d25804490307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 165406519 1250 165405269 165405277
    0xc01200304230c0f220b0306010503060606031303031b0c020102010b09070e060f0d14011a04051003020d110a2c030303010e070c0b010e010806090d02191103030c03 72
    0xb984035a04050315100465040c01e1031406101c0392010341010099582400541c0340c5620402e41d100070040120102141204e990001200c016100080c0d42d04080c02410310f0040183c11080c07117540481c0c200b1030107a0f110700881e580201a40c081e807800300604d28080c0c014082e001c3c1451600d01d00d9102d42440964031040d025182c038001d9002784404a01103040c00001c030810b6450400003203003080000400d00b400b20051403001c3da010720a91420b00c86640003011222200020880000e00c10010080c06400201d001d00c0e941c11001c4040ca000c0c50b2800003103a50548070740010605030042030360003554001c0d50050f841007640ca54502d0399030541c01001042ca085103130310061900f68407190700303031040400c013500405514003034011461a402d150054444520040c9400c080101c40c14102000400e09640c00303000700980c01d41a921541002011070503c3c50007804026590320000000440d140d00052040d0361200800d44002448001d007010244030312642d0000c1d42611000030040c80960f0008018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 165407769 1250 165406519 165406523
    0x303090f150f0c0e010c0c030b0a0204080f07051305060103140901020a1701030f110310090602130b13140d0f1a13030f030c030b0d0c03030f0903030903080c01200304 73
    0x1003224000318500c0d0403c84040600b040000703090f241c800900c0d540142d4000d808603006407203909040da9a9622105a42c504991140241e90042400c010090b010031000804002c90800780900c9420309022030441c64241455080d041d13110300104007070b44d000e503000fa0100d03540c40290140b0362902000f101e01035408907242200180c00e003442c10110000d28060b1505036540300f0342c5103100f4209170b00ca15180144908005a2501400c0c202d0a001071041c811010030b54443e040260315a06104848c00341101c09074040c21040b070040100010003400820a401681c10b01c0080e1825181c0740b20100c0c1c291150814000e080d0042c0744c1612043c8070001c0000c840c500c1c81c248602c601555a1861114801010440140810340c40c00741f0ba051540250040c580345101c510300040d02c5400315001903e140c98800d0b05444d9450104802d0003030640c450481d011542e07182c10410f09052840d81c004140c15494400030f00b83c41c1c0e010410420f00b010a4110b110f04148100b402030b9048007a04a1889590040e102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 165409019 1250 165407769 165407771
    0x1306090b042003030d050a14150301060509040201080613020c01020d150b1e03070e1e030c09010506120c09032d010c0e100e0301050c21040f030c0303090f15 69
    0x1030301c004a400d44050450802c4094040c50402096044210281501800e00c6402540740e50140c50809051002c0c1481913003c1c00c4c104a20425040902d8211006500b01c1405210130360100000350340c00141842d007082040d078841440502508c0d90718000d000704d99000c032055000154078007880420b80c0102110342c44000321a6541030790380540504a21840740300355018016400485005080303d40955807141e500d040540380301e4103050018403111042d040313402903050458208200c1d8281088062449541982d40518035410100040c210740907010020350001c14010006680d60703500000c3d80c2d02908080d0807601042c80510000304086014400c01c8161010304c4004480310005000e041c2c0380e4019074072000d005041d50403e20141b10b926400f00c800348a805a100c0440e82c800b440741d80d104800a13114140c8402070150300d841c101442140380c410b22000f11050102158180400c0100a6494181040320090515064001d809200c902602685085041105110140000d03200442056034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 165410269 1250 165409019 165409043
    0x6011211030604030c080705070b030109021801020a17090613030507180b18061f0e031e0c09060a03060525080f07050f040b031906060504060203030601081306090b04 73
    0x100307156480c0d20441d0041c0002d140b0800c40e5020407908401003883c0c41c014010740da01d89440d0035608045900a9016004030b541c0050600e60101c0444180311000c207027440039142400458840d03101800b0000068031055000054000710381d52070104494a0200d080301c6044025602e092003901c8100300d208168020049550b5201051017512504000060081080180000071890b803a4100001080540c0000103150a0607142d42210000071f110000c0303a5440d200c4002c03c600f450306180c41040b10008110840c840c07a01100400311b0800a00b090239954a56503645d01400511816250b9002a0050b446c2409205410400c5003000240c801c00c040d02816540f514030003100c0130f200c200c030401421311030741002c503500c0b6214800402e43c0401011401d420b05c1e466414280090348152488100c01680ca01148402007042c081c800044c1103608103e420986080300c041e40300d10000381107504004c10b005c0055200d9800803221000a6040038017080742c0203003407a00346590002a02c0c1590a00b40f050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 165411519 1250 165410269 165410303
    0x90c0a020609120f090406030618032601180603120f08010e06090f062206050a06050c071701110a052107020709051005030d0f030c0e0a05061605060112 67
    0xe0700358000905051032601c1d01107a0120301d1001d801c0b07800c19986c8151107900010200e555800b4031691140741140d0074900007110b1030098030001d41000a48284a0004045d43c007140604400c0c41c1118658174800c24400010031414000b0101034100030002900c1220000030140d01014001d00c010154540208903601d40c0f41088a00c03400312201c0380d00040c2600003a551201c41d0460580240000c1c00024004002c5120822440c05400080a0080da560310400551402001da007004040c1d23410118038041c4100741d0291148894096000409211030845a0142c803d5000600000e003a01d0038548039115124010203d40c0000281e20420403803041500c00e99046910050140c10070390000c001192801c04100003400006004030f14284543c6070004103502c1c103001c0010080c26030744e12080c191742c50800180c111600c807140c6d401007096402c80164244c986541c840d00392070007220025100d040103180710800080f2070034001c00501400c00001803900140c110b4800b514850b4090012006e0f0302 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 165412769 1250 165411519 165411523
    0x305061b16080901090b0d15050409050d0807021501060e09100f06140c100b090a09050706121b080714090306011e0801020f0a120b010923090c0a020609 67
    0x704031184045028650007000100c902c001040303020307810f0510101859541d55812001d40251802d2800c503500c505d0b1050740c3c0d09031590000d003c0e1a040b5002c0080104d9038a0315956013540aa84905001d223102c08650858000c2000b4a4162541060131b00c00d582c403608018400200a02941d0040b100d18001c100e038104c2d00f060744410340b03184000c445500c514243c0304990003c10480007040c04074042110b0020f41c0300610601e081056076940100e140342d40a428001074800c000d09104000c2d103806c101c04005030010032174004844582c0307031000a451202c06001c00070a00341140e005005249810070b8045508101440c0c422521516098600290690b418400d4846c00c605694150000c1c00140f2511a020074100806643c3c0d1404410458807000900d007264840d81540044040104100c1d8000e0f134461a5410100d0581c1e030280082404840083c1c440002401007040801110300c1010001c40d003140c0c5c3c4a440a0b0041c00c90f0310314288105031a90b10317444505150010301910001811842d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 165414019 1250 165412769 165412777
    0x1217090a030f050306010e0d06050610051822020c07060f0c1e030e090a02040f0b0a0e011101020904060f0807060201140406021602040c050c1506060703050702190305061b 75
    0x16181c0c444400c20302c4a003281c00d41c0c0010081c0d03050100b2201404103079258032010115541c4107440005040c00c080c0c0800c003400c0c490036040e20070014200100b401b4038281c0b014000124400b550f004c030084080101d000c110110a007241c0d02c040d48045105480750800203118011602c81c2e44614402e80710380382080b2800d18101e08040c240c0c840c881c0424101301e2901c0c1b07214446034080d1404c0c420100e0720100098441500b61243c0720030340d0700824240703c5420143d40b02801441182c1409117007200220380a04010f180380d0710181804072454084e640d07008213404031501c012005004010300fa4940780c0c2202807580341c0c0242c90040c811f4280124261340148070701003044d140c4e0107403416a47e0f80d0b5030322007001e17610204c0c0c6022800b14500319580143c0f03460042e0340c008a40f41c1c540584540200c003115141a030009500001d02c1100c209200b081d880d640e040703442654240c58010380d616158008681c905100200ba0201c10240346800402e0040c08a81c49020707458072483c900036812078048141e41405 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 165415269 1250 165414019 165414023
    0x2112040f020a15230702030d091503060e0a0f0b040e010c0e0409030837060303170106080105131803020604031b02030c040e0f0618010f05010b0706050606071217090a 73
    0x9026500c800c400c05404c0b11501007544c601c90050302d06001036001c2401d240b9040014404a0020749090000c4010940d011003191400d15007007007610720300904109100d4011705100c031005d686104031100b2058507004000e0114010304180301c4180c00f151440d0082c26403450090008002020074003140c54070340142c008003070301651001000d80b03402a0340c3c00a620854580001e00d00300d0303190015070340000095001181e884d0000090a107181d405c002d050200142840f61203403820704018002c0d142c00076941410b4072815501800c214a544076044002c2c0b0200c001c0c1d6480440c8804120b007095800a80548102e10035070781d280d86003042c40e485070615040f402c0000d6054218910344200c1c1e003059400303144036400740700848040301031320f086460900d0002c3d2480c0f07500c80c00007100807581810901801901500e0300c84c04000a6240c141031980501070301400030400c644440c081200f555076281600e164940108014001411081c0e000c0d040e010b4001c0000490702d1180300040a00001042000c480b60f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 165416519 1250 165415269 165415277
    0xc0d0e0a0c152a2a1202011b210c0605040803040212060c1602010306170601030b01140303031609180605100504120f051905060406060f06022112040f020a15 69
    0x103850359021400802510704006082a0f001a140600a5090484d0051500300c0300e0344030030325440c000108035201682c011941504032208420004056496950158580041700b0940e003008010440301c0f840c0c1c2c92030240c42541420b080c00306116200c00114016482112048034140c00039980c0e0361140811a2891401075052090307030081d4000180d1002d0040c41403600007a5035841d41100048014070316448040c0e54041d000510401881034281800350070a07100d80041c0c6088030b400281c3d02c0c80000e05001c10f00c00200965081503004101c12009040040d910303924004250b5807010040c03030b40344941e521407a074149136071004a004600f01c90175620301801c91110030a141e160754100540c25602104d50f81f054400b8400091310014500540620130030240c00c0c1401c240c1084c6c402c0c0e601c0b81d0811289071101820410603560005007240e9050041010165003501c1034a0190704c60049882000500c0c540404220800ca80c079840811803c0c42100c200c24410345410800b4900d00060881401203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 165417769 1250 165416519 165416597
    0x10207080c0715140307030605060a030516051318063308040c030201050903120c0f24060111120706060801181106130305010e030309060c030c0d0e0a0c15 68
    0x49404d0000e5a00c0f90309801c001c242c95070b079840400c0c050b41c01459140c0000c0d940300107001ea021a44180200f2480141c40c1003800c02201800080d11054640f0802504408014000711041e440f034000d0001041040303080e1410304804014110421b128989121141c580e120307032092421302130b00b00319000e1a0440b1703c141d19541145d005480766407240181c25454414510304081e00d00805e0700900811040002030501040d40c3e92000b40307030900301c0f910101103060320008250500d4049c40100e502860901e07285000001307001a00381000356010900320725210001e03011080c0300ca0798010300110340c070101c000c00c624401030700c1c04481c85031440002000ba0b49400703441d1115103080f10142100003a050180600710f81d032599440e0031a80140c100031032980001c010000b540c0e0703081c007500c4d500168000c003181c0f651074420360805240c070030ac00504100a543d06248440d56000300803a1307001d550f012041c400c1c07907601d030004c0301206268802c108000600303040b00f40c2c0b0340d5684d851007507010014605103a020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 165419019 1250 165417769 165417797
    0x6090f010c21080106050a080606071505090c0f03061510110601140901060807020d050a170112060c0504030506040f032114131505041a0a0b03010606050c0606010e0f03010207080c0715 81
    0x21560200d0340955104490101c007a805338440c1c411380e8000d00a040051200241c41300a020901f81826000c5101c0c0d0000000c014500c3e000f29400702ca80f400417201c120000b0340b104016101e1790100707201d6401600c2050004144418020030715140100c2c06c80f0890016032f601c8a08840000d8120740b01d5005803c940c0030b1000d0140581c001c0c0c9212100303824800004c0e64101c000c1050330009038012641000d440f26031070140180c500c01c24082e50b900b45412443d1600f90707114070340c1e03508000e8070042480090319202c0c01410b01c01c08440000e981c8042020f18400701c0350b030034100035140d481200342c41c01c4010313800300700c0c2c440b494400e170704d0080e0f0310146420100320711906c1c0c0343c0144002441910b12209281c0020f103086065031410388a00070480700018851001c205060844200d074010f1001d0003801c03c4100c40303400c40007410551241c400d19002e6500c80488000c25a1000b130510700d113405600214000c0104076112003d0b10740010040f00705c1d1055503075001d40149154250694801040c00c1900f0f10392 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 165420269 1250 165419019 165419029
    0x309120c05151330030603060e0a120c060216030c0b06010f0906120609050408130f0303050301030f0501060b0f1e090612180a060b01170606090f010c21080106050a0806 74
    0x141419201240584071148182060030780d0139400b03810b00020317a1a0380601c1002000e00c01d840c1c0c000ba1f15001003a04200315a550b4075402d6858002c142441190084e4104100d495011a8264580918200702000007490003030203030f442d46007040300e4032002c11000074099441020701003048003440c2e54054030b45150480a9a04030003101c02c04501c5510b0f04030209025401e03008050041c0e01c1a5a21a9959800d02c0b07644100040e03904101c2c849034040b9420808680e01509503415039410041d11030003204146451030061000d54082c0e01d5049010a01d20007031001070020b0315180030300c00ca40c444010000700170111b451040d221203503030001046c0881c0c2290f42d080031680340e220b00c4000c1c0840c00f000442c85a50300d40f040481084030115240d018151003560712800404150141c00450800380c2130440014110740500c280c454082c0c40030303030b0748007640e030f032140c400c01000e0303500171102403813200040400d07001840480d0b44000209040c0c07000055154480d1044481c40d90301a680c18510351a0b60007046 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 165421519 1250 165420269 165420293
    0x60a0e0102070f06020a140c012a0506040b01050f010e180603070810050a060501050306031c0210090b1008030a022806021c110403020a05040b010309120c051513 71
    0x9411441035000205598849590480141c070031500248001811490403031460800303030103010300507042501d88041e01e907004030840d0061892144440e48140103540d02c01c484041c0340002500c82c0c800c54003800207100743d018015050760380036540b02e05520034000c0103403002c103103401e50240c2150010b0250400d0820076079010b900031800806035500690340702d00d454a402d007912031090070030780d681060000300c03a010700c00c0b00010102800c0c098154644440005e4a81c03444900100440355800b259201c0c19100b4043e2407540c07000c0d80000c002004480c00d1600381c00004482c298100102e01001140f4103400100303803070364014030354020100340c80000000700040004c1c500fa40021000f00c03031640001031a03400336110088190714121112103800100c0c00986400b5502c010074400104818000750f11403104880507103000351400f140040f440e03c0124010004c03214050301c00104a40558a020b5004603986200350040c0b08541c0741ca0105c000b03e054036803082d200702c015100102c0d504800518040407034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 165422769 1250 165421519 165421547
    0x3040b04020d05030301080105061e031507090b0403050307141203010b131517180a110d171207090b030103030e031006062304030305040e0a112109010506060a 70
    0x10701d0200b002c0c3ea9607075207550001c2e0440305041c1d44038010840300b400c1038075609122114400783d50240410301c0000c03c0e2103c0c03295039005003500c00c0000058107a800740350041c00a00311020503a507640c0c5c0d24208503860760001101101c04004082002000000c005a25200c3d0308412000a1450740380000d000742642c0486840d4007261007441c00007a140d0012210740742c1224171a2126038412072507050602c0d9910000b440ea41c0100801c202000307400754000b600340c0c00d441d4400414660390f12a000010030321181c180c401000c4540c8021000700707000182024001304a014010100c183e1070320441a5440707180c1d0302601000c0e101c2400100046481845200801000507060358041d48040c00040c0c00e46005810220110311040c6040c413032403149281c003503007a072640c20b04c20b418281140d80003083d5100f0384c40f806030382c0c1181001044000520350720001d844c190550149640f6002d0700040100da01400700c45282101c28000010707030002040c0152446800c00902d81451300340300d030f00140d41c010400c0201c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 165424019 1250 165422769 165422779
    0x8010506070c090218040f0509030f0702010c020a0b0c1002040b0906030606070209041124040501180801050a0b0f010e09010b030a0b0a170610030b04150e062502030a020303040b0402 80
    0x2944094a20003018045c144000c0c030321441c66407400b44819039406c1031785e6503200f40c80d00d802c020b4803000c04015520160156800d0070351310802070004860203c120710029610002c00310b400145960000010300c045500a015500455a049001801c03402280300700082c52000300b02c0d110040c50300704000c0d60f211000811640c24284550041441810101c0d4202c894800807032700c0400d0f07450f116852101c05203084a42d1b00d04044a02d400710028040c511429041c03124505131910034090405865025107240b0307000304101d151441c1d901001d84000154a4000c15080d284503045500c0b80f901d1811040015001c0000c9034030303000036400c1542c4010401c4660325560216294907944103200f0707000a10303440314a002d8021210040381e0402c040a041c40841407054030003007000800d4450303007a03481038001130250075200000891001400c2d684102130080e024110400caa080c1030081118414801480e00c00c001e007031040000d99482c8110440075015a10500002d00000e00014109074400e1000d89 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 165425269 1250 165424019 165424043
    0x80705090c0c0d0903020a0b1c0902010c0506070c0303150605030712060803040f090b010302070f0b070e28060906021002030603010e01021c230a0203150307141509010801050607 78
    0x580b003030030220750742e2003500007500a100c108107610703004a040b406044000c011902c1c0141032914280c0815000500b521207030785614154056a01403204e071011300c0d80140035540180b50040b00108443d402d0001100072030301c3d01c1405500c0d03200840d40c4400340e901980321180383d900c0e20308040e500c0343d0706081c03d506026124980480e080780b041c00603000501048001050450030141900c0c25503500001c01410148140300b140007140101417684441e80d00300c030751a0940c5d15001b204440b110161061990441c1c000010900c203414500301c1d00d409051994036000c43d0355120801183c0c10360040c8074510050f4007070780f40440c0002c00c41d8010358010f10300a00004107051008005400ea03049805c1e20103026451800c8640b4410141c000c14200c60b0050908500c0d0070306601c0e4005030500f0113000d822000d540400080d0401d40c1500004001c00d00040446800c2d13940c035140c110904480c0326449006801e6011211070002c190400d894000074140c40d69025a82031809105c890f03007121006552414441c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 165426519 1250 165425269 165425287
    0x31b0714100c08180d05030a0f02030c0309060711060a240605090321040e040f060e07080d02010603170c07090203130210080702060622060801020c0105070801080705090c 75
    0x210240c0c600d422060085010301c2d048001411080005000945814422444441104021607422100882410101e13125195041c000380186909882214154400424000e481d01941e014510070150003007113031007650b2525422610702044030b100e14800c0c1d01440208030502d883d6000b0766000402c1e074450f01c450074076a61100001c059941e00c90b00118800094940b038a0074140a6483c4144103144c659805004c5186401600e214510400180c464004c0125003044410000350f1000e40d0030410501ca8000c51180391a1a40124441c0002d85e1180700e01c140611401802a0001c480d044400444139071700043c489a010390007c010040c043c02500c001007400e02942c409903000e0141110b400c82941c500d40b06000c500c04003c00504103019400341004030b620350016409a100d00c095482c840749525014500e5082001000301c210558100a07010582003415805040c81440b983d000340980c1d100c003581940d07424020f000d40b460603084000184040c1c14400e00080d080b981c0801d8040c0362004074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 165427769 1250 165426519 165426523
    0xa08090f06090a05091305011103090f07030c0e0a06170106050a060c110d05031309090210081504110f07050a150b0901030813170f1b010e040b03010b030a030c060f02031b0714 77
    0x80480c590b8000042b050200e9290700b088054404400a4002d00541d4103549030841c40d03400c2ea2094143c011482c03800202000c4080e003110000301041202100c54640100328076010381064083d09020305680e0340300180042c072401d440001e407504400311307440b900a8002404031804100c1c00540f55807004111088140e004103000c4401440600380015065006104009001500348007110400c1110000e0102d80c02d10041640d00c1c841d4222400600f2507407010804403140900f01e130030040240701060b801d081c044041104008548542c40d0842d15860a0310458200d88000400035080806e12005100162419004141c0c84c4034013199a542c3ca550340804440a104100801000d82c0100380d4250000c0390401020002340c40d80840c1540849903100000e262060300030145210381c2c2c5500311159907440030b600171802d4140107406d8071000401070070041c4c0b02840310401202d0442c94504042c11198951098a00843e03600211280300c42e00c9002c2c9294035040241300760b6000000b0001d84200801c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 165429019 1250 165427769 165427781
    0xf120501091b1406091008070908010203150102010b12030405060a0c051b010e0405010e070c0804180507090905040b0c0c031207031505031204260a08090f06090a0509130501 76
    0x10385220010b41c40c02d102c2c029038510514030401e8014a03051062401d00c0d920f02001100403105441e0691941d41ea42904491420303440d48480d4617548000b0a0090040c84111144000c46d42a0000c1c0300d0380c00c4400034000d0a10080e803074002260803d01c0300340300d0b6140c40401030080c070099141020901149840d00ca0600d025400c40300c03403040d1110345602d13076560000c01d03842d100442114104160b6140940500d8201e800408070800c00c41c4403204807040051401c00d640c05041c0081e80c41404074a10091a40100340c1a50030300003060b901d101c0012130058a0040f144205d43c410403880ba2030315102030710b42041d00511920107140c042400f603421301c001c044000c0783c0b1543c3c00c1e0740d01003004015042c035440002c140b0f0708224044c5e04028040212290090304540454801109003090300000c00010310480f1054200c20b0000c1c010824000c1c203000b65400030b000c520104a0344a418102c0e2181003000c0c07131044500c4c4a402c4028000100a50302c0c145488c42c4d800b11a4058548080b5025529603013141c039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 165430269 1250 165429019 165429053
    0x1606060f1805040b040305030714130f170d0f110a1b140a0509060d02030a030c1a16031a03070f0305061005060f07050a0206030405030304031103040f12050109 70
    0x480e4001040104260340d0980d8140c030410a0410040c2010786840440c100018000f034203000340000842e940c0361283c443d08001078407202d002c0391210341c051803d0b4981142c80c80b881c06c12569050011030081c2c520005082d8408050000301005000414169040c00d00416603c060010007520500450000d221000000380b1030710880c1030000e5540e0001110000a0300139015010321349180d000541c4032403000100382c0e071017115003001c0e60707890f500061807505d00008020340501401400307504154001c0900d500a40c07040100c80c004640354800243d11702000c03105040810050b240040c1158000d0780032103001e031008100c1018080100d8003007071070440141c0c41880c4c62904001c040090010034043e0315006250360071145115807410001804070300900307550360344020300024031004100701040403100c226400f5002503140e04e070a080c002d4880d001102c003030340498407004000880d110040119016904044948aa800c0c0ee01031403520150220108503401d43d03841c007211012812447c0e880301109 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 165431519 1250 165430269 165430289
    0xc0706180b0708031b130603050406020c0a050607030f0506011e180f06140307090605031005040f0209030f060403020717100612140c09060628031508060103050303040602160606 78
    0x1040c007190030060b001e0030070446050b20700c3c02c4c0080300345480c0f00c0c071b41081101e46910f00811662220309062009116045505440f44520300b110700030807201284081c070074001ca4804200907030101102009444085072a03d00041d07001154400016490140f4211503d9a2030100e09000050b82c01060f6081c45e42c104281c0041c000c1403c10016500004070b810710390b400742100e801c2d07041000002c1c0c03842d40c1d80d0244000b03101000c0000b6641c00c804807030304802044001c02c1400288a06030780c03a4003d40c052041d00d4064091b10010901d10300001400074006c50f071541c01400c0c964170305461100498bc0d940041142c81c0503018010b80000000d0182401400d001c0d1503002071b901a40c40c0000f80c0d004002018580da42050130541d007140d45030312140c3d6024806803a09540c03403140100e181c0034a1408203d08156611f03403942c0440300b99150740001001803880800300707140c0781c81d20302e01030340e40100344030042c110f902c2000000d0000300e640c3c01910700c498651440115002c80c40d55020142d0b00181c000868007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 165432769 1250 165431519 165431521
    0x4020c010e06041b0b040e010b0c0a08040e100b0304030e010f030b0d11010305010e010e0403030c09030203030d0f050603121b0c03030301060206090d0c080a0309021309060501030501050c0c0706180b070803 90
    0x1302c03d60b0201c59000741007a404451030310749003280b1a2045141407090a050400c003003240078240b41d007440340c402c100c1e901c003912075540c030345540e02200b01490503146034801c505e6691011a00a00c035200326030280b90103842d01c843d4038492400460380c03141c01c585250308140d281c200088081e1248030903510110b2180100010040420300010116841680801c04210303501004020408411008a070041d0301841d001c601c1240030201628114000c0e071000350544800207411105916650103107011140c208410310040d00c4402c20140d803158a40042a40c41e4010048081c00700c0b451845d4480a4100301d00740e840c140011070019096030400d92044c005a0400c104200c0c24070401e0080903a03030852410402c92180031502c0300c00960258070300364000e050755251200c0c159914008800c0441800101c244400390300c2c0c0c039060014040a2004807030f158200030214070003500c0391003a10900c4d060040140000c61511408550341c403d010030300d0303022060f5a030700404d010b550380c2d0051140c240030b94041556 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 165434019 1250 165432769 165432803
    0x304021513091b0f140c12030f0907051009090e0703020d1a0901150b1804060801021b030711060d0605040c110d0f0237030f0801060e03060604020c010e0604 69
    0x8036503c90400c0d0200403840c404c0e182540c0e0080c070011000061004255110180c0700031940c984484100ca15a42d00701c0801000025600c180c0301522540c405010b0300c1c5003540d65010703c051034428600e0000490598241848803a0b040d85c00380d000100c01008941401d540e94000c40e240c0401610152004110020a11984100948a00e0b0803140c4140204003401e94007500c902003c00714080d800c00c541d00000c0900344440302c0e9900d4180980020000c2102d15601c882990003035002c40d00c0344113500c0624500b4035a060012041d07403c0300d40c0005980c030803e42c4400410040d070340064030800680e51394800100d00e549891040080c09400c41c0c4451408051503030340c4900d404909078400e400c018617600b0051030300360301064441070b8400e0340e00301380450420380e4072804480c01480000050211101c0303811051551041c2c10a603000e4044d01d81005a98807024201c806031741600c81c054040d40103d000c41c00e0740c142036008203041c486003000000ca0a4860304c5080c10b080041ea800c0c0d030881445880084 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 165435269 1250 165434019 165434051
    0xb150d06050703020702280501050a02030c06010e01080d0809060a180506040f060e1c030e0109080c01060303030605060a050717121501020105130b010e04082802010c1103030402151309 81
    0x7c201000c41100c0d8004604140d058020161a40038450400c440400d0a07600703240200300b502c01602c407003015610070b036859071001c020b102c000340318010861003880d481001b20b9000b081c1e400d00403001480175010541d240b000400180a001030203900110340c2e4485000494018000140624801d00d40709480b4059410001d0a50743c01ca91250f4240c2c00c0344e00c402d00260741050126446001c0c2d1306003c10700001c05840a03005000d499009800c0070000114501e262006501180607648a61000c100300e135210340a0002d64041c2d0030221012070010072148002c81c00120348002f900001c0c00b0024500b0104180e00e800103c0f00ba1a40d07000c1d03500c00310560752203603028090a94480d0f210b0380c00844107100760b00d40c0c040c495018841c0d5000e44c200712001c5420302c80d01c2000c403901d40800514001c800300c126240102c56000c007421600c0194600000f1204280c40341c6040100d00c0300703020046045485a808010401c03d92000100c0d11903020030001074020b50440d5000024210310310001050011010601 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 165436519 1250 165435269 165435289
    0x4080706090504060501170c0435010605030703030c0819050c0601091503110604050904080414010e06030a0506040906110403051002190503130507090501060210090b150d06050703020702 82
    0x54443d500b003620a00080c4d03440290311824069564501c181c0703850707a1910103131034413542c3c11411040380c406640c441034030100a820f0000e01e26030820185146582542142201e0080c020759525070040d403401c0001c248200d1100d03292501904940c0d2030b240c0c03940f1240703912600d01c55552002c02c0001c02e8444600e41b0500004c1d004103070b4150140480d01150104d00c2a000b103902004140b105603108440ca81c0d207445c1e0583d805424054062615401c00b403c0c0b112281e01315229030344201030500d41040195105411166842201600701c906585a0149600183c40010049500240e44542c854085000d80c098800c1034103890f202c0c1550b0700d0440c01d1072414005000c0304d0703000d0540100004088034550740e005800740a140c3c03504030b840f600c43e05c2040801c82c1107080090154400c01001146050655000c54101e40840d000c403104000c4040316903040e034a540c0350180c1075a8402c0d0000380c1e07152032000802008500280321105605165407404201d580a070750360400641d010a1560850070204005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 165437769 1250 165436519 165436529
    0xc05010f0603230708030901140c030a0e0907090b03070e0f1008010f0b03060d02060702031603060203060a080606030a0b060d08180a050d0b19020408031215040e300408070609 77
    0x24240c4c041c01d03c0c880f03030758920600d076071181040721242e03855070034a03100000e4852108003102a039a540b010228020110049188002d01c00c5c009900415281c5015840c40001c4940b04a100c90460b44c40e050f040e5030a01b0318000840d007107411681e4500f01d90382c0b451071a104a030602d864201c034550500102e07074198030658000c40b00c541c400b0418044240d1301c03103588244a43e81200d5042d0b07500c403544042410085825081406030b102c402c808810031800d900039510400c400c0c0c03095030951340e998110903501d5030700343e80030342d015040003000c180800c001c0d1012a0748684090421114420560746030004c9a020f00741c039168100024a400e1b501303140100c902d038002c22084441400c0c104860700d0790340b03040c480a001c110b0101c0f491280000840081e805690061405100fa651190541050f42c10144400c640c00405080100882c50f114039080c461400c0c6200b00307400524030700251a003031402d521044503814a10004a52a489650345003a0040c4003034103942c005801842d03d00200901301303d0f11500a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 165439019 1250 165437769 165437773
    0x50f012a081801060e01150201050a0221060105161a07020309030706030f110409090303050f011a0c120406110f011e0c0903021002030417010204060f0c05010f060323 73
    0x4401441644a00785540006454074481204072008074181d004000a9100b005024500000040d05100716100b880740700079540c0003404140e40310b00300c0c1000c034800c4420326400c1c2ea040ca0945800074620040e01d561011042c10041d141c43c0300d081d1a8070782c079005881d00300d413916014500c906050600207101e80d0069000d000550500408400003900c6070400c0c001e9078201940d940c3d42e801c20900c1504410841c41e015499075a036a03485140000103480b0003941a00803034101808039820f210705d5005e40c1e0496440e95580866945126040701107540107001ca891780f48110050751204010510052004001a8070f034411021203c1c1c4032241400310700f020383c41342c44c0d00d081c2038044480e1415002102201c41081c0000c1d20440060065074158402e40001c0d41080c410380d60045581e40010080042e0f6442c00101480c00e54284119802c0c2d10883c0202400076500310b0321040440c1c0150051b1034020f11800000c01c2807840d044040c0c1c05c07207086601c182d030829000400180d5406005003080720310061880 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 165440269 1250 165439019 165439091
    0x1060f1802040501050a05161707030813030f2f01020a08010e0405030301090b0117090601170106050d020f060d0e0c0f01020c0901060e060408010e03090103240b16050f01 75
    0xc00038209000301411780087c8400091381c00c210780001565200816401299640107406640141800350030807102200411b0f050341c0824800345102e00c1c00f01d203040c0e26992303a079041d5032011021144801508060070044400920211100356034100c01c101000b82d07030000684400c44104003c003c3e15040c1d0200c2c100710300590510011410101c2283c0c191401000c02141c400560030048801c051b00c1001400d41701144010300010305c4010072030038101d410360070006421760828a00c107400c81d269449165489082940824010f0600180c181d10000004000c1d5003402034040c980c02c00d5462075072420300a40c0050310341030340074540801030311068102840140014522040441e05540f410f005910a02202c011800015910b000031200903000c440c000344043e0066603680c40d0780e500180c01217400b003414004100070071126992600000e5410743c040e415458900994000c031944140325983c0c01007903040b07498011400801580000c901c46100001d0a10a0a0025000c100402d000041440c2d0500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 165441519 1250 165440269 165440279
    0xc0312070c05091003080a020109030201050106091d070908030a0c020a0f080a030c020f03010905010b090a02070c06050705190803070908010b0102030f03090708010c0f09080105010e161101060f180204 88
    0x2801c50426103905981e60500c0d901d5441142040300b00c0303640010a040c600081e0035402e0365040d0004810307070f03209400900c103036601c0d0b40c4240c1d500603942c051026041c1081c0b18101000d000441616005402810714100c442d88650320b85040d81d000c2d41d20741c40810b0080e4851421820a00045402094010f9002da4403c0c20b1441098464a41900140420510070b0090b0706642d0389042a22100000a00800145d915450294081c04d0402d503da0300c038401080c002045200503008486400d6071000c003583c000d074240704083da45500700020648545c80ba81c03028102e92400403e40c00440c5001e0022180c581c41c2601000b001030301aa000307001c0c3d90f41000c040c083c05da6000000d6540f40310400b00c002c3c1e241e9482c9074403540740000760781c459240b942c03d14441448a64110186400e03002d04d69864850903a181c2c00340c2c82c2640c07000e100c4c141208002c240001e490101e194036000c20001c5520342400c132940c2c141d8600342910119000b04000b080b0300101000800f8104074680d2245c0324402055003014589 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 165442769 1250 165441519 165441533
    0x1303020f0309060403030e0114030a1d06060901060c0f0507030602040816270e03040e06030f060108120d0906050109060f1d0403050306060403051219081005040c110105090c031207 79
    0xd17120045c24400380c0d5260244d542c0c09541f091220144a10425403245402c1c2e601d40050b04000c01e41d120211484102d00814807000b0034007900c03640d40940903000a91070304800311483c041b980300075103140c6500580b0400184003844054000c5004003000340c1c42c1da01740002d2a041400c1c0d5a00c00c074038511200b1042050b084c40c0c0c0e03003d4070200020311780b155071041d50808410190280c81e5458129000002e0003145031700485d00c80600400003603085a4510f4084c880482d0ba6140a000314000c9500081c0c207041c1500c2424000c2603001c07441c56010030f0345501a40d401050325800c1e00320102990326110144025a107446001008240500045c11000200780c403040d000d0102030409010440004009545034a690301100d00071036021044882002c10210a1801c542044968018003d031003004d49291611600c0000e0243c1102041c000d1150300d448100001070058043d030005002ca0b008400085040a10031240704000903c06000482d407e40c04040c20510700c0012000700c50070030b01c0500302140e06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 165444019 1250 165442769 165442777
    0x4031b020a091d070902030405011103040804091109060a0c1e110607030207030c0801090605060d03080610030f110706230a1104050d1412031501050d11031303020f030906 75
    0x40d8100008285104205503514001d60b43c8410900740b142160001e04214150300035032066015000030400a0114001c5103014481983c001d02601e900b0b100500040895a000d84410f110201090749044180000b05e9040d8110351100808104281d000d481480210150b00d078642940740036200051144cc0d4030918021012501a401504040340e54001c15008122020140d41c0027841001580d03074134203419010b8461584101e881d5401e14010404609102512413009941926004c00c16503036101404510060b02c05188209a11652061300c4500b440c803a6440310f41c20300d030b09030703541d480141800010fa40d0304801c403a00101c4112402c055000f801e0302c0c80b5030410071144001c5100e20800ca5015614021600070716070003441001000d0410894494500032100e0400c10f84100d444520a00040303404211940e868501520105c0651036218030000c181010743c45030001002c05d0300c0da4084040d500b00b25103400b000b04203c034540060507010030411140704503000040d03240442c240d02048031806 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 165445269 1250 165444019 165444029
    0x90c030b01050a020703140a06090510110a090501081e070e15190f020102040308030c03041406010b04140a030c0308091903150f0209190f0801061d09120a0804031b020a 74
    0x5447d40d00c000d0b50400500800c1e007015040181801224210700341030351244101c40107203850074034041c81d149101203010250780c5003107041d44500170100c0c40d0400640700403000a01e60720400c0003086003440c44a040a582902801d040d80c0d0b809030000d1640240017034280c8401c440140c09005010045104008554100380300750980740211070f80c04110400d901a01840c3c00091001002004100c10078a108010f14450381c0500d11542854841c0200581c40c0c603002e00400014420410091044201500880700769000203000b4482d120341d80e032544c0100a519404c200d0b0104000580d0208500c1e02a080703544880c404000440e400b03185580319698141040c0d55511220703114400c40c0c041d480103905035001c071388029040c000811a5111400310600b042e0040102081e01101c02050310b25052103134106850344c40f12204800b810701c4100400d09000140031030494480e00c5140da50031102e06018000d003030340d940c4800354181840e00c0c02900c0b000d0307a070902c20381c81d0541090f0f08001da925080c0540c1111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 165446519 1250 165445269 165445283
    0x1104061d0c07030507120e1503250c1a010504050f0c0712030b0d0311010c0306080c0f03010b06070b04022b0201080604110a080108150601051b010f06090c030b01050a020703 76
    0x15481e0a9804c5e000b603210180540524101803400d99400010041481204503400d4200d1000230081615500040c1c0d01685010510301d03207a500045200d000240c410482d00708580341514540e204202808034440029500c90207200400840c2028011141c0082c82441c2c40c040901c0e14004004460051321805020707040d10250b44840349010740d102c1d2140d200e0242c4a42c003410381c2c074240900f028480150300203240d860122281421440f1f0300c03c4100b50f031000c0c0f0252040503041c80402182620000300141e0555903199400e88907130b514001841d42c40d10655001400b881c242c01080f44904045c91144200c1210244041e46014031014154800741d09003400c2c0010349a07440032600034003504803c900c03c030380002101f003007194102c03102034100c0b11038004440c9a100980c6c01024051026100d01e4045503082c03003038122100456940c08180d0741780350b0000614004031281d2006840580c0c2c804584240d43d17036844a9219810701505400070300c28200301e407400200b2a00295145441d10001e80b9070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 165447769 1250 165446519 165446527
    0x3030411040605060d0e0d030b031203040204020d02130609060507120c050a021002150a060302090601050705010e2a10050904022a0f070e060d031b0f1104061d0c 71
    0x60380e40c82c0d00079406010080c203c180c561110b01740120043c00c2c4591146c03081d2003462409501c1c14401c2c05510004580a00035100c0b1803403000c524609904050700480c0d20070340038001450307090000c1c800390000e200701c10700000d01c1d145010300141000c507040d005200ac02904000315008110f0704084540e06c0d000c50311701607024820714101035080600400703000f94800300a80d0184201c80c0d0000d00301b80103008285207422a41c840e84050400c503002440000e4102c201c51001074011b41c083c82c05000c03901c0c0aa0300101d081c03241da00c43d040c10000508050300f003c52012120f45d00ca6859140c814018110681d66031415017031940d400350240c041c07014401e106540000c1e42c1c401c80c461510040e852800e40ca0340d040d901c4040c0501c91754488140000c18100c61180410000f004c41189e80c41600500e070141044446000c0e0b40c03401c331818502006440030068000e44814005038951800e62601d0b0b0043c00100c1c0300c00c03040c02c1088140c0b03a140c1d000140c101200ca442c0740c04031442400b0240c20200c1005010742d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 165449019 1250 165447769 165447803
    0x50f0c12010203071403070323010603060f0e01050409050f06040c0e0702010c0e0f0a030f0602040e070c15020313050d0f0801050312040b160b0c0405041103151905330a02030304 78
    0x1c9d102c00d01c45524156040202c403d10b44c007441c081103059950b81d44080c02020348803000f208500001c4e00c503813501100740400402140c00c01e47c1c001c4c410907000d43d060b03402540c0c80001c01841d04c8000c3d10120340742100504104444140308003035603080380341c034402800a550307a804d0090102e01711800d01403103040f0f0400d00c00c0607a030710310108100841d03000200301442010b038101000250000d1060000051020002440045c49003003c1914568009008032000142e00494030082d040200b000001c00e9a0318111000b0070381c10051506030115942d280785c03518508100c0100541d5041e84918000d912991a0305010104441904c00703035038400e600320391a00e50b040188441d03040d1140d4003400c08424441440001d028450040041c3d80c2c06071020b10100c41c64001c42c07403445c8021a01e420464407060505480c1f45040070365508443c014015100313107940c5a01c0011000c0c0f80c910010104800c1e01560180a11011110041c801c3e040c0d81c14a810b20482d0321000e9102c0c0300c0280300a001040240d0768910b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 165450269 1250 165449019 165449021
    0x60105190504031e080f03040204020f0301140a17070b0c031312050f030304030507020f0103110a09050306060a0305030f130b1201091802030d0309050109050f0c120102030714030703 80
    0x40c02010103600340800310440c00340a88664424042500d5001c00204843d2413900010480007200e54442491442c040604860b901a50000744c81280c1c02074007000000b0441a051003d94040c241e05000f9104100c9171108115200070315512054403074900c40d07090312504c800428508100c3c0c1c5545049695100880015400c1d0310a82c580c0c035481740210540810091410603a0304610391040080b581c040c924402406d5036400304039801400240104030070340c01810481c600f031642d1801030402043d020140044694150804407115000404200741002a80b8003003104d9900000b0a640d12481c1d2825a02e0f110380307a200e03103501d041145200280c1c50003c40c0340c04015400034100401c01945500b21101c2c80c2035200400c0c444d0308003172400c000e05146d051400014521102d030303004000700381c83c2c024024154003400301c8400948141d50ba490303483c8013152040c4990200400c001000d00750b00c0e0010700c1081030910b0b1204a0f40701507803044c010050f13a03c1e000300e00445a04001800d482d02da41e00e10704210 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 165451519 1250 165450269 165450277
    0x60309030e0405090601260705121501090b100c02090609040201170f070e010e21030403060608030c010509061302150c031306030e0109020303070204150302031207150905060f060105 80
    0x41d411503d4841001030b884000301c0d600e8165510340c141d056a03084208255a0303407a4081600780d6042e0400c02041040e458201205407809c4030810aa40001e010803000c410f82040981c4001200d503202d41d035480b40362514010744000c000d120f040c41d100030701e05600402d0b4020001000d160050f804031000c40c0039607000f14480c2c3d109617000e0340d07800301900c0c08103002c010b1403505070386801c04540c14201c014030f5036004960190000720301409030910896120000300002440074400b00407800b04100110101d031142c01054081c103404e41c000c5036208501c410705400c6900040a07440e2a8100e40301b40b2050550380c030b0030b00300c010340c044554810a4061a04100546c402c4284180304c520000816040841c00e022542c0122041a14100400d41480006909072610140020740c141c0080082500519042c0d0080041010445a0784111074580d80030030314001032940111011400450b035a420010100c1d5407811001c50404103000919081c6c0d5007654480001d0543c5030704c02e04040004102d648100c05407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 165452769 1250 165451519 165451547
    0x5040608060d0f051c08010f05060702041d0a0302030c0601050102010c09121505040303091407080d031e0213210809012d090302241e0409050106031e0903050406030903 74
    0x182c1c4500e080c08070f100400c00d04152017100801d00310400020342031005803240c2c0803124050314203464442c0a600300402041441100300c440407850340b0380c0b070000301e04004420655200e070f0000c5030780d02c8010700713040d1400005900107811a814807200c129041cce448152074044500000150072600440d01e0407848112905003150b0304d00303152600b01f10034140e164002010241c0201505000c540710b00807100c0c0c4a40c2203028210007030340f040a80444071440380d4041c000384251080c0d0810a8808294080d060380c0c411683c11240481c0c0000c18881e250760040c031034010707070b0f020744a44250441c1503580c8410b6001c0d080485060014088001100f039503480c005690520005103050440000d4002c090041009070100303902428a0503000c2c5100c4016a20038006440740702c1140341400e10321031151aa082e8101305440c070100c0c003884005940040c80c02458048c0541c2c0d00c0104a401d00d010f013111030396103003404010503e410100c1440101742c20004440a40f00286400300b4503100c81d060580d4000d4000c400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 165454019 1250 165452769 165452773
    0x5100513090c26150f0a0503060702010e0708060103020d02091e01150210020306090406090302070b07030210321003020904060506030c030d02070e071e0e1005040608060d0f05 77
    0x2c28982294001d26840c1c1c070111071001103100e15000c8600e403401c0c00040f40c10488290900011071624906035025244204000b001076031901c2c0c172440400e040142c29031b0141d000d130f9107400e040c04c5141001e001c00c0c40034011001c0241203662442c0c0028000c40070841c4007138041c0e001540441c5a0f0141e9264000c41d02100000e00f400791350b501d0041d907040c040040842c10060040c80b654214020b0303d402101c0c0110401404030000f51101e80b600c4004102c105011815881501c800069a4401e800030b030015500980252117002480c02096080d11804040821165207415142c4c00c2c0c00348202c0c44100b084020341503103041c1c2e0303124040f0104e22480d0fa00003039400301c1c8190811003004a0b0390052480b518082e0162050b0142400c281a0390b4860040c2c2d076005600b002c2c0081c056030010200b0140e20601601d04044403810314007802e4520b00d040e940420018041c81c102200d1400e00213400640b4042034941285041c2c03030f0444c01400c0ba000504803900ca02d03819400b101c2800021701c20b5403105074100003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 165455269 1250 165454019 165454031
    0x60904060209040e15101a0a170a020406021209061b010b0301060b0702030c190317120f04020a0f1a030a060b160b0108030f0708310501090f0510051309 67
    0x4c2d00d40c0d0320703041c1c08604120f030a000e80003c0d225206080c5088201c0302c0340c911403181e811090124039001c0d001411140700308144c21258400c1c6040d010f40d4140a0b9040010050b500c07428010b00a040c4540c00c1c2d5003e0707000c64108840d8086888181c215207003119400b08184500080c1100729001d421116043e43c0d041d82001e00214240d01c0304001440b100c0e20880480c0e503c3e549031802d101540000c1c1021195802d002c0314100f001c00d1545622810902120115518101c1e00d29003190264009a03414007200c000f1070204021400d08081c400084c1442e01c40084180b8985a0300c0542c1d2500b801c0303010110390b004400b26404150b0b80d00102c014007103950a480c1c64982c110104a24480d8080041da2040c2c050300c00000c0c4c102c00807044600280071000b40c00d1800c9039546a400340781e40a68010420310021102a09100c84986c1c1c01e80e2507084a0381031504003615000006005001c1070b0018650411506c800b00902d6589000344a6072100c0ba040c415210150069050701c4155140d00090100d4100a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 165456519 1250 165455269 165455291
    0x60506040f080c03071202120309060d0212060315160c0212030307080a020a0c2307030b1902030f0609131203020301030c14030601030b130f0b070801080a030806090406020904 77
    0x1040d007106403140c540c22900d000100e01c0800d0396521840c4030b16180314611034014009801c00240c1105010a2002220b25000308074010448562000703002600c00c03640861400c980e40790082040703030070030000c900078000c00002210a1003209406024550548030041c50381419500809031400c1854000b05004824500300c803407141c0300e83c403c035024400510280005100c2113424400d40d500102c80e9660b021103241c2c0b65484102520b20702200c5000340c40d5414200e00343c18001c1001d80081c0d0300c21007211480303062488054a80020858403440304e540107000b0801c500b281440d0f0700340c0c480c400719480607150301d030b01c0d40707441d0060800344002d4850009a41c03109070003500354004504aa00c101c190724079090781c640b4071043c1c0c04010034209603da00800300400106020103009a04444445165113014556554100d9480c1e8010011207001c1d4184003005100303074110100c42c1c01402c0340000b030b0203c8451550b00070250000100000d105444000114090080070742c190786541101401c00c2021030810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 165457769 1250 165456519 165456539
    0xd0906050a0f05060d03020d0f050903010219030b01030e0a30080f1819080c03040f1e05060d18020d141011071401020d02040e040b0a0b1f0306050604 66
    0x211440060b110b0514010580758104402d004880b170f50140d01901c0902082c58040760f0b98100c0d91624800c00c081800351291507a420b02c0285401810003401a241c441c20000243c2600c0306007017001c4c1410314001c1c16082d00280841c80303100c220fa00c0340303e4200c880c1c4440d4182c074080201011764420006a071140b907a4542e0002d4545010700303000c0980c0160b41d5201d5035510300281402e065010160000d50309a25294416030345500481d100c4d081d92070500d0f5204900c0e40c07454210741e010800281c16282d040001981e403d403543c401c0107901448803841420980031985520603c4110300140f540c81140321008945103454850030740c0d009100001100c01070400000f41d24100e418400b0304c0c01001242c3c202c9444600c11000101c0c4d007840c03040e050130041d840e03041c204a20415446a5550201307e025981907003031000340050001104264650f0600f400c014044c1c240040440198900e058810b00543c1d4642c01880709442c04e40e21604411aa1250210003421155100680024005c01c0205107801d207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 165459019 1250 165457769 165457781
    0x30516061103070e09040f02091005040c0306180204060804021c06060b03011d1005010c03090e07050c0d020307050318040b040606050901030b01030b091303090b03010803130503210d0906050a 84
    0x401d80c1c400300181049800c000f245d50051390300034103500c8004c1c107003001402c0007051240c0c80107145d035071b21000310307980c0021905032402c0b1044200000e50380e501c00d0001d2041100c00c0c103900030400c2021420103041c0340020f0700c90440604040d118a071703080f00154030130b45203517601001264451001c0c0603107580e520740b030300c0c0c2500203005888034640c40144180e00b00c0079014440e403181800d42c2040c4103240c079100041d503c98020134000c2d0100400b080001c40e1400d522611940611000c0da551540c81c01c00782e00481c20100e24071114011900f080146201192001050f500840c6c80180740039200901e50700000d00610125051540203070501000085403504034010b07090007031082e01c2c01d006030702605004404468103800c00507405003081d40400c0d40701030418140d000552080c10060341c0580c07140c414000e40d030801d03401802070f90301c00158850742c021908844d07001003d0680c01480706084480e107500c4004c0b203042d51100710201c040748000e003520854018070000340d0071000070010350a0280b00e01010f803070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 165460269 1250 165459019 165459031
    0x1201060f03051303053915010e0a0c111506040608030a080103110604030c0e0712050c07120e1509120a0302030a050310030b07021005090106060c030516061103 70
    0x1000d458200340c814064040c49110b400041840c42600c40c0d030f55425074240d001401c070000203800d03450f40f01d4480710845544126044200c40c11040c03c0b40140040c618180e2100202444c1040300300040201210203940c50350000c200d0140400c01d11035031402141c070101d0421030170070f95200c1c2d661000c2009024170700030341c05208180c6d4284003082d02d60078581e50b2445401d0554001805e644010404112405026062208004c01c40c0e403800e5075030b031606424044545c009124403183c040c14060340c036800ca108180945400d80087c000752070030034401b101c24045c4c46c0011b000e000070010070700c0c090741c410000c000d8a2a001003c5c10407406580300c2440058120a4109006828004d0260b0a00c107000070161240e13981b5600440c0340c51341c1c0300300481d85500090109016404070102c0840028607990403680704d40310560040c440e5540d05100c0c20103540001c0c0c400c03200b507450a0f40501c5040c3d8082504e0b030040380c0604185035100000840c03404c10a40d1000d000d410580340148400446400717400850140d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 165461519 1250 165460269 165460277
    0x2120a0807140c100f02040305011e0c021b060702010207030b18070503070503031b100c0f031d030405190e0903070201020708010203010e0f0705091305010503011103042a030602120106 81
    0x66400042e68074511031110700402030b40c040d0303508142c038600b07a4116449203043c000c0f000d410203903030360b803114207444003115102271500039401140c2500c441d51203961080c008500c01849041d14880000f8800544084043d01031100058413200b5a4001c20a0600465001100f6980f901d460905071044040c00c0e46107801e54054810000741c2490000b4210044e280e008000d54944031004136801540119580f6006884c0603421050503900d22070300c07481400c1540b0340c4440c0040e81000c00d004044464445d15448101d130040c0c2440b0710303044001b0585090b1281034440d078800c0f83e42203541c0e103818072042c0e11010760240010104151982d001c009406c0749031003138085401507900e40c0400307400d0340024010015481e201e0400a00c107414094142a0032044a0400f80c0c0f0701655140800c8a60344070700f064039640360b1602c0040150381007d104030b0301d00210744054103045060550301c190014000d40f200442220702464055200c204110110008607031001c021035660b00011900d900d0342c0c0702441000086 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 165462769 1250 165461519 165461537
    0x209210c0d200310020d0c08010905040309050112090b13260706020901050702190f0f0e060609041103070f0801050a03031e0509060d020d061401050d0c02120a0807 72
    0x1800c0c240e1101d10a50340c02800c0385031001031540c2e55180e844800354200d51512072528058519407680c4010140812007483c04903403115406c4000c1d00900040c3e004841c040e00c3e1004000100760700228405c1521400d28040c2010030100c00e00101422242e80e002e4034494816040c1700010b141110f0840f0260312602d0100c0a800161a032040726502154a60a90903420054880001c440d68000c001c091014101b040c01c05046401080c50704121500310000182c55a10034051aaa1038500200a202c011080ea510740d0406a0444070074001810742c0e4060007001c9850300c4595159041100c4505070440e8981d101d181012000b0002154188601d006c0b5515600110b49401c084400c1d909a07130b003685401c00d2108003499162140c8242c144d0801c1042810301c01d00c00c25a5800d002001480b8030900c016840e00c0c0c2d600120400c5510382c0d44002c10000411b504e244250b604a01a18064442d80000080603198828183d00340865001a50b90024001603a0440e15070060780079070140405540b00048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 165464019 1250 165462769 165462793
    0x13020f032a03010c080411040f02031501020c060a091202060f03090a03030633020c04110409050903091804050a121205060a030804091d01090308040317060a0501080a020921 76
    0xc8404c071005240024160500080102d44011950070030700700d01034400240c800401c2e581e00c003240c005075908034103d0308003402c40c051580e04200d07545100d0000c90340e0a14005201e00041d00041c080d10680600d0340c0543c000394207550703a50040e5894019a101c94650364503100c40f08c1e948480d8184402c80109241c40e0010a60807184a240c0f080003a1206c1e1003015001c40800c202c0b007031610f45e54040e0440c40340c07072480303c03071902c4500601c140403000704030341c54070b4030305104840041c2c500c0188229a50303401800250482c2d5690710040620301420121702da241d444034205582040350a140240002244000040803590f10200e03401c0500c52004082040303854503001c0186d0340b0307090b02c4061710b0352000380418407903116564884110742c00d628004025980880c0c0c0d01d1742c04e64031581410340100d55001d00304000c0c541c10201c81c080e000540a8100040d280c00400211507007042e0003064100540d03000041d50841e0b19504403045d030640100030008001f81e80d1002b220501e0185180c2c40280260001128 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 165465269 1250 165464019 165464021
    0xb19030501020a1e08060111010e070810060e090307080a020f0a2006070b04060e01150b0406020105090f0a1b030204020c0601060e0d02030709050c120a020424020613020f032a0301 79
    0x200744c014a40c0d800f03101e51640801101c1000104980707041c195178031002da6807007076010001c40c0014030300a006000b806030742320b4030001201c00b958800c0310000e11000800007804c50100c01c42c2c9019600445041d1220300ca61b008920f070280108801c1614401e03c4036107024000c07011a20491041c040c110a080241540e05012686c0140781c0001c1070ac01d0074001003000101550044042c503c20341000103139680d04144c2d01c1403200150741c4058140c000000e403e100d00c560a00034158000c2091004080b0144c070301c4da16036a40d4034440c0b03001d0404405030761a0148551446000001036070000c2096403a107104601090f102c003400c2c49400041140e10000c2155401d01030140340000740c00602418125281075200006844000c10104481038200004200e0f4501d0303145490049030701120040e00d40c0e0130207018904110180e00b03001c0410b0000482c50481e42d0740040c0f060b0b404880c02c0c040881038691440410300d040030781e840c83d640c0f40c001c44d2260008640540700c0002c00c0708141000f0154100c411007818 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 165466519 1250 165465269 165465317
    0xb0f0105030703050405120f0d0b010e03060138180301050c070f1104090515060a030b0114030718150e040c150c0203010c0806090601020607050306040b19030501020a 73
    0x1a02255060001800032402070744002e500501600c2078640e00c0d00a044a03460a91001001c007010b20000304200003059401c0c860312081250a080c9650b400c5036000009541d10014490b250301c4044006032001c0172a24519907440b06174140804605d0880000d03032854143d08810010210b242c1918924503042c070f014029203006010050f440c82c9010815143c1c40300a09131031200742e0303901c003003055031590f644c1769880340e052420300580c091b04004481103501140d181001e80342c40c0c8901e50841041c8046540700808504662035200d1401081100768003081c2402d0517688102c00c52582141a26007085031030300182101c0388491152140c5170b480e07e0f21101c4c4483c050700c1c040d22004507243d0600a0b0320b08503070103120f80346503820f00481a24030790740040d0079a4010360000c0006004c007414841e19007050030000e0b42042d0240040c104515101500401070300000f0103030352055450314404415a01e03040004644026840210108151281400380c00b0394441541c020000c3c040f0100c080d4608903039541c0ba = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 165467625 1106 165466519 165466549
    0x501022b0e181008071a120a0b28060507080d0b19080c01030b01020c010f03051504060f14060a08040813120606030201020c010f08040b04140d0302030105040b 70
    0x101e818146546d001003e820441320029140742c1c0d403081561a41d200020096425585403c2d4a80c00340582651050300b01c100f00102451f40c25142500c103685200d244030381c0440c2a600e003403c4400f44101070010b8600081030201d40c4c48100d10350429a0b64050007045009540840351250500d214146e01a48490780900000122540c040c02045e0440c3d00034005003103400501c00020304a02041c291910405503500d0024031400000c2c2c9540303040d180091b100308140e907292100e58442d4a510300440d40800c0c9a440407043e1440c142c4116440d0a00c2e43e5500300c140c0c0c803980c1e10b209440e082102c0c0802003181064011908a56080c064502c4600400000c01d41510f1800003a0911180b01c91107410052668219400da40e008608941c21a6001c0340a43c281e5485080c0344104a000c01031040320790141105240318954035030043e5059950440e1304010602100d010400414990005 = true := by decide +kernel

theorem cover : BRFrame.Cov 165287769 165467625 := by
  have h0 := BRFrame.cov_init 165287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 165287769 ≤ n) (h2 : n < 165467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
