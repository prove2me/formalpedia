-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0801
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:52:56.044985+00:00
-- url     : https://prove2.me/submissions/392ad18b-7160-4ff0-8a9b-2fb6a8b6b28c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 143884892 ≤ n < 144064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 143886142 1250 143884892 143884963
    0x60a0309110301060f03080913051602010b01030513080304110402040801020a02071e060f0203130306020c1908030105040b031011070506010b0301030206030103060b2806090e090a020f03 82
    0x41c0107502041e82108500105401c0b504240709100842d280210100046242c2d03001500e001280641031109202c070a201c013200301c0e5400c5440f150051800080100b1280e42485000100c0c00c082c201080242407030141e84050503a003c1c00100030840000001e401c000c0704150140c0c203100302500c01d546468640301918080e4202c1c072101c000512807a400081c9108000d400304801442c0c0215549035141044012254035405015100a502c0104084810f6a5040703420900840c01043d0040c2c580c00c64188003410844000b180c03002e48243d903a18503011801035402c507411034030100c0300045e12800b000046801c3c80c01c00841444094a409202e040303054013240240081c2d4450780a40360941c2c0c03204075010390350000b070001179000034040c00180000782d9158010701036254000d00a0038442c0005501409000e650541c0380d0f60f1130760450f01000340340d0b0841447c101501400076400301c0c0c2d28060b010079541e64096200a4850004c4600780c0403161020320041c0c040d0041d01030509100c07e5040c2c00ca44082 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 143887392 1250 143886142 143886161
    0x3270409050622110402030c0408070b0a0f0509090c0d140a050f0f09120a030908071407060c030212072a080c01050901080a09030e0402070c091b0503010b1305060a03 73
    0x407112000e00c0304455543ca599694110f6020031200300c2c43d03440d1002c0c4002900014800000b980301000081209001080702ca002000c1030041a60fa5221201004160038030405580d4248507080c4a01252a554400107641c0400009001902c8018159015019019554030414090306140034011100240d130443c602c9506120f240c0c580d1601e5280d100c0f022031004884080380758006213803c1c104561100001d0141210a14000c038140e8286e8a8031000c6510805044800e00708000744004106401e0092100420b03540c108131007445642d440281d116945c2450011101c640010028100010380110340031800507000103d9400c0c840d0404103401129602407a00c01e80f00702c40e1000ca80b0341c070800031030b04906410b03910071540b0344a4031900310190482c2c030421418130400044041003512103101401c402400ba852000e001c0f8a4620082c0c02c69280e900c60005034100b284a1100054220040740e04656401c40310980e43e03c0600d4620603021415048141d204c40002444081c1030340c1600f15480301c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 143888642 1250 143887392 143887411
    0x6060509040c02030405030613210809010605121f1103010f0320010516050a08030c090103050609070c0b07020708070306060905060111120a0302071209030b070c05032704090506 78
    0x194031000701039a0f41d0050f44152981a80080c0009d11485107440d00c48002c0362003a4480c280300040c1404000c01c07501175003449000149214100b05121009014190017000c0076a040c0b0841d06001c80f81c0358464400c45010803608040400107100d02107a039000c2010340342ea070103100740c07207584641d18800c00c28850f03c4140d8040f0301c3c1400c019100749150203101c6803440161a1546007078041c4440001c00041018166594040d4160f0720001c00c403a0002940b155aa0300201070362054890009811220301030982e90003828a5810403200d150800036421010b42c101c1d0510849581c4d40d1804c80c07900303059401111941c010b0740c0b400801c000305500054141e41903c3c800340241e40e40c2e50011101200d0703c0c51134281703d602035110300725190842402402e588445290261400c0d1190b00d81642c2c03000604a5030f000520986000c00610180012464010b41545000100b1841ca03444250f40c9018032038062140d910700f800642d1000c1c0d40d0300b07100070a5040242c01809001070b40d0070007548420b4100c480c601c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 143889892 1250 143888642 143888651
    0xc230a0302120f040302130b040903050337180507091a010509030c01050c07030b0c070c1a0306090601050403120201050105190501050304150605090a0905150f070c03120606050904 79
    0xb209420702c010b80302c1c03440c00880594101450740e002c01c426014400d000c0031250740e54802020464550340901c1c50824040d840b519a24248052000d070901c01504031194940c54004c42205403200038020f001050b1145c0c04042003200d4029407000e0a00600e00000b00f0340d1043c0940042d080e42c264004180082408135841c4a500c07031000156280c0c0716022109505400015840071150300603001341480c000088202c404903501c070f035940c0001001c00d4070354182d2203a000ca0150100407851100101602c540b01001c4005404c0c1c14440078035000140c0030506c030360740440010300203074800d03c140c8004540013406880720000f021000b90080c0000e015850041704501c500a54101026030302108550061391040e05d190303220785400711200c1d2101c02d241c8003a600c41c7e60000d4166101c80903030b0301541d508c1c107000921582c14503000f49009009100c0a6402c001c180030030100b1021840b405500401500f0308040c0e5504c0e40c40e00701d5040c61a804212041850081c0102e00685d201d000707002510340c281c50400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 143891142 1250 143889892 143889913
    0xb180906101d0a092f040501090b0a171c0509010201060501050f1e0c030715180c060309140105010f060905090121080c010c0c021f020601060c230a0302 67
    0xd03814a02c6050754000c0e11154000ca50301c0c0307445502074409103004440c02140e03982004104c0c01020100e4a40300f420402c0c02c0900803061a1601c44d0074010001064108900d00c1c100307001c40c1c0c0100661140d50340102001e0103105210324148801c440310545004e0308495000e00c50030141103034000c403000500562a044001c00c07154020000c40c0d40c0080301e030b0b0415080c0340302d0300b4466403010072514481d079521105000d00e0f070441d081080500075035803181420010300400c2080803c120380074a001411186001092100410600c00200341901c0c5d0516010881f40c0613420072003811100c0e070701c1c030158039840e040c0002010f00300b0200c4542518115075919105a43d05d004210022000b030023283e40d100200c1b1081141c0901c50344480589070700c0350501c9ca050650f41d10040342104c120300003d03c0443c1742c200043c802c40c90854158107480d00e4144413891255692400290f88500c1400382e0414000f2004183c0305104440e6482005420100d06140203040000350f40c42c0c03200c000103001c0f4054407030801d140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 143892392 1250 143891142 143891159
    0x11060f04090c030e060a0e0a0c0905162c2d03010f09050c09041703010906050a1211040f0605040204261c12020705031201060f0c150b18090610 63
    0x204d0580800014201c0c1d8444401180c014540780807100c2d518400c11400e80d0004030f00310700f04401000200000074039854a0703044070700c5641c441345818082140540084219624641c0e081040c020403601200c2170140c1407020071034001c80c4c8a40c0050000c1c040320011000c0810054025240109600920428500000c81402ea9103201c0c03000780f0a40085510078200d042a2a0b26503116001e00d0080e0480c101610b0518200d92080e0003824595071101001e0110b402c0c44400b0000400d00840c03541010b1a458075202c410901801040c1d206986880c4042c01d0443d035a00108040c040003403003150b81e1780d9250084012061240b654001000c08085811511000480c220fa8010702240030701c400310380c4d80b5900700c030080541104601100e030701340a18004142d0030800b400c50341341d503110080065410301c07601900c45000c0760310450410030380c544480d000a8032900c120300742c0c2c40790300008100744241c1400920961400111344900d86002c000308020040c0001c1c0341c9002d2100c0c0c001d840481c648941c0e12 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 143893642 1250 143892392 143892401
    0x51e04111c020c0a021305060901121208090c100c110402120a05130c090b03120309070b0913051006140f0405010f0c120905130506010905010c11060f04090c03 70
    0x5070780c0340290600c0e054407101400c2c0c0061454101103801c1d01d070307146500d9000070401c4864100d8515000d50395000c2129a08008105074050490074004101d01e6415507035460002000014000030044c0c1600031402c099020003a01c44c0c2d2a2008010600c0344806460080800e032075080c1c19210310f0038500260b0b5031400c0c81c4c82114014114100200b1083c0da0381207038039014190281500a1003d00c102c0700c00c010942005209000c0c0645040100d4183d10040c10103150050600300c1141d2003100f00140310354920000303995000c841028803419140c4010100003040096405140201281002c0401c00260200390f001c40503548152540d544100307428104181c0380c09500c0300108455002c2006020079030144265026088580c5418004a1103540c0c4201e100d0a4400301ca00102c2e80001d4203018903e484440c1c201c0c06054844108024038000b4002880c0031403d00c20f032810701034140160014040d44c610400d1072010050f01040e40da04c140c0c3d21a00d0301d80e110b4810072040500e84800c00101c588030340207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 143894892 1250 143893642 143893657
    0x20304050705010c030522080607020c0603060d0804032102190507090f02091005040602010b042c03070803010e010311060a022d0601030f0501060503160603020a09051e0411 76
    0x103052a42c14040156110303aa0440709400f400428010104003581191140c09003601074407000303000a2a0178035591900070043e1040701590460890340009881c0d003002d072a0b004400b01d43d000240e40a500b0500a00e10031a00701801d124401c01d40280b0801c804a0030050742c0301c070750342103a003031000d000d4881e00e00300c40200300284580c201440402400c0b10075082520001d445c2580146083c05520001c0c3e00b84080000d0304002c2000814200029270302841001000c1e0030507031313042c46094140300f500306202c180507400c030004000e502100c20b00c101041003511ba41907402400709a42c0e503180c08021441d400240300031a158104c0c3d01809145040540c241e503000b0341584c004001c001404622400551055041012044aa40502d0801d1042005418006c50154069032032003015800c0680c02e4507050380120340070b9070200c0c05103400b4550b0145000121456403030f0040c0c0b19184050100d034000500d501180c1d014440c004c1203106a80001c81818962100315400c102c0031110102d40003080c0140c99 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 143896142 1250 143894892 143894903
    0x1506090e041a0c09270106030e0c10050c07090b03100c0518010e031f0b0922020a05091807080c01020d110109240b0103060b030601050a020a140d090504020304 70
    0x60410958000c03902d082c60300141c622003030340c0c00c0407044800704103010b00d460115030003580b100400010030801440464054951450240302580b1403104a07941c0700c000741c40d404c0c0642d54a03a411012144640140c5a040100074241c588140d940c00e42d0a001d0900c0e616050721a0081c4994007000108034810b00e00001c5240d11380d00d090a0714481421074044550103194140014031641e0a090758051100924046091240c49104002066061304640c17904141c640252a540c0511508044240e229512100c68088100e4481d00c148040703039003518141c0c81650018501c800b8050910750588501e090ba8050744101c581300c582e00c40c401555100c42c00c640034050380050b038102d041c103445410140c11402020002094260b4a507803000c0c900290402c8000c4400ca000318001a03a41d801d018154240c442481d0607c51075041100e000c0040c03001070000c9041c0580021800c403104d000713200c0006410740202c00e9613041940343c1c0140343ca50310448a0080010b141500c041510f103070a10031b8130700070b03900030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 143897392 1250 143896142 143896163
    0x504150c0509180415060b0a030b03030403020a05090408090d030f080f100611010603050f0705030d0203030903040512160303030b040b031501050d1a130605010501030216060c03020c011506090e04 86
    0x203103d8100200301600590325551650399205041d05903025800060a101e0100e6a42e001c8a400c010204e604003503134240300750003c200820150ba543c50f440002da0720115005100e03032300e4501d0b10304041d100f00211950018105000042030603001000b1480c2150103413a504c03032664400f0040b5404400450f1408800139815006002c028401d02030400290500000010015100d0f00c80c98a002008021003105a00c00385040c0b020382014016039964030440c2c0006d50a50600014854a030301450060500a070b00103503018601580c20824034188850200e8201d0320300c0d440f801d005001d4100010704500031400d0a00084031414005072071500d01c80c550b400c00c082039007032100b08070360507594000641e04c907001090700d00006038003200740758021440f029510307222105518044003a40c0c41640304a06140c130600500440344140300201c1d0300650301032400075950306100304c2138000340034030f454808140d840c0c0215810700d04190034400b03081e1051500c602c4809581d581407504000d03001c50340104800c031740 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 143898642 1250 143897392 143897419
    0xf0e070e130b010c050304031b0b0304150b0112180308010503121206010e190906091107060905010e0d0c050105060609100309020f0d120801080d0e0913060504150c0509 74
    0x1d940c007082038100145403100ca00c40c0070780c840c2880d64000d60002e80d041c4042124442c030b40340410103204014290029000d045152a0b1950241e42d00c2c40e00701401481c6d1907082d011180c0e881000b540e0200c0d84801401c0100311001c9400c540646841d40c0300b10003240c280c50020a8528001554220801940000f0703442c140091209510090011b041c082c1401604032142550341d45581c0506108425010b00c205807030700d8001c0076006e583e40d951215009070302d840d5030801058100811240c0164020038081298081c80c50424010506050541900d0041c441e884204941c000090a01d81740114028000c4d0b844400030003940e44541480194070010013103218010324025000301c15180d0005003800ba540d0448004118080b0b1030080c211525011000302100950300318240c240035040c00002000110842c840c0a48411580c0c0035003840f400c440800220211140030f2000070240d80040244841e08042c0341821400089100c0d82e26018104280c0c40c100700e00c40c000b5140c10290080030898075600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 143899892 1250 143898642 143898679
    0xc03150506010927020d0509030c0d032003090f010606020703150b0102060f090a020604060f081005010807180503030706150602060705040e180a03080105010f080408310f0e070e 78
    0x282c4e8032012891540078004407001c1c5a841c821540b0030300480340079503513400e01044064203000c0e0308000501411702e000c3c02c03040348100680340010340240481216a07643c442282e220320744181c40122007140d40c28400003007079035a40421420210b030b12031a0384851014160340f4403410b80f03604000a50050703200c100066807480e902040d6640110b00601a5040c1c03603a2500810701a5015421120104188108803500154401091588402d13441000d102d20390030700e0700081a048000d0324203400c211003402300c107002413a230410810045c00000d08581d910502454094054804203a06407100107042000161550001c601548920a2503554074a054205148010480c0001e0001d40300480051210380b1007150410101c6c480c1806916002000c2d85407a00062a031440a0741040422044209000005030700400391941240030194200a502c090b03a84000348025003092480100000c400000e4481d0640c3c0c1130001f900e010f0b400800455271a8002610300c0e0010703a0f25240c2144802045510310407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 143901142 1250 143899892 143899949
    0x4050f30091507030e15130302060c010605030a0c03020103051f0315022b06091119030b0612010801060e010b120402030309190e1303120b030a0c031505060109 70
    0x310001e00290b2504030700d04a000c4607401020084001c65590074502c0c000346070405641e03c254100b2520245000c0540001841d003545600c0700902510303000c02d15441d403803030a4100a0180c40090b007252b207240d02d5400e150314030b00741c03511060303000c01d00d4400401d80e443c014100401d0700c50214002090040d1940c0c1d00e00d0695070b900d04148110350381c20b000c807000d4902000b80c1c801c50394248880d00c000c1201c00d00d80205c22100b199200c4e98140386000c200000e0003c4080694000ba120701548000e181a450000c0c3d002d810780c0c02826502c03050010f001c2c585d400b100700b1558141d9883c0c80081114640b0b582180700301c0303d02130160284a000c10f12410912800b03898a041d805440503040c6d030b042400100c0400c0007512510303c2ca01810b5500707541885480c00354507859502000c155080200c0700403c1d14050310482c0c5440c0034480040d10b815943e0141d40307040107412200355100d05080801a03481c10719908125a0b009040c44540c2044040b0303c4641c07180d001c06d0301b0f50324540c591490351400342c43d5006400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 143902392 1250 143901142 143901157
    0xf06081f0b0a030606030c021207050f0a0f06050109050402061603030b0a08010903110111031b0708070c0503010e06010806070e03010e030706020c071d010e07110604050f30 76
    0x34241600603800d10603600d0200030040407032003403040e220b0141e00d6016080d07440c039810110815103864400120542e0001e003103e0904842d2459980d1030080c2d0034207504003030500480580d00d03c90340d9000002c00411080080d42c81d0b01a580402c0184d0b2149580d809844041c0c030040c3d072185080c42942c200710150301082034154480e040c0000d111303010401042c01201c29030301490183c0d40d698401002d05401104891001402e08000c000d20305003030740301d039050f404050078404200703680c181466450710b40c03c01110506501721518030303140c80c401d20300784e0012502030160714029400c0c40410b0082c400e000070b41c14160303500c00000d015a65078070f12040b50041d124506a80c2c0c15034039a000e08072000c0b020f1006091480c050640565940269043d043c81e212180e4484161300d0085480404102503050900381503039940d40301040b0580301c0038004c4031a12450054442035004210a000030080d00080615100718000180d9005e0036001d8050b2490100544520340034188000011142451304030040c401d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 143903642 1250 143902392 143902411
    0x105010f030f0b0406320a0311060f030c300f090a0c1e0f0b0703051c020309060105011e051206030703080c030310090e100f021c0b10090f0608 63
    0x9203c41c1d440081c05840345a03000c00c40b04005014401421007004103840d2600c40b800401002da6490ba5000c05d080d48001d1101500c510000c0441400694610084078051402c0c06551501d03800c01c50022199940a009080c0b0360700c0a80801550301c07108100d42c000300a61800c0340d43d21a50360031080c002c640c18002c040805600440381a00005803200b000707040030380114001500d459001001051340d5480941180034440403400c1c0030494000d4040449403045c0d8103207052522000b510b01002641910b24032520320341c13070000c020001401c8000488a048410990320000141c103108602c00740030011800301000103104201101c540c1c49142001c50300624084c04030f4100c59507985409120341c20000070601190230000905c40e0303040c03400c0040c0f009040054401c07c00b44101c0800c4599407012003039441c000d03070780b5500c0340c80d10081c141c0d041d00c0713032a060b1000c0c080004145c24081da0003032640c800d102e8882d890450480c100341d0321414400040d140080540c4031000d00f1b220090320507040c000c0c8000384 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 143904892 1250 143903642 143903651
    0x70f0c0816060905150405071512060b0d050c03010513090c050603070503010305060915011403010b0402040906030303050a090f03080a0902060a0807021905030318030405040504050c180105010f030f 87
    0x11408014064080075401a280000e0800d194500b003800c10326851100c40c62400c0b04c50500c8082440800c0c07100840b0040403000d04400c0ca880c1c070a43da00440e16500c00900da24003100043c04045942c000c05c3d406801420812140d52032400d01200c5000c02e005054124801003443d40c0000000d40c010489603001c0e20700c2c820445d54540025003154401c1f105400010801f00041081010410003e5088001000a0448102084802c0a2145052103201d070904007010301141c03030303072000e41c804084900060002d65031207860320200380140c07110b80300c210006498800011032110152245e85542c1368011000d10601314161021180340c800a040c00030702c03ea1700d492440050340c4110040090440c241c44810a920b0710502c00380c14000d5000c104501841040e5090f030004501004603680030040f40b4400d40303d0702c0900c01140c41c50003241c000c6c81e0032a20301410300080c00000281c88000000445440451807071140200300c401c2001e1080a010030413440c6420310a40c043d0700715201c00b1200c40c60016 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 143906142 1250 143904892 143904907
    0x80714010507170403020a0b09130f150f061106040f021012180209091501061404050306190b120c0d020402091314101a13170d0e09070f0c08 62
    0xc00c3c000c60610121005080000d0030011420000c2940004009802407581440380242c08a04c800740801007501682c2c0d910100d00d040c2030040c0c0d002c83d0400250b195003000c010348842101007620058040c1c1d90115402883ca0400800c00203001445035a10070510708503007240394284400000b229403071800b80000440080000300c0c40f07128401d40000c68507003c3c60a031280d801401000f560161404a5507040444035400d02550000500e04403840b0b071130310103001c10420648595502550304115417602510040c00074402e04840340b8160501c0d140d0082168200705c00400c60f40380320045444e0880d8100d40071001b850b10b080340c80030042c1400070740051701c0c2407a07030030000700782410348500312004035640c04160a00724500100c00b580905a009080b072040e081890504000f4580b10460941c0c2c60002034505e404044418003200034496480d102e01c0c11003100401030f07220303001a244040010b82031b013a00c41e56460f0044203203010708000d1b1261001d01c40082c8084450016442007941e54010821200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 143907392 1250 143906142 143906153
    0x4061a0705070e31080702090c0f0d0509071410030e0a0f0602030f0106030608100905030d2306060f040506030405160807061b03020712050f060c07020907020106080714010507 77
    0x46104590079440b0071144d5540342d0241400c21006034544662050b4040b03030400081e8000d0441d003caa8040302c0c0e10b20f840c2d854950030240d51107055580d1079a9280498100d02c03084e800d8108030300800d5090181c8510913194803076400604155034a542e441002480c041c11050b000b9802240401180c04c01e940360440c42d81c842454107403400204484c2030360b001003007286241d490400c1c20b014006a00c4c0c20710440d85407104a030f5680218411246c6016555071030303041000410401c651141e00022001d02c5440c8142c0c1d9002c1a54102c1e03200c000020448500282c054580441103441c4081c5d80010142003a04000520003550030081c021a0f45208114101e042150b8003002c041c01800b0180040660f1b0b4104100104015070803100350850034803c006d90f500280d00451800180c50000d0092217018815081480c80c01c01c2e50301412003203000d48028454040240c0c0d00809170a030095517240c61720340395039500301d003220700c24401c684c41500258410b00440426001c0501a01c4051402c1420100240ca64 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 143908642 1250 143907392 143907419
    0x3040f17040f06031b020d032301030f031101090b07030b010c2003010b030c030307080a09150302040509090a030207061407060203010902030105040e030301120b3102030c04061a070507 81
    0x140e0250b45458008000b450b60501503424085009000303036005540618010f0340c2c030500d040d81e200c03c0c9905e4020301010751501d10500301e480c0c045c00e0b13920b001a5035a803c00b10030b0358000820680000b2101e628100c001c100500840c4d05440d0702070407104182d5101c400850081c0001e40082d8100041e010031100800e03180341d4030f0680c0800030050b001c02600440109801c42d90780c070318024000d4100c8421041607540c04030641c1e8910b60803071031031a502d014904003140c05041c03a4014604548481c04411002641a4090030070b481060760740c7e0116403543c444190b569101c03000001c0060340590000e000b10341c49001540c044c10200d10000781041d1300b594030001a600260480605a40d010004001d1880c00380552000130811001175407642d4100345101c65403030184507014101c000040003042d024940860b052000031103800c540000c0c9061498032011040b41000207078400e2040c40c0441a042c50940301d40412030704442c1024400b081d02440c00b20f215000840b060b6094002d4050000354244654003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 143909892 1250 143908642 143908649
    0x8060f0402100909140f0601180b0a0504120f0203010f020c06070f0509030a0506160c0308070c1506030516051c020d050114010e07020628181b180504050303040f1704 73
    0xc00d000341b803030010350518488200504150400124807200180701c400c0b02a0314047e07900f2500c60351743d10011000252420301c034540c0b0100801c04c3c0141d01d542800749036140c070b1011510880c000e010001d50003e13500247c1c040c003000c0d00341a40211021827001c0c0d010340c440400740c5529003040d81c2000323003c400080c204608420241c0d141d070001c05c20065507401215040c00c2e004c0c01401d2451046840383c400400c950070040501007403110280082081c0500b480444000070407181080c0071507600d80c90312a444580c00003400030400702c5c00c5404205072901c461901791482e1142446071709a80150208084204a004180e9255680c0d128a84c5d841c080e0050050207815880703180300d018284600024a881c00040c280303402e4103412070386014849450441a4160300d144200424541440104448000c005580003007204001f50a800d11103451002c50300d0841d94040d100615103e0302011140545000325002005500701b000020005010300000480e928014440011000341c0c1e54540c440d107034850342 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 143911142 1250 143909892 143909921
    0x201110f090f062503090302100f0e010309110402070204020d0501080604050d0c030e0906060c0f0609240f1914060f1c0303020a0509130606080108060f0402100909 72
    0x40011079030030700411460244409407000e61a00f0794155a2a20150062000200345036480042c50180351140c00d4103409941c0007040b44243c1c0000c3c080103003481c0110154400826198010000a580244a14034040e904400c9d1619490004020840250700185080b40e1195081c4009114800300344036940c0606a07480c000c14050030076003440c40c9030483e410990f008100441d082c040009502c42400c1c0366410040d941503c0540320702000810602582e91901040c0c4121461001102c4000654500400e480c4040e02c0c00c81e9100d11154a44a0892a0f20a030a1a021020944c146003a1040710390020803000200c2c48868145142c10581e100c0059181d0581321074000c1c40400d1802665039600a2003c88182d070301050101c0c4c4011566403514405405c3c9a404600c035241240560112010020001d042014138481460804010403541c0220000210544000b0030001030000e40c8900802c25a0012251992558200002c202520110307500704040c8800000b4081c82901031913a40c0306c50320 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 143912392 1250 143911142 143911147
    0x203041802090a1a04090507050c06150a0510170405070e24120c090c0d090813080105010b071b0e0a0902090c04150305090111040303020f0708030a05040e070201110f 73
    0x42046903280d03044c3c0010798030b4410038080f10b90090080d0200c0d021914030403408540303070f6901070b001e43d000d00074407050f4078143c096031040010003082c290510761141c0e030440321440402c3d1900240200340c0e01a601b460013080520814030365001c402154658858440c000f20f610280d1503120840410a043e1901c409107030743c98030440d4440c1c0c4404a07111b40eaa2050390140c00d10400910f209a85120440c5058028503c4c540440c50610760700c0b04842c44490441e07030078007401803645020b6002c3d40c055001020820502000415449810b00466040b2880c5044090a04a103902c2d40114219004080412001c1201c40014465042e086c0240b1034494075200040d25100c0e40140700000400500c004240a0f08200600020042014000e090001c1c0d18000034a5511010102d00401901c1e001450105020a00008241d0b0001e00c81423062558001c0e640a030b82d60740466513581c05a500505c0101c1c1c02440f052020080c22000d06510101a00c000310302d500078040800c03400e60050a0707005500000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 143913642 1250 143912392 143912407
    0x80c1905030a06080a0c0e040c030209131118061c0b070305060102010b0f09070c1e08130614030403050d023702030f040312121b08060102060f010e070203041802 71
    0xf44500030083c500c04015000e001ca155036001d0040946e4054007078460030a0010500340030203503200b4005103078048c1c01c5944500b0152a0282c0d520a541800c55030442030180b5501c00307040c200c5034014592242e212040d0580c0f1124100100c22086866080000100c0c08442c00844d03460900d0070b02442c0e55880000e12803c0040009007594403c40300b8501503003910b00c83e840030b40c0311022080d034402d083e07162141401710b0915100c442c0d0390020040171220b04031100b81c00d051254002c0140449105c9041102c2c0407503450209945400e8441c02210b0100340c240b00203400309000b00c0007481c1c0d000314400c00504e441d40400702c2d615440c2c1d080888040710b03503146060030320b0401140c0160785c0f035a005000450030100c00b8204106103200340c0c04010076420b06000070314685401181c04505116000c0810710502032513504101000030006400c2000400a0010484a500105816010f81c103800b0041ca1140c0c01d01c0c4c0b600c0f04000c8040e1142e021840100000201c18443d90500d0181c000080380240c0d94044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 143914892 1250 143913642 143913661
    0xf1b0c030209250302090103020d0e060105010e09010608010905150301090c06020f070e0103021309020d0b0a15230a08070603091a0105030a061109060d1514030c01080c190503 77
    0x70000c0c40001e0301c1400d50880f1100100107a4141844152490056640c400000041300a40542c5400c1c0120314285090005e0001e0003056242c16240287d943c000101c11507010814411000e06c2183c011900c1d1a0041c00300000b03c0d044594040b41c01114a4103080341c0901081c00c441010070151007070070301c0341000e100803981444043d80ea003840350001e06800d810084181c101000610000f48240c42000708000520749a41000e01c400b40c00400800d907403d40d47c140110007690895806115078079005482d440d480306210144182d6008540440b0400d00c0c500403015500380d9042d1250348004000d1001030000c0741049420007038407103542e001c11481110f1230300d490705800380b61b08000c02c032000398014440342d00c0000d00c180200c0e40008011603505440c1020160601c61080b403160000c0e000510580c59a516030461600c00c0002d81d82a10103503540c4075039429a03c2c0105126a15800000c1c5020056204004030382c1c00040242c82d0625114000c0e4861040d2200216600081480441044116003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 143916142 1250 143914892 143914909
    0x3120c060b0307230d080a180504050c030f060409140a05010501080c0607081b03040609030b0a0903081609081009120c0c03080d0e010e030919050a0302010f1b0c0302 73
    0x281d0690080001d10308090303203c220f00d034410750315280c003883e03000c6071164a07a0342c0341078518410380124099580d1030019500810f031040e20b02400d00044800c51000406d800c0501c551071240010006280c15030b10390300d00e010182c034809401c0c0d5030301548070500400800c0a204015023260402c01c001c0004170480c0c6852070944405a0050b101d5401200034850b5a4071040111061154040704081d41c03800001c0203005040f501d000010401e00c4040380c04509650005120802d40340204004003080d907076050340790196a4109401400184191f0108501180035448820542c0242c10510013098949030611f250800c0b0601005802d61104002402d00400c21102400c200341d610302100000c1103600d5504010180c1d120080c003402d0000380480c0012210b50205e001c5005410003884480656250319a40ea041040558440c1490428854091003444a44000c655025210140c03841c9507400640f4420300382c281c5a014045420900ea0310703901c0049101e4005403191000082036410340c0140314610 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 143917392 1250 143916142 143916161
    0x21e04050f04090503030109020309030d1b09090203070c031803050111120709032a05120a050c04021804050903120c190503151005130906050f0301090b070f030603120c06 75
    0x5600d81407090004c81c0d00441102c0c19105408005a0b598640d82c103000c0ca1032084a603a40e410303618100c001418200030344a910006801c60740c0715000c00b5100c060b82c8089120641d00030307000c07a20ba41200310000c2c2c0207035046000c41440c49040c83c8160340e0307902e81500390382e20341e01403c40000300054005503440444dc41790340c10064500e004140141103541e10b4000010543d078500707202c01c0508203241d001c400181e081002d0301002d401801503604521070240d4a40e101c2c54101d919000b001c2100f2042c0c2080d1081d10310002d8101d409030800081101408010400580040d2050004128400c1d0f40300c0c4408082e40035500d400301c00c603529101200c0c440000e2414072541c9013044000c0081c4800c0da00300404030824450121141e28003040f40180a40e0b0038480c002d441d1600540e20307100080d40c43d100d076204408903070003510100c1e42d11344504109406c80340c907213500400d441408000f083c41284150040720381142c2d1400c0000c0c129440752035941c0284403981440002840000c4480200f006e94002c102d003a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 143918642 1250 143917392 143917399
    0x608010510090501140705031614010b040c0c02040e031911070504140c09011205090705030f03030603070308130b0d020406120902130f090f120807090303020303150301021e04050f 79
    0x2a0b03420000001c254100307007940104a003401080c1d42e024840180225403030a44494151440d030036a40c50301d049120590700008426500c0c111822407642040e010b911003034110f50f500c440c001d01d0700380e003080700506241e801c400261005000c0304101d080034038044249441944c41d80070300350340ca02105a00c0c01d00550880350042d8100800e007440401c40801094220001c000030503200d00111004854002c503003100c00b52068104400c0c0302e4400000301d017a1054807130a070f043d2485804407045c1e0b0740d07982c44181e81180e019031080c1d104001184203030026150415815524020040e601c540c404950f80265180f9012a0350001f030401a094105c1e803600d802400c03681c414070290119800280c4610703691440b66901d030b5120700741d00c000003036264003140704103034802d0700110f080703500d17041c080031156072410a6130201d034161010582080c011802201240d81c154019441e599070030489980c03e21400301038542540d021310809484031413260001101c1181c007080161520718110401c01d00c000300b060002d02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 143919892 1250 143918642 143918657
    0x15030204050f10170a080a050d110415050418050711062805040203070314030d060306021305120304060c03050405180601020d0e010c0f0c08101e061409040203030c070608010510 78
    0x1c01c820702140e45121170780c00018030b507101d07030100ca002e582c184078071056030a54600d012038145007410107402800944103405080c0c0305101d0702071002d0700c1a00c1a0b005a284401d18120300e01c0e41010250012a8000c0309403812440944000c04084e28160701600c501410500d90012a00300123090f4419225003000315409000c2801c154010035101c02c9640009040d201112501c801e0002c401c10481d2481d100f504000c103d140d41d20300b440e100940140418103c50407600200059a00d0038000c0354004519040c003451070a40381550507502c1103d9404e08800b40281800005543e41d204a074201c50341b1114154241d0900d40040020f040c5001c44000c003051010790756520201da64403451b04004154044d4103410104054181000b50943ca98441c00c42d6110f03a914002c0c0d17481050300030700c2d094011810424002080c040c0c02a00741e5556014107960724011014401c020312f4001c400e540c0150010b002d50f4074105100101c942840540d4000d4004030740c8500c010045824056a0120480c1540c5403002e0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 143921142 1250 143919892 143919929
    0x90c030f02100e01050730111009080f1c050c130b0a020a030e0d170703090e0f0a020304111306050a05040603080909100806010609030b1008060a15030204050f10 71
    0x8000307010745e1070094400036030741f044c10741352000040005550100000c9404804101e840004150100041e10102640980441d41ca141c402601480c2c454642c8400114107001c250700c030b40c50064025101540341104c29200e0260000580c2c0311b014003e090045c00c16981e10132505e19900c6805142d48003010400c810009000f034281e0120b0815a41a40752030007512204030140060104130340b407100501a03e40c0003a920941d0201800107008151007a120018000d5807080b00052100040341d01c4403040500c64006212656103034015a0f00c2845181c400303a6580146000c00c6c140d884009401d0b41c1c0682d43e100911035840d001803400003c000c110b40c00e2000c0b81c00d66441c03001500542c080726000f402500c0c0811000740c901c0507584094000031044540e9580e44080c001c01100041c8030640d06910110081500e00f440f0440c0c040c1950b00010041820740c554030074540007004000822001c18155200210060741c86004203030045401070030300420350805680d103404041c0281d000c0c1d09600b0842c2e007803a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 143922392 1250 143921142 143921147
    0x80906091b0f031203070807090608101202010c0b01081624030b010212071a0108010e06012d080d110f0604021302071401050405010b030a02150904090c030f02100e01 73
    0x40019101c01d49440c084074207400302080c6410b4188040d002e07201c00200030003580325800307880c86100d0750080d520845e2642d92103400341c5903aa41600d446100d00c9095000740036040c5d0b8400c0b5241c02d603106260100e8030880c1510b4403226850300381c110100d190001d868a04000301c160f00c411000d0700c40784110300304181e0b2208010b0501030170020511b09241c0c54464001541c1c0c000d200c030600b0718a13100200d43c0e4820007442c04d0810304480c1c00441800300c640c0000840e041d00144984258404010b0003814941d007007413045a601140048164040008011101e242814048020008011900080c04041140c06015000d01070501d00803243d644070200070b0342804400600660095010303100110b40151450b24080a4460514007800525140130000010710301503010342d11a501410081004030f00820805445803103085000c2d60081d81e640e85c002c2580c4968000b080c00440003000000c48030b40307035a1118401460344d0310507941201d8082d00c86040d0300f040c00010b0110444c9140c038004441941001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 143923642 1250 143922392 143922433
    0xc03151002100b042918100e0c03161206080706050d180b0a0b01020111030411010f030515040b0406030501090317010f1802070f051f06090507090302060f04120308090609 75
    0x389864106191704c00146c403401070458045104e408098418030308050007252101461180c150b0304c9005130001852226841c1c160380c01501d02200da4140034081c03000880301d200400c40008107403070fa55280054040401c0012400914464035890f841d80c3e030001101080301ca800c2501c003654a81ca80005001903030b007640840c0d02c220308450015044111a0040f401800070b0750072170001e010000144000e10908014040003040240d071110041c6044060440c2560001d507054200c0041e602182001d45ca810f030845441c0a202800014443c3da4a807240c3d42500d004450a4021485d03144070035218001481210340074041c0d240110b56094034081f0365664692503084014521035010513a4404c000200e440e80e50940d4024040707984031003401d00c07407a412107002d04504007800e00d002c07000680d0800710302034144104a107840d40030440d459902070080c1075100e41c00c040c4c02444104270100741c1a120500c981c4449002e5a40d003800c0d840c1081c415850071030f0240c84984036500000b45036080d401003928 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 143924892 1250 143923642 143923691
    0xb07020d1401060905010b0414010212030105120c04050103081201090603080409020703180b09010f030b090f090709060803032211040f0902060c01020c010c08040b0c03151002100b04 80
    0x40700400c1c65030405060041903244c000c9030b0401d00b05400000d40c1d04603100540180c4200741040d1014000b924010381e528448110210180f020510040100d8648000091410340e000e5041d584e00c038404600160440d40d007608129604840462951855080d0340086c81c007500c0c3c1360301c0401240e400c0d5110403800d4080c510804076030640010b20031081601ca51050031031040000324120489480fa081440290070204040f030000d010241d249040d54400d001d0b0055007080a083c41440380ca034042d0303c120f80c0760000c00f50740052040e0040060021194070a04000b410104007a5450b8204106d01c84c11003510045002d103045125920f10b03011411910600ea85076108450010700250380a4240c400b8201c108030295000101007004c2911141c190010100c074507102e8000c000c1c070045c07028103440905055070301410100f61200001c0007c03038100c0c000c64000c1c5012251882061258001901c0403c03440e807144010782040c240c10b40880c00c14000c15482404c1218244050f242592401440a05045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 143926142 1250 143924892 143924903
    0xe0609030d021305041b0e19090209060f0c0606030705101d040b0303181c0b0c0703020c12030d050108070b1e040e0c12070305040305070326130302070b07020d 70
    0x640f6451074089a078040000c0002070401d2101901000303450b44881c05403c031540110300c02661500d01d903c0c0000e0700300240e0030414007842a0500b8500000000e40050030720a0b040300701005040e025241e03840c041c200b09081140101403d103400320600d81050034550009014a550124070100c1d0350700810348900c4030503598800160f1424120004024040b03011019030103000010303d1205440b03a100c0328071252503003076038281700b19008101c1e0b203804c54454280c00390866840201280010715000c0003011290701910480d5441842440064080303103400d950050990320000e01260050030300c1c050706006092240151808500c2c0141402c494480c00100440c003030311890402503100009015a0050310f03441d9401d075054948200c80030b9a50b0300042090f89070301400b00c0060754043c480c0c02003601c200d916a8a06013805c0880da000d40d4107100001504009190401e1003000740320040c4807081c032030100c071140356140c0c0c916414003a052100f241c010703070b0a00c0f03400c10100001d621200d40041e886039011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 143927392 1250 143926142 143926147
    0x180601080415110a0905060901050919320103060602120a140a0225030804050f040f05070e0103060e0603030306150408100c03111201030813121202010e0609030d02 72
    0x3841c0080e12058038003408070181c0d1a00a003440980c40d0071010f0a5a683c49071617042400351180108051805030b580c2550018504000c07090340c40c02c0110351190286003c070420800300d6242c04191550903040d40c3c1c01402040114010206036a00b0401c0304411442030a04002c0b0905084000b5128407652212444403500007590191513481480c3e0401e00d40d0154484580301c82d0f0300c1500039100c40706c521038817410007182c13110308040803200b180703000889520034040c41c0b038107140c9018414180da0001200c1e0b407207a41c2d0381c2c003081450480e000c1d0510405107540d41c0c80c0120180c0002400700e504542100b011341a02c4000c005094074000304a9410640c1102c4040c0c04502d081c400010700c0c8039607004204140903400d1221000181e680102ea40150a51410320040740c2d9550b1108040c011580700360074a608035030040020a401c007000f40301d4100400c1c450301c00c464944c140f00d00381c0c4041c01012240e03040c1d0140c070551f15070303820306c40c084142040b00090301a9003081c686443c2d490182010342242203900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 143928642 1250 143927392 143927401
    0x60304050c0f06120a0603020a0b04060e151b070e0a110301030609060e0706050301050901090515100302090a0f15050307211517010c02010b01050f030c090a180b18060108 75
    0x4a0040d42c00c241c400130108881403070081c040c1c0010301401c1c0b10480c0100070500001c60a02c501600740c80949a490b520480003645901c100040c090701412a004015403c000881001001c0a09400d0b0414010000c1001518040ca041eaa030302c0018081600c16285c00944422880b080301200d04407504408049030072007550501e000102088069180c0520440000168a40e00f06000d14100d030003c60f482c540f6a82d131800c2d4081a00c2049426080c4a50488050340003842c200c207118446100c246001414601004040744c6004003a4000d01c4090303041c40d400300a050185002181c0000c0c40d0b00d000b500f9428498400341c00c9903000b90249014001c00300c0000240e0640b940018266241074406200155860650780c400056101c052403040d400c01d44240031042c0140543d024200f41070b9909440d107134041507030100300c0e000901400c500c03d0042000f030303000c0d54403880800043c004007480c01102d40494141c1c1c1c0c0231101c0080f900c1d80280800d0745922001070a88041540c08035007030034604030315600c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 143929892 1250 143928642 143928649
    0x6021f060b18190305070303030b010f17040f050102040b0403200303040b071403120402120c0a0510050c010c030e070801060509041709030f06070e0105041203030b0a080f031206060304050c0f 84
    0x840c08035901d00e070280f0381d8000300780800001c1000c02c0701d0294400b00040451000110381c0d424410300c0c140c011511300682a10000311084060340c0c03082c00b962043d41007080c1c5544041c2a07906c2a40102035900c000304051003841440150407030b5400b00164801e2803d034440010035105e0040b4402d4403040100407034813805200b281d64440c2010020402642ea94103003102d59015481c0b800c0d0b8080e8060040c1c040304480301140041c1800e42414000c0c1502502d034034000030000d49140180070001000780a1090a01603602405038800200d080c2e180841c032280c0110a0526240c0f690344105207a0327042a00411160300c0c0c1d40c40742a0070640121503072400404100002c44244900c5440310340520800410901c0840003142c524000d400701c1c1e41c1c1ba80e10003084801100c4a000f01d0040e880c013001e0048115000034040e51080760043d00250501a040d540c0c1c005c01e80c10328248020800079030700b0006484074201c4c643c500e01503011804a8640e810b40c1800d8458565030b00700f588030781d4001c1209185101c01940c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 143931142 1250 143929892 143929909
    0x5091608121c1107031103120a020a17090d0212030c070609020d05060f0a0507030c020c062818091b0f030b0d110f040207050a03140409020406021f060b18 68
    0x1c0b803018080561101401103813a4455441540080c5441103002e80200d00071089440b000300260740e0742d13120384583c0841d0f40258030012030242031014100720003030076481a080741c40c4604400c030060513070756824950103070030701c0d03891040721020540400800a5a4034844180c0c0d0303030306802a6001030310301214070101d800003106280c040c06d01d01c550003c2100303070034901401d188501c0b106401404503407108041541a95442c034034800161b00403ca00c00c02c2400c0003c0500440503100d08541300b502180c0d4100a0f81100081e483c03000107003442200c29185912400400050100080800c40d544201d003000701417032017001d007a20402c002d80103243d103094801d8100409402c0010400a0f03103c046150650019007401c68190060004042090851505109407804950010080d008506c100da40031926120148420a100601400003240c403005c144058006048660001c1200e0305d001c00c03006c0c1ea040d80c034092042e809414024248480e80303180065514010a26100c4440d54909000154505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 143932392 1250 143931142 143931187
    0xc030b010e04020312031b090a030c062d050d020a0909020f04050a080106030f0803040f0501181a0103080414030709020703030501061205091207050a1202010509160812 74
    0x65988004140d07882081800342c05140700710300321490307810800e419034518002281c440b000d4101f034504105050860100508440d04010181941585c480d0303036010b1501010303007203440011040034aa00c2503030342c0f44203854903080c891803580002c2000342000610600c25001440200c680110300d6217101401407010b4009440414402c1d0b46074011038080700c000360014030955207c0c8054040010b085081842a003042c0c076000448140300d010603444080350350740050000caa400c1540c001040100b582881048610324000c1820301340c0c81c0d4030341400c3c864081840124048903030f1840c0100f0000d250f0038211411a01144204882110064006800d2145945c0034052170350000451408040d41070340079505030381481c2c40d85109594020100000c840040340c25480a5100141c1442d0440d01e500162003038622810444040b01281e41ea050a81414160f0080241c0c0d121801d1041d40744080c000243c5110308441900c0c400c9113401d0704903984185040448042c04070000754801d40d0703045410307041d426 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 143933642 1250 143932392 143932403
    0x1202090a03080a09060504230102120301030f0c06050c0c10020a0203100905060f041104020711040f05040c05060702030a06090512130504050c04061e0e042306030105010f030f0c03 79
    0xa00c0c1ea282081c2a469100d480880c1c00504840d00110317002d8022000d68081e10009403a9406449044400381e43d61040c4c4c1c1a0300381580316a040703246400604500450103180708040320712421840b8074044111140e2900f005042c490184040c0c2d802490004600001042c01c0740c3c1a6a540e05a0324160700b4510301da02c01035014003815890b1294041280c20914000c2d101c2c00844d000c2c0e5488260000c0c81041c140c41c01800118640c10340105464a500a090701a001da82a84103400c40d100c00982250380c140b003041c40312510741c4100320500c49501d852030010f100075180c0314580781c80742d07001170384451b4400360050100d55170b20010028446e0404c0400341041d01641c003c4d070741720712042811480405c1b80c0300c1c8511560400000540790007943c41603070100c0d905502c420f1903e1242400c03a13680c6010381da03003070310030030941ca03041c40925601e6000d50442007151a020602c140100078421264200090030309010340e0500004000700320b40c290491048a41280c08601d000d0524074041d03030340081d1584003601 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 143934892 1250 143933642 143933659
    0x40f0e03120f0903030f1012030c110303030601051b01090503070308150619081306060b121015201507111507030e0304120507061103070209040201120209 68
    0x146400000529103200200408403469450155032500c0100441d407801c51a041440410100c2401e500d101e90001c400c540f14840c05600d964450000ca010030700705800046c6102500400d000e22084e030005401c4064010b186103151100010b0460320604a1305107100360009840f1004000a42c09034060941c44020380781d2700d24003420000d080141c00c1d80c0d990b00e000c58102c5d506801d07284c40d00850301c507200100b0920208400c80c1c03000ba9010a0003d241a080c02c40c6504114000341c0540b25050250034100701903900c9800e0300303200070f00d509001031130500d038030040302c2c0c092080880074103004088640070300d0210101d000709402d400e01400c03980394400d55441060008103010381e007030030140d1184480fa43ca2201d509101c01c505659050405480c1d52032201e6400400d03584e6100360883d08100702c2c884116480c00b9034400711090150075400007910345810484092250340e601000d800c6c59883d082c00110b04062080d00040e00c59500640000c0c10f016415140001c80369181d010389468900c01812540c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 143936142 1250 143934892 143934911
    0xe03030d0f06080616021b01170406020a030c090803040302090c070b0903030a110703090501030b060f072001020a03020601050d0303090602070f06050c0c07030b0601031b0207080d080705090f040f 86
    0x40e00399401101042c4c001d140014040c14225000070f15060141e60007050812042411a542c1e200c03192801c604110300e01ca100741404180c0b108460069214482c0165995a241e00007800c45c1d4540f9005402c00c04010410406003c000003aa8152031301150030491940b1060a0b1400501c1000b500412420002080041a40002c0083c0d031241d8920744092207000149254450148500400100800e1a5810034004d42d4031950242000c0c24000e4213040c90884801048005504400021902c0034000f4880d202c1a840c078443e11952021700b800200401500360fa0042d403103010500405005901440c800024903220b60407405003a600070318119503401c2c903414040103200141030b00744da440781880041088080c1110444000801c0403010b0301c03c2608558070354400e10800782c40303641050b8a8105c8000c004800070a141020035140c0c0080030028644000a814090310f4040e040c18400d443e0700700851a0303007180854903400030480f84011110500703000980144400505924090301e41203540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 143937392 1250 143936142 143936171
    0xb0d06021206040b1305060f030a0510200d0c210b010f050c030706050402032b0206010503030a05040524030106022103010501170a0b100c0b0a1104060e03030d 70
    0x41c10309007888880080750b5a90b28061000b1383e0039150015030800211422801c0c002c5455001c240c200c54028010500602c82c04002460f00c48010001e440940124100030321b0900c0500c01d040140c0d100900419000a061a004940b40994034902000640b2200a01c0c03c0b9440380302000c1813465074622264003200712044c0ba2000300580c140310350215600e030b014400140d0145041e0340318000000011454101c140e43c440c400342401400403605032192440101c010040c0c1c1c2c40c5d40c0c3c03581000c00501421081c0e00000285010411390101c0d02a030010000c00324550b41c00000c503001d9440948440e03d42c81e9030040c07501c3d000340844031050700c03106000c4004a890b0358080b828441803e110081d03c9d040f11f41c00640c607001c2d40700c20f1041501081340030a0000e880e6410702950790b07002e4a0a44001414218040407440c43d00d50105500d00141505129404100d500211203401044031001000408444054a11a4400c900406040c03241009100c1c0c0240c0d0100304036842c184080109004c02c903580d1070b14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 143938642 1250 143937392 143937397
    0x5010503120a09030b01062111041404060306091202060109020304020a03110d061d0c0f030622060203070804031409011413090f05010518150f181e0a0b03070302130b0d0602 76
    0x340102e00c3c0c103008280c403140788d0f4021082143d496500207441c052500e0781c0c6407925034002d14100e41154030b0700400000b16030148070341d00c456405a15003010703181414030000e091410582195001510510030b2201585844c8844425254801c402008560210001540c0ba600a40c4010003841c140310101424296041c0c000010034010012904583c058408000b5503d280100c09601503002c0700c000303400d04802c0e01000c0d0885c0c1080c1c440030000041502c0b904140e034011148540070600d814180420594810710030904062882d0183e8100002800000d00306411843c0009000300c011520308000d20a50322068000d000d402410011038a5420010028001c2445068842c48030a040020700700700c42c029481c030984407000c0240030002c26100300000303010756102e4290005c0c9030808071034184610702905030050818262203400d00134406e00c1c2000180004181c4031400d8200980e5107200c0c0c600089403019a641280e4985072000310003812001001c0c14959240c1c800c040d240c4050600249500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 143939892 1250 143938642 143938667
    0x209040c0207050f0303040308030408180a0311310b030c0a29030c030109020705070b04181104080a020637110601050d03110c04050703020d0f05010503120a09030b0106 74
    0x100c4c40c040303140c02001c0549902440c0f202400702030040000600103030181008002c1807003074041d003d10030030030140490246d8400703410884020440c8000ea084a15000c001d1100e440b00e0b2f20302c402c1d44003032581d404c0d6402441258220510584070709103880190390500055003c920003910100c3d540d9640c07071030006101c2c0c00c044000070700c0b443c415107500144501412640300302800794405181da40384c0744440000754040401991103000343c54000c07401b0760740c00c0d0081c80200b200b95407034110328000945410446000304040c2e803c552040100300080c2d2404118150520f404446240e160101e59400d8845540105140703154604164401c56098440c21640c483c014225510307100c514003a0510303603070b90311001c1c00317a0359001e01084544e070002407280c00303240304041107d4207440c4601c0c1e0410108098803410340b16840071035004540b0321038000d407030311401c1c0306a80403480c14030a0707514203c00f00317465600340d0005170211240021b07006441401120313490000c5602a80c00c15042d07a4851004040320314021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 143941142 1250 143939892 143939899
    0x10b12030a1202090616080403020d06051617060f0a03020a0305011e020a020a0b1f0f0512030f2a060a05060906040510060f020c060f0a110d1707030209040c020705 72
    0x3840600d100790390b442a0f802105018054629040d100c40680e0402c0e05403000440721f0724010840480180c0310030002d943c0542c85500049001e09003d852545031300d0310b10480c0c100b080340c00b043d9450800c0a00415640019043c0e501e81039544014022500e420060b030070194101038040030003c20440c0543c000c00d900d002003031190542c00000c04024040c1c0c0302d0300c0b0406005a01080b10300700812145110150402c0400001c01040003410180c2c00d90205103a1026600c1c0c41000301c10042c5003481107a045070340d48010003071842c1140400e0465080d000782c140a03d107121461150305a1148042c03442051120711200311000c601e80303142c070360000d054111086405a400507011a12600f40360085a024650880304109003509058044504a40e19640c160461140c1c1c0b13500006a00c60800a1084104a0300c000c0c1d03840401c040c010309498800400c0030310540c0a50b900ca0080c03036121741d241c192400042c1c074103800c40c0c55988045010b40214080e00f64002d103040103c0390034503000511a011110180c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 143942392 1250 143941142 143941157
    0x80408120412030e0607060903031b1403010e040201110f031c06061215051806030f120a050a0521040b0108010516050903070b03040807060501081609020903010b12030a 74
    0xc40400e2041c1c000c9100e01000300180c541001c00180c020200064107040190401d82010000c1e01c40005030781f0204025408a41d0724000307405890142d2070b00c58138003903080c2414100c3e40321114002039544814480d00721000d4030303500401c045a11034071302420401c03124402c59a01c901b00540c0302c0c3d1250b000f160300400c032140105c5403040030611801054204c888d03540b01c00c4d4090301121081c0c1d002e015040c0442070440640324002c207181c4d503900c12649415100142d054110b1420f48203040ca441039010482d42103a10082400c0340f03d1440c01c04807900b01c2e503540b8180b0384442101e40305682038002c850381280d00000b40b015103c460960030500384d101e58000c1c14003000e2a43c1e03079503c1358226001540e104d031200301402c03411040e41e0300541c0148403d8001404441c20b1690324580701c1c03556081554221450034000451005110140c06001d014001e80c4000d40304500c132080003007030704195034401d201c940764000c03403940c5407a682075104040c2054090481494030b0103d003059600d80c4d0060000b2804503601 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 143943642 1250 143942392 143942413
    0x310050109030c030201051602120109050f0a0b07050705030c0d050705300c03070f050c10110705010815090c0415050405090a18050a050a0b0106020c010206010b25080408 75
    0x1d01c0603002141e4008240300d181e107045800441c0e60b07a004010f0704d092084030480120050315104800c520f11010240006040724aa28040b4244882c090fa0351400d54030060300c6402003028010900e40105040c01c00e04e944003002d107401401c50088650034860341c014500d88030116901f01c4010000d13103129205076480074125000155525003510542290300000d40c00c94000d002501006080b500300403030449080486d44d030707110b102d00c101005049032507400c0003a2100c101c1c1082900400e61400c14240368800403200c00700ea50b600c4145e48122030412100c40c0104041c0b501c0d010f007190300010003502c1c0e10818504007624044561181c420000d5140e6403200b62081e0500c01c10980b4244d6034018180600c0791202d05820340a807d0b5500d4811400e01c00d00744c0c210001710100701e212034507407051000c2c0c1040185401c0c1000c44000590200c1c0664120300c150b541d07a41c2e4082456415030704001000c540300c0c2c0c194102400214101075108062420303504081040c020007030090011129000100d5038179a01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 143944892 1250 143943642 143943647
    0x8030a1506031407030e0a02030105130c050a030b040b18010c02070f0f050303030a0c03020c030a030e01060501050c1c091806140d080d050901020f210604020307050a0e0a0f080303100501 82
    0x1c412200b01e0094403c0c07008160054030940003004420b100104481c2c2c0c2c0c5a00c2d030000783c00c440d802d03190204405803030200c1100700200005904002c05048400149441c0b4580342d03081c4c5000000c3c401845d80e00620700080c5841e584203104080d504030940200206000b558000e0744e90301182c06000882c5002c0e50700003034410000501c1c40242ca101038051411500c030034296001405c4010f1112083c56000e03c410038004100300064502c007080e84e9404244c2c840b85100441c2142e10366041a810408100070b1040d12600010724005c10700c00b65a444006440190400c440000458000d10303050780000c0307440d8984070b8071a04003405039510540c405110319056410021118480007005000240a1041151101a81d030140d0b85c0460300000240c6031602110466249134000250a80c106d4001500340e52505660340d82d450b844081500c0843c518101100c000c0e2031f9024451000c000c2050070492003443c2d440780e8000030010b240d000120b01900781ca400341541c60790822203010340009140c1034002050361 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 143946142 1250 143944892 143944901
    0x6030c0e240a06080603070819060b0a0528051509090906060306010501080711070303050703170f130305090904080304171c0e031e0a02010c03050402060a050306030a08030a150603 79
    0x21401020807200c145004415516210000d0640c6e03814001e441c00041c50040a00624041c2900310740390b05102d190610f0004200e8041d2420240103c00036581407100e40c44003042518020075116141002071a10100d074440380880b500840d4102625040860340305141c4070152105841c2210001210303074070307022140d40d2010b00700c0c1c240c1c5d410b078880c10040086500416801e90000ca4078649415640c1001c0085460610168011000500002245404d1580c001030032070b03130840c500415000340d0601ea0307040b81c61140c2c0900000d101c0c01a041c000e8003058042c000310341c0401d001816001c44c0d0301c1d003820070080b103420482e0240d800c0180324040c054070904c2601103540600642051035403800c15004003600800e83c1c103000869511041240800111003d00e111030b13040c5141d5401940d80020a60003407c1d13500b4029401d051604020038040180d44581c16200ea400107894400e07125a51a40001c1c58800e0700040940650300010a0121040740c036001210107510500448080c5940c405013201182c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 143947392 1250 143946142 143946211
    0x2414090405070501050703020f0111040914090606012a0615050306011a0d09020319060606030221040503130803040608060f010c0b0903040504020c010605030714090c0d06030c0e 78
    0x16040b0350340c2880658022030141a040d4000c0c4102e07170f85810007201c840e00719404c11f0803a1b01180030104080090f030034903010700c00e41c40c11143e103000120b090440c0001e5540001500d0305041c041403200000c0020661040c00280501d440c1d41c0d21f4600000e410110010407088180c140d51401220000c151070600040550407182c2c1001180401110030710807071791a40015103801a120307182c0b64041d015a408011000d0501d08141030762080408502d420400c5418690012041c140148808074a4809610b2805001c0d8480c082c081c102e5a62840c1aa042d88100603401d8004101c051010032000700001c00751056800340c3d250200c032500c035082006030341358030b003215140000e620300c043d800002c00040015801040c864100d0342000e0311440090180c0c3c00075a035003a880d0390f6440c41040b591608008080041c41c5144d9070221354102c4c4000f01c0d80c190002080420f0300000064041780710a02c2e640700c0e80c02903800035401c2030030a8507030074075100c2ca041c1076849100310f540c881c510580d03042000e100000c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 143948642 1250 143947392 143947403
    0x5010506030a0b15040e0a0e0f0c130b06040b070302060708041509030c0b0a0f0b0a050607080c0304050d0c050102160b03130f12020a0b070f0e011224140904 69
    0x440d03882800002c098444030541c0e40c1c00c964000f040c0b420403a403000140000c0e1520040c04502031801f002281c0c1211500c04100700c55a00c00c0b00c0801e40701c40c000c100c80c00406005e48682040b14103801e10764001d00000c5005540015000600040c80c800d01405000030300d21035420398409031580c060480b40a0f00c1520003802051010a000600407580ea1100044506c2820500c0d404041501c800780c04003800c68000300e915465060140368412240b280030004035040714465281c5007410080351250003184c80c01042caa100254070500c00701c04000fa10003d10700181b45060060a0b40341a124400c0d0910846015120300340040262441c0603003d10700766a2030102642c103559501120100300ca003c00820b1300c20800c05402c3d00b000c14140181006040c40c190020800c03400c040c81e05080c21300004107001c0c1005100002589a15400511501240000d281084043c0c4840400c0c0c002002e2001c00300c908811600d69050b45154084d0444040b50404448001c2480d841c03401e000202c0c130701b220001e28 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 143949892 1250 143948642 143948647
    0xf021807090b09010206161b030519020a050c09040f0f08132301081308040905060901080d02060f0601090e0403030c030507032a090b040b03041514130501022b06060305010506 77
    0x16010706800e1031821411700d000400e84528881c01c205100500c0001d03000100700040c248641079001d18a000202e00bc0c0c070082980404d51b85802c0c1d20341301d8502d141445454280017080900c2606103055810039004001d10603081c589260494442d805100008054660001d001450010392228510014800d94610408102550046500d01001000402100451102003000c21940c9002d03001800c0c00103000a81810103908022048105034440306507640100308980c40568049041908894418861030440d110880141c81d5081140c01556107900c00340c08100900d5450b8000b100c42c5812a24100515143e4100c21800d807400403218440b1f400318942c90003001c01220070102c0c2007031210329018000a0f1248002c0744140e0241d0300000d4100000f00900c800e0003810410007030a8a00f10904025405045410b1050341d5002050344800c1e84001e8454000e2040a404a8000003d01d025403680c021090000d00000d8681d4040c002e1118030784400030414501921130b80d4182d4800928060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 143951142 1250 143949892 143949901
    0x709140f0907020102132c1e150904060902210706050906070c0e0901050a140a020a0e06040f0e0c0a140a02070302030d090303031802010504060c0f021807090b09010206 74
    0x80107070050305040840d90308200307003c0744009151003c0050966a200607402900080c2c0001d03d03040c403c41d0306001d100400741030121404200c8203003050740d401c0a0401c403440d65280000c0d003c2103000c115141e0441c45000410042192941c08403842500c200c5000030006405180380409413560182003025038000002030103800d000f00050f0110180082601c0e1034140c0380c1e950041c408456510460159640d01d00384800c4520138020035071b0044246504008100315031042110300380014000c1401654000f84d112a0144a01c803408400100548860354032a5110b18000b460425882000c14241d9030401044010700b404040764075400041d95214955045d2a8120059a01180f40f0f1003d52040a00020043c0ca084c010f0013160001a00e070a44c0070340c0b0707505010b0181c409000503018200095944e02d80142c4c0c0201c203403820717285c0314a030640614440f4900395982c007a105801a51041c18452541621181030178400c0c031804840d581d17001440e80d41c042207901350280c01601805a008140000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 143952392 1250 143951142 143951149
    0x20601050f040905191b0608090a0201120b0a0b03160305090607030c020304090c18060f0f081003140a060c020f0d05090d061802040e0d05030c09030a0b010e0709140f 73
    0xe0522030050040c5c03402070000000d015003007258840d040b113806400c0348094900c08075201004000782458100a00640303007440116440d8515a50000d05010007900024800c0525610061030040003524004040e6141d01c3c40f01d007185c10444103032040c1c8d52a092181060352190103103078080d1103924014501611120b0090700900594543c030403c5100501002528603d80e0041000110380e580742e0400781c80c2e03000b030b00d02d071140310b81d0300301030180020a4440e40000b44d12181420030100949490340031900c0d4401d0005101400b5480030b84030455401e00305d121407402090b4058036500c41c40f010441042c4110081e038036504000a07580b000d4100d4001c0b81501d90241d001041064801001d400c9100300d04d543d0101100d46000001555080200105c011800c161251800701203000005060019600034001c0c01031100a18401585038081000e0050740c50412400b141d8075801180030a00350784034a03084807083c0048681d000040c3c68040c001501000d9040078031200000500001c20059105050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 143953642 1250 143952392 143952401
    0x1080a020d0b060d060501030c0507051c050c03130e0a0b0603010b0705010b09071112180103020c0106080a1a0c0a0c0b04020a0f06120e03030c0319020708040e010312020601050f04 79
    0x60200240c4404440307001d9510f800c020242511007450001d04603080000050444400c002c103d000c1c002d00300309074004501c0000d1000c407070f5032410070200804080c0303c0e012609401000c1e00c04c2203501c40803070303003040200708400c12505407904407240342c50030b175988495801038840303d20440f6042402040140a01d0240b00000c0030314500480000c210a0300b00d0000c550382c903900f100c2c844001505041c81032145042400000a11540d40a03818105680c481c0c29554034009030544906069000602c03400f041c0084d08080005c1c0b10b050f040d034aa0f07aa80d800c029140e4032600310f00c001084200c02c00074166039060002d58418041c030395900c400143d025501c1e01d80100300540142c2e0f100900c98400100c89214402c3d40e405840c0e07035524aa24068040c00a034150f03013201c006040550000d000300901c0b0b400100c10340f80e0003182e41c454005201340c4040510001d105a00000d40b0b080000200410b18052100003281248c1c0b2481503800320151101003207860b00020b018166100808002075022864103401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 143954892 1250 143953642 143953657
    0x914070504150c0b100602060703050c04060e01020a05060c03010e18031801030e2b0e0306040b070c050303011214011418070803071202070e010303050409020a11010e010b1c0201080a02 81
    0xc00c00b41c3c2400da921200054281107a11000280b281c14003800202da05010081e00075506040a00080c1004441c407100c9000d21b016010412101598140035a8805c204500e02e05410400760348031828400e0740980c00394024007650081032441d1010403400f11220702c41480e098107101c0598105810740d50500e15040034075080d141095221801000709683c103202d14038000801100da107010101880850700955031141ca110103001606a50070002d0320007140455200f98030102c1c0074040c3d80d48000660304040380b178402502074030022001282002040f0000d89105002c0c420078984104410000e5081c1c82d00106080c60b00b4103803402007002402d0003000c0c400c104032848103880d159926220b4a504d190003080301582c41d0016500305040283e0140403240c0680150303040940c2540c1951405003030780c80ac40c81020038203940080c4c8040541d11803500c0c2843c4105040007401519a41c1608501900c004900a480f4440110410740c070380245800d0140002e5040c1c54400c49607882c007001d000203400c6140b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 143956142 1250 143954892 143954897
    0x60103150218031501060306290d090807050f0606060c1c020708030c0109020a090903050a0f020c041d011b1b060609090b0414030403150b0d050313091407050415 71
    0x4110b002660148103144a44c081045080f100390f00d0520020191081948101c0e032054404455845a40280d01d544080e4040c1c03807041c65450001c0c0c81c041c00144441407014141e40004290f40c410402c0104080f0012035403401211099102c030320400c20240b180101c0c1e000658040403244021107031040615005802600569004a50300c00e8164216131184a10300c101e44d41d100544801c620b040e1010364080d000c00b0900300b040298542c3c01074554824001c2003801d015080c81c0c00e1030181c0c401c0221411200002e0011701481ca24906250048280c070800440c5075400d140c0603098840d6064501406c20030560790720000408a54100b550b0311301040e034103440c02512203070007164010160288038401ca21964040d41c5618050401c0e4443c042d0203109000b0302e8108010420100b65611035080308410a0000000e0703900708000003e0b80c943d85520014001d00001c0307149070107480c3d50301c0305c0011541c0d40403052040c04901416410040f0003154aa80400c2c0184000c0c0003d252262510702c03035584a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 143957392 1250 143956142 143956177
    0x804050c03070801020901020609010c02060609040f02040903050c010506040b09060f060d14061305010501020703110d05061810050f01060c15020c0309130207020d02060a030605060d020a0306080601031502 90
    0x40d0082410a241074210a03542c1e0b4001880c0200c9503030400c2515841f0540d138008018041d000302c0000e41382c2e2409403045110340da901000c101484818070911201d698010002c10100c2d45614002d8180d42100007510a15480c7c07100003455420940510a8044401044002250748401c00c00408040d40241d00f50020810b00c034800e0800024800c101a42d043c2180b040302900e002006c1141c0d40700b0500b02d00e04080e00303081c010007035641c00003610411707039520012030a5940000c40104203030900f01e29020741584a25001d010340704560f140b036000080e0f00741d420343c0c80ea80300300b0482800780c03002582d034102040c803c1c0004015152080b0480032400c0d11801c1024110a2a03803065400c1ea00000390b21240c0d900005a180024908248010001d90406d007043d4100191a000a8140aa0410081d000d2280041e030b044031144240d2201021341f40040c80141c0f180208401c02000b500002200709c040392416002043c4000d000808a04a95109100454101e03030b9074016030194200c2c0065080f44180c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 143958642 1250 143957392 143957413
    0x70203062d01080f06011a0316051c0c08090a050717030427050124180f0b0d150e070e0f0901030b040c0509100501030908090a080303010315020a050901080405 70
    0x2107414160003050b64500801032800003540702814901c043e4444100e4100c0e04d68200000407001060307a03408100240403540003507010800340c406100700c80c40e00b2020010484603c81c140f107258051a1080c4050f50340280c00e940c0c101417180d64011101300178003158411801040010304907109122030030800030541e130810780e4843d683c02c6154568041c1a080b001c40c0e48640d5100203003445004d004041502041c420008401002c0110308030075081034003003000b90810000441d00300b1184c180108040003203800966039900c0708903140e8110211011003142094040b500301c01440c42050180d0311b080d607201d03500c0d881d1018140e83c0c03031030744117076032600000c2041c0c03030002c0760360f0765a50b8a000f14000d80c0d28001a16061600104900300b54001500c941d20020500c0010a1131f0182481694801e0800241d03502c202d00303110740d00b40141800740364442d0031072001040212020010b18100c070310400c0c48180746002d04030902e003a030050340c005c00c00055003032115080c41d41c410035040d41c120b03010301c0994190001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 143959892 1250 143958642 143958721
    0x106140919050c0a03050a05040b0402060d090506070306080114011a1608031501031503050c04020a02030c0109080406170103030519030b0301050901020a021204120615080a0c03020a0b07020306 85
    0xb00f00c500f0520b04101180720301515806005040e4403180560082005150030742e02c446070007001a0020380552004291042c42c04600d038414001283c000080f21200c0c03904220007805009c081c06455001d50030000400a001d200140241c182c03003005100b4000c031240705503c282103400c109405042c0c580007540c508007144014000b14003603144a10b0103440005a00005001d5030006004090007514180040004c81c2011800c400000b004075000b59645012440891440c0507003a690003455180078503a104000d004801002211481c2d140c029000414618954111600348800380101d01c04109185d0f0058540003014190160350600068401803040801c0c00c649003155040c140f60740c00a940701c20290108008401c0c80729103081d2a01e02170401c41c0d08548184292002800145c8030360382c01880800c1c084008000c0c011441c1103c00040890401c11400b40031f40c8020b9018640401012030846140b200300c0300100c0e00a40140301c50341303032928200034460117403401c5142c0c40c8005400460300403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 143961142 1250 143959892 143959901
    0x1c030209061903090c08060f0a021c060b030105010212040b040b070c0b130311040204030203031207020a120801061d18040c0b04080703150b0a140a090e0610080106140919 75
    0x1010b558000802a030645401d640c0c283d1036030050f5026910040402c100711342103140d401d0384403c801d100988c4603242c020401803440348200408120506004000c528452b00902440c100c8800342d085030070003c1e03c0680710380c02d03204a02554400c01c20801c0140100d41c1d50700c0051010074414840380b02010b5454945200a4024140c1058008032210b002c00912150041c0c027402a001242c0462038a486c65000a50700d02c1100380c440e4a4800c000005200380e0300070711a80e41000d820010740c034200c440700c10b40100038207400d0050001052a40c1d03076000301200f5080e040280850701624807000f0b194401d4022002040c0140300f140c2c8400181004200a5280d401500007004207800408885066181c242100400020b01c1040300303241000d1a51a036440550b032804890441c1e180500a1011401103046040351360042c03080300d41800602c1502280010340c1d10700c19044045450020358540940c582039410600c54001e4080f40400405042d107801454913401a000c41c20321403014203608030b0041644c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 143962392 1250 143961142 143961187
    0x7081003170f0a02160e090a020103050901060506190f26091c03060302040b0405100b0a03060801050f010323031e0415020d08070903210507020d050c0109081c03020906 74
    0x5800059030017141200d0124034201404040c800340440e842c3c0358502c140c1d00c4100d0032019042648581c007264440b107080d030090002c5d0002404c1150781e00e01c8070080c00d1101107408100710000300940040e415441c81003400c0c400344500741c1e440008442d4004012070320210050300c0c0c090070780603681c0c1d400c03201c01d90440c6510000040b9203010500301e2540c0108021940b00c03c031424000e40c144410440c0b285250491807003601e0041041c19103510068004600400740780d00504000d610f04070031b02c0854800594554100c80c412240040d41980f01c000300100072101e8004000654014003014901880c00d0301e208201101d004452810295101034108039441380c002c011001d40c1202c03144d012441e41c09201c1d281e01031501d04000f2100d62556907001c0e070142c0c03080c0c41002d0f100980803801d9540e83c0300ea8102e0b500380343c004203198503001135410710301d0f1202010010a0301050141400051171200403030700d00d02211a074110039481d5102d914054000c0d601c850351036503100d10200214030381d10103071039400c1344007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 143963642 1250 143962392 143962397
    0x507210207080f010501080a0201180b0406081501020d120f24061e02030405010c030c0f050f0c031b0409020a0b0c0106210f260a080f07081003170f0a 66
    0x103a00d0310381d0b00760402c5910342c01c14000364108401404000000940c1d10340d00c5a0a180190103904c0c040c1e20011040c034160042c488070000010005010303a0f100306554051504240380c00c1100c4a1000160303604c1100d0502000420b952940f410f000e500d159102c4100030f414201d010034812000b0386480500300c525441c04c2e8850318807a80034000b9075400b000d080d09902002503400d4444640c000b0113940c0307000380d100702c3d4100b200f1805a0f10403d031085945071070b01940001d07807072110011464110345400d50548125038030f20801d500b41d000c910300012400d0240300705408072090140f070901440060041c5210076a08208a104006080c0e65075100030285c88601000000303c0508100035814a903c4048003900024102000d43c0c004c51200e40d541c1000c950701c40c00c0c1d03500c8800c0840a0311180d005601c041c0d0504800030034440c076001d401c0003100d4480c10b03034400c042050707a072205002d40f61030505440b004007589010105000103141c0c0c07502d8841212103588801c2c1840e002402c0100c00b50f000c400701d02c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 143964892 1250 143963642 143963653
    0x7110c0d03170906010501120e160602010b030f19060e0c0d080a0f0203030f0c2d0403050601091406060a03020d020412030e010207060806040903090f0306061a0a08010605072102 78
    0x2200b4402425003104800000e4040c03545071800003095148140d40e100b1035a540c03080304040300341e010807142c60a011030064100c910303555100c000e030080c06807071071040c024050f41c1d80304d285007100070035804400c4608450700c140e14107030760701d03000000c0a0000844085d4407811002c41590343d24010440381c071610440140ba80c0e0010402c005081c02c501600f42e10940d4018011301c1011110f00c1c4031658800c512014107510f0b00c42c816090340d003541d52860101041d0514201c1140718140000c0184240c1340600c0841301203036030390300c00a400c0b9040c10f440002e002d004500890203d00d0203a00810904d8100c0c0360141c00c1c010341903900c2c03040303a20607800f01721080341015180003010340140c041007450030700b400500304a51900b000500f29a4008010b0380c03085a980ca03000003014010806400a8071f403140c0142041500c900d0300310004c2c520340c01660b2641e0400d102d80245d40381400f0898112019580c2c0d940c0e06a403130800709840681001004460005072401803184507407580c0400e80640e02d1542c018107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 143966142 1250 143964892 143964917
    0x1090c090207050f06040b1303020c0d0602030a0e0c10050c2e0506030d080f1b03040b0106091719080d0213030b0c0702150d020c0d03020c0712030807110c0d03 70
    0x40c076007440c3c2040000030350000010440400c0000303002036840000b2041040318aa1236141c1242440205d0f0444c0361f20801c40d0286c2c0f030511085078080c620404114108000c00b00c0c039072854583d140c110400c00356102500d0395918541030f100340040e00d89048a1000c03268040c0c1000c10f10030704c1550456041c4080002ca1624080e500100d01586400c03007401e50207004081c104010003001407200030404000d2180507030108503100c42d04c00812441c51070040505889080c5071810304038030b50082c170412000a01c0b40d08046540c144410780b11008129242c0105007410020101e03004103103003584c0684440c182400a441e80307010ba40000c0c903050400c088604031f40ca0031440c16494035200506400e4118400340500ca0040e11595564065400c5a80d595a100d03881d0503031a0010344200211071200e4050b44440741e840030740680190458007080425a601c0b60748510b8091080b0b9500c180150029100c1c201107000d641c01030040e41403004007036040d68030015070b81e40440e420481000341100091003070f41002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 143967392 1250 143966142 143966153
    0x1e15020120090612040201020f030d0f05011e140a0f08010509010f05010807051c0203010212250504050d06060b0307091701050601020c100225052e030e01090c090207 73
    0x91001c4214489039420858440b003ca240d50082000c0720400d01d01c074101007070640e8000c010080d202c036806012603a4070080000d8520103801c0e030540031b5a080e81400c0c008a542c807420449601e5450341414110f81d090f2401d40c0f01a00f04074002002904481c40450101d11412074600400240001200200b00381c106a860142114001d10494445c0c0c0e25080052003414004145402102c46c1102ca05403140e080c4401044403100204000f0760540c40000c0c0c8540f0341840700a940d02c2000440d00f803280c901c3c01250480ca81840c805081000aa0204024001c0f440d190081c40e00c01d13402002c00060f61601d400b44400243e1040c1c540c14049076100f441009003002141c03001e00328400ca01d000f44401c0c24100000b030341d01d1495a812600c254002141071100c14820490400c0c5900c0c0d06084014504080758002e107015010301405000b5140c403580211846c5100941555403000010400d42d168017149044008020890341d05065540360485580801c6411310380c58041c1c101000b0040c1c2c0e42e40b452030070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 143968642 1250 143967392 143967431
    0x6180606080c0102280201030b090a05010f0803031306180c0f080c010306080705090408190503060f040e060f0a0906021201140d0305040308090619020c0f191e150201 73
    0x42c141154070074030091484210f650f8415200180c075034004018440b0078030058001d4010540700d107030080400000c01030001e1003074004504840d403904400305c000d91a0146c00d9282d100c1290104680107800b8003140000d00190700248041c40c0c0381c100c2d000c4461746076507104420b81d1254042c1240301c4607510103022003079050000d00b10360700c0c007420b01304075040c90000510748440203031195a11076a05840014284031010044403c00384074107092001c540915030015095030800d40e0300f140210390a04690f541424144222080e118446000f81095035503603034003a1414000a1044408640b10311b80e8100064240c005080f1440c00d01801a40e04d40c10901003030104024229568465100184840d011a4111003183d0660350400761542d035500d100d0000c40d41511900c5006d40080021180e55a029030340498420503003030040b40c1002c1d0f40d40a00f000c10541a601a49605c10307014201010054000301c001009070400c082948805030b2965a102c4003039055400e0841b00c09130f51908500c1580706481e00d00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 143969892 1250 143968642 143968663
    0x60506010806060c0604060b031c09090c03090503031303141305030f0304030b010605030c0f030a0f0516090905090a0c170607170103110f060a05120a02070305070308040618060608 79
    0x118103043ca5103184c1140d9840c4000b40024083c035507281e4840d90617860500448800f1101d580d4088490781c40810700500030710700c1e4450aa401e624184105041911038001c0180c82d51b0000000c0d411030300e500080d00113103240603400700c06201c800005a51050b001c0c10103001055402451a04054600300c24141000310b01404c0c01c07007581040000b48001820420664103581c0a46012a101d50300d02c42c87d10442d01c203419000d6401070000c410000f2612242e0018004681180320501540e110b541c1d070101e40364004160301003c45c000f1001880029043d80c400c90b8041c603184221400c40d10262070342078000020b0380040c05254031542403514244001c1101c50b0708074080c0d07d898290b0024031040c03403c40d448180001015440c4c140e00300c810310f5503585e04030ba00d4048014410350343c2e590310000c0604540d0146500650596039440012080d64842c4266178540703426440e120300e40300d000c2c2d400f00c0c0e8195000b0000c54001d55a01d0301c1078646020b00d41d040114070f01c54500003500604103410306141000b0b520 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 143971142 1250 143969892 143969899
    0x306010201320112020d030807020a02130519060b0d0c0c02130b2701060503040f051b0a09020906030a0b2101150e06010909050a02040909080d06050303030708040b070903020d060506010806 83
    0x2881c4d0006860341c101c8185915090f01c0d15850315103070914200e0409600c03130400781d807141281480c0301ca80c3c19554003103401501013030710400f0300c82d5107070030000107440841c40341d1101007c051008201285850700a82c00f039000c3e03440c041c1c5c00d9101590008065070301010b660680a42e640300700d1a0a0306111103c0c0c5100c180c40320000c1d808001c000c030741c824201d005000b214100034001c00802d08009c10082d568141d04da008060712070b035001440547d00d0100721005036034401d0080e0f0000140741c201600c2165014032014162601c1e41d903420407940c003e030a940c022150080f83e03180d10402d203801d190152890032a040320021483c91403150b0312443c0001d0381e4010903e050f4064061042c0340e038004120f101190394044001c2065512031070004000d000d03540c400c001c41410900e184c3c04001568000301040301952808000158490090554a0008a8144d4007164641d80450301181c41e01100300e910000501d001040503449130f0200d4080e03840c11204550b01038075074040c80055a007120000c0d50000055 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 143972392 1250 143971142 143971169
    0xf01050a03080d091a0f04020a170606040b0102030702030f031206091302010309110411070203060f01060f1107030f080306090c0a050a0503101203110f010204050a0b03060102013201 80
    0x15150700082d84078400c21054607695640b1104108180780c0ea00782520082c0c03000300002c42c90052902045404105c0d4101d1140309584404140e54500c42c101d80168000d00004281d590380c0e600c280001416900603190641c4414006900146e0303007042807d00d200d80d0007000d5900e42010181c115074204026010364865000c1c101040003440c1d0100d40301c030715a502442c010600000742c0c02c1800681c0c134415582604030b41000400200b4105840091100c41d109408a418503600c181c011b409402d402e00402c400501e9151100d01620b203e0805441c5041d8400d042d03404482d56540d402a48007201d0804076440c200100420a05140a0501a62241100c01c40360328000001500403d03074800e0b8042c0b1400d201c804000701d48195445001480500120448145040e07141d08003e480469100204001e5100d148200c884802046c001d070b6049840c0a0203032000c1d1b90034150054600c0e000100054115942c400310006002b0b129010050038001a403070345201802c0d2403400d0301c1c0104d0305030000060308001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 143973642 1250 143972392 143972399
    0xb0d05010b090f060313082a0601080c060f0c07090603031209030203041e030501050405031306021212090f0601150f08011a160f0312050105030c09010920070b0f01050a 74
    0x640840c51001d440c02c940041c0e4a68640d03d8060000081d6900502500390200b5400e940d242c901e011401c0c0324807003942c40b003009034a05107100e89c0c982007401074100e1500318422109050520708090080160050f00450820301908211840e00200d0b600c40861240c0b2002c040007410f0704202c0800c4200c0031404240b05800131038030081d68a100d1441a0301c0100030a0320404200c8100c01c5100014507031000c0240715505187c1401c9690341c10510714a0f0000b01c5070311000032901e0000415011f4442c983c0700050a110100850311a800c40041401105000d190300c141d107440f400b8402e00d806042d000107032a507030390b083c00c90003010100c241c1e141c041400501d40040c06071000224071004002500305201e4be48040130340701e07000801010080240641081c0c10503a08141d0055081e02241104c90410092607070f98104043c0d0b51100010b08136000354880006122210684c1c10844c1c008051901c500c18440030201c440c906030b8407000c001c1d60300d003203400d040c40140c0c00e0007071400d030050000b12900b0580c02e08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 143974892 1250 143973642 143973649
    0x307030501061220030601170901023403120204030614011a1c09020103060302060a09150804020d0b150a030305070b060d0503040e070e090405030714010c1b050f06010b0d05010b09 79
    0x107200283c0c809204d00440050707904c0e8464490814103e0144e03648074003900703090341351501079001040c3e28400704e60f010300c00700401110315400c00c100410f01010184410180c3c1c170161420800d481900c03001703d07002c020110129000b402104154046400300072099850560544058243c0030202010641e0400030500d41e10300340300f0f4000c8050144070300020001021b10050300104103070381c802900a4008079204401e65000320401003203940b407045590703003140402e100303c5d50034404490095000000040c11004900184802c0c1d038400c00c1c4841039074054035051300241f03002445074000c030005080050342c203040001c4280e103103030040310582e1444141c0115648603500da000754020304c04900019000260321038460800c00e1210700e40a0042c41080c206402e1083c0c90703074805c00040d140910301c4042e11100190520400703180310b0840da00c12100d981c01d884481d50101c203040d002d40355441100f40c0317080d4010042c40100c2c003c082c0d420000d565a8040d088070340583d5016401141e5115040c00036010985 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 143976142 1250 143974892 143974931
    0x1d120609100e0d0e0307081516020c062b0501080c0f09010602060c1e0a120515010509130b10030903020f060403050a110f0a03110114090a170d0203070305010612 71
    0x2e10f18140b5807407600c00d21012900d00340d6030b507200403140e1050038500e600340702005086074040c1400182c200b062501001d41030740d60b0b248189a8a8200d10100010800010f54542200405c04101c0e11102d20907030105005060301c0080e081080d254002801c812a01e25003a1904800101e080d1000c84040d0304d020000f030b4803500001c094200034100001d142c207200b0917099807030010000701c60540c0c1d00da0b00b02600003481c030511409140340e60352419000c510300300507411903070486104c16582c6515102914003405a0441f80da051006040d840b5550098203076501a609900403c095800144100450400034175210403d480780c0d40f80d410003014403011992100880390260610b04010711001680204549030107480c0e9120101806411110420154804001800360402000070b01811018203500307410b0107801c0d5141e80300750348851503810000e541071034a88504815030140e03604065040c0c0ca201d060740c2c0105c80ba940020398803030051001d50703045419803c904889003010000c100340c1461900340750 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 143977392 1250 143976142 143976163
    0x10618080c0a0510050c070308040303030f0b100f0507020d0f0c0e0c180a05060a090e0702011e050408040302090a020a0201060b120402040e1002180a0602010c0903031d120609100e 79
    0x203413a0802025401d5004408a5101000701022035803080c5c4d990a01410300d400c84d000c00c40000b402c00305944112602400b528482403c01031100d0500000b006094a2070103612921000340502880300704d0150380c41411401e00c260041c0c1c68a9021110b5203803000545107070790841070200c1544030034803900305421400e5407030406030303034020f00c010310b00010010b1420507083e13020070382c050b20000310000d041ea4440710180444403d0004800c040d01c0d200d03001c1c0e00b81e03880100c3c80651b45d0507480301c000252089800658000f806140c51600d01510388e004503c44a400700e030039642894001a04000440d82489110010044100100d003440c5203080d031640c040001030030203440741d03807035817000c8001e54000d0012040030300c011001150350f0080c0c0c0728140107822102c003d1600c50001d6260002e60310b8018000c1010300c06c210794134034030700e6030940d90b00b680d01424a102da03681c0c41032030602c441000e40710240d01002040d49070004050314501000114500411444200603d90410702c6a1a84180001d644c080c0c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 143978642 1250 143977392 143977399
    0x80114090312060303070f0f0308010906080a170409091406070905091306060e1f0e070c080a050904140906180606010e030f0304060806010f0f02100906090209010618080c0a05 77
    0x3c0c1c450380006440d50080c800080c005c80d1014500c0020004041284a281c510a40300e07030703031103aa0b50708144046640606c507036181908400c00c01d900180d081400345400c03509445840c3e04254844e0324180c221903d980081b14103048980c124901c80327104000880d88010540b9102c4043c41c1000c0101c0c000c030001030300510100d0520042d0004010460300950094102501d03182c0a0f4900740070b40741403000ba058001240d070413603208042182440c400000d841f80074243c842d482d113000c803695404256031103d6007003402c01c203050080c0c858913a154002d130351041d02015001d00c1c007420050142414284050101e81180001d40480ca00241c804501e2a074400d6090800c110204807030000301e4108551180540f2031800002008506250026600380c002c5e0401c1e80c07200304041500000782d4490524105a001680c04111208558641d681141001d244140d0000c1161042039001c85d086403000c4e00601d010403880e41a03038804206003405040100203080051248660803030100d68055500d0240600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 143979892 1250 143978642 143978677
    0x30d09030507150b210c010509030a08130e060603040c09110d060905010923150d12020f010506030c0109030204020f040302030a060603030e10020d181a040801140903 73
    0x51502480c190b90500c1c0e0030051031028809110b41480c010402e43c2d180d81d109443c90b010b40e1000380d4a684150f895400d554004205014103100199096008207000302d034148208070841d000124180e0103814400c060f0030400c07101d2414480104030300600100102c0c00380105004010103d07e01071040000c403045004000f4480c4102c0d00ea01d1410f11030000c510b0b0b807040c101f5000203405000d81d031016040700c00100041050a280c0c085101c0c04450780c0c0384840070450b000c804540d0540040d41d003800c240e80014806045c03234045a550310b44c0c4462484550700541c010036140ca061201c01e01906d0f9011000b02c0150030000400b00000e04100000d01020380180d5012401c85040b0200d0001c480c051500103080352032500481c50004041c00301800201d0002e0b00ca4031041c40c25040c24114a06480f4241c1c010702071070100480708079150211220303a002800340522000604071201c007104e800104034041483d80c0e46041440282c02d4400d180141d614800c00102081031200001c010b80d001c0344a54060740c0b9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 143981142 1250 143979892 143979911
    0x1170703020405101d0402030c03010e0703020d140609061507030305090309040905030d0b0a03080405010f0212030901091b3206270f1c0302030408060702160e09030d 73
    0x40c02801a41c0140d900103503407001040c503142d08076024002034040c115010302c4595414044c84107134002550001114001032006102c4031120380b0405038040d6803440c00608024400024006036240c82c1c3c091000d082e82a81441482d04198920650199094030a0041c1c450241c1e22543c4d1b511440740c0c094201955280800d5500c2400d0040301c10b9150000c1c4140010b4809061854880d489050750b0081d091401e0541c60b0719040c0031448200f165000342090341414505001992803862520000b003c501903c00b44a41c002e01c00005140181154000050004500c0c6460010580320764a002c5070510303800750403c02504408407281c07160402100074041e450a40320001b10440035421800e6000c2400f01c0c402e05407199441000701890f22805240c507030003188500340008030700d0541c83d241e085022509021b2210b40314000642c2e540344203104481c9040c0e642d80c0c0950401700c1c103513142d0006030000e8284c81040d4000400d42c1c40a040c141541840d01d05040d80c1c92035483c401c100c011800b880c3c6516114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 143982392 1250 143981142 143981147
    0xa05190903111222060212070f020a0e0a11091f110102030106020312061905040b06120108010e25050906040207121116050303033105011401050f011707 67
    0x824a44042c5811038401d00e01c0c408402840d50480744a90040c0030200c1c509541c0c4403000c86820046900719000392100b002180506100c0b0750080e0419a110710b058070b0580b0042e210001650014907a0030141e056909014900c00280c03103909064442c209001d1101c024240e4a0b03506940140010081a03840c0031601c080030358400803212810645940b011000003061f68000c070081544c1400d840c0d01c28900d6031081c0420007040200e4114080d03c03022528240141d08180d8410140f0b030790000e080b1401c00c1d41d01c284402d02084241c100030496515420b8125600500b000400c0d0b00c60f000420070300001c0d003698904aaa0352092058500c2040d00750082400d544a90341290080c90b00104214180f10f4008400b803c8603907038440e800d8952140b200b982c1a0131344880190420303913400902461858440182c0c228101c0030300d094140010305491080c3d810000850110701c40304c1d00c140004111000340c0365075a800344805034800b03806100c2c1d00c5c44404803607a0101d001da82d20f1013032100206494407240d104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 143983642 1250 143982392 143982407
    0x14060d05010603050313090b01050a0c110a050d030905040b04020c0a060504110d140f030307020304090f0f06031b0506040f050603270703020a0906060c12050d150801050a05190903 79
    0xa131140c0000242001075219010300001941c0801c0c0c4280911860200111030500c1a1104a40060740e56603c4400007154070324100b000c40780c014844110503468500240d0ba50510400032400305103805400c20040c00d0034081c284800c20300315800c41c1003070941e40a260312a03241042c010001d5658100007002c000154130800c0900101034403c1c2c10000241c80c0040d905080324542d92220b100e80d091507801c0350350000440784500d46a5025500741841c0000b400042e00404600880181d11029045a959168880c4038005d40c003c460110031043d00c0304100581c46a01e1700054024103042100740101c00041c230740c0104070b030b00076034210f07503259212616010940003d21241c0c002400021100c03022290000c0d0560549000302c400003e07860751920b00c4011610319110300340c0450141014500403c6014242400905170f5060041c54460400c1e803c50844089122002450f6580030341441510403d100b0300360f001d1859002044907003084881ca0741c3e0180d4072074004030a1501d5403001c000b0144a11103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 143984892 1250 143983642 143983649
    0xf03030f06090903080906060303041406220f0b07030e0d11041418030315060307022b03060e04020312090f040516030b01020d23040e070906030f14060d050106 70
    0x301004896210314401001d40a940402c0d400105090007003488884c0224070340780102c40003401540741604d45900d5012209401c04c1040d13208205110000d6035041822105034070005802e1803a0640303050010b5076003500300a4014100d034050038051100080d0300512448111242190100c0b00302842d490f100102025044186400906024804130714040355103099000b007014100303000f00480c0720b20425549020864a0b0104000500300d0b0b044c46080070300046070841490720550b5041403441d04500814080c02c00f0151040c0760510a0740401541845079001034400d8840780546403c007900000d980303800c400c5900c117112200040e010110381d039580c2040070014025000340310f0f92500c0080242c055000a51910200b4201040e00005600c080b410f40114081c07030b01c40300481c1400040c1004c100b0021010980b0320501040013050240380012054402c10890740c50122240c1000001002d849408901050700d13800c10710904807000402c042c4990100040d00c165000030303442c0c14071034050989a070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 143986142 1250 143984892 143984921
    0x50f0c01020a090504050106030e0a0b0705131409061f1404150905040f140f071b1101110d21090803040f0c0b0f1602040605090c0c01050c04120f0303 66
    0x1010b00500e034200c610842112000c9404120903039880c0000e50035100c1c00192081e031a00407801e000000f40325008601d8011186c1d00e812814401c20a0181c0d510b501190802202041c450300c034414140f0b01065110b500c08016980507210408094407605001164078410060251000314a051986150156802018681509001038118030005060803042c1c0c003400d40214100031115a021b000c40c024203140c0c440040e0700302400c1e9150307003d110226030301900d01d13000c211103184440c2030505129841c0c28828050303d1401c461140d12000034100b0405000e440303515402502c00c0d82481e6400c004041c12085e1800d00742091711120250a0000f841d543c03100030b088002c0402072005120079000020425440f400d405400b6039141c4454a44c01d0042c8a5004081d940030010200e01c0105802d902804510142c004201302e5200c0d400580d83c40030894070040b101801058100d16a6400d0058a4008401e001081e151604000d0b040450040c0326402a0000d000245a50201886980400002400403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 143987392 1250 143986142 143986147
    0x70507320615030105090c03121c02210906161803050d08091e060103140f0d210501031707170403050c01030c020c010c0b0702030d0212060316030f03050f0c0102 71
    0x14544400140144002c541c041e610301000a0150b6030002020700110307200600502062800490003640c80c0c2c0001c003240222125009a1301d901e07032103800900400405020340c0d4045038038424008230b9000700100001403540c440c40a019480c21504e0350300f07528a000d440c040d011103810310005020701000b50300040c010312400c601d0700c0a80f54400c070101d0152000d4000ea0399488001282448034040c408a24440790300204010400503444e2041c01c000c6010aa0a4440d5070040c48009803e14114241c5a00480c030f0070215001c1524224140c074a07140504070041005506680f10350041e111004072080b240c91002401c0300074000010148448c480041155a035140d072245003142d01c075800224070074042800c04199001e8180082020035400c1c0040e9168031403980140c50381141c440016040c1d00541c042040314049000a6000500d03004405110100c52030030709a0a06141050b540c00d80f10400702c000c4c01c06d100013001c110142c8542c9402d45400e6888944922000c6814415040c8403544c56100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 143988642 1250 143987392 143987401
    0x12010303050c12040f150c08040608130206120709080102040305030319090c0b0703030c110d0c0804080d0c0b01080703030f110111030f0a0501050103060f060c1106030c0706050705073206 82
    0x120803021700780c4201c0544c1c4802100e07a03030800c0e6204000003100500b40c410901c81840218880c45035260b21034811041040c8244094000c55000d0b40705c2d100100c0b9500007a001c0150464128100c0802000d881c8000c40c80c1c245142c66080d01c0340006001c04000c5aa9a11a0640d03040a500300c01e41c0c6d5508024446001641c85080b012a5400100b08030040b80c18410580c08040c000d604803226080d00101034040811994411921000c8149003210065800d010108288400300314403600c001442c0c176511041d61031800c01c02204a41644140e050390302084040c00002e50142c136601c4615004d060000794807004032011405040c2000c3c48c4c01320b03150088104008203031140307443c90141d00d1008040005036221401102601c0642c05600221210740f1420003403580b207003104000d803e0151800400c2000c810b800258964030a80d212000b54001084202c14000544284c942041d1942803103464000c4551300c0100010007150203580d16641015203860b226107928003204100003140948410303250 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 143989892 1250 143988642 143988659
    0xf1104060b0309100203060906130f06060203180402161709040906051602060403080601050c01060f0b04080d0c020a14061903020c0c092a0409060b1c0212010303050c1204 75
    0x111143e00040c494404910382c2010644212801500c003c2c240201994450050008441c800040c03100fa06541d0041d02080c0301c4c0034842c01014000c0d40d4007031a540d01d0242620292025920000d921a80c81004814846603000101000b801e40c0f1050440f18999400e40c19203540c06240342c5181c001d414102c0703030700410910340c2c0b0641c0700b1100000d655015054020040740c6d0b840c1c046500801041d424004212150301480240010b806982d0010440c2a2100d042d0120a5410361010310706c0b400100301401140c2040c055291025001d02c3c01e03001000c1660001110412140310714100c98403070403150406a141d460444481c6480c3d102141071007070641ca402002540710315003a00690148502d8034145e80380c420040c03070041c1c074030581420552900b00650209100d540551042c02c1904100c0000c99200074000c4500502c07a0b080007548031085c9103130f0700d0080740000e080c14070007503c10090b50a038020250703003460540741c050cd4966110400c043c1002c0c503010f0b4a13040c03020300b444003241c001400039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 143991142 1250 143989892 143989897
    0x6090703061103040c0e0a06050d08090301060e130807020f0907120f02040815060a0e0702160501050901121e0617010b031c0c080d060902090a08030a020a0f1104060b 73
    0x344103800401010070456180050ba000035a0b0040c00d40703002400c00c1240c012a080c1c00c0e5004143c000b40041d680759200005086c03100e0000b000c54181c80d0100d844005860284100e030001e20030554000441c2c90010f8104040f450380240041030841702090380c0003503440d4198034806035003010f028141c550502000203023002143c00100c0f04450709100444140c42d4550007070790121100480106194a030007180400710510092030301e0b4014040c0c000024a030f00050300a54010415500507101e00301d01d810a95802c1e0205405c00c50610008200404050340c0c8210b0404c90101021000a078080300441c039904c00d24020414070030b00604201d4085007100c00301c1002c68528100000820000d11440c080c0f54035404001000003c00c40c0151245075942d0203501c02a61301c501c030b06650740c40d00707105411030411500560040c10307003540d0100f6290b0040c10300d40315440c05801c91000a40c00c04c0a80700c0c00a540b074100400c000e020412002010081007184170010407610002802403007841d845400511054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 143992392 1250 143991142 143991149
    0x120703030e0f1915021f05042a05090c120f0a061409060d05010f0c03020901031b0e0d030905060310031109250c080f03100605090f040b030307051005070e0a080318030708060907 78
    0x801c115a00c03110352080b5a54101c0d01d0b906018850052701e1600d0204810164001c0c0440718060081100310b40ca0700b500e80c419840b40d0b9407602c1410250416000d2607080b078000e90841c4c440c1d401082050303581e581e03a00d0003042c2d104204407500c216003e01490a217000d021403018150341c0500b00010b1000190301034000d00100d14080e40c04110307168040710712103005007480491901180c414483e07a0340710301706410290308060290038903c201542e10000b00310a07520840d1400009003011005000b08403006c0d00c00b0f50041811030b400c00c09800c1030005c0c4022011282e20100c4440c00c0d00c2080700a0a0090030031600b802e0b0014451034840c0f0b008050455141d000f201c03100e4041c070802c00c000c80c0043c050002e8802d0a28041c00005403400005c0600004040c0ca40e41240c0c113110034020140050020400d951156091180c041640e085c040070140c005141e115450b48110b011090030300520038000f040d600d000e61a90000000c540030040820b04100c0a50005c9249000d8541003240180c0002a180c00301c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 143993642 1250 143992392 143992403
    0x414270103151116030509120a150e060402011202090a0b221512180b09010b1201020a050315061b010501080d030b030c040b120703030e0f1915021f0504 67
    0x154801d01c554105910454101810b018980c04e0000042480389025080141024149103521000c041c00e0303e24080f02103008070342181c41c10f040480200142c0c041c0b20244010b100040106003080c0e80080c0426410b0550088003907070104000030280e98124481c40113021210301c0d1661151219880705004d0304102d640305411000d90000070341c450140ca142010218160fa885907000800180100a06038054007007070a00c1c40603020002041c11424620b0050143e0340001448039405000e008034140c24910000701a403051000000780741c0c0240032641d002800c8a0088142050303d80043c00e5030160882503494085103801b51004800158440e07810383d4403120803140d032102048800c8040e100aa000039400da00a400c000c3c08909042d0444d03c2da00e140208018160200c00c416145000344030b6109800080180701c141c40d1710300704540c1c82041140c040c0d03209540030425048510100d40310384100d0320a2400070314000c0e6510302c00d01100c2a4001954028490030180c5801d501c003618096500380c91 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 143994892 1250 143993642 143993651
    0x9090a0b060c0a02210703030c0c0504020f0a020d0503060607020904080705010c020304030c050a030206251b09050f1303050a050c070303090e1305060a1d100603031202041427010315 80
    0xb0341c0c003540c02005d42c80e000d410b0020071419003990b40c125000c480154046440100c40704000c83d0a60b00c50018007c62984005940e0b11850b591030001c4c94000318802240c280a010014865682c0711041110401c6406440d032892684541c1f03400c04041c4101007016006501e4400310000780d95000c002401103901070282210729585460411203401c001d80f000940c06202000110318261410242d14085034640140c82c5a035a00358a034011240c40120444c10160100380301400200b04912440b038109461402710a69445e140c0c205003540d80f44690060144a0701041401d8814482c0048400c6280560161001281c3e02d2030041c0c1041818050080d401c003030000007030f0050b00042e023000d0301c0c1070300503009142d2a1580c1c070b07828004004101014419a20040111201c2c0720101302e060100d07001c0c0d520008000d40f0b18107000700144a409070200031180100b000300315040d01c0c43c0d41e508004d02c0c00c652842030300700388280100da0b0b000c52201e0307003000b4258000000240b12540e802c0044442c0490002d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 143996142 1250 143994892 143994919
    0x17030408160f081b01030c0c1704150c0f020103090203071e060f0201091110020703021e10020706140a030f09051b01020d230403050f0601150f0509090a0b060c0a02 72
    0xb912045503441d08051002c00040d03141345903209400221a050b89070412540c0214203403192501c0c2541010600412000011b04000381c0e091081110031645040c40d0801980c0880e50f5035076020034000202070704054a49800c0341c02d40d80e050208400501480e55402e030000420003002c22a501c041c82500c001c00c00c403881d4083c0c1e060040c0203e0106603803010150f01080404010000c0c0000044400c40171807080034070100c0140c4500d039026444034505402c400989007820108500140303024503c3c400c54010320002c01170a50040107141401e100303400740c00e0b211020200d08500400c2000320100c5030701e06113401501440703004507070000b0303c211200701c10017a0a185001642d5034407100510f400001c0010706500c00010380c4a910f074002443d00e050007884c0035506e071515480c3c4801b217800c52030960800d000402070700540c0045501c002900342002c00510301d40c03500c06019030051400040c007030690000014500178460780902c2a841000700000e0b203909a03a04a1313a6100c5591400728000c900300040007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 143997392 1250 143996142 143996159
    0x30212041103060c1c09051212041101111b0607060603030302180f0a090b0607080c1e0615010c02031c021b060c0331030b16030c080117030408160f 65
    0x44800072500041500c00c110250f030044002c24601b441aa514040c010142100c00503050080c4208040c0c58040d82c404d040508042c500d50740040743c43d6060144940180034004804100710f22141e03514046410110b10020201e61580b0540e48005c120742c0c41c082c008400c00d50158040c046800303084018511101500d014411820b140d5640ca550104010300200441403903504004d91800d0060700340750600c0f80c10754030b841d842e0b08040e0108880e03400400700085058515105a003000440400400d100c6c01c100c00d03454a8a038030000514104100c94800c0d23015520100290290101217010000022003200e8000752500c0122015042600411815000a00d0a0000e880c2000340c600c003c2d51615000810100c45501c00384c981c4130b0322100b4800d1036142a801c51010354001c6004103440440c500d041e5840c0c204032100100c4050034180340144101c14161710001d00b60544248810002c1d0b84d602c40710600d40f85001d00e52100000e4441ca2242d104000c0107030001c1c00031111a290a038441c1519007200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 143998642 1250 143997392 143997397
    0xb07020607030903021e19050c1003090b1303020f250506040f06080402121005150102370501020f134406150108150a03060c030212041103060c 63
    0x5001030740451241c90f01c02ca1484140d855030544c6c0001c0b03401d81503901d8045e082c1d819421809459581100aa403415414a4564401001098502004482500d944003110068081c002241c40c0d101003c5200c04c041c004c014020661120301c0c12030710300f9510f000300300c3d030040c904580301c00310389480040000e06410a2070989043c0da0145070b100030362500b4110102c501c048000c0c010b9034044401c00700c0c001441d50034042d000343d8804041c1c02040901e04508110000810860214115440b000c0441e241c40c1000c840b08400c0c5080c0d0314110780342c6441c0f07900700d44c2d40340b01118040c10652001030109407038a1203100a2061900305207080038040d40e40c60180882c10503000020442d20440019889241c084150b05103084158039101d940c6a0704111202d4030740f840484210344142002e01341440c1c190707008641e0641c0100107000031b002000c1c81c030b804505030074190b100080100c1d46030402c426426001e501079448082918000300f26502e014245000c4104001c041d082c02401402d0202d01038440b80780c02c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 143999892 1250 143998642 143998661
    0x9061f030b0a180c0803070b01061d010804050102092106010b1c0c0c0606031203050c04050102070e0406060509270705011b0609022107240503040c050303070b0702060703 75
    0x10400765540d1600b10b54009040d40d1a20148050ba94400e0280000c036250f1280000d0504c2800464585c00a4905a03140b01d1042c0c1012090000d6445030b00b120542c10245a05081000c2c60302d8005600c49181c114064000c10f03e989520034510034541e07485942d801c581814445591003224666665045030702d02600c1144400450b0711001c000110700c1c081e06070041e8103070500300e1500e050103240c1c9855a10807200d058208a80080e094803d5508050741801a40c0d0041e404002e0355160514250010f07550303d00c5403040c070008402010000e81806013680c042802404007416164180c901030511201c1c558103164056200b904404090344c2d200000190007090b9034068480c0018056001c3d060485901c5000f4111825900c4114280050b00c3e01c0002b0080003046401c1810400b41701440c0c9800c00e403c03500000b180c010030b4500c0788000c00c040044021009080c0c01c02540c2d80c3c48a09060101c011942c100c1d41d014400003c0e08420000c520f85114842e80c03841e42030718811380320410220156440704e507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 144001142 1250 143999892 143999903
    0x7030c080d0806040213060c0302030702031209041a0f010311040b0a020309120604020a030b04150c02070501020f030f04030605220503030601030e0f0a06020c0f06010305011a03070308030417070b09061f03 90
    0xf1401d2001f01c0c003039050645014004d00407a824001568000f038608403450f0095a180007004c281115141040d0190b03c054002900c5c4418501e0740a50100e8184141c06124038109500c440400010706543c20482d000b0f04034068049075103884040c00a9540d074007220580b40031310580483d8001803100450598022540140800000d51071334807801490305e0041c006498150400c00f40340030412040c4030b0580340c000c10b034000d000420300d480006402c018000c0c0018025810401515010a10301c504540aa90707000038001120344542801100103103c46145002082c070b181d40c440709000c000800303144034007401d030307424003422107410000b07030300d4051a0600280aa10032060f160006410360042d203100666102150001d8030395008052800d4000e07070003070b50ba99546910040c0038070f612913585008103e0075002810420726507a900b144512004001030101c0d005420501001c0301e509048541880c2c0181960600c0c0c1002514292103040c250740713103d998080b19005401858102180c2000c036500b12 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 144002392 1250 144001142 144001177
    0xe01050711040c11010e060f0601021b0607030e092802040806040f08091507170324030709020a0305060301050703051e180a0f03020708010204151107030c080d08060402 74
    0x150300b40300141070100f034804184207070f80c0e103182c040c0c4000344150341080241e40028115800d040c188420380718000381c04c0038110f4200c0a14000c1500041d01c8a00c540342c5c0a03240765540e0f040c981070440e002400c02103102d500441e802d05110640b20640d050001c920000102c2c8000c0c404800400ca04034800c910070001590001c500090108540c140c4801400d1300030f0540c54606807002d400210064003802c0c49802c10280880c001003881100c001714201c801022000c0f41c074500f40b0594410b0344c82446c0110100480d205070400c00c45032028840c0320018441c030403056450305005603001e001303041b080b1101e07406980b8150000301454404d001c3c45000e2000441c0140e01c00c801646448892000106810044102140c01d040c0c0709a00700700d1314140c14002c90b00101e5840e420b03d00282861225805081e2580c014082401140f9004080d50010421805c0c041200803002e4551030900710554005015903da0031000510190081b800340e00d4851141d55200c015030740c0204100481c002d0410600340c03500e0a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 144003642 1250 144002392 144002423
    0x60e09010c0c17031e070309170406090e0c040f0f030201020c011805060f0c06070305160c0201140711030609010f060b13030b0910020d020a0e10121e0213060e010507 73
    0x200011a00700c43c40340051402003120005035618880280d1b90400000d50b14210314060081c00741032010f141d070745028941d240c51f00d000c3c0005c00b160340ba40144a92011103001041000d030031081141c00910042164134403040c1c1d035039001c401c001c0041c4000ea0160003416030b12025507201d45074184504d01c4072503040c03115504040078084c5c1904280040c081c1f4030710802200075480c1082009a00c5403070299008141442d10b0391103035120104010452041c404002d0100005070b0300b118500c068840c0070b03400c10b41c0795440c0d414440100e00c40b480700a43c15000304c00c140303c01c1c0c110641080319140c1c1480010f00c0400d50b2204080c090b849200000d43d030840d03245200340006601400c541d03401c262080100c0b0038030100424007004a80c0308007a916002607001911814030382e04100401700c44541110001100394880901174030004011044580c06d90b55801005498002d544400ea0000510300c011900e8200e15401d90540384c4090150384040f0b2440303c1c0c925225841003045405075940704400e00000780c503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 144004892 1250 144003642 144003683
    0x2103200c010605030a06050709120503030606160b070c060c11070312030b10091509080a06050a0e0d080906061906051804020c03090a0509070c0b130204060e09010c0c 73
    0x80404010100d540700c48001403244e5080006404040c09030030b0014141c240f00401030200500359200c1311110040160b44008583c0c040182c130350000056940a0395025035200c007028103041c2e4030009001140750b41c240042d0303640c4070140b003552610440040007560040b243c2035640e941ca07545152030980c01840e00748000344d00c03040e440f0784c060744038100861081360345c0000841c00302034074500b60006050303080c040003c03901171215070b05051041e0900340c09a505040617151541102100a480f084e102c0c0080f03103156456034407a0070f6a224810035640850b030928001001c0e60070075650580c0310f1045601260306881e000103070944000c0c88030914a401d5140c480c2c2540d03140c010101e00b01c103880107481a401280c445000820844544c000070f150340d4034403401080800012900700c030b40940000c404016010307402a0158a50a4004543c62500c1d030f5074100703403e590510400002c0d04242880000200c0040000c000c0703000320480c10003446004082d100488800c4480940a401a0051403160000d0070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 144006142 1250 144004892 144004897
    0x6130b070204020d06060c170304020109090203090a060606050c1b01050319021c020a110c06030604180213090b1302010804110d211202070b06010503061309210320 72
    0x910107407003d03041880790403001c2d044520070351200020071082000308042100044003407641110100c1600e00b94140750b0002000c5001500400b1b103910b500001044015408201c4e00a085600260600080e03845080082460f007288600c00e955114855154021007032020032000d03054010396580707045689443d40319020ba81c4034054805156820040c4c0380da0b8001500761001c0c0d00e10103078009070355809001e000030a01c040b40310201d01c09070080c0d0010b126954031901200e4104204440103d424ad543e04448604000340080003544504984040031403d07689403c01840c55005120050b440c5e0740d10340700308000c228613040080c005440750000400003041e920700c0300c46294014003200c013808141d03550080342c0000703800d02e4000d0384a1400c282004a41c0070b49084041d684400095040c12500d555041e058000600180d041c80750100c0080c1e240d13207929850b60303181038401105103c0310003d03003001e030b500351402004001000c59050f41c0f012198040d00501e011042c00030300c0d4103507004003019584140c0c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 144007392 1250 144006142 144006157
    0x807110d050604051f0506010903030e04060b22080f060601030f06150c12020c01050d09020f061201030b010509190506011e1205070c03021216060903020c040b06130b 73
    0x10059911610114400300022442944150700403c1020400c40c1c10340c081d0600300700401d0480d41800100707c01a41e200b5021001c0301c0c2e140c2003004101404a0014014241e00c0e006107000380d0002c070318010980340b030700300306420340b0441c20003100a29110f0301481d031201c804070b8150080360300c0440403601a5100750302c401c80040c080940010f003a44c40d680d8201010400c1200d000007c1c0c40c454041e02406110300070601000e42c0760004000701c0065200103012030040c0d140400d000783d9a149548155280c5120065030020018a906e1b03507940c0620400340e040c5400e001c20f403403a0300702c81c001203024145a64141d0107056030300c2503843c000c050030040202800009110504100c01003103551403a000f43ea03041e1100d04402d448685501c1c64a142c51030860320010022820080131400e1040800d4001c5078040f02205900f0000d50765910320b015815400d92440001000c5501c1d05801c0814964003040014401d201218180031121600c0300b000b00a0041e0001901c2281240008101009014000b0700c1c2a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 144008642 1250 144007392 144007399
    0x203010204050d05100c030c02101d0601060c03090e0f061221040302090f060a03031206050a0b0a021501050306070e0f04050a09031211030c0d09021201020d06050607080711 76
    0x34079480d030020036207582080c0d80495242d808010140700700c1e05940200e40761440346240400a10601e880000d60b121440c450324445280d54a04043c0c100c108e0103401e10407803900008403103503541c0d030355802444845000300c16000110144008219454520140c5000307445500303a04d42a51503041c10010702c2c0e44a400900900d2190940080740e05655080f50303102d0482003450340e41c4a910354014040d28007001030400c40e89100c1c036030800c01c1580d40c0612a03000d07260149403400c181d034082c8042c90300030183c0e41c01050307001c1c01d04440081d002500000401001e0401d500f6500600c020b885601c043d40c070207000e51030340b542101c00081c140a03c5019115103081d0020a1040b420030713500003080880f4000e40e0742c60703a040c0c0c41e08100020b1580000300b0000f0740202010400c02c549907000c0c7c003900c070b000141c006101ea1000294911041c1c6081d0424071359241c0040481c902070090b0300c0414001d602040c84856041e0a00b80c00080c20320b0000103480c0a03d4101328a2480e01546507180d5040038040e0410561 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 144009892 1250 144008642 144008647
    0x30d080f0c090d0c03080c1605090c070326011a09010e040218040603050a1205160303051306020c010f0f0c090909020a18051e070c020d2103060f0603050402091302030102 75
    0x410304c207042480043d0b001d01c14030b40e07503109000b21460812404115400544440d1070041080380c640550f400d50041407001c180d030702d61203203180440304141d544d2100c078020130b120030000c804281c007140d003d07040750b056000a01100c800c0d020042860700443c00c045000c524200a074100c241031a4000b0000128684486d10031030040100107021a10300350010399003a03206080c200c0802c16084c040014980e42ca04103a420601034078203120a90900b240020101743d187c20100d00f0380e40e0719030010680c95901100a40d00c0c2c0c0c2900401500811210f100c06580a0400040080c9903c840c490107005074407550701c40d40f026041403610f4001d00a211022038100c5891741c0c0004264800c20020440e01d00035031030205589c140300c00d0002094440800b1002d2468800041c001040d400020312204a80c0c1502c109540b02c28a0810801e2a841d50107499007014640c01c8040e0465410fa0141c1d0503510580c42000c0019200c10048048030310803035000b5005800349000c9411401e48410b0040324500c001c0000d803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 144011142 1250 144009892 144009919
    0x309080d02030403050111030124020307060507110d080106050a2f1b15040501030f0e071508010801050c090603100f090203190903020d0c0206040f0303080105030d080f0c09 76
    0x145000302410640c0c00581020409004201085c0200004031550b601c0141c110b504045d40002d00d2400c1d41007a003e48a0181500d1007510300902c2511111078005800704400e28007030001500803401c62488a92074003e0000e018182809201010b041c0c0d42141c0c0c840c0e0a1510854065800700c0094414a45c1c684412030900d078848001c50107505101810400b42007071048110100f02500c0110070310303500c901000824600d124502c84140c1e0300b100d400b440d001c542845018801001000740501464080c0164800482d0820a402c1050305a0702950303910012a030341c030f044a9080b071b4010340c3c03a500140c10801810300189083d1000e5500203c244078505980c540c0c0e41c04461080b03586034000508150040100158054103402f09169101c010f1018000a48180c2d0001d44030b1082000c2101809061319507a415502c1d59025100030b0502c102032110020345a04007e00806001d104181c400d04c0350147c481d403032900c0f40e030000340a002c1d0203002d21190780380d03201e410107150001e600e00b6810020610058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 144012392 1250 144011142 144011159
    0x190b0a08030a0e120a05070e0f011a03043210180311030f0c07150c030804080315090a0203150321030601030f0c08041103030702131116060f140c090d0309 68
    0x349a1780340309000502c3d000345407445001490100400d00c10022208000402c2421040012103210010303040400783c1d2541c507403400500001036241d55a4001c01c0c101d0325001000f00400c1e44030394031a012011200c10928003181e40e0191604c60340001a90b1407101907a4002030b000340040e551044102c0c06807820a0120300c2220001d420240390031007284d000110400c422640d056200718074400390300d48220300e040da90318054070080c4090001410381c0d00010018003c9200c0d04254119050014800d0f00141851100e9074080d400540d100c40401c101e68100c00100c1c0380000f111007102d615090803c0d8040031100c071600d5690802003501e030606032981300c041c0c6002002c0c441c0c44041e030069221a60305050500707100c2d2031418080e4141d40258020030000740583c1d6aa45101d03810b5443d20400304a404012000c420340740036900d5644100c00b081c5150204000068000605d03146042c1c004020600b22980c212003c440196044030201c20304110201040c1021011041e4160003030074405030356a030340d4941 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 144013642 1250 144012392 144012403
    0x140402070204060e07020309040612080304030f090f030f0c290f09040501150906020123100f0b071406150402070212190c23011206080105190b0a08030a0e12 69
    0x405c0010b800000d10640c00745010711403800504102c422000c80c42c071243d07481500622010380060107200c564000062101d1090782d40f84003410384a43d20401c1940d6a240048140b004010122061004600d001c20034844081c0c114405540b4403a10130100390581011403803950010390541071150b82044540030544582c001c0e20300900ca8101599080244c017900140000c4854004038216418454068000101081207000502c6200d0ba220215150800c0040c4803216a074404c409000e078604000400c401e0080c082e010860081e0800401c01c0d1154540e1074465000322840c01440d07504c03107071425131418240c0c00b501d03400e40b014108450b21140103000d82e203011015800b0351094100901e1034020000c411011000803d1580c2d44ca50f0740c101a11080203c000b03840e85c041d0304100d0440030f1210303903424640042c401002c0207002004103090141c0c0b64512600051041e00c0aa030600814440380d041011100007100e24141c040c2d800d103785800201e072401600006154049080c201411103110309211 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 144014892 1250 144013642 144013651
    0x111070c031a07050a0e121501050319051902180f090c04020301080a08070c1a0a030617060103020f030f0129010903030903060c050c010507020705030105010b04140402070204060e 79
    0x1441461440d00c0d460006448148202011500b0140181c250300802070b24002d84c01030402000d60b03018400400c906011004440056100300894070040c44440c013034680c1078403002e4040e204940700100b005a03441d0001c4d0300080180d07000f03080641c442c0c0c466501505003907200410055200704100f40a049104050362036003c1c01c4c0b001024040b2100c010481c1102c024825a0207506541c508a2041c2c0c55808542c0007800d00c1d00d000407024208400a00d020707014107080e804001500c85905107950107038200c3c0c940030011a1500001080045904100007a04a000002040340303030700f99400e024096a80315002030f0180329442c644140b0b50000c0c025818290389511a4440312003c86000c0c5054018251540b4103001c08900c051000c070f0740c0140c040c000d90750030034404900141c6540c0101d9003842040780002c41c5504c0c1c1020300104541c085000700071108114002d1002e82d1702c0741960407180c4242d00c56166481e10481c03806440307050903005001c80e42d00003040001c00c3c50740e0b00c910395945801100c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 144016142 1250 144014892 144014903
    0xd020f07051608010c030b030616020a0b1005010207060815120106150314010b040e0f06030307020a031a09010203070504030212010912080414060105060a050921010609060b09030a08030405011107 86
    0x1841485059005d100f1030b413580040d40f80a000c42910040801e450b407101801a808168200c0e024000035030080017110903169210f41046131915000c4500c102039070080c015a401400303101d20019145200e030100c103015440036050007050b00c0003003003001021841001c3c01400c9548450001808440d01100c80300701c1030740c5031004219407404000b01141d407807050f0800c44070703000b080c03205002031810020556400441360081300102c5c0c42c0c04000034914000c000c00254060380d044004000c102c01c2c84400480b44400c1d1079000b1483e150038503a00c0c280c6c08110b0300c0c00001349040c002040545070484a824030741a604000042c142d02c917848119450000540d038a0108025609100030040c040c0b1384a801e916030500a0300907941418005a518070841c1200d0080101c08541101c0a68420841c00301a4141d44410422800707404944e40c00380c106413140c4070440340780900000300c900c0b002048900e00e4500a018140140302c0b0350b00c400c41e5401c05401510117669420000c44280380c0800181032140c001d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 144017392 1250 144016142 144016183
    0x903050714031903050909070e031e0d0201060303020d0f0c12030905071409060d0602090907020606030d030608030a0302030405030f0711040e0109030e0906011103070602190c080d020f0705 83
    0x40050601d49283c1c0c41c21075006445044200d004258881e0660b429407804589140141c0c80300e2104072650404020100e52502501e420840c040c1c42c4544820102d460003001d0f1100401c00c21002d81c225085880050090f81141c10011051445000100c0650005041c440320903021506d481c070500d1440384841010035544c01200d0709005080000e10002c00c03080740c01c4450108010003160b1a65005081c540c003620803820031000b000104c1c0c064607031a40d40500480354610340000000d40c3da2805560803800b038002c095a1400840c4240502c2040c0d400c040003c51820301201c1c42140290b100420a5071140018403190030110210f100604d6118000d88440e406040c49100708801c075580e25040808581c94200004002500000545820b0008485010b050703501c0200680d503c9181c205070003c2c501000a68800700082540540100c1040c144851701480076403600307031800020090068002502071041c0c3d01d400d0300a40080c40b110660344001410710301c603a99480c1c6010442100c20300166001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 144018642 1250 144017392 144017429
    0x10e010e060f060604140103110706090b010e01050a0b0412060617030301060311030106020a020d110301090305040e0a0605090a090516030b090637020417060f1b0406030c09030507 79
    0x42d403410754220f0001c40d0614981890324507000d0020a41e492400d05054503103101c4201081103005980c00710303402c110b0a0214558525001005140901407001040054000400d5a0400140000c00d45260800c2d0a10302030901c0e814510861400c8402c403025521040040340c007080b1840c1004008400100a540f65410028003074103903424034000002c02301c0c050004111844d400102d84607202e4065400b42081811400c00036549025918101c0d015800c00081c1c40405a00034020800c4400d001240c2c01952039000050099905601c03a407984400040c4c045000481140cec46107110318800c0c0c2c2105d0100070301201c1880301c0c141075030040d01e00602d160100420210f080c05030a41c043c211000b90411062090340d4100e80c0114503a0311b900e0140701303030101105000303998115000350100c4a440800b4800f034000d00c90f500c1c070017211404440100135000c07803010041021044080c2200c46030a6045c01d047c9042200180030110310701d010080209400000b05000b845041c0140044813a102c002c0c441c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 144019892 1250 144018642 144018661
    0x2040b0c100f05060d020d020103090b180c03010905070315020c01110c0607030626010212010305010605120705010909050603031c0c030b01110d1107030c0b0301091406030d03050702010e010e06 85
    0x84402c40341c40c1141003000f00f060307541e50146044107095049408034000815400120014640d05400501c0080c242090040c002600c0b0701448440d521a07080703400342e1124609141c24ac1e000950014059804407000b400040c080164019010289001c01810101400e9180b4203440f2008411011500d0004810000403014000c59070300c600a03080500400b89000301824110385081c40d0740151f0b41d894102c5018245003901102c0c4d45000401c9000c2c010750712400c09a000740340d544100707485446219112000e0120104105080f540c0513152204664648a0f0010140c2001400b0f2941800100012505a0411400484080030888000900f82d0101c0c17009402c07200442c024906014410604040601d4005850450703c202480c104203c0c1c80d0080e0514542000398000400f0a1191000030803005210409503049909004041c0300310244140d1580584030306680458141c0c01201001c090b080c0a0341140c1d400803601c0c03000040d11821948414210346d003681400d801508064140840d550 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 144021142 1250 144019892 144019901
    0x22030605010f051206220501140a14190903050702060a030b1e0919090b011205010b06030106021005190618060e06060d1107170c0106211502040b0c10 66
    0x38050704c4140800da5281c0c841c1d540e901c0002d0018040c1c1c00b54a0308014100a02036000500707581c40002403000740c0c1c280c5148407081780100e030100d04191a02c10750511100400d485035001c0e501d042d028803120090165200c01600000000f9000e0100c01c01450300140c44100c000c00d83d100d100e0f80d001410841400c204100c0031040882055000d400d0120440c0d41e55404840f25040a096250044812100c5413483c002e00706801002d000311101900004480c101c415859071030724442c2000300030403010a002c0080700e01081c0243d40060344102d66030402019940d110a030403c00c068821200b510101410000303a40803600140c14603606c81144001368403483c02500d004d4440c6050030101c030700e050070104a25000f69926204480d40301c1c0d002d1022400d14a044400003904a82405000340d00d03131a1121265102d01580803141d880c2c01c60024803081c94020300389202032040780c0c400c13a002c000d407568a6074030041c50100208560800001503000038803c0201203030646031003d810640048400d0700100c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 144022392 1250 144021142 144021149
    0x3070f0207140a1202040608070e0f06030a030804021e09011214030901270305010c030b090f07020601092d050105010807051305010c06020910030605100c080f22030605010f 76
    0x1410b07111006841c0d90320a007002c015112980060801030703d603400001c0203030280358406105070158110120b9003404494451b48141391071b0300c410310107443d82000d25a43e114040b401800181200c0003050052400c070340d0900982118071161068800f4240004c2c03401d140c2a8004180341c0387e03080244040000c0b54907000c0e0b0304d903e0356014505020301d640c0042c0492200400101c001d1541042403540312015008940246411800030883e5551081d0003078001c000106c0b502d440782407540001180341100014040c0300d0b0005502402940c0d180c0420403000e401d5810900901e0b107420740303c00741c814900190f0551800c003402008039040d4034210000d81141c1015041f6020050300300900100d456000170000f0845a0a00c1c0800c00b003141d50030a40e00038018054040e038031800c040d00b032442c010b6040d08510240c501c1222604d4400c3d00480701510440040c8400510700702d01400070303d40d0048620301600c610003c0e8054808105661a8215100121500203c8039640e0707880040c884c4080d02180c5a001c1e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 144023642 1250 144022392 144022409
    0x30702010e120703050901110105040b180109030c0201030c0903080309071a040308070f06020708131716030b060d150e0d140706050403031d010e010c080f0718030803070f0207 77
    0x8010080141c1c40039100f580d2014051100003e00c9110360b9108148001d0111004030082285045c146842032034a00190b07051460011312851007818181d040c400c142080758103403541e00f1010451750042d0054020300c1501030a200003881c001001c00c421400451199010fa00500203240c1000076130302c80302c0d0042d040c50005081c00d000520005802a04641c100c541207001101a94240e00d0440080d1141b0500108007900c0859092040003241d81c3c1c1c00e054688140d26010761480309a01c1650320600b0504c000c420f50103a1783e003040800c10b0350500b203070003403005043d50b92070544a840d40202004a102100710440d84c5800d0650410002d10150070301184600d0003640c0c000408550158502501c07501500480d038800104003010f00070f41c0040000040041051000048000710358024400b106034201e2550a041046418a100b0080c031032050104a07110002c0d500d80078811181c0c100cc4034035808000c03d4140c00031000c901c1c0c15002d51310401d074a60781c050b810040039800070300340091503018400703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 144024892 1250 144023642 144023653
    0x60907080114181c020a020111160b03090c040903181a03070e130f0b0103050c030615071419110a2106021207030203011d01140103091a010b030702010e 67
    0x7540b080c20300c41642c00401c101c050b840306a00c441106400c06142001420540242407568030311960045003002c44035000362a0905504a4910a2038170b54503918840b12181c0d0450a082c006403028001442e080005901250800d440311004501168a003031025004070b803100b4034281402d5168074024020b40b2482d401e4480001d01401c24140d6404040d00361020f2004201e64078086444d0903040003010040040b06101c12805062040c0050580b40400c41c0001d0400000400c916103003011240158400b4001e2241503403030110000598106150446100400c2ca40110007040c0420040c0700c28142841c200804030054501400e08000fa82007490150400303050400000180c06540c1000074002045c0318401c003654a001c5000f8462032010350710402c002000d1111041c0c2c154080e42c165982c190320315020b20301c00405505170000912800002d078404d90b000345195482904203213289480741483c1000e1440540810900c608242c20020070804003100b0052203e60901803440c607580d850000d8003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 144026142 1250 144024892 144024911
    0x90c0f080d03201b06010605040618050d110a09020409020301051806090a1a03011401081207080a030209040b0d0b0403081608010302090c0c0f01020307020c120606012a050609070801 80
    0x49000b003c1c40c00c4820540c04114101c482401121804661a10030142d440315a111500039100e600300e8080c050001d901c407800310783e040c0c09403007001d03040d9031005000840e080340550720ba943c1600e4111005800904184000070b0b0107507a400a4000351018050258403503050805002c059120f0301501c64924807110b042c0001c075200d51030303525000400301c5000724444420241140d030b00413071344142c540c0540c41d2510a0806402051005041e101c0f5a01616070b0300000300d04030b40b024000d650014007409000c00810810b10300a6006000c9560003420202c0c120908100190010000340d03030640f0384044500070481016840300350355510560f42c241c1c0c0801c01500c51002800810140402801142c920000c40c401148200a5800710701406081700c4002540c1a8024040d4005441e00300142c440d01c804c00c0000d10309600e140d104506184000c6c6103e540701d4004640c0039054501040c00c0c401038098081c401440b404100c21300500400082c4694141949982c1c03401c18950301580060b4504008034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 144027392 1250 144026142 144026171
    0x10f0902010e12030f210c0c060f0a0603020a080102031b0301080c040209030f0610030507060f0f0e0a0308030c070201090f120308040303060e040f1a0106020304090e01090c0f080d03 80
    0x4012080701030301d070600095000b28150313246220b0031000c0d1a40d50004900401801e08a840c8000c61020000102c81030340c5079240301158074025101151440d8003c000003034541880340e900c0e01d50107861101c0c00300362160740380c02103060503209030440605650000204046485c0e184000703551100b07110103003455507140a00342902d0780f180000c640d101c0d50300003e1841c0569420004200c554503520103a61035410401140c0c03104013680d00c4222194000e081c000140140104180c0ca9802010b49a45200100c0708408803a8070380019016980903600c80c4c40070010440b01d0b0051841150080001607541e9040d0002400744802c5500c0164411039424044c400084d008840d1140c1ca540340c00c004810b40c40d02c1c60207401a040c0ca0b0800d50348000b51030200411f1103080301c6d4070712119000701c0c2c40d11030560008200c019030310402d008100169008201c10044004c0940c8442d008443c40750000503491119514a20500f130309a00400071a00084000e00402406111000310602c480c10200400070b00c0c245203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 144028642 1250 144027392 144027407
    0x702030d0b0609040501170f030702090601082505040f050301090507030602070c0b03040305030118090b0606090415090510150804020910030f0b0708220f0606050a03080c010f090201 80
    0xc042005444003007801c5a40ca4080c241c1c0e41c9503200600600096031550300d90051080c58400c000607d106868512920a01c04030403100303a103402034000da601c1e907038460040d502c108001c0c0821550242c5550f0681c0481120603107080c41c00d4481c1e603520ba84600e031480c903d203032840036089541f280c1d140009c540c0001c1c5002030500112a884000962105400d0400d0480790415a000d00c2800070004100000c056001009606960710b1a0720241d101110211080807101c04041c000c3c04c0d0381012001c0358952801c10041c200320000100f01040031100701500c0d079020300e0030b54488103083d40c0f40c2082c4082e101c0e0204012000d00f92218140c089a50060700080003110040c2c406406590440c01282440069143c030001468000090810382d02c00d9180c40081d84008585140c0001c65160124030100b003080d0514240044000a01002242944441c0d000c1040080c044030040e0395200006442e03160075840740020b41c0142c00380364661401e81466420758841c0007262401514000d900d00050ba08682c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 144029892 1250 144028642 144028657
    0x1b030b01020d12150b0d050403021509030d0b060c0a1109010b030403050a050703091a0304020a0f050d080f0903010e0d141e0d1e0b15030f060904050a12030603050f06070203 76
    0x2000704e02c41c0300500c03d0b00481401030300300941c00301c00001d0402885100c1c1d00280e000e980320358212120408210258070001d002910b00e61059041008001d62201c4190440d00c44144001c0220b0318004000c0c404a00d0805042011540140c51001005481c41c2c4541c0b00760042240b2600035244d0f20742940c4c0101144a00b5490384103000b0041001c00030715100340400c074050070080c000514100840c103128070450700100c03001ca114074000395020911105141c1703c1c004449020f414403543c1c0c80c43d9910590290072843c08031070304641c240301003106541d0034001d0b02c0d401c1c5880340242080d0540a5001045c03982200502c180f941d60421111a01400c1e166100000c01905841180c0b07030030031101070030040e0900620ba41206100361008061115159000d4000f101040303411405010319110340140d9404121250081e05500c407000980340d0030100718981d4047e1180c000d03900500075958841410154450011001955900e410310401004111503600880b0503801407429242c4200020760381d200341c40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 144031142 1250 144029892 144029927
    0x10b06160f0312020a03020408010e12030106030906090b070804021203270d05063112140d050106051801022e0209220501051813020604091b030b01020d 67
    0x80c03950705042c400c1c254034404050450041d9650b908031a001006504140980460340d442c202403600401d800089032030b10044910f16140c00c0d40e01e0181e00ba40108601e01050365178980b1403016000190b800704001d8421901c548a20500341418010312524850000d07614080d81c1c0b040124040100c0003900c0c1c0c0c05032241790400c2c450751210708000304100714410b8400411303500c44c560620607244009203072600ba403480300c580320b01800b0401d203881e2620b800001d80900801111190494154458660300c00c0c660748019085280203000e00403a0211134090380544d001920100304101082c18040e101d050002d000d2004080f0f0001e038418604000380c0000755101c182d10040e402820321005c0d5016038503466401401c44000c04440805401c1e00b01d09100203141042c03030030001180d54030b0215082c1e04800000580302c16140d4800340040c0c4d2010a0420981e44207801b400b00140700340c41c074010032018100d40e5094850b0840e070668003805680c206117030380381950080141c0f4407405601c8005281c586a505 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 144032392 1250 144031142 144031163
    0x801141306050606091f0806010504030809041802091303030f090203150a1d06061305190f02070807030314010b031303080a0b06040f0f06030902010519170a0b03010b0616 75
    0x80f000260341d84248070205d40c000070920014006440c11320080e5113404403d03102c1b0b03c0c41c0da0700c2100458030751040c0d010043c200b03102070295100d6030030107034011f51140300d000e10840a14030440d00040d090301d074101c43c0c00307400302c01c840204010036a05006002505c003600005202c08109640000c3e120307181002000130a820080000302503014503049020b5a0f108002c00458460360128100d84a0508417400c0f0300079000b502c0c07148494100da2140760701c031340c0c0198203490180c030042c072088002e0b010b00e03442e407210030350240840e0011030206401488403034440c0d2800920100400c8030300e4241e03034050b800591100300074001c102508200c3c540d01310000381e140ca04005141d40724148034004000e864001a00844080380104120003518002c01c05d1715482c0b5002c003121503072070b80100c0035038922034802070006e44280721802c006141416050a02100c5041c0321590f5580070351300070a028170403500030380303c25100e2400e40d11340e05080c802c4200c01c10b003c0c4c86a40c50105100004403003c80200743c02480c52025 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 144033642 1250 144032392 144032401
    0x911040209040b041a011e09060f11070e0618060306060f0402070b01121e050d0c150905011d062205150405031201050d1205090604030f0c080114130605 67
    0x1c43d8032849804030002d104101242c0f034250080805d4107545011408501e08005501141c50019030791a60008169184110141800000c407003048c1c501c0d00d000c003802030010707000f90b800c04c080c412080949020340829240b80703445c600700040309035200082c807990401e071b04c06c1c00041c4d107010032416030048055942000d001e40c10030124009206500c0c010302501c141310b0000c82c030b0450400035150b81034003611700c900005502201c42c0ea072401162a008049501000039607034003a02403442c036081c05000303d030502292078501c0203810590364401f00460303c0d40d66070740192640b0881d442500101441d080018502460400001d0400c15481c0312024071884a000145d000c00604210020380345103495010961420140f2784036950382c001c03a1b000c03004482c5060004c41c5501344031001d03940581d0002c02ca04a9250214401d54140d0b00c010b8010390000c00420021000c14000a00c850b01240704003102030400e454000725a00312000c0750b9800e444407030100c0034810700d500901102d40045402c078000090075220b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 144034892 1250 144033642 144033649
    0xb090132071115012d0609090c030b09130309060f050409020c160b070b0c03090a0b04020a05030a0b011404020a02070311030304030b0a0903020106091506031505030102030c0c0c03010911040209 85
    0xe070116103c64203862000100740c0c01008004c02c410001c00300410402d81c00f00030360f498071181040c06040d0006024078003c10416000d50013420b001c0306d45003030000c0c817010113002060b040c28007216034804603129081003208166006500c4001802c151400f10340c00c403011040100580310703d12030a6100ea4000c600391039158420700031401c500d0741d650b5441260a9841d10020a607403c050b200359158015800010400c410580c02c9a03c01c9001c48003902080c0d130240d070b6611283c4801343c81640c00010080e004a03007510100810041d07240641da120350558035203204074000d000080c0d401401180140b10002170a07030005034000a5951210825420148140c042131450045620140105111034240007000f102a031003c18028001d600901004c4c2c0c545035640142c59410170001801c561002040003018820b6104103400503003200180b02c82980d8800003820790704241e42102044400160ba806c0410301005000b00c0094180c0090000e0081603d42042560040b80c12500554000448051507034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 144036142 1250 144034892 144034903
    0x203070b060301332103020c0604031104020325050702040b030c0108130816080901030b03011406060a0903150e0715020307080c1903020c0f0d0206070f0f0b0901320711 74
    0x5e040340d100d0340682c080d000740c0c00c20303031440b080580150081c00e5021006041c01403c54054035081105540400b140005010080d0f00003404502070030900080c05800410030302e00b41d4154519a43c60b581c442c6640d0041000b250200300d542c0703100764004140203220380d8000034040c2e80401c0c03102148090524508296101e4400d0b03400011030140031902000c1004107500c00303421800f0003039038108150105070301414200c9420f10001e54001314800000303801803801030010000b00140307151070f507985036880e603e0080902401200c04000707611b43c2d00350078080f1010000d0100400c4007101900d290750600c20040e480e44980280a40707000c00025405080d01410485e4010303040e081d84030210034400504009481c0d80380da2490a108800c42484043d03a440d05600c01d811543c2c00901043c80d01101d43d45074818240039a104507106140e0042c440d002c50a62504584a02010710021400b81d8665250380e689114840c138103c0041c10003000c00d480401e24940d519484046820038814446d07c04d1002d61425 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 144037392 1250 144036142 144036149
    0x180402060c01050f0f010b0c07090e0a0f0804080d1e030203040303090506160201050601021609020c01060e1005031e030901030b030708030d02090405060f13050403031104060203070b06030133 84
    0x10742c202418440110000d820052055100450701c0355a0f9817118503030782c0f1520540b1110840c6d64014203040c0080b85442d80591055a00304007103c5500ea33142d6100360402e034a1a500341c454020114040216400134010070050042c146051180c5801101c41d42c00080d040300c110404069000c000181098000d900c4000200d420000700c80362440c1407028200c40b1311300006031900550800d008030b000341d400041e002002d81d001c103046030002c0d42003042c07050082d01300004500480d07407282c0c4000b44210b14509583d00403041b080d2072100850402050524200e04040a0f200301d25513079494441031030001c000d41d030340b0031001d2902084250a5100080c175056854110b40b1031400001031514a520160b0300400c40b4810035078040c4295034130700f010454041e82c69072007281c00c1004001d8070001c1d561705074099544580700342800600c2d4003907610341a1554100c0d8005c0342c05a0b00004415080c000100d0b04241d1100e0101c0084c400d40880c10b142d2440e41c8030f5041060400500d0450a80c00b2120707001002020b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 144038642 1250 144037392 144037417
    0x203010f120218192f031009060b0a020d021203010e060a05040f0605030c06030402220f02040b1c0b03210f07050705091f121b0b2718040206 62
    0xa034207003040c1c00380ca407228005100e0005445e02c0d00e100e501034445101c3d01000d10010f414280c01801a1180d5200741d880103040c2c010011a0400105d491507680c80380001030502c1a681c02d0b1074503501346010b45000c12941e0b514080d0b5001112110640e0036030340869041d551411068882034860701e0218650800c00e4228075405420076544022010b90390b4060011614118100c0d001448040c0034405603200554003e5004080c1c10000d14144001c9281c101000502400000ba0b580298403924103e800981103059034a40000b60f811000881c03c400c02c00c111400318081040d8004080000c0e030b50031264641c1c02202c82003800c01603c92940000b9149020019091103030381341c10510340540c441c00603015007481800e591010441044030070b0403a01c240d8601c00d0f2141e0586081c1070400444103031191040b51074840d80c034200314079158508600d60042040140c0c1720b484820b220380701808180d2480304002c00040480340800706585110420490b1a15640010115112400030907002c1c811034a10111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 144039892 1250 144038642 144038689
    0x1912030912031a0f060703030b2701032a030209070203090a09060905070c053705010e01180506010506130e040305190c02010804020f0102031b010506130203010f1202 73
    0xd5806410460000c10501e0800c0f10030054107003005030070381c82c8820407038010700d09110840000c0d000380d10040001c07030020500f50611401c00d80902ca000009004c001c446580f01004004001103414504107105d00c905455065001110300c404154402d480003900c50000d40e00404d43c2c0d14028811290103074405007086c402c032031b00c408401c405004140300350340d01e045c41c205c0010803241c4140d0312400415031140191540c11943d4640c55aa050b0019841c105241ca000c0041082c01001c154085500c1c4944008115160003600303160840314449400401c411071303412141d00061011425a0540d00c0442c0c07900d07119040c001180116030b18603002080c075807840d001400285500705010344401e00d52410118a03411884034100c2d80c0e0351080b00000d001c101d0b0040030070014905103541391820175041c4112401c01a200192004545d15100d02c0201079540e0400d03c0407504248014046150003820154a994540003c04203a00658442c440b01f105000620300110755860000d0002020011708400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 144041142 1250 144039892 144039923
    0x908091909020c0304030b090c130903030609050f07020609030f1209010609021b1612140f060106090503060a0207110111030c01050a0f05090c010e06072d0b070219120309 75
    0xa503254414002602c82c3d1f450b110000c2c40c1c501000074070140c1c21f200030f45220301c01c00d68041503001919030703e80220103141e100c09001c940302c001d42c4903c0f1703c0303010040c0840300d09040c03c460203810508060116141034008100b00c001030710400040303034900100b2090404169407a207860320b004001c40d4001c01c4855000040c0d40c40798105514403888600383d442d0948100710308007404c5501904081c41580803c0da00090540f000c030300c040c03400d020250012000c0d11520060700500c542031083c260000c0002c95070358034051206007400c0243e143e024158120452415205840c0da00e5001c0012442270304108003d61088159078081c13040c0c41c0b04960380070003401079046c038104090103405e08503402e400c101d24142c001040e4480c0000d000516640c1a150450f00070444000d00216a002100544090302041400460042d041c04000360900c21482843c00e080840d10b0601d0740c00d0405003c400031540315103840903055152501210405602a1102a018112940541c061311071114080c4ca070240c5241480e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 144042392 1250 144041142 144041167
    0xf0c170703021f0501080709020c0a0c1707060e030613031101051e1e012603040b0c0f0f0d18090c020703020109090e06060d0c080604060b01080a090809190902 70
    0x501c3c5403140783c0c8a401520140c4254a040b00c009110b00502035000c03e00410450400350f00a00310500000c06540c14080319881e40164202154441c07000c3d410034100c1448240014052400548000d10b1f0190781c0c0c0a0035800a03130b8510000d0501d41a00359401d500e07808150080301040600c00b207080c02800586001c0d420b14008401c440d000441c09504480001d0f0544004100040e4005485194843d42e0342000201221601c071804200f8018054143c1e4440f82442000a4001080000ba0303c0c0d5a0307402c070400b282c0c10200f1004007084240d200302c1c1e11041d49000400d50054a520038503101c8c240e04080303060b4192100c4242c3c46102c0f042e242501c400000c40e40400e096017902e0003078131156512559400107804842540c01c034041ca5400c588046500c9103000c03241d8400403805803001041003500d55030b00605200064400f19200e035038404c901040ca58000c003072203610180f0320204126816a98992070030038800c44405a200395403030319111a070b0038450b2034100d01034082c043e030441d02d070134105909 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 144043642 1250 144042392 144042403
    0x60d0209030718020301034211040e010f0f050a1701090f0b06030c06030108100203090a050d0f0e0607020a0608040230010e0102040b07230105071d010f0f0c17070302 73
    0x8e413005041020141146480e040e0000c412041c0d06000c2c0f51031140e01101d0145030075900380101415512100d5069420400300d014202a20184801c4041545440465591030f1300c5035003c02c1c00600f4100042229503200252141200e0610715500608201300500d5401070450b400c0040c4006188104001071200144c0e480b4800c031003d178112000b519400c030820445000034481c05500c4c1d8441c0a40005001ca190040c1d60071104042c2107030083e0007541d54013800c00b1041c10044000a408c800b80745000c03507010f044a44500c0003900c074240340c2000380c2c008c545040f41a000322070600c00c150002c00c2c115291f5907440e0201070001e040b03500044142d02c16080c4d54111702e0b00c00600641c20103440b501c1904061084900702c598030b420143c03070004241da4142580d48052110810510b01d03101e4a0003210080c09840d202e000a5a0f81c033396a441001e02c0681c1c1c9541e0440d040381041004420711a0407a040040c45141a02c01d0500c45454005864070018500720101d00d400400004907400d410590009072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 144044892 1250 144043642 144043649
    0x519120806010201151e030b07021606050c0c010818010e01020415020303060a17120406030204030303111603050d09150b040606111f0b091612060302060d0209030718020301 76
    0x480c240c0c0c50301c8400049007070f524080c41c03c400d80a0074a1041004040844800360100e103800a20051036036a602c031684845070854842c2c001d43c00004041282001c1060b08401602a03424050306100c0320900156035500000b81c0b81d818082c50101140f483c16030b06072a502a1140039000307221100c800110a8042d40241c0720388a0400c0400852103980c50001c42032701d11514000c0c04810419180c4294a5540b10707607210080790901038490195020203258000300017800c140c0e2401340c1d41d207107903240c02821615100600d5801c44d20501c0304004000b0002006a070564040c0380c0280c031080352402d984010b102250b00240200508040c241010005030020103a400c070807581004041d135168000d440c06480d042041c00107030041c0b0554a400004020541698082c40170300240e81d0100a000c542050001e45990139618240546080000c0e808002080004142c09041c00004c0c034541c04900382e4014050001c0000382c01280d409040d07102006090020110441070715051100402604006d610a01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 144046142 1250 144044892 144044897
    0xa1101030e160e0709120b060105120103030305040b0f0403020d08090c0303130905010f0f03142406100e0a0902071104022d120a0507020a081b010b030109030f0c051912 74
    0x40025800794021120318081b5503843c18a24000300059031080201003005000a040c4034007805000a0441c0c0b0024250103544243c074000361a05180c1403406540000030320407801c07030740740b82c0c00c2000107a4007003400f6081030501d040012498595280590801d8440e0f602c003a014440410803003255150003201e20203c07004804e081209980300c10114034140e1190003110103440303a00d1400c00014940c5492001c1000c904000d40340103507040300340c103000408030f0a440d070a020030f984280b103600d01d40381040007890642400d02c02407403001003000c91300d480b06921600002c140e02194003170a00041030302c206000d54008004564400c130200d90200c4c0a14008000c07151030380c51442d0178603d14000d01c207c441c000740700700c0c0c04012a590781c8840d00103410020a00d50031401a445400c0c00a4900360240012045088103d000020201c8865007111500c060301e5200c2d0781450240c902287d045000c050b0002c841e03242c0f010202c0d07a02d050162800e80b281000d1040003016030418018005460415800c0100340d6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 144047392 1250 144046142 144046169
    0xf180e1f0906030f0219120309030b150a060f050d0e01020703090f05061b0307060905100f1812021c0e18061302030603190b01090b10020a1101030e16 66
    0x54070100304580050000070f124801088101000d0b10b000000110b00f41c0301c00c401860182e48901c01042c3d0086511412000300b41e04030420710400804611030365201a617140d8481500b403907280000d2800c02144580024010808000d4512910841c03c9812401005909008041903030200e103000b5802004107400190902a0100b03641252641100840c1c40060182d420300e12100c484409032007010381c003500707070388002c228800000301c85002e801071482c041d03400f0b0030102419a8004c415140484500a11a8036180f240d040440d21040d42d15581c0790004220012448200016850800008000004200b144203409121680002c1000c9000805e4400840034040c40c00724103c40c0720b094840c1544001e101c5603e0b503000b8034076400356900101c001c00f2101d11401c0c213003e4182d1a050020161040180807005010700b190500a0744000e10058410480c10004040c00946400c04a01c0c0104064090502c0184680c03080d0802e0b8500c4880c031040d2810a0f502c0c507480e12040303e651056410b8180d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 144048642 1250 144047392 144047399
    0x120109020405010e093d1d1006080f0307060b01020309030601122108060409061811030601050f03030703031505090c0c01060e19020708040b03130317070f180e1f 71
    0x80c5141d405031480036806d448600310305060040c425030183c181417074401e685400220540356040781c00740e0315a0b04030006d494190b4150002070260b4072103030066100c0d50700081c202040e0010000c201c0e040c240c1c02540025528072660f0040b42075200d00160036901d80300d454004141d1610003580d034a0854450300d0345881c0801b20306400000d00300d40001c200d01181e031100c006003250130540c000301c04ac40d01c24030001a60136101542c0d801182d5404000f6604a40c40309500c0c01c19003000c010703140c0904400c682e8110004e20110010703689110340d6034014100354507880302c1400c403680e0101000c080d01000b0b1014440c0c0c500b01441c00391a800107180c0308515030a2580c0007403143d400e1722110380242c02c1c1d1030740c0b01c0e1071201d900c0400d0080e602840701114984010000000c1080204004e54064141d041100e20100d409090040000e49403148424540e2400c1061007c2c658022488002d060301d2420711b14203445a21141040407061980a0090354054004101391106d078240d0101d001d800c00403085800544 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 144049892 1250 144048642 144048673
    0x218010c0f0209042109050a060e181f0806010e0714090904080904140408040501050f04170d090e060a030b04020103230a060b04030206030109150909030309020a091406120109020405010e09 83
    0x7e00c201500320740c5003c2e0500685201d40c15918440601070500c41e2a010741c003ca42241c1740007244c45581020340c090340c3c4c0c02080c03070700c6214131300610b0b0b15401040594100a4007035500c03040070f40311500b40003010030240c410400c40400d465180a009007213201c1d41c40c0500300080307180e1140070700314829407801030708030001e10b0342000c450b0056400690031400c0c0341c1401d00541e06c3e5406248074405114041c40001603090050003801040f5141101500900802c1007024003040d0850304030341a01007240f01001b10548034500c00108598000000c0c070356035180c600040c4d00400100c403004210581c40d01108031501070961029014441c0c01804000881c2c0d214401c440c03a004900009500c9401040100105c480741d4104c2d40e030f0070902d00054081030707507140310000460b542c500c0210301194403021144150702d0030b180c40c40010244080701348040044040b060750107800c02080607100389940c0a641c55110402d40c001c00002c0c6d40940100140e5031100172003d0920f42c1150b5a048600c2a00e1080b50000d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 144051142 1250 144049892 144049907
    0x10605011b050a170c0703080c01050f09120f040510080105030c011106060d050127060609060b0a11030f0403080304140a3f0f120218010c0f02090421 66
    0x1d40200143c55828070350b0342c03141840529035102c40b901150a001014480d201803041e44010343c8140311469880e56881072070741c04c0da040100001a48410301c4204400b008010400046070226200410703580d04d12401c0320f06047c056604010303002440360b04500b000f41c1d00552800e060b640100c00711016005408011910f2414146501c82c5039001b4a0210b45281000440a5407051140c0004074031240060b000002c0622441c40002d100840e40c44500140001d62040030f000d02410721082c4000c03414641c105003280301d1050240c2c00c200c00b040c0310805244050058544644402c558556656528105103402d600305680554051484400e400c0c420340300042c0110b41c1035440100d40d2503010301841d0f95144051090400f04d5294483d04800300c1c0d602820007134401d0074405494412000166000041084400e00c0300c641c81c06204010b1024001d1114007958881007091a0203200c404251410b40584948040c0c000d40280d031100500c0304009040c40041c102c0d4401d506140b1046008075400c84444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 144052392 1250 144051142 144051197
    0x6030c090e2205030d020f03071e05190908031615051015020309040203190b01020a150b0105040b0705010603030f140f0c0307050703031e02160902030915040501060501 74
    0x88180e010228540ba42003162006181c0214203690401c0324006051050381c2c4080d40c0900d4807480042000351203900945064110b03040c90640000201c07102002030041c1c454016a8041a00d2010310742030090300c03d03282040502590000e0325141c005420b20130b450000089802c0321111501b0410585028961160720712401c0710b400442d003400e1806030310070600c58090a4074000c40c001040051010340b1103000450107000c00c0d4800c64030780300308107044008441c0b001100c2d5045400c46945e080129000b45a01801445844030004038a4050b000680300e51242c3d510080c1701c490042105000d001c03046d400501120300907100e006005032040802c88030350010a8060201000078000c440c180319011000d041c9803100c00c1c007201c0c42c20426807aa07628141c02944214002102d4907040c422003a000804813110203220700080c00d01030481400d0074401542030041400f0558003000240c60707400d040000d82180b00701300c207024405080c030703040240c06442c036030042c18085a000050012603104152606440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 144053642 1250 144052392 144052411
    0x912120213060c02063601020a030c0b07031404120809120f160609060e070b090f04050603032709010605041d04141915021201030b060d0c06030c090e 66
    0x1081c02d211058a03100c01900b400da070400c0302031000c240c102d0703001d0007240340b110850459801808a42044000d9403032031a0106811504003c000400198000492028040d400960b807001903881301d40480007405450003605842660b2820311040c004801101d45101006544060300c55840310300c0140d9404c1e42c10402100b010f8100908a000d9070103030068007607400c0a102d560201d2019031103c105072207100000795882c5950300c40a1209180401031000141080025079060225a100060308417010030140c900450f2104001011039a050044400c2c84028000302d0510364042804154284002d8035910f0107000d0600010031214020000d403000c8640301c0392500100d80324103c80b0890b07003201a200700c410788100c110099080754144000122805080502424050542070140c00d103045620030048003441005591001520b032070f01c0c18152030704440d000d82c01703840d0000450820b075107041c0301414401c4400004200182e25070800e01450045070394000f12545c451081e00700b503010079204500c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 144054892 1250 144053642 144053677
    0x906050403030c03140c010c030b0405060f2b032307020604060e01020708010c020a110d020a03120c0203030a030b01021c2102090316051c081206060c0109121202 71
    0xf40f19407800a44544285000c1d0795401114159035415040b904541d05165141d801c5000a1989417084da644840215801d101e2414640007180420032501d40d00e40c00b8040c00309104200c6e014050741c10070103180c1c08813440c403802180c0c2401030610980416030007001505c0f03d89003a4070800103050341e481c182c0003400e06241070700d0104144c5400303a10792103003410350103400c10000c1c4805c002c2c818603242203159006004184080c0c502010111b444c0c0b0300d01c503c01c0369a4407070710307015031518098041900d5001c038600451000b40d290075a0720b9030389500002d50501c400110b031007105a154101c143e501d04280c0071100d1a44d00300308403680100d40b102d10040000e0444031584282008001121201205a00018640180b840102e030400d1108022400c0c003410040c800c03c110300b4800101032501250585c0e0351809003a07959044010300c140618552840380100100d10f042ea90364046590403529403000b041f84514500e0b00f1400c2c991034a04030b401256110102d401c104503180205e80554440311005074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 144056142 1250 144054892 144054899
    0x705030a05070c0b07030203150415090c12020301120b0702010e0d030b0f15030105010e0604030c031704180615030c021f06030b0f1b090d0b1503100e01050709060504 73
    0x4000e0030000c01003003c00c1510550300d00880c02508545005050329900542e0360300e0800c81d01415811b1044e0281c2c02a45088041005800003a01c0c00d82601c40300707070010400a500ba1404c5491802e202d20074450b0f00c0c4000b00014099598490310108540b142108a403540c1d11940280d088800c160200000754229010408445101c1c5d804104442d0000300304200e800380c80004143c0c41040d5483d440801e07880003005000e290b8200035200300400003200c43d14034060540d80d80030307907001f285e100040040c1c4007044000060190402501c0190100b400f101240c42c034890004d402424161003084201800003560b094080c0c461302691040406540007420114a000c00c45010240541d040c040510794880c00400014204080207001e20400315000c0c002d4180a00d44521540782c0d40140d44082c0000c000d1100306071100f4a000e180075420004080c490f940d0b01d0042491280398094042d454005d01440003426402d81e0b000b00880c0382140005c11040e40d0302d0320140c4503c600f80c00b0b4440070510500040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 144057392 1250 144056142 144056161
    0xf03090901050d0803130228052e050d020d0905010f05010605130b0d0f1b12140109050907050303042706120213060f2607050f0d03110a0303050609010e070503 70
    0x1d43d031b0701d0702c01307040c58141034110200c0d421180000801c0c64a100a200010030440c50503400c010711a0512090007402400460094946139804030f0f0b00800f802004917042418003450341c155640100580014000e024542c5802030080c6002403200710703111b26050002ca006489141500c0034030784032240380c04150342032034034422190700030300300403070082e500c0d0020301140781307101d0003250400c8400c0d2400901c1c0c0c0042c04c802814545820795000115445c017001a20400381d20400c1c00d044401503c0c1c00940e40c1c42c0c0ca20042c1c103200c0103802a580508c00080d00040648095404020f051481c4040110b107070320324503600050f20b05501c00c5040380c2d0400300288000d458000da601b50f2045010000003541692250070044116075076100180001000b81480c024011101c4c69801d1044200043c1c00c5041c2018001082020b92462960288500c20180c408140c041c0c1c07860070440030303520201c0c0c0383c1030414a0020003400341243c207140601d00703000001079a12423104030a4000c5413981c945034217558407038041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 144058642 1250 144057392 144057421
    0xd0c03150b0a090b0d06090602130618030b090a240b0411030402060f07050d0801050f03030702011e021006140102010b0d050d080606090d03080a1505220e0f03090901050d0803 77
    0x1880d8018945c4003100d001a2542c0316107a90385205540158444608914441d0000c9280e8001c00c1849108904507071100d480700558810360783d001c2568032040d1650004079150100c40b0360000c00c2e10031403e0300410001c0300420007040d01c00008005000010155050009651481d685105903000600110300180340c0140604078a03050b010385942010301580f2a24985041488214081082180180228140030300185a40e4030203030020752520100c1e60000300303401109101c4210100a22540d148071520a004405000d20440e206100c0b0b6070315205483d0000c0e00d10200c141c05507280c02001100350400840004006411001810f9802082c0b81d00761000c00000303208950004007009000e000d550741008000c4054001e50f902c011a2030a00c42c1c1d04212008880090000c01c2c602e9130070015551610320800f03032540ca00840100c0340c1202415140500400030b0603a40c40e004074500406129000805420100130032520300c860790f42d0350340500480d40c81140014108030410400103804007044600c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 144059892 1250 144058642 144058661
    0x5010b040305031b0a02130902010306120f0b0c0912010e0705010c210513080307062f13050301050108101425020c0a090e060c0a020307020904050c0d0c03150b0a09 72
    0x1c1d01e8540b40c6035130001d08200480c0701d030403007c15582e00c101400d65130300d84a80703000b030400000c1003000307100e20b504d500615844001004140008050000740010205003e80301040e9024100c8829030b2100c1c2e00c80c6020780750020340308c1078a12800c00300003485e40c0b103206070140d002d40100d0681c0d4040004410310640e11000c10b15030b814080e041100c8003400300d100c2d0003079004098020107151911030510b41101a80e80f0312891451400442a0158840d00e65484281640401d540040d559110300704128054524582c02554036503c1c207000000c003603201142110303062440b00340800003200310460f03840d0790020954a031000000704102080c40100b0034000710305031165600495000c200301100250080816404c412103050302c806055072906000c00020750019a405080b42c142a01c20350025640c0c00740f014042d00c14440700022a090103c14412102185e00140c0700030701065041c01c100000c511075100c21500501c7c4551443c0d8601e03114450360045220040095124524044200000e86036652 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 144061142 1250 144059892 144059947
    0x6010f18120803060f0102070e06040c09080d03020703020d0201020711010e21070f17030906130f12020109080d2f010501120b0c03010b030408070804050303030403021005010b04030503 81
    0x3a03000c503403298803045640d0824410840300e070b0340e031501070140719411a034170105505540c0166000c3c482d0502003105c182e44810160340004c0d00103061003044507224000d52040b4128050a91221607807070b4550001c0c2a01406a0220351003602c007820300720300f01e00c61514081d02d000d103045074441a41d8841c14100b040004001c109504441c45003503042c811804400025070142c0c405c2c1020071080c0d0080722854000d2001c1191140301200803c4020307203070b00c03075074101920480c800200200145480302c030003005058961190741215481e00d13a100714400c0038003030a9003c9640920b00141c0b0a100107008521407069a40d2240011610601d243d081005d6401c0481001503010404a01c00e1007480b5a5000b09480101c1c5800ca2103a810f107000903446c05003403807240741001c00041c0041c80c25a001c0b650002da0101d48070740d4584050424400502440d00843e43c103000000600062540c000307a900c0850444caa400c0005076643d10004030944200c1c030000b0415007090042c01d020b00c1500e41042c00410400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 144062392 1250 144061142 144061187
    0x150b0d18060203160908030c07140a03080a05090f0405161d0d0f0605010e060307060e0f040212060a08060105030a080c010b03030c030a080606030709030f02220603020102010e0606010f 81
    0x150303500ca0030b9030030031903468019104150f4101c0c0d01c40d50040115004001d01c901862411145658413038a42090b0f009850003100141c41c1c107003440e00c13900f41074001580c014590302e4698807810070007003203039100081080c4200c0440a09220520b418030885001d0046440310441c00040a130b019070303000204100c250b00800c014013000700262641800700210714841c1e14000003a55141c5403000480d80180c01140601141c9402c201c86500c00080d00c3d420344d01c403818024061007600000426440c160100c0c00d8100303002140c10040c002c0943e031694003540c000c480c400c003840e4543c40229690602485080c3c0e044e44903100b2400440c1201000309481c91031100049144403940f4082032175035000307050ba0404d035031000508a41043e80b04802d150803045c101c0d83c0b145942403540c0000c045140da4040075001100a40d0048210b41d03546151104050341e8201c4600c842001d072204400408a502c002d9001d5401c0101481d05180081005441144c05071552101c007500402c08498440110b4166602100035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 144063642 1250 144062392 144062441
    0x10e01120b0a05060a0207090f023108070e06100309051b0418030206160806030d0305150a06050c010605060f03041407090e07230a06031e0e060703150b0d 68
    0x19440282030481c0990000d0466234941071103c070455901041c01200c1720b106000b510340c80031007500b0019040c00714207400c0120551451080e26000090f44c42183ca82c42174039400503008a40c1c101c030b00e01c50242210503658082100c0415010381d0a0010014001d4200b60307002e0310040001040d5046162020704005030046403603800c004a01c24001090b4050f0740200c0402c24240f03c86240d088000c860391030280502c1c10701801095641e2036500c040d00a044c1c036a0001003142d05100032449900710000e0618408966a900c06001940300c911810055402c0c64804200345c1062012202034000e49600e071860355450b6169042502104601100507010b04074000505540b1800b42c2042800c1e120b01808419241504018925400d01c18880940d90a09034010095071001488400c94001d402c02054050b14041c03601a05e00c100140f01840c42d1030500e0403c001500040c0561055455403410000024107088040c5403084600c42d2007014a001c1041784aaa0f4054100312004440301c014180800c08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 144064748 1106 144063642 144063649
    0x6031204030803070c02100806090901060e0105280603060e0709050f0d170a2c1f0201060320090105040b030c0d0812070203030114010e01120b0a05 65
    0x10040f001a0801d40610445640c866008104080c00000c00e4400b0f440c0f1241511064042ca00c014005048000305101e20401c0e101002d241c030900740e18080410005517006e0300480c1c64012113a001500900741c1c800524082d00c0781d0349000c10303000c1c1003003203407561280001d0890041140e01601000551598070032004101c2c01a41d00b103150f00c895051007046034440549100580b800000e1010302941e102100c0950044030310101302144c10340c2e6417990069550445015840407040342034410340800d01130000c214015900000c90860b5032511403e109a11480070031940c00c010120500c1c03646001003d540c054070f1b003150100101a03000000c02c0d60b60070b4010909010318134101024017800b5180d000d40342403041d100048201403401400080d00c9400c288190f15806001c0640c0030501e6000d61101904c0420603520754900507020a80365002d451241c5413203400013071040d008030703260300c = true := by decide +kernel

theorem cover : BRFrame.Cov 143884892 144064748 := by
  have h0 := BRFrame.cov_init 143884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 143884892 ≤ n) (h2 : n < 144064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
