-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0119
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:56:14.087028+00:00
-- url     : https://prove2.me/submissions/2cd0f186-b64e-4aaa-8aba-e7e63a7a6dac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 21223027 ≤ n < 21402883 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 21224277 1250 21223027 21223051
    0x81512010e010c020d09150809030904050412030e0f0a03080c0f0d0603110301090f0210090806090a050105070903050a2004020a020f0d090305030405060c1203040308150d030e091801090605 83
    0xc03590745c00b100c0444040c810308840c0c44130740000d10106841460b040c2d800080c01002c49040c06400c1d0002012204282d8040b58030325512150b100300345405000b15441d030a410b001624203035000300402525090003c000508000380440001d0131590350f42c00340c13a00c812519852070307103c07060320580100418080c041a51500748655035035030315103014010140c40a502500c0c01f49514001e40c2802011120304050f01c0500885202c003280010f42040894442c100c0c00e0010b15030450503043c11400c44030060000410009003032000c0c0003142c80024459055580109140001d040702e032140c1561076600d002c01035105000141e0001c0d066400180400d03014031090558050040554064035100720602c07004006410034030081100740713400340c090040d100c10f030b8040d2204c07003a188000d04c030076a10840d0f04a01084414050040c64217407015442c404402c16212103010090703d032406030081b612075003011300c130301c0086002820120101820001149807007009100e1490b4510b0404040c2c10100e6000c480f100d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 21225527 1250 21224277 21224293
    0xa080f0a0204050f0c0712030e0316020a060309020105070f020a030c1d0108030a0f03021804050f0403020606030d090e04050a020405010902180f010507080d0608031206030c10081512010e010c02 85
    0x65180251500542c01801510306c0c08221b03075034080250005641140a01d580c1da40084003080b014001061a4211800300203101c034034a204018650740e030b0fa004002010701d44007681005076002003c844503281c0104190a2207042840010f4070310b00181c00091a15120b0007002940c01c15940c06e40e405005460488621a83c980c11042d54038000c2e6650000007490500380c001e580343c0658000c0c1965201111514101c3c6008008241510b000352900740f815034a010800c018950306010180d000541140501a28151030000800e41e01c42d900a4640c01c0700c80c080414100031b410131842219540c040c005000940c0c1d40c0e15404000e4010a6900d10003c0031000781c0412481c000c0314059914105031116401d2405644032210b00360404d2a502144545d034000104500314100007500800044850511403031600f00f05150402d100d4940c0580500c15000901c0c55060300489a00e90207162665000d03090711281c000151031403c5c0b040302d00c0380c1d546804115058006d0641180c02200032607001c54541d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 21226777 1250 21225527 21225541
    0xd0803041a060108060d080c0f030705100c0806040e010e010509030408070614030f0712020c070302040c05030f0a020c0c06040906080705031f090609080a0c02040501050a030b0a0504020a080f0a020405 88
    0x803900031141d00d800034088130001034417841d003c541c26402c10300420003182008954121b9510301a100052207041d5800481c09a007000410044641c0c0c640d56040280803520040c8405013402e500940308074490340c0c83e46003550a40e202544078205004c1d408000748621f00708110369545a07489405184114010408003040550151400d403602d1440c14072580d20b95a504c4501d845001e5019004000300010761580b160b424500d40080d001c0011482c01500000c2d18520400c0101c40303039942d00703105020081c0304000302e02104528455014a43c0c2c500503a43d40c02d01c248160030b01882e034021130303444007021502090841340c2d0340c00402691105000c480c12652200109070b603e84600714140c0d01c180440840ba40c1d403081c6a0000703483c1d68414403002c102448141c2d1520b00942100d0f0b0204000b402400d1403100703514040c09120f0060805458507007141c0d08646411207100d100070b251110171a00c5034049011505e0748242c0b4001884200291604090618405503c9842000d400d900c60782c18100804e83d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 21228027 1250 21226777 21226823
    0x10f05040c050702061602090703020a02060f0112020d1502040e150f0907030e0307060c08070e0a0605070314040306020a05040311040c200106091d1b09040b090a020d080304 76
    0x10402d448240c1001680c0c0d080114035481041c481e10001e01d00c103071040050711040e441074010101c40d10701503210254200d000b8981100288104280784090300100126001c8c00c8841e0201d82c0c0581d0b960860f288507060419100c13511000203941c49200090001b5600107007010b46005060303084800507120350503410400c21442c1c172100690301881e114041101d180c001c0c0e0150071403001c0c45098030306005898660204954003000c002d40460605420090700c0c030b9000103800b0004104031412440213082100040c485c2c091408000d040c05804090b009134100c080054800855001e281903558070300c0510010016003080c0300441d01d4000300c4400408070310b0180100e02981d0425603c1803110950441d0b0b440000c07060001160055680b400c02060030159801460300940840043c6203118500d002c01614100c10f08400340c400043d0040076640c965a6070f5010754015403c003462400e20388928815606096803154000e5014003a82c0c0d904040240b40000f640c441c60052541c80110011503254001e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 21229277 1250 21228027 21228041
    0x60d0e07080102120606130b0708040e180601090f0204050d1a0a02090303090907030905010c0e030d09030c0608040804080a0c14090708060909010f050c09150a0504150e031005010f0504 81
    0x1320b0444100000c0039820004050321440c9100c40c244c00d1140d58034000055030b94045642910000c000150071300002c881c040361f503038200e86030b828000641004030540d15183c582c103000f450800380e02e6516507440c1c40041c1d01610068a4020002450340070f151034408203c0f800041c0301c0d529480c8000c0003c22541c12351003640c0c50780402030091031901c0700c90303030411101060040039035040c9a907810b200d602041092003071610407051034503110466080d941c100361030104804400810402411014070001d2032a06110003100c880703060078070064607640340060990103550010201c4c0e01c242c1a034502808543c84211003225000260a8688251171040c0103021074110b40405c08140a4008215541410000d843e4071824000002410b078114000c4102075035030664800c0780250340401d920846140a000c149040666481400d20340307441000f001c0c1082c0168854000040000600c0e03e1229019410303c24404030024152901e5030500080034004007022301410b0b007120b10203a404540b80c1898401d900c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 21230527 1250 21229277 21229297
    0x30106020c0d0c0e0f060f0f0a03020d0c030807050c010306090603260c031309050c041203050a05041a0307030c0504080703060905070b040626060901031b05060d0e07080102 76
    0x4035001c8051103440000340c4821100c0c005410000180c40e400260010700560b04048078180a06158040008803040501d0f032074482d00e1011151019503039003803858401c803a030554541d8800c004074200601900c0c05940f000c0c1075880001101410004c011500d100340401c2600c0c1040302e40d864050000440700c1c0d42c0070042c586180c50041ca01c07003403002a08864440b244090740c0340f4000803d00401d085800078105801541c0014906103c0c1c500c05000c2c8903031055007800c095090034500050080f4180e241e41c00502482400030350007142611880c01c403000380100c0040c0101e943c1880c07408081c558007c03100800040c4c941301c41402c4052003a011903049442d194001c18070281940c9890004040320a8101c910b403140c0b000000e0300301c01c0040500003c10403501e91240c24802c0d81c0003001d8849507a01c0c0c1140c0c00a0f1402004804d80c0d884510905494000c0441d10092b16a009880d1304040c2d00d0b0001c1d903101401046100d001207507500329030f004a050f1416039503440c0d61200a58240c0c01001500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 21231777 1250 21230527 21230533
    0xd0509060c030703020d060305010c1701090509030a050c0a020d0c03020306070206010f1703130806220f12271e050603070309030903080304080d05010b03060f0609180c0307031103010602 82
    0x1040e4400d04c40d4004e005620024a000a4410b0f039a41d201d031300b1a480326065070082980f11a40c01d0121a58204080c010980d0b030070301b40064680b05006940741d100308c0305458180800407606000e0b0301410045208400d0f8050080c01900c1d07520304081007811113611049129104e07800c000b41d8060703c0869018101c90b0030301c1101e08250b0800b070070190f824a404840d5055440148018101e840718102c80a0007868680e003e400c0b03905000d9007980382c594028015604034045803c0701c1000075051500c080301640c000d07080d511546140c3c0c50885810100310700b02c100240034645081030b640c18802c01d200c01c5407800690201400343c5039044a0041c1203510446622280074800a091140607420212a00344245405e0181c02c1d1a039852040c507030000d03503090b40e8410003c500e0b950310300d40c50b01c40c1502421302c030b60a641c258508040040c84000611000318024500031a031400c4544071030610904070080e00107030f0a01440d0041303520070903401c21038000c8000b0b401c12591100c1c0c40700b0101140e0603100e40382d000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 21233027 1250 21231777 21231781
    0xf0108090309030a0b0114061306120212090c0306090c22140901090c0501030203060f0d02031c1805010903080406030c12090303090c080d0e040f02070f05030d0509060c03 75
    0x64458540080100c001400308000140490b42d00784502c0311482d10648440a5035410a83c01d00542d0700da0b021a10300481d070400c0342940c1e900c491300107242107980034604506121607010000019000d180310285e48071612109000e000c2c1d00120380c600010600340e08030b41c856602e48003440c2e40c4140030510075410404140e04000c0b0340343e044041d1046061168008100e08200f03085c0e00700c14000445010b07070181d5403006401c00308a05180c5450041209103030560030360800c00e000501c412000f41c5079611910845920200710340301444465280c0302c01c1807c0003078281e510100074041c070f0103028a0103d829503800000c2029070190081d0310030380740c0001e019410b140c144803003517006040940002c4140078021442061604560080c80110f510943e00030400305554038048040c0c113074075005102d00d504561903548480d940502c4001c01c2c100101c2c1c000c100c0c410b0340c0d85104004e104040c1c01400b80d02440c20004144940000105260781c030344002000f032680c0d016520340d00c0d60800d030780d150318107501000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 21234277 1250 21233027 21233029
    0x60306071404092301031a07050708030c090a0801020406020d090e010e0105090408071e2013020703050403020303042603070b04060e010b0901030b01090b03030702030a020d08070b0f04060c030b0f 86
    0x1210f184006914420034915094540000062840983c0203c44824030101c1c0452094500e00d0303565000300c01e5003270560030010140c0c0c805502d0b0100401a241717186003c12075817103036641c0201c0000140f1041000b10356840c0c03151002511030404e03007449008901d98250002c2c09208040e0181c0c12a2030180c1e8411080e402c3c481042000f400280080d1412440ad00120001c01c1e10960103d048039409600d06003032039180c0c03404852514070116040140c800100c1c0180840d107800012a600b80c0b410030b80180d4904140c03400313403144e029a800194042c8404107011800d40c5183c05502400403001761070300c074440c4203442100d07a02c2c070030100010a0ba062100120700010300a030402c2c050005808004104040050007180b81c1910980c03050300c0c3c01c00c4440041000d00762610845103a00021340c061450700d49a42c001ca503840740350302c00027030045c08005034141c00e00c9072620544d10324650240210b002030901c243c03c4594140c051b58255400340c03500c80041142400781c4140c400060380030f0103007160082520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 21235527 1250 21234277 21234281
    0x2109040b01110c0607032d1e0c1707050f0a050f0d050a08060a08010507080402040e0a0807171204080406020d1b0204050903160605041a0603070b0903010906020d0506030607140409 79
    0x500221b0510501030040910b107040b0010000c0728820b0005480300d0b41503002c034018040d604c09040041141815000050240e500816424845801c6141420040050071404146100b0002c018001c3d01a000240703402b000042003580300303d40503404560b103901078030404540b1101c0030130144010900400503010b032503028944841d40702000611815000784d6419640e829224111414400219a24204001c600d0306200301c00f03117545000010240040c031030762007288600c664107015145100030403003103111114100440307460172000e01c2036203540d081a1a041031243c000d0300800d0090b000702c21701c0e1903101784500c100848441140c1c1d80c3c1c0a0400d0701c0d400f40b00040402030400c0d41580810000881210701d440f00c90400b5910400c000119031505007096040c00455848da04000c204040901a860754000783c210140c840051031180d0b034082040001c1c1c018542e06000034007060000c80c2003145044c90f0342c8068417504041d810740d0301941d00e4510466622044482024845c5824403003400186816 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 21236777 1250 21235527 21235537
    0x310020d06050f01030213120303090209090307030908010c0e04090204230702070608060a03020607020f060313050601050a1d0a090b01060c0b0a0b0102071701180b06030708030702030304030209040201022109040b01110c06 97
    0x80c0ad0014007410030b50041039080c502281d6600b0581e2002814804050303020403584010207a0724001c04c107003c20600000d00c55805079001511458a604015040d556070b0380c44072041400164500c0d1a072800740030078160400c8103c4444d400350240a6000072403034040d1483c03600c80e00000300800710103030440c0d0810842d5040403030266080844034000a15a40381c55000b1030044d0032400305101b41c4030941c50311900d002c0058002c3c80c041c640d601801c000001d103403220840064000a40305045580d6404040002c0410345000782043d40b6890000032031075003081d0110611401607220b41c15503500d0340115400c0e00c00c400768050050b0f102c2d84041180c0381c01d40c0e04114044840360008a115050344206100884400009850300e4151b181032000341e1408001801c000c2652034051420001e04c0d0b00086d840e4021848040c1c00381d5041c00004046a20070301c00300d00440d803030781c4500c0303640d040d051900701c059048015118080c6140090300d080070742c029000106c541e14400c00402509001800303001c00c80c1c100f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 21238027 1250 21236777 21236783
    0x803091e01020d06050103061a0318060703050601030c02010506090c0a02190516081f020702010504120501050402040b0117010b0a05040308070f150e060a0b0310020d06050f0103021312 81
    0x40381188980c1101004800820886140015032900c81c51030a0004441c41548040c2c113141c540780c0300304880c0000c0760464001c00e1700c03842e0782a2a661503190020000a10788400212809044d00704021250541c0c05907008002c00c0e0303002c116a049504040c2e00300c80c001d440300703603000041d940003403003c1c1e024100074000d03070030360748182e581d4203174502034a0f0003548030440b00301c8064000301900010140007141001c01407050000403e19070542c51100340d0121410142c00143c2c41e0000348000659000301e0132100202505108040100c0742c41c2025802080199003c910540c1003000c0d0a00b04c0d0b2044851800e49402452032594a911788082a40c240c0c3c403640008051140502c03001000c10100805005518059100f072250210f880c5004111b201c500700c9040c41d80751a20701401200d401c0000c01c00d0340b240728040002080101200003900d081e00d000980208140001640c02c2e1800380e0740c0225085440a44100c040038084900540a0b4001c5103500f0707800d448413400400090502910f03846900740 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 21239277 1250 21238027 21238033
    0x20d030e040903110607022b0302090a0617060307051305040507082b0203030408040b0306010e0406090608010b030c030d081302210616020d030b0a09021908070c0201020a080309 78
    0x15450001ca016901511000e42c0419008401e1205000042c42042d0340045a413002e803514020381d801d011407803540080d40c0b01d6040b0110b24a450a6030203641168042d15004098101d816500c1d0700c018508221b20391140340001c00c40c00803c62500f400540c00c401c2c2c41c0d00910040078040c203c10303010010305008006854610076031100103413101d414410404801c4401c10461680404c0090554403a40c0c0303090400304546c410810440400d86000a69081d40c0b030380400c6540e26280d4800403551405003110b41640a46000400100721000e58850700450308510000d00001d01c5a03410507880d002440c64154040d003201c3d58051400b44204070f0f1079888044020800c500c1685e64010851742e00021441c41116540036a05000c07030304042008560091525012240c60b040d000002500d400d0910322010505440d0000e1a08607541e00e18081c1c050402c4800454840d0b920605071702e4031445000214011a030030001054600d40300d00419012039406170002d1030413208a644c0c403e1907601c003c1c103040c9640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 21240527 1250 21239277 21239297
    0x160e040204050603270f0601050120010e0f010e010510090e10020c0c18100611010207021e041113030b0703020702090f01080601060c03081603020403020603010303091809030c020d03 80
    0x1607200c0c4007039400754141e010490620241d82c5d5144001c4204140c0e180280e80c0410b080b81008580010180d05491007071900030340c51075206948840d00085070503031810a508207005240b4442d00020441002d140c075030005d1043e10f151040c440e0032902c003922517600c0b20020700c0050000c81c020340c11820300c4940b5030046170040c0d10000680380881e001545640003603044003011104510b40b424401c0c01403110701011180ca410459907040c0c45807014070510060000302c240d10303020501d00b941a50460798025241e030102e644644117041c0201c80441003184500d2a0002d0302c0400314025055840c180c401290317120707126086480c0c09030740a00c024810b0040580030801e100c0140c45040c0300364024207001c10200850b50400600d2414104140c00600c1080403580001001c0f9600500316908541110010b02c40c0800c4100204c0280c841e0f80c00294122400000020425510512590441e03003000010b00c2c47e540426400d4080d61460344c006800540000c1c051405032801720036441030207100742011101780c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 21241777 1250 21240527 21240529
    0x6090a08030711031c0c061d07030b010801050c030106020a060b040609090501021c0506010903031b05030c0f01050c0403030c0b07031d0304050103180b0c030a090c0b071406160e04020405 82
    0x541d00000d0102ca01e10b00c3c0040003005420300300503005800262200d541c4a00c1d058030b40007800f4580701030b40645520744500250040724000d98501440340006400d403010389403603045c5040c2c0200d081c86000703113561038540003441441c1c0c0300c1c09482c169400341e40a0120040d43e80c8a013400340c108280c80f20342c465662100001d52006910400c0e41c0741d817003500096110108402000300001d04c3c0c46003038032428200001c0000580c1d1001d07000c0241d9515007410398200b0a9018002c1d03180aa4000c014000e1000045019a10b80c0c00240f00d000440210f000f07114503138842c442003801e40614032008020032010100000002e690188030f96004025140004500c980c0c0110407001d90745004400743e45030030001d0244005e580c94040c100a201d1031401500c1045007030303510300340150401042c110381e110380400481c00380c01254210340c00464103c50340340ea000351201504045d40e0b200840c100c441c9807030640c10044103580481e12504c1a40c0180f00b4881c114031024042c0ca000700c845034038a82c01a0b0800001c111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 21243027 1250 21241777 21241783
    0xf06011e09050d06060905060108010b160809030303070207030c06090602100b040b130b0307050603010509060909190c060933110105130b0f040807081c090302060601080a06060206010506090a08 85
    0x5080c0510340104150b85003031084400c130340001e02123a0400c203910b00140551a6507808441c00c07504005052480c101107806c0041a900070210510362500000051040d40f40c2d00092520075a40100800034032540c0e90030003070b28a400d85100391343c0940c014903141002c00119a0112075a1031001e4401300700c202d081c1c0b0004401d02c42441110b0032003070b500c00c510f0b125803d0811404002e0f00301911075620b0f41d4144800a140001e0043c01d241c401d496090002e80910824041c10b2407205081c130180c100c3c20460714160040c03101e030340140c0c00090150100000d45138803031911000c000c101c09130f4810050030301e0780d0101c80903008280c40070144590f800303803030040348070034441c0030f22503001590605076038102481e0188014501500b40320800810400340404241454106d8204c60303440000a6581d002c00401030300141c0f204003030a00c07030501e8149805d003450340100e0590f110708801d0b6210781c410381c2d400d007151080366124092040182d20140041c1702d5410300e24010100c0c48001420912540d54401241e40303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 21244277 1250 21243027 21243049
    0x11d030607090602060105010207060507151805011e020703120e03190809010e070513050402010c170d0b04180305070f1211150106080c070f02030d11060f06011e0905 73
    0x800070b114010704010140d41800300310702405092000d4910329280040044c5140605107010b0800ca12a0a01c03d0134204142d111100b8215104074140e40580c060810500804030901007000c2d00508008540c0e52440340d100301e80c0d00e16419103d80a5502d2641e0310100280f40500e445000c42c801044500c1c401c890b0100030101c04e6160740d0710b00d920303482c15098240c207403924901046d5240c1e1203d40c0a12055580302c0824075400c00444002419565030b00048405d036411150103094034004103150010400c0c81c0004103440c54000c41c017401245d000d10300381720031942103084c030360104858413842ea0002840f41004001240c0076490041840010f502c4001c40e040c5040e207181c002c90580688110414001e12010080005440c10040c1c0c80d0703d0540301070182003000380032a078401c1d00003402c00e00308140a043c024559030040d00316030803600707904030160102a0102180d003942c810840042c4400c070301c0742c40c1b80f0700c201c4041e0f599062007449541000341c0980100025420300582d8034000c505600c03080a221 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 21245527 1250 21244277 21244291
    0x1c020c0106030c05060415050a02120f04030302061b0301120206070c0906150309030e040b1804050c040614060a050a1106090604020907030b0a03260d020403021518011d0306 76
    0x640c042c514900948820700a80c04140942010301c8200030000b000789141c01c2d040c1560030801e0b03440385100340c228108070400100c030f41000404100810142006405003007520b00c286c08494503500c07a039200c030701807400c4c03441c40d0b102c443c104000604c04011a1145800e2507480074004a06000182d80d03214440841508184030341c1d80e5402d0b0070045a1001c0c003200510621504080000700d50a03100248003030514440c450103540c43d10113000e05610f90b00402d00b0346041c07455011007241000c7c90440e4907020541c0380a4070481c105400030401c0102810083e03407160004044170319145010400392000d40061025105000d0341c0300000c10148402d01003544252000000b8120900d068810000da16401512480c20503140550285441d1122031054081d80d4100d07080c4030b48640c05a903506079a81c030301c011400300391030003103140c440d00822600a401520301c02c803150541d0003c0d40031121828011781030700141d03048a1110704080ca5010b840c40321005104010290303201408031002c603103031500078ae83e14 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 21246777 1250 21245527 21245531
    0x6040e0a050f04030903170405040f0c020106050402090307050d0c05031207060c050a080411040e03040608010305010f0b0d24020708030f16090302120309030109030504080f071a1c020c01 82
    0x8050144284501684000b40100120441c00c20f610000c1c114815030000818150101c03107100b491800e0742042c0c03801060010002d2164108008004000d0142800d02402540c2880c1d000300c0d5070300d018000e585290101400a0442a2421040201c00d040019098a104012807004615034500381301600150100e0300d00ca80c5e17103002c98038000080390f117000403181c1004001d12007080300a500a070b030740e0340140d00080320000344410000051700501c4190304000d664480010300007840c98025001a040760b014100800402100601c020280e48101c940154000803414001c5c0014440c020403c1f0000d82c104843c0e612080001c00202c103c3e4803418013550402400310030401455000e0141a0780007030041c1c10207180ba280e50f070000d014860035010085c03080c094081100c9030301e1010419681c414070010001d01554840d820301034480c2c3c0c014016410b20307000d03c648407000c0f0140003c24800b00c41080c80340c500e2100340019a09066001110318652000c0311045c02080402c150001c0d04030942c0d42400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 21248027 1250 21246777 21246781
    0x110607060c051305040204150309140303090a020f040615110c0405010905040b06030f030910020a0c0e090607020609030301030212010209090a02030a0f090f0b0603070803040909110108090a1202010b06040e 90
    0x7000b00d10308551300c05481140100401d014423010f40c01840c5101c0c1860401241c0080c1d546043c0802c1021406019918031000c020000444400220407958600a0b2012015050503600744001c0e00c05034041c4100148021038242c01c402c0c0325004001c000c51801045e0754400d03002c0e00000d07041d01d80a0348800c80560700c2c0e200b48014000005100c07500100118010b004098010b2442d503180d01800d01c019200304820301d003c8503424000e021141146922141d06606c207078480e040503100100a03103081110348106000201070500004500f401104410015801c6a107198208080d0504404c02829a5502803101c000303e40c54145150340265030b0b20a02507200d00e030003410f54007251803003950368001505154800c070229a1001c00092095082041748415a0341c1001081c64100d0a50003a05139200002d00054404103541c000755074280709010703220006066400440f002b88080c1c07824003248c1c200d41a0000000c11903000303080c03200d03003500010503146031150010f14a50090344c0107030b040c0508002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 21249277 1250 21248027 21248047
    0x2838010803030106030e1903030f02040308040801020a020d23030601120e06011806060e0409050c0307060c020405011401050a0c0507090c02150106030510031b030803040501020d05070504080a110607060c05 90
    0xa00e903c01ca051b078010040c20008403516003003a4140a000342c14141e0380e02504000210680494003c1c6030001001075907140e45080b10f40c001d41c0200030440041c0075000c3c8822025206422001a8800d00390f034010001100d10142c0501d43d0000d000325060296019030200c20103010300034440040099400780c10f0300c0d0300d40315528584406012040c1e4086180500612016070801e5551015035020f650001d4040e01516008c0c0c5046442141c0c1d030741c103100c1d5010002c1c1c119484810348800703a20a880900c41e07a641c44904100701084181c00d140803440038008080308078800c0000c2e07000309004030300315100141c0d2002c0303020450300301e0103855006070008008480102201380020b801482245020840381c90285030107074058030180402000549500006201842421841c43c061904145050703901d0400f4036017a0300039880041240403443c10040007400103070040007600c0445031914041c0c401102035580d441c541d400d0a0f098181c0c448401c1c040140032510f80cac4210740108180d40c4805540b00c000b26 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 21250527 1250 21249277 21249281
    0x3070305031f080319180603091203060602030d0b0f031507030b09060d1203060e1003020301051605091003020f040b0405031504030806100c0b01060306060206090111071101020c12283801080303010603 88
    0x40464000e0604cc850100580e5500000721a400c0ca545000000c42c8650359001030030a080302c40c85203a0510405403401d0b541a54a11918003034051a141003204020400038000184004c07640f250380480700c00c580102040c0c1c3c5000c450907503025841c0c00102d142c0c590f14074140790101034501150030340d502030051046007030034810b15070032426a02e80104c51401d00c80f0010040e02c240005d403070141d41a90800b902031406501a0385a0390316420010380c4954413075044100ca6003240c030605100e481418288004102038035000c5000d1038041d0784180c0c42d9a41c0e1818080c0f807186a9000d00201701c54894810302041c10341200e140a01840d680100f0803e02e8040700901e404d0026002411a0340b41c19a0700b50703448c03500011191055400076183d01c614003040c0040c0e041c808661300040d08400b840f0000254441d010a10800890015244003962000f42c2c50520541c0501d0f10b00500c0c0c02d680203204942c450f000350b50601c0940e2203103484528a06822101c001d4a01c0a0348410901e80c4088014485640c040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 21251777 1250 21250527 21250553
    0xa030305090f15060f0a1a0306011b0203150c07060e06040203010e0706080609070509130b13020403030903080c0f0313092a0e030304050303070305031f08031918060309 74
    0xc2c80200041061034480c0c2c030003c98040c0000d4401c10141000312040d071500140c0000030300708502103c2411040316100c0c05907a02c1116a6400941194500d00501a040d44440345858000d0020144641040240104a07402400d0b9402c00340060240c24006581c0d801104041c0b50340030080c1c084d60501d4814075003542d015078800e0469410810041c805240c1c010308140e40003004840741086903d8080d0141c40e40d1203112410380e017103e03010240841000310b5070070807503040d0030a0300c0c2804001400c030700843c1280180c3c00010000381100104201150100010344021120b5906803001010300440e004d01d582e000411250314090b20100c204201c4400c0d109040100c0c20980c407074261591038500080c0ca082c2007aa014080c004142c100702c605803000c005940184c900507044982d2a5110708024226400031244031144030f0b64500b80f407041166020300e90040b62620b00c011800c0c48075600111040440041c448002c0041800b5040701082c000315a420042900f5140024400114207100003c2101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 21253027 1250 21251777 21251803
    0x51e06010605070609110a030b1906050604050f0612070c1203020702090a021303080f07050f010903020307020105070f020406090204080616080105010c02010e0a060807080717060d030c050a03030509 87
    0x10010000c00d60001e00300da45a5074844e03c0000ca042a0346011080280304014050704404001008000c110040014501494a07002c042001c00c0320220070344141c8469000380b6410800500c804c00450904010b07109840348024105070900503400f1840c0e5100302c003102c124001503030010080c4140034884035004049141450150329002171a0082940d10202501208071154001800442c00842c01d5900001d10750201c5a140d44044080200480341c00c222029559070141c1d801d0421071140c144160201d41d40d01d50040e42c00c0000540041d60310b81c014030320a5900410b00c010380c00051b607a510900001e002c400e0741c0141c9840c1080145454240003c20901c982d0781040050480c951300a0b045604585003407a206c07543c5445803004940221141c044590000c141f4000411500c0c0c0120026104203015941c80200344e5550900310b0b584207103100b00220340d006000209a050420281600d54240641440203251405030b071070714a040c1114000b540001c0d0385005200f100350f02440800b800803a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 21254277 1250 21253027 21253033
    0x1501090609030203070b03040f05010507020c010906090e0103080c03040803070303060e01090504022b021305070f0203040b070803180307050703020108010512190302010b030703060b0112020a0e041e020403051e 92
    0x1042d0350100303079210010701a0b01c1d8980f102100290400401480650f69194071000a000314240504040e64440441c100d16001c41d040030000315105100c1e40b9000300301c680c040154500c5920799190f480244d03002919040c0140820080804d144000708000c00c0081c1c0b00355400504180b0b0404042504003041c0c20058005061900340070240e41e0748104407a0f034021000c1c10480780f05421444480000204600942212040c401400520141e5100504c070340e4180c4c9031208078110040e4100c0c1c4900c0340780a407503c0750a080c00a440403500f00306c09150311203c0c24000044001140007039a280d904000021141540144803c2c001c65034400c0c2002c0c01481d05680030452a05540721a030f4855846000c801c81740303076010328800181807003500054190764014081d100090b46904164000c4c101e00500c4602107071220303441009449040c42140da5003155a038881e034659084a0402026282c5d052200001180003402407412504a01c002c00046100c0c1000707015032282c040c07400100c400c0701301d1010100d070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 21255527 1250 21254277 21254279
    0xa0306060806100f090504060603090b100303050304080703090b0403150e030a020c0108150d0f030e030a080a030b0a0308041e0b09060f0703030212072610060f030603050102031501090609 82
    0x3403030302203c80c0d201103058244055a10300a000454078400f099010310382c000d0900c403001442d1354040d032000495a0242c08001d4142d50b0300d03040c4541040d41c500c001070019804000080115112030043d01810344139242c60049640d5038111050643c20a4000380e80352021039480c0c0c103441c406d9218500e1242d01c3d1034040e50508101c0c000103915420100c180e5414442135400280051409003c408c51a060090180c0302202d81341c200100d00b4410003000f180494084002960a4900001c0c01060942e02490f024500004540c00300c018180849200760080301110011000801c0702011f4006000184900419050040403905640040b42e01c41c8001c1c14081003400c0242d00c4150071603901034124003400c0d81e41c0001c0c0c80c044000348600d0302c030303140c112240d2402d00c1062988802030341005070b5803481b1060290300e00f101e00c0c40e90010603a100e02d0040103030343c000c0041c01d00503182c0d84504070f01401c00059483d43ca803540d5007a68000c40711707035400b00184103c2c94000c0d81c0024442c0701412981c03500031541 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 21256777 1250 21255527 21255529
    0x10e070b0307030906020408010603060c0212030c04090902011205070518010905130506030a0c030309260c0f060f0c0a140d08061e030a05010b040f020705030315030a14030a0306060806 81
    0x1500c0081e10b000101525944540c0c207001035501250002c0604100030040360f584c0b818030100902144103480014000d03040c2d9032507120040e40c144c9004020100c0f10310302e01454010994014440180201e05010010f000e54110307204510030b40344135103860746440742d54204080b64035a0705281911014103010a02c241842151241342c0000c2540407018000580c5444600000c1c0c5403d114200003888515070000220030954030040950882d081041075020a26000c0104010340300061904151948048000140ca141c0381e840080441405003006207071500c0d0b0716585c46258040280b00344141e002d0502c1c2ca08001c0b0110000010390030001c0070340039052000c040107198800c080d103c2e82c07050060101e403500c6000c0300c01030141c440c03800404845180182d840c040340039119200c8242d106a143c89102c445031348290085505e003550040282d4a180d81d071800c0400d1900300c808080d40c1521501c0542c1c0c0000e40d84511807190902840300460702c0c1c5009907001001c1d101140c11070360820203420180542 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 21258027 1250 21256777 21256799
    0x90b0f0a15120b040c030f03020f060c0301031101030506060906040f05090109230603070e010e0603061501051e0c0a030801030b070e0a061211030c09031203040201210b150a02010e07 80
    0xc0264000040f0740c9a40711030400740d051000d1030b007016101c4c82d070b00103c007400c160700000c15110000003a020355181355510700030f10b407150000f48000b42001c0085502402590310a51007950311520050600381001e000d4030100d5a59045600010007141c5204802d0216251403c55540141100d0006000d030b030360014140d501e5490528043c141802d0200b01040325a903090012038050030034500344010941e551045a90850f000761035507030083c0500350120b4000350624007041400081a118246007522401c5a0b0a400c00d403000303c84413035002480b4414071000309000c00380d5828000d0707072030a8040d4191b05090003c440b014100070180580540c00e9000c0f501c58880103001c507011800e040180000110305200540856071240c074803c903000042004040040002e0220100203404503907031050308804400d800d03c0265806408203444201c490a0200c07225010b81e551883c054010035600b01d0840422044015511540c49100001ca241103041c2e50911917030050403144d100a00ea03181c50800c035030070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 21259277 1250 21258027 21258059
    0xf07051203040f0b040f020d08090405090a02031c0c02060703021c051204020607080c01050106080915010b030105120f070308040614031303030c030e060f010e181b04090b0f0a15 78
    0x4000c1050000117014029014045980590040c100c14a000c51a1804201941c000c00ca428422445c2c080480c00c80c0b5000a400e09110360b000e801000031614600d200101010b500b4034030300401401ca4170450040e140c1c200a000b81c503101e90010401507240c008912000e9103106860001c0140510140348207041000186800c95010b0300c84643d501c8503070405913407910440241600a608003000041c1c21303680064050310980c49101500e4400f510b00c040a504403100307124443c8034200500051140e450250494100181c1c1d020840e0076001d40000d0380e9040040550007070398407100c042801c000050304240031086003c8101c1d0300c5842c6140488100c0d0354080e904102904140c0c2d07507a41802c0d680c0c081e0f0700c5452010051001c940c143d142242158402c280c09000d0441c4109100700400c442c4a0600580e5080e20810300c00761900d41c80e03410180248070660302070300d64007586030748440001c980310001060140f414071020045a02d855440707002a59140b0310801605804840e0400038042e54003441780f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 21260527 1250 21259277 21259283
    0x61e0902030a0914060105010212090f040b030304031403090108070309080a0807050d06090504120201021303080309160b0306030d09050a0504050603030f0c0f06010503060705070308100b0f07051203040f 89
    0x141c50340c440480541c01442c910000500d8400441d031541480900043c861b4100c8000340c0c01c8482c10f002e03200f049661400340c030f407401e5000084031001a8140ca0550840d08074400060f0449007099034030344403110010840403c0c0c01c2d081e00000380040b0b40d560712050031603020525003030500480c2210b94a00f4800d01c1000e5034101000303804004100c07514130903821180700f10400b1100340304c41910b40708d803500100415a002c40b8a0690105100130841c01130007a03c40400320603410350a00703440d580301c89a6503480200000312600a4000704032108020018003400b600c40014600e442c0c1c5020000d15241c031046a8441c005d121141204120341e0f034a042805042e520b0035907001c0b4007030b180d03080460301e14090001c100341e00d0080400c0f407008104001a0821003019003000312503140c1da031030083c142c60303020580d0a800018010003c480c0441d0003010b80130b810004c00100035282580e6450104015002402169801100000c0301c0c4280002000010940038800a1183c51820b15980360010400c000c4801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 21261777 1250 21260527 21260531
    0xf0608010303050a1e03020a03060e04050303040b0417030f090f0a050d14160302030909010b03090304090c05070506070909061403061b0d02030f01030c0603021813150306020c01061e09 81
    0x184251310720600130010804a412210449540c5095024003e5000101d10b07800003807400d400081c404220001c001e024981280203180b95440c0c1e42c55116090030010300c2076414845810268450028103402584180c00024442d0303003505100344800c1c01d1409c07004000391250f108100c4880030a03070120794605040340d42d0801e1a009418840c0301c8071180100412081c42c1d2007005a500d00b499001301c0200380c04d1004680e0000107a8940c05a40c070036000c140c2e01c00c101e90f40103010611004445900c68107807609642852410911555106498810121080310000e015100204601d416038083d5402410b0a444140c049441d1840400d548850041c10b013414100450019511114180112902042006401d550701d241110041d008010700384000c90305c001e01c0c8040000d08621a01c207494800d0003101ca000400314030f0740100001005c5900400924135034946400c0c214000c0790040100540c410000540c07110b900424941c21100316070b21481044002c6108107121550503141c0c482502c1d500400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 21263027 1250 21261777 21261787
    0x1c02030c0108150a0f050f0607030903020402090f10030c0807050702030a080d060e0702010b1905030a0209061203120a06150504090e120f07050c0402041406030603010905011b08010f060801030305 86
    0x140c0f0004502c107a50300c5800140529000c501720350303036007074070001c0d603106070340042c42e0740c2962060020038403443e0701c0600002e0315810b091005240c40e40060074000790040c88601240030b840009078003c61142d15a038042507036000c0e038139000c5802402150f40040241410b030300300142c0342c012036120240410f00501013000000c9031071461845a111402600b0200d11132100c40c5422000a8000e0503081c0780c56218201c8240c4441040340c403419003106441000c0c024111280d065420700021117000381c1b83c503520018034015401070300700400182c0394030320f4107000000b40360800640700422240c290700305401200b211540a0380441d0000d040b601120200c90000139071514915101c0e0a18180c0e40303051001980004074050b003030980700003620200380a201560b049841e010708200c120300c5144600303500d4603005000349c510340c078000004c0c5070f21100160000c1640e00c10782e40d9a90860380e00f808108448500b02d0190400154884a0940940006188521080d0410f5000740041c10140720003002c002d00021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 21264277 1250 21263027 21263041
    0x60d0f1505010807031703010f090b0301090803070c030e090403090302010f180b09030609060108060c07080c0111041502070602030d090203160803040602160f060e01020a0b040501020304021c02030c0108 89
    0x650169905403031800c110301e50b1688407480d15000f0610040c0c48410030042100e0300d0707105031350441b81280d10b01c02c0c030041500d18180318500070309001d25103d82e05559400f441808580343d05c008600c101c500e81c0e283e040c15141c5250152905000c4540b840c0109481c0707003004002500050114144c0c0d4090810f40c0315002c2e100c10445088011111200d07001c00454000106103004c0b00c040c201c03120045041d60040e41d10801440c0c1d0340c420074411501d0650100010800072003a0300010301c0c2c0300f4040c0c0380c0c1c2850a295030a41900b56610140c80d900801d03c005410004511803a0611480e0b0703000384040c210711864884020754a01500c25200145903445140c0e10440d90200001483c80302d4030b0146d8000f10b5500d1229a0f102e401034803074000540100d49400c07103545860181c9000b03881d03814410805240c02d0040032070720701c40d09030940d505503c40c0c1050900400c0c008101c4911540c45240050307940c2c9030a205200d843c20940740c58080e61840b44d0400740c01aa00803500401e561401e10b09880c60ba9a003070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 21265527 1250 21264277 21264293
    0x80d0c02060403200915010c1211010e0703060b011706040b120d0804150b0a0e0405010b0901030602090a0605091e030726060702030702090a0c050409060b03040b060405060d0f 77
    0x80d000500004d440b1104003810071483c52490b00c59031044880002c5603031950071244000703010a910b07030b000501401685001172244c0c102e50710192141d292600c48048441455401c450000e029401980d108280030800c200703507801044130807482864139841000c0104440c0944401c007404003031003143c48281d40311490b2200c0900d114071484510803101c2080503c60094000003050707909aa220b0b0300182112080c103c14081d40c2503c4001425000c15a4540107412105c0f04000c2c0040b5640d54032190b0401043c0e58400c12036000c2c4d4011a0010799881e410810014120030036482001408030a1100c0b428950700ca0120041030000301caa461400368441c400241080d98503000101c026904500354540c0040c44a01c00c400d0310300b4041140e0f2580c441c440c00382e039280a56907009510003100400500714100b00d82002c403100e003035410110300f07090300c0360003640c1641e543c1d802c140980c02000c0300b00010b100303a14404a8020409441c1046103040010119103800c564110261441c22071802c0041000409 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 21266777 1250 21265527 21265529
    0x30915050706050408031f120206030415050f0108100b130207021f03020903011a0d03110115060f08060406030206091005070f08030106020706050306010e04050c130605030603010e0106080d0c020604 87
    0x80003c0282e85020b16101c2155001a201107004001c8004004412540d080000050b41c40d40d5540f00d086011a500b0080c00c1e90004004664144001004007840c80391401894040c85100704000142d605201c15a4549407820000c2c003e030350701b0b003422030315036403600e240c0050742000c40c00003d69201c07403070b00216501e00c0040b50702282042070441200c1d80340b07034568050441c0040803402030002c15000c007103880059120ba291681c0c0301c0d0055a10a000174012000ba80c107010742c0f07500119001c81e03990f22907000000103a003ca4003260301514100c039004e600c0342c0020350144044408100d46820340d000310380715014008426003e02b910f103050003c02d50184081d500e2282d48041c90707001d41c038514900940e05403c20712405000d48242d28022036104d000300c0030303a44506410307500c142019100c0d0b010080940406017041c040803004020801c00400e07612780c0440030344641c0d241e4039640d003040c00501d800c542d400c4004803c2645401030910003e840810b41c1c0d80207801d2490461541b0700315000240492240d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 21268027 1250 21266777 21266783
    0xc06020c07090204180b0307060305040507080a05010902040c08040c03021e030f031b070303050d0504020112090636080a2106080d0804020607020103050a110c010506090a02070309150507 82
    0xc03818009082d190540081094a8001c490103d12441d0800351105654080d910164142c12200c03017840168407a501c4581e2181c00340080780c00ca20380d07503004941440b02c5a20240c400f039448410241c20350910740200c2c00410540d00d0f00001e07034545502ca04c03100300c661f400001c0c400da070101c0280200f40310401c80040240350090a85082c050761a42882c1d403544400b00c0c0300c418800340255a00440004039041d42280d4064071942d02d80740c03c2440c410000d06000b08100d0612040054141c4480001c0c03258000c030902c116000101c0030000c004d280b43c40680302030440380c07200c401c4040f034054000002c8098007455214034450380b1901c5280041d00d40100d0440e503000031000d03800e0440003442035a0003401c100d07002e12040c1e40007825150411500d9140803a0080e410041c10080480107511075400968410380c2d1080014101019075800075850784404a03000da01d80d1501c090101c03030b10700204050b4105140417011464201c0d5030745d0240141445109043c0159103800000d0411405503089405040e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 21269277 1250 21268027 21268033
    0x1501120b030f060405120a080705070c0b160c08010c0c03050903010605060f04030b070507030f0e0406090f090b060607120c0c080607031a0301110f0d0204030209090a050607020102090d02010c06020c 87
    0x15500010341e5407000f088078165458480c030082c1d1103111292104540303690701c0c59503500c081035a581e2003c0e103041d40302600403582c44410310360000b0804402e0014040506140c40c42204000550801155096690f00306100c542d2401d255080c203150050224003040354141400e40d00c40740400002030051078180d2240f50041c2002035154028182d2030010003d0380e100d000203100589400204503540d000e805e0009010800c124030011303041e40100c81d84100c400009001180040c3c07940440810f44000304441c0c45002c0c0c581101100f08030031b40f00c0705540b0035810b85d0b039a0305191141d155a0050800080101c0900c001003000c0c4e8280903910002501070040d500448445080546008006040d482103001c00e00c0380070708542155280600452100c1012141c115080002c00502184298001c02d051580103608000010060f101c82541078400c56204000d484441c0140c02d000303040c0000104044e045901c100072280d801c1d0388078054459010f40a20b8000e00f10103041c5402d01c02441420040d41140c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 21270527 1250 21269277 21269293
    0x705040204030308240d0303020c1908040f12080d020304030203070506040c091107031205060102030c0106030c080601060504150f030b03100b0109080706021507051c0209181501120b03 81
    0x141d08200614010a0a8640500d05c401034400884000b00e5070440103911408910251000c01e2094000d444a4401441a1a00d0041d600711056070240540760031128024049010000c21030008800402001c400418a04840c1913030381741101407003018401c202d111390110120301450720800a81d244150f11034121102340c100390600d00d42e1a0710511990302e25904284030502c09130782c0d102c1a504420380c5900d901c17040300d41d0b80b0604009024002d0401e811448140b00a17a11032100340142c6001f0344c0140a250ae046060103200303400c0c0354050300f2120038014200401c000d5146451660b041c032001510340180e03880703500b010490280c115900d109605202d0340d16480b11054a47c0d0041c80060401d80742c1410881d520040d036521005140314000140e0000034450749007000384e0380d0484d40125603150841c9010891152065608040003420311f4035a801b14607881c46003040701001460f500c0c0e1501e0700c03410f480c0c400c00400201040502180c100607941c1c00d40527a5042c560003205036a07100806841ca01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 21271777 1250 21270527 21270533
    0x14010219120606030b100c03230711090108100b03070e010e060406150903030804080c0a0506011e0b070206090d0203010c030b13020316050307090305061003030e030f07120203070504020403 83
    0x34031000403041e05202d01e48100014154080d03c00c01e249240d000c0c15105289001c401c0942e101e003032040c0c0507421f100140710381484e032008801060b0400d59408000707542310b0381281801041d84030030903080d5000d88000801840200d40000d010b8040024280300801d440c10101d003c2410801e481d8042908a420f9200102e90300d08240e9089100365415107080040943c1c1e0036980d03000c604944003110100d618944113002182c880e00340203620500030201e00c0d05d400103003c840344c0340041d00e03881515150010401030100480414600c29902d050000012100e4102001844240f02e5000000e00c504000208494240c64018007030402d150020000c00200000754006000f81c264140300f180300e2401080085100712051013034070f01030525950080c1b80c1c03200043d01554198009080c010501132400720004c0020420880c00d4486d1041c1d0b55000e0b11a4036520380501100100c907052880ba800005140340b0564000507004110750b1844400100754a00340046400e0200c1a013290360040e000127008000c2c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 21273027 1250 21271777 21271787
    0x1020313020102010c080c340b0108160e0c0c011e02031009110a0c03020a0501020409140601030903020607030b1c0c0302010e0a030b011a0c0105130204050106030e060414010219 78
    0x114074000c0c1c00a01c5440c840d21801c03501c0103000c031200b2003501e80c2448019000e4407903002401b94500c04a100a00c840240c01820381c1c2e401601d1021200f982e81c8500500c01c140e018001a100080e0960324084091b00f03003441e0fa11034040040030642040c00100e076808080e0000d4000c104510b5603076058220400f14981c12102075801104d4003040ca8454110000320300080d40700e18810394803421010b6040004100c0b013100c0c032008601007a0708600c9401c141c0404910700303100400c010901070324000785900c000c640d0003108540c0100024140761034000b550002c6500072031034590051151500040201e00c0c0c80004103003004149001002c45035604205042115508031281030728000d8861035003411001007000010754050100402558840004000042d244082d21200e402d9261105085c00640903032982150f01c21591a03204903103405802d42503041c240706441c05400c147c64184030551070219400d60744c0388068401041c01440c442c4c1c1900f018002e50548400c080250402050007010540c010030b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 21274277 1250 21273027 21273061
    0x4090c03120801030b060105090d0609020d0c0807030308010603020906030f1801060305070e0108010603150b010c020d150f050603250306020408030406031410050f0f03030307021f050606070206030703020c010203 93
    0x45c0040c00b040407038610360081040e258100c0b0000c00c00d01045c09039a640270090001120121f0304010284000d10006007070303001c000007404c00840208800c42c40e605000f42002c4060344510140751040108604507200e5a0071240d10507129500c51102e40c86c0c1081245040750b08001401442d4a81344d004410042c000c940002201d583c80c41c680703426620303680c540b800c80c0c0d03552200508098581c419182c040b81035410442104070305040c0845001c103250082180c240751001d00701d480c80d0784481c04845c1400940f21301002840349101c100460700d4610007083c0d40b0540118450702c071244a110003c600d00325100c1d4000a1584041c0940d103403655500c0044d504d8111340100ba010130304001039a400c050350141c0c81b03842070003049003121001d4503000601c6030183c941c83c2140d410a484001010264500700000c5018803640d500410055070a00d000c1003100b0351880ca00d1140c1c86c01d050a205da1340ea9980c0c151255960101c0c2e00d190303603489803807040d402803103180401012540044100302040c900746034200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 21275527 1250 21274277 21274283
    0xa0507050c0306010605031f0f1401020105070305160e0303090415030c0603020a0207060509040f06080d11060f01030201030b0d0c0303090608010e060a060e0d0206040b040801060501020601060e04090c0312080103 93
    0x54549500d2402c0545801007409200c0000c0d00501c0000d0812418400d440f40707612812420415040d21640061520f50194005600c20a4a10b0703004016590901c82c60754840c6041c50100160700700485c2400342d203145004202d080124219001c585941c0600450351304400c014020420209202980b0110309054401515902405400090303128064001c85880e0900b81d400740130260b041080548a6400065000c4e0308075a450404603c0114244104400303007450700000d080c841c030250f1005246485442d103200507500070300300703100d0782d01002160345065a509003004140e03d0120008500885171105000e05040440c400000905402c0310720301e42502c01c0b40d9204595a030320740c06217600e645000c3d102c00c0e0b009901c820040219511514601201410050a8802c0040d4a8001820541040e00010a11240054100845c5400344101c40080c2001e0010b0521076152520140105ca01c80c0389450081ea15000e4410401c00c02d0380e9520040c3d580248640b0024282c14801454280300340411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 21276777 1250 21275527 21275533
    0x901080109050d11031603050903060405010e070603021c020a03020903070609060f050301060f0c1b080102040f05040504020d0618140114100803070201030e010b1f080a020403080306040e0c060a050705 88
    0x10192510134510051600b08642c019490142011640b0514002c1d5800c00d6003005814010426070341d42c24000303d03008500560000c5030068940000a0170100507034880b00500d032041004100401d14001c419400c81ca1494005880e0078881e00b00f500039200d00c0b031005615004290020406580200e294403d84456540304448000618403c0c0d81030701c4280034010215403009050407a051048591031940f070321903020303429000b071141014201c01200d0342001140d650081401d0040e018a0920070300100000c46042c4880d00b420380206c3c2040301c40280c0906960345074202d1090f18410014800e02040e80426492101248850294024960f10600044849890003c52444045aa64641602c1c00302029618114059005400900f407650313000b41e0315525030300900c0265861186c05407608400704000320a4050b403810040000d00010215911036105000600200c2c3e008011750b03a00001c19640015032014200c1d07082c1c0f90114880d0b910754025000a103002400f5030007000361518070700c50310403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 21278027 1250 21276777 21276793
    0xd09030c0b0a110405120f010f1409160b030901021306050702090603070501050d0b19060806030601170a0201120212070e040b0409020310021b0a0302030307110a02100518090108010905 81
    0x368000780c0f00c070b10740d80c2458640c0a110a01c09032070404500d0403400200422100440c080c551035500f520f090a40100d84a50344000c41102c0254004046501a401101174208042900071a23801803030107004100782468003000184424509504032840210056004030840303135110070081c2564022002240550810000b0401c03500780080c0041c1580d005840f05802e14261010402c002d001c18200c141c0d112307803c04614082c980c01c40c845030b00908150b44d02c000c40b5162040c10302d441d116040c1e200780f03d0f40040d0051100c2d1404081004201c2036030920f4031003c90841070b8411006805140a68802c00a0041c18402c1d8550020007041401e40256018490404007004110844094003400703900350704010903144244600b0782c024076200d81c0b031881c0c010305c032252100b90782d10340b240c10791044000d64400810304c02481d4002c0080142d0b4a99080100010f044540c0402c82c003140c0c0d14002010b10078080341100c0780c0d010f2403c0e2902440c0e800b0b001c02d9020b603510200203004e0220440c05503554014511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 21279277 1250 21278027 21278041
    0x31a060f030a050606010806060906030a0f0c08010609180908030906061314010b0c1f050403080105090415050403051c02070606050f010801030f1703070e042406030b060d09030c0b 79
    0x1010b151042c0c0110141000340c2e10f220055442c0038004000640c8200b081210303102c035a550178080c2d0b001d0405c203140002d82ca540c5504410494140041c0300b014403100340010071196030307c0803450041da0602032150f540d8204217200b29001e0020b22100400c280c2c000300401600c0e540001d001845a00101d550b641c0c0c1540c0030708410304585c61600c02185181481d0010300089216100501000d2649400c80e1001e81a00089410354081e0b40d80035401180c03200c0600041c0f69020031600d0151004482050f0141071654800d03206141002c1e040010940707540c001410303d406003095a80002c500c43d0008030aa005644200081d40201400c03540ba0b86420000700709400d0407007264181001c10384900c0c080340d096440d00b222208100404a030703480c880901811550350400c001c2c0d4020010b5444440365140301100300b0091f94000b00a1018024540101008100c164852141165030074100003413035000c00d1011444601c0740341150130701e090400040e4820141d1000018035094007030a10a807050b21940 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 21280527 1250 21279277 21279283
    0x10902181e03060709150e0d0203030408030307090b0a090e04060902090c04030203120901020601061b05011503021806010509040903090803030c04060809010501050d080c010f0516030c020c030a060506010504031a060f03 96
    0x20080d181500003645058000e44c1c051f000a0464240040581030541e01550010b0319507030150304072200980011042c0410a40c2000303031240500820644241450000344005000b00440d1040c00034040d078120115042c011071794020004185c015010700c03402d1420141411283e40988002c901a202d6903c901101c42c1007101542d0898905a016000e241d1030044100c3e00600d61345031415802201e0300e8030800003502441810700801c00704000c0b42405145004011540702c0110303060a083c112041041200d81e444011610343c08821640017030300c03d600c1c0c20100c540113080c0e00102103501c030001c14800080c40742c00c054170451b4500d65480b0116034550205034240c1e04207104051300110070b28485800900010f01418140c02c90f02d00006000c1c1c0840b10742401e07142c040d61040100104441c0f03c0300f15952500a400240080b800103160721503500c0b000ca80d44a00c03010005c1c00c0141e035200403c0c80eaa20601c101c90007107030446000d1004203c850b0300e01d9003440094075514030414a9032380d80c0260742404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 21281777 1250 21280527 21280529
    0x1209030c040f0f2f0720060c0304090501060e060313080c0c0d06240303050306041e05040303060602011802060d020306060408030a03020306030601120f0308090f010906020702090705040509010902181e03060709 92
    0x2030406d1302d15600780758a00c0740c030f20007030a20f98031110a00c10b0070700414003003001d0300040042000c003140ba0b515001c0040c181318408103096006070030820030080c00e54809543d45401c00e51050f0700903aa003003401409070500300711092091b03004294000080c01d000c030340d1300800f0034a10074a01d0201294803440c0041400c804910001380450700a000180c1d071441d05030f01814074081c0c40344d94620100400d0318558200c07842118201c0c0841d83c0c1c1c610a010003076092044918800081c003810003030314020b4001541c02d005200d04440b88c40d400100081a03602c540041d50001c0c9152030440f0344078031074500080c0c0607400c102c452138001d204031400050a0484a144943c0c03d0b40c11110417007206001e034078210340903900201100c03600d204103031080d007202d50248120032101d8051140113888074614410480035540160020701009414070060105a50725400700381111148200166950148244240c452035110b1785150f1210b400381d182480421198514206681d0440a5030000d42d143c101c20380300d001071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 21283027 1250 21281777 21281783
    0x30a1a010210050a02070f0b0f070203090d02040b0409020604180509070e0f06030c0604060f1d060405090405010b04051003030201050a0c0f0e060c0a050705031209030c040f0f2f07 79
    0x300b1055401c241d0046810140a030713400b600d40f100c3d58070341a003003c200140031180143c1c090100b2525040013a886d50708600c443c0301842c6400000000260120141140a03101c0c5549088010381a5150f9200c81e1080e98041c101c9911141d640080d4607000c41c41c001c2e0707110461301340400612000d00101d82d80d02901c400303140009403a12600400001c20000a02182e090704c0b513188a06080e42c0c0b50300140008010540c2d0300c81007003a00d640000c082805c031b0b00500e460700c0c0d84030225800075a640d4081d6000d80e00207580d00806947c441c100f03c0c0c0074008401986800ca8901030900c20860303c90407400c002e903070082d0000c1c401e9841d03038140b210885e081d00c4020b000140c0303002803040400c1c3c07180c0340001d410400140a6420460342c408218146607200e18100c620394002ca600f0045c5080070702c5011100003058000c5418201d210002c00d413560400d40034241300d143d840380300c821011125840010b1000c010007040044400c4000d070b6840a071850020384c1d04103020030004009825519044a51042d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 21284277 1250 21283027 21283033
    0x2106050703060f1409040b040813090b0406060c1a1b04061205010b03100920030a0605040b0a03081e04031a04020102010513080f030403170901060303080703050103050d12060b040605030a1a0102 85
    0x5a50703100c2d1514034402403c11035503c50104802c44ac50642c10072a80098148054002280360001081100f12566070b40443c2c10f00030344400c41c801240080d0044a035022201e890034665995a8000f05107a0030440d018010030880480d0108d8000e40c00f1814902e041c10400080000d03981301c200004060000326500c0282e000c1640007405044420f4114000c00081c6551710b400100c2d09052050745a0401c4601c031014070b03940d03c0e04004916203130040c819140010b4540b19441800c540301c0204501ca031440440398403100d40502210f100c0800216002180c02c00e6000c0810b040054490060610507101a4019800c15002c60b01c01081490140c480640c040d140501d00f0706484420080e6400040c0b05809100300c600d01b10012112520526106102c03200002510038118a409080c058001e070101c0c0426141c1001400040ca0001d4050124100b03410080c0c0e4005070b065010020348010381060041e0740b00464001109508180070750302400200c50148001a00781400d94100041118050300581c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 21285527 1250 21284277 21284281
    0x30d080a151809141506150a0503070309020102070b070506040308010510020703030c021c0503040602120702060304201302040501020f010908030601050319060605030f09070e012106050703060f1409 87
    0x10629501c8182e60038403959134203038282a020b4920381030001000d00d0f4046030401c1000c2000c14500000740341d06002100000c14207004a040700100140001072800092560714002001507a00070880300c1b0003048072420310f5944041a14040340c550381c0c03d5a0490100f5200300000c1001d24005c3c065052a100300e030b0080004918503241200d000702051410783e00040109186055034030411a64a030481c0140001d40d0303610316010f0000d24148141020020b81d5005101201c010790f944412260050b030001d14081c411440e0008085444000c0d501c0150303c0301070940b0303841d03444000342c024100300e80c0300740c080c0c52041d100203c005080e1001c506006080c2e040801c0040c04a43c00b84028581212402c1001e42d42004860b0b407940440d00c903508050081031011041240c54038003224400e0344007006802510260389003041c80706007a1018051036030100c07015004a280c10107035051000c40715400c41d0f41030103a0304002c030010340146468044d0040f40c030f89002010640c00d00c1c400c0514480480500301c407600da = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 21286777 1250 21285527 21285569
    0x3071818050c040f11040801091403070309051201020c010c02100c02030405030307080318010c0201020904061413020306030102070b040b0601020c030d120c050712120506040b0a0b09030c030d080a15 87
    0x80800713030421014113580f56000c440d40b0b8082c101400180500c8000011050039504011708581d0300c960100070300d580304000e141c000130360000c11101111000c0d41c1034420a1a00a440c40c0a800740040f503400961a01c03180102c82507001580d0907404500300300411044034000022030300ea01c01c030700400790542d104100000005000344011a4440d070540c192300f0707040000b8074010307003501d420b2b0b90554010f0790041000c0c10769180610811009000c00c044951582c0001c0020444a034004014080d90700d45c080001502c6840a4040720340f80c91740301455854528051801c2c0c04c101006441c420300500ca42c0d48a40d189082c0042e440401c080e60351503c41c4071454180004000d0800c1e0030a000802c51b0912040c000210306071194180080152141042c050451403003030201c40f801000c0d603215a08042510280d034440c1c10b00790703080c3d4880b003c0c3c82d0359034190600407a01d4404107000245d010701c24124880350269000c0005400b4103203940e001d11103084071004000303825400b4050700c100890822200340c15 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 21288027 1250 21286777 21286781
    0x315120206090904050a150f060f03021003110f040306020408060a0b0904290a240501050706020702150703090311030601030b0105210304140301060b0304030e09090106030203071818050c04 83
    0x221601c50000c171406d0850664030503031501c481c5420840c86540300caa403071680c4d06d490f028803c0074058100100d80d645255400085040c0c0240d80c0e05c200345a95074000c040c03004080340440b05074100c0c1d032007030070360b505e0362441c2140007580309100d070316039070300401020840c0e445450140424028004224501989482c2c440c648095210340720104a6083c540444031a9034000d11a103108000500c000100b02c01b228000e0041e4204d004445591010a21418001aa0071505031042650001c0005840351a24404502c0c2c400710350011002c080000b140c0c3d00b0800d58070104080649204101c04440e8025038401c2c1b541c0c1d10001e000c0185032100a000600c51401c00840d40d002200c401c1c5440d0441103005007980d404c56201ea04003080380002c15100440c03c1c20f0901451000700402403045140d403070a41c030300821283e80e400804d403140c6580e4000c100c0d40102500100003850b001010742d00b038141d07a04426075107901d280150076880e509101d044038014000d040d0210384950007002500d90480c80d4000c00c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 21289277 1250 21288027 21288031
    0xf050906040c140c01060513050601030e0f100b060d020d0203010305070b03040803040f030309021906020705030a05060a11070b0c0306040b060702090406151e0303022a13020c0105040303151202060909 88
    0x100c4c2d59a01d0b480080c442c0c1c2d4412405050f504503410020303c90818200040540d80815600e074525445481c0401c0c800d0800501700015a901d2807001070b40c041c4801c0019441d20920345111041400031425a00241c229070046040fa03110fa02160282a03030b45036180a03030f0200300c5025084100c1480060003180000b80050010b41c820325001948405079400180014400404054007c00400c0140402501004064041c00c0d084000301780a05056894682d140307030060000c141d26440e05007080e03a1154040070350301c003541c0c0000021310624001103c822680c1045072000d11603810300146804905040c001c07a07080a4001d0301000d003554668031480c0c09032203031110340b8140c40c4203502c0003c0c0d18400b0814050f952051000c2e4100d50a242d400d00038580508445100f20b400380d80c460b81202c0740e000c40045c02c1400e4080e10640421510012130200074000c001c0d00341583c0d42004204000c05516510007608000c49038007010713200f6100c0d46802c40441d05440020340180741084916090314103820126 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 21290527 1250 21289277 21289297
    0x10807030605041a01030b0103140a0e0a2a0f0803030a0b1216090b0306060a1203090306020c010b0102010f06060207030f050106050d0f050c030d08040609110303040f050906040c14 79
    0x401d5080da02c9012900b10741120620034801400b020a21020b0b41e030600611001c0442480c040c40309000f600310809000e43c000e000d805a5a6403802d0741142003009104041c403c43d001400b1138518801c040e03000c0c080113950f50102160038550a404580c046540c079161003030312401401107080d5510b40103490000c0141d0356410343e01181030302d0545c000306010012401041d591241f1032016a186c0060902a100c2c6141958803a0300401c1c1088220b403514403460007110812005250011203034101540c00d020f6507000a8520f0f0f0001038100b035404815000f001e2020401e80c000c00c42d0200700502c0d8012543c00e40103c2005801884040004c0f5150b0042150258054000017500f15035410005903e00e520b614102c0f41e006100403000c0a1007800d102050400c1001d4004c1c00002d2040c0c1c4000707100000050005019a90701c9400c0b0702030240d00400040058006011030360740c1c540340c41c110a002d0100388203080c46036090800054450a1501600000083d0790719520100c40d4140309501c03483e00f01034140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 21291777 1250 21290527 21290531
    0x903040f05031204060320040902040f09050919170d05010302100906050f070503040b0d0507090b040b0a120b0a0308031f05060421050109200d1101080702070e04140606030706020c01080703 83
    0x94036001fa8110002c000501c4d02840044e0340701d150000b100d14039501ca0380a001c80c1d07460807041102c5e44102003000104c0c4be44040254003018000d117043d64254140300b080c032001c401c000c1944190007403140e0009042c0d038000c5515248001d0348520031164008603004500000c1c2050042d24400716014003d4000300e44160107031fa00380391712015030440503000f03c08421841c03604c403021300c41d035aa00704d0240c002038012040d403a4901410010140301c40d00c1000e02c80403c001c418a508001340e000c903070142c0c0b1480c034000c002911032079803814042020f42040d2451096a64011120385143e4041100c0f0030440c3d1b406800241000c1ca8660003241e08813959002c00c402a11802c2c034031000520a10079111904c3c030990603185220480940e43c510003591804480c00394107000b01c44404145d132a40b02c00ca0b610005d02e008612a07035490b400302d003464165071100840c82e00b00002c1c0703c200518010740c007940c03101078412641903030b640d07000b0035035124168450100540c11044098055520034200c07903502103441d044c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 21293027 1250 21291777 21291821
    0x302030303040c05010f0903080f0a050903100506040b061206060904090c06080405010b060a080f040203030c010c030207110102060103030c0605150904050318040c0e0405041502030903040f050312040603 89
    0x100341180d2049808031542c03007a161040c45651381000850681a0b00c0b0300d03040203000c0c11a51680c02e6840f41780d0380d032156198046084541c3d24030600031039a034098007074180c2c0d40e40030b520001c410181c001500c64620030b60908442c00c8290510405654880660041e40c203280d4490710305100c05580003c0d00a50460f496006040c08101000a140002c09040c1d40702451460141051800c64552081e054441d4000300826155035510800c43c90f00980707400c924410a840300d10009181d8407861180134299420300310724640f2541c155024212a601a0400700503038503010004a03100c04c424000100450b4503000d02401040741580541e5004201165840d60300640400050740e6000890f0125040d500001d40300607071a01c44460517405141c00d80e0180306581072400040d10380d0a0121455001e40d82d92800502445030501f04d09611001009045689050040501c0c0c1c6980c803d010b405044a43c0b99400030749400c0004622401806084510341401d091600840c003a0210001401d8442140e01e6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 21294277 1250 21293027 21293029
    0x6031a0306040507031106120606030604061e0e06030303060102030412080d1d0d08070f03090f020607110a0815131a010b040611010203060616050321190506010905040c090302 77
    0x4070142c0224010300050200c0380c07a510b4110b213030700381100c00310340216400e2003800c0d20301000c40092604180102e03213450b200e541e4100418000c15850740f1160342e00c43c294205070515210f0035040d40c19a01038071400021907451409050342c0348405c0c0e840314010b9001b00001c00034084c10300f1580d0101c0e441950702d40d140ca0302800e840380c1a80d0210500d6521805076502d40c0c9007040f81045940c0109000b0b081078021440d0543d8060302d1340260f200b0340b03030070f254454008104201450407440d101d581e000780910b44900b01404c006030000c800340c9003140504141e51001c604114005400340b1004c0d02140840c2855a4142154150800ca001d089912550034095036444140d1a028207001e404460f401a4650340340000c02045801d030a004003030765910400c01e100d082d4981c10300326242c0b0385800c645c400380c402261514921b58401c0c80450107803081602d800b4009040340303102d894021041800140c900703501100404085038004c0d60402e010070f82040d010010350820f0f401032020500300d4140918696a260 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 21295527 1250 21294277 21294283
    0x20d08040803090f18060f04060e09010501080705090c0307050904090803130b070c0c1a0c0307060b01020607030c0c1506051c060501060f05030f0c0d021210090e0706031a03 76
    0xa00300c01c4103a007000c03d4900090034084d885850200c0c2c22105483c001000e00d50b0030007084405072140f4090240c140108000b9107031500104000e11491000b150326140420706207000b803400780556641c600820300c6c00511481c015003d20702640003076810500e151a01002500eaa038042d6603025045900c1ea01034102154400b0f01551080d559920b40c00640d080070b140080301c00e013000705600c2c2441028004240411080c0751580d0503903014500c10440d00c90441010f10b100c0c040c9000100c554400000c0d10f01c10002160008110a0700c203070201d42c0c4035207c0c140f040c1c06440741641600c0c0025a40101e230400b0800f400c2c0e184641618416000400300e071201701007008540c508102155000c0b000100000b0000f0f107128181c01401589444484215454001000752001501207a4407841140c045800824610b003111040d5294000c11503640015694110745540308440503001c02095a600041484150041000940090b405403055504003041540240701c085007601808980003c6034020341c40030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 21296777 1250 21295527 21295529
    0xf06030906060909030f0409020708280210050106050702060a090e01060c05150402031e0f06010f06030e120a030c1218150e030405010809031903020406110a02060a030504020d0804 79
    0x110281c01c1ea4a0700405000da0a00040d0080c5085e03401080300603200381c0b02c00140d900342c4140d40f41c0940e035003100341804101405407a00030920203c02031040030b4200c0c24900e1901c6174000c41d0702503c0c40b1000c01d040c2c0c0400c4910901c50740000c14003c124003001450220300901210300039041c007621032a01c41c9140c2c41c1b011006d80102003c12a039043c01c5040c8035003008028492070901342081100e103081d0740071a07214106840d5108040c6060300c00341501c003409000803607110380303500c04442042d0380d140f80704c604007481d5109940100b86080d0a10302d07412000b0070804035101890b880b030303441c00980503021802002d4142140041005a0342c0c03a401082c0703e070064000c540100d4040520380c44081c03d00312856160f400c3d204000c5460414000c0fa803031804419a0112402424150030a5880081e060305600c1040414074209400c01c802d5100705405902400a907605035070340c1c41c009201c00303c415aa070240ea1a001e5445601404468501482504540c1d4040c3c4050300081c00070556039120a80f940003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 21298027 1250 21296777 21296791
    0x9040914060a0b030a0206040b130305011103070306060206091509030409051f05010206010f0b09060d180611040501020a110105160510050601030506130c030209030a0302011509060f0902090f0603 86
    0x8604140b08160034580110400c010044002d40392084555002441c0c1c0d200d54810400c604002090300107440c020750140c04015030300709009208003000300c6407c40c0241c1c401c480741c41c042441d000000c01c61501c0021054030801c0c04000400b841da03894407040c004540c0007040c015191004220100305882c042c011103002d5440490441f00903402440b203102e4800702034111904560200b0010040c66003d03126030422604d100004a9860510601040c050300c607880c804102d207401c0049a82800684131030880303640c1e0081c0d0701044051000c03415111184580c0c0303d118010391003990325001140544014400d0704005061862405c0d1000101084858a40d002604c2e185c010441691142c0e41500500fa4400f50900c1e08010501d00070000455508544001032800d41e0b17500e0940700311a000b507044545100340181183d0450248e843d00074080c2142d40803664279101914400030703841500d030046200f500c44540354014031905202d000c070000c0d04144806a030100441e02e03803502c0782e15814002c0d07000e014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 21299277 1250 21298027 21298033
    0x1303050706051504090b010306050a051b07020301060509040b0405010506060405061c0e0a03020601140a06090603020309100203310506010e070c02090c04060f0e030304050609010c150c0f030203010503060c09040914 94
    0x850349c01c0590440c3c400a040446050030201000101021401160900c194172035000743c0b107200b680007003801004c0b107410554000050f042400300703000303202c01c4c0300348601e2140000744080d41d580740038080300c0c0c020780c8951a002901071019004511410381032107024000c91000180700d660030700c100da192070039280e0241c000d80c20210042c80228898542c0b5800c61000340d9007110940c1c40c1000040252420f441904200356021000c2945101e081c002d245081851000a54403410190b031888903004c00881d5840068504880f60441850303a00b034141a003540000143c80d03141e00e40340c5030f80c100c404018540303020440d5041001006030b0b1400801e9000310b605090080d00c0f6800d04101522000d25440342405102c2c00c104000f0890364008101d9080c4c17001918855215a2610010380b880b1050480050490401c0203501444608581c04480000c50940c0d90321154600020190101d200a00134140c25801c88400640c5900e480d00c0104161130014100049112003500c1e6903010043c045070028482d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 21300527 1250 21299277 21299279
    0x30c0909050106120509011508010b0f011b0f0206070f03050403060606081015020c03030c0d1403040f02010804170c0607090b040e06040f0204081609051303050706051504090b01 78
    0x99008121a0203002645020081941004030107044c43d040034900c51080f40d100c40008607002c00c2900b1990008001c400e01254403510303964118064008200124080e403104400b903030702588920082422148940815446a00700b03032101c01a801c00c00c03034180e23008075041100d540020480c82c0f85110060003561600e4071581903141140a440f4582c0c802020840000c0c248000d2100c0070452000b107408070b1f02048000b5061840036030405d90804600c90389404042800032011101007000d0035000d01c29a20580942c1c00c00c11929020302044d100940100514420f070320040d4081c0ea05280c005008600f4036080c008100f44004155005240c0084140c04c00401d100d25103810542d69000b9107190304440b03040a007015004c00303c0400c001d004d14801d0780c660080c2c1ca1404091341c112005092a0f03c1a1070fa40301010785045900d0200d44201d1101038940f0000921500e54441518152645940c80600c4c02c03805840c1e820182c40003400141000c207104500543c03075581c80c031501c4070712803280f40c1c00c4040d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 21301777 1250 21300527 21300551
    0x302030a0b09070501080405060a270c090b0d0812040c0905010314010b040515010c0c050904121e0503040206070611040807080111031012151104081b0307050f12060703 74
    0x200070f56206034180b0414070f007070000107100400c0c042c1d0b00840b404000595844000014480350880061030101e450300c43c541c440c01d1040040c000c4094441005091003003035091800d201046180c070b032000d003041d801480410710b0200e010305026001070040c5c0c0000800d5403a51158030803240c0c21b174030440d4a00c07504247c0b1215544c00307000310b94042000312400c2001d894000101c06582e000b01c0307182410007030003881850800c00d07414414000740c180078011003a1840c0c18580180c8400324200448041a105490248520200804400c51030a2a40c5043c01c50300c540c0d09001054208140c1250741d15190840c122100503510041c000420b205030050804d40e103800221402c40c0c801c91540c82190408004200c0d00b410a48664411184a6119410030414500b401400382d0000c480d0002c016041131601031a901c0e40c000500140d5912005036015202020344904a0b820511a02364150300160b40802c4103103400680a0390b51403018043c90040f0851101103818460200c6011002c01d90740d100340400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 21303027 1250 21301777 21301783
    0x1909050a09170a020708061602160302010c06050c0d0905011b09050603060609010c0c060e0a050108190b0301060306050c03010e010e0702070306090609060c0f0f0504061e02070302030a0b09 83
    0x4640d00004100d448440c1d00c40c11140b042000700142441c1d000940c03210030380e10810075a0300a2061500707885581c106911001698110448000014460004c000c40346021102d180d00490358143c40380e0074030849075070751507010382001800c814090340240306004040415001c1d81c580740d803085000241002a00041d04540d42603809620200021000c05100f80d459000440340c12a404898050700c98800c03d004071024007008000400d002d0403804c000030906d4107d07017820a20318040780c100048070344800044910001c00c40310045020650243c0604100155000742800600030300045161600d03901e616040d62010759182c4e402c1c030340000040003403e281c08403041c050080319485007260300345140029070301d14090002a00d4141d4075800c46d810001540c2c000c001456120078140318452010201030700e40390b04966100e022425408000207800d10402c04c84007038464548075030b0b0204a034416110041605114180154030a055022015a03402c200c0102040d119000c0c0b8042d0f4a01001c4140c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 21304277 1250 21303027 21303031
    0x10e010602010908092404090204060206010504110d0b03030c0d0816020307080a05030c160305030603010b09010f06050318060f04031706011d040b0405090c0108060a03081603030209190905 83
    0x11a403603c159800024103101c11503540751001c4803034108441c61146010200f0401c0c0c0004042d60390700140004110b402ea401401c212030641c1c096603166030380c1d40306000903a4414821482c0c040320400004004440d03a9100b84070845003d0203c83c2021503007210703149002650704440010070039000402c2641d0601d13008980c50300c0610f2000d981403440c03550341c0350b02d20700801810000b404000f00000f00c3c804405400c7e00c00014500d00b60b09120507441c01d01402c6e9500c05d03502140254200843c600007800c00d900220304a40404480340c0b04945003280440e407540014140403e000c41c1a1800c20129074200a02d6000300001008030704181060320b001b511241140c109210010404070070010740342e0300b182964142200c0c113a055050aa400c40000d00140482400294441e01c0c00c001d00c03000c0040094030000996080c0c8840302c1c543c4408081008038180d500c0000c100c828200444c0c840011045d41030b80c2814800d0070050304040c9007a0001d0550f044030241c841d14903090040400c003c100a000b815 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 21305527 1250 21304277 21304289
    0xe150306090a0305070b130203071503050a06080709020901030b030609070512060f06060a0c06060305060109060b030108030a0f0507050f030d06060f0e060c0309090c0d05010b04060503070f0c0b0906010e01 90
    0x64004180c0e4000c4c15502890002921100c22480001d1214460f1000c44800300d5000307060319070803525040b20642e00040d028121000902c0c150001d0b09d681410310914056414040040040310f00d050f0080c00654840700d5a039040545640025429441c1017200030f0240c000f8202803d9810300b80703410301003046030380c0805046640c45101440f440c0011800c3c059000a03043d203d80d0f81d207225001066450700b9170900d00400301c0c0d207090400014854040341e9181a51011130b0300340007807035036080d414502c4d000a02440c2d000b60401c002d2500e04500824910480b1a15810011306021640d00c90500300b25200e482101c0580001032100005805072181b03401500b0203080032401e120000300002c0c05101c00c22145805a500020390100074902042900c41c0081c00402640300c500d0001d00c0c80c86903401400303d0100c4581004000304034034125005480540d25190f55460443c2c0d1501e40894080710065100c80c18041c0c5a0041d0010803070b08184a40b140044400804003940b500c1a141d1913240140d00071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 21306777 1250 21305527 21305533
    0x100617061f03020d032d0f1403011e0314010c18080d0804020301110a05040807050109031a061c110316050604091109190e0a0204050a050405040303060e15030609 71
    0x201c600d101aa049505694060361140c20f00442443c06982945c0301e810284c40b035840c10030304110052031108641c003110013155100010b090000c1d0003901e5031540131052880f5580144014000d24046080a140e0fa05001d1440c9072050f59a4540899640128030034104594581a090304240c0e040f10311081c8028031602c2e0070721503034504801140c6416048541a0422400d030b800701d02556400d40007400f0b03d0384007140080e030394001200064031640c01780c42400003034054824001003640c081d6041380c080300c3d04080c1c4002140c8074140c100002e00c070002e22543d48100c0c1d69603240540310610601805103071050411402c5910000304242c6001803d4400c0001e050105006015607281c15082e50200d500d0300c0c0300465155804c0920203a103010b10f410f081e41003c084031900200907050025082124813422000c503240d09c548410300140c0c0301d980606c54008500580030412424640d1000c0c2d4018000d00d000158162900c1e00547ca03048161911a0f41030b540b002c20382d000c1c2c50180f001e5a0800100c2e802 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 21308027 1250 21306777 21306811
    0xb0105090607020409050c040e010605010909060803120921091e0a12020a051009060809010506010806010e0319060e0712051903020708060c04031707020d1410061706 73
    0x2034140d20800000900558a41c142174013084010050395403d40801003007402800340c0744c00641d000740303528442c0500050b034065000408050754030507141a12540340c040c510742088086840240c040280544da00d52196270300d40c084440705c2d006c61622608611340100d035a07020340300c108003255001c21070340d81454059000c105800c0e81c0741501002181c410600300b003401500c5000040350b03542c00364000c07038000b030b0b0518031108d009900101ca40280c810989450030192119503481d4200c66080329041e000c80c10f1800031481c01e60180481c80461003000b811a2505440708030b003000c806451902c110382072500d03443c280c0301080080c404400905681c214040d181c0406441e515038034007100046070030701200702513148185442880140003515084007154440c0c00c109070100e800364040e110503104540440a0242c2180c0c80d0380c11212829001032001450031810b44411000c1840a000911b05214bd0741e41010f4100c6a406050010019180c03d03964007007044500c4e9007440d100a200e1010001a616 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 21309277 1250 21308027 21308029
    0x21002071505060f0d0201120e07170d021513020a0305010c02060403030c03020a120f060b04030b04060b040902030c0910120809100302121302030709021204022803030311070204020f0d0b010509 85
    0x1a03410142602462310340d443e0118010440c00410fa03464a0501c5400f030035001162a00441c2190b030185a00001100c500c0e440940040303842d00203951058100c00d50b644085000c5055403100d036081103000402c941d2001e030b0341c0c2d5501400c41e4214240c400258108030100014540c140c0725000c401c0d04581025841c001c0c04007802454142d50310010a44640d44103180d071128402544110007030501c107108079546035203074281221001c6048070201c9500781040392222050500d4044d01181c503034090000d2003840c8801d010007442c20b0b0300500c8c1343e41240c00c940000400300c003d805007020f001e019200c619603900300e10041c03190760001e04401805250041081c034580e012100f440c154003019040841180b03c9051001a08242450780035140407400880d000c08403d6401c100d07140142e01c01c80303400d0800e075980007960b5600b043c06503070f20904403030404003080801d019800001501105a00052404055500040803a0032400382c100c80100c01040700c0a2940d40c3d0710409005038402d007422418009204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 21310527 1250 21309277 21309289
    0x206070815010c080903010603082808010504020904090512040302041103010b0a0c050304030b070503091e030f090a0512031b0a05070306020a020a06050f1501080c19021002071505060f 81
    0x81d100a0410881004034030034081004240c4480500c000c000f4000543d0f0390522800075040a5030030405a0780cac912000c8510b40008000000c0091152600740c05a071a0004110007504000880e941150300c403201400024028030400e405004141d5a0548031740c01d5005020440760b1069884024032010001403040e070b20000140d850075901490101c854840382d01d002c50450155500060006031000d007030012154014001c0c3d44581040000c951030303001e8240d41d07100d04c196000c003200c0b80c40c0c004100b40f9420401813001010050805021604c3c5c2d070740e88401158a654030745e010000150030210f0102084034100b070345810500711300c43c014000095540c507060345030000f5100c000c10b0642e0010380180694000d100000680d608031034104114600350484a4611408548e40300750511082d00221082d8010b100c05405050340406140c14125403005800701041300600c1d10701544903002e000421401240000e2030510f1040700c0c1788844800c1465150242da901601e80c0384030308141d582c404803076200c42c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 21311777 1250 21310527 21310561
    0x90f05100c0c02150a05040e091b0301050402240c030d020703020706020703172b06060915080c07030201020f030702010911150a08060406090c030b03060f090304230402030103030c0302060708 84
    0x80d5440342d45c401600c24103036042e20441d4000981d8050b18030410034000b00109a40c095a1038841c0c1561001612004041c01c0354000c4034000c1d071054102411010441081c4040440082a0003885241c030f0420340d40302d465a082052610791007600000d0300d000b01541071000c3c0c8000c198034001041c105003942c4c0c0d42c2030b2500120022118125001c039a052103813485042d08507000303100301001c82c80c03020700d0f50801c2c001d02400e00801c8045211220001201403c41d2600b0760030044503035451a00d84c1303648942c010b003a404100f040e000c542d028031000d000041168000d40c000e0240b41c000003950b44161410096070404030288506c240a4081d101c964080c5200403501c8070a40352030a82c0795540d5040010340100b006400c103140c070501e0b00c82c602a409405d030b4401c9070050320032000c80b1a966540d0000703102c100c0c002c99840c4080e4000380000c0042440c68086148400e00b002c0c0c016100c1c0b0140030100f012600241d1080d00010f22880701c1c5028503405100c001e40000f00c620384500c482c5031100420480c0884 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 21313027 1250 21311777 21311809
    0x10e0d080a0b09011205010c0503130212030c060c031602010c0806101808030c0f0102040501052b02070c0302100c02031905070e04030e01091202010807030b0103090f05100c0c02 78
    0xd440001c020040c0740d4440600600000d1450a41e943c4034060403042e4014100100d41740c0d860300d0b41011106000c3c1041d00d02c200c80719090142c17100c081e5401d018001d060b245010655200612010890f0704044c0030030f0303101d0703100451410340f03d281580344000c001c5841e00030782e401d69140c04080107034568401d01c5075500c00c1c0c0545030301514660851080340d0300511300500d02c81d040b410280100d0580d0004c0005d00d1290010702c1141c034130040054003a0700300d01c10303031050383d010410412828411000100803899244102840391418030010740b0390710300344d07449900d08980800c207200c0180218a05080d00c1c1e6144d600c14504040207072841e5000c41d03038030300850020f244003070490140300382004010058100944500c5c2d0708250139051134600901010b040c60b000394040b0f2000c10001c00c212900030003005156405968481c1580c54070081540106040d61300306040680718440007010034441c08141017024072410040590180034a0a0000c44004100301c0c401c11540c6420100941c0c2c40c81c1e030038550141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 21314277 1250 21313027 21313037
    0xf0c02010302070212010507020606010e1f11150702070e0901090215030a02040b070c050906100207030818100f020105130507090209190305010603051002071203110409180212010e0d 80
    0x80c1800010f1010954581c2005150301f000108200c00e54045411401240282c96040c0248002010881d040d01002150080b2080201803103200c10b00c00c10586000a14901c1941c2917240d40b024034946c04a411941080980c1c041e4904026180045006503401050403000700f02c44e8103241c0c00950111602c20452410107804008200700005607030440b00244103801c80780d0340d610790a152603000c201c102d11600e84900301c81d400003052030501e102904c00920165001c2c0c00720600f15036900b24150400ca4081c140c00c08090050411a101c00c1e1700c1001060b07054440310030903075140c8402400e580e0010002d4030500075582c1e512001510010b204002d458000c6005078603190b0140128421030108103022298584401c000000c1c000107500803010303680508140c610078096030080b4810f07449401d600512645402681e040680c1c0301303074829041e0f00c402004481c51305a90340b94150555202c080c0c0c4d000104403002040d011450300b00120101c400c00c010081c0b1540d1611600d20340c40d010f580081c039081c80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 21315527 1250 21314277 21314287
    0x1002040806040312020409140402090f01080a061a0901080102030901050c0a020c010e040207020603040803040506011a0702011110020a03061403010b030601150c02030312010311010804170c0f0607030504030f0f0c02010302 97
    0x13540a4046d035001d80281007007040311500e154031004108d001610705074081c40c0e04002241440e031820301c0c0181039a0620b0010503080450751341c0d641c000d1040a5140f41c840c90034980e00241a61040d41260080c0f004500150300c80c05c1c41c40d0b035582101c0300030b40b254015200810a01c09010340104090b00303042e03001d003090001d1402000201d40a480341c900f000354042000070800040110203009540554001d0040342e5141c1e88480b407042e01540f5070300c25801c074030380c0074400b0000645c8154040d40c41280d0755000ea0f038289040280d0346041e6085503030303400c001c42e40382c0c102070120211001d1207000204040b0002d00100c41201d010a072154818015050580c200100198a00e40642c440c1c0507910f501030b04880d40c506001490200c04c2d113080c04110350096a5818500a541c40307002d003d4010743d08001103224000c5134000ca20300b5640000c0801d45d69000b61100302056400038040b45102c1e280589000c00c19203050f150043c00c0c0180703919910240a120140030f0300b100e40c0110803c4800364282001a514 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 21316777 1250 21315527 21315557
    0x10507082a0610050906120f01050108010e0d020109020a050904020d0b09030309010b150a030b0a0f060509011403040b010b0c0a0c090e0d05030c040e070c020d051e01090201021015050a0e06010210020408060403 92
    0x1004a0301c0388c140c40383d820240002100c000550010074400c20501c25146000d80b1204124240c0e44240806984603c0b0070405101c185490300c89160031510050503d00c5040c910b60310880d0840d8100c42c80082da800200800580c0c182c2800f500400b08411504056010045011402c4034019104000100350313540100c58045d48030b00b8545400750541080340340031340355140d030300804c558005a2550300013204c040461b0781010100c0c0c1030760301903580300301901c00e103078200609903059400c800a0b2541900c84c0c84601408030f0301021081002c1c0009660208042a0f4048040d01d00101c0020038020424100108690122039400b60b50594400035504c2d40c043c1c8890100b10340d203e018003000b035445040c40c1c08403030801c0400241003000e90074000a00d00c4d103001950301d00b402c80b040d0741c0010340541c00c202130051103200c5a90180404e0292003004240c0c4036110b0000c00d612441a80029a9080014051068a41e0104424141009081ea082d49014204801e030354840c1d10262008050007101c088203420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 21318027 1250 21316777 21316783
    0x60510140916140f0d0c030b01050706050925050a050f0307090c022a0405060f1003020702150a0f1e0912021f0306170114010302010507082a061005090612 68
    0x10341d02000280d44d11189200e02c10095644004143c501941c50040324000c00c6019018141c00d101e4161911401e004e0306444410180000500701c1d0b00b240600c00040d01528100c0d110f500088880c040c08030b4240d4100024403d551019402c441e100c2c000403003201c00c2d555400aa81401c0e02c800c81004115108000003c0e4038040c641e259030100c0d41b240010184140c0d82c100150658070004440078407440e1580c80501100f001d1051040341c01078404000480c5540c080e4004200309031010300001c24445020400000540103607841000150708400c41104440e80300c1c0000407104202018004071603410100030701000398520840c020752407485280c1c020740d40c60403203410b00318104176982c070418402004001c0003010140030b05400620075400149101d641445210711042800401211507402d603001034402d50013842c01166051403c2046040301b50300007074076203d00c540f0b01c41603903007807000300b00120308042009001d10b503000c0310240d003001681c0e16000c825030032442c203561081101a0f40d08842d41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 21319277 1250 21318027 21318047
    0x21030902091302041401150f02030c010e031207050301050607060b040207020a091b02010e030909100305161d040b0c0306040603021203090111030a0207060f110604060510140916 78
    0x26000040e2400c21925616042d2154070b4103100312400c20a102903941c13280d800803828050090083c0075111241001d90140032094948107050048905250104401500b51503225009606c03941010540203035059501e404070350844454100781e070030742d810580070035258010910301134000d50f00c58112084548895049400003500903046600c59a01c41a5607006085529000700c001d0007100880441c2c2c81c41880385424601e030303500c065032038001440200182c85001904524000000c80000000a44108134070704807101d44100e4001c2151400454201c1c1842014026074030324042d500b0800000d00604041d0f42c0700602014241d01d0361140f04c082001070139141c00003908128407a51000c08154000041d0004003026601c00d04c0506e965a469512405442d0f9040b000d41e00c44802030080384e0080802449840141c644000482a010780307441c503003501038030151200c0f80e480042c0941c0c0c2000764107800c06414030403801e61001a1280c00308008071801812180c21030040c10300b42002034480c00601c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 21320527 1250 21319277 21319279
    0x161d0c0706090b06101403270303070f0e0d02030307260408010b03010f0c080115181410020c03030403020105031302030307050f0c0102120d05040c05030102030702010906140421030902 81
    0x290403881c0210543c1c02c141c2c1d0b2240b140300441c0a046180344103a0204c807107120381003140c50440e01e6500fa54172607501440303612440e01c0100703200700c0700082041018611503a03081c0e036030100f00003603201d02420102011100038000c1206448903030240e1000070494252541c00b072840c69103511248840c60b01c1000034086c003058980c0006000a0150054100c40681e042c00c80c001c019802c410390410040b03d00c4200041e0200300040f004008656000e507658983c0c48040c00c0950480c40350280412904445030042c4540f248085410711050034545000c1860400070b0008210303030029080007a07604c0c0200d01c030090400c80000300162840c030401c4130503458154003400700c0380c562032145000360b01c134040c0e40210002480303003151941e1103620004140d8105a440d291040c0b0380166030810078040c3c44024030507070b0781ea00c800d01e00207020389007440294842e1000340d0000607440d44a14104040c2c8101014144500344010244800700ea517042c0d207070300081d18030480c012503108107410a4000e41011314020b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 21321777 1250 21320527 21320531
    0x90e060406030c0f080c0d0b070c030e04020703030606020c01020610090c0e06040902030f090307170702010201020912060a060b120610090b0d050f0106020607020604061a031e161d0c0706 82
    0x80c1c40c81004000b541514002d9051b1030b80c42c40e8010501035413000c1c540e0003500c02105000441c105074002c0d8044003111340640741180240800b0801703e42a42e0010404400081e520b034000c100c204c1e8140498040000f00f44090308582c10080c02c000c10801c4c80d4010414050b030360700c80e07070400180074280340c0840d02d4016040b6604c4a5546240300025001214591404000f81d00061a41c6501004039034120354031100b1042030710602d003e040c60a03040b0000072810340d9420060301c03026079601f5554071901141040146030514000c0c40d500c0c00c0d100703560f000030440d150500c281d4200c2e88054800b40c1e84040141c900003c0240c1c02c00040b625094180d024a08062000a0404449507190080c85c49480c0b030303801845070303030760b8600302203944880231a000c20060b00050041400036200750403c251404840d4030700300de000078980001e818001d0980c0e9520452410800941d10903100307015610321440c050a45c02400e515040c40703880c2000080054002071200c4c9000600381d080000144c1b10310a42180c82 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 21323027 1250 21321777 21321779
    0x105040503100506040e0d12050a0b1903060c0e030a08030a140a0f0c1b0303090c0b0d050a0f06060503010612060b030a150506090d08030406060806040305040603060501090501090e060406030c 84
    0x6802c020a07066402c1d5010740e09000d08200b4030100006d40c012419095a204840c49421080e040010540030305072030209a150306000030340c0e50307503d113001002002c900c00c40058207103180f40c06030032600e048202ca02801480c01080c40f07550750114029090941007600d2642e02c0d03807280b4045004005100c2c400c05142114014410b01c51850b902100c90b02d400c006082000c00d002402c203490f401d81e40d04d071030b407018038807150000d00007407080c1c000c906000d2141a81c04081515801503d110b034000603d01da0010741da40080240381c00e601d018110300c985407841c041048604000300241300d03201c140142c805000741e400140502c401d00d0b40c406001080c1414826840341422000718005d4094000540480003c1490100d0795140403000c84d071240200030b00d16003a0305001d54a15030341e600000d00c1950741c90783d5804001085c50302848618495442942c41c0307a81c4a080041c041d003124925004241044420403060210703980090041055070800b8144c03102d640d0724640014040c00c2c1d01d410007484008080c0d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 21324277 1250 21323027 21323053
    0xe180607020a03020d03090b0a09020a03020402041203080a060503060402091806010308071b080606010f02010207020a03060203040b01091e02030402030c03100c171e07020a061a0901060503040c140105040503 91
    0x107110800030f0301c02c1d03080d200d4000303201d0800c40c1030300c980f410302810346c3c145030020440f690f21980c8018921480a0400d8103400d85d40e80024040340c1056003ca0803190701c480080042551024500b070303000e0a4850204a21400e240101350b94100c0100b0007070040d06001c2c04078409003d900c82d50f1000d8000c000898402c0d60f120b24041d0070075003007508100c0383c241c0100150101e4412000b40882540c0403034000300119550440119601c600303046542065541c204080c40c0940c45100010300a1405000f026070b0300d0410f803800c1300246005a2001100600c0c0070301d10071075007401001000d241c2e000c0c20350150b2a9121800083d090402841e412681441850448449115990030508010040352030f4404420803000203102c444c4022a80545054402c4480c2c00105600900081d0840c0c0544100d448031503540d510542100c0b109103c400c2c00340b030185a01e0300b584c80c20004007400740c841031074814110308041d038602017a45510b0107071150b48400324088840e5079100b003003510000c0c00c00900f00c401e0880303044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 21325527 1250 21324277 21324283
    0x40308071505070503070804120513090603030e1e010e060d0218031c0c0f03030b0303070f050105070516060506040b030307060f0510051807020703020a030602030702060f010f0e18060702 82
    0x200500700c039a041c0000101014051025a0320540058960010590341d50750b85002140d1145d03908028080140f100500b04103090004401400140c0e40c009035075411424041c0c0b80b003001ca4820b41c841c441f4040700602d1000c00410550748035000f802e107441c02c8009440002e849001d080f400c001103520100d04400c4000d02c994650060000540c159402010f007020901000c14003140c030000070502501480340014500c0d0310b062003290103840c00040a00020001a081d81d01a680c162801c0902039124800d0207428850241c00800701e08181c0d15200500b014140d10441c840c1014284c2c90307a0f100000c40d01c0d116500120f440002c020145c0707070798400a141c1140200441c2c00750700d25051034640010a404180c112000030703248010455000780c062503621016060000380702c14114000c2400000040e1a201c584901451140700056100d00e400c650003440d05000500c014038041e90080100541079401c1d04910503100d50b04d03840011039907108040781c90403c0107455486280300b10350030002a25408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 21326777 1250 21325527 21325553
    0x11070e070e040b030f0304120206040305010608030705010c051801120608010c0c06152706031a0f0604050105060418021e070c080303241f091703070b070f0504030807 73
    0x100c42c00c000458141007071503981e030001482d00d4011342c0100302c140302040000c000b0054003880206403924040e265070702e507400e69802d684054160307800800c4040800c102806100002c40c114684541040740b00d040c3c104203121402001c0f418805a40b23060044241c5542010014010420003031000b1040000002d0482a00c400b00380d078201c3c5030011740218840b18803044021a25a200903c9050a059040300b020382c80041f00703110107a07940e9000100051851441ca48002031100141d0000c0c9084c0e01c0e00c1c407a6000045c0003912991900d0010b00c80d81d580e02003a601980c020300b640c020202d8914100078000e02c66040c08402281c6a034031044455482c2c0401405124031850102122170b54450a241e070360b0100303480070f00e9645103040710a2103281e101c40c08050b403a61700418424203070800d0003481201d071181c25440000191a403605100d204000c083c2400e0b8410a20015458040261603400d03070440050025001c1003500b0f441c06003050310840581d4059600401050b0b650021403402440764118 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 21328027 1250 21326777 21326779
    0x314071205130602010203040506040605060d05070305060402040c0201050f0c0d0612080406030605010207030b040602031e160912051203060d02100201050402090c041401080901020c0f0606120105010b0a11070e070e 94
    0x82d10602240c1d01c2c0c418000d0b2402154010002c0c1120348840d03860202078000204415005802c421f40c0070081442041400c00450240c80500f00d941402c0c0140000d0b034030002000c0c1d06585c10b0005104180303414941196001440c074905d55180d1201c4080300029000030ba000094041c1d00740d00300c00a024074000248100c0c2c0e60342e14100061a80c1d13000580e01d585880c03002a00071a038040009010a90f1070b00150b9101d400560408490201048408a181000e40342e640070110210240d031481600200c0b64000381c01e4007910b45036014050364549548041101405901036008000700d84940c1b9403d0381d9211141d80101034641d80d02c0f02020080c000d24080fa0300343c0c403a900841c04952412003000c2242c050b203000158a01d0200300305001500d03948405020340040c2d642c00c01001c0740361f030300503c1614841c180c0700f00078203040d08204c400c0100c003113040741d151035241e4075010041040161540c00c60b1801aa541030107002402c207410000e0a2000030703444840c4000d030740360070410610b81c070440300c044c0c0300340c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 21329277 1250 21328027 21328057
    0xb030f0c2106121c0f050409060b0d06090203060d08090d0804061119020a060309050c1c020102010605030c0303120c12190e07050901060e060903070303020d1106040209040314071205 80
    0x100d181d800070366403104d0080c2081180041401850002d100e0707142d600513034015040007454150745070807000031039030568010243c06034007058074584401e05008560040c0101c0d101507040d0f050220016000c01e103907800c0140003860004128015444403483d0300384498010114940326130355010081d1441008058441213402200c10302d90b458036030051050350254000e04507000c801d0500c0c600340c0081013249025240c9200e4028040d180e6600da8010340044100015136085240c0c00d4030000e402d41d500c98000074442c1d00050100c10311601c0010a4400080c3c6051110005840e54664400c507481405101d0080c26540c0040040d416101001201c010160709e0040200c284402441c54640c1700900505070b0241c840401081130510601c5c24800d5140000c01840c90300c0c0c60200001c1c5004543d81c82140940c001d10095a40d10f0340008102101d09941c001511462a040d4002449504020720040a1198418044654055001c1900d5a4603841103015403910040c0c40068000d800074106006001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 21330527 1250 21329277 21329299
    0xb0706270305030402010c1406040303020a1101060e06042c0102040f0b07050706180801060f0501020601050a0e040206030a09051b0a080a0b01050d0f02060f0703090f0b030f0c2106 79
    0x50000340304415078060b500e0500f55150350f40119800b8120401c280c42c1690740b800000d10711300040c480c02d80a1071203034500580e10510440e002e0070032002c0c0c204441c200e0f40f401904100250083d0050b03644000111000241400c00c03140190044a90012011030542840c0c00c00540d00015030003401a60300d0004441d800303070b55521141c0740c1c0e8401c0250040035a0881c0c0d9081203d14011060f8000500d0300050307800009849224a900b1100f05a000054502c1c0e210410440303942c041c0101800341105894000480e0b0414070b886c80c2001007c2c0c4000c0c0662000000540d000140341d100582c05984030060ba250a030311410380e411184410082203100d0016a6070015100c1400500d2112459004100210b00d031700c5c150402041302d1080100b540e000f4140c064032001a03a0b080b0081103030b410b0000740765494840d05c2c00c00070300300845a00b01a10112001c04240602d130b40d900c050f01d50091401c181e02c1c1a5580316915581e2500641100780b0707821004003000e045000079503175980e1249000340d0308400c0e00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 21331777 1250 21330527 21330581
    0x3020f0402181207050303070308100b0c030712050405041a0f03010b030a020d0819080702010c05070309030b0709030b0a091104060f0501110708030a03050a0c1d0f04060b0706 77
    0x30b114800c1484140704001d1a08245420700c0aa4002e4521240080e00d10f455959000303e8115032001408600140d049000c002c0402122004003001c0c044020007141002045074100740d4a00c07c03040013402c4c0c000c2c1c202103030240702c0c440d004440181c00c0140051007a4225003e42a000d0701e48a81e19610070b451450407c28642014410380e061028014010700803403040d0303006d000e50a400c000090f140c00300c04001d1914001410394440c1f20910056640904514000c14000d0031209a085170b942040000c00070300010a40c42040c25064a4010510704010b484900003070714800200d60000b051043c04000308903c044440d80300700c003914001e14203407041c0910241000704480303103401410050b90b201c940500003544100c0041e01014640412149410789400c41c182c41d41d002201e071400000d85600030851072007214021707001c00c92004c2c14418003544200300000980c0e4408003d240c0138200c1d01016100d15038840d0010002460000c00c4243d0700c03010390400e84064200d48d035520701c0707401e841541d140780 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 21333027 1250 21331777 21331781
    0x50406020c010c020616020a090c08011508010308030a05190914010b041506030507050c101a0108040c050103020922050f060a030c03060b0f0907020c0a080f1e01020c030a080103020f04 81
    0x28013a40100b10310715003440201ea80c0710764064544180d0308500402030204000965102d02543d00c402c5840322405907241070a45c9066000c08203480e002c0101e50801040010203860590350091038030f08022945640d00461900e980f82c1c0001c0b04200a801c0604810a1140740003031494030b17040034002400340070300c04003e11003503400c5580d0301c42030300c0c0e4a81c40421a80f4400c0e8089038004071603141492402601c1940185003800d8000144222071340d40c01445149880162182c0300ca11003070814004625040d101d02c08001541d00c1914149a000600e550050352034003e16140c150b0181200c40e0070051a5100c2d4005040071203802480f216110003159907441c020140d2000c0300e50101c2d100e60894110fa07683e0015281d15428640c002c0d03003111178020241e588044151040c41a40c1c0104841820b0104111404c02e055000045e01c2d01f11203040c00e03010b08042155126000c680300803e82c10388040100318028821244801154000030401c840b080c1d40c032078101170480303000b280e0303501a0740f8100040000f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 21334277 1250 21333027 21333047
    0x11e060c060207031407140721060b01020c09090f1c0e101101020a0e09070201020708041e030204110a030b010801050f0105130f0e01090c0806010c1e0c1d0a1a01050c0c030d050406020c01 82
    0x21102d49c41308090000551190040d4803111010320541b1100c00d450381c00300d5021802a102a4465040a01c140354041010085902180000079005800342d24410000d4010440d8441a900030307072014000e5041d40c2d01440044058080c0e200085540d941d00e00c00041c008002c55124038407401f19040859801403050098451940d00610031514091406100100503588036441110060441d0320002c05680d851245580d490741115401f1b43e18141da44000b0101d03645200c1d040c1c10720100600502541d2038842c145106a4000e08105544040c41c03010805810350680c80794542c40304200001c10641e21080c030190480c0c007102400d00800c0f242c2c0d2402d0360010400c40340d03d8000ba109040c01404600780c60881020321040b000c151200d401d0307a4950280e40c01154010140035440d802c2e021400300502c01040b0b40c00703003403461b040003c0ca40c61000304124070701c41c1d082c950403ca8045054058a0780c14411103512050090444081c80b00001c4044d00b01d070068814480580200101201194003890400c2c6d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 21335527 1250 21334277 21334319
    0xa0201050903040f06050a0c02060d0b0f04060e1801020d06060e030f010207030203030f04030c02030d0504051504050a0b091f0c0212010218060d091a011e060c0602070314071407 78
    0x13480c00c1d4244030080750aa000500071000b00078569500b040540c5502c1e00500341d981c5031000c04a5000c114105000740c0c2c480c010400fa00030781c41c000040210030b0248012942102e0740000d540c2440030701e18000b501a0080d580c4441e04640341c0701000441e26041900a403142c80d0950940c1c1d8a805201c40d124205d00500802a0144c2c00400010385080000307030009030312a200741031140c002c000b10780101745003001c200c0500002c5880090141f00390f103040c40140107206900c60056103843d04202c08201805803d00c5a40400040402c0d929200d656510910314120010102805058140c040041010801e01016406101c4008424031312501c18004c854101032000d820130b50800396041480b400b503001070613100340c0740c2d40d404c21100062401c130a1480c41e045a844d4000c1954108500411881199400d1102071014040300700040c5802100d0a50543d03041040142c6410031414240e403204d0f081d819400b01501c5c0001c0400810501d010035510b021543d400720348075552100c0e42c642c80a0b514203c0b003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 21336777 1250 21335527 21335549
    0x11151b0d060f12080d0b0d080d0c110c0a0504050604090f031d01080114090403050c0f010603050d030203010e07030e15070f080108010e150901020c0102040b0403060b010305010501120e120309030a020105090304 92
    0x4992105d865400001110310054420809108140c542c44401d03004040c64008582c0c0f0f500f6035207034250307012842c1031403681d600c4050103640c100c6000080294107070f4460503000b03507116000580c1ca071b91141e104513117064000e190030640040c2440c0042000c8843d200188011388140440b100c25407040c1921030613a5210400100c80640c0c400820003004030040088041003002c00500c54500414044071115034070003c000715019045103000c6060031481700303000042500c144010010f1881c1110b103150460058100016160940d071001800c00c101401c0c04d17641d0404d00c10174400c050354402894082c024203030381c98a07016620391381140e082cad0f15041c6c00d50381180e100c2804840769800d0300603a00d03008040301000615065114501d0b07030030798101c2d91089051440c0810104117104c800e0242c121200d00900c0c1c108501d42c1407000180a603a01420500030043d502c8943c0c10485204015480740107121450040c0c40703107806400d0603600d52080c40ca450041d401c0c080800d0a00a0010035a802d6425003100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 21338027 1250 21336777 21336787
    0xf0112020a1217160b0c0f12090102090d08250302060712090605011401080705042301230903100203060310020703021204030503030a0c11151b0d060f1208 68
    0x645200c12098140c142c1d030030098036841031a5043c503480285810303040c1e03e025564402d0b03181081040d940e8002c1602c401c501081201c82100c808040c1103c084181654402d42d554403a200d202d40280100403a058200442c00030f1141803149417009040001c0284280004400c10081400f1a201c62200001c003d80d03c42c20100d510039000704041003240385420400942880719482e1441510403e070300032200303080781e01c03601100c5592000b00700790b0011040c20602d181c103242c81c0d48810b24012462040c14290124070440380300d680720b640d013417803501601d246490243e500003101310b40d070f40c0c000b0071164440e102e507048554005106000ba41d1003800000c005d0100140030f0420b810181d03220f44421021406100c0000c0301480000313002c2e201550148008648900d44140c00f0002c8030602907040c801d1048032002d060800500240c01031241c01410410300d45521103683d0010308030321014104804903008283c4154607080b6a0290080326401c080110809130388010700d00713040f00740c807102400308401000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 21339277 1250 21338027 21338039
    0x3020a080f0d060e0403020105060d03020604030c0807080318010b1c080309010908070308060103050711060a0c0504050406080109050105070e01050d0203250507060b030d05070318030f05060f0112020a 88
    0x10207400080c045000d424038106101007042c0c1180c0c22904501d0150440605000034076909208899100005076041c141c458129100a961048010402000c01c040c0d007074901d0400c000103007a00d0780c4651000342c643e16410107444426411254031141c40056217400300000c2c0603d031000d00044c422101c1003104100c5030803501c03071185690006003c10701640d2a280004002400c0d04000c0000c94000d40d00c050240c14010001000e64001800000c02c22100b0340139012a01c5002c00d03082d030000221580000c121440843c15030356030050368001c0386d000c0d1502e0300002d0090410b4000d01003151180c0000c01055135811419901c00c04008441c0340040d02c18060310414045590065401002024900d203070241100201c01d00b05000383c40840010340c000c21410200300c400e001e0842c0d40d240031800350005040c8000300a0060250034000b41c10482c1e61144000c3c8142c03003d40500145810204228040d1030500305540e03105016a03881100c1c8100600000f040e1000302e2130048110341c010409403000349859 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 21340527 1250 21339277 21339293
    0xf030f0a0507060b09010e0a05010b03040308060105070c05030d020a0314030c03180109050610080606010305090606010e0f06030109060e0106020303091c02010b0a0f06030e0c09010302010c03021c050306040b0d03020a 95
    0x801c04880103a50f0712000504e139500c849a0078024101002a11514a88145214256081a440811905005d00500c800260884241944a4420700e8040d807103210301e0900b40d2000c4500d900168140c0070f0b102203020380c02c3d1b0210310f1004880c001d854844403021500317041c0d401440100d6100c82606000d2010910441c206458915070405040000c648101c907901e401d420450b0903682680882108101040103000902c11280e00c410242420070451409803612038842400500c240d042060120610300c0c5a43c80c0c040303030515220058401070b2a0340e10f641419009224600400c11074080c1c420000902a20020441e4031130306840001e801202082959000e141080100304401d6549034880000103840e130b80031110081c90102640c0c0e903070f50b180c138070044c0031111850402c0351140c1118414558503110141010f044135420b10704050421307940d080c201d0030906c880504140e10260ba11400c3c00542d13100c8040c5020380000c1781c082144000040800c01107040c5c0c2c01d8000e01503000b0f0704884001c6280d03d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 21341777 1250 21340527 21340537
    0x60c0306030708010204150e0f01080601050f04030501020d0506240a03020708040b221d0402100318050102070302122b15030b01180203010b04181d060403020f030f0a05 74
    0x81c1c00c440c180750311078240d81d0990700581c0219045441c20300ca82060241d00405040d440d0b01c0170307603442139448480c0000800504008250b24140300b030005251104001541c11a4010f42d0800001c64940060f10f2504018017420794803944100c189508050802c4c20004446000d00c91840f0a1480d03c01000c4e0180c0c080d4100034030650b0080343c02d00c00000c4050300b00008100303420130340307503680c41c1502c0c900d050204842c03268100c1d400d4100c1c1d8150610030a04000d800b56081901104c06482403841294100c001d020010440b02c0d81c0042a60305504000054002e448518800c3c1c00399040250488001b045a00540b80c0704030760580d00722600f08001e40d07003071052044c2840003040894000311000c5107030062141e0354402c46e4082215801081942c1c0309c403181100f051040802903156500d041c4040c90a030240d40500b0b4411440310701c1900040c45140e010a68903c1441d090710f42d9a041031001079103602c0e04403020780c09809442c120340c480301000300854480c002d25070621401c02e01038050407138440d00a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 21343027 1250 21341777 21341779
    0x5010509240a03020a0b07051203010501020d030b0604050d1a06060702011205180d020a050609030301030804030308070c020a09020301090c030c08010603090507050301090c1806030308040b04150c0206070f020c03060c0306 97
    0xc02c6008405600ca43c0b440102400c00c040b4400c2c0e481549250651a0191301841c50104100520041c042c61381e000c07400070202a050b14012601d1060070000440b180300324bc2c481079010448140c44c80800190002c0c54103407500300c0c4481c40d4203580b40d0050055a204810000740000e40c060001000b2180c254001074001080413181070780c04d0b081800741d500d481c1c0c55010400150b44451804010401c04000c078650280030f15014508551665542e1213460180340401030901143d200018009441254440c88940d00101180040c0b503035010310000950080c081c28102038208101c858205019000325001d0540c15510004140e103060f81c00c5006050f040001c0b030b51402404000500c030383e000d01070014440c0c000d8840846e2180b4000c40d5401d45041c00c6881c1030b000e802d203407042000c030350003540d03c550003a004460404250360b21b00d0300102030328848000c0340810b842e018154041ca0782c0082d1140c0b1401740d58a9522b2303800003580d002d0340d8400034100180d070b05511400c002011100403001035070700140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 21344277 1250 21343027 21343039
    0x605040e130c03030e12070e06010c080d09060c0305010b030402010905041805060f070807020f0d030f0603050a03020109021e03060604020703030b1c050d030c1706031c0c060501050924 81
    0x141c181d45148807944190310503800128900e6941d0341034a0114103c8010501c180014111945816840c0d061800c3c0280340905210141a0034414000034030200c4421a4030940300b089501100d1030003038011f005000085000910703050010a07407503146030881e0f001c2e613016101c0081d118580b60400014220050340c12036141c0200e50b03010001a0200800c50160b440e001641a80d480c00040040401d0401000003045503c4041c483d02403040100c0e42902050b0a0700d00032031402170b0b5890100c060401540020700d50b20451440390203056040d4049000184201c44588540c81300e41200c0f00203004080381c07503a05803c840702040c002d282036402000698401d003808591201c803840042c0305c40029841e40c0700c602d280c0540302e00400205102c0800b10032003a08080002083d40070008002c283c245c12070101002103c00483d000355130401c031750b0003250b203040018050100e01001c0107200107100c9104591840c148000420303907281c410b9907948142200c0c444081e19604000c0c4042d01c104030201d4845d0014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 21345527 1250 21344277 21344311
    0x21909020403080306090a0207020607060209011e02030c060603060c2209090812010b03071209020d17090405090d051903060b040311030f2803110106060e01180605040e 74
    0x2448a001500003140243d0402d0340b01d1800b4018007030070106c02041801154410080d40c0b0040c3e4600b416128003d4009000503210314082c00142c6401400b2800e10440b15000c0070400340315940000100908226030301030b1509031f2601418103694410507541007240e14030510241301c48000e240506490702158011809500340d0701c43c0c441d8110740c5842d2041d944071000043c040c1c101100707001c41e036004113800d807919459461700d0140209044001d15504401c6500e8a06890565071411305c030040068004040340c0c034400e2080d007000c101e0391101c541c2c01d0045003884009480f1074408221030a0074a403d40303e851403c01c0b00205c151181e00700900980501d5540d0030081030010314400500083e40c4100d403164070244050040615041c0e4200c0700020507480407a5600c1a100d80201001500d0348006034101061010303d01640c00c144a0100c03051958a42030000600c01d80c00440700140d52806e0321182882007440c0791031904110207025034004510100310030002001e0062500b544520125a50f0b0810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 21346777 1250 21345527 21345539
    0xf030406051e0c01140f0403050f0318010c050a020c03030405031507050f070f020103060e13020103020309010e030c070608060d0c05010507020604120b0103060e0102040f15050c0703052104050d0219 87
    0x503003043c0000800350b9500c24400120780c0c1d5080000c0c3d001204140c0e8601146404e81c0d00403c9071161186402c440307540440410010090a00801008583d20009010000200c00c0c008c0c0160032140101c0c0051059070221200c038140801180c05580019010305517000c0c40740343d14054100301425000400400700060f260040b40f800c0500140d520480503800d54614500004080d24440e030400411011400b00f030144140c1503c01081412ba42800e0140c1c9942c4d070000e000e40100008072104840d0b000004014195800201e80603080d59203503140c91045848072001d100b60302000c160000c000621461003840b4541c000c80c0a010760610051a075498151a00303034680c1c40c11400030048890407881f00c01401086600d0182c2c100c04407001c0000c40c00c1c01d18245c0c0c006038042641c443d480d01082030750380c250521407040c01103a03d011410f5040b11482942d92601c10307030750010b800344d05404d5081e14003082d059108440890b0200c0d01c00400d000912100c135020007110011040301103c403030001400000f03203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 21348027 1250 21346777 21346837
    0xe030d020711030d050c0c01030b0f010c0512040305060a18050303180a0f0b06090108210d0902180103110a060f0e030a060c0e011211040b030c0c010501090b10020f03040605 76
    0x250f40c12aa50b000e48540900d04210300d041030040c47d840c14141042541c07001c070380707481c005025400c00912f4074907402e81300b80c10300300c4c201040c960f611403200030001008803c0c41030000b00b96000346021201042110096034404607002103030305000340160810004120058402600d0703900300c860ba0400c0c7c42245656580d210715501a040c0d08440600c0c0307084c10001c02c0d14001c0b02c0d181c010004403004d440780020300d0910014204481e0380c0e542c0c43c00b401061400300c0d07000720391041d1011076000e0040c460300a00d0301c144d0410070009110454407200060001d40041c00c00620210840380143c840300312080c1110400d49041c4888035806800d8490400311002060460281c0252450300762034401c001e03401d02d40014010116400c00300102c0c0e0404050701c03d03c80d2040100c408a82808a140d0313200d4980c0d01c600d0b00c035886208030005941d8202800800c08404c0f40c1d008210a4804071003981d00c40d03101c854181d0315006550508251500240001c000d201e000340018002402c20000d155107042c010518004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 21349277 1250 21348027 21348043
    0x3080a0e0907110c030a02010221090a03050303040507060302161502070510150e040c0905041a0a02040e06040c080106050a05040905040506060306070810030809040b04021204150e030d02071103 85
    0x40002c844401c103c0100005024494a4100030f9010303113403030f1000e17400107551522030301c9002c8100e4040e14140e40b41d0345240002d40da4a00d400a14a0600c60380d2410400eaa070342041d03506403110701030f40e0b47c0050114024030031500350300300a5522040074030f038513101c41c00d8181c0025006c0300300d00c2e000c004d0301c40040d0f024001400341140b1b2000001d603c10303101c40c07465020500ca0300b204001104580c14000410912040c08088035181d81002c190b60f40c840c580303206030080c0b403c1800480b40c0100140f0a09030b8960b0042e206036014142c00c07404036500c00080105031800c4460074000300b61000014840c0d035106030000c0c90f082030541003c2d0f14066842c1e1143c0121082110251283c1e00080300b41f2601d880d09000e603507000f801c10328004000e41085040701a00040e2448000c12020000a1010081d01c039504a0500700400078000c540390b18190000004801d0111022074402d03030590502602c900b040d00c40d948022600f40c0040d824407403c1c2c1c403140000d6202c0d1034141c03608100301f80298815501080400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 21350527 1250 21349277 21349291
    0x507170405100b1512070c0b0901060927061508030d0905010510050109060e01021c0f03060501050c1b0d02060a050a0201140f0406020d0b041a03190c03080a0e09 71
    0x182c03121008804400300d881a50080d0700c92620b0040701c00c0982c15520035100102070b80c8136113503419165030005503070900072024000c0c41485140c04000c40c50384194025002c540c201c0206010340240c2211401041e5490405200030404402c00400410000c0d4009001034a045e0a00f0f09403e4075501f03218a1500103d000d4600c490b21040c3c1d15040013003e009140e0400c03903a58a500007242400c00107087d00034180204c0082001000c1d07029516072081000c0d4400900d0700000b00b03500c4081e400d005052107a03081206000c02c0c10140d000416511072000c5482d5000307080d018141d42e041d1051955801013900000c2c0f5840060030301d42c0005030341c03450010031010100e500d8696940114403c040e094500429003507c0d866406e40400ca03412800d845001c2e4040e078010320042c0d5a9031300105080080c1401c80308150098034100003a40010006440c080c03820700d048084640e50300c40234540031459102100300402c0344511180400014401601804984085040610703400183d0750202c0d2806d2001c071041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 21351777 1250 21350527 21350533
    0x9020703090e0103020f090c0909040b041b0311060c0a06060e0403120902011704030512191d0a1202030421060b010e01020c0f0319060c080702031602040507170405 72
    0x50000c240d0030410410050104080c100e00561458000402e0602601d400b103000d0140e8800040020301c1450844d07440010041140c1542c0c18a030800b1000d014003220200c581c010340c101c13035140000b500c0300900e003125805210031030201d131035600384052508950041200c43c428082ca0800041b0140502c40180152800320710380b5280a0400910801c51207904010043c0781c90310800250b40d010601c6e0115060b54903c0250684444c5030860b841e20030b080b1548000300035541402031a000d001324810074040e0303840f01480b0080c9a0159010016a4986013990340d6204076038101c0000d0420818203410b0030580107590a00d0340e1400b01c0304000141000b548904080b0030902410402c95121380300e4111170030320300740c4404000080049c1d81c80c900341c0c07203007849840b80c0e80100f5025a8108a060104075034120740000b11481c034604140070f0712606041c500400c440000089510348000b06a0340d14050041804030406a690203100c001c1030041c02c04020488481007a000d04000d08a429000354411401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 21353027 1250 21351777 21351787
    0x501020904060501050c10020304030c0b0702150901180f060212010b0405040f060503060711030d0e01020702030c030a1a1506040303020f160609050f040605040c0f02010c020c060403200a0902 84
    0x10071048503120f4201038140002071107445042503000860b841052100e000060796620359007400d0b03070701e5081190700034044082e4004028500303502140300c180f580c41400c0540715981320030705c40500382c07120000e60069501e1210305d0b120100700c1c2c202422061034040c00c80145080c0740c58681001c00300c3c003600300001c000c00001d010402030801d40b0840d15650b00c05401008081c0c00c00300040c0d190007016003144100500c90402c10039845040c01210030704100769408100803020706900c0742c085d40141c1c03002da209004070000107c83c2d0501040302c200088d8811894690040740d442d5046480c0c6001e00403c40000c4107010f40c00c01c03070301c48000920145000e80c008010342d00320340c5000c9280c039960180d410001c00d01d20a04121168010380710005551007101e2419121104101081c006c2c50141e10940c0c1c494185010104c8050304841030429010b00c41e8024021880400410399888003810070301604030204010800c00303d403508120074628607401d0000d00b0203c0c01e6000141000d591030300074070112640090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 21354277 1250 21353027 21353029
    0x1503031204150203160305070e10020a020901050f0102030708030403020106080d09091b05030c0f0d24060804050a02040b010201140f0108010b0108090d052101030507030c090203100311130905010209 87
    0x2c2c544840d1001c406602c2d40c604501c4082d000708a0714105014952144045015075020b8407081c2084400030300700c0580084141d000a503542c01340b40082c2d00450b0321200200c6c1900b4281c000300c01014068000314900031507039850080940c8010820b600710b5584090100d405507050106a0701c040e880da035400070f079074202003112049903444002c5501c0c115070101244607860704030041d02d074003500510a103174a480c02d402d5140494070800d0362403c8a01d14000d40d08100e402203002c40304401071459440d80036161210425200102c0a44000e001c40d8008411400107203040e40100e0142c20045c800031400075080135000081c17110a507240c44d01d0400c0703640144021142481415100902480c047c0024109110350586448400e8680c90410000083c1c1004101402c0c4078040c6c0c03882030706100c2c403440d0303540d08265840d118540007c841044a01000290340c4505009581c007990041e0a12160549036030b9400c1c00c04001d100c1c0641d000000300c00d217110242803902c101c84240d80200005607540b64120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 21355527 1250 21354277 21354293
    0x5120106020303190203090601060513030503121e01060203030a050c0412060f0c0311090d030207050a080f01060f0501051801261b04032004020d3201080a0201081503031204 76
    0x110001040c0305108206447d9000600603045a01c241030155076124944400601014a40c2001c3e00d1071000045075203d804003500128424031626002c0300e003103021102c81c0c00c5a02e80a201d180010b07407051003c07959801c41c40d448070340c1000440450514203503860b4200210820280c000f6070310290b030703540f0303032000c0d18024002e0341174003481403404000500c07071b00c8103110950107040401401200c500501d41e08250003004540302070440188040d18050356501c80d01e59400f8082048140b55080c118005050386030316442c0d50a4903016161a03060a4041100080840c48144000e041080e203c120714140420f550103c15507030b40d2000e540402e03281440440c40c2c800c2e807120a03141c1d41c01c800c11041001c5031030f0103c20000f2454219040c03001e4210640050041c2c002c510060300c100d031502c8050380c030701d0130184140d103c80407120b90004240e507894002c8a41c034181c244901d0545410a2001100541c40b42c0701490780038421600960814180d00086880c540142e01d240800c5900b0b4028441441000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 21356777 1250 21355527 21355561
    0x3090b091e0712060b120a0b010305070602071505070507030b01180e03030106142206030c11070b0913021608090102070e0402030307110303070b090714060c06010501050a05120106020303 82
    0xe10081c12032900d04503040c8050070601c403014028545d0307034142800c03940e600c00819500010140881307c8104aa0030708041c2c40c03d0a20003220281f140c10000140c15001007444400c1300c01e004100d20034540d2008040e40e0760b07800b00320100c1e031500a041001c000541585032490203080c480b48110380e42140f00c1041e60441d5001003031011503500c00c3c030041128a41c0030046400588900b824140c0364500f11030b0b074514840e16141080100701103440c2c00308201c3e40c10340c080c40a80c0d0031503981c002803003100d80950381c507a102806442d0b0f0201040002020b42e090862280400c0c0301d20342c50043c540701c140100d00c240401d01c81d908031002c840028048040c3e40e41041004081e220071051701b0294140f9600003581c038031039030303c00030b000b1050390100101542c0d003441560f000d00e40201d0708544070700c0c2c12007020f80c03929164041c0b03003514103880001200c03904007501666440c0158100a2403203909240046d9110382007040014200802004101c3d4a0380400001074000c2249400854613403c05000c036105076114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 21358027 1250 21356777 21356833
    0x20d03020408030702120304030501050f0402010f0c0c031b0503010227011b11060405060a030504060e030a17090712030518042a030f060305061503061605090103090b09 74
    0x140001e0144030808400c9130416a8100c5040c4d4034200940c41180c103600960340064419440c02e800c00c411404640184c9100c3c0e0700c00d80c2c0320f24160381c0785007040d5812074400801074882e00102c601840007030b050402d51600704e140388680c0040241d031900000e007681d01041c00b002e11044c403c008141080450860b101c0303d000c0908103040300e44122a484c85203407228083c0a01130b446a041e8030b42d16030721030300200e0300903000c0902400d07981d0703000f03a03005005000e003503508449451030310710290041c500c080b00350b03580888a9990900390448980000000b08405020380034035008144002500000302c10b50400c400d846900c800f52202030b896050300e441300c02420344e02d020780e0402d241c03180700010f8000c0c40c080d000348942030710060f03d2444408600030602644070209003442d041000c414008000760292185070003da660341c64003034001c00c1c181c54000585200300c0c4a800c07500000e081d43d004001614400e030040c9070005851600340c40b24030022500f6aa5402c00e5044030100086001441c0d10501610302 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 21359277 1250 21358027 21358031
    0x80c09070e0607110406030f060b030f060106050f090a0e01080a05010e03030403050d0c0311041403010b04110405010f0e0612160207050f010309030e090907060f030b090105010e030a0b0a020406020d03 88
    0x1802401069040c030801200400161030701300070041c10f5403030741c0c414409150051054014100c0902e8804001c00c1c0480480c0e00ca8030506104488042c00000c50a05903185541c5103414410f0300000700a00d600510100c82d484040254045000010800e1050003055440d00508402e03940707080c02800c440b058840c000301d0f500200f04000c0031940100c00ca40da8182840f00018055054402c01c0300288160700441c00d007800001400100c901c056000d101c2d031004114000c20031408031008000407144458881040c0800030312040050358000d0021082c011030300d040c1149001c030402d00040322503003e0300d10207241f555150240141140060059112062075000410303000381801c00003003003510949006810542c403007800c04100b511a45d030300842ea40000e050100203003005183e403501c904080c0125800107003101e018503001442401042008031002e00004416400e0000441f60600c0c800899034141c8034061880707001411361062580b0072078000000503147ea06002c002410b28041d0007510381058 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 21360527 1250 21359277 21359297
    0x140402010813020312031510030c020114060f04090203030403050d030501030c0b0a0c23070803090319080405010305060607080d090b0606120609070309080d020403020f09010e04060507020c0307080c0907 89
    0x6100005c0ca040c102d414054215140c1e038612004600701c80020000c6074124160412a0240b15010340003012094000e40092044500800d0044401982100c00541c4040b1400b46080d0b00d041580c00b003015680090300b981d20780381e2240c46407490402c10a4540000a81d6500104113020001c4040400340400c40131031490305040794030082204804080c0a80308850404005100e0210301c1c840503180d880f180240c1d035440350b0729200143c030b07a00710008107400380c000c0445403403003114407034602480c140c0d000c914241428200300044004180c020071281e00650100000e10104403c000606009084031402244000b160b2070142c001c2c0c7e402078181400b400301071205c08080d0100300d0a640c0d01441c15100c03030384250f89074402140a40b11501000c0d203412000240c4803d0f08109400420a607130080c1c0384070010407446020b00295407424840c15034010088404540001d0b0190409038000ca050300c1121380100815001a040c04100d52003148554051201101641058103086500900c181031080403a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 21361777 1250 21360527 21360529
    0xb04120b0709060c110103062d0509061e0f0607080a02010c032c0a060203010b040611070b07060c030608060a0905010f020c0607120906050705030613050411010507050106050414040201081302 84
    0xa00313400500e030348505001000c2c1a44254000c00007080c0d050b1034401d0103c158415880030b00b4000a4001507481103440220361400c0001d00303107000e03602c0a401c1c00c21118214000013a0000c01030b1810398041b4840704c10904941c1c0320006443c06a0003007100a50740d40f58410081d0031a00625500f13001d144c1000e116040e40b020440300c900c240e1400000780e45a07541080551410190b040724000d006502c04800800e18400d140060710a80703095841c1d8a08140704001c4050f6900300c1c62049012410040142000040454102007407000040c100401c189407075641c80d42c1003035011259024190f07500d00400c010f0010900a61a201603078002c2145420020005591244401042007082c4031034880e207000b0303241a079404441d00c2c40c0c00080c200514107000708000e290782e00c1514828070620341040032940218251003007034061076000b0018a2400b54150054845401ca0f00301680c99540c0c4e80c83c0040d0944650040b5181c0f4a402410704401e45071030701c005130030b00d4006804140d1f6811410350030001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 21363027 1250 21361777 21361787
    0x109060503010b0c070801050c04030203060c03060625060606031e0504020a0b070201110303041209060f02101802030f030306150408030d020315031c082a0c01060b04120b070906 78
    0x151441c1034003c603070f00e000c2e01070040c5c6016650750008265619000420000f022507102400a6920071401c0d07a81c03a4075200c114816030300042c1c074000c3d4080c900b0810524004580c030403071640444c86d4194200d018980fa00c0e82012104030f0351120011039240c20315540400801043d01a030601c1032401042207041ca50049107140d8960701071f08200000c000340c2582075a0040d040c54490344030940449640b49814a8240d0f0030650f11042c000c0803510100c00416098003c0e40340c005202001da00600070841e070800e064001d08280385031500d2000d640d09014000d61405d004102d040d00005004550f0380c2804018802008a010245d0881c2c210034841402800004011590400c0ea041c41c0542c8a40f02c406c1c0b441e10184441c04034691600c900c054241c807095000c1d01c1d40c0c10422050f110f404003581c0341071000411400341c00103201d03040b88200d03401e800ba0103130001a00f40304019400000f03035607850780f20040281c0c3c030640080a421181d2170f0994100030b81801d0141c0d2000b068940084114901100504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 21364277 1250 21363027 21363029
    0x130b0603010606140f040f030c0f06080402030a061a04020403030e150406050a0c080d06031112160b0c030403300e09010302040504020d0803070c0303050610021e010609060312020c010906050301 85
    0x4800d00380090700d920004581700c2914050811214003510180c0da914101c2070008291189400c107420701c03400050a0f50140c00150310854001d0003a0044036802c0e583d000041900c198503122041c1903905014079521b491004d0406141703e40c076031100c0c081c20402080490a072090804a80400c00c2009008640d03206042c1d50030012282050902036660389080e510f58050400e0034142076103003031000420301201c0c04103100c1820041d5090515800740d000c481c0d459401c0549100c0003a440308000f0048010440018070011081c14240c81c201620b076503408030410011400d10303414030003405a0400e446081c0d03441e01c510b01180e06140d20700400410100d912840140b00c040e225030307540ca00040070742d00d90303059408038164400112507880c0f60540024048aaa103001030b00000d00c1d290019826003841ca98032a00c00040350000c0400c3c420724043d48181c0c1036589440310382c5540301c2000203803128070350084a014520402d00c642180441d088000d25090034000f1641c1000b4030030404200c00c54005e81142c3c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 21365527 1250 21364277 21364307
    0x3020d08030a021c0902041802030316020f120601080609070303020d0c020105120408040914060a0b0a0c060c05120c0a0903110402070203030d05160f02060604050406090506130b0603010606 83
    0x40e849a40b14102d079402030043c448002c0c1d40e580c000c1c030b070340c8101416580a5040140300701c4080220001150038003071600801c40d40250107910400466004c0c114581c0c011614900c003c01d40300c1c03003ca2030f0001c00d010501c58030442100307501080052042d42801d210441d845800d000c0103040342803440c0c50086d6683c041801c05428042d061000f2800d5900c6681243c007000070342e103c28486814240380c00318559015101c0c41c08490301c0c04202989040e482e490541c01003100408188143c0d042c8001455140d0240684400f880143d90001c40051203070f00031921a9440d0380c80b0305031950021003044c40048401003001e03000fa0010040c0f28540c603080000c040640e078000f0f040d502a82c0c02d403030204000784513090003e0360511002c0717040403401040390001d51003296110600c5401d0b206413141552510380041101025800040014845003029805554010b00591011444048949810782000416203d003d0f440b40d032450f0200c1400a44502a0b0f04880160300800c4924034200307000b000300360094504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 21366777 1250 21365527 21365543
    0x315010c0c0312110303040c05010807030b0d060c0302040e04080c1c0206071107090f0203060a090c0503010311030a0803070c060c090501140304080c03130f0504050c04050402070c15050c0106080703020d 89
    0xd4500b0303030701c0382c6201c242c04c40144040326900d0810f030a207030700d00c020140310303103800606450001020707148680581441100090008100e203d8503070b80748005402c0418000e8205a030900c80005e0b40d41c1c01c6201c840c082e9000741511682c61160180b45420840b010020405400c04010040d80841d80014a41d601484038500010303601c04101c061410006250b101801a900300344100c4c4c4a0511607000310f000d100211940c1400300d0343c039a118400e44407020382490103e01d041c001000490f400d86010001c01c50014240d81141c4c40aa40f05003140d002954890001542400c00031704024840c4101d0503000403600b8404441c07460400000d2081c0d00c1c20055081e440750100100d0108080e04050322a80344802c8181d036150b04e1030a8030420017071090321689104d543e803542d00081d03505091003410301421400c01010f02d001d0070700c0c0901c0082d50042404441455522600113400c8403102e200300d2600300c140d82c2c0e907595051245615400d4800710340200440e50403042042005130354101c2003007c1c1507804042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 21368027 1250 21366777 21366803
    0xf040506090d05010204170705040501031a0c0d0203040803010302040b09040b0a09030c0b010608040b0a1802040c021f0b0a170d0804020307030c06020616031a12011d01020315010c0c03 81
    0x800c007600041c441c01400396001203000b00301500b07c20090014080c01c00d045540803070360741d400c000075200d0031703c00504221004078085685c2611140b88540c440e50359101503160034170740f01482040340e000f2101070341c0020000c00103104500c0c050080e4071750801d088035440c14508280c0c544826919015049100c407aa0700c61219042600500000b144150000c0d040d92440d0794509000c0d080c010200c904503140c0d5808400036850081e070b44202517403507807111540200c0c01d0140d424407000b080c800034013900354402e42c140081016007000c405040fa203080c160100c4c140000c03009000100100b0340100d20080d5000315220743c8100d0000c1c0502c2c03400001e01e4034089507140c500210782040c042d0b810261031951481000314007250000b454500619868802445c18924500105c080b103025400000c46018880404e82540c07500c409010140383c3e610b0b00000701291441c40444029103c50b034141d4007a500842003000c13a0794812000c038140d400c2800c040001c12496038408220540c40d00005121440c4900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 21369277 1250 21368027 21368029
    0x20115091d030c060132190803030a0606110d020a021302070b09010507080109060305031c0b060d0b0f04020708040905040c0e070c05160501050d0e0c0a03030c170f04050609 76
    0xc1d4040e62140348425280c1d507840840c8101d4070b603c02400342204244003240510881e00001c0040d010043d6000010864042000100041c145020850b1002d41d0189000400d201009200039801040d4000c40001e00515068010f00680e1001c668912260001c038104016103401140342400b41d5411907903484035005c030020180080c0103d5401038580039403001009042c001c15441980204e046442d1456641c1c0e030780801600b99506c9000c002c003507410911102420580c0c00702c54019840c00d404002c0f4050792000e000c682a50410368403000c219071180b0480320582010440c812030810f054a00b5840e050641c1c564124511036071064024860750b03840007a0500c41154086000740c000c100c640e0f03504d804c02400040818a2280e410744150003001a4049001c0042c40d01c0d5040740c6068403080d090a8a0000b142c00521b80c040152030749000c1d0fa000e1903656035800b030405014611903110f940c1412268101000c0a040d28088425581010001c0500614103c0d054804568044404558a0070910 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 21370527 1250 21369277 21369311
    0x3090906060d06080a03030b0a060c030509032a1905060a0c0c03020613050301050604050114060a03090b090312070c0309050d020f0a150e061602040504020d0b1609050102011509 78
    0xb06403a04440c544035001c55044008180e41d0a528000c2c0c1e003c0c0403d40b0710404101610a41d0b03c10304004c00c11a40c0e10f8030000e03000d1005890690030060554003410500c1d88041c2541242c2c40001ca8004c058640c41d44c07592400c60090008540f260b1080e403a582d0400000c26a64810303403140c00c040c001e004002d84100011561080d000c2c5a0280480f9103c081300800c4805038003c50103040d01c00d501b48070010f040c0b41402d02c1000d0482d29101501d00c00e04120341c2c18042c19501c001d2400c0c003010380f2142180b01240003c001240111111401103560302860140a0303000007014003100d00b04101e601088010a03400541241952002c603140c00210000b03200148903000d043e228960041c2d07580000041c40e00329811414203148054944100d099224401c000c403e100e03022008842d06080e0354028050b0501d036211943c060b101030242c0c1803010f41d50f2207107007038a401103c5100c17444c1e484030804820603601c17400360002004280001c3c03001c01e03c048a102c400c01c5090090900740fa644400f5451841080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 21371777 1250 21370527 21370537
    0xf01030b06060f04150e030a03020d120b09150a05090c070b0c09091503060601020c13020a03091403030106090b0703080f1b07050105011401090b12090309040e06070e03030301080309090606 83
    0x266582c5c1d4407105904000034000c076000200c0c880c966010807908020440c1056a9455409803034030029440c0305449500341d41c40c1200e5003a98602000c821600e401c030a4a01a18100c02503159907802c0c9810400790034110781140e8010700c84002842580340b0220141c81415a2000881c460342c0e8035494404072030300482c031071198000c01c844188107120003030003e00d016001091703041d500c240c0c1d500f00c01079903155621007090703800c80e200c4094211845a5039014043c004880e03d40401c1d0044952500700240007441c2c1c03491040e402c004010804c407500b18015800500903103140900784a5240c80280800c1001005486002420b000252204241c11580f01250111404035501e84125040c41c40c021310f8240a4207410101c1030b2680300240d80900390400440b8440610180b0305507070700340e0580d8a041c02400b04180b9100c140030614141c0d8079401810b4500601e1070040c40f152409441c0141488120138985000750020001401101404000c661124200362007024a44d240d0700e01081d414860 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 21373027 1250 21371777 21371797
    0x70203060411042307141801180e0c0d0c090308090d0204061a07060501050d020a05100302071707050d0c020901120201140307050301080f070506040303030504020402070b0103111201050f01030b0606 87
    0xa500490f1050440412038040c024640e03c004251201e41b40ca2101841801c445410120b500c0508800e03e40c401c50500b050420200c041104e416550280540c600744140e43c901c51442300882c85071800300c1244a024089043d87c82e141c130101d49103031540714583c4251481e10380030b42d050035840002e540303032900b01100600141d81000802d1141260180584e0045142103030f46a061034000036051800000c1006450380003055a5540c43c5803004010400c24130404a1017416000e010302c0d8013150340c1599244003903680017031003070391201c4918085007042455002c0703c003808120000741e80540c5510b4155070640303001c040010080d404900040e204100400103002c60800000700308414a58064040d604031003882c1d003103c0312180060412034a804560082e0360304801c00703000402c0403078480c1c0c0160381c11500140c801441d0942c540c40703803103c482d400d0f042611a8031501803c076180c5c0c1031152041c10b10400c4000208141e00f8070403080e07c91f00c201848085c00c48180d01c00418155550b4804403200505 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 21374277 1250 21373027 21373061
    0x50a0309110306010611010b03120a11150a0b04050a021e0c0307080c0c0306010e1b03060103112101060905030a06050601141201060207090501060203190e0303070812090307020306041104 82
    0xb03500e4400038005100030303041c0381c01c550802c40d0f684c02500f40040c080c03408110b82c002b203509020669004680810300500240c48500c01e8201000c1c142c403c0443d214003810340c40e4004110656910140000e440c4007410007002c092041004208903070000281c04132400d10002d8250360b5115000c5441e1440c0500280a0803460340020001040500041e04181c548800d40c01e840680c1e0740e482030a400c000c000c03118101d00620000b141119521520300031a4403003014140010040d08048158129400c00ca40d88030700f00c02d089041c0001e100c882c2d040180100450320304480000e0800d8081382e103403840a0002440700e9103e01c04600103130300661402188502c0700341c1094962007908240b0031001c0084c03103000c000d40550b600110790042103001d82410b891030303600110b1a0a42c506806e41380300381c04c844000100525040c2400b01a5014801040035034001c081154441c4814408492080c070003170645010b07030b4400c02200006840c04143e0aa006400041e5040c040b191100494080c10004038a805610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 21375527 1250 21374277 21374279
    0xc050418020705060c090d11030106031203050414060903090409050307060207081206030604081206010e1002010212010f0303020a0803070c050703030f170105011b0f170403051606050a030911030601 87
    0x34240da02401280e40100c00320b5900352115405041c0300d1258052080c0c001211071103100115031442ca40b106403550190001a0352583c0352650910700810080310341c002500c840500c001c3c07000a00b80c000100c0301c00ea01600d601d06124564507907074813031002038500898445114070240301c0c0901c00d407201e440c0c00200c15940c91409282030a20ba0344002071400c55281d010002c2661400cec0011014032075940a07220700e103000590300750f00c2000358009010504000e51040610703000e44485207036405039000380e00050303180c071590b0715028040d14050300105200305c840c80d400c03c086640010582801c0780c00c065500d030389031124070003203403a507089810281061003624000030405900162003820012259100d022200c0070480004652400307218460018000d1030010f4400e440700c91520040511503107545020a03000c2d034a6000c0030990395421036410343e0125040060000c10302101003c030341c0d12886001c40307604200014000d402000c4020b41050783e0703401d1440400000096082c082c3d0780c01000c1310425 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 21376777 1250 21375527 21375569
    0x10203090c010906031104030b0c0705010e010614060c06010b0c070317030609010902090d120c0209040b04140a0308010605091305160e1203090405060103180b1e010e07030c0504 78
    0xc0c03040c1c02200b0300090316140001105071080c412003038103da081007100d190510316120800d0041010702180841d520401040000840903c916040642400000314156107800c0031003c070038a040702c80c580900000c101114000c1c5012484a06403402004010780792260881070a01c0c0940c1500010800702c0046218181120400c0c0076510a00080360701f403200d80c7c1c070347c50b60805134011041790076007141c100c89051002035a5200b11a03074101c41e5207404454030242d9000102c24010607541070707903051224020702080c04036019111301031208103002440b40b004969001002910144214400c020340424450419618808404882c940100040c4503e0910808113603d030f181380c0c1c6c11840881c1d040d0800803130174100b1000031400d0034403050146062600301c034103200c05003600030f03c01410107a44520f91100c080b10300d80120f80890150459241911702090024500582e104074102820464001048085250903015a01210900e4080b03014500c2c45800d80319405581c10140c1d80030240101e40580c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 21378027 1250 21376777 21376783
    0xc0210030905010f0606050922110d0f0212040b0c07060c0e0102060703060f03020415150906080a0902090103110a08100906060e01050d08130513050f0702010c05040513060801020309 80
    0x5010b00440003040b020b0300c00f20f14842107550500c01e0001207001400080300502e001d000b01d0074800681e103111901d003140003461324100c44410b02682008031020459003e07600103841000701d0195001c104605e040ca04980509030003800500c02801c542c035039170005101480c0d800036a1070260b0b014000780074100024401402c0b003400e007804640144a0781c0e001070301c141d101c1d025010454184c507503c246028215000c0c0402f80030364800000f250000c10b5070004511802d00450004182e0700c3c2d90f10302c01c560415034010140350380904400c40755418034a90601582d5043c0285046950203041502c46580c0b40c0d010407503a1240341d000381d41501400c08000c0c6403000e40d07001070304020700c105010407a030b50b182c0514080300034080c041c0303a802c1015500e245000808001c002c0200802003000f06611070394a0000445128a6869000300b4a403600300384800c41c19003203030700743d00440e0500081c403030170381c2c2030000803d83c1c081c03440b82c89e2048405400e6804485800c1c2c0c0300102034502c510095589140205165503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 21379277 1250 21378027 21378041
    0x6030201030b18070e010e060403050d090b03010b0313020d0c08211908091005040c0303030e03070314030601030f11070b0106090e0105010e010e040203130203070b0a05030402100c021003 82
    0x1000c00c0c205a0841001c0c6007107408681d40d100e82e5000a0030503265001e0840e00c0220640d81941404001d01c043c0c010341c8e89a101510042d8415402801c2c0580c003084000e0100056502000444200344014050300000d202982d43c00b91120340d039188030303020500014006e505c01e10360140c003c1d026044040f440e060086900d4014044807030144208801c444884001c82c4507400c0791101402a2002001185200e241c0c082d40184036101180d0544140340400380c00c448050b1000c880820a1810410170036825006011500744442c002d107003070038030a84000d0b080c0c59000505d402c4a000002c00555140c0c0650300114146412030740401801e84100100b80d2264454001a54180b40520000030524420030051b801c0d03030001d000020950f480c103001550784242d1011524103004141745800b0054450744007840c41020b01d20000140340170303c3c0c0141070612403190130079001e60300b08205103800325421204890b005603040d01c0208181d00030500440d1041c0d130629000b940901d4050600010030b515400c014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 21380527 1250 21379277 21379279
    0x5040c0509011703160c0e010e060406050d0201051903020409090501020301081005040c0608090703080c030702010e1507031b02091303080916051306050306070c05010605030615120c13060302 84
    0x100c0c1e03642c80c0c1103039201c0c20030f0428902120750700400c070050400d0945801c128285c1d00c00d80d2032001968581d031812454500036081280300000060800a007440e00d405040020703c001c3c0c1d4240d03141842500000d00c00d22803a101e00070550158145491100d1090341103c1c0203045c860002c221443d42d51034818080c1d0f00038403440d006441202c6541022901e18404c03a40076a600605d100c05a41c5805d00a07640103000400420303141c00740d12000000310f000c0750010310320b020090000c0c5a403541184000340581d00444082c0340515803c1111a60540200b4111283c164050a102903003454001024141d0080004000c0d002402c000900070321070f08215031075060f41c3c420303100e01c203440e0380c0c810043d551049402d1210b2406040640c0400c25070900b110f10786a5684500383c089591600d1b14046440d06000f81d44180005040c17028110034000b081c80380801a02045001d44091308280c00301401c40c8514181262090180d0b404110200070208000002408040d02c81040c054001c0c01120040c5085d110903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 21381777 1250 21380527 21380539
    0xe071107081006050a052b12031b020706120b060c0d0903020916050d0b1801030b0601030e0c06070303020a051c02030105090603010e06070813020a0801090c12030c02011209020405040c05 82
    0x40344d00d2600b4003511040e01c00207085800400c01c0502c028200344050403d0940850819032054081543e0004111005003a41c41c0410074030b205a4400030725000c1c0282440440d00030300c3d41440695440307002c0c101c40c1d090042c408241718a607180043c0282c4240420301b84144030b00c5001f054102e070840c82c0e4000b2603008503078151a6030f84011305086646001e20890002a0701001034090354140b992050340b142e14051300c000782814000e8203030501d880c420380056450706640010001c1c01c0d0790500801d40c200d1103549c0a8070905c0c000c80f011551901440c44018207041d00800c0130303003c19101d40c0550781c90280320250100002c03844140340c0000e41c000c0c02280c0c0140c4c001d10000702d10342414003035554940d0f850001030120b960350b29012250503601500005001803140d030a0744c05a50348000060113421140000180e5054500d0b160081d107509030701000c0c545491144080220b5008408420388a40a08084180d0b00e0040c41c860b0040c80c1451000350b0091612003444140694030028209440040d610 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 21383027 1250 21381777 21381779
    0x106020c1806010c030504030f060501080c0307080a02060309030f0a03200405090403080a061203020609070806060a09020a02030d0c031e0b0f04090203010b060a080708060117010e071107081006 85
    0x180050803215405012079011400045026544228214000540285000d0782481d8480d42c6e480103a581692044d161203440c2d00040c0450703c014016042c440500300c0c0100020340c0b030300304103030f884003a0711001030320070080840045d520302d0342407085945240509101a8ec1c0703003010b41c0003500a02c90807441401040f074590420600740d1480e41200c0c29644010302d100c2656803241e42c1160b10701c0000340a4562130341c548000180340c03800000200c01d01e501ca900505510b00d4203d04003450890158001082940418244241600e0318810b5005580c4108070160351004e80c028245e04e50b10a0303503101c25016181c0032134403d032640e269003d04582c444050100d45004124034004058443da03440c410b601c05500d006080c103e02e440d41c450340444e80701a0001c03403540c40c00400600700c1c0d004000f8180200301340d0310400840d0342d400b400099101809080c160100c06044400c01c45400b41401070868440500c1c011030354642c01001d6034080c1c0ca8003501181c000b9900c03102810384441e1500c230014201d508200b8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 21384277 1250 21383027 21383029
    0x3110601050d030806190905270102032e082407020c031c0c020d060618091205030423030c10050402030a02040903050d0204090203060109050409020d0311030d02030a050106020c 78
    0x1c0b000d1480340c00d90b036240c034552110b400704414215105410300d15403241c600c00040c00e01701405194410021a40344c8488680441028000100c1003c5101000d9104104004114003a04150300e00c2451580409410903c14006c2d120b40072070342d400044961003410050510400c0c00301c8031610940140c101c070003e03501c07000000d0b40d603289201c0e034040d41600940705a1a0340440400804103901052509102182460b004150a4201810181c0310581c442a05124a404000300b05078540e43c00f090403c41641c01d6101e050b07862101ca09001c0030801c00001150a200301c1c0050989000d40c00804c40d42c15051a007900d6a580d80004945140c90091503403076100007201b842a01c3c8603039005406425070070529401c0100510710303031008030184101402184458909403001c1c20140c03455200060307603420580000340032b5141aa1260f489a0306209400c4010b0f04d4902e078100740c46030706080818411052040d034900b9400f90250000790280701004000300c45946400c418126950354095683c0003030858 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 21385527 1250 21384277 21384289
    0x1008030c030315121506030a0803010902070309050603070c0f080d020d09020102070807030804050621040602120c07030512060604050402070302070306061403030a0e03280209010f0f0e04050c0901030311060105 92
    0x13200c003121600003070429200102d01c1e0503907517407000c8010142ca407003007a60340d140340c03240e0000c0c0c111144441c0e02003809410107811035120809000c1c111561030440c5071420700181300b1159850020500c50584110400700400c4a05440d851280c0410564803007070f000d02c1000041550f0300d0b060f4011b00c66400009200813012136417800f0f482d04803420170b18040c00c140c01e02000703901c0160061440002000317004984001c5c91011800765100b5100541d460030b2905244504020280a144c03035811b08025002c000b0f50800300b00c54000c10500004003032550390340000b0305d082c0565032200b0b81050002451004165003c00d001c02624840c0304c0400c034003900c0c0c41c900c04850a6800c6000c0e0103500404c820b4170300501032501c4044641e0010100c0d41418040e40c40c540d62101d44c07501c114801c4060f082c0381030452900441c2c0c00c0c050400c1c903c40161040c42c11082240344075480c07045a0501440c0004941400380620040710140b03405006d29900f0359403031070700070014520584000242c1c00b96400205040c6094 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 21386777 1250 21385527 21385549
    0x212010b0309070611070509010f080d050a050d0e0106050301150f14030309120106080307030306081b0109062318100305071706060c0a030809010c0c0804030b1008030c030315 77
    0x1034001c111003030400c542500d107480411101d01711031040300000901661224003d90190054041942402c1d00c4d01d12300a00d012540030940082c40f0b000e00c14003c5199104007540c50b8082c00d0b20002c0f49103000c0b01d8131640107044c0b0350081074055080422234050700ca58036003010b04448e144a0792a00d41070ba5240518603032101e003480507515030401c110341a40352410f0107001c90522000301c00040c689945200785442c543c080322048003c40d0721100c040000b590180268454407001c0e452240821550b400024205800c900403803090180d50071011031910b19205400c00c2a00d2200003180c0d50701d5001d03440d407090b051a12600d900c1010034910341140ea5200e030194600428454885580704d80100000548024009082c56006903080c4001c143d403a90030010071070224003d84601c2040e00704140b5850a4850745156003090040b2502504000f90078182124112908800600010307198521042c8100348264807070500361002017004a8441c0c0b0100055000320003964043d848409144280301c42c00c108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 21388027 1250 21386777 21386791
    0x402130b0919030f0212070e01121505040506010314030c060a0212090706080c0a17070c050601050109050306010e070302040503030406050a030c0c050d030515040204030308011d0f0c0c01021308010212010b03 91
    0x1a1151850040c2001035950341d191540c01c01f5521f003541c803030824441544090788803043d4050b01c070f08120244a84500c4554440c4d41005061190f41f40070345a45945480611004201c0c1c00300500b0b200c0d420100340b06a030751a001c06002d5544908000049002035000f264519511041c0c1c0c0020a5483d00e000462a00b01c844c107484044460b030790341070b140c5241e80003820084140503800707809240d60b40701d03802c1130b500c00e071640d4664180306a0700b400d140c2d1070840d0503040726050003120b540500299074001307a4241181c8818040070910b64451108401a020740e46c00703035405200c089400310305241c0000141611010300e55080100b0240010106c403154441107015180340c108000ca40744841c4070341c20896012041c42c81c17556241801030b004c82c080764407a900c15130000b0300c010018418050200c00c19070b540c4a12141d2002c0d64100b500c4c100e0b00850015019000101000816840c01c1c07600f134050780e001c80201e00748200002d80c2c070407056020f984120000c00801c03561000200d03400c1c0003102940d0207504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 21389277 1250 21388027 21388043
    0xe01021c02091f080a0b060a0c02130e030304080403170304080f0304020406050604090e010609020309060105100c0c090606180b030109021614030712030b0f09060402130b091903 78
    0x550004100258407141c05990010000d40d0380940c4a03600080340c0090140591360444e40740340031000041210002c540852252078200320650b8102d5002d101158a241c0498520034200640c585100061000712292100b41c00048104010300c403050002d04100d0b0300802401408a0810203240e889210454004021301c000740683d15000300101c2c051507202e40301800000d0718986510018100c0d4200e40e00c01e6041c42d454011402e0003140c28010040200740004056003103041c801d42443e1107440500405008044007150b801070648900d08841c40d05412055244425403a281c24801030f01e018000d120118106071026413a0084500d681d1044035550911141545d0900f00b803807000c2d6000702c40c060918180e030303000103000c19000300e02c803007500300305400455540d003241c0360000000305503030191000d240c6030041648190b169810150341c0d001040b10012055998100050000d000b10202011080700d85040840c3c1001c629004041e2040d040f1102c9861403160004a00100080e000c0204002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 21390527 1250 21389277 21389317
    0x2060c070302010b03010608031305011418010210022a0f100506040e010f02040e0f0405030403060209060706020a090501020f0708070b030a0605120c04140601020a020d0804050d08070203010e0102 86
    0x86044015000d0350348648004140030590a000909562154002e0407070b0380c0002a075030007888049100540104400c0c241701c22a5007507607084110701e0040c2c610501e0841291003010b0ba641e80b0900808502c441d461700215224000011b00103194003c0c40c117100b01d5545c4100c0480c8908a00041c0c1138080030b0444000e1403000f6000c110345014090280450b40c0042d21007400680014082c010f04c030031219480c0b00161160718081000340319001c0035018182091002d01408049103001c401ca50030b2360741084015a0703c410b0074002c1303080c42c425807201078505440442d014250f681d0000e080011181d099003124040400180c1c00c0b074456906100344c1c0300560182c00e0070002d5443c504095a400641f014000600713a54038004607148080211403240c5a402601003402c941c0b4091145c01c540040d00001c1c0982443c080380080d54509503400042d1144a0391700b002c2d01003040b84000c4601a003400f601904856005281039105074018000407403095003803182c903060001c4144250b80550076400c100380300320 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 21391777 1250 21390527 21390541
    0x402090904030f030e0a1a010e010303020a080c0a15050a0b09060604060309080405030111030117010902011b0213110c060c07032114070c1202010c141b010606080601020607020106060206 82
    0x2d4035040f1002041c99204c0074410111181849411405400380c0c140c0301d410f9100d50412040d41c01c1c16002141424502c1c4c0040c0041f0f540090b8080c140c95000c00703090343d200f0400700f801345001c08000009000034000b01d0403031008059a003140d0301801c0c038120140003c10300c0d20100641d00341c2c210703101604104148000c01c0030502c00c0e080078040c24090748000f0b02e010b0b114004207083d0b074819454440d03000300020040103015603101900806100070002004822a01d5000030200001c040c80e001c056070000703401400703640d07851002c1c030f0b103407146d10400300403004a9401001e180d4100c80030f620031a004850020b03204016250032100541d0340b5644100c0c00080c00300143ca401317510038010504543d6500a080303501001002c24902814080d1600e01c242c0800745013104000022800e0b0070216410002c641d50900e8110301c20f44954121903070440d44840390081c20154480e4400a840500d60900c40c002481d40d82101200b40510b00aa080e252a81c1e9100c0003a400e9840303cac820040180c0c800c0b4001901 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 21393027 1250 21391777 21391787
    0x4030806040c0e090c09120604050a20030d02010605041109090a0905030c03030a0506090c0711040b03010b0301060308070204050f07080408130504050403090e07030e03030606130509010f090b040209090403 90
    0x824409400c000c0c40003801e0f0408190894800c50700300340280400a0345007104e151003400f03070750312005902c0105100e00d003641e512622200303600030041400302c07a00680f0b40c100f051450140c40b44100034080311658a013a8400074081e1555105044c000da1034041010521601c600c01c032400c4000203007490300300c0e03264030803030744004c0c4510390003a510b500051100c404102c1003880214020f01503031801080301d04001d03040000303000c0090003004100307208100002c00607803000307142e42c03202604480c0000ea03484140c0209014184c180ca00d07581c954130f8103070040108603101d409490341500070b56042204c1d545420b980000c0302000c0d611100402d402500060004074140b00600c00b2220390034020500c40d95030720101d015a1410384045021a60305803040c0403a102c2e4030b0189511079141d280c24000b40e00c01c600340e16120302c4081c101c24018100014039030a0205010b4080c0e00a210103408403d8660b5074940b1180c03040c203d8012000074600b050a04103c520f0a8020713244a03810003842110349450301e0b40c003038074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 21394277 1250 21393027 21393041
    0x901050f0a050f0301080606040b040c17040302250e01050a06091a13120302010b0609010c0f0f140607030f140703020c1c051b07060207030f170301030f0510050403080604 75
    0x308000381080810758441c0c914001e1402411100c006104238202801000705a91a1411130390185140c00d9600d010341da070103102d10112440c40c0616070311030340340c50904a0405410074415980e80c0c82c0c4a040c0804401c201d04c000c4116000c4240d03554850340c0398010070040b0207481c403807000010a804011b01501552003606854000c007500042c0c0760640f03243d03080807003018540c02100e2241c00e41543c40185034083c0259410700800b110460302e05062440081e02c04807803440080c0400800f01c101c0720400c1882031031140c400e41c025550001e22451112910356482e411969900007905200012010700c00c40e0050b0280800f8038106111180d4808038120000d4010b445420072612520110790030020400303440118054443c0d65040d41d916050300d000381802c999400d20f0186034000e0300d041003102e5000c02c0e55825203922046240340040e003070820100c101c41140c00d046c11184001300010400c10441201450907105a0540300746a012a04035411104100e03000340c00325020030001000b070b150a51000c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 21395527 1250 21394277 21394297
    0x203120c07120807020c0d051b0409060f05010f0e04050303070305070e0d080d240303080903041e051302030907031203060315090203010e06151e030d18050102030901050f 75
    0x742400c1c000d840c0c5002d0181c40c00444004680703c40e05000095605204200c4810016600051a2075031a80c2e070641e604042d81c80c2c40303004501d0308411991781e030f01d40e001a10a0b507041002405010a80c0094000512081c850014019020980003400300410b410b06441150040061411507031901c00a6000d42401095170041105104e6040c441e0f83c1d8240101c40580d020340c41d400e44036001c40b0001003c54490041c10007004011403065060b0002241810040c1c0303615182565a94462151591650003a42c202d0680c0c04441c0d031483e2006800401c1001c2100c50490b0700e419080c50b0010410200e220560301841e42e50090202800400e000a0140315840150301d130001d4519942d8550f445050310014520b11099242d440300c90652074240a070130508a6110302400003410001c2100e03442051001035580075030041e0b4aa51070758074409602c1c805440340503003076500ca0603a402d002090300c0074100000050300910003022526510002c2501c14600068642d00d00e4800c501c56503d0040c0c00441c400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 21396777 1250 21395527 21395551
    0x206090d0c020a050d05010b040509030903030d0207020109120b0403020610231f0e0a0602070f031515080a0c080601050a060c08090d050f01050109050f040605070c17070215070201020312 82
    0x80c4d580740d0081042201e0b0062000054920903c030030001914400383c2405450352050140d81c26607a004011506400c504080050b664030451006030384150a5501c58002c4000c40711062003400b1110101c18451403103503081c2c601603902c0703540c903110065050203040606404d200303902e0010203800074041c0904100030150a80c2e200120641d5003606040c02c04500001c0031000c2c0a4081d040010492014001b00d0020b48001800e00302e903a4000112440003402c1d4191019030b4501b80350055015401c001c0ca02055080560303124450566210f0502c001240c074000c1e03000d8000780c101800700340103050b6207005011108a17441c1c09800c49a04450100945000b50304102c009525075628600203012840f40000d021070b8418840304e80d0854170160f124000380c1d42000704002c015004500c515621951011000689844105049808188000008100d43c44107884400100c000d400a4178440b882140c1c20b1a01d440e090880b810309005401000b07000d0b074003d00061191164864019070310032440245 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 21398027 1250 21396777 21396779
    0x50c030a090f080a180906060e060a0504030501020a08011d0601020c12010b03010e0715030506010e01030c02010e01060f080f010207020d121710170c0d1101140d0c0801060206090d0c020a 82
    0x140341e120798068601c82000c54001d40a01440d0003501d41780000400032124100041858840007812401c440203040b40316a0f00040c040c55418010401d071070165800a0086498990b01032000d0a080428010707100715402259550407891080ca20b11485800180d01130600304072101c050090000142d000004e00f5504c485101000361403d20032054012440c20003030110a02e422500c10404100b803007100205806c0c10200300144e41c01074062100e1382020720780050f16101d01102240180900b51141085509101001802c5002d0b9002030041c1c604260580e035404444100d22800c0f80705a02c00290009800140380c000302d54840040741400d500c0381001806411101e01c0101070b600e0889544401042c01c90341030141584900da0360340007503140c400130619008540006010601c411200403c410120791070032109920441d41d1031701d20711080c600710303448910000b40c046c040c003030343c2d001ca0380012141000041c140d8400500c0c103004182c0784001d4844044004000c441c000302d401c07802d90b002803179224 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 21399277 1250 21398027 21398033
    0x80a181106041e0302040e060708070509040219020105040201030615080c090d0c060203070b01050109030305120702120c01090209060402120103080f0708070510050c030714030a0b03031204060f050c030a090f 91
    0x46001455241403c0c0b000c0250451042100719201c0e90314100b1203500503020068200d030030280c06034008100b4108652036101700c0c0d0000f8040d00c0340f41d040c0c4c0f405070001103020b02120340541200e400b0714805d0703d00303101954840500700141c3c01d080c0380040003e00e00e040842e0040c2a17100c010008200c02030002000090702c0d0301c2e629001d00159001c000142c0c030015194081c440c8040e00c0e02d000d031a00b440c15018881c91070300d0060450051180c2c00d0807802c0a5004200031074020005055100d01b2503030101e49408000801320b00030441401b00b07a000d500d65900191461400d4401c627032b511040c2500c1c0118036421912a05400d13004046c045411401c200108000304521401a0616034422401408801380c8881e80c0c5081d5440a801ca80b91040240144803485070443e118001c00c42d12a0201502d0383d6620b030310000500004003074a0b8040c0000190452144110815648240d0160000707018085464004400321001107506040d610420300200754a00d030240c0040487d0b500841007850300d0001a1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 21400527 1250 21399277 21399299
    0x72303041e0807030e03010b060a050307030921031a0108130302010f0603060b030d030e0c01050705070b031f080a03020a06050402011205010e01052b020405070c050703080a080a18110604 82
    0x62002d450140011503114201076004180504203042503009000380d404201c003107840e40c0680303940c420900038040000741741030f0700c2944150107040e003081c556a045955040b150051000310744410002906001c0c50a84804034100f02000000d030694503800141d03944081c01d00c071403c0c0000c0c1181155200e9104e8105c640c1e00740140b8010b54007920f130000c2c3d1000c2d8617081602c0c25222560410901d800c000702c039403081c4804582800030080c02e09000d80e40d20140d01c1e140d81090a55040040ca009000c814055010400d10001d03c1c00301503481c41c120181d840b11355580d598403a6000042c0140c1c0003c800c2d60015029800003a08984103042004402242c08100e50650b9000d0b004407181851841c010007c0c0e1610f04600140004150780d401c0e9028221401d5500428a51f40041c2c002c0352290042800c681c801c0d4901540782d41c00c003007950801500e074035244049a22940230130300042c950602142d80c543d101d00c161030318100c241403940b1002100d61b590b000d00c0c01d40e07104080d500000601001444030840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 21401777 1250 21400527 21400583
    0x2030a0614160305040f08030c0c1209041d060703020a0504050d1202010b040209060318210702040b0901080319090f060801030507060e09040b04060f020c1507230304 73
    0x1103110401d5803611000001c10408030000340c004140c100002d100228901560f40e00d10315400500e2180c1c1ca9131040a040b070244078411280031540300360f1188002901c5004041c1507a088221024004800c034119000710040e1455654103890304000c020809283c065070040c000c1ca03001d800c2450038150388000240c2c1074040f0340400c0c1c54504191a01312200c030b6082c0300300200a8022642141441130100c0442d06a0000400104d000079064800c511041000c02c002400f1005640300311840a030000d11414040e085003204900032402d01e1040c0c0c0c2903240c04070134241622200c40045017810070343d150315509a24844181d0041c041680000310f001c10001c03c480001d404c3c00e494202065244d4503186160000507407044d0704010111030b24200d540d072034155483e00a50440f1900e0f010b40c0315424140c0080c1345035040d518440d03100040c0d40402c1003000c00c6070440445c1c140f4451181d541c034003c06582070140041594040002812140910b400c6c000245030418001c940f5045100e80c64000b10070080d0403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 21402883 1106 21401777 21401801
    0xa0e0d080c0703081b0c0d1e0816031e02030909071809090515040c05040903020703020301020406020303090706090501020606010c02010c02030a030f02010c0c0b0601050702030a06 79
    0x40400740e40058926405a40070070707a807450813841c0d40d0f2154243e00031707100d281820040313508070101d01c22031003260160181c40c40203d195140c4c4010716013488087da411541c485080c2c0400e28440c0a40146072028140e0029992203040240290400d00c050251801110407500f00c0c05a011069510441c0103480307040c1d00e03031039045003620040345010b0903180050240c000003608100383d8001540990048040d6070f40c3c04011030065602c040102c03006000a6806241042241407070f6020310a110300902c161040e054076a40002c1c02d9070300c82c0d40b00b140147d10202c18405091401d0219100800702d605142c3c4a00707140c80f0010f5210300c0300a18450502034152200c4003513901500b046407091342e0050a403032824032140f42c00380100302800b5801c001507280c055210381c158000c643e40c1c025150410360911907541c420004540c070b540211001c903058003802d8010000185da90003841c290f065 = true := by decide +kernel

theorem cover : BRFrame.Cov 21223027 21402883 := by
  have h0 := BRFrame.cov_init 21223027
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21223027 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 21223027 ≤ n) (h2 : n < 21402883) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
