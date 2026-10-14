-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1012
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:49:42.172213+00:00
-- url     : https://prove2.me/submissions/ea0e2997-2f8c-4be5-ac2e-b15ae093faeb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 181834532 ≤ n < 182014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 181835782 1250 181834532 181834603
    0x1050304051c021e0a02041503170313080a0305090609280809031c020105011a031b0d090c0512070b03010b18060406030c0306050118032a1502 63
    0x4602c840b412800842840c0180d043c03c0204544a0114414900d002483c100000c1e030101c030280296010450584081d00e00c00c0e03081d55500010708a840c0805003070300c003006401b0046a00500701340b00c0d07407142045551400368075030110a03e03100098580e805e201100c201884600d4020381d412006008a6000c0071441199082c60065543d003c00810303100c07414032035207070708407910000010705507500107003000300302c04070f0014540007100150b20380400803607000050b4880103182c103000c400c2c1c182141d40d08a03400c81c42c20b025802541001c5410b102030300b4043c48034007501460510030f00840d905242400c09100440e280d000008075a40e2040d0010424040e988003200e040d02d20340c40c0f030b641e6a004100c845a031a52140f9003000d0700608000f41c0081d640340d060380000707500c545a550520980d5038075001199180c0e1450748071211210410810400076010309101844044190b00f200400e6016030322442e101d00c01079002803140400d030803000250340d42c14070400e09000c1084002114940d0001c803000940c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 181837032 1250 181835782 181835803
    0xf090601080a1e0c030f0606061706060703092c09010501060c03081302030a12170c040b0703030b040e0d021c020304140d200102120f070803100b0313020f0105030405 73
    0x40c0382510500b65803c00e0026038003035180c0080040c0303600c0f50f9030318292803a4035407200162151b0740b030864003082c030324400d240c03040d03510a8000c54800c1548429040203959400311208409010003040c000954601c0032030300880e00014030038080c0c9903403007014032001c05100050000741c15074584001405115001004444010340520340030700590303134a4041d02d51200c003081d4041c2d41481841c0e0f0303200c100b0000700404615084035580b42c418903900c140310080c05480130b80d20499617130014002030001d52209409082c1843c000d00e00451480e140c0c0c004141250342040c1080c00542000c9800c030301154042020307008800020701c081565580c499802512400790740a4039601840d034500600c4142d076448420842244c20035034281c0d0351812485c041001e0a00803911501601812280c0c1c400c880705502560707160f44130180500e142251941d01c1c41844e900c002d0420010516100700820704900c800f000c0c40c8500c41500f07050203002c0c158010400024020f00f2500c3c10024200308200001d0004146030746c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 181838282 1250 181837032 181837043
    0x130503070b0307140705060c09101d2b08040f0f0303080606070809060a0e0a14031b011404060302090a140d060903110a06060302100206090601061103040504050f0f090601080a 77
    0x1800d041c4c64040a0a10414074060024420f14042c411816003138001413440c210100c812151108c465a01920042200401c001c20612034000301040d42c1884130500e034100b01c000c4030450140e42c214298508280310708609581a4401050a02881505c8012038001d0000b901c80c00382036503c2c542e0700500c0c00300003c0415004030404030b203c104000c40c500645419110080000d03441304007924000b055881c2123803d19102e007407880e1000402a02d1104950341c95036015021f031803c101943c0d2449010009000c00e5810860340070030703040031706c00c0810240c40a40034507170f000744c1c0d6008584100483c80710315402041c22000f1418440c042c960780c40302c03c500542ea105c0c1000ca8005680c2c1425104003d1a840c0c2414601030002800c00b000030703da1141041d01d108642100681c48500d0040382d4031041103444c0c00607039001c80c0040c0000c030700808800c03945400000c101ca2409481d0350200e000d030381040d2905103a010441c5c00713001b40c8020218034140d002c401540102010341c034081d142550781c0c0d4120304c041c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 181839532 1250 181838282 181838297
    0x5010621120504030213020c0106050f1003090218010303050304060b0906100c03170901020d0501080d08040311030d021c050603011a0118090c020c09180a110d0c0902130503070b0307 80
    0x460103941503d0045400501c1d50703103484100c0c071184000e5032043d00406c043c1d504c3e203040801d4514000a81c540e08150103811240715190090b8149c1c02804a03120903680140405101805070501d845004d010318800e64900e612030600e031905000396031480c10424415206a010442d46449900d030082c6c00b01c100d481e100352440b145080030754803908014002c0006428007010420b407120150010b080760703400604204500e030399920a840d203030511101000c1c009010000800c0106c0d201e0082c100303058103003800780e915000f034090b603110407a80506508240010548003001c0702c1d40440c0b003070300c0e4040c42c1500244020301c641020408070301003151459051200483d16003040e091031130f07003c00203000d00e40e00c100003800c81d4a401a64a91001c110188521200e40014580f440301e4021014420120401418203001756550f14001c0ba03030078202140c1040d41d040388074000c0361031074400c400103001d2a00300580d14210000c600c00c07030700890b400060195000c030a040040e056030801710b03684181681307000f10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 181840782 1250 181839532 181839563
    0x150525050c010501080304170303010b0f0a1106040c030605071e0f120608100c09180c0e030312040c0605270d0206030702010b01120b130c03180f05010621 68
    0x100c00e070165860034030309903181000100c0c40020001c01407080d5071322911070610040b1000f105039600e00c400d001b4510200c4c0103008070602000204050913800d0101d0400c0d00905d448048076a1405d002240c0c15600304980075407c005000c6184600c43d0003442c0d0707240103140e039540844219a03c403401c16460701080300d44042d207200140700e954602410007a5841c00d112031a07131140040e6842501d146190045442c0c544200340d482e004108210071035811203c04600d448010207039100510555100d90700340210503030005556500cd0000382503442800c50190000c3c2002d0a0420450b400c0da0080030602c00108804e207601000480c80c8038418a004050703500141c54000451208200498000d4200c41d001c000d0240e0707180c0640100b01c2440003a030310310b0740b15440d00700c1007001e0325845511a90400881000c950791540785402003590f000050801049088000c00c0e221215000c494007034401104060010007007000038003034040204007040b0325021030f07103002c0500b50f980d0b1500180207040b80e00045000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 181842032 1250 181840782 181840787
    0x14090d021504061707030606020a0b06061303080c2e1e05040818040b0a0e040606030b01151404050a1203020106090501090209010f020109030210110d02070609150525 73
    0x1508850101e44103440701d58031100581000008514400d01021040015810301d01c06d114120880c0c206038000e100f00b000c242c407035100342c240141103d03412080401c01018244031424015000310300c1514000d540c1c0c03c40e00702e124100340c22811000410407034212007110443e40032800500c8071000502c001502087c01045918800b20700b90700d8035519003002c0c2040140600003000c0c0c0055111b0400480000d903041003000100c80c13410103182c1d8048890340741445640c1910494540c0b061041500140b00d607126201d482000d04260300ca8182e2032108003140c1207141d404008225a805024046424281040e000407003554a1b8003592050021105021042c10b100b50080300080030003031020452540c688a800c0c3c082c0d40f2007152540803070f503041c5010b5450f51051007201301d0f81c0e81650203485407005513071207040545500001040e06070803d11010a00c54024030041810070312440002070411000d240291214400c1c1409400702441e08041182e1843c003441c03000340405184040e00e41180242d0400d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 181843282 1250 181842032 181842049
    0x90f04050f1914070c0b0106080907090b03100f0c020c040b06090609130e061806090606010302180301050906010303110d05030a02030406061211090c0a1b0c03051504020f0114090d02 80
    0xf100202d006001d1240040c2c0048420085e58041c68101020340e882e8030301501c461200b5240c84c0c00303d0740190020001c11502d075100841040e001021303184001d451141034015992280d20800329140e55000903402250100907403000102c3c1aa01404015144000140180590b9603400d024450001e1145216a01c140701442d9203409004200421950b40308019a00c00d4100c440355070310b507000c0d028003500c0030b4000f030424400c04604008204540d10500110040c0d080008045120340030b04070002e0640d44c0a000d454807504143c40100071a40c91400c0c0101500c0d50041f8182d400e400a8003018a83e9a0140880f60b11001c6840050380c1c03a00c0c0e52401d13000400c0558000d2b00c801e4180b000307070700810590261900e079411040360b24500035115940354a03c10300ca80c6c1d40c1c900200b0080d4843d8071004030b00324040c0803804e00070389c000340c2c2041d52500c8160604028a481c42d00c5444403030204000c604c1c0500ca4019204070a203000f014000410000b01424800d6603919449440c1d80c1011038115a1030214 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 181844532 1250 181843282 181843301
    0x1090c090e150a0956030f1011070203060c1e030f0402040b010912030c0609140a2603040201031805030a020c0a0509100b0f0d090305090f04050f19 65
    0x40d0340d40c250b0b62180c0707101c0188007200440d00f010184c050240320402400ca1a00c42003818003a50214100c42880008124240708150856101152201c2c017041c1c1d40601100a25201c400060648103d14070f4100f81101c210001e1864003010510054004d030b2070008101e507124104a0b505030391150b100c10250082580c0c1d2000c0c0a0717a0300d00108215242401102ca640268400c1d1405c1c00056042001510401c05c9030180745006100c0800d0180424815075071120010b00400c8001148171903521070801c1d80d14070100da10000c2e400148040c1c00c005802a0203900314182c03400c40c1c9043e0402042d00b1102d40300140c0060304054a403000d4014041c650a200190b8560001c1165a560303d108400794844290410f00b0344200c9003500300054a0500252107407203000c0320880010345a061140c40c00c1503411001083c0c041040030701c00f42c6002141407252400d20b602036101e880d11007050a04118484140700c000c1c90042d8100018401d4102c5911000c607003041d0f564405c085030110100c042c8004000548 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 181845782 1250 181844532 181844539
    0x301170f0d0504050102010c110607030917040806010302091612051f031b140a0b07231515030a060e010b040203010b13060801061e0306030f05060f01090c090e15 71
    0x10742a100307401000070f008a510a800900596a1000c002e6446041c0701c203040303440c0e801000000728403e119601a103c0c10380324141d81c12400070344180c0245150002e4211020a602c10700040c02035240c181c600651100c2010308203a0f00c201c0078200200141506d46500d48010385a0b4041000c52283c00001b04040c1010718080014030b41d80d0402c00781d01c2400c80e4908484d1003412a004c0f5002d0341000c0d281042d075801411040320180b500000e81c45c1c580c4041416a51440f404086100d020b4141c0348198030342d440d03440201085824070b100798901082c05400c2d001605011850498942c070003150307038808190456000581120f01c01c98490140800089031980148000f00114140303a0f010007500b101008040e1805c5c184d078480009503400c3c0828000d035004184c6011149003501e03140004480b0360481440d01050107543c955641c12008240c1904807855045030302000310005288000c4c070300603c0c12000501c510489020040d208443c14042c00d80401200702c00203904014248014500d014040d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 181847032 1250 181845782 181845793
    0xc0504150504050105030d02030301030f0309080706030f0b010302030f0f07090801110304120e0105040b09041103011428091d120d0f0603080313020d050d0306050a0e0403050301170f 80
    0x24806540218064041c6a02c9286820008121401c00040c02e07840e03002c2a40040d032669003142c44a440c24440248120b08008000002140c0c0c86000e01000f40180304a80b0301255085005510b0380039985c0c410070460426105000304000d0700259164950040d12600b030941c2d0544903036100700d940e022207400c001210341c204940e81d40021500c0000f075100d1801007445104110360860120741d0349a24540450010f0b070144014402081c6980040180e010000e00009480800781110849908240d00004510b044000306484a0a000002091041520015403041c400144950b12074031014001d141c007030350b0354404800c0c0c5000c903101c0041303406500c002240c2c2442640030030b01d1903c0d031003012003400913400c0c284189038525442c0034076030542c0c0d40004c0342e504555828080b580c20182280d000c5c1d9101600b50f10751b201040c014840307221000c0f0710359070200c1c10310304200900c0f80504e9603074005e0b00c1002c2102c00b0071000c00d070b2040645e4103480c4141c1c0c00d21100743c0d0a03c0c031f051404c0e0b4440c000c1d2301940200b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 181848282 1250 181847032 181847051
    0xd080306040e1c1106070212030c0706140106030b03010c050a120b1203030709060306120212030d050408090415030206030a0c210515031b0114160c0f1208070b040c0504 74
    0x803c10091803c8000d5907031090084d103072030300e00d9840e90381c2903d02030007582c001d0038104d4003521910003035944503964034000e6003003040c0b07619240c0681d0051800d004200d0300a2005101d0303a94507008100051800390003e1250b1120040014128413070300401c54100a8404040c202c4444180c01003011401d000305048030341e00e035a5035455269482070b030300800030409076103000480324007034003e003c12119405060703210920540c0a000744000880c66201182c001084800d90020b502d10540e4003d5000b8070800d500d60b24260107000031541d04201c1203000f03080d420720800050740c502c02100d40c40381640c000070074000c0440d00140c0b03c1c030078600d12065200e8030030000320030003400c5684114401c000c4613420a0f1205041e5090580365040c114140c11301e090b0161540d01700c1e5014030195000008820241880c014103075559201c2c46001420448030011594400c03c00b020300306224001605a0003055065810150303150382880c8641c1d4401003400851400082c20300081c284000020b0a024100380001f114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 181849532 1250 181848282 181848313
    0xb0111030408010f1404050c06030403110d0c05100207170c010908161506180e0313031a0a05071b0c050603070206040b0c09060f090a0503030a020607020118020d080306040e 76
    0x7404030740205403485c0450307224414070040b0019000d140c01c00d000c1c0c541c1c16100e00c1840b4251344020030507428402038804680c0404010003d0340c00703460b9187c0c1c40c5015503a40d4a40b5508140c855042608443c0c0144040008540300700b2526004400018241c0e0b0388003003c19680b03000d4403050300060500080400c1494514038a040f950005510900e0b86d200541d030018000802c0b82c0e41400f0340c50050a690f21140c11820065100b490390300504003c07a8244034406004010b22041c5410440d4000700641825100c07076440a4811342140c1382200901081c980f80d8801000101c9582084100d031a14900c000d00703005182c860340300078144c05050580d9900e01080e010350f880c00c0503a02100d942c0c820780002501c915202c0c040d03410501c00208042d00c0d1400c21039000c0f0250300640d60079a40001721510015440d90104002c2c00030f4543c54014082ca0318052a01900312520b40b1041030a06c8240d112410040e5a881c5007400d0056000401e140c171780c0c880d07501003030007008032003030080da144500c605007814440e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 181850782 1250 181849532 181849541
    0xb03010e1f0b090c0a1206050306130506010801050f19020405030a0c170109020105030c0702011107060f020f010c05040312050d0e01060807060e0f010305190606090e06100806040b011103040801 85
    0x70814103129040381e03102030008203c400c5540c1a890082030029454441c4540012502c0d20710020020601030f4a40000908000042c0c03480c206660441c009201004070511110b03005004d03200003008580341400c1e801000c0e0318014420100d06414682b10500404554103a40213020094100c0300918014035165000660324000c500444443c10070740480100140914440300780d042e5115411074464002520307007600031b04030890500c0a0300708640181001044080020001030b82c408040050144000e4100b0240310f000d0015a41055440d011258004045501f01c99101d031107031400910181040350030b03006d4191901c801c2414800b41000007181500b111007030725110030a858440d6079820080c0d40081c030000034541c104035030000f40031056001c0d512050f4050315452000c40c81c1400300a03e101110f0240e040840420507400c010301a184e10401203c5c0d1140040d52044140140c030031003e8011400180118880c948405501009074421501404d6036022141101e841c0d41d01c5d45529800ba0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 181852032 1250 181850782 181850833
    0x20307031b05012c010809010b0409151b02060105060706020d0c0f090603021c020703030b060a02060708010506030403120f0608011103010306140105100509010e10170603030f09040b03010e 83
    0x4014080f200ca40001c4003829a00751460104c8520b41e40c1030750030040d030703050500400160a80d50389040700c0c0380781d46860181d14001840340c40c40b0f03088003180101e11003c1f1483e400701d02150120585680550603000985103040d50310840e0140e8540400e403a142001c1c0c8102c5200100c03150505004404458100407240840189501e43d10382035501c41400f10100d001e07017050202c0003900049581c81c40b0031150300a050042c060325010841e0340c03429010498942c0310302c50500048e400f842c01c02007a00d41c0f00e61014050401119590f14500340b41e20010034100704141d86a5500381d076144030015043c0c1c1d07548080014076100c0000c0c0841d21504140540e81d030400d1001783c40e4941007500c40344440841c0c440701c5068407401032034a90303024607421040350075404c4020818180724088001c51407507030315011341c40c00c4085035603940c00102415116681200101a02090180c1d009201102c074240102c02035070392004003624009003030ba1422000a0240c501020f000d00180104524200854844400d90680 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 181853282 1250 181852032 181852037
    0x20120c010306080c0a03080c030717030f0f040f08210108030706240b0310030812190b060922060305010c0219080a03020d0209090c2203120507020307031b0501 70
    0x20030b0f0b0750b0700c449500c5546900982d603100f01c0301ca10038000542070b8005000d80f551000c0c100c07420031645548103601e00f2181440105540030220800c04c0d504075148046030320080b600c100741110f0031701d0350f03443e01442484040208032100101d10300c948106116851004007904107a6050f280d40c1d40ca4515407030f54028a015144107040901c01c0e40492003004089001c00c0c40c1d800f61510013480c144041c0151741002d0803968560010f00740c0080801c40300c0d03018000040c0d40d42d094002e20700b0b1048540383c0c99a41c0c03243c504092400c1c400c080030b1507a40d007801c0d226003810580c1d00d040c960000c6406078029a80403205000381a2420101105001055100b642c0c20001c540071074a0300c0300082007000c045410140c00070000740782003000c00c03420340c4260090a04003800300800b41c1080f548c41c0005d40e40c03580465100075151710200c1c11a100510501002c000d010000200300220b178115240c0710310401240d1100710034041d000070480f04548042140b50025900203070380d0b01d400f019a1a080f1842d03076051207080e00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 181854532 1250 181853282 181853291
    0x14100509070608060d12050f030c090a060c0b0a050711010e01090623010b0d1b0806090a0905060109020309150a06030b0601030225030203131206180201080420120c0103 74
    0x18481e000e8502940596001800b00d0084072aa0f80d408080e100c06c1e03011201001307010310031840c4142c0710b4406940548072254425490741400000e00c60441c0c1c8662019041002101c0c03030030041110205d00c5508215182408107195030780413810340d26103c4802182020b980381452501080006511540b42d2505c16081486550b00d102d0b2074440800c1186442492401c00c1c0004125130b501800041990038003041000c24140209404e80010f010040031103404240309004100643c9445046d0701c2c0c0c01001070303c04120043e03942d2075140d52913a05005203515664000080b9101d00410400055050310007020100c1c180361001c07060010f880c0c9480202e9501c116000400c441c2d43c011d0096594051000450890004a14200ba440005214410340550008201c441030f001490080b8101422141c500c5881050842c98030a048505120303c1c01c14101d031003805100141c1c0e101c081244c02c00d42101c60142c83d80503840c4290b82d02c88120030400d80c44000c402e00006402c60201c0e0381501038009880401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 181855782 1250 181854532 181854539
    0x1e11010b10020d030b0301061a0c06010f0617060a09111806160b0402010c0210110c06070c0b180a0303080105040506040905250806010801060f1409070c1410050907 72
    0x214441c03042255400758000c200c20070030302803003984030980301c903030042c00403a01c181c0d141603017000044800a9051004000110302c901c0340d40c100003890040080621215032241f134180002d0040800d40d810403803840440300425542c2c1c0d51a41140090028000100301d42161500d9002c00f40c9d00a04183d10340310245404101c85240c1003040d245c080c407089801180040060303480b0902840300800403410700007004010009611a014504400310b44c079141c40d064161408070b12403402d64504d109500c1144100b1401d4001000e29210501f240d42d010103182d120b030303a04a0030080c41b00341d24007026001301d843c401c00002d0607408041780381202e0007681c0810040e10b50105001c203030340c0d000d000074001d0b9003c2d10407407101c1c00c0f403000610482160130082c10601911600300318146842a485240d44d6910b032001440300e03c042c0240e2000074001c04030741c1903062076034801199012038024a0003080c884101401018010003011a80d8000e040005442c0c10076901d05803880101000e440d05520b07841080f9010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 181857032 1250 181855782 181855789
    0x40f08010c0206131a04030215090d0e19061107080d0201050610050310031106070609060902150304030f03270c170c010206060405060a150230070609031e11010b 71
    0x412034a030003a01500c14032902030345c490601580a80100d003180704804030b50312180d4010425600801030381c1c000d03107a40700358a40020810f02d0b459254078030620040245405a0b680c5410301d10403101a41004c84c07104a10380e03826410440e1036031003c00c0601486456172202c1c1d50644c0814030846040b00c2c50800381801c0182243c0c180011030f080358107025690b8051010540b4100e2110341c401c002002c03203182c04544c0d43ca510a0b20b641c05c40c1100c0c080e44a0911108600d4800f508852848d5800416811441e154034000c01200010f200d20090643d22011100424594041070b143e10940507a01c0d2a100300d82d140c0f40280c000e09100c1c540040541001c03440e124030380031441d101d0441d0168000c00c025103a802c20080108005003c0311b5001c05241740000310414800d5514604140c03680141c03100e0b894030703503240200c981100515035030b90036503442c0d0b40c00e00f011107001c0c2c8441c1500a240003801c15410702e0155054031089a10610700c0c1414030f41e0010f120b6004656280388030341c00009100d00c2103c4400d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 181858282 1250 181857032 181857061
    0x603061403030d0e07360b010504060c030c0b040503030f070e0a030305090a0509040f050c010504051804061103011238040602041206050f2a0a05040f08010c0206 71
    0x30a81e140c2c204004580d1200300301c0e0080700d400c01d000d1054404880d07031044404c0064660f4440820460f4110f8007071210380e840320b0348011194446410070f000c2d501d000c200003459841240180030070701155400c1c038000c3c148540390311481c00780e0141540107981068148142c0d80e8000315200210400402e0000e11414032403648100345420103484c2100c201c4c01c5540907181c54004a52154100f000401d0006965894500180c0120302841002c404594142020703410a5143c00d005814008200002c00068945656610a2013071421048502d030b216032a00b039010748001c83c2c001001035404000400d01c000c5000e42d903410f052003044404040e0412103401d17810903a28901c030008078140c7c2010240282006500181d00501c14480103141c983c9503000920504054402680c41a540d0800c100a200503032500c140c1140b20910006884070784814491a038801c2c45000d280352078000315403051000d000b00280d070701400d07000c64040055601d512005008015031200a030042c41800c001c50b04404d0208403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 181859532 1250 181858282 181858319
    0x16030206031b0c010f0b100504120605040f0b01140126010b031e010305010902040b090f0a020919080a0203120f0904090305090324070207060e0d061107050304060306 73
    0x304505542c0c400e0302020310188280d10036501e1200c00c2007100d07050b580078404c2c22210005150009044800401480315004450b0300d940103101d01040300707020184007910058845540010042241d13070b9030340750044080c02c12040061001540c280041600814802030084854080e07031040c01c15107000342c00200c91907180e605007141260001c01032003041ca040004590114141c41031810740c04c0000034024801c2c400740c1c8152083d175550440c10086280a000700c8081a4044a9080c1c25080074650a0403140014101140c2680c4c0060300184944030422b812102502c0c2081c40701c50140c0c0e03441017607203880c000320703080b4401c0c05110544020300d16032409485070440c1a080c031a0800c0345540520000306a200c13415802c2c04024041e1030030f507039410009107140300c24200c074142d22000010980342c0100800360114080d900180c0040c08120351080500700c005c18211605803e8048900b00a1300800d02c000d4100100403001070503c1c10b110000004104968281e9030421100c4e68034a9140389a204184 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 181860782 1250 181859532 181859539
    0x9103b090c060a020304080106060e030c01030f1107030819020301030c060e0a0902220803191407061811031204030f060b100906021207240609020a080405160302 71
    0x1420525860060421030350214500048804000c581c0c4000b420036000048101c0050b8400101444554030078000c840081c0011b00741038203907107508400030f5110449242810b0400d56940420701a10a098202c00d5500d0039206501350795161a040080140c0e0b4100c80c102c000300003124200d0950980d600c204d90499412140581007641072960486150b40c0051566600411866001c90b44c0f8980b0f2008191000b00035011a007802c01c0300500c22442d00a90b030240c84103070030034040303514101c41c0f105404d81c20380aa131600c28103640415030315502c10b001c0d0b464043c00c058a0010503d85240000f41a505d82c68011a440d14041a80c081007541e0b4184004421812003401d01c010800600c0191429140610030040480c407441c004000c038903410700c0403003800009296088200025601031002280d6403840d01c032018504a501c0e1583d980036500c1d46016a4661201241403072811030991005003d06003045040d540c038180110014441344054400b07440d5400381e4000c65056580300d000c86800c40c0d0303019 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 181862032 1250 181860782 181860869
    0x2010314060d08030403030905010515120a0503090402070501060902040801240305031b01021b030301091109060304080f12100504050106030216061503050f010e15090309040b0f0910 80
    0x2035984080f5504058012420b040e01c03000380320002202802000d01c20b01001100302c0711200300c84100b241103030664039122019040051001c010407404401ca441d8880c00b038a02582e506e072545000c0f03006258541c00115194070105010034243e4064100040700040d00300107802080c0451401141207901d44001003140c0d02c104442c5ca11410040760200c01074003020001428040000301c800c03d02a80d250311181a90000001809214014810068181030050540d400c0110140100f4420320001e023018060810110b034204405401504445205c03440320341c00c50325401c004038039400320001d40c0900780c4101c0c240070003c500c261107031003134607a048204e2014148200860321000002c051540c450034070085d51420100100310704001e4080c0d403241036000018a110460310190410b018030007030003000030b401c03018442000d00c000180c031010b02e0200d80010b0302e8000200000d680c4e00144103c0390304050000302300800352035040410011900c08000840361200c040e200c0c04049141c0803117501004024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 181863282 1250 181862032 181862059
    0x415090204080d0206061f03050c19031416080c07170408070f170a0609060f02040b03090715090e07030f050405100f060612110c06160e01050702060307030203070306210201031406 79
    0x9030802500178810500b141e2400b0bd04464491001e0000f18500300070944800d010481e0380500c1084560214110704a039107080c148080041c010350001d40300c000e0300900070a00f071060180d03106800510085001585940c1c0b80d84000381501c0d802c1511a00800d40e250b4540002e04104420940d59991104000780c6111550f613030302c5900410210328140c880c0d030f039079640c14454003035140300400203841d001066a03100e29241818034a4051240c000400e100c16034058a1040354006041e07034203071064008081c20380d40d11418110000c01c3c41400700100c50b420101400280007020a10b01980380743e11100303121b10008126920141ca55074826440041d044501d1119503404641c0800c95011083c0702442c03130030f120b001740907140031415140d40d138210031013001d02c0c00ba05400c441010046482030a201d070408426030006020760000030221024560000000b5083e14403aa1100c00030380245440001c084510a9043c2601d0000540c00c83c0464680f00303001c0950a98510740d1032152030002e01e02454084e9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 181864532 1250 181863282 181863287
    0x4060809010902060a03060e0901060b0702130e06101d060f0f13050a02030910050c03060d0501091a1e010f030807030c0c03050a032c0415090204080d0206061f 70
    0x144810340da9540c400c20720005039110700040042001a95021803094180760302e00754000c0000e400701019a01d0103d04100c440c00d03070310035501044c0c0c0480e403440d543c01c80d0744000c00117460b0101440c4101c1c01803001308105800700301110401c0e241d070005c40e100c22500b030b903498401c0020240c942c240d00c40070310701e80100c4910302600070b88010080684010b811480d0780d4002c0c01601e6003030704c14003c15a004410028400010002c0c40700d200f0b03110006001034100300107040002c0c84042c0c1140c1c020001181c0100a1140035044040242c3d0b00c2801e000c25500190114654010240e81100b101c450074850044094203041001d0305840320910f0707103409541745035521002030384018021001e00c030302c0074a4540030a0100500b4001980030368050425152123240040124907540120342503c810b40510702800800803000f5242034005aa00084406468104100d608103560108040c2800024040351541c2c0108503194030719416001c448140c0c850f041041452452020500185420398910340c000b1071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 181865782 1250 181864532 181864547
    0x17030709170f0f0c01030b010912020904020d02130b0a050409030203030105121507050705010b06042102120d0e040b030f0d0503060d060c030b090f16050f130f080708060c0406 77
    0x81c11004550308801e44072110340c109100c0030080394580d000f8000d908036550700350003030101307001007440d0016165051042040e900c00784100041c0c06203241c10b00140441d102c05084000043c0c000b004c0c2601d10101c0c20480300981604040b03c2c2c01040042d4002500f401d280c003d8900c059407507000b5500716801d010074800c601030003201070807281c8620340d18484c0761486091081d000305200c0d5070b030301e030b6a001c1c40c00e019003500d100d90f140038003410701040100091150b0000c0800c4403258400e66128844c8580001101c1c4442d5400c618010302420301500324042c0c002c45544440103007514103001040c0d42504240d1940000d0301f4407019a0441000301c134800344180000c50780030304020641e1540e07038500c1c0c0710705048441c000340440109a1750705040200d0b08d8003614155006000006211182c80d12a00480c1501c2c6040c0c2d4074070034072401103400941c690300c00003070b500ca04000745080c00c131090392900c140742810502c1c403607208a030003007001c0806e580ca00407840c01d101f8050b6000003450503241c180100c8440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 181867032 1250 181865782 181865819
    0x20d030b0d0c0303021005090735070605040e01090e0c09040f0f060e19020303091009120b0613020901050406260c0a0e0a18020319050703020717030709 67
    0x281d01c805540740001d04107610400a54000c0e030050107030001d00784001c0c0c11120085c10200142c0e020a03820042054111802c00b000c0e89540c00340a5403285408051020002c01601120b060141c60008640c2c25031001c0600204d5019251100c180c0e640c600c0140700f110007034580300300c41d0b030850301c400c1640c0c1c1010600e0076041403082c10114400e80c11501c801c01ea00340075000c11039000e0303262111141d06420420000038000580b80c0c03049444800e541c000381e500d00c500a400307801400030000b051842070291000c60010310400c0b108072200701300c40c03030404039400041f50010310642500d412582d01010364800d40b40f81000c181c45261416041200607034110005000e102c0300c080c07418015034000348200b41e0887c0540702d116800c644800e101200039020301002c4c50510300891050702e01b0003000034000b5001c2e1401c0e035440d000607500c0d06c07604249000c2d02d403d41084c1c0b20440c2080180700910b54180d00a081240c050040304c40306912445000e24948400e0b0b5071200056280c29088c0a2741d00c1031000b01e40718 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 181868282 1250 181867032 181867039
    0x302070507030f060911030d020c090a1e0c020d14090d0204060b0a020622051e0a1a0106180b03060907051c06240210110909150f0301020406020d030b 66
    0x10396803070340d0310383c050b11200c0c0d0304071521a26010f2a40402007405c0c0c1081d81c40400701c026010303460703100b48025510401420654400e00d070303403000701d03081c800c3c550b0064a9079100c288500c01e2000c4020030784030281c00420103101c0184503155000c440244500c00c5592103540300c40169203484948010804103070b00c212400d0380c0c469034a11002640038241c00c000c10000c2d06540103071006180607907000303282e031b01c2003512490b2446000140c24005040400c400ba110f002618481209850085141c0d160103180500205a0545072446e40b6051120701c1c4018102c40c2c0d103070b0300c84581c0105000200d03903240f528490245100803c1c800300f151807410f240169030002c01860030131300f00540340049400d1100400660500310f90f0fa410709000e000c601e081105401c81480d90100200e1032101c000075640c2581d0f101c00240b041d0340b0020102a002d040701101c000c4100203000003480d043c03000c00d886044940c2086144540710090050076241018000d07a011174047d030700a480c0d4110021070503030252450141c2c0e60b03407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 181869532 1250 181868282 181868293
    0xf0d050901050328050a1b050319180c081606030207021c030e1e01080f07052704360b01050f04110304061409010536010507030f150e0703020705 64
    0x6100074188185441404804d00210304180817403940011015291f54401c200710703040080141d896100c90340000d440944050001e039007071131955107140c1241e40e01e4004000e10320100000070959000554040c20b00048080e0005840c0c1e9800250308910601e500203412a0009211b003029a10201c0307049035403806070400100000482001480e4507260000b4003000b51049110390640f5603000c40116803061004159841d075082c1000d01421a004008104443c144405111039111041c401c01421b03030400034106104480038080421800a00d0340380303030b0640b1000d03682c4403d0444c0010800100c0c09421003184645a42000c09004c6044980104503400c26198664074071020111001940710740e0259030009600e18040d01251004d20000c0c028201032781c1444280521860019520364541c0c2c929001088120014dc0b842e140400c0c0600146119520348402c004500f0b0700340d00081081d0240081c10800880d000344108148611400340c80d407030101040010300003030300960040c80440e000305c01f140c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 181870782 1250 181869532 181869601
    0xa02010b011b0c26060903040810110403020f21010603030305071b08030c041a0301050306131208040f0605070206100504090c12060207050d020c01120507080402010c02210f0d0509010503 82
    0x1071910f18103940c00e031074030343c000239041054240c10710213484018400341060041444411010955004074000680300c4c0b40020010f22540d030302c800c0310386c2c1481c040881c03160b00115104100340c001c0c0054401076001c241008001040903102d400c01360170320b000710640000011440c2e01e44205c130382c200402c1c6864200e0104800300300e040481e94444803c0b2064000c40307a0f2581860140b50030680b02529240c441140703c8044000030f0f0400b00140003549492400c01095521410220f4004075580f4002d00030034030740300c2441046580803c07081c0c8144601e0052482507590307003091104842c0b42c90005087e509090300e041c80842e4600050012850003024007608000180d1915424201445060400b50b403160507aa6500d5030012282803031008901d000b04014602900e014121410061000b81001450361a000842d91407409142000e00e480041c812000e50038441c0a968080c1466040703070310320072480200000b83c481d8040312010801a51090308640760045c041000c402c40070384201c15242c10351140b4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 181872032 1250 181870782 181870859
    0x1203230d1b0201060506160203010603080c0f01060b160b04021f08090708070f1e081621030e13110d02180906010503010b1b030a02010b011b0c 63
    0xa10000202000009030768041e89078811076001d0380c28001d01036904002c0100f02d02d42e551019202c41c1040200c040c00c410080c1c0c40040d004041542005040c22408a0ba14000c92400200c0c0110b50744003200030000306031030380ca016105001c0c2000007880151860882c8000600e610001600b10340b018103041c0b1f0010140048800c00070f04009a440000c0c070308000c00c00c0c0303180200201d600034a64100a0700410341884040e080000d414002c00065032107840c641d5460310003024802d8001d0a0752400e850041074207828518401242e4400e40401c01c000c0002c803ca1962130340656511282e140d207455002c11407010a004008100707071145100b060f92218884c2522184d13000418000346d007820016542d00403885001d12a01c191811140594a0ba2040020711b0744c2081c1105d05440740c048040d42c4030301178450382c01c45090060a480c01d4500000c00d94032180d5405420032151004240c0703408215110300c49070706104072401d510140044440c502c042011300c0c0185400c0c400140701e90351000700c1100440d0030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 181873282 1250 181872032 181872037
    0x1805060916030603120503100f050d24110a1722030210140f0901020a0e090a061701091103061006051b0607120507020309030604110f0d030302040906050604120323 72
    0x2c40001c00c0d0008204024200b04a21a13400780044509c100c6940b4180700100340f2504108a0041c03821803104070721038a61803106036119205104031400c0c8885000b1052040e82c1d07400c1400130b40c0100f045000003070507200c01000024480e01040d0a8051071602008600c1814403d9510036800e43c0650655071048039081d00407124180101d4202d15071030b0800c0301814800200c010503460080c1d106010383c0ca01035034404208154030304129000e00725900c40c0301c20321004050300d41c0491844590b01ea440b00c241101900115200c5010f50b403d03505600e4200141a12080d0848061420442c10541441790601900140242607105002a81280640c409903803409006541c1d810106a9010540d180d60000e0f0040e9a4000c0103032014504040c00400403070790b22603000d000280078208091880c11103032600120502d10190003080349060707081504014000798054014a03001e00c0c1000d00211b89400d009045508452034507a100c2400c1c0c1240c1c504075840e0681a105920821882d02c81041c0015480c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 181874532 1250 181873282 181873313
    0x2090d080f091e010210020304030804030c0201020304050a0e0105030c0301020408060a1802091509070207050109170a080f0301180c080106050c011506170604060509040b090c0402131805060916030603 88
    0x36000d050030343d0310380013a182c02042940750003628010400c1000107640b00440c2a01715070b060030514804141d510050381540226084503401803854200010744141c4001480e0489100381c0584407040f41c4c140c00d2500340d2081d0302964040f9441180441c01800c86a400344907603403034402c1c05005000b01580001d0402105036603103100c0340c8a1503030803072862900c4030315541c0044050000713126503890140007801081e000c0c03244100e444905104204020400d21003461581e500101035965138081e450713003134440d41003070040060080302c6010480c1a55464840c00d50481e000381c4072001d13544e107000c1080381e0b580e100107042d04080d500d4884d000d00c510034115286000e0a080d80b240d002c007041d4000300001c1c2c09402011a4403d90505a080040d0f44800040c190026001080c0c1d410a075918900c8600d4003a04511039a000340c4000380e14410002c3d421a603005841c0c0c03008402003184040001c030401d690b001d542c01940183e18402244c85500900ea00a10128140c100802c5544c8c0e01c2c0c80d00035207440d0080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 181875782 1250 181874532 181874569
    0x30307030503061017070c0602070803100e070311040b0f19080105040f090b0c0a05191815120b0f030a0606030c0b03070c02010c2409030207080102090d080f09 70
    0x40c00320702d2074070803109000c4c5244c81c50141c505425060007483e00c00b0b0050b02c21401e210720345070f020003400307020b4048640e0290818059581e0b030800c002d0300054401a4410545800710560100c1d59071032280c014100600b11454160341000d0500c82d0149081e030181b6040100e64004105020f603841c0c4c92201d031540307210300c3e440f00d14141d85400140416601e12070384a280a501c0c0031040d0000501d555141500708201046e5581c8650900c81d00761181d21408403030b028410400b1b00c010710f5031948840700003500010409501080c541c0d83c415450030794030369035031640410440e404d102040c1c06076900000050030002c040300306104a00000c01c0c1828604501a00c085456800a005000381c0c40e092000401a22007000d00d540343c5808011f14010344d022009040104060160382400f1101d4125001a86845c0460302140340d400804401850001c10443c05405101c00c0001d00ca44107109031984140060a442c444004c02c0d80e070704050b0751044078001e06801c800d00040c495500c0d1907084012000079507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 181877032 1250 181875782 181875787
    0x61206090c0102010507020d020312060a1a0703030b0a2106020f120103110a06050406110307080406110d11030904020c01110705100605030303060d081303060e010f15060f0813020303070305 83
    0x2000207013510300c006c1040c000e540c00f00301c0419889900001300c808600c02c2c030702c4252442d100c40c800503900d20340355480003400c107401140803088150030354001c0115074440d48040144100769014000c01103121b201d01807101140210000e400b046500071002c030b80740f20350702c01840e041045200e00760350b41100c8a50028407043c1001481080104c43e19072440c02d43c01c0310558000c625054005100e031043c6d0003500200088600040d00041c0100f0a691410350701a41868a072500d608000302182540044444c0910a44081503421401010700001c500c0e0114041c606c1e01c14a0710620010354003483c0303000240e41d0b0f0341c00403a400992040103480014892000382405807501d5501c034060703a21a1300658482d4004100384101c80c0d0320040e000341616880402642c07a50000402203100302d8160740701400c4503082c469900440381040d480300940d032480c00410404136030340d642070784403104050150101281c4242c0c0944400f900860301140c0c00030b00c0050b440c00240d410307030210b401c41d000004200c0108401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 181878282 1250 181877032 181877053
    0xc050c0909010603600b040f060e180c0a1220030c120109020907111e151b04031a011413150e040f0c06170f06120609 52
    0x91010a450310419003405d0940e04022000b04c2d07161806144106850050050a03040c4619006480c030326490000c00030384950201900c40380a0304030100c60610491601f00075040c0142640f00c0c89050710f40e40c803240c15003682d44034a200040307400071061103241d105840e4480d1003030340c450344202e000d0503440c0000400d100031440d00c001130107100d4005082c00000e203501d00c0324580b4002225540007108540001c1c101020000c00c40c01000404000794101600f0010032004c3c80d00300c5041c0c200010004100c8c0e40702a060b21400720320b04614180020b05e03400180394009108406552540c0003140050641c0e100341000c0881e04050340303d50b0045a8078504c1343c2d25500e0b0f4042e1150340300e00501074801d40e60314080d13440780069a003192022814031030b580d48500c4001403c80c4e0307941c81c201074030344c84a41c4451401c00e030900216001000c6000c41d41a0020000803400b580315510030384032400034079000d540948a00081d0405642c00034400d40d00089a00551214040104125030181c2c000c20f010b469000310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 181879532 1250 181878282 181878293
    0x11203020111030112020906060c010f0c020d0c0506060904140a0f020109050a050306040b071e02071a1c0b0319030503160e0a23061201091401150c050c0909010603 72
    0x2006004040c0b1190070f10040050450384544407034101d504840d2286556a8440010101d0107144010700c0d031f0f90310701103019200d8400c80d0301086010031150200c4100c0f079103d000071508541c208000510b150407103008920242400d04c0b040b03812a20035010003942400c0c800c00342e49031181c1c9017801c0c0c07020600c100110055581000b4401d001d40b000f034514692090420001c2566000003500080c4404400400500182c1c883d00308880c03051059516001c0d041c80b01e00300256120b03290300440244419001c0360150040c1f600044132507c40c81c50a902c080142002c1c2c029000707000440070650035014031100826442040402d0b42e4a046c070945a003074881c1071010840001d000c5000404007400300809d42d4810f02e0b500c03134082c0c00c200e0f01c03000c03911a8000c2d4031020040e07102101e220900d401c1000030030b03103a07208043c110425041e06d00341c2c00c1c100b202940f4014003442043c2c007031240000801940c520403070200e00c90b00002c582c05000707004a402c0c045401e00401c0351014121000e00841e50b40e000305004201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 181880782 1250 181879532 181879541
    0x90c09050c0315130e120d0e0f0a020123071a060a05010e061605030403140d0509010f0c03032009040e0303090c0d02010207031401051006031a041d0102030112030201 73
    0xa05103540e0b0941c0707401a10b038011200203040d000d12070f412440080e542500c00740c00120203848181c082d10705248407610761001d190805100104138900f40303a0740c6c0c20b42000000d03020780c050010030001d080c0d0322120303001900c076040c10440c01110b0420401d041d8804000d0384004043c804e11031851541101e100c00c034251709552002d400c0d18420150400d013080f0f02e0780e01480400b2115806c0354429039812100e0701507420300b02a0100144240008a400001d01070541001e04a01041d10300340c0c0c09035140c611013110345100d0f4030042404929100c40c5501184d1096104c0c1d81801d200342000280c400200e880c4020b0032400c00c80d44140b061f03001402e107003c1e0030140600382c40707680490019402d50174504421901d07440700d8842240511003095402042d603100f000320303600541d08001303c0600001900b00c100d001c2d20b801c80706110660a1200001900c911a105079003a080751015440c5822644504000240c011804450021155064058003144c001c0c4002d40c000d100390380c0b201900126900d8042c0c00d45 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 181882032 1250 181880782 181880791
    0x40e071d010813020f030a0209160207150c06200c010e010e07030803161b030302040501140c0a03030e070b0a08011802070804030b1b04090b12010c12050613090c0905 73
    0x1002e100188411003041412400d10594104c0302002030034440c101003454045060300203503002d8148000d0105048140c0643c4104038a5542030b101d8007900c03040300303207145070302ca0700c190000910281221f000300d9590b034000341e02140c05203c0c40701d6001580100c2c41c081c4c0c001180c1e002c41a50340340124802c0364000d116441d41c19004802a025142c03075900d662000b400010603903811441203c0d5801d030310340d00c03480700e42c0840c0752203c100d540d0382662401d00030700941207030282030301040f0341c070154034a00300b5250245c90f42e000c454001003d5080751646e088015150001403040e06100d4084081444c0ca441c40c080c1c9041d404075656205190b240c08402a824034081d5001c44049104000403804038802c102150162908002c11203126243c14081b040e101e003680103a070710141c0010901099510389600440d02c9140201c50f441c2c11a0103104816080b00d1100f01d00b80d003c22200004110b1640c0785c0e40080e680031000501960800118400800694803d00d000700c8214840c0901800000c0607407080c11b410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 181883282 1250 181882032 181882037
    0x225210f020a020d020303070204020307080f0a18030c0203150903070b130203030a050708040b0409020706050f071b0206070506090105010806150f040f0f1506030b01021605010c08040e071d01 84
    0x80c5002504003035120b20002d40e02034000c04d205a0300c41d0540d2000c0084555455000e08115a03a10302002c008011210a868610000480c4000314a19001c0360048203000d84c0c01400042d0780c0043d60f5401c0e58440346400c400c036054040c12003d41d29114031001d84a104401507005140d40d2000c9251000814800502a005c03010704148010b000da14000305442c1400184d0820580e50140c40c149140603001d558000c0c00181c0780000d000c12038040c2500600600340c403524045c001d52300c412010511119085030745100050140100c130170501c07074079600d07405600d0018103028a800626280e150078910b007114110456034481004000c2d01c1010814168840b83c04102e5801a0a13123100042e04240800c5009100c0c0b43c035900c10444c111000c0d440001e030014004e00400201181c01811404080d4500c94023001c686424104505075002080002c44010b4041e80c10b90941e00700001901d2516000e40181c44c1244180b002151902222007201e0194500f5140e400d182001110140c805c2d02985004504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 181884532 1250 181883282 181883297
    0x1208060f090903070b27010b0f0f24040506070602210403050304080d0e030c0109060f020c0a060c0c080307031a01260c160b060f1210022521 62
    0xb024001109883d1000d034050203241c42c0e43c03a001c030901c503904254118092694507092484844680560022030011020303a500d03104031419000f004000c000c1903154982010085607618040181e680d0700c912440c2e20480704030b04140c4c035100822200d402416080740c01c50341c0058400380212120b06145280080c90200481c1490141e8008101c0e000141c00145002c201142d01c151300b51064105d40ca22a0054007100e0b141c1c0c24240c11a8042e00140000761004d80c5011644038419182d402154072000c2c1c0b4800030002d642c0e80350f88001c000c1c803500d404d24041080610800c3c0004160b840154000c2c0007554010420301c0204076800d0f003801c40e1a0020307060290b00340340d0742014801145070303180d01e03405102001c84603038071706194841a100ea03d507a2208840038640709010000d0380da40503030258206503200d900c0300744158103214002d5104003070316105a0102c100c211001d1010340040c9504107400341d001728281d03240345d4440b20890441d0b804a801d40840402e04600315403c0900c42e6500c00380349000f54 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 181885782 1250 181884532 181884541
    0x603010c05070f1106030a0f0507020304050123090415090609090c06201c020708010221100305120301080d02070303081306091407030203071a0a0e0301091208060f09 73
    0x41491107038107001810300e00f06641c100244032044e5a030301c02c0d0031405840141e41e80b4260000d5001042c2a03420b0100840c6810040343d192403000045c0c034107440301030b102c001c00403904540c1000c80e60316000400f600894200094080d40c1c541d030084101b41c03080880d0740c6a016040854402c140c8420350004040d0314542200d81010402c40000c6c40211141814200070360030510a07a03500440d001c88000303881d8800e840c11a001e0411050500307080204503820345d41c402d5111519507081c0d11907291042102d58440520813550703d080b24280d500038144101c1c004085590740c1d20725003042d200c6040c80d10913140200041080c0d0f40c00313004100000307107548013514489085580142c102c00c00541100d81c41d0201d20180b50800000c0e9001404d220340241800d060155084280c41e50f800381d60208034040d0258400c0054251005c40002c1c10074060b8078034003801e028003000d00f220240400c8032820f616649031002100840c1026103043c558400342c0d601d001492501c2c1e0240209415a500c88a008540c00d10411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 181887032 1250 181885782 181885787
    0xf03020a080c03060d0512040906081507030c1e020706030501050d2f030f0a051911010503130b040507060306050a180c0509090f04060c141603180b0309060603010c 72
    0x154000c1816078843d403280c413581301143c15990b0180340100144a0544000d107501801d07400f410840f0200c001c04d2100300e8980d03400a48411004543c40c20b2080c0540c04507a600380280c1018548410b00d250402c3c203451031485021201140b00884000740e0440282031100c81e17410300803940548000d5400001d0f405155840038211889109102402840d200c21414400c041490764944c442d001021104e0b01c0e50140702040e01d8060000040303a0520490203a403000a188402503000a5041a0b040080140020040d14145c0c801089103001001c00f00c080360003d0100080c0c1802140208000c10840c0d0400030042e040f0748840c0c100354820040c8803003c0104080e41c1c400320000101c910740219004c3d86185068840c0d000d0080303107940c0b00e0702c00d800700140041c003841d07503a12460140c4014803143c00c882c80117131441e20000e10640055030040048000c0c1c0081038a001d5010f91003403408400c13441220303081003100c100d04d400120502800100380070300c8207410880d00e80c012804030000c04c441a85090007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 181888282 1250 181887032 181887047
    0x302010506042904110d15060f02060a150905070e0a050f0607030c020a050d05100f1808030907081911040212131b06110d080103020a05040f020f190f03020a 69
    0x1d20400f02901c1d90701c941c0d6243c0380c0000642c0250403d856444d02400040400502004001c42c2042d50b080139001624922461420342d4500d01034024022940700e07159044060210b40040c900002003001c0001a452414030546220b05580e80d1490703c0d1000003400c20041407003079400341c2c1c414407183c0a40000e641c0c0d603100b103c44c010341c10704001000111901c04502800ca46a2100da8840100248801408008100030001c52921038080020440c0e0100003c1200d54641c14943e000c80080c103c10300103400d084c000c40e0894416001c840213180e031006490b2400c8045920710a42c000c0344100e0380108468880340c41101c0d14112820341c10912522240c5541c50801000f2400a10b8184020750500c8428120103d610216043c4462596125500030308080a110a0541e1038407036100308581503031050031414140c4e9401007030100c0c69803501d0200300141591038003508001c0d608008080b05c1c003050300010440300d6644601c41d11640c038a058040c1a070307500741c0c09040c11f0600401500e071210b41e00041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 181889532 1250 181888282 181888331
    0x906030a05070920040f0608071809020304030216090e0f0714010806130e0102180409031d0a0f120c1a040501140403020414041101110309040203062704030201050604 73
    0x74002007200c010041300103040905032101c1e524010004001c19550403107500c8600361019a200c0000e02d80301e4050880c3c00301c40c6001880000c99117084c06100b241e050303400640c3c209001788110341c00721400c002d010f0705c814095032019244648c0c82001c10000d0200340442408806c030340e0b001d00304092610501c031106e045524142810485582d0008041e55961001c08500310185ca00400200000441c00c500035848480607806044920007000094906402110300c1c3d142d15940700711f1418460070b4022024001e2282c0c0c1603014192034004030b20603256a840e60001c10f024280d41c0c00c0484035003884a40388106070089900603040d040d044ce80100d50200b101e04a40302881c014298002c040d55408450055401c025402030801000894001581c0d003d64080c03800350210035645c2d11000e0044d600750a0611004465800c1401440c1c004e1900703901641d40720001a00303408080e044d1300c003010031540000040e4801c008500b0280700601d942441065400740c030030b079000c010807214000c40d10408401c0c02e9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 181890782 1250 181889532 181889549
    0x80a1e061410171c02031215090612030a081005040905011b0908071203020a080c060a060b04060e040b030c090405031201120c0509041406071706100503040b0405030f0d09020906030a0507 82
    0x342844004e91007003044600816040c5000c0c041d5003050302200f40641507044505104800902c082100e40c0b0342503018640131300141008503e030281e0340c8000d030303043c0000800102c81c8140c01000058540c481d409040e801511a46c00010300d000500c0350009000401c00e1000200b140d081020b018594000650758242c842c0990842d09185c2c05180403403400c01c0c64030000305484008100191481400120300303000e10080c000601a690704c2c2c0c07481c0321043c000c0f4441e4070001a0320900c8a0346a0401d43c0c0a0501c20b00c015083e00d00d00340510010425140e400e9404a686510002d190740c642001d80110324090248169440ba41c00400d8440741c120000300c2c0900352180b20000041000c010700d00741d100038012210419140503140c822005040481c07000303905401020310400040007841e080c2c20b007801203c0d09031509400c60b100ea80311a6074494005004803194881004480000031640700a0000030308060004500c070701051061000040d00030b0090341c043c6d80b04564500008a000c1021401e840004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 181892032 1250 181890782 181890823
    0x231f05072d200406090b030c01021609201908011a070305160609050601150e03190312020d05100b030f1911030a020310060504080a1e06141017 63
    0x92903407120310b0142081e90b640649042000154001c1c241c1248441d01030803410b032038010207244010781c1c59180c00400c4d0720524240c8401440a6020340e0301024180c055030018142440110b500004680d01c9202c000486640e4840e400b40e00d517074001c08480c05000c00b05c40c464542c0ba40d41501c01c455010380e0400a0a000b80810380d13506810041800c00c28132a08402c041c0815071301414140d403600c6003801a010b41c54000c00120031014085d81d501c103000c1d43d02400a00c0500e5114848804c580400e0394201c00b0803a100c909401000a1400904003403241d04000003050300f04011090b640c5501a80710b1107106005008001c2c1d40034028440c0d50380513461002d2081c008861000d288000c0a2403001d4400460001c028031210850b10350241d84110f032060a00554151039620665450243d03100d503688585c072a8001d4800508a0b482094201c01074a2800c810102566200020340754a000105582d071444800c00104900c2d076903401c00103007103031202e43d08588600024191a0398003d050b80c044013544 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 181893282 1250 181892032 181892063
    0x103030c030309051c0806030a0f1106041805100608070f0e060f0703020102180901030b131b0b0903121305060c0f010c0906020c0307231f05072d 64
    0x2900500c030b010343d101054030802102c0d650103080c1030b101764415000042d03140001501c10f00f4000b901c8000c031900010114009030455581c040144030341260103070440d00500c40050703205500e28552903e5084118007003554900140c41401149959000d03a0410110b0307018854820b4001c42c0d48401424540782136002800300d40c001c59110b1141c0030804005400c0000c0c0e10f0140351303041d03000d0520508226808040c0d5071244040200c0c0c1c00e0300303000290a1078107940111b42e03051034a0710400c0701d181c8107a80f00e411400030448100e0b16000141d11612031b01800145080161500b44040c00c2000c05061440382040030103681010401c01501034503005203400078146180401c200000403014401a000744600369040100602d115070a118850161081050b1550035150100e41c61082e14525810955003c0350050a9148034500c010403e4001c14542d082440c210400c441444262850b40c030f90b15030700e045030324005810030100c640c41015400085189003c24611050003d003680d0071941c0c19001c07024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 181894532 1250 181893282 181893287
    0xc03010e06010306030b07020705040f0e060601112b02010c09150c0201050c0a1a070e220b0a090515031603031404120f030801090209030c10142a150103030c03 70
    0x8a03174002502c1030f4000020800e8131a40001d00c4400d80d041620148003a60504035964299451b1400d2841c29030030403c0003a00552140b80e015642d06220340895803034400c200301e9002601e402d504484000c600c003c1d5048bc109809000c0c80034214014682801342030b10b41404490042e1039403400c1d00412544e42511001d580c410420348000600700b03010340720148031034a0a241001c00100d041458903443e000000c0c5034074040c80b45c400c5040006000c0007650602c030440d2040d19503001ca04400141d641e039490449a8071080c070010050440040c00040d141084d8000f80c2e0845a07421405210713501014440c4071440e803042816044070703410f003408107a5914442120b912405140c02c00344000007001c07100340c00c0c0b00c1549002c91030344e4001d0315030280301c0c0d032160303000000d03031240c1d0040c2900360740080302040240c1000a020002c017401864400704d1800c1880c00c9005590090714240c0a41040c4142c60006000008045580d01d6004000703000700c02d60a0074012503c80f052002400303000c200c9a05800741070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 181895782 1250 181894532 181894541
    0x1e02061501210f0b060418050c071218050a060203040e1b0c030901080601080105010c0b040203070503100b0a050109030c1403030f042c2710020301030311060f0c03010e060103 77
    0x41c000564041c46592507100b040040c9205110a09420300b8103000c840c072420420304440a4550b143c1400074140d111020110107840040d1800c08203020070031040c0c0120708080c88255010b541990356850f0440e24900444200d40c00d03030042c42c07090541035030810000ba000800c45e001c44e07141c9000388005075a10300f01044c0d03095137250b140ba41c44400082c5022810000f100408250301c0988401d0701c1c0d5265035004580840090251a000c03800110460000c90300744124503a02c1031000342223520482c3c032180868103260103207280b800001c0c0c46000102181c41d0000c07149014004c28a00a040c540c603603110080c01020324842d41c9403007042c441c1482101c1e10b0510403102640401c00d034051b9034699400700b12240401c0305000821210b00c0c850700c14481d0b40c084822500407002d04005d2105296600ca1742413045a01d029030740303070a1240c0e110911040d803c41c001341d80258000d450b010040c190768042242401401894106004c2caa02c0c200021502e0034815a419603850b40603103001591880c00690081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 181897032 1250 181895782 181895807
    0x909070306150e0c0403061b20010b10030b030f01020a0e010c0c0b0403140d021204060513091404030f080403020604110f0301090506150f061204030c12020a031e02061501 75
    0x680e4040e0410205051134070080003100c0c803886007000791415042070107508034501448a00020000c034041144070134001708200d1084103450001a91101d8540001d1822912540600203e9100d84a442452034188114045054031800940c5031803004203008001c0c400c4a1400ca0510841c03420100600c41903030307100e101400f0031082059035151281008040c50b40d00b011b00180e0351084480c840c00f07152000c20080040c0183e07058442c00c19041c2a400e0365103070064400c0d4034040398a0540007a0445d01d601802ca03080620300d100c001182000c0c01d00801c0d03441c031011001c3c00d2012200902000a81c00190b09500982048006a1f110354010014211140c010050360385503080c8039410080c86400708805018011016060301140a064140b040c40244011550740c0a04140084920140e1000c11550700600c2490640d03454142642d8075088030004040711001640a0403402c401c05070040407002a04008040110860100400c001d55850380144600078240480c102d000c03d69028202002c0700c2c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 181898282 1250 181897032 181897049
    0x40b0910020f07350f09041107050705030a0b010b031509070f02280b06060c0f0c09010f05030a03030b010e040e060f0c040b0a0c111f0905090907030615 67
    0x395201007822104039008010180c1e45200025100c0c8500882d8003013440500c200a00c030154401d0054a00030342c1600517001100c2030302030402c00c40c080c9070303220302c6081350030340c048625191104000d0900f586410b2980e0086e501941c820742084001c00c9101d85200c0c1161203040350259a0350300c96902c81030030882035103120340040c0003406202089401161418489046d41d084a504030280182c101d44017008207030301c610800340c05948002042038407144a6000402500340d80c030b0291000c41d0321340340c055000c44d0000d07180c00c01c008a080038985000000c3c0104100c0c054490000c0c10040001e480d0200d04000809059482c194200c080e402508207401a11004008011404544181c3d40d01c2d040c040350f161941080072000503a08100c0c042c1640c05030745c0000c568a0400c211507405640c0450b40a800b40c4091042080d006c0c03131943d4110221500105000c003020010381e800b030000d41100c543d07800691003040c19008020071034000250b09800c6903044200440c0b0f954917413008a119032456004400e2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 181899532 1250 181898282 181898287
    0x4082e0c0302041a0d050901050c0d0504140a050706080f060a0b030a0f0501141c0503040e070909050106030b031608030a0e0103020912010e060703090c0e0402041b0e0316030209040b091002 83
    0xc240401301501049031a88802c3c0081d0355503490040c2250707070407161101074190502c500c4010201503488030758040c0c4201c03210040341e84001c66884c981000c1ca041150144c0c00604280020b41d444a00c20b030b0041800c0c120f41030b0038240400000c1081c4518042e0360a510000303c0050a485c60304c0d0840220107000d90350801080d6100c008044441845440c124040c1d8022014083d2508000241c0d50b046070308040990308003402c0415508034014094030450400880d4180814a4001c0c0d215113402005541c4001032400c96900074142807290b00740e0001ea000501050400040c84003008507681072500d40f07041102c8043d800010b90003406100404d41c2c216044280b081044d460561000c02071908030304c1110500d50b2000740480565848070801014240c0002c0c08109044080e6042d0743c100b440208049902c0c140c0802c050a01e8141e54071070300006071800c0103215141018000c2c0c01c9426500d14012003000d0868001c102c0c15100030740002c202d03c40e194001007028106009240401c05041415075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 181900782 1250 181899532 181899569
    0x60c0a0c0602010e15041110020d0201150b0f07080d0c050912061006050d06031a151c080a0324030b0c04030c0b0a020f0a03080a060e06030a121e0504082e0c030204 72
    0x35502c52b4090181c00141d0710304002c400c030544100e0a020110b6044034455450900d501c0d1421080b900840412204502e0910609044a600b4083c0b100c0424081d6103080c6c840c8403141c100305804540c018251801d0700b0080600044443d02c200c1c0700c0940f07c1e14207003150340c0e007121012131000700101c0e0f002800920343c80111804880710109100c1c010b094011000309400350341c01c10407800b6103a410036070840d034110204020004404102030000c1004030709000071400000054883c6410903501250001d0030f0645051040000041200da08001041c8000303042c94250303500c1c032800000c40d0060070740408001c6040780000e4800c011024510001d00240c5545442c0c234039000d03000d16000d0300c842216a050180110303100740002f80444c82004003c0052039181282d460ba4040e5129500726141088081d002d461500000140099107052039a43c0350340d500c51030702c04010304040d500721442c440b10a00803413100c14114011102d84c02402d180d0400100b2010380c00c01030f8001e104550028041c44010400d80c1b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 181902032 1250 181900782 181900787
    0x603020d0c0201290d0602070b06090c03070203040909020a0902071202010b1504120303090501020a020307031421071725020703051911060c0a0c0602010e15041110 72
    0x2000300e42008501880500750281c8183e00f80e802e00c2c010022801a1160380c2d100090848031081801280909141d08110703041e03c502d001e07070380910419100050804113210560518000155001000e011914110b00701030700e00a44910540c491b445c0c040e92070320001c80940d0ba600e0340400042441380c07011580c0351290301c1c0c046040c5070b14084a801652800c0706076149400e00f00304020850380001001e03407600341401c20070305401d00c11240640401d50b0351b144510000c1e4007403000b0400b0b902c641e0002e6032100c2040c5002080c428081100c0582d07400140500401303084400203c1d00c1030441070311100307a03030382d152078084621540100c2d1301110b0801d000d003400502010414199034010080d025115100c0310040141c0c5e031012503101c01040c0307a210501c1c20628a54043c40c064034284124035459035800d0000c0003850130380100d40511b4007071300110000c004002003203d0f204024038440c0028800f220b01100c040c0d40b030f100c1c640c080e541081510000174003001200e200000001100400c0c001d141041000700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 181903282 1250 181902032 181902037
    0x912060601090b041203030203070e03120306150f030a0506180403080417071122020403050c0901080a0503040303180305010e0a020102300a0c0203060103110a06030c1e1107060302 79
    0x101400302d01210b001003460080081140e065420080b0381d0b50341405160b03001c90095000078034140411180c0032284c40c483d0303400d11a05c90f9503024180e40545a04006040040c80c80d06020704000d03c1c00c0401102000001c4102501c0d408150301030005515a01d00000ca03088450400031840081e218a0400081603000700b00c03580218056040202900081d40501c0102e01c42c0002c044c0c0146241c00001c041490311402c00c00c020b104400b03c410b044411002110160b1304241c1007110560440103810f001d60404c0b05096006001c9400105160b0000c3d031a001c0e1284143e0001908010300d018086540031110f4800d94001c6a010008100802d4624203054075030010700e40c1240103011b200004041d8407030801240300078000c2c42815103004028402d13141159070044000d1000d0256078082600035039018007440c1d00a40c080c01e111a84444904100403400c1015041041854505031840d144958802c0c0d686041400c0350704568401002e001055914407018209100d50b803150840100ea910ba15401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 181904532 1250 181903282 181903291
    0x140d080301080601141002030702040b120109110f010207120605130b01091d1606050d1104080706030e030a080f06030109021e010909050103030e01051e210906010f090b030102091206 80
    0x1c1202c4080d51002c0000c1c0c00e07031440241b40103030f01c10b102540141c517140c1d12490004100404001c1c26103400c0c00030b00e080d0364800200741c40f5038942000040d40303070802010741c6144000074409068118208182203a40c1180c621000d01103a5803100002ca4070602c0215182d10a03800c1140c0c042d0540e074500c50746004d003803081480f120000403640d00740c3c002c01d130000d2030001400c034000000495904200040740d49030410048840034544540301c1810030319032a4000d00141900e54040d0994a040070b00240590f906124101180e80c001c000d00040168080500c070303040141c03050106030580b02d40700003a0241298203030107540200142c408062000c003680c804c441e039800c2030729402030155842d01c07030008980f000d00c03001e0081603000c0964200e0390b10030001002c410f805002c5540e003050b00e406440c10203070130004181c14541500c0400ca05510b0340013200325440404100200f5656042c202ca80c42c0c0c0d020a4841c03000b0168541d5920f1140d980c0a4040d41c151440242101d940701c1e000d5417075180c0c0d9120644 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 181905782 1250 181904532 181904549
    0x7080304050d0e03120f1309150e040b010501081305070602010506270402041104080a05030715020306130c02031215040b01022b140c06150d0c140d080301080601 71
    0x1000c564907008250899103d0401000b51003071443c0511044003070341c04034403403807260101040800c02c2241c01b070210001800503450001a0172040c000c00386039100e0650450302622546004000010709150304c031301c2c156542803912000548906d1000000ea521888006019000360100802e2007a415072043c2d10480c000c682d075040c00144880220100b0074214603c6840d440d10800007005410280c01500540508010244c0f401da0360780c20081c03c041100340110344a800004121081c40940d00b848160311039140c2045203141080300008400742c3c00405901c1043d5140d40c0e04c0345003540244240d804540b03100300d4000451409039050001070394904001c40c8114600302100845510001d24072504407084c207048800109982004c402191048020b6003c104086200040301c841c02d90240003a40c503100b0040c0440e00b410f8008944140b0b545404078041d44408201d14085030050141404440c43c803505400c2c24a00d04000c1a00510050000b42101c0c10000000882e0ba400013240343c100c56504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 181907032 1250 181905782 181905793
    0xf1015151218030c171303030e041109091305030c070b03010302030106060201021e090d170d0c031505060c0106050901081507171906030501052706100b030c040504020708030405 78
    0x210202c02501110700000740c0080c02840001c800038030020900d00b40b103116449420309040e41400c46c929444420b40041300020003880e500a02030405019141800071001c0d03556003071641c080081041010020940385e01c21400c2d5507441c1c2404001d00407591040045001e0700d8a075600e030b42c1407640c994401e100482c0a0340c82c05400040062040c400d079440302c0c4000c0340c52046100c6200283d0f900e0340113055826440210328056000250811012101c442010000301e5151480360290600702d90300215a00241401e043c4803003041c0f200000440161a421143c95440305080c1261781d0051610f60409600b1211010010815100001d00714940071305030803072032005640780c0b0000c80d0300609007a800c6400c071031031b500412030a045000c0e040c5901c08040c00c00007203090f626141d050030350f2800e442240689a410740c201000b0221b03445403813808031202c0d004004a0400d10000300008605118008020001002150b541c155603000c0b00c0040600500654446081d42424101d6910544085440b03120700c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 181908282 1250 181907032 181907051
    0x4020408150a090b06010c05032203060e060103080d0c0c0204140103022106161101050c0408120903030d0e0a0b010f06080f04020a0306020306010302070f060b040c020f10151512 78
    0x26409a50506035001c900340104d85ca564005460500003000126101d000c244030b00d0000704802e04c00c102c05080e00c418800c00991441c18050300725542560ba070040346d0018801440400c41d81e008907500105030490001d290704241204441581c81e41e0381c002e5000e420410b035042d10070302d6041d225058900131100700b0390000c04803000f00e0b01d80c034000d201003100f0303082507000800680d9a1040118140c0c40e07400c111a00b1681074070b1842c212034007111400000039000c10700340301000040241c001222520003003180f030408000c000030350b28010401d50b500100e0300d0b8814444058000e00540188a5100754440314035610360400000040b8980503000c0040e05800003d00d03100c0300c54500c1800355030090300720800241591a00d00c0a50700051010341032640070041c60300000c503400fa6091025004050010b80740b81c121080200381e41241d813600086600c101003003081c1440111700c10900ca540248009007400f00b00402c0b040c684060b13400b941020b04d07101911080300742c02c001d44030b01d10046110108988600c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 181909532 1250 181908282 181908301
    0xc010f0e15011d19021c061d0c0304261c050402090601080403021204090e060702010b09130f080307020606030706020601081203100306060605120a09020607080a0e0402040815 77
    0x1c244501c416000c0c04103140c2d00e00381e522040346500b00944035003191102c03203881d02c1d42c0c0c281d0380008501400044800f281c412150114801c40000d40706001180c4000580e41c0c0c201d041a540c05444040c038a04d00001249c10000e40240c540c01c00002c0500740344103004601e00005094000090304081e5040c1c1d4401c4038654101441414400c0781d0040c11540c040e19031600440305110010801c90640c4a09082040034819031400b88c0010245280040f90304503401030410304100000d4560425a03041926030146940d401000a0340903902160542da80c1842d070901c4507202c408800b000d09401000028802050341c0840c42078071030b140c10740c01c032507109a031030304200d0f511442441142c505c0c0e0813074891200201240802036400c01005015100b40350b481c1d44a40e41200c020307034008030106d9030004190301090b0340f07070094503885080780504214078941e0b42c011401a210b000c0c0000e004002c00a1080c900300d00400355003d02800291085480e55211040c490703584520900700c0007000c14110006900c0034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 181910782 1250 181909532 181909573
    0x6031802010c06020a200706031b0c0f030507060203070302040e0f010e06010309020103200c07081630143702060d0c02010203010e060f0a05010e060c010f0e 69
    0x140d040e0340b103500c0002e1545802c8001d41108500404000c8802c41c1e00d070344007083e14048003019030784501400c4d00c1482c2c108003508699801d401041e4419001c10a0000c25401011411000d034001500612000340da1400301d41c18454100020000c52004c000d100b1401c0c0e050780070b0800e4a1406c61181000c0c3c5410540c3d0070808070902c288210010710720000b50440d48645c00038070001d031040c103002c15040c81c0c0a00e1070007a030b0041c4411504481c40443d8100000c41c003004003d004005290150080c104401c00d1841c01e04858050b000e00001c1c0201c0c21625245101c0d980081c88044800e1881c044415160458943c0e4007a83c45042a2041820340580d4050a40700350308070700144110855600170b20245610719030402003041c0c2c0d01401c1404030501c8400c242c0140c041d04a2107500041e40c0e0340c1003143c014060013000c0d120501402e54803040c0e100644910f441c1c80d003515401d0811103c200c081000107007141c401c4510f8100503509000c943c0300c2d1450300741c100046c4009000140c401820680750f603d5001c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 181912032 1250 181910782 181910831
    0x30106091517070315120807060c080f04032d020d020c0f06070f020d0b0c030402010807050702061b0c060711032e0506031504110a091b0311090a0308040603 69
    0x1140420b02003070105000350b01455810782da030108000803d590f00c85c1d034401e000c002d0200b560500c8000400400304002d0b403280c6004002c4900300020541080d9030800b030b2a000c014401400d120300840c5d06001003106130080400310704031102c074401283e031491000f51074050140c0d1400c0035110b4403001036080d241940146040c010050034160070704130541c4800c403070000c0f03c00301aa00181d40005401c045080c101e0030341e21507842c07001295900e0900d8800100162001084138003044003d2140030b0060b92a101215090307450a54030340c0c20380300e401040500b0f0440442100e540000c0001b040301c1044044040070700310490880955210540c1015000c1c2ca241d0707401d200c1c1d0110402c0480b011000c17103855100d560400001382c00c50b91441810215910741d910300340c8069640030213264003000a0b250010040d009418410300501403c0c6400b8159404c0b0900362403c030050540341e42500b0705154003041035400000005220862556603414000c155a10030300030017000a08000c201c2070300c0c40c00003402800c02d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 181913282 1250 181912032 181912067
    0x1110050108031b2116080f040e0703050f0a0b040b0303030703060914060f15090406030b0108100c02030405011b0b01062706021f0b0316060e0909070b0c030f0301060915 74
    0x641c15402101d02c40d0300c5080c001440170781d5204420003080451000d4026611000c10183e0b64a05022280442240c010150410981800100681c80b080440d416810250f07994012482070041e40001d005006c0c5169041e0305072002008010701503905400c081d04072440284204200c08265100302004502240c509404c11160100303121281000d040b10b400099101041508000c007002c0041d059440640c000e440d00c61b100303401840103c1040c0014185407045100c10070503400c004001a4903401544151410f0101d0041c1010704c54400300791400902d07602508241040d81c403010040d1400f9100300c201c420101502040e0702d00c950030500c150007910050f4000708644011441014445803500328a0f08030709450b03c1c0301989035207080020b0303c150f9203a0018601c40c4c40c2441c5e4014500448202c1c070a102d458058140810642c01240b00004d5801c5010295a5001401c0f1500c0c65403007014054082c075000000005400d603808400502929103081e49182c0c0c02c07440300703000c880480e184006000e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 181914532 1250 181913282 181913323
    0xd0308061018062111090406080109020d08030a0b040207050105040303051f09020a0e04090b0a050c090a0e04050f070905150901080d320d050a090c061110050108031b 73
    0x4498000d40380484c1421000030180c240c01008240d05054071011401a40c41c80000b00700c1d41107902c0c2502524003c1c054250080050b4012500021101d03c0b031400041c201c0f590003c00f140c580c02035034200400b030060142c019561400c40340351550081c281110301364002881c00020803a40c0ba00d0034060155000c9074110700302c1c0306041030000d8000307501c441c20714000e1101c069001442d07510340c0e000703ca050754002e01541800749028649541601c81c000c0a00f40c94041c10000000e25030386a070425000d85014070b00541d10740d500d91510030302e403076100c2c0603610302c61040b040001803482c81340c0c010f248141c1c468651101c0c0d0b000e012050122100d402e000b103144c00d40090b154441407034480e0341d82c0f203800080211920001219a5192402d00c82441c2c1e0b280b400c4040091911031003030443c0902038005001040800248026072200a036043e0140038200c100401207200d4580d240003000b00c034050403141d0008200659540c18245d1b542e90090004d042c0e850141803c0500f841d1020401c5032501c1c8000700b0109 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 181915782 1250 181914532 181914539
    0x11d100608060c030a2307140301050d03030f06030602131a0304020109090b0f1513080a0b011e0305011e0c0e0915010c06060b040314120a030f02090d0308061018 71
    0x9240d000140980c800b00d07551b0040756400d41808629030080b48610703003030b01500e0030641002884040383d42c01810034400c007000108119142c00c100c1c4402590103140000781010040b00300d101800320760b480501414004110f0364640341c60172070020215103058481042c01d105200078150703507010455000c0d0100300ca85504111118150300b080c1c18040000342618507600c0c6480004d10325000b100c0c6422425200800c49003407400105074058081d040b10030090030b1500d020703584d580e1440d905010b41c28070310101c20506400040d10710110009594000000c0c08105d07040c1d2004480001110710080c951420074585017842c2d40034040b4a911182c010701050181d03951a40e000020078003650400e4100007500c120303080413400324401d5202030034403031103581c0e5145c1c554100900341c541c00071080700d855041079403544110001d010440b40c1400c000d04010801801c4458010000d005042409801440c540d030042c0403d40c0c0f00300003610030b110840c0e410040c44034240c1c00700c1c0c205035108440316000c0481740c41407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 181917032 1250 181915782 181915801
    0xf06090c0d02091f020106080a020d1e1203020a0e120d0f0c0204050906040506060109290403060f0c08090703030e0d140a0302030706061502060415020c011d10060806 73
    0x50203401420380703001d49048500703004074500c1c4400c0300300203003504403a00c000c40710954280141001880020002c040944060300058070281104d10300612040c41451010940c441d81c0d000b050a50f500030500d03041010075030700c0c054042d50201340540001080200c0110182ca0095003e480c82c4807020300034401c2c4100e0100c19a1052003001200007800140000d040051356540542840f0300b410801070503450605140103458150060000d80c10301410607028080c00c0400e40382d0308513080c01d282c90030750f00b0001c1e5441800284141c0d00054000f6003041a0403d807030080d60001e4441034883c1d551842d00b40e9903c085551141814000100020a01410201540b0f4815051040280520301c030113100883e19540c1071500c2c490240c12009604041401801d000952203010000e02c0c3c9020064091000908001d44403040144001c0c20030600f03121000f40c0740032035030550301405e00c44002003203000c13540c1e4a2541d4994854407048160b20900c185480c1c240d03510b00511088454200007081ea0782c0700c0c81d881 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 181918282 1250 181917032 181917037
    0xb03190e031c09051209280e01060e0f0f0d033e06060d0c0e04051002030106050405120c09060d080f0f07060c11030d0218090403030b090f06090c 64
    0x4544540c401440701d001c00c0300030610b41d041200d001000000d00c1140c58507140c2d0400300880400381c014401403040600b1a1120340c40c1502002c45440190b1000404480170120700405030084a40004c02500204600b0b0b084502240d001d1800c9a00e445140c1c029010040403a80104806d50444550f603d1440028001d4010f2144101c014001ca400c442d1178004c894821a9620111600359481145800150300244805074001106445001c101d0949480e200305000081c4201e8060480641c002810300106100c4000881c680e80c07825956560b5920f0011b1494102d8010b141c0b1404248540300c441240002d20f110608030042c00c10282a56139000b0803101c50118034060b80d00650411501007003800c1e8034001c0800b801c1035009640c4404650503c00212001c82c81840c051091580c901281820000f054500c441c50a80c40540c1d500c3c0c13003114038159204e5043e203050f040603820060204040e010f40128400c5002079440588030b9403002101d040040b420784481303030051140c0020501c00d0550500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 181919532 1250 181918282 181918301
    0x51305030d02161208060a0e040b0f070219110a050a1d09030c0102071a0c0307021c230703270302040c03020408030304030801150e2b020a060f03060b0319 68
    0x28080c20342c0200c2d220360f200c2c000d0032040302c1d00145c2900100200392600b0b1800b0000780c802401c0182c2d2900e01a55045480d1401405a441518000e40042d106510801c41d408102107800014002c1c00e9a900c0c0141c003003000c002c5803500c18402880040f0342030400b0b05d101421030b0018640885900140c840000f40a80d010b000b019203400100406402d404090004004951040991000c0300d841841000c4840038060401c002280702001400b07030060307000403c141e4403180c0b000812101b44410700141d03000d40201d0a40c40201c000001c013a40d06200e03070b00180150307174004e458a806a96216030890803d401c442e40407954401032030814400b40c20316070f21030b69030501642030052605445003403d918642003100c01b00c001440460061040640c201c450700f8401c840c40c18403000c8039089100103045000001ca80d507844041a070390180c90310036054894010217401901200b01c4580f901d07001850700e0b8440c1040e80200e401c0c5280090704404480840e031081d0b06418208000c0c1441944141c0030f05802c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 181920782 1250 181919532 181919557
    0x1401050907061106041209270c030207050606300102090906030109020d0803070302070c0e0412020118020118120308090c011805060a02100608161d010329041401051305030d02 77
    0x20008101409230030317030460040d03c0303604126404100c11411031050f1760080d2528810140144003480025100087c0e2a810040803a01d83c40010071340e007280c2c2484602c0000c41a059001c1e154031240070b01d410b41c020304d005031042e43e0400017a91881d060500381c1302c41d61002904154405034041c040b030746001c081c54105282d0303d005860080c080c3c40742c11040c070b903903000408005003802c140010003214161404030f5014a000034080f00c00c840d000c240343c000d02d00304040c0c141b000000da440c02480000d0310080c0500060b80701030340c002c821030600829505048407501e595100d20018a40c0d607602801244140e9882d5500d0800c0076130901c010b0000640028000320294456a062110b44401900444000d80684401880814000301003002007402c0c59004128041031002c0c07252034a501c0c000194190f0340c2040010b480c0e9212071403561200002000c054280720700c0001800204425a5450400c89125030300a0085481d56044113031042c0e281c110042803680100f08083e401c010305c2d0003400d80110880b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 181922032 1250 181920782 181920797
    0x507060207060614010e1503070c0804030506070801050120030403060b18010303050c0d03060b191209080d0606050316080a15030534030809060714010509070611060412 74
    0x941d02d080680703496030000850310b100118984600c0d64400704115100c1c20858261900c1d044070f20042001e440050300072410030036056449000e018080c0c00311801141d100c0c00b12141860a458010096002806000d00061049050f401d00d007149900d040c611078018000355107041d10795500c3c40020304c400c0c0d16461300824211801390702e0000303004c001c03402036020780c5400d6942c940d0802d0580c140b5440c42211410f040c0790900030f2069080280650baa01c080c410809904e01407401410f4904000300c513621660719007480144010403c2c03800282601100030142488034640b50f90b4282d80740d01048500d500c000c000a08400350303e501c80d50082c0e81061602c2400078112142005c11400c00d030361a002030300c1c0c5910002d803104002a440d412481004503001a8064803440e10800503000882480054205034002c610702c0e403207940d40340c201c17503916034000c040040c80f40315080d4840c06480c04440da101580150030b00013840303a0180c650b1000300300004000c2c00066540780d0b565a403140000a9010410100c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 181923282 1250 181922032 181922047
    0x90103060b0705010e0606030a050a080318070b0c0d0c02011209110402072003060912070302011103130605010503011e11040503011401030606060e060406080603100f020a08010b07080a05070602 85
    0x8407401442c4142c018030010450080f51a04140f502030b020703005a010340c0c0020044000311703001080d1609a668420b881c6a03982d200d184070b0481240b410100c1c210640515500012031140404c000e04144000c1401d0718807000c0005400e654060b0280c501a02284500e450a8214041c50307100c8021903108440c1c4101e100c06050105003260000d00040352480030b101500c1c1110041d0101d440240d8001310300078030b0140b9080c03148948a5409050981c0c0c41000400e01a00b094000e4000391a40d40d03000400c0da031603180070580403422100280060752654540400800c6508040c003d594614080c805200b9440010404c444d00070840d207040120941d20600010844d6035080c0206014071451005081e0554114100282110613541c441c80c203110500380350b0100d9445081c181d604640007810f00b02560755588000c2070421030980341c0d0041452500c40040c0000b10329a001c3c203500c901540c2c400b107a076a01c404100b600c0740300e071032005071010320184508104244248010a600e5100382c1c00503080121 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 181924532 1250 181923282 181923299
    0xb01050904140f07051804050322080a031707020c010e010e1306060c0507080d080402040c030e0609011505040614090601021002030a0203040b060f130b01051e03010504060b040303090b09010306 85
    0xf048481d070541a0000d9400300418500110140c550f003038408500021030a1070303514030b42d03a445052035401c1e09200801d6082c0b031030100c002d1520000d02c11070080d07400c1c40b016440e004200004c2081c40d8540c9101c5a001700e200540b00003183c50b03038124180c5548182c0072444006640c0c101c01529241ea0255840e11030000300383c0c49004081c001c04803034031100c0942c121498a5814803003e504902e40b07582c0221803c40b210795000c1d075030315001070701503400080c1071012007400c070040c2180c03885d0701c03010303124003410700c442c3d01415401075100c100d015000340c0141d901c406c10001614010310030340358548581452078007240703490140c080c0c000a050040300d08900364111000140d0700126241c0804940c0441044180490360381c5003a803254089599040d003100d82c2001401c0501c1005a0541042d0785050340b021690040c01113900e100d1107001c440311980c034030010504481e0b109003d00c6020314100f100001d1032070742c0235056a003a254540c58040b411030030000300c4215030b0450b500721410140c41d2100001c40340c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 181925782 1250 181924532 181924543
    0x11101020c0f06072d0e04020403020402180f0a05031e1e010606080622111e0403050106080a0203100506031618060e28090605090f1002070b0105090414 67
    0x4890005071009240005028191807980d106000100f002c070080701401150a401c030724017440260624003400d4800501040003130096410007500070b4400209800241c444110701c075103c0b4411038a0304221213814080c0200d10101d40b18194046c1e00100070911280100001e501030208000c00300c3d02002c080e581c90010010b03920000142c1a5542d420500a01c0e034002c0500d07034002e0342914000741c4060f807038200702c507284102081420b045546011a40819242c681200d50303000b8030000110350306060342c13404415503005100883d0306629214000032030b0500440d44045164004014124021340c145221000d007400404884d41801840804d034100f5100d148a10b0140035200c01c0b5407582400c0341010f000711103046d040740c1c078219200001c00c4200ca45640d502d160b49040143c1c0c40703004c00000d040031f101034007090400600e400d00b803a04001501c0000160740d2040e54005084030030503481c28400004070b1050641c0504000c02100c0140107a0424182e401d410500c16216403101c81c5000800c5030070007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 181927032 1250 181925782 181925803
    0xb2112070f060507050a0f031413030905030303011805100b0304020d110a030803190905030d090804090e06061f0f0f02030c010603060f0b011403060d03050c0d0527090402011101020c 80
    0x13080400d81500c1183d022800000c21f85590500b00895004032284d0704503110010820070a00341c007107000104051040104800030000941166140e503141c0912240300f00c11104407001c1030b4600000201000076030507001c012074400d449443e02d1500c5640030b2000a1002c2201903407204008401840c2c540c40e00f5196000a50155002c0c039101d0410011540a445400c0c5100305150705180d0b03984082040402120ba032039610341e000007501d44903803401091030302507903202e0340c0c04a1070100700101c1b00d0781c0402c0c510f10804040311029103414030700818125080101c0d41d0000050030f164a005582d900031a80c0088948150045908141d040482d00d800c0d28065007040710565107410424110441500a00c44200c1c3d0908158020a07080380d54001c5500004000600c90840380c5124814540107070103c0300340810b0700e07055540c85c0801d840064415030010340641c0000030b0540d42004031201d143c45d02013070402e00074080c110355141c9800449440c1030030912030712595800c005410400000f0000100d04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 181928282 1250 181927032 181927037
    0x80301080c0906030607450806010b04180504020a031202070503010b03070e0411040912030b0f0607050d030b0303160c08101e02030a021902010b2112070f060507 71
    0x258070720003072003008400901054080c1d4001020f10489039000304a0925408a641200848550244003081441040040110340d001c01880039626040d8503201201500c244000b02c0d842d590740c3e440302071500d10503441411000c06102c502e40360b41c840e441c0c001a40050000b441220500c0e143d48881c90314545028055015034440007080010741005c1c011401c054034118090140c4d40c0c41e00812180f2200f006000500103600d1707540c01c000640e29640000322640e00070808100207180c0000c064014049604001e200f5444042580c201e883c06504403908254454090011481844016406020001000c41d031502043c406000c81c1d0754140510303036005028000d44103074107260680d168100056503028546403800c003000c00e0f560040c503440004440603110380060380c0e0380d580c030603050007805002ca91f41521060580800c1090303505400a01801c5011111307211855003c02c0c46e00f81e4911814921000754009009880800b401400503008a03401503100c1c040c00742250340da40049800480e000c0d0301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 181929532 1250 181928282 181928293
    0x30a020d0f060602031804110a020a1b0b07080d0b060d0c030b181f0506040e0f13050c1c02060f2203030e090c1b100e030304150e0a08030108 62
    0x40419039001e104070300540850204003050a01800075140d2080300018a41d80205030310070842c0343c586c0c0d03100c0c494000c81c44540c151900801d610082d00d0b51025138050f01ca007122583c0c100030b03801000e00341e013017201e440c9480c0350301d00310450313641d94003030b03081444902d0f007880d032360b80b241901a103c0c070004010520301e205000455030380c40d0502400302d401844503140a4200c4074a2541d001c0041c0900b6900211802c41c0c10b0744103038401601d40c04401d06600241e801040200e40090129020b48405020316844008409540c3d40c0002c108000c025448002d03200c1e6000345041c0c61141048120007285803a00e01004901901640100350103a0081e14168814800041c40700c4407003007608000d840c0341c1c02201000400c07078039548004000c0341e401c401c10303442401054082869448194204e032140550800010104840b050300280c50311445a16020380608000007074000340d0011003100e10031540440036190024500c509000102400480c040d254454510200c002c103203031801540c02000b0700340081c40b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 181930782 1250 181929532 181929547
    0x3090406031407090b0f0f030f01020a0203250f0809012d0f05030c0d0b01110105090106030c05030d02060a0c0903021e1e091b0904061d010e16030e0a08030a02 70
    0xd03d03203c1240d10051459240003901d4080c0d90b40c0310020008404126543c9210090610009082000e068a45506036100003810f0200b140c010000e448200c2c54140c20414035985c0d03408203d1031510740d81c0f000f0b004c0606034060000207880c050143c0000310701031508810b0128501300180e660314805115030701e00c03076403808581c1c0407590181280340c21100030315141f070850410003001c0e0094001c0300038801030380b900c80f055601943d2050305412442c10100001b8051410001c00040c000c0040d40010703664074103500300120300b42c2400145401000d03201e600078140da0f910030b40160300800104000d0420000c00a80c0040560798014080c0f4010f00314a2140c440d4039040000c010191160f007021648280e42c19085016942d501c40b6240d0744440c0009060b200d540d491031501c81c007440b59042203588030385880c1c0c010401c18942c030020315a07490442c3c0c1e0300341d26076280e07485003080f040c04681c802c0041501ca101ca00c0c000d0310a40149843d03d044208171035504840d0355901c00e5640089900d01e0f003a69003c2100c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 181932032 1250 181930782 181930823
    0x309080d0504030b060f031203060d020a03080318031903050907031a01240f03091a0106090504140103050705150d1407020c010906020606011404091802030d0816030c020309040603 79
    0x5a0b0000400c4030b8008107000980003107072305c5039940c440e580400032002c8002192a00c900c80c040f400b4550080000504039100d2828449680080d14a031400100106604030003102c00006c88810300c5544080307007400085610100c01926005001803c580070314040000051720310b41c651100a041100303030001c50f40c18100100c80540d00004071064041e03c0030582081d550b08492003101d43c030803600d004590800305003480f9190700c0b1031040c010b0b4102c44040c000102281d2002c050402c2e964110340231720034502c103420010409202030102810315007150208128500d095103a00090b421031800c107a0610306281040300846a60a80c0ea03010382ea1740408000400340d0502040c0b061080034200800900d080000081d56040300918190500001860100a110b0140203850081011201c01d00504080660000c03402d040980c0c100d020f885039040b61240704e40a468220302c1100082d0001305107400d406c004501601703a9480c507509501003041001890b13140c0d401144007441c00f60204003189190541074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 181933282 1250 181932032 181932053
    0x1c050a0501060302150a05040303270902030118140a05130812060f01081b0310090203010308120c160f06020702030a0b01080609160306110405060d0504060b040216020405040309080d050403 83
    0x28600c0817081004498035040e0881d007030364182c0b600351408010b900301c403000414112200e4810135100000d40100080c030115503800950580c0c01c4034030761080c59a8000101829640748003206070422101d0000aa034196141c1d200300d41c04103130f0941c0d11355040503907207407945680e01c5154810160a1840d08016407420710280407500c1c1c2900b0301c0d044003c1d10384041c901e031402c0c2c48140c0380c008019002020440c0c451040044034050203100c1000c55136540d4a2403c10401da01c10010b50209034002070002c0d41242003802a1079400e0078185241c05030113140c0d0b840d9000c04042c0c400403103030306509109100243e2420040c802c84203210b2002c01e0303015418000c500d854918001c1c00070310300f42d00c80c00b40704980000203541d240c11a0b0340140041401d08030385414012034007440d00030300d03044603020511440c580e0030781d0862400f8a003e108104200032901d010300c0242e03c01d800d1203105001003d9035076001401d040e0b0083e40d200f4081d250a06055803101c04e0a400c12401800800c0010f002050138000d20250101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 181934532 1250 181933282 181933309
    0x807080706080f070309021306080708190305070b07120908090909071406031312050a12020304082a03030a020a17010f0e04080f07200102010b0f1c050a0501060302 72
    0x30b000b0002e1030051503401d0103400041001e020191200c1e1000c04648452203642c4905203003c10a11400d91540502d960b034103030314410b424180c4140440b000c90700007151015000550595500791801100b502d40f120040c07400380140f010001c0c600c6440d461080c0501c141310446102d17203001c3d0b40d103c4142c400c110051328003502c41100768101703040c10048008408012139403850296a11f60710780d0b071003403180c8031986200c82d406421009110306102d585580320000b00000e02450b00c5021148032544010b00481c0022280107001c0c10b13080264070840c40c14040b00c0c068000d11a80c40400190081c5111810f540040d00e59000e8950003141840c40c07503400c151200001c3e1900000c0e1840d641c0340c207030f244810b86043d00c2051001e911080114090182d0710007250b05001c841441141c0e10070a5240c1040c10052200c01ca500390305503140c1124a540c818000c105600900908110649100308100264004d65200401000d035070b00d116600000c006004d60b001f5140101c000051180ca14013f02000000c80070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 181935782 1250 181934532 181934537
    0xb010e040b0a0512010b03030304060606021204030302060f2a1c0504080f0307020703061b080a0c020601140118091409060403021002031e04060911150418060b03010807080706 77
    0x203094155894002404040f40d80031070780900102030b454040350040502c035914a0b050301000042000b84071181d04500d04540155085540c0208080c00200040c0a0782c00000c6c01a0004000b02d0381d013000010090750454044809100d000815000c903c0c51025500c0103280000d4020410240c46019072907241e051414401061159150a5461500c18400d1505403100501d0200100e403059108111070806107503c41c02c01c000c0303000342094035462a1540c00e000c80c00111501c00180348503500b8042c03c01c0301c8940e81c009022a03400c015201c140c20824188040c10050f0203421500342e03c20211150004007500100040c40c2d2046040c40504808014400010340d40200700703000000c0da0009200041c078103101001a01c1e81c0300e60020a0340e4a0202c00340c40010620301c001c1c030041c09401da01440007188542c041c401c282c40c098041c8481c1c0240c11400456024081c00708000360441c5842101e24058001c07400a41c040d100c2c1c1900359075800a0300a60015032003200140814482044030601900320350 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 181937032 1250 181935782 181935791
    0xc060a0f110f0708040503030c100b0d050a030e032103011503050f0411030705090a1a0a050a0902030a06050d0f11012f07030b180111130611030c030a030b010e04 71
    0x145051041c403a004511a1400b00002c80c00c062121070016a0701401c001801c0d00e076549035130390340c2c5941c5840300201488a2031414000300c034249800304058001550000181100e00140e4509440c18007400c602560140104988100303604407500740e480c1d00c0100c0c10311558603941081070204006030213200c4c0c0c100303151511007800f005014001e00e042c1d009910401d90114460080701107824040f01794400c40d00410020240a40381d80d0f960440c1020040704074410444488200800204694610070f036070700700381090002c0c0311444d02a0000d580c481c5a440740460450780d0f03a030101c3c1e854160010261184140c6590400421180d2482c10840202c240f80000d03e000c110041810306c444104e030415080e4181d41c04002c04001e040c030280000b1a00f2407002540c52034200d156940140000e0111100355190003105102c0300140c6080e60040c20515041668150034201d055403081d031203440340e00032844280f1201800c2c203400c0004140c4a80156400b041e0200c0800014051318800700c5440e00c240d040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 181938282 1250 181937032 181937051
    0x150604062003120c13080105010b030f060f0a14010203070f0803190606050d0b03010902130506120601080a080c150705070b01050607052a0a090203040212160e0c0f0c060a0f 76
    0x3c00e41c00503000b0300409081c03a038031000c60100e084c60a082e58001400c650030a0000908088102c0146101704040981510310b03640b15020401e50860400d407142c0d0000c0702c0e01080c4688110507400004400040c0101c902d809a652641e04005215550440b12100e002041154005000340070041c0306082c540c0a201c6942042c1c0007410f00c0c003a044424080554540c1e001d022640c00350046404250040c0030740d05d00d0100c005240d005803d085400500840a81209240c0036000041c3c0034101c407811805054005034030b60310b00351640e22030031050b5103a100d0450150001144100704c903001e0103042d202d1a5442c00c00d413410f010003083c164080e520514003402800040341022440c001d0011611032a030400c12171039865031615891640305d4a07003201c1c42942c00700c1d04000c81d41c01503004038022a03051501e982214010303513646d2071505547c1010b14080d0820003035042c01c003032030700d82105002c4031541c1001c0d16040035014507081445604150380c0a8030910008002610507039000300403001040c400c640ea07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 181939532 1250 181938282 181938307
    0x30818100504120503090a020609062205040c0c050307020d050304180203060a05010905031f0e0717060109020a12050601090510030906050c160305090609030a0f050d0c110108150604062003 83
    0x90b0000068049c0394001000201a41c0b0b61003120f010361f01904d0b00c03120080400059034019004e6010325400346180001c40c2c070040b400b5000112030258018011803401c1019801c1c48030300640103000303ca0300d2005220103e0b0503040e00f000d951000340400030060703c03854020100510150780380e009a060280441c000e00c0961004210500612500400710f004104c5559000b001019022444191402207010100d80c0c999900c840c4070200e50440c0441c2c1c210f90b22080341004038442c80540a010414102e010488220160462984404141070102c4119924070105003034020f507100e000f0002c0d44c0c419141080040c64843c80c0e800c1490440441d0905800c0000c3c03183c031316a5020060203210001c030b1b400d02160355900440350300300006000d0f20342032240741c5044c580700e40000718101d849028030701000c03c109200d02030651100d0342158441810038140d50054903a070902034006e1807070b82101180f074981512290000c10080c0310356036504212400c584107030140303591034a0300c440c4140c2042045020012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 181940782 1250 181939532 181939543
    0xf030a200a08040515090c040f0606051b0a050106090605040e0c060d02160c080105160305040804030b0705070b0c0a11150117070806010f170d020a03081810050412050309 75
    0x1076814002010703103d0341851031400074401101c180c03031500441040480c1c080407441d0000560240c03024049620900340c0d0307000340e032801d001e10310000e04180001e100440b03401401c810300300071210550f03090350120340740e060940c0c10a800c8900343e2501c45204200b1800d0500c40c0d80e01c00c821900103008002e81e102c001032264450102e03c00030327494003c5000c2034400740c000c03052010700c0c1d400140d044201c1d90350159a03000c0c0c4000c0710150803449502b10b0b00c40b1070300d0080c002c091040b030340403a0b5640f60900b950758400d110013025000c4800c01c5014045880040c6282078083d0184030107440058861b03404000003801840b205034910610f800c058060b99201e5004a84541524021092070302c0d43c88001075403034a0324580c1e601154051003a400001600102045424152070100c084141c1e80140603540703035a603501a0403c0f90040c4c0c440d000100100748030303c0a55800c010183c050001e41c0168000f85490250310781907002e0000d66890602003088810641c40c6250b1a0b1802c05504504c0e000c3e50958440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 181942032 1250 181940782 181940797
    0xf07050405090102040504050103061a1509010503100902032e0f05040e0f240f070f080702120d0203060405010e01030b070f03092a050306220c0306020f030a20 70
    0x1141c941e0042451800d081d01642c010704009170041103d5a52420207001400d0100c801c02d001c1e07a0403050507900790904d00403421507040c940e1441303441c0107902401160300c2d6000604009010074020340104e40050240002c5010f4900001d00b52401354521203009046d010110302c400b041d4004100800006e8010201c0104a503c201c500107449402000c40e50308243c103256280060b40038004011424400a1503e040e13072503203000c0c42c84540d035240b200c03005603190166948000f25003880140c9135024805c0b0155036101d142032060301c090141e66011400305400c440518116560040704014031414248078850040004006200595240d40c0b620039403800e01801250810000a040c010f5a070302075000130b03061030b82c800300901c030310200a0704600d03040d10f1800c02101120b10403100062146400a821030140301d0f01c100490130440744529100401503c504111100304495200101051551010f01006000389040c2992131400380d41c080100c840113551141d128100f085009290b03060002500c106 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 181943282 1250 181942032 181942039
    0x203011a07020a080304032306250306051c17030112030c1e0f0201020c1f2001020304030302120c070f030f0c120e0111011a060913050109020301060f020f0705 70
    0x8030481800418800002130300840101d2000141c0081002179001d007907481c00840d200710718105961040b00325118142074410403540c8110012502c0c8102a10070200d0078516103080010b000b9a0f98804240d540d60440b00090a003c013101e1514140701c1c81110381507410b90743c460700314595030600c003103141a40d40f0500003504011181140e04100801d1114105800020841c2c0c50b4402496107043c3c0300e1040c015400302d005004050010a041c140b000e51a580260300080d040d1108008040c2100c500901c1c05c042000310b0b240101014a8800a01c0114021402980d0145c4d17030700c1c2c0020110400e0f0701d001c1c01031200e15401300001c0021494000c0004d40d4a54546000203120400000883c1c00c00e00024006d044012000c0c40c81107415001104111a0b200c00e8a0300c1201c404000d060394200d03088440340303552161500c4684d1109180c208020004039000a010030300c4020829800d07000c80f46c007600585001c0d6400001400502c0d0001c000c0048032600d48010410105102e6a482d01c512441c07040f50301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 181944532 1250 181943282 181943287
    0x3160806040b180709090213230901090b040b0403030b060307050d051005030328110304030f0302010e100c0207090507052a0f100f0b0a0608040507090606020f0106090203011a 77
    0x3026107114140c0a100f000e000484038026110b125400c020444003004912034a0300185141c004561800340744105038141c0c00c001c021b4480d03d0910300100300c0080014000d07560710345807680015200390446016500a00500c40285090f103800390407128144a6a446992b017441003010155204048919000840c20003150607290781005080c62542c0d9081507030300d8040820f098004440c81d0095943c3c02100c2d109048595040c90b800f92241031918441e4405a08100400d0011030342c2c2c1011141068442c0c0300000303110041242c19810880540403881d241602c50b4002101154100a410046d00d400700c41084a030801c0360026050344500b120103010054101c2405907042820f180500f070601c1014241c3e94949441407800380c507101c16015190401d4545240c1443c4003c907841206040304000d4008180315040c00000c0d03d1258008208440d240721710500484d40b00003d01842e03008003100e80052003141030300024542900d03d16009110590310520040001d242c0140c00c42c00c12126034061290f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 181945782 1250 181944532 181944541
    0x5010e0412030c0c02150720060405010c0c03020603100e0c090904020154050901030b040c080304180b0d0b07120603120f0f02190227041103160806040b 67
    0x100e6034041341201035400b080380c2210444590030346008241081c8600308100001c40c0405252041c4a0001c400b603402c000c09204c1400154062410404124003c2d107036240000d03600e600081c804d0380f0454110020b10247d5030200191108802c0307135500190200740c86130400400c10041003e840e0020b0000c0e04020500b801040c081c0000c0c2c1d04261000d024428a4a0711580030380055000f0551074010300062600d1181c054003412541045025540c004010703041c6a441d54640c1002d150002c6c0090341c0c000707890716000805074001c20003000240401044d800511040c4000c00b42150000b40a1600540b181d802c5840010841d1100f00d500c00040d090441c40d0141c0780340720f04000c200b160802070a0080b00f507000704c115a08000241c1c0500500e82e40e00300800e034412030407600d65101507102004410b4140c0c5990040ca050b244620756060400143c10500300c20045a4014140603a4260313082045040c40da101402c0c01d000303680708a00e402c03858800e201d00c2c00300d170196034040041007e8500002d074000705 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 181947032 1250 181945782 181945787
    0x51c02070807080703023d1817060703020327010522020d0611090307030f020909030703170a020904090303050604061e09020a050c0f0309040f0b061c2d05010e0412030c 74
    0x1c1d00008448082417482c000700346024103408008400042310301d0202c280059105d890120f110180c41036003020301607a490ba440141c019400240c19440400d414000d210201c2d2100041150625804d00c000300726802c0c040d60003884440c1c01306032409007940308140b18015840da05402c2c3c500c10751015002880a603c08224100d600542d801c640d07042c0201080042800f40454203034041c580211303186401511508034240d600e1203000002000f09082c808882a8800780824055021400300009450301c244030300024111344010801f1008296207409106213400c0a01c01e08000d00100c185940c26000c20004595243c1c5441c803e2866050b0000b804909a500c14020364114001c3d000450f207a40d1451000c05840e900070042c2107004619018400c00d40d054540200207a0f000043e2920340741886000ca21105201c800000005a503254170011907090010b056840b40c1150b455048180d0451441c2c120701a03034010791001c07005d000c00c03200340700c041100d0040010003204a03050014a01c041c10005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 181948282 1250 181947032 181947109
    0xc12100506070f05010c030b01120c170a02131e120f020301051015030c14030405120c0309040f020703050405190f0605030403020618030313051c0207080708070302 72
    0x541e00090041100c0040042078140c5200403480740b4002c3c4040c90204000710100c48040380d000e4001403400d092064402a0345d400800300f11003510341480c1d9004104c43e021030110050b50410a542e50006109440400008011015001416012003411001000c1c2103054483c0d00034000320b80140e020364030401c008441c1407072200754058001e0005160540d128075210300103200b0702880007003a5000e101c041d0710901c02c20002c604c0c3d944540e43c039100b50191036049900003c0084070b041c46481d641d0740003c42c203074024014001c2020000e542e94040801480165a40c0b103140c02c006a00500c5414000790304141528290303401507030104544541c541d5080c0c1980312640c4030054141c06800302081041c2d0142c000e5110340d00a40842e0100e403184507148407041c009030134241c0b00b0307002800440d0703107420284c094504503030080d0111101213121440400d5040907124142d00542d0000d802000140c100303105c510018555035018011462030354010414501e209010310440c0b500c003044200c0c50600c00c822 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 181949532 1250 181948282 181948289
    0xa05131a030f0102040f0f0b0d1a040504050105010510020f070b21010b09010e030c03120c03040816030209010e01080a020607020127030c090204030f0b091c02060118050c1210 77
    0x21104521000d1802e40d000b07600c039000308008030a180d10b0101c3c0b0401700402000c00c5600c0028040d14005405151030001c2900b020882c01c07641500b4050a1550741c1e07030080c5401a80100000600d035450001084100c4a6143e10003003550000c001e034030017812022640b2030444025100156642940a02c400d5421501c00301804c100605a80041240c20303802020b045a80002e0700d40c030841c0760512007019940c61644052541c5035206010b98960402a5009481103010705000c076400c7c1500c03046510304250b910b07042848034a80d0081c1c00c1080d450300820b010700400006010204650600f01d00f2510342c0da107944044e004d42800030b0b031042164071031910001c81e072a03e10780d0126403800c3c0709001d4a81c00c41500c400c0d02d043c022804003240061091080fa4100c07544182c14140d080700ca65034070b442d016402025895280542d103030302038000000c9040000e000b01c455004e4103040d810300d04400c0c0c640307151405c41e003401780ca824100603001c600402101c03c0e0000307030408026075980d841c1c07081c5002e024540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 181950782 1250 181949532 181949539
    0x15140310090c12050d02060a020414040b0a050a1211090603060114151603030f050606121807031211070b0d0911100c03020c030606091902160b150a05131a 68
    0x340b083c00e01101043e181a80022582907980a403a18070000c0c09a0186025101244640c80d10300300c0b20f850954401c000c0000c0103030502d50340310ba07920f00040c1d6180107640100c603190104500b100402c544a105110080c0c0c04a4184a0504110000c02e035991014051250310420101c2c84000c282e48403070011240d01c159541203983d60740301e4013005005000400c0d0813408241400618103c080d0b050003071a00ca41000781c411402c2c000b81c4110540740002c054036541c0740140300c0401d01044003050203900045c0d40500380440101542210017400b0100d1010600b10a40080c40c0c0ad01c040002613086501086600c80d0200340300407141802c1101030785004032a40c1c82138120078000301a40d04001103801241c06a0280c80c042c074070100074544c80309811580d4542c00520040007441e2000c8080c0c01c00d45680000100504082c40395036500d280c04001c0b00140e03901c800e1074041050031807040d882e0040c1c0c0032050b42d01c0007100340352101103011940307080f4460500c540c5610011aa07181061100d28840c2c1004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 181952032 1250 181950782 181950809
    0x50c0a0203061006081303020c01050d0612050a030909020405030304090c030e1501080d030b0603060d0c0f06051905071a070c020a090c0f020706090b0703090e0a15140310090c 77
    0x42c1e0f5600c0d1442d45105840110f0141c2c0009002030361002c081d8444d00341c040e0040c3c031090340400e004480580c401d2804030003095891102007100030381c3e20010f420b0740c1d12400040c4000d80f001c0c1806802900c01d548103020305401003200340714545012059500302c03840c0c102c0c00b0455a58079803041c0c019158861b4a007500d44500d89103044103400c401d02e00c504880600060743c4010030b54000840513151040f080720f4200c0d84c00c2001c908681441199400100d0152902c03010b065220480e46d1203402c040e900032000600c000c00c0c030380000007202c0301104080c400f50611034a0b11903a5a100d0080000c49c1541040b4a013000b40003d403000e0069051555403a401050000000c1d01d17150040000c0100110500005000d020004c00e55800000c904082d07540c0c40e00d030307034400e81e1903c2d0b110f9402c0c1d44800011000c2000d00c6800013203900b40c80489a0240c1c0304441c0c042040d00c6164441d01c403031a4540d00c60066206000031070f80d4a0345001c03414420185200101240400036800d0034017505540c2e501145250418 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 181953282 1250 181952032 181952041
    0xc091a120a140c010e12120a0206040c05090405100b060c0d02011e060302060d1e06080a060c050a0e0f060c0f0303100e061018051c0204050a051303050c0a020306 71
    0x81040100e0303a1082036040b040712a80a011691007001c80110b074041a142e026075103451802c46001c40b4141800000c0b00c283c00b40c504c115004c9500203c80000c0940e04c028244010000000500340107404282c8600c40740c1e04d01070711410356400e1444d07070b1165240d6544500c610382c0c1e07c8440484801800500489007201c00c1c12000900030a09852000c0340c99003004140340400d2681d025030000c49800030000c904004a4828040042c09404108010384412403024140d00485005d194001d0500001034000010780d030800100341c0c0c0c00c1000e00c1040050405c1030000c0d543c0c00c90075040742903105841004a400c9543c002c02c20620800800300694880d5610f001c02c030400000086100d01c421007100024596034002e450304014003500c02d0b903400424501d02c1c10301203218240c9881035030310401038003100c41c0d40d81010520701c07424a50a860510004004101507052030300966401008540041103d8a403100d010984001c0034400201040030025440300028402c010740290590004c0507034045003003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 181954532 1250 181953282 181953319
    0x30801140109091b03050109020c061902091008010314060c040618030f0602043803040f0b190e06150d0c0e0a0203070e0303070c0501080612010f0204210c091a 70
    0x1284c5040c00c0c0000d05100010843c1c180d07a000f550078210041c40103100a032100b10800143d0180c031880354110b240d0038441134506641d5003e04c1d07403011440342c503960019415400c040c140132130f101c465800d0680c4214180b100405041e01140e040b15154030b06032103002038080080c111c0c1305040d403002d414103844c3c02090b0f05101446d801001182c0110707080c600021030714020302140c84070745010030303455004101140101005030801954014480c03a840466000c40750f503910200302c070544200e03024007000300c01d0074101c050b28170844624a040380b0040900f8904001c0002085407105041802001c41301a004104491026044003602c55440035100a01d050b19010f8020b4004450910000e2808404100075090201c2240d000980081a01c00100d007000010340b09002d0140481d034019082c45440b141011084c0b0444941000c0340c60050781d100e00d40129400b091f00130350000f01100c610b1068174000115030440503000c64684040102c4c88491140e071144031a030100042d96003000722110340c2c07910f806 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 181955782 1250 181954532 181954571
    0x80f130201140f1e180a060e041d0303090f0106060309020f060c01060e07020a050c01080606030402040b12150a0b030601152102040b07061104080a030507080c1903080604020703080114010909 84
    0x240901905c54821400d94204800390314181300300c50101d00c080302c881e40d003404c0035000560318030780351070980e805c03205964041459980100d46000c92a005040021141d45c020300404000708034a1400b031260030a50f800150040c074100745005d100e0703440050001807805007900407400500c0d0b403071840c1c3d42a2406100c0030b9142c081081303040720301e8024004280013135070058003020301804010700040d0440da9507038248002040c100d5129540300e43c00058005500c001042104400c051544504140382001000c210503107a405501511a0b00300c440148400e2508404550b400d80161030300981d05120040d2851a203452040f184003510300000380800c502e0f001c10014001e9502c544020812004024200300190003680074039911a0803050100c00032900c2075000c0e100050082c0d82c3c1e00d1404483c500002d00c1c150899450400103511701041605040c0c00c00c1e0103d501441c02d841c00e618103801a81d000300454814003a10300210102d09820703a040e4800d6030410050b043c0c00030300b005400c0700c0880170303542c44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 181957032 1250 181955782 181955797
    0x901050102032a0d11121309020901030b09010b0d0b0312121003020d0606030b06010305010803040b0703020709050a0e0d080c07060e0c0405040309180608070b0906070c06080f130201140f1e 83
    0xb4410440030941c45c5581c40101c2d07d800001d401c0d50705904d4100080d41010750300001800741051b03101c0400705125514003001e01d000300490010903030782d0b0b0100141d81055508114410384681c0001e00c071090900003840c110703410032040c5082d05d06d940e510600d000841078001e42000c6e4101e0000d199070000c000103070340b040041d640503010311411035840c9401101915024015048103800c1070008118001c0c003400a0290280700b40103954500d41c40303c07101401c0301c070308550341520b47c0e80303035100034840c03041c02e0024400c00c10f1146070201e400c1c40c140d0250740c05440380c40c50003050695030720445c0c240c105062240f4110750500802c117200d03a00309401c0c010012100303405654100450348900160703280390381c81950100c0e854640034003601880c0074410a03098120704003c4c1e07001b040030882c0c04000b581e08038015010342010384404090b03042200a101c00d520009102000f1011480b2081026070782142410503003140844245980b0b00314030121001601800a411a055000c1d1410003220507401e0050440c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 181958282 1250 181957032 181957067
    0x51c061413090c06110f010f0c030e030a0e0d020406050907020a06060605161103030c03130614090603191e061403120d0c020a0f060207060b0901050102032a0d 70
    0x10718554951400c11202181c03802001030316040c07010404640141c009150014800054846080d0341308020782c2501e0071085012444c035501e4020b000786076010b200e2150b5494402000f1070804040403000740c40b012032a17442c02e220320304100b5000308541c3c40d0703003182000c0c04018040d0500740c2003400c0003070340d50040204121205420240d0100303a051261040d01c1c160900103410805030403d5403a400c0c591450240d00380c6c0c241c0420001c500c43e1820800090504880000444520900d808001002c00714201c141c020410020081c00c4c605990b04010350b80c0041681d401d00d42c00b120380c841000011f21480c5604085412609861038100c0c000c0c0d449401124a1010041496085d03102019250443c07075038203101580f824040a01c2d962001ea10022010001c0d004072100c1407034948800d210001d01c400126511070300001d424080101034003500040711019034280744954100320000c0c0d224012010101c902c003211903540c01950709134451101407954048262209038a14a200418094802480c00300b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 181959532 1250 181958282 181958299
    0x9030a06090f020f010816030e0a05061f05010503130615091d060f090604030c0c030506010e15010f1b150603080703110f060705210c0306010f0e03060403051c0614 72
    0x154046c0c91414410042070081c0c400d5a4a0303c3d00507002085038491548a17403155405900018404001460186e1400c7e41a01c7c1030035402c401c90f501c0c07454107802c010304001c03050090044c010b80d29190700d4900c40c2c3c000004136450180104050300809540d04c07801109045c4a04a14000701811a0070700303009011069510b02c3d603c510350f0010004040e150040c03590b02940c00540842d200d4000c0c040c180e4400c46044880310343d69200e0a1410f50300382c002e07200e5012844180070518a45000b01248030a003800d16070050800c05030003030004042280070030b102c035414a0b00c031030402100000e0203445194107082000707203545a081c10302ea10782003940c00300c0204207a54549141910005160305400540c0d4004082603680d03030b80102e9440e00300001112508803880240040e40c4031075402c0d94860a1240c4640b5120710f8003400040a604107a41c5030000d011540d0300000d07640e03d020804a50158140c00d2990313480303003a295040b56075424246000e1015140503004103a00844030320045550101700c400c5034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 181960782 1250 181959532 181959559
    0x150501030603020d02040b01140a020309040b0117240402160209010b070809041d03070f030f032304050c0d0623010509040605100f06050306040c030b090c09030a06090f02 75
    0x604403203032800041d41c03003101340070f6810040c40c0981000c50901341c1132402594824000c510b102c0c6a40000c40b0700e00160b00082031410190903e1300c109554442d0910f448202101e60b00d41281060102403b1443c55421040e070b8500345c004007a414540c60b110180003155920003800a0320110388a01e081248501440000040c256001600740c8401035049110b03603150003207090420004002c95107040340c0d000e45003091200300c0d05042c4041c059450003003c412043c8080c030f1500a00000d9400f48100900d440c100c8011412a401c545103103400500c030140e6400c0b612242000e51a041240c0003c681c40b03108108800f040003a580c111507401d0361080c1221411144005110b00c46207024018660004624070009001c1043c6401264014080249800301c3c1902e4100d030494803412500250007088001040c4407840c10507118a54186070035207020008041160005400039002910043c018880850764100c9030f5424031032001b078a50700a100b0040e1a046192040e6141050902039104021900c42c40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 181962032 1250 181960782 181960787
    0x60b13150c02222007060c050310030318080304060203040f052b060906050703020a0e0603060306180f030301061d030706021e070b0403030c0b01090b0603010302060c0c13150501 78
    0x1e8507074010031900b070060354201c0594030145140c1503440210f07103450f2000012141000c2252140007001a56503540b210b50625009a0300c001242c0c50030448108204144004070441e80e0090780e5040c603000344a0212040900c102e003c0030b030040c0c01280400900040c40b103070000300034802c982421402582255941c3d0070001020211108004521402e50092940c840c0244170403140a1140034006034042e0325480b12000ca40d011244600880e80c0001c4511045803c030302c0c411036240045a44501d94038011005c40c0c0c4958010385031400a4914407a09003550405008290407008144203e98a175a5251001000162164480d0030004c0120390542c1c690f0070017090b19801d44445800030058003004200e04800c514018407008140d010703005010540118000003440150b00a1343d81c01c898640c60f0424814840042c0c0c404440c0c40e1a145800440b40c0b105030a4a045a4048500685440c070900c03410341031513005200741e640080c0102500c8182c04140d0302040015250100c1c0101c1646c0f903c006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 181963282 1250 181962032 181962047
    0x2190b04060b0d06060b1c06030c050103020a21091203020c061f0302040f060f0806010e06061312031701080309010c060902060702091317071a0a060b1315 68
    0x50060080500000c0214003a07800901180c903020305040e488036072030303210a0100c031002d420611030000006904040d02c404d602c04c1c0c182000700d03058100000f6141d9035542c0c04c14403403032298a0526801107400171600703008000041c3d203c0c0380d400302040b6021092a0400c024040c6110440d2a00c20103041c1810035442482512001d01c2c0da440106255100d5150681e00070140104082034504003020100042c2ca0714014010501c4507c64040350a50a11111003d07545013904240d0140c0c1c0410010020034400001441d04013070180c60b095a41c41c0b20b803411092900d61038104419204000400c00205603014010b0384411003800504a090b03604c6a480d603403607215004109000542225035000401c080f94060f4142910081010745420701d43d0b404108190001c942c3c0d42c41c40045540d15406202e44410303001c0120346c0c006892071130022559a0502e0411040c0301030903041480000042400c005544081d010b01426085551146140e0003030078007002450040316100d08000ca010791000f800b800c40d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 181964532 1250 181963282 181963333
    0x315090b011205030a0e0604090f020d0f09021509060d1a031501061403060303120c0403050f0601060504060c11060c0f0115080304030f051c0903030831050304030614010602 76
    0x514076008038061700700c0b469266545103590000081000140300c44003840382007004a589400540c840c042290000125110b900c84662254180341490006a8a0001c50690080d05802c1c89440d00030420102d003050280d4a0928070f03152500301c84103020005040d210100c100201c04481c2d220310380e0500c404036250300788100e90220740910080c600000013070002e582d003d500542100d040504c200c0701c01c803848006865031054284009001e1003440014802e180031203101030014a0346502d0698000c041e4400ca1047d801040f01c1c011409040140340340c100c0c0213070b54008140c1910ba01c6c014401540310f084529002110758a0300300c04801600403000c110041f83c05840196040c44e140d82c80c8c1e45008160b690f000c40e41809803542d503040c0161780e403481207603554003640d400c0700d0345040d451f01921041000e4142102d0603907500800300b1240301c0c15002d01540c1d02c00e0400d070141c0c08051411500d14083ca0b00021300701402c055126000122181b0b0340c904880c207030743c04c46d80c040701c1e13030320802084003185603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 181965782 1250 181964532 181964543
    0x6092604090903020f01060f030311151305010f060b0a0e09040f020d0510060e19140601030c050403052a0109030b150117090d020f010b010215060402040315090b0112 73
    0x11040012032459031009010b03070f0182c01580c0c4a03c41c004070803800c4448642001402c01c40125041c002c1c5940030641c00c00d00740c0795000805820b01214039401040310000c04030350340358100c804540100082074020400010144200b4006c458031040761080e680c21100d81c010024540d004030103910318002c0d40d414080d03a017100300c01504008540a00070000f00c1d0f828203a1f283c0c81290b660680c0b00e6003d01c9070364024281150400c089040c40040c001c503038841c4207c01c1c1003990a042d484055410304100c003580244090800107100f4540000a07a01c5008030ba00281080c0a8101d07209115050030382c500d000880c010342c20140300c55010300151580c0c81d15000190883d1014000112000c030306c1d42440c0c400c8a0141004082026454801380c00c25001300c44030382d0150481c04400c0c24058041089600d40c9500c0e80003403180d13104280000790740340403d103d840c181c540c40c3c03008910b40d030320345504a5001d035030044010040d5186180070040034081e0b01900725021500403000080000d121100c0c4105c807035000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 181967032 1250 181965782 181965787
    0x5160b0a051f0504050417070308040605070c02011707110d020606030f0f0a06020d1509020c0c0103051315021204051c08010501090b3609090d140d021303060926 71
    0x1e00b400010030000300219580c40107d0781e0f1501d400c2d004000340008034401c3e502e401440c54645010001d642005c2c11070420b0145e2074100e840181e0b00500c0460184603000e00402c2c990340d601c0030444003030b00302c0941140346018210844000799070104440f446600154122110300004100060b40c8900b040c800180d10b030005181000061215002801c80100174900402e0b10b42540c0d0301c540d5034000960103080d00c150b00142c0003001c20024031100391850000d080070405487c0440039a4900300000d000100b40e22642c62080300201216810794141c05500003d00354a49030910b0325540c0c545540b10050300200382100c01210952192099038140c4406035281c1c0d04040c900030402011ba040505501001056116000c5000401507103e0129858032144124901c402c8021310000c440040c10500743d03070b0001044c03840c40ca508000c40442800c01e00340584d0b0740e0000480884001e01403058500c0007c0030140002041c4102604407400c800c0c0a1400c0e038201030b412041d400111142c441000a04c62000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 181968282 1250 181967032 181967039
    0x90903040620031c06031e0b0106030f061d1b0306010212070203011404061a03030414013c1d010905060d0906090803010602010501060503220305160b0a051f 69
    0x10000c94954541c090b81c21641080b502c0c500c51030744842d010010b803500799540c6008005010b003015034500044412a86030016124030340f96403000d081c0500600d82030680310b280c608140060b07940044c0092906040c844425120703040b4000058030195200500c59800000707019020114100312802204143c0007494a00440c060307120b45500a000140c0c1d040d5605c520304480840c982c5201c500c590b10402000030301c2c509042020001c5045000640c0c000d40c001c0c8024030030b0642801d1444c14800090030102a04000c040312180841c01407606034045120b80200a90540300d181241c0c000f81d8004d46920500501480c00161001c00054003680002c64895007008035041000060840c100810700c00f080c04080e5403030324000e4420041d82141c000720000010000a03030f086c8180340c050200d514229242d4107001c00d00f0f0400c240305070746003920031600811100415004008482c0b1015901d0300c6400c007010142443c100e00303c422100002541d040030300040c664500e0380b03154688448808a0700304000d04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 181969532 1250 181968282 181968317
    0x803180c1225150c020a090b090604050406020c0d0c111e040f0608030c0a02330901050405091e220b0a061205061f0b07021012020c0a020909030406 65
    0x406500c2000580c80910300407072140d03c000640704081d0103503290000d903942c0320300c107011100036154002a46180751012407002075a65400e130f1034001e40c4c12a80440c40d5111810b00200034460704480f00fa031031142001140503150841682c0c0c01c3c0c1405400c20180c0c56180d44240089030510040381c4400703010300c0c15020140d00c0c0c08c1e80030806591110000049494480d801b13540786034428000720480d17901c5006190110f16001c200c20410100300e8080344942d240d4440703102c041041c107142012821341b0205411103580d100f13200355402802d00400700e00c00c1d0305054182170018000322100340a070f80340810028200e01d0400800c0d8030b00381c442ea441d851411100c2c0c3c5907121589806010100321903150007001510216401c04c005d1018011070207003200d402d040a03080c3c60402c0c100003024455003006400c10420ba0314038280c1d64503540648050f1451840d91600700c901300c240c607107980e034854804648018007040015121041910030340d1107454a4480041c1203035203004078443c60002031070001c0140e00111 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 181970782 1250 181969532 181969573
    0x1e02130608010e0103151a04050106050903010509030406020706260106110615030616090308070302161202010504090209040b1305090c010509030d030b030307051507030c0c030c03080709030803180c12 88
    0x24044929140b46102c000003c041c2c4400783c0c0710700d0001d0000b1a0dc0c1000e4902881401d17040350b00b00000350301d030901e04078010351600b940d031041e80103020701480b0380340178100e10350034421b552402c00e0f880341d1180d030310303464041c01a041029511405128580c00503803c122000c0c0d18443c030900080003400e1a644080826000444a160303000420203004030010000f0078580140400070b211340c02408200c2000d00c3c00700f41e40b403010340c40503107443d065155003005030b6000001c0341c090b202c2d11900540c5e2010001d0115010344402c03425140c001c418064000401c104517400180180002c400b41c421405c070b0003004458600074100000e03459040010340b005001e0007640801202c0c103019041c1e030b0510060380c80b01e0303081c48050040350499400c0d500c100840d044e8075114a9a064280307040c00048224150cc005010f40d01160300107003444403c402061105001d000042d0040d54440e102d00d949140c2200749000d00443da42074030043e8402c0800d1f800da00d2601d80e8050041e2032110004000851080c5040c44c3c088 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 181972032 1250 181970782 181970801
    0x611030c0a14030412051005061005070f2a0906080c0a05040e01090f030306030201170412080907080a0c030c062a08070c06030c021006060f031e02130608010e010315 73
    0x10302c0101300000308200500603c0710b00034046c201800c0848201d4052205450006107054800c0303006099404a494208091300d26030b0b030f00041031078001c85241c0342c080e90040c1e10315100c40c405d0076410a04825450482101d0081e40c511050078004140c0d1401c48542e110b40c805011940300c0441a002c1c0123500b000e070322412081da0b19500104841c07516881c1c0510060303001800341c000a403286418025940c0050812040750b0741d040e02030045140c90380310300783e00300c824607030140030810f1201c08110047e000b08588806040c0080580301d04c50039914104480d580c41d444101d8800250400c0003a6450141544a07480400c0c100310b80341200d140f01903510391002c410030444960304107108040200f82d141c142000505815280002c0102034140d0103880d20b800c0b2000c085070a0b08000040c40500e030310140701000302c035247c200414480c0c2da000444562017501e2804155007071000c642042c003000000d00c0d990894000e0f031180d2680381d07260704050001c600240405040c6040a52003280c2c051403542c80360002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 181973282 1250 181972032 181972073
    0x50709121106030118050c070f1e020a0603091a060f061c05010b04031401090302032d070b011502010207120c06020c060702071d011401081305030c01060611030c0a 72
    0x34514034200280d0181c1085e000542210b0303c100b403101071990903200342038200d1a00402c560400d502c91b80c40701c45a0140c3c40008110090842455148000c81d81038140c0c0305900400345890592103080c010011329100c40d060310829245246050061940e5800c10b004840c05480c810503040c101e0240f20305035000c0241619006940880303d81c0b0000d03d48540c6004c1e05280c400e85658518501b02041030b1414480c6244681c1d141c01d6550700040e80001c00c8804901e11007102c030300c021074840e4140143c5807520341c44801610700014460104051808424160380009968002c0490904804c038200e00540030020004180b428603240054095a0440708840c410a07026180c52640e20f00035081035019070312003016030f00c000010310142d0b10a08c0210603001d9102000c02c1c0c20b6140055034030745466600c1955041c05540c40100b0030301c04180c0b1018011980010460740e440701600700b0903000300b807584284000203040c01140a1000d80110464104c40f594000908600807551184480e03035803c0c109916030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 181974532 1250 181973282 181973303
    0x9071a160c0f0b1801030513021005041e0602061305030409111b010b010f030207080409050a02070f121701030809010e0415031b09020306010c081303020409050f010e0105070912 78
    0x12480d0440ba0742201600503c1d60041d00c0e55510701c00301c2160741e01106114185428001080111090308410741c004540484803403400e2400b020080e40d0300d01c6181c000c3c0c201d0340a080000f1b00e00320008107050f0308803400390307080390b40540e515444800d80d2852850000d00607001003108000006864210598a40500916601d0702c0c40e0a207001d11603401c007880030101651501034016166804c880c041013a00f40d1810194a42600f030350f100540780c4942d005031043c1070b43c0c03400440c011501560540b40500c0e407049564540f210785c1d04058034031070b44450100c00084d16000e2a1519149a0b031003440c122580a90303180c4c2004042d600545a890200340c0a6407c00c4d1b580036000049881007001c000194061040381c9140807554009001228454210f800c0e510b00400511600e47d0b4058000d9200b2500620195181d81e102802c65201401c030398000b0f54080c5c02c01c21124240440407030480d00044a000080100012a0460500340c6004983e507401041c0302c00410080000c446042d58041c6110309171000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 181975782 1250 181974532 181974539
    0xc030f02190f03030c02010e0a20061c06090c0c140a120e0307050402070201020c0d03030905010906050105040e07050f0f03071e0302030d0507050703061d1509071a160c 74
    0x70303803118000054802140c55071204040c107400d84924030902103144020300c03120780b0940710390343d442840c910024a0a0308145080140e0001c096000591040040265035282011030b4645112880b4940e235018139440c0078030018103040716104508101880d5150b0400c1300e80c031621070100b07a00213000800194060b4640318000075602e901d070035965a5070741d00c40c500031180c84814945080e484d60050b5000e02c0c8101300e400c01603a000100400d42010848402c10300310003c0c60f048010304200100280701d58200328000e002c01003141c100a058440686d42007020f0f44418800c030b5074820840c410300d50008480300600d0302a040480001c40c03c800b007c1e040390846c1e40e841d4802c410100d511843c544a81106640034407c601d010b020036041844180b9000341404100c1c0c0350551280d80520000741900c0d96036044402c1000d402c80740c10341010440342500c03407010180080030440700040710a00700d5802646400700d00e1078406208240d0800900300e26901f444003804d091031800071005015610886c5100000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 181977032 1250 181975782 181975813
    0x607030201020c06040305041508100b03070c060c350c03070302070b0f060102070e0103081c06081f20090402090604081b1003060e04060f0221010312020601060c030f02 74
    0x190061b44643e4565a07250301d0510308262805071183c02200300a00e81050102d15158200d8200581e80030345801581c1e9114840156400d009680005049905101c0450044e6411001010f40d00300041507400482d003030b003a1a028103643c0039a40301500300021020442203407106d400b8607071084040c20014901101902c130b06c02d010700c007100c500c05013000c2c0340100a0596411b002000003884181da200b000d65040d5a01c8201900590301307840d20012032204da9020586090300070000505040701501e6042050008403040000c54030304d00c10107a82441c4584200018170807028500d010782c0200b090a0515032700400c0080d5209600e081d074131079810312000c00c00342c50a000c042da410100e110000c42c000c090000784145803100b00e192400781407400c1c0b0704000c2c02003004039a5070300c96032040c400208494080320680003409034903104c034080440401c036030882c0e0141500306d0703050304c4c000c0395162044003209100b2643c5480900950703001440c0b20340e43d180002d004a520b403410b80c110f401a90510b48449508 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 181978282 1250 181977032 181977043
    0x403030f020c070518070c0303050c040b0f180a080d031e060b030406050703020901080414070b030705040602071202060f0c01020412031e2f010e06070302090a0e060f0607030201020c 80
    0x2400019040f07400e040260f032402c40c21210701c40000d83c0421039940790200010745000e8011030080c080c035858600003070300d0691400442d4090200401a682c98081c00c1c2150340b03154104a160040285040c0701c3c0c4401840d1255000c01201ca00100510b0b0401e1070280031000b401c602d888040a101c036214100d0440039990003840e002d00303d0301c50640c0d02ca16041c14085c0603210050304c080b0174584108407145690f41d205562070b50090300b000034401c036401440c4160b0b02d03000ca16449400c83d000080280001250301c50700810807a0201c0e42102c010b1511200804a1a40c1009000350321807010000c1250303501baa18068800c40d080c0000050a050b0785d156100c506222240007140044d9103040103010143d00c00c125040c16514600c0c202001a590751800e00c800402108bc20107503404078034040c59000c0c4250080409504a042640e0140c1490040075001c3d41051154030701c0348000c40310102d600b280c00903003180315030f01c014140103c1d154000f0070300c00c141c1d024210540131550200720014200d00300308803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 181979532 1250 181978282 181978297
    0xa030e011404170405130b060d0c020705012613051608010c14190e030102071b03120807140901050c0d09031506030f110a1203020d020c06030402180403030f02 70
    0x7610001450649050340305080042c0d00c0d4040f248080c40700b80701580761000c4c51403410448460001e04d03041650005085800340240f40c0000504000180704290b0340030070783c0c2c0222002030301c40b080c00403c80e01061280c03e2610010303a40e0250640c0002e6800d951803840340d602c66002d9002e451894580f422005418541354000003c00d039114824011180c1d88030090035004054003041e107041c4491000078400119881301c4903401c1107040f40034100b16a80a60442d02100d601002040b00c550803007020b11480c0f4070790311050707030341b001c8640603010214041c4110903c01c0700341c2d40d5521a030540c5600e899529801000c11141000070511100e03491900c100900100c07142c01d1f480e003580c000e14611f03100c0309080004440218950404c0820400145440c40381500c03258040050340c0031140d00008200c400718240e05c480406204a1208814150007107161802c0f20019404e90f0f0a5421200902c5040c2c4010381c1c000b034102c3c0d5001c20303c1c02c1c0c003400c8102403508103203e8a00820b24284c1d51501c10240c3c0c01600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 181980782 1250 181979532 181979561
    0x70c05030a030b130c08070e01210b040c050c07030b04030306170c130605030705060d090f0b1504060e0601080a0b03011d01060f0e1b0f031501110619020a030e01 71
    0xf41002c082d880c1000741042d0b503e038050307404c0c8040395600300010517940e03001e880003040c0600d6241030f0041e60302801e002c4540c4a148412402d201da1302100600140c9020b1980e1f41c0600e1500241d06d003150302c0380b0304689090405230b004090181c696030311000070740e0004000354109603480802041c210701d010041803503603041c54010483c10034108200020f00049006004901d440d00c1d40400c030315100460048100e8a00311451605c601c50320b405000500180d610040045000c14900e01c2008440300b003140c040c54084014800e07101500041c44219080d6006140040d00742c1c0c3d00050b000c0d071160b80c40035401181d0203000304a02c4051000310b42035505a1380380e00760b00760405c140600601024407540005150307052035100813501d041d007613401c20072018016a011030507030b40700c0440e400e1200c41241c000014018000c0d030f9030b14088a06007038155001000318001994169520b013040000512103008098039040c01c4140380b620001030000398490940741c802c0c16140c0b0101d42c043c0c1428400c800003880c0c00c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 181982032 1250 181980782 181980791
    0x20c010f0e06090d020c01050906070f030201020307080a0902090f090c1e131802011803050a11040c0c050c1216030c1a0a090302010503220f0201020607030e06040b070c05030a03 78
    0x150769410100d0060188000b41c0c000401240c14580c0041c81c10041d40342070038141e656a8480010800c1407041c8503000c0d000ca84010300314004c15078154011885480321398bd41c8200350b1901e03501c000c241d80229902941c00112500400d12040010708402e410210740c00032948543d959002040c05140240303401d1070880403200303a254041c03c00d1440c404061144140c10002082d8501d111008000e01040190400c40400707014000003032040314100c0039541210031500800c80c1c9180c01c40304408061011070190b420240e40a501c07901800b012986036a0210141c40f00764481014888a840942c1c0c01d42c040d031040d001e00b00060011a1021000b1318013588001d110700341418106464048030320840040003d081044c91140e0b030388410b0310000c1d6642440c0141c2c3e40d40361124204414103107000c80061180c403280c40d400c20046600d8690221074404c0e02983c21303a039201882541120914501c0400b20341214000400050a048145600c45080c1c1400c007105e004e03d85075680303190400c401350b4011940c2ca = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 181983282 1250 181982032 181982051
    0x209102c061912030201020f0d06060909050f0403080a0b1008040501050f0609070f140c010b0109082d03210a06080a0305070605130615050a09020405030a03080901020c010f 76
    0x120425444101501c1940740d401d41500c0401044200f8415550f28080058011013010720039011107203001e4602c60100e48480e0646203040c000c0619104100210307044540024400c619800740f0b80c45045c91444d0031200b40d07956201a190b2401c018400742145075600d40000855a03510720008841117569500301c0c1c140303028a0082e08582e00a411340349501d040c1401c01c5401d41c0c030300c035001d5801049450b08400c54168504150f416000e03049840c07100c1040400d94151a41c0154410070001c0000da8614410607911140103495035015007110030140340344040f5410b00d1001c08442c070380d4103800104580c94038212529601c41d0b9a00b000b001626030f8a600e0a1001ea0b60041c0210805400010050400a1440d54014045110b080402850300792030713000207800b82c0d4844502c01007603138004000f03001c0320700f178104400c110403000c1c05a43d1103400001030100341c03c030301e504c2907500350f80c0007400404100700c0940702a10710b540c2c000e12020b0550340070461110034210038061040c404400b00c9000c40e02100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 181984532 1250 181983282 181983359
    0x150a0603021305041e03030f09080c0d11070b0901050c01020301090b18150f030109050d03021e0c25180207060e0607020c01180e0906090601061b020910 67
    0x65884884042d1400c290a02010810200203103081107080c0074022144d0080b80380a401500c1000105110607180c00071240a2001c81030050100b0340086003610f03543d0000c4d503000d9400708017602c1108102c0c0d215071414015021a04d009142c0d01105061660904803d01c003032a0030382e4001d802c4481c482d03442c6c005006803428210310074641c0a000c0503500043e841e001581d0490a030f45030340c005218035042d000e0b0b1101600c00b0741c0039840d00c070382200c140c540c0c1001903203001e8083e5010b041c40403458003048010100104154042d0f4031204c0882010f44002403980c2d001a064880c0351081000010b0343e01c9000078804803541c450f001c00c000710480941c0b00c100300c0c00c2500880360064022205034101320200b1210980c00b044004921009081498a005400380c0d0101d14044940014402041540600640b00c100242403072190140b071044171150383c0c9640d0200d800583c074400310b160070b808a01c994070061505034442c80d400401c180a00c09050340d01c408103080c8101725403e0800c0482c0c0013551094020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 181985782 1250 181984532 181984549
    0x20703030e030a050702040b040b09270703050604061a21070e0f060904050c0301090c0e06010f0203190e1011010506060414040207080d140108060106170a0e150a060302 74
    0x1c81c0c2402030750401c0300d181d0010301075204000d0024800d6603030301c00340c540550b11035112140988000e0244205803a001a0741d107014a51a050300c04100d032000b2605440d02c0c000515001603e6000e4050919903d9581d0364001a200c0100c03054121917100f254000ea54030380008040c03190000701c0030601010100880c00341824100d400280801c642401000f0594000040072608018165008601d07681c69091060030014600c420035415405d00004905000d0041e603554152070411080f00525200c031001504c55a214800d03003400b5800030f100c02868600800d10040012580e41010007404402c880091000031014080d40007141401d40785141c451024072400e680f04400341d586501e05421b0107404d08a000307400c10300d01c0c81150001040020402c904054540405d103a640500c5585031009030490b80410134040c680c4203210303403400021124482c520b55285442840034a0b88980c9030009068058100100c03200300718400c400c02c50f9910700301c801580c3e11680041ca800034000b17056104008200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 181987032 1250 181985782 181985801
    0x3060625050a080a1416080c070306060b1c02251b091e0501030201091a0f030c030f0f0c0412081e09010f05041d041e0c090b0102030a090b0c010603051002070303 71
    0x10b00340200c1c5d00345848030015592540d007041f480341d100d00780101114904003003a08000c15040c10710000081343d00c584000b1340705134110041038141c00d817104a035030b904a00071070044104000704000c0071500078002e01082c04199016108840d0034420b1060322032406100755024a40107039894000000d44c41c04d556a1031403188080800380815455600001c2040c14240250098501c10b030299000840b0010201c9440c0d40513034407402c0d00e91034168507c141a4001321000e001e05071030003002541c6145844e10080c40b6561402c08141410705000e209035605840010445549a0070441102448a040111400c42c1002e0401c0c0b82e031941100c1c0010709000310380d0421030030300405000034403014842214a141c0e000d480b02072141c00707659900340043c8071207801d071a0114102031101c00c4001d109003115484d064032a003100070301202e0150001240c1c0c03403151020090000f007580c9414070090b0000c00003060310140600c004180540c6a454881c20444c0107a81103c20f01d40c0000e100d41007640500030725241 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 181988282 1250 181987032 181987067
    0x307171606030b030705060c010e01050901060501271809080c010504120c0503041e0b0a02010b0312030f06011110180b010501090b03010b0702061603020318040203060625050a080a 79
    0x42000c6801300759070b1042c0380940707880384101051481030000c00f5880200000032480082c0840d050006050b8000d14050003540d0001d4020400246c00202e02d95401000b91804080d04440e0740c0b511341d0102c42610a00071040c1c0041e00d030b05030032000c80c0c0c2035800380c802182000e00000345410182362a00c00c078080c29410300309210780511120041600841500d040b11507600e07070f003a600b14000000010500c032a41211810172008182c07040700d2030f81580000004403095003290550010241c248000b800300300c0c0d0b80c44040701d180b800991594030502c001c2d50701c200c1c12130484110000400f0f0f82c1c0255940004031010030414140c004007840f54852600f4010807007030030a200c0b1176007040c000c454588414060110511000a000d5086403945012120011204102003100b0183d0f482c00030340b00c5c0e002101804080701e41d4450070415141078400c403030042c2e80040c030b104c0c43c246080c0d1302c1600245080101d0074400304510001c00100740e0900140190070b214130000c1da0344045561024100905040f4071a90 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 181989532 1250 181988282 181988291
    0x22060818120d05040606031205130e040c050d030e04061d01050d0507030f0f0b040309060e150306010311070219031b060804030c021908061b070809010c02030717160603 74
    0x1407075050700c000c82e8010070456401080660381e9040180c0501050b44c0005c01003070701c070b1884404207648240035007010400081e00000c0a503a17100001c0c00b201040c2ea02801e8401c0202c1c040249103030100c81030151502c20709080011488150001d002c0310106d44c488000c981200c41d4140c1d0441c45c01e4000c601600c400c07a800040300342c46445a50b40d8001b940002400030394110009001c1c013100941c113481103540001220094541450001e04c1407482d44039100c0882c0490740c100c00c5514042d00745a5100e407801d036020b41940e544400440c05048100320156102500308030600150b14ac12410794203074005110080302040c03842c909a604885400d92a0290400300a0f06001e0b046c0d0103a1a1508150907243c0322071061484c0c000070300703a003428244201804c074a030040014882804110319114034031482a8484609d100145102d981c070030300c50007e0406104000305461580034820740710b9820b0010b030884011689031085090503402810b407401c0d0b2030740319541c80b02d07428404021060240c040e5140610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 181990782 1250 181989532 181989553
    0xb1803100b03100c080f040615030c1815120503040b0f07020f030c09070e0105131d1803031b0c010513031803050c040c0306030213060e0a0e0c01110f0a11190609060522060818 77
    0xa5010304d0dd4010307e900070b2141d00a1800388181002994027920130030641d00d9a80a50301400d0455600565049000d1041d0300d14100070ba10f00803c581100c03510180010882d030b84c032148112020b04c40c40f0782d1641806010b1000702101030180509401903c00d1020310b003218143d030b01058043c003800801300062300d80c1081c081c52a400000c400d480e0005440380c86103070254129001c0805a000e4000304103800d610b00803c00c00d130368000400c0c405440e8004c2d2540500d841c0c0ca101c0009510701c05002c080c050780c1c050444200c45050507401001d0300b840d00d20b0002189600d0b40d00161141d401c01119026a54503204d05000c600c428210f001c0d044501c0810810025019680036a210421565401d050100410030004103038418001d0000004990040e100c201c0402c2c90078a1031014401f29681c081c0314070080010f541141d4040071000d9810039120700035807500c1d00c1c400301c440360300240f88800782e0a51000071505000068413005d01800054372428128078040005080120168112514a40c000e45d01c0740d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 181992032 1250 181990782 181990811
    0x1031e170d02120f040c05060901050a140f0a110d0201060509040206070f021909050a061a1b01050c030106030c02060403090b1803100b03100c080f040615030c18 71
    0x80142401080c04a889000d11850706000f40242d405148900198408000c103142a40fa01d440c860381c4030b0020200b02c1a21642484118000c40b000180131890802020580600031218109051450400c9618002000d904c2d04400e400c0000c016000c5130a4171245845540184190700100d03140744000c112a034942800070b2060710303014001030b020758070003c2e1800500070310780c5461014617009003500d00c0c0680c0f00c50b600501420b40340300d206140c030b1400c00840d0300800d45000300c104880d05034a00440d201c1c1155156040c651048949100280000010221102080c01041e225100055503d5225031400c100582034038100c4600800310f4110400b040002904529510140c4500201e116228420500208005805d400d0541d5161190469400c110003440d000300e42c00031800c4d800c0d84c0303154000c2e04a4200b5039080d841c42c0c10103d1181000a88684140356119600a0083c2004a00d41031200360b00748d00302d0525001034030300c0402c01000f03000a04040b03901c05d00c40740120703204111254418001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 181993282 1250 181992032 181992053
    0x806060403030f05070f2d02060301090507051210030212241803040807140913150b1009030308100b0405060d1b0801090606032912070e01031e 63
    0x14148425015070203c128403440544640700c0d07114244026980190a00009450196801480e0140c565a00940045200b444c141105501074012400c0d039003004d000e440a844010071105c20410203000c4c030214180c000030700d20301802d10354548203a554194014050060b0688808001d2a8030051040428007084035601220314002d6004200d19155004801015401802e18041c0c2e80300110340890400c40200f065004c4441d070311501c4802c4404d407c144403941c3d03801c03100c0740004c0203a100c111012030810a0304114402140500050350f115200002d40c0384001c5400f01740c000341a00c0400c1c0200342c1c10910450f0070240d000041240709107022a0041e040c0b1850080034091980458034040010311034009048074800c0a203105891140c00c14010600c12003441041042ca05124000170010300a00c00e003c2c001c0d41c04100d03058004850640d07200042101c003a426042134500c2401040c03840c0902c40c0c800900240c42c41c003419540345040c01b41d90b0032084603550a1424800148100007030342ca948 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 181994532 1250 181993282 181993289
    0xd020d02150408011d0705030c03061b04090204151403090a0206091318060c09052b02030106081005010e0c09190b07060209012712060905120901090608060604 70
    0x4a2418503491001d5041d00c0c0e00495129103615801c00101a020000107403200d01d07102e10348000c070741080303580305e0030517580e195500c40f444d0b0150010300c00b0900c0d044c0000e000203002441c8015061a10380c0e00e403807280899209603c003900e80002080304088131644450603403034481d1100c04a500b5800d00c0d034901615a0303e8080001e01c10000042d02c04595281ca410070440307443c6500381000b00002c4281004c0c1003640398001152924582104002824011030351202a00c0d8003a2418500c0b050124000c440c003c2c07611f000c04c508030141010000165003d014250203445440081d001140d804e040080c08da41040e042a541680c074002007100c1980e00704151240e0b401c04541803840d42040340201d4200051540043d00c00c52400101003050020340c2c4c0003040d0899003a80d4501c5a04003400c0b1111112030301d035981c1041980100000c10041c0c00103e02c070400306000c1d120002c2c1c04401642d45c4ca1800c101002d6031103255901143c400e999603017100003980202020305142c1400e1801e1000542144620702 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 181995782 1250 181994532 181994539
    0x20c132f040b07050a02030105040605040515010602030d0e10110901031808090603060111010504050a031e12020d020c0a0b10050d030e101e2109020a0e060d02090f060306060d020d02 80
    0xb0f68142400020428254125000740080125003080e060200c05004100da0a4696100380310041460b00b600b48080340c102c0d5815030207581008101c0806001505070482c0042c018815041d03125420749180c850325000004090117260343e02c18640c000f600365445007000d903458054456602c000700c0d9403042290028103040f80c0705581ca41c0da650040e1160100d640544150750302e85420881080350000d940100d040c020b440d07640a54802e881c00340f03013404442103540005100b9442c982d0710f0748910740260840000c10340380542010702034140d151800e110004140ca400c14440227103d01c003200f1002410140c0710507540c51000c0c2c0d555440c042c0212444902103402001c1c64945103601c82c2c8500c01c10f800181505131114240860168001d05882d10f44610b41c1c03d180301006c04480070f1006110315000e00341d01814034041c15107440030f240c0108000400107600145220405001a510312003028070401804540d00d22505100007450715001006044900a0003030b8119007001d1381c2c0300400c000300e04c0d5048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 181997032 1250 181995782 181995787
    0x103050a0b031203180f0703061103060d0f02031c030501050f010816050903010b09040b180615011101060512030d05010608011409280606030e03040f0b0307020c132f040b 75
    0xa05d0043c1811030003502440070b000788020407050400104040c0116401140709002c006001245060705200c103442040d4000318200522000811065454181a0000f8140d410000344041a01c5008416450200000e07543e100180403a10340b52f411200245005e103000304a42c94804061000040054600001e000340420b149000703035070940001b03040030300243c0049964189480c000f03150311000d0702c00c620a40548080055003007000101144200d07803050340f81c1d000700d00c00c02c0191907440c1380421082a0795213550707000c80d0b280c440312240381d000b1172018011603852003c1500b0004941c0180c004500300010305004000410f922800031003012011102c41c01d040e2610000f085403170345040c0400f0300540d01d850807406a10120740c000c1d0200d4150f40c5041c1704007034482080948900c1a03000f4a0f0702d0001750101441020751003000345134044124012a0103c1070054000740d03003520640082c00d500c40c1c80c1c5101115608809040812164040c0c0c803c0c3c2e200031940410140324003403400340c8056520003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 181998282 1250 181997032 181997041
    0x908160b070c09090b06090a05041509150501030c080d1106070f17010b0c0706030209090406180b010e01030c0510210b04020d0606030c020d08040314090316050103050a0b031203 78
    0x40d01080b009100054041107040101e1a0421a14800b101d50600c10304188001401c54a0f02c1e000e154441d5a104114440e800c01c0107103c200148013500c801e56145400c80c1c908051201280325560180d40194014810140303000d142c3c0c1d2520703c0e50030b050b80400800e0072040c2018a00003c29980204641c185081d1a0480c1d00702107420350126640702c500c010f01d444c00001e1103940800102131141f440c00075030320881d07154a010f40580c03140301c2940781c010f21054005000718550741c1c030100d0411031031004000350300540d4440303640c003a10a811020080800000400c2003104c806400f0b0010041502c2c1010500700000c0d01811031015404c0c60929140111403011822143d50b100e00b01c4501c0045c4219100d00241b01400024540717130050001091a00440550150001500081e101000d545038080c69546a90403036a00302a061801405076007400304c1502581c0c14010048810b2020050280d9185031500040913248040c00c4250181e1030090144407585000c6041e9a507808117200c095900d499 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 181999532 1250 181998282 181998293
    0xf06280309050d090501020c040c0801030b040206070c030b0a1407021005041e030905040509070e0c210a0e0607140409150503070305030706050a0614040c0e03030c0705010908160b07 80
    0x1c1c03298001e01c1c0c3e00035a4442c08840390400f41d9202590b60a900f1034142c2c008043c10310080750200c2a84101140c3c104004100148420900035841440030b4030890501400e961100340305070701904122410303030520040040480729445000c21083d0b06a82d02ca01130b041c10b140181d01d40c000181594034841e1914002001c0c403100074030150300342102000303d4a01040505006014124600509104509002c01300c1d04c440b1700024038030286d6034180c440d04075640ba010b103012181d82c0070304800540e00052803480e10180444200f0603200380700c0c82c2404507903414960b031481d0800d103004010000340408d00602d01c030000e6924040d01e0540b074200900041101c0407840b4182d04510303e070700241c2d0502c107000e00841049000300203001000d202d0202070015403940746216043c0c0707889000d000c0800201a01c0b18610b4940350304035070040103840c24181c4196040c4e001182c19940001003e240c5580900420841540e0203401e482c02000c480e000f4108010043d2109000f00c0c3d007900c5003220510010484030309102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 182000782 1250 181999532 181999541
    0x70b040e0403111c091a0a0c0507090504030c020f180c1303080a02010e0d05090d080a051201090605010e010806130504080d06030303050a1803020607050a17010306020304020f062803 80
    0xf156041203600c101409900410401c0041c0d40c01d10000d0010780c00060f201c082c011b41080c0700c0c0c00806170142440810071044460180950094410f4840d02c0b00003c1d501d02c0600c80c4600560095541c00c0c8804098010302c0315241c0040c03501d030f009a100355a0165407024101415810041c00c4e420159104250311414040a0440d04040c10f81c4e80009120303002990154010701100300d2210541d40c4500740b40d142914a030041c0f0f4015030f0000d42c1c4a04040c005121800140485225401d050b030078071140800c40b002028091f040b8000d101d0303440805015568102e54400b410480034a40300c8403d01e0f0000204050984004454054544445c0030404002c040700079240718800c02c0c42d040240c1c60b500e040042c0540303410340b20081050718240400c80070b40720f000c02048200c0c1c0c25400400d15a00c1d40c080480e12680030149040400141c03003c40031841d070442c0c0155001314010701c009030322400c080c010440510000b42089202c0c61007006100c9081da14000b52246881c030159036007542a0000500f6030181 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 182002032 1250 182000782 182000807
    0x100306020306180c25030206060d0606090507030e01050109150311042004052718030d060605270904060b0d0b090a03080106050f0f071703091e070b040e0403 69
    0x44441c00810550355220f0b0090710131501c0c0c102403400d450b10305c2ca07a4204420003165005c0d005030000d00004000e414040c40b07e00d0554810b071800111256110b190500b00c03130098a1520010740c94401c00c194171002402110301500700c480f0300700301c09103400c088490340103107a103c010540d0880b08a8030010366143c4d8411800c8038a00104080425441072038250107a20900034184203240203405038a19644420300008114a445e62801c01034413071404007401011102c584181d2880100294007002c00503000b86070007441e41381c5500d601c510b1046481e0301007480704201e00c0c0352a60220f07102002131f590385121130382168103c0d200080c1c982c041d0000c070300c100710281c601901e00c89068081c007114100008510702c0090203580da10240d0713600d0701c030308942a00c100c6800200502042c000000d1880380c490040002506c2a0515000705042c0c1c0c0c500c169680003216495040d07042038440340d19000544003c0d180c040c0660b0302500419043c030029146501886c0502e4000b4590a000a4201802000081000e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 182003282 1250 182002032 182002069
    0xc012003070b010e090304030b04020f0a1e060912110d0305070611030402011106070f1407152703120209131506022a150f041e0e100306020306 63
    0x445007581000d50002c2c50030b129842e0f04105010005182d6800441554107580d800508101c07161207540801c88600c0030704207596440811400e0000319039100400c80a02001300c80d00c0642094909030019004000c0c0c0d03480700b42c0c80e44074281c03ca00042e031140500906003004440320031074241103090494490080c00c40c018202890010741012000c2000d0245120794800d03680c02d010060040c3d1529203420041d203462000c2040c80700e1009040340a0b003e40042c04802d508624142900390300c0e8200322108889488212558603100b54000d034803413011501c032150203a09410342214990754010080000303041200203460740070a0701a25a6688001059052141c04050001c2c124014100c2078907001c0d403140b00d01521803114003070b0781c0d9030700000e00d181100c08200074900300c03100d503000381700489807010320031203e20104006845038600a4030190019006805c038640040c90900e550341c501d408941c209205480720032040184020403240440243c942c81000944c494071560007041034411501880c060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 182004532 1250 182003282 182003287
    0x6060906100915031a040c0e22050c070506180304060302031005030307051c030e061812040909030219051009080408070b09040f0522050c0405041b0f080c012003 71
    0x90168103800080e00711545e05480c80034414a4020001101e041d500d00001003070a141400101303280101c6100700011607017004040410b10002ea420484034100d0f500f81042d03001140100504c1401c01025a004c40240440c42e22103500ca007107913a40b80554860b074000c2540008c00074500c5818a40048018070018040781d07103a051501c2c026480b0b088207800030b54001c0301c0544001c1082e00c00d004000d100310000300a4029501c4005558a100b1105040003406103c0d0480c00103c1684800c000d00c0105105040041d8110242c41d000b81446900340d61240200c21000b181e6011a1011030714041c0766508020014200e032103494107000d98010350740508024010ba5500192100003a4010002d0190456040245040c40c00e040002c03140b00381ea1104507405007483c03c000d0b004281c000c660840d40200c04440407620520b002600760b8008442c1180c600780300240901251500d20022000703400c82242c15a140c900385000380e6036070f010001d1818100f000d1080c800207626000420a0107010400b01078a6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 182005782 1250 182004532 182004569
    0xa03200705100518040b0d0f0501180b010e1605040e090a05010606030c090b040e0141041401051f200a0312050c07020f04020918060111060609061009 66
    0x100790b5001110385085181c044a0794403040d11785881444502c03071000304240102c0007103403030b00e0103480c501e03034030490b115961210380c08580c0c3d43d40c0000d506081c1c850303500d0042640c10101e06d00d0340000040c100400c518a1901e64040d065002800d0fa016034100d00c0030280103946648c0158904580440050625462300b200450050751542042a045002d0b80f42c0114840e41c518041c010b43c8542d104000660400c8e10052064521610f4440c10f5440d0803d4040c1a00000c040c1c0881461440c00d00311800c0340f004404081c1c0c90402e070003044590380030003888409561405000c1100061402c04660030f4003a04c040c0c405583d0700805500c00c283e00d0214114042c986008000c50341c4004100c01a00484c0d03144005180049160080074410340e00c0544103424032006600340f010300d20311140c1250340a178007417221408070b41312845a405000d00340d032403007d0b0382d0030000300141c000e00144510b14038a42041c410445140c4840711019001a403e8488a065800c0c01000b00c3d02040c8603013000c41c01580b00c80740310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 182007032 1250 182005782 182005787
    0x2040f110c0c06070f1e050106060e0103060b03040b0c1b191109040c052b05010f0b03010b030304120204090b180607170613180b16020a0320070510 65
    0x70a54284103000312014000b0540422005000b000001014000310600800014402e1844504074405108030429a505556200e5003502c1c44c036040f2000281d90800000071543c0e150044100500c0f044114901e10308143c0c8504201c900c00604c203c420280c0000c0382007003448032b040ea12126010f0042590021080f940c0700d0080310511100540704a011110829076501c0c04c0c200e80d40c040c6500c800c070b410403145810700340001000c3c035544103902200303110f42039505009450541c103103003803040d40001400c101c105092811180b4640c44903000341c2c075015070b03008141c900004980550b480601d440d5003000f0350b4800200940b01d40e034402805a035109044c0040c000076140301070800e0020209503040d036904c50504407040e49080202800a00b8500d002c185d050034806c21100d0160021316001c152086805001c0711185940c20040740e81421020400260610220050b81809040d00c050b220804070f58034001c0a52000300001c403603200d000c45400260000800403200103240c068176640d0b0107031424030701 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 182008282 1250 182007032 182007037
    0xd1805150405040605030105060d030e0114040e07021b01053709080607052106150a02030a0e0301020a0f1218030e0f0103050910020f0d06030c05010906020307031b02040f11 76
    0x600f405241480c0c804502403406018281c494523020b8074540518205890032201c01d9046801ca50502c00000414161140020020000740100440c0b01c00f6a080009009240c0005080100649800c0040140303841e030340030040b80d400141074164404102d1120120744400e04040300d401c4000c03911800614481e5404c5007104c82141d0070407042d41d40310f5a40c0101542c0601c1342c140c00c0080002c100c40000c864690001ea525000310000c1d0484d2200810080c142c21250700502d1043c016a0011602e01c20325070340402c80584404085d0001d60500d20844030103071994800c84044001d00c50700300e07260700038041c0c640c1c07090302403041c08412200210354506000e485044c14245130740c010305100001d1101e40d40280280c500519208004251601c2c4c1c46032400020f41100741104c502c024100f00d000400691130060b07030080c50054080130300640c5001c0024001a00e00e900100c10354000703000c4140425041440280048596541092020160b02c0094028121456040019813030844c610352001100d001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 182009532 1250 182008282 182008289
    0x109030206160e0f0913050106080f0706090305030307110319030b04060902071a09070e01140a0806010e010308090f090a0506030106080c0603060409110603010303050d1407020d18051504 82
    0xc0003150259801d030440780c40302a8041144c109101035080e80e40c1e8288065800ea006070125852444240d1640c0c51500b5a684c1354003400003588841c50310781c0c2c08623062007000e005020b50f09103840d1403440c503618282c0300d02009082c00c0c14418499500100d000c010b2049a1803200d4401c40542c0f04000c4c102c0142c01050011780080c000c51400c50041200d0b2038504c221b0702d01da5006a2100d034040c0c00d078850901800c0d8014001206400798107000250304428407d0140a04044081d07991080c1040080c003145e200720f5400241d840d0b1000d030040210000d000300c45c0e415640c205035220f03940c038002404149600c00d1520b00c036412036030404c01c10000080075400140120320032002030146554400c031035030b6216404074085a00642c10030120b0002e1400740e1142200610400c4960410220304000801c9a00b0913803042e4046200060141120303045403003400b500f5201481e12003058240004000e6803034840072030900c00d0001070382440c482c02c10300b06e01a0008000c0240444c500c0305800b56041d600d50094070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 182010782 1250 182009532 182009551
    0x3060c0306050f0607122717032502031606031e0209130b0a080d0c0c120c091a040e070311040902150d02091503150a03030519110109030206 62
    0x8404181450400300b85601010010500c0b8140180da032106c444c6400b100041d10244814407010900010040f45003141141c19007131400b100901e01801d40c62138804e01551070100b60420048900b0340c141603a44d1300c07486070000100c0781542078140f001c64a07000c6d15180102038280d10810014456901da00103101007000c054500050300100405141030b4010002070a500c0225804c281d510040d0b81e52040c00320803070060904100d01e0340c840340341d401d004040118800142400c0580310034810302100e0b090050264056910a500c105d8803043e84058550040c0f05d01942c5031144800c40030304464203002c400e10018000c204040900c601160355207003a100031148180110906a07051034203102c0c1840040d00544240102d4010501d1124143e0001210588550342884503500d10f44881c0820000d80c030b120b9003200e94900701a80d450b100341c00540800d9219046055091001030703800426a03c80c0c0b0042081e035805050182c030241c4e05030790f50120140d0158a1f04140c44149640044c0311030082038881d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 182012032 1250 182010782 182010791
    0x6070b070f09030b0a18020a031b140108060f03030c0609060a06060212090d0c0305010507030501030606171002030a11070804090b03160e0c040314010b03010f090f02090c09060403060c03 82
    0x85010b0700e62010a02c8003920300d400000c0043c94482407078000c0c044030407040100d50543e800e99400100c02e030314150820740700c034042810820200311151035840007810a004200460b1012000020480140103104500645160b2042881c54408105035461082144103968651401c0783c0d03126510b030f0089424003105820301c10f000420390300114003c08440c6801188500c0d01c481103040c40700d40502c000301101d03201a140fa000000c580301b8440c1c42d00454a030f41d40400c05500d903092081c00d98045c0d801001d114404041e06e6040e185001808505501c8000001340e1a5511000d8110042030058420302054100254210420456500034026241c2c044400c0220141100900d81e403400d0900301c00d213403084209410b109607480c55140300d500c41112090545000e44940c1c4d500a030301c0d031103900400581c2d154200301c5294a42030241c00703c1d00d21540810003045146481c0d1080750300c20318501901424160020442448214007155072101002d0200d0340c5d03483d80d9240c000000c1075030185603800240ba2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 182013282 1250 182012032 182012057
    0x40c02011418060402100c0803070c200102030d05040503040f0b0c0d030b0a030b091e2a01141806070515102301030605040c090302040b190b0c030906070b07 69
    0x40c0b2090000340550360004004641e41c9a01340549903000162040600410809003400100900d00440c8925501c0c0d48170f482c004c2142c5041c00c010412400c415854805240515002c3e0364004155600b0a01508011485440314108141540b20f46c0d0008400e40f000d007040862081d142c6002000044c2c040406c80f1500d424000c401c40c12a102000b4040d4803500760746040020030031380705120350001408411744501c0c0305005a8071070a680c0c1030781003181a800078000100b03020704000f480c1241c0070000c2c2500010900762400240301100c480240844110045030349150b64500d5800940d400001800f1290b45a01909250303540d50100100d41d42043d05620000b500b030f24030086800100d5007492030401003024000482c080c150310075164241050ba032907100103203554450040381c8401640d500c070000701504500520003502c22146600b0b01501706002c00c5034000c006140000100c83e0b007000c60310b4450510b010306609520a600c65941d0080000c1180303400c1c48006000e450285e0129104c1444902c0d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 182014388 1106 182013282 182013301
    0x21912020d0c0807020d020d020c04091109010308030402030714030d0c140604060509010b030102040f0504020a09090608030d0507030c0e0108130501050903120c1303150902040c020114 81
    0x91102c00d104d503441e01440303942102c001034405840d481c1c400b1040079540740725100000d4010b03503440382108140040340500289401000b440c0c3c4203103581d030381043d001b140c1040c1c41c00d82c802d025444000807018244000301c541d8810250180000020f04d00054400c241c2c1c6c110103980c2c1140e81045a1240003050040c540314078411500040c86080c407503522801c40c0d40e50b0348800e0080c0e104000510003035003619800c5049074012100980d60b4810702104541c2240d5a600c00200369003084404140c0220110182c40d000500c503904203c2681d441c14110305940114002d03c02181d038406803084c1c254411461546d102c605402190400c070200d030b4a007800c54000f1901a42d07650400320312a04070141c501c803100d800c40c0d0700c07501c0070f41130004210320b602d030142182c031000307090307d070f08950100c807607040c94121081d095001007080004806480300640a070100d1100c151030f82340ca1100040c1340c0e0704c = true := by decide +kernel

theorem cover : BRFrame.Cov 181834532 182014388 := by
  have h0 := BRFrame.cov_init 181834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 181834532 ≤ n) (h2 : n < 182014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
