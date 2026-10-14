-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0121
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:56:54.007803+00:00
-- url     : https://prove2.me/submissions/854cce7d-f975-4496-a4c7-0aa3b3e56536

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 21582740 ≤ n < 21762596 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 21583990 1250 21582740 21582749
    0x3070f020f03040b0a0c210306140d0f030c050a0f03020d0311031315090302150108030c031e0904050f0a0c020705130207050a08040e09010b04180605060109030206130e01 75
    0x402000c0350702841c01002054038180d41107001440d40301c01c0c203c1030031250703100b8180010740119001e1a80f0200607058400003400c60280d65004e00400c1d444d119002c07403c03000c100103103400103590080d0308081050155400307102032103842c043c0603407100c135121580340c528880c405031040b0340380741e02250416404001c081c8104509050920070004940c148c0c8103a808003d000d000070a003500084410402440c3d42c001c512202030000308180041420025913803107a803480b0168100c109400403d02e01000010344050310804002140307000d80000da60301002d0a43d21903960703507210600c000c102943d00c81c01110701c108800c82e1046401c1c580b1400a000362130710203980c00c0a40d00a02021b100c03e85400402c00903041140383d01507a5903400e854a24542180100040c0220b5400304003c42d0740800e4207411401040f100009000f20015501003004071040e1280e107083d26210a080c1c3e100246aa4000c00c0d8080414104485001d50b0f0b42c003c14281d40c4400d18040c62003454420034032a0307520407104c01b030251 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 21585240 1250 21583990 21583993
    0xf021b010509060403080f130203030a120609060f1203052106102f0a08030703020403031d030c040e030c0703050616031107080f040803040602010b0405130308010e0603010b1503070f02 81
    0x113040986005d8071000d8042c158050740f070800c00c0020040c1503d10012400d0310b81c0074040360380d61001810300610022034071002c03910f05802c0c5000040c40c05158001d8105841d281e546204c09245800392030188035102e4401241070050920404000d4414000200f840c0b060719041d499140c036000b01080200000000c00c10180240442c402c5007031840703100400c0b902c11104030001c140750250790b019490300e240280300a141e58400010455402e505801174003c59102e43c0310b4140e07490003840d0003800010171080e840e070503910034090160140392941042800c150107000f0f9916204036654414104000c54001b80e900d64001d17020710104603180f10108150082e540380400489407400e1850b00315200d07c21019140d0100480c4a0100e19061001c550051008800f240d545582e1000007901a01c40a00790a10071854400040e40c40481100c2d61a2004c2d07141e0754a03801c6a08001d036103808040b0190200b82c240d940c540849016868004400e1982101e084070280c8a24040c0c0000780010710054020045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 21586490 1250 21585240 21585253
    0x63106080105031002090d08040b18010309050a031409030604050c090708010b09101707031d0706050d0507020102040503060103050a0506180319030f02070c03120201020910030c030b0d141b030a08030a0f021b010509 94
    0x42103010c1100d008055040c60301089000183d01210918040c000740e09a05001d210140002c020b000202040780140a4840300c40c03c0d900d825055400300b1091041106004040100140c145001d46080700103612500b400d1141600001c8640071403441203070100c01080d500c00904400d1003030541440b04625019001341245130401c000141103001e05592030020649450118054a000b074050b94040c001c05030440308150795070304101d0f542c0c09140100307a0707403800f4003408035602c2801d0300d0110f8524034118004525210310040b03150580d800560000081517650301c9041c818420340c1c001030111500a04854000d0b50031401c1c003c00210340c1071000003d5a04c100440c00d86078490550303c100303070720450400007145008540c00340e019040c1690103652001c02e00c0d04034003c004283c14404035042515085504c01414050711020500481038055403541c0440325060018810000455109006040218001c040e40742404140c8c1c115130360710b01d1020401e080f4600035683c00d116860703200402c0c0700103100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 21587740 1250 21586490 21586493
    0x9010b040b0403080d0b0301020a02061e010e0609130b07030b041109091306020c07060c03030b090f0604020a11030a0e01020d050702060306060702063106080105031002090d08040b18010309 83
    0x91510443c4801000d05101140300300c0110502d9010211001002e0025942d4212082e07000b510380b202140e40038040618202c26025400781121a10305940520a240900381c480c3d81c10070522007001414054100202c00d1020300140381150340d507009403859180800d00f50300c0141008290340c144803c01d1164001403100040b95034405d0b02e1107403c400204180c607004142d03414218082e01c01d00c010f480c0184150200007800c55800f5a0b15031900c0d0203030350100407880d400340400400030307801d40c4e2110b4030f010f840d4007007011071400341d00403c17030b49180d8209508180412181c0c1803c8d03800060903d004514510340542c010b50b01400007440039031061809616100050380084c03140c0c00043c010074003420000c00c8040441d1552130484481c03801d80c0203100c030903e070315500400c149110040200440d0102010014685002380c00c01416207000070060442c00076540340020082d00400a043c1e40b01400d000c415011860a01c0104040d20341c0d800c81e50740d540026030600c2c00004070640202d041526107620b490 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 21588990 1250 21587740 21587759
    0xd0f0e010c0506060405041a0408090906040203060915010203070606030b0702070b0c0703060b2b02031209010203031f051c030311070f021201020f0f070209070c02090a0e030415050909010b04 84
    0xf80c4c0311208a0340018991103908107101410303410148401e087d070f5a5000d010a101050000d04114201264552030740e1b540c0e0401d1000740d0105461158001c0ca400004c6080703107004600401c030194040c41200c4c00c241440c1c070303030b8400e0750310076130050b41d1580b08070091103c0d40c1e606101300c1020b040c070600010700d0480590300c4660b8a862601c0058a02e80c0d07124035806542d80e800d42c00d80c40000c04d40030304070b46c29072240b00206450b0206c80e0040b882440340306a12a40100102c00b07440e08280160003541c207643d141d8658602041c0c10b01d008603640303001c0b01004109aa20300740c00a403100e65620110900c6142481e0150071120300c094004020300c2c0030701843d000503071514441204180c3c107941c10b0583c241249a0b0718013a008902e55205a5070005c01c0784001e515011000d003104c00d000700d94410458503900c500740d455800040c2c2c080d4224507000f00107403460f02160000400780d800382e402c0b280b500b0b075620041001d402c41880d0013400290001050700162404405150140400404940c0307054603015111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 21590240 1250 21588990 21589003
    0x4050c0c0d120921020d0e0a090f090609032703110105070c0b160201030609050601050f180d030f03050619150908010603080306010810030206120402030c030d0f0e010c05 75
    0x4410000740904076414074140c0d030003070a0038540c00314140340b200300f1300c81c030700e00e044d09079860400c00602c121449800200e1040301e03601207074a40a011000c495040c0711942001d09480c02c0d0012107183c807641c40300001a0716100d034040c03440c001c2e80d4a0360b1180e811041046000c0710003142605240300500140f001c944c51017901c1c1d00802d000d0034503582d100d185c1d1910081082c16a4082011300300d01140c0004440280420510514801da0707082247d0b9032941c006804130786086c1e0300140010010700c848040c0c00000300040c01c0414059401031025a08280014428140101c0840000344940c0224108541600a00d50001022500d1188240c00b04010f40200e24007032040000c109100050030001e240030b64a40c0004d00316210081c00525120b00380602903900c203946541c00103050344005461210203185000039039170700809092805000c02a00750075210080c2c42039030f05010b450040c0809540c2000000e08201c0c181c0c8511440312010754020b4240601503541c28103000710007000301c0001d003000c40c05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 21591490 1250 21590240 21590263
    0x3051005130506040c080d08010b07060b01050708030a0f05010b07030f050d0b0604080d0206090708070909020f090a060302040e0c09060d030512090f0607032304020103150f0504050c0c 81
    0x2156592014410401e40000c40d01910501688050005000d1449040c8040e19001804c0302c486101d109000c5504903c24428400c02c08000d00507000007903c07540003002085c00c1490010700306a929111a87c05e9070040d184600115a41c0211000300d8032140501c40c01842c01110460030804c06460190800182002d01420040c002940c114170502030b0b40043e4010384007401940e19107407154101c036600c54500c41c000016200c0e100000e540502d0000c0c040d01540c80480c06000c103240b80014504c0546a1228102d0703110040b507a504500e6100d407102c152154404e424040790f0f103441c40c0184800c85c0c00c40007030001c9a0b001410041d0007502c07505c680d0303034101d074040e5800041d1b20280c0c01c044849015031643c042c6c20a01c09030a00070b0104000440c50008440c14042e18183d032600d4405074111524034040080400b2880145040f070310b946044964131a00605001c00d028071a201300300321400c119000340b0308102c4101401d100d05d08091144a501c503040201080c6814242030005584142c050070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 21592740 1250 21591490 21591523
    0x207050603060d141e0114010f18020c0102090d1b08030f090d020d0501020a02030a0f020304030b01030b060307031b06020610050a0b071b030b06030606010306060e06160507030b01061106010305 85
    0x1d04514140c0d0811405c00840d40c0f070400c07031080c580e2a1812a000c3c4c2410104540703141c2c0b60030000f2074600e001154540498881940100c0e00c940c0fa01d121001a401a45203655076550134003540005440d540660100b0380c1c4600000340d03145861000c0d5540305540c2d604459030301e03070043c419141000e02e24000c54001400c112540103078008a0320000d00140d12281000b019135001140e400402900080545a4292952034001540038014000c03a560b010790b10014221115a1004101144810003429000700003c0c065500300b0382c9a46805000a130b4a024490502c1c1c00d031902048103650510100350032150354089001d01c1d45c038280019030310340c1450040c40001c480c001450410002446680c58005070310342c941403c17030b45c1d6904009880002c2201c0840c02b03806400006580c0358420302c41e100644885846602c00b01d946d040c140000ba41156842c2e94a4205078100ca43c082001000400000e5200300e224101a604188000f00741c40e10110300c0155075405400140300240700855148032003402d540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 21593990 1250 21592740 21592763
    0xb010806120c060f1306020609030714011401060216050102120901030b18040606030201030f0e06041e050109050f0106051206010b030403030219020f0c0d02030c090402060f0d09030207050603060d 86
    0x10102428011010b40d101d6008038002034444c050301d0100050300540120440c2080620795a260580c0c40701402c071041411604100b08180000c0d903400d2034043c41508903c000621000e5518440700c0d1244207810000141e07208181d0404401580c1d070706000908020710160100440103040130500f40144210a8107258403000c1d29082a00c2d0072103002d52056000c24030385042d08040c01d20340010100c50200b6400a420300d4103001d035018440c05041c58900d03007035004241c0d075510354036400c04004809010794180e0004081e0040422000d0040042c03140c00743d8003a0402c941a20f262900b10f074642d40c811409400a03441b081e000110119020381141c46001c040c40e43c2703035124034007200240301d44441c0e5000d14a2001d100b10060364005042e13400340e1010411100a83d440004200c00c8201c40f21000758035500c00040d0700c2d07450401d05480340c3c000384040c000034204040074604800642201c414002c1d8247d598207081c09140e410071030780e0001e010994800e0329605111011030304150114501415028244 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 21595240 1250 21593990 21594019
    0x30706020a02090703020c06070c0308060d020919020f070302070e070c021e0d020a0e09010c030b0d1410090506070210020307050301050f01170a06090f020c0304050910050a060c0303050a0b010806 86
    0x207404487c00b0320910700585446160034000a00b10b809107040c00d4001a560070001020f500f00034041d0803042d03400400518550b40c440d100f12207041c25840010356003503000d10102c01006610000740c121144250003a140a0b400d00321b105406050061000c1d0804c0b10f070302c1c82580540ca0b01303100d15113841400150110281a40004116002d0305140002d410003145030b80021070600517501d80b40148240402844504280c08045064941e061841c030340c481941a02a03001901c0c5074162617050031b0b1442525100307120440d1240403a1018130b010b507515008172040000307150303041c0400709550030a06001c5003103091841d0300521a0105024043c040d601080c0740b550141e00404152382011140c0c1521840c40c9810120000900914801c002040d03060640801e0030300964000c0d130742100100d900440c1403602e000200005414003800c0c403c004800d07048003051544030030700d200f006482070ba2a050002e4415107801000c43c6c0e401044e00d20f88034039002103e5000d130b07488003000360801c404540c00d10076850b10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 21596490 1250 21595240 21595247
    0x10e0915120a0b130c05090c0304030305090f100c180b0406020708030705100c020c040e010c03060902040b16030504150c030e010815010e0604090509010506010e0105070b04030503040c090e010b0906030706020a020907 95
    0x5c1d412065120604074200300d4005010801540308610a035401d1019440e2800402d81d0b03042c86225108140e0484501d02300569501d0344546021071640c0380a0320100c0c1c10003020051702c2c40039000304014950001e000d2144603010007c0200500080d0700443c6030000c3c5032601c5881d017031400624286640c4550001803203620030000e03a13005420040080107400c107041d481398000d00c0f00b074a6000c0800d0030402d0014442c2003038401c4e81c04507094000071a00d02507894100f00d0400c0c1c4100070880500ca41417001149401c240070b0b00300d6008141d622191003100301da00340035201d1601e1107071040c1000034000420458030101c410b5421704840a003440c010354001600059500d010319007100030041c1c507005c10001d0106054021a003e8002031700c6149030340300d10200450b444c1c8100480a042043c0100c046070001e4400e50003168481e000d20340e40b81106032203c0d504c60507525956405c62142c1e44624104c0303224a000076a007034004004070000c001c4d40703151071000b9440b540101784c00782c4034075104030011f01010700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 21597740 1250 21596490 21596513
    0x109020313051509010e0309030a11010306210308010b190c210c0b07030501080304180915020a03050609090705040f09170a020601060509010518010e0915120a0b13 72
    0x50040c107440088150031041031241d201180c0509042d1b00303004164148140101c11140055805806418810003645524030180402440309041540d6004002081c4880f00c0400d5011610310303c120b88100c1250800510004041e00811080c0104200038021140c180465040100060030318075060001d908155007080484c5280449403c2d181e940101000d500050309102c251041c8620040390b210300000324116a824001d408c0c0d581e000b00402c3c0200a460410061800271000003c41e5004041c0c0e516074080b03e5007101c0d25921034000c910001100e400d070041c16404401610301038061702c0c0008481d55103240c0c611841e80980c1c1d17265007008800600d60040e0004c81e41140742d090200c11414840b4010b0392000d554200140948000400d28a100741c08941d10918144c1d00c680c10040111211350401026004850511609603590000fa0300c901144c1c611070280843c100845203019000c0c4541c140c00a600301e40d2a82007000c42c4e6001442e030660301a007100c000d040310035100f6418946410303a40f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 21598990 1250 21597740 21597743
    0x4050a0509090a02060c1501090b030705150c070603020301061b08030a0c030b040204120b0c0403030801030b060d120509030f07051503090a050102040305060a0f0902010c150b09010b07050106050d03080109020313 93
    0x1720000760709000c0900024501c00c0c107410b0b98440502c140c0e644d240702021162601003490345a00045d03410846490001e5511040ca0062854149007060f0810010701d08141a4420b00c04a5004001041019080621241000c0e80c0c0c400c5440310030b1056076400285c3c072004100d16103c6940380800c52404c3c1c1702e94802c5040e5070003c1c3c011981d4036101d480701c415100390718404590781d0031410001205041c90b002a03030102c1c1e600da201d40b40d2690940c0c0e00c103024080000c00e655003208a1410100c0402e28607610849000c01c0c80c3c481c240e84038131100505041401d031041307690300d0b41d0111000b0805502d8082c001c0700c81c00703150a406500c0e506d0300003c450410084100142c007560010502005100010402d2070041c1900003003001555001024081035903c800c1c2e0180c003140261030f00c8001329400da81922090300101d0310020f4100c820400140105c2400e80020303e110b00c0110700901007140900c10300d8081d1900f15000030180384140c3c2e008110450500800140e80d801102080140d045003000c440340350b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 21600240 1250 21598990 21598999
    0x6030a06050c04030c0f09050711060f1b03040605070f0309050c0603040602040f030303051f05090a0c03020c0109030507050f011503060b030c0a090b032a0d0f0f031e0504050a0509090a02 82
    0x21556010f020032980001d00a507e211440c1c00045040e0754002c0780740308202c5070b10401030300c5ea03540d5441c3c040d60714102c010711007090441614003844c500104000114843da200746030002d500e0a1504004045540c41801d9600b0700d40b420642c500800d3740090800300c2d524084400c0b9649507150b26041010380103942c46141040c00300c09000c802c054054000034421806c8000b03902d00034880d80303c1600c039081c0ca407182e25000100c80e400300d220424103400580c005245030a000d884e1980e000303421070844006810a40c0000c0b00880d200e01040000d01c9804211a03440000b40518030f442c1140070700d40c065a100c01417001d5560460388682d42c40500800c001e101c0020300c45d20307040b5545c1100b1005012100758051207406610070450245140482517246025501d1800540c0c80c010018061089a103e00984400005c005440300040b0b06841d820049403003555100c941407041000c0c404a201d0002200c004d2200900043c0142c0e111904050308a850407036010f00f0546410316100c0c14200d000701e010790803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 21601490 1250 21600240 21600263
    0x30909151008090c0103020a0f0c0309152c0108191e23010e0c0f090a0b0c060703060b07230d0201060501021501050609100504080607090e0f06030a06050c0403 70
    0xd1500070b241c50f44100000410b40d00341c440c000004404038424801d08402040842407859600c42c8a414540c07080d034802c0c1002d846143d251920504c10a500c4511500022418001a10000004181c69040c182c031042c091102c00c0e8003400181c0b4000c0020700c8400d8828525038590240502500100c0000e024441e210a80c02000c00040001d0302d50000042e5440a841d4040c442e42003201215604a8501e100901603907124240101d5141c0c0c00b40560090441040c05018419600d01c0c07081c034000c00600036010b9460b00ca00320414107244008000c0d80615192800c00c00481782100c4c110b9565540c00010411606001d0b201c0d07a0100c0c0803e110790304244500351034140ca042e0154402e1058940903001c44a10412074440009420401d000b41a0046000c0c0480030325814000c001422145260902c60306107511900f075207241280c00c0f20a00006504003008103e10f03007007056481d810803c0c800780c2c0d01541c0ba0003c0442da0360140d0240c024240313079491001641880d2078000307a4000c0c540c48210001c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 21602740 1250 21601490 21601519
    0x30c1205010905060f010c17030a0b12070905010807030b040308101d190606140901020705030313090b0904020d0f03090b04030506010e0906060117040201120905010c0e0301020c03090915 82
    0x2010121340c0365000300500c4440306029801760440c5200c681d400b50b4010280c11007508804203d41000e0943c406030764452564030040d0f03580b00c1d842404102c04000908880d8036020828050721011ba000008580005906001050703403050b2444d8441d8041c10101c0361501c448e104840200d0b40d0307911042c03449649445101c0040c40c0703c140310703008400360302c800c01c070940d4a07501c43c208035003080c8030b0f0b00c0c0480c00e000220420954100c0240078504414010f54000a07503072808282564000001042c1001d500c4100707100c001c0c160710503400e1800f400c2d40e04c0d540c20300e85540170031071400400c64040d007480b69425403003041521800644014010641d40170fa07c50340c0c1c81c50034a40c5c0744000e01401c00300b9488400051003020380001d08a06c00d4a05035107401e240c0c2044603404440c988085c0042e410051000f45224000d00c2d18026030036010f20030000042c0408840100a05400710300c20305501c2030340100481c641c909000030a5400c0d80c84112003940051300c40d40102072810340904181d903044102a0143c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 21603990 1250 21602740 21602759
    0xc0d020304051c0e01090e0402040228020708240402030f030409090506010e090d080406020f040b04080d0207030b06040b0d120c02011403070c030f0513090e0d0512010501030c120501 80
    0x610030f001c0c201c0f442c0207040b4200142c0340201c0ea48505400204100300c100720004071009500c0e0001d00150005107402055005411200307030003a00100740000383c030045c13128141d040040c0402484040041d04554100c165840e248001c201001c200e03070207029012400390741e01400202c0c3c00c03000040443c0d60301c1e036840d0700b9940a8007040f03d042d034841c0940000016135007420200709108802c0f40000e454804200d28064030194801f400540340b0b03a41c2030000340d10703000291008002510390741c01c00035251464402c6807440c083d079140104003150030846040001034541d14035540c100c00112400704a0000c2c14001c07030204d003010381c03002c1c016815443c8401a8203401c100c125000c54001c0e40c891882100580070806544402d41d00071000420480351301c00807030b100b05a060724910781460290b190800d0b682862241031985c0d004101001c1d5140c40150504104005000d01e41c040340c18940e003007428140400c048880b05104450506490306800e24100d80300d450b921484414400d000c00241d6141d80106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 21605240 1250 21603990 21604003
    0x10e0d020615040203010305030412030504030501090302070f0602030a090501120b030109080403050607021203070302090f0d0b0a0b19031203060f090c020601050f060304061109030a05100609060f09050c0d02030405 94
    0xb9101c003040749000045030500b4000c49060700c2e0010000d5140903d407103141c456250300c001d41502002414040800021400e0003401403050003a801010203606002202c40116920b9001d03005640c010002c0315001034100145104942090901c18100d0b031000e4070319006890b04812481e0b0651928150b103042000c010050802c0e68083c508603200c65985a2040c1da8603004c000603142990400d0000481e101c1c400c0e001801d1541000e040741005281c50703804103000254200c01221540b40400c10000d5a00461058090400007294443c0d203030f000d90903205071388545900000d00590a8080391f940aa4000c1d00648014500c101e1840c800b59618854000209081d420880050061b000001441e15280c2d02e50341c00910700802c058a15103c3c0e0b038512004107000d040b000d540174400e02011406a4091080b15955030060780506403249004c2d0307030207084510300c1d0040040507290500174450000032030404803e480b002000011b6503180c582d000c2100340981244000210300001c10042003060100e1784 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 21606490 1250 21605240 21605251
    0x1060b0c0304090b0d03091e170c09061507060f060f120b060105070206040504050a090506070504060207080d020d0f1209080702100809030901030f0b04050a05010f0603060f1403010e0d0206 83
    0x20011315800320100040e06200b6000034002442000040c407144221001d02c101081814400300685a5581624040180707103001740400ca03004094900410b043c5442100d502034012101005144c64056001c2007034051140e000d41866620880014000242d0780b110000c0c1200f40208412030b80d031126070451455a94100702c840080d0b2a000c502c440d4010402c1c2c41180307500500b0141000d041100340700007400010088481191107080c0070f00401d200340a46405180c070f03991030a5440b420107030040d14000c45948000b80303e40c402800b2070b41c25503010610021700105842c00200c100032804044441e28102d1488040311450030031030b001040030100c010302c0c182c0d1094448000c3d44400b10780523283c1c484119840241e60300100810042980300e5804000200502c1500050030303003100000c28220f410484441d910150f440005110020400280e01c00400c0186003d000c2c032f90400b2141501c5c030945209a44034a0b50710343d0819144d036800e41044006c007a800f81100c0b481c10000030b0003960751030151407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 21607740 1250 21606490 21606509
    0x140403090f0f0306020c0a0b0403030b0a08070b03040803100b030703140105040c0c0201030506030a080304060b01030501050603070219030509030a12090f03020a0b0f0f0309010204050103050a18110301060b0c0304 93
    0x807000c6881c01500129001c107007a40d48420300e5038940c10041c0d80b018442d071109004180000000400b16443d1600441c043d80d00000c0c418804030038016000c4482c0c002602c2980002003c0006174031040c1240d50041d485083c0c0d58a98449c0c80c258071012844da04801000301001c020001060307810b50080700c08116806510b140350360f0710b40c10700c0100c419100c1505c0c005108010000050f50103030300920b130017620140c11940549040c1d240c800079900f007950f040300c0b520b0721200816180d60341800b0b03e502400c412515075195081c0008040d540b4038211040300e001d5082d40d4404c4083c0740c041c2d41503a0340c0e18009002e035000030880f8030380200181c00011b8113138081080f0410126403003414021410650f80d000d408107000d1402e10304a410300e60059a6655282c00c000c11002c0d19200b103103070196019a030303080300158686007010000340617918028000d0b1100d51400d03282c04005880c0e410618501a08142e1400d004440c584c082800f6190756001182110301c0018800d0142a0010007041102d00d40103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 21608990 1250 21607740 21607757
    0x4090f08090102010c0903020108060d051c03021c0501051309020d0b07020303041a0106050f0f0405030304060f02070506030f0a05041103033405070506130302130617070b03130204060306140403 85
    0xc0082c1c52a41d211f000181c00640381ca0b000038964103080b810402818011030031078000724140004034070b81c12504681c05001940120304d060b001c4810b04885041140c2c0000c0900840d810000880c881d044495103640130540c4800e11642551150507100c10080e40204140110f40340800c400f80da242d2094800301e40c1c006003214000380a08030300781114142c66041c4d547d645841d0200c02500701b59000162420061a02080005010342d0104014002000c0c1303130b00c4207401028010800703070401155601030390081d50200300704440b03920041546d41e440f4036182c6002645454a003003040719400500d64244e00341c0300010720b040541400c14250080c81c55200c3c0c08481c03505051038242c02c03a1030400802407840d0300104051295281002c05402222000f0342e0200440d035072030300000c006103044401005001d50b03035442407210028034440c0c00615950710f4003c0c0803440c038080b81c0403106d110060044406405251046c1d045640d1504207100643d04618144804441101da00444070320a50b0304070b001c90b8526 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 21610240 1250 21608990 21609011
    0xf0302130902010f1218050105071404080d0c050307020a030602040801110f0901110a060504060209041a01080601050901140304060b100801060228050313030203070609050901090b04090f0809010201 87
    0x50107140301a50307040e0348000b510312aa0506070781c030819008018020589800490400c851046000700155003d10f00106a40c10520005414110001c0f1070314000c20041000b40310704000000c0c154021121442c2450800c185428014110300901c04020f60003805244c000060001c0383c4c024000b5a00c1500081102103400c40381042c0a07c90080b01d1110f1420910070142c00d0741c00741d600820100e4200d015034205054641c0c60808a41701190704403039840d80440c070103010b400d01d44070381001038200c40241d006050134600064500301004100c01d040142c00509030344940d108a0007a401c00c6601060191203040501e45a0301411002144500409241c0740e2118140d03c039441c00c0d8100c0b2601d802804181032600484440020440516158001807041050006e00104010090281c5680c0790002e110b0441c4100760a0240946c0590b0400c061003006120075680c240c2404e0441e440100002081506000031034050840d041c005441200d060000e80280042c0c0c0f0010208014268002c00001910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 21611490 1250 21610240 21610279
    0x90c09030302071d190b03030c030c0c01080c03040605090309040204081c170705030a110403060903090603050c0f0d0605031f0506040911010c050c0411040302011107060806060706150f0302 83
    0x151200b413004860220302080d00c01092004000c0c580300c400340041100b24011000ca40f5581c4801240c0407580e00000ea4144054424001e02c2400c610903c3e0a04803400d2200301c81010303000203800503040b05d54030808100b040d0810000c440314100003410943d00c50b13030790f1241280c0743e5070216103119940e02d05400c80c0b0f0000b0300c640d100a03110001d907130000c0d006407501641229541c01c020100061599220841c211781040c4070080c3c00194030a140110f8214254a4024051845035101000741810706042c0141901c100c1d0580b821407144040c83d41d10385858540b44405030010b03501454150050f00d040c0c10155003551209860145014418050354403105d091000320760354518064403010601d0040c2c649584a10501e1140f140100105c404900301603000900319a0029030201202100241c20030441d60000848052028928003815010f86046c50250541d04020100b520032240025648100310b0168040c1c0741d0411100454015252500c17181c161843e940d02007039106000034091300442180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 21612740 1250 21611490 21611519
    0x61d0405011508071407080306041a0a0621090809031b010212090f090a0617010204080601050105030c070501060b0a090b0a02120904020403020306040812130309180204090c0903030207 81
    0x2512024030007841c0c04a021140f480d03000e001c2000300410f41c0803040b000f06104010b002014003c401841d0369007494010401141c03900003030344070403a4500c820fa2400d985d45128001c22248c140c00c0c81011101002c000c0d581058096500390a440d1404040e4000d100c111009407401d08010750403074000e40740c10f800141414009041c010b0043c1c2c4101c13001812180910040e0202d80d0000c0d10241980d4010800184a01c4085440d01001070751510200b01001112881c0f1001c503c040d07000310302e01400c1c03844d440d85a1405005841c140000000416030403103800085569081c0c1000003005030981350444040203030311040d000b400241da00c0201184001c03481040b6600f0603130355002088920030000c0010115000443c859900603802d100000150328140a0144179522905103075960708800c070f0300752801c031201401c054912088505000006a0000249820b90380c1150440e1445500303801c100001c0d10560700024007207801d245507600c1050b0041c0c1c5460640c0d110b9001e56200765113a5803050408803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 21613990 1250 21612740 21612749
    0x1103012a0e03031204150b060c100b0a0b0405060315030a050c0a0509071e110d03020304061506090b0306190602030c070b0a020705190f030c080601060c0201080604020a02070e01061d040501 83
    0x149154085000030b0b054041d00a0001b8503548007041d1140d500002901d0b07500700f001c84244a402148a400c0c0507076451003030700700c0c0c507004581c8040744c5424100a210f103030040740101e0340600000004108048003108402d04044001400c03518408600c2c64096111300107a100c650069428920101d50303450100c0501d0300c15901da03038800e1910031360103202c004c09002040755402804044d8445444c003034414407500000c1d119a480150b41c07808c1a242031802ca40c40c1c5540001d800c0d6100e60244007a40c1c1c0b0000e0030045078400c016280d02d079151480003a101c0403100d440c0099482d650a070002c0c15580100c00b038444030b410740c6c3c16500403594401501c42d03103100700c40701c560040c1c000140500c8989800c0d400c0e2400c60305404000400d2507252000d4403002181030b00142e956480302c40c41048440020051207000d0002482d09110101c12640040e01102c8060300b203510403900443d0214880d4804c00000006004490f061501c035603403850058860f640c0107500c1c401900b50b01158080074145401894101c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 21615240 1250 21613990 21614017
    0x714070204090f0b0c04060905030a03170a0b0d0b06030105070206010806010b130b0313151b0806030c0a0e190510030210300e0604020d1103012a0e0303 67
    0x280056081100511500c1001c0b520903041e0290030012035100091540b0800303040071059030b40da04024010341940c42c2039021900c00e501c00e11840c030001e079000b010f060803c044a11181010748500d039044001d4503101d04420342020b04000000188907441503003500445040d0000c202d50b8480d12001ca07124282401490503030f41c403050040003585000070060281f6040c00b0105e42000c1d44038503010030590310599160313041d8510000d0704028400e00c0c2c6d00b403e81c0299008005c22801540c100c540f000c1441d20341c001c10521a07500006205a02c05003c421090000107040e442e01545881c1ca4035103d20003550a40c200d0009090704000d14404d070b200309405250703a010303e22440c82c915420085000c1c0460783c842c1c1008240a0307000008a0b8260110b03210180a60f801b0342900c50044106c02100c220f8040460a0743c022414840540c580c00361a09145401c00c410b034143c02200c90119014080700380810360003a04039040113440800d0b0720030401c402e41c1255075282c024102c9004066407400b511100c090710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 21616490 1250 21615240 21615247
    0x518010b0903010b03031602030706050c0c13020c01050708010608010816030209060406080f06040303050c120a151503150e0106050a03020a0905100216060206010b16020f0a0b120714 80
    0xd1003103600282000310300040010413001c0100c00484d04680204491140c189504183e803011848c003030041002078400c514110381407040045019a456558a8019009403402040000708000580407078840745c1c00f0704002c1c0000d05007d24010251002441403e0000c0c001d0b10022403060408580c1c8100e42400c0c1800088060071030b001c0184415014100d0f551141d510720000130765941c14000010000b07051400741185250900303025041d00c0c4010a050703103c0408111102400f509441a290441d84900d40020640341c00c002000510480d504200b0f1001c0d000e8504814155040d041300e01d180d407804000c2d07074185644070190000e2480a0280c1d00200d9414440040824071a0f03001d400c0b01d5000d890042a9103a03140c010519100e085200e801c0141c010b5050b80410101003100000100f00d9440201441d40c50082050300a00500780e1100030000400c0c8603c095594482d00c992011000500107a40156221b42414899000c8404d010345416a6000541d50500443c002101c03940c40701c0e1a18034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 21617740 1250 21616490 21616499
    0xe0303040614040503010504050d03140708040f05011418010f0212060d0f0c03030809010518101d0d030b100302040501080609040f060903080603011109100e0607120305040c051801 79
    0x10b0842c524040402849002c2c0310000301e0741c2c2c0902510380200e0280c0058424070180d1200201a9401402101d122103000380c10301aa140d032110169511a40049078031030354150603e05180900084094000405040e000b88a800410103122000e9031003902c000300515841c807080242a0300544061281503200714000420304e040562900f0480c510442210401008035a13540101a80c4c0703030405d40018070034104100000400340306803900720046c000c07036141640010240543d2100c1c4040c89000035901d455401000c804108071741d45400001e03005680303c0c000c4404004000b0525003078164450305a08170f00b080e6481c080e100300c505590042e980d007407407540e4240911061041c0504100d075071604000071200030a285100700840380e442503a662502342001020907003915459410074075860b501308445481d0340d071030741e4150000e0700250400c2510010b40ea000034110f4094030303001600000d12100c0072011a98141d00c418032480c0300c0c912200c0320f40d485006001661801e18030400345950030200510 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 21618990 1250 21617740 21617747
    0x408030609040804030507030c03021516081812030703020610080a06180803100e180a11040b030303010801020409050703060501200309190306110906041509050d080a0806010e03030406 81
    0x82c1d1050140c07090600e425039a0f0340701460882c196205952200710041c0c14011440c081240420480e0f0180d2807900301544442e260189005212000f23090110005516001c40c0d03d03412004911103004162840c984020301560340c403544400c604030014010320002451024103041d02c0b80540302043c3c001d140009841d92140002c00350b0245040301003a400303524400081e0792000a5200390507011030300005a250142200007581c019000401c0710b401c1080c42411948001042c0c4005d6420042d006c5680c82c048000c04c0013401c980141d00d400d40000000810b070800150020000c40d4109182000640d071006000c42c115800b43c081d40e07000070141e45080c20f030a540c0d81070600950000d002603a02d8049000002030b65880b00024900041c0c070300070010024841d06200c0d041e14103054140a0b49046885000a41d09103d0343c0680304138440e6240e81c45110740e102e006a4400780c400a42141c2000c205d505040305150000e500c03040000c1c0d400380020342d440d442114060016880074000b542013a080800aa = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 21620240 1250 21618990 21619009
    0x70512031303030806060f04120c06030507020a02130207060603050a050c0a03020619030b0405011805010b070c0e150d0b04050606010c0206040902090d0501020417070b1201061d0a0608011d04080306 87
    0x80d41b0400902184400b104950000c00080c8411207803c5da840f8500d107454443c1c0042a44000103052800c8204900103802107032294000c2d81c102c0340c000b01c0c2d00143e1001d5000340140341700035103101c1c5800404410041c000a9000103103015800300e074a660381380d000b082142c4c110b900000f50800300c24800c40c1a91184022070401c0c0c079119040104140e07010101040403107000340d0041402020a049165400e4114030030340340540407560039241f404015407142c0e02d14100e01d02c1008421f1000c0e4002030103c1941100031284c000c0e00502c1d14036400f0030740c2030a2039031400694040d81c80d4054078011031010760050030882e030602c0c0d000e000141072614080d940002900400702c11900840010341c0c91000500a10041001c0d251500c55200e06080e000039151505030150400c11340b030b1000700315205000d004442c1250445450303240485000705081150781d807250400c030072240c20180000d004500c1d942c0058225042e56074002c0600e151900035044440552020740d4054950402040802c0d007038203142c0d680 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 21621490 1250 21620240 21620251
    0x1a0a050a0f030b030d050306040c03110412020613031a011202010804080307020a0c08030301170a030c0605060d06020d05011406070f111c03020105010503010f09020105090409110409050705120313030308 89
    0x1411003d140c000ca0308281142c10382c040060310010411545191a104507100c80440307281c01c00c040144072074060030078421405840c0844070003a025104555a076030464072892441204501070a13664682640d01d0381f140c00202d0150740c03130700001050301100202d04040e010b8059540c52041e492382c0e22101e4032940040c101d80214015403540f0400b05401d00b000b10300428004006550702c0d8507080c80b41c0400c450040100e10b16801c51288180441e9012100b23000860300719900060075118000006c15200b14080700801460000c200c450550219a0001d4101c6081c44d00e8020044010420014903118140008204181c2c18850001080c884100203803803480141c110b444641ca007408070100e9000701b64007240103030b445078014044c2e800c0030300408410101519091189c801280d00103803a500400b104c1c1030040307030b9540f504020f12001c92041c098000000d0b00c100182005400c01540720f80441c0a8079000700191705041105001c000100e40760480704000465519085540840300c440002c0c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 21622740 1250 21621490 21621497
    0x60f10080f060f01090903080403030e1515100527060d05090304090b030606100305090c130c02120f030c030415050a0e0f070602030a0e0607140105011a0a050a0f 71
    0x1010030051010452080c1c60300401c002000039281450f0308800d00c50301600f001c1c105504049003c1c000030782240c10b407500180c0c0b60401007070355040404120700c2d04068039403500740c5d1320718002488103020300c070804103204103400e503210f0050300c00450098405100d10b011045c40e62a2002c40446a05504410703200c018100074481e51400d801c0b024200305413042a540309130950800030b0100444101885013140701142074000d4881468913400054000d56030810186c141916500040c1090b6000e0000c8205041c0c01010700310444028005080240210f0f58208090700c61205070401085542c01952140c19080b22601c0c5180c1d20f0081701040ca80024004561000340040c281c840c0f000c46010f00380c4100604c042c00203416107111300c0c180c50a00c141401d94001d40042d9001d100840d400300449000319580e0501d10404e190a1010800300d01c190a400b078442800c0c5814803413001c0064103c01e049880d44802c1d5000a00030700034001d07681c448d000400000c548204030042c0b505008181c800c482c00041d04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 21623990 1250 21622740 21622771
    0x30109090501090605040c0e07030c050f09030f151009090c030303020702031005090c0f01031802040b0a0305030d020d06060908061501030908030f0a0c1d060f0f0a03050405010605090405060f 84
    0x3550013003642c40a41d021280518824401c2c0140b0b40e106143da44d126503680b506000100c80d407400500248180e400e10640707104002100d000c2510200000100c810107075003101c0380508070a4541440180546000081441d00c2d000040d000c2613900980c09040d42200b0030040292855400b1b0b0002e50110f581281c03d8003031207011001403a45841100d1180c54103101501e02408000100180442c10001141c1403500c0d065600d0f1505103543c1c454000c0c01d078196000035000380007030006840c824055200400c18800007ca20f0200000d90b0040c00e07584054000510809850308015680400c80c0d001784010f980c005000520120401d0340300151001040c103001a0740c40503500c034844164008c90700406100414014041050300780d10402c0e007002071529104c81241000101c1021040c06000041e02c10013000c43d0520f0380d002000115010040c0480303c07c0e948143d41140903001d00800c42d81505c40d5480c02100003050f0a000e07401a21480c0d100014117004d503100c00c0d0038101134402501d400702d01035802 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 21625240 1250 21623990 21623993
    0x3121b0303010f0302030120030402040c02010e01021b010c05090d080f040909030302030601200d050309031201060906020c0a0f05040911060a020304030209130309031e0b07050a0f030b010503010909050109 90
    0x20300055019040d0b0000841105003180141030940702510b1104142198000c50f405100126200340c80d0030560446000c20b0740c000c101401c13405082d010640d1a8a5440000d09000c5060204000400480844001e01c0f0309000c80f04181c9040c0120400140c12080101804000502840c000d016864440c1d801c0c50a06072100010b030200c1e50a41e40440221740d0000034480783d50307000112440c2a1420225060913202c800c2500c0c0d03240c9400c0550641403000100104004460a0040e91068110b041a5200f1503079a180300500741401c8d8400c800144c054880700306101c3c00e099803c1020380702044203004940d071400701400010a80400c0696009142c1501000e0341c0e6644401002d40300110742c01186c446045004004103550302070041d2071144000112200041c0e081203490084a07003001c210b8010720140d80811600340d171803403c02014001c26804120b0280d42143c0901024840c0e0755070405031102c404410307802c4a5001541e18080b4000740010419218035400c86120184560000314184a45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 21626490 1250 21625240 21625243
    0xa0b1c17130303020c0306010f0513141f0602010207020d0209280605120304080601050d0c18020304060c0804050606130603060e06070f090e150a0302031c030c0e03121b 74
    0x500300201c084240c8000400600d41c1c10030040345282022805000d0551401d0024000440b0b9031081a0080f00e564240e4400c4c01e43d250700070601c81448840482040c0341036101c10300c1016580102d0034a120380000c001c1000740c414130940d6102030703016080460318117041d000c003e03400100401114203480c0300c21740c400d6840e030915030701c8603c001a61000b140140c1040d041100e031004201014070240c0c0140300820840c1c80000c1c020f4110384007901c1003a0b800e24241401020410399420110403120500416448090194020351049000301030802485145150444407648146d9010313000b40d010b03601103000c6140c40040c41c1001c2c84241400680940d503961060140d0300380c0e10f078000017a00884100100c7c96045029203207036035114074001813110b00306502c000c2e100801401b130b641da110184c200b800840d1a040d04001c051a0010100c84520328035908401040e22405003c07000a41021b4000f1502405110b980110540081c00f07440e00107544146001d40b07030044095141c0c03040500c4180341107281d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 21627740 1250 21626490 21626497
    0x4020315040903030911190b0309070f06050a020601060302040e0403030e010e010e01060806180d0c02010203090d050105060406090203060604030305070620031f0b0304030509030c2101050a0b1c17 86
    0x1084d10081864800c40c140711400d03000d000a001e019200c010001c0e41003024840c49170080c0c400e030205640d03da40b41c41003800d02c0d20320590030845500c0340341203001c0340ba070b60800094070740f10040c3c0c0d00326280745e81c0700c500c118207901032485034140f07199211002c0380000c0d009800c4110625a03034000041d030300c49034007041c80c25590561260313030307480c0d5552005010208083c40303055407014250b448850103640300041c1c26030b81c3c2d10b010364041c1007040580307210045a1091045820002c0300410303480600e509030030243c5c002e01c0291503c5100c0c80c030f000030002c1c00c086540282c0340f1079840240b0560a061035030b1000d5449034800d480481d007643d80c07101c1101380300e002d403191800402211031405449203803060000c80406492003845500310340400d000c014180b003100869070b105505280c86526444040042850464a50784050340101d075044075218130b40c11411900c6000c0080d000038465500c0b880780340d000321611001c80c3e540009030114041031041c08003d402c2082845400c00f48a03038080c1d499003010980 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 21628990 1250 21627740 21627743
    0x201030b0406140f10080714040b0414030606030a0308070507080c030708071a10030206090105130b03061c17090d0c080102030601032d050a110f070501050106050f09040203150409 79
    0x140c500382c24407114100440340504000e81038840c26403048003050043d1688000421110400c1203008e000040d04486000707550042c00400e0f1100e40702c0343c45415203030a0000d800410340c000d00c14034000908615001500c1039040d41c04d6280d0783c1841d01c81d41b80441c4c0982c04054242c4500c401009150b00b4100104020700d40c4500a0000d10303116011482e0a60032101004020510a1004000c3c0400c000c18000f84004490b81103800c1596401c0140058a543c09418014904541c841b400020300146140c000c5100b4803080f00c4008425a0050b8500c00c0f4003010000506118034841000c16a00101002891500e0b4000c0c1511540141c564882001004035002040c0b5a50048180065940c050084920740500f20303440b007100280001110041d954884c1e14082c005841c0c001152000da0f040d884100040c6080c4003c41e558030341ca0380304800c00e070700c00b4504960f15881c00d4000150644a407003a0b814000425050f80d02e000741310402c1002035080076080903a2842418144061582d481c03251a0704203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 21630240 1250 21628990 21629009
    0xc0308180604090b0306010609180c030f02030f0603120a02030d0e030c0703050709060506070201021b01231309020c030403060b0103110a030504060506010509010c0308180a030206040b090307021c0201030b0406 92
    0x44c02d4060506003101a80528180941c402041c0700440c007652506038800300e045000225554020001c401400c88a1442c02e9214800070502c100c078045d40245905c284400e504440c0350140071066031000d4401c8101950050308203100240d11a42c141d0401c01480e1040e00849040ca00428202800d0081c1680200d82075800a40c0410004100d40926002403d046654a00780b21341a00080c0d2204039181000907494900320a801c2d0300d0f80170742480200c41c007100e040c605042171500c0c0031000c5a448a05034100200d0001d100150300381d118003c60750b50f400501c0c06036040a2450340c50501900600800905140d20740340905043c80168000d48290561998007080c1400d040c03c11000b00c940280980341040b1081000d80e125903000140101141c0e0f06142180b2540da03078158010441105080c42074450240320065410702d5400500300e4040c50240c1160328094589061503a540c4c8a40500250803581602804000d11100f0301680a000e006050105100100800050440c0e030640c02031200e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 21631490 1250 21630240 21630251
    0x203030906010b040f0902130e070302040314030a021519140a0b01020d0203032208040b030405061f05040e03130f0f05010305040f060507050f0d020306090f040c030818060409 77
    0xc4400300103041c01408a4610103161500b0004014150071460180102c01a00000c3c0308100030740300030740c0340028100030054040368141520002c2c0a903001d4072041da0481c02d40a8010920340000c81111481c610540040981407250004549607075401080e03c1c212044003046016040320b2405221080c082c40486066149442c1030b28504440b0301444450441d40405103410241d9000005c03a03400c40c00c4040b0405114603104a40003107801d420000030803100c404140040e0407203100c800746002d14800d00903200d55948100084214018207a90a40d8041d101801040b10b41401d0b401211107030301c03820070340e498a0840075105e180c1d00707041d500c802038118080000700800d9440b40c4425014040c2407070306200c6070406441c0c0024803010b58102502c5543c1e260080748c106030007041119800a403425816443e00700c0000c280c802074000b180c03030602030505c60001034070f54645038941500c1703542c0c00041110041d0a503101c00704650403503a068a02d02c44030030919241c940e14040038200a04102101295 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 21632740 1250 21631490 21631501
    0xd06020d140717070302030603070504020c030a0e03030a0207060f05041e08120f1c060515030906010e04021f020f070e090c060901090614130306050601030e0c0604060809100c020303 80
    0x40410300610030b00030030002c81112001206256151074002a151401503201c1e2280d00c002070901d0710652046070b100d48001090380780e42d2004409000030102540399040900c181500b49922803160720b500740e0058200007814004103000c0d80000f05850100c0c5002c50900e0b032154191210b0034802c100a01080080f031404101e0203800308107071440040b001d08020b0500e241d070007001501d40599141c8070601e00d42c0f040d900c254424150300c04001000002d08560740d01d42040d4403488540d05c15a0b07a04264002c0c0c9001181140240034000e0143d503001e000101c1418954041b01464480d0081e40d20450188416409038444100001e0300600700c1024003488030f003440c909492030007240d1800c4038014241400b01d2443c0f41e030032241e494202c904d28104444007502404c81100148203004030b14143c2543c0e03100c04000d0040e0795020602c200001c0e02d04004034100d42d201780f0b50380d03003800034010340c800e4003088207005180c810360600303030071000a078101c0d0280c04143c083e0034144c550281c400001030b8801300c00c012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 21633990 1250 21632740 21632771
    0x3050a06030b040308180d0e01080603100501060c0606060206040c030f0204090203030a03020a0905030106050f240304110102010b0a141203040905130b010b04060c120c060e1f02031006030b0d06020d 87
    0x82083d82840007d140680300404040d024441c2c00d81000d061104040004117552414014840d86042c540c004200642c0c40315005403d1b0007014105640552074081d0105240d800082c11501a5400101690015145549580781c00341c2c0340f02c04a03003042e1903e40480068038100058200303500642c9015841354040c42006000304001c0d13015030312903030400008101585881200c0c800c0041d0644800d03600211400c9154901c1450072100c58a200e0008200710920a6556040c54642000d0b4000c0c0300e200b041d10708000d8030341c50034000c0580c44490b107000b501041c0b4000550440214819003501e003081e54841210b41161000c54200c504200c0d82035620f070400421110785801350542d11622400c0a04213040140040300c05500100304108007858140c02328010034042d56155404007003844070600380a10143c803403c4540105d03010064503840151880c403107000380ca11881d0710703421440b07007145002012005040e01e134820350b0708004544400ca020030b0090004118a0391400800f1809902010b0000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 21635240 1250 21633990 21634021
    0x203090c0316091503081e2209061d0105041503021309021206011d04020f12010606030c0e030c04022a01020403030206061f0e0f0402040314100207030207030303050a06030b040308 79
    0x1c2104c1884400d1001411600568041400c091301c05510f0f02c0300090185128030407000c0d511212603000e10444070311034500360303100e00340c0b280800244111913551540c1e6440c2403880b94801402030840c0c2c01403285080c96404406a1180c00080d80240d60f9203401092a01241040d1304069603190002076003503080814540a030f60559000410281d0f03d40845001e980c0f56a110302940a117000b0046400d65407812913000403480b004080000440f00303c8072150081610707108400c0402d080a060320100c60040e96071420002000d0068101e0090344010030000354018a20040c00312440c1030013100c80b5031141c2403074980c403130402c0c00182e07183c0c2141800b03440d014000700003501c0307440390342040f00c05d03244080e21610f82c4c00094103000b2505401d5100050341d030040c00345001d4001d07201060001c00c0c400c00c0c0584511804803001901c040d8480000140d041c2d105000d40a00940d014020400002e4400d61204d9808050400d00080b12916580d0310041c0c10340a4030b0030780c005560b030000d12401da0121100e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 21636490 1250 21635240 21635261
    0x4060b030307051b04060905070305060108070806100507080c01091209080c0607080c070e0a0f0509030c06071d030d080601080708100504020c011d0a0b0c07150203090c031609 77
    0x1542030602540d109656045201ea0902c0b01e500c04d02e00b40301c401e85580e0030020161030b10344c00c148680e14001e1402002005c017201c409000582074404110150300a885181c003071070001d0104d43c800c12001c80161140e5201c210112600d85041000004000082c8504003600d07205a690400c40302c000e0400500906190300004207a0300b020301d02c60f0017659200210381e15268050351170350b140d0318211202401c0c00b5455100c2d0124001c00d10800c200185540d0100b80314040e85482003019883c0d0128103596030090801222580d8440c0e030215003c1c6001d503104403a0350810561650b02c01340000c2c0480d0030204020414804100e4203010b003c00c0350b80211071154020080c1c6410342c1035180000720303c000c1c10330500c03404e07002c0d641c00250341403184429000a241e01008403140070150b5046901d050b60b601032102c050750894600740110740e001d450f1740221940c00d03801a0a6200340c0441c0c0c01900001d6201510a80583c82903d00260081d101440051800601150408446494403230000e041d1a00da005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 21637740 1250 21636490 21636493
    0x100c021522150c0204020c0a0309090e01110307051312030309031d130f020403060203010803040503010e0d020c1903021806030c060406120207020604030803131109040308070e011e030504060b03 85
    0x10900c100b4080c8100c0100810b4180782041c031982c21400881d00038413403841c079204240664807000f414160803590400866492420030481c0d200703656416422110142040300f0000402c00c085005180320300090140013110903211079510f6561031100441100f02d5800702c02180c0c80d554001305060300302d0000b040c00c605d01c0000c90851409400014420405c200c0006015540c6e0b034010700c032004c400e41c1034401541d80034104660300d50b1141c0c0001e45c1c9030080d1151034440e40c00d19200c0510740d0b5000c9480c165040361a00100070b20f150080801008011100d000001880024000030160782c42034240c5402c1560149030078501e0410009060800e07a1035031060b801100208410003d04d6803080d4000d1009809000040c2c850409100185a0348910b40c00608948004000c1c80200f24500220502c160b01c1004690320100b8070005112514070b084901038041012000010144ca010769403100c1500e105241c2401283c05440409000d0607112050304c0005e95103404020401c00c0521174004502c80440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 21638990 1250 21637740 21637807
    0x20a02180402010816050f0703110106050301020f0412020f15070309060906120b060405180f0a051005010503130c0906030512070507061803080301031212050c030105100c0215 77
    0x4001070403d110103040034004196180381031700414440e40950342401c0100c401c056840c061418010300841c0111072441d034035403030071800048a00d8148201d6014051a44425003060703d0121144854240b03040c0580c0c00c455400c01c1c00c50255601101c0214200303a01e22419102d6900c2e05008024000540085041c80000901400b4107900850072440030300300c3d0711010880029040200b1080e0040d80e0049070000e00e4044082c07051001c062082d841200c1000703000c6038640c3d5950380388040d00c00c181d81030046881d030a142844903502c00c0004641c015400c3c401b228254031661b550b818294081d40c003407204103664107000d00400109100342601e4860018540d030601c2082c5c0c44440e100c0c0e066202d29418005040300d444042403294a642d0001c58010906039260341e900d0030403981c03008041d4038000c002464050030001c4030455101c6c1c01c1c00340020003c400d08580c00c000c10f1040b040102c40040c5c0521903a02d602c8030041c0d58100c48140e4050b206442c95072281c60150a822007111041202801c003403112 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 21640240 1250 21638990 21638993
    0xd1a01020c0603060f01031103070314070207050d1205270a120507050103090213050108010b101e08060103020c0f0703021002031608030a02040810060302010f0e1815090106020a021804 81
    0x1050781c4d0014012504800e0301040a801640200380b014804200f550010080110140c0c150740300c1c1350340b05031600f003c240c5e50f6079220080781c546e1060b008a0341e001e41c003143c907000810005000020449a1070800a00d4000014018920079113448100401d1880540000b011400c001c0c1c0d0820040c481500d40307484507000d554a00d41c1394611030061504040c1c1e1102c46d80c05559420f0316480680301d1250041045585a10481d8060028282c03a540948407042031001290310420b104042c00449644140e030003226200d0488202c06c01801d4217041640074000d0140c920810f2250f90140ca86c2c180052481614502c107016005980c0c3c1810000d5410038841500001500410f101d4032a60111a2555075070b10800c203400203010b0358105400c58410916103c800381c000741e101c50142c1c2c1c000d0701d030300c24012680401140c003121000011600a03442c2ca00541d490300a046203142c21003000700c045010003a600000c200d080100340e1140b80180d005500d400c2c29414030a04001c116001d0745444002494903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 21641490 1250 21640240 21640249
    0x1e0a06150e0d082503030605031501030b070e040e0d050405030d050403210c0804080c01090e070e040207060b030a080d0e01050106080708040317010605040806010b03010608071808030d1a01020c 85
    0x2048060f146601c001201c1000b00d103407000c200b070030300c0c2c0b8816910525401424000e00034006402a1800703445414908a25017030340c00c001a04a0360320860004c0259030711001100d0344182d01c081d840d0041d4460302840c8200009003d04103010b0520f47e906a12503180908061034805044d1b10700e002d215003000140041860040c00c0c45446d8000800c0360741c4108000e00454104400c0030700a030071120301203008103c884012940c0601034609a9800c0c1c00c1d66201d0400380c80910040e62044042503038010a00d840341041e8005e0803d040c0134141c00940e11000d90702080c01e04460f00c80440320380600055a0b0b56019003845100f22000250001304415070401d80c01810a940140406d03050044803000101010700c90180d0070040101098400c2e425655003c000c0c2054005000780c941c01e010b00170020480403090000d1300d0480e0810b81c1d4161464885e40800e850000c0d803d450500841803181012410040810080c45c0309140800001074892070f0018000b41d02c51905402130441d00312801604042c3d81c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 21642740 1250 21641490 21641509
    0x409020303040b1e0f1206010e030d0c080d020a080603070b040b0405010509040b0a03080903010b0d050703031419020a060c05070c030305090d061107120f08040b1e0a06150e 76
    0x80c03510b80f45a6504803960241d070340b440010382c01607040b4800038800722101c00c040060091103014003030b0000725846079401514500c4000032416090b0b40805021a102403168100d5540c40303004142e00e915100c550024041a81c1c801c2d0303014808904540184441410100500ca005000181d050f33810141841051090b0b8811441054104800401e20036031070b984c6e99001c0d402400c0000d01c10000310f0358a14003d802500404540c0e4469464400d40201d01e0403d241ea003001960301c06c0103445200c1c19507a06890300d24840b00021b8a0120920039482082c22201d4602c031a0380c032a8000300000d1f2503a01e000010754250840c98800c105c400d0007548009101c181144007560b0380350078a02c0d11a10350f880810050422400042c4c03c66040200b20317400c01e4400d90003403c503a030017042c00c41c112058140f402c1c0c3ea10b0344025070b0f2a0028500d0340004c0c0c01b05400001c0340e07400503078a146403502c1184031181c0e0b14240c0c4065031540c0609981e0741c8108041c0190f070b075914410a1890601002d092580d4000601c0c401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 21643990 1250 21642740 21642749
    0x10303080412030b0d0b0402010e040921020a02030f012a2c06270405040209010306050901090c0b0a080708091b0607020604030308040b060f0d020402070c0305060106030911040902030304 82
    0xb4503400020034070900903005050048006803040240d40c00c5c07070510140c03c40003540c0590101d4046440785886040038010f001143d900082d56054000c4040c0c524842c0070140301580c801c41c02462010001a5414080a600c95440300c1c000f00e0300380e0140d4050100000100158420500143c1c0825042900802a28144844e02c6884c00300c11240103a294100c94008035190b41c08040042d546555000c100c0800009400303a2304107164806071201807000b29142954003a600030301d11801080002d000c0e40081d0390000c4150000710320400d00e03555140d041891900890890700001c5181c4c01110b6000300a01d61050591a00c81003504020441d2078860800c00c40351280e074400701140340880e8868004440038941d014182903540c81c0d0f0307030030020300c984020348044554285001c003064852a00c0043c0b406d44010007000c0c0d241d003c1042e401c02000b5444843d084482c0003152800001064060140710700030700c2d5585020854080902d08925121242b6410a10841c5803004403030140c0c50000c15542683c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 21645240 1250 21643990 21644003
    0x60601050a0f0e0d0b07110c03010b0307030f1b0b040504050609010f0506090102011b0807020d09080601060822060b0109080105010f0302060a05130906031203021e0d0207140601051203030103030804 87
    0x281c00f00040b034407569000001900700d01644e0144203000307074401c9070300500c2c0986c041035800d134003101e00400d4240d0381c040e00050352582c40720340c05001003a104540080b860344152040000f16030704003820100450340b0390000c4140000410200030b070b400c00e0701a9903405441140e01d40030325810421102000815030003054001d0002082c2000350340d0013584208001305401414180680655400418808040780c1a80060180141071310141e40614034020540b03a64070b01412441e8240307441214808002064400b402000440c00300d030b0302800c119160320990240c10089201c00032480003501041d040e900c03229450385403000410002501c41304040c25690304480d615a50401281e00b21154000e10603035501203941c0800000c0c48840590014085038800c4e5000c4010800c0300100354103d00420f605d00344243c4808010b00b01900000c0c00801c2d0f50b0209800042c1041880d44814400d40405000c0a6031a40440014001441d0030b28151000340400c0d03000b946190706569004104440141000700303070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 21646490 1250 21645240 21645257
    0x6170a080a0302090a030f0311060106050a0c1109100302190501020c0603060105070b09210f030a0b15040603020d050105030d050720220c050310030b04020a03140f060601050a0f 78
    0x85074032a070112510184d00401c144032641e100d0521070450341c01030038121b01080c241006003c0302707030011801c1412a04581c0340c0a062008541c000d91720b511041204440344821000d0581c000e81d500d03c2070a0140c01908c1c20356402c40c2c1588107000e05611002440440c20422aa04205613a80010002c002c0b2005440c140c1c0c40c3d4030b91a005807103070300035140003d2001540f4000c1000210700000d9a04804001038402e0f0004000101c2104061241e9004080d00c040d0420010f9588003054010481d1100c020701b5450071f450a0100684454109402800c00240c00080c04402429035004150141204401501c010300c0c002c032001e04144a1107400415442c0e00600b040c0d00c840c100c01015841c0c200142900c140440d11a8038480f50ba2608141110100d02d0180c80e8036080c0d11900940e44140c284400c04082c541c1503884090503200b000704200d910215800c0b02000081c2048150105440420000d140c07281d035150006040c59001000541000030034810310301c00c1940064025000703030040c1002d01e40b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 21647740 1250 21646490 21646507
    0xb03070504151212020c040204060c03050306011110090c08010c02030304020d05010b030303131a06031e01020d0e0312070c0f02060304111f1106090a062c0604030306170a08 76
    0xb50580d4950142c2d8000420140c000103101120188106100c040c1c0e00752030140840310104001c90140d4003641c3c000a20a20301e800c0024040c8004540050050401409109042c84400d00e00ba0081054030718a549650038041008411b0394103501908808000f442041c004c12002960303800000e0006e445181400d18250034082c0039070088680e5080a0152580da15100d200c8200c00b01d0004000c40d10607920000c14201d410001c1d01e614041d207001805054804402a1542c0c2214101210101203550810000340c000e030740b80c45284070100c03a0034003071134803000c5004104100800003080380c001e002da603c0040300026001c2c1d10240c403035507048030441d0300c036111400d16aa282c4486544150800340442060148420b500c42c0c00c0381d108400d9030ba81c42d416030641811911504207580741e05642c7d1040542c0800900c060300b1650306920402d18980b10380c07840d001c0e0500b42016050030001c01d50420800c0c002031560500664016084a030488400c0403000c9070313030f15506c0986c0c41020b445401701285855 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 21648990 1250 21647740 21647771
    0x20403080d11190302030f060d050607030b03160e06120d08130c03050105130b06180a09050c03030a03050907060c08070f06060506181017041209030803091b040b03070504 75
    0xd90300030b04403191410803030030f01d07002500941c0151a41086e4481c03400c0002d000e8542800200e40255000c0c014001d5038446100a07000b0b4903030201681c0d030500881c240d00126500c0103616900500d0301d0f21990002c0e0500f0824410042c04030410a180c60300496983c2d10555004902981c0102c40419600c40c44101403c040c4004500360b00018015420041805445c4550001500929000b400180101c0d100c11042041e0b49804a2040c80d01e6490700c40040d0302034015510018a150103a070645146a01d0703000042e00316030101c0e450b40c0203c0d580c0c1c014056105000c10100020b40410b0404010120f10358407880d03802e0007000001000d24098650440400580341c000800406000d8400c079100c00c00051001c0d5120384000040b801461039003851280d4901c00c041c21503401c4044040c036001380e112515440710401c40f459004082c00010400040000c0c0030000039441150450090064515440000c09a8803034546944d8425402d00c0c400345003950300485c940080307607421540003655a6189141c036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 21650240 1250 21648990 21648997
    0x102040f080105100b0307090302012102031602010f0b0d0803150a15080906040c0e0c09030d090303020115061409220203010f0609080d0503040206070c03050f0d03020403080d11 78
    0x200603031085294009030700001508010300410050042e042e5580d216040b948107804100c4c0c048002404075001000594010506030524010320764141c6864411078900e2001d0740e0081d605c61640b880c00d80e01d50f13590076034203104000103054801030601800c044240060a0740849403405803a00c0800404500c86220f00702340e000d442c51014040000d0705559140c5401c0a5860b40400404a51030200141200c2404500c0d14481c0781d2048054500741e050580c03c900c0e2690080494260030810090310303005640400403c031514480d981c0d00c245680c25843c0c001e007036071842d0f40c5480c0822007a003c20320206e0f81000e00300c40103800100f1615101d04150300003030007045802020300510400050007041286468005605036400544418600c0c0d03a6003004a4410001e8070484800390084244400414400e200850b04140010302c07580c01d1800c191203e07070003c01180d0040310b00781d004d4143ca4428034024020344941c90454101142001c1c40c6440740c0c0d50782d01c103410002584503507a40001c2c0300705040d070066 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 21651490 1250 21650240 21650249
    0xb060904090c050a0e010b04060c080c01020319060e0403021507031d0d03060e0408040b07030c02060d090c12080306040b030f0d020601050f0f030c0907030605060d0605130615050309010204 83
    0x74000038040d41040742e81007541e030080c0d6000703440001d000300d0b909250b02404d9040321545040180b41c80d01c0c2907003c6420012080341100e100314100b041c60565282400a1801440b03140e04c00d80400700c3c207a15a800721031040e8441c2107010030030402c200c046500030811082e082803030000c5c80240ea403030381005c0b001420080d035620600304c10101d100400e500d00155007008103040751020440707192500302c22505100c003228020b0040200300401c0c0080c034040f1028003c0244681841c21108540c1d50004005810800c03180e4031080d0764002d10700610466041100060414054000c0c60b40317542e071141c0310103100042042c1d005948560310384d201a20100f007080c00305100102a220001e91898000f52104801e115a17480380041c20348024503032400d403401203060940240200340c2c2000040a100c240c1d40700a1242d001d06644520008060b1a03860060110680d00000055210308001c104a15412400d01c021015407512030309220951010b80c0b440442c400504089403255a002c0c41d241c00780c41190003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 21652740 1250 21651490 21651499
    0x20307090c05030406050a0902330a020a02031c121e0216051b010804060506131d011d0705060c120d0b0306090a0506061e04050103081e0702010c02040b0609 69
    0x401884880e80320000e18001d40c0720301170074052611841301100a8490414029500241942040c180d220b040142000c038180302402c850003070408401c0703540042e0031503c010000340c2c0050354418110314040c031030100d688800c25500a0b0b0b40010318401070081c40c0c61000902801e599080c00034548901f54030604000c00c0071030003507543c0c100c50300d828040300d0300040b8115600d101c1e50814a401203000221030302da070401a56142150b80e110f031240000b03050050b18050b00b058082211060056241c040c2103214016003242c440c44407401145603084400e50811800724110402c4403101c0090046540d108441003124071945600302030201e58284400600c20000707a210000300c42c9003800c0b4070307080001180d4045082c1d51503603880401181c1c5601c41024001c00340d0300084001141762503c0b001414044268482b0403050540d08000304049980c281c0090300c0142001c500c40002100c0d411754031041d0300034600b003641800107a80c00601041450b0030300900c01c13920f51000c030680343c4a03682500c0c0103110040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 21653990 1250 21652740 21652751
    0xd020405030604030e090709050337050607090b0f040501080603150a0605010f05180103051b070c0905060109060c0312020708070b010e0604090309030b0711070902030603010f0c020606090402030709 87
    0xa030180c02c0076942e00105d40240507240004030524021610740e01100c0c1c0c080d02802c0780c05c034000010758000104418903103040e8804060745041d0021150001805446440284114202000b01501c0d40303020b03500c080715140c000c005602440c11071409403022100c083c20121616101c00c000641080005581c2220701c002c01e8042040148864010310110b40c000c0c0c990b400b41c1602088116024410351000e410000302c044140c0106520035840700340e0080600000c01c0d008640009000305940c8107500940d084407004605225450103131055641104003402c0c4103003450300c1e19002800094500001505200516050003c41001c6804071090039612881079a0b907600d21307280411200d50280503aa03000710070b9400103449820513104550752241c150301c40c06181c528560b2a02c50000c0e00800d00400c011458070a61409030080201001410103c0300c050303143d00c0d14005150840d841500c55400440c104200729000035000b00325150800c1040d944442269601d0021915106003644001951494031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 21655240 1250 21653990 21653993
    0x3110f0d1403250c02040506090c090f040209030a0302010b040617060c0a03090c0e0406050a110d02030c09060408071409160302071106030112060615020606130b030a0305030108010f0e10020d020405030604 90
    0x10640f0318007171088400308100d88400c81070180b40c50741150030503420700c8104000c507542d141000e900703144128002c00c05407900301d08102285c20880c240c58200c0150391280c1c0001c560b46428025a00542400c0d51f22803500070802d000140c3c3ca40010740b14000145002607074405640c0319800c006010f40d0403082c0340001c1c03030b980c040c9144188030459058600510b0203010030401c0c030190090000f100c250030012818003e240001d08001c0d44084e0000f0810801001000b1030358507030300c014200915103c0090145140750034000e021541c1071486407840b601c4502c007040040000080c402c00f0582d0180b0700103890740110714080c1084d140c0101c240341e110b1400700000800c18400035050820358441d001c10b000f2595107003460000c1049850164000d0b8105030002585410310810300d0444121001010460311803150100341840020b040960009000200600a40d10240250602a841c05000300000504051600c1e21010f17002d86450000350001060590031200e50142c901034035006040c0c60307260415 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 21656490 1250 21655240 21655247
    0x10515010f1b020d1a0604061a0a02031209010204030302060901020c07030308060f0a03060c0908010b06030103170d020403060209010f020d0e0f03070f0b030405010c090b071106070f03110f0d140325 87
    0x201710000c180652240d00180403410b0a000b43ca0480d09c40324132031081295400030040040d04901100740c01c40c0b100780907415046c24041c5029000310f0f101c3c4001038cd03490a506009003030840080c80506a0707070041080b40c140402c00503010f8203ca130546031401e20342d140c10001800001513040d02ca54050211200442484495171203c5004007550f101c190245591301e041c10309803012803106540c0b00d94240010000f040c0d510402d0381c2981041d4006510b44500d8010b504126000f40e0020b881c0d9543c0411124000d5070060320205040d0058002010010b01002005040c509501c8425002d6071200c2e9102c2c0c4591810400c1b00050719080c8204400140c441d0004410f80e002101c042c0c07151740c20500300c110341d00e00070700120f0f0658a1582c0e04910f80507886e19107180241c0c2240700079801c40400c01070040412028204280e1042c8290340e002c14000480d441686801d04080f602c0d4200e4110002108000c2d400c0007201c442c0d2680086495220b84d10320b100d1801943c4c0304841d803c5d001d87c4142d81c82819561 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 21657740 1250 21656490 21656513
    0x9060504120305010503070b04030602030a060f030303020903010c05040b0d0c031112150607050d0305060a09020301062309030709110412050601080d020304050a03020f12010f060503010515010f1b020d 88
    0x1c035603030402550382c0e2602010f58426030362080d404414003c00c000d00c0071a2158000f968840a003140200e03034256180c0d21b00c3e481100b00da0060300000d41c0072420122910302800f401c00940d03824600a800d240c10525210300c43d120310020413a0315981c40110300c500da402900003100784502503440c0380e210014030008100c20301d000c480d2a28040400680003105184c00c10582d42e86d150000024022018007450a4000740f0303000d0304550780242040400201d510403400258080c0c419640d0b4044e00d42215056040c908407501c43ca8a48444140102c02d8603490000340170003107555200d808210301c0f210f000100c000348201d40101754840d041042c80000d0000002c0e03054121040c03402128240d44170380008070b841e801103000721076204c180030000b04058a0320214490705000010118800d111000d40a982158071005584003865103407481084140340a22915501090f40210b4080e00d03000000020840c20800d006441070110b5503411010800c5070341110041c003580500007400044041c00d005480c1c44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 21658990 1250 21657740 21657773
    0x6030c15130b0a0801031407150518030a0213090206040302101e0e031507120e0601080f03030115081008030309030304020906041a011202090301050a0608150c070f020409060504 78
    0x35520000180310880ba104888444074595190012070f4215542c814400703800b410010950322420001059502803c0c0923040c4550b2203481d000d580d1848503039400002c010b1400d42c94440c3e0460302882004d41c4607020091010f144010002480261620025215021b1500081e410505000f002d018483e0042141c0c1400e104803005800d04400c002001c40311045c0c3c000070350b40c25400c40d80502c03034030518241d07115030441081d080a5442e925480c40440440780044002e14955010600412200500b8081070b0ba220601c0b001a500c1c0d03605100e0019440407a8060302400c202080c00080ca03000d441d42000d1002e01401c3e426a03959081110207165070341c2080e1011f905c14910340c4042420b034685449410004101c41c00f008040f420180019100c03e44c104c0803240645800f040842c55554080c45850302c12002c1250006070f00e27003008601440d007600d15418141007590841403203030304510002079074122a0b1242c07903003035250003510100d03025010341c20008140d5401e02b03052204204c40c0f508407540c0704 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 21660240 1250 21658990 21659017
    0x1c110301030b010e1302010305070302090409030c03120204030c0b250503030415020405010e040b04061508040c08030405060d0e03040f090b0f0301060b070f050703050303040c080607050304080a0806030c15 90
    0x80c2d8031104c507600d24a00507103040302c04070340c20560a00154025006280e201c1d1071810b005080c81214400315041d80c4009804a00155030212078508140d0000c100c1405090b8100c02103040504591310904515528018800441000318000e8603044030001c00340400610419004d0003040745180c9580d8a42055070101c84490200264448840003071080e80c085480580d640c13003c1c07040c1202400010704000007a0b42c0c115880341404280c1d01100c0e03401c100701d8001a41c804d442460076080c070420f031051582051100390002c0000308140e0395402d003510101901c240000410303500341c604840c6180701d00c0c2e1100304074600588001566441e00d034081c2c2103052080d142c000210703546404040c200d07041d0303008410300da40302032000c0030109008240d450b000302c0c850004c80344240d0702da488061a5400c1145c049032000c00c200b0003404154010300409800a0043c10181c0c2141841d41c6d82d03035402c0c0100d082360170401c00c4081c0054119079041003007000540001c0c080b849459400304464030b01e40d01400503003901 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 21661490 1250 21660240 21660263
    0x607090602030a0c02040b0114031602060604090f14010f051006120507050d1104030c030b18010c120f0216060c110309061812010f06030204060e0601090303051c11030103 75
    0x40c1d0000c02280e0000c5a00d070b4071601030700c8243e400c110081c00c03c04e50140c10024015820901103031040300660180000010f401500c01d40e0402c001d03d05040100302e81c0c021814800c40c40005030008103c3c42034079500006400b043c00c88032403098010301c80c0103154142a42450144031450002c1815141565001d40c4c1e41001c0001c0c5c0e04015058a5041e100d0301c000034420880ca02119460394002d020104650804071b1a06075170303071036600452450388c0094441e580180c06000401908000b07521704685001d0090005100f0400090624031030b84803001146c43d19a90180400300c0c84e6412144000d50305808011003070020700f81007005004600304c02001c2502c900e081c240501c0c0010a81c0c9070004002c00891622400303c4003148242030180b001600301b03040d03c4e04994000300030f01810800d0350780d4500014280c0d18500401095907210743c01032641810140034803850741d90104900e41039036010305080341d80b000c41c030003511180c115199202c06410320741460030440a440e440258100c0b4001c1402d5400d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 21662740 1250 21661490 21661499
    0xb01140405100608090a0c09060501111903050304031b030c020103060602010e06160e03071e061d040515030a0c08010e06090a03030509030706180b0108060c07020f0607050f060709 79
    0x840390142d9075403030001c1d07285204101d0755204145540c1c0c4a80d040c2d0580d29000c1c03032a1781d45604810250445d412081d25082c1c01c1c0601e5900c1044070f80070f45030100080007840c2d540108a100c1041c00440a03081020006c001402c0c035000d440300300c21403046210885001e0f041810020209482d514040380001d00340035001410354414042c10b60600d0b0140c000c1c10290700d40100c55400071184048410031b206024400f8a1650740c240901001080b40400d049030100d0f041200040b524030640208062000805040070003084c03104044116640c1910f0018443e154240c609410700302e07003040f06a0500c522213b40b405c101401c00010308490013800240030850b140940161550310846182420f03901030000311010902c00d4002c10380142482040d00e18000701602c4540907a80600700c41c0540c0389050013000c0400242d84040c9004284101c054042030400c4180008075101d4081e004c1d20404900c00c85c03441591340d120441e968254860200c610884481801c942c48000441d00c0b80c9c007103100e0180004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 21663990 1250 21662740 21662749
    0x6070f0504050102150402040f0501180615080f130c060c0c05150a08071e0302040302030609070506041701020d020a090e010f05060409050a0207061a0f0a0302030d200601030b0114 79
    0x41c00d49105802512a200c410b50714081c40d107000401c1603900c6911030310034640075646031140e03078042c205610030369104424030200c140031b540d5942e10031440c0f4101516011f100c507a00812160f009817008210150540300c030183c040c8403200400d0040c020500503140026030682124001050501c240b50004c0f00650307038020000302e90382c000009000c520341000107400c4c45100b0740d000e82c1e01c240d140c03c10468410705a810b0344041c0e200341d00780c17001003540050309005502e003c100b22a0b0181d80c55004088060138900421300741d0003030740315507044041c55501d10001c14a003074042c0ca5a00e108804215142c0e258054002c0000b0028829902d01d0b460030f00010a042e80e5501440301038400181c001890503180c0386085000b03150090000c00300035070130b014000c001101405196068030780c00f4442c505000045003009001e100d0031600c50700c20740390400c0c1040161008111500040c8080c10310011074003030070000b0081a040038081803554056540084100408505440e050302c1510840c445804d441d0030500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 21665240 1250 21663990 21663997
    0x501051f0e0408030109091401060e0403080f1015230301050906060304050606010804020a0506071202010b010e01270b030906071416060902060f0f1e070305040308030c040e070206070f05 82
    0x141500800300014021401c50703407c032001d040d1042c2d03084a030380900260f02900311240c9d0f80001190301900b000303010505a0188071250004101c0e440a48941001e249040110019100308940d010600d01900c0c07640340649802c0c00140f1035848090340e40d0b1558944500954001d000d03181c0710341c0e00500232814a00f00b881c2500d2050368803500800c0b107512810010b44a00000610899100c03c4121011900c3d86800019200c4207110b000d003600c1500d00c5010107402d5038102288503040003045801c0008582c0e00c9082c0d040e1500c00c07045403458100c0300d50702c4500844001e030040c2c030070804000188010040e00150762440f86625070303503110b0b40d0912100b41980314440c4448542e039107040d6094440102e1000c1e40607924480c402007005140024503007041426400131b40c0815060b00022662030107580040010542081103100d0a5143c568282d4001d003903800355000182018001000090400c0760740400c0380e014081440852000c0d18081000960300e040446400300000d48050300440040d0041c400d0303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 21666490 1250 21665240 21665243
    0xc020a051e0303131707060e0106060807020a0813090c090e0a050403090506090f131a0a03031413030204020f0406020c1203031b0906030f0907082406030a0501051f0e04 74
    0x2e140745490302c50300903150748903825042e2000c080b8256203001342c0c01c403800180002032150b18082441948004101e08491441d8401400d00c10001c0c01c01440344c2d0b02040160101d6406550f198030b41c0b241e4603980040c040d85800260420b494090f20100064100c1060340841c8c0c08a6680074959413000c06070425280d00ba10010041551075500b40010720340103002d80b15058018120042010b004000640c12049a400c0a01c072595118203003030142ca600101100081e005940c0c0c21003503483c6a41c02420b110800390040c1c5580d4001c42e0b1504000e41c141a52001580c006105540340c10004003640f5896110303200390005440791403041c410743d060400401c0e01d801031610207182581e84d103011041e010703030075483c2d9124810020011861640e40340000b55000b169000c507a10264540301843c1440c2030b00a406c000310f241d00026082d183c0c0752a04400c1c1d201c2c444841c00303541d800c0e102e8001103450081680001880381d400c01d010818003501340c46844500c840201e28030b840b80c2d80d90b03452000b000b4105880 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 21667740 1250 21666490 21666493
    0x1204050109121a011707050109050d020402090d05060406020a080f15010503060301090f060204060905030f060403032309010506040b01050a0507020405041106030a060501030b040b030606010e03030d0c020a051e 92
    0x1000c204580b100500d0605540c0100040c6107000e00008801d44155026008424410380c0e01c85000305c4914100403180c05002c0070301304042a181400300140415004400c024811a000110209517446442c00e41c1141540a012a2880d00700341ca03010020b50030503c0c03003d00040d00400002c0783d000b01e0501c1240902603110750301e0041148040110307420741c0020003c540540d2108041000680c5640181c1003541c01500c0041e200c505000b0003d100b102207a1029201c0c0d0300c10792405400d90004a5100e4104d5418100002c40303443d030814442c002003201da11910422010000c00c059408190046445640111410056080150015126400ba8440b2240060804d200d25001410703e9444070390020b020b11074440262110000040d05a441100c40a0387d90f9241c84040285580501503000561422901486811080004a6034501c0000e11041c1000140c0318444425101402280c42c9481180360078030180794a400060754070b103000c00c01262284a0400e940101003046144008011403210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 21668990 1250 21667740 21667757
    0x905010516030e03032106060a091401020703060f1a0a0825090207030f02070e061f0e0a060201140901020a050301060507060204210b130209060d1109010b070512040501 74
    0x4540c01e041d66007000c0c048090000c8098018080e603000c101900c0140381d8107031643c03043d54a0b035601d90b00c090310241109005075410703c0700803c200d40096202d81600c82c1810400e60560310080102c0c9420002c0d0b201820030341c034040020000490640049100400d00c408143d4410400700c1840018141e5209003405500080e81240340b422036148000803010320750903030a60007074890602030100d0313103d440b044003c582d03480c11115000b41c0602030303800202041403020006103030003030101e004a9080d402030324050250840504000e80a4020361000f030401804515400c1e864070703400f0740200701c3c000c00284020311039400034044540500840312070800e5940c4d00e80c02c69207080782c203175025007203000e04951587d02444003044841e41202c41d45c6102c40c0461412803046194200a400808040c1120b107464144171a0000540c5030807005640010083e212000c50704100d0a00b6040986600e606980c840c040400004040304020b0281c00018090302c00c1d101500102109219148954418140131542d0310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 21670240 1250 21668990 21669007
    0x50601020a2001020106080312100f05030d030b01021608241504050601050c010c020102040e070203090f0907030b03010f0507023d0908030702070906050109080606040203040804030f1101030c09050105 88
    0x2d900059420043c0008110b0b103407a40500790650700007100c40c141668000c01049088450801c0480003030040c440b200449505110100c0e89401251044a00341901c4911314502d6910030030141408442c0f004a64244544030000191a42c2035008041d200c40715880038024617515000859005d4030384a03404143c90b402990900024040045c404e9052020900c61280520420300540b59050f125500060b03840f800e15288242c00380000d800142154001d00840510342c54580140010381d400722010455582d92002c00c0b005061459111030b095420700c01c44c2010300005402a600861141c0c081d0341003007801c0078100116054040080003040b00d058410010700c0e01c1d904c400d150401b2000ca0204490203552607225180d8400e94450f00180e0140008202310701081c45034401404d024608143d00c1c1e40b92901d650303036400d00501002d108136400001f2504101c40d0504a40040d82d01c204480304001c042d0400414003050708400c0d90100e4280405110300b031348140480b20980d08140c48950506080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 21671490 1250 21670240 21670283
    0x904060504030314070c12050304030f120204050d08090301050705070b04030c080f120403111209040515030d0504030b010503010203040c170c0415080f060601050f0f070b01031104050601020a 84
    0x500705034281a9690050415100c02100d00c40c401d0940d0345950014080624001c1d41801ca406400001c00500b4018400000c5c3e02004450940900c2e2030007200b14103a102e002c0000f44a503074005648451020b030484100304009000e8131250340220700801c52a65010001e4070f0034864001c004101c040001c0c0042e00082c0a460140d030780d14050860396007003c4900d076000c1d42790362000800444003030707030441084100740e800340b00c0100c02c0240074081c110000154044564170b015424566115544900001702d03051886101c00013040001403c80e4840c8041460107065075009000564070550124000b19150805000f00c0e8042ca90149000708058544469800391407003800a43c115405024088903e41d80d441c01002c01d80300c0224403410352245012522840c0070741045401c04103400c640304200a580e044010f0340d4400940d84052950b0b4218010725801911510100412050072180040309000c0e050140005080c0283d60400158407034200583e668451040020070a202c41e184100d8034805 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 21672740 1250 21671490 21671501
    0x3040906060e03060103050c12072309070e030616050f030a06050909010e07050103020702181006030f050f06010e01050408060a0906060801020304020306061306050301050a0906051803030f101203020d0807030209090406 96
    0x40c4227096400392503e030f0003161540c0c82204040450007140c1101c1c07030840e103008502903800c1040350038070b9003410310b41e980480d071260f800401a69141d0341650720148214010011540083c100c411000d0b80c2c1e00e01410000002d01680c0a081e011f40c0d15000052021a01482500080c40300c0c18010b02c1c0380c610f041e00450203981b0061040780c101d001d450001400c41c80b001080da015141c0e07801102e40f60b80c140305000702220401078000051307078100414441e6500804522a030801e000f032811981803148003005039031a210b81d6006510512800c403c00040004c1c50b445200c0062042001b40300050780c8040d21400c1c1d01050700d010354140c21030742c04642940b42644d04045010045000030807050b0303460300041e0841c1d1044a10f48485500c51402c80b00b00402845036550105140c514150207401011146590340401405000940984004150014403d116000090420094410401d6041e140c020f49501c44603200c140440d120383c1c0820004c0d4001d0096800c400800f81100c40326648640b0f58130040d08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 21673990 1250 21672740 21672769
    0x5070b060d0204141f0b03010b0a11060f041a091c02071203031a12070b03070e040c020d030501090605010219020a120f110402030c070204021b03040906060e03060103050c 75
    0x550072600016203460007001403407510202111070318130300856064014a074040c12481100d980b102c2c00e0280c05510015070341540c0c070409036503444940916060322a090f43c0030400185100314001c0002d03882084090710704c00e80c46001c40740790003074000420001600007560102140c1e084120001601190142031100c1c1c0010b0303104480410740d90f0201b118168401d0b0700145c00094562882041d05040041014101281a00c280c01c3c660b4102400340e4032082103000d0900c503c40d0000100303c1c2d2920078481041480c40042040050035085d10b006942c1e4080d00911328003203401c090001032040e189104002c200e034030603000b45c410201142c50440c06601e2089080f640305011802c0854050504081c91400320b20074406115000c1450401c1032800750034001c02c501c1940108100003030b002c1c00c1c1007a00c40840d1305490142c2c6402d0380103203048207141898148010780c07001240018014801d80c102d80d085031801c3d124148030070075527428582c90380030900000e0000d030300c03000c0b03c6031450400c00c11041c0f42a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 21675240 1250 21673990 21673999
    0x30f0703150e07020d110a020904030807030e0706030c0e01020606150c070e010e04021903050a02150d0f020306130515090405030409020d0207031202130b03060604030203010906060305150705070b06 87
    0x72502d412040c80c0300d000543d000d00042e171203a400004406c0d0001e0301c110b55885580002d00f868401640095280000208010200202a0040f60001c1d00030340142c2144443e0006444205444200040c01801c0c1d5002d942c0000f080080342c0351155001244880c0a40805030204280042101000210758441c80e14205584110f40001880c104509421800b0b00307000d0038a9407032804e040c0100903025600380300c1445401c070404800c00019000203041104e9075410b951031504a108550408042c0c0141038031000168100f054022848203103030300841c800c4108030350381a01d0b1410380701e0f4503003110402c403042103100070301c884500e10500c0c207040c5081e0310912482c11a440c154861940c8c400307a0f001044141d040c1d9170042510001c06401c0040c000385000e250004505000000207200c1101a8501c15541400d00000218130a900da41080750041c3d50090000d100c0c0800b42c3c44c01c02e0041c0428402603409006942c1d044d00640035081000e0300403081036448030f0400d0595281c00742d040170080d00c400ea20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 21676490 1250 21675240 21675281
    0x60e0d080307050c0106290a08070c06020903060f0604060914060904061d0d1d0609010c02040204081501090b030106030302060a05100512010c030506030c13090602040b041e0b030f0703 81
    0xc0718424011b01018012041c1c10a0150040120340050702c04894444403d03044140086204075600012141d40b0810320b10703180c0100090382c1054802441080d40654050003000c1c100021558001c000c10301541c025201000b0495448170030004a4483e407944585030b218600100d00c1c03928014645076005401a2030004e01c0180014202c4030300c4a04919081c0541c201d110088241500940d090180310294000300d4203c01c1e4810015180c3d208000740f16050100000e50f08055490302e90650f4040c100c1c1808440740d281880b1942d81520009100d1a05883d0820341e40e8401410107000710750403a0b40c5500200260785502c00c2c66000742c80028444881c058460b407000509540d42065600010025400000c5d0040c01c0003009050b00c40040c1094000d40c400480d4801d545c541c0c01208030003800702b20000601c90b9003450010b0103480386501202c00d0343c501103000701e038692000320000700c0604040180500d140c7e65400480190000b240d000e04041c501100082916001303070009904090342800341c102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 21677740 1250 21676490 21676507
    0xa020f13090302060106030e07050901050d0c03080d1d120405120a0602030c030405060a05041203020d0216081213020904020607030203090d030f090602030301030b040816060903030902010306060e0d08030705 91
    0x454469401c1680141d20002c01048213075014800c90407919804006007039624140f902107229540184109c3e8002e40c94401c1d40e200788800e50300306001079940310b003d085c3e88104d0201d112002d41500c4030383c003c4003031400640d8098244d0001d64034000480e00e68030a8102403900040250880380d0b00016441c0340290300004001801c1c41c401144160915038881d9243d041c40d0034958074180d4001c11802c46c003480c02c0c080c40301281028804240c454580c0c0b50159580f5207400421010780116101050725031070b1041804200aa5030026100035810201c4907243c95450000c0c95240365480040650022048e001007800b5040500c014000c041c040d0041300d2510341d84901080740c01410040940004403e82081c0d240d960b8461507510007001c1078401182154190340341c0403c60034016200034614203000502d035002210783d10b200c011712074000000300030310001d5003009009460015000c9000070725140c400b1400902506100602c144007400100c8280142c0d9035402442d80090300103001e00509004008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 21678990 1250 21677740 21677779
    0xa06090e0f04020310050406020403060f022a07050307080f01110f030112060603020612060a090614060d06050907020708120a021504031209051f0506061206010903080408060609070207080a020f 85
    0x81c007c80c42140010b03911840c50030114205c0e20b00d0170140045600411080f8651403410950030700003500c0c0700ca00040c00300d420200d10b14100c0140e1040340c160050301d50006004502080300d8280840c2c4c04001e0010407443c00c4000f4292007a0058a00e11000900c0140118402d9842c1040b60b544544da0008003039840f500040d40036001949041440c028002c10020142040070010b00100381c03411041c4210b60600c460400c10141c20071059003c1d0802154000c80d64065030000002024050550380d450704001400075100c103654003c0991070302c03902141924042248080b200c100000e6409005142c4c103000c3d0300c907210007020b00240c08204021120181e03043d2103110310794203a0306c074030f0080160a5442501000c0c0c03035148140986150700e17150422210792200c01c201c410785401420b59040980d94600160788103500c54001a140b220081400306c2c447c5000210580212011203040f100e60741d880d04226903980143c01040f80540041e101c590043c2840c0d00d41156455004200030003414482842c3c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 21680240 1250 21678990 21679001
    0x100e060712060b030109020c0706020102090315040804051005070c061d04020d0e070807060908070b030c03040302010f0f0b01082a0901020c100207061d0303180409020d0507050a06090e0f04020310 86
    0x301c6c051540000da10300e0758503081000b000280b40b28002582420748080001f03032140c400b8404c00c01401d1800c0c0c0020f003013103d2401220080d14000301b41d40c0008842000c0285240c0060004450240710f0010128001c0e00640003091422020a00d01c0c0144841106001c0a90041601140025112071440001410a02c609005485060010001207151100c01403141c3c501e5880703c00c058000600070301151002c001242d500c0044c00300d502b0303529101d51a0480c0140011603807402c1107860000c0c5151008200d07004062110300913a2909101d07107458110782c0c1c1981010f01c80d821003800c07584c0c43d20060040803001d041400d40500555000701c0003070f008200e03400e030305909200041c0c00210003406029006030510b80b02c0301990140b0044040c0580200c2d6592060140390404116034041c02d0b60b00b50785681105008690181819104039910300d0095920f089601640e48110403008021503c28450050202113605c81e5071848100e40740e10000c421104030142090360980120b070030044201c07200740900b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 21681490 1250 21680240 21680249
    0x70215030601090e10060f12050703020301180203090a03081308030f0f010b070c0b0d02040b0d060807060309150c020304050a0e010509010b2d090307080c03100e060712060b0301 78
    0x20540e581c6441c00c001040000240c01c000400021003003400107004140c41582e05803901c500701480e400201c51026107030010780e410b20000640c100010001d50030b80c95000795049030a21034490075940f6405001c0400c2e400219070a03501a40710402010200b072140908942060104044000c1100300b0307155008150310440e000c1200d440f0410034041d101441c500d06500408110080c2e509244481c2d5030f100c0421032901c0f640e00701c02c1001c140e0300c00300d0354103078111001404030620300341d503c8280e44000009491a481510524005d00c100003c3c001d000e40a6840c3d810350000e00c141180c07052101150040c1040400402188820320001c41c40ba03c9442c0c0110160004c40d038020341c10741c0350a04204e0814016000350b03c403400103101c20403001c41050021003021002e601b40010100da0403520032054020022950780c10f01c5a8600001c51520104840403070003001d805880b07490381d4400710002554078a0208a405512610015100c01d201d500003a2400d11503600214125a0307640c0c08201c0ba0300203811 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 21682740 1250 21681490 21681529
    0x1206010c2118050102060405030708070c230901061b08070501060b0a08090106080a0b01030b06010c06060f0503070b09061207030e0a060c0206100311010e0f090a0204030c080c0a1701020702 83
    0x788100703902c508a10314002040c0074401081c0510303051b60750645901801d08010940f0f040410004200b001405c0c41d0070180428001300b0030921421059a502c01a159190382d0180c4104000454014850315807203180c2c102c4000080882202a690158540d0112009031001c0d5a110404650100950000d080089155039111120b080100506003143c200350700c07040c02d5501c08109800052240408141165007140c0822002d0f99900010b850807424010010041403510401143c121205d404540075038106904440750291103840680242c0301c0d0703011542c4c0c81034050009071704844500b03058941c0080640750100b808034581a0140ca490300002c0221000c54aa120718900c5650400103503a11001d80302c4100102495a190382807402111000d090404c45041841c656a0f183c00a140d609050003412406082c03400080c110000c2d0018041110068980640003c443c0c1c000240f1007001d0700c0003060b456500e40382c40c0401d800c4a2191000b088595000d001c0f050140c0c2d94003486a40d052001d52 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 21683990 1250 21682740 21682757
    0x1030308060901090501050f1c021201020c010605010903050714180408070210030b01081b04050d0803060a06050a052a0307060f050a0603030801050d05030f0406020d030b04021206010c21 82
    0x4040060b6004141c11484d603140c030307242c0104070700e544989801c80810403da501070010710440c00c0c0c1c094800060b000203904101121002e100150055004019400d40503008010307041c1c40d1001150070403d503100141ca0343d40211003d2104060110100c040c61030024103c0c015070320010021111400111011f40e0341842c08140b1a00b076080c25440564845a14982001041c2e01c90380045e146c114043d11784102c0c415055546500340c40040200c42c00781c10000d03d10750004d4101c1c0b0b410900b9901c201c030310340c2c003484103804000f50280c00355090320ba1007151500e07140d0806100402c032440c08643c20ba03515100303502d800c1100402072001e10041c00a41c1c0550408200c109841146605444002c0c2090001ca494501c08001081e40080c849040d61000c503440440395030b0504001d40b544c0540d01d001c446418001500042854002030b0403100040b56407001e028110020b0104001ca0065015024160740ba0300300185180d0301c1003084d401c443e40b050000b055490500c249481c04882106280004510310701c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 21685240 1250 21683990 21684001
    0x2090103050a0204030803040f02040e01020c03041509030305030c0307020a060905010c0305060108090c0d110901060c11100f030203061318021309030e010c03170c04090c1419050c0601030308 84
    0x1070050702c0c0e00207000c01096103441d142daa51011640300003030028098000c122240d9045603265044260680c15202c0203644540e0411001a02c0350700c181703c0c401c42180113220810480740980d20a008503505034a44500f507558440580845600c01000314045004007028000007440b248661104c40307005600000d0b40840e2280e01600b10780d000340460741884406001c011940c600000c0c181481300040d203010441203940d1400d196401350040102e54801021030010038000d0744500d0b580f004a001d0700000652046178424013140880c09030688000925480c00005141e029030011604200301034024080300300d044a511080790f460340000c80c10384440758003800640c41c02c0700f03a43c1440b8010070410090009150307005071070300b0324100215040c41050b444520900d8061022250043e141803001c003803a04d00600c00888952150080e0403040e40352038441d0421611030b84240e0103030049a01ca580c03529002c4404d4500280500a0200400c9010407840d616540180b001d0340c000e41c82921247c0090030107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 21686490 1250 21685240 21685247
    0x3120403030b03010b030c0f0312071109010b0708030105010f1b061b09081c1b11090c0307080103020112060306110a031407021009020f03030a020d180807090e0c1003020901 76
    0x205140350f200b681072502c0c0880984d004294603101c804125041440060084080f9061810703518421a0030702c408600d20051004040c85448848002c860500c0582e88964001c03000380100600503280500601c0144060350150000740c0c00c5011604180c40120308a41d00c8440c0d43ea21418200d034240d4651065804401502c1040c10415105080401e221070411422941e00e00c0030880e0000e280302070001000c940c5002d1903000c600b2019001c1411025155414020445030071a01c4482c0168400c800050721181c002043e2402160159100c0d81030707900c2c5400450f00541900054150140e42d81c0700080084d120303118480042204003580c6440340c00204002d4100c414240e42101c084103818104001c055020500c64080c0b030a0420004904445002003040050959401da81520000941905968001441010200341c40d5175440840e24032135405100ca105034030440010380c1c810001801159031541240c29030254001c02c0b01e49040302003000540d10742603504c2140110b90f0016019078103507070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 21687740 1250 21686490 21686501
    0x70305070f05010203031909020a0305010b030607030b0d320609070b03071209060902042405040204062c0907050406120b091324230112080d06080312040303 69
    0x391a075404805480c202c0080d46078800107004075241a000e0050b80f2901c603196201c00c510359000303010140640c2d240d19016000380740340e01c00d4503c240b00d5480025105442406900407004002e00340c9034a031601903503040301041041600141c00350f18980700340d0401c14249180700c4000c102c000141018109601036900f0951346400080d040c0004008200c1c0070758200b41f003d03441c01c0007400c000a81041c40d04210000307102d407400080d0301030306000950548101003520301c0d400a030803130301c0500f01d255500e0821007240318030310420011079244036110580036441c3c81845008500070b0071107455440c031080001c1c01d0140c00c50341403001c5040810203000a0381e00941d00c00643d210400300b00070001042e0300290042400070001c10410407030461810410100c001044044064048141da6403c2f1007070840c4090304008500b4018140d04e900d5080c0c050040707641c150704907404220990103401d00b64844440503440b19540041c0c80c0e4440b9000500170108000a002d80460400c082003503080500e00203058a1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 21688990 1250 21687740 21687749
    0x10f020c0309010311030603060f090a02031c110c09060409020f0406030b01081002040602060414030c07060305010602011812030902150a020d030605180115091208130e04150207031b0507030507 85
    0x406e004008a40c1c9000031a60341040ca5041c403100d0342d81d00c00010304c1c41c2600550000703406002d1800c103a0b40d900451283d00c00e009801da212030413801896001c1c176a5031f8a00e00c0d075032540070040314081a85802c060380008100703800600742c2c00224000c080800e095500741d40c07085039010301e401c004102d044410701034a07060010048056281c5442c080d40203607070384406400600f5070382440400510702102003080320032640725181543c0140f642e40c0c5010b00105024810f03100554244585410041c2c00c4000000003030750b11292100794007050804c01c9008008202d012a000b50103007420028001510b4083c00300c4118170390040c00c644586c0300c0c0040644240c3c1d444580101c0c2001500c032061040b110015054a028031002499140741d07110454407d2603030340c00140b9482048884c2428403902d0001004052158070306140a966a040404100c2d40b0446002d802101030801180e08465150024a0b030329020b031034401c001c1c18002c824092107440c51001100e1aa004080030410080103100300401013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 21690240 1250 21688990 21689021
    0x60b0a0305030405060906070203010510030b010801020c100506060f07050d140309030703030504020103180507150503070801030807060209060d05040212030c10051012080a02120901090302090702010f020c03090103 94
    0x9514554030640e80c0e000f1070080310b00c1454081241c0190f030302d03001d0945040680040c003d011a003400780200316888018081035a80480e20000441c54100c14000c80c4c3c41c52400400130300c640da030803210140042c0780c00b03061103900a00401003d052030030200080d083d4180600058142940018005020401450300d900c030110002e104000c0500c90100917158030507014180854682e89034030048004040e103803041c0c10400c0c1503105440501800040740300541e0000550444a50384003441555140003c4801000041d4020018000529014003030039402d03218581c0541018100d2001524039080460b40002041e034a00411003586005214140ea054080018501d0040700001490703c2c2d880c0e070340580c0d8030390b07032a04081503407601d66500000c010004c1c1a0a0301e50350866251400081e4010f6407188010b1265044140081840750121865081c058543e1409146598244944000c00801400555603078040b00560000c403400246183e03000c2c031014590350103a03c00050b08031a0300c07414403000d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 21691490 1250 21690240 21690259
    0x206010501020c0f0105030a090b010b0403110d02030a02010c080708031602010c08070f0c050a080301080c12010c021009081603020d02190b010909140d020c0901050108130305030a0b060412060b 85
    0x102c0c0c84d400614111030700c0c2803a041d075407079485241c3c0c0e0010300490200208124240d42c000208010443e014200b9240300b0451607039521850800c1000c00c030f1400001079032540002450800540c06828480540c91044025606120048cac03110102908100c0f4032521140350300c0a031428566080c8298048028103003081c6905091041000300314001c08518402808245039542c014404100311140b6019840440143c0e40d41e1281d000c551603420800605014020710348000c9500031041c020405504410741c010419005c003042080b019001050301600d44000400002d8640860030000000450080d00145071002880383c0081c58188020801e41d0700304100c2580c840000c2c102d0368050304445010300c0101d140d070140d0402c010010341507244020780d4400e5013001c0e40c1e5590040703156080c00c02e0850750150180e07610001501d9142e001c4441d0803503620178035420400070b8068400345410600d004000284101440007041080d44950402c2d04605148120b07101041400e0155171841d04041c0c407403504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 21692740 1250 21691490 21691513
    0x40f061116180b0604031b050604030f0618210206150a0902070302190f0204050c0c03070b042a03050d020102041214190602030603010f0e1e030403120f020601050102 73
    0x2804074180c0a9454000a22048075500d00c0b065084004251070090099079115940d180075007908224254914010303510700c600140301c0c5802002d0341c044a400994045d90b0448030750b11030b40105002402c1d80421100744240c103003c42c000e0803d400d480c421500443c10340b50441540a41303000c90061184130b216542c1d03107440c039054403070503840411100c241d0780150b01c0350080c1c0b40c181c0c1007503240007041c480c550300140d1943c24000360203640308010b40240c0b000c21550725244c0701c13485a031103064403081c4203034410400d841c000303050124a04d2b4002c3c0201400c10080d0350032000081e0300e030f0089102000c0b03440805402e0040c400103201aa00c0000c0c1c0340021481d080c1350841d01c41d80c080d403014001d41500042c8020809103c0d0901c040b00810751451046608180140f03071a0300203410544500d070003986090300f44441f01003244030b02e41028041200810001d00008111400c071080c2c1c0406210038001440000006404400071000b00000e0340c58201d204014804000e00c0d0507016440181154010004000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 21693990 1250 21692740 21692773
    0x60320040f0b010f0509060d0e100e030306060304030e0d05030c030d050609010e0103030f0905031c0f02060105090a0902010306170705010f140304110103021603020d02010c0806060f030417040f0611 87
    0x185020803e003011034441240f04005641030141d100c8c0c0f988201e0401050b41d0b1052000b0a02c083c11040c02c2c801000110f8030b40e42155540e00040780e51642042040002c070700804d0040841c07100e1160000d0000f40b038080503a803100e041d43c000c10440652980041040304419409000b0241d1103002582c9042c45589044056801040103120140a210101c03001940840c0b10703010500c05801b0240c01c60f5011400306101103840d51042000a0004040442d0080d070144003250440c103c44005041039555254092100300a0080c040700700e05140d519500011041c000180081c603041d810005809190b20f000c0000d040400c07510b4406d000c0156100340c81d02c0c07001000c0c3c281c03a00f2540101089030440c510b01d0040c0c0003441042a070780403c081c04543c21080540c0028881001da00581c000d0003001e900030b03401c0e2160385040d41c10f260b0000c01800f0810010031070380d026650142c05401d400c0001065400803030304a900603004040c0b00440750340123105c119003243c0082d008440d8100200f054500c49030241c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 21695240 1250 21693990 21694007
    0x3010b0d0b0c0c010e070f0602010c120c03140a02030f011205030a0c0f0209090106080708030c0307020d0c0b0d020a031404020310050720010e010b03030a0819060320040f0b01 77
    0x180704101c01404111840c400c041070700c484450700f0b0020020150458019076580c1d4070b80c400c460281329001750219800384103000f03a80c0d0800c0d841c0c0317640c1c1a07481d0004a0304e02038402d079410402010b94a40d40708650005c1c034101c140c00f8813058900107030740e8200001c03144000d11050300190b210f8801c508440300040d0000080306e030340000c1c070710f03045100f1000c0e8a0550909070040c08040d60181014092213036107001988010121044031045a15071a036840d40369403280160911880030b038209100840250925000c1d10308454892036141d140c0342d0701d50001005a400201074043c102d58003150704a00503030135200300003010f410301c094001039151660000e0366642c1d00101c81c40c146512600801e500c5401500d840c084103100302088094101c1c1c0c40e284c0750003402c00385002689507013402d55141c0c05007408011505111801c0c1e840c404d0f50b546042d500741e1a1406d03415840c010540d40ca40c0040400d038212107024201102e100c460081011003007c20007071725170300d40d070301c5000300d180402104141ea081480c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 21696490 1250 21695240 21695243
    0xf0209090a020f07080706050f01051002030f1e03040c03030201060605031302130b030f0102090102060c07030915020a0f0803060127150509030105040501051807030305090d08091201060f0503010b0d 87
    0x15a070f0f8005040b08400501031214020b281c070f0b1004c19074404024854124910074000070341e0183d234580e6030784200040c0743c4100303503140c0260b00200310326201300004034010100b0307000440f164100d0100101d01416203a004650603910741c0c010000c28000c066081c00f4180080c019490050b0035030038081c050403002c640c00c0e60001d100c0c840c0740c52600c0c01d02c2c00036080507410540060030f5500c40c509800e240c81c047e43c403503d9028018000c04002924100701041540c034070079055030b105100e00303007000721802c100458a001c003015403040441c220000303007000000102d054400d4452980301c0c206000090642c42d210b080c0a0307052046034102980244082020300d0031240e50055501c05c0c0c41403100d042d41e40b0300c90465000d42650921003000240718054119038091703002202c006074001d450424946d260541c5000050018504110301c3c00d05113822010000020302030204a4600a100700001d140004c280e5520081c07a511480c0404c612076010a01300000d101c1940240541c0f600200003400c2801c00010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 21697740 1250 21696490 21696511
    0x60112020a03090b07050c01060f0305060f1b07050106031202010b010c0213060308130303080601050304030203090405060117160201050601020307080717090a03050708121204032706090305010f020909 88
    0x41d000722140c403a40040d10100d80160303900041d130038541c03401000303a0312030380c28890290300b07000c0009141e1034802a00c10869410201400603601da40180191110016003031040d07075501140d4036040210118010440d1922032000059014558030b42603c0c03a1844881c0c00c3c0640e45003960b0700900c0e0740c110081c40000c2e641180c01e8500302449590300c00c0200003a401c00340c85528045015461120644540f1042d41d0098481042da9610500115203910003120000c0050b00203001a44183c24190451030300100141400824010204604940490300722082a240222010402c480640a100e400e80110083c40030b9840c011043e16850341a124040d00240010054078108619800744c09c107450468200070060075420b070b903d0030100d55802c0c25005880c0c0034001c100e10803244107071030000c55000088070107041031950f075103403000daa044162020000c201e24000070204c801c402400380040280645840c1d03103e20b1030a40c10040c0c00c6a071900b42c5101c00720320421680209903240011503030b022100e0b20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 21698990 1250 21697740 21697747
    0x60f0f030501080d03091e0302010f0609060b0d0c03060e090102091009080a0311010e0f0307050c090f07210501060f1b0302060c07170d0b0f100e040209010507020a1203120506011202 80
    0x603104170b0014001007c1c0c80f22100f103c081c0810158107402195000c492024184015500e5907202c5e030440e040f9218480782d881081006103909056504400e031480c0d080d040c001045551200303c0300d9000760844031b020060f54000f500c81a1450803000c402041400e921b01041200d080c141c010f645c8076500707800501481005461411903220940040c1700c16185c2c40c0566070403a40c1307444005e941e070700504001c1b175090081030003440c082d041130310700284a40400500d80c211512400320640d110615000c6503a0220400800d000155050340505c1e40204055030b107600381c1100603e401000a501c501500170407110101c5032300046a40014001c0e000940440d00a0313903103055291081d184890740e002c03414500b20202e8040d25001c590b82c08080600001d40c2d81d69401950601000040400d5042c408007083e030005441845041640c041c1c0f04886040c18107902d0300300d1540000d01408100d900030f40e0342a005504410030141d002031050000410041e082c003c81c00c20344000f0705420101c010003450541e011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 21700240 1250 21698990 21698993
    0x108030313050c100207150203070f0807021332090703030f0203040f080606150702010206070f050c010e0a02040b091003020f0103020d0e250803090904050313060f0f030501080d0309 80
    0xe00c5402e0320f0090081504041c441000c00207902c9403802e128410240d0b401407428070f056400401102e240c40d43c01000b220090782e02c0d94500c3c4580d0000740d0141d0b080508d40d2021850014a44a090806c0100d9041e86503103254594181ea50507856040b0410b08040001c02d03c00040000101039040e2685820500c0e010341c1c0109049196000303691200803a500703042e0300003490900c045604ca00503c015a12002202002c1046283d24030a40200078016404800060503d0344558100d040041c42c5251140c17915100802641c2174440c0101c0c802c405410044d015021480c1034400d0400b0418240e0b0b01d03215619210500703c402d00420722000c9d01410440b0640501603200340d040700d40e1f248034008208180030115145a598441d412104200030754074180700110b402d5072144040807140c1070b40044d480d0104a40070f00002c0040948112618841440f00381c2d41030f884d40780035101900f0300d90394400441f0120700d001824000f5000c0d48005140c5044010300c0030020109142260a03218113001c2241001c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 21701490 1250 21700240 21700243
    0x1061d0a11090303030403030c020c0603250909090c0906050a030f03050306031002030112020a050303041809050f01061d010e0f01030f020109030204050c09010206010e010806042a09060e0906010803031305 90
    0x5220b412545800b002040104240c0c0580c4160401600c56084410000c00c05051280522040c1c3d14010001480140c4c4104035501540ca01c90380c54107481d081030345039036420700d5405640c1d55450848501010304000c0c00b03035544611071f110007030108461070600359144d612148041860001d020f02000340010016806403003c10080d588041358072421136982d80e4802c0f02c1524079511b564201e01c9007100c6080001d00b80344c000f080c2c0e010b41d541d6030603aa140244940b410001000c070a038003107520380200380d9035008010b000e12940004125400c000070603900c0b0f4041050b807030030058109201c400280c2050188591030a01c1c660f06407540400084036100c02030005850074000e03940020b600a00340f2342007014208041c006030900c3c100c2a02200e68698031581b04500c015024003074600b03d50b003c8800600400c81600d10303206820740f501002002e43c8103500424189030400c3c1c1000d03400e08e4440b1420007805401044040c0c2c841001405801c0c0303035041803900da82300d220151400390240303a4044441c051010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 21702740 1250 21701490 21701497
    0x60301090c2d1404050708160c0c0302060d061806080c040203060103090605010308040602100516051b070b040518070e091f0311010807021b010503041103100e01061d0a11 75
    0x101c282814042560f54005480280c51800007034055402c001c0400c0344a03001d140814040c0d80300554224041218010440304400b280f031003500d00c0c0b640340c000000507032189401030400e81102400806c0442c100501d440781c00d1206806520350a1800c001080011004940b83c0f40300c400480f130250341c82d250b041c0120098007801c1c2026045928043c000010422510f00820484003d602522140c02414940704c04460084540d200c4105c4140d0807403242e544a803008152400324a980356a4816605041e02c2c50300899400c0001c055200181c28001483e022450700e0128508041c120a5845c00c4000100f1904080283d10300400064011588400c8010030040d0128000c182c03c100d82d55032030402c40d40c16801015680c1c0800c2101000c03590312031012030304a004036004050b01c9078440c889001124a03500003407081e100c1e05205800c1c0207103035a05000c1341055024164001c2040e002c51103034142120b84a520000001c450302c2e8510b4620812403418940c41504601c00054504164610745114403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 21703990 1250 21702740 21702809
    0x14010504080d2304050d0b0403110601140306010510020c040506010306050310140906011505091309030f020d0f09090f02090603040f05060a020a08060d030c020604080312060301090c 80
    0x4410007040b402d030780520041d001c500755205629140310060401c0311248240c2c09403540116900314140701140c01e401ca080e4110348203181201042c07402540040c10303ca800e8101d400c440c1c050110001962400300f2017580500400c40d0600c01040507108084e654242d0066294002c80e00d500004445078003070340c40340c00100000f0381501c2244840200c040e0040c1a48072800e101e9900d940080356422000207103207410794075000b2a05815440c0d01c1130a54003a040210466800041d04010018050090041842092081d2900e2000c00e0b0280c7d0302909080c500c40056041205a0700d00c0e04005510603055821550000c0e0002610b242c4024050060710540c50440d4021400000f031004000d1421281000320380108203499654440c4180982640300381110480041d0000c80403035183d1401c02e01004501e4400d0401c050300c40d50b070350b02284150304079900c246495000401c8100303001e01c0b400f540541c0300703e04500030002c034071055540c2c00d00e410881c02004603c031038610400d9080c01c0509030303010040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 21705240 1250 21703990 21703993
    0x702010e0a0e0702030d0f0605031504060f060b04150804170f0c01060b031b16020603090a0b01031101090603051303050a0210060b0406030e010207020a090e0111030a02030906070203030c041401050408 88
    0x500c3c1203440039640742d0107064151401b0389450603400c018141c82c85080141e40c0b00401905004040703402d210045038000d8400d0782c0c850740e00c29a403076103032805100d0310006020780d40001d030700c0c0da103000303142d85083d081031524000f40103001c010400020b8450240e01c001408941030181c5032101e0700080d01c1d5038042d800c80801c0e10340ca000b0000c24903910440143d84150480604812103995a4148501c1e0f80601c4054000d581c1e90056810014030f400d00c0034562080340b8100312034032101181c8519250782002c4e841950165101200c50295580c04072443c409440507003001d000504050200fa041c000d071022019040000c00710b41c0000c128401c1c080d810401d01806420b2000365196801d007141640107200b0300003c0703444c1520820b002a01070003a185102c1d0000c1040f11043d1034001684050010203809001d40d550b03540701d101103c1c289034040d500507117108a0050700e83c5442c00d0392a01d00203020700040c00b036500520410054480007002c80b030580300c42a61207540544600010ba441d80190303000080c95 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 21706490 1250 21705240 21705269
    0x406050c07021c0b010614030a05070c1b03060f02040308160c030b0103031101050115020d18080a0c05120a0f03110705060307030515060306010203040506070c03021207080106060201020f0702010e0a 87
    0x5843c1820a03500f800307005151901c4541d0342c0306416250085400f00395003d80d50300713100155039100c0940c06158030a8060615481c100555500c5c41915800c0501060000c2e414190600c14003005103d004100f042d0503104502e05401e40c0c0300c4940350701911b00008200d4540034140020005c0c40040d01008507400275281010f5616031401415210184001c40c100b03601e000300000300200040a2103044189075006400700c503401079030440d1108031800c419029104c4420000a0802c41004010f01d1140100e80c101451410300d01001b080c80303030780490780390305600c00d0800d040841d00a122159003e5418200005003400e0410100e0a0401d960f01c00b503030180000c010801d1154064000c60300c5400f00e200c02c01e91040f840010040701e40029030712103006074404e110074000c0f03040000007400040e010381c9040130615903907030000341c6030050f9418440c042c2e00036034402c00c11700009004103c05407242e40020360500c1c0c0d8110503880d56000c4c511000c2c0c1000710540c0608856180d580c141d1000d00074a20800c00b5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 21707740 1250 21706490 21706519
    0x1a0903010203090d0206310c0f060f030e060c03010605030411130b0102060703050403050409090501060b0a0e01020601060206130b150301050c03011a0705121e0c1b0f090406050c0702 80
    0x1120186542c4c0c4801600078080044d1031001c0c08107001c480d45080c4060301d45130804462010803a4421010120340340c03405c2c95070200320480c2400200300101a559280c441c0686001d1b002002d0701c8409041c849581c1c045010702201c0742165040d281076903660310b4800e850380d55504003034080300c480c040815005070120a10700d02500150300a007041c1030702070f02140c03c16110740300103c0454a08a030098002481840180441c02e800d400040320b01e4080c00c008141c040e12680041e02543c0f1072406400400c401500d030031800d58051000ca4010551400600a14500524107a10f0700e030449100400d03900a82000420080f100d9a50300c1603482d0103402001285400c4000108940c400c1c0900804600d4050992800203002c0044600103540280a00f80b28000741408400e1900003441403024250000c00c68000d05c0d1030100034141040800d0002c007451480050b80c00d200c0720324045802d00403209402d400e61183c440011035a00164000c0c00099642d4072141075003054010403000940c8001080030f0303002c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 21708990 1250 21707740 21707743
    0x120403050c1206070206041101120e03030901060b0c10090c030602030a05040507080705180702070308030c0304030e090105010c14010609020f03060907020313091104090204080303070908161a090301020309 90
    0x440007907056403800c14038990a01c000e036440038120b40b0300d0016442080024001864040010b012190604042e541181e005030b0480a581c04181c607942c4030f0b4004800c01c215548240111402008074401652401c080300500d1611045003550268046807600742003030030000319440300320040d03070082d10071034490403d0320500c030107010255800e5846125150020440250200382c05045540c01000c0002c05034040c1c405181481d4010400001e501844e000040807400308c000561095441800c6c19a80b4501450040c10040c040707105075000d8a90b210040c070803641c0043d094440d098001c1312051061001210f02400742503d5006200210f0002c01d040f030410f0302c008003660090340122a110300c02c0d0386150b0100e82c3c0f401400300f41c0c6500b040d00a41080a0a0305602800a804010074020f1625498504010981e80168401c205960002040040c801c3c0e0085400700a408002c0207407810b146008040c0c5450310160190301142030401c49810000450320342111503035003020300250748074640340e0741a0307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 21710240 1250 21708990 21709003
    0x6120708060f03010c090302090405011b11010516090501030203090c10030603020310050402010c14010209090f04060e0a0b010911040f030b01030219080706030f1e050108190809040902010212040305 87
    0x40c0e000c0c151492402e026854113006020520b43c0a561b204070092854080049181000e80281d445550b01c8500c2c00c0001c09600d0011076120f400d4542c0d0442c0d503510210f450841c0c8004000d0000d00915100d40441503501c19060800c4900918001d03841e6192000164104004400d8403588416a2070050509030f4164000c107085074000c8040ea4000e01c1481051016544200c0e00280081c0410b0301c440009201c5044146038500c0c00c030001810515007002290100c002961050355a00e00300041204100303060044452416801014103411401c40c1d0341c034200b581040c01241c02094031015660401055070080c0d40040c0a0700088002c55039032401c01c00c00d050420b01003a406181c120354604541c203c442803003001c0300c0482c402001c3e0708d840d140e001c80c020100303105401c180c19100c0d0808403a41d88100302c00c00d102091040f0006a5503d0051154076041c1c11803404403001542c4800840801c42d040d003920b0090406407001300380c000c40703440101e0a12a25034569100fa103404030b030200a00c000060304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 21711490 1250 21710240 21710251
    0x2d040b0402121f060203030f012c07050306090114210a080d0207060e03160f030309020618040606020a02010801030f080712090f0b04030f030f09081005160e0306130206120708 77
    0x2994100707078481e84100e84034403049034564006003007236004100c040000d88031120040e00180007140001e90070b0741c10050400050351000c00141d03001c000d04c181441c080c03000500400080c40c2600c03a4035428000f264480784c004400c80144060040410700841c1c0034000b00395441e601681d1143e0ba840d258003800d000707401c44034003910400c0c50040200c060890000480b03c29110300400068000c07410303540c1400705400030004508240c1c454006600503140c000250606200c016140240c00501c5070030f02c001c8a100ea8001c40441d44090403070805070345c0281860f41502d4100d05c0303030794450000e4101040079118510000b8031081c1071460f28910709a1000550302039641d00b01500009990700c558440301c500131400040c192108080d0b9940002e03001d041030f0381c040c5071503041440140ba0355043c61418542c04102c9080c07915150000c20138140a183c840556002450600151719041200402da8444004150070600190341542d00300b55507610301910340340b03200720854800924241c2c0005100303040a44d00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 21712740 1250 21711490 21711541
    0xa0602010e0c10080a05040501200d0e1204170f06070203070606050a0303050409020d150801090c0512032a03041508090d0206070c08040504020d0207022d040b040212 73
    0x10b4450080c41d0080008401440300d0342e511150341c454904072401000045c0045655640e90b004e00d01040c0b159044851111581c174111648030320000e0302c1081a2410b45e002007405070000c41400d80c019040e10103130b80039075006920003083d14079280b101310300e418919591084a4410141000340b9160700200a1a290b8851b400601c0401c0da21030030301ca1309840c18007006020520a10040c485d00781c1540c050b1808800e82c07003000c40c1c2d1208030b11055030b00c4201c61b048000c13180d458260240600400a5488004081c195129108810b01200d001e482e07020300120a010800c030007020005680070700c80207001d070b5000902940d42d65a641c01c0c408503917000401000340800c0d0810b0008001c4000858522081c0b6115005081c0d29610240200c480d9811500110340c0b1840030300c07022440e0380f524406400c2140ca04c9000690b1340032103004001500d50502540c88014040b030008508500300301000b242082d401b07960100d18541039900040190040c90800032407403c21400304402d410310740c1c2007a2003030b03c04443c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 21713990 1250 21712740 21712753
    0x50103050f030306010e01080601020a0c0305070611060c0f070503040f0e040c06170402040506030f1204141f08040609080a020a02010305100f1403070305070e04050705040c12050402030c0a0602010e 87
    0x40e58591a0f00003142c185000c5500000000c880754000c44225600020500c1a25151a203a075a40300d010600c41d0415103140d4818001889401d81084a44264003400d2005227403501e045481000644915440e08040040104500c42041010000c1e2006810840c401040694880180c6400c0e19421541a541008007184c00181640515010fa03c00900003001c0c04281d40c50307801b4800541405131a80d90584158803051805500511445010340385080980e03581d41d15255100f908500c440d48418454076803810200805030354101005980216410002c0300ca0345c1e6030814a00a1140450140c100c51000454000305c075804543c59208078400d0b02c0402a986480820103414a0315018004c500b0011007402d00a41d81c20004d5507030003280080803900e042d0f03141e55580d42040c1c80c41d4014914002c1d0b0b40c00380003c06c2004d00580317000e0f01064504101c500c0000310020441800c441d61620156640d4001c47c040d507c0074460500711040141201c1d000030f03506d080090080040604c64802802910b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 21715240 1250 21713990 21714013
    0xa09050108040201201e030c01061502070608060102030f0a020a0204060e0907170307052b05120c030604090b0112020909010504080f0a02100504080403050d031104060c03020f010204030605010305 86
    0x2201c00c0c902880d0182d40c0c803a51001c0e503610704840c00800c28100c1506108070f4a88010510180254601c0044818041d60711804031042690075246642c000521407000f41a409000700d6001848008481c118681200d5540f10800140e0440c41000c021004452000401c14401500007816040c503034402d9034100215580c92103040b01c003078819915607032107401482040060241841c1040d070303019400404c2e2803504075a070707aa181c40c10046807060302425881c002041283c0980f003e032401c5c0300c1441e007010b51403c08062025090031070b000304080b1018030044003081c05600d6541c4012000d80e40403009550300d5031a00c90211030038000c0704040384a07110400c001075910304103000300b5014903403190f002401d0081c60800e10070213820400c81201144660f642000e002403131742c00381d603006d42d005000c0c55075034506500f041c4d0f0030040c0f00400c440a040c10059040084007080040340d084824a141c603a12100562a0890801c28400c0300c070700359503001040c007000780650b0340e111078100c03032040f0110b440418a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 21716490 1250 21715240 21715247
    0x110d0207050112020c030d050906060306010902120601270803190309080702060901170a05040308090604050703080f0c030309010501050109080a0b281a091324020903030304080a090501 81
    0x101d0003042d0000304441c4044030b010303405030050080c2c00c17864801c1d6800e002c402c1007170100f00c175000c0b40c0020301c1b54841414032602d0b05043c840da6014008020003940b410030484031103800a1405056203040000441100400d44055600b10250212909007000a6642e84440a41c0c1e0340200f00f4402c1c812a002e0780c01001c1038040e2140b0100194015040d0b03040c401c06400300300594020303c4c1c0c03031170500015400c103941c806591f050f40b9118a00301c410020b03180c100360800408c9404000c000703200f240e2103c014000455000a40001200e42c49a004c5545250f0040d00894a001d820a141c2041c4004014003c01190640006050f103900783d175058080c0da5207103e0203a407492500e002500e0484502d001c01c03803503a52030154800e14442205c0b19102e2076a0003030841c0480b070b407584d0100800c0d04808034403880c40ca0000009504904c403072031070000b60090360300c440b011708c0036409032034026080c0321105410106007a015526084002400d81e0384902e0310b401c001109900441d4060002003100d200814150702 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 21717740 1250 21716490 21716503
    0xc0201030c0905011d0609030304060206010e01050a081905011b0c05210a050703021207060b040b0a0f090203090708070b0706050714030604020d0b15090901080a050c100903080703110d02 82
    0x140e45d0726403141003030305049804051307500300140c11030806c006d000001d84041000308000c0c09658001d140380d600d0f000110341041410382016118409065040005d2040082c00742400103040115182c0744e020b0780b8003a40101080d800c510000e0000c1110201c0c1c0c282c10504812607103000307800351450106005840d503001e035098030b036144c0086010320a80c030150348207a01600d0713030a11038011221034031000d150540c8241c00661044584a0b110400c03403800c5e04140c0101e0400c240250740d01844603040501d16008182c49018107108503902200040407140c0070840b42c0c00818600059495450702c480905495501c07071070090f01d0b440d05201c0410352140c4101c40c500c0807440c40c18200345c15031f00c84004000180d80424a80480c4030744074038690300c213651689280159160090707202e5030b5a00c0110203000700d10707005a010504980104601002140b004506c00d000380d0340031200d060044070f181d4810f4078030040941004e8146400071404c031041641180200e5000e5007408200c80701c2096911049030340c1d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 21718990 1250 21717740 21717749
    0x5090d020a0f17030a0b0f0a0302060d0f090b0c0a1103070f030c051c0201020406030609050603060c1e0c0114061c171204051605030604080906280c0201030c09 70
    0xd000d01084004100061046416248281c2410b440fa0100344840c0d4100d400588003190701940d903100a070428070344400800d03c00c01c4140c0c3c9508001e461600007031598050049025111511038041b44404a0154010390341c559000c00b041020307091007004048e080d000b1107120400319000b001d1101d0008030010642d007a03035501081c107042c0031000342d50807070310001840421102d6100d0b80761074030f400b10040d8003006030240465000680303851130003000800303884c142d52101050307a207080d050088584011641d260300c13103410100950385402c4500ba504007102000e10358030100e04081600392501d281034000401c2d020252040c41e049841d002c1c1044041078490214401202c10038a0300b60000d810800084c144004503007a050030030300e074529485c50503007003183c089074160840c1219a1301e241402328007030081c14050b80100000d160036900c2400c10321400720140e200e00404a810040354620880381c3c109580c403c1807060b00c852072075602601c050b07a0408124003281c1400324a10380306129549640894 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 21720240 1250 21718990 21718993
    0x91b03110f030402101e030504021c0314090f030609060f0a020c06040303110405030115080d0203190c05190b040209010806060d020f04060f0308040303020c0109030201050a180f0f030605090d02 85
    0x40d11036500300030f03220f44580921400d10030506c940c407807151a07040e401c411000722620045030703514040c0704000c4c2e00d0200c0503030140c4140c11101c10304003003a80600407600705022419410750380c0d40103000149400000486003949881080204081c24901040ca0b5014003900041c440658841450500c180c1c0200e02c50003411358007070000240428400e400c0395030280000c107851450240c03550301090a54141145c1d1215042c0d241004010502007000301ea030414986201550400c80c0c10303004c5280a0101401d10384c00c0000e07107440d820034006c0034080b41c1940138280030310054070380852505040b4201e007142e040c1c0c800c2180c078000140b4004040351061140000819542252103150300b00000304c05400309141d005583c41d107020031941e1402440328041c6000348403440c4c03a1407942c54000e20b02130450f6056410840c91038070810040c2d030451b00b5200c1070300b003c0c01e000001c0c2e41310840e02807030300e000c5a129070084a040c1c00005a4403100e81d208605990080300f0603c030079950200d031a0350700c0054041d5800103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 21721490 1250 21720240 21720247
    0x9050f01050906090118060507230c010c0309090203070c060c1707050d0f05040f0c09060b160303150f060e010201061409070207080105041a0609040201021002090a091b03110f 77
    0x80f481d0202c01898043c4050501861000c03059888142910302600510301140d070001c1d81c6014444580d074500201500042c0300a10540b00100050f12084106030050500c0340c40c41c115400c060103212a07002800034450700311b40b680351490008040304000c1005440c5207150005000c101e5214608103400fa03041620b005905484e22041110303a0f0b0300c04001c6400700d50b6903804801e0700300b42c00e00a02e4001d500a0304034100d005981d00b40b141c08410590b0000d154580340040810000000e1800d560840403120411400e81c0a14201500900b80d4485042c0001d1500b0b01c000c07540d210502c0300c06c41a1900350f940e2100c0e40f034a410059080f00c0d018050440c00c4001002d401080d440c0c8050042e40c00380c0780c2c1c4103039200107542d40402c500f1740e032051300c04880912881820f95000f00c166103107030780d01007400c81d0000b10398103090700041c0d2a03c01c070311610800103400260b80c0c2da0380d40b1008202c3c0014021040c007002101d80078240c0ca00052003000d00b241c00682000041c0c0344803542c904c1500d080c4030147d44207a14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 21722740 1250 21721490 21721507
    0x12051005010f05040302090c040501090b16060b0a031b031202010b06030a020a0306050a0e0405011107030e010804060605060d02030f070305010503030a030b03011404050c01031103070203301609050f0105 89
    0x48440404100b5802c00104100101c0103880d0980241c2c0201550742d030140e03c6a041038005012803840b41c100c1d00c111281030008041006c0131221b8101c2040d0040070004003d00c1c90070110300c40240541000d0604024806141c00c6c1840c0088160100d07801851001c045d1188948100e007654460003805500080900209259020350750041c85008064100091007580e54404940c0004156110b00f1110603044204024080c0a0048417a80700d0140103ca02e010500c0d41c014154490519450341013181c40c03000541001051340c0304801900e002000c958607011a186410003a40c030845060389001e0095000c01c103184d009020b0a816030360014041c60422080b0300d0100c00078000d00681580c590b4807502024120440612245c0c0160700440140003045030800000d400c0d5100f25641c403600c0503080007044075041d130100c00d49504030814a003250362189650120b64000c100030b040746a2180b504818400c0da001041250083d001d07907500c440070b050b660b078010004104001c8071841d01180081242c0312 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 21723990 1250 21722740 21722747
    0xa09060e04060e09030c0f1c030e0106080601091505041a06030903042303061005060405060a0c0204020309030307020706080403050a1b05010e030c07050a080a0f02130207050105071205100501 84
    0xa1500d0003400c00290581d440c0c10002d030f401d50039124003559420000f02d00c24100814001d040c480990310f4014051142030000325040145207002441c00c045ea90900e09580c64020b4001800400707010381200c045585625000740244803058501c045402d80308400102c034101030040c6030b94030129000501c001651101400130315031009010941f140000c120100f41102d400845880070b0051101c0009030341e8440003818a001c2c0040d160340450b14000b48104499a12001100d00341e80051710300c16101e0401302c500b81d0f9540861000250b00c04d00104c00c00040f641e000000c1c51041c1c1c5564225503056547e14004d83d07415000b42c030051300080041001409441c00384600740008040c503610a5401c802c00e440310f600f15a007205406200f17401c00250402c008204014281c09040101c0c0c080398110703d0301c41c039542c0d5018500d00052204c00c8818204086d03643d04040010f48140004c13041d9030f100309516200303009040c01c88d0844045400d2040140f080c80e01885403900c203c400002d030000c000c0c1002c2c010b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 21725240 1250 21723990 21724007
    0x80703110d0f0b0613051302060a0903061802040c0807120b120d0306091d070e0402011b08090109150804030309020a05040e060603100e06010b070201090e01030b0703050c0a0906 78
    0x32508088a01524000a610740c449880054026140703e02a81490b208001040c0004132a0b28600ba0030502404007070b8040c5540b03001042d030b04070ba00c1036481c0b009000c151a280b03c50390000c0d11051403d501d0b907483d1403652650652440c807c4800704540300ea4000292805002039070036800142210200020f02c804580c880495540010804072120941c1c07900d01d80f415a031300750180006500c5580410004056004507521090884d406c00c00889100d002160750b0b0095210311103689a00c00b01140559008100c0540d14060f5110341e404540e010342401c0e84e003948052030340d0b030006280550008903c4070b068890215219260382e0700700c450f100c64808901600007507100f81d0344140074810014041d52584112905441010058200e51500804141c04d1291212084014900700000703007490f4580444d840741035a20700c070107440c1c45280c1400120b41e20084c6402440d40d107141d032400402440b11154625100f80c40c90741c0d040c05240d0f14420600c0240c001c075903984001c6030f180f050611401d401110b030b6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 21726490 1250 21725240 21725273
    0x1f0902040906110c01060504060510031e02070305040608060405040b04141e1005090a0f031103040803040909052a0d020301090812010303080702070e0601050a02010b040e070915080703 81
    0x8103807081a40c403400c1c1100c00039510030040c401d000404d9241390000b8042c68000b0302e401c66013000810302d000086000c0c1542050103608041d80c4201100c44151174404820064041c0501103442e003401d4a0044c01e29881800b400c0041111040016014a01401154410b691012054040c3d45482e510300d210900b419440380d6050066140b0405050700000d1741441d402800c40c003e0089a410401440407204080c0c0400040d800c5800700e070021591014803040900da0500c0d10070790060b035001d070441c11405180c001401c2400002000101c10310b40390020b0703c03114000c0c0c4c1031350320320b410b081d4034006040c1c070316940080b550034444c0c0034607070618160341840070150000c3e002158480c079907950921030340d212010111880c9036001c010300c01c0c5940300010a520482600003415494140b429003907070b000b0020450b904104001800340300440c0300f03400c18402c1d1580940103000c001a02040389032202a14040c040110780303070079103000320034050840340c070202c1e04902c02801604d815500d84112080359540b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 21727740 1250 21726490 21726499
    0x2090a0501060909021b0604080306040b010905060306010503040519030507060b100e010f02011503060c0807020a0521040801020324100c0204051302151c230702012c010606021f0902 80
    0x11031035006d42c820b0081c5072050b07100e41d50b03080e603074a007850810086442e04c21044d41080b000c0a011f20403900d80340110f80e00003201b400c11075101c0e40e891610a2400302c2c43c0405070038a021403da000101908100500310081c071a040520000b5070800900030110401c5822500140c1e504840752102d5011350340d4030516881c0c80c4000320f122404240650700d2400d045d807085450341d60320130301d1250b0503500108240c1c00450b00d1010b481e11100c0750702c42503603966408503240c403112180d14850190340001421107000340705840003507440749440140d0f14030b4036030b40f10410752000705005400a040d24041c0011501050140c83d501c41d10462502404001c0800802881c00c0c42c21481054001d66600294140c0c0d038602c0500c0701c0d41c0c0d03120003c202580320050b10328841d5000e08100d00d8002e100301103901c0303907000000c400381c6039003681d00c00c1f030100d01503d020341c5804017000020500d1200c0e07040304110240d1510b107640090024958503001240e40d2960119803003504c080a210244400c00103410145140f4001030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 21728990 1250 21727740 21727777
    0x7050d0908040f090c05030103060209010915030b0a05010503060d060e010905120715020f0706020717040602070501020c0a0305120a020c0307090507080a050f0105060d18080702090a050106090902 86
    0x1400004490202805958203000450100211000503a5a0000d4011504c0074401c000100303001030054003040c000109040d401003212240c0d41d1144821200070b180025484801a45165002d4010b0544c03802445c00340c0c03d00d01000c5503d50190013164010038015003100068607058071444e00a1000b5411181c4c1da548582c040c2011913420012007082c2e20049074040d030b4a4000d850002c00010741911680305041c018048900010220b05c2601d0a403034200c43d026a0750f120619003c0480308a1201ea10082800450085405580000c092013614000c1c0c00f1202c010b2202020046144007902c001491a4411280c0d01c030b0700410140584070044145c011540c046421800080c1001015081000295130b00e004202186600000d802c3c1c00161304402004907003810303a4000341c80d00c414058503010b070000141500c01c208480d403052040741200b5201600000e80391810781d8050b8807501c020384c424140750011800d20b40300751040a048908945a00090918000b0340c1c001030b401c15044400c1810304107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 21730240 1250 21728990 21729007
    0x15070c03020c280f030c0510050d05090102030a0f0203060609220507080f060f0d12050d0e060114010503011202150c0607080a060803090a03110f13090302010614180705 74
    0xd14100c220070f40032602c41220220818001218240d0303004c0701d212108940c040000c05e254070390140c159801a20f50140f810311203a400c0d00d2903c6080c032040c0c801407400c0c3c108000c6c11019400f850040350700003824421012031111800c1680030039030304190310090401c50398209240000c00d4044e10b1042c011001102c505000321401152000c9402c1808503203440e0420500c5d100b90103100b44c1c810401c44418082c0d8041b00c01241820341c901c03900030702030f4882c00314040682d8007840039513041c2d000c88402403014562005006d6200c94080c410ba15440c4000580d0501d1980110152810380d1004810700000140c04e03001c02401d084001c1d00714400b01010085254030b4007040c80f070140304d190907840e02c41160420050382070031202030303502610980c0c00c1405060603aa5401c0685800c59070400d40a046140c105000148081100074140380d001e02641d600d504814226000103640c14061b070020080559907a00c03450f0424480c41615034040b0540da07036160000940c503030a9810440e00d00c0c0403802d1a101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 21731490 1250 21730240 21730249
    0x504090b03070510020a0201030b01140304170d0905030702180f0703050402040b04050108010b13020408031b10090c06090f0506030106110f07062708030306010c030c020603010b0c010e15070c03020c 87
    0x340103444e0040e080205403009550309402018041502840c095503100c83d1492400e000c0c0c000070b00002c1401164145603040c484145003610840100e03801d0420018449280443c1d40b03a00c004001c0b03004011035030036914480e400d2503901e40300348810700841c6050b50f5071719000c6004040013003003240e000c0c0c0d5842c00349940b038440380b1426011388000c5000103000040017040100019070201e00303103201401040107008404010054602414800303120300210225030048909024007240c0b200315640c0341c4070010062100c400030700c0702110a9512105d07034a5441d40001c0d55202d455020701900400100010803140c1d100d03068496003460402c05039003013428100300d0182829110743c4808001201540c0314032400d40600903070320b281181000d40e080058500300059440c0d0000030f21003030500084d08000014140034804140e01164002c102d10303901d41e182d40d013114082e00021002079041d840c1140d16104818000f420340a0329201e90480c02d16a030311400121034900e0b848004030218050b03201200f146031078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 21732740 1250 21731490 21731509
    0xa030b0a1e0f0f0522080d020703050a0815010c0f0f02030604032003090d030e130f06060909020a020705040506060903060a0b030105091506060f1b07080f010c0504090b030705 77
    0x50741008075103101c5501d0100d05861054107800d0b1000d2030601440742a0010700c412296a601401d0400d140c5910343c10721b02d1450048407401c540c6580001425020194088001d11040c510350300c804155407203840c0880010010707145001e0100390801841d2000c03655141c400e04010384204900079552003150f010030f08111040da0101e001c6103019001c14001401052154102401c0038019400d0504210024510401406003d82406040001854075440b20790038144e089032016400c2c4880140580644014403040c070a00c80024400c005c0441c045640c2c1c0200d890503c0e03907500511a10f402c15082100900c4050149a885042000901e01c0c5440500c4901d102d45041c01d40000c01417500c500781425140c0040c070a81842d005aa0b2308030702640d1014030b864001f2816100aa05c6441032800f01c0d0703191060100c1d90381c09103188110300518500018450051750102d8003503900070b000203500c1e6406e9a259040201c00b0071300910003031150402c2075000320400381c4002c3c00c60301d000350703a070011950701107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 21733990 1250 21732740 21732791
    0x60703020106051c02030c060d0908030412080c0f03060f06090a060818120a0c050106090501080a05010c02030c0c01030b0d2a0506030606030403050702030109140d0206010503060103020a030b0a 85
    0x2d440305020800d9190420706115403100c007022460030074207160300203500c41c40c2040b852441081d010806003080c10305075024813902d561250080d41d480c203180c00c02000d10b400141c03840c000034110000040900f004c103810348014414074003200f411078030350000700800c100081220744d4201c070060026103429520246000010050f5403100308241c240150500c0780d8102001c5110070643c0954000001d400e01d500842d0a0041180380122103581a0302e40b80e8090320159108440301d034240780002c00e030321001165040d0880d100d24020080355018600a0361640240c1d2059a581d40045169904950094201e07214540e4001c041c02ca03401d509940ea0b5142220844210300924220014018543d82e103014100c05082d044507124214948100011254480203000a04004010600e0401c6440c03d404c540d20550b448081d189800302e815034031940c1c070340c01090090010721030721b4000161410085521416a500a84404c24183c02d507220040d401c4409002204200d039907051680e450740546c282004802c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 21735240 1250 21733990 21733993
    0x501050607021305180d030e07050a030c05011805030a0804090b040603050613050f0607030219030902090604020d1e0e210409110408030307030b100e010c11010201180501050108010c0908070b13030206070302 91
    0x10072380c1c0700d1101d02e010b102d504414022100c9030400d2010418502ea0708085950910b05410300307080701310019401c0403095018a03010710510501030108a20340700644203503161342004000c0c0f01c0d1800d042005451040c40064080e80029000c500182080c6030064080d5000d2401c885841030304200b5245054001c8614200099010803e15004403211180f030012100528060010994070703000507a5202c0702030a410702c034982c000f82e15400c10140d038220303d4104054280c070034020b20b01601c600c00034101090100540c0e001d601c82181032104029600b80c01684440c025034101030424010500800c068800842c0c1ca050a01c000984003000700010f5105030740c2c07590b0119000003240b00f440a1103c3c184402004e10081110010311644c0c000e0310380b007605400400b402c0180c1c0322040144d0041103d2a0b05440094003c000502808815001036040761407800082201c8941c00804850b082e0701b9008411064004180400115183d1005044142c00c00001010348680c2c03079000840d40d81c416001100035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 21736490 1250 21735240 21735251
    0x2130b0a14040f080705060304080a031a120d090b0414040c031404050d0f080921091e09010909081207090506030f04030221160503040509040503030a0501050607021305180d03 77
    0x910340709010740303002050300352541f41c00c41c2003d56400d0f101c0d01422041030100b5544988402c10f01e009080c0b4124045000703010a401c401e04000a5901e07a040f0000c60408561071120000d030f42d40c264070072101250a440111035503040f50b030741040040c00208041400f00368880702c81100a101220516001c1d52181d401081c0c0c0c1c46030707018086e0200344440c0c5011705201c2c0c20010404040c1001c6401d80100c60100c040c0503600c0880c1c246915035009404055401140c1c0703250050110790810008000c8040403280c0c851181c0c1d942c0111002e1740c207410001400f41c0014000440103800c042200e42c0c01c00940e042403a2903c0e107441c04518250401c440ca480001003610500041c11340602c0301030101c00d000704904680c2208080008078600c43e104d01c2e40d1b400c042102001d003e000003402900c0c09000000c0c551250b83c01d1504100b0343d41d40003a1050414149010000151858205c0c121181594041c20b40840e0003c9008011b008000041c0002c0d100c0594400301d000303050307042c080c1401031251514001103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 21737740 1250 21736490 21736499
    0x50f0a0501050a02040302010c0201050921071a0708042105010903030207020f01030509070510030605030609010608070906030b01050d05030c0d021b090402030a1b0305150106030b0402130b0a14040f 87
    0xc2d42c0002e4184202140b041000f440942da206608842044e02030800340d658038040d03004125940011001012086200500c0000b0303080045150f10032219240440ba40c550790346e00d00400f45100d0714600601884040104011840d401c44401010455440c6010341c0311950b900ca05095136038021017140005d6000508504500d0300d100c140a10180c286010441458140e010581d5074050340540c40c459a200d440c40e10302d46200b40c000001800c6e0103405e950740307410080800c80c041d0105002c0c4c02c105008903076002c940c10707105100e0725046075006807501a880c1d113404240003181084071001d40d0240020014003001403420403002d2004100c43d4010100c2601410100080c4041b840324a4892007450307040c0805690009000868036420038505072110a2502002c007550440f540010118000c1451028081110f0020641280d0319910300780b161811520410040f485151001908620300d21341c10b12006080d50058428a18035040280d00c1140c0382d115114150001c1e03018002028501a0911 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 21738990 1250 21737740 21737743
    0x606090614010801050103050c0c070305030301031406070f030f060b070309030b0a0204120b06010c0c060203040e1005010c030e040204090f02030117010207050304140a090203070503090c0a0b07060b060403050f0a05 94
    0x2402809041c1c1c00c0354411580c1d100003041c072041841102d041585039004101c10047e050100c406098100046805030781d643c0c50019180e03042440151581d02201e10030720800c03040440d5803445208103130f44800c4400f26107401179000345004054145542d56940010602254800c0100012800782c0c41e000302692a600d80005a140b00404071030346140140000c0049809130012103041640c8100c0c0c445032592040c004031043d522608011304005180c10f4009501da4000c00100140c171040c0c907006101d0740e02c0115005040c102845460300196204d904400440c0c030411402000383ca0041015107815603440c0000c040d1001c074082c4030b000b283d00000400010010700c80202e43c40917510000e50502882d070b11441c0d141e014905c50400c40d1407214076903500d41d070f0b41c14646501404416104540703034101100001c2182d00100c640c10701034403840c2840c44092800001d03d10450303108515a9150818565500b00540382458206800140c140720220014209001000d02c0c0e882d58401440e0000f81401c060b03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 21740240 1250 21738990 21739001
    0x310050301060b1c021213060b010206040209070804140d0207050a0e040b0606031803030406090311210a0207030c080105040b01090b090f060315071d1e0d1b03060609 73
    0x1588260714000b4100540c544200c1940c085280103100d070165032070307412007030740180c0708900c00542c84454010400292590307417004518043d01032401005000d40c0d00c00160380d41c2c0c505a8019600107100000100f165203c2c2c20b03803d43c4a0322812021a181c10b030740340e03558a01300d520a102c0d070241e00078401c00e020a08069013988c0c01414600200395203400d1036103901100d0742010302518010f080000c0000e880b100007590415010806904890781d0f80707000d0030683d00902d05a0302c02c0b0300040c0d1001840c8541d641c00101900f410390200e040d2241007001e003950480b0360b44103201c1c030070942c0204500040032500d0340300040c00034420b0500109031880c09240550700d1039016007040940a1a0882c070750303103681325104001d03031113510500e0003d440d48903d00003c0c0707408051824900a01c1c0c4030401c2006180c0e00001c401c0780e40014000c1141030310108000c1025040700004a90890804014000c03002c1c90101c440300d102d01c0c0102c8281c2462041019015800f40709070f04180d03001e540740d1000300403018852180707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 21741490 1250 21740240 21740249
    0x607020f06060901090902060408030d02091003020903060c0a09030b0408030714040303020a020904030c1e111210050c070c06030c02070506040602061b040503150103020f030705010f080405030f040b0310 89
    0x1038240d502c0c15a0009003040b1040c01190038056071610304104644030f07041243c0c0030b004900120307a254603413102d0f4070020750f20440103d40a10140403041030032074000c0c002d88001400003000752416a40319101d84502e90400d42882d0100001254008049098129a18000e60142c4280c1e949d0380b818050180610345050b0903441420001c01c000c2001c2a0b001c0b43c1e1400382981103454800c81d4849040071284548042005401d00404040b001c10750300603a6280c1c0c1605218030502c40701041c90f80c0c00c000b500d11141100c59101d030401d01d44100c018802d131340203039031011030040c1c0380d400e02901d0384580c2c00345001d5811080c0482d958444a542c200d40400c47c01000b04002c072a4207290030b04044d0002c0d114440038008043e800742c036000516508405d10240da01400020303044402e01a40070704100500f05d000e2005030301429a50f0000d1380e8508001c60740c07205035241a11806203981c1c0041048031000f00050098825002c103000c20020b03041100f000b0001403032030150309a12400c20024040b00c0d400103611 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 21742740 1250 21741490 21741493
    0x30c0b07020d0906032004080a03032706050a02120f01080f07030312051306020a0c020103060e0c16050309030106030c030210030c090b0c0309040510031b05030304050405090a050106080607020f 85
    0x40c42e4689911880311400c0d0343c3c0350314011503040740003158400c40140010071032201100105000c220079000050040d80d660007a58103225803003010720b100c2c01545a150300310600981640c0c0d84004200245c201031b40011140c2001450950003d41e8a23034140000da4503041005071110042001000400c0100803071f023a40c4c2c0141c44014079560b0003804080702a040c0c40d1123242c0303802c00900c0d20b228400d2000c10241d01300700155a80d00010100400c1202c0400d0104d02180c44c101d8081050423842c40c82600c00c010fa800c2583c038003d0014507081d00c5260000b812284c42c03000700f0544081d900e081c086c0750000d40c4129000e50025045104100480502e51070035801c161800121445990740407201004941c1480d444540d074400c203802c6281148a80614950494180018042c0300d84200c1c07800001c42c0d000b00003200c214040c44040c81000c5d44240300d0140e142c2d2040c0802e01c254a040e40c0040e03085030700502101c40903d000e6603074601392041075202d084590804002c0260554051025188003200e120 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 21743990 1250 21742740 21742753
    0x417060a050903180409050a05010c030c090311061303080d050106080606120f0705070f080903240c090103020c190302060717010b0c010207080409060315182a03030c0b0702 76
    0xb20810340d280030384551651201c180080c00d41d02520790f94400c540450300300e0165864505603040ca06e0180220400c040d00007454601110803040c0300b00e800205490381b100301162442040000c02801d5003244625540560860340000000303a00c1c5802405800400e4101007490740c90100c01604041d001004075000b04000c0009102c8420070014180e48900d0100741c00159460750041100e946c061840010491005103604900740007400d00503111800d001c80494601000740500e21100040c0500340070900000000440d0000031310340043d20284106140050904c1c034440d804a180541c036000111030845031021100c14164148200e0380d01191508000380c181c443c246d1807154203d0140b041218410001c0b820b18900c3c6820340440f254160000070b600d40700e0303071941150b9005140c03500c0120341280703e180b44009000341d280510840411844083c405540f069142c00114501c1002032020b031071400d0031807040e400d01d0304040001440c00707581c40017801c10303183c50b0400d502d64010300000c0541d0b2008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 21745240 1250 21743990 21744001
    0x60a0e040b10170702010f0207030201060e060f030706030b060d11180603010803071401020906300106090e09070305010507030c080109050c190504030f080705160806010501030207030909020417060a05 88
    0x1041445008624150343d42043d9036030030089006055030b200c0d080780c1d5400002c403082416030540001c030a50f1280c50321150162640806c00081c001041c0c4119096007041c0803c00115000c0c0d0700280d102d107009482c035864840000700c803d049540710f042c5104170002c00b04102d009000c440505845d4114150b032034615650401c4082d035900e005801008000c28034091129116020a405840302180090f010940390400740300c040601001240e029031175281d00b1803d891281d500d1417800c03412610381d51031b1607025600b400c9a01e00031600c01000340d03031141700310500000000d000748111885020b29a030009072201208200800304141a40f050710014100f50500002507040303011030320380e020f032601c1138010848100002d40f014000d6610191614210104102c1400b00300b03001050704502c184141c1d4024402c1d1400750480b00224041d540456000400600055010383d0041c00054003a00b8200c800396602c503219002e030b81c8182c100305403100440010302813544042095582269a0800038045861300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 21746490 1250 21745240 21745247
    0x170d020a0203030d020702030703020a1212020604021c030219030e040b0109150e1302030106051804330801061202010f05120402060711090702060711070e0402040207080405060a0e040b10 82
    0x79000b542400705d41c0051450300b1554104180c50055178003501000c4100d686049200f44e00d8484201503074024520352414840701c1c40450400d00c100e07030041920004c803640da0102c070200c4505410440a41c803c00d0800715406103a0486440c040f486030381d03202c0060080d04103003c01e4400b2502d03201e040c00314a03007040c80386003480e03081ca140740c0e4180d240c01e10380303001d602000401c240e07009a21459402c0c4000004200654403c0c010031520400740001c2580340020340911007140c0e8981344c0841c401d901508400d01a0080300c20b1054150811070a100030641c44001d05402c440031030b03122864401101e00d181c0211b5030002c00e070014040103420458108140c400c1c1c440484100148001d00c20740001500320200150400001000c0704050f203859554581000069551441690008042406100d107400c10541c0000c51009490840d504103900e43c980da42030202075008190216a840010302010400751500070280a0858088d44c654036460030f1032007440101c035202c8071418021a400403040c0c200c00c2c3c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 21747740 1250 21746490 21746497
    0x1109090c03100506070b07020d09030b060f0316090b0901080304061d01020304150302070b090708030703030e07030f0804090c08310b07050706050604050f0408030405010b030304170d020a020303 85
    0x4414004a40d2580e41c1c0d41c1c200c81c0c507550354100f2030784180c0100c1c2450502000806581c8601c029400303c850b0b036a1081d50039200555984002007540000700c0000341e4508042d80ba8440c98007020301252815007c692100300180c04d00d8010381d040c00d60390211240c0520741410300c0c0340144a901e010f146002c2c00d280c0024100c0f080103400e6055410030200540c01640708004172001040b281380c0040c0c040c035207160020041d5000c088162090701d1940b000c1890750001240744000c48580400440c54040b03035a5080d0040d1050400c44a032a01801c600000071421146c203115903d40f2507242c1617616410450700c101140c401c0c4074500d040209400801403a18a13145200740c040c000515245040c04c201c0034034a94015a03440300421b640703440740a100090b07801c00f01401c0030901c1200c0c18800b030b60310382d0180012134030211008101c0300510b8000c500131402c00700085800c42e0083c800400c185280601082c0707950700c60380c46508001080710007040122824052540c07080e180e84041c05024407281c001075668003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 21748990 1250 21747740 21747751
    0x40b0307030209040f0615090b0a08030904110f0a0203120a0c090e0603030715060510030b100305090a08121e0f0612010f0e010e0c0603040f080706020409050f010603110909 76
    0x1118030f8041014880b803036422504040c0d200000313103c2c0d030340c54541e00c2000313002c075215440760305040c40582c51b000d1400c10010010380c1c440800850800380c40d0740800001d052000b0350b22426140412031440e02c216120003c002a1007140c000f95643c2191a20608600000405e441031052600b100c20000350340c4290014100d6410004003100d645502000904520a00d1802802080d10140004145c0125044201103c1040310149040c0703a0385d0105405480d90300d202ca507070000c80c604601c039407540203034807461300007a401c0121503200d25280e440221302c1c0c0c4000328208200b21800200305031100700c88090780c100d1b00088404c544508240150b82c0c0c08960180216200301c0b08190507411f6242c1c254051748104911440500400501c2800240280b0b514440702e02e507409020080760b03042c181042168090380e44a0b1802140340820348401c40c40d604440001c492480c1c08010000d80c14240d80070f00f80c0a544008803e9545526002c0f026003102d2840300701c041589020f0000802507604d40015940c80b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 21750240 1250 21748990 21748999
    0x90e09060f061809010501080705010302070302070b030703020405130902040506040b0d060b01030b03070f030203120307120207050a06060914060a060c02210f03040801060509010f0303030c0c02120a020f040b03070302 95
    0x80e02c0e0075000907034514843d2141005a004001001103001d0705401c294100c44103082075030140da4a0f10011000e03840740800160140c1d008080401941c1c881c8802554007541500c1c3c01414a0b444000049402c4117690648000b140c40d9112501075181070300c1050341125040b2401c100c01604c4501040c580c11160340064030f6582e4840c1500520b9000b070300a80982500101941c84258440341d00c00c0c601d207418001a4003900c0b0b519144110500c0030b00c11240156229140c001040302c1200140e4080e60029400700c48a00481a0000029400b4022540540442540810540307509031400954850042c403043c42107040400402000d0b070031800c44480d4603010f55010260061011b010500d041d201004800305100c6c0a2075041c0c1d46034007001500c1030f100c40b0b0001f80030056466040100c1c011081c0205d42012109010820009000f5800141402024140414115003540003d140c0c44400e149410154120800d0002140307170402403452102001c480c01c003e410011400300350307199030501009014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 21751490 1250 21750240 21750271
    0xe0105130615020a05010b090402011704170a050403030e0109050108060402090d020603010b070c0906030209070c060e010507021c08010b040905102111030a0b0703020f0c030c030a090e0906 83
    0x800c091604220068018074015103401e84841c42c009540301e10038182525a035203090b0702c0e8091490322109090086405035107503290308031058005210f210000d00211980c5000c0807000c0c031040d0100300074210302c03078658031029116803650801810303500d9034030000e07030411201c0103081c851a0380040d10107401410580380140c9581d00c18011a001680091001c1d6110790084000507003614218001d01080348502ea502c01070607900c0035088155503282c00004c0d03004aa0380c0018508a11450120302d04500400010507840c111040711070846105940700801a00942410241d0301c18212074034110390300d83d161900742d9600d00785035140d00b8095402000c002d01d4540700486d01d042c00c0c0c140280080d1031079848002c5000d600000280c40291240b40480b103007901c5a103090300e10315021600040164001020303901c6503175018011002588004040050341005000c0303c400785404102504003084c42c1e400946d91340d00312160140040d1210360001c1076102d44101000403e0700d010034450780001c40f00846415 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 21752740 1250 21751490 21751519
    0xb090114160e0a15170103030c02090a061d070917060114060403050d0c0209010510120e1e070906050405040507122301020a0906050a020c0d0f0204060e09010b06040e0105 75
    0x200009010b502590005444201103080d0743c0220f20b400e41032115071211010b0841125540c0b00303c02e02488040d002c64140f56221003d42031451010380d2281d10440002461500d40c10401d403000c150303200000707104e03c02c1c0c003c20444903007040c400000f900c0d2031812040281c03501c4004950311003050040d041036042801ca08a050745481040e5000b85034040180c0e0741004050307000074102085044203030f10070501c01000091600340b500d0070031078201055803042504446030b486200070345011442981c20307106104600c4900c000c2207111911011802d405482e410f0302c1d08170a1030513110690010b84c0315620700401d1000180001034036004543d1344040c000030040260810301c00f8064096005810b45060903c690385258043d40180400601501e0300440261070741c100300c4050281505800140e80082c080c80040d00d8411a04922188078142000d5108829801325003540e20507484042021001c10038840039110070b010f00160080c06456040c00c0c903217402604031070060107100b80d60040d000c1108842 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 21753990 1250 21752740 21752747
    0xa0c091208070c0b030c0705010c0503010f0611070f06030c030b0414010314030906073905150904020d05041218140102100c0e030c06040308040e06060705010e06040b09011416 77
    0x1008208000130103499180409a80d1a5a40500411a5554a010b841c075180f81d0040c0c056078141c80e6100300425209083ca43c007555840c003c2e60290780c051083c43c81c001012106e500a550142026170b4011407507024461001e030075181c1045006206604006050306c00302160000103044903009510f08075100c56042180741144203480400e500450001000024801d076110180c00303200d00700032170300b014640d061130000d40b103004048c1024801051311030400076441d00769100320914500c250a2450822542d001034102da101d502d4140d02aa124010441440242d24003240015942e04004038031100144c081e15031490701d80030b0301322000300f102032510190340300f0055010320b0f40058100304004003058070301600f6100e020706860302c24070905620402c070381084401c0d1012a40c0c0b2052560400e402c18401d901159002400c081d0004014402c01c400700d00240505042040c441000d0325083c105418904c80507100100b000d40c0d10307070520308201050140148280d6202840074081c4032580c0f403884d01103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 21755240 1250 21753990 21754013
    0x51f0c0b070c03090801020c0a02061c0603060f2307030f090506100e0606070305070f03020309060f0d0b06090d0201030b0102030f0c0303160c2604030212060a0c09120807 75
    0x34010011110030041000d4010524100407406a155030150580d0b0302e00d410300381d108085242c042500b01646280050420101070400d20300341c947c4040c0b07144441c841030012110360b0b034800e85005803100c111040c221958800e900784150300c038500f11400d440e02207070140140d1000c0c00c50030815656640c0048160f041ea031082c0900c5170b00c8011f03140c10b420312000700f04088010340222200c030f140304408141a49000000c2304e124541c140c403500e04194468032490a0011804020703001c0d40410012000719540b6000107000044046e602a40c0311070040b24201c00311019001410b000386410482d143c2070741d0f1042d03006d0218a50900e4046004011400100c0c21800b501c803051820900c00300c0d0604200030080081c51290400100059010046c110304035052449520090100c4800d2041340c0c051035488510010650254002149015500d9011039116020b04d03403003c07426044030041c00b8800171305008070707500680a441d1030f02941d0b0400c02c00807041c00c0104401001c0714000101c820030001d289030794 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 21756490 1250 21755240 21755243
    0xf03030509060702060d020c010e0d020703080c0c0307060903050609070b07060906110d290901030b070c0f0c081516110c0301090b0f011a0901050901031508010b040e07051f0c 77
    0x82d1141b01001d40c080280d00008104c00c050f508014900310340220001c1c45080040349a03005025403855074992020650084107114030318040c3c7c00109105440420500c00103044c2981c42c01c81740c604c0c50030454240100030f45282c07495007013801c0400c400c0010741c055032143c80c1c000b14009103035078951903d50300408000d180d40031001c0c00464071001c0c601d655400484018108a44a0f0a1400507000300303c0120204101590000705d8070014004600401ca80b143d2010540c1403020070321481e0389402c3d5400f80b00c00c2c0308456018010a0078000302d40280042041c0d13498401d0103140390b040c03050711826039032038010080042140010790242d2042003042030f042c1d05038020340200220031780e50074101002141242d0103070030030701030100000c3d105529482040003041c2d8402868140800440119266840104c4450415032503201110755018003421100042c400c030702c0005880140f10042c082600c041c4c201030f06894214450402c1035454007015444105892550144440c0c0a203c1c00d40e60500803410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 21757740 1250 21756490 21756499
    0x6090f03190b01080c04020705060c07020a030c030c1401050c070b0d06030206120103140f070603050711010f060e01060c030507060b18090a030e0904020f121c030b1203040f03030509060702 83
    0x858005015030b811045059078020300584d24800301103003d203c140c0c86076200007000c9500c6000040c1c0c0c2944c1140190059910007410150301e5696502c030040325030b0058005541c00014010104001d80740d0451540c44800282000780c24486116052522040144100a100c9c031001400500c442d000381c1c040710103140d000381400c1c0c8505d041010003514a01c00d000454490035135a100303188000380021102d0f03500007910000c000580c204031040b0040e080150856003400041c0c0d292542440c000e0191600d02c1c3d1890800084107483c0c18940b580400042c1d0010341880b018540c040e02213a40901140c0705c4035000400424054060130124403480f89a69988030200c0101040c0082c0610118400c080d40d4060713540c40c04041d00f10800c0101b886019200254002490380d0061498113011040c05958110001a01c0b920000d4851484047c40d4010180340065516210710506240c09015a66013101d8400211b0405c0d08108405511000310301010302402004900841035603100700484003215401351 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 21758990 1250 21757740 21757783
    0x906090209040c090b0412020102100c0f0f0f05070611040803070c06090e150904061407020d09080106061704150906050402010e04050906070e0f09270c06090f03 71
    0x2050002508101c0344244240d00704010700780302c1e41c803030100c11007542e440380d42c0700c0e203054a0000b4507245400200b108038150300810108a030002000d10407aa401c07101902d03855040e45428034000c0440c80083c0204060144d0b4400210000307a1000a41d0344007540444001555482d1880c00c280c54040d60f17000d001c0078071002815a0401015403400400c071002034a5081c89192030391241440c0010403100d800003400145915a002d07e011001c6a410070b018a40001e0748154508583c03403068001c07030b0800050b9118800421115610803984402030007d00000c1080c0750030058000c04120702056859207034038214012801f40050b21408502c501800f0700c04001c158507903c0c0c07480250004481c01da0205d4641150b58203181047c1c040c3c64403d040000190a45540c0e850301914094151000160840301803141045941c544d181c140340900780725002c030ba192800c02c003441a5919801c08010919401040345400552143c0c010394000c20000c84800801d04c0740c1a01103854103181c00100081c00703e452 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 21760240 1250 21758990 21758999
    0x3120b0315070c050f030403020d030e01030b1306080d0804080301060819090302011e021204021504030b01030b040605070512010501050901030905010f1b03090b060409050c09150a090c08130501060906 88
    0xa261403180c900c201d0a03110007001c207817111a241d004902c00650040c504041724400288a1246440100d205040010b000103070f240110700c150148440300350515554100601a2003010071201845800340c3c54650518a403603a02c00c00e503800180300c0d120070321416402003070040141020042422045d4601000014110706009000e404070080a407110502640c5103105c0c03440b5402140c0040000c41101e2400703865a9003030008445028096442101003404040006000b20740340e14000c40c042c41c40c1c0c40103070500303003001000c541d809894041440700401c500169084030f000d4071070441c1c609080264580485a0060307010380b115840c020802d510305021000d850005601005004030304840c040071002c25070205504680c07000002030302c000142c43c0020b0f407915240e0046100c4074072680984600c45110000b00310002c1c819035942c0c5070102c0b4603145103250b06020070300500600b2100014490900548005070074040090700060811180407a01e805000003500400000c0c50341000400240b0350780c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 21761490 1250 21760240 21760247
    0x5250206190305010b03130308090102160c0f050103060e0c03041e051507030509150a0e030406170606031306050403181403070b090a05010f030b2d01090303120b031507 74
    0x181d40e600000c40c0c43c2000118440a41409892054182c1a0000e0040e00d4580f41510180c100402c004001d41d000c1040f4484980c000d5030a0103824469010010558200342152040790001d80089040600e0900b00304081032001002139040030742144001d5481d01c035420a000e80e038801071810768501817000c4010341000350000e0a0360408010094807a00e0351a60301040b0240e64099600d602c040d0700c0340c070000645101e050415500090001c1c0e0015145c2034010350123045400607071192012a0711310481714500b401410003180d00000460f0814914504584812410030044901420b00c135a1007001808241c05154040c03202050344800190507652602d450b5080084448510300900031514001011180003064540a84005020360041810200115800e0700062404420543c944280f4011926485c2e101c0c52a038210030750008641502c207640c4580d03000c03c11001ca0400180410420206e5804510f41c41000d51565010a0350301d103403800207240000c6142240c0108a800041c002030540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 21762596 1106 21761490 21761527
    0x10501180816050a060c020306070c14011e0b0f0d11011e0302030105010908030304170c12030c09040507020706020d0503070306080604060609110a05250206 69
    0x560700700040c5403076180101800280781c1c01205000a0410032040405048541401c0d030413000c0e1039000c0b139980e40c0700901075070800040b58080310810032000205402310301e16400034443d1000c81c3c006c82e0a01c450900002d6820351401c3d4065941c1e00f001c0b800ca41c01800002d004000545058841d05555030106100604010941610f405940c00c4050840005911a940180c482d81801c0c0050603a9229412204d0150b0090040100080300400c2c5403044da081394100c07903120014240310390315003107111700302d03080d4080007000300420764045502500d0340d18411502070040d40c641c100143c0c0c81d0704007401550016080310902c0c0f01000d00420007160800c2281c5030004a442d03a501c101410304800f82d40448400e03445180420001c01140036400c1c0310b55000300080e103021403010010b41184202844600d0584142080c0a621118038003c8541281c001e0b040300d81d038410703509003000c4946 = true := by decide +kernel

theorem cover : BRFrame.Cov 21582740 21762596 := by
  have h0 := BRFrame.cov_init 21582740
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21582740 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 21582740 ≤ n) (h2 : n < 21762596) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
