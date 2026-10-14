-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2212
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:00:31.693995+00:00
-- url     : https://prove2.me/submissions/faa9f103-bc64-41b3-b639-b730ecbdcbe9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 397661870 ≤ n < 397841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 397663120 1250 397661870 397661959
    0xb0309151303030c110115081c080f131205031009060501090314030c150108070602010b0109051c0605100f05040204050105030c03070c1203051911190e 67
    0x845180100c622040c519070740a810b96094004180c0e1410b030b00c0511400d0074004500c6602402138266142c54110040226403070a1009440e1541c0071140002d50125000d001800950058089a02c0107aa2000060310303110050694203007031005801030015590800c1124a140d000300066001c2c80c82242d0240b840e581e982840000c0360507a001c1e01e0700181d18804200041500c2c4242001405981d00c1500d02e420b6001c40540d207001d525440e94402140510700410a9020a10415004000c00c0c0024000541c00c00d00003403220456000307282c407400300a9502c1e09088140c100c0e800449a2000007000390b030811100e04040302034a0311a0b107620800d01c21021030700e070805009807412603006844842c1140c4818941941c59000105440c1c1080002800200420201640c88100c4400350700d0003c3e9074209a010481038108007007210180c01d0404540c005039846080441d41004040101c192442e6a5210115580410914030301d03400a001c0000184005804040901c13071500d0700740004014121 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 397664370 1250 397663120 397663153
    0x8060f1c0c15201605130f050a0b030d0306050102120c1c0e0f0d050703021c12030207020901050904020102071503020909011d10030f0807020d0209070c0b01121713050a0b0309 77
    0xc01020004c0711040c0b200c20400740c204010390700d01c401c151040204a40d1100e9a102c8201c880813201d144d0a6a03c0e03a20141481c00c0500265559000a181c1401450309200001c0d40d103c080b4240400022000203c04075103003000d0118070740c0b2012030200c25050b145038520043c170030760000203054480e0025000c00509444c0c804400e503404c0b9801009071002c0da28503000c00c85200240c411651030580c2091510b00003c03070310384840b8a15446510016180c01d81c0d4018028280c005801140c0690b04041c18000542c0e00021404100d903040054107003c002c00e100c0850203400f41d00c40060304004820300106d04442c806402910400c1c246881102c075a450400b00c46110410b440b02500203048241100702050319180203001050001d000ac00500b00b07294041405120201d078004001441e140191082103005003049004202d034608503c010402074030750701e043c080500e24488031510000380031456045110481e000505008040780c81041c2c1c1c0b4804000a07a00c1240c58040c1809450031040e000c694 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 397665620 1250 397664370 397664383
    0x3030501051201091e051608010f1a0102031801050409090305030405100204052215140906030304060e06030a1103010308070b0c0f1603030902060409090308060f1c0c1520 75
    0x20405c142c15040d01c1481c0441d00c001802c2030b4255014090780c0992554002920045401890b11400008221608280c2842160754011000c126848200e000c42140c1c2c1e400015542111120143e40720b4011120005a69601c11a032107118206d04242c1c0880505410401540c03003280510b003030724041050521a10101d100314019158854000b4001c101180030307071580694804404a00040c0071158600002c2503072141e540240c0d041450a80311004a040c00c080054100030103070020341c1010b050550240100c000c0c0e4005a02404012000600d226256048075404040500009a43c2c0d40c5034149081d4651260205541c4120744501003a40341c03e440c1d044590f2001160646030030540e01a0740700d9407480301803000f541056102d950740405a50b401c4004c0c0028408001c0002c0c100595140150002400400c450311503c4800143c2c0b02e1a00d03040740c2c000304c03030112420814904140e0301d4050000384594016099080c3c00081e00141345802c00d800e0321241400c0c602c3c555000c0c0b41540340554800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 397666870 1250 397665620 397665623
    0x21030705100c140703050708120a0e010e06010902090607061a011e02060402150d0f020c0708161a070b0403080402090105030a0c06031a040218040c11070b0a05160303050105120109 79
    0x414200c0c61200815a01000d080142d04c00d2806d81d103802c41c640c4070403140c0d4000701c1c90f43d04800542824454481300b2442200a444902c00003400311900d440c08030b6803207400500c2004a801c0c2c00088445403590f4031404ca80340e4a51203c3d0801445070b40c0001c0b0082c040c10305900d18046480109003a041c4c80941203100441100c41e03006001694982c0d0034001690011040780c2079070324042c002d607a0905030781d02600145062a0000584400d24031042c14500700f0190301c4080250040d0010000016604100000352006007010000c03201203081e00d07003001e228110014120401d04400d21080517840f100c940d010b140219540429030f601c4204141d241c0072031850040503011655030400000303010382c0101d80c07005005800c4030721403803003600800e090381e100d407141080c032400d20200444140b6040c8991a02c491513031401649102c914020580e80340758900603800540c40101c1c1c00b0b00b0640c821022166000106049441030b00c801d4613019010308000e01a40c1d118920004508029500510401c0c450f203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 397668120 1250 397666870 397666877
    0x3050907080616090302100e03101107080a090305120409051b070605070e2e11120903030913020304200307090b1305010308030709150801030201030b21030705100c 72
    0xf074a0700f4080d0a01c001c40f44006205000c09064004090b1341e42d005040122a095240c1c0642c80a00c10101070900c6a580803c0520600e00210188181d0411003030f1006682d01c00c0c001e980e40c2c40c5480d01601d20b0451544000d000344103150101140c031544902030400c481d10260103010f10344882030031245a001c0789800c10511081442043c0c04644941c0005400c4000c6003042440c1d0406940402c1041c801070040c240c1d0700c0080c04002d4180c00713403410051a44016494419580107001d503100e070710341f40180804100c065010440c1c52003039130240102c0c0d440c200c00500f40d06803140d201c0c2514019400855003070390041c0000c410f40c880e81001c0c451200c4604002006801c0f07160134849043c0081001082c1250060580c1d0807040c030380e5000b0700c1424069400780048940ba494001401081408181c120300207241110310000e000a8001c1c40b16419030341d0909020444e1034440b0301045d81154020410304411615071005125a0404001020081c1c0102d0945140c410640f044109980c204120350000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 397669370 1250 397668120 397668133
    0x5010c11040207020a0312020c090901050609040213060801022703011505270c04051005040e0f0903130303080a060918120c0b0406060608060103140714070602030112030305090708 79
    0x9898254000d0119510045c012401192652910b440d80c058203605040541e00c5080c560b45545400300e06564000400300007400341d41350042c0800c01461010780001d0061388036040b00e03000d10700160040009000c2c3d8034021515a00c80721403050700300600184112009009514692080c1810701035404052400c00740074941624003014003007105030704404150700c1c1d5803070300c070003158034615001b82401140c12a8503191a5030406007009040300207400c1c0c0c841448030421080112010b04918194415601c007455140d564a0146580c02e51142c203000800260703500d08007108140d00a448039005d01420034003000f003070b41c48070200c40c100c451a92031825140325000800000500b22444401c83d80c140349040e0007010180c0e0340d2003402c5070058404440c40394665100b40705075903020003ca40c1c800c000341f03400e0040692280f40c03a4107002000d0181020407402e00e100c881c4103540042120308459105070110350b2036a44100c0340494240328142100060306140104000c900c0018071202502c4508014088 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 397670620 1250 397669370 397669403
    0x6010e10111006050901050603010311040b040603050a0c0303020c0a1a0c0a1b0e0a110901141902010e060a0b03030409050a150602010b010f0305090a02010806030106171605010c 78
    0x20200018a58108001d881e0340d90315030009080c009040a0842c064010a10b24103207000c000305030070141c21082c007980092004001050041242d0508203805460000e016000700300450090529034001500610a04048804028410f202001164040c0d803c1e126010f0082c0100000c0400500c03a070000c040020f2400e00c8084010750050000c021102c04441100e91207a07264940c4054400401940f0010070000300002c40800d03107000d5004950002c100204910190010841d00030070400380d04021020700700b01c0d522003544045030320100b03400d20403210800c030118000303000e444811005d007024000c00003c00e03010152405075a40b0068024051810103041ca4019801004010300f000c0c81c01e0b0310381d07c2c280e01002000900c0c40c09451076500100d0400e0301c20002401000a1242001c1014900b00802010f49008074440c0c421a609180011276030302d4080000b030140115800816004500c10b14100311960001100b2144007408911070740c0040c3c1d141c005407940c0800301c0d0041c0050200c0300c940c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 397671870 1250 397670620 397670629
    0x190e0a061e23030618010b04020304030c1101030b12070603200f0a0c02060406050a0e120607030f09080a030603150e07210506040605071404080c0402210705040303031406010e 77
    0x1000c114003682d08407841034000240350000555034041045206602c546040b8403c2c0100758017414140c405500c1c6040950300101502e25048018250034030f0070030030000a138400e41200840000061031043c001d0300c81d040e1161079801d907200d4107002c2442c11504150303190301010504100d621045c5241d080c40b100c2d000220083e480000c140081101c000d80301401650781c3c50180028040590351140c84901c45400a001c1c3c1da03110310b5083c0b15401c01103100c03181c0340b070000781168000034515020030207003540902000500341d5120020001000490100480360341940401c0407240110342c02518003a81e4031200c02101c070706a2031500c0b6a0071052040c8603210143c01a581c0c05205001108059044d91300c034a82019803e6400300c90b9144c50b901400b8030180e01480101c80c4650031010b8518003854400803a0f07031440c416629500940d0040b0300c1c015a40c8118410030308203500c42c010400d0380c0c5071000e002001035009010460100e440e24590a041c40d10754014284034281c1a107402c04025044810003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 397673120 1250 397671870 397671899
    0x3140f0a020904060c09080601120b070c050703060b1801081501061701030b04020d050d030c0306050117010306050c07020907030209100503040b45010e010504080f0306190e0a061e 79
    0x17109110260800244030342003004040d0080c90501c031106030119031403030018460240a403000041269001850022507008200902281d07807007200050350341181e00102d0300769401180300800380d05d203900001030003171400300340080384010343c0448148036a01c030f00701518480707003001405042000c4000107000262241c41540d81050000700303280c013590f05c95a2024076200110340c640300004d840e0b034022141070ba01401082c4c094142402c0000c000b00d00b0001002d421001488081c140035242d20204d074a0500300e02c11107005540203080064245070603440078010f5440302101e10301406650610408040c81002641d010b01c0d0300c02c286d40e81c1611600146080c0c05158100f11401151407000f8030090740c00c203000540d0340300301032905825078425004010708440c0c004441c0c03101c80e41044100400980100d04507180c81c4079002c41151640c8620000c10b4031099102a0410344030115080414001400c00d0b2103413050060581c24089251101d60244060501010101c80014070000c140504101400c41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 397674370 1250 397673120 397673141
    0x60301270501200a08060109080a0b19020c0a05070905010311040207060b06181503070206010621090b0609091c030209060717070506010f06140c010e010603140f0a02090406 76
    0x4102202c0543c601e0460445052144600d030000040d50f9603165003001005500c90001d00700700c68a00d140a480c180c4912202000901d442d03002c03000101c10011200480b264690080411074903001c0c0005c4040e660b04401005a4039403042c50800280c03500307140a5281a40c0d40b114142e081d004a48044c0701c06508141c2c0c1c1180c1283d103c2041000c961074a00c0030b00808048060704d108600c42890501c24140f61304011003513983e8080003045041c540004805044410b01d1a0003441101c10302e02d401030b000c410f2482c941c81581400072080074440207018482c05004220b4040380c003511008000c503034620354011072001d5440300030060103a8038001e501600c2c0c1c1c1d81d4080c15491138881c1d075598050150700300c0800d0350700c06400170a01e84280442044580c0c05030042d81401685982400d101410002110a02400114000501b02e41c440029000868400d507144024420b42d42c42c0e141805400d0a80500842c081c0300c0e581e8508800d0000065561080f42c01800c01d000d41c0c1c55644440003c0c0070300303056 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 397675620 1250 397674370 397674373
    0x3190209010c020f040b0d060606030e1612050f010c031d0a150b0409050f01050403020111031519031e1101030b01080406020706020f0403050619090302151504090303140603012705 79
    0xf256405034440d0f807e0302000e10310807100054400d0500101504680300340541031040d900844514248409c0f014034070b0140c944481c5140d0300e5116900c2c0407450711864086201c07403542804941c19410f509508010050400c0c4a00708c0028210080c030b0558540d01501e002c5d103110280b40300200040701c9603020003903248001d000428404000d482c2ca1f0b1402c0e598614000041e0354800800c01818bc0c28490b00094981c9022011716600f0070302510520004c3c01c0e240544140c144694403000080b06800e200e0095921110003040c3d00c20306c502214001c00454000e80300e00d8203013900381c000c070340c400d1140d00c4201c0016191521240c40380d0f1502c41c001d41020000301c0d0465801c0007050b031041da41a01610082d881a4010011f42c507215902d45401c9401d0449200c0c2281070403a198000b035004180000750050002c603001090b603550500808946000f02000e070030901e80301c0e000742810340c190010403000d1050420a0280d845640c00c2c18202c550f10000c420111919070242c2445403140c60503100b80d03d00800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 397676870 1250 397675620 397675631
    0x80604060f03030903020901050a050603181f1b0906120905011d1609180206070c05040c050c01290d03180b0301140d050d12150b03190209010c020f04 66
    0x150401140c81c0e05400035404602207040801c114500195103901401040d00c03503a0b869803410000c03668030702020307001000420001b0035410300000100001c800188840810812100d800140023008140044241407910ba00c0e80c80c0895a9000d8407400c0101d807030695a0032001c14400e4051802088040c00c211065500c5804068200107078580110403120307101c01402c1e14281010010354452a541c0c00482c0c040c1c288501c041e03481c541c043c00d0003d80c40e0103560b038650fa10041d00c0c00600690468200d903511a01e411a94041c05907c14081c1c183d41d110340f07008014032449210111004140080d51034810003c040000d4110300f0312004007000300d886070910b9803198401001a031100c0702160000700e03040d0408001045102c021101554404000361003c8410040c3d0b80caa0380d44075403880580308144a01d0301a00103240c0c20f1940030f180c0d2156680c0000c00a10345907010a25282d000359114207441e11004600c580d402c0b520320844500400507101d0324181c10f100d5081c41180001044120750240e07441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 397678120 1250 397676870 397676879
    0xd0819020f01020f0405030601140a0b09060d09060b18060a0506070f060204080606130b010e0f0d080c0c100212040603090312050702010b03060a0903050301053006091905060708060406 81
    0x90001d4004d0005544d6a03507155401c0800f0305180901c160711400003002c0d10166409941c42c1c440e0814203071200180110340c1c0700d640e800411454413074112440f100c1c6150840b0322045c0714065000500c121000c89014030a4005910384100c442c500ba6020343e4880c4600f08100000d1400000400081c1d219400000203101c06480e1803080b41c116500c020140c1d00018100074051a159190442c1d4400981e000c000c400d40b9000000d200361251803015000e107854401000e26030ba01c2490040d07006138081200340d640d4031a0070226455480312449980200b02d441c0c44000e0311400030812000e28410210290705140c03600804501402940ba0294248041c040d00c1000224243c0200f0f071145413903400220380c89a01c9014503251032001004840400d2400100d80c002a50000850341107860803a07210307040c0301311180703c006001c0d031410341f6201084241c80040d0f071a00c0049003c0d88112204010f859901c5036a0003a0060340d025203100800070380042000508081c001e044e810340020000d000020156140c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 397679370 1250 397678120 397678123
    0x61c0b040227241f090b03010e06130f0207060207061d0a060234030207060306060504030f210908010c05070b041b17030c0708070501090e0a02210601020c0d0819020f 73
    0x1001c41415404500c2240c1880b0301e41c02c001d1400c01080e8a0001b40c0c51985040700120f207140024003107520801003070b032a80b004002c0540019451180c014000c43d522459490031000a52183c1c3c0121119800c0544500c42d0f120319451407030300b48032080d001d4150200640e40c0c0b10020740c061031900b03449540a400500310148113117040d05400d0b0340701a19422030110b508002e0720344032140c0e12010805061141c1808460b500c0300c156001c507a0711008a6042001500d8582103840001351122508190010100d501aa1020483c000c455525008100e04103e08001716020708c501d04c000303012a0448030105000440c1c0f13416514040340c1c0030030200340058445003400e02d2020701800607541c03170340046008001580184101c3c40207008039001845128540317400a0001a100d1080485965a09001400081d5a40c04940324138584c1c8480b10440c481126941402407070035500103005101d407141d40308844c10818440c4001701d0708441541e040c0494580350a400140d001540c0f0300718095800e1100d54641d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 397680620 1250 397679370 397679389
    0x91802070804180b0a080d0f11030a030b010f02010504021804150608010b13140402060c160902040e0718260a0803150603040c0905061c0b04022724 65
    0xb000c1058610075103812a4016510407804e21880f9059417141080349050016071807441c807085007400200321510b4401610b00395007813002004540030005450761259410340c411084071400341c0b110741503a141c50004138200d84049800940000c2c00200c0b842c050100c8814040e4050b1054500d4002103081c0712440c0151042c680c400425691520030b415042d2400554501440a00c00010010f2548510007000d05050241010b800341d0f4001408031000304050010b54101c44030140401e03440ca81e9518900d0080d0312512480c03d081c1203a102045000d4402c1950880380b000d008011400715003010850f1249100d582d82c402c482e40001020031401000602000b20014000d40d149900c0e03140581c00d6000d92408070b00e0381807044a0400401000032a0141c81d4011380d488040c000840c1e548140225000842e01c880400300d04003124070401c1001895920103104034400d03980c6854940d070202c10500d002c0c00551001558442c018000f800c242e042c844555100042003442010440c4d01d040850200301 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 397681870 1250 397680620 397680629
    0x4141f09030204061505040b0906070507120b241504120605040b06010f0807050a1b0f050708030412020103050910111e0a0509010305041b09020a0e0d03091802070804 73
    0x500640d0200103614051151200030a4083d0700da984441e80c03440020164030580c02083c814800204a04030319858550580e02c101390300c4402c13a803429403108030311981100805421508040d041d00019480035603441c2c10781c1c0c0503154070b102560019142c010012a841564011101d5070024400003503d000d1032903081800d54003500b4006064140303070a124400001c01080d103410720044e4142d020006a11800465008805180850700d500100f00119014103800c4400c60540c1d070440c01080500050518000d042440360b0b0407248515503035148030f0303240c3c001c9114450001c44008030316409035020740c200071380c05a008410b031032030014900c607c1d9040350b0010510505401002c143c440c040302003110100400c16820015508020711540014140d00ca150340d1581003544400208040144508104802a04e4095200b0001d81c40721a05070094101b140b4910014185120301c00046c202041400103541c1c140c0d95181007a424480814031840d000158065210750030000c18010800e008082d00c080c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 397683120 1250 397681870 397681877
    0x309051002090111120405090901061a0903061b0901030c05040e0c0703090b0f190c060c0302030a06050f0a03060c260604050705031317070503210f010b04141f 70
    0x2014810b000405440340b41101080b540d000d442d45c02681030500c400d9608131102143d14104940d0f51303817045800751950354000b10008408400740b4261480881c05040344440907400c0b91810380c1c401c85400940148002c4204485400b00b10400d15544641c000240c04440b606106140a07a0b40200040580c0b0840b8409034010b004110b0300d08140c0e01c5481c007001401d200010700c0c05c0034207905100030140300705190309540c00c901440000b809800340400409860308035008015002d9209400b9000c1c0d40200d0b1110400ca1a1580200d5145841e04500050b00d0024200803c1d05055a44040c02031800701300d10024000200007034042d0320380c10010034050680315110a10b5500301007007400203446000d0302030800d00400340b0030080061807840031040c0b03454011000415010304220000014420030001030054007001503c40107020444074001c1c00172401b1510125907540b41d850780c0114220078002d286540e18204020003d100c0c8a100102e412000104900e1107030303170403c03855802c00b114583c030040031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 397684370 1250 397683120 397683127
    0xf0503130b012607180f0902060d060f0807081209010212030a09050709060803090f041e06030215030601020a0b06130515040e1209060d0905030703050304060507051204020f010309051002 82
    0x21500354043c05030400e901d080102135260900c48412510310300350300d032110410780e112294610984a500400c41458000d03200f1507590910411400103400c1c036000d62070b404074030071800013540c08000450740204c50301c003009041805a0300c030203207840d41d0095140754114400d000383d81ca540c0126030011402550860380000e05102c3c0c03441c0060a0150b6580a410700c249040010084104040115040c210080b96007131a1001c070700000070010020782540c1e40d9024424056005507058651248059030300846443d1102c5500b20340706000740c4800c40d511401070300302130b4031540044d80349004a90401d000810030501001c25031036031400c41e50102d69080c107400303812808145505242c4114210250b65001401d071204003008441494425010725500071800025120350b0408180d1105840380ea100c010741c5d88d2044a03082c001c06a81050314140c803000d25100100d10a180142d0448016140d007400e1192160360301c0d001c115819543c4003440f8103040d1100c00c054001030301444021100c00d01c1d200010784 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 397685620 1250 397684370 397684409
    0x111070b0a060501082706090a0606080c0a210204090605060405060334180204030317040209040803040f020a0314150f220606030309050f100f0503130b01 68
    0x103045000d0021031009180c1041800266440350301d140c0c1c041ca140011000b0101441c0ca41800d18801d611445014003450b000c0c450104804500000024064081801240d480b6422503403501d0440925962025840c10102b018030104640001d12407e601c0d6410b001c2e05054012400760b400138101120702d1a45c0d14100842c42c9094891b090301300c08194010110301e01e205401070f03015a001d45040c1111001180e60310b903149074680c42c0001030012107002801140ea01c004810194210703000490124212038000318070a02100082c5101e82c0e001850030301d10351155221130186500250058501880428148016840b030348880001036205014403820f049814569a040106081010804140460a000205a200c000b864000c01c100603910301192906c035004185204401c4002c1400b420b04030000185500400e900d01221002c0c0c84500050800d98100814042480c59000110703c1c8141d540c018144914050341c1e04c070b100b17031070201d011605684030780000c1c400036801030f40807100301d045540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 397686870 1250 397685620 397685633
    0x23030f070b07030b0d060b0406030f0c06020c100e0402030403200c030606042f040e0408030f070519030b063c0921100509011a06030c0913020408011107 67
    0x940c0042c2070318040000c40c0d040f00020340544400407010b083c894541c00658a140e0300c0e41d00100c01140c1c17008403500003031043c1c6840d06d08011075108034000350045c080c0c500a94200b514140d00ba03d0351507640c05100a141104100081d0406002035041102410480e0162649950030481c006100c000030500c82001c00304141c640000100482c0c096070620140c014011000141c10b1421264240d1081d0305890f841c0c2e03001c071305018603801148280807a0041c07209000c0d101004600821039032649801d00e036907541e8180c0d451b01c0341035040307407040c00744407220240b40d4820350000c40308010040242e464118400040800c0c10b0040b4001c0e42c40310408591032210280c1c5204808103005007944a50416112100140c050034030003000b10141d89000b580c8828110060011000c14500780301c0c20001800c241e401c4500030301c1400607403806101c0341c0396003c0491410701c3c2540e10449444001a18203a40030051084101884c0c1004203d2030f020710012450a40a025413070114030390b07080305602c070062800d050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 397688120 1250 397686870 397686893
    0x30f0c0e100f0c060b031504080a0806060324040f1d07091109220606030603050c030a080a031104030602120f0c07030801052206031202070603150323030f07 69
    0x8005200c04411403480d03498008a440c3c1403241c10410014a04000c100403a04010f0300507280c0d12200c000004110400c0300d040061b101da0101950b41c10156604d00d1300380210b40c4030945212000540e61042400110752066100c111484054804182c42502850407026540050603400c0c91040d601407541910204101000003030200030720600072500c04038a80c2e02c2d80d11515a4450041d02c030b0f07003000d44400c4001958021202c0c18800100700031aa2220300070020310890200303c0781800356050000d80c4d450001509800c0f2a00076100614260014900740c1c0200044e54601011840074440040841e4030341c8081c044041c41c000d040c060a02c1d0000c128a6040c03802003080d0710210040c00303038002013036008d03036854150343d02a134154080c029100c43c9030103551000140010b81505143d8044100105c1e030f40031031200c5071113030220f07510f480d1141001e4042c0d8844d00c05880314017000000c10000b140c0c0800a04e02c60750b01481c01989102840261030342168001c00750400c0440001070f400c0c080188403620b2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 397689370 1250 397688120 397688149
    0x1109360f0102070804090213180f0c02011e05100e04060501050f03150609040807061a01030b01050c1507051b0606010e060a020d0804140d02100b030c100f030f0c0e 72
    0x71454044a559510b619001d5809906c90040e4003040e80510f54070f0010002c005080c10040d955900c8461141d903001800341303020380003586420504081c1c0e119005010b841502412501c406008a0042864a005250003098160259482c000004041345240c00311801140181004117046d03040c4021b0203604140d004481b070295120305100041d98a6103000c164010604440d800c0064580c0c0c141459180282c1c8030203804540ba241d250382d90140d4010030b0078035020081e00c3c02d100840b04130005584034018540d640b5010703089101c41e2504507540250640d842176041c2842c500b0b00302c00030084944901009500741c2c075030344044244a115038103c80504074000d4115003241c40d1645400d0002e4980d41c90510f000140302045012070708000541c1da0941d17411800f00c007200d111007070804000395244814290180410301e040b1648040382004240510840806007410151145035681282c505045e000440200369076001e01c0c4110a07500e015081c1200c5076035980f9495408002e01b004080030740c8102 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 397690620 1250 397689370 397689373
    0x14133806100c0f0816060c03020307030f02090a03080f0c010203240a0b040e040309080f210f030403140d090b010504051806070f0509060f03160503041109360f 70
    0x41480004107030103d200c155960015441c0c1d185d17400c440c5000f1003001c4201004000c181045070a401441e0300d41d000d58441d81140d41e00b480301c5280f2140741d00c00c0740305174110700340c101c92081024404660f0150080030001003403c4594035103c0020701283c01c9810594118541142d4101c2140140340c4045104623242c0045031b0320440240b400d03110701c81c00d1185200e0880c46650803400141414014a200d800401c012416540305895180403a600c0c0c021351450040c1442c60351400c4d5040c4c040280c2503ca000840c401e8091443e1103e85082d00c6039031601c028041c80031401c2156031100b003210701880c3c001500c248030327040003075040c00c0410090f2600201940c240d4115400140d483c4800003428030f81021007800c0086c02c400079250221858810100404d401c588002050408030b00040000c2d886800c020100c405c007001040c070202c546110603100a00100d40a0908001a14018800c0746d0801c1441d000d2001c803011f15a10b800c90340b140e80160059000b98044ca81c80c9120081c8a240c400030414070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 397691870 1250 397690620 397690637
    0xf09020a05030106140903010905060109270305161406060906030604050c0f0d080f0d06120b0406020310030b07020c010207080708060c070302151005041413380610 72
    0x358028030714001440380d5401c2040d40030b10294181068000c942d400741d0090700034040d608041c02c0482e6a44000c0c0704039203442e0314080d80d802c00014040411203869113007981c5a000c1c1100313505c0c01c075401d4202800d50b561100b80c00c81e044000070404508615040c28610191402e0b2410b4010003910180091882c0c2c065000308041000285001ca4140118001102c80040e020f810340301050500b410028000c0c1444c90000e007865030303441084040c1c201e052450341c1c01c0c05083d44503440041400e8010000a00c24014440840e000034155001b4542c8401c0c5188041081030f500d80302c4210164040d1009005038110b507407402d50380e5030f040c00b400303000d003544c8002851030916000405a8558000749000341c01d40300031a40d032081610a0000c0e603149240329240f01c0450600c4603002d203c410991007054031030f40c5400300f103820b0f10030200700242c0300b1000300980180341c3c080360321002c803c0015415078038038100340c0031000e109444007c43d80701580214158501000c1c94039005010440c00c001c0d2461040c8420417 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 397693120 1250 397691870 397691887
    0x5010603111603020f1014010501050408060109050c070b0a0218040509031804090b010f0e07140306010f0207030203160305070902071e050705060d021216020c0103090302100e01060f0902 82
    0x220215605105032205900b500b0314107040884c1041ca0b560b0444440f801001184007401c00d5540194860050015070707030010382da0351401500c50784030340d00c00d00110342c2202d001002000c84a40c8070342d40c000c1c0f8000a903171400300c240e55402038040b0111401a40190f000c500e81400c02215112080390b4902540c082003541400140245d883c041c104d4601300041400c00648000c0c2c13101e4100403a01740d4445824201561070341c030385040c402c2d40c5003d2442060340600000b02801d00c903210381010080e0103c4c0603803840d102d24004560800c0041004415885601b00000068038104601c01b99200c0310121603490604501e8481e090803250750082100da0700506c00e50010484007681000000d02d10b02c4040f0501c0c583d440c02d0303801c0100c698820381d0f00c000081980c807081d1006400070100000c03940d1130010a0740d9061074400c2ea804080030011b006903c01c2440741001d500a074040545240a0700403130b062004090341040a441c1c01045450300f40e51943d2042120103081e2742d04001400907000e0550516001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 397694370 1250 397693120 397693151
    0x13030b012409140a05030a0c150305100e270607110102030f0114150406120e0a1109071403041208160804060b06041d011a0c07150306080712050105010603 68
    0xc5000c2d41d04183d002e80500d41c041d603281c00d02480182000b0701510101da10508024031050041d12801d0070f15061035441e10072181c031910800d40f051198a402c0c3c190703107040007141e00350084024201c6d081505403503807440902e02e0f524000c00041800c070f00204050710b4113a00041c03800d4022130541c3c10583c0140140150720102c0078540d419101a403030041b102e05140800210307174441c0c018280040300d034000780c0890b00d00e910050b038158030b101c082018069281d2444d0244d070340340c140c4280506200000d4814050310f1800e86c15142d0130484c035240c0f0041c1e400031488211496401943d08030b42c003052112035174502e45d0300503036560b07400a0341000001d0400d410220241011600030b1009100c290b0b500c00b8100c2d60740d43d89081d42c0c017601c0609902e032900c0030707a82d03416030203540c0038010007000c26014240c0c20100040301c0d04690b8142940c10261070305501c0c005d24644041c200340c3d4000d0030325498038000300d06424100000d000910082e2414900c20709103003409403c60700180c000710101410500100108400d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 397695620 1250 397694370 397694387
    0x307050705040c0201230103110f100806010e150d061509060e0604090603080309100e03070807021f05040e060105040b040b030703090b0c12090123090313030b0124 72
    0x10540340400c3d81944000220f0042c0a002e181c00640c0a12640c4819581c00900c1c52505903882400744031003613085103003042240880c1503c010707030004601181c2240103100308201600444107061110400b581c100010303100c44c0c0701c0c06481000b02c81c00704074504401c04600440d002040400003c410760f2480040081486100703000d484288445908402c0f856103400f0700301c0e03004100707103601002159100e161101c4294000e4406c8004d07445072042c2c800b070385201880f401c0c0c1d600e204c41000314540050f650741c444080e0010281685e0094803170300f0242c00707038402000f60740c80d160003a40e80d1995941421810864004090b02990410006000a119900d581011a4142c54203d00455180c0e5210b8104078090440900e00500100404091204002e0601c024065403444c1d2454402555905000ca60880d100041042d80044c080e0407524800c2e482c0320896038101480c0020303a89003003545001168441c03120b030710031640c05c900070b001003205c170304103980c0780c452f00c28444508803106944443c0101060b8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 397696870 1250 397695620 397695629
    0x60601050714060a0204080c010311030601031d0105040b0601080a050108030717090d081c0b0904140f0303151e10080601030225021833060705011d03070507 69
    0x800000c1c0c000c1400700b11140041d4900291046031860700d059800700d0040c0d086449103e28502c40e40300502442c0d0700a0256166110b280030019056a84e03400044010309207101b10500249000c850801210000b8010b0398801c5000d2035204045083c454001410034100801d95440341d858000140210100801200e04a0f50021080180074040303980e003410905c14013020590148151560b4000c004016025011201782d1034150f60000d0340c051031880c15030b80001c0da1142d10007040000075001900a03240c48442c0803400c02140c1021480c0010246954000d407200c030901c544400390030011780341807802c122515004c0001c20501e10b46640c042841e110100a171350083c08980c0d00014942c2c1d1080d0305481e42c402001d403450240b40e0b075042100d0004101080140e00070302000600c81d035103244000845004540d4408003c0f060101046202252034802c0103080320b04c1c606d0700306c2ca01141e43d00d4003c0c2203140e00600000070713004e07094411070b180c203525012a0485c0740c009000c0d80010410201d641c0f0700303d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 397698120 1250 397696870 397696877
    0xf060503070e100801050405010f0602031c18140106060c030c260a05030412090b04090f06170c0f04231017030307080601020102040e040f060b0301050c0a080f0405060601 75
    0x36114041d06492404088814542000c0c049100c180c1c91a88102c0132412502d0a0f43c1c10400c1766200e61201d05148030740e02407000541d01c20004203000c15041043e10004881c0120001342e441c101d1000f080794045851425580d031004880250065002032081400911171420841c41208680d42d01824000b171030300b80600020461410204840000403186040000094140c0e070703201e039051806041c541040d0350554540340100302e9149040e00810748001618420b0700e07414203051a01110030081c0080c1482d005800d92103100c00a10014088114115005214068201040782c4000d100d1070f0031076501d00038030072401d010004071060340035880704200c11402080421507941e006500c4074541002e03446202000c040d40c00c0d408040350040055409080203580b540785644030a00124240d003c0d80c018513600c100c1100c045000502b6100400b80040d108203000715100b020500002d08488085a640c54103100001c0d60f121020307400303e20b4591181e030300150385095041517181d80c2c1e541c1c08002c1505050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 397699370 1250 397698120 397698127
    0x3100506031005100c030810080c12011b050a0215060f0f0a1502060601020d0f0206220c062a050606091306020d151d0c03100305070906050a0f0f0605 66
    0x30030351514810701034000076000150792140b25134010602c03454034609170002610800410117004500c01084201c45601e801000300c50824030400106020410210350150b5a8007402100d070b480d030b41c01030140c0352296224039845802e8214084c0c18002005003050f6000c10080401c640f51703940c0c0c010701882ca8802c1d208486400f00200205003900e0245d0000700000c1905050034440550004981d031080e2021307401d032010800c00401c25030b51089c80c074000c1d5015070010b00014003032194002d44010800b070040e08005185000d5116200c4c11502078020000040d044d0300380031041c221084482c0e03610150740c24401203030203080d11042d4641d540a40600d2203407200401098442c401000388800c640d0300100119603821582c020315000380380c2107200c1c40c50314400c20000501203140d4a02c91201010070b40c80f0380e0165070b80024618440c0d0004100b10943e00d4408408404236200b00040b40191440001c005000d1341400300700001e003000c507805a0381e43c200600080c0110050206190701721391040c00c02c0c0d500c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 397700620 1250 397699370 397699381
    0x2603070f110c042f072a0e09100e07030f1407270b09130f02060f0a09050f06040f0b0d020415120b041a0f06040801020301150f050310050603 62
    0x41071002d08406901c02e08051a854003d03694060103440304400c0029042d2040c210b03840400280110000944600d2102144607880c4102014009051400b103000c0380103a61244c14480100c0c0003610483d41551100c0100c0d0015030b260710858241048110060002c0d82c0303940c0c3c0340007000c420444020a20348030062881444001080001d010b0860020b080c001d0340e9200c82c000c1444030500c00d41c44200390810704040e81c00e0501c0394016009190302d610070300e4420400d8a0300d51048010b000d04a03001682084810035580c071305801b410346420715940340707071b0031600e00010000b1102006c07209902c00c140c00c03c4100104441d154422080342d0020f8099504d42072a240f1003c02070085030b20000c880e5011020f015030b01a070040e480d0303001d1602e035041045800e0b80c06003071004803441e0324140c40c0540e0b0086521855403a142419200c0300c41c00408040c6802c0d1503170b860500f640c1003a40500c3c5000030388245c603d1802d810906040800f9054544170b401d618140e099504e80c40010300c5258000c003070000200b01d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 397701870 1250 397700620 397700623
    0x103050a0606050a152102030405160501140910140a02030705061f15050f1207081005031b040f09050f070e0c030f0c0c0d0905130506030705061c092603070f11 70
    0xd4205071b5034981151245414144192601d00c45000140c810001d01c101066035806440003020485020600c54200280e0302c0c18811440010078290041c0050481c810401d1480c0c900100740b4201103901558586451f461b04600d0020090803840400f60707883c5070f00c07003450140705d00001140d28150101c42030f46401c0000740c809207d603048071910300500050f29408000c0880b00180a0710182c0c0d03a0311170301d5454051090510b00103002e0194190088030003482d112414017514400300400800000f101894014010216695020300f20354580102d403509120110038010080100703182c42004a00b40b520b8200c115045c40001c3c4402180c01d50030300802c40c40312a032416101011289411190541c14410025040c0c0095104e4540b044a50a850140307401a50203405c2c003c8401900501c0442d0500c0f003006065040501d401200508160202060b00708a014407a04d080c0181c1c0c07114140300c40d490304140061400356203c400c6041c10014000c0d05944108801142507083c40c0000c0000320120129 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 397703120 1250 397701870 397701917
    0x90a021011030706330b0306030705040f0b01030c080906040f030c060e0c040b06120f1b04090c021e0604021915051b0604030203070602090a0306050103050a0606050a15 74
    0x120341910012804200700b010300c2e844004c0c0d008412040e40b0404070030705030940760314512009500d0b4149898004201b10f00b00301000c1e540018004083d60030168944000c101143d10840746442141d448420059683d601440381d40b0807066035140c0140585400420150342e082c0280000b015910f00704205000d25102d0a0b07007180c00c0303501110501110103401e48440e50380700c001402134815440c2942c035000324606041141c0919012040c07484141d6588210441c1042c03009001d0000c4092649205004600401c01403002e400c4a503400103221411a5009103400c800d0400313541c0e1300400b00c40106210200107961a070060781107981c81c0d550030703a2002185448903d1760000d0110410340488940e00d0750490040d15a01d0803041042103045149084035030f4840d0151405000358004002803804103110b0b4004085201024005069140e969030742c20084038000da00070f903142c0d00485208070030008503002e814010b00c02160608074081c01e260480074070039226447d00040c081e03e5481c40040800c001350a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 397704370 1250 397703120 397703147
    0x1170102040e04050607030e0316080921060703060e0c03060607060b0a08010c0e0901150807140a0314060f2107050907200102040803040b0d09050610080f06090a0210 73
    0x34025505013807404076034842c0103960402c00b090500401140b00320000041d42c2240d0250109140c95a9142c0c4a601e8150300c00c0f049580c10180d142c07008006181c4c1a10140e14490144005040340c7c9841c180050441d201074200d0461a0207010500844090040a80e03401103011140c0039620045440e040d0300401600e0310254014040b100c0015080e40190f00000120f0815242e08000301194010000c0c1003000340203201d0703201c2c42d0000c81c820040c40f0f0310001e984004a07041c030420481d610024a43c41743c02030300a42001a032600c240d01601581304000c160001d00607522420328840007000510807021500c1c01105454041b40c4400503071108101d40b00007800090b00000380781c1803000b0000c000d41072200350403612140706007000a144405101322002c80e601c11001c3c0d42070600b0b2038401100c0e98082c551034071f00940c441e681c0b400481d40c01e01c40c0310f014000e0b04641e5890580740241107410101041d29950198104c4c0040015000d000701e030213600f5590443c4c41004202c0360031020744e2544080d841 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 397705620 1250 397704370 397704389
    0x4060308030a1a0a060e010504030f0b01150c020117070c02120f0c09040b0402090703060305030307200d14070c080703030203270f04050c09040213030c0e0403080117010204 76
    0x500c00d521000354064800400c003845080c2c3d1000466415050030070390f55400903035150342088454801c429042d80c3c1001450070070703c0c10303a0741e480d015800e1407078801c00d4030000044001042850f1040c41211814903070f9040c4048981c0342d680000e003110480c12084c107040c4d04002c0000f0440d40c1705001a00c2001d45c0100310484520426183d1540c40d11841e00c01503403072280003c001810301d040100b40d440395034007040b5818155141d038240018020054901e0b01810b840d40404800650300f0300207903114802d2a6034090008481e100c130080f6a10220504106941212107200401b60340b00543c0c0441c00340c0c1040540c1d60700ca8510b00030841d08190361104c00e090048510103c101a4040014540710b016280c900c03c01c0740c04051401602c0c1c400d000125442118000c22464504190b00712aa020003000c4a450030220b45001049c05e0342d02030501a94200020f03103052007000303000199240a401d070582e000b0720b18641540c2c09001c02506000e0803600e0007011504204a8000350101c60260003c0c11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 397706870 1250 397705620 397705631
    0x12121a1f030e1006150e060f0d11180117070905090402150c2a0d0b060321040609080705060f1602060d0e150403050307030221040b0f130c030602090f04 67
    0x1031004010501405061072526081e10174034901c03071141c640000322510042c81c00d480c0407904548a882c50340106400c0e490262140e0700c419803000d0510107000d010342d01104101110200400051840a451841d002c507000310740c003401400795001f0300e03103015207005480e03080c0c0b40e40701e50000480309241b003c11410201c000190580e001030005c00c04500000080b01204030b410145000c81182c000c0034640035400540d02c42013580410795180400e07800c41b4000e405d80c0d1400c81000300e44006030b804034010780101e00002400300300055016210600515030a00540000da00344000911544104110300306031030000f10744034158242595110183c203500605156841c8000b12188000d4405180d0b4001d150041a803100350f110040c2c8840c074030456041d0344a51855540c4a02034000b504a88400c3d40340d0392100e184840c00070b42c0050f1072405030740079220300310862034203401300c1c4c140e107000034070444501181c8217841c000030712040480415640c0c03008002d81c407824a24089400c0320030709442c05a20a0415 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 397708120 1250 397706870 397706893
    0x4050715050f040611190203030a0f0309020d030917060411100215010f03120203090f041505040e1c0f020a020409030311070f05071d0103080304080712121a1f030e 72
    0x5c40710342c4180b41e020094070048412240d440d04031510850010350103030003c20074a80840d10454840180580d83d04000032076505231703004030f880f9403540d20003103001c189011350602c621045900302411107072124000340040d03e415941c1d1803a01103000050b5001d241e03510444240399000b444203101140c10115905800e41e074444800281d03400901c403d0710481e960509441e9443d1000c0b084804480024005402a401035010310000f0b1070091090300c480705040c8804a1955964003a400c10402075400901c0e0340026880e5000c02d0491240d01c0c001402914203c0050450700070440b0556540c040340c0000c1c440e02c06003000d6000d444d18421929407803070000381800c01c100c01541c800e541207008400700c80c4103503110405104c48403c0b014800709028000701c01040020b0850340110b070f00610840c3d51b14280b01156503490341d4004100c0b041d20200e0030401d00442c211000d40b14400c07021003181c007907411000400011078610034100c11803d0410710389601c800b00450080e00504400494401240c0818a16 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 397709370 1250 397708120 397708127
    0x60d021801030b13050d0815120c04051e01090e10050412081b0d110d020406121109060703030905011b05040f0f05060909040f20030f0604050715050f0406 68
    0xd0004440c03989040c0c0101d0740c0b2078813540072007036016802070040410800da0035082c1d8184400501078540c40300100c5161045458010803549030302c88110003010081d0300f046c200415200c0080c038141c041401903000111410f22121901e044400362500014584503507160b180c10003406040c1010143d05043c240001c212481ea40f820300c00036195203c0660b601c500c407010310704440220400d4019a0107100d01c00c40ea801503402451500040b1039800e1a1040001001e01030340c12652242010990b11461940b140c1d0990050310070018007106000e141240381c000145042c003070603501404142c1d8400c800e4040000940c0f2640505a10090048040101d514018140d52113409015005c0c02c0c4000d0000b0a03004002151007640c50042019042090a5007485507a41c402041507549081031049000461500440192078000c0402d05115200150041c1072074842849011115540000100408a0000315580c0706403210707000301d010340b101c44900480f1180200410024241700004001466a80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 397710620 1250 397709370 397709419
    0x4081b0306060913062d0b09150303040f08010506180907061103120115110109050d050c121603030605100c020f03010b040e010903020705180103060c031d070801050109090f020603060d02 82
    0x5071b141c08035040f0700061002c042a600c150000541180b41680031401807120391600c0020004098100c0b03041658481003071200510b5030f0f0250380c0b00d035960b0302407041609082210301c43c13100d00404075a0700f0f400c10700881e42d507540c0141f2610f010000340b08150f0700400360500480d21141641d0248499658441e00513070320b154200b00000012030001c4c002d4903d400c906000302842250408098101c0003c1260f099441d42c0c001e64103c040740c001c18166000c1250800003901c40030036010b809403c0031440e403074084c08403075164000f070744a8841c81003119200c0ba4001e40c0d44d508240c1c141d40d0f81c07002118240100c1d014280240070303075a100741000c590703240f8070f10154060510140a071b0708460103d075540c1c0502c026608407494017201d080840d0014804980c4c3d40d0030038401c1814500e40041e0b2110440200b050f00080800051540c0d003108101b001584800d009050142c581244200100055039031852855810751400034044d80010001810350366440c0303015889103070040c012a045414414603140d5109 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 397711870 1250 397710620 397710671
    0x402041e0b1c03080402060706090b0103050a1205041815090c080603011d0d0e0d0b010803070c05010212040512030d060f09270f0c03051204081b030606091306 70
    0x82c0b9118403207074035910b0000b1030310340c442e015102c0e1529034035550203000c2c0b00c0d40044001d4400503119070b640d50001c1d5520403036a009501a50190050380c069241210f000d02d510040d0f0002c02000348014022081c2d81096190b031a0800000061054100c203d0310880390410b911a1071001c0c5011f080d0061560403d6000380308600c1140200600090f041d107100c03283c3c1c61881c443c0e000350701c079400c14405180907600c50102e2000c0104404001e801c15900c1e103125110036005500941c0011400c2c0f02044030a00c014070203041c1c01d0020f0310114801e42c3c5407080c40d01035446030500c500d03000507140f90f2408051040301da81d13460408042c000303291102495100a180c501c1021951881e086100940c00c1020b01b4080101414099480e4404616241e100701d041e0b45074808d031000c2c0d841010000001c0d1040100190744180103105640b5030f454042201d0412000d981100c0c020704030303045131020a58001c0351942d0b2010044900380d0140d01c1e00041280864915800242740f20720b002e849010301c682642c01070f442c07013 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 397713120 1250 397711870 397711879
    0x1303170c010f090b06270703020a0e030606010e010c06021303050703050f011e0c3b0a180507050c030c0703110105090a0506030a0905030409051e040b0606030402041e0b 74
    0x40d0b0b48014680407205403860240c039014850005c01c045d80b800300074030006044507144e203400a0f46c07001c1c080c880c0580142e40040c046513000414074170041d041982d800b102c9a0803000742510b4a0040c3c0042d110500c550078032410010106444801c000180d4103403601c54030b81d0021064078640741e02e003240d0f585031903010503a581d1080707501d8003000590500540362190720032003256000882d4846407001402c02410b0b0079041c4071210b00079224451810b091001c404248020400c0c540400301c40c0c00d400c100581c440035018080301d01081c822410305051819030542500d800044c0d55982440860300c070700a07032030f404085000003d1210b0f07500341d0008030300381500d0084000080b408600401035503580306440a01d80c201800050400040c40c290f009558000e0201da804038102a0650780d180c20f42e0302a8100c044002e03600c0ac00d010307060054120040c114000005480e0311030030541c445191105000302030302c2c03090400200103011922150050b800e10340c4411203044c684040c0c825105d008c2d000502456000703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 397714370 1250 397713120 397713131
    0x102190b01080f060112030f03090210180f0b0f13050603012309061f023a0201090f0b060609060414040e03180103110c0609071809030f051303170c01 66
    0x401c100864201d040b01c2106c0c3d8001c01005d01550191400801d180c410380901d5038a101076009601c1d03400f0b09060f460000d80d03035522a10310088c0d0801c3e10850b140c0014440395112002070107c03146000442e65000c001801c26a2560380360090a42c040049401c543d030000004000003622220ba1452428030f05028a1054201000c1000380000c012007141e0041d80101d407500700038030403c0c0550300d41d48404881c2c03058604114251111301400c46103c2c080e010081d080541c5202000703021660310303114803074030710091020160b29103861005280783c03980504401044400302e44150b882400f11200c15401038895078581359244c500b44c1200030381e080340c1401107041c240782c1da10405003c03080f02c0e080755031503003050401900440110001d120b180104208028204901c030f00c4101c040041c43d120703010a10090072014100035a611802505103807801c0304a08242007140006c0d000000c03c1174070240c5190140d10341403010309194480440d035001400565161050030a01400c0b840100003203840203001380716 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 397715620 1250 397714370 397714393
    0x2030304061815050a110115080a02010210150b030a3803060105130c02010603140c1306050306190b09041119031203180512040f05030606010215060102190b0108 71
    0xb0f00482c400c0d140000140304106480b086070040c0d0410403e0b1500800000b00b0755100a104d54000200790021422681701c14401e0f0210360341001f005d20344075000c00c01805011240c0a02d074a080d061801880600d035004000942c07001c440740e0080d080706a030604a2000e100b50b056010f00000310307840d428082894401881e2156040008801c3d040b688042e01c40148800e941d80c13400000c1903c8000e500441d502c17564000081040c5010140d45008514050210703030002104001c0700e030f204c01041601d140d0a00c142042923a40114250b40d100c0b146003007200012892800030001060702c80c0120340e00594a1040c00140403d0020840d9021000d036803203460019003005401c4204000d1000800d446181104106101d101e0382151407904800015180c030188141d1366141001d415201242040b03070b0101c1d0400116511002d4140100800c0d005400300d8200440001e4a415103081c0320b1003e40750b444045000c1d44d1003009030400c00050035a981e0001e120602c0c000188000a10410503584a194107000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 397716870 1250 397715620 397715639
    0x7030230100e0403360305030a0f09060512130605040c050907030b0307172103060301110c0a03200d0801050906040c021f060b0c101b090501050306030a020303040618 73
    0x1402160151a4400d0350178200c103036100d01820283d81c6400b05c0072454a04825642402c0001016611450265444000303100004059076a640400020001031490800c41e1980280403507201c500c10700103030f503e1a03444605404e086500c40000801480c500810402804803040c0c2c0c000c180c440885890000b40c444882c00c4040e10f0854410782d5040d0000041088030105807404403410a510009540750040340c4800092841c240102d44040f54400000f045950700e801c4c400c0a0610192001160620042c90801a91440d450a000f41440f800c8010012011805100c903000e060f100c500729203c110b16100300410003007080c4a41405000003001007181c0c3d00c1e2501460386c1c40d049940c010103020001c0d940c60303803540b1180710a0b400c400f9a200c85c08101c080b400301c004c000c0544810f0082000b481c621012030212000501d056100b0b1254040200803107600842110880f40246080c03038481e155140043e0500e4140c0750025810701c0001000102550480e1007070248000780b00400e0005a600c00140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 397718120 1250 397716870 397716899
    0x9190b04060501170907030212070603050615030106030b12070618330c050d0e010f03090507061101060b0706150b280e030d0210060b09090703023010 66
    0x1e0201300801c40b80550101d01190880e845440b4000f00d6012595039004110414804c00290f2401e0308401c0d0140441909030042c0b0b42c010405650401e80146c444c4400c000f43d01040c00784e40201078480c0200c13100d07540c58001e64100da01c03407001070b1504155a80c0001c0d042d04401c060740343c0c50b41103132a40000d02c04241c40e0341d06621a07580e040c44240c01d041d5001103001001c280105028040390340410380200c0c0d000c108004180341c254691b40c3c0ca01c1c0030343c4005420500ca604e000401c142c00c0280a00005601080c7c0c041100e0050800504098485d15118090000b5400061002401007400303803e024440e0844003070b82d082480042c4841d0f88400d040400d910403c000b000410f04942828030001c100c1400c01103541c4d11510305411000740d00070000c0c2c200684190f40500513441000341039540d40b804c1c4241c03001010309803409440c1c46140e0011600c42c100c018120414154080b452b910990142801e401d119031900d00101481f1341152400080308074146c601d060b02041e03461000c60240940c0c04107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 397719370 1250 397718120 397718129
    0xc08010f141b070c09050c0318031812100908090a05010525030306120506150a08070e0a09081621080a0b0406050d2a1505070503040509190b0406 64
    0x3402d903009074001164481e0341c070203c070032120600e4444000800d01640c1c40394500903c00304221950b0b030308040110300c4a030304c2d00d007603c030070301c1d070001c0003010603c0f03545a0721703401e00340001d99001046030f1183c0d0040341000420f030b94036980c2a00307040d07d0000700305200c40106881c1c21b003141d52008030394464004440f035003d0380b807400110f413085500602d48820f025802030300282c828a000300e4069208c140f0500c84011849040311103910100900150800c3e103524047c4240e0182c0322681ea09203030201960f03030b4110900c14060300c596004040b0300b401c10305800c003c015136001840c2c56900d43c6500600a0114515241500e91480c0d02001800540907007148111185256994081d02d4403113040c100014080e605c5225441b654490b000101510384902142e425070144180e007140031940d06249410508010817000f026100980130b000b15284007000c4814080180391940d207901d490b00d0000c1c078502c00d40d00181d6200c0642010024a4400c6542168403291801001c1c4107400205c014001503403200d014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 397720620 1250 397719370 397719391
    0x61804060b030f0a0b030307120203030406110f0703230a170f041a090c1507020f090609040b0a0923010e010c020309220603061506020c010e0603090a0c08010f14 71
    0x100703244d0100e9402200700e200d03008050f41d1801c107503940c0c2c00b4211501c0841d0007015800100c2080207004d90b034030030035101f0703800404200d1401d0f050b0a000c03171451103051001801d02000000701c0030080214042c6e540c41c03030b0640101075681d0300c090310040c14408140b0070440c1d1801351000050700c02c00380c44010310300865000c055001d070700c21071503207942070200c2c01024002148144011410266210b62614178a2200d0250066440006006220068000d100103900550000013405056140c01d6580e90340250494106103031341d15280e26000c0a80510352000d4243c0b21010b50b0a030759081030b002c03000c480810400081045100d00101c45003603c002c200c070640542c1003030200000c24140f0400300000a00c0b10a080c0d0404010426128100c400d9a0802c1d240716070b89078660905185092284006409507000915500c1d81100000b01400a0840a18060132010000c688489005c004485050798462900c0c0e44a50f101c0c40c25a00030034000c1004c10b42c503424420300750003c0044c0720107903004501444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 397721870 1250 397720620 397720651
    0x12080304060b030f070f090605120705040c0c060f14070c0c0302090a0e03040b18060f0406030b0a0e1e01050f0a3c0e0a0506220b061804060b03 63
    0x11a600700500c0d850403940c0e01401001d0900b880004144440c81c058101030760791010a0b41132020a03000c980980d002107001c1c2942c00d4643c642c55000141020481c2c02c21200850503504241041300d203501132000081055042801488100c04907030441080c080c2d22115000090361344e02c10441d04003001c0d600c05480e40d01054030920246c00d0004142e5031180c41d9480109070306012618192650b07000e0f600c40554010040350642251650091a6004540440b00903080c00708100c820b10b080c0c4035a1040c481890341d40c40c0081c006032161040c420090080f8800d950084c0b030911070003001000d6030354034044211403c8002194030301c0c10303191160031804090142c04410341010f210031070468072040000340c09520300c5813800403943d18440e6009004612247c40c07448618140c07100d4885c58014040c404914203040820405031101b4002c00c40b107003158003200c0d041104421883e0000c0200481584c0c00c44070020340e451030414511100c018aa006035400c11125540d10329889035030105482485400b6600b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 397723120 1250 397721870 397721873
    0x402090414010b10020c03120307080a0b01030b04020a0305100e0709060c230d0f1d06071103010f060f170c121603030c05060f0402011b030909050103061512080304 72
    0x2845514001c0c81d0340000241e0007100c0001403404204030f50064010381c040082e48145090034400d07e085014500c6150b8198101342740080c007400c50061070400e1250ba5404204000da00c40d82024000b004003400465171407041034801000f61408484e050000007044034001096215108024482c0140340d481d42001402e090b01118242c281c0001913404040944580f0302e0300b96403171001042c04e00e0800040000c1829600c0181c0b40d0f00c400400c640a011101c05905000d012aa00d900404001299517a59400603450044601c015503030714180c142d1b01c0c00391032401e4640d0f02ea121304207440412003d0a548c959510300d040c1d145641c20b10000319a00140740b4003c1c1800d0030036140d100b0420000503270b80c3e40d03244403d0b030142030031059200780d00159001c5500c01c1441418040960010420b510100140c5401d0300040c1000b00c00803964403d448800c113031241414850352881c00540320440040c41296501d0405002070484078408c1200007042600c001030258810203400c5405a01084443c250350b80ea = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 397724370 1250 397723120 397723133
    0x60307030503041e0b030f06030f07150f02100609020a02010624050702060403140a0201170412180e1003020405160c020603060402041d0103140703020904141f02040303080f04020904 80
    0x11355032010110a4600d40119078441c0d4400030f144640c810031600c49480c5851000c162070089088010500794025401c2481455902c041c01006145281841c80c47c19048120403440c00c0c2141800d1803101745001c00110b9207a0107900207002c0703516141e0080c04003d403215034004200ea038111000146e61354144e441d40032030380510301520381d5a00041060f8101652500c4100b4502d081c2d41440318180c21000b440404c544e0041d402d10311600342450140038074036003561981d00c0c4000811b9480c0500031080341080b80c440c10b50020710050081d02e441140c060902c820001006161030000324440c6090000080e0610070102c03c4400d01e081c3d50b66850a203644036000d009030b59001074225134200780c00300b0004c1510070300b0300080301d80d200c1036a590b40a95850f60500300c440181c0342c040d10007290001c040400242c0e551404007600a038000c1c1181d020319101450041c42c0000c1d0060f842c808043e91041c0c2007000a007036000d80100c030b01070b40f0380c244580d40b0340011444111080710000d42c000341420100e40810031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 397725620 1250 397724370 397724399
    0xa0c0504270f050609060a0f0204033212070606080312180106090c0815090112140a1202030703020c0114070b062b0212010e0703020d0f021503060906030703050304 72
    0x14209042c42024585540d802c01c0c1d800c0354a8816070b1b0000b010320180c19124440e004018501080848c2001c0c15a0740d0040d0410107034011072851324014070790045801d000076800c0381c1c0140f101c00b2107000e003034021682c4a003a04040c3d03090b1030345864002c0002c1c0300f00011003100c0d000360800307c04d5003050303a032074400308554050700c0042915596511008100107299100d001c03202030b9151034140306032400d2000b5915091030440c049004140d008010031081c83d8400f003402c805640705a441c10710b1008812400d00e010071441014103101100108801c005030003200410601c0e000742e0a8540c4a0490401910480f001549084100c0303820454032011600c45182d0a420030002030590071041c5103006922910b628a00d1424100d02c6030001600c114a0550941042e49062500030701108494106042c1c8a80039444007a02409401e14004100310b2103102c2c0f942104e034014440007881d901034043d04440c1e002101d01d68060201d2801081c007a20b4001416000c80e54800000c5146c0350500f0368182d40d401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 397726870 1250 397725620 397725623
    0x30e040e070b0d0906020a110c042c01020d09030819050103020603011a0d06240801030b13030c0b0406050f060d02090408180a090b01020118350a020a0c050427 70
    0x6a803401c09100003545c0740001d00d1040c1071a80e4a10020403040800c90804c840030308014812031400f60361400701030307915050003119104454811641e0544601c2940a44a01082c03406c800c1d140800384003c040c0c10800b030901502000751131035501c20b07801c98040d00b10b980a000c060340c41300c3c041c001006214034040c5841521480840a6801e041c403600d881002c0d00c51540200c090b00c00300c0140300090346680f05413191280c5191425006a52654841862210010348100e2807560302c2c0d4040c0302414010030180340c130550320580d01111072600e81000001810141d8011203d01c2da0a000b20341c29280060300c1c00a0650010002d90f19900c881e5501000355000c40e0f0244007607071071045c05815640d61420500020301c0f030304030007003515180c8200082c2122031840c8100201c812000d82d01e0040303064800d100d1064680c40c030301d103050406008504981d900300c00341240c07100c9200007208a8015804522102881e01c9110040c41c1c0030f0f126010402910a072001041070141241102c2da10440000025613041c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 397728120 1250 397726870 397726897
    0x6030a060905070e032e02091c0305120106170f040203011508010203010801060e10091109040e010f110313020108060f030703080301230d08090a050418030e040e070b 73
    0xa03030358001d080c00d40d842154841c001c03802045011007281420b0090303041d816451015912000c0b011001d0303803c4004024840702c4100c0d401f1400400c99291a1115029400c0c440f02c3c8254102c80341c07800030703c00d80c04005a02c00d4a8109000000d84902801007102c683c1507804008100daa26051414003201c00103205a86c150b40307507070200d002064000b13070b03400103031800c0c0001503030703e60404800310709650059008207030f580c1140c820044890245010681500c44004011501c0702c00365805e01c0e100d014140c0c0081e4013500e0700c4024a00f0510540c00306501328180c610a010074100c1c414045c0c1c140c003080321805050300000c118040150300c121400f44d88008000c03c207a01040002001c42d05e00901c41d001202e600390000018403054500d098881c80450751600b444c1034240302080170078402d15100400130314101001c16078003483d660303250144024100c054003c014240000b50328038814147c1f04415004200140c03041041d40c10140129034403c815007006100745413070500b000215500880507000710 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 397729370 1250 397728120 397728131
    0x80c090703181e03110703230f060c09090702060c0405041503051e1603120e060c010912030f1514060d06080c011e0206010e070309020a1806051207030206030a 70
    0x1a0100040b4002000f00c45240d1650764450b24014018040b450305081e403a906c04c078010000039151340c4503029a5440159802c45902c0070a010134035000340c4004034044c90050000708480e00b130140d40580108801201e4502698841200a0340c4512042c0c5144500c113100700801c1c40a410b01d50070485c141d1000907043c0686135625240c540c18400c3c100f1000030408068402d42c086010100701920441131140040501d05280d9694004030b4800c1420500611027070391102030942c0d45540559030391a04800017444624007601d0f140c00c0307001c82c009031100070901e05006207207050b4541c40b8460940d005c08042035401030621b00d90b030001001610030541c0c0030350304202c22013130500e20b400703000002c2560b440140302e02c6c08002c00150080b041107078561891355018043c0f4048070b0307000031068112004114030049603210400100d01a000d2000082e4101d0940400010118079034000a81c0c02c40c1006020481542c44004124003080d0314081c2c482c0303a60003102c0510141c9802c400035504105000c1c0001031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 397730620 1250 397729370 397729373
    0x171501080106030b03070e100e24090a090503070b0117011e050405030f0409091518060b0f03070806061f020a03210c0206040201123309020f03040309080c09070318 72
    0x15541120001100e0b0381d980e0301004480f0300ca04008d60030106060360306c030590011080301c10075100c04416441c071844110300803533844042d681c040820645c000003604d50301c0c03c00381007848018100b0311a05180710a80d074040f44141c8410300c40d5a035120742c03d50007065203801020f06100984401781040d61240410000c0d00768100e11180204002e01401ca80820004c0090034245440480030401070091b5003001c103901080c0035141505030549038084000910085490f002c034184044080099070144680c0c513002c00c00540014006200b000c0c11134440b102c2882448035100306130301c0c00001d800980c0c0400d84060004e40544800355854241c0c0c00d0102d0b4006603102a00b0944040421080c00b68214109010540d40c1c00001602c85d49406641030190480c1c002c0204058402e903c0c08405800c00c0c2e06000c100361140b80348083c01040790110641d201d04450710b13520003640c810b59046000c5501480c002402080c08035049100140c0241185c03070075654841d0a0700580f5600100e1019030040c07005440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 397731870 1250 397730620 397730639
    0x1608120d02071719030b010201110403020603070207051011070b0f0a110322140a050f2e03050906010f2301050903101d030301150f090305010507171501080106030b0307 74
    0x41031030026001c00d14544e00d81c9020301143c086001180c11a41885503043c08079001c10700311003c50354159a195078a40d41e158040782003036515084070354801800c41031036a245a03c0300c10014044041420303112416a54010882d49100d00480b08510381d2042c0300304115a0b000d00405604040094140d030310341102070000c401c524a05c0624060310200400003070081355200300d4001c0e1039603410fa51500030142030a0000d100410107034901403044a41c0300c4074540c0c55500d5090f45805039403914035416420094500074001c0c0000700c554403614800e0400003d507a0b2581a112001c95408455202d08500c040311184500b10f0302030302c0c0f9030500c40100203c82a98030108280c811244820340002060780751070410700c02e2900d1140d40c41e60300f6881032006104040c60b110107480f0680e044e050400f49441e1400c0243c0304c0720029440541194070300400c004469800401d42c000804582441d440c040d0f03a040c0c01103158044000400d40002e001c0001401124005c0d8840e40e08440001e040ba4416590b035040b08 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 397733120 1250 397731870 397731877
    0x20d0f0303091707020a0b0d0204050a0308041d0408030601081302130b0a05120613030e060a02010606140426011e091104061215060e0106021608120d020717 69
    0x3140041e41e03070b2070390390300344071104010980b0000414080b52901c0095000190300c80042c0c000e01040c50310000d594001840d8580c100d0380107040c0070f801d142241d03a0703a0a0145058005214140500c0040031314010034485100255105660004205007107407190001154299001400364618510ba002040056924038504a0400c084100c01007020001c44050003440310039641f0640c0591079482c840001520042901644180c0d034005181e074035085030408540010b000c1010303980040001550b452100d6064102001380e036660703111885035400201c0c80010900c12841900511215807a060804d1765244080820003c0b80c00c00101300d00d00028240c2d204280078804048010341d9860780c0508010101c0c03090200b02c941118100002482c100d00d20001c00340b190001003040c1c050b40400c11007424158450409071143e007549100c55a190b4102956130002c0041000d5450306803100007078840400120503c2c00c2d8100c00b41c60341488218844031000c0e4100d030b001100e10046400e16032203030b0070090001c4c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 397734370 1250 397733120 397733123
    0x310060b070f3002011109031b041104031a0c041a0306010c120309050c040c0807050d020c0102030f040b18102c0c09010602030408060705090d0b0f090106050307081207020d0f 77
    0x15581c2e010003c120183c21a400d80301d0b41507601005000022a590340468952108680c01d02e259440694410000c0c3c010284201e043e444160003240200c00e00c030080d805d0048201c03507000750322000d40b58810031940e580943e10174a130800b640780088880c83c98410010356041201810102d0141d9081c1c1e94000010100b04c12850009076999619002d00400b0803190094000a1380d08101581d44085c00903c03a03034005108405015001030a03813542d204030340c1100c201d1032a200003151281455803181c0170614003600d00740c8620340303441c02041c401c800c5e0620384841001e46400900001d89544600380180410a1610034000902c0b070098443c407840c0c03001d500590241c8005040d0704100901009005103040e04088115030040c402802450000030700941c100741c0354105281c407140c0b804001100741c401c021008060844c1070341401440b94164090700c0c026a2100d00902c80c01c0c2d102d01c1071507034401c072600c200e5610307900c007010300c0d50000d4a403001026514005001c2d00d030116040d07150b242e03c04c4044d160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 397735620 1250 397734370 397734443
    0x3050a02010c020616080c010c0809030d1d0304140906040209030616030f11030103051e070e190c030c0f1b0204090515040f0201030516050306040509100e0c0310060b070f 75
    0x5200441c00409c0c41003e25031021418080110704180a005680c2e0080c181440c600030390302c503036208110079000030288840300c609c3e003240e42e41c90311401e034281d4050302d000900e40a00070502c0803e10b0f0b4600382c001e1701c096803801790080074103541d9070380d4218904070600c01c1501416510b02000003202058042e2034015086100025580e514624241e40b410b9407101000710009400ca0460120440c041200e03004c456544020741040e840b400c00380c000d500301c3e081c0410340591401c0d022460031500350b0081040301d40c0545444000d031001020544046002c030300081000011500c200d401450160300c070654041c080c8048a1208908a50305060910141c40507074a56a841c07148804660385400f4156019010540101c00d103d08503102a10300e0001402d020310650302d542c0010820355080180428503400130401f030040d000c00030b141d47d8643c0c441c40d200c02d0083c028030f88000c3c4400c07524022a0b040720350f00b001091034281d4503116140c488034030070343c115a45040c50340400d0080092040a80001c0304cd000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 397736870 1250 397735620 397735627
    0x150b040207080c0706030603020d060504080f04150e040c0912080c060408070b0a0903120533010917060103020d03140a080a0e010c0f0f170903120705030103050a02010c02061608 78
    0xc805184c00740d00d9028038105410100b0501c0180c940390308030101c4a0344100041010340300e81ca001c010a00502416481c04c00d00410300040480082c40c40c00c4000b07805868440112040c80d0900c0244c45046000001050303c01004201d6084a681c0e01c071600c600602c4002e0910001d401200d040c404182d60a035613590010030090280310b22081c54075007110460804125400709030350301034030380014461011007041e0745800140018030402c0c454100b0b10700001c143c085012801001c00d0029140021050018103000d1000c2800e09425044640502caa10001c19680e841c3d13600b0801510000d101c2142001080e00c2801c54040d1414054880045180c580300c0c91407030020800821690300c19030b03100d1540e0411517071008664020301c005103e0507031880c003900d200c60b403030405a40b03000c00c071002c0343c01100c480c40820180d0500400944646800c200854407170f500d60340340c1121580400c4c0000340c081e8014042143c01503001d01d400f503001510103403a160400d000e10001e03022040c107446082e1152032000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 397738120 1250 397736870 397736887
    0x3050307090b070b0403050f09040501060201020c0c0301060819240b040e0c0906010503130b0a020702090f010e010b0d0e0a05010b1302040b03010915150534150b04020708 75
    0x724001c05040d506564508000b0701c0d442e001c2805a02034009400c0c410000f485112480039007046400015018200340084d582d0307494024000c1d8443c00c0000110b014542855080c0d10b41801403c04031400b850042c600d080c0091a030100501c5002c5d42107036405580004401d40761010700e881004089101070000300148000207000503910b6050f800000c6400c15900380782e150351184403c0e90070010a1074410b0f1682d4422101c19011061490043c010720081010000110030f590001c11500d8401d07101d6486e03d84901c1000d0b020006c007070144bd80109100d0005024048400e409444082c00d00d110100381d40583d0300c14282000c11000c0140c40300e945402e0b1510460a2034075600c002004689011454189002503d280300d000601603039502944a0452288881d41d01040350094860304846040c10401340e0300c060240e5115a6a00c1a601224039030a0303056642e1142a1440300011095500c00000950700c8404c843d0741048001e9249540b041d0981c480e44881c03000c0d1034481d1060750225520302c0d55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 397739370 1250 397738120 397738127
    0xa030f12020c0607080703060b04080a060b0a0e010b090a030210231920030a0809010b1c0b06030f160905090303150907020a0204020f12060405270c04060303050307 72
    0x1040c103030040d0140100010408007000150280e03002d1920b140283c100d48442030f0032000b0700102e034806014244049004107a04901041d4098014802d0100708541d071450824040301280602c203105040b46a030300100a104040f200801c21003074002c050340c0040f92a0390003d00f1402200c0e20a500040c0c60401181d400d46500c14900410301a5002d16804e00581c917a4100030444c4404980b42006000380f510000c07030b03a1450f403110001906805803038407081030070350051850004581d00104d544c200181b0399114104004006406121003a5220000c261070312076000c1903602810882e0148258120000c03011800e10541754800d00d9003000c9074140d4940b0a12405071031002d0440545a04100148420403004500e031500a05007540c5008080d56140016428401c0190b40031b50058000691600f81038038100081a28210011000c269911030f04184411500221910540301409182c400800b860800e480e07110300d103201086a801c10740d010045030603034909078030440c0490f00210520115540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 397740620 1250 397739370 397739387
    0x17150d060618050103110d02150408030a1404050f1e150a02071a041e090e0703060c020a1104020f0f0c070e010509280b030d091e03020d0b070309050a030f 68
    0x10302e058203002c694159116043c3d48000c82000f20f124240c1c0e51000811500c1c6c10b001b6001c111600c4010380d45655440b11610b899505c40345d0b916000a9400c9030801c3c2140000007510295403002d00700b54010800c01c4148007031070b4000540c035003000d01d024041c1903d95551040c46030540001540407503d80e030107403c01034544000c0b40c020310300c210081c4d0007910a5040900c165012210083c00c84101c071050f03456030310b80c807901c030f5041940002d04003240c0510180001400104607846034008110039640c8800032611003c10110040619025050300207180c076064016005007031000100610305208483d44140d0396000280150980e04040c9041001d07035441012a0300404c4159080041c0b80760003829550001150b444864404020b80c2c0300703c803d0f050170317030103120350f0350b40038080340c0d14482035190241c98100f4138030640f090100064a2070207001840300b42c100c00c0381e60281404035050b5035039452180c01c81000302180c0030107603102700ca280458010885001e40500a84440c5059043c4400c01800f009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 397741870 1250 397740620 397740659
    0x60a0903061125020a08160305100e1b060405030a060b03012007030503130c0308030f01060311090f040f0908030f01061b06051b03100519050117150d0606 68
    0x2043c0070340701d448440700c5403140b500000b0842d584025000e40c4000340c4d14040c544c0210001d031041a400c0000320345c0101002d0150790217041120290050100044250342d0110f101e40d205030010900c0740710030981e02400d500c4c000c0004151508050b182e0b00482d16002400400303079845612030102010700c4c1401e201d0990702442c100f240d0001a4812681e6158511542500400304071002000401c0c60524010340000303aa07110070100b10b42035403414110656042544c80c0a8200c41c00000024058020311038407100b101d60186003818000500204410030301140360702d40d08262903200b00420f408035031003000c00d21842500100d0b200d0410800c107090500e4142c10a6052150180d0302c1d00742c141a4581030765100780d214401140f03659500c24442c403200c60052680e0045800030040c44540e40144050b10190f62003a103260255008021040c0f1441c1a00e00c600390105940342c41c18080317101814036996100303d84400c03d0000c90b01100c0422001003080200b9a0039555550381407180003c0c82201a5252 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 397743120 1250 397741870 397741901
    0x309142407051209010b040f020a0e09090601061d060c010623090103060522030809010c0e06031503030712050d05060402090a0603020a030f05011d0c0a0f0e0d02060a090306 76
    0x1480c10200190403441503a24400850f20440002500d81c5001d41200050b00400b030018022100319080b650069080210f20f20085450100c07079030b083c0c0c01c02213451881281e036000102180e0746402030544604000140d0829925408101090907031a094010004414542c00000e030503841c00b140710051910f00c014a11b0f4655943c2d040d40d442e0346d6030040300d60540b908000000f40d41c0d2240789801041258488064000c00c5048079104141034001c04d40c18070420800001b4403a00b44400030440f0030706041b641080d4464428404a1f40c0c7e01c4403021315400e400b0b0b000c2d084a203001142e4a54140507421810754200003280047c0c600100078041c0685504084141d80a40c1048000760000303108200f940185802c0542c003081003a40f0901c40d4101c9900041a05e600308050f5840d2203400c054880b050b50280180594030300441c3c0840c00d10030888052412950b01d0011040d84510101c42e0740c0c0c0c0c030400295000c8410400c02001d651000c00804504506489240c005869494184140d4114840c0003504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 397744370 1250 397743120 397743193
    0x6050c1318020405030a14010606020109020915040b060409090302010c0309020d0b0411060f07020406081216030c02090f0f0612030f030c070f240b0d0305070201030914 74
    0x2462100640101540c07803115030006503040301da1101c802400b07154080c0340d00d88a0302c2d2054080c0070355041000e0521041000078841c039515280142e0a84201010094001c43c00500141ca4034038010320103204d419000300003003000c1c5030302d000041c601e4005030004001c0d00c0c1d558440d4010140c09102e800d01ca8486410140403600d01a00050014400744001401d1304001500003130400980c034864000c101d200400003601c96042da0200203c0f80c201600490041e860444c0c0800c0022000070103c41c01480c81d070005280c80d000c480c0b8409210400d0320100c0600c01503903101401a50f8130030300980308141d514415000c6103052924900210720113855540248550014180e01880200440e1141103403d03000c59940d0301d683c82d19281d24420448040c249414500c0c03075070100103208503848810701e12460381700354002e45410f020040b9446480385030390080c949030349100040c0c0204041d0091078014100000e9070710039a10f41e00e050542840c00d80032503400220a412207850401017112400b03040c0c1100115 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 397745620 1250 397744370 397744387
    0x904090515091608150606280201060603060e15061b01021204033b030a020409120f05090a060c081c060807060306030b060405180703030e010905031603140123010306050c 75
    0xa24809030006000d2a00012205841c008140c01c40c205000c023156111510790203030f20000d0007070805020b1000060b00303101c0d00003003101002c101c85015140f1070b14a0a1024110ba080044940c4111720b0010421038402040070001c40c00c2c4007502c100e480c03c41c01c03607403a481c042c500100040301407405805800c0c0c00700c0603401c0f00c100c0220f0030651043c020290300c80f5100b8a0700024034013003000400170f52041c10405c022040142c1c240b1200e00d0303009251110800380c00320708002d0301d03103001c0d581c0442d8202034641c03000c00401e8400d07800c05200030700070200c20b441c00340801d554420541c100d400001d9160703150310041280c2d610803c5008024600c0c4e140400a4a040d40d4500c1000a1b000d413156128079101c00200d50b8204034403503444143c045140486484130340d01e2a000e032481c030b03e0100e00e50101d55400d800040720b040c0071032007054034000b81c100c0300100c605640d107400100020100d49d114640d85ca212040c100c0c02e050042c2d0700510712910843c00a513240d80340503c140c80e8000e001c185d00c48428070070f004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 397746870 1250 397745620 397745653
    0x804031202010c021b01020c120106060207120305070b10120c0501140f0712020c0303130503010c0f02060f070302040f03060b1005070f030c020105120a0507030e120904090515091608 80
    0x1c2c007202085c407400100ca000540101d14001c9064071a5030b11260b04c0d02551100c01e815070201d8200d0304075400703580d4480da540c0c030031a00000c40303c1e401402040c0108450740000342442440355025160740d0620000644034040c0c5c1d01048112001102d4183d40c03480b0900c01980c01040300700c040340200d05050301e4101e094050f4049806144001403004080310061003404e03000340105a000400541280c0d168598007103080240c40252241902951a2100380b0950350b120b60031a040f2500310350010015612a01c1814041c00c000428070f1041560921000c102440c00294050080d8000c141c041100140581004440c902110a140500404100600000e82c1440f0411800ca426003000c1600c04203034001030301c07140700303d4006c103443c0018403003042011045680464001e00701c1d50340801480340d040a4140e0f5550b5183c01d0480540024843d020b01342c94280c01411100303215a0948071a42e4120130a41c95080c6c003030750010050341000e9100300000c8955280c11004055020080614446108120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 397748120 1250 397746870 397746883
    0xf1009020906090405070c060c0c0215130902130915081c0c0b010e0f10030312020d0b0307030320030304030e040e19030f0f05030c250b040804031202010c02 69
    0x5560458012644441c1039840e40c042e0b030410300014000348440d15020000510303032004c0d00001c40b403240c6030000b58540d584c410440713244c1003540034008103e1f03041042c3c0c0720700b4150440c00d20011000c910340c4001c91904000e0015000341d0441d0540e0100741800d10807000c056800d0010142c5260405202c1040000c80c0040c1180c1030f0851800100c456580080040301c0300b004401010700710b1071a035000092072049001d4014803801702c03e0285031aa40326465070300c41c41102444050002104d244c00c02003c103c06038000e0030440107100c400580c000c8204007190804a899000741c0100794035440303440e0204030704409222048540f0740514650b150903070b005086591040f5503e8011030740c1e0850391012800c01c0103003a0410504e0b081d07050307a025040c0b03402011001031031624800500340b21040f002c902d0042007034038014844405020304040c0b141c41d003103940c00c0c42c42180003100c0700c8403a0341c2c801107a1480c8045020714010488130765510700710309080c10300b4070007070b000142107a15042c5a409007690110f0f48 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 397749370 1250 397748120 397748129
    0x141005010c0201021501030b041709030c040e0a050733120b0f0d0606030312020a080c0708120702010b010323070309060b120a0c050f0607030522120b0f10 68
    0x31a03507956103800101d282c69040c0f00d0392042c080741d0f40c00101c140006262039074451032240b071049c4a00d5142d1000854a8092889401e400da40310790803001e50352505821188015905404445010205841d41850000701e907002d801241c04d9803000400500031098450321400003d51000485c5600c240010a046010503a000c1090341e508450791a554031034a80c807042d41c06c01000c001c418840fa003400f800400341c522045000c610345240d005000340301e17802643c3c0b000310300d900d031101540e6500d2580c07001e56200700422500040b00300701504060a21101c01c5000b42c0b41a800014102414000501250002501c075105002c810600c0d1b504050550320060f40510540340200d01e00044d4039000d40035140e65402c0507405459540140200c0c000000c101c040306000d406100000d030303507034810303c0100c031112461290055010060314011078040c08c001c0c00308455202280140501110300041054420f400c04c503405407401c8a09400d01000031001604039600040c0c0d2501401c0000141114440780c4c0308 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 397750620 1250 397749370 397749377
    0x604140103200a091e0b0109260c100809060604052401021c0c061a0d030f0203040e1303120501081905070f0e0609010e0c0306041d15070314100501 65
    0x40c4031405807283d00481e40100319406050001c14420304404495018402902c014245030003510180b0b90b110300030343d83c1200c0701407031308070b10402d20000c03241b00f030014510940d1250b1040d510b0040c1c168540b10344200c49800341e0741d00d5003003a041c081d507240d0038880301401c5544030300d083c1024031500c03000c101c14100540440d050400750b10140d010043c1d00b040c000d562179210701d003022403099040c1d0b6000076140103441d20070340f02000101d42c0c417100101103171000b0440035085642c211070f6900084c02081c05240d10b18071401181c4c10725540c2c14410700c4041d001c03a100c100c1c00030403142d0042016049810036098000190702401907605180d650380e6521114940c2503540c0c050000e403681801800e05c100d902410001c0a00d81002d5150442440ca100040d40e0590084a55000015040f411400418081c41d08442500d00d5511040208400f401c0300c50340c140110241c042c0d001480010800454011060040e075408440c07802c45030280c2100c54448a8008442c1c9140820601401c07684104056030340908 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 397751870 1250 397750620 397750673
    0x2060604180605010b0c160308070b100905010305030d0506040207050c06130b0301080105091203040804120c080a140601080a0c051009120606090b06120a050a0f0c080604140103 78
    0x500c500c0e10710341c41031010340390a00c1c007030001c05c03801d50a00c01401ca90a00f00201d0b0f039a83d180c0c00241203030081521014200362030602030075000820254074a60803520307485603024503984800c46e072002c0f06c3c005c2c0c0c42180c1c958000184110382044034040d0540c00345044908500b0300c0c065480d200c6c2c48a002c1e0b1050b42c803440c40014072155940c0550f00501c041c010303240d22607480b0740c1c6031b448290003881d055400c1c22852160380080101c040daa00e040324031503a07000126504092034800302080440c41c981e400c9442e88039103080450000e000700300c0d03410002d00544200d10319040d210401428400180c0180209400c000001e0000c1501084400704449054469002550030403800310ba90030307280e41007500600c0c0f07507480c18070a1000a4002400b6035070910020826000701004000662150490703402d42040c000001442004d125030100350301407132541012a03035050403c005002c603100040240301042e044802e002140c103192141443d03041c2d0b8002c18541c1c2d9415600c6140e050401d0034418965450180d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 397753120 1250 397751870 397751891
    0x1021209090f07261806070906030c031e0504020f0604050f0d1412040602060a0605010905100e0303040b1e04030f0f1b030c090b010206010f0902131703070201020d0f02060604 77
    0x21881c240c200b441c061310300700b56034048400192640304141daa0030010340303403151a4010b041303020a4003400740c0300035114000c00070300d080400d40142100c4042002495628030052062000c00c1008c2844a907148100041303600e0280b040104402c00003201a0040a040c4014000758543c50010000e0303070300c01c440911a6246a291180c4034902c5407240511900600c0202d0030a018100094010780c2c1e21070b02911038903503448100d07000b283c0781c0d032190b180041d4036140108803a003094a0400c404880c103282501c2c0341500314020a155130b1243e44125030840303002882803900100003040718102984050b40c2c0f0700d054a1034a0740454084101c101420070034844a420081000103507001c882e040342c3d81908101745649051140c09041d4034070a007440d041c2040d03130005940d80302082d5941a07942010004a0007030030604240c00035000001540d240140746e0750041080340c0001c46d480e148102203401541c0d5100c0c0c500c0020b0030702542105103020b1040c50741680109640105042d94004401c1d60001201003c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 397754370 1250 397753120 397753127
    0xe0c01081909060606020c03060702061302010e180f0a0f1e1104030c06050711030a020306011a04050301020f070606060c0f020409030318150c051204060507030905100b01021209090f07 81
    0x105400100034900c1c00130000340007030300412407101100d002c0741903c0c00c6a1307401d08207980b9007508560031072100e000c048040c0019800703104c01821190016200d942190811400758441d4002503d40c074506a0784581001014883c0e405005004895010203020001c500b04004001040c0e09103503070079039070b00c801d104d4800d031500c80151002550080702c11084542d8801d0060450342c400e1009840c44c0005244e65101c9040000e0440b015503409402001d039680b80c908c01c2d00c0c1100da04120800c03d040e0400000034980e409001a0a0000b00488040d544609034584401110404d40c040c80501c6107582e4045d000c40d0311505400d50780764064030301150b164450f180031401045401c000f8007101b809080d80c1c81c144101e1504070981c0115120b01003041c0d0104a5040d1854060b9806540c0402400000180001c45a802098100405090104111340d032665000d040182e00c440b814030742581da005100b41503074100056402541580c460314545158000032442aa6000304801d00d204400004154082d20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 397755620 1250 397754370 397754381
    0x2070b06061e0f03010906140f150d09030933050702041104090e01050105120d030f1404120f0e0a05120a14030a080f1005100c081c0e0c010819 63
    0x40b00d1261668501580811540b5038100f07000c0c0508082c41c0030381c0850b00740c00c0c407220001042d60080c81074441e900804d040040005407014030b209600418048403c91686a00034803a000f0708c20384507410f0490400280041346812003920740c0da2501003000340005203200110a07107050020b40f624a80e01d800c82e0010802a0201080341305400000040c0010700c00000d501941d10b202040000784442e0741e0b01c6080009281c1d03202c82041e1190003081c410942c41d8044d5100f015444404240403404a000c0700203900441c00840b4251010306603c1601c1c0401980039a40b0580030b251800c5c00d000301d000001c041803502c4803a02a442c001c42040c460111070032020002a4070040d40103151110060500c4a030075103a030807102440c400714002030082241001d00c2403900e03101d0b80c0b0340b2440e40703900307880c010410003403145071070b0101c0c04c0c400b49645400225003084010100b078048030805a2402400300e1000044600007032600c5000e8000302482500b5070713844410b060300001c0300c010f910106200c1034015802002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 397756870 1250 397755620 397755667
    0x702010204081614010f051b12030109021903060311040f020c0a0c0f080613020907050c0f030307141608090402210609011d04120519030902100302070b0606 69
    0x204003c83c0b400c01120920121044c0d40c036105a0991083c800401510011200401140032850520015103041032103883c400e40d000100c02150384000d00d1040240c0c0540c02a00407120103600055078505005400902000c4c100706481c041104514540700d121604480366403c5c0d100700d84a6040801101d4260150b508056214054030881e0440745000d0b202c55000c0d02c50082007100c50100020003d4010515500c100c00304160500c500441d942000451013000f8810400d000c82440600151a810003031900d45160900c015aa6401c086c200a4003806000b0220840300008001070f28406a42c808064491a8400802c6480700c00c25070000e00039005000301e000d180582c001c400b10108030959038983c040c030425036401c0f041e0b90b210081144d038101c0c11810091400c1051010400060b6400c00250100c200c1e45001401d0240318402c2d84e0303003640640138100c0040d4549003000b0a600d0485401010304103281402c51900d02c1a80e03641c400028010182442880041214405058905c00320000103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 397758120 1250 397756870 397756873
    0x402091e070903030f020309010203030c070512030c130504020405030309040c091814090a0302030418060e0901050708011e12080702030a14060907030b0c0a120e01320f070201020408 80
    0x2481c116400524552262005500003044034031100300e81d90010086450b40f103810390180d4910f0361801001c1c6540d51100e1001c8a0a1117100050800c0e40241c102450003111022a220741d120304007a018403448000703420242c89107104000801060350000111072489a00380e60109010b5941c410545100c07100340e009108154244203803c403208455030211200c000c41241d102c059881c0c50303070380b0340d600e100c1c410006000d40d2040200f84440f41c204a40c894140d102007001040307854132020605410403099800c1c01c0c0d103a444a06009a40340c000d918240509401003010180c620421b100181c0580340d0311a800b030b0a50902000001e0020103001c40e00c0103500a000c50b4001000f0b032401911040c2d500104040900940d40400d0303105a012580c5000c40c0c2e08003070342505139181c40c042a01c16902031342580341400030000c01c040170f00308240038804909440300000180d81c550940300318014a595040b12019071100302c3e41801d0403904c00c49080d0813108641201c042540c030600c060f4024803171900004101d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 397759370 1250 397758120 397758181
    0x150901150206160906080a020409020d020c010e0c060301150201020c01090c15020705060301090c12090b090712020d03030207300f020d0207051201060b071505130506040209 76
    0x140c481184044003032850a900721516562030014101c0c0364566900204005920342e0000c1116920501c0a29002040c00d00011301c2d01e544c4040a8080382e000300b0800100e00d402051441c2c464100703100d6400da200088000c1c04c40015042c0002d0003030301c014010440e40030740c140b92500003e4401d60546900b0013a41c40208140784990401c00003d04551041220000200311000d60061006c52240c0c101e450140115085900b0002d000c0e0140c488403440c2010441d118050340c28100f020f015034850341b801200540e4040c184501c00b103040000300c0d000812441807000c4100010b0712108140b41900d50580340041c0c03640104c0c03034000750760003480c4088000c034103140203011050405015900c45100c2c681d100c0d00b82c0200c0301c600590301c1d14140e1607400c025030000c400030480740c1050604100b140d800b007000007802949030343c40e149094106420544d18040c41c103814881c118411b00c20703a074000d0340c0a440c101e4410705030381d03c480e5110750080c4024024400c01d408a5859003603100e01d041203d1441003004c28 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 397760620 1250 397759370 397759379
    0xe01090f0c0f06021c0e270a18020d020d05030702060403081206040513060c0e040c02100b120a1e0b010602010f050c160f1403121e070507020108150901 67
    0xe0100780360040300348001034003400003400c0c4d000140c500c5110041511003c00845001d0b010303502c05010384801500a0741c01c80c074400c1d159a500d0508504882100440780541c1001c1c41c824080b55112003184110359000c48130030340035039540360f0010001681150001240300e014600282940175080c4000e404c131300f011801008102400c0c01420003411880c044101030307a5210108000c1e00d40559049407800800c0398100701243d4070307410a552440381800e0906c81c0d803012a0200b4221074041c41440d006802401800b41034003505c0c0240c9400060443d1003101e02032000c10840d0701c500300e040d001404900c0e110241c03c08038181c3c000407c0c0e1150052082d001c55a95080c019018086000d2920364040c9090001884102003d06032200644800c4000d51001c1c0700740d032240c01600b00d100301a00c590b4888000485015010030040003d0f00142101c5240c6040070301e2500300302070004000d022104091010064110751140644003047c0c2c0910f0000540d03213030307100c21030203858041c20340ca0f800c01da2000c000316 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 397761870 1250 397760620 397760633
    0x1a070c080d0c05010e3f0a020106050307051807051308010228080108030901050702010203070206040915090e060c0702010c050708011512150902130e06190b030d030e01090f 76
    0x3114020b00c020300c5801e10103001c858441e4000e080900034028003407141b0000400c1d8074190580100e240d003a442d20040808840401c0d50090740301000103070346900040c042414188800802014140c0d03034443d100c00302d11011240900001d00b0b007001c10601140a50480307155031032800040c10700314001c55486601c1c110005c1e45511015003000d11503094a41128118444c81c9428101c580c2c90340510706001c01c04004640d554032a5600342e045100030301c40b020150303440f10000c200509020705d00144401c1c142100c10110040e640c4241d41c054a0003010308400361020410b95440b8880001265990020740300607500c1c0c0c030007603e0103443c9202c1c1d01c0d00440e1915056100d508144070121108040a50390000c20300c22095000004100ba0304075060341440c3c02040c0c0049100c0b41c4001e1030481d510002d0070011007128400046105160701990501440041c0901c081d003444405131800d0040c2000700e008296034440841c003404c01c00d40d1750440c0d42180c040c02e5005100c0180c0c0070407994007120072401c1a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 397763120 1250 397761870 397761887
    0xf0403031106090d0806010207030606090608430902070b090705120a02130204030b130201170103020916120609051f08150603121c050a05011a070c080d 67
    0x31404a400c841c1e10324a06480052514410150680200a641c0f201002191031070390141c502810744c4600c0201000143d03540c0241c401401140100081440c030380f10070240f03041803c40850080c0b6240120303540e851901d0301c0c03003d0090700000c10341c81410100000d041d107807118550701c0301500381d1001c6240820407400300c1156019020310400c446140791114100101040c1c0e2914002803075102c030640300014144040d111200e0700c0341d41c1d001070904d966038403850005c15048840320401c50110b910300c411581c200e00004144030b8101110700842d070443d8089000c6c41e1018100030462003001c4000c224040c40742c1801c416a4001d0803080c00380564030247d0101400c4150b6004182d041c41003186112070705041c24520885140302c00034844150020384499000388003800c1540c15000c3c41b2550b11b109440540203100d04d6031900c103c29400c1070303000d100341c3c01c8541c013624001120341403d0040041300050740c03501003c800011034281d41d035501ba160010015030181d014036158060000e05c145420341140c0342 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 397764370 1250 397763120 397763123
    0x2060c0318270a061511161a0c0f0d020705031e0c060310030c060503041506060207051e1504081204060c030509040f0603110f0307210c0b0f0403 64
    0x7100003082000d0100420710001c02e0a03101410003440c41c1d84244000c41414a030040081c1d940007440a46030324140900380c026052440100350304194100403124100402e86403081500a00c0004508144060540d0348500640f9150301002103200d481e184002c1c01780301c00171486078003190308220702150060f440c0c80281c450b10380300380120030f2032100071b10001000c1c80c5c100780070802402c00003c1410030080c09420180c290904103904a4002c400a09080b40e00c40141096403100c0340c99203024941441c2000c0011032280e5094113000d81000420b400080320015618104c1d030322225051f80305070001003010020b803e6a40000710545000c41c3c01b444400a009990210082c0d40513060300c03800044040c481c0d4030031000010204182140880e104002904030307560001d2001c071f00f44505c014880c0070b461494000ba19403580307207101a0309914002c12188891441503000e00b0045282000361500101c02040030004030110f041180c0421407030b80200700107441c0b4000725540340c841e1204c40c8e241607040f9000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 397765620 1250 397764370 397764397
    0x10091e060b01020d02460503120a0c0905060d110d0b040c1d092d06030c03070e0402061b03071a0105010309080306120f030a030f153002060c03 63
    0x4c030380c401480415821030100024802d81c4c0c00300d209444e114400743c003541c407074074285501c40500c4400c052071082c1030440c41d01401c02151143c0265001e0602908054200ca42c407524001020900e944c01c6041401240c01c1141c0f4181c9030b11a401e22480586068407038800f22900001d800c2c4642704282d0302c20300c1181410786003004120400f407001d0741c0c02220f03005d90f0110008078180da09024503000c82815400302e00700b0300d40b1220110501088000d00800088113048207800303800c1002034181000f005403107400c101c00808420346085150444408041d0019001e080c000803075010010b408501180c2840c0c4200480380d448205007050585581007000745102c03820040000503056109024000c0ca40380c000f010740345141c5482c0f041200980c14644a025940955803180c840c950092001c3d00c1a5842c43e100801c3e50818203169104507a00000394221800ba00c4400b4040d40f074501800048280c0726010003814a41101c4020b000c65081d034900941c000b100141d54188800040003a0204910058 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 397766870 1250 397765620 397765633
    0x403080717120a0c030f0e06060306070513060302090616030801140a14090a0609060b0408070b1e1e040605070b1305030a18050901090917090310091e060b0102 70
    0x407103011007445a802d40b0102c1103036580c04501801080d52183c800c211650a00181080c15520540e0503140b00c1c00d100c4049410150803c030301410107211a42d4408d01c01c1c5081c5187c0a01003010740100d2909004403010907174003080414035501c50804544c10704a6010303082c03102c07424900d4020030181c42400b03040d901021036503151225080424200301074411108814400f00d941a0034410505001010800e0f4140c1700d080001c1c074036040d849200040c2030031410003a501e07418a00c110307240c040d40340d1092070b0500d030800410030810b0381c0c0349000441c100240425580c880000c41c02042d030700e079004e51150300d00780c001400050180c1c000f0b005101c41842a0b038032400654820f122120781c021100c0c000307402c0d5041004000951442008401c81c11070368101e6050310991100d000c5034080c84260040e03010999030700e43d0b02050000d544241c0400c007001a070480d152400d10008039172104100c0b1240c038007260701e4060700000c10800e4400800c2e40d43c6218015000454582484c0000d480000c4007280940100d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 397768120 1250 397766870 397766903
    0xf070908120d0929010503010c110a0206070203031e0403020114120403050c120d0b030c1c0605071713030305060d08040308030c2b05010e190506060d0204030807 71
    0x421002400300c0c1c0886000e00340540070542c40040d0102c3d60741101c40070700d0000307070036100d0361011040780e101503210f08501d900398104003e050071600110890340c140840380c61031070032418002a003c51a90b031705132031440c0c0720041840400c0c594028000702210008201c0c000044c4600755502800499000b6a1841100e24440c481c8091034802d42481e0600c00302180005008030340500d00400344829503070220b48602c03038204100c20094004201d407003401d6444a00e40c034a40e281c208074000740b9250480f0040c0b0284038010300702100d841c02d507070000c11640d294000500d545020304400020082c800308509681e16164500400d1a0008442200480d2030700c4041441ca00b01082c01500080d17000e40030f03600d01419926800d25075080144942e8070300d01e080042001040808882c00c40b450504082000445039601150701501c1d030580003004449402c10030030044d404031000085101811020000d4951204000b040d4503224840b580c2000900000340001001800001811070500a80120b485030214 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 397769370 1250 397768120 397768123
    0x80a02010516050f030a09020a082d070b1801020715020c041a012a06062c0c030a09050f12040f080a03050702100c06140708090c0a1208040506030f070908 68
    0x240c1314014400c003002d00010707240c00015446291070600060859a00d070b65296800c501e0311086041e000e400a20400d00000d0980240d06a01000020b50002e070070750782e041110008240c020100c05881c603034161011200c4a900a00000019140c1c002040501c80944d10010b03544e5034200350400c0c02603242441e000560343c441c0040454409050b900c40381201070f5140d030080307030340c00001d00d510103079854022200c0014041d1054200528100c0c104e00c0e080c0c4000700300014402c5801d071050119220243c100f140d0100d5603030403660311242d03000c03002682024500700b181c60a4245c1e41121424030845580306e440811000241044039803d1200800d801d440e06d9035251102c00400008010030003d10150380140303030240010807031041c00d18106a8600a03074886000703403013603880100e031142c032610203210a0325840250075500048880007014000303070440c0841e500480510460416240da094030100300706181c011180104402082c2d1600e0341803040d480c50b00500d0958101001c99001007000030359030030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 397770620 1250 397769370 397769377
    0x26040618060e0f060d180203070902040303120509100c1e03060806010306020f0d110405120303040f0b1509040501020405030f192d051b04180602090607080a0201051605 74
    0x8495503141d240c1e810300740a010b510040c000030240d11203020711a40c0d5000c0703400d00c00c1206041446c1d82c14100085540185070038110f0300c1c2c00c20805680100703c14004203400003048600c107150035800140325a500200f617824940500f03103200c4454204904246195440000c248140300f81e203140740c181290010b0240d0881d000c9204120407034101ea0700400100d402a1f0151800c0070b103030002d0714a8944616040310032220b02d03c2c1d0303540c1844001b20b41402603060003105e0b541048100402176145007131640300c040710b50301140d400410480384200052a90021402d200d00c0b80403028007000503d04062421038040e40050040501078414500155019040042c086410b480c0c190004400d0f8062030300c82c0c0351131f4061130340307442000b003400e403d1181c0f00150700f0005060b150245000c0c2c2480d000701c0030003c14503040c51411f02e109905020515455105200d00d0541035984908016510752016004ca8128000c1c40c0d0054603140d004100d04d012141c040d00b1040c407641050301030304810900300400351000d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 397771870 1250 397770620 397770629
    0x150d0609061d0406091a0108070603051b160501021c05041406011203030e010b06030a0914031e0c19050609010605010f080604050403091e090f060b0901080426040618 73
    0x790b5802281c085082a800742807000e000701c0070442409079070b0325840b02c6c40b1002c0c1d1141009a201c10b5042000f1541845101d4014849011481842540c03110302c40d004d006010010581c0b107a150820303070800009504590000300503095100c0380ea00880460801404201d0307040c4c403400f111902407060a0004225281a10540000c190007a510703034404400034400c41050101642d646c43c2c060040d559035501643c0302d03040f501c00100c2e00b03c44515200d0700c0209034150302100c561040c00304814000251400a00c141c15242d41140c0300c0b40d034400147c1c40c111900c898407180480d10301104051001c00f181d40d612402c01600284015aa150011580f4600e000b07010400201035001041c42890940c0106400600038a020b850082e1201c0c80c000c0c018411000743d94060505000070042d0840702e015625840311a42420030040d0315041c00e04c40c2c44e03c205c610b00d42c100f01d41c2d50002000c00448905038021444901c021441108854005004a6005004160201b02501826a40e460311451688140d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 397773120 1250 397771870 397771919
    0x9020604170309130506042405120111040305070e010b030f0105060d09060c02010b0103110c063d0311040e0706050f0702060c0d0807021c0509150d060906 68
    0x251810200601c8940001034480460100300302c6031900d83d4810004440300070361542c0c00070b0039003030550800084034200040386418072580040283ca10102c040030508850054580c10000e0354800302081c0103000d001c030300204d07441c004500031041c0040090050152141448000e4203a42c031a0403146580c0011103001c0e5000b580c0c6401840b060416001034150b1880404003c103500d8100c0e82c4074000d0b180c0078806100140c0d903030700d09c1c000e0300e6034103006d051140345000744a245000c5501d4462074851a004000200000e9005082c50728000c80d1443c4012640c00d402da4291014128040d2419081151000b07031400c8091010306102c0d4039051084090003410040205801807900505403030310781144800c40d114440c184040300150726040c00405910104001030002182454809800524041c15590031903100004134200e07003a800c0003c101c5d41d00c00b8109142c0300c01c1503000191241c410805254081d1601203940c12070080d285e0410002d1381d1060009010310303a20380daa0b6000594110704c01c401d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 397774370 1250 397773120 397773127
    0x61009080307020d02041b12150302010e060304020d0c03060603060b04020f0d0b060d06080304094b0c08180c0102070e06040204050a03030f0807031503020f0301060e011e0801090206 80
    0x510b450134070211502d201820128012610b0f011241091085503208404680b0b0440c10103420055485500c00441c0300d0304c2c08249482c01c680009218580000f1810f00a04002011809569030003100c0d80381070354846155a480c0f0349071b15080e000b070b2500d48400c071030880c03d0644102e011324050081e281c0e8001e285089074100701c0c51604590240000e00c0082d42c010004001c481584800ca0040c003000e80b20800086603a1840c00c04a0800c41e00c03041a20000041c2203a00c10303950752001d00031080030aa1100700745e5180d07080d40c2844425110280034900c1042e00d800041c035152900300109505c80c5800000302800602200e000030740302c0300010310003801600a1f00040c0009000c00200e180c000c54042d000604040e1108003051200d2802e41060b804180581d01d823050003035000c04880d81c0070050346002d100080c0800301e8003840301014080203101d44510100d00381715441c01d511201c02840b000c8017040f201d59440d4039a0811b40819062844602600e54002c1454003050140400465018200605c1c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 397775620 1250 397774370 397774373
    0x150a060b0a27081605150f0d02090613081501030201080106120b0301020c060130080901020339030f040902210a0b010801152003120c03061009080307 66
    0x31103031003100048640c00d20707000c12035240c00b4031820620042c080e410014a10743c4c40c14180342241241541c030007407255480c0616005600c5403901034800c0441b11820a0303407148003007031400003c0c1c0a034148050300040013040462021a48005d00710482e201c0710140d03843e980c080c40084d203072031201340406400311745404010404c1c04c1c811a4804901842e0341000500300305201c00207400d981c04030580341030660040f00148203085601c070300420400a20f02440070300000340c501c80f030450340780404003030030b00ba0020800d02e1160740240104c0d90000303514881d211100400c40003008152180a8482d0303000c855101e503070001200d00000f100c18003000504101e080c280f83c40c0341d04e0701942c001d20070814000c41c80600001810075900351f26015100c03204011541313003000d200040c00048140d101241a00c183c0701e10310011508402ca10003c10b171600030466404813401da00500e548104030006549941403001c00402407941006503000d80d03811128250612541001214503504900455a480c0c008001840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 397776870 1250 397775620 397775627
    0xa181e0c0e090603150103080703020c0121111c0603050106060c0c15140409020d1b0c02010807180303050711090405421602070b090103230702150a060b0a 68
    0x164003c3c801022250042450420410140401ea108841d607800c0407410100705a0140802c0c07441c01c50038070f485070011414110f01700030300a070130581d401040e0780d07034045411140304201110808034180300b118040c44a00f00c240001010103120a45a030b518007080441c52174450302d2019007031500045286c860030f003080c4440d03280d41e041d51150810f003d080080c001e22064401d0103003000705040200140c464201815010503129100810381080d0030f10388a2030fa1881c1c0020142000d5a02840d002207250740b02902900c15020039210b18041c18030b407907000010154098010034015108a8264425418000c144144040c00707440040c071603000140d800d1140890b0000950060b581c1c0000c48070340c1e19440c2c1004c50b420503501c1c80c0d4188202c034941000030f00d5040407030010065000b0f03c000e018071131420800e000a800740c1e0094504144c0c48040440d0b62000e1803403140703803020b040c0d691142c0300e0501100203940c651003445144d1148803c4030001d10088070030300c58103084842c49035295140c03441c0b0384002c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 397778120 1250 397776870 397776889
    0x3020402030604180305031b030103020d0602032a0903071707050d0602090d0b010501020f0a030509060a03091401140108012a23040501031d0304050f0a181e0c0e 71
    0x240c00c1603440000b184403e00003044d60000074000d8039680d58030704002c1050303034032488070800034500040100010001030b03d4100c2c2a051446c0c21010045c1c40351a08118000c016050890048002101c00300380c8880c0d05688000f011a400110100d8408581e80d400c0300f50a504030000502d03807500000710400040c1800e2418205281c492400149040341e030750300091484501a4041d95800d0309480140419601040150303940c0100c90001d00784800c4654005010788030b00320115000b07030004034402000318003a400c0314995035840451a40154495400c240c000e01d8080103441034400304400024400d07006104429210251031850310101e494040c0440d960a030104d2190b0410140400000303054151326000c0c015501024101a902c2d440c0600040648088014422a21401183c62212180000211407c45400303403010010820850b0005425411303e50000c9091080340003d2009100790b80c0c4060010800c264016081800b80c0d0961000c84c3c03d660078070f402107880c1d581003c01d03600e00a02c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 397779370 1250 397778120 397778131
    0x10e0d03020c12031306050c12061c02131406060c0705040207020f030316051b0916090305150901110301080604020108041e03050c0105010e0603070b030403030624090503010b0a0302040203 83
    0x12030f4200060821048442d80c011201e83d460480324081c4642000b00c940140c40d003189a6041c0c190500c81c048458610035500a00b0b010f210342d040c036036042d006180c3e00440600054004106942e103c00c600303552809842508515001000c4142c00140180350003010780750f02c810707554000d0819a082c002480300030f51001e41e0681c2d001a151100c034020f5034040006101c1c1c00e80e00784140007a81900d1070814504031940d03012000e86c200003101d003030703017030b21600c6200341e00c15582f00155813086050101650075449580010305075016400b046000d2a40e0180414000e0401e60000c0100c03540700002450140820f00412640d81c2090b00801c01540c0300b020f101c3c3e0031a0040001c010443c0104d0303000c40102e025844114049240410009200d410030b2044900414034001c3c251428a0304000094176455640100d000c85600440810281403080e070007040680103903440400001c2c9020740c02000c4040d42d10000380042c410010102e26418180280c0340c5484001d031004451904550800c0041d400003000e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 397780620 1250 397779370 397779373
    0x604060306021801020c0f061206060d090b1608040305191701060c0c1d01031e0506010f0e10061b050c06040306051605030403020c301c02010e0d03020c 67
    0x200480410706610040c200000da0400001e80d03101100e00290400b074040d20901d10071500600403040b25203036901299201010501c3c02081c40d03603401c00280150107441c44003d03403546010340200811070420303c01030003030124000c0e40c0b401d0352034540100d844e05011140280003074000c3c0a040701c1c032101d4800910b244591424050592000302c0c14503400d05c2c000360301c03a01c00a20883c201034103025441d03030b07500054011100800200d840584005118040c18403004241c1444040d00c1d1030040804205038500a500a044d1103184d41e5407400d800254242d03008100210010300081180410003069107002c070342c0ea98942d2007a4079040e01041903d902e50110a80d130b14050300301c04034001d954100c000e1000e588689000603140c201100c82c1504200180e40c007505000c010400c0c04003080c0c00203912050101c04480e4640d1100e10901c208100c403120303e032114a980e205550701c109182002c04c2090440d00f01000300c401a120380300c401c03400c1e45c490180c1400c49030000c2d0481c2d00709500c40c0e001814030045800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 397781870 1250 397780620 397780631
    0x80a2a05090d031817060103082206030204090509061302010f0918090317040b0a0207150f0c1b0b011205010204150519050426072318010612050604 65
    0x30104a082d48000340c2240002c404154203106903007400b001c6070141c865007400c028401c0d94480d20580d64641808080c2c119400070440340ca41001403c00503613440184100c404150b0707a52107001d00650410f00a60400909100025540c2280040d1481c4645034200007003032011104d4005454a0340f883e1601e0081045030b030404214004a01c940548421000a00041204250600900c014400e61310402c45c9840c890520022a141d1032056410032040c10005035a030200b49885010f00e041d03410858015820312880d20785030020307680b01405140168035200818122086132101c0810103202c01032002c50f1043c0180700c19400d4504000d01907201e04001072909440d00b203a807900007006030140002a00014400e0480000d03010f03e80300c1a0300b00d090090a150801174003040e0700f4110660f4196640500c04114440103040044100804404030ba40c0e6a60a9002d2030200c4030b40c2200040e401603c500421056181c1e40c607480310304899456482d40d400038090140316016002c060115a4026241e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 397783120 1250 397781870 397781887
    0x1204061d03131d0c04060305071206061805030c1e0a0503060907030c0f06050405010f090905193b210409050603010608100b0402040f15080a2a05 64
    0x700002c16515502c5040505060b00c2c110800c1c15116075420100740f8090b2000c02c0c814580710083c2510142c03035880c02c005c1030f00d5583d07550807144c0605ca6224a003051381070101c005450341d04000d800b030740003a540480c03000e21600c0b01c09040d40c9180e000709540d00a4840b151910255401d00358401080800071300e04e03074090f070381c843c0060324000d8144e4000405c2c0e040000104100989072181c0700080000350288240349213082c20240c80c50255105035410b0003500004805032601c038182c1c440141096980400c00c600344508139812510307160304442c040c64540960f800711030589802034500c403110000c0c80c0c40040c1d4100c400c01d4040100351145000c07441407000c01c19612441d00e800c0a40e80c41d14840d40c544445c601140041a80e00c05071289000b84d240c101e0504c84104c0c0030035034400c0822000c4000c81d0304840c1d000032a00a12aa80c4500302d40701c801c51021541e5106c41107801e070900d185e039840f48203030b44400b0001e030112040d0250400c07034030444100c600d014020030300150b0000202070400781e0800044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 397784370 1250 397783120 397783123
    0x72105060c0316030627140c04060e0315151f0201091a0402090403030c02030405040f092d20131401060e0102070e2706061003021204061d 61
    0x80e600d01c145a81c011040001e5286640ca00307880c0c44401d40360500c902032800c2050307683d2208a05c2c86504020342500d0030407401820341c02008101d469540004543d20700907440090b10740003801081c1c001a1103002210b1039140004d54801900820142070407281c5a03101081468203c83d01960303000740313540d40c0e08071421180d400716480c0c000e85030300045400b4000c0d240a5103005001811b4002842c0d4240c280800360300c072807803040d80c040e038941000541c19100300c030164518005c50740056806400c01c04614015040354200405c5c40348a013950710f041c940d592502e0f12030002440100580c12808025800100c5da0110920100c20450f4800c5100c9060fa0004148070442c00c1e1038600701961607044122844801090310360042005280a880303440300f04e40002d44400061091803440306180c000301c0c09032128407006494035004180803180701c0820b442d07071945685089a686204062510790460303018020300072075240a40401001419940b00d03070750900244a814007140502d20f640c456290b02315030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 397785620 1250 397784370 397784383
    0x11090f0411070804300b15030d0c020901080102190509040f090605091c0e0609030708070806090106050609010915030b0405010b0403140307030f0c08070818040c11072105 75
    0x184040c140c1c1d482c20300d0480381c4140b001700d40c0503d440c0212041224404252815503950a038800c4d55000c06850340003422113010340c8903104c10f0780750007028690f6500c0b54002d4160b50040303109941050a90b0380c2c2d400c615080380106220b103440781d038404e0080c88590388207600038189100c00400002d92800c2c0081080100c9810603c120b410302d641c0e4013803201a640800170803040744a440300d1603440401480380140150200580c2c01e000380e001040b074542568092008401401100c41111100d55441142c1681c3d0001070300d081515510342a40441ca42c18020222061560180c68418066251a00c40b00000121400090805a81e8040f4402c16640c1e40511802442c1c107010403a103450850402481000640041603155402005101c00080c5c00000709c14618a1070b0400003200741c82c030308001500f032003206c00040c1075000009281e14925802c1001d80c2c0f000605940401c94086242015900040c401080303103c10351001904000f201d040c101e803854001c0030311181c181041b01d02d50f5003500d040d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 397786870 1250 397785620 397785623
    0x2809050f0403030f29120f0a15060f12140a2d1505040c03081207090501020c01090b09010c080f030702120f0403060c0e10030c08090111090f041107 65
    0x125103040c80300341a81805a090201c12200c420081c0c0411440d40540b00b12a00c01038a05042420904072040c2d030b05c030f450010a581030681514203006006c600c01d82c44601e0307028203ca20741c2407138003d1301e142c601e50b20483c001e0750004030307820110f1030501c036002c152030030003400445045030703190a0b504100d036061100c2d0350054840e543c40d5600b41c0e8000303040b0003d402c1c00003110b890404641800c4000c0344495400844040120200091545907414691144a4681c0000d441d42c8070010700e516040780d0f00c0c015241f05111551310622982e445030012a200c903d00042c542c002400b0382418004a5038400090421040505090301000c0c00c96450401a030015403002e0344250000c010064110780500506854200c0e983c00d5034602817000907081d2281c000c502000d01819550844401c00900801d0002d05194004000c005041c194502c024007800a02c4400000524480d0109804150500540700c03088181d082d01c909120070142440f01040a202c0d5407940161540300e42900340da0000010400346 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 397788120 1250 397786870 397786891
    0x423060712020c0601050433091512110a150203030901050606040303091707090e0604120f0207060e030c09191a0604031e0c08010c0201110306280905 66
    0x203280c10240901421070030004144154010084200c5003030000c2803160542d0740480e0006241d00813114170072030070780340e05a855000b0b40c0300c1c2907a0310000c0f81084034141101d00f14030041c05107103206001a0184130880c8100d050440300011030030005130007280300c4c2103980c5024001d2000299110340c0d03910710010722000c0c000940c00000034400301201c02e004041d841081942c0c42032406155680c000c215054034440c5c11079800c040075036034203003100c28060700c001800e5450090000782000c5c100d844c2c891106aa080303a0700b441e80c140c011002c501400c071442d080703103068019040c1c0d1882c0c0700c0195141e58807014541e41c10b0184110000456850f8810f190003403801d2030b516070f104548451458100c81048680700c0d0b042c920942c0d01c9500e95204007c031010f49030700c2122200200d4142c41081036070054114014000c407507482000c9070013030701588409800f4016074001c0c032420012000704505884251001030300a854105903280c2816002003041c07141440300f5040340b0040e618012a002c40c0c0041da10308100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 397789370 1250 397788120 397788133
    0x60b07151127031c0810030c030308090f010f02120601020114011202121c020d020a021f03020915030907050a0b070206090312180f1801050f030c04050406021210030f0b0423 76
    0x7a01e601490840d030013280301605606c45411511515000100703444000c003008103243c0043d40040040c8040342d4084000e070300a100069034045010040e400030a0700d044c0b030b07003035000c00030340c8a600c1409030203040d1000300c45c1002640d00384040301c6805605100d059270801c1c00ca20481c60031103403c2003082450740568241903030383c800102c0028180501c0c004203404540c0180e03100070241c0d071040114800c5401c0d80070103c0300d50364105410380180c0640d0710011303031008401182d0034420603402e0065214a41c018140d0f883d85031210b0800c445c00400b030140d410509000c1c0140d00050510f0b5009114240b801400ca55031a80d1040c10020710354022103902ca0849001243c1c5013150404c1c0040000b5001c04842941c0c0000c200c01c0c243c6001e40e014480c1c030384510a0452500720320784090018407110390f0040c006001514040c18000080d5002204460802c0255400039a80100181a0805a99111198a20b86040d0f500c0714402001c000e0320560303c0100e455084050b1418030449000d0354004003002c7c200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 397790620 1250 397789370 397789423
    0xa02090c0306180f0c070c03080c0a0302010501080a05030f0f0913020a14120f15030d08012102100305041506121106090d14010f060b0715112703 64
    0x4000350110304950707030789407680903c100130340e02c488a1580461100151070304d4a4a604280702c1c0d00c4003980c409014480c1c0040c9010a5400214880703002602a130000c1c0f00c0340c0d0381c56421130764a00000c0e4001d40706400911400c00d140340c0d0000207122100049003283d04144802001418054444243c44002c650004400004541120403c40f81d072052000460915401803c55250418000d1480080b08212000140000203031911460b1000c00a004c480d03600b444010007031310b03151003070085500240651000a814200005c3c40c40319103940030341205000c00441000b035010304005402151403c0c40b078680c0941c2c40307542e4801d12000380044081d0a0ba404c4050403c200000b108100c0a40a4001080000340585480f00a00d102c1a4000c4512000c900303114150b82c0142006490b41c0720f2141000c100284078056400580002d9001d00c1c45c0d02c40a4041c2400102150110b40104045a00c02d01c044461060640c070b6805040a605481c1d0148085203000641041070842034005d0092042e2508070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 397791870 1250 397790620 397790629
    0x180106060903140613241109040b030f031e2101051008040809060c0c040603060501060809030c0d200f2a09010b13091a1e0d03030b01020a02090c0306 66
    0x280c60038102c60141480c5d0902107090042c41c00300c10406803807401000d030b50080d52240c500b000c00c40801050820030001701207081c3c103a4a98015207140c2c0c4035a00b03024440205260105030400310140b00c100441ca804044141100c00c103018400020309000f0074080c6000e41c0050b040703015003480c4108660403481d070410303082104505079644a90200410401004009401c0300112541501d0031101e0544900c600380f0381525180c5890300035a00305080c1f0000104218564218a06803621525007040a55500502a50324050a0b000c9070480c0c0c45101c2090580d400b512010318a0030450100094041c90410000e250224060058165501410615040c41d00440c46007003814040e05508001e468286c1c00280c0c0808117003c1d0103480d05000170b00e080c00031945224071004015842302400303003240f103c00c2180b00340c5440c0d4940d409042d104460342810342c00b103500800c0406004041501c46109910b00310000c000007042241544507071a90704000d41e40b81c00c1d00030b209008000d0301d43da5a140c501c0602 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 397793120 1250 397791870 397791893
    0x803030a051302101d0d0f0203070503061012030903060203041a160221070c06020c010314071707020f010f0f1104030c0329010b0702040e060618180106060903 70
    0x34541041902c01040060f590710340d074a0322880c65803070441c2e200c8455980b580550228143c4079548402c0c000350900800c05c0450041c88070a000710141c0c0e20290340c0c0c0040c143c41e600c080300c1504800c01041d60a2000b0180350030360511540c0070b443c141c0c40c61a00daa030b0311f80407a48280d505130f0320130155051540703a601d175442c0215805120b4880c5840c4400f000d01c0c02035910000703007024149045403103046900d28041c0780143e401d0190841400d001150b0358410180d1110340a2400500081c1041700702c400c1c0390035298083c1d02403032465503a0f0341541c501081d0300c103c080c07020340b01c2d500b1801500d002220b80c20090143e0303e0203800486d000200880c01e0b40b800cac0c045585030942d20442601c1407104201145035240c183c01200c3d0002ca01d003140158010301c205180341c0307140d0719440c400c400307a00100e800f0307048030060104503109035130401c850102c1400280c0c0d80c110071506250f0003411030754450529030f92400d001c3e40001c210604401c4610081e03a0590a403852034009500103a0640c008005110b04050f54 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 397794370 1250 397793120 397793131
    0x20a081602041b140c030c0109030809060c1204110f130c0219030203030f0c0d0501091d010603020906220c050c0d03020f0306040207080702030a1b0906050609010f02070f0803030a05 80
    0x19a104041c0030b02018000c00e00c5482540050100481c5070401e21801b44103c0d240c000f0340c01c0080002e40e0075440c0142201c40243c0d0304c03c070700e8401d1100241c204907040c01100c0040c81e54031076074011540e885ea900c03e450746e1180042c541083d2400c07003850031522080014007000360b4a0341c001c0f4002c0d95001c0001d1070000c0380780c80394180000080360203001c030303401200300c0780c00c42c030118030f180b070243e407a00a100100d00ca01408000401d2400c000003400b040d85a01c030150800302254083c92541000810900703079881400065800000381c00480d0503480e0407054416000182a004594003070840031150880d0b80d80800803021640000d881200c10905005068000e10321741411400c000208621600d039001c001c03c800c0c0a40d5000500da03050044810039101c26a40c003d003200c98428140c82c0c0825480751305401030469804800010600160306e0141c1e9094401c007404072410401c00304011246002c40c4540c000c04e5009000d00440c0b42c0305012a00c1000d050050001d540c1c90402c41c0c11701c000c8400041c013 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 397795620 1250 397794370 397794401
    0x9050c0909010f0c0c0c0608091203010605180402190e0a05120604020907110a020f0a0806070c051c050702090406090c06210c17190c0908160e0412020a08160204 71
    0xc5d400000c4c0301310800e81e0986c0c40500e801505996202211890115901d50b66002d01002000004141e40d0100c000e08803048507100f4800301606038010300059004440e030440c40c0203a4011101d4109101d1500c1e880d01d0400280f5003407030280d03500085000401091014034076130704a03070100002c1d8213200f56000d400c90b1561420a00b070301e40001e6910703118012807070000e01c1101001018121030703495003030032000350084600303441d03003421f2005014100c3c1d10801e07421a054000c040c040b081a130049420160280b1458a802c1d01e000215400c10841e42c1e4014021200c403680c50440d00042010044c4070009404103031a00c0340c1600440f4400c1603441c80d04500110002c0c14001074915641d48030313002c40e4802038040140702c019240d12200f440e800c2c41e840d11003003006c0d01d04404103426981c080d0240b8202c60780031040d03c0414034231003200e0300e0003c20f0b801801c00300803010000c203001800345050065001040e10503925820195559540194020640c5040701b00d000c036102000d52030036100e41c0584248905 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 397796870 1250 397795620 397795637
    0x303250c0e060901120828020c1e0111010f111c050103021011010b1e0a140907181d090c1206130f0206040b070b0f0c0d09050c0909010f0c 61
    0x42010703505004045c01c028041c42c41c80d0400c0340880684810305250901c1140380412050705584044045198500511030441c400050381403520018915a40031003500c030b0390035802c20054900f0084038200a81c1503594050f5817920f41040c0c4948000103030b100303001a5850304a906034044044100e90340d1010245080c00400043e0b0300c0c03400d41000220981004070b040480210414010880c50250700c0c4c2250721228450380e0f078145044051490f02c403c56116428030344440c141d0070606046240303d5017100c0c42c032002c80d08843c0102d200903505210181c00da40400e8407200d1103400d9202c19841b1007048896042440607a540901a400c54594291481001c94400c04c0c103003a52000041c1003100d412a110342401c0c188100240100e00082d0081c003910b941c0d9036250314000403684006402d407520745800c004204621007150b8064010b5488810305070802001c45107000040c501a003084442d80300300807042025840e4003071618403e00c0d021000241038410412400165100b49000008000301d0b030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 397798120 1250 397796870 397796881
    0xf050d0f030605010801050418051b031204150c05030408010212060a12021e031608030d0507020f0601032909070603061d0c07050a08030f0106030b0d0201080a0b0303250c0e 76
    0x2030255411207c3c115408556400d0303c12080c0e81c05510b0405c090824001c4103e210342c042803081514103180c1054080f6602c542c41010340390b0b014095401180c080d0705803000d074400700510507214500380500800036070307241c40e0759200d150f801c90b88545480c04840c01c100007004050315084080400514421030071030600d041560000d4443d1246c18800c5000c200900b998a4158404102c41d0440d486d039003070402105900c46220075a07a0700854034451100c1d0400303001a05031840400c604440c1e100741c1009040c070381d0a50360344295401b414150441d4080d1f90100041c4038508003291103024469103009803030120f082110040c15500310350005071075240d0300710f100c000340f041d0f00e0b904c1030380000844c0007141c84032018588103007005105200900300c100c010042c081111075913130506049036020307101000040c08003001d11012000b8040c019010404200c0058500861030304a10003580d801002d507403030b000c44418001c0290501c00c20f0401150400200c14080041d00d0704020301a10518609420b136150a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 397799370 1250 397798120 397798127
    0x20f031e01120809090c04120b041403040f030305070f020a0605120906060d06020904090f031808010c12090f0506070c060b0402040b09190b12150d0b1b070f050d0f03060501 76
    0x11541340c0c501540c0303010001400480898281c0d0041e11a600c034002c4000b2507410506040b00081c0c3d0165403441000e00d1950380d54100000b100c040742c0b61f25101e2080e2603d140c400b41d8480d040802b05075222161038000e40c0050f80c0d40346022002c1c0c98151102c1c0e0310303503018081c22109140c00904050007036015006105107a82c0b0803042c44485a0b0266026039500710260108001c1c06503005e0041008507009c0c8010209034000b038007034011200026047d5440d42d943d400e52820303150303404691800305c1c10349070100218800d141c011054030f030700400a0114442640e550107103051000c4414030700140008400a007080400d004004441c541102c05500701303810801800e01510800c65912f1244400d1141c0408030501c200d5010001c0034181c2e45c4688a18250004003028002181d0301d80600c0a551414400b03850281c0340d41300a04d40016491041e40e49000c0c00d00408030030500105a2071000f40b0100d00003502c02555105494806e0006d0241e00390580c0010b46111003c3c0500014181801070501407a6407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 397800620 1250 397799370 397799377
    0x30708060612030d020d0207021008071b060212010e0a0c020c0603130311060a0603020a0506270a050909030406020610080307080307050412051c0c24020f031e011208 73
    0x2080b1020b003045148409082e103103104030070008070b1342d50020500c0c0341241c0c925030240c8111070080c0d030200c2c0481a1354008560b60070048038200c005c02c400c000c440011162243c0c0c0c12046501c201401840c0c1000d94001d95441d1009a20030110131880c44100b0001404034021006106018001040b02034800c000085007400020b1000c1051900e031640c0b0024103100703025010130340c0c40e803009841c3c06003080034801014180c90f000c00da0258103880c1000030750741015130854994508065540001440310b04000c80c0744214003821aa114200d00c0000c500780ea00e0074000f0340030f500b00c80010f580c1d0350328102d4060304022000b0301c202d50040c40b030001040300c900040f0840f18090340c48641107550365204d0005844a00480c0c200341401d03a8101521400c001c400200481010010803111000c0c4a0040c02211030410103680241446030b200400000364405a40d640c850768010f41c00075083c082a400c01c01c481d50412142201c41c1140f81300a810400e518035051409041c000780140e03000c00c666114200c90b480b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 397801870 1250 397800620 397800631
    0x5060403030804060510030f0515100806040201030e1f0b1507020d060504020a0b0a1110020f040501051822061505030621010f02090f032103190516080603070806 71
    0x6403544006101b5006000c050405190702043c01c581816160078583d40d0340d0b0840000b5078000d1100004140880b4141c02e000044651010050029640b5680110050300260345034110b1849000003850242c1001d2010b42140c403000040000e074019440200140d030111000c1380c50240c1401c101c0c4401584450b00c0303261601e034103c0d5010071300c0c2d260b40c030208442c0e0809510041c000c1002140103c000e03030b404450300c0380002c000c208490349000c1c3c006441c0124400e40c0305220341c20004200421455001c2c1c0b0107021000c0d809503230248500385200224603400f83d21040b20317000b8501001000c03c6101288150006050020050344080406160140441c40043c00b001d12400c004c21810380b000503d0b0081c41c55030301201e0000d010400007055200082d400aa0925110b14842100c0503000e00b000990503409002e41c040800d110118103042c040558006041010030b4900c11140ca48510070a000c1c1e01d000d00c1c2c4819580b1880905a840181990302c05040d461198208803410000d08000260098104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 397803120 1250 397801870 397801883
    0x601150314070e0111030c01060b0720030c040f020c0109030c1b050f0402070f021f091208040303051b1501050103060603021e0c0307140601080d090f060320031f05060403030804 78
    0x1d0790030003080c5d45980200180702400d507090140204500c040d443c082e001180c484c4e518005540aa4a0300001801c89140c02c507405511810358074401d0700e3300760054501d0b4038812034014500b0003160348541c290703525541709401280e0088030b13030710400004150002046602d404c1610625081500140418012801440c416070700802c004050140d410411314070a68000c10381215903110090060440c040e03039000901084203148005841c90141e89400d500faa40095298507060a6a8060302c003900080006224400400c2411428000400120b02c03110b01c252100c1e80c02d90715240004080d14110b030460010503005210341c0c3c038540c03010f84400b88104000c44506488408141805103103020341d000103040240b800f0941c0c21150030115000d81130314203c030305840028807206c0e410b0307803021079912403040011580e41c030400005109911048486240341d40c6496610f58410090415800a861040381200040104414410130396400001400203480700c509180c40c60700c0203071118100401c00f4116 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 397804370 1250 397803120 397803137
    0x30f030a0f14040b010311120606060307030608030c011b03021c0e012003010f06020a020607030e03120d02030601031d0304050906150a11010e010213260601150314070e01 75
    0x2050036038000305808820303040c080216150074148404c20130421b2100380d4640351051385007486410300100420450108000038101502d030281841450341c0700514038010165144004070b030a00041c4020002c4011030310011403840385028120f4a0090b00b80c00c00401e0610405c1014006420320b8240b58101185080004d0b07040c008003503803405000b4400c1500460000c440c1d030440741c60140b40145041c2ca0041e030b8500c41c615250030080ea9100e1101c803000e540440248280d00009200d1400081060006010340e0a040032540040c01c80381c100155640002c0c0e008010440c0d2540e01d13120f031064100103001c60205000070090042d1f264401d0380102170260101200040d00c5442d00d0150180e40401010300030360360854000020b20030052100c003080a5400c04d528103400603030500070755120b542005c403c44520340c50151910758103002c0058020031412801c10003540c580003800002e00030500080f082d2140e440c2c045000b000c50b1101000b0000d55101101032040680d0700a503501c03001d00c0d082c00d08901 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 397805620 1250 397804370 397804391
    0x91006030c03150f0203070908061515031b0703110d0801050625050a08070b460905012712080601110109060902180702280b01170f030f030a 62
    0x10341495103c00104500000030300c04482d600130400308c101c0e0042c3c82a07850648900c0300b0111103908440d003c99018034102c00c0e811040042000542c0c205148a0305140142c2d0030b80c1a02840b500058401c0c1c01103080c000c0c1ca8500c908041c0072211140d0078602e4501039030740c101400202c460290b40302485004000b0342541c00036449040000714080d4000003102d100059500c3c15603003582c04000c08031851860075002c00d40c00c01250300540010100c406d118200e1801d001112500e0390058021b01c050070040981c002e109450612a4000040c0110004241c0c5a00c000341585564226902e00c85040c04001c07040b40810f4814410351420340c114940fa070751548444004a0b00d036a1000e01c0065554600011034040007013950003190490b200baa8441004d901004c90301403103040803508500560001140d800541d480c3e00041c4c903c01e502c94969100b01c5a041d02c032100c1c0b4140036004007440c5100c1e4a48134022000070012440c44400c500c008525081400d03c8101e214000506440701207610340d2010013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 397806870 1250 397805620 397805663
    0xf0f090109050601091a010807090302010507110d0c050312070305070605040812191109180403050c010606051206031621120e01030605090903070b1005120303091006030c03 76
    0x1e6054100003181c0c0596120380309880100442e5900184c10741c030100b505241075000e1612503104a0564541c07844c0140355400648166126000840c0c414a140c1c0080085554060400100c0750040c56011030a509040c00d0600e40402e00e10134500901e0107209a100003a4840c00f1188000d60002021481362241e1403e0a902d00075446481c0003034410408011420100081e58450010f02600030b00101d4645128500740703105884c1c400d030b0000100603107000f008040600d4580c025100e071503d07600c1d0440201d0b0301c0b402c40c2c0f00c90300200c001490028042c00d0b000d000504c20340d04184128040d003500b08034a49503071108800351040e803030503030241c0c108000000320540d11b1110094012035509009103107004010702c0340d4106000140442c0c0382907400300e8941007416055100d804100001d40c0fa04416071642641040c0c020303c1500103090501010559444003650b40050321020f0300150f81360b0500601760350410300c0c00500380e080c56241c208100702045040f1000c40407a03400601052b0f070801d0180509 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 397808120 1250 397806870 397806881
    0x3010203010b22173a050a18080c030709050c070b070311030f0412020a110d0501020409020d0204030c14030307031d04150602010e031206120f100f140f0f0901 70
    0x880f0030108031303071690b40741c01d008a9070903806003144041e089040c403900342c510390a1100100e08040e4082582003012000d000d2801410020507500b00715204042d0101d001100000a030401d20707051304241c64040650908201070f9000e04064181400300340351820780c60707490f0f000c2c10304080d100c0c030b0500c80440c0d8000d000c0d038421248004056140380d500e1600d180403000741c0700c05880813504890401a00142a440498008001540500c4070301400c941d9904000261410310000e40f800e55082000041100151006011542d03d0040160300d440c95414a00d0022100d50b0215036001c80311400540c03e42c5e0040b0460746600e5150401181c03200c80400ca00f040b62500140080d0058600f1480e004000030800300305040b180568002d1140f040800c81454032030040c80080e5200c200c108011890520b0a080f940701c000402e00d080718008840e4060b1245810440a108a01655204100c404600003401130b2000301085100100d05402c116483c059403034401092601c50949807030106005042c01e401a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 397809370 1250 397808120 397808129
    0x50c010c021c06021c02120103030e0604050915010e0607122d02060f06040605090c07140625030c02100509010b040c110d1b2913060b03010203010b22 66
    0x1050802c4110303140c900300a41c080f4900c554041d01c0502035010041840c021652100d03010540c2c00e00591840d0360030703142041d103d400b0641c013080511000c140c98550030803c0384103402401d0480100e0350418000b4240100c14800c46008410410100700400c3d074400034000c0c052164a0400e0030a405944074103081d900c090141000c40c01442d0b84502001e41c0001d0761400b4090401c0c00e000740340c5902c030821045440d1440b40541000c1c820b0005807403029031780003501074203000302e0740030005140c02e4281c1820803004840c1030b01140b43d81e010901c41b0541c00800b440b2804482e042c20003020780c500c0c002942e28000b40642240d2a0780ba00c001034003030042908a843c01c2d10002d403081c0544d8a03489806800002080303544030851150614035a0040d204810480509005030000054802039072035a08203440104c1402c142c07045140d1405265100800c01644940365455280040818624250080c0c80395842420700c0f9a00500060001c00c1c58481201c0c414001083c840c18a41c8180301400e50f06281c0b40d01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 397810620 1250 397809370 397809409
    0x3030f020715031b050301231903050d0e151606060312030b0906030102091014040e0c0c0615030607030c021c08010e010803030c030705070519080406020705030109050c010c02 77
    0x3902c00e41e4260b04404000244d41c0b01074240383e044000100da20b40024407406c40c1052030041c07100210703c881000d0794440680582001c001e0b03020000380d003a0720b09003a48122410b41c44250090041d0354400200020041d04403103144c041c0016241c0a8180e001c0d08000352041c0c0340080f240030410150781c1c0400c00866100d02c280342d902c000c84002030000c10001404900030b941105c00101a46018400c640d5545d03002442207801c6400d1100440e2034401701540f0982180c410000415002e030340d03840320b80c80740d40003443c22959220f10700d01031400d025010703014031240c1c428440080c03070030740d00403034201d50095003403a00017004440828100d19040307a0300d4282d60340769030501a02001552240005041c1c403240340102d5107a0b6642d0042c03542e0b0384400c45140540000a0011580c2e6900c107100038003c640c001c1085800080880d0b1070300218480d885c40c200ca00c448002001c00a00b41c0503c5032400811049008000039005030311060b884000041081e030401c04c425480404556606203480c0d0701428400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 397811870 1250 397810620 397810649
    0x1b0c03060c090111010608190c0e0108070303030b040504030207050616061508120705030703080c0705032703070803040920040618050607210e13020d0c020c090103030f0207 76
    0x16100c03095841100041c3c0040d035100110103004205010f00000c88240b00000c048080c0542286c0345096001c2a04440a070155140081c1c1d205002015071302905041002c0c1200520710328014044030807070071059004a05082c1008003080e004a481c0c0f0844030700761000341c3e44e801c16883c0e800d84620346a80040045141c51042c4c02020703a43c0280e1800e482c2d9000c200c91a000e140e4138001c40c00d0090b828001e003d42d10401c912000288103a058079040880800c0c02c07420711038155035550841c0c028030810704d01c88450b400441e08101190501c011506800e8004c0c040c554240442e00d80c5a100e01c0c0620b040380d80c0c13242c14641c0040d100c104074442c1008031450f80f80c2c0311a05c42000800c120708406e850450400840c801241900e018000c07110881c1e400034040140d4981c2501801e1704c0c1c004900d17810140201034040305556141c1641d50707070030142c211000594402c82d0075903c0c02110b000c002d84104541c403040000000b52585400e6a05680c0c2509050382c06c1005403c08900d4403a141d0000c828040303501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 397813120 1250 397811870 397811881
    0xf0a090203190c0510051201060e010519020607031a0d02010c02030a0609031116151808011107150903020606010c0609050d0c20150708090904120912081b0c0306 71
    0x306041c0262031003120782110803170b104541280d60307014803488910680d80070001007044902540fa8004101410304115047c41c3c5407484091800020218880c0940c01581c100070030300d649841440814802c41c11141240c0b0a200040b801945000e90000e0601000344d0905056560402444200700d90019007403150300010300d40201a041c0c8030b0020030350782c41031803501a01d844110100704145c030120000c200305281c100000702c0c0c40450150126005850f860b0000c100365400380154100d07070524640e0740e961994149000302c40000e1040d49458494980951840000c0d4085000345d0804800d181c00200d0b004d46003800d1000308038070400200035120390300f035080c030681d048140580c030103028410912146000000c4880c1606045d051a68131084000903002612070040c09000d01c0c900504000d410584080082007503108240c0d0141c1e10282e50202240e0500d60104040000d000b0400e11610702071740c1992441c0e901c0c01501482100019000201d1046c440104420961002c0041c12140d032420305 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 397814370 1250 397813120 397813133
    0xc0306090213050907030203060d1509050f071a030123031f05180d080103030302030c0412080403060501050a1220040f0911011b0803070c02130b04140f0a09020319 72
    0x80f8410345020300c000c000001c21403402882500e125000c00340868402c04220745d079005045c144040691742007980e40081c14040345007001544c400d0015240240101410000c00f50b201c0c0e10110040013001000300300600080903c65031034640c802c02c4000c1c660300c111600001a0070072600702400c0007140041c01c03101c42090005c0e001603000d003030103480126049c528078111640720011008050f011800190040000a00c00ea00440d440b044103243c80741031a8564101598500040c0c01c191034241c2c0100f0288103104162003039600400d400c03a1300490741842c020400034800466080139002c2a14100400360b58030f0f109064410b0300e44010410445c68039a611503000030004100c0984010003030300421480c41d4028400601c0c5140e10f04403502800065170f0f110340443e800100b1071010401110000c1e0b00507141c0c6041003550042d21500030500030b50481c00d12041722200000441941d41c400144101c3cac0b0940c1c0c1a15401c105000b501042d00d040a0001c64a8502c1700340c002090542c6031603851090008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 397815620 1250 397814370 397814407
    0x120601090f0207050615040605030118060f1e02090604050a0e1801231b131509050f042003010b04060e030c090105010f11011b0e1002100c03060902 65
    0x40c54004100c0c0422080c8090200d02404600801e035a00c0304001c07603204000400c2e8500c0300d45008101007200d589550110742034408503080c400703030114902242410082a80a07400b410041040d040040603010a19107404410000a070346e21294001040809515588100c070041c20000e0250704c90266109007600340224211401e4400c0d01e010200310001010602901d49009d4110702c1c00700300c0c400d20f030030720741d01c1c401028200188a03580060b965142c844010041d161403440d241045480d5460007566a03039040e10021200c0c00c00086000c00c1c0266a2603581c000c01d901815100021582c1441c1507010420051f4804001880000310000070008100d4000b00262052540d43d158924880300070705039100400e01c02960300ca04000014080d5520031001c11210b42050324202581541044483d421508000d105030702101c0d0f901c5060050940044030880035400513071351016152030070003000f0340318030a504c54400041c0e20f844c0104250f621940110024000162003150b465103a02c51411101c0d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 397816870 1250 397815620 397815629
    0x307030212160e03151b090d08030402010206090106080717150108070612050f0f040206070f030e04050c0a0c0803090a230601050d08090409290f0a110d09050c120601 73
    0x89225803110051300340030030860042104405c541c00540c440d00101c00005115001c07203480144203201216403503507084480702910780214412540c0307003464000241070803001004450641e05108080140000010703d01080392051a041e00030001903801d150304041540c9021144100403130004128180e0205240d401c60310f45440d82103543c0c5002a180c801d58004403514481c2414000000f0b0500c07406010103580584000c0c0418540b6440d5900d0f4030710035071002000c0d8001289800d080d041d5092038441c0c036030020140c11002307090940064008181c0340d00d4890090a01c40b0110125030900002c00c50841480da02401c51420028102a07051031044070300000291880740800028203400d04104625603d90405240c52074814840c0900000d003081410840c0d0044510340c3c655440d441c9485a001c030f40700780c501e0000c03550070310581101e00301d907002d825030020b6840c00e05045958420b2000300d500b48515180085241c080c0c45c1002400c01a40765a0140c0100c1104c00d0381404000105406050300c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 397818120 1250 397816870 397816877
    0x303062d080705031902010c02090f040219030203030a0c0c05061b060c0a02031e040509010806072c09041b17070909081606060512010b1c0203070605030703021216 72
    0x10303a92082201d80e1450329210b082d40503002040451055041c04809108450060401400c040c43c00da0105900103c1141c50744d0740d080c000000e00c001c61030540b0100408000004c85103140c3340c03e640000f83c6a12a0003035250900c05507105400412070920800c0c001840010590b54070f800d40c040061b003030101c680c03112610034040d02d00011140b11040061310852411940250b0401e05441d0302400360380d8a110030078120201c14000002e9958a518003140a000d5442c050092414120300242107030f8031080b141e00c0e1421481d43c05c43c58000907480d1280148200715030b01c8025440e1414100f8115076940350341c0c108041c064030081640307d4000e0040750216000c10856003080e64810f440000c0320344052000303140c0281044240400710b03104003001aa02d00890f00003407250f9441000401d420200c11094013543d440784410200c1c0c0c0f409403201340004251342140009254554000380d142d44c602c0c00380009010021010400301072080d0b060720f8103c0171102181100d4102a49800300c406800740518000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 397819370 1250 397818120 397818209
    0x7091802030115060c12140409140708220212030313030906020a020303040e19061806050901080c0105160f030e09010504201c1407200307060207030306 67
    0x81541c5143c1881240d44640d2103075a4a44165240b501e441c0e14929040104101024043e1146283c41d00500052007561000511950550030b4491480401818041401200c80810441e0218032020400c1d10f003845524510290852000400040d10b89904244a21010040100840051000010742030080c1c594807182c0ba900c820803a0789a000300c10007500340c1c205210822a0703400c0900035a800c401040c80c40c60f4140100c1c3d613070000310f46880e07020120701e05007540310180f134910314071801003c1d003400c0e83c1c032807040d41c1004c40d004d0f6034505241d5000d04116002500183c0090800b22110070303154003c11044941f510b506000f020089980811407203140600000560b52410344076810140070314007030070003041000390644036079900f004525180078142045030030540d82d000d00c58100c401c5613071940c156580c1040c802c0204581d2403403501002c4550503074264403403a00000251008a075103c007026a903108030307240881c050b04d0300d0340c0400e440c19144696412080c000e2201d0103240608085103416 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 397820620 1250 397819370 397819391
    0x70b091206151c082101050d02180a23070f0302190c140709060e0a090b1f0b0406030e010507030c0c02091308040b04060f0201050411010809070918020301 68
    0x45440301950030000304695020b09101c80d0034a18000104070b200851083c40355840368030782d030009500082c0341050410000407030030035aa110600c114094401680c454103845901d80c003140540d13060b80443c03034180140000140d02e0102e00e030056900246841140e0340500c40452900041302c1054820301d0104640305c40c4807078441d20910a803554080800c03200090104880743c180d401c140c0394107068a40c084911035034880c05001b0070516009042c0f02c0030009116140c0103e1900c07210700504010740c0c0a00700485080070426544031103030840700c01003040724100c0c001904201140d009a00c080000c400200b0300059240c0c05500005600d010b0000074842035541080403011070b9405081c0c1c0004c24040d03001c84002d030030304901040d4171000d00c410039842400303907071074080346071708141c1c08010403100c0040d003030101300e50008442d0700c404181c0c0000d1149040a903150f501c10184644074070304004102d03000a0303181ea010800c210041c0244a800c1282c443e00580c20343c4841000e20080e0700943c00c0c5291001e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 397821870 1250 397820620 397820623
    0x309060203030606031302030a0b070c03020105090705100f030e190203010c11060c0702011101090f12020d080f04050102131e05120303010501030207050307291f03021011070b0912 79
    0xa200f01c50052055180d036889440101c030f1140101d00503a05842218402c4001540c8828414018032550f01d500b4043c0c00c55140090a4901c0182481d039260000b410801180d22002e02e001c01619031414191040c0618040480c000c100c0846014440d2240842e070000003072103e034200c0c1c40f1038001c0c0e0080c409012012030944400301d00c0301412003680d10220008900554078005001e200b80705140c0b01d0400e00c601c50601d400c0d204100c1c41a5080f80008400e1400c000074801c06080901150015001121110300050a040b800410115a00e80300d0300004040000a6040760a09440803130b11044558441c0c80c20890349645034180c0c2c00c100c91503640403586250103801c1d404068246001545541e00740b800450294004240403a40c80c0710902400c1e0004641b11a0b07030722084000c116003001e6060b00ba04d008102200a0304480f020070703000b00a1150381d4050110601503d0701512a0752010301c000d001118603051041d0000550b0207004c5000c10007101c5100144002d22007110300351b1050260801e200d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 397823120 1250 397821870 397821877
    0xb03120703172d0901020409091406010608090705090c04080313080f070e010311220207050c0612040b18030c03030604150503070e090307080a0f110c030a3c0309060203 74
    0x100f80c0381090182c242c46640b005941c0c41e40c44804a0000750030a50340b45403500039a888503008440c20808003002c2c254846081113001d005007654a841c40c540e0414010f940e8645103070740610360103403400740002400c1802180440780100b2842044907a40c402e810301d100303040c044c1703402010924003070418000c807c1c0c140001c00c801640c00c0c10b140d155031307a4a0341c4c0e501000a00414100b07a04403004107150b1405152903d000c1c402c00b81c40981c0540ea80c0076500c0d2080c203102d80300302c103580716010030311010100b40d08420540740d00940c4001840140d84502141d101e0b050035120700603681d44000945905180004805580100070560b020b0041c25044801c1e0907000c0381070700130b454050f44085410400d100917650044d40060b03403041500c2c549210b80d165103405500030019a00460f14021403a01c0d9150b001781d82a01240340e0001800c0551030040000f9110540441c0c0070b8544985030026103100000d21100c1c0c2c030300d008100701c81d40c11002c001d84940606a491001030300880e03042e004c002551130000c01117 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 397824370 1250 397823120 397823161
    0x1f080609011d06041808040905100f03020d061d010b011214060108041713170f03090d1e03020c090703061401050c0307020d061a0103110d0b0312070317 67
    0x5001c000c00300e042d1151008403006003080c4d070081c0c503101c0041c01801070034000c170a43c501840c03401d40e487d804c0c00f586500307030340c0007500c411112101e100041000e45d4440c200101600d0303044a2403038002c20b031410300c60050904010f2008106008041098040005600c0100c90140a0b00d0703600b6108594800e95040b601d4000300d103002c0d142a82e0011383c0b10b610034403105a02c14481d034a0b042c1d03905000511300300540c108d884d01e0020a0300310f2106004e42015401d074800403c0d4000000c201411201c481103850380a90060140180c5c00068064100001080a2071304030f41c46c0d580075001d803882030400a5441d40b0180c00340e4002c281380408940d01c184079008800954000004540d20980d401c0011115a4042d80c42682c450005210080060340d5115200480501405012502c017003d881000134814a55003281d041c940340107031140c94144843c044d103c500048440001c2d4485007900824106071640c21080c00344400028401c08141e084803a12446080750805102c00356a1481440c4202200060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 397825620 1250 397824370 397824389
    0x60c09040c0909062306090a18020c0303250513050108060429011202070510110c0d0215070f27120609020f010201020901050f09040b1f08060901 64
    0x420409041503041140784480502e06854016500e80e404802c481541c0c200c800c0d001001c2154440d480c00032241c00722105401c556091620f4121070000f403922a1900c200d00c16075100c0c00500c944c13800f00d80e040c1c6040c401408160b1703540b441c0c0a0056804500d40f1004460240402062500c110f40310740c040d5030548100100c80301d421400e01006403800a001460300b54081c0e22507283c400750103484441614000c0b08118410900700c4840005440340801503c100703206841030000a0200340700013040361068140c03c01c0054542070340a10440070784100c40303002400784244000440c0c132a90001d441010740c2501104e0480540301e0303000445001600207000c1c000a00f44644244000314134000440a001d001d100d1042541d80d206480d4031441001c0c801922480e503034094240c00d508051500b901c00c05170074402141b13006204030000e0118040c1c02d501890390f10001c00d4008446d266503004082455001f0008040080c11301c008840f5480c10303200410000d80d4203400300e0818104801e00c00d05889443d00b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 397826870 1250 397825620 397825627
    0x10812040806011404020d020406020607120e100f0f1806060f03030507030807020a06051509010902040609030807030e0a0b190c02150a0314010b190c032a32060c 71
    0x407030100b424190382e056641c410341c00c0000d11071f600d03442e01c010b00040480d80c0241c02d040c1b0300f0b8100980040c000308aa5180241041c200c0240200041010030742e18554150014018503a45074032002403801407900e4100e40e140411154490104611514410748034040a02039240c8611480c1c0700301100e44001004102c05011140006e030044201c242d02c10303414411285140c0c41034403400180c40050740c071b952007021211002841801c02088060141c0107407001580382601d4150010910200d611003e02180b2011a6400406210b004001c66040c0018100d00e40c803500c981d50881264000c40c90380d0f91071301000da0b051510b03600030300500c00a241c009000b01000f10144d400e4510a60150a040e0304140e0340781c06602c4540409114035019003451000c3c240c590404251610300200000c0c0c0c10020f01c90000c0210b00001c2d401040e03202c046882c01c51000f04101000500e158001a0a90040c034060480c400c950b48207070758400904000c0f02c0d061915082000a00b41d80303464160580314160b5000040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 397828120 1250 397826870 397826879
    0x150901080c010c2a0e06040f0209100c140111090f0928020906030901020d050603190201140409020a031509020414060a09120308090c010503060102210d0207050601081204080601 78
    0x1801e011403100c202c2484042408203850010703011244036000b02c416042c0341410b00c8264206441008c0d810b400c01401107250490200002d01c0c0b40d071040a10000b08074981180108002da200d0b210251154018000d01171900001c01d4400396070040e1203103a001d002040d80320301080c03508050315801040352540c0c2000070300381480d12815504421104000b015001c03c04a01c160322028001d610481e0b04800040e22408020a401c050f0b400192140f071180c7d110340c25240080100b0f4071901440f5a0900341138101041e80e1946041500480c1e1007007814620101d00f0501c69601a0080c41c2c180d04444802c00c0d400713803603d81103000c0340103501642100276104001410242080d0004000880c1c1d00d042102034142d0711038500d00c080180f5541140010b1151062000b216000c1103c00b8100100b4203000f400d40ca0700c0310000f0b5880d1b4040603141c25050f00b80b08240c100d02003010880d0f00031128064190341e00d140f40e05149a407100c1c00c1c42442894440c5d40070341d040c07089480003503c0c141c80400d000f40c803960340392 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 397829370 1250 397828120 397828133
    0x3020906030907060215161202090a0303200d170a1d15160e0103090503040504050c070c0b09010827030f1803070b04030803040602040f090603061406100c030512150901080c010c 78
    0x1008d210b024819030801074800c0a0340c035101441c0007140309588026100d01020000480a00000410039040e40800c81c404030040e08081c8024848160200b090303169500c03108140040c1400342e50a440d44103528900440ca1140032420907501c4251200032480c540328074802c1541508490400e00010728906400d461943c0301c3e03005205038a0241d0222801c1603103620002d1704495040d030741c10500c0100042d0b4201008042002c840c0203120f203c10b90307410246000006008a0790040c04142ca03c12880390101500350500c0060400d030350843c04403512610200c001207a141d11203e5140744800c045080304140c4d14001852078250360b1039070780c0036041514590750780d0702e980c20150044801c00d400340404940300c0483c40368100100300340744000c58440e1641c100803044a5042d480328400c3c00090041240d251100d0384581c4040b1803614181c04020f802e410202c6040c059aa40a4a240081420701030000100003014001003011180f20020741d0f0380d1100141c1d0b86d04080511408030b01100180004100b5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 397830620 1250 397829370 397829387
    0x402010e1212210a020915090102070303030e03070c0305030c0705030a02060702040507140c01061a0a090506030c070609061401080706080f07090b0a0309030801090b03100c0302090603090706021516 87
    0x24840c1404030a115120f0b20030b079801c41202c41c103011903800f042c00170043c03130051440d0310010b081d803d58624080380703440000e458130101c0c00090141901c03000344044590b02001124184c1c0c1d00a952045801d03140e00d1318685960162141d4070452103140400f254034034010480403405603005240341d180202c0f42d400d100140c04c0080600c400c0c89082e550700032079280c03100014500500380031700005241307050035480c0640022130030090205040074800c0c4c02c02150014030700010380307004a8216881e550355540343e046d54800d0798401014581003a010100704020b03a0410507a1200340c840b107442d503a07220440d8030381d100700a103d510002150b000200d1040070741c0c040b0541d000043c5103440041d450321406006140d90000041c00002507031800b40d40207050b4000034490150030901e405001d4440305100090b5519000c0d0300b0070043c00d503100c00c01c00c5450300a81c1290f510700c2d400380c41240c492a00990068540070240b0581000d0b000300390ba52039800c81c0c03010401c1c0c410a40400090a0700301d00301c40c21620b292 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 397831870 1250 397830620 397830637
    0x1413140d0e01080106030e1e011e060806160c08032203020616021902060f0d06180b0d020607120e060d0e210a080c04050a0605030402010e1212 63
    0x181912450009648244440350119265032103088250000d14001001e16005034403240816162a03c1e02807450000f04110107110003178116103030380d026101400f13401441c55116040010450b815504801c030559007000046850f41401d8402c150f881018074514420ba2980d40310005014003802c8001803103030805150800b03011040c1a4512604854070380251840e1142680582d0200040020040031b10702c3d86d44600c200e901c050a04802c80d00b400d01c981044209000f40b1841d000701312040400c0511040d40c1031080301800a105540e900c607080c081844098011040050a10601c002e8500b1b00d0145c02c0c6c540b50f4050040741c0b8100c1940c0705d0b14a00c1c060001044100814064003001555905000d41040b803807482000804d94880313021145448440074052a00c1c500c0c0540f1080c021071108141c0e5003a80d12401c03c1612940d840c0742040d4244100d411103907120001e11030100d81c0c56404000b851145202782c0f1401c0c003005000c0204403c1d0250021a0340055026a40c100e1500308500003810311030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 397833120 1250 397831870 397831883
    0x12060b0307030b04050d0c020a1502010b040c0f020f03070308040b0405010e12090a12020d031407080a020d080a05060f010f0201330e010b04050910080a0f14011413 72
    0x1000094006400c1022652080d60800740034030511040c4041171100d110b4010480c20f004100c3c0800d540401c415204d0783c85000c060403442aa0700092a00031342101084090052040050310f083d9000901400c05021001006100d0700c214500b00080010403202c4403a0107458a42d119510340d60740ca4810390000780110380030754071000c0c000d000715010002d40c01c1503250484181d465003014001d0148403000d652080641e004420301700400358942e031700f800120341c1d098609038400c59400c02114039244164000100000000034000000642c0400c2d6811201010703901e5010319180c10310f0060a50b142920201e50080c510085500f0075806500c0040f03042c00f00b40000309030b412990000840361440507009100001d11402072401d4030100380241c07009040130004641a0394101080402e40f0f00480c002c0900a4800c0c40100d0094098820040d00810481e02103c440202a1910741610000a441140e20350400f00c01d94103800410b002d0700c070180032050082700381030b0f88443c1c410100340d0102c14180e0300c6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 397834370 1250 397833120 397833131
    0x607021206040c05040b0123250303140604020705101e140f0a0504050d03050709030f0503090307090e0a0201051b03070305040e09011413150501181b05041206 70
    0x900090041038800e0303000300580c44116184c03505101c15102c560000c40d04110407520200c0d1300303214000c0d18403030751035601c4960350b20746814001c208450014080181d02c00c2054400d40c404040d40742c0c00070410315054003588105910344c0e4017400f003a07014242c4014003075002901d0b1544000c58540c04040b0f1109a080b00041d8042100400b9040701d040d910b80c101d034201e5440421a00d2102112225044441060200041c4c80c141d01c03440c1c3c40c1c05841d60a03000f011349507408034a0580c8100d04000c0a107070000c2c40801e03110281d240c416502da1203010303a603000e40a000c0e400100b0b0a403522613521021410000740400c90f0140d07004441640c8400040b180441c80d0105116000c0001c0010f0415180f2071748645650b2410f10000b030301ca00c28010400101c5a0528043c0c08860f04203021058000354500101c03005c0d81181d280a1804540d010000c40100e071500c400082c030324108110301c00b180c081e662004c2001042c0d003010401c4245950540c8030100d48d0401080080804a4040c010f040f8007650300041c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 397835620 1250 397834370 397834399
    0x2070606090e0a020301060509012103110d0309140d020304093b10060503030a08190c0345080d0204090f0f0506090402010509010c0501090c0618060509060702 70
    0x80715004400d10800342d01c40b43d0803a045003401d00c03c035801340404039a09085585019408824504002400d00c001c01c6094072100815000305d440c00390101000051320010240030074003c1c0200a4128152040c3c8143c600700c2c2d90a03000441c4001000e880366001d18982802d089841001d89407003516101608a11101c03110002440d10004150700c0b40c1c0e049041c4800713901c261703507484c0024000c0c405840c180b41c6841040706503800800ca0700d00a01ca400c0c07203800e40d03a584020118214030900400111801d01020000036a4154003590041d262000704d40d800f412441c0840021a00c00000911100090240048400c07599041004540e1003000020700c0c01050b41c01c000140e8003d903104131401a01c03104d9003c50604075000c0d04030040300d414400c200c40d107000c0300040d00f104406007000c1d050010008003241c65921a80d07600d0038103604800280482c46080c94a5440702d01c86110345000580841c0341942c00c584140031120849031250748440c02e1540840402c10954442c90707040364000b08115801d01c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 397836870 1250 397835620 397835639
    0xa020d08130c0308132c04030302040b03150310023903070311240a0b121b0f0a03020102070b0a051309090606080303061804080d1d0d0e09070302070606 67
    0x1d0145108001341a01e8282d001030380100c580301d9411581120014001c2071800b48a940040f5100020040e2183d40a403070354142900244140c1e008046030100000411880314408904100080d109070b0031111020b6804201e64201d00494000301140011680e41c0030981c05850303142c0310803081074501610720000050605185034007419003200071864510003211550018880e092803103070b42000003002e01c010a036210202140041c40c03201360f140d9039258440a921258105065080068125800141c00721050361546602600c81445802032190148250412101074030880e603060300200000da06180d0320000540041ea403000400005002222200c5111074000000b010381840024800300d1034100103041c0d0388540c0083c03042e5030003081808034544500740300d0302c40e0040c3c2281281d80ca8403240341c17a003018803034090501031141c00c16007410b000303404c800d02e6050404840740441d04652300f81182aa01d05442110311030b4815082400541607030f010360010034116101d9200014910703207642099 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 397838120 1250 397836870 397836893
    0x5040902030c1b1b011e03020a120c0e030118390f03030e030706050406030e030d020301030302060f01080105090601030308070519050c0d0e030606040e03070602070809150a020d0813 80
    0x200d03043c0d10119480058103491301d1072031100b000c02e10346441c590340c50103042030168110750355641c200f5a000480f25000c074840c01038006211110764081c4441d408800d00103001d0030100980c18400d51818402c103c03d1804404200c1609511050140c0d0502030741046000d400c10f0510206001c140d8040401140700100c001071010b050f039034507130008640c1507080c018500910910141d000c0d512500041c40b5068000c0b0a84048800500d0301040d4108540b81443c00c5004844110420070b0012001108051300481c44901c10650000022110703aa5004071600780c0310b080d140410350f6040100144003091007050003680c44099410594500b10482c0704109a101802c8a94000628049010815298140300e003030800c070b00528004985d2101140026203072000074141500c55075640584200b0010107000781c40c0c02c1c0d6000242191070b00480c3c1803203e40ca900031550f103842880c1101c2120f014046120a503082101d0350b034018a10885070300d40c1603880f0100542000800c1102085120000d410103041d07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 397839370 1250 397838120 397838167
    0x209071205090a0b010b09030a0b06030f0f07170d08160c05100504030f0507022206180204080d03020a0e010e041d0a0209070801030b0403030c12090f0b0a050705040902030c 76
    0x1d00894045003001130b072050041e0081072050360104202d00d00d5545c00103001e0781a5402c050010050786600b80000c0c50110003100228980c0110494004000804203814040b544200400c04101c4040c80d101519250303030400000101c0c03824000719441c510065902000c040e040d0800341d031209040d4594900d408501040341900d15100c01c200800c040e13004258141842c81d604015080104990001e541d006840d01c000002c0c2004011a0150344c4054102c54002c1810b801d240c01c42c901c1a01d04a4041d507c180035450b16841140c00c500080e612030300c01c540c20443c195a61600d40c0b6010401120302c060000f030400c1e40207403030f0340c0f00a01e40424034001810243c4078800808100e002c038410300442c0b4800130b040c0020301040000400c00f1030710800c0d0b00303a4425131528001680025008003a902649500681e09846290200c440b003040a1070b9101003031107000e02d03d40d145959404040c001a150212000707000541305201c01c01400025402958004682c0424581004c9107070f180c0c085da02403042403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 397840620 1250 397839370 397839373
    0x6030c1418090a0b060f0409050a050d08070e0409020f060c07050112020304050c120a050a230105010510050901050f0d021b060906042a090c031116020907120509 71
    0x8015468801d00d110110310050403030740c819160680d05581c984031000c00160050351101c2c0001c01c03698070b014822030542001442044216014140706076205201e0704115010710034510130001440c080e260300d901c5003105540e003030729800010050002403c3c0f400e1041742c010f165840702c080c071a581c10028181c031030280c40041061510300700004000010550711803203120310410620020400100c0c0c10741705500241d41ea06013030112003142d1031510300c40000140c001e000e511001410401d030911039106404007580c4500100010101032800c0300c03c20f200380c551151030403680c12069030262003d0180030f0814101b41d400c2c1800720f03841ca01039500402000030002e500050850304421000c14041d4045105401000a480d024812541d201c1c009040078080a82000308504c0076104040480ea201804061821003c1e5131205040b0240540300f2050002c2030074021001c00180c80c6109441c117200c1940480f41c0c80d03100310b800744481d80c00d01800f0b20007000710000015102a9480c01032601400d907240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 397841726 1106 397840620 397840649
    0x604020d0305071a09190b27010c030204171c180f1401030e030a0804020105032205150a0b03070911130f05010909060b0904052a030405070b030f0403030b0406030c 72
    0x710f01e88c0b8030740c20900d8a8045941c590080c108499440600c0404220b07400038068480034441c0e01d545c42043c1c03411034510a40d10400c1c0c0141030316000c3c0180700740c2d117031141c903000e80303106164000700d160b0076072400d40220369641407045c403007400c05010141d03003803079040500200700c40e10140020341080740220119030341c031141c07680310040208205144030240140d49440b80c2c645903031605100c95403211000140300b4080502510714080b100030042c0010034100744080004049016242210070f805100454100b024136403110041c29221300c00c02c0643e850400010201100d80c2c204190460500c60200f03c42c10707000302981c050300021500820680e85a101d20080c140482603002c103c100c000c0100d04100d02c030940214001c901a400b940d455588505d1219000d102c00d40b001011807264500003000b0911035030150707807002c40082001c1140d84d500c0d103804000001e00c0e0082885a0481d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 397661870 397841726 := by
  have h0 := BRFrame.cov_init 397661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 397661870 ≤ n) (h2 : n < 397841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
