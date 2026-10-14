-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1215
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:48:32.935547+00:00
-- url     : https://prove2.me/submissions/a84e3743-4c60-490b-88a4-234caceb89bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 218345323 ≤ n < 218525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 218346573 1250 218345323 218345341
    0x6060c0f02030c0616050d08072c04110403021219120e10030b0103050f010e071b080a02010c02070b04140904050c0424050306040b0f070507120c1118 66
    0x21000c0072a094030504810074001c0e5924400391010014000c1c120501030f82501d48035091090380e080724818003c3c5002488000741e0007041e2003101840e1058200002e010301000b000e443c4070f0b061a442e42162410182096070345da42002402503c0c0280c9545c200201c0c9004000c0e070320000b0b491040e29141200746d81600003040c042004400010030b20f000e403001003d8000284040d0311001c0c0044c046a43c540704142c00d540c05002d0b0581c01483c802007005290300d80341d407089251100030b001104004c114150704a00d2051400c0303801d41107170400c12882e241e001c0700d01c0180c0209080f000030720240c4654000028a41e1116044405540e0940303849810038142030103100c400c100281c8120b4290040c084040103907150392181c0584030780f074825141a0740301d981c0c10040c3c404002e50042400382d00044100004191966591a0004031000300700c02181c4c0e07501811165801980c20003040e0003004043c0c0800b55601110021109016100902d0070000c00020002a03602c2c80341201700c1ea116601c00600090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 218347823 1250 218346573 218346593
    0x18241f050c01060e1006030b01140c150f01030b092e0605042a03090305162307081605030a020d15090f17070b0f0901090b0108010911030106060c 64
    0x103091460419000d448202d0940380e06800c55405040d81e102000041688001d4820091415040800128141200080c0106901c030740e4106580d60004011898807010844031030301288a0480710114140380003d900c00b03200a200071744504521501050f041b1102248080800c810006852826030b4040c21508070440584e038100e00156070b07000002940d8403640901540356440e00c110414290850200304070a20b03220303000c0010980382c07010240c0040c1e00842164407054400c0302c4084404000d01c0c040b44942c5c6107000b184140c00c19100d66110340c500c00503c0d503054400100986003401e01c58017042c94546200d10904e0385c1548a0080d1901500b405a0b191718824000c0b180f044030800b607502c0440650300d0000003214001d40d04000c100a220401c2c0244400c4100100620301d1310b5920b0f02e42529640380a4240b0003501c0350b80010400c0a0030035032025680b01c0e48003401041660751621014001e040e035031000c0d1080030039a48403910174903040c0318403029240301e034855039681e0f040c40e12800300c2a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 218349073 1250 218347823 218347879
    0x9150c0f1d040c030c0f05090f0405042a031101050702150313080a180f0f030b0a0e060f04231c0201090c1401090806010302010e0d0f021824 62
    0x8408480030070403080d250707405400d9164206403808580c009800c0c0c4002e02082101e02e4510800c0380c184010b81e00c40c0c1c3c8088015104007401c85022845444600740f0803516070f074544025200141c05c00340c5040c10740e1403202100c1201d0040c68040c50f0715602400644051144120017035015a01841070184008803001171500f10480100c9144e0040c620f580d240350380d500504615020401116818a11a10b420200b401a00d55604881a05d40c85d000e00119020322303d0100034080c00382d42e070019009502681c819141a0032000031100d01d07090181e515005004281c8007a01d841d101c90501e2030f081c0240481041d1031140c024000c10741300a0710028040c1100c94116404215500d1713000001c08903004a0900026144004c8500740d40c094100c000341c1510311582c44040c1540040004101503a08042503248901040e558031020010614001d4429445814000d40c881d618411a10000c1c20741c0a605d44a030300c034180c1045400c0130b02c012480342c0d01180a9019400119121800e000200640d051884 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 218350323 1250 218349073 218349107
    0x414040504050114010603150f0b04060311070c2c0712050c1e0d05010522020a050f161101090806060d052107151424030a0609150c0f 59
    0x25075001466102813645084e8051400030703845100142125408220520041034221012860b10745801c3e00c84000b4011072091030103041d6034807988051140250101d4072034a40c4000d000300015140d0102c0c0c483e60341c0749007414003060030512142501c0b4145200d560301a130b03026140c01e4101016885c030007014000007000c1045d242400c0c40030180b500c03032900e0011003e910030103400b620b6040404841c400c03101c0c16442548548201070410310341d0380504005505485002e0400b5070b0311118413a040e555841906480a150710000584401c02038040700d0841c010b80c807546550913038180c1040119202d2401e0301440c1207035007000000c03500b10319002c441001030074404d01c01e445070503000411080e89140c0c980750510000000103035050030042054500c079400d03426100101711400500b0703c50200c0705401041e02001c4103403840c0780b04408a10889500003004002d044070b107130a40c10714001000d050001c0003111303441449070b64440303808442c0c000e258044280b903940b1014400d00c10801c0399501801480054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 218351573 1250 218350323 218350331
    0x1808121801020a020606091302060708181206040201120b030712150510030b0f07051801020109020604090903090b040501050a0518030105160809120d0c12050f010e070504140405040501 81
    0xc2000300c02c1c00a000d0030141d80c1c000d06070070318164090004d00c40c0014200c00d810070441480c0c80050b503660303003511280754000b50340c0c0d900d035403005189502e54000c1c40f0f64036501440303442a001d100ea40014009100c0c1d4402e0303070780480d074016410701e8205442d100400140d154009040c00e00c40d002403040130b080418000e80300c01100164014582e01100c0050b9145d04c01459040c4040c8140104d524240750005034025403c00d55140410700140f881c000c0c0d00b09607041065000c81070740903a200b5003040c003801e5001480242c1c0c0303598443d604802000c0400d0b04802080c200400001c0c00740345601079404460040e102d261620b102070000300c039254046c07840d021392a01c0d801c01b040721944007403003854840c07482083d4011441800c3e003409400311400a0540c2081da00c010300e148059405141900d145651108001ca01c194901c9000e455801c1e440042c00245481c02d01000b613120051800c4a04841c0c450205424039202d00130211818030581c0601d940c40d181c660201e203003a00303299001c580d0007801000009 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 218352823 1250 218351573 218351611
    0x903011d010207170304050606040b031c020d110102041206090c170a02040f020c0c06090103021e0a0e090106080c03040f0f03020c030c180109021305090a020d180812 73
    0xd84100c40541800a003a076000c100c42040040030b0b40344000341c038098000241945080e5940d40d075a0f600040400b070040c2d4490001c5103103510208102d0200c003905840303400200d202140000c0d42e03003481c8690038000030340390281e50304034040c1842120150b5401e40c013180600c00303e51300e42e80007a0050903001c5540442680c8001058542d5030f000420300354030600503100c540941e00402003a28007000c200000b991040182d01110b50000030001c15410f0143c800c1c81e110211100168001e0140c1c500d40d042d8200c2c0c8103845050f40d045980188540c4036143c840c008000080c00620200315024010352004c00c54030030220b12403440030000b640c1c1c0b0901ca03080c1c0041c0c0480c140c0d110502032111541c12000360b0b02446d03880c80350303182c2805203038003a040c00d440c815070010250390641e81246c411301c942072840da4006812001c04280421010247c10050003400302810507501c0706000b58045a0941205403400790944107400c802c011f101c592540100a041c01c0001c0311640740f007607640290124003800c005150b170f8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 218354073 1250 218352823 218352851
    0xc0e0d1e0807060b0f04060e04060504110a081c021c0804171206090115020a02120a021906080f0705040501050d0f0507170906060120010e0a140f01150902090301 71
    0x102019845000e01007140b030802d00611000005c03180d01581720b1130405005001031540104030a034001c0c2c0060000c40c80380c8a03410075006841644803859001828102c001c00d60940018003901c4040c4552401c440e00c070440c0e80101d8070758038451240341c2022089004100510300ca41c28040c2c03c9030060a0b011040d9503040c0c0b60149c2d41e400702800e03160228481040004034a8003040003401000030980d01ca074501c3e1407074070080d207a09181c00e000b845004003d44040c00000d0411641c10f0340d50340542521b41901508c2125800c0a60303a200749400600b40c01d00042001c06030202050044003d070300c03107600b45400c1500546003500085401c0302d41c00e598600c00c90306221039000351070040100d912516031200340319201c0d07004101300800c0c940c440c0c0e201c2000d1001c60390740000070300000790040b41c50404107603d041d0801d024001c03407288a54284285202c100c00d00000400345018501980210352492440350f03103090076100c8081e4140e01e03d1114441c204501041d54000706502c20004000258101c0507001c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 218355323 1250 218354073 218354077
    0x90301050f07031a1005180d0807021207060801030809011710050307050406030506060103020f130b0d0608061605030a0b0312070b010509040b0a02070602040312020a060c0e0d1e08 79
    0x21000101220400340282c440e05031203040b90507450b240515050f81c1c40d00c8003141c2d642c00303407080c03200412a0000741ca01c400b00080404070300d5004010b0440d28180d140381051002c3e500200f606a1007900b10b03c43c51065120700054540c2144c0c0c06460300a250f80ca161030722007507504500d4600f030500c102c2500249a003058808114410a0b0001c105150a81007401785440e01341c0c40e400036805603180140910114400083d44c650205092a01690b1441d03009440100c1e80100c00030503900101100340422100030314406440a915091030030010199200c002076039604007a1003040d03000208040560301c1e00e108400841e40840080000b066101d001030100f4505894501c0c40460024041042410044001d81040c0185021203064842c0e04064941c0319040a01034099601175600140031003c0005503010b0310019900482000d05000569a019442d403103d08411201c0e54a405400c0d0325807800340d508030308054400742045803580c0656491440882900840c96400346a82040170005445000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 218356573 1250 218355323 218355331
    0x20f060a030e120a1706030118060605040f18030c0816050609060703050603030418060506040303080f090d020c12070e07090e060a15051e0d060e06150306011409030105 74
    0x16000910800302001c0d10704080300f060000d80c020364200302003c6a140c0c031043d140c034030114840030701d0900e03254040080d005202401000c0300b40c180c0301e00d64a05100340303544a0703022910255421711a400390201503d04941c151841c1441c2d005e41c1d20b00341d5011030312400714048840d1068400a180843c240c00740c0060001c007610455043d0302020410070b072100d040c071019801905030300f01404203003040030000e40c07207001d6405002c850520140d0000c04020b8603410440083c070010f44100c2d40d03030b516810000c02d108411180b003200c411742440451030b0200c000907000c1d1240c40f80d90140000ca41171804101e0521404078902446204184010500781c90818015005540a80b90340f1042803420b01c1c070007141540244201e2082040c400100018804011020b880905900e0146e40c0c80800e503c0c510461001a180030205d4240881c61618040066000d5003d40c0c550012070740c4680c1d0303031108021450240001c3d2082c198070502c042075095020396184540c064100b00f1850074003200c0b0b4042401c54a04032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 218357823 1250 218356573 218356577
    0x9030b010b1b2a030a020a05010c03092301020d0806030d050c030702100c1406010f0b0d02160501060810050606070602030705070b070c021c0f0b0702010225060c1e0507020f060a 78
    0x6481d0480f80306280e82c000e5480b0f2043c1d026090420540e0005001c04041c1d115190500803021500010544030704010000303441145050400c07084110f09a40c066148802d0460140c400c140c504000c0500501d40140301e404014000e0241e101c42103000c945581001d8543e09a910050058074016503481c0400d40d0350083c140c2d5502080c091070300348890a80c07520651300045d42c000500500000e45c0340301415059480140c02141d80b01c1408041800074407034650b010041d041c02d00030400c10800190403040845c4d240340112a0808450800719044803c190760195100104012400c0061066006142d0241c02814070300d0410f0388a884d81040140c0454002002400c0c05d4804400c40c501074844d01c0b00f41c41030081815079042c03140d4422500121201c005010204c40400140c0420301c01d404079451003100052002c1c5491800520044694000301e00b2071701581400d03030054207284181c1108507034003d403d5108065030340c4918207640c15071025009980188508442210310b4440400505044401d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 218359073 1250 218357823 218357863
    0xb180103060b04140106020a030507020a09052802040506041403010b030601060c0b1b0d0510050a09090c0603020306060406120f020f09010305010504020a170c070c1d0709030b010b1b 80
    0x4408002c02c483d040c10040242400c0302c4c00511040b64001808002d56525080c200c0e0703a0744482c0006450403a180c1d0040c0300715403c0038104a8030350901d9600d103944c402c070310505080c0000c18000800aa02480c090706030401d0040c0400c2004980352050305507100300280000907594020300100e82882800d1f0445070101d0709a11080382080341e0130740c1e1154002300b07032781c50208101d03003c2d8044081c03841119240b074079264690000c286e401e0101d04800006050080c07400024580d1400701e0b001400c004503003a0380111a200d000901c5078002e00131607108040013006a494141005400d0303c484207030300301502c1c09950700c40c9030048002992006040c0c0d5404203081c02c0d1503064210005095400c142c015600a50060200da03424a4122903884000d0204680c1c09a490f03640750340d000e00070b00176010090105484148000780c1801449550000d000846a00790015980e114050302c8161643c80009c15100410004000700c1c0f4040019207043c3c4910346070f240540a86140e11403800f0304006600300d60020b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 218360323 1250 218359073 218359091
    0xf060617060103110a050108070e2b0c08070608040b07020f011104051207060806040b010509041817031003110d060c03022a0a060e1207030305040b0105010c11040b18010306 76
    0x809155480c488030841e001752a031818503000a198103006072140c01440580b164114083d43c50108d10740e9403600b803c04a40418545289814440c00d0a00c07094414600d4144081000c80c0b010034030701d0990b202500c0e407000b40d440701d40c1c50101c0c00c1002880c91085000352003850340064000e000b01c1d030381e00300d81400c41a03c07242000200481d14101e01039040c21541302510401c80e141d0020791030341d8011411900051070310079807001a039052044051040c0d100b8031307150041000700e10070740340c06401c13038090482c21400442d111802110351200351480001880d103280100b000804150f2546504140541140b41e078640700c3d03540c541601c1120080501190300800c0451015880f080420940d4048c3c43e03038214a040300d0b4020986640c00103402500154071408445140a0104149402c981d8000e480c141e941d81c00381001001054141e40846024013004000151984206c480c40c1d211038101c0c02040c0501c414808000003021904403494100c8501000c0c101c2d80c40000c01603074000c41c0503c00202c0d081c01f03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 218361573 1250 218360323 218360333
    0x17030703140601020c04020d1e0e010506030318240a02010e12090a140105070b1008010b040203090d20070303080901180c090507050405040c05090102010b1c0f060617060103 76
    0x18229002424030007000104140d81ea400030b0ba540044805490059942e410b210030758002e050544120303000325010300c001202c0201d180e44a4090500c141008119544035941019240e00c9130305c800c03a8bd4410b461120050500d820004d00c0b0f01c080c030800d4042d5462124400416040d007088541c0301c05030b5540d091003411000144000001100000842854090500005521507040d4060203c032644859120616030340a502101c010740e807c05400c8180c0d1409007058010344080e401807180310b500704800181c09007002d0090700c1c045d044550283c42e5010301604100d9080700722100ca0907140f517140461141c20003060040c00d001d035009566110142c5481e034101d80c02c0d07491026600400b03001c0c484c1c106022403440705c0c4400070313240e001c00007080c0ba448a0320211018000c43c0c02c00ba0380f05280c040241d9620f03400800401507102c0a030000e00c0099001e40c1080701c602c1c10001c0b41402a00074504680000e4504200c5500c1c0034400c0a00042c0c0680340e48010910340c802103031085071640b2540050081c4a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 218362823 1250 218361573 218361581
    0x50a06030c0915060216170c030604150b010804020d0204023117030a0c03050310080316061a0307050f120a060507180609050d03030207170d11090607020904080717030703 75
    0x844c550009050003040c0d4010401c40f80001d201d046180030360040da0715010b01d410b004201400900408442c080c0c1800c1c10100b000e03001c407414801119103007841c031980e19400b40328502e114940042940d981914070380c0030b010183d8099411a4002a4101001d20303030587e01c5842e010b0b1003030f9111a2007200d80d082c603040c2c03040700140200401580c5c0c420b001c8a10440e43c00ba1022011551500d8402c0d02c94660360903201c1d903410a03070013200c0c0900001ca91038050584200c86404090300501c0103020072104406c0003c107600e12840c090340c241e00440c80a0000d41405240144000c8024141102c6609903159503401c2c0208403500b1035200d81c480c1c06200348154000d130b003007810124540c1c1d2705191500d8020b0150940c1e0300341c85440d0007029040014000e05020b80d0650750749907003008a00c0e601003400304072039a8941c0314240c04085c035440d02007060300074907000b000d648100002801062501c6626000c00091307400041049a15810800c83c080000b80d04210200514240c04441500d03410482005001c3d030f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 218364073 1250 218362823 218362829
    0x41401060603020903030f0702150c030310140a06050a020307060204030c0303020105010b030c0414060405060d06050103061a03062107030605010801110a020d0c081e09040c0c0201020d03050a06030c0915 89
    0x500500516241703503008030458454801c01c08800c0c2d90703103019101051380d0b1032598261040c0c100000c035004015000210081d4801e25541440e4401151510088090b01003500f81c2140c20000f101e1003800b4a070b000d40000d21400c00c0c40e0045134200041640c41005030303401070f0001c9401000c01e100c108101a02401400d000d0900c6500d001d0031403034003401c40b0156005501c030341e08000361113024200490302c5400499015050240680d5591520390184401910340b40c403c2034000391806030001092100c07400408010015440b04e14619161242000044504040c0e2100350305002e9400c0c5800700410400c00340114030416022071b00f989040821800c40f800c0c6002c83e5090a070802003606145d074007182c240700600ca20b08050500820742c0c20604101d0141504281034903522501070403403030490038081c00c840d4030216000c1c82408000f54040702c0e0030802c80b170001e02581c170001035110524000d0300304d154401701c00d0500203000341ea82d4a8092110074180c0c0b011210310b135603103500000014049014805 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 218365323 1250 218364073 218364077
    0x406050702030105010e0c030417120a1a03031c0f0225060b06030c03190902041d06010b0c070e04050f010626060735040b0702060a270203150414010606 67
    0x311f4900030349281c00c01d00c40144020002c0004000300d02410101f04140e030140c82240d60300020b540351841d0f002000380079010920220b540014145021840c2c000200c6d40e010741803800301c160050b28903100300f020b032009002c10110706409104110b40f620000780110560200c12404402814060400130b0031200d810413200e00441c020410000005015422241c021090100307001c1c0b1020b200c107000e8020041c007040294098200070154450418404000443d04070038802e079001640c0c0c80401d040b90388190080365405802a0310708000c1c81c07041c40500766109002c0c2050741c4081c0030024056003141c000b500074245182516040702000404003541070f80b002c01040c001c2c4481d0034000b1000e05000224903412603c86c0e4203028900c4944000186851900d0380c140c40244a4101880c0c414603c600840d040c00c014420350001440c103040e2801900340c0b55101c007621760001584464144842c1068210a982510480d20313840880a101504588100e019004516890f221403020900799541a800b802c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 218366573 1250 218365323 218365349
    0x2150703140f070206030a1e0203180a1505060a0306060602071401050901091511010e060a050c13260f0105090d03020909010b0904060503030f07060c1103090d0c0b040605070203010501 81
    0x201c1d031281c0070840e201c0341c4d0100d500c01d84a544402540020305111505da003050580440110f11030846034001e035000b0841d4603005100c0d030b403000002d251380c2c41c20100c0203802000c0030004030b2003129255024680220700a44804d00203900c94680e4001e948590b4082e000590010600f000040f4001c6181000c0c01000d02e0014606000341c00001c140c08075600401418000d082c1c2c8104455000d02001903035001c00f94000d200900d05960400c1d01c960040701c140c48442e09050025440a600c601200c007900b411444816483d42080642070907040c01003516054603403800303040c1c848900b0030020001c0c10040c100011600740740c0241c9460618600c000384806150043c041440f2680c1c40050036815114007010540c0c0368040d910001c0c0180925900042d090300002508110210403580142036440c041d41d0244030807031960400b1900c0d0440c40e003030108907400a00c01c00840e0b2601c4080c81c400b16020701d40d0615803a032a00030342e00e040da02680c010000b04600250900031410300b0f029460060114a4602c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 218367823 1250 218366573 218366587
    0x2190807031a09070e040e0109060504020a1a0a030b010210050906061f0207090b032803110a0b04030302070c03060c022b0503010b0a1106040b2a09040b030a0215070314 74
    0x41c0141001070030711810310407001782126582d15294042c62a404104009004400440c103040b8000d04059038164003e28842501049096445035000110544003540300d00d402c0074448220018242c4884140c11801400e43d41c50f0504c80b00d020741801842c84002800042c10100100150080c5000289201480e1040030f8403440350081103000403035400080c041216148480040c0c20104034012051210400400c0410003108111200b15118800c1e01c40c81d4440b50404880b0342d580b10b04810081c1020307000c00c00140040d20a1300903283d1948695060550701ea200d07660700f010340b501120341c0310042e802240180d907a003050988036001207509000c0d046032640900da009180384014000c2031142400025200c1d0f45500c9a81d40e603403041e5040042c0c03089410546403100074071030191010341d000603004260b410880000c08148043d40040c3c10381518244440091102818884070495850f01541e00700c100503031070304400f1440c040d24210348103030384a49500e000340107824588400310300f40c54244412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 218369073 1250 218367823 218367829
    0x4140f100207090c02030f1812071404560a12020102030c030409021c0b03100f1103090d03140c0f0706061203181508011401020102190807031a 63
    0x940103483c0700900200d0440342c00320060749188038142d20302e41480b00018441d103030851250040d040da0301e012554046680c8080c5942981c854039801455454140514075044510741540140a116080c0f0350841d840005611201345441110b42000d030381010044048000590300c0c41040b04d840c48510340303c01c03600d02d00008108140ca40d4000c0c0b420103a511840c4806680c020000c1c2d6446580c0101200e6032180c4500101010b134129400880e44028214040d0002d050369000340b40c1d1544028008004c2c101c0c8c80c0790510003410300c440c01102520364404505180903014402180300d06000310003022030703440c4980002c0c200c0f85400c03284404000d11200744003800601f601200c0c10903c0b00c040543d124101030629100802141c2d01007181e14002040c203104040d040f07143c646070340c1c061a1440c4c02d4280d40d01d0404004018040703514000880020043c0010081607a05484814042c400141091701c0d00312190101a010340300107010071101410404410b51502462041c0c11800141103401d480132404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 218370323 1250 218369073 218369083
    0x6080a080c0c0d0c150302071a07051b0105041a0103030906080a0b0915090a0b030a0f060b15030f130b07081f061d03030703020304031209090204140f1002 68
    0x90190300002440a05071204000311074400800030b04400b8040080d11300600c904070207118022025102c5030040d9400c1e40607100340c0d0013040c0c00c00810118a0110704100d590804000c06800030300c8010300c02014840103485401f00c1c04e240b4680001224180790600c0c3c02d6070440d6010f02040440b03900c0040c0b0002c3d0b44070007250211169801c100d52552515038001c0b0142c85072024407900181103604110041480d12212118a407041d500401c2588407914444103031040480c0c61a010f92000444100241041400849007070207000002405401d48000619460940c000142110303004001d110403103504c1c11049810295481c1091610038a83c2c3c1c540c0c0d80c4c40c400038003850500000c60001102e0100790304107040d50b0040030015510315515104003408400015402d450545200040b1130b04506000007110074031909600291704203440c40d5998070000f0321404100c001c010614400250402c1c071030000e8005402d285c1c0840312101c99400501a003090b8141000d41f00b203503410081c00c80d0f2038000c60 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 218371573 1250 218370323 218370343
    0x4090e0309030a0f0f05100603020f09040b06060702010203041d04210c0b0612060702010510140d02150f0f070b0603010c080a1107051b010e03030406091401110d020105010e06040608 80
    0x1013030041c4100341c105468041c0d201c44010700742d4000c500b030020b0b8a4040d03074001002e0341d101300c41d0f4401c0b00d405041402901c0d1400c407002054880c0d024003103070b000d18010300582552071052044034076081d1110613050902c0782c2c500000302c60351181402d000401022400c1e000c2e2040360103042401100001d00020144680702c00c0107401c02c0e41b82008a040c948405240301c4002c20102c1c1110301da4200094000d00808048900300d590041d8031001081c000000340401100440041104200d22180d07000c219270354510341111101e2040401c00d01c80d81030b02c41760142c036150400c00e0429866040901b803150101500500c024826454566a004480e402c07114243c1c1024010b07100291042c928040da0041e44146013015203180f2030b5841c0b26401c42d0710142c0d00208000c086e44c0d910300003041401410307640d000714041c10020424020061001d490714907104407039044140f41c60803a04160030740d070504000140240a006035100c6005100b00e10402038410340040c41620100540c5d49820a043d46a0708428 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 218372823 1250 218371573 218371583
    0x307081513021204030e0d0203030f030702010b0d0b09070f05100e27061008060904030e01091d040c0b0c0a141e030a020d360305030a0504090e0309030a 67
    0x5810010951203151140000074041d82045680e00710300d204070803414070202c600310b0019111409035040381c00d286180c1c1010b03582c050300842c14884c2c2c491080303d4507040180864115942e80241130b40270f50301c06204c008040d020312018045810181c1c121400c009158200e0b0f081100c1108041010b03803200040114450b4251420308420f0b014080094440c1c175040c1710480d6100882400c441140c0d948001c6103004103411903040d071542d4404581604d0014044402d140c0c01000305c000103000c68056070074074442800514002e01c1c0261965110181803840d0b0a0310847c1a5804080104001d100f66010020709103544815051980c05d4854a90318542040c004040c00f0b00c124001e99803120030041007600403618149484010030368030000d5a290010000c0c10010311807107a03005000750058000510b0300d00481d0f0100036004800018000e503030030b00c2c4403500381640e5924001020074018009800980455a44c1964440c13501180b84203640f01c900c0003c0c5c8540007000794100319034001400640040d441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 218374073 1250 218372823 218372851
    0x801031e021807020d0e0d0308040f0519060b030610150f02030f041202010215071407020319080405031608150c070c031b0b09030a03050c0a0206040e040b0c030708 72
    0x151000c41d059001600d40710050010b12070070f01c0011600031400034010500303640c400c03001440040030066081170a0a020b0b001c112810041400b08521100c4210814010002c64801c47e040c4220801641d00ca0007003503501036500c201281c0b40d0701e0103100d09074102c2405480410f080d42805810040202d00415490600040d22170203020b090003442980c151024078209141c40b540d0303035084550020000c0c00103e00500405500031007104204100340c0c0079010b00c2c2d40d40c5040728804566540582d100c0c10303080c2d0745441140807032040c904100c814008094829143d55899070b107000d0030300d40f4000c40c003200c0c1000442c0c102401d12406034001044035607c04000c2480d1f200d40c4941010035020b121718840504002c681740800300c2804580a0b5000c2074140d00d040b4508026902c103658000d6015282c03800c0e9142c2c109091420100c0c0c030807009007840c0041c2c4002c4d24038a1151b50300054195025031301490601c0585000c101c1441003440c0f01a0b8425500c0021610350714003c080104040c20007850101d0300080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 218375323 1250 218374073 218374133
    0x150b0a0503010504050a0c1707140d1211010c020a03051213170a021902060d0f02130e0a05010e070801120503090a06050c06101401080612070b0a02010c080103 70
    0x10661080000c1402038020030075420603090240e01e40a042034140c0300400c10040024070170030848080d85c40e0b81c9032800a030600c5030520400c442c0e41c4100141c07540d4456603184208010a020700604480c00200c3d44400c002c00c280780d000340e820340f0b80c5241050155049000e403100400d030028100c80e802c11b03800e10b172242142c5d50211f060b0717007414000801034078140c0c8503080c82c0d102c440c80c1030061100212a4003240e219490301011180175021511001707400c64002e000707105950840b9000320821450940000d81409a850840b044c03030001680001030342c07103030340050203655403083c480c0a0140903131103510343c411300c0d0405c409420014107204400340c841202c0b200c1e2041c400c2c144107681d540403008000031003180e039a031402003654210103410508ca00031280881e03642c0081e00e40280c1101c5040c28040e003080d07190700046d10010401400307180c00c9420301c0800c8940c140280110b501410740711394003680700c2054550084c21100000d00c00c600380411000180b012803003d110445400b1382c1d18098040307140d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 218376573 1250 218375323 218375329
    0xd020d0c0b040611040e1807050a180f0e010b040f0204060512091c11190201022e09050d081f050607150501090c0f050726040e040305070b010503010504150b 69
    0x180060982001340e0020501140d08a10516001e02800401640030040f1f00700c10045921924580300d0b032039000002900400c400c0b000181e0810203086221800200c1c064541c0082041c3c8400c890b00c2022139558a2100c0d41ca482c01c0d00c9054421211404110f0416003003801c0900a0f124183d030084004030301200142112400b04145001c180e040489000000c501d220054a16000712004102c14051540d9968540c0750300d014099285070142d00500c5003c02140c050588409490f15140b8a50110165030b0030308400c074054503440320302c9000207107000c48811038018960100030f0540860b01030114104008801d855800d07106503841242c1c01682c5051600e01300b02459940d0440f000d1107401c040000420030704950000d041c3c0a666107401c1c40c00002c003402120b451141c03c1d00202040f00e01410318401c030110051500c50711107401c4085150a80b00c18004002d448100e40860000700d0008503d010051025421401401e040e0000d00640c14140e50b0300e040c520050801401e0642c2e660440da42e1a5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 218377823 1250 218376573 218376581
    0x4060b1201120c0317030105090f0f0a0c021e0604060b01020d0e060f0d180203100c050415051c0b0f010e060909070e12100c0e0108010b030c070c060201020a020d020d0c0b0406 77
    0x140e07021984c0300350705c41c1051005219410900c20b851040303e4400010301c80030101004184180311120600c1c0c0c1e90360359401031000500030a00707600114452644442e110010a00b410440300c048103000f81443e00e07080c94001c00751403826540c0f50464010110901c03150b40c2018807030f1410340302203c00c10f803501007520b00a0502e0041e8002d102c80242048100040c142c2c00d41d04031001240207509450b0183d150340803900542d0f404c8882d5400298040108021801d144611a05410014a840c0386403186619051020995007079105440996804030025640303040e0b00b600d21010403e08140e8071840c26940061241d02031000464003800380b440009403c3d80c401c40324403116100046c0300d03081d00c550503031209586158200601682901d060861031140d4080c000358500f14005a45460050b0708100c880b45d40e5402c041c0c0f2121340490140640000680c4070703001c0700081e20066000585402d1012002454041c1e10f01c14442076401000812a299138840ba01284207900208108411b40321854020010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 218379073 1250 218377823 218377829
    0xc1801060309170a0302070501060e011211060c060c0a030c140d0203090f100b28050d0609020306010611061b0906070206090303030c12011d0109051905010602070504060b1201120c 79
    0xf159000492004154041d1702038080d160240c40204051501c803602c00342010300c00e006201c0d250074101c85010000c0c0000125450400014050f0790409070700e80503c0b441d0a20a0f248a40d10ba1400300f4480d60b007070341c1440f8440c2c2c0c54034246032110081e0108040c07807595124405a80c09071580000c00142d40c02c00030001c00004040303070021104541d40110130b0000400c09001d486100b5802c0100d0240a0103580c4c400681d200e11106003400524500010820040c81c42c102c21900300340c8455240002da035003440514000c1800340c43d549a2542c3c1d2404007404d001d0f00400300c1008480c44110300554500c0003007a00c40c40102038076807940d038801c0d0b800021100d024407101c080c0c2c980300c00001c01102c00c04043c064184400306e00f4070150706989590381800072651b90700340c04c0c01a06400700100074018180c3c01c202d070048484100800351070380072605041945d800360070800159000d04410031180c2801d114010040200a05003410045d42c0a40c51984103010b2191001d030304100081741c0c0074484410014801 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 218380323 1250 218379073 218379113
    0xe0409020d0c1d04080f07020a031a0402010905010807020606041a04090606141f03090303020d0c0e030f0309030a08090102070803030109060311040209010206071d10110c1801060309 80
    0x41d48032501c2c100310070311903a01800500d800c407440310180f0030f0024000603000307650102c07001c2d04054220b07030f4100c070540110a040e070303106101c2900040410f90a000101e03680031602e02c1211039203002d0001501d400c04d00d900c000e04022107502000070041d070102e40907400c1041141e01295904500c682e511b00401c1006440f0380c000c1c6402325a008004259203d00e0803139080b8802d00d2807084082c010484040c00004c914a040000e10411108003840b95220119a0744681001401d150810132001c0485034804400c0e00031841c00d5184181c0c0e4601000070600100c17402005503e03001c0e1000c042138807501ca15100804d210000304500d51660f0081c410304000e07051203801c480e120b696424041000e090b2501c81611942c000000e0240c80c0d080c00e00888041081c103800814a90b156160100c030310200040b420701d0050000301a82406580d08c80461221203580d94484940010b601100d90805410030000c5115821034103a0b0206540002c030240c2c1195564203000400307036114181a220818a9565424 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 218381573 1250 218380323 218380339
    0x609031211030a0501080a0803150d080a020a110a0b0f030408160b0f0702030304110f0d0b01090903110c030a0212070306091a1b03010512010f11091504150e040902 72
    0x2000d0704940081c5205941c41d0005115036680e0740941600c0b070692090103840d000e0200006815449001302c09610038201914101d451002e035103c5c540681c00215101c0016007000042c1c1c800d000c108040585c0c425012120140c5843c03400d28a68002c0c0b140100741e1440002c0800060207004107802640c640b800e449034440011107041c50241580c00c4200d952206412403440820302c80e52001080d68807890b4800340c2c00030107925080800065990000449602440c0300001c44002410071a84034000e024440700030a00800c1c0e444c01801c0c90184a2600b0642c0d804613410140b0341d5000560381030306a8042e034001c03004070806000309090602c0d540001d480c2a050101190805c4000900d251400c00d00c500c2c01d11030754507810b4120b41c8c6040e0160780c95107040b80a02c018010392a0101c0c1244806008000014607548400302d000d09840e1203031081c51038036401180d1900e60741049080c01c3c44200c0c0d1003d003180340c01d08159107242c04032401d40800042022407207104501e40c4a034ad101c802c85640081c0a00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 218382823 1250 218381573 218381591
    0x912070e090607090b0909010603051305100c0e03010902060a031509020f040e090d0c03081305100902040b101d06091309021c0f080304030314070302040303030506010e0d06090312 79
    0x75a680e4001e4840c0750006402040016041000d4070584512110042003410682d103060402c6002d0302c00a440011000100c02e014400101d0400c03945010021418000c600100d010324003800603880381c903c9901a0b41041001e900694400c001c680d18a81281000982003816001c1840e1121144c0c02068034144001180800030b5011400b510840313041a503001869940e100025854510204219010549020341c8100180c0200c006030b5004824080c402425041522102c1c0b404202c14000791b0300a503146860400e600f0940105c213120348080c2c3d060310307100901c804020010b1f8524502c10a1900302585580607564501e000c803103801c40b00420119456880c980d40d40c0062002c000101c3c0315407400900d001c1c20108402102100640088c03c00c00300b44426101c4902e5988020000c40070142da80c12051a01c19240702c00703600481c507035a40162118203500c0c0c0a804c40e01301030900e23410b010320b034200c03600da940c0c492501a81d46944010081142c0781203140689001d007043c0c280f0903145091000c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 218384073 1250 218382823 218382841
    0x301030803070917060105040b0d0807060c03181a010905250207050a1401351e040b1803040f050112150b300402270a0f0e0609030912070e 61
    0xc5ea040c2c5e02c0840b0308004030402d203420031582c0c041d007000082881c0414001d04011030100d5100380e03040b030030606021a07500004110136203a205020b0044900e102d42080c070440c00300705400002e02510b016282003003a0300300070801c1340c000801c400990700454501322004422510a200d80801400b0203089507440711740307400c10026220740da0301d5060b001440f620944a00c1c030207550385480c01d150741072210200d00708000b092042c0c0c0c2d0f440107040280802a2480301000c3d83d03400344145106a010710b55102c0c940c10103071196941c0c00c0004c83c0583c619441404184144079505c625041100d4090800301c1d1101088074080300500018580031000314074a000019100e91002c0c01040c1c2000680300d10030103810b030f15407081243c100441c1c0014191404400007401810324611001a00302d1303907e1100c2481c12000000707102da0001320380d520708690301e440c60026089440e001d081d1606121402803e030741d260a112607541da004030307040c0e14403a00312446050050041403144034098607980801101c02c1c98540c9403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 218385323 1250 218384073 218384083
    0xa02102d0806010f091202010e1903050609030a0f120e0106090506030114040b0f0603070909031707020d020a03080a060b03130201020c060f0403080a090b1201030b100b0301030803070917 82
    0x11004038408030005400b030740c8a0f802450340724807551500341c0030340c0c1420001460900520412814002d08040801c01030ba1841300c004405244d102c600502e450841c500301d410901c000d4002c81c400e92050ac002880e490b00030748409282101440d1494503a000614410084c040903070365200c0725480e14001140e001c0054201c90701c504000e50090180d10002841c45c10345400c111005041c11801c0b00103d0340d007441100c0e041ba000000181222421900c07280d108048a11840045011882440d2484a0141034013215a80300e038103030010780b98481c40f02c00069144c880c1c0c008000c0c00c101c600300000e10940800e900001c003038102c12140549900e000000c4409403618901e0a90151288654803001c900d8040c00302d800004078400300c01d040900e141e81300c04440e0015003100091200210700030413903500c41d2000d0000401ca0071500e824951441c14082d9540002415583c104102c05034140203189010080780d046035448042d81c0c1c2e9130354401c5800c5500b508076400600e40500c00c0c0207407030811480068 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 218386573 1250 218385323 218385407
    0x714070f05010c0f1404121103030301090c180605030708041e08040905100b070609080702102708150a141003030e0103150506070317010f0602011404050a0210 70
    0x94000c13249000d4401030340c60070800800455250800c110500592840c410fa03465070511400c2a0201c0c031203400d001a04541090b0804c1705d03400e640d40e410200707040e4418840f01c110700440c109000b541d810003000030054070000702000240011240400d04110080b1005200101014543c43d86c1718960318003000b1640c8588260144c2d10f00706030200e516024044121002c454020800d00e191107510355401000d4a000c40d41075403140780502c0540c001d41c13107111481d40402200d5880c41c02d921005040880c0c140c00d03850419035550503c4105001141d0700144006840c400a03940c80c0e00b9030707284a050009003400342a280b80c80081d144c1800b80203a0b480050106481c802d0715416040300185d4011400c980d41d0b100c00b104540115101044a82014001440924000c2c82e0000d11800300c2c0c0c0c15405c01040a82c8070310075445018030100203aa9080c8949000c000001c0f2150751182415120305e5030728001400043e1280c44800005040349004845d58242c0814000c21125408111518090001800d031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 218387823 1250 218386573 218386577
    0xb1503061504061d090618071103030a05090d0e10030902121b01230a1115010305031c140604051812071e0c09020a09030804080a05010b180714070f05010c 68
    0x2012042c8a11381a4a014400d1501514010b0440640d1070f85c0040000082e0008e030910940110350413501c00c00344000d42c8204031280002c1494104101c60324a07200c8821030071410807296042110081d640c40412800d40c586600d00842e5002c21400020410100c0d105807841600c984001c2d04400148842204e844241c240c8a5552420503801109000000c0403001014641d0030031a03049010f00961000747c40e0803070101201c108408120110b039032150203800a850a034408035034a868040c50624658221104400a210000280c114082008000f80c0781038812501c550000302480f071003040600c109000c400440715001a50740c00d0300d00039032103141c0503903000161109090346820504250034425900c06698810f26103000b0804009420807810601007100550000012541c880c0c040c001409020019000110007803070141d08440c00940014041d0061070848850700e5903203104141e02c0452414501e808944a080d41500b520421000400040d00c2d540d81109201c0c0c15405802c09060907 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 218389073 1250 218387823 218387867
    0x10060302090c04060c03050a12140906071809090303150b0706140103081909080f01051501081003030c020319050c03010b0105090f0f030319020d0905040b150306150406 74
    0x842d1030084140710340d010f0320300030030030794040d141c00203210300024400c40300c1919007d44150210340d2410242d60800604041100d41d03501032040c000303070600415821881c103041c504d0030002502116042104a4847d950b4816624200c1a0074180250071814034080322a400c0308040341c403910242d541d0703003001d0f4042c1c940503d450141d84040400014075416a81c00a031040c1c1043c90301c840c0307560125100c00780881001007944002940501c10800800340044d02400801c0c5458120b00b1070078a1034400d081c0e00c3c10008001d05101080d1003982800059039054505080c2c809820700200e440d0001d800148290002c0502d200d50074480301081b801d103401c500310000d21401c01c00e800115101d001c2d400075140e01070b040420180f0140b610182503001803038050240e13030070a10003046010040721328405200158005583c51120b159001c0c0c20030002e00400c80301008440c201002103101014009100c94903240c001002c02d41903910a800360030700c845084209075403292103601c014103000b41b00500941c16521 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 218390323 1250 218389073 218389081
    0x408060717040206030402190b030108150f0115110313150e0d0206030a0f1409010c02070b07200102100e010204090609050108060703091b0e01030b0106111b01030b031006030209 78
    0x80300c20030750b029030340041449045884603000c104103030210440000c0c0003026000000b4a034014940510700801011010307101c21880c460985041c4c0078020300e00b0300d2000c0444014041103c0c1386445075404c82c2c992034031902281898800030702d94492003140c168010048000004c0652583d0100d00700e00c41d83e80c1d9401c0b02c5c40c104105105200440c4134000b035000781d050000950b00740c901d602c00406611100800700b11174003041c104411200d402c4d0344002c4940d440c0c3c2c0300040b54036010000c810003004640061440e2000d691110030000c88034500311440f8191910003403115a2081010104d0101058420845600c99181440c000e602c10700c02d410b04141042070020b40760b0a51b1060504840c02c20f0046e0078a541c45100450040c0702000085502c4428401c010b00d02aa45002c20b5002c3d00315180d08a07207035411030401401e4020160b000c00308000144101e9054a02c0118003880400c1d55502da40308a2003109005801511070500c07803a8261040d41c004a0340201070303821010890303009072000902c41d15 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 218391573 1250 218390323 218390357
    0x21003020a0c0602090613140a1a0306010507210c05010515180604060324050a0b030a0b04020a091e1a0306011203030623030d08060a2105010204080607 67
    0x741e0864001141d01101c1c0d20000c81c090390002c240500d0028212441d05003110300c000303403100450f04000b01501d445050441d49045c00f60045000c1c0580703440c041040140c3d50a09861031000902e024100140455000c042014203004007052807920361840c100200d00d220000e060303004015040e2240d40c2408041184012103144499941c2c0d4068401e001c00341440110310013408000d46200e4002ea5261000008200c84140781010203038401403111052102610781401d40f080034200304c100610705110303111103680009004881d02e03444a8100041e90f11400021846621503204001e21030410740486220203078100418455841c01c82f0800462421303450300102909114100350705903111750300610005110b84000c0880c184241303408610552921340350301500f0a079401603803c40c907008603996076034130f02440b80c03552004062810011134a05100003c542d84060b1003104a404074051041c0031002065021120142e0048000d40d41ca55842c0d40d41560ba5000301ca181d000280d868080f001008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 218392823 1250 218391573 218391577
    0x105070e010e030a03051b03031003120f0e1207090e0102040f0806090a151107060209130504080a1110020a080613060b18010e13020d0b190306020c07120f02100302 72
    0xc80260003401d0884c0203aa05803410350203005504c9060f410815001d401c02000c0008520404d032081070a29202d00c1c43c90100c1c4140f44007000c500502c024051000000c0b90700400c1c02d480c0380da007120201c4410305200f810302d00b000d8042c1c0145454500741107e800c11004150010002c840200303624102066035640900c0d106c0b42c0c2075542c0b0103c1e4003e9940e281c0402d1101d103480e0b42208500701700283c4421850020002540050412103505801190101181c034044d0604000c141142400380b000b46059520810341d4800c0195003805d10040d8900740d00340a104100010025001c14000c56941950f490b001d00413810460340395109105e544403042141c20280a20800c441c0e480018606140b04d030790b18140440410510981006030601a150103548d8440310f40007010340100c801640c0e500c000400c141a80c0400311a540540d010101201032010428514400c0300d401c80710051300c80c2d910b0580182440e145600c981c43e6420500d61400c144000c3d44a06520035200b16404812000d44c0c0009500368 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 218394073 1250 218392823 218392847
    0xa1211030d091b170c03030415111504030207060801061b0602030a02040b0403080904111201150e03030316020606040c1b031e0503010810090b040b07121d0c09010f09020c0a080c0105070e01 83
    0x80024009c10052103000e0005407401c2c1d1213207410368800001d2442c900c46180000c41c0c040d00142d200d42000c0042580140e0312902504040c513101e0708541c2d03101d4514049034204d1100800b4954004009800b84203558107685c0544500d00509540303c1c1e80c3d007008003440d0000441684078603c2e001c03084000d804194100d4074010507801a180941c0c0c6841601c0d03010841e005220800c1c403c1d0f1030f11544007954284011442a5104055a582580200002481c0800003007465009900c2e005115812540040050081c40e0781d84580d129000d81c0da250464440c211010f84142c5401c00500510310700d508080510b041c2c0300d00350119540c0706100c0c0980e000b03849400e500949107902c40400701d000700340c0710110664803100500702650b8104042000c401141c1181402205003080001411070107071052040030134100c2c007142c42c000c0380c0d410148520981c0700309215082e1345030b90020700c00a4801c418040c50f41400d41100b0740075201c04400501e5400b03040b00b2103107031000501c0d83e803080c221980074807954ac100d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 218395323 1250 218394073 218394089
    0x8100521060919061109130911010513090216140d02160f0b031b041707090603051f0605100e040e0111032706090a1211030d091b170c030304 62
    0x2011055449910003401d0800c0c05d943c4501003003090031002e454003003035007020b180303010000500d000141c140000d9814103281c0c80d07410808200481e840ca003402038050400c0d12108440141d44002d034101c0c0b100c0020000c00001c02d81c045e1400d0030740d10500045450704200c94590250368400c8001c10b00c3c10300d1941c01d8040d0b0184003108030020300202c680c07032000e154041041000b03209407400c141c00c0e01480e03070016070007e6410403514090401c1440c0070f000c0308000f0034110109200903429503817640e4566280300d14465a044502003217142560483d081400101006040d4900824032400b004140300900030080c4d010f0340c18124018001d0b07005111301100422017140f020304540301c0c2022a4034041c80d418a410492500c2000c282c0c020105103c1070b40203080c80401007800c4510b40c0380080c1036000885101d07050107200c404a84891401008580d040b940303550001034540700c2c40ca0000c0c1050f04c410310b121060848800045011840850358030440281d13102200d90303440d078550800d50360380309038011a80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 218396573 1250 218395323 218395363
    0x318060504090c0c150c0207080606060d0c1e090f060513090203060a08030412210206060d0311010c02060106110304030213020f0c120316090602030a081005210609 72
    0x12481010340d200500e0b0000d24a03260380944c0da182c44943c8000c5003411059417140e6584002c84a41c0c0e010040c180041001901401461511800081c894092800451011a15100415200c5108944810003007441144003068168681c00007020544107004200c00b40f000724101180c1c05010f0f00c2914406198543c4100702c00b41404030030341c060341028007107035000307880c20201148192090010304040c28041841e4048101e46040c40d18451203008c03040c54022a00482100000d84c2c0450802e90111059414810b080c0302403408441648015880b24030b90b521f4451175000c0c8560201d0650b0403509a965000300200e0b5038140c05441e40700d580300081d1302c0207203611984404515a000b80800c0d1100c074481905001c03482d03005604104010041d006201c0c2c0010401c0401080030312056032400c200d10b4004203150030540087e6591081c808004244000740000904141c03005403940c010b0000039006800c2002c40500c2045c8111049680c0d01d000d0046400003a000e040004200a051828a040316 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 218397823 1250 218396573 218396579
    0x90f06070503190915020a060b06041a030910020315091b16050109060203010308040306060806040308010b09241201170c1c08030f150d02061c0902100207030318060504 74
    0x18608141904410034407842c00c00000b12505c4910710120107001c00d4001d010410030703d140450807a403604100d144900b02c24042840f500b140328009081101280d101c03e5500d0b221859403a280090000000c0c0c43d03540004100400000001c4005107080d005580f4a0810b8684110445a082078481c3c41003083c00c0a004044c0c80c40038a80d0b00003922401140000390350245521903030141e9100741c20a6503540000581003040090b203101d4000149201d602074451800c150358000c00442040c4903240e4042d1003c104e05002e0340d40c5000058038018403850748cc0c00002d0b00c141141c084d0f0003440c1308020501c5a04000140c2081c11086040300c1e50f640740160042c071201c07030304108802841c0700407000d040e00c015841c1400500000c00641c0580808855540c1d20f2501c05400d00758220b01140050148209030100401a1108426100b002040701040d407519184000c1d4900203000c0315401030340c40008004c0340000b942e00480c0003c01d0703d0180e0343d0102941d03c902c007210703000a40d901c02d032400628100020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 218399073 1250 218397823 218397847
    0x603050606121009030903050703030807020f0c0a0902030c1605011d01091109190e0610061b0204020d02070f0b061c030c060f0204050306090d030501060f2c06070305090f06070503 79
    0x84d580385100b820603113005a16519401d02e010f0250300220302040000c401d00400d01c1c1c04008002082819074000c0148440c2c1d2404214811031512070401200c0d00800481c803d5084001503840c01e8400c4a0380f10032486560504038040d01d40d0002541c09215031900103d041c3d039040c0284156540c1100a920b8001074007418080f01200080201c1d0307102c5524a00c0c80741c405101c2c010b130b81540b540c41e0020045400c02d10710810203c0a0b41e440304051040b455501d801740600f480340f007880d26404842c0180c43c0c400d4a11140c01038401d078140102200543d40443c000c00401c91a80c50187c04180c0303aa03990a100500c1c0d401e540c1158440140214800c01c4400c030000f402c3d50041052503100c0d820160804d95030304086031400400340c2c2d07000740640180500d242800c2c0d06100d0b50303004102c03a103810443c0411030744001e49800c0e030240305000101d581c10016041300c1c101460301c0d0798003000035058030307a50b0865003070050480d0007100103144641d2200d1041900c51030084151080c0b144c220300554505400c00e440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 218400323 1250 218399073 218399081
    0x204051c060b0a0506070f1103060429160c0203031b15010e091504031e1707090f140307050a0308030411271312020109030201140106051e040f0906030506061210 71
    0x401c86452342681c01d1b01c03c1e152824007100d40603511500148000040611000580708040440e05c0820b8080c08c1c20400c064450b10011101c1c014a401d244024040380e0001c20f0440c03042c614040c1d044540c010b200960100c00081e44100d00d506c1c1641c0b0f041998a94256411010054461410079170041d091036014079203400d1425003040c440e0400118401c841e26036051840a41c50355000451502103c1d40414103600440603482801c518141080504004188416000f07600030600e155103080043d80d01900c0400000000d0f283c024207000c02159a40780004140c0e00454084410314070500203030390b00b8207022601043c0d658050490b1021040c1401000c445410024940803c00524604620218510316011121170307010307a0001c5500c01a0b400c1c041e003900c030702c6000d401140391403900400c070442e0b01805031104841da502c5c00b1103100340141c00c0e141c018051034006181a20b04110001405021030340300c1e8045074411b00503a08180e0383c0100b00440b100340d4280e4100385820044e0b45010301c820342d43c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 218401573 1250 218400323 218400353
    0x6090e030a080709030506010b0c0c0a270213140109080d05040605070807020d0b10081209060307050d05090d030f05060a1701060803030a020c0601080a080d050a0204051c060b0a050607 81
    0x2404502c02c9a580d1101342c1f074100c0a9010000b09030b000a204444c600051001c0003407444165940c0c1e94045c50040640e24000480e03403540f4400110500c05c0c09034800a404071100c0980d0303080e941e0040d40c0c45070702614070550282070081c00300c0d6807504006841080030805c0c2c426000c44d5114242401d150607401c0e1031a6009200448001c1c1042001400680d902c07890a10520b00541703119015117070103e9024403484064000080701e51044c081d280a2506207400c462102c602901c005c0e0716038540102c01c0e140740c000c2c0d07108000c5c2681403500b0002d60032400161041085004d40d004d102e07109040c003000f0100d46082c0d4900350800384a16082c40084503000950148200c50000001c1441c1e0b28081d1a046401c00c0d9541e48401c1e40024207410380f80020041e440c00340c40d100024044101c803550b100f1070b107031044d030300c40401c103a854000107a01c1c1082c51b03054800920015110b0540540c0305100e43c01c11403c0c1110444045181032480140750400c01d8001c030940340b019041d1894411162a02440c440b8051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 218402823 1250 218401573 218401577
    0x60411011224061101090c14010e0330030105010f030b0604090204030b01050a0b090105221809200d200415090501051005030105040e0708030c03090406090e030a0807 73
    0x740c407001c0d00702103030141001510b15802c1c00c42849428107400070700e42e402c3d8500902e0103a051016510100c1c002c8030a01044442c03a60049190a0704140103940d0056600501c03645400341034410200b051950080c0b08110b181c4e030105040c22207400e42001e40ca40800e005190002d15114203403800580241d000d4001c41c039005044500b07242d80c49a01c40c0581c0e0250708115010030040004115504001c0a580c024010b9039441d10704009581000030120b0140040c0b03d40c6808a1440080001041d140c1c40c1010341041424049200075020640014104511045a036440c0f40c1d41340d0460320b07061040120641e80300614078a29600d0070b0311003021200c5140c2e0700183c0000080c191518650b601e2180104944030f1031400840f003071900c02e846003260701c143c0c0810300030390240e04401e80b55680101200d0559200300e50000e08d2030400d0341941d02e448000e0308540d905200c00900d20802400c00000b4140300442210103212254640c20600141e548540c3e110119500178010300122074060001e0603172050182c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 218404073 1250 218402823 218402831
    0x1207030905010f090b13081203090c061e0a0f0f020f0d0c050f0618120304020a09090809090c03010f0b0f07061d0106030312050f04020d08030c0c01020301090b01020f0604110112 78
    0xc0c448041c0103600104044000031316142c1b0401c80e1175000e000d40c03005011000d0f0000d045191400c4443d840300c40541d04603214800008a501d82d1180080b03084544281c640300c4d454460700989030180114005245681c0881d00603806064483d10010f1219004ca40680180045840d0b41d481611182403003102143d05010308410f6151850302086038a10070040d134040b1440394412280f0103170030101c80c841001d0b0010b40c01c10401003d6224207640320700322007034614005081c54203814050610f000e84400039621103540410f01c248076039110051410387c0c80c01c071003400840d99540031940183c0700d407100c2411410386c28030250700490881e9222380d520030a10002c48071801b400351001402c540e501d401c00c0740840e10107a0307414814502c0388140e4ce88100a04003854581c00c1c1500004c04c10f090108000f445407500000003210400420140e5951400c408000e5480b03585680b0b041c00940b14400ea02801481084032140711401e000900c1400ba42d0414040800744a1040044880d1003852094554103515 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 218405323 1250 218404073 218404079
    0x2010f0c0f0b0709080601230a09020304060e0c0102071a13031202060103030e0603250909021204060506180403080903070807050309041b02030a1b050f0303091207030905010f09 78
    0x28480720003440c0d02c02c40321500145412180035208030308a0b0000b00c400d80c400c400600c07010700e1303ca207460b4801c00f0525080401c0145040020744014203600000c0c0d1090020050001300b00164200031902d0302c000d420f4800e4080d000004a0395480c940c800c0002a2841c0ba03a5465221920300040c00304a03801c1c0d0f10181c1182d1682c4620901c282c014900c5001a4407000040003403582c0800360b4a800d0104642880c594284440c41e414413501c07040484050214040301d01d42c0b00c5004002c420000c00004000f5900c4031003c08540c420340400326000d5805500700b00005203180741c4032512000688550180b40c04984442d1811180800f008104c040d140c4000c22101010408440151004600c144011a9038000100920090311480c08900c5a004010f0514030364594000c015902040c0c084d103822405081840300c4c08003880030b40d40c40a8460f000c1c00440c09241c00022000b10b100b074050200b11052500600f140070881d20400602500245644e58184480e40c41502012160001e034644200e41c251 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 218406573 1250 218405323 218405333
    0x20d030b060714032502060d0509010b28050907200a06050411041a03030301181d0304260c040c030219030c0f110606060307020a0b0106020106050a090c0c02010f0c 72
    0x80d101a4000c0c0540c408100441014010502c12404074511064117520301c490354003050041c05012181e0250340e4540001940e00242580006a071410007022542200e241d680c181c3c40000000d4013003500c90080020100ba10f0402c2c0210501560720b079544e0a0031415500c8000365241c0d107600b403000035030054103038207004280d0b00d00070342e03008034003915002e01001045010031045a02940307403d080e00c0d100c2d91015015070f501000341d90464a1606025440840841000300280640e10429440c8081541000900d00c4004090410b64801c100448010102c40011010580140c0c00203007940d808088207226030300f0a9000003501d60b1641c2005410205000340740404103040503080e0000a541d0b800105119500c010035800100d200c0c00c20045071030f211410305441e554002c203100c3c024200000400c036074510800c910740d082500982d842080f56150f4030001d0281803030380304142c8070700981c01010440840724418484034a02986502c42c0d5042183e005480352a60f2890200034860250f0400020170 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 218407823 1250 218406573 218406593
    0x806040f150c0930122601090b0105130b0f16060c0e060903030711030c03070608060306010510050d050712060e0405100c020d080604020f0f03180d020d030b0607 71
    0x1030fa101d48000380c2c10000d0b004045688526007078688000400107080c001000d500403800d040c2c10010002a14207070200548220400c866041d42d860342c034003144d0310002d0801302c4040c107039241200140301d1201998011540f074003400348078042c01000582e0400a24107010002c4c030901030b060b11103030300303010b0008440528030100100546485481e690b48203110b1703a208801e2001030808554241c20201c100f001b10356203028041000b4600c40d54330500303642c5aa8102700746510240020300b10340c80d0a80340c10004101032003d40c0c6031802032040000108a0785000702140c0a40c0407265100350902c0a0344400c180584405080101030100c3c6030200c4911a070f15018075400340c4460207200d011400c041c901146030926000c0008001c07407514441442007540485e12403041a81e0f403814242d40e0702e968000070001d1046145d101daa018000546d0000f0080c0d94002e14400c5404034201e00a1802c04824251100036640096005811182686800c10301a5100454810300640890304248840d0340f100200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 218409073 1250 218407823 218407841
    0x6030e121305041e0f020a0c0204050c0f191725030618200702060405060f0d1d150106050a050d0e010e03091309050c0111010e060f07030c0206010806040f15 69
    0x2158044c10810f6114a5401101c0048450503405c42c60441d01c14002030401461150081c42603854502103400d0000ea007040d1800340c1c1803401d1090341c07244501600480b801003402113501050f038103100101c04c09140c5108512420102d01340040385552003011603004043da603041418166511000f0900c40b40000c0c0d9550348007000200090340c200f044694007401c1208528040340c0050030000000140c03500020f48040700c600759400d075241c402941c80040c690007814000c0355468586698510741400c200c540d1005203034650250f640c14004000f20030002c100c240245c60101d9410000028854407640c020705e40602480c1d000698941c1d6452a10300b590300050040103594030114044660380307803850103050b501d03040c01c5041001101d80c0e591240c9406003880310038180403211401014801080d000101200200400d544540c902505051300400c01621201c4c0002d242c024840e401d6400050900e040c3c3d840c00b002800241d5640d5560841e000b04448202c0302812151000b00c03800c803040c06500c0392 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 218410323 1250 218409073 218409101
    0x302210405010204080c120d050702220b040e0a020f01140f04080304050940051603061104080a1401090b0109020406030f0908181906030902090106030e12130504 71
    0x1303518540780b000c070315007010f2620a511402c2084000e0402d0306c400a405814a030321401c0c026180e44490000441d034080c07100d180c01901c50700104104080b51240d1118100e40c4007250b080100d8148444640d540b40b141c1340000b50040c0013100c86401e2503000c0d1102c100f544101840c03003860f03d66921030002e00ea80160340302e2051070b0300205007481180b0388589600c0c0d00c000e022041c0040780d00850992003d00c14003030200084810108000c981202000340342d00000750b00401100d8018881424001780841e0b40c3c4001d5448a05d8100d00700c21512508080340e04031ba1200000f40246e0950751240010030f00c020f00500515035940c80b4110015a491100c3c90086c45c0360b900044e1994a0b00070042c0a80300d0051200b102c81e4a4181400c00103030280c1c0c1a5000d4040c1ca4484851309a98080821118460540b941c0807001201c1d10008010b03606030042d54000340300f03030341000241c0d030303070341015825511031040c107190a401030302c41341104c0050b00002d450200c1041101c1c418950b500d070041000c4030390b90035032102d0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 218411573 1250 218410323 218410327
    0x9020f0301140f0d03030b0105070204140a0f1503110402160b09060f190213051509011d0a030305070f02091303020f0c060306010c0f0c09021b0a080a03022104050102 73
    0x120902d02d06603003442040d010740c0d0103804451140300182c40600380400040505a0b19801d42c1c246900c13075420364800d80c0d0b018000700000d10038018410002c10080340c8441d81141010380300360000010b4001c803900c06645003180304d071041c15641c030540f20303072406400320f0740283d400c2c000308000d91505001d800d10340c0e00480311a80c82d42400c140303660400b00000c0224908180707000a005150560040080d4042e02c00b000c0180c44002051000d001a90164480c0394429108480d208800011000909054000f41c81e0950740446440032005e84586d850b280c41c1d40000c2112082000c40d026800a101c0107108584d041001000b981c00100302800a96825030201c4106004204054041026441ca00c50b0b22004100702004000050158400200128100415102c003901005000341c400c421040e448403007103c0860701c0711100d800a402c10101c2044003007507000c0c005903154000c14090f0405d80c000303100300d182030010074050300a51b0100d0000074043d0035181e42c180e01d089511341d107035001d1031148001503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 218412823 1250 218411573 218411579
    0x301090b03060702010c1d010219140106060e06040303140403060203090d0f0e0904080a020a0b15101106060409080f18030705030714090a1104080c1302040e06040e0709020f0301 78
    0xd03152a200403c1c1406580c500050a20b003641c00200b0002c88a6003040c07030200030308a20740100d0805002d00901c05595032541400d00030040d00b5100c800c0342400e0b41c0c0080204680e10a070407100c8544a41c40d15401032001c010902c00300b072081c05039a9217040401c2c007440c50142e0300e9072800c089900440da1034116810511400f402603920240803010b0320842c0c50583c6503548213400199184a01420040401d8800220480035038001c0c000c012020340c20619010360343c174140701007015001c08403261612420032000c0f5003000c039000b10700a5070031601a0b40100580d5888209010007042102420303503040307009004007006450000300038001000c0c1c4141e088040c0a101c1d00f894036001030741e0443e07442500a40c000b0b02180c0d006981ca00c005200442d5880c281e6101c182e0742e03000030300f1642e408000c486070005011411400000d13074000406002d5070f2072038455110391202c40480c0a40c0c002d107008076034050301007002440c2503003068541c0d03081c08003031307030245513886940e07030126440a0143c000e5800080010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 218414073 1250 218412823 218412829
    0x409020901020c09041a04060e03070c0f0b040e0c1810170108061504021605010612051c0c020d052e0e060705030c031f0e01031b050102030d0c0201110301090b 70
    0x14604050050ba11301000d401d06990303566800b032040708915041c0f0001c0700020f06202864100100080400381520760322400da003405101410b01d030040e488058451480003440c03904940480b0100d40403800c4aa006803902a2955100d52180110700340307948c500f00c0c1c0303900c0542d103015446000807110b072104c01481070401480180200305900100e02c98200341c04001020b10191801c0340901011a8016559000d83d92026140701042002424561800d08040b5802c2030004504604c18007039400c4070042d0141100450a01241c007100800007880700c8107020050400c124000d150a100f030090319040080389031501041d008003101c0b000e40c04200f10012480e0032030f40c40f4a6a58a00c1d08026140918055400fd407040c40090200307480b402c40080040c040b200144019010b031407112402e444401d56400b0491001c40c001e00003681d841800d00340b504400d600b86245041100c006801031401d02810f0403e440003040190024003e5548a000c00ca070a00c00010045010306184000012550302c50014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 218415323 1250 218414073 218414083
    0xb1801110703020603070c020a0b120103031704020307051c150510080303060603010e040f0f05010b090108010b1005030a0e07030f0309050108071407030c020d03020a020f01020c01050d0e0a08040902090102 90
    0x5642007104140b0140c1c40741c5040f00d43c815020300744240c10003c9880810000112640580f03036180740407421004550041d102c450480b030095030b403c1000401c040004d004828207490096040c0d20010042200341400329801100103102c0c0003406031864243c8032800f811403000501e00345141c0e01c104000d91060395640440140182400460561403c0c0010612901c810701401c0c0f01000c01c031001404010048c41c001a000f81c1c0300c2d03920714136400d075441d01c2400b82880c0e07040184954000c2c4004a207511051003480c040741c8004002e404410000c580070b4605500181c9610303070064440c040503980880412411005501c103207524400c000160400401c10020740c0c006a04001d006401c0c80301c40c561029a400c0f000b031b584102e081d96402180b1b000d651032419803100035081000c60100205058011511080d158000d4a4029000ca00d62004a1700c0391a140d4295010500c244502401d00343c0950009264407213200403500c14203d10385a0380803a8005500020415400080d680d015580c10700c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 218416573 1250 218415323 218415347
    0x2701060f080708060c0f041d04030e04050c030a090c09150503120903280c2402010203060d0b0a0b031f0614010e04090c0b190e0f010206011a040b1801 66
    0x7001d01405401c0000c441d440b10400f0f082441508008640c881d0740c05a41d2046a00a0400702d920149504102d40d000b003a00000300c03004d81c00b09241c00700c00d8080342024010184aa070210340d03050f22350317600d01c1c001074003c0008020075a00100700c250007040d482e1a80c4580e0920a2007035100e124054903180c10036180c110f000c43c41c020050028422042c5039100010f45403c200034480c5034034a03031508080c442c032221008000281125261402c0051004290b0340c4d503811042182d03500000c0c038118a9030990a03480207940c0c86802101d10b000d44030101d801c03140001c3e0000003940021038521800c80002e071504020819100003080c0c0007103000c2c098030881c85140020456060344021031161880040c200c00714480d0002d0080c1e88420504081003480d000b80c5000d0b11240701840c0d1201c0d01140d030030449410005030900030421424007166145460300c0030107203440c016401000160f00700000300b20070140002501c0c003210070601000c981803022501800d5000f0441d195800042c1c507040005041003a01d00d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 218417823 1250 218416573 218416589
    0x3090b06040b01020c0d051c09180603120507080c030301090c020624151308160902040e0103170c10020d0b091b03100801060e07032703082701060f 65
    0x19503102e05036600490800210607040b03c607140780302018208103051420703d01d900c0c003480d0302180044808541001119041d100c0110021650b40ba034113540320300b2a07031103000140142e500c1d0040c0142c1144140000c0c58114420320344d40381006241c03a249461a0805c1e0045c0c0318041e2250101d2500c40d6040040c0399203c6a4203009010740710440104100303200035001d5a03400f030842c28142c8a501c900300030171104585030010039525616558000c0b00d842d60803e003110041c501482d41c000030a40e00c82c2c000c0e2000c1d1040c00d00f03200c0c174603407031030b40c03649800a1240f071080b640270002d2190071880c103001d02100050034000c080c0581d8880540078180c0c1200c082098192080344443e050012440e8841254502c807000030405650b00e03101d02001c03608400c416844041d040d0708200001c5a140d1444280078040c2520340c07001d110304904440c01c888240760301144c5092030323081289140c0100f0b100b03212103508400d2400f0024500c08845c9070b08404413014241e103031945e80d100c0c0b1041144901d0003503e8002000a6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 218419073 1250 218417823 218417831
    0x6061d221a0436080409050c19090519080c040c0e03061312140d0f06051c0b060a0b0a08040201050409020c030a08011a0a08090708061806160503071b080a03090b0604 73
    0x591341c0c0a03c0380254012248103075680c43c000f82d042202c5100302e440f200464501d50344a84040c500040010340f02e8003819010720620000b400c0788000d000c07004030070340310594064038145d81c007607051000404030301c030551081010009001611f40c8003480500d026405843c00202c8050711410801d041200800348202040000d2040f440940300c400b080d02c0c00606040c2010510808105148000d0700081d003105902a131031801c8040314201031178000300c24078800d0800d482503a4480d010043c1090300c51003071800e001e10030000030380c080380f2403c41550f2184c0705050280c1801d8a8550715800c0303801075031992078a5480021900c00315a00101c0c12401000740c220040141ca038100781440e1540110440384041c01054030101d0840c0f8400d01c000005065a5411606140b4003604650780d0300e4180d0a0580c1a8001d40001c50001c00c4c0c540074805804410303490b201c0c595269220708980262181e8049014140c03d5440000001c0e0024001d011807441641c4c089001400b030300b8411704d07502020f003503148580c7c94 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 218420323 1250 218419073 218419181
    0x12928020d17070815041113050a03050d1101060f030c051c031b11040e0102030f010b0702030604030e040b0424060c0f0b071206061d221a04 62
    0xb802c0d21640e01540034604841c4644551240e0401000a101807a6205050240040942d00c9600141c441c081411411000560752003080c08200826800080c050f500704080c403a40e02401841c00003034500548000040041d42c8184000300520180c104a039520003821080101e85040202e6000c0c2c0e1038410601085044280d80c040c1081d07604032824800d0000004e074032001d1112031040885581d4014100384142c20b41200c105000354421a0000310304244000041031702c942c000250f0307289940c0a0001c00c45034440d0788041c3c0340c0c4100e0142a45c5c0c4540c86040040c41034950f8040c01242250450781601c1103459020700b580228040d0b00070b0020000d032150803001184d40b0414884869070040003480594503003c504642514903100c80c0681542071400c00141d56600401249080c800e51580e210301410020401204841101d10f11280c1114484c40c58007400316503100b111032194252500300c024445001140c1565902841032810000c900411030042620034040105940303403030325031400c040c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 218421573 1250 218420323 218420357
    0x90303030e01020910030c05090a182007060f0603020612041401180b1e090601030b0f040f0308091f1e09020a061809110d0e0303012928020d 62
    0xd208900340400d03031681207c4c00c150b03014100b1a80090b0001d041e40780596202c08074200080340100c10b07040c00510f0610b2201c0c0707442c1075491480400d0300d4403050750318080141d16054041c001186407a1520741daa00800030060761004010910b5242e0560310b148545000d085c40a4001c000201c014103070b9051604200c108500038410b0700c0c001d944410566010780322085250b1140f18402c40c00004040c042c0c050008840c1e0008076681203034819071655603540d90b040d010015095050340d00030104800e850b0307000b0010380214841540700d0b0b0080110b480c5000348030300541e80003d820743e2040c1c1a5a071034840341c40701446c0520360000e0702c072071841c240043e19140d0f010409040341d500c00d41d800c00402c00041e59203203880c1a103403c01066600340911050030194007040c0f284c0d00001e0443e44e6a4503007100c17581300e1000482524100c800d0140b01c0b007803801003080900c008502000740f00c8a1013000b0400c140d8000c4a44002111040c003903c40754100d40640c0001901d0b00203955401028801441403070101c41c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 218422823 1250 218421573 218421589
    0x3050f070e0915030708100b0102030a0e090a3e03061f0203040909110117040510021e030a06030c060503040506150402213c040503130303090303030e010209 69
    0x320054455040b16503c03100d0818002ca0401e2980d90705001daa100005c45020005034001c5910b14298108460040d200c01a40e0ba84130311740007580840c0700c100d030b001e4092400c00b40c000d50150441d040402c210380072442c40c4062070001c24500c40c503925000495062000c40d02207980c010f00016001134610b040280020701e0846a201e00040103148420300101000d209000396402080d0102052003104403506d401034080224200640c00a45503020101031aa20003c440d070249070041c0c05401c1c4106070081d0b0b50081d51003a105540b80301c0c1003100c0858421102c3c40110700c1000b0013a00000c140e8110315005040100561108080250a00901021400101d00c40d50043d4252844541d040b01030070105000c0c0c0145207603100808205000350445009021100d44034000c40c003c280e060100140f091484034200f55411142c5802152001d548000000740581c1c000c0e00800881e07091030081c0307284030b2041303a80c1e800c22000589030700130400800d81c16020b03c0014020743c4000b0350600c015180451404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 218424073 1250 218422823 218422847
    0x14010b0603190b180903120c0a0c14010207150e0601060518010e1f090510020a0c0308090607120e130501051c0804090e030301170a03050418060b07030f03050f07 71
    0x120340d03100300c4903c050b51560301c641c8401102e40c096004500d040000280c076a0008400d91200c845500c000070044110401280d881d00c0300d5031126407407603109407a44503001c40c110f0940d0b01e0541d420008100818401c410315260000503800111b41481c07990600b0707040a5041c1e001c0c41c2400f00510001140c1141c0c0d0000808004003864080c44882c01c10000400c4015800c0d0700c8904a01d0034030044090b10740c00b4020f1380c1aa641902c510600c40350b4400308236942c40e005400980041b2602c030051000800c0b8400030700d2000d038000c100c241492404d40b205c459064910314005e01003002d00d4100c2001c0c0c1000c20001c03124030f0340f28000700b00a62520002c90010505404d104900c0b210714802401001001403c0e90040e0074140000c1003014408852240c2d40d070310a0084c10b0610800c4038242006a01c0000d229010035891760b9410304151403c920a000000195000703901035807a0749001c20480d1002005d00340302c1b8082e40cac440d0407c030f118070300190071520054412030765901d90a003081030540d000380c648858 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 218425323 1250 218424073 218424121
    0x20f04050c030a0507052802010e0d020a030806030102070203030a0908010609052701090605130201020f0d0f080403090e07270e0601052d04030c2103050a021914010b0603 75
    0x140d5648000b21160312031b86400c81c1086007004000e1f9681c100c0141030203a54038064000300722900e45c5001c0e00c0ea4495812400c400160b2001c0014400a88030750b80d0650444800350015007003030b80550010f402c42d0400c03c03c06000851000040018010074005c0800400881008102a0402940020391290050340c0022802c0c0c801101ca1041803096100000d450b40201c0b08001908044c0b0710920407003000f003000d130300511030044030000c07440002c0f0721001340e4641d9031a488120b800c590002d80c0d80b204010025070522545100000d2034a41c204e09c094427802141d6240340a500307030810224801509441c031205030031080e403030074002030580303c4d50780303411603804d00700952a003c1407540d95401107042c850035101c91080320326150b10f074849a0701500075a84281116031100792038820504507115035554544e00710001546460109008100614000342d561040d1050619602011001140e4103a4200c3d0410003040e4541c042e4002031003241c10361101120480d2660a01c0e10180030714401c068a0810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 218426573 1250 218425323 218425331
    0x807110c093301030b01030b1c0c0305010c03021b1b040f0209190305010c05120f1b1305150702010509060f07020a0b0c0105010f2402011d010207020f04050c030a 71
    0x701c102c219210000400361840302840b001c09000d90454001c0d65203840e002d0100f030038034480e400c1c198024020130b90314400160580d0000100b0b9840d000c001c0340c000c403095842c4070961038003002084003800343c80c1c071109041e1400350b80e506030441d841e100040c0103200c0ba01250005514604000c6160030075a1043c0000c0320003150700604501030600138494003541950000013030498080c00d0201071040001c49001d0f4000b04841500c1007001d42d110b10542042102c9040e1540c00508400e4001d40d040390001d040307081818250461107040b044650100c46611003200d10036001300460303e0301c200f01c21281e0061a4100342407071030300ea0020340713030b0300a18087c544100c3d80845e503031000504000030b542d0440d40040c02d000c82c07603591f2110000baa51119001d540e0950070300001040c0c1900141104040b103880e0250000004400030100c04000120040403045541318072100390b800811038150301e4a542c6440005981d004144100010030f040d6400440c0214289020010081050001e982d0b11100300741d8041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 218427823 1250 218426573 218426581
    0x5010806040f0908030c031506031e09071e0e060109031205180a1d0741040f1a130303030c030e011b020609061006051c05040f0516031e02010912060c0807110c09 71
    0x241002001e0708041111803040000c4ec50007105200e2120485883d8a201e007181d0f1980d42c01150000380c54080505409025102ca82106100c1c8005004141c0180c500500c40d02042c00040d9421525a0054469604001c7c41e00291a50024119003140780380c10b02035000c0317285200d1140d803640d483e03501e2a0129942c81c0c80c20728003040e40c0250f90b2010048040c031590340b622000b42903c1c1100c0350148411003001451080c028540c05e20858051180e03684881100300c0c9103623400c6015001d01c01c54801015200c24411017107200c03d00451068200d0b12500030040c1c00035610003481c040c0003c01755100e9501003010300c410030300451041c0e4182d44081c039100382d07110070045100d015040300c00700040c6400d152108000912542c0800070500714494015070303460140c0c04408140c0c0f80750310301020b00401101c00c1900d60441400c100c1c4107543d8418141400f80d1682c4041841c1c0c50090548107850441d11122046184d6034041a01c680c451102d04101000031642104969075800032002d80c0d0045402401003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 218429073 1250 218427823 218427841
    0x5010e0117070306081009050a06020307110a03030b131404170c0f0604060c080405070b09031002070b060315090a0818030f070602060c0405010806040f0908030c031506031e 76
    0x1e846003800001c080580e500b041600180181240d1044a400307024615000c80d40fa1254016031501c140c02c13000034000c0c94a80c0c1c0b5410000c5d0301c054008424403041c40a149541b00f4180450002c1500a45000501e80c13104e50a0200c0740c145d46480e14030746454803803030410804040d40443d82040c1c00c04034041e4140b1b041c28082100d841200c4a0705e00520554030680c0303880e080011340511642c490402401244880301007600c0c50a0150340090080d004240305000640030440544444c44004040301c50940116030b00d03a0881e8002c042c01c1d5030120a041c1000020308007001a20010418032003500b016242c1900015203c00e20b01c5070050106800003400419483c003120303043c100003401020b55502d01409400d0360340d1284079114100140c041d61000411007035075034003650101c42c81a12403130003c3d0b6401d000c100050207051401c202150b500e800d200046030f41b44000d107100340408540c8995074244100301c100201d280d000420312aa40810822040107001c0516400514025044003010388500e410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 218430323 1250 218429073 218429087
    0x70201020c060901051b0414010e0310020a030f05010b160f02010c3002070503030f130e0106050301092f0d140c0d060812160f06050a0e0d0f0905010e01 67
    0x601584180003d001c4204010b42c0081e0180c0c4041c0d618103400503440403005294011480791142440d0039400c019030a5001d00040d440b1007400409443e05a41126842d100303c1e001b90203520000396403244208401c240501c1160302422003039a9890401e1054515001964100e2900070100c0505030502004c590080a01022080c0d009244030100f82003c103801030510342030402c044c020102401404085030010038450151350000e0007644c541150444000001c2c0d02200c11608110300c001c0d400149800d030f20640f81e02030200c0366206a565490882d2500686a00214011051894005410071395800d07443c548010361200702400d450300d000d1195030f0004d25540c8078014030100803404208000030703860001c0900740350000040282684600c1034030780c2d808954012514503c010010b41100b40c40020002c0d1b0014801c3c1c1100b02c08244580d126010f0300c800741c4151200743e480e8402417102030b10601007418440c1c0030780744c1104080382a24008242c0c1c4424420181404030003005207038241d02c82c240d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 218431573 1250 218430323 218430337
    0x11407020d08070b0609040b340302030601090806011206091110020f100e060703021c02071101030c020c010e040b0a0902070507170f070612020904090f050105060a030803010b0307020102 82
    0x89820703480d04101031594000807007150f40000c031030b001a48516100710310901803a000301301c20b4015a10405c0c3d4141b000030301c0e0a01420a50402145203206090383c0c4560780036412554050b80340d04003030b03002400d400260303001000340d030304500018400212041900c01986412000100d10b581e8142850107130010100805500030b030203c41022200e540001d040e1613080c0000c01110b40e543c40041100c0121800800380c9200c5e50400301c00b140d81c10703110f82c0250200100300c1e10101c108107141480b180499003c03900803140c00030105806150b568241c414000c0b120000e0024002180341e800009000040303030403500d44190b80d00c9107410402d4503540d003000080c001d6030703808642c2c941b0b65084c160b80e122600d1207044541c5c0e0b000003042890b0345002c034024403461a05801484154284481901da51022060030115140d00b8400080389564500480750002d000f00c040c0c0f243d400c3e180c10f2550030b40c4e0005000300c0c0640240c2008200003045201202e0445441035015034aa44800404074007a10036a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 218432823 1250 218431573 218431579
    0x809040f020c012c0f07150e030f06012c0a0f110a09080c0102070b070807030c0206070f1101110d0809030706050c0406020c0405040f020f0112022a070e010501140702 73
    0x880d044511911a03075489091202044010240d21041c54086903039000605510016410a45d8100001118401f82a07803140d210300300f09203004002c1010a1400d00e00c0160807a6680c8a40010019071048405401e08000110175810019910f90985801c040740617080500d425a9480c0304015155150703c203465800d002221103980344030200340280507200501624445018282070352140d9800014100c0071142d04000c0c00707051240d16240e04455810401040d024044480d042d407005a0f9180000d041c3d03035110350100710002c02141000201140712208031410310207040082004088002080184802d1b903240503040c1d0fa5400d01c0c5142103014030300b002400340c1c2c141424070001c6041c0c030000d8000d55255a08440c1e42100c132008100c07c1d80c00550b4060813111390300c0141409401c151031041005c080c10304006c040101810000801c0380c0c0481001701d4014a502152907030b1b195480c04141d86105224001d200c51801d1441e00c1d03417000c0e010f01c07502d81800f01e0280740c0e0103000280802d4070b442603001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 218434073 1250 218432823 218432831
    0x10c020411030709031505040c030201080c09041e0f0e071e120302011b0203040e240924090402030319120c05041a030411092806050a0f030809040f020c01 68
    0x183d001400c8548140400c98007814083c40c010113481c1d851140500c5250040140c0c49291300e1600195241400138065804c014020000710809031141d018483c0c40001e442c160385803510700b0520344000c580419800e0540d95041c0100e4902103040040d042040d5503e030354001071100452540e01842c084c00c0c1e8002c0820280c0e80f026041819010761003107804040c1230320254445c94170701d03108071b890b40f207103014000071070040c100460b566050075107110348041814000d80721910302440005603081000c51340c00e0f4026400300f60307168043c0d081b0b010b034030340400c4143c0d0b0903842c50030960b00007601c900860508241c841c641f03e946c0301000707100741842c0c825410300301420001da0b540e079400200140d0290180d550810108120007a40c3c145d8074080340e1040c0c0e045910b2265034840032003004044074000d411080340c01d00043e04010404400003101700c48000700741001504501d0001440500d200c20342c48103e451075402c17810004241c52000302c1c4c048420441c1c0010386140d84e41e491100074051011407808961030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 218435323 1250 218434073 218434081
    0xd020d05030612071814090a0807110303070f020f0f280b0418050112050d1818020d0b03011514030a0f030f082202130e0a080315090411010c02041103 66
    0xb41a6142124041c0301018400c28080074400300b451841078542141f85d9225200000106407403001415200e0f1240010448450303003440001d03d183c02030b900544118149180c048210300c0c0c1115000380707400e07064a21800b004010400a9500b41255101900742c0c08111040f404020246480101900c00c0501c90b43d00c450b00c03090000508040c2c403404079011442c060000c6074030310003284c0141070030f5400b1006001d007502581044404114501c1039041194004401040300d441300019150454020307500161180711050015003a15203e5004d5400303030349050308403841e08482d011a10150b0340250300c9050b900420001191500d10110000382c070054004461008141d8030003100700050106075188403da80f038540418a80307041080740d244920880a071340c072005007464188030580307540541002501012000ca224208015020704445288000080151054290b029040101401d48000c8110318159440c001c2c05150500706905110b0800310510440d66150040301809c18040d03900c41e00c90038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 218436573 1250 218435323 218435339
    0x7080702060c0d0306080613060e0c0901090c0e040605010512070903081b0607141801031803050703021509070e0c1908010602070905091207020d05070e180d020d0503061207 76
    0xf20f9040d10030f0000c0e00700034000a85000000d1420701404440c12459020710b520303034508006081200459501d800f079030f60340b140c3c41c0d914010481d00030103000c040424920300c07140c0020027101c0b146406a110394540300060083e45d1340241510341d100088440a906912540000e50300c252150740001c1040b00300281d506001207024007070107480d1016104880d5542c40d040b00940ea6180307807d03001190a0f10902185d14a40504882d94a0044040c1000140703036642e800c0d882c0120b1620700c004d41c081000010001c3c20580c1c1084603042011850b201440181000203400791100c644c0d05c41d80b1003480e003440214001e020050112082c91070307140c10306d50403501c41401c040c007072980900c500005802080c80010341407080e03000c0d0300e22840882014015121002c60f46003205c0c2c001ba402a60031076041d180200020f0b0003004603a02600c15600850b04c50324011040c00704800095031410b600703801100c0303205041c03a00050901c98050f11400d0254507a070354071000c00c150080c0f0741704c85101841030342c0c40000c15403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 218437823 1250 218436573 218436583
    0x18240a090e01090507020607180503060901140105012309060d0f0b12010c0c12090e09060f0a06081b0f060a0305060315040c1715091b010207051507080702060c 70
    0x107100101296070390ba036103000358001c40d1001c030b42c0f640c0581c000d14001050b50b841102e1641040741c200c0c426041480c2c0f9400804c1c6098421123420556a5580c6183c000108408007a103004100900c0d000322000c007140450030480c005502040403000003c9090481070765998161101c20001580030448040340c002094084c1000940c442d0050741c4201d80a00c3d02c0030103019040912002c0d807241410030306c865850500c2c512151990301d082207030008003c180d41103054406805100307480c0040c209401c11044d0b02c1192030f4003074410300503640713088002c00035078a011501482c504020102454954040c00100e420070302d28000c2ea560296000030b594505079016804940643c1c0b080c1c0440d101b80c410b2107510901500241d4014085102c0c0b1201007004480c184a04c07203010815909803220503c040d411445000c00554041c0350f1038000d0141060ba81a00f0380ea003030400c203c01d10080c01414036000215005401d10541c00c803084400003646018404d8200072540381c1a8090a5141e036a921840c1d8a6224 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 218439073 1250 218437823 218437829
    0x1d0402090f0c074e02060c040b0306040e0604030203030103030206090c090a1e020408100b0a0b04050904030e03010603030c02030f06010315020906040f0602071703040e070c30110318240a09 83
    0x241110104203841505c0007424a01c00ca0001114520341410703c070505071035400c0100040c0d07016845210852421808bc0300c040e00441c8660005c40c0c41e94114075001e07042c410002c00b0140e40354068000354480d542c58404840e005450041c00084204800d98403101ea450098200300040d4000030700002c04801c0040d01030b1080a0480041101d60b8100c3e0030005124264821401d05c5881400180084c0c80d2441010381c10503c20708000d014148010042400d59a207607006a000c214002c4941c070035400c051005c1c00010310303c8009003041c1d60455891354884500f00314035202546d804140712001752a41000c98000e044a0050525503a9031386078020340d038001600640e41001010030303800300c0c0840000152820786103107040250440d540c0310b00c2250061600482501d00c80e21050000204458480802007075034214001d0303c00c00f40070380a000d89207600d6074010710303900d0744200302d241d41c8004400103039001054119620039101e19003403a00c10a04d0b43e0304850245600c4005250340f41541c0041d100003c0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 218440323 1250 218439073 218439203
    0x7050a0c030b0a11090d1415090601090b01080609071b081201060318051c03090204020714010b03280201020106030b0a0b04060b09090a050903041d0402090f0c07 71
    0x4c2001c401c210200c880c080d0300102a0441c3c8000b5401c400203640e090f040a1170302c82d600413202480c0d03802c45049070410041d02c445004c0d421810060110403d1800f031b910072010282425101c60070141c0c04140e509100034500410070440c905264940d030409240703001c0701070b000146640c0340e4080b240c400035010000c1c410100460714280840b071510a20f58041241c42ea0800b02614110b90381c0c100084007001b030b429501e02050360b1a40200d0040e9543e1000e08a81402042401c4c004449460398600b151113030345030544260700414050002e00d00030784040ca007200c3d401d1002c40a0409520050f4058a0700390001001103030340004100d0351014660001c50540c2c0201d03010b01c074460f0f9a400540785440785100c0c2e06c0e0003401d6140050f014811513000243c011030002c0889181c599560340c1080100b010030211000620000180320552a042900940020140326980543d0805200c0030040d0b10031804010881d40101f4598842c0f000206400035030b0401044404584c1e084545645040340410404208 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 218441573 1250 218440323 218440331
    0xb07030302030114150304060f020d0c030504031206180902041506021c080c0415020c03030a05130b0415080a180b0402010305070306141504150305040515070e010507050a0c030b0a 79
    0xa414502003c02c0a170a40514030500d14580b12501c503100a0300c0e110010f45440c5030200010704610003a4032506600c41d4403541c1c001064140b620b00200754a021400742c010880c14108244210148030207134a00180301da0100195980c61440840c4c064000e0f40c11000c0c0740550441d000544e00d4001c5582c01148030304440350818880141d006460b104001d0351420b1402100340b0051101d01c4c0c400303a9a05c42e45000e0b004488403054201c00003499540a031903100d00046000c14603512554000b06220081c3c2158104141010b042040041740e01443d0441241004044408164145070592042c40360840c4020410712003c03090904a04480d800e8803702d000a07e002c000940d050303c64824030b000d82c6e403424184840c250030002003103c15401000105c4804004110020b0314202000e410010003600361001314052509040942c05e00140146504084c1c110508201490350301c9069008210803d08141c0d8131740165040462811075901801460a41074690100522414501c1c00788289403d5030180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 218442823 1250 218441573 218441609
    0x80c0703050d080709030b1905040c1703040305101113060c020f010e09161713030e271b070f020907020d0801090e0c09040303020409050a02070b0f040501060b070303020301 76
    0xb602e1507000c5581c400022200042840021f01c00401140c20038a00c114542d07041903403c0a1804603903096801700c803010001c203400c114180c42e0144804100f1000b02c050340c01c10b442c50316044d071a0488410041a400e0b5500620360302403025505982012410070404400142c9550028105000400e0182c2c403803516641c03e000251310a17000c9001e280c20203040705c0d149403200d010640f4a03031301c00540c240038402003e1007034054012165000b0301c24883c070182401081c08ae030401805110354201e200b80110105a180f403480c1c07901c0008021400c40880c00e0040d10740c2c54a844007190112541c40c80707000000091000c0600240340700d2000030318021100540300303868010301a60b8409034800780801140801c4010001440e00b90b108083c03c0820130305640c120155840001c000120864086010075804503040c85203480c10b02c00c4c1342d40880c410104501d001950780720781c10112070040c22034070008004000103007080020340181005185031310b0203640380e2095241c00350282d0024041c03404400700314500c01d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 218444073 1250 218442823 218442827
    0x306051302030105060a1119050c0901060804030203030c0922020d05060613120204060302041803081e01030f151d01050a0203040b06060d1407031d0c03100c0309080c0703050d 77
    0x2c038101c5800909a03450300a5001c016038110340303c5400d10f0014001d41c00a4014079170704a020b41d201620940290021400000801043c1c1d0010b030070840c10841ca040c100000207400000300ea41000c03900700d950381c5468101000230300318195081480c5040d100d0000c61020145190041c01200003880018401c691780e031010302003d8000d841601d91880d000c3d541c1000186082c61003c800701e030003d8000300f54580c41c0c0d00401c0681341d08202101c1e220517240250814558001040c07900504061440fa06000802c160f07a0303030900040c000035100c4003100b1f08600c10032440000700310064103500070034403030800b0341d245450320031a4040001490f542880c00091b0007541903c00c8a00c660f600050305c1c4090f482d42028000302d50042100e0410711580c5070740d070100e00503817000030502c1a00079940100d40b1410f9040e03c403165114298906020381e001f4034960080755804035503144001d542800001c0e1040440d80d0441c040e04c01808090412480000c2e0504490030100d003007010341b40140c0484003100f0078102c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 218445323 1250 218444073 218444077
    0x901090206030a090c0905090703021002010903021e150702071706010312200a060b040f14040201052b060e090a1106130b0c06100503070f09020a11030a0306051302 72
    0x81d8085400c0000401110503603014110050141c000d6000c407640362a640341c01c490050380c0c0003a456211010400852504c2d034060118850644020f00140c88940e502035038034261101c1100480780ba0000d000030104081240700b0440908140c061907a06040c00080d49035022400788115040360140c2c0fa0350000c80000d07242d412aa40300c51003440300d40e4503d4046a14209039000c110300050a035003e1030110104001400d112800340f43d000480101040c1044202c480134000319030101d04048240f08110709103100e1550064080c02c00f1507036030380c2c10b003000c501160309034008a6100303282036404805455103602200a50b503007a074107a40d00c0d031502c0c60040d0b5640c1502c10000d04444088001e82d0f6942410006040e107100c411045002c4281c40d54803141c01d03a004040b03040c1685d8030100800c01e00034440950301005207001c0d4082d2905d28103100351508410894003e4041d03154000804079442da2080b6207040d5180e00c0d03c400c0d40d80f21840000b0040c0685000d1044d10b1042100c441d90090540f00351007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 218446573 1250 218445323 218445341
    0xa0603020f01050f041202040204050d121b0209040f05010b031e06152107090618110901020a060e0c0d0f0b06100507021903080f0a080121030809030702040c0906080901 74
    0x83c0c1d0303003002d25121040310300740946e2104a03003080e020702c4000b03642c0e21100c14212010f40700f03c00d00c0c50018002d0348010318403182d108010410703d15025652015846203a03025130041d400c541a012004060308200340500f680ca080d0980501c01c00c40110902084000c00241c1c0395018000d980c1c080d1203111182c41003407840340b00b081e800340202e81c20303100402c220818180d82c4070018083d00c951550381c90a890441d5001e60010004e8840c3c49006100b42c10035100e01061021040441400c103031070200001d40d03c8001020040c1065912a12881e160204010014168030024070050080d18585801200055880c204441d60003a000200703400d0325140642072400c2c0800e0381d405041c06107540801c217961040704110303510600c41c0c00c000700215100100600084001b4658103540c1c04031004004c0031440140e20484800051400140610481265120302d942d054030388803686898043d0a10306500c101d4400941c0705180400050440d80c002203410100c81c4180c5680e00390382d441400304c034261035801d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 218447823 1250 218446573 218446597
    0x18010314040201020705240d0203090c040c0f0c0f05060726040503070305072a171908070311060f01030b0c070b0a050a1d06010503060c07050d1209020303030a0603020f0105 76
    0x4d080c0807038101002c0040d50004007507c404211549295100c83d240d1210650411043e000000c0007a62402080f6924210009071400c04c22081020401058807400c0d0408508000c08a40c19005000c8082c0391807180c26045400d8481600307041c031000d808040d400610501744400000404c480b8003800c138604e071180d90410301652070702480d9982200c4d03950240d54101d54030907040301d0a9500050b4010031019070360b103180c000c240c03480c245001d424468020002d10f0440b0350003040e800891020444500300c2c5254008038240d00d99140c0c1c6000d51302e075040100511400d01c41c420421802d8142c855090b81243d005103400e21090b15030b810110050310a00c440a041a8610400b180d0351060f039031700003503102022220000b02c6219411151003921106100342501da40000018081441c05101154102007040900340c5132404669071652138012681d41c40701801040582001d84201b0380d00180d514039801810749650f4070b00313886900018082e600080c0e005009003105400154051812600b4900b044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 218449073 1250 218447823 218447833
    0x70605040e062805040e0106080a170702131b0e031c2303011410021005060d0b040503031b13090510050303120703180c030f0201090b1801031404020102 67
    0x4000821541480580358940000750103091840345850b01442015070300c0c000603c02c0110f031400341004280c4180661104c0543d24204003000300420006141e100302d030340f02e4040b20500e040359150a6083c0214000070750000141e0105645075a90340c1d104085c1d09880c28010741c030020111900b12415207a5581c0c55030036a01c070640c031550305801182101450501c40c60300c3c14101c02622000c0e2000384070050180d43d04070011005010882c00c0b035031268072101d000d8540242c002c1c0031402c001d5132080c96241502d840c1780d44001107240307500e030300c50611641a009417518686007440c3c40e00e21365941c42250340002d802010290b501425040030200c4410340034800300000014203140e1520018107015000300b09101c1992800a503a0300d0520140c280803561218524503841c1c48200074003580c0e00d04010b205415000b840441c0001e092055042c1502e4200e84071a00e01401880161000c10140d001510420b00c0803484099031880900a810079900a9034240000c5800c1140c10411101c2039400034050f07040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 218450323 1250 218449073 218449079
    0x905010f09020c010b041a0109050405070203070b040602091c02011d1e0303070b04030309030807020a03050a030f020c0f03090411030405070608061906030c0816080c0307020102071a01090e07060504 87
    0x14940243c9155420800001041245540010202c90466269003166501c40c200380d1150343e0410b94040050800703450034401440c0a07000251288101d400040147d401c1c500030a06010351079050b1b9040060140c525840000155108150b132203842d001280024034120401a41c0b04000d070700001d001d00054100a03076010042c180d08a070500034007101da054482480303c200400c01c010040d500560103502c0010f1101c0c000c1c18018000d4100030050790540d8410261080000d501404403a11000a49000a060264a80c103030010b4850744620515a02c202017103a28401004802481d0303203101143c04109404140380600814001124050071a03040070f0010441d5a0185001550008008061042d907500304010340041d0b243d10307084580083d503580c1c0e21402981d04540d820303800c49a0074200c030308a050074100040108400400c028815400030010441c001d000b50191015954030550308550140c1d1074a600c0308500c000d11403c0c20b11424250f1425250001084210903a206030751120f16040c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 218451573 1250 218450323 218450339
    0x803091c2c0109210503040306090c060c08070618050f0d1d03100908090d0c0f09020903030703030b012619020a021b1302040b071b0609120f1703100905010f 69
    0x90300d2644c40d1060b603400000300700069400d000900245201e40ca0025602c440d134188001444500e402c51414082c51000020111303826009581c4100c3d0320100201c1d01c030241481018400c1140b1100401600c51040b46050030407011480c00280c1507503686041c4845c1205800c44e6214800203295601a044003c0c2404260041d8014244041c00b60400a2800f4140800706040380d041560640c0c40b170501c990207101ca544904188401411451025400d0000000000352244241d1500400b4195941e2018030203900603e450088603149200002c00450100c03090200c00002300c031083c05503012164030100b48150343c0b00f80c0300340448590041c01240051030040c03004c00100303803819601c03c24440300303480042c400380000d002804507680c609072624058a400403210140d66180c2c03540b001282c03424030442c1c1c1e11043d03040841d02e0740b1400c030520246d0f6003000c003001510401c018290591121500c0442a00840251300451920420105080da01e20050040352800c4c01406607000d5450001c2101071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 218452823 1250 218451573 218451599
    0x1203090c090c03390c012a0318080409020a0903150207033513080415180503030306220c0207030c1a0a030e031204030806041107020d0803091c2c0109 66
    0x601711900001e0191102404410100701c030991050880301da0008003880c66506003d0050784410600361440c07000d40340da40e11101402030707003d000c640d15400310320260b102c1c0c4201c45075030003584c00040301a05150301d000c00c400a175110510603030205168101c80f100e840101d80000420b03c0f400086503040d40c28200116540010203880504030b659500c86417000301d403200c0010001091032030841d00261401100c00f808800900541144241010760200a16100441220b500450840c2c040300c40040b0640d94124004031040204121413608014502441c0c000a241c01503901030b04000d4400d1740c3c0e49000059000e44070b0182703640402d050144070005402500140451112001600d003407204a00c0426400441280d0503400500a0001e1020508243c41143c48030300201c19443d2901e011500480c5e11000c4038030008000c1d1a0001c000368202130180b00340381d4444910341100131481005200100704101a4207540c02082c0c0500b0310014080c0c0b40702c17071180080d00607102c0070115868055503000c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 218454073 1250 218452823 218452837
    0x2031b0309030706090c03120906030f09051c030213090603060e0f0a03030c0504030203100f0506010302181c050601060302070203012702010c02150a050301140d051203090c090c0339 80
    0xa0518000b01000048006002314070000c1c1d55650306043c0761a0003070040c00c2d580171211003044145086031072001b0072004100a00c0c1c1c094401c080481000903008210028400e140055090021400c40803e800301c0541044c0704880c080c04042c0580b08025020a48500c0d05040420503580400c850b200002d000b03030450f0248065506283d8140f035520b4001c6410103003240c0740b071440e90f03507209000244520207105041e001502841c08504214803940500440301012103014070403500e001c3c9101508034290450290194880f003510301a5a440d940075003c0d40005804a201c1d500b0215031120340e0380341000d40d94114101040c507d0b0214966001550015070110b816030700304d02505048000038860500526801d001c668070181d9943c50511240c851281d41d07039940e4880c2c0d2000c0f81c2c0d100401c0c0e0000d449045007400744403042d900d0b210a508240b4142d90b001c0c034a40c1007980a400c02000c164110051480360000c1c0300384403c580625a41c665a1101d0b11400c0c0141e9031030300410b420200e018030054084 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 218455323 1250 218454073 218454083
    0x6030c0301090c02030f030a020a021b060f09031e0a0501061a0906030a0b040608070602070803030f0c0a0207120c1809030203031b07060912140f040306020c0309100302031b030903070609 82
    0x90038a0100e0146c1555100701c481c0c04e138150300066846402d80d0f04110140c1d0f000e2961a4891001c1f000000242c0507101d10f0300c04c1000288041913001c00355a0610440070b000c00341c015403400c0700c41c0c8540c80f141c4449100d80140d8855290046c00074154089042c1a08112407102c9407a240101c10010002c0740c0d00003510f424074650341c0348000d45050725140310f920050901500100075a5141147c0285406a240c03c6510786801c10b1082c0180304814040040e04600705c4034100780c882d010420200d103440b205600c424000501ca614200610418641050568030340010310402c1c9c0b080a030b107034801c1d107014080090040e80104005402024500f104484116141150310724120305515428240c88082c1e4007030380c00c010166240e0881d1500300c45640320f0185103544403801c01c45c0d0f00302c50b800c1c6130083e071001400b844c2d00000c440c4c400c48030600481300841b100820603e14582200c000a000390011220310009032005c0e4031000d2031184c200c0560b44504c03860001140780450030b6032010084c2c1584041116 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 218456573 1250 218455323 218455327
    0x50d05010f06090e12190e120106141003021201030209060f03060a14130f03052110050f04020c0c150408070305010b090a090302100504030504050307140a0506030c0301090c0203 78
    0x3070040d90140d40b0040c90780038004103035051840c90007400d2101341d05044002060800c9502403039076912015600114150800902071784010000c1440b10b510900302c1c6000d54030f8031101096265812001504007001503c40940c42072110704250100c7c8660a003150592083c0c000410043c9080780c5256407010000d080d44e070900d00f1900c086454000c0c140c1d2001302042c0c40d0100e0306160740c3d083c50350903404140d20424289050907034503400c101414104001e01002400a0701e03003103669801d51101041ca420b013060201c02d24103648480c00c1d1012901481e03126048504121105103041d00a980d000418200502102c0000c441040445111021301c80d40c2c071001400001003841041c0701c005d00660043c0000301d0030700c0700c200400c40b00040040283d8001460f00b04110042540003d202c1c0301d12000300c00000f02c54483d410f056941303014540c0304070350500c00c0c203501141015100840904084c3c0994500c01c030b0b01d843d4420041030b0b0000f04c80c07281ca901410f00041120765059000307103041e4540350054034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 218457823 1250 218456573 218456591
    0x2060412021f02030f0709180e01022118120904050402030703170418051311041b1701080d021c030207050118021c02060a0e030708030705070e07080907050d0501 71
    0x12164940c0b80c15001e69072940881042001c1d44007050040e848203162400c460341074104400104400c1c0800d1a12103c65590710460f80c0fa590300b54103d0b40341c1e458049920488940e4840d08040c840d900703c5080100da0b00440849103000c40c0010104010088041c4803414070840a0038440140b00051041e82d041c4030300c2d4000004100e070140407007000c208001e60306507a1818296503c0d0050480740410510130310381810010001c22451141c1012030b071100c000112540d130000060090541040d502200c01074000c031089056810920800c0320390f05003c56071342d040ea41c0764120754942e20403096510140e0042920a566100c003088500e286040b035007801030500000782c540c6801c480a0141003100c841d40322000100333601c3c0c551401c0c02d075520304250440c584103455020480038028120154180007040b00e03058200c1e6030501400e409003074014100da40f5025a4104165209118491b604203c108100411130103841485618801c503100c1c1d004005072481d205c2840003004003860700341c3c2c44d9540c4420300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 218459073 1250 218457823 218457853
    0xa08031b0d110c190c12080d1103090114040203060c09011211090a0522050c1b03070c0f060509010c1a10060207060207031703090703020d060f0606050403030206041202 74
    0x1d040803003058280d10b500e50300c840d0005032401541c0200b040f07084030594400d000241071741110340b09031034141d0341110101c0502e15250707265002da08804001c0d1814495000341c4440b0103005588120702c007000034002000d19001414900b0f4081d40d0194054110380e00040e40d20444a0040030001c0c010300d0000c4048480c0d001da20116a0507042c081007482c000601c00d84240f62448128014000c12070305030a010368984441e1810041d0101400312298890300003c000b004910140d440f050b4000c4410306034281c60361100c903182d500440701200c041c0100c1130042500b22a4913044819140a03444840c13600348000c006441c80f000c1440211105218015403003641c14420040f507000b00e6290903105811424800302a003080d03000d8001c0da04640c48070604101040100b40e0120306014190a1307295a0b4882103042030404415400282d00300c6242841d010801005902410340089095010445540c42e00f00c121100c1c491480050f00690002000c2008990311000103101c540e0070b4011201d2140b8200c3d10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 218460323 1250 218459073 218459081
    0x303190e0316030201020d0f170603120a050702090f0f0c0702031c051b1920040623011e030506030718090302010605030c0a0b0a051201030b01170a08031b0d 69
    0x2001c0800e0b200d078a010000c558041101602c00d00290820406449418100400c9008a0380c0c0400c0c0c00003094020a4054805000d020114104c0d0640705654050003036000e4400d5211145c128040c00c1c01d0f0380000d040c0180c4210040c0512040c0036004400c1c2c4480118411039000ba8200340c0c2d041c05403031415a03683c020906600b8640c0255101e494403a070401404180e68900702d074892403590044900c2d03102080d6507c1e00c00c800d0720742c442a49003600c004a401c0c00c1046480806058100745000004280b00d25001d0925410601b01d42641c80c0d0a184200116007024003621011803400155080c0d076070507400381d04860350089019045580c030603030b0b881004141c0c0d8000b0035203400d40340c0e0312407160090550a00400c005010207174001c01c40c40c1d150301c003c503003030b5080c82c8542e8017001c801040640c64140b096044403080e18000c2c9910381702e945c5078181490a80400e10030300200100c80c2c442c000710f0440101c0d040f900b2030b401860480c00e43d501d14581a031118030001c2e201d214034000300074220244101c2e00c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 218461573 1250 218460323 218460343
    0xa020906070c05010e0102012a020109050303070305010314010605130506040f09120f1e0804030219051506040525020a1b03030e030610031b03061e0501140303190e03 73
    0x20241100d619103c00582203c280481c0ca07411a4103042c800c44161712500c0c05e5009884e1003c02194040d0750100e005c90040c04045401071403400000b0034020341540c19003055050303a006070390340003c4a07000c048a60032202d040c0304a54216110412261070801c60b61700c03d036481300000d040417a0a10307070708900504443d100e0008540703040b25404240b0321103900c10980e44666072141004260100001100c04a16626040d80b408200080d40050200b51003404000d003130740801d0310b5000c0f261301d0714603015440d1400c00090414484800c1c0001700d00340b500e4051070340100c60500e81041c0f11042c049003034034480203050740d460541c450800c1c05800608900309100207031490403018200a42980f40003003012031284244e621903400b41061000c0d40c1103030034404003102c5d8032601d40c41c800c0380310500803850030403181d0024065a01e08030b00d500c100611070054104007001d43d03004010580c1ca030f61092840746034400049800d540140301000404600480320507020919052070002541108000792804040702 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 218462823 1250 218461573 218461583
    0x10e1311060d240618030206030c0d020c0a0809042306010f030e0d0503060405070905090c0a1e03020715060f030602030c0409090804060f0201020708090409030e04060b2203050a03080a02090607 85
    0x414100301281e4005000341c83c0031800e45e81e90450a01d10b8001034004d0002402680300904005001c0000540715811140e4100600082c1d8222800c10306201c001d541000d03040750701490030b100c003001400e61540c00428254a918010025603200c407070044480d0301076042c0b94024940c1d540e00003c181901040381111480b290707907803243e036440e0060a020580d81c01078000001d001d841d05040c41260342d25041c6a0f88120800c4050380c880960550480c0c440c0103a1450700007052103070006001880d8140c004142d07950240740904120704041d4420f1040b14014031a821144c1e14002050001503200d400561300040702480107401c06444107841e0702128211281103403404000101000945c1d040444044800010700003142400c2498880b08031621a01c03505034811a521490403007014040c1429048210014004114043c0c03142098065540a04030038014080209003071000718070008200b20590f50300ca0041c2045d4032003940e06440106010788030301c5d0740b96002e0143da02d150b1102030140400314010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 218464073 1250 218462823 218462891
    0x11061201140a2304060b09010c0f060609020f0304020117040b0610020c041a1201050105090a0903052101050301060b03010315020c030418020717130621090506010e1311060d 76
    0x34010041155041c0d4045035024009100710240c1d42e800010000020703400c40c10003080c1d0ac6044c07429100038030b000d0700f2081c0c1c503501c081020140c01e000341d80036502c140d20030788880f280d803c04018180769030001160024107405c4d40c00009005400d041c64940640311a034011622503960240026040d201038003102c1849420b408540341c160302c0c102800c80310313006001c80200b005504103804901032510003004c3c2a00300d5110503101040610400444030021209110b00f10341d0641d000c410b0142c180c003841340b140701c1c0d0709001d404100e0800800c21241200da001d001d0176284180180500d000c2e402c00d86581005000a000005140340205040b0100c0c0490fa40b00603581c4000b8500380c4019440c0106a040500341032000c08000786200703401360260740700346c10011075003090760b600344482c00742d1805e000307a6203820010302908201d0002010742c140e5140c02c280707000b9940c076240804043e1088400107810103070500c900d0b1082c0d051900080c440d4660030b480124101c1c03001c3c0300302070002185900e68441c00c045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 218465323 1250 218464073 218464139
    0x130204052806080702061506270907050c3d020c10020315011409120a02091305060112020a09020a020f011508030f1b0607080411061201140a 62
    0x560307124070003620003800e1149850a050070025550740c2c00422076000c0280c820000d2900390b4405061715100e01d04034900c043c492150000803600c034548112080d01480940300868607030360040060301c002003000c900801c0380e249902d6404c055951480c6a5840c1c01c409a05d90003c5120094410696055000005079030782405408041ca403508491014130524814418062541880a13216120f04400d00c3d000e807081c07140d081c61507460b1048805155101026244074000c1c0c0c0c0012500c0541c3c01e008448090450f990098080c90788030310340c0d10080454002d400140a00c034252040090160b00103084120220340302d84544040341c1c8007840a0300941d110541d0300020890174011000c2846100f2010704101e8a84038000c1e91364002c0b10002c2c101200041a0f2000d5000b000c07894030214101e43c401c0352424100740750090104541514140d40d00381e91030240f0144d40c1071200031240d0b0000d42c0c805059140e840c1810f034101e106541c0a016a0085c2c101b90005030900610601c1e9a0611221201c0003071204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 218466573 1250 218465323 218465389
    0x708071401090201090b210a09110301110f0703090305030a09050f0109080304140d051608061005060403030806042a0f0809210705120a1706030c13020405 68
    0x10060081400e142c2c106204000140d9005110004448a86c0142904c0f100200405001c40c1200c1c029500d140460404124202106400414806010390f45241c0c0c0c000341c500505080c1d03100309260710712562007004100c0886c05124004c0c00894043c0c070340380030803607203039620581103500840c0c4c258005020f100041c0401c0c034003a102e20010b49803d08103400e40c2031411110a80324000c030322401344510980c034980704141d1544212044110317840740a45801c00e1000490000300b40c202d004a00442c80382c0c0300000d02c80c08908040da410385900400041c18507203107590840b43d21000410141c4c006072518200c1c086000c0d803400384206146980c03039440d00c1c1c00d9240c1006050202405041080060100910000c0075010900300240621079085211158a0b00c071042c080d881108801022031244001006456190714090140c03010b0547d1004800009040362034500b5a0689003240d01d608102e81c00b181e645401100c00c0300d40e10b400c18015040550700c0000800d2241c4141c24514803442e0400c1e81310100d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 218467823 1250 218466573 218466593
    0x117101e1d04020915180709050d06050a050c07030c02130b04050a05150105070320120a020d03050c07021e0f0a031103060601020f0604031b0605090c040c03050108030d0917070807 79
    0xb45c80c003200e00342c0000c0c0e03180c0000c80020455114150f52a80e80d800320390001c2c442c2c000200a00400340c1910140e21092810100404040b41c004490340e00c4c000200354600c03240c038211801550141c1d500200564203800304031880101c1e1610a4650740d46a01d00c94031901e442c05414402d50a115000809103868202030101242c444002c80c10000d0401c911000660005046601c50b980c15489500e01562100c6c81441c101c0c10500040301c01e8808034508050690025020302c005809aa00380074540703841c4400c0c2100d005100b4020750000030010140101c3d078000102d080d0901e40240707075202c12054107010400b1107200790025910b10321840201c0d011801c08001c55600080280b00401018040e61195a121000607000078108443e180c83d40c0d031940304040e03159500381d410a8041065041519440303a07500c1a050359540191705041c2401403040c001e2103200e0403a4600005103242c0038003000030f03000070b2110b4002106c3c0070f1010b00c50000c0564104c4060b215035880303001250b80e1030f000384c1045ea580f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 218469073 1250 218467823 218467831
    0x1f06050a091a06030c1209011112090706090b07030809070f080a02190b090d060b0402190e0102060108030313061404050102070c0806010f0603020901020a050a0c050117101e1d040209 80
    0xfa0070070000c1c03010404440c4200ca1420100740743c83d214640315111118054010b940841c0095440403400c41e6126030800640b60007a11920111005107603144002c1d02c0100740c9108000c2c4a2034180441070103c1d000f45e221961203002c003419521421748034076035500c2c115280d8001c00310316031060b130403001141019000404a40c0c1c003054000900c030b10301895201d41c2d00c600c18100d400742c0e0001030300008100c800d400c50155101c0040081d074139402e441d2180303a03001400c0c1c2000c0c1b0004e421245403d20715400494030605031b52903078003e1865552056051020345504a90403110680d958a0a203100300100100c3d60103148100009070340d03850f0900303003061001c1141c0c003c540c0580292004103d42c0f44918840300883e40d081c1009601c031543c0000507410260b9071040a0014083c6043c0c40c0200890700c0b13010015140240ca550450244040c3c0044180a040f10345200f1800d40c4e1900b0b000c040e4400114003079000044000050168480a400400e820302c840180f00b501a4402408214645100a5a40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 218470323 1250 218469073 218469079
    0x180a0b09012003130201111006241b020120011a03071a030402040506150d060e0a02071128080304060318020f0d140706080402040b040b031f06050a091a 67
    0xf9030070f04942e1621484140300300241071044125018802807000d00110b1441c5009100411500b0f030754000c0405d458100c0820b030103074144130520707682c1c00c140151080c0c0c0b6007003490300041c070040e40c0300e5006444003901c411000380c9024a2865000354a8030901038038001e50143d80c403840e82c1255010070300d0314100598005203051075040100000080812094079400f0b501140d01040640f601e8011550000c02041440c10341680020a45100318403a0041d9048403907520140385c550762100c064804031301805500409044003815242c5a52903c220310110542040344641013403801c0d40360400040c5941ea01c5000e8039080440c0401c9a690184585800d5103810218011842d040d81d0018000340414165075100d010600d4059040c03250042d0408400c481c0003044071724554032203101800c0a10700715030881c1b0130382c01d0040c41c0484e41400d024027a42c6240240007000c1e5000e104103405100228050310050245d558040001c9590f581d14801c00148611075001659205140e103142c4c1700c8a6510803280 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 218471573 1250 218470323 218470327
    0x180f020f060c071d0702060403030c030902100314070e10080405030903160e0a0510050118150504090e0c0102060403050f090312040815151201020403020402070c050901090e0303180a0b090120 84
    0x417a540e0007040b00c45e80079625250000d1203001100041d0300800307615001039000020342c801040c1850301584030110303014540392416141d5988a50458550035094100ca400040b950144c92a8038011455280c11600c80c0050360709101c807171004030b40b030446c013007c1d0551254a4079104100c500c41c0e50640e2071700b152500c0c400340034500c7d140ca07802e041c20440344502410050205500305c0c22909040d8240060160354454100b500e07446a001405c68110f4094134102525000001c06103030000200224101c2040e0043d011603515a14199101e0700103080102d40074004100714140ea036014090080745c0f00640021075156403d102c88070b850074ac0030a28407140c9941c5038041c4208452803402c880c40c4800c00300c511750041c050105200d4060300595000030340060011619a081084002c4940e0a45900755032620917aa600c400200c155100d00c0b15020142d0000c1010500d080c4410b02d0b6445c2d0092424116412800b1541c1c81c1242e40c0000c80702580715940d00d07039003900d07900341d0440303010300c00c0c649016824 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 218472823 1250 218471573 218471581
    0x102090303090f010e130518070302030c0607080706050c03010e070521090304091407170f150d0b0702011b03110306270414010f180f020f060c071d 65
    0x3603403486200c1c0643d01c41e01600f4800b41550f07204400b000c101c04805030408482801160103980034220a44045a22240d07012400004442c00100f0b44104c9800800400326040d8410600c011030f40500d030141c40c103d00401c503480c0481da041c0245400350050251680d074030341c5007085004554002500490801c0030400054480d03080d00191034402e407509001c05c0301d0340e840b907000c0107146104550144403100c5c20403500b000760b0155452414415051038442c844480d00c1144809820101103881200e201c40d5080802c4822101c2086503512820150090b015000e49490342130120a04540310070050f91296a555003210220200840f0300b000d070b042c02d1106001e131112181613400010110340c0102c9101092001082910070000c80c4801d04600486040c102801c110b2244484c40d09084074a600f4281c0680000c0503130321132012100f6107803041010703904c0310360b8aa180c00b4080d514160792141c00c0000c1c114140d5201d200401c03108110b035000f08a030514206815444001c0410380d41d154400b04d81c108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 218474073 1250 218472823 218472829
    0x603020d1109010522111c0b09090604241d0105070e190e0a061208040f06020610051e03060a0b0901050d03020303071b0b010605040608130507050d030e06031e09010209 74
    0x14030340c3d102180c004212200e50702160006c0c7c1c0a254904030310001a140c100203809420351240c40c003440d003510311003800da0b2640c0c41580d95450a4800a0010390788522401d009200b10102541072030130010040790818034203a10710031a10b0b481c0c00d40002d80e503564040c4502c2d40d40002101d04100401e54108000002a00440520040030310540480103580340009000400951102c0301030705a0b5000c44052040500705081c2c141c0190040c00d800541c0d02e11f0200d0407900000d0701620071000b000070030031514109018040560300741c003102800030a1310070144202c1d0340d080c03003618070440040a0004403504000100701c280c400c1a4001030003034801c505a84003007540441101c0e400441341c2448180c16224500c0f10300000c1c0d1100024103084074003030010462690000080080f00d00c50358031503941d9241d680411402004030383d001051940306030001c0080c3d04004010074039882c02424883c40c01075400e0b010500e217600407a80d1607072034894001174003c00d02d04011129040742c6888003c6082524101c04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 218475323 1250 218474073 218474119
    0xc0201060b04090c12020406170a0b0d29010e06031905070603150801050103060f060e070c0201030c0509060c030a082d130609030210110906070b0601030603020d11090105 75
    0x1030300c03e0490310360800d110740c94058240302c03a00e28501041155290350718036004150008811082e01c11501150220742241443e010b00400740200401c0501003110645e0343c1000d1044122041e001c42c205400c0c00a8080c0c9101e00c214000c00744c0c0c0c640840e081c42c003141018103080d0080301c89048000c02150780c001042c03002030540300303030780075818001138040e074028140308001810341c007410643d82024008403c0000503040066803911400040c0a0345403500380c0201c034100e045032700300c0004100140140c00b541c401c2d04044020700082c1043c03481d000d103403408a541d03544401c2010f040c0380e02c0042e1004082c1e50009505030f102449190400c85100a155100f00001100524840c03a29907070b00402e0b85501000100003d60b0780c400803c03c14225079140107510f49070360f09140100385143c40c11030f00c14803850f01c0c2200d0a0600080182c0e240000ca9543c03003e540c00051300d19410540e5070a004001612000b8903185400c0c080d04004410498240c20040a040160072450040d81301c1c1c01d11000c2e03001c51001d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 218476573 1250 218475323 218475329
    0x40507020616030c0912020a03120221040303020307300507170406021911060a08061f05091c080c0a0c060309020a0504020d0902060f0a031107021c05120307050408010c0201060b04 79
    0x5880c6d641c500e9240000744644206030009443c0802e500c034149880343d00011096168110031141415103100c030203400c000d078042c80c48080c0250f0003c00106d8000350203520704001352480d03120f10103102603d806a00b2812000c00d01600c0110703000143c0e06c4141b2000340c102c6c0070b0445480401d2454681080c00c02901e4000300b0710121150000c40d40410200020800b4101034404007400640c1c541e8021307400240341d03030340556180e80902c0c2603900001c059540004040c240d40701c0c1c2d4450a25145068040c0700031544000607800c2044582c0394500c001400035001840e400000d08000d242611450900104d91a0981e0081060520b0184a180147c072a109a501121022980161102c18030014a00136002ea800020350004000411a4000344400082d00c2d002c03580d07540802c07144462000701d41d014852681c0203540b104040e100135100300e15250000701910b200d2410f5600150342c0c184007054580003502e10300b021440100d001e00c6602024807030021640742070310084c0951032504130080002c2c45240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 218477823 1250 218476573 218476589
    0x609010204051c241a090907060507260a110606090c0c031c0c0233060a15020c01080f04030f0e030a02060403060605030d09151d040507020616030c09 66
    0x100000c018802c880c2e01e440c0d0340348a80744404078520071031008040185500c42c0320280d080340004080c0c0646c107003860301e14070500c2d181004004480c141141950241c0080404841d0600c400b6607905a403010000e122100e84c40c0e2640071515011501c101608072440e52401c003115034800003c0091554030040c24940101c02000c803544c1c1c51003500b400c90705611030040c10100d040100c5070b0920300203060741c3c4804030703c000c0c50b400d40750b80310b100308114641804106000c0c0300321682a0124200b0004101c60f10340c0180c001040c04a2403a030742c0c40b460f040041641d81c000056081403081c0b21107940c102d18401d0307009031200d4a2a00c0d40c941660f02074818115445400c0420044a40c01c1c006a282041804000d45e0002c0c206034a91381c0d681f40620180075a8040d65000e4040c5030f42d4034920500441421302034401c00540c8082c02100d1200480d50340702440c20310100700f4091000b8000039120751107454025115a4003400f41881e1003c49500e003d07502004950406142c502d82544480d071090680041d101a8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 218479073 1250 218477823 218477869
    0x1506110f071208090306070f08010b0f0301140402040e1503010617061302031e0106030c080c01090b070201170c0d05010e0705090d0c0b0a020303090d050a091412160602060901020405 80
    0xd41408903840c0108581c8a4040c4250b8047c000001c0c2c100d050203141403081d64a0003800d0380c88100e5108180140090092443e0003400103101d8070f0f82e807421914141c40c004d00b006042c103696440101845030b00780d642000c02c80d28200c51800c60304003802500c0203040c9004152840d4040350007a03680e110310080c00440c0d058071501c400411580e061000c6004014007851100100c000e500c1c200c0e00070080c61000303c401040c01c0c140011420804103002c818440142c4484200520304803604100e035003c02c0c01217041044540c030210400c0c0400020a004019080c840e5803512000254a8229a81a084041f849032960100140d855004048a80e0003078240d400440944041c540800e101903213030018103101402003080503046900102540c40f442a00040b40c0e00d0030b14240e030a41d824400c03541050002600004d060142080c0ea10f103454006070702070042c1039801c0101000a06219030015100c004060022003040710b00c2d410082942c201010800841c5454600000520f490442ca01409515180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 218480323 1250 218479073 218479109
    0x10603050603010e0708101d07121403070303020a08062b03051605030a090e040302030f03180f030405040b01030b0904020d1a01090504021507030f05090609041506110f07 75
    0x401c4d0000200c101c000002c070303800c40d81c850301c1103074640183c0d1202c2e54006140a900303220028111480c103802d0440742016040c0d45050042c400700c840b40c01d0409032040c070700301159815000303020002030100c0b500a640050300c804a4440060054401901d80c1f84901003204560885c1d000e40c410b880510903a0038404000001c0a140503581401111b10a4006120034483d140901c0800b00c020003042c801c1d6614084990b4441c002c07130800705c400f42c5024005920a2280c0b10700a06401c00131034101101908a00c40c141c4608106454010300d40c040000982000c00e003040342c0e0800303000c0e0440c030107000d00301403240d0002c030300104000140003007000c0c1c441d8001306807040901014504544107001e100c143c51600d5030b102c454010140c80e065400300c0c0201002164250359200350702c2502d12681e4165600403031060a80021035641c1c000c0111164807240400c03143d00d05a4a5200f00000b2261500111050741d242c0580179040254101400c1c083d50400c0b030031307440080000b080ea030080d501c22607200801210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 218481573 1250 218480323 218480329
    0x150106050a11030304080405040608150a0513140109030e0319080a0c020901030b0f07080c12100f090605040c050c030403060c0507120e0f0a150503040204020c06130501060e010e0106030506 83
    0x2c4542c4071146580000414001804060301c000d1007078404c01d580521406aa40a009603140a40c454440b03c02c106880801d041d115580c00ca02c1d00b25902c1e0b1082040c001554440b94000c0070241d1110302180e41daa0b0b103010416400c1080380303141c103e00304c010340502c4950f1001c2c10000310304e8000c024110040002c4810800340607800d190b2078a500540101035a42c1c482c03030000c40303081090756100d14032007810000072545442642000e1140309450112400c0c000005640d030441c403000740c00c1141c203100c0c2c2000800c160f483d801080c0002c003840c4902080aa20701424030089401d420402c400b0084100300100c2c10036000001c503021a036014400140004415a0860300b40c001c80c58001e1011a00e91001000107034000f032150f80703040045422290400c0902d0801c2000c2a01d40314101d1141e4407051480b800600802c0555446400504058034100082e41801d0501200311030240c1d81e088020308100c00d000d806d01c00e10000d4100c0b01d452020f42d504288511801600500c10b0004258461000440c00d407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 218482823 1250 218481573 218481587
    0x50306060a060507140f030a0305010e01270b030102030a06030c0506040509070f030f06090f151503020a020313061709010e0705040b040f0c200304031203110c16031202150106050a 79
    0x3120b845e00340c40b030800d440b040450b140d5108a0181c2c000030705180c0081069050000958100c400170b03210307207100304034040620940c030f81460252145103a0f0fa10800b19162000e00041d4400d03200340d04005016411460705085500782174015074001c26061000303200700c0d2500101c0a0f042101400c007294954075000b0f040300688402c0410b07000745820140e001501c1e441c260040c011010180c50f040c06200000340304040c2c400342c0b6205070301240c608203403010a40303030096009142d800c6041c4180e0f0314001103803108480d1007145601020020b00102c0c7d0315280d005001002d583c001c864000280802c14200300002c0d91396225000b41446103070351391032a00c446c1d911540440945180039905001003010a0005005409203000a008042c0d50a04800141c0c00102c102c6c0c0940e984054402c0d40c01140300c00c210f00900c03056481401e514400c02015540741d4040088800c00c1503180c07020002503046107482c0ca1001c1e9200f50302c1d002d55001100c3d070750014491001080c103450003450429250540b22408031416 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 218484073 1250 218482823 218482853
    0x118060905071502010603060c1b0b060102030708070b0604200405211b2115101806050f01030c080f0910020c0604141911041409010b0109050306060a060507 69
    0x103e042019140f070098040d00004100e80c020340e000c00c00d80d80560025160002000d03a62803810314584001400034041600d8160084c5041c4100d034100ae00d9980c074045603911400c016182215088200001d504d440d00800d03800220409041c52810030b1065039050500450140c688520100ca0b1121a0000a91850710100c0080c030100d0f454522407810038006038500e04a110300031001d03a40c3c03500e0182d901d2500c090368114010003d01a02a514080080041001d0200f014181c81e461000446c1c4007080c64403c5c00d42020600000c8941c9008108200f00c000c451089040c141031070502e00141c1c0d0883c0030542d002c000d51031090310680d076000116003032500080500300c00314804540510740900c00035a01d44070714131500351000c05200080c912a039030100b150101061010441e2018000350204c20460300d80788014001040203100c1c80d014a8210000311142c2a10b81e645000c1d50800350b0348a190140105020740c041c0040e400d216012644907002070042c0c20600c1800110407040004c01c0c02d80740d50b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 218485323 1250 218484073 218484089
    0x6040f020a0305040b0f0108100e0102190908190b01030201081801060914090f2e1406090609010e181011030405060702030412110105070501060e0117011806090507 72
    0x81d9145507100940101001c2d101a9030304400e640000b00c18207007010113107060300c2c09040104100c0b905507000c08040c00003001c1210707840d5000d01004110060007400103071000c003e600d40c03034242810500c82918040f41001880c8142c43c4140c50000800c640070040c6040d40d80a03e005c81071036640504100c1183c00040802480d50f10f00003001030502503a03406003802142145030802c1a485540d00180d807261048400e213002c0d0800d014100c2060501006401e00021896520311111040b0f46c2e410215014074010440e009100070400055251083c03c3c0b80e4428400c8400b01403550400b04a50701c0c1e08001420f90000f15032604166410000c10803032079102640c070401c140700101906030210030b03540007660112814824000882c0a15001100307036001d0310710214102c00e42c880b1a495140e120000c80f011a414400c041000c20f000c01c40a00401c0c001d00b208030413031205949031403121401402640482d400ca41d16180310704184121050b5040d6200e41c1040303010a100046003059401e01d03c180e441602 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 218486573 1250 218485323 218485327
    0x5011509020405010e041b0309050a17130605120a0b0d080309030901171b070606090c030c0207080102040f030b1b0d0b01030c030c020d141c060317160b06040f02 71
    0x620900c95002001610000c0e030318000c41c0031502040c84241c41e6600004a580000708090280c0c00340300b83c1c064000c42e406141116120b211a8030b8a01401e0141840500fa40354009035003642c0300741c001c040000405282c41d0881c50b008610381c0c0c18002d850003030403884907152a40b01c0da144503a611484090142e401c40340b41030350707800c2c485080c81d541e41c024074155002c41c1403c3c900501d2502441390b40d91280c0810030a0308698035030f00c960a0400d07880a00111003265071480301041d4140c003480303059410480c0703031000143d84040c1c90000e842c101d401d9000110302e0303004204c00c1c0280f9140c2d418660489601526100300d5444150102c442002d98500712490090042074106603d41190454021800c1c281c9003003040211100080b400d4908103c0c014003da170003121483c10503481100d814844c04421407215040003000032180300c0c100748072828910700b1511980705000b400b100048903100c602d1451021880c111500e52150034809101038042c00c00f504010000b509611150000c02e00c1c081c2d40e000840d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 218487823 1250 218486573 218486579
    0xe071101020f040b0903060f01120803040501020d1a030705040501060f23070c1a0f160c03020a0605070212030a022a03030d091103010e2d120403031101020304031b050115 75
    0x441035412003221700d4400d00c54400412991800084d005060b5061000c00800340559030b00c030410542d10103081107903250741c02c100e0303034041e90349511500b00d0300001d0400b20900d60020408152500d9401d42080744514980001040340365001500c80341c105001e030403c0812030406d0120444401c1c0c3c0c4a2002411400016840c41088031451404080d1104241c0c20051107070461a25000c41c0580b0301143c02c1d0000402140d2071035914100b0041c4494070400403d20141d46130740c003040e00c01d03580c0d5011902144011a9070000c43c9403c000703140b810b10201d0700442c242500c07098001c1d80d400307541000f05001030b0800708202e40a0f4003e8484240081d001e01125a03444010f8401001401040707020f480052203003e05030614034042c010036003240540320080042c01c03004204030018100c81c00360f400503051031304000c45000740300b80b00c040d5404903c0d001181d00c2d5851418050700344084146d600340300364410002c200000e9040103c544111045010481c41d800d000e10707100c0e0051a420211509081c5c5da04000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 218489073 1250 218487823 218487839
    0x1a04060303180f14011d0d111e1f0c061503110603040b0c030a020403240501050a08030f2104050a11010f17040f021801030506010f0e071101020f04 65
    0x2c0a9801c142c054215196543c000d07101001459029500310507240186081d010341c40743c00c02a030f040001c040d03d8003220b0010350000c4d860f950510000c8500301c100005141d551f16001808484504001a4030f5010307500b4440003421324821580000306160300d2481240c421442880d10007569a400b04041004040c1d40c1007201a090705848215200072005114030600d040020079280283c3c2e010a01680a85800e40e0400e415080201803440d50b5500b8400000410710406a51414800c468840c10300f0508445a00054a45c16004940200c1240c4c4081210350400400c407244422082052503c1e00c030300c4180c40300c0d036801404000141100c601d040c0003c0c454042140340b000c40c070901542c1120201c5100564489030049215004581503a440107007000c0386802807a40a40302d00360b00c82134400d242c0d00252034030107601c4400454040d403100510800008018103405000c0d001002140c40d803510401180414009101c901009090051031704a80c609405039402142007000c504d8803280c5401d40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 218490323 1250 218489073 218489087
    0x3030207051509071a120601050d15050f060301060203040306020f040f0b0a0207140307090f090b0c070c05030a0b070c060b12011415100f090e0109050612010e030307031a04060303 79
    0x4610306024803031002442c0c0d403051940008022403401e0440c01c20290600e140d1107906c2c001c1060703041c48000c0200ac041c1041a115801c4840700e618510b05919080c03000348992101c0c41f01d50b481c080e00d420001400b070b003900081a02c045a901072405a0f4500c2031400038046030090b5484180c2102c0c9100001c90b07066000f402520111070a982280e8480d9550049000e480707030f40d44141030300341c1c00607038085c402d240454200d9115803840050200d8210026580c54088100482d100100384030042512010851905480b10007444100c0c000c00183c091034a5500201401800d9081401281c040c5c403030401c141a0400c82080700001d0001b0140810030301040e01910360706041c502000c0c00840003c80380d41c50440507600104000d00140e1016080c22401c0e1498088801d44109110404c03400003620a01307503035602d01070640d00e540411b550901c0010b00581d0944030910003ca6414207000008135031000007525407048151501145681c00c0c61090a5510329025620b03802600b8500080149074000d25 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 218491573 1250 218490323 218490331
    0x13030606061b020a0605130b0a0c022106010b03130b0106050c01061e0902070c080304080d030f0b011d0f06030a090b2212050c0a1101030b010507080d0504030302070515 74
    0x35580314059003800001040034860b0360007507021007140000e2205502c02c0029001031141224a40900e580720440c6041d01e0700081c0e0014000f03516148081c0460900718a0b029806500039145921505d01248203625503005000788810024007000164903402c00c035001c0b080c0791390415a185010350310b0300c0000340030b58842d0004040700c1d801e0a00008601c1201e00709400940541c4444020382030811244070081e44c0001000e0780c00c003045641c0801c4030a002d0004100810b10207005181804130118090141c6602107000f20401b4a050785100c002e076040284000703d401440200c02c200c440d500c0029460b42c02040c081500180c002c41000025031099000140c2c02c1e00070b00c40340c210303581c0310312190340144c1c0d188080548103489481c05000003854140e01d035090750a5030a2041c00e0000d002400f9152002042c000e40d82120f1005010009507014030849101410a1818501d8402ca030303243440c0114820117107200071850369036000030f05141c42503050354441d070b5020081e1800c0071708203040300c4100c100c04e075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 218492823 1250 218491573 218491577
    0x4030812040c080309011e032a021b030c010c1b03060608060c0415050a0c020d0609060e011116050c1801061416110a151d0a0303231303060606 63
    0xb002c00302e0510000025690030400c16501c0c0c406401c000400641c5c282402901c1d0804d044c0c98802c601c041140549040e6100c0c0c42c02c3e48605a90b2030790ba0700007882e1500307410080b42d044030520300ba41d006403000302d10a0048682800c0c001c0c0d1000f01c51914154564200340b0f010345000f51250044200461a000101201c0010045403025128030204017044d1081c1d2042012620b005140745811034055405805400114201942160f0f0030f0780204d842c0c401c0e40382049410903600d046810402102c0c2c071800c4400c1030564000c0200d114413440c0007005104105907840c3d0144031080d11f000300841007144415428000e0402c2200c10781d082607504080b44203000318008256030550311422024548251900d8240b202300c1d09603070441e542c440340b00840c03a06400c07940000c41d000c004506407071103c02c1044080c3c801d030340d911707400c0c0200c8000504054503c030000340301d01031285007000440d40c058200081c10301132440b58100100c0d00d140750f0015108601075103101125403000001806000d0380300100311901c075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 218494073 1250 218492823 218492843
    0x30307030b0f04022d0f0f0d0507170604110d090501150905040b0a020a0c12020f0c0108010503030723010c020c010e010804050a082a1c020601081c03020403081204 72
    0x3420401c8103030f010311541008500b8099405e464036030400000492403400f1201900d161000c00c04203669590300040214040003000500307030750300c100c0710322619a11092a2034040c1809000700c402011a0380003418503881240c6520702202810b5424007140d12a00c1c0e5014100141800707458150301030600c0750400c07614501e0b40e000c00620303802035010312449103174029030408059860f60400d20094200741c48a800300100d2454081c00512020380c43d001441076034005008643c01c8036012840c3c03080541020341002482d2004004607100001991145540042c2510690514189400c0d50044501c0d107004c0540c21b008100c0c1c000c076000b0950b10784030002a030b40c3d058040304010040d07440702d07030950300206507510460303000c400b0402c80300141141c4081003001d11082a8144420031b0055040013006030903400c1680c030500d000100040fa43c4040c40c5600107400386600d0410220307100e605080d021842c543c07446080e9800d0074840d0b07040302d01452303010501640b100010070b0254013088046501f01c803103e0382 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 218495323 1250 218494073 218494099
    0x1020c0301051302180c030c070f0206070609021f0804081b030406090305060112050c01030b0a263a0509120c0307140616060e0723040203071d12030307030b 69
    0x20141d200c52080c15841c00321b603c0c68880030010001070340401025a43c06070340969120042ea2071074000c0030224001e244c081103044040c01000203400b107204000320522819001b508046402c2400345a1240e040180c0e81c1d240c0f8245500385c07412405440c000d2149000014020030282d82048551003a82c1c02903003211696a226010b180061030b05c0c0314094001d5008490041807588203070042d00030714002901542881f5603442003164154070701d80902200001100303425400f1079040011507a80d050203200343c0760b103688441c20802420800b0036074002c8107039205844103450f4096011076810000113402c1071201d8000190b101d44136520a000e040c8640907070038000450300d03951040c420210030700a002516010484c00780540d0780c0b152040403121542c660748044c2110805002c580028600d2601402c9240008103419601c000444032513071040340b060080c49010380d8001240b2244a80e06c04500c0404030301c034030020380c07243d0319500581038511002041040441d2f00d90464809a40c09442401c00509 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 218496573 1250 218495323 218495359
    0x305190302010506030c01090329130302120a050306130b0904060605030f06060a0603020c0f01090506040b010e1b070201020f0d021f0501030809040b1504030b01050a3201020c0301051302 82
    0x46c458201400201302d44000c0c004508040030301c40480700002980411401d10342c10b11820f09008480209000d03441581d4603050603014000c2c91030355228688400e00d0081411406845404041c081600607444548103915046d16a031101c0020600146252110b260624116016212901416000f402064ac0c081c2c40354200041450243c50004d140844003810305104400035000340c40100c00a115002c14079403480420f1041c03410150080d000b400c0140b9050810341114081030b4021130640100004006101c3c403c900101c012884025849554800c2400100d00e8294008a809071070b00680103407460300c540000d8400b1359448041c0d4a00c038440b040b514802c04450007440301801a85080002895915099125a41c880c4004214600058218224010907002501f04403203640f08039005001a00e04203d407040100ba410582e01c2c1da00031442d00404240e83c1d20054181e41152110742480a41c1c000c0c054100c21000180003041240380c00c00500c0c0405100700411b0b8051510541d808040ca8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 218497823 1250 218496573 218496583
    0x90209030604200612010906060203030103081204080403141606031e0c21022203020607030e0a0b0a081602030a0f0f0c0b0f0402030c0402270307030519030201050603 73
    0x110005019120301d03500c54503040d4000403c26000010802210720340e041c20b0380c0c2d8101622003443c0f010103943e841d40c100420079045452681181c400d5600a000403c0054006001c0351810610002c03050915260351070104802c0c010f98000900207640144000148040040e07208010550190000c14580d5109000d5084070480320140e185180540d03c841c0300320382c06d508080c3e920343c50fa02c6c002d40c003103102c4415280038840029803a00900d8000581c44800c850300f0f1b00000c030741c02c0c85e45451100703580b441d40055528803a2100080c02e10101c1429280c4568640388a0070013003d21084bc039980d50000000200744043c00c54204d5007294044c881c03030100700d1001068424100303840d10340410701e800100040c0c1c1c245500d2240c03403040180d1a11030074001210002c43d203010780c41c100d200f0111403c1c544101800c1560b030a1056020307504c14403041000c40c10444600e54458460040072140b2116080840c0c00d140d0b4a0308050a03034410041c012940390080c0f00d00c0e400c0c40d400796000700800d44417042015260 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 218499073 1250 218497823 218497837
    0xe0a09051302040e0c1c03031109090703180c081015030c440c1905060f04080d0c0b0c03070c06110d0608070609091104060c020d05010f090c0902 64
    0x20010303240800182042c0d40203c1c02c1c01444d4045801e000c281100041e42c56000045c04255000c0c0304068030201501400b84031074840c0032842a504003c03402d00403921510005003540c1c20141c941081d101111040e1a540350416041304503030307100d40d40b00c2410940d124030800d042c8800610b0601c5681510081c580d0303a9082e070f03a01c1310102c030f0b101d4503101c003041c0d115116030740e82e1440f080311580c1c011024139448010400f01c044440c0b200c09264409150500f80042910201d014440d052078603108140c000000c0030940e138080350100d89a1b6045002d2880500880d0845100740c0700740040d00580320340140e00e404189206008101c2c4a0355002c0894409020035100c1d0340210b41100820400035100e6001b44903000400305002d410603040b00201e006035002680f000ba031640081a05216050380240406c2c05003030019424002d842003160100860f12441c400c900403c03004402100031036880035804442d40c0c3d00400280548048466031000405403008201c0703c03c1100080058002c445000762818 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 218500323 1250 218499073 218499091
    0x102370605010f121104090201090f081b0303030601171e09061b070308040210050d090b0103140a050a080a020708070803030702010c08040308041410020f0903010e060105060406230a0e0a0905 84
    0x442c05c014006d000242c4200c0000724180920140081100101c4201038002445220700420810b082c0c40d5400711403040161156000b60001c1080283ca030b40c008610403020801c189500b6495a0780ca5280c41109504c07004985051000e070040c003800d9000090700f035014002d00341442c000e84810540c250014401c42c08010301144261340010054903145ca0104500141403d190f071900351100d011400f1561013810485920b00e20074014402c0c444d8114000c8041c402070401050800b80544450b5501c0d04622402010800300181c014070152007440303a00c0060014000321005c150316200304648a0308122175440056181209501716284203941443c0181d0701038581c901e2640310380d00c80c4000502a17540d5014130b0310405088298078200f0b40700503c0c0f400c0700c0708503103903c2e0b040e1074040509503022411b16070340035403260b00180560303031344c10044070102c410314188000071000090b003141d400d10f50409402d51034040031884003101500300d01d550201c1881201c41c415961b44508544088410503200c0c455 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 218501573 1250 218500323 218500343
    0x2030309070e0709030c0602010f0f150513110c062d06130605090c04051f050a08070e0a032a0b0901030b03010b061303170403020102370605010f12 65
    0x12103069070b101003035080b1541d8542552280c1e00c94032046010360282e404800141e55074002030907141410700c40d407118110920b5040c0505a6143d80303000c418112406014420b0303800c1c4403080701c00c50295005401103c03d0400d0f594584000c8284c0a031a21801c07294447d80381864441c50590b0ba54030040c40301c0106002000c5809034498009005048807000b0600301441d0350f40c07901140360740e1148103031441406c3c21041d1560311400d02c400d02541d0214281c018551400400c0c03500300c801c0e005000e46064403501e2400308015036900004880035001081c071203400105a22010050002e5002c3d00551050705602e4040e88186100c24041e0380034151040d540015414803101c440b541c032982041602c03810050000c10142002400280c01d0303842040840030000b6104010030800180001e4804006050102c0302e0500d49140c001039100c01094030012190507892206940c80c203000c2d0114600418a0020300d58070990728a0715400812080c002c2107480100c0c0000050810308540c00e040e03e40b80d004c2900b01c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 218502823 1250 218501573 218501579
    0x12070605040f060609020301090c14030c130e0901050402090603030c06011403010f181403070f03030203100803030a0509070f050604180b1005040302150f0912010e0307080d06060203030907 83
    0x1402000090002c494200180c0d03000c601044150080d2409071410b44001a03036940b42c010350307404075802e5801c0d020501003060920040780103820280c4c2c1c0e204c0035a4602d680d560200815010a54100f500114020420f020500105441c15885203114510a9070302c02d0060b12100c0426660703004000341c4c2c80c401c2c0d010000511503d001002c030f14003021070150002c04c00e007480c4089441514440590110f0341002c0c101da0906000c9001c007501071000c003000c01b451410049031100e48440308000c074064149a000800300b0512400c045102c0d0061607150f003565100d0414102120281a0944005615105040c03000c120030003d80d210000b00c905c01442c003484d062814205405d040035003044a080143c1c4c40000c10826124650035405c00082980c03500e54581c00d40c07040200c030303101150036010449400d00001803c00c840d03904450103800d04486020f40c407960b001c03056015004041c0d88040d1800007050300f00400c424100608401480d07054140189502c40c10102e0340c070f02040ba6000f1042e17100f62420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 218504073 1250 218502823 218502833
    0x5060306100c021f0c1502070812040c150f0801050405060604120f1406070201060803180d1704060903051b181f06110610051e0301150b0307020f1207 66
    0x4140c0c1501c06000741035903c000c4410502ca100108a0132400b00c0c64140c2081c080003111020030150322802d10046043c0741681d190402d05001c3c403000c00030404102000725050100c0c28040d240284000c0702154071003410310b24000e100c600700d51116004682900c0c00072840d4541401540d00c50400076200b6402c161412148500d8160003d000f9100905030700704130b001007100080303011001132090004041c5802d240500a0850b401e1340d11030384094100744940c0c021010400306003c0103a0044071244d01421050800038104102452030460b41d0200140026655800184d91400c0320301940651f8a80f05942849583c2210403829080e03000d400308141d042e0b16404c5404040d00705070051480e110a482c0001c003e01029035036041507000c1740c042a501e06580c1c10070803d030740d884440c007030035101c805140c4404107001ca06100544441c0700076401002101e920254400700840c0e40c802c5e0036102040c0e03542d9030404a548156082d00043c05220b00440c40c40030001920300602c1580000d445c6032a006480d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 218505323 1250 218504073 218504087
    0x60a0908040305010507020c09070c120e032e0e03070b041e05060a0902100c0201120c0e0301090c03060507021203040f0c0302030a05010f06050d031e0207080d1101060506030610 78
    0x400c0340c81000610001c00071540c2403052a200b15580d030003c207080407040080144950b4000c25480801410a143c10f00003262980c0c0740714000201e0520034003190001c000641029103c068407420304006c1c40c11103080e09690614100c82040441007004003681c0030750096100d11039601d000c0c0c844980c06021900244108011050f803004017a01c04216401682e141d81c200a000d44a5890310758841c80181c0940c5050340340790b4045005810b112208040317a600180403090308a80b030201d40d60780d98800000c02c034042c42e0410303641c080050003003188101070720740b5102100c6c060000361141031030000017038045400000c19146503c0c00a080d00d0969403643c0d10605510310416040b01c1c4000755440010060b10108810403485124030000b003614982d0031070719421548540e00a500c1504007058090119800c00e036a803102e030020b14910040e0035007240d403ea25080d407691009216100d1001404043c0d64490305054040c012036000303100c800d03034403020032000380001d80380a42d00c80685030b0702e480340900640e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 218506573 1250 218505323 218505341
    0x6030402030c06041e05040b090601031a0a0e091213170705091503060702070b0a030e072402070503070501050d050703290f09070207030b04030903050a11040c11060a 73
    0x1c100c1c0c18005209010540580180d40901c2200715141e01080603c4951180200601420b5034104600c01d010700006150442c094103c506041e075515a00445440c0400b541c0309010b8003504007484665180c82d0550319607421940c24256000f0a4070f030880e0b1101d510110f0350504100c0f00300f40d0240781452010194003482c68140061840754100029040c0c80b038501c0d141c03040c56031100030f0000f01190f20903d403c2c0000141000c0c04c542040305c05000c100250815a2802c0c915032500051020042e08480c0c9808000d402c40e95212442030786c8003104112149003840490425420b40790200c1c0c0e68014190f40b4503050041e0f9010078020703c50301e040a2003650140d5807003a0b6503e4003150060610380b40320440c0d01c90301d40c0d00b0220720005040240a09001104101088041d01d60303800700d280c0000b00030f455103807501000342030250309400300d010b00d4480d40f0000051500107003682c08146052501c0e068407403115102d40c4c0260300b40814030300d419024111071414140e004000e0581503880001410040c0a0b080c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 218507823 1250 218506573 218506579
    0x1180f210b13060c0207050604091107140d0914030604060f02091003020d14011809140f0c0411090102100e0708030f03070206180a1719021507050a020c06030402 71
    0x5889040415000301025000740b40520b1241e001c58114100070080d1075103d0303d80030565002e600304000603100c0c40201e5088581c1c100b00001d65840000040f07030240300c0e060010349071041d10700844641c00d00c0440d8100740c200c201c2c0c845417840c030354034540c9051089031600016499080040000c0101c1c801d6082402d48901c0503c00524110340b140018600030041015440080e0b8042084582d4004038030450b19850034568000c00c4944c98100b04881001980000049848c0c941131134100700700c0001d03a031001050300c0c5410b0f0760300c401c84060101d03a80d507420f80c1614845c0342050140d1503d100c0d83c01c21138900794010b0340980001d00110021101030301260703288040611580b4400107070700400b8006042260121b41c0d00070340d2818181c90080ca4140003030203005000ea1a0401080711050024010541c29407118a510040703503070042d011998014464685608080343c859002c0d03465020038031710200040ba1105034560b03210380201301c50a005814590001d03070b110034001e0b203162409501640c0d01034401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 218509073 1250 218507823 218507879
    0x607030f0b18010e100b030408090102070b040605090307060801060507020f0319050f12090303070b0606070804120303142a0c070308040807080d050d05150910030201180f 75
    0x48010804241c4801c40b0302d000d10340e01e00014042d190464003c00d8018007100da01c2c2c401c841c1403a070884901d22024000401a03680000c3c0420180d0080c010070005210080040d5159680e40401070301d95406501c143d841f81c01480c10102e581c50081541a041c3c0340607646907410245142d003449000c1c040c0c054696454800d0741210070303280842885996602d4840d801901c80c0c02031044040d072900e0f101701c0504400c0758081c0000c4042c0e440000903180140e40150001076280c07103c0020403218469048003500804c000035002c20350420404c900c070306051003a41e04000034800c3c1800c85c01030300401d562082d01600c1055070303003400801444440401075200d044561810141d0150580b8040c0c9540c4111004100400c0170000c17044140312010082c91070700c010f40310110141d00e00500301d12a400c47c6481c1c069540002c600300314909424004007a0014114000c1800c1a07540141817100d103105c00c90000d0842580b100d10300d419500c2d0b99085a5000007007081c200d051480041c2d0751085041281514102 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 218510323 1250 218509073 218509091
    0x30518030c0907020f01180f020d11041503021906050906090a12030c123b040c03050109180503040506340309080a0c0b1309020d0209120703050607030f 67
    0x2251055805101644c0007085012090000c01d82900c803108405047d04081854070400b091802e000380740d030b0903412502c0c68180b06051030300c0011704402e41e80940c1c1046c41c100300f1000e13508611041106503802282c0800d20b580240e50302307200c880d1440c0200000140d091009036000e0504d18040c015505004001c090000d0300d5110f034400e404a00c0c04180e00045070000c1c0c0c141400001d4148001156032840d0600ca0b0000008560709107040282c1d001140d0b01404a050280310582c02c3c4190b550b40340100240042c65603044020090802070042e8500145006001d400341e080c4d410808071000c2d4030401035810705151070104040c50304140d000b03c0a444100303c3e407440480f008414a603511b40c407403005111646290400500506a980010030284d000754443c0020803042000c0d20200da101001d400d07610807203074031445a21400c561181d203c0c60b0000c110882412826005024102d10944d1100c2645860352000c41e591035880c403002c1c0c85500400085180700b03209400142c0144c1c070604000ca84808 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 218511573 1250 218510323 218510329
    0x9010903051203010905060a03050606010e010c050322171b03071a0a17061e0609040e01020c0c0402090109090b0a050907020a051209030d05130806010b0d06050d030518030c 76
    0x10b80032140720007003000100501000c2607510440f604140180c800c0c488a50440d038a09545200143c4410305006800007401704682c40303000e06600f916488001e494440c00e4150f103909611482c0d42000814010307001000c1100700c0811100490341810400602a10421032081d1403030442c410710741900b40c0100000403441c1156040d0032056698041c404584c0c07000311501c0102421040c02c86038002e26030110074489103645500c0d10780002050000c2201118102400144145c03048891594106080c0702400400d0780041d409441078a101809607070101121200b00700883c480c2944043c007158203180c00380206542035009425262000d041c1c2c0c10300c0c80d182d00c0000d10f03c0d03600b00c13400401a449002c1c00410004140b10380c0b410100c0c01c80c485410104c8500010b81c90751240c00e0f401d42000000320b0080588a11446101c0c01400058182c681c1961034a903801d000764806c8a5001c0700d41c2c14090005802e04180d000b016549406585075810302ca1151108080741e090075000d550305100f849043d030700c960303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 218512823 1250 218511573 218511583
    0xe0307031809020f280c020f13050907142e0207050d060509190b060609041811030d050a0206011202011110062108030a020c030d060305070303140319020901090305 72
    0x6001207100b039101e04a45800d54a184d005040c003040703250a4030760100b0001c1c0c00501c2e4946d1694103c2d2441130203428031000c02c410282c4c0001c080c040324200001e01410484c0410410b090b41d0040b6013200340c110450b41440071400b14494012456981003411400c058071003c0000f03880b000e54810344000d0399a601c000340d28014070810a45451b03544106108141c0d00c1003064010741d1030402c842948222283d158a00d0022000b40280d000310000110201641d999512803102c018200320800d80780b440e0341c01e280c148075610051883c020310848440c0712104e4041d00540300c40c540b4940c01003089030300300043c02c000e101e070010040b414040404240010400c0c203025211184101c004001601c3d0701d40709201d462070f503050500c0c0100c0c609503c050400b20712a0021282c0c0060300c1e51015a46810403041e461440c40340780a6800d1035890442c0c007000700300300855280304480c003a5031a00d002c02c81d034074114881444107858813001082166034104004265801900a540050520441c0c45eaa203071505130901d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 218514073 1250 218512823 218512837
    0x60405130503070b0708012111030c0d0c050a0605072d020402031e0114060d0c050c030c010b031002160f14010c120c0311070609020a0f03050f06010503010e030703180902 75
    0x48132414200108203505c1802d260040503c8200310483e5a4540c2e031080c3d045c030b00c5603c0070709032102c41c4e500c0c03c0c02c580342008980718400003c0c2180002d61841d043c000031205050003075078400c10700c1910006890744900191911241c100303103440080c60051600c0505103c180c87d05032544103000c002c00d009030f941d0380301962040d0744000e4a07441003951100d43c0d40700500143c11803001890031a034480125203481c4c00750349020880c50000100742003808da081c7d130b4600402201030032510001030b8a203004407041d00603501380c0342c055048030032560384414100140c2c0615260401043c3e070704100c1c0000704641034411720b1640d0044040d810f140b002031032078a0a44240f0f200000100c0c42c03108018110b9126445051c030341c0903083c5409c000d00c481c00d1252440a12034040040c1030b96071a07105d0074003503580d40600a0020411000d88400c00c0d0341c0c07860055140c84c0004100c414501424000203420b06060080c14a03284900c2c02940c50000559010340b1078007200d010030607680c45a4500440c1951441c802072050b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 218515323 1250 218514073 218514083
    0x11e0e061207030e0712060e0304120c06030b0a140d0219060306030510050c09130f150302120606060406030c03060503010504050705090a021e071b031103100504020906040513050307 80
    0x1924102d20080c0c10740d04903d04034801c551000404010904082c0c4a801c013456228801041100c1c4040b40540f55000c0c2c1d8000300405079048103c0c2c02000b0039160b6035011607407552414060002c3c0c3c9400c00002030340c144144c4c8512030341c130a0711841c42d01c0e00303615200d402c6100030f1403074140c1e441040d20015060115000040400e60300c1009000340007040040c1f004254024a0600941c540015174800b0b5000303142c070725070080041400c4500314142076000900a00d02d829020003016491400c1c210440b00184003da01645200f52861003070715020a174648103210107001585801d00d091012001484c070003800408041d0b5419010030a0740d03080c010140079a00503401403074254140b1040182ca80006030840c131556204100450f14030010050700384090f42e00025441e2211024204048450b0f42c141d151100200d1006001c4100b00c0043d2248800950503011203442d4580a25000202c85050714007030340c443c84500016415140c02e40103a5881a80c10ba0030b5070715402540c0d207951464000c900c04440e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 218516573 1250 218515323 218515357
    0x302090c070b162028080304050105012303060402010f0e1201020315100903031b0813081009080403140a0b010e040b061e0409080f0c030405030d02070302011e0e06 72
    0x5040b03030700c284e40c04e02c60415074032441103000c0c41d861500e80d901710300003040024044a0041380401540b2000b1040510342050000707035685844d28005000340024000c40c80a0211281301540b0a5840600c0d424542000390040c00980c8440e00151044001c410150040102100c0c0700401a281c0c0103031007448003140e40025031241082c0480191114080504a0050144d0000041c6d000d0380548108216501030406c4c5590b4543c45030440c11901d000710f0301804d041c100051820400035400081003c840703408041d600c2c00a40003043c1025200d0700c00000d42001e0081c8024804100c111031b40d03178807600100f0f0486001444540e01e03210f104c0e00907401108a00c00da4020441844151680141c1c060310440c1c02c80c4a0304c1001c40c0070b900c403041c1401c01600451703450070794500b0004624103ea5120b20390f5071121761214255503020341c0d03da01034002c5c903000380505a08440c440780001200307001e40758141c541203040d5014080ca0b01401c0303603680404c010001c040820480c1ca4640740b000708140081c0d121071613 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 218517823 1250 218516573 218516611
    0x1706130b03191109010617041217042108070207090e010b090705030f01050303030103120509211015050d081e07080415080c0306010f091502070806070305060a0302090c070b 76
    0x4403240059114105001c07100180c451f010301f5078020568400d5000030461044100350200b100c0340841030640b103401d212004180030602c1020000d040650a03c05007806680135004002c0322050401d440314005648010002c1c4801e86194000c1c9880038006c0000180d444000313400a80c82960a039511004900b0000a110314070714030b00141409004e09500840c55545184e442440031880c5405079010070001045200441d51080c10600301c52041e48000c40202d489034850380d0301c1d40c0048000e2801d19103080860341402f050444c10a0850f000240005e00d001c030780c1c2c0c540c0e10582d40b2411210701d000d0000003480b8824170400300a80155400703601500c0c1c440d0300b0068000070056048002a0038001d00c0c0c000c03c40726035104811682e02050070310785941041c032402d0050b1100e00c42074200014029005441074420340c0d00203a800100c418107001c8400944942d00306404559007590100d8201c2d000c6c003818405424041d52041d0000b9014004615010064440d401075403000e40300081e2a0034500c84031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 218519073 1250 218517823 218517829
    0x7030c061b02030303010b0d0b09010e070e01170c0a05130b03010501120e060103031101020d0f0509071a041e05040911031002040b0301140a0806040501020a1706130b031911 76
    0x1503552401009440d01c010580380e000607640c0d002c14455003005c46030028000010310040c2d040280700c064003902d4101256113443ca54800d03008100c41020004007000f440c111251f100d0b140e1006d0901f08180c1006058581d00e01c41c80b42607100303884000074043c04001c01c580e17015101e0381e000010500c0d091269120b5041ca000142103071410f80c45401003504110000341a20804206941125031505082c1300c050b201d0b80c1414003a02415920381032151070000080c2001806810483c842ca800780305a44d480c0c0d44a2010700d980b4104443e4512103c941804280080b40742c0f0200d44565107030000681081a58400001d0180e030030708441281c183c261401a1801820300300b0107004910f179400720135400c140c1400b58008a5000505c140c005042e031000851a03241c0b140b60060300903010080c10b07184245842d0400d0f902030340c0070021082c000b982c801406c0442c00c1c218810301e400f450001b810700c0100c1c441c83c2c810f800076045c1c1510507589406080c2085034180d0140d002d500f503541c41603400d502500002020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 218520323 1250 218519073 218519087
    0x31e140d080f07051602030c0d0302100f020c07030311100504080a02070e06010e1507060c080f0703021606020a0e060c010e070806040203070326040b0d0b0f011b030c0507030c06 78
    0x2650101c1e0b14034200f80407003d40c01800b59101c204d40105242c0c20021540006032502d10625006500005411408820315601142c43c00d40080c850b032080c4500101741c41d140f0101c1c860550020781c19009541d080c40001c1c070402c8404c04800b004821500103010440714802140c00036502240c1c0c600d00092003094040e0180310f00c40c0100450341c800c4516281003000680141801e011452003100041c081c001c04007400800c2e6078200b80c001c0010401040c20041c00b0f0300e500741c10740d1010942080300c0d0008407281d00c03030f008a0741340c0e0b580010040e64030704065442c04044c1d00550600030911502400441440d02c1d1000075200c12604500042034580d0b405204074209906508040d00e01d400000030000503850001d0307030380c0403254408291180e40510300401c0a403070452068484000d2000a400100002d00102400d104016a0780420001e4007aa04104070502c0d60403a01d4046480f0040d0800c1200303030003140b021018000c0c1000d1058184980d10301c2d041117151b8000310f4a883c0c02d10740611010ba80060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 218521573 1250 218520323 218520331
    0x70c0609050405100f0b0f0c030d0905070801021306030e0a05010c1206060311091203040b190908030a0c0809060f0c0a0b2d07030605030d0e03010507030204030804031e140d08 77
    0x110b04581000b04158902c540c1d03001b699806175001070794144224010044480307180c00d02d41540d0b10340000a480c40050b0680c5902614240300f00140480c0140e8188200c03510b810107030402504480c42d00c0401e4019044504203c043e034041c060291011403401c0c007520101c0091a6213a16011080340004402c4900d190002c004040c5003032190320010824408407207078103400b1522144245a403096482c1346104a421211007608007150011219020301503181c2e086680f916000c1505072a076500d07503524022021030000003008140307031501082c001802001072400242265143c1015800d246a240c0c0c0140b12a007076950004004c0d80900c1580760303240d038111703107001c0260000c7d500030114808088440d003440c030652100040031801c05c0d8040d5110800401c0f001d425956065045040500b0780700c60000d0740b501950806000500e594403034402c6900380c036803000320300d0304043c2191110b418007505031007100014100001f2000c045018201d085221140f00c400804040308100c50041110f180a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 218522823 1250 218521573 218521591
    0x70f0909021201050409020a03050718060911031627050a080705060d050a0b120a031103160f02030307021c030f02060c0301032603160810120314070c0609050405 71
    0x10202591002c00380078028111002207401080c0c480d01c0f1300000310005025400144903100d00074000034208030000c13070700d449081202001c00120303035035919100503a03c00c2802050b445104200250151440c4140324030050054503041039015503620850318142816410000e0110010070200403d180c0194200c002d4802400502084c600d0000400c0050007428400201c0c0c03529500000c0500c12a03900140b284000209600841e0030700300d542c1511503101840c1580012040d0001c024031100010445012400c0c0e40452145044251269078889140030012139250104100d03c6002d40c3d59400d02d9502d0b43c1510842c26034003289468003803c03200180401c0700544d000b07a020810f41840c0c410650781101c1d044116100041c0c0d41e08496482c184140c01c288412400c04024002c90030300d0030200c0c60f032111054444410355228540780f6a5040040d124010b80312080c2003038200024401c141c0c845100041c410700c03c1c1407560b030307684081c01c80606810a00000300da08404001174582400b880303412801c54 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 218524073 1250 218522823 218522827
    0x7081e0f0718120203121602011b060f05040b060a06200709050907050307060f0c140f0f1b09010e0106050f0c070e1e060d060513050303091608032506060e070f090902 73
    0x59440901c7c080e04240c0a41440130140174070309801a02a0740c6007020b40e000c01c1c2040213018015222380240700c19101525507a0b520030005017981000b4000c0810380750b035034942c0b03240e200c400070b031207611306006604800310f0b40201540090002c150340034043c0034100c00710150490504280c28545056140da02810420281d1401e0707001943d0005840381107690003401828000111b00091494007032248280c0203280f040172412a0344250104d0018030006e280031325521039141e50810409214000e0050340c0000b01003c0c0100041c6015000511400a0080d0024185001c1b69001c40c11312103030380d110304140c80800c0c1c10407802000700200300302c0d0056019454071240c02d003680490710000c4503850041255075100301007015818240a400f812540c0001101d0740d0b40307010305845495180b40d031169461407070a02001300d00100080305852412400c100e201c600c941d07007100c1c1c400407408085401d40d0081d40e07074007001c2018102125810f1042e809134403541004040100000c01000040d80900851441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 218525179 1106 218524073 218524087
    0x7030306030803180706020f1f0908040f090f1b080c130f03060b060c0322090507110609190303020702040f060e07081e0f071812020312 60
    0x24130f0192030240e0340d1a10240c1e0b5030f01e003070787c8140b1940c0c01005103035a0b040101440d801c07200d4480c01003c107070202c0c01d07194010507910030342010101084000c0309002e241158050b0003481200d0345405c10084070182d1034201c0400c10301d2007030001c00c1406c2000c01c41e101440301c2502c0302400000c051039100c903600da44e00024030860344011640c040c10300010488600d04007041c4d07410150000042c504d8410300c03540103003180c00000b00c4500e80540140c80490a1049807060922640c29900d540b1000c2d0401d071252498988028032500455001380c8900c11994a407225140c03020380d0608016071207034031910000b4003074003c4044480d2a10b150180009815003c2d1803058058252030b110400380d0344801141c0700c0e42009400160f11144101004520103480044940f588144076181c095005154007003840072440f00b681c01003800c1d034850508041940b400b031009440020383c0070f50321032820368 = true := by decide +kernel

theorem cover : BRFrame.Cov 218345323 218525179 := by
  have h0 := BRFrame.cov_init 218345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 218345323 ≤ n) (h2 : n < 218525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
