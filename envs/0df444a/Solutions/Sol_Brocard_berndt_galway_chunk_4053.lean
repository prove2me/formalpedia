-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4053
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:26:03.916743+00:00
-- url     : https://prove2.me/submissions/88295dbf-9f0e-4d88-af43-a33c3f1286c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 728776978 ≤ n < 728956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 728778228 1250 728776978 728776981
    0x90506150c07030807110405070f0906140903151b071505150301020d0f1406031e07090609020c1507140c0a0204061205150106051614010e010b01030609091703 70
    0x24810b2402d000c40c0c000501031100058100f040c40180501005002e00803039041c000e582e2440001c4600c40210340d103000121b903001005000301400b4201a45082411404103414903914200081c0752908111101c1c600c49520700a120401c00402000d5401d074041000302c41c44d15015507104c00ca01c410b030b8044589260317510004910b24800048600203a039200400a544440115854400901c56404902c0341d981c070b0004141c11500750380084078880d0a004000d803904280c00000f207000015214155000ba0003484000b041c80304c0e482c0308032400341c03508160041e01c0c0c082a800062a0000800c210440f07483e104042004081d800340046d50041100d82c02182c484005200300c500e00100d90100a42c024101003010802128044200c410b050085007200c58030710042c0420780060a0030300586001032010002e40c00944081410030400e14420b04505a0801030001c00c1401c403002d4444000d000d03511401c3c00d03900ea40e454001d5902a0680340000c12805000703a5404c1540091285a90481d600120 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 728779478 1250 728778228 728778247
    0x90b030a0b0a080d02010609110412080c0303010e10060518060c012009040b1008040f080706050412140901020a1407031e061416111c0201020301090609050615 70
    0x204510180750000c2d00341090543c49805658032041e110751040c0040d8644100014140424054418062001c078045803030305081040075441c495402c0c2d025100350004101c0807003002c800304000c5008142d503614110440c1051070214120f0001940712404100040c450f0308207103002e140c1c20030990300049a130155100c07140040b15014010b00702d83d0102e42c0001080f4003d40800da200142501182180d082081e50f05c02d104100030b20b003110180b00002140c560010340003514421400d0090340c018200181030104a5460f00c080d118111000c44d01d02e0b1140c030000d10441d410844020310050107840d030303500704080a00000d507201d19090015040e040c03060200782e6508000e2100401454001002d41a015848a10501e0242940b801180d0312480c29030090602031003400120300a0224408004024030010022182c105401d03203641d1040c080d510301002c01003118401d80d58030f8031003900090b840c2c5d850401c04400f02c840c1c60f0f01c06030036141044100300c0f45644a5001820060031140450307203034502d10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 728780728 1250 728779478 728779481
    0x140a0e07050d080301050406090c0207030605070c0606060f0e0604150e13021201081006030312021e16110f010f05070816030306080105150a0b091210050711030703090b030a 76
    0x3035001d40d800030801c0d1040c80610560200444c10b9a0341603906129090390f40c96828210b0708401340300001600590428030000316076810230f0707030408680d1502d81a551650303110311084481540c4020045110002402c071481c0d08820644d680000844200b810a490100071110124041801c1000c1040d84280001035564182c40f00c20344102d030b00c00c00c540b107100c4149540003404007809074508601c0b6006034034981c40900c2c0602e5003540c2d410380d2200d0320402c0d8101c81c1c8c0302941107500d04c41c580c03d0501100f01942d40ca0038001e13000210300c1451501c0800182d00305480c125104001d0f00b4040d2003038101c81601c6980180d800b0944480c40d25145944507514100602c00d4001d4034400710303540d064800c0794004d0661503007040041d1031a24000b08007688070b0035100101c1e5170b1030100c210313000710480404001c5080200054012844080c08004041c02c800510074109003c032a101d1000720350310710500140e1a8800a0a199055003400461511000d45c03009882c0741e0452007003100b159000000540c050146 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 728781978 1250 728780728 728780743
    0x3060f03150a0e06010e0103111c02130c321b0604030c0303051509071101020408160f06020714062505010608060705040f0306020f21010315140a0e 65
    0x36441c45011505105501601811107002401e401d0300c00c0d04e00200d01c2440811401d41203d5101000c0105131700040305010444000d05c054000342d40e0b940442e40c0140e02c602035001c100d50007810000403842880000074206142150340a00c1086250f16030302000c182021034411003040c541c41803a1614407844080306c07068290700d0701e00c02c43e004400500040503000114154854031079141031049507100c06000c0c0c2c1c0f21441d001d80390707070000282c0045101c076801110080600385a2030000b61600d03032282e0f00d0924200981c4400e4a441016200c10452212600e01a00240200b480a0403a441c43d00201d0b050306c1d240240a50320411001490b01083c01c40400e030354000c1d1014000b200020012410721071f000f02540d20a400850141d0000035a803a8482e90848042d9540000302d03c5059055442e640b00940105003a10f03140d2600300b050a000c90407201e2215447c40c00810100d10340d42c190b144c28000a8800701d5071044030b034104505c1c0024102c83d10003031580060410390004800903007000356440e0154 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 728783228 1250 728781978 728782003
    0xd050a12240603020a0f1b02091f081006090e0a150f0504030302070c0504050705040909050f070b040602010608060408090f0a050603090703060b0a0302032e110d0b0103060b03060f03 80
    0x12420300103a0300c2e4058000d0319508a641d00d4012000300c03501425914005002c5900060045204001f0700510341030301809d400c150302c290780e48520044640e20402000254218048aa02444146010842500402c8003070001c080040c04100c1035009620b070340d516480401401058500c1081d00c0d4001d440d800400e400079240414401414a408c0c080c000350302400c001d1703a50129040b800b05480c02c2c130380a010301803911941c5491410340703440007103c020728101d407045569000c0c60600c02c0b20400100204030103005500313903460303440d8580320010f400c40d400380d0301110301d80d000401044041090a801d0b101490001d8440714032180c0000c0002d208880260003003a44940003205009540000042c07200079a40b10b08020000c04040f5400c0120000c02d6120003949036110064204000d8860f0b50f000c400b201d140040b205c4141c04408010003503500d0348c5128082c1c00404110091f180d0707024003031400d1140d800c2c00e080000b80c0c100120b102c103c1c40010541c0e40a00a148140441d81e10f0820900c4415036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 728784478 1250 728783228 728783291
    0x60d120c060b09040b0402120c150702010216140316081002071b0b03090d030203060d08070f0b010b0307090b09130c0c080409020406020f0d080105040c050405040504060b030d050a12 80
    0xc4c09203010580d00c0c90554007640139000c1c5160348080d40d031000030060045000108240d03100142e005e40420658000d400407411809032690782500b910354140d1100c003074000c2da0135080f41240400c05040c5054040c2c1440c0c001d5a0849004008218000c20300c980210084500580e8521080c18454221440410310102d410100c8800190541000e409103001d030820b001520409042e42034103e06078042580e010f58000008444040020708000080144d14400c100c42d4400b440240c681e07102505003648188115800001000322840d4801655005001c4070b1451b103040c400007202060002c0881c80741e100c3d51950359406984228000c26414204940c040b5600365900e4403544294080d411501c15075016108188103010ba20300c012030680c00380034182d511110243e181c101008040c0481c480800244a0100000306171603e482c040c0522403070013004007003800d0b03c1c00d10a02d460034520041010070000c092200c40c5015071f10181d05020017038540c0010a40c000c01c00c1f507015180030500c6000c100c61 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 728785728 1250 728784478 728784481
    0xf09071e09180e10020406120b040b1002010504030314091507020c060703090f0501030623180906070f0f02030406140d02190e0a0f12050c04060f0806060d120c060b09 73
    0xd140c2c07600080d40c80500c01c0f09440c0c2c03280c00001c840f000c0e4003640c0603000102c1e84a101d0046a1032141c1d00645a082d001007000c2400070941d404078005000000c05080140d444900f08028142c05016083d030004682848500901e086188142c07103407074103511414100049004144014400c0040608021004105640d01c1e50700340380c060208127070761182000421605134000384541c02840742004480002e40254250080c80208100b0b4111850109501000602640d2989081c070078034907205117007180042009013404000079010401915440003001058280404084e5000c01070b14115609030500c005a89281308248540d40545a01442c101b8070100e150703c1c40c01401411001c20040640341c50314500708840501007104240e0007004030901020904000b0040740743d030300c4682d550048060710300d0010150300080a81d201680030800c0300349000414020a041445855041002260004250310031552606400c0d010504006d0074042a02e030740d481485081d801482803401d000b401240780c2d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 728786978 1250 728785728 728785769
    0x7062c01030f0b09091f0c05040620030406080a18020105190e03030706090c170c062a060603190506070f091509060f230d110c010204050f09071e09 65
    0x321219030303031442800c2d0000818030402c1113603441075086401c0f023581c810345802e05184003641c2c0e0341c0f03421141032a01e04420600a00c41c800900123000030340281c0e918402071742461104c00d0305561740540005240644050b0a50050381c00c0b02c00c94420100c9558000b09800d22001c058800c0021401c1207901800700054490411800394444812184603007030300c07180551244025103c050106202140c6544010b900c0b10403440c2c2a000f820340d03007485201e9120490f0b000c80c4035841c3c5440c200400089644010305101030340c50309120880c9000201c21085210010b03585449540d40d401074210b20510404201a01d9258482c20a03280904144803039980c6003036001a004042d1520752003440001f078546010b10a040d8400c2051920601500341158586041096840c038036901107404050525619102038a8500d6004003030402c0304c5c1d200c0001a100d601c2d01c0140400a000050124401c806c91010083c0c419084180000440da800c0078880c2c02c502c420009484e4020709070001c452801d150f1b06070a00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 728788228 1250 728786978 728786983
    0x1020a0c020f1903380604050f010305060c0f16050106030c05030a08090f011413060228030f05040906030b010e0c13140f090f04030f0f05041a12040507062c01030f0b0909 75
    0x11b42050b1410003083d55500706080480e0f60a02005201e6000b420100ba0024803c101401603809900d12103031829101044000305010090780464040c0d451b0f10b420802d10150791480030040c001038010b0501c0c90565603e8a40034890300c9441449030900340400e8146074450b088440c2d084100d040031641e5216070f0910b01040b0b8401c3c1c450640140314802070001c5555151284080110441c540b4411400603584c090b00d0036100c1400d0303001041402d000006031418540a204021802544d6210b0305505207100c000203107400400c41010328030200401c880031418000b90710116804446c10400111083e40040d003101b00e03901c0c1c000e50103241c50b41402011202c06244a000790310070b8940100c400b0410301c1c2515401c500c00c500d10007055080c44104910b0050f10b40542c4070702009814140b17000c40d650380806101d0025281550309920211060007160b402100c81c2040c20381c011100000c0302c00c11b24090034110a0508500e0405407a503d10440ca040c40d42c22412207640014221f980034900750030b603140e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 728789478 1250 728788228 728788231
    0xd11030c0102120f10180207020127060e030105060303121b0d141b04091107060905070602120405130207031b2409050601050d0f0501020a0c020f190338 67
    0x3019050000041170501540051403001c55210b0500c4030000c01400c52144001c0d0010700043e41446245000401050b48801c1014994052080034900c55418540c0041084d0384403d11140240c0c540018401d25540c0041900d0f100760402c4036100b4140d80381041c200c90a801d5a1141c00e9868020a82c10050030b2244c010f81000d40c907404400c800da5443c919400f050990608050381c038044104002e104c050140e8000d10a0038004800c581d10f4a105542c130403007180c0d031100e02915950480402840704a6043c41091030f2808180456810581020b001070003140c0240b084203880d03a40090740100f05405036072050b00103440500700041d00840c605050428071110242032143c0045140034941c0c003111885410040c607041070003040168204003d1262030f4108103003c0c0c0b92200340780b1050000480c240010b0800c0d004035550411036150610502270820304c0c40000500c2007038440c1000b01d000c07840890810403243c00c14105001001c941e007200b10345d122207544034000540c2c4208400b0f1803521120035203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 728790728 1250 728789478 728789491
    0x3181002270103090b010e09070324140f0a0513120201050a0629180603070f0210060e061009090908090f0f180c1b0a0201140c0d11030c010212 63
    0x400d440001c0100460803600140f0303009202c034441070014002d81d11500d00a590140304a012174480f03540345d4503100b401140e03140c0040901608542c0c07281b012465030103600e03854400c1709004060b50601010010f4948001025858080c2ea0b41c800541d41225441096000c150000c814940d62079400e18000c0c040d05044034002c20b1141030000000d4805031400000940c040d21034641040351040411000899210304044502c4c2000c209959400340c1d00d4400842c017806180d242c0900d4440c0705080a803c00041994409885203008000c0100580c100003050784420200d03140210501c0802040c0c0d0010303410f8100700c0c01e01d458030707210703000700522130000301b10220040b661143c80351425001c0210742c0b0039a452254112612000300d00341080072005480d0400300c0d1031100e50424600c11050000d40c4a550700003110341e448944001c0965801203403824501013403e40980c6000e148c400c4c4280d8403061410040200400c8800403c2c080d6801c0c03040c1c810070b02c080b0000b50f640392a000d440d240c6013a001e030b890 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 728791978 1250 728790728 728790787
    0x403030c0605060303030601120504020402040e0c1222030f0c150204091104061b0606030f03050a0f09140607030512310c063f060603090803181002 65
    0x403d5076450300000344d91041e00140c3d0398607460582078844602410002c0c00880e0442c1e020f01c000300341c00584100d01403051040c240810f807594401182d6072050040035007600070100c1000782d03581051050715404411207402d81451009030040304001c1307802a000322006000080a80452440e00c00320703400900c01c442c2c9241c0c0038440320218400c000b60510440c49070703202094514580021801100003020080b03030280200145260b80d0303403107600082c58041400c0340003030307000a8103521064101e0340c81009805145410f003149803c2140b0201c550810010352440b030f0030042020020184940c00f161000050440e0820700e074140080b805040c40006490324208100c0d1b04406481c03201e00a0001032402c3e007241e5503000c203601e8100c090340c1e401d2080502111080014455400c6210040240c2c2050b80e5407a01e001d0f903030b80c018442c0c00e048481e1a0050010141001a1400400c00c01d030140d94000509800001c4e009a00e2500076103070142485188185c1c4c0d002050942c07040644219820a22500020707 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 728793228 1250 728791978 728791981
    0xf032415031806061828020409140622230709050603040b0109050a0e15060f0d0b0103080d020405031e01050f010608040f030504051305191b0509040b060403030c0605 73
    0xd01d030700d0f00c0045132103035045150135009941c040365065403140c01c1400e500703040e0103492a04070110351503c045440b4130320036a0001020044852544036002d550b5500019120540c10490006000100c040f5440566000351812100840002e03500088440c5400096541c4006121102c541118400c660782000b1032103594000410303050000c100d9116941c410704040280e800c1c820414000c00c00980100c1285030340740c241d6030701c50404109648500c450819040c20750b103840c00400124088103500d0a014181980d2401c000454140c00c140c150381c0d1001d00680c440a01c00c600000901403544055818405c013012040021095081c08042e030f035160b0002e004a03601c0710220303118814207108240c00103400314005000302d8043c000403105148a07140180c0b500f13a6810001d0180054000560001580d43c414401c0c0c40003070321071101044801510038401003558140e01050740b010407a544080c0400003c904409603515880010003090007402c0340e84960701c038140103103800c080d8841102c03020316180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 728794478 1250 728793228 728793271
    0xa0503030910030c1701060203190e010e0d06020d050408030a050f010e061c0b07180801090201020a1e060216110102010515041d1e070b0f03241503 65
    0x8841c8010400742444140304034000086000f0710701c103c00e8000300301103c0380204c0c5800090a0590080010790b000f541c440180402c00081005041c845109005c1c004134000c402d07036085504081506012140d9154102c02424444040d1003441140341820707181800300300401145001031405148100c00800465407402030703041721544280180e41c8201171000010b1814074010701036514003880c40c1e40301c10600d10560b494408510003601d80d080030039001c800c0c00b420ba5482250b00350003031400030024400c1c1201d5400103500d81c82181405042d1080c141d0b070080100c06402c42450526074404421507440b0950054200303490511101114145022400b001813588140103480c05414000789810311464070400f048000c010490910302c0b0000440c0b004d840061052200a02c100d4252164010220072075103071a0402c1c41c29000b404010006000d40300281012409480c5d10034000e049070016400c0d80e0380d10823032440010316800e13807101d203401e001c2180c4480038015500407446890f4002c0b805240d603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 728795728 1250 728794478 728794483
    0x1c0302071505270c0d060f09060501080c01021b040b06270a080606100807032003011a181522030209011a03060d031803030201060311060304080a0c08090a03060603020a0503 76
    0x1c1c002002c6500c41980f0004c0382c0b030030400181c100c5102d08400500c18030074410140a4441e5034500396a1165500300402043d40b09000310200d00100348042c0001c20450070700030300d070325400495080c0511759480400c10582c40c1c860840300300c8610350a428034040c0d00412440841780750980200e000300061302c00040d2808000659900800c0f0003003540c680200d82200848807624000d04040c101a1180041c9003a1481441035050700c03003240c100c0302d40e01d604051484c546848540c001001c042802c0106c09078041c0c84c2244000d8200f07040311084982600101c0400303c1e4011440c074001c02d60000c4c1e00004a4600070501c2408a82c070a4401201c0c40c2e9984660710844445a500011031004c1000042d420740350100c401481c030b51283c00d09240c400310509913840901425001100582e55841060040c0043c840fa078000c106021149a4a145040e0384c60036014052032260300c0612600030400e5041222020548650042c0078204500b400c0d071b85d0500e1006440c491206a001d400003410104050402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 728796978 1250 728795728 728795791
    0x40b1018052502191e08030406051005090c070f20280303030905010609020f0706061202060a0815120c0a0e1314070b130e181c0302071505 61
    0xa0380191500d607003070314090316070440745082c05c5500a401c12010340e5280a4040720800ca0b60140d40142e440e4034041c903101f012100098200c800494491400b00f025940304501254441c0b5004802500c80d000c528042e840c84030181401040c03c40320f80c91501c024007690b0403001040408071600d1410070800d45200b02c1401c11180c101030116103c1c001031000c41e0081d000380c45000c2c880d00000900a903100c0412040f41c100040e6400f420300700180410510105020354801740c0200c0e1103011500705286e000030060f104841c0458184200000025150040500700040c4968094109a4001110080540c50b021945c0c6400e01c281d21000c000324a0340702071007009120f0400010101d074004030f25204c031800d0b00b00c00050a030700c1703118240002c100d000c0746030040e00d5660008500b000116042916002c40104010545203007107082c804207402440c000224005c1a60489000340d9920886940440c00707440380790000382c684460021100ca140005034440ca00c1207003a10754003500d403440c0780c003c041c04200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 728798228 1250 728796978 728797051
    0x71e1b03080a0e0d06050c070309090218090601030f141609140105090a03060f06090b0f01021209030f0f03040603110f07030e0409060504060504050f0c09040b101805 73
    0x2400b180c41641e00408500c0e00070b00004180720b0340c2d4881c5503945130a4981c1161058481c88000c41e800c4201131700722007c03102520f0351031070941c1030102881140055445500704076100310001800710b11070782d00941c4014881c0f40120800e02070060b04428644106400307440324864941d4050760840f40c180b04119407401c2d50703040501464904044001100d4541101d5000c9a110102000008c0050014440c16040b00420745021907440d14008900040760b08078a00940501c1c558120703682284c3e07010a5041007c81d4041c01980c42d0709045000c0b071303e045411080307819948990485002403a000201500480c0c5a0303507014440104c01c1d0986a040e40217064040f00c81c074000b071010600087c064441c0d1b48919001402c000f50614054564405440d130694040e82d480e0340d12010320040c4001441403944407408040241188610780020451000e0001d2002d00740c420142d01080d00f03400b00c0414200180904070180d40d544000001d100b0081c2803d0321a45a200308a600901a032940a100001c00c602e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 728799478 1250 728798228 728798243
    0x50102030a1b030c0813050f1504060c05071a0a180602071119030b1b0a03020c1203060a032303030412090509010b030708090c03031303110402030103110105070503071e1b03 76
    0x40700c12a40c01b0030012043c60440d00b60040c0202d20b40006410000c180e81c00ea8043c0b6000300d1401c0a00741407080390f009483d4001080f00c100705402c0400c0060482804c1603008410b40c0c00c8a5451002c0030300200501c1443d00c03c00c4441c1100301d42440030076006003c0c0d19005503a08000110040100b22100c1a0850b0b0001c003021290420804100c4443c03030070381e0003041c0c08400380d000f04008502041c03a40c4440095000700c0d50119801480380300400c1042d00180904880c1e40c518100000000c4148426110040c1a0783d040d11740600c01503401302441d6260039264003101d44a00b000d02d406400d003190149000c000071280303c2d0000ba81d24164110604179500285224510b4072031030310071103100100602c4d041542c03054004202050310300300300414116a00007000e00031903056182511b000c2030600c213801d205600500040c00802c1a050300340c2581e0100f4200150f8806261810a046010f92480a0801106110300700078040348031380d200a80d14881d070840865410f0101e0100300c8035025000217001d64 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 728800728 1250 728799478 728799481
    0x307020a0b090a0b0a030f060611011521060906060b03010e0c0f0304034d070506041413022106010c32010e07080601060c110f0607050102030a1b030c08 67
    0x40500004c001720b0106240106201c9851040b29040e111a6030007800094141180c0c0f040c01503080c81303041d0711080d04000040915190851203415404807081102e1012001c0038039900f0070103d035002580c25580004240a4580e65104000c00c41e0000d10400070121030710300015541c0e4014504581c601c0310103682560440d01c0d1903c0486609000c80890100311040b400403244a203a03049600205100141d14555084ca884c120f003000021820800007095001c503900b40107664603030b011785060301c00b403444103001c1c0d0602d900001c0e0440b00c041e81e0301e15810b2000415a001508150054039110819002050316031210310045441400700c0c0006440f00150040c007501e845d0f800540c803200590f041d9484860120440202c608442201000301c5140c0d01c0020104140782082c07002d140180918208103900d40c081e51695000ea903a14444140b00700c8800300198003654482059400940e0410021512440d0a4404000410070724203090344c00c620400d820070115200b130140c200c5491083d0390b803038003a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 728801978 1250 728800728 728800739
    0x33011404061d0d0618140f0705060c01110c0c0108070f0c06050a0609020d230405071e0b0c0109110a0f0b0304020d020d21050a090506030a09140307020a0b090a 70
    0x40e1500c000d00b180e848020b840b0200e0109880c0d00484c00300202000092020b58030a03c0c02001d000c80c0c52400488607040b524001e0315014000c1607003001c444065076202d50b252801c0c040d40e8010310f2004816201024007041110b0346000008003561200c001b038880500d00d03101c50b44251a507803500c0c04490002034202d80700a001600980005401c07039a110008954161180d08500607a0441c0b5400c104c40c41d07481d200c3c41d01ea204c590540b21020031030701103492401e080030380b41d403902c0390700e28028241c1d0a21860081c828440c0c4003818640182003540155444001002080f8040c00305403809039090020540384040c2841d102c41001c089a03c1440d1044103545804240401a000280240c7c2d102079450f01c81405a01d95101e41c1400c948a0401464000c050030340d8a0b0040040c00450801c10405100e81500c3c41d1300403041105582044132025100ea036032014450180903900e02c0200301d900b200d1031200011a00002400c0007e00c01c4681c25103881c4c5920040c66140580c0031890343c00048078404000c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 728803228 1250 728801978 728802017
    0x20f0f180307060c0c05040e0a030516020603040f030e031c0c060f060e07080115020a021219080a02070b09090703090327171908033301140406 63
    0x44036044050181031080580000e4100042e961284020038800440c03041080003602c0f007600681403c0b1420000e0780507188090b50b80e0f1466103002000c4c0880054141c40c400c4d1000c000c5147c20364014419540c0e8074280c80c201c244030102420480110b180e14507104901d207000700e5600c00440c40c03044030006642004004586c10034000d001a940c1603515085403000e150b45014800161030f000b2084c0c0c0c81c500300741c0710043c05c200c0305a111042411068010040065010541d040320039011034100e50b00c103404c1d2036107504001c8207011007101c5d45404c8011904000c100f80103081c9481c8541c090700c42c07080d40d54100710518460001103030b5010070178000140340240698802c40c0214040c1c6058122043c0d03d00046c4081090641e0842c0c4100030140f04202c440722000c114203d5071590000b40412120303c0d294510130500a15004007500300c08400a01c900703101c0a40145541c01c5821030310300034030322115080503c190030780714180042c0c1910300d09220841c072542113604883c0d280d0f490035240d583c540c40030030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 728804478 1250 728803228 728803237
    0x516061d0112320c0f03040f02060f07060e0f0d05040b0f04150c05010c0c020f01271412030408060c0a020102040302090f0709080c01270e042301020f0f 67
    0x403449940700c04141c2440b103440960b112140720358080140b000d140c5030444a4024004101d40310138101007050707146440600060340e030007035400000f40316055618400240f440c00350000c02c000b00c01d400302c1c0391010300500d038000c00103204501050340e1004085d80d109075141d41c4007600082c0850401c0000f04641e0411800800515201c1d42d002428652603540c040380100f0032140c04c500082010080704103102d002e100340140018581024155981c080c3d0108481303004c0400d545040c000402c601c0d40540d050404601c0c0c0ca403c40d86460034207952201d0342001c00030943d21080d40594a441c1103c0300c9800000104c0d800d5a140b44020046031313545510002d2903611100e000f000b155000d11000005807102c12409000784141510f02c6070130310702440c004000036400e9010320b803164071404410800d642c0000c80c1404826a2050424000006400c80031a0045070f134003542c4e0f01b810354010071040c4581010700c4951400001105200845180003103800c0c0e00810303800d980144030400842004206540041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 728805728 1250 728804478 728804507
    0xe01020111031315050c12092d16061b020109260609030703050304170d090b09010b0406150e010c140c030d030902010e090601120c11010b010512010308090a080a0516061d01 76
    0xc3c3c2c031100c51041e1040f2403c81c27070131110180780301d081420001460144444400e00e88250501e4052514004000308000b10203890310202c13103d103002140c20b43e40f0035802440541103100310440110340200130381d0f11060481c1d148050b14080d81000c9441c10001108955007607130150f88442c1540c0b15174442c0101c1c00e01055030403100b075604008081c000c8010740203210f0b102d80901d6500300c0500e06007105500352925409030303034403c0c4d10b441c100b40b00c50b446039100d040720342c2c84c030b0301c0d2080d0307038164510050303480202029015141ba00c0808070b15070244000518990042401c0c1c0039298446105041501035a480c202c1c000d0100340c135081481c0d040e04100701219800ba0781403400303881c1143e000d440d46085641d60300052002500055280c98490001d0251005212080c80d0451404281082e4210920018000109030703a900040c2e005040d40c0d500c0d50b400c00380401009039541d450b01ca00d4443d540d04c09161203010035007084039000451601806100b0710680754403403c40c002c810b10000444928040c485d06 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 728806978 1250 728805728 728805733
    0x180705030c0609150408060405070608010608090a150b03071203320a0c0219050f1519050705060106170a0c0c02090601090f0b0403022e0e01020111031315050c1209 72
    0x786d403032001c10909000d14016000340c540c0754144030000b000d48605810020906c585441072080b41c0000003039880205400c45040703000020040030003805080d2402d172130b139454810040003048000b0003601500d1598800c0c1c807001c005030300712100340000034130018400008501240d000210780fa491001020b91141c90310740003203188450350015030007240440c2640c52030f840142c8c0a000c28180030f40f4404003248107c6241c0f03030a18940d640c18429201e6280140c024180313140303c84000900810980d003074141d0010940e00381d5030719248000d001240710b200300c89008681101040c00c541040c4200440324800343c0c0e4407000c07140c194080c082d0345200644a14100206540e002819199061248000e000b0090515685600d5070040002e91074003200e8445681c503c400025480040350001103400d100c0d20b040c802e0710010300c080182e004049164545056480c00410000c01a00181407403041078811100884840d00803e024000c0315000c54010034141002c100268601e490740d56100d0703020419408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 728808228 1250 728806978 728806987
    0x607080c041205100501090c20072601021b060a140c1c02030702010209010201150f0e0a0f0203010b0403050d2c031f0b0a120b04080c010212180705030c060915 70
    0x900074200c0f2402d9003e172400e2030341c840e20400c150b64440180d104840010f281d042102707017049901515400d01e445031078106984845000140614800c0e900c030101e2520b0003c42d140c002c8124550118956200600683e000b0080090f10454061140b100a10f07158850080c456035500041c0a0300d5000b43c43c0c14028103444c0c6c0b10b2880741c150600046204805682c00507889143d80d800182c203580003030903100c0f03c108403080244003650811245030103c81e50403440101035269140d0309030007400302844d01c46140d400040045039000c8c0000c002c008a91040040b1048210044400c441c0841141200304084004282404580d5418010b080c03941d4802000d0b1440141c5818940c98044564484003942d1504c4840b485e4403494611320f2000240348190b208010b041442d500c0e850045002000240220000f04003040504401d506407400a861420003080c1c0d0300307105003415940c845921849000e841001c10101c0c0500b800320f1a0300c02d000020b04110f08050014081240500c50506480f544610074070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 728809478 1250 728808228 728808253
    0x1030b090f0d0f021b0f040b13020a080411040c080601111e0a0201080c04030c0918060c080105100306060914120307110a090e0a110307051305090607080c041205 71
    0x1042e15800111511010881c0c41042406410100d0020000c0f410500c0c0140012854a5050701d140001100b203900058410a0000081103840c00745a840c110340d1000c221010031a801900c60740c025800352180340000001001004160f59090542a0010b0245c1000c608a5406003403e07080501241d019980c00070010301d00700d8000d00100d0010440daa00103082d4206550300042000e4101d004084a20b01c1c1038110b8651428840ea02d21035101503c0e6a90010b03450b48140d948a03861050340441300380a546070450740101155000e02032984a0a13440c5445205140a4843c400882e0707055154014035034502100c0e40307081052080440d13005160002c030001d550200348000c04109118502500c8805410014046081d6072a00070303c66080c5000d140c00384241c40010002d00d1a61700c0b4035862032441040d40881d0420000d0340c002a00540030140d40d020090701030b0030081c420f004a0040303821540d59600203d5403401c094655195040c0f0800c02405680c4101074400b030410301075000c0710500c51052 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 728810728 1250 728809478 728809483
    0xc090d0221120301090516171314010b010f030b1e030a0507080a050c030d081807150f030b0d170307030608031b0f011e1a0d06060819050601030b090f 66
    0x2211600b9000000014031180c1c05078800c0942113805c0708824078980300c0000300500485880b07d4505901002400002c130190003114040342540d502c503c1403480b2101040d0098068118081c880340420500319102c03403060304c030b8890319a90400c000e12044048140c00b034240c0310076000c1248103070180140c6480c40c0c00718000b00000d10050010314001c0010140354244541400202c0800c2d601c203401c40724070510081d50003003a86400a0b10162422034406200400c40c0c41c0c01815440420070b042c6501e4001c8120741c000046a001706c441c1d44041c00004005000c0041b105810300c0014044140c140058484645150246500000da820005495900d440b02c0c9480d43e0041d1140011120402010202100c410b01c01c00b1040d070090f078000d1040c00366142400d0060042440f01c0b07180c003540c607106081040d18242c80d034820030101800c034000480003401e01d0009000f10303003d52030341c0f880f44842101d80210300002c608040341c3c0010281040343d0841e91415035030300018108011034400c1204440f00c0000a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 728811978 1250 728810728 728810743
    0x5071505100e010b030c040608070309050f0102040501110604080a051303051b0112140613020d0908071403071101032013060f02031e070507120501020409050c090d0221 74
    0x2031400807591509000c0c0e1002e860503040411810b90070301c14405154a01001e4900381c8030a03051010749070742e0b07105044004000c020009019031140005900070281d041d0b004006849080c0c1e03e554520001c601841c1c0e84a0040d10000d0101c00e040010204c41881640a042d59a0011704581c4515640f034641528095402080005071164150f03848a00e68000c0c54080201030041c80074405450305a203a40120100204064058404020368410005175541220a011029801084909500d05041041360803502c000c0b02d420500c0c0303140400e40c40000064431081c075130100364000e4907522100114060a040012019940d031418480e1891003090b50290040950740c03180340340d2040c17400b500104200e61185000042d07400c1080100292210b5400c02130000340f4109106135a400c0320700c0d0442c0342007980d074400e41c0020b0401001504225040d0000c0044640c03514041c80a5103504d90b41102d14869403140a501080042111005003400ba4060300a102010111540c0c0080010303400e0402e500e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 728813228 1250 728811978 728811991
    0x6091e030609061f06020c0108250306090609090c061b12020d0906030c090308070c0f0303090e0f0601090315061e09060b0c030a110a05151e060303090105071505 71
    0x300822130f0700203001c01c51144a40b07400da6144100307850301c1e00194481101c0101641080b0760b40b000902620400b50a210a0003035103000075040226241d00100106040c2c000c440c101030030b0520028440229010364031701c05410550000c107483c03810703406840b07040c44503c2c0003c0f411420550100461416188051121010b07009020080180349000b081c410154206205261411078501801940040200142c81d0f00045440c2d843c0518101044000c2641c0d01860514908150100c101503001c4041e404440b11980c04c1842901c4882c3c4440c05440300300c070b0b460700059144504201041d0141840c3c0640310001100265158590b580a0302150440ca000809849000382c1000f034054076116100090100e0a8118102185a00f009440384202880e00080182d845481c0050170018417041c084994440222a4064005201049a40c80031100c000d000544000110962282d07031034028422080200a03515115a4800545668001c02d40644210b2130f1404d200410b4240742c800c4a00561 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 728814478 1250 728813228 728813233
    0x1d060d0c08060f01052107051c05010c09230d020d1a041b0501021216170a030f0b01020c030d05130320100c05150411060a080f010b04030206091e030609 67
    0x18140014060301030781200a019031b1182090722403005060104601c0c007076420440f94070448002100c0180449491404041c11a5213444d090038034203a0003001c01c2041b20f2000b000841c0300009009103c441c0203c16012903045508a1840070047c03800030071103035041d8442c001c0c106249401d001c02c0131036400102d42c01c68030003401c11100b603400c0c0c6c0c108010304010034007403000300712113000076038000d11a01170300070302c01500100d5680c1c43e010042c150360380d4208a22648210741e164105000e00901070003900700340854180c504449000b941d440030039403030b1500001400178400d444e51508215001c0e8030100c0441810210030f8008800200c1071002c07018640c6051140710444900c0004001e41c1c40c0054403a4418000000a1400095008903a910203101c0903542440103a5441c103050000c1030000c0095a03000800103030445407941c1200406e4050003400303040140c160b0f241d806403c03da1040e408041c1d40503905110908041c5002c15080307502070301d02e180d204a010050800309140c20300c1a2815141d0f0f8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 728815728 1250 728814478 728814481
    0x30307210e071a070503070609020a12030f210e150108030a17040606030611070311060108070b1303050a260301030c05010f030e0303070e09011d060d0c08060f 70
    0x15849025055000c0300084030400031000d40d440700d99500c000d580300e80361100311840d641044251000d01954841074100041e01e41d03a06040c50844002c0c88020403ca1050384202c00202c3c00c0185500f1701400161306407a00103201c0102d12042c0c0f491680381c0c03205141340d25800d524841500250060340d81c400c1003c4014900016030041d200c991000507000000b07542d1090060104203907015100c004030342001e001c0c018242e11203041800143c091604045c00d45418665400115031000004140081c0259100001303820f0310784000392151000c3c0700b600001d40c4018000d11644410000900d101904a291000c1d42076807070790b6503820100745040a603115076603c01100c00c0000928403000c01d802a01d05020b00d1981140d43d0202d5003040c600515040002400a200a00b402503100f0b40000c0082c004586d00c0c0c1c60011402000300810000c110302405101d80001905441a2103010b90302100d400041d8113542c640c03041c000c00070100a400e840041c0d00410009440000303001c05406400340711a0500396 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 728816978 1250 728815728 728815757
    0xa200a0201051503120c03041512140f06060a030b031e1204030c060507030c0609081917010905060135150904060b04060f12050c030319050a03020408030307 69
    0x211070004020f800d08190341d1440c1e9640b41c4d808502039440c6010100c600c1e840b042e900030158510f0040c0d4002040b205190310440751029040210800070303a00050003480049800d40b5014000b90b82500e58826408080b0082544e070316040740035101800191400007030054914002a1a0900c4012200d08041000c090404810702c148846d001c481d00c060101882d0a10f15034841c0c4030200d16108000c1045004120300c01007500c207006510780d00340c0009041c40f140d00306040910043d0301c001160f803d109200d00b86903040303034014082d440e2000040805e4243c0c1340c1c40c047d59100a230000074801810442c241c281149910f070803010a0580e009420340c1032040250f0313407000c0801128050031403d0300c080b0042c0d100300c25a84403411958000d0340030300b000c1011803a060103d00134000640201c0ba502d032202c0c40200741d800010280b190064092022181102841010b1540701c3c4514003140703900300303100141c042c0030380d01038001006208a0381c60018601559440c0c402d0841d001915200005455401640e01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 728818228 1250 728816978 728816981
    0x131d061305070e091c210c03060602070e040f0507080d090f0f0315110f0c0604062016050319020a050d081006030504020406081c09140109030b0a200a0201 68
    0x5024161000d4545041c107011490b6100503849200c01011000c0029405c4940710701c5108000700084252810001407401108000c0d00140b034030703140041e1908074002442c40c40007904000300c400800d4005030b04c0e01d41b5100c00300c0010020809649034440d203d000142c0ca24100030462000000e0303a00c4d50842d50410241e00d030341c051107510030316000c0300038402440800d807190f4860081160060b000a2200c0500315441500d02903800602c404940100d00700210f0907020441034401c9e03200d094108066070201e00c6000ca56481c51150016284083c0301c41c080c811100402c280e0041e003d034080760705003a240c4c1d20000d00b138442c0010030783c0160849040d04040003001c1145296030b5115042080700c0e4681114660540b13a0f1512580c800c0585030000b1a0030364640c3c0d4041805044400c0980b0303d2031030010ba26410001c400074160002480030708000580300c805809a0340c40c4a4140c0d00e05032603500c0e40d290a000e1031009411525495644e440c0341c02d00c0c08003d03040c0034851400359103280d00e41010325070203170 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 728819478 1250 728818228 728818243
    0x42004031b09020a12240605130806010620101a1e01080a0b0f0402040602070e0a0902031c030b0307080c041a030601120f05030c160b09131d061305 65
    0x102228018801380c1109038106500c0007200760080b50009007000140444240c02800310000540c0503c0035a01003801e40d0302000070a0702c0c2c958240c99050141d41c1d50030311681c85009116801c00207100402480c480c0500340c0e0441070f50100d81003150700341902c0c03003c0c071004c4404040d01181000304031424400242008401c0308950749001e0001c105844000c00040c0c054840285000c200030380c1d400540040b950703048002250300300081c2c411034540d40c0b41c980280d603e61290103a0108072015900040f408000780c091649030307540c00b0b0007030210600306c400070507111207081100006041d02c41c050216540ca04110900061074a940100000780080091100711441800d40da40f02030880d8101c12143e441c0000d59504480480c4800c807a0014641401c0d8880e81241000900c140800a5400030420000a0742841c2801e074000030700135203695003041c111520904c40c525400107910300f07111210401580c802004c45c05102c541c581c580c0844088141006c8040b03171440c0801900049035800c2c40010400311 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 728820728 1250 728819478 728819489
    0x6011202010f0c0b160201060306020d0e0609192613140d02090f0c0c0604050147010504090c0c06050f07120c0507020901031202010e0c0d02042004031b 67
    0x50f41d400003192070760980c80343c009008021400000481e03080c0b0720320035030100f401143c10100841d111030608038003001401141c11130100e140708402c0801c3c0f80b601c0c0418541c2d9012003200d000c510164940c1d035500c1420007190801291100300402d02580038942c000101031400e5445100651503041044c02151800d44055041c019003241c00d000d00140c95518001303400610301e60305288503541350400c0c80c009200e560342500d030a00403042030004114054200645014840700c882c80b0380074642480d90509910480d9004550b4050002146001e904143c03182c41d010041c13406500c0d01d516400b941081e26080c440020014087d03078801014454180300361900b04d01c0c02250f685150500302d000610000e161081805019510448000c2d061b0040b000c590400354043c0c00d20901d517a50f401c141440b294a214403102550034406040022003000ca18191a200014504070b5a00f9041e003e00000302026000c00845a04444400010344d038a1000b0b04019446464008092114079400302e19140300d6a016 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 728821978 1250 728820728 728820737
    0x6150d0e0f030309030a210608060108070b03040213050702070306051501030b04060302010509130209100c050d0c05190501061e0602150f280c050c0d0908030307081806011202010f 79
    0x4d100c214100401160440c1ca00c0d03240011103046141521190342c1e00020b4100d04641c43c040e0009002c84010590304d040707523044000e441100b6520001c5410500c0f04070b400952060302298034a0f022f21056112541003400391040f60002e60f142d40d92401182c6094800c481e1001e0710341e40c80665980d06000ea05421401510700780203003031070340c0e00203481c82c00340080c0d4500c540c2e070f08a54a6920b00e400e60541d411014000c3c0b20241c001c40342d40000d001200445800e440c8c034054200441440340c0a2201c9007081c2d6880700040943c080d05840c0c0340f203900b4240c0341c2200c595489000002c0c0c4070346114a402010800300404050380c0c0c0c50140003030b281c01c248000060400039103d0410a841d250000e034a540084d2114120181048440c0040720360b0341070038485400c3c14a00b0032261122a0b101020b03044a91201323040340e504c2d103000c40043c0e80c031002911400300c2d42d620400000d040390f0310446006801482100e504020503800c0d8041c170342811000d1700045001a5604140c405660f40001c9500101e0383c2400d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 728823228 1250 728821978 728821981
    0x210609063306030209031f140606090a06140c060108070807080a080901080c0904050f06090a090503031303050c0d110111190e0307150c230a060506150d0e0f0303 71
    0x96540c00021244105018994003185003481ca03181072001c1f0152018600c100c0501001185000008100844a00c8402d291020002d1160704104044038440c0400034140000341d45041170458504141100ca1001c0000501006011210420a00c0c0c060f0171584040c0250600700188170b0300e4000710340c3c40801e00344d219191342c10100710340c04216071a0f0a020f103000040c0d99260343d00d00c002e903c81d441085411074502000c0001c070443c0209491300400c0121a04ca0594a4140288090360a001f101810381e4008001041c089861030300d01c0c0305c0712071003030030703c103041900d061030190074440324070100350120f004c181401140c588284a0207124108002081341030902e240101c0c41ea50003400618014015000810641a903041145c0001422a0011150484040b200040c40d0015002041703e4084401001240710312030502d84a450701c050000824004030140c484d45c018040140c1480c0c0c00c000c04d0b48640404100240050000840b5034a0124405448003c910318140b0b441c07246400d160000e10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 728824478 1250 728823228 728823311
    0x20a0f17060721110708030106080601082a070212031914270103110a0327021008280b0910030c0512100905070509070201021321060906 60
    0x200082d045030342d040000284940d1342c0200031028070503900c1c003810200c00800000b0b400359011030303054440c031001c0e40c80444c03d455010b26400840e00c003240280c2404580100c0d40000302c1600090184507000400381c05c6542807041205066500001ea40c40950505805102c0410b400170401c180e08140c000c81c00d07150154071400100072140401d081c034030030290a0603045240c2e2103500588240d0944001080c1c0c4d0b0207041d034000c0d00074170100040c039103044000f4241084190340702d41031a82c4143c01404860b216218000d0450b00d40ca0014074240c4211910201ea00d9082002264111030340488900040c0c1d0001c24420441a500700a002d248241c00c2c3c01c0781400018142e02021049031415038022074503840c40344495090844000a1480707003850544240d0900000088140440c4c00030f44107503000d501c07032441c120b00f42d03c541004890200c011a104000028060311001800381480c0101c240c855407d6031031405981d50104103450a0351110682000c00030060860103046e4107828000b5102c00c03210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 728825728 1250 728824478 728824517
    0x40b09100e0a03120509100807110106030b0a090503040f030507060e060a2c12030a0f050309030a0c0201030605131b0c0f1202012304030201050a0e030d09020a0f170607 74
    0x40c000113108811100b048500c0340e00a42c00c0c1c6d07405120090011040c0d048810004109a40854440300003594070004460f80144c180b0420050301d401450054450752541140005404070007003ca44910003080700080240b038075481200950700c508054098649800c0c002407a2602e00440c20748141070030040c184405421890000e0009042c45200041d010340e450003c880348002190541c000301c40e640110524000800101000030140e220040020207825080380d4031300003140d00c40304a41c01000201c95050003440842410740c41450301107003ea07240c1000c1341d42440c00540d403941d040e456a08014a500710b10540101c2002c0610706100d400184d902c0e20070421f4024a000f4011003040305001c03014502c00e402010b00080c00d00580c0c0703000609034800056036201250190019403a1202186624080c3d010360b000b6507444000071410042c1c0ba003103150003803000c0201280e101074004000141c6090080041c0000c0408810035500300901d0402c030360800740c00502240030403400c1c1f040e015160144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 728826978 1250 728825728 728825749
    0xa1d04060b0a180209190e070c021906051b0c0f060f0f07140606180a0e01060f060504180c1e03180c0501030e060108030f0a0e06040b09100e 62
    0x8000466001d00c11000304111001075004000f100b0f030715240780c0d100360086400030301c000c0900b41d52001a4954a1401c400c0300c0b14603004c0c40702e4614040703000c6680940b050094210681c0000c001c084150103000542d55040b140c1c0e40701101082e000309102d01e0002201c40781c20b907074408940c0600f0746102904000780c840c40c0c003035192601c035080100741cac81c0c0700102e00401e50b2004c0100110140cac0da403106043c610584101d403007142c401840345200141841c00c1c8040d80c42c6515200103102c00300e07500c0d401001c1c0050000b44c140050590b41c1ca02c00040c0011005c81c0c0d6100903d81034031255502d80c141881009c4400900682e02001e0341032000d0b0072031259000c0403a00005400c2c00302211000c100c0e172000c9014044510312171140c00c41000c210300c1480007035103200c3d04a0302d090306c041260440c12144992194424400e04500e50400d202c600032002d1a84010a0585001d2a101c0343c45030071100040c060340c0054001604da05400b040144160802c0e10f6060900c814038204001e080d9160000160506ca5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 728828228 1250 728826978 728826983
    0x71701061d0406080c1e01140a0e21010606020303090309040b01141210080109050a0201033605011d07120f061e0b04090c05041d0a110a1d04 62
    0x801d81454048030654096030150380718020414001e07540d4804a00f50b0700c1040b41c0300d640c822140d0000c01a6005400c07452040c01c20700603194902422407a4100a600b0740000d800c107024495806400c0f075056440310084d0710101480c110f010802507415a2041c00c40d11590048002e56004000340a81c1e41d900009951a0030412540440c00084a01c0121105464032941c5500c0715004a046507104105415143c407030019480f0880300c1980d030701031a038262448900f015000750414440c59015502c60b820508411a0038018080146801d01a60031a031192010040300301d0750508540382003000a01031800c580124101c01d00c07075050804640741c0c0b1140c0622510a148408400341420042090001c0440759001a41000705040c20f039649859a21901c220300219458104105418945845512807858100e58501a032a003840709000040280c14000000481c1070001410903e0f030802030074a8091080069000c1c0210420078400f17001e917250003401c0714a41010f464038150b0001241d0a50203034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 728829478 1250 728828228 728828237
    0x220201020a11030127030f0e0f0f190b09101403130501140903072117040c03080c031206030705151c0606020f06010e1e0c0d09060b030607170106 64
    0x1002c040082d0060484011042e0040d443c003003004001494a81c9405101d8080e464020200e411000d049660000000d01a944160308030320121881c01c1192004080c000040c056801100014070110501802e60740621010600042c100a0908100c104007801e1652802c0c40101684400b2074161180001008480f81160f101c10034024010250030003075030b8286000741c00c242e078201b0b06100c0d501c2e948440f030107445e249041c0207840a01100e107550324003101c08035500c1412183d103e042c06403d42a000c0c2040d034039200015008070200382c03c000141002c0120302c00560350b030741080b00a00e48055004100500c2a00002e20801c065264510300207001c5a40c984200d81d1102c0445403188868050805601031914186000c5091600003c110540c2605032013200d120380c4c3d1394100220104401c07200d040100c1c030441505451128000d0f110750b00261640178960410050000d610201c0c2c0550400380c07451515a0b40c00700050070240700280c0c0004140c0381c0130910949107642000380003c103104410400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 728830728 1250 728829478 728829503
    0x30f0703090f0803011d010602061626010305190b0705070609241d0c09061c0c1404180b180609100501060c05070302010e01050906030f220201020a 65
    0x2520950201c0403099108203001504151414400c810740c0013406550000c2095184022180c40a004c1c428121000c0350b008201c3d6981740c1c0b04000d00141220014070070710220110f038914442c8014400000104449508400ca44c03560500c1031410440000c950150741e0703002c4000011813111584181e00140c1410400e0f03446410386010310080000359405000841c82010700340c0c0300002d00c41c0c3d00000d0704407558140b20010030b0b00824815000780310f0604089a10421401e551410501107441d404840200311000a4007559408552030f00c0622048070341c901425020b10030498020800c003140e0000365810040b2061544008403030500308403018002042c01c60024070790660070060808008100800c0d9042401c0c501d040300e540d14080c446149509003030000216440b841001c080000a8201000f8013120303103189c0042d1206ca146420090410808005540c1203461360002540162540c89000c9001c9c40c0071009044280624495114582080b100c0000540c1c0e0014008210a410540840380c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 728831978 1250 728830728 728830741
    0x6031003061d0114060f1206010312030216030c0b0c12041727040605010509010f05030a090204060b0306030c011d01120b0307030515010b0a140919180f11030f 70
    0x420389504a0300b0842d0b00b44142034850000401241c1d0003101c06461465044141c1010882480160500000c040c0c1c060401040490a881010041c2407100e060061410034501148949500000001e5010850300d017106000c0082c40380e4403a0f400f00c0856000f03810400100c0500e90246c401410242400e01c40d044d845141d0300c1d07254200d0714284032141d4004d40b00300c43d400c3c46c000300c0c070001098584207900d443d50002d829405207085440300c860587d5140031100d41c1203402d56554001030031100360b25513141c00810041e1117601c0b90300003600100d2074071516450030038209890803502065103810006440c01d020010481881100e144000900b08800c0f14000800e082c1d00401c40f910544d41c0c140f00741480041402400301e21a840a0301a000e080501d1303032580080075492007002d83d54000540b440c100d01d015000070b00d02030000010001c02403038140400e043c0f81501c9030310682010348091040c2401e4500c600040c4503007280070302c0c0c18005000501d4080c0c0420503900000744566600000b05002554 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 728833228 1250 728831978 728832011
    0x71a041a130e01090b180f0c0d060503030a0c0b070903030e100512040f03110f0c21010614100c0209040209060105040305030706090303050703150b0c24150603100306 73
    0x1a00e403150741003520b9a512a03404c00580b498800c25400345c500001c40f01c800f825041c5801d13219141d00070000d0810303240d0106040751a4009100c21818503542c0c03134040746541c0c05100400305c00c82a5601c0042c03903101401e208203001400351080d024020b90081c20030005c4d070455980150703078504984410740c03400b084000b03441d01d12403081101030b4108182c0801003009070b0f44050a40c2c0501960b00c0350300039504403007010b40d41c038035882d11421181d006d00044d6405140c4501d0300150012060304504d21107407035001c1c0a0075076019402c48130a0b24100c4480b41880d0405030b011003040c02841c039020804e83e482d500071540c40c920281000c2e025152031400645540d00444c1106c00a5034131504890365a0407a04141c1c0040c007262500b00c00203400c0c030010890182c464083c05c1c0f202c0f40b041004201c07080c60101415030541c03051201241a00490b171055a2507070401d24141e01a054900181d8054640036850989070040412160720800d07080c800d2041c1d100b54245883c09880e40800001101d9120010700030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 728834478 1250 728833228 728833267
    0x7020a05010807080105151605010e06060607080304080a0e10020a03081303051222050f0606090903030601232205010306080312060d0618021e01020a0f0f0b0108071a041a 75
    0x1d0303230000c058203034108100055110076038031580d10741926119201c840070000c0c00e202d00d11001d816000c050012070b002c0742000300204001202c13424403641214000340481c401c45000d40b203060140c1c1048040b0000e0542002a26501030304411421013100799507a00a4a98002c9410741b40540d000030700003480c03400c142e1004000b0741030203e2103048415907614140f80d59800400b002c103400e002d241d010070418288001010301401a51010b941180e484000445d2014220f20041c441c0c0020808120340141c0e0900080488a4040b18031f000c1036410781000b0100007545600c058105858214208034401c000700544034100e01c0035681075903a4039487d00103280ca94078944060802440c003944925207070341003050904954070a84815502d0403200112203440c038030a84026002d604450312003070015046030b805c0007030a8030070462503d4200140d214103108120136004080c0b141e11000341131001e40848079002c5800c00c0881c032050303d0300f801d04e0b6a8414050a01280040391003002c1015151000a00c0128 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 728835728 1250 728834478 728834497
    0x20a05030304080703060e0c0a290f090102010e0307020603061215180d0e2b08030702010617061e04050a060528020403110f150f07020a0501080708010515 68
    0x142c0d140d94851040a48945051104544c01481d00049480c115808284524a00d0700200009007080c6444110341041c103001d110745074441c505000070104d050720840a801c4c204071070358480391100c180c2000642158154559201140d009201c0b090060340d0b80c0382101d604c480196078400000d87c2d2452094602500200201e403032051000402c180c141c0c0c12110300031058000700403100b100d40c2076641a0b072101d0000c9901900300b80f0400030016254902246000181042c1c0c0000300500026210502103030420784074100180d4680404000d0b0b00155441c04600550b80130241400c0e041100c0b0108030031503840c41c1c602c440b15140700001e0a0041c1480f00180b403640065003480546003415400c000b201c0d44a52140c0c01c4201024443c41082d054420744058a07401407040051a8411040180c841d000c090402d40c40030420001840c2007034910041c02000c0948090940c4444036407042058000303042c3c00290411020004001c01568014001411144242c3e0342810380060501510f080c0e00c1119000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 728836978 1250 728835728 728835733
    0xa240f17070b221e0608060d06020f030109050c040f03120e18070f020312060d0821060a0b0304050312040302030c010c020a050f01020901200106091e110f16020a0503 73
    0x100802c500e07140c40c441011501140c081c281c0a88500c0520007601d0002d5034030104c441c415000707110315400b841c10590041401007103080c08030401e039903c0303007070340e1020f0480848041c001c070040044200500aa0b9000b84c818900c0500341030403c1101050808540b10160440c4400204d4605071401801e00c04280d080c041c1c01031814240c03040484800074010343c0c041c4005000d881501d00707950320100540d401e4400c00204001c09440d004200400400c031300405451207402001007040440c4051206014100c801018a4061500d20f04110503104a5404030310061020020040021002b20480b11130011880f8501d04540780d504040345540101468041c0c4c6621b8043c803c590f541d00013071581101c0c1c1c4544100c0d2091120710782024240d004070303142079020407403486400e424802c1426070f508141407200d0001550941c0c804801c425a9440020507040a030b65180e116441d4801e8029081c0e400030504082c0c0c0361004155200b5240c0c80754008440300c1c440c035413003507200319520024500300601e0010304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 728838228 1250 728836978 728836987
    0x4080d0612140f0a0b04050c090f1f140d030e031009020906040c201c0f02100506090a02090a05060705030a020d0c03230c01050a240f17070b 62
    0x1001c0e410148014000e540b2a21a44248089104001200320034000084007400004401c0e13904c810143c040a00101d40c940070f0480c045019440f540b003102c1c820307541c901295025041c000740c000e00e00300c0f0502484007025245d2a0500a00e00d0089002c13220207401c1c0c4040e40103900c44d007004c441c1d800c21941078a41c10701880c00c940032a0001900b004079018000c55561a00c2d8030390000b0071080b280101010310114000203800c0540d81c000101340310f039104810b015200703400090200000300030a001c81d0740001c0b0b5600c81c0d008445a5040110304154201400d0030429800d1100014490110003031969405e42d80000f00d8044d00d0b10b50040e0325008041c00780101d91516410302e00107845c3d4100f4041c0300018803a12095900561041425400e100e03096142c084c803940e03c0b1071140f50031660200805c5001a000c11001c030304023009111b200d128004520002481c6039007804079a1420392401002034000390085000d04c851000714110008440d000008000b640001c00c20903030514031540c0c4226054030000ca03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 728839478 1250 728838228 728838239
    0x70c0b03010501030c0905030c011b060e06040c050d11121e030304030e06070c09020f04150c0201031505060412021512010f092d270b01062604080d06 66
    0x10318141d4a007601d0a1080914000b02150f02105074460075626503c40c0c444c0003140e50023856450030601070402c401242800720380b20241625086481070341c990388418104002c1c040030300312020185c4401c994507590030704151188000d0310b00454056104a0701c03030080c2d004010f805c000090071400c0014050007903808941c001912074000325015004200c0b40c01a00700246040b504580100382d2001041484904045201c8003e400c012410b0715001c134208004100c81c140e294110742400096600d1000c040b0701c07480014143d5410038002e0303206a072040340031b00459880800303130380581d00000b40b029040030990000134420680c2c610f00000c2c140f00062213041400152078100d050700c410400110800e41d4400050301117a41c05000b0321144126013101b047c507401000118420315044880c04514440d00312590709104103c0301c00d101100145140d40d03020080b1017a61140146580c0c01c010110407003041c2900e40c94800b490591405100302c0001404011007101034880300103030703024200019078442 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 728840728 1250 728839478 728839499
    0xc2a03080909160203070f0c05040e060a0b1f08130606150201060e0c0304080714010507020c040b0f01141b01020f07060e0c150d0f05072304060f080606070c 69
    0x1c0800038068070202c40015080b048004002015100650080d803600c120754a9061183c030242008072880c2c004035000141964440c01003510012103100680014100b05110504440c02d580035103009140002e4091007580048035a1215900c081c100b0b41d445550b50040b41180c078030141001001135140030804111819000200d0403a100b2a030020031000c1d40301c0b0380e2414007040c122345101c5620000c00000b0000b881c230750042d005484c840c00000f410040314009072400d40310700710707105401a4450303c900b00461400d4041c042c40500305a0352142c00c036910383d000031300a5020010100001500240d03120420704034035030f038002c0442c9460085455512034810081194000e40d02501d1840c140140131a0341c2c100402c0320134104c0401486c000c2c904551130342e010000e810955022607516510720004011b11210301400d8410360b0242c1c0c802150741d0841032440f03002086892200982c520511060000d150000b1458000325418104035a0641d202c000040461246150043c1052300700c8200162140c2c0c078 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 728841978 1250 728840728 728840737
    0xc0402130302030f1b060901110105040302010b04110313080a110a030f08091b1002010609060902070b01170a02061b0d032a120b0f1e040612030c2a0308 67
    0x300d003540c41d500d040e02d44582d51101c000711001c0c5103945a1105c00e440f45821001442c200d032060400a42600c502808a42140e804580c1070700541d45401c0004c1140c42c052048400f96410500030301d045040c18850342801c0001c52000400104000039501e0100e40148603070540381c2000340480d001c8800c1c42c0b8006002c00c40c86044400810b44070f00110b000450b000c101c5ca441040010b09840c040007240c020028401014903201081d556a10000329002d15207006e210003805001901594524980ca040d00200c0d60590107000c5001104140702e09200010583c0d4810352740454240f0b441c4e044401213145402c401d131000800610400b24031000860309a04517603030013540d51140103a60f085011207040003038202141d040c00221004e0340401c4802e1550300000314a04040c0c20465254851000701e602d4480c1414a007a07000b2442c911082030b4038103030046a000c2c0c4072030012590301002d5540e000e07106d0201004000c1c0300003200000075500d4440001c0c4030004010310301d02d001c100c81d9241401c002c250711 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 728843228 1250 728841978 728841983
    0x90507090f2018010813020d0c1d10050604181109120f07050109061205090c121f02040308030a020304050f060c0a081e071409061207021504021507050c04021303 71
    0xc14100c0f074480d07004059461017031038800c118480c03450665003042803c4c003c00c20b080350001d071201d0010409031400c01285041d500b113003611002c1343c10b1040442c0381d1a582684a544074500030070040c00380025140d0f08905108915401003012035099000a1480c01541229034010b80f172454003102c80c26001030f11305881d80c00c0c04140c40e0300f03a4654004444c540b84a0158802080002c4800e62511101c0d500031907000d0744400c20b8980420540000030b0907415103919039881a07005205040003142c84560101c224004900304501e0207103141d0301d001b0346001c01080ea00c840b6034007100007800c1c07100a0006040720364402058443c6450300c1000c0c0009a000902e00d8400208a0030008862200803141d0a54207010700c0f05040a95444240803284000c010002455041040c084e4680d6500d41201070800050000020000c5240c0008002e1408881e0083d41c008103a000c8140805616007003414a84003084550403540c3d01c40174100280390008102e840382d0080c0c13000800e0070424548428601c01d982c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 728844478 1250 728843228 728843257
    0x907211803090e0a0b01020718060305011404021315121a0406150f08060a23040503030a110a0e01081506030906040c1a09040504141e0c0103090507090f20 68
    0x4c543c0b10303601040b2180031007064050b90258405024490a0402d203066880310104089400c030703181d9541071f003035840c0100c501440c160240284030451428614001100701c0c1c00004010301441e454041140c07010134410070b80020081c043c2c260510041000010912101046d12045400c080c9807000040a0035402c0e02000307000288080f842906c400704800440c1e81d1100145016111748040000800c410012218000c0c2c0e80246007070b4680004807000c1c480c3c2d006e000a140c41e4503003110501d055504902500034014010020400040d410409a8034410b89c280b904080a03a41e1109403140e052003c65040e50011010040159a500028103240300b94414540512080e944550034100c45501c072504a04071182030083c8645410a588210b038028040c034100709100d401a42c94a08194101a001d1403145100d81003c50511081000511451080c6810418003801d80c0b2000d49030103803405084030060700c401030b868084503240c104081075014640c03240d00c00c028280314494658009400c129410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 728845728 1250 728844478 728844481
    0xc120c210c0f071401020d0207032a170c09060303071401020f1b010608060103170a03090605040302033103141e0706021005010b030f040f1e030206060907211803090e 73
    0x1544007007151f003200c035060f0b00280a810304564490b4140440d605c440726210340400320703201080c040e06036044010014104460103a0301c41100681c101300411500600a2100800f444078580f40007048604140d00f1503000240840014009400391083d1150622640303004600c081c603045000d20184040310664008000160b41c8000c01611ba280c244005440d000c4088542c9141801c0d09000b41076640d1289030001d0426800d942d8031085880550702600140d0002c20f00d540840c018200c40741c1610385114180e0b1418804042c0c1d802142d180e804010050f1a550380100e203050410402030350341a01d8440c0d2482d030b40b40781d80d007855520f41c280c0c41030030010b02c0742c81070741c040910305403240314140e5070400c1c0124615542c114191007100000782080f186070281e2281c3c20081610300946c54007460714079040a08218540c10700900e440c10160005126170300081c2171090594001a240710901c0c1501c4401c51000880b8140000410b841d0b00601c43c07042d003464030381081542c0031783c00f00b05848903082040d406 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 728846978 1250 728845728 728845769
    0x606030506151e01091a0c03071104150315090609021f140a02070501030c0e2107050301051003170c0607020105012102031f020412080c120c210c0f07 66
    0xc1001c0007080c0780c00b0504605c4180204424045c29030406100b1072840c80c607100709410113500c2c41d403040700291821500b50f03503d90240c1c5401c0c0514180c203040e1403524078190f801c44d1124144404207039001913540340c1e00c0038020108261600910065900201a4441706002154820700088480030400025600c03500d04400341d0150015940b01403d154000c000140c00d1400550052a98180c40401c3c00000c1c0b4840d082c0e40d40b824001345011400c0f920800100e645801c29034540061a000b030381c0b099040ca801c0000d8036500e601108100e90f00301c21204c0618003404481da03081e201d405116a0390340540d00070041c490340c054001d141240d01041c9200f81154540c02000065003180c00002c0d4940c1101c01e99414501c40d9a461010080a104005150540e030308500b090101220030200c854490114541c2e50320001071141601404402038010b24145813141e0f907070b4481516581c3d109584162104901c40c100e40707a400d40d50745008000032280c2044244c1d0750103507202132a01c284c840390020040920706 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 728848228 1250 728846978 728847019
    0x170c030610030308190203270706081b040b0a03050103020a050f0d11011202121f03050304030303020c150a140135150103080318060c030a09060603050615 68
    0x2203500940004070195045640845411102400403051403105050000c1400090710041d030107101258041560403100b0790905500400c5801c43c0f4a440c1c0051800304035464201c0c45035540201c204488414150600710406034901503600800d03071602c004103010300c6041c1c0540c4100c0c141c9008443c1074116503514000c110142d40c0c00c0c1c0d92190011440001240080c41c4004030030f100301d1050501442d9024880070b0343d022a00040040d01d54039400409005440098130500690441c10705481c440c01800c61721210764070f02c45d43c80300808140c3e00083c96425194203000100d400c210710040c246050410484103409170211030140b00e220860703980005064405100034080c01265040070b503840c4c2101d0800c808944d1a10714051003103001da0f140501202d002800424061489004050340728200940000080342d111540c103803080e0300940900000c2104242030729032219414070049a01c140e24644800030b02290381c4024031340d110306c20030b000940504180200d0520400c0d42c01ca040202401700740d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 728849478 1250 728848228 728848231
    0xe1f09142e020c062205061e0a02070e100503011d1b01020c0402070317070c020d02040b06160506070e040513080a0c081911010c020c09190501170c0306 67
    0x2040c854803000000e511404030891010794100d0040c2e40e075610940d004205103900084101030081d0780440b0020b018089045844d0150200b03448490420f2100c1300400403103c2c1d19090726003405404244815014400c024900103010000356082e801d08088101000d01405030040501c04d500700855210b00b04041c3e54000700801c07520008019030410700c032100c082242c1c5440003d0450240c4110424141c540f80014010700f0711a90301ea049680c61428070380280d1001400b4502000803000068000d0307610010703c00110354048a00041c1c07200c2c1400050711620602c11090500f40f508128072045c000d0110784144038030403035110101d029000b0410030045074021546124180d0002d42c20102103103698010705041c00306400c0400501301315864442c26504203510300381d59158402d0341040c071654010329800b8000b50410003480b0003041004084d46903001c48503418000c1c41c0d440300007040940030406112a0036442482080196150030b6000d080040703103601c491003813003000031a00c25410001703410b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 728850728 1250 728849478 728849509
    0x9011203090905310c0b0406020d030c0e0d03020606030606040e150615040e01031203060b0a0f030b060a020a0b0603030301030b130204022106090906090d0e1f0914 72
    0x391100d09045044006120140513010740e08050070381c07124500028203440e01030540f01c43c15402140642e24002d1a04040ca03000b6200401040c0404c10501c2d40004111700c045540c0d05010507901e40c22802203812082c080001e40e44809001059414150007180e114001d480503030507a966a96403c0a10040c1c44280b05042c406034014020002981003412840790802c030010070b0308141420b80e81003034241c0d030800c0d000a4100301d02800100b04015100710034005040e102d0509224061901010091501554147e1014080c120b060002e082d1b2081c0d000004418000b40425211032032030038001c0d0b0301c0c245880c0881e0400d809402150302d6184c0001501c0c100c03603008a0900715603966000280d601000c0b42d1049030420f80a01550ba490903211190020055142c013611156181c900c041090007000500b03c0d901c02c0d0414418841400b0300411000c11280140c00e050701c4101c41a000f00d0200b80d0502269a0b04854803043c55a0196014151100702c50b000b0880781e4081d0b4500c020080c1c252000940c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 728851978 1250 728850728 728850737
    0x60a020c0f0f0405090f010c0f170411060406051210030c0302060d141302090a14061504082b0e01080402040b03010f0c020c0127060c05070801021809011203 69
    0x10466103011040c140c101e0038064266418900e01801050640d401030358054000d40149169100540c405d200e284800d0750316280c211070788001000c000d0706540b100344940142854850000e024812400d200f42040341019100076950307556044003e1007a0070031219100c0000580c0e001c00c4450000115000a0701e402072a5180228610f600f00030199003e81812011940c55850780e10201d210080c1840c401d241143e0011051159403040020400008000b8044c0714502600030241c903140504103980180103440314a0010758030340503208a400340d54815502403243e07546507500101c00410041c2c1d00803040c021110340e420a48030581d40d240070240300c83d00258041c0000703400342c072b0076030040215418041c00005100710002103401c01d40d4080800c95015901140c0741c242c4a50740041d10480e0446090034100d000d0300070b034800c03650301100c078801c00040007034142c4510207219081c03007824001c0048000865541c2071001540c2c0280e000c0e4030b4054414000040000b03030b0441403840c000805a499500e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 728853228 1250 728851978 728851993
    0x60f01060516051f060e0f0c0c01180c03030212030f0604150e040c030b01080115090203060105040510091a0309190501020904060303030e01050c0702210a0210110c060a02 75
    0x884454101c1c040c0b414004190780c4a4001151003404080c114a403150b0642c0c80b040c02800344007064034450f90100b0701070501002046268102180c00942000c0c880f40101da44070394152919024140ba21b075a2007590b81d44004060404c180d038030309030046034401d40940c1c42c4181d0484403001c0c18002140c080d80704050300e0f8000356083c6040e500610390240507951100b00e00342c40b00704801929400301c80c11200303481d10281c240207000c15001c0b454010131240000748911403802a00354038090591044441c40d0390044040f440983c000c2d02503c004d00340c042c1c40760070100c021540060815240d0300c50788807001c02185d20048038038011001c0f80c1c07140c1c01c1c03c4010100c11580202040b50807480c504156030310b560070300c0440d901303940368040d100045029507030103e502e5043c004001c0c04c4600c003074158500c2d01c60401c40c0d2001038403072010001c0031408281c8036040d03480d100c01036281404034160009600c41c054140c0006000d80051201c01ca104000048624200d1608280a018400c0c1154000944c0c0f0468 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 728854478 1250 728853228 728853239
    0x3031905060105390105100b2b0924390320070303060b031b0c16030b0a0c0906050f0c01060803030a09051504030e09070309120503090d02060f01 64
    0x4442255035424100a650303500c490070351628441c480494010b01d94485080c80081c403030141c803800140c00a90101e0b071603c45c00307030380c00050702e0107204620849103d0a014442201501d41c004285190048040c0080d400c4070303200c80381c080300d40b6041201e105280402c0c180c200e140c0cc1003900c407081240c19840c2e0030108160a0840c0380403100755024205900e0320401c005d81c0700341c8010300581d00040488540c03035480502d0041d043d2040e64001c19071000040c402c01c21000034685042900010706042d981c1e444401c18012030404ca0350f01d0bc1e0f203c4100b540c1c04000f041049054006210b058654410026a05460b000700e400d00071520842c00021302c280300102e503020360480202100401d44000042896960556900b15002150b60141c05603450100c0e0080c804280040c01800d030341c0c40034a90907450f043c2da018040b880904500c0b4010b03009180040d0040d4002c0d446161704540142445a0030190040010810b8ac0304440e8801c540c018002d4480a243c0000ba085000d8a101000c01d86583c2c2000e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 728855728 1250 728854478 728854507
    0x30408040b07111003060602100510094d0702010905060c15011d071403190609050406240308120604090c0611120901020c010305040314040803031905060105 69
    0xc6100303a500801a070400c9445513148080150340680c41c0d100860300502c1d220b8007a0030f0144084100146a00703050410515003280d840ea101603a00d032190020b80c003208021f501d402d4401c1c401a11006101d170031101e40002c4410b41840388038442c40c4050301d8180c590280400500e02400b20002c1c041007444905000364900103025007800440c9604680501e000c80f800342950345020390021070049001d1621062b80400d02c0340032640410542840464910107035403200d0740b84170042a4000301102040c85404040150300540001d09581006008606050038220020406003032144e13003581c0880401d10b4800182c199a0048940214610f41000007007010107660b0301004240c40e07841a500d5480384001380e00c1d00e51350360182085030349203680302c010009100d1078080c0130700310f403d2010300a000012090fa400215900610402e02c0c0200d21521145000d803443c408000e003203203107008085804207001b0b000101440c8180250f48421264017848888401150750960b216400100c04011000649908 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 728856978 1250 728855728 728855737
    0x60b16061e0f06050411041a090109030803010b090a050a0617090c060424030513020d060b09150102070e0103030507171c020315030d0f14090604090902090c030408040b 74
    0x540740c10110804004003903808460104815008503680c40006000505183c0300f09018451541e00f0036103000d007441200300c100240b20251070051080040e00031040e910840c6a04019540080e00d5900c3e542c55800f501c4554124841003801200d2402c030006e110f140004024081783c5003921428905854901051000b1400501c140800d1069148051817501c9500c003c1000f480c075018000300851200c8a031410161b00403a80804150801003806152030a0002d0401d40582c119100c011410042c6450400391418042d0350703601c0041001003101c0f088290447c582c00300c2c400d82c242d4960302c0e03c500c10300c0c00c07000c3d0a0002900040052141100041b4485070300c506004855aa9a0500310102c00b501040040318070501c03603494021051104d50030a0041c40a036000c0c08401901c0c099000c00e20040108000740040401c01003016040c00d402c0b0110400c40d42003000c041c040310fa81d01d80300c60301840034000002007240121000d230f0003d00005c14100c107480c007995125121030700d4546404a0304c400c9810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 728858228 1250 728856978 728857001
    0x1014040914060703020406180e06060d0f061401090902030c0906091c0609170c0d050a0306030503040e07080907060203070b040c09090f0b090a02130903050f03010e0901060b1606 78
    0x1000a030142014400b0000316200d02e109a41c0541d07241c2c140741340200050014984d20540d040c3e620414003201d1111031000f540280d085c3d588640b28040d404001c0040d01400145984e020302c0c100e00820000c285451000c548070081e00ca0070252965020003c04a101c201c0704003004c0c800500c102417040c07401600034004210b0007800550b035a98850345000d0081c00c05942154900d40c0c0f035004004000c000d46d203000c205801c0000b81d81c2018004020103403100c40442c45001008800030395800d12038045e0784840041c50f0400212601c075a150000000c1000091351503401003201d00c00001c070200400200d100c00d441d203541c05903060042035503c010310410081c00844648d40f41000200c0d1a03415840348480b142d0041d168403040003000e082c110142c0340b014103c101a80c1180034050003503204c3c18bd6562828485840024210f82141011a01d500030040074540e00c040000002801c0d802c80c070b0059000d012000e008000f00c50b6a43d401c0002840751528481c003160054a00f04042101a40041b10219 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 728859478 1250 728858228 728858243
    0x50d050a21090503120433150f0b03040507050306070933020a0b0718140604120f060b010509100e04090501230604200c0c0303030708010e10140409 65
    0x2d05550b407603041d9000341c0464104103400b4020041449403100d2000c0030754840d081c032040c85180d806000d0351450180701e04015220346070450680c070000040320440041400d4007210030040d449042c41e40c0130b0390064606032610311036075101150500c0d01051450150081c0c2c0c071940c1000b03281001c0c0c0402c4401030f8001144169001c170030740900d01c400c078451542110b6254054001c0720614900329480d903030007502c0c440400581c940c0c454002104281014180e8080b81c895003034901c80803000031918800c58110b41d4010740003003003900402a503405020b00b85132041c0800c0c05141303901401122035015001b0042d502c84058003250131501d0041303905043c40b403005000407500b00301139145c003030943e288a65100020013a152140d0102100e03122890303003143c411a801d10103d520000f10740003848110104581d050000108801492401c2141407034825010302543d4403454860070240804009124203800b6000d190b0004500000c007900e040150343c04900e00d07056420801091000900402000302c6940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 728860728 1250 728859478 728859491
    0x2040e070c060e010501062c030316020a030215030f01080319030207030e300106080304030b0606130806013012020f01021c1107080403020108041a040609050d050a21 73
    0x43d08203004650280c4060b444038444101e242c03040d64100b41c65040340707000d10f030703800700440c4041d07980070040358005e1800c04070f0b0700496600c500000c1c98164055200940c46a408081040c1c00300070400a184104040002040183e030307038840c032544038807800b00b06800c11220035804008107400380c0d01900003a40a40350494884840074049003c01488800c410800240da01d1a0303845003040c45210418000408002d109031442c1ca0145940c074040d602004240240b400d000500b191550070070f40d18540d13070305481d280300300e0340d1101c80301d407034032800e0081886120203078910114603c82050083c01d00c071400d002c1610000003a0325030000110b0201c80200031405170780b46a92000c2000d001510000c1c0b800f84400701d02501040c070080c2140c0b90f542d01288107580901c0f580010501000c1560101c0760203007000a081c1d581c62500103600e480031880303002d0701ca05140504c0280030003540254055841041210035a0200c035100303440318054041054000b0314405103988404809103880c44c2d42202141012514 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 728861978 1250 728860728 728860751
    0xc0305030c04030b0a0515190b0c0f030d060806013302010e01090302100e06190209040609090302061b0f0f0f070c380307050a020a021306030b01050402040e070c06 72
    0x138041c29102c5000c4103440b40c052281c03c600c0c40c000640c1d444801c075038103041070400d14411200000c0d81d01c038408060b10082021800180140030220000c0411b1043d40d0f610030f84041180010000c0d402061250f200d4040046016044c0211200198030391091020003a224440128000010311120004554803546005000c9109005440c502403080c4c001d04008a00c04c040c0c84129030b80c0c0c0344841450f43c0b004060101040e400b5203403058030b038403a04025a841c0c800002003405800e456004201c46072038000302605042d40410300d1340c0101d500c0300440c504902d44c804813104502862500d82105001009600181200765008000744a14581818100710a82d286c410350685a64000840310b04440e8080d080a800c079400c01d0241c4686200f00700030200d40403403482c62400020300700c00c14000001590301216000f00121100103500800035404004412a428003900070761000702d9500070944004039182c500b038001d0703401f51111964010641d590b80213041321440d10910040d60318030303075940c0714998 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 728863228 1250 728861978 728861993
    0xe010b011b110901090f0b060a170421030608060a061a0d090c0b1e0c030405010305090a140d030c030603110d170711010e030f1c110f0604020a050109060c0305030c0403 74
    0x70000d0340e80006e0640c1c61600e060f002d4030a9a0526485010b007085846803054224441c1c40c41d1604460b89240c2e0340c0e50300c0c45d00580b01031036104a0186500c1c0c182d80c603d1144c1e0301d0780040c400e0b01e80359016142984c40b413840c00b40c00e0350040c4c0038020009041c042e04d0005c4041400c090100c2c0520000c02103112500d54481c1280e001da682c0022482e090001481c001400e5100d0540610b46410701d440b6207010808a015900e030b0007540034a90400d0b0302c5401040c6280420400b100549820564010b4106d02c1010381e42d540d01040400c2d100032900b0034461004082c064826002206e40002e083c00d9a021050700b000088001c41c801110100340394074140800c440380c07801a0025500c2111180101035440b8005131001450003070341c903c290710070f540041c0d05103004100b1040c0070038000c20908081148202c01c1c3c854032512403944920344142040c000392801d0000f00307103014074000e650821140c0c3e1203000449110040d4000c4102094505140000091180000390f41c0800e080c10072034140360b100c0d500d408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 728864478 1250 728863228 728863231
    0x1e1e020408100608030304030c110f220c05070c09110408150919111014070f020f011818110406080403080c090102120c070f17010e010b011b1109 64
    0x1020790101c9060342440e0618840c40f400390440b04001c500b1850a5600204101c03102c0900030215014404c800081d921910100281d114004040c4001501c0b242040c508000d02e80c5aa184a0390030048030110380c40c0100c00b01ca110a82046100ca055410300e01140080d206102800060b02c2c8200030028000e2800c0c400c079017030805900f2010481c0d050400d403603072520044110440e0091083d12007a400100311100503841243c0c1500daa400b1084620b400f6102054a02494140100700103018002c1105542d800310780030744212030220200e2401b000444440c0000e5003a101c20150310703001445a015041c090001d10741e1034410120b204003080310500c1d60758002d80c0c00000860420340c188030801d9004000c25130b100740904602410301e202000000e40e100c032002c0010071080e400080500600c081807044001a042400450314216940d030710094011100701d401440e00d518200c03500e00260300600960424520580d0350f912008000d02800211310240241101e000b2000b0131284e84946420361040d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 728865728 1250 728864478 728864489
    0xc03010f05010207050a06080714041217131211060a0801081b010207052812050f060906013b091209090127021207030f1e1e0204 57
    0x544951400c00e400d4160800e6400c40760540d001300c0f0050006407a07580d203440071107040789802d00c03071511031a100780c61702da0408031148503880f0005400300305404040c8c0211440c0344520520584a0204c80562442e401407880651724407034012410025690008800c0e50258012107a20846855031000141301d40d12440202c0c020408000041082d00c5090220009800c41c50750400700c480c80c0400000e4640c2142e000e054841c042d428032000568409103280d0642c082c000e40202401900d4400703c0e00c1c01c4003501c0003140c2c0d80c8612242070000c0800171424038028900035000b0031043e400e007500204002c01203104030354140e03141d00b6103004801c41d07800380002c4000101d01d10202c45c1004004103081c14880c03003000103e00390403c442442078884034a144c0c11142d00d00b200304000d00e1102c503204650f015130450451118008551105110410890701d4081e20140d20204200c20708807890700140c03141d103854003c40181c60700c4c1d0a40745640c42c3c1c00c8016852480c004100b03941e121000d02108a82258008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 728866978 1250 728865728 728865751
    0xf0d020a0c14180411090c07051213180204140a1d04060b1e0f2e03020c030c0105070305010e0f040f140d0905041a0607151e02031005061809100b03 65
    0x3d403c518200744000c140c10501c0c240c10180388c050a41c54480e5108680c1c5101085440e0003d41c5448000c1c1d1030251070060504032100945140c2e200c62000c01942250141541d41040f44110f0b220b28a0a801c40508451003142c1e20050102c0c0d00461020343e080081c82554070300d8542070a001c050381c2c0c155001d00c102c0c01c01004014044c0061080c0902d110024107020300829114009541c1c6819105a0118585881062030f241d030380341100450190107950500d5105120100310501450419040340b0f100e48a199070811035a81ea424480c0c0141d0001e681592002d1a11004200410f507881c449410b4103000d841804190120529041e141c0a40c058044000803023220701400300d450540a901050344204041001810100000610a2191490040400042c11108400b001140c0c0021640c6919401c010b1000a55210000b019510880e002802d541071180301050600d44a01503881c1011001c2d80c4650701244482401103000024101d9150808000300c0064005000402944580f032203204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 728868228 1250 728866978 728867003
    0xa0f08070308010e092107060915110a0807051308100c02150f0610090b1b010e01090b010b0702040906021801080714030c0307110f0f0d020a0c141804 66
    0x6004010700010b0308586480c07001c090034403400b50780000740d80104082000c8402c6084c11800c100e00921f100769200205100c1c00c0034050700602c0141000e48519011101050001c08814901d10030240b20b01034080d03001c2219540400e50b0349105034040c01034a40c110310072800164071040b24910700f4081580d088007060321b48401d070350790b66418003003070a036510031303e00010150811045041c2c0c52540200242c5c0200340c0e25082240903403041c0041d0005061107140259510240100d0342503902640d2506e11107907007040226a50618148170300040030b40c0007952080940d00f8100c91078a60743c0300820a0303038011344820f41d0401144651008188a1503006020719401c260000050000e500041c01c2005000d040080120201403007001c0301d07840701402c0701d5980c0c0c0ea03540e0901034030707a04440450300c0c80c14443e4804440082c2c45c0095407009244e035400c200c403410181054100e03910802000010001142000200b0440c03a00200c0c07210240d0000305040681903603080192010078044a05503580c480154 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 728869478 1250 728868228 728868233
    0x1180506071202070803040602030712060e0f13030206010515070c0b090f0603090a152a0207091a0f0117190c030204031a10080307060f0c020604030f110a0f0807 71
    0x2000c0e5910311480940550500d0132640380d0700060b0100a01c050001c40e000000102a44e103d00c1c0b0031514803482890420645407201040e100200c03086940e2041c0c0e00080c40418498181c80d02946046641903005005503130901c8140b1800541c280c2c0d00320458401400814000b13400742a24002815540010540703882404041000d944440405240101c0e01001448640302011a016084075080b68100000461002070301c80180000c00c0024086c2d03010503000407a02e108508030440360011b40e402c031100c041c2c6840104003241c40d060390481e0589540f03006000d01e810a088000c2c900f0405043c500020089810701240c03540048590760707401d103c80c2d120b0a00b94249445a40d01078500c41c6821424541159903511b20143c001199505191582d800241c102080000e0b64000d80266400d903a120007852a00002520761801a01012420000c035903500030310018500e0700c115003640d079143c1c0141d2509001e0781e00d00c44111400d8a18065040140b020130307110340d6501d075401d2043c0c01c00ca64400090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 728870728 1250 728869478 728869487
    0xc0703200d120f1b0c020112050106051206030606030c3303090d080f060d02040905071403070806070f051c020f0712180b2a280203030a110118050607 66
    0x500c103c0030303514204490746201340c250750b60010040359081603110354450b0b0005179600c1001d04c000e0b8008074140303c008104954480041c0441e81c929100c04400d07500c03042c040648981088031040d41684c440490008103103002c01501c60302d5040c903007503802e2490090342a004030140851039400300400020600240c003404102c0240001480e01d40308426042889401d1548030010707051034801d18001300448c0555546a1003800410360040c12550003503a0f030843c04240488040c0e1841c030134001c0c643c2c0062001c2004c5422440f807007c0350359500c9007014411090314980c00c62601c84a95141c1c009049961170818401010442c1c90501d003103458480a00d040c03450380d20040385010801c4107655840c00601e120341e04d101c055407076071070700d854403059000600c94030196242610300804110300c0401d4844400456074007100c609142401c1d141c0003040c01e994088044080000b5050303031003003041e4580c9912854403085640700800003c2500d04164612038900191548103690941107007040c410340e187c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 728871978 1250 728870728 728870741
    0x303090f0b03090c0d15050103110109080a120503042303030610030e06010311040f0501260a081206010c02120d0e1c0b0606160c080d03050c0703200d12 67
    0x860401d8618039040601603200c5045445440c001c802d2035903e28108803110754648100101680100407130740e5a42800c0000f107113800380d000e010440c0039001280700f143c042920100e16411150105001c462010212140e42c0010070a40f51400495180031082c110015a003492036038050041d40c803414008100500181c0101002003030501d09102003021303510200d00035044a401a40004840c0998404140980030703c110400307006141900214003001d1a540070b0340050b05207441010500c0030384528540d603a25007280600080800d11100c0700c15070a041040b80d01030b01c1854840508400c550118141001c480611059034020940161030f42ea03103c02c2c1520040411940925540710068081949504041c0701a007001184000200a91039240c11100c80000b100340b00181242c0c2400c04d40c4144540380294190b0380201094098407a04c24090a805011555441403920343d2a58082c3e0b1016038256440303030645c00403040c0300142e44041c0000141600c080e25446481c47c0318800810440c4d84 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 728873228 1250 728871978 728871989
    0xf030c0306050f01060c02090a020f0a02030408010b1002060f0a0906020307030b0108060f0105070f1a041b14060f09032d250e07031b03140609010b0d1d03040303090f 73
    0xf48010003920b68480c20f20452640c0540314010192218030800c0042d1003000c66015545000240d015000380e40000100b0440c0eaa45000b0841d103c42002000b0000500c51030907401039100e4000315060301d8032907002c00c1d000b1200000018800441d81d450409a03041210b070800400d0780d4202c2c0d100301d540c020403210360140e401c80d04215600540c100203000c0d4060400013918400014000700100900d4003075108580c0003100001706507107080d1400c085035081d007034000200004544c8000840804501ea900b806540051040382444440000008141c1103008a250315105940032160741110288001486c0b95503022032070741040064071154901841c00c0c00e03170f0100f41d03400400d034600081d000110b074013514641c030701d500c1807034a82020072030107044108018042c2e5624083c4000c2940d400d50b004d10845040c5034110101550356000b00113840c8402d02c20b809076000e003080f056130590901c0d40007010340f4107881c03412481031900d8003040345160001e40048010030312440090010050200b1414000c19 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 728874478 1250 728873228 728873251
    0x2510a061403060c19050c060f010302010f031503060f021e0c16140402070512030901050103210207030201110a0807060f1103040309090b062115180f0c040f030c030605 74
    0x80c65124004d003480f401010b071040b105800c20440301c15109804448a180040080354410305007818041c088085c20321007280070407404400001003178064010104070400420134100c145d459070721004050460b021140039071030303400c10007085291124500c070705003155603a6816803030713030a40b080365031401200600c0e803416907401c1c0c00c040018480c41e00c00f25034205401d950141c0c0700c503034501e0038a19045107c0c0a18181580100030403105070f0b4154403040c100c0340181d00004120454140d01f9040d101c0c603031032120050700240c0d824030165002e03203202043c41d103141d000c0301c7e0b42c2101c035190a15150410071080303070307030944401d41510300782d6035805821480c0a00204c2189541465900901000c44ca403091381c80e0300c0c0c6c45940d10b1603170303690f01030588002c41ca40040e107503000100c01c10101e00c0050f088505100c1c0c92a4105c000c482402c05034091a0404503c0b18900e20035241d2002c007032300b860401014881c1000d0b042101040c200500090b1a0081d4800e0504c1c2610038154640075044d40c100802d50400e10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 728875728 1250 728874478 728874481
    0x3006010e0315010302130b1003090c0f0b0a030507020309030f1005010609180902030304090f0c08010b041211121903080a020322050f010c0903020102510a06140306 72
    0x342d0014041e81140e03412160020152031440340440982810b108040d03010384da09080303070701d80ca80640222220130702c5070042e11150364507810f02c007041001a01a40c2c145250500c209401c06009a02c0a5000605030040b60704000b07043c80002e00d0240e20260303c040e030f03400c00d4903c01c40680c0c403402141d01403c281e06080200608000c10042100c05c0901c10f244500e440784c070411f00b952020b000300c601801e00d280040c001300302130340c481c030015081c42c500c07140000703102000002e02510540c05903010b94980600601035240c143d2a15241c1c0d500540401e58056120400465410382c10030251707507250070000901c002d0952a050103041600b00800c0c1101440c0100108064040c3c90a84008000d034444100c0703011403224200f0500c0c105407800030013559807070481e074605c2e402d41004000046904c03d0782144c110540301c80d0002d620749a0f03a40459904500c0d4941d201e0082020090045090100c00fa905d40c40503802140108118044d5030825600b0303941c400600481c2740c0f00340d0120020f4000e03002402907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 728876978 1250 728875728 728875753
    0xc0b04080f21070c0e040b061e060307030e0139020d090509131401060f0504090506010623040608010e0a091227030803090f070806010b3006010e03 65
    0x400412802d110501800095080030003001d482280b0241c00c11880183c81464146070013088408182c1c1c600b0302c03807042c00390b0203a0a0440c007a0450301140c40a03060314255160301c00700341c024001d411102901035413950344490909900d0061281020005c034111041441c05100a0a100501c040b151085410100041c0c400d40e030018202c40c03c49100f41e91160b40750f61020441d81340300440c0740c4000c04196468510140c14503054102c40103030349000040c610300543c0d60080204451071104001c14139006440100880e40c000c2c0c140107601d4944080c4088412440311104020f50b100303410410115800c400103020601ea40d07500f880d408251341e1410031a95110b51903000710364085030b8410f070402600c40b10068407480284200c8410884000c0303050f1246490780b905900f207420403100e8501c9880b0300d0b950850010400940740c01140c6200000e012180d0030446000116400200e22045a00403604035204202c5041c840b110041c042c002ea0640383c1c244400010030420452000da0f1080c0d016000301000b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 728878228 1250 728876978 728877013
    0x405060a05100f1a190207060230092b03030c052d0d021c0c0503010f060e03030912011d0f1005040f0c1d16090303030b0a030c0b04080f 60
    0x6860301c01c00e00d110141d404c1081e240300340c41182020500c0d00d14030a880031505400240c2d00c4144c1301550250b9501c104100d0084082902207900c0b10000d882200342800c07590040f9008003491140a030076405454a483c0d602c7c0e50180482015450fa003d202c40984140350f414884e441c2504d889140c17644c0303403c40511140c0c1d01c0c600040030300f500c0c118924546420446c60042218046241080c0964954200c010241007848165000e1400103040010390700d1024172402c00c480c1640c0040d60b03c080ca0038108501229040c041c145411b8140c402005291102d503181400d1440b01c40e080400411140143c0001154185021006240d160f10130004145c80107404642088021841000002c01d561207080400c09150210b40161112f0066240450030b44800d5414803050404520030241540380c00d4032801002c03044c0700416000507488001403000034401c0d0002d20344204010a09154180c4076120405500b80d188d101ca010984c1c00102008115000d1209101420032000540702804c01c8822800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 728879478 1250 728878228 728878259
    0x20a0e090105130812100806090109060b030d020319050702150c15060105030610020703020409080c070f0302010f030b190807150c122712060e010b0307031709090405060a0510 77
    0x5e200690020026180f07400003080140100102c07002c82d00d00d0304203ca5024020b200d401415107585041c4400240f1604001403e195044003a45c0150315207981190f0750a50004040700000400070104268809a503a05207240d210f100c1c8065000e82d94103c40c5240340c9031100012004802c120034508004c00d0383e8214041c1c2e6071146059650300d00c0104440b00480c1040c280d6040298482c1c504415a0140f01d00980a41002510b0004481490f52200c02e6a0485001840700900141034440140300d0540320740c200c1a1070316809420214001c0c0458121001410f594110118950010108101445407094103240e171480f82d01344001294111f403212030000c000340c064001804007180b9501505c0894102c540c1c11407504061f80c090150300e1742900b1030b007015400d0007075400c075080c201b0442840c5010f118560750840010020010303685156941c51220640f06d0403808105000d009841da40d459243c05e251080c0c1c45100507003120b14005000c3c1044800c0a40300c410342c040d01400c1030011049200002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 728880728 1250 728879478 728879497
    0x6040b0114090102100231230a1805150109080a060b1903030806090604140a0b010504081b121c031e090f0606090c1b02060403020a0e0901051308 64
    0x1a500c0c0703280b400607071412000b510700c240401e03c00030380c44911000d01440c4071741001c008040004100740503204050441c2c018002c45003148542c142c4040030a01140780c003601c03600041c04400c000c1e40c1c1c0301040c540346440401000f42541d2210f0412101307061300005000e102c0c0d824240080c480b41010151503442e0040c44000b00590b0340d500031416285e8441c05480d80c502d042c00b050200103038076440c00030309a02e000d4682030b000310704800208035140360501400168200e0002807042c540d840701d10013005016000106814002d04100c082144075081c003502180d03140403201c007510200300d6424450f68034034801c801c0d025a0046c400c10790580d01c079404108280441460081200c0c04215400341040d1800d003550104185003200d0002041004031814000d103028003010841d491350f402400c001e42c1c1c03c2030080c00c00a038070404070710700004208030107000307031800a868107051640341e5001c00c40c0e9014581058100308900020031540030803d025455001c001c008155103c0d1901d40d842ea9410b00800c0d856 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 728881978 1250 728880728 728880767
    0x1302040f090206030414060604051302190b041d16050a0807030e030307080105030c030c010e0d08040b0f1b0705013914240c0705120c1506040b01 64
    0x454000240c5904001211500108425a00d00b01352030000081c851000200300035000e8140001d0080c030b007512130284603440708110b201d292102c0b075080102a10a001406d8407200030184041900758108000e00040c0102a1081800810303010311801c040320020941c41e81c40d50480c8120212952020540d10010030302d0820880984038484160003901c44040d002c0c4192001204000d806a882a0858100c0c0c2040d02a101d510142c1c0080c103442c1d10150006501050324501c0003500c50800742c101c0c4800c1400b48130020b041945402100c1056804220041142d00d40480e9100d5003000c03d010948014040c7c1e002404124039000c006005e107820b424429504110030303800f050855204601c0091084804020010780c030010b4a0300c140d80000c0c55546c4049131041e0154500d03001c0c4040b080719580c09448141a6560361001c4e840e2130160b1124030212814001d600303d00c003058465101800745042604058007181c1c81c900c0003903036400001450a0701c9142006100502641c02035107404008011103031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 728883228 1250 728881978 728881991
    0x206040b0309031b01020d050717010e1509010e0702060c040e22060c020717011401052e050712031a0d030201060503071e05030f030f0a020c102006130204 68
    0x1503e08500404210b9024111074041c00790080d5010b500622001c406004204216110b54904903038074026200c2080c15045110010720008070a80e50566210810240000201c50314002248140c9000e80c01060350030004000d0103940c40d0140003441d07000c480c40e81c0003802c1ca0700e0405850701c480c40240203400700800380920300c3c400e8051200c04015540d08040b0138094010651002551141c4a1103104100d0340081001151594103009d800b880381a140d8103600141d01f80000c000d14003002e0380490700074602e034056268002c03014403c4c82c00c0c03550042e00e90f01e480b04e0703441c00c0030407060380d1141c05a02018a00071042c1d041100303200d03130800c01c02815030304c1030040021450141c1c0104142e81090f81e151141800004031156022218040ea034801003540303100c0342e6144145591503101e66005c190035082800944240d15441e400742040403018030460715548081c5010444800d10f01c540680002c20510300031b24141d030303103402c81440406000c0041030a440d007800b80401010301408000d1080f9107521 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 728884478 1250 728883228 728883241
    0x909070804050a0b06031009030f030f180602222304020301030b041113051003061a010e01050724051501020d140d0623010801080106030c0e0702011814070b04030206040b03 76
    0x4001e0107d524403001c104021101d505001e0300d948039800da41c1c0c2c0042c2c1041e8203500716500c14010b40c1c000d002c03082e407001041d041580e0f410b4069082546114030390b1440842c006941801c10038484c0c01014a41c40c5110005100c1e0400d800d0919a240030311b01684c0104010130000360405115580183c100c982c25191101c51000150302c14295900c00440c40e00303200600019121010074403048911580d0700304944c2c800381031401d01d08002030030381d50302042256040d28140d5000703000504a5512aa0a01d088500d0342409074900d4901050081440c40d960010008070a6803401402d4116100b4001401e01c00c241c454000c6c2102d00c0d102c008504900007150003590941a0740104010300124560390040710400303842e03006d1940446a04c035000032003013000054015018841d03201903a070001c1c0c00c00010ba041003030010b4034190140c4444215941c0d124458040d1145258145c00c1c0392188000000c0224414862403814159030018517003039001f00320410040c1c3d80d103070031101201e149080039502c1c0d0b0f6807003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 728885728 1250 728884478 728884483
    0x11b110d030c02040c021b090405071e1203031e29060c0a05150705030115030b060723010b220b0117070507170f070204051902040b0909070804050a0b0603 68
    0x2080c00a41085c100803ea1040300c2d00401c1080e40001202216034900400300108100140d05841c05840f54010030418002c1c2021102c1c90100010030fa6148400e540e5640c1c0300c0ca1f01950600c0058001aa582c0c07580001040d50300e00b03000d50702085220600c1400b00170052501841840c0d407900303240880c9500702a010f41c60700c0003a54000300080c42520b20803041760030055141c049c821503621000c84600d00003440180148266070507560308070b099800000a00f001900101071213020981d105000703200c544d00066011247c5103289c030001464254040d00240c165007903405121031980304080404000c035007940c808010718404165542d001c07941c4280b030303001610400c3c0c2d10b401020464070b455041001c5160454010809148250319811420036041c00300c3d1154080c904040000300307800c000718405450180c000030b03002041381102900c0b40c10a405202c003242d11503800030040c490041600a036614011a40035030000f0b15082092462500f9075401c1d8640840c0e00e40100f813200035402003085901c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 728886978 1250 728885728 728885747
    0x906040b060406030b03060a02031308031003060f020903011b0507031b020d0506041202060105010905090a06051011010605030111160c0308030f04051902060318010f1a011b110d03 79
    0x5000703142e4594603402d000313001c1c0000700301442c042d00c60400440d07071850107442103c0c40380184050f203400150351a5110142c03036001818024803003442ca403000c00071440138412070181840102c00141e132080504281400e541d00030a4034101049503001c80102c0642041c1160350341d5506d481c08080d54041c131b1307900e01480d5120714400394000100c003001104014002a00500860140d01c141c0d13034110600c0c80482e84c55609000301c500050520b03000b00494201020b02c150414042c0e000810103c5d250f40100b1945001440d900740068960301d00300c42400002c0c40b070500500410b4009000100e13850024451070305c181d808113403070011f2010f081418003146a2a03c0e020b960300100c1e0640d80d0038142c1d900142840f05031000d0f01d044c05504008149011585401d450650b07010300322904594581040b1000500104142d038859500c805030780b10020310301e03c034160b4422682528280315010080005142038600000704c51a680d1108500c0045200c00010350a41c88044070400010180c40c030301107400e03d92 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 728888228 1250 728886978 728887001
    0x90b070632220b1e040305030106090e0610141917160807260c0d11030114040510050d0b040501050702010c0e040e0703140303060f040b0609090604 65
    0x30780d401000d151615840c00410389504018424562a8041502c007020905445140388840004402000840e802d089940c442e1280c45139411444040450744228034084408500041d000001132000a410440000c0540201451580b05203007043c04165020145070603101400103400e00040090b2940e8101c5020400000a58485000c0d000c0d01405101c0034030128415600c44000080a010000030740c460031507015070700c01115441300f4009458103c00340d00f550114164000741c1880e102040c402e594000c5c529000c0c817a507240b0403041440121140d0700362040c442c88080004214130702d0412507a0559030030440b40005d030303625000000191003a40c1e900030340d00300034a808000d0034440c400c10044e104901400c02400366540703402c02282250dc14900c03030b0b008601903494000c05420300b41c0c00b03190442c5928084540071516600c8441c210f04030070a80a0466200000300903841c141010400d40300081a1000c0c00800d46400c0007400314080c3d01c400e640206001c0001901680c5d851f04604078914 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 728889478 1250 728888228 728888261
    0x250c03210e032704091e02040b040c05180a0506040e0a0f11180402090607061a0409081e030f040615031b050a0b090a0e09010905030d0b0f040c090b0706 67
    0x18402c0b140140344000b500c2d080c950108420040003190306080c0101658542d200200c90308001c0700c00b51006c1d12000511069800c240d8901d03039204245c54034071440440c10315a4913200d855083e84026051015160011306001c0d4411941c108031079102d80040d00e09440b182c021064480e034501034100000c01d00b0002550900b410960510f02280d00e046c0201282071060b003041c50080980000c4c082a4441d0301003103030b0402d000f04928008100d29600c1802252840d071210074102c008100000d0503642030520544404400165191680c00c00c9084601302009038059182940f6110014854100d00200040c00702a01d030a181d2920204d0070b03c4071750203194803505140010f103207504144550300e118021103006190140c0301140300c00d50602a2110480c00509004059013080c52444c2c50030b00c040c03c02d00071507488401c041d00140c1e0070710140007003085501000034072203016010089900106001507000e2464040341d02e0410368040815810b403405400d860b60b40310a1480c054009040083c80d901420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 728890728 1250 728889478 728889487
    0x31401180807021008070503070c0510020a090f12050c0904030221040602010e030301050a030f0f0b0a0c09050904020d17040504020705010e0706021516050909250c03210e03 76
    0x341c50019182c00b40c001d403030000b000503892000340d441c0c00042d10341c040032441c03e10000340628424240c001201d84158107444c0c0c80c4c1e0000600005a07003215650401090006409124484030300310f41d040280645134140c00f0350b05d02d40d1109034562490840c018015104840000c1c140350007041035111100381149041d036803025958400b500c60300580030790001542411a1110007038000020349040e41c2008084c2c401303042c9181d44908061026403c00c4031103109035862100815030000e40c65120b10200180454207014004005180039a030350044c602c0781c0607a400b03010258480d541004421680401801d0070070a0441c038400d2140030302d0307128683c064000a0ba5004012042d003080c0304c1207403840700302c0781004c0e29054143d840d0b04485210440705101400010811000444c007c400c1d1006400e00518140ba1000031620034401200d0081c14005400800c1140c42c00784060111200000d181a40d200b65030744c1d500a0001e80041e50344000110705071806043d482e4141c0c05041d0001a0300c003100c2c2da8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 728891978 1250 728890728 728890733
    0x90a0e0412090504060321090b0417012324190905100302011707050d0212060f0a0819320c0a142701060903020a0803040308030103140118 61
    0x2400001c1e1421000900301400003d101e0a1500406050301d0348480348081e1742c98200c245205c0c00c66a8140c0c10100010340c54006241c50f588801000030b443e40340e02001160721000606825104080000600c154440070500d4102c481d1b0700c2282d4121050038050212011603d001007052100c1c05c1c02342d50310119007081c1d08003d00c10002401c0440f00d00880601441c2d45000d060703d20414103120181c04a205100b818125141d103a914941c001c3c050b082c0303141460307071003207204040381c1107880041d0302d0340400d4007480090f1800e0300303903071004200444292200e6428612402e845681a460b00100aa409650707002080091f08403014561103000c03500f4112694048140e49044580d5281800c5000f00f0404a116060000c0701d0416103034048219100c03800144240700d18007003041965100480b113104c0981200b9218401c0c43d00800709513803040000c41c1940100040d0401a038814191035004004c10000150a64141c9044a070414840300d1000b000c1e100704c0c0d0150409400740076068100c111400304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 728893228 1250 728891978 728891993
    0xe150a140313050f0325030c17180906030d030207020310020d0203070f0c030207141f0e0a05010c020d02191517090303101a0c0303100317070b0a02090a0e04 69
    0x1007a40c0100e04a50108210700304558403480340e051444540c00555000c00c02089486c0d194a5140748070b031602c8210b440081c0c640814226040d00709100c8170400007a2800d4500c1980c940e520340320717400c41e05030200341400ca00003556010354660b050141600440e104040d99824400c0c41006015644113542d0f90704850612030007903008861100120f1250030041c2200f5108402a081d4036070305400801400781440d0860944540820109a1004000350b003041c2c00d603180c55400100c01c080d034640000c20030000c0c0810204e120140c02c124100400f280190001d651254084104590144c0c2c00409a1079050000c2400302ca003a040b1303500041c44284102c0e02c0d607074450540c078140c1103002104207035521600c404907102c1c4030a654515440b80030f45414444200040440615100701c51080b03031a1120f27458855045401c1104d040c40411840d44040040c03250810503028510405407003e403500000da500d140c801d0301c010f4842010b0540c085038005964031070402d2403001c0c3c0400b020407095031400740707810342 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 728894478 1250 728893228 728893261
    0xe0c13030606030c15081b160b09060601022b0e03250e0603060a0b060d090b06031c08011203020c0402030a050a0b04200f0d140106020d0e150a1403 65
    0x4d503051200d600c00111070000300d0342c9040e541c3c103ea0743c0d0700c06900d40f401c4481441880c50a00e0032204010089043c401a02c00c901250307071445040c01c1c020911340b040e440c17424084000e01c404d055400005003101140314034400c46032401d00304488038950184000c0204c0ba100da81d132040541510610041c001862804a11340c10007201c2ca4225644e51502c1d0303100242040c1056070300d1505544118045a908165508444c0c0c0000d4003800031410000980b100350150f0f412a072096507144240c109002880c10103115280034081c41c041101603c0030701200c0100381c490305100f640c030340d507070144034040405100344074010914900400542d00c900307200c0204402064140c48010021b4908562030120741800d0040001c0d00340034001e2212048140c1c45400340961188603c504152001c015149508a0740c2c4100d0103020b048030708451882d818001e0207440d002c402d500c0c28007402a11149816160354400d03040e0050f0f403008980c240c0f10201207409a40e0441c5401c862030600801104110002e8802035580 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 728895728 1250 728894478 728894483
    0xf150c290406050a090201050d0f0b0913060513050c19090906020d0c0f080105060702010e0d0b1801060e01030f0302030c0d0e1011030304080f0415030c1e090e0c1303060603 76
    0x410554641c02401307800c958610038003d02045c2c09209038591003c155011050103000a040400d6810f007090004000c580100c1e40000740610003680304091150a1181c1503011002c0e401124030420302c0d0710b135696507226070301c91144140402c0d441d8109254501c00088010582c2038418481c01d80d2600c1d00c3c1004e50841012901028070300303602c04600c64812550802101e4030b5489505840c1d0810052000d00d900020043e03052118110322803600d61100f420300341c403850042c008202203042c00940b010340c0124072941c05090303078107280c0d0074004000c01084403411a036214107154003010280c94182d0a50148003850b400e0350090781d0120b014107410001c680c84045c400c45a0703004c0c4010740300c410baa200f03038000040c201d150b2062001170005140d1400928400e050040c2c074904240e91126607a482000c58240d21000030b8a81d0800c0810a03000041a04100072030008206145800308000b400c1c600307544614411040ba480114030040441801c603a9540c00b049008040340c0d44901308640504541d1008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 728896978 1250 728895728 728895731
    0xf0506091c0e01170a0902060c062d0705072a170106030305091c0c0b13050405090c0103050601111b15030609070e0a090618060f150c290406 62
    0x24000715030b12810707803030b041000161503060740043c10408072040c035000289005a01951564140c0160703071800080c000c0e03c2c01810040c030251400300550b543c0042841808010310040311000322002c090083c00b07662006071031601030340301e101d98280581b1807190701c034130852070b10800340c100c00099050b01800e4055603482402d602c020605095014201c1d0700c140300280002e01c051222440360b1030905101e03004a507010404007009549038888805000b0181d10110003201c2c002840703241d000c8000e50341001090101e90030040742c545440855100d1943c09110350425658500158443e03024442500744810900c082b503030700703c070040000424508002d070541d1044004012010b00c1c50301e4901200c0c420079020307008440ca5141c8920075150b814142c0790a0350b200c6030030341d40801c2500320ba10550006007440c0049074004982c4200d814112035590b042202016565403007806508000305203888044914138203c25030808508108d40c659184c80c1e66001030014034240d405c031040c0d601900034081c900401c2d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 728898228 1250 728896978 728897023
    0x30509032a0f0c0d030e150c0d0e040c0c12030908160b0604150b0a050c10022703030f09040905010504140609010b090402120f010504030f030e07210f050609 69
    0x80403580c0f00c0007441c1c150761101d0b0a072090400a4803901400c841c3d008041e101c9920030801c002d5104207a0003081400034581e100d50140558198070454000d102d00060f0750400414003030b003500070408401c4a81c00703400348000102c0e5400300e910951020508a4100c241a40c46140100c00a8052038591009841e1080954041050f40c60541304034075800004030100011146001d0345200c894000600002c2844801d204816a190003880001032030201e034480180e452411024003003041c164402c0b66804c001c2000c2107210181c40000440381c512659100d1252211580d0000801402c03207550014455400d00c070a00040002111008152003402170644206690f0701031210700300c07880d100c0103507400b40c0c11101003005418031310112543d04101300217943c4900f540503220390940e517040d102103001444206504504c00d905214a0380882203142c064400c6600d0810820001102c032a8403c030104140108081009504080c180d001a8450b0544500e4903003440c403d61116154504422101091203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 728899478 1250 728898228 728898253
    0x3020f3705120a0c11060109141f050103020c0c040603060906110328060e04030206010602061006080c0c0a020d0f0204110702090f04061508031b01050c0406030509032a 74
    0x81c155a003184101d0710144196076a002d4150107001c20b08802d60034072074844500c0000c2e500a0180794007800d5120408522a20859540524014018130603030300209185100c0d864110302001800c11542d003440c0160f155015841c0c1c1d00c0c2089480c1102680c00391070080c0000421002d0b41040c10400d001e120100115204070108030b429210840b0729045100c030070101ca5041140441c0700301ca1406540c80002011921894814050300c010740c1c1c00e41c09607226000410a66604002d6181d110a50187c1810071501d04900a4400308003c2c1500c0760808010400194800e8200b048010080d00184005d40c855481e0810b240940d0500000780c0c0120309024030b92042d2041c400403940620b0340039000d00c060b40c1e90440f0b103513010301c806001292040c3c0c8032414500304a00f4048440050320080c0d01843d0307a4480c10030814464030b50f040030021103034140703410040d05403803020940b000c850941c00e0204199451412840c04c600c25000c1040350402c0742c0f40041c5882c0242e140e00490100c0d11800c0300c59820301c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 728900728 1250 728899478 728899487
    0x20105061306050112020f04030c06020c030c0307140904060f06060504060906030515040203041506090f18051e0c04050106030227060301091a06031f1205030a03020f37 74
    0x707000303c9001c00c2d00004c0d001208a4581e0040c0000d07800e00c0842c038201034481e034807103d00c0c04d05640030200582c032803000c500031840c052080f201e205104500800d00d00d40b501c0c402040d090425400c2600c90b43c020000102031000a4000b1940e02d1080c5004000450700c4500203000d681103030007650005615010081000c2d400303442264014055203220500385d641c00780c2000082c0d171009000b1542c8108804030388502001901451000c2c2180000c041021416404500101c800030000b03100030a1082989102003031010071007203c0e05034803031040340c1c5a4202500b042d160420400030355400c01e1400c40005100e035850fa000e0302c02e042c81004085040d416413105580e224548003101607100c03030108010401d81e41b440d80000e41503491490284180f0032407038002200d9400403907000c4214135000e40408420f480c0b8412600141c108080d91103030b2480705803151070b03803801030b140c140041c59400602c0c1c881070150034017510140181780380c115403241000400b01205402c200c5030080007400d21840340262034081d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 728901978 1250 728900728 728900741
    0x1c0c090e0a0e120702030307061401050f03070b030f0405031909050a2310020109150b1002060403050909072f0105100612050402010c020604030b060312090d030c0312020a0201050613 80
    0x90010100c580030f40000010700d034028070040360300d848108004030020b24140200b6184040740c0250448942c50401031140113904c0c0c4040510940007040d00f0300c41c1d42e1050003541e0b0495039182d2002c0c040c1d80c0d030386012407540c4146480c0034030503101050700d00765144c0d00c44902d40a83d03000361010740100d680c803007005400300140c2d00c0d5031401051a101c0d20a241c02d140409461604042c80045800300d80b50300c401170300c02561000b2519140c0c0f0381c0001c0405c0d0038501c01d20030444c405840100b1040c54070352001052400b402c8089480b447d501008151464411801d00071060905901b0500a000c150000602c011401c40390007055401c00000400ea803e40908000880741c198480380c80c0041c000a07890b00070080100100e06010505100c5130141e100e001c054805184101d501800c142022420185000160910700f0300c3c499017080200d0341e54442e4402c40c403220754035003402c010888036460140c0b144a491036551900c5440400d03500a03403941500040d006c1d84007501d0700b4880701da21681c050240c0c2d41c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 728903228 1250 728901978 728902001
    0x9150301150e091f350d1211040b21010801110f130807030804060206060901121104110f07060b100207030b18150f0f0118021c0c090e0a 60
    0x34640050b40712400f21514040c846800400c0c40341c06500ca80c8084d048600c8500c0400003454106145104260f4130b20b801000c5205c0c1d5001411080c0c2e12140c02406000d08500a40001da2610780d1f15020308038102c00d0360b0243c101c06c41811b40351141145088544284400e01b003001c141018000122100180f281014200d281855030b441d008c0002105c2d2841d503c0340c80060010701c3e20240c0040e081e00c09000d80009103200350b00c0e1f07c0e030715840d200340240b41030005080c0a02c603000c0d0340b00410111a03010581d0b80340b150300c140e10b161003000000010340203117403645403c541c25400040c0100311140203001440824400e04041000380860410701c0002808400180c2c090380c09609d06002064030040455070001116035010b055802d140140303410640c110074242003900e640014003ca0101702c682e419030140109121503010f40c58125941e108079403203108464207540c0025940180f103101c007400f00f03428168203018070004004400040903004ea0713110f5610f080d201c0740f0119601c424030380900305001e0b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 728904478 1250 728903228 728903239
    0x3020109050f0d02120303070f0f2109020307090608010608030702130510030c0f031518060e071e0617100311060d2301060f02030d0b0609150301150e 66
    0x40c24241880502c2e40010403581d80409885044001070f80c520381c00000801c1c0a4001d10703124109460041e04040c842880e00c0244040305040d200c0e0f440c2c1c8802c580b81d0f070a40540500051080c2200307030f03000402010502a415010b080400704403819a45c01000407a02444000c002a9584031010b58480c041c440b4029401a245441e00c01000d0250b0440d0303802081052141c1440c999070b0b540e540b4000c60035406007082e031000090400900002c81808035900c40000f0b8103100c009040d0b0352070300307070396054440c000c0282d0382d10644540d4820040202502601c03d8400700c0040ca08000800e000320001c0384242000160030b00e882030b5038050400c2c88140a1001500300c00c01d51815607944065140500030a03076000f92040c840804200ca06000b030a524115400e618003691031820072607039a0103c141c2254051080700c1034042c8206600000311402480503000c00100280700400080c814410707800140e41c8003100110140710307100d1820041d4100d80721614044040d04444c001640c2c1c1c2c5601c02c04059001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 728905728 1250 728904478 728904497
    0x80403080906190c05010605120a122f010b010f0503180c090a020d0507020c030a030818030a02060702070501080f0103030507050a052e1a1302040807060e1801030201 73
    0x61002001d0900c04400410460505840c2c6004070105025549908000b03a0600c0a50061020a10401c409098250b03500c20b120049422500c0d51420785030402044101c03800040d280680c480c804c1080407400b1600903011405985400465100e804071051034103500c2c03c0d032850060360094041c04a1546603481d154210740c0c2d441c945005000741703049129114069504a05110f9a410382203922400c0180c0006840d007400252440c1200d5004104001350b501051003815a80c1d0b0000700c04545550615058149664802c40c0c00103451400610540761312011905040704c3d9000302d4072512810083c1c0c21210fa45a44030011968a00281c0e20216100c02210045c40402d220ba001081002d00880850300302003415130390700e0b00e0610034100e00100c075001d00c0006c102c0c084510510001d0181408001e0040c03000700e61400c4840c2e00d920070120b2080c0e81081650400d200b00d03070180c6008080301d609948140340d0300e102c090314400346403d20910440000800715040304440140030b06882d010f940c0d11030307803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 728906978 1250 728905728 728905733
    0x80d090f060e010c050705060304060203160e1c021206010801140a0506180604021c0b10030b091f0e010b0306120a0f030f230a0f1112030a0f0203070207030203070b07080403 76
    0x4c0c070004030030554050251001c0403485440e2100110b009078481c1e000107940340b901964590301881102252003c000c0130030003d4909644d50228071110322031004801842c42d100e4030014035007240c111a0350707580d4001c0000005241c803065000404900200f06501500c1d40c1d01181c0b00e04071902143c030a640461031010142400c80d03140c41050b40404064401441d00032081020310000804080c03486020b80ca4940d820614100361141c0130508a4504050004450040000c3e129540040060701d08807001c415980d1591250450b003002402c210ba020706031540c6400b5a04003e40c401c40300e00780209513041d400c02030314030009500d944854115a450205800c1c9540417030300320081e00800c404009015414646c1c101c0582640381c01300c40003e9016a0740c1c0b41800c4050310201c01101104103002112044603c0840c022414509024032131880a40d02ea40b13031540c6e1001001c500d07100041d2a403010003004042c0ba000a0355000350fa0007102222500c03680d6482e1b00c030280c4900700d402408101c051104200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 728908228 1250 728906978 728906987
    0x170403080705040503061f09060605030c070c0512030a090b0307080a0f020f0d0b03070501030b0307060305042d020306010e0c0a0503040c080109050a0c080d080114030c0a080d090f060e01 82
    0x10041482e1411a1426030307218002842d09006466070000c4600001a6031a02014074589200500b10b00005100032440c05001070014080140303841c00c140400240241044643d202100162a006007640001c1805110a903502d8002d00d00c00c81c0840c103200000315000802c80f065a110305500d9884640c507030f0351000c44e58040d06012040b52019502803010f14034000c603100c080d01a070300301c83d600001c0b000080001c0600d01303051540b0140c1414a8808658010745008c10918285c440505001c916515145402d41e0114480c1485d048002e40c2100d00700725045d454607400820b40c0c000c600311001030741c0300c20884c42245025101101c0f1420f00b00700004115009801441d0300a0046c2d1245090f07a980c2d0560700e00f0340e059010101c0d01038104803918070030000c06080340000750560301c00501c0455040344000c3d2102c04180503200e4013060641d807844459404100643c850003025140021566450128640d90244070381e00c10049000918086075042c1c4003c00706040715850355840e1030a4800500556 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 728909478 1250 728908228 728908231
    0x61208030f090a02220b061603120c0c1b0308040909032c210703050609120405060403062f0d0b120c09060d171305010305060a03061d01110c06010617040308 69
    0x1210940751008686c0c80d46c0d03218040d1035004016801a4000c00365450002c01d00b1021460030b0f81e8152070a1070030415194040c0240802136444402d9181595034142148022555036000030410040010085103e00c03090304132807803030b502c02e860720307402014451840c0c07480b0a86124880c03d80403c00301c43c1007491818400856894617003540c20142100e0030340889041c009150000d0f91143d005c1414000040d0040148200d0311003103032a0542082e051030006a440d124601c4090501340d102ca28610881004030401000f41c4100102403080c4900c10014800d19040307a0b6420300c50381c0c81c5c1004220300e03003028070041c125507050501511000700000c081000d1524044c02407500071854401c0140001c0c2d0340782030351804c100000100c41d04d8803008450246919050340225040505090510403541c40703480708801925444000810582c02c0040c1ca5030850f0804455164550b00f07080d1110b61008640005280050001c070039078109031307222a0140c880140b4407100160300c0000000140c00300b4442c0941e01d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 728910728 1250 728909478 728909539
    0x140d0c11060d020f0723061b0c1006060909090b18031207020718140f0c0903070f1d0402010503040602071e0803190c090b0d061208030f090a02 63
    0x198181502124148203c0c0c001c000130740307009280025228103000c02e281101c010351455021601e40ba10b00c80d0007054071404040d05c0581032500c492104030001d0340b09400c0e160001c226a00716002003401c1e606680140c8150301c40c0c0c4021581440001c682da4440b8001c8006903604154030035030607150846c9a01060b8211881e110071070006001c400b5811a5400b0040d00aa856134001d018850501d000701001002c00c00400b04281e24083c2d0030307c0c404584400355540014005030a0181d5644e100350340c026403007540c00860b45801a6140840c1441148103d1004ea400c90360040c1080003010820b51030510007543c0203408035800780001400102160014483d4a10a8210440407907820111490710340c41314508a61303004d4040100a21410030700d0890745902c0d0b1a40d8244090b224980c0090304140f054010b40405507000103580000c0160340d00440001d01348041c00c0203800300141021503642e04240d43d2202079041c103c012030004800041c3d03410150350000c000520380c58450502460014124050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 728911978 1250 728910728 728910739
    0x21050307080c060f010504020703080105100e19060908010c020307120c060f0c0210060e01140a03142a060a03050421081906120303090804170a140d0c11 67
    0x3014002a48180545205510400100403605040b1900c070b0301000160005402144144540004607500c200c4150448200790b896219090074031104035103040b226001c0c503410401c214034070003401400d443c1000840c0c0740c580c0c0d01c42d010b5480d420402e081e181440381e9240140e1042c01054007107a03a990080c0e68a09107410104000186942d641042c3d50b20a150080d1442e5148501e40550350140200c021280c815a0100800ba040028071480003406008217004075000b0351010301c25403941c1a08002668000c410b40c0f8081c0e00001c01c096440004491049a03900c4d10a03440c00300309042078043c600000f00a10440c00c04825600860003020001c0c4291507a600305810500d45104008511b1280001c907610441a8a0495034009222400352200c46070286441c00400074542219009000c0e00c2d030518011401d174039241061078040c01190040789500240042e0400c180340000f03640510355100c1d66516508410b1008801d8490080f103032120045100180c1800c0081d090106020a1450044c031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 728913228 1250 728911978 728911987
    0x4110f09090733030f050112230a060e0601050307080d12150302100314130305040510021c09090c14030a090503040b0f0c060c2a0114131209210503 65
    0x8840011070b182c3d403056800320303640303e000c00786854170343c0180d6015050380242d14442000554402400e008074070503140802e4692031126030686420f0000e80306958000000f48240300001d824035071509000e115451107441042b00001d841500465603501040c0c59803540c41e10744015001c00c1e0094100e40c46501c100400000c0c000c00181c0e5201c83c1a05d0201c0281c1d000103511000990301000080b02500707203e0b8040203079407120b001a0b070240880b401d564081d1044800e080c0382c414143d25118210400c203001a949107602c04005612000745421030325074070000e00034040c0002c0c09580d289544c0040f070031909010400100d00d4005500900c140354032460849161a0343d420b100d50b000d4011594224046200080a41c0c5100e02088806d80240003030686914111003458429800c0d00e580041c41004400404010112042940030215031101d00501a0305840e20f400c2d80030076148004003ca43c160380111804424500c07454110003500c800028411841c2040b6401d0540001364200c1241c06200400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 728914478 1250 728913228 728913299
    0x20a0308150a080c04060b09030a021e060408030705160f0303110f0d09440309270702151f080a030207150302070317061804110f090907 60
    0x8102c24000c042c0c0a0240841000d80c2d070800056604c1a41300b0f95000409200400199a01141c0000c2d110741c1201c954207800c0303648426200c0701249940300c3d644074001050014000d600400103000d135030703c610151f5031070805907510b4903140400360041003a007400200050000a01816030801005840c000b00c581018001c0112883d210729160351100051900004004418100f280440081e044418454814070303000f500c0059140d0000780600c40b17901c200d9229100e90070620849242c09000f900f280d0141a110108a180c450303000b41d0003a0b8a1004c01c0043d0400d807000ca50024000881000b158840c1c54040941c4800e42550500000300405941c6c0010784820401644900c54401d4016008035441c008950800c0c10980ca200c0c1c052500400065001903030255000d0b400c03248480c0d0080854888202040d42610400c04000d213030341e09801800140000d1400328204200300701c6075805c0c002c0c0140144483c0700c0c41a603115074544e10800b01480680101080040e012403948107048c0060100c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 728915728 1250 728914478 728914489
    0x9270f060f33120512030408070510052e03060506030c1906020706050f03130c0302041404050f01060513050a1b030c0e0a0501022a040603150b030105040201020a030815 74
    0xc05204041e14003007403050802c0603810500004010030ba070701070400b84a0351600741e15081c0000000828000003c00201041540000d4603c06a000070850741c0c0b60001402460091000340c840507003580c001a201c040280710110214020040c0d484c40f040c000e40345960b15005083d01400c0203030715004a80c8122141c0d00c5414112003110b80c0a0020b02401c0d180c408060b0520701e440e000942009001c100804074880c1e1001100c0e0000102000340307480301c3d42810b03c0c42c0b030380c6030f03a40000b0761007401d0800500304082060b61070b900170b81c026800d0b541c005006140c0182200c0c080d100795078000c03210039103803030a00c2990381c0141d0780702240d07180c08160f18135202d0280c0b5005043c40c00d04000b0075a119010b0031056030002030344003240c105a070340d1a2040d0074000003039030b224042d80240f001009070b640304503d200119124000882c81c090700074014961a803800c80100d9980038030004419150602501c910700e01400341900490301a0040e24203514603840c11036564a008125021210404581c00d00a4444 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 728916978 1250 728915728 728915771
    0x1315151d0402150a0207120c0e07080a060519090504151b022a0d05011b0207090b0a0e06090421050a030b0a0303121a0a09270f060f 58
    0x1010444152401c0d1041000381030079000ca00895010030b001410410b40c00103039042c140c0340422040108030b5828548001092160b403c521a007442c0003061000e295000040301e8060300680d4410300503103850b20141302c8916070140c40c444009210702e2040200700d001c0ea00030398020340503003003420601d151a07000c0d03402e84180030f1400d84a416088031041c009507061007580c1d020540d001008410020b001400990081030381071691203010000814003c200c803d51107110310300c00841c4414001104500060b4031008648a441c103e0b900340507881155140c4002c00006543c00d2800c0d142260301d903079091180500004104032a440c45804c030002c04c1900f07943c4c28400712600f90755240d6452034180801070990b4020768242c3d0048280307000c02e03c0000e402040c0030030382411000001918146049583d06100039500002e50403034403040e000308182409401c94201c0e44045c034010245510105841e98030005440e101405500b00481d106000880c541c06c0100c6400100102050303802d4031122810200c0740 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 728918228 1250 728916978 728917019
    0x6180a03110a08010902030d0503060102010209030105090303010521210d02130f0902070b2a0304050a050f240601030623010206090111040e040206070f1406131515 72
    0x19521054000703494408585006001c511000f072103030400950219560364400780441c8184034010000031690b92003541625880c100c028000d201500346502c02c2e513140e0703200f8001c190040a0203116444031206908600004842c3e81c80180700e8500c070f0500390302d1180400040c050409004110032450038a0320b0001d0b00302c02c0340036024803202600d8920001304803a229030001110078014811040414072140206a204e96030340341440360780000007090091410814090780c540700002c014070080c0311000a1443d0907a08c644200c880e00c020b46c084107603449045d440c24080f00d0b003114a0003000700c090b95803040d03080b007410f04002c6660b6881c0da2143e015450080280400c2c0d0000011000c0a982d041202e142c200c090320b8020840314500300c00007045031040b4080e510845080901080c110348600c07088401160304212084030300c280c5844c0031071704501b03002c6015000348910b10200314141720300f25a40f041560300a4074034500000c0103020101908001e603054030501011400041c1d00302d402c6251010034507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 728919478 1250 728918228 728918243
    0x40f020d0c082805030703030b030708030705010b1e0901090906021204060213090c090b07080906030f011502060c250204060612110906030f04080c01021305010f02060702070506180a03 81
    0x612a40b11025112022101d00c44586001e41c1902213400401161080c41e090305c0d0110b20081d444001c82e1418540da40b141055100004d031075070a204040d80b09158013441254500b031720384a0aa80c007041401116a0303039a200740c00d900104108419a030100d00401d204a40250602d5880c070303030780750410b101200e040e00e0f442e40000307030007940c49140d42a000140070f4031b4908005540c96070400610100840c0a04041c003140021048103205105094a2040308003c04266403481c003071091040a120a00c9040e407800d1940c108079144030b00206199105103400f688090070310300e11024040111402520030a07804024185c00005030300e0340e0040b04060702080d04c40414842010b90010103d40c0500c104250041090004030315540d2140704594206181198000b6291164101b8541612500e4248001c540c40081c0503c0d039002c1e41c031010800c0f034009807282c0c1d4081701420400d80c2c880c0000c561300350040e0441801800705243c010041c1c90b082d1560324041c40c01c0100310300410200c60741d0350426207100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 728920728 1250 728919478 728919493
    0x40209031e0705031507021c0503070c0c030501150305070f1d15030a0602250f060221100f08150f130212030414190302010f1b030807120212040f020d0c08 68
    0x403071f01000350601c034441d5882c501150080c0c10800a1407404094081c10805c40500028000d03c40c50303a81c01c401545d003082c0208509007000d14003101004041c8406c56042c00340410018641d500880c0c0401202d200c0d03241e40b01d81110100c6510f80080c00244081e2405c500c405070103415440c20821038444500c51040165288690556a08035500d9068402d24203800c107030099000070301003200d92568961003a40562241001001c400202224801c24100d05403504104545230b1100001d800c21102a12100345280d6214883c0903250030200c483c800355444d40c01d0101d000401e82102444d88403805034140040c0c109251300240c501004002c001006502c003213010303c400f032048100b078042014121103400b0000305841840050081a10001e418081c42041c00e415541c09041e40110109000e5040a1441c1c003a14014280e0001034400e207002560619007840b0410084c402c40d58000c0341003000d0449503030303580e5440c2c05400e030041040740c205010400e00c4000610354440340020341488000740992 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 728921978 1250 728920728 728920741
    0x406080d0c0309080d050d0203100b0c03070c0902180d060608010e070f05010504180c030b061b3d0905060405071703071e06200711040209031e07050315 67
    0x400c0c20703130b4200520980282c43c0c00a861030b0010100d40382c0080c1c10f0005a16680e5403070162004400c264005001b10700c000070302c58801140800180502e621076601541c2003500d800c0100104c0c0203a42103000e01c1d610003482c52050b0315244440c0b09140d4842c18000c500d4503260070386903003550084043c0b80e482d54060076050003044c0d0181c020501405080c40c000d400c1910381501c94081101c402020200720383e0b40c5a15071070152198000c516074180c082d0286589000000c5002c0d14020300000000c2c5c4d902030b80c4402c45610405a00201c28521007810803480d0108003104159a04100490b520140b540e40056100050061182c40c0c4998000c0c03010300200c40c500145001c041102910421082d00100029000204007002880702401c04c42401e000c9030b00c071403611000500d0101d083d040700805414140c4558010f61004100061180108213609000c040c01c0c4070590007030091290341034021802810074203400d0000c03001481c0c407000071540e001e540c0b040881c0c00e086d40c501c59249090000340400a8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 728923228 1250 728921978 728921987
    0x40e070812071e122604031d0a03230709110a02190c06080603031b030405030c041505010c0312020706050708091507050a0c0503030c03041e0507050d020406080d0c03 73
    0x543c0000a1084203041d03d41da0b2440e9007a49044c2c000010f1000440e41c1e100d03c0401203003012a249241c024a049905003400d0141c99210000d101c16201480510104040d0506010010440c0d07444005140c1a02165020110246440340301c030104d48504030b0000380b0309903680500581c2801500c2c0c1d803551000c40d024020704060009074020b4200c51580e0030348000136100f103101401c94540c0c0c580058a0f40b030b00380009086100d8410000642203542d242e040d458900031004200301c030030480c11101e0080c45032043c80280c402d0080c4002003030b400c1d04030402141d4000c00541c2d04251082c03501d080343c5105038100710103c1e00146015902d060b039420400160755000302c082a00804050300610400c04841c10980003410000d10342020044c2c0803a422140e0341c0500404a88140d00c0402d6036124600180c030000b0b9074100300e07010351b841d4905d42450506080500020034110b50401e024042d01807d003002d02588590406080360410f07600c83c2d000a003c1001c1c4030030700c101c50071030f5a15805400d990070020f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 728924478 1250 728923228 728923253
    0x1110060323070b03010b0706020c0a060e07060e091506161406060d080d1d190c050d0521120a090b06040c0e130204090921090b09040e07081207 63
    0x180c550b4042c16052000b41120030640341140ca4010215035945050b1400348082e00a072480c03840079100e140340402c101300094011140d48800d080c02c5844050b0b075990102c50150b03400e01c500c0d810103000008500b02d5207820440c0303070311803030003800c82842d0554080202d400e0881901094544094051070490050414024550010700440c1c0d046120440f94562110070720500c040c01c1071060f917402e503100707914615406040001044200f0340b01100481d80140d0f2107180242400c80e0101c0c8410740101d40380c1351420610075025003150003006058440030005107242601420491048000d00038203807a480d039040c159100c0c6441c503201242c0e0700507901d080ca40b40740d0f002e00300034810360902c082669110342c0214020b01849041b507036600c00c0b00c40007035000c000b80700719040408064200004802440390444100c0d804001c02c00e405074502d0140380d41201e400181e409201e00d37450341089840c556191a4016036400c0d0081402d039114596203034080c500d4445030301190104020003103200340034010309100c0c40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 728925728 1250 728924478 728924543
    0x90a1a0a141b091305090304051c08040e0711070f050907030e0d0c14030c01050106140c0616021501060815030c090103020927030702040f140711100603 67
    0x1c003050811000b5582075520080c00e85001c81c80108124441d50b544460311802850368a10400184c1890740109460341c0c080c0c001d160141402c03002c82c58001e940c82605681e690b410003041400e11f410155826050b2601420360b9080041096291524600c00d0001c0c500401e20381c2210b951140c500300031f00c0403060005100c0814140350680801c2559400b040e124249035081c604804c00e00150300e840410100d00c4030284400d0310021810f1134440105600141c141c48083d1100c03130071f070110b000741c0300c0c52807040240c0b07400c1ca60411408104100c003030171402c1c04648024015a02540c41d03560b10320214401c02d0703004100041d443c5003401907148500003078021500c400d50150080c049003030080fa00082c410301c0028005c180319400504c1c0f2402200d1310016801c41090800c0100070064402580c0ba040030806a00c00c42c60405e080c0d01d10305840c89001c8050401c0c0030750705060b0f034030418141e81031040364000300264000e000c000e42d02c04282d4821301026503c07a04d140803912464083c002074540e920b0a40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 728926978 1250 728925728 728925761
    0x50c0f010902040e1603060e0f07030c0e0f0c0702060306150c011d12091003150602011a040e0606041104150507060f0b03030f09034305010c030503090a1a0a 69
    0x801001713007000c180c400b0075a07800030720128111492900b4240f600c0c844c601d4050907409007580c04401c008070240c14208035110740345001d400da210418860703004c40b01911002025801000300300700604010b00030b142d204000400c0d0303980c814103644401195030300c1022908016503440441100c54001c80c481e420100000c02c004040d00e400d07943d4506150721510001502c00d0303140f010740901241c8250498200c00e00c0d041006501540e5448019010f05000000c080d15513100006100203803c081c480c803203c40d0005070003413280d07469003c01e12000781130700c4085400d299010070020400c0f04003000000c0910ba52603444aa650703070b660518000700c031119585911514140a4124020391340001551126441055500e680b01000000a8034000c0900b203110161941c0c0c94002c1112085416010140d0346c801d84200c02140c1c180e5910a0340e04840e0007a1030104070400d05c0003020900c203a002d580d1100b18201100d81c040000d450350142c00711900580b58440c401181000a540c03003c1c00f4181c40c03840460752 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 728928228 1250 728926978 728926993
    0xf0c03031b180d0c150906020f0c09160e0a2c040b0c0d02130e07030b010f09060e061b01050709080c180c120108030904111e0307050c0f010902040e 65
    0x40c070030510742441002e18031801890040707100f485034410a1400400c59416102c613000c0755540c01900c0c1080c1c600ca54009401100d28a81800c8800701d51000743c1c40000b071003c00a590fa0384000c031880f01506110307408001c6140641076443c0c6031415944040c0c140d110041801d0402c1180c04c41c403011000007981c1e4030682600900c00029180120290002420341481e03407208031040301a4000d0080c0d00300f407440c070302c0c2c1c0040018581d070141c60f150f80a084155802d0000607001d400545030000c40210900000b0340c03000041003854441d004510715088002d060700e03c0d01900000a902c21a0340108100c5565591400d0000c2c850b00300d1001030003410100040c0540040d42c600103000c1084c18100d901009680a0014a88081c0201200c0200c810000c842c0000d585660076190303aa000001494000e03858840d80c0c8001d03000c0f403001d907908042548481d801700c60540d0213800a036007018142e102482428040301041c01d5040c00030300010158103000140b4803100340104000d9680c109484d000c141c10800b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 728929478 1250 728928228 728928247
    0x5160c110f0d060216021f090902030a0b0a0905010f0e01061205040602070506090c01140405060d09020d05030f0d0b01050705100c02071703030f0c090a15050f0c03031b 74
    0x111900308041080762000c1d0584440804540006032003640140a684002280c50385148040c1c25040240d00a8812405540740d11520341004080c0622035008a0210003040042c04002e800071507000d070864034041407012540001c5180e0307019642040c0305554850005000300c03042d610030070f801000481c1a96190f0f515107403002d0031400c000f005000355152180005420701c00f55404850589a20004803180c034030b0300e0603941d500c901c03113100603500144400200304100c1c0480b0061310107481c40240340a141802c141c00c800300524a486003245c0040000803c0c0d00803603002d0010303101a070070740c45c1c805030f030361755042c0c040f000301c0e02c05041e200e05025042c000c3c0c1011460004a06100c1c400d000c0001501c0c0342c2c48a01039141c01d06179445040c02d0700220618003034800c8080051800b81e4014400852540ca0390300003007100d03005d5a062650803950300ca004200481c2d140e4640d0350078a046040c200c0c03a01c4650540c1802e20761082101d41c0c5907600000500151101c200341d44007503011640c0040c2c0c1840440d6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 728930728 1250 728929478 728929493
    0xb04052d100b0a290a0507150e0d081f06021e010204270b060301120303050612030304330c1704110f040f0903030b0901060f0f050c0a0c03030305160c 66
    0xa01030b40003080301000c0300c041001c0091131240c5030140001c1650f92109030345030b03009046500c860000c86106a8100f6841109140c50140d01885040d0302c029010300c04041e18100c41034174004080095207071643d4850040f681c0c0303010214000d42015400347c00c04600b03801503503c03990403a5044800c0750303104002c10800c00c241701070340158949116100205641c000003403074001d006941f032029801540040005140c044001c4007200c47e0303100c0d4606002c25640e050804c010200d0075040c00c0c0e5584c004000080010701e40c51080d65012440422140101800012007080c1090110b034100030715541d900d20004194220240d030407210205461032450f85465aa884042030000d081240200002c0c0380c410100d54440c0c100d00c141040e90603041062032810b04006016181c08508180074110030400032035401d00c1240300003414030083e2034030314003085c0b089411078443d4817000380900b041c010070f003102001801004950300114001e5402003400c1c20800d09038021004c0c0a2a044188421080f003180000d420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 728931978 1250 728930728 728930749
    0x307080d0c020f010c03020d060806010311060f160809041b020d0e0a180522030f1d0d0c08010b101b020105160b0405070608040209040b04052d100b 65
    0x51000481c00e2040d0070320680c906007010744503424035402c220044a56541c1540070707008000c058042484a5655103a425448400c01c0c00040c0c00300d80c180b50000075a007410001010210030b003a070410300e4220134042010159610080c11100c000001410400f54606030007070522822010b80000520749100c04080e40d40c1420410701014054540480c001c07903034520112400a0040300341c1d000714100a880413000600d0200e4401c2d40300000317400d403050008910030641d800150f00d511894049407542c3c42c02d44603500b220105a03c1443d05103d40440ba07243d00e00114440307885040000030342070401003072a0944810492450190350700c0c20305003440d907501c10204603000000401c00311070141c0900040351140b10b4400c074801081c0c182d80000c800c0000c45909075104034058015140c80701c0e25080103c444e090150f4001e94414016408500425038a40d0a075800074071903011240c0301500c8201e0361916150800003933840505001021904c5d482c24003401040d0b5103e040c00f0050070034030748000350b1148032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 728933228 1250 728931978 728931997
    0xe0f041b050d1101031b0206010914010602120d0b0406030f02130b0315150306040c08150f06121e03090307210b10030515060414040c060507240c080702030708 70
    0x10b0706051401d9640a41e204041306d5604441e180e8400040600184d03441c2e000b88540a07980c0d00d019041080c5407482c48006040e541c05074054540c40c503e400c0f40444c150051006184016030301c1544005650b101d2003031800441c815410790310484224010400d07a0412003207406042c90401c5c948085599004c03556003c090500c001d814074a8513070070107220342203604040780c1d0b815100c0c08050105201c01960640b00320f9103070764100ca141407103080c5601441402550204c11842d5201c010604030700e42000030100c0420040116410403a00e034044440c00045d400601006400c000b6580502e42002d2000501600c01051201c004540c0c041c00c1c44050390307079520050f000e1200038001c2110312401c1082d40c00250740040495505a100f5030f1120000041501c0040c4240d181038880300c24107002a82c510300c580c2d040030310400071034500907080d03030f2036804001e04844511140b01d0981e10a026814100100c0b400b5800001c0c0700300386404050720000d40034007840195030092000000143c0c8004c100c400025 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 728934478 1250 728933228 728933243
    0x50a05040c0201020705011401050a1a030403050a020f0d050d0e0a08071407030c27180b09010f02040b04050103061a031f15080f13030e0402130e0f041b050d 69
    0x524401c02c0b4024060100014a95401c00d011410ba800041c148207041c0d850886424031029590f0038111a0032400c80c080c0900440d00b8000100031a0107407018020b0364515005072041d038490345003541d0800e40142d4919000c82c00105a00c000108240300c0d810180c0914401801c1d07405d8691540801c074051440d00524000364401c5e4208d00c8481071003240b00961340410a01d0640380c80700d000090015410350a92245800d4154400c000c0c03116001c0c5c010603842406030803440b40c0c0c280e2102c1c0c965810081001c0303401d649071a04440342d01100d100400040200c03807102c0c0e4036141804001026552103512030554000354002d1048031510380c804580e0084c503406030300a41c100c1c03061041c191102c040d5101240d4500c032002c0301020f05801a0345035109859009003641c1e01c1da10f07a81e04100003014110041e0000e103206020980a0510764002c000d45188a900c01e543c1583d81c08a1045103002250164003102460b414002004010500340b9405200d081c80a80b5580c01c240100324000d1007008050003d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 728935728 1250 728934478 728934491
    0x5060903120a02060906060907050a080c1c06150903020604120302011d010c08012c060303250b01090b090f04060e060a0605150c191a01062007050a0504 67
    0x60303600308008580d0400050890b5200c14030140041e45034541203036283c5490003850001040340c0b41905205102e4005034840504185060307404650b06c0c20010600c81041d00200140c00343d521012108141d004d88102c40030030564241442510480910310300e00c000d20050003420300c01a598003040d501520403016040300c03501000d040c01c07405040c082c00c3c1c01204161381ca54a0f40484030640041320102416101c401e003590b030381c1d1600b40140a00032140304040f03098008840080c030441e0004c98200c940102241e0516483d011110782400160840e0f80f0b40740d03c6c00001c0070800004c0750240d40148840e5004000f10010f801c08034900890003401401c540d402c03540000c0c100b144540c002c0e150f08080a0883d0b400e4a850428080200654010f803445951000c82548400b00c9a9048800507010400030f0201054008400441c012004404540c001c84100150b00381402001e0424024440c03a80d0700e403008201d80c5078201c000026001e071480150000c00c02400766403156118881101c00c1940c0c006460b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 728936978 1250 728935728 728935747
    0x51e0a0f050712060b0301140919030c0203161503061410031404050607110102070f020d081b060a0c0c050c01050a1403010f0302030d02061e06120f0d12020408070506 73
    0x52240075003102403e5040183d9200620115500984411034194020000301d0341c0c101347e041c1154012544189d01e82c1c005031704074104003070503080e800b503047c0300c0d0071720010340c41e807039400641030402c51500d00c120b40b111a413041060810140c1104c00704855801d00b04095810003035485100407101142d98068911213112a41180c8294031803249592101c1c0c40c400241050303d002c4d92943c400392a03c1c000a1000c000d0550344403018400c862045502c01000d02984d1010340c00c0c001065100361098030822070901c0aa02e10583c110230341400d040700304001d000c0500d40103a44508580c1400b01c2c2c0000c11020207111800a040000c171141c0800c0c2c00d0030700a48804040008803502107106a82d05117a0401000022b03181150480950980c0d01c224143c543c5445104c0301203954007402c44084d00341c0054103960000403620319031130580200000c0c04c0000111005940f8500d41150104450507a0303010400807142564007007084811450151000e41c5044d252061031551280e0f44d001c0c4600c10740d4000343c035600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 728938228 1250 728936978 728936983
    0x150a080c0f0a020705010e010512010e06040e12030403020721171603030f0f09080423090103111201061514190801140d030f0305180712051e0a0f05 65
    0x251089500c242a42e6001d81100013900c0390901c3c0b1429000c500703040e036041c6080d80100103540c00703601341034074a003050f0b1b00e04884178003000c501901c11b9801640c0c07149414080c220a001c54581110080c25a0340d0340e040c0392070f000b8a0003180381c2c0b103c0c8021648101340038543e4440700207102c8803a00440d011441548401c60b0b603100740306105c4030018034008200501e00705600760300410002c00701c1c820b04000e0070039000541c100307407140c02c4001880f108040209001c015400c541140031044d241c3c1080422410000100c7d0004ca800c1c1c01c02e840500380c01c10203026502d080c80200010032550802800143e1400c080ca144401003010312505110325408015801e01e00320040e258404540000c90030301d90160a4080c0c800d86003800752428200000e04601c00c541040b0340d03580b503086e90507aa48015010000c0d0201c004041c05001c80d11961100340340c11051400411081c0701402280075500034810b0a480c0c42c030704c1c041c1c00855003030084600041203188048007081564030550031103d4182d0f8024140341250 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 728939478 1250 728938228 728938237
    0x30506010908102310030311010605090c04090e0a0302070909110d12081b0403030c150921080f070c020a081006050429010e0f041b0e150a080c 63
    0x128031a061100e1440180f5070041c04054203030b18001d407041040c0d440001000380d4211400400124172020030800240700d100801030354001e902c00010b0280d1501c0000344100026180d00d0f0700341c80e01107800d01010056115100c1c4043e880760051518817070700d58019403502554864058455501c1c02c242041c03051480fa240b048207030080c100b0881402505d044c0b00083c4560707400c040020303c48130002e01000340700c030390100710343c0c103a4070f0114100b9185944c1200c00182c040d8040b00d204200c40024a8090101d000d03a103102807080582d85102c1d00540d490305040a0007083c01c43c100001e0300203111403041d180d55a1744d00315030640380c1445129401c5c00454050100c5502caa102031244c1c4081c04503601517503200c1001e440d41200c1c2440503d448143d0603a40c6007090032481000300c0388640c0c88010307600466103c105030748050a4a00081c4d08940003031300701d030291005100641e0700310f6005407946600035841c1220200445a0568003560480408603500880f14000e085c000c4c280d000c90458080e442c00e0340e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 728940728 1250 728939478 728939489
    0x5040f060905090703120f0c08090a08010c17131a0c09061b06070c052515050702040b0301050c1204230307031728020c010207030507140a0b04030305060109 69
    0x280b00c607081c00350f640355489031540700c140c0301c040224404c219058850741071240b000c0510b55489400305a603444003282503104040c55a4001d00304c100c00281c42ea804e00504403c104039482c0c2c298001c00004150807440c3c7d000348140c41e4101c020381b00c1e20014034802ea020240307801001480f051035582e008403012070320860250315401040420560a06e000c1003101050b24400207054039250784401e41c041c1e91070210514001e00903001403e00380541c81d101c0c806503814100d42204216807a95502014207401200e03010035001800005281040d802c15000d02090402c0a6008010b28900140714107414010742981c9000740011a01042c02e112182082c030180204421940801240c8510075507901c0d0700601c41100460703030700c1d030200c07101f000340d002c540d80b203014403080141c07008524007924480c50007103208025850342c0c203001000e10028240701134480300340b0a45034140d507649107080502105009201905580d40101d10920000381c0c1028202d4205e90325040104071900c0d084016254100e940d0000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 728941978 1250 728940728 728940731
    0x12160b010b0a02010c1407061a100e010212040f0e1905010b04080115031110030e070905041401090c050126040b150d12050c030d090c030210051305040f0609 69
    0x4105078444200500d140354094000308214549042e05035280003100e9030070440b54070280071103c08145207070007158100b40c1c1210741805288101000480d940e89001c0342500007042c507054040e855030100010706103244803180c00e60902e8903107441650000080d000d806032104504011507420700705861100e03804200d02c0000d01c115a1036405040c803039001441240d1840d07080040305941c0001041260f03081d01d800685c0000007511400510800f0700b65008500c0400d995491201000c110034002c1e0005401141c001050b42e041c541410341c8110f4003100110401d914104042d03001441511360326013114401e0800ba0340c040403440c10000b0a03000c014500e161001400100002c00c5004602e041c400c030765504400b4040000c2d41c0500c40f000030341c12030051580c5000c0050748a038501403c09000804c1e150310071603140006d0f90b41c10500303481890004a54455003c4030a0003107142189101074000c603180760050628130b40341e040b4000030209107c0d96005541d5a503400c211600c45810580180460110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 728943228 1250 728941978 728941981
    0x5040b0417161202212e090b06090c030c09040906020403060c02010c0912050312090a1e020306070302090306070c060e070308040302090609010506070318030c03060c0f1112160b 78
    0x1508210800f691204910071342110080b8090904603082c540070310307650710300145142201c15a4640c00280340c0c1011740302e07021802002040a65140c011503124900c10040b2401e1802c041050000c80900075040c480000024010820030031804401d89400c1c180c100c801113486626810054028800d0f50805080c9078209610003a000e50150050740c2202c10ba5950f42d082c09546410214800c03588030f90041c0240c104201c090004881c0f401031070740260340034040d101e4450a03a940c5842081003280c2040038000030880404c10351400307000032a84048107040c15841d240b40340001036100d100050400040c024165018818001c460340401036032804401102c4125450741015000394000c0e200c01c0b0300c19455000043d0f440c0c200404a14100d84009e04a68108025540e041d111000641000c50100440401c0080816480c0b00303400003c0d801480300040e01c0c16004001040c0d18124130340042030080302c20a4417100d1500041040c0070010010030181c0341d40b4800c00d400f440030444540584180001c40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 728944478 1250 728943228 728943239
    0xc0f050a08060a0b0307020c1914061b010c0914040b0d020d1524170d0c080c0604081b0a32011a030f06070c0b0601051c02041505040b041716 62
    0x8442188d00c0d011035a1100708151808646010840d50040d2551a98404d00580860030050b024000810920340c03002030b4422800c0c0f2560841d0301804410b00000c45100040001c0d09e1381c2103800d41e414134217940500141c56000c0100300c0300074000100034000c0041501c600c0c2804852007402330320307000c0340f5018050f42039200340034000342d410166500703000e20b000304000515010079a842c580003803020001d00706100031280241e540d100e001703d051b10f5041041002e003c81543c14403155101e180300c1d1600d10348031500035204e0410307001d9680d60a5000e0b40b00002030008251108120310341c180342d50f030061142c8400b0981404000509581120a0b90b08000b07541d1241100a90505444c3c40c082c1d0448140c181c00e00011a5248400d8070b442000c1040404400c01003000c3c140150b0b84000306050080c44c00b00c8110101c1b02e401940d410304c4010307950100b414401d600c40b09080510041e2180740850820303050a45543c0d01d17220b548148030500d23495440070340d0084002d10011080c50041e414202c01d00b03595a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 728945728 1250 728944478 728944483
    0xf0603010b0a091e050f06090601021603081c23060f090129040f0302040906090f03091712090f040b0a17010c080114010c1e06020c010c0f050a08060a0b030702 70
    0x5102d00c59043d0002542d004095941d100e1140300d03881d080308201b17081e140c1c41c06001c8003290207000302d811405141d80408816004000d90342c01107104140160f503c0413400a001d404000070b0040400c441d0800c14070407076110b031040d5007440d584083c80e6807206944800001a19032026040525004803610b0000500f10017280b03892385181c007a00017503442030740440c18000c04500c124025550540c850100038805414554003c040441c400c40b0009850149600c40c88406a00c8410850019501d000c080c0a1810182040d109020510b0018900b40c07a00002007011030140c000711714080c081c102401450b6583e15080422940700c040c000189580d160001482d03855401040401c05e5070170401c09039071651041d29554121980900c0c907105403402d40b801117511441c1084103130b0b9080d03050100e00c811261a0070017010910b01c601030042e91011084c2005003911010748804080c007030322030308440180b90404111411510700e458012915540c040000c0c640124617040103080800104c20403003900d800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 728946978 1250 728945728 728945741
    0xa0f050105120a02190e03010f05070813060f110c12031608060d021f030b010e01080103030c050c12150f0f040b072604140f1c0c0204020d1506080f0f0603010b0a09 72
    0x7d400a00181070b07890325081c1650030542d10340002440340320005940c2442c22400701409885207802240500c4400084010f56207941c240e91071844000603800707600f039002c21508a00103c0c1c0d44442d4254030348464510300c0c0403103401c1d01205005d00040050381d0750399203001d50900c89070300510280d0b09000c1c903e03400c00c0d1510000d480c0c4000c2403420f08440719960240e10b4000220505a43e43e42c034607030a5940440c2c01102c1c0542c00c4842c1c1c404c2c01c443c15130340e0307943c01111004610b4010080c004000d4215134020381c000044d2882b50003514031000d109601c0380c400102503100e42c04c05e1001c0e5980c1c88002040b0384400c00d0b071803082007924900000254a00b003500c4101e000f207025100f1103005c00200c0126544030892010303503001c943d200490078010340d22050300069441c40c4600f014900310341283c000c82c0603039000049407241c1d65030321118500c42c003585084503800f805003440d2220052600d501c0c0d207118904003810100710b49406200240e00742d902500900d00000002c2d0004c4099950b9640100c0030b01403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 728948228 1250 728946978 728947007
    0xb06040f0902030f15090114040228021b090103110102071505041805061f031107080d050f0912032e090c0c020303180a0e0c090a0f050105120a0219 65
    0x44c13040100d03189846900519201c00001400b0f05402c1e4600301d0740900e282c01903a00c543e00960280905422058000108018407500c3e00441d110f02e002444c000b0300301404889400b014020b140c0e42c0c10000c7d10b42d1300b800b60541b42e01c1461399040d460640c0051345000a0360380941d0000b04015051201c113644100500200d654900c0d8005042e048d0b079030f01e1381c01c1d5001200c40c503400c0070000d0b41f04030110310600201207002d821070800040b141103070420118140d05c031030001d1318000c200042644440c5010300c03400d54003001d80240386100d0b00380b0030300e020344810000a03e0b840045020000c20096569004402042c080910381c4003081861004800c03540c0305244159101180380442c4410501d01510f42a8200d41d07000f4017562a00421242011341045070b0385184fd0040c0342c860020401a44400c2142e00951200d40c4d4543c54003001e10800c03c201c1d0700380e0040c0041007140d1070208400e076044000e590403800c0c134525002e410346c2e80c211070800070700070003141e0882c1c2c0c1704a181030030b00d594100760305110084 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 728949478 1250 728948228 728948251
    0x30901020706270b060a0b070b04020f01080402030607050d0f091b0806131b080a140d0e0109060806031c111006140112180b01060225090b06040f090203 67
    0x8a950320a01c0300c020040c41200d5041d903d100300c00b00000c0c0c4070f00c0301d00d5020b0401003119809640f601d201c4507858210003811940c640380b00d42403100303502d4901021030b0000b1003481c0000103840c113607010903184e442c01752461051040102e240020400c6c141c0198404900703c900422030041281004070344034540c4117030035a40720f440c610003080c0300c0c00200d20f807440741e00e0b1950419078202c2030b540d40d0041031150149800e51104187c2c0c011800781c409109418649015104100c00a15480c10340c50500c00907851202c240b01d4107050918050b41c2042c02501121850705110b2526501c840c00f00f0b041203010310f00802c00060aa02030740b000b03a0041289018a0301c02030843e17452031040c0240700111a407038050080c10341c14050024015610800c2003481000000300c1c0800c0c040d00184e1002d0b0000441102200c00350030040c018040caa5040040b000001e402600c0c142d80c15803e010901d80c0d0000500507520495241c003140301e4a42c40d590b040354028084002c110014594070801e2100030b4209850690100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 728950728 1250 728949478 728949491
    0x16080d082a18311a060904020405060f1902010b03100e0114013203030f070309240314150f0105040b0d020d1d030d0f1d010c0f0207030c0b0f040b030901020706 70
    0x214518440d0100c13004100311024030036901e40301046a65000030b160694401c0d001c02020841d62103030005400b40c100b82d030301c01d661941c80444250610094160b2004110380c904201091665030019a11602003120140001c03c100d60301c50107409071099401d080e82c070010070341c00003600c03000d03c05250701c8040e5042000200b241c3c00070040c07001ca0030302d01602949940248840040b01281c10014200b003482424070841841d070390b0100c070380c0c42103d004184c50314001d8115000c23182d64160003240d001c8200e8130805e1001d0700c3c08500030f40c1d18507202544a8016054455684400d034020400c960142504000c620740320290880c908001c2d40c0040704850001d810141d580342919040d0300c0d950908007882d400b071410306c00a022594000c00340100c04020503030300d480140d003000c814030281742d5004092074004142c0d4400d0007809498294000448001c56001500030008651b441181209a40040403e2035455192102c100d4283c080c0b5005484003180000c00c0c050581300541c014240544039083c144040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 728951978 1250 728950728 728950819
    0x7171b070b06100f120c090806040c0501081302060d0906020904090b06041a0d03271d1008030a050f0c01140906070c0b0106080916080d082a18 63
    0x581c040b1881804c086058410140915010383c0c200d11000f8007940382c1110407540e15041c2c00e180040968041d1641411035400f8005540e00c1035002c3d41c0600d510214000c0d14042d6408a6030754800d01071484c055560f160181d10400145030101d45224100501c00e12040d481c80c1041c0440c60415112140320300c1c07800040b82a10aa07030041561003134001418400d490596032402e5800c0100300c980b0306400592003242d4020710001807072a1000c0c0850103903a000200844244920003500a002034600c402805003c01400d4000411a0101c840c2c030720b806511500940c1c001d51241c00f4560b801d00165085c03100c003017295010801c100d88542c50f004120350054840c0c480542c8e110349d403054094000c0501c24014400c5038022806103402180040407200c00d042000c0082d403d600c8a40c202d0f07401904202c1c0d200058980c0b00d01c0b155042480d45100b480501c540c81003882c111540152202c002610104030083c02c1d02da400b4517540381d40d00140040311400303902e09000c241d1500c05a0680e000394006d03210300c60f4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 728953228 1250 728951978 728951987
    0x105060d050d050c01060f0909030e0f060d1a06120702100c120c0c0f03050a0f11150408120103080d050f0f18030f13050307050907171b070b0610 64
    0xe005801002412000062202c1250a94000b40311401251349408002030f5011144030317080010500103400250103405403400800308000c14400f140320710440c5896204075905d0000b207444403101c01000091060301610144402d50140054a84c00351010542140b503452617640144201000da0949028108100c816021181c0c0c1c0740320f41d400901e020300704040d03c542a42c40a4801241810513243d0112243d4440c0d4030b202111004400082e4003007541a07003a90400c11451108900342480d40e2404c682006031540e400c505030b10900d01c981100041014051900704a42c0350801102000204d07603102c0c01c1040680c0c3c0524180c219181c6440c5c001030034018003d0180c2d0154034419003006494880342c82e200007102c100401c11646000070001303103044a410000900729015540e8484071580d281004042c1081c175290300860040c0002030801041c43c0d480008030741c29810380e5060450740c0d110b6880340181c124140501540300794000518000340032002c1d0813a88604011516503c00c141410002c0700c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 728954478 1250 728953228 728953249
    0x3090f070801140112030e0d0f0b040f21142203030203070c0b0405031009080c010c0801170616050c190503430602070b0c120a1107110a0503010c090503010506 70
    0x10000355055000941074035003030180e48c402602401e050801c4850315264440340f20000d480848681040107120004c21080c0a01440390903217070b192400c0390308103c44003d0161034030049181e020410000d00904100c0300c9520354687c85080d1401c070b01d08581c8030700d000707962503126030401d89500000c03040006034990140200c82c261000030780070b018441044001c1401a02420b001140c003010281b11503c0d4444007446003004a0944c0d5903044c005514000420412100c0c081c0c602c2c56940064041044032060400c1c8980001c59524140350b482c500b600c0018103148600103a08940b141c03121280003440000000380fe44140404c0de0410104808044111859441d116654404400058504003450034a1007001c07114000c0344003525181440d03a402c0440d40c405c55003010880310120300e2241a07851410030542c0420002e0040050b40011003522841c1c1c01910b1008041c1181d170320004140d030300d9031140c2034000c0c100600240480d6915420141281106004050081d0311b410000b50040c505280b266 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 728955728 1250 728954478 728954483
    0x1b120a0e01110703030c0905040e0a06060b07030507020d03090906090516020703051906150b2a15070507140d0e040501050901030825061505010c02011403090f070801140112 76
    0x1c0303142c910f455906a02601021321003c003030103030f41b080000d034136107490141c401c5000d421009000004524682107088600b07941110b80c840109110001c00203410000322440b294044800d8041c00b032440c5400c807190203071908100401c070301b850b2000a02d442190000c5006400109440e904c2400040049075201d000340300180c415400079040035035209080c2c2c2c2c8142e00601aa9001c02d210f140c031000d901d055540b0790f00480c0081c2000070942c5110010319100340c6140401c40780c1c0003801e00a10b40c00380c3c5d911a18006550310260320b1f4040b071703006801041102c03800b82d84881d903400d50280f210038a80d1a1a0000c82c03050228002c1000c4450707a25140c8520750607658024070341030459086483d40c117102c1e0007480c0020b03110b1808054559080d020f0003029005540b04407004146c1c0c100c0f41050801c0080707140c6c4964180045180c00d1801070781c001104150a40c1e0000d5059100c0c2e4981599520702995500d00d0f0344c00f8080c442000c2407000e01900714a1800c035000320071000d5a41e981841100c41da1813020301 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 728956834 1106 728955728 728955761
    0x311131e0605011b0809130e0a02030d03111602030a0804180f0926091503090d050901020a111305070806090c04050d06051b120a0e01 59
    0xd0301e000d8070080c40c1001c81e035520300d9401c41d6451440c500042800c1d102241e4074009440700820007030004e202c1042485901700e0600300301c0e111002058268000c2c010508610120b900074025022150740c0c0114243c600100b1100d16021108107003012607060043d09094404160400050400740a03084012001103420003c0317207003150442140c801c2d07a0341c240100800031640305171120402c0407103442002032a44280c00ca014183c803400c00050740c0300340302641411039050301002441c460070a100855020060103601074900f8060182181d00690103d010040001c00c1e0010000c503c3c08040c0c510b2458021566030003042d15011240c400003e084881088094645042d2403500f00c9141d0398070a14250400004c500040c00700e180c003800e9651198085001d1034003446004280c140203680c81c80d182c1c8140128414124019036030780c2001c0b42005401030380b403041032081081401403801e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 728776978 728956834 := by
  have h0 := BRFrame.cov_init 728776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 728776978 ≤ n) (h2 : n < 728956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
