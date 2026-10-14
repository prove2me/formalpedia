-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1921
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:09:36.696983+00:00
-- url     : https://prove2.me/submissions/2a6617cf-d771-4696-95ef-bda5841e9103

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 345323741 ≤ n < 345503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 345324991 1250 345323741 345323749
    0x304050a09050a1406010c021507050d020322180504020f060f04090b060c070e130c0b1c0506010f030b03010213090b0901080f03040306021815041d010f031202030f0a0305070305010e0402 82
    0xe20b400d2301101e80302a241c809400b01d142034441c013030380541940903d202c1c5985030340d0000000c124170340741c1c0354486a900041c6540096541c0490107101d040d41601480099007540300c3e00301c0394010b400200001029200200010081c0d409686da446c010324010508100c14070280c825158020b0055548a1901241c0c103449512000c1074007503195540306210104101030030407100b11000e2075010300301c3c80c07010b0340b141011081900016880400d00801685034940c0580d035009240c02001c0607110362940c01420780b4198068584201170300c0d0036650a204124604c45092624002020440c0e0005200780c4100c0a020819005800c1400710f41d100d90190b420110001003254101e82e00b00700010b071a54100c170f440b406040d04818509030b1000c84000d5541198071604020002c8035003402d602001100d0b480c0720b5021030b03803007407089810f909000403007007001ca2100030038002030341c3c05803054030318002e03038802c4000103030b08101e0f80480001d5032a810000c03016014454075000d4030b100c0b03604108900d0079500007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 345326241 1250 345324991 345325007
    0x1e06140712021203040b04020f180106030b030312040809090c03010b0f0a030f1409010509010c02070b161704050f0d050d030c1b030804060b0a05060703110304050a09050a140601 78
    0x41c01c4218844003806110b1003030007026805103007000042c0e038a0800c0e042c200d580ca075040c0d0313040c0e00c84d6162001c00c0256141c40341405421420320300c007000c21a840c05000790006c20040d100c99800d0302007002140c111030300c541072480c822403142804580b68101c0a06010103030500811805240700100018010000740c003060b101a40703008030495544403a0a030040300540000c0001c104036a0400e1911004200b141e0b03080381c49010704a000708265501c1343c180a080c7c0e00b0480702500560404441031040e214030900500d08000c00c91942c01c0d0005d0b0b556580b000e44008241503000b85400490148918508031801204480080b9111142d000c05500c40d01e03101d40c4000d100c9414190b5895698240d036020f0405084015811942c00310400600d050180c5560800c81d81124a03900d400d0400d1020302e440c40c40c01058803005480d2034200240c907907080e240518004c001000d64441403100059681d617504602c40a007602e0340d40071605052184030700003038071148404410003a5000d0100403c03a42d0003100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 345327491 1250 345326241 345326243
    0x90206040e07120501081c02071d13080309030a0e0402030106090605070203070b0d1d010e21040e040f02040c020706080606090d02040c030e0609070506120703020c01061e061407 78
    0x1407424948500c0380a89040c07503900000700d2000c0c03c0c0000081c42a8011501c90021581b20051800e44940414104d80b00c10f00e40c040c54029200e4507000202c084152100c11342e2100188042c00b0811030641c84e44162900119201b4103260700005000150f941d000002e247c2c0040c044d41c0c1941107505040d005840b0040d240100410010007007040000d550703007008480c0c0103004440c081c0d9910701d0380d40c40360409015510707404150314403241c05442c001803051003880d81d14800380000c0c08000346592002074515084200300300e919030081c00301142520360750449034043e901c21b422001110303402d4030502040c2c60080d0031000554000f218208410b981102d4400d9101500703d5105685d44c025100080c144041200b000c5c0d00f15182c007440380f442c035400d50302c00e41281c1c1541707040320020756800900c00d969980368002e0f0f0b07130041414000c0710040840c54103107540110030b508000d420310079402806421581c0603031103821001e544070040590b04840200000103806540303440781e005a5412101081d03171151440c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 345328741 1250 345327491 345327509
    0x10f0c0b0601030507180305070611030f04060302071b2702120115110a0c05190b07300f0e01020106060c0b0c16050105100509060306040f03020f070e0f090109020604 73
    0x5c0880b0700c1750712884007040c110300751071b15002c4e12403c16558441144c0214800300d55440385440c406080081602c3c1c54001c07020b44e9514145c200007049000c3c0d0040e140c22508501010320192140d528807010300080c0c4202608000c0852550056185104884a100d000e10384104140c858018203107400c2c40c15541d0203035900083e003003c010121098068404032100d20b004141c040710811032191100c40844030121100462440103d22640c40b4601e548500030340404200514130020341502848201c400700c6081c0f00c042c0010304a688078404445149080c000341e507001209140e5a0440d1041c0c0c090762080c802002070300e00700b4a02a1011a04840140130009541d0000b454000300d0700850b00548104020350101030251328089020b80070544640e85412040035000c42d2074107050425030705c81d4400500a180544071f50321384a041d40a00c1100747c085000e000680c080000003004010005c0594034207020351031501241d0300d10007407800f42a201081e41806003010250b6990015581a640055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 345329991 1250 345328741 345328751
    0x60118080604230f0601050f1215060f061b06010e070e010c1b0f09060914131110020a110f030319120908090414040b010603110d06080c010f0c0b060103 67
    0x19011805405646685184910684c514200d00d0040820003d0485905646203070090742c5600c2040070142500482000039030108040e41c115000b801d290f03135006100503000500204200001c45c2595121803400ea81d042c400f425105001c420401c10f040c01040500846005400c0c41800100986000741c030050400c140e0110000030311181001c4e18cc0e1184001c0300d03070501d590b40c07a5401002010b007440384c0d140c52031402c1000517558456004028003801c1c824101e246c0d0b680c482030102d954500448007901d15810402c4078030f54540340c015a460140070942c0007090074080f9491b108850000851001e802180f81c2c01260405480000540e01ca060a00340d04034100b2000b01d0003151180039500e21600b82900b45403503c0d042c06071000c006c140e520016103050004008440710000400406c0d03c0007080d04c5104030042000c0b91195224080c4544104000381c41c10308440410360555107550842111500070440c050394640e00213415880e00d02250505041090481e101c2c4a20860002c28680c1455210 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 345331241 1250 345329991 345330023
    0x21305190905070e1003050706020712080a031806060906140d121701030b010303110105041109060f130c0807020a0b07032c01061a040509060402090f100206060118080604 75
    0x240b00b510b02514032031000100501c5c00304001449941d4034402a0340074000c2500c0400e85910200342c10f401c0d10010804020000d2944d500d02d401640480400420140e0319a400e00d209170000518030340b6203006100102d012400c0c4007a034011544a507000e041e40056012a4090503140d00301c000d10420703080240094078650081007a6602c03100000303205400316407400040204814a00d02d181601e00235510b00115a605c1c0b0f4010f401c0329801e40f009031101000007000c907501e14107000d00d0366225402034882c004803034003180170075501e1045500b00309500e51540f0007200d01039030100c0460307445078540c4018a40008030b0344540b0011100a42800c08040c0c03a0000303002c4002c0d604888182004941c0c040002c1c0020107102d040c000c00b150300500010b034024041c6a1070244105080d074041d51401062200c0035264441040000c1d44400d83d0103403c600c030b14901c0e10881d0303102c040340001000e07d078001c1c100300d14001c170004000d06c000d00080a550f001403481230001c0800010f030a68003039403080051070038502d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 345332491 1250 345331241 345331243
    0xf0706021515030d020a030f0c080d050403091208071406010e0a0209030705130c080c0c100b0d050a0b160302070f140c09090a030e04050f070f0509061204021305190905 74
    0x29403034110f40521400c48621581903002480100c2140243d4803c0000d0390802000c440382041440050050352042c41242e080304260340c400c40d0014403e041405103541d03180500b101c0300b007040b1402e0b14640800f1441006002d02003100300c0c1a004000068595581040010b14861002400701008075078045040c02541c0c8042065102424004001449490001c503c06001d0448092500c002800640104501c0d1442e0010782d1600c10409014162425070b00a0400052031600c80d07203036200580020440100e0400c1c44030340540d074080c142c00403c0d1f1030b0105c502030500d480d034540003003094810400700001c5400000d284102561169211280e102c01c540e041d0b00c0e00b0207680105501940c15010b02411010024a50b42c480784242c4450302c0c105e881c2e80800c002c0b51000c80b80014804083e900050a9a1040c88a0318102e0340505140f828070141b41d0100394580c0000d1101411701c800d26050109601e1320107444a0761660035482404907280441140070034140003045c8502d00c503200e0803a0420000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 345333741 1250 345332491 345332521
    0x111060f0c0706200d0f06030b07270e160c02150f1c051b09060301062001050a020a03050a020922090b0c070b2208090d20030f07060215 60
    0x300c010040c05503440140d13000b591984801800c81c0b0240c900807407011014030b02e000e280c044030342042c40d20607150b80c1c020080c0c03620b44140e1400e000c08174410821000380491882a03102600f05107003d480c41d0300d001c14006803c01c00c03080c0c0c54024007041d84040001a683c1c1c9400f8000e0400c1100845e8503094140c000d03c66034050030455003900910f140401030340342d5140c3d00c101e00c10031035004240c0d0305032081101d81e1182d01c90310446640191082005200c2140642a060400700303d41d0030800d0349468840a10303003152816501181103a8001802500c015810301a00e5082191004114540750840e030000b60006903c0800c50b10000c80501011b8066461754001e0614540051518446140000700801c2c180c0c444442120204c01140c0802c102940140c0603082409100842d86ca43c40529102c0c0c84554100070040d9500c81811010b00c000120764103c0200004011011401c03840c1044040505161402c0d03c80752895001910400c000b41d80021303500b114103844040e206c400e45030301d1100c084d504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 345334991 1250 345333741 345333761
    0xa0206010806012405190e040501120305040e060a030b0a0e150903120705130303020102120c13090207060b1c03090915090b040b0d0b01060e060a050f09010903060c05090111060f0c0706 81
    0x1150000003100e410707001400c1c480004001c81d4104014bc0e2501d0300c1c800d0b408064640600003a80900c0140b0500840d019401c1c0c11650080c0181213542c1e070703561a46100b01c0200e42c990300d515203e60180c51070200c104404082c01c440c06040700c4076490402441a5a405544020100384005801040c9920b00620031980890f480c0302c4c43c59400e5480c5c0c03d010b4080e47c40903440b40500744065000444e0301002e6419034108030410080080c803680703004428800794001410070b803184c6e80c3d5991408050fa0b0380002c2060301c04a0700340d4070359048045044c00780c01040c803548960021420102030501440192945200f5513a51300700c0000e403034008034007180040404c0c0c8840e50308004004012428014044441c904942e45c6a844a101032001802c1c41228010344601501207101031002031258003900c2e010b0010b41d8018034200003101e58030746908003a200c403c010300001c04c0300058000c00c2564001190102901004020206e078145209840024800284081c44400000c54260204050341e0003041c910 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 345336241 1250 345334991 345335017
    0x4020a05060d09050c04050103030f11101521111c020303030108010b1507050d0c08071a090c0301090f1209091103010501030e0f2a0a08030a0206010806012405 70
    0xc2c6500c04a0034000340b0283c041500c007486048603004c00c514090143ea41602d9240c0c2d100c003881411450207403400341040c85160058000c0f40c4000501c1d01c5188200c450a505c0c00c40840600340c94940080b4081100c8031a40c20721040b5542104045107a810101458a9003a640b0f012041542d82c0d03142004000c08000035850f0100000000e034140c1c054000c001c03015805c6545020014051a0b02c41240c8282040106690020310300c0c01c800600800d259007102d40203081c00c038a44840c554400420403040d50300c0c4000300c1d05060174845008020042c1d645469410b030000c101c42141d0703450f4480381c80f028410080031060751104071a0380b0740c41845031100034480550144842e03000c2603503200441c0c200b4010a40084e20302860980c030321500003541000000c0181c0030300b80220003200c40c203204622000001c0484903542c0c00701c001c5c9071240c0359240e0013440f0000203140c9400c0d103200300a09059040e4407240c0c0640c890401801041585240d0200d00748410300c140014207070341442900c0314018804141c3d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 345337491 1250 345336241 345336247
    0x7090b1b0a26030f0708060604050d050604201f1403040308010501020c090c09040b0604051c1506030302031204020117010e0612012d0e061e0f04080304020904020a0506 74
    0x20800c40c0888049407030b6950080940000b03100c480c0580c0d600084035600c400740c14031800300d01054001e012950304948003130b1041b803505407207002082c6044a00c2e101107819602041c00c00051011060007800c1841d01d24076113055032107440c400258130340b2100c02503d0300c030b9001c60300006103140980405040d00c282c00d60515245d03d418103020780354040901c90240540031700810501640b0b8090419885103003013681c80d03801d200e08202404020b0201012aa0300400d04100105855446810550302c218008465000e040711900d4906000c0708035071600301c0d0a50400000f40002600030090b120039944003210101e032603a860004940070500b01c4442c0419541001c0003080c07501000441ca4460082620001e440030300303500100d801c84c1c0c1c541585402010003c4420080c005d0041e8940c4000410343e000800c5122880480b60f04007442901e501d6005146041c546000b0903080382115441204950700d10250f10b002d0f101c1c140c0b10310004000911030285030000800b19a280302d50840a0880948100c0d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 345338741 1250 345337491 345337493
    0x2090a0f050103051c020606061206010207030b010f140d030906120908030c0304120e010905060c120d0c020714010f0503040212010603030806121f0905100c02100606020607090b1b0a 80
    0x80c5491035030b2a18017000d1804950822079500000d5800c0c081d16004c1c10140c9080001a40c418280c1c10141220381140130301d08000000c43c0d0b070501154007800104458480c010701e006690a8249903807141079000760140742801c0042034210444604481b403504144000d48070100d0828000c101880c0024022100441403140c003a040402551040c1d2042200710070940c07880c1d03410b84502030803988550010f100c044c8240114100745010344103140b0140126042c00f40752034090107003600030282c0180d40c550b964130112413441c0d0412810004218060055036140c030050f0008062260009540040c08000800b1504540b40c89564280c80e81d4014000c001044e12460000e1280409954861249940b01c110500c241004151200310012107541000030000c846a03582c054050910306507014082c038440305220601ca400b4618060f18668003805080b1004007044040311181d400410456100e034080020395900000101c0560303102c4c00d400f85e02c50202e140b41d4010800c10800c040d58034010401c25170 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 345339991 1250 345338741 345338743
    0x309070f0801090b070305060904060f0b0301060801050403180f0b03040305070803190506042d020c190606060908031803030d111905070f0b10031e0c0806090a02090a0f05010305 78
    0x20f44a500c121030340e4405444e0b11100324295401540c00560050507200030038009455135101c010b89220304840441c100d0030540c0003c0c2141c4070369202034001d9448400304001c140c0e10450090105c03034000d1000300f003242400032b403501d0003090740103e17146100004080f8051500410a50395550b0b40006040e56a141844490b00c940c1d405410b86010141040041422480e040c00b500640d1400307034029816071075a8a0039030281c015014441c08000740d003009800110001840910029000c0407503941c1800700c0d03403418004490b41d90f40800108100031006009c8040302004561003401c032110904c8102ca8000000b0341144a1001c00c02d015629187c2860048500b03800509101405032100c0c0b4070401c544071b07040c3d50f5032054600c01482c40d4012042e200020304038903981c540081182108008180e1030307a50341214a12100c04103450310000f07046000c1048040320500d0040e180c030300041c140c40d0074a00c0c4455070310803c960009204050040001e201140382d544081181c1c2c0c48050280075a503034a04102d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 345341241 1250 345339991 345340001
    0x2190f140c0f1c0e150408060915060d0c05010503100b0301080109170723010213170d03090c050d0303020d05071e03090f060504110d0605060a080601080d050309070f0801 75
    0x450090090000c02141c200589038503c0d8400f80070348444038103041c80801c22003070f1284030ba030000c080e00b4188408207200d1820800244108244001083d800843d83c007015180703031000f03041d07911400103140b0920009148181803401c941c42801d16a071282c4921174054020b0b485a04a800c4104d408000001c54520541080320300e80d02540100c0780320b0483d14004c08452245410203448045920b030320f900e0350840100081c108035540000182032088043c1422801c0c0303c1540052034101071041c426100b502d090040034100c02c1c2c07a05003081104851795420307072030282e14880da0b0f104d11140e00f030b80d100389800f94045580381c04500004000c540341c03c0101608100d80401e200c02944541c082005000b4024030030003c1564000d03440790f018800b582c2e607200203010020001c0300c8024021050614588074480c1e01c2030704900c5844045101e250120070321094007100d074403180042d88035200400142c0004121350304041c581d490131958903511000b1503442e154241d40b1007417039100da00c013000403d80c40640c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 345342491 1250 345341241 345341263
    0x131a030f0115080303040b0c03070908100c090801020a090311120a05070905010e0c0403060b0a150c05010b011b020f040e1e06010b0a0e130b06040b0403060501050402190f140c 77
    0x42c145031907141c0a100f541c03808201c4000f0441401e4001194a45041501842c2d100241c1c1c0741046a01da1540601c0c6c1c00c20100ca0800c50066446a0b90140086d81088c59a0003521b0204001c508203c102c5e5801815141c144c800907040100e003680d036a6094403224510001100c0000840311900054070b4110f9035403030070f4803032036000a02d840000702d04070300b500d0340481c09aa4005801c6003402e045403100001810810300307141c0d000361030b0320340081d408401c028842140221510341d004622501e0510600b9181040500703410480c141c418030712003224860312055150b030181d8040842003030203804100145950b0180203100d2054660064000e030309403040790001c108150955465980c1c41d1341d054500d0140081c5035000c104815a0180076040c0810032340c0410300121000b141021041e008200a540950480144140009418028000d00c1d02582e401441c007a1401c500c1c001d21200403045011b0b04c0e410b400200408410200401d5100340c80c15014042541c100e55550b90344140060340c1c41e030304103e07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 345343741 1250 345342491 345342521
    0x6240b0306100201020304121107030b01060c020112020c0304120f02090f070207050315180c0405090307021813020607050a0515041b03050d141306170a02030105131a030f01 76
    0x5550b0031951040c000e80340500e900620f8005d0444042d00b0070703a8001e00030044802c541c402c00340b000020843d51800203008080c180c0b03590145400ca070000400200c803402d883c2c2d41882c0100324014451800004850846038401c00800029040b845c0101e034541040c000030b5840340e14402440b01512090140351b009618580072146042e9a07001811b0725071701040b507001c001103050310000741c803543c50410000d504040c00c000d85000400810004007200d209444020965001250709401c504146000d00074409400040d0781d1107141c0444803c0c80d1200c0700768001d004040c00f141090400c0400c02c40e00c0303d07440d440400d4807050001d1078080700f400001207030281c40b03401c981404a202c5118268404d01a25000000343c0038080c0c0024082d102c4442c45002c1845034041002039440b030841950403c0d010f8070050b0f4425080f803400300c41e5007003049400b4001100d01481040100031903070310031030703418541130170317004013180d65459017800e00440e511900c8026003600402103100071110065100e0159003035000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 345344991 1250 345343741 345343759
    0x6012705090601061101050c03041203181202010e01050c09041e090f2f0103150f080a03180b0904050604140a050f07030e060105040e030f041403010b04020a050706240b0306 76
    0x165103407d1350004e4440f521b414504002140100341c2d00302c02580d0800080c1804030340c001510300c5044914449110035a2080c040410003040f0544c2800f6004414646100a0116007408010051280718030307403c46108580d81c074a201703076444105003801000441d030042001168a81c0c108650a035180c0c440c101c0740c41410b29224004030000d40700960b028480c41c0342c0c600d00702e400d140064008140c001141c410130346c2c0e12140042c503442c0540d180d20240140c50301031b104400013450040c2c03002c23482489407220192810030601c458100341050702c404a034110380116441d00c1d003601040043ca610358101e0880c4076407a0030000760511070b4220340e010f41108007800c0e0b42552070720030840840308100d03c40c45d0355800210040010b40303441d400c00c2481030703008800d423440c146025500d0340780c99100e43d00c120361900000700d242100345400e02c142e52414100390380c01c3d0300c3c24039403d000500c107108640e0001e00c1745070381e8041e50804101440c054201540d41c2d407408020740c0d403a0303802e11017542c0084801c6407045200c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 345346241 1250 345344991 345345017
    0x230301110d0606020c011e08042105190c080a0807030617030c070f05060403060203060406050d140105070f080106030c0e031608060604020f0412080f030a0902031c020601270509060106 81
    0x541c0a40d000da411060880804c01c91f41e000840300080e000d007003641d01031208126903d0707100400c0b6401804050030344079240cae41d02c00908401112648001441d040c408640c01d10004500c1090440c0d0001880d460800080d40d42d22000740d00500960700300c0d0081003415107400503a800d00200401d00506030004440d0b0340b50390381c5018510384003a4016960800424401000018010b401968111000070700102d520764450000c0342c0f48818043d07007901d0401c4011081c0e032044a0a00c01c0303642281325407034840104402c11002918891042c071466041642c1c4401d031010344d07885036030072181c5101e0080654002c4400078525015401c0a801100700780d001d10340100d0101d10703041c421100f190107203640c5142441d2800941081041c0c10140544410f0010032080d90b221164000a620034420684009a54003050052600e00300b50380c0c660f40ac040c0b090040d24a1881c3e00083c4c001d0440344580c1d030340b01848951040c168041000c1e101120304490400d424130802180104405040c1c645a6a5039010480300e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 345347491 1250 345346241 345346247
    0x17100602070b03090f073804051302070b0a0b12061b09033f042d09020310241707020f03040e07030c05070b0406020315031c18230301110d0606020c01 66
    0xb5052008105100803c41040b15051000b20764440ac12481001030a00c4d0f000c0e00c444c04030720340484615108a80d1a0f401c0c10440c90301c007658504035800ca00091003540b030504002910708004001c034021105001c105440caa42d400c01000c0c901115000200e0945075180400d0400501000303010256000c6000085440104080644003110005e040c2d1050880c1071b000840ea41d40c50b4a001612880209000407850088034002140640303489020740052a1070070103022044180340c402c2c401daa6201c0208504c1156101803042000c03c074000090f0b0107522580c006a00e40a00e240e0b01200034040401c0000d80240d00307800451003552161410b0046801903c0d0464aa11030b1200003007a2000e01c03000308010074420350245a110fa80b1071403040c030314614280081e02c0e05d840c0001400500d0414088802c00992042240c5e500700e10f10710410813031a080260101e0b0a19510411180c0d020070641c030240d00d9902500000c5414035000140d07a81e401c4502510b1000e4000d50040074058400c201e8143c40d5944 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 345348741 1250 345347491 345347579
    0x105070f020a0b06090702030c03030910050a09020f09070509040e03070209060d030804170904060306020c0d0509030706031e06030c080d050a0503070f0c050d17100602070b03090f07 80
    0x580a400c03940984c2d140703000c000c2007000c007802c5401144004e01c41d0700d4402d88208020b41c010200d102c010310f9000d51070507a20b4103840c030080000d8176075030030b220700380b40141c071045c004c20703c1080c0480384c00f181a0f59061084a00e40034084509910a003401140c00301150044018410b50b8000c0ea82c0000079500c130403d01800228003800180060001e00c006004154000100703118001c02e07420b203e1602003084001004e948445d001550700e1940001c081481581c1080700382a4125603041040c100040c01001070b8546c0b480f4465041450780320740b9841f480001c2400e0903a14003144081c00c112841e21380c1000544495213004075200da200304620207001c680550143d400103181e0343e9415145941302d14007100d640c8a051414028014100004800182c00b40a0034a040d030107641c0744095403002d612241c1c180400940003004490752000e00707224459000c02c0c3d80003030340e03686015984d80c3e882e0700c1d50191408040c140d000368070303000b030040c042082e400c1c500c07600310035030030164850301285260005c5c202001d0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 345349991 1250 345348741 345348743
    0x609080d2f160606032405070804110d060605060708041518030303090819030c0e120604110d0b01121a060d02010e0105040806010906031208090a030c110301020a020105070f020a 78
    0xc074140114008002c2050001803064402c04011544954940c1c0e485000c0c2d1685900c41c6240b15090143c0c11180c0241c480c46a22110b245800c010908207511050300042101607510302075008044007805014030b54101034024a000b428080d23070f0348011b0828480d15001360240c44100b1540c0107562614910481070442c082408190040003075213035030740590051240d51421a1012000e0041e904204501c082d03a01c0c90522070340b008108081c9841c0000c141c9000c95420718403070190030700c042c05020070024100b58400d9000201040c101d0b80040020240081c0b10001002d6603802e90010480c4030b00312440721851031141108c0304848071080c40c00c10007800c044514079002020303103c061001d5031040d0268540800d040c10514a0252150072150820f0426000601240c0d118841002080240304250070b04074102e150007c05810080e05003611801001405070030030900303000c100280711016450707051540008008540e20150b00d4400303800380804464841c007044400030890b40160011620f18071a03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 345351241 1250 345349991 345350081
    0x702060103150522050c092d060d140715031b0e120312091005010608010911120103150b030601050102121c0e030304122a0609080d 58
    0x10010b040461801414010504142c125280501e8a0804803011504100c1801400a01150301045042c494407401c00b41c0080350341c1f8140c084035480c0c158880c2c080e03080d1201098060b134168840034001000c01c1241c41c4003402042c96a10302030521100081d000044032841c40341160040085142074007142d52203003018401d201c8010303091030074a12410340801c010078010700207042c00c0c0f60061460b00d140c1105d1202003541440e00c09000c0e44505c100068545058440d40510007981410b200620f00d00d41031284804c441d443d000b44510111400d0240d0f031a4510300074003030352103603984d0805001300c020342600d1221042c9040c03c800450708012914905880040c2c000706131001c1d104460441e40c2c0c0c4048080f038081212142240001c88035400303045610f80c010702c025030712810203042c03001915400c001540b080c40180e000783c00721000d900b0020f0308060314000150b41d0040d41401d04e5009490790260041400e074001a00c0303c0c0742c104940c401c3c1c82640000b0400000900c0103126400390944125402c0c40f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 345352491 1250 345351241 345351263
    0x70c080a020604090c0216260604020a0e040f080f12101a0d090f060204081c020a0f050a0b0109020a030e0c09010905090a14100507180b0f1c0605090702060103 70
    0x10700703420440c0900b17054411150800d2142c01d44000f80c0c1215001148650303060300c0c05031000c1031042d50102082c449030b400340049080c13950024031406650321402405c2003c41c030016090014401c040c0010f503400803186552a50064403a10265100c103642084100c0c90101007441e00d54088244000c0d01c2c0d0402e9030140066840e04c02c101b050b04a0100404140d4903150440006200068880401880b0360130158885041142040c01c0004545040500340a4440c8161826030b000421060680d005949001c41030316504040b0300b840312444d0090404400b0000008031554254010b02d41d801c1195400c00c0303000c900304d203020703141e080b61300c0010391102012005109a100e507601542d008616442107922110b100c1d9205400c1182003000c2c003120360040c501c1001070413014040c0e2917101059290401d44c20102290b61b041c41400d5001d0481e021101007000d5007485408000c9440a4109070a108a504448854440500100c1c0129402400e05001054007580005003040c141c03640301c03141d000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 345353741 1250 345352491 345352499
    0x6040611160602130306020408030301050f09100302060a11060709060e030106030803180304030b0906070e04141f081f1a0306010308130b03270c01020a0f020409080f070c080a020604 80
    0x11350000400070706069121140000001d099200800040030b0340030245880b0362510301049544109039591900656000c41049002400d8081c0607050f01c0c1d044030415114130710103201311801c164401080e07140d48240c005011502e600b1040180c00c64415548040390003030030304145801c4e190588801001108107101090801008001d1340700807520341c2003147d05013a0b0b00c0d1140c2c02e41c445c064500c2207858018400303008010307500075100094a0b905541c20b1003d803628401101141c28001c01030202c468682804400301d41c04100c07180c005040354411074006400e0300107141c0b840c00040d035030f1000300c0f0b140070b0200300310240c07240205000c140001c000d000c0e40c0c1e1954480c030000c1c0d0301c0070459141e00007129001091040c41c420107140a200280e0301100900341144c0700d902d00071014250b83c1c046610406400c100c1d40c3e400540c41e00c9450313000054044d000110300c01310b40500130242d8014210b8030040b8000071070324001c00203044141e0042c11900383c640e56403900f02d51195801400650800c1c0100300900c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 345354991 1250 345353741 345353753
    0x80705060615090f06072a050102010b0607031b02060408490311030f011d01080601140409150b030d0305010e042d0309141503180a080307020604061116 67
    0x10034601d0060251490f04c02d840d65040c41001d509100500d03a100200d045881c040b4007c610000608800c0c00200030500040001403064058064001c08010040441d0b06440004016510540750f001d030080b034a541e210310703102c0d072079465a07400e405001d80b00d0b1103131440c00640c489000d104600070209445000400c5d0042d1512103402c0e0303240380103042c2c030b66094100311b0302c221000313610400c0f03007512028542d414215403180c008a62950b01943c0c0a0303103801030103503860100d030160449018085508404080c00081406801121009446c1c1d4451507581b03c42640d01c0e40140c40350341000c0703083d00d072808030390417003601180d000380181058100e0090019000916030b80703180c404600512504400c5070f03031303240c2800490030701c0080440000d42d00038400c001907408001e0000450030129076038004c0d002402e0fa803a40500000305184103044001c6480315201e0030500c04226070940040400780c1c0c0b8503145502a54070f031000c0e90b04070398082c5000340d24003000c40e6135000d4819000c8007510030500d02459407101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 345356241 1250 345354991 345355009
    0xa11091e0102031201030c0f050603101404140405010f0b1206040f061d0705130204060507020415030f032303160f1806030515010c020d0807061808070506061509 71
    0x5042d440100140b201001c14151180d00071445411038541581c00d1002280c5081120342c00b03d80500414000e0003c1b40b00c9403400c880a856100a030b078102e564081c4e00007000f86c0041c0d0400b1030406200170501c0140300041d0015091522055030074424052039000f400410f001941808189810600120b000112403110005405000324030110b8120803118000c08040d5018040c4089a8004039041145040030503a00d2021580040304504192030124003038154854440d00910070f503526549080030350f4689540a001d190068a8115442c10600e4003074402c00c0b649155031140d00944501c5035142004104481c8a1001001003030035540740300901707131a500910702c041c0c2c044c40307940c25241c0f01200c418030294000384455034001c5014103103204198940542e000410781048649410b00015848404294644503400030740c03141c1e10032003400c0020041806540c64161424414800c205001c500c901802c3c01d14000d40698003242c84003800c20912110910345c0303074030694042c03103507100718a094841 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 345357491 1250 345356241 345356299
    0x1903110a050a0612150905070804050d08220224030406060b18040b041d28080a0f1202030a020c0d0903020a1206090203032d040506180f0d030201050a1109 68
    0x3045c0c0c43c0c15200d200c0c100507034004482050004060784108814464100402c6100d0883e904041d0700380c0c1480c0c0a6024000d04140f8100c00d0584080380070300464840100385051007102c03505289203141c81605c81080d50740155002d90b61142003d90118800c81f0324402c603882052881094440181042c1c144006050900b5050b58416030700e0991100c10703100d00c24503006007507910025200549107070104004480e443d03104241d941d658a050100010a084100c46011480741458031600041400031251807025400b490740d180c0c0080284041484913801a2100550250076240000c512890842e4903048900c0041d5010050740401c000301e50904200000650142402082000e000d030003191659219000f900c464036000c004040145100e1050180c900500280b020310302460310b4002903c5001d01c000300340100d80c1c40c1f80403101641e60301d4100240060043c00c0e25046951504000c0e009080803030301c401c00380d4248601400f0000d102c40c1290404540140031841001140d1039000d082e50031001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 345358741 1250 345357491 345357521
    0x215100f0603110721030e03070503030403030b1201090b013305130902070b1506040b07020603071e020708010606030b011b020307031403090102010b0414151903110a050a0612 77
    0x13003c0d4010a0040c00e1422040e4030070400700702c803130402800c01400c54140048401d02604180001c200055010045030b420503018900480d100b81003030b00203151010800c1d0100e60710b600e0000c3c82030802275542000c50407903074000900c41040d42d031000032600121030102002c0c10715140c042d415174014050b40144c241071071907281b5921400d840d01000701c12a441381d101603481e0f00090b410000124221181503080800550307086040500d0070024800717034055841c3c000e11904020000912480c801d6501280784d288182d40d10540c1440386101030f40390f41c481c0c00b03030031099401c12101041860181c081e100b2900750680da024600b4135840d0000b40c850204250485e454000c80400102240d0a40e241d085100c00c0b0501440d0307640030384d038006400c4950b4003200d03600860419902140d00e4001289907940a10750482c00b0790b034041031310300090f41040d015040260304052180b01005200c01b131140e2403203010081d5454000030f5181c00400000d2000f901c10080082c3c030b03060007400307580070301d030090418016411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 345359991 1250 345358741 345358747
    0x10c0f05120c010f180c061d06030c070201080a0e10050405031603090815061f020a0b1f052e0302070606060c050c0a0b03010b070305090405070215100f060311 70
    0x4880003010382e10105003182d1581d1038100400112040380b082c007002e004142d80c40500a911940c3c0e0103200d002d00e00c80c00d818402518a403480807420200f1821101d14001d14440c0e4a2070f003a020b091036900a450700303a0004040e100040e0041405204040103c04503200414035101080301c03450107000014401c8545c1d000912002021858440c000d14007e0311039107a5080340350074480c1c01480c292040742c040d804480444c0a002960b201d205816000014061505007500900070050345461440c0e078000709040050f50400c1001e94903184291044952040c4102c03415564000b08641501c2080c1c0040c003079411010756481126182d170b600c0022040c1303810b0260401e0550746a01c81240c015034080c402103084044400104041444414084003044500b51070031410000513200d1030005008036038070b824002078440306240c050300c00c0d100c03020710007807041c4014a0178110094941d00c00b11600c0c4102c0040308017003250407055003040b9095880c1c4c1c1b194490000e203055002c0300602204184006982020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 345361241 1250 345359991 345360013
    0x1c030509030106030f03110303060f150c06180705030303160305180f030301061106090a17040506030a0c200c040b0d0f0b07120207150504020406120629010c0f05 71
    0x38021000151700070b8504103800700c880d0a02401c000e000b04504103c6400800030011030781e4074100114650780058490314a00400004e0070705c001d10030054804014400c000070031051301e6001100300100c120500540b840c455a0754140b660340e00003581c2410190949a401900e146d00c25444140d018040c6078503400c03680e00c8600312038104000c0361104e800e59080000140421500030f29000c0210a10400402c0c00e4a025412261242080d81008200001d4084486440d11020081d1005007000404c003a0380c5c1d061210000c00180000308001002c10240803641c815201c1c40c1c80d0300351101400c075001d03015080b0000708100003032141d03900c007690000e807030a40c00c804a092105182d0500c0d1040e1504011070030041c00103000c14003941c02280d111801001048001000e030420412258000c10020900b80c0702e40c40050080e000f10f400c0b02126410540c041000c0c002c1720741044401044040d40841403c000c0c070142c161020300c494076140400c5000003402d00164003045015031281c0034105441008043c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 345362491 1250 345361241 345361243
    0x40b0301060308030114270901050f070e0d080d0606030e0708150a0209181501021c0c14030705010c0206041703011208071704090e120403030212030709030204022b05061c03050903 79
    0x1c042d852084000c1f9101c01c015030000c0c24824160001d0320a1110301242c40e141030028010303045000c550340140040c001c0130b41000440025110b5030000c4081c10b01c505a20303228010002c000202c150b01c0a031107001c600140700c0030042402e1905001190803101640e507000c0001010758030442116400004207200194000541c080c07a60241c5d0f50108113101c00321424000a00d001c05850690194a240e42003089466400180c3c3c05806031340441e264200401000b107007400c40c080e44c02c02400700e5082c000c1d403800c2e042c0d001c6001840342e40300703900d2840e80500b50214800d10380070034041c209003240b070441c051000c200c0d4100541801481100840310003042040e541207180c105078411005151940300c40b101040090007904411012150094181455524025540c4031205200340708504004042010240310f41400d40155402600c01c2d55141aa100c04994090540c07019442554050f650400810071074040d042c0126001401060300e4800480c0c0c1ca02107442c8002c0850038000200000707039903914 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 345363741 1250 345362491 345362539
    0x130b0d020120240610050d090c0302190303110f0a02090c070611030115020118030e19140909030c12090402220833070329040b0301060308030114 64
    0xc80c407580009210300000441030140011384258031a044aa10903003801e50300c1800e0741d07800140294040f815000c6401e003181d2200d21504003a410921201e20030300400c800c2d00494003200e08c81d82e0384283c3e01e40d61021207601d40404c1e201c1b04505030005000c1001518240d09200e410400d040703201480c25050703070f80f204212081d004080715a148007000400202941e50301c02100f0045500080c80b05242041d01150a0700000100601780001e0040d000c1094a41030a0012a40c40c427111014020391034102d4000803503c580b0030030740700d034031a4000500e006901200385c078100b941020040c2502c00b01000340011542017011202d0f0881e5017400400340c400c54600c041c2200d081c80da540f50409904040403a8203000310484080d100c503045015400514114804140c2010420031203507505407110342045000d0029201510905210441680c0070201066101442200d0032a410000c2072620010300d82038800920000d44968001d000420603003a450b5107a11a411004001d40c1501c45d03500c1310813015007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 345364991 1250 345363741 345363763
    0x905040c0e1201091a13120c0204150e16030209180103060515060a080a0b0405091e1c11070509010608041e110d0609021509130b0d020120 61
    0xc0c80d20500d81e00c15003081d880420307004400700b000740b20750001611200292a0b46080f24506a00b01e407001075200031451030101d00f0365902c0440c01040500c0400010420700c0b2050080c5d01c603e00d0f0410070001032443c801901c0071035600e0346903010140e445941f5180f803405c40030052010b040d002c1100305d00a507502d4a00e480281c40100040f10594190f00701003003207510043c560103401041808410043d40c1e010299050407070305150561103680d800d61010050051041820b0708a8100b5043c0314200c00040303039426641119007404c440d081f0544502603030345c10703c0803128a80f4038104244020300d10b214049801c04109030b20104c401d0310755a0404642c2180d001d81c81030b000110304800340700030045040c075558459100c02c2c1304241d1008041d11821180800c4101c1030380b090080c1065401048a00e810180007250000c1c031655617018071035000202035001c410004e124214904d14980316019034450300101750740242112145210359801524404505c5c80d0340d8952400c80504191200f808010001020b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 345366241 1250 345364991 345364997
    0x60a0905030f1014100b071a0a05041a0f06040b060f0301080303010807060507020102100209220b030d11060c0309030705010510031208061005090604030b041b0e0903070f030905040c 80
    0x80e1101100c403004980c04e04030603502804000c000e1046440c04210420192100e00ca0100d40d10a07081c50308400c075032081020441c500259204210349902e0540c05140300e580520b0200c040c09070042820070f01190115001e40070b25510b50041086400e0550000d1010343c0003400701844e00c04d00d40d03010b02141d0001d034008800b40d4400401030000310820702c40d038001484a420314906000150780040d440714a0810b450648550206000c000c40e030700e2904501c1d134024107a41340843c014800c9900c0010701075010303c10380203100e07121101c0f1000340b090814540004405020b000e2584a03000006041c1d0300c0031300303041c44a00c014454000400d100303104540c000c001204803026081c2c550310305051a401490014800d21403c0310403c10725450320806106c0d4003503030b450129070340e803c0040041ca0fa401540c02c06415071010404120800c443c0c100340030390f42270040012481055a07100c0003c01e2500840d4100c200380c0042c0000c0d00000c1190400a90079803090038001c0f20951510003040c201d4040212040c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 345367491 1250 345366241 345366253
    0x140a020405010f08010803070305090a090f0c080714070f05030f04060c0b0604051e04020103020d090b060a080d02070b030c04090c080a050c03070c110d0602040f0f05060414060a0905030f 82
    0x203250b030854100f81540f0060f04081c6000e62405185d50380b6801014000b4060210000301c2c03201c0c640d20480814041e142d110420490f99002280b0741c8001c0000828000101c0c111102058006001c0c200c0b44007109001c41d040342c80e148441c0d4469001115580c02150a44414020300c0207c100600c00341005c0c041e030380d449107030312001410728041050014100d94005e83c40c1c00140180c01000c44148203064809111028035903c5520040300280b042d0404c00311454500240f40c002c00c0305074409180961812141824495110104a03031500d00c42c00d8640096440b05004000103824803000d19413180d00454000d00302665814400145e860710750307000000981240401402400c18880c8640081010103458210302e04000701070865003c440c03000e000814401e03078440644c0e5481041e040031030b5100341c05640b00d40c0d454008146002d81c81c0145000840380b0035001c00c0e00d00f00b100c240c03000c80d0165142412002510401c4c07100c142d02c5001c140d406c2215940c400b082c15103080110b013018803030600050003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 345368741 1250 345367491 345367499
    0xf08070f0506070807080f010302010e0a05060c03120903090a0e040309030f083007050d20090310050906040209040f050703051c0c11210105010f0e01090b0a1503140a0204 75
    0x844c0310004c0070907003070021102c28441180781000606064a0782800e216581916500c0015030040d1141d2220b9440040003e4085c5060808006405a00760600074080581c85045030315450b400744034400340d00f21011035070400c00400c0100000d17800c2402402c010003204d4513911a025408949502078030128400201002c401c1040c05411108030007100b14410700d4902c0061850f9204405080403080140100380da42004030151300050800d10a44400307840c440d0f2190900b45c0c07a4200618a41c424015440c10301da107102a0302816106a02410143c4659619a420022902c0300078200f42c4013510354000d00d900003007041145502544c0100000d160000600424601a00f20302203081d04000c0300d640750800084070314569034100c1b0700494000905031b0300d2503c0c20001145500b1030125640c00c20000054014640424000703a50401c1800c2081e0380c3c0f100910800c1da10051041178101c1c80b180010082c3c4880c0101045079403410f880c0118048801c0e00085c4514501603e00b00c3c00c2a6000500700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 345369991 1250 345368741 345368747
    0x1112e0c020c090c090f01032c0c01021606050d090c35011a0409020402190512151f090f23040c020316020307120501050f070e0604030f08070f050607 66
    0x50340260003400103840c0640f00004246c1c0f500d21030001c203041c951104d2100090f411902000c444c0b009601c10390216940304d0000b01a900e0501080c55400360064803d4040020341c0c054024082d640503488251510a0302c00f060310050042c4113042d2410914020003003140019141c85425145181e00204261200f0790381e00b10381c0c0742403444a901181c0c500661000220f0003c54443c600700c030b003128000b03009001c600108010348901c006813405d65080400c04510b8035040b2001c1d1900000c003202031211070303540039809050000d030a03151680c401c021300710102844200d0002996070004900d48501e071079545a4845100c21100e810050f1841034401000802005051540c0c000000455003440840303207200c0042e4407481500c2c080500c540840d202e500954408010110040050521720700c921690790a00c03500030402690f030f03907158000b590040b0340340c14403c2c14161500c1e103008000302e1603d0302d1580d42c00c070380030420b0000703c921040034000200815070100c60401010b001c4c1c400340c02945085e60f002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 345371241 1250 345369991 345370009
    0x30204050c0c0c2209020a0e0c030f06031515030f030d0204030204110f041e030503040e0f06030a020a170c040c0519021209130e1c0e01112e0c020c 65
    0x21400f0741c0950349030101d04044e11503050010f402c03c1000080640d054004240341703042c60303000101c00c00c0640050091041102c0020b502c190070307682429450351241801c140d11050004103d5403406001400701d00c2e81d122540340c9110654000b001c44000c0310310b91041908540144860032203095003c10108190b043c171307000f0160100540c0c0c5000749007004855912005008500a90303007010f403c02d0079542c4001c2c00201c20030185811008898803a03a96030803115070395008a0303400c0724400c0d003070000c10072506001070f000104544c000c1008601c00d0500d00604030310b4500000c02d103105e100d40e10701140c042d180c1d88150700c42d21380543e851560b1440c00b0110b06c050740c2c1d004943c107401c55000020051407440c003202a124094004c41e081c01c0e0744580700300c090018004a600f41c0581303000308011000704203d1004070303c451240c16200c2e40daaa130380c44801074440045640c001d41403034212a4500c0c5400c40b920a5000f41c031031100f0590a00a4800c0c50600c0c02c4540000008000d0790001890701c00314900a85e503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 345372491 1250 345371241 345371263
    0x6101b05070915121e2306071e080105130f090f170c070b07080903010f060801060501030603081603020a1707060510060e09040302010b1c06111204030c020a030204050c0c 75
    0x1030b0750352113904c03070362081d84900d10313880d141e50300312a501e03441c1c1d0410020500950500000a280310001ca0b4201710842d118003054030705a0101d6041204108a03600c0c5804021103d950f03900da0b254180e113401c050281c2c1c510254a00c5503e6992030b294040b906c203413403003a45595401103900505041ca1440c0c4034100025000c402040311703005014072031800303800041900542e9480c4480584420192810076041d000d004031302a419402d000e152616500c0c50350142c402c940c403080003400300550354001582207032198000030709a1001040240d0f00d00022940c100c0459100384125081e15003a901c45113050200d04444c2d4070305140c0002c0010610100d40070b22a00a91080e0040c000c0600d042e0700139000c41034250720300d8010482000080c060600030751000400390405440540282031212a0720b800c02d02c0481d048504500d00100c0800081401701510f40b40600b10352800c00c3d0340c40301c0d00d00782c03102401d92208a030300003540d813404030060302c0300c2c050340e80030b01040e18002e512413840c000202d0a148500c02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 345373741 1250 345372491 345372509
    0x190303080412020307170c031b010525170910020a17010905010f1e05030106060c1401020403020d1511072d03090b0a0908120403050607030506101b05070915 69
    0x205c0408580000300f1207081601c1065115600c424546c042c84c2140640c110000c507544241c00c90410940f01034000e03034482c1401c1c1c41800c840c0c2820304150604180c01101503c0042d43c23103110124154036a24205810074001d20840d855911407420010a80c1d2007500e200c00011a041c510000d400074102c0000e0150480301024006981401c0f488000032400c0c1c800d01341b061400c0d01c082c90304400c02c0c192000c05080094000d10030b007521000090050030300100c0071540000c4100d01c890001d0010b200b80c81c19654014401f990340c0d80503895448142c035071107103881c20465442c0100c00002e061107005203d010720800005840d1440e11742560f100c2c50394030b00c0e0000d038101e44000c2200041d038884e0440f03081e5004035544540301c640303a0034111219104c2da00420340c180300d407146c00c05900f1503c0000d031040701e104c2c00c111013580c2e40300c640482c1903070130507505160059040780804c98818018410005564800c540c001940c10560711001d00d0318255034402400e481d9140d120000290600c1c40401c040c2c08026 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 345374991 1250 345373741 345373747
    0x209090604111005070b2a040503030a0e030f0102070321020c37150605031606030f020f0d06050f040225020d0206030f0702060604060501021b1903030804120203 71
    0xe00c0e1901e084269146807841503e0810b09a91020b01400540300e103142c121186214903d0451281030402d4110417035640007000e13444040c21400201e000702c0d0709580c13014010790f050401c41601038407035500c0e484103558980280707020450103803000d10107005118043c0e035643e1320801440341d1410014100c2ca000200c6140108095a0718040001d41401c40047e00382c603183c01c3c64140004c501c04000001c8403a041854003102c82001e0214034411194025090b0b4803c0080710340d00c070101aa174a103005402e07903006246150402c481400381c0c0c0300300b158812806c0301500d07002100700c1d8a080c540c00140f800f07002c590f40d0b5405004a003007500c00c2c7da110f03450580b003c5262210120040c117034011070420b452041d520405043c401c42d2104408030111544c0500030755180e00781250510501d00c4116020070040c802c140001c1c4c010b141c18002d8a0407154180c000c3c041203146000c4560750b800741002550340021401d100c22804a00d03900301c03a030045029640b0b00e5020b080500c0d1442940011406143c1103510074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 345376241 1250 345374991 345374993
    0x10e0c121f0515150a2001060602010203100f050d0303020d020f190f030c091202130903050721080c031b04090608070e060303032202090112120305010b0d02070807060e010204030209090604 83
    0x4801c494085c0b0310380c104140072030f008032003902e2075484a2000071b01070350030031100040caa60150040e500078058190407800d9a502e070030500d90b140340b40d0310840754000201c41c107000109000341d0080c01403035440300b400b51905502c2d2840d032105074070802c6030003000c00e90002d42c80e5607194800b0032181d02120515052000d002d0403140101060074900800304000211800c481c110742e110b844003d0408a011000e001d83c44960070081c1403a0003103101074070080c21070710b680440011113041c0503542a07103a84511002c2e0300c8940c22200035030001041045404444916000000074200143c4000c028244000c600c0c542010031003030408030180d0020080c041d4190600050b640c0200a40e680300184803015689108c100c98014030500c22400081e402500003400800c2080e4080d981404c0c0b503001e125902c90081e079618003201200e8007442194910a014000f4a4010249800819503240900030b9142040d895489403c112100203501040c2d41e0f500240810441c00c0511a1075840664032015199034509 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 345377491 1250 345376241 345376279
    0x10519060f0509011112301303020a0b1006020c15070311030f0f0409060506070f06050c04030203240705040807031104140405060405010b03010e0c121f0515 69
    0x80700442034240000480ca11420381d115104c4000e076460240211b462503001e501482c1640d510107a4070704007040480d107400c9068082000107008030000b401418605603201550f01d1000c0048400c210f085029680303070900803450704070107107018000310110003c407035150110280c0b415400200c02c80c0a03c40120030702100302440002e03600c2e03403501400c1003020200042c047c43e04500c2a07000742e02ca0041c01040441301424500d0140003501c01c01c900801a40347c40300e00b04000c0e401850401440c0032140517070b180001d01c5a40010750000e117102007407800d040d201d03030000741845481054080c1d04104030fa0200e500108401001d034000256041007454541426840e94807142c881c0130240446008204000c0c1d203884985c0302d03010082041500001c10304051918548503c0c0a4500703031400d60800d89480942e00d818440e40036442d08400040000c140d508051083c4121080700c042601e0141c03484124224a44252400301510444000291403800400104110740d964510600945603e0030a90030540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 345378741 1250 345377491 345377507
    0x60109080c061e0715050717061915031406090903040603200d09020406050a08070306090203100509070303020d0302031e040609080a020c010908010203040503090d0302070312050301051906 83
    0x3002d03104039070748105401240000c0b0f01c4281101c4084000050200d00f0b118811030841c2526000400602990316942e104465182d01c05050345030a05401c0080b0351546020a801c3c00038103011501c0c2c1190a55440304003003680310703000b00240869111140340d00c5032010400041c1c0c0c0560103c4c2c0b00449801c0ca5145a80d980c0180e001e00e80a059070742d0240d07500e1242445003054a07541c0c0e10a16035a4403001900031001d4620080101d0043d400c003000400d441c507280406000365178013100101449855510f540c0c2c05040924416038241c040c07a2040100300456009141c0720b10940c90052109520f50700e4000e2030300990a000c04c04052040c01401032003071114050842e41054a09030040da0348450903c0310080000050090a0340380000300d00940c90340216900d0740842090305c07801085640d5480260907031100b00d90041c15900208000001880c1903240440001d010740704170b690280d180d070340e540542c4c0e401610000104001100400035840d019195401e00c0e4800e03800600b41510300100030740051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 345379991 1250 345378741 345378763
    0x1203080f0a060e010906031a0c0a1d1206010315021602010815030a03030605011805030a020d0309081005061f232101080129010c17071a06010908 64
    0x400303440118005401540040026000110115000d540c1d00c0203c440101807500c0200e440c0b0307050040a826045004013520301c6034600c0c49003145401d03c642c208480e48020340e050a8110294545c60320041e81320313440d8404c0f0300059600182900d50450500b20769298003001c120701c1d518010025010800c1c8000200d506040d42800c0000f03003600d5420284d148151418a03041e0544150031600b81419810340195007101c00a0322420003004000b891100e510040c4d008907a0503030b20035811180107003408018121594003e01e4101101034507400d1150410780101140d200081d1908140a40e80c03030240c403a08150f111a83c00c0310482c9101c0720004c1c11004140a0404048044030b080f26a4a000c0c1c5041f20b10520f1000da5000c42003015140c82000340c042809074107050346c80c00e2840f1b10540d07440c0125072600062026000c05a918180046541340d0514000310b418202a0310039004210350903010304002031088424044207400302c88040c1130210000d00490400502d400c0400c0381c11f0012030105100c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 345381241 1250 345379991 345380011
    0xc051203032203110a06060f050d0305041e08190b070c0b0a09080f04090509120403031b0816060c0e031b01030213030212030a2c120c06130f120308 65
    0x4a4107a00b01510003140d41000b044c014001c1e51486800c200030369000302d05031415155190320071030303c0703c05108544030070b09002000b04100308400d004070b01203103008100c0c06014400b03030250715440345200b07070410342040c075000d8a500702408078a04100301c0c050011f502207120302e40b00c00000403c0e1a110705649010302007144c5959984004424000f1607411500312400003500c2aa90303658a0300d004000300001c85011031940208550110b07940b10702402c64080740d0701a5180d105c0c00260f80301c050002204c0180490f00034604100b0403595405c0c03029004040c9000b8030000075044240340e00504010174400205201c1d801110505001008603030300301c40c601c0028a401a201d50b16800090711081c015080654002c80140780f85101820010040119601d141e95102d15035400307002c2840075100582e00f0882c0966018240002424401610b19001803d1000c0780c134030811043c00300d802030f80541c268201841c42c400050140e50034004070f440080100310070000e010001a03c0c002e103030b0340300034100c4005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 345382491 1250 345381241 345381301
    0x2210d020a033803030a0f0f0e03010515040c02070b04091a060c0102041503020c0706211410080307050604080f07050706051201080d020703030f1701030c05120303 72
    0x146911a0f40040e02c0d0300c2c94481109040c0744400010070400c038004840c60107400020007001c215041c04000d07039070405515280c9404035074400d2001c5d00c00311000c0072440100038981340e2041041d602409981e0050072800480802c01c000c4000348400e68a03030301d50031000c1d540401c1f410070940c0c441d20100c0b411242804c5000806500c000904010512620307002c2e50300500115802040302d006500400850340e00b009402c1e8640400714081c0c090303000d0a1548000342e0403090040001030b00401d10208150818224a9056103a9540240482d0200e40b000085042140c081088030b903812076140c006007242d0070040d42000041e42e1b50760b9031004024170040c900e403000f045041103100e04400380c0303000300ea0081c00e551005490701c10050480e0000c802c460003003c100310001038042c00110310a421503245034003400145007162130523201000c4000c2c081c010441c0a03c207500c1c0200c00c10141902079803050b4601900985003804001041d048200d5600b42da41082003030001851310605a0a607040b5110355201c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 345383741 1250 345382491 345382507
    0x914060a08180a020d06020d0c0c080f0d0e06090606030f070b0f090402040b0d0b0a0f0506030402040507050405040911040e030a20120304030305091c0507080315180702210d02 77
    0x3040503580c1d1402500005085c4011042102c241c02038400200c0203901040309500c540744c205d8907005000c0300a0030080081203a07610f0001c0400041620345880800800c0c10b01691501c5460440c0450310502190031070340130701a00c3d2500303204203110140c0441c01010144c0c01c141070a0000c1c461603540701c0d03954000003440790085d00e441d01610000d00d410424240c8510400c2c0c10f00000c7d002c20490740e845071030007501c04190180d60070980700a03984090451030070340d517840c1e0902000b042c001d0000c80c2032000500c800105a030320340c0950000c151042e8010301004450000740401c0d038100d03403880c201a0b0018014846041c4d801083c001d00d0340c0d42d9001c00c070031014401d51a103090245c4c800b0b6010a0a500204020034181c142c0c1245002d02a01c10440700480c507096000c0d141c4042c046c0f940000540c0c1040b41c2400700b590003010303641010039100004001312000001400c02c01000890401394012102007100040d010b11103140c4840c844242481c1a020041c414800d40c071400c880f0644107940031407803031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 345384991 1250 345383741 345383743
    0x30304090e1615020c150304120e1012050903031b03040309081501051e0109050409050102090a03032607050304030302030702030903010f0e2e020c15070914060a0818 73
    0xb40003203200040190060b51140701c4540e04a801c41d04401c054818031060715210300305206a07209000c1414003240c1151500c0c0c0c2c4101c1610b0303803113001e40108489030740d800e1140e0f5134181030000340300c10f6038442c102a800c0300c080b0700c01a01d60041c0314503501d800134030802511590020000c07102c0c0400148213640e03650b4518043e02c00d904540c204007000e12907000340420a044034101030f0b068134411500c4c14082e44038002c3e80a0f140c5800350b03800c1d0014203c1b140c10029403c081e00204481031040001500705070003400400c00c045499070095000401e060101c2c80b00703c80580e240d150440c2c240d11110042d18048201a00700c0c0310103000201010f40c00000119820310904c02d0341c0306064014000d07c80d410004100d40c003d0050001c40600354021030600301c01518407550001000340002d490040a1040b00c3c0044000f034020ba00301040030700403030141007021500d2003d80d61140302d007070b03c0b0380443e2410049504450403011184a0090a04201200d015500304060607804044c5c0032200b2007542d44c6604030303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 345386241 1250 345384991 345385003
    0x610050705070f1a0a090902030a0f0905030a081303020c150c06090c0907050a0c12050702063013020409020301181a06040204031e020109120609150b030304090e 71
    0xd000740c010450042070124400225404481040030011050035482c0b081511600c2030080d04000f081092200b00b040700c3c102e8001e0740c4c0c8941c00e010001851010980c004042e00c0000c002101c1c01c8d04006010090075030010407554000a04503d840c0c03020301b01c0c1c2e80c040e5588074403c240911603080c05d100c54010441c1c88044030b1482c4640800e6481900385104016550396840003c144215003643c0020311a45c4a0310a0702c512500703d60351079004c0340c0207440380300300352110710054030801104002200158a8160092418101c02048802c408404260707071031100005002140c0d4415440c024001456010740458100c15011180016895582d01c000b07030040030703c241c1072500140810640c4090140c000300c104c1412450034038116a5950701d500300801c9124a010040008800f10500d09009607032505200780c52f0700c103040201c100d68a89050075a500d8070030600303c843c151541407003810041601d10284001d40e2552090280d0444400000d03124021400b405145a583e81c44143c035242082200c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 345387491 1250 345386241 345386243
    0xf0e01210f0803070201050619030b04050703060606020604030e011b02060c16061d0d0309030311010f0f020d0c18140301020d0c1707020303040201080c0c101d0d09050906100507 78
    0x9030411140071071405022079001200c0500240d4a810006a0f250800d0380d40204191481d1802e045e240b811a51a1565804003a00948a0b407140800100c0094210303c12301000d4021a002081c1c80e141514008000072101007001d810040c4486503515903101d40c0c25806d44950b41100e44c29107586401a078149801010f00c26118003000c0000002109174114000058010103440ca0412103400c0c403051013030b0103074400c400500040101d1420408a0f104440074001d00100380004074003403a03018129000d03560700440d0394407907035030020b4480580c00043c440d60503043c0050070240c02210014060380d00000c03c40c41611004082d800c0840d10341c0d0317001c7d81152050380e124141040f400396450390042440d81d0701e1a614850200c041c002c244503500000030350348125070507074407284550b0341d0b600c01294542184900078410700c01d41c000360f2030501107070280c50b400004071065002c0f40c01e203000f5044c1c40c100001c4456000d100072508140050b0312002c20042e8001c20907a600002c85000100407142e0f8828000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 345388741 1250 345387491 345387503
    0x3021603030c11011b030203100e040c05100e09060f010504030f08090307061416020406050306041209060507020a0902030408070b0c0a030522020909030d0c0909060f0e0121 76
    0x10040806030990b001c0840291a559006228100c2d21801400c03220300d0010342204c0760140403401a15403198005540c8941c03050861190701e56141d05420101c03405503001c5801e11807100060150303023424134240c082103d00d85000d4010700760704004540c8242028000c0360141d40b0081c4151941e901400499005540c42110b140100e052410164219044070304054813030701440c000003c400344a000d80c9003a880c020702074140f90081c0c4940300e02569207040c0741244c02c640c980d40d00203040e54007400800c3c4140e00480151004543c0010000c00e1131000f60030040501c4414003140026883e202c2104060340c03404030f4010303a41d0b00c40781031115070340c041d0b050014035040c908410841e240c19208051303c070b02022500c09100d02e456070000f907401059a0348000004d5120b07010188094a0a0110103070040401403c0d40e1500180c0380c0307c0019100c80402c0c0501040f0460300c00c0040b101b076072040100410300302042e4400d06040c59980b04001c0d8041c4141c014030f054217044003192680d440c2107200e81c03640c450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 345389991 1250 345388741 345388777
    0x50d0c171501030e030c0319030b090f0a061505031519090504060e0319081e0c0702150f1b0a020603010618090c0305010305010b0405010503031c020c1005161e0e010302 74
    0x4030501d80e260f10010203007680d03048101212328440c0c003070302888140320f030f0080180e00155a1100a032019050081004003c2038450702c0c0003581604003065070340c45030350545d9456600d28000c01401484160041c410740074595080805031400107d5005c0c40035103800c510b000c120f030340340c80c10068050480c10154403c580400604106100b40c0000c051903080c4094480541541c0c07940c10103020403890402c2a40d800000c040043c03104003024008104041c030040c281c41240e03440348c0441403203801c02c1c000144031130303400508800c91038045d00e002c4100c0d003c00c000514041641c4d6021947c01d00043c0700d04402d001fa4105040d075411000c181c0d1f6005410703a602d0411400700365060050107020207100940e031030b5280c10001c00150905010f0141039410143c0110714289100b14030800d4030702d10301c5110b03074101c4d82440b013803401450500407612030300c80315900030a4905180030300c200c4d40084680f41d4402e21406010545001c56204000e2100c41c000b070806400d0080200e005034042d00c108101c0c41e518200c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 345391241 1250 345389991 345390007
    0x9011119030801170303060402071e0c050f03120901111e01021b0a120e0d0605100608070206040b040b13020d06050f010b0715050612030307050d0c171501030e03 71
    0x4890340c0c02540690b9450b074090366650701c00c0c00075100c1200404400e800800c0013807107074101038004002c0365111b00345a014000180c00c004c000001800811240b00010f441d04000602e0803481c565890700049025002050540b4940c1540c0d09c40d01c007425043c041341c3c0b2813400100c041030142010000c0b10218403c0880d6212166500035804901c83e1001526201b050003044400018a400300c1603006c080090b244c40c8450007a44d1a4182058083c5d1201c4603400120004056000791405005204214080c0c28141a4058007000c402014a81113600400801001c280015100c94002d500051a80100d803030fa41006079081d0244000650441180e8003141d08101c1281e02040c0f15200b8144007990756622048908900e207c1c1001c041c041d50700c4181903d83e142c0403a4000341d00000010401001d980c210980c1c0c0c0d0440d001100c507030021a20228251200c6089130007181c120304040c0c608031611042a650004120b24050f04200050203641031521b4280d0183d4070400d03c2102490460b51a0110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 345392491 1250 345391241 345391273
    0x3032304090e0f0a2a0815090309040e031309140a02070c05121c050a090b0d0204051c05070501030207021003090201031e060302360c070f0305310902090111 69
    0x205290041a03045414107901074541c1a8040e405032801000502401c6e1020000d5081d0088090300091312404200300d8800c1d83e03552f030b1003000306c10802c10015544a0700c0541940f43d0320640d40d404019514107000350307200079030655141c0d564400e0b100c100050b120004e0b800c2c80b103d10645900081d410400920360b00d103612000060700c7c50f03031900922a641c951644001d00b26400d0191000d80c40204c5d000781001d104042580c0c014100156001070014280f681c2c80d8002001034484141c4143c41c2c10807460000284030301807101c00702421007805c055240c02503075404645a50b8201000508142d071b40c0032004210381c881d03001030341c3c000000c1c0b903402442e44103c0740c1e50f401000203110880c800c11001880c042c0c16a02000901140d04001021880c2d0070007502d60701d810300324002c0540102c860b0422071302c030028220b00b00c4c00005501941da0f082d2030f500c56400004480007070103e01146550402c072110070700c070060141d00301511000b100c090303210401400160345a000528403085070340103c0540418000c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 345393741 1250 345392491 345392513
    0x10312020703060212010e0907061416020a170d030b010207180f05010306050910091a0921030a05060d020f060d060503010204081b010c0b060d0f06020a080103032304090e0f0a 77
    0x551a00200646908040c0c81d0f440d0070300c7c81000b0104803000170f80850402080c02504433620b08007040d807080b41269000840b9914140c011010a080450498601500030061201d285400e801c04110b144107200020355565050b204401d10000c0015a0200300180781d04482c0322240805402e0016503141e2500f040035190845016580340f0901e000303240d86507214045e005019401620040196401003401503200300018904c02030341c8510440c0b8207100c000208016040070607011425100c0c1485607108080d6540a081e051081c0f99a944900141e680d0650000704128100c802c03e0396003401d1007050010b40142d034401c40e859440401c00182010022500c0449000c0c3c0c1d001e03c1d2140c10042c00155042c0081040c00b40040c1008000501217082006044082c54001d02c1000341e000707820343d2800d05030f80c0205104400122a0001041015044446104043c80502c8840101c0080300d98428880c011849080940c5440b030314030341f10441c0c0c148400d102c3c0720590390945002503864201002d000e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 345394991 1250 345393741 345393749
    0xa0b0409060c120908030112081c09170f0a1d040903020c03240705090d0b0106021507211d0703052506080703051806070e041406030601031202070306021201 69
    0x3c10481e89002080580e20400042550080c0200d0442c0d0820348484140e010381501141c032440704100c080300364520010500c048145450700803070092072510300740d4520106050010702c04902030208040143c00b410540310110b515141480d90074070246042e844444280c058550010f152424010501d640851a0b003003240c429022220060b4070248102800092925503030a161a03000200d14a10301c540010b02499000810104205805840d00840a02c0030303404100581e004502c42c501868954503030950041103424180f054400c0210021040584144004074113a81c492050340c1d02c0d0443c5072040f11402c0c0250440321240c0d202e182c15955604d00e280300c44035401c0c000c101180d080010044c58030070744409658519094072042020341c040c1c0000341005007012030101c174002d80301104100381c0c0c0c030840b4543e0f0350044880424042c07000310340364541b4040e2003800d0b00e0204040790302c0004889044136807026604088003029807040b4205441da8000a01c3c2c00e00000d00b403102d05d030300c07224514141c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 345396241 1250 345394991 345394997
    0x1305090703020711030303010f030f0501020702060f07150b0f0f1f0e0111030c1c0e031501060e04021201060f020f030d06050a12200301060b0c010e0d091a030a0b0409060c 75
    0x40001e13500701a901e0000740700d0301300b401c0d00e0000180005004d902d0700740c1c100c52056001505011440c1e00260a60b001250803230302d03903900800d160041c0004c0b2603105075074150302e2104005158000002c02d410315481e908041c090007a134a0107130310300d44910303d6040320500080d5840304064903611006041220603601680090100c1103103000c9200040100c655510024009148008290488117000302801c0c050005212813100c40c84000d031410b0008820007505211280c400d90705080340580600414403c4d640150320600ca620a01c8160f81c844505440b2581040300d81c8942e450812854028421901040c90001240c12005000d4a81040c000e50380111400001030762540c0b55008000b00680c409040c80b40400307841c10351011000c4040c2c0c107856015002040076510f032443d42443d07512041c00d007c802e030764489410011103800e01004111804a29103019078518182d00b102c000402d000030589a008000003151000c0d80c40c2e4025034480601820501c203640c001d0404000070f052150300c92000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 345397491 1250 345396241 345396263
    0x90503150916150f0c0203011b030c0c0b01030f11120c010210141303030204080a030804020a0b131512060b0c07060206060607081c140a0e0304060503060613050907030207 75
    0x2540c25164102d090b20110030700984201d21040d42100e480305414480700500c9840100c52000d62400c0c06200500d040942e1844d18081070401c004049031400314601007003200700d44c101c00014900c0940c0504403500081d0003096841c0b28200304030707851115081c07164405081320800800e010082142600c843c07090b020b0b82d09000d1443c0185042d1044259070031004056480080c9030311190903040610240a0b20b001420503071114803c41c41d1101d02d200643c04501d00104003c00c503e4502c1d03d040181c260050039034242511107a0451a00c040381c004c200025082558800300c00b481202201011100314074144440c41d5501c880c810b05030702c428103080c0a8011140c01103281ca00024410303009030400f03442985014030075240e066294000c1e400940600c100301e07050703a00c41400c0b801280f480b480904c94407401030030200c510f002115a541c2101303100d9081840200041d581010990768000f074141c0b1070b00d503200d266010303519000540d038000a600c0fa05000c14060001d61603400740000c01d103d9003016503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 345398741 1250 345397491 345397513
    0xa0e0f090d320301090b03010e0304150c14031209010b0d11010f11010c030509150601050f09040b04111305150307030e161517060a05040506010905031509 68
    0x61990401114100070410a020502e814142c20001035002244010340d40030ba1198005005603503030080e0300800d00b02d500c80c00c0e4004546000c0c17003040d40e092841d5004526240c586403244a000351041104014000c1240000041c04201d1040350340402d200e605807039869640c0c60586401d910240c8030310b4a10b618004210010741080034803100c3c00c0f17811460b011210032103a801142d0a0314561241020800080341c0ca0040f807100340180c041c1006151008103c81c90f03e80c00342894000c0c6802d100303906000070070900c240781c0d1300002101c40350f031040c0c074215540302e0002003c10060021202071039001443c107500121940081000b5242d40c2c2030001c92151a07079030f680c0c1040102d601c2c15403904801107041000c01c028500aa00030a0a02e80b88016158030565480035082510060360040468018405c5400ca00075070040007494000c059108181007404e124001c40d510148134000c0c540120703a6040450803030b0380103426500003000f00408071046688000319102c0341c02426590f00e1640c0c85003c0c0124 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 345399991 1250 345398741 345398743
    0x2031905060d110301020c0f07080607022415090901050403120207051906090219060f03061815050a0620010905190611040303030c02060a02030c0405090c090a0e0f09 73
    0x60003140e004019008981650f2602908180b909140503407565003080110020401486a040c1c034105880c0506021032820702d1941c10104002c0044046410501035900c40d0141d4a000701c2c5400b94001070030328036981c1d0602c80d030f181c2c61021030b80c030b035101400e2420024540c60540015201e607220f50340e190344c40340c0711074000e03002d03801200c1c1c004000d03802030b4076080c0c00c0b290b00401328041c2c0b60140001203449e03e11a00403d140101c000452048500e844405026240e0805010090500341e403408100c210300e0f1494030340368071100b000d041801d04c0c0c80b9140d2220103141006900007400c0014a0181c0c0c240d0740d40d1004d088880820a0007040b003140440c0e40b05a240180300e84990541c02102a00346145200441c860314803045204551171603681314219040c02c8450b014001851083e10001003201c4800e10103880c0080060a2007546401002002248940741041d1400c0302c40c1600c00c0740d041d484040261318180100000d242c1c0200410030001450f01c4d5034844c260240c1d050030103100c0355484501d406 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 345401241 1250 345399991 345400001
    0x3080d0e0d11032706032d070c080c1c02161707050105130b18030f010515060d0f050412270e0a090f0b070201060e0112061d0a06020319 60
    0x300105800500c52842442c02130708100b12114420700c800c110000c510700001e5103a13001a01c51550030b1810b60030409030b64420910410210109640c0189145805903006107013010003a07008200c10301c0072440312041c80d010005a0703001810380c00072501c13000e4031200c02552160f004999844001c0009800604031000d41c0c46101c10490007009000214100401944d85034003001c18200140c0348080d00140040580015042c500d0003060310001200c040c108151915041c4504420183d2508080c8148907440401c41040c100058a606485004c68690b0170020002812040311044c2450300b00b208000712102802482402515210f040c184181d10031843c0143c0034020280c01d100048040c841040c415045a5100844401c0170440b0801544c840c40b43c0722010f442148c81c1c5200c00d023404003403502802880050803040140650341d42c54004102d1070141968070107410159135400c40da480c01c00c450343e030000421094080303a04d54106850460002c2d40201c070303c1d202d110040c1000176046a128080d07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 345402491 1250 345401241 345401267
    0x1303050d090507060305060f1912080f0a0203120f07020a060e0c09011401031113050d150c080411040e030d0b21030d0f0c120b060418050912070f030e0a03080d0e0d 72
    0x149c0a041401c0405428840c0c4070308000342c80d000d005000c005072248503080100040250713a8040c588034a40d022142640740d030003500c0e0204843e00c190030488102da0019200c01c03010303041103010880034580125142801041c55425070040309410001c1600000402d038041d8069003a03808005024a600e10794559009032142010402c0c80300e10100014901072030080e4100b406145120711001003c00704000711402c00c4c0c000001b14024008200030700c400380011064180095405205001280c0c200e140c580c07083d0f14400e5101e541d2081020381ca612005e5031140d4440200704141960f01d881d0012568903003243c07000d81482406e200c01500c44030070900804840170455140c16542030400079455000e011201e810f00e07044241400300068514074130264507465041c2100004c1c05060845a0320306003030740500c002c4500241048400c00094000a022007103981524265041c201650006144a12241d00c081d2020402041d10070100c2c405074407440c82c1401d02421540700d9144030605071801469181 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 345403741 1250 345402491 345402529
    0x2010c0c1104110315010905031f02070533010906050a090903020c0907050403050c180f0a060b070804090b010207081f0b0303040801050f0f1303050d090507060305060f 74
    0x3180100042119441100e0860001c00c00308038450780c0c0c0d04000650300308607030070f15036005565a28074031541c02c180340c940505810380203882288202083c000502402c440012106540000e0b1001407040034090f00d464102080e591484001ca4000c0d092601c0da0152600104101260b0000402e245240714001c00c5403c0980b0b40b2030700e035152840d4440284059441601503014000711520b1568603c650584100950340700d9035203950660901c0d40c81c0004141d1524011100003e0310704041104076911503100014199001c0709941c1c2c00c07000c46c0901290341c404000360002080c2c110411400001500544c4c0842d4410820f03041ca00e03004903a00c22461241c0c0c03140d9041103400c0e00500c4605440340c00c841d000d48402203011b10072180403d182d68042d80c4146082d03552507040c40601e014600c42560404d42c0348040f0321841c104885502c0e500700749144018188500040c00800b403e03255089035184941003c20341c9c4540f56107240180c017500381201d100d4031400041c1450351891a02074505030903801003031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 345404991 1250 345403741 345403757
    0x311030a022e05090f07090e100c05040e010b070611070b060f0a0305060103121413050609040b0d1a010b120103060b120a0627050309010810090204061e02010c 70
    0x80001116502c1404503440b00003081c40b800308440c0c140202c90081d485007008108562110704400c0c10040c2a4101d0030b000d504068900303400c100d00050440c42c1c03403d01800080d040302d6102054038103208a45c40000080168000040d60700c0b140b8010300303507a80c02020140524010740304003400342d2185680c0200020729650210b25181051440045520001703407413a800315440b40c98440c54950240d104490704801b2551014446a0144941c034018140e11455070404041500c1c1ca114400d0318050f8900802c1c0200710429141d41e15001034941e0345010f040d0f02c0c400060303410b142c0c07004e0300900e003007060041c40c640000606252510072240020421803642949034250790329000034105c00d034901c540c8800c5070621107089179800d200c0014a948600c000241143d204d140d040c0140300c80080312200c0c1c120404580c00498000700896072010b6091801da0120350f142d207017942251b1050b800803400144080707404184690840780246101000b81c041403080c41c86050200e0036110a8045000050040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 345406241 1250 345404991 345405013
    0x60c05160f1106160204060806060a12051c020a0506010b09130914030c030301090e0a08041401030f020d02090118080d1d031c0e01090305031b03040506070309030311030a02 76
    0x1d4485100074451445044194159000030701243c004910494800d1103180144046152900ca0a0b006140c94006010f69107007280009006030038601c00c0708161410740300382c5c42c10400709101c14040a0b030f4046040c01a140c07007500080d580c000c108000c9600740b24002c00464001d07008006d8600c0c180c030040a000070b200004585402a020810085400070500342c2e81c082c2c0c2da0414030140c0740141021300110303125071509400300141c50400c86024420381142e6032902c003042e420011079083e0386605058000464110004a008001c20701c40800d4032440468160a401590f40080249550998400243d80c01d001c07036100c4403650f0352244a409901c2100c07854030b00da006289951820510450a50204500b440480e04016541d1384880848410f280400904c6400441c010000102864000c0c12a41142e668695903c40d440840310222480e801064207800e0800841f00500405040342d83c60b1619443c001c0c108a9960000703c0110305080d842d03d001d50000002c0d41e51250181e401003800301c0304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 345407491 1250 345406241 345406253
    0xf04090507120f0c06140703030507020f161403010e0d140f031614181c020414100b0711010e0103020c1905060604060e010b160b0a0504060c0516 64
    0x1504800c4515004010000482030240004103202500031920414615800c1c500084043e2850304500c1c14031000d180c03070504c900414820f43e401c0c1e951600b00080c05071a800c2c0203910b40851b9500c1003055124918005100e480c3c108400c40407203400303203c445008500c174020180ad07549118156507490380420314012401c0c0c4030700720501032035502041c400c0c5030080043c002c280c1a0700c102c8200100c1d00304020000c09150b80114124406100d20443d5030424003020100040c11024004043c03194001c2128600084580380c00024035590042c400c211015100002c1a1030b00c000321010325203812032100c00100c2c0e050600407200242d5120328251582c404000040d28010391585c2c94604240c1e081c07002c40c1e140401046200070401f0360395040355007c038dc1d6281092030000001c0c080c6c0d024a0608104115034441c00c813005054442d14031440c7e0b21043d540400e403240c0003185202628044120060010451495009034021805a0000d02140070000300c15600c610039013000c0c09050076104149408110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 345408741 1250 345407491 345407501
    0xc0201140711060a0203131a07110103061d01050a0501021c080c0d0603050a05101802011b020a031a01120305040b090a032103050108060438010f17010b0f04 69
    0x40300b141004428a109070114103950003031800031000d80d0001843c0b9402c0b100c0024140e0080c00381d240101110b003280c44901c0501d0180410090031035100c4515030030140e010350000300240030303903260030608820f0801c0d1030640c1c001300380301d140e0080e00c01180200720755201191458110108048043da801d5031860115510035008048900340340b414000440b202c00c1c540905401140103100401d12403040e4204142086400d800c60350032a8035000000890303d03c2e02e58201c420760780900348003803410318030a081190724004000003584030340c0c6031101108000200075040e0210170700062040c030983c4c9492285000c0403140d840540440d40900040003c00c4c81600108411f2802a00900314075940742d4441c0500008410a2a0700713004031000340c0d50150f4144119401480f40400602c42d41c10079442d00008050b81c8210481c880c07030a0504c04030104c03801c51000841e6015030035002c05035a51401c000c0710107206070142005503800002c10f42c50094050081d907410f254000c0c0020340c40390b5600d040100a01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 345409991 1250 345408741 345408743
    0x20a03110f060403030e0c0d11040c090902040b030702060106020d0c062705030a02011118060702060c030a0f03050901020a080126030f07060b0307060c02010c0c1220010c02011407 79
    0x1104001400141d2101440314601680c440c0c1c8000c00d01c404810070003410520180b01c4507005520f0500309001040108021003a070540036140014548840c0c03078204d80a080c2174201e620f02500004002075102c5c2c060005510500c01c03a070079608242d880c0e41080342c42e18043c58a403c000b406071840000887c8043e400103410f10034940103060702e6007a1803050000c0401c01e4038182c44541010032040d40c029028007030b00540800440381580b80000082901d003046500c204140d00684000c280c00b011916108116401d2598441c0ec03240c50301e43c406802001d0b41d80b04400351300080d0038440404d664140c14000d41d4103c0c845915446002d07800e040844482c0c40120400e02446a40b00840c0c1c4180b0500f80000d0440217129000b8641d901264201a42600c14207031040c0d000b0b5100c102c0401003d980506094201942480d100e17150116604207100c50722002d0308009410a440c200c1c04d82084401201c04200c040c05004890207011202d0054401c3d1989410180c04545100020f62030701e5407901c001c0c007030741b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 345411241 1250 345409991 345409993
    0x303070818040618090c05030708100203090a0804180f091e15020409060f0501050724140108060a11040605070b0a06080f030304031107320310020403150606020a0311 73
    0x800d0b41c0d007011006805001102c01013482d643c0c0d02c44001d01001400340d02c00780c80c080c1d0050001c14600540241c2d510408c000b40005640e02001241201c0803d2081500c469080000544c42e141c42d040200c0800c00b0005000303580034541070300720010384214025003014070b030071004402124450591403058040070300d40131510b541c900c0004250030b0215201400140035080b1000030b40904151050301445242d41115050110034003040c1c00082030082001c0b0107802003245003513001102c0c01d24101504d0200c03011143c0140220001c280f03290000b90a610522030700320107210064545c3d00c0403400e44280d015a400080c41002118042403003511180d0704070a0480c0d0001e1190b07601c54800781041c1c09014050300c0c9400010900003410350154480c540e0040c100c0c06400442c1c60113200b0040c03100d0409a50303140c003081c4040940b00e440402810840c000024007034a684042c2202180700030362050200300da4150201c003030198140d460f880740e0010750b80c8070340003006140d1042d1070554412a8154600310380d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 345412491 1250 345411241 345411251
    0x91902120a020a080c0f04110306010c05030d0f020a02010b042a170103030f171501140706050c0408010c09050a050d05120403080a080106030c0207032a0b0a0806030307081804 77
    0x1a120440040300034100f130703409808010b02c45410421022000302c403880c843d5060104000780078550408803900200b090920703071100d190034070b8880c0c29806180355a10145150082c640fa9402d903540041250007415802041041c4000040100312914000d4031005440854400c82e0750000c03074041c00e140d0035054100b01210044000300c030f0740c038500260800c40000d0300c4803212182d0940c10042070342240324004d056484034074009203110b03210301340c041d40513040090b406004940450400203d0b010260400703800e1145141c840f070042819801403050f003041d07600c2c04419120f414800c0c20700c0c400f994801407207a825249804108010102d40c4da000390780c540a242c06020014079200010720066102e0366040d603d503000004082e0600f00160f105030141424840103030f40e5a5408105603058130f60111004078550490190407855000118012031020325076500800c0c3d42140d90701506001c0c81d10360311140541e5440c0141a01d9014803c03000303014200611a0342d0508602ea641c09030025005000000e03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 345413741 1250 345412491 345412493
    0x61d100e060103150b0903120f0d0c1419020706052505010209090411180103021c05100c12111204080d0b0a06050304020405091b1306030f1505091902120a 68
    0x14544c146500c4081004030000f00345240d400c061050f100d1242880c0f44250502d4100300300d111040c4030b025205e1300c2c1c296030b60801c9081b960090314581004802e079209552507151460700c60104d50048610400540b09030440000d03190302c10000c6070940c80030848011018035418902c00c2c7c1204002c88100c580d075400b400421000d40707480c10060b100300d0044009451210454080c022000c2a202d400f002c204080b900600251b01d5420f11034842040b201391b83c03804405079003006c50815100645480788103041c000c5086000380d00c0182c5408242d41c0711010000ca28506808009510603121246039200183c3c0001d00031800200c06042600a100e03070100317069413608001041c2c40c12541050000c02c1000c820b0005606151117102c2c1c1c1b000d601e8000700210680c1c4454a031504440280e0355104103240c3c0415240300149400080003143e00c80b12001000c165480c200c040500c03004e4440510707a00c1c8c10f00003414980c000403907024070108032048403100207264090048111500801c0d421511800100034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 345414991 1250 345413741 345413771
    0x2b11030a02060c0303070e01020a0b040b0a06050a090b040f090309051225180c050306150c010609020a080f0402010801170c130e0106051801051014030406061d100e060103 75
    0x10104100700b9000e103985e031404900180901100140c1903046612012a080004161100460300aa000100c1c20002d641f9102c11078068502a00029002050350b00001101101c2e500541d0035910304480510050103005440d8080783e03013121001d0000f5504500402072400e0901c00a220800c42d501a0313103400c0010f043e50307609203a41494400700300c506150304010054843c0300440840009940901049601c01c02c0104103010140c2014072460a84c805d03540643c040c00121070348206441c00902190740e0300c4003400020741100703075075101240091000944070011181c8140c420341d81611503aa41c0d9080800402c0c00c00c2040b48035468501c02c8005507600c80d91350001079101161481e0008c200821440c1840c1e0030b643e65584071034000c0340b40c501c0d810071191000c03050343c0c19200b09a460303407113101d551a8200c42075909107010502664000050100b0f000054015105803040d400141c484d044d09103102d03031421401110245080d0701c00c041c1c02c3c0301c4c02901541050301f043c0b05160118200750010381176 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 345416241 1250 345414991 345414997
    0x10c060603051501080607080c03060607020a0b03041704030812040206091c0213020f03040210031404111c080304060c09181e02090a0e06131a2b11030a0206 69
    0x40d682c583c002040071241501000d94070303000d0103801010f0003950510742005020303050301030001d21805c8000700020f480c0307890b42d03001e64180540083c034413201c2e143d607001c0200180c2d1055500352921504942c1e0078500000b410202c408482d0700c016007920b1f0964034007151540c4000900300320380c00a010001050071ba511041d810341d0440080180d101d00c800107204111303c42008050142140f4014000c0d01d01074104041501d034400d80640d500810708905190131002004c0c1c0246c1c00c0c01e0760401c101481700740004005401d01d07080003621058080b000c1d001907a071640040c0d143c01813442c03e0800004001034540c1c2c0160683c45a24113080748903640754410810700c4403901410f00f140302daa81080316520444601c50b00d00a1114280451402800001040048042d030140b03055a203000f00206030180c07100424a01c0c0c48a000b0001c00c8005107000701e02d03900c8038928400c01d00c5a201016172070fa204660003408403045213210804d0f071406046a8840ac8140304c504035440e070600500d0400005a200e040c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 345417491 1250 345416241 345416243
    0x1f0b060d020d050a05010f1419061d06040b0d09050705120f071a030103030c03170a0902031b0127080105090c0102060f01050d0803130507080115090b0604060e010c060603 75
    0xd81c6541c6a02508003c5a00c01003080360b00c1030401004025035140d04013080c040d02d840e00c0c1d01c000c02c1e00f42c11010907425000d45107041508002c01500103145a800300d8200c0d060580640000511003801d0304010050042d80100c0400250070030060511001caa840040207034841d1083c1c884456a600002d0300e1a003003600d00d0703d0300360011400c1000c00001880310a001d0280a070700b1040f50752103054060418001400024140650707200e03054145130084018000795410740504224500d4403180c1c0074003500490104901078411414100a846034203c0f020780054810303901c030400c28400e2301d45195408403400c581820050100004603c0c1902070241500c2192020001d2040d208010002441c110000f801c000c0a54940c030014005552184036805607550813601a9840f500d030112401c03c1c0fa8404d12000301544203a2100154002041d006120401c81c1d400c00c400445594450103070680b0000100541c2c0309008000502010780180413114010700d040c940700f1000007890392183c00700c4602d908 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 345418741 1250 345417491 345417517
    0x11061c06090b24090f0a0306050114010809030a021c090308030f040c060504060206060420030403020604060b0f1503090c06120411100c030f110706081006020f1f0b06 73
    0x154070040750030608400d035810f40e2000c815180300b08050a2a0003907010f034080030303817244048400e18003003a59901c480c40007864002c0410091965100b1761540e0490120000c0c2c1e021441040021b103074008088180d580c624901e801034140078a05821040e80d540b9891000410300010080102c00b20b600780c4055441014096100e1001c1d04050900d00c4445409074000030822408002c00d01c801d660120b41c1e642c0000041c0e8021484da48119044090f10942c10482c05d4242008800c01062607800581d00740a24003801d0204038120403d418803812903039058130315402004100c204607150f0021001140c1c04072ba03000a541c04a440b600001d2400e0740700800c1031100340841c0c0180814081501c8a00324003882c110784c290505510110301410415000c60050306200d6000c03c0080000c0c001d41d4030301d0340398660505030342106460314409000400c003a12a0110714010031800f03e0084c0c00080c02c0000b070140500100f44900e64520104180018148024071060321801c0141060b1160300140c89a21440a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 345419991 1250 345418741 345418751
    0x617070315060c11030a02060406031802121c020d090e042a06110307020d0212010b06030a0f0e120403080c0a12031415060319021c05010f1211061c0609 67
    0x70a01a5130000c082a0203846900424295001a924841203800302c03541801c021034441d1060086824081505c6c40123900a1000075203080c581c07001041151075003845408400c1c9526842034101c0c3e84207810422a00070929610061200500c0d2107161a40588224454070200c1784c0b05941020180c1014881245c1800343c0300c5c1403001030380169600c1c0200781300c400150b00300100340d00040c055038240c40000c0c2c000c00e078021840d05030f89000e40103034500500207021070f65241007110f080001440ca0040184000d803510500b0b4284d4400410740c1020010110002c900707003070860701c50036220b6104c6100352045214030380c100b5001402880483c1030304281c0b524009900e00c0040302d15101001c00400d00600002c2d4100551004d54500341035a030007214540c00c008814200302103640007445850ba040c50780c0600b50780f26840131403554100e079051314400102690740b9540d070b4500403440824804010b014483d034400301780c91800d182000d00344d81c006480c95100321301e0800c14403204840042c1c01c40355a1503116 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 345421241 1250 345419991 345419993
    0xf0d050c07091e1a030a031101060b04030f0201110f1219021609020904060321030c0206100510051c0f06050307050a05090703061706060306100617070315060c 70
    0x5000d000c0003007441d0300c82440301040d1a00c03c40840040941000c1c200d0380d45003041110b0b0200c83c3c03510b40c400c03000a0304507800034a2500700a843c28100e2101e03c440e0350b081071004503d4a0f600400d48049982c400c0c8041e448258503401550400030074880080caa1140c40f2b21440842c40070001c000814040c968003540c2c1c5c6883c00c0c45c084014158954440540d0b00c42050b81d80e508203800c240c1421184016801610b4006c2000013401400c9682c0c4007402c0320704103229050a40c0c0c40710b40e182c1c00c0034140c0d440030890a94510010b80c1c0702c40d0200c44845422a10724000c201c5800c2000105a1140c01880e10520f0320503003c0b010145401c80310a8030261555900701140709400c0d41c03241c00050f000481c018550f003407902d00041c41d9a549805141c1c0180f0400d030104080030301a40001010f090500505a1071010311451a80d42e00021030700b040c071a10407640401c4400c1c240c4050b51041c0c0e001c07540c2e5003c842d2400e00c10b00e8040c0102510600400d40e8031030400712140d034004101c00251160350742d00e0024040ca = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 345422491 1250 345421241 345421243
    0x9090f03280305010506031602030409090c2405070f1a0702010203150a0803040326071b09020306310e0a0b160e0d060e031317010507020706030e0f0d050c 68
    0x40d201c020410b240c6014010311050b40c420040e29401010501400780f5000c41030012420340c000c07580306800150074910650204100700d44028142c4100003c1031041c9086000c0461029645011100100300100070f0980031950a40b01e40b4541805414400c191580701d202400000c0c4084510f01300503507010082c40402c403a59018981480e4040f5011801c0d541003000080e1280704500c402001d07450414200d0100c4500e068203142540a000c0c4407a8a40c0020f00f000b00d2180b04030302401c484c0540d03000340481c90001c1c45c4207480c05400090081400161907500c45c3d25072031380c241d4880521800703140180000001500a0281d4082e00d90007401c2609000d01d00b50300110300180135201c9400c4100310544043d6408100600589030450f0005041c07051800d284005220322500c81e0841d0000040504080204003504000c03980c40442001c610440c2e031110034202c0e503060300e981006030405c940030060346200750814100d00d520310003510005d40c0b1003118030349888890f190501c0400c001250080c88058 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 345423741 1250 345422491 345422557
    0xc090506090118090204271a0103030c031b0f11130e1504210f1e120b04020d02030f0f06060a08010608100801020a02071e05060909090f03 61
    0x401d8400d641254144103078003005064840c860f01c483c940c1c07070b110f000c150b54481d00541c40c1c080d0341c04420000d084020212019102d03458006544036a0019500060000d582501d03a0480c1d40559030400e0f0b0b01380c181c1e800c64074801030f005140c50541d18008140046004140707004240b52040e01d028082068003414886288000201000d495141c07080382d40e40804041240c1e00d104558001044003580c0303615019603011840010b4a80c41803001e04490019604000d947c0c4001d0440e17261001245030041d80381c94203000403552000002c80000d005d4044a885401404600d6402040541006180b81c00030080740c20455541c4025601e00052000c0b15240e42d0460f90407140c141c81007441c05030003080c0136101c200188581d000304040039001170780c41110020011702524051009554503001701500a40d00c00311070140141f2850100704441628010855074012103001034412410802100100005501d0007000c101581c0103000082c07003c040148000c041100a0380c01840300300344070f0402122001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 345424991 1250 345423741 345423751
    0x5060f0c0c0f0c1504050f0d03052506050c09010c060b01090b0f0304150501080703080703050f030a0911030102130b07061503030f030e0309090610020a02030d1115060a05150f070c0905 81
    0x1103005c01080c07105c2c0e255800c8502d180d071004d840d1740410302074a15040715207101c1c02e998030081c01c510784074030440200c4040c2840003180c042c0806100c0ca032980c0350000d01e54410540c0e118041a602c00c41580018142c4e00187c40d15001410080d210b1035990305014482d50042d076000104140c0007082000700728501029038070800d039601c0708010b50340c1050710340351340e491440c080a0540403022580c0320030035100e4011079050320205100345441c0e04000030348502801001200721a41c1d840048040007034103052090340c2c07071849640c0c0402c408034502010844683d02258054402613242c0c200e42d00701102d9280d00000840c030940e214002d03c130a1003070041c100c40d000310030212150001c1140c21a10750f10348440541120007201c0340e003012503003040141d207001c0e44514029054041c884800d80d0603034000104100d800802c105807042e071300d020206c03040d00302d80441d201d40d80660385000038081030401c05442d5030500f8a01d0340080c5065014004080107800c40202103c040b0406041805034013a240556a009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 345426241 1250 345424991 345425029
    0x80601030e1603031d010504050d0f0213050105031b060318100c050307090f050105030c0306131109040c020106030f0b190608100f0905120c1009080a0f080405060f0c0c0f0c 76
    0x200d40c05c5000213102d48110321035180706415180c001001d200034140320500031a4010315065810f25001c42e130b040a840c0900c034840c8280128088003030b044150940c0c0c00c00c440d10080189266076200b03030161030012075016115a440c070400c521500404414400c1210586c1c10b929020b403a4074100000800b0a1a20b42150741c0072009100c1c1000b159030420b0680382c000390b42125168583c2e03541804a0030204205540219050a003030070b08842d0041d000040c0503081060b1402c2c8003811407007100f40c1c01c3e10a071348001450010b20900f0003011030700e44401c440d0840560010503503008050301c407250545521b40c10142c210380000035131210068844c0f02c4c481e0712502d104400d022314603068640c16228040e07001c0b28000340d000041c940b040e100040c04004c0450001100c20040b050043c24402e6107a00000c3d01a0049030000703064494280c043d15100b0312442e80134000b06400d6a507070b80812003040c4040d09129280c08140000e00303005009102e412096a000801483c660401600700800505901a040c5103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 345427491 1250 345426241 345426287
    0x10504050601262503060806010611070b030a090206130f1d07030c0203041806090f05091905070e0702031207050f40090507020715080601030e160303 66
    0x100409040d1082c00c483d44115064143e80d40d484030410040180a080f5469000e07100d40760340c2d10750564490410303a640c0744121055aa281c034416034148001c616441c0b010f900030b14041001e024240000c5610480032040403032030078034070b07400f09815411104c07005001c035010080c14001c208444003680001d001c119030321800000d22400301054030902034021410152140c0380c1c40c104500800480e0000c100c1c144c0107800b40c42c1c41c0c401c400000c015500a00301000e0404555209220150190034011888000503004a0a80d5035242e0100e10340c0340d204407001e00903110000386c209045801e407842001c094010303581d503505802400c2d141680040825040c414103110621441014509841c1c6c80b0041076400c8892a004178041c030313007030002024111510b80345100000b07003c410340c0c00003200312001c83c1e20070f11894543ca00242d860f80103d000d000c80144403103009031140352144403802d4102c4c6060400240c80c4000900307030f906002031081200c0081c000d05a04008140d40883d207001c4c0031f4200188624 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 345428741 1250 345427491 345427517
    0x60c101109011b030c02090108070f150918090b010b0a110d0f0c061d0c030d020304140f06090d03030e0c01031418161202010f05071a0c0c060a05010504050601 70
    0x450b01101c61041d82d00b07090410030190406001c1d121845801e50020211581fa695904049035219114015000d10040304440000c506d500700d00386102580681c0c03600d0a00500703005160441940c0d100404960548410140c408250312036001c90281c001c10203425541c2080e040050070042c1d010b9030a0f040d03a0300c00e201e04050300e6800101d480b244e44440c5000b41c81c07040c4508141c1c1c09401143d20b0615500303000441d2a27079214000a03101001e1000381c050b148040c000d20030070303a240c3c0102d04c0b500c01c864017461100e19840c6000c1c000500740340c2d40184042c0c2032a1140c40400c90f240b495840840102c1d60310280322a00c408200840c00040b0300c240b90520100504900348075803240042d0444c50110000042c5203500f0b03034248066400140707204515243c20b695560401c6048130040800c0e8041141c0240261180744120110b07036450f500618503c0c0704110030040c104164400611403a0303910020300103854001014030030140100883ca8020865504000800003100d4001d0882da050294885200c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 345429991 1250 345428741 345428747
    0x5092b032703111e010506030d090b03060114210103170c1218150d06060f0f0c150f050a0e060928020603180f071a070c05060c10110901 60
    0xd0006a41454580040002089003d03d40f0313100ea00000180058a2140000c90605501071446450f0880c2162510015802c2c151642121401901400002003000580e154000c104410610458005042c604401c1e040c2030800c000c106c290a541c0c0384000c000400520003c0600036050040840071285891b412022103a5030b038403a40340d9640c8035074002c52032403030360300c98480300d001c101c080036014016141c110740d9607010b070703512501c400f4181914003003010130b201d84150030750700901800e5141d0b1104100f0200c42030b90754202c01c0b5011194445044581a01d0121902503c0106d400b1050003007960304042c5008001d8038101103031401180d21500400800700c0c8002407120001440781d072250b0b04a42c0c2c0340382c10744040792030b400c020b504402c4c000144001c08140700d94000a44105009881c81800c3c0f4184013522000f513440380860b0714048500305460801400028101c03c0d101e00f07042d202d46071307440011550300d400080006041e82c010942e41a00c0d0240e6010b080e02107980c044205180950400000e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 345431241 1250 345429991 345430061
    0xf050a110409180c0e0109181a0a1d0a0201030615170411030118050c090402010e060c0708011b08100308032221021b0d0605092b03 58
    0xe00c601a20380d910840f03809404a4001540c1c1d40240c1c40402d05500e500f00d075450400700f885140d900b00d2902e500000c20308112014200c100d5440f8403100c902a5052500c403030110b1014104424940da0340d0f41c407041d2020900c07104052506424081c00c4002400d00014045665030752100304036000355654056250b501110f040550307608850303110403684440c1015403c40580e080c91503011341c6401d44050007034000718100c142c114802d00c2103600854142c030912460fa03006590081c04281c2e0340034031180c18a80400505484c11410301290760b001e50b5005c0c03650941d0ba0038080344a0000c420036510841c51b6002d040c1580c440114801d1100c0f8521f9540e5844807071100401041c48a0b40645507144601e400303184c84030015410855a40c0b1624002d000c0e5040c26179858960400740c03094040f0b22001d040142d0712400070b1200146680352200a986901018000003800065940640482d11451052040391044400115482d403203811120040c060200c604143c460307031803a12a0350001055494403025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 345432491 1250 345431241 345431249
    0x50d030c09030c0b03040b093c1b090c0a08010308161a090d090303170a110705071d15010f2c040c0509010203030714041205010f050a1104 61
    0x5103840315828100c980715100e401c014003808400d400002e111a60201440c051401807604484c141c0b0750202e80d50780c031240c2c00034800b82813041c034040548103101c1080b0114080b000a40a84400d000c07905000d01b40fa207040c0003001241c14041100d0141e003015813000340c1c000e0501e0800c80c41d00c1a801d402034020081440018401c800000c0c5810210036100c4078481c000d07500ca154964107030034021440070f1140f4103d0b58001c10b80310b02c1c3d02d041c140c14450501074041701d8154682d4290b160003403078500800d5400074a002045034441c06949480300f42c0c00001d00c6410700800c00762564508003010419030754088080e40c100b02c00c8060901c42240c003590306c1003141e12000d09040f4400d0f00c0c4d0000541d4800d00b103450840b014401c210781543e03200308101d0122443e01d400c560030803040c510510195080d002d03100449005070310034400200f0340d0f07010701440d0301c4842e258142c15003440d5031800000820810140c0c1140d20341d4403811040c040e44858000e8a8100c002004107228805070030400346924080d03441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 345433741 1250 345432491 345432497
    0x21060927081e040b0910180b0c07030807120e0a0e06010c05070918020906060403320d050d142509170d0912080702130b0d120f0507050d 60
    0x1070390b000c20782c4860041c042c2c060a811040c9464a030b4036480b040c4980c104032070640c001c811400040c00d403a403003080c4204045000d4000030034154201203010849410640800740c2c0e5200341c0001001050302400a403c90920402c01e81d405126003090050203065a15015402044500002d100c40c0c41061140c40e8000c40a01c1e00b204a0092030401600d041c1c1543d0203a00b041e40780100260a86020342d038052030050003901c8442c10b640318101406854425440050000c0410201441240e06040e002c500c0c41000c081c2400ca4400b100c004807800d01070f25010039004508001030184401c00d2502480c0c0714a44030301410601d911340344600101e060004426254a0b55260002e0240a80903000000141c58685105a41e1310101d02c1c900e50303551034850602000c1804040c0004034a01c040103c01c2d0702c0c5920000450610007160b00340156556007400381e04c50140c0f2820841c1e520f8072140382e9400058060a42c2500090b0b10349009401508101800020400104a03000110348002100c41c004d101c549 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 345434991 1250 345433741 345433747
    0x111507080a140103121709030f221d013201020f030c0706020c0a03031707050f030a0504060605060708161112030306031c0e0d02012106092708 63
    0x42601c40081c54002400c180205003070001200b4407011100241042e44513840e120b10000c40300c2102d40b411b00c000c4424030540d0b40204000000c0c440300c6005840d0040101c00980c05409018502c3c00f200c0d1b0301604410400c224249403130103480c0c0725154250042038601840c40c0140704604a480f12500e00d046030380f500e494500a4041180d20802c28003220000301e0b016651a446002252610b0f941d403481a20b00500c103001c115805403812038140d20441c1c1d81600c40a01c007883da040301740003508000f0030002c00c0c41000c0c0f181c010707550b881d40000d41c81908440c90000e101e01d407503e0981c00300e0780c882d0040d900464003489030380700040d081402c076017048440c0c2c110080000c000b0301c0d200c00d10711811000f4603042908240080c4030501c000001c0e40c001e883c21420b83d400404c089180e001c0302d1204460400c0058144074502115080594207010350500614040754940c803405144889240441802d501066236407004000d010850310132103220744140c41e81d080c1c1c1031190a80044013540569009030400c1400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 345436241 1250 345434991 345435001
    0x7060314130212010e0303092509090305040905070e0a081b0d050c0316090e0606010f110a060c0203040914040809010f170f01080d031b180b04080703020111150708 72
    0x300c02c40e075210803000d00085c414400d0faa8200d5480343c20a6540f0b038214420b00c516045816450311401c0014640c204500e641d17a440d108980300030781002c00c400d40603c00200404124003545010b01d41c414074850701c50544010300201405102300c0103a1040100c2e8208103505820000d8409000f4030300001242c06035800740c0c0c2410018107040d21280d007580e00d8032486d04c0c140b03003600c1c0002965003141e0042c442002081c903482400f40d10703924100c0342540010040b5803040f5011340941e0505186000d51011500390b06110750780c3d40c084070758504039900903900221701000781d407800b801440060a03120303040c09a1410140e0341e440032801516003150501001c6500b0100795072003103e46012441c401d01441c4664100344074110032102080c0100c0302c0500508200c00002c5001303008503041a515400342c031045c0d1608600896100e4400f001c07601840410b14000100c02103004e000e03201a120f41c001030060310f850340c8000360020b11101c00c21401074001031140b905030607000c040c0580c841001e090020042e628 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 345437491 1250 345436241 345436249
    0xe010506090a050d111507020315090c090106080a0f060506180d060212041e2102070803040b0903250b13080d030b010f02010b0d11030a05060108030309070603141302 73
    0x18503004150002c0d1922580d0050103014880c00340b0250040d600801301150300307428107006106403c0040d404ad405961007050101c0c120b9681c5d9400400340d02a14550314180b000100351000aa0103500040c551009020040c0518071441e1883c80b204c850401c45280380401140040c0291141c0d0f1165249010201400d5141d444100762500e074000b030f0440d0745006850107991040400d44050386d145e480341102d00d001c040400c3c1c11082c5e0035081001d038280d600072003505c510011502e43c1a5401c50107440c40c0001e00550800144c005010044045a1580c24a0060618001d01407040451541040c0350703055514403a040d81c10b090300c1c80c41c9003243d920440d10b0700751400d80301d1035407084565208210a46c1c2d12164154411309001600340e850200450000340704078280d030b40e00202164400da00c00050000581d100c038800444c00b501600b030b2804450f00342c950303e051030002d0384854856080041046074440d420310200026007002c3c101040100e082c0c50701012901c8008110100c2032811401100a41d52 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 345438741 1250 345437491 345437509
    0xb040501020c06010303090905060406060c062c0c030f03030c04060302030a0216030f08060a0b0a111005041b080d12021b030f0d20030c0d0e1504021002070e01050609 73
    0x2d01d00c003201c0e02c95035a4070b002003540d80a803051031165484d20001c64042d14050280100329842941c452080881030f454400080c00f28141c0d02642110b2403c6070f09141094034192021200b121029001c030803c01c800381800c2940c00220709020350410000c01036480407403001d5506480381e40c680141c40b651046030460081c4650642541d00607500b116a40801d40e00c102a00c010100300d6503901082e40303801d0103020050505010300000008184a211032061058042d0040c0c2000d0710225004024100b910310201c0310291002e4444c40504055001001c40303680c1c881e402040e0540c014a102d9001c440d0084c0080380b202c0082c03c1c000e40000d0030b80c034045280c01e00800d0018428040c2e07079460303e240c0c4117a10242d021400c082001410f006103005019001103080a80650007180030749113903181ca800e019280d00c24401d05c00c00030355850806141c480e04220031404840310440e11401410300740100400201d05180312000c55001c81410300003241c0491156044460980c0e1039502d0309812800200282 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 345439991 1250 345438741 345438757
    0x408030f0406060b1b0d0f14071a0901150b07080316180b1905040e0f07170f0a0e0309031c02030f130920300a0504060f090f0b04050102 60
    0x20401280702594a403d04c43c444091000801c201c03130004d0b886c40b200341c0b0316480d450003000210300d80c42e41e4400d88505500040c040c1c036210b0b0144d040310303000642407400740890a1b1030081103a0354620180c045990301151480152030000c4540f418010140e41f035080d1803100800060100c0c000e03130041203150b4010403d407003c200c1e05150254401c0c1d22a03c40c0641600310b41150b26a402d0600d115002d8140200201c80684007111703038001240d5242c801e2001e101e10050640001c1140d602c0711500008880e00c0d40310b002d130304403c0d225103141c00c05c00e1445040d0750b2030300c00b84c55941e0000c1080481070713640060f9007d04075034121803508134006044402e07415800b800426503418030001490000800509995100b5075090a0041040c0c4a1381d490007140300c101c91031060b1300c2076010000990100700d0f818540e0302c0842e40d210110180d00101c21182e019100a66528048236240c4040c4030420255000c0c80e8001c586071a401c019241190b103580080881d0360102803d900c0341e00010809000d401e4040320004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 345441241 1250 345439991 345440009
    0x1e04112e0e060406020709020a050c0d05030108160e04020d060f02070b011511060118090c06050901121a01051303060504050f010507030605010905121f0e060a050408030f040606 78
    0x2081100d404140d540a0022101002400300d5022201c40d01e0400c00395010748040798000e102450a1003c0c0341d000b0740c41101c03414103006041c040010803c1c400c0000d052520011f544207904e03545041402d61070300410500a07918500d400000740300f00d05e20788120641c07041d01101c2c04400e035041410706400074074106281c42c10702d40c0001031340070030311495802d514101c5201e0300c440d13150710020480c21103c03000400300440d4550016401001500070b1410209507003070b81c04500080c0c261190351081e00240d180d0340280c01080000c184c2d200300d507800610304620040300c4030781801a240c24440c008440b03081180181d06009000c5522900c0d045034100c0705018651000041015003042d01380195658101c0140351240e40c28100000c0c0c0640c840e0280c401103a01c10303140c03034501c0c40c106010000c0079000d80308000c485124200609d04100c1b0b800f58102840c000359400010340201101e03603d4100b15001f030124007654100400d0200288a4800b1243d021603190842607403501c076880c00202415895100c0c00036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 345442491 1250 345441241 345441289
    0x118060510170f06091b01180b07060f1505030d0c030c0803010f0302030f010b09062e0e1008090a030507050f07181a030c06180607060209091e0411 65
    0x1c2c12000188003510341c1c1c192089074034650300c034614107580e800402418100602c054122818a5005851044074800c000101e02a05a140d1301c1c2d20080f500200c00c1030b01c00380d49800424039080c009100340708141220442803031a103070801e0003007a610100089068100045200000c080c180b01c0c001a4400ca9404110981d803565117121a008003582c50000341c0c07090056490ba0b404622052091056802d0301400d5415136a0314107040110006603501c84450101c030250034a104034030020380031a0601000d4444041c035003244801c2c08118081c07650400140b141c14401e0008030100091060500ca51519100759a010a0300d099414800c80b900e40301c107240705044011684044030354aa1010b070f1150001048425a44800c003101c6503030400f1301c6601500103130003c0810303041034002003040010701e820081204510301c02041c0245d020080070741c1d020b40d010070f0f082d4603032900840a603044601c9440341d4030104e160340d80c4080300f030740050300040000300000d0007111183c8544115608074140a85510340c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 345443741 1250 345442491 345442529
    0x212030c04180c020105011d060907030b0d0f110114031f08070b0306010e0a1514040824181002090307090f05040204060b0c03070818060a090e0105030118060510 71
    0xe42402010b00f0b002d54280b00020903114403412000c51b6000c1180b0000016447c2d86043c0801400301412400401da1038030324509003034440d5004420018420207441043c03030218240450380c00c0c00c90364040d0400007549180600c00c1c25800580c1d80081e0f2681c0c04500807240c40840794601d80c440e0b03002d50100c1c010001d002400c5041000514410344082c0c90390062076104404000c4280e885024005946107091005c4191320710840140300a044030003d0700c0d2a1036207440c5500d1038907020710b14022142d02e84800e0031400f40b40c0151030780d802071041c550840307540c0c540b030a5090f1900b07031000655140a078089030150107a27808001600083c003051004022144005040c04042d0030300300c80c00da0049040101c0021280416000c440c4100f08080c083e41c10991160340b4415283c5c4042003030440e0308405403e5502a039603d80080001030b00a84446607400e2401c1c0b110061644141c4c060340c446d034507100c01c65110140402d80c2403241b590000d80043c203036448004021040307000380c0158082d9011050841 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 345444991 1250 345443741 345443789
    0x120f09090b06090a0806091c0f030903030b06040801020a0e120a02060f0403150608011d060a02070c0e0a0207021c02220e0706020d1209020d020d020303160506040c12030212030c04 79
    0x98007d203d06400d580c401203d00d02454000b02a101c0c003000000c102c0055400350300d11a0740248942842803402180d8005080c0015105801941007141700da50300246032007174950410807078102002d09a030300172080e401000c6aa6241c010f1600003074090400001c8804a9a2445003143c02541c6d2003000701d040101d180304114001e2615000e035a045600c0d02e00f140d040c61183c50b0030b00780110317510802041c2d55501e45103603c011b90424a003c5406d4040210003041c88001d040405104051754800180c0f80c180700e00410000c0a480581d110002c3c00340c00d100345c056240d904440101344688458901d41261000040d00100020035044406005100002c42c01c5640451001e540000c59610761841d481d907040003404840030580002d50148882207020011b003030010b140700c1154002410b82e400e0144140d55803507031282d0f13014115199002101048104803110001d40082c00c400030083d6078001a40c0e8002e95119010051781c4521032011000429100c61a011900500300c1300e68522810407254802c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 345446241 1250 345444991 345445003
    0x6060d0201051b0a0b0f1515090919060b0301151d0d110a090b0607060c020a0503070b06030d0806060702040e07080735070306150504050112120f09090b06090a08 71
    0x11141c40e100100440e15641b002000c003402900d8801509030100d81510800050040c807825610000c0c0040c40348607000d0342e64621451044040c0034031b1080300f0030040d12400849100390402c2141800a2006120062030115011079800d41c6040c0020400303e0f45011540241d80703060017551100b80d089450042001c140900c04000c0d5007a10181841629440d03140103503884040c10640158080c421000070401c1e40d0030610381c0044a0059030300002d140e407140d6055a111943c1500d0708000102403040d941020014160b0b508418603020506060540010304d0520524101a100310f03103034140c10b1002c010602504006210042c121004141d84189141038507241d014400e400c84905a012480000c9980c400301c0d143c00c0c0389020344034160031541c0701c4004100354100001c0703200f8020000b00d00c0c0d841e1440f501d4040d00c590ba0745c0c0d124000c014982a00c0001107900e40e00e00f00070242d0382e0a08401d40061144055a40b0500f0105200c0340403008640580030300130003203502c480b0103100011b40c04808508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 345447491 1250 345446241 345446243
    0x90602070302101a010212072102030408150f060d060605060a020d0206060901051c0c0506070f062003190902030a08040e0106023702030f01050a0b0a0806060d0201051b0a 75
    0x1051240c0c94403107040702580c00858485178050b0700044a50406408041b004004103442401041c4541c0060f144a0000603071028640700903a00001e0148100c410401041d01072045054446c0d100e8580120141c1040344094513090040801d08001001c0142c546c20003070151001504094413400c02c002c0082da20350400003c03134054040c20010a00e87e080004400b07058600252446442c122500b40c003041c6004030700c00c1a29082500c0c80c0214036551020020102c0500604240b400406142086001c580290305458000c95201104400c41c681d070000b641e52040018512401039042c0803080b1000d40702c020070095040c058021403e0030414500b016201b556114202c9145603071300e401003660388120000000405c4903110540c1d4241e414494808200c10040481c4204402c0c1240d02192802e210581c081780f45035110300410410b020507100d150301d071600895451101c41d02d030020003600e40b440900340d00d0080d0900c403840402e69010b0800c840b020300c14040d012010b03600606e0f111f0b8450b40d1902e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 345448741 1250 345447491 345447523
    0xc01050f01141207050d15150303120c08041b0308040b0c0c060c120a170405010e1006050105040506070503040b040308040e0c0901122a0207080601050d03020d0c06090602070302 78
    0x41d00499074100f02550101400041c0018001a400c10b020001c0014081c03d085540c0f20200000080880c85409001c40c01081c8404034204c250030f501d4007421483c52141c81d111100d15042c04041c0d05540001d1040d0455000500084c041652501ca120300f400c3c00c1c0c002400c40304000800090800c08000240700d606000703400d070750040c0d400b8810091a4419484802d07800d81c481800000d017030051100030403d5103200e00707004002c079440c00304601901d201160140c070b140c0d55074088480c1c050400c0c07060303890080004d441000518180b0f070010344103025501565001780c0b800718210040100800854000e0304540c0041d64543d50b507450b000040f50310501600202c0c0f988100031580071610f48007034403120302d4161a070040c0e550b210002c400040c40c0380021034054041c2000c10074502c151004030080100410350180845e50305102c94940f902c0010b03404940910004061200442d902107410003c40c9080c0c60259100500c9081040242485100103804c1d00e100068000030550005094610084045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 345449991 1250 345448741 345448769
    0x6150c0f0a0606090506130b0d021f031a061606180f03030c020105010f0302090a110a0210060b04050901150201090507060804120c050706030e240105090108010c050d0905030c01050f01 81
    0x104480085c0c4105940c0e01360800031200703030118499240d80103142c2c8c115025100755500f0310540c0024038849400100403a41d5089904004030a0360b0501030314000221000380d003640b242d608408a00d00d44142c60803c42e00301142c1110fa010080d90342c00c4410b204c2c0030700704130324142d66860400f00c501e1110340408802080c50640c1c1c00654a0041c05014100ca81d4008040c09591840e000e019060760002c00480c4241c3e0303240c0400b0030841c2900e002d00030020340b6500030541454000405400c4403a9a000140c503880d05200400195a40116840c1564401144014070380813914040e4050300c01604000c100d070090b01804aa00790348a188203210f58003810311003e07091040901529000065030300a41a9049400f0510542d40660440c0b941c041c2c610080751080c1300d0201c00d0040007106629104d40e06c1008100401c01440c0208600c0d026003403440003004032449481c00a0b046100d180d24100040740c0f101e40c0a4207010051042d500c80d108440000c0c4101c0c40c05040341000c060b024041d03242681121 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 345451241 1250 345449991 345449999
    0x3231602060f06010f02010213091a010309020d120c0c290703021510050d0f020a05010807020c0f0a08060f071b170708040308130e070509030606150c0f0a0606 70
    0x74001d004000d41906100b041d1940e60046604850002d407010640d0f4080010a1200b008418028001c00c46108001143c00070110300341c10042c00e11030710b1410581844200e40159881d09100704805510000082c020044810151074040b942d02026240018011f00003685268901050400d41c2110b0a10185940a01c0d07240c01940a0300e41c010380107a10001c0c00511400c0c1982103d600b21184241402a803681e84000602811040d40c0880d030014644603003d04608250400c031001d0007003420105410326112800079a40c10715002014441d40010045201130344a02d0750001c090b1501d4015100c10745068007440201c100141d0fa22400216403c3c490307242c0800c2e01909490240d4410629001400d04c0340460711942c110303600654000508010000c00a8004802020020700b03088441440c1d0b8580103e241308414000d210b9803d1003070070890915142e50108000b0341c0074500304c4540340345584502c3d550703c0034013403040444614402c0390814040c2d00000202e940c4203902c03031030303040c0300c101e0701c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 345452491 1250 345451241 345451243
    0x14010315080c1909060305010e0c031f230f071103031e0603070f0f03150212060d110415030b0c0c0304062304030b0402010305160e060a03231602 64
    0x103244540110741d0096440c140c1607282002d06003403069182040c40660a490383d01c0c40b000c40d003842d40304558580d541d80d021903c4280a01c080708543d90110007074a88860b02884152004400d5151040358940e5442034588011080300d00c030a94145405200c40145414481c03070312100016111900454062000400d9100c0700108403403181c180c114202054085444d40e40101a01c007508035503040c042c9520208441c810049800024610120000700c010716604110b03050b20300405203800b42f0750040004582d140e050860003600100184c90503801c11400307041070206c031101c0700200e03540207040c01c0c0f24250031150845907005030303806048102e1803605d88101c090304600c5448880051500144400c000907030162609010840000100d15403080d000e80590b18503038001e07041180d20310700c14001d110540d41e2502c203456010110207001104a03966a4000d02100c00921081d4031036840000c440421a21030303000b00480c0c5103913a407802c5016403c0c21040f0141c00c0704070b80380242c01d500382040e028081e00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 345453741 1250 345452491 345452531
    0x221e0809130c0e210a120f1805120102091201051006110712020303040b13230a1401051209030a0206060303030f0103080a11030a0c14030a0e0402030a110301140103 72
    0x40e20f8407001200d403001d50600c00c004044402c442e410000c0d40c030005180c48410321038400424482e9124410003500010050181283d03038001d04108402002400d9514040c0c80f044803d8031000c540029440300e0000d41507029104420318150440016000c120f21403070150801c4d40036041c2170380e102c0e45564903407800f2034800204c480c001b0001d0b4001c0a08221040140002108039070018041c1d81c542500e03240419155400001c0c011140d01b030171030041000900040718074102d410569041c0403150100c2000807221100f80c0650192100f01800402d0b050f0b01543c1200c091890060210304249801d142258072a0003200090015004500c001542d0349804801c4034400c0e082d03643e0320b140c543d081d5260b440309904817000e034105101502c901c05142c80c8003003019001d04900f995031381007001c280d4a0300e09a0148400d00202142c1c1c0180303c0440d0a60b001414042030310800d4500507100d034bc80c1c440c5403000d4000c910022180c0319000002040f4268648014031403100203890900c00910341d40b1068066103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 345454991 1250 345453741 345453761
    0xc010f0c0201081503070e041217010b1c020408010c03060f09050603030d0b060702120f100213120c03060203010305060411090c030112020409140c0103060905221e080913 75
    0x104440005110303c00f440d030115400404c0501290111038030785e80c02140d060810f580942d108006198240b940651000445141280031740e40d402c42c81d45000c1c940d5a42d8099103d1010000c1c9180004602c0a0710550586000740300d000020301c6526007400d07001e802400b05000301030ba0b40c60315070b6000c50900c1d01401018002c041c040c0080d40380c200d05e000780200078000c607003020340c0c4450300b000098050303910744038681040240200601005c120240700580b4100e02c003025030103080d006201000c0c0300303840a07404101300e074070000d84078807142820314001c0d001c14059080200114400f200100030302400280952182c0e1061032040501c2c001501017005620302100c000166520420040c801c0c00109201d4021540c405480032840207425521000c0c0c0000260f102c0d80319a105007510412503034940122401800c0c0d1810811a50801c99550b038a819440880c041fa000302c040140d0080102c1000c000c100e01c07400c0d40c0407038a486818901480c0652000350030038820102c0880f03400d1060118441e0389204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 345456241 1250 345454991 345454997
    0x60e0607050c01140412060c02010e0d0f11030904020a030b030610050f400f02030103020d03080408070816020a06030216020915030f0616110c0603100510020c010f0c0201 75
    0x141c0d01c66001180d42c4040b04420049140c010b000008a186c2e40300746c400c4c80c86110342c00c0850100b1022100a08480c0303460480c0755164000f62155040c0f6811034003001900800e450129410b4144400c1180356110302c29166800510003c7c58000790366056211000c841c9044041e1195901d5903180e03e1b1001c003803030003003503845190740416250600d4180185101101d02d48406640b0314000829041000e0110120f200880d1035003a03004200b00d914071550020b128042d00860465045801040d1080c0604a005042c000c804010034223102071401594165584058540e60303540401d4041c81c0d0200110000724051034035403d02060b00d40c020f009913801c2008a0507441c85418140d02001403041000d081001d210a0301108621951014010140b00b07800c42070051416080c10442403011030b061714400010000020b00080c10381c0c01c040303400512003070700b1210703030751a51520001c0e001d142c901948145d40c0491846207003400d250b000302d505070b40041e00741c031000100d4040341c10545016440002c02800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 345457491 1250 345456241 345456253
    0xc03050d020d0e0102070b0a0c1d090606070206040f06093305090402210903040b0403060b0f100e151c150504020406050c06010b16080306010e0316060e060705 70
    0x3a80c000e59025001c02c4000002c08118180d44003101400ca90082038140d1b11541a2010020f8000c0305024001140c0000e14101502d590440c40c100503400601501604c13034802100898455234130300051728106a001003000d551540d98032000c005800a610a070780210b00048400500300d880c0c014010380b6118041c042c210300500c20184508002c000640c01c909200062045c48290b803036030b10141c14080c0000c2c11500a07480b100500c1e40034030b00028843c500075481040148600c5803800103550440c0c0e40682c001c80d031605600b0005441c10036280d142e6030400245460544450342c040a071b500410000d40c0c24140f404820718098565115212a01069082e24030100d50001040d5100c0744100c0b142c00703948040700d0384402c0002c081e40e1059002000040c4081440f020349001172044500404c003076000d0308e00c2c1520500d2494200c018011021308500004000a04541d015031885403201100509488819030014181d96205019006040004e01f02100e00310103410000101c0341c04a07007003401082 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 345458741 1250 345457491 345457507
    0x50c03040f022e030218060a020d200102030703061e050a1412031204120f0207060302030402031c0201150f050a03020607030908100906050a050f0105041d0303090303010807060c0305 80
    0xd40340040048400b40f0048031007028207050950001c0000d0860350ba00541c5e1042c00d09048503200d0328101c0e41030f00c0750008000969040381c0002c0c101c0d86203003081c00d10401102b040c401040b14010021840b00c034550000007003048840e4940d00544c10390300b040ca070f0000041007440d002e200c2d4121900a1a030840700d611018072214060b80302c58000000e00504606d402c410148a45055030400e6100000200c4005c042c0004c010103c40034441542851510000a1501fa0002980c9903800e1080b9020305030b00101040070754030140116207400c611107400400c00c044c6e008009009007454010000c06041400000c12900c280c4030388403080302c50080020f24814115020002281d00081e021402e000320010001500c0f030702400b4503002c2c0f00d0040c40c0003d10740c0250901d90b060302c0380100f01410451403c400c0084006500540c02d0555005440005048030400301d0f0501012005d100c1503d41d10011080000015001005506903180385041c1c948880d906c07002641c4441038020000d0218034140700500c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 345459991 1250 345458741 345458749
    0x2040f0212071413030605070f021b0d06020403021c02120a05030702040c030e060106020c0a0b0307023004030f06060509010302060304030305060409120804111c030305130b0f040501050c03040f02 86
    0x1903c1d02c1c802901d06450201400b41a42005410b540301326035580d1184d00f000f4240703070092040980b06100740007a10301404841c1d4082c500b12100e41e5418881d181801c403040901680798180c03800b85074041d1041c08410456002e4146808400c1d004078800d0451525501d6141808209200800d501800450404400340d0800000d0174281c10400d080540d203030401d100354a8200724090080415401810038020040140520345001d03410030410450b0800c240002c241c1d0004d01c0080e0011000440c1c44910103480e043d014001130040d40c82d81901d0041008020b2003608000110000c0c41082c0c00c11415640300c09115941c2d500b444042c0d41f1a0080c000140480d010340c01c80341c0c0c8008010800161500710703a0b1501d410b05101d440c1c4d040011844020402040005803045500c24401c40307001480041e0110805444403590500030109a119070204184415906c800d580c0d0030b81c0605007152516010346082120901207070305483c19800c042c0803c1e058808441124080c54000ca0359031060f0320075400744 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 345461241 1250 345459991 345460007
    0x120b0603011a01140325050c0f0105040b28020a0e031009020d0212010608012909100501050a050c0111190c02010e040e190501020408070501111b030f0a06020702040f021207 76
    0x100c84000da0b900200006c07034414a155001484a481d42d0b600d91420140c2245015281100481e09030324040910011404c1b104a103944501c0c441c9070134001d50759140b094951004410910b401150000c038580b5541900204d034202c0c00c5ca019030440d0281514056040252102030300042d41081c0c8c1d18401e6000360819400260351041414004141156559043c0382116203daa0004c4a114844070304003410070340d50020000b40314200d4104e9000c0c01c02c40400309800d11a44a01e6040c0b010020303240b6105406142640c580d009010020010315040b240d1a01180d4003000420900702c5d80740c509180c02d58054001c43c4803058040e502e220203400482c1c01d0000078044400071764105d1113260080320b44a0480581020004d203c1c50002d603d981ca004150380c50300d4269004141445031700b03500f40309540c00010b01c6541c0202c440301a035070f8041040700424140313070210501a903d806004140d2052101ca80c008280c03c0e03100b0344040018500566909049000d0410000c440d110f002c0c0101e0303003441c4102c201c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 345462491 1250 345461241 345461251
    0x50d060e011e0f06081f0603050a0e01020a08070e030a0b090f0f030406050403030302131e0f05040b010509060711090a15060804021c060f020711040c020a0302061f120b0603011a011403 81
    0x1d074903a1207881c942040b5403617030550200c80040d88500400c6011020bd0040042c00000c6000a60810b4005503020303040580c004c00b080108030038a88030114a503410844006015008804140c560414941954449100c09001900b901c12038804e1200c81c880002181c00704c1d031281da0381c50f041600f9940c08401071743c400391601e5910544c160b07002c642d02214018000c15000c0e45001e441c400e510744015040700207802d6200c107204601d801001742003645c0040845014403811140d82da590005490040c10041604409070f0704801001c041100007030b001d600448a201c5400402031840741d40342c404940301242120025084075903284070700c2d0040c01c070281d04001c091058901007032a9041e101114221703003014400340d80035050541c8003501401c041c4034010ba40c02440c400380540b060300340c4bc040d542d46800340030041e0000d03881e1594140c103580074903004060801c88440100003162030800b42580c3c10162525403107546801c1d814171900c401002c0c1046100c0042e11005403001003000c1501c05900014a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 345463741 1250 345462491 345462511
    0x50a031407150201150509060109060c050a08120f01080d0c020d061b1d03010603081209010b031006140306040b150319030c0506100b030105060a050d060e011e0f0608 73
    0x402160303560070003481e102c60990960000170600a01204060307445015440710f8001c0c8804428041203036070002d4000180c0311103042c84a4903030b07100d24000b8a030540004015010000100348904800942c1c04400d01a400140510401e42d8030b908a16480302400c420359804240f03041d98540040c2409008400020700900f4009902e02c0740d00b120181c08010200303010000f81f10892144407030041214420f481e068150000c000c403e0031559011079070b10404001150114000c8001a1049025004034000d00c40c00340c240c50001c02c503480396030007030b011500505042ca05109070f0083e86080000e08584210b8103c0d940c80200e0311030540c0490403112143c82e003501400344003007800600c0388085868404901c25a22000c0411981c2405400c20704081c001c61144042d00f1010080c07806940c0076a03054440c100e07003c1d5600c41d661181502c061090750340f0b03010180d0400100003825840c50700854122114000f14a880c441c507002c0d1071036240d0a134003602e0920210f0010502441388504540e40d407100c0502 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 345464991 1250 345463741 345463753
    0x612020408032a0708100f060506090402071415040c080c13051003020315040302070605030103110105091c0b0103060c210b0f0901090e0709060302010e01080a24030209070207050a0314 81
    0x83d85941040001d0300403111a80c490703e1140c0030050684954500800c12100c100207450920703001481c24071515000c1440350b82c0208500e0240003510301c0308054a030703008044882d01e002c00a140041540e049a003a05d003ca50071000080200c40400c01d0280618001d107a1344d130030141c080100e001042d000e09401c0b90701c0c55125012006071410400d542e8a55251a407070362080c6450310300249000312540000c07081020070b000400004070907544008241c4c10900b040350315800103c001c244403100c201d881043d08010355100c10306000c0c8140a09042e070f4010700301404440b01a403402e41d41c00d6002540c0d000b1002011a46071841056503014070305070300000f401c014400700342c80c000410410303003a0071001c25665039103c4d817810840304201003001010105001d111052940e00040c055a1038071000c0c034140040400020780c60225a0700c002120100350034510208041d0404401980401740012406801580701003140d03c1d00004001c4200c2e0001010310035098116911981034135982800202207103e00f07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 345466241 1250 345464991 345465067
    0x71709060a02011d0a0b0a02210703090311010203190b04091403040e010501141c06090606110c09091c030209040603031e08070909020703020307080d0501061202040803 74
    0xc0006021030006540041859034286081501e02d4043c803d443d481a44044215400180303103280040d0b21003906a13005803500d0300001d544800440b0000f84002640c41c400c00c00c001550903034030080f00c2130301950790400009440f0884c98200d20003565031180344050480382480300c1005401c000345000340074101041800e103a0340d481d08054066000c0f00030f0b68002080a00c40307203400e806c03903030300402c004d2800c0b8900c2c540e0311032500748504c111444200d000780320242115910640750031440c01015015070030010b181c3d9034a0700400181189a200e0014001e054000f091850000300b40b41c024005500900300c03114103502040a10504070b28002d0905030240032080d4a503075584a50001107000e80c071200b07680c26170710680510940c0a68207003004d00c6052424800c2251b441429801981c0c02c41c0c80040c0d844000341026840c4d4041c8200c0144066030004444007201c180341c01160494030350380ca44103840d2034219403480582c0124015074a09500a201c00445104640114000000c0501000c42d0036540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 345467491 1250 345466241 345466249
    0x60a0b030307150b3105180607050d0606030506030d0309022704033c050f0f09030601050109081b04060b1b0c010903020a150519030f0f050705071709 66
    0x302c100c039500f802c3e6507000200b5050030206040788149010515020b6209003068022400c0400f46200c8035500c0e40c0c800c000f9104091000441a0310f104501c200c603c1494081801041a0b20407404c02c0c503c0c5080070780c00910a4000d001d290b000b680000d029100d0b039550310b202100180904842603900a030a5003040030085520650020350f4a81101100031920700f90074043c00c2d080741d8081040d040c010700d14010500320004400b01c1070000721010f20321a9548a007504031004e0041110a5000d00d4001031604030300756001c4010008110180c05941c00350fa03840005440dd115148520304e210380109043c032800341c07400380004240341802030002603800e844000d110030030f0b04400400007185d42488500c400c1c1e0002044814445c80b02464400141c90440c0c2c00304003240100d05c164404130031003031b00c0c4441240c090401e55800c0719903904158080c01c000c150040c05001011200c2c1542480e08030710507240300311800b820703109010700c0c4c1f112032520f02d2075642c00c0140b040054407020b96444c140300048059071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 345468741 1250 345467491 345467513
    0xc060c03060f060e0102211206130c1806050301030f080f0421020109050a0b09040e030702040e16081b0d0f0611130e13170c0607090620060a0b030307 66
    0x240d076942180408206001924000c0b203881f002480a0000703090005070b034518000c60700d442c20031840703203026174541c94003044591482e018403a00c0182041d850082c110362120460000308155400b100c1603540e81c01060f02c55100a01004d40316030400302122001c5940240102407c118540846c1e1401d0b0761040d510711080301c41c0000c2d554074010101d001c010340d0307800b201d1900903080803204003040514140c072441c00c030301c9420701c9079005a40303ea040b03a80c202c905109a4041c1c9030081d005009d41440b9910054030b403200107290a031550401c40e008101d4500c0014550030107880c80d150300080c1d0311070004008443d104001d003140c25280030900c4c1030001e421801081034010002c601075460348400020b044812402c3e400800034249100c080007a044800014901c207950825021801e42403000740c207480b0b030322886420400b42d02c610001d002400391301000c000c0c1250007955400c09040c05038030841c4009049003030a03450a1340310a02082101020b60f000c40502d140040c01c032498000c41d0380c1c03100c910344 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 345469991 1250 345468741 345468749
    0x160303030603030216050609010e030106031b0503071a04050409051009050708010c03150509061302040e0a0b0105090306180a05100c02071d040b150306091f060302010c060c03060f 79
    0x40e440e80010801c240c2c04200c0e0480311900202511145ca0510003c2025030203284d03052410085030807245003840c4c07829405100a10b8204401c000c0c003a0309641c0303a07507d18801c0e1013040e00a200d9460700003000e58002c1b03651640100d020400c039292a10700300400000d4a00b210013540c13103014080c001c2c41c40c03400601c40c1d2014544900080d00c00c60346008215400c43d268880b4030014107080c00d00409102c04840001c40c291361080710151256181ea03004241540c00008442104078070000d40410a034410000540c80b0f204c06034801c3c880025020011a15800b1310196aa0541c0c00240480d049108000c0b10300040103401c0c013200c80915041d141c0602c0d213010041c0c9408282c5c0c0d80c1c1a03a03102e43d42e041c01940050414422450b01c40c0200c4082c600a000303004001810381e507920340c0405c02c240320311807114880020090854480741040065942c841004603101ca0303540c0304102602d83c50310b000d07010342411207030141c43d06213500031a601c51901030000f481d080010503694001c04100014101d0841000d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 345471241 1250 345469991 345469997
    0x1208161415040309050307080604061a100309060f140a050403020c0613140102030301081b0102120408010b0f1504050909030706140a050c04051c0501110406030f0b0a03030c14160303 80
    0x1e420941005040c86100740c000754060b4000040920910800080c442e03005940403400052612882440c0303110b50a07406400e50f03105186071001080c0aa140d080044414051001041310340002d50011048239034584001405040e031600040243d0442d51105070300901a0060300d56400d035800004030143d2151045032490304070f808090113500200308154000c920280003c6145505080300a07556480c13012260304c102c2550300407980164400c0c0003400070480c6104205d038850b81c407051085d010b8900c038440580594403001c0121840d02d4000d4400c401a8940213030f4916141c10103040c0200b5400081a01d12944000c010700d01c001000380c032034294406000a040320144c01e00e018810285c03030001e81584a0120240018048da54030000c0d03046901c40941d2040101407000d240960151481c42000c02c000c003008540003412a425400c88420420403040030003540064504010030b400c014000500003070501c1c0142400514030010611032030b440f00c0101eaa050198410704d051500c0709800803000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 345472491 1250 345471241 345471283
    0x3010f0305062d3c070201090b070c1a0405030910033b011b0e0103150501051b0607020a061d060415020c12090a12081614 54
    0x601006002c6203401c000d5051014420007106040c1c3c039910090210500fa4281c9441e001c00c2c183e041140700940000314420764507003e2002c88a40c034024801d0f14490581601400000404491040c865103d107542d01480060142c0c40d0000110b0300714a080100311626807144c1c45001030315103014141e92045114074020765580c2c0161007404200350140c0344120601d8140482405244240380c0c041d48403000c0442d992036084c070b61928403140761000000d140d0241d40f07011313038038200181140031500d0f8034001034642e16164070420004504442c803002c1a890705c90942c080601c00c0d98400c1000b017903203c4082c01c800f0f0400100c46020f60905806031015000342e8805c21210303080000501030007008581c00407920450440703400e4100d844120052000300ba00f40010342c034524070b800503030642d0100070a0600319240e82d130881005c040d003940035a5400d407040a28050004043e0075800d15880c840f030b4002e07517003410100d01c1590110001c0d000310085842e0600389030180e49410301041050b00341090440817500c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 345473741 1250 345472491 345472493
    0xa0918050702190c05040b0d0807110306100b04140303090307150e06070b04060504020604121103010f0b0618060f0d0207021207050f01180b0406110d030c0c0b0403030605040203010f03 81
    0x11422100e403c0c104411000700801d28003054910120000300d5400f0b460205065804400145140001301c8008104280100c0d108040c48150740b01403159950036800c44403e40c80340314038292030000c1032040b000244000c02041c4181504501c14880c0f00d417014048074244002c1100103414400c1680040c1d80000f400f21070701134003640c400011120390718191051880c04581c0d032205a80e0000041000c1d04160b103900101d81103483d580c003100c00130721900d000c1c2c240000951801907811595140e90381d10035800c0c80e07499503d4000342d201d01d880190f002000b00c0e01d800100d01c145440790310b01c04c1c4070036840502400381c11388080c0200f0040c000e041c0148401079540c84130f44100a03071100b81e900010300562041e5000c0c01071703807108480301810b48000d00b020450f481c400c0d0340f1043da02c101500068600003000c40c0014146400030400710036040f50700103070307400812501d404070126104131302e0300c2c070001e8145400d5001280d00c200403150014064035010070f10a03118004202640d0085e8041c0941102000c0100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 345474991 1250 345473741 345473743
    0x5030708030307080a09080a0c03120501080a060f1401060804170d0b030d020f1f02070f140f06060102030a03051e040323030c0f130911090f190b0a0918050702 70
    0x250b20000d900400c00090f4241c7e101e4905038007440d490a424001d0100c0d00009141c080d40e40040038040c03040c018009980c40b84400c2e0f88566000d50110740e05c0c1d0802c030200d10706800602410181c107403074900d90521341c0c0c60080304503810b201c050420358034646500120103c0410540003424046030100d00800c02d02006020b1500e418010703400901150420751805285580114400078408a040e1440300d03451048840e000003486182001080214815154420408007000c03003140240701000351185c0704030f20b000c0c041c0c4900c41114070324010b800030099440440e0081d4049500b144180c40780002d049891203504040d01c0084e0340503030120342d491a9071800d1015a603402c0c020010001284c0e070550500c1c0d0600c0003540079545002981e4200400c02000b1340c0341c114100c900500410301e0900210031a180d072a080c540c80310420300e0003010510b860100a062480c0070005d05094141d0840d0030500e403403150759058100901e4a401c200c0702080010390003a03010782c0c1c1e0403e00c141040010f0942480700300a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 345476241 1250 345474991 345475007
    0x40b01050901171005150a083007020409030c0f03081b181c050604030513090c080f0a11040b1305090601050d0f1512020a080303190e030405030708030307 68
    0x191490403501c503e81814800200d820a000e616852000c60140c650b4105082441511804a034000c41a40c40c000780c40380c40001e0030740c45101c404400001520208003414403c0300b2002d58988410b008000003030040c1441e500c2207050900901d00300c50038080558454088074440740c020b40c005082e03a0f051140410158054044c00f0401d1201207141094030001c805120300b4003940700b031099400707965807940401304c0300320b00030341d81c3d0321005443c0700e4a02483d0113445a08800c55039401c210b021040801c481202d44039071100383d11541c442d120a6a5500d420200c0c0c2e034801420180c4681e100e4650307118000401d8050310107461158911a181c003200c018211212859600507880f6081074030610040d0798100003140e0740343c00700b114007003094405008200040c0007052001d80d9040800c500002d03ca80c902a04400300c58400c58411004681d00c50a890362030206a40d1540f441b810700f00314402c03419607503014041240b0482d09590a00303a503980024103050042d40008003e400010420208691095503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 345477491 1250 345476241 345476249
    0x30c0b070807021e030d110301090c0807080103020f0f03030a0314101d04031b0f030e0415050f0120010902090702061303030216020406090b01120603050a08030c12040b01050901 78
    0x2040c1c42500d040e4000030b55555a0100d5001c5100d0400b103d120070a606100b00c50114121000500414544080c800c0c9250310900c20740d61964036041c141c0500920a0400c40c4c05801e01e540c0f000c0850342550204080d100301408030301d238401c0582250108544003030010b4140c80c905514001500c152141030031000003001800c0b0129061030304400c0c005c815103c5800e10040c01e83c203c01d1303100b0b0b5585190aa1b565207004205d491510700b6000c541d0100170230b9290340300499120396155620f101d001801c0c0f20640f80000ba40031801c03409000b007401345050070b0800312400a0145031101c079203e108c00f0311701d2103440b40d00340320300c9142d4413440d006e019800e006403a00e801c04114402004146041c64010340d404c0d1000200400305900010380b0303c607085c5610112050582c00410400c0740c02c4c1d42c0c03e001e800a0000c1c440907070225052541d50509040f5510880382100d0f040000f03400403d440da51103056541c00103009520482040c042801c014010100d4184207502c1440209865410071041114564050380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 345478741 1250 345477491 345477497
    0xa0210090c1d01150f12050907150e1f030204050604090911030a031b02180a0914070305100c0201020f0409061a09010519110a0501050115030e07031203090807030c0b07 74
    0x10444074410010340310f940300e140d161501c016041c0d54822a8003044408100d81b000d41490700380507131440040b601c00111000700f81d0b80e11512140381025224030302c1e094001c0380c1c041d02c00d04c1050060081c0e40e140e1040500035103401440c15480f4000a1040c0d0800d800041e960b87d9a554503000b0001d6052403c1610403044005140710015554006c1c030080c0450007152004503651500811500c1d41c544c91005481d180c0024080c904e00028040010240510142c4405081031040d00d52800301299010170f41b80c020f800380401d0454050020080c202e9402da002c1199801c010081c507002012029102608000710301244581c41d006490818044445818201d0343e0f0400001c205a0b8001e42140c0c0d054544601030701003071450355016509401c602058038503038016100710000308541984800d061359030500340c1e0031b41304480c840c0403412180e22182090496102010510104040804061909180340340100d0314850b07030380c3c440c64141c0040c0006c0b00401c4d0802c1e031202c10440c120003101c0e401a4145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 345479991 1250 345478741 345478799
    0x1306030803040311070f06050a080a0507020a060203040503090a17060a0605060403110d0203030315040e03040308030c0309210703020c0d02060315120304080f0d03061401050a0210090c 81
    0x91525030340d074440603100805000801c1d0001011000501450008050360500091007036900e90015105502c001804000901003200141c4520351605c00d09000d80c000340e00400208002d40d45040082d84060302c181c0315440b060080c9482590360004c420040e01e20204403240d000c0b00c07010202e2803c2d01c0601402c154a04001042c4495110401642d080fa50000d490385c0451340108045500030403c03c002a400d40400410001c81c00a65080c05000c14030958003000302c8070804984907104d00603404020003003681040454964100040a50b07080000300d825112441489a115102510800003400c40090003045000c141038040c4500c2d0343c03110003990700002c01041540007c105200c002c2508549039904043c80c44140c44041440c05406000003c60f540c507915035861642e52140e03c2c104540b14843ca850001941d0b1280c05120104d410840e01ca12000c800300006607100c3e0007488440045200c1c01864084c000618090350300c0403805003c0d01044a1304002114a1140280c02c4825660b4420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 345481241 1250 345479991 345479993
    0x120d09050a140f010c15090308091504020d08091f03050709080313061202120c09042a0c02130f060f09090302070302040207020f031e0105151011100f020702130603 72
    0x100800326610f40910701920340001e54030313109907540c0030707500c01e4014075184ca0b010384201608084000d014149450880300f410350700c0c0ea00d03201e8410040310020b412400612100000410300d5018000c1154000d0004040d20180c12141d19056512245440007a8603441404002c0e43c10030300d1100a40002c3d07001e18a0201000b01480c8200861700c610340800003950003183c00c08240d44c0c1559010754600419200900b080e8500e4002a0410040340e0b00ca1450608080001a802c030070210201e50744061000080c084c043c4e00380c95072440350f2000d0349c11804020329003c0c0038005103d0104008508200059030500300804011080c031203800002095282c035040e9804a5000101001120360444026981d449584040f07410314200c80110380e0103116111b12174004100290301a00c80c0300c4401d008001c296105040e110350500c00c240101d03088181c801081400900c109003c007100c0c64284100c442d60390062140b601100c401e22450201c0c1c81d80840c0d46000c40c07030f28100303481d0040f1500c3c109214650031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 345482491 1250 345481241 345481249
    0x9031306110c100212042c01031502030903041d0403030501050105041802130302040e0d2a030807020c1c020316080d0516061806200d0b120d09050a14 66
    0x2660b0a50344100394051100d00000d108001030080c0500045045031910f035555104d00f0107a104500b01001580c0c80c100f034081c41c0f13250149081c102ea411a12107401c800c08848920020350001d81a000c150004020100300c0b0344d01d202884c4040004080400720515150800a0480d58181c200a0404c0800c100400c805541c1d8107e0030600156100010381e6401d205907026400d08040d8002500700d81002c0401101c00c5c5c01050001d00d03070380325880f441594001706c0111482c4900a04602045400306010600800c0c424040c0c02d80c0004240100c40f0b01d080d4000004807010408102da02d10980d69085001c110b060034088440c5d81024020000d0a0a007807a92054176070b0164412841046000705064a03d403817490401011a03800940400601e650881190064200c3ca402a9001410110940034a80143c0c0c1c10031403014040d101d1a00708019101081c001e008950131641e400310303082e0051803020394103020307200210a0580b9028009031520701030107010815584448018013540c0b0100a1a0303d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 345483741 1250 345482491 345482503
    0x70e09100902150918010312020d03110712050d050c18150d2d060905070e030606011206080601080102030105041b0f0e0112140405100207030509060d060308030903130611 75
    0x3d0b443c01c2c3c4860b500780106801c1c541c10b46051199858031000082402042888000d03100c0341c95086e10300d040a8590150180d4114844401005a04102500100d980300d0584d040003289031604034a42241d00c10410b0a540c1c2c26540c1100e00c80002a80c104402c0415001d1083c0200c140d403c11088000011984143d006001941000c41e8031110440b001101441c0380c0e0081020268103d1040424030009200506207401844100c2d03240201044e0f01c1e40c0500012400d0340c4006000740355a0f55a1001151184280d40300c25044545074040455000001e0104502910420000680383d602d4201084281d44403000807145010350030034091403559000b15030340d030301c012a410043c0c10340d9150390040b41d01d060f42845c0c000c156880c050700c610710031200540b03486c0150f00800407103205208002214007244140f44004000c0392041100500c40c2c1042e0010388042484e00500103146130b9244c40700c2c94942d00031a80c85000b03400000d00003025803078000c0c00c04007400712440d14040381c0e1110035015640390 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 345484991 1250 345483741 345483769
    0x6030c0801150207050d0507090b0d080d0e010b04060608041211101a0607030215010e1014030f0a080d150308030604390206160c03050c0c03070e09100902 68
    0x1500203500341c85214001c0004c90003e00e0090508100d10249007881515200c950041307603001d50400419142c203113000f01000340300941040c040c9143c66000380c1c0c401f0041c140c441e2520030b25501e98400f00d0040d650b07441084001c01c81915030f0700ea149818500340704034511405824003408800d0081d6011036800149401d46136235200400941c0001749682c02d2284510f01688552005000900d13074105a80420317007103c0980b4910310b160050342c891403030750000c1c00210740c080c0120a00d42c03030400100e160740c0d406444060020301554021031381c41c034206043c0105c0d402c06440c2500005010346102900d84070744002500760b11003c42415081d6a21009648009400c00b4461501d400d0407902c60895a002480d207042007003a85080d4400500286203100c1e41010301c10058092080011008489503070110050041c035501c4081b00c00c85954240c40d82e0304100c6070103000344607240000159860400290014200c59050082c00c2d280c04003189250050ba18150301070203003000044030050312034880c4071100d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 345486241 1250 345484991 345485009
    0xc10020c0d0807210f1403070c0f2111010e0604111c050d3915110d0c03020c0a111c060f0c1d061b010207030905040606030c0801 57
    0x300c21400d240b0264061410064039400c8002e0002640d2030f4042c40b50001c0d800161110011560020b1003503da0641000b0400b550440810014034828400c00200c0740f254840c00d0807180702c0c2c0c450386401312018808109518618100300d01c112025810480354100c0c14001e400a02c2015032700d43c400c507102d1801904c002c114000c8090f0709441640c540d01205e00b0344581085083c480380c61410184c0c1d960130b014003550003040c0840110044002d6030100f14440c0d481920410203c03144010a03003040c0d500100080c1e4044001c1120491a070a084c00f640702d8525481d00300d00d40300d41ca114283e0b411661126441030038144100441802c01d88049050512540c00881d0004004284400720b80700c002417410b48001400c3c1590380c0c004008040e4006640c22005002c20002010152000e58442e000e03103401d01b000d008000700440c07492500310000c203001e0300c05d4041a414105007945503401c0e6002a02c0480c04503041a00030302131420144a001c0080681d441d040c06106ca0807400a050307400180209551 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 345487491 1250 345486241 345486259
    0x60512100b06280e060c060c030c1c060e01050d05060601121b0203120109050106081906030c1d0a1a01050c120304080d0c0302031b031806090f0c10020c 67
    0x4560303030b200c042e50481c240a074600641e28080552580003030b8518400c0318045a19250040d5107804c020b0b065071941004240100001e86424103925203a810080c00e40a0145041000b800b55100221a00c020303110640000f04500d800e04401c2c4400d142c058001501070489841041d010440000e040c5410120a090002c0c10000390001040500008180661300700000391115599940c000000d207002c1d201040c401140c0d90303c0d0036006007902c1c0c00b03100302030000b4090fa0100c2c400000f5080c0f22100c42100c0c1d040050502e40e00d690394008140c02e039002c000164098a0306000104408445a9000060880811403420f204400000131021b81c41c8540c1045400b01d443c00755034508100f800d03440700d00c440015480385803c0c03415038055403291070301440b03890402445107441e90081c02a00c1c0248181c1485050343c0c0d92020381c140480e000100103400000e03220001101d98901072101500900030f0030b002d0306d4598805140545030010503c40c8600400c441308540201d40c1e404502210581401c44907512 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 345488741 1250 345487491 345487511
    0x1030b010506070803070e0a1e0503010e010b090c36010f0c020a060e040603050304090207020a06110d03020306040b0a0303020115061e03050c130603020912012c0304091e06051210 79
    0x15242c1558001004410211610000c0d0304004108101160002c4009100c0c580a45402cdc1c0c0c240c032860800300303800c0307000c010101d11840d040b08040e10388c05905d840041030b220000c0d280c1d00c13080d044040544030011032a201c40710003560b0046102031040c8060030402d8200b04035a0120f07400318990b211f690304100041004a020b95100d801040042d5040390460b512603480704030000095111183c124416945000f00040304c5005000d201c1e6200542ca010300f0640d015600b054000e0b50008082507881541c03403100764031a90701c0740c2c80c007406103000b0307400001c2c01c20b0b0110501c3c04800302d41d0170010500101d0707082410003c481840c402080440c505d80803d032502d60b10f0510390075000b8031441110864050a000c100c03c0d0381035000d062000000c41d02c00c1d44a000203110f031800c0707442100d440b114070003c41e01c060f0810402100f800e0030500c1a2811a4506552a04500c2c11070700d00000c0780e54a1040040c01d07130080da00c17034054407000c0c0c0802c54000100c0b003601c0c541250b40300d500c106040348281c0c50740c503405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 345489991 1250 345488741 345488749
    0xf0103080a110304080606010f0809060c031302120c0a0506040f090908040807030f0b070e1e0121050f0105010807021e0a08040b12010b0f070605220b01030b010506070803070e 77
    0x9a0704040b6011070f516a40c42d0b0b05d0b1580c94580842c0c090703000a1100350302c0340c060703449024954012009200030f4011500c8031900480640c0c402003511802000b14030010340180c0780d21030940e5807103d9040c0501079808299040001c0900d003a40058401d41040c0401e004101078803140200b2640f0800000900c070201c1e1402c0885806207600c6000c1074007a1349400420700042e400400012031080400d620320b9542c0b6102646c50741d800c2160242c000c98495095580800310102030290038205040c903844101c00d000114042c8405010400559512a828805280e1020050300e000d800c0900f8100054900100c0c02543c034540300300400100b603200320101440345c0741402845030f11038210054030b070b07500d4503000102c025030f000c01100a8503e001e03100002e424075603c0f0540d40500303045c980c01c52603d48a03403500405003101800c0c88203044005a2000b01100b2030f15035401d4940c0c40b0303500341010b41d8514204960701c00016440342c1e026505c10048640000d40301320440c0e500c139800d400c0c40d25450b5a81c001007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 345491241 1250 345489991 345490007
    0x40b070c020a150e15040902030417071a0c03100b0a0909110406110a030e13020d020d021c060b19050408030313020a1211130207050f0f0c0105120a02090607050109060f050c030f0103080a 82
    0x32034201c80c40010030038180141000d901c0400c0043745580c1801da01c440d50400303290311080394800182400c0380e00922690701c2213030081c22a4103003440d0003000346884907002e0044401c0900c2e19000010005410441d55401411603403030458070754050000c2022545020f0300b2124a6800103104d45134003800817a00070120f40c10b503001c1441d00c280031516844880c020354002e40c81583c0b00c0d40503130607d0b03845115001060040c641510a1840700c203041207404141c80a1160b000c88001c0b0601c1020b000204210501b000918441d141003103404541210314014021410b80b6904816013201803214050041004580d07540e0840806071602100d00107100300c0e5500901840400a1181c01601c8070700011940c0094014807680303114084d284807695400042d10607206003524078460026110004180f41c00d81e5016004511004d041c051402e680c1b651142d00f11070702c0f078408841e1265140d114114103d402d200e000d40c49490541a54950700f80b040c249403d03c94140b000414543c1c0000d60690107a100d0304a0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 345492491 1250 345491241 345491273
    0x10e0114120d0f14030903090d0c031202070303030612050a080f12040c09110c070b070f0f03030506040c17060402030a06030c03060524011b150204030f140c0108040b070c020a150e150409020304 85
    0x40d000c94100033200130b46402d800d110560010381003c00c00b00764107540c40d034100b1302c00e940200101414500b5a84118954220707200000c00c49030280a00c0d4041610041d601d88210300c43c113448907000d41889008402c0380c0c048006070075141d00c144110010b041e40001c514040d198862411512444c541c5008004011042402070140040700c1c0010205600342c1c01250150004882c1405240808201226603210300746581c41d50f5200c40000c00e1031820302d6030040d80c2000c076109002c10065200d407207100c595036055104941d15540c5030104004100b09160483c002c00c0c640141107843d5a006000900c500d80840c2140701e105540014407041003803110b568031441c088813000b503450325580d0510340301e240c10b80981514001d42e80d02d03203001d03010000300710b03071480003016140c1130110b490b540c54520106c90000d20080034002c2e841580c80240c0c0d2504401002080e031303120075541c01c02800d20700030241540301da6070b00e01841c0c1080704074401145040540d03003555904440103032030740e0b9941400807a00c1030b0000e03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 345493741 1250 345492491 345492503
    0x1706030a170306130e07030f0f060c050a0e031906020a121104050a050612010b070303060308031005121c030b01090506070c050108010e010e0114120d0f14030903090d0c03 75
    0x4a031407507150800c070280d40700d020304a98031070040b08803070542c0055030112150b00d40c4d5a001390034180300040c030040108003e03034090080b64920f11010750700c0c042111a12084500880c00101300c403000103504c08010218a4016009400601045031155106200501005252540215000303034114850b140c00c2c241c40c1c652042c10f2100c0b030010030104415503c140605401070618103c0400c2a04000040b070b04103010021000d41941e00e8411a0b849035000040300300d04164685e580000440d08090146000d0f000c03541c2d014101c02d140008106250030f44900c040a01e42142907c1108800280c2c03402c2c0c0700541c98200811a90481c20048840c0c0f061070300566440003001c41e0075410f0240307191500d02550000c2c1c0f19004c1d1642c86903881c00c4103490034071914501e401840010702c00305d0049051802026005032401c514424030000701400c0c200e00d00c01d0800048c0160761400c1000b540204046e0340501c814000301e1031410000440c503120b105804440703000b060201c1500003000309071031141c4000c42e0030031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 345494991 1250 345493741 345493763
    0x5040f0b09010e0603070807050d0f03021f1e0921021608010603121803322802090411030703150203070905151206060903030a031b050a1706030a 64
    0x60f092402080341a140709000344120100452218070000e140d0341554401023612042c800a640c50300c0426040b82e40443c110700402802c0d0480c0b44290114240c0042110000b2550143c0d04007500c0c1400c031603070f0018000600300b1911002103550514680d07007406501c0942e03001c50b16240b0b016843c3c1030307002440d03e00c1c0e9200340308000350b40f4030107520003400d0724402c02005001040c0c0100c1141c508030640318209030400b8400c81040000c215401c001b80740d401401c821000545091034004051005060307034031540d000240c80341210807106000c42e080301518040006500c840741c011071621480140010b1601c0e504001507140c41c0d030204140d100565000d19030a00b51601c1e019020080c2d0010398845002c074001c25008913091501507480700c01c020b0002c0c0343d581031003a0590394500d690070190415810a80421581c545900c0030700c001e007090300b1980c42c08075211944015007901f00c034012000c90104102400003900c1c00e0b6100c00000c0e90124400007001042d05d0b480c00081c01d0a5038100e00402080c4a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 345496241 1250 345494991 345494999
    0x60415080f0f0705030a0b01270e100c05040f090504060b030d02150601050406080c09040915060e010b0c03032d0f180604150e0312100f080a0c05040f0b0901 69
    0x5005440c1080708410b50f11060ba0300c1040c10b5485c000c00e0001401100f480d001131000a00180b00c41c011031000e0040c03120b13560204040b1404954403800e2000054115003400301c0c1d080c41c940108090340c01a40f600c40d2400f03181c145007070003001c514010720201c1901c0c2c40120b01440401e07000241d40c04001004c4c0c4030032800d0000065510403410168040414801c4001219580228299400c40742e4a4507000103d40c0d904040000036800300d01000d46c0140e81c0c03105c99011540c40b0443e030522000d05007000900b1070400c90418400304050b40051710612040100a50020703000c0241d9401c4540754140d4164081040d803050451210803045801000c00b000c2007054100740501910f01480c444500580d00510784032900d40c03030300b2007210040c0c818440740d0301c5030300100c8032a40881c803030318043d40990f824150042d800c0f210350350003660410002c10001e0014080c114a003100c8500400b14039000380401e204a85e2a001c444400c0d111b030340e104076614440b40c4281c400c40c0d0050381d000c100041002201e5070311 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 345497491 1250 345496241 345496243
    0x30c06070804021323040318060302040603110915070c090912081302031c0c05032a1b010c08121905180a0219030b01140126060415080f 60
    0x884083e0310541c48040c442c083d82205124200e0000314840b1a410706041c40f00120300301c610301500840400c50326003511851555400141d6024201c6c56030056950307442e100c001001d480100b48081072085040008031625590380341c80c01c0610085c20711654035442e4904080403c0e06c2290f02c1001040d0a04c03501c401081001950524940741d544c03500d04154842942c008441c184c01c0c0c100035015403084648079051a80788810798020b0384140b0b00040284ca09d647c2d52070030f54101040383c270300349504000340e1050000784206403506440d01c040245040d4000600c0301c50300c0c0d0720320b0040d0317414007412035100301c00e000d0398808039150301294080302145810080c419141d4480c004264014640c5401d01094036495200c2c0003c81000c4234038000c3c080c03110f240d000c10016501581c90310203541e01d1650700100189254200c0c3e4001d043d4070907000d018201100025041076445001c20045100702803800141080c0750032040d811a9041d14001981000c00d415011001d0b1690400a610310440301c1c00c1c0f00c0030fa0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 345498741 1250 345497491 345497507
    0x1b0705060c010c02070b16020f040b120606030f03031311011e120c140a05180d0506040b1308180d1502070c090612080a033207080108030417030c0607 66
    0x1542103a082e15501d50101105024a2500ca500f90045a03ca031002d0702e070403910030300c49c20b4000f480061003621000000741c1b1904000400c90a45d00310a080004a103000c0c0080c004650599020b03500d5407030012158ac0042d41d90000c024400c03900792030305030307000d9100b0708030341826107910416203200510f00d22001d00071461007901000ca6a042904c502400b03031103039403903440140d5041019810803561540648907600b1001d58001d0500a03810084c58550f107907805201081d020300c01520050034141800e024400d002414010208558050840000e554504450388004528010803160300b010b030000c0c09812a1003000b80ca0441c0315014980880c50700d900918401d403141c4002e15580b5070390b58042060f20842e03c65005040b503180a58000304580b00014810141c0728600001c5c0c90b44000c40c9044800d070044414030304c0030034609851106004150005800540c3e50814281c1d9626107140c07960703030340701e6801002c4400f0703041031020803484000c0040c1d801c3c01420805440051400ea84014000c003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 345499991 1250 345498741 345498761
    0xe1306030b0c030f16050d0c030b04020310080f010c0509011407060905010e0f0c0603040b04140a0503041503153b0a0605090915060a03020301051806010609050102031b0705060c01 79
    0x1a1090001c100d413481543d11407015100e40e41c84041c07c3c00740e4545894000c00c84180030300103068680c0d140c021070340d0f40c40c8015403107190709045600c1e6030b81c00c00421030b1911710b000750f5115940e854043c62001042c0c0100c240e9150040921f00303c90f0f00035140c1800301150007902401000d00f07050080312010040190000c160700c406260858502a50f50f0103032541c0d0b6000798100d190451420004500803e425810041d8024001d8402c06020b102e0404241c1c41c01e0b004410903565900003040070300c601070b8203201a00754440545030a000503103404032900c00300071103482202d11420325a0100791242c1682d1000d41042a009800e46003403c46a40300f649c0b000310110341c45620b151518030003003a00c1c581240c02c3c2340601c0e000f40041011000b0b11640b001c060401600b05c1c0d03401801c801300040141c0d8240221407082d4400703a41450b9008001048500c0e01d20181c20070300602190303250034440381e40d0000030f03649500c0c005051004044017a0320b0789400c010343d923008541c000500084c5c3c146003030815040240c0c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 345501241 1250 345499991 345500011
    0x30507140316050712020105071b2004020f0706020301030b0601050403120c02150d050f0f1b07021504080a0311010c050f03060a05040c020a150b1309050111130519060e1306030b0c03 80
    0x202c482b910004100d40c2102001003d00f500f1000f1700c1d400d25901c034200d01000901030700051030054002c1e104502900104d000315080c1d50000014010040780a0a040e0450400e0070903e08040c00c5a460b158020301c0d001c0c1d8641007001e0440104190350703407a103c8210140c012a0907035034481410445401800c000c407a10404802030102050000b84458001486580003070074540b180309605003e01e109610141082e82c0c0728110320b58810b250000780b00100001c04209004125040c568a40608001c04c0c80074000f20a03450061409041c0740c124044400c0808401c2429640356184400140e52208a40000790000d00d0400f04040302c170b40000f10848c04a002c6c107030346811210051441d4055031100f044070f80d00001c0d81d50090041d569031386c0081966501c1040003260208001d40250310300d030008450303c3c010071411102000b2900b0b0000d145005140d01321b00c0c2c100160709110300a81150040000769000e0780c411044804001440ea00690203541d0050300103000d41021820484c00b134205403204a04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 345502491 1250 345501241 345501257
    0x9240909061504061d0a0e07020d0f0918090b0115020f0610030308040201030f0c080106030c1b0320010504033504020603100e01120303050714031605071202010507 72
    0x14900d0b04038019948040c030320704401d24250404608480d114940903280890210103916080565a10f90500020340307500381c8940201c0c504400000c3c580781001345d54100b804012206c42299940c015880015200b032549049100200c0144550052003402030191103a01c4410010607041c0548204004000d000c0e800c98030349100840d1300c83d45510081e80c1100d0500f800703030701c01c10009006042d031a91050050500040c04c44010f4104000e03100c0744030381300000581c54001844620b0309441001c032820500d00c1e04052454030b80f107108541541c00300d80075041c0201042c0307032101c10b0000d00718071043d181c07000001c0c44142440d14019108405000a2200300020184800070002c040368944802661044502100342ca4580034043e4a60028046841020b0720388e0002c41c0341441c09850134000c081003a001c175102082e9080003400c0340d902500d1081000040c1d031040c681c44074101d0699070009800701140441507072910050380e662240810041c88032075408100080190113501c000d12030030f0942c8454031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 345503597 1106 345502491 345502501
    0x7030311160c05090a0e060a180503040602030a1e02060718050d0b24030d03020f090411090f011103161a01030b0115020604110609240909 61
    0x194003500110811180c10500b40c0240d02021480d800c2140500030b9a4458884501600052808e9200d12099030208a244d240100c02a440000c480d0fa941e5562006034983d000204140302051402c41c40a100c901401c554070541c405c164050724041d0f590f40740958505185c0c0d010b41c80d10304012600443c0940710780800000141c05100011030030302d4080350300783c18040305015280c03010076001b0307200b43d07103880c001102e0341440350600300543c4903401c1c030b488880c2602a5801a6500905203409a5040300da400002c0c145942c0c1941c1c58240900381c4801914901e01b50741c829003843c0d104000c0d081720701290300350040443c0c1c403451004541046110000fa0450720a82094a1010030200104407801191f03020b08882d110703d0000d040c0c0741c90030b85c0342c0054803100300004501511000400041554031654600f480302c0b03044460f0400c1c900300f906510030a4014108023402b0b1b801c000c0c0800c1d = true := by decide +kernel

theorem cover : BRFrame.Cov 345323741 345503597 := by
  have h0 := BRFrame.cov_init 345323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 345323741 ≤ n) (h2 : n < 345503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
