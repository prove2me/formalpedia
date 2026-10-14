-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2497
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:53:04.845326+00:00
-- url     : https://prove2.me/submissions/2f666eb6-865a-40d2-aa0f-c9f81d8c6300

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 448920863 ≤ n < 449100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 448922113 1250 448920863 448920869
    0x1528020c0f07081b2e020f01020f040e090c011710090e010203070e0a080a02011211031f052b0201030e01180213090c0605070302070f0b0901110c0604060c0c 69
    0x60042d48404900300d00f0106000c03400c0420382551000c3c0090481c00c0020203c1c0c3e00c05d0000a6401d0b90303114200452001498090816941c0140c4a4140745151624203a9001c4440300c000d00e0f00004040c0174900d4021021500601c5480003881070b408608006010010750403600064070000030300058040c1c08154100340a00340100040c400b000d0a1002a0301039042540d040c030100310400f0000d407036428500340800886800b40c006019200e040c0e001540d0b14651030044000304c0c0d0b1150b004081c149071034001103008044114001228034100984200c410005030031080c880e80303081040c0c186412101c0e0070000750260082c0410215842840140c00401038200c3c807c00550a0410003141005200743d51b0204a0007a181c00d85101c4100c605641120380c8158010000340c110304080c080144610050004203100b4011144d110b52a10b03034210081c0740651004044c3d00002420a0155902c84400700c480c52014000340403030030b00280002c24901441c015041000b541c0c00044061100d070314126401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 448923363 1250 448922113 448922143
    0x90a0807210306080d0309051e01021b0703140c01020a020405150a0306061a070206030109090206040801020d1b030506011d13021204050c0105031303030f110c1528020c 74
    0x10500007150060040d10581c8541e91060144168540c1014000e008944003160b2140c081c08100480a6181c04c1ca08503004607949150350038008540c90b601400581c900d4440300100030103480c0e00e186000314031140003003800880c580003074a0759240350360005a41c042c95681200e002c45d0640d620b00641812200801940780e01400c040310000c240300466000c1c10650301d60403400c525480d0708803107088180c070416000235000b69041004019000d040c1d484062142d10003003040b0300d1300d035881030a24266040071000403445643c569801d86003001105104c9050900e500301071280b03241030340018080c440d400542160781610b11a05141e99a10001010054072040030115102c9a000085126815040300c045889100340d200380300707a0b0342c02113095a105010b0002d03d0103c2d240795a4048001c0c3c02d01c2c040c410704503521042003000b10b04012010741044600040104400070382c5a21000c01068094111710585402401a000f2030315080510404400c1c540c4000d80d5030b030407000314281f500c41004101c1107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 448924613 1250 448923363 448923413
    0x1150c0609030c020f03030412260a0201140112150506041e0603020a0801060e01090e070324110f0702040b0303040e0106020303070224041e080f0c0114090a0807 71
    0x8250f003203000800800d000381ca8500c509020003052654070700c207a00a5600c0f8248001d40000090200d0740c402e001c00001410803005410841c0007160700e5048404c030231025035191102d450b84100a090f000b401408444a21444600e26444682e1110001014004100d88500014074941ca072500301c0300d031010101115840541851141ca40100140e00007244500c028200003d001501400f40b5000c0e28102400b815040e4070f4030000e00d008000c900c8a6841c5401140e0000ac00b1824140b10380c0514504004603900302c03010540c1e400201d5524008207a80d440060059040c0703003100205039408241c0c1038074005041000100003905c1c5014540c0040f09503210b0340d00100b0216400b1010314000c00c5a03400303d41080b614003c1807040444219005043e03500e031070000074007044604c0340460741600d8015149400200c10748a05500d42d1101c0e9030740c3c2d01c04030001084c185629091040c5200011501e1124901d41402d242e400c0d116100200040c2419034046152001c2c000311240440000f034640c09105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 448925863 1250 448924613 448924631
    0x14070515070c08061006080414060f010501080603010e030d0b06040801020403080918040f0326090102030105010906020c03060f0603100e06071b030806010f02100915060f0b0301150c06 81
    0x40100d90001ca07080311000c920500014140d500020340c0c9004101d43c000304014076043c030404552140b4001c1c8165a0100f216500880080c02440342d11b0164541d03061078001c40d0304000c000b519202001d443e8a0180c0c1c0b40100c1c1e40403141d8007000f03442c03140d00d0001001c240b249002000400343e024941103042d455100180c000308004401c4010040468141d5070311400f100540109030000c1000c0b20040e11001c11032401100091061021a090b50329255a83c085246600c80a000d40e0408986d4a000d903980040184069a00500d01c4401440c1c144000d155205500000c6511441d01400c2c401d6418030480105e0626a4240f00011100d03c2d410001c001d04204407041659412003918201d010607401c0940307094110600441c052403d4140d100d40b0308079141d403001192803852060301c81c0c0c218011080b01180d094603d009210320b0364002c241c00c1841806000a400845032194084d4000d40481c82c0b013003100003d28010369045034856540440e040308a0700b4242d8614001001c000c001c149050390f40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 448927113 1250 448925863 448925899
    0x1e06030c06160201030c0513120314191b1a1021020f090f0f0a0b04090c090606110a0f170f070501060e2403010b0d05030c010506010516140705 63
    0x1080c07154000d1740e080c0081c580030003040d44d0501c0b40400c484801486c41205016811040c50a10704c0c0c5882440c21070420403c40c503030516142c10a0075000807007402d4104280d911ba6100707600d0311990500c4804202410100d42d1140044210400005500b00080300094035400d0342d214202e005200d140300d400714400c280980007011f542841d208038403400c0100389100140c18100c0030b240c454a03244a42000d15107481c45906200e140c0100304d0240d0640350024104151603901842401500c100c3d1040c0d4002d00304110704065039a550401c070200580540384450001c030000d84070380703e20742003e2403860b01c00541c20290400400702c0f949008070000003c1c80301c4600d26080c003c01c4440d00407402088255140c002407464050291200b030301c0611040300103642c0d1141c0c07942c030454112008000040036030b04440450404002204d041d111034001084209003001c1c28080c06030301107403d280042c940a414a51049080054103000c0c0c000b00b1320351a803a007840c0d030400c0080d000c1c0100401c1b01544517000c0302c80e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 448928363 1250 448927113 448927147
    0x91504110d060b0f070222111e0901090302150f1204030e03071518090c050304050f070501080a0c0e21070b03010b1209030706020c0c04060602061e06030c06 69
    0x141001a0385803480003c0c6289410b41600c20b050744005040749082c010b03400300942c85052080c072074240b6070b41004001d0110007070b00c00d00682d00d0102c040d41e44c865040d02d040e113506003014a0403001116082090824603a441101c6c0d0040e00d138111100746414801584591150151040705118038400059071a0425020a0305a20451082d40c505641c0106501030580740c2103e80301e025941440e0450000e40311b80501a4955180b021309403054000707a50318945015281c00b03081d900040b9030000244000d01c0300c180078035110901050000c08070741e403501e00028078240740100401d980c96585e80714507110500c1008a440030200080c40102440b03000c40c81018031464459441009204000c00090400103020545e4129660720310058180513894105c40d82c15080106030b4041400f00704250340009025201400701d04900070010115090901d0038002200c44035007281c000d540c0034070100044424044200c078200020126440055210240464075041204944c00e07409840450883c050320741d07c0070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 448929613 1250 448928363 448928377
    0x21050a061802071110030b151201170304030b070306030b0906010e010602010b0108011806120f0b010506040302130902010912260322050307150c020606030105130209150411 76
    0x401111007105080c048400ca12591200904005942214036481e143c4810007030b0f855400c074200460301008140014a80c0b1012403c030f04404040814010310592071100c0d402c0c0982020b0000749001c42080f41350680e00e000328070005200043c0f40001807581803084d04514010340e03001c07880b0030301410320144c0e15480d42001d000d0203116000708400014803038414000d0448000c01030f103030040d140e42018255501055965007500e640e40d150b031400128461200003508480d406800e083c1280301591605840c400410303031000f4031412090000b80b01581c0d81b0030b580e12003039181d030000003200c620740c0c8016502c03e1115480800c45650a44c2c01905000d0450001c00007040c041001410100103100801c0c10390000359468065159075445c4542018038410007064424054402c0b64100340c2155034502da2082079903444030a0725218500600355a0301081513580002046009002c0380c40e04642d00e080201c1c0004010f481000c0c014041230030496003840c00340da01c9501030010303c40b02940c86440d1210342c0c4401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 448930863 1250 448929613 448929629
    0x612010b0c1203150613150507110312040b07021f030207060605040c020d050c010f05040f02040f200f04032108100540060603060617040321050a06 65
    0x41d003501c100c480b01e9011644a2070310743c0715071114000c1d014240500e0350800303803001e8030b0302c204d6203008200000d240c954106608440c0d134456541d2041031400310900201016414001c1d4826080707100300c80424425542540d841c1d40c42c5c6600c40800d8000070b4200b054000101885480066821413001d84c5a0024004603005032000e0015544c0c50051008a60804808800603004000e055401500c510010104803190b03d0000c01c184d982c9052080c1141e0069800f1101000e800c1d1300c207021810701c0c3c0078045900d1600e00302041001d07410040c01142e1550380c1c00400504900281d940c45054000c030aa41c00f460f00031404109240c00380032085012044a42c05502007030800c40010325002405118806686018041c45900790110080c51004240c80c400c2083e40020003402001c0f00040d9815034021245a0801084261500b0b00140440300030350041d9040100070028080340b4001010f00540043d8145003032418202203001c5965186240c0e52045142400c19080c41a09400340d000340094581c4c00e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 448932113 1250 448930863 448930873
    0x41e02090a1d0703090804170618031201031106040e010905011409240a03020907090609060207030503180d08070b090d03180201030510050d05010f050c12150612010b0c 74
    0x55039010b200801c0c58040c01c808504028002400c01d032094110000852285040750b0600e91200307030001000c07401c0c452400e241e9024100f000700300d0320454220903103590024065441c040f03407020360b6801c1d031105010142040e0b141040c1d001c2d03107450710400c803001481c488809203070a50712a58030401505080c41840e20350300c81d12030b112210749403040f01d10780151190308414000450003e4000e41d40450459040e0f4005945c03100040941c40c1d08221b00d2085807036680b03070365495041c0103000d80544030030b4202904560204006200144c40001100c007040d04444030304161190610000e5210125190f00400240c070100f251000c002581c43d0b0a4018546a820b6a28500059500b10304455540082550607000d03243c101d40554069442160405600d1001500c40c0e6111004504900c0005c00120f0301c50303540b804580d1102c0414414180c003c419420003520344980505550348102015222242d02510066480010341d03417032003250405c1480c4485c041e81981c2d200388100007900700c0c8100034aa8098 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 448933363 1250 448932113 448932119
    0x80304080d05090105040608060f0d03260907090203040602090d0521090a090509070e070e0a0e100e0711190b0f0c04060309020f120f160305060106080402041e02090a 73
    0x40b0140d0319803960682d01c10382454501a03084910003409030005401030711191850603603890b00124000098001d86400d013006076005083c00030716000401404e06410340381e0910194510100b403601c221707600078002680301d403100d0500c48024816201103550203a941580401044000706071100c45404282e0a49001030b441c21880442d4404d41c11515405040800103000c400c2d00c130741c052034001c2403c00c1180c052a480324428480f0341015a20000803900c00c000000162915202d0080949a0b00582501a051a501000e800880350041890070480d220014011520410307100003000c8005044440d522000303100710040d400400d1046e1400c1d403041000a00c1e0203494429580110340b0221050710389481e000c021001001d00c100126070020b00c402c50180c075075869180d081201e41441c0083c142088506422600d060400c00441071052917820f400c0000ca0700114001d8112556070510286550341c0e031000400078080d6100b99000b09001011080b0400500d034060004000c09035140110035407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 448934613 1250 448933363 448933367
    0x20606180f0403030e19031806030e0309060c0a050330060d02040c0507020406030809041404051c05220504060b0403020303070f021203070809010e040504021f1404080304080d 77
    0xc040394101c500107511404100028800c0e0b0080b65075021001c01e80380d1440c603642e5100075904c2641425000191205141c3c1c0c0b250150000202c000c02007400d0420410740303d1000c01b0746038010700112900c0380b88082104100090240b100007807007a80f02064a40c1c600c00d0480d031108141d2940e0f4245016042040c06259050b100d507250b23805148010f10008400885d0390030003003d00940f100910400200303124100041e00da502841c170140d4883c0040304d480340e02d00d60a000c1204e10300c800c140402c0c40884184008a4070101b5141203100e04e2034001007455400c01015900f62060b009016040503803400c6005040700c0000003002990750131a0b040c003500e9551402c00e40c05001703900000e5416007040109100190202c5020251184046d15005001c041c007d0850b04542282009482040d40050004019a8010008010240102c80c10002418640c02191901000c0544a04003440c0b90068105150166147c8507903001091200395440751100b24103912600316208800d601e104404007410558 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 448935863 1250 448934613 448934659
    0xb04060804200d0f031e09080c0f010c060b0a1a0304020f091017070f0608040b06010305040c0603020d110406110606060415050f0c07090606080f09120a05040e0403020606 75
    0x103440109281030f103002c50b440c0c000600c1d44028045040c45940010200c0f403032420428400350350601d80340d80e00040d00c0c211600d81404102d01607180b1078178034181080030680c2c200300186c49070350308a8000956508503001149a0300015000100300c500140b060ba8100c050304401984a00d10070b80d406a0042521814001030f043c080d654031a10b8507040900f40500f210540001456201700c000b118501c40d83d03680b2107a8100415000740001440c803108000034000140c12f010742150083c1383c100030301d1815071100745041c0c6440c0204410190001159008882643c1100e052903c40340401030b640c1da038908019250240300c100b00c060034003594000030748920301041501c0884072801000f8000c0014a1000c0307550ba40980f11006043e402409414581c4000b006104040c02c061500051382a050070000380585000926a18411503100100206640701080d51b0084000211509842d400c081c081900d1b2401146c020680d41c40d200010441895400100b9034000c0c0070035141490428002c0180150034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 448937113 1250 448935863 448935923
    0x1002010b0102192301050708010609150c08120c0c01111305011803050102030108010b010815220209060c0109060c020a0f120c080a1d01020307051005100b04060804 72
    0x1d0781200e60040341c43d01d002c40d00b00a00c035200d20a91081102440c081c12036100d40407143c04041c2e95103c040001c003d0700444128050903181c00e250100d02d20b808002258050180c00c00f02c00c22100c2c4070808100100301007030b01c0c886025440c8600c0385d8542441d514081e90002080c2c92115800e210f004944131302d074a01243d001001c143e501c511981c0c1400c0040d91482d005a2a20010694081000002c14420b1000c0c50182042800100e007003c400d0b0300061030324034040c1414019484a08e0340340c0440cad403003418900749050000c100034001d1403540d403050001d00616049a802840c00642e002c201403041d80030010303440c842c000070011040d9101c0c00301d0351a180d004006014821b080c171300340042048150050004403ea24140c1070036039241c1c3e0341c58400d400129102022035400c2c0c2c07100b01d01c40d8000784180c5500500307200035810504162142507a4405103100e25681950b5680410000000d100d00003015140f50486907940700c0e9074480090000c88202c40990b00c5000e0804200744080d5030300c801b180b107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 448938363 1250 448937113 448937117
    0x3403080a09080f030c07050a0c090506090702151906030309081209101b0204064e08130e180a242009011101020c0604030f0e0402070f021002010b01 65
    0x1c01c10304900c0f603219640098146001c1c4c41d0b050082d00000b400810144544600c5141586c03419840c01501c1400d56202400b032030300c2038a15500704500d8650010748000000040642000a45c46e070011040b000103d060751030b214541418004002d00d9006803e0500303d80c000001c41e5012000c48203c400240600d4801541c0500c4c0d00580c1c080c0da0744158071074585800320141a8201d20700c06e500180c00c0f03480780e521092000c148080194011400407000001d0360f03c11315103244144c0034544803002d040a601c00300800c442d800c40c01101c24032807040d040d2401c060000c124080d00e1130303c2e0760700048a140c04842e2451041d00448020b1124103011450444c0e0503400071a481010010700440240c40303694402510480790b0740c825068802400751500344106000600180d46c480712600010441c50129045d400300c1d81c0100a0300b1902c040000740f0580c000e801d880c00a11030120b81600f2142d500381c100941354840c0c0040303031000c01e000366125400b041d11710071140c481640c1d07594201030f804c0c0d4144002240c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 448939613 1250 448938363 448938367
    0x50606040603030e1203120a050708130c1203050c0a08120c07020f0405130f061a061e03100e0108011a0108040f03030b0301020405090c03040c080f030a03023403080a0908 75
    0x1242485c0140d900072084100a41c1d0518101d00710701c1d103680e0301c101c843da183c280d1140305020500380c00043d103640004800c0c031509980d8405445403849056240704600d2886211080b40050500ca01c0a0b51000700c409010340d60019111304000305260400e90130254009c1e00d00010031584450107045894503030340a004903600c0c60202c0204002003000801941c4200c038000b0109000507102c065200340c481c400c441c0042e4050300303a10b40c2d1401d00c0035000030074000d400030014402e0044034801c4840701c03140b8500d0a5581c0c2d585a2901c200141843c1e4800c507804a0080b0000c03c60000c190000610000914040080b8204a00045604030340644010b80b4a03c80b140c03942d40401d100e0303006071104420103800580f03401c3d903030404110440d100b100c0b12840001e011060004208041e0483c0700281844801070084540b401e44040d103920450201c5024941d0000305100307154402c0d40794028070b190000560080d84506042811400d0302e0500840002c0e0390240054414505407090071011500b14101d18 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 448940863 1250 448939613 448939637
    0x30b2d031b210d0e060d0e0607030c031e090f0210020601080606090c030a0f02040b0c1005011a0301060e0d0c080321012105010222080c011d090a060b0307030905060604060303 77
    0x520803811311844160842810451841c4134400c1d402407425030024917004091b2032a119000800b118011f81e0f61004240c00c0c6186c81c40c0c07001c000144d00068400007000020f0b03440c030620749035001c0092944001d41200c1c941040f940081c0d004034046048907080819581160303266801c2103a0500d048a107088e01c0305050000c112400c006502180a10740507040051400340c50b41107014060f00075180e220055801110600125031041c01004c2c01040c0c0f2410700d03001d1010300310404035540014061441000001d66032181e0380d503118100e0702941900043c0f048441500c0e41103040e200da11007251141e00540c0d030300c0441d603007a0500c1e081504981d0000b01035120f41103400e480d5101d0181040003500d6a640030b01000300b8050300600030003035441041c2c03082d006080c0382544060a08000c02d100c5410b202d8004001c08c40034041c0600021550740031641c14030f16a6810030648000c1030160008800c2c554084108031400c0e8150748448a894000c40c1150a10381c2c03248100010f0355078901004000441c2580f001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 448942113 1250 448940863 448940867
    0xf0801090c0312180f0f1509050d150f0b100c121b150501080f010501051e031e061905100b0f0c0f0a0210030b2d031b210d 54
    0x24074281c05646850070414045140c401c2c0013100c560040072480300e43c603100f00141d59507055020001e15000000c0b48110901070b2003c0d00300c002d04c2c480c00d40520b141c02c00390f40030002c0841c0f8140303020f89035200804c52194505402c1006026582c0454060909600c0c8003103220301660700b290380140e2000b8006414030200004482d40010309070409100111640b00e03500058940035050102070f03a45500080941c50a04142d180ca402c015a00d0744c2a49000010300a58441164142810348260200104080c444011034941100d461140c4c40309803006541140301b000c00304030107005c1c60b501050703c0c1c2215001e8215104943d801c0d90004e04807944a4400c10079503e01038058a0300d52004920305040070ba5074100103040c0005041c84040d280c10070915901185058490010012050710b0100300701011440410301400c2c070400050303c5401d07000c414100c42000b04811201ca010050192101e1210401120890108100450741310b04400585840e50400b44a0f0001503840d1100042008501c00c00007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 448943363 1250 448942113 448942133
    0x70309092a0e040b04060e0f18070e060f10120b0a0f121103060f0405070f060e0409020f03030f0714030c03070305070201090e0903030a0c08060112020f1e040f0801090c03 75
    0x200581180c0c42d15a03003283d0340d60340d1040d400103081c94110540d95250021a6a04941000b002582e107103400084100343c0270346c001103000c1502d0000301e01d030320304d91960030000340f07112070222125a01c000d03001105407c103075200210541c05104158107106000144041044c3d00782e00303024240c0314900044040103512028228010b109010340041180e1850303203c00710342007140484108400d070b00254280010400c00b082040003c25050f202c101500f820258001c0c4a1070300e400e840d5120700e454400c083d0640d641c0030038000134180000d044966501c1c207801d20707a07a6504442030950741c00c1c40103080c0c4002c4440101c11245415483e6000d1440d08816036016100e0f030f000000282c0c1040180c1202240550490035198020801c400c0155201e01d8201d0080f400d982d14002d200003003015400c10b014140e41c00641548403070309107103c0940c440c00310b4100c2102c0741c0261421504120289901101e900b100c407402042501d20b1994200c8640e5100c3d040642a12007181c80140003001514080001c40d0103004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 448944613 1250 448943363 448943387
    0x1e030207080906030f0103110102010203160c060f0e0d09080d0203090d06090b0a0f1505030d03200a05040501170c0316020f010f0614030705150915070309092a 70
    0x30140b4248030b02840840e41c560400c403000f4020121101c01841030248840d0101203e81c4244000d40c03551502d0190103909608010044080c000c0f0303508010700b00301d540d4000c9801d03800c0350001002030980c7c904a01c1c1e60345c41900b20240c040340d2014000702e0a0706010420807141c408075002103103003034020424012a440b44c00400d0300e41595030340000000820803078085000d50111500030a4410441005130110f80b40d81c01c41000125412008100a80f0040703039000c0c10020905000900c0700b05200554142e0a29640c030796801a400151540082c0d00a0003800541e44281e942400c48d020300141004d03130f03400135901728440030340510006904038032031010340300f8000a610640e00341085207049a801d4885143e40030802a0300c03010184a02d0011481c1181c1c2003070100c00030300b17103a46040c0101d10458100c400e102041840012908403548900c0c0c03890506580c820940ca41d56103c90600800171800c50003015070190030402407051030f810300c2450701c40080451060315208415a0010b07548180151 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 448945863 1250 448944613 448944623
    0x11517030f03010609050a05180705031305060f0403180605160c0506070f02040b040c0806060306011e0f02011d150406061809060b010f1242061e030207 67
    0x2080c0c1101d01c8400245009201c1c54403501540360402d01041a0408030390030203401002035400030303050311503025520764026820741802c580d26281d403c3d03042d00d107020510010342580718030b4051000d01807021005902c9913000780e5030b00c1e03000305660b02c0b04a0900424440c0c440080e1081c0200d58441c220b907140818111700c00c901b0450a01d40d00e01c04a13000f0f4000e041c0036201c41038071060960030343c00d050103002000c41c801ca804000288000034003420444000c0c043d9401013030080002406c6034040c0c10030f1550920030f1040d080c1411000040203002d0521416010019400c10600052158220000001000d04200070340340c0a0480c01c840d4124210080041d60000d45420000440d4158441c030140b660340c0c45400401d1040880c2002c9095600d138421290410423100080300c1100d034001c0001c1701c05054590040364014207103c007080060444a0a8200040c15007d41410810008840030441c1100303125100038950b21242520740c29000c8081c14003d50b40003040c0e0a031140309600609069100b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 448947113 1250 448945863 448945867
    0x1061d0a0314010f0c21020714030301030b100806060a06050c0c1009052716110313060219080a030e01020d0912080f010b09060c0a020d0b011701151703 67
    0x25201c00708054184650002c0030b0359500c6032400c0094040c05142c4002c8000e080004980500e604012884c034040480c0d6444140c1c041015800c006d4281070048500c4410380882e5141e584900700741c2d450000640344a04004041d103000103040f040400c01900c2034400a0503c0701261070000f043c3c130075501001e001c0109020340d81c1074507c03554800c2004100e242c0c00d682c461041c41e0070081070200940c003140441c0140030101201c4484100421280340d40040850340c0c01c0d850398172008041d0390324044104541e850f8040414401105440c0c2c0c410b207400c507101e607422039800d0700201d68485181c400b00080601001410820340c0c040c54021340049000c00f9460000628211801307807041c0482e282814200c0d118540949000b000d030341d10141458003c0c2000d0080411075141c00d600009a1203003070919402010f000c60791340c011100c00d00c040c00e0001e40141212800416500c1d001d00c1d42d6409016920500a80000f42c07206048148103511100d552080341034440c0d420019036145e19101c4030041c0b5518801 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 448948363 1250 448947113 448947119
    0x11205030706090f02300c031009030c05010203150922121b060f0e062e0306050f01151407140a080d06050a2309040606051512060301020301061d0a 65
    0xd400d00e9908000180603140315481c86c000c48034010540d00e0311412505130b00c0b094080360990340101b500706010580400000d0601b21610f000d40d00c5403031548020381a9480402003120100800090340c1c04041c1c00c403500f030140d5951180605551186515850008503603103000c1e0006824194405000265800c112003000010403070803603000b0029000b1500a6250003071048100300c903014149407080c181d00035110915010134425607044420208420581d2200c030302911312076240391900c0141d504072238141310626100401000448080c410320b41080440f01c06031481078456019004254601070303106250010946514490044c5000304510b14092010907100050180c2c1c003d0241c141140c80108041c0d00c0c0c40c1c10810214a1030380800901811402d40700200001542c02210300601198880519162418400e00400c140d40202c0c0e0001000c11542c568010610f02a141035035010703050b192182e40708002d050a0780428480c02000c164204040c132416128040407110b110409400007464503a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 448949613 1250 448948363 448948369
    0x60e01390c05150c0c0405010e0415020405210606010f090506030c191115061f0c05010e070810060b0a08041b091d07030b012106091a011205030706090f02 68
    0x8100300c000c508083c00103091881c0399007032000020307a140c200c804210035803410503541c90022000344001c0100d000c00c0d00c02d41698109a06590207004054803410082e804010b509081c465000c0c0111001e10410b400076100b58030500b17030300700f07a0891982c8031585503242509000c1c1540010300382036100b06050018070000e180c2001c038040c40311040d076614150700803403109460404840100c81200c0954003000c10400751260581102020640b01549031030421020f03007203e5040310403400504950910030210042840001d03540140c800c80e1043e180b8500a4900c11030031140288079265180d402840080c412502030000c880d4885c0c0200a8401d02400c1a124503100810320380040140b981d892018243d81100054034a245403000c900408405081d44c0701e03181c00034814490390030b101303801032030a41c0548180501d2910300c4c0d50010701441512410700d84010000c1c06200480030340d031019800001e4078440000c0340812240c222010354500170232602c1d00c0e0b015000010050717804c2e681d10310a240045c3c17 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 448950863 1250 448949613 448949629
    0x12070512030c070b0108030a081302031e010e0f0303091002070323040303080a0203190b031608030301090c020d0c02041d0a060c122702010201060807060e01390c05 72
    0x682180b4080d54500c01c03071601240ca000103070042c81c40e82c1d005001c0212800d820203841c641003200b21880036940c3d001752000a14003041044541c030038004040070b5000540c015000740c400c2c1c018003400d039030084640072820395681c0000c1728942c50540c08130811070700b4180d42d5030082c1150341c0649032450441c0c1040c00e44480c84605000d980d4414040000c0c10001e140d4440a03042e00443c1250b41940740d4248000c0e403072a401e01408403184202e07074580521610f59000c000f40c500500c038040da103129441d80c62503020707100d41091082104050030500c030b41c101c0d144042103482042d034440e1134019000ca2b039a0203010007030008100d403a814004400e086062030b5010003416200600c00c1e0804991481d5a18008000c403542c812402d000c41d080c0f180c82103a044c04082c00c0030407811140c4a40509405e140010ae01402d20b9134050380e601d00070b5510100c0c1c0c42c0d91140801300201c40a032030301050060518918445611100380c0c50a024442c14107010540307014901c14800365001d901c03c0280940c540c40054014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 448952113 1250 448950863 448950871
    0x70f08040f230d030c050a08340c0c060801030206041502100219091a0a1103160b0708070206040b0705070f08040803070b06090403020703120207031a010306140105031207051203 78
    0x180e000105903107000343e25009400e60200540b800c1c80c100686000003a02841c80075200015118051118803c03000f200130032945285007040d200b003100d807040c0c80090503031012b101003958800d002c12804181c5602400c00c1a049941c0606480e185c24505034009241e0403110101c40c04500030f44412800c106400d00140140611400d007000381900c8081c005000600c003540701070700c01c9603025030451034001e0141c150f4801555606000b0798440107500c0040c214801d001601000e000703404200310a20401881c41881000d498aa5541c203451780030041c1c0e0307501c104560003806861580c0004501d50303c914040c1400138410b104008407650582c0d03031210f183c0c000d9040305042da880801c0c540d0920100d03612443d0040c2050792420981d0500d500c0007902c6a615000c040d004001c40103200320400d00c00c1100100854010407107011503110b01c840c181c14004284415505142080700c8664a2191860030078102c800040041000d0701760340d07200c1d12168000c650280c8650182007560004400700300011841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 448953363 1250 448952113 448952183
    0x17040b0408010c030e030436140a0203221b0e07020106050604030c050105220e060f04050f060111031b060412051303080d02070203010f14070f08040f 66
    0x5607030810300c041c0c1c00c464000c5500800c0604100c00240b5a52001c42150141c403e0130026a040c0c08106c82d00d121215403010310395841d0041d0794006118407506074441504032040300510700c8651a03c0a110044c1d0006032001c00c0c0c1281e03c042c19000c1c29081c02c0403a00d42034030440950541445900083d0010b4944d580010042d1101004001d0030780d90a10454000c0d18007217404a0400782161039490f070201650054030706000d40001c6554000c9220a6068001140c0c2038040c0d104640302d510180d40e10700169600c034000d264a2506c00440d1925014085c42280c41c0903ca00c06542c0d0795004450281a000c0d61001c50301080000b9018030344058000b000c140c1d051801024582031500e030110004030304c9803200080010074014440c6842d00b60041c802200c1c0c1145034240c40f42400109140240300300c000c000c2d859841e200185a032807040360800b008a1000030030741034050351902425648144aa2902400110b00c01c000a00245200300400c2c8224015a00d90a107403100c0c1361038045101d0005041c2d51 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 448954613 1250 448953363 448953367
    0x5030703030b030c0105160803071e0302040518010503150601110f0a0b010602010c0516060204150818010509100e010b040c3903110a12030614060702090c0717040b 72
    0xb0316400d080091014501c002c2c80c00728541858201c810512445c542c50040100c03500101240380c0e54410003c0441e02014800b6500c04080c084030301600a40c004e1199a00407403000741c0b1002c941b040c143e0418101c803000340140c9002d002001c0010407205008100034148480d20100082c03408081001c140748510803001040d00007103600b84403000b003605a0040c0c0c1160b05041c40395080e268800151030304940f041840041c1c44441c0c0c80e081d400703401140c020f505c40d022208204101d0303a50103140e00b802402c03260b50069600720342000d40d5007030720021900c00d01954460414110994110746c0001c11104415000046020103600060296080c9801220014280c000030300c40541200100111401c2682c04405130030490407401145955260005014884000414085004144007080b0b61a0b0b10282e1403403400ea0105010703005113114040c0c802c544c0c480d064040800e081039002c50301c203940c000f40681d01a58030000d5580e002c3d84002004c682c0d0b00900612200a0581741000d040500440c5044607 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 448955863 1250 448954613 448954631
    0x3020a2903191a0315040309030210121b021b040902040204030c08100c090b0c010f060e0a291c051c03051609031b170102072121090503070303 63
    0x5031440303050400e0f01c5042c1499032050700d03500024848000c2d1404007050910303584a05069034250150381c4080d411a140944240e030065200381c0d141000c404966040081c40004ca810307219800c15442281d02685c00103003d0700c8019003410f541c058015000b00041004190341c3e011401340e0704254000c030707210b0710700c08003c2c0b10045061101c60904d40600a04101003d60064000d002d1419171040f109140b2002801100b94031f0203411441560900c8841401141c0d611b40c501104d50b40c041304c02d054020703d4500940c0c5040740054800020020781080820804092410032010140080310800c0e842150260f80000607014081d880840c600d9044198508801d40c02c00303070984100070b0440c06808800602c14804079000413146058a4200000b01103d0008a2000c0c840b0541508540513086c004850f07a050000150000c01202d841504580316203490104100d01d03280e50071103105d0200744100011180c5110a40b61400ca10001060114800ba802e440b020304682c4111001c0d00020749581543c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 448957113 1250 448955863 448955911
    0x60908030f1b0a0507020609060c0c0a060c0308013510050a0204030210110c04090c1502031e2203081b06090a03200d0504031a0103020a2903 62
    0x200d038031800d121a10b44070390050300d016007080e00c00c480554003031000200f0010259110003054035005500600707102d589280784001a03030766818400d1003910038034a500c004989944204a454041076154841c401181d0900c02880d03442426410780e00b0b0206400c400010201044466000c0d865500401401c1040c803086821000d0310001000a910301d4010030080005032030320a0980032900c4645018100d448614415604100a400302154400d080240802c01e2102e0a00100116420410007031b800c5015a0401e9841e4000ca04445c10001400d80503c909040101f000f45440f944000e210110440c241c480d000c1c00c010f0700d41041d0703698440403034803503010740300da0526041a50f03840703005000301d15050740f5a640c0d550034002c00400b00840a502401c1034a25011840b00148003a400d40302c0d6582c10703200040194000744000d990001000c00c8440c020141c5504540c140c0e90041c003200035290500d40044020340400400b40d2462a40001ea0211111110095400380801c8000041e56a50210380 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 448958363 1250 448957113 448957141
    0x102120a0b0a0501080f0402040e0607111b0306160309151a010201140703020702030c03060112031b020102070b070510051005010210021c0903050c0f0a060e0c100e0d06090803 77
    0x410b0040c0c003581e10603c142c1e03800840c0c0350b03400402a4281c481c07560f290f201240c003900d082032841c8104d00c10301043c0b0450300d810003120400c81c8030728812940d64203d410312142019007099106d941641050000c540f0051411040030780004840c203001c6688141ca039034000c002200c64048885c21990b801e403900c0c000e81500065100d50744244024401c000b1078051003a811140601080306140d400214101151401d004d6481564801003c2d52480d607035070300f041405a40c400c107044000406244c409000150612a4400041e4060303004222481c00c010a09a0710740c4490001d540c644180300c0112100e14040c01414441d02d02c501d0b2000300d01d07203040000b900d05280320740204403890044c0545200ea26030020700d11000c40c44100e011441a24a09050b56244220300d072010403070141c114901148040011103084c0305100f90420011402052411510f07005e0050800d640200300d02d0b110140d20344100b0b80340c03400e40001809890300f5a0325507141c2040b12901c540888262074040b0401510080d8024 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 448959613 1250 448958363 448958381
    0xa0b0f01031a040b0312040306140108030a2106090911030d03020c030f0d090804170c180f100f0e0108060606030403050a0c08120405062403070320030102120a 70
    0x7818491a052000c80400710004140306038040c9607078800c1038a41c1ea80c100301c200d5a4500065901d40e840e5201c1c20300502030070803040c201444030014000000c40f100000100e5248405580d201c0035842e80c6803581d4100804c200030f40c07d480c5528ac5c6400300b2081c00c14803c0280181c8100240c0c2860b807200300c281400c02074a9512981814030520103002c42d02c0b8040700b20740d080181030207466981c12070b0300401c1000b001525405410300e000402e0100b90741c00203011a03a2002e00760002c44d08085003d80421004403501e14603040300c07030315840c0498908100c0408840d007010305070307405078905500c40001d4207154040380c1c459500c5408010040010200512203190441000d0b02c20528619181d100a8900c0c4600c10b100c8040208000c040014841c0c2d1501f07480c12820942c060349690708203400c14030f80da400151442c0d65012425110030425202e00055000e072000013901134110130b40f940d182e0246848824101031070a4a04000c0c40c0b150f55000c1c4000c0120b40c501038030604040c1082000ea0040740d01c0070f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 448960863 1250 448959613 448959617
    0x904050109020306090c04360c020a0312020a0c23010f0b1c0537030c0303050601030b011d030a0803101509060210021b070e070e090408090d030c0b0a0b0f01 69
    0x1090000304603c034035000ca1b1515418084070036240c102e07141412002403050040c505827515a801d24110b90100c0c03010000d9001e981c07444080b024130080201240f06180d0303c05e000c11510109003002500459620120109220412150381c3c0c004041d1800e4850348002504440d94500c0180404c0c030f00720030122501c000b0a0038080801e0f1150741c91503514400b032411240f02c1d40140200e1000380f102c00034520b4288908400c2c00c8030020041c9400b822920008070102c0100f41031000203a80c6500c20f01c94551425416034900f00d802204e035012000e118204544140c02d40240040040807807040310096015884055480c1095031a20240900454060414100304503125000704051580040c0d0440240075440c1e006035a040080d00c4500e0318425040400c500f8080c100b8002102204828018424809516441d110071030300c0c0104441a60f045400410b1442c050005800a0903c00792100d209486410700c03c810b031740381d80c0328108510320448041c1c8100751104140d200500f0001d0300d9005100c001c2c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 448962113 1250 448960863 448960867
    0xa03270503130b031003060e03040f06080709060302031302040e1002180a060207030515060a15110c0415150201140f040303060909150504030509060711030706020d02030706050604020904050109020306090c 90
    0x1850304540030407086c880500341d603840b0084400c0c1548244102d40080c050300c080030515079680d42c030240c1540700c210383e074202040c0c4010000441134000d000300d80c4265030307111a50254001c50342c00c01c00102450280d41c1d8207849001c5500e0710048862004003942100c010201001c100c3d0f010410802c46c80315005881103401c20001000000d00c000f9043e002d00701c03680d4016a0b1681c030640403a20340681da0340800700304030042030308140480d000500583c0400f08503099440c250300d00c00a03c01512101001d150040d403410408100070305501c0d807485401407080c03002007000c034020b110b00300c21781e50185c8240b0a4901124203020415030148606002450004001d0000b00b40030b4176804d1a03040c0d000112500c440e00c070800241050300c5101140c0c44000c00800c600e40307401d15418101c0c00440c0c042e8034680223108643c008105d250001409210b0b051240d802940351500300e540380d070050074028041507041038090081c0e00155a4502429020b41103c0c0c0f00141c807403070704404000711080050a00380c117110003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 448963363 1250 448962113 448962121
    0x1e07060c0308130206121608010803070303020c030c011d060708040c031b0513020a0206090a0b19020f0a03091a0606040b0a1713051e030a03270503130b03 68
    0x8450550082074050410000c2aa195402c0040c1c80c5000d4100a512880c00103040102207454182c1301d020750303124a224034142c0e07070341c2c40c0c2179811980c2805200080d900034003400000070b10030b4008004850012080c4c9040c54a00302e00f80717082d500d54001032940d1450f800700c1e02c01c65120130001d065010949181c14002810107403540d00400c2400d0001801e1405104a483c54035680d5601c400e00070803018040280d007283d0b110041000b500f0050313440006004110206908860008018013401e40000c1801c0158a41c040e048035084038803254907520507000d2062018003a4518042c0900e0a40ca840104261605143c2041d2965501191801000c02c0c00207020403601c8900580e400c6e1419020a05c2d03440000c080c041d00c0c140b400050305d0300f030500c400341000b86204098059420a42c4107004503185184084541d44200080709111031065200744101c9240d0780c1309401400c0022103c3c01c20843d0300c1c110302d40994401034182400c0e02c0560000034001c240c3c6016011600003020a54021421428 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 448964613 1250 448963363 448963367
    0x14010b010c080a03020c07061e0c17030405120c0304090501092a0201090611280507170702130c11030909040807020f060a0e09060a08060402090a1d1e0706 68
    0x101c080001c0c15114000c10742101d881d01030317412035411415800865152642d0f40c00c00a200c068480c0e511112011040a0382d6001c9005104800c1096030000c5007880d03008080b580746a56810040c010780d07083c49500b0700950300c0c9078842c00801e500490b000c091030b80d803810501c035032003a900c061f031110720002d02d00401042b204614103401c3c0407a40e03050742894291413914800305e000d040100b8025004a14040d01ca40c1020450402807031100201400e905241105020314400504940c078030801245c0e04011038800240700d2001c0d2100305410030b0f240340c00e1180d0b40d0080b0304600b4026082040c466903070f481c405549a00241461102600304000b14948920320000c206440c8014100910080012901340215a2910381b81090140f005e000c841c0c8807041400c0040944c1e8020200d64003a4412002042d0341c0d0615840040690700503100801103034075542d00340000041c0c01003890400a585902009c0035024008140b81c1c07031b4200070024001507a507210100c10304405882d050307215074071450003004126 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 448965863 1250 448964613 448964627
    0x70c030b07020606120c010c0302031312120e090a0b060409050c0304050c0303090325120305030103030306060815010c1a01080c1816050a030902180a0b0d02150a050d0c080414010b01 80
    0xd0420701c0d20300d01d40581c915042e440d5000d210171500541000742c0c40370903400e510641070100e080c09080c0080a0100000007500c1c40e213440030a064101c1d108900142060383c540d00421145800642001c0c9800d41d5060303024219101910940c151080010600050000c2004500340015085010314a4600101c000999a00b09845c0f01300110700b08480c000e99a00c07200404400415500c850b07403005000c0703490002e04650007400100c010905d031400126602c1d02c6458090301c40e80c5d0780f584003e0307100324503001900e01c3d042090702120034114071002d41d83d08070030b4521018002c1401e03c0003494101c0807482001444420442405075900c40c90081101c156154211054013a071141040c0f0741e10444e0a104802030422000060f41000b0140009140784442582a03440340d09680f00400c0300a01c00701c1082504002c40700042e5101e10304400700c0941c83c02401c006d2458640300e040880c46c114584c01007a05070f03070240100c0c0d004644000108014000148100c4c64416072007402008504d0300070001070402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 448967113 1250 448965863 448965883
    0xc0102100c0903050601080609100b0f04090203101e0b0607050706030b01020a0c030c05131515090806090307020114030906150402040e090703020301110a0207090e03070c030b0702060612 82
    0xc00e495042141d1903500440c503550140d50440300303503041c40d80c40e04003443c0d580800340c0f00c41c0381750f02c030300007800c0c0c803480d071620070200c17007810080507901480c0002040001a046000040c1d074580a00b0206003a000090300c01c42c0150036451500090081c0d81c00e580da8201ca020f0034140340242400c0202200090000c01c851041e100c95007800101e45408500403850041462130007807945080c01740120500105542d180700f10340301240c01d4803a070b41d0444516002c3d5888500030300100b88510f8000c0c0445003010008910302d203100d2900042159541319020b24000d001d80700c402c22500005400025540c0c007001e51040c0c43c1c60404028914144101c00c26500c6400500740ca55805030a2543d45c5140e40d1501214010008500d100301503043c0802013646a100c148802ca03c06d62a183c0d0116092540304140e4114030036035009400c51074070b807240340d001070020780d80e80d05000d0008000d00000291614400809903008030311036401d0b498040806851f03c407014048610580c0300d6074a400c0c0100c000103002c00d01d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 448968363 1250 448967113 448967143
    0x2107030e09161103070b0c1308030d02040f0b0f070303050a240f051f030f0b0904030f0e04060b0405150705071e050a03080304081303060e250b0906160209011410020c0102 75
    0x45e604e414031104582c149903420402140c00700281c03012f0b00011540107881500c0c1c0c1400103040c090f0703641410613850701c80c655007142110010b01030745002c03a0107a03000c3c2c0e0740410311140100d80403803060607000b007401c41c4003012416001491804d000204035090808013610382951382c040020301640a102c6404803091601080507101c05642400a0f07082e00401d540c554080c3c503150300c5090034074010b400f0641d00c100d100009224400200030500d030a0040c8c2c41101c0c001c0c100070345080e041009120120005007401c0c2d0314450200034001c001901002400d004001e2460740b0700620120305034010740d0a5803640010b01c510080f59050000c907448608030fa802640c82500e195a480396000d80300b0300e40c1055031010f8105407800e0040300f038518021070f0b841c00340c3c3c10420280280e2100c003e81d4450500407800f800b60b10000900c01807513a41403490045c01c904201d0400000d50305d807640d00082048400b60040440e80310340403000c0510b130401c0180160f0460450010b080042c1001c00003d40c0da81030100360b03d070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 448969613 1250 448968363 448968367
    0x1c031b0819090902070c0303020f06040201080a0b0a050306041110050a020607050d0905010c020f010c0c05060402011803060f06050f010302120a110903120901020706022107030e09161103070b0c 85
    0x5540108060b00050041c04015519280d2a003491030301080f0350711040d4090300802600c502e0951001c2505445aa4161514615619842d00c040000c0001c14040c540000100c2e00c085980c0e5801c00019108911840c0640002d079142c60a001e1900604030704441805414060b280b801500801c1003035124140d481c080e511244800c00010160420300c40140040d481c0c4100c0c1011030350302003a510310b0700d030352540280640781c1c040508640040b01e50034060860342003080403400562260f941810501c40c001190b0009036180d807a80c00803154014800c014696540c1410840ca0a0801e15504c405809090443c100040c103030704e0790100c640003421a0b049554445007441112002d4041d6106140058201d80303810f215104091a164040c104640c0544140312000a01501c002100e078100c0150321507407002c180300c03407207403400341e40081c24118144070b50012680b04a48901d1ba08034401d031f024101888100302d01c400d018003078580900e0541440c0c0c100300000360100362007500154200000031a816 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 448970863 1250 448969613 448969657
    0x4030503012702071208060d05070e0c0714010504020a150503060f0406080a050604020906060c1504020307150f17060607020d061517070e0103020d0b04020406051c031b08 75
    0x200040b10284252119201203820800e0009103a40d80107403100e0340c0c43c1c44050f910b4080c05c100c001c40544000524a078401841804801092030486030050a540030382814a0040e694401825040481c0c00240380c1d550f000b08401e51500f075041038020110f509900d1003000c07510700000c1091000400c0300c4d000d04002c2c20700f02c8050311954081c000502d10308054881e0321030b80b4075042d40ca8a01c140c905a00c01c154502c08103580c3e107440c600710b03149551008010101c3e405006048018034a000300181e13810300481800003542d0603086141c80c0d449566a56807962419040b001815004900d40320403c85440c403810400b039610307440115038200790101d40c065500011490a0806080b01004031182620b01e4040041c01603d4248a80403402c54001565100e0303440300120038000e502484080d5120130000c0807000407902095174160864005400856281d4440380440c14407440c80d407004014031701e612610000d050b4400c0c42c11421402c5030085d0f003819040782d201c0101501541a2960448888c0390501c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 448972113 1250 448970863 448970909
    0x306010f0818071508060301140712020f07030917060123040f060f060207060816050c0a0210021e0109081911190b0f070c061a0d0b0402040b090403050301 68
    0x82c00b680740d40340c811142d07015107607581414030400340c00c0e29501140d540800b0804034601070142d420003585106134003007590b5480a0480b0000c1000303522648141d400c00030811041d240000811440340070f0b4032003000f507520317040507041840c000200b42e4540340c21035001880540500d8800e5024914913008404c1c80c0c0070b482d0001002480c0c1c200c07001416610b000000203001700484821400c8850729002d40d1903c035a41c14090f2403805080f074540d258101312b0708210350454040c40c00341c150504104201e50a42c01240d002c0795401707003d40841009688032080b115100c4c0021405031039a4000040244903841c03a076a90300c3c400d40104a40d00002003507182e07400740554824080002516014011107900c4074182000c0c10005d403081d003050b0b4601d103e800020b0b806854404200b400740032940e9406501c0c1e0b81d46c0e11080010462441c110901308078224480350b091352607080c40c1040500030f45490b1070b54201441004100d4501c074000074002c80c0058100000701ea0402c1c00e43e81102e0b4680b40c8092140e102e440d030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 448973363 1250 448972113 448972141
    0x50a021014040f05030d020a0c090f02070203030a120e010c1e03090f08030403091d0601030c09081002030f0115320c15010801060b0414030c040501032004020306010f08 74
    0x5041c080410108000640141905014007100c00550a40344400c020300c40890f100c5d14a80c0c0003400203800900c0400203207100703038403200701036040701401801c00a2030741c0064150f5005a07400000580c1d544403420581b05144035040b06042d11400821060b0507200d0044c19040d916a8003011a12640f02581c500c14000e80050314200c2d884000700786000543d20703100d0318582080e00c0903000204424008240c122030351048145200d10307100c0c1105142d40c3e0000450140101d601d1000c10065030f210b00040c5c00404100c1c9150060801c0000750312441d0030400b221041505030310035007040a078070214003070300c0d81c00541100b0fa40c2101c04021210310031145981c44180c400000040030030400182e0600031403008101922091600c8500845a0360703a1203280d030aa512038096000e10017403c00c030421865840c1c01149241075000b505598100c44420000380803144264401e60b040c403428629101c2c5014480600e0700034030400c0302e00310301394244030380020b00c0807800e0058041441444808a090030380d600b46 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 448974613 1250 448973363 448973387
    0x1002091306080307060b01030501050f0d23030403020102100c09210c03080c061005090c1b030a020c031c0804021c3c1208070c06090f0b060904050a0210 67
    0xc041c4250359039205865a2a40201e00c02d4844902c1d0008404056201c0e0107128101ca40082c80c1124aa042004020558944110484031018155486035101501d01032801c02d10b04120059511540746000186c104410544005200c41c50300c1c0c6c800b40030300c2c0c03c050b562054030413001740d0340540404004120103400807114041e00f080741041c400820041d000d0300a10407550800b0594045496248040c00034449500408d940101c0410015100d605518003900c0f21140c884030603481c04000540690030f5501c016544401a0081112000541020420542c00c1c505844840601c20000c038401011880041e0001307101d003100f141a4140c80422100c03481210b0f4000540f004800c200320301400b0503108000c3d000a19036111070a407000d011006c50038620264001205601201208030708581c00300c00140f0750b106004070008800d002c5801845243d12603480380304c4910003030040b03080500c02d440008041600c24248081040002500440c204001c15416514a19051340c040404d4840380d10b00c0d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 448975863 1250 448974613 448974649
    0x6051b07090204031415040b09010902120a02101d061602190302100c0f0b0406060e010303020307050105060916080a110c01291807050706020a1e020f100209 69
    0x1000c81e65008642c002d00c1100d101c2d100659131402da01e0a100c0c0c80c0d4200c00034881d02c8103a16030000b4085804046e000c0c1d8405000c90000900d1021580040c600082c602c41030040e65000442031011401e02c0c10318114540c0380380c20303c2d82d1881c5d80b050b80c108240c030743d07280494000e40c13010449100ea8400e0900d0701c00941c0c1d0045c80c2604940b050361007048008010f2000782e01c1401003001c50b8030002d00449a10f40080d42054610341888840c0d00da0b0501120054002c864071076888100150300400c200070366020f144280d014560310780c510700b081130070354070040d1007244203018200921103080c031040054030400502c2e00f0000f00c580c1e10000814020500c5428440c1c03100c070002441c007101201036110000c4401e40c810f0038090001d40440c81c10301c0c0c580d200207841d0400c0d145d80116040141d910302c116400303441854554901801990b81e01c0617600101030034000f00b0132104440300c108202d0343c000c280340f407190700c02041c04e0a811802e8655075104032250915003540054042c105849000c440070804d6804c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 448977113 1250 448975863 448975873
    0x1b04110307050a03060b0f0702061b010204080609010b0103150509190e0a06050c070f0b1506072022151517010e01030b010329091f02031006051b 64
    0x2074002d80b103980701d200c035100000d14040d00441c02e1300c2c0340416107980c10000040b4030b003802c03210b900340304a5a200840301c0d00c1c4841d03400004801d0b004240010030280847c43d02918480c2041140c3c3c42c00e40d8400011141810f0a000d04903c09083c00d15000701201e02c01c44a52a090b2a890740c40c15051034082114081c4504000d904910040c00151f2010914852001005140e690410961041c000c0d0440184070341001140316010030640600c00303402204680c2c19a420702660000500180d2107000112540008811111110400110524000c0f40140c490f90880401d0301020f0b89121030368000107280580d540d4a03d6451070740d0350783c480058490700340407400121640002034131000c41d80480000e040400000440c00080300306440303049a500403540301e05039080d42c0c1d81c0010300e91255448a030025458490307000c0c000d42e0b8040180111408005010251044030318404411041c02000700400d00420078849080d4140907108101c820a103841e913121803500310b251702c1e60300858217090303041d20030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 448978363 1250 448977113 448977121
    0x1206120109140d09120f0302030c0604030e100e09040b0a0605060f030a050105030d0c060b0409061d0601081f0e070b0703092301050a0c0311010f020c060f091b041103 73
    0x12203522040070045501140c40040f68000110348124980c00360940e8920152036000c00a40c80782e0311280094483e0043c0e13810081701e100305514001c0211000e1b000201d4081d6001594102090404a2000d0619088142e40006c0d000700c0c400b80d0740075100034a8549207000090f42d030081c1d81d02074000b50500418103035454000714000c5c1d03a81d406c00d40c1c1c031004031440c103000001c03d413500141c1d0b150a00a95100d0816400ba1500e4150050186030040d58001703890380d04a00004d8814811002d001042c2d50f9810b5120f00722031111894403405030030808031980075100740240100e804c840410070614030700e408a03c0c0c00200c00f245007022800d85c04802c80701d00100380001015006000c40050b502d600c0281501100401107180c0220540e1724414003203030b01006800e14040c460b10085848a000303050030b4003105000302409084031540098452001d03800f140d104200f03402485030310381041c640483d00007a4180300c1c21040d00c0d00351105c802d607055041d4003c064501e8842e6001800c03144108428113440c0c0c58 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 448979613 1250 448978363 448978373
    0x70b04050319110f07080d080a020f030a0c14040605070b06270906251d13090b0c041d1902030103030804140f07050607031101060f0303170105061206120109 69
    0x1d590143c2c031509000c1c90b00305413a101c0002a0b100100c030728020080110701c001c0c6609a9085c08058080003c041c6c0800071640140364400c0190700841c040c4200081c0300c4c0c00503800402c8524460150015003400300030030421207511005847c8503541000182e859078039a580000c0022032803580c80002c840200031a081065150746c40e00f03204040810075600b0710f6132140d200b10a40d240305054111002c00164100c922148580d500203082d150a0000807030f200c00a000040e82115008035100c0003030f403204444c0b0104420b900340ea54010310101102d50a00e41440d600e96000c1c03654500c51076020354140d00203803113903507141080d480908603e00c0840d900d50b1a410001d0030100215820b0390350381605d002c080400100007e0754400c14003941c014214140c20501000f0a0754400c00c0140d040014000d1221503180b420700ca51802050124044104203285240141c100410903001001c0440034000400c01900d90008547c048801c8114030a85542ca80700050340308070751285d030303080d40d5840c00d41d800007005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 448980863 1250 448979613 448979627
    0x1b080a0b1206010b1c110f072405090706090b0d0203060d08030109091a3102120d030501060c1a060d08120414010614060d020403052a090606070b04050319 68
    0x170100d40a092500c40e140280c0c902614402c1040d070000003000c110a46058100c403002e005418405e1030708070844081c101c8000200c0050442002c440d981d03410500c0116141044003800a100c82c2c1085008a80f50042040590280608540e42e058000000410503a5140086000750f51320100c02c948a50b101c02904006005400c1c08030740c0014286100060034001e80f030342a01c02c0c049009500880385200c4400c0c000a0f52a9044a20141c90f802803000141d90b4007081403401319a101c003d201c1c0c01000366004041d2041030f03011000b440012800c88008c0340c190082072100200080c203076486911140003040d034541840202800c10302012502001180840000d1030003640503102c0000b80150440c0464203c508074422411400e10500d40c10506007814409000580c40b100d02c0103082607070382d4446a0400c0400c8921000b0f8015840121a03c0d07a00c003220003041c110150b42c54040351601002040c100d02c00d81401804030714141c0000307020070104001702d440e4072440075504800c0c1040c000c4003030192 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 448982113 1250 448980863 448980877
    0x302030105010e04020f13020910030209090606030103050d030c020a241a030a03030b1f09080f0d0518030f0106081b04050c1603030902180a1b080a0b1206010b 70
    0x80d400c0c000001907030100861a203004980041c00584900d400204000b074906a200d21246c05580a11028a05e9500c2c10b40b142050602514056a1018400300300100d01c1d4000307000600c9030500340300500c00300d5030000b0004024420b03818002035030200c14409030310305643d1483c007d1401500585425410701d003100c01c65860600c482061140c1d182412112440c5070640154a0301070380300d0614800820b2080d0495208510042e0592280303519282043c00721107030486040001c15066901041100c00c2005480c0b111a224000f4080362085120020a07501c42c41208044100c8500d0086401d980c040c464103100d84500703070080040d10354480c3c10746e440c1e401e0205140788000c80e169145d00507040c07174040e00e0710407116038107600e1400551800c0c0720b00c903522230441941015901d00c0c0c4c210050b01c90401c1c1d16034050001007085c80b203240c00424131083e29550700ca0015080003035050071007607a8003c04416000407180401040517171521002c1840c4c07400703d03c107500d4144a82c2c000001d05d4115800180f9070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 448983363 1250 448982113 448982119
    0x20907030903030b012a0305070206031315050907030215090907020723060a0813300507050c060c0102120f040203070b03090307150f0c02010b03251a1e040302 70
    0x1113080c401c00151400c0388a000c88030300e132101018100c242d0f070900000c25004140303e402c20794104003d54021590b250012a400141d488148038904140040080600c81034040400c043c80149000040c42c0c0e120121480024000c410740104108075004401c1580c01020700546081403d140610f002942c40756280f192004641070001071851701340c1c940300d403004800d20240000d4131b843c0424038101d419003001818041202c403285401c0c00003641e00d00c2070565880d84020140701210740703458001d9400540c0c4842c10180301d020800200042d1001c43d120391048402c40e1000e886244680e40180680300302003040700007010a5007003160909101c107850740214020f800b110708041e1110040710f80c611068408500039881400394000040e81c940808800212649002c504421001e007000181c0340420a8400940d440d101400e60f907081c2000070022181c500940110003030048204010070000c00d00420b40b44011060300000c4021403c011140010050a2480c5209900d90b082c610076410501007284 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 448984613 1250 448983363 448983371
    0x20d0c1d010f090b180604080c1302042303010f060611060702010510090504020d08030f070e09070e04091a0103050d0314190209010201060e0a09230a0212010902090703090303 77
    0x1140307502c5101c050a03200240c0c0c40e140007040c00d010306010301790060700c020f4102494280c4802407a440ea4000342000f8140a030040c00c0d5030400c074082044201c03400040303a80a078414082001807000b0310030341c240d03078580041c14070052404032008203015000c0790700550783c41818000d00240e190350100e2000f5240181d18280d5640f512800c0d4120709039601955040480070b600030062000c0c5000d44c2c07000350030601c01441000e01c90700c6a40c5144030f03500300701c41c1006d10b05401e03010000d8451300001404241c0404075060742c01840c0802019010020000c00b0342d025035a640c81c2c88040014098500b1030760348541d15281c00c01d6139a40352188c0d035111500f001070300090400410b1402614944c08180c09510103810752501080c2910f01c80000750400e60f0314a04664132035800082c2c0001400010707005907000503012501000b1420513007803805451020081c0c0083c000e225000268011808190b403a6044420315100c0391411201405000c1020020307500580081c180100c0715010b52208280c0c0d03100b501c040c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 448985863 1250 448984613 448984667
    0x1b130603050f0f04020108091c080f130c06050a0507060219121503020621010b190203070c0506090d060c0309061a090f09030c0a0c050f0d08040b030a020d0c 69
    0x16803541c81c00d49220f240c0100ca200070800640c02540c100b0346c012003100031070f1030050018120303400203a4405581c40100f02088240070386003041381000c0741e110007024900d841c50722042da100e0690110610a100400401040400e04180300303100302d42940d50072007010340d03d50aa1500b40c0b854002100c140202049601023100522107044c001c0804e681100118a2421480e54003440102d9010b40307041c1e140031100c59580ca2000c00c016204034043e056060b4516200c5603107102d100314501162035464259402400a0b00000f80c860341c810098440a0720465102c041080200e1140ca81001d4028031190900c2c4002030030580c07640c80840c0c0a4042c600500920074200311410400c0070042c11a90000c808000061b0401c903440320058200e04103500303c0f4508005800f1850902091070b10807545c401c070030907003084245050340c1845078401c0211408603c031589540c810545101d98450b03880c00400200000b040c10070700d43c0c11342d4401f02d00050300340848010004000d0111f142c0310398004015182640354 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 448987113 1250 448985863 448985881
    0x90406090f0b01180603021605030a020f0d021203131a0702100b0d080307030b0f0a03030c140102030f0a15180e06070f0f08060433080102070c03020402031b13060305 73
    0x8404046003000c0d0f0708801c2c17404c0107401c0300a9030000b07032280100c2e0020164400000c00c10402050b60b04d4040d8003601640866110042c1070800f500301c010115031040d03020107000702000c400c8a811007910010100001214900743d00317100d0207086400750322007940b001c0001041c0c001c1400080440021803c2010802c10f2080040c0c1070b0000e0400f5207019020310000e00164000d9103d00400040140740003100c51408000501c0c25807607030803c400250f0407400d02420040004102581108084001d41c05c51401507504100401e005141d9010580c541c604160006808142a005006541c1d211007015409030030003c058640c40c50300540911440f400501c1441c401c0724001000f00d115600c00c1246a00c0010441d604600a4411640326981e91100200d0a170340040c0ea001c080e00382d00c441040148080344000d13281c0b6403030340030f130703080d80d0040048500082001c000003040d1390781183d00680720b1f11501056440051449403034200a800000c905105211300c912610485206a60603c055a00c0f0004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 448988363 1250 448987113 448987127
    0x2303040309140a1a1804021c050f0f040201080712050f01061701050105030712150e040203070f18050a1401061d0d1a0c0f0f04050f0108042303090406090f0b01 70
    0x150700307640c48048140003130301c2820300024585510f0507503408004969020001d0b0403070b80b15030340c1801a02141071030046848200c1c020540c2c00018080c1c480d00a250010900d0400440100000e042203099000500064010806a0602034501c1c40401241c03811010381481d0420030300441012828100403038490310707035202c441c50690b00181d55480c256112214195161420415903120340e40c1c80b2500c944a0f0f20044000f1401804c0304c50b0081d100b400c160040c1401c3c41036503081003240400010742804080150207038180c1c030b01c51082e000241c075036440c103403400105040160110900280780000645035407180380c14520301c88650030800042e401600304031200451100051803c240d042d046402c40d0680e520083d03020704030000301441c1080c1d48180140d26840a40544032001010a06100e0303800c02c000310300f01c807071002e00f42416142440d8440c45841240a014182810154108803440301d809000b5034112501c0688244610750b00d9500c15005030012940607042285003030600b607115032080c14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 448989613 1250 448988363 448988369
    0xb010818100c0e04050a060303080c040807050105091c050a061b21060812040e0a060b0304020907020c1206091009031218021e011409102303040309140a 67
    0x50018a041610040140001d0007a410a2214100d840c0e030f5240c4480c0603503886101c0913000096088c1c19031070041c102c2c54001d007544041000070f0100740000840062034034243c03032007420125100c010b000000b40c24407594241c4620b10000748c505080c04c1200004480203070502c80d0b001401065402d088000d107064008030301d000016401d01e0789070b5003009842c0f480349071180c1ca1040400c003070380c80392402032610803507120f110412000020200164102d103000319410512040007880b4a602e03010b0000c206000140000e481101401c01044cc1c03180204903069001ca03014011070801c030030182000d92500c400701c680392414007964103207006403001e51003449040343d49030b140c0ca00d4292000704075500404203100d900c50b80b64038415030100075948404040c6d01410711003108101000c249800100016000814100303c40f106000924155944c021031807130403601c40c9400d504100c0341106191900502001010641800105100c145036006481c0c10940750000f426040403040c400501c0f6031040244 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 448990863 1250 448989613 448989661
    0x61d04140906220807050f01060f09060e0105010522080706210c051204141603110405041515030b0c040501110c150306060712090533070203030c07090b0108 69
    0x11850340010910750140c103d171405001190840102d05200c282100d0b01604079645500900d4410444008540100400360040c410b00078029450300002a080b800354850b0b1495041881001d42c0081d9941d6130100e0041040004949103a503803820060070840044030041e00c00010006103820182550041c550300740c040741d0702c0615048012200d0040e000001e4011104165901c00b040c2418904120008803034100d02d9040520a1562402c02e06604441c03400c2400303039040c1010040030620304540703002c1500c0030203408942c0610408082120341842d0700000d0000405500b4440c200000901400640b00281c8440d07072500d40d000509070703a07050003c408a900c0488500e511048181c0c080c06550040d2000c1c0200c2c1c24140145c3d41d94822815a2250a00142440404004e02e15210301e86c4407c40143c0c60500d9005640840b0740306112001021001090b1000180c4900f191020422989032103e003030243c48013141c4803d1154003402c201140d0304d0005003050085407100e032000400f0010f000d401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 448992113 1250 448990863 448990921
    0x60b0f0a080a0b09030c0109031e0215010b13030b0c03010312080f070f030e03311202120c06070807050106060f1b0c05030a080415020313061d04140906 67
    0x6035655030030f9a9005182e40304034001440700f5000c24100f40101401144a9211440c0300d054983c06044c0e4100941d10344000c41d8014003020040464082803030b41901c106a203015074034540454440000b460f20b82c00285091108410450948003c0300614142d074481d00c542070020061880445040406030341440600e0361f50b40104883c140601d404101c00c00150501241950000700e0143c2103402c0300585101940f1300707404811074820350b002000c80c481c3e40d2007c5c035412103040a0380b07001c554515501c02405542e40e15480c400c03003a401c210140c42c00304000e20007551079581c0d2400041d184c000d900d04035029800e02001185050148142001d400c40039503d6440300550001d552103c10044d0700203564940f0748800202d503946081c03007950441402446c01c030340c1d95440c000c941c4c19151900142c00045400600521801c8410102000226071043c0b82900c040030200840e07010b29041040303043d81c0145481d90351030402c0549420144a80b00e06001d54a07266070300d85c5000031011203244407014808003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 448993363 1250 448992113 448992133
    0x16050307080307200a180207020f01180504020d0b030610080d08010e04120309170901020f1606080a0209031c02060a111608090a0305012c03040b09061204060b0f0a08 73
    0xc0710018102c2d400001c1002008030f540300140b106400c06242c6c0700c07820640000d00c0e2415410100e000d140086003c1c40c1102c607000c103100403858400c00034004d47e031181d500002c0038200e05000e0b4010448209005042d603060341003400c0f1403c1814214401c2003007500500e5284520103003e114240c1c12100d030b04240100594665450340044034080048401745640c3c1c442400c0802d041c00440e0080c45a481c010580d00c145040c006443d250365032100c0400703035103c8424460341d1540c10390200c0854a840c01c202d000394441d1842000603000e55881d8603014070a0702c0c0c079840c03800c0e01203010643c641d9064098480325101c558010040d00d481c500c004183c10f42c10056291402c0c10580b40500342ea0064000ca0b0805002c4000a601c40c4440c0c0d1061310181c0d1500f04541c1e25008184440e5803800c0745084071000f01449101c035030344070f010f248142000d0343c4000c181c5801603226034044403134800c0f80c26030001040c545032a0100040c400b000650b805881c064042c046541050154401a01d0b01c2174010105460 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 448994613 1250 448993363 448993403
    0x4030b010f150e0a05102f070e060f010f02250914070c0318090612050106051002060f04031b0507170f12030402010314040f0201020c0a0509160203040816050307080307 74
    0x51000d0040400c0007c205c0c004d0498040c102000e10310300c8004030701c0700b44000204103600d0714a41e0340009900300651428401e4035a1151004440914207003401c01d0502c03100001603050101081c60100e80408484000746141c0001701c0c010300740d0780c04038400c0080811520880380140300407103068011405c1c030030b401804240a02d200e10205500c4501d80d20300992a051640240d03043c6502541c0300d8405581c2c00020000203000e10005040c5c01d0303500180c201c00104c8000d55800c005000018034015201c0030405140c40740014400030f203a02c030507440c401152483c000c2d40e1542d070f51154444406a03800751072181d000104604081031070903c02842d60700c0c0350340d03410f00041d400a0401c9050558a00c00501c20380c01d101c2e8800d2003280128500e164405440c0006402c1c071224242c101c0c801c4031b81140603c00c99842d8002150810164541c048051501010680c990b1040e90000105441140b00c41c82c9100c0726060203100351403041d01030b02d10041c2d0340c13080c140e0f40f80255100113000d003c4001001da504c0c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 448995863 1250 448994613 448994629
    0x1c050415050405070b1803010b060f031909060c0206090d09050102120d0f0e031c140103030503060409051618090305091c0209070804030e0a0501080c0f04030b010f150e0a05 76
    0xc1c0101c0554444c25581d020300245a8404c0c41422003503c6004d82d86e00007032900b8426200a10b000340e9001d490040381a072110200e12004020b400a03501e10090000c035022194880390700c85602000c00c00444603100000b075610b55044a8410440c0300f2408162003440c800e203801012103c044c0c00801320001c2d01200b40001d81c1001a480581e10b0713451040b403007850501e004507034002d641000615500c0c1000400039100500d44581c090310141081640944511061180382c1140d4062910a4480e25a480050041c002c0980e0262841c41f0381e031203540d82d160503084070004544220741841141e00400512006503482140003502007071061110702441e0600c003c00c1c8005041072103c030120311401e680004c88d8502d041d9880340000c0c00003401c0008258001c13046220b1100102c42240e8440c1c80d110000300144802031100014000108a0903901c01070320042d100595400207442c100c56071a40c1000204000c01d220350707150231080c0c0c900f141d02d103801040c0344401d0a0010304418515418081801921 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 448997113 1250 448995863 448995871
    0x20f03030c090d020603070903050d02030f160201121a040b0f03030909100e04060f111c0209010302070c031a0f1e04081b010614041103010515160303021c05041505 72
    0x1214000200c000103170366840c025485400e80e40c03610340d003d9043d410801d01c0e190501c00c60340305540c0100300030001c0303115590036100c68444085000d10f40a8007480101c03504001014196006810031528005010605000b143d40007000c2d00c040003200f01c2102003006c0c80c0c00302e101c030b550182c0080104003200c0c20b01c1c1401c80d500003500710b4004d01040ea100780c4c40051a204540540b14260b03618400c59402038070b80501070301c0e5a500784c007040c240702101d40a0850001045d271900c000c00c2e8005401c88403a4041d4042e14000340d000358004840d19940e0a00e0701e103d8001d040034000c1171650324005040302240051090103072000c0c41c20b60709454402d08244c8070b4802d01910580c0c0743c46051000a1207125040e83d4052040200d0001056940c0b40646803041c0c4d000340150380e441542080d040c04003e031106c5041c1c90445908884d0f4400c0351400000a100a2240503110100801c0c84c41c040c07814503405030001c0c40342c0c03a00e860300c01480c007442540c00011503000b560010710039030802c0c1946100390101e40015400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 448998363 1250 448997113 448997119
    0x81e0f0712081b10020a020c0904120f0306080307050601080709051308070f080d0c0f09080c13090c0e0708060d020105030f07121a0405090712120e0913050d020f03030c09 75
    0x30b103d60b04800316107028681c24400c0780203174002a00a0b85544d0510078003610201c151a880807504190752043c0b442c1d0940746d60201000042204004543e21980000c1d006101c00400e60755110000c0c2041d680760300e0709004480451051072000075840d4603600c2141d10940e0340f4042c48440300c150b5601d42c8066406040291240c070b007c0100e5102142c4514010454943c440e2000140400c801c0000b810ba5941c1100384801d004203220200038161000c207082c00e904d40c00f265010540c0e006109100b00034001004040c1058510460204000201c2003e503030117002542c60316950b59680d003041000340e07400070314003c0c0020400e10101d11403a21600e0519000703021401c040304001c40712403480f401c440d450b481000801e0030803640c40704107060030310406800a54103070285c2000707401d20101c40c0d02d00d140b0000042130b03680341441080b1103a11801d03440c1e41b40b1000070f281c540c0504003a01c0416103d407004d801a5414002c2c030407681255800040c190284000300005103056684100e413140c1150020030403250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 448999613 1250 448998363 448998397
    0x1203020a08090f0a0830010e090a151e0c0509090c0403030207141f031a0a030c030b09150f0412050705060601030b0a05091627030b0a06081e0f071208 66
    0x30300c07488100150f1945103111b00e482d803030961420b20504001e0034041d00340c40d200e410820b0800c01107503020700101c071100035521010440300f20150441c5020080781d41c480004900d080e0343e01d01c1c1e0781c0c0d0000084c200910200ea1820060f11101c003a01000d2055200c0140507a0002d1400c000c030000d01100905500e000130880340621070f05804000c0c162182c0407090001a0b592880c0024003c0070070400003040c04156000d50420381190358000d0440c000c0e000140c45e040360a00003a02d20300703041242d00070b403d000d0417159100d4201115040041c000c1590200c9414586000000d4442d120301d06440c010303500040200800c1c0c40b190019030040c03150601003a001058808042030940783c00f101c050052141e041d10707035400c0140c424020100c83d24ad0040020014400c401c0042d07118411000c082602d4100180c2070f05500c075050104006c003400c1d031100409000390b0041c3c08c41030340c202150080f41d40c1c505c416184c460800c2d0461688800c680d000351038140c6025521304000c2100c54010b0326401211207032180c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 449000863 1250 448999613 448999657
    0xe01030204030807050f060a02090303031b0c1504020a0e150907020304120804031704030201091802130b0702010311030613180204060b0d0e0c0f0910031203020a08090f0a08 76
    0x850680c0c810b8130140c0383c50f800724040d42e01c0000100062a40400000c2d070450500340c03094001b9880748001f516080701450040a40810941c84130120750400e40c100080b24049990215031041800040310185d214000e50480082d0f0000b4481e4503030300c00c07090580d03140b034426046c00410615071000303000d00f400c601c010300004c02e404841080b8a81940c3c002c100a6440d1850740c41c2c021840c9288841c6140840802e020810050b41c011f8281400e0362456101015511144010360009000d4450074104c400705c0444006149001d000040a04a000380e03414007009030705a4080c10070b0700c015036255401410004000e0390040315640142c00c1584130811150004101d0f030001000c4c0d481c40d8011501040001030031005100c218403440043c80c2110009e8001e04c000343c00003484000c82810700301c0c081c4c001c000004808074040c0c0d051790b016541c0039103242060031110070001d0007504000e04100204080320045410450001409140c9505100041c482210580e0f6107042c5504586070840c1400304029542c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 449002113 1250 449000863 449000873
    0x6120a05030c0c12030909060d08160b01090c0305070801061101090507062c1507050a020a031101170417070c09020d020d0f0216110f04050a0903022b0e0103020403 72
    0x2403810050820007030010000c3c4504020078415504000c3e10349034420014110305444420034181e1043c8121040a11010300d41880c2c6840e01c105082081204000050725007008940c03a100c1e416a801c40f9030800000c01000d0080d01201c00599400340407490840042140701e2050364a0706071101d20500100d115481170381c0e014036150141d000b000202e081103501d0b4810800e025000304161404240190301c20302004007040000b5101090721813006000aa040203002d4200f021644041d409001040a250703a401d0035074036029000e800710300091403160408622801f180c1e2050242d0b400c0015000c2c130b03241800c8055051f03401550201d814900f107041c00502d10352140f0140c10a0285102d0260380c4a4500604a040310b104011900c21a441809455040b07107800350100c910303560051040500050540029814540d1500d0391580079040c0020080030880e2600300b030080074482d408580800100c01481c00000007841c0f40c8001d106103541c15070403003130f01c41c4071119902c81d01810014035003034503070f110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 449003363 1250 449002113 449002117
    0x201090b240909250509060a0311010f090509040c090b0307081203060d0c0f06021e06041101020304080709021209120a032c0f0d030b13090c0518160509010806120a0503 74
    0x701081390803026400700200e090210342e0340c0d4070071011a0600a00c500b1541d0784207a00345000c2105041050410313050103072030300604c90390010b41030040c0104a5490107141c048845001401040e58403400d01e0004001e6080c006080c5040e107612401503d046d515080d0340f0035440d040100602d0b40040340d2800440402c4022811501070310040d4041e040c02820600082d02d04207100900100f900c3c0c00d83c04252000a0106201d41c00986c08a50074400b1224640102d15501035030704075103241d0041030f90005200c0c405900038480748420309506500d6940302d007402c0752a03490480c200300d51442c040043c002c074184a0b0f804510340600301c0000420000180700c4100240030f1940c0c048a0551114240f600b07110343c03c0200c0032100c2845c3c0340901c00d00403000b011131542d03603c40240603001d80d01d5036481410410200c004501401e03000e092a4000300a0018510641d5400d46405169520125000d49058810b80c00c0303447d600410303101c10032651643c0d810300c00015450704072120a805031030b84e560001072080c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 449004613 1250 449003363 449003413
    0x50301021c0f0f050421020c09040b1801020f090a080601080304120503190f110c100c03021c0507021309080405092a0309010606020708060c0f190201090b240909 71
    0x4800244169403108906d00a43c3c29061505561040a20003120b40d115800310768081c2d03102480c40303040e448804ca020303034462010120700c2ca00d5001040f80c0080c05080f40103040d6084046880c260703000e544090450f02c442d000e01424400d85c00800c0180f1107190880c0c0c500725078a100b44102c0389081c4c001c600c0a002140011200e500141043c1404080c10390b00011980d01c01d6100c2024000b2558000e0000d14031102d0607080d07500f07000c0340705042c0003407600902850041101c0b441d1380e4000001c070030700010060f1f170144908130b1140f4000d640503007209095205040707881e43d009040c40e1900d81801d04108942100910200d407800008000074002102240030750340402c0300c0d0403040d8607410b00d00c03001800d5420035040902103502c84c14040107000340001d4055003000100d8051655801d41c50020052446681515003880d08a8600c010025034154000c071903290040c400998280c03540458a241c6100140415a406820f841c00c0c000303c1c03400d20b5440c1d41080b0041d08a0350395181c407188240e10414041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 449005863 1250 449004613 449004623
    0xb15060325140c06061e010e09070c0609110907090602210c031c06080a02090c22080a03090501050307020a03031e0f090b070f0203041a0405090a0c020106050301021c0f0f0504 77
    0x70500c885420b101b114520480c03150003005000202c0c1e0000200000a9801c6440c411312410010882141c0503100c0e03180250780000c0c0c01c4c01625554248218140707081140240503400d02000030710310610403142c2c1c4041d13032400d9015001e4141c940c20080041090441c0350f4082110400802403540410030083c81c4000e040700d000308034111b200c00c80008840442d07000700c0d0103802890034000103a4400301e00e10f903c88070320f1321200e44454050b6594200b40440968002100041c42c07000320309030200080c000308040c829a81d03a21089c1e212001103603180420b40c0e11401681c8041c07070800000780681c115803140a10680c020010503a11400407040d180c8054000c044a41d9960818041c0803804220076840111070074101c4448603180c100079038034400e511400440c2c0b2075082c000300300c40c51020b04490080800400980a42c24104c01440c01018085041c20166103420000245800c1c180292030080b00f12444100345204802d00001c050288511407056480d07882c422108010014401d05000c0c0c0c1c060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 449007113 1250 449005863 449005873
    0x604021207120608120703030e0c03030a110f16090c1218050c03030403020a171212070f0f0801090e01060902070b04020112050103021302160606030b15060325140c 72
    0xb05030300e08102c8096400c510103c1d040f03503500c0345450308140c080f0b030382c800d6240c900040c0c590300c040015824805401c0c0025410700001a02da10000e034000009900c49199400341c039030821424181030758030340a100c0d0aa444581c004000c0103020450f9208801441d01410180a411104000102181c03810701c44099003842002d1105c060000030000c50301a030301c1c140c004518141c2160001660035000384143c01c8480030000c1c60608140060140c503941503039200d00c1031b0f1a010004401160000103c52800c00203d29007412406544500308110f1081c001e82c5500c1c8003642032100541c0504200d1400e40308640d250600000c0c86130303441c0b00034424240030b007484404030b050910004108901c0254008211400c0030014409666a5212a802c90031198401695483d40e4420000342d41c2c1200300c060400c0d880c1c20307000405d1240c110040382c801d4840703004000c11080307185e04000302e5000940740b1818051008502c80c400340601010385400c00031a0030b00e40c0503c940303a0703000d24032a071102000e0000d603081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 449008363 1250 449007113 449007137
    0x110609011106070f23031b07050d0e09250806010201140103051005010501050307090b0a0306050910090b06070c03020d0c0305071d01120807030309031b050f0606090103030206010605030604021207 86
    0x80006410580103203034841d1740000f0485600c81c0e03d1800701070840311080340c00741600742c3c95181c0e02d000c03101c03032a07400300c1910121220400c000d4a03c4050005042c09071800340c000034074504503000e506120381c0101210f03035025522154101c0301200000c0c4218159980e070b68034050a24084840d1900840c40b803001091565003010640301540e6042c3c0c840e5060142c1070080c4000c075600b15a05d0000c0c2c8482c0e00285464505041e8101e0140201d0b5015a802020081c24040d4451440f2032000c03e444402c0300500540a803041440703054454040b000d014100c0d0001c00344014542050020b40c0b03a4065022150490344a032286c5003005401c0c4e1040c00a00c00d6a47c1400b203401100500c07600526042d034075503480340d000740c03600141881407401c000c04040c3d41d19003007020140540380340301610848100030b80c0c808100e85007045c0d480d42c8600c510f0440e8410300c000100300f03140402350103040e41e174076902601d02a46015001c1d140783e040030f09000d5201c0d4092110000301209651510320944456a8040c410300c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 449009613 1250 449008363 449008367
    0x1308040803040314101803050c0309090109020c1606050906070c08030a0f0305060306071403060d08220b1806030403270e060d050d121e0212090109110609011106070f 73
    0xa0405c400d480010704144488040000a444004195815080c5207075a0324002c1c00082c00c51046500155000b000000089180074081d80503004091031071084908a58082041506000340780c0b00703000000e402008504218140300b80600580da00c0b072100c2e00300c003544410045095801c4a031078840000c002c1d01091181300c0d0706005042d00460b06801411071420020b0700140710144410052140600000c0490070589484211415058024540070740f6a40c0303c144014071412850029000e600d154000451000c00d16422500c1126843c01c00b6032036084000c06001554000070070690a0200d0001016625080b54110050b04015201800c03031550401c402c0c3c221100b40501030341c2c0652154602c040c00501d0014520101400d0750510054003c403a01d0800094001030324651000310100c3e010500450a940240c107518030402e5503554240c1c0c58030003c0342210042c0b1000b424010382039416003541e041001c01004019018500192b616260810f40c6281c10303420b42e508400126a51010b240443e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 449010863 1250 449009613 449009623
    0x60b04060305062e1d0a080708010e0c0d02010804020a090e06190c0207051c140f060c0c12070f060c0c05060903090a0312020a20030c01171308040803040314 69
    0x41c80d0380c045200c01d12070103d0307030f0f0700f42c413011408410501c144400c054095400200b45403007880c1009018138039198440d00d07803c1e00d407403440c4507400c250740c00d01c8003015440001080035002010302074004803504505800440c0e60b000d014206a82011582d0301c041404ca42074007a00310b03240641c40007003040b810f08402c040c610103c504c540103082458040d600601581c04203403041100d504842c02c54440e0f189070103081c084162140000c0881e0714541780102c030044045013240390791502e030382641c85a80e244100500b4900c81d541a0308420b4100b03002c0d040b031180765500581192802800c2c403a4810b40d961b9522000c882c0c0c4000c003200455a101c001408003c001c215003940202080055400c1c9000c14001c54401511b80c00010805048081c1e0f181c1c40034820030140601542240e070a0780c000848682c00f2a40c0c40c0b00c03400303850081c0074018001c81c455004d1203003c020f41f40c8000c440d1a03a0396a520140c2c92254403d9003c445104003084000b400d580100017402c081d50182e1000d0488441c203e2401e4500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 449012113 1250 449010863 449010889
    0x50c04171b0609091603110d0f11190f05040315090606210618050102281403070e0f13140619060f1214040b150609010e0103060b0406030506 62
    0xb410200440c21450300c0302102280c00a03e6100702925214080100750701034201d216040c21001c00100340040f02403c640c00c00b0076441c601e4642008031440c0400d45000c82c0c40f40c200090010302c201d030030084800c0d00c101c1e014007905c0c0461400d141003d84076556107010403a03800a075007400b41c49510080601540b4440c0900800c5c03600300c00c00041c40b483c8801d0040781a60580640810b41d94075020100c8810002404621030f0301c80001c41d911220507080107002c514010703501041000880f0520089401a1820403000040d80b0203070f41590b480030350495500960748006030304421074481d41820f40e1506002c1d007010440032000030480f0078a01c40120f90740304000300018030981c0310300d0300c0440d0750b0300300c1044505441280c604480c0362211280f05136062040305041d496000c6c940350080510702c54028950340610f00c10320401525846680382494a90284000c40303620400802c0b030706000758080e0440070034551060501003499035580780c1e5041da5130070580c00f00b80030a0322030007041040d281c034582410b40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 449013363 1250 449012113 449012119
    0x100b19080a050613020a030f0e0307051009080304061e050f07020d09050f0f0d08030f060f0f0108010e0a0603140d020f0703120302031504180b07020a020102030d050c04171b 76
    0x142d850f01c0000a0500d02c05011002405640010428001482500900f0790014000d400b4000b0a2101180941d01ea00ca10000d4515001d40c0d4503116602142d4001c1c01c1b00c6580200c2c15600719112611080010140c20b070380105c48180c009045e0902c0e10141c001c00d0302c58548910340c550b503071900c0d640181c1044000c420030020010004c400340200e5941e003062804214041c1e54034800d00381c0c10800f01d4003c0e10a003030085c0640c0380200c1005010028007000e00e10500081d01e00b911141c1804062090a000105020303001c00c0c080e60050148209980c404c6030300c040400c0020030b000c0c0e500e4859440c140e100b52000f59441d04540c220100c4a50100980c02c0c01b0900d100090000340e10b55141d8110a8683d840c44074105074001010801843ca0400056104400100100000800030011710002c454080c02110501082c2e00000c1d850350000c91800340701c85e010b802640ca480b15901c00600202402030070241c0a103014003000c51140311480300040104145802030032500e8103000440704a06c14224002e00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 449014613 1250 449013363 449013371
    0x6070b04030825050f032815170a0609150f09050c1005040e04050a06020f0a03060e19020c10110c10020405011d0a09050705130506040617100b19080a 66
    0x10030b19800b504072009007240441064480e16081c1d0702203460400e04007a0f00480491013108139032204148e0149070086212604001195601c0b25000034400c0151780f0207240b5000b20301c0030130100310030343c000c4403078544a200b19100c1810080b04a004851585a04550b040e0303440c58044100002080510450340b000c599040c0058000c02c80144141301c0d82c040c00c1c07500082007006c1020800204507180e850780d0f010134155150001450020000e401c000b01d6400060309044000406c45503d0114a0086803c62240c1c0b0401007010100400b9502c182500c1307101d44689003400c2c032034210354130451440000c00e0307800340c4c0c3c2c1e50303200d0380801c0c84d21041e009102c601a204101c1045140e800400c0c08000010303407404001c1c0d030600540060004d1100350b00601040d0f0030f0108004500c1d42c040001c1500d40c2c981c040541c881901c8400b0700a2031b00a42c0903045c0400c42001a9260865044a03e56409918002e920740b659072075030811140c0f508051710401020364814910f81d401030304041e540d0707800341243d20200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 449015863 1250 449014613 449014681
    0x4050411091f14101103090a09020a030518070b0f1b0105010611010e0a11130f0f11030c0f160602070818040507020a0615080610030501050601050313080906070b040308 74
    0x302024258113401c418896610303096100083c007402a46c8881400030080c0305030960b1001c07000041e6101540d8240000c1c50800022007400d40c5000c1c401080000b0002800c01034207011018034180e020003658011806c040c4050040e07107022040d03000e220b540e81e200200303031540342c15805442511b1041c1070740100d9043c07000e04416548000384110b40f241e0410380d24a1107000c950042415100b001802421305400d040c0c440001c01100d81181e8000c09508100304001c15940e0060341d000d0100381d43c061500c44080010307800d14070a4001405070100352040040c0b44010554030f4000301e078425042103c51110100d2503034201d02c80740841c8880c0c0c002c240d80a0005180c140b100940356041400003c1c0520b07518031207480c00c40203803d82e0324040d000407030440e5500c1c20701118101690b1030b9448111669801c01001904551040054034020b001810520109041c142d071a1150764201c02c035541c5c0c0180c4184074041c00b2500c44683d1502450007a150400c050800c01c002e002c020b01c4140e652130003400380ca1212 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 449017113 1250 449015863 449015869
    0x50a0801023006010e0d061d1903050f0a022e05060d081b100903050c07060216030807320c0306060f090406061e14030703020f04050411091f14 63
    0x883e03120303030240303842d507800e00440000a28450510401618103490007103d407030540b507014134504100303c2d041d08440781d61419009011003400e1444e0b008002900502175054490b003010042d06201d2140e006499455000032030b00c0070003000601c0340f954a010b0300d0440050041092056603088034003612022030402650701d80e9240e0744514105140d200c2ea499800e028075078803d00000030000c2d01c00c0c0c014000c0054a04004000350400140c02030310b40220304c40002d40c9400009c4d1000c03605200c040c0009030a245480c1c82d10389800c07424040c2d9841c001745800c030b00c41c9014800704180f8a417a00c0440c080b0b40405600303c615102141c41d5a90007075200c50240001a55103003a00c04990b4021200c6030516901c5280142c09410141e024044001c0c0c0d002840000c2c800d00a0181c003504c200704100740d4880d01340320800d6a110300c18400603400c444600700880040c1481d42000703070b0041c0201441031003254030f007001c682b02c01c0c4e00b160482c207100801c12800da01140e80c03072814001042e5800190012210f14400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 449018363 1250 449017113 449017207
    0x16050d140a0801050d11061606050a0b0109030f060f050106080a2306060f070203010e0f0609071a0307050913020d0608012306031504030309032006010b0d0204050a080102 75
    0x1540d1050117400c40403020002417100d1314902403405024661071750b15071005802e00c8500d200049403128141070009803070707482a100b1140746000c140d46216255180d6201c13a14040c2c01400306444803a00c40022980b0b8421034000c0c14028a49551517541d54540000d03100100c0d102942850a09003011002ca0744440c1c201d04a1a0000d50440c0c1c610355450001d4201803070340c820030304029015404c14102c600240000724411021a01c040305840f10745e42d82c0392038140c42d103d4038003420501c102e01a0744081e907588810b010315404061030804600e401401c4001642c6800c0445244c01d46030380000300d10f981d1902034002e040c0140f90150080c000130341100c1210080340240564a00d1036607920740002d629503000c004480c86210b868141151034102030500074003400510134142d021034200744030303201c00c1c107401c0006e10610358240016145c0c07a403d01060a40c254841c020018180c0d4090002040710380da5110703008020000d0303000050792501d5004d0040c81690841000c084102d44100b40300f0410003072208 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 449019613 1250 449018363 449018369
    0x2071106030a090b0f040605090703050319031d06010510020708060411030a0c0608010305060606090f0906010e0315041a010b070807020402040b030a33091116050d140a0801 76
    0x901561a940d03030240b0384009003d03014001d841080c0b01028000191100c8221a0045000700c0c414450759491940b040d5484090b44802855540200f010100b94440c00640f0188203c542c5030216100c1030388290303100304940b0300480c102142c2200d80100b00c01c0c900380d01800c0e01c101d074600141c408186004101c0b52035003001003000c1d10403642400440c3e0166414040c00a19551092184140e2030700c50b880145411001d000844039442004085a22071a00074141c1d5045000109614080c5004c4403e2051041303000c0e01c1d140c140002d49034000c04540d0140300e884d040b520484070403900ea28003400d107000144206200340c0101590700d0700500807100c050045600c4c0307a4004802d0350303075013466201260007403090f54081204200040305200030b052040d04014180c04500ca01494040302210010b8195007202c04024200c84021a04000c05001c0d500310411a1074012503585c103084404e2961841041da4241c110344507048894036012803900681541c0e0007081d0111041d0a0500680f405019064180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 449020863 1250 449019613 449019619
    0x70f170c0d0e011d0c100e03010f0623010c08180406031e02092d04050708030403060207020f010f081906050303130e01151d030c040603081e0c0709020a05070b090a02010909020711 79
    0x1000f1103020b48c409401000302020706040030030000d40d5801740b543e0884140002c1c084104080d14580302079620600c50b080d0403580003600c05140051a554181102d00c402c00c400341c11644858002001c04d4030740001903810881459140c000900501c104100420001d00000705030304400b56000e42c4084080c0081910052040c1c1c901c5262600d050040ca48200c5038001003161100240200030031003e5005000c0317882c403d407886003080c2d0200005440760075528680c1da00159003000050100a0409403100f010f40058100040da03c0c3c41e9000f1030704560192100d0740702d10307140900400240380c1c1d4011442c01824550300d48100381d9a0300e0030041c0102d1404400d02d8208000b001b440205584c21f200740004544018402c1140651700d11340102030b908040c0c0841c1d100303c440c040940c01d0f804003104403005007480d040502029401c001d01c1070001c0d0003c041c40000c00405000c1680020141010f0381c1c06004660014050008984001040205590052564140140010000192400c0d03800d01d00319022 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 449022113 1250 449020863 449020877
    0xc0307080c03070b01241b02060d0b0a03060e07080f0c01030c090b1b010608031c0203070e090f01050f060708031513060e01080105070f170c0d0e011d0c10 68
    0x5064910710f0045030340140c107081031800009900311803002001402103000d180c6041c0e071840440150742c0380b101003100120b01c50301c0300344400051402000a0000d8400ca250024020f90310101203003c07004240c0080301c0307141c0d41c0c08810341d805400700040001000c001000b003082c0c010fa1040d4070380341c81012a40383e045c141c980d00c29801c468060010f41028061800000e52212961640070346034020024044045520300200854034080101c01c8500038001e00506518003000707104940700a5000510f400100a039600d040388080d030701c080f40140070b040c1d40d0b804003920754100810443d200d45200b4800d8412001000380030b00041c0040c0580b0360000021007051003000d03c54001c100076403003501c85010141d15011020590009619596068800c110020031280c3c2d240e0714151030088080f00040d002c42da40f451801c247c01c0032a4040e0b0707844150314202d98146042000c1d00390990f0740640e44920541d442d10302c10203a1000c00700304001e0090000c401012218500030200b440f95106030a894200300705 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 449023363 1250 449022113 449022127
    0x40305160602070605070305101a0f07060219020f010e01061d060a05060c070e06030a0f080a0e0301140115090302131109061206010f030e0d0807020a1202010609060b0c030708 77
    0x10342e0741960455030304410144010b00c1e0020006000308001c998840303901040f03600100e035400e2504081e031030007660b02860b5032604140c0117480c040d541021404a50854081001c0106803504440f002028078264001f01001c400303500c4401d0a480240444150b030743c1c54000d003040a008600d051143c1c80eaa10000d95009445131004540004001e4001c1504a0b0002945031484100000c5400c121800d40c400142e480e10380604040d01c07400a400064183c980e01001080800c61201c0140640a5103007450101c0194850209003900d0804103902002140d0200410040e80d50615040b01c2094070b14229204a041d5800900d500e003105880c2c4080a50300e080000320600e0100c02c40f00075010003840742da03c07011041404d1741c244804407115030018001b003490940050003070040c1ca170400d00650180c0120a0704840488210600070081d40844c4590300c0c040d0045001007408581200c13055002040c003e00b440b4007a8241d03201355010021002c82040a0940712501200b9100c07140e43c0420708983c0e40300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 449024613 1250 449023363 449023373
    0x807020f0d1412190b04140c0310030f050d0905010302090a06110109080408010204030302071205030405010806010507021e041b05030a0f090c0806010918020306070c03120204060507050c040504030516 88
    0x8030700c081e4540c11007200520038980f9136112500010800000103004d001c280c43c05010a0b500078900d540c0c260007061022883c440c03000301c09154890f06c40e06070002029583e40b44c030686402e14400170786140e0006040f14152590100300039019010a0809509d004104004215004c03814840c0c181080500c4061003003642003900613641d510f80010070262038648a01c6c80d02e000b90700a12044015100d003c000184140c145e903e00c0030481e03000409541001d180200654990500500150401400708011001a03a4800000414400320b004ca607401c0c01e4032409100032219800204800c012400f41910b05583d40042226805410b105021410040d420b070720030702a0208400040c01c4d210008808945154001611030403924550002e101d1030f0844032003140140034040d00070303425800580008a005009030070031540e0b42e11902d007442c10120380f0502c007412600903422000000320000f6220081c007004101c01101c0c00c2d01105c08010509059401a2103441104910290103100c0d001280c00c0c44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 449025863 1250 449024613 449024617
    0x7170a021e030a080913050f150103090b0a0f05070813170c01020f071704030f0204020a140a17250804030507050111040512010501030209010b090301020403020a03120807020f0d14 79
    0x1102030210f8100042900d84805503802c00003140d805030041d0920144c203040c050244c01d000300c010554410460f00d503d54071580c5c298190700d00d6814152186440710006200f16205841071080038400207000040225410030740d6000b80000c0104540003081c0100320008280000c81d0704d43c010701144100980d48100c00b45030041c0840b810865101244180203480314100a10903a441120440651003128440354034034000e5000c080c1218040d0136070400107040607402400c40c840241030407181110b0207580030322203a01030070301c02000442c14488140103400c12018560803200c441c02440070301440d100840035006014040204200d503020215042c180070300119214150000024440402d40c6030300104140d002e880b4290040d41c0002c0d03101d0309260103110b264143eaa0080035485964604245030b100c64004481d002d070300d95820000080147c0e50301c56214011413041407020741040d645840508200c10003859074066400502c0c2c40c640c501301c0480d803095500041d040205103484501480f404038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 449027113 1250 449025863 449025919
    0x92401050a0e060318190f11010c0606030507090b010201050c0313030507140607090602191b0e0a0603060b060c07121703070201052a0d36020307170a02 67
    0x86280082408448400741d11862000c2005000f2261b0548007154150301d01911140041c00003401e00c0000c00018900d0360581c1c019100500d080210740312541c0303030030044415991003101c003540424003c1281031a54000c054a84501f40020042881c00000600b2144401040440380500641a91040600400649142c03a410080d07103418602c1c400f0382181e540b8016180000442c3d6034a2000481500c0000c2c840810150104111030790011540e40703c030400c042035161303035905000640c041605484420605d104120002000c200d40d407075410408202c400d80041c00d40a21405c001310b9401050014422003151024242c000e00002c50b0704200d0300280784548450200b201c00010f01951650541006001d0200e05004492004001302d0610005805c6401401505800c3c072510050505642c4a00301081c40080087c40014070110034480f6000c10001c000201303d0156400402d50508100d003402030900a4031030b2200903884424150f5502800100921421890000048420b41c2485800f00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 449028363 1250 449027113 449027119
    0x303092209080c0c032803300b040b0415170c042307030c021203090a0b010f0609050405010b031503071e08060a180f030c0b070905092401050a0e 64
    0x884010383c00c11516210342c9030f1001c0c0b0074402c01c8501d100c108175001c5e00d0820840c00025800d4a40143d6900b954801c80c840d01c1d0100360100405038110014802070555040b0041d00c070000742c9201c06004002c12550390280d6280a1ba00c6c0500c0420082040c1c0320100c01c1e00c50100c80c10b09022820321141d49440c41100700d940d0003a041c405c0d200d00b50003000c51030b500c881d81c50008490349542c440004900f00c070400747c0004010b9100c6100c949042280100450b0480c05100984241a42e0342c4c40341c1e411400c0c280d00c240c40d030040c20b2100704117280c1c4c0009803034040c10040342c0c00d00c6a035250040b400418000540480d04408110030041243d943c03c000c0c1000030041c4142c0880900361407a03400d4640102c0f441440000d01483d000a0091085131246a503800e00c00000d20400c400c82e9101d0000f50038a030401202172204490b100d0000c41e00d000d000900c65071503541c0b100ca14509000501000c2107015103241c008000303050103034000380c040c40e0901c0f10070302007868042d46a02c800f503404c407045449103c0b4075070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 449029613 1250 449028363 449028367
    0x3140906070809120105040b0a0c0210050c0a120612111c05010b1201090b071407060609061a0a020c060c0c041a03010e0a03020c13020d05150a05030309220908 70
    0x820049202c0c0541681c5200300c40d41d13050822190021800e0320f00c201c400074007a58040300010640310480d484a40d203000188101e42004140c403805004581054031580070b00c50000c035420304c00765880314030b03040c8034403561006100c0d01380703422031902176130105000040c2135600301d070100e00c825129641c0e520a40c034002c4041d2007548819080007402401002e1486000e543c0051007189a00700500038484165400040c81d680f41d030314014221b0f0010a041203010b50741c4420440c44c80464054015100540445d05000500c5481c1214030050059202140386241006104440071243c001c5600c640d1010103644084d0b5503205072140c1800c007120029a140e00c80d20f0320f08544040020258000101a8164000c0040d01c1d280b0458503a5030032040801801a0300c0712a00e00b0303840c00c00c840442c1160741005400750130000342c3e040713050549100303d8440901c1245d00c01c030046585403203031481008101c1940654940603134000490344841c0205094100001c04400c1c003581c85015500c96400030380c000f40003607 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 449030863 1250 449029613 449029627
    0x17030a021c0f0f02070c0e06030c060c06100f0e1308130b030114090105130213031e0b0f010b0d15120b25200c03030408071706060d03140906 62
    0x40042000e00b4003212842e1421041c005201072920803604400d80000003005854600031010a0481d80142896018042e140c800a440d4a03140c5c05020710070031802c007808051a080d1240f283e0030100368400300710314080300020812107040d0804203812449440d008203c030900341c02c1501140c400c440c030421250a02200001d100e4501e0009541030794410240903003606021410051035140c28051198400c244aa801c820034156500424035030903002c070b9030302c48141d0781e4540180d0712240302c60049401014181c000e0401035140d411a500108505c4441e20950411191800e58014412588005980d0b600c81004d881c1045003480020b0249110304590380000d4607220450034010742d91210084d200c50301c0c0c81e0104503001488256003c9580d81c040031038121500c0c10a005146001c0440380d03002c1c403800395140e1348003400200003500700314004040462904096008180c280030880f2140e800000c03c0c401c03955101c5804550880d0145410145809914201d07081403041c1100950b100800091003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 449032113 1250 449030863 449030917
    0xc020316060f0206060d020906220c2d080c1b1617070b030a0f14090609160509041b0e04031d0d0f021201090611070b01060c17030a02 59
    0x180030001903a43c25112aa02c904c0180301200307400c800700130350141ca40000264641000c00c0034440010040d081e078020300022402c09412114104610700001d0481e41c48111107400545c0180d40c2d6038100c0b03007648105400500020800d510290468084c0c0781b000440c0300e82c4c1140800c01290410620054641c071440040440c04820b006d0320464903003140032880034429200116682d0100c1c2d42c15850f0915643d941309405006061800c240220641d5604d042c0c0b01d00201350110034460011100100034a0605445440c0b901d00141c0c01c40164034400e1405200340e407a0030740c0d55a041a48842c0320320715164114180500891075801521380c1000309800c200a02d5070121140051521500c3d2682070b0b8035160042c865020407000c0d001d450008204c5040c0c006041540d61007804032594000080e427500b8940c3c0b41825180d40701001c03110104049808818007021001c20b40c0106020b007003200c9154101d6942c1c00c80785002c09605141d004011000856001a903012500c07000403950980b00d20200380215 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 449033363 1250 449032113 449032127
    0x30906111c1403390405220212061309020307030b04020109120c050103141314190b0a0b102c0904030c1205041415160b010608060607030f0c02031606 66
    0x1303143c426800c003900c0501c0d4a404076000120044450f00140c949418a41800381d201d003011042c04113044403143d00518008507201421000307101140d40c3d421410300104008490340109131255046150144010040c1c0e40000c09508881e03010000d800c440c0d40794001a1a01042540711a59103402d910341802005103883c0e1081c180c8000340c0f010040318444400c2015103140c1114017401d60304c800351503500450580011080d0040d0400300310740c5955103052101c401200c485804030f55230102d84060081d034550302c0c000c2c0d402948081c3c801c001c612a44400040c440c034107000c07076400c0c15070421914803259898015103560058000e4040c10060800d440d004040306081d02041d43c40030718103460300016038841e00c115801c9405034280d161202c8403110407c4500f00f6061841d860032082040382035920390114072080314140c001e0489081543c5400001750260400074005841058100010f0780000c0d046465800900d2140c0781444c4540e00c0382c40400e1400c1c4091904079010040d4900000c1c02d6544018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 449034613 1250 449033363 449033401
    0x30403090819030903080705011119030e030c0c0603090f1507120501030302060c1309110903161d040f0501110409062103050a14040e04030906111c1403 67
    0x1040ba501c41110318042c10500004681c0200000d60b00d071010800300f03007110081c0010314060400040c04100c60b02a00400340e00030b0380c401c00e2513071803140102c8001350180f040c1c0740c1621201001d94a002c070000c0c0d0068a480c940c075803841c401c40011003ca644030100700107030800c400160341210f44001ca0445000c826003001c5403036800043d0b503d41802d034516010b010f454101c0364590010303e2180c40d21140d500e05500440d0304000c1140c800e110015030032645010310f9141d0000c1411940e41c81e104401454200700c0010034080801c680744200b000b0240d00300c0a070807040d60448214000369150740c9846c1010318400e603809040c56081c40c424040b5521000002e00032102c07002001c0048070340d0b030746640424440018244180954859094012038020802458540042c1c905200c007018440070404203038100d90049a100e0040d2000c0104041d00a16124060318150811190b07000c07070301d00080e568540441101c80c0b0940344031300441071203000365444c807145200922129107a02e00b0104925908030008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 449035863 1250 449034613 449034629
    0x210020406030f230406020a020a020312070204140f0403030c090302040c0e0f0102010608030d0207020f1302030a0510080a1b0b0706020309060601030b060724090b07020c031b0d0c03020603040309 86
    0x4640c104281d8006050820454446400c81c0313156596840d258002c1d000340405c1420f50080300003120040e5000c1c0302e030b00d100030040c01810703840369114018031040b5641c0700d01c04a540261103092000703c4100071481d5030f002d07a045c60040343c080000ca0703040b0354100035036000a4109040c08101d03021540c01903001c421072142510b106515a02e404012030903240c9a200d0803009400400010301c030500150010694a40091705410040030018041900413007201c8428102903808401d210045526000340e5400c039028140861100e41801c00b085d8607602841e00040c120f02055102c1003044081108003001070001c0c401d20340d165491703410003101a5000310352129250003043c0007e15507600920a9600004000d03081c1d0b828800306940391144400010703203070148070505070018800c1100d03e005041e46680f0800d606001c5041248021b07203002d240501d4103200b074104540320340345140c1c10742c160300031a84200d4210040d64070505080c442461030b07400203074203e40000300f0002456048038561085a42d02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 449037113 1250 449035863 449035871
    0x20a090203012303030f0406140c25082b090504110405010806030a08031f05030d0302070303050f0c0d020d0912020d08070503040804090b1815150f190210020406030f 73
    0x3d80109a202c0c030441c48001d03114070090005002461141011859a10013610560310b00030080118034a0043d0840d900310072251900d01c080d07000c201d02030795180203100240c02807508180039a60401074012402100c406220140508000d6601c20b205042c01084050010014480e8461004079164410b004d80c03030205100304c01103491401c0c00a02e01e92803641044a04d4156148ca007980d04101c4d113040d03040100000380000c0441d865800b030003e4858000c054800507520a428500903040d45c41c02000380c16a06800700400000440c944120780040c00c507844016551954031492000600c030205000c0d11112840b05400074484c1c000521505081158560400c40da8a51008441920003180c0042280300d050100700105c90b850b400010039007200402e0401400e1043c45000380455088480701000503503000141207605003010142a100031100c8214948061807846010b240716100c0440761401514011a0302144284803841000000b0402990340d107036a184001c01402010a074600000c1c030f4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 449038363 1250 449037113 449037179
    0x16030207170306031b0f010e220f0b1e101112040e0c0f0712030605300307050a1709060712090506040501170711010207050604060b0306041e020a09020301 68
    0x30001d030980004014030381c036040c1c0041b0700110b450504075907650350004000090a81c0030082e048118020b084034410004500b1604c1c0b0104080d510700c2102d2034011001c01c40b282170303290840c0741501c80c44034054401c0c2070f0818940008481804a117034400c45140100b03408005402000030042080755070791040c0800a44441c0400d0740d017072090032040c2a1800041101c400011014482c02042c000b041c11700083d640d5441c40072414440100d80401e280c0e1107420309500914520600c1e860801c80900025420428142c0c4c48543d40c0b580e100c409489040111740034840b07000c0f004121aa07a00001e008540c44440500d4801c020203c201141c1c00882c1c201c40c408076940c2001001c0d141200c405a480b4026065030100684a01401030304003000c0104480701420054000d000034a07140f48144000d01003171805042000448408081d001d10076001001070001181c403545944200c4120140e644102410707910005880096941c000f414850000c0300000e00499159019451000421400c65151003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 449039613 1250 449038363 449038393
    0xf06010e0303310603020d0c020606010e0909030912070314060714032e180e0c1509270603010912030e01020405060309161505031603020717030603 65
    0x303902440140c055005110080110841c4848401c03501804084002d40121620841407691169005040401c0d00041c402000e5002d5100d1020b09400320700c0900b4250078010002840c9140c16564684070351500c0c000300307901c2c010603c2206c010030401085c0b49900510150580e13185c8405200958000010343c0341641c0c4584003049151145c209079950090045107a8181d03030141d01301a2a440d101074100d000019070100800d01d81081130304400e103000c0c025140103841c030740121081440000c245d0030700381c0d1066080c20000d4403810490b0f003280c002c4045000c0f04a002003500075078508c1c641c4443e40390604801c000341c840b950486005a201803c100390780e490285400da81841000070080c0801140d2408032030300c06d0380000385503064035001520300b40e1350f90b000541c1d680083c0e55205a0350040024011050125460000240122009600da82182e500007500a000084c03000c40e11310000f18104010500c243c0c12039440d00d0f400ba2a040c600107071181c0001490f00b003201c405000740f00b1b00391403002d006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 449040863 1250 449039613 449039627
    0xf021008040b060409060e070f1802040b0a30020a0801140d061d060a060609050d080306010822030c05010c1b12021c02011b080402090708100b0f030f0601 68
    0x9800005540b110340b2000180001420450f00586642c0c1d511045a14281000c0c81014002c3c150302141d21452402c08056140807450000004007061042100308241e0315424140c0d54502918113007010404d0102d036200807960001c140c4611100c010b00e07643c102d42241503000c1d0020351520795581090b0303038942000440303154104024a502c014442d5100d0300140450f0031078021422105c00002d0407980b0588041e1600106a03a0000005c0d2a100e061010341e40c0036581c00014102168410b10005407034513036022701d1101074152810031046900040d861103000c0b0101030604448580c40d100d0307500e141001085504480006c40e503d50800a00a031000c0c0b0542d1705821901a50800804641403680d0f400c00c0341e0080c464490960084c03028000e400300001d6014486584142c001046d540100e45407001d8031030b080c1070f155050240341e00c20b00025031106d4240e154842001d040c900029101e10441c0c9901494030740c0001031510002030740a14208000c40070714000e00c95214002d00750b84a00b80155648 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 449042113 1250 449040863 449040871
    0x1807050d150506040f140f10050a031101031806020c0106090e0d12090605010611060a05071706010903140a02040f02040503031e0903060705190f141e070f021008 71
    0x111445890101414585a2006401c43d000400c00522070300704010707101c159000070455010f940c485108014054138072071304140e40541c0ca4114440558109000900d8400c44c50001503c480c1707006443e581540d0080c0d01c94400c20b4004041103c0d0b02c566442d00320701a5200400d44c566035420014005070404041c002c041e000da407214003030190b19800354001c0340c1503107440025038030664a910b00000450390900c5402e000e0401030303130b40071014030f1100c1000c0e24284002c0c000302c50b240d2905c4200301ca0503510840382c84003020b800c2d000c07000b41d4480000403101030172103402c0500501800007070301450480006941400a109a5007400150341420107401240070303d100d080d030581c01c100862092050321010f50080e4103043c001c000d04080000d4007003440d0100031240503011660001c2e0030300521054501402004203140340000c5201d03607068000b08401c0c0c0c3c40c1600c1c0041080461480030300b14003020343c0400c55455503070307940d150111410800c4108800040a07409a03107000d070501d00c06031244003643e04c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 449043363 1250 449042113 449042123
    0xe07031407021009020a05190602071a041203050c060c0903010c02071203030c14040e0103031b171c0f0207030f0207030c0b2104050607020c0a0509040803041106031807050d 76
    0xf000c9400000c00702070200103200301e03480380507424085284d0f92803110400088019100c51030009040c074034003a1622105400045590000441000305010310340c1c225001c1e11114040341c1c0040d0040d1905860f81d0103480050135240c007074038080012130304104029105014040b80240040d1015490a90301c440e141e018a00c0402c050002d0b190209010f40c0040ba0703600043d141990400296010724516034003d034100d440089001c1c00104113240d406035541503000040c20a00c2c030140d400365142240c0e500740c0c1d110002403407804600441007840d0580c0700700884020020034003000e00c0043d9550002c0d404031104034003150a6040000320580300040303e000b92913010b030103003441070b040042e800620341001549424014a645c1d4041b4285c1142080310302503445000100720606003da0041d052202c080b4560b03006034100e1004002d40e03035480080c6030300aa044152079549881b83e0900d50407a100c01c0c810190810000428403040034007114454010712030f02e07015211503030780b00d4040015403090a43c0240c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 449044613 1250 449043363 449043373
    0x1503160f17180a02150304060506060f03040609021207090506150304050619021b16141305040f06140703050702061015030902132906031303020f06010e0703140702 72
    0x40c0401c09182d140c040740c0715160482c0c400c0d0b043c50b800508103843c0140c03602c0860102000740300c1082181e000340c94004800300e4820b4148110b90550171030a0100400107048507460b000c3d020155110741c03201c5030010140b03030180d410941e12000343d0006004103459181c068001603803c1d8250842d040152401707143e01030050070290f04c0f91190241d0800140c10302e5004035908001200544000101d01408811148060b0a0104444507540e058075060781c000c1040342e01040b407080c080d9503024003200004911a200290b19242c504000d062804040801800f8134a0166048040e040815510f072195000d81d0b41402559036a100490b1280f10030348102105d100040c90900c40030101c1c400242c2114000d10300090380034210340000d202400741d800c50740800d81d620300c9a8070703441c10741802000f945c00a800060380400b0f10440881c1181c40020a401d0261303c407500d401d81091710030f00042e05559203c41c11a019945c6526901c20004801d64000007c40d213005034040d03c100e207600354070f4455541900640 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 449045863 1250 449044613 449044621
    0x501080a0b0c0304081b16030b010e0907030506271005090d030b0d1211010609050a180203030d021c0c02010f050f06030705010518060d0c03180b0c091503160f17 71
    0x3800c0520f11b11840190046a8a48000070300404410300154025901c04040c0d52400b1442e079240c0d8006403600300d031078020720710600210b1000280300303420000c914000030f031696262109503040140f1244125980c05900352a125040341c0b034000034003a2080000b603d0600d80c40d2079080e0104e810a11180b60085000c0000c0740101d030008184102e2246141401084104842c0b045800c40311950401101c0715030301c90511404160503c25100c0450b0100b051166455032500003954034080e1069000381181c001860176174207070292501ea1000303400340304103024881c2c644501a01a0100000c210115440d0800180c02c40001c1609140502e2000d00a00f0041d82040300468407544480e01d4201c00803041e100d1410161142002044a2000982c0003c3d034655980c9008058400310080808001c00002d90800891810402c003604800900032040d030364040c902c0480d15000c1020f281d58026580402042100c10300340300b039460420955901c0b6074031803e0300c8000740c4001d42c00001c00340306110a04009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 449047113 1250 449045863 449045887
    0xd200105121302041103070207031e03170a02040302090103030905040b100c0b07020c0d0f12170a020d0f0203010b09040f020f090609120a030c050c1e0d03120501080a0b0c030408 78
    0x426500190004c45e28030054030b0f510740300303600507102c00005a2003698100305004100c0d040c0040e4090402c21120780000035280100104000f424185080040c10040382d20b60f12254125001968064580d8416603500d04028040c1981485240d00543c1090b02c01485032401d80d56000c900719058441540a10309504c8000e00e0035001000e51003940305012032120142e07500d801e100061446204840d003280c00510740170790040c102078075882c1401070304041d2000100307080f03507c02d0f0311044684005803034086031515000501a801c2190014500c00030020807405a14001808040400d48050111503102c0550008a201e90f9141d8680301500384035040f4203240a00c000c2c581100010a903035174044d0001c2807982403048440701100400c1c00721a510041080501c8801c0007260104c95401c10311402503180501e16036040c150a114207081d0240c0000c00d8002e42c0c8140441c0c0b81d0304010031013580c58100b144d907141c2c1020010b131408916640094590006d42080381c3c0f1844d800010981400e9401c848 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 449048363 1250 449047113 449047141
    0x90103060207152d020c060c0c011113050118050915030f030d14070305040c090f1e0c14040302060910050f0d06060818060705180d20010512 62
    0x100f110b40003400b91000d001c60000c1e0080c0001900301c0920402821071900135122443c032054404001d2034018030038894920340100d04103501032810030055550340c0310301110320f00410311002c503107212030390220b040c554031080c10524001b55042070f00c1e03405c0011b40c1341d10340700061101882602d40c00707420300c0005241c02ca07a00b2042d4003500d00c00b8048517054100c0c5601107080d43c0245940c444d2581d521107411016aa10040680c1c11105d2030400b00081d0419498061881d251070207201c52180e01e4040d070003003991b84c41d442249a048181400d0135060000c40011015151116941000401808036506410b070901c0c1124210307a03008010074905082581840207205181d5000b0003440341c14040c088030f0140d80700007030842c240d5400e000141503041c058007802d0418090b181203c0150b1002c00691054000640719421501c681407603a1507821503001841f0f64034280342103c0e007201c000c2d0380754030070090308190041d4245c41d21201c04001042c01e2004407102d010f0541040c40c20b248000c081388446d80301c148 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 449049613 1250 449048363 449048377
    0xf011d0a02130801090f1a09071a04031a0103050f010605060301090b060f03040804030203100b06030f040219080102030a0c030b0105041502010b060408030d0e010b061b07120302030c06010609050901030602 90
    0x2c1d01d4400a41d6600b600d40c04c60302d1000b4183e500c00c40d000071180c100807500c807000110340b000c1078880c081c03404c26105881d610607079170150858801c1d40d0004440a1040581514019540300381003021040c0700100403c60741c0801e2104585d02d10030364180d1080c2c004180102401e4030f40141031142540c2c44d18035542d0140130081801a00200c0030842c0304089400c45001b14800c50003440d0a641d11465481851315140c1002c0c1d880030030034a80302c080c07900340d84c4510484c1d4004007959150840b46d1650b0001030300380d01d80124010102d030701d402c00010f000017040d00518460003103840304010f84030101d44164280c0764000c03006400104204400d01031000100c5218080c07000510002910200c07403c046107090740250400d0762070b540f010030b00e0381ca501e0003809100031403000303e0001e100303920b0a0000f040d8031b805107200600c0e1303142d81ca9030308a100c280c007080001c000b007400c2c15441080e0561401c2c040e442c0d500844551070f090007a0000401c049018841100486001910070030150703295031603800003074002c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 449050863 1250 449049613 449049637
    0x2091e06071b0303020f0705011d03010b0a0603090606080f2109030a0c14010e0109050d1502030403050c120301050d06020a02010f1d0705090114060a18030b0f011d0a02 74
    0x10142074041081d051021000e6100003910140181c00d50402038540750744108981155480844180481e9901a0044400c100c07029030326000c1d071006d44002409003101c0c1d60b00c01c1d008517113100c0010700b0950580142c4015030051004110041c0c840d607540703842e032031004003004440c2d00400c5010010054019040e0040c008440c01d28103000c1ca500000b42803428030341b8160f40901180e842400684580c901c40741c0e40c1c03542400c103a1001250303240040e1003c0c0c99840f5140c89404100402424002c2400144035121100311046680c0c6c50b003850080d20b0343d003001e64103080b10700c034117219481c802c201c810449060318002090042c00400070b0362842d01a5000409000455403609481d80e000c990074003030381c02c0746030b054940d40130038040c030b03220a501d4146640d018601c0345c00400300410900e5100400e04000803030584490b90f60326540c200a440b0003000c6a10012822414140002030100190b00ba901480350014144400d0343c0c4d50314016070701d03028410a100004a0100810885490b55000346402c0300301d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 449052113 1250 449050863 449050867
    0x518010908070b090a050a03020d0314060d06110c0a0c0306060510050f0d2715061a1e0c01020715052203020c0604080303100f03080a0c03030603080c0a11030102091e06 74
    0x17aa955905103849004101e01507442010300112098043c0109528140030021981640c43c1000004103209078450001d059103585640c041060980c50341207030706500102044680d05040c03131500300c2142c859480107072201c5142c02c101280520305445203203045d490329503849041c10200003c1c500c0350352091103400350907591405200010280d1408080c00340740003002021400d0383d28206008a0485c58081c0b01685142c181c0c244501c03120000c0c41c0a00b105c03021043d40d100c1c8000700c01e10700c0c01741020000e22056030303000c00c4141003060150004d00c601d034030600654506810500030b80e010f980d01030700c0c0301903a0a510480b40f2040030f00422100740b03450081c411140030a0b08800818120f60064100c2055508000304204000c018568480300408511100781206031458450310424014443e04404100d001ca03003030410706109402c00d00156403c00c00d850b50302d0341a051031541c0c40410920840f101d21009203690b070285010700c251046810050091041c00080e02080211204218001c690201d82 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 449053363 1250 449052113 449052133
    0x90e0319020f061b0f0f040905090703060c0e0603010504200a110115050d15090602040b0406180b0a0311130303030e060a0510051519030518010908070b09 68
    0x80500c40c40d8040e0690041d1070b5200c0400c0c0500e041c010300414a2200301c042030800000e0404103411030340c86501c403440c4991102841040441d6500c202d034424288141007400b0b10030390b1800816101d0480b8802c2c04200a00c20040390241c80200014000c6a030000080c0010406424150809401640c005007402c4cc1080d000c159040c454018085080009039038400c0f03114040402d1056000800c2442e0860f44118941030009200c2d03038001e1801030816680340d008114048964220001c1c0e20360002c7c00355181ca4543c4858901a01f040c0315050000e01071041e41c52049403040444010b444081050f981340000c0440168050b2184002c0210464420402c02d82840410760700340014500c681e502184001030241d03454686000503100b0108a440d00f010b11100350441020202200c5d41070f1414040c81d9000f801010090081d800002c3d0500c0320034015800441d07150b48610700c5801c00c0841046022950540c06007292030000000305106030412010300403c02092071180c0c401d105100715041528 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 449054613 1250 449053363 449053387
    0x60602031813240609030b06060901020a0b0109021c0c0207060e36180a061e09030f09060207060219060626060f042015040b071403040609090e03 64
    0x1c103980c4184004940034503212000744100c0000e030700400c403918001d4109420342d1120800004003034980c1f40b09c1c1400080c0280264020300c40380c18000d03005102d8441940e0b644003003038003961002c2c5c8180746040010b4941c5580d05002d10625026810340d500802ca1301c7d0400000f51500224004a103900c241c11192600303160b0251101000c10f9610800314100c3ea5600961204244a0181c823250000c0c2c56800501108440002c051035825004003000c204094412007240c8240b0040340b51640309402c02202c681416045100007652442c07076580c560040faa115402c0303885c0d0141c0e0050500503040503401d42407103410070311205034180c09132400140761551005505a00c4800540d6110060300c4c901d010059103106120302640004c1a40246803e03141c156600d444d81d0952000940700040c2079005195580c603040018400704a408e1182540ca60715501005050381280404849100d401215040c800d01c020090f50129041a10b80c85801c90030b109440010709031121100401e84810b01c40c15000320 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 449055863 1250 449054613 449054621
    0xc021204090212091207080d1404080915030c120c04050418050d0305010b09010503070210150f08120f031932011a0c0f01060f18060602031813 63
    0x7204086005943c0d601c000d401c03a000410040c00c8003000d4011801d402e041d40c25400440e070346140e0104010f83c3d24845105140c2c0100521040e00769009023000401082010201c000c04590004a07107489001c84c00b4140c0e180740788801c03202d0550469090005c1040e0100c3c13264150f0300f0100c0006684c0c106a12840401c04640428138461015540c50809034184001030003c0c0d98501103903c2c01340010b43c10701440c00d00ea44a548901410032074000006007002d442400300842c3d26403525401d000c00301d2410b5503035038000040d008840740802e242c0e0340069101800501324952414440c00142080e501d5501025507400040c10a2110009942107101e40d625071300c1200822103007958015513400c1c03042180020040d07040324030054480e402005000340981964000e010b9041089025995450040030504251024460005940c01d1030804502c06c007020b040c0009481c12001040d60403198a01d03540203650040c0720307920258108009068045232203800e26601608080c102c00340595445565204076 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 449057113 1250 449055863 449055869
    0x506031c0f0e03030a090e010b16030c06021b03030601110105040b07260f1506070b010b0d02090406090e0111041212031b08010501020705010906080105040203090a0203060a150e09030d0c021204 85
    0x46c0c01c8001842281280000326015164440c0002d003000d01d2440c1c007d0a03d040e240016040c01591a00042000220f40450b00c4086480034160201107140303602c039969401c25503400740858801031031202846014070803580306580144c510b11454490341001c1d200389130a40034a001c076034600b500101c0903000f82c03214035000c1c1290070f10781c82042c0f03000c044008065042d005098801c03481040288042072035901e00c0382c15104c090080541da0307040d030102040284120844140c00a040a030001020040390b0b0260075600d941310028031003a03c0c800c4050075584124002e50300041c0d138000380c18000c2100900c00c046c150140f4200011000315190842d600d00210900c0500041d90390700c014804d40d64140101d00040c0350a003004c3c1d29181c101180602484414041c19014550100002c1c0c810399040000804082d005800c0d54010701782003115a0203011340700044104a210310740c1c00940c81d001107548505c126050340c040c5042c04400c1c0c4c0400f0160a40c51807000443c410040056404032041c4010402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 449058363 1250 449057113 449057117
    0xc0f04090b060405060a0507061b200708011a040501060903081603021002072303040b04090209041508060f06030c0d0b040c03050610091a0d080f0c0303040c03060506031c0f0e03030a 80
    0x104e058509d0a041a5004600440c0c9204002030200c030328103410000311550f0b0760700701442004004005007040e01d8100d80c1c0d440201d2960070000c40c40b80d4038000c1c0711034912208003950140004d80c3c84e0740c010340d03812420344401408140100240b10306035060b0712104405e10300c02d00c1969031841d102c1c100c03c000c1c0e8020000a41d80354140c41c03061030402d8054440456560a118080e5060629001207420300303020300e1003540c000540000d004071855481d1741c00503058405c004846c4038141e49807404c1581d80c0a041300d0710010910300c440466001d10300090700c1003075904010681c1d96178417425954007001d484054401c58079002e64480100001d941444101e00ca14441c040c0b20400030300c0c007030291068404a400c03402d5606030f0741700f0003c0e40d6120070404140c050340040c540d541d12858554200c8207842032006000407400044240002c01c05100ca1050842e0b004020501c4291100c608045c3c590040e01d903044010f00503181c0a0300500e014640707055007040345042c2a404018030b1004a800c5510011103000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 449059613 1250 449058363 449058367
    0x71203180314100e06070e060c030c06190605060304110d021e130e15040206040305060a0b10110c01081b030f0618090a0b10050301150e0c0f04090b060405060a05 71
    0xc00e9060421080c00348910341e020034420984e9221285448a5001d4180002c1001e416070900641d10303100200c90380041e0344030441e903450507078040c0240c5501047e1250a4450365400b91501c40c011103029040c1030700e10051800e461601d86a440740001c0280404d81904415959080c4025039904110b599490400c801c00e102d42c0c3e003903482085104180c81e80c43c41c14903454050a051002030004404010b01c003444582c0c0c1d41c64a80f400010581c0c055a4002401d40c4680340070008240401c2c0c2002c0355661050300c02d4003000171080001d45004400504180b02d507804a40c503d4115072007080c40c650032110100c40ca001e0b444032030303c10b64490350046958007031543d01390090040b0b504000c000f8100c075480c44c16040b01123046c5031a400b80c5034100f49030301400380503900303001c6180e500003120f1210007801d00900810084040c039803808000c00b01d9101d50024144001d0001e00103400c1d01003110170710440d2040c3c0c1890309041600c004000d011210003150000018800428640c80c0c3c178000349420811038a44903 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 449060863 1250 449059613 449059643
    0x50a05041511010e161d01050d030c050a2027100503010e2103010b0301030303020304020f0907020a0515060d0311010b04020a050c010b0102010b010804021c050709091a06030712031803 81
    0x142d49101280e21140707004400885195102c04146c05c8141034440072a000c030001c116608084840400340000a081c5000e1124010104290311002c1500108084940080f01000d202005940124005011524803540c40c02000e40512819415030180019030680603080e110000700382101c10100c00e5900b19407211180081003031840d81414005500040740c0c0b45150304100a4040601040c40003c0905401002140841d518503480030920364029008038994986040020b43d60580c1600603100c2d8002c500c030a0398000341c0700e41c040388121800341c002c000700900350b80c00f1250a004018141c4255598131403042c038554890000340141811030780c4e52601c074455801810f003140c241440c0c90307056a16100d6810070b241d030081d59881d40590100c800031070300b500b50142003603c00080c0c1001041d0b4012064041010a101d0b803040901d90f020f1200d904035840059a40d0132803030000d860641e416440100b0801c048c400d01807070308540e203209240014030340d041040700940c080b03c03030303081110041c0700d80440d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 449062113 1250 449060863 449060893
    0x3140d090506191b0506070504180923070b0a020102040501090602030403020906040902031501031415100e0c0c0f01091a0601230f07080415050a05041511010e 70
    0x380050a000c8403620b280801c1c0725960080240c05000c14401d0200c000c452014010b1000010742c51145c00109440a600e083c6100802c0c0b584031340a00e1031042040d0940b00d5201605100701c500ea60340c08100408000c400c09046440303000082500b40c2240f084080200303510000e10050000c10303d050300051b1b269420400054010350301500041d003103500c00c1c0f00420159444503d55a0071910544001495102c940003090403d402044926030b140c1d00c1d000004100f240e4490403015080c4210b058800518060304005104101503550400c80c008804040c0130500906140340c1d04a62030102c510b240240e102111800c1c481805502440c0fa50b40307a9404003400011200d80080040010100b10289403a00002c2c198151102902580d0803a546003018a42c040f401229200e6a61032903840d201c0d090b620b81107540f5070050081c00540f0444240004449010360b05403003481e003454a40314142030900065000180e4203001030380400198015401c0c00030020f02c54078010070044805001c0700c209070015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 449063363 1250 449062113 449062127
    0xf05070807140915161a010f030503071e23010c050c25081e0f010b0105190c0b0a050411120706080a060306110307031b0c031803140d 59
    0x400d01800760040c0e54103100b0648004854003100100d03125800c40000046000321400713650320390000103203810301c4607040c04100f0707103810444000601c11001503038a401031b0302c031080e84912009005034400e00910002410021401002002003d00c91006a08507140d0148400002420080101c0f0140320b03011032144c00e02521034070b901c5e203041103031070507030300080050369460481d1103203924051524071500309600348035210004121103401c440181a0000300f45184801043e600c080901c1596620705942c42c1c18041e004191005071682402c0c100c145228005030300e40412000c3c2003241d40100c2400040e881042140a80700944000681d440d0034035191840c0c0751480c1c0140d110390080150700d41202e40000d166000e9031054509803070305450748050032002d85480c2d0401440c02c1c0c01c002d01045602000340145200300c0c500d603400d00466480e0301000783c0c001c0506a86900003120034a000000c01c2c041c0407850222010340080300d80165598940032101600e003498030100f80c001344902c020312075000c55 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 449064613 1250 449063363 449063371
    0x4030305031b03160201110901090b07061506050c1b180a0209090114030c0316053307031205010617040f0b07020714031c082e031205070f15020c010f050708 69
    0x1180034070f0000504c0019102c2c0400c0c0c2f19803840500000344a508102c9960000c221380207808a0314040191182400360250300840e20f0f09403248554a20f01101200309000c50030401c40262003403a0003144039109400a0b2801841664096001c00c00c03210141c3310040c102c2d00a000064031002c23001c0c01c207000c050801f8548020382c3e100f50700104000d020751072044140703000c0f02d404681400442400700d8080880030240018038800e5081640042002124117004003442803195568500d070648012102c4200c80702800390000181c1400d00c0355241c0000d51034a140c10500900340380002c0350807661000301818085410741d006801001003007107a8410b000585015600890140109008004a00000400320b0402e60700b080b0762080882c240b0402240078464101e4a000580d0f214400c05502203070200551004071025120407101040c128454000e58184940c02b0480913010300154a82a0f112000202c0950b0340e00e508000000f078951007407041183c45108140042654681968060311100d4002c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 449065863 1250 449064613 449064641
    0x301050405150310020310030c0803131d04060911040213080606010302160605060120011e090f1709190302040c0201020c250b0d15060302090604030305031b03160201 73
    0x4503407042d580102d450848051802c4e00141c6998034680304c0c0420400319400585202061403001c0344000010005040036040d4101500d141344e035882c446900001e0030b1100f0100d40769404042000908950480c4074000d001d5051004450400d00004049030722154803602c660801f5403081000354801d20020b9404402401c2c110f05000c0c41c1950405510f12082008250f903540320b00240c5680e010700f050f00d1004603202c9a0203443c28038000020700804080c403401d08030401c034443d020480526030242d0546568408100d141e01019a0744c2c0c071383c406404985d003400b0f41c1c0041c84501040c1d160134980f14500624070300517644040c41d500501048480c11280c200442e401001406402e80c0c000034089004450b000c001021000c040c80c0003102400e160700422418100081c0b06440041d00e5003208200c42a90740038140e02c199122401e174101d00c0748e003240c1504a607044c001003000c80c3c040da02540c0d10225801c900b030a407446250b800b000ca5401280d4010035890b2104132661714950911801c56111400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 449067113 1250 449065863 449065891
    0x708010c05090609040f09140c0301200c10020c0109210c02060d2c01150303080129040b070c090b090a0902011205180d090e01170a0b0106050301050405 67
    0x10349002482442000300d5503001c0d6100103642e000545a581c040c0707044010804041200d03c080349050744d421115940528190f218100701c50809240600c540f141c0c545001012000d903150018240e4001d0708100141c60043c09144036480c541c6241c0e000400c08020700c0400000d4415180c54014002e02002002551401c000c44184114540008005401a40468150340c54106103d40000507010b60500881069055000c5200103240030b04850316021039800284564003ca001100804079640300281c00691000d004200840c0306c0c066810b000c1b118074070350800d182c41000c07880c1e81c1071740564041d0742c0e5a14000b0700e1205201e00921014040c298080301806030300b48407400200b00190160440140725501c4007071a0841e0302910707200280d80403001081c402851720842031104041c2c8100c120300f00340100340310700c44143c3c403400c00441501d034031541d1004680d00300342d549496030280d0380b020f503884d10a240c018000301e81407450050080480d651045e0f92581072a003030009848000d00501004040d1b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 449068363 1250 449067113 449067131
    0x1d091b07020d05340311030a0c030b180105060d14151006080c04080c0f04090f050a032319140c1b1e0d1506090e010c020a030f0c0507091a03070801 65
    0x141604c820101d940003600800307088507880000b4105100858010301c405602500081044a446801c070320030326200b030142040e2603181a050b800e0300c0045030380a5201c0d180d200c200b0f0016420413034100c1803c51a00866650000c80040340030150341c01c2e1000852130004000801442d68400783c03082d03010040800070703410207203405499940c2e07429040780d00e4414156050184001d4450754414011982c021500401c040309508025894042c04101580019400d02a80b00501d030015282500451051146440c14000c0004405a200c140003404104590300d034140b0524003400002d480300c0041c04015050700d0440d0446c10346000000c0390800e015040d0b60302c40481c4106007216148540302c06503142410a4118940440150003411007020503c0c5000f6000c01c1a000e182e00100d00d001200f402000711080ca110140d99403904503d004000800030350614100b075104403800b061162048049034203071074558460030242c1da0600d001d501026440c0300001182d19040015000070b180405c020410655 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 449069613 1250 449068363 449068453
    0xb01090305070e19110d0c09050d0602070212161409010b0417161509050405091c030905030d0b010807081006050f040b04080109031d091b07020d05 65
    0xb0040c07090708050000140050801092150000c2c0c040500000401c140361841c003403040f0b00d030041e08003034003c2460300c110340540c0e900960042e410758000918049240d01d03140e0340c035030103948440f80c00c0741c0141c1c0c0351803080001070041000100d10340260260201c0b1380d00701564000d000003024138007880b819020b0010440440441c040b20140c449118105039010307407180c00306180c815000e2510a4140031060000b90301c14440020041c0c4800540d01c500c4860760325020441a68800c0e1801c062a810545170242d004404160010350034515043c0414408166140c10f070440c1c0000b0580622203031604e40c5c00c609980d01807480d5500545508143c042420684540310801801e4043d0101744180018001e114103a03660075580140354000c0f00310b81d0380e034036035003028013030291404100c01042d2130013030803840214440c42010f6109000f814001481e80c401ca6a03154603001140810700c480c034108030aa001d622064040d44c143c80c015002846942880050783c03400c684e03022a6000c220300101d101c507500300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 449070863 1250 449069613 449069623
    0x30e100218040f0b0901060f0e0a03170a02071206140115020d0e03160f0503010c1b0b040c03060504030305090d03020a09051908030a0c050715020c1e03010603080d0b01090305 77
    0x41400d9500140f050300c00c10b0114000c00c20340300b16a84c805c10f840c00000e6441d07070104280c451b10081c0d9903803041503d025814800e525400b400001c01040005500c8000d41c00b0102c0603145d01034081c41141c0000b60385601c859100ca09200e026200c4545458181280800b03912006004220621078862003500f603900080d06c40e0103109502c1e003004082442c04103941e40812401c081c0c5005680c1210801c0d0b990140950500401d101d5079000303500300441c4003240ea0041406d9039086c901940381504029140d65005541a8024011540c01a4005010010030014420036100b2403007900e0006d03442c2820b1140310300d807900500d503c804050042003484001680b01d94400216402940c0008035007281c000750200c1030341550060b1045203c01328110144c103600218843d034840c014000d480708207448038200c0c2000d140342040f42c000750b4030030728403042103044c04228034481c0c80e04a00d40b0020700c050380d030000e800d4411690059810000204207002010000e2143da0492003003420280f285038030f1562035070340b10307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 449072113 1250 449070863 449070907
    0x15090c09090f090c031e010605030a0807030305130606030b0609010e090d26100608102301170c07031706010c03120b0a030c030b09010e07050d0503040f06030e1002 72
    0x40000c1101080f0203880403c904000d140c001402d596400a00030f2900c03005903101400f0125641c01d2410000b890b0402050303000e850b0b50030040300f030314045040c2c40503030140a000e000d071050458003801c0310002c0b41302c0c0d1183e23002840c8580010941d80c00c061007000b03881441038100c099059401800e000c2c0000b0001040441a2214103041020f601d00d00480c250996001d20b20180d0741c1e010900b040b40000d041d031308000940d4541d0b00d410b20346072109840141240c20b14060700c021000400340c0400c042101c111010070307402c0705140c40260b034240e086d1380d010081015201d184500d1000f0660408140d00b20311200900d05000d81000c23002c0c500303440028440110954094148500350001041901060708442030a900c00b034545d1030181e503286460141c4003485d200503546d580c1d032040401c3d8414010300403114070320880310062101c14100000c100e0000c0180904503a0361108000000364070f0041d082e120010700182e20300003103042e550030340c060500c2001c9010a4009204010060303d40fa9102901d00380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 449073363 1250 449072113 449072131
    0xa08030a1b1b020631170d20070803090a0b070b040305090d210305070203030f06010e0604080f010218060712030f0f2901090506030604050c1215090c0909 68
    0xe00d200b03a002060580c0b00745e20329040640c040b65050403018524800000c0c0001c80081c44038601550342d07042c4201481a0020022030303800c905900388005120700504000c16100c456152014001d41c1459403910803240e000300c030240c00c00305002401d441d0100840300244000400c05180000c182e0303441c000c8040090005051100128040003191141050480c109a000c104089038a14688028000000246001c000030381482d0010383c58604c08015280110743c401d0045000d5210640192840b50801c2d1b1081c0c0c0081e070034440040c412600708500e0407250342c400d000581d140e1b806800c00d1901089040c00c4c030b005400030041903001400c130207440ca05190300c2d0302d00041c49044510b80d00c006800d0014142640c40d0600c0b509040660320695000e00202281c145440c1010304a401524100c02e984112640100d0900010350f05050035044294000d0700341c1000c07032030000d0341c030303403001e00c9007403d0381c0310310003055003014000f85400d02500041c0c002040e417000b00c0c2890b07581d13030015104010003000202 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 449074613 1250 449073363 449073407
    0xc09030f170c0a0b011a2a2404050c03150a0507230a09091b05090a03060e0f061b0d0b0a03120e1305010303080f15030a08030a1b 57
    0x440344020500307640030103242e00c09682c0e000c0c0c02410721201d407050a005805034070103c3c828514084c108003040340c0740e1209114020a40350440c84502c0c0c000c11a01600001902071010b110002808800c803280300100321501140040c10181803140c50080442120f42c0260722000340706041d140c101034115071260180201061079038881c00700301c0d046446600102d500b00c00700400c0d419103002c0381c0080c01c4071901a0340e602844c243d59400300ca064603540794000f40400718988501a45501c180024003014a000c2c1020600d00d990390348007421200d60000801c91500540104403130304400703200094220920b50800f0344005043d2108420a10400801000d416503e07110307030405498a01d61070006503003054000f101342d0144c0d000908404030300400c947c80b0300070101010010442d24802e450603650180d40d140403035540e01c424901004009440228403582e03a4081e00d50030b030303000c01102c0d030b0340d80c825124142c8a0600d8100d120a6801c8810303c005c81b2009207210001c041e9000740e0185502101c0031500c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 449075863 1250 449074613 449074643
    0x806060f160f050706171b0412110907080402090708060f0d02030109122f031206031f09030f2d05090a0807050307270b01091e090c09030f 61
    0x44034802c0d10810050650180711030008a09420041c81003000c0c90340e8903a0483d81c2c2e141c902144442d4209540710107141010300060101040c43c070220304e0329034450003200c04400e4050300041d401c100212640740006041c00b0030041182400502c15401001a0400c5515404c01d100054601100680260300a8440908140030340d40c0940104000720707008014800d040c200c041d030051043c582c03040300303c002c1e20301081c88180034007070305000c0310680340044051400c00311142e4104841b41c4e00034042c146e040c4114880030810703c1c41040c0e0300810828100001400010520380504040d41201d20380c42488000b03c40f4901411104042c4107000800c5800c0d0b0329117400c3c0200039205809280152500134262000c017081d19400025110240d800031000c680c121039443d44400d1f500c1501d0b00d400c40c8444002c00d51010303106400e80040718250030505181c5105900d440c00d040510941c130300c0b00c495403036034100100504086849046024800e61500640a42c11340c0c5074080c448402c4007000b855107440d47d076a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 449077113 1250 449075863 449075873
    0x40305070501090f080a0807151b200601091d060a050601090e0403021e0304080a0f0204060821090a050904110f010206010605090d210f08010806060d020405061302030a0c0806060f16 80
    0x1c0270404008182c100714040000c807204207540b201c00748007004145070281c9550109c1c8482141140c00003884000d00d11a82445580009403002c60151079107420000c02090500304140000742c4158075520700000c0a00d0311030001043e10706030340d0080804580000900c40841c0d030100d49407806980030b4000c03803c40d022600300d4900e1485a80d212000070f00038003c0c6401040b18032002414041e000303c5040c420b042d1034011442c1c07200e0f1102a40b25112050f0b0700151031600a03480a800000f200601400c081a07494000c5003e00e20304480441d40a0040d21501c0440e02d0601c80318840440c0a00c0148542d41c1803590141c418401c2e1074407131307118000060740102004200902c80c2004040300700140400005540003a0101d880202c0410116400100104203e035000400900c544002088031841080701d409002c0100310140600342c001c04c0081d0b80694009079400158000c02c01c0041c0045c00b24882007000b8030a14010306030910500e010084280804500c43c2900c682c05800d031000700e02141c061401c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 449078363 1250 449077113 449077133
    0x12d09030c05010204090207050c060c06061011010c080118060303080112210c0c17030f0319060303020706091d0103080c100c1d100f110c06040305070501090f080a0807 74
    0x700a200350b00020b40442d00d0b071503d80250030b0786449a400c03210070060031070070440039014000411403d40e0014001509038507014000441c01c11060401c0c80d01c0071043c81c0b038207003034401750f101500c04200e1a500400c600c407040000c0c4100c040600100304030150540d0b600405401c1c0600c50044020300c181d1600082c40a045803281003010030300c0b03544003800b484603c080e003514a840c0e010fa80c0c81c4250706000402245c8030000e0640d0b0b042540c00b640c0b60090326080c0e00d03260340002e00000c000c5813480e503041e040248980300326005035000340c005220092500302d0082c040d4403503421101001c1c4a0443c0c489aa10350007a4090540f5403140f803d948401c00c002d525031902e420b41031181446401c24400d0040940c0042d0741c0b1100003e25240741685184810034001e0030300a400804000030200c402d001140c51040c002030284542c10800c1d60182c944100004650b90450f8005660941054804209640e00840c0c42001041c1100104620526044a4680324207038107601034201d03803000441000700400104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 449079613 1250 449078363 449078387
    0x9110907051b0a1406150915032e1107080705031309050615070b131707080c01140618060f22050906150f0f0306070203030702012d0903 60
    0x10301c000000540003030568400c3c5854082ea05024080f4910b4840840490352034400d084001e069944020b05c90b0070703c041020020b0005110749041c04910304155810300c0b0f440100954041c0114140c590420306c080955100c7c4014089075151850f07241d244c2c40746000380d0362030b244c200e03102c5038480c1150308101d41503103c1c00c0010340c0041d29038000860003040aa03c094002c1805440c1c1210b95840108102070b54070500034003a000e140030300c1c0042c485041050a4010552080b0b0400c0866100e40a0300030090b08850302c1256030741d801103070300014520240319180d492a1079a40041d140e0402c100401c1c90203500201d03201e460000c0e01d00142d0b880e241c42501017500d0001801d9000350300802100d00541103d0400340740c682600348404a6400a00051214014440100c8440101d20020100f10004200d461051f400220001180101b9a01070186600c24003032500a1a40c91525810082c00c6441e1501c050a0b49820404070a03080b0000c04492020561038002c0050040303914141543e150320808 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 449080863 1250 449079613 449079637
    0x50a18030e0d050607020f070f0e0408031317071509020a33050711030601061e140a0207060809060f0a020904020904110901090b030f1302180f16030911090705 70
    0x4c03052001c4140c0c00902d004482d04864107035400e0035140c5e103514410040610511f02044421408900441d02002c011500038214004040c00c005007507540031036030490310b002d103410907501042c407100b404600750310900488a100c1003000701540d2940058072402c207074000c01d10742c480000340d4400c0804407490748409031040d0300800882c911803c24000c0c01c039440360000700c840c0c1409a11380034090800042041c1a1046520b0365000000414490616034403820001c00801c103000040600b60405407008000500306503018003803841c00c000000d41204070141c842c007030703a40c044400c11001c0c00344000031903005451000d0150383d421200001070007074024440c4d103550007450043d850000100800040850307070401c2e00c6081440d55240d021104078082140d0701100c0e051404001070b0340441b02500c140308588006d14203403119410011140710082d007100c4050301c010142d010b21044040740030200d1440d0f400e07442c0c04d0000c0d60080e0b80710104101c031400c4403800307042440042600349015100755003502141e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 449082113 1250 449080863 449080873
    0x609060e0f0a02091c08130b090a03140127060c1b1b150f08090706140903030708030c090405180a06050c0d0f0510240c02010e04050703050a050a18030e0d05 69
    0x981051089a842588403014080c1c0c0c0c5140000c20010308409c0d2180f1441c028000400c03640745403a80001250402c0600e07480c2e559610000c58156111100726410b1320709001c1401e400031440c80c0000440300c080300c07900103015018014510701e400e4018440112584280900344000100b0414040d510068209940036103120140f8070419510140380100c4001c160744541207922018401703900c5000b18020800000c5148070700c2d2180b203081000510040074060200c07072030422551035986043c0c109403505900c0701c80008a508141c42d081c040e40e5040700030001c0c0042c480c070301082c046540d00001c1e00c00612003a03c0f08009800310541006989050701c1c0741c0b00a003e40c42c0307502140b000610b4120703124094400c1c440c0e004144009141d1488a48501c41e080d00b00f003200e600c65058494800b150403c0341040a01414203001ba00e950080754060344071510081041d05100880d40251400107146030001450000912055840d480030307620150b1300340c2000740c3c500300f046004c28040c80103001c000d032051144c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 449083363 1250 449082113 449082169
    0x3030207290403020c040c020a140c060a020a0c09020f091207030602030a060f0b041a03100302030d03050a051b0306011d101701080304080706030203060111100609060e0f0a0209 78
    0x1c0709207a48035502c43d5080d903c820949000b00011103090941c62001640442071180000305088805140d54140900302c2d0600c40140c800603483d81e004044003001a04240342c100c041140e4000540c02420f0b0701302080d414400c0640038004280a00c941d0141b050040c0605800c1040090128001660b00038105540d0f901d0211078140c042c00c0e8034840c5d80012403c0e13000000e51501a03006603020b8070011214800c000c4039680c100c055680018182013031491214100000581d010000141c1400058802084519001c0710103811a84c000706200564402c1c0074000200c004803a0880350300c07102c02d0824164102c0781c03605104507a40000d20040c0c000300d81000607942d060300321621440d014584081c0d0422683c8072014603840e030003188155881a031002506004d014080d402445c0e0000c410314103d60751420408036207103010130200c1c1229045a540800f4000d042c040e0240f80040c000e40340ea204160f0801030402e0501c0d40006020207130301580030451141c1590381e02d1070b80c84800d409030701d125a0022 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 449084613 1250 449083363 449083433
    0xe061e04050a060521092b0305010b07120518040e1b030a1104110c0109150b04090203101d03030f0f060103050105010e090a021e0304170f0703030207 66
    0x4024001d942c410300790408005840b03441402207544140e4076072450441d42c040b80c0300c442040074014141d170ba002c1c000d101050f0455826034490b80380b100142e02010304402e1600402400300c0d80e068000c1c0b00d00e00d02c10040c0030f000c9a5104a00c41000505d4a4600d550310300c04941d2548204000e0201c030b60050038020309030406080010402080c154584c8210480340489080560380d03c12190f00811200c1c4d0150341000b0340c60194044101509001c40151501e0070b10140c2d5821613000348011101d182401a0f00c20102d0080d00c5075100401082c0e604006076805500040d0b950107540c0c00600665483d4049102580b200000018001701c010081f242c030b074105207100921206080b20081024032200380000e44a40c03080c000c00c0d0407148180c41c0c80140c01743d1a01440700d000e4004201c4141c0a408104101100840d601c40951101541103031a4a07030409141c091040c84a580e0086100e100a001c6015041d810800f01c610f1706a26050042e0703940241d1500c0782040c0398003040c602201204000c0d4219001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 449085863 1250 449084613 449084617
    0x9010f0e03040e0906040b04110f060c010e01060b13330903060b0402160f210e010e0604141905060708030601082a0a03140403170108010c08070e061e 66
    0x1c083c01c000d100b4980e2509102d5695000856000e0300c07900c036110109004c5a82d000181c20990405020001140210301c081181c0358015004001944e648161480d0190700a20880c8090280c8518061a003c3d20036900600502107000d21540f0458441c240814030a00c9000004954048200080c00041102c0082d08001c010b1105a41c90b44c140602c01c40c8602e424421a42500c51f0405045003420041c2c40d014149901010100e5003c41b0500400860803060b03070001982c02e0f09552104d240d0364085c0c000401c3c100c158442c05000b904140400d200000d4040040d4002d41004e07a13100b49550270f84042101015500d84c81303a90000000501341050088000096105120070789407036880c2c0e22002104002d082c070b119001200f0050030500580d501c2807280080c5540300c3d09180108130406c0408082c0100c030303001d80c2e0840204e02d0031a815014041d04203012401003440c0f030001c11941000b00c00240101c000246010b00304104024070101030381c0c40800b9500c90a1141c0c1c86145418806e003401149071b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 449087113 1250 449085863 449085869
    0x3050a12020607050a0c050124140f0a14010203123d27051311120d0e1807030c02010b040b010e13060302030319030605010305160809010f0e0304 64
    0x4a00c011803100350900004900b0700035100d40da601440c3ca1514542103c04120103401116030303548580449a100c800c1004501e40310781c00c0402e010b8441c0c0740ca11700e52071500d4840e841c940030701c2803812000c0c21a541c0b0620072040b5541c03000118018006480100d0844c4101e12034407803042d10301d0091200e005014950341c00c15504c007080404280d0113525210020f40314074425140d07030002140b42403100c401d4081004480c00c0078084041240100b003000503040d15011600303400180c0001041000b03015000141c241c1c00c48065400101d0b00800c8000f1b203443d400c0310200c0303a09000401c0e41c0c00030507446074082058003600c5200107401504100c04d0040160002c031500c40e00542c2000d01103155440c00307116017598008140c5030820780719850000d100e41600207010415007107584520000160320305000820440c100302340300e04090744408602504407511270304507034101031030b040c10841e5224005805030780344020350030124299500c02d0b000324003402d1500641ca00403030070a2681058401c0000c050000e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 449088363 1250 449087113 449087123
    0x1b0d0230090a032a061403160203190201020c0606190605090d021017071107051c0506010b03041e020105121005152d03060d060906060f050910050907030e0a0c03050a 73
    0x19550700c20088545140000b50071825106c20000310b41842000450100508058010390381803922026104034a0714103a0514001350350002440218410140400c0da4027070000c4031000c2c01c8581004250340107140c01e004400500c50b000502c1070040c1d403103040305901140d0090844a0218104174001d08540ca80400f0301030754012000803801e020b00030120803036a190f0702c1c401810b44070b182c0020080b44403d0032183d58010400e826291002c11410311282c0d0103810612860365680c1450302c0e00003041a00c4a109103107041d030b802e0321500141c0c2c5c05802c0f22000340c07880f284044c0c40d03140c2950544030b0402c40e81c461588035070000b9900c403042ea840c0e00988003200031510303060b2a000c01008186401310544c8440d0074412010000540a46030111540702d1075070084c00005419402d699605003166881d400040116036580c0e0104098584885150380c021000001104800d241c039000c910000b030064000700a16403900c0a000301e04104100c0c01095070f8000d881c00f065681d40c0d0801039121140c586054032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 449089613 1250 449088363 449088443
    0xc04030f060f0e0f1c0504090507090e071e0f0e1201050108120412121103040b04090b18010603021602090f2a0409020706021b0d0230090a03 62
    0x1c941c03c0c0030500c000c628402c68050030304111000c1d040c07221840c4840520062210500000c500341d801c03445503910a490946406000c0c0e070a0500c0211591802001481003000c01d1900c1f102480c2000c407034140c8460395042450020070806c000343c1704180c03041d24094020010622540e04a0760541100341203a0001c8192148a09580c4402006204a002c2e8040c01c6244c02400d0000845001713442491100074505069130382615505141540e201da48080179114012809000c070700c9080c813810321504011a02c0148101c0f1000700300d800e07001305110310402d00d580410610f2804107862920004d00781d00410380c074190300d44070281e00e003502c030283c0c5c00d0305580c4200200e8044400c6030340b0b0344104040415001c5400c040c50800071074040d40c01800100c0b2925001d01c42000112604420500280c5038040981301060071064000e00e0b20000f848501c5541c5812401c0c000541031003207080c01c44920220442d55248000350124002046030f5000500480005029218290b01c451903050b0814260b010340e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 449090863 1250 449089613 449089631
    0xc0102180a05040612020f0114030a0902100305040b06010f02010e160905101818020d0809130213062a08040f1a0d0f0e03030907140306041a0c04030f060f 68
    0x22540130740603071110710710907060740c00c0585000e035011001024149041c01c030301002401d00d140581c00a4400c003501d035444400700011850302040d5108140e00e00c0c5410050340ca0a40c0390750042d1740d800f40c1150305004001e031581c0c11052003900010b00c08113052080301c6005650b4a60070540301d4007840be071003440745000e022642d1701580091220449001e900d1b207201c0d40740c1c0103170b98200a0000f03100c1030080700408158000180c0b29401c08038a480d02450142d0384480082080c0070090285040e0001010301c1000b04183c08842a021035003611a145024403101c0350030340e011451050500305400001000c0182c2c41c1c20030101c038004209503064580c0007000b184d0f858102e400d1203903c00c8624580780009011521041803190700840544012035008105090380c01c01007800c6a10a48149070190403500007400b00c400351041d0101c038014154001c00c03403442c4c9031b221074010f400c0302410f0036a1200c000001c01c4080010100707031805141c006030105401d6141e031400074000e05428010075845401c00401c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 449092113 1250 449090863 449090869
    0x3090a08010e0718060e010b040e1029070501050c0304150b0307121a04150c09050303070f050f0106090c0801080a200a120c03030219081c020c0102180a05 68
    0x11805405502c010401d4509002e2142001041c180c020348029540b40000103003000d0401d5243d0082444286c400c0e50b031420502104860400200510082203070410100200c91118010a0896242d084288800d1103400d505a00c50310622901810541c00c4c503040c04a10042d41d0025070096200c1c14640e00c244684995100a0701c5c1c154000070f525400440c010069545810b0901104900c20012070b6034403100d100d0700868607030042e2070588441520300003c60a5941900c134821408007642803c82c110b500c0c00000950343e1103607450003071100860202c02d404001c003c0000c4001c51001c1c0009100868403424024001c1409040280024500303200010b1a00008549010030b2600008282100d503509481c0a691a000d0084240c200040b524000303021420400492b208a01c5103150349407051440c01c0080c075204140001c05c044411b039030748180004401804840481d42c45c03000e010300e00c4220031000402400340403076101c0154000191880740540d0307000d2111403140d0403030b2160401c0343c0361018 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 449093363 1250 449092113 449092121
    0x1d071209050a060c080f0405030d021602030307031d041e090503130e0901050c031909080d06120c0e070c0b100b040e0a0e0f030d020309160314150c0304140c0402030903090a0801 78
    0x5c0a0306a809c204810703d1340100d140c00a0034404480c4040050300411540481d1655028440560000d1007050000000c03e0003810446a154001c480500c5185403280240328030032400142c0d030040c2942c5502010811206200307a5100005880080c0d00322b541d40c07075141e40c424038221164211546040006040006404103503401450461701c82c1c8501c5411040c0f540090182d080c0603540b01c1c00c188101c0f0740c81c021034020000a0100002079070b01400c0c02e8a0400e5402c1e840307420a07060100054200942c0503881022000c1c10307500320700841000d07107030162581c4e03000b815504807240023000000c0c0420441001200640a207855000420600c1e94840c4415212095070903d00610b40041040c12440c00c41a00650382010b20381c8251111035811000004907008a0342c0111080b007051035002810f28018085801148501c0c050000c0c5890085007040e103c0c40000c00c000c1001d28030180001c5004010031400c050040c01034001c6640342000008540e4075040300c1c1216101e101c12806c04640c140b01030003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 449094613 1250 449093363 449093371
    0xf09060e010f020a06020f0706140c031909050307082115010c050f030c070315050121050109050105151e06040e1f060e01091d071209050a060c080f 65
    0x1840040c250380880044401e9000c82c030500d021445040903000c041101c0e440200780c580306c09011950340b03002a1501400307646500c0da842c10074104e08801c02103104542d00c12217500030008002c00b80301c10101d9001800410808038094600c3c40302080342c0301005080e0707004100e100642440d82036000d500e0301c000030404908a80c42c4035400103003a01c06615501815000d0076a604c01c03410743d48011a4800007034a075800140301e080c3c0070b83c480b800030030134000c0c07401c131404000f01038003c00d00a6604000c0c504181c690b01107910800e080300c0019107020700400b036100d0b44003a94400028003a41c00e003240f031020b075001d0b50080a4440c59600808003028141240c142a0011010700201d0401c2d00d420319000c2071003802070510703240407840b02e02226480c40002e02c51000e07020320b441d039819003032008000400c0c0c81e036035401c40d80c1c1c0e86002d05010700001000e0241c041c0d1265662a040848404015214010700f03141c0100034028070a14080c0c40411145410070100140303541d40d0308140b6985c2c04011420302c44103903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 449095863 1250 449094613 449094617
    0x3040603140702072c1306150b03010510030915091b0e0606070f1202070906050a03050a0b090717060a050a0212011203090f0e10060f050f1c0212070f0906 68
    0x40c41c100f104000c0d070081d000c0784940010040710051740e210701a0110030341c00c68407a00a048007420440821009100d4844a542c010075403592683c10400a8a5203100600686100e40f802c1c0802400c000e12030307000030511039480501da010808514130010084d00310020129040440c61417490001502030110204540d41300e03124060710703101c882c144040c90b80a00815240041c904104d8400304030303d00c4524407400041c0e07004200d03a501d020340e008112040b40c0c0046200e40b0080c1d004101250b000a8100441a040741400c0c540d034031400e915524007003442d404440b082003d212130013005072010902c2031050203018800d02043e40d4010170203049114001d00f54958401c500014030804000400100d6403610900340b0708092526148070b014500e40940c071800c005100c2c0320420900b8040c43c40071340011b1880e03007800c00e50b25515030f9002e0010300030314115141526003c1045030714441c0c82900034408682046046540e078075582100c20400300200e03800808103440e41240d11501d0720403501c0a0071a0229 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 449097113 1250 449095863 449095873
    0x503060601050a18051008090d0206150603181f0e010c0504030f0519060b030c0111070603020c0c0d030e03071e0312030b040c0801170102040b220801050903040603140702 75
    0x5580f040e50f0120b07100c542c0510544103448081000e460356210b07246d25107250340b00c900032850000c01e1a4a4240140c0004e0f00b15001001030006406860000d4000c2c2e4038201e41e529282d544071941440204001d5408610a11817015419241c40d92102203114000c1c1522050240106009a6500761119901010000b4008010410100d04401b201d49420b52055040e2209001c82c00111010701540890035107503582c0c0d81c01d081c1c64516082040c4621507100303007400d5142490407200b442e12804184a0701e41856000146440c0443d401d1080310402c80c1d00400300c000140303007400d00400c60320a09680500030310400401007602e202d038005500b403e10420502c4001e09095a40382c0d0074241011040c1c50a061f2110390400d219583d0b801604549100c42d03032022165850f003100c1007042d191041c0300070b250340d20401083c808001d4520031141c0010302c98021000d03000074118009243d115551195419520b4442845061800400108229001e9590a0149840c601c00891b0315403410b40d840340142c1d100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 449098363 1250 449097113 449097127
    0x303091213080d090906090506010816020a170c120403080702040c05070602071b0b070b0a0e030f0f0406200c0409030e18010317040302030a0813150e0406050306060105 74
    0xc114000d0006000792a19454a5607581c2101440e120002189501103121102c0c00d0007402c226202d401d0080040000500680c1030200020380541c00c00362001d03192101d04481c1c40c90a900070001d080c00540d1003011060101d0940340302041d5604540c1364640c1500401407181c00f004410400c0e201600d4104030040e2502e401c60382001700410412503030b01c0c14001b0510040001c1411032014103031060241446400003ca10b205001e0810328036040700c121a0380038404000403442443c40c85511100300c0344005450740840070f80c00d00c3c5000d07410015500b00000198664846014130244c011030740c1030348900d100c034001c000e600907083c182c2d00a850792503070003004214118a03058010001e114040d0410001d20705402d00440c042c0c1003c0e1640408414020340100200805003c0032030705112050038040c1440c1c15540000d86400c4444405840403101240900941d0300403104040141100d5544e0b240d2400820320240c90600e07012100361056280040004450a0200d0183e00ca2071059443c3c600d0141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 449099613 1250 449098363 449098393
    0x50f010f0e070c0c0509070e121f05060f09191b0804030e0d0c080106030203060609040b0408030703150f030b16020d0f020f0106090518010b01080f1911030a0c02030309 74
    0x103d0b01c0000c1c2c0304c0026060000a1580b281204607000c0c000c03d5450100e4005440144200c041d21000844051352100c4200b4889114441206100340c0ad441004203107a110704000800c00c260322003420b0350018940d402c0c030240c028050f0500c04000c440b407030140702c00420740400c80c2108502d0f20040323001c290110f0010b00000d200b145030101010000340300c000140b80503110711000c0042900b09105aa550380c100380207510f800c000e5698007a400f111261582c0c50319594013502007002030030040111501101040040c0c3c0a900402800015034010101e050358501154003010440c0c401503e5482450001c541c039501c0b601400c44c0e02844980080c00012a4044112a01d56681600d001103000d0407503102100c000078000d06d4000c02811030081020b0a1440030041c03141a40d46603400c490785450308004c400e90300701822550101041d5004034555407005210b040f0f49001c40c44040d0001d00d01882180c281001001a501600f105034042056134000c1d0000d80c0e4034402900c1c40344003503001c0455545400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 449100719 1106 449099613 449099627
    0x70c05121b060405030d27030305040305210105040606020f060f1008061503070816090b04110c0d020610033206070906120c0e0f150d050f010f0e07 65
    0x7d0b0003100702040d0403074103c4000c0925880e9400182414040c20584082c4000303841584090080c50700307245040d0400740a01481a490104041b485910000d2040c81d1508a24001c00c0c1c00d4451404040d041d4400a14030b80030b90b88018404641850107100450042e001010001c04044400003054280601500070122aa20804610034940030304915a01290004d4030000b0f0030600c21008180a000755422200444d01c00088803028030a0004d480b880c1d00747d4070ba00303170b5550343c55001c2030180b800514070000c1c112640800340100031921204508010784115200e040f5402c41707a1842d039081c4903003101c0c0c2c40c0100790103403c2080200e40041700c804414859100070400b00e4007103907002c1d0101e02c10347c903800e0040e5054965070145868990050000301c100700086601c0e8207081050002a1034111000e5410360b03841c800000d29452075140003415100f080b0a0480517a50740030086890b5 = true := by decide +kernel

theorem cover : BRFrame.Cov 448920863 449100719 := by
  have h0 := BRFrame.cov_init 448920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 448920863 ≤ n) (h2 : n < 449100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
