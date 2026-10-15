-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4711
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:29:36.589892+00:00
-- url     : https://prove2.me/submissions/76170e7f-5a00-4e16-b913-c7fe9ce8fecc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 847122302 ≤ n < 847302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 847123552 1250 847122302 847122329
    0x30a0c021b03250b0406030b031e100b010504030b100509090d02070b030c0c01110a0f0e0306070e030a1e151506031d0a060e0d0206011d060a05130603020f0a 69
    0x444008058410302c9940035441500c03400060660316220081c0007420031940c7c040754560000c401d040c94008103440b4040c00102070742c0c522001170f000040d015004850540e0111f41d01c10a0001620320388107503000501003607804010041d1401101116504680d02a1540c10f052b590340c0086a0715008061507190040c0c11a80c1c0c204070100ba51400b42d500216581005450700045c00141400c5880c00101e50001ca2030106d05400040e411112000d503229a6042c050b1070007400c0e10001c0d8440b9001000001031200c4c0d0140004103407001c1107941d0310315900000303202616450390b211148060012204071018034071f060031030f5507121040c01454252255507a41c0440941040f000381c020b8000980491200030344030111004603c000c0008141ca54091b80c00004c0c4015031052807428180b40e020200c0665000c2c200400041c2c0215000c0403110300c0095034008140c4544000407410b001075480707180c1c040350b034028420102000b54468800c8910884105448459170b00c05d200f400921445060200c4820 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 847124802 1250 847123552 847123573
    0x80403200a030c0e061309120224010b030406060803030411090c0c150405010e0a0f06111e0a050f0a050d06060306050f01030906090f0f0303050a02040b2d030a0c021b03 74
    0x80c2581603400c000010b001d640048100c08104003140c1441c1f8003940e00420390020400c0340f41d018801442c4002c031700150f0003c0c001081c10380154819044c401c452029000100080500a50360302a401a00c2484143d903928102410078901c080e45107800d041c8140e07542c101084c40d085007442210381c92051000039180d007101c0a8241500e402008005503250754031070104409905041c003850088031305c144010b41d415070150414401300c0d501c00d14030300d030040b50400a42c05071450145528044003404584140e451000c04001c40d86405444402000c1c100d0100d001c80200741c01c0005004a243d40802c1007200641c0e8030000c50682e81c0d41c0c441c5076084418482d01d01d400e035210b40c010401d90742c05010041054405507884c0c0d070480311410002d60f540c3d51505400d60405506004443d08030445802c10350070079042115088191240c8403020904120300d541c013104072400d20218003071b0301c2c9144907890340302c1c0307040c034500c1d8017500152580d10018064444410071040c108101001d600c00f01078000c0c01c030f4491 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 847126052 1250 847124802 847124819
    0x903080601031a030f0d020c060405030c13020708132306090114070b07030905240606180a0b0405041404080706020c0307050a1109090a05060c09010903080403200a030c 74
    0xa002190f0440c0d10040d401080c05038038104180102c40c9200401130001100c1a07038000e007040788815419110b50000c200401c42681c0011300c501c05044212280402e84410f682c800300213200d0103400620f2500d001c2100000014144c1007642240d440c0360302d25101162688240d03c01039500030307819910031403c0c4059880c3e035124102ca40d580840a0740b00515003071540d100c0561128044840100182d141d1950008004050101c4403a0b06150f100148811013202c8500300c0e1540d0082826002d810042444130080300ca80c444d1681001c40500f046203040d480c1c0c40503020560040c052030b4061801c0c400c030358036000e0300c00c4d003001d00c61038110388024180307d015940e00c0080c0d0301c40703109407030740e40700030f001040c04684240001c810072445403e10400f00040d40b41440803c0c0001007414555411403102040484d0700490059032062100c044140d89a07446401a0342c504c0310340c1c0002e004014085008020880c510895080440207a000700560280480802c010802c0f24000140741125100d000c000021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 847127302 1250 847126052 847126061
    0xb120d030b01140c0d1b02030102070503091801060804122d021b090a0e030705120c060a021903050718080a23070b0d0f05090a060b031c0c17070812060103090308060103 74
    0x161100b240c03082001b6250000703400e90704224000c0c1d8a60304000381003005850140304408140c204420481110741c9090805080c1050003072010b4a034107a08028001ca451044080a2803484003030301d40003d9100e6031401c00c01005855981b240980725100780c1c22220f02c3c44420703180002400810142180d40c40000200c0944410603e41d4940d100030b10418000545c03c0c421900100e0324111101d0b03c1c0d007418045180742030001780406d07080c148100440fa68a500c0300510700100481401e004c40c0d9510303015001c60300d003500c0d44103035403840700c14900108565902190350310f5114090180141d0300d203911440c0700030590103c0e00d2584160301c00c0d6810400e80c1e419601a20926004000005070101e42e60b00c50810745204680c1c3c401135410481801d41001142e12130f8118540d03080d030050166806180700451200100304840741171040701c0a00000300a03007800500c5020b80510354840d1106560302d0f215005401515040844140c00b0380000d80d154400d22a00a04a405603914400358079000015001070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 847128552 1250 847127302 847127327
    0x105070c170318010807080127020406110708060c0301052b08041707180207060e120a0906080412030e0c100801080c04060f05040b120d030b01140c0d 66
    0x4080c00440040c1280c900030a42031500800005555128041c40b06030a00f00c200399146414041402e051010071540b1000c0b40303056441101250660130066140c00d034200641040c0248000d00000c0c02140135a4000d80010100e40084206c0304616103444a240d02c2302070880c1c2c802608042400100500c1c03030070f1001d410154080d225610fa880380903407030128a80342078200075034407a20002420480c07181ca803410300240900300c0c0060400c039401c12020014400c041d0304100500350f00818280c040c130101e2360200c502d08140904594020780c001110040d00d0f0828544400491505840002e28900644882c1d1280d68052a041400210003000b42c000305001a0149020322541c0c105060a49440b600304404c00d4460304e400e08103624000d0194904280c0c070106500030340c00d140041000840680802081c0d5108035000b05404400402062007400d82001882c0244030708100d2017400c6802da445800780c0d440a90307601041c0d071062907000c10544955144c417041503201c80d150140781c502c2074800380c510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 847129802 1250 847128552 847128563
    0x6050109080a080d05340f031a152116020318061e1606150f140301090816210c0204050711100509071401090308090d06050906092a010507 61
    0x40401d00c007011104007080c1c1907120f200507840740c0890041ba410403042d0380b60315114078081c00740c003070040319065202010604540c01038001801c0d4810000780c4030155280d40080d08070122100021288014103140155440c0c050310000760301c001c0f6410720100032035032000034081800c0392a0341c0b02800e005c00365110f44680030409040028006c0c10003541d10081040301d0b0308848184402e40340e030410100301e83e0501c0700000f0901510500700041003190b00404200c8445141c14004c900007000401c1c0074204041d00100004000210840d05540132010402e18034081c119001c4540d51003046556404d60b18200311000c19107050311a00103251a42101e540088685032004030b464101a82501e0002c1003031b26038245540351420400580c0080083c480200104040d1141c404113140019080038000d000103001000c2c0040c41840d5a01d4841856901b81c0e80807808101c0c0e03243c0340d18141d80743e840548003021503024a42e00c2140e025880c52518541e80c3d05192900014030b12903005554030390111404494 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 847131052 1250 847129802 847129831
    0x30403030c0501021c051006111509071a211306050907030b100e06060f0703120905030a090806100f05040914060f0708070935070906050109080a080d05 67
    0x3045c03071488a040004000301c800480c4609003200c517000601c2e00768002d40100120f86921080c3ca01c000520940051440c4001035119161180300c0381c02d05045412400311904419503e1015080100c028941050080c140c80c481c20303e00f118070405c058003a01c0490300c418803504c0c0600498855031209403c81041c41c1140d00c07140d0703299078140d000c0c0302c02c40d9084007001d140701e03040050809903604661300000480e401403502c0802440c1200a004e0002d014007000102415001c1840da15400203000a030880c0450ba140d20290500070320415450041004c00d001e1480480e20864040c1000029030700080075030307807503503042c903091200916402c1c0e402d03100e207800c04c2544140e142d024007526025050f10302a4102d140341201010f022640c000c0e200c134040001c1c1360360802c2148500015100c0c169038800c107208803220a1850700c2d01401c80904010304038050341da00042c418465902c840200c3e4000e0300d501d05415503a03030310340e9100c0da120400588100d10030407078800110101d9004951009000d0100b08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 847132302 1250 847131052 847131067
    0x204050d14100614030106090b0d1202120705060a27080d0920040b1203030f1b0c3d0903030221010501201902120114180f030403030c050102 62
    0x4081e0388155100c8134400328101040314a5060078010a40030300081c6405102e0020000045662541610340c081c1100198140700889603200303028400248240d0030f4070f02c2c3c03661518101035407165000d0318901c0100e0300c0d00c58041150207442900c11607908424888200d42c000d20f8403a44043c0d403018030300010703071a070b030301580070002d507c1c0d001c0204c2c04855145105440f4084c141840201c85004e4440c6201d08450060440c400800204a0f0b51001503424294a103456500415244030400d26030303030750374141c04100302070030a03000541e502c0010041900e0100c00c0700007008002c84400b0300e00255010401e101507054400306940c01040816200707180040ca0220b0750001001c8081007030815689851016004002a40e030004044160041c0244410740300c50042c4a440c1d0784040440c81360080d00342c80a5000199522000e2210361801c40e02c0090048040c40c0319401482e00c01204e101c1c4031491915804146000001144124240088021403516056031026a200105071404540c590340070072044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 847133552 1250 847132302 847132333
    0x506060d03031808040504060b07080f0c0109060207110a150203040902030603100c02060703150f06030b03010f061d090a1113150308090f03060c090d060b04090305030103020a090204050d14 83
    0x20394500039130038642c0703c0c0e0401d010001901c1079544040b1030300b0400d01a05002c9503c80d41120315513030714100800c3e81c6010201c0e07a1405454018800351401c4e1000c1690000d01a013800280c5100b00d00301c5880f02166101c03105001012000000000103a0041c041407180c070456a00558200000408460600400032148030075650781c3c00851006030032420600c14015018041c0507070407a0300e604585074050800071082ca0001c0c0510074074040540315903400c02039403020b50250212944005051140b181c444142c804400315981110b101080712500180e4000000b088003948641d016125280d010407150420a070341d50004201940e0654422a14a0504c0c40c0001540114445c020846d1551142000c0002522204e1a4240690064030401c805503074280d0031100c071400100c0c0d010f448a106030900c0c000609468032041e40040c80c0103013413024140c00c040a14103c80c0f003187c214121584619401c81680900d2080355000081400b02c000080d81000030700400c2e0440c1d0003204c10b000343c0582035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 847134802 1250 847133552 847133591
    0xc02030d0f020610150e040f0516110a082d0309011a030c1f050c100615021b090a02250204060501090b07060905011d0d0801120506060d0303 62
    0x201001c544420400141a901400080c0d03000c5966001200f440c0d01c1d00e680c15200406000b0b602c81000305000f0b81c54903554903640840402084c0100402481c84c00c2c0c0480c2e5030560001c0c03000c03004a62104000d1000c864001a91010304e584494020305204282d02e020389041441040282500c41400100c1300840c10b10000d54482c8030740100101788080515501540d086070304040c00e000350000e9101c00c07102d4a0741d44021081a40c03541e42c5c0058040c8014080b41c980c0548040307a4800d005810b0030110101040d00b00d001a00c2c00940001d0180a0b681420390780c801150142d00b41d100140315422003140303007074402150300c120340c141d000d451704901c01d06140350b0301c0c1d408500c3c07040390418480c92400c0d4106481031202906007800d0000d03080d400e0041581c00c034001e103000200386940711107180c0100a400c1d00202d510583c50920b101254026404440e11441d45101010000b03020b1000003034421003101000348015084005030546840d04000e000544a000030241d062640381c400011510500212 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 847136052 1250 847134802 847134823
    0xf100905031b090f1e0910060b0c010c0507051c0c0b010816090c052a0d050a0e031501050d0303150b0a0306151e0201060909060516090806070e010c0203 67
    0x81e00640e0b103040508101001e0409042044a01500001c01410710300d00c0e42c1c80429540301c4800c001c0c00380d4500410919041121941346901c0b41044000a45540081d010744100d84102d0000d0120004420003260f5900030004081c20603840090020340d03d41e03540020071000300051528440420094072a1741c1d80a80c203901102d0560700a1912985034141c0c607502c03038050200903401b446158a440f20092140c014004441c00700030244984121204c0b5006600b521080b4801c25036201d005d07410406400e9400489142010403040f0801440c1d81c640440c0c02e000f42c017080711109a9907401d060900c05504c1401100310141507031200b03440e010b4004101004000c00c08444226a50303502150004c1c01d440c0564060800c04125401e0f041e102c0e0303001390740d9425000854950084100ba4030b01c0490140c502079000401d030600e4910310505010f4981c119600c60745c003440d103c100c4502181c10031200da00c0d8500c41c030400c1d908410080b40e242881040910201c05052502000720344268001a007003200e01349 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 847137302 1250 847136052 847136083
    0xc0e0912180306090d1e20010c140918060607061e0c080906060d08040f060c1718090a0605090c03040308070f05040501051b06070c030e030c0f10090503 67
    0xc0d070000d03080c9010000f10b0750080b40c03c00500140f0814074000352110326107161100c0401801840807a031a4070a4500042503404003d6030000d8007011031042c2d00030080a64924005503003045203c2c000d60000d402c4851400c1c014004251300e803501000c2d503540060290015038001c0c0104102e501041240c003811481c000701140e016462102041d00004440340c480e5403006020400d810402c6040c4003040b4140c1c0484240d40ea4028440c4901d0060914442e030307003200081c020b9036240868060390040c900d9500d00d00c507035040507000c90003c4001d1200c2c02100060012500002d080c80d03800d0030001602c3d41c010104440200d40c464850700050344000c01206c80750400840401000181030348040425000046818007110400c01210000d01d280302d140155418040b0025640720420303040030307448540300c0c0001d058584a040c90b03c4014921481c4203019070004e0720741d03111006e05140c0401d1b24004060000c0c81d04150300400c03020301c8200c80040380240140b240d4524000384944051021140850522 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 847138552 1250 847137302 847137337
    0xb040615121a01090908182116061d011d10120609060b0a050a0e0a0314010c030e071a0403021008090d0305060904150b210c09040c0e0912 61
    0x190741203039103400583c801c030072660805c94001c0119024804480c1e0000d14a000c06409030005400f2401d210707031605486604002410443c903016070041815807501c0814501c1c01200c560701c1e20102c070a1040a00092000400c00c10310324401d602542400340f052449034002286d44200100141c18500e4400b10580031400b4410b40302ea1034003c5120b00780103044054000c22099080007100306040c0035090152043c0030001941043d454000c458155009a00808102da9681c603440d0060411821300f40c01c1d18250700b46070201d95514080e01511a0120044008050003403820b0308074145070306043c2002000d28010000480076880d00d180907031404190b512a2125410100c640c9407400305521140c004040ca0030060042564441c0841504a030b000b42c010950000340100da10f005100e0f1140081e88031000c4000d81d540b404074061000900418201910301d082100414000002001c84008241703d00d1500c0030720100050380001500203e02d9012a040c802031050000400da1040c46250092001c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 847139802 1250 847138552 847138583
    0x309090b15041e081204060503070e0a03111c020907050a05040812040f08280614151c020904121101020309030403021c150513020411030610020a0b04061512 69
    0x524100b007001304100401040b401a95040080307490155005407000c0140000100c1c84140c403910312086128401420400030999030300d84898203031190003840380036400a405d8042e000503001038451040fa00500400c0259a500c101121b499028100030340c00c0c01424440865110b00070083c0c88008400005441d0391181413407040082d0018580c4868190740c4841012090591007081c0c00400c04440c800c110b4000800307240803000b0b025180100203d00c240c40c1c04010302c9000034040c0d640305843c203031000740c5c1889104411400030313000c030b00000e50010414000b041c00100201c4881050300c4e21441c00e0b40366000f00080640c01e80e481a07401841540c40450203105610341004141003d600c80744002024a24aa551110300101400189001c0c0d640d03100040780144108507000c0c580782d005108100c069480c0d982e0114a8000b0f07101180075010314488461fa05000151000340c403034010400b03121650700d40d0f8a40d40505141108040c0281d8500b10000700e503130034444801e004611500400401301d48 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 847141052 1250 847139802 847139849
    0x12120108060c0304170a030b0306070807091203021f020910081b0301050f040902041820090118052d0901110a0509132301080d0c0309090b1504 63
    0x100a0700d415001c05082040c440040c1c0041c00d4440000c11400c10301d5100c6e28018002e40c01420b414400c5038040c010394041040c01070340907440ca4031450042e02d42e060708036107070442072500c15588a4010013507405a400045240008840e0b403030a00c0301c0c42800740c80e11080d000071550190f8a50303180e40110380030406200c0e90764000c1c20800c04201d604140c07a8103561501d0b00040c0c081083c00c084078000c50742c1d01c032841c00b5921690042c4003000d103800301d040d501c4103542c0b4005d803222040010300a812051402500320601c0c240d070b0070a0498013074414861035806005040c2c1d00810000e0462002076440034411005481c83c204c070014003411000e151140c501e8802c035010b09444d103500b004090301004101c10301c1015001800e4500c0c280c2d0507118581e10b60007426070b0400506082e03c0700c2155502c2c00c900f02a80240c000196410388202400769040c81d40748500941d4540c00c500720040204110900922501da1154060305140800501d100100040034884102c03603445030300043c8000c1e6401c1c00070f110510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 847142302 1250 847141052 847141063
    0xe120c010b0409030c0f0311031c0f0c0905150903060a0504060b0d261b0f070e0613020c01140406020c0705010503090a03051308190b0112050a08030912120108 70
    0x14400e4400340108030490754000c10036030610310300600000d01b10b0014030515208104044200b41e04504407995054181c0808207840a0090001202d90a16945601e000094001c0c508880c6c482d4a44078016414141003000c4ea00340c00b1103031031100006005c0310b1200e03907080040c3c0e8000c07433551030006264100340c1024400d58652150300c900076588001c15400250251624404405207101020700001d90f2034000d280c1c512540000c9201410440c0070061400408070381d92050302000740407214083d0b070300c69001800003011600b03d513006151288000984c0c03034030b800a1034459440800001c5009d420340c070b1209042e4080d0350565a00b40e020074000002d402c1001400090502400c02c1c5056141148141d030740c039080c84200900300038011070101c0000c40f5950000001c0c0c00d220058a14500c1856810380c2806182242550410382e1300c000000c80103050700c48000d031190407101a01060302140c0b112940c075440940650f4003840303207094404002204d9005800080e07000c0703041c0c0149500d010742d102d1800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 847143552 1250 847142302 847142321
    0xa03050901091115040e010e10060f1b1a0a140a1427251502031801200109050105060108060a030f110a06051902030f0f0d0e120c01 58
    0x10780c9440071040114448115207810035100311103110705840c203030802ca2a60b00980d4004c1c0e400c251854004110280082c54883c45040c1c200860041c00b03540c1e0301d04481c100c01c0c40d0488404200d03140750038030710a05641001c24519009460343c640004100c0380580307450000700c80800010303139112444c0c0c04c012140307003074680c200003222010f0180e2281140000f0100c0c0014060211114a40c00c0075030302c000300d51560110794440403080e00c03045480f080c0034081511504100c8040c3c0c110010000c9074003d40580301c00c001c01d00c43e030b00a40c1054048110f1030100c80c1c0c5000070754103024085403540c1c020100100d05c6899000e0325000030410b0403051824500b9110050f08190510500b8010407001e2f40310f01c54903408a07500b08040d40c1c686501404c141c60707102c074400c1003103422802e50038000c01d450780c01000520003842c00302d88098408007c980d080361603008a06200c0d4043d00200300c0c07022881800307001b03004a18001c07600011008692310202c3c1c1340400e4418008540540882c401c000313684203100321130f83c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 847144802 1250 847143552 847143571
    0x1060804110118180b0402040303180503010c090603020a0909020f0a02160311100302070b0c0c0c0307050114130503012a0801030507030308070219030801080c010c1208041505010b0a0305 82
    0x2c3e070400d07003060340d0010480c000c1d000b1150404040c00041015504050350320a800750086503210b44070b050040521000d0031000c10000d880c068001918101445516551116661095081810400210040d501c1420340d03030108480e9107401b0428080500c02083d80d40101103480b079035002596400b0707007030428070782c00c0318401d003c16942000417940b080080d05080004a0b0120410700350501c0c150001c0c01101c401030075503034101301086080c8101e107009101d0350701e4540031034011451180406a0b29850b0b130042500040c00e0000c54039002018102500c40d400450f00b47d8960700740c0707400c046800c40305400c1c54045000c07030820f15034159103003405889400c40c1103807505224640c15a10740c1d9507502c00510000b0b0420002d4800504010305c01d200006503a010b071520520008083d04009001c2442030040704801c2c0100559560113600900c15083c0c80e0341d00a03000020070003681d00507070f42150020305c29594044802e02c8040f02004500c5038a020f407801124182d216251408014102c3c2c8004200104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 847146052 1250 847144802 847144817
    0x20c1513080601230a0501110a1b050a140f0f150c03031f061b0609020613030b07030c02070e06060c1203090d03060506090906010513121407120f0206040e010608041101 74
    0x21316180c8003081420340340282404440045442d6147e03181804038840035280e9a038440c0305000c2035500c000107038200c2e030307007111305d80301072903c03149000b5802c1c8840140ea44c4c4411081c1c003d0381e503824030f0a95501d040340c3c002c00c0c01d07820b1201c091320f16059600c40164601250000010812001c062204903214412a2100000c086080c40d00c080c02d40340315159030b41c0a10202a50380f80401845da00314050140e80038004507101e0f13010241c502e0f80c0480900003140d440380950005000720b840f030301c1a5115040c90ba401080e03a18504070f65022001030151195420082c200170740113130301038100144c00e07001c8101d1426550f6460495000303802d010207190800101030402c0c4080102c0d685000aa8254907001c4601c0390407034452000580c2e09205941c41111424041c00c00000e08030060070301a0b0030b960081e01e40172448050500c00c40d41b0b400c028081d0030404800b90340f03603002168032420494131482c406408140b030b140e29240180c5510a099008c800040c201c081088100f100d0700082c42644803082c02c0250 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 847147302 1250 847146052 847146119
    0x61d15160f12020706390f0c11060c0604080703020d090b03190608010608030706061a030f0702010f0218010f0903110111010b09040807031d01020c1513080601 70
    0x2042d0308034040b00c000c81c09402054a800b8401517600c00126008a03400804207490fa44020910014101c25100e680c040d001046c041080c1c026502c5196041a80e42d03014140340c003946c2c846086440503040340c2d410020500031890885000c01800e030150303028207485911150103140007840c00c20700300014000c01c1007154040009182d400152a0420504401c095500b102e03003a824004080c0b5600000c5150708010300000c030414088010b0411500403041401a10740350940051408011041d10900490800c0040c0405109511503504034850f48004a82c20111500300400d0b608106000a501c0744009540e9581d5a0043c07c64a100020b60400c146a1451612243d002c95800b00d8254140f02c016500c040500c1429401b40c0b10400c0010256101820030b4180202035030007401c001c601141e08001801d9110b42c2c0c00b5001da40e0018140c0c000c05100941400780003c6aa414003069051902401440000c1205164003000f50011200600866241034102510b800e800404861050790240081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 847148552 1250 847147302 847147307
    0x2030a021b190609050a050a061a0f030304090b0a0f03080405010e010c03020a060509031c0518070e15010e03030703030504110d0f110102070b0c0c13021204061d15160f 74
    0xe003502e0f040100058076000c64140b0314108444248000c00c18000d803802c99040104c964010202407414040c0070441d5031642c010301c403c070350f10010700b1035056106010400030081550401c0b01c0350301d800b070020800035640c2c41c541405d11803603410407202d0310340c04102030006581c8098038890503542442e0140143c4010388000e901e4401d00113014241c00e0701d079000a418807004004a41212a44800c42064040720031710100007480e0030360710419000c4074011620460300e0001609000c0c1ca050045001440e00c4000d9075500c11001c20b0320701410b0168911039000d245d501803002c1c0c9251400b80d1004200d0707180600e4610800b5038264800c1c0e104800d20800b030404210a4050300c00010b13881000d00550303401000050b49441c226034411000c4040000d0b02c084c4010000c01e001010503019203602d0b8040d03900e84d46d00401c0e402815603100c00813a900000601240301074100c904801d81c1c001c4a000401c2d514040a400c004c1c030403c0802401a8240502921191078240d40e09848030510704420103103c1c11500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 847149802 1250 847148552 847148593
    0xb01050702091311130504050f0708100216120c03032018120f0a0c0537090f0c080606180d0311062e0825050402030a021b 54
    0x2003e884000c01c1003894104855540c110000100090000d400100b454a241c0060300f02142c0490f024007840d02d02a050000c005900401c2d210488058034071103800d240060000e40000a5007441c2900300076080e40800c41c010400d88143c4c506643d01e0410150340c0c140601941d8500a0189090070403100d481c0500d040201039400b00f606042c0c18242c12540040040d0b0034111002c0c4c101441c2c0a50045101450400101050039900c034007100a010b5a69070308000c40d5040100d08068180d009468107100300600b140000351000c113100800244648a60b028411075062150300503105075280c804072089500201c1c55644100e0031201c96281000c0c1c45041b80703482e2032030b040f0f00307004441d080194410140100d820040c12991901142c2c1c151801c1441e101c84414040324103104401d18034041155050b00070141400e503000b8000900c841e500241040c00b003c92221282e6848500305403002c00e4940c2c0d1800218045d001e2481c025071a0000c003030300002801c18925000989030300000308007030300d5030210704c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 847151052 1250 847149802 847149811
    0x80906040c090209010c061109100f050901080c07150b041113260f0c01080a05090c0906031e070302031c020a02010813060509010516020d140304170d0903030b0105070209 75
    0x4001d80c03100c10944c01a506d003800b21100800160409000140e4850100b019048041d801c9a011590440e00c1c9420744112007c000b1100004104000c1f101c4194004d080340c640013603c0480c401c1c0b5200b041d803140c0b150703503011084e9484d5064a5680035107052415000780c203001500300c0b450916103c10907007401211491f034407030103070b58030300d4603040c0d080140c840d206441a201c0b0704802d079206100102d004540310040320022074045000c080204a05d815a031003030714400c4036110f005020491550301080403072003005003020b6140c4280211031240c1c0e103048910700007149105000300a0f0a042d403041504100d0821502041002c5288019040c568002034220302c4640a003030200003900c0340094101e03c10104007014050034205010700912140560240d489154402591300395020007140482c4c0302c013100740e5008000740b800903d9440181a007001943c01a20072504d2070040e880c28103000d0305075041507044140742651039248406054143c0601d511501c0246820307490301080c0c0d030000c0c1c0c21090150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 847152302 1250 847151052 847151069
    0x204060b0c1015080d0c0c0605031909080c1e060a290d060c05070c08160e0c13030b0a0e0d0c080a02120301180b060708072d0f03080906040c 62
    0x340c10042d41c3c1001014400513042c90f4040e41c84a2807009030203030551048a00c22102d01107221000521070303105400f43c0b4080c0c2d402c01c5021914400641c4000702422000b00c064401d50742c10007407a20714086c100018981d040d20142c62002c140710341d800e17041c00c082c8014144241d07181401a0103441744800354201031200c080da4484403112581d000464450450310800408031490150b888080640010107065454420402005d629403106601904e5444a054a0b9001044c246050040c0c001c41102c00f6442141c801401d820205000304808517412541c0c02512003001000901a10020a0181050111010005142328100c0b0b200007004200c03c0c1a0180c010b040c04200706200310710a0248401040700c40307001030713101d507110306032940020200466800c205180c403940c6042e50030f041c0d0540e041a504036403c141046401d03150b01840307545c024440c0d0000310f1030105105c80c1c3c45903016031414986c01040020717011041841e001d840004050000c0520350b000f50304010004044003c400141d50990 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 847153552 1250 847152302 847152311
    0x614010c020d0c05041a03010513030801261608120301080d26010f050103140103110603090a0c080a06141003030f0e0301020301080319090605030609190203090601030204060b0c10 79
    0xc0c14030391411801c3c1d4000e180e000c1d0030a80c00f4207468000320400b03510501e04034020845902c5810b10402c2c2d04041038002400702e11f400d801004562961808412840581e000c003242450003d00d501d818402d00000e5409000f135030000600401401b0030110368071403400c030002407455041c001d415550340030300c408030380400981403984503514400800000c1c01a004804116141d40c4511500142590074050346000901c1d00000b41c80c0f950342c04038110b0482c2e4120b500110804c400c0424031481d0740c40107015554030301c542c191440c0022041c3d082d0303c3c0200303c0c02028014540040ca8180c0a40c0c10341c01c00d131a600e8880030b061059071a404800002100d034142003264071320301035072019100d50000c003046039859440800001a106000300c02040503e5501c02c00d001111007958040e10060880d000d00d8001440c10710000f00c550a220200c00c2e0042005c000740c1070f0000c15026000142c6e0700445007a2050b07000303a0010000c500b460b00407440a052155042c6081844405015540b00500d01c100d250300d503200c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 847154802 1250 847153552 847153579
    0x50a18020a050c1b01020d2102030907082e1a190f06020c13060e073b090f150108040c0e100806240d060f020318010614010c02 56
    0x228200d4410155140581d100154441c0c084140b64003d008a42d0241c059410381207c481c0c4108001c2810000404c807005044905032a0100207420060940c0082e1190301d0300461078500400c1843c1128001c141d10a00010300340c901814200740350ba00401d032003030801c1d260101c0d191800d81b141c10128015100314044030b0005040d141d0b2558140d0103042241c0c00550003041c2c082e400701c4c00b000700c01c0d07003070fa007410b080e003400007030f10045507041d2050307070b80b40041503000c154910b1260200720b054803100002c00c020380c40011452460850380d9664403103071840b0f00d4030441c21405c0c180c20055120340240c082c00c1141c5420b150a02c00d80b4416030a503810000c0d00000a000c11441c200c2c3c0d140030703207103e842d080500d00d40610101003401c000c3c080e000382ca00c140c4d40082d01c1d00c0c0c03050300c00b444900c002000e4414a0210300b018007030181c000c20b0b412180e55440da00c21a14180310351001d07522420204410003040e6141000c460f08441c0280c021032054000c0000c04d8a2036600040450764130381c0e043e01d82d9080601d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 847156052 1250 847154802 847154807
    0x1e05010927063b0f060105070503131401030e01060e18070b07030c020307150e01030e010b0325050102190b07090806070c03030c08070c06020a0c05030408010204030309050a18020a 79
    0x42c0c80d0000e401c4850049039038442480c03078529145040300340444030030341c001d409003420103030000849140d84459110070000d6150f500c01d10190050307610a8003281c0c00c00d118420218662512038020018804071052144a50341e858007030f60003420b141c02c008000d01414022050001c0d0401007020010030980041c400e6400700c2003006000501c0003450341505c0b844079150080103070740d417804140d20034801c000c00422050200d07100207070341981030340341c0c40752111001c0d00540260000003d008407556075505031541a89061144800359102507103144024071140d444080750400d036820045c11035104d15407000a140000070004140b43e00070185549596030710b18200c4070200150007500042c0100011b0048640e000111a00030030322a44017440b540420b00e00864036810708444690006042c1c1c3c1c0c00394040f8071580e000f440d258119140190124103503880380e40c9154031650048000760340c0000c040007070643c40807038070700a010212060700d005071904180000c40314401454154250340010f4103942d1a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 847157302 1250 847156052 847156061
    0xb150c0c0f190902120c0f090915030a0f021003150302040b0f030a2d0302100914031209010c0201060501020a08030702071706191104060311040b041e05010927 70
    0x12074182e044240794841940c44040d400803040419042540c8021400001d034030301c00d890045180219050a0035402002c10030344403405450110468100072410000781c40c18450700917000e005181c5000d200410b4414031004000d4041d0480405181200e80c0e808020544080c4040ba601210042403046640001890030f545804c40b0760360601c1140c4c2c50004200d144a0b01002003c600c084170089015540491090303c542190010016001203800b00e5090b900c0d940300d17128007030094841c0480a00c910303003a649103030300c64183d030b404500c0c0e95810042d402c50240107524485c0d134180700a00600e8a0407001070b60303c3d900544010301880c0d0100008440c5442000032800409901046900913400340c01c203d44c8400041e05c441c21a4800401000e80c80303e07e030b028107e5101044020b4524151404408a00400080790407581e11a42008002081340c10080580301411108603542d040d102c051428070f280d081c0d143e0141d818071154070005c10020380184c510b0f20450350050a00310801005151a60052 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 847158552 1250 847157302 847157329
    0x151005010c050f0303010e09070902030c0f031807080109020306100305031b10060b09040510030c180b060a02011b14070b0a020d06082401120303020703021608010b150c0c0f 76
    0x14813002c400015801656500b141c0541448030544840688030502881640300403201104e01400c01c0080000c1440200001c56004c6216205120680700302141c4600300456581b0007003a81e074441405105610301803140a80100c041040205080d18543e1140e440b402441406490740c01c409041c043d0302101440b075030981605a000030071540b9282e40c04c980740350304044410350080345800c0000c0c01c510307000070300e860649410105016600340343c070300c40341c032076104240714ad0480315100c02c04c0300e44c07913100e01014000b00c0c1440e030004282e5001c40c00280d448100384803051400c0140d1000b1703186956400340111400145c002d0f0110703108d5607851000c20042e11030300e158926502d00d07140d0300048500b0042079490081184003461448078140400251580c135083c001c00350712030400c2d26150f0000380264001c103001e078842d0040c0d421504081c0d1103011801204d501812041e51222569600da10303151035010400c4041c603614074204200304502d542c0d905251000075006569028100216a46100400d8000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 847159802 1250 847158552 847158583
    0xc0c03130f09050f13170903120c010b0a03150b0a0e04140105061203120601090b040305010f06120803070809072d0605040303050a0e01180305030903151005010c05 72
    0x200c0c0d6031141e00c00240c80203881030b076254900d4203001c0b904440c0c4070098280165132200d080c1540e4051a00c0760110700c03a0038010070440d400200100306d410b03107040c45049024004450500c1e00c400d00f07110414252280030199900c43c545070301007400003039080b0201c003104520010740001c41ca100c440103d240348000d03410001c050b40e8030380104003c002c00c1460b200c1910345250002c0c05039490312411b110340c001c03135602c001e8400c0e0414095125800ca03400e0150794440c40501d054005d5980c1c030765500300654400d0304140e501d6511910162800321450060310000c091500c0e01006005c981c0c3c035440c0b4140000740100c0200a01c1001140f24040d0400040c005001368600002c85121303104081880001c05400a240d8104001e000050260286090305c044a8241d12210300d060860441141c0f80d00080310101d040c001406458488040c200d815071001e103200d4801103a441281404140c9030003014000610b5a240a100308080c04881685e5038003200c90a0a1200e00b41002e4a806824215500e81c103118 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 847161052 1250 847159802 847159837
    0x1090807081606090f050c01090f05010815210615010c0b0a061a0927041b03050d030c18080c012303070206100b0c0c3106090f02120c0c03 61
    0x91101c0d0002e05c08800307205908585507411040c0055402041d03600c1107800042050300100425401a00150362168802c0e00010752800e60740b00042c0c00c402540480307844e15280d001100028034041002d02c2c1c1003030142022051a58544000a00303601d0304c941c006180320b84150100d00700090300c1d0000c50213041600d488401282119032442d41e55005034810354850114070011443d884040c010b00203920741d00165100322517986490b22100e4544450140303018a040c94800000700c1d005003e000c40f90343c010394000c0745400440314028404005042c01c1002902c0f9800200a4010b000510082e0100700b8244005000c81c4000c10350328072054070103111030000340041009541a03000c03031840d124800e4180c8049040e9228a00300085014500700340c19a80c3c084000d40646240c14048103400c51042d440107442001c0c2005802c20340c180202c4c403803000c183ca410017131214000a0082a000054054085003071004603d080403419602404505d1154000a00007003059002d01c111041885000c8081c0d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 847162302 1250 847161052 847161071
    0x3270b1809041b0b030f040b040f1401020304141c030c0507140606030114190b1f0f030c031103060f061b0703020f040608150903041503050103120201090807081606 72
    0x46034800f9449864240c000c24000c046492001c080581e0b000b84080100d00c610365135107540300410180003900070307916800b12024440010700c0106031514451b04102c00580c480c10301e0300c0c0400d02401406000b41d240e4002a0f2415031502c00504400403070501d5180116030404203a409442e01e10030500b000e09201d0701c031082018640400145503008002c154000c100b4441c82000b20700030303a50103407101c0170f250220f00101d000081c4180c0100001c460004c000b45031041551100003074200608500310041140e00349a0104150144a4490440d10070308041c0901d500c2007400e09071078030004140c284641c0d4501a1442251039210a481d19501c0d01e07040700c901e1942c611a01c0d80d950100f0b00c8101e00c82d48903010503403c6400e041c0901c1c000c440d103642c000c2c02c00e800c8444488050800080000d2074521003408006010615100f001484a900da20000380950441c00e040210141030b20031401560b0402c1500000502c2d03013003c413010300342c2041e80f0503150b000079145202c00000c01d0b080507080504006400c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 847163552 1250 847162302 847162313
    0xf03120f060e0609060a140102120d09031d0a030b1009090b01082401060309060b040f061802040605030708041b0e18120a05090303070f0b0403270b180904 68
    0x201c0a80d26a811030000c0c030b40d6a80100700e40700a003164078903041040502c00308011040c1c696018141c10301401502c0c80c3c0b10908194001a4000320415181181c450380781a06060b00515800405620715609401071105000480c00f480d031a03201c0200414990f200044800c020007070550064145010103002078900ca0034001c00d21b41b002c0c020503000303010700c90010b100112584840c05841d402500813105583c46d1071010340c0204142d6501761150741d100c0340300303191580d968404c0305003130907940d040080c0c21401c05080182c00c0030036010520000748100030901100da042000d47c1d41c00611480c100e007241d6614034203040050ba1619911982d202c1441d4041400c1c02c074600218418940043d0210211850031407950380c4580309585d0b244910010020501014800e1000702030058002d411240b80c0101661840c00000300700c40203a07015004102403008041c0c3c4061040c1952101d000340c004807200703800040c40b002c809031044290120700040c0c0844007441c5201041c1f020400148a840c96107000c3c10320 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 847164802 1250 847163552 847163561
    0x91008010e100501022d030307020d0912020a2705040804090606050f1605191208130c26030c210a1b21030605010e0a06020c06030c07020d1a0609010e040f03120f 71
    0x2000220b540d207900491310341001d43c4137840e1180c00801040000f0b2030082c0c1032070107150074540e00c0428805030400031103a4145016031401284142c240e41e5540d440c0c6086603040300d45642062003004000c110f8181c5a828440503155584034510070070410084c28130704140782255804080001c50341c80f0140500340450790151100801311a1904129a5aa401400c2584515010007400c0490000b03040c0680320198510303507210420003500c99428034401e24000c0c5144c001000703c48070b0b40c0c40041c600800a01d000c02450010942c1c100c20350400c0e090761000781c031034004c0345448168002d10b02d41010a20445c1e00f00c5149200d000f80c1407280e807441c2c2c0c07032006000c5c0c0b80b6400383c180410029407082006081001c01c2c00e08540d03440d8041d0681d12026000c2180c0c1d584049c2c400104604140401000351713455642c4800058400c070810394400c14044140340041c0307001041144111044070041098500d82c624407940b05a0141782100314400360315098520400b803000c10586030340b411448044039442c41e40b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 847166052 1250 847164802 847164823
    0xd06020301090b01050309100c0e0607060f0c05090a03030c0203010f1a010905220902240418140c03070908060108030403140c010f14091008010e100501022d03030702 73
    0x406103c0d8028490054600e03100944603071409a000741c8004024148590000c81442c1182c60800710211040c00000e0047e044100f06850076036407840000800040c903c079010700240d071360400504111043c000078a51001c40d20000c3c1c140a1191130341000c6650a40c007502408907a62410400f848496040c240001031410300140443e00c1c0e2500070a1a142100010002104241c050001c5000100c0244058887d050040b60045c001e504003105074001c0607443c80e012072407403087c1911030703103802c1c0c1c0052011941c1344618261031a28400c1200c200800d0122a4080290316100e6600d0701c655100b240ca40015602100e4140501c0c0700100b0040d1021006100700c074001c40c2602c50a012801001d0344512a21200a002c1003074a80820090ba003d05940d00f01417901c402e0550601500c00301103100d5012070b002da500020b802200521014091000258106c07130390010900d00641000c0020391f41d41a06030205001072005119803d003505100c90104880c080324003501e8403801c200d440a5a20038031982d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 847167302 1250 847166052 847166069
    0x120403080c0f0c130b01090308040308090112020a0c2306161d28080105070201020a110c09040213110d09110111120d0605120705010e010c1a0a09020d06020301 70
    0x2205001c1c1400c0096101c5501d14010310520307001d040c0460020041000031700980c140718641c3d0001002c1142080500015409a0802d5544607990000107020340304801d03001112910601461402d240d00159078080b40713a22014044280300d08102088410012000001032072180c0020008409400c100120501c0380d20340b502d9981c000301c05884011400d10481c0c494000070310000c3d020360030308076552211a240d00540301d40000b0f920f44082609448049401c040944c0d00003800c200c01c0c0d6402808088070041f40c10143c00602d41e9400060150318000d00040d2056017480001d10060406078000e21242c19007110442c2e4a055001050b005440010310503290b980c00c66481d0308181d401440c2808419420801900801c2c50500312114240c2041c0308210f215a03a4810101d0280c44040303480c0c02408000b40281501803900000503c0e2184011601e030411070014113010000f100700c610340702449110840c08400fa5103a107200002041448800382d440120300c09868203000903580218166203021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 847168552 1250 847167302 847167313
    0xd020a0e030d051804020307170f060a05040c08070e2b02180c190903060606050c010c0e0a2c040305030a060b0a0c060b2206260304051002120403080c 66
    0x103032056600d070256080c1c00d806804c00481028083c0740075401107a001141c0d00f050800d843c50300b095042081000c9840c040d486842c0010300c0000c6ca0315807190001403904803411311458812990040803079501410741e2040c0110a03d500c032850307135075074044406400c2d000350121151004406a0525031030340f120a03405030034115540c0303400380e40e070302c4030180b040e8103802d0300c0c9191110b066140a40d007098410904100128881c0200003d901406940c2c001c0056940d0281c43d02c0c141c05540b421254042050014020207a0034241549c8500851408030f803154014078090300c00411843e44030000d0016900110002081080100354000c40658000c014000c400c10460343c440d5005280ea06c2500703c01c4001c19102410a0300040c6607400142c480380f406081c0c20f011003901c120088850322100f80d1103600c5511580c05009007081501c1c41940b250141c865000c2c0d203010110415220701c614090385024032510901640e9113070007041010002003180b5042ca40d29652414481076070380010358080f40c1400761 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 847169802 1250 847168552 847168573
    0x50a082208011406060a030e0105010f0303030c030b030c060906120901090302070807030309120203010b04050c0c010e0a0210051b100917030f010e06011709150f040b07140d020a0e03 80
    0x14802e003040300c410f610310007419440311410031071150014615502016221010040f8140086c01403070300030b10042440590150544c0f07406000e640c000003051082603d001d503544026070700012044100f01069034100e59501060b80800c00c00c8c07140032918082c0641c40740c03d10590903015480240400d00070b03429214400d803070b003070400d440d0b5446200107000a9071034407040c450120740d089140b80e2144014000104400400e000c01d0903600c0480b503013002c505000c100c0c603100d004203010b01400c1141c1100681460040d40d40044c1030701e02c00320701c990200400841c900340103620424070034007a894448122010421103041c0000549820442160140107480345010040f03180c1d01076a01940204c901d141d071582c240301c0b0782d0305500c4000340820f0400c1209072519031110f001c41d41d014000e030403030030207000d0182c0c600b001800e051601510a0040070070f40c00410003c1081c98032102c1e0054078a261803007079540c0c041c9822450740a00038402c0091b0340700189410b28290019802801e011003903084d0b0706000340c0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 847171052 1250 847169802 847169819
    0x21c1406091c05040302030a110910061d04020c06010e0601140307081503070504021317030301050102030d0513120302130501030506030a0b04060908042c070504030f050a0822 77
    0x1401e031401910340c1d112544140000da0035111400c00807100d4548207041075503d4000925100d121a41a240700390000102c4029042501506910132610f074410300c80c3d14500000101210808544005140b41c4810210742c80d565940484415041203c1260110758640a1000300c0c0d6400b03070390950210760720316918080c8118002c00c1c1c0b4070659480d1600400b40da14050f012841e80c000c03c060300d50600404c00701240e00e60b518405498960b4030020b00380701e242d007800c0c000709141c0780410002c4155441840100700584c0e0000c11650200d06420000c911502c0e1204001e030300c0a140c0800a05000718915540e1380c41e603040e40602102c0ca407619480700001d6455005400710340b070a6800c690141c110b00c086401044840b064540c101c0d22800e40000c0310199a2120882c981198001c40f001c912140c80707800d24090082049134001d20b0604125503582001d4801800c01d1145100c0108581000400d0900780141404000d1601e6044450b09a03120b5241440359460803281c0800c1c6001d004040c000300340460b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 847172302 1250 847171052 847171063
    0x82a18090d03180c0e09211e07050309130905070b03090c100905040903110303130b07030c09090b01020307020d032006090703080c0f070305030702040b04091703070507021c14 77
    0x284c002090804450504403c804215801048154244900b07142803100815052042c42203a8204aa85803901003e00142401031080404011041003d00000010400100840740c505008032250741c032961003070221401402d034646c0003030302c01c0c011858002440b04c40f000055100b010014107031080d00d201c103030411181000620092000441003e820310041c00c281d27103c2c46045010b420000070107010400c0080ca5544101d6040020845070300b00e18081089104009401c054182028450307051300c3c0d0700003041181139100b00b600c03060320340440c145143d00038801c071010980c001d00000003640c000e00707000e4070800c4260801c0686010200251814100104150b030003508060042e1800c02e195031248a00c0d030b00420380c00b00250007100800741e0780160400500c0f005500c02c0b03000d1070300c07540e06004001c02c03100300c41745650080e130404004000050803005803001c40490820400e40301d49401500315014020014025000850051401c1280314103040b1b10b544144640000800341208100503904e42 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 847173552 1250 847172302 847172351
    0x109050418060b0a0509160f050c210d0203070804150605030a020402090a0f061d100e01081512010e0105250804050c130213082a18090d03 61
    0x403046803000c1e600084082e0082c80c0e824900800f020300d00d03611000001c00c13400003640c01c00703800607510845580042e00030301c00500c1c0f00424144203050558a03c6015110010a10350041c1003040280c5500c4003030881095810040005100710744a24000340082c01030ce0301510107650f1200d00841c1e4020104150003560141c031000340140c048640c0b15400d0002a4002d0903a440d8440115607021800854025041000300120354034403902d010301e00308044040610703420362800781000528500c203094102c4034400105800b0318107074480395210000b503c0d0780c8180c0b81815074441041c01e000180c20505400000c024480d0304020091625203213048412000c0c61804d225640401440c0c2c6000540280c202c3c070740c89070142e425101070120410008000080345411054441e50118120340051801008980a84002d00050615840e549061a80052030607400c1c1c90045060801007802c0c1c56914818240c000404c0128a85062a0814945074100c0c12180c41c0003e02e00800c280344d404486610343c129 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 847174802 1250 847173552 847173581
    0x60204170c220911030105160e010801031a040c0b0310080601080d0c02091e10090b0a0308190e0301020a03020403030f05040b1c090506040605062106070c0c09021801090504 76
    0x30815501c040c0001d096031110688101104180e11220f5440c07c1c0500e5100d1102140005104110002d0207007a841c10700100070304000c41f0b20018000180c200d05c5400c03141d8150000c40c49241d5640c5004000c2042c10b0b0040c0081c0000401801030800c00344c9402c1c416582810142c0f03400f680c07502c07107899940c0007a000040000e1540241140941060941e09400181c5001300d04085a5441c682c4200b680041e50034410408401c0380c204569000d510a4545c800004c0384c20300c0d41280b85481d40d040d00cac080c00f081c211040b100d44407181c07030407402181310742249040074009544034012444041c009401510041d03000c00c0c08180d040220a00c2001100c0550345070b8092a03040140701c2e0070080b003504003510703088000750355590f109012036002c01111f032080380b2908011038141362400a016404207503141203e1488904105401521008201c0941c070211910703046140c03c6480c1459403910f05998440b02000e4400a800190500483c0041000500030380322101c4082d0f070b0f40c0034042110401548880c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 847176052 1250 847174802 847174849
    0x70303050d061e051c2009060603040b0712150b19050415050a0507060222172112070206060a1202030303040b0403030e070602062202010c0b070c060204170c 69
    0x398030300b030031070821044178240d103415016155540c0c1c3c403081002c10042c1004500e43c1c40301c0f49110320380700031800d6000b5000d0b1219421400c259541040c0303020041d1181c0c052004401140c007203e841d80d4070600603d5001c0c03801e443e500d9915000080f041e0302811101c0d0311070300c4808904120034028030855044500c0005840030b601d80415045a080d0080380c3c0a20400904001e0700e070104803980040e00114522001e00c0e12088070302d4204800030b40c11944500b030800c104c0414441017020114825203141003a07911202d5082180307c62600d41e00c258000217102481840038001c0c12540094246e125120642d0281902901c456200c09900d40e00d81d0b0003581070f8010030020b00020003405480f0380041c80b0381030115402d4848100c003410302c400c0745c202d0700040c0d01c49010050002985900c00d9002e04241005009920140e00020050fa100e4040a80344000810116031140c1c410110b40300d4461300000704644a544400350b0354041090b00107502060700c220034201200c1e18100c03080c1140051258844c2c0e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 847177302 1250 847176052 847176059
    0x806041205130e0108300d2a0903120804080d0b03010b04021b15010506120705090d0605060f0109140d0f02060c03041806030308040809030a05070303050d061e 70
    0x1296640114040160340160030400510110b002840a018005045c003401e03c030b00340d400342e080103900700b0b4140220541504590700081c04024013140d0640c9507154001c00c2c0c000c6444140e88541ca041c01050034a403440140751030407240d0100c1401d05a0f80304a0080089000d04441103558103030541d000f6007004000c1103142c1c41d0380219071042410380700280010950024102c001012600328500f100140140080c54076820501444440d102040d410443c030702a506140100f03a0500130042c540381c030820224080b840c2c40707010300c0503200e200c54000c09030680e94000380743c4400541801e80300c090207040c0000ca5082c1a40c041d03c0f071035082ea483c000018803445d05441c00c100d400e07041d03a11b080d00e039200700c003013890096150f8000a00004807400011035846280c0700484c9003032091240707510708092410a05000080d800b5402e582c104d900800501d4a50030480002410701c0307051400100a0b20032650000100760b0400c01070800340914200070040151b85402a0103004848203014400341d030031001c00e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 847178552 1250 847177302 847177307
    0x160221030916090e070503120f2a0c01030f0212160509060c06100f08193008100e0c1605030c0609011a06071104021608030a0608060412 60
    0x440e48a034400d4202c0d5040310b100c21000c19144160340080310000d40303444070613014200c2040b03003170000c0000703900400c039614400b003180b48a8001c0240094502c0000908245841345801c03a000c20032648001d200000c880480015a0f2450358080450220703040c012002c407071901038070a80e0048800000580401c3d5205245100380d54000522602804000e009184040d20340b01d01900c0c0d0b03892000d0040c54241802403001c1181c030300f5039201100b483c21141c41400340c560003003401c6030207802710303002100308201c1031900414176103aa60001440b0100d1000400c007d615041c1040c0080303440740c4461400da21000443e88501030301e4000e60189901d2600400c04240d1400010013040441d2091030444070840d0362468215071000610096680c00001804110745007882242249a0742d04090040b540c080c4000c07401c140500d0501400c4140148206040c5407560f804640e43c07a44100090303000c200e440d1620302c2c069041514014a400d1503c8008500b049001600f00d000c2c0e83c0000d480305482c0440d0004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 847179802 1250 847178552 847178557
    0x3031c0b0627010207080d05090a1e0e09101404020f091b07051924141609080106060201140916050d0501060503062521020c03070209040605160221 65
    0x140d8114480c0a10004071b800c03090224003105003a50352859681e61101e01002078080d10b94010010640200c0991241000481268000c88255102001841c4d442008113405e020300c0c0c4003200300c5d680c02d0403148c000c81c1602c4840144594070803500b40e80940e0400050010800c0c08a0b18208a400c1c00c030104426090702c3c001800940d40720780c040f01c001015154080349400407002e42152083d00800c58000700c060840d1289142882e04801004103038121032945400030800b82c2030390701c2c172a03242d804411411b10a4180c41c0103064150020300003181d031054000d0007044134841c0c1c0f011070326041c00030604001003c0f42c0105039603030145011010906210810005108840c400c5800790358070240020b85882c2800028800c101070a1030907245800c81c1d50204074010b103050842c04200100c1c078200b8100110380c0c0111001c90500000507103958078104070324518070682001950000e000f41c100020003000c1e4021500c11030600041d80000451988166070ba9a6503124412440c81c41c02504071008080c1d402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 847181052 1250 847179802 847179877
    0x30b0f01062304030f0c080607020105090606010e130c0f0f020309030d0e0d0507030308010603110a1d0301240602011805070b0d0204090e060601180302010e040f0b03031c0b06 77
    0xb0310914090f603a60380e130150741d403d500d811100289a52420007240c40103000301a0b00440c0341c0001d10070340c9007400d4441e40301c40d0020032035030502036182140640f5465441d06148440711025080100502e8081c0140c000e00b9862810000960b40ca09450606032000c400e0b141d1440000d401003103403039030700041a1403103071030072000c513030000501401e10010a208000c50401540241c903813003134a5041c000028140c92012200545413042040141c078244ea00a9651104010420038074109070700f5840000d0141c40422841c0c0b9004440240c41c800740c0d01031a1800e03046582e6078000f08100e01600050481114207040c0103405034001c003204122610040c1d000700070483e030030b04005192549450403082100e01c4999045903903070045042128550b0021403141c014003116006190691450740000c040714907401001e4041e6464039032290001c00950000c03800000024152078030743c0d06000018810000750b801003840241000513031402c0d810044c2c00c90722900902c0c00c00556a1086c00046035092000f4030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 847182302 1250 847181052 847181117
    0x105061e090d02030715021203010503060415110403030e12060405030d05101a071401060506090d080702030105010b0a0215060d08130f14091006050a0c062004030b0f0106 75
    0x110b020340140d40503c02d010142580070301400120614510003490100c0e0301141c8090002c0810051100390303000a9801c0e841944645082200040600c842010704101c0c004404a660003181c0030041640160400321841400d85246030150195000142c4d20380d0295400340c6960400c1000c1307400c00e90f06810469020220101c064205584c0c1c2a08600c84100d40021042e20311000c91541c080080c5d03225400700c0015040001d1084504110000d8074038813442a000d40710b00035001c2e00008202103001074a104680080080241351b9690290307203035580c050030300240140078881c003400c2d21403000e4000300d01428020703142191554140d601c48407564000c011890000c5030010700000c54810005540c000340840110300320749640c0c0c440a11076080c07405001650300182719801442100d0b03000c4160740c680d02da5071a000d90003207141c0c00d000c401407000180000b000f443c0400c0958a04100c0b00092007180e2242d507413500c01d80e48013100c007810341000307001c0e04000802085002000c80104094401c0702650350 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 847183552 1250 847182302 847182319
    0x932010e0606180c13030605010e061005030c070c1703090102150f0121170c190809011b1515060f090504021321051c09030b040c05120c090105061e09 66
    0x1883e1820108a1750b84103d0301e0036110301c010b1080310071070195a500008141c1e050b0b1070006409101a040e4080100071040c1240003044240c1842100d0304200b009205506407186007401d14482c6c1a240c1c3d0091100a01507c1841d201c0000c001c45061914401c0300010001c0440d40d01740450b01035907601141200c03428114188440c00460b0340c01d901c00e03207803001101d4116651901000614109540036804801d5800c0040c20400030880c42ca0480d1a14a02464403100c4104040103100710b82300c03400e030003810400102c0800e1011a0a551180406810510034202082d640d51022500001781c80c00c0b02000400d1042d0402c86c9040c00e8000d01185446003441040c010f803100c40d400c0c034070030000e50442c0009590480000c14010103115901680503c0c50b074200382d00008070006089900c1a20009050704a02c0000509000d91000ca41002d4440105020280301060400d243d561040c0702010303202c1d903281f100016461402c88101c840d001840c03554502c03540138004c91700300302d900840c41032900408075 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 847184802 1250 847183552 847183567
    0x612020f0a02060f130302030904050a0608100203060f0f131a10092d031205070b010e0406050a0c0e0409172803020a0c060932010e0606180c 62
    0xc10050101c0c151a540109804d10b4030801040c10f4600281c403002080c0081d420745008030f9404000c41d0000801030306c1c003143c15214001101c00402e01c950005045000305035a204110585030011801014100c801c504078132031210401000c8070102c0100307a0700c801020303d00c01001c05580c000070b03a044035298078008100301c0c02001c60b801d4a4110b41410014208600174001c1da045883c0c4504445a5020f8160320000010300b04e00c0f100d80f203404007070003940e28050704d01d0b0407522500c2160003a43d0f2000d00e0322925692903041c50a840010b503022941c6508010000c2d1807041103202d400b40c0e84080d42e07203800030b41040b04240801018588810b4554881054400d40c20341546401024003e411001808100d100d00349d480c62005086040681054010441120b0050740441c04500701c580002e00000c45460314a001e2030110701c001c403641303200d40002c081500b0b0202c1850401d00a034101c1c0c40244040c010549095440d03000407244241c0c0305414100807a500300c15900c910ba44189020142440c20a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 847186052 1250 847184802 847184827
    0x6030f0a0f0f020d150e040f06021c0522110d0f02030d0804020a061409130f05040809030d02300408030c0714010203070f0311070308130302180f01061202 68
    0x10b01e21501c0c0e02c207600010031007010300303c03031007035000c1401c1c0342d581c0c4504c0300d04041701d600460b800604050180800c5244050502006504031141860005020400008070140f25000781500b104c0044610758098a60941b0941c110800d1100340c0d8050386184103040904204030301180c86010540d64400c10700c50010040c1c408103e84a514141c0b52162070152602c0c2c4104041403100c1c0e00413208000b03050319001f1184401000340c424000301268000d03040a4514084001085401d046000c00c500306024002841510710041c403220100303a0980c1d01c50758000d081641d03554584001c551000c98a044a40c01707003414000b41c210381e0080741100b98642951141e6a078550b41103001d0b200c0058002c1c4c101040b00e142c40c0141981441e800380003842c00c042d00b80e04e40341c00200310309a0245c244196078420300b180c858103000420203160301030213003601d0307001031030018604420741c0c0400c03405100ea0200c00301c00c1080c000345c20b62255204041035041c1340c0c00c00d00d040700e80e546031000900c040382e000e001c4070a0401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 847187302 1250 847186052 847186061
    0x2a0e010902090a050d1203020702060d2f041a0706060b0d020309070f080c09060f0d030c050d1b030c02041404050c0307210303110f0f220506030f0a0f 66
    0x1032462009a107650801c000c10007040e20a52085100b00d143c501d42030001041d0940100c6800e199060050316a00c0a00100d8814400d884030701080790700d01055104105840711102d803486500c415005442c41180100c420540b245006514031001c410114030002d951040007060543d114180200341e0301c0d42c541201c1110b030071001e424804650040200220480c5c10013480c0001c0c41c00a5081c400c0c0e902d1b001e021615200507820990190121900053f9030b030b01c4020b9805110000a81240c0d254481428002c00130003075543c0460311802200c0108070103e100c0c0c01c02003991040c0320f01c40c1c0020b10140d542690315031030300d8204907002501c50f240300e90090003003a0691311850051004e08007038103002c0101428034206030000300364803010a02211000c0000010307035a2060f0f01d42800200b01c000d080454142d0f001d030100b14014070f040000c00c030700c40b100408054580345502601a100842c8035050a41138000709000721600303c0010700010706030720600d85006402405070000003440c1d14540c41400e0588 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 847188552 1250 847187302 847187309
    0x1050f1b0f2104111f03020c0a140a0303140c04062a03050903150c04090f0207140106150806090712090210090501120203060616021f080708132a0e01 66
    0x51140701c0400003402180c0c60b41c1c1c01800d81c115685c1c41e00c401c004680141c0d0b0320a26001400301070740495000c26201c010884001c0c41c907041861072981e0000e8450107aa00c010f44c80781100060700b0308031030389103070351345002400d0040050080ca00c0c03e150800c901201c10200e0040d06000301d0000e00f0180c0c5c1d050b0b500701e00300c40c0103a0081c0d641580e01d14820050500d09010050203803682d0103204104201104401c0c1602e060710241c100105900782d440c04901d02034010b20300c020b0a8403030240e18a010170181580610204c4504040b140b07842e0035a100c0940324010201c400b5038212100000158107903205004500e0700081c4614002030b0b8500da600402d105000540704640410009079080c041980c0254520b91180e11800d415031a5140c5039000c20820f006030070072000c5480b04200480b0465441c0101c0e280c52801c010400070154401003001800c00c00300740c815801095580300032400145c0c5089090f00074076000300c4156541542d5400084001d058840b46850304480380c64007203418440d80340707194000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 847189802 1250 847188552 847188607
    0x91c0503070917210702030303010b031e22240f05010902270d020d1a060f010e19050409140f0a05100906020409020a020f01050f1b0f 59
    0xea262500000c0c0404000ba0406800400d404141d010100800904400044030a108961a001090390380c00124010810f009505000100c00800c80c103102401451203001c6290800c00d260814103060b411224096441100d62101c20b070003003982d1448503003000440c40c8922900900d070300d1559000d144203611002e4100b03826440d4002c00b005c0340d03124041c860141c031401c1c800314505561106054222050400d06160300192031213600d030f01e0303541c8141c0031990a070090200c07901c942c01d505d06a40e5602485c1a805800651040410241e00702014410212001070b11201c5403902038804001c50305503003040041c1d991581282c00b00f200e480314040c1e800c00601c80c44400404485c102411801d011209822640035801102c1c1c1e20041040020340c3c407148044000001200c98017401c0480180c4100e400402c0843d00000e102890258001880d00d4880c1a41c0007c01160703c441519034545541030300d0307903d15096581c09800700c2034003620051400300703000319190380303069007410395400142d54105c0a07015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 847191052 1250 847189802 847189807
    0x1302030c0a1701050a0e09010e060903070b070903022b060e030702010311071a0a020408030406080717040b060f030a0209070e010f050301030c060305061c05210702031203091c05 78
    0x81d1076402455402d1889a80c100c9a03200f5070402d070100f085001c0520a8520454012001c1240d202080d1301c285000c1103104140e421b2841c1681d00c1035900e078071860003145c1c2d540350344c00062581d503c1000000160783d070040c5003045401d440c600c1030051900038800c09040325080c0407140d000a840d44100308002c0043c001039a01d808160001500b103524446040d088810100151000200e480480c04406000c00c40480d00c1501c075450a0b00003406150007030001d0b8440050f010404a4001c04400c0c801e00c100c0d80d40503050070203031000c5040c000094030300800704411340010031030901c0c200c0c58458800d074000e41141e1030788080390002130044809681910102d5100c1c00c0c244a10350788030007404584000760610307900d19499640c80c40c5298a062185404056888000c55416907a0500b00080ca445245800302005031504084d5160b40d1881c01040c1c0126414032034140520f00d0304252160140c00401a1481680308640f0700102c2d4070040440c40240034000000b011821038050001007482950b0b1420f4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 847192302 1250 847191052 847191067
    0x10204081f2c0c0603010b03160c0c0803070c0b0a0e31020c0d080403080f100504090c0e0109060513091b0314100506240c0706020a1203020c07030609021302030c 71
    0x900f0868603003a180c1c01014100014041008958201c9400030740d2180d107416071542026088030040d4079580000c0003190b05103030008444500102410045020713440052505070780d9000004c3c0c5216041e100740100e641c0041c2e40080b807520241841c01c424031080d01cac00c600301d082000c8001700380e000d0000d0401d2030b42c08035480e8490f003010040c0d01d032120560f082c05007060030191000f4101c10070050508900c103007a0000204c030010503c54bc003006150192003845076400c1803070000c030200303ea80181c03299807598000010b01811345001e61030440c3e1014080001041240092002414410a0951f1041540703040c0d00311407002c40c85404010340c007a85031940071403c81c0c50034900b800460f003441c801190600c0148070032035545012503040c4155950403c0180c0030207540d04000c50082606450050003100c0c1d0000300c0311380228140d4000c0d4811510303c10304903074144050b0100d0184802a00346603200420510000d0781c1684410a024001440c41c8640c40c85c5424180690340200c804520300000800d448 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 847193552 1250 847192302 847192391
    0x90e011a04060b030f07211d0624060f070305040e0106260601020a080315030f010204060206071d030303240901031709130507090f0602010204081f 65
    0x14280928100e50600849250800070711860001800a1344a10004000316100c4d901408646e0722124100b03402105101f4181350181c01010000600ba2125180d1000394131440804107800e0301c138401640003605810f5441e40b040000302c481e86445908004100b10044d10790341c00340051f0030040c0c425940c03a41d90b2400d240300410031910607406107050004200c12251004850784004240c2000810040420750ba203000403840c16240c1000070f480003000105021060b03820105d580d41c0c109040d4105e86032540500a070310b080388620311899005800201c081074050348980300c59231038262007600b4081d650106600103420350344251903441c04500c25014400a81c1d00103550128018800c86032419903624644403900c0c9a02000b0411a200b0303c0014808000d0780c032882010045035285c4020402d51904140c06000307039203a8041c000d51040300800000d0744a1050007214160784181c1c02500f0700d20121020307001c1d0403246100f00701c0815203e01c41c05400c003140c1400101405680c80f205000220f041964 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 847194802 1250 847193552 847193591
    0x7120c090f170d021f09020303070c030803180a0c1203020f010608060f01081908030c0c1b093102011e0e01110120070f0b0103061a0d02030d110304090e01 68
    0x12a015034110b10f03640705c030240188107640001d50311070602103186038030740c40064114820940002d04001c3e1503440802400084c0d00550f1060540c24001d070030452060040c91307600d400d82d0703a0040880304d081506000307071510034500401807031007801280c1041003c4500103094440a40181980758443c00400014540340032440d8010131a0720040d0800450445181000c1c0e800c01d41d018100d00000004a011002d0840442d00c020481d0400e4900380c401c040c0d48846501c2e8044c0140e44501c034158007040c589804103501c2c00e00f540c0306a03502a011039986640c0b407004501c48405a061061580d1385400d400080009903046003078a83d1225840c15400001401c10b4040c10482d40484c2c2c509081c542e075407540c0c6000c10241c1c04521500a841d4a07181c87d0401140c02407c10042c0504042c9000004000071904456000502103030f4541c40d000e00401442644500440c4c082d40c190b11044d988882d090050038044800b10602050743d04e807907115240300013520101885010940c0d03640141c00d000c03a10043c1c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 847196052 1250 847194802 847194823
    0xb070b060f10122a020303010801050105061c0b010224070909020a0f03150312020307030912030f0e0a150f09081606050d020c010f0b031507120c090f17 67
    0x1c8509003000d12001c001c0c030f50440c1d00000c035038490b40c03201110400382d880340c00b40d42203003180c540710b2510700700072140203459070020f10840565609140c00441c076440c00c07900b0f452000400c0705030b941d80407030540b150002070041000c8603415401058100140480d042031a08022504001030301184e007000b000040c4001d03040d9025030000d91040c0303c000030059120351401000002480d0100f20400580d00c04824042035600003007405c61013040072108a070300400500b80d46402500c034100c840750303514501c810b0f0035107481c00100002c0c68036500050031806824035001c1580050015000c685c1c941c02021402c4003001000030109000f0b680c080e130a1580655400007a14203080a004048950070a103402030407540249000c2c0032021403460f0144c4510340c11380740794078032280c020310041600c0c542444c0200184001d031400303402102e0400612078600c01c6054002c4d4550380c4d4000740c3d601f80071400c40042c403521082c58100091b910740000c90000030741040d80a0302c200090381044550406a030740c5004141071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 847197302 1250 847196052 847196059
    0x603021002011a010e2215090b030705100c0b091c0c0506010501051b0106060306140d03091403010204050303040305100c020d08070c060b1f12181b0b070b060f 70
    0x240300e0f24011440010081000400e084c50351481c114803002501054403400544160180100b2607003003400319410220500721040b6641d0407540d250705c1400103982280c0d5540d6010f40c8800750400141c101641400c4d11044985000c3c5100039107607840040181c426580c0d00303526440240914001c00008594520040c002d0a12000140b440c2d13075907a449650503c629030500c040403420400000d4030320401c41103481a08003c11183c0e4980d40050000c200c540107102c0303030a0300c0da5509661402d0510121040981545610716a00d1401010a461511005540360503540910000885480800180001c2c41c864006406000c0c2005d103003408031104103a8100440d03015800c07060100b40c10500641e0043d1141c60114114035050a048028002003a1120b420a9184490030318640302010380e400000b2940c0c1e1144a815031044000707040d01d41c80509030030012004e403085000a0b03c190040f0814100c0c02c14442c00c215a0b89019022603085110207036640002e04e42003000a26101d003080f1800380d02103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 847198552 1250 847197302 847197311
    0xe0a020907090f1514130f060c030203031302040204090207031d0613030b0901140403020c0406060206011505160b01030c0f0803070b0f09011508010906051008120f090d06060302100201 81
    0x100c0c0411a000541c41004000251a041c2e900a0303171046400306040664410f545590303091041d10403540e482d07240300b100d43c1a0b80c50076002c0b072000d204080481100b03415038000c40c02d40e12020065014100c803e101213920035400c1000140074403c40c000782c80c245e4000d44403100d0010841000703070202c81c2c030008014840d890030403402c4214200701d403d220a0700e03080804520300e503807003081030781c01406c20034a00d5400500f45400c1100305030740000c0c408442c0304182c6061008030b40e2030109913560308084c000e204901542480444c03c051141c0040c0400700c18100000700e425816803070f405007010007030300281c0c4c0c4004580018400c0000b0b4010b13450080c20410700540c9031924584440410b4a0040d01c40d01d00701004001084205001750050040d1911807080c100a0603a1138828500a0480d4481100d100b0f0a0800145e86811014401d0302201ea00704040c11200c810021800c000d030303118054150120100340040780450f1a01c00c0312a900c00e200321400101ca508600400541c0300d407a18244045a051 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 847199802 1250 847198552 847198559
    0x203090406050303040302220f0f061502010c0f1b060e0609121c23091608120403020402070819020304090e0a24020d05090a03081e010b0f0d0e0a02090709 68
    0x20a4083e8444020b25140c5140340100708e4550805040d4030507c01070902c0c10072185020440184e44107000302d42b1502000110303c02100c00580c00d8034580350361040442e98580c0d40e0381d07545000b158101e41e031500503419003182c043c0658601c0c0490f00307402d007240100e80c404c00030071030501003c200c030700d4940c0040c180c00750401100d4000c01405a01e00b0114218403629050318080020140314110103148400b134030b480213880c00760007182c0d1b5400303000400b80480f1205800001e08083c04504840c94070303440d085c0c591a0900719001c0c0000f13944030340c13802c0700c1200c02005080c010390030700c0742c42030809210303980a10398507441c0002d4881910b0007001c0d000d0058100300070200c0001c880e1411404030604403954641014829010840213024041c001940e00d0300301400c01240000109407600070505c01c3e298410107482d0400491130b945140d00d940d00c2c4c0c601002005000c00018003001d0031382568141c006904e0481140300401c00da80c0d0300b800840030f681c003654020013185010160154403c0451a0105800b440c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 847201052 1250 847199802 847199809
    0x50412051309021c0c02060429040b0903190801290304060c1116051002150a020d110a0203190f02150603030409050f160206071706120d0203090406050303040302 71
    0x19480b0b0300050590010701420354150440120305007000750380e400c10038860740000203500e40d58115803c8440038042e00c0e00408040d0b101b154500301401008240c0780507610360b03031003411080001e800c09916200903c1200382c0100d140300200c6d00108155a035083c6540740c040c1858110000241551101c3c44841c1e80b0030748017003c0820349900c82d030020300c041000030307429000391000c03400d0450004c164001c414007140705001e203280c0c40c802c541003a11403010350316283d00101e8454110746030070b0f01c1034601e0038007040498085402410304442031080006810760304070700008959002d030803440090307040071403541c85030107186296004c130003080d080101721b003442804001c0d03d4000880c1c070820554010004518075403800c0040d200504403c21040080c1d08094100e0801c0e0182110541034101c411920b984880e8070103c0c4050044d0001c1e102c509003c2d88003814140c0240d00246181d8210005800074243c070354003008a084c0248894000d1555030f10004184401d41c2e0994000c14040e0f841000308000584 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 847202302 1250 847201052 847201087
    0x5150f010518060a090612020f06041508090102090607030305040b0f100501180b1614010b061615150f080f0a030e0d1b14091014030a050f0105041205 66
    0x51071000c000b1240c1d22000016400505900449601843c20303501140d1100c1080c0049015070080b40e500e8500702801c010840316204c1c030700500640c00d041c600610030b214010400e00381c120316030f84005403c003802c001c007158058000c0b24095000a440303100384001d000541507006e411140c13500240890703141280260701a1151841894100300e01c01c040b0202400b0403079007c0b0007424003500310540c1d8800c8004580040c61001c44241d500404945070081440c405204210766032300040d102c1410308207281318140085031000010740c0c440c1c00c12a54408101c0292096600f018941c000784400141070000b154100c0d041c0d038110801507407020305605012007000800c0300e1140c1e4546082c1c4008411000410603c1d90440c43c0241079000c40085000c0f00c2d00d251301e0f54000e5941e0071155110140c0c0038010803400d500c0c01d0340c0e002005960003405101714403d2841084c0078800c06000c841d04000302e65201450400304401140345a5542c0091008100d00341e090700f030b07500c3c03030700d141080c01c0030500c03000540301ea03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 847203552 1250 847202302 847202329
    0x60203061e1516020d080918092505100908191a04030c02030a05100c030605011710050a140906030c0603070f120f0203090c191a070f05150f0105 64
    0x10180030845110202c907000da803c0b9401c1c0e0103400c200300000c81c1c0c50000c5407034009082d0a4460105e2520b15488a0888680940300e03155100003040e05240c0094518911041801b8030398800c0d2583d00c010a880d12500e03951450314400b5a40c0700e24642c0b80640341c1c0e0030712052008011610715026401d2011551a444900898980c120103180c0c0d074450b4982560380c0780704510029054082c03070701d200d800d000021a8507011245403040030b1050b8079900d00c003201281c8043c05014041000c8000b5450544400514103900c60100c4076403480d140c1e2910700085d18140564840c140c01d1081c604580114101511000e0300441c040d8020003a0030515070000d00c590000509150803c01c2d030840c0108014460f042100d43c10085c00010000180c10360001d0000e5481141c40707000c4ca100d154111f40c01800d0000040800703c0042c84080d89041c1858481c84c8007201180c10306080301c001384002d4012460034865404000e01c00c0300141494800d1590310800303180014110700100f02310030010092501d07040e107042c03c0c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 847204802 1250 847203552 847203589
    0x1b020a03230a08131703040c060903080d24080f15130b100b07030f030c09050a1802040801060605221802030408070507090e07050a03050c040513050604060203061e 72
    0x551380c0e02040ca02e07684206180546075092407841000080d440c0c40c000c42c021801201e1080401752500810b6680310410b1000504d115010044880504040d6004001c15002070b00c0c03815074910443d10720880e0001c9600144400d0700f0100e643c2481e120304100d84203404002d0480140e983c5400407188050540701c64015052402003070001c1c40c002c622903814000f400d51030003143d03196101828010a0b92176003024480201c1d18240f403d08400b4000d140f02d508a81000304400c054a00b04078090102000c4076014525094080c000441d40d08003c0c002e41000d0240b540d0390ba622144c00d00114410508407110b9542040e038124400e0083d024156154519411514009070396512507140640480c4039907503018100f0700880c50007003410700c1141c0080a0110703208fc1210513280c0c54101300326a00301c00340300051650348019821022410b064205903840100c0c0c143c8c040800034591102c504048080764100c66040c0c1c0001041007070328002c0340e4a503d00210322030300701c2401801c01c046401c1c543e9841c481100d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 847206052 1250 847204802 847204817
    0x415150e100c050a050a0309030c0806091f090209040f0501060e011a07030e06030a0606022838010602060106030c050921010c02030c0c030d1d041b020a03230a 70
    0x5000d0700b04014000242c5c0401203400591079030030020b00d8010745010803902110924000510360f030000a455000b8000e8901034030b20312001c50142c801c1d1a9840c911644910b444414403130242e60f52404451085003d0146c05007104101d1400c6400c4899a070880364030103a2000050000c40c1603140104115046400382968a403002c1c2010358030008170b508000c2c0d110600104028221600e6008441100c0c801c0c2c0803203601c201320b51341d101c0c0d4079182e07082121119040704c121400807801c900320b60040040c1d0b54044408100c1da101c0318030028406846404502c0707c00702c00401c0515810805c00d0700414262a0400507000c000e031000380a441103105c0349119101c4d46088002504481048010b01030703d000080054070300040300607460350802140000e181c0541d11001c9503500300030910a82800c1030b030351100106018090759405000c040d46540d03800c2643e4840f00344050000302c0b00c44030001d60580081c84240c1143c9401009480716802c036502208c10880e4420900064500361070b800c0d0040d080591 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 847207302 1250 847206052 847206077
    0x2031504140412300f050606070206071103030304031e02070302060d240f0503071208031602100c0c02030607021b010c08270901080604080421020415150e10 69
    0x280e880b4010004407006084580c1c511041c2c41402c0d450b860304c031071080018410040651151001c40300d04481e131680001e01085480c0c011310b080001000c455218103100b40402c0160302c0030a165400403181100031501e500c1324ac00c1001001d2a0402da23384040c0300a04040d41181c0c00b040950051011f8800c40c02c1d1220041c40d440616060076181a04c205004201c900ea41d8020000c07995219203d0603019008a1030081220030203074404c0120707903412095061441d00c50304032008001102d40c086000318040c000211203084d0150052503402c84155131414109421401050308000c001b42401040d940a034040e000c060003003840c041444030b001d003040b0740e201116040154083c031503440d00108002d040341d030220440b0760310780c03110700c50700c60503603980a242c2e80728080d540c0c0d6040241c6001c0c20000382404208184045079903084c40c1c0c00d0071a80d0b01206000e80d603005c03a040c1c9101110135054080825014840c1190071700d034290000f8040d02d40340300115038020100d4007900002c114802000030404610 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 847208552 1250 847207302 847207307
    0x3020d030b0f091f0506031005010509030a0f0812010509131101111c0e0102030408120f09041a031603020d1502040f06050c0706030507080a0b0307090f02031504140412 74
    0x30248100c041c18100c1185030050104a6900e00c00ba01000c1e03c0c42004d502160504081050380d200d24210110310400600301001500c0a41182c0c0e095a458400d0050080c00156a903807007103103640c4102c01e11038660440070b00d14105168145c0200f0f004102c11b40400c802820680d848055883d0000c0d00350480d00036000040702c80c210003072440003103031144208441c2003180c1898102440101540d90505090f03040004a031a886980b01d03c0c0300c07542c010101690b0204c040001041008031b250102440c101c588000306087d80d101080b002c01c02105004000c1c01414180014904408485540c00071030f4156800288140c0710030102410305214030509003500e41540d41240d0190247c040d500503e11390740d440052240e404013009481c1c50042d1200061094043c1c09200c1c0905082d0f290848190b5a58056200070107002c0d806c6a418407402c0800144144c0c14843d40d52a00760910000d81e9a1400044411200640a0419001d9450310780d50300002c45542e101d40382c01c154400642140f4a85440f402c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 847209802 1250 847208552 847208569
    0x3130906140f013c081506190f020a060c0302090906041b0c0219030c15080c0f0a03140a060306060509100317190e01030507020606010f030b01120612051903020d030b 73
    0x1250f00c010004c40d001c807070564010000310b1050306469266034407130700c010060121a010703000c44460500a41500e0888650150789080b030608064070480d07000300e41980f01c0100790751202c40040c0204c0d42c00030341c00080d030509590a5900c01002d4406110400c0c6031211050800540c190350f40c200b00c000c103035407001c540e104082443c15244400c030040c00aa200e0400b0051500b45100c1c100d00d81e41550320405145014101192141c0110000030b4100301101a0040312640001001c500309a5680d40000c0c21011002a160040041c890001100780c110329000c400c461031500301074841c065032130410801c2d690000741d070307000d4990000c00c01c2c1295402d501c00d05054040c1250b240c0400c00da40ba10240090f50000c20764a880c00240c1e001e0015844804061303071031307000584010340044c01c0a1070b0303c20410300079000440c4484061500e20103408540c2d00c000c040341e005030072400403400b1186c1344105000c001c000d40708540b140012200302c40c0b00350b50780196807072542103010300c00d050325940c400120783e135030b10304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 847211052 1250 847209802 847209887
    0x3122b05010311030d1d0913020a0305030408100902030706200703080a0e01050331080f07032d08100b160203100b0d02040e03130906140f01 62
    0x1003888556100e24041030b00c0680c8101e854080c1c420000d0f00c1e0120b0340302d50030b0189040101e540d50034121822100340004000005c2890225040d00100f0500588410903034600075400f410166484500307020100382098000c1948003185c074103014104015130303404030f10401111114207000440f6050800803d2440c81d601c12144080d024940d80001031003030140050071001002c1d640c403911070610000540e200c0c08140c0e2600300d5800c141052011f810b6600d01d18400106444900054059890782d0301c1029520011301d82c010030070701240c10303010160800c1c00c40a1000080d0f0030074001e0780c1841c1e500403d44038043c061208001140c07012884241060000b003000d050b044003840c1d43c549030740d10a2104025500c3c8120300a21442140c003050016620402c104460014101d40820083c0c1d02000042c10983c40305021902041250b1500562580800c400030420007401003070151408240c00b200110444003540541c1e002c0f080c8052a070384c0142010300c1280e44d141002010071040e40c110b0850365140c1d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 847212302 1250 847211052 847211137
    0x90f032a0c060d0f0506120a02040e03190914091b0d021902010b090f10060e190323120406031505130605040501080d0c080d1806020301140312 63
    0x2030b040350784041d07940000200130100316040c40f00d900c901051003160040800c40f58801e4001c1400313800140740a400c07488000100201302ea00f0420406134445801c82190340310310100e40b030007400f08109482a03200e800007400464a80d03585184c80400c4001040d010141c802d810840050000201c0403036034150b489198403803034401c208d410f0060300a8000e000206c3c40a124010110008400c0403409075278912503d508a0700d550390500c1c1c500705440e05030a030219184e10030840c1403101104105600704100440c00740f400001300c2e84c04c07180c0b44298403d41050a103c2e54000c000d61f041440c07100e00845084450a281c0041c038140708450541100309650880c99000103018400980000160406402d0f1001202c04000780d0b40c0e80c442440d0b0f21103e804202003c80c64420786c080114032200040c00301d05000142c04a203141004205c020162500300c411184194044014041945040c0341c11800c06400c0d4020580300d88101c0c110b405901412000c005603075103807103089400a4068901120307515882 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 847213552 1250 847212302 847212307
    0x8030f0408040e0a06053307080403080f0a26041401290415050f04021b1c0806040b090412030b0a1d0f0c0304020906010311070b090f032a0c06 63
    0x40904d070301400c010320400344118049220f13002d19004181040b0307200c0c0c00c00c904811104401446448450f0001c03101562021000e10000002c035050070001c00d4211007540869a4511407044040c2003540c02d070000150802202e80e548110011016002d90000d1700036442c441450704000299001d03088032201611400103071803a60ba83e40109001080b05204101c07024031065141e075800700c60b2000c07141324056001052034038104170390901340c1c010705007088145040c11044101c00c018915044200d901c0141241500b80c1c110401c55021390103680010007101d09000c1641c80700009104814007030809410b034030107415460b00c0c082c000e80c442e009006010740100102507a4510a0198040c400900114060024005080080d010320b1143c4a04408841142140c030f9507020301101c101c008054074107140c2c0e138041108403d24a600500310302da20032a021003207490b100b20440d08003029040303481c3d110341c070502107802d5011300f500c2d9446031041c00c1512018140b0480445601d0b0072902260107403c00d000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 847214802 1250 847213552 847213561
    0x42009010302161406090d02011419020c0a0b1e01060806040e030c070b091003050705030114040b0904061d010c02031215190303031515030903091e08010b030a08030f0408040e 77
    0x1140d017910541010b01651489070241c03009034203070b032804885901d9410094001030510008d81b41c1e13601c1416000d900c018204500402d030689011b4064105503201c0799480100412038240605441c0482d40449103c0c54130351501802074030040c0c0c007038030580c8140d0700c034450010300f0b00c01003080d1180440d800d401c60360340c07558606440032a070303026408440c01010015007005982c0d000e070103898004d44003a52901e255038600101d9a00c00810391481a50058a55000d0f02d00b5030b45501d9514000e500407440001c10306440701c5001000b42e42000310285a0b4140116040c54503008815500840150040d0f2010359444082042c1815208080b259004042120507054a03580d0071803601920b102b80c0341004038a032407422140400080d41f00f019030580d2100000d6141c2c0e44241c01c0000c0c494440e05001c01e03501e0321200742804050040300f942d54004000d043c208030542c82400f507808510420b40103080114a1611443c4075071200030310040b041e038203e20100d010810704404a80081298109034561401c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 847216052 1250 847214802 847214843
    0x52409070c120f271503200a02013c020909010b09030f0105060a06030905161814010e011401090e0702030304060c0e011d0a1d01030204200901030216 66
    0x94000d50100010b0041010040240c22558030f1201e104a02400540f240c0ca4140e4160038910101006010147c483d4085801c2c240c0d0b0501c1242d8034040d580d007068462070080b03402421100d41c09000d101c3e45200b81c10003d5007030700340380300b119140341c180012040728a1075250340400380c0703d40140c2d80d40019005000140c0300150310090100c0c1c0508a003640d02d403404440e055030aa40b400c0d900c45600c505c4410701000781c14000d42c0705a0407140f2410035559117410a0b02400080c112540c0004880c03a040c4c00380c503d02039810300c10f030452110591a501c8030303541014001018203905000d40034105007c03420440481c0c0c080c4030a80010555030202da01d0524048030025200c2e00141d038202c41c0305090164440c1d44a010f15a9030184580694414284040281414803007504502480f604210f4140d8042100c184c1e0f1149010078418401c0b005025501d544140021036900c4400c025110010a0f008d03100440100e046906480c0309180c0036890b089505111419500031242c001c1a5041c8016003640c030070b8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 847217302 1250 847216052 847216067
    0x60603270c040605030d17070323010906090204061d04021c06031101031109040515030a030809060106020303060303220f15030f0b03030a1d090f0901052409070c12 72
    0x28180c03400d1000650320828582c1c3c0d2904210b4442c08200c440c81a96411b0781f98803003072580030601d45008241d40d000c603942d01c40814825056200d001103888014032009403030b03008010040c094810110b107417901d46840103024640045012aa00c0c0c500221a001ca0340c8580590ba01682e00c1c08018408240c00c003080d40061030503100450700e000c0c10005040503907002e8481d940032a0071040c451860700500f4400c002c0100030003001c07003a00c07044070b591811083d101000071000103846a242c440305420401802460580705901102c1150b1080003044400c0e10088192040c1c000c0e0200c00240080000d0300030b4020903ca904036000c80040c0080004284e00d450751400390300c0a1a403010805188a10b000c1c000b55560810348030b805910030044100c000d40306041d54500072a4000c0740d0400e61085e60b0018407056010b42d0795030320001e425401e12110000c284a02d0b03410079079170029400111952404440c0c021307100a031082c07044030200c0c0002c00305c6018510420f202c17544020402030301100e80d0006410360 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 847218552 1250 847217302 847217323
    0xf0507051305040c0c06180b0c0903070f0f0608091203190c0906081602030903011104050a15080f0703090f0b1b0f031b0f0c011d1506060327 62
    0x200a40c40e0014040c141032013180f50244140d030782d00340c8803101c0e0345641020704003a01a0491a04081c000300020a1942c1d040d140076000b00600039656503001d404240c03030101d56800030340c0414048141044483e20443c09034080b0340040c00e020f5142e44d03c02407214103014988140f0a881c80000080008020004140b01d401441207001044040340482c01111036403c1da0280b40003080d101004182a407151040103124424244100c0b03203803c9034080030030b083d90300d400b500d00130519010900b400203180059029000e004041005503020741150402402c1450141c008001d01c15030034080381013184290005018190046908018010203207010040a0411114050014003181c0000306005001e82142c0002100460140c2181c4035075590305003e00c1c00301c00641c0e21003c10000c081e903048180001d00b0038290240c000044c135601201c5900000b0282c80b000704d070710350004000402d4041003801003a420404c19500b80b07403170780d03551a860582d80d500d82d0340580362004104206101c02c91b0025090440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 847219802 1250 847218552 847218577
    0x90604061119020c130b0d0320031810230315031c1803050715030222081c050327010e0c030118050a0f0c09051501020c0a080717010f050705 62
    0x2a4981780f5010002c403818411011b074000300e00c521001c0071a218495014040082d05c40d03440802540030030702d07031441d80304800b10700d084502e420709a0103919041c1000c0c02d0341082c90601000c60004005e107001c27040400c88147d10b9034600800403e100d0750320704008032460034024007201c10f4011418450b0301c1d501481112074001a0540000344c0c07200201c0d4624004480d4000000c006050815a0000c91514410303190000c0540c2805402c25015800c105002c501141c0d140d4208010b0801100302c0c104000c2106605071000c0b02105c0c51880b69105003201e80c0007141030795600002213032b0141e5148100302021401015070800054040c24100840c010000300c004800030061f540e441c500d2480341c141620005401a004a0b510b040490440d4a92041075886069200f507600c0d100c0520004642040e01d8007c485010205610300700c5d6010008442d140d0400c0360f047c0e180344c1c0f070002c4699442005008030b0360005500c0141d060042003d4100c2480c002080c4400c2c0880e207424840140250002c2601024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 847221052 1250 847219802 847219819
    0x8030f04060b010905100311090901060f020105070f05030a020702030a05120d060f0302240906040e070314090303130501090f0f0308070302120601140c010c020d110105090604061119020c 82
    0xb03031503016491600841d10003404080402000e440c040d402404000000d210f1614100102076465441d0000705010700f01d5911141030850401a0003421124010b00d51810b1203401c042800b84c40b60098140c3c1e0703001400e040096960180d0f880401c1c280544c486d00180b4030b108032589c10b43d80d25003500141c101245c103c0d408001113540c03074071010030f214650700c8003940101c403c85000c8ac00001c0140791200e6106845000c034030705840c2c0d07408036015030b00c00c1d4407120388910402c0902c030280f0f505015003842c401c0d5200c442d40c0d107030900103d029124032024000e01030300382440c0403090402c08203411400003d5000400550b50301024148000d2042001c1c4040700014a20000a540750740207101340c4800100300910403a450792844010744034464545006446540c080c404035004210034002c41f203a8000c154090010144620f03000380100d00881240405a410041000401000000e0b40fa07400b9420401c00b14854a07941100681c2d442904c10588040c84171250a42076950000707a400100e00054a1050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 847222302 1250 847221052 847221071
    0x706051804060b03040311071a0a1101020c0705040b2202040303090509090601050d030507080703030b040b0d080706020310050307170607030b18060301151e0603051b0d0908030f0406 80
    0x1180d501c1d00880040e00d0040c0701085c0402d20900c3d0385203075909500100c0c0c046503103504940010684a45000105a00c005203d07040300c2c0c4e200d400e0724821045c0d100254109003880b41700783d44401a9000e0b61f400b540d40c80f520545142c1e00c0b001c906840c2c0e2120100790701c1342c00606500c40c2c040e5129000540c041502c0150005281c100100c1aa1007110300303d0150005900b08010002c3c0741c41c042c501a02001000c1c401c4078080703400f810003440000d200740c0700040e120682c5824002542c2c1981c11591040d54040d855001081500c01100c40b12030b032100e030040e42c3c0d0355003031500c040041c40c0350056500741c801c0e1100802c8011060050718400e104035411a00c1c541d99860089040c0c074000d00013540c019603290203003e03480d41d08a605d01c3d00b00304d006002184014a024803941c10717500391750260b07144c5d2402034800040885d401e24052302505482c0303005c1c05140703002c1540301d044e8005500c140c48201c100003010b210881203640700a4140d83d114480d10b80d2814501e811200c2004181c0c1c003513403100d28062621 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 847223552 1250 847222302 847222309
    0x105060121051b03070e030106140307090f0e031902070b25170a02071a0403050c0d03050903031306030e0106150f0909060605070b0901060e04020d020d020307060518 73
    0x10000381e19001208955400181c1c50390003070200907054009451031081020481220754010390310806079a594500d5494001003010f086d00c3c0950310000302050600d0452150740c80c082064026504400c0c0049405000010f1001c000c00880b42c002c00ca40c0070100d4241c01d1040d411180c1c8404107181d5080358501d580b1000c11407514452040b1180e289064003d000040388002c5403c140003030700070310310003403480000480398000d0352007030b9240801a0000c00007403104104ca42c08001000c160030310400d00345411035440c2907440030b18151a07417040c007000d403510082510581c116044010003405070790701c4043d014001e04103604203000320b002207400c2103001303c1c4c5038005204030021140103c081c4a041061944d0980d011301d08500c0d50410040e03440404180f6100c0d5020385001448583e60f030750360314802400e00101060f0007600001d0181d0602c0c00400c030305403d1000da81c4e0001d030100d414034000c00c51840052001035072003500a4050250500000c0c916070050040c00074100311180c0400400c0c50001003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 847224802 1250 847223552 847223567
    0xf0302060f0c040518060105090909030c0d02161a0403080c03040906061e1d031b0906120703031202040305010c110d0309080403230a080a0909052703191101050601 72
    0x141038001074517500000b002081e01080c1500210181041c614203000b120210389410f00031607000400b9400007420340d6008804005003200710f1014406044c1100c004c0c41d40b160b004805100f0b4140c4d801039004010b0311690050200c038020369202c1c01d06540c81a1007506140c0780d0b04648100c05d0001d1400000080040c0034500030347e0f800d8495a41c0c1000c1008403176094039250b811203c800c550340c6100450410030348080003101c45500c00c200c80f018030884c42000700070864000800d408d018500143c84041c0c8404001155016a90b05003032000c01c1038020740c940c000078041c650002d49a5801c0c109100c484680120b0004900301d08802540ca0010003d902a4295130803201d000b441c0c0c050170802003021a5000d402081c02d02c400e4a6802c40f040d442120240c40d1106951065a034560000346611120307400146180003015172420031b004d50f1501c5241d240360390700e00c400c500d011441c8002d0400ca040c0342c280121504120750b128200b441c0c10a412000b021144000030466aa61070407020178200c1d03014611 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 847226052 1250 847224802 847224809
    0x2040e031c061d07020d0f05090a06021f09021c1110110c150909060a0801050f100f2102040609150e0a0204210503090a06080f100b0f13030f0302060f0c04 68
    0x1c1219a021780c0c0100c0707107c0340740003c0108002041c004154180d850001c1e500c0141000d130b004000d2488040061502c91925201d000300d124a050b400e5001603d6401c1440f90302c0714103007920700484c0c815040159040030400c030503c0c1d000e12001400c030030650b004237900d0780c40040c07642103a131b0071011407050000702c0111205c0110100001c3c4554403080c60b001e9040c652015000d0300c000c030fa0750359411082c4c0c2901e9003a17404440f510030400401103080c115402d81002440100782c10f402a901d4105040c2c60b0302c101446020701e140380941c007a425521241c10210042406402c10040380603c1d034a6100100e495004480d446907407840403c0c62050729009980a0f01c2d100769810070032241d10300d100344c185161810102c549000c00d00c0000400d80e60444003c0042c040d544480c0c00c50b161000240340510402040c040041034008000e211b880106070503a00440000d1807503941d5401200a50250780d9003542c0002e0001c60020040c2c020182d02103020350141d20b000d80f4806058407071466207142c2c0d004601 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 847227302 1250 847226052 847226057
    0x4051903150b090a0902030c0d11101404060c0212060907090e1515010909020409050417130501050c15010b190c0b040201050307031805011a06070f02040e031c061d07 73
    0x40c04507101010300c4d170040036401d00c001c003112045030300240495000a03c0b110240c2d9051042d22072042c0c0e60400403490360405c0000c0c0340c400e410040d100103500300c1d4000d03401903070b0800010b03035100f104640b20418040965440803080390b25610f1700080441c3c0c0ca0768503000b142d0000381003070146500920001200901d0703042202e24011240d8a0350f40d54040d0a0304c494901d810007451640001d15443d05d8401440601301011002c10249003d0400700006450044040510340080022820599032030364584240d03082480c2c820755800e40100d407245800c410381c0004007020074035800068012901d400602c0c0e00100d00040106104103a481610b140c0481080604200144000500190720602c02107030301c0031581c2000510490001c004c2500a040040704030b9103690340b0120003942c40310311210701140141c11104245460102da6941600c18102c2000074000ca0b01c42030001c10f5844180150723550272801e50314510b1510b9800d40800054a024130a40317030800c42c0c2c180c003e140d4040d01340c100c03845a4184e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 847228552 1250 847227302 847227319
    0x50703060f0506090906010c021e18150907121a1507150207050712030507030305010b180409020406091104140301050411120a12030e0f0f070e090304051903150b 71
    0x132030a120b010480105411b041240801d120340042c0e490400700c0c0c40000b81c02d900303070f000640c1349020b102c020304e28410510085a02041004802c01c0c44a161882c0c000782a28040d80544500b00107403944070600c125250481d04003000700c910020000b601c102034030402c031900c2c07003100d9044c803081c2c280344200840a001b8407030714401c1225142480d0001d1405034414021145c0c800e5450408014080c105c5004500198000070818185641070140318050709034682c02918103441103030302803032240c9541a000c0c0180c0e11681ba0100790360701e80d031015000700407002d01800002520701401840c0d07031250182c0d0702d40d000c508440c2c00c414141441003d1145a0120281c210b0a02800c01c02003034150002e07402c0520b100c0c41941d000050550502080747170804d036860200704038161484060800302c0c1f10030501351550003814185a80c500c0001c800d030403140d000d2035440c082d0701d50104050031849150405a006000303c0504242c03950704c10380010803a40143c420144980d60011001c06640d04844043d5000442 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 847229802 1250 847228552 847228567
    0x11514090c030c04050a090b0415080601050f030f0d0203030103140606090a020c0109480608071b08071a100e07050d090c0e0c04030b04082b050703060f0506 69
    0x103070002142c001c90801102820180e42c2d400140d40c1c40140c0d00280070309601c40c120745881342028000d004e5140301c54034182102c0303814558030658600052180602c1207500050041054800b84440f0751304c408240141d031003c07035040c01c010759a54402c1c40101e400400c0707002c0c100603072603022820601540d4010210b8590f40c0342d030040e1901a41041d405051203560b240b420400282c45011541c50600c1c041680400343c2040240004c0b0030702c0343c0f02c0c1a0403c940c8010349480003080c038a01c040c2c02d880041c10000307215102c40d1412183c01100a1547c5200c0e010140c41400384145603010b400c007248240300055000020420100b4060f40550b61091038507085039041c0040e00e110043d55500403c1e0346000341c1840403118100b400e854030071505840c8a8002e0b07005002c0d030304442008541c0841d28464403850645195551045514000e00c0508200e402264003150292240204a80320b020030300c0300b070301c0500c0c00345000300208015035600e00400c1c60000001280002c8800d000d044a00080819040040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 847231052 1250 847229802 847229821
    0x30b0903031905220c0306051f150c0203070b0910030228050c0d0e0a051503040b2a1305010e01021e031b03040305010605061801031d0102040801151409 67
    0x602802480010861003a40f900441143d0b88050f0f8144c017411581d68030302d145081c403004945016152040703424025400c840540340c81034015044802c11440030580b246407407001c480c5409107042c001c0d814090001d000410510450180142810840d01d81200e41c0000b10b05908a10410310954074000c0710a4245402d00c00400c04e043c11088941041440c02542114007070030202c1000060340440c60b0140241c0603410548071401c00f034001905c2e8408000440c40b948031480c040240020400c001b01d00c00070b481800450020318102c80f61203241c181e0805508000841ca410040d42040710700840c0c08c00041662180c10074185484045e00903004802c10040782e150103080c0c0380d50710482441b0401014070f1650341e07851070f5940b81c4d807000c003c0c6440c1e40c11403400b1030a4880c1c0d0f9010520602080c8040550051244010f8000d40000d00b0002038045005401c0d41e409824070040101035440800c00140e020300c103400c40c038100c00b106032100c4d003910f44442d004000c1c90380e00106160072144c2c2c0e00c0010134105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 847232302 1250 847231052 847231061
    0xc06011e050d15090b07031e020306031203040f0b040807020102010506040b01081620011b030606201504140f120f09120708010207030306140312090f030f0601030b09030319 76
    0xa62100380444c92414a03100d410f00158141c982c0740000366a401d4101ca05003c030000c015814070f6042c400e510b1420300e803000a50365400c66030100c00c520800004101006815191102000c3d03024100124510b4582004022504a0034044e405542020000340c1c2501d002e120320544144161190b072040d481d02402004004070301e0083c1030501520000c60080c900034003001c41c2c1491588800403609030b54582400c0c2c048c601c41c411780001e1606101c801d2007100d8124100741e046007400c200107807000f092001c00514114181000e064246105018441030108150030300174051101411190090080c0490a6075121034150102c407245c414070008000c00c00800040c062030100070644080f6030582c2e01d6007401c11115901294590b9070003d044d42c10544c05001c0d100c02010405054018404010013103615045003861200c3c105070002440c606c1d40e44c480500d42c10041e00541158890900d50314000c0d07071101c0c20300007560014100400621210341c0001105c1c8680d00380c14010745002032070700c003640181 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 847233552 1250 847232302 847232333
    0x60d050a0605270a0201230a0315090906050103020f030a230a05060709080c040c0e010e0a0b04080606030f0d1e0207120515100b0a080c09060c06011e050d 68
    0x1071a8804003c504904000000d0102e070400142141c0c154500c00501462806400d0b64801100c0b00010181c0c61305e81025038000105905001c50308502015200d1541c1009070041044180fa01c4075440c18012280e220324180c0e4802d50b5070441c0701c0070502c2050b03034681041000405402b0020408504003000c404482800c0c61600225615840103545032810581700b12059000550125010013003120104407861500c00d0a030340402058144050050801078441071081c140190111001c607142c45a5090f000140710455a503516192561119620ba010a6904510911400c511110400b1003c1112940300190384c1710000c00c240b2418812100482100191081d030083da040051141d525980f103400d10782c80741020300b16582c84400d60f803030b4000c40513060356104101d0b01c40c01d020540895045400b500f0007400c000c0700c59950094658803a104d81401c0356007108001c01c1320045890b0004845041e03851541000e00c2900d40800d90140c1ca040600c100c640c080b41684680000c182440a080d014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 847234802 1250 847233552 847233571
    0x105070807060e030d06091103011211040f0c0905030102041d041a131b2607030f060b09071d010e031501150f051c02130f03030e0108060d050a0605 65
    0x100340e0a6103514040f0380303d01c211100c0700d4000152060700c81e2998030401d005080b1550041140c1d0035090310180c404d00050150650407132001c5148018022902c0402c40c1c00c00c4020000d101c02e140b12a04ca0024107000100710b804120b459402040310f26060007031f10142e90741e0902e02c94001c4511820f039504604003800c141c6070808401d40ea078603041100101c0d00c0c0300e035a200503c0f030508420b920b49a05e0ba03001c54010680070407450f6100b800080c6000769045072448000310b084c090008001d042c0e0781005070355400106154400005a81003241980080ca0b02c1003007103500f0502035407040010348046400001812504840c1280c03250341e0342c010041c5544058010307080b16504a0401c0e04240384074800e800c240141000c000c03031981841d80c003000c14202d1282d0792520300e00f0110f03003250b8640410305507205820704035008902050b00307002c004803550041112404042e0170580d41e0401401d0b044628103110700090326100000ca041c00c2001000b004c042d4050b000b4000a5040d8840c24001c6c800900795200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 847236052 1250 847234802 847234807
    0x31833090911040317030f0c033408130330180524040611071a06040b12190611070510050f0603060c0d09080309100f0204050a0501050708 61
    0x409140d1845092507030100c10b1003440e60740e8114106204404919003c21940c200c04104000360b8035050908190001c08407003450751680c541016240c00c20214903183c02d1a45105220020981001c0c170700000c20541c1526688007540340d2050b00c10164161210140100e007a2480c4070b410048050713000d030301d903141050110a08142ca51a03c4080d1415020020784030b183c60100c407000c1c031109004600c403c01c10003403d4180e501d40c3c4c12984405000040028020550364400e1400f17400b40c8030106d40b012640035034111401d20886158800d2000c042d100700340034600d04500310540342410180e100511007040014000da6852445a122040d800f40b411580180c0b9000042e032100200c0020b803022500c110084e1900c002c03144004c10445a006100c5540b20b000101482552385010030510340112001c012540d9580500305410080c0c108441c0040c000e41002080003201480420340c03218010015800740123409000d1110030590180c2d0241c164444011707281009950b006000800215129080060 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 847237302 1250 847236052 847236059
    0x1170901060b0c030703030b01081e04050118140c030a080712030e1605040b040203041109041109010609170703032c0405010b041a130501050a0309060903183309 71
    0x112607000607443c10a2980041042c00c10141c240c02402c040303e1081c81d0140641c0f030300d800301049201c0030200308081e0064800c081010b2207005e400407400310010400d04c2403a150145088042d04050f0480b04c0795038000d424000e2020701d00419014045074126034128280a03540e00c600003016a401101c2e81816a0303074000c1a5480c100340405250b240c032010311860f0003454241400103980c111180709100ba81b04104020000d640c40c0070081c0030701d6046d914006250b0342e80c074040250f03038a158030b02070744641030b14000600d40d0740c454100010b55001d0450401112510642681d84202500000380824a00c1e0b049800c410398004103080100c203134a1102c0900914030021404485080e08003c1c040d81c40043c0510039134410380f10380d805e5024043c00e210720380420f04401d440702c0001e9000c1c650412000150003a60345100e40c00040b501600150100030345030b480c1c64098039201c86125200c9058889020005401c1c2060384140408070301c40c81040101074400da0007051000606850a080c000864400b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 847238552 1250 847237302 847237319
    0x100b030a02030f1b06131401050f030c03070e010e01020a170912010c08010609080601050d02063c130b070303090819090b071a0603010204180b040501080109020117090106 75
    0x10949514044080e180d6400000b000684c2541454841c500590040044500421043d0600f004170b4562900c080705048401004032101d04c10414020080c0c074000c001c5c405803401080056020b011907403203180b500b841020044d14200d200091050250700f0810040340800d603000007040c8420300110125207031040c0300300007a4000c000d0030001d24145c0e544500404031282c0000040340542582c2c00c0011180d0714080c13103507a988105018250003013010a4008045490b59001d0780c4081084400520580708110400001c0465401e11143c14004006c000882300c640a012145000ca800c84094180c9017011042c1d0746a40c410700c0c00f1401c06544090640109040c80042c0249860004c401e441a0740005030080c00501e03250010307011060f0070411200080c00c203526141c4039204444070402d10f5901d07400003e0080c0501c1e404400803048645088124400d2a4841c0c004a141201e0070040d998a030324542d4221102c1c1c0c54024086403401c00c942d02c0c40c12000c1c410940c400390400c00840c0041c0c403031210 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 847239802 1250 847238552 847238563
    0x10120b1b0d05010e060d15111e030402101b0311150f010f1d1816060e040501150e06070f06060609090e0c0a0b0a090f030b160c0203100b030a0203 64
    0x50703911658510040c042900350001a507041142182e0b110b03680c001607101c0403400c0740b401182400065a82d5803511420f052071096074504982d2089800d152496260905035960044600300d100d02415020190918040c0c078200c0003075000410400190f0700503650035601010641c41c00d2041d0300c03c45c1701c42c000a03455503002c10710070801d04810162552410440d81c15240d01500729880035800ba040500440203408040c42d4000c1c03a20b9000d88400f0b100004a90070f001c41c008405096440c0f90101088003502f190144001c100140c0e0100203903a43da409983c0704907601030020740051318180c1500315921307194000d0690705000300e07061642130402d41e4641c0e0450b51280e000340b02040003000200086040d91040140340f00100018201c8600c0c0300303002581d40c945c0d07406502e9080201181d0048218441c5040b017001c0c0004242d03980e440c40d01d82c202250526000c841c100200d005a1014507015031280303450028060380540241a5001e400e004400504152010150903114140301c0341e001d40c1e400c000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 847241052 1250 847239802 847239817
    0x160b0c0115121505040302030a0305070509131d1911120a0c031e020f120f1b0a0f0e0c03060d0515090c01030b01020a020d06060b0406051210120b1b 65
    0xc500103090680b41c06483c11040300c50820006103040d04001c0072a40100403110075804a1070700040c0c0380d80d41001516103000e640386494002a152011041c1a9440d51164054a8900010a03201403680390080e56402601a17000d1071300c4981d109610001e2200d80445034490b00040507114004002c281040c40c0031074421050351b540d205600c0800521031325200720251558500d81d400c071100f110350040340c030800038542d519014041d019800b03c40c0c890144015014002d082c401d44071010310f100b207400d6015500107550b511a9a00720790003e00101075020320702c111401c01c14071000b40e658840c54030400b5080141426040003c840b40000080d4061101c1c00480c801010001031506000c000c6074a03050001000a06040c41c1034450403c680c2c001604070b4041d9411150070030148a20326044000c0c080542c0021503101c0040740c00b040080d08075000d4a500406500a50019900d5180906110f142c078812207840c0c0141d208002c0200700340140c225449841012501c0030040e4030758400b0301c1c40d0b00440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 847242302 1250 847241052 847241069
    0x120e06073c0c031a040506040201200f0c1206071b0302010b04050127050603070e2703041a040b0a030905070e010603060305010b0f01140703020a0206121503160b0c0115 74
    0x803403c2c003c0040c0880c020003100040003040b490382c80c01d940c1d03a959a020103040a41407007808081c00201c1e2403802c0501507400340b50b07410741d4948100c01081c0b6980301210400703030f84154480300c4103504040f40043c0780e5105031a15640c20350384c0c046c41c0341c0c41c00c0c1600000c1e4041d0110f5480b0710040390356450350b014142c001c0c401401c0901c0300390120a20017009800c48401414aa41454140942603a00103070701e00a4500c0d03100034047c0c4e0748900505c200c00b200300940744000c140302100d038244024400710181040b03c001c00402c4080321444090002c4510403800380007400701e41803010915051184e8070410040744104116028507440d0302c501701c40e83e102640003200003030311a801403040141c00c0c000d01110b18000c2d030ba5410401c0303940d00003a02e0f600208180c0c1031400f030040b4580c4c0916108004000781d0039005814150360790f150b0001002480000c44094a02c4900c641c80b8003818100050000354a1411480048500d41070043c0240c4961001355005000e6480d26008002d00d07940040c030600809125 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 847243552 1250 847242302 847242323
    0x12150103080d1a010909150f0b0301180903021c17010f05031e0c06031b04030605060a08061005060a020f07170f07031e060e0109120e06073c 62
    0x45002c1010340b1070650701c092445150841c145100e1740c203c1e24030801d5030700c150b001050198a0f859010744100d135961001000c40380c205000207482046400031816180d9000824100b44c25420611098803030441d4000c005900c0b226400e2440c0040b004100201100381c03516400880908441c251554003e070002c5940600e44002040704d0b02c8c0811003a2040e06d181b001840003141c0340a07200d0344954801d80c1440c01140000b001030303140726411a1000e02c3c40940c0182075110b80d22400c00c0c00041500300c132914091002600301207a140c3c000034640b4031803c405680039140c2c0d0704040130302440b44c100420b4030056100f0354820040c0040b090080d20040c15203186c082402044140c4021b10b04050201030007004d030484601032002c2820350107400c80480d401400e5402840d0079140020082160030450203a5500c2c00a542042040c64000c1014040c1c140c0c0d58034141e01d514200b0404544541d4000070100b103041d40d804500c0d2017016206d1641144900b040840409045070204e149a10b0440100c0d000001c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 847244802 1250 847243552 847243567
    0xe13031b0819081308040902070c05030d03020a0818031e1e1908090a08210a0509060105040606390804030510110702090925050301050f06010e1215010308 68
    0x1141003291300c9070701340000340ea0a1020383c5480306a4425400342d11082500002c0100c01d01c1500b0200b480280000340451303070200300c1f90600500a40112544000045204020640300c8089005041110b000c410203180b801100801450202d40d1a10040004c2c00c82845802c0c44801e0881420007840e0440c40000c1c2e49002c905d4103a10440d080e00d4201051106034030502c0b031007140000b98411440d61250380e1a98503801c0300002035071075070361600814542d0201c404002c0c401c006c9400090194007c0401c491b160f1345c0702c43c20441603c4c001e0180d04001402c035030220300f64100040100503001d030004d01107202020740c550b0000076a9034184040e103d10310b000a0030002c00504020842b000f110308442040038180c085510034051003101c10103171044040001140c1a01024010100000006100580000b8207201c1354201c034401c40c801c0c01d00c43d5103010f0001e0341d01d10074808071500c5510140d4848280f42601c070200700c10f00c29000e003034035464883c0c40c01c051182494140030750302940c007850296848000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 847246052 1250 847244802 847244807
    0xa02030901030b1e0d082b15060f1803080c03091306050a05121516030608071d0c041a03041e051c1209060b09010e13031b0819 56
    0x2100d5002d14001d00e080c590000c600e80b05495640d130403420840d1020686915070808070414010444114040100c00308484103030700c80340c10445c04031070b166401070240d2000d08043c2035a5a0243c4140d4010903124940c42408500c0340c2c0414000f160158129500c084e102d40b078074a4a50040c50700c135020382d0702c002119000c071f02c0c14035011481004c0e00795007809060b0074000451a1880d00d4407565000310607039a9030b0301140c6001d002c401c002095611840c0c0715441c2400324502e684400848850109281620115043d800480d2000035242c8100700007141498016590240007c000c1100e440528240004211419010341c242a41110006442e444c1d0602e0700b03101d83c104200c101e94000100361107000c1400603c011600000c0256410a8810420b1802d241035410010100542e0000c9252400a070200440c650044084c88010390b1905078a81e240c80c240d820401041d80d180c10042c408181d0038000920070101400f200055513080102403100f1b65030081c03d40c0003814841e42050442104454456 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 847247302 1250 847246052 847246061
    0x16210b0f22050a0609080d05040f060c0e090114060c060705091903020319020102011d0f16060207121b090b100305061804020a0f0b0c072c04020a03080a0203090103 72
    0x4411681100c00640307141e4038580c0d00c0700030140007401103444d030715140c007840003c00035142e150003d0801807055203014900128440c0100004550091500040b010f0052058200c10701140001e803001c08640d0030020242c0c00104078640040d44440308001c1c41e02140c809000c0e0501900540d2952511000d01c00c04210320f004041184002e002c407240c03030030400359038001400440d00843d401c001c00c0b02d00300b5000403030240c040150008103240700703030506026030080025180b2a0011b0103080c0c1d40b8541c80b8800c10b1101034100d03c104030050348182000d0291400d400581502e00b8400d03a40b4401c00400c00784409040d407141c1e8011084280d584100342100c2c01c03c445064213801e00c5241c10012880c1110004855240c000754220074048110001011504c2d0721582001802d15600003000e019550032159850f82d200b6a820001c500a1410000c0c0000c01034404840380700300060140040001c5128003010850002c1060781d04c1441554001b0200784080e008050a01c2c0c650301966542c42040300240585 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 847248552 1250 847247302 847247341
    0x130e130c0f031406060a0608091e0c041b0e01052d090906040b01050d0905070b0f04050a0608100b0901020a060c11160f0306050c21071116210b0f 64
    0x4e800c500d080110b56650b080c2d104083c6c0745141406181c03916100e010038a4040410060341000c1050044000503640000e0942c081c8031007154241703d07840340e0494421802c903039a015500880d04600c4540300b2980504054082c0307401094500352200a007080e908035440406046140c8098002401d0003c0d040104950354010b10503601848140d84140001300341c3c1c4980841286c04036665841e4808100061040600401c0c99054203925482c2112151405600a01c101031050840300d00c0041d01d240103100151042c0d41c03030f68502c0da1503403611110308060f078003901f041c5045000710381c0154000f880030f02c1b03071398001c1b522039581041d0806903840003850710500d8a61107402e660703103040030420000a51440c006480e8042030100d0f05171100925140e032409011168818107041d1040042c4161910034140d00c19004d41d07807141840090b6a55407626041d203064100361007405484c01740005040c0155000407000182e002d650441c500781c540088100c3c0503101c40804c130300c0306814400c2d0014900c4890286 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 847249802 1250 847248552 847248593
    0xd0507030c020a02100306050d060e011416030203070c02191401020c03030d020c07170604120804051b03160603060e06040204080a0b060a030209070e01080903130e130c0f03 76
    0x124407588400395030f40d40f0249000303200c1c150031400410028481d4101d00000d10000e8408802c1c2411031a001e009050b09040036005580303040303000c40a00104406490280c40014211411200c80640803006588010541001e01030034601d040d005031a2a12010749000c03a00c1015442d013401c1c5580a200e50106144660456100070784030718030360390b010013140e8440640c07100060b030352400c1c65159030501c105544698020030012243c504000310108145204a205480e0f50082d60240081601c04400a0b10b001c2c10f640d10801034159403002c004510755000728000c04550940c200d0454082c0b96039841c0d0031000c0000d803502c1c81008400721070941385400140031a429400c00b4206040b03d03941b095107000c0075040c0d900f80300c00b05a171501c0c0c09042030095078001c0d12000c0980f40480010b444c00340602140e80c002500500042c0006c50007100b5204118801d1740c0c01c40d4aa45031000c103010809000d410212640800f101c440c0c00500d40b943d50200400d482e40e81019585e03e50305151510365000b4060018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 847251052 1250 847249802 847249811
    0xa0305090c01030c120225031211030103031b060f020f0706150605030c0a050412140606011e050a2c090a05010305030901140d060b04172b1b080d050703 67
    0x116540c005148503841400c5a800507102e000301b0190f500d03040c81e0082d07520102041c00c01900c0034141c2c860301e4a6401d4216140610054030070582e02b001501c424440600000d400d4543d209048205031541208035003d00804030380c0000c0044000704a905c0314000d40f034401d500150010030007074030340152031290b0041c5019004062810b080900a44401400800d0355100082c3c0001e2841c003c1c0c09484c003510742d5101a001d02556440c0000b03c1c020358400b05800c601c0768000196041d846030f5140790743c000110900203c1400000d1050f68250803c0807c0302c00c0c801c2c15030880500c40516000e0f09401e0640032940f908030340d064018006d1040001e00072074002400d040050010800001c11101181401c0c070b8042d280807820035482085001c1c400111005a003000c100007002207112002d0004c0c0c80750070100e40200c022410000355950348049800c8000d10b0341002c134041c0c0d200123030404040145c480c10b10740403055440e464020f081619000854180c200400c603865040802d119099004008c0d003800c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 847252302 1250 847251052 847251071
    0x1512071d180406020c070b030406140f060d03050d06170c180f0114010504030f03090f0906080a081b030a050a0f0908061314030f030a18030801060c05010b060a0305090c0103 76
    0x1c203910300c000c0028082540020f01d4449500b0700704500d0000707051401c04c3c940c0701d0500d480d1070f0b40074100441d003102c0e81e82c0b03820000c10114a14040003a00852000340b02c00705540c8681d8058540f6004002d403c04560754503407002440030440390b00e05201440b40f2018161031907400c0204080101d03070310034880208031440b040086013442d00000a040d54507820250228412900040300e55200302d40004100e08182c02d4208201500001c02d2810b80d0800301400101c51f40f0b0341101422100d403846070983c0c50f40100d5244010038102c3c802002400e502041c0d01070720550282440b40f8582c8104002c2000420005644803540c1d8020195400450f00340b502804041c5000e000c6627864401038500c41100400070a04406c0050701640c0d007103603680f00c009503525081c6140f10034030b642e003040340d00802c030604100510f1400114440d03138071001c5074142c44454559003040000c03901061144411110780d0340e076100f00455683e483c0c0107030503071001039075003c1801c0c07418005050816103094640e40c189428003011a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 847253552 1250 847252302 847252339
    0x140403140f0a0206031503011b0e03060f090a08030c13060804032606060d0b041d0c030d051903020706050a0902011b0804050f03030d060f03050607020c010e1512071d 73
    0xd80c1c000c400c3c20b01c603650f07502828000900404a50b03100340b0f6841c1b5402d5504109d503402c80344681c840142141070b01d4060b907450035964110780d0202d82d42803103500011040000159020003650f0011422080c0a0600e2101d80b101003e80c11180c2001d0007048040d003c0104042c0e100180c40540103d011403161404a040000804000050300c2640308005c0400c031400c0d5054554402014660010320074400b130300305050340b81844600c5000890715409812480015404d0000f0600600d9090b666154075000b103402c2a8880c4113098a85801007540030002c1c400807600742e006940c087c440c4e541e03001880340d21078400503003420300001c00000100d0016101d440410284404d0703c080b250144d07140c641408600c00080c1c2103214424017920f034a0302d030060200d228464a140c034400d136441182142e20b607441e070410aa07900e00348461000d00151f8107613040380c0a0705107460b10f0480604200082410314074500650040544202d51400015402e07800c20748a000500500e5110030405a40c0503481c0c2800a030175 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 847254802 1250 847253552 847253557
    0x418020702060a0c0f1b051002011116030c05060109050a0e1c0813020402030a050103020f1815060f0c0d021b1c08090603040b150411030a0507140403140f0a0206 71
    0x8400d004c0c1054100d0140718038a503080c46050b512022500515114114a205107141402440e01a05100032410007160051240d031103410b03d058802820141813000c0c6c80751702d050b8440c003141001035103a0382c00002001000303081d01921820501181d01e14181c2642d4003101c02140c0c103003900303502410061980081c3c0c0001c03180302103180c3c586407103513544141d09820403e6201e24000e402c24800410084a4259070384078a050f03d04c02c0b50170005840b81c5104104100094224171814a40030001064080c02922401c03640010094101402c00c0310104d905c07505600000400c0c103c682080001b0750800d54144045c803a004c0303510560001040490010030941c1d0f190f80304044154030f17002d034054180400d000c2034901c0048001c000301c3e80da141614010215090664400b00c11000624104c5118a480e0040d5141e10b9020b14200382140d4415040b0005400080c1400061113001550007403001035030310040c400b850240b104071101200030b2072807600e403400c810041031441e0882c00e00a001a81d07080c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 847256052 1250 847254802 847254817
    0x20d080402100e0114300105031005070315030311102705070807030318080606102006010f03030215010501020c1519030603060b01081920030903041802070206 70
    0x1000151040620010303205c810300b8030030300f000200e400324110510035007485428a20302e0a000f40000441e010556207a6841c8081c010700b03515030004c4031120072184d03881c0c1c0020761154407454007150382808544600991041908194005400c1240000c1c241c41c0c100410456031610100420060b41b00d54800d881c01e10070240c000c514018144040c07400c0c444100201c0001e0040c2c60103503134000740c1e01d10b006001943d858170369030a554410301c800145210b000c0ba8907840344002604195100381840000c44109090394900d881c0c0b10700c0c40c1c1c1154030411040100c513003c3c242243c0d81301c0409003903040107840c0c0b003003d402404903882c0740070050100366030101303204d6144c41c0c083d1b8190301c0e030131400200340010b4000c0d103800700c1001e03144c190048400c175416080a0201c030f0040e0700401604517800011a006101240c408802013596400c048018280d83d224212001d40f001c2c4103400601c8001000c1c0c0d2592056070040440d074000710701842140c018200b0440c8039038103d40114030305a0f1560100343ca501403201c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 847257302 1250 847256052 847256057
    0x50309060c070f0b0d14090c120a0c06170703020408070303121805100b0f0d02150d0c0807140a02060613020f04030b0412020d1b150e07090b04020f180d02031606020d08040210 77
    0x9c0c0064801c1a0411240002640c4034544c3ca40007034803013000030110a180000c00100700f4080c00400d904038004d200311820303070b0003240203402401d003181c8040c0c42d2034900302c40100e40e840d81ca01403118071941c110401c148031803040f4098001514580c0301c240079a8051030881c0d11659018180800f81c0d5140706500701540d85c1900c800540c41d169564041c81406200e41200b1303c1d030b080c028418000340d0700c889014031504040c4c80d420316249410b480c10125020380030140c40075130720005c0030030480d1610720345824205020290141c548003181144091a400a9004036041201041840b0070080c41d840b002c40c0c0440c103407000341200050711300700420351203007241884000c04200804106001c644010840d201410110a000d40d034050004941d03502250b1095621803072804a06082d1860705d40200c4080a651695507070600c414404002c040b0302401318030350760100c0d101c0742030310051b181401101c80014408145e611800e03e4040007a0800c01420580410451007404200040c0e5401e2910b010180b07061 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 847258552 1250 847257302 847257319
    0x207061d04050702031303030e03160e0a0b03070b040b03011811070b060a05150901020f1920150706060b0702101101060f080a140a050309060c070f0b0d14090c 70
    0x18001a805d610031550b5050003001c10080100078160403983d00d5084100a400b1a05240c0c030000030135107121480d005078200e2000b44000f0640050107500650344c000001000d9480065a8891049103944586c0c0803060001d00030004001121034284a80c0403c2c140010510162000340040700b01b82c0708400c001044004480d0115081c0e4852001c0f850161001426080c01085070600100f9650480340d01c0070b0041c481c0e03e41c1c00d0300101f004200d0b120003202d00b505e09080d4181c55500e413036903039107031440010880121102e103414580d503010142c0b25420304508583d42c1c900c120306004d0141d40681e003000c0c494103005c001640060320b800c0100c481c80426450010b000e1b40700c0c49945400341c0015480f10078200644440854410004226600301d288182c1030710880040d54100c55840d0003600f0409403c2c2d410500403104e00d401c00700c00410591156009803000b20740c0f52000e0901c1c0544541282d05c08800203d000400c020051141840c0400c9480d01000380303207000c0c0303074285d80d404000c01c1076400340090303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 847259802 1250 847258552 847258561
    0xd0203071503090203070608090d09080715050f03100f0806092107060504060c1d061605150112030e030a15020f0403060203040f020301060b0c100c052101060207061d0405 75
    0xba074082c2440070350040590750840c0c1e0b00c41008101c583d0a6900b0391060160a561880301d80c0201c43e10421500550060300c01d03645002400e44d8104a61041203003408070030012000500c1c0000015071141c50703c1490001c065091a802c00c202034400d07008003809520010610108070000280c0311100c03412881c04400640e0401c8001c04d542c021008024402820700091200300107003604055002580c2c0e07030314501400f1a42e030380346000e01450028503412a10030807026800d100701c10440c0c00010b00810880c0c00803004d105840300caa1a09a000d00400000080300c4803c00d680405d60fa03000e400110028540e001f00b9450b4000c5619603a1282c1c0074a903400250300104142c820309503001103420850454592400e400c02c1d901010510f04124401e5103000c002146000303d010036540c42d40e0b20000145450090030024200919231640c6080a21600340704180c6a034400745880c200039007800c0d90342010b035403402c0303c06442e00c0c0c0160040c4003808502089000c07119150303036162821702d404030b0300071900744c0742d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 847261052 1250 847259802 847259807
    0x812040c0b0c010917070309031202010b031b0108161b0c18050a050c03040b15010903081c0e01110f0706060519060e010509280924050d02030715 64
    0x20603030702103000d1100109903064403000640c07003031108034010302c101c030295940c0c2002400b0900c81c03048000c003c01c017108001d0001c26050041203081d001c5c1800006140304a4500180c60490400c4881c410802020a081030a5911035125074001000c2640450400d0f070209001c0d00205400c40d10610f01da4034100007105009103082c1c1d10000308860390464020024017651900a00030854224840300c2c10000450a440c5280c0200d901c40c5420006407201074858a48100340b1038004140300d8104082e4070030100101389c0c607000070080b040b1000d148454850044040c0400d890300c40044a0a80e4508523034019043c0041003110180c034180c144aa585000354a0302d0402001250801138100302d8480c4440e03c590000700009094075175940b6080e03544c00300303000110340300c5c813030300c0c9006402c41c0c465404600d4481d540c03005901010070b041e04c030900d016100da803448110707001002c00c4901e000010b5401c0844a100d406080b000e4030341540c000c9e071038402a0300820340d140341c41c0c4036032800f450341b12001200c0c1a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 847262302 1250 847261052 847261073
    0x518010b091303111e0106080f06060120030705030301090b090a060e070c03050c030a0c020a09020f040909030e030a080918010b040b160602040e070e180402040509030d06080a050705030a081204 85
    0x406041100c07040903a1703c1d0854000c041e070340504a40c0e40700c3d0b00f00e4212804400034100d441080140d4030003825000b0201d498400c2030001c810701500344018818800050018030155002c0d04a0740c00004202d000da030100300101202429008059242010502601c000501140d50000f20b5003803040302030280745022170742c40c81000007411007400082541c903880350344508012a03050084a11190468440d21117400300c5c0700d0b071303280b2911419042000300040d102581085c0815406800c00300c98860b03201022a0401124080440f10010002201c021515105010f00303d03103440002104295810141c25000074816401012035640011030402c1c8034242205e410102c140d403100f419912140d550050502141c0145c0d0b04201150040800403200e050a41504a660711800701c00b03002d603112902030000400001e440c1d54070354041003188060805003802000018090b0400400b490400c0303041c12424601260000d910035005a400f03038011560aa0a1b19100403440825400e10f0721540360000196 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 847263552 1250 847262302 847262323
    0xc0c0909070305010603080403020109080312040f02060d151e081b120d02030301030b07030b0607020f011413090606030e0a170405130507030e01290609040518010b09130311 76
    0xc2d03080185c04030812442401900449200381c0750811100d40f144d81d000c1c0c680c0510007100715204481d20000780462084144500a140050581e40ca065085d6441105840c000d04000482c0c0911120401c094596880305a02201c0a4184001214180010039440342c03441020008000f07048401040d2030340e580c0000c44409809a021180b48021102000c0e480303403c244029072310031f42c8003400645468040c2c0690780c1a1280102040d1400c00c640c0d08020001e814080d07618100400340c0d40303203003904800300b0081007442180c2103031018491900301ca0070255a038a4005504045c145245503404580000701991016480b01a60848004140d0010194049c42d03000701e5000c10318110f0761108414a9015500030035055505000849202d10380307600360b0b4174088115054035005c01c900da0711001e0ba55840500135000031300891a00300e00da800102980d20a4551050302700302e40e1103910b0400340034481c0a002c44002d46075440280f410440b0300309404409400075081c0480c54080403111031040c02406540b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 847264802 1250 847263552 847263563
    0xc081309090f0b0f0705030103020d03020715020a050615010503041401110708090301150501090b0d0f0c02010b01090608010e010506160b07090f0e0c0301210804290c0c09090703 78
    0x10032503070781001c00311410401030555005058201181e802c01d86054000d205038003580319945940d103103909001034007004810070b0701140a030b14000300340d41050034141401584158000c1500441500b860390400402504240d02e81c1c85080c82112542d8000c0181e9501c5500100d00041040761400c43c9405410703070f20340400c010340c1d000866a003002036072000340c0204e4000750020410900141c07002e00c140e0315a805500c0c08540044010005902e40000411a080301c1c000c000c1001c500c030b0200f51080e501d8241140c00940d455810200d20381d60b10481d0302d4000c2c0070600d0401c403c0d5151016150880a041c02401e0040c0c4000036240d0b0f4070401e0070040083c00e6131094903541c407481e00c050010400c0000c0e02529200c002c1c618400560700c01700a450381e01800001003a41d00c1c503440c1c100d040990003201d03000d42c100d480d124a02ca00100d501400903100514108000c818880d03030350051440c0c0c416030003030399494541060042ca955094005065500041c054480c0250340d00c0d03214999160104c55030000b0301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 847266052 1250 847264802 847264811
    0x9080f030a02130e04031d0f0d0606090c02030a141812100e16051905030f06190c0c240c0e090604231f060c14010c0c081309 55
    0x18075a04a030300405031a550000411002600d0b00440300c50010f050310013800181e28a00c0840c1d411440520001c1d000000800e12819080e80e000403448024072404151101590391030704211043c0075001e012680302d082d10165291101032000642144989004402c48200100b19080340041c113090900d000384c0010441201c090521051b00d984220b01817044800c1d03800c04000d040d01c680000340500e0b18900d8030351740d020041d007403805010811031000e150001c1c00d00545030026103600d00f401200c28001c41440640f0b0a840c00015412102e441c1810315116103140580c1508800d83c001000d503101540a003000b02c03a1600943c8200030707084620038646501c0d20f002948140c0701d422020584164030295410440c45d07842c0000c020448145640c00201c0d800c0300525100c2e01c0703040341f1040b035000040c01da18890700c159400001389981c80c0707500140c0210341110140002e000c681d58036600501d076080d00034011615540801000f0540d0390300020007020000c5240a460010440c030100500784114003000f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 847267302 1250 847266052 847266061
    0x10f0f05041a0702040b0a06051803010209060c030a0e010c151808210a1104120501090b1003020913050705040c0c1401090201121b0804080c072402030909060409080f03 74
    0x7071456000d80f004900c240c3c50150301100d94144800d00100304c40c140c1c3c58031410803070607000e5540d441860004041d4195820003482000d070340d03200080d21360100207800560715a90008005440c228198070518140700c14030702030500041c0702c0790300301e9640840381a0103d520303108900b21011a91021074010900b01001ca141c00180b10090040d414207560300c480d03910381c1d8540d0408903048810321003054268000810041c8000c144042046060a10844c00015010703529200d025602c80107880d90f051320740c00d003d820801e500d0015005604510003e01c1d02c00401115626683c0d0b560082c03040a000359218006106418060040e0030800341d0840c01010b0601d9454480030b00801e60302900b240410307030040303104800010794400c0c7d07112409401240100c80300b0410040d00d0402c4020404c8500410801c000b0621240c103000090041041c00d4545000c602240c0c0121030401011069404561040c40301d80050f0307861450440d04400c090750001056459810015000d11078108810131f00300e030020030300c0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 847268552 1250 847267302 847267349
    0xb0f09010305011a011e0e15040311010e220b0a031709041b020309010e040f0911030f0109023f100b22050619030303150501080402010f0f0504 63
    0x100c1e4030320340400f020031080600e401511b0005a0180c00e401c445071020060301403600581240c42c40e170350f00406400e12a440507040790701e0780c1d200f500102c0340318440c0c0a00040707558020324840702c040c104071400d810548140251400112010226140c050380707030320000111f91155400080996040030380e0040c50085003d414940d584007110355401541341442c4004000903039103114441c1212603000d11301c2e000d080d43c0112070042c009910070707600c695104c02c4180286500c0c413491071018480c000d030401c1c070b50000c82010308002c0e83d0020086243d040407540401030381e40c40d120b0b401e0303035060200341d95080460b8035503030014090550b0301d00d071a4100074211020442c1d00180410799000c84640500a0110250a00c00540d030501041c0d6940a20728401c12840521a00503a40c0002c020f840e5045120004c030810a0b000140c0d030043d400300b83e9602c01e0b003042c0c814501501002c2e000271300300038540b0308296000030040c1030383c180e804040001c0800c0182c2000c3c85a41110014034443d03440401c84d55240298 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 847269802 1250 847268552 847268561
    0x1401390501091122050a061d160e030a0f06020903010c0903050601052704030311030114040501090c0507170904091a0f1605130806010905040203210d0b0f0901030501 73
    0x2c2da41801c4540b03100e02e891a020200b0802003440350011140302d60300110388030241030f01420841b00709485c0e66001c280c80c213209448504100040017107810b5030511810694404000d08086010046107000d070103e80d80340040c14952096219112401c4080d041c1001402030040201d030383e60550a00f40e649852681c482d0400042d00d00500a50b07001e40d1717980d01007001c8601c0b03100e540c241100c03500c08211810410b00006560140c081c0c00d0204840d1101c5151006503070098004224640340b003c80c00300181070512801303014140400c030400180c0c4104d43c0250050040e040d00400c0c00040403050362010f00c8510544507800c201900c14080d02d61146001c036548400003002c02c240b001183c001407100c5000c1c40d400da000700034891910883d015902030880f01c680c41a004426100285138001800080402580b4000d00b201e01000665042610404d810b003501943c106011328000030702c0b00a0f06182804480042510101c0000e9907001c0202090079404110701090f401092080008123000c0c06400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 847271052 1250 847269802 847269821
    0xb0909030702010207080d080105010f170708010906060c0b040b061206010b090111011a01050f0715020703021203070f080411030604110a230d081b03131401390501 72
    0x179201c24544816030b140d40c0355080f00b03180300014080c600401c00303075001e85110310108030f280c6040c94103a8040c09a41e04600070a64291000801c0000100001c424911030803000d00054a0207850443ca50b45502034008806000546110f420303001244060780c40010344440010700c40d0945a841d83c0d1040142c00c2138000d00780c0d180c040f4040d0b5013486a50708041c402c40b41c00c20419941014512004401110b0303581004c0d00801e601e0714100104c601040c511030f00c203200e00d40110800b42e903034219468002c0c1440200c0300c2a64502c1000c0c0107115400f87c1014003103100000c0b6181168545d41e031810301d03a01ca8100e540c0f500d40c15009501c180000e010021a409400c610150380314000a40c3ea01c0c40387c1c0303002c411540c100c0400d0389410b542e038181e4a071400c101d2588900034640c2d01d0800c007001c0711364040072104842c004151341c000035600c00d01c0041d080c01d040040c90fa580004082444a0300041c1841890301c034081d8860992010301d03070f80784082c500e1a2201d200b00d8042d995105c1c443e4076210b4000c00800f203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 847272302 1250 847271052 847271057
    0x30103080906040f090b04113a1508071d0c03070c12081008060c070b06060d230106082203020708160f1205030f0c1c030c0e10021c030b090903070201 66
    0x521030b6411032103070302100d01c9184042c452500e5100c42048141e40203201040fa8150300d055890030401500ca5801461060011003484ae0200f038a0454000d203062026440303c068810b00c0c5820031000d040c40e4607402d6012101c0e000140e07903995810800c44400d0304908006085101c08080c607620300d035006250611505466140035140350304c4100c015601c0c4000c684141404908101920005040c8496550442c00107800741b418190030001c010180c907410900f51700c040b2403401c1540e000d0040995401d00516503420b204003181080c1d011104910b030094400388081510081c000308041c42048900d00070034882013503490308801e0110030b10004603140700d940c2c00420310220203d43d280700101c6e0903c1080e03004004524201030240c4c8820035400071903103980d05008003840d80c11030132720305a440c02c04204e6075600018140c4441c28007402c0d5151038003215000e100b00314072a0a2464000612480000407542606c4071060f0f4120300720068100c15201030b0700600e02e40207100b98988004043c0241ea40700340c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 847273552 1250 847272302 847272311
    0x3040c0e1506030a020708090909010522050c1512010e0106140c03181206070e211203090c030a0f1403030f0103020409030e2101050c040605030103080906040f090b04 73
    0x900390403103006103018965002c80104042401c0d606141d00902e40e0b030b441188010305000048001070101e4500700c60f04081c1c1d0b511602040a00c604540d03100300341c1c510034061280c07a00204d84659a5030f415104030280105031080c8410415a5070006840c4140314840e001f142d00d68440b038084000e1007082c8125000304046070b074640448a0000140d0f49000c041c0f500031810041400d1140c0d84120001c0d4802d40c02c160609080e414148050100f18814280b0f030700c561a03403940a900f4801021666140168400303010941e48007d1100825491888002c82c003610b0b440740c856022240c105448440455818403c1580800401c9001400d9528160003007214114459510000e59240d100c02c65480e840501c401c8010300052401b07a00100c456806480d107002c0c4450b021000c41d0115042505c807070204003001071890023000c0300740501e90f80400c59409481c00c06182650141041c001800028885040400c5170b10260315410203490041020000c2094840e0740d952000c8010609441d0303050013903040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 847274802 1250 847273552 847273561
    0xc0c300c0a05070b040e0f0406110c030307120605091b0c071403060f070f050c10050406140705190c023001050a060302010c0209040f140c04053d0b03040c0e 69
    0x107001c5c0e4045482408144541c2da65500d04010203140003001146c0980c1d817411404c1403080400064510144098011680e0b07042ca000090041880c03155546100c40c14401e051096848001c1050340101450041664040305039249103054021030001440a214a282c006200c0b00070360030030856154164291201c54468410346601c51000307c4144010403000d04001c048188500010100848028252610b69803041c00e0001600c000790741c00e8507140c1d1286008446048040281d5801801c1d03410006d107031032410b140e43c0548076200040c0c0e1041c020344595000940d181c400d06030b80ca880c258140340040349040c8440c0f14081059204025207903280c4800209004150320905080c1e0350140c60783e06100030203a003002321440000704200c4102c2520000000090a000301c0b1006040c101d1018045d0283d01e9001c0c0000ca800c0101202c40203039404600b10903401c01050303030140360414003c0724080e190714520724200501d640d07480f90f14080303070000c100814010a0503613841522002d004607481c5454 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 847276052 1250 847274802 847274819
    0xd081f0b2d0712351f03080310030507060c02030c0d1e0807020a031b1707091d010f27020901030b070903080315090c0a020601090f0f02040902120c0c300c0a0507 71
    0x203104017582852116100c184080f61000029552007406d05e51000b100030340ba0b5a07098102051980722a010130f083e8840c00c011490148481500342d10151000102001580c03141d86680100030040c0707110034404904201484103482c22150402d8003e8038100310a42c2d00c0ca043c92010082a0504070041141c602c0485c102101c40e00c1c03414a0004003008042c41814200c0c41402044101d46083c1440701882da1825003070400e000c0d440b1150f40c802c100280381e0407000b0b80c002c0006013459401032100c0d892200400140e4900240c10f0550740c1014240c9225035600038207442c8280260406091418080100300c1d03043c2d000760b902000c1171000c0c1d40b00d1202e0740b282e03030640c0c4960144822000240c0c01180c0180813140b0746901055074034107040c101040c4003100d400910120780c0642c004440c0f00350000b03980c045100b240d900c0703940c1101c140000185814400356440d40ca84218800c610352607080c2034a11014101b0308100d0320405110481c01641c3c410224070020394a030050301e0300321344600600000088100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 847277302 1250 847276052 847276081
    0x18020d2c070b090105130e09070303140408120906091e150c30040905010314070812070309090e030a020c0102030c0d081f0b2d071235 59
    0x20102c44105041641c0e480054800f03801c001d15094400941e401c0025507442c595000314028600600640001815400c00030200e403400d4043c0051040108801c0089000024126007415030702146e80703450f81011000101d861084884640d07010824103840c01c0c0c04016503000c0111010100c42c40114a00e89000e6008140261205000e00741c0180e0b400d69110384103482c0c00320140d090888402d410706003c4440748c1e190b411a0300501117a581d580014010025200074440c86c113075051008120484c43c0c81125a0b903100c2100020f100604081000c00403d40249038a03400752132000400e01044060701140d9641e50031005038070f001880b4540d03801e0183d50000c81200c10010404028041100384000243c0343c0010141c0085820310ba2084011404040301030004080c1581c034841a0b076440c43c0540780d004149180460780030b00b404051007551101041800c4a032046d40c01110500c1c55010380b030f401e95015110040007048141c0d85403d030312002003501c202c1003101a0b08120081b072901e03030320320204428 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 847278552 1250 847277302 847277309
    0x8100f0603020a140a0504050705131a0306190902180f0906061b03090409030e01081005011d030a0212010507090b03101716091a180118020d2c07 64
    0x10303580c3e00f8000000386141da0b8511103000742c065105166a03030b0100e0221281250b02000040e07002c214100d818000380f40100007092820140f082e001004d540b850400d02c170203003215105100003c0b58910701d0648001200080800600441d104da488401480200080c038041500ca2007801d03a0002540c50104034183c002c0c480030300007a01303244c1c00c0c61241122403490241901c0138481480f1880f601c0e1f0395030051000c075a01c650750f80c90f8a560004009041800c000d440b01c5901c0c802c01d0b07010312142e44e11a4121b4000d1000c0c0403007550720760485021905003582d0023000780d0482e20301100080344003015000b09015100039950341d80110f648036080b14450100b81c81c7d02c2928907440b41304200c800402d240c8004540000e04c1911041c05901440781240d400d9584080c6000f51902641c141407604024549c643c0801a20100c2c0a02240346a403800a0414000e8415204c43e03283d00e114014015410340d03080c1440d107402081040000d0f07442c003101810a240e108102d28100008502e8103001080c00c000b02c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 847279802 1250 847278552 847278559
    0x14150a0f1808180301150f05090f1302010c120c0b06040207030c14070e150a170a230706110f0c0108241804060507030b010903110a030c08100f060302 66
    0xc0c1c1c852079681012650144407580070701042e0781a82c140b00d9500703108a008100c4800c02404066240800f4405400340d45e62005100c0c4031210b040000405032004995845000c10942080802c01c610059541c280f80000160280008003403841780e864110380c4104010f801030712400d6080e624102040140d00c60340d81c0040004001c094002c00144c4e21805150402c0020010380c2c10a03501c8440f0740407204002c550440401c0180a5650b141d418899006c9014010661841c4850340820080540e64694038000030b007600c511441c1034005012130517401414618140070b956070a983e5260041c0700180003480040b16001d03e0080041c69180044c081d00702a1042c6c4484006540d5071009969401d421500000d052000b22005242d698803c480d076a40c1484a01405c00d06041c1030400e82d0403240000c01460500d441c0c40510030040c0c4c4c000000c0400c596100d001c4c160842010000300c4ca07408140d81c4001d140c0d0a00681c046815180450030680c401c425120030416001034141d42d0060702d1007407001940 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 847281052 1250 847279802 847279841
    0xd030506030d0507031409030a0510060f03080f0a020a05010518010b0a0e010312031e091a1b09010302070b040b013602072604060e0a030c0b0714150a0f 67
    0x1b03001c0c0940b205018051801503082c0144000442d0401e4a0008110380603040a02030f170300302c1030543c41201c02419070b00c4884800c80d800d50b1f4803c003007071080710599030104101049031804240300304082c1c03401941c004003c2c410342c00c095500c00b41803c00c854816103039508001002c030301c0f820040400d104403a010100da04990b407a64803514803061000203800d01309912800554203c0b503615105407000c001800001440365100d0400300050f28182c12401c4541e4544c0080c0a035002c1c00700d0312056071603400d174134a9a4995801e401a40240b186403c001e100a04441c2044188044500840d0407920180f80c0c016000c185082000c000d21342d4040320b48180780a5490038100b110b07840d8040c0210038441c045041d040c6100d82c01000c00001c035969540020310002074140204d0f54004032503000c0d03038802e61307c192500d8119520000d01902501810711001d10120303003042803084107040384504044c0101903606801980d2058149107008854040f540c60a01807001401d10452248800b00c0841400b00b15 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 847282302 1250 847281052 847281067
    0xc0503190b09060d17040f0617130803090109020918010606170a200706150801110d0f0b06160219050d02010e042910080108060712020409020c0d030506030d05 70
    0x100151040f00c1030b00c60f0100c2411640d4110312400086c0f01524921541200f010f15004005010305401d4a0b04001c1041708018002001c80400710024820b900c0144507440365120a5400d00400e1031507800b03503004043c403060001400c951845407030300c684060024003001703841c4c05040c0c0d820f00510011654813000c0c13800203111400940d01c0b83c54040716018405059040e2070000182c15042183e064400ea603544403d5113110b0b0b6400b024000030400c0200030f016103000c50010261901a112002401d19201c003c40d10a1004941c0804004a00201002e1306c4006110300041d0350301071040200d00590703004030942c00d00082a00f01e81c0485c2e10050125610b108190300465012150300710700e5070819203603100860700000148030000001d01c13070000d030305031030303100104201704503002407422018880c203034005000024010954a40c0450030b418141c80c1b485900d11444000c0c401c0b0ba00ca00015840440c44022003040480c0c442001000e60b80c0c01d0110b03840b50b9081584654000b0000004500b0400400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 847283552 1250 847282302 847282309
    0x9011d011211101d0f0a0608090a020a061205010504090c090b010e102d1710030b010b04090e01060b0a18090e2508071211040c0503190b0906 62
    0x140245441000204800586400450407610000e48081d020841e40002c41d41070b107203000080000d2560031035802e40200c100d9008506541a5070140d9001c0011608c00a52050001c01c8840d5025501600c10044541d4880300184000000d101d07000e88a03090000016852406004182140c0e40200340b8619503032400c1150303c010003030092300a05100546c04134408070f654010340c03105144059103c0348030308241e0b4200d01d19020140d40e10341d011181c02201c90422580d0050b84a107043e1400c444009860710350342c09034151104654002000c000884001003161291240500121088040148034000100c45400d00380c415501480d80000014007500170701901ca400c0300402400003107041c11400d501c44106c0c07802d4070030f003814425556008045180800907020600a03002c90004503c4c840d060500a5031500d40c003645c03055401d074100d0f41040000b0b1100451940c40544002441044007101003035015081384c10880350b004080304001141040d02c03806000722441c141c40240f88403c29590314042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 847284802 1250 847283552 847283579
    0xc1a0c0309060a0c0b0108010f141003030305070c0b0405010f0b06070b1614070c0618060c030f17070e0a050414061302070f110918031603110d050909011d01 69
    0x4140400007138443c9100800d2060710114040c0c2050300006c102c03007080f5002c031310070743d0031070000105445003034020841079074215150041078070ba02d4500410340b5100c840f821290003000034030243c010006041888100314056102c0b2038040c9400304180b08448003042084041d0180c07140c05040c0105000c00a00e456422240d81080042c8030b081400d2075102c5807841140075081514215154941c030070703007445260b030080c00a1094180c0075005190860800300020401d0f42222002014000710501c401c0681d400303107650850000804082c2070070380c078101c1e8004246034142c0e076005000d0f1040c0040841d40f420140590242451505600009502e5100c140b00101c0c0d42400e003d001c0d07a03403c0c4641c60004640e00382c0200440d01030001d42400030309482c1004507401018104042c40e0109000c91000c4100100640e00e44110511152958800600303050360307801d80188a01061f802030744940f100c2542c014020b002c50200a56408146070380300c0304135202009040b02c8400700b03400c21400420000050b17558 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 847286052 1250 847284802 847284817
    0x20117010806181903030b18010510030b011b05010c090602060702030f03040c050a060c1b030f060c0e10021f050601080610050f0406050c0609060c09010f09120c1a0c030906 76
    0x13190428080c5440e1481c1c0c80c0c480c800110b0029413105206585880c14034003182d403400d458001d4084030b514141c00500c403505400c515206150f110801280644c3c012000f06074001198280d919000d1440d01e0041d00034230390700c44810007048103614042140c5200281040c4101c0f0380703400a51411418030b50a00321508000d101b203405800c203440100e45515040710200041515441c0c03404420094501030391a080030000c8050703902d480010800100f0760410b00a01402e0300b2030000503907041205000c661190070318100c00e80016080c42c2d5120019400505482c0e0108000d00310401604078103c2c001c1610810b441c002d00040006011400e1860004441303c908241410000c0c50205d01044c4440c0135080b0f5400a000b00d200850641010001400840da00a03031103c0688090301e80418640858041c200465040210f402c924650030b50045d03401c40043d00c1d0085039902c07410501d240c64144c0c40302c24001c1415005400320040c008200020136a00300300020360256050840100c24800c50303402420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 847287302 1250 847286052 847286101
    0x5040c031e0e030d020c010e060c18040f0b030601030302030913050f040305090111100209040606180e181002030403231c0605043303020d0209060103021c0603020117010806 76
    0x104c00c030704541030381c40203003006c840d6000045a2814441481c60a0070340041c1140c80d076000070891100c1c0c011043c6030f40c003040b4500712000500482510741e030303200070301800811541502c201e81c00401403580020182070042000c0315405107440f250f40c0c0f40320680d241079480304958652000070400190081c40074180e03d900601d03180c1d4280c0400b40b046072500c59550102805142e000420708030b81d0034035025880180c00c10b070400102403000d0221b415000d501901c660040306003840c010800e04628954101c41105c0715408941002d0150640c0b0402035005070750403000b148981b410402580724050140421081c1089442d090501d44950b0310044200c00c100000e0207640c9000100d850f0703949209010100801c5a59681e40040382140c0f03c8410a03400003103800d41ca061142080140d0ba01030405620790b074141c44502d0980c03698401640a0300440446601c2080c04c0c5000c1d07246003441790b112000700d038003d907260030080c0080d107210f0103000c80030300410415030031000c00155480000c1d8915070020340e100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 847288552 1250 847287302 847287307
    0x40b1305090a020630160f0908031318060819021804050c011d1003110403050a140111090d06200406030e01050a15120314040e0105040c031e0e03 64
    0xb0740c0021111780c00140e0040d201000c1414071803411031120f80c92916004541800e078200d05040c40b100007801e0200300d28900300030402c03090050355807054588500421420003201c0d12440001c02134401c040450084048401c4401e01911a02150f8040c01e400c0b10040320292041c10106008081c992514640507a003100c3c4445980c00b0002006140c14451030003034028110400f04c10f0300040141d40c2d400701c03c140e940d08800d01150b00740d0b17580407841c400d5100c80c180050b51380e00c0400b9002e0b25008541c80588035006403104201440b164405014007890640000c02c1030400e405140c01c81c0e4020610300c15000490452100e00188595200100050241c0c05042004448002d1400c403507002d600000c0020743c4500c00840031840900400d40c0241c0301e0070040c04034407640d0040d1407000c45944200b0314881810704040b401d140c01201c0c0742c85140d03103903003a643d40d540c4c51310326100d09000280b080304e008074f144c06080000036100b0300c00c8000c41c0181d03d00c02d840104146c00100040c0028400d0b102d0180000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 847289802 1250 847288552 847288573
    0x8071103070807021207060f0f17070203191704060506030307020a061e03090b3108090a0603090b041b0e0405071410171003020301090f060b040b130509 67
    0x200080c05086100b4211255a2811481800088080d841d06054294001c01043c0034480c0c0001498240c000310385400147c0200e001f40c200c070340b120b1050703940d640318001109001c51190b000c0024501c0300f225160015001c072101604480c0e58080e480ca0340066107101d000b02e400500704d40c00c495009100202101d04110194000901d4690640e000c0c4022400407901c1d0071a20210000f03500e054013007400e0400c160b4005446200c0c0707000e80248842d07518101f64120704136401d60f00301241400c3c4043d601d411805070181c82c03e00700341c1c1d011500c00c91140215010000e41240b04c0d00410706015446242802140c90341c2d605c00d00c00310a004a10841c2c0304900394081140306140100e00c1c40b43d4000e0b401030041c180342620402065145080107070080e2003144a10808031b030086001003082c00d1041e020401595050344401e2020041d0300000d6055080000303c0e03041c86800140b0658071401010100050f030800c2081204507a61300d014260400d04004045801414a030b00081d48550040e0030340782c81e2080c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 847291052 1250 847289802 847289837
    0xc030313060f09181406030f07030b06041409030703080f01050330070c09050c040605160c17060a0b010912020405100e040b040b0a02340602030108031c02120402010807 74
    0xf1050110000c0369903c0d0010b0500704a020005500a1b0b401d82c00f07020101c200305069038072140705000261400c003401c0b000c40c0660300c480e07012004195004000840a05003272003050340b65801400240c001a030f424000c2200c6401c0041c4550490708020002d1444440c0351401c41070b00e40003c00c4110f114a1000b450445580d074070703c003c1458502c141c054141041c201055942203400240a50a2407141072000380320040e00102165115421104540a01e280e00e19007041e8081d242d4010300c1e084045004180d0030400001401070183c80010303c00d01c800702026004442c100f24a104a18500601600320070150400d50311446e0440407107031078815200e88821103198040c0040c0e400722510f10211040109000e1840401c0d03420070b03a8200c0c150b1420705040891108020520902918503000481100026401e42a80c014150b80a80c0039501c030340c1d40d0660b49440340c024104110030800c0302c8188c0c242c140194400c440c0c00c03449045111a41d520780e82c00454801c40018800390034081314903200c543c0d035032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 847292302 1250 847291052 847291079
    0x152417010e1b03010f020306060913060b120f06090601050d0207150e0d02060106020309010c1707050a080c011d120306012c0a0603021e030c090a080109050c030313060f09 75
    0x1c2011044600e082c100c1c028142150340380c511081c8031034814814407100d942c2d41811a07402c203a0803190018208a1080f4000c02429141d03c1a02c0540340020921503d190380d13188180b00b03d03c101052841a40c0b0001071104085007222800d000950400c484100d10b5030a0303004d404075601070b00030040c100051038041030850704d10402c81000741e44102420000710340e041242ca409050640302850a184003100040e00030320110000401e0030303201c1642e41d00100450301c2034402240d001400c035203144800e41400c00c50380d80300c002c4500d03955080078482905e0300882d42c20b2042c1905000b00806511a5501d1480041d8001403c01410400b00004c59008255081c20075907803422202240212120000e04101400c2d0342c0350701903418140184145040241440300e25500d0f41503a5012540c0c981d68a0300c00042031140d042c0c402d07032084d41e400022480e181c055020507000391044089841c480707000410144d80c3e0040e0444c1c0d202d9800030781400d00c071552288401d5103140c840390424010058681c4081100340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 847293552 1250 847292302 847292323
    0x90b0c07020a062102090411130e060301060515131203030e1603110d0501020d020f04262a0d1a070504060e041a0904152417010e 57
    0x25008112541545080c02d040700041c0210305021402c500303615459080b842c8140701c00030b0b0b1581e000c0b40c2840c2d1034031140c22071141d00c52a01d0069030364400324a48440203810901804490401c0c2c0c40c00106242070501c80e82060701c400806268401044c001c440c070f0700768006120080000748a00002848000c80c1e03070b0010215102c1d44001c580c60b90018005450032020020722101080714100800110b10b050042c548446000c2d2807440141689050060281c46110740c0211114030018144409566802c040c2040c2c4415103184122148000b600c00c800720030f401d07045040c94014000d410000c000c0c080e034440440c081c14000c503010300b801c2c20004807003103002217041e141c00400c809140c4117141a00c4203140d01030181d00704241811f04051000b0001319442e80214080c980d2a038101c04101c01900c0001500503004041c200c5524092401041d420f024040340c50383c043c1458110200b2554560706068071400c580e0401e040da40c075004151121071101450b03070589550b40c25512416460910401020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 847294802 1250 847293552 847293571
    0x40b1810080607120e010c0507080a0905130c09052b060e1005060907090303080a0209030109021c031205011503110c0d0f090801090506010909032a110906090703020c01090b 76
    0x5148900c1c800c069840246517407205925112040340300f241c20000f036581d1250040141c6488402c2d40f88217031184681a00900c4d031010204c6058508442607412540580344995102d28109a0b9074050120b04241c0d0481c90055050340d14481d00494051031078031845500400c0d01048014441e00041d0030300b100303407039824106900c0c0c0d4200403090601c009a15000b90041c581110250b103181c900600c03000014100500442d000200204030366803d4102212440c3c00620b440000d003049071692505208800045020461000c01844d40d4103081c490b25040b601c246502c0b40d080c0c0c6109504a006141c21108110049005d01c15040110800c128000c141091074844071840c42d180840a03101151903401491180c2c1441e0600c0e000404c0800e015044a40100c40855482c40c00d1800b0303a41c2c41c40010119512203002040006085502040c10440342d02600c0130800301425a014440b88100880381c65420002010110304810f12950081401e41c101b040009404116a60352408911003038414186 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 847296052 1250 847294802 847294817
    0x30c020a0b070b06060c010603170304060509032502040f020d0518030a09050411070215130605040b030f19090b09121317030d1107050c040b1810080607 67
    0x21800d020040102406010070300070b042680c19550000420740050580b40a1000420201d00b042000d4100741702465001c2c4000c0e005d81302018942096030000c4605465140c01d00007c1002c0043c080119200d400c65002d43e0100011040c00340103d4202010007241c210f50f44010902c40441148050304180c0081c01003c20799080420030120710500d240d16104990708104550001250400308030411550140d0300880c115000383c110455500072540e020f5082500744000126600707401000b0100740030f40c0c01c005510b40313849040c01c40e400c0c05036024904403030b0810008940400350b202c64955001011083d01000d6401d2800030409039070090604071410001103003405105107083c05046041c852200c5800d080032a800c00300c60b0900b1141c07140300188425002c004400990900803101900700b0760304280320f9416200030344601035000b400180c1380c0d03014000742d1000d60718050240320714544000702031091060150b418000d43c2000a01410b04021003200005000601480091301c07030720343e40c1c84468 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 847297302 1250 847296052 847296077
    0xa030807021c1d221802090906011721130317040f0905040c180b0301050f0f0708070f050f07050f0105101203020703082104120215060d020607020d06020703 69
    0xb601004400e42c900c54640d0414000e0140c3c0d00c0744c41d030701030340d030940802050003221200d6810310140032950203904000700104000b02290b00088070303412038503640503801c00044402604c1da11240c0c4c0000300c041d08283c1c40385007240310740f10401030543c04d03149000701750141c0da4035620343e10035455080850411b4000400d0800505104030100f030700a00080348103012520b02561a0b4544030f14a0050300a08001400300080c205455845a4210700c0098001c20007800d00f5100d1300e03429101225868001305010000913103aa101d103801138000d1003d904d0700b90f100f1200c07850590b25074022404c9401c0900007402001c000c540e0412851581040d10000003c890420035034464140381c0640049500032221a520303000261b0010741001140c2d00f1103941c5444180041000c03034411421406031100c040850140f1080c000340c03490504600c00d4a400b12200d587e1085c50000c068481221850781c030031040300c03861016003070040040035103030700c0141482c90300d0000c0ea940d00c0c01c83e0007405043e00040d41c02080305 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 847298552 1250 847297302 847297337
    0x110904022b290307120c170a0b010503030712300e060106091401200a150c17040f1a0109060906090614040f020f04080105041b080a030807021c 63
    0x9004082e86492036070903004a4000c6a0780b80f20310710030300e00800701e000903ea060181c00800c0d100a000c1018900000390101090550f8a0f410301006580b00d40b901000080c403807800004444880d5807103d0400303600e20321400d0946041d515241054120741c01032103850800d048566108403400280440055805140c90348546000d40503040310041c0300f10b0180c141f201030440340c48115508400d182a040100301c2a01418504602d4000b00308a44500d464500400a2000e40827240003030b1194100808110101c5c1110f50f01c2e6401441c450b0420034402040c00716024405c556000740c0036062229207442e000c9102c481d14503090340712920036560780078107000f03a03030b16400707000c00810107060140103490601a00c0d00c01c480c607012500d44a990380d01c0c0e6021400c0316079010349961940030901181c48542e00c15410340609011101114282c032094200a0000718a005030010307030308054010101c3c0003659605850030800074103d1025849540c040c011602c9001071a40c1d01080f00381d032140d406050701c403281d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 847299802 1250 847298552 847298591
    0x302060f0705040e0109050601030b040c050d0b091b1806071b0b0f0f031003021906140a0c14030d050717090f030a0c0602121e0109110904022b 63
    0x103100400c42d0801c001c00040c9a4107014a05460f64080002215280e850041c1c00a00088242c0d80d00207042880f0b020750560000e02800380c14144540521101c24075504010820404607240314060340c96640001410520101600c81d0409045012500c440c1c240000b500a4019950850b20884110882c0240380d942c030a142006003220910300d0300b807d4032052021510f001d4030000d4001c441c4003000180d070400040c416000119005002d031034203402116220010460346001d0280030170000c540e0107902160550440b002d61015a841c441c20604541c2d8100e0b034010100011f2013244810f002c1060b4604840c80360a01404c0103859400c0c1d140e440315500d510034a4010f09050b081c0e04080a0720340000b901000710781e41da05503850300140c02c0c00c591074200003e0183c030313503884040040c240401c500704074000e9488401c035402814070403150303a0b50a560310584080a0305d030781d04400c042c0120051420243c010308101c580d15001d580c402540f5580c03681a41c5000101d041465864800d2607900185d6040d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 847301052 1250 847299802 847299811
    0x18011b050d1e05030403111509010b102c060708130e09150705160b01080303150d0804090906090f0f02240415140c010b03010f05152b0302060f 63
    0x1021002c0c1804800500076000080c000b606011002a103e41074007403d02020940141d00302030a055402c1410340301e4028411600410b00070320580030446003e500801c6607075102800b40183d41c140c0c40045007240e070100040b0040e140c01a5003070059a00081415000d0081c003c280e51045000f54a0180400c600e468054011550394005110922488038a40000c990080c058201250746d100e075081400030011002e6006418015018004038880c030000c0300640c01901c0d50301da14164075070f072030081101d003034140ca40c010b05844040004002d202000e80003e401140110700001d640720181c3c0300e40310042c8030341c40100c8000d042029894114a448109030709234030581c1440d04002401c500451026209074002c607007810100d00050000c640c07007030b40a180e00110b0341c2e600301e4503402e0208519019202d0907411034829400d0103901c0d1702840c04c80c481ea41c03284202140c4003400495260911005004070340d02800f0007900c1000401e15419192111520f41c1c0c0710340d0042c4000e00c1c08280c40099484041c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 847302158 1106 847301052 847301087
    0x904031206270608031c09080c0a020a08060601050a110a0f0b0a050108010209060702271503060105091620070909140109030518011b050d 61
    0x70303407040075000344503a0044400e06030034001502d0060051204545c0244580c42007821010180800383c01d030448001480c000685840c0001e5101c1484443c0c940d118944900450828420150050042c01c000e440103040100000b8140d01c6160280010812817682248103080c0c03e10406184903440107024405004078a010048000125800810315207800d00003e940348042c000c0314904a401814680341c41c0d0076908000d00f051084100e00007003600382d41550110001d03c0000c5005031034000ca000485e40d4104209460030b50140c111a005180000a01c074a141011440905402103070818210108000e2112100b80f5503505504416200351580019251034581c003c2c1c2606004500d425030b25402062180e00380d401c1c00c2c000600044040291a01c0d800808642e09050401454180d081c540740c101030202c003126121098950342c00629100c114540c0102d001c044030032404 = true := by decide +kernel

theorem cover : BRFrame.Cov 847122302 847302158 := by
  have h0 := BRFrame.cov_init 847122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 847122302 ≤ n) (h2 : n < 847302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
